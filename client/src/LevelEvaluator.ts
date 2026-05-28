/**
 * LevelEvaluator — domain layer on top of LeanSessionManager.
 *
 * Owns the Lean preamble, assembles the full source from a "player
 * contribution", and translates LSP positions back to contribution
 * coordinates so callers never see preamble line numbers.
 *
 * Single entry point: `evaluate(contribution)` does the full round trip
 * and returns `{ diagnostics, leafGoals, hypKindMap, complete }`. The
 * trip itself is just two RPC calls — `updateFile` followed by
 * `Lean.Widget.getInteractiveDiagnostics`. There is no manual waiting
 * for processing or diagnostics, no version tracking, no race
 * management: the widget RPC call is request/response and the server
 * holds the response until elaboration is ready, so a single await
 * gives us the full state.
 *
 * `leafGoals` is shaped as a list of (position, goal) pairs. With
 * today's input — `workspaceToLean` emits `skip` for empty bodies —
 * each unsolved leaf in the proof tree produces its own diagnostic and
 * its own LeafGoal entry, automatically.
 */
import type {
  InteractiveGoal,
  InteractiveDiagnostic,
  TaggedText,
  MsgEmbed,
} from '@leanprover/infoview-api';
import {
  LeanSessionManager,
  type Position,
  type Range,
} from './LeanSessionManager';
import { log, logError } from './log';

const TAG = 'LevelEvaluator';
const DEFAULT_URI = 'file:///blockly/Blockly.lean';

// In-memory prelude prepended to the player's contribution. The stable
// bits — `import Mathlib`, the per-goal info RPC, etc. — live in the
// on-disk `MathlibDemo.Preamble` module so they compile once into a
// `.olean` and never re-elaborate. Only level-specific definitions
// live here.
const DEFAULT_PRELUDE = `import MathlibDemo.Preamble

attribute [grind .] inv_lt_of_inv_lt₀
attribute [grind =] one_mul
attribute [grind =] Nat.cast_le._simp_1
attribute [grind =] Mathlib.Tactic.Qify.intCast_le._simp_1
attribute [grind =] Mathlib.Tactic.Rify.ratCast_le._simp_1
attribute [grind =] Int.cast_natCast
attribute [grind =] Rat.cast_natCast

macro "triangle_ineq" : tactic => \`(tactic| (
  simp only [abs, max_def]
  split_ifs <;> linarith
))

macro "conclude" "[" t:term,* "]" : tactic => do
  \`(tactic| iterate 5 (try (first
    | (fail_if_no_progress triangle_ineq)
    | rel [$t,*]
    | (fail_if_no_progress simp [$[$t:term],*]; norm_num)
    | (fail_if_no_progress field_simp [$[$t:term],*])
    | ring_nf | norm_num | norm_cast
    | linarith only [$t,*] | nlinarith only [$t,*]
    | positivity | abel | omega)))

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y ≠ c, |y - c| < δ → |f y - L| < ε

def FunCont (f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

def SeqConv (a : ℕ → ℝ) : Prop :=  ∃ L, SeqLim a L

theorem ArchProp {ε : ℝ} (hε : ε > 0) : ∃ N > (0 : ℕ), 1 / (N : ℝ) < ε := by sorry

`;

// ── Public types ─────────────────────────────────────────────────────

/** A drag-and-drop affordance reported by the Lean RPC. Each variant's
 * `kind` matches the server's inductive `Affordance` constructor name
 * and is also the key used in per-level `allowedAffordances`. Variants
 * can carry data — e.g. `choose` carries the binder name of the
 * existential as a suggested default variable. */
export type Affordance =
  | { kind: 'apply' }
  | { kind: 'rewrite' }
  | { kind: 'choose'; suggestedName: string }
  | { kind: 'use' }
  | { kind: 'intro' }
  | { kind: 'specialize' };

/** Per-hypothesis info extracted server-side from the Lean `Expr` AST.
 * `affordances` is the list of drag-and-drop affordances the Lean side
 * deems *potentially* applicable; the client intersects it with the
 * level's allowed-affordance set before rendering. */
export interface HypInfo {
  isAssumption: boolean;
  affordances: Affordance[];
}

/** Per-goal information from the server. `hyps` is keyed by fvarId,
 * `target.affordances` lists drag affordances for the goal target. */
export interface GoalInfo {
  mvarId: string;
  hyps: Map<string, HypInfo>;
  target: { affordances: Affordance[] };
}

/** mvarId → GoalInfo, for every leaf goal in the current evaluation. */
export type GoalInfoMap = Map<string, GoalInfo>;

export interface ContributionDiagnostic {
  range: Range; // contribution-relative
  severity?: number;
  message: string;
}

export interface LeafGoal {
  /** Position in the contribution where this goal applies. */
  position: Position;
  /** The interactive goal payload. */
  goal: InteractiveGoal;
}

export interface EvaluationResult {
  diagnostics: ContributionDiagnostic[];
  leafGoals: LeafGoal[];
  /** Server-extracted info about each leaf goal (hypothesis kinds and
   * target syntax), keyed by mvarId. */
  goalInfoMap: GoalInfoMap;
  /** True iff there are no error diagnostics and no leaf goals. */
  complete: boolean;
}

// ── Internal helpers ────────────────────────────────────────────────

/**
 * Generic plain-text flatten for any TaggedText. Walks text/append/tag
 * uniformly, ignoring tag annotations entirely. Suitable for
 * `CodeWithInfos` (TaggedText<SubexprInfo>), where the embed payload
 * carries no display text and the tag content holds the rendering.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function flattenAnyTaggedText(tt: any): string {
  if (!tt || typeof tt !== 'object') return '';
  if ('text' in tt)   return tt.text;
  if ('append' in tt) return tt.append.map(flattenAnyTaggedText).join('');
  if ('tag' in tt)    return flattenAnyTaggedText(tt.tag[1]);
  return '';
}

/** Render an InteractiveGoal as a compact plain-text block. */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function renderGoalAsText(goal: any): string {
  const lines: string[] = [];
  if (goal.userName) lines.push(`case ${goal.userName}`);
  for (const h of goal.hyps ?? []) {
    const names = (h.names ?? []).join(' ');
    const typeStr = flattenAnyTaggedText(h.type);
    lines.push(`${names} : ${typeStr}`);
  }
  const goalPrefix = goal.goalPrefix ?? '⊢ ';
  lines.push(`${goalPrefix}${flattenAnyTaggedText(goal.type)}`);
  return lines.join('\n');
}

/**
 * Flatten an InteractiveDiagnostic message TaggedText to a plain
 * string. Unlike a naive recursive walk, this dispatches on the
 * embed type when it hits a `tag` node — for `expr` and `goal`
 * embeds, the actual display text lives in the *payload*, not in
 * the tag's content (which is typically a placeholder like `{text:""}`).
 */
function flattenInteractiveMessage(tt: TaggedText<MsgEmbed>): string {
  if ('text' in tt) return tt.text;
  if ('append' in tt) return tt.append.map(flattenInteractiveMessage).join('');
  if ('tag' in tt) {
    const [embed, content] = tt.tag;
    if ('expr' in embed) {
      return flattenAnyTaggedText(embed.expr);
    }
    if ('goal' in embed) {
      return renderGoalAsText(embed.goal);
    }
    if ('widget' in embed) {
      return flattenInteractiveMessage(embed.widget.alt);
    }
    if ('trace' in embed) {
      return flattenInteractiveMessage(embed.trace.msg);
    }
    // lazyTrace or anything else: fall back to the tag content.
    return flattenInteractiveMessage(content);
  }
  return '';
}

/**
 * Walk an InteractiveDiagnostic message tree and pull out every embedded
 * InteractiveGoal. Returns goals in document order.
 */
function extractGoalsFromTaggedText(tt: TaggedText<MsgEmbed>): InteractiveGoal[] {
  const goals: InteractiveGoal[] = [];
  function traverse(node: TaggedText<MsgEmbed>) {
    if ('text' in node) return;
    if ('append' in node) {
      node.append.forEach(traverse);
      return;
    }
    if ('tag' in node) {
      const [embed, content] = node.tag;
      if ('goal' in embed) goals.push(embed.goal);
      traverse(content);
    }
  }
  traverse(tt);
  return goals;
}

// ── LevelEvaluator ──────────────────────────────────────────────────

export interface LevelEvaluatorOptions {
  uri?: string;
  prelude?: string;
}

export class LevelEvaluator {
  private session: LeanSessionManager;
  private uri: string;
  private prelude: string;
  private preludeLineCount: number;

  constructor(session: LeanSessionManager, opts: LevelEvaluatorOptions = {}) {
    this.session = session;
    this.uri = opts.uri ?? DEFAULT_URI;
    this.prelude = opts.prelude ?? DEFAULT_PRELUDE;
    // The prelude ends in `\n`, so split('\n').length - 1 is the number
    // of lines it occupies and also the 0-indexed line where the
    // contribution starts.
    this.preludeLineCount = this.prelude.split('\n').length - 1;
  }

  /**
   * Assemble the full Lean source for `contribution`, but with the
   * `import MathlibDemo.Preamble` line replaced by a plain `import
   * Mathlib`. Useful for copying out of the game and pasting into a
   * standalone Lean editor (e.g. live.lean-lang.org), where the
   * `MathlibDemo` lake project doesn't exist but Mathlib is available.
   */
  assembleStandaloneSource(contribution: string): string {
    return (this.prelude + contribution).replace(
      /^import MathlibDemo\.Preamble$/m,
      'import Mathlib',
    );
  }

  /**
   * Run the player's contribution through Lean and return diagnostics +
   * leaf goals in contribution-relative coordinates. A single round
   * trip: updateFile (sends didChange), then getInteractiveDiagnostics
   * via widget RPC (which the server holds until elaboration is ready).
   */
  async evaluate(contribution: string): Promise<EvaluationResult | null> {
    const fullSource = this.prelude + contribution;

    let interactiveDiagnostics: InteractiveDiagnostic[];
    try {
      await this.session.updateFile(this.uri, fullSource);
      // Lean's widget RPCs return data for the most recently elaborated
      // snapshot, NOT for the latest didChange — so we must wait for
      // processing to catch up before asking for diagnostics, or we'd
      // get stale results from the previous edit.
      await this.session.waitForProcessing(this.uri);
      log(TAG, 'Calling getInteractiveDiagnostics...');
      interactiveDiagnostics = await this.session.widgetRpcCall<InteractiveDiagnostic[]>(
        this.uri,
        'Lean.Widget.getInteractiveDiagnostics',
        { textDocument: { uri: this.uri } },
      );
    } catch (err) {
      logError(TAG, 'evaluate failed:', err);
      return null;
    }

    // Derive both plain diagnostics and leaf goals from the same single
    // server response — they are two views of the same data.
    const diagnostics: ContributionDiagnostic[] = [];
    const leafGoals: LeafGoal[] = [];
    for (const diag of interactiveDiagnostics) {
      // Skip anything entirely inside the preamble.
      if (diag.range.end.line < this.preludeLineCount) continue;

      // Suppress the Lean linter's "merge intros" suggestion
      // (severity 2 = Warning, message starts with "Try this: intro").
      // The diagnostic has no `code` or `tags` so we match by message.
      if (diag.severity === 2) {
        const flat = flattenInteractiveMessage(diag.message);
        if (/^Try this: intro/.test(flat)) continue;
      }

      diagnostics.push({
        range: this.translateRangeToContribution(diag.range),
        severity: diag.severity,
        message: flattenInteractiveMessage(diag.message),
      });

      const goals = extractGoalsFromTaggedText(diag.message);
      const position = this.translatePositionToContribution(diag.range.start);
      for (const goal of goals) {
        leafGoals.push({ position, goal });
      }
    }
    log(TAG, `Got ${diagnostics.length} diagnostic(s), ${leafGoals.length} leaf goal(s)`);

    // Extract per-goal server-side info (hypothesis kinds + target
    // syntax) via the in-memory-prelude `getGoalInfo` RPC. Position
    // must be after the prelude so the method is registered.
    const goalInfoMap: GoalInfoMap = new Map();
    const callPos: Position = { line: this.preludeLineCount, character: 0 };
    for (const { goal } of leafGoals) {
      if (!goal.ctx || !goal.mvarId) continue;
      try {
        const result = await this.session.widgetRpcCall<GoalInfoResult>(
          this.uri,
          'getGoalInfo',
          { ctx: goal.ctx, mvarId: goal.mvarId },
          callPos,
        );
        const hyps = new Map<string, HypInfo>();
        for (const h of result.hyps) {
          hyps.set(h.fvarId, {
            isAssumption: h.isAssumption,
            affordances: h.affordances,
          });
        }
        goalInfoMap.set(result.mvarId, {
          mvarId: result.mvarId,
          hyps,
          target: { affordances: result.target.affordances },
        });
      } catch (err) {
        logError(TAG, 'getGoalInfo failed:', err);
      }
    }

    // `complete` must account for errors ANYWHERE in the file, not just
    // in the contribution. If the preamble fails to elaborate, its
    // errors are filtered out by the preludeLineCount check above — but
    // swallowing them would spuriously mark the proof as complete
    // (no filtered diagnostics, no leaf goals). Guard against that by
    // scanning the raw diagnostics too.
    const hasErrors = interactiveDiagnostics.some((d) => d.severity === 1);
    const complete = !hasErrors && leafGoals.length === 0;
    if (hasErrors && diagnostics.length === 0) {
      logError(TAG, 'errors present but all inside preamble — ' +
        'preamble likely broken; surfacing first error to the user.');
      const firstErr = interactiveDiagnostics.find(d => d.severity === 1)!;
      diagnostics.push({
        range: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } },
        severity: 1,
        message: `Preamble elaboration error (rebuild MathlibDemo?): ${flattenInteractiveMessage(firstErr.message)}`,
      });
    }

    return { diagnostics, leafGoals, goalInfoMap, complete };
  }

  // ── Coordinate translation ──────────────────────────────────────

  private translatePositionToContribution(p: Position): Position {
    return {
      line: Math.max(0, p.line - this.preludeLineCount),
      character: p.character,
    };
  }

  private translateRangeToContribution(r: Range): Range {
    return {
      start: this.translatePositionToContribution(r.start),
      end: this.translatePositionToContribution(r.end),
    };
  }
}

// ── HypKinds RPC payload type (internal to this module) ────────────

interface GoalInfoResult {
  mvarId: string;
  hyps: Array<{ fvarId: string; isAssumption: boolean; affordances: Affordance[] }>;
  target: { affordances: Affordance[] };
}
