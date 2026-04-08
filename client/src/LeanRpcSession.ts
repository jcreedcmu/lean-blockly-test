/**
 * LeanRpcSession — TRANSITIONAL adapter.
 *
 * The new transport-layer module is `LeanSessionManager`, which knows
 * nothing about preambles, hyp-kinds, or "goals." This file used to
 * contain that logic; it now exists only to preserve the legacy
 * `getGoals` / `hasErrors` / `setDiagnosticsCallback` API that
 * `App.tsx` and `LeanSession.ts` still call. It will be deleted once
 * `LevelEvaluator` lands and `App.tsx` is rewritten to use it
 * directly. See plans/REFACTOR.md.
 */
import type { MessageConnection } from './LeanLspClient';
import type {
  InteractiveGoals,
  InteractiveGoal,
  InteractiveDiagnostic,
  TaggedText,
  MsgEmbed,
} from '@leanprover/infoview-api';
import { log, logError } from './log';
import { LeanSessionManager, type LspDiagnostic } from './LeanSessionManager';

export type { LspDiagnostic } from './LeanSessionManager';

const TAG = 'LeanRpc';

// ── helpers ──────────────────────────────────────────────────────────

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
      if ('goal' in embed) {
        goals.push(embed.goal);
      }
      traverse(content);
    }
  }

  traverse(tt);
  return goals;
}

function extractGoalsFromDiagnostics(diagnostics: InteractiveDiagnostic[]): InteractiveGoals {
  const allGoals: InteractiveGoal[] = [];
  for (const diag of diagnostics) {
    allGoals.push(...extractGoalsFromTaggedText(diag.message));
  }
  return { goals: allGoals };
}

// ── HypKinds types (still used by Goals.tsx via re-export) ──────────

export interface HypIsAssumption {
  fvarId: string;
  isAssumption: boolean;
}

export interface GoalHypKinds {
  mvarId: string;
  hyps: HypIsAssumption[];
}

export interface HypKindResult {
  goals: GoalHypKinds[];
}

export type HypKindMap = Map<string, boolean>;

export interface GoalsWithHypKinds {
  goals: InteractiveGoals;
  hypKindMap: HypKindMap;
}

// ── LeanRpcSession (legacy adapter) ─────────────────────────────────

export class LeanRpcSession {
  private manager: LeanSessionManager;
  private uri: string;
  private onDiagnosticsChange?: (diagnostics: LspDiagnostic[]) => void;
  private diagnosticsPoll: ReturnType<typeof setInterval> | null = null;
  private lastDiagnosticsSnapshot: LspDiagnostic[] = [];

  constructor(connection: MessageConnection, uri: string) {
    this.manager = new LeanSessionManager(connection);
    this.uri = uri;

    // Legacy push-style diagnostics: poll the manager and fire the
    // callback on change. The whole push API goes away in task #3.
    this.diagnosticsPoll = setInterval(() => {
      const diags = this.manager.getDiagnostics(this.uri);
      if (diags !== this.lastDiagnosticsSnapshot) {
        this.lastDiagnosticsSnapshot = diags;
        this.onDiagnosticsChange?.(diags);
      }
    }, 100);
  }

  /** Expose the underlying manager so newer code (LevelEvaluator) can use it. */
  getManager(): LeanSessionManager {
    return this.manager;
  }

  // ── Diagnostics (legacy push API) ───────────────────────────────

  setDiagnosticsCallback(callback: (diagnostics: LspDiagnostic[]) => void): void {
    this.onDiagnosticsChange = callback;
  }

  hasErrors(): boolean {
    return this.manager.getDiagnostics(this.uri).some((d) => d.severity === 1);
  }

  // ── Legacy getGoals orchestration ───────────────────────────────

  async getGoals(code: string, preludeLineCount: number): Promise<GoalsWithHypKinds | null> {
    try {
      await this.manager.updateFile(this.uri, code);
      await this.manager.waitForProcessing(this.uri);

      log(TAG, 'Calling getInteractiveDiagnostics...');
      const diagnostics = await this.manager.widgetRpcCall<InteractiveDiagnostic[]>(
        this.uri,
        'Lean.Widget.getInteractiveDiagnostics',
        { textDocument: { uri: this.uri } },
      );
      const goals = extractGoalsFromDiagnostics(diagnostics);
      log(TAG, 'Extracted goals:', goals.goals.length);

      // Call our custom RPC method (defined in the preamble) to get
      // isProp classification for each goal. Position must be after
      // the preamble.
      const hypKindMap: HypKindMap = new Map();
      const callPos = { line: preludeLineCount, character: 0 };
      for (const goal of goals.goals) {
        if (goal.ctx && goal.mvarId) {
          try {
            const hypKindResult = await this.manager.widgetRpcCall<HypKindResult>(
              this.uri,
              'getHypKinds',
              { ctx: goal.ctx, mvarId: goal.mvarId },
              callPos,
            );
            for (const g of hypKindResult.goals) {
              for (const h of g.hyps) {
                hypKindMap.set(h.fvarId, h.isAssumption);
              }
            }
          } catch (err) {
            logError(TAG, 'getHypKinds failed:', err);
          }
        }
      }

      return { goals, hypKindMap };
    } catch (err) {
      logError(TAG, 'getGoals failed:', err);
      return null;
    }
  }

  // ── Cleanup ─────────────────────────────────────────────────────

  dispose(): void {
    if (this.diagnosticsPoll) {
      clearInterval(this.diagnosticsPoll);
      this.diagnosticsPoll = null;
    }
    this.manager.dispose();
  }
}
