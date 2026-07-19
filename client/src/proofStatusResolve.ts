/**
 * Backward direction of the pill <-> position model: map goal-state diagnostics
 * (Lean's "unsolved goals" errors) back to the status pill that *governs* the
 * position, so each pill can show success / failure independently.
 *
 * This is the per-pill replacement for the old per-block line-overlap pass. It
 * is pure over (serialized workspace, sourceInfo, pill list, diagnostics) so it
 * is unit-testable without a live Blockly workspace or Lean session. It is
 * deliberately *defensive*: overlapping governed regions are resolved
 * deterministically (innermost wins) and an unmatched diagnostic is ignored
 * rather than fatal. See `plans/pill-position-mapping.md`.
 */
import type { BlocklyState } from './Blockly';
import { governedRegion, type MarkerLocation } from './markerResolve';
import type { SourceInfo } from './workspaceToLean';
import type { ProofStatus } from './FieldProofStatus';

type Point = { line: number; character: number };

/** A status pill, identified by its block and the input arm it governs. */
export interface Pill {
  blockId: string;
  target: string;
}

/** Minimal diagnostic shape (matches the LSP `Diagnostic.range`). */
export interface DiagnosticLike {
  range: {
    start: { line: number; character: number };
    end: { line: number; character: number };
  };
  message: string;
  severity?: number;
}

export interface PillStatus extends Pill {
  status: ProofStatus;
}

/** A pill paired with its resolved governed region (undefined if unresolved). */
interface PillRegion extends Pill {
  region: MarkerLocation | undefined;
}

/** Stable key for a pill, so callers can address fields by (block, target). */
export function pillKey(blockId: string, target: string): string {
  return `${blockId}::${target}`;
}

/**
 * A goal-state diagnostic is Lean's "unsolved goals" error. Severity 1
 * (error) is required.
 */
export function isGoalStateDiagnostic(d: DiagnosticLike): boolean {
  return (d.severity ?? 1) === 1 && d.message.includes('unsolved goals');
}

function lineSpan(loc: MarkerLocation): number {
  return loc.endLineCol[0] - loc.startLineCol[0];
}

/** Does `loc` enclose the (0-based) line `line`? */
function regionContainsLine(loc: MarkerLocation, line: number): boolean {
  return loc.startLineCol[0] <= line && line <= loc.endLineCol[0];
}

/**
 * The pill whose governed region best encloses the given line: among regions
 * that enclose it, the *innermost* (smallest line span), tie-broken by latest
 * start line. Returns undefined if none encloses it.
 */
function bestPillRegionForLine(
  pills: PillRegion[],
  line: number,
): PillRegion | undefined {
  let best: PillRegion | undefined;
  for (const p of pills) {
    if (!p.region || !regionContainsLine(p.region, line)) continue;
    if (!best || !best.region) {
      best = p;
      continue;
    }
    const span = lineSpan(p.region);
    const bestSpan = lineSpan(best.region);
    if (
      span < bestSpan ||
      (span === bestSpan && p.region.startLineCol[0] > best.region.startLineCol[0])
    ) {
      best = p;
    }
  }
  return best;
}

function bestPillForDiagnostic(
  pills: PillRegion[],
  diag: DiagnosticLike,
): PillRegion | undefined {
  return bestPillRegionForLine(pills, diag.range.start.line);
}

/**
 * The status pill governing a contribution position — the innermost whose
 * governed region encloses it — or null. Used to map a leaf goal back to its
 * pill so the goal tabs and pill selection stay in sync.
 */
export function pillForPosition(
  workspace: BlocklyState,
  sourceInfo: SourceInfo[],
  pills: Pill[],
  position: Point,
): Pill | null {
  const pillRegions: PillRegion[] = pills.map((p) => ({
    ...p,
    region: governedRegion(workspace, sourceInfo, p.blockId, p.target),
  }));
  const best = bestPillRegionForLine(pillRegions, position.line);
  return best ? { blockId: best.blockId, target: best.target } : null;
}

export interface ResolveResult {
  statuses: PillStatus[];
  /** Diagnostics that matched no pill region. Surfaced for debugging. */
  unmatched: DiagnosticLike[];
}

/**
 * Resolve per-pill proof statuses from the file's diagnostics.
 *
 * Every pill defaults to `complete`; a pill is `incomplete` if some goal-state
 * diagnostic is attributed to it. A pill whose region can't be resolved is left
 * `unknown`.
 */
export function resolveProofStatuses(
  workspace: BlocklyState,
  sourceInfo: SourceInfo[],
  pills: Pill[],
  diagnostics: DiagnosticLike[],
): ResolveResult {
  const pillRegions: PillRegion[] = pills.map((p) => ({
    ...p,
    region: governedRegion(workspace, sourceInfo, p.blockId, p.target),
  }));

  const status = new Map<string, ProofStatus>();
  for (const p of pillRegions) {
    status.set(pillKey(p.blockId, p.target), p.region ? 'complete' : 'unknown');
  }

  // Any error inside a governed subproof makes that proof incomplete. Lean can
  // recover from a tactic error by synthesizing the requested `have`, so
  // looking only for "unsolved goals" would incorrectly paint such a proof
  // green and expose the recovered hypothesis in the outer goal.
  const errorDiags = diagnostics.filter((d) => (d.severity ?? 1) === 1);
  const unmatched: DiagnosticLike[] = [];
  for (const diag of errorDiags) {
    const match = bestPillForDiagnostic(pillRegions, diag);
    if (match) {
      status.set(pillKey(match.blockId, match.target), 'incomplete');
    } else if (isGoalStateDiagnostic(diag)) {
      unmatched.push(diag);
    }
  }

  return {
    statuses: pills.map((p) => ({
      ...p,
      status: status.get(pillKey(p.blockId, p.target)) ?? 'unknown',
    })),
    unmatched,
  };
}

/** Where a diagnostic was attributed: a specific pill, or (fallback) the
 * narrowest block whose broad range contains it. */
export type DiagnosticSource =
  | { kind: 'pill'; blockId: string; target: string }
  | { kind: 'block'; blockId: string };

function rangeContainsPoint(r: SourceInfo, p: Point): boolean {
  const afterStart =
    r.startLineCol[0] < p.line ||
    (r.startLineCol[0] === p.line && r.startLineCol[1] <= p.character);
  const beforeEnd =
    p.line < r.endLineCol[0] ||
    (p.line === r.endLineCol[0] && p.character <= r.endLineCol[1]);
  return afterStart && beforeEnd;
}

/** The smallest (by line span, then column span) range that contains `p`. */
function narrowestContaining(ranges: SourceInfo[], p: Point): SourceInfo | undefined {
  const size = (r: SourceInfo): [number, number] => [
    r.endLineCol[0] - r.startLineCol[0],
    r.endLineCol[1] - r.startLineCol[1],
  ];
  let best: SourceInfo | undefined;
  for (const r of ranges) {
    if (!rangeContainsPoint(r, p)) continue;
    if (!best) {
      best = r;
      continue;
    }
    const [bl, bc] = size(best);
    const [rl, rc] = size(r);
    if (rl < bl || (rl === bl && rc < bc)) best = r;
  }
  return best;
}

/**
 * Locate the source of a diagnostic for the click-to-highlight affordance:
 *
 * 1. If it's a goal-state diagnostic that lands in a status pill's governed
 *    region, then use that (innermost) pill.
 * 2. Otherwise, use the narrowest block whose broad range contains it.
 *
 * Returns null if nothing contains it. Pure, like `resolveProofStatuses`.
 */
export function locateDiagnostic(
  workspace: BlocklyState,
  sourceInfo: SourceInfo[],
  blockRanges: SourceInfo[],
  pills: Pill[],
  diag: DiagnosticLike,
): DiagnosticSource | null {
  if (isGoalStateDiagnostic(diag)) {
    const pillRegions: PillRegion[] = pills.map((p) => ({
      ...p,
      region: governedRegion(workspace, sourceInfo, p.blockId, p.target),
    }));
    const match = bestPillForDiagnostic(pillRegions, diag);
    if (match) return { kind: 'pill', blockId: match.blockId, target: match.target };
  }
  const block = narrowestContaining(blockRanges, diag.range.start);
  return block ? { kind: 'block', blockId: block.id } : null;
}
