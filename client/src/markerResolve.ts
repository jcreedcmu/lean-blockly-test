import type { BlocklyState } from './Blockly';
import {
  emptyArmId,
  type SourceInfo,
  type SerializedBlock,
  type SerializedWorkspace,
} from './workspaceToLean';

/** A resolved source range for a goal-position marker. Unlike `SourceInfo`
 * there is no single block id, because an arm's range may span several blocks. */
export interface MarkerLocation {
  startLineCol: [number, number];
  endLineCol: [number, number];
}

/** Find the block with `id` anywhere under `block` (its inputs and next-chain). */
function findBlock(block: SerializedBlock | undefined, id: string): SerializedBlock | undefined {
  if (!block) return undefined;
  if (block.id === id) return block;
  if (block.inputs) {
    for (const input of Object.values(block.inputs)) {
      const found = findBlock(input.block ?? input.shadow, id);
      if (found) return found;
    }
  }
  return findBlock(block.next?.block, id);
}

function findBlockInWorkspace(workspace: BlocklyState, id: string): SerializedBlock | undefined {
  const ws = workspace as SerializedWorkspace;
  for (const top of ws.blocks?.blocks ?? []) {
    const found = findBlock(top, id);
    if (found) return found;
  }
  return undefined;
}

/** The last block in a `.next` chain starting at `block`. */
function lastInChain(block: SerializedBlock): SerializedBlock {
  let cur = block;
  while (cur.next?.block) cur = cur.next.block;
  return cur;
}

/**
 * Resolve a goal-position marker (`blockId` + `target`) to a source range in
 * the generated contribution text:
 *
 * - no `target` → the block's own range (e.g. `intro`, whose start is the
 *   goal-entering position the marker names).
 * - `target` with a codegen `skip` anchor → that anchor's range. This is the
 *   narrow constant-goal position at the arm's end. Blocks on the
 *   trailing-anchor model (lemma, constructor arms) always emit it; empty arms
 *   of any block always emit it too.
 * - `target` with content but **no** anchor (blocks not yet migrated, e.g.
 *   have/show/transform) → the span from the first child's start to the
 *   **last** child's end (walking the `.next` chain).
 *
 * Pure over the serialized workspace + `sourceInfo`, so it is unit-testable
 * without a live Blockly workspace. Returns undefined if the block or position
 * can't be found in `sourceInfo`.
 */
export function resolveMarkerLocation(
  workspace: BlocklyState,
  sourceInfo: SourceInfo[],
  blockId: string,
  target: string,
): MarkerLocation | undefined {
  const byId = new Map(sourceInfo.map((s) => [s.id, s]));
  const range = (s: SourceInfo | undefined): MarkerLocation | undefined =>
    s ? { startLineCol: s.startLineCol, endLineCol: s.endLineCol } : undefined;

  if (!target) {
    // Self: the block's own generated range.
    return range(byId.get(blockId));
  }

  // Prefer the codegen-emitted `skip` anchor for this arm, when present. It's
  // the canonical narrow range; always present for empty arms and for arms of
  // blocks migrated to the trailing-anchor model.
  const anchor = byId.get(emptyArmId(blockId, target));
  if (anchor) return range(anchor);

  // Fallback (un-migrated non-empty arm): span first child's start to last
  // child's end.
  const block = findBlockInWorkspace(workspace, blockId);
  const first = block?.inputs?.[target]?.block;
  if (!first) return undefined;
  const last = lastInChain(first);
  const startInfo = first.id ? byId.get(first.id) : undefined;
  const endInfo = last.id ? byId.get(last.id) : undefined;
  if (!startInfo || !endInfo) return undefined;
  return { startLineCol: startInfo.startLineCol, endLineCol: endInfo.endLineCol };
}

/**
 * The *governed region* of a status pill: the broad source span a goal-state
 * diagnostic must fall within to be attributed to this pill. Unlike
 * {@link resolveMarkerLocation} (which gives the narrow constant-goal *anchor*
 * for the forward query), this spans the arm's whole body so a diagnostic
 * reported anywhere from the arm's first tactic down to the trailing `skip`
 * anchor still matches.
 *
 * - constructor arm (`BODY1`/`BODY2`): the bullet's first tactic … the arm's
 *   anchor (the two arms get disjoint regions — neither claims the shared
 *   `constructor` line).
 * - wrapper proof (`LEMMA_PROOF`/`PROOF` on lemma/have/show/transform): the
 *   block's own header line (so a diagnostic at `:= by` is included) … the
 *   proof's end.
 *
 * Returns undefined for a position marker (no `target`) or when ranges can't be
 * resolved. Pure over the serialized workspace + `sourceInfo`.
 */
export function governedRegion(
  workspace: BlocklyState,
  sourceInfo: SourceInfo[],
  blockId: string,
  target: string,
): MarkerLocation | undefined {
  if (!target) return undefined;
  const byId = new Map(sourceInfo.map((s) => [s.id, s]));

  const anchor = byId.get(emptyArmId(blockId, target));
  const block = findBlockInWorkspace(workspace, blockId);
  const first = block?.inputs?.[target]?.block;

  let startLineCol: [number, number] | undefined;
  let endLineCol: [number, number] | undefined;

  if (first) {
    const startInfo = first.id ? byId.get(first.id) : undefined;
    const last = lastInChain(first);
    const endInfo = last.id ? byId.get(last.id) : undefined;
    startLineCol = startInfo?.startLineCol;
    endLineCol = (anchor ?? endInfo)?.endLineCol;
  } else if (anchor) {
    // Empty arm: the region is just the synthesized `skip` line.
    startLineCol = anchor.startLineCol;
    endLineCol = anchor.endLineCol;
  }

  // A wrapper proof's pill governs the whole block: extend the region up to the
  // block's header so a `:= by`-positioned diagnostic is attributed here. Arm
  // pills (BODY1/BODY2) must NOT swallow the shared `constructor` line.
  const isArm = target === 'BODY1' || target === 'BODY2';
  if (!isArm) {
    const own = byId.get(blockId);
    if (own) startLineCol = own.startLineCol;
  }

  if (!startLineCol || !endLineCol) return undefined;
  return { startLineCol, endLineCol };
}
