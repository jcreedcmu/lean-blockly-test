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
 * - no `target` → the block's own range.
 * - `target` (a statement-input name) with content → the span from the first
 *   child's start to the **last** child's end (walking the `.next` chain).
 * - `target` whose arm is empty → the synthesized placeholder position the
 *   codegen emits under `emptyArmId`.
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

  const block = findBlockInWorkspace(workspace, blockId);
  const first = block?.inputs?.[target]?.block;
  if (!first) {
    // Empty arm: the placeholder the codegen emits, keyed synthetically.
    return range(byId.get(emptyArmId(blockId, target)));
  }

  // Non-empty arm: span the first child's start to the last child's end.
  const last = lastInChain(first);
  const startInfo = first.id ? byId.get(first.id) : undefined;
  const endInfo = last.id ? byId.get(last.id) : undefined;
  if (!startInfo || !endInfo) return undefined;
  return { startLineCol: startInfo.startLineCol, endLineCol: endInfo.endLineCol };
}
