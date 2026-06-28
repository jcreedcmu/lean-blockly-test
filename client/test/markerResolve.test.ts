/**
 * Unit tests for resolveMarkerLocation — mapping a goal-position marker
 * (blockId + target) to a source range, over a serialized workspace +
 * sourceInfo. We hand-construct both so the tests are independent of Blockly
 * and of the codegen's exact output.
 */
import { resolveMarkerLocation } from '../src/markerResolve';
import { emptyArmId, type SourceInfo } from '../src/workspaceToLean';
import type { BlocklyState } from '../src/Blockly';

// ── Builders ────────────────────────────────────────────────────────

type Block = {
  type: string;
  id?: string;
  inputs?: Record<string, { block?: Block }>;
  next?: { block?: Block };
};

function workspace(...topBlocks: Block[]): BlocklyState {
  return { blocks: { languageVersion: 0, blocks: topBlocks } } as BlocklyState;
}

/** Chain tactic blocks with the given ids into a `.next` stack. */
function chain(...ids: string[]): Block | undefined {
  let block: Block | undefined;
  for (const id of [...ids].reverse()) {
    block = { type: 't', id, ...(block ? { next: { block } } : {}) };
  }
  return block;
}

function si(id: string, start: [number, number], end: [number, number]): SourceInfo {
  return { id, startLineCol: start, endLineCol: end };
}

// A constructor with a 3-tactic BODY1 and an empty BODY2. Under the
// trailing-anchor model the codegen emits a `skip` anchor at the end of each
// arm, keyed by `emptyArmId`: BODY1's after t3, BODY2's as the `· skip` bullet.
const ws = workspace({
  type: 'tactic_constructor',
  id: 'C',
  inputs: { BODY1: { block: chain('t1', 't2', 't3') } },
});

const sourceInfo: SourceInfo[] = [
  si('C', [4, 0], [4, 18]),
  si('t1', [5, 2], [5, 8]),
  si('t2', [6, 2], [6, 10]),
  si('t3', [7, 2], [7, 6]),
  si(emptyArmId('C', 'BODY1'), [8, 4], [8, 8]),
  si(emptyArmId('C', 'BODY2'), [9, 4], [9, 8]),
];

// ── Tests ───────────────────────────────────────────────────────────

test('self (no target) → the block’s own range', () => {
  expect(resolveMarkerLocation(ws, sourceInfo, 'C', '')).toEqual({
    startLineCol: [4, 0],
    endLineCol: [4, 18],
  });
});

test('filled arm → its `skip` anchor (not the tactic span)', () => {
  // The anchor is the canonical narrow range at the arm's end, regardless of
  // how many tactics precede it.
  expect(resolveMarkerLocation(ws, sourceInfo, 'C', 'BODY1')).toEqual({
    startLineCol: [8, 4],
    endLineCol: [8, 8],
  });
});

test('single-tactic arm → its `skip` anchor', () => {
  const ws1 = workspace({
    type: 'tactic_constructor',
    id: 'D',
    inputs: { BODY1: { block: chain('only') } },
  });
  const si1 = [
    si('D', [0, 0], [0, 5]),
    si('only', [1, 2], [1, 9]),
    si(emptyArmId('D', 'BODY1'), [2, 4], [2, 8]),
  ];
  expect(resolveMarkerLocation(ws1, si1, 'D', 'BODY1')).toEqual({
    startLineCol: [2, 4],
    endLineCol: [2, 8],
  });
});

test('empty arm → the synthesized `skip` anchor position', () => {
  expect(resolveMarkerLocation(ws, sourceInfo, 'C', 'BODY2')).toEqual({
    startLineCol: [9, 4],
    endLineCol: [9, 8],
  });
});

test('un-migrated arm with no anchor → first-start … last-end span (fallback)', () => {
  // `have` is not on the trailing-anchor model, so its filled PROOF arm has no
  // `emptyArmId` entry and resolves via the arm-span fallback (first child's
  // start to the LAST child's end).
  const nested = workspace({
    type: 'tactic_constructor',
    id: 'C',
    inputs: {
      BODY1: {
        block: {
          type: 'tactic_have',
          id: 'h',
          inputs: { PROOF: { block: chain('p1', 'p2') } },
        },
      },
    },
  });
  const nsi = [
    si('h', [1, 0], [1, 10]),
    si('p1', [2, 2], [2, 8]),
    si('p2', [3, 2], [3, 9]),
  ];
  expect(resolveMarkerLocation(nested, nsi, 'h', 'PROOF')).toEqual({
    startLineCol: [2, 2],
    endLineCol: [3, 9],
  });
});

test('unknown block / missing sourceInfo → undefined', () => {
  expect(resolveMarkerLocation(ws, sourceInfo, 'nope', '')).toBeUndefined();
  expect(resolveMarkerLocation(ws, sourceInfo, 'C', 'NO_SUCH_INPUT')).toBeUndefined();
});
