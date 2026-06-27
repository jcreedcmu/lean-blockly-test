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

// A constructor with a 3-tactic BODY1 and an empty BODY2.
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
  si(emptyArmId('C', 'BODY2'), [8, 2], [8, 8]),
];

// ── Tests ───────────────────────────────────────────────────────────

test('self (no target) → the block’s own range', () => {
  expect(resolveMarkerLocation(ws, sourceInfo, 'C', '')).toEqual({
    startLineCol: [4, 0],
    endLineCol: [4, 18],
  });
});

test('multi-tactic arm → first tactic start … LAST tactic end', () => {
  expect(resolveMarkerLocation(ws, sourceInfo, 'C', 'BODY1')).toEqual({
    startLineCol: [5, 2], // t1 start
    endLineCol: [7, 6],   // t3 end (not t1 end — this is the bug being fixed)
  });
});

test('single-tactic arm → that tactic’s range', () => {
  const ws1 = workspace({
    type: 'tactic_constructor',
    id: 'D',
    inputs: { BODY1: { block: chain('only') } },
  });
  const si1 = [si('D', [0, 0], [0, 5]), si('only', [1, 2], [1, 9])];
  expect(resolveMarkerLocation(ws1, si1, 'D', 'BODY1')).toEqual({
    startLineCol: [1, 2],
    endLineCol: [1, 9],
  });
});

test('empty arm → the synthesized placeholder position', () => {
  expect(resolveMarkerLocation(ws, sourceInfo, 'C', 'BODY2')).toEqual({
    startLineCol: [8, 2],
    endLineCol: [8, 8],
  });
});

test('nested arm (block id inside another arm) is found', () => {
  // `C` contains t1→t2→t3; give t2 its own arm BODY and resolve through it.
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
