/**
 * Unit tests for resolveProofStatuses — the backward direction: mapping
 * goal-state diagnostics to the status pill that governs the position. We
 * hand-build the workspace + sourceInfo to mirror the trailing-anchor codegen:
 *
 *   theorem foo ... := by      line 0   (lemma block `L`)
 *     constructor              line 1   (constructor `C`)
 *     · t1                     line 2
 *       skip                   line 3   (emptyArmId C BODY1)
 *     · t2                     line 4
 *       skip                   line 5   (emptyArmId C BODY2)
 *     skip                     line 6   (emptyArmId L LEMMA_PROOF)
 */
import {
  resolveProofStatuses,
  isGoalStateDiagnostic,
  locateDiagnostic,
  pillForPosition,
  type Pill,
  type DiagnosticLike,
} from '../src/proofStatusResolve';
import { emptyArmId, type SourceInfo } from '../src/workspaceToLean';
import type { BlocklyState } from '../src/Blockly';

type Block = {
  type: string;
  id?: string;
  inputs?: Record<string, { block?: Block }>;
  next?: { block?: Block };
};

function workspace(...top: Block[]): BlocklyState {
  return { blocks: { languageVersion: 0, blocks: top } } as BlocklyState;
}
function si(id: string, start: [number, number], end: [number, number]): SourceInfo {
  return { id, startLineCol: start, endLineCol: end };
}
function diag(
  line: number,
  character: number,
  message = 'unsolved goals\n⊢ P',
  severity = 1,
): DiagnosticLike {
  return {
    range: { start: { line, character }, end: { line, character: character + 1 } },
    message,
    severity,
  };
}

const ws = workspace({
  type: 'lemma',
  id: 'L',
  inputs: {
    LEMMA_PROOF: {
      block: {
        type: 'tactic_constructor',
        id: 'C',
        inputs: {
          BODY1: { block: { type: 't', id: 't1' } },
          BODY2: { block: { type: 't', id: 't2' } },
        },
      },
    },
  },
});

const sourceInfo: SourceInfo[] = [
  si('L', [0, 0], [0, 20]),
  si('C', [1, 2], [1, 13]),
  si('t1', [2, 4], [2, 9]),
  si('t2', [4, 4], [4, 9]),
  si(emptyArmId('C', 'BODY1'), [3, 4], [3, 8]),
  si(emptyArmId('C', 'BODY2'), [5, 4], [5, 8]),
  si(emptyArmId('L', 'LEMMA_PROOF'), [6, 2], [6, 6]),
];

const pills: Pill[] = [
  { blockId: 'L', target: 'LEMMA_PROOF' },
  { blockId: 'C', target: 'BODY1' },
  { blockId: 'C', target: 'BODY2' },
];

// Broad per-block spans (as computeBlockRanges would produce), nesting L ⊇ C ⊇
// {t1, t2}. Used by locateDiagnostic's block-range fallback.
const blockRanges: SourceInfo[] = [
  si('L', [0, 0], [6, 6]),
  si('C', [1, 2], [5, 8]),
  si('t1', [2, 4], [2, 9]),
  si('t2', [4, 4], [4, 9]),
];

function statusOf(
  r: ReturnType<typeof resolveProofStatuses>,
  blockId: string,
  target: string,
): string | undefined {
  return r.statuses.find((s) => s.blockId === blockId && s.target === target)?.status;
}

test('no goal diagnostics → every pill complete', () => {
  const r = resolveProofStatuses(ws, sourceInfo, pills, []);
  expect(statusOf(r, 'L', 'LEMMA_PROOF')).toBe('complete');
  expect(statusOf(r, 'C', 'BODY1')).toBe('complete');
  expect(statusOf(r, 'C', 'BODY2')).toBe('complete');
});

test('diagnostic inside an arm attributes to the innermost arm pill', () => {
  const r = resolveProofStatuses(ws, sourceInfo, pills, [diag(5, 4)]);
  expect(statusOf(r, 'C', 'BODY2')).toBe('incomplete');
  // The lemma region also encloses line 5, but the arm is innermost.
  expect(statusOf(r, 'C', 'BODY1')).toBe('complete');
  expect(statusOf(r, 'L', 'LEMMA_PROOF')).toBe('complete');
});

test('diagnostic at the `:= by` line attributes to the lemma pill only', () => {
  const r = resolveProofStatuses(ws, sourceInfo, pills, [diag(0, 0)]);
  expect(statusOf(r, 'L', 'LEMMA_PROOF')).toBe('incomplete');
  expect(statusOf(r, 'C', 'BODY1')).toBe('complete');
  expect(statusOf(r, 'C', 'BODY2')).toBe('complete');
});

test('two arms incomplete → both arm pills flip independently', () => {
  const r = resolveProofStatuses(ws, sourceInfo, pills, [diag(3, 4), diag(5, 4)]);
  expect(statusOf(r, 'C', 'BODY1')).toBe('incomplete'); // line 3 ∈ [2,3]
  expect(statusOf(r, 'C', 'BODY2')).toBe('incomplete'); // line 5 ∈ [4,5]
});

test('non-goal-state diagnostics (e.g. type mismatch) are ignored', () => {
  const r = resolveProofStatuses(ws, sourceInfo, pills, [diag(5, 4, 'type mismatch\n…')]);
  expect(statusOf(r, 'C', 'BODY2')).toBe('complete');
  expect(r.unmatched).toHaveLength(0);
});

test('isGoalStateDiagnostic requires severity 1 and the unsolved-goals message', () => {
  expect(isGoalStateDiagnostic(diag(0, 0))).toBe(true);
  expect(isGoalStateDiagnostic(diag(0, 0, 'unsolved goals', 2))).toBe(false); // warning
  expect(isGoalStateDiagnostic(diag(0, 0, 'linarith failed'))).toBe(false);
});

test('a goal diagnostic outside every region is unmatched, not fatal', () => {
  const r = resolveProofStatuses(ws, sourceInfo, pills, [diag(99, 0)]);
  expect(r.unmatched).toHaveLength(1);
  expect(statusOf(r, 'L', 'LEMMA_PROOF')).toBe('complete');
});

test('a pill whose region cannot be resolved is left unknown', () => {
  const r = resolveProofStatuses(
    ws,
    sourceInfo,
    [...pills, { blockId: 'nope', target: 'PROOF' }],
    [],
  );
  expect(statusOf(r, 'nope', 'PROOF')).toBe('unknown');
});

describe('locateDiagnostic', () => {
  test('goal-state diagnostic in an arm → that arm’s pill', () => {
    expect(locateDiagnostic(ws, sourceInfo, blockRanges, pills, diag(5, 4)))
      .toEqual({ kind: 'pill', blockId: 'C', target: 'BODY2' });
  });

  test('goal-state diagnostic at the `:= by` line → the lemma pill', () => {
    expect(locateDiagnostic(ws, sourceInfo, blockRanges, pills, diag(0, 0)))
      .toEqual({ kind: 'pill', blockId: 'L', target: 'LEMMA_PROOF' });
  });

  test('non-goal-state diagnostic on a tactic → narrowest block (the tactic)', () => {
    const err = diag(2, 4, 'type mismatch\n…');
    expect(locateDiagnostic(ws, sourceInfo, blockRanges, pills, err))
      .toEqual({ kind: 'block', blockId: 't1' });
  });

  test('non-goal-state diagnostic on the header line → narrowest block (the lemma)', () => {
    const err = diag(0, 0, 'unexpected token\n…');
    expect(locateDiagnostic(ws, sourceInfo, blockRanges, pills, err))
      .toEqual({ kind: 'block', blockId: 'L' });
  });

  test('a diagnostic contained by no range → null', () => {
    expect(locateDiagnostic(ws, sourceInfo, blockRanges, pills, diag(99, 0))).toBeNull();
  });
});

describe('pillForPosition', () => {
  test('a position inside an arm → that arm’s pill', () => {
    expect(pillForPosition(ws, sourceInfo, pills, { line: 5, character: 4 }))
      .toEqual({ blockId: 'C', target: 'BODY2' });
  });

  test('a position at the `:= by` line → the lemma pill', () => {
    expect(pillForPosition(ws, sourceInfo, pills, { line: 0, character: 0 }))
      .toEqual({ blockId: 'L', target: 'LEMMA_PROOF' });
  });

  test('a position governed by no pill → null', () => {
    expect(pillForPosition(ws, sourceInfo, pills, { line: 99, character: 0 })).toBeNull();
  });
});
