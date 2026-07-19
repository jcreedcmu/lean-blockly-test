/**
 * Unit tests for the "before" goal-marker pill transform. These are pure
 * (no Blockly runtime): we assert that prependGoalMarker rewrites message0 /
 * args0 correctly and that applyBeforePills only touches the intended tactics.
 */
import {
  prependGoalMarker,
  applyBeforePills,
  shouldGetBeforePill,
} from '../src/beforePills';

// Highest %N referenced in a message string (0 if none).
function maxPlaceholder(message0: string): number {
  const nums = [...message0.matchAll(/%(\d+)/g)].map((m) => Number(m[1]));
  return nums.length ? Math.max(...nums) : 0;
}

const MARKER = { type: 'field_goal_marker', name: 'GOAL_AT' };

describe('prependGoalMarker', () => {
  it('adds the marker as %1 for a block with no placeholders', () => {
    const out = prependGoalMarker({ type: 'tactic_refl', message0: 'reflexivity' });
    expect(out.message0).toBe('%1 reflexivity');
    expect(out.args0).toEqual([MARKER]);
  });

  it('shifts a single placeholder up by one', () => {
    const out = prependGoalMarker({
      type: 'tactic_conclude',
      message0: 'conclude %1',
      args0: [{ type: 'input_value', name: 'ARG' }],
    });
    expect(out.message0).toBe('%1 conclude %2');
    expect(out.args0).toEqual([MARKER, { type: 'input_value', name: 'ARG' }]);
  });

  it('shifts every placeholder and keeps message/args in sync', () => {
    const args0 = [{ a: 1 }, { a: 2 }, { a: 3 }];
    const out = prependGoalMarker({ message0: '%1 intro %2 %3', args0 });
    expect(out.message0).toBe('%1 %2 intro %3 %4');
    // One marker + the three originals; placeholder count must match args length.
    expect(out.args0).toHaveLength(4);
    expect(maxPlaceholder(out.message0!)).toBe(out.args0!.length);
  });

  it('handles multi-digit placeholders without corruption', () => {
    const out = prependGoalMarker({ message0: 'x %9 %10 %11' });
    expect(out.message0).toBe('%1 x %10 %11 %12');
  });

  it('does not mutate the input def', () => {
    const def = { type: 'tactic_refl', message0: 'reflexivity' };
    prependGoalMarker(def);
    expect(def.message0).toBe('reflexivity');
    expect(def).not.toHaveProperty('args0');
  });
});

describe('shouldGetBeforePill', () => {
  it('includes every tactic block, even ones with sub-proof pills', () => {
    for (const type of ['tactic_unfold', 'tactic_apply', 'tactic_convert', 'tactic_exact',
      'tactic_use', 'tactic_rewrite', 'tactic_rewrite_at', 'tactic_choose',
      'tactic_at', 'tactic_refl', 'tactic_calc', 'tactic_have', 'tactic_show',
      'tactic_constructor', 'tactic_transform', 'tactic_other']) {
      expect(shouldGetBeforePill({ type, message0: 'x' })).toBe(true);
    }
  });

  it('excludes non-tactic blocks', () => {
    for (const type of ['prop', 'prop_declaration', 'term_nas_split_even_odd', 'lemma']) {
      expect(shouldGetBeforePill({ type, message0: 'x' })).toBe(false);
    }
  });

  it('excludes conv-internal tactic_enter', () => {
    expect(shouldGetBeforePill({ type: 'tactic_enter', message0: 'x' })).toBe(false);
  });

  it('is idempotent: skips blocks that already start with a marker', () => {
    const intro = {
      type: 'tactic_intro',
      message0: '%1 intro %2',
      args0: [{ type: 'field_goal_marker', name: 'GOAL_AT' }, { type: 'field_input' }],
    };
    expect(shouldGetBeforePill(intro)).toBe(false);
    // Applying the transform twice yields the same result as once.
    const once = applyBeforePills([{ type: 'tactic_refl', message0: 'reflexivity' }]);
    const twice = applyBeforePills(once);
    expect(twice).toEqual(once);
  });
});

describe('applyBeforePills', () => {
  it('transforms tactic blocks and passes non-tactics through by identity', () => {
    const refl = { type: 'tactic_refl', message0: 'reflexivity' };
    const prop = { type: 'prop', message0: 'x %1', args0: [{ x: 1 }] };
    const [outRefl, outProp] = applyBeforePills([refl, prop]);

    expect(outRefl.message0).toBe('%1 reflexivity');
    // Untouched defs are returned by identity (no needless copies).
    expect(outProp).toBe(prop);
  });

  it('adds a start pill to a block that already has a sub-proof pill', () => {
    const have = {
      type: 'tactic_have',
      message0: 'have %1 : %2 by %3 %4',
      args0: [
        { type: 'field_monospace_input', name: 'NAME' },
        { type: 'field_monospace_input', name: 'TYPE' },
        { type: 'input_statement', name: 'PROOF' },
        { type: 'field_proof_status', name: 'PROOF_STATUS', target: 'PROOF' },
      ],
    };
    const [out] = applyBeforePills([have]);
    expect(out.message0).toBe('%1 have %2 : %3 by %4 %5');
    const args = out.args0 as Array<{ type: string }>;
    expect(args[0]).toEqual({ type: 'field_goal_marker', name: 'GOAL_AT' });
    // The existing sub-proof pill is preserved (just shifted down the list).
    expect(args.some((a) => a.type === 'field_proof_status')).toBe(true);
  });
});
