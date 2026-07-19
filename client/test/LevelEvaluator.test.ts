import { LevelEvaluator } from '../src/LevelEvaluator';
import type { LeanSessionManager } from '../src/LeanSessionManager';

function evaluator(): LevelEvaluator {
  return new LevelEvaluator({} as LeanSessionManager);
}

describe('LevelEvaluator standalone source', () => {
  test('preserves the explicitly declared helper theorems', () => {
    const source = evaluator().assembleStandaloneSource(
      'example : True := by\n  have h := even_sum_even_terms\n  trivial\n',
    );

    expect(source).toContain('import Mathlib\n');
    expect(source).not.toContain('import MathlibDemo.Preamble');
    expect(source).toContain('theorem even_sum_relation_fibers');
    expect(source).toContain('theorem even_sum_even_terms');
    expect(source).toContain('theorem even_card_of_even_sum_over_odd_terms');
  });
});
