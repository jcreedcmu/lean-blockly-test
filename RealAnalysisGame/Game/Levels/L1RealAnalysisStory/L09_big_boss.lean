import Game.Metadata

World "RealAnalysisStory"
Level 9
Title "Big Boss: The Ultimate Tactic Challenge"

Introduction "
# The Final Challenge

Congratulations! You've learned many fundamental tactics for mathematical reasoning in Lean:
- `apply hypothesisName` for when a hypothesis matches the goal
- `rfl` for reflexivity (proving `X = X`)
- `rewrite [hypothesisName]` for rewriting using equalities
- `ring_nf` for algebraic manipulation
- `use` for providing witnesses to existence statements in goals
- `intro` for handling universal quantifiers in goals
- `specialize` for applying universal statements to specific values in hypotheses
- `choose value hypothesisOnValue using ExistentialHypothesis` for extracting information from existence statements in hypotheses

Here's a little \"Universal/Existential Quantifier Cheat Sheet\":

|           | ∀        | ∃      |
|-----------|----------|--------|
| **Goal**  | `intro`    | `use`    |
| **Hypothesis** | `specialize` | `choose` |

Now it's time for your first **Big Boss** - a problem that requires you to use almost ALL of these tactics in a single proof!
"

Statement (f : ℝ → ℝ) (h_existential : ∃ (a : ℝ), f (a) = 3) (h_universal : ∀ x > 0, f (x + 1) = f (x) + 9) :
  ∃ (b : ℝ), ∀ y > 0, f (y + 1)^2 = (f (y) + (f b)^2)^2 := by
  choose a ha using h_existential
  use a
  intro y
  intro hy
  specialize h_universal y hy
  rewrite [h_universal]
  rewrite [ha]
  ring_nf

Conclusion "
# Victory!

You've defeated the Big Boss and mastered all the fundamental tactics of mathematical reasoning!

**You are now ready to begin your journey to rigorous calculus!**

Welcome to the Introduction to Formal Real Analysis.
"
