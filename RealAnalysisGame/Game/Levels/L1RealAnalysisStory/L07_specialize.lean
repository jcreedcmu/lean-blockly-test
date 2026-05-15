import Game.Metadata

World "RealAnalysisStory"
Level 7
Title "The specialize tactic"

Introduction "
# Using universal statements

Now let's learn the flip side of `intro`. You have already learned that:
- if you have `∃` in the goal, you write `use` to provide a specific value. And
- if you have `∀` in the goal, you write `intro` to introduce an arbitrary variable

But what if you have `∀` in a *hypothesis* and you want to use it for a particular value?

This is where the `specialize` command comes in. You can write `specialize hf t` to specialize the statement `hf` to the particular value `t`. This transforms `hf` from \"∀ x > 0, f (x) = x²\" into \"t > 0 → f (t) = t²\". You can then write `specialize hf t_pos` to feed in the proof. Or combine: `specialize hf t t_pos`.
"

/-- The `specialize` tactic applies a universal statement in a hypothesis to a specific value. -/
TacticDoc specialize

Statement (t : ℝ) (t_pos : t > 0) (f : ℝ → ℝ) (hf : ∀ x > 0, f (x) = x^2) : f (t) = t^2 := by
  specialize hf t
  specialize hf t_pos
  apply hf

NewTactic specialize

AllowBlock "tactic_specialize" "tactic_specialize1" "tactic_specialize2"

Conclusion "
Great! You've learned the `specialize` tactic.

The pattern is:
- `intro` when you have `∀` in the goal (\"introduce an arbitrary term...\")
- `specialize` when you have `∀` in a hypothesis (\"apply the hypothesis to specific value...\")

This is fundamental in real analysis when working with:
- Function properties that hold \"for all x\"
- Limit definitions involving \"for all ε > 0\"
- Continuity statements
"
