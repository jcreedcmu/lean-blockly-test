import Game.Metadata

World "RealAnalysisStory"
Level 2
Title "The rfl tactic"

Introduction "
# When things are identical to themselves

Sometimes in mathematics, we need to prove that something equals itself.
"

/-- The `rfl` tactic proves goals of the form `A = A` where both sides are *identical*. -/
TacticDoc rfl

Statement (x y : ℝ) : x ^ 2 + 2 * y = x ^ 2 + 2 * y := by
  rfl

NewTactic rfl

AllowBlock "tactic_refl"

Conclusion "
Excellent! You've learned the `rfl` tactic.
"
