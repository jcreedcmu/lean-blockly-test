import Game.Metadata

World "RealAnalysisStory"
Level 1
Title "The \"apply\" Tactic"

Introduction "
# Your First Formal Proof

In this Tutorial World, we are learning how to build formal proofs with blocks. This first level is deliberately tiny. You are given a real number `x` and an assumption, called `h` (but we could have called it just about anything, like `Alice`), that `x = 5`. Your Goal is to prove this same fact, that `x = 5`.

In ordinary mathematical writing, we might say: \"This follows immediately from the assumption.\" In this Game, we refer to assumptions by name. The tactic for \"this follows immediately\" is called `apply`.

So the formal proof is simply:

`apply h`
"

/-- The `apply` tactic solves a goal when one of the hypotheses is the same as the goal. -/
TacticDoc apply

Statement (x : ℝ) (h : x = 5) : x = 5 := by
  apply h

NewTactic apply

AllowBlock "prop" "tactic_apply"

TheoremBlockLabel "Example"

Conclusion "
Perfect! You've completed your first Lean proof involving real numbers.

Remember: the `apply` tactic is used when you have what you need to prove the goal. Look at the top right: your list of tactics now includes `apply`, and if you forget how it works or what it does, just click on it for a reminder.
"
