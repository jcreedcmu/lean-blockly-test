import Game.Metadata

World "L1Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1"

/-- Given that `f (u) = 2 * u + 1` for all `u`, prove that there exists some `a` such that `f (3) = a`. -/
Statement (f : ℝ → ℝ) (h : ∀ u, f (u) = 2 * u + 1) :
  ∃ a, f (3) = a := by
  use 7
  specialize h 3
  rewrite [h]
  ring_nf

Conclusion "Done."
