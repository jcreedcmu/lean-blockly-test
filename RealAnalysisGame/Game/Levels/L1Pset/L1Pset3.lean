import Game.Metadata

World "L1Pset"
Level 3
Title "Problem 3"

Introduction "
# Problem 3

You've just learned to add any necessary
auxiliary
facts to the list of hypotheses via the
`have` tactic.
In this problem,
you might find the following new idea useful.

You already know that if you
have a hypothesis `h : X = Y`, and the Goal
contains `X`, then if you `rewrite [h]`,
then any instances of `X` in the goal
get replaced by `Y`.
But what if you have another hypothesis `h2`,
and you want to replace `X`'s in `h2` by `Y`s, what should you do then?
Elementary, my dear Watson!
You simply type:

`rewrite [h] at h2`.

So the syntax is `rewrite [h]` as before, then
the word `at`, and finally the name of the
hypothesis where you want the rewriting to happen.
Similarly, you can say `ring_nf at h2`,
and any algebra in hypothesis `h2` will be put into normal form.

Now you should be able to solve this problem!
"

/-- Solve the problem -/
Statement (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3)
 (h2 : g (0) = 5) : g (1) = 8 := by
  specialize h1 0
  rewrite [h2] at h1
  ring_nf at h1
  apply h1

Conclusion "Done."
