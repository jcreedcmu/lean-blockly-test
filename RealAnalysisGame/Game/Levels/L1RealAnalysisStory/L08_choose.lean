import Game.Metadata

World "RealAnalysisStory"
Level 8
Title "The choose tactic"

Introduction "
# Extracting information from existential quantifiers

Now let's learn the counterpart to `use`. You know that if you have `∃` in the goal, you write `use` to provide a specific value.

But suppose you have a *hypothesis* that says \"there exists a real number `c` such that `f (c) = 2`\". In Lean, this looks like:
`h : ∃ (c : ℝ), f c = 2`

If you know from `h` that at least one such `c` exists, how do you *choose* one? The syntax is:

`choose c hc using h`.

You need to give a name to both the value of `c`, and to the hypothesis with which `c` is bundled (here we named it `hc`).

You should be able to figure out how to solve the goal from here.
"

/-- The `choose` tactic extracts a witness from an existence statement in a hypothesis. -/
TacticDoc choose

Statement (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  choose c hc using h
  use c
  rewrite [hc]
  ring_nf

NewTactic choose

AllowBlock "tactic_choose"

Conclusion "
Excellent! You've learned the `choose` tactic for working with existence in hypotheses.

The symmetry is beautiful:
- `use` when you have `∃` in the goal (\"here's my specific example\")
- `choose` when you have `∃` in a hypothesis (\"let me unpack this existence claim\")

|           | ∀        | ∃      |
|-----------|----------|--------|
| **Goal**  | `intro`    | `use`    |
| **Hypothesis** | `specialize` | `choose` |
"
