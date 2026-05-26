import Game.Metadata

World "L1Pset"
Level 2
Title "Problem 2"

Introduction "
# Problem 2

In this problem you are asked to show that there is some `c` so that `(x + y) ^ 2 = c`, given that
`x * y = 1` and `x ^ 2 + y ^ 2 = 2`.

You will likely have a hard time solving this problem as is.
You surely can work out what value of
`c` you need. But if you try
`ring_nf`, you won't have control over
how the \"normal form\" chooses to
express things. In fact, the
left-hand side, `(x + y) ^ 2` will
turn into `x * y * 2 + x ^ 2 + y ^ 2`,
which is parsed in this order:

`(((x * y) * 2) + x ^ 2) + y ^ 2`

This means that you *will* be able to
`rewrite [h2]` successfully,
but then you will *not* be able to rewrite by `h1`, because the (invisible) parentheses  go the wrong way. (Hint: If you want to know how things are grouped but don't see parentheses, you can hover your cursor over the text in the Goal State, and Lean will show you the groupings. Try it!)

Now, in natural language, there are times when you might want to
record an auxiliary fact: \"let's
*have* the fact that such and such ...\". The Lean
syntax for this is as follows:

`have NewFactName (Assumptions) : Conclusion := by Proof`

That is, you first write `have`; then give
the new hypothesis a name; then include any
assumptions, like `(x : ℝ)`, meaning, `x`
is a real number, etc (the symbol `ℝ` is written with a backslash, then capital `R`, then space); then you put a colon,
and then state the conclusion; then you
put a colon-equals and the word `by`; and finally you give the proof.

For example, if you wanted to declare
the new fact that, say, for any real `u` and `v`,

`(u + v) ^ 2 = (u ^ 2 + v ^ 2) + 2 * (u * v)`

and you wanted to call this fact `huv` (a hypothesis on `u` and `v`),
and you wanted to prove this fact by
invoking the ring normal form tactic,
 then you would give Lean the command:

`have huv (u v : ℝ) : (u + v) ^ 2 = (u ^ 2 + v ^ 2) + 2 * (u * v) := by ring_nf`

This will add to your list of hypotheses
the fact: `huv : ∀ (u v : ℝ), (u + v) ^ 2 = (u ^ 2 + v ^ 2) + 2 * (u * v)`.

Something like this (if not exactly this)
will be useful to you in solving this problem.
"
/-- The `have` tactic has the following
syntax: `have NewHypothesisName (Assumptions) : Claim := by GiveTheProof`.
This creates a new hypothesis called
`NewHypothesisName : ∀ (Assumptions), ClaimHolds`.
 -/
TacticDoc «have»

/-- Show that there exists a constant `c` so that, for any real numbers `x` and `y` with `x ^ 2 + y ^ 2 = 2` and `x * y = 1`, we have `(x + y) ^ 2 = c`. -/
Statement :
 ∃ c, ∀ x y : ℝ, x ^ 2 + y ^ 2 = 2 → x * y = 1 → (x + y) ^ 2 = c := by
  use 4
  intro x y
  Hint (hidden := true) "If you're stuck at this point, let me remind you that, in a previous level, the Goal was: `∀ ε > 0, BlahBlah`, and
  after `intro ε`, the Goal became `ε > 0 → BlahBlah`.
  Then what did you do?..."
  intro h1 h2
  have hxy : (x + y) ^ 2 = (x ^ 2 + y ^ 2) + 2 * (x * y) := by ring_nf
  rewrite [hxy]
  rewrite [h1]
  rewrite [h2]
  ring_nf

NewTactic «have»

Conclusion "Did you end up using `huv`?
And then `specialize`ing it with `u` and `v` replaced, respectively, by `x` and `y`?
Or did you think of going via the more direct route:
`have hxy : (x + y) ^ 2 = (x ^ 2 + y ^ 2) + 2 * (x * y) := by ring_nf`?"
