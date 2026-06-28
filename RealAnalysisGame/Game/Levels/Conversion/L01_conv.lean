import Game.Metadata

World "Conversion"
Level 1
Title "The conv tactic"

Introduction "
# Zooming in with `conv`

Most tactics act on the *whole* goal. Sometimes, though, you want to rewrite
just one specific part of an expression. The `conv` (short for \"conversion\")
tactic lets you *navigate into* a subexpression and work only there.

In this app: drop a `conv` block into your proof, then **drag a subexpression
of the goal** into it. That creates an `enter` step pointing at exactly the
piece you grabbed, and you can then rewrite inside that focused subexpression.

Here you're given `h : a = b`, and the two sides of the goal differ in just one
spot. Try zooming in with `conv` (or finish it however you like).
"

Statement (a b : ℝ) (h : a = b) : a + a = a + b := by
  rewrite [h]
  rfl

AllowBlock "tactic_conv" "tactic_enter"

Conclusion "
Nice — you've met the `conv` tactic!

`conv` is the tool of choice when an ordinary rewrite would hit the wrong
occurrence, and it's the gateway to precise, surgical term manipulation.
"
