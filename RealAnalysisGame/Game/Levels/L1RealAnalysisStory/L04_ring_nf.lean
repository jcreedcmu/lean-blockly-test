import Game.Metadata

World "RealAnalysisStory"
Level 4
Title "The ring_nf tactic"

Introduction "
# Algebraic manipulations

Now let's learn about algebraic simplification. Suppose you need to prove that $(x + y)^3 = x^3 + 3x^2y + 3xy^2 + y^3$.

This is true by the basic laws of algebra - expanding the left side using the distributive law, commutativity, associativity, etc. But doing this by hand would be extremely tedious.

Fortunately, Lean has a powerful tactic called `ring_nf` (\"ring normal form\") that can automatically perform algebraic manipulations like:
- Expanding products
- Collecting like terms
- Rearranging using commutativity and associativity
- Applying the distributive law

When you have an algebraic identity involving addition, subtraction, and multiplication, `ring_nf` can often prove it automatically.

Try it out on this classic binomial expansion!
"

/-- The `ring_nf` tactic puts both sides of an equation into a standard algebraic form and checks if they're equal. -/
TacticDoc ring_nf

Statement (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  ring_nf

NewTactic ring_nf

AllowBlock "tactic_ring_nf"
AllowAllAffordances

Conclusion "
Excellent! You've learned the `ring_nf` tactic.

This tactic is incredibly powerful for algebraic manipulations. It automatically handles all the tedious algebra that would take many steps to do by hand.

Your toolkit now includes:
- `apply hypothesis_name` for when a hypothesis matches your goal
- `rfl` for proving something equals itself
- `rewrite [hypothesis_name]` for rewriting using equalities
- `ring_nf` for algebraic simplifications and expansions

As we move into real analysis proper, you'll find that `ring_nf` is invaluable for dealing with polynomial expressions, which appear everywhere in calculus!
"
