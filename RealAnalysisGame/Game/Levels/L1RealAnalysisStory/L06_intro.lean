import Game.Metadata

World "RealAnalysisStory"
Level 6
Title "The intro tactic"

Introduction "
# Universal statements

In mathematics, we often need to prove statements that are true \"for all\" values of some variable. For example, we might want to prove: \"for all $\\varepsilon > 0$, we have $(\\varepsilon + 1)^2 = (\\varepsilon + 1)^2$.\"

If you're thinking that `rfl` will do the trick, that's a good idea, but it won't work, because the goal isn't (yet) an equality. So we need to do something else first.

In Lean, \"for all\" is written using `∀` (the *universal quantifier*).

To prove a \"for all\" statement, you need to show that it's true for an arbitrary element. The syntax is the command `intro`, followed by whatever name you want to give a dummy variable or a hypothesis.

So: when you see a goal that starts with `∀`, you can write `intro` to \"introduce\" the variable. For example:
- `intro ε` introduces the variable ε.
- Then `intro hε` introduces the hypothesis that `ε > 0`.

After using `intro` twice, the goal will become one that you should know how to solve.

If you want to be really slick, you can combine the two `intro` commands into one: `intro ε hε`.
"

/-- The `intro` tactic introduces variables and hypotheses from ∀ statements or implications. -/
TacticDoc intro

Statement : ∀ ε : ℝ, ε > 0 → (ε + 1)^2 = (ε + 1)^2 := by
  intro ε
  intro h
  rfl

NewTactic intro

AllowBlock "tactic_intro"

Conclusion "
Excellent! You've learned the `intro` tactic for universal statements.

Notice what happened:
1. `intro ε` introduced the arbitrary real number ε
2. `intro hε` introduced the hypothesis `hε : ε > 0`
3. The goal became `(ε + 1)^2 = (ε + 1)^2`
4. `rfl` solved the goal

The `intro` tactic is absolutely crucial in real analysis. You'll use it constantly to:
- Handle \"for all ε > 0\" statements in limit definitions
- Introduce arbitrary points in domain/range proofs
- Work with function definitions
"
