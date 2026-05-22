# Game Redesign Proposal

This is a topic-first redesign of the current lecture levels. The goal is to
replace classroom-date worlds with mathematical worlds: each world should teach
one coherent cluster of ideas, and, when possible, end with a satisfying
`Big Boss` theorem.

The proposal keeps the existing levels in roughly their current mathematical
order, but it moves proof-tool levels to where they support the story and
splits long lecture runs into better subtopics.

## Design Principles

- A world should have a mathematical identity, not a lecture number.
- A world should usually end with a boss theorem. If the current material does
  not yet have a good endpoint, this file marks the missing boss explicitly.
- Earlier worlds should unlock concepts that are genuinely used later.
- Tactic tutorials should be front-loaded only when they are general proof
  grammar; specialized tactics can appear inside the world that needs them.
- Problem-set levels are not included here, but many would make good optional
  side quests attached to these worlds.

## Proposed Dependency Graph

```text
Core sequence and real-number spine:

Proof Tutorial
  -> Intro to Sequences
    -> Absolute Values and Squeeze
      -> Algebraic Limit Theorems
        -> Cauchy Sequences
          -> Subsequences
            -> Bolzano-Weierstrass
              -> The Real Numbers

Series branch:

The Real Numbers
  -> Intro to Series
    -> Absolute and Alternating Series
      -> Riemann Rearrangement
        -> Conditional Convergence (optional side world)

Calculus branch:

The Real Numbers
  -> Function Limits and Continuity
    -> Derivatives
    -> Riemann Sums
      -> Uniformity
        -> Topology and Compactness
          -> Heine-Borel
            -> Continuous Functions Are Integrable
              -> Calculus Capstone / FTC

Optional advanced branch:

Intro to Series + Derivatives
  -> Taylor Series
    -> Fourier Series (optional expansion)

Taylor Series also benefits from Uniformity.
Fourier Series also depends on Integration/Uniformity.
```

## World Plan

### 1. Proof Tutorial

Purpose: give the player the nine proof moves they will use throughout the game,
presented as natural-language actions rather than tactic names.

`ring`, `rfl`, and `ring_nf` are intentionally absent: students should never
need them. All arithmetic is discharged by `conclude [...]`.

`intro` is split into two named levels because the two uses are pedagogically
distinct: **fix** introduces a universally-quantified object ("fix an arbitrary
real number x"), while **assume** introduces a hypothesis from an implication
("assume h : P"). Similarly `specialize` is split: **plug** fills a term slot
("plug in x = 3"), while **feed** supplies a proof ("feed the assumption h").

Proposed levels (10 total):

**Level 1 — apply**
The goal is a statement that follows immediately from a single named theorem or
hypothesis. The player drags `apply` and snaps the right theorem bubble into it.
Example: given `h : x = 2` and a goal of `x = 2`, write `apply h`.
Teaches: the basic shape of a proof step; how `apply` closes a goal of the identical shape (there is no need for `exact` and we will later see "fancier" uses of `apply`).

**Level 2 — rewrite**
The goal mentions a sub-expression that a hypothesis equates to something
simpler. The player rewrites with that hypothesis.
Example: given `h : x = 2`, prove a goal involving `x` by rewriting by `h`.
Teaches: substitution; how `rewrite` transforms the goal rather than closing it
directly.

**Level 3 — calc**
The goal is an equality or inequality that requires a two-step chain.
Example: given `h₁ : a ≤ b` and `h₂ : b < c`, prove `a + 1 ≤ c + 1` via
`have h := (calc a + 1 ≤ b + 1 using [h₁]; _ ≤ c + 1 using [h₂])`.
Now `apply h`.
Teaches: chained reasoning; how each step of a calc block carries its own
`[...]` justification.

**Level 4 — use**
The goal is `∃ x, P x`. The player must choose a concrete witness.
Example: prove `∃ n : ℕ, n > 5` by using `n = 6`.
Teaches: existential introduction; the idea that to prove existence you produce
a specific example.

**Level 5 — choose**
A hypothesis has the form `∃ x, P x`. The player uses `choose` to extract a
name and a proof.
Example: given `h : ∃ N, ∀ n > N, a n > 0`, extract `N` and `hN`.
Teaches: existential elimination; how `choose` gives you a usable object from an
existence claim.

**Level 6 — fix**
The goal begins `∀ x : ℝ, ...`. The player uses `fix` (the `intro` block) to
name the arbitrary real number.
Example: prove `∀ x : ℝ, x + 0 = x` by fixing `x` and concluding.
Teaches: universal introduction for objects ("fix an arbitrary x").

**Level 7 — assume**
The goal begins `P → Q`. The player uses `assume` (also the `intro` block, but
applied to a proposition) to add `h : P` as a local hypothesis.
Example: prove `x > 0 → x ≠ 0` by assuming `hx : x > 0` and concluding.
Teaches: implication introduction ("assume h and show the conclusion").
Also clarifies why `fix` and `assume` are the same tactic at two different types.

**Level 8 — plug**
A hypothesis has the form `∀ x, P x` and the player needs `P` at a specific
value. The player uses `specialize h to (val)` to plug in that value.
Example: given `h : ∀ n : ℕ, a n ≥ 0`, specialize to `n = N`.
Teaches: universal elimination for objects.

**Level 9 — feed**
A hypothesis has the form `P → Q` and the player already has a proof of `P`.
The player uses `specialize h to (hP)` to feed the proof and obtain `Q`.
Example: given `h : x > 0 → x ≠ 0` and `hx : x > 0`, feed `hx` to get `h : x ≠ 0`.
Teaches: modus ponens / implication elimination.
Also clarifies why `plug` and `feed` are the same tactic at two different types.

**Level 10 — Big Boss**
A pure-logic puzzle that requires all nine moves in concert, with no analysis
definitions needed. The existing boss is:

> Given `f : ℝ → ℝ`, `hf₁ : ∃ a, f a = 3`, and
> `hf₂ : ∀ x > 0, f (x + 1) = f x + 9`, prove
> `∃ b, ∀ y > 0, f (y + 1)² = (f y + (f b)²)²`.

Solution sketch: choose `a` from `h₁`; use `a` as the witness for
`b`; fix `y` and assume `hy`; plug `y` into `hf₂`; feed `hy` into `hf₂`; now 
`calc f (y + 1)² = (f y + 9)² using hf₂

`

Boss: existing `RealAnalysisStory_9`.

Notes: `choose` appears here even though its heavy use is in the subsequence
world. Seeing it once early means the player is not surprised when the
subsequence world leans on it hard. The subsequence world can then
reintroduce `choose ... using ...` as a refinement.

### 2. Intro to Sequences

Purpose: introduce epsilon definitions, basic examples, nonconvergence, and
the first algebraic limit theorem.

Current levels to include:

- `The Convergence of a Sequence`: `SeqLim`, `ConstLim`
- `Archimedean Property`: quote `ArchProp` as an available fact for now;
  introduce `push_cast` and `bound` through its use rather than proving it here
- `First Real Limit`: `OneOverNLimZero`, `linarith`, `field_simp`,
  `exact_mod_cast`
- `NonConvergence`: `SeqConv`, `(-1)^n` does not converge
- `Doubling a Convergent Sequence`: scalar multiplication by `2`
- `Split Ands`: conjunction goals, if not moved into Tutorial
- `Big Boss: The Sum of Convergent Sequences`: `SumLim`

Boss: `SumLim`.

Notes: this world should be the first place where epsilon bookkeeping feels
like a reusable pattern rather than a one-off computation.

Later return: after constructing the real numbers, add a level proving
`ArchProp` from completeness. The early sequence world should borrow this fact;
the real-number world should eventually explain why the borrowing was justified.

### 3. Absolute Values and Squeeze

Purpose: teach the logic and inequalities needed to turn absolute-value
closeness into ordinary order estimates.

Current levels to include:

- `Left and Right`: disjunction goals
- `Dot Notation`: extracting hypotheses from conjunctions
- `Cases'`: case splitting on disjunctions
- `AbsLe`: `abs_lt`
- `Big Boss: Squeeze Theorem`: `SqueezeThm`

Boss: `SqueezeThm`.

Notes: this is a better home for `left`, `right`, dot notation, and `cases'`
than the algebraic-limit lecture wrapper, because these proof moves are exactly
what make squeeze arguments readable.

### 4. Algebraic Limit Theorems

Purpose: finish the standard algebra of convergent sequences and order
properties of limits.

Current levels to include:

- `Uniqueness of Limits`: `LimUnique`, `by_contra`
- `Eventually`: `EventuallyGeHalfLimPos`
- `Sequences of Absolute Values`: `AbsLim`, `abs_Lipschitz`
- `SeqInvLim`: reciprocal limits
- `ByCases`: `EventuallyGeHalfLim`, `by_cases`
- `Bounded`: `SeqBdd`, `Bdd_of_ConvNonzero`
- `Product of Sequences`: `ProdLimNeNe`
- `Order Limit Theorem`: `SeqBddBy`, `OrderLimLe`

Current boss: `ProdLimNeNe`.

Better future boss: a full algebraic limit theorem package, for example:

- `ProdLim`: product without nonzero hypotheses
- `QuotLim`: quotient limit
- `AlgLimitThm`: a bundled theorem that exposes sum, scalar, product, and
  quotient behavior from one world endpoint

Notes: `Bdd_of_ConvNonzero` currently has a nonzero limit hypothesis. A cleaner
future version should probably prove boundedness of any convergent sequence,
then use it for the product theorem.

### 5. Cauchy Sequences

Purpose: shift from knowing a limit to detecting convergence internally.

Current levels to include:

- `Limits are Cauchy`: `IsCauchy`, `IsCauchy_of_SeqConv`
- `Sums of Cauchy Sequences`: `IsCauchy_of_Sum`
- `Cauchy Implies Bounded`: `IsBdd_of_Cauchy`
- `Monotone and Bounded Implies Cauchy`: `Monotone`,
  `IsCauchy_of_MonotoneBdd`, `push_neg`
- `Iterated Gaps`: technical proof of `IterateGap`

Boss: `IsCauchy_of_MonotoneBdd`.

Notes: in the current files, `IterateGap` is documented before its proof-level
appears. In the redesigned world, the proof should appear before the boss or be
presented as a helper level immediately before the boss.

### 6. Subsequences

Purpose: build subsequences deliberately, then use them to extract monotone
structure.

Current levels to include:

- `Subsequences`: `Subseq`, `SubseqConv`
- `Subsequence Example`: extracting a convergent subsequence of `(-1)^n`,
  `let`
- `Iterated Subsequence`: `succ_iterate`, `subseq_of_succ`,
  `Subseq_of_Iterate`
- `Enhanced Choose`: building subsequences from infinitely many witnesses
- `Monotone Subsequence`: `IsAPeak`, `UnBddPeaks`,
  `MonotoneSubseq_of_BddPeaks`

Boss: `MonotoneSubseq_of_BddPeaks`.

Notes: this world should feel constructive. It starts with what a subsequence
is, then escalates into choosing and iterating index functions.

### 7. Bolzano-Weierstrass

Purpose: combine boundedness, monotone subsequences, and Cauchy behavior into
the central compactness theorem for sequences.

Current levels to include:

- `IsCauchy_of_AntitoneBdd`
- `AntitoneSubseq_of_UnBddPeaks`
- `BolzanoWeierstrass`

Boss: `BolzanoWeierstrass`.

Notes: this can be a short world. That is fine: it is a theorem payoff world,
not a toolbox world.

### 8. The Real Numbers

Purpose: explain why the previous Cauchy technology constructs/completes the
real line.

Current levels to include:

- `Completeness`: `Real_of_CauSeq`, `SeqLim_of_Real_of_Cau`,
  `Reals_are_Complete`

Boss: `Reals_are_Complete`.

Future additions:

- equivalence classes of Cauchy rational sequences, if this becomes playable
- rational density
- proof of `ArchProp` from completeness, closing the loop on the early quoted
  fact
- least upper bound property as an analytic theorem here, or later in topology

Notes: the current topology world later proves `HasLUB_of_BddNonempty`.
Pedagogically, that theorem could either live here as "Completeness II" or
remain in topology as the engine for Heine-Borel. I would keep it in topology
for the game flow, but cross-reference it here.

### 9. Intro to Series

Purpose: introduce series as limits of partial sums and prove first convergence
tests/examples.

Current levels to include:

- `Finite Sums`: `range`, `sum_range_succ`, `sum_nonneg`, `TermLeSum`
- `Series`: `Series`, `SeriesLim`, `SeriesConv`,
  `LimZero_of_SeriesConv`
- `Leibniz Series` finite identity
- `Leibniz Series` convergence
- `Series Order Theorem`
- `The Basel Problem`

Boss: current boss should be the Basel comparison proof.

Better future boss:

- `ComparisonTest`
- `GeometricSeries`
- `BaselBound` or a named convergence result for `sum 1 / n^2`

Notes: finite sums appear before series in the current lecture order, and they
should stay early. They are the grammar of all later series worlds.

### 10. Absolute and Alternating Series

Purpose: teach the two main ways series converge before rearrangements.

Current levels to include:

- `Absolute Convergence Implies Convergence`: `AbsSeriesConv`,
  `Conv_of_AbsSeriesConv`
- `Alternating Series Test`: `AlternatingSeriesTest`

Boss: `AlternatingSeriesTest`.

Notes: this world currently depends on several helper theorem docs from pset-like
material (`SeqEvenOdd`, `MonotoneSeriesEven`, etc.). In the redesign, those
helpers should become visible levels, short side quests, or hidden theorem
unlocks immediately before the boss.

### 11. Riemann Rearrangement

Purpose: show why absolute convergence makes infinite addition stable under
reordering.

Current levels to include:

- `More Flexible Cauchy`: `StrongCauchy_of_AbsSeriesConv`
- `Rearrangements`: `Injective`, `Surjective`, `Rearrangement`,
  `EventuallyCovers_of_Rearrangement`
- `Big Boss: Rearrangement Theorem`: `RearrangementThm`

Boss: `RearrangementThm`.

Notes: this is already shaped like a good world.

### 12. Conditional Convergence

Purpose: give the contrasting theorem: conditional convergence is flexible
enough to rearrange to any target.

Status: optional side world branching off `Riemann Rearrangement`.

Current levels to include:

- `Conditional Convergence Theorem`

Boss: the current conditional convergence theorem.

Needs development:

- positive and negative parts of a conditionally convergent series
- choosing enough positive or negative terms to cross a target
- constructing the rearrangement

Notes: this should be a separate world from `Riemann Rearrangement`. The player
should feel the sharp dichotomy: absolute convergence gives invariance;
conditional convergence gives controllable chaos. It should not block the main
calculus route, and it needs further development before it becomes cleanly
playable.

### 13. Function Limits and Continuity

Purpose: move from sequences to functions, prove the sequential criterion, and
establish basic continuous-function algebra.

Current levels to include:

- `Limits of Functions`: `FunLimAt`
- `Continuous Functions`: `FunContAt`
- `Sum of Continuous Functions`: `FunContAtAdd`
- `Sequential Criterion for Limits`, forward direction:
  `SeqLim_of_FunLimAt`
- `Sequential Criterion for Limits`, backward direction:
  `FunLim_of_SeqLim`
- `Continuity Everywhere`: `FunCont`
- `Continuous Composition`: `Cont_Comp`

Current boss: `Cont_Comp`.

Better future boss:

- `ContinuousAlgebra`: sums, products, scalar multiples, quotients
- `ContinuousPolynomial`: every polynomial is continuous

Notes: this world should come after real completeness, not just after sequence
manipulation, because it conceptually starts calculus on the completed real
line.

### 14. Derivatives

Purpose: define differentiability and start building derivative calculus.

Current levels to include:

- `Computing a Derivative`: `FunDerivAt`
- `The Derivative Function`: `FunDeriv`

Needs development:

- derivative implies continuity
- constant, identity, sum, product, chain rules
- Fermat's theorem
- Rolle's theorem
- Mean Value Theorem

Boss: future `MeanValueTheorem`.

Notes: right now this is more of a seed than a world. It should eventually be
one of the main roads into the Fundamental Theorem of Calculus.

### 15. Riemann Sums

Purpose: define the Riemann integral via sums, prove simple examples, and make
the player discover exactly why ordinary pointwise continuity is not enough for
the convergence proof.

Current levels to include:

- `Integration`: `RiemannSum`, `HasIntegral`, `IntegrableOn`,
  integrability of `fun x => x`
- `Riemann Sum Refinement`: `RiemannSumRefinement`
- `Integration Converges`: first attempted proof path toward
  `HasIntegral_of_UnifContOn`

Boss: `RiemannSumRefinement`.

Notes: this world should end with a genuine need: to prove integrability of
continuous functions, the estimates have to be uniform across the interval. This
sets up `Uniformity` as a mathematical necessity, not as a detached concept.

### 16. Uniformity

Purpose: introduce uniform convergence and uniform continuity exactly when the
integration proof demands uniform control.

Current levels to include:

- `Uniform Convergence`: `UnifConv`, `Cont_of_UnifConv`
- `Integration Converges`: `UnifContOn`, `HasIntegral_of_UnifContOn`
- `Uniform Convergence Implies Integrability`: `Integrable_of_UnifConv`

Boss: `HasIntegral_of_UnifContOn`.

Notes: the current ordering can still be adjusted internally. The key narrative
point is that uniformity arrives because Riemann sums require one `δ` that
works across many sample points. `Integrable_of_UnifConv` may fit better as an
advanced follow-up after the basic uniform-continuity integration theorem.

### 17. Topology and Compactness

Purpose: introduce open balls, open and closed sets, compactness, and the least
upper bound property because uniform continuity on closed intervals now needs a
source.

Current levels to include:

- `Compactness`: `Ball`, `IsCompact`, `mem_Union`, `FinMinPos`
- `Heine-Borel Part 1a`: compact implies bounded
- `Heine-Borel Part 1b`: compact implies closed
- `Least Upper Bound Property`: `IsUB`, `IsLUB`,
  `HasLUB_of_BddNonempty`

Boss: `HasLUB_of_BddNonempty`, if this is kept inside topology.

Alternative: move `HasLUB_of_BddNonempty` to `The Real Numbers` and make this
world end with `IsClosed_of_Compact`.

### 18. Heine-Borel

Purpose: prove the full compactness characterization for closed bounded
subsets of the real line, then feed it back into uniform continuity and
integration.

Current levels to include:

- `Closed intervals are compact`: `IsCompact_of_ClosedInterval`
- `Closed subsets of compact sets are compact`:
  `IsCompact_of_ClosedSubset`

Boss: a future single theorem, perhaps:

- `HeineBorel`: `IsCompact S <-> IsClosed S /\ Bdd S`
- or, more game-friendly, `IsCompact_of_ClosedBdd`

Notes: the current two levels are strong, but the world wants a final named
theorem that says "this is Heine-Borel" in one place.

### 19. Continuous Functions Are Integrable

Purpose: cash out the just-in-time topology arc by proving that continuous
functions on closed intervals are integrable.

Current levels to include:

- `Compactness`: `UnifContOn_of_Compact`, once `IsCompact` is available
- `Integration Converges`: use `HasIntegral_of_UnifContOn`

Needs development:

- closed intervals are compact as the standard input
- continuous on `[a,b]` implies uniformly continuous on `[a,b]`
- continuous on `[a,b]` implies integrable on `[a,b]`

Boss: future `ContinuousIntegrableOnCompact` or
`ContinuousIntegrableOnClosedInterval`.

Notes: this is the payoff for introducing compactness. The player should first
feel the need for uniformity in Riemann sums, then use Heine-Borel to obtain it
from ordinary continuity on closed intervals.

### 20. Calculus Capstone

Purpose: assemble continuity, compactness, derivatives, and integrals into the
theorems students expect from calculus.

Current levels to include:

- `Intermediate Value Theorem`: `IVT`

Needs development:

- Extreme Value Theorem
- uniform continuity on closed intervals as a corollary of Heine-Borel
- integrability of continuous functions on closed intervals
- Fundamental Theorem of Calculus, Part I
- Fundamental Theorem of Calculus, Part II

Boss: future `FundamentalTheoremOfCalculus`.

Notes: this is the natural ending of the core game. The story started by asking
what makes calculus rigorous; this world should answer that question directly.

## Optional Advanced Worlds

### Taylor Series

Status: recommended optional world.

Why it belongs: the Newton pi story is already in the game, and Taylor series
would reconnect the opening narrative to rigorous convergence.

Likely dependencies:

- `Intro to Series`
- `Absolute and Alternating Series`
- `Derivatives`
- `Uniformity`, if the world proves convergence of Taylor remainders uniformly

Possible boss:

- Taylor's theorem with remainder
- power series are differentiable inside their radius of convergence
- a rigorous version of Newton's binomial expansion

### Fourier Series

Status: optional, probably after the main game.

Why it belongs: Fourier is central to the opening motivation, but a full
Fourier world could easily become a second course.

Likely dependencies:

- `Taylor Series` or at least advanced series maturity
- `Uniformity`
- integration

Possible scope:

- trigonometric polynomial approximation
- pointwise versus uniform convergence
- a carefully chosen example showing why Cauchy's intuition failed

Recommendation: keep Fourier as an epilogue or future expansion, not part of
the first complete game.

## Proposed World Names and Bosses

| Order | World | Current boss | Needs new boss? |
| --- | --- | --- | --- |
| 1 | Proof Tutorial | `RealAnalysisStory_9` (∃/∀ function puzzle) | no |
| 2 | Intro to Sequences | `SumLim` | no |
| 3 | Absolute Values and Squeeze | `SqueezeThm` | no |
| 4 | Algebraic Limit Theorems | `ProdLimNeNe` | yes, full ALT/quotient |
| 5 | Cauchy Sequences | `IsCauchy_of_MonotoneBdd` | probably no |
| 6 | Subsequences | `MonotoneSubseq_of_BddPeaks` | no |
| 7 | Bolzano-Weierstrass | `BolzanoWeierstrass` | no |
| 8 | The Real Numbers | `Reals_are_Complete` | no |
| 9 | Intro to Series | Basel comparison level | yes, named theorem |
| 10 | Absolute and Alternating Series | `AlternatingSeriesTest` | no |
| 11 | Riemann Rearrangement | `RearrangementThm` | no |
| 12 | Conditional Convergence | conditional convergence theorem | optional; needs supporting levels |
| 13 | Function Limits and Continuity | `Cont_Comp` | yes, continuous algebra |
| 14 | Derivatives | none yet | yes, MVT |
| 15 | Riemann Sums | `RiemannSumRefinement` | no |
| 16 | Uniformity | `HasIntegral_of_UnifContOn` | no |
| 17 | Topology and Compactness | `HasLUB_of_BddNonempty` | open: LUB here or in Real Numbers |
| 18 | Heine-Borel | interval/subset compactness | yes, named `HeineBorel` |
| 19 | Continuous Functions Are Integrable | future continuous integrability theorem | yes |
| 20 | Calculus Capstone | `IVT` currently | yes, FTC |
| 21 | Taylor Series | future | yes |
| 22 | Fourier Series | future optional | yes |

## Migration Notes

1. Create new world wrapper files by topic, for example
   `Game/Levels/W01_ProofTutorial.lean`, rather than mutating the old lecture
   wrappers immediately.
2. Move or re-export existing level files gradually. The old files can keep
   their physical paths while the new wrappers import them in redesigned order.
3. Introduce new dependencies according to the graph above. Avoid making every
   world import all previous worlds; that will hide missing prerequisite
   structure.
4. Add explicit boss levels where the current material ends abruptly:
   algebraic limits, series comparison, continuous algebra, derivatives,
   Heine-Borel, continuous integrability, and FTC.
5. Once the topic worlds compile, update `Game.lean` to import the topic
   wrappers and define dependencies between topic worlds instead of lecture
   worlds.

## Highest-Value New Levels

If we want the redesign to feel complete without boiling the ocean, these are
the best next additions:

- `Bdd_of_Conv`: remove the nonzero-limit restriction from boundedness.
- `ProdLim`: product theorem without nonzero hypotheses.
- `QuotLim`: quotient theorem.
- `ComparisonTest`: a reusable series comparison theorem.
- `ArchProp`: prove the Archimedean property from completeness after the real
  numbers are constructed.
- `HeineBorel`: closed and bounded iff compact, or at least
  `IsCompact_of_ClosedBdd`.
- `DerivativeImpliesContinuous`.
- `MeanValueTheorem`.
- `ContinuousIntegrableOnCompact`.
- `FundamentalTheoremOfCalculus`.

That sequence would turn the current excellent skeleton into a genuinely
complete real analysis game arc.
