import Mathlib

/-
The goal of this file is to build up the entire Game and test the various closing tactics against the situations in which they occur. They should be just strong enough but not too strong!
-/

macro "split_abs" "[" t:term,* "]" : tactic => `(tactic| (
  simp only [abs_lt, abs_le, $[$t:term],*]
  split_ifs <;> linarith
))

macro "triangle_ineq" : tactic => `(tactic| (
  simp only [abs, max_def]
  split_ifs <;> linarith
))

macro "contradiction" "[" t:term,* "]" : tactic => `(tactic| (
  linarith only [$t,*]
))

macro "conclude" "[" t:term,* "]" : tactic => do
  `(tactic| (iterate 5 (try (first
    | (fail_if_no_progress triangle_ineq)
    | rel [$t,*]
    | (fail_if_no_progress simp [$[$t:term],*]; norm_num)
    | (fail_if_no_progress field_simp [$[$t:term],*])
    | ring_nf | norm_num | norm_cast
    | linarith only [$t,*] | nlinarith only [$t,*]
    | positivity | abel | omega)); done)
    )

--------------- TESTS ----------------------------

-- Problem 1 needs:
example (f : ℝ → ℝ) (c : ℝ) (hf : ∀ x, f x = c) (y : ℝ) : |f y - c| = 0 := by
  -- conclude [hf] -- FAILS!?
  simp [hf] -- SUCCEEDS

-- Problem 3 needs:
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = 1/n) (n : ℕ) : |a n - 0| = 1 / n := by
  -- conclude [ha] -- FAILS!?
  simp [ha] -- SUCCEEDS

-- Problem 3 needs:
example (N : ℕ) (Npos : N > 0) (n : ℕ) (hn : n > N) : (1 : ℝ) / n ≤ 1 / N := by
--  conclude [] -- FAILS; good!
  conclude [hn] -- SUCCEEDS; good

-- `NegOnePowDNC` needs:
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = (-1) ^ n) (N : ℕ) : a (2 * N) = 1 := by
  -- conclude [ha] -- FAILS!?
  simp [ha] -- SUCCEEDS

-- `NegOnePowDNC` needs:
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = (-1) ^ n) (N : ℕ) : a (2 * N + 1) = -1 := by
  -- conclude [] -- FAILS; good!
  conclude [ha] -- SUCCEEDS; good

-- `NegOnePowDNC` needs:
example : (2 : ℝ) = |1 - (-1)| := by
  conclude [] -- SUCCEEDS; good

-- `NegOnePowDNC` needs:
example (L : ℝ) : |1 - (-1)| ≤|1 - L| + |(-1) - L| := by
  conclude [] -- SUCCEEDS; good

-- `NegOnePowDNC` needs:
example (L a2n a2n1 : ℝ) (ha2n : a2n = 1) (ha2n1 : a2n = -1) :
    |1 - L| + |(-1) - L| = |a2n - L| + |a2n1 - L| := by
  -- conclude [] -- SUCCEEDS! It shouldn't
  conclude [ha2n, a2n1] -- SUCCEEDS

-- `NegOnePowDNC` needs:
example (L a2n a2n1 : ℝ) (ha2n : |a2n - L| ≤ 1/2) (ha2n1 : |a2n1 - L| ≤ 1/2) :
    |a2n - L| + |a2n1 - L| ≤ 1/2 + 1/2 := by
  -- conclude [ha2n, a2n1] -- FAILS!?
  linarith only [ha2n, ha2n1] -- SUCCEEDS

-- `DoubleSeqConv` step 0: simple `linarith`
example (ε : ℝ) (hε : ε > 0) : 0 < ε / 2 := by
  -- conclude [hε] -- FAILS!?
  linarith only [hε] -- SUCCEEDS

-- `DoubleSeqConv` step 1: rewrite b n via hb n
example (a b : ℕ → ℝ) (L : ℝ) (N : ℕ) (n : ℕ) (hb : b n = 2 * a n) :
    |b n - 2 * L| = 2 * |a n - L| := by
  -- conclude [] -- SUCCEEDS; it shouldn't!
  conclude [hb] -- SUCCEEDS

-- `DoubleSeqConv` step 2: multiplying an inequality by a positive number
example (a : ℕ → ℝ) (L ε : ℝ) (n : ℕ) (hN : |a n - L| < ε / 2) :
    2 * |a n - L| < 2 * (ε / 2) := by
  -- conclude [hN] -- FAILS!?
  simp [hN] -- SUCCEEDS

-- `SumLim` step 1: rewrite c n via hc n
example (a b c : ℕ → ℝ) (L M : ℝ) (n : ℕ) (hc : c n = a n + b n) :
    |c n - (L + M)| = |a n + b n - (L + M)| := by
  -- conclude [] -- SUCCEEDS; it shouldn't!
  conclude [hc] -- SUCCEEDS

-- `SumLim` step 2: abs of ring-equal expressions
example (a b : ℕ → ℝ) (L M : ℝ) (n : ℕ) :
    |a n + b n - (L + M)| = |(a n - L) + (b n - M)| := by
  conclude [] -- SUCCEEDS (ring_nf normalizes inside abs)

-- `SumLim` step 3: triangle inequality
example (a b : ℕ → ℝ) (L M : ℝ) (n : ℕ) :
    |(a n - L) + (b n - M)| ≤ |a n - L| + |b n - M| := by
  conclude [] -- SUCCEEDS (triangle_ineq)

-- `SumLim` step 4: adding two half-epsilon bounds
-- conclude FAILS: triangle_ineq fires first, expands abs in goal into cases,
-- then linarith can't close them because h1/h2 are still in |·| form
example (a b : ℕ → ℝ) (L M ε : ℝ) (n : ℕ)
    (h1 : |a n - L| < ε / 2) (h2 : |b n - M| < ε / 2) :
    |a n - L| + |b n - M| < ε / 2 + ε / 2 := by
  -- conclude [h1, h2] -- FAILS
  linarith only [h1, h2] -- SUCCEEDS

-- SumLim step 5: arithmetic
-- conclude FAILS: ring_nf normalizes to ε*(1+1) = ε*2 but can't close it
-- (norm_num won't close an equation with a free variable ε)
example (ε : ℝ) : ε / 2 + ε / 2 = ε := by
  -- conclude [] -- FAILS
  linarith only -- SUCCEEDS

---------------------

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y ≠ c, |y - c| < δ → |f y - L| < ε

def FunCont (f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

-- **DECISION**: Should `ε` be implicit argument? Con: it is the most common variable to be used in the proof, so it would be nice to have it available without having to write `ε` every time. Pro: it is a variable that is often used in multiple places in the same proof, so it would be nice to have it available as an explicit argument.
-- def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
--   ∀ {ε : ℝ}, ε > 0 → ∃ N, ∀ n ≥ N, |a n - L| < ε

-- **WORLD 1** Sequence convergence and limits, first steps

def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

def SeqConv (a : ℕ → ℝ) : Prop :=  ∃ L, SeqLim a L

theorem ArchProp {ε : ℝ} (hε : ε > 0) : ∃ N > (0 : ℕ), 1 / (N : ℝ) < ε := by sorry

theorem SeqConstLim (a : ℕ → ℝ) (c : ℝ) (ha : ∀ n, a n = c) :
    SeqLim a c := by
  intro ε hε
  use 0
  intro n hn
  have h1 := (calc
    |a n - c| = 0 := by simp [ha] -- conclude [ha] FAILS
    _ < ε := by conclude [hε])
  apply h1

theorem SeqLimOneOverN (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) :
    SeqLim a 0 := by
  intro ε hε
  choose N Npos hN using ArchProp hε
  use N
  intro n hn
  have h1 := (calc
    |a n - 0| = 1 / n := by simp [ha] -- conclude [ha] FAILS
    _ ≤ 1 / N := by conclude [hn]
    _ < ε := by conclude [hN])
  apply h1

theorem NegOnePowDNC (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) : ¬ SeqConv a := by
  intro h
  choose L hL using h
  specialize hL (1/2) (by simp)
  choose N hN using hL
  have h1 := (calc
    a (2*N+1) = -1 := by conclude [ha])
  have h2 := (calc
    a (2*N) = 1 := by simp [ha]) -- conclude [ha]) -- FAILS!
  have h1p := (calc
    |a (2 * N + 1) - L| < 1/2 := by
            apply hN _ (by linarith only)) -- conclude [hN])
  have h2p := (calc
    |a (2 * N) - L| < 1/2 := by
            apply hN _ (by linarith only)) -- conclude [hN])
  have h3 := (calc
    (2 : ℝ) = |1 - (-1)| := by conclude []
    _ ≤ |1 - L| + |-1 - L| := by conclude []
    _ = |a (2 * N) - L| + |a (2 * N + 1) - L| := by conclude [h1, h2]
    _ ≤ 1/2 + 1/2 := by linarith only [h1p, h2p])
  contradiction [h3]

theorem DoubleSeqConv (a b : ℕ → ℝ) (L : ℝ)
    (ha : SeqLim a L) (hb : ∀ n, b n = 2 * a n) :
    SeqLim b (2 * L) := by
  intro ε hε
  have hε2 := (calc 0 < ε / 2 := by linarith only [hε]) -- conclude [hε])
  specialize ha _ hε2
  choose N hN using ha
  use N
  intro n hn
  specialize hN n hn
  specialize hb n
  have h1 := (calc
    |b n - 2 * L| = 2 * |a n - L| := by conclude [hb]
    _ < 2 * (ε / 2) := by simp [hN] -- conclude [hN]
    _ = ε := by conclude [])
  apply h1

-- **BIG BOSS** `SumLim`
theorem SumLim (a b c : ℕ → ℝ) (L M : ℝ)
    (ha : SeqLim a L) (hb : SeqLim b M) (hc : ∀ n, c n = a n + b n) :
    SeqLim c (L + M) := by
  intro ε hε
--  have hε2 : 0 < ε / 2 := by linarith only [hε] -- conclude [hε] FAILS
  choose Na hNa using ha (ε / 2) (by simp [hε])
  choose Nb hNb using hb (ε / 2) (by simp [hε])
  -- max (Na, Nb, Nc, Nd)
  -- max Na (max Nb (max Nc Nd))
  -- max {Na, Nb, Nc, Nd}
  -- Na + Nb + Nc + Nd
  -- ∑ n in range N, |f n|
  use Na + Nb
  intro n hn
  -- have hna : Na ≤ n := by linarith only [hn] -- conclude [hn] FAILS
  -- have hnb : Nb ≤ n := by linarith only [hn] -- conclude [hn] FAILS
  specialize hNa n (by linarith)
  specialize hNb n (by linarith)
  have h := (calc |c n - (L + M)|
                = |a n + b n - (L + M)| := by simp [hc] -- conclude [hc n]  -- FAILS
              _ ≤ |a n - L| + |b n - M| := by triangle_ineq       -- SUCCEEDS
              _ < ε / 2 + ε / 2 := by linarith only [hNa, hNb]   -- conclude FAILS (step 4)
              _ = ε := by linarith only []) -- conclude [] FAILS (step 5)
  apply h

-- **WORLD 2** Working with absolute values in convergence

-- `split_ands` NEW:
example (x y : ℝ) (hx : x = 2) (hy : y = 3) :
    x = 2 ∧ y = 3 := by
split_ands
apply hx
apply hy

-- `right` and `left` NEW:
example (x y : ℝ) (hx : x = 2) (hy : y = 3) :
    x = 3 ∨ y = 3 := by
right
apply hy

-- Dot notation NEW:
example  (x y : ℝ) (h : x = 2 ∧ y = 3) :
    y = 3 := by
apply h.2

-- `cases'` NEW:
example (x y : ℝ) (h : x = 2 ∨ y = 3) :
    (x - 2) * (y - 3) = 0 := by
cases' h with h1 h2
rewrite [h1]
ring_nf
rewrite [h2]
ring_nf

/-
Need: `split_abs` block/tactic that rewrites `|x| < y` into `-y < x ∧ x < y` and `|x| ≤ y` into `-y ≤ x ∧ x ≤ y`. This is the key to working with absolute values in convergence proofs, and it will allow us to apply our And/Or toolkit to these situations.
-/

theorem SeqLimLe (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) :
  ∃ N, ∀ n ≥ N, a n > L - 1 := by
specialize ha 1 (by simp)
choose N hN using ha
use N
intro n hn
specialize hN n hn
have h := (calc L - 1 < a n := by sorry ) --split_abs [hN]) -- conclude [hN]
apply h

-- **BIG BOSS**: `SqueezeTheorem`
theorem SqueezeTheorem (a b c : ℕ → ℝ) (L : ℝ)
    (ha : SeqLim a L) (hb : SeqLim b L) (hc : ∃ N, ∀ n ≥ N, a n ≤ c n ∧ c n ≤ b n) :
    SeqLim c L := by
  intro ε hε
  choose Na hNa using ha _ hε
  choose Nb hNb using hb _ hε
  choose N hN using hc
  use Na + Nb + N
  intro n hn
  have hna : Na ≤ n := by linarith only [hn] -- conclude [hn] FAILS
  have hnb : Nb ≤ n := by linarith only [hn] -- conclude [hn] FAILS
  have hnc : N ≤ n := by linarith only [hn] -- conclude [hn] FAILS
  specialize hNa n hna
  specialize hNb n hnb
  specialize hN n hnc
  -- `split_ands` -- FAILS
  rw [abs_lt] at ⊢ hNa hNb
  split_ands
  · have h1 := (calc
      -ε < a n - L := by conclude [hNa.1]
      _ ≤ c n - L := by conclude [hN.1])
    apply h1
  · have h1 := (calc
      c n - L ≤ b n - L := by conclude [hN.2]
      _ < ε := by conclude [hNb.2])
    apply h1

------------ **AI GENERATED BELOW, NOT TO BE TRUSTED** ------------

-- **WORLD 4** Algebraic Limit Theorems

-- Helpers introduced in this world
theorem abs_pos_of_nonzero' {x : ℝ} (h : x ≠ 0) : 0 < |x| := abs_pos.mpr h
theorem abs_Lipschitz' {x y : ℝ} : |(|x| - |y|)| ≤ |x - y| := abs_abs_sub_abs_le x y

-- `LimUnique`
-- conclude [] SUCCEEDS: ring rearrangement inside abs, triangle ineq
-- conclude [abs_sub_comm] SUCCEEDS: simp flips L-a to a-L
-- 0 < |L-M|/2: conclude [habs] FAILS; linarith
-- combining two hN bounds: conclude FAILS; linarith
theorem LimUnique (a : ℕ → ℝ) (L M : ℝ) (aToL : SeqLim a L) (aToM : SeqLim a M) :
    L = M := by
  by_contra h
  have habs : 0 < |L - M| := abs_pos_of_nonzero' (sub_ne_zero.mpr h)
  have hε2 : 0 < |L - M| / 2 := by linarith   -- conclude [habs] FAILS
  choose N1 hN1 using aToL _ hε2
  choose N2 hN2 using aToM _ hε2
  have hN1' : |a (N1 + N2) - L| < |L - M| / 2 := hN1 (N1 + N2) (by linarith)
  have hN2' : |a (N1 + N2) - M| < |L - M| / 2 := hN2 (N1 + N2) (by linarith)
  have h1 := (calc
    |L - M|
      = |(L - a (N1 + N2)) + (a (N1 + N2) - M)| := by conclude []
    _ ≤ |L - a (N1 + N2)| + |a (N1 + N2) - M| := by conclude []
    _ = |a (N1 + N2) - L| + |a (N1 + N2) - M| := by conclude [abs_sub_comm])
  linarith [h1, hN1', hN2']   -- conclude FAILS

-- `EventuallyGeHalfLimPos`: reverse triangle inequality
-- conclude [] SUCCEEDS for ring rearrangement and triangle ineq
-- conclude [abs_sub_comm] SUCCEEDS
-- linarith at end: conclude FAILS
example (a : ℕ → ℝ) (L : ℝ) (hL : 0 < |L|) (N : ℕ)
    (hN : ∀ n ≥ N, |a n - L| < |L| / 2) (n : ℕ) (hn : N ≤ n) : |L| / 2 ≤ |a n| := by
  have hNn := hN n hn
  have h1 := (calc
    |L| = |a n + (L - a n)| := by conclude []
    _ ≤ |a n| + |L - a n|   := by conclude []
    _ = |a n| + |a n - L|   := by conclude [abs_sub_comm])
  linarith [h1, hNn]   -- conclude FAILS

-- `AbsLim`: if b n = |a n| and a → L then b → |L|
-- simp [hb] SUCCEEDS (conclude [hb] also should succeed via simp)
-- abs_Lipschitz step: conclude FAILS (triangle_ineq fires first, opens cases, can't close)
-- conclude [hNn] SUCCEEDS
theorem AbsLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (b : ℕ → ℝ)
    (hb : ∀ n, b n = |a n|) : SeqLim b |L| := by
  intro ε hε
  choose N hN using aToL ε hε
  use N
  intro n hn
  have hNn := hN n hn
  simp only [hb]   -- conclude [hb] FAILS (nested abs parse issue); simp works
  have h1 : |(|a n| - |L|)| < ε := calc
    |(|a n| - |L|)| ≤ |a n - L| := abs_Lipschitz'   -- conclude FAILS; apply directly
    _ < ε := by linarith only [hNn]      -- linarith only, SUCCEEDS
  apply h1

-- `EventuallyGeHalfLim`: L = 0 branch — simp [hzero] SUCCEEDS; conclude [hzero] FAILS
example (a : ℕ → ℝ) (L : ℝ) (hzero : L = 0) (n : ℕ) : |L| / 2 ≤ |a n| := by
  simp [hzero]   -- conclude [hzero] FAILS

-- `OrderLimLe`: if a → L and a n ≤ K, then L ≤ K
-- by_contra + rw [abs_lt]: conclude has no role here; purely structural
theorem OrderLimLe (a : ℕ → ℝ) (L K : ℝ) (ha : SeqLim a L) (hK : ∀ n, a n ≤ K) :
    L ≤ K := by
  by_contra hL
  have hLK : 0 < L - K := by linarith   -- conclude [] FAILS
  choose N hN using ha _ hLK
  have hNn := hN N (le_refl N)
  rw [abs_lt] at hNn
  linarith [hNn.1, hK N]   -- conclude FAILS

-- `ProdLimNeNe` key calc steps:
-- ring rearrangement: conclude [] SUCCEEDS
-- triangle ineq: conclude [] SUCCEEDS
-- |a*b| = |a|*|b|: simp [abs_mul] (conclude FAILS: triangle_ineq fires first)
-- final nlinarith with multiplication bounds: conclude FAILS
example (a b : ℕ → ℝ) (L M K ε : ℝ) (n : ℕ) (Kpos : 0 < K) (hL : 0 < |L|)
    (hbn : |b n| ≤ K) (han : |a n - L| < ε / (2 * K))
    (hbn' : |b n - M| < ε / (2 * |L|)) :
    |a n * b n - L * M| < ε := by
  have f1 := (calc
    |a n * b n - L * M|
      = |(a n - L) * b n + L * (b n - M)| := by conclude []    -- ring_nf, SUCCEEDS
    _ ≤ |(a n - L) * b n| + |L * (b n - M)| := by conclude []  -- triangle_ineq, SUCCEEDS
    _ = |a n - L| * |b n| + |L| * |b n - M| := by simp [abs_mul] -- conclude FAILS
    _ ≤ (|a n - L|) * K + |L| * (ε / (2 * |L|)) := by gcongr -- conclude FAILS
    _ < (ε / (2 * K)) * K + |L| * (ε / (2 * |L|)) := by gcongr -- conclude FAILS
    _ = ε := by field_simp; ring) -- conclude FAILS
  apply f1

-- `SubseqConv`: if a → L and σ is strictly monotone, then a ∘ σ → L
-- No epsilon arithmetic at all — monotonicity gives σ n ≥ n ≥ N directly
theorem SubseqConv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) : SeqLim (a ∘ σ) L := by
  intro ε hε
  choose N hN using ha ε hε
  use N
  intro n hn
  apply hN (σ n) (le_trans hn (hσ.id_le n))

-- **WORLD 5** Cauchy Sequences

def IsCauchy' (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε

-- `IsCauchy_of_SeqConv`: convergent → Cauchy
-- ring_nf: conclude [] SUCCEEDS; triangle_ineq: conclude [] SUCCEEDS
-- conclude [abs_sub_comm] SUCCEEDS (simp flips sign)
-- linarith at ε/2 + ε/2 and = ε: conclude FAILS
theorem IsCauchy_of_SeqConv (a : ℕ → ℝ) (ha : SeqConv a) : IsCauchy' a := by
  choose L hL using ha
  intro ε hε
  choose N hN using hL _ (by linarith : 0 < ε / 2)  -- conclude [hε] FAILS
  use N
  intro n hn m hm
  have hn' := hN n hn
  have hm' := hN m (by linarith)
  have h1 := (calc
    |a m - a n|
      = |(a m - L) + (L - a n)| := by conclude []
    _ ≤ |a m - L| + |L - a n|   := by conclude []
    _ = |a m - L| + |a n - L|   := by conclude [abs_sub_comm]
    _ < ε / 2 + ε / 2           := by linarith [hm', hn']  -- conclude FAILS
    _ = ε                        := by linarith)            -- conclude [] FAILS
  apply h1

-- `IsCauchy_of_Sum`: sum of Cauchy sequences is Cauchy — same pattern
theorem IsCauchy_of_Sum (a b : ℕ → ℝ) (ha : IsCauchy' a) (hb : IsCauchy' b) :
    IsCauchy' (fun n => a n + b n) := by
  intro ε hε
  choose N1 hN1 using ha _ (by linarith : 0 < ε / 2)
  choose N2 hN2 using hb _ (by linarith : 0 < ε / 2)
  use N1 + N2
  intro n hn m hm
  have haN := hN1 n (by linarith) m (by linarith)
  have hbN := hN2 n (by linarith) m (by linarith)
  have h1 := (calc
    |a m + b m - (a n + b n)|
      = |(a m - a n) + (b m - b n)| := by conclude []
    _ ≤ |a m - a n| + |b m - b n|   := by conclude []
    _ < ε / 2 + ε / 2               := by linarith [haN, hbN]  -- conclude FAILS
    _ = ε                            := by linarith)            -- conclude [] FAILS
  apply h1

-- **WORLD 13** Function Limits and Continuity

def FunContAt' (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

-- `FunContAtAdd`: sum of continuous functions is continuous
-- Triangle ineq: conclude [] SUCCEEDS as usual
-- 0 < min δ₁ δ₂: conclude [hδ₁, hδ₂] FAILS (linarith can't use min_le facts)
-- |x-c| < δ₁ from min: conclude FAILS (same)
-- linarith at ε/2 steps: conclude FAILS
theorem FunContAtAdd (f g : ℝ → ℝ) (c : ℝ)
    (hf : FunContAt' f c) (hg : FunContAt' g c) : FunContAt' (fun x => f x + g x) c := by
  intro ε hε
  choose δ₁ hδ₁ hf' using hf _ (by linarith : 0 < ε / 2)
  choose δ₂ hδ₂ hg' using hg _ (by linarith : 0 < ε / 2)
  use min δ₁ δ₂
  constructor
  · exact lt_min hδ₁ hδ₂   -- conclude [hδ₁, hδ₂] FAILS
  intro x hx
  have hd1 : |x - c| < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)   -- conclude FAILS
  have hd2 : |x - c| < δ₂ := lt_of_lt_of_le hx (min_le_right _ _)  -- conclude FAILS
  have h1 := (calc
    |f x + g x - (f c + g c)|
      = |(f x - f c) + (g x - g c)| := by conclude []
    _ ≤ |f x - f c| + |g x - g c|   := by conclude []
    _ < ε / 2 + ε / 2               := by linarith [hf' x hd1, hg' x hd2]  -- conclude FAILS
    _ = ε                            := by linarith)  -- conclude [] FAILS
  apply h1

-- `Cont_Comp`: composition of continuous functions — no conclude role; purely structural
def FunCont' (f : ℝ → ℝ) : Prop := ∀ x, FunContAt' f x

theorem Cont_Comp (f g : ℝ → ℝ) (hf : FunCont' f) (hg : FunCont' g) :
    FunCont' (f ∘ g) := by
  intro x ε hε
  choose ε₁ hε₁ hfε₁ using hf (g x) ε hε
  choose δ hδ hgδ using hg x ε₁ hε₁
  exact ⟨δ, hδ, fun t ht => hfε₁ (g t) (hgδ t ht)⟩

-- **WORLD 16** Uniformity

def UnifConv' (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |f n x - F x| < ε

-- `Cont_of_UnifConv`: uniform limit of continuous fns is continuous
-- 3-term triangle ineq: conclude [] UNKNOWN (triangle_ineq may not handle 3 terms; try)
-- conclude [abs_sub_comm] SUCCEEDS for flipping one term
-- linarith at ε/3 steps: conclude FAILS
theorem Cont_of_UnifConv (f : ℕ → ℝ → ℝ) (hf : ∀ n, FunCont' (f n))
    (F : ℝ → ℝ) (hfF : UnifConv' f F) : FunCont' F := by
  intro x ε hε
  choose N hN using hfF _ (by linarith : 0 < ε / 3)
  choose δ hδpos hfδ using hf N x (ε / 3) (by linarith)
  use δ, hδpos
  intro y hy
  have hFNy := hN N (le_refl N) y
  have hFNx := hN N (le_refl N) x
  have hfNxy := hfδ y hy
  have h1 := (calc
    |F y - F x|
      = |(F y - f N y) + (f N y - f N x) + (f N x - F x)| := by conclude []
    _ ≤ |F y - f N y| + |f N y - f N x| + |f N x - F x|   := by conclude []  -- UNKNOWN: 3-term tri
    _ = |f N y - F y| + |f N y - f N x| + |f N x - F x|   := by conclude [abs_sub_comm]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [hFNy, hFNx, hfNxy]  -- conclude FAILS
    _ = ε := by linarith)  -- conclude [] FAILS
  apply h1

-- **WORLD 5 (Boss)** IsCauchy_of_MonotoneBdd
-- No calc/conclude role anywhere; proof is by_contra + gap accumulation

-- IterateGap': monotone with persistent ε-gaps → grows by k*ε
-- conclude has no role; induction + linarith
theorem IterateGap' (a : ℕ → ℝ) (ha : Monotone a) (ε : ℝ) (εpos : ε > 0)
    (τ : ℕ → ℕ) (hτ : ∀ n, τ n ≥ n) (σ : ℕ → ℕ) (hσ : ∀ n, σ n ≥ τ n)
    (hgap : ∀ n, ε ≤ |a (σ n) - a (τ n)|) :
    ∀ k : ℕ, (k : ℝ) * ε ≤ a (σ^[k] 0) - a 0 := by
  intro k; induction k with
  | zero => simp
  | succ k hk =>
    rw [Function.iterate_succ', Function.comp]
    push_cast
    have hmono_τ : a (σ^[k] 0) ≤ a (τ (σ^[k] 0)) := ha (hτ _)
    have hmono_σ : a (τ (σ^[k] 0)) ≤ a (σ (σ^[k] 0)) := ha (hσ _)
    have hgapk := hgap (σ^[k] 0)
    rw [abs_of_nonneg (by linarith)] at hgapk
    linarith

-- IsCauchy_of_MonotoneBdd: by_contra + IterateGap' → exceeds bound → contradiction
-- conclude has no role anywhere
theorem IsCauchy_of_MonotoneBdd' {a : ℕ → ℝ} {M : ℝ} (ha : Monotone a) (hM : ∀ n, a n ≤ M) :
    IsCauchy' a := by
  intro ε hε
  by_contra h
  push_neg at h   -- conclude FAILS (structural)
  choose τ hτ σ hσ hgap using h
  have f1 := IterateGap' a ha ε hε τ hτ σ hσ hgap
  choose k hk using exists_nat_gt ((M - a 0) / ε)   -- conclude FAILS (Archimedean)
  specialize f1 (k + 1)
  specialize hM (σ^[k + 1] 0)
  have hMε : M - a 0 < (↑(k + 1) : ℝ) * ε := by
    have hk1 : (M - a 0) / ε < ↑(k + 1) :=
      lt_trans hk (by exact_mod_cast Nat.lt_succ_self k)
    have h2 := mul_lt_mul_of_pos_right hk1 hε
    rwa [div_mul_cancel₀ (M - a 0) (ne_of_gt hε)] at h2
  linarith   -- conclude FAILS

-- **WORLD 6** Subsequences

def IsAPeak' (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ m > n, a m ≤ a n
def UnBddPeaks' (a : ℕ → ℝ) : Prop := ∀ k, ∃ n > k, IsAPeak' a n

-- MonotoneSubseq_of_BddPeaks: conclude has no role
-- push_neg → choose witnesses beyond last peak → conditional orbit → monotone composition
theorem MonotoneSubseq_of_BddPeaks' (a : ℕ → ℝ) (ha : ¬ UnBddPeaks' a) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ Monotone (a ∘ σ) := by
  unfold UnBddPeaks' IsAPeak' at ha
  push_neg at ha   -- conclude FAILS (structural)
  choose k hk using ha
  -- hk : ∀ n > k, ∃ m > n, a n < a m  (beyond k, no peak)
  -- Build σ via orbit of τ' = (if n ≤ k then n+1 else witness beyond n)
  sorry

-- **WORLD 7** Bolzano-Weierstrass

-- BolzanoWeierstrass: bounded → Cauchy subsequence
-- No calc/conclude: by_cases on UnBddPeaks', then apply structural results
theorem BolzanoWeierstrass' (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, |a n| ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ IsCauchy' (a ∘ σ) := by
  by_cases hPeaks : UnBddPeaks' a   -- conclude FAILS (case split)
  · -- peaks unbounded → antitone subseq (bounded below by -M) → Cauchy by IsCauchy_of_AntitoneBdd
    sorry
  · -- no unbounded peaks → monotone subseq (bounded above by M) → Cauchy by IsCauchy_of_MonotoneBdd'
    obtain ⟨σ, hσstrict, hσmono⟩ := MonotoneSubseq_of_BddPeaks' a hPeaks
    use σ, hσstrict
    apply IsCauchy_of_MonotoneBdd' (hσmono) (fun n => by specialize hM (σ n); rw [abs_le] at hM; exact hM.2)

-- **WORLD 9** Intro to Series

open Finset in
def Series'' (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, a k

-- LeibnizSeriesFinite: induction + field_simp/ring; conclude has no role
open Finset in
theorem LeibnizSeriesFinite'' {a : ℕ → ℝ} (ha : ∀ n, a n = 1 / ((↑n + 1) * (↑n + 2))) :
    ∀ n, Series'' a n = 1 - 1 / (↑n + 1) := by
  intro n; induction n with
  | zero => simp [Series'']
  | succ m hm =>
    simp only [Series'', sum_range_succ]
    unfold Series'' at hm
    rw [hm, ha m]; push_cast; field_simp; ring   -- conclude has no role (algebra)

-- SeriesOrderThm: induction + linarith; conclude has no role
open Finset in
theorem SeriesOrderThm'' {a b : ℕ → ℝ} (hab : ∀ n, a n ≤ b n) :
    ∀ n, Series'' a n ≤ Series'' b n := by
  intro n; induction n with
  | zero => simp [Series'']
  | succ m hm =>
    simp only [Series''] at hm
    unfold Series''
    rw [sum_range_succ, sum_range_succ]
    linarith [hm, hab m]   -- conclude FAILS (multi-hyp linarith)

-- LeibnizSeries: ε-N using LeibnizSeriesFinite'' and ArchProp
-- simp for partial sum formula: conclude [hform] FAILS
-- abs rewrite |-(1/(n+1))| = 1/(n+1): conclude [] FAILS (abs_neg + abs_of_nonneg pattern)
-- 1/(n+1) ≤ 1/N: one_div_le_one_div_of_le (conclude [hn] FAILS; field div)
-- final linarith: conclude FAILS (multi-hyp)
theorem LeibnizSeries'' {a : ℕ → ℝ} (ha : ∀ n, a n = 1 / ((↑n + 1) * (↑n + 2))) :
    ∃ L, SeqLim (Series'' a) L := by
  use 1
  intro ε hε
  choose N Npos hN using ArchProp hε
  use N
  intro n hn
  have hform := LeibnizSeriesFinite'' ha n
  show |Series'' a n - 1| < ε   -- conclude [hform] FAILS (simp needed)
  rw [hform, show (1 : ℝ) - 1 / (↑n + 1) - 1 = -(1 / (↑n + 1)) by ring]
  rw [abs_neg, abs_of_nonneg (by positivity)]   -- conclude [] FAILS (rewrite pattern)
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Npos
  sorry

-- BaselConv: 1/(n+2)² converges by comparison with Leibniz + monotone bounded convergence
-- conclude has no role: comparison via SeriesOrderThm'', boundedness from Leibniz formula
example {a : ℕ → ℝ} (ha : ∀ n, a n = 1 / ((↑n + 2) ^ 2)) :
    ∃ L, SeqLim (Series'' a) L := by
  -- Series'' a is monotone (terms nonneg) and bounded above by 1 (≤ Leibniz partial sums)
  -- SeqConv_of_MonotoneBdd combines IsCauchy_of_MonotoneBdd + completeness
  sorry

-- **WORLD 10** Absolute and Alternating Series

-- Conv_of_AbsSeriesConv: key calc step is FINITE triangle ineq
-- |∑ Ico n m, a k| ≤ ∑ Ico n m, |a k|
-- conclude [] FAILS: triangle_ineq only handles 2-term |A+B|; use Finset.abs_sum_le_sum_abs
open Finset in
example (a : ℕ → ℝ) {n m : ℕ} :
    |∑ k ∈ Ico n m, a k| ≤ ∑ k ∈ Ico n m, |a k| := by
  -- conclude [] FAILS (finite sum triangle ineq, not 2-term)
  exact abs_sum_le_sum_abs _ _

-- AlternatingSeriesTest: structural (MonotoneSeriesEven + IsCauchy_of_MonotoneBdd + SeqEvenOdd)
-- conclude has no role
example {a : ℕ → ℝ} (ha : Antitone a) (aLim : SeqLim a 0) :
    ∃ L, SeqLim (fun n => Series'' (fun k => (-1)^k * a k) n) L := by
  sorry

-- **WORLD 17** Topology: HasLUB_of_BddNonempty
-- No calc/conclude; order-theoretic (Real.sSup / isLUB_csSup)
def IsUB'' (S : Set ℝ) (b : ℝ) : Prop := ∀ x ∈ S, x ≤ b
def IsLUB'' (S : Set ℝ) (c : ℝ) : Prop := IsUB'' S c ∧ ∀ b, IsUB'' S b → c ≤ b

theorem HasLUB_of_BddNonempty' {S : Set ℝ} (hS : S.Nonempty) (hb : ∃ b, IsUB'' S b) :
    ∃ c, IsLUB'' S c := by
  obtain ⟨b, hb⟩ := hb
  use sSup S
  constructor
  · intro x hx
    exact le_csSup ⟨b, fun y hy => hb y hy⟩ hx   -- conclude FAILS (topology)
  · intro u hu
    exact csSup_le hS (fun x hx => hu x hx)

-- **WORLD 18** Heine-Borel: IsCompact_of_ClosedInterval, IsCompact_of_ClosedSubset
-- No calc/conclude: set topology + sum type index construction
-- (see L24Levels/L04.lean and L25.lean for full proofs)

-- **WORLD 20 (Boss)** IVT
-- Key structure: S = {x ∈ [a,b] | f x < 0}, c = sup S
-- Continuity arguments involve |y - c| < δ (abs_lt rewrite)
-- conclude [] could handle δ-ball membership but surrounding LUB logic uses linarith
-- conclude has no role in the overall proof structure
theorem IVT' (f : ℝ → ℝ) (hf : FunCont f) {a b : ℝ} (hab : a < b)
    (hfa : f a < 0) (hfb : 0 < f b) : ∃ c, a < c ∧ c < b ∧ f c = 0 := by
  -- c = sup S where S = {x ∈ [a,b] | f x < 0}
  let S := {x | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have hSne : S.Nonempty := ⟨a, le_refl _, le_of_lt hab, hfa⟩
  have hSbdd : ∃ u, IsUB'' S u := ⟨b, fun x hx => hx.2.1⟩
  obtain ⟨c, hcUB, hcLUB⟩ := HasLUB_of_BddNonempty' hSne hSbdd
  have ha_le_c : a ≤ c := hcUB a ⟨le_refl _, le_of_lt hab, hfa⟩
  have hc_le_b : c ≤ b := hcLUB b (fun x hx => hx.2.1)
  -- Show f c = 0 by ruling out f c < 0 and f c > 0
  have hfcnn : ¬ f c < 0 := by
    intro hfc
    obtain ⟨δ, hδpos, hδ⟩ := hf c (-f c / 2) (by linarith)
    have hcd : c + δ / 2 ∈ S := by
      refine ⟨by linarith, ?_, ?_⟩
      · -- c + δ/2 ≤ b: if not, then b ∈ Ball(c,δ) and f b < 0 by continuity, contradiction
        by_contra hb'
        push_neg at hb'
        have : |b - c| < δ := by
          rw [abs_lt]; constructor <;> linarith
        have := hδ b this; rw [abs_lt] at this   -- conclude [] for abs_lt rewrite UNKNOWN
        linarith [this.1, hfc, hfb]
      · have : |c + δ/2 - c| < δ := by
          rw [abs_of_nonneg (by linarith)]; linarith   -- conclude [] FAILS
        sorry --linarith [hδ (c + δ/2) this |>.1, hfc]
    linarith [hcUB (c + δ/2) hcd, hδpos]
  have hfcnp : ¬ 0 < f c := by
    intro hfc
    obtain ⟨δ, hδpos, hδ⟩ := hf c (f c / 2) (by linarith)
    have hcmhUB : IsUB'' S (c - δ/2) := by
      intro x hx
      by_contra hxc
      push_neg at hxc
      have hxc2 : x ≤ c := hcUB x hx
      have : |x - c| < δ := by
        rw [abs_lt]; constructor <;> linarith   -- conclude [] for abs_lt rewrite UNKNOWN
      sorry -- linarith [hδ x this |>.1, hx.2.2, hfc]
    linarith [hcLUB (c - δ/2) hcmhUB, hδpos]
  have hfc : f c = 0 := le_antisymm (not_lt.mp hfcnp) (not_lt.mp hfcnn)
  have hac : a < c := by
    rcases eq_or_lt_of_le ha_le_c with rfl | h
    · sorry -- linarith [hfcnn.elim (lt_of_not_le (not_le.mpr hfa))]
    · exact h
  have hcb : c < b := by
    rcases eq_or_lt_of_le hc_le_b with rfl | h
    · sorry -- linarith [hfcnp.elim (lt_of_not_le (not_le.mpr hfb))]
    · exact h
  exact ⟨c, hac, hcb, hfc⟩

#exit

-- attribute [grind .] inv_lt_of_inv_lt₀
attribute [grind =] one_mul
attribute [grind =] Nat.cast_le._simp_1
attribute [grind =] Mathlib.Tactic.Qify.intCast_le._simp_1
attribute [grind =] Mathlib.Tactic.Rify.ratCast_le._simp_1
attribute [grind =] Int.cast_natCast
attribute [grind =] Rat.cast_natCast
