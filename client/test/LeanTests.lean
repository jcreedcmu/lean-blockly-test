import Mathlib

/-
The goal of this file is to build up the entire Game and test the various closing tactics against the situations in which they occur. They should be just strong enough but not too strong!
-/

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
  -- conclude [hf] -- FAILS!
  simp [hf] -- SUCCEEDS

-- Problem 3 needs:
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = 1/n) (n : ℕ) : |a n - 0| = 1 / n := by
  -- conclude [ha] -- FAILS!
  simp [ha] -- SUCCEEDS

-- Problem 3 needs:
example (N : ℕ) (Npos : N > 0) (n : ℕ) (hn : n > N) : (1 : ℝ) / n ≤ 1 / N := by
--  conclude [] -- FAILS; good!
  conclude [hn] -- SUCCEEDS

-- Problem 4 needs:
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = (-1) ^ n) (N : ℕ) : a (2 * N) = 1 := by
  -- conclude [ha] -- FAILS!?
  simp [ha] -- SUCCEEDS

-- Problem 4 needs:
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = (-1) ^ n) (N : ℕ) : a (2 * N + 1) = -1 := by
  conclude [ha] -- SUCCEEDS

-- Problem 4 needs:
example : (2 : ℝ) = |1 - (-1)| := by
  conclude [] -- SUCCEEDS

-- Problem 4 needs:
example (L : ℝ) : |1 - (-1)| ≤|1 - L| + |(-1) - L| := by
  conclude [] -- SUCCEEDS

-- Problem 4 needs:
example (L a2n a2n1 : ℝ) (ha2n : a2n = 1) (ha2n1 : a2n = -1) :
    |1 - L| + |(-1) - L| = |a2n - L| + |a2n1 - L| := by
  -- conclude [] -- SUCCEEDS! It shouldn't
  conclude [ha2n, a2n1] -- SUCCEEDS

-- Problem 4 needs:
example (L a2n a2n1 : ℝ) (ha2n : |a2n - L| ≤ 1/2) (ha2n1 : |a2n1 - L| ≤ 1/2) :
    |a2n - L| + |a2n1 - L| ≤ 1/2 + 1/2 := by
  -- conclude [ha2n, a2n1] -- FAILS!?
  linarith only [ha2n, ha2n1] -- SUCCEEDS

---------------------

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y ≠ c, |y - c| < δ → |f y - L| < ε

def FunCont (f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε

def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε

def SeqConv (a : ℕ → ℝ) : Prop :=  ∃ L, SeqLim a L

theorem ArchProp {ε : ℝ} (hε : ε > 0) : ∃ N > (0 : ℕ), 1 / (N : ℝ) < ε := by sorry

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
    |a (2 * N + 1) - L| < 1/2 := by sorry) -- conclude [hN])
  have h2p := (calc
    |a (2 * N) - L| < 1/2 := by sorry) -- conclude [hN])
  have h3 := (calc
    (2 : ℝ) = |1 - (-1)| := by conclude []
    _ ≤ |1 - L| + |-1 - L| := by conclude []
    _ = |a (2 * N) - L| + |a (2 * N + 1) - L| := by conclude [h1, h2]
    _ ≤ 1/2 + 1/2 := by linarith only [h1p, h2p])
  contradiction [h3]

#exit

-- attribute [grind .] inv_lt_of_inv_lt₀
attribute [grind =] one_mul
attribute [grind =] Nat.cast_le._simp_1
attribute [grind =] Mathlib.Tactic.Qify.intCast_le._simp_1
attribute [grind =] Mathlib.Tactic.Rify.ratCast_le._simp_1
attribute [grind =] Int.cast_natCast
attribute [grind =] Rat.cast_natCast
