import Mathlib
import Game.Metadata

open Classical

private lemma sum_card_fibers_eq_card_relation
    {α : Type}
    (s : Finset α)
    (R : α → α → Prop) :
    (∑ x ∈ s, {y ∈ s | R x y}.card) =
      ((s ×ˢ s).filter fun p => R p.1 p.2).card := by
  classical
  calc
    _ = ∑ x ∈ s, ∑ y ∈ s, if R x y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ s ×ˢ s, if R p.1 p.2 then 1 else 0 := by
      rw [Finset.sum_product]
    _ = _ := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma even_card_symmetric_irreflexive_relation
    {α : Type}
    (s : Finset α)
    (R : α → α → Prop)
    (hsymm : ∀ x y, R x y → R y x)
    (hirref : ∀ x, ¬ R x x) :
    Even ((s ×ˢ s).filter fun p => R p.1 p.2).card := by
  classical
  rw [← sum_card_fibers_eq_card_relation s R]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      let n := {y ∈ s | R a y}.card
      have hrow : {y ∈ insert a s | R a y}.card = n := by
        rw [Finset.filter_insert]
        simp [n, hirref]
      have hcol (x : α) (hx : x ∈ s) :
          {y ∈ insert a s | R x y}.card =
            {y ∈ s | R x y}.card + if R x a then 1 else 0 := by
        rw [Finset.filter_insert]
        by_cases h : R x a <;> simp [ha, h]
      have hindicator :
          ∑ x ∈ s, (if R x a then 1 else 0) = n := by
        rw [← Finset.card_filter]
        congr 1
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, hxa⟩
          exact ⟨hx, hsymm x a hxa⟩
        · rintro ⟨hx, hax⟩
          exact ⟨hx, hsymm a x hax⟩
      have hsumcol :
          (∑ x ∈ s, {y ∈ insert a s | R x y}.card) =
            ∑ x ∈ s, ({y ∈ s | R x y}.card + if R x a then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hcol x hx
      rw [Finset.sum_insert ha, hrow, hsumcol, Finset.sum_add_distrib, hindicator]
      have hn : Even (2 * n) := by simp
      simpa [n, two_mul, add_assoc, add_comm, add_left_comm] using ih.add hn

private lemma even_sum_relation_counts
    {α : Type}
    (s : Finset α)
    {R : α → α → Prop}
    (hsymm : ∀ x y, R x y → R y x)
    (hirref : ∀ x, ¬ R x x)
    {Count : α → ℕ}
    (Count_Is : ∀ x, Count x = {y ∈ s | R x y}.card) :
    Even (∑ x ∈ s, Count x) := by
  simp only [Count_Is]
  rw [sum_card_fibers_eq_card_relation s R]
  exact even_card_symmetric_irreflexive_relation s R hsymm hirref

private lemma sum_eq_sum_even_add_sum_odd
    {α : Type}
    (s : Finset α)
    (f : α → ℕ) :
    (∑ x ∈ s, f x) =
      (∑ x ∈ s.filter fun x => Even (f x), f x) +
      (∑ x ∈ s.filter fun x => Odd (f x), f x) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun x => Even (f x))]
  congr 2
  ext x
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hx
  exact Nat.not_even_iff_odd

private lemma even_sum_even_terms
    {α : Type}
    (s : Finset α)
    (f : α → ℕ) :
    Even (∑ x ∈ s.filter fun x => Even (f x), f x) := by
  apply Finset.even_sum
  simp

private lemma even_right_of_even_add
    {a b : ℕ}
    (hab : Even (a + b))
    (ha : Even a) :
    Even b :=
  (Nat.even_add.mp hab).mp ha

private lemma even_right_of_even_split
    {total evenPart oddPart : ℕ}
    (hsplit : total = evenPart + oddPart)
    (htotal : Even total)
    (hevenPart : Even evenPart) :
    Even oddPart := by
  rw [hsplit] at htotal
  exact even_right_of_even_add htotal hevenPart

private lemma odd_sum_of_odd_terms_of_odd_card
    {α : Type}
    (s : Finset α)
    (f : α → ℕ)
    (hall : ∀ x ∈ s, Odd (f x))
    (hcard : Odd s.card) :
    Odd (∑ x ∈ s, f x) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hfilter : s.filter (fun x => Odd (f x)) = s :=
    Finset.filter_eq_self.mpr hall
  rwa [hfilter]

private lemma even_card_of_even_sum_over_odd_terms
    {α : Type}
    (s : Finset α)
    (f : α → ℕ)
    (hsum : Even (∑ x ∈ s.filter fun x => Odd (f x), f x)) :
    Even (s.filter fun x => Odd (f x)).card := by
  by_contra hcard
  have hcardOdd : Odd (s.filter (fun x => Odd (f x))).card :=
    Nat.not_even_iff_odd.mp hcard
  have hsumOdd : Odd (∑ x ∈ s.filter fun x => Odd (f x), f x) := by
    apply odd_sum_of_odd_terms_of_odd_card
    · simp
    · exact hcardOdd
  exact (Nat.not_even_iff_odd.mpr hsumOdd) hsum

World "NASPresentation"
Level 1
Title "The Handshake Lemma"

Introduction "
# The Handshake Lemma

Experiment with a block proof that the number of partygoers who shook an odd
number of hands is even.
"

/-- The number of partygoers who shook an odd number of hands is even. -/
TheoremDoc NumOddHandshakes_is_Even as "Odd handshakes are even" in "Combinatorics"

/-- Admit the current goal while experimenting with the level. -/
TacticDoc «sorry»

Statement NumOddHandshakes_is_Even
    (Person : Type)
    (Party : Finset Person)
    (Handshake : Person → Person → Prop)
    (Handshake_symm : ∀ x y, Handshake x y → Handshake y x)
    (Handshake_irref : ∀ x, ¬ Handshake x x)
    (HandshakeCount : Person → ℕ)
    (HandshakeCount_Is : ∀ x, HandshakeCount x = {y ∈ Party | Handshake x y}.card)
    (NumOddHandshakes : ℕ)
    (NumOddHandshakes_Is : NumOddHandshakes = {x ∈ Party | Odd (HandshakeCount x)}.card) :
    Even NumOddHandshakes := by
  let NumTotHandshakes := ∑ x ∈ Party, HandshakeCount x
  let EvenPeople := Party.filter fun x => Even (HandshakeCount x)
  let OddPeople := Party.filter fun x => Odd (HandshakeCount x)
  let NumTotEven := ∑ x ∈ EvenPeople, HandshakeCount x
  let NumTotOdd := ∑ x ∈ OddPeople, HandshakeCount x
  have NumTotHandshakes_is_Even : Even NumTotHandshakes :=
    even_sum_relation_counts
      Party Handshake_symm Handshake_irref HandshakeCount_Is
  have NumTot_split : NumTotHandshakes = NumTotEven + NumTotOdd :=
    sum_eq_sum_even_add_sum_odd Party HandshakeCount
  have NumTotEven_is_Even : Even NumTotEven :=
    even_sum_even_terms Party HandshakeCount
  have NumTotOdd_is_Even : Even NumTotOdd :=
    even_right_of_even_split
      NumTot_split NumTotHandshakes_is_Even NumTotEven_is_Even
  have OddPeople_is_Even : Even OddPeople.card :=
    even_card_of_even_sum_over_odd_terms
      Party HandshakeCount NumTotOdd_is_Even
  rw [NumOddHandshakes_Is]
  exact OddPeople_is_Even

NewTactic «sorry»

-- Keep this standalone playground unrestricted without relying on permissions
-- inherited from the tutorial worlds.
AllowBlock "tactic_unfold" "tactic_calc" "tactic_let" "tactic_intro" "tactic_use"
AllowBlock "tactic_rewrite" "tactic_apply" "tactic_specialize" "tactic_choose"
AllowBlock "tactic_at" "tactic_constructor" "tactic_have" "tactic_show"
AllowBlock "tactic_conv" "tactic_sorry" "tactic_other" "tactic_refl"
AllowBlock "tactic_ring_nf" "tactic_simp" "tactic_conclude" "tactic_rewrite_at"
AllowBlock "tactic_transform" "tactic_exact" "prop_declaration" "prop"
AllowBlock "term_nas_even_total_relation_counts"
AllowBlock "term_nas_split_even_odd" "term_nas_even_sum_even_terms"
AllowBlock "term_nas_even_right_of_split" "term_nas_even_card_odd_terms"
AllowAllAffordances

Conclusion "The number of partygoers with an odd number of handshakes is even."
