import E1088.Refine

/-!
# Theorem LR, part 1: type functions, gap normal form, pairwise processing (Lemma NF, NF1–NF2)

A *type function* is a row function `a(x)` or a column function `b(w)` (constants are column
functions). Every difference of two type functions has the form `A(x) + B(w)`.
A *basic quantity* is written uniformly as a product `qr(x) * qc(w)` with `qr, qc > 0`; this
covers positive row functions, positive column functions and positive constants.
-/

set_option linter.unusedSectionVars false

open Finset

namespace E1088

/-- Row or column type function. -/
inductive TF (α β : Type*) where
  | row (a : α → ℝ)
  | col (b : β → ℝ)

namespace TF

variable {α β : Type*}

/-- Value of a type function at an entry. -/
def eval : TF α β → α → β → ℝ
  | row a => fun x _ => a x
  | col b => fun _ w => b w

/-- Row part. -/
def rp : TF α β → α → ℝ
  | row a => a
  | col _ => 0

/-- Column part. -/
def cp : TF α β → β → ℝ
  | row _ => 0
  | col b => b

theorem eval_eq (t : TF α β) (x : α) (w : β) : t.eval x w = t.rp x + t.cp w := by
  cases t <;> simp [eval, rp, cp]

end TF

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

/-- The types `S` cover every entry of `M` on `X × Y`. -/
def Covers (M : α → β → ℝ) (τ : ι → TF α β) (S : Finset ι) (X : Finset α) (Y : Finset β) :
    Prop :=
  ∀ x ∈ X, ∀ w ∈ Y, ∃ t ∈ S, M x w = (τ t).eval x w

theorem Covers.mono {M : α → β → ℝ} {τ : ι → TF α β} {S : Finset ι} {X X' : Finset α}
    {Y Y' : Finset β} (h : Covers M τ S X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    Covers M τ S X' Y' := fun x hx w hw => h x (hX hx) w (hY hw)

/-- `g` is `c`-comparable to a basic quantity on `X × Y`. -/
def Comparable (g : α → β → ℝ) (c : ℝ) (X : Finset α) (Y : Finset β) : Prop :=
  ∃ qr : α → ℝ, ∃ qc : β → ℝ, (∀ x ∈ X, 0 < qr x) ∧ (∀ w ∈ Y, 0 < qc w) ∧
    ∀ x ∈ X, ∀ w ∈ Y, qr x * qc w ≤ |g x w| ∧ |g x w| ≤ c * (qr x * qc w)

theorem Comparable.mono {g : α → β → ℝ} {c : ℝ} {X X' : Finset α} {Y Y' : Finset β}
    (h : Comparable g c X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : Comparable g c X' Y' := by
  obtain ⟨qr, qc, h1, h2, h3⟩ := h
  exact ⟨qr, qc, fun x hx => h1 x (hX hx), fun w hw => h2 w (hY hw),
    fun x hx w hw => h3 x (hX hx) w (hY hw)⟩

/-- Strict constant sign. -/
def StrictSign (g : α → β → ℝ) (X : Finset α) (Y : Finset β) : Prop :=
  (∀ x ∈ X, ∀ w ∈ Y, 0 < g x w) ∨ (∀ x ∈ X, ∀ w ∈ Y, g x w < 0)

theorem StrictSign.mono {g : α → β → ℝ} {X X' : Finset α} {Y Y' : Finset β}
    (h : StrictSign g X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : StrictSign g X' Y' := by
  rcases h with h | h
  · exact Or.inl fun x hx w hw => h x (hX hx) w (hY hw)
  · exact Or.inr fun x hx w hw => h x (hX hx) w (hY hw)

/-- Sum of a positive row function and a nonnegative column function is 2-comparable
(hence 32-comparable) to a basic quantity on a refinement of cost `(4, 4)` (Lemma B). -/
theorem sum_comparable (X : Finset α) (Y : Finset β) (hY : Y.Nonempty) (D : α → ℝ)
    (E : β → ℝ) (hD : ∀ x ∈ X, 0 < D x) (hE : ∀ w ∈ Y, 0 ≤ E w) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 4 * #Y' ∧
      Comparable (fun x w => D x + E w) 32 X' Y' := by
  obtain ⟨X', hX', Y', hY', h1, h2, h⟩ := lemmaB X Y hY D E hD hE
  refine ⟨X', hX', Y', hY', h1, h2, ?_⟩
  rcases X'.eq_empty_or_nonempty with hXe | hX0
  · exact ⟨fun _ => 1, fun _ => 1, fun _ _ => one_pos, fun _ _ => one_pos, by simp [hXe]⟩
  rcases h with h | h | ⟨s, hs, hDs, hEs⟩
  · refine ⟨D, fun _ => 1, fun x hx => hD x (hX' hx), fun _ _ => one_pos, fun x hx w hw => ?_⟩
    have := hD x (hX' hx); have := hE w (hY' hw); have := h x hx w hw
    rw [abs_of_pos (by linarith)]
    constructor <;> nlinarith
  · refine ⟨fun _ => 1, E, fun _ _ => one_pos, fun w hw => ?_, fun x hx w hw => ?_⟩
    · obtain ⟨x, hx⟩ := hX0
      have := hD x (hX' hx); have := h x hx w hw; linarith
    · have := hD x (hX' hx); have := hE w (hY' hw); have := h x hx w hw
      rw [abs_of_pos (by linarith)]
      constructor <;> nlinarith
  · refine ⟨fun _ => s / 4, fun _ => 1, fun _ _ => by positivity, fun _ _ => one_pos,
      fun x hx w hw => ?_⟩
    have := hDs x hx; have := hEs w hw
    rw [abs_of_pos (by linarith)]
    constructor <;> nlinarith

/-- Pigeonhole for the three-way sign split of a row function. -/
theorem three_split (X : Finset α) (g : α → ℝ) :
    #X ≤ 3 * #(X.filter fun x => g x < 0) ∨ #X ≤ 3 * #(X.filter fun x => g x = 0) ∨
      #X ≤ 3 * #(X.filter fun x => 0 < g x) := by
  have := card_trichotomy X g 0
  omega

/-- A row function of constant strict sign is 1-comparable to a basic quantity. -/
theorem comparable_row (X : Finset α) (Y : Finset β) (g : α → ℝ) (hg : ∀ x ∈ X, g x ≠ 0) :
    Comparable (fun x _ => g x) 32 X Y :=
  ⟨fun x => |g x|, fun _ => 1, fun x hx => abs_pos.2 (hg x hx), fun _ _ => one_pos,
    fun x hx w hw => by
      have := abs_nonneg (g x)
      simp only [mul_one]; constructor <;> linarith⟩

/-- A column function of constant strict sign is 1-comparable to a basic quantity. -/
theorem comparable_col (X : Finset α) (Y : Finset β) (g : β → ℝ) (hg : ∀ w ∈ Y, g w ≠ 0) :
    Comparable (fun _ w => g w) 32 X Y :=
  ⟨fun _ => 1, fun w => |g w|, fun _ _ => one_pos, fun w hw => abs_pos.2 (hg w hw),
    fun x hx w hw => by
      have := abs_nonneg (g w)
      simp only [one_mul]; constructor <;> linarith⟩

/-- **Gap lemma** (one pair of Lemma NF). For a gap `A(x) + B(w)` there is a refinement of cost
`(16, 16)` on which the gap vanishes identically, or has strict constant sign and is
32-comparable to a basic quantity. -/
theorem gap_lemma (X : Finset α) (Y : Finset β) (hX : X.Nonempty) (hY : Y.Nonempty)
    (A : α → ℝ) (B : β → ℝ) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 16 * #X' ∧ #Y ≤ 16 * #Y' ∧
      ((∀ x ∈ X', ∀ w ∈ Y', A x + B w = 0) ∨
        (StrictSign (fun x w => A x + B w) X' Y' ∧
          Comparable (fun x w => A x + B w) 32 X' Y')) := by
  obtain ⟨X1, hX1, Y1, hY1, c1, c2, h⟩ := lemmaA X Y hX A (fun w => -B w)
  have hY1ne : Y1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hY; omega
  rcases h with ⟨c, hc⟩ | ⟨θ, hA, hB⟩ | ⟨θ, hA, hB⟩
  · -- `A` is constant: a column function `c + B w`
    rcases three_split Y1 (fun w => c + B w) with h | h | h
    · refine ⟨X1, hX1, Y1.filter fun w => c + B w < 0, (filter_subset _ _).trans hY1, by omega,
        by omega, Or.inr ⟨?_, ?_⟩⟩
      · exact Or.inr fun x hx w hw => by show A x + B w < 0; rw [hc x hx]; exact (mem_filter.1 hw).2
      · obtain ⟨qr, qc, h1, h2, h3⟩ := comparable_col X1 (Y1.filter fun w => c + B w < 0)
          (fun w => c + B w) (fun w hw => (mem_filter.1 hw).2.ne)
        exact ⟨qr, qc, h1, h2, fun x hx w hw => by
          show _ ≤ |A x + B w| ∧ |A x + B w| ≤ _; rw [hc x hx]; exact h3 x hx w hw⟩
    · refine ⟨X1, hX1, Y1.filter fun w => c + B w = 0, (filter_subset _ _).trans hY1, by omega,
        by omega, Or.inl ?_⟩
      intro x hx w hw; rw [hc x hx]; exact (mem_filter.1 hw).2
    · refine ⟨X1, hX1, Y1.filter fun w => 0 < c + B w, (filter_subset _ _).trans hY1, by omega,
        by omega, Or.inr ⟨?_, ?_⟩⟩
      · exact Or.inl fun x hx w hw => by show 0 < A x + B w; rw [hc x hx]; exact (mem_filter.1 hw).2
      · obtain ⟨qr, qc, h1, h2, h3⟩ := comparable_col X1 (Y1.filter fun w => 0 < c + B w)
          (fun w => c + B w) (fun w hw => (mem_filter.1 hw).2.ne')
        exact ⟨qr, qc, h1, h2, fun x hx w hw => by
          show _ ≤ |A x + B w| ∧ |A x + B w| ≤ _; rw [hc x hx]; exact h3 x hx w hw⟩
  · -- `θ < A x`, `-B w ≤ θ`: gap `= (A x - θ) + (θ + B w)`
    obtain ⟨X2, hX2, Y2, hY2, d1, d2, hcmp⟩ := sum_comparable X1 Y1 hY1ne (fun x => A x - θ)
      (fun w => θ + B w) (fun x hx => by linarith [hA x hx]) (fun w hw => by linarith [hB w hw])
    refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, by omega, by omega, Or.inr ⟨?_, ?_⟩⟩
    · exact Or.inl fun x hx w hw => by linarith [hA x (hX2 hx), hB w (hY2 hw)]
    · obtain ⟨qr, qc, h1, h2, h3⟩ := hcmp
      exact ⟨qr, qc, h1, h2, fun x hx w hw => by
        have := h3 x hx w hw; simp only at this; ring_nf at this ⊢; exact this⟩
  · -- `A x < θ`, `θ ≤ -B w`: gap `= -((θ - A x) + (-B w - θ))`
    obtain ⟨X2, hX2, Y2, hY2, d1, d2, hcmp⟩ := sum_comparable X1 Y1 hY1ne (fun x => θ - A x)
      (fun w => -B w - θ) (fun x hx => by linarith [hA x hx]) (fun w hw => by linarith [hB w hw])
    refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, by omega, by omega, Or.inr ⟨?_, ?_⟩⟩
    · exact Or.inr fun x hx w hw => by linarith [hA x (hX2 hx), hB w (hY2 hw)]
    · obtain ⟨qr, qc, h1, h2, h3⟩ := hcmp
      refine ⟨qr, qc, h1, h2, fun x hx w hw => ?_⟩
      have := h3 x hx w hw
      have e : |A x + B w| = |θ - A x + (-B w - θ)| := by
        rw [← abs_neg]; ring_nf
      rw [e]; exact this

/-- The gap between two types. -/
def gap (τ : ι → TF α β) (t t' : ι) (x : α) (w : β) : ℝ := (τ t).eval x w - (τ t').eval x w

/-- Two types are strictly ordered and their gap is comparable to a basic quantity (NF1, NF2). -/
def PairGood (τ : ι → TF α β) (t t' : ι) (X : Finset α) (Y : Finset β) : Prop :=
  StrictSign (gap τ t t') X Y ∧ Comparable (gap τ t t') 32 X Y

theorem PairGood.mono {τ : ι → TF α β} {t t' : ι} {X X' : Finset α} {Y Y' : Finset β}
    (h : PairGood τ t t' X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : PairGood τ t t' X' Y' :=
  ⟨h.1.mono hX hY, h.2.mono hX hY⟩

theorem gap_eq (τ : ι → TF α β) (t t' : ι) (x : α) (w : β) :
    gap τ t t' x w = ((τ t).rp x - (τ t').rp x) + ((τ t).cp w - (τ t').cp w) := by
  simp only [gap, TF.eval_eq]; ring

/-- **Pair step.** Refinement of cost `(16,16)` after which either one of the two types can be
deleted (it agrees with the other one everywhere) or the pair is good. -/
theorem pair_step (M : α → β → ℝ) (τ : ι → TF α β) (S : Finset ι) (X : Finset α)
    (Y : Finset β) (hX : X.Nonempty) (hY : Y.Nonempty) (hcov : Covers M τ S X Y) (t t' : ι) (ht : t ∈ S) (htt : t ≠ t') :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 16 * #X' ∧ #Y ≤ 16 * #Y' ∧ ∃ S' ⊆ S, Covers M τ S' X' Y' ∧
      (t' ∉ S' ∨ PairGood τ t t' X' Y') := by
  obtain ⟨X', hX', Y', hY', h1, h2, h⟩ := gap_lemma X Y hX hY
    (fun x => (τ t).rp x - (τ t').rp x) (fun w => (τ t).cp w - (τ t').cp w)
  refine ⟨X', hX', Y', hY', h1, h2, ?_⟩
  rcases h with h | ⟨hs, hc⟩
  · refine ⟨S.erase t', erase_subset _ _, fun x hx w hw => ?_, Or.inl (notMem_erase _ _)⟩
    obtain ⟨u, hu, hM⟩ := hcov x (hX' hx) w (hY' hw)
    by_cases hut : u = t'
    · subst hut
      have hg := h x hx w hw
      have : (τ t).eval x w = (τ u).eval x w := by
        have := gap_eq τ t u x w; simp only [gap] at this; linarith
      exact ⟨t, mem_erase.2 ⟨htt, ht⟩, by rw [hM, this]⟩
    · exact ⟨u, mem_erase.2 ⟨hut, hu⟩, hM⟩
  · refine ⟨S, subset_refl _, hcov.mono hX' hY', Or.inr ⟨?_, ?_⟩⟩
    · rcases hs with hs | hs
      · exact Or.inl fun x hx w hw => by rw [gap_eq]; exact hs x hx w hw
      · exact Or.inr fun x hx w hw => by rw [gap_eq]; exact hs x hx w hw
    · obtain ⟨qr, qc, a1, a2, a3⟩ := hc
      exact ⟨qr, qc, a1, a2, fun x hx w hw => by rw [gap_eq]; exact a3 x hx w hw⟩

/-- **Pairwise processing** (first half of Lemma NF): after a refinement of cost
`16^#P` per side, every pair of `P` whose members both survive is good. -/
theorem process_pairs (M : α → β → ℝ) (τ : ι → TF α β) (P : Finset (ι × ι)) :
    ∀ (S : Finset ι) (X : Finset α) (Y : Finset β), X.Nonempty → Y.Nonempty →
      Covers M τ S X Y →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 16 ^ #P * #X' ∧ #Y ≤ 16 ^ #P * #Y' ∧ ∃ S' ⊆ S,
        Covers M τ S' X' Y' ∧
        ∀ p ∈ P, p.1 ∈ S' → p.2 ∈ S' → p.1 ≠ p.2 → PairGood τ p.1 p.2 X' Y' := by
  induction P using Finset.induction_on with
  | empty =>
    intro S X Y _ _ hcov
    exact ⟨X, subset_refl _, Y, subset_refl _, by simp, by simp, S, subset_refl _, hcov,
      by simp⟩
  | insert a P haP ih =>
    intro S X Y hX hY hcov
    obtain ⟨X1, hX1, Y1, hY1, c1, c2, S1, hS1, hcov1, hgood1⟩ := ih S X Y hX hY hcov
    have hX1ne : X1.Nonempty := by
      rw [← card_pos]; have := card_pos.2 hX
      rcases Nat.eq_zero_or_pos #X1 with h | h
      · rw [h] at c1; omega
      · exact h
    have hY1ne : Y1.Nonempty := by
      rw [← card_pos]; have := card_pos.2 hY
      rcases Nat.eq_zero_or_pos #Y1 with h | h
      · rw [h] at c2; omega
      · exact h
    rw [card_insert_of_notMem haP, pow_succ]
    by_cases hcase : a.1 ∈ S1 ∧ a.1 ≠ a.2
    · obtain ⟨X2, hX2, Y2, hY2, d1, d2, S2, hS2, hcov2, h2⟩ :=
        pair_step M τ S1 X1 Y1 hX1ne hY1ne hcov1 a.1 a.2 hcase.1 hcase.2
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, ?_, ?_, S2, hS2.trans hS1, hcov2, ?_⟩
      · calc #X ≤ 16 ^ #P * #X1 := c1
          _ ≤ 16 ^ #P * (16 * #X2) := Nat.mul_le_mul_left _ d1
          _ = 16 ^ #P * 16 * #X2 := by ring
      · calc #Y ≤ 16 ^ #P * #Y1 := c2
          _ ≤ 16 ^ #P * (16 * #Y2) := Nat.mul_le_mul_left _ d2
          _ = 16 ^ #P * 16 * #Y2 := by ring
      · intro p hp hp1 hp2 hne
        rcases mem_insert.1 hp with rfl | hp
        · rcases h2 with h2 | h2
          · exact absurd hp2 h2
          · exact h2
        · exact (hgood1 p hp (hS2 hp1) (hS2 hp2) hne).mono hX2 hY2
    · refine ⟨X1, hX1, Y1, hY1, ?_, ?_, S1, hS1, hcov1, ?_⟩
      · calc #X ≤ 16 ^ #P * #X1 := c1
          _ ≤ 16 ^ #P * 16 * #X1 := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by norm_num))
      · calc #Y ≤ 16 ^ #P * #Y1 := c2
          _ ≤ 16 ^ #P * 16 * #Y1 := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by norm_num))
      · intro p hp hp1 hp2 hne
        rcases mem_insert.1 hp with rfl | hp
        · exact absurd ⟨hp1, hne⟩ hcase
        · exact hgood1 p hp hp1 hp2 hne

end E1088
