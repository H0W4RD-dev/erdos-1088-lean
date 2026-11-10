import Mathlib

/-!
# Refinement toolkit: medians, Lemma A and Lemma B of Theorem LR (round11/01)

A *refinement* of a rectangle `X × Y` with cost `(c₁, c₂)` is a sub-rectangle `X' × Y'` with
`#X ≤ c₁ * #X'` and `#Y ≤ c₂ * #Y'`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace E1088

variable {α β : Type*}

/-- Covering by three sets bounds the cardinality. -/
theorem card_le_of_cover3 [DecidableEq α] {X A B C : Finset α}
    (h : ∀ x ∈ X, x ∈ A ∨ x ∈ B ∨ x ∈ C) : #X ≤ #A + #B + #C := by
  have hsub : X ⊆ A ∪ B ∪ C := by
    intro x hx
    rcases h x hx with h | h | h <;> simp [h]
  calc #X ≤ #(A ∪ B ∪ C) := card_le_card hsub
    _ ≤ #(A ∪ B) + #C := card_union_le _ _
    _ ≤ #A + #B + #C := by have := card_union_le A B; omega

/-- Two-way pigeonhole. -/
theorem half_split (X : Finset α) (p : α → Prop) [DecidablePred p] :
    #X ≤ 2 * #(X.filter p) ∨ #X ≤ 2 * #(X.filter fun x => ¬ p x) := by
  have := card_filter_add_card_filter_not (s := X) p
  omega

/-- Existence of a median value. -/
theorem exists_median (X : Finset α) (hX : X.Nonempty) (a : α → ℝ) :
    ∃ θ, 2 * #(X.filter fun x => a x < θ) ≤ #X ∧ 2 * #(X.filter fun x => θ < a x) ≤ #X := by
  classical
  set V := X.filter fun x => 2 * #(X.filter fun y => a y < a x) ≤ #X with hV
  have hVne : V.Nonempty := by
    obtain ⟨x0, hx0, hmin⟩ := exists_min_image X a hX
    refine ⟨x0, mem_filter.2 ⟨hx0, ?_⟩⟩
    have : X.filter (fun y => a y < a x0) = ∅ :=
      filter_eq_empty_iff.2 fun y hy => not_lt.2 (hmin y hy)
    simp [this]
  obtain ⟨xs, hxs, hmax⟩ := exists_max_image V a hVne
  refine ⟨a xs, (mem_filter.1 hxs).2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hne : (X.filter fun x => a xs < a x).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; rw [h] at hcon; simp at hcon
  obtain ⟨y, hy, hymin⟩ := exists_min_image _ a hne
  obtain ⟨hyX, hya⟩ := mem_filter.1 hy
  have heq : X.filter (fun z => a z < a y) = X.filter (fun z => ¬ a xs < a z) := by
    ext z
    simp only [mem_filter, not_lt]
    constructor
    · rintro ⟨hz, hzy⟩
      refine ⟨hz, ?_⟩
      by_contra h
      push Not at h
      exact absurd (hymin z (mem_filter.2 ⟨hz, h⟩)) (not_le.2 hzy)
    · rintro ⟨hz, hzx⟩
      exact ⟨hz, lt_of_le_of_lt hzx hya⟩
  have hsum := card_filter_add_card_filter_not (s := X) (fun z => a xs < a z)
  have hyV : y ∈ V := by
    refine mem_filter.2 ⟨hyX, ?_⟩
    rw [heq]; omega
  exact absurd (hmax y hyV) (not_le.2 hya)

/-- Three-way split by comparison with `θ`. -/
theorem card_trichotomy (X : Finset α) (a : α → ℝ) (θ : ℝ) :
    #(X.filter fun x => a x < θ) + #(X.filter fun x => a x = θ) +
      #(X.filter fun x => θ < a x) = #X := by
  classical
  have e1 := card_filter_add_card_filter_not (s := X) (fun x => a x < θ)
  have e2 := card_filter_add_card_filter_not (s := X.filter fun x => ¬ a x < θ)
    (fun x => a x = θ)
  simp only [filter_filter] at e2
  have h1 : X.filter (fun x => ¬ a x < θ ∧ a x = θ) = X.filter (fun x => a x = θ) :=
    filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨by simp [h], h⟩⟩
  have h2 : X.filter (fun x => ¬ a x < θ ∧ ¬ a x = θ) = X.filter (fun x => θ < a x) :=
    filter_congr fun x _ => ⟨fun h => lt_of_le_of_ne (not_lt.1 h.1) (Ne.symm h.2),
      fun h => ⟨not_lt.2 h.le, h.ne'⟩⟩
  rw [h1, h2] at e2
  omega

/-- **Lemma A** (separating a row function from a column function). Refinement of cost
`(4, 2)` on which `a` is constant, or a threshold separates `a` from `b`. -/
theorem lemmaA (X : Finset α) (Y : Finset β) (hX : X.Nonempty) (a : α → ℝ) (b : β → ℝ) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 2 * #Y' ∧
      ((∃ c, ∀ x ∈ X', a x = c) ∨
       (∃ θ, (∀ x ∈ X', θ < a x) ∧ ∀ w ∈ Y', b w ≤ θ) ∨
       (∃ θ, (∀ x ∈ X', a x < θ) ∧ ∀ w ∈ Y', θ ≤ b w)) := by
  classical
  obtain ⟨θ, h1, h2⟩ := exists_median X hX a
  have h3 := card_trichotomy X a θ
  by_cases hc : #X ≤ 4 * #(X.filter fun x => a x = θ)
  · exact ⟨_, filter_subset _ _, Y, subset_refl _, hc, by omega,
      Or.inl ⟨θ, fun x hx => (mem_filter.1 hx).2⟩⟩
  rcases half_split Y (fun w => b w ≤ θ) with hY | hY
  · refine ⟨X.filter fun x => θ < a x, filter_subset _ _, _, filter_subset _ _, by omega, hY,
      Or.inr (Or.inl ⟨θ, fun x hx => (mem_filter.1 hx).2, fun w hw => (mem_filter.1 hw).2⟩)⟩
  · refine ⟨X.filter fun x => a x < θ, filter_subset _ _, _, filter_subset _ _, by omega, hY,
      Or.inr (Or.inr ⟨θ, fun x hx => (mem_filter.1 hx).2,
        fun w hw => le_of_lt (not_le.1 (mem_filter.1 hw).2)⟩)⟩

/-- **Lemma B** (trichotomy of scales). `D > 0` a row function, `E ≥ 0` a column function.
Refinement of cost `(4, 4)` on which `D ≥ 2E`, or `E ≥ 2D`, or both lie in `(s/4, 4s)`. -/
theorem lemmaB (X : Finset α) (Y : Finset β) (hY : Y.Nonempty) (D : α → ℝ) (E : β → ℝ)
    (hD : ∀ x ∈ X, 0 < D x) (_hE : ∀ w ∈ Y, 0 ≤ E w) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 4 * #Y' ∧
      ((∀ x ∈ X', ∀ w ∈ Y', 2 * E w ≤ D x) ∨
       (∀ x ∈ X', ∀ w ∈ Y', 2 * D x ≤ E w) ∨
       (∃ s > 0, (∀ x ∈ X', s / 4 < D x ∧ D x < 4 * s) ∧
          ∀ w ∈ Y', s / 4 < E w ∧ E w < 4 * s)) := by
  classical
  obtain ⟨s, h1, h2⟩ := exists_median Y hY E
  have h3 := card_trichotomy Y E s
  -- columns with `E ≤ s` and with `E ≥ s`
  have hle : #Y ≤ 2 * #(Y.filter fun w => E w ≤ s) := by
    have := card_le_of_cover3 (X := Y) (A := Y.filter fun w => E w ≤ s)
      (B := Y.filter fun w => s < E w) (C := ∅) (fun w hw => by
        rcases le_or_gt (E w) s with h | h
        · exact Or.inl (mem_filter.2 ⟨hw, h⟩)
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hw, h⟩)))
    simp at this; omega
  have hge : #Y ≤ 2 * #(Y.filter fun w => s ≤ E w) := by
    have := card_le_of_cover3 (X := Y) (A := Y.filter fun w => s ≤ E w)
      (B := Y.filter fun w => E w < s) (C := ∅) (fun w hw => by
        rcases le_or_gt s (E w) with h | h
        · exact Or.inl (mem_filter.2 ⟨hw, h⟩)
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hw, h⟩)))
    simp at this; omega
  rcases le_or_gt s 0 with hs | hs
  · refine ⟨X, subset_refl _, Y.filter fun w => E w ≤ s, filter_subset _ _, by omega, by omega,
      Or.inl ?_⟩
    intro x hx w hw
    have := (mem_filter.1 hw).2
    have := hD x hx
    linarith
  by_cases hA : #X ≤ 4 * #(X.filter fun x => 2 * s ≤ D x)
  · refine ⟨_, filter_subset _ _, Y.filter fun w => E w ≤ s, filter_subset _ _, hA, by omega,
      Or.inl ?_⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2; have := (mem_filter.1 hw).2; linarith
  by_cases hB : #X ≤ 4 * #(X.filter fun x => D x ≤ s / 2)
  · refine ⟨_, filter_subset _ _, Y.filter fun w => s ≤ E w, filter_subset _ _, hB, by omega,
      Or.inr (Or.inl ?_)⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2; have := (mem_filter.1 hw).2; linarith
  set R1 := X.filter fun x => s / 2 < D x ∧ D x < 2 * s with hR1
  have hR1c : #X ≤ 2 * #R1 := by
    have := card_le_of_cover3 (X := X) (A := R1) (B := X.filter fun x => 2 * s ≤ D x)
      (C := X.filter fun x => D x ≤ s / 2) (fun x hx => by
        by_cases h1 : 2 * s ≤ D x
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hx, h1⟩))
        by_cases h2 : D x ≤ s / 2
        · exact Or.inr (Or.inr (mem_filter.2 ⟨hx, h2⟩))
        exact Or.inl (mem_filter.2 ⟨hx, not_le.1 h2, not_le.1 h1⟩))
    omega
  by_cases hC : #Y ≤ 4 * #(Y.filter fun w => E w ≤ s / 4)
  · refine ⟨R1, filter_subset _ _, _, filter_subset _ _, by omega, hC, Or.inl ?_⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2.1; have := (mem_filter.1 hw).2; linarith
  by_cases hC' : #Y ≤ 4 * #(Y.filter fun w => 4 * s ≤ E w)
  · refine ⟨R1, filter_subset _ _, _, filter_subset _ _, by omega, hC', Or.inr (Or.inl ?_)⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2.2; have := (mem_filter.1 hw).2; linarith
  set C1 := Y.filter fun w => s / 4 < E w ∧ E w < 4 * s with hC1
  have hC1c : #Y ≤ 2 * #C1 := by
    have := card_le_of_cover3 (X := Y) (A := C1) (B := Y.filter fun w => E w ≤ s / 4)
      (C := Y.filter fun w => 4 * s ≤ E w) (fun w hw => by
        by_cases h1 : E w ≤ s / 4
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hw, h1⟩))
        by_cases h2 : 4 * s ≤ E w
        · exact Or.inr (Or.inr (mem_filter.2 ⟨hw, h2⟩))
        exact Or.inl (mem_filter.2 ⟨hw, not_le.1 h1, not_le.1 h2⟩))
    omega
  refine ⟨R1, filter_subset _ _, C1, filter_subset _ _, by omega, by omega,
    Or.inr (Or.inr ⟨s, hs, fun x hx => ?_, fun w hw => (mem_filter.1 hw).2⟩)⟩
  have := (mem_filter.1 hx).2
  constructor <;> linarith [this.1, this.2]

end E1088
