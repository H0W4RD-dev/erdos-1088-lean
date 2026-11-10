import E1088.Round

/-!
# Theorem LR (label rounding), round11/01

Rank-`r` matrix whose entries on `X × Y` are covered by `k` row/column type functions
⟹ a single-type rectangle of relative size `≥ 1 / LRcost k r` on each side.

Everything here is proved except `lemmaR` (E1088/LemmaR.lean), which is assumed.
-/

set_option linter.unusedSectionVars false

open Finset

namespace E1088

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

/-- **One elimination round, core** (Lemma R + GL). The positive entries of `N` are covered by
the types `A`, negative entries match no type of `A`, and positives are the majority. Then on a
refinement of cost `64 R' 4^T` the types `A` cover everything. -/
theorem round_core (M N : α → β → ℝ) (τ : ι → TF α β) (A : Finset ι) (X : Finset α)
    (Y : Finset β) (r R' : ℕ) (K : ℝ) (hr : rankOn M X Y ≤ r) (hN : rankOn N X Y ≤ r + 2)
    (hR' : (r + 1) ^ #A ≤ R') (hR1 : 1 ≤ R')
    (hbd : ∀ x ∈ X, ∀ w ∈ Y, 1 / 2 ≤ |N x w| ∧ |N x w| ≤ K)
    (hposA : ∀ x ∈ X, ∀ w ∈ Y, 0 < N x w → ∃ t ∈ A, M x w = (τ t).eval x w)
    (hnegA : ∀ x ∈ X, ∀ w ∈ Y, N x w < 0 → ∀ t ∈ A, M x w ≠ (τ t).eval x w)
    (hmaj : #X * #Y ≤ 2 * #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y,
      (#X : ℝ) ≤ 64 * R' * 4 ^ roundsT K (1 / (16 * R')) (r + 2) * #X' ∧
      (#Y : ℝ) ≤ 64 * R' * 4 ^ roundsT K (1 / (16 * R')) (r + 2) * #Y' ∧
      Covers M τ A X' Y' := by
  classical
  set δ : ℝ := 1 / (16 * R') with hδ
  have hR'pos : (0 : ℝ) < R' := by exact_mod_cast hR1
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ R' := by exact_mod_cast hR1
    linarith
  have hpos : δ * (#X * #Y) ≤ #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2) := by
    have h1 : ((#X * #Y : ℕ) : ℝ) ≤ 2 * #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2) := by
      exact_mod_cast hmaj
    have h2 : (0 : ℝ) ≤ #X * #Y := by positivity
    push_cast at h1
    nlinarith
  obtain ⟨X1, hX1, Y1, hY1, c1, c2, hneg⟩ := lemmaR N X Y (r + 2) K δ hN hbd hδ0 hδ1 hpos
  set T := roundsT K δ (r + 2)
  -- the Hadamard product over `A`
  set H : α → β → ℝ := fun x w => ∏ t ∈ A, (M x w - (τ t).eval x w) with hH
  have hHrank : rankOn H X1 Y1 ≤ R' :=
    (rankOn_prod_sub M τ A X1 Y1 r ((rankOn_mono M hX1 hY1).trans hr)).trans hR'
  have hsupp : supp H X1 Y1 ⊆ (X1 ×ˢ Y1).filter fun p => N p.1 p.2 < 0 := by
    intro p hp
    obtain ⟨hpXY, hHp⟩ := mem_filter.1 hp
    obtain ⟨hpx, hpy⟩ := mem_product.1 hpXY
    refine mem_filter.2 ⟨hpXY, ?_⟩
    have hb := hbd p.1 (hX1 hpx) p.2 (hY1 hpy)
    rcases lt_trichotomy (N p.1 p.2) 0 with h | h | h
    · exact h
    · rw [h] at hb; norm_num at hb
    · obtain ⟨t, ht, hM⟩ := hposA p.1 (hX1 hpx) p.2 (hY1 hpy) h
      exact absurd (prod_eq_zero ht (by rw [hM]; ring)) hHp
  have hsuppc : 16 * R' * #(supp H X1 Y1) ≤ #X1 * #Y1 := by
    have h1 : (#(supp H X1 Y1) : ℝ) ≤ δ * (#X1 * #Y1) :=
      (by exact_mod_cast card_le_card hsupp : (#(supp H X1 Y1) : ℝ) ≤ _).trans hneg
    have h2 : ((16 * R' * #(supp H X1 Y1) : ℕ) : ℝ) ≤ ((#X1 * #Y1 : ℕ) : ℝ) := by
      push_cast
      rw [hδ] at h1
      have : (16 * R' : ℝ) * (1 / (16 * R') * (#X1 * #Y1)) = #X1 * #Y1 := by
        field_simp
      nlinarith
    exact_mod_cast h2
  obtain ⟨X2, hX2, Y2, hY2, d1, d2, hzero⟩ := cleaning H X1 Y1 R' hR1 hHrank hsuppc
  refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, ?_, ?_, ?_⟩
  · have e1 : (#X1 : ℝ) ≤ 2 * #X2 := by exact_mod_cast d1
    have e2 : (16 * R' : ℝ) * δ = 1 := by rw [hδ]; field_simp
    have h4 : (0 : ℝ) ≤ 4 ^ T := by positivity
    calc (#X : ℝ) = 16 * R' * 2 * (δ / 2 * #X) := by
          rw [show (16 * R' * 2 : ℝ) * (δ / 2 * #X) = (16 * R' * δ) * #X by ring, e2, one_mul]
      _ ≤ 16 * R' * 2 * (4 ^ T * #X1) := by gcongr
      _ ≤ 16 * R' * 2 * (4 ^ T * (2 * #X2)) := by gcongr
      _ ≤ 64 * R' * 4 ^ T * #X2 := by nlinarith
  · have e1 : (#Y1 : ℝ) ≤ 2 * #Y2 := by exact_mod_cast d2
    have e2 : (16 * R' : ℝ) * δ = 1 := by rw [hδ]; field_simp
    have h4 : (0 : ℝ) ≤ 4 ^ T := by positivity
    calc (#Y : ℝ) = 16 * R' * 2 * (δ / 2 * #Y) := by
          rw [show (16 * R' * 2 : ℝ) * (δ / 2 * #Y) = (16 * R' * δ) * #Y by ring, e2, one_mul]
      _ ≤ 16 * R' * 2 * (4 ^ T * #Y1) := by gcongr
      _ ≤ 16 * R' * 2 * (4 ^ T * (2 * #Y2)) := by gcongr
      _ ≤ 64 * R' * 4 ^ T * #Y2 := by nlinarith
  · intro x hx w hw
    have := hzero x hx w hw
    obtain ⟨t, ht, h0⟩ := prod_eq_zero_iff.1 this
    exact ⟨t, ht, by linarith⟩

end E1088
