import E1088.Rplus

/-!
# The covering pattern GL + LR + OR (used in the Slicing Lemma, Core Lemma, Theorem R⁺)

Rows `R0`, columns `C0` inside `X`. Types: column functions `colF i` (`i ∈ J`) and "bisector" row
functions `x ↦ ‖x - s‖²` (`s ∈ P`). If in every column all but `|R0| / (16 (D+2)^k)` rows are
covered by a type (`k = |J| + |P| ≤ k*`) and `|R0| > 2 LRcost(k*, D+2) h`, then
`|C0| ≤ 2 LRcost(k*, D+2) h`.

Proof: the kill matrix `∏ (‖x-c‖² - type)` has rank `≤ (D+2)^k` (HP) and few nonzeros, so GL gives
a half×half zero rectangle; there every entry is covered by a type, LR gives a single-type
rectangle, and every type gives an orthogonal split (column type: equidistance; row type
`‖x-s‖²`: bisector `H(s, c)`).
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- **GL + LR + OR covering lemma.** -/
theorem gl_lr_or {ι : Type*} [DecidableEq ι] (n D h : ℕ) (X : Finset (ℝ^d))
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (R0 C0 : Finset (ℝ^d)) (hR0 : R0 ⊆ X) (hC0 : C0 ⊆ X) (J : Finset ι)
    (colF : ι → ℝ^d → ℝ) (P : Finset (ℝ^d)) (hk : J.card + P.card ≤ kstar n)
    (hfew : ∀ c ∈ C0, 16 * (D + 2) ^ (J.card + P.card) *
      (R0.filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card ≤ R0.card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < R0.card) :
    (C0.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  classical
  set k := J.card + P.card with hkdef
  set LRc := LRcost (kstar n) (D + 2) with hLRc
  have hLR1 : 1 ≤ LRc := one_le_LRcost _ _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  rcases C0.eq_empty_or_nonempty with hCe | hCne
  · rw [hCe, card_empty, Nat.cast_zero]; positivity
  have hRne : R0.Nonempty := by
    rw [← card_pos]; have : (0 : ℝ) < R0.card := by nlinarith
    exact_mod_cast this
  -- the kill matrix
  let B : ℝ^d → ℝ^d → ℝ := fun x c =>
    (∏ i ∈ J, (‖x - c‖ ^ 2 - colF i c)) * ∏ s ∈ P, (‖x - c‖ ^ 2 - ‖x - s‖ ^ 2)
  have hBzero : ∀ x c, B x c ≠ 0 → (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
      ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2 := by
    intro x c hB
    simp only [B, ne_eq, mul_eq_zero, not_or, prod_eq_zero_iff, not_exists, not_and] at hB
    exact ⟨fun i hi h => hB.1 i hi (by rw [h]; ring),
      fun s hs h => hB.2 s hs (by rw [h]; ring)⟩
  have hrank : rankOn B R0 C0 ≤ (D + 2) ^ k := by
    unfold rankOn
    let F : ι ⊕ ℝ^d → ℝ^d → ℝ^d → ℝ := fun t => match t with
      | Sum.inl i => fun x c => ‖x - c‖ ^ 2 - 0 - colF i c
      | Sum.inr s => fun x c => ‖x - c‖ ^ 2 - ‖x - s‖ ^ 2 - 0
    have hB : (Matrix.of fun (x : R0) (c : C0) => B x c) =
        Matrix.of fun (x : R0) (c : C0) => ∏ t ∈ J.disjSum P, F t x c := by
      ext x c
      simp only [Matrix.of_apply, B, prod_disjSum, F, sub_zero]
    rw [hB]
    refine (rank_finset_prod_le (J.disjSum P) (fun t => Matrix.of fun (x : R0) (c : C0) =>
      F t x c)).trans ?_
    calc ∏ t ∈ J.disjSum P, (Matrix.of fun (x : R0) (c : C0) => F t x c).rank
        ≤ ∏ _t ∈ J.disjSum P, (D + 2) := by
          refine prod_le_prod' fun t _ => ?_
          rcases t with i | s
          · exact rank_sqdist_le_affine X D hD (fun x : R0 => (x : ℝ^d)) (fun c : C0 => (c : ℝ^d))
              (fun x => hR0 x.2) (fun c => hC0 c.2) (fun _ => 0) (fun c => colF i c)
          · exact rank_sqdist_le_affine X D hD (fun x : R0 => (x : ℝ^d)) (fun c : C0 => (c : ℝ^d))
              (fun x => hR0 x.2) (fun c => hC0 c.2) (fun x => ‖(x : ℝ^d) - s‖ ^ 2) (fun _ => 0)
      _ = (D + 2) ^ k := by rw [prod_const, card_disjSum]
  have hsupp : 16 * (D + 2) ^ k * (supp B R0 C0).card ≤ R0.card * C0.card := by
    rw [card_supp_eq_sum', mul_sum]
    calc ∑ c ∈ C0, 16 * (D + 2) ^ k * (R0.filter fun x => B x c ≠ 0).card
        ≤ ∑ _c ∈ C0, R0.card := by
          refine sum_le_sum fun c hc => le_trans ?_ (hfew c hc)
          exact Nat.mul_le_mul_left _ (card_le_card fun x hx =>
            mem_filter.2 ⟨(mem_filter.1 hx).1, hBzero x c (mem_filter.1 hx).2⟩)
      _ = R0.card * C0.card := by rw [sum_const, smul_eq_mul, mul_comm]
  obtain ⟨R1, hR1, C1, hC1, c1, c2, hzero⟩ :=
    cleaning B R0 C0 ((D + 2) ^ k) (Nat.one_le_pow _ _ (by omega)) hrank hsupp
  have hR1ne : R1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hRne; omega
  have hC1ne : C1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hCne; omega
  -- LR on the zero rectangle
  let τ : ι ⊕ ℝ^d → TF (ℝ^d) (ℝ^d) := fun t => match t with
    | Sum.inl i => TF.col (colF i)
    | Sum.inr s => TF.row fun x => ‖x - s‖ ^ 2
  let M : ℝ^d → ℝ^d → ℝ := fun x c => ‖x - c‖ ^ 2
  have hcov : Covers M τ (J.disjSum P) R1 C1 := by
    intro x hx c hc
    have h0 := hzero x hx c hc
    simp only [B, mul_eq_zero, prod_eq_zero_iff] at h0
    rcases h0 with ⟨i, hi, hi0⟩ | ⟨s, hs, hs0⟩
    · exact ⟨Sum.inl i, inl_mem_disjSum.2 hi, by simp only [M, τ, TF.eval]; linarith⟩
    · exact ⟨Sum.inr s, inr_mem_disjSum.2 hs, by simp only [M, τ, TF.eval]; linarith⟩
  have hrankM : rankOn M R1 C1 ≤ D + 2 := by
    unfold rankOn
    have := rank_sqdist_le_affine X D hD (fun x : R1 => (x : ℝ^d)) (fun c : C1 => (c : ℝ^d))
      (fun x => hR0 (hR1 x.2)) (fun c => hC0 (hC1 c.2)) (fun _ => 0) (fun _ => 0)
    have e : (Matrix.of fun (x : R1) (c : C1) => M x c) =
        Matrix.of fun (x : R1) (c : C1) => ‖(x : ℝ^d) - c‖ ^ 2 - 0 - 0 := by
      ext; simp [M]
    rw [e]; exact this
  obtain ⟨R2, hR2, C2, hC2, t₀, -, e1, e2, hM⟩ :=
    theoremLR M τ (D + 2) (kstar n) (J.disjSum P) R1 C1 (by rw [card_disjSum]; exact hk)
      hR1ne hC1ne hrankM hcov
  have hortho : ∀ x ∈ R2, ∀ x' ∈ R2, ∀ c ∈ C2, ∀ c' ∈ C2, inner ℝ (x - x') (c - c') = 0 := by
    rcases t₀ with i | s
    · refine ortho_of_equidistant R2 C2 (fun c => Real.sqrt (colF i c)) fun x hx c hc => ?_
      have := hM x hx c hc
      simp only [M, τ, TF.eval] at this
      rw [← this, Real.sqrt_sq (norm_nonneg _)]
    · refine ortho_of_bisector R2 C2 s fun x hx c hc => ?_
      have := hM x hx c hc
      simp only [M, τ, TF.eval] at this
      exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this).symm
  have hRC : affDim (R2 ∪ C2) ≤ D :=
    (affDim_mono (union_subset ((hR2.trans hR1).trans hR0) ((hC2.trans hC1).trans hC0))).trans hD
  have hmin := min_affDim_le_of_ortho R2 C2 D hRC hortho
  have hc1r : (R0.card : ℝ) ≤ 2 * R1.card := by exact_mod_cast c1
  have hc2r : (C0.card : ℝ) ≤ 2 * C1.card := by exact_mod_cast c2
  rcases le_total (affDim R2) (affDim C2) with hle | hle
  · rw [min_eq_left hle] at hmin
    have hR := hh R2 ((hR2.trans hR1).trans hR0) hmin
    have : (R2.card : ℝ) ≤ h := by exact_mod_cast hR
    have : (R0.card : ℝ) ≤ 2 * LRc * h := by
      calc (R0.card : ℝ) ≤ 2 * R1.card := hc1r
        _ ≤ 2 * (LRc * R2.card) := by linarith
        _ ≤ 2 * LRc * h := by nlinarith
    linarith
  · rw [min_eq_right hle] at hmin
    have hC := hh C2 ((hC2.trans hC1).trans hC0) hmin
    have : (C2.card : ℝ) ≤ h := by exact_mod_cast hC
    calc (C0.card : ℝ) ≤ 2 * C1.card := hc2r
      _ ≤ 2 * (LRc * C2.card) := by linarith
      _ ≤ 2 * LRc * h := by nlinarith

end E1088
