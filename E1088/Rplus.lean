import E1088.G1Count
import E1088.Skeleton

/-!
# Theorem R⁺: the base level Claim(n-2) (proved from G1) and the combined statement

Manuscript Section 7.1, "Proof of Claim(n-2)": for a level-`(n-2)` configuration every label has
degree `< (n-2)σ`; if `|W| ≥ 4(n-2)²σ` the degree form of G1 gives `|W| ≤ σ_min ≤ σ`, a
contradiction. Hence Claim(n-2) with `Γ_{n-2} = 4(n-2)²`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem LRcost_mono (r : ℕ) {k k' : ℕ} (h : k ≤ k') : LRcost k r ≤ LRcost k' r := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    simp only [LRcost]
    have h1 := one_le_roundCost (m + 1) r
    have h2 := one_le_LRcost m r
    nlinarith

theorem kG_le_kstar (n : ℕ) : kG n ≤ kstar n := by
  unfold kG kstar
  have h1 : (n - 2).choose 2 ≤ (n - 2) * (n - 2) := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have h2 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h3 : n < 6 ^ n := Nat.lt_pow_self (by norm_num)
  have h4 : n ^ 2 = n * n := sq n
  have h5 : n ≤ n * n := Nat.le_mul_self n
  rw [h4]
  generalize (n - 2).choose 2 = C at *
  generalize (n - 2) * (n - 2) = P at *
  generalize n * n = Z at *
  generalize 6 ^ n = Y at *
  omega

theorem ClaimAt.mono_Γ {X : Finset (ℝ^d)} {j : ℕ} {Γ Γ' σmin : ℝ} (hσ : 0 ≤ σmin)
    (hΓ : Γ ≤ Γ') (h : ClaimAt X j Γ σmin) : ClaimAt X j Γ' σmin := by
  intro S W σ hc hs
  have := h S W σ hc hs
  have : 0 ≤ σ := hσ.trans hs
  nlinarith

/-- **Claim(n-2)** with `Γ_{n-2} = 4(n-2)²` (manuscript Section 7.1). -/
theorem claim_top (n : ℕ) (hn : 4 ≤ n) (d D h : ℕ) (X : Finset (ℝ^d)) (hX : Ambient n D h X) :
    ClaimAt X (n - 2) (4 * ((n - 2 : ℕ) : ℝ) ^ 2) (smin n D h) := by
  classical
  intro S W σ hc hσ
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  by_contra hcon
  push Not at hcon
  have hS : S.card + 2 = n := by rw [hc.card]; omega
  have hS1 : S.Nonempty := card_pos.1 (by rw [hc.card]; omega)
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hn2 : (2 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 2 by omega)
  have hdeg : ∀ v : ℝ, 4 * (n - 2) * (W.filter fun x => v ∈ labels S x).card ≤ W.card := by
    intro v
    have hsub : (W.filter fun x => v ∈ labels S x) ⊆ S.biUnion fun s => W.filter fun x => dist x s = v := by
      intro x hx
      obtain ⟨hxW, hv⟩ := mem_filter.1 hx
      obtain ⟨s, hs, hsv⟩ := mem_image.1 hv
      exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hxW, hsv⟩⟩
    have hc1 : ((W.filter fun x => v ∈ labels S x).card : ℝ) ≤ ((n - 2 : ℕ) : ℝ) * σ := by
      have h1 := (card_le_card hsub).trans card_biUnion_le
      have h2 : ∀ s ∈ S, ((W.filter fun x => dist x s = v).card : ℝ) ≤ σ := by
        intro s hs
        by_cases hv : 0 < v
        · exact (hc.cap s hs v hv).le
        · have : (W.filter fun x => dist x s = v) = ∅ := by
            rw [filter_eq_empty_iff]
            intro x hx hxv
            have := dist_pos.2 (fun e : x = s => hWS x hx (e ▸ hs))
            rw [hxv] at this; exact hv this
          rw [this, card_empty, Nat.cast_zero]; linarith
      calc ((W.filter fun x => v ∈ labels S x).card : ℝ)
          ≤ ∑ s ∈ S, ((W.filter fun x => dist x s = v).card : ℝ) := by exact_mod_cast h1
        _ ≤ ∑ _s ∈ S, σ := sum_le_sum h2
        _ = ((n - 2 : ℕ) : ℝ) * σ := by rw [sum_const, nsmul_eq_mul, hc.card]
    have key : (4 : ℝ) * ((n - 2 : ℕ) : ℝ) * ((W.filter fun x => v ∈ labels S x).card : ℝ) ≤
        W.card := by
      have h0 : (0 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have : 4 * ((n - 2 : ℕ) : ℝ) * ((W.filter fun x => v ∈ labels S x).card : ℝ) ≤
          4 * ((n - 2 : ℕ) : ℝ) * (((n - 2 : ℕ) : ℝ) * σ) :=
        mul_le_mul_of_nonneg_left hc1 (by positivity)
      nlinarith
    exact_mod_cast key
  have hG := G1_degree n D h X S W hX.free hX.dim hX.half hc.subX hS hS1 hc.subW
    (fun x hx => ⟨hWS x hx, hc.ext x hx⟩) hdeg
  -- `4 · 4^{n-2} · LRcost(k_G) · h ≤ 3 σ_min`
  have hL := LRcost_mono (D + 2) (kG_le_kstar n)
  have hL1 := one_le_LRcost (kG n) (D + 2)
  have h4 : (4 : ℝ) * 4 ^ (n - 2) ≤ 4 ^ (n + 1) := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hbound : 4 * (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h)) ≤ smin n D h := by
    unfold smin
    have e1 : LRcost (kG n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * (h + 1) :=
      mul_le_mul hL (by linarith) hh0 (by linarith)
    calc 4 * (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h))
        = (4 * 4 ^ (n - 2)) * (LRcost (kG n) (D + 2) * h) := by ring
      _ ≤ 4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * (h + 1)) :=
          mul_le_mul h4 e1 (by positivity) (by positivity)
      _ = _ := by ring
  have hW : 3 * (W.card : ℝ) ≤ smin n D h := hG.trans hbound
  have hn2' : (1 : ℝ) ≤ 4 * ((n - 2 : ℕ) : ℝ) ^ 2 := by nlinarith
  have : (W.card : ℝ) ≤ σ := by nlinarith [Nat.cast_nonneg (α := ℝ) W.card]
  nlinarith

end E1088
