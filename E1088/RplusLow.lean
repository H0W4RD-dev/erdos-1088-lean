import E1088.RplusStep
import E1088.CoreFinal

/-!
# Theorem R⁺ at levels `n-3` and `n-4` (manuscript Theorem 7.1), proved

From Claim(n-2) (`claim_top`) two applications of `rplus_step` give Claim(n-3) and Claim(n-4),
with constants `(D+2)^c`, `c` depending only on `n`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem kA_le_kstar (n : ℕ) (hn : 4 ≤ n) : kA n ≤ kstar n := by
  unfold kA kstar
  have h1 := choose_two_le_sq' (n - 2)
  have h3 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h4 : 4 * n ≤ n * n := Nat.mul_le_mul_right n hn
  rw [sq]
  generalize (n - 2).choose 2 = C1 at *
  generalize (n - 2) * (n - 2) = P at *
  generalize n * n = Z at *
  generalize 6 ^ n = Y at *
  omega

theorem two_pow_le_E (E : ℝ) (hE : 2 ≤ E) (k : ℕ) : (2 : ℝ) ^ k ≤ E ^ k :=
  pow_le_pow_left₀ (by norm_num) hE k

theorem nat_le_E_pow (E : ℝ) (hE : 2 ≤ E) (k : ℕ) : (k : ℝ) ≤ E ^ k := by
  have h1 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
  exact h1.le.trans (two_pow_le_E E hE k)

/-- The exponent added by one application of `rplus_step`. -/
def cAdd (n : ℕ) : ℕ := 27 + 2 * n + 5 * kA n + 2 * n + 3 + 2 * (2 + 2 * n + n ^ 2)

/-- One level down: Claim(r+1) with `E^c` gives Claim(r) with `E^{c + cAdd n}`. -/
theorem claim_step_Rplus (n : ℕ) (hn : 4 ≤ n) (D h : ℕ) (X : Finset (ℝ^d))
    (hX : Ambient n D h X) (r : ℕ) (hr : n - 4 ≤ r) (hrn : r ≤ n) (c : ℕ)
    (hcl : ClaimAt X (r + 1) (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h)) :
    ClaimAt X r (((D + 2 : ℕ) : ℝ) ^ (c + cAdd n)) (smin n D h) := by
  intro S W σ hc hσ
  set E : ℝ := ((D + 2 : ℕ) : ℝ) with hE
  have hE2 : 2 ≤ E := by rw [hE]; exact_mod_cast (show 2 ≤ D + 2 by omega)
  have hE1 : 1 ≤ E := by linarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hΓ0 : (0 : ℝ) ≤ E ^ c := by positivity
  have hW := rplus_step n hn D h X hX r hr (E ^ c) (QA n D * σ) σ hcl S W hc hΓ0 hσ rfl
    (kA_le_kstar n hn)
  have he : 2 * LRcost (kstar n) (D + 2) * h ≤ σ := (e_lt_smin n D h).le.trans hσ
  set q := 27 + 2 * n + 5 * kA n with hq
  have hQ : QA n D ≤ E ^ q := by
    unfold QA
    rw [← hE]
    have h1 : (2 : ℝ) ^ 27 ≤ E ^ 27 := two_pow_le_E E hE2 27
    have h2 : (n : ℝ) ^ 2 ≤ E ^ (2 * n) := by
      rw [pow_mul']
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (nat_le_E_pow E hE2 n) 2
    have h3 : (E ^ kA n) ^ 5 = E ^ (5 * kA n) := by rw [← pow_mul, mul_comm]
    rw [h3, hq, pow_add, pow_add]
    have : (0 : ℝ) ≤ n ^ 2 := by positivity
    have := mul_le_mul h1 h2 this (by positivity)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  -- the bracket
  set N := c + q + 2 * n with hN
  have hEN : ∀ k, k ≤ N → E ^ k ≤ E ^ N := fun k hk => pow_le_pow_right₀ hE1 hk
  have b1 : E ^ c * (QA n D * σ) ≤ E ^ N * σ := by
    have : E ^ c * QA n D ≤ E ^ (c + q) := by
      rw [pow_add]; exact mul_le_mul_of_nonneg_left hQ hΓ0
    have h' : E ^ (c + q) ≤ E ^ N := hEN _ (by omega)
    have := mul_le_mul_of_nonneg_right (this.trans h') hσ0
    linarith [show E ^ c * (QA n D * σ) = E ^ c * QA n D * σ by ring]
  have b2 : (r : ℝ) ^ 2 * σ ≤ E ^ N * σ := by
    have : (r : ℝ) ^ 2 ≤ E ^ N := by
      have e1 : (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
        have : (r : ℝ) ≤ n := by exact_mod_cast hrn
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
      have e2 : (n : ℝ) ^ 2 ≤ E ^ (2 * n) := by
        rw [pow_mul']
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (nat_le_E_pow E hE2 n) 2
      exact e1.trans (e2.trans (hEN _ (by omega)))
    exact mul_le_mul_of_nonneg_right this hσ0
  have b3 : 2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ ≤ E ^ N * σ := by
    have e1 : (4 : ℝ) + 2 * (n - 4 : ℕ) ≤ E ^ N := by
      have : ((4 + 2 * (n - 4) : ℕ) : ℝ) ≤ E ^ (4 + 2 * (n - 4)) := nat_le_E_pow E hE2 _
      push_cast at this
      exact this.trans (hEN _ (by omega))
    have := mul_le_mul_of_nonneg_right e1 hσ0
    linarith [he]
  have b4 : (1 : ℝ) ≤ E ^ N * σ := by
    have : (1 : ℝ) ≤ E ^ N := one_le_pow₀ hE1
    nlinarith
  have hbr : E ^ c * (QA n D * σ) + r ^ 2 * σ +
      (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1 ≤ E ^ (N + 3) * σ := by
    have : (4 : ℝ) * (E ^ N * σ) ≤ E ^ (N + 3) * σ := by
      have e : E ^ (N + 3) * σ = E ^ 3 * (E ^ N * σ) := by rw [pow_add]; ring
      rw [e]
      have h8 : (4 : ℝ) ≤ E ^ 3 := by
        have := two_pow_le_E E hE2 3; norm_num at this; linarith
      have h0 : 0 ≤ E ^ N * σ := by positivity
      exact mul_le_mul_of_nonneg_right h8 h0
    linarith
  -- the prefactor
  have hM : ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) ≤ E ^ (2 * (2 + 2 * n + n ^ 2)) := by
    have hds : (dists S).card ≤ n ^ 2 := by
      have := card_dists_le S
      rw [hc.card] at this
      have h2 := choose_two_le_sq' r
      have h3 : r * r ≤ n * n := Nat.mul_le_mul hrn hrn
      rw [sq]; omega
    have hcast : ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) =
        E ^ ((2 + 2 * r + (dists S).card) * 2) := by rw [hE]; push_cast; ring
    rw [hcast]
    exact pow_le_pow_right₀ hE1 (by
      have : 2 + 2 * r + (dists S).card ≤ 2 + 2 * n + n ^ 2 := by omega
      calc (2 + 2 * r + (dists S).card) * 2 ≤ (2 + 2 * n + n ^ 2) * 2 := by omega
        _ = 2 * (2 + 2 * n + n ^ 2) := by ring)
  have hM0 : (0 : ℝ) ≤ ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) := by positivity
  calc (W.card : ℝ) ≤ ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) *
        (E ^ c * (QA n D * σ) + r ^ 2 * σ +
          (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1) := hW
    _ ≤ E ^ (2 * (2 + 2 * n + n ^ 2)) * (E ^ (N + 3) * σ) := by
        have hQA0 : 0 ≤ QA n D := by unfold QA; positivity
        have he0 := e_nonneg n D h
        have hbr0 : 0 ≤ E ^ c * (QA n D * σ) + r ^ 2 * σ +
            (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1 := by
          have t1 : 0 ≤ E ^ c * (QA n D * σ) := mul_nonneg hΓ0 (mul_nonneg hQA0 hσ0)
          have t2 : (0 : ℝ) ≤ r ^ 2 * σ := mul_nonneg (sq_nonneg _) hσ0
          have t3 : (0 : ℝ) ≤ 2 * (n - 4 : ℕ) * σ := mul_nonneg (by positivity) hσ0
          linarith
        exact mul_le_mul hM hbr hbr0 (pow_nonneg (by linarith) _)
    _ = E ^ (c + cAdd n) * σ := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        simp only [cAdd, hN, hq]; ring

/-- **Theorem R⁺, levels `n-3` and `n-4`** (manuscript Theorem 7.1), proved. -/
theorem theorem_Rplus_low_proved (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ∀ j, n - 4 ≤ j → j ≤ n - 3 → ClaimAt X j (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
  refine ⟨4 * n ^ 2 + 2 * cAdd n, fun d D h X hX hD j hj1 hj2 => ?_⟩
  have ha1 : (1 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ D + 2 by omega)
  have ha2 : (2 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ D + 2 by omega)
  have hs0 : 0 ≤ smin n D h := le_trans zero_le_one (one_le_smin n D h)
  -- Claim(n-2) with `E^{4n²}`
  have htop : ClaimAt X (n - 2) (((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2)) (smin n D h) := by
    refine (claim_top n hn d D h X hX).mono_Γ hs0 ?_
    have h1 : ((4 * (n - 2) ^ 2 : ℕ) : ℝ) < 2 ^ (4 * (n - 2) ^ 2) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) :=
      pow_le_pow_left₀ (by norm_num) ha2 _
    have h3 : ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2) :=
      pow_le_pow_right₀ ha1 (by
        have : (n - 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
        omega)
    push_cast at h1
    linarith
  have h3 : ClaimAt X (n - 3) (((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2 + cAdd n)) (smin n D h) :=
    claim_step_Rplus n hn D h X hX (n - 3) (by omega) (by omega) _
      (by rw [show n - 3 + 1 = n - 2 by omega]; exact htop)
  have h4 : ClaimAt X (n - 4) (((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2 + cAdd n + cAdd n)) (smin n D h) :=
    claim_step_Rplus n hn D h X hX (n - 4) le_rfl (by omega) _
      (by rw [show n - 4 + 1 = n - 3 by omega]; exact h3)
  rcases (show j = n - 3 ∨ j = n - 4 by omega) with rfl | rfl
  · exact h3.mono_Γ hs0 (pow_le_pow_right₀ ha1 (by omega))
  · exact h4.mono_Γ hs0 (pow_le_pow_right₀ ha1 (by omega))

/-- **Theorem R⁺** (manuscript Theorem 7.1): Claim(j) for `j = n-2, n-3, n-4`, combining the
proved base level with `theorem_Rplus_low_proved`. -/
theorem theorem_Rplus_proved (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ∀ j, n - 4 ≤ j → j ≤ n - 2 → ClaimAt X j (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
  obtain ⟨c₀, hlow⟩ := theorem_Rplus_low_proved n hn
  refine ⟨c₀ + 4 * n ^ 2, fun d D h X hX hD j hj1 hj2 => ?_⟩
  have ha1 : (1 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ D + 2 by omega)
  have ha2 : (2 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ D + 2 by omega)
  have hs0 : 0 ≤ smin n D h := le_trans zero_le_one (one_le_smin n D h)
  rcases Nat.lt_or_ge j (n - 2) with hlt | hge
  · exact (hlow d D h X hX hD j hj1 (by omega)).mono_Γ hs0
      (pow_le_pow_right₀ ha1 (by omega))
  · have hj : j = n - 2 := by omega
    subst hj
    refine (claim_top n hn d D h X hX).mono_Γ hs0 ?_
    have h1 : ((4 * (n - 2) ^ 2 : ℕ) : ℝ) < 2 ^ (4 * (n - 2) ^ 2) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) :=
      pow_le_pow_left₀ (by norm_num) ha2 _
    have h3 : ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (c₀ + 4 * n ^ 2) :=
      pow_le_pow_right₀ ha1 (by
        have : (n - 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
        omega)
    push_cast at h1
    linarith

end E1088
