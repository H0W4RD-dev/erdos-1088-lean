import E1088.Statement.Erdos1088
import E1088.Asymp

/-!
# From the halving step to `Erdos1088.erdos_1088`

* `HalvingStep n`: Theorem 1.6 of round14 / manuscript Theorem 10.3, i.e.
  `s'_n(D) ≤ 2^{C_n √D log₂(D+2)} (s'_n(⌊D/2⌋) + 1)`, phrased without the function `s'`;
  proved in E1088/Assembly.lean from the paper's named results.
* `card_le_of_rainbowFree` : the halving recursion solved (round11/n4_full_proof Sec. 9). PROVED.
* `erdos_1088_of_halving`  : the asymptotic conclusion from `HalvingStep`. PROVED.
-/

open Filter Asymptotics
open scoped EuclideanGeometry

namespace E1088

/-- `X` contains no `n` points with pairwise distinct distances ("rainbow-`n`-free"). -/
def RainbowFree (n : ℕ) {d : ℕ} (X : Finset (ℝ^d)) : Prop :=
  ¬ Erdos1088.HasSubsetWithDistinctDistances n X

/-- Affine dimension of a finite point set. -/
noncomputable def affDim {d : ℕ} (X : Finset (ℝ^d)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (X : Set (ℝ^d)))

/-- Exponent of the loss per halving: `C √D log₂(D+2)`. -/
noncomputable def halvingExp (C : ℝ) (D : ℕ) : ℝ := C * (Real.sqrt D * Real.logb 2 (D + 2))

/-- **Halving step** (round14 Theorem 1.6 / manuscript Theorem 10.3, with round11 Sec. 9
conventions), as a property of `n`. For fixed `n ≥ 3` there is `C > 0` such that every
rainbow-`n`-free set of affine dimension `≤ D` has at most `2^{C √D log₂(D+2)} (B + 1)` points,
provided every rainbow-`n`-free set of affine dimension `≤ ⌊D/2⌋` has at most `B` points.
It is proved in E1088/Assembly.lean (`halving_step`) from the paper's named results. -/
def HalvingStep (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d D B : ℕ) (X : Finset (ℝ^d)), RainbowFree n X → affDim X ≤ D →
    (∀ Y : Finset (ℝ^d), RainbowFree n Y → affDim Y ≤ D / 2 → Y.card ≤ B) →
    (X.card : ℝ) ≤ (2 : ℝ) ^ halvingExp C D * (B + 1)

/-- Exponent of the solved recursion: `4 (C+1) √D log₂(D+2) + 1`. -/
noncomputable def solvedExp (C : ℝ) (D : ℕ) : ℝ := 4 * (C + 1) * (Real.sqrt D * Real.logb 2 (D + 2)) + 1

theorem card_le_one_of_affDim_zero {d : ℕ} (X : Finset (ℝ^d)) (h : affDim X = 0) :
    X.card ≤ 1 := by
  unfold affDim at h
  rw [Submodule.finrank_eq_zero, vectorSpan_eq_bot_iff_subsingleton] at h
  exact Finset.card_le_one.2 fun a ha b hb => h ha hb

theorem sqrt_mul_logb_ge_one (D : ℕ) (hD : 1 ≤ D) : 1 ≤ Real.sqrt D * Real.logb 2 (D + 2) := by
  have h1 : (1 : ℝ) ≤ Real.sqrt D := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hD)
  have h2 : (1 : ℝ) ≤ Real.logb 2 (D + 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    rw [Real.rpow_one]; linarith
  nlinarith

theorem sqrt_half_le (D : ℕ) : Real.sqrt ((D / 2 : ℕ) : ℝ) ≤ 3 / 4 * Real.sqrt D := by
  rw [show (3 / 4 : ℝ) = Real.sqrt (9 / 16) by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have : ((D / 2 : ℕ) : ℝ) ≤ (D : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self D 2
  have h0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  linarith

theorem logb_half_le (D : ℕ) : Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) ≤ Real.logb 2 (D + 2) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  have : ((D / 2 : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.div_le_self D 2
  linarith

/-- **The halving recursion solved.** Every rainbow-`n`-free set of affine dimension `≤ D` has
`|X| + 1 ≤ 2^{4(C+1)√D log₂(D+2) + 1}` points. -/
theorem card_le_of_rainbowFree (n : ℕ) (C : ℝ) (hC : 0 < C)
    (hstep : ∀ (d D B : ℕ) (X : Finset (ℝ^d)), RainbowFree n X → affDim X ≤ D →
      (∀ Y : Finset (ℝ^d), RainbowFree n Y → affDim Y ≤ D / 2 → Y.card ≤ B) →
      (X.card : ℝ) ≤ (2 : ℝ) ^ halvingExp C D * (B + 1)) (d : ℕ) :
    ∀ D : ℕ, ∀ X : Finset (ℝ^d), RainbowFree n X → affDim X ≤ D →
      (X.card : ℝ) + 1 ≤ (2 : ℝ) ^ solvedExp C D := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro X hX hdim
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have := card_le_one_of_affDim_zero X (by omega)
      have : (X.card : ℝ) ≤ 1 := by exact_mod_cast this
      simp [solvedExp]; linarith
    set E2 := solvedExp C (D / 2) with hE2
    have hE2nn : 0 ≤ E2 := by
      simp only [hE2, solvedExp]
      have : 0 ≤ Real.sqrt ((D / 2 : ℕ) : ℝ) * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.logb_nonneg (by norm_num) (by
          have : (0 : ℝ) ≤ ((D / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith))
      nlinarith
    have h2E : (1 : ℝ) ≤ 2 ^ E2 := Real.one_le_rpow (by norm_num) hE2nn
    set B := ⌊(2 : ℝ) ^ E2 - 1⌋₊ with hB
    have hYB : ∀ Y : Finset (ℝ^d), RainbowFree n Y → affDim Y ≤ D / 2 → Y.card ≤ B := by
      intro Y hY hYd
      have := ih (D / 2) (Nat.div_lt_self hD (by norm_num)) Y hY hYd
      exact Nat.le_floor (by linarith)
    have hBle : (B : ℝ) ≤ 2 ^ E2 - 1 := Nat.floor_le (by linarith)
    have hX' := hstep d D B X hX hdim hYB
    have hhE : halvingExp C D + E2 + 1 ≤ solvedExp C D := by
      simp only [halvingExp, hE2, solvedExp]
      have a1 := sqrt_half_le D
      have a2 := logb_half_le D
      have a3 := sqrt_mul_logb_ge_one D hD
      have a4 : 0 ≤ Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) := Real.logb_nonneg (by norm_num) (by
          have : (0 : ℝ) ≤ ((D / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith)
      have a5 : Real.sqrt ((D / 2 : ℕ) : ℝ) * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) ≤
          3 / 4 * (Real.sqrt D * Real.logb 2 (D + 2)) := by
        calc Real.sqrt ((D / 2 : ℕ) : ℝ) * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2)
            ≤ 3 / 4 * Real.sqrt D * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) :=
              mul_le_mul_of_nonneg_right a1 a4
          _ ≤ 3 / 4 * Real.sqrt D * Real.logb 2 (D + 2) :=
              mul_le_mul_of_nonneg_left a2 (by positivity)
          _ = _ := by ring
      nlinarith
    have hpow : (2 : ℝ) ^ halvingExp C D * 2 ^ E2 * 2 ≤ 2 ^ solvedExp C D := by
      have e : (2 : ℝ) ^ (halvingExp C D + E2 + 1) = 2 ^ halvingExp C D * 2 ^ E2 * 2 := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]
      rw [← e]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hhE
    have h1 : (1 : ℝ) ≤ 2 ^ halvingExp C D := Real.one_le_rpow (by norm_num) (by
      simp only [halvingExp]
      exact mul_nonneg hC.le (mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith))))
    have : (X.card : ℝ) ≤ 2 ^ halvingExp C D * 2 ^ E2 := by
      calc (X.card : ℝ) ≤ 2 ^ halvingExp C D * (B + 1) := hX'
        _ ≤ 2 ^ halvingExp C D * 2 ^ E2 := by gcongr; linarith
    nlinarith

theorem affDim_le {d : ℕ} (X : Finset (ℝ^d)) : affDim X ≤ d := by
  unfold affDim
  exact (Submodule.finrank_le _).trans (by simp)

/-- **Erdős #1088 from the halving step.** -/
theorem erdos_1088_of_halving (hH : ∀ n ≥ 3, HalvingStep n) :
    ∀ n ≥ 3,
      (fun d : ℕ ↦ Real.logb 2 (Erdos1088.f d n : ℝ)) =o[atTop] (fun d : ℕ ↦ (d : ℝ)) := by
  intro n hn
  obtain ⟨C, hC, hstep⟩ := hH n hn
  have hcard := card_le_of_rainbowFree n C hC hstep
  -- `f d n ≤ n * 2^{E(d)}`
  have hf : ∀ d : ℕ, (Erdos1088.f d n : ℝ) ≤ n * 2 ^ solvedExp C d := by
    intro d
    set m := max n ⌊(2 : ℝ) ^ solvedExp C d⌋₊ with hm
    have hmem : m ∈ Erdos1088.cardSet d n := by
      refine ⟨le_max_left _ _, fun S hS => ?_⟩
      by_contra hcon
      have h1 := hcard d d S hcon (affDim_le S)
      have h2 : S.card + 1 ≤ ⌊(2 : ℝ) ^ solvedExp C d⌋₊ := Nat.le_floor (by exact_mod_cast h1)
      have h3 : ⌊(2 : ℝ) ^ solvedExp C d⌋₊ ≤ m := le_max_right _ _
      omega
    have hle : Erdos1088.f d n ≤ m := Nat.sInf_le hmem
    have hE : (1 : ℝ) ≤ 2 ^ solvedExp C d := Real.one_le_rpow (by norm_num) (by
      simp only [solvedExp]
      have : 0 ≤ Real.sqrt d * Real.logb 2 (d + 2) := mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      nlinarith)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hm' : (m : ℝ) ≤ n * 2 ^ solvedExp C d := by
      rcases le_total n ⌊(2 : ℝ) ^ solvedExp C d⌋₊ with h | h
      · rw [hm, max_eq_right h]
        have := Nat.floor_le (show (0 : ℝ) ≤ 2 ^ solvedExp C d by positivity)
        nlinarith
      · rw [hm, max_eq_left h]; nlinarith
    calc (Erdos1088.f d n : ℝ) ≤ m := by exact_mod_cast hle
      _ ≤ _ := hm'
  have hlog : ∀ d : ℕ, ‖Real.logb 2 (Erdos1088.f d n : ℝ)‖ ≤
      Real.logb 2 n + (1 + 4 * (C + 1) * (Real.sqrt d * Real.logb 2 (d + 2))) := by
    intro d
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    rcases Nat.eq_zero_or_pos (Erdos1088.f d n) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero, norm_zero]
      have : 0 ≤ Real.sqrt d * Real.logb 2 (d + 2) := mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      have : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
      nlinarith
    · have hf1 : (1 : ℝ) ≤ Erdos1088.f d n := by exact_mod_cast hpos
      have hnn : 0 ≤ Real.logb 2 (Erdos1088.f d n : ℝ) := Real.logb_nonneg (by norm_num) hf1
      rw [Real.norm_of_nonneg hnn]
      calc Real.logb 2 (Erdos1088.f d n : ℝ) ≤ Real.logb 2 (n * 2 ^ solvedExp C d) :=
            Real.logb_le_logb_of_le (by norm_num) (by linarith) (hf d)
        _ = Real.logb 2 n + solvedExp C d := by
            rw [Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num)
              (by norm_num)]
        _ = _ := by simp only [solvedExp]; ring
  refine IsBigO.trans_isLittleO (g := fun d : ℕ =>
    Real.logb 2 n + (1 + 4 * (C + 1) * (Real.sqrt d * Real.logb 2 (d + 2)))) ?_ ?_
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun d => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have : 0 ≤ Real.logb 2 n + (1 + 4 * (C + 1) * (Real.sqrt d * Real.logb 2 (d + 2))) := by
      have : 0 ≤ Real.sqrt d * Real.logb 2 (d + 2) := mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      have : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
      nlinarith
    rw [one_mul, Real.norm_of_nonneg this]
    exact hlog d
  · have := bound_isLittleO (Real.logb 2 n + 1) (4 * (C + 1))
    refine this.congr' (Eventually.of_forall fun d => ?_) EventuallyEq.rfl
    ring

end E1088
