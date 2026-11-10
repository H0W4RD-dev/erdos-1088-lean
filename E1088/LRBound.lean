import E1088.LRMain

/-!
# Theorem LR: the size of the loss

`LRcost k r ≤ 2^{C_k √(r+2) log₂(r+2)}`: for every fixed number `k` of types, the loss in
Theorem LR is `2^{O_k(√r log r)}`, which is the shape used in the rest of the proof.
(The paper claims `C_k = O(k³)`; our tournament version of NF3 gives `C_k = 2^{O(k)}`, see
E1088/NF.lean. Only fixed `k` is ever used.)
-/

open Finset Real

namespace E1088

/-- `L(r) = √(r+2) log₂(r+2)`. -/
noncomputable def Lr (r : ℕ) : ℝ := Real.sqrt (r + 2) * Real.logb 2 (r + 2)

theorem one_le_logb (r : ℕ) : 1 ≤ Real.logb 2 ((r : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
  have := Nat.cast_nonneg (α := ℝ) r; linarith

theorem one_le_sqrt (r : ℕ) : 1 ≤ Real.sqrt ((r : ℝ) + 2) := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_le_sqrt; have := Nat.cast_nonneg (α := ℝ) r; linarith

theorem one_le_Lr (r : ℕ) : 1 ≤ Lr r := by
  unfold Lr; have := one_le_logb r; have := one_le_sqrt r; nlinarith

theorem logb_le_Lr (r : ℕ) : Real.logb 2 ((r : ℝ) + 2) ≤ Lr r := by
  unfold Lr; have := one_le_logb r; have := one_le_sqrt r; nlinarith

theorem two_rpow_le {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ 2 ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- Bound on one round. -/
theorem roundCost_le (k r : ℕ) :
    roundCost k r ≤ (2 : ℝ) ^ ((4 * k * k + 3 * k + 8 + 2 * Real.pi * margK k * (9 + 2 * k)) *
      Lr r) := by
  have hL := one_le_Lr r
  have hlog := one_le_logb r
  have hsq := one_le_sqrt r
  set R' : ℕ := (r + 1) ^ k with hR'
  set δ : ℝ := 1 / (16 * (R' : ℝ)) with hδ
  set T := roundsT (margK k) δ (r + 2) with hT
  have hR'pos : (0 : ℝ) < R' := by exact_mod_cast pow_pos (Nat.succ_pos r) k
  have hmK : 0 ≤ margK k := by unfold margK; positivity
  -- the constant part
  have hA : (16 : ℝ) ^ (k * k) * 4 ^ k * 64 = 2 ^ ((4 * k * k + 2 * k + 6 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num,
      show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1; ring
  -- the rank part
  have hB : (R' : ℝ) ≤ 2 ^ (k * Real.logb 2 ((r : ℝ) + 2)) := by
    rw [hR']; push_cast
    rw [mul_comm (k : ℝ), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by positivity), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  -- the Gaussian part
  have hlogδ : Real.log (2 / δ ^ 2) ≤ (9 + 2 * k) * Real.logb 2 ((r : ℝ) + 2) := by
    have e : 2 / δ ^ 2 = 512 * (R' : ℝ) ^ 2 := by rw [hδ]; field_simp; ring
    rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h512 : Real.log 512 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 512 by norm_num)
      have h2 : Real.log 512 = 9 * Real.log 2 := by
        rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    have hR'log : Real.log R' ≤ k * Real.logb 2 ((r : ℝ) + 2) := by
      have := Real.log_le_log hR'pos hB
      rw [Real.log_rpow (by norm_num)] at this
      have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      have h0 : 0 ≤ (k : ℝ) * Real.logb 2 ((r : ℝ) + 2) := by positivity
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
    push_cast
    nlinarith
  have hTle : (T : ℝ) ≤ Real.pi * margK k * (9 + 2 * k) * Lr r + 1 := by
    have h1 : (T : ℝ) < Real.pi * margK k * Real.sqrt ((r + 2 : ℕ) : ℝ) *
        Real.log (2 / δ ^ 2) + 1 := Nat.ceil_lt_add_one (by
          apply mul_nonneg (by positivity)
          apply Real.log_nonneg
          rw [hδ]; rw [show 2 / (1 / (16 * (R' : ℝ))) ^ 2 = 512 * (R' : ℝ) ^ 2 by field_simp; ring]
          have : (1 : ℝ) ≤ R' := by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos r)
          nlinarith)
    have h2 : Real.sqrt ((r + 2 : ℕ) : ℝ) = Real.sqrt ((r : ℝ) + 2) := by push_cast; rfl
    rw [h2] at h1
    have h3 : Real.pi * margK k * Real.sqrt ((r : ℝ) + 2) * Real.log (2 / δ ^ 2) ≤
        Real.pi * margK k * (9 + 2 * k) * Lr r := by
      unfold Lr
      have := mul_le_mul_of_nonneg_left hlogδ
        (show 0 ≤ Real.pi * margK k * Real.sqrt ((r : ℝ) + 2) by positivity)
      nlinarith
    linarith
  have hC : (4 : ℝ) ^ T ≤ 2 ^ ((2 * Real.pi * margK k * (9 + 2 * k) + 2) * Lr r) := by
    rw [show (4 : ℝ) ^ T = 2 ^ ((2 * T : ℕ) : ℝ) by
      rw [Real.rpow_natCast, pow_mul]; norm_num]
    apply two_rpow_le
    push_cast
    nlinarith
  -- assemble
  unfold roundCost
  rw [← hR', ← hδ, ← hT]
  have e1 : (16 : ℝ) ^ (k * k) * 4 ^ k * (64 * (R' : ℝ) * 4 ^ T) =
      ((16 : ℝ) ^ (k * k) * 4 ^ k * 64) * (R' : ℝ) * 4 ^ T := by ring
  rw [e1, hA]
  have hA' : (2 : ℝ) ^ ((4 * k * k + 2 * k + 6 : ℕ) : ℝ) ≤
      2 ^ ((4 * k * k + 2 * k + 6 : ℝ) * Lr r) := by
    apply two_rpow_le; push_cast
    have : (0 : ℝ) ≤ 4 * k * k + 2 * k + 6 := by positivity
    nlinarith
  have hB' : (R' : ℝ) ≤ 2 ^ (k * Lr r) :=
    hB.trans (two_rpow_le (mul_le_mul_of_nonneg_left (logb_le_Lr r) (by positivity)))
  calc 2 ^ ((4 * k * k + 2 * k + 6 : ℕ) : ℝ) * (R' : ℝ) * 4 ^ T
      ≤ 2 ^ ((4 * k * k + 2 * k + 6 : ℝ) * Lr r) * 2 ^ (k * Lr r) *
          2 ^ ((2 * Real.pi * margK k * (9 + 2 * k) + 2) * Lr r) := by
        gcongr
    _ = 2 ^ ((4 * k * k + 2 * k + 6 : ℝ) * Lr r + k * Lr r +
          (2 * Real.pi * margK k * (9 + 2 * k) + 2) * Lr r) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
    _ = _ := by congr 1; ring

/-- **Size of the loss in Theorem LR**: `LRcost k r ≤ 2^{C_k √(r+2) log₂(r+2)}`. -/
theorem LRcost_le (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, LRcost k r ≤ (2 : ℝ) ^ (C * Lr r) := by
  induction k with
  | zero => exact ⟨0, le_rfl, fun r => by simp [LRcost]⟩
  | succ k ih =>
    obtain ⟨C, hC, h⟩ := ih
    set c := (4 * (k + 1 : ℕ) * (k + 1 : ℕ) + 3 * (k + 1 : ℕ) + 8 +
      2 * Real.pi * margK (k + 1) * (9 + 2 * (k + 1 : ℕ)) : ℝ) with hc
    have hc0 : 0 ≤ c := by
      have : 0 ≤ margK (k + 1) := by unfold margK; positivity
      rw [hc]; positivity
    refine ⟨c + C, by linarith, fun r => ?_⟩
    simp only [LRcost]
    have h1 := roundCost_le (k + 1) r
    have h2 := h r
    have h0 : 0 ≤ LRcost k r := le_trans zero_le_one (one_le_LRcost k r)
    calc roundCost (k + 1) r * LRcost k r ≤ 2 ^ (c * Lr r) * 2 ^ (C * Lr r) :=
          mul_le_mul h1 h2 h0 (by positivity)
      _ = 2 ^ ((c + C) * Lr r) := by rw [← Real.rpow_add (by norm_num)]; ring_nf

end E1088
