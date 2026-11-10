import Mathlib

/-!
# Asymptotics: `√x · log(x+2) = o(x)`
-/

open Filter Asymptotics Real

namespace E1088

theorem sqrt_log_isLittleO :
    (fun x : ℝ => Real.sqrt x * Real.log (x + 2)) =o[atTop] (fun x => x) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h2 : (fun x : ℝ => Real.log (x + 2)) =o[atTop] (fun x => (x + 2) ^ (1 / 2 : ℝ)) :=
    h1.comp_tendsto (tendsto_atTop_add_const_right _ 2 tendsto_id)
  have h3 : (fun x : ℝ => (x + 2) ^ (1 / 2 : ℝ)) =O[atTop] (fun x => Real.sqrt x) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have : Real.sqrt (x + 2) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    exact this
  have h4 := h2.trans_isBigO h3
  have h5 : (fun x : ℝ => Real.sqrt x * Real.log (x + 2)) =o[atTop]
      (fun x => Real.sqrt x * Real.sqrt x) := (isBigO_refl _ _).mul_isLittleO h4
  refine h5.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Real.mul_self_sqrt hx

/-- `c₀ + c₁ √d log₂(d+2) = o(d)` along the naturals. -/
theorem bound_isLittleO (c₀ c₁ : ℝ) :
    (fun d : ℕ => c₀ + c₁ * (Real.sqrt d * Real.logb 2 (d + 2))) =o[atTop]
      (fun d : ℕ => (d : ℝ)) := by
  have hA : (fun d : ℕ => c₀) =o[atTop] (fun d : ℕ => (d : ℝ)) :=
    (isLittleO_const_id_atTop c₀).natCast_atTop
  have hB : (fun d : ℕ => Real.sqrt d * Real.log ((d : ℝ) + 2)) =o[atTop]
      (fun d : ℕ => (d : ℝ)) := sqrt_log_isLittleO.natCast_atTop
  have hB' : (fun d : ℕ => c₁ * (Real.sqrt d * Real.logb 2 (d + 2))) =o[atTop]
      (fun d : ℕ => (d : ℝ)) := by
    have := hB.const_mul_left (c₁ / Real.log 2)
    refine this.congr' (Eventually.of_forall fun d => ?_) EventuallyEq.rfl
    simp only [Real.logb]
    ring
  exact hA.add hB'

end E1088
