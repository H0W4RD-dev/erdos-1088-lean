import Mathlib

/-!
# Sheppard's formula for the standard Gaussian measure

For unit vectors `u, v` of a finite-dimensional real inner product space and `g ~ stdGaussian`,
`P[⟨g,u⟩ ≥ 0 ∧ ⟨g,v⟩ ≥ 0] = 1/2 - arccos⟨u,v⟩/(2π)`.

Proof: extend `{u, w}` (`w ⟂ u` a unit vector in the plane of `u, v`) to an orthonormal basis;
in that basis `stdGaussian` is a product of standard real Gaussians, so `(⟨g,u⟩, ⟨g,w⟩)` is a
standard Gaussian on `ℝ × ℝ`. The event is a sector of angle `π - arccos⟨u,v⟩`; its Gaussian
measure is computed in polar coordinates (`lintegral_comp_polarCoord_symm`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace E1088

/-- `∫_0^∞ r e^{-r²/2} dr = 1`. -/
theorem integral_mul_exp_half :
    ∫ r in Ioi (0 : ℝ), r * Real.exp (-(1 / 2) * r ^ 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have e : (fun r : ℝ => (r : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (r : ℂ) ^ 2)) =
      fun r : ℝ => ((r * Real.exp (-(1 / 2) * r ^ 2) : ℝ) : ℂ) := by
    funext r
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [e, integral_complex_ofReal] at h
  have h2 : (2 * (1 / 2 : ℂ))⁻¹ = ((1 : ℝ) : ℂ) := by norm_num
  rw [h2] at h
  exact_mod_cast h

/-- The arc `{θ ∈ (-π, π) : cos θ ≥ 0, cos (θ - φ) ≥ 0}` has length `π - φ` for `φ ∈ [0, π]`. -/
theorem volume_arc (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
    volume ({θ : ℝ | 0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - φ)} ∩ Ioo (-π) π) =
      ENNReal.ofReal (π - φ) := by
  have hpi := Real.pi_pos
  set A := {θ : ℝ | 0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - φ)} ∩ Ioo (-π) π with hA
  have h1 : Icc (φ - π / 2) (π / 2) ⊆ A := by
    rintro θ ⟨ha, hb⟩
    refine ⟨⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, hb⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩, by linarith, by linarith⟩
  have h2 : A ⊆ Icc (φ - π / 2) (π / 2) ∪ {-(π / 2)} := by
    rintro θ ⟨⟨hc1, hc2⟩, hlo, hhi⟩
    have hθ1 : θ ≤ π / 2 := by
      by_contra h
      push Not at h
      exact absurd hc1 (not_le.2 (Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith)))
    have hθ2 : -(π / 2) ≤ θ := by
      by_contra h
      push Not at h
      have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := -θ) (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      exact absurd hc1 (not_le.2 this)
    by_cases h3 : φ - π / 2 ≤ θ
    · exact Or.inl ⟨h3, hθ1⟩
    · push Not at h3
      by_cases h4 : θ - φ = -(3 * π / 2)
      · right
        rw [mem_singleton_iff]
        linarith
      · exfalso
        have h5 : -(3 * π / 2) < θ - φ := lt_of_le_of_ne (by linarith) (Ne.symm h4)
        have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := θ - φ + 2 * π) (by linarith)
          (by linarith)
        rw [Real.cos_add_two_pi] at this
        exact absurd hc2 (not_le.2 this)
  apply le_antisymm
  · calc volume A ≤ volume (Icc (φ - π / 2) (π / 2) ∪ {-(π / 2)}) := measure_mono h2
      _ ≤ volume (Icc (φ - π / 2) (π / 2)) + volume ({-(π / 2)} : Set ℝ) := measure_union_le _ _
      _ = ENNReal.ofReal (π - φ) := by
          rw [Real.volume_singleton, add_zero, Real.volume_Icc]; congr 1; ring
  · calc ENNReal.ofReal (π - φ) = volume (Icc (φ - π / 2) (π / 2)) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ volume A := measure_mono h1

/-- The standard Gaussian measure on `ℝ × ℝ`. -/
noncomputable abbrev gauss2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

theorem gauss_pdf_prod (r θ : ℝ) :
    gaussianPDFReal 0 1 (r * Real.cos θ) * gaussianPDFReal 0 1 (r * Real.sin θ) =
      Real.exp (-(1 / 2) * r ^ 2) / (2 * π) := by
  have hpi := Real.pi_pos
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have h2 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have h3 : Real.exp (-(r * Real.cos θ) ^ 2 / 2) * Real.exp (-(r * Real.sin θ) ^ 2 / 2) =
      Real.exp (-(1 / 2) * r ^ 2) := by
    rw [← Real.exp_add]; congr 1
    have := Real.cos_sq_add_sin_sq θ
    nlinarith [this]
  calc (√(2 * π))⁻¹ * Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
        ((√(2 * π))⁻¹ * Real.exp (-(r * Real.sin θ) ^ 2 / 2))
      = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          Real.exp (-(r * Real.sin θ) ^ 2 / 2)) := by ring
    _ = _ := by rw [h2, h3]; field_simp

/-- **Sector probability.** For `a ∈ [-1,1]`, the standard Gaussian measure of the sector
`{x ≥ 0, a x + √(1-a²) y ≥ 0}` is `1/2 - arccos a / (2π)`. -/
theorem gauss2_sector (a : ℝ) (ha1 : -1 ≤ a) (ha2 : a ≤ 1) :
    gauss2 {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ a * p.1 + √(1 - a ^ 2) * p.2} =
      ENNReal.ofReal (1 / 2 - Real.arccos a / (2 * π)) := by
  have hpi := Real.pi_pos
  set φ := Real.arccos a with hφ
  have hc : Real.cos φ = a := Real.cos_arccos ha1 ha2
  have hs : Real.sin φ = √(1 - a ^ 2) := Real.sin_arccos a
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg a
  have hφπ : φ ≤ π := Real.arccos_le_pi a
  rw [← hs, ← hc]
  set S := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ Real.cos φ * p.1 + Real.sin φ * p.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ)) measurable_const measurable_fst).inter
      (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ))
        (g := fun p : ℝ × ℝ => Real.cos φ * p.1 + Real.sin φ * p.2) measurable_const
        (by fun_prop))
  set f : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2 with hf
  have hν : gauss2 = volume.withDensity f := by
    simp only [gauss2]
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
      ← Measure.volume_eq_prod]
  rw [hν, withDensity_apply _ hSm, ← lintegral_indicator hSm, ← lintegral_comp_polarCoord_symm]
  set A := {θ : ℝ | 0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - φ)} with hA
  set F : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r * Real.exp (-(1 / 2) * r ^ 2) / (2 * π))
    with hF
  have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • S.indicator f (polarCoord.symm p) =
      F p.1 * A.indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : 0 < r := hr
    simp only [polarCoord_symm_apply]
    have hiff : (r * Real.cos θ, r * Real.sin θ) ∈ S ↔ θ ∈ A := by
      simp only [hS, hA, mem_ofPred_eq, Real.cos_sub]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨nonneg_of_mul_nonneg_right (by linarith [h1]) hr0, ?_⟩
        have : 0 ≤ r * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) := by nlinarith
        exact nonneg_of_mul_nonneg_right (by linarith) hr0
      · rintro ⟨h1, h2⟩
        exact ⟨mul_nonneg hr0.le h1, by nlinarith⟩
    by_cases hθA : θ ∈ A
    · rw [indicator_of_mem (hiff.2 hθA), indicator_of_mem hθA]
      simp only [hf, gaussianPDF, Pi.one_apply, mul_one, smul_eq_mul, hF]
      rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        ← ENNReal.ofReal_mul hr0.le, gauss_pdf_prod]
      congr 1; ring
    · rw [indicator_of_notMem (fun h => hθA (hiff.1 h)), indicator_of_notMem hθA]
      simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hAm : MeasurableSet A :=
    (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) measurable_const
      Real.continuous_cos.measurable).inter
      (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) (g := fun θ => Real.cos (θ - φ))
        measurable_const (by fun_prop))
  rw [lintegral_prod_mul (by fun_prop) ((measurable_one.indicator hAm).aemeasurable)]
  -- radial part
  have hrad : ∫⁻ r in Ioi (0 : ℝ), F r = ENNReal.ofReal (1 / (2 * π)) := by
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_div, integral_mul_exp_half]
    · exact ((integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn).div_const _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have : (0 : ℝ) < r := hr
      positivity
  -- angular part
  have hang : ∫⁻ θ in Ioo (-π) π, A.indicator 1 θ = ENNReal.ofReal (π - φ) := by
    rw [lintegral_indicator_one hAm, Measure.restrict_apply hAm]
    exact volume_arc φ hφ0 hφπ
  rw [hrad, hang, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- Two coordinates of a product of probability measures. -/
theorem pi_map_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (i j : ι) (hij : i ≠ j) :
    (Measure.pi μ).map (fun x => (x i, x j)) = (μ i).prod (μ j) := by
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply (by fun_prop) (hs.prod ht)]
  have hset : (fun x : ι → ℝ => (x i, x j)) ⁻¹' (s ×ˢ t) =
      Set.pi univ (fun k => if k = i then s else if k = j then t else univ) := by
    ext x
    simp only [mem_preimage, mem_prod, Set.mem_pi, mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hki : k = i
      · subst hki; simpa using h1
      · by_cases hkj : k = j
        · subst hkj; simpa [hki] using h2
        · simp [hki, hkj]
    · intro h
      exact ⟨by simpa using h i, by simpa [Ne.symm hij] using h j⟩
  rw [hset, Measure.pi_pi,
    Fintype.prod_eq_mul i j hij (fun k hk => by simp [hk.1, hk.2])]
  simp [Ne.symm hij]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem inner_sum_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E)
    (x : ι → ℝ) (j : ι) : inner ℝ (∑ i, x i • b i) (b j) = x j := by
  simp [sum_inner, real_inner_smul_left, orthonormal_iff_ite.1 b.orthonormal]

/-- `(⟨g,u⟩, ⟨g,w⟩)` is a standard Gaussian on `ℝ × ℝ` for orthonormal `u, w`. -/
theorem stdGaussian_map_pair (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0) :
    (stdGaussian E).map (fun g => (inner ℝ g u, inner ℝ g w)) = gauss2 := by
  classical
  have huw' : u ≠ w := by
    rintro rfl; rw [real_inner_self_eq_norm_sq, hu] at huw; norm_num at huw
  have hon : Orthonormal ℝ (Subtype.val : ({u, w} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp [real_inner_self_eq_norm_sq, hu]
    · simp [huw, huw']
    · rw [real_inner_comm]; simp [huw, Ne.symm huw']
    · simp [real_inner_self_eq_norm_sq, hw]
  obtain ⟨U, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  have hu' : u ∈ U := hsub (by simp)
  have hw' : w ∈ U := hsub (by simp)
  have hbu : b ⟨u, hu'⟩ = u := by rw [hb]
  have hbw : b ⟨w, hw'⟩ = w := by rw [hb]
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_map (by fun_prop) (by fun_prop)]
  have : (fun g => (inner ℝ g u, inner ℝ g w)) ∘ (fun x : U → ℝ => ∑ i, x i • b i) =
      fun x => (x ⟨u, hu'⟩, x ⟨w, hw'⟩) := by
    funext x
    simp only [Function.comp]
    conv_lhs => rw [← hbu, ← hbw]
    rw [inner_sum_basis, inner_sum_basis]
  rw [this, pi_map_pair _ _ _ (fun h => huw' (congrArg Subtype.val h))]

/-- `⟨g,u⟩` is a standard real Gaussian for a unit vector `u`. -/
theorem stdGaussian_map_one (u : E) (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g => inner ℝ g u) = gaussianReal 0 1 := by
  classical
  have hon : Orthonormal ℝ (Subtype.val : ({u} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    simp [real_inner_self_eq_norm_sq, hu]
  obtain ⟨U, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  have hu' : u ∈ U := hsub (by simp)
  have hbu : b ⟨u, hu'⟩ = u := by rw [hb]
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_map (by fun_prop) (by fun_prop)]
  have : (fun g => inner ℝ g u) ∘ (fun x : U → ℝ => ∑ i, x i • b i) = fun x => x ⟨u, hu'⟩ := by
    funext x
    simp only [Function.comp]
    conv_lhs => rw [← hbu]
    rw [inner_sum_basis]
  rw [this]
  exact (measurePreserving_eval (fun _ : U => gaussianReal 0 1) ⟨u, hu'⟩).map_eq

/-- **Sheppard's formula** for `stdGaussian` on a finite-dimensional inner product space. -/
theorem sheppard_general (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian E).real {g | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} =
      1 / 2 - Real.arccos (inner ℝ u v) / (2 * π) := by
  have hpi := Real.pi_pos
  set a := inner ℝ u v with ha
  have hab : |a| ≤ 1 := by
    have := abs_real_inner_le_norm u v; rw [hu, hv, one_mul] at this; exact this
  have ha1 : -1 ≤ a := (abs_le.1 hab).1
  have ha2 : a ≤ 1 := (abs_le.1 hab).2
  set c := √(1 - a ^ 2) with hc
  set S := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ a * p.1 + c * p.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ)) measurable_const measurable_fst).inter
      (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ))
        (g := fun p : ℝ × ℝ => a * p.1 + c * p.2) measurable_const (by fun_prop))
  -- `‖v - a u‖² = 1 - a²`
  have hnorm : ‖v - a • u‖ ^ 2 = 1 - a ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, real_inner_comm, hu, hv]
    rw [Real.norm_eq_abs, mul_one, sq_abs, ← ha]; ring
  have key : stdGaussian E {g | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} = gauss2 S := by
    by_cases hlt : a ^ 2 < 1
    · have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith)
      set w := c⁻¹ • (v - a • u) with hw
      have hvau : ‖v - a • u‖ = c := by
        rw [hc, ← hnorm, Real.sqrt_sq (norm_nonneg _)]
      have hw1 : ‖w‖ = 1 := by
        rw [hw, norm_smul, hvau, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos,
          inv_mul_cancel₀ hcpos.ne']
      have huw : inner ℝ u w = 0 := by
        rw [hw, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hu, ← ha]; ring
      have hv' : v = a • u + c • w := by
        rw [hw, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]; abel
      have hset : {g : E | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} =
          (fun g => (inner ℝ g u, inner ℝ g w)) ⁻¹' S := by
        ext g
        simp only [mem_setOf_eq, mem_preimage, hS]
        rw [hv', inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [hset, ← Measure.map_apply (by fun_prop) hSm, stdGaussian_map_pair u w hu hw1 huw]
    · have ha2' : a ^ 2 = 1 := by nlinarith [sq_abs a, abs_nonneg a]
      have hc0 : c = 0 := by rw [hc, ha2']; simp
      have hvau : v = a • u := by
        have : ‖v - a • u‖ ^ 2 = 0 := by rw [hnorm, ha2']; ring
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        exact sub_eq_zero.1 (norm_eq_zero.1 this)
      set S1 := {x : ℝ | 0 ≤ x ∧ 0 ≤ a * x} with hS1
      have hS1m : MeasurableSet S1 :=
        (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) measurable_const measurable_id).inter
          (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) (g := fun x : ℝ => a * x)
            measurable_const (by fun_prop))
      have hSS : S = S1 ×ˢ univ := by
        ext p; simp [hS, hS1, hc0]
      have hset : {g : E | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} = (fun g => inner ℝ g u) ⁻¹' S1 := by
        ext g; simp only [mem_setOf_eq, mem_preimage, hS1]; rw [hvau, real_inner_smul_right]
      rw [hset, ← Measure.map_apply (by fun_prop) hS1m, stdGaussian_map_one u hu, hSS,
        Measure.prod_prod, measure_univ, mul_one]
  rw [measureReal_def, key, hS, hc, gauss2_sector a ha1 ha2, ENNReal.toReal_ofReal]
  have := Real.arccos_le_pi a
  rw [sub_nonneg, div_le_iff₀ (by positivity)]; linarith

end E1088
