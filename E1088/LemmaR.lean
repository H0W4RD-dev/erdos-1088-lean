import E1088.GL
import E1088.Sheppard
import E1088.JohnFactor

/-!
# Lemma R (margin rounding)

Source: round9/01 "Lemma R", Rothvoss arXiv:1409.6366 Sec. 3 made quantitative.

**Statement.** Let `N` restricted to `X × Y` have rank `≤ s`, and all entries satisfy
`1/2 ≤ |N x w| ≤ K`. Let `0 < δ ≤ 1/2` and suppose at least `δ |X| |Y|` entries are positive.
Then there is `X' × Y' ⊆ X × Y` with `|X'| ≥ (δ/2) 4^{-T} |X|`, `|Y'| ≥ (δ/2) 4^{-T} |Y|`
containing at most `δ |X'| |Y'|` negative entries, where `T = ⌈π K √s ln(2/δ²)⌉`.

The proof is complete. The two classical inputs are proved in separate files
(E1088/JohnFactor.lean and E1088/Sheppard.lean):

* `john_factor` — John's theorem in factorisation form (a `γ₂`-factorisation): a rank-`≤ s`
  matrix with entries bounded by `K` is `N_xw = ⟨u_x, v_w⟩` in `ℝ^s` with `|u_x| ≤ s^{1/4}` and
  `|v_w| ≤ K s^{1/4}` (put `conv{±u_x}` in John position).
* `sheppard` — Sheppard's formula for the standard Gaussian measure `stdGaussian` on `ℝ^s`:
  `P[⟨g,u⟩ ≥ 0, ⟨g,v⟩ ≥ 0] = 1/2 - arccos⟨u,v⟩/(2π)` for unit vectors `u, v`.

Everything else (normalisation, margin, the product measure of `T` independent Gaussian cuts,
the first-moment argument, the choice of an outcome) is proved here.
-/

set_option linter.unusedSectionVars false

open Finset MeasureTheory ProbabilityTheory Real

namespace E1088

/-- Number of Gaussian rounds in Lemma R: `T = ⌈π K √s ln(2/δ²)⌉`. -/
noncomputable def roundsT (K δ : ℝ) (s : ℕ) : ℕ :=
  ⌈Real.pi * K * Real.sqrt s * Real.log (2 / δ ^ 2)⌉₊

/-- **John's theorem, factorisation form** (`γ₂(N) ≤ √s · max |N|`). PROVED in
E1088/JohnFactor.lean (`john_factor_proved`) by a D-optimal-design argument, without John's
ellipsoid. For a matrix of rank `≤ s` (`s ≥ 1`) on `X × Y` with entries bounded by `K ≥ 0` there
are vectors `u_x, v_w ∈ ℝ^s` with `N x w = ⟨u_x, v_w⟩`, `‖u_x‖ ≤ s^{1/4}`, `‖v_w‖ ≤ K s^{1/4}`.
(Statement fix: the hypothesis `0 ≤ K` was missing; without it the statement is false when
`X = ∅`, `Y ≠ ∅`, `K < 0`. The only use, in `lemmaR`, has `K ≥ 1/2`.) -/
theorem john_factor {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (s : ℕ) (hs1 : 1 ≤ s) (K : ℝ) (hK0 : 0 ≤ K)
    (hrank : rankOn N X Y ≤ s) (hK : ∀ x ∈ X, ∀ w ∈ Y, |N x w| ≤ K) :
    ∃ (u : α → EuclideanSpace ℝ (Fin s)) (v : β → EuclideanSpace ℝ (Fin s)),
      (∀ x ∈ X, ∀ w ∈ Y, N x w = inner ℝ (u x) (v w)) ∧
      (∀ x ∈ X, ‖u x‖ ≤ (s : ℝ) ^ (1 / 4 : ℝ)) ∧
      (∀ w ∈ Y, ‖v w‖ ≤ K * (s : ℝ) ^ (1 / 4 : ℝ)) :=
  john_factor_proved N X Y s hs1 K hK0 hrank hK

/-- The quadrant event `{g : ⟨g,u⟩ ≥ 0, ⟨g,v⟩ ≥ 0}`. -/
def quadrant {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) : Set (EuclideanSpace ℝ (Fin s)) :=
  {g | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v}

/-- **Sheppard's formula** (proved in E1088/Sheppard.lean). For unit vectors `u, v` and a
standard Gaussian vector `g` in `ℝ^s`, `P[⟨g,u⟩ ≥ 0 ∧ ⟨g,v⟩ ≥ 0] = 1/2 - arccos⟨u,v⟩/(2π)`. -/
theorem sheppard {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin s))).real (quadrant u v) =
      1 / 2 - Real.arccos (inner ℝ u v) / (2 * Real.pi) :=
  sheppard_general u v hu hv

theorem measurableSet_quadrant {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) :
    MeasurableSet (quadrant u v) := by
  have h1 : IsClosed {g : EuclideanSpace ℝ (Fin s) | 0 ≤ inner ℝ g u} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  have h2 : IsClosed {g : EuclideanSpace ℝ (Fin s) | 0 ≤ inner ℝ g v} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  exact (h1.inter h2).measurableSet

/-- Sheppard, positive correlation: probability at least `1/4`. -/
theorem sheppard_pos {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : 0 ≤ inner ℝ u v) :
    1 / 4 ≤ (stdGaussian (EuclideanSpace ℝ (Fin s))).real (quadrant u v) := by
  rw [sheppard u v hu hv]
  have h1 := Real.arccos_le_pi_div_two.2 ha
  have hπ := Real.pi_pos
  have : Real.arccos (inner ℝ u v) / (2 * Real.pi) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-- Sheppard, negative correlation `≤ -b`: probability at most `1/4 - b/(2π)`. -/
theorem sheppard_neg {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ha : inner ℝ u v ≤ -b) :
    (stdGaussian (EuclideanSpace ℝ (Fin s))).real (quadrant u v) ≤
      1 / 4 - b / (2 * Real.pi) := by
  rw [sheppard u v hu hv]
  have hπ := Real.pi_pos
  have h1 : Real.arccos (-b) ≤ Real.arccos (inner ℝ u v) := Real.arccos_le_arccos ha
  rw [Real.arccos_neg, Real.arccos_eq_pi_div_two_sub_arcsin] at h1
  have h2 : b ≤ Real.arcsin b := by
    have := Real.sin_le (Real.arcsin_nonneg.2 hb0)
    rwa [Real.sin_arcsin (by linarith) hb1] at this
  have h3 : (Real.pi / 2 + b) / (2 * Real.pi) ≤ Real.arccos (inner ℝ u v) / (2 * Real.pi) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h4 : (Real.pi / 2 + b) / (2 * Real.pi) = 1 / 4 + b / (2 * Real.pi) := by
    field_simp; ring
  linarith

/-- `(1 - y)^T ≤ exp(-L)` when `L ≤ y T`. -/
theorem one_sub_pow_le_exp (y L : ℝ) (T : ℕ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hT : L ≤ y * T) :
    (1 - y) ^ T ≤ Real.exp (-L) := by
  calc (1 - y) ^ T ≤ (Real.exp (-y)) ^ T := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (-y); linarith
    _ = Real.exp (-(y * T)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)

theorem rankOn_eq_zero_imp {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (h : rankOn N X Y = 0) : ∀ x ∈ X, ∀ w ∈ Y, N x w = 0 := by
  intro x hx w hw
  obtain ⟨r, U, V, hr, hUV⟩ := exists_factor (Matrix.of fun (i : X) (j : Y) => N i j)
  have hr0 : r = 0 := by rw [hr]; exact h
  subst hr0
  have := congrFun (congrFun hUV ⟨x, hx⟩) ⟨w, hw⟩
  simpa [Matrix.mul_apply] using this

set_option maxHeartbeats 2000000 in
/-- **Lemma R (margin rounding).** Proved from `john_factor` and `sheppard`. -/
theorem lemmaR {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (s : ℕ) (K δ : ℝ) (hs : rankOn N X Y ≤ s)
    (hN : ∀ x ∈ X, ∀ w ∈ Y, 1 / 2 ≤ |N x w| ∧ |N x w| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hpos : δ * (#X * #Y) ≤ #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y,
      δ / 2 * #X ≤ 4 ^ roundsT K δ s * #X' ∧ δ / 2 * #Y ≤ 4 ^ roundsT K δ s * #Y' ∧
      (#((X' ×ˢ Y').filter fun p => N p.1 p.2 < 0) : ℝ) ≤ δ * (#X' * #Y') := by
  classical
  set T := roundsT K δ s with hT
  have h4T : (1 : ℝ) ≤ 4 ^ T := one_le_pow₀ (by norm_num)
  -- degenerate rectangles
  by_cases hne : X.Nonempty ∧ Y.Nonempty
  swap
  · refine ⟨X, subset_refl _, Y, subset_refl _, ?_, ?_, ?_⟩
    · have : (0 : ℝ) ≤ #X := Nat.cast_nonneg _
      nlinarith
    · have : (0 : ℝ) ≤ #Y := Nat.cast_nonneg _
      nlinarith
    · have : X ×ˢ Y = ∅ := by
        rcases not_and_or.1 hne with h | h
        · rw [not_nonempty_iff_eq_empty] at h; simp [h]
        · rw [not_nonempty_iff_eq_empty] at h; simp [h]
      simp only [this, filter_empty, card_empty, Nat.cast_zero]
      positivity
  obtain ⟨⟨x0, hx0⟩, ⟨w0, hw0⟩⟩ := hne
  have hK : 1 / 2 ≤ K := (hN x0 hx0 w0 hw0).1.trans (hN x0 hx0 w0 hw0).2
  have hs1 : 1 ≤ s := by
    by_contra h
    have h0 : rankOn N X Y = 0 := by omega
    have h1 := rankOn_eq_zero_imp N X Y h0 x0 hx0 w0 hw0
    have h2 := (hN x0 hx0 w0 hw0).1
    rw [h1, abs_zero] at h2; norm_num at h2
  obtain ⟨u, v, hNuv, hu, hv⟩ := john_factor N X Y s hs1 K (by linarith) hs (fun x hx w hw => (hN x hx w hw).2)
  set c4 : ℝ := (s : ℝ) ^ (1 / 4 : ℝ) with hc4
  have hs1r : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hc4pos : 0 < c4 := Real.rpow_pos_of_pos (by linarith) _
  have hc4sq : c4 * c4 = Real.sqrt s := by
    rw [hc4, ← Real.rpow_add (by linarith), Real.sqrt_eq_rpow]; norm_num
  have hsqrt1 : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs1r
  -- the vectors are nonzero
  have hun : ∀ x ∈ X, 0 < ‖u x‖ := by
    intro x hx
    rw [norm_pos_iff]; intro h0
    have := (hN x hx w0 hw0).1
    rw [hNuv x hx w0 hw0, h0, inner_zero_left, abs_zero] at this; norm_num at this
  have hvn : ∀ w ∈ Y, 0 < ‖v w‖ := by
    intro w hw
    rw [norm_pos_iff]; intro h0
    have := (hN x0 hx0 w hw).1
    rw [hNuv x0 hx0 w hw, h0, inner_zero_right, abs_zero] at this; norm_num at this
  set uh : α → EuclideanSpace ℝ (Fin s) := fun x => ‖u x‖⁻¹ • u x with huh
  set vh : β → EuclideanSpace ℝ (Fin s) := fun w => ‖v w‖⁻¹ • v w with hvh
  have huh1 : ∀ x ∈ X, ‖uh x‖ = 1 := fun x hx => by
    simp only [huh]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hun x hx).ne']
  have hvh1 : ∀ w ∈ Y, ‖vh w‖ = 1 := fun w hw => by
    simp only [hvh]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hvn w hw).ne']
  have hinner : ∀ x ∈ X, ∀ w ∈ Y, inner ℝ (uh x) (vh w) = N x w / (‖u x‖ * ‖v w‖) := by
    intro x hx w hw
    simp only [huh, hvh]
    rw [real_inner_smul_left, real_inner_smul_right, ← hNuv x hx w hw]
    field_simp
  -- margin
  set b : ℝ := 1 / (2 * K * Real.sqrt s) with hb
  have hKs : 1 ≤ 2 * K * Real.sqrt s := by nlinarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb1 : b ≤ 1 := by rw [hb, div_le_one (by linarith)]; exact hKs
  have hbK : b * (K * Real.sqrt s) = 1 / 2 := by
    rw [hb]; field_simp
  have hmarg_pos : ∀ x ∈ X, ∀ w ∈ Y, 0 < N x w → 0 ≤ inner ℝ (uh x) (vh w) := by
    intro x hx w hw h
    rw [hinner x hx w hw]
    exact div_nonneg h.le (mul_pos (hun x hx) (hvn w hw)).le
  have hmarg_neg : ∀ x ∈ X, ∀ w ∈ Y, N x w < 0 → inner ℝ (uh x) (vh w) ≤ -b := by
    intro x hx w hw h
    rw [hinner x hx w hw]
    have hP := mul_pos (hun x hx) (hvn w hw)
    have hPle : ‖u x‖ * ‖v w‖ ≤ K * Real.sqrt s := by
      have := mul_le_mul (hu x hx) (hv w hw) (norm_nonneg _) hc4pos.le
      rw [← hc4sq]; nlinarith
    have hNle : N x w ≤ -(1 / 2) := by
      have := (hN x hx w hw).1
      rw [abs_of_neg h] at this; linarith
    rw [div_le_iff₀ hP]
    nlinarith
  -- probabilities of the single quadrant events
  set γ := stdGaussian (EuclideanSpace ℝ (Fin s)) with hγ
  set p : α → β → ℝ := fun x w => γ.real (quadrant (uh x) (vh w)) with hp
  have hp_pos : ∀ x ∈ X, ∀ w ∈ Y, 0 < N x w → 1 / 4 ≤ p x w := fun x hx w hw h =>
    sheppard_pos _ _ (huh1 x hx) (hvh1 w hw) (hmarg_pos x hx w hw h)
  have hp_neg : ∀ x ∈ X, ∀ w ∈ Y, N x w < 0 → p x w ≤ 1 / 4 * (1 - 2 * b / Real.pi) := by
    intro x hx w hw h
    have := sheppard_neg _ _ (huh1 x hx) (hvh1 w hw) b hb0.le hb1 (hmarg_neg x hx w hw h)
    have hπ := Real.pi_pos
    have e : 1 / 4 - b / (2 * Real.pi) = 1 / 4 * (1 - 2 * b / Real.pi) := by field_simp; ring
    linarith
  have hp_nn : ∀ x w, 0 ≤ p x w := fun x w => measureReal_nonneg
  -- T independent Gaussian cuts
  set μ : Measure (Fin T → EuclideanSpace ℝ (Fin s)) := Measure.pi fun _ => γ with hμ
  set B : α → β → Set (Fin T → EuclideanSpace ℝ (Fin s)) :=
    fun x w => Set.pi Set.univ fun _ => quadrant (uh x) (vh w) with hB
  have hBmeas : ∀ x w, MeasurableSet (B x w) := fun x w =>
    MeasurableSet.univ_pi fun _ => measurableSet_quadrant _ _
  have hμB : ∀ x w, μ.real (B x w) = p x w ^ T := by
    intro x w
    simp only [hμ, hB, measureReal_def, Measure.pi_pi, prod_const, card_univ, Fintype.card_fin,
      ENNReal.toReal_pow, hp]
  set Qp := (X ×ˢ Y).filter fun q => 0 < N q.1 q.2 with hQp
  set Qn := (X ×ˢ Y).filter fun q => N q.1 q.2 < 0 with hQn
  set F : (Fin T → EuclideanSpace ℝ (Fin s)) → ℝ := fun ω =>
    (∑ q ∈ Qp, (B q.1 q.2).indicator 1 ω) - (1 / δ) * ∑ q ∈ Qn, (B q.1 q.2).indicator 1 ω
    with hF
  have hint : ∀ q : α × β, Integrable ((B q.1 q.2).indicator (1 : (Fin T → EuclideanSpace ℝ (Fin s)) → ℝ)) μ := fun q =>
    (integrable_const (1 : ℝ)).indicator (hBmeas q.1 q.2)
  have hFint : Integrable F μ :=
    (integrable_finsetSum _ fun q _ => hint q).sub
      ((integrable_finsetSum _ fun q _ => hint q).const_mul _)
  have hIF : ∫ ω, F ω ∂μ = (∑ q ∈ Qp, p q.1 q.2 ^ T) - (1 / δ) * ∑ q ∈ Qn, p q.1 q.2 ^ T := by
    simp only [hF]
    rw [integral_sub (integrable_finsetSum _ fun q _ => hint q)
      ((integrable_finsetSum _ fun q _ => hint q).const_mul _), integral_const_mul,
      integral_finsetSum _ fun q _ => hint q, integral_finsetSum _ fun q _ => hint q]
    simp only [integral_indicator_one (hBmeas _ _), hμB]
  -- the expectation bound
  set y : ℝ := 2 * b / Real.pi with hy
  have hπ := Real.pi_pos
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one hπ]; have := Real.pi_gt_three; linarith
  have hL : Real.log (2 / δ ^ 2) ≤ y * T := by
    have hlog : 0 ≤ Real.log (2 / δ ^ 2) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hTge : Real.pi * K * Real.sqrt s * Real.log (2 / δ ^ 2) ≤ T := Nat.le_ceil _
    have : y * (Real.pi * K * Real.sqrt s * Real.log (2 / δ ^ 2)) = Real.log (2 / δ ^ 2) := by
      rw [hy]
      have : 2 * b * (K * Real.sqrt s) = 1 := by linarith
      field_simp
      linear_combination Real.log (2 / δ ^ 2) * this
    nlinarith
  have hexp : (1 - y) ^ T ≤ δ ^ 2 / 2 := by
    have := one_sub_pow_le_exp y _ T hy0 hy1 hL
    rwa [Real.exp_neg, Real.exp_log (by positivity), inv_div] at this
  have hq : (0 : ℝ) < (1 / 4) ^ T := by positivity
  have hsumP : #Qp * (1 / 4 : ℝ) ^ T ≤ ∑ q ∈ Qp, p q.1 q.2 ^ T := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun q hq' => ?_
    obtain ⟨hqXY, hq0⟩ := mem_filter.1 hq'
    obtain ⟨hqx, hqw⟩ := mem_product.1 hqXY
    exact pow_le_pow_left₀ (by norm_num) (hp_pos q.1 hqx q.2 hqw hq0) T
  have hsumN : ∑ q ∈ Qn, p q.1 q.2 ^ T ≤ (#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2)) := by
    calc ∑ q ∈ Qn, p q.1 q.2 ^ T ≤ ∑ _q ∈ Qn, (1 / 4 : ℝ) ^ T * (δ ^ 2 / 2) := by
          refine sum_le_sum fun q hq' => ?_
          obtain ⟨hqXY, hq0⟩ := mem_filter.1 hq'
          obtain ⟨hqx, hqw⟩ := mem_product.1 hqXY
          calc p q.1 q.2 ^ T ≤ (1 / 4 * (1 - 2 * b / Real.pi)) ^ T :=
                pow_le_pow_left₀ (hp_nn _ _) (hp_neg q.1 hqx q.2 hqw hq0) T
            _ = (1 / 4) ^ T * (1 - y) ^ T := by rw [mul_pow]
            _ ≤ (1 / 4) ^ T * (δ ^ 2 / 2) := mul_le_mul_of_nonneg_left hexp hq.le
      _ = #Qn * ((1 / 4 : ℝ) ^ T * (δ ^ 2 / 2)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : #Qn ≤ #X * #Y := (card_filter_le _ _).trans (card_product X Y).le
          exact_mod_cast this
  have hEF : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ ∫ ω, F ω ∂μ := by
    rw [hIF]
    have h1 : δ * (#X * #Y) * (1 / 4 : ℝ) ^ T ≤ ∑ q ∈ Qp, p q.1 q.2 ^ T :=
      (mul_le_mul_of_nonneg_right hpos hq.le).trans hsumP
    have h2 : (1 / δ) * ∑ q ∈ Qn, p q.1 q.2 ^ T ≤
        (1 / δ) * ((#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2))) :=
      mul_le_mul_of_nonneg_left hsumN (by positivity)
    have h3 : (1 / δ) * ((#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2))) =
        (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) := by field_simp
    nlinarith
  obtain ⟨ω, hω⟩ := exists_integral_le hFint
  -- the random rectangle
  set X' := X.filter fun x => ∀ t, 0 ≤ inner ℝ (ω t) (uh x) with hX'
  set Y' := Y.filter fun w => ∀ t, 0 ≤ inner ℝ (ω t) (vh w) with hY'
  have hmemB : ∀ q ∈ X ×ˢ Y, ω ∈ B q.1 q.2 ↔ q ∈ X' ×ˢ Y' := by
    intro q hq'
    obtain ⟨hqx, hqw⟩ := mem_product.1 hq'
    simp only [hB, Set.mem_pi, Set.mem_univ, true_implies, quadrant, Set.mem_ofPred_eq, hX', hY',
      mem_product, mem_filter]
    constructor
    · intro h; exact ⟨⟨hqx, fun t => (h t).1⟩, ⟨hqw, fun t => (h t).2⟩⟩
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ t; exact ⟨h1 t, h2 t⟩
  have hcount : ∀ (Q : Finset (α × β)) (P : α × β → Prop) [DecidablePred P],
      Q = (X ×ˢ Y).filter P →
      ∑ q ∈ Q, (B q.1 q.2).indicator (1 : (Fin T → EuclideanSpace ℝ (Fin s)) → ℝ) ω = #((X' ×ˢ Y').filter P) := by
    intro Q P _ hQ
    rw [hQ]
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [sum_boole]
    norm_cast
    congr 1
    ext q
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hq', hP⟩, hB'⟩
      exact ⟨(hmemB q hq').1 hB', hP⟩
    · rintro ⟨hq', hP⟩
      have hq'' : q ∈ X ×ˢ Y := by
        obtain ⟨a, b'⟩ := mem_product.1 hq'
        exact mem_product.2 ⟨(mem_filter.1 a).1, (mem_filter.1 b').1⟩
      exact ⟨⟨hq'', hP⟩, (hmemB q hq'').2 hq'⟩
  have hFω : F ω = (#((X' ×ˢ Y').filter fun q => 0 < N q.1 q.2) : ℝ) -
      (1 / δ) * (#((X' ×ˢ Y').filter fun q => N q.1 q.2 < 0) : ℝ) := by
    simp only [hF]
    rw [hcount Qp (fun q => 0 < N q.1 q.2) hQp, hcount Qn (fun q => N q.1 q.2 < 0) hQn]
  set Pc : ℝ := ((#((X' ×ˢ Y').filter fun q => 0 < N q.1 q.2) : ℕ) : ℝ) with hPc
  set Nc : ℝ := ((#((X' ×ˢ Y').filter fun q => N q.1 q.2 < 0) : ℕ) : ℝ) with hNc
  have hmain : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ Pc - (1 / δ) * Nc := by
    rw [← hFω]; linarith
  have hPle : Pc ≤ #X' * #Y' := by
    have : #((X' ×ˢ Y').filter fun q => 0 < N q.1 q.2) ≤ #X' * #Y' :=
      (card_filter_le _ _).trans (card_product X' Y').le
    rw [hPc]; exact_mod_cast this
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 ⟨x0, hx0⟩
  have hYpos : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 ⟨w0, hw0⟩
  have hNc0 : 0 ≤ Nc := Nat.cast_nonneg _
  have hpos' : 0 < (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) := by positivity
  have hX'le : (#X' : ℝ) ≤ #X := by exact_mod_cast card_le_card (filter_subset _ _)
  have hY'le : (#Y' : ℝ) ≤ #Y := by exact_mod_cast card_le_card (filter_subset _ _)
  have h4q : (4 : ℝ) ^ T * (1 / 4) ^ T = 1 := by rw [← mul_pow]; norm_num
  have hXY' : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ #X' * #Y' := by
    have : 0 ≤ (1 / δ) * Nc := by positivity
    linarith
  refine ⟨X', filter_subset _ _, Y', filter_subset _ _, ?_, ?_, ?_⟩
  · -- `(δ/2) |X| ≤ 4^T |X'|`
    have h1 : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ #X' * #Y := by
      have : (#X' : ℝ) * #Y' ≤ #X' * #Y := mul_le_mul_of_nonneg_left hY'le (Nat.cast_nonneg _)
      linarith
    have h2 : (1 / 4 : ℝ) ^ T * (δ / 2) * #X ≤ #X' := by
      have := h1
      rw [show (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) = ((1 / 4 : ℝ) ^ T * (δ / 2) * #X) * #Y
        by ring] at this
      exact le_of_mul_le_mul_right this hYpos
    calc δ / 2 * #X = 4 ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #X) := by
          rw [show (4 : ℝ) ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #X) =
            ((4 : ℝ) ^ T * (1 / 4) ^ T) * (δ / 2 * #X) by ring, h4q, one_mul]
      _ ≤ 4 ^ T * #X' := mul_le_mul_of_nonneg_left h2 (by positivity)
  · have h1 : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ #X * #Y' := by
      have : (#X' : ℝ) * #Y' ≤ #X * #Y' := mul_le_mul_of_nonneg_right hX'le (Nat.cast_nonneg _)
      linarith
    have h2 : (1 / 4 : ℝ) ^ T * (δ / 2) * #Y ≤ #Y' := by
      have := h1
      rw [show (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) = ((1 / 4 : ℝ) ^ T * (δ / 2) * #Y) * #X
        by ring, mul_comm (#X : ℝ) (#Y' : ℝ)] at this
      exact le_of_mul_le_mul_right this hXpos
    calc δ / 2 * #Y = 4 ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #Y) := by
          rw [show (4 : ℝ) ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #Y) =
            ((4 : ℝ) ^ T * (1 / 4) ^ T) * (δ / 2 * #Y) by ring, h4q, one_mul]
      _ ≤ 4 ^ T * #Y' := mul_le_mul_of_nonneg_left h2 (by positivity)
  · -- `Nc ≤ δ Pc ≤ δ |X'||Y'|`
    have h1 : (1 / δ) * Nc ≤ Pc := by linarith
    have h2 : Nc ≤ δ * Pc := by
      have := mul_le_mul_of_nonneg_left h1 hδ0.le
      rwa [← mul_assoc, mul_one_div_cancel hδ0.ne', one_mul] at this
    calc Nc ≤ δ * Pc := h2
      _ ≤ δ * (#X' * #Y') := mul_le_mul_of_nonneg_left hPle hδ0.le

end E1088
