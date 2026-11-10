import E1088.GL

/-!
# A `γ₂`-factorisation of bounded low-rank matrices (replaces John's theorem)

`john_factor_proved`: a matrix of rank `≤ s` with entries bounded by `K ≥ 0` factors as
`N x w = ⟨u_x, v_w⟩` in `ℝ^s` with `‖u_x‖ ≤ s^{1/4}` and `‖v_w‖ ≤ K s^{1/4}`.

Proof (D-optimal design / Kiefer–Wolfowitz, no ellipsoids): write `N x w = a_x ⬝ b_w` in `ℝ^r`,
`r = rank`, with the `a_x` spanning; maximise `det (∑ λ_x a_x a_xᵀ)` over the standard simplex;
first-order optimality (matrix determinant lemma + Bernoulli) gives `a_xᵀ M⁻¹ a_x ≤ r`; with
`M = U diag(e) Uᵀ` put `u'_x = diag(e^{-1/2}) Uᵀ a_x`, `v'_w = diag(e^{1/2}) Uᵀ b_w`, so
`‖u'_x‖² ≤ r`, `‖v'_w‖² = ∑ λ_x N_xw² ≤ K²`; rescale by `r^{∓1/4}`.
-/

set_option linter.unusedSectionVars false

open Finset Matrix

namespace E1088

/-! ### The scalar step -/

theorem kw_scalar (r : ℕ) (hr : 1 ≤ r) (q : ℝ) (hq0 : 0 ≤ q)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → (1 - t) ^ r + t * (1 - t) ^ (r - 1) * q ≤ 1) :
    q ≤ r := by
  by_contra hcon
  push Not at hcon
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hqpos : 0 < q := lt_of_lt_of_le (by linarith) hcon.le
  set t : ℝ := (q - r) / (2 * r * q) with ht
  have htpos : 0 < t := div_pos (by linarith) (by positivity)
  have ht2 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]
    nlinarith
  have hrt : (r : ℝ) * t ≤ 1 / 2 := by
    rw [ht, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hb1 : 1 + (r : ℝ) * (-t) ≤ (1 + -t) ^ r := one_add_mul_le_pow (by linarith) r
  have hb2 : 1 + ((r - 1 : ℕ) : ℝ) * (-t) ≤ (1 + -t) ^ (r - 1) := one_add_mul_le_pow (by linarith) _
  have hcast : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub hr]; simp
  rw [hcast] at hb2
  have hpos2 : 0 ≤ 1 + ((r : ℝ) - 1) * (-t) := by nlinarith
  have key := h t htpos ht2
  have e1 : (1 - t) ^ r ≥ 1 - r * t := by
    have : (1 + -t) = 1 - t := by ring
    rw [this] at hb1; linarith
  have e2 : (1 - t) ^ (r - 1) ≥ 1 - (r - 1) * t := by
    have : (1 + -t) = 1 - t := by ring
    rw [this] at hb2; linarith
  have e3 : t * (1 - t) ^ (r - 1) * q ≥ t * (1 - (r - 1) * t) * q := by
    have : 0 ≤ t * q := by positivity
    have := mul_le_mul_of_nonneg_left e2 this
    linarith [show t * (1 - t) ^ (r - 1) * q = t * q * (1 - t) ^ (r - 1) by ring,
      show t * (1 - (r - 1) * t) * q = t * q * (1 - (r - 1) * t) by ring]
  -- `1 - rt + tq(1 - (r-1)t) > 1`
  have e4 : t * (q - r) - (r - 1) * q * t ^ 2 > 0 := by
    have h1 : (r - 1) * q * t ≤ (q - r) / 2 := by
      have : (r : ℝ) * q * t = (q - r) / 2 := by
        rw [ht]; field_simp
      nlinarith
    have : t * (q - r) - (r - 1) * q * t ^ 2 = t * ((q - r) - (r - 1) * q * t) := by ring
    rw [this]
    apply mul_pos htpos
    linarith
  nlinarith

/-! ### Design matrices -/

section design

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- `∑ λ_i a_i a_iᵀ`. -/
noncomputable def designMat (a : ι → Fin r → ℝ) (lam : ι → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ i, lam i • vecMulVec (a i) (a i)

theorem designMat_mulVec (a : ι → Fin r → ℝ) (lam : ι → ℝ) (x : Fin r → ℝ) :
    designMat a lam *ᵥ x = ∑ i, (lam i * (a i ⬝ᵥ x)) • a i := by
  unfold designMat
  rw [sum_mulVec]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, vecMulVec_mulVec]
  ext k
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem designMat_quad (a : ι → Fin r → ℝ) (lam : ι → ℝ) (x y : Fin r → ℝ) :
    y ⬝ᵥ (designMat a lam *ᵥ x) = ∑ i, lam i * (a i ⬝ᵥ x) * (a i ⬝ᵥ y) := by
  rw [designMat_mulVec, dotProduct_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm y (a i)]

theorem designMat_isHermitian (a : ι → Fin r → ℝ) (lam : ι → ℝ) :
    (designMat a lam).IsHermitian := by
  unfold designMat IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  ext k l
  simp [transpose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]

theorem designMat_posSemidef (a : ι → Fin r → ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    (designMat a lam).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (designMat_isHermitian a lam) fun x => ?_
  rw [star_trivial, designMat_quad]
  exact sum_nonneg fun i _ => by
    have := hlam i
    have : 0 ≤ (a i ⬝ᵥ x) * (a i ⬝ᵥ x) := mul_self_nonneg _
    nlinarith

theorem designMat_comb (a : ι → Fin r → ℝ) (lam : ι → ℝ) (t : ℝ) (i0 : ι) :
    designMat a ((1 - t) • lam + t • Pi.single i0 1) =
      (1 - t) • designMat a lam + t • vecMulVec (a i0) (a i0) := by
  unfold designMat
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, sum_add_distrib, mul_smul,
    ← smul_sum]
  congr 1
  rw [Finset.sum_eq_single i0]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · intro h; exact absurd (mem_univ _) h

/-- **Kiefer–Wolfowitz** (the half used): an optimal design has `a_iᵀ M⁻¹ a_i ≤ r`. -/
theorem kw_design [Nonempty ι] (a : ι → Fin r → ℝ) (hr : 1 ≤ r)
    (hspan : ∀ x : Fin r → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ (designMat a lam).PosDef ∧
      ∀ i, a i ⬝ᵥ ((designMat a lam)⁻¹ *ᵥ a i) ≤ r := by
  classical
  set f : (ι → ℝ) → ℝ := fun lam => (designMat a lam).det with hf
  have hfc : Continuous f := by
    refine Continuous.matrix_det ?_
    unfold designMat
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set u : ι → ℝ := fun _ => 1 / n with hu
  have hu_mem : u ∈ stdSimplex ℝ ι := by
    refine ⟨fun i => by positivity, ?_⟩
    simp only [hu, sum_const, card_univ, nsmul_eq_mul]
    rw [← hn]; field_simp
  obtain ⟨lam, hlam, hmax⟩ := (isCompact_stdSimplex ℝ ι).exists_isMaxOn ⟨u, hu_mem⟩ hfc.continuousOn
  have hlam0 : ∀ i, 0 ≤ lam i := hlam.1
  have hlam1 : ∑ i, lam i = 1 := hlam.2
  -- the uniform design is positive definite
  have hupd : (designMat a u).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos (designMat_isHermitian a u) fun x hx => ?_
    rw [star_trivial, designMat_quad]
    have hex : ∃ i, a i ⬝ᵥ x ≠ 0 := by
      by_contra hno; push Not at hno; exact hx (hspan x hno)
    obtain ⟨i0, hi0⟩ := hex
    have hterm : ∀ i ∈ univ, 0 ≤ u i * (a i ⬝ᵥ x) * (a i ⬝ᵥ x) := fun i _ => by
      have h1 : 0 ≤ u i := by simp only [hu]; exact div_nonneg zero_le_one hnpos.le
      rw [mul_assoc]; exact mul_nonneg h1 (mul_self_nonneg _)
    refine lt_of_lt_of_le ?_ (single_le_sum hterm (mem_univ i0))
    have : 0 < (a i0 ⬝ᵥ x) * (a i0 ⬝ᵥ x) := mul_self_pos.2 hi0
    rw [mul_assoc]; exact mul_pos (by simp only [hu]; exact div_pos one_pos hnpos) this
  have hdetu : 0 < f u := hupd.det_pos
  have hdet : 0 < f lam := lt_of_lt_of_le hdetu (hmax hu_mem)
  set M := designMat a lam with hM
  have hMpd : M.PosDef := (designMat_posSemidef a lam hlam0).posDef_iff_det_ne_zero.2 hdet.ne'
  refine ⟨lam, hlam0, hlam1, hMpd, fun i0 => ?_⟩
  -- first-order optimality in the direction of `e_{i0}`
  set q := a i0 ⬝ᵥ (M⁻¹ *ᵥ a i0) with hq
  have hq0 : 0 ≤ q := by
    have := hMpd.inv.posSemidef
    have h2 := (posSemidef_iff_dotProduct_mulVec.1 this).2 (a i0)
    rwa [star_trivial] at h2
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet.ne'
  refine kw_scalar r hr q hq0 fun t ht0 ht2 => ?_
  have ht1 : t < 1 := by linarith
  have hmem : (1 - t) • lam + t • Pi.single i0 1 ∈ stdSimplex ℝ ι := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hlam0 i
      have : 0 ≤ (Pi.single i0 (1 : ℝ) : ι → ℝ) i := by
        by_cases h : i = i0 <;> simp [Pi.single_apply, h]
      nlinarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hlam1]
      simp
  have hle : f ((1 - t) • lam + t • Pi.single i0 1) ≤ f lam := hmax hmem
  simp only [hf] at hle
  rw [designMat_comb] at hle
  -- `det((1-t)M + t aaᵀ) = (1-t)^r det M (1 + t/(1-t) q)`
  set c : ℝ := t / (1 - t) with hc
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hsplit : (1 - t) • M + t • vecMulVec (a i0) (a i0) =
      (1 - t) • (M + replicateCol Unit (c • a i0) * replicateRow Unit (a i0)) := by
    rw [← vecMulVec_eq, smul_add]
    congr 1
    ext k l
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hc]
    field_simp
  have hlemma := det_add_replicateCol_mul_replicateRow (ι := Unit) hMunit (c • a i0) (a i0)
  have hentry : (1 + replicateRow Unit (a i0) * M⁻¹ * replicateCol Unit (c • a i0)).det =
      1 + c * q := by
    rw [det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
      replicateCol_apply, Pi.smul_apply, smul_eq_mul, hq, dotProduct, mulVec, Finset.univ_unique,
      Finset.sum_singleton]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [hsplit, det_smul, hlemma, hentry, Fintype.card_fin] at hle
  -- divide by `det M > 0`
  have hdetM : 0 < M.det := hdet
  have h3 : (1 - t) ^ r * (1 + c * q) ≤ 1 := by
    have : (1 - t) ^ r * (M.det * (1 + c * q)) ≤ 1 * M.det := by linarith
    nlinarith
  have hr1 : (1 - t) ^ r = (1 - t) * (1 - t) ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : (1 - t) ^ r * (1 + c * q) = (1 - t) ^ r + t * (1 - t) ^ (r - 1) * q := by
    rw [hr1, hc]; field_simp
  linarith

end design

/-! ### Square-root factorisation of a positive definite matrix -/

theorem dot_mulVec_mulVec {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ) (y z : Fin r → ℝ) :
    (A *ᵥ y) ⬝ᵥ (B *ᵥ z) = y ⬝ᵥ ((Aᵀ * B) *ᵥ z) := by
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec]

theorem pd_factor {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.PosDef) :
    ∃ L R : Matrix (Fin r) (Fin r) ℝ, Lᵀ * R = 1 ∧ Rᵀ * R = M ∧ Lᵀ * L = M⁻¹ := by
  classical
  have hH := hM.1
  set U : Matrix (Fin r) (Fin r) ℝ := (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  set e := hH.eigenvalues with he
  have hspec : M = U * diagonal e * Uᵀ := by
    have h := hH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp] at h
    exact h
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using this
  have hUtU : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using this
  have hepos : ∀ i, 0 < e i := hM.eigenvalues_pos
  set sq : Fin r → ℝ := fun i => Real.sqrt (e i) with hsq
  have hsqpos : ∀ i, 0 < sq i := fun i => Real.sqrt_pos.2 (hepos i)
  refine ⟨diagonal (fun i => (sq i)⁻¹) * Uᵀ, diagonal sq * Uᵀ, ?_, ?_, ?_⟩
  · rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have : (fun i => (sq i)⁻¹ * sq i) = fun _ => (1 : ℝ) := by
      funext i; exact inv_mul_cancel₀ (hsqpos i).ne'
    rw [this, diagonal_one, Matrix.one_mul, hUU]
  · have hss : (fun i => sq i * sq i) = e := funext fun i => Real.mul_self_sqrt (hepos i).le
    rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal, hss, hspec, Matrix.mul_assoc]
  · rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    symm
    apply inv_eq_right_inv
    rw [hspec]
    calc U * diagonal e * Uᵀ * (U * (diagonal (fun i => (sq i)⁻¹ * (sq i)⁻¹) * Uᵀ))
        = U * (diagonal e * (Uᵀ * U) * diagonal (fun i => (sq i)⁻¹ * (sq i)⁻¹)) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * Uᵀ := by
          rw [hUtU, Matrix.mul_one, diagonal_mul_diagonal]
          have : (fun i => e i * ((sq i)⁻¹ * (sq i)⁻¹)) = fun _ => (1 : ℝ) := by
            funext i
            have h1 : sq i * sq i = e i := Real.mul_self_sqrt (hepos i).le
            rw [← h1]; field_simp [(hsqpos i).ne']
          rw [this, diagonal_one, Matrix.mul_one]
      _ = 1 := hUU

/-- A factorisation of a matrix through its rank, with spanning left factors. -/
theorem rank_factor {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) :
    ∃ (r : ℕ) (a : X → Fin r → ℝ) (b : Y → Fin r → ℝ), r = rankOn N X Y ∧
      (∀ (i : X) (j : Y), N i j = a i ⬝ᵥ b j) ∧
        (∀ x : Fin r → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0) := by
  classical
  set A : Matrix X Y ℝ := Matrix.of fun (i : X) (j : Y) => N i j with hA
  set V := LinearMap.range A.mulVecLin with hV
  set bV := Module.finBasis ℝ V with hbV
  let col : Y → V := fun j => ⟨A.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨Module.finrank ℝ V, fun i k => (bV k : X → ℝ) i, fun j k => bV.repr (col j) k, rfl,
    ?_, ?_⟩
  · intro i j
    have h := bV.sum_repr (col j)
    have h2 := congrArg (fun v : V => (v : X → ℝ) i) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h2
    have hcol : ((col j : V) : X → ℝ) i = N i j := by
      simp [col, Matrix.mulVecLin_apply, mulVec_single_one, hA]
    rw [← hcol, ← h2, dotProduct]
    exact sum_congr rfl fun k _ => mul_comm _ _
  · intro x hx
    have hsum : ∑ k, x k • bV k = 0 := by
      apply Subtype.ext
      funext i
      have := hx i
      simp only [dotProduct] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
      rw [← this]
      exact sum_congr rfl fun k _ => mul_comm _ _
    funext k
    exact Fintype.linearIndependent_iff.1 bV.linearIndependent x hsum k

/-- Embedding `ℝ^r → ℝ^s` (`r ≤ s`). -/
noncomputable def embR {r : ℕ} (s : ℕ) (v : Fin r → ℝ) : EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 (fun k : Fin s => if hk : (k : ℕ) < r then v ⟨k, hk⟩ else 0)

theorem embR_inner {r s : ℕ} (hrs : r ≤ s) (v w : Fin r → ℝ) :
    inner ℝ (embR s v) (embR s w) = v ⬝ᵥ w := by
  let f : ℕ → ℝ := fun n => if h : n < r then v ⟨n, h⟩ * w ⟨n, h⟩ else 0
  have h1 : inner ℝ (embR s v) (embR s w) = ∑ k : Fin s, f k := by
    simp only [embR, PiLp.inner_apply, f]
    refine sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < r <;> simp [hk, mul_comm]
  have h2 : v ⬝ᵥ w = ∑ k : Fin r, f k := by
    simp only [dotProduct, f]
    exact sum_congr rfl fun k _ => by simp [k.2]
  rw [h1, h2, Fin.sum_univ_eq_sum_range f s, Fin.sum_univ_eq_sum_range f r]
  symm
  refine sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun n _ hn => ?_
  simp only [mem_range] at hn
  simp [f, hn]

theorem embR_norm_sq {r s : ℕ} (hrs : r ≤ s) (v : Fin r → ℝ) : ‖embR s v‖ ^ 2 = v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq, embR_inner hrs]

theorem norm_le_of_sq_le {E : Type*} [NormedAddCommGroup E] {e : E} {B : ℝ} (hB : 0 ≤ B)
    (h : ‖e‖ ^ 2 ≤ B ^ 2) : ‖e‖ ≤ B := by
  nlinarith [norm_nonneg e]

/-- **The `γ₂` factorisation** (replaces John's theorem). -/
theorem john_factor_proved {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (s : ℕ) (hs1 : 1 ≤ s) (K : ℝ) (hK0 : 0 ≤ K)
    (hrank : rankOn N X Y ≤ s) (hK : ∀ x ∈ X, ∀ w ∈ Y, |N x w| ≤ K) :
    ∃ (u : α → EuclideanSpace ℝ (Fin s)) (v : β → EuclideanSpace ℝ (Fin s)),
      (∀ x ∈ X, ∀ w ∈ Y, N x w = inner ℝ (u x) (v w)) ∧
      (∀ x ∈ X, ‖u x‖ ≤ (s : ℝ) ^ (1 / 4 : ℝ)) ∧
      (∀ w ∈ Y, ‖v w‖ ≤ K * (s : ℝ) ^ (1 / 4 : ℝ)) := by
  classical
  obtain ⟨r, a, b, hr, hab, hspan⟩ := rank_factor N X Y
  have hrs : r ≤ s := hr ▸ hrank
  have hs4 : (0 : ℝ) ≤ (s : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · refine ⟨0, 0, fun x hx w hw => ?_, fun x _ => by simpa using hs4,
      fun w _ => by simpa using mul_nonneg hK0 hs4⟩
    have h := hab ⟨x, hx⟩ ⟨w, hw⟩
    subst hr0
    simp only [dotProduct, univ_eq_empty, sum_empty] at h
    simp [h]
  have : Nonempty X := by
    rcases isEmpty_or_nonempty X with h | h
    · exfalso
      have := hspan (fun _ => 1) (fun i => isEmptyElim i)
      have h1 := congrFun this ⟨0, hr1⟩
      simp at h1
    · exact h
  obtain ⟨lam, hlam0, hlam1, hMpd, hopt⟩ := kw_design a hr1 hspan
  obtain ⟨L, R, hLR, hRR, hLL⟩ := pd_factor _ hMpd
  set c : ℝ := (r : ℝ) ^ (1 / 4 : ℝ) with hc
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hcpos : 0 < c := Real.rpow_pos_of_pos hrpos _
  have hc2 : c ^ 2 = Real.sqrt r := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hrpos.le, Real.sqrt_eq_rpow]; norm_num
  have hcs : c ≤ (s : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hrpos.le (by exact_mod_cast hrs) (by norm_num)
  refine ⟨fun x => if hx : x ∈ X then c⁻¹ • embR s (L *ᵥ a ⟨x, hx⟩) else 0,
    fun w => if hw : w ∈ Y then c • embR s (R *ᵥ b ⟨w, hw⟩) else 0, ?_, ?_, ?_⟩
  · intro x hx w hw
    simp only [dif_pos hx, dif_pos hw, inner_smul_left, inner_smul_right, embR_inner hrs,
      dot_mulVec_mulVec, hLR, Matrix.one_mulVec, RCLike.conj_to_real]
    rw [hab ⟨x, hx⟩ ⟨w, hw⟩]
    field_simp
  · intro x hx
    simp only [dif_pos hx, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hcpos]
    have hq : ‖embR s (L *ᵥ a ⟨x, hx⟩)‖ ≤ Real.sqrt r := by
      refine norm_le_of_sq_le (Real.sqrt_nonneg _) ?_
      rw [embR_norm_sq hrs, dot_mulVec_mulVec, hLL, Real.sq_sqrt hrpos.le]
      exact hopt _
    calc c⁻¹ * ‖embR s (L *ᵥ a ⟨x, hx⟩)‖ ≤ c⁻¹ * Real.sqrt r :=
          mul_le_mul_of_nonneg_left hq (inv_nonneg.2 hcpos.le)
      _ = c := by rw [← hc2]; field_simp
      _ ≤ _ := hcs
  · intro w hw
    simp only [dif_pos hw, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    have hq : ‖embR s (R *ᵥ b ⟨w, hw⟩)‖ ≤ K := by
      refine norm_le_of_sq_le hK0 ?_
      rw [embR_norm_sq hrs, dot_mulVec_mulVec, hRR, designMat_quad]
      calc ∑ i, lam i * (a i ⬝ᵥ b ⟨w, hw⟩) * (a i ⬝ᵥ b ⟨w, hw⟩)
          ≤ ∑ i, lam i * K ^ 2 := by
            refine sum_le_sum fun i _ => ?_
            have hN := hK i.1 i.2 w hw
            rw [show N i w = a i ⬝ᵥ b ⟨w, hw⟩ from hab i ⟨w, hw⟩] at hN
            have : (a i ⬝ᵥ b ⟨w, hw⟩) * (a i ⬝ᵥ b ⟨w, hw⟩) ≤ K ^ 2 := by
              rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hN 2
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this (hlam0 i)
        _ = K ^ 2 := by rw [← sum_mul, hlam1, one_mul]
    calc c * ‖embR s (R *ᵥ b ⟨w, hw⟩)‖ ≤ c * K := mul_le_mul_of_nonneg_left hq hcpos.le
      _ = K * c := mul_comm _ _
      _ ≤ K * (s : ℝ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hcs hK0

end E1088
