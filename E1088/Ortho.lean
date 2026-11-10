import E1088.Main

/-!
# Orthogonal splits (tool OR of round11/n4_full_proof Sec. 1)

If `⟨x - x', w - w'⟩ = 0` for all `x, x' ∈ R`, `w, w' ∈ C`, then the direction spaces of
`aff R` and `aff C` are orthogonal subspaces of the direction space of `aff (R ∪ C)`, so
`dim R + dim C ≤ dim (R ∪ C)` and `min (dim R) (dim C) ≤ ⌊dim (R ∪ C) / 2⌋`.
Two sufficient conditions used in the paper: every `w ∈ C` is equidistant from `R`, or `R` lies in
the perpendicular bisector `H(p, w)` for every `w ∈ C` (fixed `p`).
-/

open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem affDim_add_le_of_ortho [DecidableEq (ℝ^d)] (R C : Finset (ℝ^d))
    (h : ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0) :
    affDim R + affDim C ≤ affDim (R ∪ C) := by
  unfold affDim
  set U := vectorSpan ℝ (R : Set (ℝ^d))
  set W := vectorSpan ℝ (C : Set (ℝ^d))
  have hUW : U ⟂ W := by
    simp only [U, W, vectorSpan_def]
    rw [Submodule.isOrtho_span]
    rintro u ⟨x, hx, x', hx', rfl⟩ v ⟨w, hw, w', hw', rfl⟩
    exact h x hx x' hx' w hw w' hw'
  have hdisj : U ⊓ W = ⊥ := hUW.disjoint.eq_bot
  have hsup : U ⊔ W ≤ vectorSpan ℝ ((R ∪ C : Finset (ℝ^d)) : Set (ℝ^d)) := by
    apply sup_le
    · exact vectorSpan_mono ℝ (by simp)
    · exact vectorSpan_mono ℝ (by simp)
  have := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hdisj, finrank_bot, add_zero] at this
  rw [← this]
  exact Submodule.finrank_mono hsup

/-- **Orthogonal split.** -/
theorem min_affDim_le_of_ortho [DecidableEq (ℝ^d)] (R C : Finset (ℝ^d)) (D : ℕ)
    (hD : affDim (R ∪ C) ≤ D)
    (h : ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0) :
    min (affDim R) (affDim C) ≤ D / 2 := by
  have := affDim_add_le_of_ortho R C h
  omega

/-- Equidistance gives orthogonality. -/
theorem ortho_of_equidistant (R C : Finset (ℝ^d)) (ρ : ℝ^d → ℝ)
    (h : ∀ x ∈ R, ∀ w ∈ C, ‖x - w‖ = ρ w) :
    ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0 := by
  intro x hx x' hx' w hw w' hw'
  have e1 : ‖x - w‖ ^ 2 = ‖x' - w‖ ^ 2 := by rw [h x hx w hw, h x' hx' w hw]
  have e2 : ‖x - w'‖ ^ 2 = ‖x' - w'‖ ^ 2 := by rw [h x hx w' hw', h x' hx' w' hw']
  rw [norm_sub_sq_real, norm_sub_sq_real] at e1 e2
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

/-- Lying on all bisectors `H(p, w)` gives orthogonality. -/
theorem ortho_of_bisector (R C : Finset (ℝ^d)) (p : ℝ^d)
    (h : ∀ x ∈ R, ∀ w ∈ C, ‖x - p‖ = ‖x - w‖) :
    ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0 := by
  intro x hx x' hx' w hw w' hw'
  have e : ∀ z ∈ R, ∀ v ∈ C, 2 * inner ℝ z (v - p) = ‖v‖ ^ 2 - ‖p‖ ^ 2 := by
    intro z hz v hv
    have := congrArg (· ^ 2) (h z hz v hv)
    rw [norm_sub_sq_real, norm_sub_sq_real] at this
    rw [inner_sub_right]; linarith
  have a1 := e x hx w hw
  have a2 := e x' hx' w hw
  have a3 := e x hx w' hw'
  have a4 := e x' hx' w' hw'
  rw [inner_sub_right] at a1 a2 a3 a4
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

end E1088
