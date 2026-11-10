import E1088.Main
import E1088.GL

/-!
# Rank of squared-distance matrices inside a set of affine dimension `≤ D`

For points of a finite set `X ⊆ ℝ^d` of affine dimension `≤ D`, the matrix
`[‖p_i - q_j‖² - f_i - g_j]` has rank `≤ D + 2` (the "lifted coordinates" `(|y|², y)` of DIM).
-/

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem rank_sqdist_le_affine {m n : Type*} [Fintype m] [Fintype n] (X : Finset (ℝ^d)) (D : ℕ)
    (hD : affDim X ≤ D) (p : m → ℝ^d) (q : n → ℝ^d) (hp : ∀ i, p i ∈ X) (hq : ∀ j, q j ∈ X)
    (f : m → ℝ) (g : n → ℝ) :
    (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j).rank ≤ D + 2 := by
  classical
  rcases X.eq_empty_or_nonempty with hX | ⟨x0, hx0⟩
  · -- no points: `m` or `n` is empty only if ... in fact `p i ∈ ∅` is impossible
    rcases isEmpty_or_nonempty m with hm | ⟨⟨i⟩⟩
    · exact (Matrix.rank_le_card_height _).trans (by simp)
    · exact absurd (hp i) (by simp [hX])
  set V := vectorSpan ℝ (X : Set (ℝ^d)) with hV
  set b := stdOrthonormalBasis ℝ V with hb
  set k := Module.finrank ℝ V with hk
  have hkD : k ≤ D := hD
  have hmem : ∀ y ∈ X, y - x0 ∈ V := fun y hy =>
    vsub_mem_vectorSpan ℝ (mem_coe.2 hy) (mem_coe.2 hx0)
  set a : m → V := fun i => ⟨p i - x0, hmem _ (hp i)⟩
  set c : n → V := fun j => ⟨q j - x0, hmem _ (hq j)⟩
  have hinner : ∀ i j, inner ℝ (p i - x0) (q j - x0) =
      ∑ t : Fin k, inner ℝ (a i) (b t) * inner ℝ (b t) (c j) := by
    intro i j
    rw [b.sum_inner_mul_inner (a i) (c j)]
    rfl
  have : (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j) =
      (Matrix.of fun i (t : Fin k ⊕ Fin 2) => Sum.elim (fun t => -2 * inner ℝ (a i) (b t))
        (fun t => if t = 0 then ‖p i - x0‖ ^ 2 - f i else 1) t) *
      (Matrix.of fun (t : Fin k ⊕ Fin 2) j => Sum.elim (fun t => inner ℝ (b t) (c j))
        (fun t => if t = 0 then 1 else ‖q j - x0‖ ^ 2 - g j) t) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Fin.sum_univ_two, Fin.isValue, if_true, one_ne_zero, if_false, mul_one,
      one_mul]
    have e : p i - q j = (p i - x0) - (q j - x0) := by abel
    rw [e, norm_sub_sq_real, hinner i j]
    have h2 : ∑ t : Fin k, -2 * inner ℝ (a i) (b t) * inner ℝ (b t) (c j) =
        -2 * ∑ t : Fin k, inner ℝ (a i) (b t) * inner ℝ (b t) (c j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h2]
    ring
  rw [this]
  exact (rank_mul_le_card _ _).trans (by simp; omega)

end E1088
