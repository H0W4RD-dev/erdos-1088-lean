import Mathlib

/-!
# Rank tools: factorisation, sum and Hadamard-product bounds (tool HP), Lemma H

Elementary matrix-rank facts used throughout the Erdős #1088 proof.
* `rank_eq_factor` : a rank-`r` matrix factors through `Fin r`.
* `rank_hadamard_le` : (HP) `rank (A ⊙ B) ≤ rank A * rank B`.
* `rank_add_le'` : `rank (A + B) ≤ rank A + rank B`.
* `rank_sqdist_le` : `[‖p i - q j‖² - f i - g j]` has rank `≤ D + 2`.
* `card_le_rank_sq_of_kill` : Lemma H (symmetric one-sided kill form).
-/

open Matrix

namespace E1088

section Field

variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Rank factorisation: a matrix of rank `r` is `U * V` with inner dimension `r`. -/
theorem exists_factor (A : Matrix m n K) :
    ∃ (r : ℕ) (U : Matrix m (Fin r) K) (V : Matrix (Fin r) n K), r = A.rank ∧ A = U * V := by
  classical
  set S := Submodule.span K (Set.range A.col) with hS
  have hcol : ∀ j, A.col j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
  let b := Module.finBasis K S
  refine ⟨Module.finrank K S, Matrix.of fun i k => (b k : m → K) i,
    Matrix.of fun k j => b.repr ⟨A.col j, hcol j⟩ k, A.rank_eq_finrank_span_cols.symm, ?_⟩
  ext i j
  have h := congrArg (fun v : S => (v : m → K) i) (b.sum_repr ⟨A.col j, hcol j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  simp only [Matrix.mul_apply, Matrix.of_apply]
  change A.col j i = _
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

omit [Fintype m] in
/-- A product through an inner index type `k` has rank at most `card k`. -/
theorem rank_mul_le_card {k : Type*} [Fintype k] (U : Matrix m k K) (V : Matrix k n K) :
    (U * V).rank ≤ Fintype.card k :=
  (rank_mul_le_left U V).trans (rank_le_card_width U)

/-- Rank does not increase under arbitrary row/column reindexing (submatrices, repetitions). -/
theorem rank_submatrix_le' {m' n' : Type*} [Fintype m'] [Fintype n'] (A : Matrix m n K)
    (f : m' → m) (g : n' → n) : (A.submatrix f g).rank ≤ A.rank := by
  obtain ⟨r, U, V, hr, rfl⟩ := exists_factor A
  have : (U * V).submatrix f g = U.submatrix f id * V.submatrix id g := by
    ext i j; simp [Matrix.mul_apply]
  rw [this, hr.symm]
  exact (rank_mul_le_card _ _).trans_eq (by simp)

/-- (HP) Rank of a Hadamard product. -/
theorem rank_hadamard_le (A B : Matrix m n K) : (A ⊙ B).rank ≤ A.rank * B.rank := by
  obtain ⟨r, U, V, hr, rfl⟩ := exists_factor A
  obtain ⟨s, U', V', hs, hB⟩ := exists_factor B
  rw [← hr, ← hs]
  have : (U * V) ⊙ B = (Matrix.of fun i (p : Fin r × Fin s) => U i p.1 * U' i p.2) *
      (Matrix.of fun (p : Fin r × Fin s) j => V p.1 j * V' p.2 j) := by
    ext i j
    rw [hB]
    simp only [hadamard_apply, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact (rank_mul_le_card _ _).trans_eq (by simp)

/-- Subadditivity of rank. -/
theorem rank_add_le' (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  obtain ⟨r, U, V, hr, rfl⟩ := exists_factor A
  obtain ⟨s, U', V', hs, hB⟩ := exists_factor B
  rw [← hr, ← hs]
  have : U * V + B = (Matrix.of fun i (p : Fin r ⊕ Fin s) => Sum.elim (U i) (U' i) p) *
      (Matrix.of fun (p : Fin r ⊕ Fin s) j => Sum.elim (fun k => V k j) (fun k => V' k j) p) := by
    ext i j
    rw [hB]
    simp [Matrix.mul_apply, Fintype.sum_sum_type]
  rw [this]
  exact (rank_mul_le_card _ _).trans_eq (by simp)

/-- Iterated (HP): the entrywise product of `e` matrices. -/
theorem rank_prod_le (e : ℕ) (M : Fin e → Matrix m n K) :
    (Matrix.of fun i j => ∏ k, M k i j).rank ≤ ∏ k, (M k).rank := by
  induction e with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have : (Matrix.of fun (_ : m) (_ : n) => (1 : K)) = vecMulVec (fun _ => 1) (fun _ => 1) := by
      ext; simp [vecMulVec]
    rw [this]; exact rank_vecMulVec_le _ _
  | succ e ih =>
    have : (Matrix.of fun i j => ∏ k : Fin (e + 1), M k i j) =
        M 0 ⊙ Matrix.of fun i j => ∏ k : Fin e, M k.succ i j := by
      ext i j; simp [Fin.prod_univ_succ]
    rw [this, Fin.prod_univ_succ]
    exact (rank_hadamard_le _ _).trans (Nat.mul_le_mul_left _ (ih _))

/-- Lemma H (symmetric form, matrix version). If `F i i ≠ 0` and for every `i ≠ j` one of
`F i j`, `F j i` vanishes, then the number of indices is at most `rank F ^ 2`. -/
theorem card_le_rank_sq_of_kill [DecidableEq m] (F : Matrix m m K) (hdiag : ∀ i, F i i ≠ 0)
    (hkill : ∀ i j, i ≠ j → F i j = 0 ∨ F j i = 0) : Fintype.card m ≤ F.rank ^ 2 := by
  classical
  have hD : F ⊙ Fᵀ = diagonal fun i => F i i * F i i := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rcases hkill i j h with h' | h' <;> simp [h, h']
  have h1 : (F ⊙ Fᵀ).rank = Fintype.card m := by
    rw [hD, rank_diagonal]
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun i => mul_ne_zero (hdiag i) (hdiag i))
  have h2 := rank_hadamard_le F Fᵀ
  rw [h1, rank_transpose] at h2
  simpa [sq] using h2

end Field

section Geometry

variable {m n : Type*} [Fintype m] [Fintype n] {D : ℕ}

omit [Fintype m] in
/-- The matrix `[‖p i - q j‖² - f i - g j]` has rank at most `D + 2`
(row functions `f`, column functions `g`). -/
theorem rank_sqdist_le (p : m → EuclideanSpace ℝ (Fin D)) (q : n → EuclideanSpace ℝ (Fin D))
    (f : m → ℝ) (g : n → ℝ) :
    (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j).rank ≤ D + 2 := by
  have : (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j) =
      (Matrix.of fun i (k : Fin D ⊕ Fin 2) =>
        Sum.elim (fun k => -2 * p i k) (fun t => if t = 0 then ‖p i‖ ^ 2 - f i else 1) k) *
      (Matrix.of fun (k : Fin D ⊕ Fin 2) j =>
        Sum.elim (fun k => q j k) (fun t => if t = 0 then 1 else ‖q j‖ ^ 2 - g j) k) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Fin.sum_univ_two]
    rw [@norm_sub_sq_real, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, if_true, if_false, one_ne_zero, mul_one, one_mul]
    have : ∑ x, -2 * (p i).ofLp x * (q j).ofLp x = -(2 * ∑ x, (q j).ofLp x * (p i).ofLp x) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this]; ring
  rw [this]
  exact (rank_mul_le_card _ _).trans_eq (by simp)

/-- Kill-polynomial form of Lemma H in `ℝ^D`: if each point `i` has a "kill function"
`y ↦ ∏_{k<e} (‖p i - y‖² - f k i - g k y)` not vanishing at `p i`, and every pair is killed
from at least one side, then there are at most `(D+2)^(2e)` points. -/
theorem card_le_of_kill [DecidableEq m] (p : m → EuclideanSpace ℝ (Fin D)) (e : ℕ)
    (f : Fin e → m → ℝ) (g : Fin e → m → ℝ)
    (hdiag : ∀ i, ∏ k, (‖p i - p i‖ ^ 2 - f k i - g k i) ≠ 0)
    (hkill : ∀ i j, i ≠ j → ∏ k, (‖p i - p j‖ ^ 2 - f k i - g k j) = 0 ∨
      ∏ k, (‖p j - p i‖ ^ 2 - f k j - g k i) = 0) :
    Fintype.card m ≤ (D + 2) ^ (2 * e) := by
  set F : Matrix m m ℝ := Matrix.of fun i j => ∏ k, (‖p i - p j‖ ^ 2 - f k i - g k j)
  have hF : F.rank ≤ (D + 2) ^ e := by
    have := rank_prod_le e (fun k => Matrix.of fun i j => ‖p i - p j‖ ^ 2 - f k i - g k j)
    refine this.trans ?_
    calc ∏ k : Fin e, (Matrix.of fun i j => ‖p i - p j‖ ^ 2 - f k i - g k j).rank
        ≤ ∏ _k : Fin e, (D + 2) := Finset.prod_le_prod' fun k _ => rank_sqdist_le _ _ _ _
      _ = (D + 2) ^ e := by simp
  have := card_le_rank_sq_of_kill F hdiag hkill
  calc Fintype.card m ≤ F.rank ^ 2 := this
    _ ≤ ((D + 2) ^ e) ^ 2 := Nat.pow_le_pow_left hF 2
    _ = (D + 2) ^ (2 * e) := by ring

end Geometry

end E1088
