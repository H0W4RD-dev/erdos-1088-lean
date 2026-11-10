import E1088.Cut
import E1088.LemmaR

/-!
# Theorem LR, part 4: rescaling and one elimination round

* `rankOn_rescale` : `N = (M - φ - θ)/(qr qc)` has rank `≤ rank M + 2` (the rescaling step).
* `rankOn_prod_sub` : `∏_{t∈A} (M - τ_t)` has rank `≤ (rank M + 1)^{|A|}` (HP).
* `round_core` : Lemma R + (GL) remove the minority side.
-/

set_option linter.unusedSectionVars false

open Finset Matrix

namespace E1088

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

/-- Iterated (HP) over a finset of factors. -/
theorem rank_finset_prod_le {m n : Type*} [Fintype m] [Fintype n] (A : Finset ι)
    (F : ι → Matrix m n ℝ) :
    (Matrix.of fun i j => ∏ t ∈ A, F t i j).rank ≤ ∏ t ∈ A, (F t).rank := by
  induction A using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    have : (Matrix.of fun (_ : m) (_ : n) => (1 : ℝ)) = vecMulVec (fun _ => 1) (fun _ => 1) := by
      ext; simp [vecMulVec]
    rw [this]; exact rank_vecMulVec_le _ _
  | insert a A haA ih =>
    have : (Matrix.of fun i j => ∏ t ∈ insert a A, F t i j) =
        F a ⊙ Matrix.of fun i j => ∏ t ∈ A, F t i j := by
      ext i j; simp [prod_insert haA]
    rw [this, prod_insert haA]
    exact (rank_hadamard_le _ _).trans (Nat.mul_le_mul_left _ ih)

/-- A type function, as a matrix, has rank `≤ 1`. -/
theorem rank_tf_le {m n : Type*} [Fintype m] [Fintype n] (t : TF α β) (fx : m → α)
    (fw : n → β) : (Matrix.of fun i j => t.eval (fx i) (fw j)).rank ≤ 1 := by
  cases t with
  | row a =>
    have : (Matrix.of fun i j => (TF.row a : TF α β).eval (fx i) (fw j)) =
        vecMulVec (fun i => a (fx i)) (fun _ => 1) := by ext; simp [vecMulVec, TF.eval]
    rw [this]; exact rank_vecMulVec_le _ _
  | col b =>
    have : (Matrix.of fun i j => (TF.col b : TF α β).eval (fx i) (fw j)) =
        vecMulVec (fun _ => 1) (fun j => b (fw j)) := by ext; simp [vecMulVec, TF.eval]
    rw [this]; exact rank_vecMulVec_le _ _

theorem rank_neg_le {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    (-A).rank ≤ A.rank := by
  rw [show -A = (-1 : ℝ) • A by simp,
    rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero (by norm_num))]

/-- `M - τ_t` has rank `≤ rank M + 1`. -/
theorem rankOn_sub_tf (M : α → β → ℝ) (t : TF α β) (X : Finset α) (Y : Finset β) :
    rankOn (fun x w => M x w - t.eval x w) X Y ≤ rankOn M X Y + 1 := by
  unfold rankOn
  have : (Matrix.of fun (i : X) (j : Y) => M i j - t.eval i j) =
      (Matrix.of fun (i : X) (j : Y) => M i j) +
        -(Matrix.of fun (i : X) (j : Y) => t.eval i j) := by
    ext; simp [sub_eq_add_neg]
  rw [this]
  refine (rank_add_le' _ _).trans (Nat.add_le_add_left ?_ _)
  exact (rank_neg_le _).trans (rank_tf_le t (fun i : X => (i : α)) (fun j : Y => (j : β)))

/-- `∏_{t∈A} (M - τ_t)` has rank `≤ (rank M + 1)^{|A|}`. -/
theorem rankOn_prod_sub (M : α → β → ℝ) (τ : ι → TF α β) (A : Finset ι) (X : Finset α)
    (Y : Finset β) (r : ℕ) (hr : rankOn M X Y ≤ r) :
    rankOn (fun x w => ∏ t ∈ A, (M x w - (τ t).eval x w)) X Y ≤ (r + 1) ^ #A := by
  unfold rankOn
  have := rank_finset_prod_le A
    (fun t => Matrix.of fun (i : X) (j : Y) => M i j - (τ t).eval i j)
  refine this.trans ?_
  calc ∏ t ∈ A, (Matrix.of fun (i : X) (j : Y) => M i j - (τ t).eval i j).rank
      ≤ ∏ _t ∈ A, (r + 1) := prod_le_prod' fun t _ =>
        (rankOn_sub_tf M (τ t) X Y).trans (by unfold rankOn at hr ⊢; omega)
    _ = (r + 1) ^ #A := by simp

/-- **Rescaling step.** `N = (M - φ - θ) / (qr qc)` has rank `≤ rank M + 2`. -/
theorem rankOn_rescale (M : α → β → ℝ) (φ : α → ℝ) (θ : β → ℝ) (qr : α → ℝ) (qc : β → ℝ)
    (X : Finset α) (Y : Finset β) :
    rankOn (fun x w => (M x w - (φ x + θ w)) / (qr x * qc w)) X Y ≤ rankOn M X Y + 2 := by
  unfold rankOn
  have h1 : (Matrix.of fun (i : X) (j : Y) => (M i j - (φ i + θ j)) / (qr i * qc j)) =
      ((Matrix.of fun (i : X) (j : Y) => M i j) + vecMulVec (fun i : X => -φ i) (fun _ => 1) +
        vecMulVec (fun _ => 1) (fun j : Y => -θ j)) ⊙
        vecMulVec (fun i : X => 1 / qr i) (fun j : Y => 1 / qc j) := by
    ext i j
    simp only [of_apply, hadamard_apply, Matrix.add_apply, vecMulVec_apply, one_div,
      div_eq_mul_inv, mul_inv]
    ring
  rw [h1]
  refine (rank_hadamard_le _ _).trans ?_
  have h2 := rank_vecMulVec_le (fun i : X => 1 / qr i) (fun j : Y => 1 / qc j)
  have h3 := rank_add_le' ((Matrix.of fun (i : X) (j : Y) => M i j) +
    vecMulVec (fun i : X => -φ i) (fun _ => 1)) (vecMulVec (fun _ => 1) (fun j : Y => -θ j))
  have h4 := rank_add_le' (Matrix.of fun (i : X) (j : Y) => M i j)
    (vecMulVec (fun i : X => -φ i) (fun _ => 1))
  have h5 := rank_vecMulVec_le (fun i : X => -φ i) (fun _ : Y => (1 : ℝ))
  have h6 := rank_vecMulVec_le (fun _ : X => (1 : ℝ)) (fun j : Y => -θ j)
  calc _ ≤ (rank (Matrix.of fun (i : X) (j : Y) => M i j) + 2) * 1 :=
        Nat.mul_le_mul (by omega) h2
    _ = _ := by ring

end E1088
