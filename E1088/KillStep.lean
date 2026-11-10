import E1088.GL
import E1088.CaroWei

/-!
# The kill step (core of round12/01 Theorem R and round14 Lemma 1.2)

Each point `b` has a kill function `F b ·` with `F b b ≠ 0`; the matrix `F` has rank `≤ m` on `W`;
and for each `b` at most `Δ` other points `x ∈ W` survive (`F b x ≠ 0`). Then
`|W| ≤ m² (Δ + 1)`: the graph of pairs unkilled from both sides has maximum degree `≤ Δ`,
Caro–Wei gives an independent set `I` with `|W| ≤ |I| (Δ+1)`, and on `I` every pair is killed
from one side, so Lemma H gives `|I| ≤ m²`.

`kill_bound_geometric` is the instance used in the paper: kill functions
`y ↦ ∏_{k<e} (‖p b - y‖² - f_k(b) - g_k(y))` (spheres about `b`, bisectors, …), rank `≤ (D+2)^e`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace E1088

variable {ι : Type*} [DecidableEq ι]

/-- **Kill step** (abstract form). -/
theorem kill_bound (W : Finset ι) (F : ι → ι → ℝ) (m Δ : ℕ) (hrank : rankOn F W W ≤ m)
    (hdiag : ∀ b ∈ W, F b b ≠ 0)
    (hsurv : ∀ b ∈ W, #(W.filter fun x => x ≠ b ∧ F b x ≠ 0) ≤ Δ) :
    #W ≤ m ^ 2 * (Δ + 1) := by
  classical
  -- the graph of pairs unkilled from both sides
  let G : SimpleGraph ι := SimpleGraph.fromRel fun a b => F a b ≠ 0 ∧ F b a ≠ 0
  have hdeg : ∀ b ∈ W, degIn G W b ≤ Δ := by
    intro b hb
    refine (card_le_card fun x hx => ?_).trans (hsurv b hb)
    obtain ⟨hxW, hadj⟩ := mem_filter.1 hx
    rw [SimpleGraph.fromRel_adj] at hadj
    refine mem_filter.2 ⟨hxW, hadj.1.symm, ?_⟩
    rcases hadj.2 with h | h
    · exact h.1
    · exact h.2
  obtain ⟨I, hIW, hind, hcw⟩ := caro_wei G W
  -- `|W| ≤ |I| (Δ + 1)`
  have h1 : (#W : ℝ) ≤ #I * (Δ + 1) := by
    rcases W.eq_empty_or_nonempty with hW | hW
    · simp only [hW, card_empty, Nat.cast_zero]; positivity
    have hsum : ∑ v ∈ W, ((degIn G W v : ℝ) + 1) ≤ #W * ((Δ : ℝ) + 1) := by
      calc ∑ v ∈ W, ((degIn G W v : ℝ) + 1) ≤ ∑ _v ∈ W, ((Δ : ℝ) + 1) :=
            sum_le_sum fun v hv => by have := hdeg v hv; push_cast; exact_mod_cast
              (show degIn G W v + 1 ≤ Δ + 1 by omega)
        _ = #W * ((Δ : ℝ) + 1) := by rw [sum_const, nsmul_eq_mul]
    have hWpos : (0 : ℝ) < #W := by exact_mod_cast card_pos.2 hW
    have : (#W : ℝ) ^ 2 ≤ #I * (#W * ((Δ : ℝ) + 1)) :=
      hcw.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    nlinarith
  -- Lemma H on `I`
  have h2 : #I ≤ m ^ 2 := by
    have hH := card_le_rank_sq_of_kill (Matrix.of fun (i : I) (j : I) => F i j)
      (fun i => hdiag i (hIW i.2)) (fun i j hij => by
        by_contra h
        push Not at h
        have hne : (i : ι) ≠ j := fun e => hij (Subtype.ext e)
        exact hind i.2 j.2 hne ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨h.1, h.2⟩⟩))
    have hr : (Matrix.of fun (i : I) (j : I) => F i j).rank ≤ m :=
      (rankOn_mono F hIW hIW).trans hrank
    simp only [Fintype.card_coe] at hH
    exact hH.trans (Nat.pow_le_pow_left hr 2)
  have h3 : ((#I : ℕ) : ℝ) ≤ (m ^ 2 : ℕ) := by exact_mod_cast h2
  have : (#W : ℝ) ≤ (m ^ 2 : ℕ) * ((Δ : ℝ) + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  exact_mod_cast this

open scoped EuclideanGeometry

/-- **Kill step, geometric form.** Kill functions are products of `e` factors
`‖p b - y‖² - f_k(b) - g_k(y)`. -/
theorem kill_bound_geometric {D : ℕ} (W : Finset ι) (p : ι → EuclideanSpace ℝ (Fin D)) (e Δ : ℕ)
    (f g : Fin e → ι → ℝ)
    (hdiag : ∀ b ∈ W, ∏ k, (‖p b - p b‖ ^ 2 - f k b - g k b) ≠ 0)
    (hsurv : ∀ b ∈ W, #(W.filter fun x => x ≠ b ∧
      ∏ k, (‖p b - p x‖ ^ 2 - f k b - g k x) ≠ 0) ≤ Δ) :
    #W ≤ ((D + 2) ^ e) ^ 2 * (Δ + 1) := by
  refine kill_bound W (fun b x => ∏ k, (‖p b - p x‖ ^ 2 - f k b - g k x)) ((D + 2) ^ e) Δ ?_
    hdiag hsurv
  unfold rankOn
  have := rank_prod_le e (fun k => Matrix.of fun (i : W) (j : W) =>
    ‖p i - p j‖ ^ 2 - f k i - g k j)
  refine this.trans ?_
  calc ∏ k : Fin e, (Matrix.of fun (i : W) (j : W) => ‖p i - p j‖ ^ 2 - f k i - g k j).rank
      ≤ ∏ _k : Fin e, (D + 2) := Finset.prod_le_prod' fun k _ =>
        rank_sqdist_le (fun i : W => p i) (fun j : W => p j) (fun i : W => f k i)
          (fun j : W => g k j)
    _ = (D + 2) ^ e := by simp

end E1088
