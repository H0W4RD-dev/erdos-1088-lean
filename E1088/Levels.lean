import E1088.AffRank
import E1088.KillStep
import E1088.Round

/-!
# Levels and configurations; Lemma 1.2 of round14 (kill step at level r)

Definitions follow round14/general_n_full_proof.md Part 1 ("Setting", "Definition (level-j
configuration)", `R_b`, `Big_b`, `Claim(j)`), for a finite point set `X ⊆ ℝ^d` of affine dimension
`≤ D`.

`lemma_1_2` is proved in full from `Claim(r+1)` (a hypothesis, as in the paper), the kill step
(Lemma H + Caro–Wei) and the rank bound for squared-distance matrices.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- All values `δ a a'` on pairs of distinct points of `A` are distinct (abstract form). -/
def RainbowF {P : Type*} (δ : P → P → ℝ) (A : Finset P) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, ∀ c ∈ A, ∀ c' ∈ A, a ≠ a' → c ≠ c' → δ a a' = δ c c' →
    (a = c ∧ a' = c') ∨ (a = c' ∧ a' = c)

/-- All pairwise distances of `A` are distinct ("rainbow"). -/
abbrev Rainbow (A : Finset (ℝ^d)) : Prop := RainbowF dist A

/-- The set `D_A` of distances of `A`. -/
noncomputable def dists (A : Finset (ℝ^d)) : Finset ℝ := A.offDiag.image fun p => dist p.1 p.2

local macro "memtac" : tactic => `(tactic| first
  | exact mem_insert_self _ _
  | exact mem_insert_of_mem (by assumption)
  | exact mem_insert_of_mem (mem_insert_self _ _)
  | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))

set_option maxHeartbeats 3000000 in
/-- Rainbow test for `S ∪ {b, x}`, for an abstract symmetric `δ` (the case analysis of round14
Lemma 1.1 / Lemma 1.2). Stated abstractly so that the case split never unfolds `dist`. -/
theorem rainbowF_insert_insert {P : Type*} [DecidableEq P] (δ : P → P → ℝ)
    (hcomm : ∀ u v, δ u v = δ v u) (S : Finset P) (b x : P)
    (hbS : RainbowF δ (insert b S)) (hxS : RainbowF δ (insert x S))
    (hcross : ∀ s ∈ S, ∀ s' ∈ S, δ x s ≠ δ b s')
    (h1 : ∀ s ∈ S, δ x b ≠ δ b s) (h2 : ∀ s ∈ S, δ x b ≠ δ x s)
    (h3 : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → δ x b ≠ δ s s') :
    RainbowF δ (insert x (insert b S)) := by
  have C : ∀ s s', δ x s = δ b s' → s ∈ S → s' ∈ S → False :=
    fun s s' h hs hs' => hcross s hs s' hs' h
  have E1 : ∀ s, δ x b = δ b s → s ∈ S → False := fun s h hs => h1 s hs h
  have E2 : ∀ s, δ x b = δ x s → s ∈ S → False := fun s h hs => h2 s hs h
  have E3 : ∀ s s', δ x b = δ s s' → s ∈ S → s' ∈ S → s ≠ s' → False :=
    fun s s' h hs hs' hne => h3 s hs s' hs' hne h
  intro a ha a' ha' c hc c' hc' hne hne' hd
  have hd1 : δ a a' = δ c c' := hd
  have hd2 : δ c c' = δ a a' := hd.symm
  have hd3 : δ a' a = δ c c' := by rw [hcomm]; exact hd
  have hd4 : δ a a' = δ c' c := by rw [hcomm c']; exact hd
  have hd5 : δ a' a = δ c' c := by rw [hcomm a', hcomm c']; exact hd
  have hd6 : δ c c' = δ a' a := by rw [hcomm a']; exact hd.symm
  have hd7 : δ c' c = δ a a' := by rw [hcomm]; exact hd.symm
  have hd8 : δ c' c = δ a' a := by rw [hcomm c', hcomm a']; exact hd.symm
  simp only [mem_insert] at ha ha' hc hc'
  rcases ha with rfl | rfl | ha <;> rcases ha' with rfl | rfl | ha' <;>
    rcases hc with rfl | rfl | hc <;> rcases hc' with rfl | rfl | hc' <;>
  first
    | exact absurd rfl hne
    | exact absurd rfl hne'
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩
    | exact hxS _ (by memtac) _ (by memtac) _ (by memtac) _ (by memtac) hne hne' hd
    | exact hbS _ (by memtac) _ (by memtac) _ (by memtac) _ (by memtac) hne hne' hd
    | exact (C _ _ hd1 (by assumption) (by assumption)).elim
    | exact (E1 _ hd1 (by assumption)).elim
    | exact (E2 _ hd1 (by assumption)).elim
    | exact (E3 _ _ hd1 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd1 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd2 (by assumption) (by assumption)).elim
    | exact (E1 _ hd2 (by assumption)).elim
    | exact (E2 _ hd2 (by assumption)).elim
    | exact (E3 _ _ hd2 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd2 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd3 (by assumption) (by assumption)).elim
    | exact (E1 _ hd3 (by assumption)).elim
    | exact (E2 _ hd3 (by assumption)).elim
    | exact (E3 _ _ hd3 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd3 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd4 (by assumption) (by assumption)).elim
    | exact (E1 _ hd4 (by assumption)).elim
    | exact (E2 _ hd4 (by assumption)).elim
    | exact (E3 _ _ hd4 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd4 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd5 (by assumption) (by assumption)).elim
    | exact (E1 _ hd5 (by assumption)).elim
    | exact (E2 _ hd5 (by assumption)).elim
    | exact (E3 _ _ hd5 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd5 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd6 (by assumption) (by assumption)).elim
    | exact (E1 _ hd6 (by assumption)).elim
    | exact (E2 _ hd6 (by assumption)).elim
    | exact (E3 _ _ hd6 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd6 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd7 (by assumption) (by assumption)).elim
    | exact (E1 _ hd7 (by assumption)).elim
    | exact (E2 _ hd7 (by assumption)).elim
    | exact (E3 _ _ hd7 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd7 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd8 (by assumption) (by assumption)).elim
    | exact (E1 _ hd8 (by assumption)).elim
    | exact (E2 _ hd8 (by assumption)).elim
    | exact (E3 _ _ hd8 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd8 (by assumption) (by assumption) (Ne.symm (by assumption))).elim

/-- Rainbow test for `S ∪ {b, x}` in `ℝ^d`. -/
theorem rainbow_insert_insert (S : Finset (ℝ^d)) (b x : ℝ^d)
    (hbS : Rainbow (insert b S)) (hxS : Rainbow (insert x S))
    (hcross : ∀ s ∈ S, ∀ s' ∈ S, dist x s ≠ dist b s')
    (h1 : ∀ s ∈ S, dist x b ≠ dist b s) (h2 : ∀ s ∈ S, dist x b ≠ dist x s)
    (h3 : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → dist x b ≠ dist s s') :
    Rainbow (insert x (insert b S)) :=
  rainbowF_insert_insert dist dist_comm S b x hbS hxS hcross h1 h2 h3

end E1088
