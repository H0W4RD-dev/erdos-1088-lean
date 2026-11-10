import E1088.Cover
import E1088.Konig
import E1088.E1Proof

/-!
# Slicing Lemma, part 1: label conflicts (step (c)) and basic facts about rainbow families
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- **Step (c)**: out-degree `≤ 1` conflicts; Caro–Wei gives `K` conflict-free indices out of
`3K`. -/
theorem conflict_free (I1 : Finset ℕ) (K : ℕ) (hI1 : I1.card = 3 * K) (lam : ℕ → ℝ)
    (lab : ℕ → Finset ℝ) (hout : ∀ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ lam k ∈ lab k').card ≤ 1) :
    ∃ I' ⊆ I1, I'.card = K ∧ ∀ k ∈ I', ∀ k' ∈ I', k ≠ k' → lam k ∉ lab k' := by
  classical
  let R : ℕ → ℕ → Prop := fun k k' => lam k ∈ lab k'
  let G : SimpleGraph ℕ := SimpleGraph.fromRel R
  obtain ⟨T, hTI, hind, hcw⟩ := caro_wei G I1
  -- degree sum
  have hdeg : ∀ k ∈ I1, degIn G I1 k ≤ (I1.filter fun k' => k' ≠ k ∧ R k k').card +
      (I1.filter fun k' => k' ≠ k ∧ R k' k).card := by
    intro k _
    unfold degIn
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro k' hk'
    obtain ⟨hk'I, hadj⟩ := mem_filter.1 hk'
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hk'I, hadj.1.symm, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hk'I, hadj.1.symm, h⟩)
  have hsum2 : ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k' k).card ≤ I1.card := by
    have : ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k' k).card =
        ∑ k' ∈ I1, (I1.filter fun k => k' ≠ k ∧ R k' k).card := by
      simp only [card_filter]; exact Finset.sum_comm
    rw [this]
    calc ∑ k' ∈ I1, (I1.filter fun k => k' ≠ k ∧ R k' k).card
        ≤ ∑ _k' ∈ I1, 1 := sum_le_sum fun k' hk' => by
          have := hout k' hk'
          refine le_trans (card_le_card fun k hk => ?_) this
          obtain ⟨hkI, hne, hR⟩ := mem_filter.1 hk
          exact mem_filter.2 ⟨hkI, Ne.symm hne, hR⟩
      _ = I1.card := by simp
  have hsum : ∑ k ∈ I1, ((degIn G I1 k : ℝ) + 1) ≤ 3 * I1.card := by
    have h1 : ∑ k ∈ I1, degIn G I1 k ≤ 2 * I1.card := by
      calc ∑ k ∈ I1, degIn G I1 k
          ≤ ∑ k ∈ I1, ((I1.filter fun k' => k' ≠ k ∧ R k k').card +
              (I1.filter fun k' => k' ≠ k ∧ R k' k).card) := sum_le_sum hdeg
        _ = ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k k').card +
            ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k' k).card := sum_add_distrib
        _ ≤ I1.card + I1.card := by
            refine Nat.add_le_add ?_ hsum2
            calc ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k k').card
                ≤ ∑ _k ∈ I1, 1 := sum_le_sum hout
              _ = I1.card := by simp
        _ = 2 * I1.card := by ring
    have h2 : (∑ k ∈ I1, degIn G I1 k : ℝ) ≤ 2 * I1.card := by exact_mod_cast h1
    rw [sum_add_distrib]; push_cast at h2 ⊢
    simp only [sum_const, nsmul_eq_mul, mul_one]
    linarith
  have hT : K ≤ T.card := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · omega
    have hIpos : (0 : ℝ) < I1.card := by rw [hI1]; push_cast; positivity
    have h1 : ((I1.card : ℝ)) ^ 2 ≤ T.card * (3 * I1.card) :=
      hcw.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    have h2 : (I1.card : ℝ) ≤ 3 * T.card := by nlinarith
    have h3 : (3 * K : ℝ) ≤ 3 * T.card := by rw [hI1] at h2; push_cast at h2; exact h2
    have : (K : ℝ) ≤ T.card := by linarith
    exact_mod_cast this
  obtain ⟨I', hI'T, hI'c⟩ := exists_subset_card_eq hT
  refine ⟨I', hI'T.trans hTI, hI'c, fun k hk k' hk' hne hR => ?_⟩
  exact hind (hI'T hk) (hI'T hk') hne ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl hR⟩)

/-- Classes of a rainbow family are pairwise disjoint. -/
theorem family_classes_disjoint {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {k k' : ℕ} (hk : k ∈ I) (hk' : k' ∈ I)
    (hne : k ≠ k') {x : ℝ^d} (hx : x ∈ C k) : x ∉ C k' := by
  intro hx'
  obtain ⟨b, hb⟩ := hF.Bne
  have h1 := hF.F2 k hk x hx b hb
  have h2 := hF.F2 k' hk' x hx' b hb
  exact hne (hF.F3.1 k hk k' hk' b hb b hb (h1.symm.trans h2)).1

/-- Spheres about the points of `S` with radii in a finite set `T0` of positive reals carry fewer
than `|S| |T0| σ` points of `W` (cap condition). -/
theorem removal_bound {X S W : Finset (ℝ^d)} {r : ℕ} {σ : ℝ} (hc : Config X S W r σ)
    (T0 : Finset ℝ) (hT0 : ∀ t ∈ T0, 0 < t) :
    ((S.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ) ≤ r * (T0.card * σ) := by
  classical
  have hsub : (S.biUnion fun s => W.filter fun x => dist x s ∈ T0) ⊆
      S.biUnion fun s => T0.biUnion fun t => W.filter fun x => dist x s = t := by
    intro x hx
    obtain ⟨s, hs, hx⟩ := mem_biUnion.1 hx
    obtain ⟨hxW, ht⟩ := mem_filter.1 hx
    exact mem_biUnion.2 ⟨s, hs, mem_biUnion.2 ⟨_, ht, mem_filter.2 ⟨hxW, rfl⟩⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∀ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) ≤
      T0.card * σ := by
    intro s hs
    have := card_biUnion_le (s := T0) (t := fun t => W.filter fun x => dist x s = t)
    calc ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ)
        ≤ ∑ t ∈ T0, ((W.filter fun x => dist x s = t).card : ℝ) := by exact_mod_cast this
      _ ≤ ∑ _t ∈ T0, σ := sum_le_sum fun t ht => (hc.cap s hs t (hT0 t ht)).le
      _ = T0.card * σ := by rw [sum_const, nsmul_eq_mul]
  calc ((S.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ)
      ≤ ∑ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ _s ∈ S, (T0.card * σ) := sum_le_sum h2
    _ = r * (T0.card * σ) := by rw [sum_const, nsmul_eq_mul, hc.card]

end E1088
