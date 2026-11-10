import E1088.Slicing1

/-!
# Slicing Lemma, part 2: the new family (step (d))
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem union_insert_eq (S B : Finset (ℝ^d)) (c : ℝ^d) : S ∪ insert c B = insert c (S ∪ B) := by
  ext x; simp only [mem_union, mem_insert]; tauto

/-- **Step (d)**: the new family `B ∪ {c}`. -/
theorem new_family (X S W B : Finset (ℝ^d)) (r : ℕ) (σ : ℝ) (hc : Config X S W r σ)
    (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (hF : RainbowFamily S W B I C β)
    (π : ℕ) (hπ : π ∈ I) (c : ℝ^d) (hcπ : c ∈ C π) (I' : Finset ℕ) (hI' : I' ⊆ I.erase π)
    (lam : ℕ → ℝ) (hinj : ∀ k ∈ I', ∀ k' ∈ I', lam k = lam k' → k = k')
    (hΦ : ∀ k ∈ I', lam k ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c))
    (hβk : ∀ k ∈ I', lam k ∉ B.image (β k))
    (hindep : ∀ k ∈ I', ∀ k' ∈ I', k ≠ k' → lam k ∉ B.image (β k'))
    (hpos : ∀ k ∈ I', 0 < lam k)
    (hlarge : ∀ k ∈ I', (r : ℝ) * (r + I'.card) * σ <
      ((C k).filter fun x => dist x c = lam k).card) :
    ∃ (C' : ℕ → Finset (ℝ^d)) (β' : ℕ → ℝ^d → ℝ), RainbowFamily S W (insert c B) I' C' β' ∧
      (∀ k ∈ I', C' k ⊆ C k) ∧ ∀ k ∈ I',
        (((C k).filter fun x => dist x c = lam k).card : ℝ) - r * (r + I'.card) * σ ≤ (C' k).card := by
  classical
  have hI'I : ∀ k ∈ I', k ∈ I := fun k hk => (mem_erase.1 (hI' hk)).2
  have hI'π : ∀ k ∈ I', k ≠ π := fun k hk => (mem_erase.1 (hI' hk)).1
  obtain ⟨hcSB, hcR⟩ := hF.F4 π hπ c hcπ
  have hcS : c ∉ S := fun h => hcSB (mem_union_left _ h)
  have hcB : c ∉ B := fun h => hcSB (mem_union_right _ h)
  set T0 := S.image (dist c) ∪ I'.image lam with hT0
  set Rem := S.biUnion fun s => W.filter fun x => dist x s ∈ T0 with hRem
  let C' : ℕ → Finset (ℝ^d) := fun k => ((C k).filter fun x => dist x c = lam k) \ Rem
  let β' : ℕ → ℝ^d → ℝ := fun k b => if b = c then lam k else β k b
  have hT0pos : ∀ t ∈ T0, 0 < t := by
    intro t ht
    rcases mem_union.1 ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := mem_image.1 ht; exact dist_pos.2 fun h => hcS (h ▸ hs)
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 ht; exact hpos k hk
  have hT0c : (T0.card : ℝ) ≤ r + I'.card := by
    have h1 := card_union_le (S.image (dist c)) (I'.image lam)
    have h2 := card_image_le (s := S) (f := dist c)
    have h3 := card_image_le (s := I') (f := lam)
    rw [hc.card] at h2
    have : T0.card ≤ r + I'.card := by rw [hT0]; omega
    exact_mod_cast this
  have hRemc : (Rem.card : ℝ) ≤ r * (r + I'.card) * σ := by
    by_cases hS : S.Nonempty
    · obtain ⟨s, hs⟩ := hS
      have hσ0 : 0 ≤ σ := le_trans (Nat.cast_nonneg _) (hc.cap s hs 1 one_pos).le
      calc (Rem.card : ℝ) ≤ r * (T0.card * σ) := removal_bound hc T0 hT0pos
        _ ≤ r * ((r + I'.card) * σ) := by gcongr
        _ = r * (r + I'.card) * σ := by ring
    · have hSe : S = ∅ := not_nonempty_iff_eq_empty.1 hS
      have hr0 : r = 0 := by have := hc.card; rw [hSe, card_empty] at this; omega
      have : Rem = ∅ := by rw [hRem, hSe, biUnion_empty]
      rw [this, card_empty, hr0]; simp
  have hC'card : ∀ k ∈ I', (((C k).filter fun x => dist x c = lam k).card : ℝ) -
      r * (r + I'.card) * σ ≤ (C' k).card := by
    intro k _
    have h1 := card_le_card_sdiff_add_card (s := (C k).filter fun x => dist x c = lam k) (t := Rem)
    have h2 : ((((C k).filter fun x => dist x c = lam k).card : ℕ) : ℝ) ≤ (C' k).card + Rem.card := by
      exact_mod_cast h1
    linarith
  -- distances from `c` to `S ∪ B` lie in `Φ(c)`
  have hcdist : ∀ y ∈ S ∪ B, dist c y ∈ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) := by
    intro y hy
    rcases mem_union.1 hy with hy | hy
    · exact mem_union_right _ (mem_image.2 ⟨y, hy, rfl⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_image.2 ⟨y, hy, (hF.F2 π hπ c hcπ y hy).symm⟩))
  have hβπ : ∀ k ∈ I', ∀ b ∈ B, ∀ b' ∈ B, β k b ≠ β π b' := fun k hk b hb b' hb' h =>
    hI'π k hk (hF.F3.1 k (hI'I k hk) π hπ b hb b' hb' h).1
  refine ⟨C', β', ⟨insert_nonempty _ _, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩,
    fun k _ x hx => (mem_filter.1 (mem_sdiff.1 hx).1).1, hC'card⟩
  · -- F1
    rw [disjoint_insert_right]; exact ⟨hcS, hF.F1.1⟩
  · rw [union_insert_eq]; exact hcR
  · -- classes nonempty, inside `W`
    intro k hk
    refine ⟨?_, fun x hx => (hF.Cne k (hI'I k hk)).2 (mem_filter.1 (mem_sdiff.1 hx).1).1⟩
    rw [← card_pos]
    have := hC'card k hk; have := hlarge k hk
    have : (0 : ℝ) < (C' k).card := by linarith
    exact_mod_cast this
  · -- F2
    intro k hk x hx b hb
    obtain ⟨hxf, -⟩ := mem_sdiff.1 hx
    obtain ⟨hxC, hxc⟩ := mem_filter.1 hxf
    rcases mem_insert.1 hb with hbc | hb
    · simp only [β', if_pos hbc]; rw [hbc]; exact hxc
    · have hbc : b ≠ c := fun h => hcB (h ▸ hb)
      simp only [β', if_neg hbc]; exact hF.F2 k (hI'I k hk) x hxC b hb
  · -- F3 (a)
    intro k hk k' hk' b hb b' hb' h
    rcases mem_insert.1 hb with hbc | hb <;> rcases mem_insert.1 hb' with hb'c | hb'
    · simp only [β', if_pos hbc, if_pos hb'c] at h
      exact ⟨hinj k hk k' hk' h, hbc.trans hb'c.symm⟩
    · have hb'ne : b' ≠ c := fun e => hcB (e ▸ hb')
      simp only [β', if_pos hbc, if_neg hb'ne] at h
      by_cases hkk : k = k'
      · subst hkk; exact absurd (mem_image.2 ⟨b', hb', h.symm⟩) (hβk k hk)
      · exact absurd (mem_image.2 ⟨b', hb', h.symm⟩) (hindep k hk k' hk' hkk)
    · have hbne : b ≠ c := fun e => hcB (e ▸ hb)
      simp only [β', if_pos hb'c, if_neg hbne] at h
      by_cases hkk : k' = k
      · subst hkk; exact absurd (mem_image.2 ⟨b, hb, h⟩) (hβk k' hk')
      · exact absurd (mem_image.2 ⟨b, hb, h⟩) (hindep k' hk' k hk hkk)
    · have hbc : b ≠ c := fun e => hcB (e ▸ hb)
      have hb'c : b' ≠ c := fun e => hcB (e ▸ hb')
      simp only [β', if_neg hbc, if_neg hb'c] at h
      exact hF.F3.1 k (hI'I k hk) k' (hI'I k' hk') b hb b' hb' h
  · -- F3 (b)
    intro k hk b hb hmem
    rw [union_insert_eq] at hmem
    have hmem' := dists_insert_subset (S ∪ B) c hmem
    rcases mem_insert.1 hb with hbc | hb
    · simp only [β', if_pos hbc] at hmem'
      rcases mem_union.1 hmem' with h | h
      · exact hΦ k hk (mem_union_left _ (mem_union_left _ h))
      · obtain ⟨y, hy, hye⟩ := mem_image.1 h
        exact hΦ k hk (hye ▸ hcdist y hy)
    · have hbc : b ≠ c := fun e => hcB (e ▸ hb)
      simp only [β', if_neg hbc] at hmem'
      rcases mem_union.1 hmem' with h | h
      · exact hF.F3.2 k (hI'I k hk) b hb h
      · obtain ⟨y, hy, hye⟩ := mem_image.1 h
        rcases mem_union.1 hy with hy | hy
        · exact hF.F5 π hπ c hcπ y hy k (hI'I k hk) b hb hye
        · rw [hF.F2 π hπ c hcπ y hy] at hye
          exact hβπ k hk b hb y hy hye.symm
  · -- F4
    intro k hk x hx
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    obtain ⟨hxC, hxc⟩ := mem_filter.1 hxf
    obtain ⟨hxSB, hxRb⟩ := hF.F4 k (hI'I k hk) x hxC
    have hxcne : x ≠ c := fun e =>
      family_classes_disjoint hF (hI'I k hk) hπ (hI'π k hk) hxC (e ▸ hcπ)
    have hnot : ∀ s ∈ S, dist x s ∉ T0 := fun s hs ht =>
      hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF.Cne k (hI'I k hk)).2 hxC, ht⟩⟩)
    refine ⟨?_, ?_⟩
    · rw [union_insert_eq]
      intro hmem
      rcases mem_insert.1 hmem with h | h
      · exact hxcne h
      · exact hxSB h
    · rw [union_insert_eq]
      refine rainbow_insert_insert (S ∪ B) c x hcR hxRb ?_ ?_ ?_ ?_
      · intro y hy y' hy' h
        rcases mem_union.1 hy with hy | hy <;> rcases mem_union.1 hy' with hy' | hy'
        · exact hnot y hy (mem_union_left _ (mem_image.2 ⟨y', hy', h.symm⟩))
        · rw [hF.F2 π hπ c hcπ y' hy'] at h
          exact hF.F5 k (hI'I k hk) x hxC y hy π hπ y' hy' h
        · rw [hF.F2 k (hI'I k hk) x hxC y hy] at h
          exact hF.F5 π hπ c hcπ y' hy' k (hI'I k hk) y hy h.symm
        · rw [hF.F2 k (hI'I k hk) x hxC y hy, hF.F2 π hπ c hcπ y' hy'] at h
          exact hβπ k hk y hy y' hy' h
      · intro y hy h
        rw [hxc] at h
        exact hΦ k hk (h ▸ hcdist y hy)
      · intro y hy h
        rw [hxc] at h
        rcases mem_union.1 hy with hy | hy
        · exact hnot y hy (mem_union_right _ (mem_image.2 ⟨k, hk, h⟩))
        · rw [hF.F2 k (hI'I k hk) x hxC y hy] at h
          exact hβk k hk (mem_image.2 ⟨y, hy, h.symm⟩)
      · intro y hy y' hy' hne h
        rw [hxc] at h
        exact hΦ k hk (mem_union_left _ (mem_union_left _ (h ▸ mem_dists hy hy' hne)))
  · -- F5
    intro k hk x hx s hs k' hk' b hb
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    obtain ⟨hxC, -⟩ := mem_filter.1 hxf
    rcases mem_insert.1 hb with hbc | hb
    · simp only [β', if_pos hbc]
      intro h
      exact hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF.Cne k (hI'I k hk)).2 hxC,
        mem_union_right _ (mem_image.2 ⟨k', hk', h.symm⟩)⟩⟩)
    · have hbc : b ≠ c := fun e => hcB (e ▸ hb)
      simp only [β', if_neg hbc]
      exact hF.F5 k (hI'I k hk) x hxC s hs k' (hI'I k' hk') b hb

end E1088
