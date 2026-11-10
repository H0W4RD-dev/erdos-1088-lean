import Mathlib

/-!
# König's theorem (finite bipartite graphs), vertex-cover form

Bipartite graph: left vertices `L : Finset α`, neighbourhoods `N a : Finset β`.
A *matching* is a finite set `M` of edges `(a, b)` (`a ∈ L`, `b ∈ N a`) no two of which share an
endpoint. If every matching has fewer than `m` edges, there is a vertex cover `A ∪ B`
(`A ⊆ L`, every edge `(a, b)` with `a ∉ A` has `b ∈ B`) with `|A| + |B| < m`.
Used in the Slicing Lemma (manuscript Lemma 9.1(a)).

Proof: deficiency version of Hall's theorem, from Mathlib's
`Finset.all_card_le_biUnion_card_iff_exists_injective`, by adding `d` dummy right vertices,
where `d` is the maximal deficiency `|S| - |N(S)|`.
-/

open Finset

namespace E1088

/-- **König's theorem**, vertex-cover form. -/
theorem konig_cover {α β : Type*} [DecidableEq α] [DecidableEq β] (L : Finset α)
    (N : α → Finset β) (m : ℕ)
    (hno : ∀ M : Finset (α × β), (∀ p ∈ M, p.1 ∈ L ∧ p.2 ∈ N p.1) →
      (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 ∨ p.2 = q.2 → p = q) → M.card < m) :
    ∃ A ⊆ L, ∃ B : Finset β, (∀ a ∈ L, a ∉ A → N a ⊆ B) ∧ A.card + B.card < m := by
  classical
  have hm : 0 < m := hno ∅ (by simp) (by simp)
  by_cases hβ : Nonempty β
  swap
  · exact ⟨∅, empty_subset _, ∅, fun a _ _ b _ => (hβ ⟨b⟩).elim, by simpa using hm⟩
  obtain ⟨b0⟩ := hβ
  -- maximal deficiency
  obtain ⟨S, hS, hmax⟩ := exists_max_image L.powerset
    (fun S => (S.card : ℤ) - (S.biUnion N).card) ⟨∅, empty_mem_powerset _⟩
  rw [mem_powerset] at hS
  set d : ℤ := (S.card : ℤ) - (S.biUnion N).card with hd
  have hd0 : 0 ≤ d := by
    have := hmax ∅ (empty_mem_powerset _); simpa using this
  set d' := d.toNat with hd'
  have hdd : (d' : ℤ) = d := Int.toNat_of_nonneg hd0
  -- Hall with `d'` dummy vertices
  let t : {a // a ∈ L} → Finset (β ⊕ Fin d') := fun a => (N a.1).disjSum Finset.univ
  have hHall : ∀ s : Finset {a // a ∈ L}, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
    · simp
    set s' := s.map (Function.Embedding.subtype _) with hs'
    have hs'L : s' ⊆ L := by
      intro a ha; obtain ⟨x, -, rfl⟩ := mem_map.1 ha; exact x.2
    have hsub : (s'.biUnion N).disjSum (Finset.univ : Finset (Fin d')) ⊆ s.biUnion t := by
      intro z hz
      rcases z with b | i
      · rw [inl_mem_disjSum, mem_biUnion] at hz
        obtain ⟨a, ha, hb⟩ := hz
        obtain ⟨x, hx, rfl⟩ := mem_map.1 ha
        exact mem_biUnion.2 ⟨x, hx, inl_mem_disjSum.2 hb⟩
      · exact mem_biUnion.2 ⟨a0, ha0, inr_mem_disjSum.2 (mem_univ _)⟩
    have h1 := card_le_card hsub
    rw [card_disjSum, card_univ, Fintype.card_fin] at h1
    have h2 := hmax s' (mem_powerset.2 hs'L)
    have h3 : s'.card = s.card := card_map _
    have : (s.card : ℤ) ≤ (s'.biUnion N).card + d' := by rw [hdd]; omega
    omega
  obtain ⟨f, hfinj, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  -- the matching
  set Ll := (Finset.univ : Finset {a // a ∈ L}).filter fun a => (f a).isLeft with hLl
  set Lr := (Finset.univ : Finset {a // a ∈ L}).filter fun a => ¬ (f a).isLeft with hLr
  let g : {a // a ∈ L} → β := fun a => Sum.elim id (fun _ => b0) (f a)
  have hgL : ∀ a ∈ Ll, f a = Sum.inl (g a) := by
    intro a ha
    have := (mem_filter.1 ha).2
    simp only [g]
    rcases h : f a with b | i
    · rfl
    · rw [h] at this; simp at this
  set M := Ll.image fun a => (a.1, g a) with hM
  have hMprop : ∀ p ∈ M, p.1 ∈ L ∧ p.2 ∈ N p.1 := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    refine ⟨a.2, ?_⟩
    have := hft a
    rw [hgL a ha] at this
    exact inl_mem_disjSum.1 this
  have hMinj : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 ∨ p.2 = q.2 → p = q := by
    intro p hp q hq h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨a', ha', rfl⟩ := mem_image.1 hq
    rcases h with h | h
    · have : a = a' := Subtype.ext h
      rw [this]
    · have : f a = f a' := by rw [hgL a ha, hgL a' ha']; simp only at h; rw [h]
      rw [hfinj this]
  have hMcard : M.card = Ll.card :=
    card_image_of_injective _ (fun a a' h => Subtype.ext (Prod.ext_iff.1 h).1)
  have hLrcard : Lr.card ≤ d' := by
    have hmaps : ∀ a ∈ Lr, f a ∈ (Finset.univ : Finset (Fin d')).map Function.Embedding.inr := by
      intro a ha
      have := (mem_filter.1 ha).2
      rcases h : f a with b | i
      · rw [h] at this; simp at this
      · exact mem_map.2 ⟨i, mem_univ _, rfl⟩
    have := card_le_card_of_injOn f hmaps (fun x _ y _ h => hfinj h)
    simpa using this
  have hsplit : Ll.card + Lr.card = L.card := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_coe]
  have hMlt := hno M hMprop hMinj
  -- the cover
  refine ⟨L \ S, sdiff_subset, S.biUnion N, ?_, ?_⟩
  · intro a ha haA
    have haS : a ∈ S := by
      by_contra h; exact haA (mem_sdiff.2 ⟨ha, h⟩)
    exact subset_biUnion_of_mem N haS
  · rw [card_sdiff_of_subset hS]
    have hSL := card_le_card hS
    have : ((L.card - S.card + (S.biUnion N).card : ℕ) : ℤ) = L.card - d := by
      push_cast [Nat.cast_sub hSL]; rw [hd]; ring
    have h4 : (L.card : ℤ) - d < m := by rw [← hdd]; omega
    omega

end E1088
