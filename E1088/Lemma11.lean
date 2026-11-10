import E1088.Lemma12

/-!
# round14 Lemma 1.1 / manuscript Lemma 6.4 (HR_r, the hereditary relative bound)

Assume `Claim(r+1)` with constant `Γ`. Let `(S, W, σ)` be a level-`r` configuration, `σ ≥ σ_min`,
`c ∈ W`, `V ⊆ W \ {c}`, `θ ≥ σ`. Then the points `x ∈ V` with `|xc| ∉ R_c`, `x` off every bisector
`H(c, s)`, and `|V ∩ S(c, |xc|)| < θ` number at most `(Γ + r²) θ`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- The set controlled by HR. -/
noncomputable def hrSet (S V : Finset (ℝ^d)) (c : ℝ^d) (θ : ℝ) : Finset (ℝ^d) :=
  V.filter fun x => dist x c ∉ Rb S c ∧ (∀ s ∈ S, dist x c ≠ dist x s) ∧
    ((V.filter fun y => dist y c = dist x c).card : ℝ) < θ

/-- The conclusion of HR_r for a configuration, with constant `Γ'`. -/
def HRholds (S W : Finset (ℝ^d)) (σ Γ' : ℝ) : Prop :=
  ∀ c ∈ W, ∀ V ⊆ W.erase c, ∀ θ : ℝ, σ ≤ θ → ((hrSet S V c θ).card : ℝ) ≤ Γ' * θ

/-- **Lemma 1.1 (HR_r).** -/
theorem lemma_HR (X : Finset (ℝ^d)) (r : ℕ) (Γ σmin σ : ℝ)
    (hclaim : ClaimAt X (r + 1) Γ σmin) (S W : Finset (ℝ^d)) (hc : Config X S W r σ)
    (hσpos : 0 < σ) (hσ : σmin ≤ σ) : HRholds S W σ (Γ + r ^ 2) := by
  classical
  intro c hcW V hV θ hθ
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hVW : V ⊆ W := hV.trans (erase_subset _ _)
  set V0 := hrSet S V c θ
  set Cls := (S ×ˢ S).biUnion fun q => W.filter fun x => dist x q.1 = dist c q.2
  set V1 := V0.filter fun x => x ∉ Cls
  have hV0 : V0 ⊆ Cls ∪ V1 := by
    intro x hx
    by_cases h : x ∈ Cls
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_filter.2 ⟨hx, h⟩)
  have hCls : (Cls.card : ℝ) ≤ r ^ 2 * θ := by
    have h1 : Cls.card ≤ ∑ q ∈ S ×ˢ S, (W.filter fun x => dist x q.1 = dist c q.2).card :=
      card_biUnion_le
    have h2 : ∀ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist c q.2).card : ℝ) ≤ θ := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := mem_product.1 hq
      have hpos : 0 < dist c q.2 := dist_pos.2 fun e => hWS c hcW (e ▸ hq2)
      exact (hc.cap q.1 hq1 _ hpos).le.trans hθ
    calc (Cls.card : ℝ) ≤ ∑ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist c q.2).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ _q ∈ S ×ˢ S, θ := sum_le_sum h2
      _ = r ^ 2 * θ := by rw [sum_const, card_product, hc.card, nsmul_eq_mul]; push_cast; ring
  -- `(S ∪ {c}, V1, θ)` is a level-(r+1) configuration
  have hconf : Config X (insert c S) V1 (r + 1) θ := by
    refine ⟨insert_subset (hc.subW hcW) hc.subX, hc.ext c hcW, ?_, ?_, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem (hWS c hcW), hc.card]
    · intro x hx
      exact hc.subW (hVW (mem_filter.1 (mem_filter.1 hx).1).1)
    · rw [disjoint_left]
      intro x hx hxi
      have hxV : x ∈ V := (mem_filter.1 (mem_filter.1 hx).1).1
      have hxc : x ≠ c := (mem_erase.1 (hV hxV)).1
      rcases mem_insert.1 hxi with h | h
      · exact hxc h
      · exact hWS x (hVW hxV) h
    · intro x hx
      obtain ⟨hx0, hxC⟩ := mem_filter.1 hx
      obtain ⟨hxV, hR, hbis, -⟩ := mem_filter.1 hx0
      have hxW := hVW hxV
      have hxc : x ≠ c := (mem_erase.1 (hV hxV)).1
      refine rainbow_insert_insert S c x (hc.ext c hcW) (hc.ext x hxW) ?_ ?_ ?_ ?_
      · intro s hs s' hs' h
        exact hxC (mem_biUnion.2 ⟨(s, s'), mem_product.2 ⟨hs, hs'⟩, mem_filter.2 ⟨hxW, h⟩⟩)
      · intro s hs h
        exact hR (mem_union_right _ (mem_image.2 ⟨s, hs, h.symm⟩))
      · intro s hs h; exact hbis s hs h
      · intro s hs s' hs' hne h
        exact hR (mem_union_left _ (h ▸ mem_dists hs hs' hne))
    · intro s hs t ht
      have hsub : V1 ⊆ V := fun x hx => (mem_filter.1 (mem_filter.1 hx).1).1
      rcases mem_insert.1 hs with rfl | hsS
      · by_cases hne : (V1.filter fun x => dist x s = t).Nonempty
        · obtain ⟨x0, hx0⟩ := hne
          obtain ⟨hx0V1, hx0t⟩ := mem_filter.1 hx0
          have hlt := (mem_filter.1 (mem_filter.1 hx0V1).1).2.2.2
          rw [hx0t] at hlt
          calc ((V1.filter fun x => dist x s = t).card : ℝ)
              ≤ ((V.filter fun x => dist x s = t).card : ℝ) := by
                exact_mod_cast card_le_card (filter_subset_filter _ hsub)
            _ < θ := hlt
        · rw [not_nonempty_iff_eq_empty] at hne
          rw [hne, card_empty, Nat.cast_zero]; linarith
      · calc ((V1.filter fun x => dist x s = t).card : ℝ)
            ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
              exact_mod_cast card_le_card (filter_subset_filter _ (hsub.trans hVW))
          _ < σ := hc.cap s hsS t ht
          _ ≤ θ := hθ
  have hV1 : (V1.card : ℝ) ≤ Γ * θ := hclaim _ _ θ hconf (hσ.trans hθ)
  have h1 : V0.card ≤ Cls.card + V1.card := (card_le_card hV0).trans (card_union_le _ _)
  have : (V0.card : ℝ) ≤ Cls.card + V1.card := by exact_mod_cast h1
  linarith

end E1088
