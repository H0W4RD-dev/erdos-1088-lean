import E1088.Levels

/-!
# round14 Lemma 1.2 (kill step at level `r`, case `B_K`)

Assume `Claim(r+1)`. Let `(S, W, σ)` be a level-`r` configuration with `σ ≥ σ_min`, `τ ≥ σ`, and
`|Big_b(τ)| ≤ K` for every `b ∈ W`. Then `|W| ≤ P (Γ_{r+1} τ + r² σ + 1)` with
`P = ((D+2)^e)^2`, `e = K + 2r + |D_S|`.

(The paper states `|W| ≤ C(D+1+e,e)^2 (2Γ_{r+1}τ + 2r²σ + 1)` with `e = K + 2r + C(r,2)`; our
bound is of the same shape: `C(D+1+e, e)` is replaced by `(D+2)^e` (rank form of DIM) and the
factors 2 are not needed. `|D_S| ≤ C(r,2)`.)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- Level-`j` configuration `(S, W, σ)` inside `X` (round14, Part 1). -/
structure Config (X S W : Finset (ℝ^d)) (j : ℕ) (σ : ℝ) : Prop where
  subX : S ⊆ X
  rainbow : Rainbow S
  card : S.card = j
  subW : W ⊆ X
  disj : Disjoint W S
  ext : ∀ x ∈ W, Rainbow (insert x S)
  cap : ∀ s ∈ S, ∀ t : ℝ, 0 < t → ((W.filter fun x => dist x s = t).card : ℝ) < σ

/-- `R_b = D_S ∪ {|bs| : s ∈ S}`. -/
noncomputable def Rb (S : Finset (ℝ^d)) (b : ℝ^d) : Finset ℝ := dists S ∪ S.image (dist b)

/-- `Big_b(τ)`: radii `λ ∉ R_b` of spheres about `b` meeting `W` in at least `τ` points. -/
noncomputable def Big (S W : Finset (ℝ^d)) (b : ℝ^d) (τ : ℝ) : Finset ℝ :=
  ((W.erase b).image fun x => dist x b).filter fun l =>
    l ∉ Rb S b ∧ τ ≤ ((W.filter fun x => dist x b = l).card : ℝ)

/-- `Claim(j)` with constant `Γ` above the threshold `σ_min`. -/
def ClaimAt (X : Finset (ℝ^d)) (j : ℕ) (Γ σmin : ℝ) : Prop :=
  ∀ S W : Finset (ℝ^d), ∀ σ : ℝ, Config X S W j σ → σmin ≤ σ → (W.card : ℝ) ≤ Γ * σ

theorem mem_dists {A : Finset (ℝ^d)} {a a' : ℝ^d} (ha : a ∈ A) (ha' : a' ∈ A) (h : a ≠ a') :
    dist a a' ∈ dists A :=
  mem_image.2 ⟨(a, a'), mem_offDiag.2 ⟨ha, ha', h⟩, rfl⟩

theorem pos_of_mem_dists {A : Finset (ℝ^d)} {t : ℝ} (h : t ∈ dists A) : 0 < t := by
  obtain ⟨p, hp, rfl⟩ := mem_image.1 h
  exact dist_pos.2 (mem_offDiag.1 hp).2.2

theorem sq_ne_of_ne {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≠ b ^ 2) : a ≠ b := by
  rintro rfl; exact h rfl

theorem ne_of_sq_sub_ne {a b : ℝ} (h : a ^ 2 - b ^ 2 ≠ 0) : a ≠ b := by
  rintro rfl; simp at h

/-- **Lemma 1.2** (round14 Part 1). -/
theorem lemma_1_2 (X : Finset (ℝ^d)) (D : ℕ) (hD : affDim X ≤ D) (r K : ℕ) (Γ σmin σ τ : ℝ)
    (hclaim : ClaimAt X (r + 1) Γ σmin) (S W : Finset (ℝ^d)) (hc : Config X S W r σ)
    (hΓ : 0 ≤ Γ) (hσpos : 0 < σ) (hσ : σmin ≤ σ) (hτ : σ ≤ τ) (hbig : ∀ b ∈ W, (Big S W b τ).card ≤ K) :
    (W.card : ℝ) ≤ (((D + 2) ^ (K + 2 * r + (dists S).card)) ^ 2 : ℕ) *
      (Γ * τ + r ^ 2 * σ + 1) := by
  classical
  -- factor index type
  let J := Fin K ⊕ (S ⊕ (S ⊕ dists S))
  have hJ : Fintype.card J = K + 2 * r + (dists S).card := by
    simp only [J, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hc.card]; ring
  -- the enumerated big radii
  let lam : ℝ^d → Fin K → ℝ := fun b i =>
    if h : (i : ℕ) < (Big S W b τ).card then ((Big S W b τ).equivFin.symm ⟨i, h⟩ : ℝ) else 0
  let f : J → ℝ^d → ℝ := fun k b => match k with
    | Sum.inl i => if (i : ℕ) < (Big S W b τ).card then lam b i ^ 2 else -1
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl s)) => dist b s ^ 2
    | Sum.inr (Sum.inr (Sum.inr δ)) => (δ : ℝ) ^ 2
  let g : J → ℝ^d → ℝ := fun k y => match k with
    | Sum.inr (Sum.inl s) => ‖y - s‖ ^ 2
    | _ => 0
  let F : ℝ^d → ℝ^d → ℝ := fun b y => ∏ k : J, (‖b - y‖ ^ 2 - f k b - g k y)
  -- facts about the big radii
  have hlam_mem : ∀ b (i : Fin K) (h : (i : ℕ) < (Big S W b τ).card), lam b i ∈ Big S W b τ := by
    intro b i h; simp only [lam, dif_pos h]; exact Finset.coe_mem _
  have hlam_surj : ∀ b ∈ W, ∀ l ∈ Big S W b τ, ∃ i : Fin K, (i : ℕ) < (Big S W b τ).card ∧
      lam b i = l := by
    intro b hb l hl
    set j := (Big S W b τ).equivFin ⟨l, hl⟩
    refine ⟨⟨j, lt_of_lt_of_le j.2 (hbig b hb)⟩, j.2, ?_⟩
    simp only [lam, dif_pos j.2]
    simp [j]
  have hBig_pos : ∀ b l, l ∈ Big S W b τ → 0 < l := by
    intro b l hl
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 hl).1
    exact dist_pos.2 (ne_of_mem_erase hx)
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hWX : ∀ x ∈ W, x ∈ X := fun x hx => hc.subW hx
  -- apply the kill step
  set Δ := ⌊Γ * τ + r ^ 2 * σ⌋₊ with hΔ
  have hrank : rankOn F W W ≤ (D + 2) ^ (K + 2 * r + (dists S).card) := by
    unfold rankOn
    have h1 := rank_finset_prod_le (Finset.univ : Finset J) (fun k => Matrix.of fun (i : W) (j : W) =>
      ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j)
    refine h1.trans ?_
    calc ∏ k ∈ (Finset.univ : Finset J), (Matrix.of fun (i : W) (j : W) =>
          ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j).rank
        ≤ ∏ _k ∈ (Finset.univ : Finset J), (D + 2) := Finset.prod_le_prod' fun k _ =>
          rank_sqdist_le_affine X D hD (fun i : W => (i : ℝ^d)) (fun j : W => (j : ℝ^d))
            (fun i => hWX _ i.2) (fun j => hWX _ j.2) _ _
      _ = (D + 2) ^ (K + 2 * r + (dists S).card) := by
          rw [Finset.prod_const, Finset.card_univ, hJ]
  have hdiag : ∀ b ∈ W, F b b ≠ 0 := by
    intro b hb
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_sub]
    rcases k with i | s | s | δ
    · simp only [f, g]
      split_ifs with h
      · have := hBig_pos b _ (hlam_mem b i h)
        intro h0; nlinarith
      · norm_num
    · simp only [f, g, neg_zero, zero_sub, neg_ne_zero]
      have : b ≠ (s : ℝ^d) := fun e => hWS b hb (e ▸ s.2)
      have := norm_pos_iff.2 (sub_ne_zero.2 this)
      positivity
    · simp only [f, g, sub_zero, neg_ne_zero]
      have : b ≠ (s : ℝ^d) := fun e => hWS b hb (e ▸ s.2)
      have := dist_pos.2 this; positivity
    · simp only [f, g, sub_zero, neg_ne_zero]
      have := pos_of_mem_dists δ.2; positivity
  have hsurv : ∀ b ∈ W, #(W.filter fun x => x ≠ b ∧ F b x ≠ 0) ≤ Δ := by
    intro b hb
    set Sv := W.filter fun x => x ≠ b ∧ F b x ≠ 0
    set Cls := (S ×ˢ S).biUnion fun q => W.filter fun x => dist x q.1 = dist b q.2
    set W' := (W.erase b).filter fun x =>
      Rainbow (insert x (insert b S)) ∧ dist x b ∉ Big S W b τ
    -- survivors are in `Cls ∪ W'`
    have hsub : Sv ⊆ Cls ∪ W' := by
      intro x hx
      obtain ⟨hxW, hxb, hF⟩ := mem_filter.1 hx
      have hfac : ∀ k : J, ‖b - x‖ ^ 2 - f k b - g k x ≠ 0 := fun k =>
        Finset.prod_ne_zero_iff.1 hF k (Finset.mem_univ _)
      have hbx : ‖b - x‖ = dist x b := by rw [← dist_eq_norm, dist_comm]
      by_cases hcl : x ∈ Cls
      · exact mem_union_left _ hcl
      refine mem_union_right _ (mem_filter.2 ⟨mem_erase.2 ⟨hxb, hxW⟩, ?_, ?_⟩)
      · refine rainbow_insert_insert S b x (hc.ext b hb) (hc.ext x hxW) ?_ ?_ ?_ ?_
        · intro s hs s' hs' h
          exact hcl (mem_biUnion.2 ⟨(s, s'), mem_product.2 ⟨hs, hs'⟩, mem_filter.2 ⟨hxW, h⟩⟩)
        · intro s hs h
          have := hfac (Sum.inr (Sum.inr (Sum.inl ⟨s, hs⟩)))
          simp only [f, g, sub_zero] at this
          rw [hbx] at this
          exact ne_of_sq_sub_ne this h
        · intro s hs h
          have := hfac (Sum.inr (Sum.inl ⟨s, hs⟩))
          simp only [f, g, sub_zero] at this
          rw [hbx, ← dist_eq_norm] at this
          exact ne_of_sq_sub_ne this h
        · intro s hs s' hs' hne h
          have := hfac (Sum.inr (Sum.inr (Sum.inr ⟨dist s s', mem_dists hs hs' hne⟩)))
          simp only [f, g, sub_zero] at this
          rw [hbx] at this
          exact ne_of_sq_sub_ne this h
      · intro hl
        obtain ⟨i, hi, hli⟩ := hlam_surj b hb _ hl
        have := hfac (Sum.inl i)
        simp only [f, g, sub_zero, if_pos hi] at this
        rw [hbx, hli] at this
        exact this (by ring)
    -- the classes of `S` are small
    have hCls : (#Cls : ℝ) ≤ r ^ 2 * σ := by
      have h1 : #Cls ≤ ∑ q ∈ S ×ˢ S, #(W.filter fun x => dist x q.1 = dist b q.2) :=
        card_biUnion_le
      have h2 : ∀ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) ≤ σ := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := mem_product.1 hq
        have hpos : 0 < dist b q.2 := dist_pos.2 fun e => hWS b hb (e ▸ hq2)
        exact (hc.cap q.1 hq1 _ hpos).le
      calc (#Cls : ℝ) ≤ ∑ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) := by
            exact_mod_cast h1
        _ ≤ ∑ _q ∈ S ×ˢ S, σ := sum_le_sum h2
        _ = r ^ 2 * σ := by rw [sum_const, card_product, hc.card, nsmul_eq_mul]; push_cast; ring
    -- `W'` is a level-(r+1) configuration
    have hconf' : Config X (insert b S) W' (r + 1) τ := by
      refine ⟨insert_subset (hWX b hb) hc.subX, hc.ext b hb, ?_, ?_, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem (hWS b hb), hc.card]
      · exact (filter_subset _ _).trans ((erase_subset _ _).trans hc.subW)
      · rw [disjoint_left]
        intro x hx hxi
        obtain ⟨hxe, -⟩ := mem_filter.1 hx
        rcases mem_insert.1 hxi with rfl | hxS
        · exact (mem_erase.1 hxe).1 rfl
        · exact hWS x (mem_erase.1 hxe).2 hxS
      · intro x hx; exact (mem_filter.1 hx).2.1
      · intro s hs t ht
        have hsubW : W' ⊆ W := (filter_subset _ _).trans (erase_subset _ _)
        rcases mem_insert.1 hs with rfl | hsS
        · -- the new centre `s = b`
          by_cases hne : (W'.filter fun x => dist x s = t).Nonempty
          · obtain ⟨x0, hx0⟩ := hne
            obtain ⟨hx0W', hx0t⟩ := mem_filter.1 hx0
            obtain ⟨hx0e, hrb, hnb⟩ := mem_filter.1 hx0W'
            have hx0W := (mem_erase.1 hx0e).2
            have hx0b := (mem_erase.1 hx0e).1
            have himg : t ∈ (W.erase s).image fun x => dist x s :=
              mem_image.2 ⟨x0, hx0e, hx0t⟩
            have hnotR : t ∉ Rb S s := by
              intro hR
              rcases mem_union.1 hR with hR | hR
              · obtain ⟨q, hq, hqt⟩ := mem_image.1 hR
                obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
                have := hrb x0 (mem_insert_self _ _) s (mem_insert_of_mem (mem_insert_self _ _))
                  q.1 (mem_insert_of_mem (mem_insert_of_mem hq1)) q.2
                  (mem_insert_of_mem (mem_insert_of_mem hq2)) hx0b hq12 (by rw [hx0t, hqt])
                rcases this with ⟨h1, -⟩ | ⟨h1, -⟩
                · exact hWS x0 hx0W (h1 ▸ hq1)
                · exact hWS x0 hx0W (h1 ▸ hq2)
              · obtain ⟨q, hq, hqt⟩ := mem_image.1 hR
                have hsq : s ≠ q := fun e => hWS s hb (e ▸ hq)
                have := hrb x0 (mem_insert_self _ _) s (mem_insert_of_mem (mem_insert_self _ _))
                  s (mem_insert_of_mem (mem_insert_self _ _)) q
                  (mem_insert_of_mem (mem_insert_of_mem hq)) hx0b hsq (by rw [hx0t, hqt])
                rcases this with ⟨h1, -⟩ | ⟨h1, h2⟩
                · exact hx0b h1
                · exact hWS x0 hx0W (h1 ▸ hq)
            have hlt : ((W.filter fun x => dist x s = t).card : ℝ) < τ := by
              by_contra hge
              push Not at hge
              exact hnb (by rw [hx0t]; exact mem_filter.2 ⟨himg, hnotR, hge⟩)
            calc ((W'.filter fun x => dist x s = t).card : ℝ)
                ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
                  exact_mod_cast card_le_card (filter_subset_filter _ hsubW)
              _ < τ := hlt
          · rw [not_nonempty_iff_eq_empty] at hne
            rw [hne, card_empty, Nat.cast_zero]; linarith
        · calc ((W'.filter fun x => dist x s = t).card : ℝ)
              ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
                exact_mod_cast card_le_card (filter_subset_filter _ hsubW)
            _ < σ := hc.cap s hsS t ht
            _ ≤ τ := hτ
    have hW' : (#W' : ℝ) ≤ Γ * τ := hclaim _ _ τ hconf' (hσ.trans hτ)
    have : (#Sv : ℝ) ≤ Γ * τ + r ^ 2 * σ := by
      have h1 : #Sv ≤ #Cls + #W' := (card_le_card hsub).trans (card_union_le _ _)
      have : (#Sv : ℝ) ≤ #Cls + #W' := by exact_mod_cast h1
      linarith
    exact Nat.le_floor this
  have hkill := kill_bound W F _ Δ hrank hdiag hsurv
  have hτpos : 0 < τ := lt_of_lt_of_le hσpos hτ
  have hΔle : (Δ : ℝ) ≤ Γ * τ + r ^ 2 * σ := Nat.floor_le (by positivity)
  have : (W.card : ℝ) ≤ (((D + 2) ^ (K + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := by
    exact_mod_cast hkill
  calc (W.card : ℝ) ≤ (((D + 2) ^ (K + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := this
    _ ≤ _ := by gcongr

end E1088
