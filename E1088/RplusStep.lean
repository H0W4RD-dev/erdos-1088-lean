import E1088.RplusA3

/-!
# Theorem R⁺: the kill step with Step A (manuscript Section 7, proof of Theorem 7.1)

`rplus_step` is `lemma_1_2` (Lemma12.lean) with `K = 2`, where a point `b` with at least three
big radii is handled by Step A (`stepA`) instead of the inductive Claim(r+1).
(The paper switches to Step A as soon as `|Big_b| ≥ 2`; using it only for `|Big_b| ≥ 3` is
equivalent here, since the kill function then removes both big spheres.)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

set_option maxHeartbeats 2000000 in
theorem rplus_step (n : ℕ) (hn : 4 ≤ n) (D h : ℕ) (X : Finset (ℝ^d)) (hX : Ambient n D h X)
    (r : ℕ) (hr : n - 4 ≤ r) (Γ τ σ : ℝ) (hclaim : ClaimAt X (r + 1) Γ (smin n D h))
    (S W : Finset (ℝ^d)) (hc : Config X S W r σ) (hΓ : 0 ≤ Γ) (hσ : smin n D h ≤ σ)
    (hτ : τ = QA n D * σ) (hk : kA n ≤ kstar n) :
    (W.card : ℝ) ≤ (((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) *
      (Γ * τ + r ^ 2 * σ + (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1) := by
  have hD := hX.dim
  have hσpos : 0 < σ := lt_of_lt_of_le zero_lt_one ((one_le_smin n D h).trans hσ)
  have hQ1 : (1 : ℝ) ≤ QA n D := by
    unfold QA
    have h1 : (1 : ℝ) ≤ n ^ 2 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have h2 : (1 : ℝ) ≤ (((D + 2 : ℕ) : ℝ) ^ kA n) ^ 5 :=
      one_le_pow₀ (one_le_pow₀ (by exact_mod_cast (show 1 ≤ D + 2 by omega)))
    have h3 : (1 : ℝ) ≤ 2 ^ 27 * n ^ 2 := by nlinarith
    nlinarith
  have hτσ : σ ≤ τ := by rw [hτ]; nlinarith
  have he0 := e_nonneg n D h
  have hτ' := hτσ
  classical
  -- factor index type
  let J := Fin 2 ⊕ (S ⊕ (S ⊕ dists S))
  have hJ : Fintype.card J = 2 + 2 * r + (dists S).card := by
    simp only [J, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hc.card]; ring
  -- the enumerated big radii
  let lam : ℝ^d → Fin 2 → ℝ := fun b i =>
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
  have hlam_mem : ∀ b (i : Fin 2) (h : (i : ℕ) < (Big S W b τ).card), lam b i ∈ Big S W b τ := by
    intro b i h; simp only [lam, dif_pos h]; exact Finset.coe_mem _
  have hlam_surj : ∀ b ∈ W, (Big S W b τ).card ≤ 2 → ∀ l ∈ Big S W b τ, ∃ i : Fin 2,
      (i : ℕ) < (Big S W b τ).card ∧ lam b i = l := by
    intro b hb hB l hl
    set j := (Big S W b τ).equivFin ⟨l, hl⟩
    refine ⟨⟨j, lt_of_lt_of_le j.2 hB⟩, j.2, ?_⟩
    simp only [lam, dif_pos j.2]
    simp [j]
  have hBig_pos : ∀ b l, l ∈ Big S W b τ → 0 < l := by
    intro b l hl
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 hl).1
    exact dist_pos.2 (ne_of_mem_erase hx)
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hWX : ∀ x ∈ W, x ∈ X := fun x hx => hc.subW hx
  -- apply the kill step
  set Δ := ⌊Γ * τ + r ^ 2 * σ + (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ)⌋₊ with hΔ
  have hrank : rankOn F W W ≤ (D + 2) ^ (2 + 2 * r + (dists S).card) := by
    unfold rankOn
    have h1 := rank_finset_prod_le (Finset.univ : Finset J) (fun k => Matrix.of fun (i : W) (j : W) =>
      ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j)
    refine h1.trans ?_
    calc ∏ k ∈ (Finset.univ : Finset J), (Matrix.of fun (i : W) (j : W) =>
          ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j).rank
        ≤ ∏ _k ∈ (Finset.univ : Finset J), (D + 2) := Finset.prod_le_prod' fun k _ =>
          rank_sqdist_le_affine X D hD (fun i : W => (i : ℝ^d)) (fun j : W => (j : ℝ^d))
            (fun i => hWX _ i.2) (fun j => hWX _ j.2) _ _
      _ = (D + 2) ^ (2 + 2 * r + (dists S).card) := by
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
    by_cases hB2 : (Big S W b τ).card ≤ 2
    · set Sv := W.filter fun x => x ≠ b ∧ F b x ≠ 0
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
          obtain ⟨i, hi, hli⟩ := hlam_surj b hb hB2 _ hl
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
              _ ≤ τ := hτσ
      have hW' : (#W' : ℝ) ≤ Γ * τ := hclaim _ _ τ hconf' (hσ.trans hτσ)
      have : (#Sv : ℝ) ≤ Γ * τ + r ^ 2 * σ := by
        have h1 : #Sv ≤ #Cls + #W' := (card_le_card hsub).trans (card_union_le _ _)
        have : (#Sv : ℝ) ≤ #Cls + #W' := by exact_mod_cast h1
        linarith
      have hA0 : (0 : ℝ) ≤ 2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ := by
        have : (0 : ℝ) ≤ (n - 4 : ℕ) := Nat.cast_nonneg _
        nlinarith
      exact Nat.le_floor (by linarith)
    · push Not at hB2
      set Sv := W.filter fun x => x ≠ b ∧ F b x ≠ 0
      set Cls := (S ×ˢ S).biUnion fun q => W.filter fun x => dist x q.1 = dist b q.2
      have h0 : 0 < (Big S W b τ).card := by omega
      have h1 : 1 < (Big S W b τ).card := by omega
      have h0' : ((0 : Fin 2) : ℕ) < (Big S W b τ).card := by simpa using h0
      have h1' : ((1 : Fin 2) : ℕ) < (Big S W b τ).card := by simpa using h1
      have hρ1 := hlam_mem b 0 h0'
      have hρ2 := hlam_mem b 1 h1'
      have hρne : lam b 0 ≠ lam b 1 := by
        intro he
        simp only [lam, dif_pos h0', dif_pos h1'] at he
        have := (Big S W b τ).equivFin.symm.injective (Subtype.ext he)
        simp [Fin.ext_iff] at this
      have hsub : Sv ⊆ Cls ∪ AsetA S W b (lam b 0) (lam b 1) := by
        intro x hx
        obtain ⟨hxW, hxb, hF⟩ := mem_filter.1 hx
        have hfac : ∀ k : J, ‖b - x‖ ^ 2 - f k b - g k x ≠ 0 := fun k =>
          Finset.prod_ne_zero_iff.1 hF k (Finset.mem_univ _)
        have hbx : ‖b - x‖ = dist x b := by rw [← dist_eq_norm, dist_comm]
        by_cases hcl : x ∈ Cls
        · exact mem_union_left _ hcl
        refine mem_union_right _ (mem_AsetA.2 ⟨mem_erase.2 ⟨hxb, hxW⟩, ?_, ?_, ?_⟩)
        · have := hfac (Sum.inl 0)
          simp only [f, g, sub_zero] at this
          rw [if_pos h0', hbx] at this
          exact fun h => this (by rw [h]; ring)
        · have := hfac (Sum.inl 1)
          simp only [f, g, sub_zero] at this
          rw [if_pos h1', hbx] at this
          exact fun h => this (by rw [h]; ring)
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
      have hA := stepA hn hr hX hc hσ hk hb hρne (by rw [← hτ]; exact hρ1) (by rw [← hτ]; exact hρ2)
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
      have hSv : (#Sv : ℝ) ≤ #Cls + (((AsetA S W b (lam b 0) (lam b 1)).card : ℕ) : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
      have hΓτ : 0 ≤ Γ * τ := mul_nonneg hΓ (by linarith)
      exact Nat.le_floor (by linarith)
  have hkill := kill_bound W F _ Δ hrank hdiag hsurv
  have hτpos : 0 < τ := lt_of_lt_of_le hσpos hτσ
  have hΔle : (Δ : ℝ) ≤ Γ * τ + r ^ 2 * σ +
      (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) := by
    refine Nat.floor_le ?_
    have : 0 ≤ Γ * τ := mul_nonneg hΓ hτpos.le
    have : (0 : ℝ) ≤ r ^ 2 * σ := by positivity
    have : (0 : ℝ) ≤ (n - 4 : ℕ) := Nat.cast_nonneg _
    nlinarith
  have : (W.card : ℝ) ≤ (((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := by
    exact_mod_cast hkill
  calc (W.card : ℝ) ≤ (((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := this
    _ ≤ _ := by gcongr

end E1088
