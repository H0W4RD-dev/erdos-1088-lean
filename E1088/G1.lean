import E1088.Lemma12
import E1088.Ortho
import E1088.LRBound

/-!
# The label lemma and G1 (manuscript Section 5, bipartite form)

* `pdd_iff_rainbow` : the upstream `PairwiseDistancesDistinct` is our `Rainbow`.
* `label_lemma` : for label-disjoint `T`-generic `x, w`, `|xw| ∈ D_T ∪ L_x ∪ L_w`.
* `G1_bip` : if every `x ∈ P`, `w ∈ Q` are label-disjoint, `min(|P|,|Q|) ≤ 2^{L_{k_G}(D+2)} h`
  (with `LRcost k_G (D+2)` in place of `2^{L_{k_G}(D+2)}`), via Theorem LR and OR.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- `dist` on unordered pairs. -/
noncomputable def symDist : Sym2 (ℝ^d) → ℝ := Sym2.lift ⟨dist, dist_comm⟩

theorem dists_eq_image (A : Finset (ℝ^d)) :
    dists A = (A.offDiag.image Sym2.mk.uncurry).image symDist := by
  rw [image_image]; rfl

theorem card_dists_le (A : Finset (ℝ^d)) : (dists A).card ≤ (A.card).choose 2 := by
  rw [dists_eq_image, ← Sym2.card_image_offDiag]; exact card_image_le

/-- The upstream rainbow notion coincides with ours. -/
theorem pdd_iff_rainbow (A : Finset (ℝ^d)) :
    Erdos1088.PairwiseDistancesDistinct A ↔ Rainbow A := by
  unfold Erdos1088.PairwiseDistancesDistinct distinctDistances
  have hds : distanceSet A = dists A := rfl
  rw [hds, dists_eq_image, ← Sym2.card_image_offDiag, card_image_iff]
  constructor
  · intro hinj a ha a' ha' c hc c' hc' hne hne' hd
    have h1 : s(a, a') ∈ A.offDiag.image Sym2.mk.uncurry :=
      mem_image.2 ⟨(a, a'), mem_offDiag.2 ⟨ha, ha', hne⟩, rfl⟩
    have h2 : s(c, c') ∈ A.offDiag.image Sym2.mk.uncurry :=
      mem_image.2 ⟨(c, c'), mem_offDiag.2 ⟨hc, hc', hne'⟩, rfl⟩
    exact Sym2.eq_iff.1 (hinj h1 h2 hd)
  · intro hr z1 hz1 z2 hz2 heq
    obtain ⟨⟨a, a'⟩, hp, rfl⟩ := mem_image.1 hz1
    obtain ⟨⟨c, c'⟩, hq, rfl⟩ := mem_image.1 hz2
    obtain ⟨ha, ha', hne⟩ := mem_offDiag.1 hp
    obtain ⟨hc, hc', hne'⟩ := mem_offDiag.1 hq
    exact Sym2.eq_iff.2 (hr a ha a' ha' c hc c' hc' hne hne' heq)

/-- Rainbow-`n`-freeness in terms of `Rainbow`. -/
theorem rainbowFree_iff (n : ℕ) (X : Finset (ℝ^d)) :
    RainbowFree n X ↔ ∀ A ⊆ X, A.card = n → ¬ Rainbow A := by
  unfold RainbowFree Erdos1088.HasSubsetWithDistinctDistances
  constructor
  · intro h A hA hAn hr; exact h ⟨A, hA, hAn, (pdd_iff_rainbow A).2 hr⟩
  · rintro h ⟨A, hA, hAn, hp⟩; exact h A hA hAn ((pdd_iff_rainbow A).1 hp)

/-- **Label lemma.** -/
theorem label_lemma (n : ℕ) (X T : Finset (ℝ^d)) (x w : ℝ^d) (hfree : RainbowFree n X)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hx : x ∈ X) (hw : w ∈ X)
    (hxT : x ∉ T) (hwT : w ∉ T) (hxr : Rainbow (insert x T)) (hwr : Rainbow (insert w T))
    (hdisj : ∀ t ∈ T, ∀ t' ∈ T, dist x t ≠ dist w t') :
    x ≠ w ∧ (dist x w ∈ dists T ∨ (∃ t ∈ T, dist x w = dist x t) ∨
      ∃ t ∈ T, dist x w = dist w t) := by
  have hxw : x ≠ w := by
    rintro rfl; obtain ⟨t, ht⟩ := hT1; exact hdisj t ht t ht rfl
  refine ⟨hxw, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h3, h2, h1⟩ := hcon
  have hR : Rainbow (insert x (insert w T)) :=
    rainbow_insert_insert T w x hwr hxr (fun s hs s' hs' => hdisj s hs s' hs')
      (fun s hs => h1 s hs) (fun s hs => h2 s hs)
      (fun s hs s' hs' hne h => h3 (h ▸ mem_dists hs hs' hne))
  have hcard : (insert x (insert w T)).card = n := by
    rw [card_insert_of_notMem, card_insert_of_notMem hwT]
    · omega
    · simp [hxw, hxT]
  exact (rainbowFree_iff n X).1 hfree _ (insert_subset hx (insert_subset hw hTX)) hcard hR

theorem affDim_mono {A B : Finset (ℝ^d)} (h : A ⊆ B) : affDim A ≤ affDim B := by
  unfold affDim
  exact Submodule.finrank_mono (vectorSpan_mono ℝ (by exact_mod_cast h))

/-- Number of LR types in G1: `k_G = C(n-2, 2) + 2(n-2)`. -/
def kG (n : ℕ) : ℕ := (n - 2).choose 2 + 2 * (n - 2)

theorem one_le_LRcost' (k r : ℕ) : (0 : ℝ) ≤ LRcost k r := le_trans zero_le_one (one_le_LRcost k r)

/-- **G1, bipartite form.** -/
theorem G1_bip (n D h : ℕ) (X T P Q : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty)
    (hP : P ⊆ X) (hQ : Q ⊆ X) (hPg : ∀ x ∈ P, x ∉ T ∧ Rainbow (insert x T))
    (hQg : ∀ w ∈ Q, w ∉ T ∧ Rainbow (insert w T))
    (hdisj : ∀ x ∈ P, ∀ w ∈ Q, ∀ t ∈ T, ∀ t' ∈ T, dist x t ≠ dist w t') :
    (min P.card Q.card : ℝ) ≤ LRcost (kG n) (D + 2) * h := by
  classical
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · simp only [hPe, card_empty, CharP.cast_eq_zero]
    exact (min_le_left _ _).trans (mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _))
  rcases Q.eq_empty_or_nonempty with hQe | hQne
  · simp only [hQe, card_empty, CharP.cast_eq_zero]
    exact (min_le_right _ _).trans (mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _))
  -- the LR setup
  let ι := ↥(dists T) ⊕ (↥T ⊕ ↥T)
  let τ : ι → TF (ℝ^d) (ℝ^d) := fun k => match k with
    | Sum.inl δ => TF.col fun _ => (δ : ℝ) ^ 2
    | Sum.inr (Sum.inl t) => TF.col fun w => dist w t ^ 2
    | Sum.inr (Sum.inr t) => TF.row fun x => dist x t ^ 2
  let M : ℝ^d → ℝ^d → ℝ := fun x w => dist x w ^ 2
  have hcardS : (Finset.univ : Finset ι).card ≤ kG n := by
    rw [card_univ]
    simp only [ι, Fintype.card_sum, Fintype.card_coe, kG]
    have hT' : T.card = n - 2 := by omega
    have := card_dists_le T
    rw [hT'] at this
    omega
  have hrank : rankOn M P Q ≤ D + 2 := by
    unfold rankOn
    have := rank_sqdist_le_affine X D hD (fun i : P => (i : ℝ^d)) (fun j : Q => (j : ℝ^d))
      (fun i => hP i.2) (fun j => hQ j.2) (fun _ => 0) (fun _ => 0)
    have e : (Matrix.of fun (i : P) (j : Q) => M i j) =
        Matrix.of fun (i : P) (j : Q) => ‖(i : ℝ^d) - j‖ ^ 2 - 0 - 0 := by
      ext i j; simp [M, dist_eq_norm]
    rw [e]; exact this
  have hcov : Covers M τ Finset.univ P Q := by
    intro x hx w hw
    obtain ⟨hxT, hxr⟩ := hPg x hx
    obtain ⟨hwT, hwr⟩ := hQg w hw
    obtain ⟨-, hcase⟩ := label_lemma n X T x w hfree hTX hTn hT1 (hP hx) (hQ hw) hxT hwT hxr hwr
      (hdisj x hx w hw)
    rcases hcase with h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · exact ⟨Sum.inl ⟨_, h⟩, mem_univ _, rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨t, ht⟩), mem_univ _, by simp [M, τ, TF.eval, h]⟩
    · exact ⟨Sum.inr (Sum.inl ⟨t, ht⟩), mem_univ _, by simp [M, τ, TF.eval, h]⟩
  obtain ⟨R, hRP, C, hCQ, t₀, -, c1, c2, hM⟩ :=
    theoremLR M τ (D + 2) (kG n) Finset.univ P Q hcardS hPne hQne hrank hcov
  -- the single type gives an orthogonal split
  have hortho : ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0 := by
    rcases t₀ with δ | t | t
    · refine ortho_of_equidistant R C (fun _ => (δ : ℝ)) fun x hx w hw => ?_
      have := hM x hx w hw
      simp only [M, τ, TF.eval] at this
      rw [← dist_eq_norm]
      have hδ : 0 ≤ (δ : ℝ) := (pos_of_mem_dists δ.2).le
      exact (pow_left_inj₀ dist_nonneg hδ two_ne_zero).1 this
    · refine ortho_of_equidistant R C (fun w => dist w t) fun x hx w hw => ?_
      have := hM x hx w hw
      simp only [M, τ, TF.eval] at this
      rw [← dist_eq_norm]
      exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 this
    · refine ortho_of_bisector R C t fun x hx w hw => ?_
      have := hM x hx w hw
      simp only [M, τ, TF.eval] at this
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact ((pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 this).symm
  have hRC : affDim (R ∪ C) ≤ D :=
    (affDim_mono (union_subset (hRP.trans hP) (hCQ.trans hQ))).trans hD
  have hmin := min_affDim_le_of_ortho R C D hRC hortho
  have hL := one_le_LRcost (kG n) (D + 2)
  rcases le_total (affDim R) (affDim C) with hle | hle
  · rw [min_eq_left hle] at hmin
    have hR := hh R (hRP.trans hP) hmin
    have : (R.card : ℝ) ≤ h := by exact_mod_cast hR
    calc (min P.card Q.card : ℝ) ≤ P.card := by exact_mod_cast min_le_left _ _
      _ ≤ LRcost (kG n) (D + 2) * R.card := c1
      _ ≤ LRcost (kG n) (D + 2) * h := mul_le_mul_of_nonneg_left this (by linarith)
  · rw [min_eq_right hle] at hmin
    have hC := hh C (hCQ.trans hQ) hmin
    have : (C.card : ℝ) ≤ h := by exact_mod_cast hC
    calc (min P.card Q.card : ℝ) ≤ Q.card := by exact_mod_cast min_le_right _ _
      _ ≤ LRcost (kG n) (D + 2) * C.card := c2
      _ ≤ LRcost (kG n) (D + 2) * h := mul_le_mul_of_nonneg_left this (by linarith)

end E1088
