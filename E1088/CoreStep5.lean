import E1088.CoreStep34

/-!
# Core Lemma: Step 5 ingredients (manuscript Section 8, Step 5 and Lemma 8.11)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- `Ty(a₁, a₂)`. -/
noncomputable def Ty (S B : Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (l m : ℕ) (a1 a2 : ℝ^d) : Finset ℝ :=
  dists (S ∪ B) ∪ B.image (β l) ∪ B.image (β m) ∪ S.image (dist a1) ∪ S.image (dist a2)

/-- Distances from a point `x` of a class to `S ∪ B` avoid `D_{S∪B}` and are injective. -/
theorem class_point_facts {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {k : ℕ} (hk : k ∈ I) {x : ℝ^d}
    (hx : x ∈ C k) :
    (∀ y ∈ S ∪ B, ∀ y' ∈ S ∪ B, dist x y = dist x y' → y = y') ∧
      ∀ y ∈ S ∪ B, dist x y ∉ dists (S ∪ B) := by
  obtain ⟨hxSB, hxR⟩ := hF.F4 k hk x hx
  refine ⟨fun y hy y' hy' h => ?_, fun y hy h => ?_⟩
  · have hxy : x ≠ y := fun e => hxSB (e ▸ hy)
    have hxy' : x ≠ y' := fun e => hxSB (e ▸ hy')
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) x (mem_insert_self _ _) y'
      (mem_insert_of_mem hy') hxy hxy' h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 hxy'
  · obtain ⟨q, hq, hqe⟩ := mem_image.1 h
    obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
    have hxy : x ≠ y := fun e => hxSB (e ▸ hy)
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) q.1
      (mem_insert_of_mem hq1) q.2 (mem_insert_of_mem hq2) hxy hq12 hqe.symm with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxSB (h1 ▸ hq1)
    · exact hxSB (h1 ▸ hq2)

/-- **Lemma 8.11** (the direction used): outside `Π` and with `|a₁a₂| ∉ Ty`, `T` is rainbow. -/
theorem coreT_rainbow {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m)
    (hPi : ∀ s ∈ S, ∀ s' ∈ S, dist a1 s ≠ dist a2 s') (hTy : dist a1 a2 ∉ Ty S B β l m a1 a2) :
    Rainbow (coreT S B a1 a2) := by
  classical
  have h12 : a1 ≠ a2 := fun e => family_classes_disjoint hF hl hm hlm ha1 (e ▸ ha2)
  obtain ⟨hinj1, hout1⟩ := class_point_facts hF hl ha1
  have hTy1 : ∀ s ∈ S, dist a1 a2 ≠ dist a1 s := fun s hs e =>
    hTy (by unfold Ty; rw [e]; exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hs)))
  have hTy2 : ∀ b ∈ B, dist a1 a2 ≠ dist a1 b := fun b hb e => hTy (by
    unfold Ty; rw [e, hF.F2 l hl a1 ha1 b hb]
    exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_image_of_mem _ hb)))))
  have hTy3 : ∀ s ∈ S, dist a1 a2 ≠ dist a2 s := fun s hs e =>
    hTy (by unfold Ty; rw [e]; exact mem_union_right _ (mem_image_of_mem _ hs))
  have hTy4 : ∀ b ∈ B, dist a1 a2 ≠ dist a2 b := fun b hb e => hTy (by
    unfold Ty; rw [e, hF.F2 m hm a2 ha2 b hb]
    exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hb))))
  have hTy5 : dist a1 a2 ∉ dists (S ∪ B) := fun h => hTy (by
    unfold Ty
    exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ h))))
  refine rainbow_insert_one _ a1 (hF.F4 m hm a2 ha2).2 ?_ ?_ ?_
  · simp only [mem_insert, not_or]; exact ⟨h12, (hF.F4 l hl a1 ha1).1⟩
  · intro y hy y' hy' h
    rcases mem_insert.1 hy with ey | hy <;> rcases mem_insert.1 hy' with ey' | hy'
    · exact ey.trans ey'.symm
    · rw [ey] at h
      rcases mem_union.1 hy' with hs | hb
      · exact absurd h (hTy1 _ hs)
      · exact absurd h (hTy2 _ hb)
    · rw [ey'] at h
      rcases mem_union.1 hy with hs | hb
      · exact absurd h.symm (hTy1 _ hs)
      · exact absurd h.symm (hTy2 _ hb)
    · exact hinj1 y hy y' hy' h
  · intro y hy hmem
    rcases mem_union.1 (dists_insert_subset _ a2 hmem) with h | h
    · rcases mem_insert.1 hy with ey | hy
      · rw [ey] at h; exact hTy5 h
      · exact hout1 y hy h
    · obtain ⟨z, hz, hze⟩ := mem_image.1 h
      rcases mem_insert.1 hy with ey | hy
      · rw [ey] at hze
        rcases mem_union.1 hz with hzS | hzB
        · exact hTy3 z hzS hze.symm
        · exact hTy4 z hzB hze.symm
      · rcases mem_union.1 hy with hyS | hyB <;> rcases mem_union.1 hz with hzS | hzB
        · exact hPi y hyS z hzS hze.symm
        · rw [hF.F2 m hm a2 ha2 z hzB] at hze
          exact hF.F5 l hl a1 ha1 y hyS m hm z hzB hze.symm
        · rw [hF.F2 l hl a1 ha1 y hyB] at hze
          exact hF.F5 m hm a2 ha2 z hzS l hl y hyB hze
        · rw [hF.F2 l hl a1 ha1 y hyB, hF.F2 m hm a2 ha2 z hzB] at hze
          exact hlm (hF.F3.1 m hm l hl z hzB y hyB hze).1.symm

/-- For `k ∉ {l, m}` with `|a₁a₂| ∉ β(k)`, `β(k) ∩ D_T = ∅`. -/
theorem beta_disjoint {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m k : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hk : k ∈ I) (hkl : k ≠ l) (hkm : k ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m)
    (hk12 : dist a1 a2 ∉ B.image (β k)) :
    Disjoint (B.image (β k)) (dists (coreT S B a1 a2)) := by
  classical
  rw [disjoint_left]
  intro v hv hvT
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
  rcases mem_union.1 (dists_coreT_subset S B a1 a2 hvT) with h | h
  · rcases mem_union.1 h with h | h
    · exact hF.F3.2 k hk b hb h
    · obtain ⟨z, hz, hze⟩ := mem_image.1 h
      rcases mem_union.1 hz with hzS | hzB
      · exact hF.F5 m hm a2 ha2 z hzS k hk b hb hze
      · rw [hF.F2 m hm a2 ha2 z hzB] at hze
        exact hkm (hF.F3.1 m hm k hk z hzB b hb hze).1.symm
  · obtain ⟨z, hz, hze⟩ := mem_image.1 h
    rcases mem_insert.1 hz with rfl | hz
    · exact hk12 (hze ▸ hv)
    rcases mem_union.1 hz with hzS | hzB
    · exact hF.F5 l hl a1 ha1 z hzS k hk b hb hze
    · rw [hF.F2 l hl a1 ha1 z hzB] at hze
      exact hkl (hF.F3.1 l hl k hk z hzB b hb hze).1.symm

/-- `Cov_j` gives the covering shape with `w₂ = C(n-2,2) + p` radii and `δ = 6ε`. -/
theorem cov_shape {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {l m j : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m) (ε : ℝ)
    (hcov : CovK S B C β ε j a1 a2) :
    CoverShape S C ((n - 2).choose 2 + (n - 4 - r)) (6 * ε) j a1 a2 := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  refine ⟨dists (coreT S B a1 a2) ∪ B.image (β j), ?_, (C j).filter fun x => ¬ LamK S B β j a1 a2 x,
    filter_subset _ _, hcov.le, ?_⟩
  · have e1 := card_union_le (dists (coreT S B a1 a2)) (B.image (β j))
    have e2 := card_dists_le (coreT S B a1 a2)
    have e3 := card_image_le (s := B) (f := β j)
    rw [card_coreT hF hl hm hlm ha1 ha2, card_union_of_disjoint hF.F1.1, hc.card, hB] at e2
    rw [hB] at e3
    have : r + (n - 4 - r) + 2 = n - 2 := by omega
    rw [this] at e2
    omega
  · intro x hx
    by_cases hL : LamK S B β j a1 a2 x
    · rcases hL with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_filter.2 ⟨hx, hL⟩))))

open Classical in
/-- The per-pair count of Step 5: on `V_{lm}`, `#Good + #Cov ≥ 6` over `I \ {l, m}`
(with `|I| = 12`). -/
theorem pair_count {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) (hI : I.card = 12) (M ε δ1 : ℝ) (hM0 : 0 < M)
    (hMk : ∀ k ∈ I, M ≤ (C k).card) (hε : 0 < ε) (hP2 : 2 * n ^ 2 * σ ≤ ε * M)
    (hδ1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M) + 3 * n ^ 2 * σ / M ≤ δ1)
    {l m : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l)
    (ha2 : a2 ∈ C m) (hPi : ∀ s ∈ S, ∀ s' ∈ S, dist a1 s ≠ dist a2 s')
    (hTy : dist a1 a2 ∉ Ty S B β l m a1 a2) :
    6 ≤ (((I.erase l).erase m).filter fun j =>
          CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 j a1 a2).card +
        (((I.erase l).erase m).filter fun j => CovK S B C β ε j a1 a2).card := by
  classical
  have hF := cc.fam
  have hT := coreT_rainbow hF hl hm hlm ha1 ha2 hPi hTy
  set I2 := (I.erase l).erase m with hI2
  have hI2c : I2.card = 10 := by
    rw [hI2, card_erase_of_mem (mem_erase.2 ⟨fun e => hlm e.symm, hm⟩), card_erase_of_mem hl, hI]
  set I0 := I2.filter fun k => dist a1 a2 ∉ B.image (β k) with hI0
  have hbad : (I2.filter fun k => dist a1 a2 ∈ B.image (β k)).card ≤ 1 := by
    rw [card_le_one]
    intro k hk k' hk'
    obtain ⟨hkI, hk1⟩ := mem_filter.1 hk
    obtain ⟨hk'I, hk'1⟩ := mem_filter.1 hk'
    obtain ⟨b, hb, hbe⟩ := mem_image.1 hk1
    obtain ⟨b', hb', hbe'⟩ := mem_image.1 hk'1
    exact (hF.F3.1 k (mem_of_mem_erase (mem_of_mem_erase hkI)) k'
      (mem_of_mem_erase (mem_of_mem_erase hk'I)) b hb b' hb' (hbe.trans hbe'.symm)).1
  have hI0c : 9 ≤ I0.card := by
    have := card_filter_add_card_filter_not (s := I2) (fun k => dist a1 a2 ∈ B.image (β k))
    rw [hI2c] at this
    rw [hI0]
    omega
  have hmemI0 : ∀ k ∈ I0, k ∈ I ∧ k ≠ l ∧ k ≠ m ∧ dist a1 a2 ∉ B.image (β k) := by
    intro k hk
    obtain ⟨hk2, hk1⟩ := mem_filter.1 hk
    obtain ⟨hkm, hk2'⟩ := mem_erase.1 hk2
    obtain ⟨hkl, hkI⟩ := mem_erase.1 hk2'
    exact ⟨hkI, hkl, hkm, hk1⟩
  have hI0sub : I0 ⊆ I2 := filter_subset _ _
  set g := (I0.filter fun k =>
    CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2).card with hg
  by_cases hgc : I0.card ≤ g + 3
  · have : g ≤ (I2.filter fun j =>
        CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 j a1 a2).card :=
      card_le_card (filter_subset_filter _ hI0sub)
    omega
  · push Not at hgc
    have hall : ∀ k' ∈ I0, CovK S B C β ε k' a1 a2 := by
      intro k' hk'
      obtain ⟨hk'I, hk'l, hk'm, hk'12⟩ := hmemI0 k' hk'
      set J := (I0.erase k').filter fun k =>
        ¬ CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2 with hJ
      have hJ3 : 3 ≤ J.card := by
        have e1 := card_filter_add_card_filter_not (s := I0.erase k') (fun k =>
          CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2)
        have e2 : ((I0.erase k').filter fun k =>
            CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2).card ≤ g :=
          card_le_card (filter_subset_filter _ (erase_subset _ _))
        rw [card_erase_of_mem hk'] at e1
        rw [hJ]
        omega
      have hJI : J ⊆ I := fun k hk => (hmemI0 k (mem_of_mem_erase (mem_filter.1 hk).1)).1
      refine core_step2 hF ε hε M hM0 (hMk k' hk'I) J hJI hJ3 fun k hk => ?_
      obtain ⟨hkI0', hnG⟩ := mem_filter.1 hk
      obtain ⟨hkk', hkI0⟩ := mem_erase.1 hkI0'
      obtain ⟨hkI, hkl, hkm, hk12⟩ := hmemI0 k hkI0
      rcases core_step1 cc M ε δ1 hM0 hMk hε hP2 hδ1 hl hm hlm hkI hk'I hkl hkm hk'l hk'm hkk'
          ha1 ha2 hT (beta_disjoint hF hl hm hkI hkl hkm ha1 ha2 hk12)
          (beta_disjoint hF hl hm hk'I hk'l hk'm ha1 ha2 hk'12) with h | h
      · exact absurd h hnG
      · exact h
    have : I0.card ≤ (I2.filter fun j => CovK S B C β ε j a1 a2).card := by
      calc I0.card = (I0.filter fun j => CovK S B C β ε j a1 a2).card := by
            rw [filter_true_of_mem hall]
        _ ≤ _ := card_le_card (filter_subset_filter _ hI0sub)
    omega

end E1088
