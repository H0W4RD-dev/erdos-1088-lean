import E1088.CoreBasic

/-!
# Core Lemma (manuscript Theorem 8.2): setting, notation and Step 0

Throughout: a level-`r` configuration `(S, W, σ)`, HR_r with constant `Γ'`, and a rainbow family
`(B, (C_k, β(k))_{k∈I})` with `|B| = n-4-r`. For `a₁ ∈ C_l`, `a₂ ∈ C_m` put
`T = S ∪ B ∪ {a₁, a₂}`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- The standing hypotheses of Sections 8–9. -/
structure CoreCtx (n D h r : ℕ) (X S W : Finset (ℝ^d)) (σ Γ' : ℝ) (B : Finset (ℝ^d))
    (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) : Prop where
  hn : 5 ≤ n
  hr : r ≤ n - 5
  amb : Ambient n D h X
  conf : Config X S W r σ
  hσ : smin n D h ≤ σ
  hΓ : 1 ≤ Γ'
  hHR : HRholds S W σ Γ'
  fam : RainbowFamily S W B I C β
  BX : B ⊆ X
  hB : B.card = n - 4 - r

/-- `T(a₁, a₂) = S ∪ B ∪ {a₁, a₂}`. -/
noncomputable def coreT (S B : Finset (ℝ^d)) (a1 a2 : ℝ^d) : Finset (ℝ^d) := insert a1 (insert a2 (S ∪ B))

/-- `Hyp(a₁, a₂)`: the bisectors `H(s, aᵢ)`. -/
def Hyp (S : Finset (ℝ^d)) (a1 a2 x : ℝ^d) : Prop :=
  ∃ s ∈ S, dist x s = dist x a1 ∨ dist x s = dist x a2

/-- The radii of `Sm(a₁, a₂)`. -/
noncomputable def smRadii (S : Finset (ℝ^d)) (a1 a2 : ℝ^d) : Finset ℝ :=
  S.image (dist a1) ∪ S.image (dist a2) ∪ {dist a1 a2}

/-- `Sm(a₁, a₂)`: spheres about the points of `S` with radii in `smRadii`. -/
def Sm (S : Finset (ℝ^d)) (a1 a2 x : ℝ^d) : Prop :=
  ∃ s ∈ S, dist x s ∈ smRadii S a1 a2

/-- `Λ_k(a₁, a₂)`. -/
def LamK (S B : Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (k : ℕ) (a1 a2 x : ℝ^d) : Prop :=
  dist x a1 ∈ dists (coreT S B a1 a2) ∪ B.image (β k) ∨
    dist x a2 ∈ dists (coreT S B a1 a2) ∪ B.image (β k) ∨ dist x a1 = dist x a2 ∨ Hyp S a1 a2 x

noncomputable instance (S : Finset (ℝ^d)) (a1 a2 : ℝ^d) : DecidablePred (Hyp S a1 a2) :=
  fun x => by unfold Hyp; infer_instance

noncomputable instance (S : Finset (ℝ^d)) (a1 a2 : ℝ^d) : DecidablePred (Sm S a1 a2) :=
  fun x => by unfold Sm; infer_instance

noncomputable instance (S B : Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (k : ℕ) (a1 a2 : ℝ^d) :
    DecidablePred (LamK S B β k a1 a2) :=
  fun x => by unfold LamK; infer_instance

theorem dists_coreT_subset (S B : Finset (ℝ^d)) (a1 a2 : ℝ^d) :
    dists (coreT S B a1 a2) ⊆
      dists (S ∪ B) ∪ (S ∪ B).image (dist a2) ∪ (insert a2 (S ∪ B)).image (dist a1) := by
  intro v hv
  rcases mem_union.1 (dists_insert_subset _ a1 hv) with h | h
  · rcases mem_union.1 (dists_insert_subset _ a2 h) with h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
  · exact mem_union_right _ h

/-- **Step 0** (manuscript Lemma 8.4): non-generic points of `C_k` lie in `Λ_k ∪ Sm`. -/
theorem core_step0 {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m k : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hk : k ∈ I) (hkl : k ≠ l) (hkm : k ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m)
    (hT : Rainbow (coreT S B a1 a2)) (hβ : Disjoint (B.image (β k)) (dists (coreT S B a1 a2)))
    {x : ℝ^d} (hx : x ∈ C k) (hng : ¬ Rainbow (insert x (coreT S B a1 a2))) :
    LamK S B β k a1 a2 x ∨ Sm S a1 a2 x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hL, hSm⟩ := hcon
  simp only [LamK, not_or] at hL
  obtain ⟨hL1, hL2, hL12, hHyp⟩ := hL
  simp only [Hyp, not_exists, not_and, not_or] at hHyp
  simp only [Sm, not_exists, not_and] at hSm
  obtain ⟨hxSB, hxR⟩ := hF.F4 k hk x hx
  have hxa1 : x ≠ a1 := fun e => family_classes_disjoint hF hk hl hkl hx (e ▸ ha1)
  have hxa2 : x ≠ a2 := fun e => family_classes_disjoint hF hk hm hkm hx (e ▸ ha2)
  have hxT : x ∉ coreT S B a1 a2 := by
    simp only [coreT, mem_insert, not_or]; exact ⟨hxa1, hxa2, hxSB⟩
  -- distances from `x` to `S ∪ B` are pairwise distinct
  have hSBinj : ∀ y ∈ S ∪ B, ∀ y' ∈ S ∪ B, dist x y = dist x y' → y = y' := by
    intro y hy y' hy' h
    have hxy : x ≠ y := fun e => hxSB (e ▸ hy)
    have hxy' : x ≠ y' := fun e => hxSB (e ▸ hy')
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) x (mem_insert_self _ _) y'
      (mem_insert_of_mem hy') hxy hxy' h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 hxy'
  -- a distance `|xb|`, `b ∈ B`, lies in `β(k)`
  have hxb : ∀ b ∈ B, dist x b ∈ B.image (β k) := fun b hb =>
    mem_image.2 ⟨b, hb, (hF.F2 k hk x hx b hb).symm⟩
  refine hng (rainbow_insert_one _ x hT hxT ?_ ?_)
  · intro y hy y' hy' h
    simp only [coreT, mem_insert] at hy hy'
    rcases hy with rfl | rfl | hy <;> rcases hy' with rfl | rfl | hy'
    · rfl
    · exact absurd h hL12
    · rcases mem_union.1 hy' with hs | hb
      · exact absurd h.symm ((hHyp _ hs).1)
      · exact absurd (h ▸ hxb y' hb) (fun hm' => hL1 (mem_union_right _ hm'))
    · exact absurd h.symm hL12
    · rfl
    · rcases mem_union.1 hy' with hs | hb
      · exact absurd h.symm ((hHyp _ hs).2)
      · exact absurd (h ▸ hxb y' hb) (fun hm' => hL2 (mem_union_right _ hm'))
    · rcases mem_union.1 hy with hs | hb
      · exact absurd h ((hHyp _ hs).1)
      · exact absurd (h.symm ▸ hxb y hb) (fun hm' => hL1 (mem_union_right _ hm'))
    · rcases mem_union.1 hy with hs | hb
      · exact absurd h ((hHyp _ hs).2)
      · exact absurd (h.symm ▸ hxb y hb) (fun hm' => hL2 (mem_union_right _ hm'))
    · exact hSBinj y hy y' hy' h
  · intro y hy hmem
    simp only [coreT, mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · exact hL1 (mem_union_left _ hmem)
    · exact hL2 (mem_union_left _ hmem)
    rcases mem_union.1 hy with hs | hb
    · -- `|xs| ∈ D_T`
      rcases mem_union.1 (dists_coreT_subset S B a1 a2 hmem) with h | h
      · rcases mem_union.1 h with h | h
        · -- in `D_{S∪B}`: impossible by (F4)
          obtain ⟨q, hq, hqe⟩ := mem_image.1 h
          obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
          have hxy : x ≠ y := fun e => hxSB (e ▸ mem_union_left _ hs)
          rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem (mem_union_left _ hs)) q.1
            (mem_insert_of_mem hq1) q.2 (mem_insert_of_mem hq2) hxy hq12 hqe.symm with
            ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hxSB (h1 ▸ hq1)
          · exact hxSB (h1 ▸ hq2)
        · obtain ⟨z, hz, hze⟩ := mem_image.1 h
          rcases mem_union.1 hz with hzS | hzB
          · exact hSm y hs (mem_union_left _ (mem_union_right _ (mem_image.2 ⟨z, hzS, hze⟩)))
          · rw [hF.F2 m hm a2 ha2 z hzB] at hze
            exact hF.F5 k hk x hx y hs m hm z hzB hze.symm
      · obtain ⟨z, hz, hze⟩ := mem_image.1 h
        rcases mem_insert.1 hz with rfl | hz
        · exact hSm y hs (mem_union_right _ (mem_singleton.2 hze.symm))
        rcases mem_union.1 hz with hzS | hzB
        · exact hSm y hs (mem_union_left _ (mem_union_left _ (mem_image.2 ⟨z, hzS, hze⟩)))
        · rw [hF.F2 l hl a1 ha1 z hzB] at hze
          exact hF.F5 k hk x hx y hs l hl z hzB hze.symm
    · exact disjoint_left.1 hβ (hxb y hb) hmem

end E1088
