import E1088.CoreStep34
import E1088.Rplus
import E1088.TwoDist

/-!
# Theorem R⁺: Step A (manuscript Lemma 7.3)

A point `b ∈ W` with two big radii `ρ₁ ≠ ρ₂`: the auxiliary points `a` off both spheres and off
the kill locus of `b` are few. Constants differ from the paper (recorded in STATUS.md): we use
`Q = 2^27 n² E^{5k'}` and the branch threshold `θ = 2^22 n² E^{4k'} σ` (paper: `Q = 2^44 n⁴ E^{8k'}`,
`θ = Q^{1/2} σ`), with `E = D + 2` and `k' = C(n-2,2) + 3 + (n-4)`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem rainbow_subset {A B : Finset (ℝ^d)} (h : A ⊆ B) (hB : Rainbow B) : Rainbow A :=
  fun a ha a' ha' c hc c' hc' => hB a (h ha) a' (h ha') c (h hc) c' (h hc')

/-- `removal_bound` for a subset `S' ⊆ S`. -/
theorem removal_bound' {X S W : Finset (ℝ^d)} {r : ℕ} {σ : ℝ} (hc : Config X S W r σ)
    {S' : Finset (ℝ^d)} (hS' : S' ⊆ S) (T0 : Finset ℝ) (hT0 : ∀ t ∈ T0, 0 < t) :
    ((S'.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ) ≤ S'.card * (T0.card * σ) := by
  classical
  have hsub : (S'.biUnion fun s => W.filter fun x => dist x s ∈ T0) ⊆
      S'.biUnion fun s => T0.biUnion fun t => W.filter fun x => dist x s = t := by
    intro x hx
    obtain ⟨s, hs, hx⟩ := mem_biUnion.1 hx
    obtain ⟨hxW, ht⟩ := mem_filter.1 hx
    exact mem_biUnion.2 ⟨s, hs, mem_biUnion.2 ⟨_, ht, mem_filter.2 ⟨hxW, rfl⟩⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∀ s ∈ S', ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) ≤
      T0.card * σ := by
    intro s hs
    have := card_biUnion_le (s := T0) (t := fun t => W.filter fun x => dist x s = t)
    calc ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ)
        ≤ ∑ t ∈ T0, ((W.filter fun x => dist x s = t).card : ℝ) := by exact_mod_cast this
      _ ≤ ∑ _t ∈ T0, σ := sum_le_sum fun t ht => (hc.cap s (hS' hs) t (hT0 t ht)).le
      _ = T0.card * σ := by rw [sum_const, nsmul_eq_mul]
  calc ((S'.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ)
      ≤ ∑ s ∈ S', ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ _s ∈ S', (T0.card * σ) := sum_le_sum h2
    _ = S'.card * (T0.card * σ) := by rw [sum_const, nsmul_eq_mul]

/-- Points of `W` have injective distances to `S`, avoiding `D_S`. -/
theorem config_point_facts {X S W : Finset (ℝ^d)} {r : ℕ} {σ : ℝ} (hc : Config X S W r σ)
    {x : ℝ^d} (hx : x ∈ W) :
    (∀ y ∈ S, ∀ y' ∈ S, dist x y = dist x y' → y = y') ∧ ∀ y ∈ S, dist x y ∉ dists S := by
  have hxS : x ∉ S := fun h => disjoint_left.1 hc.disj hx h
  have hxR := hc.ext x hx
  refine ⟨fun y hy y' hy' h => ?_, fun y hy h => ?_⟩
  · have hxy : x ≠ y := fun e => hxS (e ▸ hy)
    have hxy' : x ≠ y' := fun e => hxS (e ▸ hy')
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) x (mem_insert_self _ _) y'
      (mem_insert_of_mem hy') hxy hxy' h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 hxy'
  · obtain ⟨q, hq, hqe⟩ := mem_image.1 h
    obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
    have hxy : x ≠ y := fun e => hxS (e ▸ hy)
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) q.1
      (mem_insert_of_mem hq1) q.2 (mem_insert_of_mem hq2) hxy hq12 hqe.symm with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxS (h1 ▸ hq1)
    · exact hxS (h1 ▸ hq2)

/-- `k' = C(n-2,2) + 3 + (n-4)`. -/
def kA (n : ℕ) : ℕ := (n - 2).choose 2 + 3 + (n - 4)

/-- `Q = 2^27 n² E^{5k'}`. -/
noncomputable def QA (n D : ℕ) : ℝ := 2 ^ 27 * n ^ 2 * (((D + 2 : ℕ) : ℝ) ^ kA n) ^ 5

/-- The set `T(a) = {b, a} ∪ S'`. -/
noncomputable def TA (S' : Finset (ℝ^d)) (a b : ℝ^d) : Finset (ℝ^d) := insert b (insert a S')

/-- The radii of `Sm_ν(a)`. -/
noncomputable def SmA (S' : Finset (ℝ^d)) (a b : ℝ^d) (ρ : ℝ) : Finset ℝ :=
  insert ρ (insert (dist a b) (S'.image (dist b) ∪ S'.image (dist a)))

/-- The covering property `(7.4)` for one class `C`, with cut-off `16 K'`. -/
def CoverA (S' C : Finset (ℝ^d)) (a b : ℝ^d) (ρ1 ρ2 : ℝ) (K' : ℝ) : Prop :=
  ∃ t : ℝ, 16 * K' * (((C.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
    ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤ C.card

/-- The common setting of Step A for one auxiliary point `a`. -/
structure StepACtx (n D h j : ℕ) (X S W S' : Finset (ℝ^d)) (σ : ℝ) (a b : ℝ^d) (ρ1 ρ2 : ℝ) :
    Prop where
  hn : 4 ≤ n
  amb : Ambient n D h X
  conf : Config X S W j σ
  hσ : smin n D h ≤ σ
  sub : S' ⊆ S
  card : S'.card = n - 4
  hb : b ∈ W
  ha : a ∈ W
  hab : a ≠ b
  hρ : ρ1 ≠ ρ2
  ρ1pos : 0 < ρ1
  ρ2pos : 0 < ρ2
  ρ1R : ρ1 ∉ Rb S b
  ρ2R : ρ2 ∉ Rb S b
  a1 : dist a b ≠ ρ1
  a2 : dist a b ≠ ρ2
  rb : Rainbow (insert a (insert b S))
  aS : ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2

section StepA

variable {n D h j : ℕ} {X S W S' : Finset (ℝ^d)} {σ : ℝ} {a b : ℝ^d} {ρ1 ρ2 : ℝ}

theorem StepACtx.notS (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {x : ℝ^d} (hx : x ∈ W) :
    x ∉ S := fun h => disjoint_left.1 cx.conf.disj hx h

theorem StepACtx.card_T (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) :
    (TA S' a b).card = n - 2 := by
  have haS : a ∉ S' := fun h => cx.notS cx.ha (cx.sub h)
  have hbS : b ∉ insert a S' := by
    simp only [mem_insert, not_or]; exact ⟨cx.hab.symm, fun h => cx.notS cx.hb (cx.sub h)⟩
  rw [TA, card_insert_of_notMem hbS, card_insert_of_notMem haS, cx.card]
  have := cx.hn; omega

theorem StepACtx.rainbow_T (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) :
    Rainbow (TA S' a b) := by
  refine rainbow_subset ?_ cx.rb
  intro y hy
  simp only [TA, mem_insert] at hy ⊢
  rcases hy with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (cx.sub h))

theorem StepACtx.T_sub (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) : TA S' a b ⊆ X := by
  intro y hy
  simp only [TA, mem_insert] at hy
  rcases hy with h | h | h
  · exact h ▸ cx.conf.subW cx.hb
  · exact h ▸ cx.conf.subW cx.ha
  · exact cx.conf.subX (cx.sub h)

/-- `D_T ⊆ D_{S'} ∪ {|bs|} ∪ {|as|} ∪ {|ab|}`. -/
theorem dists_TA_subset (S' : Finset (ℝ^d)) (a b : ℝ^d) :
    dists (TA S' a b) ⊆ dists S' ∪ S'.image (dist a) ∪ (insert a S').image (dist b) := by
  intro v hv
  rcases mem_union.1 (dists_insert_subset _ b hv) with h | h
  · rcases mem_union.1 (dists_insert_subset _ a h) with h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
  · exact mem_union_right _ h

theorem dists_subset_of_subset {A B : Finset (ℝ^d)} (h : A ⊆ B) : dists A ⊆ dists B := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hv
  obtain ⟨h1, h2, h12⟩ := mem_offDiag.1 hq
  exact mem_image.2 ⟨q, mem_offDiag.2 ⟨h h1, h h2, h12⟩, rfl⟩

/-- Step 1: `ρ_ν ∉ D_T`. -/
theorem StepACtx.rho_notin (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ}
    (hρR : ρ ∉ Rb S b) (hab : dist a b ≠ ρ) (has : ∀ s ∈ S', dist a s ≠ ρ) :
    ρ ∉ dists (TA S' a b) := by
  intro h
  rcases mem_union.1 (dists_TA_subset S' a b h) with h | h
  · rcases mem_union.1 h with h | h
    · exact hρR (mem_union_left _ (dists_subset_of_subset cx.sub h))
    · obtain ⟨s, hs, hse⟩ := mem_image.1 h
      exact has s hs hse
  · obtain ⟨z, hz, hze⟩ := mem_image.1 h
    rcases mem_insert.1 hz with ez | hz
    · rw [ez, dist_comm] at hze; exact hab hze
    · exact hρR (mem_union_right _ (mem_image.2 ⟨z, cx.sub hz, hze⟩))

theorem StepACtx.SmA_pos (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ t ∈ SmA S' a b ρ, 0 < t := by
  intro t ht
  simp only [SmA, mem_insert, mem_union, mem_image] at ht
  rcases ht with rfl | rfl | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · exact hρ
  · exact dist_pos.2 cx.hab
  · exact dist_pos.2 fun e => cx.notS cx.hb (e ▸ cx.sub hs)
  · exact dist_pos.2 fun e => cx.notS cx.ha (e ▸ cx.sub hs)

theorem StepACtx.SmA_card (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) (ρ : ℝ) :
    (SmA S' a b ρ).card ≤ 2 * (n - 4) + 2 := by
  have e1 := card_insert_le ρ (insert (dist a b) (S'.image (dist b) ∪ S'.image (dist a)))
  have e2 := card_insert_le (dist a b) (S'.image (dist b) ∪ S'.image (dist a))
  have e3 := card_union_le (S'.image (dist b)) (S'.image (dist a))
  have e4 := card_image_le (s := S') (f := dist b)
  have e5 := card_image_le (s := S') (f := dist a)
  rw [cx.card] at e4 e5
  simp only [SmA]
  omega

/-- Step 2: a point `x` of `C_ν = W ∩ Sph(b, ρ_ν)` that is not `T`-generic lies on a sphere
about `a` with radius in `D_T ∪ {ρ_ν}`, on a bisector `H(a, s)`, or in `Sm_ν(a)`. -/
theorem StepACtx.step2 (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρT : ρ ∉ dists (TA S' a b)) (hab : dist a b ≠ ρ) {x : ℝ^d} (hx : x ∈ W)
    (hxb : dist x b = ρ) (hng : ¬ Rainbow (insert x (TA S' a b))) :
    dist x a ∈ dists (TA S' a b) ∪ {ρ} ∨ (∃ s ∈ S', dist x a = dist x s) ∨
      (∃ s ∈ S', dist x s ∈ SmA S' a b ρ) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hxS := cx.notS hx
  have hxb' : x ≠ b := fun e => by rw [e, dist_self] at hxb; linarith
  have hxa : x ≠ a := fun e => hab (by rw [← e]; exact hxb)
  have hxT : x ∉ TA S' a b := by
    simp only [TA, mem_insert, not_or]; exact ⟨hxb', hxa, fun h => hxS (cx.sub h)⟩
  obtain ⟨hinjS, houtS⟩ := config_point_facts cx.conf hx
  have hxaT : dist x a ∉ dists (TA S' a b) := fun h => h1 (mem_union_left _ h)
  have hxaρ : dist x a ≠ ρ := fun h => h1 (mem_union_right _ (mem_singleton.2 h))
  have hSm : ∀ s ∈ S', dist x s ≠ ρ ∧ dist x s ≠ dist a b ∧ (∀ s' ∈ S', dist x s ≠ dist b s') ∧
      ∀ s' ∈ S', dist x s ≠ dist a s' := by
    intro s hs
    have := h3 s hs
    simp only [SmA, mem_insert, mem_union, mem_image, not_or, not_exists, not_and] at this
    obtain ⟨e1, e2, e3, e4⟩ := this
    exact ⟨e1, e2, fun s' hs' h => e3 s' hs' h.symm, fun s' hs' h => e4 s' hs' h.symm⟩
  refine hng (rainbow_insert_one _ x cx.rainbow_T hxT ?_ ?_)
  · intro y hy y' hy' hyy
    simp only [TA, mem_insert] at hy hy'
    rcases hy with ey | ey | hy <;> rcases hy' with ey' | ey' | hy'
    · exact ey.trans ey'.symm
    · rw [ey, ey', hxb] at hyy; exact absurd hyy.symm hxaρ
    · rw [ey, hxb] at hyy; exact absurd hyy.symm (hSm y' hy').1
    · rw [ey, ey', hxb] at hyy; exact absurd hyy hxaρ
    · exact ey.trans ey'.symm
    · rw [ey] at hyy; exact absurd hyy (h2 y' hy')
    · rw [ey', hxb] at hyy; exact absurd hyy (hSm y hy).1
    · rw [ey'] at hyy; exact absurd hyy.symm (h2 y hy)
    · exact hinjS y (cx.sub hy) y' (cx.sub hy') hyy
  · intro y hy hmem
    simp only [TA, mem_insert] at hy
    rcases hy with ey | ey | hy
    · rw [ey, hxb] at hmem; exact hρT hmem
    · rw [ey] at hmem; exact hxaT hmem
    · rcases mem_union.1 (dists_TA_subset S' a b hmem) with h | h
      · rcases mem_union.1 h with h | h
        · exact houtS y (cx.sub hy) (dists_subset_of_subset cx.sub h)
        · obtain ⟨s', hs', he⟩ := mem_image.1 h
          exact (hSm y hy).2.2.2 s' hs' he.symm
      · obtain ⟨z, hz, hze⟩ := mem_image.1 h
        rcases mem_insert.1 hz with ez | hz
        · rw [ez, dist_comm] at hze; exact (hSm y hy).2.1 hze.symm
        · exact (hSm y hy).2.2.1 z hz hze.symm

end StepA

end E1088
