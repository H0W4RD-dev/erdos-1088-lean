import E1088.CoreStep0

/-!
# Core Lemma: Steps 1 and 2 (manuscript Lemmas 8.5, 8.6)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- `Good`/`Cov` shape: `C_k` is covered by spheres about `a₁, a₂` with radii in a set of size
`≤ w`, the bisector `H(a₁,a₂)`, `Hyp`, and an exceptional set of size `≤ δ |C_k|`. -/
def CoverShape (S : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (w : ℕ) (δ : ℝ) (k : ℕ)
    (a1 a2 : ℝ^d) : Prop :=
  ∃ Ω : Finset ℝ, Ω.card ≤ w ∧ ∃ Ex ⊆ C k, (Ex.card : ℝ) ≤ δ * (C k).card ∧
    ∀ x ∈ C k, dist x a1 ∈ Ω ∨ dist x a2 ∈ Ω ∨ dist x a1 = dist x a2 ∨ Hyp S a1 a2 x ∨ x ∈ Ex

/-- Alternative (ii)_{k,k'} of Step 1. -/
def AltII (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (ε : ℝ) (k k' : ℕ)
    (a1 a2 : ℝ^d) : Prop :=
  (((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
    dist x a2 ∈ B.image (β k))).card : ℝ) < 2 * ε * (C k').card

/-- `Cov_{k'}(a₁, a₂)`. -/
def CovK (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (ε : ℝ) (k' : ℕ)
    (a1 a2 : ℝ^d) : Prop :=
  (((C k').filter fun x => ¬ LamK S B β k' a1 a2 x).card : ℝ) < 6 * ε * (C k').card

/-- G1 (b): label-disjoint pairs between disjoint sets of generic points. -/
theorem G1_pairs (n D h : ℕ) (X T P Q : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hPX : P ⊆ X) (hQX : Q ⊆ X)
    (hPQ : Disjoint P Q) (hPg : ∀ x ∈ P, x ∉ T ∧ Rainbow (insert x T))
    (hQg : ∀ x ∈ Q, x ∉ T ∧ Rainbow (insert x T)) :
    (((Q ×ˢ P).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) ≤
      4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) * (P.card + Q.card) := by
  classical
  have hY := G1_count n D h X T (P ∪ Q) hfree hD hh hTX hTn hT1 (union_subset hPX hQX)
    (fun x hx => by rcases mem_union.1 hx with h | h; exact hPg x h; exact hQg x h)
  have hsub : ((Q ×ˢ P).filter fun q => Disjoint (labels T q.1) (labels T q.2)) ⊆
      (((P ∪ Q) ×ˢ (P ∪ Q)).filter fun q => Disjoint (labels T q.1) (labels T q.2)) := by
    intro q hq
    obtain ⟨hqQP, hd⟩ := mem_filter.1 hq
    obtain ⟨h1, h2⟩ := mem_product.1 hqQP
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_union_right _ h1, mem_union_left _ h2⟩, hd⟩
  have hc : ((P ∪ Q).card : ℝ) = P.card + Q.card := by
    rw [card_union_of_disjoint hPQ]; push_cast; ring
  rw [← hc]
  exact (by exact_mod_cast card_le_card hsub : (_ : ℝ) ≤ _).trans hY

theorem card_coreT {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m) :
    (coreT S B a1 a2).card = (S ∪ B).card + 2 := by
  have h12 : a1 ≠ a2 := fun e => family_classes_disjoint hF hl hm hlm ha1 (e ▸ ha2)
  have h1 : a1 ∉ insert a2 (S ∪ B) := by
    simp only [mem_insert, not_or]; exact ⟨h12, (hF.F4 l hl a1 ha1).1⟩
  rw [coreT, card_insert_of_notMem h1, card_insert_of_notMem (hF.F4 m hm a2 ha2).1]

set_option maxHeartbeats 1000000 in
/-- **Step 1** (manuscript Lemma 8.5). -/
theorem core_step1 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) (M ε δ1 : ℝ) (hM0 : 0 < M)
    (hMk : ∀ k ∈ I, M ≤ (C k).card) (hε : 0 < ε) (hP2 : 2 * n ^ 2 * σ ≤ ε * M)
    (hδ1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M) + 3 * n ^ 2 * σ / M ≤ δ1)
    {l m k k' : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hlm : l ≠ m) (hk : k ∈ I) (hk' : k' ∈ I)
    (hkl : k ≠ l) (hkm : k ≠ m) (hk'l : k' ≠ l) (hk'm : k' ≠ m) (hkk : k ≠ k')
    {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m) (hT : Rainbow (coreT S B a1 a2))
    (hβk : Disjoint (B.image (β k)) (dists (coreT S B a1 a2)))
    (hβk' : Disjoint (B.image (β k')) (dists (coreT S B a1 a2))) :
    CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2 ∨
      AltII S B C β ε k k' a1 a2 := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  set T := coreT S B a1 a2 with hTdef
  set μ0 := LRcost (kG n) (D + 2) * h with hμ0
  have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  have hSB : (S ∪ B).card = r + (n - 4 - r) := by
    rw [card_union_of_disjoint hF.F1.1, hc.card, hB]
  have hTc : T.card = n - 2 := by rw [hTdef, card_coreT hF hl hm hlm ha1 ha2, hSB]; omega
  have hTX : T ⊆ X := by
    intro y hy
    simp only [hTdef, coreT, mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · exact hc.subW ((hF.Cne l hl).2 ha1)
    · exact hc.subW ((hF.Cne m hm).2 ha2)
    · rcases mem_union.1 hy with hy | hy
      · exact hc.subX hy
      · exact hBX hy
  have hT1 : T.Nonempty := ⟨a1, mem_insert_self _ _⟩
  have hTn : T.card + 2 = n := by omega
  have hkW : C k ⊆ W := (hF.Cne k hk).2
  have hk'W : C k' ⊆ W := (hF.Cne k' hk').2
  have hnotT : ∀ j ∈ I, j ≠ l → j ≠ m → ∀ x ∈ C j, x ∉ T := by
    intro j hj hjl hjm x hx hxT
    simp only [hTdef, coreT, mem_insert] at hxT
    rcases hxT with e | e | e
    · exact family_classes_disjoint hF hj hl hjl hx (e ▸ ha1)
    · exact family_classes_disjoint hF hj hm hjm hx (e ▸ ha2)
    · exact (hF.F4 j hj x hx).1 e
  -- labels of points of `C_j`
  have hlabT : ∀ j ∈ I, ∀ x ∈ C j, ∀ v ∈ labels T x,
      (∃ s ∈ S, v = dist x s) ∨ v ∈ B.image (β j) ∨ v = dist x a1 ∨ v = dist x a2 := by
    intro j hj x hx v hv
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hv
    simp only [hTdef, coreT, mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · rcases mem_union.1 hy with hs | hb
      · exact Or.inl ⟨y, hs, rfl⟩
      · exact Or.inr (Or.inl (mem_image.2 ⟨y, hb, (hF.F2 j hj x hx y hb).symm⟩))
  have hRem : ∀ R0 : Finset ℝ, (∀ t ∈ R0, 0 < t) →
      (((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0).card : ℝ) ≤ r * (R0.card * σ) := by
    intro R0 hR0
    refine le_trans ?_ (removal_bound hc R0 hR0)
    exact_mod_cast card_le_card fun x hx => by
      obtain ⟨hxC, s, hs, hxs⟩ := mem_filter.1 hx
      exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hkW hxC, hxs⟩⟩
  have hsmpos : ∀ t ∈ smRadii S a1 a2, 0 < t := by
    intro t ht
    simp only [smRadii, mem_union, mem_image, mem_singleton] at ht
    rcases ht with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | rfl
    · exact dist_pos.2 fun e => (hF.F4 l hl a1 ha1).1 (mem_union_left _ (e ▸ hs))
    · exact dist_pos.2 fun e => (hF.F4 m hm a2 ha2).1 (mem_union_left _ (e ▸ hs))
    · exact dist_pos.2 fun e => family_classes_disjoint hF hl hm hlm ha1 (e ▸ ha2)
  have hsmc : (smRadii S a1 a2).card ≤ 2 * r + 1 := by
    have e1 := card_union_le (S.image (dist a1) ∪ S.image (dist a2)) {dist a1 a2}
    have e2 := card_union_le (S.image (dist a1)) (S.image (dist a2))
    have e3 := card_image_le (s := S) (f := dist a1)
    have e4 := card_image_le (s := S) (f := dist a2)
    rw [hc.card] at e3 e4
    simp only [smRadii, card_singleton] at e1 ⊢
    omega
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hrn : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hSmk : ∀ j ∈ I, (((C j).filter fun x => Sm S a1 a2 x).card : ℝ) ≤ 2 * n ^ 2 * σ := by
    intro j hj
    have h1 : (((C j).filter fun x => Sm S a1 a2 x).card : ℝ) ≤
        r * ((smRadii S a1 a2).card * σ) := by
      refine le_trans ?_ (removal_bound hc _ hsmpos)
      exact_mod_cast card_le_card fun x hx => by
        obtain ⟨hxC, s, hs, hxs⟩ := mem_filter.1 hx
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF.Cne j hj).2 hxC, hxs⟩⟩
    have h2 : ((smRadii S a1 a2).card : ℝ) ≤ 2 * r + 1 := by exact_mod_cast hsmc
    have h3 : (r : ℝ) * ((smRadii S a1 a2).card * σ) ≤ r * ((2 * r + 1) * σ) := by gcongr
    have hr5 : (r : ℝ) + 5 ≤ n := by exact_mod_cast (show r + 5 ≤ n by omega)
    have hq : (r : ℝ) * (2 * r + 1) ≤ 2 * n ^ 2 := by nlinarith
    have h4 : (r : ℝ) * ((2 * r + 1) * σ) ≤ 2 * n ^ 2 * σ := by
      have := mul_le_mul_of_nonneg_right hq hσ0
      linarith [show (r : ℝ) * ((2 * r + 1) * σ) = r * (2 * r + 1) * σ by ring]
    linarith
  -- generic points
  set P := (C k).filter fun x => Rainbow (insert x T) with hP
  set Q := (C k').filter fun x => Rainbow (insert x T) with hQ
  set Q' := Q.filter fun w => Disjoint (labels T w) (B.image (β k)) with hQ'
  have hCk'M : M ≤ (C k').card := hMk k' hk'
  have hCkM : M ≤ (C k).card := hMk k hk
  by_cases hcase : ε * (C k').card ≤ Q'.card
  · left
    have hQ'pos : (0 : ℝ) < Q'.card := lt_of_lt_of_le (mul_pos hε (lt_of_lt_of_le hM0 hCk'M)) hcase
    have hQ'ne : Q'.Nonempty := by rw [← card_pos]; exact_mod_cast hQ'pos
    set LD := (Q' ×ˢ P).filter fun q => Disjoint (labels T q.1) (labels T q.2) with hLD
    have hLDc : (LD.card : ℝ) ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) := by
      have h1 := G1_pairs n D h X T P Q' hX.free hX.dim hX.half hTX hTn hT1
        ((filter_subset _ _).trans (hkW.trans hc.subW))
        (((filter_subset _ _).trans (filter_subset _ _)).trans (hk'W.trans hc.subW))
        (disjoint_left.2 fun x hxP hxQ => family_classes_disjoint hF hk hk' hkk
          (mem_filter.1 hxP).1 (mem_filter.1 (mem_filter.1 hxQ).1).1)
        (fun x hx => ⟨hnotT k hk hkl hkm x (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩)
        (fun x hx => ⟨hnotT k' hk' hk'l hk'm x (mem_filter.1 (mem_filter.1 hx).1).1,
          (mem_filter.1 (mem_filter.1 hx).1).2⟩)
      have e1 : (P.card : ℝ) ≤ (C k).card := by exact_mod_cast card_le_card (filter_subset _ _)
      have e2 : (Q'.card : ℝ) ≤ (C k').card :=
        by exact_mod_cast card_le_card ((filter_subset _ _).trans (filter_subset _ _))
      calc (LD.card : ℝ) ≤ 4 ^ (n - 2) * μ0 * (P.card + Q'.card) := h1
        _ ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) := by gcongr
    -- a point `w0 ∈ Q'` with few label-disjoint partners
    let part : ℝ^d → Finset (ℝ^d) := fun w => P.filter fun x => Disjoint (labels T w) (labels T x)
    obtain ⟨w0, hw0, hwmin⟩ := exists_min_image Q' (fun w => (part w).card) hQ'ne
    have hpart : (Q'.card : ℝ) * (part w0).card ≤ LD.card := by
      have : Q'.card * (part w0).card ≤ LD.card := by
        calc Q'.card * (part w0).card = ∑ _w ∈ Q', (part w0).card := by rw [sum_const, smul_eq_mul]
          _ ≤ ∑ w ∈ Q', (part w).card := sum_le_sum hwmin
          _ = LD.card := by
              rw [hLD, card_filter, sum_product]
              exact sum_congr rfl fun w _ => by simp only [part, card_filter]
      have h' : ((Q'.card * (part w0).card : ℕ) : ℝ) ≤ LD.card := by exact_mod_cast this
      rwa [Nat.cast_mul] at h'
    have hw0Q := (mem_filter.1 hw0).1
    have hw0C : w0 ∈ C k' := (mem_filter.1 hw0Q).1
    have hw0T : w0 ∉ T := hnotT k' hk' hk'l hk'm w0 hw0C
    have hw0dis : Disjoint (labels T w0) (B.image (β k)) := (mem_filter.1 hw0).2
    set R0 := S.image (dist w0) ∪ {dist w0 a1, dist w0 a2} with hR0
    have hR0pos : ∀ t ∈ R0, 0 < t := by
      intro t ht
      simp only [hR0, mem_union, mem_image, mem_insert, mem_singleton] at ht
      rcases ht with ⟨s, hs, rfl⟩ | rfl | rfl
      · exact dist_pos.2 fun e => hw0T (by simp [hTdef, coreT, e ▸ hs])
      · exact dist_pos.2 fun e => hw0T (by simp [hTdef, coreT, e])
      · exact dist_pos.2 fun e => hw0T (by simp [hTdef, coreT, e])
    have hR0c : R0.card ≤ r + 2 := by
      have e1 := card_union_le (S.image (dist w0)) {dist w0 a1, dist w0 a2}
      have e2 := card_image_le (s := S) (f := dist w0)
      have e3 : ({dist w0 a1, dist w0 a2} : Finset ℝ).card ≤ 2 := card_le_two
      rw [hc.card] at e2
      rw [hR0]; omega
    refine ⟨labels T w0 ∪ dists T ∪ B.image (β k), ?_,
      part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪ ((C k).filter fun x => Sm S a1 a2 x),
      ?_, ?_, ?_⟩
    · have e1 := card_union_le (labels T w0 ∪ dists T) (B.image (β k))
      have e2 := card_union_le (labels T w0) (dists T)
      have e3 : (labels T w0).card ≤ T.card := card_image_le
      have e4 := card_dists_le T
      have e5 := card_image_le (s := B) (f := β k)
      rw [hTc] at e3 e4
      rw [hB] at e5
      omega
    · intro x hx
      rcases mem_union.1 hx with hx | hx
      · rcases mem_union.1 hx with hx | hx
        · exact (mem_filter.1 (mem_filter.1 hx).1).1
        · exact (mem_filter.1 hx).1
      · exact (mem_filter.1 hx).1
    · -- size of the exceptional set
      have h1 : ((part w0).card : ℝ) ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card := by
        rw [le_div_iff₀ hQ'pos]; linarith
      have h2 := hRem R0 hR0pos
      have h3 := hSmk k hk
      have hR0r : (R0.card : ℝ) ≤ r + 2 := by exact_mod_cast hR0c
      have h4 : (r : ℝ) * (R0.card * σ) ≤ r * ((r + 2) * σ) := by gcongr
      have hex : ((part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪
          ((C k).filter fun x => Sm S a1 a2 x)).card : ℝ) ≤
          4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card + 3 * n ^ 2 * σ := by
        have c1 := card_union_le (part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0))
          ((C k).filter fun x => Sm S a1 a2 x)
        have c2 := card_union_le (part w0) ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0)
        have c3 : ((part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪
            ((C k).filter fun x => Sm S a1 a2 x)).card : ℝ) ≤ (part w0).card +
            ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0).card +
            ((C k).filter fun x => Sm S a1 a2 x).card := by exact_mod_cast c1.trans (by omega)
        have hrn2' : (r : ℝ) * ((r + 2) * σ) ≤ n ^ 2 * σ := by
          have hr5 : (r : ℝ) + 5 ≤ n := by exact_mod_cast (show r + 5 ≤ n by omega)
          have hq : (r : ℝ) * (r + 2) ≤ n ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right hq hσ0
          linarith [show (r : ℝ) * ((r + 2) * σ) = r * (r + 2) * σ by ring]
        linarith only [c3, h1, h2, h3, h4, hrn2']
      -- compare with `δ1 |C_k|`
      have hCkpos : (0 : ℝ) < (C k).card := lt_of_lt_of_le hM0 hCkM
      have hfrac : 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card ≤
          2 * 4 ^ (n - 2) * μ0 / (ε * M) * (C k).card := by
        have hA : (0 : ℝ) ≤ 4 ^ (n - 2) * μ0 := mul_nonneg (by positivity) hμ
        rw [div_le_iff₀ hQ'pos, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hε hM0)]
        have hCk0 : (0 : ℝ) ≤ (C k).card := Nat.cast_nonneg _
        have hCk'0 : (0 : ℝ) ≤ (C k').card := Nat.cast_nonneg _
        have f1 : ((C k).card : ℝ) * M ≤ (C k).card * (C k').card :=
          mul_le_mul_of_nonneg_left hCk'M hCk0
        have f2 : ((C k').card : ℝ) * M ≤ (C k).card * (C k').card := by
          have := mul_le_mul_of_nonneg_right hCkM hCk'0
          linarith [mul_comm ((C k').card : ℝ) M]
        have e2 : ((C k).card + (C k').card) * (ε * M) ≤ 2 * (C k).card * (ε * (C k').card) := by
          have := mul_le_mul_of_nonneg_left (add_le_add f1 f2) hε.le
          linarith [show (((C k).card : ℝ) + (C k').card) * (ε * M) =
            ε * ((C k).card * M + (C k').card * M) by ring,
            show 2 * ((C k).card : ℝ) * (ε * (C k').card) =
            ε * ((C k).card * (C k').card + (C k).card * (C k').card) by ring]
        have e3 : 2 * (C k).card * (ε * (C k').card) ≤ 2 * (C k).card * Q'.card := by
          have : (0 : ℝ) ≤ 2 * (C k).card := by linarith [hCk0]
          exact mul_le_mul_of_nonneg_left hcase this
        calc 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) * (ε * M)
            = 4 ^ (n - 2) * μ0 * (((C k).card + (C k').card) * (ε * M)) := by ring
          _ ≤ 4 ^ (n - 2) * μ0 * (2 * (C k).card * Q'.card) := by
              exact mul_le_mul_of_nonneg_left (e2.trans e3) hA
          _ = 2 * 4 ^ (n - 2) * μ0 * (C k).card * Q'.card := by ring
      have hlast : 3 * n ^ 2 * σ ≤ 3 * n ^ 2 * σ / M * (C k).card := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hM0]
        have : (0 : ℝ) ≤ 3 * n ^ 2 * σ := mul_nonneg (by positivity) hσ0
        nlinarith
      have hδ1' : 0 ≤ (C k).card := Nat.zero_le _
      calc ((part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪
            ((C k).filter fun x => Sm S a1 a2 x)).card : ℝ)
          ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card + 3 * n ^ 2 * σ := hex
        _ ≤ 2 * 4 ^ (n - 2) * μ0 / (ε * M) * (C k).card + 3 * n ^ 2 * σ / M * (C k).card := by
            linarith only [hfrac, hlast]
        _ = (2 * 4 ^ (n - 2) * μ0 / (ε * M) + 3 * n ^ 2 * σ / M) * (C k).card := by ring
        _ ≤ δ1 * (C k).card := mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg _)
    · -- the covering
      intro x hxC
      by_cases hgen : Rainbow (insert x T)
      · have hxP : x ∈ P := mem_filter.2 ⟨hxC, hgen⟩
        by_cases hpx : x ∈ part w0
        · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_left _ hpx)))))
        · have hnd : ¬ Disjoint (labels T w0) (labels T x) := fun hd => hpx (mem_filter.2 ⟨hxP, hd⟩)
          rw [not_disjoint_iff] at hnd
          obtain ⟨v, hvw, hvx⟩ := hnd
          rcases hlabT k hk x hxC v hvx with ⟨s, hs, rfl⟩ | hvb | rfl | rfl
          · -- `|xs| ∈ L_{w0}`
            rcases hlabT k' hk' w0 hw0C _ hvw with ⟨s', hs', he⟩ | hvb' | he | he
            · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _
                (mem_filter.2 ⟨hxC, s, hs, by
                  rw [he]; exact mem_union_left _ (mem_image.2 ⟨s', hs', rfl⟩)⟩))))))
            · obtain ⟨b, hb, hbe⟩ := mem_image.1 hvb'
              exact absurd hbe.symm (hF.F5 k hk x hxC s hs k' hk' b hb)
            · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _
                (mem_filter.2 ⟨hxC, s, hs, by rw [he]; simp [hR0]⟩))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _
                (mem_filter.2 ⟨hxC, s, hs, by rw [he]; simp [hR0]⟩))))))
          · exact absurd hvb (disjoint_left.1 hw0dis hvw)
          · exact Or.inl (mem_union_left _ (mem_union_left _ hvw))
          · exact Or.inr (Or.inl (mem_union_left _ (mem_union_left _ hvw)))
      · rcases core_step0 hF hl hm hk hkl hkm ha1 ha2 hT hβk hxC hgen with hL | hS
        · rcases hL with h | h | h | h
          · exact Or.inl (by
              rcases mem_union.1 h with h | h
              · exact mem_union_left _ (mem_union_right _ h)
              · exact mem_union_right _ h)
          · exact Or.inr (Or.inl (by
              rcases mem_union.1 h with h | h
              · exact mem_union_left _ (mem_union_right _ h)
              · exact mem_union_right _ h))
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_right _ (mem_filter.2 ⟨hxC, hS⟩)))))
  · right
    push Not at hcase
    have hsub : ((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
        dist x a2 ∈ B.image (β k))) ⊆ Q' ∪ ((C k').filter fun x => Sm S a1 a2 x) := by
      intro x hx
      obtain ⟨hxC, hnot⟩ := mem_filter.1 hx
      push Not at hnot
      obtain ⟨hnL, hn1, hn2⟩ := hnot
      by_cases hgen : Rainbow (insert x T)
      · refine mem_union_left _ (mem_filter.2 ⟨mem_filter.2 ⟨hxC, hgen⟩, ?_⟩)
        rw [disjoint_left]
        intro v hvx hvb
        rcases hlabT k' hk' x hxC v hvx with ⟨s, hs, rfl⟩ | hvb' | rfl | rfl
        · obtain ⟨b, hb, hbe⟩ := mem_image.1 hvb
          exact hF.F5 k' hk' x hxC s hs k hk b hb hbe.symm
        · obtain ⟨b, hb, hbe⟩ := mem_image.1 hvb
          obtain ⟨b', hb', hbe'⟩ := mem_image.1 hvb'
          exact hkk (hF.F3.1 k hk k' hk' b hb b' hb' (hbe.trans hbe'.symm)).1
        · exact hn1 hvb
        · exact hn2 hvb
      · rcases core_step0 hF hl hm hk' hk'l hk'm ha1 ha2 hT hβk' hxC hgen with hL | hS
        · exact absurd hL hnL
        · exact mem_union_right _ (mem_filter.2 ⟨hxC, hS⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le Q' ((C k').filter fun x => Sm S a1 a2 x)
    have h3 := hSmk k' hk'
    have h4 : (2 : ℝ) * n ^ 2 * σ ≤ ε * (C k').card := hP2.trans (by gcongr)
    have : (((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
        dist x a2 ∈ B.image (β k))).card : ℝ) ≤ Q'.card +
        ((C k').filter fun x => Sm S a1 a2 x).card := by exact_mod_cast h1.trans h2
    unfold AltII
    linarith

/-- **Step 2** (manuscript Lemma 8.6). -/
theorem core_step2 {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) (ε : ℝ) (hε : 0 < ε) (M : ℝ)
    (hM0 : 0 < M) {k' : ℕ} (hMk' : M ≤ (C k').card) {a1 a2 : ℝ^d}
    (J : Finset ℕ) (hJI : J ⊆ I) (hJ3 : 3 ≤ J.card)
    (hII : ∀ k ∈ J, AltII S B C β ε k k' a1 a2) : CovK S B C β ε k' a1 a2 := by
  classical
  set A := (C k').filter fun x => ¬ LamK S B β k' a1 a2 x with hA
  set N : ℝ := ((C k').card : ℝ) with hN
  have hNpos : 0 < N := lt_of_lt_of_le hM0 hMk'
  unfold CovK
  by_contra hcon
  push Not at hcon
  set U1 : ℕ → Finset (ℝ^d) := fun k => A.filter fun x => dist x a1 ∈ B.image (β k) with hU1
  set U2 : ℕ → Finset (ℝ^d) := fun k => A.filter fun x => dist x a2 ∈ B.image (β k) with hU2
  have hlow : ∀ k ∈ J, (A.card : ℝ) - 2 * ε * N < (U1 k).card + (U2 k).card := by
    intro k hk
    have h1 := hII k hk
    unfold AltII at h1
    have hsub : A ⊆ ((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
        dist x a2 ∈ B.image (β k))) ∪ (U1 k ∪ U2 k) := by
      intro x hx
      by_cases h1' : dist x a1 ∈ B.image (β k)
      · exact mem_union_right _ (mem_union_left _ (mem_filter.2 ⟨hx, h1'⟩))
      by_cases h2' : dist x a2 ∈ B.image (β k)
      · exact mem_union_right _ (mem_union_right _ (mem_filter.2 ⟨hx, h2'⟩))
      obtain ⟨hxC, hxL⟩ := mem_filter.1 hx
      refine mem_union_left _ (mem_filter.2 ⟨hxC, ?_⟩)
      rintro (h | h | h)
      · exact hxL h
      · exact h1' h
      · exact h2' h
    have e1 := (card_le_card hsub).trans (card_union_le _ _)
    have e2 := card_union_le (U1 k) (U2 k)
    have : (A.card : ℝ) ≤ ((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨
        dist x a1 ∈ B.image (β k) ∨ dist x a2 ∈ B.image (β k))).card +
        ((U1 k).card + (U2 k).card) := by
      exact_mod_cast e1.trans (by omega)
    linarith
  have hdisj : ∀ (f : ℝ^d → ℝ),
      ∑ k ∈ J, (A.filter fun x => f x ∈ B.image (β k)).card ≤ A.card := by
    intro f
    rw [← card_biUnion]
    · exact card_le_card (biUnion_subset.2 fun k _ => filter_subset _ _)
    · intro k hk k'' hk'' hne
      rw [Function.onFun, disjoint_left]
      intro x hx1 hx2
      obtain ⟨b, hb, hbe⟩ := mem_image.1 (mem_filter.1 hx1).2
      obtain ⟨b', hb', hbe'⟩ := mem_image.1 (mem_filter.1 hx2).2
      exact hne (hF.F3.1 k (hJI hk) k'' (hJI hk'') b hb b' hb' (hbe.trans hbe'.symm)).1
  have hs1 := hdisj (fun x => dist x a1)
  have hs2 := hdisj (fun x => dist x a2)
  have hJpos : 0 < J.card := by omega
  have hsum : (J.card : ℝ) * ((A.card : ℝ) - 2 * ε * N) < 2 * A.card := by
    calc (J.card : ℝ) * ((A.card : ℝ) - 2 * ε * N) = ∑ _k ∈ J, ((A.card : ℝ) - 2 * ε * N) := by
          rw [sum_const, nsmul_eq_mul]
      _ < ∑ k ∈ J, (((U1 k).card : ℝ) + (U2 k).card) :=
          sum_lt_sum_of_nonempty (card_pos.1 hJpos) hlow
      _ = ((∑ k ∈ J, (U1 k).card + ∑ k ∈ J, (U2 k).card : ℕ) : ℝ) := by
          push_cast; rw [sum_add_distrib]
      _ ≤ 2 * A.card := by
          have : ∑ k ∈ J, (U1 k).card + ∑ k ∈ J, (U2 k).card ≤ 2 * A.card := by
            simp only [hU1, hU2]; omega
          exact_mod_cast this
  have hJ3r : (3 : ℝ) ≤ J.card := by exact_mod_cast hJ3
  have hεN : 0 < ε * N := mul_pos hε hNpos
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  nlinarith

end E1088
