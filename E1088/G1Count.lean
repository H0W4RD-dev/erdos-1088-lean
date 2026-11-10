import E1088.G1

/-!
# G1, counting forms (manuscript Corollary 5.3 (a), (c))

(a) For `Y` a set of `T`-generic points of `X`, the ordered label-disjoint pairs number at most
`4^{n-2} μ₀ |Y|` with `μ₀ = LRcost k_G (D+2) · h` (the random colouring of the manuscript is
replaced by an exact average over all colourings).
(c) Degree form: if every label `v` lies in at most `|Y|/(4(n-2))` label sets, then
`3|Y| ≤ 4(4^{n-2} μ₀ + 1)`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- Label set `L_x = {|xt| : t ∈ T}`. -/
noncomputable def labels (T : Finset (ℝ^d)) (x : ℝ^d) : Finset ℝ := T.image (dist x)

/-- Number of red sets `R ⊆ V` containing `A` and missing `B` (`A, B ⊆ V` disjoint). -/
theorem card_colourings {α : Type*} [DecidableEq α] (V A B : Finset α) (hA : A ⊆ V)
    (hB : B ⊆ V) (hAB : Disjoint A B) :
    (V.powerset.filter fun R => A ⊆ R ∧ Disjoint B R).card = 2 ^ (V.card - A.card - B.card) := by
  have hc : (V \ (A ∪ B)).card = V.card - A.card - B.card := by
    rw [card_sdiff_of_subset (union_subset hA hB), card_union_of_disjoint hAB]; omega
  rw [← hc, ← card_powerset]
  refine card_nbij' (fun R => R \ A) (fun S => S ∪ A) ?_ ?_ ?_ ?_
  · intro R hR
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset] at hR
    obtain ⟨hRV, hAR, hBR⟩ := hR
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_sdiff, coe_union]
    intro x hx
    obtain ⟨hxR, hxA⟩ := hx
    refine ⟨hRV hxR, fun h => ?_⟩
    rcases h with h | h
    · exact hxA h
    · exact disjoint_left.1 hBR h hxR
  · intro S hS
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_sdiff, coe_union] at hS
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset]
    refine ⟨union_subset (fun x hx => (hS (mem_coe.2 hx)).1) hA, subset_union_right, ?_⟩
    rw [disjoint_left]
    intro x hxB hx
    rcases mem_union.1 hx with h | h
    · exact (hS (mem_coe.2 h)).2 (Or.inr hxB)
    · exact disjoint_left.1 hAB h hxB
  · intro R hR
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset] at hR
    exact sdiff_union_of_subset hR.2.1
  · intro S hS
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_sdiff, coe_union] at hS
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hxA⟩
      · exact h
      · exact absurd h hxA
    · intro hx
      exact ⟨Or.inl hx, fun hxA => (hS (mem_coe.2 hx)).2 (Or.inl hxA)⟩

theorem card_labels (T : Finset (ℝ^d)) (x : ℝ^d) (hxT : x ∉ T) (hr : Rainbow (insert x T)) :
    (labels T x).card = T.card := by
  unfold labels
  refine card_image_of_injOn fun t ht t' ht' h => ?_
  by_contra hne
  have hxt : x ≠ t := fun e => hxT (e ▸ ht)
  have hxt' : x ≠ t' := fun e => hxT (e ▸ ht')
  rcases hr x (mem_insert_self _ _) t (mem_insert_of_mem ht) x (mem_insert_self _ _) t'
      (mem_insert_of_mem ht') hxt hxt' h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact hne h2
  · exact hxt' h1

/-- **G1 (a)**: ordered label-disjoint pairs in `Y`. -/
theorem G1_count (n D h : ℕ) (X T Y : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hYX : Y ⊆ X)
    (hYg : ∀ x ∈ Y, x ∉ T ∧ Rainbow (insert x T)) :
    (((Y ×ˢ Y).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) ≤
      4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) * Y.card := by
  classical
  set μ0 := LRcost (kG n) (D + 2) * h with hμ0
  have hμ0 : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  set V := Y.biUnion (labels T) with hV
  set LD := (Y ×ˢ Y).filter fun q => Disjoint (labels T q.1) (labels T q.2) with hLD
  have hlab : ∀ x ∈ Y, (labels T x).card = n - 2 := fun x hx => by
    rw [card_labels T x (hYg x hx).1 (hYg x hx).2]; omega
  have hlabV : ∀ x ∈ Y, labels T x ⊆ V := fun x hx => subset_biUnion_of_mem _ hx
  rcases LD.eq_empty_or_nonempty with hLDe | ⟨q0, hq0⟩
  · rw [hLDe, card_empty, Nat.cast_zero]; positivity
  -- `|V| ≥ 2(n-2)`
  have hV2 : 2 * (n - 2) ≤ V.card := by
    obtain ⟨hq0Y, hq0d⟩ := mem_filter.1 hq0
    obtain ⟨h1, h2⟩ := mem_product.1 hq0Y
    have := card_le_card (union_subset (hlabV _ h1) (hlabV _ h2))
    rw [card_union_of_disjoint hq0d, hlab _ h1, hlab _ h2] at this
    omega
  -- each colouring gives a small product
  have hprod : ∀ R ∈ V.powerset, (((Y.filter fun x => labels T x ⊆ R).card *
      (Y.filter fun w => Disjoint (labels T w) R).card : ℕ) : ℝ) ≤ μ0 * Y.card := by
    intro R _
    set P := Y.filter fun x => labels T x ⊆ R
    set Q := Y.filter fun w => Disjoint (labels T w) R
    have hmin := G1_bip n D h X T P Q hfree hD hh hTX hTn hT1
      ((filter_subset _ _).trans hYX) ((filter_subset _ _).trans hYX)
      (fun x hx => hYg x (mem_filter.1 hx).1) (fun w hw => hYg w (mem_filter.1 hw).1)
      (fun x hx w hw t ht t' ht' heq => by
        have hxR := (mem_filter.1 hx).2
        have hwR := (mem_filter.1 hw).2
        have h1 : dist x t ∈ R := hxR (mem_image_of_mem _ ht)
        have h2 : dist w t' ∈ labels T w := mem_image_of_mem _ ht'
        exact disjoint_left.1 hwR h2 (heq ▸ h1))
    have hP : (P.card : ℝ) ≤ Y.card := by exact_mod_cast card_le_card (filter_subset _ _)
    have hQ : (Q.card : ℝ) ≤ Y.card := by exact_mod_cast card_le_card (filter_subset _ _)
    push_cast
    rcases le_total P.card Q.card with hle | hle
    · rw [min_eq_left (by exact_mod_cast hle)] at hmin
      calc (P.card : ℝ) * Q.card ≤ μ0 * Q.card :=
            mul_le_mul_of_nonneg_right hmin (Nat.cast_nonneg _)
        _ ≤ μ0 * Y.card := mul_le_mul_of_nonneg_left hQ hμ0
    · rw [min_eq_right (by exact_mod_cast hle)] at hmin
      calc (P.card : ℝ) * Q.card ≤ P.card * μ0 :=
            mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg _)
        _ ≤ Y.card * μ0 := mul_le_mul_of_nonneg_right hP hμ0
        _ = μ0 * Y.card := mul_comm _ _
  -- double counting
  have hdc : ∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
      (Y.filter fun w => Disjoint (labels T w) R).card) =
      ∑ q ∈ Y ×ˢ Y, (V.powerset.filter fun R => labels T q.1 ⊆ R ∧
        Disjoint (labels T q.2) R).card := by
    have hR : ∀ R, (Y.filter fun x => labels T x ⊆ R).card *
        (Y.filter fun w => Disjoint (labels T w) R).card =
        ((Y ×ˢ Y).filter fun q => labels T q.1 ⊆ R ∧ Disjoint (labels T q.2) R).card := by
      intro R
      rw [← card_product]
      congr 1
      ext q
      simp only [mem_product, mem_filter]
      tauto
    rw [Finset.sum_congr rfl (fun R _ => hR R)]
    simp only [card_filter]
    exact Finset.sum_comm
  have hlow : LD.card * 2 ^ (V.card - 2 * (n - 2)) ≤
      ∑ q ∈ Y ×ˢ Y, (V.powerset.filter fun R => labels T q.1 ⊆ R ∧
        Disjoint (labels T q.2) R).card := by
    calc LD.card * 2 ^ (V.card - 2 * (n - 2))
        = ∑ q ∈ LD, (V.powerset.filter fun R => labels T q.1 ⊆ R ∧
            Disjoint (labels T q.2) R).card := by
          rw [card_eq_sum_ones, sum_mul]
          refine sum_congr rfl fun q hq => ?_
          obtain ⟨hqY, hqd⟩ := mem_filter.1 hq
          obtain ⟨h1, h2⟩ := mem_product.1 hqY
          rw [card_colourings V _ _ (hlabV _ h1) (hlabV _ h2) hqd, hlab _ h1, hlab _ h2]
          rw [one_mul]; congr 1; omega
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  have hup : (∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
      (Y.filter fun w => Disjoint (labels T w) R).card : ℕ) : ℝ) ≤
      2 ^ V.card * (μ0 * Y.card) := by
    push_cast
    calc ∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
          ((Y.filter fun w => Disjoint (labels T w) R).card : ℝ))
        ≤ ∑ _R ∈ V.powerset, μ0 * Y.card := by
          refine sum_le_sum fun R hR => ?_
          have := hprod R hR; push_cast at this; exact this
      _ = 2 ^ V.card * (μ0 * Y.card) := by rw [sum_const, card_powerset, nsmul_eq_mul]; push_cast; ring
  have hkey : (LD.card : ℝ) * 2 ^ (V.card - 2 * (n - 2)) ≤ 2 ^ V.card * (μ0 * Y.card) := by
    have : ((LD.card * 2 ^ (V.card - 2 * (n - 2)) : ℕ) : ℝ) ≤
        ((∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
          (Y.filter fun w => Disjoint (labels T w) R).card) : ℕ) : ℝ) := by
      exact_mod_cast (hlow.trans hdc.symm.le)
    push_cast at this
    exact this.trans (by exact_mod_cast hup)
  have hsplit : (2 : ℝ) ^ V.card = 2 ^ (V.card - 2 * (n - 2)) * 4 ^ (n - 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
  rw [hsplit] at hkey
  have hpos : (0 : ℝ) < 2 ^ (V.card - 2 * (n - 2)) := by positivity
  have : (LD.card : ℝ) * 2 ^ (V.card - 2 * (n - 2)) ≤
      (4 ^ (n - 2) * μ0 * Y.card) * 2 ^ (V.card - 2 * (n - 2)) := by nlinarith
  exact le_of_mul_le_mul_right this hpos

/-- **G1 (c), degree form.** If every label lies in at most `|Y|/(4(n-2))` label sets, then
`3|Y| ≤ 4 · 4^{n-2} μ₀` (slightly stronger than the manuscript's `|Y| ≤ (4/3)(4^{n-2}μ + 1)`). -/
theorem G1_degree (n D h : ℕ) (X T Y : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hYX : Y ⊆ X)
    (hYg : ∀ x ∈ Y, x ∉ T ∧ Rainbow (insert x T))
    (hdeg : ∀ v : ℝ, 4 * (n - 2) * (Y.filter fun x => v ∈ labels T x).card ≤ Y.card) :
    3 * (Y.card : ℝ) ≤ 4 * (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h)) := by
  classical
  set μ0 := LRcost (kG n) (D + 2) * h with hμ0
  set V := Y.biUnion (labels T) with hV
  set LD := (Y ×ˢ Y).filter fun q => Disjoint (labels T q.1) (labels T q.2) with hLD
  set Yv : ℝ → Finset (ℝ^d) := fun v => Y.filter fun x => v ∈ labels T x with hYv
  set Sh := V.biUnion fun v => Yv v ×ˢ Yv v with hSh
  have hn2 : 1 ≤ n - 2 := by have := card_pos.2 hT1; omega
  have hlab : ∀ x ∈ Y, (labels T x).card = n - 2 := fun x hx => by
    rw [card_labels T x (hYg x hx).1 (hYg x hx).2]; omega
  have hcover : Y ×ˢ Y ⊆ LD ∪ Sh := by
    intro q hq
    by_cases hd : Disjoint (labels T q.1) (labels T q.2)
    · exact mem_union_left _ (mem_filter.2 ⟨hq, hd⟩)
    · obtain ⟨h1, h2⟩ := mem_product.1 hq
      rw [not_disjoint_iff] at hd
      obtain ⟨v, hv1, hv2⟩ := hd
      exact mem_union_right _ (mem_biUnion.2 ⟨v, mem_biUnion.2 ⟨q.1, h1, hv1⟩,
        mem_product.2 ⟨mem_filter.2 ⟨h1, hv1⟩, mem_filter.2 ⟨h2, hv2⟩⟩⟩)
  have hsumdeg : ∑ v ∈ V, (Yv v).card = (n - 2) * Y.card := by
    have : ∑ v ∈ V, (Yv v).card = ∑ x ∈ Y, (V.filter fun v => v ∈ labels T x).card := by
      simp only [hYv, card_filter]
      exact Finset.sum_comm
    rw [this]
    have h2 : ∀ x ∈ Y, (V.filter fun v => v ∈ labels T x).card = n - 2 := by
      intro x hx
      rw [← hlab x hx]
      congr 1
      ext v
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨subset_biUnion_of_mem _ hx h, h⟩⟩
    rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
  have hSh : 4 * (n - 2) * Sh.card ≤ (n - 2) * Y.card * Y.card := by
    have h1 : Sh.card ≤ ∑ v ∈ V, (Yv v).card * (Yv v).card := by
      refine card_biUnion_le.trans (le_of_eq ?_)
      exact sum_congr rfl fun v _ => card_product _ _
    calc 4 * (n - 2) * Sh.card ≤ ∑ v ∈ V, (4 * (n - 2) * (Yv v).card) * (Yv v).card := by
          calc 4 * (n - 2) * Sh.card ≤ 4 * (n - 2) * ∑ v ∈ V, (Yv v).card * (Yv v).card :=
                Nat.mul_le_mul_left _ h1
            _ = ∑ v ∈ V, (4 * (n - 2) * (Yv v).card) * (Yv v).card := by
                rw [mul_sum]; exact sum_congr rfl fun v _ => by ring
      _ ≤ ∑ v ∈ V, Y.card * (Yv v).card := sum_le_sum fun v _ => Nat.mul_le_mul_right _ (hdeg v)
      _ = Y.card * ((n - 2) * Y.card) := by rw [← mul_sum, hsumdeg]
      _ = (n - 2) * Y.card * Y.card := by ring
  have hLDc := G1_count n D h X T Y hfree hD hh hTX hTn hT1 hYX hYg
  have h1 : Y.card * Y.card ≤ LD.card + Sh.card := by
    rw [← card_product]; exact (card_le_card hcover).trans (card_union_le _ _)
  have h1r : (Y.card : ℝ) * Y.card ≤ LD.card + Sh.card := by exact_mod_cast h1
  have h2r : 4 * ((n - 2 : ℕ) : ℝ) * Sh.card ≤ ((n - 2 : ℕ) : ℝ) * Y.card * Y.card := by
    exact_mod_cast hSh
  have hn2r : (1 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast hn2
  have h3 : 4 * (Sh.card : ℝ) ≤ Y.card * Y.card := by
    have : ((n - 2 : ℕ) : ℝ) * (4 * Sh.card) ≤ ((n - 2 : ℕ) : ℝ) * (Y.card * Y.card) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  rcases Nat.eq_zero_or_pos Y.card with h0 | hpos
  · rw [h0, Nat.cast_zero]
    have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
    have := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (n - 2)) hμ
    linarith
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hpos
  have : 3 * (Y.card : ℝ) * Y.card ≤ 4 * (4 ^ (n - 2) * μ0) * Y.card := by nlinarith
  exact le_of_mul_le_mul_right this hYpos

end E1088
