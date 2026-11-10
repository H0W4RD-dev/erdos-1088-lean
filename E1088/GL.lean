import E1088.Rank

/-!
# The Gavinsky–Lovett cleaning lemma (tool GL)

If `B` restricted to `X × Y` has rank `≤ R` (`R ≥ 1`) and at most `|X||Y|/(16R)` nonzero
entries, then `B` vanishes on some `X' × Y'` with `|X'| ≥ |X|/2`, `|Y'| ≥ |Y|/2`.
Proof as recalled in round9/01: discard heavy rows/columns, take a maximum induced matching
(its size is `≤ rank`), discard its neighbourhood.
-/

set_option linter.unusedSectionVars false

open Matrix Finset

namespace E1088

variable {K : Type*} [Field K] [DecidableEq K] {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The rank of `B` restricted to the rectangle `X × Y`. -/
noncomputable def rankOn (B : α → β → K) (X : Finset α) (Y : Finset β) : ℕ :=
  (Matrix.of fun (i : X) (j : Y) => B i j).rank

omit [DecidableEq K] [DecidableEq α] [DecidableEq β] in
/-- Rank is monotone under passing to sub-rectangles. -/
theorem rankOn_mono (B : α → β → K) {X X' : Finset α} {Y Y' : Finset β} (hX : X' ⊆ X)
    (hY : Y' ⊆ Y) : rankOn B X' Y' ≤ rankOn B X Y := by
  unfold rankOn
  have : (Matrix.of fun (i : X') (j : Y') => B i j) =
      (Matrix.of fun (i : X) (j : Y) => B i j).submatrix (fun i => ⟨i.1, hX i.2⟩)
        (fun j => ⟨j.1, hY j.2⟩) := by ext; simp
  rw [this]; exact rank_submatrix_le' _ _ _

/-- The set of nonzero entries of `B` in `X × Y`. -/
def supp (B : α → β → K) (X : Finset α) (Y : Finset β) : Finset (α × β) :=
  (X ×ˢ Y).filter fun p => B p.1 p.2 ≠ 0

/-- An induced matching of size `t` gives rank `≥ t`. -/
theorem card_le_rankOn_of_induced (B : α → β → K) (X : Finset α) (Y : Finset β)
    (F : Finset (α × β)) (hF : F ⊆ X ×ˢ Y) (hind : ∀ p ∈ F, ∀ q ∈ F, B p.1 q.2 ≠ 0 ↔ p = q) :
    #F ≤ rankOn B X Y := by
  classical
  have hmem : ∀ p ∈ F, p.1 ∈ X ∧ p.2 ∈ Y := fun p hp => mem_product.1 (hF hp)
  let G : Matrix F F K := (Matrix.of fun (i : X) (j : Y) => B i j).submatrix
    (fun p => ⟨p.1.1, (hmem p.1 p.2).1⟩) (fun q => ⟨q.1.2, (hmem q.1 q.2).2⟩)
  have hG : G = diagonal fun p => B p.1.1 p.1.2 := by
    ext p q
    by_cases h : p = q
    · subst h; simp [G]
    · have : ¬ (B p.1.1 q.1.2 ≠ 0) := fun h' =>
        h (Subtype.ext ((hind p.1 p.2 q.1 q.2).1 h'))
      simp only [ne_eq, not_not] at this
      simp [G, h, this]
  have h1 : G.rank = #F := by
    rw [hG, rank_diagonal]
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (p := fun p : F => B p.1.1 p.1.2 ≠ 0)
      fun p => ((hind p.1 p.2 p.1 p.2).2 rfl))]
    simp
  rw [← h1]
  exact rank_submatrix_le' _ _ _

omit [DecidableEq α] [DecidableEq β] in
/-- Row sums of the support. -/
theorem card_supp_eq_sum (B : α → β → K) (X : Finset α) (Y : Finset β) :
    #(supp B X Y) = ∑ i ∈ X, #(Y.filter fun j => B i j ≠ 0) := by
  unfold supp
  rw [card_filter, sum_product]
  exact sum_congr rfl fun i _ => (card_filter _ _).symm

omit [DecidableEq α] [DecidableEq β] in
/-- Column sums of the support. -/
theorem card_supp_eq_sum' (B : α → β → K) (X : Finset α) (Y : Finset β) :
    #(supp B X Y) = ∑ j ∈ Y, #(X.filter fun i => B i j ≠ 0) := by
  unfold supp
  rw [card_filter, sum_product_right]
  exact sum_congr rfl fun i _ => (card_filter _ _).symm

/-- Heavy rows are few. -/
theorem heavy_rows (B : α → β → K) (X : Finset α) (Y : Finset β) (R : ℕ)
    (hnz : 16 * R * #(supp B X Y) ≤ #X * #Y) (hY : 0 < #Y) :
    4 * #(X.filter fun i => ¬ 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y) ≤ #X := by
  set H := X.filter fun i => ¬ 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y
  have h1 : #H * #Y ≤ 4 * R * #(supp B X Y) := by
    rw [card_supp_eq_sum, mul_sum, card_eq_sum_ones, sum_mul]
    calc ∑ i ∈ H, 1 * #Y ≤ ∑ i ∈ H, 4 * R * #(Y.filter fun j => B i j ≠ 0) :=
          sum_le_sum fun i hi => by
            have := (mem_filter.1 hi).2; omega
      _ ≤ ∑ i ∈ X, 4 * R * #(Y.filter fun j => B i j ≠ 0) :=
          sum_le_sum_of_subset (filter_subset _ _)
  have : 4 * #H * #Y ≤ #X * #Y := by nlinarith
  exact Nat.le_of_mul_le_mul_right this hY

/-- Heavy columns are few. -/
theorem heavy_cols (B : α → β → K) (X : Finset α) (Y : Finset β) (R : ℕ)
    (hnz : 16 * R * #(supp B X Y) ≤ #X * #Y) (hX : 0 < #X) :
    4 * #(Y.filter fun j => ¬ 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X) ≤ #Y := by
  set H := Y.filter fun j => ¬ 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X
  have h1 : #H * #X ≤ 4 * R * #(supp B X Y) := by
    rw [card_supp_eq_sum', mul_sum, card_eq_sum_ones, sum_mul]
    calc ∑ i ∈ H, 1 * #X ≤ ∑ j ∈ H, 4 * R * #(X.filter fun i => B i j ≠ 0) :=
          sum_le_sum fun i hi => by
            have := (mem_filter.1 hi).2; omega
      _ ≤ ∑ j ∈ Y, 4 * R * #(X.filter fun i => B i j ≠ 0) :=
          sum_le_sum_of_subset (filter_subset _ _)
  have : 4 * #H * #X ≤ #Y * #X := by nlinarith
  exact Nat.le_of_mul_le_mul_right this hX

/-- **Cleaning lemma (Gavinsky–Lovett; HMST Lemma 4.7).** -/
theorem cleaning (B : α → β → K) (X : Finset α) (Y : Finset β) (R : ℕ) (hR : 1 ≤ R)
    (hrank : rankOn B X Y ≤ R) (hnz : 16 * R * #(supp B X Y) ≤ #X * #Y) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 2 * #X' ∧ #Y ≤ 2 * #Y' ∧ ∀ i ∈ X', ∀ j ∈ Y', B i j = 0 := by
  classical
  rcases Nat.eq_zero_or_pos #X with hX | hX
  · refine ⟨X, subset_refl _, Y, subset_refl _, by omega, by omega, fun i hi => ?_⟩
    simp_all
  rcases Nat.eq_zero_or_pos #Y with hY | hY
  · refine ⟨X, subset_refl _, Y, subset_refl _, by omega, by omega, fun i _ j hj => ?_⟩
    simp_all
  set X0 := X.filter fun i => 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y with hX0
  set Y0 := Y.filter fun j => 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X with hY0
  have hX0c : 3 * #X ≤ 4 * #X0 := by
    have h := heavy_rows B X Y R hnz hY
    have := card_filter_add_card_filter_not (s := X) (fun i => 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y)
    rw [hX0]; omega
  have hY0c : 3 * #Y ≤ 4 * #Y0 := by
    have h := heavy_cols B X Y R hnz hX
    have := card_filter_add_card_filter_not (s := Y) (fun j => 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X)
    rw [hY0]; omega
  set Mset := (X0 ×ˢ Y0).powerset.filter
    (fun F => ∀ p ∈ F, ∀ q ∈ F, B p.1 q.2 ≠ 0 ↔ p = q) with hMset
  have hne : Mset.Nonempty := ⟨∅, by simp [hMset]⟩
  obtain ⟨F, hFM, hFmax⟩ := exists_max_image Mset (fun F => #F) hne
  obtain ⟨hFsub, hFind⟩ := mem_filter.1 hFM
  rw [mem_powerset] at hFsub
  have hFsub' : F ⊆ X ×ˢ Y := hFsub.trans (product_subset_product (filter_subset _ _)
    (filter_subset _ _))
  have hFR : #F ≤ R := (card_le_rankOn_of_induced B X Y F hFsub' hFind).trans hrank
  set NC := X0.filter fun i => ∃ q ∈ F, B i q.2 ≠ 0 with hNC
  set NR := Y0.filter fun j => ∃ p ∈ F, B p.1 j ≠ 0 with hNR
  have hNCc : 4 * #NC ≤ #X := by
    have hsub : NC ⊆ F.biUnion fun q => X.filter fun i => B i q.2 ≠ 0 := by
      intro i hi
      obtain ⟨hi0, q, hq, hb⟩ := mem_filter.1 hi
      exact mem_biUnion.2 ⟨q, hq, mem_filter.2 ⟨(mem_filter.1 hi0).1, hb⟩⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ q ∈ F, 4 * R * #(X.filter fun i => B i q.2 ≠ 0) ≤ #X := fun q hq =>
      (mem_filter.1 (mem_product.1 (hFsub hq)).2).2
    have h3 : 4 * R * #NC ≤ #F * #X := by
      calc 4 * R * #NC ≤ 4 * R * ∑ q ∈ F, #(X.filter fun i => B i q.2 ≠ 0) :=
            Nat.mul_le_mul_left _ h1
        _ = ∑ q ∈ F, 4 * R * #(X.filter fun i => B i q.2 ≠ 0) := by rw [mul_sum]
        _ ≤ ∑ q ∈ F, #X := sum_le_sum h2
        _ = #F * #X := by simp
    have h4 : 4 * R * #NC ≤ R * #X := h3.trans (Nat.mul_le_mul_right _ hFR)
    have : R * (4 * #NC) ≤ R * #X := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hNRc : 4 * #NR ≤ #Y := by
    have hsub : NR ⊆ F.biUnion fun p => Y.filter fun j => B p.1 j ≠ 0 := by
      intro j hj
      obtain ⟨hj0, p, hp, hb⟩ := mem_filter.1 hj
      exact mem_biUnion.2 ⟨p, hp, mem_filter.2 ⟨(mem_filter.1 hj0).1, hb⟩⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ p ∈ F, 4 * R * #(Y.filter fun j => B p.1 j ≠ 0) ≤ #Y := fun p hp =>
      (mem_filter.1 (mem_product.1 (hFsub hp)).1).2
    have h3 : 4 * R * #NR ≤ #F * #Y := by
      calc 4 * R * #NR ≤ 4 * R * ∑ p ∈ F, #(Y.filter fun j => B p.1 j ≠ 0) :=
            Nat.mul_le_mul_left _ h1
        _ = ∑ p ∈ F, 4 * R * #(Y.filter fun j => B p.1 j ≠ 0) := by rw [mul_sum]
        _ ≤ ∑ p ∈ F, #Y := sum_le_sum h2
        _ = #F * #Y := by simp
    have h4 : 4 * R * #NR ≤ R * #Y := h3.trans (Nat.mul_le_mul_right _ hFR)
    have : R * (4 * #NR) ≤ R * #Y := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  refine ⟨X0 \ NC, sdiff_subset.trans (filter_subset _ _), Y0 \ NR,
    sdiff_subset.trans (filter_subset _ _), ?_, ?_, ?_⟩
  · have := le_card_sdiff NC X0; omega
  · have := le_card_sdiff NR Y0; omega
  · intro i hi j hj
    by_contra hb
    obtain ⟨hi0, hiN⟩ := mem_sdiff.1 hi
    obtain ⟨hj0, hjN⟩ := mem_sdiff.1 hj
    have hiq : ∀ q ∈ F, B i q.2 = 0 := fun q hq => by
      by_contra h; exact hiN (mem_filter.2 ⟨hi0, q, hq, h⟩)
    have hjp : ∀ p ∈ F, B p.1 j = 0 := fun p hp => by
      by_contra h; exact hjN (mem_filter.2 ⟨hj0, p, hp, h⟩)
    have hnot : (i, j) ∉ F := fun h => hb (hiq _ h)
    have hmem : insert (i, j) F ∈ Mset := by
      refine mem_filter.2 ⟨mem_powerset.2 (insert_subset (mem_product.2 ⟨hi0, hj0⟩) hFsub), ?_⟩
      intro p hp q hq
      rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
      · simpa using hb
      · simp only [hiq q hq, ne_eq, not_true_eq_false, false_iff]
        rintro rfl; exact hnot hq
      · simp only [hjp p hp, ne_eq, not_true_eq_false, false_iff]
        rintro rfl; exact hnot hp
      · exact hFind p hp q hq
    have := hFmax _ hmem
    rw [card_insert_of_notMem hnot] at this
    omega

end E1088
