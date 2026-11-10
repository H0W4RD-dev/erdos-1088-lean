import E1088.G1Count
import E1088.Skeleton

/-!
# The case `n = 3` without Blokhuis's theorem

Replaces the cited Blokhuis bound by an argument inside the project (halving form, which is all
that `HalvingStep 3` needs):

1. (G1 with `T = {o}`) For every `o ∈ X` all but `4 μ₀` points of `X \ {o}` lie on one sphere
   about `o` (`μ₀ = LRcost k_G (D+2) · h`): label-disjoint pairs are pairs at different distances
   from `o`, and G1(a) bounds them by `4 μ₀ |Y|`.
2. Take an affinely independent `O ⊆ X` spanning `aff X` (`|O| ≤ dim X + 1`) and let `Z` be the
   points lying on the big sphere of every `o ∈ O`. Every `o ∈ O` is equidistant from `Z`, so
   `dim Z + dim O ≤ dim X = dim O` (orthogonal split), hence `|Z| ≤ 1`.
3. `|X| ≤ |Z| + |O| (1 + 4 μ₀) ≤ 1 + (D + 1)(1 + 4 μ₀)`.

This uses Theorem LR (through G1), hence `john_factor`. Blokhuis's polynomial bound `C(D+2,2)` is
NOT reproved; it is not needed downstream.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem rainbow_pair (x o : ℝ^d) : Rainbow (insert x ({o} : Finset (ℝ^d))) := by
  intro a ha a' ha' c hc c' hc' hne hne' _
  simp only [mem_insert, mem_singleton] at ha ha' hc hc'
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> simp_all

theorem labels_singleton (o x : ℝ^d) : labels {o} x = {dist x o} := by
  simp [labels]

/-- Step 1: a big sphere about every point. -/
theorem big_sphere (D h : ℕ) (X : Finset (ℝ^d)) (hfree : RainbowFree 3 X) (hD : affDim X ≤ D)
    (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h) (o : ℝ^d) (ho : o ∈ X) :
    ∃ r : ℝ, (((X.erase o).filter fun x => dist x o ≠ r).card : ℝ) ≤
      4 * (LRcost (kG 3) (D + 2) * h) := by
  classical
  set μ0 := LRcost (kG 3) (D + 2) * h with hμ0
  have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  set Y := X.erase o with hY
  rcases Y.eq_empty_or_nonempty with hYe | hYne
  · exact ⟨0, by rw [hYe]; simp; positivity⟩
  have hYg : ∀ x ∈ Y, x ∉ ({o} : Finset (ℝ^d)) ∧ Rainbow (insert x ({o} : Finset (ℝ^d))) :=
    fun x hx => ⟨by simpa using (mem_erase.1 hx).1, rainbow_pair x o⟩
  have hG := G1_count 3 D h X {o} Y hfree hD hh (by simpa using ho) (by simp) (by simp)
    (erase_subset _ _) hYg
  simp only [labels_singleton, disjoint_singleton] at hG
  -- the largest class
  let m : ℝ^d → ℕ := fun x => (Y.filter fun w => dist w o = dist x o).card
  obtain ⟨x0, hx0, hmax⟩ := exists_max_image Y m hYne
  refine ⟨dist x0 o, ?_⟩
  set LD := (Y ×ˢ Y).filter fun q => dist q.1 o ≠ dist q.2 o with hLD
  set SL := (Y ×ˢ Y).filter fun q => dist q.1 o = dist q.2 o with hSL
  have hsplit : LD.card + SL.card = Y.card * Y.card := by
    rw [hLD, hSL, add_comm, card_filter_add_card_filter_not, card_product]
  have hSLc : SL.card ≤ Y.card * m x0 := by
    have hsub : SL ⊆ Y.biUnion fun x => ({x} : Finset (ℝ^d)) ×ˢ
        (Y.filter fun w => dist w o = dist x o) := by
      intro q hq
      obtain ⟨hqY, hqe⟩ := mem_filter.1 hq
      obtain ⟨h1, h2⟩ := mem_product.1 hqY
      exact mem_biUnion.2 ⟨q.1, h1, mem_product.2 ⟨mem_singleton_self _, mem_filter.2 ⟨h2, hqe.symm⟩⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ x ∈ Y, (({x} : Finset (ℝ^d)) ×ˢ (Y.filter fun w => dist w o = dist x o)).card
        = ∑ x ∈ Y, m x := sum_congr rfl fun x _ => by rw [card_product, card_singleton, one_mul]
      _ ≤ ∑ _x ∈ Y, m x0 := sum_le_sum hmax
      _ = Y.card * m x0 := by rw [sum_const, smul_eq_mul]
  have hfilt : ((Y.filter fun x => dist x o ≠ dist x0 o).card) + m x0 = Y.card := by
    have := card_filter_add_card_filter_not (s := Y) (fun x => dist x o ≠ dist x0 o)
    simp only [not_not] at this
    omega
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast card_pos.2 hYne
  have h1 : (Y.card : ℝ) * Y.card ≤ 4 * μ0 * Y.card + Y.card * m x0 := by
    have e1 : ((LD.card + SL.card : ℕ) : ℝ) = Y.card * Y.card := by exact_mod_cast hsplit
    have e2 : (SL.card : ℝ) ≤ Y.card * m x0 := by exact_mod_cast hSLc
    push_cast at e1
    norm_num at hG
    linarith
  have h2 : (Y.card : ℝ) ≤ 4 * μ0 + m x0 := by
    have : (Y.card : ℝ) * Y.card ≤ (4 * μ0 + m x0) * Y.card := by linarith
    exact le_of_mul_le_mul_right this hYpos
  have h3 : ((Y.filter fun x => dist x o ≠ dist x0 o).card : ℝ) + m x0 = Y.card := by
    exact_mod_cast hfilt
  linarith

/-- Steps 2–3: the bound for rainbow-3-free sets. -/
theorem card_le_n3 (D h : ℕ) (X : Finset (ℝ^d)) (hfree : RainbowFree 3 X) (hD : affDim X ≤ D)
    (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h) :
    (X.card : ℝ) ≤ 1 + (D + 1) * (1 + 4 * (LRcost (kG 3) (D + 2) * h)) := by
  classical
  set μ0 := LRcost (kG 3) (D + 2) * h with hμ0
  have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  choose! rad hrad using fun o (ho : o ∈ X) => big_sphere D h X hfree hD hh o ho
  -- an affinely independent spanning subset
  obtain ⟨t, htX, hspan, hind⟩ := exists_affineIndependent ℝ (ℝ^d) (X : Set (ℝ^d))
  have hfin : t.Finite := X.finite_toSet.subset htX
  haveI : Fintype t := hfin.fintype
  set O := hfin.toFinset with hO
  have hOt : (O : Set (ℝ^d)) = t := hfin.coe_toFinset
  have hOX : O ⊆ X := fun x hx => htX (hfin.mem_toFinset.1 hx)
  have hvs : vectorSpan ℝ t = vectorSpan ℝ (X : Set (ℝ^d)) := by
    rw [← direction_affineSpan, hspan, direction_affineSpan]
  have hdimO : affDim O = affDim X := by
    unfold affDim; rw [hOt, hvs]
  have hOcard : O.card ≤ affDim X + 1 := by
    have h1 := hind.card_le_finrank_succ
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hvs] at h1
    have h2 : O.card = Fintype.card t := hfin.card_toFinset
    rw [h2]; exact h1
  -- the common big-sphere set
  set Z := X.filter fun x => ∀ o ∈ O, x ≠ o ∧ dist x o = rad o with hZ
  have hcover : X ⊆ Z ∪ (O ∪ O.biUnion fun o => (X.erase o).filter fun x => dist x o ≠ rad o) := by
    intro x hx
    by_cases hz : x ∈ Z
    · exact mem_union_left _ hz
    refine mem_union_right _ ?_
    by_cases hxO : x ∈ O
    · exact mem_union_left _ hxO
    refine mem_union_right _ ?_
    have : ¬ ∀ o ∈ O, x ≠ o ∧ dist x o = rad o := fun h => hz (mem_filter.2 ⟨hx, h⟩)
    push Not at this
    obtain ⟨o, ho, hxo⟩ := this
    have hne : x ≠ o := fun e => hxO (e ▸ ho)
    exact mem_biUnion.2 ⟨o, ho, mem_filter.2 ⟨mem_erase.2 ⟨hne, hx⟩, hxo hne⟩⟩
  -- `|Z| ≤ 1` by the orthogonal split
  have hZ1 : Z.card ≤ 1 := by
    have hortho := ortho_of_equidistant Z O (fun o => rad o) fun z hz o ho => by
      rw [← dist_eq_norm]; exact ((mem_filter.1 hz).2 o ho).2
    have hadd := affDim_add_le_of_ortho Z O hortho
    have hU : affDim (Z ∪ O) ≤ affDim X := affDim_mono (union_subset (filter_subset _ _) hOX)
    have : affDim Z = 0 := by omega
    exact card_le_one_of_affDim_zero Z this
  have hbig : ∀ o ∈ O, (((X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ) ≤ 4 * μ0 :=
    fun o ho => hrad o (hOX ho)
  have h1 := (card_le_card hcover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_union_le _ _) _))
  have h2 := card_biUnion_le (s := O) (t := fun o => (X.erase o).filter fun x => dist x o ≠ rad o)
  have h3 : ((O.biUnion fun o => (X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ) ≤
      O.card * (4 * μ0) := by
    calc ((O.biUnion fun o => (X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ)
        ≤ ∑ o ∈ O, (((X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ) := by
          exact_mod_cast h2
      _ ≤ ∑ _o ∈ O, 4 * μ0 := sum_le_sum hbig
      _ = O.card * (4 * μ0) := by rw [sum_const, nsmul_eq_mul]
  have hOD : (O.card : ℝ) ≤ D + 1 := by
    have : O.card ≤ D + 1 := by omega
    exact_mod_cast this
  have hX : (X.card : ℝ) ≤ Z.card + (O.card + O.card * (4 * μ0)) := by
    have : (X.card : ℝ) ≤ Z.card + (O.card + (O.biUnion fun o =>
        (X.erase o).filter fun x => dist x o ≠ rad o).card) := by exact_mod_cast h1
    linarith
  have hZr : (Z.card : ℝ) ≤ 1 := by exact_mod_cast hZ1
  have : (O.card : ℝ) * (1 + 4 * μ0) ≤ (D + 1) * (1 + 4 * μ0) :=
    mul_le_mul_of_nonneg_right hOD (by positivity)
  nlinarith

end E1088
