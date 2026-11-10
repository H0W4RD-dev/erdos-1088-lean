import E1088.CoreStep12

/-!
# Core Lemma: Steps 3 and 4 (manuscript Lemmas 8.7, 8.8 and Corollary 8.9)

`e = 2 · LRcost(k*, D+2) · h` is the output bound of the covering lemma `gl_lr_or`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- `gl_lr_or` with, for each column, a *set* of at most `w` column values (padded). -/
theorem gl_lr_or_sets (n D h : ℕ) (X : Finset (ℝ^d))
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (R0 C0 : Finset (ℝ^d)) (hR0 : R0 ⊆ X) (hC0 : C0 ⊆ X) (w : ℕ) (Val : ℝ^d → Finset ℝ)
    (hVal : ∀ c ∈ C0, (Val c).card ≤ w) (P : Finset (ℝ^d)) (hk : w + P.card ≤ kstar n)
    (hfew : ∀ c ∈ C0, 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + P.card) *
      ((R0.filter fun x => ‖x - c‖ ^ 2 ∉ Val c ∧ ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℝ) ≤
        R0.card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < R0.card) :
    (C0.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  refine gl_lr_or n D h X hD hh R0 C0 hR0 hC0 (range w) (fun i c => (Val c).toList.getD i 0) P
    (by rwa [card_range]) ?_ hbig
  intro c hc
  rw [card_range]
  have h1' : 16 * (D + 2) ^ (w + P.card) * (R0.filter fun x => ‖x - c‖ ^ 2 ∉ Val c ∧
      ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card ≤ R0.card := by exact_mod_cast hfew c hc
  refine le_trans (Nat.mul_le_mul_left _ (card_le_card ?_)) h1'
  intro x hx
  rw [mem_filter] at hx ⊢
  obtain ⟨hxR, hA, hB⟩ := hx
  refine ⟨hxR, fun hv => ?_, hB⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (mem_toList.2 hv)
  have hiw : i < w := lt_of_lt_of_le hi (by rw [length_toList]; exact hVal c hc)
  apply hA i (mem_range.2 hiw)
  rw [List.getD_eq_getElem _ _ hi, he]

/-- Average form of `gl_lr_or_sets`. -/
theorem gl_lr_or_avg_sets (n D h : ℕ) (X : Finset (ℝ^d))
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (R0 C0 : Finset (ℝ^d)) (hR0 : R0 ⊆ X) (hC0 : C0 ⊆ X) (w : ℕ) (Val : ℝ^d → Finset ℝ)
    (hVal : ∀ c ∈ C0, (Val c).card ≤ w) (P : Finset (ℝ^d)) (hk : w + P.card ≤ kstar n)
    (htot : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + P.card) *
      (((R0 ×ˢ C0).filter fun q => ‖q.1 - q.2‖ ^ 2 ∉ Val q.2 ∧
        ∀ s ∈ P, ‖q.1 - q.2‖ ^ 2 ≠ ‖q.1 - s‖ ^ 2).card : ℝ) ≤ R0.card * C0.card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < R0.card) :
    (C0.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  refine gl_lr_or_avg n D h X hD hh R0 C0 hR0 hC0 (range w) (fun i c => (Val c).toList.getD i 0)
    P (by rwa [card_range]) ?_ hbig
  rw [card_range]
  have h1' : 16 * (D + 2) ^ (w + P.card) * ((R0 ×ˢ C0).filter fun q => ‖q.1 - q.2‖ ^ 2 ∉ Val q.2 ∧
      ∀ s ∈ P, ‖q.1 - q.2‖ ^ 2 ≠ ‖q.1 - s‖ ^ 2).card ≤ R0.card * C0.card := by exact_mod_cast htot
  refine le_trans (Nat.mul_le_mul_left _ (card_le_card ?_)) h1'
  intro q hq
  rw [mem_filter] at hq ⊢
  obtain ⟨hqR, hA, hB⟩ := hq
  refine ⟨hqR, fun hv => ?_, hB⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (mem_toList.2 hv)
  have hiw : i < w :=
    lt_of_lt_of_le hi (by rw [length_toList]; exact hVal q.2 (mem_product.1 hqR).2)
  apply hA i (mem_range.2 hiw)
  rw [List.getD_eq_getElem _ _ hi, he]

/-- `e < σ_min`. -/
theorem e_lt_smin (n D h : ℕ) : 2 * LRcost (kstar n) (D + 2) * h < smin n D h := by
  unfold smin
  have h1 : (4 : ℝ) ≤ 4 ^ (n + 1) := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 := one_le_LRcost (kstar n) (D + 2)
  have h3 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have h4 : 4 * LRcost (kstar n) (D + 2) * (h + 1) ≤ 4 ^ (n + 1) * LRcost (kstar n) (D + 2) * (h + 1) := by
    gcongr
  nlinarith

theorem e_nonneg (n D h : ℕ) : (0 : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h :=
  mul_nonneg (mul_nonneg zero_le_two (one_le_LRcost' _ _)) (Nat.cast_nonneg _)

/-- `a₂` is `w`-few on `C_j` (manuscript Definition 8.7), with threshold `θ`. -/
def Few (S : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (Γ' σ θ : ℝ) (r w j : ℕ) (a2 : ℝ^d) : Prop :=
  ∃ Ξ : Finset ℝ, Ξ.card ≤ w + r + r.choose 2 ∧
    (((C j).filter fun x => dist x a2 ∉ Ξ ∧ ∀ s ∈ S, dist x a2 ≠ dist x s).card : ℝ) ≤
      Γ' * (θ + r * σ)

/-- **Step 3** (two-centre lemma, manuscript Lemma 8.8). -/
theorem core_step3 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {l m j : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hj : j ∈ I)
    (hjl : j ≠ l) (hjm : j ≠ m) {a2 : ℝ^d} (ha2 : a2 ∈ C m) (w : ℕ) (δ θ : ℝ) (hθ : σ ≤ θ)
    (hδ : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + 1 + r) * (δ * (C j).card) ≤ θ)
    (hk : w + 1 + r ≤ kstar n) (Z : Finset (ℝ^d)) (hZ : Z ⊆ C l)
    (hcov : ∀ a1 ∈ Z, CoverShape S C w δ j a1 a2) :
    Few S C Γ' σ θ r w j a2 ∨ (Z.card : ℝ) ≤ (w + 1) * (2 * LRcost (kstar n) (D + 2) * h) := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  have he := e_lt_smin n D h
  have he0 := e_nonneg n D h
  choose! Ω hΩ Ex hExC hEx hcv using hcov
  let R : ℝ → Finset (ℝ^d) := fun t => (C j).filter fun x => dist x a2 = t ∧ ∀ s ∈ S, dist x s ≠ t
  let Zl : ℝ → Finset (ℝ^d) := fun t => Z.filter fun a1 => t ∉ Ω a1
  have hCjX : C j ⊆ X := (hF.Cne j hj).2.trans hc.subW
  have hClX : C l ⊆ X := (hF.Cne l hl).2.trans hc.subW
  have claim : ∀ t, θ ≤ ((R t).card : ℝ) → ((Zl t).card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
    intro t hRt
    refine gl_lr_or_sets n D h X hX.dim hX.half (R t) (Zl t) ((filter_subset _ _).trans hCjX)
      ((filter_subset _ _).trans (hZ.trans hClX)) (w + 1)
      (fun a1 => (insert t (Ω a1)).image (· ^ 2)) ?_ S (by rw [hc.card]; exact hk) ?_ (by linarith)
    · intro a1 ha1
      exact card_image_le.trans ((card_insert_le _ _).trans (by
        have := hΩ a1 (mem_filter.1 ha1).1; omega))
    · intro a1 ha1
      obtain ⟨ha1Z, htΩ⟩ := mem_filter.1 ha1
      rw [hc.card]
      have hEx1 : ((Ex a1).card : ℝ) ≤ δ * (C j).card := hEx a1 ha1Z
      refine le_trans (mul_le_mul_of_nonneg_left (le_trans (Nat.cast_le.2 (card_le_card ?_)) hEx1)
        (by positivity)) (hδ.trans hRt)
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hxR, hv, hps⟩ := hx
      simp only [R, mem_filter] at hxR
      obtain ⟨hxC, hxl, hxs⟩ := hxR
      rcases hcv a1 ha1Z x hxC with h1 | h1 | h1 | h1 | h1
      · exact absurd (mem_image.2 ⟨_, mem_insert_of_mem h1, by rw [dist_eq_norm]⟩) hv
      · exact absurd (hxl ▸ h1) htΩ
      · exact absurd (mem_image.2 ⟨t, mem_insert_self _ _, by rw [← dist_eq_norm, h1, hxl]⟩) hv
      · obtain ⟨s, hs, h2 | h2⟩ := h1
        · exact absurd (by rw [← dist_eq_norm, ← dist_eq_norm, h2]) (hps s hs)
        · exact absurd (h2.trans hxl) (hxs s hs)
      · exact h1
  set Λ := ((C j).image fun x => dist x a2).filter fun t => θ ≤ ((R t).card : ℝ) with hΛdef
  by_cases hΛ : w + 1 ≤ Λ.card
  · right
    obtain ⟨Λ', hΛ'sub, hΛ'c⟩ := exists_subset_card_eq hΛ
    have hZsub : Z ⊆ Λ'.biUnion Zl := by
      intro a1 ha1
      by_contra hno
      have hsub : Λ' ⊆ Ω a1 := fun t ht => by
        by_contra htΩ
        exact hno (mem_biUnion.2 ⟨t, ht, mem_filter.2 ⟨ha1, htΩ⟩⟩)
      have := card_le_card hsub
      have := hΩ a1 ha1
      omega
    calc (Z.card : ℝ) ≤ (Λ'.biUnion Zl).card := by exact_mod_cast card_le_card hZsub
      _ ≤ ∑ t ∈ Λ', ((Zl t).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _t ∈ Λ', 2 * LRcost (kstar n) (D + 2) * h :=
          sum_le_sum fun t ht => claim t (mem_filter.1 (hΛ'sub ht)).2
      _ = (w + 1) * (2 * LRcost (kstar n) (D + 2) * h) := by
          rw [sum_const, hΛ'c, nsmul_eq_mul]; push_cast; ring
  · left
    push Not at hΛ
    refine ⟨Λ ∪ Rb S a2, ?_, ?_⟩
    · have e1 := card_union_le Λ (Rb S a2)
      have e2 : (Rb S a2).card ≤ (dists S).card + (S.image (dist a2)).card := card_union_le _ _
      have e3 := card_dists_le S
      have e4 := card_image_le (s := S) (f := dist a2)
      rw [hc.card] at e3 e4
      omega
    · have hCjW : C j ⊆ W.erase a2 := fun y hy =>
        mem_erase.2 ⟨fun e => family_classes_disjoint hF hj hm hjm hy (e ▸ ha2), (hF.Cne j hj).2 hy⟩
      have hG : ((C j).filter fun x => dist x a2 ∉ Λ ∪ Rb S a2 ∧ ∀ s ∈ S, dist x a2 ≠ dist x s) ⊆
          hrSet S (C j) a2 (θ + r * σ) := by
        intro x hx
        obtain ⟨hxC, hxn, hxs⟩ := mem_filter.1 hx
        refine mem_filter.2 ⟨hxC, fun h => hxn (mem_union_right _ h), hxs, ?_⟩
        have hRl : ((R (dist x a2)).card : ℝ) < θ := by
          by_contra hh
          push Not at hh
          exact hxn (mem_union_left _ (mem_filter.2 ⟨mem_image.2 ⟨x, hxC, rfl⟩, hh⟩))
        have hlpos : 0 < dist x a2 :=
          dist_pos.2 fun e => family_classes_disjoint hF hj hm hjm hxC (e ▸ ha2)
        have hsub2 : (C j).filter (fun y => dist y a2 = dist x a2) ⊆ R (dist x a2) ∪
            S.biUnion fun s => W.filter fun y => dist y s ∈ ({dist x a2} : Finset ℝ) := by
          intro y hy
          obtain ⟨hyC, hyl⟩ := mem_filter.1 hy
          by_cases hys : ∃ s ∈ S, dist y s = dist x a2
          · obtain ⟨s, hs, hse⟩ := hys
            exact mem_union_right _ (mem_biUnion.2 ⟨s, hs,
              mem_filter.2 ⟨(hF.Cne j hj).2 hyC, mem_singleton.2 hse⟩⟩)
          · push Not at hys
            exact mem_union_left _ (mem_filter.2 ⟨hyC, hyl, hys⟩)
        have hrb := removal_bound hc {dist x a2} (by simpa using hlpos)
        rw [card_singleton, Nat.cast_one, one_mul] at hrb
        have h3 : (((C j).filter (fun y => dist y a2 = dist x a2)).card : ℝ) ≤
            (R (dist x a2)).card +
              (S.biUnion fun s => W.filter fun y => dist y s ∈ ({dist x a2} : Finset ℝ)).card := by
          exact_mod_cast (card_le_card hsub2).trans (card_union_le _ _)
        linarith
      have hr0 : (0 : ℝ) ≤ r * σ := mul_nonneg (Nat.cast_nonneg _) (by linarith [one_le_smin n D h])
      calc (((C j).filter fun x => dist x a2 ∉ Λ ∪ Rb S a2 ∧ ∀ s ∈ S, dist x a2 ≠ dist x s).card : ℝ)
          ≤ (hrSet S (C j) a2 (θ + r * σ)).card := by exact_mod_cast card_le_card hG
        _ ≤ Γ' * (θ + r * σ) := hHR a2 ((hF.Cne m hm).2 ha2) (C j) hCjW _ (by linarith)

/-- **Step 4** (manuscript Lemma 8.9). -/
theorem core_step4 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {m j : ℕ} (hm : m ∈ I) (hj : j ∈ I)
    (w : ℕ) (θ : ℝ) (hk : w + r + r.choose 2 + r ≤ kstar n)
    (hA : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + r + r.choose 2 + r) * (Γ' * (θ + r * σ)) ≤ (C j).card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < (C j).card) (F : Finset (ℝ^d)) (hFm : F ⊆ C m)
    (hFew : ∀ a2 ∈ F, Few S C Γ' σ θ r w j a2) :
    (F.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  choose! Ξ hΞc hΞ using hFew
  refine gl_lr_or_sets n D h X hX.dim hX.half (C j) F ((hF.Cne j hj).2.trans hc.subW)
    (hFm.trans ((hF.Cne m hm).2.trans hc.subW)) (w + r + r.choose 2)
    (fun a2 => (Ξ a2).image (· ^ 2)) (fun a2 ha2 => card_image_le.trans (hΞc a2 ha2)) S
    (by rw [hc.card]; exact hk) ?_ hbig
  intro a2 ha2
  rw [hc.card]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans (Nat.cast_le.2 (card_le_card ?_))
    (hΞ a2 ha2)) (by positivity)) hA
  intro x hx
  rw [mem_filter] at hx ⊢
  obtain ⟨hxC, hv, hps⟩ := hx
  exact ⟨hxC, fun h => hv (mem_image.2 ⟨_, h, by rw [dist_eq_norm]⟩),
    fun s hs h => hps s hs (by rw [← dist_eq_norm, ← dist_eq_norm, h])⟩

/-- **Corollary of Steps 3–4** (manuscript Corollary 8.10). -/
theorem core_cor34 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {l m j : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hj : j ∈ I)
    (hjl : j ≠ l) (hjm : j ≠ m) (w : ℕ) (δ θ : ℝ) (hθ : σ ≤ θ)
    (hδ : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + 1 + r) * (δ * (C j).card) ≤ θ)
    (hk3 : w + 1 + r ≤ kstar n) (hk4 : w + r + r.choose 2 + r ≤ kstar n)
    (hA : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + r + r.choose 2 + r) * (Γ' * (θ + r * σ)) ≤ (C j).card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < (C j).card)
    (Pr : ℝ^d → ℝ^d → Prop) [DecidablePred fun q : ℝ^d × ℝ^d => Pr q.1 q.2]
    (hPr : ∀ a1 ∈ C l, ∀ a2 ∈ C m, Pr a1 a2 → CoverShape S C w δ j a1 a2) :
    ((((C l ×ˢ C m).filter fun q => Pr q.1 q.2).card : ℕ) : ℝ) ≤
      2 * LRcost (kstar n) (D + 2) * h * (C l).card +
        (w + 1) * (2 * LRcost (kstar n) (D + 2) * h) * (C m).card := by
  classical
  set e := 2 * LRcost (kstar n) (D + 2) * h with hedef
  have he0 : 0 ≤ e := e_nonneg n D h
  let Z : ℝ^d → Finset (ℝ^d) := fun a2 => (C l).filter fun a1 => Pr a1 a2
  have hcount : ((C l ×ˢ C m).filter fun q => Pr q.1 q.2).card = ∑ a2 ∈ C m, (Z a2).card := by
    rw [card_filter, sum_product_right]
    exact sum_congr rfl fun a2 _ => by
      simp only [Z, card_filter]; exact sum_congr rfl fun x _ => by by_cases hp : Pr x a2 <;> simp [hp]
  set F := (C m).filter fun a2 => Few S C Γ' σ θ r w j a2 with hFdef
  have hF := core_step4 cc hm hj w θ hk4 hA hbig F (filter_subset _ _)
    (fun a2 ha2 => (mem_filter.1 ha2).2)
  have hsplit := sum_filter_add_sum_filter_not (C m) (fun a2 => Few S C Γ' σ θ r w j a2)
    (fun a2 => ((Z a2).card : ℝ))
  have h1 : ∑ a2 ∈ F, ((Z a2).card : ℝ) ≤ e * (C l).card := by
    calc ∑ a2 ∈ F, ((Z a2).card : ℝ) ≤ ∑ _a2 ∈ F, ((C l).card : ℝ) :=
          sum_le_sum fun a2 _ => by exact_mod_cast card_le_card (filter_subset _ _)
      _ = F.card * (C l).card := by rw [sum_const, nsmul_eq_mul]
      _ ≤ e * (C l).card := by gcongr
  have h2 : ∑ a2 ∈ (C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2), ((Z a2).card : ℝ) ≤
      (w + 1) * e * (C m).card := by
    calc ∑ a2 ∈ (C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2), ((Z a2).card : ℝ)
        ≤ ∑ _a2 ∈ (C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2), (w + 1) * e := by
          refine sum_le_sum fun a2 ha2 => ?_
          obtain ⟨ha2m, hnf⟩ := mem_filter.1 ha2
          rcases core_step3 cc hl hm hj hjl hjm ha2m w δ θ hθ hδ hk3 (Z a2) (filter_subset _ _)
            (fun a1 ha1 => hPr a1 (mem_filter.1 ha1).1 a2 ha2m (mem_filter.1 ha1).2) with h | h
          · exact absurd h hnf
          · exact h
      _ = ((C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2)).card * ((w + 1) * e) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (C m).card * ((w + 1) * e) := by
          have : (((C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2)).card : ℝ) ≤ (C m).card := by
            exact_mod_cast card_le_card (filter_subset _ _)
          have : 0 ≤ (w + 1 : ℝ) * e := by positivity
          nlinarith
      _ = (w + 1) * e * (C m).card := by ring
  have : ((((C l ×ˢ C m).filter fun q => Pr q.1 q.2).card : ℕ) : ℝ) =
      ∑ a2 ∈ C m, ((Z a2).card : ℝ) := by rw [hcount]; push_cast; rfl
  rw [this, ← hsplit]
  linarith

end E1088
