import E1088.Slicing3

/-!
# The Slicing Lemma (manuscript Lemma 9.1), assembled from steps (a)–(d)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Slicing Lemma** (manuscript Lemma 9.1). -/
theorem slicing_lemma_proved (n : ℕ) (hn : 6 ≤ n) (d D h r K : ℕ) (hr : r ≤ n - 6) (hK : 1 ≤ K)
    (X : Finset (ℝ^d)) (hX : Ambient n D h X) (S W : Finset (ℝ^d)) (σ Γ' : ℝ)
    (hc : Config X S W r σ) (hσ : smin n D h ≤ σ) (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ')
    (B : Finset (ℝ^d)) (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (hF : RainbowFamily S W B I C β) (hB1 : 1 ≤ B.card) (hB2 : B.card ≤ n - 5 - r)
    (hI : 6 * K ≤ I.card) (hk : ksl r B.card K ≤ kstar n) (M : ℝ)
    (hMk : ∀ k ∈ I, M ≤ (C k).card)
    (hMsl : 2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) ≤ M) :
    ∃ c ∈ I.biUnion C, ∃ I' ⊆ I, I'.card = K ∧ ∃ (C' : ℕ → Finset (ℝ^d)) (β' : ℕ → ℝ^d → ℝ),
      (∀ k ∈ I', C' k ⊆ C k) ∧ RainbowFamily S W (insert c B) I' C' β' ∧
      ∀ k ∈ I', M / (2 * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K)) ≤ (C' k).card := by
  classical
  obtain ⟨π, hπ⟩ : I.Nonempty := by rw [← card_pos]; omega
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast (show 1 ≤ D + 2 by omega)
  set θinv := 16 * Γ' * a ^ ksl r B.card K with hθdef
  have hθ16 : 16 ≤ θinv := by
    have : 1 ≤ a ^ ksl r B.card K := one_le_pow₀ ha1
    rw [hθdef]; nlinarith
  have hθpos : 0 < θinv := by linarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hnK : (1 : ℝ) ≤ 2 * n * (n + K) := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have : (6 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hMσ : θinv * (2 * n * (n + K) * σ) ≤ M := by
    have e : θinv * (2 * n * (n + K) * σ) =
        2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) := by
      rw [hθdef, ha]; ring
    rw [e]; exact hMsl
  have hσM : σ ≤ M := by
    have e1 : 1 ≤ θinv * (2 * n * (n + K)) := by nlinarith
    nlinarith
  set LRc := LRcost (kstar n) (D + 2) with hLRc
  have hLR1 : 1 ≤ LRc := one_le_LRcost _ _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hsmin : 4 * LRc * h < smin n D h := by
    unfold smin
    have h4 : (16 : ℝ) ≤ 4 ^ (n + 1) := by
      calc (16 : ℝ) = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : 16 * LRc * (h + 1) ≤ 4 ^ (n + 1) * LRc * (h + 1) := by gcongr
    nlinarith
  have hbad := bad_centres n d D h r K X hX S W σ Γ' hc hσ hΓ' hHR B I C β hF hI hK hk M hMk
    hMsl π hπ
  rw [← ha, ← hθdef] at hbad
  set L := I.erase π with hL
  set N := slNbr S B C β π θinv with hN
  -- (b) a good centre
  have hlt : (slBad S B C β π θinv L K).card < (C π).card := by
    have h1 := hMk π hπ
    have : ((slBad S B C β π θinv L K).card : ℝ) < (C π).card := by linarith
    exact_mod_cast this
  obtain ⟨c, hcπ, hcgood⟩ : ∃ c ∈ C π, c ∉ slBad S B C β π θinv L K := by
    by_contra hcon
    push Not at hcon
    exact absurd (card_le_card fun x hx => hcon x hx) (not_le.2 hlt)
  have hmatch : ¬ ∀ Mt, IsSlMatch L (N c) Mt → Mt.card < 3 * K :=
    fun hall => hcgood (mem_slBad.2 ⟨hcπ, hall⟩)
  push Not at hmatch
  obtain ⟨Mt, hMt, hMtc⟩ := hmatch
  obtain ⟨Mt', hMt'sub, hMt'c⟩ := exists_subset_card_eq hMtc
  have hMt'1 : ∀ q ∈ Mt', q.1 ∈ L ∧ q.2 ∈ N c q.1 := fun q hq => hMt.1 q (hMt'sub hq)
  have hMt'2 : ∀ q ∈ Mt', ∀ q' ∈ Mt', q.1 = q'.1 ∨ q.2 = q'.2 → q = q' :=
    fun q hq q' hq' => hMt.2 q (hMt'sub hq) q' (hMt'sub hq')
  set I1 := Mt'.image Prod.fst with hI1
  have hI1c : I1.card = 3 * K := by
    rw [hI1, card_image_of_injOn (fun q hq q' hq' h => hMt'2 q hq q' hq' (Or.inl h)), hMt'c]
  let lam : ℕ → ℝ := fun k => if hk : ∃ q ∈ Mt', q.1 = k then (Classical.choose hk).2 else 0
  have hlam : ∀ k ∈ I1, (k, lam k) ∈ Mt' := by
    intro k hk
    have hex : ∃ q ∈ Mt', q.1 = k := by
      obtain ⟨q, hq, hqk⟩ := mem_image.1 hk; exact ⟨q, hq, hqk⟩
    obtain ⟨hq, hqk⟩ := Classical.choose_spec hex
    simp only [lam, dif_pos hex]
    have : (k, (Classical.choose hex).2) = Classical.choose hex := by
      ext
      · exact hqk.symm
      · rfl
    rw [this]; exact hq
  have hlamN : ∀ k ∈ I1, k ∈ L ∧ lam k ∈ N c k := fun k hk => hMt'1 _ (hlam k hk)
  have hlaminj : ∀ k ∈ I1, ∀ k' ∈ I1, lam k = lam k' → k = k' := fun k hk k' hk' h =>
    (Prod.ext_iff.1 (hMt'2 _ (hlam k hk) _ (hlam k' hk') (Or.inr h))).1
  -- (c) conflict-free indices
  have hout : ∀ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ lam k ∈ B.image (β k')).card ≤ 1 := by
    intro k hk
    refine card_le_one.2 fun k1 hk1 k2 hk2 => ?_
    obtain ⟨hk1I, -, hm1⟩ := mem_filter.1 hk1
    obtain ⟨hk2I, -, hm2⟩ := mem_filter.1 hk2
    obtain ⟨b1, hb1, he1⟩ := mem_image.1 hm1
    obtain ⟨b2, hb2, he2⟩ := mem_image.1 hm2
    have hk1I' := (mem_erase.1 (hlamN k1 hk1I).1).2
    have hk2I' := (mem_erase.1 (hlamN k2 hk2I).1).2
    exact (hF.F3.1 k1 hk1I' k2 hk2I' b1 hb1 b2 hb2 (he1.trans he2.symm)).1
  obtain ⟨I', hI'I1, hI'c, hindep⟩ := conflict_free I1 K hI1c lam (fun k => B.image (β k)) hout
  -- (d) the new family
  have hI'L : I' ⊆ L := fun k hk => (hlamN k (hI'I1 hk)).1
  have hedge : ∀ k ∈ I', lam k ∈ (C k).image (fun x => dist x c) ∧
      lam k ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) ∧ lam k ∉ B.image (β k) ∧
      ((C k).card : ℝ) ≤ θinv * ((C k).filter fun x => dist x c = lam k).card := by
    intro k hk
    have := (hlamN k (hI'I1 hk)).2
    simp only [hN, slNbr, mem_filter] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  have hpos : ∀ k ∈ I', 0 < lam k := by
    intro k hk
    obtain ⟨x, hx, hxe⟩ := mem_image.1 (hedge k hk).1
    have hkI := (mem_erase.1 (hI'L hk)).2
    have hkπ := (mem_erase.1 (hI'L hk)).1
    rw [← hxe]
    exact dist_pos.2 fun e => family_classes_disjoint hF hkI hπ hkπ hx (e ▸ hcπ)
  have hrn : (r : ℝ) * (r + K) ≤ n * (n + K) := by
    have : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith
  have hfilt : ∀ k ∈ I', 2 * n * (n + K) * σ ≤ ((C k).filter fun x => dist x c = lam k).card := by
    intro k hk
    have h1 := (hedge k hk).2.2.2
    have h2 := hMk k ((mem_erase.1 (hI'L hk)).2)
    have : θinv * (2 * n * (n + K) * σ) ≤ θinv * ((C k).filter fun x => dist x c = lam k).card := by
      linarith
    exact le_of_mul_le_mul_left this hθpos
  have hn0 : (0 : ℝ) < n * (n + K) := by
    have : (6 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  obtain ⟨C', β', hF', hsub, hcard⟩ := new_family X S W B r σ hc I C β hF π hπ c hcπ I' hI'L
    lam (fun k hk k' hk' h => hlaminj k (hI'I1 hk) k' (hI'I1 hk') h)
    (fun k hk => (hedge k hk).2.1) (fun k hk => (hedge k hk).2.2.1)
    (fun k hk k' hk' hne => hindep k hk k' hk' hne) hpos
    (fun k hk => by
      have := hfilt k hk
      rw [hI'c]
      nlinarith)
  refine ⟨c, mem_biUnion.2 ⟨π, hπ, hcπ⟩, I', fun k hk => (mem_erase.1 (hI'L hk)).2, hI'c,
    C', β', hsub, hF', fun k hk => ?_⟩
  have h1 := hcard k hk
  rw [hI'c] at h1
  have h2 := (hedge k hk).2.2.2
  have h3 := hMk k ((mem_erase.1 (hI'L hk)).2)
  have hdiv : M / (2 * θinv) ≤ ((C k).filter fun x => dist x c = lam k).card - r * (r + K) * σ := by
    rw [div_le_iff₀ (by positivity)]
    set F : ℝ := (((C k).filter fun x => dist x c = lam k).card : ℝ) with hFdef
    have s1 : M ≤ θinv * F := h3.trans h2
    have s2 : θinv * (2 * ((r : ℝ) * (r + K)) * σ) ≤ θinv * (2 * n * (n + K) * σ) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hθpos.le
    have e : (F - r * (r + K) * σ) * (2 * θinv) =
        2 * (θinv * F) - θinv * (2 * ((r : ℝ) * (r + K)) * σ) := by ring
    rw [e]; linarith
  linarith

end E1088
