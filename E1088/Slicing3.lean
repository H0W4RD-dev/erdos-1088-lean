import E1088.Slicing2

/-!
# Slicing Lemma, part 3: few bad centres (step (a)) and the assembly (manuscript Lemma 9.1)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem dists_mono {A A' : Finset (ℝ^d)} (h : A ⊆ A') : dists A ⊆ dists A' :=
  image_subset_image (offDiag_mono h)

/-- The bipartite graph `G_c` of the Slicing Lemma: the neighbours of `k`. -/
noncomputable def slNbr (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (π : ℕ) (θinv : ℝ) (c : ℝ^d) (k : ℕ) : Finset ℝ :=
  ((C k).image fun x => dist x c).filter fun l =>
    l ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) ∧ l ∉ B.image (β k) ∧
      ((C k).card : ℝ) ≤ θinv * ((C k).filter fun x => dist x c = l).card

/-- `Mt` is a matching of `G_c` on the left set `L`. -/
def IsSlMatch (L : Finset ℕ) (N : ℕ → Finset ℝ) (Mt : Finset (ℕ × ℝ)) : Prop :=
  (∀ q ∈ Mt, q.1 ∈ L ∧ q.2 ∈ N q.1) ∧ (∀ q ∈ Mt, ∀ q' ∈ Mt, q.1 = q'.1 ∨ q.2 = q'.2 → q = q')

/-- The bad centres: `c ∈ C π` such that `G_c` has no matching of size `3K`. -/
noncomputable def slBad (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (π : ℕ) (θinv : ℝ) (L : Finset ℕ) (K : ℕ) : Finset (ℝ^d) := by
  classical
  exact (C π).filter fun c => ∀ Mt, IsSlMatch L (slNbr S B C β π θinv c) Mt → Mt.card < 3 * K

theorem mem_slBad {S B : Finset (ℝ^d)} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    {π : ℕ} {θinv : ℝ} {L : Finset ℕ} {K : ℕ} {c : ℝ^d} :
    c ∈ slBad S B C β π θinv L K ↔
      c ∈ C π ∧ ∀ Mt, IsSlMatch L (slNbr S B C β π θinv c) Mt → Mt.card < 3 * K := by
  unfold slBad; simp only [mem_filter]

set_option maxHeartbeats 4000000 in
/-- **Step (a)**: few bad centres. -/
theorem bad_centres (n : ℕ) (d D h r K : ℕ) (X : Finset (ℝ^d)) (hX : Ambient n D h X)
    (S W : Finset (ℝ^d)) (σ Γ' : ℝ) (hc : Config X S W r σ) (hσ : smin n D h ≤ σ)
    (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ') (B : Finset (ℝ^d)) (I : Finset ℕ)
    (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (hF : RainbowFamily S W B I C β)
    (hI : 6 * K ≤ I.card) (hK : 1 ≤ K) (hk : ksl r B.card K ≤ kstar n) (M : ℝ)
    (hMk : ∀ k ∈ I, M ≤ (C k).card)
    (hMsl : 2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) ≤ M)
    (π : ℕ) (hπ : π ∈ I) :
    ((slBad S B C β π (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) (I.erase π) K).card : ℝ) ≤
      4 * LRcost (kstar n) (D + 2) * h := by
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast (show 1 ≤ D + 2 by omega)
  set θinv := 16 * Γ' * a ^ ksl r B.card K with hθdef
  have hθ16 : 16 ≤ θinv := by
    have : 1 ≤ a ^ ksl r B.card K := one_le_pow₀ ha1
    rw [hθdef]; nlinarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  set LRc := LRcost (kstar n) (D + 2) with hLRc
  have hLR1 : 1 ≤ LRc := one_le_LRcost _ _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ 2 * n * (n + K) := by positivity
  have hnK : (1 : ℝ) ≤ 2 * n * (n + K) := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0` is impossible: `ksl ≤ kstar 0 = 1` forces `K ≤ 0`
      exfalso
      subst hn; unfold ksl kstar at hk; simp at hk; omega
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  have hMσ : θinv * (2 * n * (n + K) * σ) ≤ M := by
    have e : θinv * (2 * n * (n + K) * σ) =
        2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) := by
      rw [hθdef, ha]; ring
    rw [e]; exact hMsl
  have hsmin : 2 * LRc * h < smin n D h := by
    unfold smin
    have h4 : (4 : ℝ) ≤ 4 ^ (n + 1) := by
      calc (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : 4 * LRc * (h + 1) ≤ 4 ^ (n + 1) * LRc * (h + 1) := by gcongr
    nlinarith
  set L := I.erase π with hL
  set N := slNbr S B C β π θinv with hN
  set Zbad := slBad S B C β π θinv L K with hZbad
  -- König covers for bad centres
  have hcovK : ∀ c ∈ Zbad, ∃ A ⊆ L, ∃ Λ0 : Finset ℝ, (∀ k ∈ L, k ∉ A → N c k ⊆ Λ0) ∧
      A.card + Λ0.card < 3 * K := fun c hc =>
    konig_cover L (N c) (3 * K) (fun Mt h1 h2 => (mem_slBad.1 hc).2 Mt ⟨h1, h2⟩)
  choose! A hAL Λ0 hcover hsize using hcovK
  set Zk : ℕ → Finset (ℝ^d) := fun k => Zbad.filter fun c => k ∉ A c with hZk
  have hLc : 6 * K - 1 ≤ L.card := by rw [hL, card_erase_of_mem hπ]; omega
  have hLne : L.Nonempty := by rw [← card_pos]; omega
  obtain ⟨kst, hkst, hmax⟩ := exists_max_image L (fun k => (Zk k).card) hLne
  -- averaging
  have havg : Zbad.card ≤ 2 * (Zk kst).card := by
    have h1 : ∑ k ∈ L, (Zk k).card = ∑ c ∈ Zbad, (L.filter fun k => k ∉ A c).card := by
      simp only [hZk, card_filter]; exact Finset.sum_comm
    have h2 : ∀ c ∈ Zbad, L.card - (3 * K - 1) ≤ (L.filter fun k => k ∉ A c).card := by
      intro c hc
      have e1 := card_filter_add_card_filter_not (s := L) (fun k => k ∉ A c)
      have e2 : (L.filter fun k => ¬ k ∉ A c).card ≤ (A c).card :=
        card_le_card fun k hk => by simpa using (mem_filter.1 hk).2
      have e3 := hsize c hc
      have e4 : (L.filter fun k => ¬ k ∉ A c).card ≤ 3 * K - 1 := by omega
      omega
    have h3 : Zbad.card * (L.card - (3 * K - 1)) ≤ L.card * (Zk kst).card := by
      calc Zbad.card * (L.card - (3 * K - 1)) = ∑ _c ∈ Zbad, (L.card - (3 * K - 1)) := by
            rw [sum_const, smul_eq_mul]
        _ ≤ ∑ c ∈ Zbad, (L.filter fun k => k ∉ A c).card := sum_le_sum h2
        _ = ∑ k ∈ L, (Zk k).card := h1.symm
        _ ≤ ∑ _k ∈ L, (Zk kst).card := sum_le_sum hmax
        _ = L.card * (Zk kst).card := by rw [sum_const, smul_eq_mul]
    have h4 : L.card ≤ 2 * (L.card - (3 * K - 1)) := by omega
    have hLpos : 0 < L.card := card_pos.2 hLne
    have : L.card * Zbad.card ≤ L.card * (2 * (Zk kst).card) := by
      calc L.card * Zbad.card ≤ 2 * (L.card - (3 * K - 1)) * Zbad.card :=
            Nat.mul_le_mul_right _ h4
        _ = 2 * (Zbad.card * (L.card - (3 * K - 1))) := by ring
        _ ≤ 2 * (L.card * (Zk kst).card) := Nat.mul_le_mul_left _ h3
        _ = L.card * (2 * (Zk kst).card) := by ring
    exact Nat.le_of_mul_le_mul_left this hLpos
  -- the covering lemma on rows `C kst`, columns `Zk kst`
  have hkstI : kst ∈ I := (mem_erase.1 hkst).2
  have hkstπ : kst ≠ π := (mem_erase.1 hkst).1
  have hCkW : C kst ⊆ W := (hF.Cne kst hkstI).2
  have hCπW : C π ⊆ W := (hF.Cne π hπ).2
  set Cst : Finset ℝ := dists (S ∪ B) ∪ B.image (β π) ∪ B.image (β kst) with hCst
  let ι := Fin (3 * K - 1) ⊕ (ℝ ⊕ ℝ^d)
  let lam0 : ℝ^d → Fin (3 * K - 1) → ℝ := fun c i =>
    if hi : (i : ℕ) < (Λ0 c).card then ((Λ0 c).equivFin.symm ⟨i, hi⟩ : ℝ) else 0
  let colF : ι → ℝ^d → ℝ := fun t => match t with
    | Sum.inl i => fun c => lam0 c i ^ 2
    | Sum.inr (Sum.inl v) => fun _ => v ^ 2
    | Sum.inr (Sum.inr s) => fun c => dist c s ^ 2
  let J : Finset ι := (Finset.univ : Finset (Fin (3 * K - 1))).disjSum (Cst.disjSum S)
  have hSB : (S ∪ B).card = r + B.card := by
    rw [card_union_of_disjoint hF.F1.1, hc.card]
  have hJP : J.card + S.card ≤ ksl r B.card K := by
    have hJc : J.card = (3 * K - 1) + (Cst.card + S.card) := by
      simp only [J]; rw [card_disjSum, card_disjSum, card_univ, Fintype.card_fin]
    rw [hJc]
    have h1 : Cst.card ≤ (r + B.card).choose 2 + B.card + B.card := by
      rw [hCst]
      have e1 := card_union_le (dists (S ∪ B) ∪ B.image (β π)) (B.image (β kst))
      have e2 := card_union_le (dists (S ∪ B)) (B.image (β π))
      have e3 := card_dists_le (S ∪ B)
      have e4 := card_image_le (s := B) (f := β π)
      have e5 := card_image_le (s := B) (f := β kst)
      rw [hSB] at e3
      omega
    rw [hc.card]; unfold ksl; omega
  have hfew : ∀ c ∈ Zk kst, 16 * (D + 2) ^ (J.card + S.card) *
      ((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card ≤ (C kst).card := by
    intro c hcZ
    obtain ⟨hcZb, hcA⟩ := mem_filter.1 hcZ
    have hcπ : c ∈ C π := (mem_slBad.1 hcZb).1
    have hcW : c ∈ W := hCπW hcπ
    set θ : ℝ := (C kst).card / θinv with hθ
    have hθpos : 0 < θinv := by linarith
    have hθσ : σ ≤ θ := by
      rw [hθ, le_div_iff₀ hθpos]
      have := hMk kst hkstI
      nlinarith
    have hVsub : C kst ⊆ W.erase c := fun x hx => mem_erase.2 ⟨fun e =>
      family_classes_disjoint hF hkstI hπ hkstπ hx (e ▸ hcπ), hCkW hx⟩
    have hHRc := hHR c hcW (C kst) hVsub θ hθσ
    have hsub : ((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2) ⊆ hrSet S (C kst) c θ := by
      intro x hx
      obtain ⟨hxC, hJ, hP⟩ := mem_filter.1 hx
      have hxc : ‖x - c‖ = dist x c := (dist_eq_norm x c).symm
      have hnot : ∀ v : ℝ, ∀ i ∈ J, colF i c = v ^ 2 → dist x c ≠ v := by
        intro v i hi he hv
        exact hJ i hi (by rw [hxc, hv, he])
      -- `λ = |xc|` avoids `Λ0 c`, `Φ(c)`, `β(kst)`
      have hΛ : dist x c ∉ Λ0 c := by
        intro hm
        set j := (Λ0 c).equivFin ⟨dist x c, hm⟩
        have hj : (j : ℕ) < 3 * K - 1 := by
          have := hsize c hcZb; have := j.2; omega
        refine hnot (dist x c) (Sum.inl ⟨j, hj⟩) (inl_mem_disjSum.2 (mem_univ _)) ?_ rfl
        simp only [colF, lam0, dif_pos j.2]
        simp [j]
      have hCstm : ∀ v ∈ Cst, dist x c ≠ v := fun v hv =>
        hnot v (Sum.inr (Sum.inl v)) (inr_mem_disjSum.2 (inl_mem_disjSum.2 hv)) rfl
      have hΦ : dist x c ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) := by
        intro hm
        rcases mem_union.1 hm with hm | hm
        · exact hCstm _ (mem_union_left _ hm) rfl
        · obtain ⟨s, hs, hse⟩ := mem_image.1 hm
          exact hnot (dist c s) (Sum.inr (Sum.inr s)) (inr_mem_disjSum.2 (inr_mem_disjSum.2 hs))
            rfl hse.symm
      have hβk : dist x c ∉ B.image (β kst) := fun hm => hCstm _ (mem_union_right _ hm) rfl
      have hbis : ∀ s ∈ S, dist x c ≠ dist x s := fun s hs h => hP s hs (by
        rw [hxc, h, dist_eq_norm])
      -- the threshold fails since `kst` is few for `c`
      have hthr : θinv * ((C kst).filter fun y => dist y c = dist x c).card < (C kst).card := by
        by_contra hge
        push Not at hge
        have hmemN : dist x c ∈ N c kst := mem_filter.2 ⟨mem_image.2 ⟨x, hxC, rfl⟩, hΦ, hβk, hge⟩
        exact hΛ (hcover c hcZb kst hkst hcA hmemN)
      refine mem_filter.2 ⟨hxC, ?_, hbis, ?_⟩
      · intro hm
        rcases mem_union.1 hm with hm | hm
        · exact hΦ (mem_union_left _ (mem_union_left _ (dists_mono subset_union_left hm)))
        · exact hΦ (mem_union_right _ hm)
      · rw [hθ, lt_div_iff₀ hθpos]; linarith
    have h1 := card_le_card hsub
    have h2 : ((((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℕ) : ℝ) ≤ Γ' * θ :=
      (by exact_mod_cast h1 : _ ≤ ((hrSet S (C kst) c θ).card : ℝ)).trans hHRc
    have hpow : ((D + 2 : ℕ) : ℝ) ^ (J.card + S.card) ≤ a ^ ksl r B.card K :=
      pow_le_pow_right₀ ha1 hJP
    have : ((16 * (D + 2) ^ (J.card + S.card) * ((C kst).filter fun x =>
        (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧ ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℕ) : ℝ) ≤
        (C kst).card := by
      push_cast
      have e : Γ' * θ * (16 * a ^ ksl r B.card K) = (C kst).card := by
        rw [hθ, hθdef]; field_simp
      have h0 : (0 : ℝ) ≤ (((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℝ) := Nat.cast_nonneg _
      have hpow' : ((D : ℝ) + 2) ^ (J.card + S.card) ≤ a ^ ksl r B.card K := by
        rw [ha] at hpow ⊢; push_cast at hpow ⊢; exact hpow
      calc 16 * ((D : ℝ) + 2) ^ (J.card + S.card) * (((C kst).filter fun x =>
            (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧ ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℝ)
          ≤ 16 * a ^ ksl r B.card K * (Γ' * θ) := by gcongr
        _ = (C kst).card := by rw [← e]; ring
    exact_mod_cast this
  have hbig : 2 * LRc * h < (C kst).card := by
    have h1 := hMk kst hkstI
    have e1 : 1 ≤ θinv * (2 * n * (n + K)) := by nlinarith
    have e2 : σ ≤ θinv * (2 * n * (n + K) * σ) := by nlinarith
    linarith
  have hZk := gl_lr_or n D h X hX.dim hX.half (C kst) (Zk kst) (hCkW.trans hc.subW)
    (fun c hc' => hc.subW (hCπW (mem_slBad.1 (mem_filter.1 hc').1).1)) J colF S
    (hJP.trans hk) hfew hbig
  have : (Zbad.card : ℝ) ≤ 2 * (Zk kst).card := by exact_mod_cast havg
  linarith

end E1088
