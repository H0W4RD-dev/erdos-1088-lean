import E1088.Skeleton

/-!
# E1_r from the Core Lemma and the Slicing Lemma (manuscript Theorem 9.2)

`theorem_E1_proved` derives the class-count theorem from `core_lemma_proved` and `slicing_lemma`:
the initial family (one centre `b`, classes on the big spheres about `b`, cleaned of the small
classes of `S`), then `n-5-r` slicing rounds, then a contradiction with the Core Lemma.
The constant `ratio_r = 2 m̂₁ + 2n(n+K_r)` is `n`-polynomial in `D+2` and `Γ'`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem dists_insert_subset (S : Finset (ℝ^d)) (b : ℝ^d) :
    dists (insert b S) ⊆ dists S ∪ S.image (dist b) := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := mem_image.1 ht
  obtain ⟨h1, h2, h12⟩ := mem_offDiag.1 hp
  rcases mem_insert.1 h1 with e1 | e1 <;> rcases mem_insert.1 h2 with e2 | e2
  · exact absurd (e1.trans e2.symm) h12
  · exact mem_union_right _ (mem_image.2 ⟨p.2, e2, by rw [e1]⟩)
  · exact mem_union_right _ (mem_image.2 ⟨p.1, e1, by rw [e2, dist_comm]⟩)
  · exact mem_union_left _ (mem_image.2 ⟨p, mem_offDiag.2 ⟨e1, e2, h12⟩, rfl⟩)

theorem union_singleton_eq (S : Finset (ℝ^d)) (b : ℝ^d) : S ∪ {b} = insert b S := by
  rw [union_comm, ← insert_eq]

/-! ### The constants of Theorem 9.2 -/

/-- `K^{(r,p)} = 12 · 6^{n-4-r-p}`. -/
def Kp (n r p : ℕ) : ℕ := 12 * 6 ^ (n - 4 - r - p)

/-- `1/θ_sl(p) = 16 Γ' (D+2)^{k_sl(r,p)}`. -/
noncomputable def thInv (n D r p : ℕ) (Γ' : ℝ) : ℝ :=
  16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r p (Kp n r (p + 1))

/-- `M̂_core`. -/
noncomputable def McoreHat (n D r : ℕ) (Γ' : ℝ) : ℝ :=
  2 ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * ((D + 2 : ℕ) : ℝ) ^ (2 * kc n r)

/-- `M̂_sl(p) = 2n(n + K^{(p+1)}) / θ_sl(p)`. -/
noncomputable def MslHat (n D r p : ℕ) (Γ' : ℝ) : ℝ :=
  2 * n * (n + Kp n r (p + 1)) * thInv n D r p Γ'

/-- `m̂` indexed by `j = (n-4-r) - p`. -/
noncomputable def mAux (n D r : ℕ) (Γ' : ℝ) : ℕ → ℝ
  | 0 => McoreHat n D r Γ'
  | j + 1 => max (MslHat n D r (n - 4 - r - (j + 1)) Γ')
      (2 * thInv n D r (n - 4 - r - (j + 1)) Γ' * mAux n D r Γ' j)

/-- `m̂_p`. -/
noncomputable def mHat (n D r : ℕ) (Γ' : ℝ) (p : ℕ) : ℝ := mAux n D r Γ' (n - 4 - r - p)

/-- `ratio_r = 2 m̂₁ + 2n(n + K_r)`. -/
noncomputable def ratioE1 (n D r : ℕ) (Γ' : ℝ) : ℝ := 2 * mHat n D r Γ' 1 + 2 * n * (n + Kr n r)

theorem mHat_top (n D r : ℕ) (Γ' : ℝ) : mHat n D r Γ' (n - 4 - r) = McoreHat n D r Γ' := by
  simp [mHat, mAux]

theorem mHat_step (n D r p : ℕ) (Γ' : ℝ) (hp : p < n - 4 - r) :
    mHat n D r Γ' p = max (MslHat n D r p Γ') (2 * thInv n D r p Γ' * mHat n D r Γ' (p + 1)) := by
  unfold mHat
  obtain ⟨j, hj⟩ : ∃ j, n - 4 - r - p = j + 1 := ⟨n - 4 - r - p - 1, by omega⟩
  rw [hj, mAux]
  have h1 : n - 4 - r - (j + 1) = p := by omega
  have h2 : n - 4 - r - (p + 1) = j := by omega
  rw [h1, h2]

theorem mAux_nonneg (n D r : ℕ) (Γ' : ℝ) (hΓ : 1 ≤ Γ') : ∀ j, 0 ≤ mAux n D r Γ' j := by
  intro j
  induction j with
  | zero => simp only [mAux, McoreHat]; positivity
  | succ j ih =>
    simp only [mAux]
    exact le_max_of_le_right (mul_nonneg (by unfold thInv; positivity) ih)

/-! ### The initial family (proof of Theorem 9.2, first paragraph) -/

theorem initial_family (X S W : Finset (ℝ^d)) (r : ℕ) (σ τ : ℝ) (hc : Config X S W r σ)
    (hσ : 0 < σ) (b : ℝ^d) (hb : b ∈ W) (K : ℕ) (hK : K ≤ (Big S W b τ).card)
    (hτ : r * (r + K) * σ < τ) :
    ∃ (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ), RainbowFamily S W {b} (range K) C β ∧
      ∀ k ∈ range K, τ - r * (r + K) * σ ≤ (C k).card := by
  classical
  obtain ⟨I0, hI0, hI0c⟩ := exists_subset_card_eq hK
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hbS := hWS b hb
  let e := I0.equivFin
  let ρ : ℕ → ℝ := fun k => if h : k < K then (e.symm (Fin.cast hI0c.symm ⟨k, h⟩) : ℝ) else 0
  have hρmem : ∀ k ∈ range K, ρ k ∈ I0 := by
    intro k hk
    have hk' := mem_range.1 hk
    simp only [ρ, dif_pos hk']; exact coe_mem _
  have hρinj : ∀ k ∈ range K, ∀ k' ∈ range K, ρ k = ρ k' → k = k' := by
    intro k hk k' hk' h
    have h1 := mem_range.1 hk; have h2 := mem_range.1 hk'
    simp only [ρ, dif_pos h1, dif_pos h2] at h
    have := e.symm.injective (Subtype.ext h)
    simpa [Fin.ext_iff] using this
  have hBig : ∀ k ∈ range K, ρ k ∉ Rb S b ∧ τ ≤ ((W.filter fun x => dist x b = ρ k).card : ℝ) ∧
      0 < ρ k := by
    intro k hk
    have hm := hI0 (hρmem k hk)
    obtain ⟨himg, hR, hτk⟩ := mem_filter.1 hm
    refine ⟨hR, hτk, ?_⟩
    obtain ⟨x, hx, hxe⟩ := mem_image.1 himg
    rw [← hxe]; exact dist_pos.2 (ne_of_mem_erase hx)
  set T0 := S.image (dist b) ∪ I0 with hT0
  set Rem := S.biUnion fun s => W.filter fun x => dist x s ∈ T0 with hRem
  let C : ℕ → Finset (ℝ^d) := fun k => (W.filter fun x => dist x b = ρ k) \ Rem
  have hT0pos : ∀ t ∈ T0, 0 < t := by
    intro t ht
    rcases mem_union.1 ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := mem_image.1 ht
      exact dist_pos.2 fun h => hbS (h ▸ hs)
    · obtain ⟨himg, -, -⟩ := mem_filter.1 (hI0 ht)
      obtain ⟨x, hx, rfl⟩ := mem_image.1 himg
      exact dist_pos.2 (ne_of_mem_erase hx)
  have hRemc : (Rem.card : ℝ) ≤ r * (r + K) * σ := by
    have hsub : Rem ⊆ S.biUnion fun s => T0.biUnion fun t => W.filter fun x => dist x s = t := by
      intro x hx
      obtain ⟨s, hs, hx⟩ := mem_biUnion.1 hx
      obtain ⟨hxW, ht⟩ := mem_filter.1 hx
      exact mem_biUnion.2 ⟨s, hs, mem_biUnion.2 ⟨_, ht, mem_filter.2 ⟨hxW, rfl⟩⟩⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) ≤
        T0.card * σ := by
      intro s hs
      have := card_biUnion_le (s := T0) (t := fun t => W.filter fun x => dist x s = t)
      calc ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ)
          ≤ ∑ t ∈ T0, ((W.filter fun x => dist x s = t).card : ℝ) := by exact_mod_cast this
        _ ≤ ∑ _t ∈ T0, σ := sum_le_sum fun t ht => (hc.cap s hs t (hT0pos t ht)).le
        _ = T0.card * σ := by rw [sum_const, nsmul_eq_mul]
    have hT0c : (T0.card : ℝ) ≤ r + K := by
      have := card_union_le (S.image (dist b)) I0
      rw [← hT0] at this
      have h3 := card_image_le (s := S) (f := dist b)
      rw [hc.card] at h3
      have : T0.card ≤ r + K := by omega
      exact_mod_cast this
    calc (Rem.card : ℝ) ≤ ∑ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ _s ∈ S, (T0.card * σ) := sum_le_sum h2
      _ = r * (T0.card * σ) := by rw [sum_const, nsmul_eq_mul, hc.card]
      _ ≤ r * ((r + K) * σ) := by gcongr
      _ = r * (r + K) * σ := by ring
  have hCcard : ∀ k ∈ range K, τ - r * (r + K) * σ ≤ (C k).card := by
    intro k hk
    have h1 := card_le_card_sdiff_add_card (s := W.filter fun x => dist x b = ρ k) (t := Rem)
    have h2 : (((W.filter fun x => dist x b = ρ k).card : ℕ) : ℝ) ≤ (C k).card + Rem.card := by
      exact_mod_cast h1
    have := (hBig k hk).2.1
    linarith
  refine ⟨C, fun k _ => ρ k, ⟨singleton_nonempty b, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩, hCcard⟩
  · exact disjoint_singleton_right.2 hbS
  · rw [union_singleton_eq]; exact hc.ext b hb
  · intro k hk
    refine ⟨?_, fun x hx => (mem_filter.1 (mem_sdiff.1 hx).1).1⟩
    rw [← card_pos]
    have h := hCcard k hk
    have : (0 : ℝ) < (C k).card := by linarith
    exact_mod_cast this
  · intro k hk x hx b' hb'
    rw [mem_singleton] at hb'; subst hb'
    exact (mem_filter.1 (mem_sdiff.1 hx).1).2
  · intro k hk k' hk' b1 hb1 b2 hb2 h
    rw [mem_singleton] at hb1 hb2; subst hb1; subst hb2
    exact ⟨hρinj k hk k' hk' h, rfl⟩
  · intro k hk b' hb' hmem
    rw [mem_singleton] at hb'; subst hb'
    rw [union_singleton_eq] at hmem
    exact (hBig k hk).1 (dists_insert_subset S b' hmem)
  · intro k hk x hx
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    obtain ⟨hxW, hxb⟩ := mem_filter.1 hxf
    have hxb' : x ≠ b := by
      rintro rfl; rw [dist_self] at hxb; exact absurd hxb (hBig k hk).2.2.ne
    refine ⟨?_, ?_⟩
    · rw [union_singleton_eq]
      intro hmem
      rcases mem_insert.1 hmem with h | h
      · exact hxb' h
      · exact hWS x hxW h
    · rw [union_singleton_eq]
      have hnot : ∀ s ∈ S, dist x s ∉ T0 := fun s hs ht =>
        hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hxW, ht⟩⟩)
      refine rainbow_insert_insert S b x (hc.ext b hb) (hc.ext x hxW) ?_ ?_ ?_ ?_
      · intro s hs s' hs' h
        exact hnot s hs (mem_union_left _ (mem_image.2 ⟨s', hs', h.symm⟩))
      · intro s hs h
        rw [hxb] at h
        exact (hBig k hk).1 (mem_union_right _ (mem_image.2 ⟨s, hs, h.symm⟩))
      · intro s hs h
        rw [hxb] at h
        exact hnot s hs (mem_union_right _ (h ▸ hρmem k hk))
      · intro s hs s' hs' hne h
        rw [hxb] at h
        exact (hBig k hk).1 (mem_union_left _ (h ▸ mem_dists hs hs' hne))
  · intro k hk x hx s hs k' hk' b' hb' h
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    exact hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(mem_filter.1 hxf).1,
      mem_union_right _ (h ▸ hρmem k' hk')⟩⟩)

end E1088
