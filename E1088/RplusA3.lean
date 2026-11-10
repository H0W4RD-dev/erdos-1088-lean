import E1088.RplusA2

/-!
# Theorem R⁺, Step A: the covering (Step 4) and the conclusion (Step 5)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

section StepA

variable {n D h j : ℕ} {X S W S' : Finset (ℝ^d)} {σ : ℝ} {a b : ℝ^d} {ρ1 ρ2 : ℝ}

open Classical in
/-- Bad points of one class lie in the generic part (off the spheres `ρ_other, t`) or in `Sm`. -/
theorem StepACtx.bad_subset (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ ρo t : ℝ}
    (hρ0 : 0 < ρ) (hρT : ρ ∉ dists (TA S' a b)) (hab : dist a b ≠ ρ)
    (hV : ∀ v, v ∈ dists (TA S' a b) ∪ {ρ} ∪ {ρo, t} → v ∈ dists (TA S' a b) ∪ {ρ1, ρ2, t})
    (C : Finset (ℝ^d)) (hC : C = W.filter fun x => dist x b = ρ) :
    (C.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
        ∀ s ∈ S', dist x a ≠ dist x s) ⊆
      ((C.filter fun x => Rainbow (insert x (TA S' a b))).filter fun x =>
          dist x a ≠ ρo ∧ dist x a ≠ t) ∪
        (C.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ) := by
  intro x hx
  obtain ⟨hxC, hxV, hxs⟩ := mem_filter.1 hx
  have hxW : x ∈ W := by rw [hC] at hxC; exact (mem_filter.1 hxC).1
  have hxb : dist x b = ρ := by rw [hC] at hxC; exact (mem_filter.1 hxC).2
  by_cases hg : Rainbow (insert x (TA S' a b))
  · refine mem_union_left _ (mem_filter.2 ⟨mem_filter.2 ⟨hxC, hg⟩, ?_, ?_⟩)
    · intro e; exact hxV (hV _ (mem_union_right _ (by simp [e])))
    · intro e; exact hxV (hV _ (mem_union_right _ (by simp [e])))
  · rcases cx.step2 hρ0 hρT hab hxW hxb hg with h1 | h1 | h1
    · exact absurd (hV _ (mem_union_left _ h1)) hxV
    · obtain ⟨s, hs, he⟩ := h1; exact absurd he (hxs s hs)
    · exact mem_union_right _ (mem_filter.2 ⟨hxC, h1⟩)

open Classical in
theorem StepACtx.Sm_count (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (C : Finset (ℝ^d)) (hC : C ⊆ W) :
    (((C.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ).card : ℕ) : ℝ) ≤ 2 * n ^ 2 * σ := by
  have hσ0 : (0 : ℝ) ≤ σ := le_trans zero_le_one ((one_le_smin n D h).trans cx.hσ)
  have hs : (C.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ) ⊆
      S'.biUnion fun s => W.filter fun x => dist x s ∈ SmA S' a b ρ := by
    intro x hx
    obtain ⟨hxC, s, hs, hm⟩ := mem_filter.1 hx
    exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hC hxC, hm⟩⟩
  have h1 := removal_bound' cx.conf cx.sub (SmA S' a b ρ) (cx.SmA_pos hρ0)
  rw [cx.card] at h1
  have h2 : ((SmA S' a b ρ).card : ℝ) ≤ 2 * (n - 4 : ℕ) + 2 := by exact_mod_cast cx.SmA_card ρ
  have hn : ((n - 4 : ℕ) : ℝ) * (2 * (n - 4 : ℕ) + 2) ≤ 2 * n ^ 2 := by
    have h4 := cx.hn
    have hm : ((n - 4 : ℕ) : ℝ) + 4 = n := by
      have : n - 4 + 4 = n := by omega
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ ((n - 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [← hm]; nlinarith
  have h3 : ((n - 4 : ℕ) : ℝ) * ((SmA S' a b ρ).card * σ) ≤ 2 * n ^ 2 * σ := by
    calc ((n - 4 : ℕ) : ℝ) * ((SmA S' a b ρ).card * σ)
        ≤ (n - 4 : ℕ) * ((2 * (n - 4 : ℕ) + 2) * σ) := by gcongr
      _ = ((n - 4 : ℕ) * (2 * (n - 4 : ℕ) + 2)) * σ := by ring
      _ ≤ 2 * n ^ 2 * σ := mul_le_mul_of_nonneg_right hn hσ0
  exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Step 4** (manuscript (7.4)): one of the two classes is covered. -/
theorem StepACtx.cover (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) (C1 C2 : Finset (ℝ^d))
    (hC1 : C1 = W.filter fun x => dist x b = ρ1) (hC2 : C2 = W.filter fun x => dist x b = ρ2)
    (hQ1 : QA n D * σ ≤ C1.card) (hQ2 : QA n D * σ ≤ C2.card) :
    CoverA S' C1 a b ρ1 ρ2 (((D + 2 : ℕ) : ℝ) ^ kA n) ∨
      CoverA S' C2 a b ρ1 ρ2 (((D + 2 : ℕ) : ℝ) ^ kA n) := by
  set T := TA S' a b with hTdef
  set K' : ℝ := ((D + 2 : ℕ) : ℝ) ^ kA n with hK'
  have hK1 : 1 ≤ K' := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D + 2 by omega))
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans cx.hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast cx.hn
  have hn2 : (16 : ℝ) ≤ n ^ 2 := by nlinarith
  set θ : ℝ := 2 ^ 22 * n ^ 2 * K' ^ 4 * σ with hθ
  set κ : ℝ := 1 / (32 * K') with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ2 : κ ≤ 1 / 2 := by
    rw [hκ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hQ : QA n D = 2 ^ 27 * n ^ 2 * K' ^ 5 := rfl
  have hρ1T := cx.rho_notin cx.ρ1R cx.a1 (fun s hs => (cx.aS s hs).1)
  have hρ2T := cx.rho_notin cx.ρ2R cx.a2 (fun s hs => (cx.aS s hs).2)
  have hC1W : C1 ⊆ W := by rw [hC1]; exact filter_subset _ _
  have hC2W : C2 ⊆ W := by rw [hC2]; exact filter_subset _ _
  set Pg := C1.filter fun x => Rainbow (insert x T) with hPgdef
  set Qg := C2.filter fun x => Rainbow (insert x T) with hQgdef
  have hSm1 := cx.Sm_count cx.ρ1pos C1 hC1W
  have hSm2 := cx.Sm_count cx.ρ2pos C2 hC2W
  -- numerical facts
  have hK4 : 1 ≤ K' ^ 4 := one_le_pow₀ hK1
  have hK5 : K' ≤ K' ^ 5 := by
    calc K' = K' * 1 := by ring
      _ ≤ K' * K' ^ 4 := by gcongr
      _ = K' ^ 5 := by ring
  have N1 : 16 * K' * (θ + 2 * n ^ 2 * σ) ≤ QA n D * σ := by
    rw [hQ, hθ]
    have : 32 * K' * n ^ 2 * σ ≤ 2 ^ 26 * n ^ 2 * K' ^ 5 * σ := by
      have : 0 ≤ n ^ 2 * σ := by positivity
      nlinarith
    nlinarith
  have N2 : ∀ (C : Finset (ℝ^d)) (u : ℝ), QA n D * σ ≤ C.card → u ≤ κ * C.card →
      16 * K' * (u + 2 * n ^ 2 * σ) ≤ C.card := by
    intro C u hC hu
    have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    have e1 : 16 * K' * u ≤ C.card / 2 := by
      have := mul_le_mul_of_nonneg_left hu (show 0 ≤ 16 * K' by positivity)
      have e : 16 * K' * (κ * C.card) = C.card / 2 := by rw [hκ]; field_simp; ring
      linarith
    have e2 : 16 * K' * (2 * n ^ 2 * σ) ≤ C.card / 2 := by
      have : 32 * K' * n ^ 2 * σ ≤ 2 ^ 26 * n ^ 2 * K' ^ 5 * σ := by
        have : 0 ≤ n ^ 2 * σ := by positivity
        nlinarith
      rw [hQ] at hC
      nlinarith
    linarith
  have hV1 : ∀ t v, v ∈ dists T ∪ {ρ1} ∪ {ρ2, t} → v ∈ dists T ∪ {ρ1, ρ2, t} := by
    intro t v hv; simp only [mem_union, mem_insert, mem_singleton] at hv ⊢; tauto
  have hV2 : ∀ t v, v ∈ dists T ∪ {ρ2} ∪ {ρ1, t} → v ∈ dists T ∪ {ρ1, ρ2, t} := by
    intro t v hv; simp only [mem_union, mem_insert, mem_singleton] at hv ⊢; tauto
  have cov1 : ∀ t u, (((Pg.filter fun x => dist x a ≠ ρ2 ∧ dist x a ≠ t).card : ℕ) : ℝ) ≤ u →
      16 * K' * (u + 2 * n ^ 2 * σ) ≤ C1.card → CoverA S' C1 a b ρ1 ρ2 K' := by
    intro t u hu hfin
    refine ⟨t, le_trans ?_ hfin⟩
    have hs := cx.bad_subset cx.ρ1pos hρ1T cx.a1 (hV1 t) C1 hC1
    have h1 := (card_le_card hs).trans (card_union_le _ _)
    have h2 : (((C1.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
        ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤ u + 2 * n ^ 2 * σ := by
      have : (((C1.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
          ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤
          (((Pg.filter fun x => dist x a ≠ ρ2 ∧ dist x a ≠ t).card : ℕ) : ℝ) +
          (((C1.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ1).card : ℕ) : ℝ) := by
        exact_mod_cast h1
      linarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have cov2 : ∀ t u, (((Qg.filter fun x => dist x a ≠ ρ1 ∧ dist x a ≠ t).card : ℕ) : ℝ) ≤ u →
      16 * K' * (u + 2 * n ^ 2 * σ) ≤ C2.card → CoverA S' C2 a b ρ1 ρ2 K' := by
    intro t u hu hfin
    refine ⟨t, le_trans ?_ hfin⟩
    have hs := cx.bad_subset cx.ρ2pos hρ2T cx.a2 (hV2 t) C2 hC2
    have h1 := (card_le_card hs).trans (card_union_le _ _)
    have h2 : (((C2.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
        ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤ u + 2 * n ^ 2 * σ := by
      have : (((C2.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
          ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤
          (((Qg.filter fun x => dist x a ≠ ρ1 ∧ dist x a ≠ t).card : ℕ) : ℝ) +
          (((C2.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ2).card : ℕ) : ℝ) := by
        exact_mod_cast h1
      linarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  by_cases hP : (Pg.card : ℝ) < θ
  · left
    refine cov1 0 θ (le_trans (by exact_mod_cast card_le_card (filter_subset _ _)) hP.le)
      (N1.trans hQ1)
  by_cases hQs : (Qg.card : ℝ) < θ
  · right
    refine cov2 0 θ (le_trans (by exact_mod_cast card_le_card (filter_subset _ _)) hQs.le)
      (N1.trans hQ2)
  push Not at hP hQs
  -- both generic parts are large: the two-distribution lemma
  have hS2 := cx.S2 Pg Qg
    (fun x hx => by
      obtain ⟨hxC, hg⟩ := mem_filter.1 hx
      rw [hC1] at hxC; exact ⟨(mem_filter.1 hxC).1, (mem_filter.1 hxC).2, hg⟩)
    (fun x hx => by
      obtain ⟨hxC, hg⟩ := mem_filter.1 hx
      rw [hC2] at hxC; exact ⟨(mem_filter.1 hxC).1, (mem_filter.1 hxC).2, hg⟩)
  have hμ := four_pow_mu_le n D h σ cx.hσ
  have hP0 : (0 : ℝ) ≤ Pg.card := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ Qg.card := Nat.cast_nonneg _
  have hκ4θ : κ ^ 4 * θ = 4 * n ^ 2 * σ := by rw [hκ, hθ]; field_simp; ring
  have hN : ((((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
      dist q.1 a ≠ dist q.2 a).card : ℕ) : ℝ) ≤ κ ^ 4 * Qg.card * Pg.card := by
    refine hS2.trans ?_
    have hσn : σ ≤ n ^ 2 * σ := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n ^ 2 by linarith) hσ0
      linarith
    have e1 : 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) + n ^ 2 * σ ≤ 2 * n ^ 2 * σ := by
      linarith
    have e2 : 4 * n ^ 2 * σ * Pg.card ≤ κ ^ 4 * Qg.card * Pg.card := by
      rw [← hκ4θ]
      have : κ ^ 4 * θ ≤ κ ^ 4 * Qg.card := mul_le_mul_of_nonneg_left hQs (by positivity)
      exact mul_le_mul_of_nonneg_right this hP0
    have e3 : 4 * n ^ 2 * σ * Qg.card ≤ κ ^ 4 * Qg.card * Pg.card := by
      rw [← hκ4θ]
      have : κ ^ 4 * θ ≤ κ ^ 4 * Pg.card := mul_le_mul_of_nonneg_left hP (by positivity)
      have := mul_le_mul_of_nonneg_right this hQ0
      linarith [show κ ^ 4 * (Pg.card : ℝ) * Qg.card = κ ^ 4 * Qg.card * Pg.card by ring]
    have e4 : (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) + n ^ 2 * σ) * (Pg.card + Qg.card) ≤
        2 * n ^ 2 * σ * (Pg.card + Qg.card) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    linarith [show 2 * (n : ℝ) ^ 2 * σ * (Pg.card + Qg.card) =
      (4 * n ^ 2 * σ * Pg.card + 4 * n ^ 2 * σ * Qg.card) / 2 by ring]
  obtain ⟨t, ht | ht⟩ := two_dist Qg Pg (fun w => dist w a) (fun x => dist x a) ρ2 ρ1 κ hκ0 hκ2 hN
  · right
    refine cov2 t (κ * Qg.card) ht (N2 C2 _ hQ2 ?_)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (filter_subset _ _)) hκ0
  · left
    refine cov1 t (κ * Pg.card) ht (N2 C1 _ hQ1 ?_)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (filter_subset _ _)) hκ0

end StepA

open Classical in
/-- The set `A` of Step A. -/
noncomputable def AsetA (S W : Finset (ℝ^d)) (b : ℝ^d) (ρ1 ρ2 : ℝ) : Finset (ℝ^d) :=
  (W.erase b).filter fun a => dist a b ≠ ρ1 ∧ dist a b ≠ ρ2 ∧ Rainbow (insert a (insert b S))

open Classical in
theorem mem_AsetA {S W : Finset (ℝ^d)} {b : ℝ^d} {ρ1 ρ2 : ℝ} {a : ℝ^d} :
    a ∈ AsetA S W b ρ1 ρ2 ↔ a ∈ W.erase b ∧ dist a b ≠ ρ1 ∧ dist a b ≠ ρ2 ∧
      Rainbow (insert a (insert b S)) := by
  unfold AsetA; exact mem_filter

open Classical in
/-- **Step A** (manuscript Lemma 7.3), with the sphere/class removals done by the caller:
the set `A` of `a ∈ W \ {b}` off both spheres with `S ∪ {b, a}` rainbow has
`|A| ≤ 2e + 2(n-4)σ`. -/
theorem stepA {n D h j : ℕ} (hn : 4 ≤ n) (hj1 : n - 4 ≤ j) {X S W : Finset (ℝ^d)} {σ : ℝ}
    (hX : Ambient n D h X) (hc : Config X S W j σ) (hσ : smin n D h ≤ σ) (hk : kA n ≤ kstar n)
    {b : ℝ^d} (hb : b ∈ W) {ρ1 ρ2 : ℝ} (hρ : ρ1 ≠ ρ2) (hρ1 : ρ1 ∈ Big S W b (QA n D * σ))
    (hρ2 : ρ2 ∈ Big S W b (QA n D * σ)) :
    (((AsetA S W b ρ1 ρ2).card : ℕ) : ℝ) ≤
      2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ := by
  obtain ⟨S', hS'S, hS'c⟩ := exists_subset_card_eq (show n - 4 ≤ S.card by rw [hc.card]; exact hj1)
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  set e := 2 * LRcost (kstar n) (D + 2) * h with hedef
  have he0 : 0 ≤ e := e_nonneg n D h
  have heσ : e < σ := lt_of_lt_of_le (e_lt_smin n D h) hσ
  set K' : ℝ := ((D + 2 : ℕ) : ℝ) ^ kA n with hK'
  have hK1 : 1 ≤ K' := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D + 2 by omega))
  have hQ1 : (1 : ℝ) ≤ QA n D := by
    unfold QA
    have : (1 : ℝ) ≤ n ^ 2 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have : (1 : ℝ) ≤ K' ^ 5 := one_le_pow₀ hK1
    rw [← hK']
    have : (1 : ℝ) ≤ 2 ^ 27 := by norm_num
    nlinarith [mul_le_mul this ‹(1 : ℝ) ≤ n ^ 2› zero_le_one (by positivity)]
  -- facts from `Big`
  have bigfacts : ∀ ρ ∈ Big S W b (QA n D * σ), 0 < ρ ∧ ρ ∉ Rb S b ∧
      QA n D * σ ≤ ((W.filter fun x => dist x b = ρ).card : ℝ) := by
    intro ρ hρ
    obtain ⟨himg, hR, hcard⟩ := mem_filter.1 hρ
    obtain ⟨x, hx, rfl⟩ := mem_image.1 himg
    exact ⟨dist_pos.2 (ne_of_mem_erase hx), hR, hcard⟩
  obtain ⟨hρ1p, hρ1R, hC1big⟩ := bigfacts ρ1 hρ1
  obtain ⟨hρ2p, hρ2R, hC2big⟩ := bigfacts ρ2 hρ2
  set A := AsetA S W b ρ1 ρ2 with hAdef
  set A0 := A.filter fun a => ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2 with hA0def
  -- `A \ A0` is small
  have hrem : ((A.filter fun a => ¬ ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2).card : ℝ) ≤
      2 * (n - 4 : ℕ) * σ := by
    have hs : (A.filter fun a => ¬ ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2) ⊆
        S'.biUnion fun s => W.filter fun x => dist x s ∈ ({ρ1, ρ2} : Finset ℝ) := by
      intro x hx
      obtain ⟨hxA, hn'⟩ := mem_filter.1 hx
      push Not at hn'
      obtain ⟨s, hs, hse⟩ := hn'
      have hxW : x ∈ W := (mem_erase.1 (mem_AsetA.1 hxA).1).2
      refine mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hxW, ?_⟩⟩
      by_cases h1 : dist x s = ρ1
      · simp [h1]
      · simp [hse h1]
    have h1 := removal_bound' hc hS'S ({ρ1, ρ2} : Finset ℝ) (by
      intro t ht; simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl; exact hρ1p; exact hρ2p)
    rw [hS'c] at h1
    have h2 : (({ρ1, ρ2} : Finset ℝ).card : ℝ) ≤ 2 := by exact_mod_cast card_le_two
    have h3 : ((n - 4 : ℕ) : ℝ) * ((({ρ1, ρ2} : Finset ℝ).card : ℝ) * σ) ≤ 2 * (n - 4 : ℕ) * σ := by
      have : ((n - 4 : ℕ) : ℝ) * ((({ρ1, ρ2} : Finset ℝ).card : ℝ) * σ) ≤
          (n - 4 : ℕ) * (2 * σ) := by gcongr
      linarith [show ((n - 4 : ℕ) : ℝ) * (2 * σ) = 2 * (n - 4 : ℕ) * σ by ring]
    exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)
  -- each `a ∈ A0` gives a Step A context
  have hctx : ∀ a ∈ A0, StepACtx n D h j X S W S' σ a b ρ1 ρ2 := by
    intro a ha
    obtain ⟨haA, haS⟩ := mem_filter.1 ha
    obtain ⟨hae, ha1, ha2, harb⟩ := mem_AsetA.1 haA
    obtain ⟨hab, haW⟩ := mem_erase.1 hae
    exact ⟨hn, hX, hc, hσ, hS'S, hS'c, hb, haW, hab, hρ, hρ1p, hρ2p, hρ1R, hρ2R, ha1, ha2, harb, haS⟩
  set C1 := W.filter fun x => dist x b = ρ1 with hC1
  set C2 := W.filter fun x => dist x b = ρ2 with hC2
  have hcov : ∀ a ∈ A0, CoverA S' C1 a b ρ1 ρ2 K' ∨ CoverA S' C2 a b ρ1 ρ2 K' := fun a ha =>
    (hctx a ha).cover C1 C2 hC1 hC2 hC1big hC2big
  -- Step 5 for each class
  have hTcard : ∀ a ∈ A0, (dists (TA S' a b)).card ≤ (n - 2).choose 2 := by
    intro a ha
    have := card_dists_le (TA S' a b)
    rwa [(hctx a ha).card_T] at this
  have step5 : ∀ (C : Finset (ℝ^d)) (ρ : ℝ), C = W.filter (fun x => dist x b = ρ) →
      QA n D * σ ≤ C.card →
      ((A0.filter fun a => CoverA S' C a b ρ1 ρ2 K').card : ℝ) ≤ e := by
    intro C ρ hC hCbig
    have hCX : C ⊆ X := by rw [hC]; exact (filter_subset _ _).trans hc.subW
    set Aν := A0.filter fun a => CoverA S' C a b ρ1 ρ2 K' with hAν
    have hAνX : Aν ⊆ X := fun a ha =>
      hc.subW (mem_erase.1 (mem_AsetA.1 (mem_filter.1 (mem_filter.1 ha).1).1).1).2
    choose! tt htt using fun a (ha : a ∈ Aν) => (mem_filter.1 ha).2
    refine gl_lr_or_sets n D h X hX.dim hX.half C Aν hCX hAνX ((n - 2).choose 2 + 3)
      (fun a => (dists (TA S' a b) ∪ {ρ1, ρ2, tt a}).image (· ^ 2)) ?_ S'
      (by rw [hS'c]; unfold kA at hk; omega) ?_ ?_
    · intro a ha
      refine card_image_le.trans ((card_union_le _ _).trans ?_)
      have e1 := hTcard a (mem_filter.1 ha).1
      have e2 : ({ρ1, ρ2, tt a} : Finset ℝ).card ≤ 3 := card_le_three
      omega
    · intro a ha
      rw [hS'c]
      have hexp : (n - 2).choose 2 + 3 + (n - 4) = kA n := rfl
      rw [hexp, ← hK']
      refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (card_le_card ?_)) (by positivity))
        (htt a ha)
      intro x hx
      rw [mem_filter] at hx ⊢
      obtain ⟨hxC, hv, hps⟩ := hx
      exact ⟨hxC, fun h => hv (mem_image.2 ⟨_, h, by rw [dist_eq_norm]⟩),
        fun s hs h => hps s hs (by rw [← dist_eq_norm, ← dist_eq_norm, h])⟩
    · have : σ ≤ QA n D * σ := by nlinarith
      linarith
  have h1 := step5 C1 ρ1 hC1 hC1big
  have h2 := step5 C2 ρ2 hC2 hC2big
  have hA0sub : A0 ⊆ (A0.filter fun a => CoverA S' C1 a b ρ1 ρ2 K') ∪
      (A0.filter fun a => CoverA S' C2 a b ρ1 ρ2 K') := by
    intro a ha
    rcases hcov a ha with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨ha, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨ha, h⟩)
  have hA0 : (A0.card : ℝ) ≤ 2 * e := by
    have := (card_le_card hA0sub).trans (card_union_le _ _)
    have : (A0.card : ℝ) ≤ ((A0.filter fun a => CoverA S' C1 a b ρ1 ρ2 K').card : ℝ) +
        ((A0.filter fun a => CoverA S' C2 a b ρ1 ρ2 K').card : ℝ) := by exact_mod_cast this
    linarith
  have hsplit := card_filter_add_card_filter_not (s := A)
    (fun a => ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2)
  have : (A.card : ℝ) = A0.card +
      ((A.filter fun a => ¬ ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2).card : ℝ) := by
    rw [hA0def]; exact_mod_cast hsplit.symm
  rw [this]
  linarith

end E1088
