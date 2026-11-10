import E1088.E1Final
import E1088.RplusLow
import E1088.N3

/-!
# Assembly: all Claims (manuscript Theorem 10.1) and the halving step (Theorem 10.3)

Everything in this file is proved; it uses the named results of E1088/Skeleton.lean
(Theorem R⁺ is `theorem_Rplus_proved`, the Core Lemma `core_lemma_proved`; E1_r is
`theorem_E1_proved`) together with the proved
`lemma_HR` (Lemma 1.1) and `lemma_1_2` (kill step), and the LR loss bound `LRcost_le`.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem pow_le_pow_of_le {a : ℝ} (ha : 1 ≤ a) {p q : ℕ} (h : p ≤ q) : a ^ p ≤ a ^ q :=
  pow_le_pow_right₀ ha h

theorem natsq_le_pow (a : ℝ) (ha : 2 ≤ a) (r : ℕ) : ((r ^ 2 : ℕ) : ℝ) ≤ a ^ (r ^ 2) := by
  have h1 : r ^ 2 < 2 ^ (r ^ 2) := Nat.lt_two_pow_self
  have h2 : ((r ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r ^ 2) := by exact_mod_cast h1.le
  exact h2.trans (pow_le_pow_left₀ (by norm_num) ha _)

/-- One step of the downward induction of Theorem 10.1. -/
theorem claim_step (n : ℕ) (hn : 5 ≤ n) (c₁ : ℕ)
    (hE1 : ∀ (d D h r : ℕ), r ≤ n - 5 → ∀ (Γ' : ℝ), 1 ≤ Γ' →
      ∃ ratio : ℝ, 1 ≤ ratio ∧ ratio ≤ ((D + 2 : ℕ) : ℝ) ^ c₁ * Γ' ^ c₁ ∧
        ∀ (X : Finset (ℝ^d)), Ambient n D h X → ∀ (S W : Finset (ℝ^d)) (σ : ℝ),
          Config X S W r σ → smin n D h ≤ σ → HRholds S W σ Γ' →
          ∀ b ∈ W, (Big S W b (ratio * σ)).card < Kr n r)
    (r g : ℕ) (hr : r ≤ n - 5)
    (hclaim : ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ClaimAt X (r + 1) (((D + 2 : ℕ) : ℝ) ^ g) (smin n D h)) :
    ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ClaimAt X r (((D + 2 : ℕ) : ℝ) ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2) +
        (g + c₁ + c₁ * (g + r ^ 2 + 1)) + r ^ 2 + 1)) (smin n D h) := by
  intro d D h X hX hD S W σ hc hσ
  have ha3' : (3 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ D + 2 by omega)
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha3 : 3 ≤ a := ha3'
  have ha1 : 1 ≤ a := by linarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσpos : 0 < σ := by linarith
  set Γ := a ^ g with hΓ
  have hΓ1 : 1 ≤ Γ := one_le_pow₀ ha1
  have hcl := hclaim d D h X hX hD
  -- HR_r
  have hHR := lemma_HR X r Γ (smin n D h) σ hcl S W hc hσpos hσ
  set Γ' := Γ + (r : ℝ) ^ 2 with hΓ'
  have hΓ'1 : 1 ≤ Γ' := by have := sq_nonneg (r : ℝ); linarith
  -- E1_r
  obtain ⟨ratio, hrat1, hrat, hbig⟩ := hE1 d D h r hr Γ' hΓ'1
  have hbig' : ∀ b ∈ W, (Big S W b (ratio * σ)).card ≤ Kr n r - 1 := by
    intro b hb; have := hbig X hX S W σ hc hσ hHR b hb; omega
  -- kill step
  have hkill := lemma_1_2 X D hX.dim r (Kr n r - 1) Γ (smin n D h) σ (ratio * σ) hcl S W hc
    (by linarith) hσpos hσ (by nlinarith) hbig'
  -- bounding the constants
  have hr2 : (r : ℝ) ^ 2 ≤ a ^ (r ^ 2) := by
    have := natsq_le_pow a (by linarith) r; push_cast at this; exact this
  have hΓ'le : Γ' ≤ a ^ (g + r ^ 2 + 1) := by
    have e1 : Γ ≤ a ^ (g + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e2 : a ^ (r ^ 2) ≤ a ^ (g + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e3 : a ^ (g + r ^ 2 + 1) = a ^ (g + r ^ 2) * a := pow_succ _ _
    have e4 : 1 ≤ a ^ (g + r ^ 2) := one_le_pow₀ ha1
    rw [e3]; nlinarith
  have hratle : ratio ≤ a ^ (c₁ + c₁ * (g + r ^ 2 + 1)) := by
    rw [pow_add, mul_comm c₁, pow_mul]
    exact hrat.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) hΓ'le c₁) (by positivity))
  set E := g + c₁ + c₁ * (g + r ^ 2 + 1) with hE
  have hΓrat : Γ * ratio ≤ a ^ E := by
    rw [hE, Nat.add_assoc, pow_add]
    exact mul_le_mul_of_nonneg_left hratle (by positivity)
  have hsum : Γ * ratio + (r : ℝ) ^ 2 + 1 ≤ a ^ (E + r ^ 2 + 1) := by
    have e1 : a ^ E ≤ a ^ (E + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e2 : a ^ (r ^ 2) ≤ a ^ (E + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e3 : (1 : ℝ) ≤ a ^ (E + r ^ 2) := one_le_pow₀ ha1
    have e4 : a ^ (E + r ^ 2 + 1) = a ^ (E + r ^ 2) * a := pow_succ _ _
    rw [e4]; nlinarith
  have hdS : (dists S).card ≤ r.choose 2 := by
    have := card_dists_le S; rw [hc.card] at this; exact this
  have hP : ((((D + 2) ^ (Kr n r - 1 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) ≤
      a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2)) := by
    rw [ha]
    push_cast
    rw [← pow_mul, mul_comm (Kr n r - 1 + 2 * r + (dists S).card) 2]
    exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) D; linarith) (by omega)
  have hP0 : (0 : ℝ) ≤ ((((D + 2) ^ (Kr n r - 1 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  calc (W.card : ℝ)
      ≤ ((((D + 2) ^ (Kr n r - 1 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) *
          (Γ * (ratio * σ) + (r : ℝ) ^ 2 * σ + 1) := hkill
    _ ≤ a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2)) * ((Γ * ratio + (r : ℝ) ^ 2 + 1) * σ) := by
        apply mul_le_mul hP _ (by positivity) (by positivity)
        nlinarith
    _ ≤ a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2)) * (a ^ (E + r ^ 2 + 1) * σ) := by
        gcongr
    _ = a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2) + E + r ^ 2 + 1) * σ := by
        rw [show 2 * (Kr n r - 1 + 2 * r + r.choose 2) + E + r ^ 2 + 1 =
          2 * (Kr n r - 1 + 2 * r + r.choose 2) + (E + r ^ 2 + 1) by ring, pow_add]; ring

/-- **Theorem 10.1 at level 0** (all Claims, downward induction). -/
theorem all_claims (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ClaimAt X 0 (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
  obtain ⟨c₀, htop⟩ := theorem_Rplus_proved n hn
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · exact ⟨c₀, fun d D h X hX hD => htop d D h X hX hD 0 (by norm_num) (by norm_num)⟩
  have hn5' : 5 ≤ n := hn5
  obtain ⟨c₁, hE1⟩ := theorem_E1_proved n hn5'
  -- downward induction: level `n - 4 - i`
  have key : ∀ i, i ≤ n - 4 → ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X →
      1 ≤ D → ClaimAt X (n - 4 - i) (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨c₀, fun d D h X hX hD => htop d D h X hX hD (n - 4 - 0) (by omega) (by omega)⟩
    | succ i ih =>
      intro hi
      obtain ⟨g, hg⟩ := ih (by omega)
      have hr : n - 4 - (i + 1) ≤ n - 5 := by omega
      have hlev : n - 4 - (i + 1) + 1 = n - 4 - i := by omega
      refine ⟨_, claim_step n hn5' c₁ hE1 (n - 4 - (i + 1)) g hr ?_⟩
      intro d D h X hX hD
      rw [hlev]; exact hg d D h X hX hD
  obtain ⟨c, hc⟩ := key (n - 4) le_rfl
  refine ⟨c, fun d D h X hX hD => ?_⟩
  have := hc d D h X hX hD
  rwa [show n - 4 - (n - 4) = 0 by omega] at this

theorem config_zero (X : Finset (ℝ^d)) (σ : ℝ) : Config X ∅ X 0 σ := by
  refine ⟨empty_subset _, ?_, rfl, subset_refl _, disjoint_empty_right _, ?_, by simp⟩
  · intro a ha; simp at ha
  · intro x _ a ha a' ha' _ _ _ _ hne _ _
    simp only [insert_empty, mem_singleton] at ha ha'
    exact absurd (ha.trans ha'.symm) hne

theorem two_rpow_natpow (a : ℝ) (ha : 0 < a) (c : ℕ) : a ^ c = (2 : ℝ) ^ (c * Real.logb 2 a) := by
  rw [mul_comm (c : ℝ), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) ha,
    Real.rpow_natCast]

/-- **The halving step** for `n ≥ 4` (manuscript Theorem 10.3 / round14 Theorem 1.6). -/
theorem halving_step_ge4 (n : ℕ) (hn : 4 ≤ n) : HalvingStep n := by
  obtain ⟨c, hc⟩ := all_claims n hn
  obtain ⟨Ck, hCk0, hCk⟩ := LRcost_le (kstar n)
  refine ⟨c + 2 * n + 2 + 6 * Ck + 1, by positivity, fun d D B X hX hD hY => ?_⟩
  set Cst : ℝ := c + 2 * n + 2 + 6 * Ck + 1 with hCst
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have := card_le_one_of_affDim_zero X (by have := hD; omega)
    have h1 : (X.card : ℝ) ≤ 1 := by exact_mod_cast this
    simp only [halvingExp, Nat.cast_zero, Real.sqrt_zero, zero_mul, mul_zero, Real.rpow_zero,
      one_mul]
    have := Nat.cast_nonneg (α := ℝ) B; linarith
  have hamb : Ambient n D B X :=
    ⟨hX, hD, fun Y hYX hYd => hY Y ((rainbowFree_iff n Y).2 fun A hA hAn =>
      (rainbowFree_iff n X).1 hX A (hA.trans hYX) hAn) hYd⟩
  have hbound := hc d D B X hamb hDpos ∅ X (smin n D B) (config_zero X _) le_rfl
  -- `|X| ≤ (D+2)^c · 4^{n+1} · LRcost · (B+1)`
  set L : ℝ := Real.sqrt D * Real.logb 2 (D + 2) with hL
  have hL1 : 1 ≤ L := sqrt_mul_logb_ge_one D hDpos
  have hsq1 : 1 ≤ Real.sqrt D := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hDpos)
  have hlog0 : 0 ≤ Real.logb 2 ((D : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  have hA : (((D + 2 : ℕ) : ℝ)) ^ c ≤ (2 : ℝ) ^ (c * L) := by
    rw [two_rpow_natpow _ (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [hL]; nlinarith
  have hB4 : (4 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ ((2 * n + 2) * L) := by
    rw [show (4 : ℝ) ^ (n + 1) = (2 : ℝ) ^ (((2 * n + 2 : ℕ) : ℝ)) by
      rw [Real.rpow_natCast, show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]; norm_num]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; nlinarith
  have hLr : Lr (D + 2) ≤ 6 * L := by
    unfold Lr
    push_cast
    have h1 : Real.sqrt ((D : ℝ) + 2 + 2) ≤ 3 * Real.sqrt D := by
      rw [show (3 : ℝ) * Real.sqrt D = Real.sqrt (9 * D) by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      apply Real.sqrt_le_sqrt
      have : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
      linarith
    have h2 : Real.logb 2 ((D : ℝ) + 2 + 2) ≤ 2 * Real.logb 2 ((D : ℝ) + 2) := by
      rw [← Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      rw [show ((D : ℝ) + 2) ^ (2 : ℝ) = ((D : ℝ) + 2) ^ (2 : ℕ) by norm_cast]
      nlinarith [Nat.cast_nonneg (α := ℝ) D]
    have h3 : 0 ≤ Real.logb 2 ((D : ℝ) + 2 + 2) :=
      Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
    calc Real.sqrt ((D : ℝ) + 2 + 2) * Real.logb 2 ((D : ℝ) + 2 + 2)
        ≤ (3 * Real.sqrt D) * (2 * Real.logb 2 ((D : ℝ) + 2)) :=
          mul_le_mul h1 h2 h3 (by positivity)
      _ = 6 * L := by rw [hL]; ring
  have hC : LRcost (kstar n) (D + 2) ≤ (2 : ℝ) ^ (6 * Ck * L) := by
    refine (hCk (D + 2)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    nlinarith
  have hB1 : (0 : ℝ) ≤ B + 1 := by positivity
  calc (X.card : ℝ) ≤ (((D + 2 : ℕ) : ℝ)) ^ c * smin n D B := hbound
    _ = (((D + 2 : ℕ) : ℝ)) ^ c * (4 ^ (n + 1) * LRcost (kstar n) (D + 2)) * (B + 1) := by
        unfold smin; ring
    _ ≤ (2 : ℝ) ^ (c * L) * ((2 : ℝ) ^ ((2 * n + 2) * L) * (2 : ℝ) ^ (6 * Ck * L)) * (B + 1) := by
        have hLR0 : 0 ≤ LRcost (kstar n) (D + 2) := le_trans zero_le_one (one_le_LRcost _ _)
        apply mul_le_mul_of_nonneg_right _ hB1
        exact mul_le_mul hA (mul_le_mul hB4 hC hLR0 (by positivity)) (by positivity)
          (by positivity)
    _ = (2 : ℝ) ^ ((c + 2 * n + 2 + 6 * Ck) * L) * (B + 1) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ halvingExp Cst D * (B + 1) := by
        gcongr
        · norm_num
        · rw [halvingExp, hCst, ← hL]; nlinarith

/-- `L(D+2) ≤ 6 √D log₂(D+2)` for `D ≥ 1`. -/
theorem Lr_le (D : ℕ) (hDpos : 0 < D) :
    Lr (D + 2) ≤ 6 * (Real.sqrt D * Real.logb 2 (D + 2)) := by
  unfold Lr
  push_cast
  have h1 : Real.sqrt ((D : ℝ) + 2 + 2) ≤ 3 * Real.sqrt D := by
    rw [show (3 : ℝ) * Real.sqrt D = Real.sqrt (9 * D) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    apply Real.sqrt_le_sqrt
    have : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
    linarith
  have h2 : Real.logb 2 ((D : ℝ) + 2 + 2) ≤ 2 * Real.logb 2 ((D : ℝ) + 2) := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [show ((D : ℝ) + 2) ^ (2 : ℝ) = ((D : ℝ) + 2) ^ (2 : ℕ) by norm_cast]
    nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have h3 : 0 ≤ Real.logb 2 ((D : ℝ) + 2 + 2) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  calc Real.sqrt ((D : ℝ) + 2 + 2) * Real.logb 2 ((D : ℝ) + 2 + 2)
      ≤ (3 * Real.sqrt D) * (2 * Real.logb 2 ((D : ℝ) + 2)) :=
        mul_le_mul h1 h2 h3 (by positivity)
    _ = 6 * (Real.sqrt D * Real.logb 2 (D + 2)) := by ring

/-- **The halving step** for `n = 3`, from the G1 argument of E1088/N3.lean (Blokhuis's theorem
is not used). -/
theorem halving_step_three : HalvingStep 3 := by
  obtain ⟨Ck, hCk0, hCk⟩ := LRcost_le (kG 3)
  refine ⟨4 + 6 * Ck + 1, by positivity, fun d D B X hX hD hY => ?_⟩
  set Cst : ℝ := 4 + 6 * Ck + 1 with hCst
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have := card_le_one_of_affDim_zero X (by have := hD; omega)
    have h1 : (X.card : ℝ) ≤ 1 := by exact_mod_cast this
    simp only [halvingExp, Nat.cast_zero, Real.sqrt_zero, zero_mul, mul_zero, Real.rpow_zero,
      one_mul]
    have := Nat.cast_nonneg (α := ℝ) B; linarith
  have hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ B := fun Y hYX hYd =>
    hY Y ((rainbowFree_iff 3 Y).2 fun A hA hAn => (rainbowFree_iff 3 X).1 hX A (hA.trans hYX) hAn)
      hYd
  have hb := card_le_n3 D B X hX hD hh
  set L : ℝ := Real.sqrt D * Real.logb 2 (D + 2) with hL
  have hL1 : 1 ≤ L := sqrt_mul_logb_ge_one D hDpos
  have hsq1 : 1 ≤ Real.sqrt D := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hDpos)
  have hlog0 : 0 ≤ Real.logb 2 ((D : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  set LR := LRcost (kG 3) (D + 2) with hLRdef
  have hLR1 : 1 ≤ LR := one_le_LRcost _ _
  have hLR : LR ≤ (2 : ℝ) ^ (6 * Ck * L) := by
    refine (hCk (D + 2)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have := Lr_le D hDpos; rw [← hL] at this; nlinarith
  have hD2 : ((D : ℝ) + 2) ≤ (2 : ℝ) ^ L := by
    calc ((D : ℝ) + 2) = (2 : ℝ) ^ (Real.logb 2 ((D : ℝ) + 2)) := by
          rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
      _ ≤ (2 : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hL]; nlinarith)
  have h5 : (5 : ℝ) ≤ (2 : ℝ) ^ (3 * L) := by
    calc (5 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℕ) : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (3 * L) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hstep : (X.card : ℝ) ≤ ((D : ℝ) + 2) * (5 * LR * (B + 1)) := by
    have e1 : 1 + 4 * (LR * B) ≤ 5 * LR * (B + 1) := by nlinarith
    have e2 : (0 : ℝ) ≤ 1 + 4 * (LR * B) := by positivity
    have e3 : (1 : ℝ) ≤ 1 + 4 * (LR * B) := by nlinarith
    calc (X.card : ℝ) ≤ 1 + (D + 1) * (1 + 4 * (LR * B)) := hb
      _ ≤ ((D : ℝ) + 2) * (1 + 4 * (LR * B)) := by nlinarith
      _ ≤ ((D : ℝ) + 2) * (5 * LR * (B + 1)) := by gcongr
  calc (X.card : ℝ) ≤ ((D : ℝ) + 2) * (5 * LR * (B + 1)) := hstep
    _ ≤ (2 : ℝ) ^ L * ((2 : ℝ) ^ (3 * L) * (2 : ℝ) ^ (6 * Ck * L) * (B + 1)) := by
        apply mul_le_mul hD2 _ (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul h5 hLR (by linarith) (by positivity)
    _ = (2 : ℝ) ^ ((4 + 6 * Ck) * L) * (B + 1) := by
        rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num),
          ← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ halvingExp Cst D * (B + 1) := by
        gcongr
        · norm_num
        · rw [halvingExp, hCst, ← hL]; nlinarith

/-- **The halving step** for every `n ≥ 3`. -/
theorem halving_step : ∀ n ≥ 3, HalvingStep n := by
  intro n hn
  rcases Nat.eq_or_lt_of_le hn with rfl | h
  · exact halving_step_three
  · exact halving_step_ge4 n h

end E1088
