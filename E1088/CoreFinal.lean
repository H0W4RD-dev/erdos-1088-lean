import E1088.CoreStep5
import E1088.Rplus

/-!
# The Core Lemma (manuscript Theorem 8.2), assembled from Steps 0–5

Constants (cf. manuscript Section 8, "Constants" and Lemma 8.3): with `E = D + 2`,
`K = E^{k_c}`, `G = Γ' K`,
`ε = 1/(3072 G)`, `δ₁ = 1/(512 G)`, and, for `w ∈ {w₁, w₂}` and an index `j`,
`θ_w(j) = |C_j| / (32 Γ' E^{k₄(w)}) + σ` (the paper uses `max` instead of `+`).
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

theorem choose_two_le_sq' (m : ℕ) : m.choose 2 ≤ m * m := by
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem quad_le_six_pow (n : ℕ) (hn : 5 ≤ n) : n ^ 2 + 7 * n + 1 ≤ 6 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ 6 k]
      nlinarith

theorem kc_le_kstar (n r : ℕ) (hn : 5 ≤ n) (hr : r ≤ n) : kc n r ≤ kstar n := by
  have h0 : kc n r ≤ 3 * n ^ 2 + 7 * n + 1 := by
    show (n - 2) + (n - 2).choose 2 + (n - 4 - r) + 1 + r +
      ((n - 2) + (n - 2).choose 2 + (n - 4 - r) + 2 * r + r.choose 2) ≤ 3 * n ^ 2 + 7 * n + 1
    have h1 := choose_two_le_sq' (n - 2)
    have h2 := choose_two_le_sq' r
    have h3 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h4 : r * r ≤ n * n := Nat.mul_le_mul hr hr
    have h6 : n ^ 2 = n * n := sq n
    rw [h6]
    generalize (n - 2).choose 2 = C1 at *
    generalize r.choose 2 = C2 at *
    generalize (n - 2) * (n - 2) = P at *
    generalize r * r = R at *
    generalize n * n = Z at *
    omega
  have := quad_le_six_pow n hn
  unfold kstar
  omega

/-- The numerical side conditions of Steps 3 and 4. -/
theorem params34 (E Γ' σ δ Cj K : ℝ) (a b r n : ℕ) (hE : 1 ≤ E) (hΓ : 1 ≤ Γ') (hσ : 0 ≤ σ)
    (hK : E ^ (a + b) ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (512 * Γ' * K)) (hrn : r + 1 ≤ n)
    (hM : 32 * K * Γ' * n * σ ≤ Cj) :
    σ ≤ Cj / (32 * Γ' * E ^ b) + σ ∧
      16 * E ^ a * (δ * Cj) ≤ Cj / (32 * Γ' * E ^ b) + σ ∧
      16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b) + σ + r * σ)) ≤ Cj := by
  have hEa : 1 ≤ E ^ a := one_le_pow₀ hE
  have hEb : 1 ≤ E ^ b := one_le_pow₀ hE
  have hab : E ^ a * E ^ b ≤ K := by rw [← pow_add]; exact hK
  have hK1 : 1 ≤ K := le_trans (by nlinarith) hab
  have hEbK : E ^ b ≤ K := le_trans (by nlinarith) hab
  have hn1 : (r : ℝ) + 1 ≤ n := by exact_mod_cast hrn
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hKσ : 0 ≤ 32 * K * Γ' * n * σ := by
    have : (0 : ℝ) ≤ n := by linarith
    positivity
  have hCj : 0 ≤ Cj := hKσ.trans hM
  have hpos : 0 < 32 * Γ' * E ^ b := by positivity
  refine ⟨by have := div_nonneg hCj hpos.le; linarith, ?_, ?_⟩
  · have h1 : δ * Cj ≤ Cj / (512 * Γ' * K) := by
      calc δ * Cj ≤ 1 / (512 * Γ' * K) * Cj := mul_le_mul_of_nonneg_right hδ hCj
        _ = Cj / (512 * Γ' * K) := by ring
    have h2 : 16 * E ^ a * (Cj / (512 * Γ' * K)) ≤ Cj / (32 * Γ' * E ^ b) := by
      rw [show 16 * E ^ a * (Cj / (512 * Γ' * K)) = 16 * E ^ a * Cj / (512 * Γ' * K) by ring,
        div_le_div_iff₀ (by positivity) hpos]
      have := mul_le_mul_of_nonneg_left hab (show 0 ≤ 512 * Γ' * Cj by positivity)
      nlinarith
    have h3 : 16 * E ^ a * (δ * Cj) ≤ 16 * E ^ a * (Cj / (512 * Γ' * K)) := by gcongr
    linarith
  · have h1 : 16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b))) = Cj / 2 := by
      field_simp; ring
    have h2 : 16 * E ^ b * (Γ' * (σ + r * σ)) ≤ Cj / 2 := by
      have e1 : 16 * E ^ b * (Γ' * (σ + r * σ)) = 16 * E ^ b * Γ' * ((r + 1) * σ) := by ring
      have e2 : (r + 1 : ℝ) * σ ≤ n * σ := mul_le_mul_of_nonneg_right hn1 hσ
      have e3 : 16 * E ^ b * Γ' * ((r + 1) * σ) ≤ 16 * K * Γ' * (n * σ) := by
        have : 0 ≤ (r + 1 : ℝ) * σ := by positivity
        calc 16 * E ^ b * Γ' * ((r + 1) * σ) ≤ 16 * K * Γ' * ((r + 1) * σ) := by gcongr
          _ ≤ 16 * K * Γ' * (n * σ) := by gcongr
      nlinarith
    have : 16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b) + σ + r * σ)) =
        16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b))) + 16 * E ^ b * (Γ' * (σ + r * σ)) := by ring
    linarith

/-- `μ = LRcost(k_G, D+2) h ≤ σ`. -/
theorem mu_le_sigma (n D h : ℕ) (σ : ℝ) (hσ : smin n D h ≤ σ) :
    LRcost (kG n) (D + 2) * h ≤ σ := by
  have h1 := LRcost_mono (D + 2) (kG_le_kstar n)
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have h2 : LRcost (kG n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * h :=
    mul_le_mul_of_nonneg_right h1 h0
  have h3 : LRcost (kstar n) (D + 2) * h ≤ smin n D h := by
    unfold smin
    have e1 : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have e2 := one_le_LRcost (kstar n) (D + 2)
    have a1 : LRcost (kstar n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * (h + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : LRcost (kstar n) (D + 2) * (h + 1) ≤ 4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * (h + 1)) :=
      le_mul_of_one_le_left (by positivity) e1
    linarith [show 4 ^ (n + 1) * LRcost (kstar n) (D + 2) * ((h : ℝ) + 1) =
      4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * (h + 1)) by ring]
  linarith

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Core Lemma** (manuscript Theorem 8.2), proved. -/
theorem core_lemma_proved (n : ℕ) (hn : 5 ≤ n) (d D h r : ℕ) (hr : r ≤ n - 5) (X : Finset (ℝ^d))
    (hX : Ambient n D h X) (S W : Finset (ℝ^d)) (σ Γ' : ℝ) (hc : Config X S W r σ)
    (hσ : smin n D h ≤ σ) (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ')
    (B : Finset (ℝ^d)) (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (hF : RainbowFamily S W B I C β) (hBX : B ⊆ X) (hB : B.card = n - 4 - r) (hI : 12 ≤ I.card)
    (hM : ∀ k ∈ I, 2 ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * ((D + 2 : ℕ) : ℝ) ^ (2 * kc n r) * σ ≤
      (C k).card) : False := by
  obtain ⟨I', hI'sub, hI'c⟩ := exists_subset_card_eq hI
  have hF' := hF.restrict hI'sub
  have cc : CoreCtx n D h r X S W σ Γ' B I' C β := ⟨hn, hr, hX, hc, hσ, hΓ', hHR, hF', hBX, hB⟩
  obtain ⟨l, hl, m, hm, hlm⟩ := one_lt_card.1 (by omega : 1 < I'.card)
  -- constants
  set E : ℝ := ((D + 2 : ℕ) : ℝ) with hEdef
  have hE1 : 1 ≤ E := by rw [hEdef]; exact_mod_cast (by omega : 1 ≤ D + 2)
  set K : ℝ := E ^ kc n r with hKdef
  have hK1 : 1 ≤ K := one_le_pow₀ hE1
  set p := n - 4 - r with hp
  set w1 := (n - 2) + (n - 2).choose 2 + p with hw1
  set w2 := (n - 2).choose 2 + p with hw2
  have hkc : kc n r = (w1 + 1 + r) + (w1 + r + r.choose 2 + r) := by
    simp only [kc]; omega
  have hkst := kc_le_kstar n r hn (by omega)
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  set e := 2 * LRcost (kstar n) (D + 2) * h with hedef
  have he0 : 0 ≤ e := e_nonneg n D h
  have heσ : e < σ := lt_of_lt_of_le (e_lt_smin n D h) hσ
  set G := Γ' * K with hGdef
  have hG1 : 1 ≤ G := by rw [hGdef]; nlinarith
  have hGpos : 0 < G := by linarith
  set M0 := 2 ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * E ^ (2 * kc n r) * σ with hM0def
  have hn1 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hM0G : M0 = 2 ^ 20 * 4 ^ n * n ^ 2 * G ^ 2 * σ := by
    rw [hM0def, hGdef, hKdef, pow_mul, mul_pow]; ring
  have h4n : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hbase : 2 ^ 20 * (n ^ 2 * G * σ) ≤ M0 := by
    rw [hM0G]
    have e1 : G ≤ G ^ 2 := by nlinarith
    have e2 : G ≤ 4 ^ n * G ^ 2 := le_trans e1 (le_mul_of_one_le_left (by positivity) h4n)
    have e3 : (0 : ℝ) ≤ 2 ^ 20 * n ^ 2 * σ := by positivity
    have := mul_le_mul_of_nonneg_left e2 e3
    linarith [show 2 ^ 20 * n ^ 2 * σ * G = 2 ^ 20 * ((n : ℝ) ^ 2 * G * σ) by ring,
      show 2 ^ 20 * n ^ 2 * σ * (4 ^ n * G ^ 2) = 2 ^ 20 * 4 ^ n * (n : ℝ) ^ 2 * G ^ 2 * σ by ring]
  have hnG : (0 : ℝ) ≤ n ^ 2 * G * σ := by positivity
  have hn2 : (25 : ℝ) ≤ n ^ 2 := by nlinarith
  have hσM : σ ≤ M0 := by
    have h1 : (1 : ℝ) ≤ n ^ 2 * G := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hσ0
    linarith
  have hM0pos : 0 < M0 := by linarith
  have hMk : ∀ k ∈ I', M0 ≤ (C k).card := fun k hk => hM k (hI'sub hk)
  set ε : ℝ := 1 / (3072 * G) with hεdef
  set δ1 : ℝ := 1 / (512 * G) with hδ1def
  have hε : 0 < ε := by positivity
  have hεM : ε * M0 = M0 / (3072 * G) := by rw [hεdef]; field_simp
  have hP2 : 2 * n ^ 2 * σ ≤ ε * M0 := by
    rw [hεM, le_div_iff₀ (by positivity)]
    linarith [show 2 * (n : ℝ) ^ 2 * σ * (3072 * G) = 6144 * ((n : ℝ) ^ 2 * G * σ) by ring]
  have hμ := mu_le_sigma n D h σ hσ
  have hμ0 : 0 ≤ LRcost (kG n) (D + 2) * h :=
    mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  have hδ1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M0) + 3 * n ^ 2 * σ / M0 ≤ δ1 := by
    have h4 : (4 : ℝ) ^ n = 16 * 4 ^ (n - 2) := by
      rw [show n = (n - 2) + 2 by omega, pow_add]; norm_num; ring_nf
    have h4' : (0 : ℝ) ≤ 4 ^ (n - 2) := by positivity
    have t1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M0) ≤ 1 / (1024 * G) := by
      rw [hεM, div_div_eq_mul_div, div_le_div_iff₀ hM0pos (by positivity), hM0G, h4]
      generalize hμg : LRcost (kG n) (D + 2) * (h : ℝ) = μg at hμ hμ0 ⊢
      generalize hFg : (4 : ℝ) ^ (n - 2) = F4 at h4' ⊢
      have e1 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
      have e2 : F4 * μg * G ^ 2 ≤ F4 * σ * G ^ 2 := by
        have : 0 ≤ F4 * G ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hμ this
        linarith [show F4 * G ^ 2 * μg = F4 * μg * G ^ 2 by ring,
          show F4 * G ^ 2 * σ = F4 * σ * G ^ 2 by ring]
      have e3 : F4 * σ * G ^ 2 ≤ F4 * σ * G ^ 2 * n ^ 2 := by
        have : 0 ≤ F4 * σ * G ^ 2 := by positivity
        exact le_mul_of_one_le_right this e1
      have l : 2 * F4 * μg * (3072 * G) * (1024 * G) = 6291456 * (F4 * μg * G ^ 2) := by ring
      have r : 1 * (2 ^ 20 * (16 * F4) * n ^ 2 * G ^ 2 * σ) = 16777216 * (F4 * σ * G ^ 2 * n ^ 2) := by
        ring
      rw [l, r]
      have : 0 ≤ F4 * σ * G ^ 2 := by positivity
      linarith
    have t2 : 3 * n ^ 2 * σ / M0 ≤ 1 / (1024 * G) := by
      rw [div_le_div_iff₀ hM0pos (by positivity)]
      linarith [show 3 * (n : ℝ) ^ 2 * σ * (1024 * G) = 3072 * ((n : ℝ) ^ 2 * G * σ) by ring]
    have : 1 / (1024 * G) + 1 / (1024 * G) = δ1 := by rw [hδ1def]; field_simp; ring
    linarith
  -- index bookkeeping
  set I2 := (I'.erase l).erase m with hI2
  have hI2c : I2.card = 10 := by
    rw [hI2, card_erase_of_mem (mem_erase.2 ⟨fun e => hlm e.symm, hm⟩), card_erase_of_mem hl, hI'c]
  have hmemI2 : ∀ j ∈ I2, j ∈ I' ∧ j ≠ l ∧ j ≠ m := by
    intro j hj
    obtain ⟨hjm, hj'⟩ := mem_erase.1 hj
    obtain ⟨hjl, hjI⟩ := mem_erase.1 hj'
    exact ⟨hjI, hjl, hjm⟩
  have hClX : C l ⊆ X := (hF'.Cne l hl).2.trans hc.subW
  have hCmX : C m ⊆ X := (hF'.Cne m hm).2.trans hc.subW
  set A : ℝ := ((C l).card : ℝ) with hAdef
  set Bm : ℝ := ((C m).card : ℝ) with hBmdef
  have hA : M0 ≤ A := hMk l hl
  have hBm : M0 ≤ Bm := hMk m hm
  have hrn : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
  -- Steps 3–4 for each `j ∈ I2`, both widths
  have hkc3 : ∀ w, w ≤ w1 → w + 1 + r + (w + r + r.choose 2 + r) ≤ kc n r := by
    intro w hw; rw [hkc]; omega
  have hEmono : ∀ a, a ≤ kc n r → E ^ a ≤ K := fun a ha => pow_le_pow_right₀ hE1 ha
  have hCjbig : ∀ j ∈ I', 32 * K * Γ' * n * σ ≤ (C j).card := by
    intro j hj
    refine le_trans ?_ (hMk j hj)
    have : 32 * K * Γ' * n * σ ≤ 2 ^ 20 * (n ^ 2 * G * σ) := by
      rw [hGdef]
      have e1 : (n : ℝ) ≤ n ^ 2 := by nlinarith
      have : 0 ≤ K * Γ' * σ := by positivity
      nlinarith
    linarith
  have hcor : ∀ j ∈ I2, ∀ w : ℕ, w ≤ w1 → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / (512 * Γ' * K) →
      ∀ (Pr : ℝ^d → ℝ^d → Prop),
      (∀ a1 ∈ C l, ∀ a2 ∈ C m, Pr a1 a2 → CoverShape S C w δ j a1 a2) →
      ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) => Pr q.1 q.2).card : ℕ) : ℝ) ≤ e * A + (w + 1) * e * Bm := by
    intro j hj w hw δ hδ0 hδ Pr hPr
    obtain ⟨hjI, hjl, hjm⟩ := hmemI2 j hj
    obtain ⟨p1, p2, p3⟩ := params34 E Γ' σ δ (C j).card K (w + 1 + r) (w + r + r.choose 2 + r) r n
      hE1 hΓ' hσ0 (hEmono _ (hkc3 w hw)) hδ0 hδ (by omega) (hCjbig j hjI)
    exact core_cor34 cc hl hm hjI hjl hjm w δ _ p1 p2 (by have := hkc3 w hw; omega)
      (by have := hkc3 w hw; omega) p3
      (by linarith [hMk j hjI]) Pr hPr
  -- the Good and Cov counts
  have hGoodj : ∀ j ∈ I2, ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CoverShape S C w1 δ1 j q.1 q.2).card : ℕ) : ℝ) ≤ e * A + (w1 + 1) * e * Bm := by
    intro j hj
    refine hcor j hj w1 le_rfl δ1 (by positivity) (by rw [hδ1def, hGdef, mul_assoc]) _ ?_
    intro a1 _ a2 _ h; exact h
  have hCovj : ∀ j ∈ I2, ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CovK S B C β ε j q.1 q.2).card : ℕ) : ℝ) ≤ e * A + (w2 + 1) * e * Bm := by
    intro j hj
    refine hcor j hj w2 (by omega) (6 * ε) (by positivity)
      (by rw [hεdef, hGdef]; field_simp; norm_num) _ ?_
    intro a1 ha1 a2 ha2 h
    exact cov_shape cc hl hm hlm ha1 ha2 ε h
  -- `V` and `Π`
  set V := (C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
    (∀ s ∈ S, ∀ s' ∈ S, dist q.1 s ≠ dist q.2 s') ∧ dist q.1 q.2 ∉ Ty S B β l m q.1 q.2 with hVdef
  set Pi := (C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) => ∃ s ∈ S, ∃ s' ∈ S, dist q.1 s = dist q.2 s' with hPidef
  have hV6 : 6 * V.card ≤ ∑ j ∈ I2, ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CoverShape S C w1 δ1 j q.1 q.2).card) + (((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CovK S B C β ε j q.1 q.2).card)) := by
    have h1 : ∀ q ∈ V, 6 ≤ (I2.filter fun j => CoverShape S C w1 δ1 j q.1 q.2).card +
        (I2.filter fun j => CovK S B C β ε j q.1 q.2).card := by
      intro q hq
      obtain ⟨hqp, hPi, hTy⟩ := mem_filter.1 hq
      obtain ⟨ha1, ha2⟩ := mem_product.1 hqp
      exact pair_count cc hI'c M0 ε δ1 hM0pos hMk hε hP2 hδ1 hl hm hlm ha1 ha2 hPi hTy
    calc 6 * V.card = ∑ _q ∈ V, 6 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ q ∈ V, ((I2.filter fun j => CoverShape S C w1 δ1 j q.1 q.2).card +
          (I2.filter fun j => CovK S B C β ε j q.1 q.2).card) := sum_le_sum h1
      _ = ∑ j ∈ I2, ((V.filter fun q => CoverShape S C w1 δ1 j q.1 q.2).card +
          (V.filter fun q => CovK S B C β ε j q.1 q.2).card) := by
          simp only [card_filter, sum_add_distrib]
          rw [sum_comm, sum_comm (s := V) (t := I2)]
      _ ≤ _ := by
          refine sum_le_sum fun j _ => add_le_add ?_ ?_
          · exact card_le_card (filter_subset_filter _ (filter_subset _ _))
          · exact card_le_card (filter_subset_filter _ (filter_subset _ _))
  have hVbound : 6 * (V.card : ℝ) ≤ 10 * (2 * e * A + (w1 + w2 + 2) * e * Bm) := by
    have h1 : (6 * V.card : ℝ) ≤ ∑ j ∈ I2, (((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CoverShape S C w1 δ1 j q.1 q.2).card : ℕ) : ℝ) + ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CovK S B C β ε j q.1 q.2).card : ℕ) : ℝ)) := by exact_mod_cast hV6
    have h2 : ∑ j ∈ I2, (((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CoverShape S C w1 δ1 j q.1 q.2).card : ℕ) : ℝ) + ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CovK S B C β ε j q.1 q.2).card : ℕ) : ℝ)) ≤
        ∑ _j ∈ I2, ((e * A + (w1 + 1) * e * Bm) + (e * A + (w2 + 1) * e * Bm)) :=
      sum_le_sum fun j hj => add_le_add (hGoodj j hj) (hCovj j hj)
    rw [sum_const, hI2c, nsmul_eq_mul] at h2
    push_cast at h2
    nlinarith
  have hPibound : (Pi.card : ℝ) ≤ r * (r * σ) * Bm := by
    have hcount : Pi.card = ∑ a2 ∈ C m,
        ((C l).filter fun a1 => ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s').card := by
      rw [hPidef, card_filter, sum_product_right]
      exact sum_congr rfl fun a2 _ => (card_filter _ _).symm
    have hper : ∀ a2 ∈ C m, ((((C l).filter fun a1 =>
        ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s').card : ℕ) : ℝ) ≤ r * (r * σ) := by
      intro a2 ha2
      have hpos : ∀ t ∈ S.image (dist a2), 0 < t := by
        intro t ht
        obtain ⟨s, hs, rfl⟩ := mem_image.1 ht
        exact dist_pos.2 fun e => (hF'.F4 m hm a2 ha2).1 (mem_union_left _ (e ▸ hs))
      have hsub : ((C l).filter fun a1 => ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s') ⊆
          S.biUnion fun s => W.filter fun x => dist x s ∈ S.image (dist a2) := by
        intro a1 ha1
        obtain ⟨ha1C, s, hs, s', hs', he⟩ := mem_filter.1 ha1
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF'.Cne l hl).2 ha1C,
          mem_image.2 ⟨s', hs', he.symm⟩⟩⟩
      have h1 := removal_bound hc (S.image (dist a2)) hpos
      have h2 : ((S.image (dist a2)).card : ℝ) ≤ r := by
        rw [← hc.card]; exact_mod_cast card_image_le
      have h3 : (r : ℝ) * ((S.image (dist a2)).card * σ) ≤ r * (r * σ) := by gcongr
      exact (by exact_mod_cast card_le_card hsub : (_ : ℝ) ≤ _).trans (h1.trans h3)
    rw [hcount]; push_cast
    calc ∑ a2 ∈ C m, ((((C l).filter fun a1 => ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s').card : ℕ) : ℝ)
        ≤ ∑ _a2 ∈ C m, (r * (r * σ)) := sum_le_sum hper
      _ = r * (r * σ) * Bm := by rw [sum_const, nsmul_eq_mul, hBmdef]; ring
  -- the final rectangle argument
  set Val : ℝ^d → Finset ℝ := fun a2 =>
    (dists (S ∪ B) ∪ B.image (β l) ∪ B.image (β m) ∪ S.image (dist a2)).image (· ^ 2) with hValdef
  have hValc : ∀ a2 ∈ C m, (Val a2).card ≤ w1 := by
    intro a2 _
    refine card_image_le.trans ?_
    have e1 := card_union_le (dists (S ∪ B) ∪ B.image (β l) ∪ B.image (β m)) (S.image (dist a2))
    have e2 := card_union_le (dists (S ∪ B) ∪ B.image (β l)) (B.image (β m))
    have e3 := card_union_le (dists (S ∪ B)) (B.image (β l))
    have e4 := card_dists_le (S ∪ B)
    rw [card_union_of_disjoint hF'.F1.1, hc.card, hB] at e4
    have e5 : (r + p).choose 2 ≤ (n - 2).choose 2 := Nat.choose_le_choose 2 (by omega)
    have e6 := card_image_le (s := B) (f := β l)
    have e7 := card_image_le (s := B) (f := β m)
    have e8 := card_image_le (s := S) (f := dist a2)
    rw [hB] at e6 e7
    rw [hc.card] at e8
    omega
  have hbad : ((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) => ‖q.1 - q.2‖ ^ (2 : ℕ) ∉ Val q.2 ∧
      ∀ s ∈ S, (‖q.1 - q.2‖ ^ (2 : ℕ) : ℝ) ≠ ‖q.1 - s‖ ^ (2 : ℕ)) ⊆ V ∪ Pi := by
    intro q hq
    obtain ⟨hqp, hv, hps⟩ := mem_filter.1 hq
    have hTy : dist q.1 q.2 ∉ Ty S B β l m q.1 q.2 := by
      intro hT
      simp only [Ty, mem_union] at hT
      rcases hT with (((h1 | h1) | h1) | h1) | h1
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inl (Or.inl (Or.inl h1)),
          by rw [dist_eq_norm]⟩)
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inl (Or.inl (Or.inr h1)),
          by rw [dist_eq_norm]⟩)
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inl (Or.inr h1),
          by rw [dist_eq_norm]⟩)
      · obtain ⟨s, hs, hse⟩ := mem_image.1 h1
        exact hps s hs (by rw [← dist_eq_norm, ← dist_eq_norm, hse])
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inr h1,
          by rw [dist_eq_norm]⟩)
    by_cases hPi : ∃ s ∈ S, ∃ s' ∈ S, dist q.1 s = dist q.2 s'
    · exact mem_union_right _ (mem_filter.2 ⟨hqp, hPi⟩)
    · push Not at hPi
      exact mem_union_left _ (mem_filter.2 ⟨hqp, hPi, hTy⟩)
  have hw12 : (w1 + w2 + 2 : ℝ) ≤ 3 * n ^ 2 := by
    have h1 := choose_two_le_sq' (n - 2)
    have h3 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have : w1 + w2 + 2 ≤ 3 * (n * n) := by
      rw [hw1, hw2, hp]
      generalize (n - 2).choose 2 = C1 at *
      generalize (n - 2) * (n - 2) = P at *
      have : 5 * 5 ≤ n * n := Nat.mul_le_mul hn hn
      have : 5 * n ≤ n * n := Nat.mul_le_mul_right n hn
      generalize n * n = Z at *
      omega
    have : ((w1 + w2 + 2 : ℕ) : ℝ) ≤ ((3 * (n * n) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  have hEW : E ^ (w1 + S.card) ≤ K := by rw [hc.card]; exact hEmono _ (by rw [hkc]; omega)
  have hfin := gl_lr_or_avg_sets n D h X hX.dim hX.half (C l) (C m) hClX hCmX w1 Val hValc S
    (by rw [hc.card]; rw [hkc] at hkst; omega) ?_ (by rw [← hAdef]; linarith)
  · rw [← hBmdef] at hfin
    linarith
  · rw [← hAdef, ← hBmdef]
    set bad : ℝ := (V.card : ℝ) + Pi.card with hbaddef
    have hA0 : 0 ≤ A := by linarith
    have hB0 : 0 ≤ Bm := by linarith
    have hr2 : (r : ℝ) * (r * σ) ≤ n ^ 2 * σ := by
      have : (r : ℝ) * r ≤ n * n := mul_le_mul hrn hrn (Nat.cast_nonneg _) (by linarith)
      nlinarith
    have hbadb : 6 * bad ≤ 56 * n ^ 2 * σ * (A + Bm) := by
      have e1 : e * A ≤ σ * A := mul_le_mul_of_nonneg_right heσ.le hA0
      have e2 : (w1 + w2 + 2 : ℝ) * e * Bm ≤ 3 * n ^ 2 * σ * Bm := by
        have : (w1 + w2 + 2 : ℝ) * e ≤ 3 * n ^ 2 * σ := by
          have : (0 : ℝ) ≤ w1 + w2 + 2 := by positivity
          calc (w1 + w2 + 2 : ℝ) * e ≤ (w1 + w2 + 2) * σ := by gcongr
            _ ≤ 3 * n ^ 2 * σ := by gcongr
        exact mul_le_mul_of_nonneg_right this hB0
      have e3 : r * (r * σ) * Bm ≤ n ^ 2 * σ * Bm := mul_le_mul_of_nonneg_right hr2 hB0
      have e4 : σ * A ≤ n ^ 2 * σ * A := by
        have : 0 ≤ σ * A := by positivity
        have h1 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right h1 this
        linarith [show (n : ℝ) ^ 2 * (σ * A) = n ^ 2 * σ * A by ring]
      have f1 : 0 ≤ (n : ℝ) ^ 2 * σ * A := by positivity
      have f2 : 0 ≤ (n : ℝ) ^ 2 * σ * Bm := by positivity
      rw [hbaddef]
      linarith [hVbound, hPibound]
    have hKbig : 16 * K * (56 * n ^ 2 * σ) ≤ 3 * M0 := by
      have : 16 * K * (56 * n ^ 2 * σ) ≤ 2 ^ 20 * (n ^ 2 * G * σ) := by
        rw [hGdef]
        have h0 : 0 ≤ K * n ^ 2 * σ := by positivity
        have := mul_le_mul_of_nonneg_left hΓ' h0
        linarith [show 16 * K * (56 * (n : ℝ) ^ 2 * σ) = 896 * (K * n ^ 2 * σ) by ring,
          show 2 ^ 20 * ((n : ℝ) ^ 2 * (Γ' * K) * σ) = 2 ^ 20 * (K * n ^ 2 * σ * Γ') by ring]
      linarith
    have hEW0 : 0 ≤ E ^ (w1 + S.card) := by positivity
    have hbad0 : 0 ≤ bad := by rw [hbaddef]; positivity
    refine le_trans (mul_le_mul_of_nonneg_left (c := bad) (by
      rw [hbaddef]; exact_mod_cast (card_le_card hbad).trans (card_union_le V Pi)) (by positivity)) ?_
    calc 16 * E ^ (w1 + S.card) * bad ≤ 16 * K * bad := by gcongr
      _ ≤ 16 * K * (56 * n ^ 2 * σ * (A + Bm) / 6) := by gcongr; linarith
      _ = 16 * K * (56 * n ^ 2 * σ) * (A + Bm) / 6 := by ring
      _ ≤ 3 * M0 * (A + Bm) / 6 := by gcongr
      _ = M0 * (A + Bm) / 2 := by ring
      _ ≤ A * Bm := by nlinarith [mul_nonneg hA0 (sub_nonneg.2 hBm), mul_nonneg hB0 (sub_nonneg.2 hA)]

end E1088
