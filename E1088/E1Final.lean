import E1088.CoreFinal

/-!
# E1_r from the Core and Slicing Lemmas: numerics, iteration, conclusion
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-! ### Numerics -/

theorem choose_two_le_sq (m : ℕ) : m.choose 2 ≤ m * m := by
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem ksl_le_kstar (n r p : ℕ) (hn : 5 ≤ n) (hr : r ≤ n - 5) (hp : p ≤ n - 4 - r) :
    ksl r p (Kp n r (p + 1)) ≤ kstar n := by
  unfold ksl Kp kstar
  have h1 : 3 * (12 * 6 ^ (n - 4 - r - (p + 1))) ≤ 6 ^ n := by
    have : 3 * (12 * 6 ^ (n - 4 - r - (p + 1))) = 6 ^ (n - 4 - r - (p + 1) + 2) := by
      rw [pow_add]; ring
    rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := choose_two_le_sq (r + p)
  have h3 : r + p ≤ n := by omega
  have h4 : (r + p) * (r + p) ≤ n * n := Nat.mul_le_mul h3 h3
  have h5 : 2 * p + 2 * r ≤ n * n := by nlinarith
  have h6 : n ^ 2 = n * n := sq n
  rw [h6]
  generalize 3 * (12 * 6 ^ (n - 4 - r - (p + 1))) = X at *
  generalize (r + p).choose 2 = C at *
  generalize n * n = Z at *
  generalize 6 ^ n = Y at *
  omega

theorem natCast_le_pow (A : ℝ) (hA : 2 ≤ A) (N : ℕ) : (N : ℝ) ≤ A ^ N := by
  have h1 : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
  exact h1.le.trans (pow_le_pow_left₀ (by norm_num) hA N)

theorem kc_le (n r : ℕ) (hr : r ≤ n) : kc n r ≤ 3 * n ^ 2 + 7 * n + 1 := by
  show (n - 2) + (n - 2).choose 2 + (n - 4 - r) + 1 + r +
    ((n - 2) + (n - 2).choose 2 + (n - 4 - r) + 2 * r + r.choose 2) ≤ 3 * n ^ 2 + 7 * n + 1
  have h1 := choose_two_le_sq (n - 2)
  have h2 := choose_two_le_sq r
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

/-- The uniform exponent of `ratio_r`. -/
def cE1 (n : ℕ) : ℕ :=
  (22 + 2 * n + n ^ 2 + 2 * (3 * n ^ 2 + 7 * n + 1)) +
    n * (2 * n * (n + 12 * 6 ^ n) + 6 + kstar n) + 2 * n * (n + 12 * 6 ^ n) + 3

theorem ratioE1_le (n D r : ℕ) (hn : 5 ≤ n) (hr : r ≤ n - 5) (Γ' : ℝ) (hΓ : 1 ≤ Γ') :
    ratioE1 n D r Γ' ≤ ((D + 2 : ℕ) : ℝ) ^ cE1 n * Γ' ^ cE1 n := by
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha2 : 2 ≤ a := by rw [ha]; push_cast; have := Nat.cast_nonneg (α := ℝ) D; linarith
  set A := a * Γ' with hA
  have hA2 : 2 ≤ A := by rw [hA]; nlinarith
  have hA1 : 1 ≤ A := by linarith
  have haA : a ≤ A := by rw [hA]; nlinarith
  have hΓA : Γ' ≤ A := by rw [hA]; nlinarith
  have mono : ∀ {p q : ℕ}, p ≤ q → A ^ p ≤ A ^ q := fun h => pow_le_pow_right₀ hA1 h
  set e0 := 22 + 2 * n + n ^ 2 + 2 * (3 * n ^ 2 + 7 * n + 1) with he0
  set N1 := 2 * n * (n + 12 * 6 ^ n) + 6 + kstar n with hN1
  have hK : ∀ p, Kp n r p ≤ 12 * 6 ^ n := fun p =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hth : ∀ p, p ≤ n - 4 - r → thInv n D r p Γ' ≤ A ^ (5 + kstar n) := by
    intro p hp
    unfold thInv
    have h16 : (16 : ℝ) ≤ A ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ A ^ 4 := pow_le_pow_left₀ (by norm_num) hA2 4
    have hak : a ^ ksl r p (Kp n r (p + 1)) ≤ A ^ kstar n :=
      (pow_le_pow_left₀ (by linarith) haA _).trans (mono (ksl_le_kstar n r p hn hr hp))
    calc 16 * Γ' * a ^ ksl r p (Kp n r (p + 1)) ≤ A ^ 4 * A * A ^ kstar n := by
          gcongr
      _ = A ^ (5 + kstar n) := by ring
  have hMsl : ∀ p, p ≤ n - 4 - r → MslHat n D r p Γ' ≤ A ^ N1 := by
    intro p hp
    unfold MslHat
    have h1 : (2 * n * (n + Kp n r (p + 1)) : ℝ) ≤ A ^ (2 * n * (n + 12 * 6 ^ n)) := by
      have := natCast_le_pow A hA2 (2 * n * (n + Kp n r (p + 1)))
      push_cast at this
      exact this.trans (mono (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hK _) _)))
    calc (2 * n * (n + Kp n r (p + 1)) : ℝ) * thInv n D r p Γ'
        ≤ A ^ (2 * n * (n + 12 * 6 ^ n)) * A ^ (5 + kstar n) :=
          mul_le_mul h1 (hth p hp) (by unfold thInv; positivity) (by positivity)
      _ ≤ A ^ N1 := by rw [← pow_add]; exact mono (by omega)
  have hcore : McoreHat n D r Γ' ≤ A ^ e0 := by
    unfold McoreHat
    have h20 : (2 : ℝ) ^ 20 ≤ A ^ 20 := pow_le_pow_left₀ (by norm_num) hA2 20
    have h4 : (4 : ℝ) ^ n ≤ A ^ (2 * n) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by nlinarith) n
    have hn2 : ((n : ℝ)) ^ 2 ≤ A ^ (n ^ 2) := by
      have := natCast_le_pow A hA2 (n ^ 2); push_cast at this; exact this
    have hG : Γ' ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by linarith) hΓA 2
    have hkc : a ^ (2 * kc n r) ≤ A ^ (2 * (3 * n ^ 2 + 7 * n + 1)) :=
      (pow_le_pow_left₀ (by linarith) haA _).trans
        (mono (Nat.mul_le_mul_left _ (kc_le n r (by omega))))
    calc (2 : ℝ) ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * a ^ (2 * kc n r)
        ≤ A ^ 20 * A ^ (2 * n) * A ^ (n ^ 2) * A ^ 2 * A ^ (2 * (3 * n ^ 2 + 7 * n + 1)) := by
          gcongr
      _ = A ^ e0 := by rw [he0]; simp only [← pow_add]; ring_nf
  have haux : ∀ j, j ≤ n - 4 - r → mAux n D r Γ' j ≤ A ^ (e0 + j * N1) := by
    intro j
    induction j with
    | zero => intro _; simpa [mAux] using hcore
    | succ j ih =>
      intro hj
      simp only [mAux]
      have hN1' : 6 + kstar n ≤ N1 := by
        rw [hN1]; generalize 2 * n * (n + 12 * 6 ^ n) = Q; omega
      have hjN : e0 + (j + 1) * N1 = e0 + j * N1 + N1 := by ring
      apply max_le
      · exact (hMsl _ (by omega)).trans (mono (by rw [hjN]; omega))
      · have h1 := ih (by omega)
        have h2 := hth (n - 4 - r - (j + 1)) (by omega)
        have h0 : 0 ≤ thInv n D r (n - 4 - r - (j + 1)) Γ' := by unfold thInv; positivity
        calc 2 * thInv n D r (n - 4 - r - (j + 1)) Γ' * mAux n D r Γ' j
            ≤ A * A ^ (5 + kstar n) * A ^ (e0 + j * N1) :=
              mul_le_mul (mul_le_mul (by linarith) h2 h0 (by linarith)) h1
                (mAux_nonneg n D r Γ' hΓ j) (by positivity)
          _ = A ^ (e0 + j * N1 + 6 + kstar n) := by ring
          _ ≤ A ^ (e0 + (j + 1) * N1) := mono (by rw [hjN]; omega)
  have hm1 : mHat n D r Γ' 1 ≤ A ^ (e0 + n * N1) :=
    (haux _ (by omega)).trans (mono (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _))
  have hrest : (2 * n * (n + Kr n r) : ℝ) ≤ A ^ (2 * n * (n + 12 * 6 ^ n)) := by
    have := natCast_le_pow A hA2 (2 * n * (n + Kr n r))
    push_cast at this
    refine this.trans (mono (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _)))
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfin : ratioE1 n D r Γ' ≤ A ^ cE1 n := by
    unfold ratioE1
    set P := e0 + n * N1 + 2 * n * (n + 12 * 6 ^ n) with hP
    have e1 : A ^ (e0 + n * N1) ≤ A ^ P := mono (by omega)
    have e2 : A ^ (2 * n * (n + 12 * 6 ^ n)) ≤ A ^ P := mono (by omega)
    have e3 : A ^ cE1 n = A ^ P * A ^ 3 := by rw [← pow_add]; rfl
    have e5 : 8 ≤ A ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA2 3; norm_num at this; linarith
    have hP0 : 0 ≤ A ^ P := by positivity
    rw [e3]
    nlinarith
  calc ratioE1 n D r Γ' ≤ A ^ cE1 n := hfin
    _ = a ^ cE1 n * Γ' ^ cE1 n := by rw [hA, mul_pow]

/-! ### The slicing iteration and the contradiction -/

theorem iterate_families (n : ℕ) (hn : 5 ≤ n) (d D h r : ℕ) (hr : r ≤ n - 5) (X : Finset (ℝ^d))
    (hX : Ambient n D h X) (S W : Finset (ℝ^d)) (σ Γ' : ℝ) (hc : Config X S W r σ)
    (hσ : smin n D h ≤ σ) (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ') (b : ℝ^d) (hb : b ∈ W)
    (hbig : Kr n r ≤ (Big S W b (ratioE1 n D r Γ' * σ)).card) :
    ∀ p, 1 ≤ p → p ≤ n - 4 - r → ∃ (B : Finset (ℝ^d)) (I : Finset ℕ) (C : ℕ → Finset (ℝ^d))
      (β : ℕ → ℝ^d → ℝ), RainbowFamily S W B I C β ∧ B ⊆ X ∧ B.card = p ∧ I.card = Kp n r p ∧
        ∀ k ∈ I, mHat n D r Γ' p * σ ≤ (C k).card := by
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσpos : 0 < σ := by linarith
  have hm0 : ∀ p, 0 ≤ mHat n D r Γ' p := fun p => mAux_nonneg n D r Γ' hΓ' _
  intro p hp1 hpq
  induction p, hp1 using Nat.le_induction with
  | base =>
    have hK1 : Kr n r = Kp n r 1 := by unfold Kr Kp; congr 2; omega
    set τ := ratioE1 n D r Γ' * σ with hτ
    have hrn : (r : ℝ) * (r + Kr n r) ≤ n * (n + Kr n r) := by
      have : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      nlinarith
    have hn0 : (0 : ℝ) < n * (n + Kr n r) := by
      have : (5 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    have hm1 := hm0 1
    have hτbig : (r : ℝ) * (r + Kr n r) * σ < τ := by
      rw [hτ]; unfold ratioE1; nlinarith
    obtain ⟨C, β, hF, hC⟩ := initial_family X S W r σ τ hc hσpos b hb (Kr n r) hbig hτbig
    refine ⟨{b}, range (Kr n r), C, β, hF, singleton_subset_iff.2 (hc.subW hb), card_singleton b,
      by rw [card_range, hK1], ?_⟩
    intro k hk
    have := hC k hk
    have h2 : mHat n D r Γ' 1 * σ ≤ τ - r * (r + Kr n r) * σ := by
      rw [hτ]; unfold ratioE1; nlinarith
    linarith
  | succ p hp1 ih =>
    obtain ⟨B, I, C, β, hF, hBX, hB, hI, hM⟩ := ih (by omega)
    have hpq' : p < n - 4 - r := by omega
    have hstep := mHat_step n D r p Γ' hpq'
    set K := Kp n r (p + 1) with hKdef
    have hthpos : 0 < thInv n D r p Γ' := by unfold thInv; positivity
    have hMsl : 2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) ≤
        mHat n D r Γ' p * σ := by
      rw [hB]
      have : MslHat n D r p Γ' ≤ mHat n D r Γ' p := by rw [hstep]; exact le_max_left _ _
      unfold MslHat thInv at this
      nlinarith
    have hI6 : 6 * K ≤ I.card := by
      rw [hI, hKdef]; unfold Kp
      have : 6 * (12 * 6 ^ (n - 4 - r - (p + 1))) = 12 * 6 ^ (n - 4 - r - p) := by
        rw [show n - 4 - r - p = (n - 4 - r - (p + 1)) + 1 by omega, pow_succ]; ring
      omega
    obtain ⟨c, hcI, I', hI'I, hI'c, C', β', hC'C, hF', hC'⟩ :=
      slicing_lemma_proved n (by omega) d D h r K (by omega) (by rw [hKdef]; unfold Kp; exact Nat.one_le_iff_ne_zero.2 (by positivity))
        X hX S W σ Γ' hc hσ hΓ' hHR B I C β hF (by omega) (by omega) hI6
        (by rw [hB]; exact ksl_le_kstar n r p hn hr (by omega)) (mHat n D r Γ' p * σ) hM hMsl
    refine ⟨insert c B, I', C', β', hF', ?_, ?_, hI'c, ?_⟩
    · obtain ⟨k, hk, hck⟩ := mem_biUnion.1 hcI
      exact insert_subset (hc.subW ((hF.Cne k hk).2 hck)) hBX
    · obtain ⟨k, hk, hck⟩ := mem_biUnion.1 hcI
      have hcB : c ∉ B := fun h => (hF.F4 k hk c hck).1 (mem_union_right _ h)
      rw [card_insert_of_notMem hcB, hB]
    · intro k hk
      have h1 := hC' k hk
      rw [hB] at h1
      have h2 : 2 * thInv n D r p Γ' * mHat n D r Γ' (p + 1) ≤ mHat n D r Γ' p := by
        rw [hstep]; exact le_max_right _ _
      have h3 : mHat n D r Γ' (p + 1) * σ ≤
          mHat n D r Γ' p * σ / (2 * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r p K)) := by
        rw [le_div_iff₀ (by positivity)]
        unfold thInv at h2
        nlinarith
      linarith

/-- **E1_r proved from the Core Lemma and the Slicing Lemma.** -/
theorem theorem_E1_proved (n : ℕ) (hn : 5 ≤ n) :
    ∃ c : ℕ, ∀ (d D h r : ℕ), r ≤ n - 5 → ∀ (Γ' : ℝ), 1 ≤ Γ' →
      ∃ ratio : ℝ, 1 ≤ ratio ∧ ratio ≤ ((D + 2 : ℕ) : ℝ) ^ c * Γ' ^ c ∧
        ∀ (X : Finset (ℝ^d)), Ambient n D h X → ∀ (S W : Finset (ℝ^d)) (σ : ℝ),
          Config X S W r σ → smin n D h ≤ σ → HRholds S W σ Γ' →
          ∀ b ∈ W, (Big S W b (ratio * σ)).card < Kr n r := by
  refine ⟨cE1 n, fun d D h r hr Γ' hΓ' =>
    ⟨ratioE1 n D r Γ', ?_, ratioE1_le n D r hn hr Γ' hΓ', ?_⟩⟩
  · unfold ratioE1
    have := mAux_nonneg n D r Γ' hΓ' (n - 4 - r - 1)
    have h1 : (1 : ℝ) ≤ 2 * n * (n + Kr n r) := by
      have : (5 : ℝ) ≤ n := by exact_mod_cast hn
      have : (0 : ℝ) ≤ Kr n r := Nat.cast_nonneg _
      nlinarith
    unfold mHat
    linarith
  · intro X hX S W σ hc hσ hHR b hb
    by_contra hcon
    push Not at hcon
    obtain ⟨B, I, C, β, hF, hBX, hB, hI, hM⟩ :=
      iterate_families n hn d D h r hr X hX S W σ Γ' hc hσ hΓ' hHR b hb hcon (n - 4 - r)
        (by omega) le_rfl
    refine core_lemma_proved n hn d D h r hr X hX S W σ Γ' hc hσ hΓ' hHR B I C β hF hBX hB ?_ ?_
    · rw [hI]; unfold Kp; simp
    · intro k hk
      have := hM k hk
      rw [mHat_top] at this
      unfold McoreHat at this
      exact this

end E1088
