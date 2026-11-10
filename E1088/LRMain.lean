import E1088.LR

/-!
# Theorem LR: the round and the induction
-/

set_option linter.unusedSectionVars false

open Finset

namespace E1088

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

theorem CutData.mono_K {τ : ι → TF α β} {S : Finset ι} {K K' : ℝ} {X : Finset α}
    {Y : Finset β} (hK : K ≤ K') (h : CutData τ S K X Y) : CutData τ S K' X Y := by
  obtain ⟨Lo, Hi, h1, h2, h3, h4, φ, θ, qr, qc, hqr, hqc, hb⟩ := h
  refine ⟨Lo, Hi, h1, h2, h3, h4, φ, θ, qr, qc, hqr, hqc, fun x hx w hw => ?_⟩
  have hσ := mul_pos (hqr x hx) (hqc w hw)
  obtain ⟨hL, hH⟩ := hb x hx w hw
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨a, b⟩ := hL t ht; exact ⟨by nlinarith, b⟩
  · obtain ⟨a, b⟩ := hH t ht; exact ⟨a, by nlinarith⟩

/-- Margin constant used with `k` types. -/
noncomputable def margK (k : ℕ) : ℝ := 32 * k * 16 ^ k

/-- Cost of one round with at most `k` types and rank `≤ r`. -/
noncomputable def roundCost (k r : ℕ) : ℝ :=
  16 ^ (k * k) * 4 ^ k *
    (64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2))

theorem one_le_roundCost (k r : ℕ) : 1 ≤ roundCost k r := by
  unfold roundCost
  have h1 : (1 : ℝ) ≤ 16 ^ (k * k) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ ((r + 1) ^ k : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have h4 : (1 : ℝ) ≤ 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) :=
    one_le_pow₀ (by norm_num)
  have h5 : (1 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k)
      (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) := by nlinarith
  nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]

/-- **One round of Theorem LR.** With `2 ≤ #S ≤ k` types covering a rank-`≤ r` matrix, a
refinement of cost `roundCost k r` is covered by strictly fewer types. -/
theorem lr_round (M : α → β → ℝ) (τ : ι → TF α β) (S : Finset ι) (X : Finset α) (Y : Finset β)
    (k r : ℕ) (hX : X.Nonempty) (hY : Y.Nonempty) (hr : rankOn M X Y ≤ r)
    (hcov : Covers M τ S X Y) (hS : 2 ≤ #S) (hSk : #S ≤ k) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, (#X : ℝ) ≤ roundCost k r * #X' ∧ (#Y : ℝ) ≤ roundCost k r * #Y' ∧
      ∃ S' ⊆ S, #S' < #S ∧ Covers M τ S' X' Y' := by
  classical
  obtain ⟨X1, hX1, Y1, hY1, c1, c2, S1, hS1, hcov1, hgood⟩ :=
    process_pairs M τ (S ×ˢ S) S X Y hX hY hcov
  rw [card_product] at c1 c2
  have hX1ne := nonempty_of_card_le hX c1
  have hY1ne := nonempty_of_card_le hY c2
  have hkk : (16 : ℝ) ^ (#S * #S) ≤ 16 ^ (k * k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul hSk hSk)
  have c1r : (#X : ℝ) ≤ 16 ^ (k * k) * #X1 := by
    have : (#X : ℝ) ≤ 16 ^ (#S * #S) * #X1 := by exact_mod_cast c1
    nlinarith [(Nat.cast_nonneg #X1 : (0 : ℝ) ≤ #X1)]
  have c2r : (#Y : ℝ) ≤ 16 ^ (k * k) * #Y1 := by
    have : (#Y : ℝ) ≤ 16 ^ (#S * #S) * #Y1 := by exact_mod_cast c2
    nlinarith [(Nat.cast_nonneg #Y1 : (0 : ℝ) ≤ #Y1)]
  have hRC := one_le_roundCost k r
  by_cases hS1c : #S1 ≤ 1
  · refine ⟨X1, hX1, Y1, hY1, ?_, ?_, S1, hS1, by omega, hcov1⟩
    · have : (16 : ℝ) ^ (k * k) ≤ roundCost k r := by
        unfold roundCost
        have h2 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ ((r + 1) ^ k : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
        have h4 : (1 : ℝ) ≤ 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) :=
          one_le_pow₀ (by norm_num)
        have h0 : (0 : ℝ) ≤ 16 ^ (k * k) := by positivity
        have h5 : (1 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k)
          (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2 h0]
      nlinarith [(Nat.cast_nonneg #X1 : (0 : ℝ) ≤ #X1)]
    · have : (16 : ℝ) ^ (k * k) ≤ roundCost k r := by
        unfold roundCost
        have h2 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ ((r + 1) ^ k : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
        have h4 : (1 : ℝ) ≤ 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) :=
          one_le_pow₀ (by norm_num)
        have h0 : (0 : ℝ) ≤ 16 ^ (k * k) := by positivity
        have h5 : (1 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k)
          (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2 h0]
      nlinarith [(Nat.cast_nonneg #Y1 : (0 : ℝ) ≤ #Y1)]
  push Not at hS1c
  have hS1k : #S1 ≤ k := (card_le_card hS1).trans hSk
  obtain ⟨X2, hX2, Y2, hY2, d1, d2, hcut⟩ := cut_of_good τ S1 X1 Y1 hX1ne hY1ne hS1c
    (fun t ht t' ht' hne => hgood (t, t') (mem_product.2 ⟨hS1 ht, hS1 ht'⟩) ht ht' hne)
  have hKle : (32 * #S1 * 16 ^ #S1 : ℝ) ≤ margK k := by
    unfold margK
    have a1 : (#S1 : ℝ) ≤ k := by exact_mod_cast hS1k
    have a2 : (16 : ℝ) ^ #S1 ≤ 16 ^ k := pow_le_pow_right₀ (by norm_num) hS1k
    have := mul_le_mul a1 a2 (by positivity) (by positivity)
    nlinarith
  obtain ⟨Lo, Hi, hLH, hdisj, hLo, hHi, φ, θ, qr, qc, hqr, hqc, hb⟩ := hcut.mono_K hKle
  have hX2ne := nonempty_of_card_le hX1ne d1
  have hY2ne := nonempty_of_card_le hY1ne d2
  set N : α → β → ℝ := fun x w => (M x w - (φ x + θ w)) / (qr x * qc w) with hNdef
  have hNrank : rankOn N X2 Y2 ≤ r + 2 :=
    (rankOn_rescale M φ θ qr qc X2 Y2).trans
      (by have := (rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr; omega)
  -- each entry: its covering type decides the sign of `N`
  have hcov2 := hcov1.mono hX2 hY2
  have hentry : ∀ x ∈ X2, ∀ w ∈ Y2, ∀ t ∈ S1, M x w = (τ t).eval x w →
      (t ∈ Lo → -margK k ≤ N x w ∧ N x w ≤ -1 / 2) ∧
      (t ∈ Hi → 1 / 2 ≤ N x w ∧ N x w ≤ margK k) := by
    intro x hx w hw t ht hM
    have hσ := mul_pos (hqr x hx) (hqc w hw)
    obtain ⟨hL, hH⟩ := hb x hx w hw
    constructor
    · intro htL
      obtain ⟨a, b⟩ := hL t htL
      rw [← hM] at a b
      simp only [hNdef]
      constructor
      · rw [le_div_iff₀ hσ]; linarith
      · rw [div_le_iff₀ hσ]; linarith
    · intro htH
      obtain ⟨a, b⟩ := hH t htH
      rw [← hM] at a b
      simp only [hNdef]
      constructor
      · rw [le_div_iff₀ hσ]; linarith
      · rw [div_le_iff₀ hσ]; linarith
  have hmem : ∀ t ∈ S1, t ∈ Lo ∨ t ∈ Hi := fun t ht => by
    rw [← hLH] at ht; exact mem_union.1 ht
  have hbd : ∀ x ∈ X2, ∀ w ∈ Y2, 1 / 2 ≤ |N x w| ∧ |N x w| ≤ margK k := by
    intro x hx w hw
    obtain ⟨t, ht, hM⟩ := hcov2 x hx w hw
    have he := hentry x hx w hw t ht hM
    rcases hmem t ht with h | h
    · obtain ⟨a, b⟩ := he.1 h
      rw [abs_of_neg (by linarith)]; constructor <;> linarith
    · obtain ⟨a, b⟩ := he.2 h
      rw [abs_of_pos (by linarith)]; constructor <;> linarith
  have hcardLH : #Lo + #Hi = #S1 := by rw [← card_union_of_disjoint hdisj, hLH]
  have hLoc := card_pos.2 hLo
  have hHic := card_pos.2 hHi
  have hR1 : 1 ≤ (r + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  -- total number of positive and negative entries
  have hsplit : #((X2 ×ˢ Y2).filter fun p => 0 < N p.1 p.2) +
      #((X2 ×ˢ Y2).filter fun p => 0 < (-N p.1 p.2)) = #X2 * #Y2 := by
    rw [← card_product]
    have : (X2 ×ˢ Y2).filter (fun p => 0 < (-N p.1 p.2)) =
        (X2 ×ˢ Y2).filter (fun p => ¬ 0 < N p.1 p.2) := by
      refine filter_congr fun p hp => ?_
      obtain ⟨hx, hw⟩ := mem_product.1 hp
      have := hbd p.1 hx p.2 hw
      constructor
      · intro h; linarith
      · intro h
        rcases lt_or_eq_of_le (not_lt.1 h) with h' | h'
        · linarith
        · rw [h'] at this; norm_num at this
    rw [this]; exact card_filter_add_card_filter_not _
  have finish : ∀ X3 ⊆ X2, ∀ Y3 ⊆ Y2,
      (#X2 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) *
        4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #X3 →
      (#Y2 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) *
        4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #Y3 →
      (#X : ℝ) ≤ roundCost k r * #X3 ∧ (#Y : ℝ) ≤ roundCost k r * #Y3 := by
    intro X3 _ Y3 _ e1 e2
    have f1 : (#X1 : ℝ) ≤ 4 ^ k * #X2 := by
      have : (#X1 : ℝ) ≤ 4 ^ #S1 * #X2 := by exact_mod_cast d1
      have a : (4 : ℝ) ^ #S1 ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hS1k
      nlinarith [(Nat.cast_nonneg #X2 : (0 : ℝ) ≤ #X2)]
    have f2 : (#Y1 : ℝ) ≤ 4 ^ k * #Y2 := by
      have : (#Y1 : ℝ) ≤ 4 ^ #S1 * #Y2 := by exact_mod_cast d2
      have a : (4 : ℝ) ^ #S1 ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hS1k
      nlinarith [(Nat.cast_nonneg #Y2 : (0 : ℝ) ≤ #Y2)]
    have p1 : (0 : ℝ) ≤ 16 ^ (k * k) := by positivity
    have p2 : (0 : ℝ) ≤ 4 ^ k := by positivity
    constructor
    · calc (#X : ℝ) ≤ 16 ^ (k * k) * #X1 := c1r
        _ ≤ 16 ^ (k * k) * (4 ^ k * #X2) := mul_le_mul_of_nonneg_left f1 p1
        _ ≤ 16 ^ (k * k) * (4 ^ k * (64 * ((r + 1) ^ k : ℕ) *
              4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #X3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 p2) p1
        _ = roundCost k r * #X3 := by unfold roundCost; ring
    · calc (#Y : ℝ) ≤ 16 ^ (k * k) * #Y1 := c2r
        _ ≤ 16 ^ (k * k) * (4 ^ k * #Y2) := mul_le_mul_of_nonneg_left f2 p1
        _ ≤ 16 ^ (k * k) * (4 ^ k * (64 * ((r + 1) ^ k : ℕ) *
              4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #Y3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 p2) p1
        _ = roundCost k r * #Y3 := by unfold roundCost; ring
  by_cases hmaj : #X2 * #Y2 ≤ 2 * #((X2 ×ˢ Y2).filter fun p => 0 < N p.1 p.2)
  · -- majority positive: keep `Hi`
    have hHk : (r + 1) ^ #Hi ≤ (r + 1) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨X3, hX3, Y3, hY3, e1, e2, hcov3⟩ := round_core M N τ Hi X2 Y2 r ((r + 1) ^ k)
      (margK k) ((rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr) hNrank hHk hR1 hbd
      (fun x hx w hw hN => by
        obtain ⟨t, ht, hM⟩ := hcov2 x hx w hw
        refine ⟨t, ?_, hM⟩
        rcases hmem t ht with h | h
        · have := ((hentry x hx w hw t ht hM).1 h).2; linarith
        · exact h)
      (fun x hx w hw hN t ht hM => by
        have := ((hentry x hx w hw t (hLH ▸ mem_union_right _ ht) hM).2 ht).1; linarith)
      hmaj
    obtain ⟨f1, f2⟩ := finish X3 hX3 Y3 hY3 e1 e2
    refine ⟨X3, hX3.trans (hX2.trans hX1), Y3, hY3.trans (hY2.trans hY1), f1, f2, Hi,
      (hLH ▸ subset_union_right).trans hS1, by have := card_le_card hS1; omega, hcov3⟩
  · -- majority negative: keep `Lo` (apply the core to `-N`)
    have hLk : (r + 1) ^ #Lo ≤ (r + 1) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have hNrank' : rankOn (fun x w => -N x w) X2 Y2 ≤ r + 2 := by
      have : (fun x w => -N x w) = fun x w =>
          (M x w - (φ x + θ w)) / ((-qr x) * qc w) := by
        funext x w; simp only [hNdef]; rw [neg_mul, div_neg]
      rw [this]
      exact (rankOn_rescale M φ θ (fun x => -qr x) qc X2 Y2).trans
        (by have := (rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr; omega)
    obtain ⟨X3, hX3, Y3, hY3, e1, e2, hcov3⟩ := round_core M (fun x w => -N x w) τ Lo X2 Y2 r
      ((r + 1) ^ k) (margK k) ((rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr)
      hNrank' hLk hR1 (fun x hx w hw => by rw [abs_neg]; exact hbd x hx w hw)
      (fun x hx w hw hN => by
        obtain ⟨t, ht, hM⟩ := hcov2 x hx w hw
        refine ⟨t, ?_, hM⟩
        rcases hmem t ht with h | h
        · exact h
        · have := ((hentry x hx w hw t ht hM).2 h).1; linarith)
      (fun x hx w hw hN t ht hM => by
        have := ((hentry x hx w hw t (hLH ▸ mem_union_left _ ht) hM).1 ht).2
        linarith)
      (by have h' := hsplit; push Not at hmaj; linarith)
    obtain ⟨f1, f2⟩ := finish X3 hX3 Y3 hY3 e1 e2
    refine ⟨X3, hX3.trans (hX2.trans hX1), Y3, hY3.trans (hY2.trans hY1), f1, f2, Lo,
      (hLH ▸ subset_union_left).trans hS1, by have := card_le_card hS1; omega, hcov3⟩

/-- Total cost of Theorem LR with at most `k` types. -/
noncomputable def LRcost : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, r => roundCost (k + 1) r * LRcost k r

theorem one_le_LRcost (k r : ℕ) : 1 ≤ LRcost k r := by
  induction k with
  | zero => simp [LRcost]
  | succ k ih =>
    simp only [LRcost]
    have := one_le_roundCost (k + 1) r
    nlinarith

/-- **Theorem LR** (label rounding, round11/01), modulo `lemmaR`. -/
theorem theoremLR (M : α → β → ℝ) (τ : ι → TF α β) (r : ℕ) :
    ∀ (k : ℕ) (S : Finset ι) (X : Finset α) (Y : Finset β), #S ≤ k → X.Nonempty →
      Y.Nonempty → rankOn M X Y ≤ r → Covers M τ S X Y →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ t ∈ S, (#X : ℝ) ≤ LRcost k r * #X' ∧
        (#Y : ℝ) ≤ LRcost k r * #Y' ∧ ∀ x ∈ X', ∀ w ∈ Y', M x w = (τ t).eval x w := by
  intro k
  induction k with
  | zero =>
    intro S X Y hS hX hY _ hcov
    obtain ⟨x, hx⟩ := hX; obtain ⟨w, hw⟩ := hY
    obtain ⟨t, ht, _⟩ := hcov x hx w hw
    have := card_pos.2 ⟨t, ht⟩; omega
  | succ k ih =>
    intro S X Y hS hX hY hr hcov
    by_cases h1 : #S ≤ 1
    · obtain ⟨x, hx⟩ := hX; obtain ⟨w, hw⟩ := hY
      obtain ⟨t, ht, _⟩ := hcov x hx w hw
      have hst : S = {t} := by
        rw [eq_singleton_iff_unique_mem]
        exact ⟨ht, fun u hu => card_le_one.1 h1 u hu t ht⟩
      have hL := one_le_LRcost (k + 1) r
      refine ⟨X, subset_refl _, Y, subset_refl _, t, ht, ?_, ?_, fun x' hx' w' hw' => ?_⟩
      · nlinarith [(Nat.cast_nonneg #X : (0 : ℝ) ≤ #X)]
      · nlinarith [(Nat.cast_nonneg #Y : (0 : ℝ) ≤ #Y)]
      · obtain ⟨u, hu, hM⟩ := hcov x' hx' w' hw'
        rw [hst, mem_singleton] at hu; rw [hM, hu]
    · push Not at h1
      obtain ⟨X1, hX1, Y1, hY1, c1, c2, S1, hS1, hlt, hcov1⟩ :=
        lr_round M τ S X Y (k + 1) r hX hY hr hcov h1 hS
      have hX1ne : X1.Nonempty := by
        rw [← card_pos]; by_contra h
        have h0 : #X1 = 0 := by omega
        have e : (#X : ℝ) ≤ 0 := by simpa [h0] using c1
        have e' : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 hX
        linarith
      have hY1ne : Y1.Nonempty := by
        rw [← card_pos]; by_contra h
        have h0 : #Y1 = 0 := by omega
        have e : (#Y : ℝ) ≤ 0 := by simpa [h0] using c2
        have e' : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 hY
        linarith
      obtain ⟨X2, hX2, Y2, hY2, t, ht, d1, d2, hM⟩ := ih S1 X1 Y1 (by omega) hX1ne hY1ne
        ((rankOn_mono M hX1 hY1).trans hr) hcov1
      have hRC := one_le_roundCost (k + 1) r
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, t, hS1 ht, ?_, ?_, hM⟩
      · simp only [LRcost]
        calc (#X : ℝ) ≤ roundCost (k + 1) r * #X1 := c1
          _ ≤ roundCost (k + 1) r * (LRcost k r * #X2) := by gcongr
          _ = _ := by ring
      · simp only [LRcost]
        calc (#Y : ℝ) ≤ roundCost (k + 1) r * #Y1 := c2
          _ ≤ roundCost (k + 1) r * (LRcost k r * #Y2) := by gcongr
          _ = _ := by ring

end E1088
