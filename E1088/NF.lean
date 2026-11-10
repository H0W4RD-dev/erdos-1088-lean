import E1088.LRBasic

/-!
# Theorem LR, part 2: dominant gap (NF3) and the cut

* `compare_basic` : two basic quantities are comparable up to a factor 16 on a refinement.
* `tournament`    : among finitely many basic quantities one dominates all others up to `16^p`.

DEVIATION FROM THE PAPER (harmless): round11/01 Lemma NF (NF3) claims a dominant gap with
factor 16 independent of `k`; we use a simple tournament, which gives factor `16^(k-1)`.
This only changes the constant `K` of the rescaled matrix (from `256 (k-1)` to
`32 (k-1) 16^(k-1)`), i.e. the loss per round becomes `O(16^k k sqrt(r) log r)` instead of
`O(k^2 sqrt(r) log r)`. For fixed `k` (as in the application) the shape
`2^{-O_k(sqrt r log r)}` is unchanged.
-/

set_option linter.unusedSectionVars false

open Finset

namespace E1088

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

theorem nonempty_of_card_le {γ : Type*} {X X' : Finset γ} {c : ℕ} (hX : X.Nonempty)
    (h : #X ≤ c * #X') : X'.Nonempty := by
  rw [← card_pos]
  have := card_pos.2 hX
  rcases Nat.eq_zero_or_pos #X' with h0 | h0
  · rw [h0] at h; omega
  · exact h0

theorem cross_le {a b c d k : ℝ} (hb : 0 < b) (hd : 0 < d) (h : k * (c / d) ≤ a / b) :
    k * c * b ≤ a * d := by
  have := mul_le_mul_of_nonneg_right h (mul_pos hb hd).le
  have e1 : k * (c / d) * (b * d) = k * c * b := by field_simp
  have e2 : a / b * (b * d) = a * d := by field_simp
  linarith

theorem cross_lt {a b c d k : ℝ} (hb : 0 < b) (hd : 0 < d) (h : c / d < k * (a / b)) :
    c * b < k * a * d := by
  have := mul_lt_mul_of_pos_right h (mul_pos hb hd)
  have e1 : k * (a / b) * (b * d) = k * a * d := by field_simp
  have e2 : c / d * (b * d) = c * b := by field_simp
  linarith

/-- Comparison of two basic quantities `Q = qr qc`, `Q' = qr' qc'` (via Lemma B). -/
theorem compare_basic (X : Finset α) (Y : Finset β) (hY : Y.Nonempty)
    (qr qr' : α → ℝ) (qc qc' : β → ℝ) (h1 : ∀ x ∈ X, 0 < qr x) (h2 : ∀ x ∈ X, 0 < qr' x)
    (h3 : ∀ w ∈ Y, 0 < qc w) (h4 : ∀ w ∈ Y, 0 < qc' w) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 4 * #Y' ∧
      ((∀ x ∈ X', ∀ w ∈ Y', qr' x * qc' w ≤ 16 * (qr x * qc w)) ∨
       (∀ x ∈ X', ∀ w ∈ Y', qr x * qc w ≤ 16 * (qr' x * qc' w))) := by
  obtain ⟨X', hX', Y', hY', c1, c2, h⟩ := lemmaB X Y hY (fun x => qr x / qr' x)
    (fun w => qc' w / qc w) (fun x hx => div_pos (h1 x hx) (h2 x hx))
    (fun w hw => (div_pos (h4 w hw) (h3 w hw)).le)
  refine ⟨X', hX', Y', hY', c1, c2, ?_⟩
  rcases h with h | h | ⟨s, hs, hD, hE⟩
  · refine Or.inl fun x hx w hw => ?_
    have a1 := h1 x (hX' hx); have a2 := h2 x (hX' hx)
    have a3 := h3 w (hY' hw); have a4 := h4 w (hY' hw)
    have := cross_le a2 a3 (h x hx w hw)
    nlinarith [mul_pos a1 a3, mul_pos a2 a4]
  · refine Or.inr fun x hx w hw => ?_
    have a1 := h1 x (hX' hx); have a2 := h2 x (hX' hx)
    have a3 := h3 w (hY' hw); have a4 := h4 w (hY' hw)
    have := cross_le a3 a2 (h x hx w hw)
    nlinarith [mul_pos a1 a3, mul_pos a2 a4]
  · refine Or.inl fun x hx w hw => ?_
    have a1 := h1 x (hX' hx); have a2 := h2 x (hX' hx)
    have a3 := h3 w (hY' hw); have a4 := h4 w (hY' hw)
    obtain ⟨d1, d2⟩ := hD x hx
    obtain ⟨e1, e2⟩ := hE w hw
    -- `qc'/qc < 4 s < 16 (qr/qr')`
    have : qc' w / qc w < 16 * (qr x / qr' x) := by linarith
    have := cross_lt a2 a3 this
    nlinarith [mul_pos a1 a3, mul_pos a2 a4]

/-- **Tournament.** Among the basic quantities `Q_j = qr j * qc j` (`j ∈ J`, `J` nonempty) one
dominates all others up to `16^#J`, on a refinement of cost `4^#J` per side. -/
theorem tournament {κ : Type*} [DecidableEq κ] (qr : κ → α → ℝ) (qc : κ → β → ℝ)
    (J : Finset κ) :
    ∀ (X : Finset α) (Y : Finset β), Y.Nonempty → J.Nonempty →
      (∀ j ∈ J, ∀ x ∈ X, 0 < qr j x) → (∀ j ∈ J, ∀ w ∈ Y, 0 < qc j w) →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 ^ #J * #X' ∧ #Y ≤ 4 ^ #J * #Y' ∧ ∃ j₀ ∈ J,
        ∀ j ∈ J, ∀ x ∈ X', ∀ w ∈ Y', qr j x * qc j w ≤ 16 ^ #J * (qr j₀ x * qc j₀ w) := by
  induction J using Finset.induction_on with
  | empty => intro X Y _ h; exact absurd h (by simp)
  | insert a J haJ ih =>
    intro X Y hY _ hqr hqc
    rw [card_insert_of_notMem haJ]
    rcases J.eq_empty_or_nonempty with hJ | hJ
    · subst hJ
      refine ⟨X, subset_refl _, Y, subset_refl _, by simp; omega, by simp; omega, a,
        mem_insert_self _ _, fun j hj x hx w hw => ?_⟩
      simp only [insert_empty, mem_singleton] at hj
      subst hj
      have := mul_pos (hqr j (mem_insert_self _ _) x hx) (hqc j (mem_insert_self _ _) w hw)
      simp; linarith
    obtain ⟨X1, hX1, Y1, hY1, c1, c2, j₁, hj₁, hdom⟩ := ih X Y hY hJ
      (fun j hj => hqr j (mem_insert_of_mem hj)) (fun j hj => hqc j (mem_insert_of_mem hj))
    have hY1ne : Y1.Nonempty := nonempty_of_card_le hY c2
    obtain ⟨X2, hX2, Y2, hY2, d1, d2, hc⟩ := compare_basic X1 Y1 hY1ne (qr j₁) (qr a) (qc j₁)
      (qc a) (fun x hx => hqr j₁ (mem_insert_of_mem hj₁) x (hX1 hx))
      (fun x hx => hqr a (mem_insert_self _ _) x (hX1 hx))
      (fun w hw => hqc j₁ (mem_insert_of_mem hj₁) w (hY1 hw))
      (fun w hw => hqc a (mem_insert_self _ _) w (hY1 hw))
    have cX : #X ≤ 4 ^ (#J + 1) * #X2 := by
      calc #X ≤ 4 ^ #J * #X1 := c1
        _ ≤ 4 ^ #J * (4 * #X2) := Nat.mul_le_mul_left _ d1
        _ = 4 ^ (#J + 1) * #X2 := by ring
    have cY : #Y ≤ 4 ^ (#J + 1) * #Y2 := by
      calc #Y ≤ 4 ^ #J * #Y1 := c2
        _ ≤ 4 ^ #J * (4 * #Y2) := Nat.mul_le_mul_left _ d2
        _ = 4 ^ (#J + 1) * #Y2 := by ring
    have h16 : (16 : ℝ) ^ #J ≤ 16 ^ (#J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rcases hc with hc | hc
    · -- champion stays `j₁`
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, cX, cY, j₁, mem_insert_of_mem hj₁,
        fun j hj x hx w hw => ?_⟩
      have hpos := mul_pos (hqr j₁ (mem_insert_of_mem hj₁) x (hX1 (hX2 hx)))
        (hqc j₁ (mem_insert_of_mem hj₁) w (hY1 (hY2 hw)))
      rcases mem_insert.1 hj with rfl | hj
      · have := hc x hx w hw
        have : (16 : ℝ) ≤ 16 ^ (#J + 1) := by
          calc (16 : ℝ) = 16 ^ 1 := by norm_num
            _ ≤ 16 ^ (#J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      · have := hdom j hj x (hX2 hx) w (hY2 hw)
        nlinarith
    · -- new champion `a`
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, cX, cY, a, mem_insert_self _ _,
        fun j hj x hx w hw => ?_⟩
      have hpos := mul_pos (hqr a (mem_insert_self _ _) x (hX1 (hX2 hx)))
        (hqc a (mem_insert_self _ _) w (hY1 (hY2 hw)))
      rcases mem_insert.1 hj with rfl | hj
      · have : (1 : ℝ) ≤ 16 ^ (#J + 1) := one_le_pow₀ (by norm_num)
        nlinarith
      · have h1 := hdom j hj x (hX2 hx) w (hY2 hw)
        have h2 := hc x hx w hw
        have hp16 : (0 : ℝ) ≤ 16 ^ #J := by positivity
        calc qr j x * qc j w ≤ 16 ^ #J * (qr j₁ x * qc j₁ w) := h1
          _ ≤ 16 ^ #J * (16 * (qr a x * qc a w)) := mul_le_mul_of_nonneg_left h2 hp16
          _ = 16 ^ (#J + 1) * (qr a x * qc a w) := by ring

end E1088
