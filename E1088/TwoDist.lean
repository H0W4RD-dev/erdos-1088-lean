import Mathlib

/-!
# The two-distribution lemma (manuscript Lemma 7.2), in counting form

`P, Q` are finite sets with value maps `f, g` into `ℝ`. If at most `κ⁴ |P| |Q|` pairs `(x, w)` have
`f x ≠ ρ'`, `g w ≠ ρ` and `f x ≠ g w`, then for some `t` all but `κ |P|` points of `P` have
`f x ∈ {ρ', t}`, or all but `κ |Q|` points of `Q` have `g w ∈ {ρ, t}` (`0 ≤ κ ≤ 1/2`).
(The paper states this with `η = κ⁴ ≤ 1/16`.)
-/

open Finset

namespace E1088

theorem two_dist {α β : Type*} [DecidableEq α] [DecidableEq β] (P : Finset α) (Q : Finset β)
    (f : α → ℝ) (g : β → ℝ) (ρ ρ' κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2)
    (hN : ((((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2).card : ℕ) : ℝ) ≤
      κ ^ 4 * P.card * Q.card) :
    ∃ t : ℝ, (((P.filter fun x => f x ≠ ρ' ∧ f x ≠ t).card : ℕ) : ℝ) ≤ κ * P.card ∨
      (((Q.filter fun w => g w ≠ ρ ∧ g w ≠ t).card : ℕ) : ℝ) ≤ κ * Q.card := by
  classical
  set P1 := P.filter fun x => f x ≠ ρ' with hP1
  set Q1 := Q.filter fun w => g w ≠ ρ with hQ1
  set Pc : ℝ := (P.card : ℝ) with hPc
  set Qc : ℝ := (Q.card : ℝ) with hQc
  have hP0 : 0 ≤ Pc := Nat.cast_nonneg _
  have hQ0 : 0 ≤ Qc := Nat.cast_nonneg _
  by_cases ha : (P1.card : ℝ) ≤ κ * Pc
  · have hs : (P.filter fun x => f x ≠ ρ' ∧ f x ≠ ρ') ⊆ P1 := fun x hx =>
      mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.1⟩
    exact ⟨ρ', Or.inl (le_trans (by exact_mod_cast card_le_card hs) ha)⟩
  by_cases hb : (Q1.card : ℝ) ≤ κ * Qc
  · have hs : (Q.filter fun w => g w ≠ ρ ∧ g w ≠ ρ) ⊆ Q1 := fun w hw =>
      mem_filter.2 ⟨(mem_filter.1 hw).1, (mem_filter.1 hw).2.1⟩
    exact ⟨ρ, Or.inr (le_trans (by exact_mod_cast card_le_card hs) hb)⟩
  push Not at ha hb
  set a : ℝ := (P1.card : ℝ) with hadef
  set b : ℝ := (Q1.card : ℝ) with hbdef
  -- fibre counts in `Q1`
  let c : ℝ → ℕ := fun t => (Q1.filter fun w => g w = t).card
  have hQ1ne : Q1.Nonempty := by
    rw [← card_pos]; have : (0 : ℝ) < Q1.card := lt_of_le_of_lt (by positivity) hb
    exact_mod_cast this
  obtain ⟨t0, ht0, hmax0⟩ := exists_max_image (Q1.image g) c (hQ1ne.image g)
  have hmax : ∀ t, c t ≤ c t0 := by
    intro t
    by_cases ht : t ∈ Q1.image g
    · exact hmax0 t ht
    · have : c t = 0 := by
        simp only [c, card_eq_zero, filter_eq_empty_iff]
        intro w hw hwt; exact ht (mem_image.2 ⟨w, hw, hwt⟩)
      omega
  have hfib : ∀ s, s ≠ t0 → c s + c t0 ≤ Q1.card := by
    intro s hs
    rw [← card_union_of_disjoint]
    · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    · rw [disjoint_left]; intro w h1 h2
      exact hs ((mem_filter.1 h1).2.symm.trans (mem_filter.1 h2).2)
  -- `m` = number of pairs in `P1 × Q1` with equal values
  set m : ℕ := ∑ x ∈ P1, c (f x) with hm
  have hmN : (P1.card * Q1.card : ℕ) ≤ m +
      ((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2).card := by
    have e1 : P1.card * Q1.card = ((P1 ×ˢ Q1).filter fun q => f q.1 = g q.2).card +
        ((P1 ×ˢ Q1).filter fun q => ¬ f q.1 = g q.2).card := by
      rw [card_filter_add_card_filter_not, card_product]
    have e2 : ((P1 ×ˢ Q1).filter fun q => f q.1 = g q.2).card = m := by
      rw [hm, card_filter, sum_product]
      refine sum_congr rfl fun x _ => ?_
      simp only [c, card_filter]
      exact sum_congr rfl fun w _ => by by_cases h : f x = g w <;> simp [h, eq_comm]
    have e3 : ((P1 ×ˢ Q1).filter fun q => ¬ f q.1 = g q.2) ⊆
        ((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2) := by
      intro q hq
      obtain ⟨hq1, hne⟩ := mem_filter.1 hq
      obtain ⟨hx, hw⟩ := mem_product.1 hq1
      obtain ⟨hxP, hx'⟩ := mem_filter.1 hx
      obtain ⟨hwQ, hw'⟩ := mem_filter.1 hw
      exact mem_filter.2 ⟨mem_product.2 ⟨hxP, hwQ⟩, hx', hw', hne⟩
    have := card_le_card e3
    omega
  have hmN' : a * b ≤ (m : ℝ) + κ ^ 4 * Pc * Qc := by
    have : ((P1.card * Q1.card : ℕ) : ℝ) ≤ (m : ℝ) +
        ((((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2).card : ℕ) : ℝ) := by
      exact_mod_cast hmN
    push_cast at this
    linarith
  set cs : ℝ := (c t0 : ℝ) with hcs
  have hm1 : (m : ℝ) ≤ a * cs := by
    have : m ≤ P1.card * c t0 := by
      rw [hm]
      calc ∑ x ∈ P1, c (f x) ≤ ∑ _x ∈ P1, c t0 := sum_le_sum fun x _ => hmax _
        _ = P1.card * c t0 := by rw [sum_const, smul_eq_mul]
    rw [hadef, hcs]; exact_mod_cast this
  set u := (P.filter fun x => f x ≠ ρ' ∧ f x ≠ t0).card with hu
  have hm2 : (m : ℝ) ≤ (a - u) * cs + u * (b - cs) := by
    have hsplit := sum_filter_add_sum_filter_not P1 (fun x => f x = t0) (fun x => c (f x))
    have hu' : (P1.filter fun x => ¬ f x = t0).card = u := by
      rw [hu, hP1, filter_filter]
    have hu'' : (P1.filter fun x => f x = t0).card + u = P1.card := by
      rw [← hu', card_filter_add_card_filter_not]
    have s1 : ∑ x ∈ P1.filter (fun x => f x = t0), c (f x) =
        (P1.filter fun x => f x = t0).card * c t0 := by
      rw [sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2], sum_const, smul_eq_mul]
    have s2 : ∑ x ∈ P1.filter (fun x => ¬ f x = t0), c (f x) ≤ u * (Q1.card - c t0) := by
      calc ∑ x ∈ P1.filter (fun x => ¬ f x = t0), c (f x)
          ≤ ∑ _x ∈ P1.filter (fun x => ¬ f x = t0), (Q1.card - c t0) := by
            refine sum_le_sum fun x hx => ?_
            have := hfib (f x) (mem_filter.1 hx).2
            omega
        _ = u * (Q1.card - c t0) := by rw [sum_const, smul_eq_mul, hu']
    have hcQ : c t0 ≤ Q1.card := card_le_card (filter_subset _ _)
    have : (m : ℝ) ≤ ((P1.filter fun x => f x = t0).card : ℝ) * cs + u * (b - cs) := by
      have h1 : m ≤ (P1.filter fun x => f x = t0).card * c t0 + u * (Q1.card - c t0) := by
        rw [hm, ← hsplit, s1]; omega
      have h2 : ((u * (Q1.card - c t0) : ℕ) : ℝ) = u * (b - cs) := by
        rw [Nat.cast_mul, Nat.cast_sub hcQ]
      have h3 : (m : ℝ) ≤ (((P1.filter fun x => f x = t0).card * c t0 : ℕ) : ℝ) +
          ((u * (Q1.card - c t0) : ℕ) : ℝ) := by exact_mod_cast h1
      rw [h2] at h3; push_cast at h3; exact h3
    have hpa : ((P1.filter fun x => f x = t0).card : ℝ) = a - u := by
      rw [hadef, ← hu'']; push_cast; ring
    rw [hpa] at this; exact this
  refine ⟨t0, Or.inl ?_⟩
  by_contra hcon
  push Not at hcon
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hcs0 : (0 : ℝ) ≤ cs := Nat.cast_nonneg _
  have hcsb : cs ≤ b := by rw [hcs, hbdef]; exact_mod_cast card_le_card (filter_subset _ _)
  have haP : a ≤ Pc := by rw [hadef, hPc]; exact_mod_cast card_le_card (filter_subset _ _)
  -- `u cs ≤ κ⁴ P Q` and `a cs ≥ a b - κ⁴ P Q`
  have k1 : u * cs ≤ κ ^ 4 * Pc * Qc := by
    have : (a - u) * cs + u * (b - cs) ≤ (a - u) * cs + a * (b - cs) := by
      have hs : (P.filter fun x => f x ≠ ρ' ∧ f x ≠ t0) ⊆ P1 := fun x hx =>
        mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.1⟩
      have hua : (u : ℝ) ≤ a := by rw [hadef, hu]; exact_mod_cast card_le_card hs
      have : 0 ≤ b - cs := by linarith
      have := mul_le_mul_of_nonneg_right hua this
      linarith
    have e : (a - u) * cs + a * (b - cs) = a * b - u * cs := by ring
    linarith
  have k2 : a * b - κ ^ 4 * Pc * Qc ≤ a * cs := by linarith
  have hκP : κ * Pc < u := hcon
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  have hb0 : 0 < b := lt_of_le_of_lt (by positivity) hb
  -- `u (a b - κ⁴PQ) ≤ u a cs ≤ a κ⁴ P Q`
  have k3 : u * (a * b - κ ^ 4 * Pc * Qc) ≤ a * (κ ^ 4 * Pc * Qc) := by
    calc u * (a * b - κ ^ 4 * Pc * Qc) ≤ u * (a * cs) := mul_le_mul_of_nonneg_left k2 hu0
      _ = a * (u * cs) := by ring
      _ ≤ a * (κ ^ 4 * Pc * Qc) := mul_le_mul_of_nonneg_left k1 ha0.le
  have hκ2 : κ ^ 2 ≤ 1 / 4 := by nlinarith
  have hPQ0 : 0 ≤ κ ^ 2 * Pc * Qc := by positivity
  have hpos : κ ^ 2 * Pc * Qc * (1 - κ ^ 2) ≥ κ ^ 4 * Pc * Qc := by
    have := mul_nonneg hPQ0 (show 0 ≤ 1 - 2 * κ ^ 2 by linarith)
    have e : κ ^ 2 * Pc * Qc * (1 - κ ^ 2) - κ ^ 4 * Pc * Qc = κ ^ 2 * Pc * Qc * (1 - 2 * κ ^ 2) := by
      ring
    linarith
  have hab : a * b > κ * Pc * (κ * Qc) := by
    have : κ * Pc * (κ * Qc) ≤ a * (κ * Qc) := mul_le_mul_of_nonneg_right ha.le (by positivity)
    have : a * (κ * Qc) < a * b := mul_lt_mul_of_pos_left hb ha0
    linarith
  have hD : 0 < a * b - κ ^ 4 * Pc * Qc := by
    have e : κ * Pc * (κ * Qc) = κ ^ 2 * Pc * Qc := by ring
    have : κ ^ 4 * Pc * Qc ≤ κ ^ 2 * Pc * Qc := by
      have := mul_le_mul_of_nonneg_left (show κ ^ 2 ≤ 1 by linarith) hPQ0
      linarith [show κ ^ 2 * Pc * Qc * κ ^ 2 = κ ^ 4 * Pc * Qc by ring]
    linarith
  -- `κ P (a b - κ⁴ P Q) < a κ⁴ P Q`, i.e. `a (b - κ³ Q) < κ⁴ P Q` after dividing by `κ P`
  have k4 : κ * Pc * (a * b - κ ^ 4 * Pc * Qc) < a * (κ ^ 4 * Pc * Qc) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hκP hD) k3
  rcases eq_or_lt_of_le hκ0 with hκe | hκpos
  · subst hκe; norm_num at k4
  have hPpos : 0 < Pc := by
    by_contra h; push Not at h; have : Pc = 0 := le_antisymm h hP0; rw [this] at ha; linarith
  have k5 : a * b - κ ^ 4 * Pc * Qc < a * (κ ^ 3 * Qc) := by
    have hkP : 0 < κ * Pc := mul_pos hκpos hPpos
    have : κ * Pc * (a * b - κ ^ 4 * Pc * Qc) < κ * Pc * (a * (κ ^ 3 * Qc)) := by
      calc κ * Pc * (a * b - κ ^ 4 * Pc * Qc) < a * (κ ^ 4 * Pc * Qc) := k4
        _ = κ * Pc * (a * (κ ^ 3 * Qc)) := by ring
    exact lt_of_mul_lt_mul_left this hkP.le
  -- but `a (b - κ³Q) > κP · κQ (1 - κ²) ≥ κ⁴ P Q`
  have k6 : a * (b - κ ^ 3 * Qc) ≥ κ * Pc * (κ * Qc * (1 - κ ^ 2)) := by
    have e1 : b - κ ^ 3 * Qc ≥ κ * Qc * (1 - κ ^ 2) := by
      linarith [show κ * Qc * (1 - κ ^ 2) = κ * Qc - κ ^ 3 * Qc by ring]
    have e2 : 0 ≤ κ * Qc * (1 - κ ^ 2) := by
      have : 0 ≤ 1 - κ ^ 2 := by nlinarith
      positivity
    calc a * (b - κ ^ 3 * Qc) ≥ a * (κ * Qc * (1 - κ ^ 2)) := mul_le_mul_of_nonneg_left e1 ha0.le
      _ ≥ κ * Pc * (κ * Qc * (1 - κ ^ 2)) := mul_le_mul_of_nonneg_right ha.le e2
  have e1 : a * (b - κ ^ 3 * Qc) = a * b - a * (κ ^ 3 * Qc) := by ring
  have e2 : κ * Pc * (κ * Qc * (1 - κ ^ 2)) = κ ^ 2 * Pc * Qc * (1 - κ ^ 2) := by ring
  linarith

end E1088
