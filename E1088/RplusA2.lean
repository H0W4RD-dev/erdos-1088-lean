import E1088.RplusA

/-!
# Theorem R⁺, Step A: the cross-pair count (Step 3) and the covering (Step 4)
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

section StepA

variable {n D h j : ℕ} {X S W S' : Finset (ℝ^d)} {σ : ℝ} {a b : ℝ^d} {ρ1 ρ2 : ℝ}

theorem StepACtx.notT (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hab : dist a b ≠ ρ) {x : ℝ^d} (hx : x ∈ W) (hxb : dist x b = ρ) : x ∉ TA S' a b := by
  have hxb' : x ≠ b := fun e => by rw [e, dist_self] at hxb; linarith
  have hxa : x ≠ a := fun e => hab (by rw [← e]; exact hxb)
  simp only [TA, mem_insert, not_or]
  exact ⟨hxb', hxa, fun h => cx.notS hx (cx.sub h)⟩

/-- `4^{n-2} μ ≤ σ`. -/
theorem four_pow_mu_le (n D h : ℕ) (σ : ℝ) (hσ : smin n D h ≤ σ) :
    4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) ≤ σ := by
  have h1 := LRcost_mono (D + 2) (kG_le_kstar n)
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hL := one_le_LRcost (kstar n) (D + 2)
  have h2 : LRcost (kG n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * h :=
    mul_le_mul_of_nonneg_right h1 h0
  have h4 : (4 : ℝ) ^ (n - 2) ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4' : (0 : ℝ) ≤ 4 ^ (n - 2) := by positivity
  have h3 : 4 ^ (n - 2) * (LRcost (kstar n) (D + 2) * h) ≤ smin n D h := by
    unfold smin
    have : 0 ≤ LRcost (kstar n) (D + 2) * h := by positivity
    have e : 4 ^ (n - 2) * (LRcost (kstar n) (D + 2) * h) ≤
        4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * h) := mul_le_mul_of_nonneg_right h4 this
    nlinarith
  have := mul_le_mul_of_nonneg_left h2 h4'
  linarith

/-- **Step 3** (`Lemma S2`, manuscript (7.3)). -/
theorem StepACtx.S2 (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) (Pg Qg : Finset (ℝ^d))
    (hPg : ∀ x ∈ Pg, x ∈ W ∧ dist x b = ρ1 ∧ Rainbow (insert x (TA S' a b)))
    (hQg : ∀ w ∈ Qg, w ∈ W ∧ dist w b = ρ2 ∧ Rainbow (insert w (TA S' a b))) :
    ((((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧ dist q.1 a ≠ dist q.2 a).card
      : ℕ) : ℝ) ≤ (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) + n ^ 2 * σ) * (Pg.card + Qg.card) := by
  classical
  set T := TA S' a b with hTdef
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans cx.hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hTn : T.card + 2 = n := by rw [cx.card_T]; have := cx.hn; omega
  have hT1 : T.Nonempty := ⟨b, mem_insert_self _ _⟩
  have hPQ : Disjoint Pg Qg := by
    rw [disjoint_left]; intro x hxP hxQ
    exact cx.hρ ((hPg x hxP).2.1.symm.trans (hQg x hxQ).2.1)
  have hLD := G1_pairs n D h X T Pg Qg cx.amb.free cx.amb.dim cx.amb.half cx.T_sub hTn hT1
    (fun x hx => cx.conf.subW (hPg x hx).1) (fun x hx => cx.conf.subW (hQg x hx).1) hPQ
    (fun x hx => ⟨cx.notT cx.ρ1pos cx.a1 (hPg x hx).1 (hPg x hx).2.1, (hPg x hx).2.2⟩)
    (fun x hx => ⟨cx.notT cx.ρ2pos cx.a2 (hQg x hx).1 (hQg x hx).2.1, (hQg x hx).2.2⟩)
  -- the two classes of label-sharing pairs
  let R : ℝ^d → Finset ℝ := fun w => insert ρ2 (insert (dist w a) (S'.image (dist w)))
  set Cl1 := (Qg ×ˢ Pg).filter fun q => ∃ s ∈ S', dist q.2 s ∈ R q.1 with hCl1
  set Cl2 := (Qg ×ˢ Pg).filter fun q => ∃ s ∈ S', dist q.1 s ∈ ({ρ1, dist q.2 a} : Finset ℝ)
    with hCl2
  have hsub : ((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
      dist q.1 a ≠ dist q.2 a) ⊆
      ((Qg ×ˢ Pg).filter fun q => Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1 ∪ Cl2 := by
    intro q hq
    obtain ⟨hqp, hq1, hq2, hq3⟩ := mem_filter.1 hq
    obtain ⟨hw, hx⟩ := mem_product.1 hqp
    by_cases hd : Disjoint (labels T q.1) (labels T q.2)
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hqp, hd⟩))
    rw [not_disjoint_iff] at hd
    obtain ⟨v, hvw, hvx⟩ := hd
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hvw
    obtain ⟨y', hy', he⟩ := mem_image.1 hvx
    have hwb := (hQg _ hw).2.1
    have hxb := (hPg _ hx).2.1
    have c1 : ∀ s ∈ S', dist q.2 s ∈ R q.1 → q ∈ ((Qg ×ˢ Pg).filter fun q =>
        Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1 ∪ Cl2 := fun s hs hm =>
      mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hqp, s, hs, hm⟩))
    have c2 : ∀ s ∈ S', dist q.1 s ∈ ({ρ1, dist q.2 a} : Finset ℝ) → q ∈ ((Qg ×ˢ Pg).filter
        fun q => Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1 ∪ Cl2 := fun s hs hm =>
      mem_union_right _ (mem_filter.2 ⟨hqp, s, hs, hm⟩)
    simp only [hTdef, TA, mem_insert] at hy hy'
    rcases hy with ey | ey | hy <;> rcases hy' with ey' | ey' | hy'
    · rw [ey, ey', hwb, hxb] at he; exact absurd he cx.hρ
    · rw [ey, ey', hwb] at he; exact absurd he hq2
    · rw [ey, hwb] at he; exact c1 y' hy' (by simp [R, he])
    · rw [ey, ey', hxb] at he; exact absurd he.symm hq1
    · rw [ey, ey'] at he; exact absurd he.symm hq3
    · rw [ey] at he; exact c1 y' hy' (by simp [R, he])
    · rw [ey', hxb] at he; exact c2 y hy (by simp [he])
    · rw [ey'] at he; exact c2 y hy (by simp [he])
    · exact c1 y' hy' (mem_insert_of_mem (mem_insert_of_mem (mem_image.2 ⟨y, hy, he.symm⟩)))
  -- counting `Cl1` (for fixed `w`) and `Cl2` (for fixed `x`)
  have hCl1c : (Cl1.card : ℝ) ≤ Qg.card * ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ)) := by
    have hcount : Cl1.card = ∑ w ∈ Qg, (Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w).card := by
      rw [hCl1, card_filter, sum_product]
      exact sum_congr rfl fun w _ => by simp only [card_filter]
    have hper : ∀ w ∈ Qg, (((Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w).card : ℕ) : ℝ) ≤
        (n - 4 : ℕ) * ((n - 2 : ℕ) * σ) := by
      intro w hw
      obtain ⟨hwW, hwb, -⟩ := hQg w hw
      have hwa : w ≠ a := fun e => cx.a2 (by rw [← e]; exact hwb)
      have hpos : ∀ t ∈ R w, 0 < t := by
        intro t ht
        simp only [R, mem_insert, mem_image] at ht
        rcases ht with rfl | rfl | ⟨s, hs, rfl⟩
        · exact cx.ρ2pos
        · exact dist_pos.2 hwa
        · exact dist_pos.2 fun e => cx.notS hwW (e ▸ cx.sub hs)
      have hRc : (R w).card ≤ n - 2 := by
        have e1 := card_insert_le ρ2 (insert (dist w a) (S'.image (dist w)))
        have e2 := card_insert_le (dist w a) (S'.image (dist w))
        have e3 := card_image_le (s := S') (f := dist w)
        rw [cx.card] at e3
        have := cx.hn
        simp only [R]; omega
      have hs : (Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w) ⊆
          S'.biUnion fun s => W.filter fun x => dist x s ∈ R w := by
        intro x hx
        obtain ⟨hxP, s, hs, hm⟩ := mem_filter.1 hx
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hPg x hxP).1, hm⟩⟩
      have h1 := removal_bound' cx.conf cx.sub (R w) hpos
      rw [cx.card] at h1
      have h2 : ((R w).card : ℝ) ≤ (n - 2 : ℕ) := by exact_mod_cast hRc
      have h3 : ((n - 4 : ℕ) : ℝ) * ((R w).card * σ) ≤ (n - 4 : ℕ) * ((n - 2 : ℕ) * σ) := by gcongr
      exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)
    rw [hcount]; push_cast
    calc ∑ w ∈ Qg, (((Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w).card : ℕ) : ℝ)
        ≤ ∑ _w ∈ Qg, ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ) : ℝ) := sum_le_sum hper
      _ = Qg.card * ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ)) := by rw [sum_const, nsmul_eq_mul]
  have hCl2c : (Cl2.card : ℝ) ≤ Pg.card * ((n - 4 : ℕ) * (2 * σ)) := by
    have hcount : Cl2.card = ∑ x ∈ Pg,
        (Qg.filter fun w => ∃ s ∈ S', dist w s ∈ ({ρ1, dist x a} : Finset ℝ)).card := by
      rw [hCl2, card_filter, sum_product_right]
      exact sum_congr rfl fun x _ => by simp only [card_filter]
    have hper : ∀ x ∈ Pg, (((Qg.filter fun w => ∃ s ∈ S',
        dist w s ∈ ({ρ1, dist x a} : Finset ℝ)).card : ℕ) : ℝ) ≤ (n - 4 : ℕ) * (2 * σ) := by
      intro x hx
      obtain ⟨hxW, hxb, -⟩ := hPg x hx
      have hxa : x ≠ a := fun e => cx.a1 (by rw [← e]; exact hxb)
      have hpos : ∀ t ∈ ({ρ1, dist x a} : Finset ℝ), 0 < t := by
        intro t ht
        simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact cx.ρ1pos
        · exact dist_pos.2 hxa
      have hs : (Qg.filter fun w => ∃ s ∈ S', dist w s ∈ ({ρ1, dist x a} : Finset ℝ)) ⊆
          S'.biUnion fun s => W.filter fun w => dist w s ∈ ({ρ1, dist x a} : Finset ℝ) := by
        intro w hw
        obtain ⟨hwQ, s, hs, hm⟩ := mem_filter.1 hw
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hQg w hwQ).1, hm⟩⟩
      have h1 := removal_bound' cx.conf cx.sub ({ρ1, dist x a} : Finset ℝ) hpos
      rw [cx.card] at h1
      have h2 : (({ρ1, dist x a} : Finset ℝ).card : ℝ) ≤ 2 := by exact_mod_cast card_le_two
      have h3 : ((n - 4 : ℕ) : ℝ) * ((({ρ1, dist x a} : Finset ℝ).card : ℝ) * σ) ≤
          (n - 4 : ℕ) * (2 * σ) := by gcongr
      exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)
    rw [hcount]; push_cast
    calc ∑ x ∈ Pg, (((Qg.filter fun w => ∃ s ∈ S',
          dist w s ∈ ({ρ1, dist x a} : Finset ℝ)).card : ℕ) : ℝ)
        ≤ ∑ _x ∈ Pg, ((n - 4 : ℕ) * (2 * σ) : ℝ) := sum_le_sum hper
      _ = Pg.card * ((n - 4 : ℕ) * (2 * σ)) := by rw [sum_const, nsmul_eq_mul]
  have htot : ((((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
      dist q.1 a ≠ dist q.2 a).card : ℕ) : ℝ) ≤
      (((Qg ×ˢ Pg).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) +
        Cl1.card + Cl2.card := by
    have e1 := card_le_card hsub
    have e2 := card_union_le (((Qg ×ˢ Pg).filter fun q =>
      Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1) Cl2
    have e3 := card_union_le ((Qg ×ˢ Pg).filter fun q =>
      Disjoint (labels T q.1) (labels T q.2)) Cl1
    have : ((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
        dist q.1 a ≠ dist q.2 a).card ≤ ((Qg ×ˢ Pg).filter fun q =>
          Disjoint (labels T q.1) (labels T q.2)).card + Cl1.card + Cl2.card := by omega
    exact_mod_cast this
  -- numerics: `(n-4)(n-2) ≤ n²` and `2(n-4) ≤ n²`
  have hn1 : ((n - 4 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) ≤ n ^ 2 := by
    have : (n - 4) * (n - 2) ≤ n ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    exact_mod_cast this
  have hn2 : ((n - 4 : ℕ) : ℝ) * 2 ≤ n ^ 2 := by
    have : (n - 4) * 2 ≤ n ^ 2 := by
      rw [sq]
      have h2 : 2 * n ≤ n * n := Nat.mul_le_mul_right n (by have := cx.hn; omega)
      omega
    exact_mod_cast this
  have hP0 : (0 : ℝ) ≤ Pg.card := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ Qg.card := Nat.cast_nonneg _
  have e1 : (Qg.card : ℝ) * ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ)) ≤ Qg.card * (n ^ 2 * σ) := by
    apply mul_le_mul_of_nonneg_left _ hQ0
    have := mul_le_mul_of_nonneg_right hn1 hσ0
    linarith [show ((n - 4 : ℕ) : ℝ) * ((n - 2 : ℕ) * σ) = (n - 4 : ℕ) * (n - 2 : ℕ) * σ by ring]
  have e2 : (Pg.card : ℝ) * ((n - 4 : ℕ) * (2 * σ)) ≤ Pg.card * (n ^ 2 * σ) := by
    apply mul_le_mul_of_nonneg_left _ hP0
    have := mul_le_mul_of_nonneg_right hn2 hσ0
    linarith [show ((n - 4 : ℕ) : ℝ) * (2 * σ) = (n - 4 : ℕ) * 2 * σ by ring]
  have e3 : (((Qg ×ˢ Pg).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) ≤
      4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) * (Pg.card + Qg.card) := hLD
  nlinarith

end StepA

end E1088
