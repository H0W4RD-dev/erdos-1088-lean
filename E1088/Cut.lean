import E1088.NF

/-!
# Theorem LR, part 3: the cut (Lemma NF assembled)

After pairwise processing all types are strictly ordered with comparable gaps. We sort them,
pick a dominant consecutive gap by the tournament, and cut the types into a lower group `Lo`
and an upper group `Hi`. With `z = (τ_{i₀} + τ_{i₀+1})/2 = φ(x) + θ(w)` and the basic quantity
`σ = qr(x) qc(w)` of the dominant gap, every lower type satisfies `-Kσ ≤ τ - z ≤ -σ/2` and every
upper type `σ/2 ≤ τ - z ≤ Kσ`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace E1088

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

/-- Data of a cut of the types `S'` with margin constant `K` on `X × Y`. -/
def CutData (τ : ι → TF α β) (S' : Finset ι) (K : ℝ) (X : Finset α) (Y : Finset β) : Prop :=
  ∃ Lo Hi : Finset ι, Lo ∪ Hi = S' ∧ Disjoint Lo Hi ∧ Lo.Nonempty ∧ Hi.Nonempty ∧
  ∃ (φ : α → ℝ) (θ : β → ℝ) (qr : α → ℝ) (qc : β → ℝ),
    (∀ x ∈ X, 0 < qr x) ∧ (∀ w ∈ Y, 0 < qc w) ∧
    ∀ x ∈ X, ∀ w ∈ Y,
      (∀ t ∈ Lo, -(K * (qr x * qc w)) ≤ (τ t).eval x w - (φ x + θ w) ∧
          (τ t).eval x w - (φ x + θ w) ≤ -(qr x * qc w) / 2) ∧
      (∀ t ∈ Hi, (qr x * qc w) / 2 ≤ (τ t).eval x w - (φ x + θ w) ∧
          (τ t).eval x w - (φ x + θ w) ≤ K * (qr x * qc w))

/-- The cut, given pairwise good types. -/
theorem cut_of_good (τ : ι → TF α β) (S : Finset ι) (X : Finset α) (Y : Finset β)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hS : 2 ≤ #S)
    (hgood : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → PairGood τ t t' X Y) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 ^ #S * #X' ∧ #Y ≤ 4 ^ #S * #Y' ∧
      CutData τ S (32 * #S * 16 ^ #S) X' Y' := by
  classical
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨w0, hw0⟩ := hY
  set q := #S with hq
  set val : ι → ℝ := fun t => (τ t).eval x0 w0 with hval
  -- order transfer
  have transfer : ∀ t ∈ S, ∀ t' ∈ S, val t < val t' →
      ∀ x ∈ X, ∀ w ∈ Y, (τ t).eval x w < (τ t').eval x w := by
    intro t ht t' ht' hlt x hx w hw
    have hne : t ≠ t' := by rintro rfl; exact lt_irrefl _ hlt
    rcases (hgood t ht t' ht' hne).1 with h | h
    · have := h x0 hx0 w0 hw0; simp only [gap] at this; simp only [hval] at hlt; linarith
    · have := h x hx w hw; simp only [gap] at this; linarith
  have inj : Set.InjOn val S := by
    intro t ht t' ht' heq
    by_contra hne
    rcases (hgood t ht t' ht' hne).1 with h | h
    · have := h x0 hx0 w0 hw0; simp only [gap] at this; simp only [hval] at heq; linarith
    · have := h x0 hx0 w0 hw0; simp only [gap] at this; simp only [hval] at heq; linarith
  set V := S.image val with hV
  have hVc : #V = q := card_image_of_injOn inj
  set emb := V.orderEmbOfFin hVc with hemb
  have hch : ∀ i : Fin q, ∃ t ∈ S, val t = emb i := by
    intro i
    have := orderEmbOfFin_mem V hVc i
    obtain ⟨t, ht, h⟩ := mem_image.1 this
    exact ⟨t, ht, h⟩
  choose f hfS hfv using hch
  have hq0 : 0 < q := by omega
  let e : ℕ → ι := fun i => if h : i < q then f ⟨i, h⟩ else f ⟨0, hq0⟩
  have heS : ∀ i, e i ∈ S := by
    intro i; simp only [e]; split_ifs <;> exact hfS _
  have hev : ∀ i (h : i < q), val (e i) = emb ⟨i, h⟩ := by
    intro i h; simp only [e, dif_pos h]; exact hfv _
  have hmono : ∀ i j, i < j → j < q → val (e i) < val (e j) := by
    intro i j hij hj
    rw [hev i (by omega), hev j hj]
    exact emb.strictMono (Fin.mk_lt_mk.2 hij)
  have hsurj : ∀ t ∈ S, ∃ i < q, e i = t := by
    intro t ht
    have hmem : val t ∈ Set.range emb := by
      rw [hemb, range_orderEmbOfFin]; exact mem_coe.2 (mem_image_of_mem _ ht)
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i, i.2, inj (heS _) ht ?_⟩
    rw [hev i i.2]; exact hi
  have hle : ∀ i j, i ≤ j → j < q → ∀ x ∈ X, ∀ w ∈ Y,
      (τ (e i)).eval x w ≤ (τ (e j)).eval x w := by
    intro i j hij hj x hx w hw
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (transfer _ (heS i) _ (heS j) (hmono i j hlt hj) x hx w hw).le
  -- consecutive gaps and their basic quantities
  have hgap : ∀ i : ℕ, ∃ qr : α → ℝ, ∃ qc : β → ℝ, i < q - 1 →
      (∀ x ∈ X, 0 < qr x) ∧ (∀ w ∈ Y, 0 < qc w) ∧ ∀ x ∈ X, ∀ w ∈ Y,
        qr x * qc w ≤ gap τ (e (i + 1)) (e i) x w ∧
          gap τ (e (i + 1)) (e i) x w ≤ 32 * (qr x * qc w) := by
    intro i
    by_cases hi : i < q - 1
    · have hne : e (i + 1) ≠ e i := by
        intro h; have := hmono i (i + 1) (by omega) (by omega); rw [h] at this
        exact lt_irrefl _ this
      obtain ⟨qr, qc, h1, h2, h3⟩ := (hgood _ (heS _) _ (heS _) hne).2
      refine ⟨qr, qc, fun _ => ⟨h1, h2, fun x hx w hw => ?_⟩⟩
      have hpos : 0 < gap τ (e (i + 1)) (e i) x w := by
        have := transfer _ (heS i) _ (heS (i + 1)) (hmono i (i + 1) (by omega) (by omega))
          x hx w hw
        simp only [gap]; linarith
      have := h3 x hx w hw
      rwa [abs_of_pos hpos] at this
    · exact ⟨fun _ => 1, fun _ => 1, fun h => absurd h hi⟩
  choose qr qc hQ using hgap
  have hJ : (range (q - 1)).Nonempty := ⟨0, mem_range.2 (by omega)⟩
  obtain ⟨X', hX', Y', hY', c1, c2, i0, hi0, hdom⟩ := tournament qr qc (range (q - 1)) X Y
    ⟨w0, hw0⟩ hJ (fun j hj x hx => (hQ j (mem_range.1 hj)).1 x hx)
    (fun j hj w hw => (hQ j (mem_range.1 hj)).2.1 w hw)
  rw [card_range] at c1 c2 hdom
  have hi0q : i0 < q - 1 := mem_range.1 hi0
  have h4 : 4 ^ (q - 1) ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨X', hX', Y', hY', c1.trans (Nat.mul_le_mul_right _ h4),
    c2.trans (Nat.mul_le_mul_right _ h4), ?_⟩
  -- the cut
  refine ⟨(range (i0 + 1)).image e, (Ico (i0 + 1) q).image e, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← image_union, range_eq_Ico, Ico_union_Ico_eq_Ico (by omega) (by omega)]
    ext t
    simp only [mem_image, mem_Ico]
    constructor
    · rintro ⟨i, _, rfl⟩; exact heS i
    · intro ht; obtain ⟨i, hi, rfl⟩ := hsurj t ht; exact ⟨i, ⟨by omega, hi⟩, rfl⟩
  · rw [disjoint_left]
    intro t ht ht'
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ht
    obtain ⟨j, hj, hji⟩ := mem_image.1 ht'
    rw [mem_range] at hi; rw [mem_Ico] at hj
    have := hmono i j (by omega) hj.2
    rw [hji] at this; exact lt_irrefl _ this
  · exact ⟨e 0, mem_image.2 ⟨0, mem_range.2 (by omega), rfl⟩⟩
  · exact ⟨e (i0 + 1), mem_image.2 ⟨i0 + 1, mem_Ico.2 ⟨le_rfl, by omega⟩, rfl⟩⟩
  refine ⟨fun x => ((τ (e i0)).rp x + (τ (e (i0 + 1))).rp x) / 2,
    fun w => ((τ (e i0)).cp w + (τ (e (i0 + 1))).cp w) / 2, qr i0, qc i0,
    fun x hx => (hQ i0 hi0q).1 x (hX' hx), fun w hw => (hQ i0 hi0q).2.1 w (hY' hw), ?_⟩
  intro x hx w hw
  have hxX := hX' hx
  have hwY := hY' hw
  have hz : ((τ (e i0)).rp x + (τ (e (i0 + 1))).rp x) / 2 +
      ((τ (e i0)).cp w + (τ (e (i0 + 1))).cp w) / 2 =
      ((τ (e i0)).eval x w + (τ (e (i0 + 1))).eval x w) / 2 := by
    rw [TF.eval_eq, TF.eval_eq]; ring
  rw [hz]
  set σ := qr i0 x * qc i0 w with hσ
  have hσpos : 0 < σ := mul_pos ((hQ i0 hi0q).1 x hxX) ((hQ i0 hi0q).2.1 w hwY)
  have hg0 := ((hQ i0 hi0q).2.2 x hxX w hwY).1
  simp only [gap] at hg0
  -- spread bound
  have htel : (τ (e (q - 1))).eval x w - (τ (e 0)).eval x w =
      ∑ i ∈ range (q - 1), gap τ (e (i + 1)) (e i) x w := by
    simp only [gap]
    rw [sum_range_sub (fun i => (τ (e i)).eval x w)]
  have hspread : (τ (e (q - 1))).eval x w - (τ (e 0)).eval x w ≤ 32 * #S * 16 ^ #S * σ := by
    rw [htel]
    calc ∑ i ∈ range (q - 1), gap τ (e (i + 1)) (e i) x w
        ≤ ∑ _i ∈ range (q - 1), 32 * (16 ^ (q - 1) * σ) := by
          refine sum_le_sum fun i hi => ?_
          have h1 := ((hQ i (mem_range.1 hi)).2.2 x hxX w hwY).2
          have h2 := hdom i hi x hx w hw
          nlinarith
      _ = (q - 1 : ℕ) * (32 * (16 ^ (q - 1) * σ)) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ 32 * #S * 16 ^ #S * σ := by
          have a1 : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
          have a2 : (16 : ℝ) ^ (q - 1) ≤ 16 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
          have a3 : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          rw [← hq]
          have : ((q - 1 : ℕ) : ℝ) * 16 ^ (q - 1) ≤ q * 16 ^ q :=
            mul_le_mul a1 a2 (by positivity) (by positivity)
          nlinarith
  have hbot : ∀ j, j < q → (τ (e 0)).eval x w ≤ (τ (e j)).eval x w :=
    fun j hj => hle 0 j (Nat.zero_le _) hj x hxX w hwY
  have htop : ∀ j, j < q → (τ (e j)).eval x w ≤ (τ (e (q - 1))).eval x w :=
    fun j hj => hle j (q - 1) (by omega) (by omega) x hxX w hwY
  have hA := hbot i0 (by omega)
  have hB := htop (i0 + 1) (by omega)
  have hA' := htop i0 (by omega)
  have hB' := hbot (i0 + 1) (by omega)
  constructor
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
    rw [mem_range] at hj
    have h1 := hle j i0 (by omega) (by omega) x hxX w hwY
    have h2 := hbot j (by omega)
    constructor <;> linarith
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
    rw [mem_Ico] at hj
    have h1 := hle (i0 + 1) j hj.1 hj.2 x hxX w hwY
    have h2 := htop j hj.2
    constructor <;> linarith

end E1088
