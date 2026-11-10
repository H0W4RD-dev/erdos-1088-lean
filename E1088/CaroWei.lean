import Mathlib

/-!
# Caro–Wei (tool CW)

For a finite vertex set `s` of a simple graph there is an independent `t ⊆ s` with
`∑_{v ∈ s} 1/(deg_s v + 1) ≤ |t|`; consequently `|s|² ≤ |t| · ∑_{v∈s} (deg_s v + 1)`, i.e.
`|t| ≥ |s|/(d̄ + 1)` for the average degree `d̄` (the form used in round12/01 Theorem R and in the
slicing lemma of round14).
-/

open Finset

namespace E1088

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Degree of `v` inside `s`. -/
def degIn (s : Finset V) (v : V) : ℕ := #(s.filter (G.Adj v))

theorem degIn_mono {s s' : Finset V} (h : s' ⊆ s) (v : V) : degIn G s' v ≤ degIn G s v :=
  card_le_card (filter_subset_filter _ h)

/-- **Caro–Wei**, harmonic form. -/
theorem caro_wei_harmonic : ∀ (s : Finset V), ∃ t ⊆ s, (t : Set V).Pairwise (fun a b => ¬ G.Adj a b) ∧
    ∑ v ∈ s, (1 : ℝ) / (degIn G s v + 1) ≤ #t := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, subset_refl _, by simp, by simp⟩
    obtain ⟨v, hv, hmin⟩ := exists_min_image s (degIn G s) hne
    set Nv := s.filter (G.Adj v) with hNv
    set s' := s \ insert v Nv with hs'
    have hsub : s' ⊂ s := by
      refine ⟨sdiff_subset, fun h => ?_⟩
      have := h hv
      simp [hs'] at this
    obtain ⟨t', ht's, hind, hsum⟩ := ih s' hsub
    have hvt' : v ∉ t' := fun h => by
      have := ht's h; simp [hs'] at this
    refine ⟨insert v t', insert_subset hv (ht's.trans sdiff_subset), ?_, ?_⟩
    · rw [coe_insert]
      refine hind.insert fun b hb hvb => ?_
      have hb' := ht's hb
      simp only [hs', mem_sdiff, mem_insert, hNv, mem_filter, not_or, not_and] at hb'
      constructor
      · intro hadj; exact hb'.2.2 hb'.1 hadj
      · intro hadj; exact hb'.2.2 hb'.1 (G.adj_symm hadj)
    · rw [card_insert_of_notMem hvt', Nat.cast_add, Nat.cast_one]
      have hsplit : s = insert v Nv ∪ s' := by
        rw [hs', union_sdiff_of_subset (insert_subset hv (filter_subset _ _))]
      have hdisj : Disjoint (insert v Nv) s' := disjoint_sdiff
      rw [hsplit, sum_union hdisj]
      rw [← hsplit]
      have hvN : v ∉ Nv := fun h => G.loopless.irrefl v (mem_filter.1 h).2
      have h1 : ∑ u ∈ insert v Nv, (1 : ℝ) / (degIn G s u + 1) ≤ 1 := by
        calc ∑ u ∈ insert v Nv, (1 : ℝ) / (degIn G s u + 1)
            ≤ ∑ _u ∈ insert v Nv, (1 : ℝ) / (degIn G s v + 1) := by
              refine sum_le_sum fun u hu => ?_
              have hus : u ∈ s := by
                rcases mem_insert.1 hu with rfl | hu
                · exact hv
                · exact (mem_filter.1 hu).1
              apply one_div_le_one_div_of_le (by positivity)
              have := hmin u hus
              exact_mod_cast Nat.add_le_add_right this 1
          _ = 1 := by
              rw [sum_const, card_insert_of_notMem hvN, nsmul_eq_mul]
              have : (degIn G s v : ℝ) = #Nv := rfl
              rw [this]; push_cast
              exact mul_one_div_cancel (Nat.cast_add_one_ne_zero _)
      have h2 : ∑ u ∈ s', (1 : ℝ) / (degIn G s u + 1) ≤
          ∑ u ∈ s', (1 : ℝ) / (degIn G s' u + 1) := by
        refine sum_le_sum fun u _ => ?_
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (degIn_mono G sdiff_subset u) 1
      linarith

/-- **Caro–Wei**, average-degree form: `|s|² ≤ |t| · ∑_{v ∈ s} (deg_s v + 1)`. -/
theorem caro_wei (s : Finset V) : ∃ t ⊆ s, (t : Set V).Pairwise (fun a b => ¬ G.Adj a b) ∧
    ((#s : ℝ)) ^ 2 ≤ #t * ∑ v ∈ s, ((degIn G s v : ℝ) + 1) := by
  obtain ⟨t, hts, hind, hsum⟩ := caro_wei_harmonic G s
  refine ⟨t, hts, hind, ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpos : 0 < ∑ v ∈ s, ((degIn G s v : ℝ) + 1) :=
    sum_pos (fun v _ => by positivity) hne
  have hCS := sq_sum_div_le_sum_sq_div s (fun _ => (1 : ℝ))
    (g := fun v => (degIn G s v : ℝ) + 1) (fun v _ => by positivity)
  simp only [sum_const, nsmul_eq_mul, mul_one, one_pow] at hCS
  have : (#s : ℝ) ^ 2 / ∑ v ∈ s, ((degIn G s v : ℝ) + 1) ≤ #t := hCS.trans hsum
  rwa [div_le_iff₀ hpos] at this

end E1088
