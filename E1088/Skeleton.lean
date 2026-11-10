import E1088.Lemma11
import E1088.G1
import E1088.Konig

/-!
# The halving step split into the paper's named results

Manuscript numbering (e1088/manuscript): Definition 6.1–6.3 (parameters, configurations, Claim),
Lemma 6.4 (HR_r = round14 Lemma 1.1, `lemma_HR`, PROVED), Lemma 6.6 (kill step = round14
Lemma 1.2 = the step of round12 "Theorem R", `lemma_1_2`, PROVED), Theorem 7.1 (Theorem R⁺: base level
`claim_top` PROVED from G1, levels n-3, n-4 `theorem_Rplus_low_proved` in RplusLow.lean PROVED), Definition 8.1 (rainbow families), Theorem 8.2 (Core Lemma,
`core_lemma_proved` in CoreFinal.lean, PROVED), Lemma 9.1 (Slicing Lemma, `slicing_lemma_proved` in Slicing1–4.lean, PROVED), Theorem 9.2 (E1_r,
`theorem_E1_proved` in E1Proof/E1Final.lean, PROVED from Core + Slicing), Theorem 10.1 (all Claims, assembly, `all_claims`, PROVED from the above),
Theorem 10.3 (Main Theorem via the halving step, `halving_step`, PROVED from the above) and the case `n = 3`
(E1088/N3.lean, proved via G1; Blokhuis's theorem is not used).

Global setting (`Ambient`): a finite rainbow-`n`-free `X ⊆ ℝ^d` of affine dimension `≤ D`, and `h`
bounding every subset of `X` of affine dimension `≤ ⌊D/2⌋` (in the paper `h = s_n(⌊D/2⌋)`).

Deviation from the manuscript (harmless): the loss `2^{L_k(D+2)}` of Theorem LR is our
`LRcost k (D+2)`, and `k*` is replaced by the larger `kstar n = 6^n + 2n^2`, so our `σ_min` is
at least the paper's.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped EuclideanGeometry

namespace E1088

variable {d : ℕ}

/-- The global setting of manuscript Sections 6–10. -/
structure Ambient (n D h : ℕ) (X : Finset (ℝ^d)) : Prop where
  free : RainbowFree n X
  dim : affDim X ≤ D
  half : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h

/-- An upper bound for the paper's `k*` (manuscript Definition 6.1: `k* ≤ 6^{n-4} + 2n²`). -/
def kstar (n : ℕ) : ℕ := 6 ^ n + 2 * n ^ 2

/-- `σ_min = 2^{L* + 2 + 2n} (h + 1)` (manuscript Definition 6.2). -/
noncomputable def smin (n D h : ℕ) : ℝ := 4 ^ (n + 1) * LRcost (kstar n) (D + 2) * (h + 1)

theorem one_le_smin (n D h : ℕ) : 1 ≤ smin n D h := by
  unfold smin
  have h1 : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have h2 := one_le_LRcost (kstar n) (D + 2)
  have h3 : (1 : ℝ) ≤ h + 1 := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  have := mul_le_mul h1 h2 zero_le_one (by linarith)
  nlinarith

/-- Class counts `K_r = 12 · 6^{n-5-r}` (manuscript Definition 6.1). -/
def Kr (n r : ℕ) : ℕ := 12 * 6 ^ (n - 5 - r)

/-! ### Rainbow families (manuscript Definition 8.1) -/

/-- A rainbow family at level `r` for the configuration `(S, W)`: centres `B`, index set
`I ⊆ ℕ`, classes `C k ⊆ W` and labels `β k b = |x b|` for `x ∈ C k` (conditions F1–F5). -/
structure RainbowFamily (S W : Finset (ℝ^d)) (B : Finset (ℝ^d)) (I : Finset ℕ)
    (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) : Prop where
  Bne : B.Nonempty
  F1 : Disjoint S B ∧ Rainbow (S ∪ B)
  Cne : ∀ k ∈ I, (C k).Nonempty ∧ C k ⊆ W
  F2 : ∀ k ∈ I, ∀ x ∈ C k, ∀ b ∈ B, dist x b = β k b
  F3 : (∀ k ∈ I, ∀ k' ∈ I, ∀ b ∈ B, ∀ b' ∈ B, β k b = β k' b' → k = k' ∧ b = b') ∧
    ∀ k ∈ I, ∀ b ∈ B, β k b ∉ dists (S ∪ B)
  F4 : ∀ k ∈ I, ∀ x ∈ C k, x ∉ S ∪ B ∧ Rainbow (insert x (S ∪ B))
  F5 : ∀ k ∈ I, ∀ x ∈ C k, ∀ s ∈ S, ∀ k' ∈ I, ∀ b ∈ B, dist x s ≠ β k' b

/-! ### Type counts (manuscript Definition 6.1) -/

/-- `k_c(r) = k₃(w₁) + k₄(w₁)` with `w₁ = (n-2) + C(n-2,2) + (n-4-r)`. -/
def kc (n r : ℕ) : ℕ :=
  let w1 := (n - 2) + (n - 2).choose 2 + (n - 4 - r)
  (w1 + 1 + r) + (w1 + 2 * r + r.choose 2)

/-- `k_sl = 3K - 1 + C(r+p, 2) + 2p + 2r`. -/
def ksl (r p K : ℕ) : ℕ := 3 * K - 1 + (r + p).choose 2 + 2 * p + 2 * r

/-! ### The named results -/

end E1088
