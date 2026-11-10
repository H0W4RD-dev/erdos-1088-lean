> Development log kept during the formalisation (historical; file names and statuses below reflect the time of writing). "roundNN" refers to the informal research notes compiled in the accompanying proof document.

# lean1088 status (live notes)

Project: lean1088 (Lake, Lean v4.33.1, Mathlib 0df444a3 = formal-conjectures c77fdd44 revision).
Build note (Windows): if the full project path is long, build through a short directory junction,
because paths over 260 characters make Lean fail to open .olean files.

## Files
- E1088/Rank.lean   : rank factorisation, (HP) rank(A⊙B) <= rank A * rank B, rank_add, iterated HP,
                      rank [|p_i-q_j|^2 - f_i - g_j] <= D+2, Lemma H (matrix + kill-polynomial forms). PROVED.
- E1088/GL.lean     : Gavinsky-Lovett cleaning lemma on finset rectangles. PROVED.
- E1088/Refine.lean : median, Lemma A, Lemma B. PROVED.
- E1088/LRBasic.lean: type functions, gap lemma (Lemma A+B), pair step, pairwise processing (NF1, NF2). PROVED.
- E1088/NF.lean     : compare_basic, tournament (NF3 with factor 16^k, see deviation note). PROVED.
- E1088/Cut.lean    : sorted cut with margins (Lemma NF assembled). PROVED.
- E1088/LemmaR.lean : Lemma R (margin rounding). SORRY (John + Sheppard not in Mathlib).
- E1088/Round.lean  : rescaling rank <= r+2, HP for prod (M - tau_t). PROVED.
- E1088/LR.lean     : round_core (Lemma R + GL). PROVED modulo lemmaR.
- E1088/LRMain.lean : lr_round, theoremLR (induction). PROVED modulo lemmaR.
- logs/build_02.log, logs/axioms_01.log: clean build; only lemmaR-dependent theorems use sorryAx.

## Deviations / findings so far
1. NF3 (dominant gap within factor 16, independent of k) is replaced by a tournament: factor 16^(k-1),
   so K = 32 k 16^k instead of 256 (k-1). Loss per round O(16^k k sqrt r log r) instead of
   O(k^2 sqrt r log r). Shape 2^{-O_k(sqrt r log r)} unchanged (k fixed). The paper's NF3 sketch
   ("split rows by which row-type Q_j is largest ...") was not formalised.
2. Lemma B does not need E >= 0 (hypothesis unused in the proof).
3. Coincident types: handled exactly as the paper says (delete one of two types that agree on the
   rectangle); Lean confirms "minority = support of H" once all pairs are strictly ordered.

## Update (later in session)
- LemmaR.lean now PROVES lemmaR from two isolated sorries: `john_factor` (John/γ₂ factorisation)
  and `sheppard` (Sheppard's formula for stdGaussian). The product measure of T Gaussian cuts,
  first-moment argument and choice of outcome are formal.
- LRBound.lean: LRcost k r <= 2^{C_k sqrt(r+2) log2(r+2)}. PROVED.
- CaroWei.lean, KillStep.lean (Lemma H + Caro-Wei kill step), Ortho.lean (OR), AffRank.lean
  (rank <= D+2 for affine dimension D). PROVED.
- Statement/Erdos1088.lean + Main.lean: verbatim upstream statement; erdos_1088 proved from
  `halving_step` (SORRY) via the solved recursion and asymptotics (PROVED).
- Levels.lean / Lemma12.lean: rainbow sets, configurations, Claim(j), Lemma 1.2 (in progress).

## Notes on the upstream statement
- `f d n = sInf (cardSet d n)` is 0 when `cardSet d n = ∅`, so `erdos_1088` alone does not certify
  finiteness of f_d(n). Our proof does not use this: it shows `max n ⌊2^{E(d)}⌋ ∈ cardSet d n`.

## Final state (build_05.log, axioms_04.log)
- `lake build`: 8727 jobs, success; exactly 3 `sorry`s: `john_factor`, `sheppard` (LemmaR.lean),
  `halving_step` (Main.lean).
- 47 theorems audited; every theorem not depending on those three uses only
  propext, Classical.choice, Quot.sound.
- Lemma 1.2 (round14) PROVED (`lemma_1_2`), with rainbow test `rainbow_insert_insert`.
- Statement check: scripts/check_statement.py, 14 verbatim runs ALL MATCH (negative test detects
  a one-character change).

## Stage 3 (Sheppard, König, G1, decomposition of the halving step)

Source for the paper statements: e1088/manuscript/*.tex (the round*/ .md notes are no longer on disk).

Milestones and logs:
- build_06 / axioms_05: Sheppard's formula PROVED (E1088/Sheppard.lean: 2D reduction by extending
  {u, w} to an orthonormal basis, product marginal of stdGaussian, sector measure in polar
  coordinates). `sheppard` in LemmaR.lean is no longer a sorry.
- build_07 / axioms_06: halving step split into named results (E1088/Skeleton.lean); König,
  G1 (bipartite), Lemma 1.1 (HR), E1_r (from Core + Slicing), all-Claims assembly and the halving
  step itself PROVED; erdos_1088 moved to E1088/Final.lean (verbatim block rechecked).
- build_08 / axioms_07: G1 counting forms (a), (c) and the base level Claim(n-2) of Theorem R⁺
  PROVED; R⁺ sorry reduced to levels n-3, n-4.

Named results (manuscript numbering):
| result | Lean | status |
|---|---|---|
| Lemma 5.1 label lemma | G1.lean `label_lemma` | proved |
| Thm 5.2 G1 bipartite | G1.lean `G1_bip` | proved (uses Theorem LR, hence `john_factor`) |
| Cor 5.3 (a), (c) | G1Count.lean `G1_count`, `G1_degree` | proved |
| König (Thm 3.9) | Konig.lean `konig_cover` | proved |
| Lemma 6.4 HR_r (round14 L1.1) | Lemma11.lean `lemma_HR` | proved |
| Lemma 6.6 kill step (round12 "Theorem R" step, round14 L1.2) | Lemma12.lean `lemma_1_2` | proved |
| Thm 7.1 R⁺, level n-2 | Rplus.lean `claim_top` | proved |
| Thm 7.1 R⁺, levels n-3, n-4 | Skeleton.lean `theorem_Rplus_low` | SORRY |
| Thm 8.2 Core Lemma | Skeleton.lean `core_lemma` | SORRY |
| Lemma 9.1 Slicing Lemma | Skeleton.lean `slicing_lemma` | SORRY |
| Thm 9.2 E1_r | E1Proof.lean, E1Final.lean `theorem_E1_proved` | proved from Core + Slicing |
| Thm 10.1 all Claims | Assembly.lean `all_claims` | proved |
| Thm 10.3 halving step / Main Theorem | Assembly.lean `halving_step` | proved |
| Blokhuis (n = 3) | Skeleton.lean `blokhuis` | SORRY (cited classical result) |
| John's theorem (factorisation form) | LemmaR.lean `john_factor` | SORRY (not in Mathlib) |

Remaining sorries: john_factor, theorem_Rplus_low, core_lemma, slicing_lemma, blokhuis.

Paper vs Lean (this stage): no mathematical error found. Notes:
- G1 / Lemma typeOR: the manuscript assumes "points of T are not in Q" for the bisector case; Lean
  shows this is not needed (`ortho_of_bisector` has no such hypothesis).
- G1 (c): Lean gets `3|Y| ≤ 4·4^{n-2}μ` (pairs with x = w are counted among label-sharing pairs since
  labels are nonempty), slightly stronger than the manuscript's `|Y| ≤ (4/3)(4^{n-2}μ+1)`.
- The kill step and HR need `σ > 0`, `Γ ≥ 0`; the manuscript has these (σ > 0 in Def 6.2,
  Γ_j ≥ 1 in Def 6.3), round14 had them only implicitly.
- E1_r: the Slicing Lemma hypothesis `k_sl ≤ k*` is discharged with our `kstar n = 6^n + 2n²`
  (`ksl_le_kstar`); the manuscript's `k* ≤ 6^{n-4} + 2n²` would also do.
- Our `σ_min = 4^{n+1} LRcost(k*, D+2) (h+1)` plays the role of `2^{L*+2+2n}(h+1)`.
- Final state of stage 3: build_08 (8738 jobs, OK), axioms_07 (73 theorems; sorryAx only through
  the 5 sorries below; all others propext/Classical.choice/Quot.sound), statement check ALL MATCH.
- Lines: 5258 Lean lines in E1088/ (≈2000 added this stage: Sheppard 317, Konig 121, G1 179,
  G1Count 256, Lemma11 107, Skeleton 125, E1Proof 211, E1Final 261, Assembly 261, Rplus 145,
  Final 35, plus edits to Main/LemmaR).
- Remaining sorries: john_factor (LemmaR), theorem_Rplus_low, core_lemma, slicing_lemma,
  blokhuis (Skeleton).

## PAUSED (2026-11-10, user request: "pause all claude work on this pc")
The Lean agent was stopped mid-stage while it was writing a reusable GL+LR+OR covering lemma for the Skeleton.lean sorries.
- Last verified clean build: logs/build_08.log. Later files may be mid-edit and are unverified; rebuild before trusting them.
- Remaining sorries at the last clean build: john_factor, theorem_Rplus_low, core_lemma, slicing_lemma, blokhuis.
- Planned order on resume: blokhuis, slicing_lemma, core_lemma, theorem_Rplus_low, then john_factor last.
- Update at pause: the source now shows only 3 sorries (john_factor, theorem_Rplus_low, core_lemma), so blokhuis and slicing_lemma appear to be done. This is NOT verified: build_10 was cut off when the agent stopped. Run a clean `lake build` and the axiom audit first on resume.

## Stage 4 (resumed 2026-11-10)
### Milestone 1: clean build verified (build_12.log, axioms_11.log)
- `lake build` OK (8744 jobs). `declaration uses sorry` only at LemmaR:42 (`john_factor`),
  Skeleton:89 (`theorem_Rplus_low`), Skeleton:95 (`core_lemma`).
- blokhuis is gone (n = 3 now handled by N3.lean `card_le_n3`, proved via G1); `slicing_lemma_proved`
  (Slicing1–4, Cover) has no sorry of its own. In axioms_11 its sorryAx comes only through
  `gl_lr_or` → Theorem LR → `john_factor`.
- `#print axioms Erdos1088.erdos_1088`: [propext, sorryAx, Classical.choice, Quot.sound];
  statement check: 14 verbatim runs ALL MATCH.
- Statement fix (my omission, not a paper error): Definition 8.1 has `B ⊆ X`. `RainbowFamily` does not
  include it, so `core_lemma` now takes `hBX : B ⊆ X`, and `iterate_families` (E1Final) carries
  the invariant `B ⊆ X`. It is needed so that `T = S ∪ B ∪ {a₁,a₂} ⊆ X` in G1.
- Core Lemma work in progress (not yet imported by E1088.lean): CoreBasic, CoreStep0, CoreStep12,
  CoreStep34, CoreStep5, CoreFinal.

### Milestone 2: Core Lemma proved (`core_lemma_proved`, CoreFinal.lean)
Files: CoreBasic (rainbow_insert_one, family restriction, `gl_lr_or_avg`), CoreStep0 (Step 0),
CoreStep12 (Steps 1–2, `G1_pairs`), CoreStep34 (`gl_lr_or_sets`, `gl_lr_or_avg_sets`, Steps 3–4 and
Corollary 8.10 as `core_cor34`), CoreStep5 (`Ty`, Lemma 8.11 direction used, `beta_disjoint`,
`cov_shape`, `pair_count`), CoreFinal (constants and the final rectangle). `E1Final` now calls
`core_lemma_proved`; the Skeleton `core_lemma` sorry is deleted.
Deviations from the manuscript (constants only; the hypothesis `M ≥ M_core` is unchanged):
- θ_w(j) = |C_j|/(32Γ'E^{k4(w)}) + σ instead of max(θ_rel|C_j|, σ);
- ε = 1/(3072 Γ' E^{k_c}), δ₁ = 1/(512 Γ' E^{k_c}) (paper: ε from k3(w2)+k4(w2), δ₁ from μ and M);
  Step 1 is proved for any δ₁ ≥ 2·4^{n-2}μ/(εM) + 3n²σ/M, and this δ₁ satisfies it.
- Step 5 counts via |I| = 12 exactly (restriction), Good+Cov ≥ 6 per valid pair, as in the paper.
- k* is our `kstar n`; all type counts used are ≤ k_c ≤ kstar (`kc_le_kstar`).
No gap found in Sections 8 (all steps went through as written, modulo constants).

### Milestone 3: Theorem R⁺ levels n-3, n-4 proved (`theorem_Rplus_low_proved`, RplusLow.lean)
Files: TwoDist (Lemma 7.2 in counting form, `two_dist`), RplusA/RplusA2/RplusA3 (Step A: Steps 1–5,
`stepA`), RplusStep (`rplus_step` = the kill step `lemma_1_2` with K = 2 and Step A for points with
≥ 3 big radii), RplusLow (two applications from `claim_top`; `theorem_Rplus_proved` combines all
three levels; Assembly uses it). Skeleton `theorem_Rplus_low` and Rplus `theorem_Rplus` deleted.
Deviations (constants/presentation only):
- Q = 2^27 n² E^{5k'}, branch threshold θ = 2^22 n² E^{4k'} σ (paper: Q = 2^44 n⁴ E^{8k'},
  θ = Q^{1/2}σ); two-distribution lemma stated with η = κ⁴, κ = 1/(32E^{k'}) ≤ 1/2.
- Step A is applied when |Big_b(Qσ)| ≥ 3 (paper: ≥ 2), using the first two big radii; points with
  |Big_b| ≤ 2 have both big spheres in the kill polynomial and are handled as in Lemma 6.6 (K = 2).
  This is equivalent for the bound.
- The S2 count uses n²σ instead of n(n-4)σ.
- Γ_j = (D+2)^{c} with c = 4n² + 2·cAdd(n) (paper: explicit P⁺_j(2QΓ_{j+1}+...)); only the
  polynomial-in-(D+2) form is used downstream.
No gap found in Section 7.

### Remaining: `john_factor` (LemmaR.lean) — plan, not started
Needed bound: γ₂(N) ≤ √s · max|N| (only √s, not s, keeps the halving exponent o(d); the
Auerbach/max-determinant basis argument gives only s and would not suffice).
Planned proof without John's ellipsoid (D-optimal design, Kiefer–Wolfowitz):
1. factor N = Σ_k a_k(x) b_k(w) with r = rank ≤ s and the rows a_x spanning ℝ^r
   (basis of the column space, `Matrix.rank_eq_finrank_span_cols`);
2. maximise det(Σ_x λ_x a_x a_xᵀ) over the standard simplex (compact, continuous), M := optimum,
   det M > 0;
3. first-order optimality via the matrix determinant lemma
   (`Matrix.det_add_replicateCol_mul_replicateRow`) and Bernoulli: a_xᵀ M⁻¹ a_x ≤ r;
4. M = PᵀP (`posSemidef` factorisation), u_x := P⁻ᵀ a_x, v_w := P b_w:
   ‖u_x‖² = a_xᵀM⁻¹a_x ≤ r, ‖v_w‖² = Σ λ_x N_xw² ≤ K², ⟨u_x, v_w⟩ = N_xw;
5. rescale by r^{±1/4} and embed ℝ^r ⊆ ℝ^s.

### Verified (build_13.log, axioms_12.log)
`lake build` OK (8756 jobs); the only `declaration uses sorry` is LemmaR:42 `john_factor`.
In axioms_12 every sorryAx (incl. `core_lemma_proved`, `theorem_Rplus_low_proved`, `stepA`) comes
through Theorem LR → `john_factor`; `two_dist` is axiom-clean. Statement check ALL MATCH.

### Milestone 4: `john_factor` proved (JohnFactor.lean, `john_factor_proved`)
D-optimal design route as planned: `rank_factor` (factor through a basis of the column space,
rows spanning), `kw_design` (maximise det of the design matrix on the compact simplex; first-order
optimality from `det_add_replicateCol_mul_replicateRow` + Bernoulli in `kw_scalar`, giving
a_iᵀM⁻¹a_i ≤ r), `pd_factor` (M = U diag(e) Uᵀ from the spectral theorem; L = diag(e^{-1/2})Uᵀ,
R = diag(e^{1/2})Uᵀ), `embR` (ℝ^r ⊆ ℝ^s), rescaling by r^{±1/4}.
Statement fix (my statement error, not the paper's): `john_factor` now assumes `0 ≤ K`. Without it
the old statement was false (X = ∅, Y ≠ ∅, K < 0 forces ‖v_w‖ ≤ K s^{1/4} < 0). Its only use,
in `lemmaR`, has K ≥ 1/2.

## FINAL (build_14.log, axioms_13.log)
Clean build (`rm -rf .lake/build` of this package, then `lake build`): OK, 8757 jobs, no
`declaration uses sorry`. `#print axioms Erdos1088.erdos_1088`: [propext, Classical.choice,
Quot.sound]; all 92 audited declarations are sorryAx-free. check_statement.py: 14 verbatim runs
ALL MATCH. No sorry remains. No gap was found in the paper; all deviations are listed above
(constants, the n = 3 route via G1 instead of Blokhuis, `kstar`, `B ⊆ X` in the Core statement,
`0 ≤ K` in `john_factor`).
