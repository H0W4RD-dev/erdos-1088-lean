# Erdős Problem #1088 in Lean 4: f_d(n) = 2^{o(d)}

This is a complete Lean 4 formalization of a positive answer to Erdős Problem #1088
(JSP-000905). For every fixed n ≥ 3, f_d(n) ≤ n · 2^{C_n √d log₂(d+2)}. In particular
log₂ f_d(n) = o(d).

Here f_d(n) is the least m such that every set of m points in ℝ^d contains n points whose
pairwise distances are all distinct.

> **Review status.** Lean's kernel checks the formal proof against the verbatim formal-conjectures
> statement, with only the standard axioms. **No human expert has reviewed the informal mathematical
> argument yet.** Both the proof and the formalization were produced with AI assistance; see
> [Authorship and AI assistance](#authorship-and-ai-assistance).

## Target theorem

`Erdos1088.erdos_1088` in [`E1088/Final.lean`](E1088/Final.lean):

```lean
theorem erdos_1088 :
    ∀ n ≥ 3,
      (fun d : ℕ ↦ Real.logb 2 (f d n : ℝ)) =o[atTop] (fun d : ℕ ↦ (d : ℝ))
```

The statement and its definitions are copied character for character from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
at commit `c77fdd446d23539302aa73bcfae4a9fa962b8382`. The copied files are:

- `FormalConjectures/ErdosProblems/1088.lean`: `PairwiseDistancesDistinct`,
  `HasSubsetWithDistinctDistances`, `cardSet`, `f` and `erdos_1088`.
- `FormalConjecturesForMathlib/Geometry/Metric.lean`: `distanceSet` and `distinctDistances`.
- `FormalConjecturesForMathlib/Geometry/Euclidean.lean`: the notation `ℝ^d`.

The copies sit in [`E1088/Statement/Erdos1088.lean`](E1088/Statement/Erdos1088.lean) and
`E1088/Final.lean`, between `BEGIN VERBATIM` / `END VERBATIM` markers. Raw upstream copies are
in [`upstream/`](upstream/), obtained with `git show <commit>:<path>`.

Two kinds of line are dropped:
- module-system headers (`module`, `public import`, `@[expose] public section`);
- the metadata attributes `@[category …]` and `@[AMS …]`.

`f_isLeast` is not copied, because `erdos_1088` does not use it.

[`scripts/check_statement.py`](scripts/check_statement.py) checks that every verbatim block
occurs exactly in the upstream file.

**Non-vacuity.** `f d n` is defined as `sInf (cardSet d n)`, which Lean sets to 0 when
`cardSet d n` is empty. The proof does not rely on that convention.
`E1088.erdos_1088_of_halving` in [`E1088/Main.lean`](E1088/Main.lean) constructs an explicit
element of `cardSet d n` and proves `f d n ≤ n · 2^{C √d log₂(d+2)}`.

## Toolchain

Both pins are identical to formal-conjectures at the commit above.

- Lean: `leanprover/lean4:v4.33.1` ([`lean-toolchain`](lean-toolchain)).
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474` ([`lakefile.toml`](lakefile.toml) and
  [`lake-manifest.json`](lake-manifest.json)).

## Reproduce

```bash
lake exe cache get        # download Mathlib build cache
lake build                # builds all of E1088 (target: E1088/Final.lean)
lake env lean scripts/AuditMain.lean
python scripts/check_statement.py
```

Expected output of `scripts/AuditMain.lean`:

```
'Erdos1088.erdos_1088' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/Audit.lean` prints the axioms for the main intermediate results too. Reference logs from
the development machine are in [`logs/`](logs/).

The source contains no `sorry`, `admit`, `axiom` declarations, `native_decide`,
`implemented_by`, `extern` or custom notation or macros beyond the copied `ℝ^d` notation.

## Proof outline and file map

The formalization follows the accompanying manuscript.

| Manuscript | Lean |
|---|---|
| Rank tools, Lemma H, Hadamard-product rank bound | `Rank.lean`, `AffRank.lean` |
| Gavinsky–Lovett cleaning lemma | `GL.lean` |
| Theorem LR (normal form, rescaling, margin rounding, induction) | `Refine.lean`, `LRBasic.lean`, `NF.lean`, `Cut.lean`, `Round.lean`, `LR.lean`, `LRMain.lean`, `LRBound.lean` |
| Lemma R inputs: γ₂-type factorization (Kiefer–Wolfowitz optimal design); Sheppard's formula | `JohnFactor.lean`, `Sheppard.lean`, `LemmaR.lean` |
| Caro–Wei, kill step, orthogonal splits | `CaroWei.lean`, `KillStep.lean`, `Ortho.lean` |
| G1 (bipartite step via rainbow sets) | `G1.lean`, `G1Count.lean` |
| Levels, Lemma 1.1 (HR), Lemma 1.2 | `Levels.lean`, `Lemma11.lean`, `Lemma12.lean` |
| Theorem R⁺ | `Rplus.lean`, `TwoDist.lean`, `RplusA*.lean`, `RplusStep.lean`, `RplusLow.lean` |
| König's theorem, slicing lemma | `Konig.lean`, `Cover.lean`, `Slicing1–4.lean` |
| Core Lemma, E1 | `CoreBasic.lean`, `CoreStep*.lean`, `CoreFinal.lean`, `E1Proof.lean`, `E1Final.lean` |
| Halving step, recursion, asymptotics | `Skeleton.lean`, `N3.lean`, `Assembly.lean`, `Main.lean`, `Asymp.lean` |
| Target statement | `Statement/Erdos1088.lean`, `Final.lean` |

### Differences from the manuscript

None of these affects the theorem.

- **Theorem LR loss.** The formal loss is 2^{O(k)} · √r log r rather than O(k³) · √r log r,
  because the NF3 normalization step is replaced by a tournament argument. For fixed k the
  shape is the same.
- **Constants.** Some constants in the Core Lemma and Theorem R⁺ are larger. Step A is
  applied at 3 big radii instead of 2, and `kstar` is larger than the manuscript's k*.
- **John's theorem.** It is replaced by a factorization proved from the Kiefer–Wolfowitz
  optimal-design theorem, using the determinant lemma and the spectral theorem.
- **The case n = 3.** It is handled through G1 rather than by citing Blokhuis.

[`notes/DEVELOPMENT_NOTES.md`](notes/DEVELOPMENT_NOTES.md) is the historical development log.

## Paper

- [`paper/main.pdf`](paper/main.pdf) is the compiled manuscript; the LaTeX sources are in [`paper/`](paper/), with `main.tex` as the main file.
- [`paper/research_notes_compiled.pdf`](paper/research_notes_compiled.pdf) is the compiled
  research record from which the manuscript was assembled: the assembled proof, the appendices
  and the AI referee reports. It is a working document, not the manuscript.

## Authorship and AI assistance

**Authors:** Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer.

The mathematical argument, the manuscript and the Lean code were produced by AI agents (Claude,
Anthropic) in research sessions directed by Will Howe. Three independent AI referee passes checked
the informal argument. Lean's kernel then checked the full formalization. No human expert has
reviewed the informal argument yet. Section 13 of the manuscript has the full disclosure (Section 12 describes the Lean formalization).

## License

Copyright 2026 Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer. Licensed under the
[Apache License, Version 2.0](LICENSE), the same license formal-conjectures uses.

## Third-party material

The files in `upstream/` and the verbatim blocks in `E1088/Statement/Erdos1088.lean` and
`E1088/Final.lean` come from google-deepmind/formal-conjectures. Copyright 2025–2026 The Formal
Conjectures Authors, licensed under the Apache License, Version 2.0.
