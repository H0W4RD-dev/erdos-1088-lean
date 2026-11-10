import Mathlib

/-!
# Erdős Problem 1088: verbatim copy of the formal statement

Copied from google-deepmind/formal-conjectures at commit c77fdd446d23539302aa73bcfae4a9fa962b8382
(raw copies in `upstream/`, obtained with `git show <commit>:<path>`):
* `FormalConjecturesForMathlib/Geometry/Euclidean.lean` (notation `ℝ^n`),
* `FormalConjecturesForMathlib/Geometry/Metric.lean` (`distanceSet`, `distinctDistances`),
* `FormalConjectures/ErdosProblems/1088.lean` (namespace `Erdos1088`).

Only the module headers (`module`, `public import`, `@[expose] public section`) and the metadata
attributes `@[category ...]`, `@[AMS ...]` (from FormalConjecturesUtil) are dropped; the
declarations are copied character for character. `scripts/check_statement.py` verifies this.
`f_isLeast` (an API lemma, `sorry` upstream) is not copied: `erdos_1088` does not use it.
`erdos_1088` itself is NOT stated here with a proof; see `E1088/Main.lean`.
-/

-- BEGIN VERBATIM Euclidean.lean
scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
-- END VERBATIM Euclidean.lean

-- BEGIN VERBATIM Metric.lean
open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/--
Given a finite set of points in a metric space, we define the number of distinct distances
between pairs of points.
-/
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)
-- END VERBATIM Metric.lean

-- BEGIN VERBATIM 1088.lean
open Filter
open scoped EuclideanGeometry

namespace Erdos1088

variable {d : ℕ}

/-- A finite set of points has all pairwise distances distinct. -/
def PairwiseDistancesDistinct (A : Finset (ℝ^d)) : Prop :=
  distinctDistances A = Nat.choose A.card 2

/-- The finite set `S` contains an `n`-point subset with all pairwise distances distinct. -/
def HasSubsetWithDistinctDistances (n : ℕ) (S : Finset (ℝ^d)) : Prop :=
  ∃ A : Finset (ℝ^d), A ⊆ S ∧ A.card = n ∧ PairwiseDistancesDistinct A

/--
The set of cardinalities `m` such that every `m`-point subset of `ℝ^d` contains an `n`-point
subset with all pairwise distances distinct.
-/
def cardSet (d n : ℕ) : Set ℕ :=
  { m | n ≤ m ∧ ∀ S : Finset (ℝ^d), S.card = m → HasSubsetWithDistinctDistances n S }

/--
The least `m` such that every `m`-point subset of `ℝ^d` contains an `n`-point subset with all
pairwise distances distinct.
-/
noncomputable def f (d n : ℕ) : ℕ := sInf (cardSet d n)

-- END VERBATIM 1088.lean

end Erdos1088
