import E1088.Assembly

/-!
# The target statement `Erdos1088.erdos_1088` (verbatim from formal-conjectures c77fdd44)

Proved from `E1088.halving_step` (E1088/Assembly.lean), with no `sorry` anywhere in the
development (see `#print axioms Erdos1088.erdos_1088` in logs/axioms_*.log).
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos1088

open scoped EuclideanGeometry

-- BEGIN VERBATIM erdos_1088 statement (upstream 1088.lean; proof replaced)
/--
Let $f_d(n)$ be the minimal $m$ such that any set of $m$ points in $\mathbb{R}^d$ contains a set of
$n$ points for which any two determined distances are distinct. Erdős Problem 1088 asks to
estimate $f_d(n)$. In particular, is it true that, for every fixed $n \geq 3$,
$$
f_d(n) = 2^{o(d)}
$$
as $d \to \infty$?

The little-$o$ condition is stated after taking the base-$2$ logarithm.
-/
theorem erdos_1088 :
    ∀ n ≥ 3,
      (fun d : ℕ ↦ Real.logb 2 (f d n : ℝ)) =o[atTop] (fun d : ℕ ↦ (d : ℝ)) := by
-- END VERBATIM erdos_1088 statement
  exact E1088.erdos_1088_of_halving E1088.halving_step

end Erdos1088
