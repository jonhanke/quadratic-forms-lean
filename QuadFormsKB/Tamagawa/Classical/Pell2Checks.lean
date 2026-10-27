/-
# Classical special cases over $\mathbb Q$: numerical check of the values of $x_0^2-2x_1^2$

**Layer:** $\mathbb Z$ (finite computation, kernel `decide`).

An independent check, for $1\le m\le 100$, of the criterion `pell2_value_iff` (`Pell2Values.lean`; it checks the
formula, not the proof): $m = x_0^2 - 2x_1^2$ has a solution in the box $0\le x_0\le 14$, $0\le x_1\le 7$ iff every prime
$q\equiv3,5\pmod8$ divides $m$ to an even power. The box suffices: for $m>0$ some solution has
$0\le x_1\le\sqrt{m/2}\le7$ (reduce by the unit $3+2\sqrt2$), hence $x_0^2 = m + 2x_1^2\le198$.
-/
import Mathlib

namespace QuadFormsKB.Tamagawa.Classical.Checks

set_option maxRecDepth 100000 in
/-- **The values of $x_0^2-2x_1^2$, numerically**, $1\le m\le 100$: a solution in the box $[0,14]\times[0,7]$ exists iff
every prime $q\equiv3,5\pmod8$ divides $m$ to an even power. -/
theorem checks_pell2_values : ∀ m ∈ Finset.Icc 1 100,
    (∃ x ∈ Finset.range 15, ∃ y ∈ Finset.range 8, x ^ 2 = m + 2 * y ^ 2) ↔
      ∀ q ∈ m.primeFactors, q % 8 = 3 ∨ q % 8 = 5 → Even (padicValNat q m) := by
  decide +kernel

end QuadFormsKB.Tamagawa.Classical.Checks
