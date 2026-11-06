/-
# Cassels, Chapter 14, §5: the case $r \equiv s \equiv -1 \pmod 4$ of quadratic reciprocity

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §5, pp. 344–345.

Cassels deduces this case of quadratic reciprocity from Theorem 5.1 (Gauss' second proof), using the forms
$[r, 0, -s]$ of discriminant $4rs$. Theorem 5.1 for general discriminants is not formalized here; the statement is
proved from Mathlib's quadratic reciprocity (`legendreSym.quadratic_reciprocity_three_mod_four`).
-/
import QuadFormsKB.Defs.QuadForm

namespace QuadFormsKB.Composition

/-- **Quadratic reciprocity for $r \equiv s \equiv -1 \pmod 4$** (Cassels, Ch. 14, (5.6)–(5.7), p. 344): *for distinct
primes $r \equiv s \equiv -1 \pmod 4$, $(r/s)(s/r) = -1$*, i.e. $(r/s) = -(s/r)$. Proved from Mathlib, not by Cassels'
argument through Theorem 5.1. -/
@[kb "cassels1978" "Ch. 14, §5, (5.6)–(5.7), pp. 344–345 (proved from Mathlib's quadratic reciprocity)"]
theorem legendreSym_mul_legendreSym_of_three_mod_four {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hrs : r ≠ s)
    (hr : r % 4 = 3) (hs : s % 4 = 3) : legendreSym s r * legendreSym r s = -1 := by
  rw [legendreSym.quadratic_reciprocity_three_mod_four hr hs, neg_mul, ← sq,
    legendreSym.sq_one r (a := (s : ℤ)) ?_]
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  exact hrs ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) (Fact.out : s.Prime)).mp (by exact_mod_cast h0))

end QuadFormsKB.Composition
