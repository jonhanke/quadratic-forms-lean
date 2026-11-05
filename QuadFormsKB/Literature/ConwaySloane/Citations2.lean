/-
# Conway–Sloane, Ch. 15: more citations for declarations elsewhere in the library

Continuation of `Citations.lean`: tags (`attribute [kb …]`) on existing declarations, in the library and in Mathlib,
that state items of §§2–7 of Conway–Sloane's Chapter 15 and had no citation tag yet. Each locator says how the declaration relates to the book's item.
-/
import QuadFormsKB.Defs.Integral
import QuadFormsKB.Defs.Rational
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Literature.Cassels.Ch2.WittChain
import QuadFormsKB.Literature.Cassels.Ch4.ExamplesScan

namespace QuadFormsKB

/-! ### §2 -/

attribute [kb "conwaysloane1999" "Ch. 15, §2.1, (2), p. 354 (the form xAxᵗ of a symmetric integer matrix A)"]
  gramForm

attribute [kb "conwaysloane1999" "Ch. 15, §2.2, p. 355 (a lattice in a rational space: the ℤ-span of a basis; over a number field)"]
  Lattices.Lat

attribute [kb "conwaysloane1999" "Ch. 15, §2.2, p. 355 (a change of basis M gives the same lattice iff M⁻¹ is integral iff det M = ±1: an integer matrix is invertible over ℤ iff its determinant is a unit)"]
  Matrix.isUnit_iff_isUnit_det

/-! ### §4 -/

attribute [kb "conwaysloane1999" "Ch. 15, §4, pp. 366–367 (the primes −1, 2, 3, 5, …: the places of ℚ, −1 = the real place)"]
  RatPlace

attribute [kb "conwaysloane1999" "Ch. 15, §4.2, p. 367 (p odd: a rational integer prime to p that is a quadratic residue mod p is a p-adic square)"]
  Cassels.Ch4Scan.isSquare_odd_of_residue

attribute [kb "conwaysloane1999" "Ch. 15, §4.4, p. 369 (over a field of characteristic ≠ 2 every form diagonalizes)"]
  QuadraticForm.equivalent_weightedSumSquares

/-! ### §6 -/

attribute [kb "conwaysloane1999" "Ch. 15, §6.2, p. 375 (every equivalence of diagonal forms is a chain of binary equivalences: Witt's chain lemma)"]
  Cassels.exists_reflTransGen_normalBasis

attribute [kb "conwaysloane1999" "Ch. 15, §6.2, (18), p. 376 (the reflection x ↦ x − 2 f(x,r)/f(r,r) · r)"]
  Lattices.symm

attribute [kb "conwaysloane1999" "Ch. 15, §6.2, p. 376 (Sylvester's law of inertia); §7.1, p. 379 (p = −1: f = f₁ ⊕ (−1)f₋₁ with f_{±1} positive definite)"]
  QuadraticForm.equivalent_signType_weighted_sum_squared

end QuadFormsKB
