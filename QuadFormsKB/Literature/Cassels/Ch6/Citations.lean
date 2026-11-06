/-
# Cassels, Chapter 6: citations for declarations elsewhere in the library

Declarations outside `Literature/Cassels/Ch6/` that state items of Cassels' Chapter 6 (*Quadratic forms over the
rationals*, pp. 75–101) by other proofs, and carried no Cassels tag for these items yet. The tags are added with
`attribute [kb …]`, so the files where the declarations live are unchanged. Each locator says how the declaration differs from Cassels' item.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain
import QuadFormsKB.Literature.Classical.DavenportCassels
import QuadFormsKB.Literature.Classical.SumsOfSquares
import QuadFormsKB.Witt.Represents
import Mathlib.Combinatorics.Configuration
import QuadFormsKB.Literature.Cassels.Ch6.Sec4

namespace QuadFormsKB

/-! ### §11: Corollary 2 to Theorem 11.1 -/

attribute [kb "cassels1978" "Ch. 6, Cor. 2 to Thm. 11.1, p. 94 (the Weak Hasse Principle; proved from the strong principle and the local classification, not through the Witt group)"]
  isometric_iff_everywhere

/-! ### Notes (6.r3) -/

attribute [kb "cassels1978" "Ch. 6, Notes, p. 96 (the Strong Hasse Principle over a number field; O'Meara's and Lam's proofs)"]
  hasseMinkowski_nf
attribute [kb "cassels1978" "Ch. 6, Notes, p. 96 (n = 3 is equivalent to the norm theorem for quadratic extensions: the norm theorem)"]
  HasseNorm.hilbert_eq_one_of_everywhere
attribute [kb "cassels1978" "Ch. 6, Notes, p. 96 (the Strong Hasse Principle over a number field for n = 3, from the norm theorem)"]
  HMNF.hasseMinkowski_three_nf

/-! ### Example 6 -/

attribute [kb "cassels1978" "Ch. 6, Ex. 6, p. 100 (c is a sum of n integral squares iff of n rational squares, n ≤ 3; Davenport–Cassels descent instead of Aubry's method)"]
  DavenportCassels.sum_sq_int_of_rat
attribute [kb "cassels1978" "Ch. 6, Ex. 6, p. 100 (every positive integer is a sum of four squares; Mathlib's proof)"]
  Grosswald.lagrange_four_squares
attribute [kb "cassels1978" "Ch. 6, Ex. 6, p. 100 (when c is a sum of two integral squares; Mathlib's criterion)"]
  Grosswald.two_squares_iff
attribute [kb "cassels1978" "Ch. 6, Ex. 6, p. 100 (when c is a sum of three integral squares; Legendre's criterion)"]
  Grosswald.legendre_three_squares

/-! ### §1: proof of Corollary 2 to Theorem 1.1 (6.p1) -/

attribute [kb "cassels1978" "Ch. 6, §1, proof of Cor. 2 to Thm. 1.1, p. 76 (f represents e iff f ⊥ ⟨−e⟩ is isotropic; Ch. 2, Lemma 2.3)"]
  QuadForm.representsIn_iff_isotropicIn_orthSum

/-! ### §10: finite projective planes (6.r12)

Cassels' definition (p. 91): points and lines with an incidence relation, two distinct points on exactly one line, two
distinct lines through exactly one point (and a non-degeneracy condition); its order $n$: every line has $n + 1$ points
and every point lies on $n + 1$ lines, so there are $n^2 + n + 1$ points and lines. Mathlib's
`Configuration.ProjectivePlane` is this definition (used by `Cassels.Ch6.bruck_ryser`). -/

attribute [kb "cassels1978" "Ch. 6, §10, p. 91 (definition: finite projective plane)"] Configuration.ProjectivePlane
attribute [kb "cassels1978" "Ch. 6, §10, p. 91 (definition: the order n of a finite projective plane)"]
  Configuration.ProjectivePlane.order
attribute [kb "cassels1978" "Ch. 6, §10, p. 91 (every line has n + 1 points)"] Configuration.ProjectivePlane.pointCount_eq
attribute [kb "cassels1978" "Ch. 6, §10, p. 91 (every point lies on n + 1 lines)"] Configuration.ProjectivePlane.lineCount_eq
attribute [kb "cassels1978" "Ch. 6, §10, p. 91 (there are n² + n + 1 points)"] Configuration.ProjectivePlane.card_points

/-! ### §4: proof of Theorem 4.1 (6.p4) -/

-- 6.p4: the congruences (4.7), (4.8) define a lattice of index 4|a₁a₂a₃| on which g ≡ 0 (mod 4|a₁a₂a₃|); Ch. 5,
-- Thm. 2.3 applied to the ellipsoid |a₁|x₁² + |a₂|x₂² + |a₃|x₃² < 4|a₁a₂a₃| gives the zero. This is the proof of
-- `Cassels.Ch6.legendre_small_zero`.
attribute [kb "cassels1978" "Ch. 6, §4, proof of Thm. 4.1, pp. 80–81 (the lattice of index 4|a₁a₂a₃| and Minkowski's Thm. 2.3 for the ellipsoid)"]
  Cassels.Ch6.legendre_small_zero

end QuadFormsKB
