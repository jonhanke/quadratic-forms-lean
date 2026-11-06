/-
# Cassels, Chapters 2–4: citations for declarations elsewhere in the library

Declarations outside `Literature/Cassels/Ch2*`, `Ch3*`, `Ch4*` that state (variants of) items of Cassels' Chapters 2–4
of *Rational Quadratic Forms* (1978)
but carried no Cassels tag. The tags are added with `attribute [kb …]`, so the files where the declarations live are
unchanged. Each locator says how the declaration differs from Cassels' item.
-/
import QuadFormsKB.Defs.QuadForm
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Lattices.Basic
import QuadFormsKB.Lattices.Genus
import QuadFormsKB.Lattices.SAVectorsIsotropic
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Tamagawa.Reflection
import QuadFormsKB.Literature.Cassels.Ch2.WittGroup
import QuadFormsKB.Literature.OMeara.Sec91Units
import QuadFormsKB.Literature.OMeara.Sec43CD
import QuadFormsKB.Literature.HasseNorm.LocalIndexTwo
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

namespace QuadFormsKB

/-! ### Chapter 2: quadratic forms over a field -/

attribute [kb "cassels1978" "Ch. 2, §1, p. 12, (1.2) (the polar form of φ, stated without the factor ½: φ(u₁+u₂) − φ(u₁) − φ(u₂) = xᵀ(C+Cᵀ)y, over any algebra K)"]
  QuadForm.polar_eq_hessian
attribute [kb "cassels1978" "Ch. 2, §1, p. 12, (1.3)–(1.4) (a basis gives a form; this is the isometry of (V, Q) with the coordinate form, over a field F)"]
  Lattices.coordIsometry
attribute [kb "cassels1978" "Ch. 2, §1, p. 12, (1.4) (equivalence of forms, here lattices of a number field: L and M isometric by an element of GL_n(F))"]
  Lattices.IsIsometric
attribute [kb "cassels1978" "Ch. 2, §1, p. 12 (definition: regular; for a form over a ring R, det of the Hessian C + Cᵀ is nonzero, i.e. char ≠ 2)"]
  QuadForm.Nondegenerate
attribute [kb "cassels1978" "Ch. 2, §1, pp. 12–13 (determinant d(φ) of a regular space as an element of k^×, well defined modulo squares: isometric spaces have the same class in k^×/(k^×)²)"]
  Cassels.detU
attribute [kb "cassels1978" "Ch. 2, §1, pp. 12–13 (d(φ) ∈ k^×/(k^×)² is independent of the basis: equivalent forms have equal determinant modulo squares)"]
  Cassels.detU_eq_of_equivalent
attribute [kb "cassels1978" "Ch. 2, §1, pp. 12–13 (equality in k^×/(k^×)² for rationals d₁, d₂ viewed in a field K of characteristic 0: d₁ = t² d₂)"]
  SameSquareClass
attribute [kb "cassels1978" "Ch. 2, §2, p. 15 (definition: represents; Q represents c over K if Q(x) = c has a solution x ∈ Kⁿ, including c = 0)"]
  QuadForm.RepresentsIn
attribute [kb "cassels1978" "Ch. 2, §2, p. 15 (definition: isotropic; a nonzero zero over K; anisotropic is its negation)"]
  QuadForm.IsotropicIn
attribute [kb "cassels1978" "Ch. 2, §2, p. 15, (2.1) (the hyperbolic plane as a binary form over a number field F, with matrix of the form xy)"]
  Lattices.hypForm
attribute [kb "cassels1978" "Ch. 2, §2, p. 15, (2.1) (the hyperbolic plane, the form x₀x₁ on k²)"]
  Cassels.hypSpace
attribute [kb "cassels1978" "Ch. 2, §4, pp. 18–19 (definition: isometry/autometry; the group O(U) of autometries, here O(V) over a field F with 2 invertible, V finite-dimensional or not)"]
  OMeara.orth
attribute [kb "cassels1978" "Ch. 2, §4, pp. 18–19 (the group O(U) of autometries, as matrices in GL_n(R) preserving the form Q, for R an algebra over a number field F)"]
  Lattices.orthGroup
attribute [kb "cassels1978" "Ch. 2, §4, pp. 18–19 (definition: isometry; Q and Q' are isometric over a ring extension K, via P ∈ GL_n(K))"]
  QuadForm.IsometricIn
attribute [kb "cassels1978" "Ch. 2, §4, p. 19 (the proper autometries O⁺(U) = autometries of determinant 1, over a field with 2 invertible)"]
  OMeara.orthPlus
attribute [kb "cassels1978" "Ch. 2, §4, p. 19, (4.1)–(4.3) (the symmetry τ_v in an anisotropic vector v, as a linear automorphism of V over a field with 2 invertible)"]
  OMeara.symmetry
attribute [kb "cassels1978" "Ch. 2, §4, p. 19 (det τ_v = −1)"]
  OMeara.det_symmetry
attribute [kb "cassels1978" "Ch. 2, §4, p. 19, (4.1)–(4.3) (the symmetry τ_x in a vector x ∈ Kⁿ with Q(x) ≠ 0, as an element of O(Q)(K); identity if Q(x) = 0)"]
  Lattices.symm
attribute [kb "cassels1978" "Ch. 2, §4, p. 19 (det τ_v = −1, for the reflection matrix of a form over a domain A)"]
  QuadForm.det_reflMat

/-! ### Chapter 2, exercises -/

attribute [kb "cassels1978" "Ch. 2, Ex. 8, p. 30 (Cartan–Dieudonné: every autometry of a regular n-dimensional space is a product of at most n symmetries; over a field with 2 invertible, O'Meara's 43:3)"]
  OMeara.exists_symmetry_prod_eq_length_le

/-! ### Chapter 3: p-adic numbers -/

attribute [kb "cassels1978" "Ch. 3, Cor. to Lemma 1.7, p. 41 (a nondegenerate form over ℚ in n ≥ 5 variables is isotropic over ℚ_p)"]
  isotropic_padic_of_five_le
attribute [kb "cassels1978" "Ch. 3, Cor. to Lemma 1.7, p. 41 (a diagonal form with nonzero coefficients in 5 variables over ℚ_p is isotropic)"]
  PadicClass.padic_isotropic_five
attribute [kb "cassels1978" "Ch. 3, Cor. to Lemma 1.7, p. 41 (a diagonal form with nonzero coefficients in n ≥ 5 variables over a local Hilbert field K is isotropic)"]
  PadicClass.isotropic_of_five_le
attribute [kb "cassels1978" "Ch. 3, §2, pp. 41–42 (the Hilbert symbol (a,b) = 1 iff a x² + b y² = 1 is solvable; here over any field of characteristic ≠ 2, not the form a = z² − b y²)"]
  hilbertSymbol_eq_one_iff_conic
attribute [kb "cassels1978" "Ch. 3, §2, p. 42 (the a with (a,b) = 1 are the norms from the quadratic extension; here over a completion F_v of a number field, for b a nonsquare)"]
  HN.mem_range_norm_iff
attribute [kb "cassels1978" "Ch. 3, §2, p. 42 (the norm group of the quadratic extension has index 2 when b is not a square; here over a completion F_v of a number field)"]
  HN.index_norm_eq_two

/-! ### Chapter 3, exercises -/

attribute [kb "cassels1978" "Ch. 3, Ex. 11, p. 50 (the Hilbert symbol (p^u a, p^v b) for p odd and a, b units; the formula is stated with Legendre symbols rather than as a congruence mod p)"]
  HilbertLocal.hilbertSymbol_odd_formula

/-! ### Chapter 4: the Hasse–Minkowski theorem -/

attribute [kb "cassels1978" "Ch. 4, Cor. to Lemma 2.1, p. 57 (the Hasse invariant of a diagonal form depends only on its isometry class; stated for n variables, Cassels' case is n = 2 with (a₁, a₂))"]
  PadicClass.hasseVec_eq_of_isometric

end QuadFormsKB
