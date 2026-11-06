/-
# Conway–Sloane, Ch. 15: citations for declarations elsewhere in the library

Declarations outside `Literature/ConwaySloane/` that state items of Conway–Sloane's Chapter 15 but carried no
Conway–Sloane tag. The tags are added with
`attribute [kb …]`, so the files where the declarations live are unchanged. Each locator says how the declaration
differs from the book's item.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Witt.Cancellation
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Lattices.SAVectorsAnisotropic
import QuadFormsKB.Lattices.SpinorGenusCount
import QuadFormsKB.Literature.Cassels.Ch11Examples
import QuadFormsKB.Literature.Cassels.Ch8.Automorphs
import QuadFormsKB.Literature.Cassels.Ch8.CanonicalExists
import QuadFormsKB.Literature.Cassels.Ch8.Dyadic
import QuadFormsKB.Literature.Cassels.Ch14.GenusCosets
import QuadFormsKB.Literature.Cassels.Ch14.Ambiguous
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Literature.Cassels.Ch6.Sec7
import QuadFormsKB.Literature.Cassels.Ch12.LemmaOneTwo
import QuadFormsKB.Literature.Cassels.Ch12.Sec1
import QuadFormsKB.Literature.Cassels.Ch12.Bridge
import QuadFormsKB.Literature.Cassels.Ch12.Sec5
import QuadFormsKB.Literature.Cassels.Ch3.Basic

namespace QuadFormsKB

/-! ### §2 -/

attribute [kb "conwaysloane1999" "Ch. 15, §2.1, p. 355 (integral as a symmetric bilinear form = classically integral)"]
  IsClassicallyIntegral

attribute [kb "conwaysloane1999" "Ch. 15, §2.2, (4), p. 356 (integral equivalence, det M = ±1; on the quadratic form)"]
  Siegel.IntEquiv

/-! ### §3 -/

attribute [kb "conwaysloane1999" "Ch. 15, §3.4, p. 364 (composition: the group of proper classes; Dirichlet's composition)"]
  Composition.FormClass.instCommGroup

attribute [kb "conwaysloane1999" "Ch. 15, §3.4, p. 366 (improperly equivalent forms lie in the inverse class; ambiguous forms)"]
  Composition.isAmbiguous_iff_improper

attribute [kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (same genus iff the quotient is a square in the class group)"]
  Composition.sameGenus_iff_exists_sq

/-! ### §4 -/

attribute [kb "conwaysloane1999" "Ch. 15, §4.1, p. 367 (product formula for the p-adic metrics, p including −1)"]
  Cassels.product_formula

attribute [kb "conwaysloane1999" "Ch. 15, §4.4, Thm. 2, pp. 369–370 (p odd: diagonalization over ℤ_p, in canonical form)"]
  Cassels.exists_canonical

attribute [kb "conwaysloane1999" "Ch. 15, §4.4, Thm. 2, pp. 369–370 (p = 2: blocks 2^e·u x², 2^e·2xy, 2^e(2x²+2xy+2y²))"]
  Cassels.exists_dyadic_decomp

/-! ### §§5–6 -/

attribute [kb "conwaysloane1999" "Ch. 15, §5.1, Thm. 4, p. 372 (weak Hasse principle)"]
  isometric_iff_everywhere

attribute [kb "conwaysloane1999" "Ch. 15, §5.2, Thm. 5, p. 372 (existence of a rational form with prescribed local forms; Hasse invariants in place of p-excesses)"]
  Cassels.Ch6.exists_form_of_local

attribute [kb "conwaysloane1999" "Ch. 15, §6.2, Thm. 6, p. 376 (Witt cancellation)"]
  QuadraticForm.equivalent_of_prod_equivalent_prod

/-! ### §§7, 9 -/

attribute [kb "conwaysloane1999" "Ch. 15, §7, p. 378 (genus: ℤ_p-equivalent for all p including −1)"]
  Siegel.SameGenus

attribute [kb "conwaysloane1999" "Ch. 15, §9.1, Thm. 14, p. 388 (Eichler; over number fields, for the full orthogonal group)"]
  Lattices.eichler_spinorGenus_eq_class_uncond

attribute [kb "conwaysloane1999" "Ch. 15, §9.1, p. 389 (the spinor genera in a genus form a principal homogeneous set of a group of exponent 2)"]
  Lattices.spinorGeneraEquivQuot

attribute [kb "conwaysloane1999" "Ch. 15, §9.5, Remark, p. 391 (p odd: integral automorphisms are products of integral reflections)"]
  Cassels.intAut_eq_prod_tau

/-! ### §§10–11 -/

attribute [kb "conwaysloane1999" "Ch. 15, §10.1, (45), p. 396 (Minkowski reduced)"]
  Reduction.IsMinkowskiReduced

attribute [kb "conwaysloane1999" "Ch. 15, §10.1, (46), p. 396"]
  Reduction.IsMinkowskiReduced.diag_mono

attribute [kb "conwaysloane1999" "Ch. 15, §10.1, p. 396 (finitely many of the inequalities suffice)"]
  Reduction.thm_1_3

attribute [kb "conwaysloane1999" "Ch. 15, §10.1, p. 397 (Minkowski: for n ≤ 4, test vectors with coefficients 0, ±1)"]
  Reduction.lemma_1_2

attribute [kb "conwaysloane1999" "Ch. 15, §10.1, p. 397 (finitely many classes of given determinant)"]
  Reduction.finite_intEquiv_isMinkowskiReduced

attribute [kb "conwaysloane1999" "Ch. 15, §11, pp. 403–404 (the Dickson–Ross forms are equivalent)"]
  Siegel.ex2_properIntEquiv

end QuadFormsKB
