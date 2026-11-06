/-
# Conway–Sloane, Ch. 15: further citations

Continuation of `Citations2.lean`: tags (`attribute [kb …]`) on existing declarations, in the library and in Mathlib,
that state items of Chapter 15 and had no citation tag yet.
-/
import QuadFormsKB.Literature.Hanke2005.WittDiag
import QuadFormsKB.Literature.OMeara.Sec42Extra
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace QuadFormsKB

attribute [kb "conwaysloane1999" "Ch. 15, §2.2, p. 356 (isometric forms over a field have Gram determinants equal modulo nonzero squares: in every basis the determinant is c²·d with c ≠ 0; so the ratio of the determinants of rationally equivalent forms is a nonzero rational square)"]
  Hanke2005.SqDet.of_isometryEquiv

attribute [kb "conwaysloane1999" "Ch. 15, §4.1, p. 367 (a rational whose denominator is prime to p has p-adic norm ≤ 1, i.e. is a p-adic integer)"]
  Padic.norm_rat_le_one

attribute [kb "conwaysloane1999" "Ch. 15, §6.1, p. 375 (the isotropic form diag(A, −A), a hyperbolic plane, represents every number: Q(H) = F)"]
  OMeara.hyperbolic_universal

end QuadFormsKB
