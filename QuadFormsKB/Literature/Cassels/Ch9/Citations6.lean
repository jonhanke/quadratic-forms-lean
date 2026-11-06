/-
# Cassels, Chapter 9: citations for running-text items

Declarations elsewhere in the library that state items of Cassels' Chapter 9 (*Integral forms over the rational
integers*, pp. 127–168) which had no citation tag yet. The tags are added with `attribute [kb …]`, so the files where the declarations
live are unchanged. Each locator says how the declaration relates to Cassels' item.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.Cassels.Ch9Sec5Squares
import QuadFormsKB.Literature.Cassels.Ch9Sec5Exist
import QuadFormsKB.Literature.Cassels.Ch13.Sec3
import QuadFormsKB.Literature.Classical.SumsOfSquares
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Binary.GenusClassGroup
import QuadFormsKB.Binary.GenusMass

namespace QuadFormsKB

/-! ### §1, §2: notation -/

attribute [kb "cassels1978" "Ch. 9, §1, p. 127 (the determinant d(f) = det(f_ij) of f = Σ f_ij x_i x_j; here det H / 2^n)"]
  Siegel.gramDet
attribute [kb "cassels1978" "Ch. 9, §2, p. 133 (notation ‖b‖_p = max_j |b_j|_p, written entrywise)"]
  Siegel.exists_basis_approx
attribute [kb "cassels1978" "Ch. 9, §7, p. 155 (the groups O_A(f), O_A⁺(f) of A-integral automorphs, for A = ℤ)"]
  Siegel.Aut
attribute [kb "cassels1978" "Ch. 9, §7, p. 155 (the groups O_A(f), O_A⁺(f) of A-integral automorphs, for A = ℤ)"]
  Siegel.AutPlus

/-! ### §1: genera and representations -/

attribute [kb "cassels1978" "Ch. 9, §1, p. 129 (x² − 82y² and 2x² − 41y² are in the same genus but not equivalent; proved in Ch. 13, §3)"]
  Reduction.sameGenus_not_intEquiv_82
attribute [kb "cassels1978" "Ch. 9, §1, p. 130 (Thm. 1.3 for a genus of one class: every positive integer is a sum of four squares)"]
  Grosswald.lagrange_four_squares

/-! ### §4, §5 -/

attribute [kb "cassels1978" "Ch. 9, Lemma 4.1, Note, p. 139 (one may speak of the determinant of a genus)"]
  Siegel.SameGenus.hessian_det_eq
attribute [kb "cassels1978" "Ch. 9, §5, p. 141 (only one ℤ_p-class of forms of determinant d for p ∤ 2d, by Ch. 8, Cor. to Thm. 3.1)"]
  Siegel.Kneser.isometricGL_of_unimodular
attribute [kb "cassels1978" "Ch. 9, §5, p. 142 (proof route of θ_n: strong Hasse principle, Witt cancellation, completing the square, Lemma 4.2, Chinese remainder theorem)"]
  Siegel.casselsTheta
attribute [kb "cassels1978" "Ch. 9, §5, p. 144 (for (i) only ℤ_2 and the ℤ_p with p ∣ a need be considered)"]
  Siegel.primRep_sumSq_two_iff
attribute [kb "cassels1978" "Ch. 9, §5, p. 144 (for (ii) only ℤ_2 need be considered)"]
  Siegel.primRep_sumSq_three_iff

/-! ### §6 -/

attribute [kb "cassels1978" "Ch. 9, Lemma 6.4, Note 1, p. 150 (every genus of primitive binary forms has the same number of classes; special case: fundamental D < 0, from the class group interface)"]
  Binary.IsFormClassGroup.card_classes_in_genus
attribute [kb "cassels1978" "Ch. 9, Lemma 6.4, Note 1, p. 150 (every genus of positive definite binary forms of discriminant D has the same mass)"]
  Binary.mass_genus

end QuadFormsKB
