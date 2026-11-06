import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch2.Exercises
import Mathlib.NumberTheory.Pell
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Cassels, Chapter 13: citations of declarations elsewhere, and the form $f_{2,2}$

Items of Cassels, *Rational Quadratic Forms* (1978), Chapter 13, that are used in the chapter's formalization or
recalled by Cassels from earlier chapters, but carried no Chapter 13 tag. The tags are added with `attribute [kb …]`,
so the files where the declarations live are unchanged.

* §3, (3.9)–(3.10), p. 290: primitive, properly primitive and improperly primitive binary forms are the special case
  $n = 2$ of Cassels' Ch. 9 definitions `Siegel.IsPrimitiveCI`, `Siegel.IsProperlyPrimitive`,
  `Siegel.IsImproperlyPrimitive` (`Literature/Cassels/Ch9Sec1.lean`).
* §3, p. 292: the fundamental solution of Pell's equation is *Mathlib*'s `Pell.IsFundamental`.
* §4, footnote, p. 299: for $n$ odd a proper automorph fixes a nonzero vector (Ch. 2, Ex. 9), `Cassels.Ch2Ex.ex9`.
* §6, (6.1)–(6.3), p. 304: the diagonalization of a rational form, *Mathlib*'s
  `QuadraticForm.equivalent_weightedSumSquares`.
* §9, (9.10)–(9.11), p. 318: the form $f_{2,2}$ is the determinant of the matrix $X$ (`det_X_f22`).
-/

open Matrix

namespace QuadFormsKB

attribute [kb "cassels1978" "Ch. 13, §3, (3.9), p. 290 (primitive binary form; n-ary form of Ch. 9)"] Siegel.IsPrimitiveCI
attribute [kb "cassels1978" "Ch. 13, §3, (3.10), p. 290 (properly primitive binary form; n-ary form of Ch. 9)"]
  Siegel.IsProperlyPrimitive
attribute [kb "cassels1978" "Ch. 13, §3, p. 290 (improperly primitive binary form; n-ary form of Ch. 9)"]
  Siegel.IsImproperlyPrimitive
attribute [kb "cassels1978" "Ch. 13, §3, p. 292 (the fundamental solution of Pell's equation)"] Pell.IsFundamental
attribute [kb "cassels1978" "Ch. 13, §4, footnote, p. 299 (n odd, T proper: Tb = b for some b ≠ 0; Ch. 2, Ex. 9)"]
  Cassels.Ch2Ex.ex9
attribute [kb "cassels1978" "Ch. 13, §6, (6.1)–(6.3), p. 304 (diagonalization; variant: every field of characteristic ≠ 2)"]
  QuadraticForm.equivalent_weightedSumSquares

namespace Reduction

/-- **The form $f_{2,2}$ as a determinant** (Cassels, Ch. 13, §9, (9.10)–(9.11), p. 318): for real
$x_0, x_1, x_2, x_3$ (Cassels' $x_1, \dots, x_4$, shifted to $0$-based indices), the matrix
$X = \begin{pmatrix} x_0 + x_2 & x_3 + x_1 \\ x_3 - x_1 & x_0 - x_2 \end{pmatrix}$ has
$\det X = f_{2,2}(\vec x) = x_0^2 + x_1^2 - x_2^2 - x_3^2$. So the automorphs $X \mapsto AXB$ of `det_mul_mul_eq`
(with $\det A = \det B = 1$) are automorphs of $f_{2,2}$. -/
@[kb "cassels1978" "Ch. 13, §9, (9.10)–(9.11), p. 318"]
theorem det_X_f22 (x : Fin 4 → ℝ) :
    !![x 0 + x 2, x 3 + x 1; x 3 - x 1, x 0 - x 2].det = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 := by
  rw [Matrix.det_fin_two_of]; ring

end Reduction

end QuadFormsKB
