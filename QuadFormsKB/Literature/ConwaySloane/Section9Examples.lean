/-
# Conway–Sloane, Ch. 15, §9.7: the binary example of determinant $-17$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, p. 396
(`conwaysloane1999`).

**Erratum.** The book says that the forms $\begin{pmatrix}2&3\\3&-4\end{pmatrix}$ and
$\begin{pmatrix}-2&3\\3&4\end{pmatrix}$ "are in distinct classes although both belong to the genus
$\mathrm{II}_{1,1}(17)$" (justifying $d_0(2) = 17$ in Cor. 22). They are in the **same** class, even properly:
with $M = \begin{pmatrix}1&-4\\2&-7\end{pmatrix}$, $\det M = 1$, $M^{\mathsf T}\begin{pmatrix}2&3\\3&-4\end{pmatrix}M
= \begin{pmatrix}-2&3\\3&4\end{pmatrix}$ (the first form takes the value $-2$ at $(1, 2)$).

**Proves** `example17_congr`, `example17_intEquiv`.
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem11

namespace QuadFormsKB.ConwaySloane

open Matrix

/-- The congruence $M^{\mathsf T}AM = B$ for $A = \begin{pmatrix}2&3\\3&-4\end{pmatrix}$,
$B = \begin{pmatrix}-2&3\\3&4\end{pmatrix}$, $M = \begin{pmatrix}1&-4\\2&-7\end{pmatrix}$ ($\det M = 1$). -/
theorem example17_congr :
    (!![1, -4; 2, -7] : Matrix (Fin 2) (Fin 2) ℤ)ᵀ * !![2, 3; 3, -4] * !![1, -4; 2, -7] = !![-2, 3; 3, 4] ∧
      (!![1, -4; 2, -7] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.det_fin_two]

/-- **Erratum to Conway–Sloane, §9.7, p. 396**: the binary forms $\begin{pmatrix}2&3\\3&-4\end{pmatrix}$ and
$\begin{pmatrix}-2&3\\3&4\end{pmatrix}$ of the genus $\mathrm{II}_{1,1}(17)$ are integrally equivalent (printed:
"in distinct classes"). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, p. 396 (the two binary forms of determinant -17; erratum: they are equivalent)"]
theorem example17_intEquiv :
    Siegel.IntEquiv (Cassels.Ch8Ex2.gramForm (!![2, 3; 3, -4] : Matrix (Fin 2) (Fin 2) ℤ))
      (Cassels.Ch8Ex2.gramForm !![-2, 3; 3, 4]) := by
  rw [Siegel.IntEquiv, isometricGL_gramForm_iff (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl)]
  have hu : IsUnit (!![1, -4; 2, -7] : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [example17_congr.2]; exact isUnit_one
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr hu |>.unit, example17_congr.1⟩

end QuadFormsKB.ConwaySloane
