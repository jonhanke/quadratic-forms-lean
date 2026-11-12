/-
# Kitaoka 1993, Section 5.2: Proposition 5.2.3 (ternary unimodular diagonal lattices over $\mathbb Z_2$)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.2, Proposition 5.2.3, pp. 78–79 (printed pages).

**Setting.** $p = 2$, $R = \mathbb Z_2$. A lattice with a basis is described by its Gram matrix $(B(v_i, v_j))$ for
Kitaoka's bilinear form $B$ with $B(x, x) = Q(x)$; $\langle \epsilon_1\rangle \perp \langle \epsilon_2\rangle \perp
\langle \epsilon_3\rangle$ is the diagonal Gram matrix $\mathrm{diag}(\epsilon_1, \epsilon_2, \epsilon_3)$, and two
lattices with Gram matrices $S$, $T$ are isometric when $T = {}^tP\,S\,P$ for some $P \in \mathrm{GL}_3(\mathbb Z_2)$
(that is, $\det P \in \mathbb Z_2^\times$).

**Defines** the statement `Proposition523` (stated).
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import QuadFormsKB.Citation

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

/-- **Kitaoka 1993, Proposition 5.2.3** (pp. 78–79), *stated*: let $p = 2$ and $\epsilon_1, \epsilon_2, \epsilon_3 \in
R^\times = \mathbb Z_2^\times$. Then
$$\langle \epsilon_1\rangle \perp \langle \epsilon_2\rangle \perp \langle \epsilon_3\rangle \cong
\begin{pmatrix} 2a & 1 \\ 1 & 2a \end{pmatrix} \perp \langle \epsilon\rangle$$
for some $\epsilon \in R^\times$ and $a = 0$ or $1$; if $a = 1$, then the binary lattice
$\begin{pmatrix} 2 & 1 \\ 1 & 2\end{pmatrix}$ is anisotropic, i.e. $Q(x, y) = 2x^2 + 2xy + 2y^2$ has no nontrivial zero
over $\mathbb Q_2$. The isometry is written with Gram matrices: ${}^tP\,\mathrm{diag}(\epsilon_1, \epsilon_2,
\epsilon_3)\,P$ equals the block matrix, for a matrix $P$ over $\mathbb Z_2$ with unit determinant. -/
@[kb "kitaoka1993" "§5.2, Prop. 5.2.3, p. 78"]
def Proposition523 : Prop :=
  ∀ ε : Fin 3 → ℤ_[2], (∀ i, IsUnit (ε i)) →
    ∃ (e a : ℤ_[2]), IsUnit e ∧ (a = 0 ∨ a = 1) ∧
      (∃ P : Matrix (Fin 3) (Fin 3) ℤ_[2], IsUnit P.det ∧
        Pᵀ * diagonal ε * P = !![2 * a, 1, 0; 1, 2 * a, 0; 0, 0, e]) ∧
      (a = 1 → ∀ x y : ℚ_[2], 2 * x ^ 2 + 2 * x * y + 2 * y ^ 2 = 0 → x = 0 ∧ y = 0)

end QuadFormsKB.Kitaoka.Padic
