/-
# Integral quadratic forms

**Integrality means integrality of the upper-triangular coefficient matrix.** An integral
quadratic form in `n` variables is an integer quadratic polynomial
`Q(x) = ∑_{i ≤ j} c i j * x i * x j` (`IntQF n := QuadForm ℤ n`, see `Defs/QuadForm.lean`),
and a rational form is integral (`RatQF.IsIntegral`) when all its coefficients `c i j` are
integers, equivalently when it takes integer values on `ℤⁿ` (the sense of the 290-Theorem).

*Secondary notion.* Some literature (O'Meara's *integral*, the 15-Theorem) uses the stricter
**classically integral**: `Q(x) = xᵀ A x` for a symmetric integer Gram matrix `A`,
equivalently every cross coefficient is even (`Equiv/Integral.lean`). It is kept only for
statements that need it.

The link to Mathlib's `QuadraticForm ℤ (Fin n → ℤ)` is the bijection in `Equiv/Mathlib.lean`.
-/
import Mathlib
import QuadFormsKB.Defs.Rational

open Matrix

namespace QuadFormsKB

variable {n : ℕ}

/-- An integral quadratic form: an integer quadratic polynomial `∑_{i ≤ j} c i j x i x j`. -/
abbrev IntQF (n : ℕ) := QuadForm ℤ n

/-- **A rational form is integral** when every entry of its upper-triangular coefficient
matrix is an integer: $c_{ij} \in \mathbb{Z}$ for all $0 \le i \le j < n$.

This is the primary meaning of "integral" in this library. It is equivalent to coming from an
`IntQF` (`RatQF.isIntegral_iff_exists_intQF`), and to being **integer-valued**, i.e.
$Q(\mathbb{Z}^n) \subseteq \mathbb{Z}$ (`RatQF.isIntegral_iff_integerValued`), the sense of the
290-Theorem. Example: $x_0^2 + x_0 x_1 + x_1^2$ is integral, but not classically integral. -/
@[kb "bhargavahanke" "§1"]
def RatQF.IsIntegral (Q : RatQF n) : Prop := ∀ i j, ∃ z : ℤ, Q.coeff i j = z

/-- **The Gram-matrix expression** $\vec{x}^{\mathsf T} A\, \vec{x} = \sum_{i,j} A_{ij}\, x_i x_j$ for an
integer matrix $A$ and $\vec{x} \in \mathbb{Z}^n$. Used only to state `IsClassicallyIntegral`. -/
def gramForm (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ :=
  x ⬝ᵥ (A *ᵥ x)

/-- **Classically integral** (a *secondary* notion; O'Meara's "integral", and the hypothesis of
the 15-Theorem): $Q(\vec{x}) = \vec{x}^{\mathsf T} A\, \vec{x}$ for some **symmetric integer** matrix $A$.

Equivalently, every cross coefficient is even: $2 \mid c_{ij}$ for $i < j$
(`isClassicallyIntegral_iff`). This is stricter than integral: $x_0^2 + x_0 x_1 + x_1^2$
is integral but not classically integral (`eisensteinForm_not_isClassicallyIntegral`), while
$2Q$ is always classically integral (`two_smul_isClassicallyIntegral`). "Integral" in this
library means `RatQF.IsIntegral` / `IntQF`, not this. -/
@[kb "omeara1963" "§41"]
def IsClassicallyIntegral (Q : IntQF n) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℤ, A.IsSymm ∧ ∀ x, Q.eval x = gramForm A x

end QuadFormsKB
