/-
# Quadratic forms as quadratic polynomials

**The primary definition.** A quadratic form in $n$ variables over a commutative ring $R$ is
a homogeneous quadratic polynomial
$$Q(\vec{x}) = \sum_{0 \le i \le j < n} c_{ij}\, x_i x_j, \qquad c_{ij} \in R,$$
recorded by its **upper-triangular coefficient matrix** $C = (c_{ij})$ (Mathlib's
`Matrix.IsUpperTriangular`: $c_{ij} = 0$ for $j < i$). Forms and upper-triangular matrices
correspond one-to-one, and nothing is halved or doubled, so the definition works over every
commutative ring ($\mathbb{Z}$, $\mathbb{Z}_p$, $\mathbb{F}_2$, …).

**Indexing is 0-based, as in Lean** (`Fin n` $= \{0, \dots, n-1\}$): the variables are
$x_0, \dots, x_{n-1}$ and $c_{ij}$ is the coefficient of $x_i x_j$. All docstrings in this
library follow that convention.

**Other definitions.** The symmetric Gram-matrix description $Q(\vec{x}) = \vec{x}^{\mathsf T} A \vec{x}$ with
$A = \tfrac12 (C + C^{\mathsf T})$ is equivalent only when $2$ is a unit. Over $\mathbb{Q}$ it is proved
equivalent in `Equiv/RationalGram.lean`. Mathlib's `QuadraticForm R (Fin n → R)` is proved
equivalent over every $R$ in `Equiv/Mathlib.lean`.
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix

namespace QuadFormsKB

/-- A quadratic form in `n` variables over `R`: the polynomial `∑_{i ≤ j} c i j x i x j`,
given by its upper-triangular coefficient matrix. -/
@[ext]
structure QuadForm (R : Type*) [CommRing R] (n : ℕ) where
  coeff : Matrix (Fin n) (Fin n) R
  upper : coeff.IsUpperTriangular

namespace QuadForm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The value of $Q$ at a vector over an $R$-algebra $K$** (evaluation after base change).

For a commutative ring $K$ with an $R$-algebra structure and $\vec{x} \in K^n$,
$$Q(\vec{x}) = \sum_{0 \le i \le j < n} \bar c_{ij}\, x_i x_j \in K,$$
where $\bar c_{ij}$ is the image of $c_{ij}$ under `algebraMap R K`. Typical uses: $K = R$
(`eval`), $R = \mathbb{Z} \to K = \mathbb{Q}$, and $R = \mathbb{Q} \to K = \mathbb{R}$ or
$\mathbb{Q}_p$ (the local forms in Hasse–Minkowski).

See also: `evalIn_eq_dotProduct` ($Q(\vec{x}) = \vec{x}^{\mathsf T} C \vec{x}$), `polar_eq_hessian`. -/
@[kb "omeara1963" "§41"]
def evalIn (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R n) (x : Fin n → K) : K :=
  ∑ i, ∑ j, if i ≤ j then algebraMap R K (Q.coeff i j) * x i * x j else 0

/-- **The value of $Q$ at $\vec{x} \in R^n$**, over the coefficient ring $R$ itself:
$Q(\vec{x}) = \sum_{0 \le i \le j < n} c_{ij}\, x_i x_j \in R$. This is `evalIn` with $K = R$. -/
abbrev eval (Q : QuadForm R n) (x : Fin n → R) : R := Q.evalIn R x

/-- **Build a form from any coefficient function** $c : \{0,\dots,n-1\}^2 \to R$: the form
$\sum_{0 \le i \le j < n} c_{ij}\, x_i x_j$. Entries below the diagonal ($j < i$) are
**ignored** (replaced by $0$), so any function gives a valid upper-triangular form.

Indices are 0-based. Example: `ofUpper ![![1, 1], ![0, 1]]` has
$c_{00} = c_{01} = c_{11} = 1$ (the entry in position $(1,0)$ is ignored), so it is
$x_0^2 + x_0 x_1 + x_1^2$. -/
def ofUpper (c : Fin n → Fin n → R) : QuadForm R n where
  coeff := Matrix.of fun i j => if i ≤ j then c i j else 0
  upper := by
    intro i j h
    simp only [id] at h
    simp only [Matrix.of_apply, ite_eq_right (not_le.mpr h)]

/-- **Scaling a form by $a \in R$:** the form $a \cdot Q$ has coefficients $a\, c_{ij}$, so
$(a \cdot Q)(\vec{x}) = a\, Q(\vec{x})$. (Coefficientwise; the upper-triangular shape is preserved.) -/
instance : SMul R (QuadForm R n) where
  smul a Q := ⟨a • Q.coeff, fun i j h => by simp [Q.upper h]⟩

@[simp] theorem smul_coeff (a : R) (Q : QuadForm R n) : (a • Q).coeff = a • Q.coeff := rfl

/-- **Change of coefficient ring** along a ring homomorphism $f : R \to S$: the form over $S$
with coefficients $f(c_{ij})$. Example: an integral form ($R = \mathbb{Z}$) viewed over
$S = \mathbb{Q}$ via `Int.castRingHom ℚ`, as in `RatQF.IsIntegral`. -/
def map {S : Type*} [CommRing S] (f : R →+* S) (Q : QuadForm R n) : QuadForm S n :=
  ⟨Q.coeff.map f, fun i j h => by simp [Q.upper h]⟩

/-- **Matrix form of the value:** $Q(\vec{x}) = \vec{x}^{\mathsf T} \bar C\, \vec{x}$ for $\vec{x} \in K^n$, where
$\bar C$ is the coefficient matrix mapped into $K$. The terms below the diagonal vanish because
$C$ is upper triangular. -/
theorem evalIn_eq_dotProduct (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R n)
    (x : Fin n → K) : Q.evalIn K x = x ⬝ᵥ (Q.coeff.map (algebraMap R K) *ᵥ x) := by
  simp only [evalIn, dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · ring
  · simp [Q.upper (show id j < id i from not_le.mp h)]

/-- The Hessian matrix `C + Cᵀ = (∂²Q / ∂xᵢ∂xⱼ)`: symmetric, integral, no division by 2. -/
def hessian (Q : QuadForm R n) : Matrix (Fin n) (Fin n) R := Q.coeff + Q.coeffᵀ

/-- **The Hessian is the matrix of the associated bilinear form.** For $\vec{x}, \vec{y} \in K^n$ over any
$R$-algebra $K$,
$$B(\vec{x}, \vec{y}) := Q(\vec{x} + \vec{y}) - Q(\vec{x}) - Q(\vec{y}) = \vec{x}^{\mathsf T} H\, \vec{y}, \qquad H = C + C^{\mathsf T}.$$
In particular $B(\vec{x}, \vec{x}) = 2\, Q(\vec{x})$. The form comes first; the bilinear form and its matrix
are derived from it without dividing by $2$. -/
@[kb "omeara1963" "§41"]
theorem polar_eq_hessian (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R n)
    (x y : Fin n → K) :
    Q.evalIn K (x + y) - Q.evalIn K x - Q.evalIn K y =
      x ⬝ᵥ (Q.hessian.map (algebraMap R K) *ᵥ y) := by
  rw [evalIn_eq_dotProduct, evalIn_eq_dotProduct, evalIn_eq_dotProduct, hessian, Matrix.map_add _ (map_add _),
      Matrix.transpose_map]
  generalize Q.coeff.map (algebraMap R K) = M
  have h : x ⬝ᵥ Mᵀ *ᵥ y = y ⬝ᵥ M *ᵥ x := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  rw [add_mulVec, dotProduct_add, h, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  ring

/-- **Nondegenerate over the coefficient ring $R$:** the Hessian $H = C + C^{\mathsf T}$ (the
matrix of the associated bilinear form) has $\det H \ne 0$ **in $R$**.

*Scope.* This is the right notion whenever $\operatorname{char} R \ne 2$, e.g. $R = \mathbb{Z},
\mathbb{Q}, \mathbb{R}, \mathbb{Z}_p, \mathbb{Q}_p$ (including $p = 2$). For $R = \mathbb{Z}$
it means nondegenerate over $\mathbb{Q}$. It is **not** "unimodular" ($\det H$ a unit). In
characteristic $2$ it fails for odd $n$ (then $\det H = 0$ always). The half-discriminant
that fixes this is deferred.

*Edge case.* The $0$-dimensional form is nondegenerate ($\det$ of the empty matrix is $1$).

See also: `RatQF.nondegenerate_iff_det_gram` (over $\mathbb{Q}$: $\det H \ne 0 \iff$ the Gram
matrix has nonzero determinant). -/
@[kb "omeara1963" "§41"]
def Nondegenerate (Q : QuadForm R n) : Prop := Q.hessian.det ≠ 0

/-- **Isotropic over $K$:** $Q$ has a nontrivial zero with coordinates **in $K$**, i.e.
$Q(\vec{x}) = 0$ for some $\vec{x} \in K^n$, $\vec{x} \ne 0$ (coefficients mapped into the $R$-algebra $K$).

The answer depends on $K$: $x_0^2 + x_1^2$ is anisotropic over $\mathbb{R}$, but isotropic over
$\mathbb{Q}_5$ (since $-1$ is a square there) and over $\mathbb{C}$. The $0$-dimensional form
is never isotropic.

See also: `RatQF.isotropicIn_iff_baseChange` (agreement with Mathlib's `Anisotropic`). -/
@[kb "serre1973" "Ch. IV, §1.6"]
def IsotropicIn (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R n) : Prop :=
  ∃ x : Fin n → K, x ≠ 0 ∧ Q.evalIn K x = 0

/-- **$Q$ represents $c \in R$ over $K$:** $Q(\vec{x}) = c$ for some $\vec{x} \in K^n$, with $c$ viewed in
$K$. Solutions are sought **in $K^n$**.

*Edge case.* Every form represents $0$ (take $\vec{x} = 0$), so for $c = 0$ this condition is trivial.
The meaningful condition at $0$ is `IsotropicIn`. Serre's "represents" is for $c \ne 0$. -/
@[kb "serre1973" "Ch. IV, §1.6"]
def RepresentsIn (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R n) (c : R) : Prop :=
  ∃ x : Fin n → K, Q.evalIn K x = algebraMap R K c

/-- **$Q$ and $Q'$ are isometric (equivalent) over $K$:** there is an invertible
$P \in \mathrm{GL}_n(K)$ with
$$Q(P \vec{x}) = Q'(\vec{x}) \quad \text{for all } \vec{x} \in K^n,$$
i.e. $Q'$ is obtained from $Q$ by the invertible change of variables $\vec{x} \mapsto P \vec{x}$ over $K$.

*Why on values.* The matrix $P^{\mathsf T} C P$ is generally not upper triangular, so the condition
is stated on values rather than as an equation of coefficient matrices. -/
@[kb "serre1973" "Ch. IV, §1.1"]
def IsometricIn (K : Type*) [CommRing K] [Algebra R K] (Q Q' : QuadForm R n) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P.det ∧ ∀ x, Q.evalIn K (P *ᵥ x) = Q'.evalIn K x

/-- **The diagonal form** $\langle a_0, \dots, a_{n-1} \rangle = a_0 x_0^2 + \cdots +
a_{n-1} x_{n-1}^2$: coefficients $c_{ii} = a_i$ and $c_{ij} = 0$ for $i \ne j$. -/
def diag (a : Fin n → R) : QuadForm R n := ⟨Matrix.diagonal a, Matrix.blockTriangular_diagonal a⟩

end QuadForm

end QuadFormsKB
