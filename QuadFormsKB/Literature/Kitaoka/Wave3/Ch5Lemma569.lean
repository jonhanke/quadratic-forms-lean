/-
# Kitaoka 1993, Lemma 5.6.9: isometries of a totally isotropic space into a regular space over $\mathbb F_q$ (stated)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Lemma 5.6.9, p. 120 (printed page), with the
function $\chi$ of §1.3.

**Book statement.** Let $\mathbb F_q$ be a finite field with $q$ elements, $U$ a totally isotropic quadratic space
($Q(U) = 0$) and $V$ a regular quadratic space over $\mathbb F_q$, and suppose $U$ is represented by $V$. Then the
number $r(U, V)$ of isometries from $U$ to $V$ satisfies, with $u = \dim U$, $v = \dim V$,
$$q^{u(u+1)/2 - uv}\,r(U, V) = \begin{cases}\prod_{i=0}^{u-1}\bigl(1 - q^{-(v-2u+2i+1)}\bigr) & v \text{ odd},\\[2pt]
\prod_{i=0}^{u-1}\bigl(1 - \chi(V)q^{-(v-2u+2i+2)/2}\bigr)\bigl(1 + \chi(V)q^{-(v-2u+2i)/2}\bigr) & v \text{ even},
\end{cases}$$
where $\chi(V) = 0$ if $\dim V$ is odd, $1$ if $V$ is hyperbolic and $-1$ otherwise. (The product is over
$i = 0, \dots, u-1$ in the book already.)

**Encoding.** $U = \mathbb F_q^u$ with the zero form, $V = \mathbb F_q^v$ with a quadratic form $Q_V$ whose polar form
is nondegenerate (regular); an isometry is an injective linear map $\sigma$ with $Q_V(\sigma x) = 0$ for all $x$
(`isoCountFq`). $V$ is hyperbolic exactly when $v$ is even and the Witt index (`QuadraticForm.wittIndex`) is $v/2$
(`chiV`). "$U$ is represented by $V$" is the hypothesis `0 < isoCountFq`, equivalently $u \le$ the Witt index.

**Status.** *Stated* (`Lemma569`). Kitaoka proves it by induction on $u$ from the number of isotropic vectors
(Lemma 1.3.1); neither is formalized here.
-/
import QuadFormsKB.Witt.Decomposition
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QuadFormsKB.Citation

open QuadraticMap

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- $\chi(V)$ (Kitaoka 1993, §1.3): $0$ if $\dim V$ is odd, $1$ if $V$ is hyperbolic (Witt index $\dim V/2$), and
$-1$ otherwise. -/
@[kb "kitaoka1993" "§1.3, p. 14 (χ(V))"]
def chiV {K : Type*} [Field K] {v : ℕ} (QV : QuadraticForm K (Fin v → K)) : ℝ :=
  if Odd v then 0 else if QuadraticForm.wittIndex QV = v / 2 then 1 else -1

/-- $r(U, V)$ for $U = \mathbb F_q^u$ with the zero form: the number of injective linear maps
$\sigma : \mathbb F_q^u \to \mathbb F_q^v$ with $Q_V(\sigma x) = 0$ for all $x$. -/
def isoCountFq {K : Type*} [Field K] (u : ℕ) {v : ℕ} (QV : QuadraticForm K (Fin v → K)) : ℕ :=
  Nat.card {σ : (Fin u → K) →ₗ[K] (Fin v → K) // Function.Injective σ ∧ ∀ x, QV (σ x) = 0}

/-- **Kitaoka 1993, Lemma 5.6.9** (p. 120), *stated*: for a finite field $K$ with $q$ elements, $u \ge 0$ and a regular
quadratic form $Q_V$ on $K^v$ representing the totally isotropic space $K^u$,
$q^{u(u+1)/2-uv}r(U, V)$ is $\prod_{i<u}(1 - q^{-(v-2u+2i+1)})$ for odd $v$ and
$\prod_{i<u}(1 - \chi(V)q^{-(v-2u+2i+2)/2})(1 + \chi(V)q^{-(v-2u+2i)/2})$ for even $v$. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.9, p. 120"]
def Lemma569 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (u v : ℕ) (QV : QuadraticForm K (Fin v → K)),
    (polarBilin QV).Nondegenerate → 0 < isoCountFq u QV →
    let q : ℝ := Fintype.card K
    q ^ ((u * (u + 1) / 2 : ℕ) - (u * v : ℤ)) * (isoCountFq u QV : ℝ) =
      if Odd v then ∏ i ∈ Finset.range u, (1 - q ^ (-((v : ℝ) - 2 * u + 2 * i + 1)))
      else ∏ i ∈ Finset.range u, (1 - chiV QV * q ^ (-((v : ℝ) - 2 * u + 2 * i + 2) / 2)) *
        (1 + chiV QV * q ^ (-((v : ℝ) - 2 * u + 2 * i) / 2))

end QuadFormsKB.Kitaoka
