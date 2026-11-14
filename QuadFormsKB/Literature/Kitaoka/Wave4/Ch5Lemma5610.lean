/-
# Kitaoka 1993, Lemma 5.6.10: isometries of a degenerate space into a regular space over $\mathbb F_p$ (stated)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Lemma 5.6.10, p. 121 (printed page), with the
function $\chi$ of §1.3 (`chiV`).

**Book statement.** Let $p$ be an odd prime and $U$, $V$ quadratic spaces over $\mathbb F_p$ with $U$ represented by
$V$ and $V$ regular. Write $U = U_0 \perp U^{\perp}$ ($U^{\perp}$ the radical, so $Q(U^{\perp}) = 0$ and $U_0$ regular)
and put $t = \dim U_0$, $u = \dim U$, $v = \dim V$; suppose $u < v$ and $v > 2$. Then
$$p^{u(u+1)/2-uv}\,r(U, V) = \prod_{i=1}^{a}(1 \pm p^{-r_i}) \times
\begin{cases} 2 & v - 2u + t = 0,\\ 1 + \chi(W)p^{-1} & v - 2u + t = 2,\\ 1 & \text{otherwise,}\end{cases}$$
where $2 \le r_i \le b$, $a$ and $b$ are bounded by a number depending only on $v$, $r(U, V)$ is the number of
isometries $U \rightarrowtail V$, and $W$ is defined by $V \cong U_0 \perp W$.

**Reading of the statement.** The printed statement is damaged in the machine-read text; the factors $2$ and
$1 + \chi(W)p^{-1}$ were read from the proof (pp. 122–123), and checked against the page image of the printed
statement.

**Encoding.** $U_0 = \mathbb F_p^t$ with a quadratic form $Q_{U_0}$ with nondegenerate polar form, $U^{\perp} =
\mathbb F_p^s$ with the zero form, $u = t + s$; $U = U_0 \perp U^{\perp}$ is $\mathbb F_p^t \times \mathbb F_p^s$ with
$Q(x, y) = Q_{U_0}(x)$. $V = \mathbb F_p^v$ with $Q_V$ with nondegenerate polar form. An isometry is an injective
linear map $\sigma$ with $Q_V(\sigma(x, y)) = Q_{U_0}(x)$ (`isoCountDeg`). $W = \mathbb F_p^{w}$ with form $Q_W$,
$w = v - t$ (hypothesis `t + w = v`), and the hypothesis that there is a linear isomorphism $\tau$ from
$\mathbb F_p^t \times \mathbb F_p^w$ onto $V$ with $Q_V(\tau(x, z)) = Q_{U_0}(x) + Q_W(z)$ says $V \cong U_0 \perp W$
(it exists for every $U_0$ represented by $V$, and $\chi(W)$ depends only on the isometry class of $W$). "$U$ is
represented by $V$" is `0 < isoCountDeg`. The bound "depending only on $v$" is a constant $C$ chosen before $p$, with
$a \le C$ and $2 \le r_i \le C$ (so $b \le C$); each sign $\pm$ is $\varepsilon_i \in \{1, -1\}$.

**Status.** *Stated* (`Lemma5610`). Kitaoka proves it from Theorem 1.3.2 and Lemma 5.6.9; none is used here.
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Lemma569
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open QuadraticMap

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- $r(U, V)$ for $U = U_0 \perp U^{\perp} = \mathbb F_p^t \times \mathbb F_p^s$ with form $Q_{U_0}(x)$ (the zero form
on the $\mathbb F_p^s$ factor): the number of injective linear maps $\sigma : \mathbb F_p^t \times \mathbb F_p^s \to
\mathbb F_p^v$ with $Q_V(\sigma(x, y)) = Q_{U_0}(x)$ for all $x$, $y$. -/
def isoCountDeg {K : Type*} [Field K] {t : ℕ} (s : ℕ) {v : ℕ} (QU : QuadraticForm K (Fin t → K))
    (QV : QuadraticForm K (Fin v → K)) : ℕ :=
  Nat.card {σ : ((Fin t → K) × (Fin s → K)) →ₗ[K] (Fin v → K) //
    Function.Injective σ ∧ ∀ x y, QV (σ (x, y)) = QU x}

/-- **Kitaoka 1993, Lemma 5.6.10** (p. 121), *stated*: for every $v$ there is a bound $C$ such that for every odd
prime $p$, regular $Q_{U_0}$ on $\mathbb F_p^t$ (nondegenerate polar form), $s \ge 0$ (so $u = t + s$), regular $Q_V$ on
$\mathbb F_p^v$, and $W$ with $V \cong U_0 \perp W$, if $u < v$, $v > 2$ and $U_0 \perp U^{\perp}$ is represented by $V$,
then there are $a \le C$, signs $\varepsilon_i \in \{1, -1\}$ and exponents $2 \le r_i \le C$ ($i < a$) with
$$p^{u(u+1)/2-uv}\,r(U, V) = \prod_{i<a}(1 + \varepsilon_ip^{-r_i}) \cdot
\begin{cases} 2 & v - 2u + t = 0,\\ 1 + \chi(W)p^{-1} & v - 2u + t = 2,\\ 1 & \text{otherwise.}\end{cases}$$
See the module docstring for the encoding and the reading of the printed statement. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.10, p. 121"]
def Lemma5610 : Prop :=
  ∀ v : ℕ, ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (t s w : ℕ)
    (QU : QuadraticForm (ZMod p) (Fin t → ZMod p)) (QV : QuadraticForm (ZMod p) (Fin v → ZMod p))
    (QW : QuadraticForm (ZMod p) (Fin w → ZMod p)),
    (polarBilin QU).Nondegenerate → (polarBilin QV).Nondegenerate → t + w = v →
    (∃ τ : ((Fin t → ZMod p) × (Fin w → ZMod p)) ≃ₗ[ZMod p] (Fin v → ZMod p),
      ∀ x z, QV (τ (x, z)) = QU x + QW z) →
    t + s < v → 2 < v → 0 < isoCountDeg s QU QV →
    ∃ (a : ℕ) (ε : Fin a → ℤ) (r : Fin a → ℕ), a ≤ C ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i, 2 ≤ r i ∧ r i ≤ C) ∧
      ((p : ℝ) ^ (((t + s) * (t + s + 1) / 2 : ℕ) - ((t + s) * v : ℕ) : ℤ)) * (isoCountDeg s QU QV : ℝ) =
        (∏ i : Fin a, (1 + (ε i : ℝ) * (p : ℝ) ^ (-(r i : ℤ)))) *
          (if (v : ℤ) - 2 * (t + s) + t = 0 then 2
           else if (v : ℤ) - 2 * (t + s) + t = 2 then 1 + chiV QW * (p : ℝ) ^ (-1 : ℤ)
           else 1)

end QuadFormsKB.Kitaoka
