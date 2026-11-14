/-
# Kitaoka 1993, Theorem 5.6.3 (I): the local density $\beta_p(N, N)$ for odd $p$ (stated)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Theorem 5.6.3, pp. 108–109 (printed pages),
case (I), $p \ne 2$.

**Book statement (I).** Let $N = \perp_{j} M_j$ be a regular quadratic lattice over $\mathbb Z_p$ ($p \ne 2$), where
$M_j$ is $(p^j)$-modular or $\{0\}$, only finitely many $M_j \ne \{0\}$, and $M_j = N_j^{p^j}$ is the scaling by
$p^j$ of a unimodular lattice $N_j$. Put $n_j = \operatorname{rank}N_j$,
$w = \sum_j jn_j\bigl(\sum_{k > j}n_k + (n_j + 1)/2\bigr)$, $P(m) = \prod_{i=1}^m(1 - p^{-2i})$ ($P(0) = 1$), and
for a regular quadratic space $U$ over $\mathbb Z/p\mathbb Z$, $\chi(U) = 0$ if $\dim U$ is odd, $1$ if $U$ is
hyperbolic, $-1$ otherwise; $\chi(N_j) = \chi(N_j/pN_j)$. Then
$$\beta_p(N, N) = 2^sp^wPE, \qquad s = \#\{j \mid M_j \ne \{0\}\},\quad P = \prod_jP([n_j/2]),\quad
E = \prod_{j : M_j \ne \{0\}}(1 + \chi(N_j)p^{-n_j/2})^{-1}.$$

**Encoding.** For $p$ odd every lattice has an orthogonal basis, so $N$ has a Gram matrix
$S = \operatorname{diag}(p^{e_0}u_0, \dots, p^{e_{n-1}}u_{n-1})$ with $u_i \in \mathbb Z_p^\times$; then $M_j$ is
spanned by the basis vectors with $e_i = j$, $n_j = \#\{i \mid e_i = j\}$ and $N_j$ has Gram matrix
$\operatorname{diag}(u_i)_{e_i = j}$. Exponents are taken $\ge 0$ ($S$ integral, as `betaP` requires; the general
case is a scaling, Proposition 5.6.1 (iii)). For $n_j = 2k$ even, the space $N_j/pN_j$ over $\mathbb F_p$ is
hyperbolic exactly when $(-1)^k\prod_{e_i = j}u_i$ is a square modulo $p$, so
$\chi(N_j) = \chi_p\bigl((-1)^k\prod_{e_i=j}u_i\bigr)$ with $\chi_p$ the quadratic character of $\mathbb F_p$
(Mathlib `quadraticChar`). The integer $w$ is computed as $\sum_j\bigl(jn_j\sum_{k>j}n_k + j\,n_j(n_j+1)/2\bigr)$.

**Status.** *Stated* (`Theorem563odd`). Kitaoka's proof uses Corollary 5.6.1 (second reduction) and counts over finite
fields (Theorem 1.3.2); neither is formalized here. Case (II) ($p = 2$) is not stated.
-/
import QuadFormsKB.Literature.Kitaoka.Ch5Densities
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

/-- $P(m) = \prod_{i=1}^m(1 - p^{-2i})$ (Kitaoka 1993, Theorem 5.6.3, p. 108). -/
def kitP (p m : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 m, (1 - (p : ℝ) ^ (-(2 * (i : ℤ))))

/-- The ranks $n_j = \#\{i \mid e_i = j\}$ of the Jordan components. -/
def jordanRank {n : ℕ} (e : Fin n → ℕ) (j : ℕ) : ℕ := (Finset.univ.filter fun i => e i = j).card

/-- $\chi(N_j)$ for the diagonal unimodular component $N_j = \operatorname{diag}(u_i)_{e_i = j}$, $p$ odd: $0$ if
$n_j$ is odd, otherwise the quadratic character of $(-1)^{n_j/2}\prod_{e_i = j}u_i$ modulo $p$ ($1$ exactly when
$N_j/pN_j$ is hyperbolic). -/
def chiJ (p : ℕ) [Fact p.Prime] {n : ℕ} (e : Fin n → ℕ) (u : Fin n → ℤ_[p]) (j : ℕ) : ℝ :=
  if Odd (jordanRank e j) then 0 else
    (quadraticChar (ZMod p) (PadicInt.toZMod
      ((-1) ^ (jordanRank e j / 2) * ∏ i ∈ Finset.univ.filter (fun i => e i = j), u i)) : ℝ)

/-- **Kitaoka 1993, Theorem 5.6.3 (I)** (p. 108), *stated*, for $p \ne 2$ and the diagonal Gram matrix
$S = \operatorname{diag}(p^{e_i}u_i)$ ($u_i$ units): $\beta_p(N, N) = 2^sp^wPE$ with $J = \{e_i\}$ the set of $j$ with
$M_j \ne \{0\}$, $s = \#J$, $w = \sum_{j \in J}\bigl(jn_j\sum_{k \in J, k > j}n_k + jn_j(n_j+1)/2\bigr)$,
$P = \prod_{j\in J}P([n_j/2])$ and $E = \prod_{j \in J}(1 + \chi(N_j)p^{-n_j/2})^{-1}$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.3 (I), p. 108"]
def Theorem563odd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (n : ℕ) (e : Fin n → ℕ) (u : Fin n → ℤ_[p]), (∀ i, IsUnit (u i)) →
    let S : Matrix (Fin n) (Fin n) ℤ_[p] := diagonal fun i => (p : ℤ_[p]) ^ e i * u i
    let J : Finset ℕ := Finset.univ.image e
    let w : ℕ := ∑ j ∈ J, (j * jordanRank e j * ∑ k ∈ J.filter (fun k => j < k), jordanRank e k +
      j * (jordanRank e j * (jordanRank e j + 1) / 2))
    betaP p S S = (2 : ℝ) ^ J.card * (p : ℝ) ^ w * (∏ j ∈ J, kitP p (jordanRank e j / 2)) *
      ∏ j ∈ J, (1 + chiJ p e u j * (p : ℝ) ^ (-((jordanRank e j : ℝ) / 2)))⁻¹

end QuadFormsKB.Kitaoka.Density
