/-
# Shimura 2004, §8.18: the local Euler series $T'(s)$ of $SO^\varphi$ (8.23a)

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §5.19 (the denominator ideal,
printed p. 44), §8.3 and §8.18, (8.22)–(8.23a) (pp. 64, 74–75). Page numbers are printed pages.

**What the book says.** Over a nonarchimedean local field $F$ with maximal order $\mathfrak g$, prime $\mathfrak p$
and $q = [\mathfrak g:\mathfrak p]$, for $(V,\varphi)$ satisfying (8.1), a $\mathfrak g$-maximal lattice $L$ with
Witt decomposition of Witt index $r$ and core dimension $t = n - 2r$ (§8.3), and $C = \{\alpha\in SO^\varphi \mid
L\alpha = L\}$ (8.3a), the series
$$T'(s) = \sum_{\alpha\in C\backslash SO^\varphi}|\mathrm{dil}(\alpha)|^s\qquad(8.22)$$
is, under (8.19) ($t \le 2$, with extra conditions when $t = 2$),
$$T'(s) = \prod_{i=1}^r\frac{1-q^{2i-2-2s}}{(1-q^{r+t+i-2-s})(1-q^{r-i-s})}.\qquad(8.23a)$$
Here $\mathrm{dil}(\alpha)$ is the denominator ideal of the matrix of $\alpha$ in a $\mathfrak g$-basis of $L$ (§5.19)
and $|\mathfrak p^m| = q^{-m}$. The book deduces (8.23a) from [S97, Theorem 16.16]; it is the first case of the formal
Euler factors (8.24) behind the Euler products of Chapters V and VI.

**Formalization.** $F = K_v$ is the completion of a number field $K$ at a finite prime $v$, $V = F^n$, $L = \mathfrak
g^n$ (`Lattices.std v`; any $\mathfrak g$-maximal lattice is $\mathfrak g^n$ in a suitable basis), and matrices act
on the left. The cosets $\alpha C$ correspond to the lattices $\alpha L$, $\alpha\in SO^\varphi$, and
$N(\mathrm{dil}(\alpha)) = [L + \alpha L : L]$ (both equal $\prod_{e_i<0}q^{-e_i}$ for the elementary divisors
$\mathfrak p^{e_i}$ of $\alpha$, [S97, §3.7]); so the coefficient of $X^m$, $X = q^{-s}$, in (8.23a) counts the
lattices $\alpha L$ with $[L+\alpha L:L] = q^m$. The statement is restricted to $t \le 1$, where (8.19) holds
automatically. The Witt index is `QuadraticForm.wittIndex`.

**States** `Formula8_23a` (a named proposition; *not proved here*).
-/
import QuadFormsKB.Literature.Shimura2004.Diophantine
import QuadFormsKB.Tamagawa.LocalVolume
import QuadFormsKB.Witt.Decomposition
import Mathlib.RingTheory.PowerSeries.Basic
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Matrix PowerSeries

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

/-- The geometric series $\sum_{k\ge0} a^kX^k = (1 - aX)^{-1}$. -/
def geomSeries (a : ℚ) : PowerSeries ℚ := PowerSeries.mk fun k => a ^ k

/-- **The right-hand side of (8.23a)** (Shimura 2004, p. 75) as a power series in $X = q^{-s}$:
$\prod_{i=1}^r(1 - q^{2i-2}X^2)(1-q^{r+t+i-2}X)^{-1}(1-q^{r-i}X)^{-1}$. -/
@[kb "shimura2004" "(8.23a), p. 75 (right-hand side, as a power series in q^{-s})"]
def eulerT' (q r t : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.Icc 1 r, ((1 - C ((q : ℚ) ^ (2 * i - 2)) * X ^ 2) * geomSeries ((q : ℚ) ^ (r + t + i - 2)) *
    geomSeries ((q : ℚ) ^ (r - i)))

/-- **(8.23a)** (Shimura 2004, §8.18, p. 75): let $K$ be a number field, $v$ a finite prime, $F = K_v$ with maximal
order $\mathfrak g$ and $q = [\mathfrak g:\mathfrak p]$, $\varphi$ a nondegenerate form on $F^n$ satisfying (8.1)
for which $L = \mathfrak g^n$ is $\mathfrak g$-maximal, $r$ its Witt index and $t = n - 2r \le 1$. Then for every
$m \ge 0$ the lattices $\alpha L$, $\alpha \in SO^\varphi(F)$, with $[L + \alpha L : L] = q^m$ (i.e.
$N(\mathrm{dil}(\alpha)) = q^m$) are finite in number, and their number is the coefficient of $X^m$ in
$\prod_{i=1}^r(1-q^{2i-2}X^2)/((1-q^{r+t+i-2}X)(1-q^{r-i}X))$ (`eulerT'`). *Stated, not proved* (the book quotes
[S97, Theorem 16.16]). -/
@[kb "shimura2004" "(8.22), (8.23a), p. 75 (T'(s) = Σ_{C\\SO} |dil(α)|^s = ∏ (1-q^{2i-2-2s})/(…))"]
def Formula8_23a : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (Q : QuadForm (v.adicCompletion K) n), Q.Nondegenerate →
    letI : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
    Cond81 (v.adicCompletionIntegers K) Q.toQuadraticForm →
    OMeara.IsMaximal Q.toQuadraticForm (1 : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K))
      (std v : Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)) →
    n - 2 * QuadraticForm.wittIndex Q.toQuadraticForm ≤ 1 →
    ∀ m : ℕ,
      let S : Set (Submodule (v.adicCompletionIntegers K) (Fin n → v.adicCompletion K)) :=
        {M | (∃ α ∈ soSub Q (v.adicCompletion K), locAct v (α : GL (Fin n) (v.adicCompletion K)) (std v) = M) ∧
          (std v).toAddSubgroup.relIndex (std v ⊔ M).toAddSubgroup = Nat.card (𝓞 K ⧸ v.asIdeal) ^ m}
      S.Finite ∧
        (S.ncard : ℚ) = coeff m (eulerT' (Nat.card (𝓞 K ⧸ v.asIdeal))
          (QuadraticForm.wittIndex Q.toQuadraticForm) (n - 2 * QuadraticForm.wittIndex Q.toQuadraticForm))

end QuadFormsKB.Shimura2004
