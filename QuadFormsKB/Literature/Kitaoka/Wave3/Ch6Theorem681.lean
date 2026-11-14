/-
# Kitaoka 1993, Theorem 6.8.1: the Minkowski–Siegel formula in Kitaoka's normalization (stated)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §6.8, Theorem 6.8.1, p. 173 (printed page), with the
definitions of $E(K)$ and the weight $w(K)$ just before it, and the local densities of §5.6 (p. 98).

**Setting.** Lattices $M$, $N$ on positive definite quadratic spaces over $\mathbb Q$ are given by Gram matrices
$T = (B(m_i, m_j))$ ($m \times m$) and $S = (B(n_i, n_j))$ ($n \times n$), with Kitaoka's $B(x, x) = Q(x)$. Here
the Gram matrices are taken integral ($\mathfrak s(M), \mathfrak s(N) \subseteq \mathbb Z$), the case in which the
local densities `alphaP`, `primDensity` of §5.6 are defined; Kitaoka allows rational Gram matrices.
* $E(K) = \#O(K)$, the number of $U \in M_n(\mathbb Z)$ with $U^{\mathsf T}SU = S$ (`orthCount`; such $U$ are
  automatically invertible);
* $r(M, N) = \#\{X \in M_{n,m}(\mathbb Z) \mid X^{\mathsf T}SX = T\}$, the number of isometries $M \to N$
  (`isomCount`), and $r_{pr}(M, N)$ the number of those with $X(M)$ primitive in $N$, i.e. $X \bmod p$ of rank $m$
  for every prime $p$ (`primIsomCount`);
* the genus of $N$: positive definite $S'$ with $U_p^{\mathsf T}SU_p = S'$ for some $U_p \in \mathrm{GL}_n(\mathbb Z_p)$
  at every prime $p$ (`GramSameGenus`; at the real place both are positive definite, hence equivalent). This is
  the Gram-matrix form of `QuadFormsKB.Siegel.SameGenus` (stated for integral quadratic forms);
* isometry classes: $S' \sim S''$ when $S'' = U^{\mathsf T}S'U$ for some $U \in \mathrm{GL}_n(\mathbb Z)$ (`GramEquiv`);
* $w(N) = \sum_i E(N_i)^{-1}$ over a complete set of representatives $N_i$ of the classes in the genus of $N$;
* $\varepsilon_{m,n} = \tfrac12$ if $n = m + 1$ or $n = m > 1$, and $1$ otherwise;
* $\alpha_p(M_p, N_p) = 2^{m\delta_{2,p} - \delta_{m,n}}\beta_p(M_p, N_p)$ (`alphaP`) and
  $D_p(M_p, N_p) = 2^{m\delta_{2,p} - \delta_{m,n}}d_p(M_p, N_p)$ (from `primDensity`).

**Theorem 6.8.1.** (ii) and (iii):
$$w(N)^{-1}\sum_i \frac{r(M, N_i)}{E(N_i)} = \varepsilon_{m,n}\,\pi^{m(2n-m+1)/4}\prod_{i=0}^{m-1}
\Gamma\Big(\frac{n-i}{2}\Big)^{-1}(dN)^{-m/2}(dM)^{(n-m-1)/2}\prod_p\alpha_p(M_p, N_p),$$
and the same with $r_{pr}$ and $D_p$ in place of $r$ and $\alpha_p$. Part (i) is the case $N = M$ of (ii)
(Kitaoka: "We note that (i) is a special case of (ii), by putting N = M"). Kitaoka's product $\prod_{i=0}^{m-1}$ is
0-based already; $dM = \det T$, $dN = \det S$.

**Status.** *Stated* only (`Theorem681ii`, `Theorem681iii`). Related results proved in this repository, in other
normalizations: the mass formula (part (i)) for totally positive forms of rank at least 3
(`QuadFormsKB.Tamagawa.massFormulaHolds_totallyReal`, `QuadFormsKB.Cassels.AppBThm41.massFormula_uncond`), and the
mean value of representations by the genus for rank difference at least 3 in terms of the library's local densities
(`QuadFormsKB.Tamagawa.Frames.siegelFormsAt_totallyReal_general`); bridging those normalizations to Kitaoka's
$\alpha_p$ is not done here.
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Primitive
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Siegel681

variable {m n : ℕ}

/-- $E(N) = \#O(N)$ (Kitaoka 1993, §6.8, p. 173): the number of $U \in M_n(\mathbb Z)$ with $U^{\mathsf T}SU = S$. -/
@[kb "kitaoka1993" "§6.8, p. 173 (E(K) = #O(K))"]
def orthCount (S : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Nat.card {U : Matrix (Fin n) (Fin n) ℤ // Uᵀ * S * U = S}

/-- $r(M, N)$ (Kitaoka 1993, Theorem 6.8.1, p. 173): the number of isometries from $M$ to $N$, i.e. of
$X \in M_{n,m}(\mathbb Z)$ with $X^{\mathsf T}SX = T$. -/
@[kb "kitaoka1993" "§6.8, Thm. 6.8.1, p. 173 (r(M, N))"]
def isomCount (S : Matrix (Fin n) (Fin n) ℤ) (T : Matrix (Fin m) (Fin m) ℤ) : ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin m) ℤ // Xᵀ * S * X = T}

/-- $r_{pr}(M, N)$ (Kitaoka 1993, Theorem 6.8.1, p. 173): the number of isometries $\sigma : M \to N$ with
$\sigma(M)$ primitive in $N$, i.e. $X^{\mathsf T}SX = T$ and $X \bmod p$ of rank $m$ for every prime $p$. -/
@[kb "kitaoka1993" "§6.8, Thm. 6.8.1, p. 173 (r_pr(M, N))"]
def primIsomCount (S : Matrix (Fin n) (Fin n) ℤ) (T : Matrix (Fin m) (Fin m) ℤ) : ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin m) ℤ // Xᵀ * S * X = T ∧
    ∀ p : Nat.Primes, (X.map (Int.cast : ℤ → ZMod p)).rank = m}

/-- A positive definite integral Gram matrix. -/
def IsPosGramZ (S : Matrix (Fin n) (Fin n) ℤ) : Prop := (S.map (Int.cast : ℤ → ℝ)).PosDef

/-- **The genus** in Gram-matrix form (Kitaoka 1993, §6.1, p. 134): $S'$ is positive definite and
$U_p^{\mathsf T}SU_p = S'$ for some $U_p \in \mathrm{GL}_n(\mathbb Z_p)$, at every prime $p$. -/
def GramSameGenus (S S' : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsPosGramZ S' ∧ ∀ p : Nat.Primes, haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
    ∃ U : Matrix (Fin n) (Fin n) ℤ_[p], IsUnit U ∧
      Uᵀ * S.map (Int.cast : ℤ → ℤ_[p]) * U = S'.map (Int.cast : ℤ → ℤ_[p])

/-- **Isometric lattices** in Gram-matrix form: $S'' = U^{\mathsf T}S'U$ for some $U \in \mathrm{GL}_n(\mathbb Z)$. -/
def GramEquiv (S' S'' : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U ∧ Uᵀ * S' * U = S''

/-- $\varepsilon_{m,n}$ of Theorem 6.8.1: $\tfrac12$ if $n = m + 1$ or $n = m > 1$, and $1$ otherwise. -/
def epsMN (m n : ℕ) : ℝ := if n = m + 1 ∨ (n = m ∧ 1 < m) then 1 / 2 else 1

/-- The archimedean factor $\varepsilon_{m,n}\pi^{m(2n-m+1)/4}\prod_{i=0}^{m-1}\Gamma((n-i)/2)^{-1}
(dN)^{-m/2}(dM)^{(n-m-1)/2}$ of Theorem 6.8.1 (ii), (iii). -/
def archFactor (S : Matrix (Fin n) (Fin n) ℤ) (T : Matrix (Fin m) (Fin m) ℤ) : ℝ :=
  epsMN m n * Real.pi ^ ((m : ℝ) * (2 * n - m + 1) / 4) *
    (∏ i ∈ Finset.range m, (Real.Gamma (((n : ℝ) - i) / 2))⁻¹) *
    ((S.det : ℝ) ^ (-(m : ℝ) / 2)) * ((T.det : ℝ) ^ (((n : ℝ) - m - 1) / 2))

/-- $D_p(M_p, N_p) = 2^{m\delta_{2,p} - \delta_{m,n}}d_p(M_p, N_p)$ (Kitaoka 1993, Theorem 6.8.1, p. 173). -/
def primAlphaP (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) : ℝ :=
  (2 : ℝ) ^ ((if p = 2 then (m : ℤ) else 0) - if m = n then 1 else 0) * Density.primDensity p S T

/-- A finite complete set $(N_i)_{i \in \iota}$ of representatives of the isometry classes in the genus of $S$. -/
def IsGenusReps (S : Matrix (Fin n) (Fin n) ℤ) {ι : Type} (Ns : ι → Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, GramSameGenus S (Ns i)) ∧ (∀ i j, GramEquiv (Ns i) (Ns j) → i = j) ∧
    ∀ S', GramSameGenus S S' → ∃ i, GramEquiv (Ns i) S'

/-- **Kitaoka 1993, Theorem 6.8.1 (ii)** (p. 173), *stated*: for positive definite integral Gram matrices $T$ of $M$
($m \times m$) and $S$ of $N$ ($n \times n$) with $m \le n$, and a finite complete set of representatives $(N_i)$ of
the classes in the genus of $N$,
$$w(N)^{-1}\sum_i\frac{r(M, N_i)}{E(N_i)} = \varepsilon_{m,n}\pi^{m(2n-m+1)/4}\prod_{i=0}^{m-1}
\Gamma\Big(\frac{n-i}2\Big)^{-1}(dN)^{-m/2}(dM)^{(n-m-1)/2}\prod_p\alpha_p(M_p, N_p),$$
the product over the primes being convergent (`Multipliable`; Kitaoka writes $\prod_p$). For $m > n$ both sides
vanish trivially, and Kitaoka's statement has no restriction; $m \le n$ is assumed here. -/
@[kb "kitaoka1993" "§6.8, Thm. 6.8.1 (ii), p. 173"]
def Theorem681ii : Prop :=
  ∀ (m n : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (S : Matrix (Fin n) (Fin n) ℤ), IsPosGramZ T → IsPosGramZ S → m ≤ n →
    ∀ (ι : Type) [Fintype ι] (Ns : ι → Matrix (Fin n) (Fin n) ℤ), IsGenusReps S Ns →
      let a : Nat.Primes → ℝ := fun p => haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        Density.alphaP p (S.map (Int.cast : ℤ → ℤ_[p])) (T.map (Int.cast : ℤ → ℤ_[p]))
      Multipliable a ∧
        (∑ i, (isomCount (Ns i) T : ℝ) / orthCount (Ns i)) / (∑ i, (1 : ℝ) / orthCount (Ns i)) =
          archFactor S T * ∏' p, a p

/-- **Kitaoka 1993, Theorem 6.8.1 (iii)** (p. 173), *stated*: the primitive version of (ii),
$$w(N)^{-1}\sum_i\frac{r_{pr}(M, N_i)}{E(N_i)} = \varepsilon_{m,n}\pi^{m(2n-m+1)/4}\prod_{i=0}^{m-1}
\Gamma\Big(\frac{n-i}2\Big)^{-1}(dN)^{-m/2}(dM)^{(n-m-1)/2}\prod_pD_p(M_p, N_p),$$
with $D_p = 2^{m\delta_{2,p}-\delta_{m,n}}d_p$ (`primAlphaP`). -/
@[kb "kitaoka1993" "§6.8, Thm. 6.8.1 (iii), p. 173"]
def Theorem681iii : Prop :=
  ∀ (m n : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (S : Matrix (Fin n) (Fin n) ℤ), IsPosGramZ T → IsPosGramZ S → m ≤ n →
    ∀ (ι : Type) [Fintype ι] (Ns : ι → Matrix (Fin n) (Fin n) ℤ), IsGenusReps S Ns →
      let a : Nat.Primes → ℝ := fun p => haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        primAlphaP p (S.map (Int.cast : ℤ → ℤ_[p])) (T.map (Int.cast : ℤ → ℤ_[p]))
      Multipliable a ∧
        (∑ i, (primIsomCount (Ns i) T : ℝ) / orthCount (Ns i)) / (∑ i, (1 : ℝ) / orthCount (Ns i)) =
          archFactor S T * ∏' p, a p

end QuadFormsKB.Kitaoka.Siegel681
