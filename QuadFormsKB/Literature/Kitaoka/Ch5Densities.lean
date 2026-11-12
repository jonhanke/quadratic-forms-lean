/-
# Kitaoka 1993, Section 5.6: local densities, Theorems 5.6.4, 5.6.5 and Corollary 5.6.2

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6: definition of the local density, p. 98,
Proposition 5.6.1, p. 99, Theorem 5.6.4, pp. 115–116, Theorem 5.6.5, p. 117, Corollary 5.6.2, p. 126 (printed pages).

**Setting** (Kitaoka, pp. 98–99). Let $p$ be a prime and $R = \mathbb Z_p$. A regular quadratic lattice $N$ of rank
$n$ over $R$ with basis $n_0, \dots, n_{n-1}$ is described by its Gram matrix $S = (B(n_i, n_j))$, a symmetric
$n \times n$ matrix with $\det S \ne 0$; Kitaoka's $B$ satisfies $Q(x) = B(x, x)$. Likewise $M$ of rank $m$ has Gram
matrix $T$. When $S$ and $T$ are integral (the scales $\mathfrak s(M)$, $\mathfrak s(N)$ lie in $R$), Kitaoka's
definition of the local density reads (p. 98, last line of the display; Proposition 5.6.1 (i))
$$\beta_p(M, N) = \lim_{r\to\infty} (p^r)^{m(m+1)/2 - mn}\, \#A_{p^r}(T, S),$$
$$A_{p^r}(T, S) = \{X \in M_{n,m}(R/p^rR) \mid S[X] \equiv T \bmod p^r E_m\},$$
where $S[X] = X^{\mathsf T} S X$ and $E_m$ is the set of symmetric $m \times m$ matrices over $R$ with even diagonal
(Kitaoka, p. 104): the diagonal entries agree modulo $2p^r$ and the others modulo $p^r$. This is the set of
$\sigma : M \to N/p^rN$ with $Q(\sigma(x)) \equiv Q(x) \bmod 2p^r$ for $x \in M$, through matrix representation. The
condition does not depend on the representative of $X$ modulo $p^r$ (for $r \ge 1$). Siegel's normalization is
$\alpha_p(M, N) = 2^{m\delta_{2,p} - \delta_{m,n}}\beta_p(M, N)$ (p. 98).

Lattices and inclusions in Gram-matrix terms: if $N$ has basis $(n_i)$ and $N'$ has basis $(n'_i)$ with
$(n_0, \dots, n_{n-1}) = (n'_0, \dots, n'_{n-1})\,C$, $C \in M_n(R)$, $\det C \ne 0$, then $N \subseteq N'$,
$S = C^{\mathsf T} S' C$ and $[N' : N] = |\det C|_p^{-1}$, where $|\cdot|_p$ is the $p$-adic norm ($|p|_p = p^{-1}$,
Lean's `‖·‖` on `ℤ_[p]`). An isometry $\eta : M \rightarrowtail N$ is a matrix $X \in M_{n,m}(R)$ with
$S[X] = T$. The scaled lattice $p^rM$ has Gram matrix $p^{2r}T$.

**Defines**
* `countA p r S T` $= \#A_{p^r}(T, S)$ (residues modulo $p^r$ represented by $0, \dots, p^r - 1$);
* `betaP p S T` $= \beta_p(M, N)$ and `alphaP p S T` $= \alpha_p(M, N)$ for integral $S$, $T$ (Lean's `limUnder`, a junk
  value if the limit does not exist; Kitaoka's Lemma 5.6.1 shows the sequence is eventually constant);
* `colSpan X`, `satSpan X`, `satIndex X`: for $X \in M_{n,m}(R)$, the submodule $M_0 = X R^m$ of $N = R^n$, the
  primitive closure $FM_0 \cap N$, and the index $[FM_0 \cap N : M_0]$;
* `gramForm S`: the quadratic form $x \mapsto x^{\mathsf T} S x$ on $\mathbb Q_p^n$, the space $FN$;
* statements `Theorem564a`, `Theorem564b`, `Theorem564c`, `Theorem564d`, `Theorem564e`, `Theorem565a`,
  `Theorem565b`, `Corollary562` (stated).

All of these are statements only (`def … : Prop`); none is proved here. In Theorem 5.6.4 Kitaoka first reduces to
integral scales by part (a) ("we may assume that the scales of $M, M', N, N'$ are in $R$", p. 116); the statements
below take integral Gram matrices throughout, which is that case.
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import QuadFormsKB.Witt.Decomposition

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {m n : ℕ}

/-- The matrix with entries in $\mathbb Z_p$ obtained from residues $0 \le a < p^r$. -/
def liftRes (p r : ℕ) [Fact p.Prime] (X : Matrix (Fin n) (Fin m) (Fin (p ^ r))) : Matrix (Fin n) (Fin m) ℤ_[p] :=
  X.map fun a => ((a : ℕ) : ℤ_[p])

/-- **$\#A_{p^r}(T, S)$** (Kitaoka 1993, §5.6, p. 98; the set $A_{p^r}(T, S)$ of Lemma 5.6.1, p. 104, with $e = 0$):
the number of $X \in M_{n,m}(\mathbb Z_p/p^r\mathbb Z_p)$ with $S[X] \equiv T \bmod p^r E_m$, i.e.
$(X^{\mathsf T} S X - T)_{ii} \in 2p^r\mathbb Z_p$ and $(X^{\mathsf T} S X - T)_{ij} \in p^r\mathbb Z_p$ for $i \ne j$. The
residues modulo $p^r$ are represented by $0, \dots, p^r - 1$. -/
@[kb "kitaoka1993" "§5.6, p. 98 (A_{p^r}(T, S))"]
def countA (p : ℕ) [Fact p.Prime] (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) :
    ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin m) (Fin (p ^ r)) //
    ∀ i j, ((p : ℤ_[p]) ^ r * if i = j then 2 else 1) ∣ ((liftRes p r X)ᵀ * S * liftRes p r X - T) i j}

/-- **The local density** $\beta_p(M, N)$ (Kitaoka 1993, §5.6, p. 98, and Proposition 5.6.1 (i), p. 99) of the lattice
$M$ with integral Gram matrix $T$ ($m \times m$) in the lattice $N$ with integral Gram matrix $S$ ($n \times n$):
$\lim_{r\to\infty} (p^r)^{m(m+1)/2 - mn}\, \#A_{p^r}(T, S)$ (Lean's `limUnder`). -/
@[kb "kitaoka1993" "§5.6, p. 98 (local density β_p(M, N))"]
def betaP (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) : ℝ :=
  limUnder atTop fun r : ℕ =>
    ((p : ℝ) ^ r) ^ (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n) * (countA p r S T : ℝ)

/-- **Siegel's local density** $\alpha_p(M, N) = 2^{m\delta_{2,p} - \delta_{m,n}}\beta_p(M, N)$ (Kitaoka 1993, §5.6,
p. 98; $\delta$ is Kronecker's delta). -/
@[kb "kitaoka1993" "§5.6, p. 98 (Siegel's local density α_p(M, N))"]
def alphaP (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) : ℝ :=
  (2 : ℝ) ^ ((if p = 2 then (m : ℤ) else 0) - if m = n then 1 else 0) * betaP p S T

/-- **The submodule $M_0 = X R^m$ of $N = R^n$** spanned by the columns $X_0, \dots, X_{m-1}$ of
$X \in M_{n,m}(\mathbb Z_p)$. -/
def colSpan {p : ℕ} [Fact p.Prime] (X : Matrix (Fin n) (Fin m) ℤ_[p]) : Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
  Submodule.span ℤ_[p] (Set.range Xᵀ)

/-- **The primitive closure $FM_0 \cap N$** of $M_0 = X R^m$ in $N = R^n$: the vectors of $\mathbb Z_p^n$ lying in
the $\mathbb Q_p$-span $FM_0$ of the columns of $X$. -/
def satSpan {p : ℕ} [Fact p.Prime] (X : Matrix (Fin n) (Fin m) ℤ_[p]) : Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
  ((Submodule.span ℚ_[p] (Set.range fun j i => (X i j : ℚ_[p]))).restrictScalars ℤ_[p]).comap
    ((Algebra.linearMap ℤ_[p] ℚ_[p]).compLeft (Fin n))

/-- **The index $[FM_0 \cap N : M_0]$** (Kitaoka 1993, Theorem 5.6.5 (a), p. 117) for $M_0 = X R^m$. -/
def satIndex {p : ℕ} [Fact p.Prime] (X : Matrix (Fin n) (Fin m) ℤ_[p]) : ℕ :=
  (colSpan X).toAddSubgroup.relIndex (satSpan X).toAddSubgroup

/-- **The quadratic space $FN$** of a lattice with Gram matrix $S$: $Q(x) = x^{\mathsf T} S x$ on $\mathbb Q_p^n$. -/
def gramForm {p : ℕ} [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]) :=
  Matrix.toQuadraticForm' (S.map fun a => (a : ℚ_[p]))

/-- A regular integral Gram matrix: symmetric with nonzero determinant. -/
def IsRegGram {p k : ℕ} [Fact p.Prime] (S : Matrix (Fin k) (Fin k) ℤ_[p]) : Prop := S.IsSymm ∧ S.det ≠ 0

/-! ### Theorem 5.6.4 -/

/-- **Kitaoka 1993, Theorem 5.6.4 (a)** (p. 115), *stated*: $\beta_p(p^rM, p^rN) = p^{r(m+1)m}\beta_p(M, N)$
($p^rM$, $p^rN$ have Gram matrices $p^{2r}T$, $p^{2r}S$), for regular lattices with $m \le n$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (a), p. 115"]
def Theorem564a : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n r : ℕ) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (S : Matrix (Fin n) (Fin n) ℤ_[p]),
    m ≤ n → IsRegGram T → IsRegGram S →
    betaP p ((p : ℤ_[p]) ^ (2 * r) • S) ((p : ℤ_[p]) ^ (2 * r) • T) = (p : ℝ) ^ (r * (m + 1) * m) * betaP p S T

/-- **Kitaoka 1993, Theorem 5.6.4 (b)** (p. 115), *stated*: if $N \subseteq N'$ then
$\beta_p(M, N) \le [N' : N]^m\beta_p(M, N')$. Here $S = C^{\mathsf T} S' C$ with $\det C \ne 0$ ($N$ is spanned by
the columns of $C$ in the basis of $N'$) and $[N' : N] = |\det C|_p^{-1}$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (b), p. 115"]
def Theorem564b : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (S' C : Matrix (Fin n) (Fin n) ℤ_[p]),
    m ≤ n → IsRegGram T → IsRegGram S' → C.det ≠ 0 →
    betaP p (Cᵀ * S' * C) T ≤ ‖C.det‖⁻¹ ^ m * betaP p S' T

/-- **Kitaoka 1993, Theorem 5.6.4 (c)** (p. 115), *stated*: if $N \subseteq N'$ and $p^rN' \subseteq N$ then
$\beta_p(M, N') \le p^{-rm(m+1)}[N : p^rN']^m\beta_p(p^rM, N)$. Here $S = C^{\mathsf T} S' C$, and $p^rN' \subseteq N$
means $C C'' = p^r 1_n$ for an integral $C''$, the matrix of $p^rN'$ in the basis of $N$, so
$[N : p^rN'] = |\det C''|_p^{-1}$; $p^rM$ has Gram matrix $p^{2r}T$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (c), p. 115"]
def Theorem564c : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n r : ℕ) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (S' C C'' : Matrix (Fin n) (Fin n) ℤ_[p]),
    m ≤ n → IsRegGram T → IsRegGram S' → C * C'' = (p : ℤ_[p]) ^ r • (1 : Matrix (Fin n) (Fin n) ℤ_[p]) →
    betaP p S' T ≤ (p : ℝ) ^ (-((r * m * (m + 1) : ℕ) : ℤ)) * ‖C''.det‖⁻¹ ^ m *
      betaP p (Cᵀ * S' * C) ((p : ℤ_[p]) ^ (2 * r) • T)

/-- **Kitaoka 1993, Theorem 5.6.4 (d)** (p. 116), *stated*: if $M \subseteq M'$ then
$\beta_p(M', N) \le [M' : M]^{n-m-1}\beta_p(M, N)$. Here $T = D^{\mathsf T} T' D$ with $\det D \ne 0$ and
$[M' : M] = |\det D|_p^{-1}$; the exponent $n - m - 1$ is an integer ($-1$ when $m = n$). -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (d), p. 116"]
def Theorem564d : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (T' D : Matrix (Fin m) (Fin m) ℤ_[p]) (S : Matrix (Fin n) (Fin n) ℤ_[p]),
    m ≤ n → IsRegGram T' → IsRegGram S → D.det ≠ 0 →
    betaP p S T' ≤ ‖D.det‖⁻¹ ^ ((n : ℤ) - m - 1) * betaP p S (Dᵀ * T' * D)

/-- **Kitaoka 1993, Theorem 5.6.4 (e)** (p. 116), *stated*: if $N' \subseteq N$ and $\eta(M) \subseteq N'$ for every
isometry $\eta : M \rightarrowtail N$, then $\beta_p(M, N) = [N : N']^{-m}\beta_p(M, N')$. Here $S' = C^{\mathsf T} S C$
with $\det C \ne 0$, $[N : N'] = |\det C|_p^{-1}$, and the hypothesis says that every $X$ with $S[X] = T$ is $X = CY$
with $Y$ integral. (The "in particular" clause for maximal anisotropic $N$ is not stated here.) -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (e), p. 116"]
def Theorem564e : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (S C : Matrix (Fin n) (Fin n) ℤ_[p]),
    m ≤ n → IsRegGram T → IsRegGram S → C.det ≠ 0 →
    (∀ X : Matrix (Fin n) (Fin m) ℤ_[p], Xᵀ * S * X = T → ∃ Y : Matrix (Fin n) (Fin m) ℤ_[p], X = C * Y) →
    betaP p S T = ‖C.det‖ ^ m * betaP p (Cᵀ * S * C) T

/-! ### Theorem 5.6.5 -/

/-- **Kitaoka 1993, Theorem 5.6.5 (a)** (p. 117), *stated*: for a regular lattice $N$ of rank $n$ there is $c > 0$ such
that for every regular $M$ of rank $m \le n$ and every submodule $M_0 = X R^m$ of $N$ isometric to $M$ ($S[X] = T$),
$\beta_p(M, N) > c\,[FM_0 \cap N : M_0]^{m+1-n}$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.5 (a), p. 117"]
def Theorem565a : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]), IsRegGram S →
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (X : Matrix (Fin n) (Fin m) ℤ_[p]),
      m ≤ n → IsRegGram T → Xᵀ * S * X = T → c * (satIndex X : ℝ) ^ ((m : ℤ) + 1 - n) < betaP p S T

/-- **Kitaoka 1993, Theorem 5.6.5 (b)** (p. 117), *stated*: for a regular lattice $N$ there is $c_1 > 0$ such that for
every regular $M$ of rank $m \le n$ represented by $N$, if the Witt index of $FN$ is at least $m$ and
$\beta_p(M, N) \ne 0$, then $\beta_p(M, N) \ge c_1$. The Witt index is `QuadraticForm.wittIndex` of `gramForm S`.
(Part (c), an upper bound through primitive densities $d_p$, is not stated here.) -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.5 (b), p. 117"]
def Theorem565b : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]), IsRegGram S →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (m : ℕ) (T : Matrix (Fin m) (Fin m) ℤ_[p]),
      m ≤ n → IsRegGram T → (∃ X : Matrix (Fin n) (Fin m) ℤ_[p], Xᵀ * S * X = T) →
      m ≤ QuadraticForm.wittIndex (gramForm S) → betaP p S T ≠ 0 → c₁ ≤ betaP p S T

/-! ### Corollary 5.6.2 -/

/-- **Kitaoka 1993, Corollary 5.6.2** (p. 126), *stated*: let $N$ be a lattice on a regular quadratic space over
$\mathbb Q$ with Gram matrix $S$ ($n \times n$). There are $c_1, c_2 > 0$, depending only on $N$, such that for every
lattice $M$ of rank $m$ with Gram matrix $T$, $n \ge 2m + 3$ and $M_p \rightarrowtail N_p$ for every prime $p$,
$$c_1 < \prod_p \alpha_p(M_p, N_p) < c_2$$
(the product converges: `Multipliable`). Here $S$ is integral (scaling $N$ only changes the constants) and then $T$
is integral as well (a lattice represented by $N_p$ has scale in $\mathfrak s(N_p)$), so both are taken in
$M_n(\mathbb Z)$, $M_m(\mathbb Z)$; $M_p \rightarrowtail N_p$ is $S[X] = T$ for some $X \in M_{n,m}(\mathbb Z_p)$. -/
@[kb "kitaoka1993" "§5.6, Cor. 5.6.2, p. 126"]
def Corollary562 : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℤ), S.IsSymm → S.det ≠ 0 →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (m : ℕ) (T : Matrix (Fin m) (Fin m) ℤ), T.IsSymm → T.det ≠ 0 →
      2 * m + 3 ≤ n →
      (∀ p : Nat.Primes, haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ∃ X : Matrix (Fin n) (Fin m) ℤ_[p], Xᵀ * S.map (Int.cast : ℤ → ℤ_[p]) * X = T.map (Int.cast : ℤ → ℤ_[p])) →
      let a : Nat.Primes → ℝ := fun p => haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        alphaP p (S.map (Int.cast : ℤ → ℤ_[p])) (T.map (Int.cast : ℤ → ℤ_[p]))
      Multipliable a ∧ c₁ < ∏' p, a p ∧ ∏' p, a p < c₂

end QuadFormsKB.Kitaoka.Density
