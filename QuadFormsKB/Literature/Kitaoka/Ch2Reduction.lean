/-
# Kitaoka 1993, Section 2.1: reduction theory of positive definite matrices over $\mathbb R$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.1, pp. 33–37 (printed pages).

**Setting** (Kitaoka, p. 33): $m \ge 2$, $G = \mathrm{GL}_m(\mathbb R)$, $\Gamma = \mathrm{GL}_m(\mathbb Z)$ acting on real
matrices through the entrywise cast, and $P = P(m)$ the positive definite real symmetric $m \times m$ matrices. For
matrices $p$, $x$ Kitaoka writes $p[x] = {}^t x\,p\,x$. Matrices are `Matrix (Fin m) (Fin m) ℝ`; indices are 0-based, so
Kitaoka's $a_1, \dots, a_m$ are `a 0, …, a (m-1)` and his condition $a_i / a_{i+1} \le t$ ($1 \le i \le m-1$) reads
`a i / a (i+1) ≤ t` for $0 \le i \le m-2$.

**Defines** (Kitaoka, pp. 33–34, 36)
* `posDiag m` $= A$: positive diagonal matrices; `siegelA m t` $= A_t$: those with $a_i/a_{i+1} \le t$;
* `unitri m` $= N$: upper triangular matrices with $1$ on the diagonal; `siegelN m u` $= N_u$: those with
  $|n_{ij}| \le u$ for $i < j$;
* `orthMat m` $= K$: the orthogonal matrices (Mathlib `Matrix.orthogonalGroup`);
* `siegelDomainG m t u` $= \tilde S_{t,u} = K A_t N_u$, the Siegel domain for $G$;
* `siegelDomain m t u` $= S_{t,u} = \{a[n] \mid a \in A_t, n \in N_u\}$, Siegel's domain in $P$;
* `firstColNorm g` $= \phi(g) = |g e|$ with $e = {}^t(1, 0, \dots, 0)$;
* `intCast γ`: the real matrix of $\gamma \in \Gamma$;
* `latMin p` $= \min p = \min\{p[x] \mid 0 \ne x \in \mathbb Z^m\}$ and `hermiteConst m` $= \mu_m$, Hermite's constant.

**Statements** (named propositions): `IwasawaDecomposition`, `Lemma211` (both proved in `Ch2ReductionProofs.lean`),
`Lemma212`, `Lemma213`, `Theorem211`, `Theorem212`, `Theorem213`, `Corollary211` (stated); and `IsMajorant`
(2.1.d7, p. 41).
-/
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QuadFormsKB.Citation

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Reduction

variable (m : ℕ)

/-- **The group $A = A(m)$** (Kitaoka 1993, §2.1, p. 33): the diagonal matrices $\mathrm{diag}(a_1, \dots, a_m)$ with
every $a_i > 0$. -/
@[kb "kitaoka1993" "§2.1, p. 33 (the group A)"]
def posDiag : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {x | ∃ a : Fin m → ℝ, (∀ i, 0 < a i) ∧ x = diagonal a}

/-- **The set $A_t$** (Kitaoka 1993, §2.1, p. 34): $\{\mathrm{diag}(a_1, \dots, a_m) \in A \mid a_i/a_{i+1} \le t$ for
$i = 1, \dots, m-1\}$ (0-based here: `a i / a (i+1) ≤ t` whenever `i + 1 < m`). -/
@[kb "kitaoka1993" "§2.1, p. 34 (the set A_t)"]
def siegelA (t : ℝ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {x | ∃ a : Fin m → ℝ, (∀ i, 0 < a i) ∧ (∀ i j : Fin m, j.val = i.val + 1 → a i / a j ≤ t) ∧ x = diagonal a}

/-- **The group $N = N(m)$** (Kitaoka 1993, §2.1, p. 34): the upper triangular matrices with every diagonal entry
equal to $1$. -/
@[kb "kitaoka1993" "§2.1, p. 34 (the group N)"]
def unitri : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {n | n.IsUpperTriangular ∧ ∀ i, n i i = 1}

/-- **The set $N_u$** (Kitaoka 1993, §2.1, p. 34): $\{n = (n_{ij}) \in N \mid |n_{ij}| \le u$ for
$1 \le i < j \le m\}$. -/
@[kb "kitaoka1993" "§2.1, p. 34 (the set N_u)"]
def siegelN (u : ℝ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {n | n ∈ unitri m ∧ ∀ i j, i < j → |n i j| ≤ u}

/-- **The group $K = K(m)$** (Kitaoka 1993, §2.1, p. 34): the orthogonal matrices in $G$ (Mathlib
`Matrix.orthogonalGroup`, $k\,{}^tk = 1$). -/
@[kb "kitaoka1993" "§2.1, p. 34 (the group K)"]
def orthMat : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {k | k ∈ Matrix.orthogonalGroup (Fin m) ℝ}

/-- **The Siegel domain for $G$** $\tilde S_{t,u} = K A_t N_u = \{kan \mid k \in K, a \in A_t, n \in N_u\}$ (Kitaoka
1993, §2.1, p. 34). -/
@[kb "kitaoka1993" "§2.1, p. 34 (Siegel domain S̃_{t,u} for G)"]
def siegelDomainG (t u : ℝ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {g | ∃ k ∈ orthMat m, ∃ a ∈ siegelA m t, ∃ n ∈ siegelN m u, g = k * a * n}

/-- **Siegel's domain** $S_{t,u} = \{a[n] \mid a \in A_t, n \in N_u\}$ in the cone $P$ of positive definite matrices
(Kitaoka 1993, §2.1, p. 36), with $a[n] = {}^t n\,a\,n$. -/
@[kb "kitaoka1993" "§2.1, p. 36 (Siegel's domain S_{t,u})"]
def siegelDomain (t u : ℝ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {p | ∃ a ∈ siegelA m t, ∃ n ∈ siegelN m u, p = nᵀ * a * n}

variable {m}

/-- **The function $\phi(g) = |ge|$** (Kitaoka 1993, §2.1, p. 34): the Euclidean length of $g e$ for
$e = {}^t(1, 0, \dots, 0)$, i.e. of the first column of $g$ (index `0` here; this needs $m \ge 1$, and is $0$ for
$m = 0$). -/
@[kb "kitaoka1993" "§2.1, p. 34 (φ(g) = |ge|)"]
def firstColNorm (g : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  Real.sqrt (∑ i, (if h : 0 < m then g i ⟨0, h⟩ else 0) ^ 2)

/-- The real matrix of $\gamma \in \Gamma = \mathrm{GL}_m(\mathbb Z)$ (entrywise cast). -/
def intCast (γ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℝ :=
  (γ : Matrix (Fin m) (Fin m) ℤ).map (Int.cast : ℤ → ℝ)

/-- **The arithmetic minimum** $\min p = \min\{p[x] \mid 0 \ne x \in \mathbb Z^m\}$ of a real symmetric matrix $p$
(Kitaoka 1993, §2.1, Theorem 2.1.1, p. 36), with $p[x] = {}^t x\,p\,x$; defined as an infimum (for positive definite
$p$ it is attained). -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.1, p. 36 (min p)"]
def latMin (p : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  sInf {r | ∃ x : Fin m → ℤ, x ≠ 0 ∧ r = (fun i => (x i : ℝ)) ⬝ᵥ (p *ᵥ fun i => (x i : ℝ))}

variable (m) in
/-- **Hermite's constant** $\mu_m = \sup_{p \in P} \min p / (\det p)^{1/m}$ (Kitaoka 1993, §2.1, Theorem 2.1.1,
p. 36), the supremum over positive definite real symmetric $m \times m$ matrices $p$ (`Matrix.PosDef`). Defined with
`sSup`, which returns $0$ for a set that is not bounded above; Theorem 2.1.1 (`Theorem211`) asserts the bound
$(4/3)^{(m-1)/2}$. -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.1, p. 36 (Hermite's constant μ_m)"]
def hermiteConst : ℝ :=
  sSup {r | ∃ p : Matrix (Fin m) (Fin m) ℝ, p.PosDef ∧ r = latMin p / p.det ^ ((1 : ℝ) / m)}

/-! ### Statements -/

/-- **The Iwasawa decomposition** (Kitaoka 1993, §2.1, p. 34), *stated*: every $g \in G = \mathrm{GL}_m(\mathbb R)$
can be written $g = kan$ with $k \in K$, $a \in A$, $n \in N$, i.e. $G = KAN$. -/
@[kb "kitaoka1993" "§2.1, p. 34 (Iwasawa decomposition g = kan)"]
def IwasawaDecomposition : Prop :=
  ∀ (m : ℕ) (g : GL (Fin m) ℝ), ∃ k ∈ orthMat m, ∃ a ∈ posDiag m, ∃ n ∈ unitri m, (g : Matrix _ _ ℝ) = k * a * n

/-- **Kitaoka 1993, Lemma 2.1.1** (p. 34), *stated*: $N = N_{1/2} N_{\mathbb Z}$ with $N_{\mathbb Z} = N \cap \Gamma$,
i.e. every $x \in N$ is $x = z y$ with $z \in N_{1/2}$ and $y$ an integral matrix in $N$. -/
@[kb "kitaoka1993" "§2.1, Lemma 2.1.1, p. 34"]
def Lemma211 : Prop :=
  ∀ (m : ℕ), ∀ x ∈ unitri m, ∃ z ∈ siegelN m (1 / 2), ∃ y : Matrix (Fin m) (Fin m) ℤ,
    y.map (Int.cast : ℤ → ℝ) ∈ unitri m ∧ x = z * y.map (Int.cast : ℤ → ℝ)

/-- **Kitaoka 1993, Lemma 2.1.3** (p. 35), *stated*: for $m \ge 2$ and every $g \in G$ there is $\gamma_0 \in \Gamma$
with $\phi(g\gamma_0) = \min_{\gamma \in \Gamma} \phi(g\gamma)$ and $g\gamma_0 \in \tilde S_{2/\sqrt3, 1/2}$. -/
@[kb "kitaoka1993" "§2.1, Lemma 2.1.3, p. 35"]
def Lemma213 : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ g : GL (Fin m) ℝ, ∃ γ₀ : GL (Fin m) ℤ,
    (∀ γ : GL (Fin m) ℤ, firstColNorm ((g : Matrix _ _ ℝ) * intCast γ₀) ≤
      firstColNorm ((g : Matrix _ _ ℝ) * intCast γ)) ∧
    (g : Matrix _ _ ℝ) * intCast γ₀ ∈ siegelDomainG m (2 / Real.sqrt 3) (1 / 2)

/-- **Kitaoka 1993, Theorem 2.1.1** (p. 36), *stated*: for $m \ge 2$,
$P = \bigcup_{\gamma \in \Gamma} S_{4/3, 1/2}[\gamma]$ (every positive definite $p$ is ${}^t\gamma\,s\,\gamma$ with
$s \in S_{4/3,1/2}$, $\gamma \in \mathrm{GL}_m(\mathbb Z)$), and Hermite's constant satisfies
$\mu_m \le (4/3)^{(m-1)/2}$. The second part is stated as the bound
$\min p \le (4/3)^{(m-1)/2} (\det p)^{1/m}$ for every $p \in P$, which is what $\mu_m \le (4/3)^{(m-1)/2}$ means
(`hermiteConst` is the supremum of the left side divided by $(\det p)^{1/m}$). -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.1, p. 36"]
def Theorem211 : Prop :=
  ∀ (m : ℕ), 2 ≤ m →
    (∀ p : Matrix (Fin m) (Fin m) ℝ, p.PosDef →
      ∃ γ : GL (Fin m) ℤ, ∃ s ∈ siegelDomain m (4 / 3) (1 / 2), p = (intCast γ)ᵀ * s * intCast γ) ∧
    (∀ p : Matrix (Fin m) (Fin m) ℝ, p.PosDef →
      latMin p ≤ (4 / 3 : ℝ) ^ (((m : ℝ) - 1) / 2) * p.det ^ ((1 : ℝ) / m))

/-- **Kitaoka 1993, Lemma 2.1.2** (p. 35), *stated*: let $m \ge 2$ and $g = kan \in G$ ($k \in K$,
$a = \mathrm{diag}(a_1, a_2, \dots) \in A$, $n \in N$), and assume $\phi(g\gamma) \ge \phi(g)$ for all $\gamma \in \Gamma$;
then $a_1/a_2 \le 2/\sqrt 3$ (0-based: `α 0 / α 1`). -/
@[kb "kitaoka1993" "§2.1, Lemma 2.1.2, p. 35"]
def Lemma212 : Prop :=
  ∀ (m : ℕ) (hm : 2 ≤ m) (g : GL (Fin m) ℝ) (k : Matrix (Fin m) (Fin m) ℝ) (α : Fin m → ℝ)
    (n : Matrix (Fin m) (Fin m) ℝ), k ∈ orthMat m → (∀ i, 0 < α i) → n ∈ unitri m →
    (g : Matrix (Fin m) (Fin m) ℝ) = k * diagonal α * n →
    (∀ γ : GL (Fin m) ℤ, firstColNorm (g : Matrix (Fin m) (Fin m) ℝ) ≤ firstColNorm ((g : Matrix (Fin m) (Fin m) ℝ) * intCast γ)) →
    α ⟨0, by omega⟩ / α ⟨1, by omega⟩ ≤ 2 / Real.sqrt 3

/-- **Kitaoka 1993, Theorem 2.1.2** (p. 37), *stated*: for $t, u > 0$ there are constants $c_1, c_2 > 0$ depending only
on $t$, $u$, $m$ such that for $p = a[n] \in S_{t,u}$ ($a \in A_t$, $n \in N_u$)
$$c_1 \le p[x]/a[x] \le c_2 \quad\text{for all nonzero } x \in \mathbb R^m,$$
and in particular $c_1 \le p_{ii}/a_i \le c_2$ for every $i$. Here $p[x] = {}^t x\,p\,x$; the inequalities are written
multiplied out ($a[x] > 0$ and $a_i > 0$). -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.2, p. 37"]
def Theorem212 : Prop :=
  ∀ (m : ℕ) (t u : ℝ), 0 < t → 0 < u → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ a ∈ siegelA m t, ∀ n ∈ siegelN m u,
      (∀ x : Fin m → ℝ, x ≠ 0 →
        c₁ * (x ⬝ᵥ (a *ᵥ x)) ≤ x ⬝ᵥ ((nᵀ * a * n) *ᵥ x) ∧
          x ⬝ᵥ ((nᵀ * a * n) *ᵥ x) ≤ c₂ * (x ⬝ᵥ (a *ᵥ x))) ∧
      (∀ i, c₁ * a i i ≤ (nᵀ * a * n) i i ∧ (nᵀ * a * n) i i ≤ c₂ * a i i)

/-- **Kitaoka 1993, Theorem 2.1.3** (p. 38), *stated*: put $S = S_{t,u}$ for $t, u > 0$ and let $d > 0$. Then there are
only finitely many $m \times m$ integral matrices $x$ with $0 < |\det x| < d$ and $S \cap S[x] \ne \emptyset$, where
$S[x] = \{{}^t x\,s\,x \mid s \in S\}$. -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.3, p. 38"]
def Theorem213 : Prop :=
  ∀ (m : ℕ) (t u d : ℝ), 0 < t → 0 < u → 0 < d →
    {x : Matrix (Fin m) (Fin m) ℤ | 0 < |(x.det : ℝ)| ∧ |(x.det : ℝ)| < d ∧
      ∃ s ∈ siegelDomain m t u, (x.map (Int.cast : ℤ → ℝ))ᵀ * s * x.map (Int.cast : ℤ → ℝ) ∈
        siegelDomain m t u}.Finite

/-- **A majorant** (Kitaoka 1993, §2.1, p. 41): for a real symmetric regular matrix $q$ (not necessarily positive
definite), a positive definite symmetric matrix $p$ is a majorant of $q$ if $q^{-1}[p] = q$, i.e.
${}^t p\,q^{-1}p = q$. -/
@[kb "kitaoka1993" "§2.1, p. 41 (majorant)"]
def IsMajorant (p q : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  p.PosDef ∧ pᵀ * q⁻¹ * p = q

/-- **Kitaoka 1993, Corollary 2.1.1** (finiteness of class number, p. 41), *stated*: let $d$ be a nonzero integer and
$Q_d = \{q \in M_m(\mathbb Z) \mid {}^t q = q,\ \det q = d\}$, with $q_1 \sim q_2$ iff $q_1 = q_2[u] = {}^t u\,q_2\,u$ for
some $u \in \mathrm{GL}_m(\mathbb Z)$. Then the number of equivalence classes in $Q_d$ is finite: there is a finite set
$T \subseteq Q_d$ such that every $q \in Q_d$ is equivalent to an element of $T$. The matrices need not be definite. -/
@[kb "kitaoka1993" "§2.1, Cor. 2.1.1, p. 41"]
def Corollary211 : Prop :=
  ∀ (m : ℕ) (d : ℤ), d ≠ 0 → ∃ T : Finset (Matrix (Fin m) (Fin m) ℤ),
    (∀ q ∈ T, qᵀ = q ∧ q.det = d) ∧
    ∀ q : Matrix (Fin m) (Fin m) ℤ, qᵀ = q → q.det = d →
      ∃ q₂ ∈ T, ∃ u : GL (Fin m) ℤ, q = (u : Matrix (Fin m) (Fin m) ℤ)ᵀ * q₂ * u

end QuadFormsKB.Kitaoka.Reduction
