/-
# Kitaoka 1993, Section 7.1: positive lattices of E-type

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), Chapter 7 introduction, p. 189, and §7.1, pp. 190–193
(printed pages).

**Setting.** A positive lattice $L$ of rank $n$ (a $\mathbb Z$-lattice on a positive definite quadratic space over
$\mathbb Q$) is described here by its Gram matrix $A = (B(e_i, e_j))$ in a basis $e_0, \dots, e_{n-1}$: a symmetric
rational $n \times n$ matrix with $x^{\mathsf T} A x > 0$ for $x \ne 0$ (`IsPosGram`), and $L = \mathbb Z^n$ with
$Q(x) = x^{\mathsf T} A x$ (`gramQ`). Every positive lattice has a basis, and E-type is invariant under isometry, so
nothing is lost. For positive lattices $L = (\mathbb Z^n, A)$ and $M = (\mathbb Z^m, B)$, Kitaoka (p. 189) puts on
$L \otimes M$ the form restricted from $\mathbb QL \otimes \mathbb QM$, whose Gram matrix in the basis $e_i \otimes f_j$
is $A \otimes B$. An element $\sum_{i,j} X_{ij}\, e_i \otimes f_j$ of $L \otimes M$ is the integer $n \times m$ matrix
$X$, and
$$Q(X) = \sum_{i,j,k,l} X_{ij} X_{kl} A_{ik} B_{jl} = \operatorname{tr}(X^{\mathsf T} A X B)$$
(`tensorQ`). The element $x \otimes y$ is the matrix $x y^{\mathsf T}$ (`Matrix.vecMulVec x y`); such elements are
called *split*.

**Defines**
* `IsPosGram A`, `gramQ A x`, `tensorQ A B X`;
* `IsMinimalVector A x`: $x \in \mathcal M(L)$, a minimal vector ($x \ne 0$ and $Q(x) = \min(L)$, §7.1, p. 190);
* `IsMinimalTensor A B X`: $X \in \mathcal M(L \otimes M)$;
* `IsEType A`: $L$ is of E-type, $\mathcal M(L \otimes M) \subseteq \{x \otimes y\}$ for every positive lattice $M$
  (Definition, p. 190);
* `Theorem711`, `Lemma711ii`, `Lemma711eq`, `Lemma711iii`, `Lemma712`, `Lemma713`, `Theorem712`, `Lemma714`: the
  statements of Theorems 7.1.1, 7.1.2 and Lemmas 7.1.1 (3), (ii), (iii), 7.1.2, 7.1.3, 7.1.4 (stated);
* §7.4: `GramIsometric`, `IsIndecomposable`, `IsMultIndecomposable`, `MinSpanFull` ($[L : \tilde L] < \infty$),
  `MinConnected` ($\tilde L$ indecomposable), `tensorGram`, `AssertionA12`; statements `Theorem741`, `Corollary741`,
  `Theorem742`, `Theorem743`.

Lattices are indexed by an arbitrary finite type $\iota$ (a basis $e_i$, $i \in \iota$), so that orthogonal sums
($\iota \sqcup \kappa$) and tensor products ($\iota \times \kappa$) are expressed without renumbering; the test lattices
$M$ in the definition of E-type are indexed by `Fin m`, which loses nothing.

**Proves**
* `tensorQ_vecMulVec`: $Q(x \otimes y) = Q(x)Q(y)$ (p. 190);
* `isEType_of_rank_one` (Lemma 7.1.1 (i)): a positive lattice of rank $1$ is of E-type;
* `tensorQ_le_of_isMinimal` (Lemma 7.1.1 (2)): $\min(L \otimes M) \le \min(L)\min(M)$.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QuadFormsKB.Literature.Kitaoka.Ch2Reduction

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **A positive Gram matrix**: a symmetric rational matrix $A$ with $x^{\mathsf T} A x > 0$ for every nonzero
$x \in \mathbb Q^n$, i.e. the Gram matrix of a positive lattice (Kitaoka 1993, §6.1, p. 129: a positive lattice is a
lattice on a positive definite quadratic space over $\mathbb Q$). -/
def IsPosGram (A : Matrix ι ι ℚ) : Prop :=
  A.IsSymm ∧ ∀ x : ι → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

/-- **The form of the lattice** $(\mathbb Z^n, A)$: $Q(x) = x^{\mathsf T} A x$ for $x \in \mathbb Z^n$. -/
def gramQ (A : Matrix ι ι ℚ) (x : ι → ℤ) : ℚ :=
  (fun i => (x i : ℚ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℚ))

/-- **The form of $L \otimes M$** (Kitaoka 1993, p. 189): for $L = (\mathbb Z^n, A)$, $M = (\mathbb Z^m, B)$ and
$X = \sum_{i,j} X_{ij}\, e_i \otimes f_j$, $Q(X) = \sum_{i,j,k,l} X_{ij} X_{kl} A_{ik} B_{jl}$ (Gram matrix
$A \otimes B$). -/
@[kb "kitaoka1993" "Ch. 7, p. 189 (tensor product L ⊗ M of positive lattices)"]
def tensorQ (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) (X : Matrix ι κ ℤ) : ℚ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (X i j : ℚ) * X k l * A i k * B j l

/-- **A minimal vector** of $L = (\mathbb Z^n, A)$ (Kitaoka 1993, §7.1, p. 190): $x \ne 0$ with
$Q(x) = \min(L) = \min\{Q(y) \mid 0 \ne y \in L\}$, i.e. $Q(x) \le Q(y)$ for every nonzero $y$. -/
@[kb "kitaoka1993" "§7.1, p. 190 (minimal vector, M(L))"]
def IsMinimalVector (A : Matrix ι ι ℚ) (x : ι → ℤ) : Prop :=
  x ≠ 0 ∧ ∀ y : ι → ℤ, y ≠ 0 → gramQ A x ≤ gramQ A y

/-- **A minimal vector of $L \otimes M$** (Kitaoka 1993, §7.1, p. 190): $X \ne 0$ in $L \otimes M$ with
$Q(X) \le Q(Y)$ for every nonzero $Y \in L \otimes M$. -/
@[kb "kitaoka1993" "§7.1, p. 190 (M(L ⊗ M))"]
def IsMinimalTensor (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) (X : Matrix ι κ ℤ) :
    Prop :=
  X ≠ 0 ∧ ∀ Y : Matrix ι κ ℤ, Y ≠ 0 → tensorQ A B X ≤ tensorQ A B Y

/-- **E-type** (Kitaoka 1993, §7.1, Definition, p. 190): the positive lattice $L = (\mathbb Z^n, A)$ is of E-type if
$\mathcal M(L \otimes M) \subseteq \{x \otimes y \mid x \in L, y \in M\}$ for every positive lattice $M$: every minimal
vector of $L \otimes M$ is split, $X = x y^{\mathsf T}$ with $x \in \mathbb Z^n$, $y \in \mathbb Z^m$. -/
@[kb "kitaoka1993" "§7.1, Definition, p. 190 (positive lattice of E-type)"]
def IsEType (A : Matrix ι ι ℚ) : Prop :=
  ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) ℚ), IsPosGram B →
    ∀ X : Matrix ι (Fin m) ℤ, IsMinimalTensor A B X → ∃ x : ι → ℤ, ∃ y : Fin m → ℤ, X = vecMulVec x y

/-- **Kitaoka 1993, Theorem 7.1.1** (p. 193), *stated*: every positive lattice $L$ with $\operatorname{rank} L < 43$
is of E-type. Kitaoka's proof uses the bound $\mu_r < \sqrt r$ on Hermite's constant for $2 \le r < 43$
(Lemma 7.1.2) and the inequality $\operatorname{tr} AB \ge n(|A||B|)^{1/n}$ (Lemma 7.1.3). -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.1, p. 193"]
def Theorem711 : Prop :=
  ∀ (n : ℕ), n < 43 → ∀ A : Matrix (Fin n) (Fin n) ℚ, IsPosGram A → IsEType A

/-! ### Section 7.4: Theorem 7.4.1 -/

/-- **Isometric positive lattices** in the Gram-matrix model: $(\mathbb Z^\kappa, A') \cong (\mathbb Z^\iota, A)$ iff
$A' = {}^t P A P$ for an integral matrix $P$ with an integral inverse. -/
def GramIsometric {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℚ) (A' : Matrix κ κ ℚ) : Prop :=
  ∃ (P : Matrix ι κ ℤ) (P' : Matrix κ ι ℤ), P * P' = 1 ∧ P' * P = 1 ∧
    A' = (P.map (Int.cast : ℤ → ℚ))ᵀ * A * P.map (Int.cast : ℤ → ℚ)

/-- **Indecomposable** (Kitaoka 1993, §7.2–7.4): $L \ne 0$, and $L \cong L_1 \perp L_2$ with positive lattices
$L_1$, $L_2$ forces $L_1 = 0$ or $L_2 = 0$ (ranks $a$, $b$; Gram matrix of $L_1 \perp L_2$ is `Matrix.fromBlocks`). -/
@[kb "kitaoka1993" "§7.4, p. 223 (indecomposable positive lattice)"]
def IsIndecomposable [DecidableEq ι] (A : Matrix ι ι ℚ) : Prop :=
  Nonempty ι ∧ ∀ (a b : ℕ) (A₁ : Matrix (Fin a) (Fin a) ℚ) (A₂ : Matrix (Fin b) (Fin b) ℚ),
    IsPosGram A₁ → IsPosGram A₂ → GramIsometric A (Matrix.fromBlocks A₁ 0 0 A₂) → a = 0 ∨ b = 0

/-- **Multiplicatively indecomposable** (Kitaoka 1993, §7.4, p. 223): $L \cong K_1 \otimes K_2$ for positive lattices
$K_1$, $K_2$ implies $\operatorname{rank} K_1 = 1$ or $\operatorname{rank} K_2 = 1$. -/
@[kb "kitaoka1993" "§7.4, p. 223 (multiplicatively indecomposable)"]
def IsMultIndecomposable [DecidableEq ι] (A : Matrix ι ι ℚ) : Prop :=
  ∀ (a b : ℕ) (K₁ : Matrix (Fin a) (Fin a) ℚ) (K₂ : Matrix (Fin b) (Fin b) ℚ),
    IsPosGram K₁ → IsPosGram K₂ → GramIsometric A (Matrix.kroneckerMap (· * ·) K₁ K₂) → a = 1 ∨ b = 1

/-- **$[L : \tilde L] < \infty$** (Kitaoka 1993, §7.4, p. 223), where $\tilde L$ is the sublattice spanned by the
minimal vectors $\mathcal M(L)$: the minimal vectors span $\mathbb Q^\iota$. -/
@[kb "kitaoka1993" "§7.4, p. 223 ([L : L̃] < ∞)"]
def MinSpanFull (A : Matrix ι ι ℚ) : Prop :=
  Submodule.span ℚ {v : ι → ℚ | ∃ x, IsMinimalVector A x ∧ v = fun i => (x i : ℚ)} = ⊤

/-- **$\tilde L$ is indecomposable**, in the form used in Kitaoka's proof of Lemma 7.4.1 (p. 223): the minimal vectors
cannot be split into two nonempty sets orthogonal to each other. (For a set $S$ not closed under $x \mapsto -x$ the
condition holds trivially with $y = -x$.) Every minimal vector of an orthogonal sum lies in one summand and
$\mathcal M(\tilde L) = \mathcal M(L)$, so this is equivalent to the indecomposability of $\tilde L$. -/
@[kb "kitaoka1993" "§7.4, p. 223 (L̃ indecomposable)"]
def MinConnected (A : Matrix ι ι ℚ) : Prop :=
  ∀ S : Set (ι → ℤ), (∃ x ∈ S, IsMinimalVector A x) → (∃ x, IsMinimalVector A x ∧ x ∉ S) →
    ∃ x y, IsMinimalVector A x ∧ IsMinimalVector A y ∧ x ∈ S ∧ y ∉ S ∧
      (fun i => (x i : ℚ)) ⬝ᵥ (A *ᵥ fun i => (y i : ℚ)) ≠ 0

/-- **Kitaoka 1993, Theorem 7.4.1 (i), (ii)** (p. 223), *stated*: let $L$ be a positive lattice of E-type such that
$[L : \tilde L] < \infty$ (`MinSpanFull`), $\tilde L$ is indecomposable (`MinConnected`) and $L$ is multiplicatively
indecomposable, where $\tilde L$ is the sublattice spanned by the minimal vectors $\mathcal M(L)$. Then for every
indecomposable positive lattice $X$: (i) $L \otimes X$ is indecomposable; (ii) $L \otimes X \cong L \otimes Y$ implies
$X \cong Y$ for every positive lattice $Y$. Part (iii) (generation of $O(L \otimes X)$) is not stated here. -/
@[kb "kitaoka1993" "§7.4, Thm. 7.4.1 (i), (ii), p. 223"]
def Theorem741 : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ), IsPosGram A → IsEType A → MinSpanFull A → MinConnected A →
    IsMultIndecomposable A →
    ∀ (k : ℕ) (X : Matrix (Fin k) (Fin k) ℚ), IsPosGram X → IsIndecomposable X →
      IsIndecomposable (Matrix.kroneckerMap (· * ·) A X) ∧
      ∀ (l : ℕ) (Y : Matrix (Fin l) (Fin l) ℚ), IsPosGram Y →
        GramIsometric (Matrix.kroneckerMap (· * ·) A X) (Matrix.kroneckerMap (· * ·) A Y) →
        GramIsometric X Y

/-- **Assertions (A1), (A2) of §7.2** (Kitaoka 1993, p. 199) for an indecomposable positive lattice $L$: for every
indecomposable positive lattice $X$, (A1) $L \otimes X$ is indecomposable, and (A2) $L \otimes X \cong L \otimes Y$
implies $X \cong Y$ for every positive lattice $Y$. (Assertion (A3), on generators of $O(L \otimes X)$, is not stated
here.) -/
@[kb "kitaoka1993" "§7.2, p. 199 (assertions (A1), (A2))"]
def AssertionA12 [DecidableEq ι] (A : Matrix ι ι ℚ) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k) (Fin k) ℚ), IsPosGram X → IsIndecomposable X →
    IsIndecomposable (Matrix.kroneckerMap (· * ·) A X) ∧
    ∀ (l : ℕ) (Y : Matrix (Fin l) (Fin l) ℚ), IsPosGram Y →
      GramIsometric (Matrix.kroneckerMap (· * ·) A X) (Matrix.kroneckerMap (· * ·) A Y) → GramIsometric X Y

/-- **Kitaoka 1993, Theorem 7.4.2** (p. 227), *stated* for assertions (A1), (A2): for an indecomposable binary
positive lattice $E$, assertion (A) of §7.2 holds for $L = E$; here its parts (A1) and (A2) (`AssertionA12`). -/
@[kb "kitaoka1993" "§7.4, Thm. 7.4.2, p. 227 ((A1), (A2))"]
def Theorem742 : Prop :=
  ∀ E : Matrix (Fin 2) (Fin 2) ℚ, IsPosGram E → IsIndecomposable E → AssertionA12 E

/-- **Kitaoka 1993, Corollary 7.4.1** (p. 223), *stated*: let $L$ be a positive lattice of E-type with
$[L : \tilde L] < \infty$ and $\tilde L$ indecomposable. If $L \cong L_1 \otimes L_2$ for positive lattices $L_1$,
$L_2$, then $L_1$, $L_2$ are of E-type, $[L_i : \tilde L_i] < \infty$ and $\tilde L_i$ is indecomposable. -/
@[kb "kitaoka1993" "§7.4, Cor. 7.4.1, p. 223"]
def Corollary741 : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ), IsPosGram A → IsEType A → MinSpanFull A → MinConnected A →
    ∀ (a b : ℕ) (A₁ : Matrix (Fin a) (Fin a) ℚ) (A₂ : Matrix (Fin b) (Fin b) ℚ), IsPosGram A₁ → IsPosGram A₂ →
      GramIsometric A (Matrix.kroneckerMap (· * ·) A₁ A₂) →
      (IsEType A₁ ∧ MinSpanFull A₁ ∧ MinConnected A₁) ∧ (IsEType A₂ ∧ MinSpanFull A₂ ∧ MinConnected A₂)

/-- **The Gram matrix of a tensor product** $L_0 \otimes \cdots \otimes L_{k-1}$ of lattices
$L_i = (\mathbb Z^{r_i}, A_i)$ in the basis $e_{x_0} \otimes \cdots \otimes e_{x_{k-1}}$, indexed by
$x \in \prod_i \mathrm{Fin}\, r_i$: the entry at $(x, y)$ is $\prod_i (A_i)_{x_i y_i}$. -/
def tensorGram {k : ℕ} {r : Fin k → ℕ} (A : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℚ) :
    Matrix (∀ i, Fin (r i)) (∀ i, Fin (r i)) ℚ :=
  Matrix.of fun x y => ∏ i, A i (x i) (y i)

/-- **Kitaoka 1993, Theorem 7.4.3** (p. 236), *stated*: let $L_0, \dots, L_{k-1}$ be positive lattices of E-type with
$\operatorname{rank} L_i > 1$, $[L_i : \tilde L_i] < \infty$, $\tilde L_i$ indecomposable and $L_i$ multiplicatively
indecomposable, and let $M_0, \dots, M_{l-1}$ be multiplicatively indecomposable positive lattices with
$\operatorname{rank} M_j > 1$. If $\bigotimes_i L_i \cong \bigotimes_j M_j$, then $k = l$ and, after renumbering,
$L_i \cong M_i^{a_i}$ (the scaling of $M_i$ by a rational $a_i > 0$, Gram matrix $a_i B_i$). Kitaoka also states that
the given isometry is the tensor product $\otimes \sigma_i$ of such isometries; that refinement is not stated here.
The renumbering is a bijection $\pi : \mathrm{Fin}\, k \to \mathrm{Fin}\, l$. -/
@[kb "kitaoka1993" "§7.4, Thm. 7.4.3, p. 236"]
def Theorem743 : Prop :=
  ∀ (k l : ℕ) (r : Fin k → ℕ) (s : Fin l → ℕ) (A : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℚ)
    (B : ∀ j, Matrix (Fin (s j)) (Fin (s j)) ℚ),
    (∀ i, IsPosGram (A i) ∧ IsEType (A i) ∧ 1 < r i ∧ MinSpanFull (A i) ∧ MinConnected (A i) ∧
      IsMultIndecomposable (A i)) →
    (∀ j, IsPosGram (B j) ∧ 1 < s j ∧ IsMultIndecomposable (B j)) →
    GramIsometric (tensorGram A) (tensorGram B) →
    k = l ∧ ∃ π : Fin k ≃ Fin l, ∀ i, ∃ a : ℚ, 0 < a ∧ GramIsometric (A i) (a • B (π i))

/-! ### Lemma 7.1.1 (2), (3), (iii), Theorem 7.1.2, Lemma 7.1.4 -/

/-- **Kitaoka 1993, Lemma 7.1.1 (3)** (p. 191), *stated*: if $L$ is of E-type, then for every positive lattice $M$,
$\min(L \otimes M) = \min(L)\min(M)$ and $\mathcal M(L \otimes M) = \mathcal M(L) \otimes \mathcal M(M)$
$= \{x \otimes y \mid x \in \mathcal M(L), y \in \mathcal M(M)\}$. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (3), p. 191"]
def Lemma711eq : Prop :=
  ∀ {ι : Type} [Fintype ι] (A : Matrix ι ι ℚ), IsPosGram A → IsEType A →
    ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) ℚ), IsPosGram B →
      (∀ X x y, IsMinimalTensor A B X → IsMinimalVector A x → IsMinimalVector B y →
        tensorQ A B X = gramQ A x * gramQ B y) ∧
      ∀ X, IsMinimalTensor A B X ↔ ∃ x y, IsMinimalVector A x ∧ IsMinimalVector B y ∧ X = vecMulVec x y

/-- **Kitaoka 1993, Lemma 7.1.1 (iii)** (p. 191), *stated*: if $L = (\mathbb Z^\iota, A)$ is of E-type and $M$ is a
submodule of $L$ with $\min(M) = \min(L)$, then $M$ is of E-type. The submodule $M$ has the basis given by the columns
of an integral matrix $P \in M_{\iota \times k}(\mathbb Z)$ with linearly independent columns, and Gram matrix
$P^{\mathsf T} A P$; $\min(M) = \min(L)$ is written with minimal vectors $x$ of $L$ and $y$ of $M$. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (iii), p. 191"]
def Lemma711iii : Prop :=
  ∀ {ι : Type} [Fintype ι] (A : Matrix ι ι ℚ) (k : ℕ) (P : Matrix ι (Fin k) ℤ), IsPosGram A → IsEType A →
    Function.Injective (P.map (Int.cast : ℤ → ℚ)).mulVec →
    (∀ x y, IsMinimalVector A x →
      IsMinimalVector ((P.map (Int.cast : ℤ → ℚ))ᵀ * A * P.map (Int.cast : ℤ → ℚ)) y →
      gramQ ((P.map (Int.cast : ℤ → ℚ))ᵀ * A * P.map (Int.cast : ℤ → ℚ)) y = gramQ A x) →
    IsEType ((P.map (Int.cast : ℤ → ℚ))ᵀ * A * P.map (Int.cast : ℤ → ℚ))

/-- **Kitaoka 1993, Theorem 7.1.2** (p. 194), *stated*: a positive lattice $L$ with $\mathfrak sL \subseteq \mathbb Z$
(all $B(e_i, e_j) \in \mathbb Z$) and $\min(L) \le 6$ (some nonzero $x \in L$ has $Q(x) \le 6$) is of E-type. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.2, p. 194"]
def Theorem712 : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ), IsPosGram A → (∀ i j, ∃ z : ℤ, A i j = z) →
    (∃ x : Fin n → ℤ, x ≠ 0 ∧ gramQ A x ≤ 6) → IsEType A

/-- **Kitaoka 1993, Lemma 7.1.4** (p. 194), *stated*: Hermite's constant satisfies $\mu_n < n/6$ for $n \ge 40$. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.4, p. 194"]
def Lemma714 : Prop :=
  ∀ n : ℕ, 40 ≤ n → Reduction.hermiteConst n < (n : ℝ) / 6

/-- **Kitaoka 1993, Lemma 7.1.1 (ii)** (p. 191), *stated*: if $L = (\mathbb Z^\iota, A)$ and $M = (\mathbb Z^\kappa, B)$
are of E-type, then so are $L \perp M$ (Gram matrix $\begin{pmatrix} A & 0 \\ 0 & B\end{pmatrix}$ on
$\iota \sqcup \kappa$, `Matrix.fromBlocks`) and $L \otimes M$ (Gram matrix $A \otimes B$ on $\iota \times \kappa$,
`Matrix.kroneckerMap`). -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (ii), p. 191"]
def Lemma711ii : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ),
    IsPosGram A → IsPosGram B → IsEType A → IsEType B →
      IsEType (Matrix.fromBlocks A 0 0 B) ∧ IsEType (Matrix.kroneckerMap (· * ·) A B)

/-- **Kitaoka 1993, Lemma 7.1.2** (p. 192), *stated*: Hermite's constant satisfies $\mu_r < \sqrt r$ for
$2 \le r < 43$ (`Reduction.hermiteConst`, Chapter 2). -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.2, p. 192"]
def Lemma712 : Prop :=
  ∀ r : ℕ, 2 ≤ r → r < 43 → Reduction.hermiteConst r < Real.sqrt r

/-- **Kitaoka 1993, Lemma 7.1.3** (p. 193), *stated*: for positive definite real symmetric $n \times n$ matrices $A$,
$B$, $\operatorname{tr} AB \ge n\,(|A|\,|B|)^{1/n}$, where $|A| = \det A$. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.3, p. 193"]
def Lemma713 : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ), A.PosDef → B.PosDef →
    (n : ℝ) * (A.det * B.det) ^ ((1 : ℝ) / n) ≤ (A * B).trace

/-- $Q(x) = \sum_{i,k} x_i x_k A_{ik}$. -/
theorem gramQ_eq_sum (A : Matrix ι ι ℚ) (z : ι → ℤ) : gramQ A z = ∑ i, ∑ k, (z i : ℚ) * z k * A i k := by
  simp only [gramQ, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- **$Q(x \otimes y) = Q(x)Q(y)$** (Kitaoka 1993, §7.1, p. 190): the value of the tensor form on a split element is
the product of the values. -/
@[kb "kitaoka1993" "§7.1, p. 190 (Q(x ⊗ y) = Q(x)Q(y))"]
theorem tensorQ_vecMulVec (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) (x : ι → ℤ)
    (y : κ → ℤ) : tensorQ A B (vecMulVec x y) = gramQ A x * gramQ B y := by
  rw [gramQ_eq_sum A x, gramQ_eq_sum B y, Finset.sum_mul_sum]
  simp only [tensorQ, vecMulVec_apply, Int.cast_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **Kitaoka 1993, Lemma 7.1.1 (i)** (p. 191): a positive lattice of rank $1$ is of E-type. *Proof:* every element
$X$ of $L \otimes M$ (a $1 \times m$ integer matrix) is $e_0 \otimes y$ with $y = X_{0\,\cdot}$, so it is split. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (i), p. 191"]
theorem isEType_of_rank_one (A : Matrix (Fin 1) (Fin 1) ℚ) : IsEType A := by
  intro m B _ X _
  refine ⟨fun _ => 1, X 0, ?_⟩
  ext i j
  simp [vecMulVec_apply, Subsingleton.elim i 0]

omit [Fintype ι] [Fintype κ] in
/-- $x \otimes y \ne 0$ for $x, y \ne 0$. -/
theorem vecMulVec_ne_zero {x : ι → ℤ} {y : κ → ℤ} (hx : x ≠ 0) (hy : y ≠ 0) : vecMulVec x y ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  intro h
  have := congrFun (congrFun h i) j
  simp only [vecMulVec_apply, Matrix.zero_apply] at this
  exact mul_ne_zero hi hj this

/-- **Kitaoka 1993, Lemma 7.1.1 (2)** (p. 191): $\min(L \otimes M) \le \min(L)\min(M)$. For minimal vectors $X$ of
$L \otimes M$, $x$ of $L$ and $y$ of $M$: $Q(X) \le Q(x \otimes y) = Q(x)Q(y)$, since $x \otimes y \ne 0$. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (2), p. 191"]
theorem tensorQ_le_of_isMinimal {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} {X : Matrix ι κ ℤ} {x : ι → ℤ}
    {y : κ → ℤ} (hX : IsMinimalTensor A B X) (hx : IsMinimalVector A x) (hy : IsMinimalVector B y) :
    tensorQ A B X ≤ gramQ A x * gramQ B y := by
  rw [← tensorQ_vecMulVec]
  exact hX.2 _ (vecMulVec_ne_zero hx.1 hy.1)

end QuadFormsKB.Kitaoka.EType
