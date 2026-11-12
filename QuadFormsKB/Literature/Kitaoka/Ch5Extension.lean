/-
# Kitaoka 1993, Sections 5.3–5.4: extending isometries of sublattices over $\mathbb Z_p$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), Chapter 5, p. 70 (setting), §5.1, p. 70 (dual
lattice), §5.3, Theorem 5.3.4, p. 82, §5.4, Theorem 5.4.1 (Eichler), p. 86. Printed page numbers.

**Setting** (Kitaoka, p. 70): $p$ is a prime, $R = \mathbb Z_p$, $F = \mathbb Q_p$, and $(a) = aR$ for $a \in F$. A
quadratic space is $V = F^n$ with a quadratic form $Q$ (Mathlib `QuadraticForm ℚ_[p] (Fin n → ℚ_[p])`), with
Kitaoka's bilinear form $B(x, y) = \tfrac12(Q(x+y) - Q(x) - Q(y))$ (`pbil`, so $B(x,x) = Q(x)$). A regular quadratic
lattice over $R$ is a lattice $L$ on $V$ (Mathlib `Submodule.IsLattice`: finitely generated, spanning $V$) with $V$
regular ($B$ nondegenerate). A submodule $M$ of $L$ may have smaller rank.

**Defines**
* `InIdeal a x`: $x \in (a)$, i.e. $x = ar$ for some $r \in \mathbb Z_p$;
* `upperL Q L a` $= L^a = \{x \in L \mid B(x, L) \subseteq (a)\}$ and `lowerL Q L a` $= L_a = \{x \in L^a \mid Q(x) \in (2a)\}$
  (Theorem 5.3.4);
* `dualL Q L` $= L^\sharp = \{x \in V \mid B(x, L) \subseteq R\}$ (§5.1, p. 70);
* `ExtendsToIsometryOf Q L σ S`: the isometry $\sigma : M \cong N$ extends to an isometry $\tau$ of $L$ ($\tau \in O(V)$,
  $\tau L = L$, $\tau|_M = \sigma$) with $\tau(x) \equiv x \bmod S$ for every $x \in L$;
* `Theorem534`, `Theorem541`: the statements of Theorems 5.3.4 and 5.4.1 (stated).
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import QuadFormsKB.Citation

open QuadraticMap

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **$x \in (a)$** for the principal fractional ideal $(a) = a\mathbb Z_p$ of $\mathbb Q_p$ (Kitaoka 1993, Chapter 5,
p. 70): $x = ar$ for some $r \in \mathbb Z_p$. -/
def InIdeal (a x : ℚ_[p]) : Prop := ∃ r : ℤ_[p], x = a * r

/-- **Kitaoka's bilinear form** $B(x, y) = \tfrac12\bigl(Q(x + y) - Q(x) - Q(y)\bigr)$ of a quadratic form on
$\mathbb Q_p^n$ (Kitaoka 1993, §1.1; $B(x,x) = Q(x)$). -/
def pbil (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (x y : Fin n → ℚ_[p]) : ℚ_[p] := polar Q x y / 2

/-- **The set $L^a = \{x \in L \mid B(x, L) \subseteq (a)\}$** (Kitaoka 1993, Theorem 5.3.4, p. 82). -/
@[kb "kitaoka1993" "§5.3, Thm. 5.3.4, p. 82 (L^a)"]
def upperL (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (L : Submodule ℤ_[p] (Fin n → ℚ_[p])) (a : ℚ_[p]) :
    Set (Fin n → ℚ_[p]) :=
  {x | x ∈ L ∧ ∀ y ∈ L, InIdeal a (pbil Q x y)}

/-- **The set $L_a = \{x \in L^a \mid Q(x) \in (2a)\}$** (Kitaoka 1993, Theorem 5.3.4, p. 82). -/
@[kb "kitaoka1993" "§5.3, Thm. 5.3.4, p. 82 (L_a)"]
def lowerL (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (L : Submodule ℤ_[p] (Fin n → ℚ_[p])) (a : ℚ_[p]) :
    Set (Fin n → ℚ_[p]) :=
  {x | x ∈ upperL Q L a ∧ InIdeal (2 * a) (Q x)}

/-- **The dual lattice** $L^\sharp = \{x \in V \mid B(x, L) \subseteq R\}$ (Kitaoka 1993, §5.1, p. 70). -/
@[kb "kitaoka1993" "§5.1, p. 70 (dual lattice L^♯)"]
def dualL (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (L : Submodule ℤ_[p] (Fin n → ℚ_[p])) :
    Set (Fin n → ℚ_[p]) :=
  {x | ∀ y ∈ L, InIdeal 1 (pbil Q x y)}

/-- **$\sigma$ extends to an isometry of $L$ congruent to the identity modulo $S$** (the conclusion of Kitaoka's
Theorems 5.3.4 and 5.4.1): there is a $\mathbb Q_p$-linear isometry $\tau$ of $V$ with $\tau(L) = L$, $\tau(x) = \sigma(x)$
for $x \in M$, and $\tau(x) - x \in S$ for every $x \in L$. -/
def ExtendsToIsometryOf (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (L : Submodule ℤ_[p] (Fin n → ℚ_[p]))
    {M N : Submodule ℤ_[p] (Fin n → ℚ_[p])} (σ : M ≃ₗ[ℤ_[p]] N) (S : Set (Fin n → ℚ_[p])) : Prop :=
  ∃ τ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]),
    (∀ x, Q (τ x) = Q x) ∧ (∀ x ∈ L, τ x ∈ L) ∧ (∀ x ∈ L, τ.symm x ∈ L) ∧
    (∀ x : M, τ x = σ x) ∧ (∀ x ∈ L, τ x - x ∈ S)

/-- **Kitaoka 1993, Theorem 5.3.4** (p. 82), *stated*. Let $L$ be a regular quadratic lattice over $R = \mathbb Z_p$
and $M$, $N$ submodules of $L$. For $a \in F^\times$ put $L^a = \{x \in L \mid B(x, L) \subseteq (a)\}$ and
$L_a = \{x \in L^a \mid Q(x) \in (2a)\}$. Suppose that $M$ and $N$ satisfy
(3) $\mathrm{Hom}_R(M, R) = \{x \mapsto a^{-1}B(x, y) \mid y \in L_a\}$ and the same for $N$.
If $\sigma : M \cong N$ (an isometry of $M$ onto $N$) satisfies (4) $\sigma(x) \equiv x \bmod L^a$ for $x \in M$, then
$\sigma$ extends to an isometry of $L$ with $\sigma(x) \equiv x \bmod L_a$ for $x \in L$.

*Encoding of (3).* Both inclusions are written out: every $R$-linear $f : M \to R$ is $x \mapsto a^{-1}B(x, y)$ for some
$y \in L_a$, and for every $y \in L_a$ the map $x \mapsto a^{-1}B(x, y)$ is $R$-valued and $R$-linear on $M$ (this
second inclusion holds automatically, as $M \subseteq L$ and $L_a \subseteq L^a$). -/
@[kb "kitaoka1993" "§5.3, Thm. 5.3.4, p. 82"]
def Theorem534 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    (L M N : Submodule ℤ_[p] (Fin n → ℚ_[p])) (a : ℚ_[p]),
    (polarBilin Q).Nondegenerate → L.IsLattice ℚ_[p] → M ≤ L → N ≤ L → a ≠ 0 →
    (∀ f : M →ₗ[ℤ_[p]] ℤ_[p], ∃ y ∈ lowerL Q L a, ∀ x : M, (f x : ℚ_[p]) = a⁻¹ * pbil Q x y) →
    (∀ y ∈ lowerL Q L a, ∃ f : M →ₗ[ℤ_[p]] ℤ_[p], ∀ x : M, (f x : ℚ_[p]) = a⁻¹ * pbil Q x y) →
    (∀ f : N →ₗ[ℤ_[p]] ℤ_[p], ∃ y ∈ lowerL Q L a, ∀ x : N, (f x : ℚ_[p]) = a⁻¹ * pbil Q x y) →
    (∀ y ∈ lowerL Q L a, ∃ f : N →ₗ[ℤ_[p]] ℤ_[p], ∀ x : N, (f x : ℚ_[p]) = a⁻¹ * pbil Q x y) →
    ∀ σ : M ≃ₗ[ℤ_[p]] N, (∀ x : M, Q (σ x) = Q x) →
      (∀ x : M, ((σ x : Fin n → ℚ_[p]) - x) ∈ upperL Q L a) →
      ExtendsToIsometryOf Q L σ (lowerL Q L a)

/-- **Kitaoka 1993, Theorem 5.4.1** (p. 86; essentially due to Eichler), *stated*. Let $L$ be a regular quadratic lattice
over $R = \mathbb Z_p$ and $M$, $N$ isometric submodules of $L$. Put $\tilde M := FM \cap L$, $\tilde N := FN \cap L$ and
suppose
$$\tilde M/M \cong \tilde N/N \cong R/(p^{a_1}) \oplus \cdots \oplus R/(p^{a_r}), \qquad 0 \le a_1 \le \cdots \le a_r$$
as $R$-modules. Take $a \in F^\times$ with $a\,\mathfrak n(L^\sharp) \subseteq (2)$. If $\sigma : M \cong N$ satisfies
$\sigma(x) \equiv x \bmod a p^{a_r} L^\sharp$ for every $x \in M$, then $\sigma$ can be extended to an isometry of $L$ with
$\sigma(x) \equiv x \bmod aL^\sharp$ for $x \in L$.

*Encoding.* The exponents are `e : Fin r → ℕ` (monotone, 0-based: Kitaoka's $a_1, \dots, a_r$ are `e 0, …, e (r-1)`),
with largest value $a_r$ = `Finset.univ.sup e` ($0$ when $r = 0$, i.e. $\tilde M = M$); the quotient $\tilde M/M$ is
`M̃ ⧸ M.comap M̃.subtype`. The norm $\mathfrak n(L^\sharp)$ is the ideal generated by $Q(L^\sharp)$, so
$a\,\mathfrak n(L^\sharp) \subseteq (2)$ means $aQ(x) \in (2)$ for every $x \in L^\sharp$. "$x \equiv y \bmod cL^\sharp$"
means $x - y = cz$ with $z \in L^\sharp$. Kitaoka writes $n$ for the number of summands; here it is `r`, and $n$ is the
dimension. -/
@[kb "kitaoka1993" "§5.4, Thm. 5.4.1, p. 86"]
def Theorem541 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    (L M N : Submodule ℤ_[p] (Fin n → ℚ_[p])) (a : ℚ_[p]) (r : ℕ) (e : Fin r → ℕ),
    (polarBilin Q).Nondegenerate → L.IsLattice ℚ_[p] → M ≤ L → N ≤ L → a ≠ 0 → Monotone e →
    let Mt : Submodule ℤ_[p] (Fin n → ℚ_[p]) := (Submodule.span ℚ_[p] (M : Set _)).restrictScalars ℤ_[p] ⊓ L
    let Nt : Submodule ℤ_[p] (Fin n → ℚ_[p]) := (Submodule.span ℚ_[p] (N : Set _)).restrictScalars ℤ_[p] ⊓ L
    Nonempty ((Mt ⧸ M.comap Mt.subtype) ≃ₗ[ℤ_[p]] ((i : Fin r) → ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ e i})) →
    Nonempty ((Nt ⧸ N.comap Nt.subtype) ≃ₗ[ℤ_[p]] ((i : Fin r) → ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ e i})) →
    (∀ x ∈ dualL Q L, InIdeal 2 (a * Q x)) →
    ∀ σ : M ≃ₗ[ℤ_[p]] N, (∀ x : M, Q (σ x) = Q x) →
      (∀ x : M, ∃ z ∈ dualL Q L, (σ x : Fin n → ℚ_[p]) - x = (a * (p : ℚ_[p]) ^ Finset.univ.sup e) • z) →
      ExtendsToIsometryOf Q L σ {w | ∃ z ∈ dualL Q L, w = a • z}

end QuadFormsKB.Kitaoka.Padic
