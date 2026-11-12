/-
# Kitaoka 1993, Sections 1.3, 1.5 and 3.5: finite fields, quaternion algebras, representations over $\mathbb Q_p$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.2, Theorem 1.2.2, p. 6; §1.3, Theorem 1.3.1, p. 14; §1.5, pp. 24–27
(quaternion algebras, Propositions 1.5.2 and 1.5.4); §3.5, Corollary 3.5.4, p. 63. Printed page numbers.

**Setting.** Quadratic spaces are Mathlib quadratic forms `QuadraticForm F V` on finite-dimensional vector spaces.
Kitaoka (Chapter 1) calls a quadratic space $(V, q)$ *regular* when the bilinear form $b(x, y) = q(x+y) - q(x) - q(y)$
is nondegenerate, which is `(QuadraticMap.polarBilin q).Nondegenerate`. Isometry of spaces is
`QuadraticMap.Equivalent`, the orthogonal sum is `QuadraticMap.prod`, the hyperbolic plane $H$ and the hyperbolic
space $H^k$ are `QuadraticForm.hyperbolicPlane` and `QuadraticForm.hyperbolicSpace` (`Witt/Decomposition.lean`).

A quaternion algebra $(\alpha, \beta)$ over $F$ (§1.5, p. 24; characteristic $\ne 2$) has a basis $1, x_1, x_2, x_3$ with
$x_1^2 = \alpha$, $x_2^2 = \beta$, $x_3 = x_1x_2 = -x_2x_1$, $\alpha, \beta \in F^\times$; this is Mathlib's
$ℍ[F, \alpha, 0, \beta]$ (notation `ℍ[F,α,β]`). Its norm is
$N(a_0 + a_1x_1 + a_2x_2 + a_3x_3) = a_0^2 - \alpha a_1^2 - \beta a_2^2 + \alpha\beta a_3^2$, so
$(C, N) \cong \langle 1\rangle \perp \langle -\alpha\rangle \perp \langle -\beta\rangle \perp \langle \alpha\beta\rangle$ and
its restriction to the pure quaternions $C^0 = Fx_1 + Fx_2 + Fx_3$ is
$(C, N)^0 \cong \langle -\alpha\rangle \perp \langle -\beta\rangle \perp \langle \alpha\beta\rangle$ (p. 25).

**Defines** `quatNorm α β` ($N$ on $(\alpha,\beta)$ as a quadratic form, through the coordinates
`QuaternionAlgebra.linearEquivTuple`), `quatNormPure α β` ($(C, N)^0$ in the coordinates $a_1, a_2, a_3$), `quatConj`
($x \mapsto \bar x$ as a linear map), and the statements `Theorem122`, `Theorem131`, `Proposition152`, `Proposition154`,
`Corollary354` (stated).
-/
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.Padics.PadicNumbers
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Literature.OMeara.Sec6Defs

open QuadraticMap Quaternion

noncomputable section

namespace QuadFormsKB.Kitaoka

/-! ### Theorem 1.2.2: Kneser's theorem of Witt type -/

/-- **Kitaoka 1993, Theorem 1.2.2** (Kneser, p. 6), *stated*. Let $\tilde R \supseteq R$ be rings and $P$ a proper ideal
of $R$ with $R = R^\times \cup P$ and $R^\times \cap P = \emptyset$ (so $R$ is a local ring with maximal ideal $P$;
written `IsLocalRing R`, with $R \to \tilde R$ injective). Let $U$ be a quadratic module over $\tilde R$ (form $q$,
$b(x, y) = q(x+y) - q(x) - q(y)$, `QuadraticMap.polar`) and $L, M, N, H$ finitely generated $R$-submodules of $U$ with
$M$, $N$ free and $L \supseteq M, N, H$. Suppose
(1) $q(H) \subseteq R$, $b(L, H) \subseteq R$;
(2a) $\operatorname{Hom}_R(M, R) = \{x \mapsto b(x, y) \mid y \in H\}$, (2b) the same for $N$
(only "$\subseteq$" is written; "$\supseteq$" follows from (1));
and $\sigma : M \cong N$ is an isometry with (3) $\sigma(x) \equiv x \bmod H$ for $x \in M$. Then $\sigma$ extends to an
element $\tau$ of $O(L)$ (an $R$-linear bijection of $L$ preserving $q$) with (4) $\tau = \mathrm{id}$ on $H^\perp$
(the $x \in L$ with $b(x, H) = 0$) and (3) for every $x \in L$. -/
@[kb "kitaoka1993" "§1.2, Thm. 1.2.2, p. 6"]
def Theorem122 : Prop :=
  ∀ (R Rt U : Type) [CommRing R] [IsLocalRing R] [CommRing Rt] [Algebra R Rt] [AddCommGroup U] [Module Rt U]
    [Module R U] [IsScalarTower R Rt U] (q : QuadraticForm Rt U) (L M N H : Submodule R U),
    Function.Injective (algebraMap R Rt) → L.FG → M.FG → N.FG → H.FG → Module.Free R M → Module.Free R N →
    ∀ (hM : M ≤ L) (_ : N ≤ L) (_ : H ≤ L),
    (∀ h ∈ H, q h ∈ (algebraMap R Rt).range) → (∀ x ∈ L, ∀ h ∈ H, polar q x h ∈ (algebraMap R Rt).range) →
    (∀ f : M →ₗ[R] R, ∃ y ∈ H, ∀ x : M, algebraMap R Rt (f x) = polar q x y) →
    (∀ f : N →ₗ[R] R, ∃ y ∈ H, ∀ x : N, algebraMap R Rt (f x) = polar q x y) →
    ∀ σ : M ≃ₗ[R] N, (∀ x, q (σ x) = q x) → (∀ x, (σ x : U) - x ∈ H) →
    ∃ τ : L ≃ₗ[R] L, (∀ x, q (τ x) = q x) ∧ (∀ x : M, (τ ⟨x, hM x.2⟩ : U) = σ x) ∧
      (∀ x : L, (∀ h ∈ H, polar q x h = 0) → τ x = x) ∧ ∀ x : L, (τ x : U) - x ∈ H

/-! ### Theorem 1.3.1: regular quadratic spaces over a finite field -/

/-- **Kitaoka 1993, Theorem 1.3.1** (p. 14), *stated*: a regular quadratic space $V$ over a finite field $F$ which is
not hyperbolic is isometric to $H^k \perp W$ with $W$ an anisotropic $2$-dimensional space ($\cong (F', N)$ for the
quadratic extension $F'$ of $F$, Proposition 1.3.1), or to $H^k \perp \langle a\rangle$ with $a \ne 0$; the latter only
when $\operatorname{char} F \ne 2$. Written as a three-way alternative including the hyperbolic case $V \cong H^k$. -/
@[kb "kitaoka1993" "§1.3, Thm. 1.3.1, p. 14"]
def Theorem131 : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), (polarBilin Q).Nondegenerate →
    ∃ k : ℕ, Q.Equivalent (QuadraticForm.hyperbolicSpace F k) ∨
      (∃ W : QuadraticForm F (Fin 2 → F), W.Anisotropic ∧
        Q.Equivalent ((QuadraticForm.hyperbolicSpace F k).prod W)) ∨
      (ringChar F ≠ 2 ∧ ∃ a : F, a ≠ 0 ∧
        Q.Equivalent ((QuadraticForm.hyperbolicSpace F k).prod (weightedSumSquares F ![a])))

/-! ### Section 1.5: quaternion algebras -/

section Quaternion

variable {F : Type} [Field F]

/-- **The norm form $(C, N)$ of the quaternion algebra $C = (\alpha, \beta)$** (Kitaoka 1993, §1.5, p. 25):
$N(a_0 + a_1x_1 + a_2x_2 + a_3x_3) = a_0^2 - \alpha a_1^2 - \beta a_2^2 + \alpha\beta a_3^2$, as a quadratic form on
$ℍ[F, \alpha, \beta]$ (through the coordinates $(a_0, a_1, a_2, a_3)$, `QuaternionAlgebra.linearEquivTuple`). -/
@[kb "kitaoka1993" "§1.5, p. 25 (norm form (C, N))"]
def quatNorm (α β : F) : QuadraticForm F ℍ[F,α,β] :=
  (weightedSumSquares F ![1, -α, -β, α * β]).comp
    (QuaternionAlgebra.linearEquivTuple (R := F) α 0 β).toLinearMap

/-- **The pure part $(C, N)^0$** (Kitaoka 1993, §1.5, p. 25): the norm on $C^0 = Fx_1 + Fx_2 + Fx_3$ in the
coordinates $(a_1, a_2, a_3)$, i.e. $\langle -\alpha\rangle \perp \langle -\beta\rangle \perp \langle \alpha\beta\rangle$. -/
@[kb "kitaoka1993" "§1.5, p. 25 ((C, N)⁰)"]
def quatNormPure (α β : F) : QuadraticForm F (Fin 3 → F) :=
  weightedSumSquares F ![-α, -β, α * β]

/-- **The conjugation** $x \mapsto \bar x$ of $(\alpha, \beta)$ (Kitaoka 1993, §1.5, p. 25) as an $F$-linear map. -/
def quatConj (α β : F) : ℍ[F,α,β] →ₗ[F] ℍ[F,α,β] :=
  (MulOpposite.opLinearEquiv F).symm.toLinearMap ∘ₗ (QuaternionAlgebra.starAe (R := F)).toLinearMap

/-- **Kitaoka 1993, Proposition 1.5.2** (p. 25), *stated*: for quaternion algebras $C = (\alpha, \beta)$ and
$D = (\gamma, \delta)$ over a field $F$ of characteristic $\ne 2$, the following are equivalent: (i) $C \cong D$ as
$F$-algebras; (ii) $(C, N) \cong (D, N)$; (iii) $(C, N)^0 \cong (D, N)^0$. -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.2, p. 25"]
def Proposition152 : Prop :=
  ∀ (F : Type) [Field F], (2 : F) ≠ 0 → ∀ α β γ δ : F, α ≠ 0 → β ≠ 0 → γ ≠ 0 → δ ≠ 0 →
    List.TFAE [Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]), (quatNorm α β).Equivalent (quatNorm γ δ),
      (quatNormPure α β).Equivalent (quatNormPure γ δ)]

/-- **Kitaoka 1993, Proposition 1.5.4** (p. 27), *stated*: for $\alpha, \beta \in F^\times$ ($\operatorname{char} F \ne 2$)
and $C = (\alpha, \beta)$:
(i) $O^+(C, N) = \{x \mapsto a x b \mid a, b \in C,\ N(ab) = 1\}$: a linear map $f$ of $C$ preserves $N$ and has
determinant $1$ iff $f(x) = axb$ for some $a, b$ with $N(ab) = 1$;
(ii) $x \mapsto \bar x$ is an isometry of $(C, N)$, not in $O^+$ (its determinant is not $1$);
(iii) for a pure $u$ with $N(u) \ne 0$, the symmetry $\tau_u(x) = x - \frac{T(x\bar u)}{N(u)}u$ of $(C, N)^0$ (with
$T(y) = y + \bar y$, so $N(x+y) - N(x) - N(y) = T(x\bar y)$) is $\tau_u(x) = -uxu^{-1}$ for pure $x$, where
$u^{-1} = N(u)^{-1}\bar u$. Pure means $\operatorname{re} x = 0$. -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.4, p. 27"]
def Proposition154 : Prop :=
  ∀ (F : Type) [Field F], (2 : F) ≠ 0 → ∀ α β : F, α ≠ 0 → β ≠ 0 →
    (∀ f : ℍ[F,α,β] →ₗ[F] ℍ[F,α,β], ((∀ x, quatNorm α β (f x) = quatNorm α β x) ∧ LinearMap.det f = 1) ↔
      ∃ a b : ℍ[F,α,β], quatNorm α β (a * b) = 1 ∧ ∀ x, f x = a * x * b) ∧
    ((∀ x, quatNorm α β (quatConj α β x) = quatNorm α β x) ∧ LinearMap.det (quatConj α β) ≠ 1) ∧
    ∀ u x : ℍ[F,α,β], u.re = 0 → x.re = 0 → quatNorm α β u ≠ 0 →
      x - ((x * star u + star (x * star u)).re / quatNorm α β u) • u =
        -(u * x * ((quatNorm α β u)⁻¹ • star u))

end Quaternion

/-! ### Corollary 3.5.4: representations of quadratic spaces over $\mathbb Q_p$ -/

/-- **Kitaoka 1993, Corollary 3.5.4** (p. 63), *stated*: let $U$, $V$ be regular quadratic spaces over $\mathbb Q_p$
with $\dim U \le \dim V$. Then $U$ is represented by $V$ (`OMeara.IsRepresentedBy`: an injective isometry $U \to V$)
iff $\dim V - \dim U \ge 3$, or
* $V \cong U$ if $\dim V = \dim U$,
* $V \cong U \perp \langle dU \cdot dV\rangle$ if $\dim V = \dim U + 1$,
* $V \cong U \perp H$ if $\dim V = \dim U + 2$ and $dV = -dU$ (in $\mathbb Q_p^\times/(\mathbb Q_p^\times)^2$),
where $dU$ is the determinant of $U$ (`QuadraticMap.discr'`, the determinant of the Gram matrix of $B$ with
$Q(x) = B(x, x)$) and $H$ is the hyperbolic plane. In the case $\dim V = \dim U + 2$ with $dV \ne -dU$ no condition
is imposed (Kitaoka's proof: then $U$ is always represented). Spaces are $\mathbb Q_p^m$, $\mathbb Q_p^n$; regular
means $dU, dV \ne 0$. -/
@[kb "kitaoka1993" "§3.5, Cor. 3.5.4, p. 63"]
def Corollary354 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (QU : QuadraticForm ℚ_[p] (Fin m → ℚ_[p]))
    (QV : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])), QU.discr' ≠ 0 → QV.discr' ≠ 0 → m ≤ n →
    (OMeara.IsRepresentedBy QU QV ↔
      3 ≤ n - m ∨ (n = m ∧ QV.Equivalent QU) ∨
      (n = m + 1 ∧ QV.Equivalent (QU.prod (weightedSumSquares ℚ_[p] ![QU.discr' * QV.discr']))) ∨
      (n = m + 2 ∧ ((∃ c : ℚ_[p], c ≠ 0 ∧ QV.discr' = -QU.discr' * c ^ 2) →
        QV.Equivalent (QU.prod (QuadraticForm.hyperbolicPlane ℚ_[p])))))

end QuadFormsKB.Kitaoka
