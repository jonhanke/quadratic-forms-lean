/-
# Kitaoka 1993, Proposition 1.3.3 (first case): isometries into a space with a radical

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, Proposition 1.3.3, p. 18 (printed page).

**Book statement.** Let $V, W$ be quadratic spaces over $F = \mathbb F_q$ with $V$ regular and represented by $W$.
Put $W = W_0 \perp \operatorname{Rad} W$, $v = \dim V$, $w = \dim W_0$, $r = \dim \operatorname{Rad} W$. Then
$r(V, W) = r(V, W_0)\,q^{vr}$ if $W^\perp = \operatorname{Rad} W$, and
$r(V, W) = q^{v \dim W - v(v+1)/2}\prod_{w - v + 2 \le e \le w,\ e \text{ even}}(1 - q^{-e})$ if
$W^\perp \ne \operatorname{Rad} W$ (possible only in characteristic $2$).

**Encoding.** $r(V, W)$ is `Kitaoka.FqCount.isomCount` (injective linear maps preserving the forms). Here
$\operatorname{Rad} W = \{x \in W^\perp : Q(x) = 0\}$. When $W^\perp = \operatorname{Rad} W$ the space is
$W = W_0 \perp \operatorname{Rad} W$ with $W_0$ regular and $Q$ zero on $\operatorname{Rad} W$; it is encoded as the
product $W_0 \times R$ with the form $Q_0 \oplus 0$ (`Q₀.prod 0`), $R$ a vector space of dimension $r$. Isometry
counts depend only on the isometry class (`isomCount_congr_right`). The formula holds for any form $Q_0$ on $W_0$
(regularity of $W_0$ and "represented by" are not used) and for any field $F$ with finitely many elements.

**Proves** (unconditional): `proposition133_rad`, the first case. The second case (characteristic $2$,
$W^\perp \ne \operatorname{Rad} W$) is `proposition133_char2` in `Ch1Prop133Char2.lean`.

**Proof.** (Kitaoka.) An isometry $\sigma : V \to W_0 \times R$ is a pair $(\eta, \tau)$ with $\eta : V \to W_0$ an
isometry and $\tau : V \to R$ an arbitrary linear map; $\eta$ is injective because $V$ is regular. There are
$q^{vr}$ linear maps $V \to R$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1IsometryCountProof

open QuadraticMap Module

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

variable {F : Type} [Field F]

/-- An isometry from a regular space is injective. -/
theorem injective_of_iso_regular {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {QV : QuadraticForm F V} {QW : QuadraticForm F W} (hV : (polarBilin QV).Nondegenerate) (σ : V →ₗ[F] W)
    (hσ : ∀ x, QW (σ x) = QV x) : Function.Injective σ := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  refine hV.1 x fun y => ?_
  rw [polarBilin_apply_apply, ← polar_of_iso σ hσ, hx]
  simp [polar]

/-- The isometries into $W_0 \times R$ with the form $Q_0 \oplus 0$ are the pairs (isometry into $W_0$, linear map
into $R$). -/
def isoProdZeroEquiv {V W₀ R : Type} [AddCommGroup V] [Module F V] [AddCommGroup W₀] [Module F W₀]
    [AddCommGroup R] [Module F R] {QV : QuadraticForm F V} (hV : (polarBilin QV).Nondegenerate)
    (Q₀ : QuadraticForm F W₀) :
    {σ : V →ₗ[F] W₀ × R // Function.Injective σ ∧ ∀ x, (Q₀.prod (0 : QuadraticForm F R)) (σ x) = QV x} ≃
      {η : V →ₗ[F] W₀ // Function.Injective η ∧ ∀ x, Q₀ (η x) = QV x} × (V →ₗ[F] R) where
  toFun σ :=
    have h : ∀ x, Q₀ ((LinearMap.fst F W₀ R ∘ₗ σ.1) x) = QV x := fun x => by
      have := σ.2.2 x
      simpa using this
    (⟨LinearMap.fst F W₀ R ∘ₗ σ.1, injective_of_iso_regular hV _ h, h⟩, LinearMap.snd F W₀ R ∘ₗ σ.1)
  invFun p :=
    ⟨p.1.1.prod p.2, fun a b hab => p.1.2.1 (by simpa using congrArg Prod.fst hab),
      fun x => by simpa using p.1.2.2 x⟩
  left_inv σ := by
    ext x <;> simp
  right_inv p := by
    ext x <;> simp

/-- **Kitaoka 1993, Proposition 1.3.3, first case** (p. 18). Let $F$ be a finite field with $q$ elements, $V$ a regular
quadratic space over $F$ of dimension $v$ (form $Q_V$ with nondegenerate polar form), and
$W = W_0 \perp \operatorname{Rad} W$ where $\operatorname{Rad} W = R$ carries the zero form and has dimension $r$ (the
case $W^\perp = \operatorname{Rad} W$). Then $r(V, W) = r(V, W_0)\,q^{vr}$. Unconditional. -/
@[kb "kitaoka1993" "§1.3, Prop. 1.3.3, p. 18 (case W^⊥ = Rad W)"]
theorem proposition133_rad [Finite F] {V W₀ R : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W₀] [Module F W₀] [AddCommGroup R] [Module F R] [FiniteDimensional F R]
    (QV : QuadraticForm F V) (hV : (polarBilin QV).Nondegenerate) (Q₀ : QuadraticForm F W₀) :
    isomCount QV (Q₀.prod (0 : QuadraticForm F R)) =
      isomCount QV Q₀ * Nat.card F ^ (finrank F V * finrank F R) := by
  unfold isomCount
  rw [Nat.card_congr (isoProdZeroEquiv hV Q₀), Nat.card_prod, Module.natCard_eq_pow_finrank (K := F) (V := V →ₗ[F] R),
    Module.finrank_linearMap]

end QuadFormsKB.Kitaoka.FqCount
