/-
# Kitaoka 1993, Theorem 1.3.2: the number of isometries between regular spaces over $\mathbb F_q$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, Theorem 1.3.2, p. 16 (printed page), with
$\chi$ of p. 14 and $U^{(-1)}$ of p. 16.

**Book statement.** Let $V, W$ be regular quadratic spaces over $F = \mathbb F_q$, $v = \dim V \le w = \dim W$. The
number $r(V, W)$ of isometries from $V$ to $W$ is
$$q^{vw - v(v+1)/2}\bigl(1 - \chi(W)q^{-w/2}\bigr)\bigl(1 + \chi(V \perp W^{(-1)})q^{(v-w)/2}\bigr)
\prod_{\substack{w-v+1 \le e \le w-1\\ e \text{ even}}}(1 - q^{-e}).$$

**Encoding.** $V = F^v$, $W = F^w$ with quadratic forms $Q_V, Q_W$ whose polar forms are nondegenerate (regular). An
isometry from $V$ to $W$ is an injective linear map $\sigma$ with $Q_W(\sigma x) = Q_V(x)$ (`isomCount`; injectivity
is automatic for regular $V$ and is written for clarity). $W^{(-1)}$ is $(W, -Q_W)$, $V \perp W^{(-1)}$ is
`QV.prod (-QW)`, and $\chi$ is `Kitaoka.FqCount.chiGen` ($0$ for odd dimension, $1$ for hyperbolic spaces,
$-1$ otherwise). Powers with half-integral exponents are real powers.

*Update:* the hypothesis $v \ge 1$ is added. The book allows $v = 0$ (the zero space is regular), but then the formula
gives $1 - \chi(W)^2 q^{-w}$, which is $1 - q^{-w} \ne 1 = r(0, W)$ for every even $w$ (and $0$ for $w = 0$).
Kitaoka's induction starts at $v = 1$.

**Status.** *Proved* for every finite field as `theorem132` in `Ch1Char2Main.lean`: for $q$ odd by
`theorem132_odd` (`Ch1IsometryCountProof.lean`, Kitaoka's induction on $v$ splitting off $\langle t\rangle$), for $q$
even by `theorem132_char2` (splitting off regular planes).
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch5Lemma569Proof

open QuadraticMap Module

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

/-- $r(V, W)$: the number of isometries from $(V, Q_V)$ to $(W, Q_W)$, i.e. injective linear maps
$\sigma : V \to W$ with $Q_W(\sigma x) = Q_V(x)$ for all $x$ (Kitaoka 1993, §1.3, p. 14). -/
@[kb "kitaoka1993" "§1.3, p. 14 (r(V, W))"]
def isomCount {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (QV : QuadraticForm K V) (QW : QuadraticForm K W) : ℕ :=
  Nat.card {σ : V →ₗ[K] W // Function.Injective σ ∧ ∀ x, QW (σ x) = QV x}

/-- **Kitaoka 1993, Theorem 1.3.2** (p. 16), *stated*. For a finite field $K$ with $q$ elements and regular quadratic
forms $Q_V$ on $K^v$ and $Q_W$ on $K^w$ with $1 \le v \le w$, the number of isometries $r(V, W)$ equals
$q^{vw - v(v+1)/2}(1 - \chi(W)q^{-w/2})(1 + \chi(V \perp W^{(-1)})q^{(v-w)/2})
\prod_{w-v+1 \le e \le w-1,\ e \text{ even}}(1 - q^{-e})$. -/
@[kb "kitaoka1993" "§1.3, Thm. 1.3.2, p. 16"]
def Theorem132 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (v w : ℕ) (QV : QuadraticForm K (Fin v → K))
    (QW : QuadraticForm K (Fin w → K)), (polarBilin QV).Nondegenerate → (polarBilin QW).Nondegenerate →
    0 < v → v ≤ w →
    let q : ℝ := Fintype.card K
    (isomCount QV QW : ℝ) =
      q ^ ((v * w : ℤ) - (v * (v + 1) / 2 : ℕ)) * (1 - chiGen QW * q ^ (-(w : ℝ) / 2)) *
        (1 + chiGen (QV.prod (-QW)) * q ^ (((v : ℝ) - w) / 2)) *
        ∏ e ∈ (Finset.Icc (w - v + 1) (w - 1)).filter Even, (1 - q ^ (-(e : ℤ)))

end QuadFormsKB.Kitaoka.FqCount
