/-
# Hanke 2005, §6: the condition of Theorem 6.3 and the named input on similitudes

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Defines** `qv`, `hessV` ($Q_0$ over $F_\mathfrak p$ as a quadratic map and its Gram matrix), `pPow` ($\mathfrak p^k\mathfrak o_\mathfrak p$), `ordIdeal` ($\mathrm{ord}_\mathfrak p\mathfrak a$), `HankeIdealCond` (the hypothesis on $\mathfrak a$ in Theorem 6.3) and the named
input `SimilitudeOddMultiplier` (similitudes of multiplier of valuation $1$, from Shimura's local models).
-/
import QuadFormsKB.Literature.Hanke2005.MassFormula
import QuadFormsKB.Literature.Hanke2005.Similitudes

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- $\mathrm{ord}_\mathfrak p(\mathfrak a)$ for a nonzero ideal $\mathfrak a$ of $\mathcal O_F$. -/
def ordIdeal (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

/-- **Hanke's condition on $\mathfrak a$ in Theorem 6.3** (p. 20): if $n$ is odd, $\mathfrak a_\mathfrak p$ is a square (even
$\mathrm{ord}_\mathfrak p$) for every $\mathfrak p$; if $n$ is even and $t_\mathfrak p = 2$, $\mathfrak a_\mathfrak p$ is a norm from
$K_\mathfrak p = k_\mathfrak p(\sqrt{(-1)^{n/2}d_\mathfrak p})$, i.e. $\mathrm{ord}_\mathfrak p\mathfrak a$ is even unless $\mathfrak p$ ramifies in $K$. -/
@[kb "hanke2005crelle" "Theorem 6.3, p. 20 (conditions on a_p)"]
def HankeIdealCond (Q₀ : QuadForm (𝓞 F) n) (I : Ideal (𝓞 F)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), (Odd n → Even (ordIdeal v I)) ∧
    (Even n → anisoDim v Q₀ = 2 → ¬ IsRamifiedAt v Q₀ → Even (ordIdeal v I))

/-- **Similitudes of odd multiplier** (Hanke thesis, proof of Theorem 6.3, p. 21, with [Shi, §3.2]) — formerly a named
input, now **proved** for every number field (`similitudeOddMultiplier`, `LocalTypes.lean`): for even $n\ge3$ and a nondegenerate $Q_0$, at a place with $t_\mathfrak p = 0$, or $t_\mathfrak p = 2$ and $\mathfrak p$ ramified
in $K$, or $t_\mathfrak p = 4$, the Gram matrix $\varphi_\mathfrak p$ has a similitude whose multiplier has valuation $1$.
Field: `exists_mult`. -/
@[kb "hanke2005crelle" "proof of Theorem 6.3, p. 21 (ord_p Ξ_p(θ_p), with the models of Shimura 1999, §3.2)"]
structure SimilitudeOddMultiplier (F : Type) [Field F] [NumberField F] : Prop where
  /-- A multiplier of valuation $1$. -/
  exists_mult : ∀ {n : ℕ}, 3 ≤ n → Even n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate →
    ∀ v : HeightOneSpectrum (𝓞 F),
      (anisoDim v Q₀ = 0 ∨ (anisoDim v Q₀ = 2 ∧ IsRamifiedAt v Q₀) ∨ anisoDim v Q₀ = 4) →
      ∃ ξ ∈ multipliers (gramOf v (NF.Qp v Q₀)), Valued.v ξ = WithZero.exp (-1 : ℤ)

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The form $Q_0$ over $F_\mathfrak p$, as a quadratic map on $F_\mathfrak p^n$ (O'Meara's setting). -/
def qv (Q₀ : QuadForm (𝓞 F) n) : QuadraticForm Fv (Fin n → Fv) :=
  QuadForm.toQuadraticForm ((Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F Fv))

/-- The Gram (Hessian) matrix of $Q_0$ over $F_\mathfrak p$. -/
def hessV (Q₀ : QuadForm (𝓞 F) n) : Matrix (Fin n) (Fin n) Fv :=
  (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (algebraMap F Fv)

/-- The fractional ideal $\mathfrak p^k\mathfrak o_\mathfrak p$ of $F_\mathfrak p$. -/
def pPow (k : ℕ) : Submodule 𝔬 Fv := Submodule.span 𝔬 {((NF.π v : 𝔬) : Fv) ^ k}

end Local

end QuadFormsKB.Hanke2005
