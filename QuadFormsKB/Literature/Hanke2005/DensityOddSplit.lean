/-
# Hanke 2005, (3.3): splitting the remaining named input by the type of place

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

`ShimuraMaximalDensityRest F` is Shimura's local factor (3.3) at the places $\mathfrak p$ that are dyadic or have
$\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$. It is split here into three named statements, each about one kind of place:
* `ShimuraDensityOddRamified F`: $\mathfrak p$ non-dyadic, $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$;
* `ShimuraDensityDyadicSelfDual F`: $\mathfrak p$ dyadic, $\widetilde\Lambda_\mathfrak p=\Lambda_\mathfrak p$ (even unimodular);
* `ShimuraDensityDyadicBad F`: $\mathfrak p$ dyadic, $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$.
`shimuraMaximalDensityRest_of_split` recovers the old input from the three. Later files prove the statements one by one.
-/
import QuadFormsKB.Literature.Hanke2005.DensitySelfDual

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.Lattices

/-- The right-hand side of (3.3) at a place $v$ (the common shape of the three statements below). -/
def shimuraBetaRHS {n : ℕ} (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  ‖((2 : v.adicCompletion F) • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))).det‖ ^ (((n : ℝ) + 1) / 2) *
    (‖(2 : v.adicCompletion F)‖ ^ n)⁻¹ * dualIndexAt v Q₀ * xiAt v Q₀

/-- **(3.3) at a non-dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$** (Hanke thesis, (3.3), p. 8, from
[Shi, Thm 8.6(3), Prop. 3.9, (3.1.9)]): a **named input**, to be proved from the Jordan splitting of a maximal lattice at an
odd place. Not equivalent to Theorem 5.1. Field: `beta_eq`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (non-dyadic places with Λ̃_p ≠ Λ_p)"]
structure ShimuraDensityOddRamified (F : Type) [Field F] [NumberField F] : Prop where
  /-- The local factor (3.3) at such a place. -/
  beta_eq : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ ≠ 1 →
      hankeBeta v (std v) (gramOf v (NF.Qp v Q₀)) = shimuraBetaRHS F v Q₀

/-- **(3.3) at a dyadic place with $\widetilde\Lambda_\mathfrak p=\Lambda_\mathfrak p$** (Hanke thesis, (3.3), p. 8): a **named input**.
Field: `beta_eq`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p = Λ_p)"]
structure ShimuraDensityDyadicSelfDual (F : Type) [Field F] [NumberField F] : Prop where
  /-- The local factor (3.3) at such a place. -/
  beta_eq : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ = 1 →
      hankeBeta v (std v) (gramOf v (NF.Qp v Q₀)) = shimuraBetaRHS F v Q₀

/-- **(3.3) at a dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$** (Hanke thesis, (3.3), p. 8): a **named input**.
Field: `beta_eq`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p ≠ Λ_p)"]
structure ShimuraDensityDyadicBad (F : Type) [Field F] [NumberField F] : Prop where
  /-- The local factor (3.3) at such a place. -/
  beta_eq : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ ≠ 1 →
      hankeBeta v (std v) (gramOf v (NF.Qp v Q₀)) = shimuraBetaRHS F v Q₀

/-- **The three place-types give the remaining input.** -/
@[kb "hanke2005crelle" "(3.3), p. 8 (the remaining places, by type)"]
theorem shimuraMaximalDensityRest_of_split {F : Type} [Field F] [NumberField F]
    (I₁ : ShimuraDensityOddRamified F) (I₂ : ShimuraDensityDyadicSelfDual F) (I₃ : ShimuraDensityDyadicBad F) :
    ShimuraMaximalDensityRest F := by
  refine ⟨fun {n} hn Q₀ hQ hmax hdet v hv => ?_⟩
  by_cases h2 : IsUnit (2 : v.adicCompletionIntegers F)
  · have h1 : dualIndexAt v Q₀ ≠ 1 := hv.resolve_left (not_not.2 h2)
    exact I₁.beta_eq hn Q₀ hQ hmax hdet v h2 h1
  · by_cases h1 : dualIndexAt v Q₀ = 1
    · exact I₂.beta_eq hn Q₀ hQ hmax hdet v h2 h1
    · exact I₃.beta_eq hn Q₀ hQ hmax hdet v h2 h1

end QuadFormsKB.Hanke2005
