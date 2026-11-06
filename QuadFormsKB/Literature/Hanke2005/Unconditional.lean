/-
# Hanke 2005: Theorems 5.1 and 6.3 with the proved inputs discharged

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

The former named inputs `ShimuraMaximalTypes F` and `SimilitudeOddMultiplier F` are proved for every number field
(`shimuraMaximalTypes`, `similitudeOddMultiplier`, `LocalTypes.lean`). Hence:
* `theorem51_of_density`, `theorem51_definite_of_density`: Theorem 5.1 (any signature; totally definite case),
  conditional only on the named input `ShimuraMaximalDensity F` ((3.3), Shimura's local factor of a maximal lattice);
  Shimura's hypothesis `ShimuraDetHyp` stays a hypothesis (a proposed correction of the printed statement).
* `theorem51_of_rest`, `theorem51_definite_of_rest`: the same, conditional only on the smaller named input
  `ShimuraMaximalDensityRest F` ((3.3) at the dyadic places and the places dividing $\mathfrak e$; (3.3) at the other places
  is proved, `siegelDensity_selfDual_nondyadic`).
* `theorem63_definite_uncond`: Theorem 6.3 in the totally definite case, **unconditional**.
The conditional versions `theorem51`, `theorem51_definite`, `theorem63_definite` are kept.
-/
import QuadFormsKB.Literature.Hanke2005.LocalTypes
import QuadFormsKB.Literature.Hanke2005.DensitySelfDual
import QuadFormsKB.Literature.Hanke2005.MassDefinite
import QuadFormsKB.Literature.Hanke2005.TheoremSixThree

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.LatChange QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Theorem 5.1** (Hanke thesis, pp. 16–17), conditional only on the named input `ShimuraMaximalDensity F` ((3.3)):
for $n\ge3$, $Q_0$ nondegenerate over $\mathcal O_F$ (any number field, any signature) with $\mathcal O_F^n$ maximal and
Shimura's hypothesis, Hanke's mass is the right side `theorem51RHS`. The local types are proved
(`shimuraMaximalTypes`). -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19 (local types proved)"]
theorem theorem51_of_density (I₁ : ShimuraMaximalDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51 I₁ shimuraMaximalTypes hn Q₀ hQ hmax hdet

/-- **Theorem 5.1, totally definite case** (Hanke thesis, Theorem 5.1, Part 1, pp. 17–18), conditional only on
`ShimuraMaximalDensity F`: $\sum_a[\Gamma_a:1]^{-1}$ is the right side of Theorem 5.1. -/
@[kb "hanke2005crelle" "Theorem 5.1, Part 1, pp. 17–18 (totally definite; local types proved)"]
theorem theorem51_definite_of_density [IsTotallyReal F] (I₁ : ShimuraMaximalDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_definite I₁ shimuraMaximalTypes hn Q₀ hQ hpd hmax hdet

/-- **Theorem 5.1** (Hanke thesis, pp. 16–17), conditional only on the named input `ShimuraMaximalDensityRest F` ((3.3)
at the dyadic places and the places dividing $\mathfrak e$): for $n\ge3$, $Q_0$ nondegenerate over $\mathcal O_F$ (any number
field, any signature) with $\mathcal O_F^n$ maximal and Shimura's hypothesis, Hanke's mass is `theorem51RHS`. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19 (local types and (3.3) at non-dyadic self-dual places proved)"]
theorem theorem51_of_rest (I : ShimuraMaximalDensityRest F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_of_density (shimuraMaximalDensity_of_rest I) hn Q₀ hQ hmax hdet

/-- **Theorem 5.1, totally definite case**, conditional only on `ShimuraMaximalDensityRest F`. -/
@[kb "hanke2005crelle" "Theorem 5.1, Part 1, pp. 17–18 (totally definite; conditional on (3.3) at finitely many places)"]
theorem theorem51_definite_of_rest [IsTotallyReal F] (I : ShimuraMaximalDensityRest F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_definite_of_density (shimuraMaximalDensity_of_rest I) hn Q₀ hQ hpd hmax hdet

/-- **Theorem 6.3, totally definite case, unconditional** (Hanke thesis, pp. 20–21): $F$ totally real, $Q_0$ totally
positive definite in $n\ge3$ variables, $L$ an $\mathfrak a$-maximal lattice and $M$ a maximal lattice on $V$, $\mathfrak a\ne0$
satisfying Hanke's condition. Then $\mathrm{Mass}(L) = \mathrm{Mass}(M)$. -/
@[kb "hanke2005crelle" "Theorem 6.3, pp. 20–21 (totally definite case; unconditional)"]
theorem theorem63_definite_uncond [IsTotallyReal F] (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcond : HankeIdealCond Q₀ I) (L M : Lat F n)
    (hL : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)))
        (Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F)))) L.1)
    (hM : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) M.1) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) L = mass (Q₀.map (algebraMap (𝓞 F) F)) M :=
  theorem63_definite similitudeOddMultiplier hn Q₀ hQ hpd I hI hcond L M hL hM

end QuadFormsKB.Hanke2005
