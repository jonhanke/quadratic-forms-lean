/-
# Hanke 2005, Theorem 5.1 conditional only on the ramified binary kernel

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005), Thm 5.1.

With `DyadicQuaternaryDensity` proved (`dyadicQuaternaryDensity`), the only named input left under (3.3), hence under
Theorem 5.1, is `DyadicRamifiedBinaryDensity` (the self-density $4|\det H_N|^{-1}$ of the ramified anisotropic binary
kernel at a dyadic place, and the ramification of $\mathfrak p$ in $F_\mathfrak p(\sqrt\delta)$ for that kernel).
-/
import QuadFormsKB.Literature.Hanke2005.Unconditional
import QuadFormsKB.Literature.Hanke2005.DyadicRamifiedBinary

open NumberField IsDedekindDomain
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.LatChange QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **`DyadicKernelDensityLow` from the ramified binary kernel alone.** -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic H^k ⊥ N, r = 2, 3, 4; quoting Shimura 1999, Thm 8.6(3), Prop. 3.9)"]
theorem dyadicKernelDensityLow_of_ramBinary (I2 : DyadicRamifiedBinaryDensity F) : DyadicKernelDensityLow F :=
  dyadicKernelDensityLow_of_inputs (dyadicQuaternaryDensity F) I2

/-- **`ShimuraMaximalDensityRest` (hence (3.3) at every place) from the ramified binary kernel alone.** -/
@[kb "hanke2005crelle" "(3.3), p. 8 (all places; conditional only on the ramified dyadic binary kernel)"]
theorem shimuraMaximalDensityRest_of_ramBinary (I2 : DyadicRamifiedBinaryDensity F) : ShimuraMaximalDensityRest F :=
  shimuraMaximalDensityRest_of_inputs (dyadicQuaternaryDensity F) I2

/-- **Theorem 5.1** (Hanke thesis, pp. 16–17, with Shimura's hypothesis), conditional only on
`DyadicRamifiedBinaryDensity F`. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–17 (conditional only on the ramified dyadic binary kernel)"]
theorem theorem51_of_ramBinary (I2 : DyadicRamifiedBinaryDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_of_rest (shimuraMaximalDensityRest_of_ramBinary I2) hn Q₀ hQ hmax hdet

/-- **Theorem 5.1, totally definite case**, conditional only on `DyadicRamifiedBinaryDensity F`. -/
@[kb "hanke2005crelle" "Theorem 5.1, Part 1, pp. 17–18 (totally definite; conditional only on the ramified dyadic binary kernel)"]
theorem theorem51_definite_of_ramBinary [IsTotallyReal F] (I2 : DyadicRamifiedBinaryDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_definite_of_rest (shimuraMaximalDensityRest_of_ramBinary I2) hn Q₀ hQ hpd hmax hdet

/-- **(3.3) at every place from the self-density of the ramified binary kernel alone** (the ramification of
$\mathfrak p$ in $F_\mathfrak p(\sqrt\delta)$ for that kernel is proved, `ramBinary_ram`). -/
@[kb "hanke2005crelle" "(3.3), p. 8 (all places; conditional only on the ramified dyadic binary self-density)"]
theorem shimuraMaximalDensityRest_of_selfDensity (I : DyadicRamifiedBinarySelfDensity F) :
    ShimuraMaximalDensityRest F :=
  shimuraMaximalDensityRest_of_ramBinary (dyadicRamifiedBinaryDensity_of_selfDensity F I)

/-- **Theorem 5.1**, conditional only on `DyadicRamifiedBinarySelfDensity F`. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–17 (conditional only on the ramified dyadic binary self-density)"]
theorem theorem51_of_selfDensity (I : DyadicRamifiedBinarySelfDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_of_rest (shimuraMaximalDensityRest_of_selfDensity I) hn Q₀ hQ hmax hdet

/-- **Theorem 5.1, totally definite case**, conditional only on `DyadicRamifiedBinarySelfDensity F`. -/
@[kb "hanke2005crelle" "Theorem 5.1, Part 1, pp. 17–18 (totally definite; conditional only on the ramified dyadic binary self-density)"]
theorem theorem51_definite_of_selfDensity [IsTotallyReal F] (I : DyadicRamifiedBinarySelfDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_definite_of_rest (shimuraMaximalDensityRest_of_selfDensity I) hn Q₀ hQ hpd hmax hdet

end QuadFormsKB.Hanke2005
