/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Classical.BinaryProduct
import QuadFormsKB.Tamagawa.HeadlineFactsWeil
import QuadFormsKB.Tamagawa.Indefinite.DCFinite

/-!
# Headline statements, proved: Siegel's formula for indefinite forms over every number field

The declarations of `Challenge_SiegelIndefinite.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/SiegelIndefinite.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_SiegelIndefinite.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## Siegel's formula for indefinite forms over every number field

Setting: F any number field; Q₀ a nondegenerate quadratic form over 𝓞 F in N variables, of any signature (at a complex
place every form is indefinite); L = 𝓞_F^N; G = SO(V), G_∞ = ∏_{w | ∞} SO(V)(F_w). The sums ∑' i run over the proper
classes M_i in the genus of L (`DC Q₀`: the double cosets SO(V)(F)\SO(V)(𝔸_f)/SO(L̂)), as sums in [0, ∞] (`ENNReal`).
`unitVolume Q₀ hQ i` = v(M_i) is the covolume of the unit group SO(M_i) in G_∞ for Weil's archimedean Tamagawa measure
μ_∞ (`muArchTamSO`). For a rational point (a vector ξ ∈ F^N with Q₀(ξ) = m, `RatSphere`; or a frame Ξ ∈ F^{N×r} with
Q₀ ∘ Ξ = T₀, `RatFrame`), Siegel's measure of representations ρ(M_i, ·) (`repMeasure`, `repMeasureT`) is
∑_{x ∈ Γ_i\R(M_i, ·)} vol(Γ_{i,x}\H_x), the sum over the unit-group orbits of the representations by M_i of the
covolumes of their stabilizers, for the quotient measures on the stabilizers H_x ⊆ G_∞ given by an archimedean
fibration of μ_∞ (`archFibrationNF`, `frameArchFibrationNF`, `frameArchFibrationRank2`). The constants c_∞
(`cInfNF`, `cInfTNF`, `cInfCorankOne`) are products of |d_F|^{-N(N-1)/4} and normalized archimedean absolute values;
the local sides (`finDensityProduct`, `frameDensityProduct`, ...) are |d_F|^{-…} times products over the primes 𝔭 of
𝓞 F of the local densities β_𝔭 (`LocalDensity.NF.localDensity`, `LocalDensity.NF.localDensityForm`), regularized by
L_F(1, χ) or by ρ_F = Res_{s=1} ζ_F(s) when the stabilizer has rank 2.

**Side conditions.** Each statement also states that the real products ∏'_𝔭 on the local side converge
unconditionally (a `tprod` is 1 otherwise), that L_F(1, χ) exists and is positive where it occurs, that
0 < ∑_i v(M_i) < ∞, and that there are finitely many proper classes M_i in the genus of L (`Finite (DC Q₀)`, from
`finite_DC`: O'Meara 103:4, for every nondegenerate Q₀ of any signature). The sums over classes are sums in [0, ∞];
with finitely many classes they are finite sums. -/

section SiegelIndefinite

set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F]

open MeasureTheory QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Indefinite
  QuadFormsKB.Tamagawa.Frames QuadFormsKB.LocalDensity

/-- **Siegel's formula for indefinite forms, numbers, every number field** (Siegel 1936, measure of
representations; Weil 1965). For Q₀ nondegenerate over 𝓞 F in N = k + 1 ≥ 4 variables (any signature) and
m ∈ 𝓞 F, m ≠ 0, represented by Q₀ over F (a rational point ξ),
c_∞(m) · ∑_i ρ(M_i, m) = |d_F|^{-(N-1)/2} ∏_𝔭 β_𝔭(L, m) · ∑_i v(M_i),
with c_∞(m) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |2m|_w^{-(N-1)} (`cInfNF`) and ρ for the archimedean sphere fibration
`archFibrationNF`. Moreover ∏_𝔭 β_𝔭(L, m) converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_numberField {k : ℕ} (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensity v Q₀ m) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefinite_uncond hQ hk hm ξ,
    Siegel.multipliable_eulerFactorNF_uncond hQ (by omega) fun h => hm (by simp [h]),
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula for indefinite forms, forms by forms, every number field** (Siegel 1936; Weil 1965).
For Q₀ nondegenerate over 𝓞 F in N = r + n' variables (any signature), n' ≥ 3, and T₀ nondegenerate over 𝓞 F of rank
r ≥ 1 represented by Q₀ over F (a rational frame Ξ, Q₀ ∘ Ξ = T₀),
c_∞(T₀) · ∑_i ρ(M_i, T₀) = |d_F|^{-(N(N-1) - n'(n'-1))/4} ∏_𝔭 β_𝔭(L, T₀) · ∑_i v(M_i),
with c_∞(T₀) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |det H_{T₀}|_w^{-n'} (`cInfTNF`) and ρ for the frame fibration
`frameArchFibrationNF`. Moreover the product ∏_𝔭 β_𝔭(L, T₀) converges unconditionally and
0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_numberField {r n' : ℕ} (hr : 1 ≤ r) (hn' : 3 ≤ n') (Q₀ : QuadForm (𝓞 F) (r + n'))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationNF Q₀ hQ T₀ hT hn' Ξ) i =
      ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_uncond Q₀ hQ T₀ hT hn' Ξ hr,
    multipliable_localDensityForm_of_frame Q₀ hQ T₀ hT hn' Ξ,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula, forms by forms with an anisotropic stabilizer of rank 2, every number field.** For Q₀
nondegenerate over 𝓞 F in N = r + 2 variables (any signature), T₀ nondegenerate of rank r ≥ 1 with a rational frame Ξ,
and δ = -det H_{Q₀} det H_{T₀} not a square in F (`deltaForms`; the orthogonal complement of Ξ is anisotropic),
c_∞(T₀) · ∑_i ρ(M_i, T₀) = |d_F|^{-(N(N-1)-2)/4} L_F(1, χ) ∏_𝔭 β_𝔭(L, T₀)(1 - χ(𝔭)/N𝔭) · ∑_i v(M_i),
χ = `chiForms Q₀ T₀` (χ(𝔭) = (δ/𝔭) at 𝔭 ∤ 2δ, 0 otherwise), ρ for `frameArchFibrationRank2`. Moreover
L_F(1, χ) = lim_{s→1⁺} L_F(s, χ) exists and is positive, the corrected product ∏_𝔭 β_𝔭(L, T₀)(1 - χ(𝔭)/N𝔭)
converges unconditionally, and 0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_rank2 {r : ℕ} (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (hW : ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
    (Ξ : RatFrame Q₀ T₀) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationRank2 Q₀ hQ T₀ hT hW Ξ) i =
      ENNReal.ofReal (frameDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiForms Q₀ T₀) (LOne (chiForms Q₀ T₀)) ∧ 0 < LOne (chiForms Q₀ T₀) ∧
    (Multipliable fun v =>
      NF.localDensityForm v Q₀ T₀ * (1 - chiForms Q₀ T₀ v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ)) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  by
    refine ⟨siegelIndefiniteForms_rank2_uncond Q₀ hQ T₀ hT hW Ξ hr, (lOne_chiForms_nf hQ hT hW).2,
      (lOne_chiForms_nf hQ hT hW).1, ?_,
      tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      finite_DC Q₀ hQ⟩
    simpa only [zpow_one] using multipliable_localDensityForm_rank2 Q₀ hQ T₀ hT hW Ξ hr

/-- **Siegel's formula for numbers by ternary forms, every number field** (the case r = 1 of
`siegel_indefinite_forms_rank2`). For Q₀ nondegenerate ternary over 𝓞 F (any signature), m ∈ 𝓞 F, m ≠ 0,
represented by Q₀ over F (a rational point ξ), and -2m det H_{Q₀} not a square in F (m^⊥ anisotropic),
c_∞(m) · ∑_i ρ(M_i, m) = |d_F|^{-1} L_F(1, χ) ∏_𝔭 β_𝔭(L, m)(1 - χ(𝔭)/N𝔭) · ∑_i v(M_i),
with χ = `chiForms Q₀ ⟨m⟩` (χ(𝔭) = (-2m det H_{Q₀}/𝔭) at the good primes), ρ the measures of the representations
of m (vectors read as 1-frames, `ratFrameEquivRatSphere`) for `frameArchFibrationRank2`. Moreover L_F(1, χ) exists
and is positive, the corrected product converges unconditionally, and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_ternary (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hW : ¬ IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := 2) (m : F) * ∑' i, repMeasureT Q₀ (DVR.unary m) hQ
        (frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
          ((ratFrameEquivRatSphere Q₀ m).symm ξ)) i =
      ENNReal.ofReal (ternaryDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiForms Q₀ (DVR.unary m)) (LOne (chiForms Q₀ (DVR.unary m))) ∧
    0 < LOne (chiForms Q₀ (DVR.unary m)) ∧
    (Multipliable fun v =>
      NF.localDensity v Q₀ m * (1 - chiForms Q₀ (DVR.unary m) v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ)) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  by
    refine ⟨siegelIndefinite_ternary_uncond Q₀ hQ hm hW ξ,
      (lOne_chiForms_nf hQ (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)).2,
      (lOne_chiForms_nf hQ (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)).1, ?_,
      tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      finite_DC Q₀ hQ⟩
    have h := multipliable_localDensityForm_rank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
      (not_isSquare_deltaForms_unary hW) ((ratFrameEquivRatSphere Q₀ m).symm ξ) le_rfl
    simpa only [zpow_one, NF.localDensityForm_unary] using h

/-- **Siegel's formula, forms by forms with an isotropic stabilizer of rank 2 (Siegel's excluded case),
regularized, every number field.** For Q₀ nondegenerate over 𝓞 F in N = r + 2 variables (any signature), T₀
nondegenerate of rank r ≥ 1 with a rational frame Ξ, and δ = -det H_{Q₀} det H_{T₀} a square in F (the stabilizers
are split tori),
2 c_∞(T₀) · ∑_i ρ¹(M_i, T₀) = |d_F|^{-(N(N-1)-2)/4} ρ_F ∏_𝔭 β_𝔭(L, T₀)(1 - N𝔭^{-1}) · ∑_i v(M_i),
ρ_F = Res_{s=1} ζ_F(s), with ρ¹ the measures of representations for the norm-one stabilizers (`repMeasureIso`).
Moreover the corrected product converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_rank2_isotropic {r : ℕ} (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 2))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀) :
    2 * (cInfTNF Q₀ T₀ * ∑' i, repMeasureIso Q₀ hQ T₀ hT hiso Ξ i) =
      ENNReal.ofReal (isoDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ * lamV v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_rank2_isotropic_uncond Q₀ hQ T₀ hT hiso Ξ hr,
    multipliable_localDensityForm_iso Q₀ hQ T₀ hT hiso Ξ hr,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula for numbers by ternary forms with m^⊥ isotropic (Siegel's excluded case), regularized,
every number field** (the case r = 1 of `siegel_indefinite_forms_rank2_isotropic`). For Q₀ nondegenerate ternary over
𝓞 F (any signature), m ∈ 𝓞 F, m ≠ 0, represented by Q₀ over F (a rational point ξ), and -2m det H_{Q₀} a square in F,
2 c_∞(m) · ∑_i ρ¹(M_i, m) = |d_F|^{-1} ρ_F ∏_𝔭 β_𝔭(L, m)(1 - N𝔭^{-1}) · ∑_i v(M_i).
Moreover the corrected product converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_ternary_isotropic (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    2 * (cInfNF (k := 2) (m : F) * ∑' i, repMeasureIso Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
        (isSquare_deltaForms_unary hiso) ((ratFrameEquivRatSphere Q₀ m).symm ξ) i) =
      ENNReal.ofReal (ternaryIsoDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensity v Q₀ m * lamV v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefinite_ternary_isotropic_uncond Q₀ hQ hm hiso ξ,
    multipliable_localDensity_ternary_iso Q₀ hQ hm hiso ξ,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula, forms of corank one, every number field** (Siegel 1935, Hauptsatz for n = m + 1,
ε = 1/2). For Q₀ nondegenerate over 𝓞 F in N = r + 1 variables (any signature), r ≥ 2, and T₀ nondegenerate of rank r
with a rational frame Ξ,
c⁽¹⁾_∞(Q₀) · ∑_i n(M_i, T₀) = (1/2) |d_F|^{-(N(N-1))/4} ∏_𝔭 β_𝔭(L, T₀) · ∑_i v(M_i),
n(M_i, T₀) = `repCount` the number of representations of T₀ by M_i modulo the unit group (a cardinal in [0, ∞]),
c⁽¹⁾_∞(Q₀) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |det H_{Q₀}|_w^{-1} (`cInfCorankOne`). Moreover the product
∏_𝔭 β_𝔭(L, T₀) converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_corank1 {r : ℕ} (hr : 2 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, Indefinite.repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_corank1_uncond Q₀ hQ T₀ hT Ξ hr,
    multipliable_localDensityForm_corank1 Q₀ hQ T₀ hT Ξ hr,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula for the numbers represented by an anisotropic binary form, every number field**
(Siegel 1935, Hauptsatz for n = 2, m = 1, ε = 1/2; Dirichlet over ℚ). For Q₀ a nondegenerate binary form over 𝓞 F (any
signature) that is anisotropic over F, E a discriminant field of Q₀ (`IsDiscField`; one exists,
`exists_isDiscField_of_anisotropicF`), and T₀ = ⟨m⟩ nondegenerate of rank one with a rational frame Ξ (Q₀(Ξ) = m),
c⁽¹⁾_∞(Q₀) · ∑_i n(M_i, m) = (1/2) |d_F|^{-1/2} L_F(1, χ_E)^{-1} ∏_𝔭 L_𝔭(1, χ_E) β_𝔭(L, m) · ∑_i v(M_i),
n(M_i, m) = `repCount` (the representations modulo the unit group SO(M_i); finite for definite Q₀, infinite unit group
for indefinite Q₀). Moreover L_F(1, χ_E) exists and is positive, and the product ∏_𝔭 L_𝔭(1, χ_E) β_𝔭(L, m)
converges unconditionally, and 0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, Indefinite.repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ / lamL (chiE F E) v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefinite_binary_uncond Q₀ hQ hA E hE T₀ hT Ξ, (hasLOne_chiE hE.finrank_eq_two).1,
    (hasLOne_chiE hE.finrank_eq_two).2, multipliable_binDensity Q₀ hQ E hE T₀ hT Ξ,
    (tsum_unitVolume_ne_zero_top_binary Q₀ hQ hA E hE).1, (tsum_unitVolume_ne_zero_top_binary Q₀ hQ hA E hE).2,
    finite_DC Q₀ hQ⟩

open Classical in
/-- **Siegel's formula for forms of the same rank (corank zero), every number field** (Siegel 1935, Hauptsatz
for n = m, ε = 1/2 at every place). For Q₀ nondegenerate over 𝓞 F in N ≥ 3 variables (any signature) and T₀
nondegenerate in N variables with a rational frame Ξ (Q₀ ∘ Ξ = T₀, Ξ ∈ GL_N(F)),
∑_i n(M_i, T₀) = ∏_{w | ∞} |det Ξ|_w^{-1} ∏_𝔭 β_𝔭(L, T₀)/2 · ∑_i v(M_i)
(normalized absolute values; n = `repCount`). Moreover the product ∏_𝔭 β_𝔭(L, T₀)/2 converges unconditionally and
0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_corank0 {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    ∑' i, Indefinite.repCount Q₀ T₀ i =
      ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) *
        ∏' v, NF.localDensityForm v Q₀ T₀ / 2) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ / 2) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_corank0_uncond Q₀ hQ T₀ hT Ξ hN,
    multipliable_localDensityForm_half_corank0 Q₀ hQ T₀ hT Ξ hN,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

end SiegelIndefinite

end QuadFormsKB.Headlines
