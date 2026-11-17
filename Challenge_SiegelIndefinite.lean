/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Classical.BinaryProduct
import QuadFormsKB.Tamagawa.HeadlineFactsWeil
import QuadFormsKB.Tamagawa.Indefinite.DCFinite

/-!
# Headline statements: Siegel's formula for indefinite forms over every number field

The measure form of Siegel's formula for forms of every signature over every number field.

Every proof here is a deliberate `sorry`. `Solution_SiegelIndefinite.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/SiegelIndefinite.json`) checks that each theorem of
`Solution_SiegelIndefinite.lean` has exactly the statement given here and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The headlines are split into one file per book or topic (`comparator.json`
lists them), so that each check loads only what its statements need.

**Conventions.** Q denotes a quadratic form (`QuadForm R n`: the polynomial ∑_{i ≤ j} c_ij x_i x_j) or a quadratic
form on an abstract vector space (Mathlib's `QuadraticForm F V`). Classes of lattices are isometry classes under the
full orthogonal group O(Q) (improper isometries included), and every lattice L' in a genus is weighted by 1/|O(L')|.
F is a number field with ring of integers 𝓞 F; "totally positive" means positive under every real embedding.

**No hidden default values.** Some notions in the formulas take a default value outside their intended range:
`∏'` (Mathlib's unconditional infinite product) is `1` when the product does not converge unconditionally, `∑ᶠ` is
`0` over an infinite set, `Nat.card` is `0` for an infinite type, and `L_F(1, χ)` (`LOne`, a limit) is a junk value
when the limit does not exist. Each headline therefore states, as extra conjuncts, the facts that make every such
term meaningful: the genus has finitely many classes, the automorphism groups and representation sets are finite,
the infinite products converge unconditionally, and L_F(1, χ) exists (and is positive).
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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

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
    Finite (DC Q₀) := by
  sorry

end SiegelIndefinite

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.
* `QuadForm.hessian` (Defs/QuadForm.lean): the Hessian matrix H = C + Cᵀ, so Q(x) = (1/2) xᵀ H x.
* `QuadForm.Nondegenerate` (Defs/QuadForm.lean): det H ≠ 0.

Siegel's theorem
* `SiegelSpace.LatClassV.repCount Q c t` (Tamagawa/SiegelGenusV.lean): r_M(t) = #{x ∈ M : Q(x) = t} for any lattice
  M in the class c (a `Nat.card`; independent of the representative).

`Tamagawa/Measure/`)
* `AnisotropicF Q₀` (Weil/TauTwoAnisotropic.lean): Q₀(ξ) = 0 only for ξ = 0 in F^n; `IsotropicF Q₀`, `IsIsoVec Q₀ e`
  (Weil/BinaryIsotropic.lean): Q₀ has an isotropic vector; e ≠ 0 with Q₀(e) = 0.
* `IsDiscField Q₀ E`, `chiE F E`, `lamL χ`, `muTamChi`, `muTamBin Q₀ hQ E` (Weil/BinaryMeasure.lean): [E : F] = 2 and E
  contains a square root of -det H outside F; χ_E(v) = 1, -1, 0 as v splits, is inert, ramifies in E; λ_v = 1 - χ(v)/Nv;
  L_F(1, χ)^{-1} · `muTam Q₀ hQ (lamL χ)`; the case χ = χ_E.
* `tauIso Q₀ hQ he`, `muTamIso`, `isoShell`, `isoChar`, `lamV` (Weil/BinaryIsotropic.lean, Weil/Ideles.lean): the
  covolume of SO(V)(F) for ρ_F^{-1} `muTam Q₀ hQ lamV` restricted to {0 ≤ log ‖χ_e(g)‖ < 1}, χ_e : SO(V) ≅ 𝔾_m the
  character of the isotropic line of e, λ_v = 1 - N(v)^{-1}; ρ_F = Mathlib's `dedekindZeta_residue F`.
* `RegProd.LOne`, `RegProd.HasLOne` (Siegel/RegProd.lean, as above).

Siegel's formula for indefinite forms (namespace `Tamagawa.Indefinite` unless stated; paths in `Tamagawa/Indefinite/`)
* `DC Q₀` (ClassicalSetup.lean): SO(V)(F)\SO(V)(𝔸_f)/SO(L̂), the proper classes in the genus of L = 𝓞_F^N.
* `unitGroup Q₀ i`, `unitVolume Q₀ hQ i`, `reps`, `repMeasure Q₀ hQ m 𝔉 i` (ClassicalMeasures.lean) and
  `repMeasureOf` (ThetaUnfold.lean): Γ_i = SO(M_i) in G_∞; v(M_i) = covolume of Γ_i in G_∞ for `muArchTamSO`; the
  representations of m by M_i; ρ(M_i, m) = ∑ over Γ_i-orbits of x of the covolume of the stabilizer Γ_{i,x} in H_x for
  the stabilizer measure of the archimedean fibration 𝔉 (`ArchFibration`, ThetaUnfold.lean).
* `repMeasureT`, `RatFrame Q₀ T₀` (FrameClassical.lean): the same for representations of forms (frames X with
  Q₀ ∘ X = T₀); rational frames. `Measure.Weil.RatSphere Q₀ ρ` (Measure/Weil/SphereOrbitsNF.lean): {η ∈ F^N : Q₀(η) = ρ}.
* `repMeasureIso`, `isoStabMeasure` (IsoMeasures.lean): ρ¹, the same with the stabilizer measures restricted to the
  shells {0 ≤ log |χ_X|_∞ < 1} (the norm-one volumes).
* `Indefinite.repCount Q₀ T₀ i` (CorankOneCount.lean): #(Γ_i\R(M_i, T₀)) in [0, ∞], R(M_i, T₀) = `repsT`.
* `archFibrationNF`, `cInfNF` (SiegelComplex.lean): the archimedean sphere fibration (constructed from
  `realArchFibration`, `complexArchFibrationW`) and c_∞(m) = |d_F|^{-N(N-1)/4} ∏_w |2m|_w^{-(N-1)}.
* `frameArchFibrationNF`, `cInfTNF` (FormsIndefiniteNF.lean); `frameArchFibrationRank2`, `frameDensityProductReg`
  (FormsIndefiniteRank2.lean); `isoDensityProductReg` (FormsIndefiniteIso.lean); `cInfCorankOne`, `binDensityProduct`
  (SiegelCorankOne.lean): the frame fibrations, c_∞(T₀) = |d_F|^{-N(N-1)/4} ∏_w |det H_{T₀}|_w^{-n'},
  c⁽¹⁾_∞(Q₀) = |d_F|^{-N(N-1)/4} ∏_w |det H_{Q₀}|_w^{-1}, and the regularized local sides displayed in the docstrings.
* `finDensityProduct` (SiegelIndefinite.lean), `frameDensityProduct` (FormsIndefinite.lean),
  `ternaryDensityProductReg`, `not_isSquare_deltaForms_unary` (SiegelTernary.lean), `ternaryIsoDensityProductReg`,
  `isSquare_deltaForms_unary` (SiegelTernaryIso.lean), `ratFrameEquivRatSphere`, `unary_nondegenerate`
  (FormsIndefiniteChecks.lean): the local sides; vectors as 1-frames.
* `Frames.deltaForms`, `Frames.chiForms` (Tamagawa/FrameSiegelReg.lean): δ = -det H_{Q₀} det H_{T₀} and its quadratic
  character (0 at 𝔭 | 2δ). `LocalDensity.NF.localDensity v Q m`, `LocalDensity.NF.localDensityForm v Q T`
  (LocalDensity/NFFormDensity.lean): β_𝔭(L, m), β_𝔭(L, T). `LocalDensity.DVR.unary m` (LocalDensity/FormDensity.lean):
  the form ⟨m⟩ in one variable. `Measure.Weil.σR`, `Measure.Weil.σC` (Measure/Weil/AdelicSphere.lean): the real and
  complex embeddings of F indexed by the infinite places.

Exact mass formulas (paths in `Literature/`)
* `Tamagawa.Indefinite.DC Q₀`, `Tamagawa.Indefinite.unitGroup Q₀ i` (Tamagawa/Indefinite/ClassicalSetup.lean and
  ClassicalMeasures.lean, outside `Literature/`): the proper classes in the genus of 𝓞_F^n, and Γ_i = SO(L_i).

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).
-/

end QuadFormsKB.Headlines
