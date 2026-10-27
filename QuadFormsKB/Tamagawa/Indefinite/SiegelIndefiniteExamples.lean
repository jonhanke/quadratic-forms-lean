/-
# Siegel's formula for indefinite forms: norm forms of quaternion division algebras

**Layer:** number fields. (what is unconditional today).

Let $F$ be a number field, $a, b\in\mathcal O_F\setminus0$ with $D = (a,b)_F$ a **division** algebra, of any signature
(definite or indefinite at each real place). The norm form $Q_0 = \langle1,-a,-b,ab\rangle$ (`qSq a b`, $N = 4$)
represents $m = 1$ at $\xi = e_0$, and $\xi^\perp$ carries the pure form $Q' = \langle-a,-b,ab\rangle$ (`pureFormO a b`), the
reduced norm on the trace-zero quaternions. For these data:
* $\tau(SO(Q')) = 2$ is **proved** (`tamagawaNumberTwoAdelic_pureForm`, every number field, every signature);
* $\tau(SO(Q_0)) = 2$ is `tamagawaNumberTwoAdelic_qSq`, conditional on the named input `GnatTamagawaComparison`.

**Proves**
* `lintegral_theta_quatNorm`: $\int_E\theta\,d\mu = 2\int_{T(1)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}$, using only
  the `AdelicSphereFibration` (the factor $\tau(SO(Q')) = 2$ is proved);
* `siegelIndefinite_adelic_quatNorm`: the mean value of $\theta$ is $\int\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}$, given in
  addition `GnatTamagawaComparison`;
* `siegelIndefinite_classical_quatNorm` (totally real $F$): $c_\infty(1)\sum_i\rho(M_i, 1) =
  |d_F|^{-3/2}\prod_\mathfrak p\beta_\mathfrak p(L, 1)\cdot\sum_iv(M_i)$, given in addition `AdelicSphereDensities`.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelIndefinite
import QuadFormsKB.Tamagawa.Measure.Weil.GnatTamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchRatio

open MeasureTheory Measure Set NumberField IsDedekindDomain Quaternion
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.QuatZeta

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
  (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) (hQ : (qSq a b).Nondegenerate)

omit [NumberField F] in
theorem one_coe_ne_zero : ((1 : 𝓞 F) : F) ≠ 0 := by simp

include hdiv

/-- **The theta integral of the norm form of a quaternion division algebra** (any number field, any signature):
given Weil's adelic fibration over $T(1)$ with stabilizer $SO(\langle-a,-b,ab\rangle)$ (`AdelicSphereFibration`,
input),
$$\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu = 2\int_{T(1)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}.$$
The factor $2 = \tau(SO(\langle-a,-b,ab\rangle))$ is proved. -/
@[kb "weil1982" "§4.5, p. 109; Thm 3.7.1 (m = 3), p. 65 [unverified page]"]
theorem lintegral_theta_quatNorm {A : AdelicSphereData (qSq a b) ((1 : 𝓞 F) : F) (pureFormO a b)}
    (hA : AdelicSphereFibration (qSq a b) hQ (nondegenerate_pureFormO a b ha hb) A)
    {Φ : VInf F 4 → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele (qSq a b))}
    (hE : IsFundamentalDomain (GammaSOAdele (qSq a b)) E (muTam (qSq a b) hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratA (qSq a b) ((1 : 𝓞 F) : F)) (ratF (qSq a b) ((1 : 𝓞 F) : F)) Φ (latHat F 4) g
        ∂muTam (qSq a b) hQ (fun _ => 1) =
      2 * ∫⁻ x, testFn Φ x.1 ∂A.σ := by
  rw [lintegral_theta_adelic (qSq a b) hQ (by norm_num) one_coe_ne_zero hA hΦ hE]
  have h : covolume (GammaSOAdele (pureFormO a b)) (SOAdele (pureFormO a b))
      (muTam (pureFormO a b) (nondegenerate_pureFormO a b ha hb) fun _ => 1) = 2 :=
    tamagawaNumberTwoAdelic_pureForm a b ha hb hdiv
  rw [h]

/-- **Siegel's formula for the norm form of a quaternion division algebra, adelic form** (any number field, any
signature): given `AdelicSphereFibration` and `GnatTamagawaComparison` (inputs), the mean value of $\theta$ over
$SO(V)(F)\backslash SO(V)(\mathbb A)$ is $\int_{T(1)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}$. -/
@[kb "weil1982" "§4.5, p. 109; Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem siegelIndefinite_adelic_quatNorm (hC : GnatTamagawaComparison F)
    {A : AdelicSphereData (qSq a b) ((1 : 𝓞 F) : F) (pureFormO a b)}
    (hA : AdelicSphereFibration (qSq a b) hQ (nondegenerate_pureFormO a b ha hb) A)
    {Φ : VInf F 4 → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele (qSq a b))}
    (hE : IsFundamentalDomain (GammaSOAdele (qSq a b)) E (muTam (qSq a b) hQ fun _ => 1)) :
    (∫⁻ g in E, thetaFn (ratA (qSq a b) ((1 : 𝓞 F) : F)) (ratF (qSq a b) ((1 : 𝓞 F) : F)) Φ (latHat F 4) g
        ∂muTam (qSq a b) hQ (fun _ => 1)) /
        covolume (GammaSOAdele (qSq a b)) (SOAdele (qSq a b)) (muTam (qSq a b) hQ fun _ => 1) =
      ∫⁻ x, testFn Φ x.1 ∂A.σ :=
  siegelIndefinite_adelic (qSq a b) hQ (by norm_num) one_coe_ne_zero hA
    (tamagawaNumberTwoAdelic_qSq hC ha hb hQ) (tamagawaNumberTwoAdelic_pureForm a b ha hb hdiv) hΦ hE

/-- **Siegel's formula for the norm form of a quaternion division algebra over a totally real field, classical
measure form** ($N = 4$, $m = 1$, any signature): given `AdelicSphereFibration`, `AdelicSphereDensities` and
`GnatTamagawaComparison` (inputs),
$$c_\infty(1)\sum_i\rho(M_i, 1) = |d_F|^{-3/2}\prod_\mathfrak p\beta_\mathfrak p(L, 1)\cdot\sum_iv(M_i),$$
$L = \mathcal O_F^4$ with $Q_0 = \langle1,-a,-b,ab\rangle$, $c_\infty(1) = c_F\,2^{-3r_1}$ (`cInf`). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form); N = 4 [unverified]"]
theorem siegelIndefinite_classical_quatNorm [IsEmpty {w : InfinitePlace F // w.IsComplex}]
    (hC : GnatTamagawaComparison F) {A : AdelicSphereData (qSq a b) ((1 : 𝓞 F) : F) (pureFormO a b)}
    (hA : AdelicSphereFibration (qSq a b) hQ (nondegenerate_pureFormO a b ha hb) A)
    (hβ : AdelicSphereDensities (qSq a b) A (sigInf (qSq a b) ((1 : 𝓞 F) : F)) (τInf (qSq a b) ((1 : 𝓞 F) : F))) :
    cInf (k := 3) ((1 : 𝓞 F) : F) *
        ∑' i, repMeasure (qSq a b) hQ ((1 : 𝓞 F) : F)
          (totallyRealArchFibration (qSq a b) hQ one_coe_ne_zero (by norm_num)) i =
      ENNReal.ofReal (finDensityProduct (qSq a b) 1) * ∑' i, unitVolume (qSq a b) hQ i :=
  siegelIndefinite_classical_totallyReal (qSq a b) hQ (by norm_num) one_coe_ne_zero hA hβ
    (tamagawaNumberTwoAdelic_qSq hC ha hb hQ) (tamagawaNumberTwoAdelic_pureForm a b ha hb hdiv)

end QuadFormsKB.Tamagawa.Indefinite
