import QuadFormsKB.Tamagawa.Measure.Weil.GnatQuaternary
import QuadFormsKB.Tamagawa.Measure.Weil.GnatComparisonAny
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoIsotropic
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropicGauss

/-!
# $\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $\ge3$ over every number field

$F$ a number field. This file plugs together the three developments:

* **Archimedean comparison** (`GnatComparisonAny.lean`): `GnatTamagawaComparison F` from the named input
  `GnatMeasureComparisonNSIndef F` (`gnatTamagawaComparison_of_nsIndef`; the square model and the totally definite
  non-square models are theorems).
* **Quaternary case** (`GnatQuaternary.lean`): $\tau(SO(V)) = 2$ for every nondegenerate quaternary $V$ from
  `GnatTamagawaComparison F` (`tamagawaNumberTwoAdelic_quaternary`).
* **Combined induction** (`TauTwoIsotropic.lean`): the induction `tauTwoAll_of_inputs` from the quaternary base case
  `QuaternaryTauTwoBase F` and the per-dimension step inputs; **Poisson variant** (`TauTwoAnisotropicGauss.lean`): the
  anisotropic step inputs without the Poisson and vanishing fields (`AdelicStepInputsGauss`).

Results:

* **`quaternaryTauTwoBase_of_nsIndef`**: `QuaternaryTauTwoBase F` (hence `AnisotropicTauTwoBase F 4`) from
  `GnatMeasureComparisonNSIndef F`.
* **`AdelicWeilCoreGauss`**, **`AdelicConeStepInputsGauss`**: the cone step inputs with the Gaussian test function, so the
  twisted Poisson formula (`adelicThetaPoisson_gauss`) and the vanishing at non-represented classes
  (`nonrepresentedVanish_of_nondegenerate`) are no longer inputs; `AdelicConeStepInputsGauss.toAdelicConeStepInputs`.
* **`tauTwoAll_of_nsIndef`** (headline): $\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $n\ge3$ over $F$,
  conditional only on `GnatMeasureComparisonNSIndef F`, `AdelicStepInputsGauss F k` ($k\ge4$) and
  `AdelicConeStepInputsGauss F k` ($k\ge3$).
-/

open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta
  QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.ConeAdelic
  QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F]

/-! ### The quaternary base case -/

/-- **The quaternary base case from `GnatTamagawaComparison F`** (`tamagawaNumberTwoAdelic_quaternary`). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; §4.5 (induction base) [unverified page]"]
theorem quaternaryTauTwoBase_of_comparison (hC : GnatTamagawaComparison F) : QuaternaryTauTwoBase F :=
  ⟨fun Q₀ hQ => tamagawaNumberTwoAdelic_quaternary hC Q₀ hQ⟩

/-- **$\tau(SO(V)) = 2$ for every nondegenerate quaternary $V$ over every number field**, conditional only on the named
input `GnatMeasureComparisonNSIndef F` (Weil's local-ratio identity for the non-square models that are not totally
definite over a totally real field). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), pp. 63-65 [unverified page]; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_quaternary_of_nsIndef (h : GnatMeasureComparisonNSIndef F) (Q₀ : QuadForm (𝓞 F) 4)
    (hQ : Q₀.Nondegenerate) : TamagawaNumberTwoAdelic Q₀ hQ :=
  tamagawaNumberTwoAdelic_quaternary (gnatTamagawaComparison_of_nsIndef h) Q₀ hQ

/-- **The quaternary base case from the indefinite non-square input**. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; §4.5 (induction base) [unverified page]"]
theorem quaternaryTauTwoBase_of_nsIndef (h : GnatMeasureComparisonNSIndef F) : QuaternaryTauTwoBase F :=
  quaternaryTauTwoBase_of_comparison (gnatTamagawaComparison_of_nsIndef h)

/-- The anisotropic base case `AnisotropicTauTwoBase F 4` from the indefinite non-square input. -/
theorem anisotropicTauTwoBase_of_nsIndef (h : GnatMeasureComparisonNSIndef F) : AnisotropicTauTwoBase F 4 :=
  (quaternaryTauTwoBase_of_nsIndef h).anisotropic

/-! ### The cone step inputs with the Gaussian test function -/

variable {k : ℕ}

/-- **Weil's sphere data for one form with the Gaussian test function** ($Q_0$ in $k+1$ variables, any signature,
isotropic or not): `AdelicWeilCore` without the fields now proved (`poisson`, `vanish`), with $\Phi$ = `gaussTest` and
$\hat\Phi$ = `gaussTestHat Q₀` fixed. This is `AdelicWeilDataGauss` without the anisotropy field `aniso'`. The named inputs
among the fields are `fib`, `euler` and `eulerHat`; the rest are data and elementary conditions. Fields: `S`, `fib`, `Φr`,
`Ψ`, `κ`, `euler`, `κ_nonneg`, `b_eq`, `archTest`, `Φr_nonneg`, `archTestC`, `Ψ_nonneg`, `Φhr`, `Ψh`, `κh`, `eulerHat`,
`κh_nonneg`, `Φhr_nonneg`, `Ψh_nonneg`. -/
structure AdelicWeilCoreGauss (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) where
  /-- The sphere family. -/
  S : AdelicSphereFamily Q₀
  /-- Weil's fibration over each sphere (input). -/
  fib : S.Fibration hQ
  /-- Real-place data of $\Phi$. -/
  Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ
  /-- Complex-place data of $\Phi$. -/
  Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ
  /-- The measure constant for $\Phi$. -/
  κ : ℝ
  /-- The Euler-product identification for $\Phi$ (input). -/
  euler : AdelicSphericalEuler S (gaussTest F (k + 1)) Φr Ψ κ
  κ_nonneg : 0 ≤ κ
  /-- $\hat\Phi(0) = \int_{V_{\mathbb A}}\Phi = \kappa\cdot$ `phiIntegralNF`. -/
  b_eq : (muFinVec F (Fin (k + 1)) OHatVec).toReal = κ * phiIntegralNF Φr Ψ
  archTest : IsArchTestFn Q₀ Φr
  Φr_nonneg : ∀ w x, 0 ≤ Φr w x
  archTestC : IsArchTestFnC Q₀ Ψ
  Ψ_nonneg : ∀ w x, 0 ≤ Ψ w x
  /-- Real-place data of $\hat\Phi$. -/
  Φhr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ
  /-- Complex-place data of $\hat\Phi$. -/
  Ψh : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ
  /-- The measure constant for $\hat\Phi$. -/
  κh : ℝ
  /-- The Euler-product identification for $\hat\Phi$ (input). -/
  eulerHat : AdelicSphericalEuler S (gaussTestHat Q₀) Φhr Ψh κh
  κh_nonneg : 0 ≤ κh
  Φhr_nonneg : ∀ w x, 0 ≤ Φhr w x
  Ψh_nonneg : ∀ w x, 0 ≤ Ψh w x

/-- **`AdelicWeilCore` from `AdelicWeilCoreGauss`**: the Poisson field is `adelicThetaPoisson_gauss`, the vanishing field
is `nonrepresentedVanish_of_nondegenerate`. -/
def AdelicWeilCoreGauss.toAdelicWeilCore {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate}
    (W : AdelicWeilCoreGauss Q₀ hQ) : AdelicWeilCore Q₀ hQ where
  S := W.S
  fib := W.fib
  Φ := gaussTest F (k + 1)
  Φh := gaussTestHat Q₀
  measurable_Φ := measurable_gaussTest
  measurable_Φh := measurable_gaussTestHat Q₀
  poisson := adelicThetaPoisson_gauss hQ
  a := 1
  b := (muFinVec F (Fin (k + 1)) OHatVec).toReal
  a_nonneg := zero_le_one
  b_pos := muFinVec_OHatVec_toReal_pos
  Φ_zero := gaussTest_zero
  Φh_zero := gaussTestHat_zero Q₀
  Φr := W.Φr
  Ψ := W.Ψ
  κ := W.κ
  euler := W.euler
  κ_nonneg := W.κ_nonneg
  b_eq := W.b_eq
  archTest := W.archTest
  Φr_nonneg := W.Φr_nonneg
  archTestC := W.archTestC
  Ψ_nonneg := W.Ψ_nonneg
  vanish := nonrepresentedVanish_of_nondegenerate Q₀ hQ W.Φr W.Ψ
  Φhr := W.Φhr
  Ψh := W.Ψh
  κh := W.κh
  eulerHat := W.eulerHat
  κh_nonneg := W.κh_nonneg
  Φhr_nonneg := W.Φhr_nonneg
  Ψh_nonneg := W.Ψh_nonneg

/-- **The per-dimension cone inputs, Gaussian form** (**input**): every cone form
$\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ with $Q_0'$ nondegenerate in $k$ variables carries the sphere data
`AdelicWeilCoreGauss` (sphere fibration, the two spherical Euler-product identifications) and the cone inputs
`AdelicConeInputs` (cone fibration, the two cone Euler-product identifications) for $\Phi$ = `gaussTest`,
$\hat\Phi$ = `gaussTestHat`. It is `AdelicConeStepInputs` without the proved Poisson and vanishing fields, and contains no
covolume or Tamagawa number of the form itself. Field: `data`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (inputs of the induction step, isotropic case) [unverified page]"]
structure AdelicConeStepInputsGauss (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop where
  /-- The data for each cone form. -/
  data : ∀ (c₀ : 𝓞 F) (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) k) (hQ' : Q₀'.Nondegenerate)
    (hQ : (coneFormO c₀ Q₀').Nondegenerate),
    Nonempty (AdelicWeilCoreGauss (coneFormO c₀ Q₀') hQ ×
      AdelicConeInputs hc₀ hQ' hQ (gaussTest F (k + 1 + 1)) (gaussTestHat (coneFormO c₀ Q₀')))

theorem AdelicConeStepInputsGauss.toAdelicConeStepInputs (h : AdelicConeStepInputsGauss F k) :
    AdelicConeStepInputs F k :=
  ⟨fun c₀ hc₀ Q₀' hQ' hQ => (h.data c₀ hc₀ Q₀' hQ' hQ).map fun p => ⟨p.1.toAdelicWeilCore, p.2⟩⟩

/-! ### The final theorem -/

/-- **Weil's induction with the quaternary base case supplied by the quaternary results**
(from `GnatTamagawaComparison F`). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3, by induction on dim)"]
theorem tauTwoAll_of_comparison (hC : GnatTamagawaComparison F) (stepA : ∀ k, 4 ≤ k → AdelicStepInputs F k)
    (stepC : ∀ k, 3 ≤ k → AdelicConeStepInputs F k) : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_of_inputs (quaternaryTauTwoBase_of_comparison hC) stepA stepC

/-- **$\tau(SO(V)) = 2$ for every nondegenerate quadratic space $V$ of dimension $n\ge3$ over every number field $F$**
(Weil 1982, §4.5, pp. 108–109, and Thm 3.7.1 for $n = 3, 4$): every nondegenerate $Q_0$ over $\mathcal O_F$ in
$n\ge3$ variables, every signature, isotropic or anisotropic, any class number, has adelic covolume
$\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A_F)) = 2$ for the Tamagawa measure (`TamagawaNumberTwoAdelic`).
Conditional only on the named inputs

* `GnatMeasureComparisonNSIndef F` (dimension $4$: Weil's local-ratio identity $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the
  non-square quaternion models not totally definite over a totally real field);
* `AdelicStepInputsGauss F k` for $k\ge4$ (anisotropic forms in $k+1\ge5$ variables: the sphere fibration and the two
  spherical Euler-product identifications for the Gaussian);
* `AdelicConeStepInputsGauss F k` for $k\ge3$ (cone forms in $k+2\ge5$ variables: the same sphere inputs, the cone
  fibration and the two cone Euler-product identifications).

Dimension $3$ is unconditional (`tauTwoAll_three`). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_of_nsIndef (h : GnatMeasureComparisonNSIndef F) (stepA : ∀ k, 4 ≤ k → AdelicStepInputsGauss F k)
    (stepC : ∀ k, 3 ≤ k → AdelicConeStepInputsGauss F k) : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_of_inputs (quaternaryTauTwoBase_of_nsIndef h) (fun k hk => (stepA k hk).toAdelicStepInputs)
    (fun k hk => (stepC k hk).toAdelicConeStepInputs)

/-- **$\tau(SO(V)) = 2$ for every anisotropic $V$ of dimension $n\ge5$**, conditional only on
`GnatMeasureComparisonNSIndef F` and `AdelicStepInputsGauss F k` ($k\ge4$). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO) = 2 by induction on dim)"]
theorem anisotropicTauTwo_of_nsIndef (h : GnatMeasureComparisonNSIndef F)
    (step : ∀ k, 4 ≤ k → AdelicStepInputsGauss F k) : ∀ n, 5 ≤ n → AnisotropicTauTwo F n :=
  anisotropicTauTwo_of_inputs_gauss (anisotropicTauTwoBase_of_nsIndef h) step

end QuadFormsKB.Tamagawa.Measure.Weil
