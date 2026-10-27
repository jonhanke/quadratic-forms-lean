import QuadFormsKB.Tamagawa.Measure.Weil.ThetaPoissonSO
import QuadFormsKB.Tamagawa.Measure.Weil.NonrepresentedVanishProof

/-!
# Weil's induction for anisotropic forms without the Poisson and vanishing inputs

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $m = k+1$ variables. The file `TauTwoAnisotropic.lean`
proves $\tau(SO(V)) = 2$ for anisotropic $V$ of dimension $m\ge5$ from the data `AdelicWeilData`, whose named inputs are
`fib`, `poisson` (`AdelicThetaPoisson`), `euler`, `vanish` (`NonrepresentedVanish`) and `eulerHat`. Two of them are now
proved:

* `AdelicThetaPoisson` for the Gaussian $\Phi = G\otimes\mathbf 1_{\hat{\mathcal O}^m}$ (`gaussTest`) and its transform
  $\hat\Phi$ (`gaussTestHat`): `adelicThetaPoisson_gauss` (ThetaPoissonSO.lean);
* `NonrepresentedVanish` for every nondegenerate form: `nonrepresentedVanish_of_nondegenerate`
  (NonrepresentedVanishProof.lean, Hasse–Minkowski for representations).

This file packages the remaining data as `AdelicWeilDataGauss` (the test function is fixed to the Gaussian: $\Phi(0) = 1$,
$\hat\Phi(0) = \mu_f(\hat{\mathcal O}^m) = |d_F|^{-m/2}$), builds `AdelicWeilData` from it (`AdelicWeilDataGauss.toAdelicWeilData`)
and restates the consumers:

* **`tamagawaNumberTwoAdelic_of_anisotropic_gauss`**: $\tau(SO(V)) = 2$ for anisotropic $V$, $\dim V\ge5$, from
  `AdelicWeilDataGauss` (inputs: the fibration and the two Euler-product identifications only) and the induction
  hypothesis `AdelicComplementTauTwo`;
* **`anisotropicTauTwo_of_inputs_gauss`**: the induction, from `AnisotropicTauTwoBase F 4` and `AdelicStepInputsGauss`.
-/

open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta
  QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### The Gaussian test functions: measurability and values at $0$ -/

theorem measurable_gV_fst : Measurable fun y : AdeleSpace F (Fin n) => ENNReal.ofReal (gV fun i => (y i).1) := by
  refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
  exact continuous_gR.measurable.comp (measurable_fst.comp (measurable_pi_apply i))

theorem measurable_snd_vec : Measurable fun y : AdeleSpace F (Fin n) => fun i => (y i).2 :=
  measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i)

theorem measurable_gaussTest : Measurable (gaussTest F n) := by
  refine Measurable.mul ?_ measurable_gV_fst
  exact (measurable_const.indicator (MeasurableSet.univ_pi fun _ => measurableSet_OHat)).comp measurable_snd_vec

theorem measurable_gaussDualTest : Measurable (gaussDualTest F n) := by
  refine Measurable.mul ?_ measurable_gV_fst
  exact (measurable_const.indicator measurableSet_DHatVec).comp measurable_snd_vec

theorem measurable_gaussTestHat (Q₀ : QuadForm (𝓞 F) n) : Measurable (gaussTestHat Q₀) :=
  measurable_const.mul (measurable_gaussDualTest.comp (continuous_const.matrix_mulVec continuous_id).measurable)

theorem gV_zero_fst : (gV fun i => ((0 : AdeleSpace F (Fin n)) i).1) = 1 := gV_zero

theorem gaussTest_zero : gaussTest F n 0 = ENNReal.ofReal 1 := by
  rw [gaussTest, gV_zero_fst, indicator_of_mem (show (fun i => ((0 : AdeleSpace F (Fin n)) i).2) ∈
    (OHatVec : Set (Fin n → AF)) from fun i _ => zero_mem_OHat), one_mul]

theorem gaussDualTest_zero : gaussDualTest F n 0 = 1 := by
  rw [gaussDualTest, gV_zero_fst, indicator_of_mem (show (fun i => ((0 : AdeleSpace F (Fin n)) i).2) ∈
    {c : Fin n → AF | ∀ i, c i ∈ DHat} from fun i => zero_mem_DHat), one_mul, ENNReal.ofReal_one]

/-- $\hat\Phi(0) = \mu_f(\hat{\mathcal O}^n)$, a positive real number. -/
theorem gaussTestHat_zero (Q₀ : QuadForm (𝓞 F) n) :
    gaussTestHat Q₀ 0 = ENNReal.ofReal (muFinVec F (Fin n) OHatVec).toReal := by
  rw [gaussTestHat, Matrix.mulVec_zero, gaussDualTest_zero, mul_one, ENNReal.ofReal_toReal muFinVec_OHatVec_ne_top]

theorem muFinVec_OHatVec_toReal_pos : 0 < (muFinVec F (Fin n) OHatVec).toReal :=
  ENNReal.toReal_pos muFinVec_OHatVec_ne_zero muFinVec_OHatVec_ne_top

/-! ### The data, the consumers -/

variable {k : ℕ}

/-- **Weil's data for one form with the Gaussian test function**: `AdelicWeilData` without the fields now proved
(`poisson`, `vanish`), with $\Phi$ = `gaussTest` and $\hat\Phi$ = `gaussTestHat Q₀` fixed, so $\Phi(0) = 1$ and
$\hat\Phi(0) = \mu_f(\hat{\mathcal O}^{k+1})$. The named inputs among the fields are `fib`, `euler` and `eulerHat`; the rest are
data and elementary conditions. -/
structure AdelicWeilDataGauss (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) where
  /-- The sphere family. -/
  S : AdelicSphereFamily Q₀
  /-- Weil's fibration over each sphere (input). -/
  fib : S.Fibration hQ
  /-- The complements are anisotropic. -/
  aniso' : ∀ c, AnisotropicF (S.Q' c)
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

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate}

/-- **`AdelicWeilData` from `AdelicWeilDataGauss`**: the Poisson field is `adelicThetaPoisson_gauss`, the vanishing field is
`nonrepresentedVanish_of_nondegenerate`. -/
def AdelicWeilDataGauss.toAdelicWeilData (W : AdelicWeilDataGauss Q₀ hQ) : AdelicWeilData Q₀ hQ where
  S := W.S
  fib := W.fib
  aniso' := W.aniso'
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

/-- **$\tau(SO(V)) = 2$ for anisotropic $V$ of dimension $m = k+1\ge5$, without the Poisson and vanishing inputs**
(Weil 1982, §4.5, pp. 108–109): from `AdelicWeilDataGauss` (named inputs: the fibration and the two Euler-product
identifications) and the induction hypothesis `AdelicComplementTauTwo` in dimension $m-1$. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(G) = 2 by comparing the residues of Z(s) at s = 0)"]
theorem tamagawaNumberTwoAdelic_of_anisotropic_gauss (hk : 4 ≤ k) (haniso : AnisotropicF Q₀)
    (W : AdelicWeilDataGauss Q₀ hQ) (hτ : AdelicComplementTauTwo W.S) : TamagawaNumberTwoAdelic Q₀ hQ :=
  tamagawaNumberTwoAdelic_of_anisotropic hk haniso W.toAdelicWeilData.toAdelicWeilCore hτ

/-- **Weil's per-dimension inputs, Gaussian form** (**input**): every anisotropic nondegenerate form in $k+1$ variables
carries `AdelicWeilDataGauss` (the fibration and the Euler-product identifications for the Gaussian test function).
Field: `data`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (inputs of the induction step) [unverified page]"]
structure AdelicStepInputsGauss (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop where
  /-- The data for each anisotropic form. -/
  data : ∀ (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate), AnisotropicF Q₀ →
    Nonempty (AdelicWeilDataGauss Q₀ hQ)

theorem AdelicStepInputsGauss.toAdelicStepInputs (h : AdelicStepInputsGauss F k) : AdelicStepInputs F k :=
  ⟨fun Q₀ hQ haniso => (h.data Q₀ hQ haniso).map AdelicWeilDataGauss.toAdelicWeilData⟩

/-- **Weil's induction for anisotropic forms, without the Poisson and vanishing inputs**:
from the base case $m = 4$ and `AdelicStepInputsGauss`, $\tau(SO(V)) = 2$ for every anisotropic $V$ of dimension
$m\ge5$ over the number field $F$. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO) = 2 by induction on dim)"]
theorem anisotropicTauTwo_of_inputs_gauss (base : AnisotropicTauTwoBase F 4)
    (step : ∀ k, 4 ≤ k → AdelicStepInputsGauss F k) : ∀ m, 5 ≤ m → AnisotropicTauTwo F m :=
  anisotropicTauTwo_of_inputs base fun k hk => (step k hk).toAdelicStepInputs

end QuadFormsKB.Tamagawa.Measure.Weil
