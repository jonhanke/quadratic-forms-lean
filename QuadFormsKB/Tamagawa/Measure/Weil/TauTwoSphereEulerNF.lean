import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoSphereEuler
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerGaussNF

/-!
# Weil's induction step over every number field, sphere side
$F$ any number field. The spherical Euler identification for the Gaussian test function over every number field
(**`adelicSphericalEuler_gaussTestNF`**: `AdelicSphericalEuler` with $\kappa = 1$, $\Phi_w = G$ at the real places,
$\Psi_w = G_{\mathbb C}$ = `gaussFnC` at the complex places; `lintegral_mellinPhi_gaussTestNF`), and with it the data of
Weil's induction step with no input left (**`adelicWeilCoreB_gaussNF`**) and the anisotropic step
(**`tamagawaNumberTwoAdelic_of_anisotropicNF`**): $\tau(SO(V)) = 2$ for anisotropic $V$ of dimension $N\ge5$ from
$\tau = 2$ in dimension $N-1$. The bound for $\hat\Phi$ is `mellinPhi_gaussTestHat_le`, now over every number field.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.SphericalZeta QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.Measure.ConeAdelic QuadFormsKB.Tamagawa.Measure.ConeAlgebra
  QuadFormsKB.Tamagawa.Measure.ConeReduction QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **The adelic spherical integrals of the Gaussian are Weil's Euler products over every number field** ($Q_0$
nondegenerate in $N = k+1\ge5$ variables): `AdelicSphericalEuler` for the constructed sphere family, $\Phi$ =
`gaussTest`, $\Phi_w = G$ at the real places, $\Psi_w = G_{\mathbb C}(x) = e^{-2\pi\sum|x_i|^2}$ at the complex places,
$\kappa = 1$. -/
@[kb "weil1982" "§4.5, (1), p. 102; p. 109 (the spherical integrals as Euler products)"]
theorem adelicSphericalEuler_gaussTestNF {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    (hk4 : 4 ≤ k) :
    AdelicSphericalEuler (sphereFamily hQ hk) (gaussTest F (k + 1)) (fun _ => gaussFn) (fun _ => gaussFnC) 1 := by
  refine ⟨fun c s hs => ?_⟩
  rw [one_mul]
  exact (classSetup hQ (by omega) c).lintegral_mellinPhi_gaussTestNF (repρ_ne_zero c) hQ hk hk4 hs

theorem phiIntegralNF_gaussFnC {n : ℕ} :
    phiIntegralNF (F := F) (n := n) (fun _ : RealPlace F => gaussFn) (fun _ => gaussFnC) =
      |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) := by
  rw [phiIntegralNF, phiIntegral_eq]
  simp [integral_gaussFn, integral_gaussFnC]

theorem muFinVec_eq_phiIntegralNF_gaussFnC {n : ℕ} :
    (muFinVec F (Fin n) OHatVec).toReal =
      1 * phiIntegralNF (n := n) (fun _ : RealPlace F => gaussFn) (fun _ => gaussFnC) := by
  rw [one_mul, phiIntegralNF_gaussFnC, toReal_muFinVec_OHatVec']

/-- **The data of Weil's induction step for the Gaussian, every number field, no input left** ($Q_0$ nondegenerate
in $N = k+1\ge5$ variables). -/
def adelicWeilCoreB_gaussNF {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk4 : 4 ≤ k) :
    AdelicWeilCoreB Q₀ hQ where
  S := sphereFamily hQ (by omega)
  fib := sphereFamily_fibration hQ (by omega)
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
  Φr := fun _ => gaussFn
  Ψ := fun _ => gaussFnC
  κ := 1
  euler := adelicSphericalEuler_gaussTestNF hQ (by omega) hk4
  κ_nonneg := zero_le_one
  b_eq := muFinVec_eq_phiIntegralNF_gaussFnC
  archTest := isArchTestFn_gaussFn Q₀
  Φr_nonneg := fun _ _ => (Real.exp_pos _).le
  archTestC := isArchTestFnC_gaussFnC Q₀
  Ψ_nonneg := fun _ _ => (Real.exp_pos _).le
  vanish := nonrepresentedVanish_of_nondegenerate Q₀ hQ _ _
  hatBound := mellinPhi_gaussTestHat_le hQ 1

/-- **$\tau(SO(V)) = 2$ for anisotropic $V$ of dimension $k+2\ge5$ over every number field**, from $\tau = 2$ in
dimension $k+1$. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2, V anisotropic, dim ≥ 5)"]
theorem tamagawaNumberTwoAdelic_of_anisotropicNF (hk : 3 ≤ k) {Q₀ : QuadForm (𝓞 F) (k + 1 + 1)}
    (hQ : Q₀.Nondegenerate) (haniso : AnisotropicF Q₀)
    (hτ : ∀ (Q : QuadForm (𝓞 F) (k + 1)) (hQ : Q.Nondegenerate), TamagawaNumberTwoAdelic Q hQ) :
    TamagawaNumberTwoAdelic Q₀ hQ :=
  tamagawaNumberTwoAdelic_of_anisotropic_B (k := k + 1) (by omega) haniso
    (adelicWeilCoreB_gaussNF hQ (by omega)) ⟨fun c => hτ _ _⟩

end QuadFormsKB.Tamagawa.Measure.Weil

end
