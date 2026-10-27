import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerGaussHat
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereFibProof

/-!
# $\tau(SO(V)) = 2$ over a totally real field, with only the spherical Euler inputs open

$F$ totally real. For the Gaussian test function $\Phi$ = `gaussTest` and its transform $\hat\Phi$ = `gaussTestHat`:

* the sphere fibration is proved (`sphereFamily_fibration`), the twisted Poisson formula
  (`adelicThetaPoisson_gauss`) and the vanishing at non-represented classes (`nonrepresentedVanish_of_nondegenerate`)
  are proved;
* the cone fibration is proved (`coneFibration`), and the cone Euler identifications for $\Phi$ and $\hat\Phi$ are proved
  (`adelicConeEuler_gaussTest`, `adelicConeEuler_gaussTestHat`).

What remains of `AdelicWeilCore` is the spherical Euler-product identification (`AdelicSphericalEuler`) for $\Phi$
and $\hat\Phi$ with its archimedean data, bundled as **`AdelicSphereEulerGauss`** and, per dimension, as the input
**`AdelicSphereEulerGaussInputs`**. Hence:

* **`adelicConeStepInputs_of_gauss`**: `AdelicConeStepInputs` from `AdelicSphereEulerGaussInputs`;
* **`tamagawaNumberTwoAdelic_of_isotropic_gauss`**: $\tau = 2$ for isotropic $V$, $\dim V\ge5$, from the spherical Euler
  inputs, $\tau = 2$ in dimension $\dim V - 1$ and finiteness of the covolume in dimension $\dim V - 2$;
* **`tauTwoAll_of_inputs_gauss`**: $\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $\ge3$, conditional only on
  `QuaternaryTauTwoBase F` and `AdelicSphereEulerGaussInputs F k` ($k\ge4$).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta
  QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **The spherical Euler data for the Gaussian test functions** of the constructed sphere family
`sphereFamily hQ hk` ($Q_0$ nondegenerate in $k+1\ge4$ variables): archimedean data $\Phi_r,\Psi$ and a constant
$\kappa$ with `AdelicSphericalEuler` for $\Phi$ = `gaussTest` (`euler`) and $\hat\Phi(0) = \kappa\int\Phi_\infty$
(`b_eq`), and the same for $\hat\Phi$ = `gaussTestHat Q₀` (`eulerHat`). The named inputs among the fields are `euler`
and `eulerHat`; the rest are data and elementary conditions. Fields: `Φr`, `Ψ`, `κ`, `euler`, `κ_nonneg`, `b_eq`,
`archTest`, `Φr_nonneg`, `archTestC`, `Ψ_nonneg`, `Φhr`, `Ψh`, `κh`, `eulerHat`, `κh_nonneg`, `Φhr_nonneg`,
`Ψh_nonneg`. -/
structure AdelicSphereEulerGauss (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) where
  /-- Real-place data of $\Phi$. -/
  Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ
  /-- Complex-place data of $\Phi$. -/
  Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ
  /-- The measure constant for $\Phi$. -/
  κ : ℝ
  /-- The Euler-product identification for $\Phi$ (input). -/
  euler : AdelicSphericalEuler (sphereFamily hQ hk) (gaussTest F (k + 1)) Φr Ψ κ
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
  eulerHat : AdelicSphericalEuler (sphereFamily hQ hk) (gaussTestHat Q₀) Φhr Ψh κh
  κh_nonneg : 0 ≤ κh
  Φhr_nonneg : ∀ w x, 0 ≤ Φhr w x
  Ψh_nonneg : ∀ w x, 0 ≤ Ψh w x

/-- **`AdelicWeilCore` from the spherical Euler data**: the sphere family and its fibration are
given by (`sphereFamily`, `sphereFamily_fibration`), the Poisson field is `adelicThetaPoisson_gauss`, the vanishing
field is `nonrepresentedVanish_of_nondegenerate`. -/
def AdelicSphereEulerGauss.toAdelicWeilCore {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate} {hk : 3 ≤ k}
    (E : AdelicSphereEulerGauss Q₀ hQ hk) : AdelicWeilCore Q₀ hQ where
  S := sphereFamily hQ hk
  fib := sphereFamily_fibration hQ hk
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
  Φr := E.Φr
  Ψ := E.Ψ
  κ := E.κ
  euler := E.euler
  κ_nonneg := E.κ_nonneg
  b_eq := E.b_eq
  archTest := E.archTest
  Φr_nonneg := E.Φr_nonneg
  archTestC := E.archTestC
  Ψ_nonneg := E.Ψ_nonneg
  vanish := nonrepresentedVanish_of_nondegenerate Q₀ hQ E.Φr E.Ψ
  Φhr := E.Φhr
  Ψh := E.Ψh
  κh := E.κh
  eulerHat := E.eulerHat
  κh_nonneg := E.κh_nonneg
  Φhr_nonneg := E.Φhr_nonneg
  Ψh_nonneg := E.Ψh_nonneg

/-- **The spherical Euler inputs in dimension $k+1$** (**input**): every nondegenerate form in $k+1\ge4$ variables carries
`AdelicSphereEulerGauss` (the Euler-product identification of the adelic spherical integrals of the Gaussian test
function and its transform, for the constructed sphere family). It contains no covolume or Tamagawa number. Field:
`data`.

*Erratum:* this input is **false** in general: its field `eulerHat` uses the standard local factors of $Q_0$ for the
transform $\hat\Phi$, whose local lattices are the duals $H^{-1}\mathfrak d_v^{-1}\mathcal O_v^N$ (counterexample over
$\mathbb Q$: $x_0^2+x_1^2+x_2^2+x_3^2+3x_4^2$, $\rho = 1$ versus $\rho = 57$, at $p = 3$; see `docs/results/errata.md`).
Theorems assuming it are vacuous; the unconditional replacements are `tauTwoAll_release_uncond` and
`Indefinite.siegelIndefinite_uncond`. -/
@[kb "weil1982" "§4.5, (1), p. 102; p. 109 (the spherical integrals as Euler products) [unverified page]"]
structure AdelicSphereEulerGaussInputs (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop where
  /-- The data for each form. -/
  data : ∀ (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate), Nonempty (AdelicSphereEulerGauss Q₀ hQ hk)

/-- **The cone step inputs over a totally real field**: the cone data, `coneFibration` and the two cone Euler
identifications are proved; only the spherical Euler inputs remain. -/
@[kb "weil1982" "§4.5, pp. 108–109 (inputs of the induction step, isotropic case) [unverified page]"]
theorem adelicConeStepInputs_of_gauss [IsTotallyReal F] (hk : 3 ≤ k) (sph : AdelicSphereEulerGaussInputs F (k + 1)) :
    AdelicConeStepInputs F k := by
  refine ⟨fun c₀ hc₀ Q₀' hQ' hQ => ?_⟩
  obtain ⟨E⟩ := sph.data (by omega) (coneFormO c₀ Q₀') hQ
  exact ⟨⟨E.toAdelicWeilCore,
    { A := coneData hc₀ hQ' hk
      fib := coneFibration hc₀ hQ' hk
      euler := adelicConeEuler_gaussTest hc₀ hQ' hk hQ
      eulerHat := adelicConeEuler_gaussTestHat hc₀ hQ' hk hQ }⟩⟩

/-- **$\tau(SO(V)) = 2$ for isotropic $V$ of dimension $k+2\ge5$ over a totally real field** (Weil 1982, §4.5): from the
spherical Euler inputs (`AdelicSphereEulerGaussInputs`), $\tau = 2$ in dimension $k+1$ and finiteness of the covolume in
dimension $k$. The cone inputs are proved. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2, V isotropic, dim ≥ 5)"]
theorem tamagawaNumberTwoAdelic_of_isotropic_gauss [IsTotallyReal F] (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1 + 1))
    (hQ : Q₀.Nondegenerate) (hiso : (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn F)
    (sph : AdelicSphereEulerGaussInputs F (k + 1))
    (hτ : ∀ (Q : QuadForm (𝓞 F) (k + 1)) (hQ : Q.Nondegenerate), TamagawaNumberTwoAdelic Q hQ)
    (hcov : ∀ (Q : QuadForm (𝓞 F) k) (hQ : Q.Nondegenerate), covolSO Q hQ ≠ ⊤) :
    TamagawaNumberTwoAdelic Q₀ hQ :=
  tamagawaNumberTwoAdelic_of_isotropic hk Q₀ hQ hiso (adelicConeStepInputs_of_gauss hk sph) hτ hcov

/-- **Weil's induction over a totally real field, with only the spherical Euler inputs and the quaternary base open**:
$\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $m\ge3$ over the totally real field $F$,
anisotropic or isotropic, every signature, from `QuaternaryTauTwoBase F` and `AdelicSphereEulerGaussInputs F k` for
$k\ge4$. The sphere and cone fibrations, the Poisson formula, the vanishing at non-represented classes and the cone
Euler identifications are proved. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3, by induction on dim)"]
theorem tauTwoAll_of_inputs_gauss [IsTotallyReal F] (base : QuaternaryTauTwoBase F)
    (sph : ∀ k, 4 ≤ k → AdelicSphereEulerGaussInputs F k) : ∀ m, 3 ≤ m → TauTwoAll F m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases (show m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with rfl | rfl | h5
    · exact tauTwoAll_three
    · exact base.tau_two
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 + 1 := ⟨m - 2, by omega⟩
      intro Q₀ hQ
      have hτ : TauTwoAll F (k + 1) := ih (k + 1) (by omega) (by omega)
      by_cases haniso : AnisotropicF Q₀
      · obtain ⟨E⟩ := (sph (k + 1) (by omega)).data (by omega) Q₀ hQ
        exact tamagawaNumberTwoAdelic_of_anisotropic (k := k + 1) (by omega) haniso E.toAdelicWeilCore
          ⟨fun c => hτ _ _⟩
      · refine tamagawaNumberTwoAdelic_of_isotropic_gauss (by omega) Q₀ hQ (isotropicIn_of_not_anisotropicF haniso)
          (sph (k + 1) (by omega)) hτ fun Q hQ' => ?_
        exact (ih k (by omega) (by omega) Q hQ').finite.ne

end QuadFormsKB.Tamagawa.Measure.Weil

end
