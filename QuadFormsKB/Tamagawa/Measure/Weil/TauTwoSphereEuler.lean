import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoHatBound
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerGauss
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerHat
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerGaussFacts

/-!
# $\tau(SO(V)) = 2$ and Siegel's formula over a totally real field without the spherical Euler input

$F$ totally real. The spherical Euler identification is proved for the Gaussian test function
(**`adelicSphericalEuler_gaussTest`**: `AdelicSphericalEuler` with $\kappa = 1$, $\Phi_w = G$, for the constructed sphere
family, $N\ge5$; `lintegral_mellinPhi_gaussTest`). The Euler identification for $\hat\Phi$ asked for by
`AdelicSphereEulerGauss.eulerHat` is false in general and
is replaced by the pointwise bound `mellinPhi_gaussTestHat_le` through `AdelicWeilCoreB` (`TauTwoHatBound.lean`).
Hence:

* **`adelicWeilCoreB_gauss`**: the data of Weil's induction step for every nondegenerate $Q_0$ in $N\ge5$ variables, with
  no input left;
* **`tamagawaNumberTwoAdelic_of_isotropic_totallyReal`**, **`tauTwoAll_totallyReal_of_base`**: Weil's induction from the
  quaternary base alone;
* **`tauTwoAll_totallyReal_of_nsIndef`** (release headline (A), totally real): $\tau(SO(V)) = 2$ for every nondegenerate
  $V$ of dimension $\ge3$, conditional only on `GnatMeasureComparisonNSIndef F`;
* **`siegelIndefinite_totallyReal_of_nsIndef`** (release headline (B)): Siegel's formula for indefinite forms in
  $N\ge4$ variables, conditional only on `GnatMeasureComparisonNSIndef F`.

These replace `tauTwoAll_release_totallyReal` and `siegelIndefinite_release_totallyReal`, whose input
`AdelicSphereEulerGaussInputs` is false (its `eulerHat` field).
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

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {k : ℕ}

/-- **The adelic spherical integrals of the Gaussian are Weil's Euler products** (totally real $F$, $Q_0$ nondegenerate
in $N = k+1\ge5$ variables): `AdelicSphericalEuler` for the constructed sphere family, $\Phi$ = `gaussTest`,
$\Phi_w = G$ the standard Gaussian at every real place, $\kappa = 1$:
$Z(s,c) = |d_F|^{-N/2}\prod_wZ_w(s,\rho_c)\prod_\mathfrak pZ_\mathfrak p(s,\rho_c)$ for $s > 0$. -/
@[kb "weil1982" "§4.5, (1), p. 102; p. 109 (the spherical integrals as Euler products)"]
theorem adelicSphericalEuler_gaussTest {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    (hk4 : 4 ≤ k) :
    AdelicSphericalEuler (sphereFamily hQ hk) (gaussTest F (k + 1)) (fun _ => gaussFn) (fun _ _ => 0) 1 := by
  refine ⟨fun c s hs => ?_⟩
  unfold sphericalZetaAtNF
  rw [Finset.prod_eq_one (fun w _ => isEmptyElim w), mul_one, one_mul]
  exact (classSetup hQ (by omega) c).lintegral_mellinPhi_gaussTest (repρ_ne_zero c) hQ hk hk4 hs

/-- **The data of Weil's induction step for the Gaussian, with no input left** (totally real $F$, $Q_0$ nondegenerate in
$N = k+1\ge5$ variables): sphere family and fibration (`sphereFamily_fibration`), Poisson formula
(`adelicThetaPoisson_gauss`), Euler identification for $\Phi$ (`adelicSphericalEuler_gaussTest`), $\hat\Phi(0) =
\mu_f(\hat{\mathcal O}^N) = \int\Phi$, vanishing at non-represented classes, and the bound for $\hat\Phi$
(`mellinPhi_gaussTestHat_le`). -/
def adelicWeilCoreB_gauss {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk4 : 4 ≤ k) :
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
  Ψ := fun _ _ => 0
  κ := 1
  euler := adelicSphericalEuler_gaussTest hQ (by omega) hk4
  κ_nonneg := zero_le_one
  b_eq := muFinVec_eq_phiIntegralNF_gaussFn
  archTest := isArchTestFn_gaussFn Q₀
  Φr_nonneg := fun _ _ => (Real.exp_pos _).le
  archTestC := ⟨fun w => isEmptyElim w, fun w => isEmptyElim w⟩
  Ψ_nonneg := fun _ _ => le_rfl
  vanish := nonrepresentedVanish_of_nondegenerate Q₀ hQ _ _
  hatBound := mellinPhi_gaussTestHat_le hQ 1

/-- **$\tau(SO(V)) = 2$ for isotropic $V$ of dimension $k+2\ge5$ over a totally real field**, from $\tau = 2$ in
dimension $k+1$ and finiteness of the covolume in dimension $k$; no Euler input. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2, V isotropic, dim ≥ 5)"]
theorem tamagawaNumberTwoAdelic_of_isotropic_totallyReal (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1 + 1))
    (hQ : Q₀.Nondegenerate) (hiso : (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn F)
    (hτ : ∀ (Q : QuadForm (𝓞 F) (k + 1)) (hQ : Q.Nondegenerate), TamagawaNumberTwoAdelic Q hQ)
    (hcov : ∀ (Q : QuadForm (𝓞 F) k) (hQ : Q.Nondegenerate), covolSO Q hQ ≠ ⊤) :
    TamagawaNumberTwoAdelic Q₀ hQ := by
  obtain ⟨c₀, hc₀, Q₀', hQ', heq⟩ := covolume_muTam_eq_cone (by omega) Q₀ hQ hiso
  show covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2
  rw [heq]
  have hQc : (coneFormO c₀ Q₀').Nondegenerate :=
    nondegenerate_splitForm hc₀ (nondegenerate_splitForm (neg_ne_zero.mpr hc₀) hQ')
  exact tamagawaNumberTwoAdelic_cone_B hk hc₀ hQ' (adelicWeilCoreB_gauss (k := k + 1) hQc (by omega))
    { A := coneData hc₀ hQ' hk
      fib := coneFibration hc₀ hQ' hk
      euler := adelicConeEuler_gaussTest hc₀ hQ' hk hQc
      eulerHat := adelicConeEuler_gaussTestHat hc₀ hQ' hk hQc }
    ⟨fun c => hτ _ _⟩ (hcov _ _)

/-- **Weil's induction over a totally real field from the quaternary base alone**: $\tau(SO(V)) = 2$ for every
nondegenerate $V$ of dimension $m\ge3$, conditional only on `QuaternaryTauTwoBase F`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3, by induction on dim)"]
theorem tauTwoAll_totallyReal_of_base (base : QuaternaryTauTwoBase F) : ∀ m, 3 ≤ m → TauTwoAll F m := by
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
      · exact tamagawaNumberTwoAdelic_of_anisotropic_B (k := k + 1) (by omega) haniso
          (adelicWeilCoreB_gauss hQ (by omega)) ⟨fun c => hτ _ _⟩
      · refine tamagawaNumberTwoAdelic_of_isotropic_totallyReal (by omega) Q₀ hQ
          (isotropicIn_of_not_anisotropicF haniso) hτ fun Q hQ' => ?_
        exact (ih k (by omega) (by omega) Q hQ').finite.ne

/-- **Release headline (A), totally real $F$, without the spherical Euler input**: $\tau(SO(V)) = 2$ for every
nondegenerate quadratic space $V$ of dimension $n\ge3$ over a totally real field $F$ (every signature, isotropic or
anisotropic), conditional only on the named input `GnatMeasureComparisonNSIndef F` (used for $n\ge4$). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_totallyReal_of_nsIndef (h : GnatMeasureComparisonNSIndef F) : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_totallyReal_of_base (quaternaryTauTwoBase_of_nsIndef h)

/-- **Release headline (B), without the spherical Euler input: Siegel's formula for indefinite forms over a totally real
field, measure form** ($Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1\ge4$ variables, $m\in\mathcal O_F\setminus0$ with
a rational point $\xi$ on $Q_0 = m$):
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i),$$
conditional only on `GnatMeasureComparisonNSIndef F`. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_totallyReal_of_nsIndef (h : GnatMeasureComparisonNSIndef F) {Q₀ : QuadForm (𝓞 F) (k + 1)}
    (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_classical_totallyReal_of_tau hQ hk hm ξ
    (tauTwoAll_totallyReal_of_nsIndef h (k + 1) (by omega) Q₀ hQ) (tauTwoAll_totallyReal_of_nsIndef h k hk)

end QuadFormsKB.Tamagawa.Measure.Weil

end
