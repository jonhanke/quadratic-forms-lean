import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoSphereEulerNF
import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerNF

/-!
# $\tau(SO(V)) = 2$ in every dimension $\ge3$ over every number field

$F$ any number field. With the sphere data `adelicWeilCoreB_gaussNF` and the cone Euler identifications
`adelicConeEuler_gaussTestNF`, `adelicConeEuler_gaussTestHatNF` (both over every number field):

* **`tamagawaNumberTwoAdelic_of_isotropicNF`**: $\tau(SO(V)) = 2$ for isotropic $V$ of dimension $k+2\ge5$ from
  $\tau = 2$ in dimension $k+1$ and finiteness of the covolume in dimension $k$;
* **`tauTwoAll_of_baseNF`**: Weil's induction from the quaternary base alone, every number field;
* **`tauTwoAll_uncondNF`**: $\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $\ge3$ over every number field,
  with the quaternary base `quaternaryTauTwoBase_of_nsIndef gnatMeasureComparisonNSIndef`.
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

/-- **$\tau(SO(V)) = 2$ for isotropic $V$ of dimension $k+2\ge5$ over every number field**, from $\tau = 2$ in
dimension $k+1$ and finiteness of the covolume in dimension $k$; no Euler input. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2, V isotropic, dim ≥ 5)"]
theorem tamagawaNumberTwoAdelic_of_isotropicNF (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1 + 1))
    (hQ : Q₀.Nondegenerate) (hiso : (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn F)
    (hτ : ∀ (Q : QuadForm (𝓞 F) (k + 1)) (hQ : Q.Nondegenerate), TamagawaNumberTwoAdelic Q hQ)
    (hcov : ∀ (Q : QuadForm (𝓞 F) k) (hQ : Q.Nondegenerate), covolSO Q hQ ≠ ⊤) :
    TamagawaNumberTwoAdelic Q₀ hQ := by
  obtain ⟨c₀, hc₀, Q₀', hQ', heq⟩ := covolume_muTam_eq_cone (by omega) Q₀ hQ hiso
  show covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2
  rw [heq]
  have hQc : (coneFormO c₀ Q₀').Nondegenerate :=
    nondegenerate_splitForm hc₀ (nondegenerate_splitForm (neg_ne_zero.mpr hc₀) hQ')
  exact tamagawaNumberTwoAdelic_cone_B hk hc₀ hQ' (adelicWeilCoreB_gaussNF (k := k + 1) hQc (by omega))
    { A := coneData hc₀ hQ' hk
      fib := coneFibration hc₀ hQ' hk
      euler := adelicConeEuler_gaussTestNF hc₀ hQ' hk hQc
      eulerHat := adelicConeEuler_gaussTestHatNF hc₀ hQ' hk hQc }
    ⟨fun c => hτ _ _⟩ (hcov _ _)

/-- **Weil's induction over every number field from the quaternary base alone**: $\tau(SO(V)) = 2$ for every
nondegenerate $V$ of dimension $m\ge3$, conditional only on `QuaternaryTauTwoBase F`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3, by induction on dim)"]
theorem tauTwoAll_of_baseNF (base : QuaternaryTauTwoBase F) : ∀ m, 3 ≤ m → TauTwoAll F m := by
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
      · exact tamagawaNumberTwoAdelic_of_anisotropicNF (by omega) hQ haniso hτ
      · refine tamagawaNumberTwoAdelic_of_isotropicNF (by omega) Q₀ hQ
          (isotropicIn_of_not_anisotropicF haniso) hτ fun Q hQ' => ?_
        exact (ih k (by omega) (by omega) Q hQ').finite.ne

/-- **$\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $n\ge3$ over every number field, unconditional**:
`tauTwoAll_of_baseNF` with the quaternary base `quaternaryTauTwoBase_of_nsIndef gnatMeasureComparisonNSIndef`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_uncondNF : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_of_baseNF (quaternaryTauTwoBase_of_nsIndef gnatMeasureComparisonNSIndef)

end QuadFormsKB.Tamagawa.Measure.Weil

end
