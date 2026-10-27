import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoFinal
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoIsotropicGauss
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereDensitiesProof
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqTauTwo
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSIndefFinal
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoSphereEuler
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAllNF

/-!
# The two release headlines

$F$ a number field. This file plugs every proved input of the Tamagawa development into the two final theorems.

## Summary for the 0.2.0 release

**Unconditional** (no hypotheses beyond those in the statement):

* (A) `tauTwoAll_release_uncond`:$\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $n\ge3$ over
  every number field; `tauTwoAll_release_totallyReal_uncond`: the same over every totally real number field (the
  earlier headline); `tauTwoQuaternary_release`: $n = 4$ over every number field; `tauTwoAll_three`: $n = 3$ over every
  number field.
* (B) `siegelIndefinite_release_totallyReal_uncond`: Siegel's formula for indefinite forms in $N\ge4$ variables over every
  totally real number field; `siegelIndefinite_release_quaternary_uncond`, `siegelIndefinite_release_quaternary_isSquare`,
  `siegel_release_quaternary_definite` ($N = 4$).

**Assume a false input (vacuous as stated).** `tauTwoAll_release`, `tauTwoAll_release_totallyReal`,
`siegelIndefinite_release_totallyReal` and their variants without the measure-comparison input
(`tauTwoAll_release_of_sphere_cone`, `tauTwoAll_release_totallyReal_of_sphere`,
`siegelIndefinite_release_totallyReal_of_sphere`) assume `AdelicSphereEulerGaussInputs F k` for every $k\ge4$, which is
false (its `eulerHat` field; counterexample over $\mathbb Q$ with $k = 4$). Their
statements are kept unchanged (reviewed statements); the unconditional headlines above do not use that input.

**Open:** Siegel's formula for indefinite forms over number fields with complex places (the indefinite Siegel track is
stated over totally real $F$).

The sections below describe the headlines in the order they were added.

## (A) $\tau(SO(V)) = 2$

* **`tauTwoAll_release`**: for every nondegenerate quadratic space $V$ of dimension $n\ge3$ over every number field $F$,
  $\tau(SO(V)) = 2$ (`TamagawaNumberTwoAdelic`), conditional only on the named inputs
  `GnatMeasureComparisonNSIndef F`, `AdelicSphereEulerGaussInputs F k` ($k\ge4$) and `AdelicConeEulerGaussInputs F k`
  ($k\ge3$).
* **`tauTwoAll_release_totallyReal`**: over a totally real field the cone Euler inputs are theorems
  (`adelicConeEulerGaussInputs_of_totallyReal`), so only `GnatMeasureComparisonNSIndef F` and
  `AdelicSphereEulerGaussInputs F k` ($k\ge4$) remain.
* Unconditional special cases already proved: $n = 3$ (`tauTwoAll_three`), $n = 4$ with square discriminant over every
  number field (`tamagawaNumberTwoAdelic_quaternary_of_isSquare`), $n = 4$ definite at every real place over a totally
  real field (`tamagawaNumberTwoAdelic_quaternary_definite`).

Proved and plugged in here (no longer inputs): the sphere fibration (`sphereFamily_fibration`, every number field), the
twisted Poisson formula and the vanishing at non-represented classes, the cone fibration (`coneFibration`,
every number field), the cone Euler identifications for the Gaussian test functions over a totally real field
(`adelicConeEuler_gaussTest`, `adelicConeEuler_gaussTestHat`), the measure comparison for the square quaternion model and
the totally definite non-square models.

## (B) Siegel's formula for indefinite forms (measure form, totally real $F$)

* **`siegelIndefinite_release_totallyReal`**: $N = k+1\ge4$ variables, conditional only on
  `GnatMeasureComparisonNSIndef F` and `AdelicSphereEulerGaussInputs F j` ($4\le j\le k$ is what is used; stated for all
  $j\ge4$).
* **`siegelIndefinite_release_quaternary`**: $N = 4$, conditional only on `GnatMeasureComparisonNSIndef F`.
* **`siegelIndefinite_release_quaternary_isSquare`**: $N = 4$, square discriminant: **unconditional**.
* **`siegel_release_quaternary_definite`**: $N = 4$, definite at every real place (not indefinite; same proof):
  **unconditional**.

`AdelicSphereFibration` and `AdelicSphereDensities` are proved for the constructed sphere data, so only
$\tau = 2$ enters Siegel's formula.

## The input `GnatMeasureComparisonNSIndef F` is a theorem

`gnatMeasureComparisonNSIndef` (GnatNSIndefFinal.lean) proves `GnatMeasureComparisonNSIndef F` for every number field.
The versions of the headlines without it, added next to the conditional ones:

* **`tauTwoQuaternary_release`**: $\tau(SO(V)) = 2$ for every nondegenerate quaternary $V$ over every number field:
  **unconditional** (with `quaternaryTauTwoBase_release`, `anisotropicTauTwoBase_four_release`).
* **`tauTwoAll_release_of_sphere_cone`**, **`tauTwoAll_release_totallyReal_of_sphere`**: as above, conditional only on the
  sphere (and, over a general field, cone) Euler inputs.
* **`siegelIndefinite_release_totallyReal_of_sphere`**: conditional only on `AdelicSphereEulerGaussInputs F j` ($j\ge4$).
* **`siegelIndefinite_release_quaternary_uncond`**: $N = 4$ over a totally real field: **unconditional**.

## Unconditional headlines over totally real $F$

The spherical Euler development (TauTwoSphereEuler.lean) replaces the false `eulerHat` field of
`AdelicSphereEulerGaussInputs` by the proved bound `mellinPhi_gaussTestHat_le` and proves
the remaining spherical Euler identity over every totally real field; its headlines are conditional only on
`GnatMeasureComparisonNSIndef F`, now a theorem. Hence:

* **`tauTwoAll_release_totallyReal_uncond`**: $\tau(SO(V)) = 2$, $n\ge3$, totally real $F$: **unconditional**.
* **`siegelIndefinite_release_totallyReal_uncond`**: Siegel's formula, $N\ge4$, totally real $F$: **unconditional**.

## $\tau(SO(V)) = 2$ over every number field

The development of TauTwoAllNF.lean and the `NF` files it imports proves the sphere and cone box formulas at the
complex places (with Weil's normalization `cxWeil`), the complex local spherical identity (`cplxZetaAt`),
the spherical Euler identity for the Gaussian (`adelicSphericalEuler_gaussTestNF`),
the bound for $\hat\Phi$ (`mellinPhi_gaussTestHat_le`)
and the cone Euler identifications (`adelicConeEuler_gaussTestNF`, `adelicConeEuler_gaussTestHatNF`) over every
number field. Hence:

* **`adelicConeEulerGaussInputs_uncond`**: the named input `AdelicConeEulerGaussInputs F k` is a theorem over every
  number field;
* **`tauTwoAll_release_uncond`**: $\tau(SO(V)) = 2$, $n\ge3$, every number field: **unconditional**.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta
  QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-! ### (A) The cone Euler inputs over a general number field -/

/-- **The cone Euler-product identifications for the Gaussian test functions, in dimension $k+2$** (**input**): for every
cone form $\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ (`coneFormO c₀ Q₀'`, $c_0\in\mathcal O_F\setminus0$, $Q_0'$
nondegenerate in $k\ge3$ variables) and the constructed adelic cone measure $\sigma_C$ (`(coneData hc₀ hQ' hk).σ`),
`AdelicConeEuler` holds for $\Phi$ = `gaussTest` and for $\hat\Phi$ = `gaussTestHat (coneFormO c₀ Q₀')`.

It is a statement about one measure on the adelic cone (its integral against a product test function factors into local
cone integrals); no covolume or Tamagawa number occurs. Over a totally real field it is a theorem
(`adelicConeEulerGaussInputs_of_totallyReal`), and over every number field (`adelicConeEulerGaussInputs_uncond`,
the box formula for $\sigma_C$ at the complex places). Field: `euler`. -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral as a product of local factors) [unverified page]"]
structure AdelicConeEulerGaussInputs (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop where
  /-- The two cone Euler identifications ($\Phi$, then $\hat\Phi$) for each cone form. -/
  euler : ∀ (c₀ : 𝓞 F) (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) k) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)
    (hQ : (coneFormO c₀ Q₀').Nondegenerate),
    AdelicConeEuler hc₀ Q₀' hQ (coneData hc₀ hQ' hk).σ (gaussTest F (k + 1 + 1)) ∧
      AdelicConeEuler hc₀ Q₀' hQ (coneData hc₀ hQ' hk).σ (gaussTestHat (coneFormO c₀ Q₀'))

/-- **The cone Euler inputs over a totally real field**. -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral as a product of local factors) [unverified page]"]
theorem adelicConeEulerGaussInputs_of_totallyReal [IsTotallyReal F] : AdelicConeEulerGaussInputs F k :=
  ⟨fun _ hc₀ _ hQ' hk hQ => ⟨adelicConeEuler_gaussTest hc₀ hQ' hk hQ, adelicConeEuler_gaussTestHat hc₀ hQ' hk hQ⟩⟩

/-- **The cone step inputs over every number field** from the spherical and the cone Euler inputs: the sphere family and
fibration, the Poisson and vanishing fields, the cone data and the cone fibration are proved. -/
@[kb "weil1982" "§4.5, pp. 108–109 (inputs of the induction step, isotropic case) [unverified page]"]
theorem adelicConeStepInputs_of_sphere_cone (hk : 3 ≤ k) (sph : AdelicSphereEulerGaussInputs F (k + 1))
    (cone : AdelicConeEulerGaussInputs F k) : AdelicConeStepInputs F k := by
  refine ⟨fun c₀ hc₀ Q₀' hQ' hQ => ?_⟩
  obtain ⟨E⟩ := sph.data (by omega) (coneFormO c₀ Q₀') hQ
  exact ⟨⟨E.toAdelicWeilCore,
    { A := coneData hc₀ hQ' hk
      fib := coneFibration hc₀ hQ' hk
      euler := (cone.euler c₀ hc₀ Q₀' hQ' hk hQ).1
      eulerHat := (cone.euler c₀ hc₀ Q₀' hQ' hk hQ).2 }⟩⟩

/-- **Weil's induction from the quaternary base and the two Euler inputs**, every number field. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3, by induction on dim)"]
theorem tauTwoAll_of_base_sphere_cone (base : QuaternaryTauTwoBase F)
    (sph : ∀ k, 4 ≤ k → AdelicSphereEulerGaussInputs F k) (cone : ∀ k, 3 ≤ k → AdelicConeEulerGaussInputs F k) :
    ∀ m, 3 ≤ m → TauTwoAll F m := by
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
      · refine tamagawaNumberTwoAdelic_of_isotropic (by omega) Q₀ hQ (isotropicIn_of_not_anisotropicF haniso)
          (adelicConeStepInputs_of_sphere_cone (by omega) (sph (k + 1) (by omega)) (cone k (by omega))) hτ
          fun Q hQ' => ?_
        exact (ih k (by omega) (by omega) Q hQ').finite.ne

/-- **Release headline (A): $\tau(SO(V)) = 2$ for every nondegenerate quadratic space $V$ of dimension $n\ge3$ over every
number field $F$** (Weil 1982, §4.5, pp. 108–109, and Thm 3.7.1 for $n = 3, 4$): every nondegenerate $Q_0$ over
$\mathcal O_F$ in $n\ge3$ variables, every signature, isotropic or anisotropic, any class number, has
$\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A_F)) = 2$ for the Tamagawa measure (`TamagawaNumberTwoAdelic`).

Conditional only on the named inputs

* `GnatMeasureComparisonNSIndef F` (used for $n\ge4$): Weil's local-ratio identity $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the
  non-square quaternion models that are not totally definite over a totally real field;
* `AdelicSphereEulerGaussInputs F k` for $k\ge4$ (used for $n\ge5$): the Euler-product identification of the adelic
  spherical integrals of the Gaussian test function and its transform;
* `AdelicConeEulerGaussInputs F k` for $k\ge3$ (used for isotropic $V$, $n\ge5$): the cone Euler identifications; a
  theorem over a totally real field (`tauTwoAll_release_totallyReal`).

Dimension $3$ is unconditional (`tauTwoAll_three`). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_release (h : GnatMeasureComparisonNSIndef F) (sph : ∀ k, 4 ≤ k → AdelicSphereEulerGaussInputs F k)
    (cone : ∀ k, 3 ≤ k → AdelicConeEulerGaussInputs F k) : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_of_base_sphere_cone (quaternaryTauTwoBase_of_nsIndef h) sph cone

/-- **Release headline (A), totally real $F$**: $\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $n\ge3$,
conditional only on `GnatMeasureComparisonNSIndef F` and `AdelicSphereEulerGaussInputs F k` ($k\ge4$); the cone Euler
inputs are theorems over a totally real field. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_release_totallyReal [IsTotallyReal F] (h : GnatMeasureComparisonNSIndef F)
    (sph : ∀ k, 4 ≤ k → AdelicSphereEulerGaussInputs F k) : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_release h sph fun _ _ => adelicConeEulerGaussInputs_of_totallyReal

/-- **$\tau(SO(V)) = 2$ for every nondegenerate quaternary $V$ over every number field — unconditional** (Weil 1982,
Thm 3.7.1, $m = 4$): `GnatMeasureComparisonNSIndef F` is the theorem `gnatMeasureComparisonNSIndef`. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), pp. 63-65 [unverified page]; Thm 2.3.1"]
theorem tauTwoQuaternary_release (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate) : TamagawaNumberTwoAdelic Q₀ hQ :=
  tamagawaNumberTwoAdelic_quaternary_of_nsIndef gnatMeasureComparisonNSIndef Q₀ hQ

/-- **The quaternary base case of the induction — unconditional** (every number field). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; §4.5 (induction base) [unverified page]"]
theorem quaternaryTauTwoBase_release : QuaternaryTauTwoBase F :=
  quaternaryTauTwoBase_of_nsIndef gnatMeasureComparisonNSIndef

/-- The anisotropic base case `AnisotropicTauTwoBase F 4` — unconditional (every number field). -/
theorem anisotropicTauTwoBase_four_release : AnisotropicTauTwoBase F 4 :=
  anisotropicTauTwoBase_of_nsIndef gnatMeasureComparisonNSIndef

/-- **Release headline (A) without the measure-comparison input**: $\tau(SO(V)) = 2$ for every nondegenerate $V$ of
dimension $n\ge3$ over every number field, conditional only on `AdelicSphereEulerGaussInputs F k` ($k\ge4$) and
`AdelicConeEulerGaussInputs F k` ($k\ge3$). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_release_of_sphere_cone (sph : ∀ k, 4 ≤ k → AdelicSphereEulerGaussInputs F k)
    (cone : ∀ k, 3 ≤ k → AdelicConeEulerGaussInputs F k) : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_release gnatMeasureComparisonNSIndef sph cone

/-- **Release headline (A), totally real $F$, without the measure-comparison input**: conditional only on
`AdelicSphereEulerGaussInputs F k` ($k\ge4$). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_release_totallyReal_of_sphere [IsTotallyReal F]
    (sph : ∀ k, 4 ≤ k → AdelicSphereEulerGaussInputs F k) : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_release_totallyReal gnatMeasureComparisonNSIndef sph

/-- **Release headline (A), totally real $F$ — unconditional**: $\tau(SO(V)) = 2$ for every nondegenerate quadratic space
$V$ of dimension $n\ge3$ over every totally real number field $F$ (Weil 1982, §4.5, pp. 108–109, and Thm 3.7.1 for
$n = 3, 4$): every nondegenerate $Q_0$ over $\mathcal O_F$ in $n\ge3$ variables, every signature, isotropic or
anisotropic, any class number, has $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A_F)) = 2$ for the Tamagawa
measure (`TamagawaNumberTwoAdelic`). No hypotheses: `tauTwoAll_totallyReal_of_nsIndef` (which does not
use `AdelicSphereEulerGaussInputs`) with the theorem `gnatMeasureComparisonNSIndef`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_release_totallyReal_uncond [IsTotallyReal F] : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_totallyReal_of_nsIndef gnatMeasureComparisonNSIndef

/-- **The cone Euler inputs over every number field**:`adelicConeEuler_gaussTestNF`,
`adelicConeEuler_gaussTestHatNF`. -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral as a product of local factors) [unverified page]"]
theorem adelicConeEulerGaussInputs_uncond : AdelicConeEulerGaussInputs F k :=
  ⟨fun _ hc₀ _ hQ' hk hQ => ⟨adelicConeEuler_gaussTestNF hc₀ hQ' hk hQ, adelicConeEuler_gaussTestHatNF hc₀ hQ' hk hQ⟩⟩

/-- **Release headline (A) — unconditional, every number field**: $\tau(SO(V)) = 2$ for every nondegenerate quadratic
space $V$ of dimension $n\ge3$ over every number field $F$ (Weil 1982, §4.5, pp. 108–109, and Thm 3.7.1 for
$n = 3, 4$): every nondegenerate $Q_0$ over $\mathcal O_F$ in $n\ge3$ variables, every signature, isotropic or
anisotropic, any class number, real and complex places, has $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A_F)) = 2$
for the Tamagawa measure in Weil's normalization (`TamagawaNumberTwoAdelic`, `muTam` with `cxWeil` at the complex
places). No hypotheses: `tauTwoAll_uncondNF`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3); Thm 3.7.1 (m = 3, 4), p. 65 [unverified page]"]
theorem tauTwoAll_release_uncond : ∀ n, 3 ≤ n → TauTwoAll F n :=
  tauTwoAll_uncondNF

/-! ### (B) Siegel's formula for indefinite forms -/

section Siegel

variable [IsTotallyReal F]

/-- **Release headline (B): Siegel's formula for indefinite forms over a totally real field, measure form**
($Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1\ge4$ variables, $m\in\mathcal O_F\setminus0$ with a rational point
$\xi$ on $Q_0 = m$; $M_i$ the classes in the genus, $\rho(M_i, m)$ the representation measures `repMeasure`, $v(M_i)$ the
unit volumes `unitVolume`, $\beta_\mathfrak p$ the local densities):
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$
The sphere fibration and the sphere densities are proved; $\tau = 2$ in dimensions $N$ and $N-1$ comes from
`tauTwoAll_release_totallyReal`. Conditional only on `GnatMeasureComparisonNSIndef F` and
`AdelicSphereEulerGaussInputs F j` ($j\ge4$; only $j\le k$ is used). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_release_totallyReal (h : GnatMeasureComparisonNSIndef F)
    (sph : ∀ j, 4 ≤ j → AdelicSphereEulerGaussInputs F j) {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate)
    (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_classical_totallyReal_of_tau hQ hk hm ξ
    (tauTwoAll_release_totallyReal h sph (k + 1) (by omega) Q₀ hQ) (tauTwoAll_release_totallyReal h sph k hk)

/-- **Siegel's formula for quaternary forms over a totally real field** ($N = 4$), conditional only on
`GnatMeasureComparisonNSIndef F`:
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-3/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real; N = 4) [unverified]"]
theorem siegelIndefinite_release_quaternary (h : GnatMeasureComparisonNSIndef F) (Q₀ : QuadForm (𝓞 F) 4)
    (hQ : Q₀.Nondegenerate) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := 3) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_classical_quaternary_of_tau Q₀ hQ hm ξ (tamagawaNumberTwoAdelic_quaternary_of_nsIndef h Q₀ hQ)

/-- **Release headline (B) without the measure-comparison input**: Siegel's formula for indefinite forms over a totally
real field in $N = k+1\ge4$ variables, conditional only on `AdelicSphereEulerGaussInputs F j` ($j\ge4$). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_release_totallyReal_of_sphere (sph : ∀ j, 4 ≤ j → AdelicSphereEulerGaussInputs F j)
    {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate)
    (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_release_totallyReal gnatMeasureComparisonNSIndef sph hQ hk hm ξ

/-- **Release headline (B) — unconditional: Siegel's formula for indefinite forms over a totally real field, measure
form** ($Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1\ge4$ variables, $m\in\mathcal O_F\setminus0$ with a rational
point $\xi$ on $Q_0 = m$; $M_i$ the classes in the genus, $\rho(M_i, m)$ the representation measures `repMeasure`,
$v(M_i)$ the unit volumes `unitVolume`, $\beta_\mathfrak p$ the local densities):
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$
No hypotheses beyond these: `siegelIndefinite_totallyReal_of_nsIndef` with the theorem
`gnatMeasureComparisonNSIndef`. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_release_totallyReal_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate)
    (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_totallyReal_of_nsIndef gnatMeasureComparisonNSIndef hQ hk hm ξ

/-- **Siegel's formula for quaternary forms over a totally real field — unconditional** ($N = 4$):
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-3/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real; N = 4) [unverified]"]
theorem siegelIndefinite_release_quaternary_uncond (Q₀ : QuadForm (𝓞 F) 4)
    (hQ : Q₀.Nondegenerate) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := 3) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_release_quaternary gnatMeasureComparisonNSIndef Q₀ hQ hm ξ

/-- **Siegel's formula for quaternary forms of square discriminant over a totally real field — unconditional**
($N = 4$, $\det$ of the Hessian a square in $F$). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real; N = 4) [unverified]"]
theorem siegelIndefinite_release_quaternary_isSquare (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate)
    (hsq : IsSquare ((algebraMap (𝓞 F) F) Q₀.hessian.det)) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := 3) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_classical_quaternary_of_tau Q₀ hQ hm ξ (tamagawaNumberTwoAdelic_quaternary_of_isSquare Q₀ hQ hsq)

/-- **Siegel's formula for quaternary forms definite at every real place over a totally real field — unconditional**
($N = 4$; the sign may differ from one real place to another). Not an indefinite case in Siegel's sense; listed because
the same proof gives it. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real; N = 4) [unverified]"]
theorem siegel_release_quaternary_definite (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate)
    (hdef : IsDefiniteAtRealPlaces Q₀) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := 3) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_classical_quaternary_of_tau Q₀ hQ hm ξ (tamagawaNumberTwoAdelic_quaternary_definite Q₀ hQ hdef)

end Siegel

end QuadFormsKB.Tamagawa.Measure.Weil

end
