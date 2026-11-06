/-
# Siegel's formula for indefinite forms: the remaining statements without inputs
**Layer:** number fields. Every named input of the indefinite Siegel formula is now a theorem on main:
* $\tau(SO(V)) = 2$ for every nondegenerate form in $n\ge3$ variables over every number field (`tauTwoAll_release_uncond`);
* Weil's adelic fibration over the sphere $T(m)$ for the constructed sphere data, $N = k+1\ge4$
  (`AdelicSphereSetup.sphereFibration`);
* the density identity `AdelicSphereDensities` over every number field, complex places included
  (`adelicSphereDensitiesNF`), and the archimedean fibration at real and complex places (`archFibrationNF`).

The headline `siegelIndefinite_uncond` (every number field, every signature, $N\ge4$) already uses them. This file states
the forms of the theorem that were still only available with the inputs as hypotheses, now without inputs.

**Proves** ($F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1$ variables, any signature)
* `tsum_unitVolume_ne_zero_uncond`, `tsum_unitVolume_ne_top_uncond`: $0 < \sum_iv(M_i) < \infty$ ($N\ge3$);
* `lintegral_theta_adelic_uncond`, **`siegelIndefinite_adelic_uncond`** ($N\ge4$): the adelic form
  (`siegelIndefinite_adelic` without `AdelicSphereFibration` and $\tau = 2$, for the constructed sphere data);
* **`siegelWeil_indefinite_uncond`** ($N\ge4$): Weil's form with the local densities,
  $$\frac{1}{\operatorname{covol}}\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu
    = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\int_{T_\infty}\Phi\,d\sigma_\infty;$$
* **`siegelIndefinite_div_uncond`** ($N\ge4$): the ratio form over every number field;
* `siegelIndefinite_of_subsingleton_uncond`, **`siegelIndefinite_oneClass_uncondNF`**, `siegelIndefinite_oneClass_div_uncondNF`
  ($N\ge4$): one proper class in the genus, over every number field with $\mathcal O_F$ a principal ideal domain
  (`siegelIndefinite_oneClass_uncond` needed $F$ totally real);
* `siegelIndefinite_ternary_oneClass_uncond`, `siegelIndefinite_ternary_isotropic_oneClass_uncond` ($N = 3$): the same for
  ternary forms, with the regularized product;
* **`siegelIndefinite_qEx_uncond`**: the example $\langle1,1,1,-1\rangle$ over $\mathbb Q$ (`siegelIndefinite_qEx` without
  inputs).
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelComplex
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernaryIso
import QuadFormsKB.Tamagawa.Indefinite.OneClassExample
import QuadFormsKB.Tamagawa.InputsFollowup

open MeasureTheory Measure Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Frames LocalDensity

section NF

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **$\sum_iv(M_i)\ne0$ without inputs** ($n\ge3$, every number field, every signature): `tsum_unitVolume_ne_zero` with
$\tau(SO(V)) = 2$ proved (`tauTwoAll_release_uncond`). -/
theorem tsum_unitVolume_ne_zero_uncond {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    ∑' i, unitVolume Q₀ hQ i ≠ 0 :=
  tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond n hn Q₀ hQ)

/-- **$\sum_iv(M_i) < \infty$ without inputs** ($n\ge3$, every number field, every signature). -/
theorem tsum_unitVolume_ne_top_uncond {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    ∑' i, unitVolume Q₀ hQ i ≠ ⊤ :=
  tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond n hn Q₀ hQ)

/-- **The theta integral of an indefinite form, adelically, without inputs** (Weil 1982, §4.5, p. 109): for $F$ a number
field, $Q_0$ nondegenerate in $N = k+1\ge4$ variables (any signature), $m\in F^\times$, the constructed sphere data `S` of
$T(m)$, every fundamental domain $E$ of $SO(V)(F)$ in $SO(V)(\mathbb A)$ and every measurable $\Phi\ge0$ on $V_\infty$,
$$\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu = 2\int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}.$$
`lintegral_theta_adelic` with `AdelicSphereFibration` proved (`AdelicSphereSetup.sphereFibration`) and
$\tau(SO(Q')) = 2$ proved (`tauTwoAll_release_uncond`, $Q'$ in $k\ge3$ variables). -/
@[kb "weil1982" "§4.5, p. 109 (unfolding along T(ρ)); Lemma 2.4.1, Thm 2.4.3 [unverified page]"]
theorem lintegral_theta_adelic_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : F}
    (hm : m ≠ 0) (S : AdelicSphereSetup Q₀ m) {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ)
    {E : Set (SOAdele Q₀)} (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1) =
      2 * ∫⁻ x, testFn Φ x.1 ∂(S.sphereData hm hQ hk).σ := by
  rw [lintegral_theta_adelic Q₀ hQ (by omega) hm (S.sphereFibration hm hQ hk) hΦ hE]
  have h : covolume (GammaSOAdele S.C.Q') (SOAdele S.C.Q') (muTam S.C.Q' S.C.hQ' fun _ => 1) = 2 :=
    tauTwoAll_release_uncond k hk S.C.Q' S.C.hQ'
  rw [h]

/-- **Siegel's formula for indefinite forms, adelic form, without inputs** (Siegel–Weil; Weil 1982, §4.5, p. 109): for
$F$ a number field, $Q_0$ nondegenerate in $N = k+1\ge4$ variables (any signature), $m\in F^\times$ and the constructed
sphere data `S` of $T(m)$,
$$\frac1{\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A))}\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu
  = \int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}.$$
`siegelIndefinite_adelic` with its inputs `AdelicSphereFibration` and `TamagawaNumberTwoAdelic` (for $Q_0$ and $Q'$)
discharged. -/
@[kb "weil1982" "§4.5, p. 109 (Siegel's formula from τ(G) = τ(G'_ρ) = 2) [unverified page]"]
theorem siegelIndefinite_adelic_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : F}
    (hm : m ≠ 0) (S : AdelicSphereSetup Q₀ m) {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ)
    {E : Set (SOAdele Q₀)} (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    (∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1)) /
        covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) =
      ∫⁻ x, testFn Φ x.1 ∂(S.sphereData hm hQ hk).σ :=
  siegelIndefinite_adelic Q₀ hQ (by omega) hm (S.sphereFibration hm hQ hk)
    (tauTwoAll_release_uncond (k + 1) (by omega) Q₀ hQ) (tauTwoAll_release_uncond k hk S.C.Q' S.C.hQ') hΦ hE

/-- **The Siegel–Weil formula for indefinite forms with the local densities, without inputs** (Weil 1965, *Sur la
formule de Siegel*; Weil 1982, §4.5, p. 109; Siegel 1936): for $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$
in $N = k+1\ge4$ variables (any signature), $m\in\mathcal O_F$, $m\ne0$, with a rational point $\xi$ on $Q_0 = m$, every
fundamental domain $E$ of $SO(V)(F)$ in $SO(V)(\mathbb A)$ and every measurable $\Phi\ge0$ on $V_\infty$,
$$\frac1{\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A))}\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu
  = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\int_{T_\infty}\Phi\circ\tau_\infty\,d\sigma_\infty,$$
$L = \mathcal O_F^N$, $\beta_\mathfrak p$ = `NF.localDensity`, $\sigma_\infty$ = `sigInfNF` the Leray measure of
$\{Q = m\}\subseteq V_\infty$ (Weil's normalization at the complex places), $\tau_\infty$ = `τInfNF`. The covolume is $2$
(`tauTwoAll_release_uncond`). -/
@[kb "weil1965" "Sur la formule de Siegel: Siegel's formula for indefinite forms (mean value of theta = product of local densities) [unverified]"]
theorem siegelWeil_indefinite_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ)
    {E : Set (SOAdele Q₀)} (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    (∫⁻ g in E, thetaFn (ratA Q₀ (m : F)) (ratF Q₀ (m : F)) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1)) /
        covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∫⁻ x, Φ (τInfNF Q₀ (m : F) x) ∂sigInfNF Q₀ (m : F) := by
  obtain ⟨S⟩ := exists_adelicSphereSetup hQ hm ξ (by omega)
  rw [siegelIndefinite_adelic_uncond hQ hk hm S hΦ hE, (adelicSphereDensitiesNF Q₀ hQ hk S hm).lintegral_eq Φ hΦ]

/-- **Siegel's formula for indefinite forms over every number field, ratio form, without inputs** (Siegel 1936,
Hauptsatz for indefinite forms, measure of representations): under the hypotheses of `siegelIndefinite_uncond`
($F$ a number field, $Q_0$ nondegenerate in $N = k+1\ge4$ variables, any signature, $m\in\mathcal O_F\setminus0$ with a
rational point $\xi$ on $Q_0 = m$), $0 < \sum_iv(M_i) < \infty$ and
$$\frac{c_\infty(m)\sum_i\rho(M_i, m)}{\sum_iv(M_i)} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m).$$
`siegelIndefinite_classical_div` without its inputs, every number field. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; every number field) [unverified]"]
theorem siegelIndefinite_div_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    (cInfNF (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) i) /
        ∑' i, unitVolume Q₀ hQ i =
      ENNReal.ofReal (finDensityProduct Q₀ m) := by
  rw [siegelIndefinite_uncond hQ hk hm ξ, ENNReal.mul_div_cancel_right
    (tsum_unitVolume_ne_zero_uncond (by omega) Q₀ hQ) (tsum_unitVolume_ne_top_uncond (by omega) Q₀ hQ)]

/-- **One proper class in the genus, every number field, without inputs**: if
$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ is a single point, then for every proper class $M_0$ (the only one),
$$c_\infty(m)\,\rho(M_0, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot v(M_0),$$
under the hypotheses of `siegelIndefinite_uncond`. `siegelIndefinite_classical_totallyReal_of_subsingleton` without
its inputs and without "totally real". -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus; every number field) [unverified]"]
theorem siegelIndefinite_of_subsingleton_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} [Subsingleton (DC Q₀)]
    (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) (i₀ : DC Q₀) :
    cInfNF (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) i₀ =
      ENNReal.ofReal (finDensityProduct Q₀ m) * unitVolume Q₀ hQ i₀ := by
  have h := siegelIndefinite_uncond hQ hk hm ξ
  rwa [tsum_eq_single i₀ (fun j hj => absurd (Subsingleton.elim j i₀) hj),
    tsum_eq_single i₀ (fun j hj => absurd (Subsingleton.elim j i₀) hj)] at h

/-- **Siegel's formula for an indefinite form with one class in its genus, every number field, without inputs**
(Siegel 1936, Hauptsatz for indefinite forms; Eichler 1952): let $F$ be a number field (real and complex places
allowed) with $\mathcal O_F$ a principal ideal domain, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1\ge4$ variables,
$Q$ isotropic at every infinite place (`hinf`; automatic at the complex places), with `LocalSpinorUnits` at the primes
$\mathfrak p\mid2\det H$ (`hbad`), and $m\in\mathcal O_F\setminus0$ with a rational point $\xi$ on $Q_0 = m$. Then
$$c_\infty(m)\,\rho(L, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot v(L),$$
$L = \mathcal O_F^N$, $v(L)$ = `unitVolume` and $\rho(L, m)$ = `repMeasure` at the proper class `dcL` of $L$ (the only one,
`subsingleton_DC_of_bad`), $c_\infty(m)$ = `cInfNF`, stabilizer measures of `archFibrationNF`. Extends
`siegelIndefinite_oneClass_uncond` from totally real fields to every number field. The principal ideal domain
hypothesis is the one of `subsingleton_DC_of_bad` (Eichler's theorem in the form proved there: with a nontrivial class
group the genus can contain several spinor genera). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus; every number field) [unverified]"]
theorem siegelIndefinite_oneClass_uncondNF [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (k + 1))
    (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (k + 1)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) (dcL Q₀) =
      ENNReal.ofReal (finDensityProduct Q₀ m) * unitVolume Q₀ hQ (dcL Q₀) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  exact siegelIndefinite_of_subsingleton_uncond hQ hk hm ξ (dcL Q₀)

/-- **The ratio form, one class, every number field, without inputs**: under the hypotheses of
`siegelIndefinite_oneClass_uncondNF`, $0 < v(L) < \infty$ and
$$\frac{c_\infty(m)\,\rho(L, m)}{v(L)} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus; every number field) [unverified]"]
theorem siegelIndefinite_oneClass_div_uncondNF [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (k + 1))
    (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (k + 1)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    (cInfNF (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) (dcL Q₀)) /
        unitVolume Q₀ hQ (dcL Q₀) =
      ENNReal.ofReal (finDensityProduct Q₀ m) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  have hsum : ∑' i, unitVolume Q₀ hQ i = unitVolume Q₀ hQ (dcL Q₀) :=
    tsum_eq_single (dcL Q₀) fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj
  rw [siegelIndefinite_oneClass_uncondNF Q₀ hQ hk hinf hbad hm ξ, ENNReal.mul_div_cancel_right
    (hsum ▸ tsum_unitVolume_ne_zero_uncond (by omega) Q₀ hQ) (hsum ▸ tsum_unitVolume_ne_top_uncond (by omega) Q₀ hQ)]

end NF

/-! ### Ternary forms with one class in the genus -/

section Ternary

variable {F : Type} [Field F] [NumberField F]

/-- **Siegel's formula for numbers by a ternary form with one class in its genus, without inputs** (every number field
with $\mathcal O_F$ a principal ideal domain, $m^\perp$ anisotropic): under the hypotheses of `siegelIndefinite_ternary_uncond`
and those of `subsingleton_DC_of_bad` (`hinf`, `hbad`),
$$c_\infty(m)\,\rho(L, m) = |d_F|^{-1}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac{\chi(\mathfrak p)}{N\mathfrak p}\Bigr)\cdot v(L),$$
at the proper class `dcL` of $L = \mathcal O_F^3$, the only one in its genus. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (ternary forms, one class in the genus) [unverified]"]
theorem siegelIndefinite_ternary_oneClass_uncond [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (1 + 2))
    (hQ : Q₀.Nondegenerate)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (1 + 2)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (hW : ¬ IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := 2) (m : F) * repMeasureT Q₀ (DVR.unary m) hQ
        (frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
          ((ratFrameEquivRatSphere Q₀ m).symm ξ)) (dcL Q₀) =
      ENNReal.ofReal (ternaryDensityProductReg Q₀ m) * unitVolume Q₀ hQ (dcL Q₀) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  have h := siegelIndefinite_ternary_uncond Q₀ hQ hm hW ξ
  rwa [tsum_eq_single (dcL Q₀) (fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj),
    tsum_eq_single (dcL Q₀) (fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj)] at h

/-- **The ternary case with $m^\perp$ isotropic and one class in the genus, without inputs** (every number field with
$\mathcal O_F$ a principal ideal domain): under the hypotheses of `siegelIndefinite_ternary_isotropic_uncond` and those of
`subsingleton_DC_of_bad`,
$$2\,c_\infty(m)\,\rho^1(L, m) = |d_F|^{-1}\,\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac1{N\mathfrak p}\Bigr)\cdot v(L).$$ -/
@[kb "siegel1944" "On the theory of indefinite quadratic forms; ternary forms, m⊥ isotropic, one class in the genus [unverified]"]
theorem siegelIndefinite_ternary_isotropic_oneClass_uncond [IsPrincipalIdealRing (𝓞 F)]
    (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (1 + 2)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    2 * (cInfNF (k := 2) (m : F) * repMeasureIso Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
        (isSquare_deltaForms_unary hiso) ((ratFrameEquivRatSphere Q₀ m).symm ξ) (dcL Q₀)) =
      ENNReal.ofReal (ternaryIsoDensityProductReg Q₀ m) * unitVolume Q₀ hQ (dcL Q₀) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  have h := siegelIndefinite_ternary_isotropic_uncond Q₀ hQ hm hiso ξ
  rwa [tsum_eq_single (dcL Q₀) (fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj),
    tsum_eq_single (dcL Q₀) (fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj)] at h

end Ternary

/-! ### The example $\langle1,1,1,-1\rangle$ -/

/-- **Siegel's formula for $\langle1,1,1,-1\rangle$ without inputs** (Siegel 1936, Hauptsatz for indefinite forms, one class
in the genus): for $m\in\mathbb Z\setminus0$ with a rational point $\xi$ on $x_0^2+x_1^2+x_2^2-x_3^2 = m$,
$$\frac{c_\infty(m)\,\rho(L, m)}{v(L)} = \prod_p\beta_p(L, m)\qquad(|d_{\mathbb Q}| = 1).$$
`siegelIndefinite_qEx` with its inputs `AdelicSphereFibration`, `AdelicSphereDensities` and $\tau(SO(V)) = 2$
discharged (via `siegelIndefinite_oneClass_div_uncond`). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (example ⟨1,1,1,−1⟩) [unverified]"]
theorem siegelIndefinite_qEx_uncond {m : 𝓞 ℚ} (hm : (m : ℚ) ≠ 0) (ξ : RatSphere qEx (m : ℚ)) :
    (cInf (k := 3) (m : ℚ) *
        repMeasure qEx nondegenerate_qEx (m : ℚ) (totallyRealArchFibration qEx nondegenerate_qEx hm (by norm_num))
          (dcL qEx)) / unitVolume qEx nondegenerate_qEx (dcL qEx) =
      ENNReal.ofReal (∏' p : HeightOneSpectrum (𝓞 ℚ), NF.localDensity p qEx m) := by
  rw [siegelIndefinite_oneClass_div_uncond qEx nondegenerate_qEx le_rfl (fun w => isotropicIn_qE w.Completion)
    localSpinorUnits_qEx_bad hm ξ, finDensityProduct, Rat.numberField_discr]
  simp

end QuadFormsKB.Tamagawa.Indefinite
