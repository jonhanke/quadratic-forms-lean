/-
# Siegel's formula for indefinite forms: the adelic identity and the classical measure form

**Layer:** number fields; it combines the adelic unfolding
(`SphericalUnfoldAdelic.lean`) with the classical translation (`ClassicalMeasures.lean`).

Let $F$ be a number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $N = k + 1$ variables of any
signature, $V = F^N$, $L = \mathcal O_F^N$, $G = SO(V)$ with Weil's Tamagawa measure $\mu$ = `muTam Q₀ hQ 1`, and
$m\in F^\times$ represented by $Q$ over $F$. Let $\xi\in T(m)(F) = \{Q = m\}$, $H = SO(\xi^\perp)$ (a form $Q'$ in $k$
variables), and let `A : AdelicSphereData Q₀ m Q'` be adelic data for the sphere $T(m)$ satisfying Weil's fibration
`AdelicSphereFibration` (the named input): $\mu_G = \mathrm{coord}_*(\sigma_{\mathbb A}\otimes\mu_H)$, constant $1$.
For $\Phi\ge0$ measurable on $V_\infty$ put $\Phi\otimes1_{\hat L}$ = `testFn Φ` and
$$\theta(g) = \sum_{\eta\in T(m)(F)}\Phi(g_\infty^{-1}\eta)\,1_{\hat L}(g_f^{-1}\eta)\qquad(\texttt{thetaFn}).$$

**Proves**
* `thetaFn_eq_tsum`: $\theta(g) = \sum_\eta(\Phi\otimes1_{\hat L})(g^{-1}\eta)$ (the classical theta function is the
  adelic orbit sum).
* **`lintegral_theta_adelic`** (Weil 1982, §4.5, p. 109; given `AdelicSphereFibration`; no hypothesis on any covolume,
  identity in $[0,\infty]$): for every fundamental domain $E$ of $G(F)$ in $G(\mathbb A)$,
  $$\int_E\theta\,d\mu = \operatorname{covol}(H(F)\backslash H(\mathbb A))\cdot\int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}.$$
* **`siegelIndefinite_adelic`** (Siegel–Weil, adelic form): if moreover $\tau(G) = \tau(H) = 2$
  (`TamagawaNumberTwoAdelic` for $Q$ and $Q'$, hypotheses), the mean value of $\theta$ is
  $$\frac{1}{\operatorname{covol}(G(F)\backslash G(\mathbb A))}\int_E\theta\,d\mu = \int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}.$$
* `covolume_eq_muFin_mul_tsum_unitVolume`: $\operatorname{covol}(G(F)\backslash G(\mathbb A)) = \mu_f(SO(\hat L))\sum_iv(M_i)$.
* **`siegelIndefinite_classical`** (Siegel 1936, Hauptsatz, measure form; Weil 1965): with the archimedean fibration
  $\mathfrak F$ of $\mu_\infty$ (constant $c$, Leray measure $\sigma_\infty$ of the quadric $\{Q = m\}\subseteq V_\infty$), the
  input `AdelicSphereDensities` ($\sigma_{\mathbb A} = |d_F|^{-(N-1)/2}\,\sigma_\infty\otimes\prod_p\sigma_p$ on
  $\Phi\otimes1_{\hat L}$, with $\sigma_p(\hat L_p\cap T) = \beta_p(L, m)$) and $\tau(G) = \tau(H) = 2$:
  $$c\cdot\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_p\beta_p(L, m)\cdot\sum_iv(M_i),$$
  and `siegelIndefinite_classical_div`: when $0 < \sum_iv(M_i) < \infty$,
  $c\sum_i\rho(M_i,m)/\sum_iv(M_i) = |d_F|^{-(N-1)/2}\prod_p\beta_p(L, m)$. Here $c\cdot\rho(M_i, m)$ is Siegel's measure
  of representations for the quotient measure $\mu_\infty/\sigma_\infty$ on the stabilizers (`repMeasure` uses the
  stabilizer measures $\mu_{H_x}$ of $\mathfrak F$, for which $\mu_\infty = c\,\sigma_\infty\otimes\mu_{H_x}$). There is no
  $\beta_\infty$: the archimedean fibration absorbs it.
* `siegelIndefinite_classical_totallyReal`: the same for totally real $F$ with the constructed fibration
  (`totallyRealArchFibration`, $c = c_\infty(m)$, $\sigma_\infty = \bigotimes_w\sigma_{\sigma_w(m)}$).

**Status.** Conditional on the named inputs `AdelicSphereFibration` and `AdelicSphereDensities` (this file), and on
the hypotheses $\tau(G) = \tau(H) = 2$. For $N = 4$ and $Q_0 = \langle1,-a,-b,ab\rangle$ (`qSq a b`, the norm form of a
quaternion division algebra $D = (a,b)_F$) with $m = 1$, the complement is $\langle-a,-b,ab\rangle$ and
$\tau(H) = 2$ is proved unconditionally (`tamagawaNumberTwoAdelic_pureForm`, every number field, every signature);
$\tau(G) = 2$ is `tamagawaNumberTwoAdelic_qSq`, conditional on `GnatTamagawaComparison` (`SiegelIndefiniteExamples.lean`).
-/
import QuadFormsKB.Tamagawa.Indefinite.ClassicalMeasures
import QuadFormsKB.Tamagawa.Measure.Weil.SphericalUnfoldAdelic
import QuadFormsKB.LocalDensity.NFLocal

open MeasureTheory Measure MulAction Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-! ### The test function $\Phi\otimes1_{\hat L}$ -/

section TestFn

variable {n : ℕ}

theorem continuous_archVec : Continuous (archVec : AdeleSpace F (Fin n) → VInf F n) :=
  Continuous.prodMk (continuous_pi fun w => continuous_pi fun j =>
      (continuous_apply w).comp (continuous_fst.comp (continuous_fst.comp (continuous_apply j))))
    (continuous_pi fun w => continuous_pi fun j =>
      (continuous_apply w).comp (continuous_snd.comp (continuous_fst.comp (continuous_apply j))))

theorem continuous_finVec : Continuous (finVec : AdeleSpace F (Fin n) → (Fin n → FiniteAdeleRing (𝓞 F) F)) :=
  continuous_pi fun j => continuous_snd.comp (continuous_apply j)

/-- $\hat L = \prod_v\mathfrak o_v^n$ is open in $\mathbb A_f^n$. -/
theorem isOpen_latHat : IsOpen (latHat F n) := by
  have h : latHat F n = ⋂ j : Fin n, (fun z : Fin n → FiniteAdeleRing (𝓞 F) F => z j) ⁻¹'
      {y : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F} := by
    ext z; simp [latHat]
  rw [h]
  exact isOpen_iInter_of_finite fun j =>
    (RestrictedProduct.isOpen_forall_mem (fun v => isOpen_adicCompletionIntegers v)).preimage (continuous_apply j)

/-- **The adelic test function** $\Phi\otimes1_{\hat L}$: $y\mapsto\Phi(y_\infty)\,1_{\hat L}(y_f)$ on $\mathbb A_F^n$, for
$\Phi : V_\infty\to[0,\infty]$. -/
def testFn (Φ : VInf F n → ℝ≥0∞) (y : AdeleSpace F (Fin n)) : ℝ≥0∞ :=
  Φ (archVec y) * (latHat F n).indicator 1 (finVec y)

theorem measurable_testFn {Φ : VInf F n → ℝ≥0∞} (hΦ : Measurable Φ) : Measurable (testFn (F := F) Φ) :=
  (hΦ.comp continuous_archVec.measurable).mul
    ((measurable_one.indicator isOpen_latHat.measurableSet).comp continuous_finVec.measurable)

variable (Q₀ : QuadForm (𝓞 F) n)

/-- **The theta function is the orbit sum**: $\theta(g) = \sum_{\eta\in T(m)(F)}(\Phi\otimes1_{\hat L})(g^{-1}\eta)$. -/
theorem thetaFn_eq_tsum (m : F) (Φ : VInf F n → ℝ≥0∞) (g : SOAdele Q₀) :
    thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F n) g =
      ∑' η : RatSphere Q₀ m, testFn Φ (g⁻¹ • diagVec F (Fin n) η.1) :=
  rfl

end TestFn

/-! ### The adelic identity -/

section Adelic

variable {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)

/-- **The theta integral of an indefinite form, adelically** (Weil 1982, §4.5, p. 109, unfolding along $T(m)$; Siegel
1936): given Weil's adelic fibration over the sphere $T(m)$ (`AdelicSphereFibration`, input), for every fundamental
domain $E$ of $SO(V)(F)$ in $SO(V)(\mathbb A)$ and every measurable $\Phi\ge0$ on $V_\infty$,
$$\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu = \operatorname{covol}(H(F)\backslash H(\mathbb A))\cdot
  \int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}$$
in $[0,\infty]$, with $H = SO(Q')$ the stabilizer of the base point. No hypothesis on any covolume. -/
@[kb "weil1982" "§4.5, p. 109 (unfolding along T(ρ)); Lemma 2.4.1, Thm 2.4.3 [unverified page]"]
theorem lintegral_theta_adelic (hk : 1 ≤ k) {m : F} (hm : m ≠ 0) {Q' : QuadForm (𝓞 F) k}
    {hQ' : Q'.Nondegenerate} {A : AdelicSphereData Q₀ m Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1) =
      covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' fun _ => 1) * ∫⁻ x, testFn Φ x.1 ∂A.σ := by
  simp_rw [thetaFn_eq_tsum]
  exact hA.lintegral_unfold hm hk hE (measurable_testFn hΦ)

/-- **Siegel's formula for indefinite forms, adelic form** (Siegel–Weil; Weil 1982, §4.5, p. 109; Weil 1965): given
Weil's adelic fibration over $T(m)$ (`AdelicSphereFibration`, input) and **the Tamagawa numbers
$\tau(SO(V)) = \tau(SO(Q')) = 2$** (`TamagawaNumberTwoAdelic` for $Q$ and $Q'$, hypotheses), the mean value of the theta
function over $SO(V)(F)\backslash SO(V)(\mathbb A)$ is the integral of the test function over the adelic sphere:
$$\frac1{\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A))}\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu
  = \int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}.$$ -/
@[kb "weil1982" "§4.5, p. 109 (Siegel's formula from τ(G) = τ(G'_ρ) = 2) [unverified page]"]
theorem siegelIndefinite_adelic (hk : 1 ≤ k) {m : F} (hm : m ≠ 0) {Q' : QuadForm (𝓞 F) k}
    {hQ' : Q'.Nondegenerate} {A : AdelicSphereData Q₀ m Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ')
    {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    (∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1)) /
        covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) =
      ∫⁻ x, testFn Φ x.1 ∂A.σ := by
  rw [lintegral_theta_adelic Q₀ hQ hk hm hA hΦ hE]
  have h1 : covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' fun _ => 1) = 2 := hτ'
  have h2 : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := hτ
  rw [h1, h2, mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

end Adelic

/-! ### The local densities (input) -/

section Densities

variable {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1))

/-- **The local side of the classical formula**:
$$|d_F|^{-(N-1)/2}\prod_{\mathfrak p}\beta_{\mathfrak p}(L, m),\qquad N = k + 1,$$
$\beta_\mathfrak p$ = `NF.localDensity` (Haar measures with $\operatorname{vol}(\mathfrak o_\mathfrak p) = 1$), the product over
the finite primes of $F$ (`tprod`). The discriminant factor is the ratio $c_F(SO_N)/c_F(SO_{N-1})$ of the
normalizing constants of Weil's Tamagawa measures (`cF`). *Warning:* meaningful for $N\ge4$ (absolute convergence);
for $N = 3$ `tprod` may return its junk value (see `siegelProduct`). -/
@[kb "weil1965" "Sur la formule de Siegel; local densities and the factor |d_F|^{-(N-1)/2} [unverified]"]
def finDensityProduct (m : 𝓞 F) : ℝ :=
  |(discr F : ℝ)| ^ (-((k + 1 : ℕ) - 1 : ℝ) / 2) * ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.localDensity v Q₀ m

/-- **Input: the adelic sphere measure is the product of the archimedean Leray measure and the local densities**
(Weil 1965, *Sur la formule de Siegel*, §§ on the Tamagawa measure of $G/H$ [unverified]; Weil 1982, Lemma 2.4.1,
Thm 2.4.3 [unverified page]). For adelic sphere data `A` for $T(m)$,
$m\in\mathcal O_F$, a measure $\sigma_\infty$ on a space $T_\infty$ and a parametrization $\tau_\infty : T_\infty\to V_\infty$
of the archimedean quadric $\{Q = m\}$:
* `lintegral_eq`: for every measurable $\Phi\ge0$ on $V_\infty$,
  $$\int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot
    \int_{T_\infty}\Phi\circ\tau_\infty\,d\sigma_\infty.$$

It is meant for $\sigma_\infty$ the **product of the Leray measures** $dx/dQ$ at the archimedean places, without
constants (at a real place `SphereLeray.sig`; see `sigInf`). Why it holds there: `AdelicSphereFibration.fib` determines
$\sigma_{\mathbb A}$ (as $\mu_G/\mu_H$), and the local fibration identities give
$\sigma_{\mathbb A} = \frac{c_F(SO_N)}{c_F(SO_{N-1})}\prod_v|2m|_v^{-(N-1)}\bigotimes_v\sigma^{\mathrm{Leray}}_v$, where
$c_F(SO_N)/c_F(SO_{N-1}) = |d_F|^{-(N-1)/2}$, $\prod_v|2m|_v = 1$ (product formula) and
$\sigma^{\mathrm{Leray}}_\mathfrak p(\hat L_\mathfrak p\cap T) = \beta_\mathfrak p(L, m)$. It says nothing about any covolume, Tamagawa
number or representation measure: it is a statement about one measure on the adelic sphere, so it is not equivalent
to the conclusion of `siegelIndefinite_classical`. Discharging it includes checking that the finite local measures
behind `muFin` (`muLocSO`) and the archimedean ones behind `muArchTamSO` (Weil's normalization at complex places,
`cxWeil`) are the gauge measures for which the local Leray measures give exactly $\beta_\mathfrak p$ and
$\sigma_\infty$. *Warning:* for $N = 3$ the product is not absolutely convergent and `finDensityProduct` may be a junk
value; use for $N\ge4$. Field: `lintegral_eq`. -/
@[kb "weil1965" "Sur la formule de Siegel: Tamagawa measure of the sphere = ∏ local densities [unverified]"]
structure AdelicSphereDensities {m : 𝓞 F} {Q' : QuadForm (𝓞 F) k} (A : AdelicSphereData Q₀ (m : F) Q')
    {T : Type*} [MeasurableSpace T] (σ : Measure T) (τ : T → VInf F (k + 1)) : Prop where
  /-- The integral of $\Phi\otimes1_{\hat L}$ over the adelic sphere. -/
  lintegral_eq : ∀ Φ : VInf F (k + 1) → ℝ≥0∞, Measurable Φ →
    ∫⁻ x, testFn Φ x.1 ∂A.σ = ENNReal.ofReal (finDensityProduct Q₀ m) * ∫⁻ x, Φ (τ x) ∂σ

end Densities

/-! ### The classical measure form -/

section Classical

variable {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)

/-- **The β-decomposition of the covolume** (any signature; `covolume_eq_measure_mul_tsum_covolume`):
$$\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A)) = \mu_f(SO(\hat L))\cdot\sum_iv(M_i).$$ -/
theorem covolume_eq_muFin_mul_tsum_unitVolume {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) =
      muFin Q₀ (fun _ => 1) (KSO Q₀) * ∑' i, unitVolume Q₀ hQ i := by
  have := countable_GammaSOAdele Q₀
  haveI := fun i => countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  haveI := fun i => smulInvariantMeasure_subgroup (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
    (muArchTamSO Q₀ hQ)
  haveI := fun i => measurableConstSMul_subgroup (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
  exact covolume_eq_measure_mul_tsum_covolume (GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet
    (dcRep Q₀) (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFin Q₀ fun _ => 1)


/-- $\sum_iv(M_i)\ne0$ when $\tau(SO(V)) = 2$ ($\mu_f(SO(\hat L)) < \infty$). -/
theorem tsum_unitVolume_ne_zero {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) : ∑' i, unitVolume Q₀ hQ i ≠ 0 := by
  intro h0
  have h := covolume_eq_muFin_mul_tsum_unitVolume Q₀ hQ
  rw [h0, mul_zero] at h
  have h2 : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := hτ
  rw [h2] at h
  exact two_ne_zero h

/-- $\sum_iv(M_i) < \infty$ when $\tau(SO(V)) = 2$: the covolume $\mu_f(SO(\hat L))\sum_iv(M_i) = 2$ forces
$\mu_f(SO(\hat L))\ne0$, hence $\sum_iv(M_i)\ne\infty$. -/
theorem tsum_unitVolume_ne_top {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) : ∑' i, unitVolume Q₀ hQ i ≠ ⊤ := by
  have h := covolume_eq_muFin_mul_tsum_unitVolume Q₀ hQ
  have h2 : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := hτ
  rw [h2] at h
  have hK : muFin Q₀ (fun _ => 1) (KSO Q₀) ≠ 0 := by
    intro hK
    rw [hK, zero_mul] at h
    exact two_ne_zero h
  intro htop
  rw [htop, ENNReal.mul_top hK] at h
  exact ENNReal.ofNat_ne_top h


variable {T : Type*} [MeasurableSpace T] {P : Set (VInf F (k + 1))} {σ : Measure T} {τ : T → VInf F (k + 1)}
  {c : ℝ≥0∞}

/-- **Siegel's formula for indefinite forms, classical measure form** (Siegel 1936, Hauptsatz for indefinite forms,
measure of representations; Weil 1965). Let `𝔉` be an archimedean fibration of $\mu_\infty$ over the quadric
$\{Q = m\}\subseteq V_\infty$ (constant $c$, measure $\sigma_\infty$ on $T_\infty$, parametrization $\tau_\infty$), `A`
adelic sphere data for $T(m)$ with Weil's fibration (`AdelicSphereFibration`, input) and the local-density identity
(`AdelicSphereDensities`, input), and assume **$\tau(SO(V)) = \tau(SO(Q')) = 2$** (hypotheses). If some measurable
$\Phi\ge0$ has $0 < \int\Phi\circ\tau_\infty\,d\sigma_\infty < \infty$ (the archimedean quadric has positive measure), then
$$c\cdot\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^N$, $v(M_i)$ = `unitVolume`,
$\rho(M_i, m)$ = `repMeasure` (with the stabilizer measures of `𝔉`). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form) [unverified]"]
theorem siegelIndefinite_classical (hk : 1 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) [SFinite σ]
    (𝔉 : ArchFibration (muArchTamSO Q₀ hQ) P σ τ c) (hP : ∀ η : RatSphere Q₀ (m : F), ratA Q₀ (m : F) η ∈ P)
    {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate} {A : AdelicSphereData Q₀ (m : F) Q'}
    (hA : AdelicSphereFibration Q₀ hQ hQ' A) (hβ : AdelicSphereDensities Q₀ A σ τ)
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ')
    (Φ : VInf F (k + 1) → ℝ≥0∞) (hΦ : Measurable Φ) (hΦτ : Measurable fun x => Φ (τ x))
    (hI0 : ∫⁻ x, Φ (τ x) ∂σ ≠ 0) (hItop : ∫⁻ x, Φ (τ x) ∂σ ≠ ⊤) :
    c * ∑' i, repMeasure Q₀ hQ (m : F) 𝔉 i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  have := countable_GammaSOAdele Q₀
  have := discreteTopology_GammaSOAdele Q₀
  obtain ⟨E, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q₀)
  have hEf : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1) :=
    IsFundamentalDomain.mk' hE.1.nullMeasurableSet hE.2
  have h1 := lintegral_theta_mul_tsum_unitVolume Q₀ hQ (m : F) 𝔉 hP Φ hΦ hΦτ hEf
  rw [lintegral_theta_adelic Q₀ hQ hk hm hA hΦ hEf, hβ.lintegral_eq Φ hΦ] at h1
  have hG : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := hτ
  have hH : covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' fun _ => 1) = 2 := hτ'
  rw [hG, hH] at h1
  set I := ∫⁻ x, Φ (τ x) ∂σ
  set X := ENNReal.ofReal (finDensityProduct Q₀ m)
  have h2 : (2 * I) * (X * ∑' i, unitVolume Q₀ hQ i) = (2 * I) * (c * ∑' i, repMeasure Q₀ hQ (m : F) 𝔉 i) := by
    calc (2 * I) * (X * ∑' i, unitVolume Q₀ hQ i) = 2 * (X * I) * ∑' i, unitVolume Q₀ hQ i := by ring
      _ = 2 * c * (∑' i, repMeasure Q₀ hQ (m : F) 𝔉 i) * I := h1
      _ = (2 * I) * (c * ∑' i, repMeasure Q₀ hQ (m : F) 𝔉 i) := by ring
  exact ((ENNReal.mul_right_inj (mul_ne_zero two_ne_zero hI0)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hItop)).mp h2).symm

/-- **Siegel's formula for indefinite forms, as a ratio** (Siegel 1936):
$$\frac{c\sum_i\rho(M_i, m)}{\sum_iv(M_i)} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m),$$
under the hypotheses of `siegelIndefinite_classical`. Since $\operatorname{covol} = \mu_f(SO(\hat L))\sum_iv(M_i) = 2$
(`covolume_eq_muFin_mul_tsum_unitVolume`), $0 < \sum_iv(M_i) < \infty$ holds automatically (`tsum_unitVolume_ne_zero`,
`tsum_unitVolume_ne_top`). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form) [unverified]"]
theorem siegelIndefinite_classical_div (hk : 1 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) [SFinite σ]
    (𝔉 : ArchFibration (muArchTamSO Q₀ hQ) P σ τ c) (hP : ∀ η : RatSphere Q₀ (m : F), ratA Q₀ (m : F) η ∈ P)
    {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate} {A : AdelicSphereData Q₀ (m : F) Q'}
    (hA : AdelicSphereFibration Q₀ hQ hQ' A) (hβ : AdelicSphereDensities Q₀ A σ τ)
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ')
    (Φ : VInf F (k + 1) → ℝ≥0∞) (hΦ : Measurable Φ) (hΦτ : Measurable fun x => Φ (τ x))
    (hI0 : ∫⁻ x, Φ (τ x) ∂σ ≠ 0) (hItop : ∫⁻ x, Φ (τ x) ∂σ ≠ ⊤) :
    (c * ∑' i, repMeasure Q₀ hQ (m : F) 𝔉 i) / ∑' i, unitVolume Q₀ hQ i =
      ENNReal.ofReal (finDensityProduct Q₀ m) := by
  rw [siegelIndefinite_classical Q₀ hQ hk hm 𝔉 hP hA hβ hτ hτ' Φ hΦ hΦτ hI0 hItop,
    ENNReal.mul_div_cancel_right (tsum_unitVolume_ne_zero Q₀ hQ hτ) (tsum_unitVolume_ne_top Q₀ hQ hτ)]

end Classical

/-! ### Totally real fields: the constructed fibration -/

section TotallyReal

open QuadFormsKB.Tamagawa.Measure.SphereLeray NumberField.InfinitePlace
open scoped Classical

/-- **A nonempty level set has nonzero Leray measure**: if $Q(y) = c\ne0$ for some $y\in\mathbb R^n$, $n\ge1$, then
$\sigma_c\ne0$. (Otherwise the cone $\{cQ > 0\} = \bigcup_a\{e^tx : t\le a,\ x\in S_c\}$, a nonempty open set, would be
Lebesgue null.) -/
theorem sig_ne_zero {n : ℕ} {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (hn : 1 ≤ n) {y : Fin n → ℝ}
    (hy : Q.eval y = c) : sig Q c ≠ 0 := by
  intro h0
  have h1 : nu Q c univ = 0 := by
    have h : sig Q c univ = 0 := by rw [h0]; rfl
    rw [sig, Measure.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left
      (ENNReal.ofReal_pos.mpr (div_pos one_pos (mul_pos two_pos (abs_pos.mpr hc)))).ne'
  rw [nu_apply hc MeasurableSet.univ] at h1
  have h2 : volume (pol Q c '' (Iic 0 ×ˢ univ)) = 0 :=
    (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  have h3 : posSet Q c ⊆ ⋃ a : ℕ, pol Q c '' (Iic (a : ℝ) ×ˢ univ) := by
    rw [← range_pol hc]
    rintro _ ⟨⟨t, x⟩, rfl⟩
    obtain ⟨a, ha⟩ := exists_nat_ge t
    exact mem_iUnion.mpr ⟨a, ⟨(t, x), ⟨ha, mem_univ _⟩, rfl⟩⟩
  have h4 : volume (posSet Q c) = 0 := measure_mono_null h3 (measure_iUnion_null fun a => by
    rw [volume_image_pol_Iic, h2, mul_zero])
  have h5 : (posSet Q c).Nonempty := ⟨y, by show 0 < c * Q.eval y; rw [hy]; exact mul_self_pos.mpr hc⟩
  exact (isOpen_posSet Q c).measure_ne_zero volume h5 h4

variable {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)

/-- **The archimedean Leray measure of the quadric is nonzero** when $Q = m$ has a solution over $F$ (totally real
$F$). -/
theorem sigInf_ne_zero [IsEmpty {w : InfinitePlace F // w.IsComplex}] {m : F} (hm : m ≠ 0) (η : RatSphere Q₀ m) :
    sigInf Q₀ m ≠ 0 := by
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  intro h0
  have h1 : sigInf Q₀ m (univ ×ˢ univ) = 0 := by rw [h0]; rfl
  rw [sigInf, Measure.prod_prod, Measure.pi_univ, Measure.pi_univ,
    Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty,
    mul_one, Finset.prod_eq_zero_iff] at h1
  obtain ⟨w, -, hw⟩ := h1
  exact sig_ne_zero (mR_ne_zero hm w) (by omega) ((ratA_mem_quadricInf Q₀ m η).1 w (mem_univ w))
    (Measure.measure_univ_eq_zero.mp hw)

/-- **A test function with $0 < \int\Phi\,d\sigma_\infty < \infty$** (totally real $F$, $Q = m$ solvable over $F$):
the indicator of a large bounded piece of the archimedean quadric. -/
theorem exists_testFn_totallyReal [IsEmpty {w : InfinitePlace F // w.IsComplex}] {m : F} (hm : m ≠ 0)
    (η : RatSphere Q₀ m) :
    ∃ Φ : VInf F (k + 1) → ℝ≥0∞, Measurable Φ ∧ ∫⁻ x, Φ (τInf Q₀ m x) ∂sigInf Q₀ m ≠ 0 ∧
      ∫⁻ x, Φ (τInf Q₀ m x) ∂sigInf Q₀ m ≠ ⊤ := by
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  let S : ℕ → Set (VInf F (k + 1)) := fun R => {x | ∀ w, ‖x.1 w‖ ≤ R}
  have hS : ∀ R, MeasurableSet (S R) := fun R => by
    simp only [S, ofPred_forall]
    exact MeasurableSet.iInter fun w => measurableSet_le
      (continuous_norm.comp ((continuous_apply w).comp continuous_fst)).measurable measurable_const
  have hpre : ∀ R, τInf Q₀ m ⁻¹' S R =
      (univ.pi fun w => {y : Sph (QRe Q₀ w) (mR m w) | ‖(y : Fin (k + 1) → ℝ)‖ ≤ R}) ×ˢ univ := by
    intro R; ext t; simp [S, τInf]
  have hfin : ∀ R, sigInf Q₀ m (τInf Q₀ m ⁻¹' S R) ≠ ⊤ := by
    intro R
    rw [hpre, sigInf, Measure.prod_prod, Measure.pi_pi, Measure.pi_univ]
    refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => ?_)
      (ENNReal.prod_ne_top fun j _ => isEmptyElim j)
    rw [sig, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nu_bounded_lt_top (mR_ne_zero hm w) R).ne
  have hcov : ⋃ R : ℕ, τInf Q₀ m ⁻¹' S R = univ := by
    refine eq_univ_of_forall fun t => mem_iUnion.mpr ?_
    obtain ⟨R, hR⟩ := exists_nat_ge (∑ w, ‖(τInf Q₀ m t).1 w‖)
    exact ⟨R, fun w => (Finset.single_le_sum (fun w _ => norm_nonneg ((τInf Q₀ m t).1 w))
      (Finset.mem_univ w)).trans hR⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, sigInf Q₀ m (τInf Q₀ m ⁻¹' S R) ≠ 0 := by
    by_contra h
    push_neg at h
    apply sigInf_ne_zero Q₀ hm η
    rw [← Measure.measure_univ_eq_zero, ← hcov]
    exact measure_iUnion_null h
  have hI : ∫⁻ x, (S R).indicator 1 (τInf Q₀ m x) ∂sigInf Q₀ m = sigInf Q₀ m (τInf Q₀ m ⁻¹' S R) := by
    rw [← lintegral_indicator_one ((measurable_τInf Q₀ m) (hS R))]
    rfl
  exact ⟨(S R).indicator 1, measurable_one.indicator (hS R), hI ▸ hR, hI ▸ hfin R⟩

/-- **Siegel's formula for indefinite forms over a totally real field, classical measure form**: with the constructed
archimedean fibration (`totallyRealArchFibration`, $c_\infty(m) = c_F\prod_w|2\sigma_w(m)|^{-(N-1)}$,
$\sigma_\infty = \bigotimes_w\sigma_{\sigma_w(m)}$), for $m\in\mathcal O_F\setminus0$ with $Q = m$ solvable over $F$ (the
base point of `A`), given the inputs `AdelicSphereFibration`, `AdelicSphereDensities` and $\tau(SO(V)) = \tau(SO(Q')) = 2$:
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_classical_totallyReal [IsEmpty {w : InfinitePlace F // w.IsComplex}] (hk : 1 ≤ k)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ (m : F) Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    (hβ : AdelicSphereDensities Q₀ A (sigInf Q₀ (m : F)) (τInf Q₀ (m : F)))
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ') :
    cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm hk) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  have := sigmaFinite_sigInf Q₀ hm
  obtain ⟨Φ, hΦ, h0, htop⟩ := exists_testFn_totallyReal Q₀ hm A.ξ
  exact siegelIndefinite_classical Q₀ hQ hk hm (totallyRealArchFibration Q₀ hQ hm hk) (ratA_mem_quadricInf Q₀ _)
    hA hβ hτ hτ' Φ hΦ (hΦ.comp (measurable_τInf Q₀ _)) h0 htop

/-- **The ratio form over a totally real field**:
$c_\infty(m)\sum_i\rho(M_i, m)/\sum_iv(M_i) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)$. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_classical_div_totallyReal [IsEmpty {w : InfinitePlace F // w.IsComplex}] (hk : 1 ≤ k)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ (m : F) Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    (hβ : AdelicSphereDensities Q₀ A (sigInf Q₀ (m : F)) (τInf Q₀ (m : F)))
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ') :
    (cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm hk) i) /
        ∑' i, unitVolume Q₀ hQ i =
      ENNReal.ofReal (finDensityProduct Q₀ m) := by
  rw [siegelIndefinite_classical_totallyReal Q₀ hQ hk hm hA hβ hτ hτ',
    ENNReal.mul_div_cancel_right (tsum_unitVolume_ne_zero Q₀ hQ hτ) (tsum_unitVolume_ne_top Q₀ hQ hτ)]

/-- **One proper class in the genus**: if $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ is a single
point (for indefinite $L$ this is what Eichler's theorem gives when the genus is one proper spinor genus), the sums
reduce to the class $M_0$ of $L$:
$$c_\infty(m)\,\rho(M_0, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot v(M_0),$$
under the hypotheses of `siegelIndefinite_classical_totallyReal`. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus) [unverified]"]
theorem siegelIndefinite_classical_totallyReal_of_subsingleton [IsEmpty {w : InfinitePlace F // w.IsComplex}]
    [Subsingleton (DC Q₀)] (hk : 1 ≤ k)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ (m : F) Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    (hβ : AdelicSphereDensities Q₀ A (sigInf Q₀ (m : F)) (τInf Q₀ (m : F)))
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ') (i₀ : DC Q₀) :
    cInf (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm hk) i₀ =
      ENNReal.ofReal (finDensityProduct Q₀ m) * unitVolume Q₀ hQ i₀ := by
  have h := siegelIndefinite_classical_totallyReal Q₀ hQ hk hm hA hβ hτ hτ'
  rwa [tsum_eq_single i₀ (fun j hj => absurd (Subsingleton.elim j i₀) hj),
    tsum_eq_single i₀ (fun j hj => absurd (Subsingleton.elim j i₀) hj)] at h

end TotallyReal

end QuadFormsKB.Tamagawa.Indefinite
