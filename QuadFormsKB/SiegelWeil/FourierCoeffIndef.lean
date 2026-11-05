/-
# The Fourier coefficients of the theta integral of an indefinite form, place by place
**Layer:** global, $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1\ge4$ variables, any
signature; $V_\infty = \prod_{w\ \mathrm{real}}\mathbb R^N\times\prod_{w\ \mathrm{complex}}\mathbb C^N$.

The $m$-th orbit piece $I_m(\Phi)$ of the theta integral (`ThetaIntegralIndef.thetaMean`, the mean value of the theta
function of the quadric $\{Q = m\}$) is, by the library's indefinite Siegel formula, the product of the local densities and
the archimedean orbital integral. For a **product test function** $\Phi = \bigotimes_w\Phi_w$ the archimedean factor
splits over the infinite places, and at each place it is the local Whittaker integral (`OrbitalReal`, `OrbitalComplex`). This is the
Siegel–Weil formula in **Fourier-coefficient form** (Weil 1965, *Sur la formule de Siegel*, §§ 8–10 [unverified];
Kudla, *Some extensions of the Siegel–Weil formula*, §1 [unverified]): the $m$-th coefficient of the theta integral is
$\prod_vW_v(m)$, the $m$-th coefficient of the Eisenstein series.

**Proves**
* `lintegral_sigInfNF_prodFn`: $\int_{T_\infty}\bigotimes_w\Phi_w\,d\sigma_\infty = \prod_{w\ \mathrm{real}}\rho_{\Phi_w}(\sigma_w(m))
  \cdot\prod_{w\ \mathrm{complex}}2^{N-1}\int_{\{Q = \sigma_w(m)\}}\Phi_w\,d\sigma$.
* **`thetaMean_prodFn`**: for $m\in\mathcal O_F\setminus0$ with a rational point on $\{Q = m\}$,
  $$I_m\Big(\bigotimes_w\Phi_w\Big) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot
    \prod_{w\ \mathrm{real}}\rho_{\Phi_w}(\sigma_w(m))\cdot\prod_{w\ \mathrm{complex}}2^{N-1}\int\Phi_w\,d\sigma.$$
* **`thetaMean_gauss`** (every number field, $Q_0 = \sum_ia_ix_i^2$, $\Phi_w$ the Gaussian of the majorant
  $e^{-\pi\sum_i|\sigma_w(a_i)|x_i^2}$ at every real place and $e^{-2\pi\sum_i|\sigma_w(a_i)||x_i|^2}$ at every complex place):
  $I_m(\Phi) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\prod_{w\ \mathrm{real}}\rho_w(\sigma_w(m))
  \prod_{w\ \mathrm{complex}}2^{N-1}\rho_w(\sigma_w(m))$, and **`whittakerInf_eq_orbR`**, **`whittakerInfC_eq_orbCR`**: each
  $\rho_w(\sigma_w(m))$ is (resp. $4\times$) the absolutely convergent archimedean Whittaker integral
  $\int_{F_w}\big(\int_{F_w^N}\Phi_w(x)\psi_w(bQ_w(x))\,dx\big)\psi_w(-\sigma_w(m)b)\,db$ (Lebesgue measures).
* **`thetaMean_gauss_eq_whittaker`** (every number field, $N$ even):
  $I_t(\Phi) = \gamma_{V,\infty}c_{B,\infty}\prod_{v<\infty}W_v(t)\prod_{w\ \mathrm{real}}W_w(\sigma_w(t))\prod_{w\ \mathrm{complex}}2^{N+1}W_w(\sigma_w(t))$
  with the finite Whittaker integrals `whittakerV` (convergent product): the Fourier-coefficient form of Siegel–Weil
  ($2^{N+1}W_w$ is the complex Whittaker integral for the self-dual measures).
-/
import QuadFormsKB.SiegelWeil.ThetaIntegralIndef
import QuadFormsKB.SiegelWeil.OrbitalReal
import QuadFormsKB.SiegelWeil.OrbitalComplex
import QuadFormsKB.Tamagawa.Measure.PiProdLintegral
import QuadFormsKB.SiegelWeil.GlobalWhittaker

open MeasureTheory Measure Set NumberField IsDedekindDomain Complex
open scoped ENNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.SiegelWeil.Indefinite

open QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Tamagawa.Measure.SphereLerayC

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **A product test function on $V_\infty$**: $\Phi(x) = \prod_{w\ \mathrm{real}}\Phi_w(x_w)\cdot\prod_{w\ \mathrm{complex}}\Phi_w(x_w)$.
Parameters: `Φr` (one function on $\mathbb R^N$ per real place), `Φc` (one function on $\mathbb C^N$ per complex place). -/
def prodFn (Φr : ∀ _w : {w : InfinitePlace F // w.IsReal}, (Fin (k + 1) → ℝ) → ℝ≥0∞)
    (Φc : ∀ _w : {w : InfinitePlace F // w.IsComplex}, (Fin (k + 1) → ℂ) → ℝ≥0∞) (x : VInf F (k + 1)) : ℝ≥0∞ :=
  (∏ w, Φr w (x.1 w)) * ∏ w, Φc w (x.2 w)

variable {Φr : ∀ _w : {w : InfinitePlace F // w.IsReal}, (Fin (k + 1) → ℝ) → ℝ≥0∞}
  {Φc : ∀ _w : {w : InfinitePlace F // w.IsComplex}, (Fin (k + 1) → ℂ) → ℝ≥0∞}

theorem measurable_prodFn (hr : ∀ w, Measurable (Φr w)) (hc : ∀ w, Measurable (Φc w)) :
    Measurable (prodFn Φr Φc) :=
  (Finset.measurable_prod _ fun w _ => (hr w).comp ((measurable_pi_apply w).comp measurable_fst)).mul
    (Finset.measurable_prod _ fun w _ => (hc w).comp ((measurable_pi_apply w).comp measurable_snd))

variable (Q₀ : QuadForm (𝓞 F) (k + 1))

/-- **The archimedean orbital integral of a product test function is a product over the places**:
$$\int_{T_\infty}\Phi\circ\tau_\infty\,d\sigma_\infty = \prod_{w\ \mathrm{real}}\rho_{\Phi_w}(\sigma_w(m))\cdot
  \prod_{w\ \mathrm{complex}}2^{N-1}\int_{\{Q = \sigma_w(m)\}}\Phi_w\,d\sigma,$$
$\rho$ = `Orbital.orbI` (the Leray orbital integral at a real place). -/
theorem lintegral_sigInfNF_prodFn {m : F} (hm : m ≠ 0) (hr : ∀ w, Measurable (Φr w)) (hc : ∀ w, Measurable (Φc w)) :
    ∫⁻ x, prodFn Φr Φc (τInfNF Q₀ m x) ∂sigInfNF Q₀ m =
      (∏ w, Orbital.orbI (QRe Q₀ w) (Φr w) (σR w m)) *
        ∏ w, (2 : ℝ≥0∞) ^ k * ∫⁻ y, Φc w y ∂sigC (QCx Q₀ w) (mC m w) := by
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  have := fun w => sigmaFinite_sigC (Q := QCx Q₀ w) (mC_ne_zero hm w) (Nat.succ_pos k)
  have := fun w => sigmaFinite_smul (sigC (QCx Q₀ w) (mC m w)) (c := (2 : ℝ≥0∞) ^ k)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hR : Measurable fun a : (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w m)) =>
      ∏ w, Φr w (a w : Fin (k + 1) → ℝ) :=
    Finset.measurable_prod _ fun w _ => (hr w).comp (measurable_subtype_coe.comp (measurable_pi_apply w))
  have hC : Measurable fun b : (∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (mC m w)) =>
      ∏ w, Φc w (b w : Fin (k + 1) → ℂ) :=
    Finset.measurable_prod _ fun w _ => (hc w).comp (measurable_subtype_coe.comp (measurable_pi_apply w))
  rw [sigInfNF]
  change ∫⁻ z : TInfNF Q₀ m, (∏ w, Φr w (z.1 w : Fin (k + 1) → ℝ)) * ∏ w, Φc w (z.2 w : Fin (k + 1) → ℂ) ∂_ = _
  rw [lintegral_prod_mul hR.aemeasurable hC.aemeasurable,
    QuadFormsKB.Tamagawa.Measure.lintegral_pi_prod _
      (f := fun w (y : Sph (QRe Q₀ w) (σR w m)) => Φr w (y : Fin (k + 1) → ℝ))
      fun w => (hr w).comp measurable_subtype_coe,
    QuadFormsKB.Tamagawa.Measure.lintegral_pi_prod _
      (f := fun w (y : SphC (QCx Q₀ w) (mC m w)) => Φc w (y : Fin (k + 1) → ℂ))
      fun w => (hc w).comp measurable_subtype_coe]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [lintegral_smul_measure, smul_eq_mul]

/-- **The $m$-th Fourier coefficient of the theta integral for a product test function** (every number field, every
signature, $N = k+1\ge4$): for $m\in\mathcal O_F\setminus0$ with a rational point $\xi$ on $\{Q = m\}$ and $E$ a fundamental
domain,
$$I_m\Big(\bigotimes_w\Phi_w\Big) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot
  \prod_{w\ \mathrm{real}}\rho_{\Phi_w}(\sigma_w(m))\cdot\prod_{w\ \mathrm{complex}}2^{N-1}\int_{\{Q = \sigma_w(m)\}}\Phi_w\,d\sigma.$$
`thetaMean_eq_finDensityProduct` (the library's indefinite Siegel formula) and `lintegral_sigInfNF_prodFn`. -/
@[kb "weil1965" "Sur la formule de Siegel: the m-th coefficient of the theta integral is a product of local factors [unverified]"]
theorem thetaMean_prodFn (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0)
    (ξ : RatSphere Q₀ (m : F)) (hr : ∀ w, Measurable (Φr w)) (hc : ∀ w, Measurable (Φc w)) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    thetaMean Q₀ hQ (prodFn Φr Φc) E m =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ((∏ w, Orbital.orbI (QRe Q₀ w) (Φr w) (σR w (m : F))) *
        ∏ w, (2 : ℝ≥0∞) ^ k * ∫⁻ y, Φc w y ∂sigC (QCx Q₀ w) (mC (m : F) w)) := by
  rw [thetaMean_eq_finDensityProduct Q₀ hQ hk hm ξ (measurable_prodFn hr hc) hE,
    lintegral_sigInfNF_prodFn Q₀ hm hr hc]

/-! ### The Gaussian of the majorant, every number field -/

section Gauss

open Orbital

/-- The coefficients $\sigma_w(a_i)$ of $Q_0 = \sum_ia_ix_i^2$ at a real place $w$. -/
abbrev aR (a : Fin (k + 1) → 𝓞 F) (w : {w : InfinitePlace F // w.IsReal}) : Fin (k + 1) → ℝ :=
  fun i => σR w (a i : F)

/-- The coefficients $\sigma_w(a_i)$ of $Q_0 = \sum_ia_ix_i^2$ at a complex place $w$. -/
abbrev aC (a : Fin (k + 1) → 𝓞 F) (w : {w : InfinitePlace F // w.IsComplex}) : Fin (k + 1) → ℂ :=
  fun i => σC w (a i : F)

/-- **The Gaussian of the majorant on $V_\infty$**: $\Phi(x) = \prod_{w\ \mathrm{real}}e^{-\pi\sum_i|\sigma_w(a_i)|x_{w,i}^2}\cdot
\prod_{w\ \mathrm{complex}}e^{-2\pi\sum_i|\sigma_w(a_i)||x_{w,i}|^2}$, the standard archimedean test function of the
Siegel–Weil formula for $Q_0 = \sum_ia_ix_i^2$ (for a form definite at a real place $w$ the factor is the usual Gaussian
$e^{-\pi Q_w(x)}$). Parameter: `a`. -/
def gaussInf (a : Fin (k + 1) → 𝓞 F) : VInf F (k + 1) → ℝ≥0∞ :=
  prodFn (fun w x => ENNReal.ofReal (gaussMaj (aR a w) x)) fun w x => ENNReal.ofReal (gaussMajC (aC a w) x)

theorem orbR_nonneg {n : ℕ} (Q : QuadForm ℝ n) (Φ : (Fin n → ℝ) → ℝ) (t : ℝ) : 0 ≤ orbR Q Φ t :=
  ENNReal.toReal_nonneg

theorem orbCR_nonneg {n : ℕ} (Q : QuadForm ℂ n) (Φ : (Fin n → ℂ) → ℝ) (t : ℂ) : 0 ≤ orbCR Q Φ t :=
  ENNReal.toReal_nonneg

/-- The orbital integral of the Gaussian of the majorant is finite off $0$. -/
theorem orbI_gaussMaj_ne_top {n : ℕ} (hn : 1 ≤ n) {b : Fin n → ℝ} (hb : ∀ i, b i ≠ 0) (Q : QuadForm ℝ n) {t : ℝ}
    (ht : t ≠ 0) : orbI Q (fun x => ENNReal.ofReal (gaussMaj b x)) t ≠ ⊤ := by
  obtain ⟨C, hC⟩ := gaussMaj_decay b hb
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_sig_decay_lt_top (Q := Q) ht hn).ne)
    (?_ : orbI Q _ t ≤ ENNReal.ofReal C * _)
  rw [orbI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul' (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hC _)

/-- **The $m$-th Fourier coefficient of the theta integral for the Gaussian of the majorant** (every number field $F$,
$Q_0 = \sum_ia_ix_i^2$ over $\mathcal O_F$ nondegenerate, any signature, $N = k+1\ge4$, $m\in\mathcal O_F\setminus0$ with a
rational point $\xi$ on $\{Q = m\}$):
$$I_m(\Phi) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\prod_{w\ \mathrm{real}}\rho_w(\sigma_w(m))\cdot
  \prod_{w\ \mathrm{complex}}2^{N-1}\rho_w(\sigma_w(m)),$$
$\rho_w(t) = \int_{\{Q_w = t\}}\Phi_w\,d\sigma_t$ (`orbR` at a real place, `orbCR` at a complex place); each $\rho_w(\sigma_w(m))$
is the archimedean Whittaker integral (`whittakerInf_eq_orbR`, `whittakerInfC_eq_orbCR`). -/
@[kb "weil1965" "Sur la formule de Siegel: the m-th coefficient of the theta integral, Gaussian of the majorant [unverified]"]
theorem thetaMean_gauss (a : Fin (k + 1) → 𝓞 F) (ha : ∀ i, (a i : F) ≠ 0) (hQ : (QuadForm.diag a).Nondegenerate)
    (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere (QuadForm.diag a) (m : F))
    {E : Set (SOAdele (QuadForm.diag a))}
    (hE : IsFundamentalDomain (GammaSOAdele (QuadForm.diag a)) E (muTam (QuadForm.diag a) hQ fun _ => 1)) :
    thetaMean (QuadForm.diag a) hQ (gaussInf a) E m =
      ENNReal.ofReal (finDensityProduct (QuadForm.diag a) m) *
        ((∏ w, ENNReal.ofReal (orbR (QuadForm.diag (aR a w)) (gaussMaj (aR a w)) (σR w (m : F)))) *
          ∏ w, (2 : ℝ≥0∞) ^ k *
            ENNReal.ofReal (orbCR (QuadForm.diag (aC a w)) (gaussMajC (aC a w)) (mC (m : F) w))) := by
  have hr : ∀ w, Measurable fun x => ENNReal.ofReal (gaussMaj (aR a w) x) := fun w =>
    ENNReal.measurable_ofReal.comp (continuous_gaussMaj _).measurable
  have hc : ∀ w, Measurable fun x => ENNReal.ofReal (gaussMajC (aC a w) x) := fun w =>
    ENNReal.measurable_ofReal.comp (continuous_gaussMajC _).measurable
  rw [gaussInf, thetaMean_prodFn (QuadForm.diag a) hQ hk hm ξ hr hc hE]
  congr 2
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hQw : QRe (QuadForm.diag a) w = QuadForm.diag (aR a w) := diag_map_map a _
    have haw : ∀ i, aR a w i ≠ 0 := fun i => (map_ne_zero _).mpr (ha i)
    rw [hQw]
    exact (ENNReal.ofReal_toReal (orbI_gaussMaj_ne_top (by omega) haw _ (mR_ne_zero hm w))).symm
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hQw : QCx (QuadForm.diag a) w = QuadForm.diag (aC a w) := diag_map_map a _
    have haw : ∀ i, aC a w i ≠ 0 := fun i => (map_ne_zero _).mpr (ha i)
    rw [hQw]
    congr 1
    exact (ENNReal.ofReal_toReal (orbC_gaussMajC_ne_top (by omega) haw _ (mC_ne_zero hm w))).symm

/-- **The archimedean factor is the Whittaker integral, real place** ($Q_0 = \sum_ia_ix_i^2$, $N = k+1\ge3$, $m\ne0$): at
every real place $w$ the Whittaker integral of the Gaussian of the majorant converges absolutely and
$$\int_{\mathbb R}\Big(\int_{\mathbb R^N}\Phi_w(x)\,e(bQ_w(x))\,dx\Big)e(-\sigma_w(m)b)\,db = \rho_w(\sigma_w(m)),$$
$Q_w = \sum_i\sigma_w(a_i)x_i^2$ (`OrbitalReal.whittaker_gaussMaj_eq_orbR` in the field's coordinates). With
`thetaMean_gauss` and $W_\mathfrak p = C_\mathfrak p\beta_\mathfrak p$ this is $I_m(\Phi) = \prod_vW_v(m)$ up to the normalizing
constants $\gamma_Vc_B$ of the sections. -/
@[kb "weil1965" "Sur la formule de Siegel: archimedean Whittaker integral = integral over {Q = m}, every real place [unverified]"]
theorem whittakerInf_eq_orbR (a : Fin (k + 1) → 𝓞 F) (ha : ∀ i, (a i : F) ≠ 0) (hk : 2 ≤ k) {m : F} (hm : m ≠ 0)
    (w : {w : InfinitePlace F // w.IsReal}) :
    ∫ b : ℝ, (∫ x, (gaussMaj (aR a w) x : ℂ) * cexp (2 * Real.pi * I * (b * (QuadForm.diag (aR a w)).eval x))) *
        cexp (2 * Real.pi * I * (-(σR w m * b))) =
      orbR (QuadForm.diag (aR a w)) (gaussMaj (aR a w)) (σR w m) :=
  whittaker_gaussMaj_eq_orbR _ (fun i => (map_ne_zero _).mpr (ha i)) hk (mR_ne_zero hm w)

/-- **The archimedean factor is the Whittaker integral, complex place** ($Q_0 = \sum_ia_ix_i^2$, $N = k+1\ge3$, $m\ne0$):
at every complex place $w$, with $\psi_{\mathbb C}(z) = e^{2\pi i\cdot2\operatorname{Re}z}$ and Lebesgue measures, the Whittaker
integral of the Gaussian of the majorant converges absolutely and
$$\int_{\mathbb C}\Big(\int_{\mathbb C^N}\Phi_w(x)\,\psi_{\mathbb C}(bQ_w(x))\,dx\Big)\psi_{\mathbb C}(-\sigma_w(m)b)\,db
  = \tfrac14\rho_w(\sigma_w(m))$$
(`OrbitalComplex.whittakerC_gaussMajC_eq_orbCR`). With the self-dual measures $2\,dx\,dy$ the left side is $2^{N+1}$ times
larger, i.e. $2^{N-1}\rho_w(\sigma_w(m))$, the complex factor of `thetaMean_gauss`. -/
@[kb "weil1965" "Sur la formule de Siegel: archimedean Whittaker integral = integral over {Q = m}, every complex place [unverified]"]
theorem whittakerInfC_eq_orbCR (a : Fin (k + 1) → 𝓞 F) (ha : ∀ i, (a i : F) ≠ 0) (hk : 2 ≤ k) {m : F} (hm : m ≠ 0)
    (w : {w : InfinitePlace F // w.IsComplex}) :
    ∫ b : ℂ, (∫ x, (gaussMajC (aC a w) x : ℂ) *
          cexp (2 * Real.pi * I * (2 * (b * (QuadForm.diag (aC a w)).eval x).re))) *
        cexp (2 * Real.pi * I * (-(2 * (mC m w * b).re))) =
      (1 / 4 : ℂ) * orbCR (QuadForm.diag (aC a w)) (gaussMajC (aC a w)) (mC m w) :=
  whittakerC_gaussMajC_eq_orbCR _ (fun i => (map_ne_zero _).mpr (ha i)) hk (mC_ne_zero hm w)

open QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData in
/-- **The Siegel–Weil formula in Fourier-coefficient form for an indefinite form over a number field** (every number
field $F$, $Q_0 = \sum_ib_ix_i^2$ over $\mathcal O_F$ nondegenerate, all $b_i\ne0$, any signature, $N = 2(j+1)\ge4$ even,
$t\in\mathcal O_F\setminus0$ with a rational point $\xi$ on $\{Q = t\}$, $\Phi$ = the Gaussian of the majorant at every infinite
place, $E$ a fundamental domain of $SO(V)(F)$ in $SO(V)(\mathbb A)$): the finite Whittaker integrals have a convergent
product, $\prod_{v<\infty}W_v(t) = C_f\prod_\mathfrak p\beta_\mathfrak p(t)$, and the $t$-th orbit piece of the theta integral is
$$I_t(\Phi) = \gamma_{V,\infty}c_{B,\infty}\cdot\prod_{v<\infty}W_v(t)\cdot\prod_{w\ \mathrm{real}}W_w(\sigma_w(t))\cdot
  \prod_{w\ \mathrm{complex}}2^{N+1}W_w(\sigma_w(t)),$$
$W_w(t) = \int_{\mathbb R}\big(\int_{\mathbb R^N}\Phi_w(x)e(bQ_w(x))\,dx\big)e(-tb)\,db$ at a real place and
$W_w(t) = \int_{\mathbb C}\big(\int_{\mathbb C^N}\Phi_w(x)\psi_{\mathbb C}(bQ_w(x))\,dx\big)\psi_{\mathbb C}(-tb)\,db$ at a complex place
(Lebesgue measures; $2^{N+1}W_w$ is the Whittaker integral for the self-dual measures $2\,dx\,dy$ of $\psi_{\mathbb C}$). That is,
the $t$-th coefficient of the theta integral is the Euler product of the local Whittaker integrals of the Siegel–Weil
section (with $\gamma_{V,\infty}c_{B,\infty}$ the archimedean normalizing constant and $W_v$ = `whittakerV` of
$\mathbf 1_{\mathcal O_v^N}$): the right side $E_t(1, s_0, \Phi) = \prod_vW_v(t)$ of Weil's identity. Assembled from
`thetaMean_gauss` (the library's indefinite Siegel formula), `whittakerInf_eq_orbR`, `whittakerInfC_eq_orbCR`,
`hasProd_whittakerV` and `globalConst_eq` ($\gamma_{V,\infty}c_{B,\infty}C_f = |d_F|^{-(N-1)/2}$). -/
@[kb "weil1965" "Sur la formule de Siegel: Fourier coefficients of the theta integral = Euler product of Whittaker integrals [unverified]"]
theorem thetaMean_gauss_eq_whittaker {j : ℕ} (hj : 1 ≤ j) (b : Fin (2 * (j + 1)) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hQ : (QuadForm.diag b).Nondegenerate) {t : 𝓞 F} (ht : t ≠ 0) (ξ : RatSphere (QuadForm.diag b) (t : F))
    {E : Set (SOAdele (QuadForm.diag b))}
    (hE : IsFundamentalDomain (GammaSOAdele (QuadForm.diag b)) E (muTam (QuadForm.diag b) hQ fun _ => 1)) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        whittakerV v (aOfInt v b hb) ((LocalDensity.NF.ι v t : v.adicCompletionIntegers F) : v.adicCompletion F))
      (constFin (unitsOfInt b hb) * Siegel.eulerProductNF (QuadForm.diag b) t) ∧
    (((thetaMean (k := 2 * j + 1) (QuadForm.diag b) hQ (gaussInf b) E t).toReal : ℝ) : ℂ) =
      (localDataInf (F := F)).gammaV (aInf (unitsOfInt b hb)) * (localDataInf (F := F)).cB (aInf (unitsOfInt b hb)) *
        (constFin (unitsOfInt b hb) * Siegel.eulerProductNF (QuadForm.diag b) t) *
        ((∏ w, ∫ y : ℝ, (∫ x, (gaussMaj (aR b w) x : ℂ) *
            cexp (2 * Real.pi * I * (y * (QuadForm.diag (aR b w)).eval x))) *
          cexp (2 * Real.pi * I * (-(σR w (t : F) * y)))) *
        ∏ w, (2 : ℂ) ^ (2 * (j + 1) + 1) * ∫ y : ℂ, (∫ x, (gaussMajC (aC b w) x : ℂ) *
            cexp (2 * Real.pi * I * (2 * (y * (QuadForm.diag (aC b w)).eval x).re))) *
          cexp (2 * Real.pi * I * (-(2 * (mC (t : F) w * y).re)))) := by
  have hb' : ∀ i, (b i : F) ≠ 0 := fun i h => hb i (by exact_mod_cast h)
  have ht' : (t : F) ≠ 0 := fun h => ht (by exact_mod_cast h)
  have hP := Siegel.hasProd_eulerProductNF_uncond hQ (by omega : 4 ≤ 2 * (j + 1)) ht
  refine ⟨hasProd_whittakerV (by omega) b hb t ht hP, ?_⟩
  have hβ : 0 ≤ Siegel.eulerProductNF (QuadForm.diag b) t :=
    tprod_nonneg fun v => Siegel.localDensityNF_nonneg v _ hQ ht
  have hd : |(discr F : ℝ)| ^ (-(((2 * j + 1 + 1 : ℕ) : ℝ) - 1) / 2) =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * (j + 1) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (abs_nonneg _), ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg _), show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    congr 1
    push_cast
    ring
  have hfin : finDensityProduct (QuadForm.diag b) t =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * (j + 1) - 1) * Siegel.eulerProductNF (QuadForm.diag b) t := by
    rw [finDensityProduct]
    exact congrArg (fun x => x * Siegel.eulerProductNF (QuadForm.diag b) t) hd
  have hfin0 : 0 ≤ finDensityProduct (QuadForm.diag b) t := by
    rw [hfin]; exact mul_nonneg (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _) hβ
  rw [thetaMean_gauss (k := 2 * j + 1) b hb' hQ (by omega) ht' ξ hE, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_prod, ENNReal.toReal_prod, ENNReal.toReal_ofReal hfin0]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (orbR_nonneg _ _ _), ENNReal.toReal_ofReal (orbCR_nonneg _ _ _)]
  have hR : ((∏ w, orbR (QuadForm.diag (aR b w)) (gaussMaj (aR b w)) (σR w (t : F)) : ℝ) : ℂ) =
      ∏ w, ∫ y : ℝ, (∫ x, (gaussMaj (aR b w) x : ℂ) *
          cexp (2 * Real.pi * I * (y * (QuadForm.diag (aR b w)).eval x))) *
        cexp (2 * Real.pi * I * (-(σR w (t : F) * y))) := by
    push_cast
    exact Finset.prod_congr rfl fun w _ => (whittakerInf_eq_orbR (k := 2 * j + 1) b hb' (by omega) ht' w).symm
  have hC : ((∏ w, (2 ^ (2 * j + 1) : ℝ≥0∞).toReal *
        orbCR (QuadForm.diag (aC b w)) (gaussMajC (aC b w)) (mC (t : F) w) : ℝ) : ℂ) =
      ∏ w, (2 : ℂ) ^ (2 * (j + 1) + 1) * ∫ y : ℂ, (∫ x, (gaussMajC (aC b w) x : ℂ) *
          cexp (2 * Real.pi * I * (2 * (y * (QuadForm.diag (aC b w)).eval x).re))) *
        cexp (2 * Real.pi * I * (-(2 * (mC (t : F) w * y).re))) := by
    push_cast
    refine Finset.prod_congr rfl fun w _ => ?_
    refine Eq.trans ?_ (congrArg (fun z => (2 : ℂ) ^ (2 * (j + 1) + 1) * z)
      (whittakerInfC_eq_orbCR (k := 2 * j + 1) b hb' (by omega) ht' w).symm)
    simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    push_cast
    ring_nf
    rfl
  have hK : ((finDensityProduct (QuadForm.diag b) t : ℝ) : ℂ) =
      (localDataInf (F := F)).gammaV (aInf (unitsOfInt b hb)) * (localDataInf (F := F)).cB (aInf (unitsOfInt b hb)) *
        (constFin (unitsOfInt b hb) * Siegel.eulerProductNF (QuadForm.diag b) t) := by
    rw [← mul_assoc, globalConst_eq, hfin]
    push_cast
    ring
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  exact congrArg₂ (· * ·) hK (congrArg₂ (· * ·) hR hC)

end Gauss

end QuadFormsKB.SiegelWeil.Indefinite
