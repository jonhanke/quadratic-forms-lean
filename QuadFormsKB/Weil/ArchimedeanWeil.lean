/-
# The Weil identity for every Schwartz function on $F_\infty$; the archimedean model

**Layer:** local, archimedean, any number field $F$.

**The Weil identity** (`weilInf_identity_schwartz`): for every Schwartz function $f$ on $F_\infty$, every unit
$b \in F_\infty^\times$ and $c = -(4b)^{-1}$,
$$\mathcal F\big(\psi_\infty(bx^2)\,\hat f\big)(y) = \gamma_\infty(b)\,\psi_\infty(cy^2)\,\mathcal F\big(\psi_\infty(cx^2)f\big)(2cy).$$
Previously it was available only for the Gaussian (`weilInf_identity`). *Proof* (regularization): with $r_\varepsilon(x) = e^{-\varepsilon\|x\|^2}$
(`regInf`, a product over the places),
1. $\mathcal F(\psi(bx^2)\hat f)(y) = \lim_{\varepsilon\to0^+}\int r_\varepsilon(x)\psi(bx^2)\hat f(x)\psi(xy)\,dx$ (dominated convergence,
   $\hat f$ integrable);
2. for $\varepsilon > 0$, Fubini gives $\int f(z)K_\varepsilon(z + y)\,dz$ with $K_\varepsilon = \mathcal F(r_\varepsilon\psi(bx^2))$ (`kerInf`), a product of
   explicit complex Gaussian transforms: at a real place $K = (\varepsilon/\pi - 2ib)^{-1/2}e^{-\pi\eta^2/(\varepsilon/\pi - 2ib)}$ (`KR_eq`),
   at a complex place $K = (u^2 + 4|b|^2)^{-1/2}\exp\big(-\pi\frac{2|\eta|^2u + 4i\operatorname{Re}(\bar b\eta^2)}{u^2 + 4|b|^2}\big)$, $u = \varepsilon/2\pi$
   (`KC_eq`, from `fourierC_chirpC_gaussC` by dilation);
3. $K_\varepsilon(\eta) \to \gamma_\infty(b)\psi(c\eta^2)$ boundedly (`tendsto_kerInf`, `norm_kerInf_le`), so by dominated convergence
   the limit is $\gamma_\infty(b)\int f(z)\psi(c(z+y)^2)\,dz = \gamma_\infty(b)\psi(cy^2)\mathcal F(\psi(cx^2)f)(2cy)$.

**The archimedean model** (`isModel_inf`): all axioms of `LocalData.IsModel` hold for `localDataInf`, so
**`weilRepInf`** $: \mathrm{SL}_2(k) \to \operatorname{End}_{\mathbb C}S(V_\infty)$ is a representation for every field $k \to F_\infty$.

Sources: Weil, Acta Math. 111 (1964), §14, Thm. 2 and §26 [unverified]; Kudla, *Notes on the local theta
correspondence* (1996), §I.1 [unverified]; Folland, *Harmonic analysis in phase space* (1989), Ch. 4 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Archimedean

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Complex Filter Topology
open QuadFormsKB.Analysis
open scoped Classical MatrixGroups Real FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

/-! ### The real place -/

lemma chirpR_eq_exp (β x : ℝ) : chirpR β x = cexp (2 * π * I * (β : ℂ) * (x : ℂ) ^ 2) := by
  rw [chirpR, fourierChar_coe]; push_cast; ring_nf

/-- The regularized chirp kernel at a real place: $K_{\mathbb R}(\varepsilon, \beta, \eta) = \int e^{-\varepsilon x^2}e(\beta x^2)e(x\eta)\,dx$. -/
def KR (ε β η : ℝ) : ℂ := fourierR (fun x : ℝ => cexp (-(ε : ℂ) * (x : ℂ) ^ 2) * chirpR β x) η

/-- The parameter $\varepsilon/\pi - 2i\beta$. -/
def gR (ε β : ℝ) : ℂ := (ε : ℂ) / π - 2 * I * β

lemma KR_eq {ε : ℝ} (hε : 0 < ε) (β η : ℝ) :
    KR ε β η = (gR ε β)⁻¹ ^ (1 / 2 : ℂ) * cexp (-π * (η : ℂ) ^ 2 / gR ε β) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : (fun x : ℝ => cexp (-(ε : ℂ) * (x : ℂ) ^ 2) * chirpR β x) =
      fun x : ℝ => cexp (-(π * gR ε β) * (x : ℂ) ^ 2) := by
    funext x; rw [chirpR_eq_exp, ← Complex.exp_add, gR]; congr 1; field_simp; ring
  rw [KR, h, fourierR_cexp_sq _ (by simp [gR]; positivity)]

lemma gR_ne_zero {ε β : ℝ} (hβ : β ≠ 0) : gR ε β ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [gR] at this
  exact hβ this

lemma tendsto_gR (β : ℝ) : Tendsto (fun ε : ℝ => gR ε β) (𝓝[>] 0) (𝓝 (-2 * I * β)) := by
  have : Continuous fun ε : ℝ => gR ε β := by unfold gR; fun_prop
  have h := this.tendsto 0
  simp only [gR, Complex.ofReal_zero, zero_div, zero_sub] at h
  exact (h.mono_left nhdsWithin_le_nhds).congr' (Eventually.of_forall fun ε => by simp [gR]) |>.trans
    (by rw [neg_mul, neg_mul])

lemma tendsto_KR {β : ℝ} (hβ : β ≠ 0) (η : ℝ) :
    Tendsto (fun ε => KR ε β η) (𝓝[>] 0) (𝓝 (weilR β * chirpR (-(4 * β)⁻¹) η)) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have h0 : (-2 * I * (β : ℂ)) ≠ 0 := by simp [hβc]
  have h1 := tendsto_gR β
  have h2 := h1.inv₀ h0
  have hslit : (-2 * I * (β : ℂ))⁻¹ ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right
    simp [Complex.inv_im, hβ]
  have h3 := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hslit).tendsto.comp h2
  have h4 := ((tendsto_const_nhds (x := -π * (η : ℂ) ^ 2)).div h1 h0).cexp
  have hlim := h3.mul h4
  refine (hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => (KR_eq hε β η).symm)).trans ?_
  apply le_of_eq; congr 1
  rw [weilR, chirpR_eq_exp]
  congr 1
  · congr 1; field_simp; rw [I_sq]
  · congr 1; push_cast; field_simp; ring_nf; rw [I_sq]; ring

lemma norm_KR_le {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : β ≠ 0) (η : ℝ) :
    ‖KR ε β η‖ ≤ (2 * |β|)⁻¹ ^ (1 / 2 : ℝ) := by
  have hg0 := gR_ne_zero (ε := ε) hβ
  rw [KR_eq hε, norm_mul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real,
    Complex.norm_exp]
  have hre : (-π * (η : ℂ) ^ 2 / gR ε β).re ≤ 0 := by
    rw [div_eq_mul_inv, show -π * (η : ℂ) ^ 2 = ((-π * η ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    refine mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos, sq_nonneg η]) ?_
    rw [Complex.inv_re]
    exact div_nonneg (by simp [gR]; positivity) (Complex.normSq_nonneg _)
  have hnorm : 2 * |β| ≤ ‖gR ε β‖ := by
    have := Complex.abs_im_le_norm (gR ε β)
    simpa [gR, abs_mul] using this
  have hb : 0 < 2 * |β| := by positivity
  calc ‖(gR ε β)⁻¹‖ ^ (1 / 2 : ℝ) * Real.exp (-π * (η : ℂ) ^ 2 / gR ε β).re
      ≤ (2 * |β|)⁻¹ ^ (1 / 2 : ℝ) * 1 := by
        gcongr
        · rw [norm_inv]; exact inv_anti₀ hb hnorm
        · exact Real.exp_le_one_iff.mpr hre
    _ = _ := mul_one _

/-! ### The complex place -/

/-- The regularized chirp kernel at a complex place:
$K_{\mathbb C}(\varepsilon, \beta, \eta) = \int e^{-\varepsilon|z|^2}e(2\operatorname{Re}(\beta z^2))e(2\operatorname{Re}(z\eta))\,2\,dx\,dy$. -/
def KC (ε : ℝ) (β η : ℂ) : ℂ := fourierC (fun z => cexp (-(ε : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)) * chirpC β z) η

/-- The closed form $(u^2 + 4|\beta|^2)^{-1/2}\exp\big(-\pi\frac{2u|\eta|^2 + 4i\operatorname{Re}(\bar\beta\eta^2)}{u^2 + 4|\beta|^2}\big)$. -/
def CF (u : ℝ) (β η : ℂ) : ℂ :=
  ((Real.sqrt (u ^ 2 + 4 * ‖β‖ ^ 2))⁻¹ : ℝ) *
    cexp (-π * (2 * u * ((‖η‖ ^ 2 : ℝ) : ℂ) + 4 * I * (((starRingEnd ℂ β * η ^ 2).re : ℝ) : ℂ)) /
      ((u ^ 2 + 4 * ‖β‖ ^ 2 : ℝ) : ℂ))

/-- Dilation at a complex place: $\mathcal F(g(s\,\cdot))(\eta) = s^{-2}\hat g(\eta/s)$ for $s > 0$. -/
lemma fourierC_comp_smul (g : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (η : ℂ) :
    fourierC (fun z => g ((s : ℂ) * z)) η = ((s ^ 2)⁻¹ : ℝ) * fourierC g (η / s) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold fourierC
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ))
    (fun w : ℂ => g w * (𝐞 (2 * (w * (η / s)).re) : ℂ)) s
  simp only [Complex.real_smul, Complex.finrank_real_complex] at h
  have e : ∀ z : ℂ, g ((s : ℂ) * z) * (𝐞 (2 * (z * η).re) : ℂ) =
      g ((s : ℂ) * z) * (𝐞 (2 * ((s : ℂ) * z * (η / s)).re) : ℂ) := by
    intro z; congr 4; field_simp
  simp only [e, h]
  rw [abs_of_pos (by positivity)]
  push_cast
  ring

lemma KC_eq {ε : ℝ} (hε : 0 < ε) {β : ℂ} (hβ : β ≠ 0) (η : ℂ) : KC ε β η = CF (ε / (2 * π)) β η := by
  set s : ℝ := Real.sqrt (ε / (2 * π)) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = ε / (2 * π) := Real.sq_sqrt (by positivity)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hfun : (fun z => cexp (-(ε : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)) * chirpC β z) =
      fun z => (fun w => chirpC (β / ((s ^ 2 : ℝ) : ℂ)) w * gaussC w) ((s : ℂ) * z) := by
    funext z
    simp only [gaussC, chirpC]
    rw [mul_comm]
    congr 1
    · congr 3
      push_cast
      field_simp
    · congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow, hs2]
      push_cast
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
  rw [KC, hfun, fourierC_comp_smul (fun w => chirpC (β / ((s ^ 2 : ℝ) : ℂ)) w * gaussC w) hs,
    fourierC_chirpC_gaussC, gaussFTC, CF]
  have hπ : 0 < π := Real.pi_pos
  have hβn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hD : (0 : ℝ) < (ε / (2 * π)) ^ 2 + 4 * ‖β‖ ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + 4 * ‖β / ((s ^ 2 : ℝ) : ℂ)‖ ^ 2) =
      Real.sqrt ((ε / (2 * π)) ^ 2 + 4 * ‖β‖ ^ 2) / s ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), hs2]
    rw [show 1 + 4 * (‖β‖ / (ε / (2 * π))) ^ 2 = ((ε / (2 * π)) ^ 2 + 4 * ‖β‖ ^ 2) / ((ε / (2 * π)) ^ 2) by
      field_simp]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  rw [← mul_assoc]
  congr 1
  · push_cast
    have : (Real.sqrt ((ε / (2 * π)) ^ 2 + 4 * ‖β‖ ^ 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
    have : ((s : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ hs0
    field_simp
  · congr 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), map_div₀, Complex.conj_ofReal]
    have hre : ((starRingEnd ℂ β / ((s ^ 2 : ℝ) : ℂ) * (η / (s : ℂ)) ^ 2).re : ℂ) =
        (((starRingEnd ℂ β * η ^ 2).re : ℝ) : ℂ) / ((s ^ 2 : ℝ) : ℂ) ^ 2 := by
      rw [show starRingEnd ℂ β / ((s ^ 2 : ℝ) : ℂ) * (η / (s : ℂ)) ^ 2 =
          (starRingEnd ℂ β * η ^ 2) / (((s ^ 2) ^ 2 : ℝ) : ℂ) by push_cast; field_simp]
      rw [Complex.div_ofReal_re]; push_cast; ring
    rw [hre, hs2]
    push_cast
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have : ((ε : ℂ) / (2 * π)) ^ 2 + 4 * (‖β‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hD.ne'
    have hsq : (s : ℂ) ^ 2 = ε / (2 * π) := by exact_mod_cast hs2
    rw [div_pow ((‖η‖ : ℝ) : ℂ), hsq]
    field_simp

lemma CF_denom_pos {β : ℂ} (hβ : β ≠ 0) (u : ℝ) : 0 < u ^ 2 + 4 * ‖β‖ ^ 2 := by
  have := norm_pos_iff.mpr hβ; positivity

lemma continuous_CF {β : ℂ} (hβ : β ≠ 0) (η : ℂ) : Continuous fun u : ℝ => CF u β η := by
  unfold CF
  refine Continuous.mul ?_ ?_
  · refine Complex.continuous_ofReal.comp (Continuous.inv₀ (by fun_prop) fun u => ?_)
    exact (Real.sqrt_pos.mpr (CF_denom_pos hβ u)).ne'
  · refine Complex.continuous_exp.comp (Continuous.div (by fun_prop) (by fun_prop) fun u => ?_)
    exact_mod_cast (CF_denom_pos hβ u).ne'

lemma re_neg_inv_four_mul (β η : ℂ) (hβ : β ≠ 0) :
    (-(4 * β)⁻¹ * η ^ 2).re = -(starRingEnd ℂ β * η ^ 2).re / (4 * ‖β‖ ^ 2) := by
  have hn : (Complex.normSq β : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.mpr hβ).ne'
  have e : -(4 * β)⁻¹ * η ^ 2 = (starRingEnd ℂ β * η ^ 2) * ((-(4 * Complex.normSq β)⁻¹ : ℝ) : ℂ) := by
    rw [mul_inv, Complex.inv_def β]
    push_cast
    field_simp
  rw [e, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq]
  ring

lemma CF_zero {β : ℂ} (hβ : β ≠ 0) (η : ℂ) : CF 0 β η = weilC β * chirpC (-(4 * β)⁻¹) η := by
  have hβn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  unfold CF weilC chirpC
  rw [fourierChar_coe, re_neg_inv_four_mul β η hβ]
  have hs : Real.sqrt ((0 : ℝ) ^ 2 + 4 * ‖β‖ ^ 2) = 2 * ‖β‖ := by
    rw [show (0 : ℝ) ^ 2 + 4 * ‖β‖ ^ 2 = (2 * ‖β‖) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs]
  congr 1
  congr 1
  push_cast
  have : (‖β‖ : ℂ) ≠ 0 := by exact_mod_cast hβn.ne'
  field_simp
  ring

lemma tendsto_KC {β : ℂ} (hβ : β ≠ 0) (η : ℂ) :
    Tendsto (fun ε => KC ε β η) (𝓝[>] 0) (𝓝 (weilC β * chirpC (-(4 * β)⁻¹) η)) := by
  have h1 : Tendsto (fun ε : ℝ => ε / (2 * π)) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_id.div_const (2 * π)).tendsto 0)
  have h2 := ((continuous_CF hβ η).tendsto 0).comp h1
  rw [CF_zero hβ η] at h2
  exact (h2.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun ε hε => (KC_eq hε hβ η).symm)

lemma norm_KC_le {ε : ℝ} (hε : 0 < ε) {β : ℂ} (hβ : β ≠ 0) (η : ℂ) : ‖KC ε β η‖ ≤ (2 * ‖β‖)⁻¹ := by
  have hβn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  set u : ℝ := ε / (2 * π) with hu
  have hu0 : 0 ≤ u := by positivity
  have hD := CF_denom_pos hβ u
  rw [KC_eq hε hβ η, CF, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-π * (2 * u * ((‖η‖ ^ 2 : ℝ) : ℂ) + 4 * I * (((starRingEnd ℂ β * η ^ 2).re : ℝ) : ℂ)) /
      ((u ^ 2 + 4 * ‖β‖ ^ 2 : ℝ) : ℂ)).re ≤ 0 := by
    rw [Complex.div_ofReal_re]
    refine div_nonpos_of_nonpos_of_nonneg ?_ hD.le
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.I_re, Complex.I_im, Complex.neg_im, Complex.add_im, Complex.mul_im]
    norm_num
    have : 0 ≤ π * (2 * u * ‖η‖ ^ 2) := by positivity
    linarith
  have hsq : 2 * ‖β‖ ≤ Real.sqrt (u ^ 2 + 4 * ‖β‖ ^ 2) := by
    rw [show 2 * ‖β‖ = Real.sqrt ((2 * ‖β‖) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hD))]
  calc (Real.sqrt (u ^ 2 + 4 * ‖β‖ ^ 2))⁻¹ * Real.exp _ ≤ (2 * ‖β‖)⁻¹ * 1 := by
        gcongr
        exact Real.exp_le_one_iff.mpr hre
    _ = _ := mul_one _

lemma continuous_KR_eta {ε : ℝ} (β : ℝ) : Continuous fun η : ℝ =>
    (gR ε β)⁻¹ ^ (1 / 2 : ℂ) * cexp (-π * (η : ℂ) ^ 2 / gR ε β) := by fun_prop

lemma continuous_CF_eta (u : ℝ) (β : ℂ) : Continuous fun η : ℂ => CF u β η := by
  unfold CF; fun_prop

/-! ### The kernel on $F_\infty$ -/

section Global

variable {F : Type} [Field F] [NumberField F]

local notation "V∞" => mixedSpace F

/-- **The regularizer** $r_\varepsilon(x) = \prod_{w\ \mathrm{real}}e^{-\varepsilon x_w^2}\prod_{w\ \mathrm{complex}}e^{-\varepsilon|x_w|^2}$. -/
def regInf (ε : ℝ) (x : V∞) : ℂ :=
  (∏ w, cexp (-(ε : ℂ) * ((x.1 w : ℝ) : ℂ) ^ 2)) * ∏ w, cexp (-(ε : ℂ) * ((‖x.2 w‖ ^ 2 : ℝ) : ℂ))

/-- **The regularized kernel** $K_\varepsilon = \mathcal F(r_\varepsilon\,\psi_\infty(bx^2))$. -/
def kerInf (ε : ℝ) (b η : V∞) : ℂ := fourierInf (fun x => regInf ε x * (psiInf (b * x * x) : ℂ)) η

lemma kerInf_eq (ε : ℝ) (b η : V∞) :
    kerInf ε b η = (∏ w, KR ε (b.1 w) (η.1 w)) * ∏ w, KC ε (b.2 w) (η.2 w) := by
  have h : (fun x : V∞ => regInf ε x * (psiInf (b * x * x) : ℂ)) = fun x =>
      (∏ w, (fun w (t : ℝ) => cexp (-(ε : ℂ) * (t : ℂ) ^ 2) * chirpR (b.1 w) t) w (x.1 w)) *
        ∏ w, (fun w (z : ℂ) => cexp (-(ε : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)) * chirpC (b.2 w) z) w (x.2 w) := by
    funext x
    rw [regInf, psiInf_chirp_eq_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  rw [kerInf, h, fourierInf_prod (fun w (t : ℝ) => cexp (-(ε : ℂ) * (t : ℂ) ^ 2) * chirpR (b.1 w) t)
    (fun w (z : ℂ) => cexp (-(ε : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)) * chirpC (b.2 w) z)]
  rfl

lemma norm_regInf_le {ε : ℝ} (hε : 0 ≤ ε) (x : V∞) : ‖regInf ε x‖ ≤ 1 := by
  rw [regInf, norm_mul, norm_prod, norm_prod]
  refine mul_le_one₀ (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun w _ => ?_)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun w _ => ?_)
  · rw [Complex.norm_exp, Real.exp_le_one_iff]
    rw [show -(ε : ℂ) * ((x.1 w : ℝ) : ℂ) ^ 2 = ((-ε * x.1 w ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    nlinarith [sq_nonneg (x.1 w)]
  · rw [Complex.norm_exp, Real.exp_le_one_iff]
    rw [show -(ε : ℂ) * ((‖x.2 w‖ ^ 2 : ℝ) : ℂ) = ((-ε * ‖x.2 w‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    nlinarith [sq_nonneg ‖x.2 w‖]

lemma continuous_regInf (ε : ℝ) : Continuous (regInf (F := F) ε) := by
  unfold regInf; fun_prop

lemma tendsto_regInf (x : V∞) : Tendsto (fun ε => regInf ε x) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous fun ε : ℝ => regInf ε x := by unfold regInf; fun_prop
  have h := hc.tendsto 0
  simp only [regInf, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, Finset.prod_const_one,
    mul_one] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- $r_\varepsilon$ is Schwartz for $\varepsilon > 0$ (a dilate of the self-dual Gaussian). -/
lemma regInf_mem_schwartzInf {ε : ℝ} (hε : 0 < ε) : regInf (F := F) ε ∈ schwartzInf (F := F) := by
  set a : ℝ := Real.sqrt (ε / π)
  set c : ℝ := Real.sqrt (ε / (2 * π))
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  set σ : (V∞)ˣ :=
    { val := (fun _ => a, fun _ => (c : ℂ))
      inv := (fun _ => a⁻¹, fun _ => ((c⁻¹ : ℝ) : ℂ))
      val_inv := by
        ext w
        · exact mul_inv_cancel₀ ha.ne'
        · simp [hc.ne']
      inv_val := by
        ext w
        · exact inv_mul_cancel₀ ha.ne'
        · simp [hc.ne'] }
  have h : regInf (F := F) ε = dil (σ : V∞) (gaussInfFun (F := F)) := by
    funext x
    simp only [regInf, dil, gaussInfFun, gaussR, gaussC, σ, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
    have ha2 : a ^ 2 = ε / π := Real.sq_sqrt (by positivity)
    have hc2 : c ^ 2 = ε / (2 * π) := Real.sq_sqrt (by positivity)
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      congr 1
      have ha2' : (a : ℂ) ^ 2 = ε / π := by rw [← Complex.ofReal_pow, ha2]; push_cast; ring
      push_cast
      rw [mul_pow, ha2']
      field_simp
    · refine Finset.prod_congr rfl fun w _ => ?_
      congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, mul_pow, hc2]
      push_cast; field_simp
  rw [h]
  exact dil_mem_schwartzInf σ gaussInfFun_mem

lemma integrable_of_mem_schwartzInf {f : V∞ → ℂ} (hf : f ∈ schwartzInf (F := F)) :
    Integrable f (selfDualInf (F := F)) := by
  obtain ⟨G, rfl⟩ := hf
  unfold selfDualInf; exact G.integrable.smul_measure_nnreal

lemma continuous_of_mem_schwartzInf {f : V∞ → ℂ} (hf : f ∈ schwartzInf (F := F)) : Continuous f := by
  obtain ⟨G, rfl⟩ := hf; exact G.continuous

lemma continuous_psiInf_comp {X : Type*} [TopologicalSpace X] {g : X → V∞} (hg : Continuous g) :
    Continuous fun x => (psiInf (g x) : ℂ) :=
  continuous_subtype_val.comp ((Real.continuous_fourierChar).comp (continuous_traceInf.comp hg))

lemma unit_inv_fst (u : (V∞)ˣ) (w : {w : InfinitePlace F // IsReal w}) :
    ((u⁻¹ : (V∞)ˣ) : V∞).1 w = ((u : V∞).1 w)⁻¹ := by
  have h := congrArg (fun z : V∞ => z.1 w) u.mul_inv
  simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] at h
  exact eq_inv_of_mul_eq_one_right h

lemma unit_inv_snd (u : (V∞)ˣ) (w : {w : InfinitePlace F // IsComplex w}) :
    ((u⁻¹ : (V∞)ˣ) : V∞).2 w = ((u : V∞).2 w)⁻¹ := by
  have h := congrArg (fun z : V∞ => z.2 w) u.mul_inv
  simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] at h
  exact eq_inv_of_mul_eq_one_right h

lemma cW_fst (b : (V∞)ˣ) (w : {w : InfinitePlace F // IsReal w}) :
    (((localDataInf (F := F)).cW b : (V∞)ˣ) : V∞).1 w = -(4 * (b : V∞).1 w)⁻¹ := by
  simp only [LocalData.cW, Units.val_neg, Prod.fst_neg, Pi.neg_apply, unit_inv_fst, Units.val_mul,
    Prod.fst_mul, Pi.mul_apply]
  congr 2
  rw [show (localDataInf (F := F)).two = twoInf from rfl, twoInf_val]
  norm_num

lemma cW_snd (b : (V∞)ˣ) (w : {w : InfinitePlace F // IsComplex w}) :
    (((localDataInf (F := F)).cW b : (V∞)ˣ) : V∞).2 w = -(4 * (b : V∞).2 w)⁻¹ := by
  simp only [LocalData.cW, Units.val_neg, Prod.snd_neg, Pi.neg_apply, unit_inv_snd, Units.val_mul,
    Prod.snd_mul, Pi.mul_apply]
  congr 2
  rw [show (localDataInf (F := F)).two = twoInf from rfl, twoInf_val]
  norm_num

/-- **The limit of the kernel**: $K_\varepsilon(\eta) \to \gamma_\infty(b)\psi_\infty(c\eta^2)$, $c = -(4b)^{-1}$. -/
lemma tendsto_kerInf (b : (V∞)ˣ) (η : V∞) :
    Tendsto (fun ε => kerInf ε (b : V∞) η) (𝓝[>] 0)
      (𝓝 (weilInf (b : V∞) * (psiInf (((localDataInf (F := F)).cW b : V∞) * η * η) : ℂ))) := by
  simp only [kerInf_eq]
  have hR := tendsto_finsetProd (Finset.univ : Finset {w : InfinitePlace F // IsReal w})
    fun w _ => tendsto_KR (unit_fst_ne_zero b w) (η.1 w)
  have hC := tendsto_finsetProd (Finset.univ : Finset {w : InfinitePlace F // IsComplex w})
    fun w _ => tendsto_KC (unit_snd_ne_zero b w) (η.2 w)
  convert hR.mul hC using 2
  rw [weilInf, psiInf_chirp_eq_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [cW_fst, cW_snd]
  ring

/-- The bound $\|K_\varepsilon(\eta)\| \le C_b$. -/
def kerBound (b : V∞) : ℝ :=
  (∏ w, (2 * |b.1 w|)⁻¹ ^ (1 / 2 : ℝ)) * ∏ w, (2 * ‖b.2 w‖)⁻¹

lemma norm_kerInf_le {ε : ℝ} (hε : 0 < ε) (b : (V∞)ˣ) (η : V∞) :
    ‖kerInf ε (b : V∞) η‖ ≤ kerBound (b : V∞) := by
  rw [kerInf_eq, norm_mul, norm_prod, norm_prod, kerBound]
  exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun w _ =>
      norm_KR_le hε (unit_fst_ne_zero b w) _)
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun w _ => norm_KC_le hε (unit_snd_ne_zero b w) _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => by positivity)

lemma continuous_kerInf {ε : ℝ} (hε : 0 < ε) (b : (V∞)ˣ) : Continuous (kerInf ε (b : V∞)) := by
  have h : kerInf ε (b : V∞) = fun η : V∞ =>
      (∏ w, (gR ε ((b : V∞).1 w))⁻¹ ^ (1 / 2 : ℂ) * cexp (-π * ((η.1 w : ℝ) : ℂ) ^ 2 / gR ε ((b : V∞).1 w))) *
        ∏ w, CF (ε / (2 * π)) ((b : V∞).2 w) (η.2 w) := by
    funext η
    rw [kerInf_eq]
    congr 1
    · exact Finset.prod_congr rfl fun w _ => KR_eq hε _ _
    · exact Finset.prod_congr rfl fun w _ => KC_eq hε (unit_snd_ne_zero b w) _
  rw [h]
  refine Continuous.mul (continuous_finsetProd _ fun w _ => ?_) (continuous_finsetProd _ fun w _ => ?_)
  · exact (continuous_KR_eta (ε := ε) _).comp ((continuous_apply w).comp continuous_fst)
  · exact (continuous_CF_eta _ _).comp ((continuous_apply w).comp continuous_snd)

end Global

/-! ### The Weil identity for every Schwartz function -/

section Main

variable {F : Type} [Field F] [NumberField F]

local notation "V∞" => mixedSpace F

lemma psiInf_add' (u v : V∞) : (psiInf (u + v) : ℂ) = psiInf u * psiInf v := by
  rw [psiInf, traceInf_add, AddChar.map_add_eq_mul, Circle.coe_mul]; rfl

/-- **The Weil identity at the infinite places for every Schwartz function** $f$ (axiom (W) of `LocalData.IsModel` for
`localDataInf`): for $b \in F_\infty^\times$ and $c = -(4b)^{-1}$,
$$\mathcal F\big(\psi_\infty(bx^2)\hat f\big)(y) = \gamma_\infty(b)\,\psi_\infty(cy^2)\,\mathcal F\big(\psi_\infty(cx^2)f\big)(2cy).$$
*Proof:* regularize by $r_\varepsilon(x) = e^{-\varepsilon\|x\|^2}$, Fubini, and dominated convergence twice, with the explicit kernel
$K_\varepsilon = \mathcal F(r_\varepsilon\psi(bx^2)) \to \gamma_\infty(b)\psi(c\eta^2)$ (`tendsto_kerInf`, bounded by `norm_kerInf_le`). -/
@[kb "weil1964" "§14, Thm. 2 (the relation $\\mathcal F e_b\\mathcal F = \\gamma(b)\\,e_c D_{2c}\\mathcal F e_c$), archimedean places [unverified]"]
theorem weilInf_identity_schwartz {f : V∞ → ℂ} (hf : f ∈ schwartzInf (F := F)) (b : (V∞)ˣ) (y : V∞) :
    (localDataInf (F := F)).four ((localDataInf (F := F)).chirp b ((localDataInf (F := F)).four f)) y =
      (localDataInf (F := F)).γ b * ((localDataInf (F := F)).ψ ((localDataInf (F := F)).cW b * y ^ 2) : ℂ) *
        (localDataInf (F := F)).four ((localDataInf (F := F)).chirp ((localDataInf (F := F)).cW b) f)
          (2 * (localDataInf (F := F)).cW b * y) := by
  set c : V∞ := (((localDataInf (F := F)).cW b : (V∞)ˣ) : V∞) with hc
  set μ := selfDualInf (F := F)
  have hΦ := fourierInf_mem_schwartzInf hf
  set Φ := fourierInf f with hΦdef
  have hΦi : Integrable Φ μ := integrable_of_mem_schwartzInf hΦ
  have hΦc : Continuous Φ := continuous_of_mem_schwartzInf hΦ
  have hfi : Integrable f μ := integrable_of_mem_schwartzInf hf
  have hfc : Continuous f := continuous_of_mem_schwartzInf hf
  -- the two sides as integrals
  have hL : (localDataInf (F := F)).four ((localDataInf (F := F)).chirp b ((localDataInf (F := F)).four f)) y =
      ∫ x, (psiInf ((b : V∞) * x * x) : ℂ) * Φ x * psiInf (x * y) ∂μ := by
    show ∫ x, (psiInf ((b : V∞) * x ^ 2) : ℂ) * fourierInf f x * psiInf (x * y) ∂μ = _
    simp only [sq, mul_assoc]
    rfl
  have hR : (localDataInf (F := F)).γ b * ((localDataInf (F := F)).ψ (c * y ^ 2) : ℂ) *
      (localDataInf (F := F)).four ((localDataInf (F := F)).chirp c f) (2 * c * y) =
      ∫ z, f z * (weilInf (b : V∞) * psiInf (c * (z + y) * (z + y))) ∂μ := by
    show weilInf (b : V∞) * (psiInf (c * y ^ 2) : ℂ) *
      ∫ z, (psiInf (c * z ^ 2) : ℂ) * f z * psiInf (z * (2 * c * y)) ∂μ = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [show c * (z + y) * (z + y) = c * z ^ 2 + (c * y ^ 2 + z * (2 * c * y)) by ring, psiInf_add',
      psiInf_add']
    ring
  rw [hL, hR]
  -- Step 1: regularization
  set I : ℝ → ℂ := fun ε => ∫ x, regInf ε x * ((psiInf ((b : V∞) * x * x) : ℂ) * Φ x * psiInf (x * y)) ∂μ
  have h1 : Tendsto I (𝓝[>] 0) (𝓝 (∫ x, (psiInf ((b : V∞) * x * x) : ℂ) * Φ x * psiInf (x * y) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖Φ x‖) ?_ ?_ hΦi.norm ?_
    · exact Eventually.of_forall fun ε => ((continuous_regInf ε).mul
        (((continuous_psiInf_comp (by fun_prop)).mul hΦc).mul (continuous_psiInf_comp (by fun_prop)))).aestronglyMeasurable
    · refine eventually_nhdsWithin_of_forall fun ε hε => Eventually.of_forall fun x => ?_
      rw [norm_mul, norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul, mul_one]
      calc ‖regInf ε x‖ * ‖Φ x‖ ≤ 1 * ‖Φ x‖ := by
            gcongr; exact norm_regInf_le (le_of_lt hε) x
        _ = _ := one_mul _
    · refine Eventually.of_forall fun x => ?_
      simpa using (tendsto_regInf x).mul_const ((psiInf ((b : V∞) * x * x) : ℂ) * Φ x * psiInf (x * y))
  -- Step 2: Fubini
  set J : ℝ → ℂ := fun ε => ∫ z, f z * kerInf ε (b : V∞) (z + y) ∂μ
  have h2 : ∀ ε, 0 < ε → I ε = J ε := by
    intro ε hε
    have hreg : Integrable (regInf (F := F) ε) μ := integrable_of_mem_schwartzInf (regInf_mem_schwartzInf hε)
    set H : V∞ → V∞ → ℂ := fun x z =>
      regInf ε x * (psiInf ((b : V∞) * x * x) : ℂ) * (f z * psiInf (z * x)) * psiInf (x * y)
    have hHc : Continuous (Function.uncurry H) := by
      simp only [H]
      exact ((((continuous_regInf ε).comp continuous_fst).mul (continuous_psiInf_comp (by fun_prop))).mul
        ((hfc.comp continuous_snd).mul (continuous_psiInf_comp (by fun_prop)))).mul
          (continuous_psiInf_comp (by fun_prop))
    have hHi : Integrable (Function.uncurry H) (μ.prod μ) := by
      refine (hreg.norm.mul_prod hfi.norm).mono' hHc.aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      simp only [H, Function.uncurry, norm_mul, Circle.norm_coe, mul_one]
      rfl
    have e1 : I ε = ∫ x, ∫ z, H x z ∂μ ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [H, Φ, fourierInf]
      calc regInf ε x * ((psiInf ((b : V∞) * x * x) : ℂ) * (∫ z, f z * (psiInf (z * x) : ℂ) ∂selfDualInf) *
            psiInf (x * y)) = (regInf ε x * (psiInf ((b : V∞) * x * x) : ℂ)) *
            (∫ z, f z * (psiInf (z * x) : ℂ) ∂selfDualInf) * psiInf (x * y) := by ring
        _ = _ := by rw [← integral_const_mul, ← integral_mul_const]
    have e2 : ∀ z, ∫ x, H x z ∂μ = f z * kerInf ε (b : V∞) (z + y) := by
      intro z
      simp only [H, kerInf, fourierInf]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [show x * (z + y) = z * x + x * y by ring, psiInf_add']
      ring
    haveI : SFinite μ := by show SFinite selfDualInf; unfold selfDualInf; infer_instance
    rw [e1, integral_integral_swap hHi]
    exact integral_congr_ae (Eventually.of_forall e2)
  -- Step 3: the limit of the kernel
  have h3 : Tendsto J (𝓝[>] 0) (𝓝 (∫ z, f z * (weilInf (b : V∞) * psiInf (c * (z + y) * (z + y))) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => kerBound (b : V∞) * ‖f z‖) ?_ ?_
      (hfi.norm.const_mul _) ?_
    · exact eventually_nhdsWithin_of_forall fun ε hε =>
        (hfc.mul ((continuous_kerInf hε b).comp (continuous_id.add continuous_const))).aestronglyMeasurable
    · refine eventually_nhdsWithin_of_forall fun ε hε => Eventually.of_forall fun z => ?_
      rw [norm_mul, mul_comm]
      gcongr
      exact norm_kerInf_le hε b _
    · exact Eventually.of_forall fun z => (tendsto_kerInf b (z + y)).const_mul (f z)
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsGT_neBot 0
  have h12 : Tendsto J (𝓝[>] 0) (𝓝 (∫ x, (psiInf ((b : V∞) * x * x) : ℂ) * Φ x * psiInf (x * y) ∂μ)) :=
    h1.congr' (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun ε (hε : ε ∈ Set.Ioi (0 : ℝ)) =>
      h2 ε hε)
  exact tendsto_nhds_unique h12 h3

/-! ### The archimedean model -/

/-- **All axioms of the local model hold at the infinite places**: Fourier inversion
(`fourierInf_fourierInf`), dilation (`fourierInf_dil`), the Weil identity for every Schwartz function
(`weilInf_identity_schwartz`), (S) `weilInf_mul_sq`, (H) `weilInf_mul`, and $S \ne 0$. -/
@[kb "weil1964" "§14, §26 (the archimedean places) [unverified]"]
theorem isModel_inf : (localDataInf (F := F)).IsModel where
  toIsOps := isOps_inf
  inversion f hf x := fourierInf_fourierInf hf x
  four_dil f hf t y := fourierInf_dil hf t y
  weil f hf b y := weilInf_identity_schwartz hf b y
  γ_sq t s := weilInf_mul_sq t s
  weil_hilb s t := weilInf_mul s t
  nontrivial := ⟨gaussInfFun, gaussInfFun_mem, fun h => by
    have := congrFun h 0
    simp [gaussInfFun, gaussR, gaussC] at this⟩

/-- **The Weil representation at the infinite places**: for $V_\infty = \langle a_0, \dots, a_{2m-1}\rangle$ over
$F_\infty$ and every field $k$ with a ring map $\iota : k \to F_\infty$ (e.g. $k = F$),
$$\omega_\infty : \mathrm{SL}_2(k) \to \operatorname{End}_{\mathbb C}S(V_\infty),$$
a monoid homomorphism with the Schrödinger-model formulas on $n(b)$, $m(t)$, $w$; $S(V_\infty)$ is the span of pure tensors
of Schwartz functions. -/
@[kb "weil1964" "§14, Thm. 2 (the archimedean Weil representation, $n$ even) [unverified]"]
def weilRepInf {m : ℕ} (a : Fin (2 * m) → (mixedSpace F)ˣ) {k : Type*} [Field k] (ι : k →+* mixedSpace F) :
    SL(2, k) →* Module.End ℂ ((localDataInf (F := F)).Sn (2 * m)) :=
  (localDataInf (F := F)).weilRep isModel_inf (a := a) ι

/-- **Compatibility at infinity:** for $\gamma \in \mathrm{SL}_2(F)$ and $\Phi_\infty \in S(V_\infty)$, the archimedean component of
$\omega(\gamma)\Phi$ (the cell formula, `omegaG`) is $\omega_\infty(\gamma)\Phi_\infty$ for the representation `weilRepInf` with
$\iota = $ `mixedEmbedding F`. So the archimedean action used in `thetaDist_omegaG` and in the theta law is multiplicative. -/
@[kb "weil1964" "§14, §29 [unverified]"]
theorem omegaG_inf_eq_weilRepInf {m : ℕ} (a : Fin (2 * m) → Fˣ) (γ : SL(2, F)) {Φ : GDatum F (2 * m)}
    (hΦ : Φ.inf ∈ (localDataInf (F := F)).Sn (2 * m)) :
    (omegaG a γ Φ).inf = (weilRepInf (aInf a) (mixedEmbedding F) γ ⟨Φ.inf, hΦ⟩ :
      (Fin (2 * m) → mixedSpace F) → ℂ) := by
  unfold omegaG weilRepInf LocalData.weilRep
  rw [cellHom_apply]
  by_cases hc : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · rw [cellRep_of_c_eq_zero hc, cellRep_of_c_eq_zero hc, Aof_of_ne (a_ne_zero_of_c_eq_zero hc),
      Aof_of_ne (a_ne_zero_of_c_eq_zero hc)]
    rfl
  · rw [cellRep_of_c_ne_zero hc, cellRep_of_c_ne_zero hc, Aof_of_ne (unit_ne_zero_aux hc),
      Aof_of_ne (unit_ne_zero_aux hc)]
    rfl

end Main

end QuadFormsKB.WeilRep
