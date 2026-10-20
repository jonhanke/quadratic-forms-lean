import QuadFormsKB.Analysis.AdelicPoisson

/-!
# The Weil index at the infinite places

At a real place ($\psi(x) = e(x)$, Lebesgue measure) and at a complex place ($\psi(z) = e(2\operatorname{Re} z)$,
measure $2\,dx\,dy$), with the self-dual Gaussians $e^{-\pi x^2}$ and $e^{-2\pi|z|^2}$, the chirped Gaussians have
explicit Fourier transforms, and the **Weil identity**
$$\mathcal F\big(\psi(bx^2)\,\mathcal F\varphi\big)(y) = \gamma(b)\,\psi(cy^2)\,\mathcal F\big(\varphi\,\psi(cx^2)\big)(2cy),
\qquad c = -\tfrac1{4b},$$
holds with
$$\gamma_{\mathbb R}(b) = \Big(\frac{i}{2b}\Big)^{1/2} = \frac{e^{\pi i\operatorname{sgn}(b)/4}}{\sqrt{2|b|}}, \qquad
\gamma_{\mathbb C}(b) = \frac1{2|b|}$$
(`weilR_identity`, `weilC_identity`). On $F_\infty = \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ these combine to
`weilInf_identity` for the product Gaussian `gaussInf` (a Schwartz function, self-dual: `fourierInf_gaussInf`).

Sources: Weil, Acta Math. 111 (1964), §14 and §26 [unverified]; Rao (1993) [unverified].
-/

open MeasureTheory Complex NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Real FourierTransform

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

/-! ### Powers -/

/-- $(uw)^s = u^s w^s$ if $\operatorname{Re} u \ge 0$ and $\operatorname{Re} w > 0$ (the arguments add up inside
$(-\pi, \pi)$). -/
lemma cpow_mul_of_re {u w : ℂ} (hu : 0 ≤ u.re) (hu0 : u ≠ 0) (hw : 0 < w.re) (s : ℂ) :
    (u * w) ^ s = u ^ s * w ^ s := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1 := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hu)
  have h2 := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  rw [cpow_def_of_ne_zero (mul_ne_zero hu0 hw0), cpow_def_of_ne_zero hu0, cpow_def_of_ne_zero hw0,
    ← Complex.exp_add, Complex.log_mul hu0 hw0 ⟨by linarith, by linarith⟩, add_mul]

lemma fourierChar_coe (t : ℝ) : ((𝐞 t : Circle) : ℂ) = cexp (2 * π * I * t) := by
  rw [Real.fourierChar_apply]; push_cast; ring_nf

lemma fourierChar_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    𝐞 (∑ i ∈ s, f i) = ∏ i ∈ s, 𝐞 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-! ### The real place -/

/-- **Fourier transform of a complex Gaussian at a real place:** for $\operatorname{Re}\gamma > 0$,
$\int e^{-\pi\gamma x^2}e(x\eta)\,dx = (\gamma^{-1})^{1/2}e^{-\pi\eta^2/\gamma}$. -/
lemma fourierR_cexp_sq (γ : ℂ) (hγ : 0 < γ.re) (η : ℝ) :
    fourierR (fun x : ℝ => cexp (-(π * γ) * (x : ℂ) ^ 2)) η =
      γ⁻¹ ^ (1 / 2 : ℂ) * cexp (-π * (η : ℂ) ^ 2 / γ) := by
  have hb : 0 < ((π : ℂ) * γ).re := by
    rw [show ((π : ℂ) * γ).re = π * γ.re by simp]; exact mul_pos Real.pi_pos hγ
  have hf : (fun x : ℝ => cexp (-(π * γ) * (x : ℂ) ^ 2)) =
      (gaussianSchwartz (E := ℝ) ((π : ℂ) * γ) hb : ℝ → ℂ) := by
    ext x
    rw [gaussianSchwartz_apply]
    congr 2
    rw [Real.norm_eq_abs, sq_abs]
    push_cast; ring
  have hγ0 : γ ≠ 0 := fun h => by rw [h] at hγ; simp at hγ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hf, fourierR_gaussianSchwartz]
  congr 1
  · congr 1; field_simp
  · congr 1; field_simp

/-- The self-dual Gaussian at a real place, $e^{-\pi x^2}$. -/
def gaussR (x : ℝ) : ℂ := cexp (-π * (x : ℂ) ^ 2)

/-- The chirp $e(\beta x^2)$ at a real place. -/
def chirpR (β x : ℝ) : ℂ := (𝐞 (β * x ^ 2) : ℂ)

/-- The Fourier transform of the chirped Gaussian $e^{-\pi\gamma x^2}$ at a real place:
$E_{\mathbb R}(\gamma,\eta) = (\gamma^{-1})^{1/2}e^{-\pi\eta^2/\gamma}$. -/
def gaussFTR (γ : ℂ) (η : ℝ) : ℂ := γ⁻¹ ^ (1 / 2 : ℂ) * cexp (-π * (η : ℂ) ^ 2 / γ)

lemma chirpR_mul_gaussR (β x : ℝ) :
    chirpR β x * gaussR x = cexp (-(π * (1 - 2 * I * β)) * (x : ℂ) ^ 2) := by
  rw [chirpR, gaussR, fourierChar_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma gaussR_mul_chirpR (β x : ℝ) :
    gaussR x * chirpR β x = cexp (-(π * (1 - 2 * I * β)) * (x : ℂ) ^ 2) := by
  rw [mul_comm, chirpR_mul_gaussR]

lemma re_one_sub_two_I_mul (β : ℝ) : (1 - 2 * I * (β : ℂ)).re = 1 := by simp

/-- **Fourier transform of a chirped Gaussian at a real place.** -/
lemma fourierR_chirpR_gaussR (β η : ℝ) :
    fourierR (fun x => chirpR β x * gaussR x) η = gaussFTR (1 - 2 * I * β) η := by
  simp_rw [chirpR_mul_gaussR]
  exact fourierR_cexp_sq _ (by rw [re_one_sub_two_I_mul]; exact one_pos) η

/-- **$e^{-\pi x^2}$ is self-dual at a real place.** -/
lemma fourierR_gaussR : fourierR gaussR = gaussR := by
  ext η
  have := fourierR_chirpR_gaussR 0 η
  simp only [chirpR, zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, one_mul] at this
  rw [this, gaussFTR, gaussR]
  simp

/-- **The Weil constant at a real place:** $\gamma_{\mathbb R}(b) = (i/(2b))^{1/2}$ (principal branch), i.e.
$e^{\pi i/4}(2b)^{-1/2}$ for $b > 0$ and $e^{-\pi i/4}(2|b|)^{-1/2}$ for $b < 0$. -/
@[kb "weil1964" "§26 (the index at a real place) [unverified]"]
def weilR (b : ℝ) : ℂ := (I / (2 * b)) ^ (1 / 2 : ℂ)

/-- **The Weil identity at a real place** (for the Gaussian $\varphi(x) = e^{-\pi x^2}$): with $c = -1/(4b)$,
$$\mathcal F\big(e(bx^2)\,\hat\varphi\big)(y) = \gamma_{\mathbb R}(b)\,e(cy^2)\,\mathcal F\big(\varphi\,e(cx^2)\big)(2cy).$$ -/
@[kb "weil1964" "§14, Thm. 2, at a real place [unverified]"]
theorem weilR_identity {b : ℝ} (hb : b ≠ 0) (y : ℝ) :
    fourierR (fun x => chirpR b x * fourierR gaussR x) y =
      weilR b * (𝐞 (-(4 * b)⁻¹ * y ^ 2) : ℂ) *
        fourierR (fun x => gaussR x * chirpR (-(4 * b)⁻¹) x) (2 * (-(4 * b)⁻¹) * y) := by
  rw [fourierR_gaussR, fourierR_chirpR_gaussR]
  simp_rw [gaussR_mul_chirpR]
  rw [fourierR_cexp_sq _ (by rw [re_one_sub_two_I_mul]; exact one_pos)]
  set c : ℝ := -(4 * b)⁻¹ with hc
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  set u : ℂ := I / (2 * b) with hu
  set w : ℂ := 1 - 2 * I * b with hw
  have hw0 : w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hw] at this
  have hu0 : u ≠ 0 := div_ne_zero I_ne_zero (mul_ne_zero two_ne_zero hb')
  have hure : u⁻¹.re = 0 := by
    rw [hu, inv_div]
    simp
  have hwre : 0 < w⁻¹.re := by
    rw [Complex.inv_re]
    have : w.re = 1 := by simp [hw]
    rw [this]
    exact div_pos one_pos (Complex.normSq_pos.mpr hw0)
  have hkey : (1 - 2 * I * (c : ℂ)) = u * w := by
    rw [hc, hu, hw]; push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have huarg : u.arg ≠ π := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    have hre : u.re = 0 := by rw [hu]; simp [Complex.div_re]
    linarith [this.1]
  rw [gaussFTR, hkey, mul_inv, cpow_mul_of_re (hure.symm ▸ le_rfl) (inv_ne_zero hu0) hwre,
    Complex.inv_cpow _ _ huarg]
  have hsq : u ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hu0 h.1
  rw [weilR, ← hu]
  rw [show u ^ (1 / 2 : ℂ) * ((𝐞 (c * y ^ 2) : Circle) : ℂ) *
      ((u ^ (1 / 2 : ℂ))⁻¹ * w⁻¹ ^ (1 / 2 : ℂ) * cexp (-π * ((2 * c * y : ℝ) : ℂ) ^ 2 / (u * w))) =
      w⁻¹ ^ (1 / 2 : ℂ) * (((𝐞 (c * y ^ 2) : Circle) : ℂ) *
        cexp (-π * ((2 * c * y : ℝ) : ℂ) ^ 2 / (u * w))) by field_simp]
  congr 1
  rw [fourierChar_coe, ← Complex.exp_add]
  congr 1
  have hw1 : (1 - 2 * I * (b : ℂ)) ≠ 0 := hw0
  rw [hu, hw, hc]
  push_cast
  field_simp
  ring_nf
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  simp only [hI3, I_sq]
  ring

/-! ### The complex place -/

/-- **The Fourier transform at a complex place:** $\hat g(\eta) = \int_{\mathbb C} g(z)\,e(2\operatorname{Re}(z\eta))\,
2\,dx\,dy$ (character $e\circ\operatorname{Tr}_{\mathbb C/\mathbb R}$, self-dual measure twice Lebesgue). -/
def fourierC (g : ℂ → ℂ) (η : ℂ) : ℂ := 2 * ∫ z, g z * (𝐞 (2 * (z * η).re) : ℂ)

/-- The self-dual Gaussian at a complex place, $e^{-2\pi|z|^2}$. -/
def gaussC (z : ℂ) : ℂ := cexp (-(2 * π) * ((‖z‖ ^ 2 : ℝ) : ℂ))

/-- The chirp $e(2\operatorname{Re}(\beta z^2))$ at a complex place. -/
def chirpC (β z : ℂ) : ℂ := (𝐞 (2 * (β * z ^ 2).re) : ℂ)

/-- The Fourier transform of the chirped Gaussian at a complex place:
$E_{\mathbb C}(\beta, \eta) = (1 + 4|\beta|^2)^{-1/2}\exp\Big(-\pi\,\frac{2|\eta|^2 + 4i\operatorname{Re}(\bar\beta\eta^2)}{1 + 4|\beta|^2}\Big)$. -/
def gaussFTC (β η : ℂ) : ℂ :=
  ((Real.sqrt (1 + 4 * ‖β‖ ^ 2))⁻¹ : ℝ) *
    cexp (-π * (2 * ((‖η‖ ^ 2 : ℝ) : ℂ) + 4 * I * (((starRingEnd ℂ β * η ^ 2).re : ℝ) : ℂ)) /
      (1 + 4 * ((‖β‖ ^ 2 : ℝ) : ℂ)))

lemma integrand_coord (β₀ : ℝ) (η : ℂ) (u v : ℝ) :
    chirpC β₀ (u + v * I) * gaussC (u + v * I) * (𝐞 (2 * ((u + v * I) * η).re) : ℂ) =
      (cexp (-(π * (2 - 4 * I * β₀)) * (u : ℂ) ^ 2) * (psiR (u * (2 * η.re)) : ℂ)) *
        (cexp (-(π * (2 + 4 * I * β₀)) * (v : ℂ) ^ 2) * (psiR (v * (-2 * η.im)) : ℂ)) := by
  simp only [chirpC, gaussC, psiR_apply, fourierChar_coe]
  simp only [← Complex.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, sq]
  push_cast
  ring_nf

/-- **Fourier transform of a chirped Gaussian at a complex place, real chirp parameter.** -/
lemma fourierC_chirp_real (β₀ : ℝ) (η : ℂ) :
    fourierC (fun w => chirpC β₀ w * gaussC w) η =
      ((Real.sqrt (1 + 4 * β₀ ^ 2))⁻¹ : ℝ) *
        cexp (-π * (2 * ((‖η‖ ^ 2 : ℝ) : ℂ) + 4 * I * β₀ * (((η ^ 2).re : ℝ) : ℂ)) /
          (1 + 4 * (β₀ : ℂ) ^ 2)) := by
  unfold fourierC
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  simp only [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
  simp_rw [integrand_coord]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun u : ℝ => cexp (-(π * (2 - 4 * I * β₀)) * (u : ℂ) ^ 2) *
      (psiR (u * (2 * η.re)) : ℂ)) (fun v : ℝ => cexp (-(π * (2 + 4 * I * β₀)) * (v : ℂ) ^ 2) *
      (psiR (v * (-2 * η.im)) : ℂ))]
  have h1 : 0 < (2 - 4 * I * (β₀ : ℂ)).re := by simp
  have h2 : 0 < (2 + 4 * I * (β₀ : ℂ)).re := by simp
  have e1 := fourierR_cexp_sq _ h1 (2 * η.re)
  have e2 := fourierR_cexp_sq _ h2 (-2 * η.im)
  unfold fourierR at e1 e2
  rw [e1, e2]
  set γ₁ : ℂ := 2 - 4 * I * β₀ with hγ₁
  set γ₂ : ℂ := 2 + 4 * I * β₀ with hγ₂
  have hγ₁0 : γ₁ ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hγ₂0 : γ₂ ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hprod : γ₁ * γ₂ = ((4 * (1 + 4 * β₀ ^ 2) : ℝ) : ℂ) := by
    rw [hγ₁, hγ₂]; push_cast; ring_nf; rw [I_sq]; ring
  have hpos : (0 : ℝ) < 1 + 4 * β₀ ^ 2 := by positivity
  have hre1 : 0 ≤ γ₁⁻¹.re := by
    rw [Complex.inv_re]; exact div_nonneg h1.le (Complex.normSq_nonneg _)
  have hre2 : 0 < γ₂⁻¹.re := by
    rw [Complex.inv_re]; exact div_pos h2 (Complex.normSq_pos.mpr hγ₂0)
  have hconst : 2 * (γ₁⁻¹ ^ (1 / 2 : ℂ) * γ₂⁻¹ ^ (1 / 2 : ℂ)) =
      (((Real.sqrt (1 + 4 * β₀ ^ 2))⁻¹ : ℝ) : ℂ) := by
    rw [← cpow_mul_of_re hre1 (inv_ne_zero hγ₁0) hre2, ← mul_inv, hprod, ← Complex.ofReal_inv,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.mpr (by positivity)), ← Real.sqrt_eq_rpow, Real.sqrt_inv,
      Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    push_cast
    have : Real.sqrt (1 + 4 * β₀ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
  rw [show γ₁⁻¹ ^ (1 / 2 : ℂ) * cexp (-↑π * ((2 * η.re : ℝ) : ℂ) ^ 2 / γ₁) *
      (γ₂⁻¹ ^ (1 / 2 : ℂ) * cexp (-↑π * ((-2 * η.im : ℝ) : ℂ) ^ 2 / γ₂)) =
      (γ₁⁻¹ ^ (1 / 2 : ℂ) * γ₂⁻¹ ^ (1 / 2 : ℂ)) *
        cexp (-↑π * ((2 * η.re : ℝ) : ℂ) ^ 2 / γ₁ + -↑π * ((-2 * η.im : ℝ) : ℂ) ^ 2 / γ₂) by
      rw [Complex.exp_add]; ring, ← mul_assoc, hconst]
  congr 2
  have hden : (1 + 4 * (β₀ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sq, Complex.mul_re]
  push_cast
  field_simp
  rw [hγ₁, hγ₂]
  ring_nf
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  simp only [hI3, I_sq]
  ring

/-- **Fourier transform of a chirped Gaussian at a complex place:**
$\mathcal F\big(e(2\operatorname{Re}(\beta z^2))e^{-2\pi|z|^2}\big)(\eta) = E_{\mathbb C}(\beta,\eta)$ (rotate $z$ so that
$\beta$ becomes $|\beta|$, then Fubini in real coordinates). -/
theorem fourierC_chirpC_gaussC (β η : ℂ) :
    fourierC (fun z => chirpC β z * gaussC z) η = gaussFTC β η := by
  -- the rotation `ζ = e^{-i arg(β)/2}`
  set ζ : Circle := Circle.exp (-β.arg / 2) with hζ
  have hζc : (ζ : ℂ) = cexp (((-β.arg / 2 : ℝ) : ℂ) * I) := Circle.coe_exp _
  have hζn : ‖(ζ : ℂ)‖ = 1 := by rw [hζc]; exact Complex.norm_exp_ofReal_mul_I _
  have hζ2 : β * (ζ : ℂ) ^ 2 = ((‖β‖ : ℝ) : ℂ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I β]
    rw [hζc, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    push_cast
    rw [show (β.arg : ℂ) * I + 2 * (-(β.arg : ℂ) / 2 * I) = 0 by ring, Complex.exp_zero, mul_one]
  have hrot : ∫ z, chirpC β z * gaussC z * (𝐞 (2 * (z * η).re) : ℂ) =
      ∫ w, chirpC (‖β‖ : ℝ) w * gaussC w * (𝐞 (2 * (w * ((ζ : ℂ) * η)).re) : ℂ) := by
    rw [← (LinearIsometryEquiv.measurePreserving (rotation ζ)).integral_comp
      (rotation ζ).toHomeomorph.measurableEmbedding]
    congr 1; ext w
    simp only [rotation_apply, chirpC, gaussC, norm_mul, hζn, one_mul]
    rw [mul_pow, ← mul_assoc, hζ2, show (ζ : ℂ) * w * η = w * ((ζ : ℂ) * η) by ring]
  unfold fourierC
  rw [hrot]
  have := fourierC_chirp_real ‖β‖ ((ζ : ℂ) * η)
  unfold fourierC at this
  rw [this, gaussFTC]
  congr 2
  rw [norm_mul, hζn, one_mul]
  -- `|β| Re((ζη)²) = Re(conj β · η²)`
  have hre : ((‖β‖ : ℝ) : ℂ) * ((((ζ : ℂ) * η) ^ 2).re : ℂ) = (((starRingEnd ℂ β * η ^ 2).re : ℝ) : ℂ) := by
    have hconj : (‖β‖ : ℂ) * (ζ : ℂ) ^ 2 = starRingEnd ℂ β := by
      by_cases hβ : β = 0
      · simp [hβ]
      have hβ' : (β : ℂ) ≠ 0 := hβ
      have : (‖β‖ : ℂ) * (ζ : ℂ) ^ 2 * β = starRingEnd ℂ β * β := by
        rw [mul_assoc, mul_comm ((ζ : ℂ) ^ 2), hζ2, Complex.conj_mul']
        push_cast; ring
      exact mul_right_cancel₀ hβ' this
    rw [← Complex.ofReal_mul, ← Complex.re_ofReal_mul, mul_pow, ← mul_assoc, hconj]
  rw [show (4 : ℂ) * I * ((‖β‖ : ℝ) : ℂ) * (((ζ : ℂ) * η) ^ 2).re =
      4 * I * (((‖β‖ : ℝ) : ℂ) * ((((ζ : ℂ) * η) ^ 2).re : ℂ)) by ring, hre]
  push_cast
  ring

/-- **$e^{-2\pi|z|^2}$ is self-dual at a complex place.** -/
lemma fourierC_gaussC : fourierC gaussC = gaussC := by
  ext η
  have := fourierC_chirpC_gaussC 0 η
  simp only [chirpC, zero_mul, Complex.zero_re, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one,
    one_mul] at this
  rw [show (fun z => gaussC z) = gaussC from rfl] at this
  rw [this, gaussFTC, gaussC]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    Real.sqrt_one, inv_one, Complex.ofReal_one, one_mul, map_zero, zero_mul, Complex.zero_re,
    Complex.ofReal_zero, div_one]
  congr 1; push_cast; ring

/-- **The Weil constant at a complex place:** $\gamma_{\mathbb C}(b) = \frac{1}{2|b|}$. -/
@[kb "weil1964" "§26 (the index at a complex place is $1$) [unverified]"]
def weilC (b : ℂ) : ℂ := ((2 * ‖b‖)⁻¹ : ℝ)

lemma re_coe (z : ℂ) : ((z.re : ℝ) : ℂ) = (z + starRingEnd ℂ z) / 2 := Complex.re_eq_add_conj z

lemma normSq_coe (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := by
  rw [Complex.mul_conj, Complex.sq_norm]

lemma normSq_coe' (z : ℂ) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
  rw [← normSq_coe]; push_cast; ring

/-- **The Weil identity at a complex place** (for $\varphi(z) = e^{-2\pi|z|^2}$): with $c = -1/(4b)$,
$$\mathcal F\big(e(2\operatorname{Re}(bz^2))\,\hat\varphi\big)(y) = \gamma_{\mathbb C}(b)\,e(2\operatorname{Re}(cy^2))\,
\mathcal F\big(\varphi\,e(2\operatorname{Re}(cz^2))\big)(2cy).$$ -/
@[kb "weil1964" "§14, Thm. 2, at a complex place [unverified]"]
theorem weilC_identity {b : ℂ} (hb : b ≠ 0) (y : ℂ) :
    fourierC (fun z => chirpC b z * fourierC gaussC z) y =
      weilC b * (𝐞 (2 * (-(4 * b)⁻¹ * y ^ 2).re) : ℂ) *
        fourierC (fun z => gaussC z * chirpC (-(4 * b)⁻¹) z) (2 * (-(4 * b)⁻¹) * y) := by
  rw [fourierC_gaussC, fourierC_chirpC_gaussC]
  simp_rw [mul_comm (gaussC _) (chirpC _ _)]
  rw [fourierC_chirpC_gaussC]
  set c : ℂ := -(4 * b)⁻¹ with hc
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hcn : ‖c‖ = (4 * ‖b‖)⁻¹ := by rw [hc, norm_neg, norm_inv, norm_mul]; norm_num
  unfold gaussFTC weilC
  -- the constants
  have hconst : ((Real.sqrt (1 + 4 * ‖b‖ ^ 2))⁻¹ : ℝ) =
      (2 * ‖b‖)⁻¹ * (Real.sqrt (1 + 4 * ‖c‖ ^ 2))⁻¹ := by
    have hpos : (0 : ℝ) < 1 + 4 * ‖b‖ ^ 2 := by positivity
    have h1 : 1 + 4 * ‖c‖ ^ 2 = (1 + 4 * ‖b‖ ^ 2) / (2 * ‖b‖) ^ 2 := by
      rw [hcn]; field_simp; ring
    rw [h1, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have : Real.sqrt (1 + 4 * ‖b‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
  rw [hconst, fourierChar_coe]
  push_cast
  rw [show ∀ A B E₂ E₃ : ℂ, A * E₂ * (B * E₃) = A * B * (E₂ * E₃) from fun _ _ _ _ => by ring,
    ← Complex.exp_add]
  congr 2
  -- the exponents, via `Re z = (z + z̄)/2` and `|z|² = z z̄`
  have hb' : starRingEnd ℂ b ≠ 0 := (map_ne_zero _).mpr hb
  have hden1 : (1 + 4 * b * starRingEnd ℂ b) ≠ 0 := by
    rw [mul_assoc, ← normSq_coe]; exact_mod_cast (show (0 : ℝ) < 1 + 4 * ‖b‖ ^ 2 by positivity).ne'
  have hcc : starRingEnd ℂ c = -(4 * starRingEnd ℂ b)⁻¹ := by
    rw [hc, map_neg, map_inv₀, map_mul, map_ofNat]
  simp only [normSq_coe', re_coe]
  simp only [map_mul, map_pow, map_ofNat, hcc, Complex.conj_conj, map_inv₀, map_neg, map_one]
  rw [hc]
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hden2 : (1 + starRingEnd ℂ b * b * 4) ≠ 0 := by
    rw [show starRingEnd ℂ b * b * 4 = 4 * b * starRingEnd ℂ b by ring]; exact hden1
  field_simp
  ring_nf
  field_simp
  ring

/-! ### The product over the infinite places -/

section Inf

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

lemma coe_prod_circle {ι : Type*} (s : Finset ι) (f : ι → Circle) :
    ((∏ i ∈ s, f i : Circle) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
  map_prod Circle.coeHom f s

/-- $\psi_\infty(xy)$ as a product over the infinite places. -/
lemma psiInf_mul_eq_prod (x y : V) :
    (psiInf (x * y) : ℂ) = (∏ w, (𝐞 (x.1 w * y.1 w) : ℂ)) * ∏ w, (𝐞 (2 * (x.2 w * y.2 w).re) : ℂ) := by
  rw [psiInf, traceInf, AddChar.map_add_eq_mul, fourierChar_sum, fourierChar_sum, Circle.coe_mul,
    coe_prod_circle, coe_prod_circle]
  rfl

/-- **Fourier transform of a product function on $F_\infty$:** for $f(x) = \prod_{w\ \mathrm{real}} f_w(x_w)\cdot
\prod_{w\ \mathrm{complex}} g_w(x_w)$, $\hat f(y) = \prod_w \hat f_w(y_w)\cdot\prod_w \hat g_w(y_w)$ (`fourierR`, `fourierC`). -/
theorem fourierInf_prod (fr : {w : InfinitePlace F // IsReal w} → ℝ → ℂ)
    (fc : {w : InfinitePlace F // IsComplex w} → ℂ → ℂ) (y : V) :
    fourierInf (fun x => (∏ w, fr w (x.1 w)) * ∏ w, fc w (x.2 w)) y =
      (∏ w, fourierR (fr w) (y.1 w)) * ∏ w, fourierC (fc w) (y.2 w) := by
  unfold fourierInf selfDualInf
  rw [integral_smul_nnreal_measure]
  have hfun : (fun x : V => (∏ w, fr w (x.1 w)) * (∏ w, fc w (x.2 w)) * (psiInf (x * y) : ℂ)) =
      fun x => (∏ w, fr w (x.1 w) * (𝐞 (x.1 w * y.1 w) : ℂ)) *
        ∏ w, fc w (x.2 w) * (𝐞 (2 * (x.2 w * y.2 w).re) : ℂ) := by
    ext x
    rw [psiInf_mul_eq_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  rw [hfun, Measure.volume_eq_prod, integral_prod_mul (fun a : {w : InfinitePlace F // IsReal w} → ℝ =>
      ∏ w, fr w (a w) * (𝐞 (a w * y.1 w) : ℂ)) (fun b : {w : InfinitePlace F // IsComplex w} → ℂ =>
      ∏ w, fc w (b w) * (𝐞 (2 * (b w * y.2 w).re) : ℂ)), volume_pi, volume_pi,
    integral_fintype_prod_eq_prod (fun w (a : ℝ) => fr w a * (𝐞 (a * y.1 w) : ℂ)),
    integral_fintype_prod_eq_prod (fun w (a : ℂ) => fc w a * (𝐞 (2 * (a * y.2 w).re) : ℂ))]
  unfold fourierC fourierR
  simp_rw [psiR_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

/-- **The self-dual Gaussian on $F_\infty$:** $\Phi_\infty(x) = \prod_{w\ \mathrm{real}} e^{-\pi x_w^2}
\prod_{w\ \mathrm{complex}} e^{-2\pi|x_w|^2}$. -/
def gaussInfFun (x : V) : ℂ := (∏ w, gaussR (x.1 w)) * ∏ w, gaussC (x.2 w)

/-- $\hat\Phi_\infty = \Phi_\infty$. -/
theorem fourierInf_gaussInfFun : fourierInf (gaussInfFun (F := F)) = gaussInfFun := by
  ext y
  unfold gaussInfFun
  rw [fourierInf_prod (fun _ => gaussR) (fun _ => gaussC), fourierR_gaussR, fourierC_gaussC]

/-- The chirp $\psi_\infty(bx^2)$ as a product over the places. -/
lemma psiInf_chirp_eq_prod (b x : V) :
    (psiInf (b * x * x) : ℂ) = (∏ w, chirpR (b.1 w) (x.1 w)) * ∏ w, chirpC (b.2 w) (x.2 w) := by
  rw [psiInf_mul_eq_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    simp only [chirpR, Prod.fst_mul, Pi.mul_apply, sq, mul_assoc]
  · refine Finset.prod_congr rfl fun w _ => ?_
    simp only [chirpC, Prod.snd_mul, Pi.mul_apply, sq, mul_assoc]

/-- **The Weil constant at infinity:** $\gamma_\infty(b) = \prod_{w\ \mathrm{real}}\gamma_{\mathbb R}(b_w)
\prod_{w\ \mathrm{complex}}\gamma_{\mathbb C}(b_w)$. -/
@[kb "weil1964" "§26 [unverified]"]
def weilInf (b : V) : ℂ := (∏ w, weilR (b.1 w)) * ∏ w, weilC (b.2 w)

/-- **The Weil identity on $F_\infty$** for the self-dual Gaussian $\Phi_\infty$: with $c = -1/(4b)$ (componentwise,
all $b_w \ne 0$),
$$\mathcal F\big(\psi_\infty(bx^2)\,\hat\Phi_\infty\big)(y) = \gamma_\infty(b)\,\psi_\infty(cy^2)\,
\mathcal F\big(\Phi_\infty\,\psi_\infty(cx^2)\big)(2cy).$$ -/
@[kb "weil1964" "§14, Thm. 2, at the infinite places [unverified]"]
theorem weilInf_identity {b : V} (hb₁ : ∀ w, b.1 w ≠ 0) (hb₂ : ∀ w, b.2 w ≠ 0) (y : V) :
    fourierInf (fun x => (psiInf (b * x * x) : ℂ) * fourierInf gaussInfFun x) y =
      weilInf b * (psiInf (-(4 * b)⁻¹ * y * y) : ℂ) *
        fourierInf (fun x => gaussInfFun x * (psiInf (-(4 * b)⁻¹ * x * x) : ℂ)) (2 * -(4 * b)⁻¹ * y) := by
  rw [fourierInf_gaussInfFun]
  have hL : (fun x : V => (psiInf (b * x * x) : ℂ) * gaussInfFun x) = fun x =>
      (∏ w, chirpR (b.1 w) (x.1 w) * fourierR gaussR (x.1 w)) *
        ∏ w, chirpC (b.2 w) (x.2 w) * fourierC gaussC (x.2 w) := by
    ext x
    rw [psiInf_chirp_eq_prod, gaussInfFun, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      fourierR_gaussR, fourierC_gaussC]
    ring
  have hR : (fun x : V => gaussInfFun x * (psiInf (-(4 * b)⁻¹ * x * x) : ℂ)) = fun x =>
      (∏ w, gaussR (x.1 w) * chirpR (-(4 * b.1 w)⁻¹) (x.1 w)) *
        ∏ w, gaussC (x.2 w) * chirpC (-(4 * b.2 w)⁻¹) (x.2 w) := by
    ext x
    rw [psiInf_chirp_eq_prod, gaussInfFun, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_inv, Prod.snd_inv, Prod.fst_mul, Prod.snd_mul,
      Pi.neg_apply, Pi.inv_apply, Pi.mul_apply, Prod.fst_ofNat, Prod.snd_ofNat, Pi.ofNat_apply]
    ring
  rw [hL, hR, fourierInf_prod (fun w x => chirpR (b.1 w) x * fourierR gaussR x)
      (fun w z => chirpC (b.2 w) z * fourierC gaussC z),
    fourierInf_prod (fun w x => gaussR x * chirpR (-(4 * b.1 w)⁻¹) x)
      (fun w z => gaussC z * chirpC (-(4 * b.2 w)⁻¹) z)]
  simp_rw [weilR_identity (hb₁ _), weilC_identity (hb₂ _)]
  rw [psiInf_mul_eq_prod, weilInf]
  simp only [Finset.prod_mul_distrib, Prod.fst_neg, Prod.snd_neg, Prod.fst_inv, Prod.snd_inv,
    Prod.fst_mul, Prod.snd_mul, Pi.neg_apply, Pi.inv_apply, Pi.mul_apply, Prod.fst_ofNat,
    Prod.snd_ofNat, Pi.ofNat_apply]
  have e1 : ∀ w : {w : InfinitePlace F // IsReal w},
      (𝐞 (-(4 * b.1 w)⁻¹ * y.1 w * y.1 w) : ℂ) = (𝐞 (-(4 * b.1 w)⁻¹ * y.1 w ^ 2) : ℂ) := by
    intro w; rw [sq, ← mul_assoc]
  have e2 : ∀ w : {w : InfinitePlace F // IsComplex w},
      (𝐞 (2 * (-(4 * b.2 w)⁻¹ * y.2 w * y.2 w).re) : ℂ) = (𝐞 (2 * (-(4 * b.2 w)⁻¹ * y.2 w ^ 2).re) : ℂ) := by
    intro w; rw [sq, ← mul_assoc]
  simp_rw [e1, e2]
  ring

/-! ### Schwartz functions on $F_\infty$ -/

/-- The scaling $(x, z) \mapsto (x, \sqrt2 z)$ of $F_\infty$. -/
def scaleSqrtTwo : V ≃ₗ[ℝ] V where
  toFun x := (x.1, Real.sqrt 2 • x.2)
  invFun x := (x.1, (Real.sqrt 2)⁻¹ • x.2)
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' c x := by ext <;> simp [smul_comm c]
  left_inv x := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    ext <;> simp [smul_smul, this]
  right_inv x := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    ext <;> simp [smul_smul, this]

/-- The linear isomorphism $F_\infty \to \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ (Euclidean) with
$\|Tx\|^2 = \sum_{w\ \mathrm{real}}x_w^2 + 2\sum_{w\ \mathrm{complex}}|x_w|^2$. -/
def gaussT : V ≃L[ℝ] euclidean.mixedSpace F :=
  (scaleSqrtTwo (F := F)).toContinuousLinearEquiv.trans (euclidean.toMixed F).symm

lemma norm_gaussT_sq (x : V) :
    ‖gaussT x‖ ^ 2 = (∑ w, (x.1 w) ^ 2) + 2 * ∑ w, ‖x.2 w‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ w, ‖x.1 w‖ ^ 2) + ∑ w, ‖Real.sqrt 2 • x.2 w‖ ^ 2 = _
  congr 1
  · simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [_root_.norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]

/-- **The self-dual Gaussian on $F_\infty$ as a Schwartz function** (`gaussInf_apply`: it is `gaussInfFun`). -/
def gaussInf : SchwartzMap V ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussT (F := F))
    (gaussianSchwartz (π : ℂ) (by simp [Real.pi_pos]))

theorem gaussInf_apply (x : V) : gaussInf x = gaussInfFun x := by
  rw [gaussInf, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    gaussianSchwartz_apply, norm_gaussT_sq, gaussInfFun]
  simp only [gaussR, gaussC]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  push_cast
  rw [mul_add]
  simp only [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun w _ => by ring

/-- **The chirp $x \mapsto \psi_\infty(bx^2)$ has temperate growth.** -/
theorem hasTemperateGrowth_chirpInf (b : V) :
    Function.HasTemperateGrowth fun x : V => (psiInf (b * x * x) : ℂ) := by
  set B : V →L[ℝ] V →L[ℝ] V := (ContinuousLinearMap.mul ℝ V).comp (ContinuousLinearMap.mul ℝ V b)
  have hB : Function.HasTemperateGrowth fun x : V => B x x :=
    B.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id Function.HasTemperateGrowth.id
  set L : V →L[ℝ] ℝ := (2 * π) • LinearMap.toContinuousLinearMap (traceInfL (F := F))
  have hL := L.hasTemperateGrowth.comp hB
  have h := Complex.hasTemperateGrowth_exp_mul_I.comp hL
  convert h using 1
  ext x
  simp only [Function.comp_apply, psiInf, fourierChar_coe, L, B]
  congr 1
  simp [traceInfL]
  ring

/-- **The chirped Gaussian** $x \mapsto \psi_\infty(bx^2)\,\Phi_\infty(x)$ as a Schwartz function. -/
def chirpGauss (b : V) : SchwartzMap V ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : V => (psiInf (b * x * x) : ℂ)) gaussInf

theorem chirpGauss_apply (b x : V) :
    chirpGauss b x = (psiInf (b * x * x) : ℂ) * gaussInfFun x := by
  rw [chirpGauss, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_chirpInf b), gaussInf_apply,
    smul_eq_mul]

end Inf

end

end QuadFormsKB.Analysis
