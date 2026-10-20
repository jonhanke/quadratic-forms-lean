/-
# One-variable Fourier transforms for Hilbert Eisenstein series

For $k \ge 2$, $s \ge 0$ let $\varphi_{k,s}(w) = w^{-k}|w|^{-2s}$ (`phiKS`) and, for $h \ne 0$,
$$T_{k,s}(\xi, h) = \int_{\mathbb{R}}\varphi_{k,s}(u + ih)\,e(-\xi u)\,du\qquad(\texttt{lineFT}),\qquad e(x) = e^{2\pi ix}.$$
These are the one-variable factors of the Fourier transform of $t \mapsto \prod_v\varphi_{k,s}(c_vz_v + t_v)$, which governs the
$q$-expansion of Hilbert Eisenstein series ($s = 0$) and Hecke's trick in weight $2$ ($s \to 0^+$).

* `integral_shift_strip`: **contour shift** across a horizontal strip for holomorphic functions decaying uniformly at
  $\operatorname{Re}w \to \pm\infty$ (from `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).
-/
import Mathlib

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

/-- **Contour shift across a horizontal strip.** If $f$ is holomorphic on $\{a \le \operatorname{Im}w \le b\}$, integrable on the two
boundary lines, and $f(x + ti) \to 0$ as $|x| \to \infty$ uniformly in $t \in [a, b]$, then
$\int_{\mathbb{R}}f(x + ai)\,dx = \int_{\mathbb{R}}f(x + bi)\,dx$. -/
theorem integral_shift_strip {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {w : ℂ | a ≤ w.im ∧ w.im ≤ b})
    (ha : Integrable fun x : ℝ => f (x + a * I)) (hb : Integrable fun x : ℝ => f (x + b * I))
    (hdec : ∀ ε > 0, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → ∀ t ∈ Icc a b, ‖f (x + t * I)‖ ≤ ε) :
    ∫ x : ℝ, f (x + a * I) = ∫ x : ℝ, f (x + b * I) := by
  -- the rectangle identity
  have hrect : ∀ R : ℝ, 0 ≤ R →
      ((∫ x : ℝ in -R..R, f (x + a * I)) - ∫ x : ℝ in -R..R, f (x + b * I)) =
        -(I • (∫ y : ℝ in a..b, f (R + y * I)) - I • ∫ y : ℝ in a..b, f (-R + y * I)) := by
    intro R hR
    have h := integral_boundary_rect_eq_zero_of_differentiableOn f ((-R : ℝ) + a * I) (R + b * I) ?_
    · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add] at h
      push_cast at h
      linear_combination h
    · refine hf.mono fun w hw => ?_
      rw [mem_reProdIm] at hw
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add] at hw
      rw [uIcc_of_le hab] at hw
      exact ⟨hw.2.1, hw.2.2⟩
  -- the vertical sides tend to `0`
  have hV : Tendsto (fun R : ℝ => I • (∫ y : ℝ in a..b, f (R + y * I)) -
      I • ∫ y : ℝ in a..b, f (-R + y * I)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R₀, hR₀⟩ := hdec (ε / (4 * (b - a + 1))) (by positivity)
    filter_upwards [eventually_ge_atTop (max R₀ 0)] with R hR
    rw [dist_zero_right]
    have hb1 : ∀ x : ℝ, R₀ ≤ |x| → ‖∫ y : ℝ in a..b, f (x + y * I)‖ ≤ ε / (4 * (b - a + 1)) * |b - a| := by
      intro x hx
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      rw [uIoc_of_le hab] at hy
      exact hR₀ x hx y ⟨hy.1.le, hy.2⟩
    have hR1 : R₀ ≤ |R| := (le_max_left _ _).trans (hR.trans (le_abs_self R))
    have hR2 : R₀ ≤ |-R| := by rw [abs_neg]; exact hR1
    have e1 := hb1 R hR1
    have e2 := hb1 (-R) hR2
    push_cast at e2
    calc ‖I • (∫ y : ℝ in a..b, f (R + y * I)) - I • ∫ y : ℝ in a..b, f (-R + y * I)‖
        ≤ ‖∫ y : ℝ in a..b, f (R + y * I)‖ + ‖∫ y : ℝ in a..b, f (-R + y * I)‖ := by
          refine (norm_sub_le _ _).trans ?_
          simp [norm_smul]
      _ ≤ 2 * (ε / (4 * (b - a + 1)) * |b - a|) := by linarith
      _ < ε := by
          rw [abs_of_nonneg (sub_nonneg.mpr hab)]
          have : 0 < b - a + 1 := by linarith
          rw [show 2 * (ε / (4 * (b - a + 1)) * (b - a)) = ε * ((b - a) / (2 * (b - a + 1))) by
            field_simp; ring]
          refine mul_lt_of_lt_one_right hε ?_
          rw [div_lt_one (by positivity)]; linarith
  have hlim : Tendsto (fun R : ℝ => (∫ x : ℝ in -R..R, f (x + a * I)) - ∫ x : ℝ in -R..R, f (x + b * I))
      atTop (𝓝 ((∫ x : ℝ, f (x + a * I)) - ∫ x : ℝ, f (x + b * I))) :=
    (intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id)
  have hlim' : Tendsto (fun R : ℝ => (∫ x : ℝ in -R..R, f (x + a * I)) - ∫ x : ℝ in -R..R, f (x + b * I))
      atTop (𝓝 0) := by
    have := hV.neg
    rw [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    exact (hrect R hR).symm
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim hlim')

/-! ### The functions $\varphi_{k,s}$ and $T_{k,s}$ -/

/-- **$\varphi_{k,s}(w) = w^{-k}|w|^{-2s}$** ($\varphi_{k,0}(w) = w^{-k}$; for real $\lambda > 0$, $\varphi_{k,s}(\lambda w) = \lambda^{-k-2s}\varphi_{k,s}(w)$). -/
noncomputable def phiKS (k : ℕ) (s : ℝ) (w : ℂ) : ℂ := (w ^ k)⁻¹ * ((‖w‖ ^ (-2 * s) : ℝ) : ℂ)

/-- **The line Fourier transform** $T_{k,s}(\xi, h) = \int_{\mathbb{R}}\varphi_{k,s}(u + ih)\,e(-\xi u)\,du$. -/
noncomputable def lineFT (k : ℕ) (s ξ h : ℝ) : ℂ :=
  ∫ u : ℝ, phiKS k s (u + h * I) * cexp (-2 * π * I * ξ * u)

@[simp] lemma phiKS_zero (k : ℕ) (w : ℂ) : phiKS k 0 w = (w ^ k)⁻¹ := by simp [phiKS]

lemma norm_phiKS (k : ℕ) (s : ℝ) (w : ℂ) : ‖phiKS k s w‖ = (‖w‖ ^ k)⁻¹ * ‖w‖ ^ (-2 * s) := by
  rw [phiKS, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

lemma norm_add_mul_I_sq (u h : ℝ) : ‖(u : ℂ) + h * I‖ ^ 2 = u ^ 2 + h ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

lemma abs_le_norm_add_mul_I (u h : ℝ) : |h| ≤ ‖(u : ℂ) + h * I‖ := by
  have := Complex.abs_im_le_norm ((u : ℂ) + h * I)
  simpa using this

/-- **A uniform integrable bound**: for $h \ne 0$, $k \ge 2$ and $0 \le s \le 1$,
$|\varphi_{k,s}(u + ih)| \le C_h\,(1 + u^2)^{-1}$ with $C_h = \max(1, |h|^{-2})^3\max(1, |h|^{-k})$. -/
lemma norm_phiKS_le {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {h : ℝ} (hh : h ≠ 0)
    (u : ℝ) :
    ‖phiKS k s (u + h * I)‖ ≤ (max 1 (|h| ^ 2)⁻¹) ^ 3 * max 1 ((|h| ^ k)⁻¹) * (1 + u ^ 2)⁻¹ := by
  set w : ℂ := u + h * I
  have hh0 : 0 < |h| := abs_pos.mpr hh
  have hw : |h| ≤ ‖w‖ := abs_le_norm_add_mul_I u h
  have hw0 : 0 < ‖w‖ := hh0.trans_le hw
  rw [norm_phiKS]
  -- `‖w‖^{-2s} ≤ max 1 (|h|^2)⁻¹`
  have h1 : ‖w‖ ^ (-2 * s) ≤ max 1 (|h| ^ 2)⁻¹ := by
    rcases le_or_gt 1 ‖w‖ with hw1 | hw1
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hw1 (by linarith)).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      calc ‖w‖ ^ (-2 * s) ≤ |h| ^ (-2 * s) :=
            Real.rpow_le_rpow_of_nonpos hh0 hw (by linarith)
        _ ≤ |h| ^ (-2 : ℝ) := by
            have hh1 : |h| < 1 := hw.trans_lt hw1
            exact Real.rpow_le_rpow_of_exponent_ge hh0 hh1.le (by linarith)
        _ = (|h| ^ 2)⁻¹ := by rw [Real.rpow_neg hh0.le]; norm_cast
  -- `(‖w‖^k)⁻¹ ≤ max 1 (|h|^k)⁻¹ * (‖w‖^2)⁻¹ * max 1 ...`
  have h2 : (‖w‖ ^ k)⁻¹ ≤ max 1 ((|h| ^ k)⁻¹) * (‖w‖ ^ 2)⁻¹ * (max 1 (|h| ^ 2)⁻¹) := by
    have hsplit : (‖w‖ ^ k)⁻¹ = (‖w‖ ^ (k - 2))⁻¹ * (‖w‖ ^ 2)⁻¹ := by
      rw [← mul_inv, ← pow_add, Nat.sub_add_cancel hk]
    rw [hsplit]
    have h3 : (‖w‖ ^ (k - 2))⁻¹ ≤ max 1 ((|h| ^ k)⁻¹) * max 1 (|h| ^ 2)⁻¹ := by
      rcases le_or_gt 1 ‖w‖ with hw1 | hw1
      · have : (‖w‖ ^ (k - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hw1)
        exact this.trans (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
      · have hh1 : |h| < 1 := hw.trans_lt hw1
        calc (‖w‖ ^ (k - 2))⁻¹ ≤ (|h| ^ (k - 2))⁻¹ :=
              inv_anti₀ (pow_pos hh0 _) (pow_le_pow_left₀ hh0.le hw _)
          _ = (|h| ^ k)⁻¹ * |h| ^ 2 := by
              rw [show k = (k - 2) + 2 from (Nat.sub_add_cancel hk).symm, pow_add]
              field_simp
              rw [Nat.sub_add_cancel hk]
          _ ≤ (|h| ^ k)⁻¹ * 1 := by
              gcongr
              exact pow_le_one₀ hh0.le hh1.le
          _ ≤ max 1 ((|h| ^ k)⁻¹) * max 1 (|h| ^ 2)⁻¹ := by
              rw [mul_one]
              exact (le_max_right _ _).trans (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
    calc (‖w‖ ^ (k - 2))⁻¹ * (‖w‖ ^ 2)⁻¹ ≤ (max 1 ((|h| ^ k)⁻¹) * max 1 (|h| ^ 2)⁻¹) * (‖w‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := by ring
  -- `(‖w‖^2)⁻¹ ≤ max 1 (|h|^2)⁻¹ * (1 + u^2)⁻¹`
  have h4 : (‖w‖ ^ 2)⁻¹ ≤ max 1 (|h| ^ 2)⁻¹ * (1 + u ^ 2)⁻¹ := by
    rw [norm_add_mul_I_sq]
    rw [← sq_abs h]
    have hpos : 0 < u ^ 2 + |h| ^ 2 := by positivity
    rw [inv_le_iff_one_le_mul₀ hpos]
    rcases le_or_gt 1 (|h| ^ 2) with hh1 | hh1
    · have : max 1 (|h| ^ 2)⁻¹ = 1 := max_eq_left (inv_le_one_of_one_le₀ hh1)
      rw [this, one_mul, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]; nlinarith
    · have : max 1 (|h| ^ 2)⁻¹ = (|h| ^ 2)⁻¹ := max_eq_right (one_le_inv₀ (by positivity) |>.mpr hh1.le)
      rw [this, ← mul_inv, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg u, sq_nonneg h]
  calc (‖w‖ ^ k)⁻¹ * ‖w‖ ^ (-2 * s)
      ≤ (max 1 ((|h| ^ k)⁻¹) * (‖w‖ ^ 2)⁻¹ * (max 1 (|h| ^ 2)⁻¹)) * max 1 (|h| ^ 2)⁻¹ :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ ≤ (max 1 ((|h| ^ k)⁻¹) * (max 1 (|h| ^ 2)⁻¹ * (1 + u ^ 2)⁻¹) * (max 1 (|h| ^ 2)⁻¹)) *
          max 1 (|h| ^ 2)⁻¹ := by gcongr
    _ = _ := by ring

lemma continuous_phiKS_line (k : ℕ) (s : ℝ) {h : ℝ} (hh : h ≠ 0) :
    Continuous fun u : ℝ => phiKS k s (u + h * I) := by
  have hne : ∀ u : ℝ, (u : ℂ) + h * I ≠ 0 := fun u h0 => by
    have := congrArg Complex.im h0; simp at this; exact hh this
  unfold phiKS
  refine Continuous.mul ?_ ?_
  · exact (continuous_ofReal.add continuous_const).pow k |>.inv₀ fun u => pow_ne_zero _ (hne u)
  · refine continuous_ofReal.comp ?_
    exact ((continuous_ofReal.add continuous_const).norm).rpow_const fun u =>
      Or.inl (norm_ne_zero_iff.mpr (hne u))

lemma integrable_phiKS_line {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {h : ℝ}
    (hh : h ≠ 0) (ξ : ℝ) :
    Integrable fun u : ℝ => phiKS k s (u + h * I) * cexp (-2 * π * I * ξ * u) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul
    ((max 1 (|h| ^ 2)⁻¹) ^ 3 * max 1 ((|h| ^ k)⁻¹))) ?_ (Eventually.of_forall fun u => ?_)
  · exact ((continuous_phiKS_line k s hh).mul (by fun_prop)).aestronglyMeasurable
  · rw [norm_mul, show -2 * π * I * ξ * u = ((-2 * π * ξ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact norm_phiKS_le hk hs0 hs1 hh u

/-! ### Exponential decay of $T_{k,s}(\xi, 1)$, uniformly in $s \in [0,1]$ -/

/-- The holomorphic continuation of $u \mapsto \varphi_{k,s}(u + i)e(-\xi u)$ to the strip $|\operatorname{Im}w| \le \frac12$:
$G(w) = (w + i)^{-k}(w^2 + 1)^{-s}e(-\xi w)$ (principal branch; $\operatorname{Re}(w^2 + 1) \ge \frac34$ there). -/
noncomputable def contG (k : ℕ) (s ξ : ℝ) (w : ℂ) : ℂ :=
  ((w + I) ^ k)⁻¹ * (w ^ 2 + 1) ^ ((-s : ℝ) : ℂ) * cexp (-2 * π * I * ξ * w)

lemma re_sq_add_one_ge {w : ℂ} (hw : |w.im| ≤ 1 / 2) : 3 / 4 ≤ (w ^ 2 + 1).re := by
  have : (w ^ 2 + 1).re = w.re ^ 2 - w.im ^ 2 + 1 := by simp [sq]
  rw [this]
  have h2 : w.im ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (neg_le_of_abs_le hw) (le_of_abs_le hw); nlinarith [sq_nonneg w.re]
  nlinarith [sq_nonneg w.re]

lemma contG_real (k : ℕ) (s ξ u : ℝ) :
    contG k s ξ u = phiKS k s (u + (1 : ℝ) * I) * cexp (-2 * π * I * ξ * u) := by
  have hsq : (u : ℂ) ^ 2 + 1 = ((u ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
  have hn : ‖(u : ℂ) + I‖ ^ (-2 * s) = (u ^ 2 + 1) ^ (-s) := by
    have h1 : ‖(u : ℂ) + I‖ = Real.sqrt (u ^ 2 + 1) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      congr 1
      have := norm_add_mul_I_sq u 1
      simpa using this
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have key : ((u : ℂ) ^ 2 + 1) ^ ((-s : ℝ) : ℂ) = ((‖(u : ℂ) + I‖ ^ (-2 * s) : ℝ) : ℂ) := by
    rw [hsq, hn, ofReal_cpow (by positivity)]
  simp only [contG, phiKS, ofReal_one, one_mul, key]

lemma contG_differentiableOn (k : ℕ) (s ξ : ℝ) :
    DifferentiableOn ℂ (contG k s ξ) {w : ℂ | |w.im| ≤ 1 / 2} := by
  intro w hw
  have hw' : |w.im| ≤ 1 / 2 := hw
  have hI : w + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
    rw [show w.im = -1 by linarith] at hw'; norm_num at hw'
  have hslit : w ^ 2 + 1 ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (by linarith [re_sq_add_one_ge hw']))
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold contG
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) (by fun_prop)
  · exact ((differentiableAt_id.add_const I).pow k).inv (pow_ne_zero _ hI)
  · exact ((differentiableAt_id.pow 2).add_const 1).cpow_const hslit

/-- $|G(x + it)| \le 2^k\,\frac43\,(1 + x^2)^{-1}e^{2\pi\xi t}$ on the strip, for $k \ge 2$, $0 \le s \le 1$. -/
lemma norm_contG_le {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ξ x t : ℝ)
    (ht : |t| ≤ 1 / 2) :
    ‖contG k s ξ (x + t * I)‖ ≤ 2 ^ k * (4 / 3) * (1 + x ^ 2)⁻¹ * Real.exp (2 * π * ξ * t) := by
  set w : ℂ := x + t * I
  have hwim : w.im = t := by simp [w]
  have hwre : w.re = x := by simp [w]
  rw [contG, norm_mul, norm_mul]
  -- the first factor
  have hb : ‖w + I‖ ^ 2 = x ^ 2 + (t + 1) ^ 2 := by
    rw [show w + I = (x : ℂ) + ((t + 1 : ℝ) : ℂ) * I by simp [w]; ring, norm_add_mul_I_sq]
  have hb2 : (1 + x ^ 2) / 4 ≤ ‖w + I‖ ^ 2 := by
    rw [hb]; have : 1 / 2 ≤ t + 1 := by linarith [neg_abs_le t]
    nlinarith
  have h1 : ‖((w + I) ^ k)⁻¹‖ ≤ 2 ^ k * (1 + x ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    have hhalf : 1 / 2 ≤ ‖w + I‖ := by
      have := Complex.abs_im_le_norm (w + I)
      have him : (w + I).im = t + 1 := by simp [hwim]
      rw [him] at this
      have : 1 / 2 ≤ |t + 1| := by
        rw [abs_of_nonneg (by linarith [neg_abs_le t])]; linarith [neg_abs_le t]
      linarith
    have hpos : 0 < ‖w + I‖ := by linarith
    have hsplit : (‖w + I‖ ^ k)⁻¹ = (‖w + I‖ ^ (k - 2))⁻¹ * (‖w + I‖ ^ 2)⁻¹ := by
      rw [← mul_inv, ← pow_add, Nat.sub_add_cancel hk]
    have e1 : (‖w + I‖ ^ (k - 2))⁻¹ ≤ 2 ^ (k - 2) := by
      calc (‖w + I‖ ^ (k - 2))⁻¹ ≤ ((1 / 2 : ℝ) ^ (k - 2))⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hhalf _)
        _ = 2 ^ (k - 2) := by rw [one_div, inv_pow, inv_inv]
    have e2 : (‖w + I‖ ^ 2)⁻¹ ≤ 4 * (1 + x ^ 2)⁻¹ := by
      rw [show (4 : ℝ) * (1 + x ^ 2)⁻¹ = ((1 + x ^ 2) / 4)⁻¹ by field_simp]
      exact inv_anti₀ (by positivity) hb2
    rw [hsplit]
    calc (‖w + I‖ ^ (k - 2))⁻¹ * (‖w + I‖ ^ 2)⁻¹ ≤ 2 ^ (k - 2) * (4 * (1 + x ^ 2)⁻¹) :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = 2 ^ k * (1 + x ^ 2)⁻¹ := by
          rw [show k = (k - 2) + 2 from (Nat.sub_add_cancel hk).symm, pow_add]
          simp only [Nat.add_sub_cancel]; ring
  -- the second factor
  have h2 : ‖(w ^ 2 + 1) ^ ((-s : ℝ) : ℂ)‖ ≤ 4 / 3 := by
    rw [norm_cpow_real]
    have hre := re_sq_add_one_ge (w := w) (by rw [hwim]; exact ht)
    have hn : 3 / 4 ≤ ‖w ^ 2 + 1‖ := hre.trans (Complex.re_le_norm _)
    calc ‖w ^ 2 + 1‖ ^ (-s) ≤ (3 / 4 : ℝ) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by linarith)
      _ ≤ (3 / 4 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
          (by linarith)
      _ = 4 / 3 := by norm_num [Real.rpow_neg_one]
  -- the exponential
  have h3 : ‖cexp (-2 * π * I * ξ * w)‖ = Real.exp (2 * π * ξ * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [w, mul_re, mul_im]
  rw [h3]
  calc ‖((w + I) ^ k)⁻¹‖ * ‖(w ^ 2 + 1) ^ ((-s : ℝ) : ℂ)‖ * Real.exp (2 * π * ξ * t)
      ≤ (2 ^ k * (1 + x ^ 2)⁻¹) * (4 / 3) * Real.exp (2 * π * ξ * t) := by gcongr
    _ = _ := by ring

lemma continuous_contG_line (k : ℕ) (s ξ : ℝ) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    Continuous fun x : ℝ => contG k s ξ (x + t * I) := by
  have hc : ContinuousOn (contG k s ξ) {w : ℂ | |w.im| ≤ 1 / 2} :=
    (contG_differentiableOn k s ξ).continuousOn
  refine hc.comp_continuous (by fun_prop) fun x => ?_
  show |((x : ℂ) + t * I).im| ≤ 1 / 2
  simpa using ht

lemma integrable_contG_line {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ξ : ℝ)
    {t : ℝ} (ht : |t| ≤ 1 / 2) : Integrable fun x : ℝ => contG k s ξ (x + t * I) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul
    (2 ^ k * (4 / 3) * Real.exp (2 * π * ξ * t))) (continuous_contG_line k s ξ ht).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  refine (norm_contG_le hk hs0 hs1 ξ x t ht).trans (le_of_eq ?_)
  ring

/-- **Exponential decay of $T_{k,s}(\xi, 1)$, uniformly in $s \in [0, 1]$** ($k \ge 2$):
$|T_{k,s}(\xi, 1)| \le 2^k\cdot\frac43\cdot\pi_0\,e^{-\pi|\xi|}$, $\pi_0 = \int_{\mathbb{R}}(1 + u^2)^{-1}du$. *Proof:* shift the line of
integration to $\operatorname{Im}w = -\frac12\operatorname{sgn}\xi$ (`integral_shift_strip`), where $|e(-\xi w)| = e^{-\pi|\xi|}$. -/
theorem norm_lineFT_one_le {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ξ : ℝ) :
    ‖lineFT k s ξ 1‖ ≤ 2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹) * Real.exp (-π * |ξ|) := by
  set η : ℝ := if 0 ≤ ξ then -1 / 2 else 1 / 2 with hη
  have hηabs : |η| ≤ 1 / 2 := by simp only [hη]; split_ifs <;> norm_num [abs_div]
  have hξη : 2 * π * ξ * η = -π * |ξ| := by
    simp only [hη]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have h0 : lineFT k s ξ 1 = ∫ x : ℝ, contG k s ξ (x + (0 : ℝ) * I) := by
    rw [lineFT]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ofReal_zero, zero_mul, add_zero]
    exact (contG_real k s ξ u).symm
  have hshift : ∫ x : ℝ, contG k s ξ (x + (0 : ℝ) * I) = ∫ x : ℝ, contG k s ξ (x + η * I) := by
    have hdec : ∀ ε > 0, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| →
        ∀ t : ℝ, |t| ≤ 1 / 2 → ‖contG k s ξ (x + t * I)‖ ≤ ε := by
      intro ε hε
      set C := 2 ^ k * (4 / 3) * Real.exp (2 * π * |ξ| * (1 / 2))
      have hC : 0 < C := by positivity
      refine ⟨Real.sqrt (C / ε), fun x hx t htabs => ?_⟩
      refine (norm_contG_le hk hs0 hs1 ξ x t htabs).trans ?_
      have hexp : Real.exp (2 * π * ξ * t) ≤ Real.exp (2 * π * |ξ| * (1 / 2)) := by
        rw [Real.exp_le_exp]
        have h2 : ξ * t ≤ |ξ| * |t| := by
          rw [← abs_mul]; exact le_abs_self _
        have h3 : |ξ| * |t| ≤ |ξ| * (1 / 2) := mul_le_mul_of_nonneg_left htabs (abs_nonneg ξ)
        have := mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity : (0 : ℝ) ≤ 2 * π)
        linarith
      have hx2 : C / ε ≤ x ^ 2 := by
        rw [← sq_abs]
        calc C / ε = Real.sqrt (C / ε) ^ 2 := (Real.sq_sqrt (by positivity)).symm
          _ ≤ |x| ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
      calc 2 ^ k * (4 / 3) * (1 + x ^ 2)⁻¹ * Real.exp (2 * π * ξ * t)
          ≤ 2 ^ k * (4 / 3) * (1 + x ^ 2)⁻¹ * Real.exp (2 * π * |ξ| * (1 / 2)) := by gcongr
        _ = C * (1 + x ^ 2)⁻¹ := by ring
        _ ≤ C * (C / ε)⁻¹ := by
            gcongr
            linarith
        _ = ε := by field_simp
    have hdec' : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ∀ ε > 0, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| →
        ∀ t ∈ Icc a b, ‖contG k s ξ (x + t * I)‖ ≤ ε := by
      intro a b ha hb ε hε
      obtain ⟨R, hR⟩ := hdec ε hε
      refine ⟨R, fun x hx t ht => hR x hx t ?_⟩
      rw [abs_le]
      constructor
      · linarith [ht.1, neg_abs_le a, (abs_le.mp ha).1]
      · linarith [ht.2, (abs_le.mp hb).2]
    by_cases h : 0 ≤ ξ
    · have hη' : η = -1 / 2 := by simp [hη, h]
      rw [hη']
      have := integral_shift_strip (f := contG k s ξ) (a := -1 / 2) (b := 0) (by norm_num)
        ((contG_differentiableOn k s ξ).mono fun w hw => by
          show |w.im| ≤ 1 / 2; rw [abs_le]; constructor <;> linarith [hw.1, hw.2])
        (integrable_contG_line hk hs0 hs1 ξ (by norm_num [abs_div]))
        (integrable_contG_line hk hs0 hs1 ξ (by norm_num))
        (hdec' (-1 / 2) 0 (by norm_num [abs_div]) (by norm_num))
      push_cast at this ⊢
      exact this.symm
    · have hη' : η = 1 / 2 := by simp [hη, h]
      rw [hη']
      have := integral_shift_strip (f := contG k s ξ) (a := 0) (b := 1 / 2) (by norm_num)
        ((contG_differentiableOn k s ξ).mono fun w hw => by
          show |w.im| ≤ 1 / 2; rw [abs_le]; constructor <;> linarith [hw.1, hw.2])
        (integrable_contG_line hk hs0 hs1 ξ (by norm_num))
        (integrable_contG_line hk hs0 hs1 ξ (by norm_num [abs_div]))
        (hdec' 0 (1 / 2) (by norm_num) (by norm_num [abs_div]))
      push_cast at this ⊢
      exact this
  rw [h0, hshift]
  calc ‖∫ x : ℝ, contG k s ξ (x + η * I)‖ ≤ ∫ x : ℝ, ‖contG k s ξ (x + η * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, 2 ^ k * (4 / 3) * Real.exp (2 * π * ξ * η) * (1 + x ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_inv_one_add_sq.const_mul _) (Eventually.of_forall fun x => ?_)
        refine (norm_contG_le hk hs0 hs1 ξ x η hηabs).trans (le_of_eq ?_)
        ring
    _ = 2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹) * Real.exp (-π * |ξ|) := by
        rw [MeasureTheory.integral_const_mul, hξη]; ring

/-! ### Scaling, the limit $s \to 0$, and the size of $T_{2,s}(0, 1)$ -/

lemma phiKS_real_mul (k : ℕ) (s : ℝ) {r : ℝ} (hr : r ≠ 0) (w : ℂ) :
    phiKS k s ((r : ℂ) * w) = ((r : ℂ) ^ k)⁻¹ * ((|r| ^ (-2 * s) : ℝ) : ℂ) * phiKS k s w := by
  rw [phiKS, phiKS, mul_pow, mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg r) (norm_nonneg w), ofReal_mul]
  ring

/-- **Scaling**: $T_{k,s}(\xi, h) = |h|\,h^{-k}\,|h|^{-2s}\,T_{k,s}(\xi h, 1)$ for $h \ne 0$ (substitute $u = hu'$). -/
theorem lineFT_scale (k : ℕ) (s ξ : ℝ) {h : ℝ} (hh : h ≠ 0) :
    lineFT k s ξ h = ((|h| : ℝ) : ℂ) * ((h : ℂ) ^ k)⁻¹ * ((|h| ^ (-2 * s) : ℝ) : ℂ) * lineFT k s (ξ * h) 1 := by
  rw [lineFT, lineFT]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => phiKS k s (u + h * I) *
    cexp (-2 * π * I * ξ * u)) h
  have hinv : |h⁻¹| = |h|⁻¹ := abs_inv h
  rw [hinv] at hsub
  have hh' : (0 : ℝ) < |h| := abs_pos.mpr hh
  have : ∫ u : ℝ, phiKS k s (u + h * I) * cexp (-2 * π * I * ξ * u) =
      |h| • ∫ u : ℝ, phiKS k s ((h * u : ℝ) + h * I) * cexp (-2 * π * I * ξ * (h * u : ℝ)) := by
    rw [hsub, smul_smul, mul_inv_cancel₀ hh'.ne', one_smul]
  rw [this, real_smul, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  have e1 : ((h * u : ℝ) : ℂ) + h * I = (h : ℂ) * ((u : ℂ) + ((1 : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [e1, phiKS_real_mul k s hh]
  push_cast
  ring

/-- $|T_{k,s}(\xi, 1)| \le C_k := 8\cdot\max(1, 1)\int(1 + u^2)^{-1}$, uniformly (the crude bound). -/
lemma norm_lineFT_one_le_const {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ξ : ℝ) :
    ‖lineFT k s ξ 1‖ ≤ ∫ u : ℝ, (1 + u ^ 2)⁻¹ := by
  rw [lineFT]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) integrable_inv_one_add_sq
    (Eventually.of_forall fun u => ?_))
  dsimp only
  rw [norm_mul, show -2 * π * I * ξ * u = ((-2 * π * ξ * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  have := norm_phiKS_le hk hs0 hs1 (h := 1) one_ne_zero u
  norm_num at this
  simpa using this

/-- **The limit $s \to 0^+$**: $T_{k,s}(\xi, 1) \to T_{k,0}(\xi, 1)$ (dominated convergence). -/
theorem tendsto_lineFT_zero {k : ℕ} (hk : 2 ≤ k) (ξ : ℝ) :
    Tendsto (fun s => lineFT k s ξ 1) (𝓝[>] 0) (𝓝 (lineFT k 0 ξ 1)) := by
  have hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᵐ u : ℝ,
      ‖phiKS k s (u + (1 : ℝ) * I) * cexp (-2 * π * I * ξ * u)‖ ≤ (1 + u ^ 2)⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    refine Eventually.of_forall fun u => ?_
    rw [norm_mul, show -2 * π * I * ξ * u = ((-2 * π * ξ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have := norm_phiKS_le hk hs.1.le hs.2.le (h := 1) one_ne_zero u
    simpa using this
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ hbound integrable_inv_one_add_sq ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((continuous_phiKS_line k s one_ne_zero).mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    refine Tendsto.mul ?_ tendsto_const_nhds
    unfold phiKS
    refine Tendsto.mul tendsto_const_nhds ?_
    refine (continuous_ofReal.tendsto _).comp ?_
    have hne : ‖(u : ℂ) + ((1 : ℝ) : ℂ) * I‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; intro h; have := congrArg Complex.im h; simp at this
    have : Continuous fun s : ℝ => ‖(u : ℂ) + ((1 : ℝ) : ℂ) * I‖ ^ (-2 * s) :=
      continuous_const.rpow (by fun_prop) fun _ => Or.inl hne
    have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h0

/-! ### $s = 0$: the holomorphic case -/

/-- $w \mapsto (w + i)^{-k}e(-\xi w)$, holomorphic on $\operatorname{Im}w > -1$. -/
noncomputable def contF (k : ℕ) (ξ : ℝ) (w : ℂ) : ℂ := ((w + I) ^ k)⁻¹ * cexp (-2 * π * I * ξ * w)

lemma contF_line (k : ℕ) (ξ x t : ℝ) :
    contF k ξ (x + t * I) = phiKS k 0 (x + ((1 + t : ℝ) : ℂ) * I) * cexp (-2 * π * I * ξ * x) *
      Real.exp (2 * π * ξ * t) := by
  have e1 : (x : ℂ) + t * I + I = x + ((1 + t : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : cexp (-2 * π * I * ξ * (x + t * I)) =
      cexp (-2 * π * I * ξ * x) * ((Real.exp (2 * π * ξ * t) : ℝ) : ℂ) := by
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast; ring_nf; rw [I_sq]; ring
  rw [contF, e1, e2, phiKS_zero]; ring

lemma contF_differentiableOn (k : ℕ) (ξ : ℝ) {a : ℝ} (ha : -1 < a) :
    DifferentiableOn ℂ (contF k ξ) {w : ℂ | a ≤ w.im} := by
  intro w hw
  have hI : w + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
    have : a ≤ w.im := hw; linarith
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold contF
  exact (((differentiableAt_id.add_const I).pow k).inv (pow_ne_zero _ hI)).mul (by fun_prop)

/-- **Vertical shift, $s = 0$**: $T_{k,0}(\xi, 1 + t) = e^{-2\pi\xi t}T_{k,0}(\xi, 1)$ for $t > -1$. -/
theorem lineFT_zero_shift {k : ℕ} (hk : 2 ≤ k) (ξ : ℝ) {t : ℝ} (ht : -1 < t) :
    lineFT k 0 ξ (1 + t) = Real.exp (-2 * π * ξ * t) * lineFT k 0 ξ 1 := by
  have hline : ∀ τ : ℝ, -1 < τ → (fun x : ℝ => contF k ξ (x + τ * I)) =
      fun x : ℝ => phiKS k 0 ((x : ℂ) + ((1 + τ : ℝ) : ℂ) * I) * cexp (-2 * π * I * ξ * x) *
        ((Real.exp (2 * π * ξ * τ) : ℝ) : ℂ) := fun τ _ => funext fun x => contF_line k ξ x τ
  have hint : ∀ τ : ℝ, -1 < τ → Integrable fun x : ℝ => contF k ξ (x + τ * I) := by
    intro τ hτ
    rw [hline τ hτ]
    exact (integrable_phiKS_line hk le_rfl zero_le_one (h := 1 + τ) (by linarith) ξ).mul_const _
  set a := min 0 t
  set b := max 0 t
  have ha : -1 < a := lt_min (by norm_num) ht
  have hab : a ≤ b := min_le_max
  have hshift := integral_shift_strip (f := contF k ξ) hab
    ((contF_differentiableOn k ξ ha).mono fun w hw => hw.1)
    (hint a ha) (hint b (ha.trans_le hab)) ?_
  · have h0 : ∫ x : ℝ, contF k ξ (x + (0 : ℝ) * I) = lineFT k 0 ξ 1 := by
      rw [hline 0 (by norm_num), lineFT]; simp
    have ht' : ∫ x : ℝ, contF k ξ (x + t * I) = Real.exp (2 * π * ξ * t) * lineFT k 0 ξ (1 + t) := by
      rw [hline t ht, lineFT, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only; ring
    have heq : ∫ x : ℝ, contF k ξ (x + (0 : ℝ) * I) = ∫ x : ℝ, contF k ξ (x + t * I) := by
      rcases le_total 0 t with h | h
      · simp only [a, b, min_eq_left h, max_eq_right h] at hshift; exact hshift
      · simp only [a, b, min_eq_right h, max_eq_left h] at hshift; exact hshift.symm
    rw [h0, ht'] at heq
    rw [heq, ← mul_assoc, ← ofReal_mul, ← Real.exp_add, show -2 * π * ξ * t + 2 * π * ξ * t = 0 by ring,
      Real.exp_zero, ofReal_one, one_mul]
  · -- decay
    intro ε hε
    set M := Real.exp (2 * π * |ξ| * max |a| |b|)
    refine ⟨max 1 (M / ε), fun x hx τ hτ => ?_⟩
    have hx1 : 1 ≤ |x| := (le_max_left _ _).trans hx
    have hτ' : -1 < τ := ha.trans_le hτ.1
    rw [contF_line, norm_mul, norm_mul, phiKS_zero, norm_inv, norm_pow,
      show -2 * π * I * ξ * x = ((-2 * π * ξ * x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hxw : |x| ≤ ‖(x : ℂ) + ((1 + τ : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + ((1 + τ : ℝ) : ℂ) * I); simpa using this
    have h1 : (‖(x : ℂ) + ((1 + τ : ℝ) : ℂ) * I‖ ^ k)⁻¹ ≤ |x|⁻¹ := by
      have hx0 : 0 < |x| := by linarith
      calc (‖(x : ℂ) + ((1 + τ : ℝ) : ℂ) * I‖ ^ k)⁻¹ ≤ (|x| ^ k)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hxw k)
        _ ≤ |x|⁻¹ := inv_anti₀ hx0 (le_self_pow₀ hx1 (by omega))
    have h2 : Real.exp (2 * π * ξ * τ) ≤ M := by
      rw [Real.exp_le_exp]
      have hτa : |τ| ≤ max |a| |b| := by
        rw [abs_le]; constructor
        · have := neg_abs_le a; linarith [hτ.1, le_max_left |a| |b|]
        · have := le_abs_self b; linarith [hτ.2, le_max_right |a| |b|]
      have : ξ * τ ≤ |ξ| * max |a| |b| := by
        calc ξ * τ ≤ |ξ * τ| := le_abs_self _
          _ = |ξ| * |τ| := abs_mul _ _
          _ ≤ |ξ| * max |a| |b| := mul_le_mul_of_nonneg_left hτa (abs_nonneg _)
      nlinarith [Real.pi_pos]
    have hM : 0 < M := Real.exp_pos _
    calc (‖(x : ℂ) + ((1 + τ : ℝ) : ℂ) * I‖ ^ k)⁻¹ * Real.exp (2 * π * ξ * τ) ≤ |x|⁻¹ * M :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ (M / ε)⁻¹ * M :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) ((le_max_right _ _).trans hx)) hM.le
      _ = ε := by field_simp

/-- **$T_{k,0}(\xi, 1) = 0$ for $\xi \le 0$** (shift the line up to $+i\infty$). -/
theorem lineFT_zero_of_nonpos {k : ℕ} (hk : 2 ≤ k) {ξ : ℝ} (hξ : ξ ≤ 0) : lineFT k 0 ξ 1 = 0 := by
  -- `T(ξ, 1) = e^{2πξt} T(ξ, 1+t)` and `|T(ξ, 1+t)| ≤ (1+t)^{1-k} C → 0`
  have key : ∀ t : ℝ, 0 < t → ‖lineFT k 0 ξ 1‖ ≤ (1 + t)⁻¹ * ∫ u : ℝ, (1 + u ^ 2)⁻¹ := by
    intro t ht
    have h1 := lineFT_zero_shift hk ξ (t := t) (by linarith)
    have hne : Real.exp (-2 * π * ξ * t) ≠ 0 := (Real.exp_pos _).ne'
    have h2 : lineFT k 0 ξ 1 = Real.exp (2 * π * ξ * t) * lineFT k 0 ξ (1 + t) := by
      rw [h1, ← mul_assoc, ← ofReal_mul, ← Real.exp_add, show 2 * π * ξ * t + -2 * π * ξ * t = 0 by ring,
        Real.exp_zero, ofReal_one, one_mul]
    rw [h2, lineFT_scale k 0 ξ (h := 1 + t) (by linarith), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hexp : Real.exp (2 * π * ξ * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h3 : ξ * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hξ ht.le
      have h4 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 2 * π) h3
      linarith [show 2 * π * ξ * t = 2 * π * (ξ * t) by ring]
    have h1t : 0 < 1 + t := by linarith
    have hpre : ‖((|1 + t| : ℝ) : ℂ) * (((1 + t : ℝ) : ℂ) ^ k)⁻¹ * (((|1 + t| ^ (-2 * (0 : ℝ))) : ℝ) : ℂ)‖ ≤
        (1 + t)⁻¹ := by
      rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (abs_nonneg _), Real.norm_eq_abs, abs_of_pos h1t, mul_zero, Real.rpow_zero,
        norm_one, mul_one]
      rw [show (1 + t) * ((1 + t) ^ k)⁻¹ = ((1 + t) ^ (k - 1))⁻¹ by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
        field_simp
        rw [Nat.sub_add_cancel (by omega)]]
      calc ((1 + t) ^ (k - 1))⁻¹ ≤ ((1 + t) ^ 1)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
        _ = (1 + t)⁻¹ := by rw [pow_one]
    calc Real.exp (2 * π * ξ * t) * ‖((|1 + t| : ℝ) : ℂ) * (((1 + t : ℝ) : ℂ) ^ k)⁻¹ *
          (((|1 + t| ^ (-2 * (0 : ℝ))) : ℝ) : ℂ) * lineFT k 0 (ξ * (1 + t)) 1‖
        ≤ 1 * ((1 + t)⁻¹ * ∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
          refine mul_le_mul hexp ?_ (norm_nonneg _) zero_le_one
          rw [norm_mul]
          exact mul_le_mul hpre (norm_lineFT_one_le_const hk le_rfl zero_le_one _) (norm_nonneg _)
            (by positivity)
      _ = _ := one_mul _
  -- let `t → ∞`
  have hlim : Tendsto (fun t : ℝ => (1 + t)⁻¹ * ∫ u : ℝ, (1 + u ^ 2)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)).mul_const
      (∫ u : ℝ, (1 + u ^ 2)⁻¹)
    simpa using this
  have hle : ‖lineFT k 0 ξ 1‖ ≤ 0 :=
    ge_of_tendsto hlim (by filter_upwards [eventually_gt_atTop 0] with t ht using key t ht)
  exact norm_le_zero_iff.mp hle

/-- **Homogeneity**: $T_{k,0}(\xi, 1) = \xi^{k-1}e^{-2\pi(\xi - 1)}\,T_{k,0}(1, 1)$ for $\xi > 0$. -/
theorem lineFT_zero_homog {k : ℕ} (hk : 2 ≤ k) {ξ : ℝ} (hξ : 0 < ξ) :
    lineFT k 0 ξ 1 = ((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ) : ℂ) * lineFT k 0 1 1 := by
  have h1 := lineFT_scale k 0 1 (h := ξ) hξ.ne'
  have h2 := lineFT_zero_shift hk 1 (t := ξ - 1) (by linarith)
  rw [show (1 : ℝ) + (ξ - 1) = ξ by ring] at h2
  rw [one_mul, mul_zero, Real.rpow_zero, ofReal_one, mul_one, abs_of_pos hξ] at h1
  rw [h2] at h1
  -- `ξ^{1-k} T(ξ,1) = e^{-2π(ξ-1)} T(1,1)`
  have hξk : ((ξ : ℂ) * ((ξ : ℂ) ^ k)⁻¹) * ((ξ : ℂ) ^ (k - 1)) = 1 := by
    have hξ0 : (ξ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hξ.ne'
    rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
    field_simp
    rw [Nat.sub_add_cancel (by omega)]
  calc lineFT k 0 ξ 1 = ((ξ : ℂ) * ((ξ : ℂ) ^ k)⁻¹ * (ξ : ℂ) ^ (k - 1)) * lineFT k 0 ξ 1 := by
        rw [hξk, one_mul]
    _ = (ξ : ℂ) ^ (k - 1) * ((ξ : ℂ) * ((ξ : ℂ) ^ k)⁻¹ * lineFT k 0 ξ 1) := by ring
    _ = (ξ : ℂ) ^ (k - 1) * (((Real.exp (-2 * π * 1 * (ξ - 1)) : ℝ) : ℂ) * lineFT k 0 1 1) := by
        rw [h1]
    _ = _ := by push_cast; ring_nf

lemma lineFT_eq_fourier (k : ℕ) (s ξ h : ℝ) :
    lineFT k s ξ h = 𝓕 (fun u : ℝ => phiKS k s (u + h * I)) ξ := by
  rw [lineFT, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast; ring

/-- **The value $T_{k,0}(1, 1) = \frac{(-2\pi i)^k}{(k-1)!}e^{-2\pi}$** (Fourier inversion at $u = 0$ and $\Gamma(k) = (k-1)!$). -/
theorem lineFT_zero_one_one {k : ℕ} (hk : 2 ≤ k) :
    lineFT k 0 1 1 = (-2 * π * I) ^ k / (k - 1).factorial * Real.exp (-2 * π) := by
  set f : ℝ → ℂ := fun u => phiKS k 0 (u + ((1 : ℝ) : ℂ) * I) with hf
  set L := lineFT k 0 1 1
  have hFf : 𝓕 f = fun ξ => if 0 < ξ then ((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ) : ℂ) * L
      else 0 := by
    funext ξ
    rw [← lineFT_eq_fourier]
    split_ifs with h
    · exact lineFT_zero_homog hk h
    · exact lineFT_zero_of_nonpos hk (not_lt.mp h)
  have hcont : Continuous f := continuous_phiKS_line k 0 one_ne_zero
  have hint : Integrable f := by
    have := integrable_phiKS_line hk le_rfl zero_le_one (h := 1) one_ne_zero 0
    rw [hf]; simpa using this
  -- integrability of `𝓕 f`
  have hgint : IntegrableOn (fun ξ : ℝ => ξ ^ ((k - 1 : ℕ) : ℝ) * Real.exp (-(2 * π) * ξ ^ (1 : ℝ)))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by have h0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) one_pos (by positivity)
  have hFint : Integrable (𝓕 f) := by
    rw [hFf]
    have hset : (fun ξ : ℝ => if 0 < ξ then ((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ) : ℂ) * L
        else 0) = (Ioi (0 : ℝ)).indicator
          (fun ξ => ((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ) : ℂ) * L) := by
      funext ξ; simp [Set.indicator, mem_Ioi]
    rw [hset, integrable_indicator_iff measurableSet_Ioi]
    refine Integrable.mul_const ?_ L
    refine Integrable.ofReal (f := fun ξ : ℝ => ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1))) ?_
    refine IntegrableOn.congr_fun (show IntegrableOn (fun ξ : ℝ => Real.exp (2 * π) *
        (ξ ^ ((k - 1 : ℕ) : ℝ) * Real.exp (-(2 * π) * ξ ^ (1 : ℝ)))) (Ioi 0) volume from
          hgint.const_mul (Real.exp (2 * π))) (fun ξ hξ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, Real.rpow_natCast]
    rw [show -2 * π * (ξ - 1) = -(2 * π) * ξ + 2 * π by ring, Real.exp_add]; ring
  have hinv := congrFun (hcont.fourierInv_fourier_eq hint hFint) 0
  rw [Real.fourierInv_eq] at hinv
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] at hinv
  rw [hFf] at hinv
  -- the left side is a Gamma integral
  have hval : ∫ ξ : ℝ, (if 0 < ξ then ((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ) : ℂ) * L else 0) =
      L * Real.exp (2 * π) * ((((1 / (2 * π)) ^ (k : ℝ) : ℝ) : ℂ) * (k - 1).factorial) := by
    have hset : (fun ξ : ℝ => if 0 < ξ then ((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ) : ℂ) * L
        else 0) = (Ioi (0 : ℝ)).indicator
          (fun ξ => ((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ) : ℂ) * L) := by
      funext ξ; simp [Set.indicator, mem_Ioi]
    rw [hset, integral_indicator measurableSet_Ioi, integral_mul_const]
    have hG := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ)) (r := 2 * π)
      (by exact_mod_cast (show 0 < k by omega)) (by positivity)
    have hfact : Real.Gamma (k : ℝ) = (k - 1).factorial := by
      rw [show (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 by
        rw [Nat.cast_sub (by omega)]; push_cast; ring]
      exact Real.Gamma_nat_eq_factorial (k - 1)
    rw [hfact] at hG
    have hconv : ∫ ξ : ℝ in Ioi 0, (((ξ ^ (k - 1) * Real.exp (-2 * π * (ξ - 1)) : ℝ)) : ℂ) =
        ((Real.exp (2 * π) * ∫ t : ℝ in Ioi 0, t ^ ((k : ℝ) - 1) * Real.exp (-(2 * π * t)) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, ← integral_const_mul]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : 0 < t := ht
      rw [show (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]; push_cast; ring,
        Real.rpow_natCast, show -2 * π * (t - 1) = -(2 * π * t) + 2 * π by ring, Real.exp_add]
      ring
    rw [hconv, hG]
    push_cast
    ring
  rw [hval] at hinv
  -- `f 0 = (i^k)⁻¹`
  have hf0 : f 0 = (I ^ k)⁻¹ := by simp [hf]
  rw [hf0] at hinv
  -- solve for `L`
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hfac : ((k - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hrpow : ((1 / (2 * π)) ^ (k : ℝ) : ℝ) = ((2 * π) ^ k)⁻¹ := by
    rw [Real.rpow_natCast, one_div, inv_pow]
  have hrpowC : (((1 / (2 * π)) ^ (k : ℝ) : ℝ) : ℂ) = ((2 * π : ℂ) ^ k)⁻¹ := by
    rw [hrpow]; push_cast; ring
  rw [hrpowC] at hinv
  have hexp : (Real.exp (2 * π) : ℂ) * (Real.exp (-2 * π) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.exp_add, show 2 * π + -2 * π = 0 by ring, Real.exp_zero, ofReal_one]
  have hI : (I ^ k)⁻¹ * (2 * π : ℂ) ^ k = (-2 * π * I) ^ k := by
    rw [← div_eq_inv_mul, ← div_pow]
    congr 1
    field_simp
    rw [I_sq]; ring
  have hpiC : (2 * π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have h2π : ((2 * π : ℂ) ^ k)⁻¹ * (2 * π : ℂ) ^ k = 1 := inv_mul_cancel₀ (pow_ne_zero _ hpiC)
  have hfac' : ((k - 1).factorial : ℂ) * ((k - 1).factorial : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hfac
  calc L = L * ((Real.exp (2 * π) : ℂ) * (Real.exp (-2 * π) : ℂ)) *
        (((2 * π : ℂ) ^ k)⁻¹ * (2 * π : ℂ) ^ k) * (((k - 1).factorial : ℂ) * ((k - 1).factorial : ℂ)⁻¹) := by
        rw [hexp, h2π, hfac']; ring
    _ = (L * Real.exp (2 * π) * (((2 * π : ℂ) ^ k)⁻¹ * (k - 1).factorial)) * (2 * π : ℂ) ^ k /
        (k - 1).factorial * Real.exp (-2 * π) := by ring
    _ = (I ^ k)⁻¹ * (2 * π : ℂ) ^ k / (k - 1).factorial * Real.exp (-2 * π) := by rw [hinv]
    _ = (-2 * π * I) ^ k / (k - 1).factorial * Real.exp (-2 * π) := by rw [hI]

/-- **The line transforms at $s = 0$**: for $h > 0$,
$T_{k,0}(\xi, h) = \frac{(-2\pi i)^k}{(k-1)!}\,\xi^{k-1}e^{-2\pi\xi h}$ if $\xi > 0$ and $0$ if $\xi \le 0$. -/
theorem lineFT_zero_pos {k : ℕ} (hk : 2 ≤ k) (ξ : ℝ) {h : ℝ} (hh : 0 < h) :
    lineFT k 0 ξ h = if 0 < ξ then (-2 * π * I) ^ k / (k - 1).factorial * ξ ^ (k - 1) *
      Real.exp (-2 * π * ξ * h) else 0 := by
  rw [lineFT_scale k 0 ξ hh.ne', mul_zero, Real.rpow_zero, ofReal_one, mul_one, abs_of_pos hh]
  split_ifs with hξ
  · rw [lineFT_zero_homog hk (mul_pos hξ hh), lineFT_zero_one_one hk]
    have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
    have hk1 : (h : ℂ) * ((h : ℂ) ^ k)⁻¹ * (h : ℂ) ^ (k - 1) = 1 := by
      rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
      field_simp
      rw [Nat.sub_add_cancel (by omega)]
    have e1 : ((Real.exp (-2 * π * (ξ * h - 1)) : ℝ) : ℂ) * ((Real.exp (-2 * π) : ℝ) : ℂ) =
        ((Real.exp (-2 * π * ξ * h) : ℝ) : ℂ) := by
      rw [← ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [ofReal_mul, ofReal_pow, ofReal_mul, mul_pow]
    linear_combination ((-2 * π * I) ^ k / (k - 1).factorial * (ξ : ℂ) ^ (k - 1) *
      ((Real.exp (-2 * π * (ξ * h - 1)) : ℝ) : ℂ) * ((Real.exp (-2 * π) : ℝ) : ℂ)) * hk1 +
      ((-2 * π * I) ^ k / (k - 1).factorial * (ξ : ℂ) ^ (k - 1)) * e1
  · rw [lineFT_zero_of_nonpos hk (by nlinarith [not_lt.mp hξ]), mul_zero]

/-- **The line transforms at $s = 0$, any height $h \ne 0$**:
$T_{k,0}(\xi, h) = \operatorname{sgn}(h)\frac{(-2\pi i)^k}{(k-1)!}\,\xi^{k-1}e^{-2\pi\xi h}$ if $\xi h > 0$, and $0$ otherwise. -/
theorem lineFT_zero_eq {k : ℕ} (hk : 2 ≤ k) (ξ : ℝ) {h : ℝ} (hh : h ≠ 0) :
    lineFT k 0 ξ h = if 0 < ξ * h then ((if 0 < h then 1 else -1 : ℝ) : ℂ) *
      ((-2 * π * I) ^ k / (k - 1).factorial * ξ ^ (k - 1) * Real.exp (-2 * π * ξ * h)) else 0 := by
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · rw [lineFT_scale k 0 ξ hh, mul_zero, Real.rpow_zero, ofReal_one, mul_one,
      lineFT_zero_pos hk (ξ * h) one_pos]
    simp only [hneg.not_gt, ↓reduceIte, mul_one]
    split_ifs with hξ
    · have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh
      have hk1 : (h : ℂ) * ((h : ℂ) ^ k)⁻¹ * (h : ℂ) ^ (k - 1) = 1 := by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
        field_simp
        rw [Nat.sub_add_cancel (by omega)]
      rw [abs_of_neg hneg, show -2 * π * (ξ * h) = -2 * π * ξ * h by ring]
      rw [ofReal_neg, ofReal_mul, mul_pow]
      push_cast [ofReal_neg]
      linear_combination (-((-2 * π * I) ^ k / (k - 1).factorial * (ξ : ℂ) ^ (k - 1) *
        cexp (-2 * π * ξ * h))) * hk1
    · simp
  · rw [lineFT_zero_pos hk ξ hpos]
    by_cases hξ : 0 < ξ
    · simp [hξ, hpos, mul_pos hξ hpos]
    · have : ¬ 0 < ξ * h := fun h' => hξ (pos_of_mul_pos_left h' hpos.le)
      simp [hξ, this]

/-- **$T_{2,s}(0, 1) = O(s)$** as $s \to 0$ (it vanishes at $s = 0$): $|T_{2,s}(0, 1)| \le 4s\int(1 + u^2)^{-3/4}du$ for
$0 \le s \le 1$. This is what kills the non-holomorphic term of Hecke's trick when $d \ge 2$. -/
theorem norm_lineFT_two_zero_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖lineFT 2 s 0 1‖ ≤ s * (4 * ∫ u : ℝ, (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) := by
  have h0 : lineFT 2 0 0 1 = 0 := lineFT_zero_of_nonpos le_rfl le_rfl
  have hdiff : lineFT 2 s 0 1 = ∫ u : ℝ, (phiKS 2 s (u + (1 : ℝ) * I) - phiKS 2 0 (u + (1 : ℝ) * I)) := by
    rw [← sub_zero (lineFT 2 s 0 1), ← h0, lineFT, lineFT, ← integral_sub]
    · simp
    · exact integrable_phiKS_line le_rfl hs0 hs1 one_ne_zero 0
    · exact integrable_phiKS_line le_rfl le_rfl zero_le_one one_ne_zero 0
  have hint : Integrable fun u : ℝ => (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num)
  rw [hdiff]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    ((hint.const_mul 4).const_mul s) (Eventually.of_forall fun u => ?_)
  simp only
  set w : ℂ := u + ((1 : ℝ) : ℂ) * I
  have hw2 : ‖w‖ ^ 2 = 1 + u ^ 2 := by rw [norm_add_mul_I_sq]; ring
  have hw1 : 1 ≤ ‖w‖ := by
    have := abs_le_norm_add_mul_I u 1; simpa [w] using this
  have hw0 : 0 < ‖w‖ := by linarith
  rw [phiKS, phiKS, mul_zero, Real.rpow_zero, ofReal_one, mul_one, ← mul_sub_one, norm_mul, norm_inv,
    norm_pow, show (((‖w‖ ^ (-2 * s)) : ℝ) : ℂ) - 1 = ((‖w‖ ^ (-2 * s) - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  -- `|r^{-2s} - 1| ≤ 2 s log r`
  have hlog : |‖w‖ ^ (-2 * s) - 1| ≤ s * Real.log (1 + u ^ 2) := by
    have hr : ‖w‖ ^ (-2 * s) = Real.exp (-(2 * s * Real.log ‖w‖)) := by
      rw [Real.rpow_def_of_pos hw0]; congr 1; ring
    have hL : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw1
    have hx : 0 ≤ 2 * s * Real.log ‖w‖ := by positivity
    rw [hr, abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)])]
    have := Real.add_one_le_exp (-(2 * s * Real.log ‖w‖))
    have hlog2 : Real.log (1 + u ^ 2) = 2 * Real.log ‖w‖ := by
      rw [← hw2, Real.log_pow]; push_cast; ring
    rw [hlog2]; linarith
  have hlog' : Real.log (1 + u ^ 2) ≤ 4 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div (x := 1 + u ^ 2) (by positivity) (ε := 1 / 4) (by norm_num)
    linarith
  have hnorm : ‖u‖ ^ 2 = u ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hpos : 0 < 1 + u ^ 2 := by positivity
  calc (‖w‖ ^ 2)⁻¹ * |‖w‖ ^ (-2 * s) - 1| ≤ (1 + u ^ 2)⁻¹ * (s * (4 * (1 + u ^ 2) ^ (1 / 4 : ℝ))) := by
        rw [hw2]
        refine mul_le_mul_of_nonneg_left (hlog.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hlog' hs0
    _ = s * (4 * (1 + u ^ 2) ^ (-(3 / 2 : ℝ) / 2)) := by
        rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hpos, Real.rpow_one]
        field_simp

end QuadFormsKB.HilbertModular
