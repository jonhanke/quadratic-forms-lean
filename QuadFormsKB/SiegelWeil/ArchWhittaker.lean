/-
# The archimedean Whittaker integral is the archimedean density

**Layer:** local, one real place. Classical analysis on $\mathbb R$ and $\mathbb R^n$; no global input.

**Setting.** $V = \mathbb R^{n}$, $n = 2m$, with the positive definite diagonal form $Q(x) = \sum_{i<n}a_ix_i^2$, $a_i > 0$
(0-based indices), $D = \prod_ia_i$; $\psi_\infty(x) = e(x) = e^{2\pi ix}$ and Lebesgue measure (self-dual for $\psi_\infty$);
$z = x + iy \in \mathbb H$. For the Gaussian $\varphi_\infty(x) = e^{-2\pi Q(x)}$ and $g_z = n(x)m(y^{1/2})$ the Schrödinger
model gives $\omega_\infty(g_z)\varphi_\infty = y^{m/2}G_z$, $G_\tau(x) = e^{2\pi i\tau Q(x)}$ (`WeilRep.borelInf_phiStd_inf`), and
then (`SiegelWeil.sec_wMat_nMat`)
$$f_\infty(wn(b)g_z) = (\omega_\infty(wn(b))\,\omega_\infty(g_z)\varphi_\infty)(0) = \gamma_V\,c_B\,y^{m/2}\,\mathcal G(z + b),\qquad
  \mathcal G(\tau) = \int_{\mathbb R^n}e^{2\pi i\tau Q(x)}\,dx,$$
$c_B = \prod_i(2a_i)^{1/2}$, $\gamma_V$ the Weil index. The **archimedean Whittaker integral** is
$W_\infty(t, z) = \int_{\mathbb R}f_\infty(wn(b)g_z)\,e(-tb)\,db$.

**Results.**
* `integral_pow_mul_cexp_neg` (the Laplace transform of $u^k$ at a complex point): $\int_0^\infty u^ke^{-ru}\,du = k!/r^{k+1}$
  for $\operatorname{Re}r > 0$ (integration by parts; Mathlib has only real $r$).
* `gaussQ_eq`: $\mathcal G(\tau) = \big(\prod_i(\pi/a_i)^{1/2}\big)(-2\pi i\tau)^{-m}$ for $\operatorname{Im}\tau > 0$; no branch
  ambiguity, since $n = 2m$ is even.
* **`archWhittaker_eq`** (**item 3**, Siegel's computation of $\beta_\infty$): for $m \ge 2$ ($n \ge 4$), $\operatorname{Im}z > 0$,
  $t \in \mathbb R$,
  $$\int_{\mathbb R}\mathcal G(z + b)\,e(-tb)\,db = \begin{cases}\beta_\infty(t)\,e(tz), & t > 0,\\ 0, & t \le 0,\end{cases}\qquad
    \beta_\infty(t) = \frac{\pi^{n/2}}{\Gamma(n/2)}D^{-1/2}t^{n/2-1} = \frac{n\,\omega_n}{2}D^{-1/2}t^{n/2-1},$$
  the repo's archimedean density `Siegel.betaInfR` of $Q$ (Hanke (5.5); `Siegel.tendsto_volume_shell_div_real` identifies it
  with $\lim_{\varepsilon\to0}\operatorname{vol}\{t < Q \le t+\varepsilon\}/\varepsilon$). Hence
  $$W_\infty(t, z) = \gamma_V\,c_B\,y^{m/2}\,\beta_\infty(t)\,e(tz)\ (t > 0),\qquad W_\infty(t, z) = 0\ (t \le 0)$$
  (`archWhittakerW_eq`); at $z = i$: $W_\infty(t) = \gamma_Vc_B\,\beta_\infty(t)\,e^{-2\pi t}$ $= \gamma_Vc_B\frac{\pi^m}{\Gamma(m)}D^{-1/2}t^{m-1}e^{-2\pi t}$.
  *Proof:* $\mathcal G(z + b) = \frac{\pi^mD^{-1/2}}{(m-1)!}\,\mathcal F^{-1}h(b)$ for $h(u) = \mathbf 1_{u>0}u^{m-1}e(zu)$ (Gaussian integral
  and the Laplace transform), then Fourier inversion $\mathcal F\mathcal F^{-1}h = h$ (Mathlib), which needs $m \ge 2$ for the
  continuity of $h$ at $0$ and the integrability of $(z + b)^{-m}$. This is the archimedean half of "Whittaker = density":
  the same constant shape $\gamma_V\,c_B\operatorname{vol}(\mathcal O)^{n-1}\beta_v(t)$ as at the finite places
  (`SiegelWeil.whittakerV_eq_localDensity`), with $\operatorname{vol} = 1$.

Sources: Siegel, Ann. Math. 36 (1935), §§ on the archimedean factor [unverified]; Weil, Acta Math. 113 (1965) [unverified];
Kudla (2008), §1 (the archimedean Whittaker function of weight $m$) [unverified]; Hanke 2004, (5.5) (the value of
$\beta_\infty$).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Siegel.ArchimedeanNF
import QuadFormsKB.Analysis.WeilIndexInf

open MeasureTheory Complex Set Filter Topology
open scoped FourierTransform Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

/-! ### The Laplace transform of $u^k$ at a complex point -/

lemma norm_pow_mul_cexp_neg (k : ℕ) (r : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ k * cexp (-(r * u))‖ = u ^ (k : ℝ) * Real.exp (-r.re * u ^ (1 : ℝ)) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, Complex.norm_exp,
    Real.rpow_natCast, Real.rpow_one]
  congr 2
  simp [Complex.mul_re]

lemma integrableOn_pow_mul_cexp (k : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ k * cexp (-(r * u))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := k) (p := 1) (b := r.re)
    (by have := k.cast_nonneg (α := ℝ); linarith) one_pos hr
  refine Integrable.mono' h ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    exact (norm_pow_mul_cexp_neg k r hu).le

lemma tendsto_pow_mul_cexp_neg (k : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun u : ℝ => (u : ℂ) ^ k * cexp (-(r * u))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp (tendsto_id.const_mul_atTop hr)
  have h2 := h1.const_mul ((r.re ^ k)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr' ((eventually_gt_atTop 0).mono fun u hu => ?_)
  simp only [Function.comp, id]
  rw [norm_pow_mul_cexp_neg k r hu, Real.rpow_natCast, Real.rpow_one, mul_pow]
  field_simp

/-- **The Laplace transform of $u^k$ at a complex point:** $\int_0^\infty u^ke^{-ru}\,du = k!/r^{k+1}$ for
$\operatorname{Re}r > 0$. (Integration by parts, by induction on $k$; Mathlib's `integral_cpow_mul_exp_neg_mul_Ioi` has
only real $r$.) -/
theorem integral_pow_mul_cexp_neg (k : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ k * cexp (-(r * u)) = k.factorial / r ^ (k + 1) := by
  have hr0 : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
  induction k with
  | zero =>
    have := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    rw [show (fun u : ℝ => cexp (-(r * u))) = fun u : ℝ => cexp (-r * u) by funext u; ring_nf]
    rw [this]; field_simp
  | succ k ih =>
    set g : ℝ → ℂ := fun u => (u : ℂ) ^ (k + 1) * cexp (-(r * u)) with hg
    set Fp : ℝ → ℂ := fun u => -(g u) / r with hFp
    have hderiv : ∀ u : ℝ, HasDerivAt Fp (g u - ((k + 1 : ℕ) : ℂ) / r * ((u : ℂ) ^ k * cexp (-(r * u)))) u := by
      intro u
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
      have h2 := h1.pow (k + 1)
      have h3 : HasDerivAt (fun u : ℝ => cexp (-(r * u))) (cexp (-(r * u)) * (-(r * 1))) u :=
        ((h1.const_mul r).neg).cexp
      have h4 := ((h2.mul h3).neg).div_const r
      convert h4 using 1
      simp only [hg, Nat.add_sub_cancel, Pi.pow_apply]
      push_cast
      field_simp
      ring
    have hint : IntegrableOn (fun u => g u - ((k + 1 : ℕ) : ℂ) / r * ((u : ℂ) ^ k * cexp (-(r * u)))) (Ioi 0) :=
      (integrableOn_pow_mul_cexp (k + 1) hr).sub ((integrableOn_pow_mul_cexp k hr).const_mul _)
    have hlim : Tendsto Fp atTop (𝓝 0) := by
      have := ((tendsto_pow_mul_cexp_neg (k + 1) hr).neg).div_const r
      simpa [hFp, hg] using this
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
      ((by unfold Fp g; fun_prop : Continuous Fp).continuousWithinAt) (fun u _ => hderiv u) hint hlim
    rw [integral_sub (integrableOn_pow_mul_cexp (k + 1) hr) ((integrableOn_pow_mul_cexp k hr).const_mul _),
      integral_const_mul, ih] at hFTC
    have hF0 : Fp 0 = 0 := by simp [hFp, hg]
    rw [hF0, sub_zero] at hFTC
    have : ∫ u in Ioi (0 : ℝ), g u = ((k + 1 : ℕ) : ℂ) / r * (k.factorial / r ^ (k + 1)) := by
      linear_combination hFTC
    rw [this, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-! ### The Gaussian integral $\mathcal G(\tau)$ -/

variable {m : ℕ} (a : Fin (2 * m) → ℝ)

/-- **$\mathcal G(\tau) = \int_{\mathbb R^n}e^{2\pi i\tau Q(x)}\,dx$**, $Q(x) = \sum_{i<n}a_ix_i^2$, $n = 2m$ (Lebesgue measure). For
$\operatorname{Im}\tau > 0$ it is $(\omega_\infty(w)G_\tau)(0)/(\gamma_Vc_B)$. -/
def gaussQ (τ : ℂ) : ℂ := ∫ x : Fin (2 * m) → ℝ, cexp (2 * π * I * τ * ∑ i, (a i : ℂ) * (x i : ℂ) ^ 2)

/-- The constant $\prod_{i<n}(\pi/a_i)^{1/2}$ $(= \pi^{m}D^{-1/2}$, `cG_eq`). -/
def cG : ℝ := ∏ i, Real.sqrt (π / a i)

lemma cG_eq (ha : ∀ i, 0 < a i) : cG a = π ^ m * (∏ i, a i) ^ (-(1 : ℝ) / 2) := by
  have hpos : ∀ i ∈ Finset.univ, 0 ≤ π / a i := fun i _ => (div_pos Real.pi_pos (ha i)).le
  have hD : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  rw [cG]
  simp only [Real.sqrt_eq_rpow]
  rw [Real.finsetProd_rpow _ _ hpos, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Real.div_rpow (by positivity) hD.le, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  rw [div_eq_mul_inv, ← Real.rpow_neg hD.le]
  congr 1
  · rw [show ((2 * m : ℕ) : ℝ) * (1 / 2) = (m : ℝ) by push_cast; ring]; exact Real.rpow_natCast _ _
  · congr 1; ring

/-- **The Gaussian integral in closed form**: for $\operatorname{Im}\tau > 0$ and $a_i > 0$,
$$\mathcal G(\tau) = \Big(\prod_{i<n}(\pi/a_i)^{1/2}\Big)\,(-2\pi i\tau)^{-m}.$$
(Each coordinate gives $(\pi/(-2\pi i\tau a_i))^{1/2} = (\pi/a_i)^{1/2}(-2\pi i\tau)^{-1/2}$, $\operatorname{Re}(-2\pi i\tau) > 0$, and the
$2m$ square roots combine to the integral power $(-2\pi i\tau)^{-m}$.) -/
theorem gaussQ_eq (ha : ∀ i, 0 < a i) {τ : ℂ} (hτ : 0 < τ.im) :
    gaussQ a τ = (cG a : ℂ) * ((-2 * π * I * τ)⁻¹) ^ m := by
  set r : ℂ := -2 * π * I * τ with hr
  have hrre : 0 < r.re := by
    simp [hr, Complex.mul_re]; positivity
  have hr0 : r ≠ 0 := fun h => by rw [h] at hrre; simp at hrre
  have hwre : 0 < (r⁻¹).re := by
    rw [Complex.inv_re]; exact div_pos hrre (Complex.normSq_pos.mpr hr0)
  have hfac : ∀ i, ∫ x : ℝ, cexp (2 * π * I * τ * ((a i : ℂ) * (x : ℂ) ^ 2)) =
      (Real.sqrt (π / a i) : ℂ) * (r⁻¹) ^ (1 / 2 : ℂ) := by
    intro i
    have hb : 0 < (r * a i).re := by
      rw [Complex.mul_re]; simp; exact mul_pos hrre (ha i)
    have h := integral_gaussian_complex hb
    have e1 : (fun x : ℝ => cexp (2 * π * I * τ * ((a i : ℂ) * (x : ℂ) ^ 2))) =
        fun x : ℝ => cexp (-(r * a i) * (x : ℂ) ^ 2) := by
      funext x; congr 1; rw [hr]; ring
    rw [e1, h]
    have e2 : (π : ℂ) / (r * a i) = ((π / a i : ℝ) : ℂ) * r⁻¹ := by
      push_cast; field_simp
    rw [e2, Analysis.cpow_mul_of_re (by simp; exact (div_pos Real.pi_pos (ha i)).le)
      (by exact_mod_cast (div_pos Real.pi_pos (ha i)).ne') hwre]
    congr 1
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_pos Real.pi_pos (ha i)).le]
    push_cast; ring_nf
  unfold gaussQ
  have e : (fun x : Fin (2 * m) → ℝ => cexp (2 * π * I * τ * ∑ i, (a i : ℂ) * (x i : ℂ) ^ 2)) =
      fun x => ∏ i, (fun i (y : ℝ) => cexp (2 * π * I * τ * ((a i : ℂ) * (y : ℂ) ^ 2))) i (x i) := by
    funext x; rw [Finset.mul_sum, Complex.exp_sum]
  rw [e, integral_fintype_prod_volume_eq_prod (fun i (y : ℝ) => cexp (2 * π * I * τ * ((a i : ℂ) * (y : ℂ) ^ 2)))]
  simp only [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [cG]; push_cast
  congr 1
  rw [pow_mul, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, Complex.cpow_nat_inv_pow _ two_ne_zero]

/-! ### Fourier inversion for $h(u) = \mathbf 1_{u > 0}u^{m-1}e(zu)$ -/

/-- $h_z(u) = \mathbf 1_{u > 0}\,u^{k}\,e^{2\pi izu}$ (here $k = m - 1$). -/
def hW (k : ℕ) (z : ℂ) (u : ℝ) : ℂ := (Ioi (0 : ℝ)).indicator (fun u => (u : ℂ) ^ k * cexp (2 * π * I * z * u)) u

lemma hW_eq_max {k : ℕ} (hk : 1 ≤ k) (z : ℂ) (u : ℝ) :
    hW k z u = ((max u 0 : ℝ) : ℂ) ^ k * cexp (2 * π * I * z * u) := by
  unfold hW
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem (by exact hu), max_eq_left hu.le]
  · rw [Set.indicator_of_notMem (by simpa using hu), max_eq_right (not_lt.mp hu)]
    simp [zero_pow (by omega : k ≠ 0)]

lemma continuous_hW {k : ℕ} (hk : 1 ≤ k) (z : ℂ) : Continuous (hW k z) := by
  have : hW k z = fun u => ((max u 0 : ℝ) : ℂ) ^ k * cexp (2 * π * I * z * u) := funext (hW_eq_max hk z)
  rw [this]; fun_prop

lemma rW_re {z : ℂ} (hz : 0 < z.im) (w : ℝ) : 0 < (-2 * π * I * (z - w)).re := by
  simp [Complex.mul_re]; positivity

lemma integrable_hW (k : ℕ) {z : ℂ} (hz : 0 < z.im) : Integrable (hW k z) := by
  unfold hW
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := integrableOn_pow_mul_cexp k (rW_re hz 0)
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
  rw [show (2 * π * I * z * u : ℂ) = -((-2 * π * I * (z - ((0 : ℝ) : ℂ))) * u) by push_cast; ring]

/-- **The Fourier transform of $h_z$:** $\mathcal Fh_z(w) = k!\,(-2\pi i(z - w))^{-(k+1)}$. -/
lemma fourier_hW (k : ℕ) {z : ℂ} (hz : 0 < z.im) (w : ℝ) :
    𝓕 (hW k z) w = k.factorial / (-2 * π * I * (z - w)) ^ (k + 1) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : (fun v : ℝ => cexp (((-2 * π * v * w : ℝ) : ℂ) * I) • hW k z v) =
      (Ioi (0 : ℝ)).indicator (fun u : ℝ => (u : ℂ) ^ k * cexp (-((-2 * π * I * (z - w)) * u))) := by
    funext v
    unfold hW
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, smul_eq_mul]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
  rw [e, integral_indicator measurableSet_Ioi, integral_pow_mul_cexp_neg k (rW_re hz w)]

lemma norm_inv_rW_pow_le {z : ℂ} (hz : 0 < z.im) {m : ℕ} (hm : 2 ≤ m) (w : ℝ) :
    ‖((-2 * π * I * (z - w)) ^ m)⁻¹‖ ≤
      (((2 * π * z.im) ^ (m - 2))⁻¹ * (4 * π ^ 2 * min 1 (z.im ^ 2))⁻¹) * (1 + (w - z.re) ^ 2)⁻¹ := by
  set y := z.im with hydef
  have hnorm : ‖-2 * π * I * (z - w)‖ = 2 * π * ‖z - w‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I]; simp [abs_of_pos Real.pi_pos]
  have hzw2 : ‖z - w‖ ^ 2 = (z.re - w) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [y]; ring
  have hy : y ≤ ‖z - w‖ := by
    have := Complex.abs_im_le_norm (z - w)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have hpos : 0 < ‖z - w‖ := lt_of_lt_of_le hz hy
  have hmin : min 1 (y ^ 2) * (1 + (w - z.re) ^ 2) ≤ ‖z - w‖ ^ 2 := by
    rw [hzw2]
    have h1 : min 1 (y ^ 2) ≤ 1 := min_le_left _ _
    have h2 : min 1 (y ^ 2) ≤ y ^ 2 := min_le_right _ _
    have h0 : 0 ≤ min 1 (y ^ 2) := le_min zero_le_one (sq_nonneg _)
    nlinarith [sq_nonneg (w - z.re), sq_nonneg (z.re - w), mul_le_mul_of_nonneg_right h1 (sq_nonneg (w - z.re))]
  have hm0 : 0 < min 1 (y ^ 2) := lt_min one_pos (by positivity)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [norm_inv, norm_pow, hnorm, Nat.add_sub_cancel, pow_add, mul_inv]
  have hA : 0 < 2 * π * ‖z - w‖ := by positivity
  have h1 : ((2 * π * ‖z - w‖) ^ k)⁻¹ ≤ ((2 * π * y) ^ k)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) k)
  have h2 : ((2 * π * ‖z - w‖) ^ 2)⁻¹ ≤ (4 * π ^ 2 * min 1 (y ^ 2) * (1 + (w - z.re) ^ 2))⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    calc 4 * π ^ 2 * min 1 (y ^ 2) * (1 + (w - z.re) ^ 2) = 4 * π ^ 2 * (min 1 (y ^ 2) * (1 + (w - z.re) ^ 2)) := by ring
      _ ≤ 4 * π ^ 2 * ‖z - w‖ ^ 2 := by gcongr
      _ = (2 * π * ‖z - w‖) ^ 2 := by ring
  calc ((2 * π * ‖z - w‖) ^ k)⁻¹ * ((2 * π * ‖z - w‖) ^ 2)⁻¹
      ≤ ((2 * π * y) ^ k)⁻¹ * (4 * π ^ 2 * min 1 (y ^ 2) * (1 + (w - z.re) ^ 2))⁻¹ :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by rw [mul_inv, mul_inv]; ring

lemma integrable_inv_rW_pow {z : ℂ} (hz : 0 < z.im) {m : ℕ} (hm : 2 ≤ m) :
    Integrable (fun w : ℝ => ((-2 * π * I * (z - w)) ^ m)⁻¹) := by
  have hne : ∀ w : ℝ, -2 * π * I * (z - w) ≠ 0 := fun w h => by
    have := rW_re hz w; rw [h] at this; simp at this
  refine Integrable.mono' ((integrable_inv_one_add_sq.comp_sub_right z.re).const_mul _) ?_
    (Filter.Eventually.of_forall fun w => norm_inv_rW_pow_le hz hm w)
  exact (Continuous.aestronglyMeasurable (by
    refine Continuous.inv₀ (by fun_prop) fun w => pow_ne_zero _ (hne w)))

/-! ### The archimedean Whittaker integral -/

lemma gramDetR_diag (a : Fin (2 * m) → ℝ) : Siegel.gramDetR (QuadForm.diag a) = ∏ i, a i := by
  unfold Siegel.gramDetR QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  rw [show (fun i => a i + a i) = fun i => 2 * a i by funext i; ring, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp

/-- $\beta_\infty(t) = \frac{\pi^m}{(m-1)!}D^{-1/2}t^{m-1}$ for the diagonal form (Hanke (5.5), `Siegel.betaInfR`). -/
lemma betaInfR_diag (hm : 1 ≤ m) (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 < t) :
    Siegel.betaInfR (QuadForm.diag a) t = cG a / (m - 1).factorial * t ^ (m - 1) := by
  unfold Siegel.betaInfR
  rw [gramDetR_diag, Siegel.unitBallVol_eq (by omega), cG_eq a ha]
  have hΓ : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = m.factorial := by
    rw [show ((2 * m : ℕ) : ℝ) / 2 + 1 = ((m : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have hexp : (((2 * m : ℕ) : ℝ) - 2) / 2 = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm]; push_cast; ring
  rw [hΓ, hexp, Real.rpow_natCast, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

/-- **The archimedean Whittaker integral of the Gaussian is $\beta_\infty$** (item 3; Siegel). For $Q = \sum_{i<n}a_ix_i^2$,
$a_i > 0$, $n = 2m \ge 4$, $z \in \mathbb H$ and $t \in \mathbb R$,
$$\int_{\mathbb R}\mathcal G(z + b)\,e^{-2\pi itb}\,db = \begin{cases}\beta_\infty(t)\,e^{2\pi itz}, & t > 0,\\ 0, & t \le 0,\end{cases}$$
$\mathcal G(\tau) = \int_{\mathbb R^n}e^{2\pi i\tau Q(x)}dx$ (`gaussQ`), $\beta_\infty$ = `Siegel.betaInfR` $= \frac{n\,\omega_n}{2}D^{-1/2}t^{n/2-1}$. -/
@[kb "siegel1935" "the archimedean factor of the Fourier coefficients [unverified]; Hanke 2004, (5.5)"]
theorem archWhittaker_eq (hm : 2 ≤ m) (ha : ∀ i, 0 < a i) {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ∫ b : ℝ, gaussQ a (z + b) * cexp (-2 * π * I * t * b) =
      if 0 < t then (Siegel.betaInfR (QuadForm.diag a) t : ℂ) * cexp (2 * π * I * t * z) else 0 := by
  have hk : 1 ≤ m - 1 := by omega
  have hm1 : m - 1 + 1 = m := by omega
  -- `𝒢(z + b)` is a multiple of `𝓕⁻ h (b)`
  have hG : ∀ b : ℝ, gaussQ a (z + b) = (cG a / (m - 1).factorial : ℂ) * 𝓕⁻ (hW (m - 1) z) b := by
    intro b
    rw [gaussQ_eq a ha (by simpa using hz), Real.fourierInv_eq_fourier_neg, fourier_hW _ hz, hm1]
    have hne : (-2 * π * I * (z - ((-b : ℝ) : ℂ))) ≠ 0 := by
      have := rW_re hz (-b); intro h; rw [h] at this; simp at this
    have hf : ((m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast
    rw [show z - -(b : ℂ) = z + b by ring] at *
    field_simp
    rw [div_eq_mul_inv (cG a : ℂ), ← inv_pow, one_div, inv_neg]
  have hint : Integrable (𝓕 (hW (m - 1) z)) := by
    have := (integrable_inv_rW_pow hz hm).const_mul ((m - 1).factorial : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    rw [fourier_hW _ hz, hm1, div_eq_mul_inv]
  have hinv := (integrable_hW (m - 1) hz).fourier_fourierInv_eq hint (continuous_hW hk z).continuousAt (v := t)
  rw [Real.fourier_real_eq_integral_exp_smul] at hinv
  have e : ∫ b : ℝ, gaussQ a (z + b) * cexp (-2 * π * I * t * b) =
      (cG a / (m - 1).factorial : ℂ) * ∫ b : ℝ, cexp (((-2 * π * b * t : ℝ) : ℂ) * I) • 𝓕⁻ (hW (m - 1) z) b := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    rw [hG, smul_eq_mul]; push_cast; ring_nf
  rw [e, hinv]
  unfold hW
  split_ifs with ht
  · rw [Set.indicator_of_mem (by exact ht), betaInfR_diag a (by omega) ha ht]
    push_cast; ring_nf
  · rw [Set.indicator_of_notMem (by simpa using ht), mul_zero]

/-- **The archimedean Whittaker function** $W_\infty(t, z) = \int_{\mathbb R}f_\infty(wn(b)g_z)e(-tb)\,db$ with
$f_\infty(wn(b)g_z) = \gamma\,c_B\,y^{m/2}\mathcal G(z + b)$ (Schrödinger model: $\gamma$ the Weil index $\gamma_V$, $c_B = \prod_i(2a_i)^{1/2}$;
see the module docstring): $W_\infty(t, z) = \gamma c_B y^{m/2}\beta_\infty(t)e(tz)$ for $t > 0$, and $0$ for $t \le 0$. -/
@[kb "kudla2008" "§1 (the archimedean Whittaker function, weight $m$) [unverified]"]
theorem archWhittakerW_eq (hm : 2 ≤ m) (ha : ∀ i, 0 < a i) (γ : ℂ) {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ∫ b : ℝ, γ * (∏ i, (Real.sqrt (2 * a i) : ℂ)) * ((z.im : ℂ) ^ ((m : ℂ) / 2)) * gaussQ a (z + b) *
        cexp (-2 * π * I * t * b) =
      γ * (∏ i, (Real.sqrt (2 * a i) : ℂ)) * ((z.im : ℂ) ^ ((m : ℂ) / 2)) *
        (if 0 < t then (Siegel.betaInfR (QuadForm.diag a) t : ℂ) * cexp (2 * π * I * t * z) else 0) := by
  rw [← archWhittaker_eq a hm ha hz t, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  ring

/-- **Consistency with the ℚ archimedean density** (`Siegel.betaInf`, used in the proved ℚ results of `Siegel/`):
for an integral diagonal form $Q = \sum_ib_ix_i^2$, $b_i \in \mathbb Z$, the real-form density of $Q\otimes\mathbb R$ is the
repo's $\beta_\infty(Q, t)$ over ℚ, so `archWhittaker_eq` at $F = \mathbb Q$ reads
$\int\mathcal G(z + b)e(-tb)\,db = \beta_\infty(Q, t)\,e(tz)$ with the ℚ normalization $D = \det(H/2)$. -/
theorem betaInfR_diag_eq_betaInf (b : Fin (2 * m) → ℤ) (t : ℝ) :
    Siegel.betaInfR (QuadForm.diag fun i => (b i : ℝ)) t = Siegel.betaInf (QuadForm.diag b) t := by
  unfold Siegel.betaInfR Siegel.betaInf
  congr 4
  rw [gramDetR_diag]
  unfold Siegel.gramDet QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  rw [show (fun i => b i + b i) = fun i => 2 * b i by funext i; ring, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  field_simp

/-- **Item 3 at $F = \mathbb Q$:** for $Q = \sum_ib_ix_i^2$ with $b_i \in \mathbb Z_{>0}$, $n = 2m \ge 4$,
$\int_{\mathbb R}\mathcal G(z + b)e(-tb)\,db = \beta_\infty(Q, t)e(tz)$ for $t > 0$ and $0$ for $t \le 0$, with the repo's
$\beta_\infty$ over ℚ (`Siegel.betaInf`, Hanke (5.5)). -/
theorem archWhittaker_eq_rat (hm : 2 ≤ m) (b : Fin (2 * m) → ℤ) (hb : ∀ i, 0 < b i) {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ∫ x : ℝ, gaussQ (fun i => (b i : ℝ)) (z + x) * cexp (-2 * π * I * t * x) =
      if 0 < t then (Siegel.betaInf (QuadForm.diag b) t : ℂ) * cexp (2 * π * I * t * z) else 0 := by
  rw [archWhittaker_eq _ hm (fun i => by exact_mod_cast hb i) hz, betaInfR_diag_eq_betaInf]

end QuadFormsKB.SiegelWeil
