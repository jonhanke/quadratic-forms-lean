import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchLeray

/-!
# The Leray measure of the hyperbola $x_0^2 - \delta x_1^2 = 1$
**Layer:** one real place with $E_w = \mathbb R\times\mathbb R$: $\delta > 0$, $s = \sqrt\delta$, $Q = \langle1,-\delta\rangle$
(`QuadForm.diag ![1, -δ]`), $S_1 = \{Q = 1\}$. The branch $x_0 > 0$ of $S_1$ is parametrized by
$\gamma(\tau) = (\cosh\tau,\ \sinh\tau/s)$ (in the coordinates of the two places of $E$ over $w$, $\gamma(\tau)$ is
$(e^\tau, e^{-\tau})$).

**Proves**
* **`sig_hypArc`**: $\sigma_1(\gamma(J)) = \mathrm{vol}(J)/(2s)$ for every measurable $J\subseteq\mathbb R$. *Proof:* $\sigma_1(A)$ is the
  Lebesgue measure of the cone $\{e^rx : r\le0,\ x\in A\}$ (`nu_apply`, `sig`), the cone over $\gamma(J)$ is the image of
  $(-\infty,0]\times J$ under $\Phi(r,\tau) = (e^r\cosh\tau, e^r\sinh\tau/s)$, whose Jacobian is $e^{2r}/s$
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`), and $\int_{-\infty}^0e^{2r}\,dr = 1/2$.
* **`lerayMeasure_rotSec_hypArc`**: $\mu_Q(\rho(\gamma(J))) = \mathrm{vol}(J)/(8\delta^{3/2})$ (with `lerayMeasure_rotSec_image`).
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {δ : ℝ}

/-- The hyperbola point $\gamma(\tau) = (\cosh\tau, \sinh\tau/\sqrt\delta)$ of $x_0^2 - \delta x_1^2 = 1$. -/
def hypVec (δ : ℝ) (τ : ℝ) : Fin 2 → ℝ := ![Real.cosh τ, (Real.sqrt δ)⁻¹ * Real.sinh τ]

theorem hypVec_mem (hδ : 0 < δ) (τ : ℝ) : hypVec δ τ ∈ sph (QuadForm.diag ![1, -δ]) 1 := by
  change (QuadForm.diag ![1, -δ]).eval (hypVec δ τ) = 1
  rw [eval_diag_one_D]
  simp only [hypVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  have hs0 : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  rw [mul_pow, inv_pow, hs]
  field_simp
  have := Real.cosh_sq_sub_sinh_sq τ
  linarith

/-- $\gamma(\tau)$ as a point of $S_1$. -/
def hypArc (hδ : 0 < δ) (τ : ℝ) : Sph (QuadForm.diag ![1, -δ]) 1 := ⟨hypVec δ τ, hypVec_mem hδ τ⟩

/-- The map $\Phi(r,\tau) = (e^r\cosh\tau, e^r\sinh\tau/s)$. -/
def hypPhi (δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp p.1 * Real.cosh p.2, (Real.sqrt δ)⁻¹ * (Real.exp p.1 * Real.sinh p.2))

/-- Its derivative. -/
def hypPhiD (δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((Real.exp p.1 * Real.cosh p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (Real.exp p.1 * Real.sinh p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (((Real.sqrt δ)⁻¹ * (Real.exp p.1 * Real.sinh p.2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ((Real.sqrt δ)⁻¹ * (Real.exp p.1 * Real.cosh p.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem hasFDerivAt_hypPhi (p : ℝ × ℝ) : HasFDerivAt (hypPhi δ) (hypPhiD δ p) p := by
  have he : HasFDerivAt (fun q : ℝ × ℝ => Real.exp q.1) (Real.exp p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (Real.hasDerivAt_exp p.1).comp_hasFDerivAt p hasFDerivAt_fst
  have hc : HasFDerivAt (fun q : ℝ × ℝ => Real.cosh q.2) (Real.sinh p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (Real.hasDerivAt_cosh p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have hs : HasFDerivAt (fun q : ℝ × ℝ => Real.sinh q.2) (Real.cosh p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (Real.hasDerivAt_sinh p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => Real.exp q.1 * Real.cosh q.2) _ p := he.mul hc
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => (Real.sqrt δ)⁻¹ * (Real.exp q.1 * Real.sinh q.2)) _ p :=
    (he.mul hs).const_mul _
  refine (h1.prodMk h2).congr_fderiv ?_
  ext q <;> simp [hypPhiD] <;> (try ring_nf) <;> simp

theorem det_hypPhiD (hδ : 0 < δ) (p : ℝ × ℝ) : (hypPhiD δ p).det = Real.exp (2 * p.1) / Real.sqrt δ := by
  have hs0 : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, hypPhiD, Module.Basis.finTwoProd]
  rw [show (2 : ℝ) * p.1 = p.1 + p.1 by ring, Real.exp_add]
  field_simp
  have := Real.cosh_sq_sub_sinh_sq p.2
  linear_combination this

theorem hypPhi_injective (hδ : 0 < δ) : Function.Injective (hypPhi δ) := by
  intro p q h
  have hs0 : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  simp only [hypPhi, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : Real.exp p.1 * Real.sinh p.2 = Real.exp q.1 * Real.sinh q.2 :=
    mul_left_cancel₀ (inv_ne_zero hs0) h2
  -- e^{2r} = x₀² - (s x₁)²
  have hr : Real.exp p.1 ^ 2 = Real.exp q.1 ^ 2 := by
    have e1 := Real.cosh_sq_sub_sinh_sq p.2
    have e2 := Real.cosh_sq_sub_sinh_sq q.2
    calc Real.exp p.1 ^ 2 = (Real.exp p.1 * Real.cosh p.2) ^ 2 - (Real.exp p.1 * Real.sinh p.2) ^ 2 := by
          linear_combination (-(Real.exp p.1 ^ 2)) * e1
      _ = (Real.exp q.1 * Real.cosh q.2) ^ 2 - (Real.exp q.1 * Real.sinh q.2) ^ 2 := by rw [h1, h2']
      _ = Real.exp q.1 ^ 2 := by linear_combination (Real.exp q.1 ^ 2) * e2
  have hr' : Real.exp p.1 = Real.exp q.1 :=
    (pow_left_inj₀ (Real.exp_pos _).le (Real.exp_pos _).le two_ne_zero).1 hr
  have h1' : p.1 = q.1 := Real.exp_injective hr'
  have hsinh : Real.sinh p.2 = Real.sinh q.2 := by
    rw [hr'] at h2'; exact mul_left_cancel₀ (Real.exp_pos _).ne' h2'
  exact Prod.ext h1' (Real.sinh_injective hsinh)

/-- The coordinates $(\mathbb R\times\mathbb R)\to\mathbb R^2$. -/
abbrev toVec2 : ℝ × ℝ ≃ᵐ (Fin 2 → ℝ) := (MeasurableEquiv.finTwoArrow).symm

theorem toVec2_hypPhi (p : ℝ × ℝ) : toVec2 (hypPhi δ p) = Real.exp p.1 • hypVec δ p.2 := by
  funext i; fin_cases i <;> simp [hypPhi, hypVec] <;> ring

/-- **The Leray measure of an arc of the hyperbola**: $\sigma_1(\gamma(J)) = \mathrm{vol}(J)/(2\sqrt\delta)$. -/
theorem sig_hypArc (hδ : 0 < δ) {J : Set ℝ} (hJ : MeasurableSet J) :
    sig (QuadForm.diag ![1, -δ]) 1 (hypArc hδ '' J) = ENNReal.ofReal (1 / (2 * Real.sqrt δ)) * volume J := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hinj : Function.Injective (hypArc hδ) := fun a b h => by
    have := congrArg (fun x : Sph (QuadForm.diag ![1, -δ]) 1 => (x : Fin 2 → ℝ) 1) h
    simp only [hypArc, hypVec, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    exact Real.sinh_injective (mul_left_cancel₀ (inv_ne_zero hs.ne') this)
  have hmeasA : MeasurableSet (hypArc hδ '' J) := by
    have hc : Continuous (hypArc hδ) := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun i => ?_
      fin_cases i
      · simp only [hypVec, Matrix.cons_val_zero]; fun_prop
      · simp only [hypVec, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop
    exact (hc.measurableEmbedding hinj).measurableSet_image.mpr hJ
  rw [sig, Measure.smul_apply, nu_apply one_ne_zero hmeasA, smul_eq_mul]
  -- the cone is the image of `Iic 0 ×ˢ J` under `toVec2 ∘ hypPhi`
  have himg : pol (QuadForm.diag ![1, -δ]) 1 '' (Iic 0 ×ˢ (hypArc hδ '' J)) = toVec2 '' (hypPhi δ '' (Iic 0 ×ˢ J)) := by
    ext y
    constructor
    · rintro ⟨⟨r, x⟩, ⟨hr, ⟨τ, hτ, rfl⟩⟩, rfl⟩
      exact ⟨hypPhi δ (r, τ), ⟨(r, τ), ⟨hr, hτ⟩, rfl⟩, by rw [toVec2_hypPhi]; rfl⟩
    · rintro ⟨_, ⟨⟨r, τ⟩, ⟨hr, hτ⟩, rfl⟩, rfl⟩
      exact ⟨(r, hypArc hδ τ), ⟨hr, τ, hτ, rfl⟩, by rw [toVec2_hypPhi]; rfl⟩
  rw [himg]
  have hpres : MeasurePreserving toVec2 volume volume := (volume_preserving_finTwoArrow ℝ).symm
  have hvol : volume (toVec2 '' (hypPhi δ '' (Iic 0 ×ˢ J))) = volume (hypPhi δ '' (Iic 0 ×ˢ J)) := by
    rw [MeasurableEquiv.image_eq_preimage_symm, ← hpres.symm.measure_preimage_equiv]
  rw [hvol]
  have hS : MeasurableSet (Iic (0 : ℝ) ×ˢ J) := measurableSet_Iic.prod hJ
  have hJac := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun p _ => (hasFDerivAt_hypPhi (δ := δ) p).hasFDerivWithinAt) (hypPhi_injective hδ).injOn (fun _ => 1)
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul, mul_one] at hJac
  rw [hJac]
  simp_rw [det_hypPhiD hδ]
  -- ∫_{Iic 0 × J} e^{2r}/s = (1/(2s)) vol J
  have key : ∫⁻ r in Iic (0 : ℝ), ENNReal.ofReal |Real.exp (2 * r) / Real.sqrt δ| =
      ENNReal.ofReal (1 / (2 * Real.sqrt δ)) := by
    have hpos : ∀ r : ℝ, |Real.exp (2 * r) / Real.sqrt δ| = Real.exp (2 * r) / Real.sqrt δ := fun r =>
      abs_of_pos (div_pos (Real.exp_pos _) hs)
    simp_rw [hpos]
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_mul_Iic two_pos 0).div_const _)
      (Filter.Eventually.of_forall fun r => (div_pos (Real.exp_pos _) hs).le), integral_div,
      integral_exp_mul_Iic two_pos 0]
    congr 1
    rw [mul_zero, Real.exp_zero]
    field_simp
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [lintegral_mul_const _ (by fun_prop), key]
  have h2 : ENNReal.ofReal (1 / 2) * 2 = 1 := by
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  calc _ = (ENNReal.ofReal (1 / 2) * 2) * (ENNReal.ofReal (1 / (2 * Real.sqrt δ)) * volume J) := by ring
    _ = _ := by rw [h2, one_mul]

/-- **The Leray measure of the rotations by an arc of the hyperbola**:
$\mu_{\langle1,-\delta\rangle}(\rho(\gamma(J))) = \mathrm{vol}(J)/(8\delta^{3/2})$. -/
theorem lerayMeasure_rotSec_hypArc (hδ : 0 < δ) {J : Set ℝ} (hJ : MeasurableSet J) :
    lerayMeasure (QuadForm.diag ![1, -δ]) (gramDetR_diag_one_D_ne_zero (neg_ne_zero.mpr hδ.ne'))
        (rotSec (-δ) '' (hypArc hδ '' J)) =
      ENNReal.ofReal (1 / (8 * δ * Real.sqrt δ)) * volume J := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hinj : Function.Injective (hypArc hδ) := fun a b h => by
    have := congrArg (fun x : Sph (QuadForm.diag ![1, -δ]) 1 => (x : Fin 2 → ℝ) 1) h
    simp only [hypArc, hypVec, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    exact Real.sinh_injective (mul_left_cancel₀ (inv_ne_zero hs.ne') this)
  have hc : Continuous (hypArc hδ) := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp only [hypVec, Matrix.cons_val_zero]; fun_prop
    · simp only [hypVec, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop
  have hA : MeasurableSet (hypArc hδ '' J) := (hc.measurableEmbedding hinj).measurableSet_image.mpr hJ
  rw [lerayMeasure_rotSec_image (neg_ne_zero.mpr hδ.ne') hA, sig_hypArc hδ hJ, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_neg, abs_of_pos hδ]
  congr 2
  field_simp
  ring

end QuadFormsKB.Tamagawa.Measure.Weil
