import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchSplit
import QuadFormsKB.Tamagawa.Measure.OrbitImage
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchComplex

/-!
# Complex-place Leray measures for binary forms
**Layer:** one complex place. Complex analogues of `BinaryArchLeray` and `BinaryArchSplit`. Throughout,
$|z|_{\mathbb C} = \|z\|^2$, `volume` is Lebesgue measure on $\mathbb C = \mathbb R^2$, and
`isoSqC` $= \{w : |\operatorname{Re}w| < 1,\ |\operatorname{Im}w| < 1\}$ is an open square on which $\exp$ and
$\gamma(w) = (\cosh w, \sinh w)$ are injective.

**Proves** (all unconditional)
* `lerayMeasureC_diag_one_univ_iso`: $\mu_{\langle c\rangle}(SO(\langle c\rangle)(\mathbb C)) = 1/\|2c\|^2$
  (the group is trivial). *Proof:* the fibration identity `lerayMeasureC_region` with $\varphi = 1$ on the
  regions $\{X : \operatorname{Re}X > 0,\ cX^2 \in \bar B_r(c)\}$, whose volume is computed by the change of
  variables $w = cX^2$ (Jacobian $\|2cX\|^2$), and the continuity of the density $\rho$ at $c_Q$ (`rho_coeffUC`);
  both sides are averaged over $\bar B_r(c)$ and $r \to 0$.
* `lerayMeasureC_rotSecC_image_iso`: $\mu_{\langle1,D\rangle}(\rho(A)) = \sigma_1(A)/(16\|D\|^2)$ for the rotation section
  `rotSecC_iso`, $u \mapsto \begin{pmatrix}u_0 & -Du_1\\ u_1 & u_0\end{pmatrix}$ (`lerayMeasureC_image_sec`, $m = 1$).
* `sigC_hypArc`: $\sigma_1(\gamma(J)) = \mathrm{vol}(J)/4$ for $Q = \langle1,-1\rangle$, measurable $J \subseteq$ `isoSqC`.
  *Proof:* $\nu_1(A) = \mathrm{Leb}(R_0\cdot A)/\lambda(R_0)$ (`nuC_apply_volume`); the map
  $(\beta, w) \mapsto \beta\gamma(w)$ has complex Jacobian $\beta$, real Jacobian $\|\beta\|^2$, so
  $\mathrm{Leb}(R_0\cdot\gamma(J)) = \lambda(R_0)\,\mathrm{vol}(J)$ and $\lambda(R_0)$ cancels (it is never computed).
* `lerayMeasureC_rotSecC_hypArc`: $\mu_{\langle1,-1\rangle}(\rho(\gamma(J))) = \mathrm{vol}(J)/64$.
* `lintegral_exp_image_complex`: $\int_{\exp(J)} \|z\|^{-2}\,d^2z = \mathrm{vol}(J)$ for $J \subseteq$ `isoSqC`;
  `lintegral_exp_image_real`: $\int_{\exp(J)} |x|^{-1}\,dx = \mathrm{vol}(J)$ for measurable $J \subseteq \mathbb R$.
-/

open MeasureTheory Measure Set Matrix Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchVol
  QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
  QuadFormsKB.Tamagawa.Measure.OrbitalComplex

/-! ### Jacobians of holomorphic maps -/

/-- The real determinant of multiplication by `a` on `ℂ` is `‖a‖²`. -/
theorem det_restrict_mul (a : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight a).restrictScalars ℝ).det = Complex.normSq a := by
  have h : ((1 : ℂ →L[ℂ] ℂ).smulRight a : ℂ →ₗ[ℂ] ℂ) = a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := by
    ext; simp [mul_comm]
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, det_restrictScalars_complex, h,
    LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]

/-- **Change of variables for a holomorphic injective map `ℂ → ℂ`**: Jacobian `‖f'‖²`. -/
theorem lintegral_image_holo {f f' : ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (hf : ∀ x ∈ S, HasDerivAt f (f' x) x) (hinj : InjOn f S) (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in f '' S, g y = ∫⁻ x in S, ENNReal.ofReal (Complex.normSq (f' x)) * g (f x) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (f' := fun x => ((1 : ℂ →L[ℂ] ℂ).smulRight (f' x)).restrictScalars ℝ)
    (fun x hx => ((hf x hx).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj g
  rw [h]
  refine setLIntegral_congr_fun hS fun x _ => ?_
  rw [det_restrict_mul, abs_of_nonneg (Complex.normSq_nonneg _)]

/-- The open square `|Re w| < 1, |Im w| < 1`. -/
def isoSqC : Set ℂ := {w | |w.re| < 1 ∧ |w.im| < 1}

theorem exp_injOn_isoSqC : InjOn Complex.exp isoSqC := by
  intro w hw w' hw' h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have him := congrArg Complex.im hk
  simp at him
  have h1 : |w.im| < 1 := hw.2
  have h2 : |w'.im| < 1 := hw'.2
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
    have : (k : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) := by nlinarith [Real.pi_pos]
    have := Real.pi_gt_three
    rw [abs_lt] at h1 h2
    nlinarith
  · subst hk0
    simp at hk
    exact hk
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have : (2 * Real.pi) ≤ (k : ℝ) * (2 * Real.pi) := by nlinarith [Real.pi_pos]
    have := Real.pi_gt_three
    rw [abs_lt] at h1 h2
    nlinarith

/-- **Idele side, complex place**: `∫_{exp(J)} dz/‖z‖² = vol(J)` for `J` in the open square. -/
theorem lintegral_exp_image_complex {J : Set ℂ} (hJ : MeasurableSet J) (hJs : J ⊆ isoSqC) :
    ∫⁻ z in Complex.exp '' J, ENNReal.ofReal (‖z‖ ^ 2)⁻¹ = volume J := by
  rw [lintegral_image_holo (f' := Complex.exp) hJ (fun x _ => Complex.hasDerivAt_exp x)
    (exp_injOn_isoSqC.mono hJs)]
  have : ∀ x : ℂ, ENNReal.ofReal (Complex.normSq (Complex.exp x)) *
      ENNReal.ofReal (‖Complex.exp x‖ ^ 2)⁻¹ = 1 := by
    intro x
    rw [← ENNReal.ofReal_mul (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
      mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (Complex.exp_ne_zero x))), ENNReal.ofReal_one]
  simp_rw [this]
  simp

/-- **Idele side, real place**: `∫_{exp(J)} dx/|x| = vol(J)`. -/
theorem lintegral_exp_image_real {J : Set ℝ} (hJ : MeasurableSet J) :
    ∫⁻ x in Real.exp '' J, ENNReal.ofReal |x|⁻¹ = volume J := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hJ
    (f := Real.exp) (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ (Real.exp x))
    (fun x _ => (Real.hasDerivAt_exp x).hasFDerivAt.hasFDerivWithinAt)
    Real.exp_injective.injOn (fun x => ENNReal.ofReal |x|⁻¹)
  rw [h]
  have : ∀ x : ℝ, ENNReal.ofReal |(ContinuousLinearMap.toSpanSingleton ℝ (Real.exp x)).det| * ENNReal.ofReal |Real.exp x|⁻¹ = 1 := by
    intro x
    have hd : (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp x)).det = Real.exp x := by
      have : ContinuousLinearMap.toSpanSingleton ℝ (Real.exp x) = Real.exp x • (1 : ℝ →L[ℝ] ℝ) := by
        ext; simp
      rw [this, ContinuousLinearMap.det]
      simp
    rw [hd, ← ENNReal.ofReal_mul (abs_nonneg _), mul_inv_cancel₀ (abs_pos.mpr (Real.exp_pos x).ne').ne',
      ENNReal.ofReal_one]
  simp_rw [this]
  simp

/-! ### Gram data of `⟨c⟩` and `⟨1, D⟩` over `ℂ` -/

section Gram

theorem gramC_diag_one_iso (c : ℂ) : gramC (QuadForm.diag ![c]) = !![c] := by
  ext i j; fin_cases i; fin_cases j; simp [gramC, QuadForm.hessian, QuadForm.diag]; ring

theorem gramDetC_diag_one_iso (c : ℂ) : gramDetC (QuadForm.diag ![c]) = c := by
  rw [gramDetC, gramC_diag_one_iso, Matrix.det_fin_one_of]

theorem gramDetC_diag_one_ne_zero_iso {c : ℂ} (hc : c ≠ 0) : gramDetC (QuadForm.diag ![c]) ≠ 0 := by
  rwa [gramDetC_diag_one_iso]

theorem gramC_diag_one_D_iso (D : ℂ) : gramC (QuadForm.diag ![1, D]) = !![1, 0; 0, D] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gramC, QuadForm.hessian, QuadForm.diag] <;> ring

theorem gramDetC_diag_one_D_iso (D : ℂ) : gramDetC (QuadForm.diag ![1, D]) = D := by
  rw [gramDetC, gramC_diag_one_D_iso, Matrix.det_fin_two_of]; ring

theorem gramDetC_diag_one_D_ne_zero_iso {D : ℂ} (hD : D ≠ 0) : gramDetC (QuadForm.diag ![1, D]) ≠ 0 := by
  rwa [gramDetC_diag_one_D_iso]

theorem diag_one_D_eq_splitFormC_iso (D : ℂ) :
    QuadForm.diag ![1, D] = splitForm 1 (QuadForm.diag ![D]) := by
  have h : (QuadForm.diag ![1, D]).coeff = (splitForm (1 : ℂ) (QuadForm.diag ![D])).coeff := by
    rw [splitForm_coeff]
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  cases h' : QuadForm.diag ![1, D]
  cases h'' : splitForm (1 : ℂ) (QuadForm.diag ![D])
  rw [h', h''] at h
  simp only at h
  subst h
  rfl

end Gram

/-! ### The hyperbola over `ℂ` -/

section Hyp

/-- The form `x₀² - x₁²` over `ℂ`. -/
abbrev QH : QuadForm ℂ 2 := QuadForm.diag ![1, -1]

theorem eval_diag_one_DC (D : ℂ) (x : Fin 2 → ℂ) : (QuadForm.diag ![1, D]).eval x = x 0 ^ 2 + D * x 1 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two]; ring

/-- The point `γ(w) = (cosh w, sinh w)`. -/
def hypVecC (w : ℂ) : Fin 2 → ℂ := ![Complex.cosh w, Complex.sinh w]

theorem hypVecC_mem (w : ℂ) : hypVecC w ∈ sphC QH 1 := by
  change QH.eval (hypVecC w) = 1
  rw [eval_diag_one_DC]
  simp only [hypVecC, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.cosh_sq]; ring

/-- `γ(w)` as a point of `S_1`. -/
def hypArcC (w : ℂ) : SphC QH 1 := ⟨hypVecC w, hypVecC_mem w⟩

theorem continuous_hypArcC : Continuous hypArcC := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [hypVecC]; fun_prop
  · simp only [hypVecC]; fun_prop

theorem hypArcC_injOn : InjOn hypArcC isoSqC := by
  intro w hw w' hw' h
  have h0 := congrArg (fun x : SphC QH 1 => (x : Fin 2 → ℂ) 0) h
  have h1 := congrArg (fun x : SphC QH 1 => (x : Fin 2 → ℂ) 1) h
  simp only [hypArcC, hypVecC, Matrix.cons_val_one, Matrix.cons_val_zero] at h0 h1
  apply exp_injOn_isoSqC hw hw'
  rw [← Complex.cosh_add_sinh w, ← Complex.cosh_add_sinh w', h0, h1]

/-- The map `Φ(β, w) = β γ(w)`. -/
def hypPhiC (p : ℂ × ℂ) : ℂ × ℂ := (p.1 * Complex.cosh p.2, p.1 * Complex.sinh p.2)

/-- Its complex derivative. -/
def hypPhiDC (p : ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  ((Complex.cosh p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ + (p.1 * Complex.sinh p.2) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((Complex.sinh p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ + (p.1 * Complex.cosh p.2) • ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem hasFDerivAt_hypPhiC (p : ℂ × ℂ) : HasFDerivAt hypPhiC (hypPhiDC p) p := by
  have hc : HasFDerivAt (fun q : ℂ × ℂ => Complex.cosh q.2) (Complex.sinh p.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
    (Complex.hasDerivAt_cosh p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have hs : HasFDerivAt (fun q : ℂ × ℂ => Complex.sinh q.2) (Complex.cosh p.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
    (Complex.hasDerivAt_sinh p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have h1 : HasFDerivAt (fun q : ℂ × ℂ => q.1 * Complex.cosh q.2) _ p := (hasFDerivAt_fst).mul hc
  have h2 : HasFDerivAt (fun q : ℂ × ℂ => q.1 * Complex.sinh q.2) _ p := (hasFDerivAt_fst).mul hs
  refine (h1.prodMk h2).congr_fderiv ?_
  ext <;> simp [hypPhiDC]

theorem det_hypPhiDC (p : ℂ × ℂ) : ((hypPhiDC p).restrictScalars ℝ).det = Complex.normSq p.1 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, det_restrictScalars_complex]
  have : LinearMap.det (hypPhiDC p : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ) = p.1 := by
    rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℂ), Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, hypPhiDC, Module.Basis.finTwoProd]
    linear_combination p.1 * Complex.cosh_sq p.2
  rw [this]

theorem injOn_hypPhiC : InjOn hypPhiC ({β : ℂ | 0 < β.re} ×ˢ isoSqC) := by
  rintro ⟨β, w⟩ ⟨hβ, hw⟩ ⟨β', w'⟩ ⟨hβ', hw'⟩ h
  simp only [hypPhiC, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  change 0 < β.re at hβ
  change 0 < β'.re at hβ'
  have hsq : β ^ 2 = β' ^ 2 := by
    have isoE1 := Complex.cosh_sq w
    have e2 := Complex.cosh_sq w'
    calc β ^ 2 = (β * Complex.cosh w) ^ 2 - (β * Complex.sinh w) ^ 2 := by linear_combination (-β ^ 2) * isoE1
      _ = (β' * Complex.cosh w') ^ 2 - (β' * Complex.sinh w') ^ 2 := by rw [h1, h2]
      _ = β' ^ 2 := by linear_combination (β' ^ 2) * e2
  have hbb : β = β' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exfalso; rw [h] at hβ; simp at hβ; linarith
  subst hbb
  have hb0 : β ≠ 0 := fun h => by rw [h] at hβ; simp at hβ
  have hc := mul_left_cancel₀ hb0 h1
  have hs := mul_left_cancel₀ hb0 h2
  have : w = w' := by
    apply exp_injOn_isoSqC hw hw'
    rw [← Complex.cosh_add_sinh w, ← Complex.cosh_add_sinh w', hc, hs]
  rw [this]

end Hyp

/-! ### The Leray measure of an arc of the complex hyperbola -/

section HypArc

/-- The sector `R₀ = {Re β > 0, |β| < 1}` as a subset of `ℂ`. -/
def R0c_iso : Set ℂ := {β | 0 < β.re ∧ ‖β‖ < 1}

theorem isOpen_R0c : IsOpen R0c_iso :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_norm continuous_const)

theorem image_R0 : Units.val '' R0 = R0c_iso := by
  have : R0 = Units.val ⁻¹' R0c_iso := rfl
  rw [this, image_preimage_eq_inter_range, range_val]
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
  intro h h0
  rw [h0] at h
  simp [R0c_iso] at h

theorem lamU_two_R0_iso : lamU 2 R0 = ∫⁻ z in R0c_iso, ENNReal.ofReal (Complex.normSq z) := by
  have hme : MeasurableEmbedding (Units.val : ℂˣ → ℂ) := SphereLerayC.measurableEmbedding_val
  have hG : ∀ β : ℂˣ, SphereLerayC.wt (2 * ((2 : ℕ) : ℤ) - 2) β = ENNReal.ofReal (Complex.normSq (β : ℂ)) := by
    intro β
    rw [SphereLerayC.wt, Complex.normSq_eq_norm_sq, ← ENNReal.ofReal_coe_nnreal]
    norm_num
  rw [lamU, withDensity_apply _ isOpen_R0.measurableSet]
  simp_rw [hG]
  rw [volU, hme.restrict_comap, image_R0]
  rw [← hme.lintegral_map (fun z => ENNReal.ofReal (Complex.normSq z)), hme.map_comap,
    Measure.restrict_eq_self_of_ae_mem]
  refine ae_restrict_of_forall_mem isOpen_R0c.measurableSet fun z hz => ?_
  rw [range_val]
  intro h0
  rw [h0] at hz
  simp [R0c_iso] at hz

theorem volume_hypPhiC_image {J : Set ℂ} (hJ : MeasurableSet J) (hJs : J ⊆ isoSqC) :
    volume (hypPhiC '' (R0c_iso ×ˢ J)) = lamU 2 R0 * volume J := by
  have hS : MeasurableSet (R0c_iso ×ˢ J) := isOpen_R0c.measurableSet.prod hJ
  have hsub : R0c_iso ×ˢ J ⊆ {β : ℂ | 0 < β.re} ×ˢ isoSqC := prod_mono (fun _ h => h.1) hJs
  rw [Measure.volume_eq_prod]
  have hJac := lintegral_image_eq_lintegral_abs_det_fderiv_mul ((volume : Measure ℂ).prod volume) hS
    (f := hypPhiC) (f' := fun p => (hypPhiDC p).restrictScalars ℝ)
    (fun p _ => ((hasFDerivAt_hypPhiC p).restrictScalars ℝ).hasFDerivWithinAt)
    ((injOn_hypPhiC).mono hsub) (fun _ => 1)
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul, mul_one] at hJac
  rw [hJac]
  simp_rw [det_hypPhiDC, abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [lintegral_mul_const _ (by fun_prop), lamU_two_R0_iso]

/-- The coordinates `ℂ × ℂ → ℂ²`. -/
abbrev toVec2C_iso : ℂ × ℂ ≃ᵐ (Fin 2 → ℂ) := (MeasurableEquiv.finTwoArrow).symm

theorem toVec2C_hypPhiC (p : ℂ × ℂ) : toVec2C_iso (hypPhiC p) = p.1 • hypVecC p.2 := by
  funext i; fin_cases i <;> simp [hypPhiC, hypVecC]

/-- **The Leray measure of an arc of the complex hyperbola** `x₀² - x₁² = 1`:
`σ₁(γ(J)) = vol(J) / 4` for `J` in the open square. -/
theorem sigC_hypArc {J : Set ℂ} (hJ : MeasurableSet J) (hJs : J ⊆ isoSqC) :
    sigC QH 1 (hypArcC '' J) = ENNReal.ofReal (1 / 4) * volume J := by
  have hA : MeasurableSet (hypArcC '' J) :=
    hJ.image_of_continuousOn_injOn continuous_hypArcC.continuousOn (hypArcC_injOn.mono hJs)
  rw [sigC, Measure.smul_apply, nuC_apply_volume one_ne_zero hA, smul_eq_mul]
  have himg : polC QH 1 '' (R0 ×ˢ (hypArcC '' J)) = toVec2C_iso '' (hypPhiC '' (R0c_iso ×ˢ J)) := by
    ext y
    constructor
    · rintro ⟨⟨b, x⟩, ⟨hb, ⟨w, hw, rfl⟩⟩, rfl⟩
      exact ⟨hypPhiC ((b : ℂ), w), ⟨((b : ℂ), w), ⟨hb, hw⟩, rfl⟩, by rw [toVec2C_hypPhiC]; rfl⟩
    · rintro ⟨_, ⟨⟨b, w⟩, ⟨hb, hw⟩, rfl⟩, rfl⟩
      have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp [R0c_iso] at hb
      exact ⟨(Units.mk0 b hb0, hypArcC w), ⟨hb, w, hw, rfl⟩, by rw [toVec2C_hypPhiC]; rfl⟩
  rw [himg]
  have hpres : MeasurePreserving toVec2C_iso volume volume := (volume_preserving_finTwoArrow ℂ).symm
  have hvol : ∀ X : Set (ℂ × ℂ), volume (toVec2C_iso '' X) = volume X := fun X => by
    rw [MeasurableEquiv.image_eq_preimage_symm, ← hpres.symm.measure_preimage_equiv]
  rw [hvol, volume_hypPhiC_image hJ hJs]
  have h0 : lamU 2 R0 ≠ 0 := lamU_R0_pos.ne'
  have h1 : lamU 2 R0 ≠ ⊤ := (lamU_R0_lt_top (by norm_num)).ne
  rw [← mul_assoc (lamU 2 R0)⁻¹, ENNReal.inv_mul_cancel h0 h1, one_mul]
  congr 1
  have h2 : ‖(2 : ℂ) * 1‖₊ = 2 := by simp
  rw [h2, ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
  congr 1
  apply NNReal.eq
  simp
  norm_num

end HypArc

/-! ### Rank one: the Leray measure of the trivial group `SO(⟨c⟩)(ℂ)` -/

section RankOneC

/-- The index set `UIdx 1` has one element. -/
instance uniqueUIdx1 : Unique (UIdx 1) where
  default := ⟨(0, 0), le_rfl⟩
  uniq _ := Subtype.ext (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-- Coefficient space `ℂ^{UIdx 1} ≃ ℂ`. -/
abbrev isoE1 : (UIdx 1 → ℂ) ≃ᵐ ℂ := MeasurableEquiv.funUnique (UIdx 1) ℂ

/-- Matrix space `M₁(ℂ) ≃ ℂ`. -/
abbrev isoPsi1 : (Fin 1 → Fin 1 → ℂ) ≃ᵐ ℂ :=
  (MeasurableEquiv.funUnique (Fin 1) (Fin 1 → ℂ)).trans (MeasurableEquiv.funUnique (Fin 1) ℂ)

theorem measurePreserving_e1 : MeasurePreserving isoE1 volume volume := volume_preserving_funUnique (UIdx 1) ℂ

theorem measurePreserving_ψ1 : MeasurePreserving isoPsi1 volume volume :=
  (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))

/-- The region `{X : Re det X > 0, Φ_Q(X) ∈ E}` for `Q = ⟨c⟩` in coordinates. -/
theorem regionC_diag_one (c : ℂ) (F : Set ℂ) :
    regionC (QuadForm.diag ![c]) (isoE1 ⁻¹' F) = isoPsi1 ⁻¹' {x : ℂ | 0 < x.re ∧ c * x ^ 2 ∈ F} := by
  ext X
  simp only [regionC, mem_ofPred_eq, mem_preimage]
  have h1 : (ofCols X).det = X 0 0 := by rw [Matrix.det_fin_one]; rfl
  have h2 : isoE1 (phi (QuadForm.diag ![c]) (ofCols X)) = c * (X 0 0) ^ 2 := by
    simp [phi, wtU, gramC_diag_one_iso, ArchVol.wt, Matrix.mul_apply, ofCols, Fin.fin_one_eq_zero]
    ring
  rw [h1, h2]
  rfl

/-- **Change of variables `w = c x²` on the right half plane.** -/
theorem volume_sqrt_region {c : ℂ} (hc : c ≠ 0) {F : Set ℂ} (hF : MeasurableSet F)
    (hFb : F ⊆ Metric.ball c ‖c‖) :
    volume {x : ℂ | 0 < x.re ∧ c * x ^ 2 ∈ F} = ∫⁻ y in F, ENNReal.ofReal (1 / (4 * ‖c‖ * ‖y‖)) := by
  set S : Set ℂ := {x : ℂ | 0 < x.re ∧ c * x ^ 2 ∈ F} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const Complex.measurable_re).inter (hF.preimage (by fun_prop))
  have hnz : ∀ x ∈ S, x ≠ 0 := fun x hx h0 => by have := hx.1; rw [h0] at this; simp at this
  have hinj : InjOn (fun x : ℂ => c * x ^ 2) S := fun x hx x' hx' h => eq_of_sq_eq_half hc hx.1 hx'.1 h
  have himg : (fun x : ℂ => c * x ^ 2) '' S = F := by
    ext y; constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
    · intro hy
      have hyb : ‖y - c‖ < ‖c‖ := by simpa [dist_eq_norm] using hFb hy
      have hre : 0 < (y / c).re := by
        have h1 : y / c = 1 + (y - c) / c := by field_simp; ring
        have h2 : ‖(y - c) / c‖ < 1 := by
          rw [norm_div, div_lt_one (norm_pos_iff.mpr hc)]; exact hyb
        have h3 := Complex.abs_re_le_norm ((y - c) / c)
        rw [h1, Complex.add_re, Complex.one_re]
        have := abs_le.mp h3
        linarith [this.1]
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y / c) (two_pos : 0 < 2)
      have hz2 : z ^ 2 = y / c := hz
      have hrz : z.re ≠ 0 := by
        intro h0
        have : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
        rw [hz2, h0] at this
        nlinarith [sq_nonneg z.im]
      have hyc : c * (y / c) = y := by field_simp
      rcases lt_or_gt_of_ne hrz with hneg | hpos
      · refine ⟨-z, ⟨by simpa using hneg, ?_⟩, ?_⟩
        · rw [neg_sq, hz2, hyc]; exact hy
        · simp only [neg_sq, hz2, hyc]
      · refine ⟨z, ⟨hpos, ?_⟩, ?_⟩
        · rw [hz2, hyc]; exact hy
        · simp only [hz2, hyc]
  have hder : ∀ x ∈ S, HasDerivAt (fun x : ℂ => c * x ^ 2) (2 * c * x) x := fun x _ => by
    have := (hasDerivAt_pow 2 x).const_mul c
    convert this using 1
    simp; ring
  have hJ := lintegral_image_holo hS hder hinj (fun y => ENNReal.ofReal (1 / (4 * ‖c‖ * ‖y‖)))
  rw [himg] at hJ
  rw [hJ, ← Measure.restrict_apply_univ, ← lintegral_one]
  refine setLIntegral_congr_fun hS fun x hx => ?_
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (hnz x hx)
  have hc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← ENNReal.ofReal_mul (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, norm_mul, norm_mul]
  rw [norm_mul c, norm_pow, Complex.norm_ofNat, ← ENNReal.ofReal_one]
  congr 1
  field_simp
  norm_num

theorem e1_symm_apply (w : ℂ) : isoE1.symm w = fun _ => w := by
  funext i; rw [Subsingleton.elim i default]; rfl

theorem continuous_e1_symm : Continuous isoE1.symm := by
  have : (isoE1.symm : ℂ → UIdx 1 → ℂ) = fun w _ => w := funext e1_symm_apply
  rw [this]; exact continuous_pi fun _ => continuous_id

/-- Averages over small closed balls converge to the value at a point of continuity. -/
theorem tendsto_avg_closedBall {h : ℂ → ℝ≥0∞} {c : ℂ} (hh : ContinuousAt h c) :
    Tendsto (fun r : ℝ => (∫⁻ w in Metric.closedBall c r, h w) / volume (Metric.closedBall c r)) (𝓝[>] 0)
      (𝓝 (h c)) := by
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨b, hab, hbc⟩ := exists_between ha'
    have hev : ∀ᶠ w in 𝓝 c, b < h w := hh.eventually (lt_mem_nhds hbc)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hV0 : volume (Metric.closedBall c r) ≠ 0 := (Metric.measure_closedBall_pos volume c hr.1).ne'
    have hVt : volume (Metric.closedBall c r) ≠ ⊤ := measure_closedBall_lt_top.ne
    refine lt_of_lt_of_le hab ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVt)]
    calc b * volume (Metric.closedBall c r) = ∫⁻ w in Metric.closedBall c r, b := (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun w hw =>
          (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hr.2)).le
  · intro a' ha'
    obtain ⟨b, hcb, hba⟩ := exists_between ha'
    have hev : ∀ᶠ w in 𝓝 c, h w < b := hh.eventually (gt_mem_nhds hcb)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    refine lt_of_le_of_lt ?_ hba
    apply ENNReal.div_le_of_le_mul
    calc _ ≤ ∫⁻ w in Metric.closedBall c r, b := setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
          fun w hw => (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hr.2)).le
      _ = _ := setLIntegral_const _ _

/-- **The Leray measure of the trivial group `SO(⟨c⟩)(ℂ)`** is the point mass `1/‖2c‖²`. -/
theorem lerayMeasureC_diag_one_univ_iso {c : ℂ} (hc : c ≠ 0) :
    lerayMeasureC (QuadForm.diag ![c]) (gramDetC_diag_one_ne_zero_iso hc) univ =
      ENNReal.ofReal (1 / ‖2 * c‖ ^ 2) := by
  set Q : QuadForm ℂ 1 := QuadForm.diag ![c] with hQdef
  have hQ := gramDetC_diag_one_ne_zero_iso hc
  set D := DiagC.ofExists Q hQ
  set m := lerayMeasureC Q hQ univ with hm
  set a : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (rho D (isoE1.symm w)) with ha
  set g : ℂ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 / (4 * ‖c‖ * ‖y‖)) with hg
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcoeff : isoE1.symm c = coeffUC Q := by
    funext p
    simp [coeffUC, hQdef, QuadForm.diag, Fin.fin_one_eq_zero]
  have hmem : isoE1.symm c ∈ U0 D := by rw [hcoeff]; exact coeffUC_mem_U0 D
  have hcont_a : ContinuousAt a c := by
    have h1 : ContinuousAt (rho D) (isoE1.symm c) :=
      (continuousOn_rho D).continuousAt ((isOpen_U0 D).mem_nhds hmem)
    exact ENNReal.continuous_ofReal.continuousAt.comp (h1.comp continuous_e1_symm.continuousAt)
  have ha_c : a c = 1 := by
    show ENNReal.ofReal (rho D (isoE1.symm c)) = 1
    rw [hcoeff, rho_coeffUC]; simp
  have hcont_g : ContinuousAt g c := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    exact (continuousAt_const.div (continuousAt_const.mul continuous_norm.continuousAt)
      (mul_ne_zero (mul_ne_zero four_ne_zero hc0.ne') hc0.ne'))
  have hg_c : g c = ENNReal.ofReal (1 / ‖2 * c‖ ^ 2) := by
    simp only [hg]
    congr 1
    rw [norm_mul, Complex.norm_ofNat]
    field_simp
    ring
  have hU : isoE1.symm ⁻¹' U0 D ∈ 𝓝 c := (isOpen_U0 D).preimage continuous_e1_symm |>.mem_nhds hmem
  obtain ⟨δ1, hδ1, hball1⟩ := Metric.mem_nhds_iff.mp hU
  have key : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∫⁻ w in Metric.closedBall c r, g w) =
      (∫⁻ w in Metric.closedBall c r, a w) * m := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ1 hc0)] with r hr
    have hr1 : r < δ1 := hr.2.trans_le (min_le_left _ _)
    have hr2 : r < ‖c‖ := hr.2.trans_le (min_le_right _ _)
    have hF : MeasurableSet (Metric.closedBall c r) := Metric.isClosed_closedBall.measurableSet
    have hFb : Metric.closedBall c r ⊆ Metric.ball c ‖c‖ := Metric.closedBall_subset_ball hr2
    have hE : MeasurableSet (isoE1 ⁻¹' Metric.closedBall c r) := hF.preimage isoE1.measurable
    have hEU : isoE1 ⁻¹' Metric.closedBall c r ⊆ U0 D := fun y hy => by
      have : isoE1 y ∈ isoE1.symm ⁻¹' U0 D := hball1 (Metric.closedBall_subset_ball hr1 hy)
      rwa [mem_preimage, isoE1.symm_apply_apply] at this
    have hreg := lerayMeasureC_region (hQ := hQ) D (φ := fun _ => 1) measurable_const hE hEU
    rw [regionC_diag_one] at hreg
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at hreg
    rw [measurePreserving_ψ1.measure_preimage_equiv, volume_sqrt_region hc hF hFb] at hreg
    rw [hreg]
    have hae : AEMeasurable (fun y => ENNReal.ofReal (rho D y)) (volume.restrict (isoE1 ⁻¹' Metric.closedBall c r)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (((continuousOn_rho D).mono hEU).aemeasurable hE)
    rw [lintegral_mul_const'' _ hae]
    congr 1
    have := measurePreserving_e1.setLIntegral_comp_preimage_emb isoE1.measurableEmbedding a (Metric.closedBall c r)
    rw [← this]
    simp only [ha, isoE1.symm_apply_apply]
  have tg := tendsto_avg_closedBall hcont_g
  have ta := tendsto_avg_closedBall hcont_a
  have ta' := ENNReal.Tendsto.const_mul ta (Or.inl (by rw [ha_c]; exact one_ne_zero) : a c ≠ 0 ∨ m ≠ ⊤)
  have tg' : Tendsto (fun r : ℝ => m * ((∫⁻ w in Metric.closedBall c r, a w) / volume (Metric.closedBall c r)))
      (𝓝[>] 0) (𝓝 (g c)) :=
    tg.congr' (key.mono fun r hr => by rw [hr, mul_comm, mul_div_assoc])
  have := tendsto_nhds_unique ta' tg'
  rw [ha_c, mul_one, hg_c] at this
  exact this

end RankOneC


/-! ### Rotations over `ℂ` -/

section Rot

variable {D : ℂ}

/-- The rotation matrix `!![a, -D b; b, a]`. -/
def rotMatC (D a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, -(D * b); b, a]

/-- Its inverse (for `a² + D b² = 1`). -/
def rotMatInvC (D a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, D * b; -b, a]

theorem norm_one_of_sphC_iso (u : SphC (QuadForm.diag ![1, D]) 1) :
    (u : Fin 2 → ℂ) 0 ^ 2 + D * (u : Fin 2 → ℂ) 1 ^ 2 = 1 := by
  have h : (QuadForm.diag ![1, D]).eval (u : Fin 2 → ℂ) = 1 := u.2
  rwa [eval_diag_one_DC] at h

theorem rotMatC_mul_inv {a b : ℂ} (h : a ^ 2 + D * b ^ 2 = 1) : rotMatC D a b * rotMatInvC D a b = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMatC, rotMatInvC, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h

theorem rotMatC_inv_mul {a b : ℂ} (h : a ^ 2 + D * b ^ 2 = 1) : rotMatInvC D a b * rotMatC D a b = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMatC, rotMatInvC, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h

/-- The rotation with first column `u ∈ S_1`, in `GL₂(ℂ)`. -/
def rotGLC_iso (D : ℂ) (u : SphC (QuadForm.diag ![1, D]) 1) : GL (Fin 2) ℂ :=
  ⟨rotMatC D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1), rotMatInvC D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1),
    rotMatC_mul_inv (norm_one_of_sphC_iso u), rotMatC_inv_mul (norm_one_of_sphC_iso u)⟩

theorem rotGLC_mem_iso (u : SphC (QuadForm.diag ![1, D]) 1) : rotGLC_iso D u ∈ soC (QuadForm.diag ![1, D]) := by
  have h := norm_one_of_sphC_iso u
  rw [mem_soC_iff]
  refine ⟨?_, ?_⟩
  · change (rotMatC D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1))ᵀ * gramC (QuadForm.diag ![1, D]) *
      rotMatC D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) = gramC (QuadForm.diag ![1, D])
    rw [gramC_diag_one_D_iso]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotMatC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
      first | ring1 | linear_combination h | linear_combination D * h
  · change (rotMatC D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1)).det = 1
    rw [rotMatC, Matrix.det_fin_two_of]; linear_combination h

/-- **The rotation section** `S_1 → SO(⟨1, D⟩)(ℂ)`, `u ↦ !![u₀, -D u₁; u₁, u₀]`. -/
def rotSecC_iso (D : ℂ) (u : SphC (QuadForm.diag ![1, D]) 1) : ArchSOC (QuadForm.diag ![1, D]) :=
  ArchSOC.mk _ (rotGLC_iso D u) (rotGLC_mem_iso u)

theorem mat_rotSecC_iso (u : SphC (QuadForm.diag ![1, D]) 1) :
    ArchSOC.mat _ (rotSecC_iso D u) = !![(u : Fin 2 → ℂ) 0, -(D * (u : Fin 2 → ℂ) 1); (u : Fin 2 → ℂ) 1, (u : Fin 2 → ℂ) 0] :=
  rfl

theorem continuous_rotSecC_iso : Continuous (rotSecC_iso D) := by
  have h0 : Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℂ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℂ) 1 :=
    (continuous_apply 1).comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · change Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 =>
      rotMatC D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [rotMatC] <;>
      first | exact h0 | exact h1 | exact (continuous_const.mul h1).neg
  · change Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 =>
      rotMatInvC D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [rotMatInvC] <;>
      first | exact h0 | exact h1.neg | exact continuous_const.mul h1

theorem rotSecC_spec_iso (u : SphC (QuadForm.diag ![1, D]) 1) :
    ArchSOC.mat _ (rotSecC_iso D u) *ᵥ (e₀ : Fin 2 → ℂ) = (u : Fin 2 → ℂ) := by
  rw [mat_rotSecC_iso]
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e₀]

/-- The embedding `SO(⟨D⟩) → SO(⟨1, D⟩)`, `h ↦ diag(1, h)`. -/
def iotaC1_iso (D : ℂ) (h : ArchSOC (QuadForm.diag ![D])) : ArchSOC (QuadForm.diag ![1, D]) :=
  ArchSOC.mk _ (blockGL (ArchSOC.incl _ h)) (by
    rw [diag_one_D_eq_splitFormC_iso]; exact blockGL_mem_soC 1 _ (ArchSOC.incl_mem _ h))

theorem mat_iotaC1_iso (h : ArchSOC (QuadForm.diag ![D])) :
    ArchSOC.mat _ (iotaC1_iso D h) = cornerMat 1 (ArchSOC.mat _ h) := by
  change ((blockGL (ArchSOC.incl _ h) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [blockGL_val]; rfl

/-- `SO(⟨D⟩)(ℂ)` is trivial. -/
theorem archSOC_one_eq_one (h : ArchSOC (QuadForm.diag ![D])) : ArchSOC.mat _ h = 1 := by
  have hdet := ArchSOC.det_mat _ h
  rw [Matrix.det_fin_one] at hdet
  ext i j; fin_cases i; fin_cases j
  exact hdet

theorem iotaC1_eq_one_iso (h : ArchSOC (QuadForm.diag ![D])) : iotaC1_iso D h = 1 := by
  apply Subtype.ext; apply Units.ext
  change ArchSOC.mat _ (iotaC1_iso D h) = 1
  rw [mat_iotaC1_iso, archSOC_one_eq_one, cornerMat_one]

/-- **The Leray measure of the rotations by `A ⊆ S_1`** over `ℂ`:
`μ_{⟨1,D⟩}(ρ(A)) = σ₁(A) / (16 ‖D‖²)`. -/
theorem lerayMeasureC_rotSecC_image_iso (hD : D ≠ 0) {A : Set (SphC (QuadForm.diag ![1, D]) 1)}
    (hA : MeasurableSet A) :
    lerayMeasureC (QuadForm.diag ![1, D]) (gramDetC_diag_one_D_ne_zero_iso hD) (rotSecC_iso D '' A) =
      ENNReal.ofReal (1 / (16 * ‖D‖ ^ 2)) * sigC (QuadForm.diag ![1, D]) 1 A := by
  have h := lerayMeasureC_image_sec (m := 1) one_ne_zero (gramDetC_diag_one_ne_zero_iso hD) (QuadForm.diag ![1, D])
    (diag_one_D_eq_splitFormC_iso D) (gramDetC_diag_one_D_ne_zero_iso hD) (rotSecC_iso D) continuous_rotSecC_iso.measurable
    rotSecC_spec_iso (iotaC1_iso D) mat_iotaC1_iso hA MeasurableSet.univ
  have himg : (fun p : SphC (QuadForm.diag ![1, D]) 1 × ArchSOC (QuadForm.diag ![D]) =>
      rotSecC_iso D p.1 * iotaC1_iso D p.2) '' (A ×ˢ univ) = rotSecC_iso D '' A := by
    ext g
    constructor
    · rintro ⟨⟨u, h⟩, ⟨hu, -⟩, rfl⟩
      exact ⟨u, hu, by simp [iotaC1_eq_one_iso]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u, 1), ⟨hu, mem_univ _⟩, by simp [iotaC1_eq_one_iso]⟩
  rw [himg, lerayMeasureC_diag_one_univ_iso hD] at h
  rw [h, mul_comm (sigC _ _ A), ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hD' : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  rw [norm_mul]
  push_cast
  simp only [mul_one, Complex.norm_ofNat]
  field_simp
  ring

end Rot

/-- **The Leray measure of the rotations by an arc of the complex hyperbola**:
`μ_{⟨1,-1⟩}(ρ(γ(J))) = vol(J) / 64` for measurable `J` in the open square. -/
theorem lerayMeasureC_rotSecC_hypArc {J : Set ℂ} (hJ : MeasurableSet J) (hJs : J ⊆ isoSqC) :
    lerayMeasureC QH (gramDetC_diag_one_D_ne_zero_iso (D := -1) (neg_ne_zero.mpr one_ne_zero))
        (rotSecC_iso (-1) '' (hypArcC '' J)) = ENNReal.ofReal (1 / 64) * volume J := by
  have hA : MeasurableSet (hypArcC '' J) :=
    hJ.image_of_continuousOn_injOn continuous_hypArcC.continuousOn (hypArcC_injOn.mono hJs)
  rw [lerayMeasureC_rotSecC_image_iso (neg_ne_zero.mpr one_ne_zero) hA, sigC_hypArc hJ hJs, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  simp only [norm_neg, norm_one]
  norm_num


end QuadFormsKB.Tamagawa.Measure.Weil
