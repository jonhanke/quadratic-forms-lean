import QuadFormsKB.Tamagawa.Measure.Weil.PDArchReal
import QuadFormsKB.Tamagawa.Measure.LerayUnimodularC

/-!
# The archimedean comparison at a complex place

**Layer:** $A, B \in \mathbb C^\times$, $D_w = (A,B)_{\mathbb C} \cong M_2(\mathbb C)$, $Q = \langle -A, -B, AB\rangle$,
$\mu_Q$ = the Leray measure on $SO(Q)(\mathbb C)$ (real Lebesgue measures $dX$, $dc$; $|z|_{\mathbb C} = |z|^2$).

**Proves** `tendsto_lerayC_quatBall`: in the quaternion chart $y \mapsto c(1+y)$ ($y \in \mathbb C^3$),
$$\frac{\mu_Q\big(c(1 + B_\delta)\big)}{\mathrm{vol}(B_\delta)} \longrightarrow \frac{1}{|8A^3B^3|_{\mathbb C}}
  = \frac{1}{|8A^3B^3|^2}\qquad(\delta\to0^+).$$

*Proof.* As at the real places (`PDArchReal`), with the fibre-counting fibration (`lerayMeasureC_fibration`), which is
an ordinary pull-back on the injectivity neighbourhood $V_0$ of the slice group, and complex determinants
($\det_{\mathbb R} = |\det_{\mathbb C}|^2$, `det_restrictScalars_complex`; the density of $\kappa_0$ is
$|\det b|^{-2}$ by `det_act`).
-/

open Matrix MeasureTheory Set Metric Filter Topology Quaternion
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### Injectivity of the quaternion chart (any field) -/

section Generic

variable {K : Type*} [Field K] {A B : K}

/-- **The quaternion chart is injective**: $c(1+y) = c(1+y')$ forces $y = y'$ (the kernel of conjugation is the centre). -/
theorem cMat_injective (h2 : (2 : K) ≠ 0) (hA : A ≠ 0) {y y' : Fin 3 → K} (hy : 1 + qPure A B y ≠ 0)
    (hy' : 1 + qPure A B y' ≠ 0) (h : cMat A B y = cMat A B y') : y = y' := by
  set u := unitOneAdd A B y hy
  set u' := unitOneAdd A B y' hy'
  have hc : conjSO u = conjSO u' := by
    apply Subtype.ext; apply Units.ext
    rw [coe_conjSO, coe_conjSO]
    change ((conjGL u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((conjGL u' : GL (Fin 3) K) : Matrix _ _ K)
    rw [conjGL_eq_cMat A B u y rfl, conjGL_eq_cMat A B u' y' rfl, h]
  have hk : u'⁻¹ * u ∈ (conjSO : (ℍ[K,A,B])ˣ →* SO (pureForm A B)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hc, inv_mul_cancel]
  rw [ker_conjSO h2 hA, mem_centerUnits] at hk
  obtain ⟨r, hr⟩ := hk
  have hu : (u : ℍ[K,A,B]) = (u' : ℍ[K,A,B]) * (r : ℍ[K,A,B]) := by
    rw [← hr, ← Units.val_mul, mul_inv_cancel_left]
  rw [val_unitOneAdd, val_unitOneAdd] at hu
  have hre := congrArg QuaternionAlgebra.re hu
  have hI := congrArg QuaternionAlgebra.imI hu
  have hJ := congrArg QuaternionAlgebra.imJ hu
  have hK := congrArg QuaternionAlgebra.imK hu
  simp [Quat.pure] at hre hI hJ hK
  have hr1 : r = 1 := by simpa using hre.symm
  subst hr1
  funext i; fin_cases i <;> simp_all

end Generic

/-! ### The complex place -/

section Complex

variable (A B : ℂ)

theorem gramC_pureForm : gramC (pureForm A B) = Matrix.diagonal ![-A, -B, A * B] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gramC, pureForm, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

variable {A B}

/-- Slice data with $P = 1$. -/
abbrev diagPureC (hA : A ≠ 0) (hB : B ≠ 0) : DiagC (pureForm A B) where
  P := 1
  d := ![-A, -B, A * B]
  hd := fun i => by fin_cases i <;> simp [hA, hB]
  hP := by simp [gramC_pureForm]

variable (hA : A ≠ 0) (hB : B ≠ 0)

local notation "D₀" => diagPureC hA hB

theorem utU_eq_utK (w : UIdx 3 → ℂ) : utU w = utK w := rfl

/-- Upper triangular coordinates on the slice group (`coordOf` for $P = 1$). -/
def coordC (x : SliceB (1 : GL (Fin 3) ℂ)) : UIdx 3 → ℂ := coordOf 1 (SliceB.mat 1 x)

theorem continuous_coordC : Continuous coordC := (continuous_coordOf 1).comp (SliceB.continuous_mat 1)

theorem matC_eq_one_add_utK (x : SliceB (1 : GL (Fin 3) ℂ)) : SliceB.mat 1 x = 1 + utK (coordC x) := by
  have h := sliceCoord_coordOf (1 : GL (Fin 3) ℂ) (SliceB.incl_mem 1 x)
  rw [sliceCoord] at h
  simp only [Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one] at h
  rw [coordC, SliceB.mat, ← utU_eq_utK]
  exact h.symm

theorem det_one_add_utK_C (w : UIdx 3 → ℂ) :
    (1 + utK w : Matrix (Fin 3) (Fin 3) ℂ).det = ∏ i : Fin 3, (1 + w ⟨(i, i), le_rfl⟩) := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [utK]
  · intro i j hij
    have hij' : j < i := hij
    simp [utK, not_le.mpr hij', Matrix.one_apply_ne (ne_of_gt hij')]

/-- The slice element $1 + U(w)$ ($\det \ne 0$). -/
def jC (w : UIdx 3 → ℂ) (hw : ∀ i : Fin 3, 1 + w ⟨(i, i), le_rfl⟩ ≠ 0) : SliceB (1 : GL (Fin 3) ℂ) :=
  SliceB.mk 1 (Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + utK w) (by
    rw [det_one_add_utK_C]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hw i)) (by
    rw [mem_sliceGroup]
    simp only [inv_one, one_mul, mul_one]
    intro i j hij
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, utK, not_le.mpr hij, Matrix.one_apply_ne (ne_of_gt hij)])

theorem matC_jC (w : UIdx 3 → ℂ) (hw : ∀ i : Fin 3, 1 + w ⟨(i, i), le_rfl⟩ ≠ 0) :
    SliceB.mat 1 (jC w hw) = 1 + utK w := rfl

theorem coordC_jC (w : UIdx 3 → ℂ) (hw : ∀ i : Fin 3, 1 + w ⟨(i, i), le_rfl⟩ ≠ 0) : coordC (jC w hw) = w := by
  rw [coordC, matC_jC, ← utU_eq_utK]
  have := coordOf_sliceCoord (1 : GL (Fin 3) ℂ) w
  rwa [sliceCoord, Units.val_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at this

theorem ne_zero_of_mem_ball {w : UIdx 3 → ℂ} {δ : ℝ} (hδ : δ ≤ 1) (hw : w ∈ ball (0 : UIdx 3 → ℂ) δ) (i : Fin 3) :
    1 + w ⟨(i, i), le_rfl⟩ ≠ 0 := by
  rw [mem_ball_zero_iff] at hw
  have h1 := (norm_le_pi_norm w ⟨(i, i), le_rfl⟩).trans_lt hw
  intro h
  have : w ⟨(i, i), le_rfl⟩ = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at h1
  linarith

/-- The slice neighbourhood $\mathcal K_\delta$. -/
def KCq (δ : ℝ) : Set (SliceB (1 : GL (Fin 3) ℂ)) := coordC ⁻¹' ball 0 δ

theorem isOpen_KCq (δ : ℝ) : IsOpen (KCq δ) := isOpen_ball.preimage continuous_coordC

theorem phiC_pureForm (M : Matrix (Fin 3) (Fin 3) ℂ) : phi (pureForm A B) M = phiK ![-A, -B, A * B] M := by
  funext p
  simp [phi, phiK, LerayComplex.wtU, gramC_pureForm]

/-- The radius below which $\mathcal K_\delta$ lies in the injectivity neighbourhood $V_0$. -/
theorem exists_KCq_subset_V0 : ∃ δV > (0 : ℝ), ∀ δ ≤ δV, KCq δ ⊆ V0 D₀ := by
  set U : Set (UIdx 3 → ℂ) :=
    (ift D₀).source ∩ {w | 0 < (1 + utK w : Matrix (Fin 3) (Fin 3) ℂ).det.re}
  have hU : IsOpen U := by
    refine (ift D₀).open_source.inter (isOpen_lt continuous_const ?_)
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    exact continuous_const.add (by rw [← funext utU_eq_utK]; exact continuous_utU)
  have h0 : (0 : UIdx 3 → ℂ) ∈ U := by
    refine ⟨zero_mem_ift_source D₀, ?_⟩
    show 0 < (1 + utK (0 : UIdx 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ).det.re
    rw [show utK (0 : UIdx 3 → ℂ) = 0 by ext i j; simp [utK]]; simp
  obtain ⟨δV, hδV, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  refine ⟨δV, hδV, fun δ hδ x hx => ?_⟩
  have hw := hball (ball_subset_ball hδ hx)
  refine ⟨hw.1, ?_⟩
  show 0 < (SliceB.mat (D₀).P x).det.re
  change 0 < (SliceB.mat 1 x).det.re
  rw [matC_eq_one_add_utK]; exact hw.2

theorem betaC_image_KCq {δ : ℝ} (hδ : δ ≤ 1) :
    LerayComplex.beta D₀ '' KCq δ = betaJ ![-A, -B, A * B] '' ball 0 δ := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨coordC x, hx, ?_⟩
    rw [LerayComplex.beta, betaJ, phiC_pureForm, ← matC_eq_one_add_utK]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨jC w (ne_zero_of_mem_ball hδ hw), ?_, ?_⟩
    · simp only [KCq, mem_preimage, coordC_jC]; exact hw
    · rw [LerayComplex.beta, betaJ, phiC_pureForm]; rfl

/-- The element $c(1+y) \in SO(Q)(\mathbb C)$. -/
def gCq (y : Fin 3 → ℂ) (h : 1 + qPure A B y ≠ 0) : ArchSOC (pureForm A B) :=
  ArchSOC.mk _ (conjGL (unitOneAdd A B y h)) (by
    rw [mem_soC_iff, gramC]
    have := (mem_SO_iff_hessian (two_ne_zero (α := ℂ))).1 (conjGL_mem (unitOneAdd A B y h))
    refine ⟨?_, this.1⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, this.2])

theorem matC_gCq (y : Fin 3 → ℂ) (h : 1 + qPure A B y ≠ 0) :
    ArchSOC.mat _ (gCq y h) = cMat A B y :=
  conjGL_eq_cMat A B _ y (val_unitOneAdd A B y h)

/-- The chart neighbourhood $\mathcal A_\delta = c(1 + B_\delta)$ in $SO(Q)(\mathbb C)$. -/
def ACq (A B : ℂ) (δ : ℝ) : Set (ArchSOC (pureForm A B)) :=
  {g | ∃ y ∈ ball (0 : Fin 3 → ℂ) δ, ArchSOC.mat _ g = cMat A B y}

theorem chartC_image {δ : ℝ} (hδ : δ ≤ rad0 A B) :
    LerayComplex.chart D₀ '' (ACq A B δ ×ˢ KCq δ) = chartF A B '' shearSet (upVecL A B) δ := by
  have hδ1 : δ ≤ 1 := hδ.trans (min_le_left _ _)
  ext X
  constructor
  · rintro ⟨⟨g, x⟩, ⟨⟨y, hy, hg⟩, hx⟩, rfl⟩
    refine ⟨(y, coordC x + upVec A B y), ⟨hy, ?_⟩, ?_⟩
    · show coordC x + upVec A B y - upVecL A B y ∈ _
      rw [upVecL_apply, add_sub_cancel_right]; exact hx
    · simp only [chartF, chartMat, add_sub_cancel_right, LerayComplex.chart]
      change colsK _ = LerayComplex.cols (ArchSOC.mat _ g * SliceB.mat 1 x)
      rw [← matC_eq_one_add_utK, hg]; rfl
  · rintro ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
    have hq : 1 + qPure A B y ≠ 0 := one_add_qPure_ne_zero A B
      ((mem_ball_zero_iff.mp hy).trans_le (hδ.trans (min_le_right _ _)))
    simp only [upVecL_apply] at hu
    refine ⟨(gCq y hq, jC (u - upVec A B y) (ne_zero_of_mem_ball hδ1 hu)), ⟨⟨y, hy, matC_gCq y hq⟩, ?_⟩, ?_⟩
    · simp only [KCq, mem_preimage, coordC_jC]; exact hu
    · simp only [LerayComplex.chart, matC_gCq, chartF, chartMat]
      rfl

/-! ### Measurability of $\mathcal A_\delta$ -/

theorem continuous_nMat_one_add (A B : ℂ) :
    Continuous fun y : Fin 3 → ℂ => colsK (nMat (1 + Quat.pure y : ℍ[ℂ,A,B])) := by
  refine continuous_pi fun j => continuous_pi fun i => ?_
  simp only [colsK]
  fin_cases i <;> fin_cases j <;> simp [nMat, imv, Quat.pure, Pi.single_apply] <;> fun_prop

theorem continuousOn_cMat {δ : ℝ} (hδ : δ ≤ rad0 A B) :
    ContinuousOn (fun y : Fin 3 → ℂ => colsK (cMat A B y)) (ball 0 δ) := by
  have hq : ContinuousOn (fun y : Fin 3 → ℂ => (1 + qPure A B y)⁻¹) (ball 0 δ) := by
    refine ContinuousOn.inv₀ (by unfold qPure; fun_prop) fun y hy => one_add_qPure_ne_zero A B
      ((mem_ball_zero_iff.mp hy).trans_le (hδ.trans (min_le_right _ _)))
  have : (fun y : Fin 3 → ℂ => colsK (cMat A B y)) =
      fun y => (1 + qPure A B y)⁻¹ • colsK (nMat (1 + Quat.pure y : ℍ[ℂ,A,B])) := by
    funext y; funext j i; simp [colsK, cMat]
  rw [this]
  exact hq.smul (continuous_nMat_one_add A B).continuousOn

include hA in
theorem measurableSet_ACq {δ : ℝ} (hδ : δ ≤ rad0 A B) : MeasurableSet (ACq A B δ) := by
  have hinj : InjOn (fun y : Fin 3 → ℂ => colsK (cMat A B y)) (ball 0 δ) := by
    intro y hy y' hy' h
    have hq : ∀ z ∈ ball (0 : Fin 3 → ℂ) δ, 1 + qPure A B z ≠ 0 := fun z hz => one_add_qPure_ne_zero A B
      ((mem_ball_zero_iff.mp hz).trans_le (hδ.trans (min_le_right _ _)))
    refine cMat_injective two_ne_zero hA (hq y hy) (hq y' hy') ?_
    ext i j; exact congrFun (congrFun h j) i
  have himg : MeasurableSet ((fun y : Fin 3 → ℂ => colsK (cMat A B y)) '' ball 0 δ) :=
    measurableSet_ball.image_of_continuousOn_injOn (continuousOn_cMat hδ) hinj
  have hpre : ACq A B δ = (fun g => colsK (ArchSOC.mat _ g)) ⁻¹' ((fun y : Fin 3 → ℂ => colsK (cMat A B y)) '' ball 0 δ) := by
    ext g
    simp only [ACq, mem_ofPred_eq, mem_preimage, mem_image]
    constructor
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by rw [h]⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, ?_⟩
      ext i j; exact (congrFun (congrFun h j) i).symm
  rw [hpre]
  have hc : Continuous fun g : ArchSOC (pureForm A B) => colsK (ArchSOC.mat _ g) :=
    continuous_pi fun j => continuous_pi fun i => (ArchSOC.continuous_mat _).matrix_elem i j
  exact himg.preimage hc.measurable

/-! ### The fibration identity and the slice factor -/

theorem sigmaFinite_kappa0C {n : ℕ} {Q : QuadForm ℂ n} (D : DiagC Q) : SigmaFinite (kappa0 D) := inferInstance

theorem leray_mul_kappa0C (hQ : gramDetC (pureForm A B) ≠ 0) {δ : ℝ} (hKV : KCq δ ⊆ V0 D₀)
    (hδ : δ ≤ rad0 A B) :
    lerayMeasureC (pureForm A B) hQ (ACq A B δ) * kappa0 D₀ (KCq δ) =
      volume ((fun p => eMatE (chartF A B p)) '' shearSet (upVecL A B) δ) := by
  have := sigmaFinite_kappa0C D₀
  have hS : MeasurableSet (ACq A B δ ×ˢ KCq δ) := (measurableSet_ACq hA hδ).prod (isOpen_KCq δ).measurableSet
  have hinj : InjOn (LerayComplex.chart D₀) (ACq A B δ ×ˢ KCq δ) :=
    (injOn_chart D₀ (injOn_beta_V0 D₀)).mono (prod_mono (subset_univ _) hKV)
  rw [← Measure.prod_prod, ← lerayMeasureC_fibration hQ D₀,
    Leray.fibreCount_apply_of_injOn (continuous_chart D₀) (isLocInj_chart D₀) volume hS hinj,
    chartC_image hA hB hδ, ← volume_image_eMatE, image_image]

theorem thetaBC_eq (x : SliceB (1 : GL (Fin 3) ℂ)) :
    (LerayComplex.thetaB D₀ x : ℝ≥0∞) = ((‖(SliceB.mat 1 x).det‖₊ ^ 2)⁻¹ : ℝ≥0) := by
  have hd : ‖(SliceB.mat 1 x).det‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (SliceB.det_mat_ne_zero 1 x)
  congr 1
  change LerayComplex.chiB D₀ x * (LerayComplex.JB D₀ x)⁻¹ = _
  simp only [LerayComplex.chiB, LerayComplex.JB, MonoidHom.coe_mk, OneHom.coe_mk, det_act, nnnorm_pow]
  change ‖(SliceB.mat 1 x).det‖₊ ^ (2 * 3) * ((‖(SliceB.mat 1 x).det‖₊ ^ (3 + 1)) ^ 2)⁻¹ = _
  rw [← pow_mul, show (3 + 1) * 2 = 2 * 3 + 2 by norm_num, pow_add, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hd), one_mul]

theorem thetaBC_bounds {δ : ℝ} (hδ1 : δ < 1) {x : SliceB (1 : GL (Fin 3) ℂ)} (hx : x ∈ KCq δ) :
    ENNReal.ofReal ((1 + δ) ^ 6)⁻¹ ≤ (LerayComplex.thetaB D₀ x : ℝ≥0∞) ∧
      (LerayComplex.thetaB D₀ x : ℝ≥0∞) ≤ ENNReal.ofReal ((1 - δ) ^ 6)⁻¹ := by
  have hw : coordC x ∈ ball (0 : UIdx 3 → ℂ) δ := hx
  have hb : ∀ i : Fin 3, ‖coordC x ⟨(i, i), le_rfl⟩‖ < δ := fun i => by
    rw [mem_ball_zero_iff] at hw
    exact (norm_le_pi_norm (coordC x) ⟨(i, i), le_rfl⟩).trans_lt hw
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hb 0).le
  have hpos : 0 < 1 - δ := by linarith
  have hn : ∀ i : Fin 3, 1 - δ ≤ ‖1 + coordC x ⟨(i, i), le_rfl⟩‖ ∧ ‖1 + coordC x ⟨(i, i), le_rfl⟩‖ ≤ 1 + δ := by
    intro i
    constructor
    · have := norm_sub_norm_le (1 : ℂ) (-coordC x ⟨(i, i), le_rfl⟩)
      rw [sub_neg_eq_add, norm_one, norm_neg] at this
      linarith [hb i]
    · have := norm_add_le (1 : ℂ) (coordC x ⟨(i, i), le_rfl⟩)
      rw [norm_one] at this; linarith [hb i]
  set N := ‖(SliceB.mat 1 x).det‖ with hNdef
  have hN : N = ‖1 + coordC x ⟨(0, 0), le_rfl⟩‖ * ‖1 + coordC x ⟨(1, 1), le_rfl⟩‖ *
      ‖1 + coordC x ⟨(2, 2), le_rfl⟩‖ := by
    rw [hNdef, matC_eq_one_add_utK, det_one_add_utK_C, Fin.prod_univ_three, norm_mul, norm_mul]
  obtain ⟨l0, u0⟩ := hn 0; obtain ⟨l1, u1⟩ := hn 1; obtain ⟨l2, u2⟩ := hn 2
  have hlo : (1 - δ) ^ 3 ≤ N := by
    rw [hN]
    have := mul_le_mul (mul_le_mul l0 l1 hpos.le (hpos.le.trans l0)) l2 hpos.le
      (mul_nonneg (hpos.le.trans l0) (hpos.le.trans l1))
    nlinarith
  have hhi : N ≤ (1 + δ) ^ 3 := by
    rw [hN]
    have := mul_le_mul (mul_le_mul u0 u1 (norm_nonneg _) (by linarith)) u2 (norm_nonneg _) (by nlinarith)
    nlinarith
  have hNp : 0 < N := lt_of_lt_of_le (by positivity) hlo
  have hθ : (LerayComplex.thetaB D₀ x : ℝ≥0∞) = ENNReal.ofReal (N ^ 2)⁻¹ := by
    rw [thetaBC_eq, ENNReal.ofReal, Real.toNNReal_inv]
    congr 2
    rw [← NNReal.coe_inj, NNReal.coe_pow, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  rw [hθ]
  constructor
  · refine ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) ?_)
    rw [show (1 + δ) ^ 6 = ((1 + δ) ^ 3) ^ 2 by ring]; exact pow_le_pow_left₀ hNp.le hhi 2
  · refine ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) ?_)
    rw [show (1 - δ) ^ 6 = ((1 - δ) ^ 3) ^ 2 by ring]; exact pow_le_pow_left₀ (by positivity) hlo 2

theorem kappa0C_bounds {δ : ℝ} (hδ1 : δ < 1) (hKV : KCq δ ⊆ V0 D₀) :
    ENNReal.ofReal ((1 + δ) ^ 6)⁻¹ * volume (betaJ ![-A, -B, A * B] '' ball 0 δ) ≤ kappa0 D₀ (KCq δ) ∧
      kappa0 D₀ (KCq δ) ≤ ENNReal.ofReal ((1 - δ) ^ 6)⁻¹ * volume (betaJ ![-A, -B, A * B] '' ball 0 δ) := by
  have hK := (isOpen_KCq δ).measurableSet
  have hk1 : kappa1 D₀ (KCq δ) = volume (betaJ ![-A, -B, A * B] '' ball 0 δ) := by
    rw [kappa1, Leray.fibreCount_apply_of_injOn (continuous_beta D₀) (isLocInj_beta D₀) volume hK
      ((injOn_beta_V0 D₀).mono hKV), betaC_image_KCq hA hB hδ1.le]
  rw [kappa0, withDensity_apply _ hK, ← hk1]
  constructor
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hK fun x hx => (thetaBC_bounds hA hB hδ1 hx).1
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hK fun x hx => (thetaBC_bounds hA hB hδ1 hx).2

/-! ### The two first-order factors and the limit -/

variable (A B) in
/-- The complex-linear derivative of the chart in adapted coordinates. -/
def chartDEC : ((Fin 3 → ℂ) × (UIdx 3 → ℂ)) →L[ℂ] ((Fin 3 → ℂ) × (UIdx 3 → ℂ)) :=
  (eMatE : (Fin 3 → Fin 3 → ℂ) ≃L[ℂ] _).toContinuousLinearMap.comp (LinearMap.toContinuousLinearMap (chartDL A B))

variable (A B) in
theorem hasStrictFDerivAt_chartEC :
    HasStrictFDerivAt (fun p => eMatE (chartF A B p)) ((chartDEC A B).restrictScalars ℝ) 0 :=
  ((eMatE : (Fin 3 → Fin 3 → ℂ) ≃L[ℂ] _).hasStrictFDerivAt.comp 0 (hasStrictFDerivAt_chartF A B)).restrictScalars ℝ

variable (A B) in
theorem det_chartDEC : ((chartDEC A B).restrictScalars ℝ).det = Complex.normSq (8 * A) := by
  have : ((chartDEC A B : _ →L[ℂ] _) : ((Fin 3 → ℂ) × (UIdx 3 → ℂ)) →ₗ[ℂ] _) = eMatL ∘ₗ chartDL A B := rfl
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, det_restrictScalars_complex, this,
    eMatL_chartDL, LinearMap.det_prodMap, det_dLow, LinearMap.det_id, mul_one]

theorem hasStrictFDerivAt_betaJC (α : Fin 3 → ℂ) :
    HasStrictFDerivAt (betaJ α) ((LinearMap.toContinuousLinearMap (betaDL α)).restrictScalars ℝ) 0 :=
  (hasStrictFDerivAt_betaJ α).restrictScalars ℝ

theorem det_betaJC (α : Fin 3 → ℂ) :
    ((LinearMap.toContinuousLinearMap (betaDL α)).restrictScalars ℝ).det =
      Complex.normSq (64 * α 0 ^ 3 * α 1 ^ 2 * α 2) := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, det_restrictScalars_complex]
  rw [show ((LinearMap.toContinuousLinearMap (betaDL α) : _ →L[ℂ] _) : (UIdx 3 → ℂ) →ₗ[ℂ] _) = betaDL α from rfl,
    det_betaDL]

theorem volume_betaJC_image_ne_top (α : Fin 3 → ℂ) (δ : ℝ) : volume (betaJ α '' ball 0 δ) ≠ ∞ :=
  ((measure_mono (image_mono ball_subset_closedBall)).trans_lt
    ((isCompact_closedBall 0 δ).image (contDiff_betaJ α).continuous).measure_lt_top).ne

include hA hB in
/-- **The local Leray asymptotics at a complex place**: in the quaternion chart $y\mapsto c(1+y)$,
$\mu_Q(c(1+B_\delta))/\mathrm{vol}(B_\delta) \to 1/|8A^3B^3|^2 = 1/|8A^3B^3|_{\mathbb C}$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratio of gauge measures, complex place) [unverified]"]
theorem tendsto_lerayC_quatBall (hQ : gramDetC (pureForm A B) ≠ 0) :
    Tendsto (fun δ => (lerayMeasureC (pureForm A B) hQ (ACq A B δ)).toReal / (volume (ball (0 : Fin 3 → ℂ) δ)).toReal)
      (𝓝[>] 0) (𝓝 (1 / (8 * ‖A‖ ^ 3 * ‖B‖ ^ 3) ^ 2)) := by
  obtain ⟨δV, hδV, hKV⟩ := exists_KCq_subset_V0 hA hB
  set α : Fin 3 → ℂ := ![-A, -B, A * B]
  set vb : ℝ → ℝ := fun δ => (volume (ball (0 : Fin 3 → ℂ) δ)).toReal
  set vw : ℝ → ℝ := fun δ => (volume (ball (0 : UIdx 3 → ℂ) δ)).toReal
  set V : ℝ → ℝ := fun δ => (volume (betaJ α '' ball 0 δ)).toReal
  set κ : ℝ → ℝ := fun δ => (kappa0 D₀ (KCq δ)).toReal
  have hvb : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < vb δ :=
    eventually_mem_nhdsWithin.mono fun δ hδ => toReal_volume_ball_pos volume hδ
  have hvw : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < vw δ :=
    eventually_mem_nhdsWithin.mono fun δ hδ => toReal_volume_ball_pos volume hδ
  have hlt : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < min (min (rad0 A B) (1 / 2)) δV :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min (lt_min (rad0_pos A B) (by norm_num)) hδV))
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ rad0 A B ∧ δ < 1 / 2 ∧ δ ≤ δV :=
    hlt.mono fun δ hδ => ⟨(le_of_lt hδ).trans ((min_le_left _ _).trans (min_le_left _ _)),
      hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _)), (le_of_lt hδ).trans (min_le_right _ _)⟩
  have tG := tendsto_div_of_bounds (hvb.and hvw |>.mono fun δ h => mul_pos h.1 h.2)
    (eventually_shear_image (upVecL A B) (hasStrictFDerivAt_chartEC A B))
  rw [det_chartDEC] at tG
  have tV : Tendsto (fun δ => V δ / vw δ) (𝓝[>] 0)
      (𝓝 |((LinearMap.toContinuousLinearMap (betaDL α)).restrictScalars ℝ).det|) :=
    tendsto_image_ball_div volume (hasStrictFDerivAt_betaJC α)
  rw [det_betaJC] at tV
  set dB := |Complex.normSq (64 * α 0 ^ 3 * α 1 ^ 2 * α 2)|
  have tlo : Tendsto (fun δ : ℝ => ((1 + 1 * δ) ^ 6)⁻¹ * (V δ / vw δ)) (𝓝[>] 0) (𝓝 dB) := by
    have h : Tendsto (fun δ : ℝ => ((1 + 1 * δ) ^ 6)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have h' : ContinuousAt (fun δ : ℝ => ((1 + 1 * δ) ^ 6)⁻¹) 0 :=
        ((continuous_const.add (continuous_const.mul continuous_id)).pow 6).continuousAt.inv₀ (by simp)
      simpa using h'.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h.mul tV
  have thi : Tendsto (fun δ : ℝ => ((1 + (-1) * δ) ^ 6)⁻¹ * (V δ / vw δ)) (𝓝[>] 0) (𝓝 dB) := by
    have h : Tendsto (fun δ : ℝ => ((1 + (-1) * δ) ^ 6)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have h' : ContinuousAt (fun δ : ℝ => ((1 + (-1) * δ) ^ 6)⁻¹) 0 :=
        ((continuous_const.add (continuous_const.mul continuous_id)).pow 6).continuousAt.inv₀ (by simp)
      simpa using h'.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h.mul tV
  have hκ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((1 + 1 * δ) ^ 6)⁻¹ * V δ ≤ κ δ ∧ κ δ ≤ ((1 + (-1) * δ) ^ 6)⁻¹ * V δ := by
    filter_upwards [hsmall, eventually_mem_nhdsWithin] with δ hδ hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    obtain ⟨b1, b2⟩ := kappa0C_bounds hA hB (δ := δ) (by linarith [hδ.2.1]) (hKV δ hδ.2.2)
    have hVt := volume_betaJC_image_ne_top α δ
    have hκt : kappa0 D₀ (KCq δ) ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) b2
    constructor
    · have := ENNReal.toReal_mono hκt b1
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
      simpa only [one_mul] using this
    · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) b2
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
        have : 0 < 1 - δ := by linarith [hδ.2.1]
        positivity), show (1 : ℝ) - δ = 1 + (-1) * δ by ring] at this
  have tK : Tendsto (fun δ => κ δ / vw δ) (𝓝[>] 0) (𝓝 dB) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tlo thi ?_ ?_
    · filter_upwards [hκ, hvw] with δ h hw
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h.1 hw.le
    · filter_upwards [hκ, hvw] with δ h hw
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h.2 hw.le
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (lerayMeasureC (pureForm A B) hQ (ACq A B δ)).toReal * κ δ =
      (volume ((fun p => eMatE (chartF A B p)) '' shearSet (upVecL A B) δ)).toReal := by
    filter_upwards [hsmall] with δ hδ
    rw [← ENNReal.toReal_mul, leray_mul_kappa0C hA hB hQ (hKV δ hδ.2.2) hδ.1]
  have hα : α 0 = -A ∧ α 1 = -B ∧ α 2 = A * B := ⟨rfl, rfl, rfl⟩
  have hdBv : dB = (64 * ‖A‖ ^ 4 * ‖B‖ ^ 3) ^ 2 := by
    simp only [dB, hα.1, hα.2.1, hα.2.2, Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_neg]
    rw [abs_of_nonneg (by positivity)]
    norm_num
    ring
  have hdB : dB ≠ 0 := by
    rw [hdBv]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (norm_ne_zero_iff.mpr hA)))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hB)))
  have := tendsto_ratio_of_tendsto hdB hvb hvw h1 tG tK
  convert this using 2
  rw [hdBv, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity), norm_mul]
  have hA' : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  have hB' : ‖B‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  field_simp
  norm_num

end Complex

end QuadFormsKB.Tamagawa.Measure.Weil
