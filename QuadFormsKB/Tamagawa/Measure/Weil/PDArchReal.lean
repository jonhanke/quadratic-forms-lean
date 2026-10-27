import QuadFormsKB.Tamagawa.Measure.Weil.PDArchSlice
import QuadFormsKB.Tamagawa.Measure.OrbitalReal

/-!
# The archimedean comparison at a real place, any signature

**Layer:** $A, B \in \mathbb R^\times$ (any signs), $D_w = (A,B)_{\mathbb R}$, $Q = \langle -A, -B, AB\rangle$
(`pureForm A B`), $\mu_Q$ = the Leray measure on $SO(Q)(\mathbb R)$.

**Proves** `tendsto_leray_quatBall`: in the quaternion chart $y \mapsto c(1+y)$ ($y \in \mathbb R^3$ the pure part,
$c$ conjugation on $D_w^0$),
$$\frac{\mu_Q\big(c(1 + B_\delta)\big)}{\mathrm{vol}(B_\delta)} \longrightarrow \frac{1}{|8A^3B^3|}\qquad(\delta\to0^+).$$
Since Weil's quotient measure $\operatorname{nrd}^{-2}dx/(dt/|t|)$ on $D_w^\times/\mathbb R^\times$ has density
$\operatorname{nrd}(1+y)^{-2}$ in the same chart, this is the local ratio $r_w = |8A^3B^3|_w$ of Weil's Thm 2.3.1 at a real
place of **any signature** (`cArch_eq` covers only the definite places, by total masses).

*Proof.* the fibration (`lerayMeasure_fibration`, slice data with $P = 1$, possible because the Gram matrix is
diagonal): $\mu_Q(\mathcal A)\,\kappa_0(\mathcal K) = \mathrm{vol}(\mathcal A\cdot\mathcal K)$. Take
$\mathcal A_\delta = c(1+B_\delta)$ and $\mathcal K_\delta = 1 + U(B'_\delta)$. The product set is the image of a shear set
under the chart $(y, w)\mapsto c(1+y)(1+U(w - u(y)))$, whose derivative at $0$ in adapted coordinates is
$\operatorname{diag}(2,-2,-2A)\times\mathrm{id}$ (`PDArchChart`); $\kappa_0 = |\det b|^{-1}\beta^*(dc)$ (OrbitalReal's
`thetaB_eq`) with $\beta(1 + U(w))$ of derivative $w_{ij}\mapsto 2\alpha_iw_{ij}$, determinant $64A^4B^3$ (`PDArchSlice`).
The first-order volume lemma (`ArchFirstOrder`) and the ratio limit give $8|A|/(64|A|^4|B|^3)$.
-/

open Matrix MeasureTheory Set Metric Filter Topology Quaternion
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.ArchSOMeasure

/-! ### Generic pieces -/

section Generic

variable {K : Type*} [Field K] (A B : K)

/-- The unit $1 + y$ of $(A,B)_K$ when $\operatorname{nrd}(1+y) \ne 0$. -/
def unitOneAdd (y : Fin 3 → K) (h : 1 + qPure A B y ≠ 0) : (ℍ[K,A,B])ˣ :=
  ((isUnit_iff_nrd_ne_zero (1 + Quat.pure y : ℍ[K,A,B])).2 (by rwa [nrd_one_add_pure_eq])).unit

theorem val_unitOneAdd (y : Fin 3 → K) (h : 1 + qPure A B y ≠ 0) :
    ((unitOneAdd A B y h : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = 1 + Quat.pure y := rfl

end Generic

section GenericK

variable {𝕜 : Type*} [RCLike 𝕜] (A B : 𝕜)

/-- `upVec` as a continuous linear map. -/
def upVecL : (Fin 3 → 𝕜) →L[𝕜] (UIdx 3 → 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := upVec A B
      map_add' := fun y y' => by
        funext p; simp only [upVec, Pi.add_apply]; rw [adMat_eq, adMat_eq, adMat_eq]
        obtain ⟨⟨i, j⟩, h⟩ := p
        fin_cases i <;> fin_cases j <;> simp <;> ring
      map_smul' := fun t y => by rw [upVec_smul]; rfl }

@[simp] theorem upVecL_apply (y : Fin 3 → 𝕜) : upVecL A B y = upVec A B y := rfl

theorem norm_qPure_le (y : Fin 3 → 𝕜) : ‖qPure A B y‖ ≤ (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ ^ 2 := by
  have h0 : ‖y 0‖ ≤ ‖y‖ := norm_le_pi_norm y 0
  have h1 : ‖y 1‖ ≤ ‖y‖ := norm_le_pi_norm y 1
  have h2 : ‖y 2‖ ≤ ‖y‖ := norm_le_pi_norm y 2
  calc ‖qPure A B y‖ ≤ ‖A‖ * ‖y 0‖ ^ 2 + ‖B‖ * ‖y 1‖ ^ 2 + ‖A * B‖ * ‖y 2‖ ^ 2 := by
        unfold qPure
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
        · rw [norm_mul, norm_neg, norm_mul, norm_pow, norm_pow]
        · rw [norm_mul, norm_pow]
    _ ≤ (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) h0 2
        have := pow_le_pow_left₀ (norm_nonneg _) h1 2
        have := pow_le_pow_left₀ (norm_nonneg _) h2 2
        nlinarith [norm_nonneg A, norm_nonneg B, norm_nonneg (A * B)]

/-- For $\|y\| < 1/(1 + \|A\| + \|B\| + \|AB\|)$, $\operatorname{nrd}(1+y) \ne 0$. -/
theorem one_add_qPure_ne_zero {y : Fin 3 → 𝕜} (hy : ‖y‖ < 1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) :
    1 + qPure A B y ≠ 0 := by
  intro h
  have hq : qPure A B y = -1 := by linear_combination h
  have hle := norm_qPure_le A B y
  rw [hq, norm_neg, norm_one] at hle
  have hc : 0 < 1 + ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
  have hd1 : 1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖) ≤ 1 := by
    rw [div_le_one hc]; linarith [norm_nonneg A, norm_nonneg B, norm_nonneg (A * B)]
  have hy1 : ‖y‖ < 1 := hy.trans_le hd1
  have hy2 : ‖y‖ ^ 2 ≤ ‖y‖ := by nlinarith [norm_nonneg y]
  have hC0 : 0 ≤ ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
  have h3 : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ ^ 2 ≤ (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ :=
    mul_le_mul_of_nonneg_left hy2 hC0
  have h4 : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ < 1 := by
    rw [lt_div_iff₀ hc] at hy; nlinarith [norm_nonneg y]
  linarith

/-- The radius below which the chart is defined. -/
def rad0 : ℝ := min 1 (1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖))

theorem rad0_pos : 0 < rad0 A B := lt_min one_pos (by positivity)

end GenericK

/-! ### The real place -/

theorem sigmaFinite_kappa0 {n : ℕ} {Q : QuadForm ℝ n} (D : Diag Q) : SigmaFinite (kappa0 D) := inferInstance

theorem isOpenPosMeasure_kappa0 {n : ℕ} {Q : QuadForm ℝ n} (D : Diag Q) : Measure.IsOpenPosMeasure (kappa0 D) :=
  inferInstance

theorem isFiniteMeasureOnCompacts_kappa0 {n : ℕ} {Q : QuadForm ℝ n} (D : Diag Q) :
    IsFiniteMeasureOnCompacts (kappa0 D) := inferInstance

section Real

variable (A B : ℝ)

theorem gramMatrixR_pureForm : gramMatrixR (pureForm A B) = Matrix.diagonal ![-A, -B, A * B] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gramMatrixR, pureForm, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

variable {A B}

/-- Slice data with $P = 1$ (the Gram matrix of $\langle -A,-B,AB\rangle$ is diagonal). -/
abbrev diagPure (hA : A ≠ 0) (hB : B ≠ 0) : Diag (pureForm A B) where
  P := 1
  d := ![-A, -B, A * B]
  hd := fun i => by fin_cases i <;> simp [hA, hB]
  hP := by simp [gramMatrixR_pureForm]

variable (hA : A ≠ 0) (hB : B ≠ 0)

local notation "D₀" => diagPure hA hB

/-- Upper triangular coordinates on the slice group $B^+$. -/
def coordR (x : SliceB (1 : GL (Fin 3) ℝ)) : UIdx 3 → ℝ := fun p => (SliceB.mat 1 x - 1) p.1.1 p.1.2

theorem continuous_coordR : Continuous coordR :=
  continuous_pi fun p => ((SliceB.continuous_mat 1).sub continuous_const).matrix_elem _ _

theorem mat_eq_one_add_utK (x : SliceB (1 : GL (Fin 3) ℝ)) : SliceB.mat 1 x = 1 + utK (coordR x) := by
  have hx := (mem_sliceGroup 1 _).mp (SliceB.incl_mem 1 x)
  have hUT : IsUT (SliceB.mat 1 x) := by
    have := hx.1
    simpa [SliceB.mat] using this
  ext i j
  simp only [Matrix.add_apply, utK, coordR, Matrix.sub_apply]
  split_ifs with h
  · ring
  · rw [hUT i j (not_le.mp h), Matrix.one_apply_ne (ne_of_gt (not_le.mp h)), add_zero]

theorem isUT_one_add_utK (w : UIdx 3 → ℝ) : IsUT (1 + utK w) := fun i j hij => by
  simp [utK, not_le.mpr hij, Matrix.one_apply_ne (ne_of_gt hij)]

theorem det_one_add_utK (w : UIdx 3 → ℝ) :
    (1 + utK w : Matrix (Fin 3) (Fin 3) ℝ).det = ∏ i : Fin 3, (1 + w ⟨(i, i), le_rfl⟩) := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => isUT_one_add_utK w i j hij)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [utK]

/-- The slice element $1 + U(w)$ (positive diagonal). -/
def jR (w : UIdx 3 → ℝ) (hw : ∀ i : Fin 3, 0 < 1 + w ⟨(i, i), le_rfl⟩) : SliceB (1 : GL (Fin 3) ℝ) :=
  SliceB.mk 1 (Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + utK w) (by
    rw [det_one_add_utK]; exact Finset.prod_ne_zero_iff.mpr fun i _ => (hw i).ne')) (by
    rw [mem_sliceGroup]
    refine ⟨?_, fun i => ?_⟩
    · simpa using isUT_one_add_utK w
    · simpa [utK] using hw i)

theorem mat_jR (w : UIdx 3 → ℝ) (hw : ∀ i : Fin 3, 0 < 1 + w ⟨(i, i), le_rfl⟩) :
    SliceB.mat 1 (jR w hw) = 1 + utK w := rfl

theorem coordR_jR (w : UIdx 3 → ℝ) (hw : ∀ i : Fin 3, 0 < 1 + w ⟨(i, i), le_rfl⟩) : coordR (jR w hw) = w := by
  funext p
  simp only [coordR, mat_jR, add_sub_cancel_left, utK, dite_eq_left p.2]

theorem pos_of_mem_ball {w : UIdx 3 → ℝ} {δ : ℝ} (hδ : δ ≤ 1) (hw : w ∈ ball (0 : UIdx 3 → ℝ) δ) (i : Fin 3) :
    0 < 1 + w ⟨(i, i), le_rfl⟩ := by
  rw [mem_ball_zero_iff] at hw
  have := (norm_le_pi_norm w ⟨(i, i), le_rfl⟩).trans_lt hw
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le (w ⟨(i, i), le_rfl⟩)]

/-- The slice neighbourhood $\mathcal K_\delta = 1 + U(B'_\delta)$. -/
def KRq (δ : ℝ) : Set (SliceB (1 : GL (Fin 3) ℝ)) := coordR ⁻¹' ball 0 δ

theorem isOpen_KRq (δ : ℝ) : IsOpen (KRq δ) := isOpen_ball.preimage continuous_coordR

theorem coordR_one : coordR (1 : SliceB (1 : GL (Fin 3) ℝ)) = 0 := by
  funext p; simp [coordR, SliceB.mat_one]

theorem one_mem_KRq {δ : ℝ} (hδ : 0 < δ) : (1 : SliceB (1 : GL (Fin 3) ℝ)) ∈ KRq δ := by
  simp [KRq, coordR_one, hδ]

theorem phi_pureForm (M : Matrix (Fin 3) (Fin 3) ℝ) : phi (pureForm A B) M = phiK ![-A, -B, A * B] M := by
  funext p
  simp [phi, phiK, wtU, gramMatrixR_pureForm]

theorem beta_image_KRq {δ : ℝ} (hδ : δ ≤ 1) :
    beta D₀ '' KRq δ = betaJ ![-A, -B, A * B] '' ball 0 δ := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨coordR x, hx, ?_⟩
    rw [beta, betaJ, phi_pureForm, ← mat_eq_one_add_utK]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨jR w (pos_of_mem_ball hδ hw), ?_, ?_⟩
    · simp only [KRq, mem_preimage, coordR_jR]; exact hw
    · rw [beta, betaJ, phi_pureForm]; rfl

/-- The element $c(1+y) \in SO(Q)(\mathbb R)$. -/
def gRq (y : Fin 3 → ℝ) (h : 1 + qPure A B y ≠ 0) : ArchSO (pureForm A B) :=
  ArchSOInst.mk _ (conjGL (unitOneAdd A B y h)) (by
    rw [mem_soReal_iff]
    have := (mem_SO_iff_hessian (two_ne_zero (α := ℝ))).1 (conjGL_mem (unitOneAdd A B y h))
    exact ⟨this.2, this.1⟩)

theorem mat_gRq (y : Fin 3 → ℝ) (h : 1 + qPure A B y ≠ 0) :
    ArchSOInst.mat _ (gRq y h) = cMat A B y := by
  exact conjGL_eq_cMat A B _ y (val_unitOneAdd A B y h)

/-- The chart neighbourhood $\mathcal A_\delta = c(1 + B_\delta)$ in $SO(Q)(\mathbb R)$. -/
def ARq (A B : ℝ) (δ : ℝ) : Set (ArchSO (pureForm A B)) :=
  {g | ∃ y ∈ ball (0 : Fin 3 → ℝ) δ, ArchSOInst.mat _ g = cMat A B y}

theorem chart_image {δ : ℝ} (hδ : δ ≤ rad0 A B) :
    chart D₀ '' (ARq A B δ ×ˢ KRq δ) = chartF A B '' shearSet (upVecL A B) δ := by
  have hδ1 : δ ≤ 1 := hδ.trans (min_le_left _ _)
  ext X
  constructor
  · rintro ⟨⟨g, x⟩, ⟨⟨y, hy, hg⟩, hx⟩, rfl⟩
    refine ⟨(y, coordR x + upVec A B y), ⟨hy, ?_⟩, ?_⟩
    · show coordR x + upVec A B y - upVecL A B y ∈ _
      rw [upVecL_apply, add_sub_cancel_right]; exact hx
    · simp only [chartF, chartMat, add_sub_cancel_right, chart, ← mat_eq_one_add_utK, hg]
      rfl
  · rintro ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
    have hq : 1 + qPure A B y ≠ 0 := one_add_qPure_ne_zero A B
      ((mem_ball_zero_iff.mp hy).trans_le (hδ.trans (min_le_right _ _)))
    simp only [upVecL_apply] at hu
    refine ⟨(gRq y hq, jR (u - upVec A B y) (pos_of_mem_ball hδ1 hu)), ⟨⟨y, hy, mat_gRq y hq⟩, ?_⟩, ?_⟩
    · simp only [KRq, mem_preimage, coordR_jR]; exact hu
    · simp only [chart, mat_gRq, mat_jR, chartF, chartMat]
      rfl

/-! ### The fibration identity and the two first-order factors -/

/-- **The fibration on the product neighbourhood**: $\mu_Q(\mathcal A_\delta)\,\kappa_0(\mathcal K_\delta)$ is the
volume of
the image of the shear set under the chart, in adapted coordinates. -/
theorem leray_mul_kappa0 (hQ : gramDetR (pureForm A B) ≠ 0) {δ : ℝ} (hδ : δ ≤ rad0 A B) :
    lerayMeasure (pureForm A B) hQ (ARq A B δ) * kappa0 D₀ (KRq δ) =
      volume ((fun p => eMatE (chartF A B p)) '' shearSet (upVecL A B) δ) := by
  have := sigmaFinite_kappa0 D₀
  rw [← Measure.prod_prod, ← lerayMeasure_fibration hQ D₀, (measurableEmbedding_chart D₀).comap_apply,
    chart_image hA hB hδ, ← volume_image_eMatE, image_image]

variable (A B) in
/-- The real-linear derivative of the chart in adapted coordinates. -/
def chartDE : ((Fin 3 → ℝ) × (UIdx 3 → ℝ)) →L[ℝ] ((Fin 3 → ℝ) × (UIdx 3 → ℝ)) :=
  (eMatE : (Fin 3 → Fin 3 → ℝ) ≃L[ℝ] _).toContinuousLinearMap.comp (LinearMap.toContinuousLinearMap (chartDL A B))

variable (A B) in
theorem hasStrictFDerivAt_chartE :
    HasStrictFDerivAt (fun p => eMatE (chartF A B p)) (chartDE A B) 0 :=
  (eMatE : (Fin 3 → Fin 3 → ℝ) ≃L[ℝ] _).hasStrictFDerivAt.comp 0 (hasStrictFDerivAt_chartF A B)

variable (A B) in
theorem det_chartDE : (chartDE A B).det = 8 * A := by
  have : ((chartDE A B : _ →L[ℝ] _) : ((Fin 3 → ℝ) × (UIdx 3 → ℝ)) →ₗ[ℝ] _) = eMatL ∘ₗ chartDL A B := rfl
  rw [ContinuousLinearMap.det, this, eMatL_chartDL, LinearMap.det_prodMap, det_dLow, LinearMap.det_id, mul_one]

variable (A B) in
theorem abs_det_betaDL : |LinearMap.det (betaDL ![-A, -B, A * B])| = 64 * |A| ^ 4 * |B| ^ 3 := by
  rw [det_betaDL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [show (64 : ℝ) * (-A) ^ 3 * (-B) ^ 2 * (A * B) = -(64 * A ^ 4 * B ^ 3) by ring, abs_neg, abs_mul, abs_mul,
    abs_pow, abs_pow]
  norm_num

/-- The density $\theta = |\det|^{-1}$ of $\kappa_0$ is within $(1\pm\delta)^{\mp3}$ of $1$ on $\mathcal K_\delta$. -/
theorem thetaB_bounds {δ : ℝ} (hδ1 : δ < 1) {x : SliceB (1 : GL (Fin 3) ℝ)} (hx : x ∈ KRq δ) :
    ENNReal.ofReal ((1 + δ) ^ 3)⁻¹ ≤ (thetaB D₀ x : ℝ≥0∞) ∧ (thetaB D₀ x : ℝ≥0∞) ≤ ENNReal.ofReal ((1 - δ) ^ 3)⁻¹ := by
  have hw : coordR x ∈ ball (0 : UIdx 3 → ℝ) δ := hx
  have hb : ∀ i : Fin 3, |coordR x ⟨(i, i), le_rfl⟩| < δ := fun i => by
    rw [mem_ball_zero_iff] at hw
    have := (norm_le_pi_norm (coordR x) ⟨(i, i), le_rfl⟩).trans_lt hw
    rwa [Real.norm_eq_abs] at this
  have hdet : (SliceB.mat (D₀).P x).det = ∏ i : Fin 3, (1 + coordR x ⟨(i, i), le_rfl⟩) := by
    show (SliceB.mat 1 x).det = _
    rw [mat_eq_one_add_utK, det_one_add_utK]
  rw [Fin.prod_univ_three] at hdet
  set d0 := 1 + coordR x ⟨(0, 0), le_rfl⟩
  set d1 := 1 + coordR x ⟨(1, 1), le_rfl⟩
  set d2 := 1 + coordR x ⟨(2, 2), le_rfl⟩
  have h0 := abs_lt.mp (hb 0); have h1 := abs_lt.mp (hb 1); have h2 := abs_lt.mp (hb 2)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hb 0).le
  have hd0 : 1 - δ < d0 ∧ d0 < 1 + δ := ⟨by simp only [d0]; linarith, by simp only [d0]; linarith⟩
  have hd1 : 1 - δ < d1 ∧ d1 < 1 + δ := ⟨by simp only [d1]; linarith, by simp only [d1]; linarith⟩
  have hd2 : 1 - δ < d2 ∧ d2 < 1 + δ := ⟨by simp only [d2]; linarith, by simp only [d2]; linarith⟩
  have hpos : 0 < 1 - δ := by linarith
  have hlo : (1 - δ) ^ 3 ≤ d0 * d1 * d2 := by
    have := mul_le_mul (mul_le_mul hd0.1.le hd1.1.le hpos.le (by linarith)) hd2.1.le hpos.le
      (mul_pos (hpos.trans hd0.1) (hpos.trans hd1.1)).le
    nlinarith
  have hhi : d0 * d1 * d2 ≤ (1 + δ) ^ 3 := by
    have := mul_le_mul (mul_le_mul hd0.2.le hd1.2.le (by linarith) (by linarith)) hd2.2.le (by linarith)
      (by nlinarith)
    nlinarith
  have hθ : (thetaB D₀ x : ℝ≥0∞) = ENNReal.ofReal (d0 * d1 * d2)⁻¹ := by
    rw [OrbitalReal.thetaB_eq, hdet]
    have hp : 0 < d0 * d1 * d2 := lt_of_lt_of_le (by positivity) hlo
    have h1 : ‖d0 * d1 * d2‖₊ = (d0 * d1 * d2).toNNReal := by
      rw [← NNReal.coe_inj, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hp, Real.coe_toNNReal _ hp.le]
    have h2 : (d0 * d1 * d2).toNNReal ≠ 0 := by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hp
    rw [h1, ENNReal.ofReal, Real.toNNReal_inv, ENNReal.coe_inv h2]
  rw [hθ]
  have hp : 0 < d0 * d1 * d2 := lt_of_lt_of_le (by positivity) hlo
  exact ⟨ENNReal.ofReal_le_ofReal (inv_anti₀ hp hhi), ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) hlo)⟩

theorem kappa0_bounds {δ : ℝ} (hδ1 : δ < 1) :
    ENNReal.ofReal ((1 + δ) ^ 3)⁻¹ * volume (betaJ ![-A, -B, A * B] '' ball 0 δ) ≤ kappa0 D₀ (KRq δ) ∧
      kappa0 D₀ (KRq δ) ≤ ENNReal.ofReal ((1 - δ) ^ 3)⁻¹ * volume (betaJ ![-A, -B, A * B] '' ball 0 δ) := by
  have hK := (isOpen_KRq δ).measurableSet
  have hk1 : kappa1 D₀ (KRq δ) = volume (betaJ ![-A, -B, A * B] '' ball 0 δ) := by
    rw [kappa1_apply D₀ hK, beta_image_KRq hA hB hδ1.le]
  rw [kappa0, withDensity_apply _ hK, ← hk1]
  constructor
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hK fun x hx => (thetaB_bounds hA hB hδ1 hx).1
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hK fun x hx => (thetaB_bounds hA hB hδ1 hx).2

/-- **First-order expansion on balls** for a strictly differentiable self-map of a finite-dimensional space. -/
theorem tendsto_image_ball_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {L : E →L[ℝ] E}
    (hf : HasStrictFDerivAt f L 0) :
    Tendsto (fun δ => (μ (f '' ball 0 δ)).toReal / (μ (ball (0 : E) δ)).toReal) (𝓝[>] 0) (𝓝 |L.det|) := by
  refine tendsto_div_of_bounds (eventually_mem_nhdsWithin.mono fun δ hδ => toReal_volume_ball_pos μ hδ) ?_
  intro ε hε
  obtain ⟨r, hr, hnear⟩ := eventually_image_near μ hf hε
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hr)] with δ hδ
  obtain ⟨h1, h2⟩ := hnear _ (ball_subset_ball (le_of_lt hδ)) measure_ball_lt_top.ne
  rw [abs_le]; constructor <;> nlinarith

theorem tendsto_inv_pow_three (c : ℝ) :
    Tendsto (fun δ : ℝ => ((1 + c * δ) ^ 3)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h : ContinuousAt (fun δ : ℝ => ((1 + c * δ) ^ 3)⁻¹) 0 :=
    ((continuous_const.add (continuous_const.mul continuous_id)).pow 3).continuousAt.inv₀ (by simp)
  simpa using h.tendsto.mono_left nhdsWithin_le_nhds

theorem volume_betaJ_image_ne_top (α : Fin 3 → ℝ) (δ : ℝ) : volume (betaJ α '' ball 0 δ) ≠ ∞ :=
  ((measure_mono (image_mono ball_subset_closedBall)).trans_lt
    ((isCompact_closedBall 0 δ).image (contDiff_betaJ α).continuous).measure_lt_top).ne

include hA hB in
/-- **The local Leray asymptotics at a real place, any signature**: in the quaternion chart
$y\mapsto c(1+y)$, $\mu_Q(c(1+B_\delta))/\mathrm{vol}(B_\delta) \to 1/|8A^3B^3|$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratio of gauge measures, real place) [unverified]"]
theorem tendsto_leray_quatBall (hQ : gramDetR (pureForm A B) ≠ 0) :
    Tendsto (fun δ => (lerayMeasure (pureForm A B) hQ (ARq A B δ)).toReal / (volume (ball (0 : Fin 3 → ℝ) δ)).toReal)
      (𝓝[>] 0) (𝓝 (1 / (8 * |A| ^ 3 * |B| ^ 3))) := by
  set α : Fin 3 → ℝ := ![-A, -B, A * B]
  set vb : ℝ → ℝ := fun δ => (volume (ball (0 : Fin 3 → ℝ) δ)).toReal
  set vw : ℝ → ℝ := fun δ => (volume (ball (0 : UIdx 3 → ℝ) δ)).toReal
  set V : ℝ → ℝ := fun δ => (volume (betaJ α '' ball 0 δ)).toReal
  set κ : ℝ → ℝ := fun δ => (kappa0 D₀ (KRq δ)).toReal
  have hvb : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < vb δ :=
    eventually_mem_nhdsWithin.mono fun δ hδ => toReal_volume_ball_pos volume hδ
  have hvw : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < vw δ :=
    eventually_mem_nhdsWithin.mono fun δ hδ => toReal_volume_ball_pos volume hδ
  have hlt : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < min (rad0 A B) (1 / 2) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min (rad0_pos A B) (by norm_num)))
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ rad0 A B ∧ δ < 1 / 2 :=
    hlt.mono fun δ hδ => ⟨(le_of_lt hδ).trans (min_le_left _ _), hδ.trans_le (min_le_right _ _)⟩
  -- the chart factor
  have tG := tendsto_div_of_bounds (hvb.and hvw |>.mono fun δ h => mul_pos h.1 h.2)
    (eventually_shear_image (upVecL A B) (hasStrictFDerivAt_chartE A B))
  rw [det_chartDE] at tG
  -- the slice factor
  have tV : Tendsto (fun δ => V δ / vw δ) (𝓝[>] 0) (𝓝 |LinearMap.det (betaDL α)|) :=
    tendsto_image_ball_div volume (hasStrictFDerivAt_betaJ α)
  have tlo : Tendsto (fun δ : ℝ => ((1 + 1 * δ) ^ 3)⁻¹ * (V δ / vw δ)) (𝓝[>] 0)
      (𝓝 |LinearMap.det (betaDL α)|) := by simpa using (tendsto_inv_pow_three 1).mul tV
  have thi : Tendsto (fun δ : ℝ => ((1 + (-1) * δ) ^ 3)⁻¹ * (V δ / vw δ)) (𝓝[>] 0)
      (𝓝 |LinearMap.det (betaDL α)|) := by simpa using (tendsto_inv_pow_three (-1)).mul tV
  have hκ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((1 + 1 * δ) ^ 3)⁻¹ * V δ ≤ κ δ ∧ κ δ ≤ ((1 + (-1) * δ) ^ 3)⁻¹ * V δ := by
    filter_upwards [hsmall, eventually_mem_nhdsWithin] with δ hδ hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    obtain ⟨b1, b2⟩ := kappa0_bounds hA hB (δ := δ) (by linarith [hδ.2])
    have hVt := volume_betaJ_image_ne_top α δ
    have hκt : kappa0 D₀ (KRq δ) ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) b2
    have hp1 : 0 ≤ ((1 + 1 * δ) ^ 3)⁻¹ := by positivity
    have hp2 : 0 ≤ ((1 + (-1) * δ) ^ 3)⁻¹ := by
      have : 0 < 1 + (-1) * δ := by linarith [hδ.2]
      positivity
    constructor
    · have := ENNReal.toReal_mono hκt b1
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
      simpa only [one_mul] using this
    · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) b2
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
        have : 0 < 1 - δ := by linarith [hδ.2]
        positivity), show (1 : ℝ) - δ = 1 + (-1) * δ by ring] at this
  have tK : Tendsto (fun δ => κ δ / vw δ) (𝓝[>] 0) (𝓝 |LinearMap.det (betaDL α)|) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tlo thi ?_ ?_
    · filter_upwards [hκ, hvw] with δ h hw
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h.1 hw.le
    · filter_upwards [hκ, hvw] with δ h hw
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h.2 hw.le
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (lerayMeasure (pureForm A B) hQ (ARq A B δ)).toReal * κ δ =
      (volume ((fun p => eMatE (chartF A B p)) '' shearSet (upVecL A B) δ)).toReal := by
    filter_upwards [hsmall] with δ hδ
    rw [← ENNReal.toReal_mul, leray_mul_kappa0 hA hB hQ hδ.1]
  have hdB : |LinearMap.det (betaDL α)| ≠ 0 := by
    rw [abs_det_betaDL]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (abs_ne_zero.mpr hA)))
      (pow_ne_zero _ (abs_ne_zero.mpr hB))
  have := tendsto_ratio_of_tendsto hdB hvb hvw h1 tG tK
  convert this using 2
  rw [abs_det_betaDL, abs_mul]
  have hA' : |A| ≠ 0 := abs_ne_zero.mpr hA
  have hB' : |B| ≠ 0 := abs_ne_zero.mpr hB
  field_simp
  norm_num

end Real

end QuadFormsKB.Tamagawa.Measure.Weil
