import QuadFormsKB.Tamagawa.Measure.OrbitImage
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchComplex
import QuadFormsKB.Tamagawa.BinaryNormOne

/-!
# The Leray measure of $SO(\langle1,D\rangle)(\mathbb C)$ on rotations
**Layer:** one complex place. $D\in\mathbb C\setminus0$, $Q = \langle1,D\rangle = x_0^2 + Dx_1^2$
(`QuadForm.diag ![1, D]`), $S_1 = \{Q = 1\}$ (`SphC Q 1`), $\sigma^{\mathbb C}_1$ its Leray measure (`sigC Q 1`).

**Proves**
* `lerayMeasureC_diag_one_univ`: the Leray measure of the trivial group $SO(\langle c\rangle)(\mathbb C)$ is
  $1/(4|c|^2)$ (the fibration identity `lerayMeasureC_fibration` with the slice group $\mathbb C^\times$:
  $\tau = \mu\otimes\kappa_0$, where $\tau$ is Lebesgue measure on the right half plane and $\kappa_0 = 4|c|^2\,dz$ there);
* **`lerayMeasureC_rotSecC_image`**: $\mu_Q(\rho(A)) = \dfrac{1}{16|D|^2}\,\sigma^{\mathbb C}_1(A)$ for every measurable
  $A\subseteq S_1$ (the orbital identity `lerayMeasureC_image_sec`);
* **`sigC_arcC`**: for $s^2 = -D$ and $\gamma(\tau) = (\cosh\tau, s^{-1}\sinh\tau)$, $\sigma^{\mathbb C}_1(\gamma(J)) =
  \mathrm{vol}(J)/(4|D|)$ for measurable $J\subseteq\mathbb C$ on which $\gamma$ is injective;
* **`lerayMeasureC_rotSecC_arcC`**: $\mu_Q(\rho(\gamma(J))) = \mathrm{vol}(J)/(64|D|^3)$.
-/

open MeasureTheory Measure Set Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
  QuadFormsKB.Tamagawa.Measure.OrbitalComplex

/-! ### Rank one -/

section RankOne

theorem hessian_diag_one_C (c : ℂ) : (QuadForm.diag ![c]).hessian = !![2 * c] := by
  ext i j; fin_cases i; fin_cases j; simp [QuadForm.hessian, QuadForm.diag]; ring

theorem gramC_diag_one (c : ℂ) : gramC (QuadForm.diag ![c]) = !![c] := by
  rw [gramC, hessian_diag_one_C]
  ext i j; fin_cases i; fin_cases j; simp

theorem gramDetC_diag_one (c : ℂ) : gramDetC (QuadForm.diag ![c]) = c := by
  rw [gramDetC, gramC_diag_one, Matrix.det_fin_one_of]

theorem gramDetC_diag_one_ne_zero {c : ℂ} (hc : c ≠ 0) : gramDetC (QuadForm.diag ![c]) ≠ 0 := by
  rwa [gramDetC_diag_one]

/-- Slice data for $\langle c\rangle$: $P = 1$. -/
abbrev diagDataC (c : ℂ) (hc : c ≠ 0) : DiagC (QuadForm.diag ![c]) where
  P := 1
  d := ![c]
  hd := fun i => by fin_cases i; simpa using hc
  hP := by
    rw [gramC_diag_one]
    ext i j; fin_cases i; fin_cases j; simp

/-- In rank one every invertible matrix lies in every slice group. -/
theorem mem_sliceGroup_one (P x : GL (Fin 1) ℂ) : x ∈ sliceGroup P := by
  rw [mem_sliceGroup]
  intro i j hij
  have := Subsingleton.elim i j
  subst this
  exact absurd hij (lt_irrefl _)

/-- $SO(Q)(\mathbb C)$ is trivial in rank one. -/
theorem archSOC_one_mat {Q : QuadForm ℂ 1} (g : ArchSOC Q) : ArchSOC.mat Q g = 1 := by
  have h := ArchSOC.det_mat Q g
  rw [Matrix.det_fin_one] at h
  ext i j; fin_cases i; fin_cases j
  exact h

/-- The coordinate $b\mapsto b_{00}$ on the slice group $\mathbb C^\times$. -/
def psi1 (b : SliceB (1 : GL (Fin 1) ℂ)) : ℂ := SliceB.mat 1 b 0 0

theorem continuous_psi1 : Continuous psi1 :=
  ((SliceB.continuous_mat (1 : GL (Fin 1) ℂ)).matrix_elem 0 0)

theorem psi1_ne_zero (b : SliceB (1 : GL (Fin 1) ℂ)) : psi1 b ≠ 0 := by
  have := SliceB.det_mat_ne_zero (1 : GL (Fin 1) ℂ) b
  rwa [Matrix.det_fin_one] at this

theorem psi1_injective : Function.Injective psi1 := by
  intro b b' h
  have hm : SliceB.mat 1 b = SliceB.mat 1 b' := by
    ext i j; fin_cases i; fin_cases j; exact h
  exact Subtype.ext (Units.ext hm)

theorem exists_psi1 {z : ℂ} (hz : z ≠ 0) : ∃ b, psi1 b = z := by
  have hd : (!![z] : Matrix (Fin 1) (Fin 1) ℂ).det ≠ 0 := by simpa using hz
  refine ⟨SliceB.mk 1 (toGL !![z]) (mem_sliceGroup_one _ _), ?_⟩
  change ((toGL !![z] : GL (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = z
  rw [toGL_val hd]; rfl

theorem measurableEmbedding_psi1 : MeasurableEmbedding psi1 :=
  continuous_psi1.measurableEmbedding psi1_injective

/-- The unique coefficient index of a rank-one form. -/
def idx0 : UIdx 1 := ⟨(0, 0), le_rfl⟩

instance uniqueUIdxOne : Unique (UIdx 1) :=
  ⟨⟨idx0⟩, fun _ => Subtype.ext (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

theorem default_UIdx_one : (default : UIdx 1) = idx0 := rfl

theorem act_one_apply (M : Matrix (Fin 1) (Fin 1) ℂ) :
    act M = (M 0 0 ^ 2) • (LinearMap.id : (UIdx 1 → ℂ) →ₗ[ℂ] (UIdx 1 → ℂ)) := by
  refine LinearMap.ext fun y => funext fun p => ?_
  have hp : p = idx0 := Subsingleton.elim _ _
  subst hp
  simp [act_apply, wtU, symOf, idx0, Matrix.mul_apply, ArchVol.wt]
  ring

theorem det_act_one (M : Matrix (Fin 1) (Fin 1) ℂ) : LinearMap.det (act M) = M 0 0 ^ 2 := by
  rw [act_one_apply, LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

variable {c : ℂ} (hc : c ≠ 0)

theorem beta_idx0 (b : SliceB (1 : GL (Fin 1) ℂ)) :
    beta (diagDataC c hc) b idx0 = c * psi1 b ^ 2 := by
  simp [beta, phi, wtU, gramC_diag_one, psi1, idx0, Matrix.mul_apply, ArchVol.wt]
  ring

theorem thetaB_eq (b : SliceB (1 : GL (Fin 1) ℂ)) :
    (thetaB (diagDataC c hc) b : ℝ≥0) = (‖psi1 b‖₊ ^ 2)⁻¹ := by
  have h1 : (SliceB.mat (diagDataC c hc).P b).det = psi1 b := by
    rw [Matrix.det_fin_one]; rfl
  have h2 : SliceB.mat (diagDataC c hc).P b 0 0 = psi1 b := rfl
  simp only [thetaB, chiB, JB, MonoidHom.coe_mk, OneHom.coe_mk, det_act_one, h1, h2, nnnorm_pow]
  have hne : ‖psi1 b‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (psi1_ne_zero b)
  field_simp

theorem det_smulRight_C (a : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).restrictScalars ℝ).det = Complex.normSq a := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, det_restrictScalars_complex]
  have : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) =
      a • LinearMap.id := by
    ext; simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

/-- **Area of the image under $z\mapsto cz^2$**: Jacobian $4|c|^2|z|^2$. -/
theorem volume_sq_image {E : Set ℂ} (hE : MeasurableSet E) (hinj : InjOn (fun z : ℂ => c * z ^ 2) E) :
    volume ((fun z : ℂ => c * z ^ 2) '' E) = ∫⁻ z in E, ENNReal.ofReal (4 * ‖c‖ ^ 2 * ‖z‖ ^ 2) := by
  have hder : ∀ z ∈ E, HasFDerivWithinAt (fun z : ℂ => c * z ^ 2)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (c * (↑(2 : ℕ) * z ^ (2 - 1)))).restrictScalars ℝ) E z :=
    fun z _ => (((hasDerivAt_pow 2 z).const_mul c).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE hder hinj (fun _ => 1)
  simp only [mul_one, det_smulRight_C] at h
  rw [← setLIntegral_one, h]
  refine setLIntegral_congr_fun hE fun z _ => ?_
  rw [abs_of_nonneg (Complex.normSq_nonneg _)]
  congr 1
  rw [Complex.normSq_eq_norm_sq, norm_mul, norm_mul, norm_pow]
  simp
  ring

include hc in
theorem injOn_sq_halfPlane : InjOn (fun z : ℂ => c * z ^ 2) {z : ℂ | 0 < z.re} := by
  intro z hz w hw h
  have h2 : z ^ 2 = w ^ 2 := mul_left_cancel₀ hc h
  have h3 : (z - w) * (z + w) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linear_combination h4
  · exfalso
    have := congrArg Complex.re h4
    simp only [Complex.add_re, Complex.zero_re] at this
    have hz' : 0 < z.re := hz
    have hw' : 0 < w.re := hw
    linarith

/-- The disc $A = B(1,1/2)$ in the right half plane. -/
def discA : Set ℂ := Metric.ball (1 : ℂ) (1 / 2)

theorem discA_subset : discA ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  have h1 : ‖z - 1‖ < 1 / 2 := by simpa [discA, dist_eq_norm] using hz
  have h2 : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have h3 := (abs_le.mp h2).1
  simp only [Complex.sub_re, Complex.one_re] at h3
  show 0 < z.re
  linarith

theorem discA_ne_zero {z : ℂ} (hz : z ∈ discA) : z ≠ 0 := by
  intro h
  have := discA_subset hz
  simp [h] at this

theorem measurableSet_discA : MeasurableSet discA := Metric.isOpen_ball.measurableSet

theorem volume_discA_pos : 0 < volume discA := Metric.measure_ball_pos _ _ (by norm_num)

theorem volume_discA_lt_top : volume discA < ⊤ := measure_ball_lt_top

/-- The coefficient coordinate of a rank-one form. -/
def ev0 (y : UIdx 1 → ℂ) : ℂ := y idx0

theorem measurePreserving_ev0 : MeasurePreserving ev0 volume volume :=
  volume_preserving_funUnique (UIdx 1) ℂ

theorem volume_preimage_ev0 (S : Set ℂ) : volume (ev0 ⁻¹' S) = volume S :=
  (volume_preserving_funUnique (UIdx 1) ℂ).measure_preimage_equiv S

include hc in
theorem beta_image_psi1 {E : Set ℂ} (hE : ∀ z ∈ E, z ≠ 0) :
    beta (diagDataC c hc) '' (psi1 ⁻¹' E) = ev0 ⁻¹' ((fun z : ℂ => c * z ^ 2) '' E) := by
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨psi1 b, hb, by simp [ev0, beta_idx0 hc]⟩
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨b, hb⟩ := exists_psi1 (hE z hz)
    refine ⟨b, by simpa [hb] using hz, ?_⟩
    funext p
    have hp : p = idx0 := Subsingleton.elim _ _
    subst hp
    rw [beta_idx0 hc, hb]
    exact hzy

include hc in
theorem injOn_beta_psi1 {E : Set ℂ} (hE : E ⊆ {z : ℂ | 0 < z.re}) :
    InjOn (beta (diagDataC c hc)) (psi1 ⁻¹' E) := by
  intro b hb b' hb' h
  have h2 : c * psi1 b ^ 2 = c * psi1 b' ^ 2 := by
    rw [← beta_idx0 hc b, ← beta_idx0 hc b', h]
  have hb1 : psi1 b ∈ {z : ℂ | 0 < z.re} := hE hb
  have hb2 : psi1 b' ∈ {z : ℂ | 0 < z.re} := hE hb'
  exact psi1_injective (injOn_sq_halfPlane hc hb1 hb2 h2)

include hc in
/-- $\kappa_1$ of a set of the slice group over $E$ in the right half plane is the area of $\{cz^2 : z\in E\}$. -/
theorem kappa1_psi1 {E : Set ℂ} (hEm : MeasurableSet E) (hE : E ⊆ {z : ℂ | 0 < z.re}) :
    kappa1 (diagDataC c hc) (psi1 ⁻¹' E) = volume ((fun z : ℂ => c * z ^ 2) '' E) := by
  have hne : ∀ z ∈ E, z ≠ 0 := fun z hz h => by
    have := hE hz
    simp [h] at this
  have hm : MeasurableSet (psi1 ⁻¹' E) := measurableEmbedding_psi1.measurable hEm
  have h := Leray.fibreCount_apply_of_injOn (continuous_beta (diagDataC c hc))
    (isLocInj_beta (diagDataC c hc)) volume hm (injOn_beta_psi1 hc hE)
  refine h.trans ?_
  rw [beta_image_psi1 hc hne, volume_preimage_ev0]

theorem measurePreserving_ev1 :
    MeasurePreserving (fun X : Fin 1 → Fin 1 → ℂ => X 0 0) volume volume :=
  (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))

include hc in
/-- **The chart measure on the disc**: $\tau(\mathrm{SO}\times\{b : b_{00}\in A\}) = \mathrm{vol}(A)$. -/
theorem tauM_psi1_discA :
    tauM (diagDataC c hc) (univ ×ˢ (psi1 ⁻¹' discA)) = volume discA := by
  have hV : MeasurableSet (psi1 ⁻¹' discA) := measurableEmbedding_psi1.measurable measurableSet_discA
  have h := Leray.fibreCount_apply_of_injOn (continuous_chart (diagDataC c hc))
    (isLocInj_chart (diagDataC c hc)) volume (MeasurableSet.univ.prod hV)
    (injOn_chart (diagDataC c hc) (injOn_beta_psi1 hc discA_subset))
  refine h.trans ?_
  have himg : chart (diagDataC c hc) '' (univ ×ˢ (psi1 ⁻¹' discA)) =
      (fun X : Fin 1 → Fin 1 → ℂ => X 0 0) ⁻¹' discA := by
    ext X
    constructor
    · rintro ⟨⟨g, b⟩, ⟨-, hb⟩, rfl⟩
      simp only [chart, archSOC_one_mat g, Matrix.one_mul]
      exact hb
    · intro hX
      obtain ⟨b, hb⟩ := exists_psi1 (discA_ne_zero hX)
      refine ⟨(1, b), ⟨mem_univ _, by simpa [hb] using hX⟩, ?_⟩
      funext i j
      have hi := Subsingleton.elim i 0
      have hj := Subsingleton.elim j 0
      subst hi hj
      simp [chart, cols, ArchSOC.mat_one]
      exact hb
  rw [himg]
  exact measurePreserving_ev1.measure_preimage measurableSet_discA.nullMeasurableSet

theorem ofReal_nnreal_inv_sq (z : ℂ) :
    ((((‖z‖₊ ^ 2)⁻¹ : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal ((‖z‖ ^ 2)⁻¹) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1

include hc in
/-- **$\kappa_0$ on the disc**: $\kappa_0(\{b : b_{00}\in A\}) = 4|c|^2\,\mathrm{vol}(A)$. -/
theorem kappa0_psi1_discA :
    kappa0 (diagDataC c hc) (psi1 ⁻¹' discA) = ENNReal.ofReal (4 * ‖c‖ ^ 2) * volume discA := by
  have hV : MeasurableSet (psi1 ⁻¹' discA) := measurableEmbedding_psi1.measurable measurableSet_discA
  have hw : Measurable fun z : ℂ => ENNReal.ofReal (4 * ‖c‖ ^ 2 * ‖z‖ ^ 2) := by fun_prop
  have hg : Measurable fun z : ℂ => ENNReal.ofReal ((‖z‖ ^ 2)⁻¹) := by fun_prop
  have hmap : ((kappa1 (diagDataC c hc)).restrict (psi1 ⁻¹' discA)).map psi1 =
      ((volume : Measure ℂ).restrict discA).withDensity
        (fun z => ENNReal.ofReal (4 * ‖c‖ ^ 2 * ‖z‖ ^ 2)) := by
    ext B hB
    have hBA : MeasurableSet (B ∩ discA) := hB.inter measurableSet_discA
    have hsub : B ∩ discA ⊆ {z : ℂ | 0 < z.re} := inter_subset_right.trans discA_subset
    rw [Measure.map_apply continuous_psi1.measurable hB,
      Measure.restrict_apply (continuous_psi1.measurable hB), withDensity_apply _ hB,
      Measure.restrict_restrict hB, ← preimage_inter, kappa1_psi1 hc hBA hsub,
      volume_sq_image hBA ((injOn_sq_halfPlane hc).mono hsub)]
  rw [kappa0, withDensity_apply _ hV]
  have hθ : ∀ b, ((thetaB (diagDataC c hc) b : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((‖psi1 b‖ ^ 2)⁻¹) := by
    intro b
    rw [thetaB_eq hc, ofReal_nnreal_inv_sq]
  simp_rw [hθ]
  calc ∫⁻ b in psi1 ⁻¹' discA, ENNReal.ofReal ((‖psi1 b‖ ^ 2)⁻¹) ∂kappa1 (diagDataC c hc)
      = ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ 2)⁻¹) ∂(((kappa1 (diagDataC c hc)).restrict (psi1 ⁻¹' discA)).map psi1) :=
        (lintegral_map hg continuous_psi1.measurable).symm
    _ = ∫⁻ z in discA, ENNReal.ofReal (4 * ‖c‖ ^ 2) := by
        rw [hmap, lintegral_withDensity_eq_lintegral_mul _ hw hg]
        refine setLIntegral_congr_fun measurableSet_discA fun z hz => ?_
        have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr (discA_ne_zero hz)
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = _ := by rw [setLIntegral_const]

/-- **The Leray measure of $SO(\langle c\rangle)(\mathbb C) = \{1\}$** is $1/(4|c|^2)$, for every $c\ne0$.

*Proof.* The fibration identity $\tau = \mu\otimes\kappa_0$ (`lerayMeasureC_fibration`, slice group
$\mathbb C^\times$) on the set $\{b : b_{00}\in B(1,1/2)\}$: $\tau$ is Lebesgue measure $\mathrm{vol}(B)$
(`tauM_psi1_discA`), $\kappa_0$ is $4|c|^2\,\mathrm{vol}(B)$ (`kappa0_psi1_discA`). -/
theorem lerayMeasureC_diag_one_univ (hc : c ≠ 0) :
    lerayMeasureC (QuadForm.diag ![c]) (gramDetC_diag_one_ne_zero hc) univ =
      ENNReal.ofReal (1 / (4 * ‖c‖ ^ 2)) := by
  have hfib := lerayMeasureC_fibration (gramDetC_diag_one_ne_zero hc) (diagDataC c hc)
  have hV : MeasurableSet (psi1 ⁻¹' discA) := measurableEmbedding_psi1.measurable measurableSet_discA
  have h1 : tauM (diagDataC c hc) (univ ×ˢ (psi1 ⁻¹' discA)) =
      lerayMeasureC (QuadForm.diag ![c]) (gramDetC_diag_one_ne_zero hc) univ *
        (ENNReal.ofReal (4 * ‖c‖ ^ 2) * volume discA) := by
    have := isHaarMeasure_lerayMeasureC (gramDetC_diag_one_ne_zero hc)
    have := sigmaFinite_kappa0C (diagDataC c hc)
    rw [← kappa0_psi1_discA hc, ← Measure.prod_prod]
    exact congrArg (fun μ => μ (univ ×ˢ (psi1 ⁻¹' discA))) hfib
  rw [tauM_psi1_discA hc] at h1
  set m := lerayMeasureC (QuadForm.diag ![c]) (gramDetC_diag_one_ne_zero hc) univ
  have hc2 : 0 < 4 * ‖c‖ ^ 2 := by have := norm_pos_iff.mpr hc; positivity
  have hv0 : volume discA ≠ 0 := volume_discA_pos.ne'
  have hvt : volume discA ≠ ⊤ := volume_discA_lt_top.ne
  have h2 : m * ENNReal.ofReal (4 * ‖c‖ ^ 2) = 1 := by
    have h3 : (m * ENNReal.ofReal (4 * ‖c‖ ^ 2)) * volume discA = 1 * volume discA := by
      rw [one_mul, mul_assoc]; exact h1.symm
    exact (ENNReal.mul_left_inj hv0 hvt).mp h3
  rw [one_div, ENNReal.ofReal_inv_of_pos hc2]
  exact ENNReal.eq_inv_of_mul_eq_one_left h2

end RankOne

/-! ### The binary form $\langle1,D\rangle$ and its rotations -/

section Binary

variable {D : ℂ}

theorem diag_one_D_eq_splitFormC (D : ℂ) :
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

theorem hessian_diag_one_D_C (D : ℂ) : (QuadForm.diag ![1, D]).hessian = BinaryNormOne.hessD D := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, QuadForm.diag, BinaryNormOne.hessD] <;> ring

theorem eval_diag_one_D_C (D : ℂ) (x : Fin 2 → ℂ) :
    (QuadForm.diag ![1, D]).eval x = x 0 ^ 2 + D * x 1 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two]; ring

theorem gramC_diag_one_D (D : ℂ) :
    gramC (QuadForm.diag ![1, D]) = (1 / 2 : ℂ) • BinaryNormOne.hessD D := by
  rw [gramC, hessian_diag_one_D_C]

theorem gramDetC_diag_one_D (D : ℂ) : gramDetC (QuadForm.diag ![1, D]) = D := by
  rw [gramDetC, gramC_diag_one_D, BinaryNormOne.hessD, Matrix.det_fin_two]
  simp

theorem gramDetC_diag_one_D_ne_zero (hD : D ≠ 0) : gramDetC (QuadForm.diag ![1, D]) ≠ 0 := by
  rwa [gramDetC_diag_one_D]

theorem norm_one_of_sphC (u : SphC (QuadForm.diag ![1, D]) 1) :
    (u : Fin 2 → ℂ) 0 ^ 2 + D * (u : Fin 2 → ℂ) 1 ^ 2 = 1 := by
  have h : (QuadForm.diag ![1, D]).eval (u : Fin 2 → ℂ) = 1 := u.2
  rwa [eval_diag_one_D_C] at h

/-- The rotation $\rho(u)$ with first column $u\in S_1$, as an element of $GL_2(\mathbb C)$. -/
def rotGLC (D : ℂ) (u : SphC (QuadForm.diag ![1, D]) 1) : GL (Fin 2) ℂ :=
  ⟨BinaryNormOne.rotMat D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) 1,
    BinaryNormOne.rotMatInv D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) 1,
    BinaryNormOne.rotMat_mul_rotMatInv (norm_one_of_sphC u) (by norm_num),
    BinaryNormOne.rotMatInv_mul_rotMat (norm_one_of_sphC u) (by norm_num)⟩

theorem rotGLC_mem (u : SphC (QuadForm.diag ![1, D]) 1) : rotGLC D u ∈ soC (QuadForm.diag ![1, D]) := by
  rw [mem_soC_iff]
  refine ⟨?_, ?_⟩
  · change (BinaryNormOne.rotMat D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) 1)ᵀ *
      gramC (QuadForm.diag ![1, D]) * BinaryNormOne.rotMat D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) 1 =
      gramC (QuadForm.diag ![1, D])
    rw [gramC_diag_one_D, Matrix.mul_smul, Matrix.smul_mul,
      BinaryNormOne.rotMat_isometry (norm_one_of_sphC u) (by norm_num)]
  · exact BinaryNormOne.det_rotMat (norm_one_of_sphC u)

/-- **The rotation section** $S_1\to SO(\langle1,D\rangle)(\mathbb C)$, $u\mapsto\rho(u)$. -/
def rotSecC (D : ℂ) (u : SphC (QuadForm.diag ![1, D]) 1) : ArchSOC (QuadForm.diag ![1, D]) :=
  ArchSOC.mk _ (rotGLC D u) (rotGLC_mem u)

theorem mat_rotSecC (u : SphC (QuadForm.diag ![1, D]) 1) :
    ArchSOC.mat _ (rotSecC D u) =
      BinaryNormOne.rotMat D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) 1 := rfl

theorem continuous_rotSecC : Continuous (rotSecC D) := by
  have h0 : Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℂ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℂ) 1 :=
    (continuous_apply 1).comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · change Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 =>
      BinaryNormOne.rotMat D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) 1
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [BinaryNormOne.rotMat] <;>
      first | exact h0 | exact h1 | exact (continuous_const.mul h1).neg
  · change Continuous fun u : SphC (QuadForm.diag ![1, D]) 1 =>
      BinaryNormOne.rotMatInv D ((u : Fin 2 → ℂ) 0) ((u : Fin 2 → ℂ) 1) 1
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [BinaryNormOne.rotMatInv] <;>
      first | exact h0 | exact h1.neg | exact continuous_const.mul h1

theorem rotSecC_spec (u : SphC (QuadForm.diag ![1, D]) 1) :
    ArchSOC.mat _ (rotSecC D u) *ᵥ (e₀ : Fin 2 → ℂ) = (u : Fin 2 → ℂ) := by
  rw [mat_rotSecC]
  funext i; fin_cases i <;> simp [BinaryNormOne.rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e₀]

/-- The embedding $SO(\langle D\rangle)\to SO(\langle1,D\rangle)$, $h\mapsto\mathrm{diag}(1,h)$. -/
def iotaC1 (D : ℂ) (h : ArchSOC (QuadForm.diag ![D])) : ArchSOC (QuadForm.diag ![1, D]) :=
  ArchSOC.mk _ (blockGL (ArchSOC.incl _ h)) (by
    rw [diag_one_D_eq_splitFormC]; exact blockGL_mem_soC 1 _ (ArchSOC.incl_mem _ h))

theorem mat_iotaC1 (h : ArchSOC (QuadForm.diag ![D])) :
    ArchSOC.mat _ (iotaC1 D h) = cornerMat 1 (ArchSOC.mat _ h) := by
  change ((blockGL (ArchSOC.incl _ h) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [blockGL_val]; rfl

theorem iotaC1_eq_one (h : ArchSOC (QuadForm.diag ![D])) : iotaC1 D h = 1 := by
  apply Subtype.ext; apply Units.ext
  change ArchSOC.mat _ (iotaC1 D h) = 1
  rw [mat_iotaC1, archSOC_one_mat, cornerMat_one]

/-- **The Leray measure of the rotations by $A\subseteq S_1$**:
$\mu_{\langle1,D\rangle}(\rho(A)) = \sigma^{\mathbb C}_1(A)/(16|D|^2)$. -/
theorem lerayMeasureC_rotSecC_image (hD : D ≠ 0) {A : Set (SphC (QuadForm.diag ![1, D]) 1)}
    (hA : MeasurableSet A) :
    lerayMeasureC (QuadForm.diag ![1, D]) (gramDetC_diag_one_D_ne_zero hD) (rotSecC D '' A) =
      ENNReal.ofReal (1 / (16 * ‖D‖ ^ 2)) * sigC (QuadForm.diag ![1, D]) 1 A := by
  have h := lerayMeasureC_image_sec (m := 1) one_ne_zero (gramDetC_diag_one_ne_zero hD)
    (QuadForm.diag ![1, D]) (diag_one_D_eq_splitFormC D) (gramDetC_diag_one_D_ne_zero hD) (rotSecC D)
    continuous_rotSecC.measurable rotSecC_spec (iotaC1 D) mat_iotaC1 hA MeasurableSet.univ
  have himg : (fun p : SphC (QuadForm.diag ![1, D]) 1 × ArchSOC (QuadForm.diag ![D]) =>
      rotSecC D p.1 * iotaC1 D p.2) '' (A ×ˢ univ) = rotSecC D '' A := by
    ext g
    constructor
    · rintro ⟨⟨u, h⟩, ⟨hu, -⟩, rfl⟩
      exact ⟨u, hu, by simp [iotaC1_eq_one]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u, 1), ⟨hu, mem_univ _⟩, by simp [iotaC1_eq_one]⟩
  rw [himg, lerayMeasureC_diag_one_univ hD] at h
  have hD0 : 0 < ‖D‖ := norm_pos_iff.mpr hD
  rw [h, mul_comm (sigC _ _ A), ← mul_assoc, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  push_cast
  have h2 : ‖(2 : ℂ) * 1‖ = 2 := by simp
  rw [h2]
  field_simp
  norm_num

end Binary

/-! ### The arc $\gamma(\tau) = (\cosh\tau, s^{-1}\sinh\tau)$ -/

section Arc

variable {D s : ℂ}

/-- The point $\gamma(\tau) = (\cosh\tau,\ s^{-1}\sinh\tau)$ of $x_0^2 + Dx_1^2 = 1$ (where $s^2 = -D$). -/
def arcVecC (s : ℂ) (τ : ℂ) : Fin 2 → ℂ := ![Complex.cosh τ, s⁻¹ * Complex.sinh τ]

theorem ne_zero_of_sq_eq_neg (hD : D ≠ 0) (hs : s ^ 2 = -D) : s ≠ 0 := by
  rintro rfl
  apply hD
  have : -D = 0 := by rw [← hs]; ring
  exact neg_eq_zero.mp this

theorem arcVecC_mem (hD : D ≠ 0) (hs : s ^ 2 = -D) (τ : ℂ) :
    arcVecC s τ ∈ sphC (QuadForm.diag ![1, D]) 1 := by
  have hs0 := ne_zero_of_sq_eq_neg hD hs
  change (QuadForm.diag ![1, D]).eval (arcVecC s τ) = 1
  rw [eval_diag_one_D_C]
  simp only [arcVecC, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hD': D = -s ^ 2 := by linear_combination hs
  rw [hD', mul_pow, inv_pow]
  field_simp
  have := Complex.cosh_sq τ
  linear_combination this

/-- $\gamma(\tau)$ as a point of $S_1$. -/
def arcC (hD : D ≠ 0) (hs : s ^ 2 = -D) (τ : ℂ) : SphC (QuadForm.diag ![1, D]) 1 :=
  ⟨arcVecC s τ, arcVecC_mem hD hs τ⟩

theorem continuous_arcC (hD : D ≠ 0) (hs : s ^ 2 = -D) : Continuous (arcC hD hs) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [arcVecC]; fun_prop
  · simp only [arcVecC]; fun_prop

/-- The map $\Phi(\beta,\tau) = (\beta\cosh\tau,\ s^{-1}\beta\sinh\tau)$. -/
def arcPhi (s : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 * Complex.cosh p.2, s⁻¹ * (p.1 * Complex.sinh p.2))

/-- Its complex derivative. -/
def arcPhiD (s : ℂ) (p : ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  ((Complex.cosh p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (p.1 * Complex.sinh p.2) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((s⁻¹ * Complex.sinh p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (s⁻¹ * (p.1 * Complex.cosh p.2)) • ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem hasFDerivAt_arcPhi (s : ℂ) (p : ℂ × ℂ) : HasFDerivAt (arcPhi s) (arcPhiD s p) p := by
  have hc : HasFDerivAt (fun q : ℂ × ℂ => Complex.cosh q.2)
      (Complex.sinh p.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
    (Complex.hasDerivAt_cosh p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have hs : HasFDerivAt (fun q : ℂ × ℂ => Complex.sinh q.2)
      (Complex.cosh p.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
    (Complex.hasDerivAt_sinh p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have h1 : HasFDerivAt (fun q : ℂ × ℂ => q.1 * Complex.cosh q.2) _ p :=
    (hasFDerivAt_fst (𝕜 := ℂ) (p := p)).mul hc
  have h2 : HasFDerivAt (fun q : ℂ × ℂ => s⁻¹ * (q.1 * Complex.sinh q.2)) _ p :=
    ((hasFDerivAt_fst (𝕜 := ℂ) (p := p)).mul hs).const_mul _
  refine (h1.prodMk h2).congr_fderiv ?_
  ext <;> simp [arcPhiD]

theorem det_arcPhiD (hD : D ≠ 0) (hs : s ^ 2 = -D) (p : ℂ × ℂ) :
    (((arcPhiD s p).restrictScalars ℝ)).det = Complex.normSq (p.1 * s⁻¹) := by
  have hs0 := ne_zero_of_sq_eq_neg hD hs
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, det_restrictScalars_complex]
  congr 1
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℂ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, arcPhiD, Module.Basis.finTwoProd]
  have := Complex.cosh_sq p.2
  field_simp
  linear_combination p.1 * this

theorem wt_two_eq (β : ℂˣ) : SphereLerayC.wt 2 β = ENNReal.ofReal (‖(β : ℂ)‖ ^ 2) := by
  rw [SphereLerayC.wt, ← ENNReal.ofReal_coe_nnreal]
  congr 1

/-- **The mass of $R_0$ for $n = 2$ in Lebesgue terms**: $\lambda_2(R_0) = \int_{R_0}|z|^2\,dz$. -/
theorem lamU_two_R0 : lamU 2 R0 = ∫⁻ z in Units.val '' R0, ENNReal.ofReal (‖z‖ ^ 2) := by
  have hme : MeasurableEmbedding (Units.val : ℂˣ → ℂ) := SphereLerayC.measurableEmbedding_val
  have hR : MeasurableSet R0 := isOpen_R0.measurableSet
  have hmap : volU.map Units.val = volume.restrict (range Units.val) := hme.map_comap volume
  have hsub : Units.val '' R0 ⊆ range Units.val := image_subset_range _ _
  have hS : MeasurableSet (Units.val '' R0) := hme.measurableSet_image.mpr hR
  calc lamU 2 R0 = ∫⁻ β in R0, SphereLerayC.wt (2 * ((2 : ℕ) : ℤ) - 2) β ∂volU := withDensity_apply _ hR
    _ = ∫⁻ β in R0, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2) ∂volU := by
        refine setLIntegral_congr_fun hR fun β _ => ?_
        rw [← wt_two_eq]; norm_num
    _ = ∫⁻ z in Units.val '' R0, ENNReal.ofReal (‖z‖ ^ 2) ∂(volU.map Units.val) := by
        rw [hme.restrict_map, hme.lintegral_map, hme.injective.preimage_image]
    _ = _ := by rw [hmap, Measure.restrict_restrict hS, inter_eq_left.mpr hsub]

/-- Lebesgue measure on $\mathbb C\times\mathbb C$ is an additive Haar measure. -/
instance isAddHaarMeasure_volume_complex_prod : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- The region $R_0\subseteq\mathbb C^\times$ as a subset of $\mathbb C$. -/
abbrev R0c : Set ℂ := Units.val '' R0

/-- The coordinates $(\mathbb C\times\mathbb C)\to\mathbb C^2$. -/
abbrev toVec2C : ℂ × ℂ ≃ᵐ (Fin 2 → ℂ) := (MeasurableEquiv.finTwoArrow).symm

theorem toVec2C_arcPhi (p : ℂ × ℂ) : toVec2C (arcPhi s p) = p.1 • arcVecC s p.2 := by
  funext i; fin_cases i
  · simp [arcPhi, arcVecC]
  · simp [arcPhi, arcVecC]; ring

theorem arcPhi_injOn (hD : D ≠ 0) (hs : s ^ 2 = -D) {J : Set ℂ} (hJ : InjOn (arcC hD hs) J) :
    InjOn (arcPhi s) (R0c ×ˢ J) := by
  have hs0 := ne_zero_of_sq_eq_neg hD hs
  rintro ⟨β, τ⟩ ⟨⟨u, hu, rfl⟩, hτ⟩ ⟨β', τ'⟩ ⟨⟨u', hu', rfl⟩, hτ'⟩ h
  simp only [arcPhi, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : (u : ℂ) * Complex.sinh τ = (u' : ℂ) * Complex.sinh τ' := mul_left_cancel₀ (inv_ne_zero hs0) h2
  have hsq : (u : ℂ) ^ 2 = (u' : ℂ) ^ 2 := by
    have e1 := Complex.cosh_sq τ
    have e2 := Complex.cosh_sq τ'
    calc (u : ℂ) ^ 2 = ((u : ℂ) * Complex.cosh τ) ^ 2 - ((u : ℂ) * Complex.sinh τ) ^ 2 := by
          linear_combination (-(u : ℂ) ^ 2) * e1
      _ = ((u' : ℂ) * Complex.cosh τ') ^ 2 - ((u' : ℂ) * Complex.sinh τ') ^ 2 := by rw [h1, h2']
      _ = (u' : ℂ) ^ 2 := by linear_combination ((u' : ℂ) ^ 2) * e2
  have hre : 0 < (u : ℂ).re := hu.1
  have hre' : 0 < (u' : ℂ).re := hu'.1
  have hbb : (u : ℂ) = u' := by
    have h3 : ((u : ℂ) - u') * ((u : ℂ) + u') = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linear_combination h4
    · exfalso
      have := congrArg Complex.re h4
      simp only [Complex.add_re, Complex.zero_re] at this
      linarith
  have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
  have hue : u = u' := Units.ext hbb
  subst hue
  have hc : Complex.cosh τ = Complex.cosh τ' := mul_left_cancel₀ hu0 h1
  have hsn : Complex.sinh τ = Complex.sinh τ' := mul_left_cancel₀ hu0 h2'
  have : arcC hD hs τ = arcC hD hs τ' := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact hc
    · simp only [arcC, arcVecC]
      show s⁻¹ * Complex.sinh τ = s⁻¹ * Complex.sinh τ'
      rw [hsn]
  exact Prod.ext rfl (hJ hτ hτ' this)


/-- **The Leray measure of an arc of the complex conic**: $\sigma^{\mathbb C}_1(\gamma(J)) =
\mathrm{vol}(J)/(4|D|)$ for every measurable $J\subseteq\mathbb C$ on which $\gamma$ is injective (for example
$J\subseteq\{|\operatorname{Im}\tau|<\pi/2\}$).

*Proof.* $\sigma^{\mathbb C}_1 = (4)^{-1}\nu$ and $\nu(A) = \mathrm{vol}(R_0\cdot A)/\lambda_2(R_0)$ (`nuC_apply_volume`);
the cone over $\gamma(J)$ is the image of $R_0\times J$ under $\Phi(\beta,\tau) = (\beta\cosh\tau,\ s^{-1}\beta\sinh\tau)$,
a holomorphic map with complex Jacobian $\beta/s$, hence real Jacobian $|\beta|^2/|D|$
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`), and $\int_{R_0}|\beta|^2 = \lambda_2(R_0)$. -/
theorem sigC_arcC (hD : D ≠ 0) (hs : s ^ 2 = -D) {J : Set ℂ} (hJ : MeasurableSet J)
    (hinj : InjOn (arcC hD hs) J) :
    sigC (QuadForm.diag ![1, D]) 1 (arcC hD hs '' J) = ENNReal.ofReal (1 / (4 * ‖D‖)) * volume J := by
  have hs0 := ne_zero_of_sq_eq_neg hD hs
  have hD0 : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hmeasA : MeasurableSet (arcC hD hs '' J) :=
    hJ.image_of_continuousOn_injOn (continuous_arcC hD hs).continuousOn hinj
  rw [sigC, Measure.smul_apply, nuC_apply_volume one_ne_zero hmeasA, smul_eq_mul]
  have himg : polC (QuadForm.diag ![1, D]) 1 '' (R0 ×ˢ (arcC hD hs '' J)) =
      toVec2C '' (arcPhi s '' (R0c ×ˢ J)) := by
    ext y
    constructor
    · rintro ⟨⟨β, x⟩, ⟨hβ, ⟨τ, hτ, rfl⟩⟩, rfl⟩
      exact ⟨arcPhi s ((β : ℂ), τ), ⟨((β : ℂ), τ), ⟨⟨β, hβ, rfl⟩, hτ⟩, rfl⟩, by rw [toVec2C_arcPhi]; rfl⟩
    · rintro ⟨_, ⟨⟨_, τ⟩, ⟨⟨u, hu, rfl⟩, hτ⟩, rfl⟩, rfl⟩
      exact ⟨(u, arcC hD hs τ), ⟨hu, τ, hτ, rfl⟩, by rw [toVec2C_arcPhi]; rfl⟩
  rw [himg]
  have hpres : MeasurePreserving toVec2C volume volume := (volume_preserving_finTwoArrow ℂ).symm
  have hvol : volume (toVec2C '' (arcPhi s '' (R0c ×ˢ J))) =
      volume (arcPhi s '' (R0c ×ˢ J)) := by
    rw [MeasurableEquiv.image_eq_preimage_symm, ← hpres.symm.measure_preimage_equiv]
  rw [hvol]
  have hR' : MeasurableSet (Units.val '' R0) :=
    (SphereLerayC.measurableEmbedding_val.measurableSet_image.mpr isOpen_R0.measurableSet)
  have hS : MeasurableSet (R0c ×ˢ J) := hR'.prod hJ
  have hJac := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (ℂ × ℂ)) hS
    (fun p _ => ((hasFDerivAt_arcPhi s p).restrictScalars ℝ).hasFDerivWithinAt)
    (arcPhi_injOn hD hs hinj) (fun _ => 1)
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul, mul_one] at hJac
  rw [hJac]
  have hns : ‖s‖ ^ 2 = ‖D‖ := by rw [← norm_pow, hs, norm_neg]
  have hdet : ∀ p : ℂ × ℂ, |((arcPhiD s p).restrictScalars ℝ).det| =
      ‖p.1‖ ^ 2 * (1 / ‖D‖) := by
    intro p
    rw [det_arcPhiD hD hs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, norm_mul,
      norm_inv, mul_pow, inv_pow, hns]
    ring
  simp_rw [hdet]
  have key : ∫⁻ p in R0c ×ˢ J, ENNReal.ofReal (‖p.1‖ ^ 2 * (1 / ‖D‖)) =
      ENNReal.ofReal (1 / ‖D‖) * lamU 2 R0 * volume J := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
    simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [lintegral_mul_const _ (by fun_prop), lamU_two_R0]
    congr 1
    rw [← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  rw [key]
  have hpos : lamU 2 R0 ≠ 0 := lamU_R0_pos.ne'
  have hfin : lamU 2 R0 ≠ ⊤ := (lamU_R0_lt_top (by norm_num)).ne
  have h2 : ((((‖(2 : ℂ) * 1‖₊ ^ 2)⁻¹ : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    simp only [mul_one]
    norm_num
  rw [h2, mul_comm (ENNReal.ofReal (1 / ‖D‖)) (lamU 2 R0), mul_assoc, ← mul_assoc (lamU 2 R0)⁻¹,
    ENNReal.inv_mul_cancel hpos hfin, one_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  congr 2
  field_simp

/-- **The Leray measure of the rotations by an arc of the complex conic**:
$\mu_{\langle1,D\rangle}(\rho(\gamma(J))) = \mathrm{vol}(J)/(64|D|^3)$, for measurable $J\subseteq\mathbb C$ on which
$\gamma$ is injective. -/
theorem lerayMeasureC_rotSecC_arcC (hD : D ≠ 0) (hs : s ^ 2 = -D) {J : Set ℂ} (hJ : MeasurableSet J)
    (hinj : InjOn (arcC hD hs) J) :
    lerayMeasureC (QuadForm.diag ![1, D]) (gramDetC_diag_one_D_ne_zero hD)
        (rotSecC D '' (arcC hD hs '' J)) =
      ENNReal.ofReal (1 / (64 * ‖D‖ ^ 3)) * volume J := by
  have hD0 : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hA : MeasurableSet (arcC hD hs '' J) :=
    hJ.image_of_continuousOn_injOn (continuous_arcC hD hs).continuousOn hinj
  rw [lerayMeasureC_rotSecC_image hD hA, sigC_arcC hD hs hJ hinj, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
  ring

end Arc

end QuadFormsKB.Tamagawa.Measure.Weil
