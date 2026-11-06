/-
# Whittaker integral = orbital integral at a complex place

**Layer:** one complex place. The complex analogue of `OrbitalReal`: the $m$-th local Whittaker integral of the
Siegel–Weil section of $\Phi$ at a complex place is the integral of $\Phi$ over the quadric $\{Q = m\}\subset\mathbb C^n$ for
the Leray measure (Weil 1965, *Sur la formule de Siegel*, §§ 8–10 [unverified]).

**Setting.** $Q$ a complex quadratic form in $n$ variables (`QuadForm ℂ n`), $S_t = \{x\in\mathbb C^n : Q(x) = t\}$ and
$\sigma_t$ the complex Leray measure $|dx/dQ|_{\mathbb C}$ on $S_t$ (`SphereLerayC.sigC`, $t\ne0$). For $\Phi\ge0$ on
$\mathbb C^n$ the **orbital integral** is $\rho_\Phi(t) = \int_{S_t}\Phi\,d\sigma_t$ (`orbC`). Lebesgue measure on
$\mathbb C\cong\mathbb R^2$ and on $\mathbb C^n\cong\mathbb R^{2n}$ throughout; the character is
$\psi_{\mathbb C}(z) = e(\operatorname{Tr}_{\mathbb C/\mathbb R}z) = e^{2\pi i\cdot2\operatorname{Re}z}$.

**Proves**
* `lintegral_eq_lintegral_halfP_sq`: the change of variables $t = z^2$ from the right half plane onto $\mathbb C$.
* `volume_diagC_eval_eq_zero`, `volume_eval_notMem_slitPlane`: the null cone of a nondegenerate diagonal form is null,
  and then so is $\{x : Q(x)\in(-\infty, 0]\}$ (a rotation argument).
* `lintegral_eq_lintegral_orbC` (**coarea formula**): $\int_{\mathbb C^n}\Phi\,dx = \int_{\mathbb C}\rho_\Phi(t)\,dt$, and
  $Q_*(\Phi\,dx) = \rho_\Phi\,dt$ (`map_withDensity_eq_orbC`).
* `fourier_orbCR`: the Fourier transform of $\rho_\Phi$ is the oscillatory integral of $\Phi$.
* **`tendsto_whittakerRegC`**, **`integral_whittakerC_eq_orbCR`**: the Whittaker integral
  $\int_{\mathbb C}\big(\int_{\mathbb C^n}\Phi(x)\psi_{\mathbb C}(bQ(x))\,dx\big)\psi_{\mathbb C}(-mb)\,db = \tfrac14\rho_\Phi(m)$
  (Gauss-regularized, resp. absolutely convergent; $\tfrac14$ is the Jacobian of $b\mapsto-2\bar b$: with the self-dual
  measure $2\,dx\,dy$ for $\psi_{\mathbb C}$ on every copy of $\mathbb C$ the factor is $2^{n+1}/4 = 2^{n-1}$, the constant of
  `sigInfNF` at a complex place).
* `continuousAt_orbCR`: continuity of $\rho_\Phi$ off $0$ for $\Phi$ of polynomial decay.
* **`whittakerC_gaussMajC_eq_orbCR`**: for the Gaussian of the majorant $e^{-2\pi\sum_i|a_i||x_i|^2}$ of
  $Q = \sum_ia_ix_i^2$, $n\ge3$, the Whittaker integral converges absolutely and equals $\tfrac14\rho_\Phi(m)$, $m\ne0$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.SphereLerayC
import QuadFormsKB.SiegelWeil.OrbitalReal

open MeasureTheory Measure Set Filter Topology Complex
open scoped ENNReal FourierTransform RealInnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Orbital

/-! ### The squaring map on the right half plane -/

section Square

/-- The open right half plane $\{\operatorname{Re}z > 0\}$ in $\mathbb C$. -/
def halfP : Set ℂ := {z | 0 < z.re}

theorem isOpen_halfP : IsOpen halfP := isOpen_lt continuous_const continuous_re

theorem volume_im_eq_zero : volume {z : ℂ | z.im = 0} = 0 := by
  have h : {z : ℂ | z.im = 0} = measurableEquivRealProd ⁻¹' (univ ×ˢ {0}) := by
    ext z; simp [measurableEquivRealProd]
  rw [h, volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem volume_slitPlane_compl : volume slitPlaneᶜ = 0 := by
  refine measure_mono_null (fun z hz => ?_) volume_im_eq_zero
  simp only [mem_compl_iff, mem_slitPlane_iff, not_or, not_lt, not_not] at hz
  exact hz.2

theorem sq_mem_slitPlane {z : ℂ} (hz : z ∈ halfP) : z ^ 2 ∈ slitPlane := by
  have hz' : 0 < z.re := hz
  rw [mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left; simp [sq, him]; positivity
  · right; simp [sq]
    intro h
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · exact him h3

theorem exists_sq_of_mem_slitPlane {t : ℂ} (ht : t ∈ slitPlane) : ∃ z ∈ halfP, z ^ 2 = t := by
  have ht0 : t ≠ 0 := slitPlane_ne_zero ht
  refine ⟨cexp (log t / 2), ?_, ?_⟩
  · show 0 < (cexp (log t / 2)).re
    rw [exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · have := neg_pi_lt_arg t
      simp only [div_ofNat_im, log_im]; linarith
    · have h1 := arg_le_pi t
      have h2 : t.arg ≠ Real.pi := (mem_slitPlane_iff_arg.1 ht).1
      simp only [div_ofNat_im, log_im]
      have := lt_of_le_of_ne h1 h2
      linarith
  · rw [← exp_nat_mul]; push_cast
    rw [show (2 : ℂ) * (log t / 2) = log t by ring, exp_log ht0]

theorem image_sq_halfP : (fun z : ℂ => z ^ 2) '' halfP = slitPlane := by
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩; exact sq_mem_slitPlane hz
  · intro ht; obtain ⟨z, hz, h⟩ := exists_sq_of_mem_slitPlane ht; exact ⟨z, hz, h⟩

theorem injOn_sq_halfP : InjOn (fun z : ℂ => z ^ 2) halfP := by
  intro z hz w hw h
  simp only at h
  have hzw : (z - w) * (z + w) = 0 := by ring_nf; rw [h]; ring
  rcases mul_eq_zero.1 hzw with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have : (z + w).re = 0 := by rw [h1]; simp
    have hz' : 0 < z.re := hz
    have hw' : 0 < w.re := hw
    simp at this; linarith

theorem hasFDerivAt_sq (z : ℂ) :
    HasFDerivAt (fun z : ℂ => z ^ 2) (ContinuousLinearMap.mul ℝ ℂ (2 * z)) z := by
  have h := ((hasDerivAt_pow 2 z).hasFDerivAt).restrictScalars ℝ
  refine h.congr_fderiv ?_
  ext1 u
  simp
  ring

theorem det_mul_two (z : ℂ) : (ContinuousLinearMap.mul ℝ ℂ (2 * z)).det = ‖2 * z‖ ^ 2 := by
  show LinearMap.det (Algebra.lmul ℝ ℂ (2 * z)) = _
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply, normSq_eq_norm_sq]

/-- **The change of variables $t = z^2$** from the right half plane onto $\mathbb C$ (real Jacobian $|2z|^2$; the
negative real axis is null): $\int_{\mathbb C}g(t)\,dt = \int_{\operatorname{Re}z>0}|2z|^2g(z^2)\,dz$. -/
theorem lintegral_eq_lintegral_halfP_sq (g : ℂ → ℝ≥0∞) :
    ∫⁻ t, g t = ∫⁻ z in halfP, ((‖2 * z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * g (z ^ 2) := by
  have h1 : ∫⁻ t, g t = ∫⁻ t in slitPlane, g t := by
    have := lintegral_add_compl g isOpen_slitPlane.measurableSet (μ := volume)
    rw [setLIntegral_measure_zero _ _ volume_slitPlane_compl, add_zero] at this
    exact this.symm
  rw [h1, ← image_sq_halfP, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume isOpen_halfP.measurableSet
    (fun z _ => (hasFDerivAt_sq z).hasFDerivWithinAt) injOn_sq_halfP]
  refine setLIntegral_congr_fun isOpen_halfP.measurableSet fun z _ => ?_
  rw [det_mul_two, abs_of_nonneg (by positivity)]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]; congr 1

open QuadFormsKB.Tamagawa.Measure.SphereLerayC

theorem halfU_eq_preimage : halfU = (Units.val : ℂˣ → ℂ) ⁻¹' halfP := rfl

/-- The half-plane integral against `volU` on $\mathbb C^\times$ is the Lebesgue integral over $\operatorname{Re}z > 0$. -/
theorem setLIntegral_halfU (G : ℂ → ℝ≥0∞) : ∫⁻ β in halfU, G β ∂volU = ∫⁻ z in halfP, G z := by
  have hmap : volU.map (Units.val : ℂˣ → ℂ) = volume.restrict (range Units.val) :=
    measurableEmbedding_val.map_comap volume
  rw [← lintegral_indicator (isOpen_halfU.measurableSet), ← lintegral_indicator isOpen_halfP.measurableSet]
  have h := measurableEmbedding_val.lintegral_map (μ := volU) (halfP.indicator G)
  rw [hmap] at h
  have e : (fun β : ℂˣ => halfP.indicator G (β : ℂ)) = halfU.indicator fun β : ℂˣ => G β := by
    funext β; rw [halfU_eq_preimage]; rfl
  rw [← e, ← h, range_val]
  rw [show {z : ℂ | z ≠ 0} = {0}ᶜ from rfl]
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ({0}ᶜ : Set ℂ) := compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))
  rw [Measure.restrict_eq_self_of_ae_mem hae]

end Square


/-! ### Null sets in $\mathbb C^n$ -/

section Null

open QuadFormsKB.Tamagawa.Measure.SphereLerayC QuadFormsKB.Siegel

theorem eval_diag_cx {n : ℕ} (b z : Fin n → ℂ) : (QuadForm.diag b).eval z = ∑ i, b i * z i ^ 2 := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- **The null cone of a nondegenerate diagonal form over $\mathbb C$ has measure zero**: $\{x\in\mathbb C^{k+1} :
\sum_ia_ix_i^2 = 0\}$ is Lebesgue-null when $a_0\ne0$ (each complex line parallel to the $x_0$-axis meets it in at most two
points). -/
theorem volume_diagC_eval_eq_zero {k : ℕ} {a : Fin (k + 1) → ℂ} (ha : a 0 ≠ 0) :
    volume {x : Fin (k + 1) → ℂ | (QuadForm.diag a).eval x = 0} = 0 := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0
  have hp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0
  set R : (Fin k → ℂ) → ℂ := fun y => ∑ i : Fin k, a i.succ * y i ^ 2
  set T : Set (ℂ × (Fin k → ℂ)) := {p | a 0 * p.1 ^ 2 + R p.2 = 0}
  have hT : MeasurableSet T := measurableSet_eq_fun (by fun_prop) measurable_const
  have hS : {x : Fin (k + 1) → ℂ | (QuadForm.diag a).eval x = 0} = e ⁻¹' T := by
    ext x
    simp only [mem_preimage, T, R, eval_diag_cx, e,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    simp only [Set.mem_ofPred_eq, Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove_zero]
  rw [hS, hp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
  refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun y => ?_)
  simp only [Pi.zero_apply]
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-R y / a 0) (by norm_num : 0 < 2)
  have hsub : (fun x : ℂ => (x, y)) ⁻¹' T ⊆ {s, -s} := by
    intro x hx
    have hx' : a 0 * x ^ 2 + R y = 0 := hx
    have hx2 : x ^ 2 = s ^ 2 := by rw [hs, eq_div_iff ha]; linear_combination hx'
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hx2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

variable {n : ℕ}

theorem measurePreserving_smul_unit {v : ℂ} (hv : ‖v‖ = 1) :
    MeasurePreserving (fun x : Fin n → ℂ => v • x) volume volume := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  refine ⟨(scV n (Units.mk0 v hv0)).measurable, ?_⟩
  have h := map_scV_volume (n := n) (Units.mk0 v hv0)
  have hw : wt (-(2 * n : ℕ)) (Units.mk0 v hv0) = 1 := by
    have : ‖v‖₊ = 1 := by ext; simpa using hv
    simp [wt, this]
  rw [hw, one_smul] at h
  exact h

/-- The unit $u_j = e^{i/(j+1)}$ (pairwise distinct, $j\in\mathbb N$). -/
def uRot (j : ℕ) : ℂ := cexp ((1 / (j + 1 : ℝ) : ℝ) * I)

/-- A square root of $u_j$: $v_j = e^{i/(2(j+1))}$. -/
def vRot (j : ℕ) : ℂ := cexp ((1 / (2 * (j + 1)) : ℝ) * I)

theorem norm_vRot (j : ℕ) : ‖vRot j‖ = 1 := by rw [vRot, norm_exp_ofReal_mul_I]

theorem vRot_sq (j : ℕ) : vRot j ^ 2 = uRot j := by
  rw [vRot, uRot, ← exp_nat_mul]; congr 1; push_cast; field_simp

theorem uRot_injective : Function.Injective uRot := by
  intro i j h
  have key : ∀ j : ℕ, arg (uRot j) = 1 / (j + 1 : ℝ) := fun j => by
    rw [uRot, exp_mul_I, arg_cos_add_sin_mul_I]
    have h1 : (0 : ℝ) < 1 / (j + 1 : ℝ) := by positivity
    have h2 : 1 / (j + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ j := by positivity
      linarith
    constructor <;> linarith [Real.pi_gt_three]
  have := congrArg arg h
  rw [key, key] at this
  have h' : (i + 1 : ℝ) = j + 1 := by
    have hi : (0 : ℝ) < i + 1 := by positivity
    have hj : (0 : ℝ) < j + 1 := by positivity
    field_simp at this; linarith
  exact_mod_cast (by linarith : (i : ℝ) = j)

/-- The rotated negative ray: $\{x : uQ(x)\in(-\infty, 0)\}$. -/
def rayU (Q : QuadForm ℂ n) (u : ℂ) : Set (Fin n → ℂ) :=
  {x | (u * Q.eval x).im = 0 ∧ (u * Q.eval x).re < 0}

/-- $R_j = \{x : u_jQ(x)\in(-\infty, 0)\}$. -/
abbrev rayR (Q : QuadForm ℂ n) (j : ℕ) : Set (Fin n → ℂ) := rayU Q (uRot j)

theorem measurableSet_rayU (Q : QuadForm ℂ n) (u : ℂ) : MeasurableSet (rayU Q u) := by
  have hc : Measurable fun x : Fin n → ℂ => u * Q.eval x := (continuous_evalC Q).measurable.const_mul _
  exact (measurableSet_eq_fun (Complex.measurable_im.comp hc) measurable_const).inter
    (measurableSet_lt (Complex.measurable_re.comp hc) measurable_const)

theorem rayR_disjoint (Q : QuadForm ℂ n) : Pairwise (Function.onFun Disjoint (rayR Q)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hi hj => hij (uRot_injective ?_)
  set q := Q.eval x
  have hui : ‖uRot i‖ = 1 := by rw [uRot, norm_exp_ofReal_mul_I]
  have huj : ‖uRot j‖ = 1 := by rw [uRot, norm_exp_ofReal_mul_I]
  have ei : uRot i * q = ((uRot i * q).re : ℂ) := Complex.ext (by simp) (by rw [ofReal_im]; exact hi.1)
  have ej : uRot j * q = ((uRot j * q).re : ℂ) := Complex.ext (by simp) (by rw [ofReal_im]; exact hj.1)
  set r := (uRot i * q).re
  set r' := (uRot j * q).re
  have hr : r < 0 := hi.2
  have hr' : r' < 0 := hj.2
  have hnr : ‖uRot i * q‖ = ‖uRot j * q‖ := by rw [norm_mul, norm_mul, hui, huj]
  rw [ei, ej, norm_real, norm_real, Real.norm_of_nonpos hr.le, Real.norm_of_nonpos hr'.le] at hnr
  have hrr : r = r' := by linarith
  have hq : q ≠ 0 := by
    intro hq
    have : r = 0 := by simp [r, hq]
    linarith
  have : uRot i * q = uRot j * q := by rw [ei, ej, hrr]
  exact mul_right_cancel₀ hq this

/-- **The complement of the slit plane is null on $\mathbb C^n$**: if the null cone $\{Q = 0\}$ is Lebesgue-null, so is
$\{x : Q(x)\in(-\infty, 0]\}$. (The sets $\{u_jQ\in(-\infty,0)\}$ for distinct units $u_j$ are pairwise disjoint and are
rotations of each other; in a ball they have equal finite measure summing to at most the measure of the ball.) -/
theorem volume_eval_notMem_slitPlane (Q : QuadForm ℂ n) (hnull : volume {x : Fin n → ℂ | Q.eval x = 0} = 0) :
    volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0 := by
  have hsub : {x : Fin n → ℂ | Q.eval x ∉ slitPlane} ⊆ {x | Q.eval x = 0} ∪ rayU Q 1 := by
    intro x hx
    simp only [mem_ofPred_eq, mem_slitPlane_iff, not_or, not_lt, not_not] at hx
    rcases hx.1.lt_or_eq with h | h
    · right
      simp [rayU, hx.2, h]
    · left; exact Complex.ext (by simpa using h) (by simpa using hx.2)
  refine measure_mono_null hsub (measure_union_null hnull ?_)
  -- each ball meets `rayU Q 1` in a null set
  have hball : ∀ r : ℕ, volume (rayU Q 1 ∩ Metric.closedBall (0 : Fin n → ℂ) r) = 0 := by
    intro r
    set B := Metric.closedBall (0 : Fin n → ℂ) r
    have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
    have hrot : ∀ j, volume (rayR Q j ∩ B) = volume (rayU Q 1 ∩ B) := by
      intro j
      have hpre : (fun x => vRot j • x) ⁻¹' (rayU Q 1 ∩ B) = rayR Q j ∩ B := by
        ext x
        simp only [mem_preimage, mem_inter_iff, rayU, mem_ofPred_eq, eval_smulC, vRot_sq, B,
          Metric.mem_closedBall, dist_zero_right, norm_smul, norm_vRot, one_mul]
      rw [← hpre, (measurePreserving_smul_unit (norm_vRot j)).measure_preimage
        ((measurableSet_rayU Q 1).inter hB).nullMeasurableSet]
    have hdisj : Pairwise (Function.onFun Disjoint fun j => rayR Q j ∩ B) := fun i j hij =>
      (rayR_disjoint Q hij).mono inter_subset_left inter_subset_left
    have hU := measure_iUnion (μ := volume) hdisj fun j => (measurableSet_rayU Q (uRot j)).inter hB
    simp_rw [hrot] at hU
    by_contra h0
    have htop := ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) h0
    have hle : volume (⋃ j, rayR Q j ∩ B) ≤ volume B := measure_mono (iUnion_subset fun j => inter_subset_right)
    rw [hU, htop] at hle
    exact (measure_closedBall_lt_top (x := (0 : Fin n → ℂ)) (r := (r : ℝ))).ne (top_le_iff.1 hle)
  have : rayU Q 1 = ⋃ r : ℕ, rayU Q 1 ∩ Metric.closedBall (0 : Fin n → ℂ) r := by
    rw [← inter_iUnion]
    refine (inter_eq_left.2 fun x _ => ?_).symm
    obtain ⟨r, hr⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨r, by simpa using hr⟩
  rw [this]
  exact measure_iUnion_null hball

end Null


/-! ### The coarea formula for a complex quadratic form -/

section CoareaC

open QuadFormsKB.Tamagawa.Measure.SphereLerayC QuadFormsKB.Siegel

variable {n : ℕ} (Q : QuadForm ℂ n)

/-- **The orbital integral at a complex place** $\rho_\Phi(t) = \int_{S_t}\Phi\,d\sigma_t$ of $\Phi\ge0$ over the quadric
$S_t = \{x\in\mathbb C^n : Q(x) = t\}$ for the complex Leray measure $\sigma_t$ (`SphereLerayC.sigC`; it is $0$ at $t = 0$).
Parameters: `Q`, `Φ`, `t`. -/
@[kb "weil1965" "Sur la formule de Siegel: the integral of Φ over {Q = t} for |dx/dQ| (complex place) [unverified]"]
def orbC (Φ : (Fin n → ℂ) → ℝ≥0∞) (t : ℂ) : ℝ≥0∞ := ∫⁻ x, Φ x ∂sigC Q t

theorem orbC_zero (Φ : (Fin n → ℂ) → ℝ≥0∞) : orbC Q Φ 0 = 0 := by
  simp [orbC, sigC]

/-- The square root $s(t) = e^{\log t/2}$ ($s(t)^2 = t$ for $t\ne0$, $\operatorname{Re}s(t) > 0$ on the slit plane). -/
def sqrtC (t : ℂ) : ℂ := cexp (log t / 2)

theorem sqrtC_sq {t : ℂ} (ht : t ≠ 0) : sqrtC t ^ 2 = t := by
  rw [sqrtC, ← exp_nat_mul]; push_cast
  rw [show (2 : ℂ) * (log t / 2) = log t by ring, exp_log ht]

theorem sqrtC_ne_zero (t : ℂ) : sqrtC t ≠ 0 := exp_ne_zero _

theorem measurable_sqrtC : Measurable sqrtC :=
  Complex.measurable_exp.comp (Complex.measurable_log.div_const _)

/-- **Homogeneity**: $\rho_\Phi(s^2c) = |s|^{2(n-2)}\int_{S_c}\Phi(sx)\,d\sigma_c(x)$ for $s\ne0$. -/
theorem orbC_sq_mul {c s : ℂ} (hc : c ≠ 0) (hs : s ≠ 0) (hn : 2 ≤ n) {Φ : (Fin n → ℂ) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    orbC Q Φ (s ^ 2 * c) = ((‖s‖₊ ^ (2 * (n - 2)) : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, Φ (s • (x : Fin n → ℂ)) ∂sigC Q c :=
  lintegral_sigC_scale hc hs hn hΦ

/-- $t\mapsto\rho_\Phi(t)$ is measurable (by homogeneity it is $|t|^{n-2}\int_{S_1}\Phi(\sqrt t\,x)\,d\sigma_1$ off $0$). -/
theorem measurable_orbC (hn : 2 ≤ n) {Φ : (Fin n → ℂ) → ℝ≥0∞} (hΦ : Measurable Φ) : Measurable (orbC Q Φ) := by
  have := sigmaFinite_sigC (Q := Q) (c := 1) one_ne_zero (by omega)
  set g : ℂ → ℝ≥0∞ := fun t =>
    ((‖sqrtC t‖₊ ^ (2 * (n - 2)) : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, Φ (sqrtC t • (x : Fin n → ℂ)) ∂sigC Q 1
  have hg : Measurable g := by
    refine ((measurable_sqrtC.nnnorm.pow_const _).coe_nnreal_ennreal).mul ?_
    exact Measurable.lintegral_prod_right' (f := fun p : ℂ × SphC Q 1 => Φ (sqrtC p.1 • (p.2 : Fin n → ℂ)))
      (hΦ.comp ((measurable_sqrtC.comp measurable_fst).smul (measurable_subtype_coe.comp measurable_snd)))
  have e : orbC Q Φ = ({0}ᶜ : Set ℂ).piecewise g 0 := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp [orbC_zero]
    · rw [piecewise_eq_of_mem _ _ _ (show t ∈ ({0}ᶜ : Set ℂ) from ht)]
      conv_lhs => rw [show t = sqrtC t ^ 2 * 1 by rw [sqrtC_sq ht, mul_one]]
      exact orbC_sq_mul Q one_ne_zero (sqrtC_ne_zero t) hn hΦ
  rw [e]
  exact hg.piecewise (measurableSet_singleton 0).compl measurable_const

theorem image_polC_one : polC Q 1 '' (halfU ×ˢ univ) = {y | Q.eval y ∈ slitPlane} := by
  ext y
  constructor
  · rintro ⟨⟨β, x⟩, ⟨hβ, -⟩, rfl⟩
    show Q.eval (polC Q 1 (β, x)) ∈ slitPlane
    rw [polC, eval_smulC, x.2, mul_one]
    exact sq_mem_slitPlane hβ
  · intro hy
    obtain ⟨z, hz, hzt⟩ := exists_sq_of_mem_slitPlane hy
    have hz0 : z ≠ 0 := by rintro rfl; exact lt_irrefl _ (show (0 : ℂ).re > 0 from hz)
    have hx : Q.eval (z⁻¹ • y) = 1 := by
      rw [eval_smulC, inv_pow, hzt, inv_mul_cancel₀ (slitPlane_ne_zero hy)]
    refine ⟨(Units.mk0 z hz0, ⟨z⁻¹ • y, hx⟩), ⟨hz, mem_univ _⟩, ?_⟩
    show (z : ℂ) • z⁻¹ • y = y
    rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]

/-- **The coarea formula at a complex place** $\int_{\mathbb C^n}\Phi\,dx = \int_{\mathbb C}\rho_\Phi(t)\,dt$ (Leray), for $Q$
with $\{x : Q(x)\in(-\infty, 0]\}$ Lebesgue-null (`volume_eval_notMem_slitPlane`: e.g. every nondegenerate diagonal form,
`volume_diagC_eval_eq_zero`). -/
@[kb "weil1982" "§2.2 (dx = σ_t ⊗ dt on the fibres of Q, complex place) [unverified]"]
theorem lintegral_eq_lintegral_orbC (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ≥0∞} (hΦ : Measurable Φ) : ∫⁻ x, Φ x = ∫⁻ t, orbC Q Φ t := by
  have hS : MeasurableSet {y : Fin n → ℂ | Q.eval y ∈ slitPlane} :=
    isOpen_slitPlane.measurableSet.preimage (continuous_evalC Q).measurable
  have h1 : ∫⁻ x, Φ x = ∫⁻ y in {y : Fin n → ℂ | Q.eval y ∈ slitPlane}, Φ y := by
    have hc : volume ({y : Fin n → ℂ | Q.eval y ∈ slitPlane}ᶜ) = 0 := hnull
    have := lintegral_add_compl Φ hS (μ := volume)
    rw [setLIntegral_measure_zero _ _ hc, add_zero] at this
    exact this.symm
  rw [h1, ← image_polC_one, lintegral_fibrationC one_ne_zero hn hΦ]
  change ∫⁻ β in halfU, ((‖2 * 1 * (β : ℂ)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * orbC Q Φ ((β : ℂ) ^ 2 * 1) ∂volU = _
  rw [setLIntegral_halfU (fun z => ((‖2 * 1 * z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * orbC Q Φ (z ^ 2 * 1)),
    lintegral_eq_lintegral_halfP_sq (orbC Q Φ)]
  simp only [mul_one]

/-- $\rho_{\Phi\cdot g\circ Q} = g\cdot\rho_\Phi$. -/
theorem orbC_mul_comp (Φ : (Fin n → ℂ) → ℝ≥0∞) (hΦ : Measurable Φ) (g : ℂ → ℝ≥0∞) (t : ℂ) :
    orbC Q (fun x => Φ x * g (Q.eval x)) t = orbC Q Φ t * g t := by
  have h : ∀ x : SphC Q t, Φ x * g (Q.eval x) = Φ x * g t := fun x => by
    rw [show Q.eval (x : Fin n → ℂ) = t from x.2]
  rw [orbC, orbC]
  simp_rw [h]
  exact lintegral_mul_const _ (hΦ.comp measurable_subtype_coe)

/-- **The coarea formula, weighted**: $\int\Phi(x)\,g(Q(x))\,dx = \int\rho_\Phi(t)\,g(t)\,dt$. -/
theorem lintegral_mul_comp_eq_orbC (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ≥0∞} (hΦ : Measurable Φ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, Φ x * g (Q.eval x) = ∫⁻ t, orbC Q Φ t * g t := by
  have h := lintegral_eq_lintegral_orbC Q hn hnull (Φ := fun x => Φ x * g (Q.eval x))
    (hΦ.mul (hg.comp (continuous_evalC Q).measurable))
  rw [h]
  exact lintegral_congr fun t => orbC_mul_comp Q Φ hΦ g t

/-- **Push-forward**: $Q_*(\Phi\,dx) = \rho_\Phi\,dt$ on $\mathbb C$. -/
theorem map_withDensity_eq_orbC (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (volume.withDensity Φ).map Q.eval = volume.withDensity (orbC Q Φ) := by
  have hQm := (continuous_evalC Q).measurable
  ext s hs
  rw [Measure.map_apply hQm hs, withDensity_apply _ (hQm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hQm hs), ← lintegral_indicator hs]
  have h := lintegral_mul_comp_eq_orbC Q hn hnull hΦ (g := s.indicator 1) (measurable_one.indicator hs)
  have e1 : ∀ x, (Q.eval ⁻¹' s).indicator Φ x = Φ x * s.indicator 1 (Q.eval x) := fun x => by
    by_cases hx : Q.eval x ∈ s
    · simp [Set.indicator_of_mem (show x ∈ Q.eval ⁻¹' s from hx), Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem (show x ∉ Q.eval ⁻¹' s from hx), Set.indicator_of_notMem hx]
  have e2 : ∀ t, s.indicator (orbC Q Φ) t = orbC Q Φ t * s.indicator 1 t := fun t => by
    by_cases ht : t ∈ s
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  simp_rw [e1, e2]
  exact h

end CoareaC


/-! ### The Fourier transform of $\rho_\Phi$ and the Whittaker integral at a complex place -/

section FourierC

open QuadFormsKB.Tamagawa.Measure.SphereLerayC

variable {n : ℕ} (Q : QuadForm ℂ n)

/-- **The orbital integral of a real test function** $\Phi\ge0$ at a complex place: $\rho_\Phi(t)\in\mathbb R$ (`orbC` of
$\Phi$, as a real number). Parameters: `Q`, `Φ`, `t`. -/
def orbCR (Φ : (Fin n → ℂ) → ℝ) (t : ℂ) : ℝ := (orbC Q (fun x => ENNReal.ofReal (Φ x)) t).toReal

variable {Q}

theorem ae_orbC_lt_top (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦ : Integrable Φ) :
    ∀ᵐ t, orbC Q (fun x => ENNReal.ofReal (Φ x)) t < ∞ := by
  refine ae_lt_top (measurable_orbC Q hn hΦm.ennreal_ofReal) ?_
  rw [← lintegral_eq_lintegral_orbC Q hn hnull hΦm.ennreal_ofReal]
  exact hΦ.lintegral_lt_top.ne

/-- **The coarea formula against a bounded weight** (Bochner form): for $\Phi\ge0$ measurable and integrable and $g$
continuous, $\int_{\mathbb C}\rho_\Phi(t)\,g(t)\,dt = \int_{\mathbb C^n}\Phi(x)\,g(Q(x))\,dx$. -/
theorem integral_orbCR_mul (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ) {g : ℂ → ℂ}
    (hg : Continuous g) :
    ∫ t, (orbCR Q Φ t : ℂ) * g t = ∫ x, (Φ x : ℂ) * g (Q.eval x) := by
  have hm := hΦm.ennreal_ofReal
  have h1 : ∫ t, g t ∂(volume.withDensity (orbC Q fun x => ENNReal.ofReal (Φ x))) =
      ∫ t, (orbCR Q Φ t : ℂ) * g t := by
    rw [integral_withDensity_eq_integral_toReal_smul (measurable_orbC Q hn hm) (ae_orbC_lt_top hn hnull hΦm hΦ)]
    simp [orbCR, Complex.real_smul]
  have h2 : ∫ x, g (Q.eval x) ∂(volume.withDensity fun x => ENNReal.ofReal (Φ x)) =
      ∫ x, (Φ x : ℂ) * g (Q.eval x) := by
    rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp [ENNReal.toReal_ofReal (hΦ0 _), Complex.real_smul]
  rw [← h1, ← h2, ← map_withDensity_eq_orbC Q hn hnull hm,
    integral_map (continuous_evalC Q).measurable.aemeasurable hg.aestronglyMeasurable]

theorem integrable_orbCR (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦ : Integrable Φ) : Integrable fun t => (orbCR Q Φ t : ℂ) := by
  have hm := hΦm.ennreal_ofReal
  refine Integrable.ofReal (integrable_toReal_of_lintegral_ne_top (measurable_orbC Q hn hm).aemeasurable ?_)
  rw [← lintegral_eq_lintegral_orbC Q hn hnull hm]
  exact hΦ.lintegral_lt_top.ne

/-- **The Fourier transform of the orbital integral** at a complex place ($\mathbb C\cong\mathbb R^2$ with
$\langle t, w\rangle = \operatorname{Re}(t\bar w)$): $\hat\rho_\Phi(w) = \int_{\mathbb C^n}\Phi(x)\,e^{-2\pi i\langle Q(x), w\rangle}\,dx$. -/
theorem fourier_orbCR (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ) (w : ℂ) :
    𝓕 (fun t => (orbCR Q Φ t : ℂ)) w =
      ∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (-((w * (starRingEnd ℂ) (Q.eval x)).re : ℂ))) := by
  rw [Real.fourier_eq']
  have h := integral_orbCR_mul hn hnull hΦm hΦ0 hΦ
    (g := fun t => cexp (2 * Real.pi * I * (-((w * (starRingEnd ℂ) t).re : ℂ)))) (by fun_prop)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, Complex.inner]
  rw [mul_comm]
  congr 2
  push_cast; ring

/-- **The substitution $w = -2\bar b$** on $\mathbb C$ (real Jacobian $4$): $\int_{\mathbb C}G(-2\bar b)\,db =
\frac14\int_{\mathbb C}G(w)\,dw$. -/
theorem integral_neg_two_conj (G : ℂ → ℂ) :
    ∫ b : ℂ, G (-2 * (starRingEnd ℂ) b) = (1 / 4 : ℂ) * ∫ w : ℂ, G w := by
  have hc : MeasurePreserving (starRingEnd ℂ) volume volume := Complex.conjLIE.measurePreserving
  have h1 : ∫ b : ℂ, G (-2 * (starRingEnd ℂ) b) = ∫ b : ℂ, G (-2 * b) :=
    hc.integral_comp Complex.conjLIE.toHomeomorph.measurableEmbedding (fun b => G (-2 * b))
  have h2 := Measure.integral_comp_smul (volume : Measure ℂ) G (-2)
  simp only [Complex.finrank_real_complex] at h2
  rw [h1]
  have e : ∀ b : ℂ, ((-2 : ℝ) • b) = -2 * b := fun b => by rw [Complex.real_smul]; push_cast; ring
  simp_rw [e] at h2
  rw [h2]
  norm_num

/-- **The local identity at a complex place, regularized**: for $\Phi\ge0$ integrable and $\rho_\Phi$ continuous at $m$,
$$\lim_{c\to\infty}\int_{\mathbb C}e^{-|b|^2/c}\Big(\int_{\mathbb C^n}\Phi(x)\,\psi_{\mathbb C}(bQ(x))\,dx\Big)\psi_{\mathbb C}(-mb)\,db
  = \tfrac14\rho_\Phi(m),\qquad\psi_{\mathbb C}(z) = e^{2\pi i\cdot2\operatorname{Re}z}.$$ -/
@[kb "weil1965" "Sur la formule de Siegel: the local Whittaker integral is the integral over {Q = m} (complex place) [unverified]"]
theorem tendsto_whittakerRegC (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ) {m : ℂ}
    (hcont : ContinuousAt (orbCR Q Φ) m) :
    Tendsto (fun c : ℝ => ∫ b : ℂ, cexp (-c⁻¹ * ‖b‖ ^ 2) *
      (∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * Q.eval x).re))) *
        cexp (2 * Real.pi * I * (-(2 * (m * b).re))))
      atTop (𝓝 ((1 / 4 : ℂ) * orbCR Q Φ m)) := by
  have hc' : ContinuousAt (fun t => (orbCR Q Φ t : ℂ)) m := Complex.continuous_ofReal.continuousAt.comp hcont
  have hT := tendsto_integral_cexp_fourier (integrable_orbCR hn hnull hΦm hΦ) hc'
  have h4 : Tendsto (fun c : ℝ => 4 * c) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  refine ((hT.comp h4).const_mul (1 / 4 : ℂ)).congr fun c => ?_
  simp only [Function.comp_apply]
  rw [← integral_neg_two_conj]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [fourier_orbCR hn hnull hΦm hΦ0 hΦ, Complex.exp_add]
  have e1 : ‖-2 * (starRingEnd ℂ) b‖ = 2 * ‖b‖ := by
    rw [norm_mul, norm_neg, Complex.norm_conj]; norm_num
  have e2 : ⟪m, -2 * (starRingEnd ℂ) b⟫ = -2 * (m * b).re := by
    rw [Complex.inner, show -2 * (starRingEnd ℂ) b * (starRingEnd ℂ) m = -2 * (starRingEnd ℂ) (m * b) by
      rw [map_mul]; ring]
    simp
  have e3 : ∀ x : Fin n → ℂ, (-2 * (starRingEnd ℂ) b * (starRingEnd ℂ) (Q.eval x)).re = -2 * (b * Q.eval x).re := by
    intro x
    rw [show -2 * (starRingEnd ℂ) b * (starRingEnd ℂ) (Q.eval x) = -2 * (starRingEnd ℂ) (b * Q.eval x) by
      rw [map_mul]; ring]
    simp
  simp_rw [e1, e2, e3]
  have hc4 : -((4 * c)⁻¹ : ℝ) * ((2 * ‖b‖ : ℝ) : ℂ) ^ 2 = -(c⁻¹ : ℝ) * (‖b‖ : ℂ) ^ 2 := by
    push_cast
    rcases eq_or_ne (c : ℂ) 0 with h | h
    · rw [h]; simp
    · field_simp; ring
  rw [hc4]
  push_cast
  ring_nf

/-- **The local identity at a complex place, absolutely convergent form**: if
$b\mapsto\int\Phi(x)\psi_{\mathbb C}(bQ(x))\,dx$ is integrable on $\mathbb C$ (e.g. the Gaussian of the majorant for $n\ge3$),
then at every $m$ where $\rho_\Phi$ is continuous
$$\int_{\mathbb C}\Big(\int_{\mathbb C^n}\Phi(x)\,\psi_{\mathbb C}(bQ(x))\,dx\Big)\psi_{\mathbb C}(-mb)\,db = \tfrac14\rho_\Phi(m).$$ -/
@[kb "weil1965" "Sur la formule de Siegel: the local Whittaker integral is the integral over {Q = m} (complex place) [unverified]"]
theorem integral_whittakerC_eq_orbCR (hn : 2 ≤ n) (hnull : volume {x : Fin n → ℂ | Q.eval x ∉ slitPlane} = 0)
    {Φ : (Fin n → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ)
    (hW : Integrable fun b : ℂ => ∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * Q.eval x).re))) {m : ℂ}
    (hcont : ContinuousAt (orbCR Q Φ) m) :
    ∫ b : ℂ, (∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * Q.eval x).re))) *
        cexp (2 * Real.pi * I * (-(2 * (m * b).re))) = (1 / 4 : ℂ) * orbCR Q Φ m := by
  have hW' : Integrable fun b : ℂ => (∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * Q.eval x).re))) *
      cexp (2 * Real.pi * I * (-(2 * (m * b).re))) := by
    refine hW.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun b => ?_)
    rw [Complex.norm_exp]
    simp
  have h := Real.tendsto_integral_cexp_sq_smul hW'
  refine tendsto_nhds_unique h ((tendsto_whittakerRegC hn hnull hΦm hΦ0 hΦ hcont).congr fun c => ?_)
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [smul_eq_mul]
  ring

end FourierC

/-! ### Continuity of the orbital integral off $0$ -/

section RegularityC

open QuadFormsKB.Tamagawa.Measure.SphereLerayC

variable {n : ℕ} {Q : QuadForm ℂ n}

theorem finrank_cn : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]; simp [mul_comm]

/-- **Polynomial decay is integrable on $S_c$**: $\int_{S_c}(1+\|x\|)^{-(2n+1)}\,d\nu_c < \infty$ (from
$dx = |\beta|^{2n-2}d^2\beta\otimes\nu_c$ on the half plane, restricted to $\{\operatorname{Re}\beta > 0, |\beta| < 1\}$). -/
theorem lintegral_nuC_decay_lt_top {c : ℂ} (hc : c ≠ 0) (hn : 1 ≤ n) :
    ∫⁻ x, ENNReal.ofReal ((1 + ‖(x : Fin n → ℂ)‖) ^ (-(2 * n + 1 : ℝ))) ∂nuC Q c < ⊤ := by
  set f : SphC Q c → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + ‖(x : Fin n → ℂ)‖) ^ (-(2 * n + 1 : ℝ)))
  set G : (Fin n → ℂ) → ℝ≥0∞ := fun y => ENNReal.ofReal ((1 + ‖y‖) ^ (-(2 * n + 1 : ℝ)))
  have hG : Measurable G := by fun_prop
  have hGfin : ∫⁻ y, G y < ⊤ :=
    (integrable_one_add_norm (E := Fin n → ℂ) (μ := volume) (r := 2 * n + 1)
      (by rw [finrank_cn]; push_cast; linarith)).lintegral_lt_top
  have hlow : lamU n R0 * ∫⁻ x, f x ∂nuC Q c ≤ ∫⁻ y in polC Q c '' (halfU ×ˢ univ), G y := by
    rw [lintegral_polC_half hc hn hG]
    calc lamU n R0 * ∫⁻ x, f x ∂nuC Q c = ∫⁻ β in R0, ∫⁻ x, f x ∂nuC Q c ∂lamU n := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ β in R0, ∫⁻ x, G ((β : ℂ) • (x : Fin n → ℂ)) ∂nuC Q c ∂lamU n := by
          refine setLIntegral_mono' isOpen_R0.measurableSet fun β hβ => ?_
          refine lintegral_mono fun x => ?_
          simp only [f, G]
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
          rw [norm_smul]
          have : ‖(β : ℂ)‖ ≤ 1 := hβ.2.le
          nlinarith [norm_nonneg (x : Fin n → ℂ), norm_nonneg (β : ℂ)]
      _ ≤ _ := lintegral_mono_set R0_subset_halfU
  have h1 : ∫⁻ y in polC Q c '' (halfU ×ˢ univ), G y < ⊤ := lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hGfin
  exact ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hlow h1).ne lamU_R0_pos.ne'

theorem lintegral_sigC_decay_lt_top {c : ℂ} (hc : c ≠ 0) (hn : 1 ≤ n) :
    ∫⁻ x, ENNReal.ofReal ((1 + ‖(x : Fin n → ℂ)‖) ^ (-(2 * n + 1 : ℝ))) ∂sigC Q c < ⊤ := by
  rw [sigC, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lintegral_nuC_decay_lt_top hc hn)

theorem continuousAt_sqrtC_div {m : ℂ} (hm : m ≠ 0) : Tendsto (fun t : ℂ => sqrtC (t / m)) (𝓝 m) (𝓝 1) := by
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  have hc : ContinuousAt (fun t : ℂ => sqrtC (t / m)) m := by
    unfold sqrtC
    refine Complex.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.div_const ?_ _
    refine ContinuousAt.comp (g := log) (by rw [div_self hm]; exact continuousAt_clog h1) ?_
    exact continuousAt_id.div_const _
  have := hc.tendsto
  simpa [sqrtC, div_self hm] using this

/-- **Continuity of the orbital integral off $0$ at a complex place**: if $\Phi\ge0$ is continuous with
$\Phi(x)\le C(1+\|x\|)^{-(2n+1)}$ (e.g. a Schwartz function or the Gaussian), then $t\mapsto\rho_\Phi(t)$ is continuous at
every $m\ne0$. -/
theorem continuousAt_orbCR (hn : 2 ≤ n) {Φ : (Fin n → ℂ) → ℝ} (hΦc : Continuous Φ) (hΦ0 : ∀ x, 0 ≤ Φ x)
    {C : ℝ} (hdec : ∀ x, Φ x ≤ C * (1 + ‖x‖) ^ (-(2 * n + 1 : ℝ))) {m : ℂ} (hm : m ≠ 0) :
    ContinuousAt (orbCR Q Φ) m := by
  set s : ℝ := 2 * n + 1
  have hs : 0 ≤ s := by positivity
  set F : ℂ → ℝ≥0∞ := fun a => ∫⁻ x, ENNReal.ofReal (Φ (a • (x : Fin n → ℂ))) ∂sigC Q m
  set B : SphC Q m → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (C * 2 ^ s) * ENNReal.ofReal ((1 + ‖(x : Fin n → ℂ)‖) ^ (-s))
  have hBfin : ∫⁻ x, B x ∂sigC Q m ≠ ⊤ := by
    rw [lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_sigC_decay_lt_top hm (by omega)).ne
  have hC : 0 ≤ C := by
    have h1 := (hΦ0 0).trans (hdec 0)
    have h0 : (0 : ℝ) < (1 + ‖(0 : Fin n → ℂ)‖) ^ (-(2 * n + 1 : ℝ)) := by positivity
    exact nonneg_of_mul_nonneg_left h1 h0
  have hF : Tendsto F (𝓝 1) (𝓝 (F 1)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence B ?_ ?_ hBfin ?_
    · exact Eventually.of_forall fun a => (hΦc.comp (by fun_prop)).measurable.ennreal_ofReal
    · filter_upwards [Metric.ball_mem_nhds (1 : ℂ) (show (0 : ℝ) < 1 / 2 by norm_num)] with a ha
      refine Eventually.of_forall fun x => ?_
      simp only [B]
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((hdec _).trans ?_)
      have ha1 : 1 / 2 < ‖a‖ := by
        have h := norm_sub_norm_le (1 : ℂ) a
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at ha
        simp at h; linarith
      have hx : (1 + ‖(x : Fin n → ℂ)‖) / 2 ≤ 1 + ‖a • (x : Fin n → ℂ)‖ := by
        rw [norm_smul]
        nlinarith [norm_nonneg (x : Fin n → ℂ)]
      have h2 : (1 + ‖a • (x : Fin n → ℂ)‖) ^ (-s) ≤ ((1 + ‖(x : Fin n → ℂ)‖) / 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith)
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul] at h2
      calc C * (1 + ‖a • (x : Fin n → ℂ)‖) ^ (-(2 * n + 1 : ℝ))
          = C * (1 + ‖a • (x : Fin n → ℂ)‖) ^ (-s) := rfl
        _ ≤ C * ((1 + ‖(x : Fin n → ℂ)‖) ^ (-s) * 2 ^ s) := by gcongr
        _ = C * 2 ^ s * (1 + ‖(x : Fin n → ℂ)‖) ^ (-s) := by ring
    · refine Eventually.of_forall fun x => ?_
      exact (ENNReal.continuous_ofReal.comp (hΦc.comp (by fun_prop))).tendsto 1
  have hF1 : F 1 = orbC Q (fun x => ENNReal.ofReal (Φ x)) m := by simp [F, orbC]
  have hF1fin : F 1 ≠ ⊤ := by
    refine ne_top_of_le_ne_top hBfin (lintegral_mono fun x => ?_)
    simp only [one_smul, B]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((hdec _).trans ?_)
    have h2 : (1 : ℝ) ≤ 2 ^ s := Real.one_le_rpow (by norm_num) hs
    have h3 : (0 : ℝ) ≤ (1 + ‖(x : Fin n → ℂ)‖) ^ (-s) := by positivity
    change C * (1 + ‖(x : Fin n → ℂ)‖) ^ (-s) ≤ C * 2 ^ s * (1 + ‖(x : Fin n → ℂ)‖) ^ (-s)
    nlinarith [mul_le_mul_of_nonneg_left h2 hC]
  have ha := continuousAt_sqrtC_div hm
  have hev : ∀ᶠ t in 𝓝 m, orbC Q (fun x => ENNReal.ofReal (Φ x)) t =
      ((‖sqrtC (t / m)‖₊ ^ (2 * (n - 2)) : ℝ≥0) : ℝ≥0∞) * F (sqrtC (t / m)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show m ∈ ({0}ᶜ : Set ℂ) from hm)] with t ht
    have ht0 : t / m ≠ 0 := div_ne_zero ht hm
    have ht' : t = sqrtC (t / m) ^ 2 * m := by rw [sqrtC_sq ht0]; field_simp
    conv_lhs => rw [ht']
    exact orbC_sq_mul Q hm (sqrtC_ne_zero _) hn hΦc.measurable.ennreal_ofReal
  have hlim : Tendsto (fun t => orbC Q (fun x => ENNReal.ofReal (Φ x)) t) (𝓝 m)
      (𝓝 (orbC Q (fun x => ENNReal.ofReal (Φ x)) m)) := by
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    have h1 : Tendsto (fun t => ((‖sqrtC (t / m)‖₊ ^ (2 * (n - 2)) : ℝ≥0) : ℝ≥0∞)) (𝓝 m) (𝓝 1) := by
      have hcont : Continuous fun a : ℂ => ((‖a‖₊ ^ (2 * (n - 2)) : ℝ≥0) : ℝ≥0∞) := by fun_prop
      have := (hcont.tendsto 1).comp ha
      simpa [Function.comp_def] using this
    have h2 := hF.comp ha
    rw [← hF1, ← one_mul (F 1)]
    exact ENNReal.Tendsto.mul h1 (Or.inr hF1fin) h2 (Or.inr ENNReal.one_ne_top)
  rw [hF1] at hF1fin
  exact (ENNReal.tendsto_toReal hF1fin).comp hlim

end RegularityC

/-! ### The Gaussian of the majorant at a complex place -/

section GaussC

variable {n : ℕ} (a : Fin n → ℂ)

/-- **The Gaussian of the majorant at a complex place** of $Q = \sum_ia_ix_i^2$:
$\Phi_a(x) = \exp(-2\pi\sum_i|a_i||x_i|^2)$. Parameters: `a`, `x`. -/
def gaussMajC (x : Fin n → ℂ) : ℝ := Real.exp (-2 * Real.pi * ∑ i, ‖a i‖ * ‖x i‖ ^ 2)

theorem gaussMajC_nonneg (x : Fin n → ℂ) : 0 ≤ gaussMajC a x := (Real.exp_pos _).le

theorem continuous_gaussMajC : Continuous (gaussMajC a) := by unfold gaussMajC; fun_prop

/-- **Decay**: $\Phi_a(x)\le C(1+\|x\|)^{-(2n+1)}$ when all $a_i\ne0$ (sup norm on $\mathbb C^n$). -/
theorem gaussMajC_decay (ha : ∀ i, a i ≠ 0) :
    ∃ C, ∀ x, gaussMajC a x ≤ C * (1 + ‖x‖) ^ (-(2 * n + 1 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, fun x => ?_⟩
    have hx : ‖x‖ = 0 := by rw [Subsingleton.elim x 0, norm_zero]
    simp [gaussMajC, hx]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set α := Finset.univ.inf' hne fun i => ‖a i‖
  have hα : 0 < α := (Finset.lt_inf'_iff hne).2 fun i _ => norm_pos_iff.2 (ha i)
  have hsq : ∀ x : Fin n → ℂ, ‖x‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := fun x => by
    have h : ‖x‖ ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [← Real.sqrt_sq (norm_nonneg (x i))]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
    calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = ∑ i, ‖x i‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  refine ⟨2 ^ (2 * n + 1) * (1 + (2 * n + 1).factorial / (2 * Real.pi * α) ^ (2 * n + 1)), fun x => ?_⟩
  have hsum : 2 * Real.pi * α * ‖x‖ ^ 2 ≤ 2 * Real.pi * ∑ i, ‖a i‖ * ‖x i‖ ^ 2 := by
    have : α * ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖a i‖ * ‖x i‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ i))
        (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left (hsq x) hα.le
    have h3 := mul_le_mul_of_nonneg_left (h2.trans this) (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    linarith [show 2 * Real.pi * α * ‖x‖ ^ 2 = 2 * Real.pi * (α * ‖x‖ ^ 2) by ring]
  have hb := exp_neg_mul_sq_mul_pow_le (mul_pos (by positivity : (0:ℝ) < 2 * Real.pi) hα) (2 * n + 1)
    (norm_nonneg x)
  have hpos : (0 : ℝ) < (1 + ‖x‖) ^ (2 * n + 1) := by positivity
  rw [Real.rpow_neg (by positivity), show (2 * (n : ℝ) + 1) = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc gaussMajC a x * (1 + ‖x‖) ^ (2 * n + 1) ≤
        Real.exp (-(2 * Real.pi * α) * ‖x‖ ^ 2) * (1 + ‖x‖) ^ (2 * n + 1) := by
        gcongr
        unfold gaussMajC
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ _ := hb

theorem integrable_gaussMajC (ha : ∀ i, a i ≠ 0) : Integrable (gaussMajC a) := by
  obtain ⟨C, hC⟩ := gaussMajC_decay a ha
  refine ((integrable_one_add_norm (E := Fin n → ℂ) (μ := volume) (r := 2 * n + 1) ?_).const_mul C).mono'
    (continuous_gaussMajC a).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  · simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussMajC_nonneg a x)]
  exact hC x

/-- Real-parameter case of the one-variable complex oscillatory Gaussian. -/
theorem integral_gauss1C_real {α : ℝ} (hα : 0 < α) (r : ℝ) :
    ∫ z : ℂ, (Real.exp (-2 * Real.pi * α * ‖z‖ ^ 2) : ℂ) * cexp (2 * Real.pi * I * (2 * ((r : ℂ) * z ^ 2).re)) =
      ((Real.pi : ℂ) / (2 * Real.pi * α - 4 * Real.pi * I * r)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / (2 * Real.pi * α + 4 * Real.pi * I * r)) ^ (1 / 2 : ℂ) := by
  have hpt : ∀ p : ℝ × ℝ, (fun z : ℂ => (Real.exp (-2 * Real.pi * α * ‖z‖ ^ 2) : ℂ) *
      cexp (2 * Real.pi * I * (2 * ((r : ℂ) * z ^ 2).re))) (Complex.measurableEquivRealProd.symm p) =
      cexp (-(2 * Real.pi * α - 4 * Real.pi * I * r) * (p.1 : ℂ) ^ 2) *
      cexp (-(2 * Real.pi * α + 4 * Real.pi * I * r) * (p.2 : ℂ) ^ 2) := by
    intro p
    obtain ⟨x, y⟩ := p
    simp only [Complex.measurableEquivRealProd_symm_apply]
    rw [← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have h1 : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; ring
    have h2 : ((r : ℂ) * (⟨x, y⟩ : ℂ) ^ 2).re = r * (x ^ 2 - y ^ 2) := by
      simp [pow_two]
    rw [h1, h2]
    push_cast
    ring
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp' ]
  simp_rw [hpt]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod_mul (fun x : ℝ => cexp (-(2 * Real.pi * α - 4 * Real.pi * I * r) * (x : ℂ) ^ 2))
      (fun y : ℝ => cexp (-(2 * Real.pi * α + 4 * Real.pi * I * r) * (y : ℂ) ^ 2))]
  congr 1
  · refine integral_gaussian_complex ?_
    simp; positivity
  · refine integral_gaussian_complex ?_
    simp; positivity

/-- **The one-variable oscillatory Gaussian at a complex place**, in closed form (norm):
$\big|\int_{\mathbb C}e^{-2\pi\alpha|z|^2}e^{2\pi i\cdot2\operatorname{Re}(cz^2)}\,dz\big| = \frac1{2\sqrt{\alpha^2+4|c|^2}}$. -/
theorem norm_integral_gauss1C {α : ℝ} (hα : 0 < α) (c : ℂ) :
    ‖∫ z : ℂ, (Real.exp (-2 * Real.pi * α * ‖z‖ ^ 2) : ℂ) * cexp (2 * Real.pi * I * (2 * (c * z ^ 2).re))‖ =
      1 / (2 * Real.sqrt (α ^ 2 + 4 * ‖c‖ ^ 2)) := by
  -- reduce to c = ‖c‖ by a rotation
  have hrot : ∫ z : ℂ, (Real.exp (-2 * Real.pi * α * ‖z‖ ^ 2) : ℂ) * cexp (2 * Real.pi * I * (2 * (c * z ^ 2).re)) =
      ∫ z : ℂ, (Real.exp (-2 * Real.pi * α * ‖z‖ ^ 2) : ℂ) *
        cexp (2 * Real.pi * I * (2 * (((‖c‖ : ℝ) : ℂ) * z ^ 2).re)) := by
    set v : Circle := Circle.exp (-(Complex.arg c) / 2) with hv
    have hvc : (v : ℂ) = cexp ((-(Complex.arg c) / 2 : ℝ) * I) := by rw [hv, Circle.coe_exp]
    have hvv : (v : ℂ) ^ 2 * c = (‖c‖ : ℝ) := by
      have hc := Complex.norm_mul_exp_arg_mul_I c
      have h1 : (v : ℂ) ^ 2 * cexp (c.arg * I) = 1 := by
        rw [hvc, ← Complex.exp_nat_mul, ← Complex.exp_add]
        rw [show ((2 : ℕ) : ℂ) * (((-(c.arg) / 2 : ℝ) : ℂ) * I) + c.arg * I = 0 by push_cast; ring]
        simp
      calc (v : ℂ) ^ 2 * c = (v : ℂ) ^ 2 * (‖c‖ * cexp (c.arg * I)) := by rw [hc]
        _ = ‖c‖ * ((v : ℂ) ^ 2 * cexp (c.arg * I)) := by ring
        _ = _ := by rw [h1, mul_one]
    rw [← (rotation v).measurePreserving.integral_comp (rotation v).toHomeomorph.measurableEmbedding]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [rotation_apply, norm_mul, Circle.norm_coe, one_mul]
    congr 4
    rw [← hvv]; congr 2; ring
  rw [hrot, integral_gauss1C_real hα, norm_mul]
  have hs : 0 < α ^ 2 + 4 * ‖c‖ ^ 2 := by positivity
  set s := Real.sqrt (α ^ 2 + 4 * ‖c‖ ^ 2) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hs
  have hs2 : s ^ 2 = α ^ 2 + 4 * ‖c‖ ^ 2 := Real.sq_sqrt hs.le
  have hB : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      ‖(2 * Real.pi * α + ε * 4 * Real.pi * I * ‖c‖ : ℂ)‖ = 2 * Real.pi * s := by
    intro ε hε
    have hsq : ‖(2 * Real.pi * α + ε * 4 * Real.pi * I * ‖c‖ : ℂ)‖ ^ 2 = (2 * Real.pi * s) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, hs2]
      have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
      simp
      nlinarith [hε2]
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  have hB1 := hB 1 (Or.inl rfl)
  have hB2 := hB (-1) (Or.inr rfl)
  have e1 : (2 * Real.pi * α - 4 * Real.pi * I * ‖c‖ : ℂ) = 2 * Real.pi * α + ((-1 : ℝ) : ℂ) * 4 * Real.pi * I * ‖c‖ := by
    push_cast; ring
  have e2 : (2 * Real.pi * α + 4 * Real.pi * I * ‖c‖ : ℂ) = 2 * Real.pi * α + ((1 : ℝ) : ℂ) * 4 * Real.pi * I * ‖c‖ := by
    push_cast; ring
  rw [e1, e2, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real, norm_cpow_real,
    norm_div, norm_div, hB1, hB2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [← Real.rpow_add (by positivity), show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  field_simp

/-- The oscillatory integral $W(b) = \int_{\mathbb C^n}\Phi_a(x)\,e^{2\pi i\cdot2\operatorname{Re}(bQ(x))}\,dx$,
$Q(x) = \sum_ia_ix_i^2$. -/
def oscC (b : ℂ) : ℂ :=
  ∫ x : Fin n → ℂ, (gaussMajC a x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * ∑ i, a i * x i ^ 2).re))

theorem continuous_oscC (ha : ∀ i, a i ≠ 0) : Continuous (oscC a) := by
  unfold oscC
  have hg := continuous_gaussMajC a
  refine continuous_of_dominated (bound := gaussMajC a) (fun b => ?_) (fun b => ?_)
    (integrable_gaussMajC a ha) (Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : Fin n → ℂ => (gaussMajC a x : ℂ) * cexp (2 * Real.pi * I *
      (2 * (b * ∑ i, a i * x i ^ 2).re))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gaussMajC_nonneg a x)]
    have : (2 * Real.pi * I * (2 * ((b * ∑ i, a i * x i ^ 2).re : ℝ)) : ℂ) =
        ((2 * Real.pi * (2 * (b * ∑ i, a i * x i ^ 2).re) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
  · fun_prop

theorem norm_oscC_eq (ha : ∀ i, a i ≠ 0) (b : ℂ) :
    ‖oscC a b‖ = ∏ i, (1 / (2 * Real.sqrt (‖a i‖ ^ 2 + 4 * ‖b * a i‖ ^ 2))) := by
  have hpt : ∀ x : Fin n → ℂ, (gaussMajC a x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * ∑ i, a i * x i ^ 2).re)) =
      ∏ i, ((Real.exp (-2 * Real.pi * ‖a i‖ * ‖x i‖ ^ 2) : ℂ) *
        cexp (2 * Real.pi * I * (2 * ((b * a i) * x i ^ 2).re))) := fun x => by
    rw [Finset.prod_mul_distrib]
    simp_rw [Complex.ofReal_exp]
    rw [← Complex.exp_sum, ← Complex.exp_sum, gaussMajC, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    have hre : (b * ∑ i, a i * x i ^ 2).re = ∑ i, ((b * a i) * x i ^ 2).re := by
      rw [Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]
    rw [hre]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold oscC
  simp_rw [hpt]
  rw [show (volume : Measure (Fin n → ℂ)) = Measure.pi fun _ => volume from rfl,
    integral_fintype_prod_eq_prod (f := fun i (z : ℂ) => (Real.exp (-2 * Real.pi * ‖a i‖ * ‖z‖ ^ 2) : ℂ) *
        cexp (2 * Real.pi * I * (2 * ((b * a i) * z ^ 2).re))), norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_integral_gauss1C (norm_pos_iff.2 (ha i)) _

theorem gauss1C_factor_le {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    1 / (2 * Real.sqrt (A ^ 2 + 4 * (t * A) ^ 2)) ≤ 1 / A * (1 + t)⁻¹ := by
  have h : A * (1 + t) / 2 ≤ Real.sqrt (A ^ 2 + 4 * (t * A) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (A * (1 + t)), sq_nonneg (A * t), sq_nonneg A, mul_nonneg (sq_nonneg A) (sq_nonneg t),
      mul_nonneg (sq_nonneg A) ht]
  have hp : 0 < A * (1 + t) := by positivity
  calc 1 / (2 * Real.sqrt (A ^ 2 + 4 * (t * A) ^ 2)) ≤ 1 / (2 * (A * (1 + t) / 2)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = 1 / A * (1 + t)⁻¹ := by field_simp

/-- **Absolute convergence of the complex Whittaker integral for the Gaussian**, $n\ge3$:
$b\mapsto W(b)$ is integrable on $\mathbb C$ (it is $O((1+|b|)^{-n})$). -/
theorem integrable_oscC (ha : ∀ i, a i ≠ 0) (hn : 3 ≤ n) : Integrable (oscC a) := by
  set K := ∏ i, (1 / ‖a i‖)
  have hK : 0 ≤ K := Finset.prod_nonneg fun i _ => by have := norm_nonneg (a i); positivity
  refine ((integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3) (by simp [Complex.finrank_real_complex]; norm_num)).const_mul
    K).mono' (continuous_oscC a ha).aestronglyMeasurable (Eventually.of_forall fun b => ?_)
  rw [norm_oscC_eq a ha b]
  have h1 : ∏ i, (1 / (2 * Real.sqrt (‖a i‖ ^ 2 + 4 * ‖b * a i‖ ^ 2))) ≤ ∏ i, (1 / ‖a i‖ * (1 + ‖b‖)⁻¹) := by
    refine Finset.prod_le_prod₀ (fun i _ => by have := norm_nonneg (a i); positivity) fun i _ => ?_
    rw [norm_mul]
    exact gauss1C_factor_le (norm_pos_iff.2 (ha i)) (norm_nonneg b)
  refine h1.trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hb : 0 < 1 + ‖b‖ := by positivity
  rw [Real.rpow_neg hb.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  gcongr
  rw [← inv_pow]
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by linarith [norm_nonneg b])) hn

end GaussC

/-! ### Whittaker = orbital integral for the Gaussian of the majorant at a complex place -/

section WhittakerGaussC

open QuadFormsKB.Tamagawa.Measure.SphereLerayC

/-- The orbital integral of the complex Gaussian of the majorant is finite off $0$. -/
theorem orbC_gaussMajC_ne_top {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (Q : QuadForm ℂ n) {t : ℂ}
    (ht : t ≠ 0) : orbC Q (fun x => ENNReal.ofReal (gaussMajC a x)) t ≠ ⊤ := by
  obtain ⟨C, hC⟩ := gaussMajC_decay a ha
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_sigC_decay_lt_top (Q := Q) ht hn).ne)
    (?_ : orbC Q _ t ≤ ENNReal.ofReal C * _)
  rw [orbC, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul' (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hC _)

/-- **Whittaker integral = orbital integral for the Gaussian, complex place** ($Q = \sum_ia_ix_i^2$ over $\mathbb C$, all
$a_i\ne0$, $n = k+1\ge3$, $m\ne0$, $\psi_{\mathbb C}(z) = e^{2\pi i\cdot2\operatorname{Re}z}$, Lebesgue measures): the integral
converges absolutely and
$$\int_{\mathbb C}\Big(\int_{\mathbb C^n}\Phi_a(x)\,\psi_{\mathbb C}(bQ(x))\,dx\Big)\psi_{\mathbb C}(-mb)\,db
  = \tfrac14\int_{\{Q = m\}}\Phi_a\,d\sigma_m,\qquad\Phi_a(x) = e^{-2\pi\sum_i|a_i||x_i|^2}.$$
With the self-dual measure $2\,dx\,dy$ on each copy of $\mathbb C$ the left side is multiplied by $2^{n+1}$, giving
$2^{n-1}\rho_{\Phi_a}(m)$: the complex factor of the library's indefinite Siegel formula (`sigInfNF`). -/
@[kb "weil1965" "Sur la formule de Siegel: archimedean Whittaker integral = integral over {Q = m}, complex place [unverified]"]
theorem whittakerC_gaussMajC_eq_orbCR {k : ℕ} (a : Fin (k + 1) → ℂ) (ha : ∀ i, a i ≠ 0) (hk : 2 ≤ k) {m : ℂ}
    (hm : m ≠ 0) :
    ∫ b : ℂ, (∫ x, (gaussMajC a x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * (QuadForm.diag a).eval x).re))) *
        cexp (2 * Real.pi * I * (-(2 * (m * b).re))) =
      (1 / 4 : ℂ) * orbCR (QuadForm.diag a) (gaussMajC a) m := by
  obtain ⟨C, hC⟩ := gaussMajC_decay a ha
  have hW : Integrable fun b : ℂ =>
      ∫ x, (gaussMajC a x : ℂ) * cexp (2 * Real.pi * I * (2 * (b * (QuadForm.diag a).eval x).re)) := by
    simp_rw [eval_diag_cx]
    exact integrable_oscC a ha (by omega)
  exact integral_whittakerC_eq_orbCR (by omega)
    (volume_eval_notMem_slitPlane _ (volume_diagC_eval_eq_zero (ha 0)))
    (continuous_gaussMajC a).measurable (gaussMajC_nonneg a) (integrable_gaussMajC a ha) hW
    (continuousAt_orbCR (by omega) (continuous_gaussMajC a) (gaussMajC_nonneg a) hC hm)

end WhittakerGaussC

end QuadFormsKB.SiegelWeil.Orbital
