import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchSplit
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchComplex

/-!
# Two integrals against the Leray measures of $SO(\langle1,D\rangle)$ at an archimedean place

**Layer:** the archimedean local factors of the measure comparison for the binary torus.  For a point $x$ of the group
$SO(\langle1,D\rangle)$ at an archimedean place $w$ put
$t(x) = x_{00} + s\,x_{10}$ where $s^2 = -D$: this is the coordinate of $x e_0$ at the first place of $E = F(\sqrt{-D})$
over $w$, it is multiplicative ($t(xy) = t(x)t(y)$) and non-zero.  Indices are 0-based: $x_{00}$ and $x_{10}$ are the
two entries of the first column.

**Proves**
* **`lintegral_splitWeight`** (split real place, $\delta>0$, $s = \sqrt\delta$, $Q = \langle1,-\delta\rangle$, $\mu$ the Leray
  measure of $SO(Q)(\mathbb R)$):
  $$\int_{SO(Q)(\mathbb R)}2\max\bigl(0,\ 1-|\log|t(x)||\bigr)\,d\mu(x) = \frac{1}{2\delta\sqrt\delta}.$$
  *Proof.* Every $x$ has $x_{00}\ne0$.  The open set $R = \{x_{00}>0\}$ is $\{\rho(\gamma(\tau)):\tau\in\mathbb R\}$
  (`exists_rotSec_eq`, with $\gamma(\tau) = (\cosh\tau,\sinh\tau/s)$) and $t(\rho(\gamma(\tau))) = e^\tau$; by
  `lerayMeasure_rotSec_hypArc` the restriction of $\mu$ to $R$ is the image of $\frac{1}{8\delta\sqrt\delta}\,d\tau$ under
  $\tau\mapsto\rho(\gamma(\tau))$.  The complement of $R$ is $-R$, and $\mu$ is invariant under multiplication by
  $-1\in SO(Q)(\mathbb R)$, which changes $t$ to $-t$.  Hence the integral is
  $2\cdot\frac{1}{8\delta\sqrt\delta}\int_{\mathbb R}2(1-|\tau|)_+\,d\tau = \frac{1}{2\delta\sqrt\delta}$.
* **`lintegral_complexWeight`** (complex place, $D\ne0$, $s^2=-D$, $Q = \langle1,D\rangle$, $\mu$ the Leray measure of
  $SO(Q)(\mathbb C)$):
  $$\int_{SO(Q)(\mathbb C)}2\pi\max\bigl(0,\ 1-2|\log\|t(x)\||\bigr)\,d\mu(x) = \frac{\pi^2}{32\,|D|^3}.$$
  *Proof.* Every $x$ is $\rho(\gamma(\tau))$ for a unique $\tau$ in the strip $\{-\pi<\operatorname{Im}\tau\le\pi\}$
  (`exists_rotSecC_eq`, `arcC_injOn_strip`; $\gamma(\tau) = (\cosh\tau, s^{-1}\sinh\tau)$), and
  $t(\rho(\gamma(\tau))) = e^\tau$, so $\log\|t\| = \operatorname{Re}\tau$.  By `lerayMeasureC_rotSecC_arcC` the measure
  $\mu$ is the image of $\frac{1}{64|D|^3}\,d\tau$ restricted to the strip, and
  $\int_{\text{strip}}2\pi(1-2|\operatorname{Re}\tau|)_+\,d\tau = 2\pi\cdot2\pi\cdot\tfrac12$.
-/

open MeasureTheory Measure Set Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.ArchVol
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray
  QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
  QuadFormsKB.Tamagawa.Measure.OrbitalComplex

/-! ### The tent function -/

section Tent

/-- $\int_{\mathbb R}\max(0,1-|r|)\,dr = 1$. -/
theorem integral_tent_one : ∫ r : ℝ, max 0 (1 - |r|) = 1 := by
  have hc : Continuous fun r : ℝ => max 0 (1 - |r|) := by fun_prop
  have hz : ∀ r ∉ Ioc (-1 : ℝ) 1, max 0 (1 - |r|) = 0 := by
    intro r hr
    have : 1 ≤ |r| := by
      by_contra h
      replace h := not_le.mp h
      exact hr ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩
    exact max_eq_left (by linarith)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (-1 : ℝ)..0, max 0 (1 - |x|) = ∫ x in (-1 : ℝ)..0, (1 + x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simp only
    rw [abs_of_nonpos hx.2, max_eq_right (by linarith [hx.1])]
    ring
  have h2 : ∫ x in (0 : ℝ)..1, max 0 (1 - |x|) = ∫ x in (0 : ℝ)..1, (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simp only
    rw [abs_of_nonneg hx.1, max_eq_right (by linarith [hx.2])]
  rw [h1, h2, intervalIntegral.integral_add (by simp) (by simp),
    intervalIntegral.integral_sub (by simp) (by simp)]
  simp [integral_id]
  norm_num

/-- $\int_{\mathbb R}\max(0,1-a|r|)\,dr = 1/a$ for $a>0$ (as a Lebesgue integral of a non-negative function). -/
theorem lintegral_tent {a : ℝ} (ha : 0 < a) :
    ∫⁻ r : ℝ, ENNReal.ofReal (max 0 (1 - a * |r|)) = ENNReal.ofReal (1 / a) := by
  have hz : ∀ r ∉ Icc (-1 : ℝ) 1, max 0 (1 - |r|) = 0 := by
    intro r hr
    have : 1 ≤ |r| := by
      by_contra h
      replace h := not_le.mp h
      exact hr ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩
    exact max_eq_left (by linarith)
  have hint : Integrable fun r : ℝ => max 0 (1 - |r|) :=
    (show Continuous fun r : ℝ => max 0 (1 - |r|) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc hz)
  have hint' : Integrable fun r : ℝ => max 0 (1 - a * |r|) := by
    have := hint.comp_mul_left' ha.ne'
    simpa [abs_mul, abs_of_pos ha] using this
  have h : ∫ r : ℝ, max 0 (1 - a * |r|) = 1 / a := by
    have := Measure.integral_comp_mul_left (fun r : ℝ => max 0 (1 - |r|)) a
    simp only [abs_mul, abs_of_pos ha] at this
    rw [this, integral_tent_one]
    simp [abs_inv, abs_of_pos ha]
  rw [← ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun r => le_max_left _ _), h]

end Tent

/-! ### Rotations: every element of $SO(\langle1,D\rangle)$ is a rotation -/

section Real

variable {δ : ℝ}

/-- **The coordinate** $t(x) = x_{00} + \sqrt\delta\,x_{10}$ of $x\in SO(\langle1,-\delta\rangle)(\mathbb R)$
(0-based entries: the two entries of the first column), the coordinate of $xe_0$ at the first place of
$E = F(\sqrt\delta)$ over the split real place. -/
def splitCoord (δ : ℝ) (x : ArchSO (QuadForm.diag ![1, -δ])) : ℝ :=
  ArchSOInst.mat _ x 0 0 + Real.sqrt δ * ArchSOInst.mat _ x 1 0

theorem continuous_splitCoord (δ : ℝ) : Continuous (splitCoord δ) := by
  have h := ArchSOInst.continuous_mat (QuadForm.diag ![1, -δ])
  exact (h.matrix_elem 0 0).add (continuous_const.mul (h.matrix_elem 1 0))

/-- Every element of $SO(\langle1,D\rangle)(\mathbb R)$ is the rotation with its own first column. -/
theorem exists_rotSec_eq {D : ℝ} (hD : D ≠ 0) (x : ArchSO (QuadForm.diag ![1, D])) :
    ∃ u, rotSec D u = x := by
  have hg : (ArchSOInst.mat _ x)ᵀ * BinaryNormOne.hessD D * ArchSOInst.mat _ x = BinaryNormOne.hessD D := by
    have := ((mem_soReal_iff _ _).mp (ArchSOInst.incl_mem (QuadForm.diag ![1, D]) x)).1
    rwa [hessian_diag_one_D] at this
  obtain ⟨h1, h2, -⟩ := BinaryNormOne.orth_eq_rotMat (K := ℝ) two_ne_zero hD hg
  rw [ArchSOInst.det_mat] at h1
  have hu : (QuadForm.diag ![1, D]).eval ![ArchSOInst.mat _ x 0 0, ArchSOInst.mat _ x 1 0] = 1 := by
    rw [eval_diag_one_D]; simpa using h2
  refine ⟨⟨![ArchSOInst.mat _ x 0 0, ArchSOInst.mat _ x 1 0], hu⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  change ArchSOInst.mat _ (rotSec D _) = ArchSOInst.mat _ x
  rw [mat_rotSec]
  exact h1.symm

theorem entries_rotSec (u : Sph (QuadForm.diag ![1, -δ]) 1) :
    ArchSOInst.mat _ (rotSec (-δ) u) 0 0 = (u : Fin 2 → ℝ) 0 ∧
      ArchSOInst.mat _ (rotSec (-δ) u) 1 0 = (u : Fin 2 → ℝ) 1 := by
  rw [mat_rotSec]
  simp [BinaryNormOne.rotMat]

/-- The map $\tau\mapsto\rho(\gamma(\tau))$, $\gamma(\tau) = (\cosh\tau, \sinh\tau/\sqrt\delta)$. -/
def hypRot (hδ : 0 < δ) (τ : ℝ) : ArchSO (QuadForm.diag ![1, -δ]) := rotSec (-δ) (hypArc hδ τ)

theorem continuous_hypArc (hδ : 0 < δ) : Continuous (hypArc hδ) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [hypVec]; fun_prop
  · simp only [hypVec]; fun_prop

theorem continuous_hypRot (hδ : 0 < δ) : Continuous (hypRot hδ) :=
  continuous_rotSec.comp (continuous_hypArc hδ)

theorem splitCoord_hypRot (hδ : 0 < δ) (τ : ℝ) : splitCoord δ (hypRot hδ τ) = Real.exp τ := by
  have hs0 : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  obtain ⟨h0, h1⟩ := entries_rotSec (hypArc hδ τ)
  unfold splitCoord hypRot
  rw [h0, h1]
  simp only [hypArc, hypVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul, Real.cosh_add_sinh]

theorem mat_zero_zero_hypRot (hδ : 0 < δ) (τ : ℝ) : 0 < ArchSOInst.mat _ (hypRot hδ τ) 0 0 := by
  obtain ⟨h0, -⟩ := entries_rotSec (hypArc hδ τ)
  unfold hypRot
  rw [h0]
  simp only [hypArc, hypVec, Matrix.cons_val_zero]
  exact Real.cosh_pos τ

/-- Every element of $SO(\langle1,-\delta\rangle)(\mathbb R)$ has $x_{00}\ne0$. -/
theorem mat_zero_zero_ne (hδ : 0 < δ) (x : ArchSO (QuadForm.diag ![1, -δ])) :
    ArchSOInst.mat _ x 0 0 ≠ 0 := by
  obtain ⟨u, rfl⟩ := exists_rotSec_eq (neg_ne_zero.mpr hδ.ne') x
  obtain ⟨h0, -⟩ := entries_rotSec u
  rw [h0]
  intro h
  have := norm_one_of_sph u
  rw [h] at this
  nlinarith [sq_nonneg ((u : Fin 2 → ℝ) 1)]

/-- Every element of $SO(\langle1,-\delta\rangle)(\mathbb R)$ with $x_{00}>0$ is $\rho(\gamma(\tau))$. -/
theorem exists_hypRot_eq (hδ : 0 < δ) {x : ArchSO (QuadForm.diag ![1, -δ])}
    (hx : 0 < ArchSOInst.mat _ x 0 0) : ∃ τ, hypRot hδ τ = x := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  obtain ⟨u, rfl⟩ := exists_rotSec_eq (neg_ne_zero.mpr hδ.ne') x
  obtain ⟨h0, h1⟩ := entries_rotSec u
  rw [h0] at hx
  have hu := norm_one_of_sph u
  set a := (u : Fin 2 → ℝ) 0 with ha
  set b := (u : Fin 2 → ℝ) 1 with hb
  have hsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  refine ⟨Real.arsinh (Real.sqrt δ * b), ?_⟩
  have hc : Real.cosh (Real.arsinh (Real.sqrt δ * b)) = a := by
    rw [Real.cosh_arsinh]
    have : 1 + (Real.sqrt δ * b) ^ 2 = a ^ 2 := by
      rw [mul_pow, hsq]; linarith
    rw [this, Real.sqrt_sq hx.le]
  have hsn : (Real.sqrt δ)⁻¹ * Real.sinh (Real.arsinh (Real.sqrt δ * b)) = b := by
    rw [Real.sinh_arsinh, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have : hypArc hδ (Real.arsinh (Real.sqrt δ * b)) = u := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simpa [hypArc, hypVec] using hc
    · simpa [hypArc, hypVec] using hsn
  unfold hypRot
  rw [this]

/-- **The element $-1$** of $SO(\langle1,D\rangle)(\mathbb R)$ (the matrix $-I_2$, of determinant $1$). -/
def negSO (D : ℝ) : ArchSO (QuadForm.diag ![1, D]) :=
  ArchSOInst.mk _ (-1) ((mem_soReal_iff _ _).2 ⟨by simp, by simp [Matrix.det_neg]⟩)

theorem mat_negSO_mul (D : ℝ) (x : ArchSO (QuadForm.diag ![1, D])) :
    ArchSOInst.mat _ (negSO D * x) = -ArchSOInst.mat _ x := by
  rw [ArchSOInst.mat_mul]
  have : ArchSOInst.mat _ (negSO D) = -1 := rfl
  rw [this]
  simp

theorem splitCoord_negSO_mul (x : ArchSO (QuadForm.diag ![1, -δ])) :
    splitCoord δ (negSO (-δ) * x) = -splitCoord δ x := by
  unfold splitCoord
  rw [mat_negSO_mul]
  simp only [Matrix.neg_apply]
  ring

/-- The weight function of the split real place. -/
def splitWeight (δ : ℝ) (x : ArchSO (QuadForm.diag ![1, -δ])) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * max 0 (1 - |Real.log (|splitCoord δ x|)|))

theorem measurable_splitWeight (δ : ℝ) : Measurable (splitWeight δ) := by
  have h : Measurable fun r : ℝ => ENNReal.ofReal (2 * max 0 (1 - |Real.log (|r|)|)) := by fun_prop
  exact h.comp (continuous_splitCoord δ).measurable

theorem splitWeight_negSO_mul (x : ArchSO (QuadForm.diag ![1, -δ])) :
    splitWeight δ (negSO (-δ) * x) = splitWeight δ x := by
  unfold splitWeight
  rw [splitCoord_negSO_mul, abs_neg]

theorem splitWeight_hypRot (hδ : 0 < δ) (τ : ℝ) :
    splitWeight δ (hypRot hδ τ) = ENNReal.ofReal (2 * max 0 (1 - |τ|)) := by
  unfold splitWeight
  rw [splitCoord_hypRot, abs_of_pos (Real.exp_pos _), Real.log_exp]

/-- The Leray measure of $SO(\langle1,-\delta\rangle)(\mathbb R)$. -/
abbrev leraySplit (hδ : 0 < δ) : Measure (ArchSO (QuadForm.diag ![1, -δ])) :=
  lerayMeasure (QuadForm.diag ![1, -δ]) (gramDetR_diag_one_D_ne_zero (neg_ne_zero.mpr hδ.ne'))

/-- The open branch $\{x_{00}>0\}$. -/
def branchPos (δ : ℝ) : Set (ArchSO (QuadForm.diag ![1, -δ])) := {x | 0 < ArchSOInst.mat _ x 0 0}

theorem isOpen_branchPos (δ : ℝ) : IsOpen (branchPos δ) :=
  isOpen_lt continuous_const ((ArchSOInst.continuous_mat _).matrix_elem 0 0)

/-- **The Leray measure on the branch $x_{00}>0$** is the image of $\frac{1}{8\delta\sqrt\delta}\,d\tau$ under
$\tau\mapsto\rho(\gamma(\tau))$. -/
theorem restrict_branchPos (hδ : 0 < δ) :
    (leraySplit hδ).restrict (branchPos δ) =
      ((ENNReal.ofReal (1 / (8 * δ * Real.sqrt δ))) • (volume : Measure ℝ)).map (hypRot hδ) := by
  ext A hA
  have hF : Measurable (hypRot hδ) := (continuous_hypRot hδ).measurable
  rw [Measure.restrict_apply hA, Measure.map_apply hF hA, Measure.smul_apply, smul_eq_mul]
  have hA' : A ∩ branchPos δ = hypRot hδ '' (hypRot hδ ⁻¹' A) := by
    ext y
    constructor
    · rintro ⟨hyA, hy⟩
      obtain ⟨τ, rfl⟩ := exists_hypRot_eq hδ hy
      exact ⟨τ, hyA, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨hτ, mat_zero_zero_hypRot hδ τ⟩
  rw [hA']
  have := lerayMeasure_rotSec_hypArc hδ (hF hA)
  rw [Set.image_image] at this
  exact this

/-- **The integral of the split weight against the Leray measure of $SO(\langle1,-\delta\rangle)(\mathbb R)$.**

$$\int 2\max(0,\ 1-|\log|t(x)||)\,d\mu(x) = \frac{1}{2\delta\sqrt\delta},$$
the archimedean local factor at a split real place of the measure comparison for the binary non-compact case. -/
@[kb "weil1982" "§2.2 (gauge forms at the archimedean places) [unverified]"]
theorem lintegral_splitWeight (hδ : 0 < δ) :
    ∫⁻ x, ENNReal.ofReal (2 * max 0 (1 - |Real.log (|splitCoord δ x|)|)) ∂(leraySplit hδ) =
      ENNReal.ofReal (1 / (2 * δ * Real.sqrt δ)) := by
  have hQ := gramDetR_diag_one_D_ne_zero (neg_ne_zero.mpr hδ.ne')
  have := isHaarMeasure_lerayMeasure hQ
  change ∫⁻ x, splitWeight δ x ∂(leraySplit hδ) = _
  have hR : MeasurableSet (branchPos δ) := (isOpen_branchPos δ).measurableSet
  rw [← lintegral_add_compl _ hR]
  -- the complement is the translate of the branch by `-1`
  have hneg : ∫⁻ x in (branchPos δ)ᶜ, splitWeight δ x ∂(leraySplit hδ) =
      ∫⁻ x in branchPos δ, splitWeight δ x ∂(leraySplit hδ) := by
    rw [← lintegral_indicator hR.compl, ← lintegral_indicator hR,
      ← lintegral_mul_left_eq_self ((branchPos δ).indicator (splitWeight δ)) (negSO (-δ))]
    refine lintegral_congr fun x => ?_
    by_cases hx : 0 < ArchSOInst.mat _ x 0 0
    · have hx' : negSO (-δ) * x ∉ branchPos δ := by
        show ¬ 0 < ArchSOInst.mat _ (negSO (-δ) * x) 0 0
        rw [mat_negSO_mul]; simp only [Matrix.neg_apply]; linarith
      rw [indicator_of_notMem hx', indicator_of_notMem]
      exact fun h => h hx
    · have hx0 := mat_zero_zero_ne hδ x
      have hxn : ArchSOInst.mat _ x 0 0 < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
      have hx' : negSO (-δ) * x ∈ branchPos δ := by
        show 0 < ArchSOInst.mat _ (negSO (-δ) * x) 0 0
        rw [mat_negSO_mul]; simp only [Matrix.neg_apply]; linarith
      rw [indicator_of_mem hx', indicator_of_mem (show x ∈ (branchPos δ)ᶜ from hx), splitWeight_negSO_mul]
  have hpos : ∫⁻ x in branchPos δ, splitWeight δ x ∂(leraySplit hδ) =
      ENNReal.ofReal (1 / (8 * δ * Real.sqrt δ)) * ENNReal.ofReal 2 := by
    rw [restrict_branchPos hδ,
      lintegral_map (measurable_splitWeight δ) (continuous_hypRot hδ).measurable,
      lintegral_smul_measure]
    simp_rw [splitWeight_hypRot hδ, smul_eq_mul]
    congr 1
    have h1 := lintegral_tent (a := 1) one_pos
    simp only [one_mul, div_one] at h1
    simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1]
    simp
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  rw [hneg, hpos, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

end Real

/-! ### The complex place -/

section ComplexPlace

variable {D s : ℂ}

/-- **The coordinate** $t(x) = x_{00} + s\,x_{10}$ of $x\in SO(\langle1,D\rangle)(\mathbb C)$, $s^2 = -D$ (0-based
entries: the two entries of the first column). -/
def complexCoord (D s : ℂ) (x : ArchSOC (QuadForm.diag ![1, D])) : ℂ :=
  ArchSOC.mat _ x 0 0 + s * ArchSOC.mat _ x 1 0

theorem continuous_complexCoord (D s : ℂ) : Continuous (complexCoord D s) := by
  have h := ArchSOC.continuous_mat (QuadForm.diag ![1, D])
  exact (h.matrix_elem 0 0).add (continuous_const.mul (h.matrix_elem 1 0))

/-- Every element of $SO(\langle1,D\rangle)(\mathbb C)$ is the rotation with its own first column. -/
theorem exists_rotSecC_eq (hD : D ≠ 0) (x : ArchSOC (QuadForm.diag ![1, D])) :
    ∃ u, rotSecC D u = x := by
  have hg : (ArchSOC.mat _ x)ᵀ * BinaryNormOne.hessD D * ArchSOC.mat _ x = BinaryNormOne.hessD D := by
    have h := ArchSOC.isometry (QuadForm.diag ![1, D]) x
    rw [gramC_diag_one_D, Matrix.mul_smul, Matrix.smul_mul] at h
    exact smul_right_injective _ (by norm_num : (1 / 2 : ℂ) ≠ 0) h
  obtain ⟨h1, h2, -⟩ := BinaryNormOne.orth_eq_rotMat (K := ℂ) two_ne_zero hD hg
  rw [ArchSOC.det_mat] at h1
  have hu : (QuadForm.diag ![1, D]).eval ![ArchSOC.mat _ x 0 0, ArchSOC.mat _ x 1 0] = 1 := by
    rw [eval_diag_one_D_C]; simpa using h2
  refine ⟨⟨![ArchSOC.mat _ x 0 0, ArchSOC.mat _ x 1 0], hu⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  change ArchSOC.mat _ (rotSecC D _) = ArchSOC.mat _ x
  rw [mat_rotSecC]
  exact h1.symm

theorem entries_rotSecC (u : SphC (QuadForm.diag ![1, D]) 1) :
    ArchSOC.mat _ (rotSecC D u) 0 0 = (u : Fin 2 → ℂ) 0 ∧
      ArchSOC.mat _ (rotSecC D u) 1 0 = (u : Fin 2 → ℂ) 1 := by
  rw [mat_rotSecC]
  simp [BinaryNormOne.rotMat]

/-- The map $\tau\mapsto\rho(\gamma(\tau))$, $\gamma(\tau) = (\cosh\tau, s^{-1}\sinh\tau)$. -/
def complexRot (hD : D ≠ 0) (hs : s ^ 2 = -D) (τ : ℂ) : ArchSOC (QuadForm.diag ![1, D]) :=
  rotSecC D (arcC hD hs τ)

theorem continuous_complexRot (hD : D ≠ 0) (hs : s ^ 2 = -D) : Continuous (complexRot hD hs) :=
  continuous_rotSecC.comp (continuous_arcC hD hs)

theorem complexCoord_complexRot (hD : D ≠ 0) (hs : s ^ 2 = -D) (τ : ℂ) :
    complexCoord D s (complexRot hD hs τ) = Complex.exp τ := by
  have hs0 := ne_zero_of_sq_eq_neg hD hs
  obtain ⟨h0, h1⟩ := entries_rotSecC (arcC hD hs τ)
  unfold complexCoord complexRot
  rw [h0, h1]
  simp only [arcC, arcVecC, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul, Complex.cosh_add_sinh]

/-- **The fundamental strip** $\{\tau : -\pi<\operatorname{Im}\tau\le\pi\}$ of the exponential. -/
def complexStrip : Set ℂ := Complex.im ⁻¹' Ioc (-Real.pi) Real.pi

theorem measurableSet_complexStrip : MeasurableSet complexStrip :=
  Complex.measurable_im measurableSet_Ioc

/-- **$\gamma$ is injective on the strip**: $\cosh\tau$ and $\sinh\tau$ determine $e^\tau$. -/
theorem arcC_injOn_strip (hD : D ≠ 0) (hs : s ^ 2 = -D) : InjOn (arcC hD hs) complexStrip := by
  have hs0 := ne_zero_of_sq_eq_neg hD hs
  intro τ hτ τ' hτ' h
  have h0 := congrArg (fun u : SphC (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℂ) 0) h
  have h1 := congrArg (fun u : SphC (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℂ) 1) h
  simp only [arcC, arcVecC, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hsn : Complex.sinh τ = Complex.sinh τ' := mul_left_cancel₀ (inv_ne_zero hs0) h1
  have he : Complex.exp τ = Complex.exp τ' := by
    rw [← Complex.cosh_add_sinh, ← Complex.cosh_add_sinh τ', h0, hsn]
  have := congrArg Complex.log he
  rwa [Complex.log_exp hτ.1 hτ.2, Complex.log_exp hτ'.1 hτ'.2] at this

/-- Every element of $SO(\langle1,D\rangle)(\mathbb C)$ is $\rho(\gamma(\tau))$ for some $\tau$ in the strip. -/
theorem exists_complexRot_eq (hD : D ≠ 0) (hs : s ^ 2 = -D) (x : ArchSOC (QuadForm.diag ![1, D])) :
    ∃ τ ∈ complexStrip, complexRot hD hs τ = x := by
  have hs0 := ne_zero_of_sq_eq_neg hD hs
  obtain ⟨u, rfl⟩ := exists_rotSecC_eq hD x
  have hu := norm_one_of_sphC u
  set a := (u : Fin 2 → ℂ) 0 with ha
  set b := (u : Fin 2 → ℂ) 1 with hb
  have hD' : D = -s ^ 2 := by linear_combination hs
  have hmul : (a + s * b) * (a - s * b) = 1 := by
    rw [hD'] at hu; linear_combination hu
  have hz : a + s * b ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hinv : (a + s * b)⁻¹ = a - s * b := inv_eq_of_mul_eq_one_right hmul
  have hexp : Complex.exp (Complex.log (a + s * b)) = a + s * b := Complex.exp_log hz
  refine ⟨Complex.log (a + s * b), ⟨Complex.neg_pi_lt_log_im _, Complex.log_im_le_pi _⟩, ?_⟩
  have hexp' : Complex.exp (-Complex.log (a + s * b)) = a - s * b := by
    rw [Complex.exp_neg, hexp, hinv]
  have e1 := Complex.cosh_add_sinh (Complex.log (a + s * b))
  have e2 := Complex.cosh_sub_sinh (Complex.log (a + s * b))
  rw [hexp] at e1
  rw [hexp'] at e2
  have hc : Complex.cosh (Complex.log (a + s * b)) = a := by linear_combination (e1 + e2) / 2
  have hsn' : Complex.sinh (Complex.log (a + s * b)) = s * b := by linear_combination (e1 - e2) / 2
  have hsn : s⁻¹ * Complex.sinh (Complex.log (a + s * b)) = b := by
    rw [hsn', ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  have : arcC hD hs (Complex.log (a + s * b)) = u := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simpa [arcC, arcVecC] using hc
    · simpa [arcC, arcVecC] using hsn
  unfold complexRot
  rw [this]

/-- The weight function of the complex place, $2\pi\max(0,\ 1-2|\log\|t(x)\||)$. -/
def complexWeight (D s : ℂ) (x : ArchSOC (QuadForm.diag ![1, D])) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |Real.log ‖complexCoord D s x‖|))

theorem measurable_complexWeight (D s : ℂ) : Measurable (complexWeight D s) := by
  have h : Measurable fun r : ℂ => ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |Real.log ‖r‖|)) := by
    fun_prop
  exact h.comp (continuous_complexCoord D s).measurable

theorem complexWeight_complexRot (hD : D ≠ 0) (hs : s ^ 2 = -D) (τ : ℂ) :
    complexWeight D s (complexRot hD hs τ) = ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |τ.re|)) := by
  unfold complexWeight
  rw [complexCoord_complexRot, Complex.norm_exp, Real.log_exp]

/-- **The Leray measure of $SO(\langle1,D\rangle)(\mathbb C)$ is the image of $\frac{1}{64|D|^3}\,d\tau$ on the
fundamental strip** under $\tau\mapsto\rho(\gamma(\tau))$. -/
theorem lerayMeasureC_eq_map_strip (hD : D ≠ 0) (hs : s ^ 2 = -D) :
    lerayMeasureC (QuadForm.diag ![1, D]) (gramDetC_diag_one_D_ne_zero hD) =
      ((ENNReal.ofReal (1 / (64 * ‖D‖ ^ 3))) • (volume : Measure ℂ).restrict complexStrip).map
        (complexRot hD hs) := by
  ext A hA
  have hF : Measurable (complexRot hD hs) := (continuous_complexRot hD hs).measurable
  rw [Measure.map_apply hF hA, Measure.smul_apply, Measure.restrict_apply (hF hA), smul_eq_mul]
  have hA' : A = rotSecC D '' (arcC hD hs '' (complexRot hD hs ⁻¹' A ∩ complexStrip)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨τ, hτ, rfl⟩ := exists_complexRot_eq hD hs y
      exact ⟨arcC hD hs τ, ⟨τ, ⟨hy, hτ⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨τ, ⟨hτA, -⟩, rfl⟩, rfl⟩
      exact hτA
  conv_lhs => rw [hA']
  exact lerayMeasureC_rotSecC_arcC hD hs ((hF hA).inter measurableSet_complexStrip)
    ((arcC_injOn_strip hD hs).mono inter_subset_right)

/-- **Integration over the strip of a function of the real part**:
$\int_{\text{strip}}f(\operatorname{Re}\tau)\,d\tau = 2\pi\int_{\mathbb R}f$. -/
theorem lintegral_strip (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z in complexStrip, f z.re = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r, f r := by
  have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => f p.1)
    (univ ×ˢ Ioc (-Real.pi) Real.pi)
  have hS : Complex.measurableEquivRealProd ⁻¹' (univ ×ˢ Ioc (-Real.pi) Real.pi) = complexStrip := by
    ext z; simp [complexStrip]
  rw [hS] at h
  simp only [Complex.measurableEquivRealProd_apply] at h
  rw [h, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
    Measure.restrict_univ]
  rw [lintegral_mul_const _ hf, mul_comm]
  congr 2
  ring

/-- **The integral of the complex weight against the Leray measure of $SO(\langle1,D\rangle)(\mathbb C)$.**

$$\int 2\pi\max(0,\ 1-2|\log\|t(x)\||)\,d\mu(x) = \frac{\pi^2}{32|D|^3},$$
the archimedean local factor at a complex place of the measure comparison for the binary non-compact case. -/
@[kb "weil1982" "§2.2 (gauge forms at the archimedean places) [unverified]"]
theorem lintegral_complexWeight (hD : D ≠ 0) (hs : s ^ 2 = -D) :
    ∫⁻ x, ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |Real.log ‖complexCoord D s x‖|))
        ∂(lerayMeasureC (QuadForm.diag ![1, D]) (gramDetC_diag_one_D_ne_zero hD)) =
      ENNReal.ofReal (Real.pi ^ 2 / (32 * ‖D‖ ^ 3)) := by
  have hD0 : 0 < ‖D‖ := norm_pos_iff.mpr hD
  change ∫⁻ x, complexWeight D s x ∂_ = _
  rw [lerayMeasureC_eq_map_strip hD hs,
    lintegral_map (measurable_complexWeight D s) (continuous_complexRot hD hs).measurable,
    lintegral_smul_measure]
  simp_rw [complexWeight_complexRot hD hs, smul_eq_mul]
  rw [lintegral_strip (fun r => ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |r|))) (by fun_prop)]
  have h2 := lintegral_tent (a := 2) two_pos
  simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h2, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

end ComplexPlace

end QuadFormsKB.Tamagawa.Measure.Weil
