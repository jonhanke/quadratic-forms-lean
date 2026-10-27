import QuadFormsKB.Tamagawa.Measure.Weil.NSArchDensityC
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchGroup

/-!
# The Cayley chart of the complex norm-one quaternions and its cone density

**Layer:** one complex place, $D = \mathbb H[\mathbb C,A,B]$ ($A, B\ne0$), $N = \langle1,-A,-B,AB\rangle$ (`normForm A B`), $S_1 = \{N = 1\}$
(`SphereLerayC.SphC`). Complex analogue of `NSArchCayleyR.lean`.

* **`cayC A B z`** $= \operatorname{nrd}(1+z)^{-1/2}(1+z)$ for a pure quaternion $z\in\mathbb C^3$ near $0$ (principal branch of the
  complex power; $\operatorname{nrd}(1+z)$ lies in the right half plane): a point of $S_1$ (`eval_cayC`).
* **`cayBallC A B δ`** $= \{x\in S_1 : \operatorname{Re}x_0>0,\ \|x_{1..3}/x_0\| < \delta\}$, the image of the polydisc $B^{\mathbb C^3}_\delta$
  under `cayC` (`mem_cayBallC_iff`); it is open.
* **`coneMapC A B`** $y\mapsto(1+y_0)\,\mathrm{cay}(y_1,y_2,y_3)$ maps $B^{\mathbb C^4}_\delta$ onto
  $\mathrm{pol}(R_\delta\times\mathrm{cayBall}_\delta)$ (`coneMapC_image`) and has real strict derivative the identity at $0$
  (`hasStrictFDerivAt_coneMapC`).
* **`tendsto_nuC_cayBallC`**: $\nu_{\mathbb C}(\mathrm{cayBall}_\delta)/\mathrm{vol}(B^{\mathbb C^3}_\delta)\to1$.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLerayC

variable (A B : ℂ)

/-- The radius below which $\|\operatorname{nrd}(1+z)-1\|<1$. -/
def radC : ℝ := min 1 (1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)))

theorem radC_pos : 0 < radC A B := lt_min one_pos (by positivity)

theorem radC_le_one : radC A B ≤ 1 := min_le_left _ _

variable {A B}

theorem norm_qPure_lt_one {z : Fin 3 → ℂ} (hz : ‖z‖ < radC A B) : ‖qPure A B z‖ < 1 / 2 := by
  have hc : 0 < 1 + ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
  have hz1 : ‖z‖ < 1 := hz.trans_le (radC_le_one A B)
  have hz2 : ‖z‖ < 1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) := hz.trans_le (min_le_right _ _)
  have hle := norm_qPure_le A B z
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  have h1 : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ ^ 2 < 1 / 2 := by
    have : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ ≤ (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
    have h3 : (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ < 1 / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ * 2 = ‖z‖ * (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) := by ring
        _ < 1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) * (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) :=
            mul_lt_mul_of_pos_right hz2 (by positivity)
        _ = 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ ‖A‖ + ‖B‖ + ‖A * B‖)]
  linarith

theorem one_add_qPure_re_pos {z : Fin 3 → ℂ} (hz : ‖z‖ < radC A B) : 0 < (1 + qPure A B z).re := by
  have h := norm_qPure_lt_one hz
  have h2 := Complex.abs_re_le_norm (qPure A B z)
  have h3 := neg_abs_le (qPure A B z).re
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem one_add_qPure_mem_slitPlane {z : Fin 3 → ℂ} (hz : ‖z‖ < radC A B) :
    1 + qPure A B z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (one_add_qPure_re_pos hz))

theorem one_add_qPure_ne_zeroC {z : Fin 3 → ℂ} (hz : ‖z‖ < radC A B) : 1 + qPure A B z ≠ 0 :=
  Complex.slitPlane_ne_zero (one_add_qPure_mem_slitPlane hz)

/-- The principal square root $b^{-1/2}$ has positive real part on the slit plane. -/
theorem re_cpow_neg_half_pos {b : ℂ} (hb : b ∈ Complex.slitPlane) : 0 < (b ^ (-(1 / 2 : ℂ))).re := by
  have hb0 : b ≠ 0 := Complex.slitPlane_ne_zero hb
  rw [Complex.cpow_def_of_ne_zero hb0, Complex.exp_re]
  have h1 := Complex.neg_pi_lt_arg b
  have h2 := lt_of_le_of_ne (Complex.arg_le_pi b) (Complex.mem_slitPlane_iff_arg.1 hb).1
  have him : (Complex.log b * -(1 / 2 : ℂ)).im = -(1 / 2) * b.arg := by
    simp [Complex.log_im]; ring
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> rw [him] <;> nlinarith [Real.pi_pos]

theorem sq_cpow_neg_half {b : ℂ} (hb : b ≠ 0) : (b ^ (-(1 / 2 : ℂ))) ^ 2 = b⁻¹ := by
  rw [← Complex.cpow_nat_mul]
  norm_num
  rw [Complex.cpow_neg_one]

/-- The vector $(1, z)$ of $1 + z$. -/
theorem consC_one (z : Fin 3 → ℂ) : (Fin.cons 1 z : Fin 4 → ℂ) 1 = z 0 := rfl
theorem consC_two (z : Fin 3 → ℂ) : (Fin.cons 1 z : Fin 4 → ℂ) 2 = z 1 := rfl
theorem consC_three (z : Fin 3 → ℂ) : (Fin.cons 1 z : Fin 4 → ℂ) 3 = z 2 := rfl

theorem eval_normForm_consC (z : Fin 3 → ℂ) :
    (normForm A B).eval (Fin.cons 1 z : Fin 4 → ℂ) = 1 + qPure A B z := by
  rw [eval_normForm]
  simp [nrd, vecQ, qPure, consC_one, consC_two, consC_three]; ring

theorem eval_normForm_smulC (r : ℂ) (v : Fin 4 → ℂ) :
    (normForm A B).eval (r • v) = r ^ 2 * (normForm A B).eval v := by
  rw [eval_normForm, eval_normForm]
  simp [nrd, vecQ]; ring

variable (A B) in
/-- **The Cayley point** $\operatorname{nrd}(1+z)^{-1/2}(1+z)$ (principal branch). -/
def cayC (z : Fin 3 → ℂ) : Fin 4 → ℂ := (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) • (Fin.cons 1 z : Fin 4 → ℂ)

theorem eval_cayC {z : Fin 3 → ℂ} (hz : ‖z‖ < radC A B) : (normForm A B).eval (cayC A B z) = 1 := by
  have hp := one_add_qPure_ne_zeroC hz
  rw [cayC, eval_normForm_smulC, eval_normForm_consC, sq_cpow_neg_half hp, inv_mul_cancel₀ hp]

theorem cayC_zero_coord (z : Fin 3 → ℂ) : cayC A B z 0 = (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) := by
  simp [cayC]

theorem cayC_succ_coord (z : Fin 3 → ℂ) (i : Fin 3) :
    cayC A B z i.succ = (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) * z i := by
  simp [cayC]

/-- The tail $(x_1, x_2, x_3)$ of a vector. -/
abbrev tlC (x : Fin 4 → ℂ) : Fin 3 → ℂ := Fin.tail x

variable (A B) in
/-- **The Cayley ball** $\{x\in S_1 : \operatorname{Re}x_0 > 0,\ \|x_{1..3}/x_0\|<\delta\}$. -/
def cayBallC (δ : ℝ) : Set (SphC (normForm A B) 1) :=
  {x | 0 < ((x : Fin 4 → ℂ) 0).re ∧ ‖((x : Fin 4 → ℂ) 0)⁻¹ • tlC (x : Fin 4 → ℂ)‖ < δ}

theorem isOpen_cayBallC (δ : ℝ) : IsOpen (cayBallC A B δ) := by
  have h0 : Continuous fun x : SphC (normForm A B) 1 => (x : Fin 4 → ℂ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have ht : Continuous fun x : SphC (normForm A B) 1 => tlC (x : Fin 4 → ℂ) :=
    continuous_pi fun i => (continuous_apply _).comp continuous_subtype_val
  have hU : IsOpen {x : SphC (normForm A B) 1 | 0 < ((x : Fin 4 → ℂ) 0).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp h0)
  have : ContinuousOn (fun x : SphC (normForm A B) 1 => ‖((x : Fin 4 → ℂ) 0)⁻¹ • tlC (x : Fin 4 → ℂ)‖)
      {x | 0 < ((x : Fin 4 → ℂ) 0).re} :=
    ((h0.continuousOn.inv₀ fun x hx => by
      intro h
      have hx' : 0 < ((x : Fin 4 → ℂ) 0).re := hx
      rw [h] at hx'; simp at hx').smul ht.continuousOn).norm
  have h := this.isOpen_inter_preimage hU (isOpen_Iio (a := δ))
  have e : cayBallC A B δ = {x : SphC (normForm A B) 1 | 0 < ((x : Fin 4 → ℂ) 0).re} ∩
      (fun x : SphC (normForm A B) 1 => ‖((x : Fin 4 → ℂ) 0)⁻¹ • tlC (x : Fin 4 → ℂ)‖) ⁻¹' Iio δ := by
    ext x; simp [cayBallC]
  rw [e]; exact h

theorem measurableSet_cayBallC (δ : ℝ) : MeasurableSet (cayBallC A B δ) := (isOpen_cayBallC δ).measurableSet

/-- **`cayBallC` is the image of the polydisc under `cayC`.** -/
theorem mem_cayBallC_iff {δ : ℝ} (hδ : δ ≤ radC A B) (x : SphC (normForm A B) 1) :
    x ∈ cayBallC A B δ ↔ ∃ z ∈ ball (0 : Fin 3 → ℂ) δ, (x : Fin 4 → ℂ) = cayC A B z := by
  constructor
  · rintro ⟨hx0, hz⟩
    set z := ((x : Fin 4 → ℂ) 0)⁻¹ • tlC (x : Fin 4 → ℂ)
    refine ⟨z, mem_ball_zero_iff.2 hz, ?_⟩
    have hzr : ‖z‖ < radC A B := lt_of_lt_of_le hz hδ
    have hx00 : (x : Fin 4 → ℂ) 0 ≠ 0 := by
      intro h; rw [h] at hx0; simp at hx0
    have hxz : (x : Fin 4 → ℂ) = (x : Fin 4 → ℂ) 0 • (Fin.cons 1 z : Fin 4 → ℂ) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, z, tlC, Fin.tail]
        field_simp
    have hev : (x : Fin 4 → ℂ) 0 ^ 2 * (1 + qPure A B z) = 1 := by
      have := x.2
      change (normForm A B).eval (x : Fin 4 → ℂ) = 1 at this
      rw [hxz, eval_normForm_smulC, eval_normForm_consC] at this
      exact this
    have hp := one_add_qPure_ne_zeroC hzr
    have hsl := one_add_qPure_mem_slitPlane hzr
    have hsq : (x : Fin 4 → ℂ) 0 ^ 2 = ((1 + qPure A B z) ^ (-(1 / 2 : ℂ))) ^ 2 := by
      rw [sq_cpow_neg_half hp]; exact eq_inv_of_mul_eq_one_left hev
    have hx0' : (x : Fin 4 → ℂ) 0 = (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
      · exact h
      · exfalso
        have := re_cpow_neg_half_pos hsl
        rw [h, Complex.neg_re] at hx0
        linarith
    rw [hxz, hx0']; rfl
  · rintro ⟨z, hz, hxz⟩
    have hzr : ‖z‖ < radC A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
    have hp := one_add_qPure_ne_zeroC hzr
    have hr := re_cpow_neg_half_pos (one_add_qPure_mem_slitPlane hzr)
    have h0 : (x : Fin 4 → ℂ) 0 = (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) := by rw [hxz, cayC_zero_coord]
    have hne : (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
      intro h; rw [h] at hr; simp at hr
    refine ⟨by rw [h0]; exact hr, ?_⟩
    have : ((x : Fin 4 → ℂ) 0)⁻¹ • tlC (x : Fin 4 → ℂ) = z := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, tlC, Fin.tail]
      rw [hxz, cayC_succ_coord, cayC_zero_coord]
      field_simp
    rw [this]; exact mem_ball_zero_iff.1 hz

/-! ### The cone map -/

variable (A B) in
/-- **The cone map** $y\mapsto(1+y_0)\,\mathrm{cay}(y_1,y_2,y_3)$. -/
def coneMapC (t : Fin 4 → ℂ) : Fin 4 → ℂ := (1 + t 0) • cayC A B (tlC t)

theorem ball_four_iffC {δ : ℝ} (t : Fin 4 → ℂ) :
    t ∈ ball (0 : Fin 4 → ℂ) δ ↔ t 0 ∈ ball (0 : ℂ) δ ∧ tlC t ∈ ball (0 : Fin 3 → ℂ) δ := by
  rcases le_or_gt δ 0 with hδ | hδ
  · simp only [ball_eq_empty.2 hδ, mem_empty_iff_false, false_iff, not_and]
    intro h; exact h.elim
  simp only [mem_ball_zero_iff, pi_norm_lt_iff hδ, Fin.forall_fin_succ, tlC, Fin.tail]

/-- **The cone map takes $B^{\mathbb C^4}_\delta$ onto $\mathrm{pol}(R_\delta\times\mathrm{cayBall}_\delta)$.** -/
theorem coneMapC_image {δ : ℝ} (hδ : δ ≤ radC A B) :
    coneMapC A B '' ball 0 δ = polC (normForm A B) 1 '' (RdC δ ×ˢ cayBallC A B δ) := by
  have hδ1 : δ ≤ 1 := hδ.trans (radC_le_one A B)
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨h0, hz⟩ := (ball_four_iffC t).1 ht
    have hzr : ‖tlC t‖ < radC A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
    have h0' : ‖t 0‖ < δ := mem_ball_zero_iff.1 h0
    have hne : 1 + t 0 ≠ 0 := by
      intro h
      have : t 0 = -1 := by linear_combination h
      rw [this, norm_neg, norm_one] at h0'
      linarith
    refine ⟨(Units.mk0 (1 + t 0) hne, ⟨cayC A B (tlC t), eval_cayC hzr⟩), ⟨?_, ?_⟩, rfl⟩
    · show ‖(1 + t 0) - 1‖ < δ
      simpa using h0'
    · exact (mem_cayBallC_iff hδ _).2 ⟨tlC t, hz, rfl⟩
  · rintro ⟨⟨s, x⟩, ⟨hs, hx⟩, rfl⟩
    obtain ⟨z, hz, hxz⟩ := (mem_cayBallC_iff hδ x).1 hx
    refine ⟨Fin.cons ((s : ℂ) - 1) z, (ball_four_iffC _).2 ⟨?_, by simpa [tlC] using hz⟩, ?_⟩
    · have : ‖(s : ℂ) - 1‖ < δ := hs
      simpa using this
    · simp only [coneMapC, polC, Fin.cons_zero, hxz, tlC, Fin.tail_cons]
      simp

theorem analyticAt_coneMapC : AnalyticAt ℂ (coneMapC A B) 0 := by
  have hq : AnalyticAt ℂ (fun t : Fin 4 → ℂ => 1 + qPure A B (tlC t)) 0 := by
    have hc : ∀ i, AnalyticAt ℂ (fun t : Fin 4 → ℂ => t i) 0 := fun i => analyticAt_pi_iff.1 analyticAt_id i
    simp only [qPure, tlC, Fin.tail]
    exact analyticAt_const.add ((((analyticAt_const.mul ((hc _).pow 2)).sub (analyticAt_const.mul ((hc _).pow 2))).add
      (analyticAt_const.mul ((hc _).pow 2))))
  have hsl : (fun t : Fin 4 → ℂ => 1 + qPure A B (tlC t)) 0 ∈ Complex.slitPlane := by
    simp [qPure, tlC, Fin.tail]
  have hr : AnalyticAt ℂ (fun t : Fin 4 → ℂ => (1 + qPure A B (tlC t)) ^ (-(1 / 2 : ℂ))) 0 :=
    hq.cpow analyticAt_const hsl
  rw [analyticAt_pi_iff]; intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [coneMapC, cayC, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, mul_one]
    exact (analyticAt_const.add (analyticAt_pi_iff.1 analyticAt_id 0)).mul hr
  · simp only [coneMapC, cayC, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    exact (analyticAt_const.add (analyticAt_pi_iff.1 analyticAt_id 0)).mul
      (hr.mul (analyticAt_pi_iff.1 analyticAt_id i.succ))

theorem contDiffAt_coneMapC : ContDiffAt ℂ ⊤ (coneMapC A B) 0 := analyticAt_coneMapC.contDiffAt

theorem hasDerivAt_coneMapC_line (p : Fin 4 → ℂ) :
    HasDerivAt (fun s : ℂ => coneMapC A B (s • p)) p 0 := by
  rw [hasDerivAt_pi]; intro i
  have hq : HasDerivAt (fun s : ℂ => 1 + qPure A B (tlC (s • p))) 0 0 := by
    have e : (fun s : ℂ => 1 + qPure A B (tlC (s • p))) = fun s => 1 + s ^ 2 * qPure A B (tlC p) := by
      funext s; simp only [qPure, tlC, Fin.tail, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    simpa using ((hasDerivAt_pow 2 (0 : ℂ)).mul_const (qPure A B (tlC p))).const_add 1
  have hr : HasDerivAt (fun s : ℂ => (1 + qPure A B (tlC (s • p))) ^ (-(1 / 2 : ℂ))) 0 0 := by
    have h := hq.cpow_const (c := -(1 / 2 : ℂ)) (by simp [qPure, tlC, Fin.tail])
    simpa using h
  have he : HasDerivAt (fun s : ℂ => 1 + (s • p) 0) (p 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (p 0)).const_add 1
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [coneMapC, cayC, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, mul_one]
    convert he.mul hr using 1
    simp [qPure, tlC, Fin.tail]
  · simp only [coneMapC, cayC, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    have hz : HasDerivAt (fun s : ℂ => tlC (s • p) i) (p i.succ) 0 := by
      simpa [tlC, Fin.tail] using (hasDerivAt_id (0 : ℂ)).mul_const (p i.succ)
    convert he.mul (hr.mul hz) using 1
    simp [qPure, tlC, Fin.tail]

/-- **The complex strict derivative of the cone map at $0$ is the identity.** -/
theorem hasStrictFDerivAt_coneMapC_complex :
    HasStrictFDerivAt (coneMapC A B) (ContinuousLinearMap.id ℂ (Fin 4 → ℂ)) 0 := by
  have h := contDiffAt_coneMapC (A := A) (B := B) |>.hasStrictFDerivAt (by simp)
  convert h using 1
  refine ContinuousLinearMap.ext fun p => ?_
  have hd : HasFDerivAt (coneMapC A B) (fderiv ℂ (coneMapC A B) 0) ((0 : ℂ) • p) := by
    rw [zero_smul]
    exact (contDiffAt_coneMapC.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun r : ℂ => r • p) p 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const p
  have h1 : HasDerivAt (fun r : ℂ => coneMapC A B (r • p)) (fderiv ℂ (coneMapC A B) 0 p) 0 := by
    simpa [Function.comp_def] using hd.comp_hasDerivAt (0 : ℂ) hline
  exact ((hasDerivAt_coneMapC_line p).unique h1)

/-- **The real strict derivative of the cone map at $0$ is the identity.** -/
theorem hasStrictFDerivAt_coneMapC :
    HasStrictFDerivAt (coneMapC A B) (ContinuousLinearMap.id ℝ (Fin 4 → ℂ)) 0 :=
  hasStrictFDerivAt_coneMapC_complex.restrictScalars ℝ

/-- **The cone density of the Cayley balls**: $\nu_{\mathbb C}(\mathrm{cayBall}_\delta)/\mathrm{vol}(B^{\mathbb C^3}_\delta)\to1$. -/
theorem tendsto_nuC_cayBallC :
    Tendsto (fun δ => (nuC (normForm A B) 1 (cayBallC A B δ)).toReal /
      (volume (ball (0 : Fin 3 → ℂ) δ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_nuC_div (fun δ => measurableSet_cayBallC δ) hasStrictFDerivAt_coneMapC
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventually_of_mem (Iic_mem_nhds (radC_pos A B)) fun δ hδ => coneMapC_image hδ))
  have hdet : |(ContinuousLinearMap.id ℝ (Fin 4 → ℂ)).det| = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one]
  rwa [hdet] at h

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
