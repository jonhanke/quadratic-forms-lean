import QuadFormsKB.Tamagawa.Measure.Weil.NSArchDensity
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchGroup

/-!
# The Cayley chart of the real norm-one quaternions and its cone density

**Layer:** one real place, $D = \mathbb H[\mathbb R,A,B]$ ($A, B\ne0$, any signs), $N = \langle1,-A,-B,AB\rangle$ (`normForm A B`), $S_1 = \{N = 1\}$.

* **`cay A B z`** $= \operatorname{nrd}(1+z)^{-1/2}(1+z)$ for a pure quaternion $z\in\mathbb R^3$ near $0$: a point of $S_1$ (`eval_cay`).
* **`cayBall A B δ`** $= \{x\in S_1 : x_0>0,\ \|x_{1..3}/x_0\| < \delta\}$, the image of the ball $B^3_\delta$ under `cay`
  (`mem_cayBall_iff`); it is open.
* **`coneMap A B`** $t\mapsto e^{t_0}\,\mathrm{cay}(t_1,t_2,t_3)$ maps $B^4_\delta$ onto $\mathrm{pol}((-\delta,\delta)\times\mathrm{cayBall}_\delta)$
  (`coneMap_image`) and has strict derivative the identity at $0$ (`hasStrictFDerivAt_coneMap`).
* **`tendsto_nu_cayBall`**: $\nu(\mathrm{cayBall}_\delta)/\mathrm{vol}(B^3_\delta)\to1$, so $\sigma(\mathrm{cayBall}_\delta)/\mathrm{vol}(B^3_\delta)\to\tfrac12$.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLeray

variable (A B : ℝ)

/-- The radius below which $\operatorname{nrd}(1+z) > 0$. -/
def radR : ℝ := min 1 (1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)))

theorem radR_pos : 0 < radR A B := lt_min one_pos (by positivity)

theorem radR_le_one : radR A B ≤ 1 := min_le_left _ _

variable {A B}

theorem one_add_qPure_pos {z : Fin 3 → ℝ} (hz : ‖z‖ < radR A B) : 0 < 1 + qPure A B z := by
  have hc : 0 < 1 + ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
  have hz1 : ‖z‖ < 1 := hz.trans_le (radR_le_one A B)
  have hz2 : ‖z‖ < 1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) := hz.trans_le (min_le_right _ _)
  have hle := norm_qPure_le A B z
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  have h1 : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ ^ 2 < 1 := by
    have : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ ≤ (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
    have h3 : (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ < 1 / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ * 2 = ‖z‖ * (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) := by ring
        _ < 1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) * (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) :=
            mul_lt_mul_of_pos_right hz2 (by positivity)
        _ = 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ ‖A‖ + ‖B‖ + ‖A * B‖)]
  have := (Real.norm_eq_abs _ ▸ hle : |qPure A B z| ≤ _)
  linarith [neg_abs_le (qPure A B z)]

/-- The vector $(1, z)$ of $1 + z$. -/
theorem cons_one (z : Fin 3 → ℝ) : (Fin.cons 1 z : Fin 4 → ℝ) 1 = z 0 := rfl
theorem cons_two (z : Fin 3 → ℝ) : (Fin.cons 1 z : Fin 4 → ℝ) 2 = z 1 := rfl
theorem cons_three (z : Fin 3 → ℝ) : (Fin.cons 1 z : Fin 4 → ℝ) 3 = z 2 := rfl

theorem qVec_one_add_pure (z : Fin 3 → ℝ) :
    qVec (1 + Quat.pure z : ℍ[ℝ,A,B]) = Fin.cons 1 z := by
  funext i; fin_cases i <;> simp [qVec, Quat.pure, cons_one, cons_two, cons_three]

variable (A B) in
/-- **The Cayley point** $\operatorname{nrd}(1+z)^{-1/2}(1+z)$. -/
def cay (z : Fin 3 → ℝ) : Fin 4 → ℝ := (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) • (Fin.cons 1 z : Fin 4 → ℝ)

theorem eval_normForm_cons (z : Fin 3 → ℝ) :
    (normForm A B).eval (Fin.cons 1 z : Fin 4 → ℝ) = 1 + qPure A B z := by
  rw [eval_normForm, nrd_vecQ_cons]
where
  nrd_vecQ_cons : nrd (vecQ (Fin.cons 1 z : Fin 4 → ℝ) : ℍ[ℝ,A,B]) = 1 + qPure A B z := by
    simp [nrd, vecQ, qPure, cons_one, cons_two, cons_three]; ring

theorem eval_normForm_smul (r : ℝ) (v : Fin 4 → ℝ) : (normForm A B).eval (r • v) = r ^ 2 * (normForm A B).eval v := by
  rw [eval_normForm, eval_normForm]
  simp [nrd, vecQ]; ring

theorem eval_cay {z : Fin 3 → ℝ} (hz : ‖z‖ < radR A B) : (normForm A B).eval (cay A B z) = 1 := by
  have hp := one_add_qPure_pos hz
  rw [cay, eval_normForm_smul, eval_normForm_cons, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  norm_num
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hp.ne']

theorem cay_zero_coord (z : Fin 3 → ℝ) : cay A B z 0 = (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) := by
  simp [cay]

theorem cay_succ_coord (z : Fin 3 → ℝ) (i : Fin 3) :
    cay A B z i.succ = (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) * z i := by
  simp [cay]

/-- The tail $(x_1, x_2, x_3)$ of a vector. -/
abbrev tl (x : Fin 4 → ℝ) : Fin 3 → ℝ := Fin.tail x

variable (A B) in
/-- **The Cayley ball** $\{x\in S_1 : x_0 > 0,\ \|x_{1..3}/x_0\|<\delta\}$. -/
def cayBall (δ : ℝ) : Set (Sph (normForm A B) 1) :=
  {x | 0 < (x : Fin 4 → ℝ) 0 ∧ ‖((x : Fin 4 → ℝ) 0)⁻¹ • tl (x : Fin 4 → ℝ)‖ < δ}

theorem isOpen_cayBall (δ : ℝ) : IsOpen (cayBall A B δ) := by
  have h0 : Continuous fun x : Sph (normForm A B) 1 => (x : Fin 4 → ℝ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have ht : Continuous fun x : Sph (normForm A B) 1 => tl (x : Fin 4 → ℝ) :=
    continuous_pi fun i => (continuous_apply _).comp continuous_subtype_val
  have hU : IsOpen {x : Sph (normForm A B) 1 | 0 < (x : Fin 4 → ℝ) 0} := isOpen_lt continuous_const h0
  have : ContinuousOn (fun x : Sph (normForm A B) 1 => ‖((x : Fin 4 → ℝ) 0)⁻¹ • tl (x : Fin 4 → ℝ)‖)
      {x | 0 < (x : Fin 4 → ℝ) 0} :=
    ((h0.continuousOn.inv₀ fun x hx => (ne_of_gt hx)).smul ht.continuousOn).norm
  have h := this.isOpen_inter_preimage hU (isOpen_Iio (a := δ))
  have e : cayBall A B δ = {x : Sph (normForm A B) 1 | 0 < (x : Fin 4 → ℝ) 0} ∩
      (fun x : Sph (normForm A B) 1 => ‖((x : Fin 4 → ℝ) 0)⁻¹ • tl (x : Fin 4 → ℝ)‖) ⁻¹' Iio δ := by
    ext x; simp [cayBall]
  rw [e]; exact h

theorem measurableSet_cayBall (δ : ℝ) : MeasurableSet (cayBall A B δ) := (isOpen_cayBall δ).measurableSet

/-- **`cayBall` is the image of the ball under `cay`.** -/
theorem mem_cayBall_iff {δ : ℝ} (hδ : δ ≤ radR A B) (x : Sph (normForm A B) 1) :
    x ∈ cayBall A B δ ↔ ∃ z ∈ ball (0 : Fin 3 → ℝ) δ, (x : Fin 4 → ℝ) = cay A B z := by
  constructor
  · rintro ⟨hx0, hz⟩
    set z := ((x : Fin 4 → ℝ) 0)⁻¹ • tl (x : Fin 4 → ℝ)
    refine ⟨z, mem_ball_zero_iff.2 hz, ?_⟩
    have hzr : ‖z‖ < radR A B := lt_of_lt_of_le hz hδ
    have hxz : (x : Fin 4 → ℝ) = (x : Fin 4 → ℝ) 0 • (Fin.cons 1 z : Fin 4 → ℝ) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, z, tl, Fin.tail]
        field_simp
    have hev : (x : Fin 4 → ℝ) 0 ^ 2 * (1 + qPure A B z) = 1 := by
      have := x.2
      change (normForm A B).eval (x : Fin 4 → ℝ) = 1 at this
      rw [hxz, eval_normForm_smul, eval_normForm_cons] at this
      exact this
    have hp := one_add_qPure_pos hzr
    have hx0' : (x : Fin 4 → ℝ) 0 = (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) := by
      have hsq : ((1 + qPure A B z) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 + qPure A B z)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num; rw [Real.rpow_neg_one]
      have h1 : (x : Fin 4 → ℝ) 0 ^ 2 = ((1 + qPure A B z) ^ (-(1 / 2 : ℝ))) ^ 2 := by
        rw [hsq]; exact eq_inv_of_mul_eq_one_left hev
      exact (sq_eq_sq₀ hx0.le (Real.rpow_nonneg hp.le _)).1 h1
    rw [hxz, hx0']; rfl
  · rintro ⟨z, hz, hxz⟩
    have hzr : ‖z‖ < radR A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
    have hp := one_add_qPure_pos hzr
    have hr : 0 < (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hp _
    have h0 : (x : Fin 4 → ℝ) 0 = (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) := by rw [hxz, cay_zero_coord]
    refine ⟨by rw [h0]; exact hr, ?_⟩
    have : ((x : Fin 4 → ℝ) 0)⁻¹ • tl (x : Fin 4 → ℝ) = z := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, tl, Fin.tail]
      rw [hxz, cay_succ_coord, cay_zero_coord]
      field_simp
    rw [this]; exact mem_ball_zero_iff.1 hz

/-! ### The cone map -/

variable (A B) in
/-- **The cone map** $t\mapsto e^{t_0}\,\mathrm{cay}(t_1,t_2,t_3)$. -/
def coneMap (t : Fin 4 → ℝ) : Fin 4 → ℝ := Real.exp (t 0) • cay A B (tl t)

theorem ball_four_iff {δ : ℝ} (t : Fin 4 → ℝ) :
    t ∈ ball (0 : Fin 4 → ℝ) δ ↔ t 0 ∈ Ioo (-δ) δ ∧ tl t ∈ ball (0 : Fin 3 → ℝ) δ := by
  rcases le_or_gt δ 0 with hδ | hδ
  · simp only [ball_eq_empty.2 hδ, mem_empty_iff_false, false_iff, not_and]
    intro h; exact absurd (h.1.trans h.2) (by linarith)
  simp only [mem_ball_zero_iff, pi_norm_lt_iff hδ, Real.norm_eq_abs, abs_lt, Fin.forall_fin_succ, tl,
    Fin.tail, mem_Ioo]

/-- **The cone map takes $B^4_\delta$ onto $\mathrm{pol}((-\delta,\delta)\times\mathrm{cayBall}_\delta)$.** -/
theorem coneMap_image {δ : ℝ} (hδ : δ ≤ radR A B) :
    coneMap A B '' ball 0 δ = pol (normForm A B) 1 '' (Ioo (-δ) δ ×ˢ cayBall A B δ) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨h0, hz⟩ := (ball_four_iff t).1 ht
    have hzr : ‖tl t‖ < radR A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
    refine ⟨(t 0, ⟨cay A B (tl t), eval_cay hzr⟩), ⟨h0, ?_⟩, rfl⟩
    exact (mem_cayBall_iff hδ _).2 ⟨tl t, hz, rfl⟩
  · rintro ⟨⟨s, x⟩, ⟨hs, hx⟩, rfl⟩
    obtain ⟨z, hz, hxz⟩ := (mem_cayBall_iff hδ x).1 hx
    refine ⟨Fin.cons s z, (ball_four_iff _).2 ⟨by simpa using hs, by simpa [tl] using hz⟩, ?_⟩
    simp only [coneMap, pol, Fin.cons_zero, hxz, tl, Fin.tail_cons]

theorem contDiffAt_coneMap : ContDiffAt ℝ ⊤ (coneMap A B) 0 := by
  have hq : ContDiffAt ℝ ⊤ (fun t : Fin 4 → ℝ => 1 + qPure A B (tl t)) 0 := by
    simp only [qPure, tl, Fin.tail]; fun_prop
  have hpos : (fun t : Fin 4 → ℝ => 1 + qPure A B (tl t)) 0 ≠ 0 := by simp [qPure, tl, Fin.tail]
  have hr : ContDiffAt ℝ ⊤ (fun t : Fin 4 → ℝ => (1 + qPure A B (tl t)) ^ (-(1 / 2 : ℝ))) 0 :=
    hq.rpow_const_of_ne hpos
  rw [contDiffAt_pi]; intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [coneMap, cay, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, mul_one]
    exact (Real.contDiff_exp.contDiffAt.comp _ (contDiffAt_apply ℝ (fun _ => ℝ) 0 (0 : Fin 4 → ℝ))).mul hr
  · simp only [coneMap, cay, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    exact (Real.contDiff_exp.contDiffAt.comp _ (contDiffAt_apply ℝ (fun _ => ℝ) 0 (0 : Fin 4 → ℝ))).mul
      (hr.mul (contDiffAt_apply ℝ (fun _ => ℝ) i.succ (0 : Fin 4 → ℝ)))

theorem hasDerivAt_coneMap_line (p : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => coneMap A B (s • p)) p 0 := by
  rw [hasDerivAt_pi]; intro i
  have hq : HasDerivAt (fun s : ℝ => 1 + qPure A B (tl (s • p))) 0 0 := by
    have e : (fun s : ℝ => 1 + qPure A B (tl (s • p))) = fun s => 1 + s ^ 2 * qPure A B (tl p) := by
      funext s; simp only [qPure, tl, Fin.tail, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (qPure A B (tl p))).const_add 1
  have hr : HasDerivAt (fun s : ℝ => (1 + qPure A B (tl (s • p))) ^ (-(1 / 2 : ℝ))) 0 0 := by
    have h := hq.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (by simp [qPure, tl, Fin.tail]))
    simpa using h
  have he : HasDerivAt (fun s : ℝ => Real.exp ((s • p) 0)) (p 0) 0 := by
    have := (Real.hasDerivAt_exp (0 * p 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).mul_const (p 0))
    simpa [Function.comp_def] using this
  have hval : (1 + qPure A B (tl ((0 : ℝ) • p))) ^ (-(1 / 2 : ℝ)) = 1 := by simp [qPure, tl, Fin.tail]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [coneMap, cay, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, mul_one]
    convert he.mul hr using 1
    simp [qPure, tl, Fin.tail]
  · simp only [coneMap, cay, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    have hz : HasDerivAt (fun s : ℝ => tl (s • p) i) (p i.succ) 0 := by
      simpa [tl, Fin.tail] using (hasDerivAt_id (0 : ℝ)).mul_const (p i.succ)
    convert he.mul (hr.mul hz) using 1
    simp [qPure, tl, Fin.tail]

/-- **The strict derivative of the cone map at $0$ is the identity.** -/
theorem hasStrictFDerivAt_coneMap :
    HasStrictFDerivAt (coneMap A B) (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) 0 := by
  have h := contDiffAt_coneMap (A := A) (B := B) |>.hasStrictFDerivAt (by simp)
  convert h using 1
  refine ContinuousLinearMap.ext fun p => ?_
  have hd : HasFDerivAt (coneMap A B) (fderiv ℝ (coneMap A B) 0) ((0 : ℝ) • p) := by
    rw [zero_smul]
    exact (contDiffAt_coneMap.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => r • p) p 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun r : ℝ => coneMap A B (r • p)) (fderiv ℝ (coneMap A B) 0 p) 0 := by
    simpa [Function.comp_def] using hd.comp_hasDerivAt (0 : ℝ) hline
  exact ((hasDerivAt_coneMap_line p).unique h1)

/-- **The cone density of the Cayley balls**: $\nu(\mathrm{cayBall}_\delta)/\mathrm{vol}(B^3_\delta)\to1$. -/
theorem tendsto_nu_cayBall :
    Tendsto (fun δ => (nu (normForm A B) 1 (cayBall A B δ)).toReal / (volume (ball (0 : Fin 3 → ℝ) δ)).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_nu_div (fun δ => measurableSet_cayBall δ) hasStrictFDerivAt_coneMap
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventually_of_mem (Iic_mem_nhds (radR_pos A B)) fun δ hδ => coneMap_image hδ))
  have hdet : |(ContinuousLinearMap.id ℝ (Fin 4 → ℝ)).det| = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one]
  rwa [hdet] at h

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
