import QuadFormsKB.Tamagawa.Measure.Weil.NSArchDensity
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSplitR
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchCayleyR

/-!
# The graph chart of the real sphere $Q_0 = 1$ and its cone density

**Layer:** one real place, $Q_0 = $ `nsFormR A B d` $= v_0^2 + P(v_1,v_2,v_3)$ with
$P(u) = -Ad\,u_0^2 - Bd\,u_1^2 + ABd\,u_2^2$ (`qPD A B d u`; indices 0-based), $S = \{Q_0 = 1\}$.

* **`gr A B d u`** $= (\sqrt{1-P(u)}, u)$ for $\|u\| < $ `radG`: a point of $S$ (`eval_gr`).
* **`grBall A B d δ`** $= \{x\in S : x_0>0,\ \|x_{1..3}\| < \delta\}$, the image of $B^3_\delta$ under `gr`
  (`mem_grBall_iff`); it is open, and contained in $\|x\|\le 2$ (`grBall_subset`).
* **`grCone`** $t\mapsto e^{t_0}\,\mathrm{gr}(t_1,t_2,t_3)$ maps $B^4_\delta$ onto
  $\mathrm{pol}((-\delta,\delta)\times\mathrm{grBall}_\delta)$ (`grCone_image`), strict derivative the identity at $0$.
* **`tendsto_nu_grBall`**: $\nu(\mathrm{grBall}_\delta)/\mathrm{vol}(B^3_\delta)\to1$.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLeray

variable (A B d : ℝ)

/-- The ternary part $P(u) = -Ad\,u_0^2 - Bd\,u_1^2 + ABd\,u_2^2$ of `nsFormR A B d`. -/
def qPD (u : Fin 3 → ℝ) : ℝ := -A * d * u 0 ^ 2 - B * d * u 1 ^ 2 + A * B * d * u 2 ^ 2

/-- The radius below which $1 - P(u) > 0$. -/
def radG : ℝ := min 1 (1 / (2 * (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖)))

theorem radG_pos : 0 < radG A B d := lt_min one_pos (by positivity)

theorem radG_le_one : radG A B d ≤ 1 := min_le_left _ _

variable {A B d}

theorem abs_term_le (a : ℝ) (u : Fin 3 → ℝ) (i : Fin 3) : |a * u i ^ 2| ≤ ‖a‖ * ‖u‖ ^ 2 := by
  rw [abs_mul, abs_pow, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2) (norm_nonneg _)

theorem abs_qPD_le (u : Fin 3 → ℝ) :
    |qPD A B d u| ≤ (‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ ^ 2 := by
  have h1 := abs_term_le (-A * d) u 0
  have h2 := abs_term_le (-(B * d)) u 1
  have h3 := abs_term_le (A * B * d) u 2
  have e : qPD A B d u = (-A * d) * u 0 ^ 2 + (-(B * d)) * u 1 ^ 2 + (A * B * d) * u 2 ^ 2 := by
    simp only [qPD]; ring
  rw [e]
  have n1 : ‖-A * d‖ = ‖A * d‖ := by rw [neg_mul, norm_neg]
  have n2 : ‖-(B * d)‖ = ‖B * d‖ := norm_neg _
  rw [n1] at h1; rw [n2] at h2
  calc _ ≤ |(-A * d) * u 0 ^ 2| + |(-(B * d)) * u 1 ^ 2| + |(A * B * d) * u 2 ^ 2| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ _ := by nlinarith

theorem one_sub_qPD_pos {u : Fin 3 → ℝ} (hu : ‖u‖ < radG A B d) : 0 < 1 - qPD A B d u := by
  have hc : 0 < 1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖ := by positivity
  have hz1 : ‖u‖ < 1 := hu.trans_le (radG_le_one A B d)
  have hz2 : ‖u‖ < 1 / (2 * (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖)) := hu.trans_le (min_le_right _ _)
  have hle := abs_qPD_le (A := A) (B := B) (d := d) u
  have hsq : ‖u‖ ^ 2 ≤ ‖u‖ := by nlinarith [norm_nonneg u]
  have h1 : (‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ ^ 2 < 1 := by
    have : (‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ ≤ (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg u)
    have h3 : (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ < 1 / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ * 2
          = ‖u‖ * (2 * (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖)) := by ring
        _ < 1 / (2 * (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖)) * (2 * (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖)) :=
            mul_lt_mul_of_pos_right hz2 (by positivity)
        _ = 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖)]
  linarith [le_abs_self (qPD A B d u)]

variable (A B d) in
/-- **The graph point** $(\sqrt{1-P(u)}, u)$. -/
def gr (u : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.cons (Real.sqrt (1 - qPD A B d u)) u

theorem eval_nsFormR_tail (v : Fin 4 → ℝ) :
    (nsFormR A B d).eval v = v 0 ^ 2 + qPD A B d (Fin.tail v) := by
  rw [eval_nsFormR]
  have h1 : Fin.tail v 0 = v 1 := rfl
  have h2 : Fin.tail v 1 = v 2 := rfl
  have h3 : Fin.tail v 2 = v 3 := rfl
  simp only [qPD, h1, h2, h3]; ring

theorem eval_gr {u : Fin 3 → ℝ} (hu : ‖u‖ < radG A B d) : (nsFormR A B d).eval (gr A B d u) = 1 := by
  have hp := one_sub_qPD_pos hu
  rw [eval_nsFormR_tail]
  simp only [gr, Fin.cons_zero, Fin.tail_cons]
  rw [Real.sq_sqrt hp.le]; ring

variable (A B d) in
/-- **The graph ball** $\{x\in S : x_0>0,\ \|x_{1..3}\|<\delta\}$. -/
def grBall (δ : ℝ) : Set (Sph (nsFormR A B d) 1) :=
  {x | 0 < (x : Fin 4 → ℝ) 0 ∧ ‖Fin.tail (x : Fin 4 → ℝ)‖ < δ}

theorem isOpen_grBall (δ : ℝ) : IsOpen (grBall A B d δ) := by
  have h0 : Continuous fun x : Sph (nsFormR A B d) 1 => (x : Fin 4 → ℝ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have ht : Continuous fun x : Sph (nsFormR A B d) 1 => Fin.tail (x : Fin 4 → ℝ) :=
    continuous_pi fun i => (continuous_apply _).comp continuous_subtype_val
  have e : grBall A B d δ = {x : Sph (nsFormR A B d) 1 | 0 < (x : Fin 4 → ℝ) 0} ∩
      (fun x : Sph (nsFormR A B d) 1 => ‖Fin.tail (x : Fin 4 → ℝ)‖) ⁻¹' Iio δ := by
    ext x; simp [grBall]
  rw [e]
  exact (isOpen_lt continuous_const h0).inter (isOpen_Iio.preimage ht.norm)

theorem measurableSet_grBall (δ : ℝ) : MeasurableSet (grBall A B d δ) := (isOpen_grBall δ).measurableSet

/-- **`grBall` is the image of the ball under `gr`.** -/
theorem mem_grBall_iff {δ : ℝ} (hδ : δ ≤ radG A B d) (x : Sph (nsFormR A B d) 1) :
    x ∈ grBall A B d δ ↔ ∃ u ∈ ball (0 : Fin 3 → ℝ) δ, (x : Fin 4 → ℝ) = gr A B d u := by
  constructor
  · rintro ⟨hx0, hz⟩
    refine ⟨Fin.tail (x : Fin 4 → ℝ), mem_ball_zero_iff.2 hz, ?_⟩
    have hev : (x : Fin 4 → ℝ) 0 ^ 2 + qPD A B d (Fin.tail (x : Fin 4 → ℝ)) = 1 := by
      have := x.2
      change (nsFormR A B d).eval (x : Fin 4 → ℝ) = 1 at this
      rwa [eval_nsFormR_tail] at this
    have h0 : (x : Fin 4 → ℝ) 0 = Real.sqrt (1 - qPD A B d (Fin.tail (x : Fin 4 → ℝ))) := by
      rw [← Real.sqrt_sq hx0.le]; congr 1; linarith
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [gr] using h0
    · simp [gr, Fin.tail]
  · rintro ⟨u, hu, hxu⟩
    have hur : ‖u‖ < radG A B d := lt_of_lt_of_le (mem_ball_zero_iff.1 hu) hδ
    have hp := one_sub_qPD_pos hur
    refine ⟨?_, ?_⟩
    · rw [hxu]; simpa [gr] using Real.sqrt_pos.2 hp
    · rw [hxu]; simpa [gr] using mem_ball_zero_iff.1 hu

theorem grBall_subset {δ : ℝ} (hδ : δ ≤ radG A B d) :
    grBall A B d δ ⊆ {x | ‖(x : Fin 4 → ℝ)‖ ≤ 2} := by
  intro x hx
  obtain ⟨u, hu, hxu⟩ := (mem_grBall_iff hδ x).1 hx
  have hur : ‖u‖ < radG A B d := lt_of_lt_of_le (mem_ball_zero_iff.1 hu) hδ
  have hu1 : ‖u‖ < 1 := hur.trans_le (radG_le_one A B d)
  have hc : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hcl : 0 ≤ ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖ := by positivity
  have hq := abs_qPD_le (A := A) (B := B) (d := d) u
  have hz2 : ‖u‖ < 1 / (2 * (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖)) := hur.trans_le (min_le_right _ _)
  have hbd : (‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ ^ 2 ≤ 1 := by
    have : (‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) * ‖u‖ < 1 / 2 := by
      have hpos : 0 < 2 * (1 + ‖A * d‖ + ‖B * d‖ + ‖A * B * d‖) := by positivity
      rw [lt_div_iff₀ hpos] at hz2
      nlinarith [norm_nonneg u]
    nlinarith [norm_nonneg u, mul_le_mul_of_nonneg_left hc hcl]
  have hq1 : 1 - qPD A B d u ≤ 2 := by linarith [neg_abs_le (qPD A B d u)]
  show ‖(x : Fin 4 → ℝ)‖ ≤ 2
  rw [hxu, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [gr, Fin.cons_zero, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (1 - qPD A B d u) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · simp only [gr, Fin.cons_succ]
    exact ((norm_le_pi_norm u i).trans hu1.le).trans (by norm_num)

theorem zero_lt_one_add_of_mem_grBall {δ : ℝ} {x : Sph (nsFormR A B d) 1} (hx : x ∈ grBall A B d δ) :
    0 < 1 + (x : Fin 4 → ℝ) 0 := by
  linarith [hx.1]

/-! ### The cone map -/

variable (A B d) in
/-- **The cone map** $t\mapsto e^{t_0}\,\mathrm{gr}(t_1,t_2,t_3)$. -/
def grCone (t : Fin 4 → ℝ) : Fin 4 → ℝ := Real.exp (t 0) • gr A B d (Fin.tail t)

/-- **The graph cone map takes $B^4_\delta$ onto $\mathrm{pol}((-\delta,\delta)\times\mathrm{grBall}_\delta)$.** -/
theorem grCone_image {δ : ℝ} (hδ : δ ≤ radG A B d) :
    grCone A B d '' ball 0 δ = pol (nsFormR A B d) 1 '' (Ioo (-δ) δ ×ˢ grBall A B d δ) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨h0, hz⟩ := (ball_four_iff t).1 ht
    have hzr : ‖tl t‖ < radG A B d := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
    refine ⟨(t 0, ⟨gr A B d (tl t), eval_gr hzr⟩), ⟨h0, ?_⟩, rfl⟩
    exact (mem_grBall_iff hδ _).2 ⟨tl t, hz, rfl⟩
  · rintro ⟨⟨s, x⟩, ⟨hs, hx⟩, rfl⟩
    obtain ⟨z, hz, hxz⟩ := (mem_grBall_iff hδ x).1 hx
    refine ⟨Fin.cons s z, (ball_four_iff _).2 ⟨by simpa using hs, by simpa [tl] using hz⟩, ?_⟩
    simp only [grCone, pol, Fin.cons_zero, hxz, Fin.tail_cons]

theorem contDiffAt_grCone : ContDiffAt ℝ ⊤ (grCone A B d) 0 := by
  have hq : ContDiffAt ℝ ⊤ (fun t : Fin 4 → ℝ => 1 - qPD A B d (Fin.tail t)) 0 := by
    simp only [qPD, Fin.tail]; fun_prop
  have hpos : (fun t : Fin 4 → ℝ => 1 - qPD A B d (Fin.tail t)) 0 ≠ 0 := by simp [qPD, Fin.tail]
  have hr : ContDiffAt ℝ ⊤ (fun t : Fin 4 → ℝ => Real.sqrt (1 - qPD A B d (Fin.tail t))) 0 :=
    hq.sqrt hpos
  rw [contDiffAt_pi]; intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [grCone, gr, Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
    exact (Real.contDiff_exp.contDiffAt.comp _ (contDiffAt_apply ℝ (fun _ => ℝ) 0 (0 : Fin 4 → ℝ))).mul hr
  · simp only [grCone, gr, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    exact (Real.contDiff_exp.contDiffAt.comp _ (contDiffAt_apply ℝ (fun _ => ℝ) 0 (0 : Fin 4 → ℝ))).mul
      (contDiffAt_apply ℝ (fun _ => ℝ) i.succ (0 : Fin 4 → ℝ))

theorem hasDerivAt_grCone_line (p : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => grCone A B d (s • p)) p 0 := by
  rw [hasDerivAt_pi]; intro i
  have hq : HasDerivAt (fun s : ℝ => 1 - qPD A B d (Fin.tail (s • p))) 0 0 := by
    have e : (fun s : ℝ => 1 - qPD A B d (Fin.tail (s • p))) = fun s => 1 - s ^ 2 * qPD A B d (Fin.tail p) := by
      funext s; simp only [qPD, Fin.tail, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (qPD A B d (Fin.tail p))).const_sub 1
  have hr : HasDerivAt (fun s : ℝ => Real.sqrt (1 - qPD A B d (Fin.tail (s • p)))) 0 0 := by
    have h := hq.sqrt (by simp [qPD, Fin.tail])
    simpa using h
  have he : HasDerivAt (fun s : ℝ => Real.exp ((s • p) 0)) (p 0) 0 := by
    have := (Real.hasDerivAt_exp (0 * p 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).mul_const (p 0))
    simpa [Function.comp_def] using this
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [grCone, gr, Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
    convert he.mul hr using 1
    simp [qPD, Fin.tail]
  · simp only [grCone, gr, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    have hz : HasDerivAt (fun s : ℝ => Fin.tail (s • p) i) (p i.succ) 0 := by
      simpa [Fin.tail] using (hasDerivAt_id (0 : ℝ)).mul_const (p i.succ)
    simp only [Fin.tail, Pi.smul_apply, smul_eq_mul] at hz ⊢
    convert he.mul hz using 1
    simp

/-- **The strict derivative of the graph cone map at $0$ is the identity.** -/
theorem hasStrictFDerivAt_grCone :
    HasStrictFDerivAt (grCone A B d) (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) 0 := by
  have h := contDiffAt_grCone (A := A) (B := B) (d := d) |>.hasStrictFDerivAt (by simp)
  convert h using 1
  refine ContinuousLinearMap.ext fun p => ?_
  have hd : HasFDerivAt (grCone A B d) (fderiv ℝ (grCone A B d) 0) ((0 : ℝ) • p) := by
    rw [zero_smul]
    exact (contDiffAt_grCone.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => r • p) p 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun r : ℝ => grCone A B d (r • p)) (fderiv ℝ (grCone A B d) 0 p) 0 := by
    simpa [Function.comp_def] using hd.comp_hasDerivAt (0 : ℝ) hline
  exact ((hasDerivAt_grCone_line p).unique h1)

/-- **The cone density of the graph balls**: $\nu(\mathrm{grBall}_\delta)/\mathrm{vol}(B^3_\delta)\to1$. -/
theorem tendsto_nu_grBall :
    Tendsto (fun δ => (nu (nsFormR A B d) 1 (grBall A B d δ)).toReal / (volume (ball (0 : Fin 3 → ℝ) δ)).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_nu_div (fun δ => measurableSet_grBall δ) hasStrictFDerivAt_grCone
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventually_of_mem (Iic_mem_nhds (radG_pos A B d)) fun δ hδ => grCone_image hδ))
  have hdet : |(ContinuousLinearMap.id ℝ (Fin 4 → ℝ)).det| = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one]
  rwa [hdet] at h

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
