import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSL1C

/-!
# The local ratio of $\mathrm{SL}_1(D_w)\to SO(D_w^0)$ at a complex place

**Layer:** one complex place, $D = \mathbb H[\mathbb C,A,B]$ ($A,B\ne0$), $S_1$ with its Haar measure $\sigma_{\mathbb C}$ (`NSArchSL1C`),
$c = $ `conjSC` $: S_1\to SO(\langle-A,-B,AB\rangle)(\mathbb C)$. Complex analogue of `NSArchRhoR.lean`.

* `eq_or_eq_neg_of_conjSC_eq`: $c(x) = c(y)$ implies $y = \pm x$; hence `isLocInj_conjSC`.
* `conjSC_image_cayBallC`: $c(\mathrm{cayBall}_\delta) = $ `ACq A B δ` (the chart neighbourhood), and $c$ is injective on
  $\mathrm{cayBall}_\delta$ (`injOn_conjSC_cayBallC`).
* **`leray_conjSC_image`**: for every measurable $Y\subseteq S_1$ on which $c$ is injective,
  $$\mu_{\langle-A,-B,AB\rangle}(c(Y)) = \frac{1}{16\,|A|^6|B|^6}\,\sigma_{\mathbb C}(Y).$$
  The constant: $\mu(\mathrm{ACq}_\delta)/\mathrm{vol}(B_\delta)\to1/(8|A|^3|B|^3)^2$ (`tendsto_lerayC_quatBall`) and
  $\sigma_{\mathbb C}(\mathrm{cayBall}_\delta)/\mathrm{vol}(B_\delta)\to\tfrac14$ ($\sigma_{\mathbb C} = \nu_{\mathbb C}/|2|^2$).
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLerayC QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.Leray

variable {A B : ℂ}

/-- If $c(x) = c(y)$ then $y = \pm x$. -/
theorem eq_or_eq_neg_of_conjSC_eq (hA : A ≠ 0) {x y : SphC (normForm A B) 1} (h : conjSC x = conjSC y) :
    (y : Fin 4 → ℂ) = x ∨ (y : Fin 4 → ℂ) = -(x : Fin 4 → ℂ) := by
  have h1 : conjSC (y * x⁻¹) = 1 := by rw [map_mul, map_inv, ← h, mul_inv_cancel]
  have h2 := congrArg (ArchSOC.incl (pureForm A B)) h1
  rw [map_one] at h2
  have h3 : conjSO (toUnitC (y * x⁻¹)) = 1 := Subtype.ext h2
  have h4 : toUnitC (y * x⁻¹) ∈ centerUnits A B := by
    rw [← ker_conjSO (two_ne_zero (α := ℂ)) hA, MonoidHom.mem_ker]; exact h3
  obtain ⟨r, hr⟩ := mem_centerUnits.1 h4
  have hyx : (vecQ (y : Fin 4 → ℂ) : ℍ[ℂ,A,B]) = (r : ℍ[ℂ,A,B]) * vecQ (x : Fin 4 → ℂ) := by
    have e : ((toUnitC (y * x⁻¹) : (ℍ[ℂ,A,B])ˣ) : ℍ[ℂ,A,B]) * vecQ (x : Fin 4 → ℂ) = vecQ (y : Fin 4 → ℂ) := by
      rw [toUnitC_mul]
      show vecQ (y : Fin 4 → ℂ) * (vecQ (qVec (star (vecQ (x : Fin 4 → ℂ))))) * vecQ (x : Fin 4 → ℂ) = _
      rw [vecQ_qVec, mul_assoc, star_mul_eq_nrd, nrd_sphC]; simp
    rw [← e, hr]
  have hr2 : r ^ 2 = 1 := by
    have := congrArg nrd hyx
    rw [nrd_mul, nrd_coe, nrd_sphC, nrd_sphC, mul_one] at this
    exact this.symm
  have hr' : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hv : (y : Fin 4 → ℂ) = qVec ((r : ℍ[ℂ,A,B]) * vecQ (x : Fin 4 → ℂ)) := by
    rw [← hyx, qVec_vecQ]
  rcases hr' with rfl | rfl
  · left; rw [hv]; simp
  · right; rw [hv]; funext i; fin_cases i <;> simp [qVec, vecQ]

/-- Points of the norm-one sphere have sup norm at least $c_0 = (1+|A|+|B|+|AB|)^{-1/2}$. -/
theorem norm_ge_of_sphC (x : SphC (normForm A B) 1) :
    1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖) ≤ ‖(x : Fin 4 → ℂ)‖ ^ 2 := by
  have hx := nrd_sphC x
  set r := ‖(x : Fin 4 → ℂ)‖
  have hi : ∀ i, ‖(x : Fin 4 → ℂ) i‖ ≤ r := fun i => norm_le_pi_norm _ i
  have hsq : ∀ i, ‖(x : Fin 4 → ℂ) i‖ ^ 2 ≤ r ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (hi i) 2
  have hc : 0 < 1 + ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
  rw [div_le_iff₀ hc]
  have hx' : (x : Fin 4 → ℂ) 0 ^ 2 + (-A * (x : Fin 4 → ℂ) 1 ^ 2) + (-B * (x : Fin 4 → ℂ) 2 ^ 2) +
      A * B * (x : Fin 4 → ℂ) 3 ^ 2 = 1 := by
    simp only [nrd, vecQ] at hx
    linear_combination hx
  have hn : (1 : ℝ) ≤ ‖(x : Fin 4 → ℂ) 0‖ ^ 2 + ‖A‖ * ‖(x : Fin 4 → ℂ) 1‖ ^ 2 + ‖B‖ * ‖(x : Fin 4 → ℂ) 2‖ ^ 2 +
      ‖A * B‖ * ‖(x : Fin 4 → ℂ) 3‖ ^ 2 := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
      _ = _ := congrArg norm hx'.symm
      _ ≤ ‖(x : Fin 4 → ℂ) 0 ^ 2 + (-A * (x : Fin 4 → ℂ) 1 ^ 2) + (-B * (x : Fin 4 → ℂ) 2 ^ 2)‖ +
            ‖A * B * (x : Fin 4 → ℂ) 3 ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(x : Fin 4 → ℂ) 0 ^ 2 + (-A * (x : Fin 4 → ℂ) 1 ^ 2)‖ + ‖-B * (x : Fin 4 → ℂ) 2 ^ 2‖) +
            ‖A * B * (x : Fin 4 → ℂ) 3 ^ 2‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(x : Fin 4 → ℂ) 0 ^ 2‖ + ‖-A * (x : Fin 4 → ℂ) 1 ^ 2‖) + ‖-B * (x : Fin 4 → ℂ) 2 ^ 2‖) +
            ‖A * B * (x : Fin 4 → ℂ) 3 ^ 2‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by simp only [norm_mul, norm_pow, norm_neg]
  have h0 := hsq 0; have h1 := hsq 1; have h2 := hsq 2; have h3 := hsq 3
  nlinarith [norm_nonneg A, norm_nonneg B, norm_nonneg (A * B), mul_le_mul_of_nonneg_left h1 (norm_nonneg A),
    mul_le_mul_of_nonneg_left h2 (norm_nonneg B), mul_le_mul_of_nonneg_left h3 (norm_nonneg (A * B))]

theorem conjSC_neg_eq (x y : SphC (normForm A B) 1) (h : (y : Fin 4 → ℂ) = -(x : Fin 4 → ℂ)) :
    conjSC y = conjSC x := by
  apply Subtype.ext; apply Units.ext
  change ArchSOC.mat _ (conjSC y) = ArchSOC.mat _ (conjSC x)
  rw [mat_conjSC, mat_conjSC, h]
  have : (vecQ (-(x : Fin 4 → ℂ)) : ℍ[ℂ,A,B]) = (-1 : ℂ) • vecQ (x : Fin 4 → ℂ) := by
    ext <;> simp [vecQ]
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nMat, imv, Quat.pure, Pi.single_apply]

theorem isLocInj_conjSC (hA : A ≠ 0) : IsLocInj (conjSC (A := A) (B := B)) := by
  intro x
  set c := 1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖)
  have hc : 0 < c := by positivity
  refine ⟨{y | dist y x < Real.sqrt c}, isOpen_lt (continuous_id.dist continuous_const) continuous_const,
    by simpa using Real.sqrt_pos.2 hc, fun y hy y' hy' hyy => ?_⟩
  rcases eq_or_eq_neg_of_conjSC_eq hA hyy with h | h
  · exact (Subtype.ext h).symm
  · exfalso
    have hd : dist (y' : Fin 4 → ℂ) (y : Fin 4 → ℂ) < 2 * Real.sqrt c := by
      calc dist (y' : Fin 4 → ℂ) (y : Fin 4 → ℂ) ≤ dist (y' : Fin 4 → ℂ) x + dist (y : Fin 4 → ℂ) x :=
            dist_triangle_right _ _ _
        _ < Real.sqrt c + Real.sqrt c := add_lt_add hy' hy
        _ = 2 * Real.sqrt c := by ring
    rw [h, dist_eq_norm, show -(y : Fin 4 → ℂ) - y = (-2 : ℂ) • (y : Fin 4 → ℂ) by
      rw [neg_smul, two_smul]; abel, norm_smul] at hd
    have hn := norm_ge_of_sphC y
    have h2 : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [h2] at hd
    have : ‖(y : Fin 4 → ℂ)‖ < Real.sqrt c := by linarith
    have := (Real.lt_sqrt (norm_nonneg _)).1 this
    linarith

/-! ### The Cayley chart -/

theorem toUnitC_eq_smul {x : SphC (normForm A B) 1} {z : Fin 3 → ℂ} (hxz : (x : Fin 4 → ℂ) = cayC A B z) :
    ((toUnitC x : (ℍ[ℂ,A,B])ˣ) : ℍ[ℂ,A,B]) = (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) • (1 + Quat.pure z) := by
  show vecQ (x : Fin 4 → ℂ) = _
  rw [hxz]
  ext <;> simp [cayC, vecQ, Quat.pure, consC_one, consC_two, consC_three]

theorem conjSC_cayC {δ : ℝ} (hδ : δ ≤ radC A B) {x : SphC (normForm A B) 1} {z : Fin 3 → ℂ}
    (hz : z ∈ ball (0 : Fin 3 → ℂ) δ) (hxz : (x : Fin 4 → ℂ) = cayC A B z) :
    ArchSOC.mat _ (conjSC x) = cMat A B z := by
  have hzr : ‖z‖ < radC A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
  have hp := one_add_qPure_ne_zeroC hzr
  have hr : (1 + qPure A B z) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
    intro h
    have := re_cpow_neg_half_pos (one_add_qPure_mem_slitPlane hzr)
    rw [h] at this; simp at this
  exact conjGL_eq_cMat_of_smul (toUnitC x) _ z hr hp (toUnitC_eq_smul hxz)

theorem conjSC_image_cayBallC {δ : ℝ} (hδ : δ ≤ radC A B) :
    conjSC '' cayBallC A B δ = ACq A B δ := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := (mem_cayBallC_iff hδ x).1 hx
    exact ⟨z, hz, conjSC_cayC hδ hz hxz⟩
  · rintro ⟨z, hz, hg⟩
    have hzr : ‖z‖ < radC A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
    refine ⟨⟨cayC A B z, eval_cayC hzr⟩, (mem_cayBallC_iff hδ _).2 ⟨z, hz, rfl⟩, ?_⟩
    apply Subtype.ext; apply Units.ext
    change ArchSOC.mat _ (conjSC _) = ArchSOC.mat _ g
    rw [hg, conjSC_cayC hδ hz rfl]

theorem injOn_conjSC_cayBallC (hA : A ≠ 0) (δ : ℝ) :
    InjOn (conjSC (A := A) (B := B)) (cayBallC A B δ) := by
  intro x hx y hy hxy
  rcases eq_or_eq_neg_of_conjSC_eq hA hxy with h | h
  · exact (Subtype.ext h).symm
  · exfalso
    have h0 := congrArg Complex.re (congrFun h 0)
    have := hx.1; have := hy.1
    simp only [Pi.neg_apply, Complex.neg_re] at h0
    linarith

/-- **The local ratio of $\mathrm{SL}_1\to SO_3$ at a complex place.** -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratio of gauge measures, complex place)"]
theorem leray_conjSC_image (hA : A ≠ 0) (hB : B ≠ 0) (hQ : gramDetC (pureForm A B) ≠ 0)
    {Y : Set (SphC (normForm A B) 1)} (hY : MeasurableSet Y) (hinj : InjOn conjSC Y) :
    lerayMeasureC (pureForm A B) hQ (conjSC '' Y) =
      ENNReal.ofReal (1 / (16 * ‖A‖ ^ 6 * ‖B‖ ^ 6)) * sigC (normForm A B) 1 Y := by
  have := isHaarMeasure_lerayMeasureC (Q := pureForm A B) (hQ := hQ)
  obtain ⟨c, hc⟩ := exists_measure_image_eq_smul (sigC (normForm A B) 1) (lerayMeasureC (pureForm A B) hQ)
    conjSC continuous_conjSC (isLocInj_conjSC hA)
  have hsig : ∀ S, (sigC (normForm A B) 1 S).toReal = (nuC (normForm A B) 1 S).toReal / 4 := fun S => by
    rw [sigC, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
    have h2 : ‖(2 * 1 : ℂ)‖₊ = 2 := by ext; simp
    rw [h2]
    push_cast
    ring
  have hfg : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (lerayMeasureC (pureForm A B) hQ (ACq A B δ)).toReal =
      (c : ℝ) * (sigC (normForm A B) 1 (cayBallC A B δ)).toReal := by
    filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds (radC_pos A B))] with δ hδ
    rw [← conjSC_image_cayBallC hδ, hc _ (measurableSet_cayBallC δ) (injOn_conjSC_cayBallC hA δ),
      ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hs : Tendsto (fun δ => (sigC (normForm A B) 1 (cayBallC A B δ)).toReal /
      (volume (ball (0 : Fin 3 → ℂ) δ)).toReal) (𝓝[>] 0) (𝓝 (1 / 4)) := by
    have h := (tendsto_nuC_cayBallC (A := A) (B := B)).div_const 4
    refine h.congr fun δ => ?_
    rw [hsig]; ring
  have hκ := ratio_eq_of_tendsto hfg (tendsto_lerayC_quatBall hA hB hQ) hs (by norm_num)
  have hc' : (c : ℝ) = 1 / (16 * ‖A‖ ^ 6 * ‖B‖ ^ 6) := by
    have hA3 : 0 < ‖A‖ := norm_pos_iff.2 hA
    have hB3 : 0 < ‖B‖ := norm_pos_iff.2 hB
    rw [hκ]
    field_simp
    ring
  rw [hc Y hY hinj, ← ENNReal.ofReal_coe_nnreal, hc']

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
