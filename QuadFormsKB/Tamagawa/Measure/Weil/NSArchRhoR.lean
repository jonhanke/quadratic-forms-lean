import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSL1R

/-!
# The local ratio of $\mathrm{SL}_1(D_w)\to SO(D_w^0)$ at a real place

**Layer:** one real place, $D = \mathbb H[\mathbb R,A,B]$ ($A,B\ne0$, any signs), $S_1$ with its Haar measure $\sigma$ (`NSArchSL1R`),
$c = $ `conjS` $: S_1\to SO(\langle-A,-B,AB\rangle)(\mathbb R)$.

* `eq_or_eq_neg_of_conjS_eq`: $c(x) = c(y)$ implies $y = \pm x$; hence `isLocInj_conjS` (the sphere avoids a neighbourhood of $0$,
  `norm_ge_of_sph`).
* `conjS_image_cayBall`: $c(\mathrm{cayBall}_\delta) = $ `ARq A B δ` (the chart neighbourhood), and $c$ is injective on
  $\mathrm{cayBall}_\delta$ (`injOn_conjS_cayBall`).
* **`leray_conjS_image`**: for every measurable $Y\subseteq S_1$ on which $c$ is injective,
  $$\mu_{\langle-A,-B,AB\rangle}(c(Y)) = \frac{1}{4|A|^3|B|^3}\,\sigma(Y).$$
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLeray QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.Leray

variable {A B : ℝ}

/-- If $c(x) = c(y)$ then $y = rx$ with $r^2 = 1$. -/
theorem eq_or_eq_neg_of_conjS_eq (hA : A ≠ 0) {x y : Sph (normForm A B) 1} (h : conjS x = conjS y) :
    (y : Fin 4 → ℝ) = x ∨ (y : Fin 4 → ℝ) = -(x : Fin 4 → ℝ) := by
  have h1 : conjS (y * x⁻¹) = 1 := by rw [map_mul, map_inv, ← h, mul_inv_cancel]
  have h3 : conjSO (toUnit (y * x⁻¹)) = 1 := Subtype.ext (congrArg (fun g : ArchSO (pureForm A B) => g.1) h1)
  have h4 : toUnit (y * x⁻¹) ∈ centerUnits A B := by
    rw [← ker_conjSO (two_ne_zero (α := ℝ)) hA, MonoidHom.mem_ker]; exact h3
  obtain ⟨r, hr⟩ := mem_centerUnits.1 h4
  have hyx : (vecQ (y : Fin 4 → ℝ) : ℍ[ℝ,A,B]) = (r : ℍ[ℝ,A,B]) * vecQ (x : Fin 4 → ℝ) := by
    have e : ((toUnit (y * x⁻¹) : (ℍ[ℝ,A,B])ˣ) : ℍ[ℝ,A,B]) * vecQ (x : Fin 4 → ℝ) = vecQ (y : Fin 4 → ℝ) := by
      rw [toUnit_mul]
      show vecQ (y : Fin 4 → ℝ) * (vecQ (qVec (star (vecQ (x : Fin 4 → ℝ))))) * vecQ (x : Fin 4 → ℝ) = _
      rw [vecQ_qVec, mul_assoc, star_mul_eq_nrd, nrd_sph]; simp
    rw [← e, hr]
  have hr2 : r ^ 2 = 1 := by
    have := congrArg nrd hyx
    rw [nrd_mul, nrd_coe, nrd_sph, nrd_sph, mul_one] at this
    exact this.symm
  have hr' : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  have hv : (y : Fin 4 → ℝ) = qVec ((r : ℍ[ℝ,A,B]) * vecQ (x : Fin 4 → ℝ)) := by
    rw [← hyx, qVec_vecQ]
  rcases hr' with rfl | rfl
  · left; rw [hv]; simp
  · right; rw [hv]; funext i; fin_cases i <;> simp [qVec, vecQ]

/-- Points of the norm-one sphere have sup norm at least $c_0 = (1+|A|+|B|+|AB|)^{-1/2}$. -/
theorem norm_ge_of_sph (x : Sph (normForm A B) 1) :
    1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖) ≤ ‖(x : Fin 4 → ℝ)‖ ^ 2 := by
  have hx := nrd_sph x
  set r := ‖(x : Fin 4 → ℝ)‖
  have hi : ∀ i, |(x : Fin 4 → ℝ) i| ≤ r := fun i => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
  have hsq : ∀ i, (x : Fin 4 → ℝ) i ^ 2 ≤ r ^ 2 := fun i => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hi i) 2
  have hc : 0 < 1 + ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
  rw [div_le_iff₀ hc]
  simp only [nrd, vecQ] at hx
  have h0 := hsq 0; have h1 := hsq 1; have h2 := hsq 2; have h3 := hsq 3
  have e1 : -A * (x : Fin 4 → ℝ) 1 ^ 2 ≤ ‖A‖ * r ^ 2 := by
    have := neg_abs_le A; rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg A, sq_nonneg ((x : Fin 4 → ℝ) 1)]
  have e2 : -B * (x : Fin 4 → ℝ) 2 ^ 2 ≤ ‖B‖ * r ^ 2 := by
    have := neg_abs_le B; rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg B, sq_nonneg ((x : Fin 4 → ℝ) 2)]
  have e3 : A * B * (x : Fin 4 → ℝ) 3 ^ 2 ≤ ‖A * B‖ * r ^ 2 := by
    have := le_abs_self (A * B); rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (A * B), sq_nonneg ((x : Fin 4 → ℝ) 3)]
  nlinarith

theorem conjS_neg_eq (x y : Sph (normForm A B) 1) (h : (y : Fin 4 → ℝ) = -(x : Fin 4 → ℝ)) :
    conjS y = conjS x := by
  apply Subtype.ext; apply Units.ext
  change ArchSOInst.mat _ (conjS y) = ArchSOInst.mat _ (conjS x)
  rw [mat_conjS, mat_conjS, h]
  have : (vecQ (-(x : Fin 4 → ℝ)) : ℍ[ℝ,A,B]) = (-1 : ℝ) • vecQ (x : Fin 4 → ℝ) := by
    ext <;> simp [vecQ]
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nMat, imv, Quat.pure, Pi.single_apply]

theorem isLocInj_conjS (hA : A ≠ 0) : IsLocInj (conjS (A := A) (B := B)) := by
  intro x
  set c := 1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖)
  have hc : 0 < c := by positivity
  refine ⟨{y | dist y x < Real.sqrt c}, isOpen_lt (continuous_id.dist continuous_const) continuous_const,
    by simpa using Real.sqrt_pos.2 hc, fun y hy y' hy' hyy => ?_⟩
  rcases eq_or_eq_neg_of_conjS_eq hA hyy with h | h
  · exact (Subtype.ext h).symm
  · exfalso
    have hd : dist (y' : Fin 4 → ℝ) (y : Fin 4 → ℝ) < 2 * Real.sqrt c := by
      calc dist (y' : Fin 4 → ℝ) (y : Fin 4 → ℝ) ≤ dist (y' : Fin 4 → ℝ) x + dist (y : Fin 4 → ℝ) x :=
            dist_triangle_right _ _ _
        _ < Real.sqrt c + Real.sqrt c := add_lt_add hy' hy
        _ = 2 * Real.sqrt c := by ring
    rw [h, dist_eq_norm, show -(y : Fin 4 → ℝ) - y = (-2 : ℝ) • (y : Fin 4 → ℝ) by
      rw [neg_smul, two_smul]; abel, norm_smul] at hd
    have hn := norm_ge_of_sph y
    have : ‖(y : Fin 4 → ℝ)‖ < Real.sqrt c := by
      norm_num at hd; linarith
    have := (Real.lt_sqrt (norm_nonneg _)).1 this
    linarith

/-! ### The Cayley chart -/

theorem toUnit_eq_smul {δ : ℝ} (hδ : δ ≤ radR A B) {x : Sph (normForm A B) 1} {z : Fin 3 → ℝ}
    (hz : z ∈ ball (0 : Fin 3 → ℝ) δ) (hxz : (x : Fin 4 → ℝ) = cay A B z) :
    ((toUnit x : (ℍ[ℝ,A,B])ˣ) : ℍ[ℝ,A,B]) = (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) • (1 + Quat.pure z) := by
  show vecQ (x : Fin 4 → ℝ) = _
  rw [hxz]
  ext <;> simp [cay, vecQ, Quat.pure, cons_one, cons_two, cons_three]

theorem conjS_cay {δ : ℝ} (hδ : δ ≤ radR A B) {x : Sph (normForm A B) 1} {z : Fin 3 → ℝ}
    (hz : z ∈ ball (0 : Fin 3 → ℝ) δ) (hxz : (x : Fin 4 → ℝ) = cay A B z) :
    ArchSOInst.mat _ (conjS x) = cMat A B z := by
  have hzr : ‖z‖ < radR A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
  have hp := one_add_qPure_pos hzr
  exact conjGL_eq_cMat_of_smul (toUnit x) _ z (Real.rpow_pos_of_pos hp _).ne' hp.ne' (toUnit_eq_smul hδ hz hxz)

theorem conjS_image_cayBall {δ : ℝ} (hδ : δ ≤ radR A B) :
    conjS '' cayBall A B δ = ARq A B δ := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := (mem_cayBall_iff hδ x).1 hx
    exact ⟨z, hz, conjS_cay hδ hz hxz⟩
  · rintro ⟨z, hz, hg⟩
    have hzr : ‖z‖ < radR A B := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ
    refine ⟨⟨cay A B z, eval_cay hzr⟩, (mem_cayBall_iff hδ _).2 ⟨z, hz, rfl⟩, ?_⟩
    apply Subtype.ext; apply Units.ext
    change ArchSOInst.mat _ (conjS _) = ArchSOInst.mat _ g
    rw [hg, conjS_cay hδ hz rfl]

theorem injOn_conjS_cayBall (hA : A ≠ 0) (δ : ℝ) : InjOn (conjS (A := A) (B := B)) (cayBall A B δ) := by
  intro x hx y hy hxy
  rcases eq_or_eq_neg_of_conjS_eq hA hxy with h | h
  · exact (Subtype.ext h).symm
  · exfalso
    have h0 := congrFun h 0
    have := hx.1; have := hy.1
    simp only [Pi.neg_apply] at h0
    linarith

/-- **The local ratio of $\mathrm{SL}_1\to SO_3$ at a real place.** -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratio of gauge measures, real place)"]
theorem leray_conjS_image (hA : A ≠ 0) (hB : B ≠ 0) (hQ : gramDetR (pureForm A B) ≠ 0)
    {Y : Set (Sph (normForm A B) 1)} (hY : MeasurableSet Y) (hinj : InjOn conjS Y) :
    lerayMeasure (pureForm A B) hQ (conjS '' Y) =
      ENNReal.ofReal (1 / (4 * |A| ^ 3 * |B| ^ 3)) * sig (normForm A B) 1 Y := by
  have := isHaarMeasure_lerayMeasure hQ
  obtain ⟨c, hc⟩ := exists_measure_image_eq_smul (sig (normForm A B) 1) (lerayMeasure (pureForm A B) hQ)
    conjS continuous_conjS (isLocInj_conjS hA)
  -- identify `c` on the Cayley balls
  have hsig : ∀ S, sig (normForm A B) 1 S = ENNReal.ofReal (1 / 2) * nu (normForm A B) 1 S := fun S => by
    rw [sig, Measure.smul_apply, smul_eq_mul]; norm_num
  have hfin : ∀ δ, δ ≤ radR A B → nu (normForm A B) 1 (cayBall A B δ) ≠ ⊤ := fun δ hδ => by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (cayBall_subset hδ)) (nu_bounded_lt_top one_ne_zero 2))
  have hfg : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (lerayMeasure (pureForm A B) hQ (ARq A B δ)).toReal =
      ((c : ℝ) / 2) * (nu (normForm A B) 1 (cayBall A B δ)).toReal := by
    filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds (radR_pos A B))] with δ hδ
    rw [← conjS_image_cayBall hδ, hc _ (measurableSet_cayBall δ) (injOn_conjS_cayBall hA δ), hsig,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by norm_num)]
    ring
  have hκ := ratio_eq_of_tendsto hfg (tendsto_leray_quatBall hA hB hQ) tendsto_nu_cayBall one_ne_zero
  have hc' : (c : ℝ) = 1 / (4 * |A| ^ 3 * |B| ^ 3) := by
    have hA3 : 0 < |A| ^ 3 := pow_pos (abs_pos.2 hA) 3
    have hB3 : 0 < |B| ^ 3 := pow_pos (abs_pos.2 hB) 3
    rw [div_one] at hκ
    field_simp at hκ ⊢
    linarith
  rw [hc Y hY hinj, ← ENNReal.ofReal_coe_nnreal, hc']

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
