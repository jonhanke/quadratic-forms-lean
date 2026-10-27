import QuadFormsKB.Tamagawa.Measure.SphereLerayC
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchReal

/-!
# Densities of the complex sphere Leray measures in a chart

Complex analogue of `tendsto_nu_div` (`NSArchDensity.lean`): if $G(B^{\mathbb C^4}_\delta) =
\mathrm{pol}(R_\delta\times A_\delta)$ with $R_\delta = \{\beta\in\mathbb C^\times : |\beta-1|<\delta\}$ and $G$ has real
strict derivative $L$ at $0$, then $\nu_{\mathbb C}(A_\delta)/\mathrm{vol}(B^{\mathbb C^3}_\delta)\to|\det_{\mathbb R}L|$
(**`tendsto_nuC_div`**). The radial factor is $\lambda_4(R_\delta)=\int_{R_\delta}|\beta|^6\,d^2\beta\sim\pi\delta^2$.
-/

open MeasureTheory Measure Set Filter Topology Metric
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

section Complex

open SphereLerayC

/-- The disc $R_\delta = \{\beta\in\mathbb C^\times : |\beta-1|<\delta\}$ of radial parameters. -/
def RdC (δ : ℝ) : Set ℂˣ := {β | ‖(β : ℂ) - 1‖ < δ}

theorem isOpen_RdC (δ : ℝ) : IsOpen (RdC δ) :=
  isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const

theorem image_val_RdC {δ : ℝ} (hδ : δ ≤ 1) : Units.val '' RdC δ = ball (1 : ℂ) δ := by
  ext z
  constructor
  · rintro ⟨β, hβ, rfl⟩
    simpa [RdC, dist_eq_norm] using hβ
  · intro hz
    have hz' : ‖z - 1‖ < δ := by simpa [dist_eq_norm] using hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz'; linarith
    exact ⟨Units.mk0 z hz0, hz', rfl⟩

theorem volU_RdC {δ : ℝ} (hδ : δ ≤ 1) : volU (RdC δ) = volume (ball (1 : ℂ) δ) := by
  rw [volU_apply (isOpen_RdC δ).measurableSet, image_val_RdC hδ]

theorem RdC_subset_halfU {δ : ℝ} (hδ : δ ≤ 1) : RdC δ ⊆ halfU := by
  intro β hβ
  have h2 : ‖(β : ℂ) - 1‖ < δ := hβ
  have h4 : 1 - (β : ℂ).re ≤ ‖(β : ℂ) - 1‖ := by
    have h := Complex.abs_re_le_norm ((β : ℂ) - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    have := neg_abs_le ((β : ℂ).re - 1)
    linarith
  show 0 < (β : ℂ).re
  linarith

theorem wt_six (β : ℂˣ) : wt 6 β = ENNReal.ofReal (‖(β : ℂ)‖ ^ 6) := by
  rw [wt, ← ENNReal.ofReal_coe_nnreal]
  congr 1

theorem lamU_four_RdC_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal ((1 - δ) ^ 6) * volume (ball (1 : ℂ) δ) ≤ lamU 4 (RdC δ) ∧
      lamU 4 (RdC δ) ≤ ENNReal.ofReal ((1 + δ) ^ 6) * volume (ball (1 : ℂ) δ) := by
  have hk : ((2 * (4 : ℕ) - 2 : ℤ)) = 6 := by norm_num
  have hl : lamU 4 (RdC δ) = ∫⁻ β in RdC δ, wt 6 β ∂volU := by
    rw [lamU, withDensity_apply _ (isOpen_RdC δ).measurableSet]
    simp only [hk]
  have hnorm : ∀ β ∈ RdC δ, 1 - δ ≤ ‖(β : ℂ)‖ ∧ ‖(β : ℂ)‖ ≤ 1 + δ := by
    intro β hβ
    have h : ‖(β : ℂ) - 1‖ < δ := hβ
    have h1 := abs_norm_sub_norm_le (β : ℂ) 1
    rw [norm_one] at h1
    constructor <;> linarith [abs_le.1 h1]
  have hv : volU (RdC δ) = volume (ball (1 : ℂ) δ) := volU_RdC hδ1.le
  constructor
  · rw [hl, ← hv, ← setLIntegral_const]
    refine setLIntegral_mono' (isOpen_RdC δ).measurableSet fun β hβ => ?_
    rw [wt_six]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) (hnorm β hβ).1 6)
  · rw [hl, ← hv, ← setLIntegral_const]
    refine setLIntegral_mono' (isOpen_RdC δ).measurableSet fun β hβ => ?_
    rw [wt_six]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hnorm β hβ).2 6)

theorem volume_polC_RdC {Q : QuadForm ℂ 4} {δ : ℝ} (hδ1 : δ ≤ 1) {A : Set (SphC Q 1)}
    (hA : MeasurableSet A) : volume (polC Q 1 '' (RdC δ ×ˢ A)) = lamU 4 (RdC δ) * nuC Q 1 A := by
  rw [← MC_apply_of_subset one_ne_zero ((isOpen_RdC δ).measurableSet.prod hA)
    (prod_mono (RdC_subset_halfU hδ1) (subset_univ _)),
    MC_prod one_ne_zero (by norm_num) hA (isOpen_RdC δ).measurableSet]

theorem volume_ball_pi_C (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    volume (ball (0 : Fin k → ℂ) δ) = volume (ball (0 : ℂ) δ) ^ k := by
  rw [ball_pi _ hδ, volume_pi_pi]; simp

theorem volume_disc_toReal (c : ℂ) {δ : ℝ} (hδ : 0 < δ) : (volume (ball c δ)).toReal = Real.pi * δ ^ 2 := by
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le]
  simp; ring

theorem volume_ball_four_C {δ : ℝ} (hδ : 0 < δ) :
    (volume (ball (0 : Fin 4 → ℂ) δ)).toReal =
      Real.pi * δ ^ 2 * (volume (ball (0 : Fin 3 → ℂ) δ)).toReal := by
  rw [volume_ball_pi_C _ hδ, volume_ball_pi_C _ hδ, ENNReal.toReal_pow, ENNReal.toReal_pow, volume_disc_toReal 0 hδ]
  ring

theorem tendsto_pi_div_lamU :
    Tendsto (fun δ : ℝ => Real.pi * δ ^ 2 / (lamU 4 (RdC δ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto (fun δ : ℝ => ((1 + δ) ^ 6)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have : ContinuousAt (fun δ : ℝ => ((1 + δ) ^ 6)⁻¹) 0 :=
      ((continuous_const.add continuous_id).pow 6).continuousAt.inv₀ (by simp)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun δ : ℝ => ((1 - δ) ^ 6)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have : ContinuousAt (fun δ : ℝ => ((1 - δ) ^ 6)⁻¹) 0 :=
      ((continuous_const.sub continuous_id).pow 6).continuousAt.inv₀ (by simp)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have key : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 ∧
      (1 - δ) ^ 6 * (Real.pi * δ ^ 2) ≤ (lamU 4 (RdC δ)).toReal ∧
      (lamU 4 (RdC δ)).toReal ≤ (1 + δ) ^ 6 * (Real.pi * δ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))] with δ
      (hδ : 0 < δ) hδ1
    have hδ1 : δ < 1 := hδ1
    obtain ⟨b1, b2⟩ := lamU_four_RdC_bounds hδ hδ1
    have hfin : volume (ball (1 : ℂ) δ) ≠ ⊤ := measure_ball_lt_top.ne
    have hvol : (volume (ball (1 : ℂ) δ)).toReal = Real.pi * δ ^ 2 := volume_disc_toReal 1 hδ
    have htop : lamU 4 (RdC δ) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) b2
    refine ⟨hδ, hδ1, ?_, ?_⟩
    · have := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) htop).2 b1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have : 0 ≤ 1 - δ := by linarith
                                                         positivity), hvol] at this
    · have := (ENNReal.toReal_le_toReal htop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)).2 b2
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hvol] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [key] with δ ⟨hδ, hδ1, h1, h2⟩
    have hP : 0 < Real.pi * δ ^ 2 := by positivity
    have h0 : 0 < (1 - δ) ^ 6 := pow_pos (by linarith) 6
    have hpos : 0 < (lamU 4 (RdC δ)).toReal := lt_of_lt_of_le (mul_pos h0 hP) h1
    show ((1 + δ) ^ 6)⁻¹ ≤ _
    rw [inv_eq_one_div, div_le_div_iff₀ (pow_pos (by linarith) 6) hpos]
    linarith
  · filter_upwards [key] with δ ⟨hδ, hδ1, h1, h2⟩
    have hP : 0 < Real.pi * δ ^ 2 := by positivity
    have h0 : 0 < (1 - δ) ^ 6 := pow_pos (by linarith) 6
    have hpos : 0 < (lamU 4 (RdC δ)).toReal := lt_of_lt_of_le (mul_pos h0 hP) h1
    show _ ≤ ((1 - δ) ^ 6)⁻¹
    rw [inv_eq_one_div, div_le_div_iff₀ hpos h0]
    linarith

/-- **The cone density in a chart** (complex): if $G(B^{\mathbb C^4}_\delta)=\mathrm{pol}(R_\delta\times A_\delta)$ for small
$\delta$ and $G$ has real strict derivative $L$ at $0$, then $\nu_{\mathbb C}(A_\delta)/\mathrm{vol}(B^{\mathbb C^3}_\delta)
\to|\det_{\mathbb R}L|$. -/
theorem tendsto_nuC_div {Q : QuadForm ℂ 4} {A : ℝ → Set (SphC Q 1)} (hA : ∀ δ, MeasurableSet (A δ))
    {G : (Fin 4 → ℂ) → Fin 4 → ℂ} {L : (Fin 4 → ℂ) →L[ℝ] Fin 4 → ℂ} (hG : HasStrictFDerivAt G L 0)
    (himg : ∀ᶠ δ in 𝓝[>] (0 : ℝ), G '' ball 0 δ = polC Q 1 '' (RdC δ ×ˢ A δ)) :
    Tendsto (fun δ => (nuC Q 1 (A δ)).toReal / (volume (ball (0 : Fin 3 → ℂ) δ)).toReal) (𝓝[>] 0)
      (𝓝 |L.det|) := by
  have hT := tendsto_image_ball_div (volume : Measure (Fin 4 → ℂ)) hG
  have hbdd : ∀ᶠ δ in 𝓝[>] (0 : ℝ), volume (G '' ball 0 δ) ≠ ⊤ := by
    have hc : ContinuousAt G 0 := hG.hasFDerivAt.continuousAt
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds (ball_mem_nhds (G 0) one_pos))
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hr)] with δ hδ
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (measure_ball_lt_top (x := G 0) (r := 1)))
    rintro _ ⟨z, hz, rfl⟩
    exact hsub (ball_subset_ball (le_of_lt hδ) hz)
  have key : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (nuC Q 1 (A δ)).toReal / (volume (ball (0 : Fin 3 → ℂ) δ)).toReal =
      (volume (G '' ball 0 δ)).toReal / (volume (ball (0 : Fin 4 → ℂ) δ)).toReal *
        (Real.pi * δ ^ 2 / (lamU 4 (RdC δ)).toReal) := by
    filter_upwards [himg, hbdd, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))]
      with δ hδ hfin (hδ0 : 0 < δ) hδ1
    have hδ1 : δ < 1 := hδ1
    rw [hδ, volume_polC_RdC hδ1.le (hA δ)] at hfin ⊢
    obtain ⟨b1, b2⟩ := lamU_four_RdC_bounds hδ0 hδ1
    have hvf : volume (ball (1 : ℂ) δ) ≠ ⊤ := measure_ball_lt_top.ne
    have hvp : 0 < volume (ball (1 : ℂ) δ) := measure_ball_pos volume _ hδ0
    have hl0 : lamU 4 (RdC δ) ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le ?_ b1)
      refine ENNReal.mul_pos (ENNReal.ofReal_pos.2 (pow_pos (by linarith) 6)).ne' hvp.ne'
    have hlt : lamU 4 (RdC δ) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvf) b2
    have hnt : nuC Q 1 (A δ) ≠ ⊤ := fun h => hfin (by rw [h, ENNReal.mul_top hl0])
    have hlpos : 0 < (lamU 4 (RdC δ)).toReal := ENNReal.toReal_pos hl0 hlt
    have hv3 : 0 < (volume (ball (0 : Fin 3 → ℂ) δ)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos volume _ hδ0).ne' measure_ball_lt_top.ne
    have hP : 0 < Real.pi * δ ^ 2 := by positivity
    rw [ENNReal.toReal_mul, volume_ball_four_C hδ0]
    field_simp
  have h := hT.mul tendsto_pi_div_lamU
  rw [mul_one] at h
  exact h.congr' (key.mono fun δ hδ => hδ.symm)

end Complex

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
