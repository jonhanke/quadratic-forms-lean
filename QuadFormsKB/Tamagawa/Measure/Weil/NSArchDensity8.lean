import QuadFormsKB.Tamagawa.Measure.Weil.NSArchDensity

/-!
# The density of the complex sphere measure in a real chart

**Layer:** one archimedean place; a complex quaternary form $Q$ and its sphere $S_1 = \{Q = 1\}\subseteq\mathbb C^4$ with the cone measure
$\nu_{\mathbb C}$ (`nuC`). Here the chart is **real**: $\mathbb C^4$ is identified with $E = (\mathbb R^2)^4$ (`eC`, real and imaginary parts,
measure preserving, `measurePreserving_eC`), and the radial parameter runs over the square
$R_\delta = \{\beta : |\operatorname{Re}\beta - 1|<\delta,\ |\operatorname{Im}\beta|<\delta\}$ (`rsq`).

* **`tendsto_nuC_div8`**: if $G : E\to E$ has strict derivative $L$ at $0$ and $G(B^E_\delta) = e_{\mathbb C}(\{\beta x : \beta\in R_\delta,\ x\in A_\delta\})$
  for small $\delta$, then $\nu_{\mathbb C}(A_\delta)/(2\delta)^6\to|\det L|$.

This is the sphere-side input at a real place with $E_w = \mathbb C$, where the test set is a product of two real $3$-dimensional
families inside the $6$-dimensional complex sphere.
-/

open MeasureTheory Measure Set Filter Topology Metric
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open SphereLerayC

/-- The real coordinates of $\mathbb C^4$. -/
abbrev E8 : Type := Fin 4 → Fin 2 → ℝ

/-- $\mathbb C^4\to(\mathbb R^2)^4$, real and imaginary parts. -/
def eC (y : Fin 4 → ℂ) : E8 := fun i => Complex.measurableEquivPi (y i)

theorem measurePreserving_eC : MeasurePreserving eC (volume : Measure (Fin 4 → ℂ)) (volume : Measure E8) :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) fun _ => Complex.volume_preserving_equiv_pi

theorem eC_injective : Function.Injective eC := fun y y' h => by
  funext i
  exact Complex.measurableEquivPi.injective (congrFun h i)

theorem measurableEmbedding_eC : MeasurableEmbedding eC :=
  (MeasurableEquiv.piCongrRight fun _ : Fin 4 => Complex.measurableEquivPi).measurableEmbedding

/-- The square $R_\delta$ of radial parameters. -/
def rsq (δ : ℝ) : Set ℂˣ := {β | |(β : ℂ).re - 1| < δ ∧ |(β : ℂ).im| < δ}

theorem measurableSet_rsq (δ : ℝ) : MeasurableSet (rsq δ) := by
  have h1 : Continuous fun β : ℂˣ => |(β : ℂ).re - 1| :=
    continuous_abs.comp ((Complex.continuous_re.comp Units.continuous_val).sub continuous_const)
  have h2 : Continuous fun β : ℂˣ => |(β : ℂ).im| := continuous_abs.comp (Complex.continuous_im.comp Units.continuous_val)
  exact (isOpen_lt h1 continuous_const).measurableSet.inter (isOpen_lt h2 continuous_const).measurableSet

theorem rsq_subset_halfU {δ : ℝ} (hδ : δ ≤ 1) : rsq δ ⊆ halfU := fun β hβ => by
  show 0 < (β : ℂ).re
  have := (abs_lt.1 hβ.1).1; linarith

theorem val_image_rsq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Units.val '' rsq δ = {z : ℂ | |z.re - 1| < δ ∧ |z.im| < δ} := by
  ext z
  constructor
  · rintro ⟨β, hβ, rfl⟩; exact hβ
  · intro hz
    have hz0 : z ≠ 0 := by
      rintro rfl; have := hz.1; simp at this; linarith
    exact ⟨Units.mk0 z hz0, hz, rfl⟩

theorem volume_square {δ : ℝ} (hδ : 0 < δ) :
    volume {z : ℂ | |z.re - 1| < δ ∧ |z.im| < δ} = ENNReal.ofReal ((2 * δ) ^ 2) := by
  have e : {z : ℂ | |z.re - 1| < δ ∧ |z.im| < δ} = Complex.measurableEquivRealProd ⁻¹' (Ioo (1 - δ) (1 + δ) ×ˢ Ioo (-δ) δ) := by
    ext z
    simp only [mem_setOf_eq, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Ioo, abs_lt]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩
  rw [e, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith)]
  congr 1; ring

theorem volU_rsq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : volU (rsq δ) = ENNReal.ofReal ((2 * δ) ^ 2) := by
  rw [volU_apply (measurableSet_rsq δ), val_image_rsq hδ hδ1, volume_square hδ]

theorem norm_bounds_rsq {δ : ℝ} (hδ1 : δ < 1) {β : ℂˣ} (hβ : β ∈ rsq δ) :
    1 - δ ≤ ‖(β : ℂ)‖ ∧ ‖(β : ℂ)‖ ≤ 1 + 2 * δ := by
  obtain ⟨h1, h2⟩ := hβ
  have hre := abs_lt.1 h1
  constructor
  · calc 1 - δ ≤ (β : ℂ).re := by linarith
      _ ≤ |(β : ℂ).re| := le_abs_self _
      _ ≤ ‖(β : ℂ)‖ := Complex.abs_re_le_norm _
  · calc ‖(β : ℂ)‖ ≤ |(β : ℂ).re| + |(β : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (1 + δ) + δ := by
          have : |(β : ℂ).re| ≤ 1 + δ := by rw [abs_le]; constructor <;> linarith
          linarith
      _ = 1 + 2 * δ := by ring

theorem lamU_rsq_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal ((1 - δ) ^ 6 * (2 * δ) ^ 2) ≤ lamU 4 (rsq δ) ∧
      lamU 4 (rsq δ) ≤ ENNReal.ofReal ((1 + 2 * δ) ^ 6 * (2 * δ) ^ 2) := by
  have hw : ∀ β ∈ rsq δ, ENNReal.ofReal ((1 - δ) ^ 6) ≤ wt (2 * (4 : ℕ) - 2) β ∧
      wt (2 * (4 : ℕ) - 2) β ≤ ENNReal.ofReal ((1 + 2 * δ) ^ 6) := fun β hβ => by
    obtain ⟨h1, h2⟩ := norm_bounds_rsq hδ1 hβ
    have e : wt (2 * (4 : ℕ) - 2) β = ENNReal.ofReal (‖(β : ℂ)‖ ^ 6) := by
      rw [wt, show (2 * ((4 : ℕ) : ℤ) - 2) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast, ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, coe_nnnorm, ENNReal.ofReal_pow (norm_nonneg _)]
    rw [e]
    exact ⟨ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) h1 6),
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith [norm_nonneg (β : ℂ)]) h2 6)⟩
  rw [lamU, withDensity_apply _ (measurableSet_rsq δ)]
  constructor
  · calc ENNReal.ofReal ((1 - δ) ^ 6 * (2 * δ) ^ 2) = ∫⁻ _ in rsq δ, ENNReal.ofReal ((1 - δ) ^ 6) ∂volU := by
          rw [setLIntegral_const, volU_rsq hδ hδ1, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := setLIntegral_mono' (measurableSet_rsq δ) fun β hβ => (hw β hβ).1
  · calc ∫⁻ β in rsq δ, wt (2 * (4 : ℕ) - 2) β ∂volU ≤ ∫⁻ _ in rsq δ, ENNReal.ofReal ((1 + 2 * δ) ^ 6) ∂volU :=
          setLIntegral_mono' (measurableSet_rsq δ) fun β hβ => (hw β hβ).2
      _ = _ := by rw [setLIntegral_const, volU_rsq hδ hδ1, ← ENNReal.ofReal_mul (by positivity)]

theorem tendsto_sq_div_lamU :
    Tendsto (fun δ => (2 * δ) ^ 2 / (lamU 4 (rsq δ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto (fun δ : ℝ => ((1 + 2 * δ) ^ 6)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun δ : ℝ => ((1 + 2 * δ) ^ 6)⁻¹) 0 :=
      ((continuous_const.add (continuous_const.mul continuous_id)).pow 6).continuousAt.inv₀ (by simp)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun δ : ℝ => ((1 - δ) ^ 6)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun δ : ℝ => ((1 - δ) ^ 6)⁻¹) 0 :=
      ((continuous_const.sub continuous_id).pow 6).continuousAt.inv₀ (by simp)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with δ (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    obtain ⟨-, h2⟩ := lamU_rsq_bounds hδ (by linarith)
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    obtain ⟨h1, -⟩ := lamU_rsq_bounds hδ (by linarith)
    have h1m : 0 < 1 - δ := by linarith
    have hlb : 0 < (1 - δ) ^ 6 * (2 * δ) ^ 2 := by positivity
    have hpos : 0 < (lamU 4 (rsq δ)).toReal := by
      rw [← ENNReal.toReal_ofReal hlb.le] at hlb
      exact lt_of_lt_of_le hlb ((ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).2 h1)
    have h2' : (lamU 4 (rsq δ)).toReal ≤ (1 + 2 * δ) ^ 6 * (2 * δ) ^ 2 := by
      rw [← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 + 2 * δ) ^ 6 * (2 * δ) ^ 2)]
      exact (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2 h2
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hpos]
    linarith
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with δ (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    obtain ⟨h1, h2⟩ := lamU_rsq_bounds hδ (by linarith)
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    have h1m : 0 < 1 - δ := by linarith
    have hlb : 0 < (1 - δ) ^ 6 * (2 * δ) ^ 2 := by positivity
    have h1' : (1 - δ) ^ 6 * (2 * δ) ^ 2 ≤ (lamU 4 (rsq δ)).toReal := by
      rw [← ENNReal.toReal_ofReal hlb.le]
      exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).2 h1
    rw [inv_eq_one_div, div_le_div_iff₀ (hlb.trans_le h1') (by positivity)]
    nlinarith

/-- **The cone density in a real chart of the complex sphere.** -/
theorem tendsto_nuC_div8 {Q : QuadForm ℂ 4} {A : ℝ → Set (SphC Q 1)} (hA : ∀ δ, MeasurableSet (A δ))
    {G : E8 → E8} {L : E8 →L[ℝ] E8} (hG : HasStrictFDerivAt G L 0)
    (himg : ∀ᶠ δ in 𝓝[>] (0 : ℝ), G '' ball 0 δ = eC '' (polC Q 1 '' (rsq δ ×ˢ A δ))) :
    Tendsto (fun δ => (nuC Q 1 (A δ)).toReal / (2 * δ) ^ 6) (𝓝[>] 0) (𝓝 |L.det|) := by
  have hT := tendsto_image_ball_div (volume : Measure E8) hG
  have hbdd : ∀ᶠ δ in 𝓝[>] (0 : ℝ), volume (G '' ball 0 δ) ≠ ⊤ := by
    have hc : ContinuousAt G 0 := hG.hasFDerivAt.continuousAt
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds (ball_mem_nhds (G 0) one_pos))
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hr)] with δ hδ
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (measure_ball_lt_top (x := G 0) (r := 1)))
    rintro _ ⟨z, hz, rfl⟩
    exact hsub (ball_subset_ball (le_of_lt hδ) hz)
  have hvol8 : ∀ δ : ℝ, 0 < δ → (volume (ball (0 : E8) δ)).toReal = (2 * δ) ^ 2 * (2 * δ) ^ 6 := fun δ hδ => by
    rw [volume_pi_ball _ hδ]
    simp only [Real.volume_pi_ball _ hδ, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    rw [← ENNReal.ofReal_pow (by positivity), ENNReal.toReal_ofReal (by positivity)]
    ring
  have key : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (nuC Q 1 (A δ)).toReal / (2 * δ) ^ 6 =
      (volume (G '' ball 0 δ)).toReal / (volume (ball (0 : E8) δ)).toReal *
        ((2 * δ) ^ 2 / (lamU 4 (rsq δ)).toReal) := by
    filter_upwards [himg, hbdd, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with δ hδ hfin (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    have hpol : volume (G '' ball 0 δ) = lamU 4 (rsq δ) * nuC Q 1 (A δ) := by
      rw [hδ, ← measurePreserving_eC.map_eq, measurableEmbedding_eC.map_apply,
        Set.preimage_image_eq _ eC_injective,
        ← MC_apply_of_subset one_ne_zero ((measurableSet_rsq δ).prod (hA δ))
          (prod_mono (rsq_subset_halfU (by linarith)) (subset_univ _)),
        MC_prod one_ne_zero (by norm_num) (hA δ) (measurableSet_rsq δ)]
    rw [hpol] at hfin ⊢
    obtain ⟨h1, h2⟩ := lamU_rsq_bounds hδ0 (by linarith)
    have hr0 : lamU 4 (rsq δ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by
      have : 0 < 1 - δ := by linarith
      positivity)) h1)
    have hrt : lamU 4 (rsq δ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    have hnt : nuC Q 1 (A δ) ≠ ⊤ := fun h => hfin (by rw [h, ENNReal.mul_top hr0])
    have hrpos : 0 < (lamU 4 (rsq δ)).toReal := ENNReal.toReal_pos hr0 hrt
    rw [ENNReal.toReal_mul, hvol8 δ hδ0]
    field_simp
  have h := hT.mul tendsto_sq_div_lamU
  rw [mul_one] at h
  exact h.congr' (key.mono fun δ hδ => hδ.symm)

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
