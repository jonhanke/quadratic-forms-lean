import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling

/-!
# The multiplicative Haar measure $|x|^{-1}dx$ on $R^\times$

**Generic, Mathlib-only hypotheses (upstreamable).** Let $R$ be a locally compact topological ring (not necessarily commutative) whose
unit group is open (`Units.val` an open embedding), $\nu$ a regular additive Haar measure on $R$, and
$\Delta = $ `distribHaarChar R` the modulus of $R^\times$ acting on $R$ ($\nu(u\cdot E) = \Delta(u)\nu(E)$).
If $\Delta$ is continuous, then

* **`unitsHaar ν`** $=\Delta(u)^{-1}\,d\nu(u)$ restricted to $R^\times$ (`unitsHaar_apply`) is a (left) Haar measure on
  $R^\times$ (**`isHaarMeasure_unitsHaar`**). This is Weil's $\omega = |x|^{-1}dx$ for $A = R$ (Weil 1982, §2.3
  [unverified page]): $dx/|x|$ on $\mathbb R^\times$, $2\,dx\,dy/|z|^2$ on $\mathbb C^\times$ (self-dual $dx$), and
  $|x|_v^{-1}dx_v$ on $F_v^\times$;
* **`unitsHaar_apply_of_forall_eq_one`**: on a set where $\Delta = 1$ (e.g. $\mathcal O_v^\times$) it is $\nu$;
* `continuous_distribHaarChar_of_eventually_eq_one`: $\Delta$ is continuous as soon as $\Delta = 1$ near $1$.
-/

open MeasureTheory Topology Set Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [MeasurableSpace R] [BorelSpace R]

/-- A homomorphism $R^\times\to\mathbb R_{\ge0}$ that is $1$ near $1$ is continuous. -/
theorem continuous_distribHaarChar_of_eventually_eq_one
    (h : ∀ᶠ u in 𝓝 (1 : Rˣ), distribHaarChar R u = 1) : Continuous (distribHaarChar R : Rˣ → ℝ≥0) := by
  refine continuous_of_continuousAt_one _ ?_
  refine (continuousAt_const (y := (1 : ℝ≥0))).congr ?_
  filter_upwards [h] with u hu using hu.symm

theorem distribHaarChar_ne_zero (g : Rˣ) : distribHaarChar R g ≠ 0 := by
  intro h0
  have : distribHaarChar R g * distribHaarChar R g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h0, zero_mul] at this
  exact zero_ne_one this

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ] [T2Space R]

variable (R) in
/-- **Weil's $\omega = |x|^{-1}dx$ on $R^\times$**: the measure $\Delta(u)^{-1}\,d\nu(u) = \Delta(u^{-1})\,d\nu(u)$ on the
units ($\nu$ restricted to $R^\times$ via `Units.val`). -/
def unitsHaar (ν : Measure R) : Measure Rˣ :=
  (ν.comap Units.val).withDensity fun u => (distribHaarChar R u⁻¹ : ℝ≥0∞)

variable (hval : IsOpenEmbedding (Units.val : Rˣ → R)) (hΔ : Continuous (distribHaarChar R : Rˣ → ℝ≥0))
  (ν : Measure R) [ν.IsAddHaarMeasure] [ν.Regular]

include hval in
theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : Rˣ → R) :=
  hval.measurableEmbedding

include hΔ in
theorem measurable_distribHaarChar_inv :
    Measurable fun u : Rˣ => (distribHaarChar R u⁻¹ : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp (hΔ.comp continuous_inv)).measurable

include hval hΔ in
theorem unitsHaar_apply {A : Set Rˣ} (hA : MeasurableSet A) :
    unitsHaar R ν A = ∫⁻ u in A, (distribHaarChar R u⁻¹ : ℝ≥0∞) ∂(ν.comap Units.val) :=
  withDensity_apply _ hA

include hval in
/-- $(u\cdot)_*(\nu|_{R^\times}) = \Delta(u)^{-1}\,\nu|_{R^\times}$. -/
theorem map_mul_comap_val (g : Rˣ) :
    (ν.comap Units.val).map (g * ·) = (distribHaarChar R g : ℝ≥0∞)⁻¹ • ν.comap Units.val := by
  have he := measurableEmbedding_val hval
  ext A hA
  rw [Measure.map_apply (measurable_const_mul g) hA, he.comap_apply, Measure.smul_apply, he.comap_apply]
  have himg : Units.val '' ((g * ·) ⁻¹' A) = (fun x : R => g • x) ⁻¹' (Units.val '' A) := by
    ext x
    simp only [mem_image, mem_preimage, Units.smul_def]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨g * u, hu, rfl⟩
    · rintro ⟨w, hw, hwx⟩
      refine ⟨g⁻¹ * w, by simpa using hw, ?_⟩
      rw [Units.val_mul, hwx, smul_eq_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hm : MeasurableSet (Units.val '' A) := he.measurableSet_image.mpr hA
  rw [himg, ← Measure.map_apply (continuous_const_smul g).measurable hm, map_smul_eq_distribHaarChar_inv' ν g,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (distribHaarChar_ne_zero g)]
  rfl

include hval hΔ in
/-- Left invariance of `unitsHaar`: the density transforms by $\Delta(g)^{-1}$, the measure by $\Delta(g)$. -/
theorem map_mul_unitsHaar (g : Rˣ) : (unitsHaar R ν).map (g * ·) = unitsHaar R ν := by
  have hf := measurable_distribHaarChar_inv hΔ
  have hg : Measurable (g * · : Rˣ → Rˣ) := measurable_const_mul g
  have hΔg0 : (distribHaarChar R g : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (distribHaarChar_ne_zero g)
  have hΔgT : (distribHaarChar R g : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  ext A hA
  rw [Measure.map_apply hg hA, unitsHaar_apply hval hΔ ν (hA.preimage hg), unitsHaar_apply hval hΔ ν hA]
  have hpt : ∀ u : Rˣ, (distribHaarChar R u⁻¹ : ℝ≥0∞) =
      (distribHaarChar R g : ℝ≥0∞) * (distribHaarChar R (g * u)⁻¹ : ℝ≥0∞) := by
    intro u
    rw [← ENNReal.coe_mul]
    congr 1
    rw [mul_inv_rev, map_mul, mul_comm (distribHaarChar R u⁻¹), ← mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      one_mul]
  conv_lhs => enter [2, u]; rw [hpt u]
  rw [lintegral_const_mul _ (f := fun u => (distribHaarChar R (g * u)⁻¹ : ℝ≥0∞)) (hf.comp hg), ← setLIntegral_map hA hf hg, map_mul_comap_val hval ν g,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hΔg0 hΔgT, one_mul]

include hval hΔ in
theorem isMulLeftInvariant_unitsHaar : (unitsHaar R ν).IsMulLeftInvariant :=
  ⟨fun g => map_mul_unitsHaar hval hΔ ν g⟩

include hval hΔ in
/-- **`unitsHaar ν` is a Haar measure on $R^\times$.** -/
@[kb "weil1982" "§2.3 [unverified page] (ω = |x|^{-1}dx on A^×)"]
theorem isHaarMeasure_unitsHaar : (unitsHaar R ν).IsHaarMeasure := by
  have he := measurableEmbedding_val hval
  have hf := measurable_distribHaarChar_inv hΔ
  have := isMulLeftInvariant_unitsHaar hval hΔ ν
  have : T2Space Rˣ := hval.isEmbedding.t2Space
  refine { lt_top_of_isCompact := fun K hK => ?_, toIsOpenPosMeasure := ⟨fun U hU hne => ?_⟩ }
  · obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun u : Rˣ => (distribHaarChar R u⁻¹ : ℝ))
      ((NNReal.continuous_coe.comp (hΔ.comp continuous_inv)).continuousOn)
    rw [unitsHaar_apply hval hΔ ν hK.measurableSet]
    have hbd : ∀ u ∈ K, (distribHaarChar R u⁻¹ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      intro u hu
      have := hM u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal this
    calc ∫⁻ u in K, (distribHaarChar R u⁻¹ : ℝ≥0∞) ∂(ν.comap Units.val)
        ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(ν.comap Units.val) :=
          setLIntegral_mono measurable_const fun u hu => hbd u hu
      _ = ENNReal.ofReal M * ν (Units.val '' K) := by
          rw [setLIntegral_const, he.comap_apply]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((hK.image Units.continuous_val).measure_lt_top)
  · rw [Ne, unitsHaar, withDensity_apply_eq_zero' hf.aemeasurable]
    have hne0 : {u : Rˣ | (distribHaarChar R u⁻¹ : ℝ≥0∞) ≠ 0} = univ := by
      ext u
      simp only [mem_ofPred_eq, mem_univ, iff_true, ne_eq, ENNReal.coe_eq_zero]
      exact distribHaarChar_ne_zero u⁻¹
    rw [hne0, univ_inter, he.comap_apply]
    exact ((hval.isOpenMap U hU).measure_ne_zero ν (hne.image _))

include hval hΔ in
/-- On a measurable set where $\Delta = 1$ (e.g. $\mathcal O_v^\times$), `unitsHaar ν` is $\nu$. -/
theorem unitsHaar_apply_of_forall_eq_one {A : Set Rˣ} (hA : MeasurableSet A)
    (h1 : ∀ u ∈ A, distribHaarChar R u = 1) : unitsHaar R ν A = ν (Units.val '' A) := by
  rw [unitsHaar_apply hval hΔ ν hA, setLIntegral_congr_fun hA (g := fun _ => 1) (fun u hu => by
    simp [map_inv, h1 u hu]), setLIntegral_const, one_mul, (measurableEmbedding_val hval).comap_apply]

end

end QuadFormsKB.Tamagawa.Measure.Weil
