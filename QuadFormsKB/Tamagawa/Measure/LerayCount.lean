import Mathlib

/-!
# Pulling back a measure along a locally injective map by counting fibres

The abstract tool for the Leray measures at the **complex places**. Over $\mathbb C$ no slice group acts simply
transitively near $c_Q$: the chart $(g, b) \mapsto gb$ from $SO(Q)(\mathbb C) \times B$ is $|C|$-to-one, with
$C = SO(Q)(\mathbb C) \cap B$ a finite group of signs, so the pull-back `Measure.comap` (which needs an injective map)
is useless. We replace it by the **fibre-counting pull-back** (`fibreCount`)
$$m^\#\nu(S) = \int_Z \#\bigl(S \cap m^{-1}(z)\bigr)\,d\nu(z)$$
of a measure $\nu$ on $Z$ along a continuous, locally injective map $m : Y \to Z$ from a Polish space. It is a
measure (`Measure.bind` with the counting measures on the fibres), and

* on a measurable set $S$ on which $m$ is injective it is the old pull-back: $m^\#\nu(S) = \nu(m(S))$
  (`fibreCount_apply_of_injOn`, `map_restrict_fibreCount`);
* it is natural: if $m \circ T = T' \circ m$ for measurable equivalences $T$, $T'$ then
  $T_*(m^\#\nu) = m^\#(T'_*\nu)$ (`fibreCount_map`), so invariance properties of $\nu$ pass to $m^\#\nu$ with no
  injectivity at all;
* it is finite on compact sets and positive on open sets when $\nu$ is, and $m$ is an open map
  (`fibreCount_isFiniteMeasureOnCompacts`, `fibreCount_isOpenPosMeasure`).

So the abstract slice decomposition (`Leray.slice_decomposition`, global Haar uniqueness on the slice group) applies
verbatim at the complex places; no local Haar uniqueness is needed. The section ends with an averaging lemma over
shrinking closed balls for any measure (`tendsto_avg_closedBall`).
-/

open MeasureTheory Measure Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Leray

section FibreCount

variable {Y Z : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]

/-- **Local injectivity**: every point has an open neighbourhood on which $m$ is injective. -/
def IsLocInj (m : Y → Z) : Prop := ∀ y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ InjOn m U

/-- A locally injective map from a second countable space has a countable measurable partition into pieces of
injectivity. -/
theorem exists_partition_injOn {m : Y → Z} (hloc : IsLocInj m) :
    ∃ U : ℕ → Set Y, (∀ k, MeasurableSet (U k)) ∧ (∀ k, InjOn m (U k)) ∧ Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      (⋃ k, U k) = univ := by
  choose O hO hyO hinj using hloc
  obtain ⟨s, hs, hcov⟩ := TopologicalSpace.countable_cover_nhds (f := O) fun y => (hO y).mem_nhds (hyO y)
  rcases s.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun _ => injOn_empty _,
      fun _ _ _ => Set.empty_disjoint _, ?_⟩
    rw [← hcov]; simp
  · obtain ⟨f, rfl⟩ := hs.exists_eq_range hne
    refine ⟨disjointed fun k => O (f k), fun k => MeasurableSet.disjointed (fun k => (hO (f k)).measurableSet) k,
      fun k => (hinj (f k)).mono (disjointed_subset _ k), disjoint_disjointed _, ?_⟩
    rw [iUnion_disjointed, ← hcov]
    simp

variable {m : Y → Z}

theorem count_inter_fibre_of_injOn {s : Set Y} (hinj : InjOn m s) (z : Z) :
    count (s ∩ m ⁻¹' {z}) = (m '' s).indicator 1 z := by
  by_cases hz : z ∈ m '' s
  · obtain ⟨y, hy, rfl⟩ := hz
    have : s ∩ m ⁻¹' {m y} = {y} := by
      ext y'
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact hinj h1 hy h2
      · rintro rfl; exact ⟨hy, rfl⟩
    rw [this, count_singleton, indicator_of_mem (mem_image_of_mem m hy)]
    rfl
  · have : s ∩ m ⁻¹' {z} = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro h1 rfl
      exact hz ⟨y, h1, rfl⟩
    rw [this, measure_empty, indicator_of_notMem hz]

variable (hm : Continuous m) (hloc : IsLocInj m)
include hm hloc

theorem measurable_count_fibre {s : Set Y} (hs : MeasurableSet s) :
    Measurable fun z => count (s ∩ m ⁻¹' {z}) := by
  obtain ⟨U, hUm, hUi, hUd, hUc⟩ := exists_partition_injOn hloc
  have h : ∀ z, count (s ∩ m ⁻¹' {z}) = ∑' k, (m '' (s ∩ U k)).indicator 1 z := by
    intro z
    have hsplit : s ∩ m ⁻¹' {z} = ⋃ k, (s ∩ U k) ∩ m ⁻¹' {z} := by
      rw [← iUnion_inter, ← inter_iUnion, hUc, inter_univ]
    rw [hsplit, measure_iUnion]
    · congr 1
      funext k
      exact count_inter_fibre_of_injOn ((hUi k).mono inter_subset_right) z
    · intro i j hij
      exact Disjoint.mono (fun x hx => hx.1.2) (fun x hx => hx.1.2) (hUd hij)
    · exact fun k => (hs.inter (hUm k)).inter (hm.measurable (measurableSet_singleton z))
  simp_rw [h]
  exact Measurable.tsum fun k => measurable_one.indicator
    ((hs.inter (hUm k)).image_of_continuousOn_injOn hm.continuousOn ((hUi k).mono inter_subset_right))

theorem measurable_fibreKernel : Measurable fun z : Z => (count : Measure Y).restrict (m ⁻¹' {z}) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [restrict_apply hs]
  exact measurable_count_fibre hm hloc hs

omit hm hloc in
/-- **The fibre-counting pull-back** $m^\#\nu(S) = \int \#(S \cap m^{-1}(z))\,d\nu(z)$ of a measure $\nu$ on $Z$
along $m : Y \to Z$ (`fibreCount_apply`; meaningful for continuous locally injective $m$). -/
def fibreCount (m : Y → Z) (ν : Measure Z) : Measure Y :=
  ν.bind fun z => (count : Measure Y).restrict (m ⁻¹' {z})

variable (ν : Measure Z)

theorem fibreCount_apply {s : Set Y} (hs : MeasurableSet s) :
    fibreCount m ν s = ∫⁻ z, count (s ∩ m ⁻¹' {z}) ∂ν := by
  rw [fibreCount, bind_apply hs (measurable_fibreKernel hm hloc).aemeasurable]
  simp_rw [restrict_apply hs]

/-- **On a set of injectivity the fibre-counting pull-back is the pull-back**: $m^\#\nu(S) = \nu(m(S))$. -/
theorem fibreCount_apply_of_injOn {s : Set Y} (hs : MeasurableSet s) (hinj : InjOn m s) :
    fibreCount m ν s = ν (m '' s) := by
  rw [fibreCount_apply hm hloc ν hs]
  simp_rw [count_inter_fibre_of_injOn hinj]
  exact lintegral_indicator_one (hs.image_of_continuousOn_injOn hm.continuousOn hinj)

/-- **Change of variables on a set of injectivity**: $m_*(m^\#\nu|_S) = \nu|_{m(S)}$. -/
theorem map_restrict_fibreCount {s : Set Y} (hs : MeasurableSet s) (hinj : InjOn m s) :
    ((fibreCount m ν).restrict s).map m = ν.restrict (m '' s) := by
  ext A hA
  rw [map_apply hm.measurable hA, restrict_apply (hm.measurable hA), restrict_apply hA,
    fibreCount_apply_of_injOn hm hloc ν ((hm.measurable hA).inter hs) (hinj.mono inter_subset_right)]
  congr 1
  ext z
  constructor
  · rintro ⟨y, ⟨hyA, hys⟩, rfl⟩; exact ⟨hyA, y, hys, rfl⟩
  · rintro ⟨hzA, y, hys, rfl⟩; exact ⟨y, ⟨hzA, hys⟩, rfl⟩

/-- **Naturality**: if $m \circ T = T' \circ m$ then $T_*(m^\#\nu) = m^\#(T'_*\nu)$. -/
theorem fibreCount_map (T : Y ≃ᵐ Y) (T' : Z ≃ᵐ Z) (hT : ∀ y, m (T y) = T' (m y)) :
    (fibreCount m ν).map T = fibreCount m (ν.map T') := by
  ext s hs
  rw [map_apply T.measurable hs, fibreCount_apply hm hloc ν (T.measurable hs), fibreCount_apply hm hloc _ hs,
    lintegral_map_equiv]
  refine lintegral_congr fun z => ?_
  have : T ⁻¹' s ∩ m ⁻¹' {z} = T ⁻¹' (s ∩ m ⁻¹' {T' z}) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hT]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨h1, rfl⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, T'.injective h2⟩
  have hA : MeasurableSet (s ∩ m ⁻¹' {T' z}) := hs.inter (hm.measurable (measurableSet_singleton _))
  rw [this, count_apply (T.measurable hA), count_apply hA, encard_preimage_of_bijective T.bijective]

theorem fibreCount_smul (c : ℝ≥0∞) : fibreCount m (c • ν) = c • fibreCount m ν := by
  ext s hs
  rw [fibreCount_apply hm hloc _ hs, Measure.smul_apply, fibreCount_apply hm hloc _ hs, lintegral_smul_measure]

/-- $m^\#\nu$ is finite on compact sets (finitely many pieces of injectivity cover a compact set). -/
theorem fibreCount_isFiniteMeasureOnCompacts [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (fibreCount m ν) := by
  refine ⟨fun K hK => ?_⟩
  have hloc' := hloc
  choose O hO hyO hinj using hloc'
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover O fun y _ => (hO y).mem_nhds (hyO y)
  calc fibreCount m ν K ≤ fibreCount m ν (⋃ y ∈ t, K ∩ O y) := measure_mono fun x hx => by
        obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcov hx)
        exact mem_iUnion₂.mpr ⟨y, hy, hx, hxy⟩
    _ ≤ ∑ y ∈ t, fibreCount m ν (K ∩ O y) := measure_biUnion_finset_le _ _
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun y _ => by
        rw [fibreCount_apply_of_injOn hm hloc ν (hK.measurableSet.inter (hO y).measurableSet)
          ((hinj y).mono inter_subset_right)]
        exact lt_of_le_of_lt (measure_mono (image_mono inter_subset_left)) (hK.image hm).measure_lt_top

/-- $m^\#\nu$ is positive on open sets when $\nu$ is and $m$ is an open map. -/
theorem fibreCount_isOpenPosMeasure [IsOpenPosMeasure ν] (hopen : IsOpenMap m) :
    IsOpenPosMeasure (fibreCount m ν) := by
  refine ⟨fun W hW hne h0 => ?_⟩
  obtain ⟨y, hy⟩ := hne
  obtain ⟨O, hO, hyO, hinj⟩ := hloc y
  have h1 := measure_mono_null (inter_subset_left : W ∩ O ⊆ W) h0
  rw [fibreCount_apply_of_injOn hm hloc ν (hW.inter hO).measurableSet (hinj.mono inter_subset_right)] at h1
  exact (hopen _ (hW.inter hO)).measure_ne_zero ν ⟨m y, y, ⟨hy, hyO⟩, rfl⟩ h1

end FibreCount

/-! ### Averages over shrinking balls -/

/-- **Averages over shrinking closed balls**: if $G \ge 0$ is continuous on an open $U \ni c_0$ and $\mu$ gives the
closed balls about $c_0$ finite positive mass, then
$\frac{1}{\mu(\bar B_\varepsilon)}\int_{\bar B_\varepsilon}G\,d\mu \to G(c_0)$ as $\varepsilon \to 0^+$. -/
theorem tendsto_avg_closedBall {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) {c₀ : E} (hpos : ∀ ε > 0, 0 < μ (Metric.closedBall c₀ ε))
    (hfin : ∀ ε, μ (Metric.closedBall c₀ ε) ≠ ∞) {U : Set E} (hU : IsOpen U) (hc : c₀ ∈ U) {G : E → ℝ}
    (hGc : ContinuousOn G U) (hG0 : ∀ t ∈ U, 0 ≤ G t) :
    Tendsto (fun ε => (∫⁻ t in Metric.closedBall c₀ ε, ENNReal.ofReal (G t) ∂μ).toReal /
      (μ (Metric.closedBall c₀ ε)).toReal) (𝓝[>] 0) (𝓝 (G c₀)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  have hcont : ContinuousAt G c₀ := hGc.continuousAt (hU.mem_nhds hc)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hcont (η / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.isOpen_iff.mp hU c₀ hc
  refine ⟨min δ1 δ2, by positivity, fun {ε} hε hεd => ?_⟩
  have hε : 0 < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hε] at hεd
  set B := Metric.closedBall c₀ ε
  have hsub : ∀ t ∈ B, dist t c₀ < min δ1 δ2 := fun t ht => lt_of_le_of_lt (Metric.mem_closedBall.mp ht) hεd
  have hU' : ∀ t ∈ B, t ∈ U := fun t ht =>
    h2 (Metric.mem_ball.mpr ((hsub t ht).trans_le (min_le_right _ _)))
  have hclose : ∀ t ∈ B, |G t - G c₀| < η / 2 := fun t ht => by
    rw [← Real.dist_eq]; exact h1 ((hsub t ht).trans_le (min_le_left _ _))
  have hmeasB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hV : μ B ≠ ∞ := hfin ε
  have hV0 : 0 < (μ B).toReal := ENNReal.toReal_pos (hpos ε hε).ne' hV
  have hG0' := hG0 c₀ hc
  have hup : ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ ≤ ENNReal.ofReal (G c₀ + η / 2) * μ B := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).2])
  have hlo : ENNReal.ofReal (G c₀ - η / 2) * μ B ≤ ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).1])
  have hfin' : ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hup' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hlo' := ENNReal.toReal_mono hfin' hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hup'
  rw [ENNReal.toReal_mul] at hlo'
  have hlo'' : (G c₀ - η / 2) * (μ B).toReal ≤ (∫⁻ t in B, ENNReal.ofReal (G t) ∂μ).toReal :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _) hV0.le) hlo'
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hV0]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hV0]; nlinarith

end QuadFormsKB.Tamagawa.Measure.Leray
