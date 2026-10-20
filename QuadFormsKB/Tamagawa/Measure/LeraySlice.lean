import Mathlib

/-!
# Slices of invariant measures: the abstract part

The measure-theoretic core of the Leray (gauge-form) measures. A gauge form $\omega$ on a fibre $G = \Phi^{-1}(c)$
of a submersion $\Phi$ is characterized by $dX = \omega \wedge d\Phi$ near the fibre. When a second group $B$ acts
simply transitively on a neighbourhood of $c$, the chart $G \times B \to \Phi^{-1}(U)$, $(g, b) \mapsto gb$, turns this
into a statement about a measure $\tau$ on $G \times B$ (the pull-back of $dX$) which is

* invariant under left translation in $G$, and
* relatively invariant under right translation in $B$, with a character $\chi$ ($\chi(b) = |\det b|^n$ for $dX$).

We prove that such a $\tau$ is a product $\mu_G \otimes \kappa$ (`prod_eq_of_map_mul_left`, Haar uniqueness on $G$
slice by slice), and that $\kappa$ is unique up to a scalar among $\chi$-relatively right-invariant measures on $B$
(`eq_smul_of_map_mul_right`, Haar uniqueness on $B$ after tilting by $\chi$). Together (`slice_decomposition`):
$$\tau = (c\cdot\mu_G) \otimes \kappa_0$$
for any fixed $\chi$-relatively right-invariant comparison measure $\kappa_0$ that is positive on open sets. No
differential forms and no Jacobians are needed: the comparison measure is written down directly in the application
(`Tamagawa/Measure/LerayReal.lean`).

Weil 1982, §2.2 (gauge forms) and §2.4, Theorem 2.4.3, p. 25 (matching of the measures on $G$, $H$, $G/H$): the
fibration principle here is the special case where $G/H$ is replaced by a group $B$ acting simply transitively.
-/

open MeasureTheory Measure Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Leray

section Prod

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- **The slice measure** of $\tau$ on $G \times Y$ over a compact set $K_0 \subseteq G$: $F \mapsto \tau(K_0 \times F)$. -/
def sliceMeasure (K₀ : Set G) (τ : Measure (G × Y)) : Measure Y :=
  (τ.restrict (K₀ ×ˢ univ)).map Prod.snd

theorem sliceMeasure_apply (K₀ : Set G) (hK₀ : MeasurableSet K₀) (τ : Measure (G × Y)) {F : Set Y}
    (hF : MeasurableSet F) : sliceMeasure K₀ τ F = τ (K₀ ×ˢ F) := by
  rw [sliceMeasure, map_apply measurable_snd hF, restrict_apply (measurable_snd hF)]
  congr 1
  ext ⟨a, b⟩
  simp [and_comm]

/-- The marginal $A \mapsto \tau(A \times F)$ of $\tau$ on $G$. -/
def marginalFst (τ : Measure (G × Y)) (F : Set Y) : Measure G :=
  (τ.restrict (univ ×ˢ F)).map Prod.fst

theorem marginalFst_apply (τ : Measure (G × Y)) {F : Set Y} (hF : MeasurableSet F) {A : Set G}
    (hA : MeasurableSet A) : marginalFst τ F A = τ (A ×ˢ F) := by
  rw [marginalFst, map_apply measurable_fst hA, restrict_apply (measurable_fst hA)]
  congr 1
  ext ⟨a, b⟩
  simp

theorem marginalFst_isMulLeftInvariant (τ : Measure (G × Y))
    (hτ : ∀ g : G, τ.map (fun p : G × Y => (g * p.1, p.2)) = τ) {F : Set Y} (hF : MeasurableSet F) :
    (marginalFst τ F).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext A hA
  have hm : Measurable fun p : G × Y => (g * p.1, p.2) :=
    (measurable_const_mul g |>.comp measurable_fst).prodMk measurable_snd
  rw [map_apply (measurable_const_mul g) hA, marginalFst_apply τ hF (measurable_const_mul g hA),
    marginalFst_apply τ hF hA]
  conv_rhs => rw [← hτ g]
  rw [map_apply hm (hA.prod hF)]
  rfl

theorem marginalFst_isFiniteMeasureOnCompacts (τ : Measure (G × Y)) [IsFiniteMeasureOnCompacts τ]
    {F : Set Y} (hF : MeasurableSet F) {K : Set Y} (hK : IsCompact K) (hFK : F ⊆ K) :
    IsFiniteMeasureOnCompacts (marginalFst τ F) := by
  refine ⟨fun C hC => ?_⟩
  rw [marginalFst_apply τ hF hC.measurableSet]
  exact lt_of_le_of_lt (measure_mono (prod_mono le_rfl hFK)) (hC.prod hK).measure_lt_top

variable (K₀ : PositiveCompacts G)

/-- **Product structure of a left-invariant measure** (Haar uniqueness on $G$, slice by slice): if $\tau$ on
$G \times Y$ is finite on compact sets and invariant under $(g', y) \mapsto (gg', y)$, then
$\tau = \mu_{K_0} \otimes \kappa$ with $\mu_{K_0}$ the Haar measure normalized by $\mu(K_0) = 1$ and
$\kappa(F) = \tau(K_0 \times F)$. -/
theorem prod_eq_of_map_mul_left (τ : Measure (G × Y)) [IsFiniteMeasureOnCompacts τ]
    (hτ : ∀ g : G, τ.map (fun p : G × Y => (g * p.1, p.2)) = τ) :
    τ = (haarMeasure K₀).prod (sliceMeasure (K₀ : Set G) τ) := by
  have hK₀m : MeasurableSet (K₀ : Set G) := K₀.isCompact.measurableSet
  set μ := haarMeasure K₀
  set κ := sliceMeasure (K₀ : Set G) τ
  -- the formula on rectangles with F inside a compact set
  have hcpt : ∀ {F : Set Y} {K : Set Y}, MeasurableSet F → IsCompact K → F ⊆ K → ∀ A : Set G,
      MeasurableSet A → τ (A ×ˢ F) = μ A * κ F := by
    intro F K hF hK hFK A hA
    haveI := marginalFst_isMulLeftInvariant τ hτ hF
    haveI := marginalFst_isFiniteMeasureOnCompacts τ hF hK hFK
    have h := isMulLeftInvariant_eq_smul (marginalFst τ F) μ
    have h1 := congrArg (fun ν : Measure G => ν A) h
    have h2 := congrArg (fun ν : Measure G => ν K₀) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1 h2
    rw [marginalFst_apply τ hF hK₀m, haarMeasure_self, mul_one] at h2
    rw [marginalFst_apply τ hF hA] at h1
    rw [h1, ← h2, sliceMeasure_apply _ hK₀m τ hF, mul_comm]
  -- general rectangles, by exhaustion with compact sets
  have hrect : ∀ A : Set G, ∀ F : Set Y, MeasurableSet A → MeasurableSet F →
      τ (A ×ˢ F) = μ A * κ F := by
    intro A F hA hF
    set Fk : ℕ → Set Y := fun k => F ∩ compactCovering Y k
    have hmono : Monotone Fk := fun i j hij => inter_subset_inter_right _ (compactCovering_subset Y hij)
    have hU : (⋃ k, Fk k) = F := by
      simp only [Fk, ← inter_iUnion, iUnion_compactCovering, inter_univ]
    have hFkm : ∀ k, MeasurableSet (Fk k) := fun k =>
      hF.inter (isCompact_compactCovering Y k).measurableSet
    have e1 : τ (A ×ˢ F) = ⨆ k, τ (A ×ˢ Fk k) := by
      rw [← hU, prod_iUnion]
      exact Monotone.measure_iUnion (μ := τ) fun i j hij => prod_mono le_rfl (hmono hij)
    have e2 : κ F = ⨆ k, κ (Fk k) := by
      rw [← hU]; exact hmono.measure_iUnion
    rw [e1, e2, ENNReal.mul_iSup]
    refine iSup_congr fun k => hcpt (hFkm k) (isCompact_compactCovering Y k) inter_subset_right A hA
  haveI : IsFiniteMeasureOnCompacts κ := ⟨fun C hC => by
    rw [sliceMeasure_apply _ hK₀m τ hC.measurableSet]
    exact (K₀.isCompact.prod hC).measure_lt_top⟩
  exact (prod_eq fun A F hA hF => hrect A F hA hF).symm

end Prod

section Rel

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

/-- **Relative right invariance** of a measure $\kappa$ on $B$ with character $\chi$: $\kappa(Fb) = \chi(b)\kappa(F)$,
written as $(\cdot\, b)_*\kappa = \chi(b)^{-1}\kappa$. -/
def IsRelRightInvariant (χ : B →* ℝ≥0) (κ : Measure B) : Prop :=
  ∀ b : B, κ.map (· * b) = (((χ b)⁻¹ : ℝ≥0) : ℝ≥0∞) • κ

theorem char_ne_zero (χ : B →* ℝ≥0) (b : B) : χ b ≠ 0 := by
  have h : χ b * χ b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- The tilt $\chi^{-1}\kappa$. -/
def tilt (χ : B →* ℝ≥0) (κ : Measure B) : Measure B :=
  κ.withDensity fun b => (((χ b)⁻¹ : ℝ≥0) : ℝ≥0∞)

variable (χ : B →* ℝ≥0) (hχ : Continuous χ)
include hχ

theorem continuous_char_inv : Continuous fun b => (((χ b)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
  ENNReal.continuous_coe.comp (hχ.inv₀ fun b => char_ne_zero χ b)

theorem measurable_char_inv : Measurable fun b => (((χ b)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
  (continuous_char_inv χ hχ).measurable

theorem tilt_isMulRightInvariant {κ : Measure B} (hκ : IsRelRightInvariant χ κ) :
    (tilt χ κ).IsMulRightInvariant := by
  refine ⟨fun b => ?_⟩
  ext E hE
  have hmr : Measurable (· * b : B → B) := measurable_mul_const b
  rw [map_apply hmr hE, tilt, withDensity_apply _ (hmr hE), withDensity_apply _ hE]
  have h1 : ∫⁻ x in (· * b) ⁻¹' E, (((χ x)⁻¹ : ℝ≥0) : ℝ≥0∞) ∂κ
      = ∫⁻ y in E, (((χ (y * b⁻¹))⁻¹ : ℝ≥0) : ℝ≥0∞) ∂(κ.map (· * b)) := by
    rw [setLIntegral_map (f := fun y => (((χ (y * b⁻¹))⁻¹ : ℝ≥0) : ℝ≥0∞)) hE
      ((measurable_char_inv χ hχ).comp (measurable_mul_const b⁻¹)) hmr]
    simp only [mul_inv_cancel_right]
  rw [h1, hκ b, setLIntegral_smul_measure]
  have h2 : ∀ y, (((χ (y * b⁻¹))⁻¹ : ℝ≥0) : ℝ≥0∞) = (χ b : ℝ≥0∞) * (((χ y)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    intro y
    rw [← ENNReal.coe_mul, map_mul, map_inv, mul_inv, inv_inv, mul_comm]
  simp_rw [h2]
  rw [lintegral_const_mul _ (measurable_char_inv χ hχ), smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    inv_mul_cancel₀ (char_ne_zero χ b), ENNReal.coe_one, one_mul]

theorem tilt_isFiniteMeasureOnCompacts {κ : Measure B} [IsFiniteMeasureOnCompacts κ] :
    IsFiniteMeasureOnCompacts (tilt χ κ) := by
  refine ⟨fun C hC => ?_⟩
  rw [tilt, withDensity_apply _ hC.measurableSet]
  have hc : Continuous fun b => (((χ b)⁻¹ : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (hχ.inv₀ fun b => char_ne_zero χ b)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  calc ∫⁻ x in C, (((χ x)⁻¹ : ℝ≥0) : ℝ≥0∞) ∂κ ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂κ := by
        refine setLIntegral_mono measurable_const fun x hx => ?_
        have := hM x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal this
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem tilt_isOpenPosMeasure {κ : Measure B} [IsOpenPosMeasure κ] : IsOpenPosMeasure (tilt χ κ) := by
  refine ⟨fun U hU hne h0 => ?_⟩
  rw [tilt, withDensity_apply _ hU.measurableSet] at h0
  have hpos : ∀ x, (0 : ℝ≥0∞) < (((χ x)⁻¹ : ℝ≥0) : ℝ≥0∞) := fun x => by
    rw [ENNReal.coe_pos]; exact inv_pos.mpr (pos_iff_ne_zero.mpr (char_ne_zero χ x))
  have h0' := (withDensity_apply_eq_zero' (measurable_char_inv χ hχ).aemeasurable).mp
    ((withDensity_apply _ hU.measurableSet).trans h0)
  have hset : {x | (((χ x)⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0} ∩ U = U := by
    ext x; simp only [mem_inter_iff, mem_setOf_eq, and_iff_right_iff_imp]; exact fun _ => (hpos x).ne'
  have : κ U = 0 := by rwa [hset] at h0'
  exact hU.measure_ne_zero κ hne this

theorem withDensity_tilt (κ : Measure B) : (tilt χ κ).withDensity (fun b => (χ b : ℝ≥0∞)) = κ := by
  have hm : Measurable fun b => (χ b : ℝ≥0∞) := (ENNReal.continuous_coe.comp hχ).measurable
  rw [tilt, ← withDensity_mul _ (measurable_char_inv χ hχ) hm]
  have : ((fun b => (((χ b)⁻¹ : ℝ≥0) : ℝ≥0∞)) * fun b => (χ b : ℝ≥0∞)) = fun _ => 1 := by
    funext b
    simp only [Pi.mul_apply]
    rw [← ENNReal.coe_mul, inv_mul_cancel₀ (char_ne_zero χ b), ENNReal.coe_one]
  rw [this]
  exact withDensity_one

/-- **Uniqueness of relatively right-invariant measures** (Haar uniqueness on $B$ after tilting by $\chi^{-1}$):
if $\kappa$ and $\kappa_0$ are both $\chi$-relatively right-invariant and finite on compact sets, and $\kappa_0$ is
positive on open sets, then $\kappa = c\,\kappa_0$ for some $c \in [0, \infty)$. -/
theorem eq_smul_of_map_mul_right {κ κ₀ : Measure B} [IsFiniteMeasureOnCompacts κ] [IsFiniteMeasureOnCompacts κ₀]
    [IsOpenPosMeasure κ₀] (hκ : IsRelRightInvariant χ κ) (hκ₀ : IsRelRightInvariant χ κ₀) :
    ∃ c : ℝ≥0, κ = (c : ℝ≥0∞) • κ₀ := by
  haveI := tilt_isMulRightInvariant χ hχ hκ
  haveI := tilt_isMulRightInvariant χ hχ hκ₀
  haveI := tilt_isFiniteMeasureOnCompacts χ hχ (κ := κ)
  haveI := tilt_isFiniteMeasureOnCompacts χ hχ (κ := κ₀)
  haveI := tilt_isOpenPosMeasure χ hχ (κ := κ₀)
  haveI : IsFiniteMeasureOnCompacts (tilt χ κ).inv := by
    refine ⟨fun C hC => ?_⟩
    rw [inv_apply]
    exact (hC.inv).measure_lt_top
  haveI : IsOpenPosMeasure (tilt χ κ₀).inv := by
    refine ⟨fun U hU hne => ?_⟩
    rw [inv_apply]
    exact hU.inv.measure_ne_zero _ (by simpa using hne)
  haveI : IsFiniteMeasureOnCompacts (tilt χ κ₀).inv := by
    refine ⟨fun C hC => ?_⟩
    rw [inv_apply]
    exact (hC.inv).measure_lt_top
  haveI : (tilt χ κ₀).inv.IsHaarMeasure := ⟨⟩
  have h := isMulLeftInvariant_eq_smul (tilt χ κ).inv (tilt χ κ₀).inv
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, tilt χ κ = c • tilt χ κ₀ := by
    refine ⟨haarScalarFactor (tilt χ κ).inv (tilt χ κ₀).inv, ?_⟩
    have hinv : ∀ (c : ℝ≥0) (ν : Measure B), (c • ν).inv = c • ν.inv := fun c ν => by
      rw [Measure.inv, Measure.inv, ENNReal.smul_def, ENNReal.smul_def, Measure.map_smul]; exact measurable_inv.aemeasurable
    have := congrArg Measure.inv h
    rwa [Measure.inv_inv, hinv, Measure.inv_inv] at this
  refine ⟨c, ?_⟩
  rw [← withDensity_tilt χ hχ κ, hc]
  conv_rhs => rw [← withDensity_tilt χ hχ κ₀]
  rw [ENNReal.smul_def, withDensity_smul_measure]

end Rel

section WithDensity

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
variable (χ₁ χ₂ : B →* ℝ≥0) (hχ₂ : Continuous χ₂)
include hχ₂

theorem measurable_char : Measurable fun b => (χ₂ b : ℝ≥0∞) := (ENNReal.continuous_coe.comp hχ₂).measurable

/-- **Changing the character by a density**: if $\kappa$ is $\chi_1$-relatively right-invariant, then
$\chi_2\kappa$ is $\chi_1\chi_2$-relatively right-invariant. -/
theorem isRelRightInvariant_withDensity {κ : Measure B} (hκ : IsRelRightInvariant χ₁ κ) :
    IsRelRightInvariant (χ₁ * χ₂) (κ.withDensity fun b => (χ₂ b : ℝ≥0∞)) := by
  intro b
  ext E hE
  have hmr : Measurable (· * b : B → B) := measurable_mul_const b
  rw [map_apply hmr hE, withDensity_apply _ (hmr hE), Measure.smul_apply, withDensity_apply _ hE]
  have h1 : ∫⁻ x in (· * b) ⁻¹' E, (χ₂ x : ℝ≥0∞) ∂κ
      = ∫⁻ y in E, (χ₂ (y * b⁻¹) : ℝ≥0∞) ∂(κ.map (· * b)) := by
    rw [setLIntegral_map (f := fun y => (χ₂ (y * b⁻¹) : ℝ≥0∞)) hE
      ((measurable_char χ₂ hχ₂).comp (measurable_mul_const b⁻¹)) hmr]
    simp only [mul_inv_cancel_right]
  rw [h1, hκ b, setLIntegral_smul_measure]
  have h2 : ∀ y, (χ₂ (y * b⁻¹) : ℝ≥0∞) = (((χ₂ b)⁻¹ : ℝ≥0) : ℝ≥0∞) * (χ₂ y : ℝ≥0∞) := by
    intro y
    rw [← ENNReal.coe_mul, map_mul, map_inv, mul_comm]
  simp_rw [h2]
  rw [lintegral_const_mul _ (measurable_char χ₂ hχ₂), smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← ENNReal.coe_mul, MonoidHom.mul_apply, mul_inv]

theorem withDensity_char_isFiniteMeasureOnCompacts {κ : Measure B} [IsFiniteMeasureOnCompacts κ] :
    IsFiniteMeasureOnCompacts (κ.withDensity fun b => (χ₂ b : ℝ≥0∞)) := by
  refine ⟨fun C hC => ?_⟩
  rw [withDensity_apply _ hC.measurableSet]
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (NNReal.continuous_coe.comp hχ₂).continuousOn
  calc ∫⁻ x in C, (χ₂ x : ℝ≥0∞) ∂κ ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂κ := by
        refine setLIntegral_mono measurable_const fun x hx => ?_
        have := hM x hx
        rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal this
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem withDensity_char_isOpenPosMeasure {κ : Measure B} [IsOpenPosMeasure κ] :
    IsOpenPosMeasure (κ.withDensity fun b => (χ₂ b : ℝ≥0∞)) := by
  refine ⟨fun U hU hne h0 => ?_⟩
  have h0' := (withDensity_apply_eq_zero' (measurable_char χ₂ hχ₂).aemeasurable).mp h0
  have hset : {x | (χ₂ x : ℝ≥0∞) ≠ 0} ∩ U = U := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, and_iff_right_iff_imp, ne_eq, ENNReal.coe_eq_zero]
    exact fun _ => char_ne_zero χ₂ x
  rw [hset] at h0'
  exact hU.measure_ne_zero κ hne h0'

end WithDensity

section Slice

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

/-- **The slice decomposition** (fibration principle for a simply transitive slice group): let $\tau$ on $G \times B$
be finite on compact sets, invariant under left translation in $G$, and $\chi$-relatively invariant under right
translation in $B$; let $\kappa_0$ on $B$ be $\chi$-relatively right-invariant, finite on compacts and positive on
opens. Then $\tau = (c\,\mu_{K_0}) \otimes \kappa_0$ for a constant $c \in [0, \infty)$. -/
theorem slice_decomposition (K₀ : PositiveCompacts G) (χ : B →* ℝ≥0) (hχ : Continuous χ)
    (τ : Measure (G × B)) [IsFiniteMeasureOnCompacts τ]
    (hτG : ∀ g : G, τ.map (fun p : G × B => (g * p.1, p.2)) = τ)
    (hτB : ∀ b : B, τ.map (fun p : G × B => (p.1, p.2 * b)) = (((χ b)⁻¹ : ℝ≥0) : ℝ≥0∞) • τ)
    (κ₀ : Measure B) [IsFiniteMeasureOnCompacts κ₀] [IsOpenPosMeasure κ₀] (hκ₀ : IsRelRightInvariant χ κ₀) :
    ∃ c : ℝ≥0, τ = ((c : ℝ≥0∞) • haarMeasure K₀).prod κ₀ := by
  have hK₀m : MeasurableSet (K₀ : Set G) := K₀.isCompact.measurableSet
  set κ := sliceMeasure (K₀ : Set G) τ with hκdef
  have hprod := prod_eq_of_map_mul_left K₀ τ hτG
  haveI : IsFiniteMeasureOnCompacts κ := ⟨fun C hC => by
    rw [hκdef, sliceMeasure_apply _ hK₀m τ hC.measurableSet]
    exact (K₀.isCompact.prod hC).measure_lt_top⟩
  have hκ : IsRelRightInvariant χ κ := by
    intro b
    ext F hF
    have hmr : Measurable (· * b : B → B) := measurable_mul_const b
    have hm : Measurable fun p : G × B => (p.1, p.2 * b) := measurable_fst.prodMk (hmr.comp measurable_snd)
    rw [map_apply hmr hF, Measure.smul_apply, smul_eq_mul, hκdef, sliceMeasure_apply _ hK₀m τ (hmr hF),
      sliceMeasure_apply _ hK₀m τ hF]
    have := congrArg (fun ν : Measure (G × B) => ν ((K₀ : Set G) ×ˢ F)) (hτB b)
    simp only [Measure.smul_apply, smul_eq_mul] at this
    rw [map_apply hm (hK₀m.prod hF)] at this
    rw [← this]
    rfl
  obtain ⟨c, hc⟩ := eq_smul_of_map_mul_right χ hχ hκ hκ₀
  refine ⟨c, ?_⟩
  rw [hprod, show sliceMeasure (K₀ : Set G) τ = κ from rfl, hc, prod_smul_right, prod_smul_left]

end Slice

end QuadFormsKB.Tamagawa.Measure.Leray
