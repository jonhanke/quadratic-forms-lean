/-
# Cassels, Appendix B, §2, Lemma 2.1 for $D > 0$

Proof of the named statement `Lemma21Pos` (hyperbolic sector).
-/
import QuadFormsKB.Literature.Cassels.AppB.Sec2Lemmas

open Filter Topology Matrix MeasureTheory
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

namespace Lemma21Pos530

open QuadFormsKB.Binary

/-! ### Geometry of the hyperbolic sector in the coordinates $(u, v)$ -/

section Geo

/-- Helper: **the sector cone** $\{y = (u, v) : 0 < v \le u < \varepsilon^2 v\}$ of $\mathbb R^2$ (the half-open sector between
the ray $u = v$ and its image under $(u, v) \mapsto (\varepsilon u, \varepsilon^{-1} v)$). Argument `ε`: the unit. -/
def sectorCone (ε : ℝ) : Set (Fin 2 → ℝ) := {y | 0 < y 1 ∧ y 1 ≤ y 0 ∧ y 0 < ε ^ 2 * y 1}

/-- Helper: **the hyperbolic form** $H(u, v) = uv$. -/
def hyp (y : Fin 2 → ℝ) : ℝ := y 0 * y 1

/-- Helper: **the sector cut by the hyperbola** $\{y \in \text{sectorCone}\ \varepsilon : uv \le 1\}$. -/
def sectorSet (ε : ℝ) : Set (Fin 2 → ℝ) := {y | y ∈ sectorCone ε ∧ hyp y ≤ 1}

theorem sectorCone_smul {ε : ℝ} {x : Fin 2 → ℝ} {r : ℝ} (hx : x ∈ sectorCone ε) (hr : 0 < r) :
    r • x ∈ sectorCone ε := by
  obtain ⟨h1, h2, h3⟩ := hx
  simp only [sectorCone, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
  refine ⟨by positivity, mul_le_mul_of_nonneg_left h2 hr.le, ?_⟩
  calc r * x 0 < r * (ε ^ 2 * x 1) := mul_lt_mul_of_pos_left h3 hr
    _ = ε ^ 2 * (r * x 1) := by ring

theorem hyp_smul (x : Fin 2 → ℝ) {r : ℝ} (_hr : 0 ≤ r) :
    hyp (r • x) = r ^ Fintype.card (Fin 2) * hyp x := by
  simp only [hyp, Pi.smul_apply, smul_eq_mul, Fintype.card_fin]
  ring

theorem sectorSet_bounded {ε : ℝ} (hε : 1 < ε) : Bornology.IsBounded (sectorSet ε) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨ε ^ 2 + 1, fun y hy => ?_⟩
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hy
  simp only [hyp] at h4
  have hε2 : 1 < ε ^ 2 := by nlinarith
  have hy1 : y 1 ≤ 1 := by nlinarith
  have hy0 : y 0 ≤ ε ^ 2 := by nlinarith
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith)]; linarith
  · simp only [Fin.mk_one, Real.norm_eq_abs]
    rw [abs_of_pos h1]; nlinarith

theorem sectorSet_measurable (ε : ℝ) : MeasurableSet (sectorSet ε) := by
  have h0 : Measurable (fun y : Fin 2 → ℝ => y 0) := measurable_pi_apply 0
  have h1 : Measurable (fun y : Fin 2 → ℝ => y 1) := measurable_pi_apply 1
  have : sectorSet ε = {y | 0 < y 1} ∩ ({y | y 1 ≤ y 0} ∩ ({y | y 0 < ε ^ 2 * y 1} ∩ {y | y 0 * y 1 ≤ 1})) := by
    ext y; simp [sectorSet, sectorCone, hyp, and_assoc]
  rw [this]
  refine (measurableSet_lt measurable_const h1).inter ((measurableSet_le h1 h0).inter
    ((measurableSet_lt h0 (measurable_const.mul h1)).inter (measurableSet_le (h0.mul h1) measurable_const)))

/-- Helper: a measurable set of $\mathbb R^2$ all of whose vertical lines $\{x\} \times \mathbb R$ meet it in at most one
point is null. -/
theorem null_of_slices {s : Set (Fin 2 → ℝ)} (hs : MeasurableSet s)
    (h : ∀ x : ℝ, {y : ℝ | ![x, y] ∈ s}.Subsingleton) : volume s = 0 := by
  have hpres := volume_preserving_finTwoArrow ℝ
  set e := MeasurableEquiv.finTwoArrow (α := ℝ) with he
  set t : Set (ℝ × ℝ) := e.symm ⁻¹' s with ht
  have hst : s = e ⁻¹' t := by
    ext y
    have hy : (![y 0, y 1] : Fin 2 → ℝ) = y := by ext i; fin_cases i <;> rfl
    simp [ht, he, hy]
  have hmt : MeasurableSet t := e.symm.measurable hs
  rw [hst, hpres.measure_preimage_equiv]
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmt]
  refine Filter.Eventually.of_forall (fun x => ?_)
  refine Set.Subsingleton.measure_zero ?_ _
  intro y hy z hz
  exact h x (by simpa [ht, he] using hy) (by simpa [ht, he] using hz)

theorem sectorSet_frontier_null {ε : ℝ} (hε : 1 < ε) : volume (frontier (sectorSet ε)) = 0 := by
  have hε0 : ε ^ 2 ≠ 0 := by positivity
  have hcont0 : Continuous (fun y : Fin 2 → ℝ => y 0) := continuous_apply 0
  have hcont1 : Continuous (fun y : Fin 2 → ℝ => y 1) := continuous_apply 1
  -- the four null sets
  set Z1 : Set (Fin 2 → ℝ) := {y | y 1 = 0} with hZ1
  set Z2 : Set (Fin 2 → ℝ) := {y | y 1 = y 0} with hZ2
  set Z3 : Set (Fin 2 → ℝ) := {y | y 0 = ε ^ 2 * y 1} with hZ3
  set Z4 : Set (Fin 2 → ℝ) := {y | y 0 * y 1 = 1} with hZ4
  have n1 : volume Z1 = 0 := by
    refine null_of_slices (isClosed_eq hcont1 continuous_const).measurableSet (fun x y hy z hz => ?_)
    simp [hZ1] at hy hz
    rw [hy, hz]
  have n2 : volume Z2 = 0 := by
    refine null_of_slices (isClosed_eq hcont1 hcont0).measurableSet (fun x y hy z hz => ?_)
    simp [hZ2] at hy hz
    rw [hy, hz]
  have n3 : volume Z3 = 0 := by
    refine null_of_slices (isClosed_eq hcont0 (continuous_const.mul hcont1)).measurableSet (fun x y hy z hz => ?_)
    simp [hZ3] at hy hz
    exact mul_left_cancel₀ hε0 (by rw [← hy, ← hz])
  have n4 : volume Z4 = 0 := by
    refine null_of_slices (isClosed_eq (hcont0.mul hcont1) continuous_const).measurableSet (fun x y hy z hz => ?_)
    simp [hZ4] at hy hz
    have hx : x ≠ 0 := by rintro rfl; simp at hy
    exact mul_left_cancel₀ hx (by rw [hy, hz])
  refine measure_mono_null ?_ (measure_union_null (measure_union_null (measure_union_null n1 n2) n3) n4)
  intro y hy
  -- closure and interior
  have hcl : closure (sectorSet ε) ⊆ {y : Fin 2 → ℝ | 0 ≤ y 1 ∧ y 1 ≤ y 0 ∧ y 0 ≤ ε ^ 2 * y 1 ∧ y 0 * y 1 ≤ 1} := by
    apply closure_minimal
    · rintro z ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1.le, h2, h3.le, h4⟩
    · exact (isClosed_le continuous_const hcont1).inter ((isClosed_le hcont1 hcont0).inter
        ((isClosed_le hcont0 (continuous_const.mul hcont1)).inter (isClosed_le (hcont0.mul hcont1) continuous_const)))
  have hint : {y : Fin 2 → ℝ | 0 < y 1 ∧ y 1 < y 0 ∧ y 0 < ε ^ 2 * y 1 ∧ y 0 * y 1 < 1} ⊆ interior (sectorSet ε) := by
    apply interior_maximal
    · rintro z ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2.le, h3⟩, h4.le⟩
    · exact (isOpen_lt continuous_const hcont1).inter ((isOpen_lt hcont1 hcont0).inter
        ((isOpen_lt hcont0 (continuous_const.mul hcont1)).inter (isOpen_lt (hcont0.mul hcont1) continuous_const)))
  obtain ⟨hyc, hyi⟩ := hy
  obtain ⟨c1, c2, c3, c4⟩ := hcl hyc
  by_contra hno
  simp only [Set.mem_union, Set.mem_ofPred_eq, hZ1, hZ2, hZ3, hZ4, not_or] at hno
  obtain ⟨⟨⟨n1', n2'⟩, n3'⟩, n4'⟩ := hno
  exact hyi (hint ⟨lt_of_le_of_ne c1 (Ne.symm n1'), lt_of_le_of_ne c2 n2', lt_of_le_of_ne c3 n3',
    lt_of_le_of_ne c4 n4'⟩)

/-- Helper: the Lebesgue integral of $\mathrm{ofReal}\circ g$ over $(a, b]$ for continuous nonnegative $g$. -/
theorem lintegral_Ioc_ofReal {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b))
    (hnn : ∀ x ∈ Set.Ioc a b, 0 ≤ g x) :
    ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (g x) = ENNReal.ofReal (∫ x in a..b, g x) := by
  rw [intervalIntegral.integral_of_le hab]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hnn)

/-- Helper: the length of the vertical slice of the sector at abscissa $x$. -/
theorem slice_volume {ε : ℝ} (hε : 1 < ε) (x : ℝ) :
    volume {y : ℝ | 0 < y ∧ y ≤ x ∧ x < ε ^ 2 * y ∧ x * y ≤ 1} =
      ENNReal.ofReal (min x (1 / x) - x / ε ^ 2) := by
  have hε2 : 1 < ε ^ 2 := by nlinarith
  have hε0 : 0 < ε ^ 2 := by linarith
  by_cases hx : 0 < x
  · have : {y : ℝ | 0 < y ∧ y ≤ x ∧ x < ε ^ 2 * y ∧ x * y ≤ 1} = Set.Ioc (x / ε ^ 2) (min x (1 / x)) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_Ioc, le_min_iff, div_lt_iff₀ hε0, le_div_iff₀ hx]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨by linarith, h2, by linarith⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨?_, h2, by linarith, by linarith⟩
        by_contra hy
        push Not at hy
        nlinarith
    rw [this, Real.volume_Ioc]
  · have hemp : {y : ℝ | 0 < y ∧ y ≤ x ∧ x < ε ^ 2 * y ∧ x * y ≤ 1} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -, -⟩
      linarith
    rw [hemp, measure_empty]
    symm
    rw [ENNReal.ofReal_eq_zero]
    have h1 : min x (1 / x) ≤ x := min_le_left _ _
    have h2 : x ≤ x / ε ^ 2 := by
      rw [le_div_iff₀ hε0]; nlinarith
    linarith

/-- Helper: **the area of the hyperbolic sector** $\{0 < v \le u < \varepsilon^2 v,\ uv \le 1\}$ is $\log\varepsilon$
($\varepsilon > 1$). Argument `ε`: the unit; `hε`: $1 < \varepsilon$. -/
theorem volume_sectorSet {ε : ℝ} (hε : 1 < ε) : volume.real (sectorSet ε) = Real.log ε := by
  have hε2 : 1 < ε ^ 2 := by nlinarith
  have hε0 : 0 < ε ^ 2 := by linarith
  have hεpos : 0 < ε := by linarith
  have hpres := volume_preserving_finTwoArrow ℝ
  set e := MeasurableEquiv.finTwoArrow (α := ℝ) with he
  set t : Set (ℝ × ℝ) := e.symm ⁻¹' sectorSet ε with ht
  have hst : sectorSet ε = e ⁻¹' t := by
    ext y
    have hy : (![y 0, y 1] : Fin 2 → ℝ) = y := by ext i; fin_cases i <;> rfl
    simp [ht, he, hy]
  have hmt : MeasurableSet t := e.symm.measurable (sectorSet_measurable ε)
  have hvol : volume (sectorSet ε) = ∫⁻ x : ℝ, ENNReal.ofReal (min x (1 / x) - x / ε ^ 2) := by
    rw [hst, hpres.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_apply hmt]
    refine lintegral_congr (fun x => ?_)
    rw [← slice_volume hε x]
    congr 1
    ext y
    simp [ht, he, sectorSet, sectorCone, hyp, and_assoc]
  set φ : ℝ → ℝ := fun x => min x (1 / x) - x / ε ^ 2 with hφ
  have hsupp : Function.support (fun x => ENNReal.ofReal (φ x)) ⊆ Set.Ioc 0 ε := by
    intro x hx
    rw [Function.mem_support, Ne, ENNReal.ofReal_eq_zero, not_le] at hx
    simp only [hφ] at hx
    have hx0 : 0 < x := by
      by_contra h
      push Not at h
      have h1 : min x (1 / x) ≤ x := min_le_left _ _
      have h2 : x ≤ x / ε ^ 2 := by rw [le_div_iff₀ hε0]; nlinarith
      linarith
    refine ⟨hx0, ?_⟩
    by_contra h
    push Not at h
    have h1 : min x (1 / x) ≤ 1 / x := min_le_right _ _
    have h2 : 1 / x ≤ x / ε ^ 2 := by
      rw [div_le_div_iff₀ hx0 hε0]; nlinarith
    linarith
  rw [Measure.real, hvol, ← setLIntegral_eq_of_support_subset hsupp]
  have hsplit : Set.Ioc (0 : ℝ) ε = Set.Ioc 0 1 ∪ Set.Ioc 1 ε := (Set.Ioc_union_Ioc_eq_Ioc zero_le_one hε.le).symm
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 ε) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    linarith [h1.2, h2.1]
  rw [hsplit, lintegral_union measurableSet_Ioc hdisj]
  have hA : ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (φ x) =
      ENNReal.ofReal (∫ x in (0 : ℝ)..1, (x - x / ε ^ 2)) := by
    rw [← lintegral_Ioc_ofReal zero_le_one (g := fun x => x - x / ε ^ 2) (by fun_prop)]
    · refine setLIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      simp only [hφ]
      have : min x (1 / x) = x := by
        apply min_eq_left
        rw [le_div_iff₀ hx.1]; nlinarith [hx.1, hx.2]
      rw [this]
    · intro x hx
      have : x / ε ^ 2 ≤ x := by
        rw [div_le_iff₀ hε0]; nlinarith [hx.1]
      linarith
  have hB : ∫⁻ x in Set.Ioc (1 : ℝ) ε, ENNReal.ofReal (φ x) =
      ENNReal.ofReal (∫ x in (1 : ℝ)..ε, (1 / x - x / ε ^ 2)) := by
    rw [← lintegral_Ioc_ofReal hε.le (g := fun x => 1 / x - x / ε ^ 2)]
    · refine setLIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      simp only [hφ]
      have hx0 : 0 < x := by linarith [hx.1]
      have : min x (1 / x) = 1 / x := by
        apply min_eq_right
        rw [div_le_iff₀ hx0]; nlinarith [hx.1]
      rw [this]
    · apply ContinuousOn.sub
      · apply ContinuousOn.div continuousOn_const continuousOn_id
        intro x hx; simp only [id]; linarith [hx.1]
      · fun_prop
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have : x / ε ^ 2 ≤ 1 / x := by
        rw [div_le_div_iff₀ hε0 hx0]; nlinarith [hx.2]
      linarith
  rw [hA, hB]
  have iA : ∫ x in (0 : ℝ)..1, (x - x / ε ^ 2) = (1 - 1 / ε ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [integral_id, intervalIntegral.integral_div]
    ring
  have iB : ∫ x in (1 : ℝ)..ε, (1 / x - x / ε ^ 2) = Real.log ε - (1 - 1 / ε ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub]
    · rw [integral_one_div_of_pos zero_lt_one hεpos]
      simp [integral_id, intervalIntegral.integral_div]
      field_simp
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hε.le] at hx
      simp only [id]; linarith [hx.1]
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  have nA : 0 ≤ (1 - 1 / ε ^ 2) / 2 := by
    have : 1 / ε ^ 2 ≤ 1 := by rw [div_le_one hε0]; linarith
    linarith
  have nB : 0 ≤ Real.log ε - (1 - 1 / ε ^ 2) / 2 := by
    rw [← iB]
    exact intervalIntegral.integral_nonneg hε.le (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      have : x / ε ^ 2 ≤ 1 / x := by
        rw [div_le_div_iff₀ hε0 hx0]; nlinarith [hx.2]
      linarith)
  rw [iA, iB, ← ENNReal.ofReal_add nA nB, ENNReal.toReal_ofReal (by linarith)]
  ring

end Geo

/-! ### Counting lattice points of $\mathbb Z^2$ in the sector, in transformed coordinates -/

section Count

open ZLattice

/-- Helper: **lattice points in the transformed sector.** For $\varepsilon > 1$ and an invertible real matrix $B$,
$$\frac{\#\{w \in \mathbb Z^2 : Bw \in \text{sectorCone}\ \varepsilon,\ H(Bw) \le c\}}{c} \longrightarrow
\frac{\log\varepsilon}{|\det B|}\quad(c \to \infty),$$
by Mathlib's `ZLattice.covolume.tendsto_card_le_div` for the lattice $\mathbb Z^2$, the cone $B^{-1}(\text{sector})$ and the
homogeneous function $H \circ B$. Arguments: `ε` the unit, `hε`, `B` the matrix, `hB` that its determinant is nonzero. -/
theorem cone_count {ε : ℝ} (hε : 1 < ε) (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B.det ≠ 0) :
    Tendsto (fun c : ℝ => (Nat.card {w : Fin 2 → ℤ // B.mulVec (fun i => (w i : ℝ)) ∈ sectorCone ε ∧
        hyp (B.mulVec (fun i => (w i : ℝ))) ≤ c} : ℝ) / c) atTop (𝓝 (Real.log ε / |B.det|)) := by
  classical
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  let M : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' B)
  let Mi : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' B⁻¹)
  have hM : ∀ x, M x = B.mulVec x := fun x => by simp [M, Matrix.toLin'_apply]
  have hMi : ∀ x, Mi x = B⁻¹.mulVec x := fun x => by simp [Mi, Matrix.toLin'_apply]
  have hMMi : ∀ y, M (Mi y) = y := by
    intro y; rw [hMi, hM, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hMiM : ∀ x, Mi (M x) = x := by
    intro x; rw [hM, hMi, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  let E : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) := ContinuousLinearEquiv.equivOfInverse M Mi hMiM hMMi
  have hE : ∀ x, E x = B.mulVec x := hM
  have hcoe : (E : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = ⇑(Matrix.toLin' B) := funext (fun x => by rw [hE, Matrix.toLin'_apply])
  have hdet : LinearMap.det (Matrix.toLin' B) ≠ 0 := by rw [LinearMap.det_toLin']; exact hB
  -- the sector set pulled back
  have hpre : ∀ s : Set (Fin 2 → ℝ), volume (E ⁻¹' s) = ENNReal.ofReal |B.det⁻¹| * volume s := by
    intro s
    rw [hcoe, Measure.addHaar_preimage_linearMap volume hdet s, LinearMap.det_toLin']
  have hX : ∀ ⦃x : Fin 2 → ℝ⦄ ⦃r : ℝ⦄, x ∈ E ⁻¹' sectorCone ε → 0 < r → r • x ∈ E ⁻¹' sectorCone ε := by
    intro x r hx hr
    simp only [Set.mem_preimage, map_smul] at hx ⊢
    exact sectorCone_smul hx hr
  have hF : ∀ x : Fin 2 → ℝ, ∀ ⦃r : ℝ⦄, 0 ≤ r →
      hyp (E (r • x)) = r ^ Fintype.card (Fin 2) * hyp (E x) := by
    intro x r hr
    rw [map_smul]; exact hyp_smul _ hr
  have hset : {x | x ∈ E ⁻¹' sectorCone ε ∧ hyp (E x) ≤ 1} = E ⁻¹' sectorSet ε := rfl
  have h2 : Bornology.IsBounded {x | x ∈ E ⁻¹' sectorCone ε ∧ hyp (E x) ≤ 1} := by
    rw [hset]
    have : E ⁻¹' sectorSet ε = E.symm '' sectorSet ε := by
      rw [E.image_symm_eq_preimage]
    rw [this]
    exact (ContinuousLinearMap.lipschitzWith (E.symm : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))).isBounded_image
      (sectorSet_bounded hε)
  have h3 : MeasurableSet {x | x ∈ E ⁻¹' sectorCone ε ∧ hyp (E x) ≤ 1} := by
    rw [hset]
    exact (sectorSet_measurable ε).preimage E.continuous.measurable
  have h4 : volume (frontier {x | x ∈ E ⁻¹' sectorCone ε ∧ hyp (E x) ≤ 1}) = 0 := by
    rw [hset]
    have hf : frontier (E ⁻¹' sectorSet ε) = E ⁻¹' frontier (sectorSet ε) :=
      (E.toHomeomorph.preimage_frontier _).symm
    rw [hf, hpre, sectorSet_frontier_null hε, mul_zero]
  have h := ZLattice.covolume.tendsto_card_le_div Lemma21Aux.Lz (X := E ⁻¹' sectorCone ε)
    (F := fun x => hyp (E x)) hX hF h2 h3 h4
  have hvol : volume.real {x | x ∈ E ⁻¹' sectorCone ε ∧ hyp (E x) ≤ 1} = Real.log ε / |B.det| := by
    rw [hset, measureReal_def, hpre, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      ← measureReal_def, volume_sectorSet hε, abs_inv]
    ring
  rw [hvol, Lemma21Aux.covolume_Lz, div_one] at h
  refine h.congr (fun c => ?_)
  congr 1
  rw [← Nat.card_congr (Equiv.ofBijective (fun w : {w : Fin 2 → ℤ // B.mulVec (fun i => (w i : ℝ)) ∈ sectorCone ε ∧
      hyp (B.mulVec (fun i => (w i : ℝ))) ≤ c} =>
      (⟨fun i => (w.1 i : ℝ), ⟨by simpa [hE] using w.2, (Lemma21Aux.mem_Lz _).mpr ⟨w.1, rfl⟩⟩⟩ :
        ↥({x : Fin 2 → ℝ | x ∈ E ⁻¹' sectorCone ε ∧ hyp (E x) ≤ c} ∩ (Lemma21Aux.Lz : Set (Fin 2 → ℝ))))) ⟨?_, ?_⟩)]
  · intro v w hvw
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val hvw) i
    simp only at this
    exact_mod_cast this
  · rintro ⟨x, hx1, hx2⟩
    obtain ⟨v, rfl⟩ := (Lemma21Aux.mem_Lz x).mp hx2
    exact ⟨⟨v, by simpa [hE] using hx1⟩, rfl⟩

end Count

/-! ### The congruence conditions as sublattices -/

section Sub

/-- Helper: **a line mod a prime is a sublattice of index $q$.** For a prime $q$ and $(\alpha, \beta) \in (\mathbb Z/q)^2$
not both zero there is an integer matrix $B$ of determinant $q$ whose image $B\mathbb Z^2$ is exactly
$\{w \in \mathbb Z^2 : \alpha w_0 + \beta w_1 \equiv 0 \pmod q\}$. -/
theorem cut_matrix (q : ℕ) [hq : Fact q.Prime] (α β : ZMod q) (h : α ≠ 0 ∨ β ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ, B.det = q ∧ ∀ w : Fin 2 → ℤ,
      (α * (w 0 : ZMod q) + β * (w 1 : ZMod q) = 0 ↔ ∃ z : Fin 2 → ℤ, w = B.mulVec z) := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hq0 : ((q : ℤ) : ZMod q) = 0 := by simp
  by_cases hα : α = 0
  · have hβ : β ≠ 0 := by tauto
    refine ⟨!![1, 0; 0, (q : ℤ)], by simp [Matrix.det_fin_two_of], fun w => ?_⟩
    subst hα
    constructor
    · intro hw
      simp only [zero_mul, zero_add, mul_eq_zero, hβ, false_or] at hw
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (w 1) q).mp hw
      refine ⟨![w 0, k], ?_⟩
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hk]
    · rintro ⟨z, rfl⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hq0]
  · set x : ZMod q := -(β / α) with hx
    set γ : ℤ := (x.val : ℤ) with hγ
    have hγx : ((γ : ℤ) : ZMod q) = x := by
      simp [hγ]
    refine ⟨!![(q : ℤ), γ; 0, 1], by simp [Matrix.det_fin_two_of], fun w => ?_⟩
    constructor
    · intro hw
      have h1 : ((w 0 - γ * w 1 : ℤ) : ZMod q) = 0 := by
        push_cast
        rw [hγx, hx]
        field_simp
        linear_combination hw
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h1
      refine ⟨![k, w 1], ?_⟩
      ext i; fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linarith
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rintro ⟨z, rfl⟩
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast
      rw [hγx, hx]
      field_simp
      simp [hq0]

/-- Helper: for a prime $q$ at which the form vanishes exactly on the line $\alpha\sigma_0 + \beta\sigma_1 = 0$
(`hiff`, as in `Lemma21Aux.local_zero_form`), $q \mid f(v) \iff \alpha v_0 + \beta v_1 \equiv 0 \pmod q$. -/
theorem dvd_iff_lin (q : ℕ) (a b c : ℤ) (α β : ZMod q)
    (hiff : ∀ σ : Fin 2 → ZMod q, ((a : ZMod q) * σ 0 ^ 2 + (b : ZMod q) * σ 0 * σ 1 + (c : ZMod q) * σ 1 ^ 2 = 0 ↔
      α * σ 0 + β * σ 1 = 0)) (v : Fin 2 → ℤ) :
    (q : ℤ) ∣ Lemma21Aux.Fint a b c v ↔ α * (v 0 : ZMod q) + β * (v 1 : ZMod q) = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := hiff (fun i => (v i : ZMod q))
  simp only [Lemma21Aux.Fint]
  push_cast
  exact this

/-- Helper: the linear form after substituting $v = Aw$. -/
theorem lin_mulVec (q : ℕ) (α β : ZMod q) (A : Matrix (Fin 2) (Fin 2) ℤ) (w : Fin 2 → ℤ) :
    α * ((A.mulVec w) 0 : ZMod q) + β * ((A.mulVec w) 1 : ZMod q) =
      (α * (A 0 0 : ZMod q) + β * (A 1 0 : ZMod q)) * (w 0 : ZMod q) +
        (α * (A 0 1 : ZMod q) + β * (A 1 1 : ZMod q)) * (w 1 : ZMod q) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Helper: **the conditions $p \mid f(v)$, $p \in P$, cut out a sublattice $A\mathbb Z^2$ of index $\prod_{p \in P}p$.**
For integers $a, b, c$ and a finite set $S$ of primes each dividing $b^2 - 4ac$ but not all of $a, b, c$, and every
$P \subseteq S$: there is an integer matrix $A$ with $|\det A| = \prod_{p \in P}p$ such that
$\{v \in \mathbb Z^2 : p \mid f(v)\ \forall p \in P\} = A\mathbb Z^2$ (induction on $P$ using `cut_matrix`). -/
theorem sublattice_exists (a b c : ℤ) (S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime)
    (hD : ∀ p ∈ S, (p : ℤ) ∣ b ^ 2 - 4 * a * c)
    (hprim : ∀ p ∈ S, ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    ∀ P : Finset ℕ, P ⊆ S → ∃ A : Matrix (Fin 2) (Fin 2) ℤ, A.det.natAbs = ∏ p ∈ P, p ∧
      ∀ v : Fin 2 → ℤ, (∀ p ∈ P, (p : ℤ) ∣ Lemma21Aux.Fint a b c v) ↔ ∃ w : Fin 2 → ℤ, v = A.mulVec w := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨1, by simp, fun v => ?_⟩
    simp
  | insert q P hqP ih =>
    intro hsub
    obtain ⟨A, hAdet, hA⟩ := ih ((Finset.subset_insert q P).trans hsub)
    have hqS : q ∈ S := hsub (Finset.mem_insert_self q P)
    have hq : q.Prime := hSp q hqS
    haveI : Fact q.Prime := ⟨hq⟩
    have hqdet : ¬ (q : ℤ) ∣ A.det := by
      intro hdvd
      have h1 : q ∣ A.det.natAbs := Int.natCast_dvd.mp hdvd
      rw [hAdet] at h1
      obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp h1
      have hp' : p.Prime := hSp p (hsub (Finset.mem_insert_of_mem hp))
      have := (Nat.prime_dvd_prime_iff_eq hq hp').mp hqp
      exact hqP (this ▸ hp)
    obtain ⟨α, β, hαβ, hiff⟩ := Lemma21Aux.local_zero_form q a b c (hD q hqS) (hprim q hqS)
    obtain ⟨α', hα'⟩ : ∃ x : ZMod q, x = α * (A 0 0 : ZMod q) + β * (A 1 0 : ZMod q) := ⟨_, rfl⟩
    obtain ⟨β', hβ'⟩ : ∃ x : ZMod q, x = α * (A 0 1 : ZMod q) + β * (A 1 1 : ZMod q) := ⟨_, rfl⟩
    have hdetq : (A.det : ZMod q) ≠ 0 := fun h => hqdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h)
    have hd : (A.det : ZMod q) = (A 0 0 : ZMod q) * A 1 1 - A 0 1 * A 1 0 := by
      rw [Matrix.det_fin_two]; push_cast; ring
    have hne : α' ≠ 0 ∨ β' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [hα'] at h1
      rw [hβ'] at h2
      have hα0 : α * (A.det : ZMod q) = 0 := by
        rw [hd]
        linear_combination (A 1 1 : ZMod q) * h1 - (A 1 0 : ZMod q) * h2
      have hβ0 : β * (A.det : ZMod q) = 0 := by
        rw [hd]
        linear_combination (-(A 0 1 : ZMod q)) * h1 + (A 0 0 : ZMod q) * h2
      have hα1 : α = 0 := (mul_eq_zero.mp hα0).resolve_right hdetq
      have hβ1 : β = 0 := (mul_eq_zero.mp hβ0).resolve_right hdetq
      rcases hαβ with h | h
      · exact h hα1
      · exact h hβ1
    obtain ⟨B, hBdet, hB⟩ := cut_matrix q α' β' hne
    refine ⟨A * B, ?_, fun v => ?_⟩
    · rw [Matrix.det_mul, Int.natAbs_mul, hAdet, hBdet, Finset.prod_insert hqP]
      simp [mul_comm]
    · rw [Finset.forall_mem_insert, hA v]
      constructor
      · rintro ⟨hqv, w, rfl⟩
        have h1 := (dvd_iff_lin q a b c α β hiff _).mp hqv
        rw [lin_mulVec, ← hα', ← hβ'] at h1
        obtain ⟨z, rfl⟩ := (hB w).mp h1
        exact ⟨z, by rw [Matrix.mulVec_mulVec]⟩
      · rintro ⟨z, rfl⟩
        refine ⟨?_, B.mulVec z, by rw [Matrix.mulVec_mulVec]⟩
        rw [← Matrix.mulVec_mulVec, dvd_iff_lin q a b c α β hiff, lin_mulVec, ← hα', ← hβ']
        exact (hB _).mpr ⟨z, rfl⟩

end Sub

