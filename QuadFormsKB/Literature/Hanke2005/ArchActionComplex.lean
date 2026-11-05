/-
# Hanke 2005, §4.3: the action of $SO_n(\mathbb C)$ on the coordinates of $Z_{\mathbb C}$, and $\sigma$-finiteness

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Defines** `actZC g v`: the action (4.3.1)–(4.3.2) of $g\in SO_n(\mathbb C)$ on the coordinates $v = (z_{ik})_{i>k}$
of $Z_{\mathbb C}$, extended by the identity outside $Z_{\mathbb C}$ (so that it is a total action on `LIdx n → ℝ`).

**Proves**
* `MulAction (ArchSOC (sumSqC n)) (LIdx n → ℝ)` (via `actC_one`, `actC_mul`), and
  `FCG_mul`: $F_{\mathbb C}(gh) = g\cdot F_{\mathbb C}(h)$ (equivariance);
* `MeasurableConstSMul`: each $g$ acts measurably;
* $\sigma$-finiteness of `muZC`, `hankeHaarC` (complex place) and of `muZR`, `hankeHaarR` (real place).
-/
import QuadFormsKB.Literature.Hanke2005.ArchFibrationComplex
import QuadFormsKB.Literature.Hanke2005.ArchVolumeReal

open MeasureTheory Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {n : ℕ}

/-- **The action of $SO_n(\mathbb C)$ on the coordinates of $Z_{\mathbb C}$** (Hanke thesis, (4.3.1)–(4.3.2), p. 13):
$g\cdot v = (z\mapsto gz)$ in the coordinates $z_{ik}$, $i>k$, for $\mathrm{skewOf}\,v\in Z_{\mathbb C}$, and
$g\cdot v = v$ otherwise (a total extension; only the values on $Z_{\mathbb C}$ matter). -/
@[kb "hanke2005crelle" "(4.3.1)–(4.3.2), p. 13"]
def actZC (g : ArchSOC (sumSqC n)) (v : LIdx n → ℝ) : LIdx n → ℝ :=
  open Classical in if skewOf v ∈ ZC n then lowerOf (actC (ArchSOC.mat _ g) (skewOf v)) else v

theorem actZC_of_mem (g : ArchSOC (sumSqC n)) {v : LIdx n → ℝ} (hv : skewOf v ∈ ZC n) :
    actZC g v = lowerOf (actC (ArchSOC.mat _ g) (skewOf v)) := by
  classical
  simp [actZC, hv]

theorem skewOf_actZC (g : ArchSOC (sumSqC n)) {v : LIdx n → ℝ} (hv : skewOf v ∈ ZC n) :
    skewOf (actZC g v) = actC (ArchSOC.mat _ g) (skewOf v) := by
  have hz := (actC_mem (mat_mem_SOC g) hv).2
  rw [actZC_of_mem g hv, skewOf_lowerOf hz.1]

instance : SMul (ArchSOC (sumSqC n)) (LIdx n → ℝ) := ⟨actZC⟩

theorem smul_def (g : ArchSOC (sumSqC n)) (v : LIdx n → ℝ) : g • v = actZC g v := rfl

instance : MulAction (ArchSOC (sumSqC n)) (LIdx n → ℝ) where
  one_smul v := by
    classical
    rw [smul_def]
    by_cases hv : skewOf v ∈ ZC n
    · rw [actZC_of_mem _ hv, ArchSOC.mat_one, actC_one, lowerOf_skewOf]
    · simp [actZC, hv]
  mul_smul g h v := by
    classical
    simp only [smul_def]
    by_cases hv : skewOf v ∈ ZC n
    · have hv' : skewOf (actZC h v) ∈ ZC n := by
        rw [skewOf_actZC h hv]; exact (actC_mem (mat_mem_SOC h) hv).2
      rw [actZC_of_mem _ hv, actZC_of_mem _ hv', skewOf_actZC h hv, ArchSOC.mat_mul,
        actC_mul (mat_mem_SOC g) (mat_mem_SOC h) hv]
    · simp [actZC, hv]

/-- **Equivariance of $F_{\mathbb C}$**: $F_{\mathbb C}(gh) = g\cdot F_{\mathbb C}(h)$ (Hanke thesis, (4.3.3)). -/
theorem FCG_mul (g h : ArchSOC (sumSqC n)) : FCG (g * h) = g • FCG h := by
  have hm := FCG_mem h
  rw [smul_def, actZC_of_mem g hm, FCG, FCG, ArchSOC.mat_mul,
    actC_mul (mat_mem_SOC g) (mat_mem_SOC h) zero_mem_ZC,
    skewOf_lowerOf (actC_mem (mat_mem_SOC h) zero_mem_ZC).2.1]

/-! ### Measurability -/

theorem continuous_skewOf : Continuous (skewOf : (LIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  unfold skewOf
  simp only [of_apply]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).neg
  · exact continuous_const

theorem skewOf_transpose (v : LIdx n → ℝ) : (skewOf v)ᵀ = -skewOf v := by
  ext i k
  simp only [skewOf, transpose_apply, of_apply, Matrix.neg_apply]
  by_cases h : k < i
  · have : ¬ i < k := not_lt.mpr h.le
    simp [h, this]
  · by_cases h' : i < k
    · simp [h, h']
    · simp [h, h']

theorem measurableSet_skewOf_ZC : MeasurableSet (skewOf ⁻¹' ZC n : Set (LIdx n → ℝ)) := by
  set A : (LIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun v => 1 - (skewOf v)ᵀ * skewOf v with hA
  have hAc : Continuous A := by
    have := (continuous_skewOf (n := n))
    exact continuous_const.sub (this.matrix_transpose.matrix_mul this)
  have hH : ∀ v, (A v).IsHermitian := fun v => by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    simp [hA, transpose_mul, transpose_sub]
  have hset : (skewOf ⁻¹' ZC n : Set (LIdx n → ℝ)) =
      (⋂ x : Fin n → ℝ, {v | 0 ≤ x ⬝ᵥ (A v *ᵥ x)}) ∩ {v | (A v).det ≠ 0} := by
    ext v
    simp only [ZC, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨fun x => by simpa using h.posSemidef.dotProduct_mulVec_nonneg x, h.det_pos.ne'⟩
    · rintro ⟨h1, h2⟩
      have hps : (A v).PosSemidef :=
        PosSemidef.of_dotProduct_mulVec_nonneg (hH v) fun x => by simpa using h1 x
      exact ⟨skewOf_transpose v, hps.posDef_iff_det_ne_zero.mpr h2⟩
  rw [hset]
  have hc : ∀ x : Fin n → ℝ, Continuous fun v : LIdx n → ℝ => x ⬝ᵥ (A v *ᵥ x) := fun x =>
    continuous_const.dotProduct (hAc.matrix_mulVec continuous_const)
  exact MeasurableSet.inter (isClosed_iInter fun x => isClosed_le continuous_const (hc x)).measurableSet
    (isOpen_ne_fun hAc.matrix_det continuous_const).measurableSet

theorem measurable_matInv {α : Type*} [MeasurableSpace α] {f : α → Matrix (Fin n) (Fin n) ℝ}
    (hf : Measurable f) : Measurable fun x => (f x)⁻¹ := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have h1 : Measurable fun x => (f x).det :=
    (Continuous.matrix_det continuous_id).measurable.comp hf
  have h2 : Measurable fun x => (f x).adjugate i j :=
    (((continuous_apply j).comp ((continuous_apply i).comp
      (Continuous.matrix_adjugate continuous_id))).measurable).comp hf
  have : (fun x => (f x)⁻¹ i j) = fun x => ((f x).det)⁻¹ * (f x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  show Measurable fun x => (f x)⁻¹ i j
  rw [this]
  exact h1.inv.mul h2

theorem measurable_matMul {α : Type*} [MeasurableSpace α] {f g : α → Matrix (Fin n) (Fin n) ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x * g x := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  show Measurable fun x => (f x * g x) i j
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf))
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hg))

theorem measurable_matSub {α : Type*} [MeasurableSpace α] {f g : α → Matrix (Fin n) (Fin n) ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x - g x := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)).sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hg))

theorem measurable_matAdd {α : Type*} [MeasurableSpace α] {f g : α → Matrix (Fin n) (Fin n) ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x + g x := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)).add
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hg))

instance : MeasurableConstSMul (ArchSOC (sumSqC n)) (LIdx n → ℝ) where
  measurable_const_smul g := by
    classical
    show Measurable fun v : LIdx n → ℝ => actZC g v
    unfold actZC
    refine Measurable.ite measurableSet_skewOf_ZC ?_ measurable_id
    have hs : Measurable (skewOf : (LIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ) := continuous_skewOf.measurable
    have ha : Measurable fun z : Matrix (Fin n) (Fin n) ℝ => reM (ArchSOC.mat _ g) * z - imM (ArchSOC.mat _ g) :=
      measurable_matSub (measurable_matMul measurable_const measurable_id) measurable_const
    have hb : Measurable fun z : Matrix (Fin n) (Fin n) ℝ => reM (ArchSOC.mat _ g) + imM (ArchSOC.mat _ g) * z :=
      measurable_matAdd measurable_const (measurable_matMul measurable_const measurable_id)
    have hact : Measurable fun z : Matrix (Fin n) (Fin n) ℝ => actC (ArchSOC.mat _ g) z :=
      measurable_matMul ha (measurable_matInv hb)
    refine measurable_pi_iff.mpr fun p => ?_
    exact (measurable_pi_apply p.1.2).comp ((measurable_pi_apply p.1.1).comp (hact.comp hs))

/-! ### $\sigma$-finiteness -/

theorem sigmaFinite_ofReal_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (c : ℝ) :
    SigmaFinite (ENNReal.ofReal c • μ) := by
  show SigmaFinite (((Real.toNNReal c : NNReal) : ℝ≥0∞) • μ)
  rw [← ENNReal.smul_def]
  infer_instance

instance : SigmaFinite (muZC n) := by
  unfold muZC; infer_instance

instance : SigmaFinite (hankeHaarC n) := by
  have := isHaarMeasure_lerayMeasureC (Q := sumSqC n) (hQ := gramDetC_sumSqC_ne_zero)
  have : SigmaFinite (lerayMeasureC (sumSqC n) gramDetC_sumSqC_ne_zero) := inferInstance
  unfold hankeHaarC
  exact sigmaFinite_ofReal_smul _ _

end QuadFormsKB.Hanke2005.ArchCx

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.ArchSOMeasure

instance {r t : ℕ} : SigmaFinite (muZR r t) := by
  unfold muZR; infer_instance

instance {r t : ℕ} : SigmaFinite (hankeHaarR r t) := by
  have := isHaarMeasure_lerayMeasure (Q := phiQ r t) (hQ := gramDetR_phiQ_ne_zero)
  have : SigmaFinite (lerayMeasure (phiQ r t) gramDetR_phiQ_ne_zero) := inferInstance
  unfold hankeHaarR
  exact QuadFormsKB.Hanke2005.ArchCx.sigmaFinite_ofReal_smul _ _

end QuadFormsKB.Hanke2005.ArchReal
