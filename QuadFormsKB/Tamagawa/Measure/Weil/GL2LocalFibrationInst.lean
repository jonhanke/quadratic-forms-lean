import QuadFormsKB.Tamagawa.Measure.Weil.GL2LocalFibration
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Local

/-!
# The hypotheses of the local $\mathrm{GL}_2$ fibration at the places of a number field

$F$ a number field. `GL2Fib.Hyp` holds
* at the archimedean places together, $R = F_\infty$ (`mixedSpace F`) with the self-dual measure
  `Analysis.selfDualInf` and the module $|u|_\infty = |\det(x\mapsto ux)|$ (`normInf`): **`hyp_mixedSpace`**;
* at a finite place $v$, $R = F_v$ with the self-dual measure `Analysis.selfDualV v` and the module
  $|u|_v = \Delta_{F_v}(u)$ (`modK`): **`hyp_adic`**.
-/

open MeasureTheory Measure Set NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-! ### The archimedean places -/

theorem isUnit_mixedSpace_iff {a : mixedSpace F} : IsUnit a ↔ (∀ w, a.1 w ≠ 0) ∧ ∀ w, a.2 w ≠ 0 := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  simp only [isUnit_iff_ne_zero]

theorem mixedSpace_mul_inv_cancel {a : mixedSpace F} (ha : IsUnit a) : a * a⁻¹ = 1 := by
  obtain ⟨h1, h2⟩ := isUnit_mixedSpace_iff.1 ha
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · exact mul_inv_cancel₀ (h1 w)
  · exact mul_inv_cancel₀ (h2 w)

theorem measurableSet_isUnit_mixedSpace : MeasurableSet {a : mixedSpace F | IsUnit a} := by
  have : {a : mixedSpace F | IsUnit a} =
      (⋂ w, {a : mixedSpace F | a.1 w ≠ 0}) ∩ ⋂ w, {a : mixedSpace F | a.2 w ≠ 0} := by
    ext a; simp [isUnit_mixedSpace_iff, Set.mem_iInter]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun w => ?_) (MeasurableSet.iInter fun w => ?_)
  · exact (measurableSet_singleton 0).compl.preimage ((measurable_pi_apply w).comp measurable_fst)
  · exact (measurableSet_singleton 0).compl.preimage ((measurable_pi_apply w).comp measurable_snd)

theorem det_mulLeft_ne_zero_of_isUnit' {x : mixedSpace F} (hx : IsUnit x) :
    LinearMap.det (LinearMap.mulLeft ℝ x) ≠ 0 := by
  have := (hx.map (Algebra.norm ℝ)).ne_zero
  rwa [Algebra.norm_apply] at this

/-- **The local fibration hypotheses at the archimedean places.** -/
theorem hyp_mixedSpace : GL2Fib.Hyp (Analysis.selfDualInf (F := F)) (normInf (F := F)) where
  measurable_inv := measurable_inv_mixedSpace
  mul_inv_cancel _ ha := mixedSpace_mul_inv_cancel ha
  measurableSet_units := measurableSet_isUnit_mixedSpace
  measurable_md := measurable_normInf
  md_mul u v _ _ := by
    rw [normInf, normInf, normInf, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, ← LinearMap.det_comp]
    congr 3
    exact LinearMap.ext fun x => by simp
  md_one := by simp [normInf]
  md_ne_zero u hu := by
    rw [normInf, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (det_mulLeft_ne_zero_of_isUnit' hu)
  md_ne_top _ _ := ENNReal.ofReal_ne_top
  map_mul u hu := by
    have hdet := det_mulLeft_ne_zero_of_isUnit' hu
    ext s hs
    rw [Measure.map_apply (measurable_const_mul u) hs, Measure.smul_apply, smul_eq_mul]
    have hpre : (fun x => u * x) ⁻¹' s = (LinearMap.mulLeft ℝ u) ⁻¹' s := rfl
    rw [hpre, Measure.addHaar_preimage_linearMap _ hdet, normInf, abs_inv,
      ENNReal.ofReal_inv_of_pos (abs_pos.2 hdet)]

/-! ### The finite places -/

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F

theorem coe_unitsHomeomorphNeZero_symm {a : Kv} (ha : a ≠ 0) :
    ((unitsHomeomorphNeZero.symm ⟨a, ha⟩ : Kvˣ) : Kv) = a :=
  congrArg Subtype.val (unitsHomeomorphNeZero.apply_symm_apply ⟨a, ha⟩)

theorem modK_of_ne_zero {a : Kv} (ha : a ≠ 0) :
    modK v a = (distribHaarChar Kv (unitsHomeomorphNeZero.symm ⟨a, ha⟩) : ℝ≥0∞) := by
  rw [modK, dite_eq_left_of_eq_true (eq_true ha)]

/-- **The local fibration hypotheses at a finite place.** -/
theorem hyp_adic : GL2Fib.Hyp (Analysis.selfDualV v) (modK v) where
  measurable_inv := measurable_inv
  mul_inv_cancel a ha := mul_inv_cancel₀ (isUnit_iff_ne_zero.1 ha)
  measurableSet_units := by
    simp only [isUnit_iff_ne_zero]
    exact (measurableSet_singleton 0).compl
  measurable_md := measurable_modK v
  md_mul u w hu hw := by
    have hu0 := isUnit_iff_ne_zero.1 hu
    have hw0 := isUnit_iff_ne_zero.1 hw
    rw [modK_of_ne_zero v hu0, modK_of_ne_zero v hw0, modK_of_ne_zero v (mul_ne_zero hu0 hw0),
      ← ENNReal.coe_mul, ← map_mul]
    congr 3
    refine Units.ext ?_
    rw [Units.val_mul, coe_unitsHomeomorphNeZero_symm, coe_unitsHomeomorphNeZero_symm,
      coe_unitsHomeomorphNeZero_symm]
  md_one := by
    rw [modK_of_ne_zero v one_ne_zero]
    have : (unitsHomeomorphNeZero.symm ⟨(1 : Kv), one_ne_zero⟩ : Kvˣ) = 1 :=
      Units.ext (coe_unitsHomeomorphNeZero_symm v _)
    rw [this, map_one, ENNReal.coe_one]
  md_ne_zero u hu := by
    rw [modK_of_ne_zero v (isUnit_iff_ne_zero.1 hu)]
    exact ENNReal.coe_ne_zero.2 distribHaarChar_pos.ne'
  md_ne_top u hu := by
    rw [modK_of_ne_zero v (isUnit_iff_ne_zero.1 hu)]
    exact ENNReal.coe_ne_top
  map_mul u hu := by
    have hu0 := isUnit_iff_ne_zero.1 hu
    set g : Kvˣ := unitsHomeomorphNeZero.symm ⟨u, hu0⟩
    have := map_smul_eq_distribHaarChar_inv (Analysis.selfDualV v) g
    rw [modK_of_ne_zero v hu0, ← ENNReal.coe_inv distribHaarChar_pos.ne']
    convert this using 2
    funext x
    rw [Units.smul_def, smul_eq_mul, coe_unitsHomeomorphNeZero_symm]

end QuadFormsKB.Tamagawa.Measure.Weil
