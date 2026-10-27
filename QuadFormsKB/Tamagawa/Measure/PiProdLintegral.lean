import Mathlib

/-!
# Generic product lemmas for finite product measures

* `lintegral_pi_prod`: lower Lebesgue integral of a product of one-variable functions over
  `Measure.pi`.
* `measurePreserving_piComm`: swapping the two indices of a double finite product is measure
  preserving.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadFormsKB.Tamagawa.Measure

set_option backward.isDefEq.respectTransparency false in
private theorem lintegral_fin_pi_prod {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, MeasureTheory.Measure (α i)) [∀ i, SigmaFinite (μ i)] {f : ∀ i, α i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂MeasureTheory.Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmp := (MeasureTheory.measurePreserving_piFinSuccAbove μ 0).symm
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero]
    simp_rw [Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [← ih (μ := fun i => μ i.succ) (fun i => hf _),
      ← lintegral_prod_mul]
    · exact (hf 0).aemeasurable
    · exact (Finset.measurable_prod _ fun i _ => (hf i.succ).comp
        (measurable_pi_apply i)).aemeasurable

/-- Product formula for lower Lebesgue integrals over a finite product measure. -/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, MeasureTheory.Measure (α i)) [∀ i, SigmaFinite (μ i)] {f : ∀ i, α i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂MeasureTheory.Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (MeasureTheory.measurePreserving_piCongrLeft μ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_pi_prod (fun k => μ (e k)) (fun k => hf (e k))

/-- Swapping the two indices of a double finite product is measure preserving. -/
theorem measurePreserving_piComm {ι κ : Type*} [Fintype ι] [Fintype κ] {α : Type*}
    [MeasurableSpace α] (μ : MeasureTheory.Measure α) [SigmaFinite μ] :
    MeasurePreserving (fun (x : ι → κ → α) (k : κ) (i : ι) => x i k)
      (MeasureTheory.Measure.pi fun _ : ι => MeasureTheory.Measure.pi fun _ : κ => μ)
      (MeasureTheory.Measure.pi fun _ : κ => MeasureTheory.Measure.pi fun _ : ι => μ) := by
  classical
  have hmeas : Measurable (fun (x : ι → κ → α) (k : κ) (i : ι) => x i k) := by
    refine measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun i => ?_
    exact (measurable_pi_apply k).comp (measurable_pi_apply i)
  refine ⟨hmeas, ?_⟩
  symm
  refine MeasureTheory.Measure.pi_eq_generateFrom
    (C := fun _ : κ => Set.pi univ '' Set.pi univ fun _ : ι => {s : Set α | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => MeasureTheory.Measure.FiniteSpanningSetsIn.pi
      (fun _ : ι => μ.toFiniteSpanningSetsIn)) ?_
  intro s hs
  choose t ht hts using hs
  have hs' : s = fun k => Set.pi univ (t k) := funext fun k => (hts k).symm
  subst hs'
  have hmt : ∀ k i, MeasurableSet (t k i) := fun k i => ht k i (mem_univ i)
  rw [MeasureTheory.Measure.map_apply hmeas
    (MeasurableSet.univ_pi fun k => MeasurableSet.univ_pi fun i => hmt k i)]
  have hpre : (fun (x : ι → κ → α) (k : κ) (i : ι) => x i k) ⁻¹' Set.pi univ (fun k => Set.pi univ (t k))
      = Set.pi univ (fun i => Set.pi univ (fun k => t k i)) := by
    ext x
    simp only [mem_preimage, mem_pi, mem_univ, true_implies]
    exact forall_comm
  rw [hpre, MeasureTheory.Measure.pi_pi]
  simp_rw [MeasureTheory.Measure.pi_pi]
  exact Finset.prod_comm

end QuadFormsKB.Tamagawa.Measure
