/-
# Generic pieces of the assembly over every number field

**Layer:** generic Haar uniqueness; $F$ any number field and $Q$ any nondegenerate form over $\mathcal O_F$.

* **`eq_of_eq_on_measurable`**: a Haar measure and a left invariant measure finite on compacts that agree on one measurable
  set of positive finite measure are equal (`eq_of_eq_on_open` without openness).
* **`muArchTamSO_pi`**: $\mu^{\mathrm{Tam}}_\infty(\prod_wU_w) = c_F(n)\,2^{n(n-1)r_2/2}\prod_w\mathrm{Leray}_w(U_w)$ for product sets over all
  archimedean places.

Source: Weil 1982, §2.1 (uniqueness of Haar measure), §2.3 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqGeneral

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.ArchPolar
open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchSOMeasure

noncomputable section

section Generic

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- **Haar uniqueness on one set of positive finite measure.** -/
@[kb "weil1982" "§2.1 (uniqueness of Haar measure) [unverified]"]
theorem eq_of_eq_on_measurable (μ μ' : Measure B) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts μ']
    [μ'.IsMulLeftInvariant] {U : Set B} (h0 : μ U ≠ 0) (hUt : μ U ≠ ∞) (h : μ U = μ' U) : μ = μ' := by
  have hc := isMulLeftInvariant_eq_smul μ' μ
  have h1 : (haarScalarFactor μ' μ : ℝ≥0∞) = 1 := by
    have := congrArg (fun ν : Measure B => ν U) hc
    simp only [Measure.smul_apply, nnreal_smul_coe_apply] at this
    rw [← h] at this
    have h2 : (haarScalarFactor μ' μ : ℝ≥0∞) * μ U = 1 * μ U := by rw [one_mul]; exact this.symm
    exact (ENNReal.mul_left_inj h0 hUt).1 h2
  rw [hc]
  have : haarScalarFactor μ' μ = 1 := by exact_mod_cast h1
  rw [this, one_smul]

end Generic

section ArchBox

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

open scoped Classical in
/-- **$\mu^{\mathrm{Tam}}_\infty(\prod_wU_w) = c_F(n)\,2^{n(n-1)r_2/2}\prod_{w\text{ real}}\mathrm{Leray}_w(U_w)
\prod_{w\text{ complex}}\mathrm{Leray}_w(U_w)$.** -/
theorem muArchTamSO_pi (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (UR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe Q w)))
    (UC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx Q w))) :
    muArchTamSO Q hQ ((univ.pi UR) ×ˢ (univ.pi UC)) =
      ENNReal.ofReal (cF F n * cxWeil F n) *
        ((∏ w, lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ w) (UR w)) *
          ∏ w, lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ w) (UC w)) := by
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero Q hQ w); infer_instance
  have hsfC : ∀ w, SigmaFinite (lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero Q hQ w); infer_instance
  rw [muArchTamSO, Measure.smul_apply, smul_eq_mul, LerayArch.muArchNF, LerayArch.muArchLeray,
    Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]

end ArchBox

end

end QuadFormsKB.Tamagawa.Measure.Weil
