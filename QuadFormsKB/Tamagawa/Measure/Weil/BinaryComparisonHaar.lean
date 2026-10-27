import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchGlue

/-!
# Haar measures on a product are determined by one product test function
**Generic.** $G_1$, $G_2$ locally compact second-countable groups, $\mu$ a Haar measure on $G_1\times G_2$, $\nu_i$ Haar
measures on $G_i$. If for measurable $f_1, f_2\ge0$ the integral $\int f_1(x_1)f_2(x_2)\,d\mu$ equals
$(\int f_1\,d\nu_1)(\int f_2\,d\nu_2)\notin\{0,\infty\}$, then $\mu = \nu_1\times\nu_2$ (`eq_prod_of_lintegral`): by Haar uniqueness
$\mu = c\,(\nu_1\times\nu_2)$ and Tonelli, so $c = 1$. This is how the comparison $\Phi_*\mu_T = \mu^{\lambda}_{\mathrm{Tam}}$ is
read off from the archimedean and the finite fibre integrals.
-/

open MeasureTheory Measure
open scoped ENNReal NNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
  [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]

/-- **A Haar measure on a product is the product measure if it gives the same value to one product test function.** -/
theorem eq_prod_of_lintegral (μ : Measure (G₁ × G₂)) (ν₁ : Measure G₁) (ν₂ : Measure G₂) [μ.IsHaarMeasure]
    [ν₁.IsHaarMeasure] [ν₂.IsHaarMeasure] {f₁ : G₁ → ℝ≥0∞} {f₂ : G₂ → ℝ≥0∞} (hf₁ : Measurable f₁)
    (hf₂ : Measurable f₂) (h : ∫⁻ x, f₁ x.1 * f₂ x.2 ∂μ = (∫⁻ x, f₁ x ∂ν₁) * ∫⁻ x, f₂ x ∂ν₂)
    (h0 : (∫⁻ x, f₁ x ∂ν₁) * ∫⁻ x, f₂ x ∂ν₂ ≠ 0) (ht : (∫⁻ x, f₁ x ∂ν₁) * ∫⁻ x, f₂ x ∂ν₂ ≠ ⊤) :
    μ = ν₁.prod ν₂ := by
  set c := μ.haarScalarFactor (ν₁.prod ν₂)
  have hc : μ = (c : ℝ≥0∞) • (ν₁.prod ν₂) := Measure.isMulLeftInvariant_eq_smul _ _
  have hprod : ∫⁻ x, f₁ x.1 * f₂ x.2 ∂(ν₁.prod ν₂) = (∫⁻ x, f₁ x ∂ν₁) * ∫⁻ x, f₂ x ∂ν₂ :=
    lintegral_prod_mul hf₁.aemeasurable hf₂.aemeasurable
  rw [hc, lintegral_smul_measure, hprod] at h
  have h1 : (c : ℝ≥0∞) = 1 := by
    have h' : (c : ℝ≥0∞) * ((∫⁻ x, f₁ x ∂ν₁) * ∫⁻ x, f₂ x ∂ν₂) = 1 * ((∫⁻ x, f₁ x ∂ν₁) * ∫⁻ x, f₂ x ∂ν₂) := by
      rw [one_mul]; exact h
    exact (ENNReal.mul_left_inj h0 ht).1 h'
  rw [hc, h1, one_smul]

section Weights

open NumberField NumberField.InfinitePlace QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

open scoped Classical in
theorem measurable_archWeight :
    Measurable fun x : GInfSO (diagForm1 D) => (∏ w, wReal D w (x.1 w)) * ∏ w, wCpx D w (x.2 w) := by
  refine (Finset.measurable_prod _ fun w _ => (measurable_wReal D w).comp (measurable_fst.eval (a := w))).mul
    (Finset.measurable_prod _ fun w _ => (measurable_wCpx D w).comp (measurable_snd.eval (a := w)))

end Weights

end QuadFormsKB.Tamagawa.Measure.Weil
