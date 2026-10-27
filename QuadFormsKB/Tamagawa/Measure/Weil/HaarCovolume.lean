import QuadFormsKB.Tamagawa.Measure.Weil.CovolumeTransport

/-!
# Two Haar measures with the same finite nonzero covolume are equal

**Generic.** $G$ a locally compact second-countable group, $\Gamma\le G$ a countable subgroup, $\mu_1,\mu_2$ Haar measures on $G$.
If $\mathrm{covol}(\Gamma,\mu_1) = \mathrm{covol}(\Gamma,\mu_2)\notin\{0,\infty\}$ then $\mu_1 = \mu_2$ (Haar uniqueness:
$\mu_1 = c\,\mu_2$, and the covolume scales by $c$, `covolume_smul`). Used for the consistency test of the binary torus
measure comparison.
-/

open MeasureTheory Measure
open scoped ENNReal NNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **Haar measures are determined by one finite nonzero covolume.** -/
theorem eq_of_covolume_eq (Γ : Subgroup G) [Countable Γ] (μ₁ μ₂ : Measure G) [μ₁.IsHaarMeasure]
    [μ₂.IsHaarMeasure] (h : covolume Γ G μ₁ = covolume Γ G μ₂) (h0 : covolume Γ G μ₂ ≠ 0)
    (htop : covolume Γ G μ₂ ≠ ∞) : μ₁ = μ₂ := by
  set c := μ₁.haarScalarFactor μ₂
  have hc : μ₁ = (c : ℝ≥0∞) • μ₂ := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    have := Measure.haarScalarFactor_pos_of_isHaarMeasure μ₁ μ₂
    exact_mod_cast this.ne'
  rw [hc, covolume_smul Γ μ₂ hc0] at h
  have h1 : (c : ℝ≥0∞) = 1 := by
    have h' : (c : ℝ≥0∞) * covolume Γ G μ₂ = 1 * covolume Γ G μ₂ := by rw [one_mul]; exact h
    exact (ENNReal.mul_left_inj h0 htop).1 h'
  rw [hc, h1, one_smul]

end QuadFormsKB.Tamagawa.Measure.Weil
