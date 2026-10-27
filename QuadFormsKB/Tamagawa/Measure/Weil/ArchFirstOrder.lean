import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# First-order volume asymptotics of a strictly differentiable map

**Generic, Mathlib-only (upstreamable).** For a map $f : E\to E$ of a finite-dimensional real normed space with strict
derivative $L$ at $x$, and an additive Haar measure $\mu$:
$$\mu(f(s)) \le m\,\mu(s)\quad(m > |\det L|),\qquad m\,\mu(s) \le \mu(f(s))\quad(m < |\det L|)$$
for every set $s$ inside a small enough ball around $x$ (`eventually_image_le`, `eventually_le_image`).

This is Mathlib's `addHaar_image_le_mul_of_det_lt` / `mul_le_addHaar_image_of_lt_det` (Jacobian.lean) combined with
`HasStrictFDerivAt.approximates_deriv_on_nhds`; it is the form used to read off the constant between two Haar
measures from a computation at the identity only (Weil 1982, §2.2: a gauge form is determined by its value at one point).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Upper bound near a point** for a strictly differentiable map (Mathlib's Jacobian lemma, localized). -/
theorem eventually_image_le {f : E → E} {L : E →L[ℝ] E} {x : E} (hf : HasStrictFDerivAt f L x) {m : ℝ≥0}
    (hm : ENNReal.ofReal |L.det| < m) :
    ∃ r > (0 : ℝ), ∀ s ⊆ Metric.ball x r, μ (f '' s) ≤ m * μ s := by
  obtain ⟨δ, hδ, hδ0⟩ := ((addHaar_image_le_mul_of_det_lt μ L hm).and self_mem_nhdsWithin).exists
  obtain ⟨U, hU, hUapp⟩ := hf.approximates_deriv_on_nhds (c := δ) (Or.inr hδ0)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  exact ⟨r, hr, fun s hs => hδ s f (hUapp.mono_set (hs.trans hball))⟩

/-- **Lower bound near a point** for a strictly differentiable map. -/
theorem eventually_le_image {f : E → E} {L : E →L[ℝ] E} {x : E} (hf : HasStrictFDerivAt f L x) {m : ℝ≥0}
    (hm : (m : ℝ≥0∞) < ENNReal.ofReal |L.det|) :
    ∃ r > (0 : ℝ), ∀ s ⊆ Metric.ball x r, (m : ℝ≥0∞) * μ s ≤ μ (f '' s) := by
  obtain ⟨δ, hδ, hδ0⟩ := ((mul_le_addHaar_image_of_lt_det μ L hm).and self_mem_nhdsWithin).exists
  obtain ⟨U, hU, hUapp⟩ := hf.approximates_deriv_on_nhds (c := δ) (Or.inr hδ0)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  exact ⟨r, hr, fun s hs => hδ s f (hUapp.mono_set (hs.trans hball))⟩

/-- **Two-sided form**: for every $\varepsilon > 0$, near $x$ the expansion factor of $f$ is within $\varepsilon$ of
$|\det L|$ (as real numbers, for sets of finite measure). -/
theorem eventually_image_near {f : E → E} {L : E →L[ℝ] E} {x : E} (hf : HasStrictFDerivAt f L x) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r > (0 : ℝ), ∀ s ⊆ Metric.ball x r, μ s ≠ ∞ →
      (|L.det| - ε) * (μ s).toReal ≤ (μ (f '' s)).toReal ∧ (μ (f '' s)).toReal ≤ (|L.det| + ε) * (μ s).toReal := by
  set d := |L.det|
  obtain ⟨r₁, hr₁, h₁⟩ := eventually_image_le μ hf (m := (d + ε).toNNReal) (by
    rw [ENNReal.ofReal, ENNReal.coe_lt_coe]
    exact Real.toNNReal_lt_toNNReal_iff_of_nonneg (abs_nonneg _) |>.mpr (by linarith))
  by_cases hd : d - ε ≤ 0
  · refine ⟨r₁, hr₁, fun s hs hfin => ⟨?_, ?_⟩⟩
    · exact (mul_nonpos_of_nonpos_of_nonneg hd ENNReal.toReal_nonneg).trans ENNReal.toReal_nonneg
    · have h := h₁ s hs
      have hfin' : μ (f '' s) ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h
      have := (ENNReal.toReal_le_toReal hfin' (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)).mpr h
      rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ (by positivity)] at this
  rw [not_le] at hd
  obtain ⟨r₂, hr₂, h₂⟩ := eventually_le_image μ hf (m := (d - ε).toNNReal) (by
    rw [ENNReal.ofReal, ENNReal.coe_lt_coe]
    exact Real.toNNReal_lt_toNNReal_iff_of_nonneg hd.le |>.mpr (by linarith))
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun s hs hfin => ⟨?_, ?_⟩⟩
  · have h := h₂ s (hs.trans (Metric.ball_subset_ball (min_le_right _ _)))
    have h1 := h₁ s (hs.trans (Metric.ball_subset_ball (min_le_left _ _)))
    have hfin' : μ (f '' s) ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h1
    have := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) hfin').mpr h
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ hd.le] at this
  · have h := h₁ s (hs.trans (Metric.ball_subset_ball (min_le_left _ _)))
    have hfin' : μ (f '' s) ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h
    have := (ENNReal.toReal_le_toReal hfin' (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)).mpr h
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ (by positivity)] at this

end QuadFormsKB.Tamagawa.Measure.Weil
