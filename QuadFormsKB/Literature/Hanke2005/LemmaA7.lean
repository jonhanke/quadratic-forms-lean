/-
# Hanke 2005, Lemma A7: volumes of quotients along a fibration

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Lemma A7** (p. 24): for a fibration $F : X\to Y$ with fibre $C$, compatible with the action of a discrete group
$\Gamma$, $\mu_X(\Gamma\backslash X) = \mu_Y(\Gamma\backslash Y)\,\mu_C((\Gamma\cap S)\backslash C)$, $S$ the kernel of the action on
$Y$. In the application (proof of Theorem 5.1, (5.6), p. 17) $X = G_a$, $Y = Z$, the fibres are cosets of $C_a$ and
$\Gamma\cap S = \Gamma\cap\{\pm1\}$ (Lemma A1).

**Measure-theoretic form** (`lemmaA7`). The fibre volume enters through the push-forward identity
$F_*\mu_X = c\,\mu_Y$ ($c = \mu_C(C)$, the content of the volume computations of §4.2–§4.3, e.g. `map_FR_hankeHaar`).
The quotient $\Gamma\backslash Y$ is measured by a set $D\subseteq Y$ that meets almost every $\Gamma$-orbit exactly $s$ times
counted with multiplicity, $\sum_{\gamma\in\Gamma}1_D(\gamma z) = s$; when the kernel of the action has $s$ elements and
$D$ is a fundamental domain for the effective action, this holds and $\mu_Y(D) = \mu_Y(\Gamma\backslash Y)$. Then for every
fundamental domain $E$ of $\Gamma$ in $X$:
$$s\cdot\mu_X(E) = c\cdot\mu_Y(D),\qquad\text{i.e.}\qquad \mu_X(\Gamma\backslash X) = \frac{c}{s}\,\mu_Y(\Gamma\backslash Y),$$
which is Lemma A7 with $\mu_C((\Gamma\cap S)\backslash C) = c/|\Gamma\cap S|$. Unconditional.
-/
import Mathlib
import QuadFormsKB.Citation

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Hanke2005

/-- **Lemma A7** (Hanke thesis, p. 24), measure-theoretic form: if $F : X\to Y$ is $\Gamma$-equivariant with
$F_*\mu_X = c\,\mu_Y$, $E$ is a fundamental domain of $\Gamma$ in $X$, and $D\subseteq Y$ meets almost every
$\Gamma$-orbit $s$ times ($\sum_\gamma 1_D(\gamma z) = s$), then $s\,\mu_X(E) = c\,\mu_Y(D)$. -/
@[kb "hanke2005crelle" "Lemma A7, p. 24"]
theorem lemmaA7 {Γ X Y : Type*} [Group Γ] [Countable Γ] [MeasurableSpace X] [MeasurableSpace Y]
    [MulAction Γ X] [MulAction Γ Y] [MeasurableConstSMul Γ X] {μX : Measure X} [SMulInvariantMeasure Γ X μX]
    {μY : Measure Y} {F : X → Y} (hF : Measurable F) (hequiv : ∀ (γ : Γ) (x : X), F (γ • x) = γ • F x)
    [MeasurableConstSMul Γ Y] {c : ℝ≥0∞} (hfib : μX.map F = c • μY)
    {E : Set X} (hE : IsFundamentalDomain Γ E μX) {D : Set Y} (hD : MeasurableSet D) {s : ℝ≥0∞}
    (hDs : ∀ᵐ y ∂μY, ∑' γ : Γ, D.indicator 1 (γ • y) = s) :
    s * μX E = c * μY D := by
  have h1 : c * μY D = ∫⁻ x, D.indicator 1 (F x) ∂μX := by
    have : c * μY D = (c • μY) D := by rw [Measure.smul_apply, smul_eq_mul]
    rw [this, ← hfib, Measure.map_apply hF hD, ← lintegral_indicator_one (hF hD)]
    rfl
  have hmeas : ∀ γ : Γ, Measurable fun x : X => D.indicator (1 : Y → ℝ≥0∞) (F (γ • x)) := fun γ =>
    (measurable_one.indicator hD).comp (hF.comp (measurable_const_smul γ))
  rw [h1, hE.lintegral_eq_tsum'' (fun x => D.indicator 1 (F x)), ← lintegral_tsum fun γ => (hmeas γ).aemeasurable]
  -- the integrand equals `s` almost everywhere
  have hae : ∀ᵐ x ∂μX, ∑' γ : Γ, D.indicator (1 : Y → ℝ≥0∞) (F (γ • x)) = s := by
    have hnull : μY {y | ∑' γ : Γ, D.indicator (1 : Y → ℝ≥0∞) (γ • y) ≠ s} = 0 := by
      simpa [ae_iff] using hDs
    have hmY : MeasurableSet {y | ∑' γ : Γ, D.indicator (1 : Y → ℝ≥0∞) (γ • y) ≠ s} :=
      (Measurable.ennreal_tsum fun γ => (measurable_one.indicator hD).comp (measurable_const_smul γ)
        ) (measurableSet_singleton s).compl
    have : μX (F ⁻¹' {y | ∑' γ : Γ, D.indicator (1 : Y → ℝ≥0∞) (γ • y) ≠ s}) = 0 := by
      rw [← Measure.map_apply hF hmY, hfib, Measure.smul_apply, hnull, smul_zero]
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) this
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
    simpa [hequiv] using hx
  rw [lintegral_congr_ae (ae_restrict_of_ae hae), setLIntegral_const]

end QuadFormsKB.Hanke2005
