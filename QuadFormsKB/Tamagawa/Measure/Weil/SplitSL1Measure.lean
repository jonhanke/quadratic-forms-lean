import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Finite
import QuadFormsKB.Tamagawa.Measure.Weil.QuatNrdFibration

/-!
# $\psi_*\mu_{\mathrm{SL}_1} = \mu_T$ for split $D$: the reduction to one box

**Layer:** $F$ a number field, $a, b\in\mathcal O_F\setminus 0$, $x, y\in F$ with $x^2 - ay^2 = b$
($D = \mathbb H[F,a,b]\cong M_2(F)$), $\psi$ = `sl1SplitEquiv`.

The reduced-norm fibration `fibMeas_nrdPos` says that `tamQuat` is the fibred measure of $\mu_{A_+}$ and
$\mu_{\mathrm{SL}_1}$ along $\operatorname{nrd}$. Since $\psi_*\mu_{\mathrm{SL}_1}$ and $\mu_T$ are Haar measures on
$\mathrm{SL}_2(\mathbb A_F)$, they differ by a constant $c$, and so do the two fibred measures; hence
**`map_muSL1_eq_muT_of_box`**: $\psi_*\mu_{\mathrm{SL}_1} = \mu_T$ as soon as `tamQuat` and the fibred measure of
$\mu_{A_+}$ and $\psi^*\mu_T$ agree on one set $X$ with $0 < \mathrm{tamQuat}(X) < \infty$.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {a b x y : F}
  (ha : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
    Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
    Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b)

/-- $\psi^*\mu_T$ on $\ker(\operatorname{nrd} : (D\otimes\mathbb A)^\times\to A_+)$. -/
def muTP : Measure (nrdPos a b).ker :=
  ((muT F).map (sl1SplitEquiv ha0 hb0 h).symm).map (kerPosEquiv a b).symm

theorem isHaarMeasure_muTP : (muTP ha0 hb0 h).IsHaarMeasure := by
  have : ((muT F).map (sl1SplitEquiv ha0 hb0 h).symm).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  exact ContinuousMulEquiv.isHaarMeasure_map _ _

set_option maxHeartbeats 1000000 in
include ha hb in
/-- **Reduction to one box**: if `tamQuat` and the fibred measure of $\mu_{A_+}$ and $\psi^*\mu_T$ agree on one set of
finite positive `tamQuat`-measure, then $\psi_*\mu_{\mathrm{SL}_1} = \mu_T$. -/
theorem map_muSL1_eq_muT_of_box {X : Set (QuatAdele a b)ˣ} (h0 : tamQuat a b X ≠ 0)
    (htop : tamQuat a b X ≠ ∞)
    (hbox : NormalFib.fibMeas (nrdPos a b) (nrdPos_surjective ha0 hb0) (muPosA a b) (muTP ha0 hb0 h) X =
      tamQuat a b X) :
    (muSL1 ha hb ha0 hb0).map (sl1SplitEquiv ha0 hb0 h) = muT F := by
  set ψ := sl1SplitEquiv ha0 hb0 h
  set ν : Measure (SL1A a b) := (muT F).map ψ.symm with hν
  have : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  have := isHaarMeasure_muTP ha0 hb0 h
  set c := (muSL1 ha hb ha0 hb0).haarScalarFactor ν
  have hc : muSL1 ha hb ha0 hb0 = (c : ℝ≥0∞) • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have hP : muSL1P ha hb ha0 hb0 = (c : ℝ≥0∞) • muTP ha0 hb0 h := by
    rw [muSL1P, hc, Measure.map_smul _ (map_continuous (kerPosEquiv a b).symm).measurable.aemeasurable]; rfl
  have hfib := fibMeas_nrdPos ha hb ha0 hb0
  rw [hP, NormalFib.fibMeas_smul _ _ measurable_nrdPos _ _ _ ENNReal.coe_ne_top] at hfib
  have hX' := congrArg (fun μ : Measure (QuatAdele a b)ˣ => μ X) hfib
  simp only [Measure.smul_apply, smul_eq_mul, hbox] at hX'
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have : (c : ℝ≥0∞) * tamQuat a b X = 1 * tamQuat a b X := by rw [one_mul]; exact hX'
    exact (ENNReal.mul_left_inj h0 htop).1 this
  rw [hc, hc1, one_smul, hν, Measure.map_map (map_continuous ψ).measurable (map_continuous ψ.symm).measurable]
  have : (ψ ∘ ψ.symm) = id := funext fun g => ψ.apply_symm_apply g
  rw [this, Measure.map_id]

end QuadFormsKB.Tamagawa.Measure.Weil
