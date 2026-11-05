/-
# Hanke 2005, §4.3 and §5: consequences of the complex-place fibre volume

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

The named statement `ArchCx.ArchFibrationComplex n` is now a theorem for $n\ge1$ (`ArchCx.archFibrationComplex`,
`ArchVolumeComplex.lean`). This file removes it from the results that assumed it.

**Proves** (all for $n\ge1$, resp. $n\ge3$ for Theorem 5.1)
* `ArchCx.map_FCQ_uncond`: the fibration at a complex place for every nondegenerate complex form;
* `Eq57.map_FQ_uncond`, `Eq57.eq56_class_uncond`, `Eq57.hankeMass_eq_tsum_uncond`: (5.1)–(5.7) over any number field,
  unconditional;
* `Eq57.theorem51_volZ_uncond`: **Theorem 5.1 for Hanke's mass (5.4)–(5.5), over any number field, with no named input**
  (the finite places by `R2Ram.shimuraMaximalDensityRest_proved`);
* `Eq57.corollary52_uncond`, `Eq57.corollary52_classNumberOne_uncond`: Corollary 5.2 (corrected), conditional only on
  Shimura's Theorem 5.10(1) (`ShimuraEqualMasses`).
-/
import QuadFormsKB.Literature.Hanke2005.ArchVolumeComplex
import QuadFormsKB.Literature.Hanke2005.Corollary52
import QuadFormsKB.Literature.Hanke2005.DyadicR2Ram

open MeasureTheory Measure NumberField NumberField.InfinitePlace
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

namespace ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex

/-- **The fibration at a complex place, for any nondegenerate complex form** (Hanke thesis, §4.3 with (2.9) and
Lemma 2.2), unconditional for $n\ge1$: $(F_Q)_*\big(2^{3n(n-1)/2}\mu_Q\big) =
|\det A|^{-(n+1)}\,\mathrm{vol}_C(C_{\mathbb C})\,\omega_Z$. -/
@[kb "hanke2005crelle" "§4.3, pp. 14–15; (2.9), p. 6; Lemma 2.2, p. 6"]
theorem map_FCQ_uncond {n : ℕ} (hn : 1 ≤ n) {Q : QuadForm ℂ n} (D : NFDataC Q) (hQ : gramDetC Q ≠ 0) :
    (ENNReal.ofReal ((2 : ℝ) ^ (3 * (n * (n - 1) / 2))) • lerayMeasureC Q hQ).map (FCQ D) =
      ENNReal.ofReal ((‖gramDetC Q‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * volCComplex n) • muZC n :=
  map_FCQ D (archFibrationComplex hn) hQ

end ArchCx

namespace Eq57

open QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Siegel
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

/-- **(5.1)–(5.3), unconditional**: $F_*\tau_a = \mathrm{vol}_C(C_a)\,\mu_Z$ over any number field. -/
@[kb "hanke2005crelle" "(5.1)–(5.3), p. 16; §4; (2.9)"]
theorem map_FQ_uncond (hn : 1 ≤ n) :
    (muArchHanke Q₀ hQ).map (FQ Q₀ hQ) = ENNReal.ofReal (∏ w, volCAt Q₀ w) • muZQ Q₀ hQ :=
  map_FQ Q₀ hQ hn fun _ => ArchCx.archFibrationComplex hn

/-- **(5.6) for the unit group of a class, unconditional.** -/
@[kb "hanke2005crelle" "(5.6), p. 17"]
theorem eq56_class_uncond (hn : 1 ≤ n) (i : DC Q₀) {D : Set (ZQ Q₀ hQ)} (hD : MeasurableSet D) {s : ℝ≥0∞}
    (hDs : ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, D.indicator 1 (γ • z) = s) :
    s * covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      ENNReal.ofReal (∏ w, volCAt Q₀ w) * muZQ Q₀ hQ D :=
  eq56_class Q₀ hQ hn (fun _ => ArchCx.archFibrationComplex hn) i hD hDs

/-- **(5.6)–(5.7), unconditional**: Hanke's mass is $\sum_a s_a^{-1}\mathrm{vol}_Z(D_a)$ over any number field. -/
@[kb "hanke2005crelle" "(5.4)–(5.7), pp. 16–17"]
theorem hankeMass_eq_tsum_uncond (hn : 1 ≤ n) (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i))
    (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0) (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) :
    hankeMass Q₀ hQ = ∑' i, muZQ Q₀ hQ (D i) / s i :=
  hankeMass_eq_tsum Q₀ hQ hn (fun _ => ArchCx.archFibrationComplex hn) D hD s hs0 hsT hDs

/-- **Theorem 5.1 for Hanke's mass (5.4)–(5.5), with no named input** (Hanke thesis, pp. 16–19): over any number field,
for $n\ge3$, $\mathcal O_F^n$ maximal and Shimura's hypothesis,
$\sum_a s_a^{-1}\mathrm{vol}_Z(D_a)$ equals the right side of Theorem 5.1. The archimedean volumes are proved fibre volumes
at every place (`ArchReal.map_FR_hankeHaar`, `ArchCx.archFibrationComplex`), the finite places are
`R2Ram.shimuraMaximalDensityRest_proved`. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19; (5.4)–(5.7)"]
theorem theorem51_volZ_uncond (hn : 3 ≤ n) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) :
    ∑' i, muZQ Q₀ hQ (D i) / s i = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_volZ Q₀ hQ R2Ram.shimuraMaximalDensityRest_proved hn hmax hdet
    (fun _ => ArchCx.archFibrationComplex (by omega)) D hD s hs0 hsT hDs

/-- **Corollary 5.2 (corrected)**, conditional only on Shimura's Theorem 5.10(1) (`ShimuraEqualMasses`). -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (corrected)"]
theorem corollary52_uncond (hn : 1 ≤ n) (I : ShimuraEqualMasses Q₀ hQ) (D : DC Q₀ → Set (ZQ Q₀ hQ))
    (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0) (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ / (Nat.card (DC Q₀) : ℝ≥0∞) :=
  corollary52 Q₀ hQ hn (fun _ => ArchCx.archFibrationComplex hn) I D hD s hs0 hsT hDs i

/-- **Corollary 5.2 for class number one (corrected)**, conditional only on `ShimuraEqualMasses`. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (corrected), class number one"]
theorem corollary52_classNumberOne_uncond (hn : 1 ≤ n) (I : ShimuraEqualMasses Q₀ hQ)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i)
    (hcard : Nat.card (DC Q₀) = 1) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ :=
  corollary52_classNumberOne Q₀ hQ hn (fun _ => ArchCx.archFibrationComplex hn) I D hD s hs0 hsT hDs hcard i

end Eq57

end QuadFormsKB.Hanke2005
