import QuadFormsKB.Literature.Hanke2005.Eq57
import QuadFormsKB.Tamagawa.Indefinite.DCFinite
import QuadFormsKB.Citation

open MeasureTheory Measure NumberField NumberField.InfinitePlace
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.Eq57

open QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.LerayArch QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005.ArchReal
  QuadFormsKB.Hanke2005.ArchCx QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

open scoped Classical

/-- **Shimura's equality of masses** (Shimura 1999, Theorem 5.10(1), quoted in the proof of Hanke's Corollary 5.2,
p. 19): all the classes $a$ in the genus have the same volume
$\tau_a(\Gamma_a\backslash G_a)$ with respect to Hanke's archimedean measure $\tau_a$ on $G_a = SO(V)(F\otimes\mathbb R)$.
This is a cited result, assumed (not proved) here. -/
@[kb "hanke2005crelle" "proof of Corollary 5.2, p. 19 (quoting Shimura 1999, Thm 5.10(1))"]
structure ShimuraEqualMasses (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : Prop where
  eq : ∀ i j : DC Q₀, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
    covolume (unitGroup Q₀ j) (GInfSO Q₀) (muArchHanke Q₀ hQ)

/-- **Corollary 5.2, corrected** (Hanke thesis, p. 19). Let $D_a\subseteq Z$ meet almost every $\Gamma_a$-orbit $s_a$ times;
when $D_a$ is a fundamental domain of the effective action of $\Gamma_a$ on $Z$, $s_a = \varepsilon = [\Gamma_a\cap\{\pm1\}:1]$
($\varepsilon = 2$ for $n$ even, $1$ for $n$ odd, $-1\in\Gamma_a$ being $-1\in SO$ iff $n$ even). If all the classes have the same
$\tau_a(\Gamma_a\backslash G_a)$ (`ShimuraEqualMasses`), then
$$\mathrm{vol}_Z(D_a) = \frac{s_a\cdot\mathrm{Mass}}{h},\qquad h = \#\mathrm{Cl}\ (=\ \texttt{Nat.card (DC Q₀)}),$$
i.e. $\mathrm{vol}(\Gamma^a\backslash Z) = \varepsilon\,\mathrm{Mass}/[k_{\mathbb A}^\times : k^\times\sigma(D)]$.

*Erratum:* Hanke's printed statement has the class number in the numerator, $\mathrm{vol}(\Gamma^a\backslash Z) =
\varepsilon\,[k_{\mathbb A}^\times : k^\times\sigma(D)]\,\mathrm{Mass}$; the correct statement (which follows from
$\mathrm{Mass} = \sum_a\nu(\Gamma_a)$ and the equality of the $\nu(\Gamma_a)$) has it in the denominator, as here.

*Not formalized:* the identification of `Nat.card (DC Q₀)` with the index $[k_{\mathbb A}^\times : k^\times\sigma(D)]$ (Shimura
1999, Lemma 2.3(4), via Eichler's theorem "spinor genus = class", `eichler_spinorGenus_eq_class_uncond`). The statement is
in terms of the number of classes `Nat.card (DC Q₀)`, which is finite (`finite_DC`). -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (corrected)"]
theorem corollary52 (hn : 1 ≤ n) (hC : Nonempty {w : InfinitePlace F // w.IsComplex} → ArchFibrationComplex n)
    (I : ShimuraEqualMasses Q₀ hQ) (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i))
    (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0) (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ / (Nat.card (DC Q₀) : ℝ≥0∞) := by
  haveI := finite_DC Q₀ hQ
  haveI : Fintype (DC Q₀) := Fintype.ofFinite _
  set C := ENNReal.ofReal (∏ w, volCAt Q₀ w) with hCdef
  have hC0 : C ≠ 0 := by
    simp only [C, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun w _ => volCAt_pos Q₀ hQ w
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  set c := covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) with hcdef
  set K : ℝ≥0∞ := (Nat.card (DC Q₀) : ℝ≥0∞) with hKdef
  have hK0 : K ≠ 0 := by
    simp only [K, ne_eq, Nat.cast_eq_zero]
    exact Nat.card_pos_iff.mpr ⟨⟨i⟩, inferInstance⟩ |>.ne'
  have hKT : K ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmass : C * hankeMass Q₀ hQ = K * c := by
    have : hankeMass Q₀ hQ = (K * c) / C := by
      rw [hankeMass, tsum_congr (fun j => I.eq j i), tsum_fintype, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    rw [this, mul_comm]; exact ENNReal.div_mul_cancel hC0 hCT
  have h56 := eq56_class Q₀ hQ hn hC i (hD i) (hDs i)
  have key : K * muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ := by
    refine (ENNReal.mul_right_inj hC0 hCT).1 ?_
    calc C * (K * muZQ Q₀ hQ (D i)) = K * (C * muZQ Q₀ hQ (D i)) := by ring
      _ = K * (s i * c) := by rw [← h56]
      _ = s i * (K * c) := by ring
      _ = s i * (C * hankeMass Q₀ hQ) := by rw [hmass]
      _ = C * (s i * hankeMass Q₀ hQ) := by ring
  exact (ENNReal.eq_div_iff hK0 hKT).2 key

/-- **Corollary 5.2 for class number one** (corrected): if there is a single class, $\mathrm{vol}_Z(D_a) = s_a\cdot\mathrm{Mass}$,
i.e. $\mathrm{vol}(\Gamma\backslash Z) = \varepsilon\,\mathrm{Mass}$ when $D_a$ is a fundamental domain of the effective action
and $s_a = \varepsilon$. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (corrected), class number one"]
theorem corollary52_classNumberOne (hn : 1 ≤ n)
    (hC : Nonempty {w : InfinitePlace F // w.IsComplex} → ArchFibrationComplex n)
    (I : ShimuraEqualMasses Q₀ hQ) (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i))
    (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0) (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i)
    (hcard : Nat.card (DC Q₀) = 1) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ := by
  rw [corollary52 Q₀ hQ hn hC I D hD s hs0 hsT hDs i, hcard]
  simp

end QuadFormsKB.Hanke2005.Eq57
