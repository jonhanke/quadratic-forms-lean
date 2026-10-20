/-
# Haar reduction of `GnatMeasureComparisonDef` to one compact open set

**Layer:** a number field $F$; $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$.

* **`eq_of_eq_on_compact_open`** (generic): in a second countable locally compact group, a Haar measure $\mu$ and a left
  invariant measure $\mu'$ finite on compacts which agree on one nonempty compact open set are equal
  (Haar uniqueness, Mathlib's `isMulLeftInvariant_eq_smul`).
* **`muTam` is finite on compacts** (instance; $c_F\mu^{\mathrm{Leray}}_\infty$ is a Haar measure, $\mu_f$ = `haarNorm`).
* **`map_muP_sq_eq_of_compact_open`**: for the square model, $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ as soon as
  $\mu_P(\Phi^{-1}K') = \mu_{\mathrm{Tam}}(K')$ for one nonempty compact open $K'\subseteq SO(V)(\mathbb A)$; the same for the
  non-square model (`map_muP_ns_eq_of_compact_open`).

Source: Weil 1982, §2.3 (Haar uniqueness behind Thm 2.3.1) [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatComparison

open MeasureTheory Measure Set Function Topology NumberField
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

noncomputable section

section Generic

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- **Haar uniqueness on one compact open set**: a Haar measure $\mu$ and a left invariant measure $\mu'$ that is finite on
compacts, agreeing on a nonempty compact open $K$, are equal. -/
@[kb "weil1982" "§2.1 (uniqueness of Haar measure) [unverified]"]
theorem eq_of_eq_on_compact_open (μ μ' : Measure B) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts μ']
    [μ'.IsMulLeftInvariant] {K : Set B} (hKc : IsCompact K) (hKo : IsOpen K) (hKne : K.Nonempty)
    (h : μ K = μ' K) : μ = μ' := by
  have hc := isMulLeftInvariant_eq_smul μ' μ
  have h0 : μ K ≠ 0 := (hKo.measure_pos μ hKne).ne'
  have ht : μ K ≠ ∞ := hKc.measure_lt_top.ne
  have h1 : (haarScalarFactor μ' μ : ℝ≥0∞) = 1 := by
    have := congrArg (fun ν : Measure B => ν K) hc
    simp only [Measure.smul_apply, nnreal_smul_coe_apply] at this
    rw [← h] at this
    have h2 : (haarScalarFactor μ' μ : ℝ≥0∞) * μ K = 1 * μ K := by rw [one_mul]; exact this.symm
    exact (ENNReal.mul_left_inj h0 ht).1 h2
  rw [hc]
  have : haarScalarFactor μ' μ = 1 := by exact_mod_cast h1
  rw [this, one_smul]

end Generic

section MuTam

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

instance isFiniteMeasureOnCompacts_muArchTamSO (hQ : Q₀.Nondegenerate) :
    IsFiniteMeasureOnCompacts (muArchTamSO Q₀ hQ) := by
  have := LerayArch.isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ)
    (gramDetC_QCx_ne_zero Q₀ hQ)
  unfold muArchTamSO LerayArch.muArchNF; rw [ofReal_smul_eq]; infer_instance

instance isFiniteMeasureOnCompacts_muFin (lam : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℝ) :
    IsFiniteMeasureOnCompacts (Measure.muFin Q₀ lam) := by
  unfold Measure.muFin; infer_instance

/-- `muTam` is finite on compact sets. -/
instance isFiniteMeasureOnCompacts_muTam (hQ : Q₀.Nondegenerate)
    (lam : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℝ) : IsFiniteMeasureOnCompacts (muTam Q₀ hQ lam) := by
  unfold muTam; infer_instance

end MuTam

section Square

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

/-- **Step 1 for the square model**: $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ if both measures agree on one nonempty compact open
$K'\subseteq SO(V)(\mathbb A)$. -/
@[kb "weil1982" "§2.3 (Haar uniqueness) [unverified]"]
theorem map_muP_sq_eq_of_compact_open (hQ : (qSq a b).Nondegenerate) {K : Set (SOAdele (qSq a b))}
    (hKc : IsCompact K) (hKo : IsOpen K) (hKne : K.Nonempty)
    (h : (gnatSqO ha0 hb0).muP (muSq ha0 hb0) (sqPEquiv ha0 hb0 ⁻¹' K) = muTam (qSq a b) hQ (fun _ => 1) K) :
    ((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map (sqPEquiv ha0 hb0) = muTam (qSq a b) hQ (fun _ => 1) := by
  have := (gnatSqO ha0 hb0).isHaarMeasure_muP (muSq ha0 hb0)
  have : (((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map (sqPEquiv ha0 hb0)).IsHaarMeasure :=
    (sqPEquiv ha0 hb0).isHaarMeasure_map _
  refine eq_of_eq_on_compact_open _ _ hKc hKo hKne ?_
  rw [← h]; exact Measure.map_apply (sqPEquiv ha0 hb0).continuous.measurable hKo.measurableSet

end Square

end

end QuadFormsKB.Tamagawa.Measure.Weil
