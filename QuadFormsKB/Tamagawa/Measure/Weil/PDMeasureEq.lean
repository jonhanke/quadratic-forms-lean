/-
# Weil's quotient measure $\mu_{PD}$ is the Tamagawa measure of $SO(D^0)$

**Layer:** a totally real number field $F$, $a, b\in\mathcal O_F\setminus0$ with $\langle-a,-b,ab\rangle$ totally positive definite
($D = (a,b)_F$ totally definite, hence a division algebra).

* **`map_muPD_pdAdeleEquiv`**: the isomorphism $PD^\times(\mathbb A)\cong SO(D^0)(\mathbb A)$ (`pdAdeleEquiv`) carries
  `muPD` (the quotient of `tamQuat` by `tamIdeles`) to `muTam` with $\lambda_v = 1$.

*Proof.* Both are Haar measures, so they are proportional (`isMulLeftInvariant_eq_smul`), and they give the same covolume
$2$ to $PD^\times(F)\leftrightarrow SO(D^0)(F)$: `tamagawa_PD_division` (Weil's centre argument: $\tau(SL_1(D)) = 1$ and
Fujisaki/zeta) on one side, the ternary lattice route `tamagawaNumberTwoAdelic_ternary` (Siegel's mass formula for ternary
forms) on the other. No local computation is needed: this is how the archimedean bookkeeping of
`omegaQuatInf` on product shells is bypassed.

Source: Weil 1982, Thm 3.2.1, p. 43; Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatMeasureHaar

open MeasureTheory Measure Set Function Topology NumberField
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F}

local notation "Q₃" => QuatZeta.pureFormO a b

/-- **Weil's quotient measure on $PD^\times(\mathbb A)$ is the Tamagawa measure of $SO(D^0)$** (totally definite $D$ over a
totally real $F$): `(muPD …).map (pdAdeleEquiv a b ha hb) = muTam ⟨-a,-b,ab⟩ hQ 1`. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §3.7(a), p. 63; Thm 2.3.1 [unverified page]"]
theorem map_muPD_pdAdeleEquiv (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (Q₃).Nondegenerate)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₃))
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)).map
      (pdAdeleEquiv a b ha hb) = muTam Q₃ hQ (fun _ => 1) := by
  have ha0' : (a : F) ≠ 0 := by simpa using ha
  have hb0' : (b : F) ≠ 0 := by simpa using hb
  set μP := muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  have hH := isHaarMeasure_muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  set μ := μP.map (pdAdeleEquiv a b ha hb)
  have : μ.IsHaarMeasure := (pdAdeleEquiv a b ha hb).isHaarMeasure_map _
  have hc := isMulLeftInvariant_eq_smul (muTam Q₃ hQ (fun _ => 1)) μ
  set c := haarScalarFactor (muTam Q₃ hQ (fun _ => 1)) μ
  have := countable_pdGamma a b
  have hcov1 : covolume (GammaSOAdele Q₃) (SOAdele Q₃) μ = 2 := by
    rw [← covolume_eq_of_map (pdGamma a b) (GammaSOAdele Q₃) (pdAdeleEquiv a b ha hb).toMulEquiv
      (pdAdeleEquiv a b ha hb).continuous.measurable (pdAdeleEquiv a b ha hb).symm.continuous.measurable
      (map_pdGamma a b ha hb) μP μ rfl]
    exact tamagawa_PD_division a b ha hb hdiv
  have hcov2 : covolume (GammaSOAdele Q₃) (SOAdele Q₃) (muTam Q₃ hQ (fun _ => 1)) = 2 :=
    tamagawaNumberTwoAdelic_ternary Q₃ hQ hpd
  have := countable_GammaSOAdele Q₃
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    have hc0' : c = 0 := by exact_mod_cast h0
    rw [hc, hc0', zero_smul] at hcov2
    unfold covolume at hcov2
    split_ifs at hcov2 <;> simp at hcov2
  have h1 : (c : ℝ≥0∞) = 1 := by
    have h := covolume_smul (GammaSOAdele Q₃) μ hc0
    have hc' : muTam Q₃ hQ (fun _ => 1) = (c : ℝ≥0∞) • μ := by rw [hc]; ext s hs; simp
    rw [← hc', hcov2, hcov1] at h
    have h2 : (c : ℝ≥0∞) * 2 = 1 * 2 := by rw [one_mul]; exact h.symm
    exact (ENNReal.mul_left_inj (by norm_num) (by norm_num)).1 h2
  rw [hc]
  have : c = 1 := by exact_mod_cast h1
  rw [this, one_smul]

end

end QuadFormsKB.Tamagawa.Measure.Weil
