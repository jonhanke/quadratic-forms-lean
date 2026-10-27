import QuadFormsKB.Tamagawa.Measure.Weil.BinaryComparisonHaar

/-!
# The measure comparison for the norm-one torus, from its archimedean and finite factors

**Layer:** as in `BinaryNonCompact.lean`. $\Phi_*\mu_T$ = `muTorSO`, $\mu^\lambda_{\mathrm{Tam}}$ = `muTam (diagForm1 D) hQ (lamL χ_E)`.

**Proves**
* **`torComparison_of_finiteFactor`**: if a finite box $A_f$ (over the places of $E$) has finite fibre function
  $K_f = N\cdot\mathbf 1_{K'}$ and $\mu_{f,E}(A_f) = \text{shellRatio}^{-1}\cdot N\cdot\mu^\lambda_f(K')$ with $0 < N\mu^\lambda_f(K') < \infty$,
  then $\Phi_*\mu_T = \mu^\lambda_{\mathrm{Tam}}$. *Proof:* the fibration identity for the box $\text{shell}\times A_f$
  (`tamQuad_box_eq_lintegral`), the archimedean factor $\omega_{\infty,E}(\text{shell}) = \text{shellRatio}\cdot\int K_\infty\,d\mu_{\infty}$
  (`omegaInf_shellE_eq_mul`), and `eq_prod_of_lintegral`.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {D : 𝓞 F} {E : Type} [Field E] [NumberField E] [Algebra F E]
  {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D))

theorem measurableSet_shellE (E : Type) [Field E] [NumberField E] : MeasurableSet (shellE E) := by
  refine (measurableSet_infBoxSet (fun _ => ?_) (fun _ => ?_)).preimage Units.continuous_val.measurable
  · exact measurableSet_Icc.preimage continuous_abs.measurable
  · exact measurableSet_Icc.preimage (continuous_norm.pow 2).measurable

theorem shellRatio_pos (hD : D ≠ 0) : 0 < shellRatio D := by
  have hd : (4 * dD D : F) ≠ 0 := by
    refine mul_ne_zero (by norm_num) (neg_ne_zero.mpr ?_)
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hD
  have hN : (0 : ℝ) < ((|Algebra.norm ℚ (4 * dD D)| : ℚ) : ℝ) := by
    have : Algebra.norm ℚ (4 * dD D) ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hd
    exact_mod_cast abs_pos.mpr this
  have hdF : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F))
  unfold shellRatio
  positivity

/-- **The comparison from the finite factor.** -/
theorem torComparison_of_finiteFactor (hD : D ≠ 0) {Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ} (hAf : MeasurableSet Af)
    (N : ℝ≥0∞) (K' : Set (SOAf (diagForm1 D))) (hK' : MeasurableSet K')
    (hKf : ∀ x, fibFinSO E hb1 hD Af x = N * K'.indicator 1 x)
    (hfin : muFinUnits E Af = ENNReal.ofReal (shellRatio D)⁻¹ *
      (N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K'))
    (h0 : N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ 0)
    (ht : N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ ⊤) :
    muTorSO hb0 hb1 hD = muTam (diagForm1 D) (nondegenerate_diagForm1 hD) (lamL (chiE F E)) := by
  have hQ := nondegenerate_diagForm1 hD
  set μI := muArchTamSO (diagForm1 D) hQ
  set μF := Measure.muFin (diagForm1 D) (lamL (chiE F E))
  -- the integrals
  have hIinf := lintegral_fibInfSO_shellE_real D hb0 hb1 hD hQ
  set r := cF F 2 * cxWeil F 2 * ((∏ w, realLocalR D w) * ∏ w, cpxLocalR D w) with hr
  have hrpos : 0 < r := by
    have h1 : 0 < ∏ w, realLocalR D w := Finset.prod_pos fun w _ => realLocalR_pos D hD w
    have h2 : 0 < ∏ w, cpxLocalR D w := Finset.prod_pos fun w _ => cpxLocalR_pos D hD w
    have h3 : 0 < cF F 2 :=
      Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))) _
    have := cxWeil_pos (F := F) (n := 2)
    positivity
  have hIfin : ∫⁻ x, fibFinSO E hb1 hD Af x ∂μF = N * μF K' := by
    simp_rw [hKf]
    rw [lintegral_const_mul N (measurable_one.indicator hK'), lintegral_indicator_one hK']
  have hfmeas : Measurable fun x => fibFinSO E hb1 hD Af x := by
    have : (fun x => fibFinSO E hb1 hD Af x) = fun x => N * K'.indicator 1 x := funext hKf
    rw [this]; exact measurable_const.mul (measurable_one.indicator hK')
  have himeas : Measurable fun x => fibInfSO E hb1 hD (shellE E) x := by
    have : (fun x => fibInfSO E hb1 hD (shellE E) x) =
        fun x : GInfSO (diagForm1 D) => (∏ w, wReal D w (x.1 w)) * ∏ w, wCpx D w (x.2 w) :=
      funext (fibInfSO_shellE D hb0 hb1 hD)
    rw [this]; exact measurable_archWeight D
  have hglue := tamQuad_box_eq_lintegral hb0 hb1 hD (measurableSet_shellE E) hAf
  have := isHaarMeasure_muTorSO hb0 hb1 hD
  have hHaarI : μI.IsHaarMeasure := by
    have := LerayArch.isHaarMeasure_muArchLeray (QRe (diagForm1 D) ) (QCx (diagForm1 D))
      (gramDetR_QRe_ne_zero _ hQ) (gramDetC_QCx_ne_zero _ hQ)
    simp only [μI]
    unfold muArchTamSO LerayArch.muArchNF
    rw [ofReal_smul_eq]
    exact IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr (mul_pos
      (Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))) _) cxWeil_pos)).ne'
  have hpos : 0 < finFactor (diagForm1 D) (lamL (chiE F E)) := by
    rcases (finFactor_nonneg (diagForm1 D) (lamL (chiE F E))).lt_or_eq with hlt | h0'
    · exact hlt
    · exfalso; apply h0
      have hz : μF = 0 := by simp only [μF]; unfold Measure.muFin haarNorm; rw [← h0']; simp
      rw [hz, Measure.coe_zero, Pi.zero_apply, mul_zero]
  have hHaarF : μF.IsHaarMeasure := by
    simp only [μF]; unfold Measure.muFin haarNorm
    exact IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr hpos).ne'
  change muTorSO hb0 hb1 hD = μI.prod μF
  refine eq_prod_of_lintegral _ _ _ himeas hfmeas ?_ ?_ ?_
  · have hs1 : ENNReal.ofReal (shellRatio D) * ENNReal.ofReal (shellRatio D)⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (shellRatio_pos hD).le, mul_inv_cancel₀ (shellRatio_pos hD).ne', ENNReal.ofReal_one]
    rw [← hglue, hIfin, hIinf, omegaInf_shellE_eq_mul D hb0 hb1 hD hQ, hIinf, hfin]
    calc _ = ENNReal.ofReal r * (N * μF K') * (ENNReal.ofReal (shellRatio D) * ENNReal.ofReal (shellRatio D)⁻¹) := by
          ring
      _ = _ := by rw [hs1, mul_one]
  · rw [hIinf, hIfin]; exact mul_ne_zero (by simpa using hrpos) h0
  · rw [hIinf, hIfin]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht

end QuadFormsKB.Tamagawa.Measure.Weil
