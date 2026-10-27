import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereMeas
import QuadFormsKB.Tamagawa.OrbitalEuler

/-!
# Continuity of the stabilizer embedding and positivity of the Tamagawa measure

* **`continuous_iota`**: $\iota : SO(Q')(\mathbb A)\to SO(V)(\mathbb A)$ is continuous (the finite part through
  `RestrictedProduct.mapAlong_continuous`).
* **`muTam_ne_zero`**: for a nondegenerate $Q$ in $n\ge3$ variables, $\mu_{\mathrm{Tam}}\ne0$: the archimedean factor is
  a positive multiple of a Haar measure and $\mu_f(SO(\hat L)) = \prod_v\alpha_v(L,L)>0$
  (`tprod_siegelDensity_pos`, which needs $n\ge3$).
* **`isFiniteMeasureOnCompacts_muTam'`**: $\mu_{\mathrm{Tam}}$ is finite on compact sets.
-/

open MeasureTheory Measure Set
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

namespace AdelicSphereSetup

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}
  (S : AdelicSphereSetup Q₀ ρ)

theorem continuous_iotaR (w : {w : InfinitePlace F // w.IsReal}) : Continuous (S.iotaR w) :=
  Continuous.subtype_mk ((continuous_conjBlockGL _).comp continuous_subtype_val) _

theorem continuous_iotaC (w : {w : InfinitePlace F // w.IsComplex}) : Continuous (S.iotaC w) :=
  Continuous.subtype_mk ((continuous_conjBlockGL _).comp continuous_subtype_val) _

theorem continuous_iotaV (v : HeightOneSpectrum (𝓞 F)) : Continuous (S.iotaV v) :=
  Continuous.subtype_mk ((continuous_conjBlockGL _).comp continuous_subtype_val) _

theorem continuous_iotaOAf : Continuous S.iotaOAf := by
  have hmaps : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Set.MapsTo (fun h : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F) => S.iotaV v h)
        (stdStab (S.C.Q'.map (algebraMap (𝓞 F) F)) v : Set _) (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Set _) :=
    S.eventually_PAt_glInt.mono fun v hv _ hh => S.iotaV_mem_stdStab hv hh
  have h : Continuous (RestrictedProduct.mapAlong (A₁ := fun v : HeightOneSpectrum (𝓞 F) => (stdStab (S.C.Q'.map (algebraMap (𝓞 F) F)) v : Set _))
      (A₂ := fun v : HeightOneSpectrum (𝓞 F) => (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Set _))
      (fun v : HeightOneSpectrum (𝓞 F) => orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
      (fun v : HeightOneSpectrum (𝓞 F) => orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
      id Filter.tendsto_id (fun v h => S.iotaV v h) hmaps) :=
    RestrictedProduct.mapAlong_continuous (A₁ := fun v : HeightOneSpectrum (𝓞 F) => (stdStab (S.C.Q'.map (algebraMap (𝓞 F) F)) v : Set _))
      (A₂ := fun v : HeightOneSpectrum (𝓞 F) => (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Set _))
      (fun v : HeightOneSpectrum (𝓞 F) => orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
      (fun v : HeightOneSpectrum (𝓞 F) => orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
      id Filter.tendsto_id (fun v h => S.iotaV v h) hmaps fun v => S.continuous_iotaV v
  exact h

theorem continuous_iotaFin : Continuous S.iotaFin :=
  Continuous.subtype_mk (S.continuous_iotaOAf.comp continuous_subtype_val) _

/-- **The stabilizer embedding $\iota : SO(Q')(\mathbb A)\to SO(V)(\mathbb A)$ is continuous.** -/
theorem continuous_iota : Continuous S.iota := by
  have hR : Continuous (MonoidHom.piMap S.iotaR) :=
    continuous_pi fun w => (S.continuous_iotaR w).comp (continuous_apply w)
  have hC : Continuous (MonoidHom.piMap S.iotaC) :=
    continuous_pi fun w => (S.continuous_iotaC w).comp (continuous_apply w)
  exact (hR.prodMap hC).prodMap S.continuous_iotaFin

end AdelicSphereSetup

section MuTam

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm (𝓞 F) n)

/-- $c_F > 0$. -/
theorem cF_pos' : 0 < cF F n :=
  Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))) _

/-- The archimedean factor of $\mu_{\mathrm{Tam}}$ is nonzero. -/
theorem muArchTamSO_univ_ne_zero (hQ : Q.Nondegenerate) : muArchTamSO Q hQ univ ≠ 0 := by
  have := LerayArch.isHaarMeasure_muArchLeray (QRe Q) (QCx Q) (gramDetR_QRe_ne_zero Q hQ)
    (gramDetC_QCx_ne_zero Q hQ)
  unfold muArchTamSO LerayArch.muArchNF
  rw [Measure.smul_apply, smul_eq_mul]
  refine mul_ne_zero ?_ (measure_univ_ne_zero.mpr (NeZero.ne _))
  exact (ENNReal.ofReal_pos.mpr (mul_pos cF_pos' cxWeil_pos)).ne'

/-- **$\mu_{\mathrm{Tam}}\ne 0$** for a nondegenerate form in $n \ge 3$ variables. -/
theorem muTam_ne_zero (hQ : Q.Nondegenerate) (hn : 3 ≤ n) : muTam Q hQ (fun _ => 1) ≠ 0 := by
  intro h
  have h1 : muTam Q hQ (fun _ => 1) (univ ×ˢ (KSO Q : Set (SOAf Q))) = 0 := by rw [h]; rfl
  rw [muTam, Measure.prod_prod, muFin_KSO] at h1
  have hpos : 0 < finFactor Q (fun _ => 1) := by
    rw [finFactor_one Q hQ]; exact tprod_siegelDensity_pos hn Q hQ
  exact (mul_ne_zero (muArchTamSO_univ_ne_zero Q hQ) (ENNReal.ofReal_pos.mpr hpos).ne') h1

/-- **$\mu_{\mathrm{Tam}}$ is finite on compact sets.** -/
theorem isFiniteMeasureOnCompacts_muTam' (hQ : Q.Nondegenerate)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) : IsFiniteMeasureOnCompacts (muTam Q hQ lam) := by
  have h1 : IsFiniteMeasureOnCompacts (muArchTamSO Q hQ) := by
    have := LerayArch.isHaarMeasure_muArchLeray (QRe Q) (QCx Q) (gramDetR_QRe_ne_zero Q hQ)
      (gramDetC_QCx_ne_zero Q hQ)
    unfold muArchTamSO LerayArch.muArchNF; rw [ofReal_smul_eq]; infer_instance
  have h2 : IsFiniteMeasureOnCompacts (Measure.muFin Q lam) := by
    unfold Measure.muFin; infer_instance
  unfold muTam; infer_instance

end MuTam

end QuadFormsKB.Tamagawa.Measure.Weil

end
