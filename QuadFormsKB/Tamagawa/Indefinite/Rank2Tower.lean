/-
# Frame coordinates with a binary anisotropic complement

**Layer:** number fields, adeles. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 2$ variables (any
signature), $\Xi$ a rational frame of a nondegenerate $T_0$ whose orthogonal complement $W$ is **anisotropic**
(`ComplAnisotropic`; equivalently $\delta = -\det H_{Q_0}\det H_{T_0}$ is not a square, `complAnisotropic_iff`).

`FrameTower` (`FrameTower.lean`) was built for complements of rank $n'\ge3$ only because the adelic sphere measure, the
quotient of `muTam Q₀ 1` by `muTam Q' 1`, needs `muTam Q' 1 ≠ 0`. For the last step, with a binary complement $Q'$,
`muTam Q' 1 ≠ 0` holds when $Q'$ is anisotropic (`muTam_one_ne_zero_of_anisotropicF`), although `muTam Q' 1` is then
not Weil's measure (it has no convergence factors; it is a positive multiple of Weil's measure `muTamBin`). This file:
* `sphereMeasureOf`, `sphereFibrationOf`: the adelic sphere measure and Weil's fibration for any setup with
  `muTam Q' 1 ≠ 0` (the proof of `AdelicSphereSetup.sphereFibration`, with that hypothesis in place of $k\ge3$);
* `FrameTower.stepWith`: the induction step of `FrameTower.step` from any sphere measure with the fibration identity;
* **`nonempty_frameTower_rank2`** (orthogonal frames) and **`nonempty_frameTower_ratFrame_rank2`** (every rational frame
  of $T_0$ with $\delta$ not a square): frame coordinates with complement of rank $2$.
-/
import QuadFormsKB.Tamagawa.Indefinite.Rank2Compl
import QuadFormsKB.Tamagawa.Indefinite.Rank2Analytic

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-! ### The adelic sphere measure when `muTam Q' 1 ≠ 0` -/

section SphereOf

variable {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F} (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)
  (hQ : Q₀.Nondegenerate) (h0 : muTam S.C.Q' S.C.hQ' (fun _ => 1) ≠ 0)

/-- An auxiliary set $U$ with $0 < \mu'(U) < \infty$, $\mu' = $ `muTam Q' 1`. -/
def refSetOf : Set (SOAdele S.C.Q') :=
  (OrbitSection.exists_pos_lt_top (muTam S.C.Q' S.C.hQ' fun _ => 1) h0).choose

theorem refSetOf_spec : MeasurableSet (refSetOf S h0) ∧ muTam S.C.Q' S.C.hQ' (fun _ => 1) (refSetOf S h0) ≠ 0 ∧
    muTam S.C.Q' S.C.hQ' (fun _ => 1) (refSetOf S h0) ≠ ∞ :=
  (OrbitSection.exists_pos_lt_top (muTam S.C.Q' S.C.hQ' fun _ => 1) h0).choose_spec

/-- **The measure on the adelic sphere**: the quotient of `muTam Q₀ 1` by `muTam Q' 1` (as `sphereMeasure`, for any
complement with `muTam Q' 1 ≠ 0`). -/
def sphereMeasureOf : Measure (adelicSphere Q₀ ρ) :=
  quotMeasure (S.coordEquiv hρ) (muTam Q₀ hQ fun _ => 1) (refSetOf S h0) (muTam S.C.Q' S.C.hQ' fun _ => 1)

/-- The adelic sphere data with `sphereMeasureOf`. -/
def sphereDataOf : AdelicSphereData Q₀ ρ S.C.Q' where
  ξ := S.ξ
  ι := S.iota
  T := adelicSphere Q₀ ρ
  σ := sphereMeasureOf S hρ hQ h0
  coord := S.coordEquiv hρ

include hQ in
/-- **Weil's adelic fibration over the sphere** for any complement with `muTam Q' 1 ≠ 0`. -/
theorem sphereFibrationOf : AdelicSphereFibration Q₀ hQ S.C.hQ' (sphereDataOf S hρ hQ h0) := by
  have hμ' := isFiniteMeasureOnCompacts_muTam' S.C.Q' S.C.hQ' (fun _ => 1)
  have hspec := refSetOf_spec S h0
  have hμ : ∀ (h' : SOAdele S.C.Q') (E : Set (SOAdele Q₀)), MeasurableSet E →
      muTam Q₀ hQ (fun _ => 1) ((fun g => S.iota h' * g) ⁻¹' E) = muTam Q₀ hQ (fun _ => 1) E :=
    fun h' E _ => measure_preimage_mul _ _ _
  refine ⟨fun x h h' => S.coordFun_mul hρ x h h', fun x h => S.coordFun_inv_smul hρ (x, h),
    fun h hh => S.iota_mem_gamma hh, fun γ hγ hfix => S.exists_iota_gamma hρ hγ hfix, ?_, ?_⟩
  · have := sigmaFinite_quotMeasure (S.coordEquiv hρ) S.iota (fun x h h' => S.coordFun_mul hρ x h h')
      (muTam Q₀ hQ fun _ => 1) hμ (muTam S.C.Q' S.C.hQ' fun _ => 1) h0 hspec.1 hspec.2.1
      hspec.2.2 (S.coverSet hρ) (S.measurableSet_coverSet hρ) (S.iUnion_coverSet hρ) (S.coverSet_fin hρ hQ)
    show SFinite (sphereMeasureOf S hρ hQ h0)
    unfold sphereMeasureOf
    infer_instance
  · exact map_prod_quotMeasure (S.coordEquiv hρ) S.iota (fun x h h' => S.coordFun_mul hρ x h h')
      (muTam Q₀ hQ fun _ => 1) hμ (muTam S.C.Q' S.C.hQ' fun _ => 1) h0 hspec.1 hspec.2.1
      hspec.2.2 (S.coverSet hρ) (S.measurableSet_coverSet hρ) (S.iUnion_coverSet hρ) (S.coverSet_fin hρ hQ)

end SphereOf

/-! ### The induction step with a given sphere measure -/

section StepWith

variable {k r n' : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F} (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)
  (hQ : Q₀.Nondegenerate) (σ₀ : Measure (adelicSphere Q₀ ρ)) [SFinite σ₀]
  (hfib₀ : muTam Q₀ hQ 1 = (σ₀.prod (muTam S.C.Q' S.C.hQ' 1)).map (S.orbitCoord hρ).coord)
  (Ξ : Fin (r + 1) → Fin (k + 1) → F) (hΞ0 : S.ξ.1 = Ξ 0)
  (hperp : ∀ j : Fin r, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian S.ξ.1 (Ξ j.succ) = 0)
  (D' : FrameTower S.C.Q' S.C.hQ' n' fun j : Fin r => S.complRat (Ξ j.succ))

include hfib₀ in
theorem stepWith_fib :
    haveI := D'.sFinite
    muTam Q₀ hQ 1 = ((σ₀.prod D'.σ).prod (muTam D'.Q'' D'.hQ'' 1)).map (stepC S hρ Ξ hΞ0 hperp D').coord := by
  have := D'.sFinite
  have h0 : muTam Q₀ hQ 1 = (1 : ℝ≥0∞) • (σ₀.prod (muTam S.C.Q' S.C.hQ' 1)).map (S.orbitCoord hρ).coord := by
    rw [one_smul]; exact hfib₀
  have h1 : muTam S.C.Q' S.C.hQ' 1 = (1 : ℝ≥0∞) • (D'.σ.prod (muTam D'.Q'' D'.hQ'' 1)).map D'.C.coord := by
    rw [one_smul]; exact D'.fib
  have := fib_compose (S.orbitCoord hρ) S.complA (step_he S) D'.C h0 h1
  rwa [one_mul, one_smul] at this

include hfib₀ in
/-- **The induction step** of `FrameTower.step`, from any sphere measure $\sigma_0$ with Weil's fibration identity. -/
def FrameTower.stepWith : FrameTower Q₀ hQ n' Ξ :=
  haveI := D'.sFinite
  { Q'' := D'.Q''
    hQ'' := D'.hQ''
    ιInf := stepInf S Ξ D'
    ιFin := stepFin S Ξ D'
    measurable_ιInf := ((measurable_pi_iff.mpr fun w => (S.measurable_iotaR w).comp (measurable_pi_apply w)).comp
        measurable_fst).prodMk
      ((measurable_pi_iff.mpr fun w => (S.measurable_iotaC w).comp (measurable_pi_apply w)).comp
        measurable_snd) |>.comp D'.measurable_ιInf
    continuous_ιInf := (((continuous_pi fun w => (S.continuous_iotaR w).comp (continuous_apply w)).comp
        continuous_fst).prodMk
      ((continuous_pi fun w => (S.continuous_iotaC w).comp (continuous_apply w)).comp continuous_snd)).comp
        D'.continuous_ιInf
    T := adelicSphere Q₀ ρ × D'.T
    σ := σ₀.prod D'.σ
    τ := composeτ (S.orbitCoord hρ) S.complA D'.τ
    C := stepC S hρ Ξ hΞ0 hperp D'
    sFinite := inferInstance
    fib := stepWith_fib S hρ hQ σ₀ hfib₀ Ξ hΞ0 hperp D'
    gamma_mem := step_gamma_mem S Ξ D'
    stabΓ := step_stabΓ S hρ Ξ hΞ0 hperp D'
    stab := step_stab S hρ Ξ hΞ0 hperp D'
    Cm := S.Gc * D'.Cm
    hCR := step_hCR S Ξ D'
    hCC := step_hCC S Ξ D'
    hCV := step_hCV S Ξ D'
    hCH := step_hCH S Ξ D'
    hΞC := step_hΞC S Ξ hΞ0 hperp D' }

end StepWith

/-! ### Existence of frame coordinates with a binary anisotropic complement -/

/-- **Frame coordinates for an orthogonal rational frame with anisotropic binary complement** ($N = r + 2$). -/
theorem nonempty_frameTower_rank2 :
    ∀ (r : ℕ) {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (_hN : N = r + 2)
      (Ξ : Fin r → Fin N → F)
      (_horth : ∀ i j, i ≠ j → bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ i) (Ξ j) = 0)
      (_hne : ∀ j, qF Q₀ (Ξ j) ≠ 0) (_hW : ComplAnisotropic Q₀ Ξ), Nonempty (FrameTower Q₀ hQ 2 Ξ) := by
  intro r
  induction r with
  | zero =>
    intro N Q₀ hQ hN Ξ _ _ _
    obtain rfl : N = 2 := by omega
    exact ⟨FrameTower.base Q₀ hQ Ξ⟩
  | succ r ih =>
    intro N Q₀ hQ hN Ξ horth hne hW
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨r + 2, by omega⟩
    have hρ : qF Q₀ (Ξ 0) ≠ 0 := hne 0
    obtain ⟨Cc⟩ := exists_sphereComplement Q₀ hQ (Ξ 0) hρ
    have hdet : (Q₀.map (algebraMap (𝓞 F) F)).hessian.det ≠ 0 := by
      rw [Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ
    have hx₀ : qH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ 0) ≠ 0 := by
      rw [qH_hessian]; exact mul_ne_zero two_ne_zero hρ
    obtain ⟨w, hw, hworth⟩ := exists_orth_anisotropic (H := (Q₀.map (algebraMap (𝓞 F) F)).hessian)
      (hessian_transpose Q₀) two_ne_zero hdet (by omega) hx₀
    obtain ⟨S, hS⟩ : ∃ S : AdelicSphereSetup Q₀ (qF Q₀ (Ξ 0)), S.ξ.1 = Ξ 0 :=
      ⟨⟨⟨Ξ 0, rfl⟩, Cc, w, hw, hworth⟩, rfl⟩
    have hperp : ∀ j : Fin r, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian S.ξ.1 (Ξ j.succ) = 0 := by
      rw [hS]; exact bH_cols_zero horth
    have horth' : ∀ i j : Fin r, i ≠ j →
        bH (S.C.Q'.map (algebraMap (𝓞 F) F)).hessian (S.complRat (Ξ i.succ)) (S.complRat (Ξ j.succ)) = 0 := by
      intro i j hij
      rw [S.bH_complRat (hperp i) (hperp j)]
      exact horth _ _ (fun h => hij (Fin.succ_injective _ h))
    have hne' : ∀ j : Fin r, qF S.C.Q' (S.complRat (Ξ j.succ)) ≠ 0 := fun j => by
      rw [S.qF_complRat (hperp j)]; exact hne _
    have hW' := complAnisotropic_complRat S Ξ hS hperp hW
    obtain ⟨D'⟩ := ih S.C.Q' S.C.hQ' (by omega) (fun j => S.complRat (Ξ j.succ)) horth' hne' hW'
    -- `muTam Q' 1 ≠ 0`: for `k ≥ 3` as before; for `k = 2` (the last step) by anisotropy
    have h0 : muTam S.C.Q' S.C.hQ' (fun _ => 1) ≠ 0 := by
      by_cases hk : 3 ≤ k
      · exact muTam_ne_zero S.C.Q' S.C.hQ' hk
      · obtain rfl : k = 2 := by omega
        obtain rfl : r = 0 := by omega
        exact muTam_one_ne_zero_of_anisotropicF S.C.Q' S.C.hQ'
          ((complAnisotropic_zero_iff S.C.Q' _).1 hW')
    have : SFinite (sphereMeasureOf S hρ hQ h0) := (sphereFibrationOf S hρ hQ h0).sFinite
    exact ⟨FrameTower.stepWith S hρ hQ (sphereMeasureOf S hρ hQ h0) (sphereFibrationOf S hρ hQ h0).fib Ξ hS
      hperp D'⟩

/-- **Every rational frame of $T_0$ has frame coordinates with complement of rank $2$** when
$\delta = -\det H_{Q_0}\det H_{T_0}$ is not a square in $F$ (i.e. the orthogonal complement is anisotropic). -/
theorem nonempty_frameTower_ratFrame_rank2 {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (hW : ¬ IsSquare (algebraMap (𝓞 F) F (QuadFormsKB.Tamagawa.Frames.deltaForms Q₀ T₀))) (X : RatFrame Q₀ T₀) :
    Nonempty (FrameTower Q₀ hQ 2 (cols X.1)) := by
  obtain ⟨P, dg, hP, hdg, hPd⟩ := QuadFormsKB.Tamagawa.Frames.exists_diag_global T₀ hT
  set f := algebraMap (𝓞 F) F with hf
  set PF : Matrix (Fin r) (Fin r) F := P.map f with hPF
  have hdet : IsUnit PF.det := by
    rw [isUnit_iff_ne_zero, hPF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hP
  have hG : (Q₀.map f).compMat (X.1 * PF) = (QuadForm.diag dg).map f := by
    rw [← QuadFormsKB.QuadForm.compMat_mul, X.2, hPF, QuadFormsKB.QuadForm.map_compMat, hPd]
  have hcols : frameMul (cols X.1) PF = cols (X.1 * PF) := by
    funext j i
    simp only [frameMul, cols, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hdiag : ∀ i j, i ≠ j →
      bH (Q₀.map f).hessian (cols (X.1 * PF) i) (cols (X.1 * PF) j) = 0 := by
    intro i j hij
    have h1 := congrArg (fun G => QuadForm.hessian G i j) hG
    simp only [QuadFormsKB.QuadForm.hessian_compMat] at h1
    have h2 := QuadFormsKB.QuadForm.transpose_mul_mul_apply (Q₀.map f).hessian (X.1 * PF) i j
    unfold bH
    rw [show (cols (X.1 * PF) i) = fun l => (X.1 * PF) l i from rfl, show (cols (X.1 * PF) j) =
      fun l => (X.1 * PF) l j from rfl, ← h2, h1, QuadFormsKB.QuadForm.hessian_map]
    simp [QuadFormsKB.Tamagawa.Frames.hessian_diag, hij]
  have hne : ∀ j, qF Q₀ (cols (X.1 * PF) j) ≠ 0 := by
    intro j
    have := QuadFormsKB.Tamagawa.Frames.eval_col_of_compMat (Q₀.map f) hG j
    show (Q₀.map f).eval (fun i => (X.1 * PF) i j) ≠ 0
    rw [this]
    simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply]
    simp only [Matrix.diagonal_apply_eq]
    exact (map_ne_zero_iff f RingOfIntegers.coe_injective).mpr (hdg j)
  have hWX : ComplAnisotropic Q₀ (cols (X.1 * PF)) := by
    rw [← hcols, complAnisotropic_frameMul_iff Q₀ _ PF hdet]
    exact (complAnisotropic_iff Q₀ T₀ hT X).2 hW
  obtain ⟨D⟩ := nonempty_frameTower_rank2 r Q₀ hQ rfl (cols (X.1 * PF)) hdiag hne hWX
  have hinv : IsUnit PF⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hdet
  have e : frameMul (cols (X.1 * PF)) PF⁻¹ = cols X.1 := by
    rw [← hcols, frameMul_mul, Matrix.mul_nonsing_inv _ hdet, frameMul_one]
  exact ⟨e ▸ D.transport PF⁻¹ hinv⟩

end QuadFormsKB.Tamagawa.Indefinite
