import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoArchR
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoArchC
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoHyp
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchComplex
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSShellRatio

/-!
# The archimedean comparison for the hyperbolic plane
**Layer:** a number field $F$, $H = x_0x_1$ (`hypForm F`), $\Phi_\infty$ = `hypInfEquiv F` :
$F_\infty^\times\cong SO(H)(F_\infty)$, $t\mapsto(\mathrm{diag}(t_w,t_w^{-1}))_w$.

**Proves**
* `lerayMeasureC_setHypC_of_eq`: at a complex place, $\mu_H(\{\mathrm{diag}(e^z,e^{-z}) : z\in J\}) = \mathrm{vol}(J)$ for
  measurable $J$ in the open square `isoSqC` (as `lerayMeasure_setHypR_of_eq` at real places: the similarity
  $H\circ G = x_0^2-x_1^2$ multiplies the complex Leray measure by $|\det G|_{\mathbb C}^3 = 64$, and the rotations by an
  arc of the complex hyperbola have measure $\mathrm{vol}(J)/64$);
* **`map_omegaInf_hypInfEquiv`**: $(\Phi_\infty)_*\omega_\infty = 2^{r_2}\,\mu^{\mathrm{Leray}}_\infty$, i.e.
  $(\Phi_\infty)_*\omega_\infty = |d_F|^{1/2}\cdot$`muArchTamSO H` (`map_omegaInf_hypInfEquiv_muArchTamSO`): the Leray measure of
  $SO(H)(\mathbb R)$ is $dt/|t|$ and that of $SO(H)(\mathbb C)$ is $d^2t/|t|^2$, while Weil's $\omega_\infty$ is
  $\prod dt/|t|\cdot\prod2\,d^2t/|t|^2$. *Proof:* both sides are Haar measures on $G_\infty$; they agree on the product set
  $\prod_{\mathrm{real}}\{\mathrm{diag}(e^s,e^{-s}) : 0<s<1\}\times\prod_{\mathrm{complex}}\{\mathrm{diag}(e^z,e^{-z}) : z\in\mathrm{isoSqC}\}$
  (`omegaInf_box` and `lintegral_exp_image_real/complex` on the $\omega_\infty$ side).
-/

open MeasureTheory Measure Set Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC QuadFormsKB.LocalDensity

/-! ### The complex places -/

section Complex

theorem gramDetC_hyperbolic : gramDetC (DVR.hyperbolic ℂ) ≠ 0 := by
  rw [gramDetC, gramC, hessian_hyperbolic, Matrix.det_smul, Matrix.det_fin_two_of]; norm_num

/-- $\mathrm{diag}(e^z, e^{-z})\in SO(H)(\mathbb C)$. -/
def diagGLC (z : ℂ) : GL (Fin 2) ℂ :=
  ⟨!![Complex.exp z, 0; 0, Complex.exp (-z)], !![Complex.exp (-z), 0; 0, Complex.exp z], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add],
   by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]⟩

theorem diagGLC_mem (z : ℂ) : diagGLC z ∈ soC (DVR.hyperbolic ℂ) := by
  rw [mem_soC_iff, gramC, hessian_hyperbolic]
  have hz : Complex.exp z * Complex.exp (-z) = 1 := by rw [← Complex.exp_add]; simp
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [diagGLC, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination (2⁻¹ : ℂ) * hz
  · simp [diagGLC, Matrix.det_fin_two, hz]

/-- $z\mapsto\mathrm{diag}(e^z,e^{-z})$, $\mathbb C\to SO(H)(\mathbb C)$. -/
def diagSOC (z : ℂ) : ArchSOC (DVR.hyperbolic ℂ) := ArchSOC.mk _ (diagGLC z) (diagGLC_mem z)

theorem mat_diagSOC (z : ℂ) : ArchSOC.mat _ (diagSOC z) = !![Complex.exp z, 0; 0, Complex.exp (-z)] := rfl

theorem continuous_diagSOC : Continuous diagSOC := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · change Continuous fun z : ℂ => !![Complex.exp z, 0; 0, Complex.exp (-z)]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous fun z : ℂ => !![Complex.exp (-z), 0; 0, Complex.exp z]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem diagSOC_injOn : InjOn diagSOC isoSqC := fun s hs t ht h => by
  have := congrArg (fun g => ArchSOC.mat _ g 0 0) h
  simp only [mat_diagSOC] at this
  exact exp_injOn_isoSqC hs ht (by simpa using this)

/-- **Conjugation by $G$ carries $\mathrm{diag}(e^z,e^{-z})$ to the rotation $\rho(\cosh z,\sinh z)$.** -/
theorem conjSOC_diagSOC (z : ℂ) :
    conjSOC (hypG ℂ) 1 (hessian_hyp_conj ℂ) one_ne_zero (diagSOC z) = rotSecC_iso (-1) (hypArcC z) := by
  apply Subtype.ext; apply Units.ext
  change ((hypG ℂ)⁻¹ : GL (Fin 2) ℂ).val * !![Complex.exp z, 0; 0, Complex.exp (-z)] * (hypG ℂ).val =
    !![hypVecC z 0, -((-1) * hypVecC z 1); hypVecC z 1, hypVecC z 0]
  rw [hypG_inv_val, hypG_val]
  simp only [hypVecC, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.cosh, Complex.sinh]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The Leray measure of $SO(x_0x_1)(\mathbb C)$**: $\mu_H(\{\mathrm{diag}(e^z,e^{-z}) : z\in J\}) = \mathrm{vol}(J)$. -/
theorem lerayMeasureC_hypC_image {J : Set ℂ} (hJ : MeasurableSet J) (hJs : J ⊆ isoSqC) :
    lerayMeasureC (DVR.hyperbolic ℂ) gramDetC_hyperbolic (diagSOC '' J) = volume J := by
  set φ := conjSOC (hypG ℂ) 1 (hessian_hyp_conj ℂ) one_ne_zero with hφ
  have hmap := map_lerayMeasureC_conjSOC' (hypG ℂ) 1 (hessian_hyp_conj ℂ) one_ne_zero gramDetC_hyperbolic
    (gramDetC_diag_one_D_ne_zero_iso (D := -1) (neg_ne_zero.mpr one_ne_zero))
  have hdet : ‖((hypG ℂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 2 := by
    rw [hypG_val, Matrix.det_fin_two_of]; norm_num
  rw [hdet] at hmap
  have himg : φ '' (diagSOC '' J) = rotSecC_iso (-1) '' (hypArcC '' J) := by
    rw [image_image, image_image]
    exact image_congr fun s _ => conjSOC_diagSOC s
  have h1 : lerayMeasureC (DVR.hyperbolic ℂ) gramDetC_hyperbolic (diagSOC '' J) =
      ((lerayMeasureC (DVR.hyperbolic ℂ) gramDetC_hyperbolic).map φ) (φ '' (diagSOC '' J)) := by
    rw [show (φ : ArchSOC (DVR.hyperbolic ℂ) → ArchSOC QH) = φ.toHomeomorph.toMeasurableEquiv from rfl,
      MeasurableEquiv.map_apply]
    congr 1
    exact (φ.injective.preimage_image _).symm
  rw [h1, hmap, Measure.smul_apply, himg, lerayMeasureC_rotSecC_hypArc hJ hJs, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The set $\{g\in SO(Q)(\mathbb C) : g = \mathrm{diag}(e^z,e^{-z}),\ z\in J\}$. -/
def setHypC (Q : QuadForm ℂ 2) (J : Set ℂ) : Set (ArchSOC Q) :=
  {g | ∃ z ∈ J, ArchSOC.mat Q g = !![Complex.exp z, 0; 0, Complex.exp (-z)]}

theorem setHypC_hyperbolic (J : Set ℂ) : setHypC (DVR.hyperbolic ℂ) J = diagSOC '' J := by
  ext g
  constructor
  · rintro ⟨z, hz, hg⟩
    refine ⟨z, hz, Subtype.ext (Units.ext ?_)⟩
    exact (mat_diagSOC z).trans hg.symm
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, mat_diagSOC z⟩

theorem measurableSet_setHypC {Q : QuadForm ℂ 2} (hQe : Q = DVR.hyperbolic ℂ) {J : Set ℂ} (hJ : MeasurableSet J)
    (hJs : J ⊆ isoSqC) : MeasurableSet (setHypC Q J) := by
  subst hQe
  rw [setHypC_hyperbolic]
  exact hJ.image_of_continuousOn_injOn continuous_diagSOC.continuousOn (diagSOC_injOn.mono hJs)

/-- **The Leray measure of $SO(Q)(\mathbb C)$ for any complex form $Q = x_0x_1$**. -/
theorem lerayMeasureC_setHypC_of_eq {Q : QuadForm ℂ 2} (hQe : Q = DVR.hyperbolic ℂ) (hQ : gramDetC Q ≠ 0)
    {J : Set ℂ} (hJ : MeasurableSet J) (hJs : J ⊆ isoSqC) : lerayMeasureC Q hQ (setHypC Q J) = volume J := by
  subst hQe
  rw [setHypC_hyperbolic]
  exact lerayMeasureC_hypC_image hJ hJs

end Complex

/-! ### All archimedean places: $(\Phi_\infty)_*\omega_\infty = 2^{r_2}\mu^{\mathrm{Leray}}_\infty$ -/

section Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding QuadFormsKB.Tamagawa.Measure.LerayArch
  QuadFormsKB.Tamagawa.Measure.LerayReal

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_isoSqC : IsOpen isoSqC :=
  (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem QRe_hypForm (w : {w : InfinitePlace F // w.IsReal}) : QRe (hypForm F) w = DVR.hyperbolic ℝ := by
  rw [QRe, DVR.hyperbolic_map, DVR.hyperbolic_map]

theorem QCx_hypForm (w : {w : InfinitePlace F // w.IsComplex}) : QCx (hypForm F) w = DVR.hyperbolic ℂ := by
  rw [QCx, DVR.hyperbolic_map, DVR.hyperbolic_map]

variable (F) in
/-- The test set $\prod_{\mathrm{real}}\{\mathrm{diag}(e^s,e^{-s}) : 0<s<1\}\times
\prod_{\mathrm{complex}}\{\mathrm{diag}(e^z,e^{-z}) : z\in\mathrm{sqC}\}\subseteq G_\infty$. -/
def hypTestInf : Set (GInfSO (hypForm F)) :=
  (univ.pi fun w => setHypR (QRe (hypForm F) w) (Ioo 0 1)) ×ˢ (univ.pi fun w => setHypC (QCx (hypForm F) w) isoSqC)

theorem measurableSet_hypTestInf : MeasurableSet (hypTestInf F) :=
  (MeasurableSet.univ_pi fun w => measurableSet_setHypR (QRe_hypForm w) measurableSet_Ioo).prod
    (MeasurableSet.univ_pi fun w => measurableSet_setHypC (QCx_hypForm w) isOpen_isoSqC.measurableSet subset_rfl)

open Classical in
theorem muArchNF_hypTestInf :
    muArchNF ((hypForm F).map (algebraMap (𝓞 F) F)) (gramDetR_QRe_ne_zero _ nondegenerate_hypForm)
        (gramDetC_QCx_ne_zero _ nondegenerate_hypForm) (hypTestInf F) =
      volume isoSqC ^ nrComplexPlaces F := by
  have : ∀ w : {w : InfinitePlace F // w.IsReal},
      SigmaFinite (lerayMeasure (QRe (hypForm F) w) (gramDetR_QRe_ne_zero _ nondegenerate_hypForm w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero (hypForm F) nondegenerate_hypForm w); infer_instance
  have : ∀ w : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (lerayMeasureC (QCx (hypForm F) w) (gramDetC_QCx_ne_zero _ nondegenerate_hypForm w)) := fun w => by
    have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero (hypForm F) nondegenerate_hypForm w); infer_instance
  rw [muArchNF, muArchLeray, hypTestInf, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal},
      lerayMeasure (QRe (hypForm F) w) (gramDetR_QRe_ne_zero _ nondegenerate_hypForm w)
        (setHypR (QRe (hypForm F) w) (Ioo 0 1)) = 1 := fun w => by
    rw [lerayMeasure_setHypR_of_eq (QRe_hypForm w) _ measurableSet_Ioo, Real.volume_Ioo]; simp
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      lerayMeasureC (QCx (hypForm F) w) (gramDetC_QCx_ne_zero _ nondegenerate_hypForm w)
        (setHypC (QCx (hypForm F) w) isoSqC) = volume isoSqC := fun w =>
    lerayMeasureC_setHypC_of_eq (QCx_hypForm w) _ isOpen_isoSqC.measurableSet subset_rfl
  simp only [hR, hC, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ]

theorem mat_hypInfEquiv_fst (t : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ArchSOInst.mat _ ((hypInfEquiv F t).1 w) =
      !![(t : mixedSpace F).1 w, 0; 0, ((t⁻¹ : (mixedSpace F)ˣ) : mixedSpace F).1 w] := rfl

theorem mat_hypInfEquiv_snd (t : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    ArchSOC.mat _ ((hypInfEquiv F t).2 w) =
      !![(t : mixedSpace F).2 w, 0; 0, ((t⁻¹ : (mixedSpace F)ˣ) : mixedSpace F).2 w] := rfl

theorem exists_diag_eq_expR_iff {a b : ℝ} (hab : b * a = 1) (J : Set ℝ) :
    (∃ s ∈ J, !![a, 0; 0, b] = !![Real.exp s, 0; 0, Real.exp (-s)]) ↔ a ∈ Real.exp '' J := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (congrFun (congrFun h 0) 0).symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    have hb : b = Real.exp (-s) := by
      rw [Real.exp_neg]; exact eq_inv_of_mul_eq_one_left hab
    rw [hb]

theorem exists_diag_eq_expC_iff {a b : ℂ} (hab : b * a = 1) (J : Set ℂ) :
    (∃ s ∈ J, !![a, 0; 0, b] = !![Complex.exp s, 0; 0, Complex.exp (-s)]) ↔ a ∈ Complex.exp '' J := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (congrFun (congrFun h 0) 0).symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    have hb : b = Complex.exp (-s) := by
      rw [Complex.exp_neg]; exact eq_inv_of_mul_eq_one_left hab
    rw [hb]

theorem units_inv_mul_fst (t : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ((t⁻¹ : (mixedSpace F)ˣ) : mixedSpace F).1 w * (t : mixedSpace F).1 w = 1 := by
  exact congrArg (fun x : mixedSpace F => x.1 w) (Units.inv_mul t)

theorem units_inv_mul_snd (t : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    ((t⁻¹ : (mixedSpace F)ˣ) : mixedSpace F).2 w * (t : mixedSpace F).2 w = 1 := by
  exact congrArg (fun x : mixedSpace F => x.2 w) (Units.inv_mul t)

/-- $\Phi_\infty^{-1}$ of the test set is the box $\prod_{\mathrm{real}}\exp(0,1)\times\prod_{\mathrm{complex}}\exp(\mathrm{sqC})$. -/
theorem hypInfEquiv_preimage_hypTestInf :
    (hypInfEquiv F) ⁻¹' hypTestInf F =
      Units.val ⁻¹' infBoxSet (fun _ => Real.exp '' Ioo 0 1) (fun _ => Complex.exp '' isoSqC) := by
  ext t
  simp only [mem_preimage, hypTestInf, mem_prod, mem_univ_pi, infBoxSet]
  refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun w => ?_)
  · change (∃ s ∈ Ioo (0 : ℝ) 1, ArchSOInst.mat _ ((hypInfEquiv F t).1 w) = _) ↔ _
    rw [mat_hypInfEquiv_fst]
    exact exists_diag_eq_expR_iff (units_inv_mul_fst t w) _
  · change (∃ s ∈ isoSqC, ArchSOC.mat _ ((hypInfEquiv F t).2 w) = _) ↔ _
    rw [mat_hypInfEquiv_snd]
    exact exists_diag_eq_expC_iff (units_inv_mul_snd t w) _

theorem omegaInf_hypTestInf :
    omegaInf F ((hypInfEquiv F) ⁻¹' hypTestInf F) =
      (2 : ℝ≥0∞) ^ nrComplexPlaces F * volume isoSqC ^ nrComplexPlaces F := by
  have hJR : MeasurableSet (Real.exp '' Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.image_of_continuousOn_injOn Real.continuous_exp.continuousOn Real.exp_injective.injOn
  have hJC : MeasurableSet (Complex.exp '' isoSqC) :=
    isOpen_isoSqC.measurableSet.image_of_continuousOn_injOn Complex.continuous_exp.continuousOn exp_injOn_isoSqC
  rw [hypInfEquiv_preimage_hypTestInf, omegaInf_box (fun _ => hJR) (fun _ => hJC)
    (fun _ ⟨_, _, h⟩ => (Real.exp_pos _).ne' h) (fun _ ⟨_, _, h⟩ => Complex.exp_ne_zero _ h)]
  simp only [lintegral_exp_image_real measurableSet_Ioo, lintegral_exp_image_complex isOpen_isoSqC.measurableSet
    subset_rfl, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, one_mul, Finset.prod_const,
    Finset.card_univ]

theorem volume_isoSqC_ne_zero : volume isoSqC ≠ 0 :=
  (isOpen_isoSqC.measure_pos volume ⟨0, by simp [isoSqC]⟩).ne'

theorem volume_isoSqC_ne_top : volume isoSqC ≠ ⊤ := by
  refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : ℂ)) (r := 2)).ne (measure_mono fun z hz => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 + 1 := add_le_add hz.1.le hz.2.le
    _ = 2 := by norm_num

open Classical in
/-- **The archimedean comparison**: $(\Phi_\infty)_*\omega_\infty = 2^{r_2}\,\mu^{\mathrm{Leray}}_\infty$ on
$G_\infty = SO(x_0x_1)(F_\infty)$. -/
theorem map_omegaInf_hypInfEquiv :
    (omegaInf F).map (hypInfEquiv F) = (2 : ℝ≥0∞) ^ nrComplexPlaces F •
      muArchNF ((hypForm F).map (algebraMap (𝓞 F) F)) (gramDetR_QRe_ne_zero _ nondegenerate_hypForm)
        (gramDetC_QCx_ne_zero _ nondegenerate_hypForm) := by
  set μ := muArchNF ((hypForm F).map (algebraMap (𝓞 F) F)) (gramDetR_QRe_ne_zero _ nondegenerate_hypForm)
    (gramDetC_QCx_ne_zero _ nondegenerate_hypForm) with hμ
  have : μ.IsHaarMeasure := isHaarMeasure_muArchLeray _ _ _ _
  have h := isMulLeftInvariant_eq_smul ((omegaInf F).map (hypInfEquiv F)) μ
  set c := haarScalarFactor ((omegaInf F).map (hypInfEquiv F)) μ
  have hval := congrArg (fun m : Measure (GInfSO (hypForm F)) => m (hypTestInf F)) h
  simp only [Measure.smul_apply] at hval
  rw [show ((hypInfEquiv F) : (mixedSpace F)ˣ → GInfSO (hypForm F)) =
      (hypInfEquiv F).toHomeomorph.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply] at hval
  change omegaInf F ((hypInfEquiv F) ⁻¹' hypTestInf F) = _ at hval
  rw [omegaInf_hypTestInf, hμ, muArchNF_hypTestInf] at hval
  have hm0 : volume isoSqC ^ nrComplexPlaces F ≠ 0 := pow_ne_zero _ volume_isoSqC_ne_zero
  have hmT : volume isoSqC ^ nrComplexPlaces F ≠ ⊤ := ENNReal.pow_ne_top volume_isoSqC_ne_top
  have hc : (c : ℝ≥0∞) = 2 ^ nrComplexPlaces F := ((ENNReal.mul_left_inj hm0 hmT).mp hval).symm
  rw [h, ENNReal.smul_def, hc]

open Classical in
/-- **The archimedean comparison with Weil's normalization**: $(\Phi_\infty)_*\omega_\infty = |d_F|^{1/2}\cdot$
`muArchTamSO H` ($c_F = |d_F|^{-1/2}$ for $n = 2$, and Weil's factor $2^{r_2}$ at the complex places). -/
theorem map_omegaInf_hypInfEquiv_muArchTamSO :
    (omegaInf F).map (hypInfEquiv F) =
      (ENNReal.ofReal (ohatVol F))⁻¹ • muArchTamSO (hypForm F) nondegenerate_hypForm := by
  rw [map_omegaInf_hypInfEquiv, muArchTamSO, smul_smul, cF_two, cxWeil_two]
  congr 1
  have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have hs : 0 < Real.sqrt |(discr F : ℝ)| := Real.sqrt_pos.mpr hd
  have hrp : |(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) = (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
    rw [Real.rpow_neg hd.le, Real.sqrt_eq_rpow]
  have h0 : ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hs)).ne'
  rw [ohatVol, hrp, ENNReal.ofReal_mul (inv_pos.mpr hs).le, ← mul_assoc,
    ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_mul, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

end Global

end QuadFormsKB.Tamagawa.Measure.Weil
