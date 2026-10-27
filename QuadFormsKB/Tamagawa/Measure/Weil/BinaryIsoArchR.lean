import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchSplit
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchReal
import QuadFormsKB.LocalDensity.FormDensityHyperbolic

/-!
# The Leray measure of $SO(x_0x_1)(\mathbb R)\cong\mathbb R^\times$
**Layer:** one real place. $H = x_0x_1$ (`DVR.hyperbolic ℝ`), $SO(H)(\mathbb R) = \{\mathrm{diag}(t,t^{-1})\}$.

**Proves** **`lerayMeasure_hypR_image`**: for every measurable $J\subseteq\mathbb R$,
$$\mu_H\bigl(\{\mathrm{diag}(e^s,e^{-s}) : s\in J\}\bigr) = \mathrm{vol}(J),$$
i.e. the Leray (gauge-form) measure of $SO(H)(\mathbb R)$ is $dt/|t|$ under $\mathrm{diag}(t,t^{-1})\mapsto t$ (on $t > 0$).
*Proof.* The similarity $H\circ G = x_0^2 - x_1^2$, $G = \begin{pmatrix}1&1\\1&-1\end{pmatrix}$, conjugates
$\mathrm{diag}(e^s,e^{-s})$ to the hyperbolic rotation $\rho(\cosh s,\sinh s)$ and multiplies the Leray measure by
$|\det G|^3 = 8$ (`map_lerayMeasure_conjSO'`); the Leray measure of the rotations by an arc of the hyperbola is
$\mathrm{vol}(J)/8$ (`lerayMeasure_rotSec_hypArc`, $\delta = 1$). The same statement for any real form equal to $H$
(`lerayMeasure_setHypR_of_eq`), as needed at the real places of a number field.
-/

open MeasureTheory Measure Set Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.LocalDensity

/-- $G = \begin{pmatrix}1&1\\1&-1\end{pmatrix}$, with $H\circ G = x_0^2 - x_1^2$. -/
def hypG (K : Type*) [Field K] [NeZero (2 : K)] : GL (Fin 2) K :=
  ⟨!![1, 1; 1, -1], !![1 / 2, 1 / 2; 1 / 2, -1 / 2], by
    have h2 : (2 : K) ≠ 0 := NeZero.ne 2
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring,
   by
    have h2 : (2 : K) ≠ 0 := NeZero.ne 2
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring⟩

theorem hypG_val (K : Type*) [Field K] [NeZero (2 : K)] :
    ((hypG K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, -1] := rfl

theorem hypG_inv_val (K : Type*) [Field K] [NeZero (2 : K)] :
    (((hypG K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1 / 2, 1 / 2; 1 / 2, -1 / 2] := rfl

theorem hessian_hyperbolic (K : Type*) [CommRing K] : (DVR.hyperbolic K).hessian = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [DVR.hyperbolic, QuadForm.hessian, QuadForm.ofUpper]

theorem hessian_diag_one_neg_one (K : Type*) [CommRing K] :
    (QuadForm.diag ![1, -1] : QuadForm K 2).hessian = !![2, 0; 0, -2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QuadForm.diag, QuadForm.hessian] <;> ring

/-- $(x_0^2-x_1^2) = 1\cdot(H\circ G)$ on Hessians. -/
theorem hessian_hyp_conj (K : Type*) [Field K] [NeZero (2 : K)] :
    (QuadForm.diag ![1, -1] : QuadForm K 2).hessian =
      (1 : K) • (((hypG K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ * (DVR.hyperbolic K).hessian *
        ((hypG K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  rw [hessian_diag_one_neg_one, hessian_hyperbolic, hypG_val, one_smul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem gramDetR_hyperbolic : gramDetR (DVR.hyperbolic ℝ) ≠ 0 := by
  rw [gramDetR, hessian_hyperbolic, Matrix.det_fin_two_of]; norm_num

/-- $\mathrm{diag}(e^s, e^{-s})\in SO(H)(\mathbb R)$. -/
def diagGLR (s : ℝ) : GL (Fin 2) ℝ :=
  ⟨!![Real.exp s, 0; 0, Real.exp (-s)], !![Real.exp (-s), 0; 0, Real.exp s], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add],
   by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]⟩

theorem diagGLR_mem (s : ℝ) : diagGLR s ∈ soReal (DVR.hyperbolic ℝ) := by
  rw [mem_soReal_iff, hessian_hyperbolic]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [diagGLR, Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  · simp [diagGLR, Matrix.det_fin_two, ← Real.exp_add]

/-- $s\mapsto\mathrm{diag}(e^s,e^{-s})$, $\mathbb R\to SO(H)(\mathbb R)$. -/
def diagSOR (s : ℝ) : ArchSO (DVR.hyperbolic ℝ) := ⟨diagGLR s, diagGLR_mem s⟩

theorem mat_diagSOR (s : ℝ) :
    ArchSOInst.mat _ (diagSOR s) = !![Real.exp s, 0; 0, Real.exp (-s)] := rfl

theorem continuous_diagSOR : Continuous diagSOR := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · change Continuous fun s : ℝ => !![Real.exp s, 0; 0, Real.exp (-s)]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous fun s : ℝ => !![Real.exp (-s), 0; 0, Real.exp s]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem diagSOR_injective : Function.Injective diagSOR := fun s t h => by
  have := congrArg (fun g => ArchSOInst.mat _ g 0 0) h
  simpa [mat_diagSOR] using this

/-- **Conjugation by $G$ carries $\mathrm{diag}(e^s,e^{-s})$ to the hyperbolic rotation $\rho(\cosh s,\sinh s)$.** -/
theorem conjSO_diagSOR (s : ℝ) :
    conjSO (hypG ℝ) 1 (hessian_hyp_conj ℝ) one_ne_zero (diagSOR s) = rotSec (-1) (hypArc one_pos s) := by
  apply Subtype.ext; apply Units.ext
  change ((hypG ℝ)⁻¹ : GL (Fin 2) ℝ).val * !![Real.exp s, 0; 0, Real.exp (-s)] * (hypG ℝ).val =
    BinaryNormOne.rotMat (-1) (hypVec 1 s 0) (hypVec 1 s 1) 1
  rw [hypG_inv_val, hypG_val]
  simp only [hypVec, Real.sqrt_one, inv_one, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    BinaryNormOne.rotMat, Real.cosh_eq, Real.sinh_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The Leray measure of $SO(x_0x_1)(\mathbb R)$**: $\mu_H(\{\mathrm{diag}(e^s,e^{-s}) : s\in J\}) = \mathrm{vol}(J)$. -/
theorem lerayMeasure_hypR_image {J : Set ℝ} (hJ : MeasurableSet J) :
    lerayMeasure (DVR.hyperbolic ℝ) gramDetR_hyperbolic (diagSOR '' J) = volume J := by
  set φ := conjSO (hypG ℝ) 1 (hessian_hyp_conj ℝ) one_ne_zero with hφ
  have hmap := map_lerayMeasure_conjSO' (hypG ℝ) 1 (hessian_hyp_conj ℝ) one_ne_zero gramDetR_hyperbolic
    (gramDetR_diag_one_D_ne_zero (neg_ne_zero.mpr one_ne_zero))
  have hdet : |((hypG ℝ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| = 2 := by
    rw [hypG_val, Matrix.det_fin_two_of]; norm_num
  rw [hdet] at hmap
  have himg : φ '' (diagSOR '' J) = rotSec (-1) '' (hypArc one_pos '' J) := by
    rw [image_image, image_image]
    exact image_congr fun s _ => conjSO_diagSOR s
  have h1 : lerayMeasure (DVR.hyperbolic ℝ) gramDetR_hyperbolic (diagSOR '' J) =
      ((lerayMeasure (DVR.hyperbolic ℝ) gramDetR_hyperbolic).map φ) (φ '' (diagSOR '' J)) := by
    rw [show (φ : ArchSO (DVR.hyperbolic ℝ) → ArchSO (QuadForm.diag ![1, -1])) =
      φ.toHomeomorph.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply]
    congr 1
    exact (φ.injective.preimage_image _).symm
  rw [h1, hmap, Measure.smul_apply, himg, lerayMeasure_rotSec_hypArc one_pos hJ, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The set $\{g\in SO(Q)(\mathbb R) : g = \mathrm{diag}(e^s,e^{-s}),\ s\in J\}$ for a real binary form $Q$. -/
def setHypR (Q : QuadForm ℝ 2) (J : Set ℝ) : Set (ArchSO Q) :=
  {g | ∃ s ∈ J, ArchSOInst.mat Q g = !![Real.exp s, 0; 0, Real.exp (-s)]}

theorem setHypR_hyperbolic (J : Set ℝ) : setHypR (DVR.hyperbolic ℝ) J = diagSOR '' J := by
  ext g
  constructor
  · rintro ⟨s, hs, hg⟩
    refine ⟨s, hs, Subtype.ext (Units.ext ?_)⟩
    exact (mat_diagSOR s).trans hg.symm
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, mat_diagSOR s⟩

theorem measurableSet_setHypR {Q : QuadForm ℝ 2} (hQe : Q = DVR.hyperbolic ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (setHypR Q J) := by
  subst hQe
  rw [setHypR_hyperbolic]
  exact (continuous_diagSOR.measurableEmbedding diagSOR_injective).measurableSet_image.mpr hJ

/-- **The Leray measure of $SO(Q)(\mathbb R)$ for any real form $Q = x_0x_1$**:
$\mu_Q(\{\mathrm{diag}(e^s,e^{-s}) : s\in J\}) = \mathrm{vol}(J)$. -/
theorem lerayMeasure_setHypR_of_eq {Q : QuadForm ℝ 2} (hQe : Q = DVR.hyperbolic ℝ) (hQ : gramDetR Q ≠ 0)
    {J : Set ℝ} (hJ : MeasurableSet J) : lerayMeasure Q hQ (setHypR Q J) = volume J := by
  subst hQe
  rw [setHypR_hyperbolic]
  exact lerayMeasure_hypR_image hJ

end QuadFormsKB.Tamagawa.Measure.Weil
