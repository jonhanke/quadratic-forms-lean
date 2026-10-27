import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling
import QuadFormsKB.Tamagawa.Measure.Weil.Ideles

/-!
# The measure $dw$ on the unipotent radical $N \cong V'$, adelically

In the cone orbital identities (`ConeRealOrbit.lean`, `ConeComplexOrbit.lean`, `ConeFiniteOrbit.lean`) the unipotent radical
$N \cong V' = F^k$ of the stabilizer of the isotropic vector carries, at every place $v$, the **coordinate measure**
$dw_v$: Lebesgue measure $dw$ at a real place, $d^2w = dx\,dy$ per coordinate at a complex place, and the Haar measure with
$\mathrm{vol}(\mathcal O_v^k) = 1$ at a finite place. This file compares their product with the self-dual measure of
the adelic additive group.

* `dwA F` $= dx_\infty \otimes \mu_{\hat{\mathcal O}}$ on $\mathbb A_F$ (Lebesgue on $F_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$,
  Haar on $\mathbb A_f$ with $\mathrm{vol}(\hat{\mathcal O}) = 1$), `dwVec F k` its $k$-th power on $\mathbb A_F^k$.
* **`muAdd_eq_smul_dwA`**: the self-dual measure is $\mu_{\mathbb A} = 2^{r_2}|d_F|^{-1/2}\,dw_{\mathbb A}$ (the
  `muAdd`: $2^{r_2}$ from $|dz\wedge d\bar z| = 2\,dx\,dy$ at the complex places, $|d_F|^{-1/2}$ from
  $\prod_v\mathrm{vol}_{\mathrm{sd}}(\mathcal O_v)$), hence `muAddVec_eq_smul_dwVec`.
* **`addCovolume_dwTam`**: for the normalized measure $dw^{\mathrm{Tam}} = (2^{r_2}|d_F|^{-1/2})^k\,dw_{\mathbb A}$,
  $\mathrm{vol}(V'_{\mathbb A}/V'_F) = 1$; equivalently `addCovolume_dwVec`:
  $\mathrm{vol}(\mathbb A^k/F^k,\ \prod_v dw_v) = (2^{-r_2}|d_F|^{1/2})^k$.
* **`map_mulVec_muAddVec_rat`** (the Gram determinant): for $H \in GL_k(F)$ (e.g. the Gram matrix of $Q'$), $x \mapsto Hx$
  preserves $\mu_{\mathbb A^k}$, because $\|\det H\|_{\mathbb A} = 1$ (product formula). The self-dual measure of $V'_{\mathbb A}$
  for the pairing $\psi(B_{Q'}(x, y)) = \psi(x\cdot Hy)$ is the self-dual measure for $\psi(x\cdot y)$ transported by $H$,
  times $\|\det H\|_{\mathbb A}^{1/2}$, so it is again $\mu_{\mathbb A^k}$: **the self-dual measure of $V'_{\mathbb A}$ for
  $B_{Q'}$ is $dw^{\mathrm{Tam}}$, with $\mathrm{vol}(V'_{\mathbb A}/V'_F) = 1$**, whatever the Gram determinant.
-/

open MeasureTheory Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeAdelic

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa.Measure.Weil NumberField.mixedEmbedding
open NumberField.InfinitePlace

variable (F : Type) [Field F] [NumberField F]

/-- **The coordinate measure on $\mathbb A_F$**: Lebesgue measure on $F_\infty$ (with $dx\,dy$ on each $\mathbb C$) times the
Haar measure of $\mathbb A_f$ with $\mathrm{vol}(\hat{\mathcal O}) = 1$, i.e. the product of the local measures $dw_v$. -/
def dwA : Measure (Adeles F) :=
  (((2 : ℝ≥0) ^ nrComplexPlaces F)⁻¹ • Analysis.selfDualInf (F := F)).prod (Measure.addHaarMeasure (OHatCompacts F))

/-- The constant $2^{r_2}|d_F|^{-1/2}$. -/
def dwConst : ℝ := (2 : ℝ) ^ nrComplexPlaces F * ohatVol F

theorem dwConst_pos : 0 < dwConst F := by
  unfold dwConst ohatVol
  have := sqrt_abs_discr_pos (F := F)
  positivity

/-- **The self-dual measure is $2^{r_2}|d_F|^{-1/2}$ times the product of the local coordinate measures.** -/
theorem muAdd_eq_smul_dwA : muAdd F = ENNReal.ofReal (dwConst F) • dwA F := by
  have h2 : ((2 : ℝ≥0) ^ nrComplexPlaces F) ≠ 0 := pow_ne_zero _ two_ne_zero
  have e1 : Analysis.selfDualInf (F := F) =
      ((2 : ℝ≥0) ^ nrComplexPlaces F) • (((2 : ℝ≥0) ^ nrComplexPlaces F)⁻¹ • Analysis.selfDualInf (F := F)) := by
    rw [smul_smul, mul_inv_cancel₀ h2, one_smul]
  rw [muAdd, muFin, dwA, Measure.prod_smul_right]
  conv_lhs => rw [e1, Measure.prod_smul_left]
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  have h2' : (((2 : ℝ≥0) ^ nrComplexPlaces F : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces F) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h2', dwConst, ENNReal.ofReal_mul (by positivity)]
  ring

/-- The coordinate measure on $\mathbb A_F^k$. -/
def dwVec (k : ℕ) : Measure (AdeleSpace F (Fin k)) := Measure.pi fun _ : Fin k => dwA F

instance : SigmaFinite (dwA F) := by unfold dwA; infer_instance

instance : (dwA F).IsAddHaarMeasure := by
  unfold dwA
  have : (((2 : ℝ≥0) ^ nrComplexPlaces F)⁻¹ • Analysis.selfDualInf (F := F)).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.nnreal_smul _ (inv_ne_zero (pow_ne_zero _ two_ne_zero))
  infer_instance

instance (k : ℕ) : (dwVec F k).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

theorem muAddVec_eq_smul_dwVec (k : ℕ) :
    muAddVec F (Fin k) = ENNReal.ofReal (dwConst F) ^ k • dwVec F k := by
  rw [muAddVec, dwVec]
  refine Measure.pi_eq (μ := fun _ : Fin k => muAdd F) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp_rw [muAdd_eq_smul_dwA F, Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The Tamagawa-normalized measure on $V' = F^k$**: $dw^{\mathrm{Tam}} = (2^{r_2}|d_F|^{-1/2})^k\prod_v dw_v$. -/
def dwTam (k : ℕ) : Measure (AdeleSpace F (Fin k)) := ENNReal.ofReal (dwConst F) ^ k • dwVec F k

/-- **$\mathrm{vol}(V'_{\mathbb A}/V'_F) = 1$ for $dw^{\mathrm{Tam}}$** (it is the self-dual measure). -/
@[kb "weil1982" "§2.1 (the self-dual measure, vol(A/k) = 1) [unverified page]; tate1950 Thm 4.1.2"]
theorem addCovolume_dwTam (k : ℕ) : addCovolume (diagVecSub F (Fin k)) (AdeleSpace F (Fin k)) (dwTam F k) = 1 := by
  rw [dwTam, ← muAddVec_eq_smul_dwVec]
  exact addCovolume_muAddVec (F := F) (ι := Fin k)

/-- **The covolume of the product of the local coordinate measures**: $\mathrm{vol}(\mathbb A^k/F^k, \prod_v dw_v) =
(2^{r_2}|d_F|^{-1/2})^{-k}$. -/
theorem addCovolume_dwVec (k : ℕ) :
    addCovolume (diagVecSub F (Fin k)) (AdeleSpace F (Fin k)) (dwVec F k) = (ENNReal.ofReal (dwConst F) ^ k)⁻¹ := by
  have hc0 : ENNReal.ofReal (dwConst F) ^ k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr (dwConst_pos F)).ne'
  have hct : ENNReal.ofReal (dwConst F) ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [(isAddFundamentalDomain_fundDomVec (dwVec F k)).covolume_eq_volume]
  have h := muAddVec_fundDomVec (F := F) (ι := Fin k)
  rw [muAddVec_eq_smul_dwVec, Measure.smul_apply, smul_eq_mul] at h
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)

/-- **The Gram determinant does not change the self-dual measure** (product formula): for $H \in GL_k(F)$, acting
diagonally on $\mathbb A_F^k$, $H_*\mu_{\mathbb A^k} = \mu_{\mathbb A^k}$ (`map_mulVec_muAddVec` with
$\|\det H\|_{\mathbb A} = 1$). Applied to the Gram matrix $H$ of $Q'$: the self-dual measure for $\psi(x\cdot Hy)$, which is
$\|\det H\|_{\mathbb A}^{1/2}$ times the transport of $\mu_{\mathbb A^k}$, is $\mu_{\mathbb A^k} = dw^{\mathrm{Tam}}$. -/
@[kb "weil1982" "§2.1 (self-dual measures; product formula, Thm 2.3.1) [unverified page]"]
theorem map_mulVec_muAddVec_rat {k : ℕ} (H : GL (Fin k) F) :
    Measure.map (((Matrix.GeneralLinearGroup.map (diagRing F) H : GL (Fin k) (Adeles F)) :
      Matrix (Fin k) (Fin k) (Adeles F))).mulVec (muAddVec F (Fin k)) = muAddVec F (Fin k) := by
  rw [map_mulVec_muAddVec]
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (diagRing F) H) =
      diagUnits F (Matrix.GeneralLinearGroup.det H) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagUnits_val]
    exact (RingHom.map_det (diagRing F) (H : Matrix (Fin k) (Fin k) F)).symm
  rw [hdet, ideleNorm_diagUnits, inv_one, ENNReal.ofReal_one, one_smul]

end QuadFormsKB.Tamagawa.Measure.ConeAdelic
