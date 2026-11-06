/-
# Hanke 2005, §4.2: the Leray measure of $SO(q, r)$ along the fibres of $F_{\mathbb R}$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $\varphi_v = \mathrm{diag}[1_q, -1_r]$, $q = r + t$, as the repository form `phiQ r t` (`QuadForm.diag`), and
the repository's Leray (gauge-form) measure `lerayMeasure (phiQ r t)` on $SO(q, r)$ (coefficient coordinates; Hanke's
$\widetilde\omega_G$ uses Gram coordinates and is $2^{n(n-1)/2}$ times it).

**Proves** (all unconditional)
* `diagRev`: slice data for the Leray chart (`LerayReal.Diag`) with $P$ the reversal permutation, whose slice group is
  lower triangular (`mat_lower`);
* `lastCols_mul_lower` (with `zOf_mul_right`): right multiplication by a lower triangular $b$ does not change $F_{\mathbb R}$
  ($F_{\mathbb R}(\alpha b) = F_{\mathbb R}(\alpha)$), since `zOf` is invariant under $u\mapsto ub$, $b\in GL_r(\mathbb R)$;
* `volume_region_FR` (**the fibration identity**): for every measurable $B\subseteq\mathbb R^{q\times r}$ and every
  measurable $E$ in the image of the slice map,
  $$\mathrm{Leb}\{X : \det X > 0,\ \Phi(X)\in E,\ \mathrm{zOf}(\text{last } r \text{ columns of } X)\in B\}
  = \mu(F_{\mathbb R}^{-1}B)\int_E\rho,$$
  with $\rho$ the continuous Leray density (`LerayReal.rho`, $\rho(c_\varphi) = 1$).
-/
import QuadFormsKB.Literature.Hanke2005.ArchSymmetricReal
import QuadFormsKB.Tamagawa.Measure.LerayReal

open MeasureTheory Measure Matrix Set Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.ArchSOMeasure

variable {r t : ℕ}

/-! ### The form $\varphi_v$ -/

/-- $\varphi_v = \mathrm{diag}[1_q, -1_r]$, $q = r + t$, as a real quadratic form in $n = q + r$ variables
(Hanke thesis, (2.9), p. 6). -/
def phiQ (r t : ℕ) : QuadForm ℝ (r + t + r) := QuadForm.diag (signVec r t)

theorem signVec_ne_zero (i : Fin (r + t + r)) : signVec r t i ≠ 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [signVec]

theorem gramMatrixR_phiQ : gramMatrixR (phiQ r t) = phiR r t := by
  ext i j
  simp only [gramMatrixR, phiQ, QuadForm.hessian, QuadForm.diag, phiR, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, diagonal_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp; ring
  · simp [h, Ne.symm h]

theorem gramDetR_phiQ_ne_zero : gramDetR (phiQ r t) ≠ 0 := by
  have h : gramDetR (phiQ r t) = (gramMatrixR (phiQ r t)).det := by
    rw [gramDetR, gramMatrixR, det_smul, Fintype.card_fin, one_div, inv_pow, div_eq_inv_mul]
  rw [h, gramMatrixR_phiQ, phiR, det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => signVec_ne_zero i

/-! ### Slice data with lower triangular slice group -/

variable (n : ℕ) in
/-- The reversal permutation matrix $J$, $J_{ij} = [j = n - 1 - i]$. -/
def revMat : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => if j = Fin.rev i then 1 else 0

theorem revMat_apply {n : ℕ} (i j : Fin n) : revMat n i j = if j = Fin.rev i then 1 else 0 := rfl

theorem revMat_mul_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (revMat n * M) i j = M (Fin.rev i) j := by
  simp [Matrix.mul_apply, revMat_apply]

theorem mul_revMat_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (M * revMat n) i j = M i (Fin.rev j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp [revMat_apply]
  · intro k _ hk; simp only [revMat_apply]
    rw [if_neg]; · ring
    intro h; exact hk (by rw [h, Fin.rev_rev])
  · simp

theorem revMat_mul_self {n : ℕ} : revMat n * revMat n = 1 := by
  ext i j; rw [revMat_mul_apply, revMat_apply, one_apply, Fin.rev_rev]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem revMat_transpose {n : ℕ} : (revMat n)ᵀ = revMat n := by
  ext i j; simp only [transpose_apply, revMat_apply]
  by_cases h : i = Fin.rev j
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', Fin.rev_rev]))]

variable (n : ℕ) in
/-- $J$ as an element of $GL_n(\mathbb R)$ ($J^2 = 1$). -/
def revGL : GL (Fin n) ℝ := ⟨revMat n, revMat n, revMat_mul_self, revMat_mul_self⟩

/-- **Slice data with $P = J$**: ${}^tJ\varphi_vJ$ is diagonal. -/
def diagRev (r t : ℕ) : Diag (phiQ r t) where
  P := revGL (r + t + r)
  d := fun i => signVec r t (Fin.rev i)
  hd := fun i => signVec_ne_zero _
  hP := by
    ext i j
    simp only [revGL, Units.val_mk, revMat_transpose, gramMatrixR_phiQ, phiR, mul_revMat_apply,
      revMat_mul_apply, diagonal_apply, Fin.rev_inj]

theorem conj_diagRev (x : SliceB (diagRev r t).P) :
    ((((diagRev r t).P)⁻¹ * SliceB.incl _ x * (diagRev r t).P : GL (Fin (r + t + r)) ℝ) :
        Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) =
      revMat _ * SliceB.mat (diagRev r t).P x * revMat _ := by
  rw [Units.val_mul, Units.val_mul]; rfl

/-- **The slice group of `diagRev` is lower triangular**: $b_{ab} = 0$ for $a < b$. -/
theorem mat_lower (x : SliceB (diagRev r t).P) {a b : Fin (r + t + r)} (hab : a < b) :
    SliceB.mat (diagRev r t).P x a b = 0 := by
  have h := (mem_sliceGroup _ _).mp (SliceB.incl_mem _ x)
  have hUT := h.1 (Fin.rev a) (Fin.rev b) (Fin.rev_lt_rev.mpr hab)
  rw [conj_diagRev, mul_revMat_apply, revMat_mul_apply, Fin.rev_rev, Fin.rev_rev] at hUT
  exact hUT

theorem mat_diag_pos (x : SliceB (diagRev r t).P) (a : Fin (r + t + r)) :
    0 < SliceB.mat (diagRev r t).P x a a := by
  have h := (mem_sliceGroup _ _).mp (SliceB.incl_mem _ x)
  have hd := h.2 (Fin.rev a)
  rw [conj_diagRev, mul_revMat_apply, revMat_mul_apply, Fin.rev_rev] at hd
  exact hd

/-! ### $F_{\mathbb R}$ is constant along the slices -/

/-- The lower right $r\times r$ block of an $n\times n$ matrix. -/
def lowerRight (b : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  b.submatrix (Fin.natAdd (r + t)) (Fin.natAdd (r + t))

/-- For lower triangular $b$, the last $r$ columns of $\alpha b$ are (the last $r$ columns of $\alpha$)$\cdot b_{22}$. -/
theorem lastCols_mul_lower (α b : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)
    (hb : ∀ a c : Fin (r + t + r), a < c → b a c = 0) :
    lastCols (α * b) = lastCols α * lowerRight b := by
  ext i j
  simp only [lastCols, submatrix_apply, id, Matrix.mul_apply, lowerRight]
  rw [Fin.sum_univ_add]
  have : ∀ a : Fin (r + t), b (Fin.castAdd r a) (Fin.natAdd (r + t) j) = 0 := fun a =>
    hb _ _ (by simp [Fin.lt_def]; omega)
  simp [this]

theorem det_lowerRight_ne_zero (x : SliceB (diagRev r t).P) :
    (lowerRight (SliceB.mat (diagRev r t).P x)).det ≠ 0 := by
  have hlow : (lowerRight (SliceB.mat (diagRev r t).P x)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h1 : i < j := OrderDual.toDual_lt_toDual.mp hij
    exact mat_lower x (by rw [Fin.lt_def] at h1 ⊢; simp only [Fin.coe_natAdd]; omega)
  rw [det_of_isLowerTriangular _ hlow]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (mat_diag_pos x _).ne'

/-! ### Measurability of $F_{\mathbb R}$ -/

theorem measurable_matMul {α : Type*} [MeasurableSpace α] {l m p : ℕ}
    {F : α → Matrix (Fin l) (Fin m) ℝ} {G : α → Matrix (Fin m) (Fin p) ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun a => F a * G a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hF)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hG))

theorem measurable_inv_matrix {k : ℕ} : Measurable fun M : Matrix (Fin k) (Fin k) ℝ => M⁻¹ := by
  have : (fun M : Matrix (Fin k) (Fin k) ℝ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable

theorem measurable_zOf : Measurable (zOf : Matrix (Fin (r + t + r)) (Fin r) ℝ → Fin (r + t) → Fin r → ℝ) := by
  have hc : Continuous (cBlk : Matrix (Fin (r + t + r)) (Fin r) ℝ → _) := by
    unfold cBlk; fun_prop
  have hf : Continuous (fBlk : Matrix (Fin (r + t + r)) (Fin r) ℝ → _) := by
    unfold fBlk; fun_prop
  have hw : Continuous (wBlk : Matrix (Fin (r + t + r)) (Fin r) ℝ → _) := by
    unfold wBlk; fun_prop
  have hinv : Measurable fun u : Matrix (Fin (r + t + r)) (Fin r) ℝ => (wBlk u + cBlk u)⁻¹ :=
    measurable_inv_matrix.comp (hw.add hc).measurable
  have hx : Measurable fun u : Matrix (Fin (r + t + r)) (Fin r) ℝ => (wBlk u - cBlk u) * (wBlk u + cBlk u)⁻¹ :=
    measurable_matMul (hw.sub hc).measurable hinv
  have hy : Measurable fun u : Matrix (Fin (r + t + r)) (Fin r) ℝ => Real.sqrt 2 • fBlk u * (wBlk u + cBlk u)⁻¹ :=
    measurable_matMul (hf.const_smul (Real.sqrt 2)).measurable hinv
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [zOf, zMk, Fin.addCases_left]
    exact measurable_pi_iff.mpr fun j => (measurable_pi_apply j).comp ((measurable_pi_apply a).comp hx)
  · simp only [zOf, zMk, Fin.addCases_right]
    exact measurable_pi_iff.mpr fun j => (measurable_pi_apply j).comp ((measurable_pi_apply b).comp hy)

/-- $F_{\mathbb R}$ on $SO(q, r)$. -/
def FRG (g : ArchSO (phiQ r t)) : Fin (r + t) → Fin r → ℝ := FR (ArchSOInst.mat _ g)

theorem measurable_FRG : Measurable (FRG : ArchSO (phiQ r t) → _) := by
  have hl : Continuous (lastCols : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ → _) := by
    unfold lastCols; fun_prop
  exact measurable_zOf.comp (hl.comp (ArchSOInst.continuous_mat _)).measurable

/-! ### The image of the chart -/

/-- The last $r$ columns of $X$ (columns convention `X j i` = entry $(i, j)$) as an $n\times r$ matrix. -/
def lastColsX (X : Fin (r + t + r) → Fin (r + t + r) → ℝ) : Matrix (Fin (r + t + r)) (Fin r) ℝ :=
  Matrix.of fun i j => X (Fin.natAdd (r + t) j) i

theorem lastColsX_cols (M : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) : lastColsX (cols M) = lastCols M := by
  ext i j; rfl

/-- **The chart over $F_{\mathbb R}^{-1}B$**: $m(F_{\mathbb R}^{-1}B\times\beta^{-1}E) = \{X : \det X > 0,\ \Phi(X)\in E,\
\mathrm{zOf}(X_{\text{last}})\in B\}$. -/
theorem image_chart_FR {E : Set (UIdx (r + t + r) → ℝ)} (hE : E ⊆ range (beta (diagRev r t)))
    (B : Set (Fin (r + t) → Fin r → ℝ)) :
    chart (diagRev r t) '' ((FRG ⁻¹' B) ×ˢ (beta (diagRev r t) ⁻¹' E)) =
      {X | 0 < (Matrix.of X).det ∧ pullCoeff (phiQ r t) X ∈ E ∧ zOf (lastColsX X) ∈ B} := by
  have hz : ∀ p : ArchSO (phiQ r t) × SliceB (diagRev r t).P,
      zOf (lastColsX (chart (diagRev r t) p)) = FRG p.1 := by
    rintro ⟨g, x⟩
    rw [chart, lastColsX_cols, lastCols_mul_lower _ _ (fun a c h => mat_lower x h),
      zOf_mul_right _ (isUnit_iff_ne_zero.mpr (det_lowerRight_ne_zero x))]
    rfl
  ext X
  constructor
  · rintro ⟨p, ⟨hB, hE'⟩, rfl⟩
    have h1 : chart (diagRev r t) p ∈ chart (diagRev r t) '' (univ ×ˢ (beta (diagRev r t) ⁻¹' E)) :=
      ⟨p, ⟨mem_univ _, hE'⟩, rfl⟩
    rw [image_chart _ hE] at h1
    exact ⟨h1.1, h1.2, by rw [hz]; exact hB⟩
  · rintro ⟨hdet, hX, hB⟩
    have h1 : X ∈ {X : Fin (r + t + r) → Fin (r + t + r) → ℝ | 0 < (Matrix.of X).det ∧
        pullCoeff (phiQ r t) X ∈ E} := ⟨hdet, hX⟩
    rw [← image_chart _ hE] at h1
    obtain ⟨p, ⟨-, hp⟩, rfl⟩ := h1
    exact ⟨p, ⟨by rw [mem_preimage, ← hz]; exact hB, hp⟩, rfl⟩

/-- **The fibration identity over $F_{\mathbb R}^{-1}B$**: for measurable $B$ and measurable $E$ inside the image of the
slice map, the region $\{\det X > 0,\ \Phi(X)\in E,\ \mathrm{zOf}(X_{\text{last}})\in B\}$ has Lebesgue measure
$\mu(F_{\mathbb R}^{-1}B)\int_E\rho$, $\mu$ = `lerayMeasure (phiQ r t)`. -/
theorem volume_region_FR {E : Set (UIdx (r + t + r) → ℝ)} (hEm : MeasurableSet E)
    (hE : E ⊆ range (beta (diagRev r t))) {B : Set (Fin (r + t) → Fin r → ℝ)} (hB : MeasurableSet B) :
    volume {X : Fin (r + t + r) → Fin (r + t + r) → ℝ |
        0 < (Matrix.of X).det ∧ pullCoeff (phiQ r t) X ∈ E ∧ zOf (lastColsX X) ∈ B} =
      lerayMeasure (phiQ r t) gramDetR_phiQ_ne_zero (FRG ⁻¹' B) *
        ∫⁻ c in E, ENNReal.ofReal (rho (diagRev r t) c) := by
  have hm : MeasurableSet ((FRG ⁻¹' B) ×ˢ (beta (diagRev r t) ⁻¹' E)) :=
    (measurable_FRG hB).prod ((continuous_beta _).measurable hEm)
  rw [← image_chart_FR hE B, ← tauM_apply _ hm, tauM, lerayFibration, Measure.prod_prod,
    kappa0_preimage _ hEm, inter_eq_left.mpr hE, lerayMeasure, lerayD_eq]

end QuadFormsKB.Hanke2005.ArchReal
