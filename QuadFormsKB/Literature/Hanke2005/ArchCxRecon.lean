/-
# Hanke 2005, §4.3: reconstructing the coordinates $(u, Y, \sigma)$ near $SO_n(\mathbb C)$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Proves**
* `gram_psiM`: ${}^t\Psi\Psi = (1 - i\sigma)\,T\,(1 - i\sigma)$ for $\Psi = (1 - iu)Y(1 - i\sigma)$, $u$ skew, $\sigma$ symmetric,
  $T = {}^tY(1 - {}^tuu)Y$; hence `phi_psiM`: $\Phi(\Psi) = h(c(T, \sigma))$ (`cOf`);
* `recon` (**reconstruction**): if $\Phi(X) = h(c)$ with $T = $ `cT c` positive definite and $1 - i\sigma$ invertible
  ($\sigma = $ `cS c`), then with $A = X(1 - i\sigma)^{-1}$, $Y = \operatorname{Re}A$ and $u = -\operatorname{Im}A\,Y^{-1}$:
  $Y$ is invertible, $u$ is skew with $1 - {}^tuu$ positive definite ($u\in Z_{\mathbb C}$), $X = \Psi(u, Y, \sigma)$ and
  ${}^tY(1 - {}^tuu)Y = T$.
-/
import QuadFormsKB.Literature.Hanke2005.ArchCxLocal

open Matrix Complex

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

/-! ### Real and imaginary parts -/

theorem reM_cplx (A : Matrix (Fin n) (Fin n) ℝ) : reM (cplx A) = A := by ext i j; simp [reM, cplx]

theorem imM_cplx (A : Matrix (Fin n) (Fin n) ℝ) : imM (cplx A) = 0 := by ext i j; simp [imM, cplx]

theorem reM_transpose (A : Matrix (Fin n) (Fin n) ℂ) : reM Aᵀ = (reM A)ᵀ := by ext i j; simp [reM]

theorem imM_transpose (A : Matrix (Fin n) (Fin n) ℂ) : imM Aᵀ = (imM A)ᵀ := by ext i j; simp [imM]

theorem cplx_re_add_im (A : Matrix (Fin n) (Fin n) ℂ) : cplx (reM A) + I • cplx (imM A) = A := by
  ext i j; simp [reM, imM, cplx]; rw [mul_comm]; exact Complex.re_add_im (A i j)

/-! ### The Gram matrix of $\Psi$ -/

theorem transpose_one_sub_I_sym {σ : Matrix (Fin n) (Fin n) ℝ} (hσ : σᵀ = σ) :
    (1 - I • cplx σ)ᵀ = 1 - I • cplx σ := by
  rw [transpose_sub, transpose_one, transpose_smul, ← cplx_transpose, hσ]

theorem transpose_one_sub_I_skew {u : Matrix (Fin n) (Fin n) ℝ} (hu : uᵀ = -u) :
    (1 - I • cplx u)ᵀ = 1 + I • cplx u := by
  rw [transpose_sub, transpose_one, transpose_smul, ← cplx_transpose, hu, cplx_neg, smul_neg, sub_neg_eq_add]

theorem one_add_mul_one_sub {u : Matrix (Fin n) (Fin n) ℝ} (hu : uᵀ = -u) :
    (1 + I • cplx u) * (1 - I • cplx u) = cplx (mZ u) := by
  rw [mZ, cplx_sub, cplx_one, cplx_mul, hu, cplx_neg, Matrix.neg_mul, sub_neg_eq_add]
  set a := cplx u
  have e : (1 + I • a) * (1 - I • a) = 1 - (I • a) * (I • a) := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]; abel
  rw [e, smul_mul_smul_comm, I_mul_I, neg_one_smul, sub_neg_eq_add]

/-- ${}^t\Psi\Psi = (1 - i\sigma)\,T\,(1 - i\sigma)$, $T = {}^tY(1 - {}^tuu)Y$. -/
theorem gram_psiM {u Y σ : Matrix (Fin n) (Fin n) ℝ} (hu : uᵀ = -u) (hσ : σᵀ = σ) :
    (psiM u Y σ)ᵀ * psiM u Y σ = (1 - I • cplx σ) * cplx (tT u Y) * (1 - I • cplx σ) := by
  rw [psiM, transpose_mul, transpose_mul, transpose_one_sub_I_sym hσ, transpose_one_sub_I_skew hu, tT,
    cplx_mul, cplx_mul, cplx_transpose, ← one_add_mul_one_sub hu]
  simp only [Matrix.mul_assoc]

theorem mZ_transpose (u : Matrix (Fin n) (Fin n) ℝ) : (mZ u)ᵀ = mZ u := by
  rw [mZ, transpose_sub, transpose_one, transpose_mul, transpose_transpose]

theorem tT_transpose (u Y : Matrix (Fin n) (Fin n) ℝ) : (tT u Y)ᵀ = tT u Y := by
  rw [tT, transpose_mul, transpose_mul, transpose_transpose, mZ_transpose, Matrix.mul_assoc]

/-! ### Packing $(T, \sigma)$ into a coefficient vector -/

/-- The complex coefficient vector with $\operatorname{Re} = $ the upper coordinates of $T$ and $\operatorname{Im} = $ those
of $\sigma$. -/
def cOf (T σ : Matrix (Fin n) (Fin n) ℝ) : UIdx n → ℂ := fun q => ⟨T q.1.1 q.1.2, σ q.1.1 q.1.2⟩

theorem symU_upperOf {T : Matrix (Fin n) (Fin n) ℝ} (hT : Tᵀ = T) : symU (upperOf T) = T := by
  ext i j
  simp only [symU, upperOf, of_apply]
  split_ifs
  · rfl
  · rw [← transpose_apply T i j, hT]

theorem cT_cOf {T : Matrix (Fin n) (Fin n) ℝ} (σ : Matrix (Fin n) (Fin n) ℝ) (hT : Tᵀ = T) : cT (cOf T σ) = T :=
  symU_upperOf hT

theorem cS_cOf (T : Matrix (Fin n) (Fin n) ℝ) {σ : Matrix (Fin n) (Fin n) ℝ} (hσ : σᵀ = σ) : cS (cOf T σ) = σ :=
  symU_upperOf hσ

theorem cOf_cT_cS (c : UIdx n → ℂ) : cOf (cT c) (cS c) = c := by
  funext q
  apply Complex.ext
  · simp [cOf, cT, symU_apply_le _ q.2]
  · simp [cOf, cS, symU_apply_le _ q.2]

theorem phi_sumSqC (X : Matrix (Fin n) (Fin n) ℂ) : phi (sumSqC n) X = wtU (Xᵀ * X) := by
  rw [phi, gramC_sumSqC, Matrix.mul_one]

/-- $\Phi(\Psi(u, Y, \sigma)) = h(c(T, \sigma))$. -/
theorem phi_psiM {u Y σ : Matrix (Fin n) (Fin n) ℝ} (hu : uᵀ = -u) (hσ : σᵀ = σ) :
    phi (sumSqC n) (psiM u Y σ) = hmap (cOf (tT u Y) σ) := by
  rw [phi_sumSqC, gram_psiM hu hσ, hmap, cT_cOf σ (tT_transpose u Y), cS_cOf _ hσ]

/-! ### Reconstruction -/

theorem symm_hmap_arg (c : UIdx n → ℂ) :
    ((1 - I • cplx (cS c)) * cplx (cT c) * (1 - I • cplx (cS c)))ᵀ =
      (1 - I • cplx (cS c)) * cplx (cT c) * (1 - I • cplx (cS c)) := by
  rw [transpose_mul, transpose_mul, transpose_one_sub_I_sym (cS_transpose c), ← cplx_transpose, cT_transpose,
    Matrix.mul_assoc]

/-- If $\Phi(X) = h(c)$ then ${}^tXX = (1 - i\sigma)T(1 - i\sigma)$. -/
theorem gram_of_hmap {X : Matrix (Fin n) (Fin n) ℂ} {c : UIdx n → ℂ} (hc : hmap c = phi (sumSqC n) X) :
    Xᵀ * X = (1 - I • cplx (cS c)) * cplx (cT c) * (1 - I • cplx (cS c)) := by
  rw [phi_sumSqC, hmap] at hc
  refine wtU_inj ?_ (symm_hmap_arg c) hc.symm
  rw [transpose_mul, transpose_transpose]

/-- $A = X(1 - i\sigma)^{-1}$. -/
def aOf (X : Matrix (Fin n) (Fin n) ℂ) (c : UIdx n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  X * (1 - I • cplx (cS c))⁻¹

/-- $u = -\operatorname{Im}A\,(\operatorname{Re}A)^{-1}$. -/
def uOfc (X : Matrix (Fin n) (Fin n) ℂ) (c : UIdx n → ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  -imM (aOf X c) * (reM (aOf X c))⁻¹

section recon

variable {X : Matrix (Fin n) (Fin n) ℂ} {c : UIdx n → ℂ} (hc : hmap c = phi (sumSqC n) X)
  (hT : PDU (fun q => (c q).re)) (hd : (1 - I • cplx (cS c)).det ≠ 0)

include hc hd in
theorem gram_aOf : (aOf X c)ᵀ * aOf X c = cplx (cT c) := by
  have hu : IsUnit (1 - I • cplx (cS c)).det := isUnit_iff_ne_zero.mpr hd
  rw [aOf, transpose_mul, transpose_nonsing_inv, transpose_one_sub_I_sym (cS_transpose c)]
  calc (1 - I • cplx (cS c))⁻¹ * Xᵀ * (X * (1 - I • cplx (cS c))⁻¹)
      = (1 - I • cplx (cS c))⁻¹ * (Xᵀ * X) * (1 - I • cplx (cS c))⁻¹ := by simp only [Matrix.mul_assoc]
    _ = cplx (cT c) := by
      rw [gram_of_hmap hc]
      simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
      rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]

include hc hd in
theorem re_im_aOf : (reM (aOf X c))ᵀ * reM (aOf X c) - (imM (aOf X c))ᵀ * imM (aOf X c) = cT c ∧
    (reM (aOf X c))ᵀ * imM (aOf X c) + (imM (aOf X c))ᵀ * reM (aOf X c) = 0 := by
  have h := gram_aOf hc hd
  have h1 := congrArg reM h
  have h2 := congrArg imM h
  rw [reM_mul, reM_transpose, imM_transpose, reM_cplx] at h1
  rw [imM_mul, reM_transpose, imM_transpose, imM_cplx] at h2
  exact ⟨h1, h2⟩

theorem symU_re_eq_cT : symU (fun q => (c q).re) = cT c := rfl

include hc hT hd in
/-- $Y = \operatorname{Re}A$ is injective, i.e. invertible. -/
theorem det_reM_aOf_ne_zero : (reM (aOf X c)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hYv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := (re_im_aOf hc hd).1
  have hq : v ⬝ᵥ (cT c *ᵥ v) = -((imM (aOf X c) *ᵥ v) ⬝ᵥ (imM (aOf X c) *ᵥ v)) := by
    rw [← h1, sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hYv, mulVec_zero, dotProduct_zero,
      zero_sub, dotProduct_mulVec, vecMul_transpose]
  have hpos : 0 < v ⬝ᵥ (cT c *ᵥ v) := hT v hv
  have hnn : 0 ≤ (imM (aOf X c) *ᵥ v) ⬝ᵥ (imM (aOf X c) *ᵥ v) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  linarith

include hc hT hd in
theorem uOfc_mul_reM : uOfc X c * reM (aOf X c) = -imM (aOf X c) := by
  have hu : IsUnit (reM (aOf X c)).det := isUnit_iff_ne_zero.mpr (det_reM_aOf_ne_zero hc hT hd)
  rw [uOfc, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

include hc hT hd in
/-- $u$ is skew-symmetric. -/
theorem uOfc_skew : (uOfc X c)ᵀ = -uOfc X c := by
  set Y := reM (aOf X c)
  set W := imM (aOf X c)
  set u := uOfc X c
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.mpr (det_reM_aOf_ne_zero hc hT hd)
  have huT : IsUnit Yᵀ.det := by rw [det_transpose]; exact hu
  have huY : u * Y = -W := uOfc_mul_reM hc hT hd
  have h2 := (re_im_aOf hc hd).2
  have key : Yᵀ * (uᵀ + u) * Y = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc Yᵀ u Y, huY, ← transpose_mul, huY,
      transpose_neg, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, add_comm, h2, neg_zero]
  have : uᵀ + u = 0 := by
    have e : (Yᵀ)⁻¹ * (Yᵀ * (uᵀ + u) * Y) * Y⁻¹ = uᵀ + u := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [← e, key, Matrix.mul_zero, Matrix.zero_mul]
  exact eq_neg_of_add_eq_zero_left this

include hc hT hd in
theorem aOf_eq : aOf X c = (1 - I • cplx (uOfc X c)) * cplx (reM (aOf X c)) := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, ← cplx_mul, uOfc_mul_reM hc hT hd, cplx_neg, smul_neg,
    sub_neg_eq_add, cplx_re_add_im]

include hc hT hd in
/-- **Reconstruction**: $X = \Psi(u, Y, \sigma)$. -/
theorem X_eq_psiM : X = psiM (uOfc X c) (reM (aOf X c)) (cS c) := by
  have hu : IsUnit (1 - I • cplx (cS c)).det := isUnit_iff_ne_zero.mpr hd
  rw [psiM, ← aOf_eq hc hT hd, aOf, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

include hc hT hd in
theorem tT_uOfc : tT (uOfc X c) (reM (aOf X c)) = cT c := by
  have huY := uOfc_mul_reM hc hT hd
  rw [tT, mZ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (reM _),
    ← transpose_mul, huY, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← (re_im_aOf hc hd).1]

include hc hT hd in
/-- $1 - {}^tuu$ is positive definite. -/
theorem dot_mZ_pos {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ (mZ (uOfc X c) *ᵥ x) := by
  set Y := reM (aOf X c)
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.mpr (det_reM_aOf_ne_zero hc hT hd)
  set y := Y⁻¹ *ᵥ x
  have hxy : x = Y *ᵥ y := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hy : y ≠ 0 := by
    intro h; rw [h, mulVec_zero] at hxy; exact hx hxy
  have := hT y hy
  rw [symU_re_eq_cT, ← tT_uOfc hc hT hd, tT, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose, ← hxy] at this
  exact this

include hc hT hd in
/-- $u\in Z_{\mathbb C}$. -/
theorem uOfc_mem_ZC : uOfc X c ∈ ZC n := by
  refine ⟨uOfc_skew hc hT hd, ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact mZ_transpose _
  · rw [star_trivial]; exact dot_mZ_pos hc hT hd hx

end recon

end QuadFormsKB.Hanke2005.ArchCx
