/-
# Hua's integral, algebraic part: the Schur complement of $B + iI$ in the first row

**Layer:** local, one real place; linear algebra of real symmetric matrices (no global input).
`hH b` $= \mathrm{symU}(b) + iI$; `det_hH_asm` is the Schur complement in the first row and `exists_im_quad` the
normalization of the imaginary part of $u^{\mathsf T}(B' + iI)^{-1}u$, both used by `ArchHua.lean`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.ArchDetBound

open MeasureTheory Matrix Complex
open scoped Real ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open WeilRep.Genus QuadFormsKB.Tamagawa.ArchVol

/-- The complex matrix $\mathrm{symU}(b) + iI$. -/
abbrev hH {r : ℕ} (b : UIdx r → ℝ) : Matrix (Fin r) (Fin r) ℂ := cR (symU b) + I • (1 : Matrix (Fin r) (Fin r) ℂ)

/-- A real vector as a complex vector. -/
abbrev cV {r : ℕ} (u : Fin r → ℝ) : Fin r → ℂ := fun j => (u j : ℂ)

lemma one_le_norm_det_hH {r : ℕ} (b : UIdx r → ℝ) : 1 ≤ ‖(hH b).det‖ := by
  have h := norm_det_sq_ge (symU_transpose b)
  have h0 : 0 ≤ ∑ i, ∑ j, symU b i j ^ 2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : 1 ≤ ‖(hH b).det‖ ^ 2 := by simp only [hH]; linarith
  nlinarith [norm_nonneg (hH b).det]

lemma det_hH_ne_zero {r : ℕ} (b : UIdx r → ℝ) : (hH b).det ≠ 0 := by
  intro h; have := one_le_norm_det_hH b; rw [h, norm_zero] at this; linarith

lemma continuous_det_hH {r : ℕ} : Continuous fun b : UIdx r → ℝ => (hH b).det := by
  have := continuous_det_add_symU (r := r) (I • (1 : Matrix (Fin r) (Fin r) ℂ))
  simpa [hH, add_comm] using this

/-! ### The Schur complement in the first row -/

/-- **Schur complement:** $\det(B + iI) = \det(B' + iI)(a + i - u^{\mathsf T}(B' + iI)^{-1}u)$ for
$B = \begin{pmatrix}a & u^{\mathsf T}\\ u & B'\end{pmatrix}$ (`asm a u v`, $B' = \mathrm{symU}(v)$). -/
theorem det_hH_asm {r : ℕ} (a : ℝ) (u : Fin r → ℝ) (v : UIdx r → ℝ) :
    (hH (asm a u v)).det = (hH v).det * ((a : ℂ) + I - cV u ⬝ᵥ ((hH v)⁻¹ *ᵥ cV u)) := by
  classical
  let e : Fin (r + 1) ≃ Fin r ⊕ Unit := (finSuccEquiv r).trans (Equiv.optionEquivSumPUnit (Fin r))
  have he0 : e.symm (Sum.inr ()) = 0 := rfl
  have hej : ∀ j, e.symm (Sum.inl j) = j.succ := fun j => rfl
  have hM : reindex e e (hH (asm a u v)) =
      fromBlocks (hH v) (Matrix.of fun i (_ : Unit) => (u i : ℂ)) (Matrix.of fun (_ : Unit) j => (u j : ℂ))
        (Matrix.of fun (_ : Unit) (_ : Unit) => (a : ℂ) + I) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hH, cR, Matrix.one_apply, he0, hej, symU_zero_zero, symU_zero_succ, symU_succ_zero,
        symU_succ_succ, Fin.succ_inj, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  have : Invertible (hH v) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.2 (det_hH_ne_zero v))
  have hu : ∀ M : Matrix Unit Unit ℂ, M.det = M () () := fun M => by simp [Matrix.det_unique]
  rw [← Matrix.det_reindex_self e, hM, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hu]
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_mul, cV]
  refine Finset.sum_congr rfl fun j _ => by ring

/-! ### The imaginary part of the quadratic form $u^{\mathsf T}(B' + iI)^{-1}u$ -/

/-- There is a real $A$ with $|\det A| = |\det(B' + iI)|$ and
$\operatorname{Im}((Aw)^{\mathsf T}(B' + iI)^{-1}(Aw)) = -w^{\mathsf T}w$. -/
theorem exists_im_quad {r : ℕ} (v : UIdx r → ℝ) :
    ∃ A : Matrix (Fin r) (Fin r) ℝ, |A.det| = ‖(hH v).det‖ ∧
      ∀ w : Fin r → ℝ, (cV (A *ᵥ w) ⬝ᵥ ((hH v)⁻¹ *ᵥ cV (A *ᵥ w))).im = -(w ⬝ᵥ w) := by
  classical
  have hSym : (symU v).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact symU_transpose v
  obtain ⟨U, hUU, hUU', hCeq⟩ := exists_orth_diag hSym
  set μ := hSym.eigenvalues
  have hne : ∀ j, (μ j : ℂ) + I ≠ 0 := fun j h => by
    have := congrArg Complex.im h; simp at this
  have hdiag : hH v = cR U * diagonal (fun j => (μ j : ℂ) + I) * cR Uᵀ := by
    have h1 : diagonal (fun j => (μ j : ℂ) + I) = cR (diagonal μ) + I • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    have h2 : cR U * cR Uᵀ = 1 := by rw [← cR_mul, hUU']; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h2,
      ← cR_mul, ← cR_mul, ← hCeq]
  have h2 : cR U * cR Uᵀ = 1 := by rw [← cR_mul, hUU']; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have h3 : cR Uᵀ * cR U = 1 := by rw [← cR_mul, hUU]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hL : ∀ X : Matrix (Fin r) (Fin r) ℂ, cR Uᵀ * (cR U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  have hR : ∀ X : Matrix (Fin r) (Fin r) ℂ, X * cR U * cR Uᵀ = X := fun X => by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have hinv : (hH v)⁻¹ = cR U * diagonal (fun j => ((μ j : ℂ) + I)⁻¹) * cR Uᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hdiag]
    have hD : diagonal (fun j => (μ j : ℂ) + I) * diagonal (fun j => ((μ j : ℂ) + I)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal]; ext i j
      by_cases h : i = j
      · subst h; simp [hne i]
      · simp [h]
    calc cR U * diagonal (fun j => (μ j : ℂ) + I) * cR Uᵀ * (cR U * diagonal (fun j => ((μ j : ℂ) + I)⁻¹) * cR Uᵀ)
        = cR U * (diagonal (fun j => (μ j : ℂ) + I) * (cR Uᵀ * (cR U * (diagonal (fun j => ((μ j : ℂ) + I)⁻¹) * cR Uᵀ)))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hL, ← Matrix.mul_assoc (diagonal _), hD, Matrix.one_mul, h2]
  set s : Fin r → ℝ := fun j => Real.sqrt (1 + μ j ^ 2) with hs
  have hspos : ∀ j, 0 < s j := fun j => Real.sqrt_pos.2 (by positivity)
  have hss : ∀ j, s j ^ 2 = 1 + μ j ^ 2 := fun j => Real.sq_sqrt (by positivity)
  have hdetU : |U.det| = 1 := by
    have : U.det * U.det = 1 := by
      have := congrArg Matrix.det hUU
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    have h' : |U.det| * |U.det| = 1 := by rw [← abs_mul, this, abs_one]
    nlinarith [abs_nonneg U.det]
  refine ⟨U * diagonal s, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, abs_mul, hdetU, one_mul, abs_of_nonneg
      (Finset.prod_nonneg fun j _ => (hspos j).le), hdiag, Matrix.mul_assoc, Matrix.det_mul_comm,
      Matrix.mul_assoc, h3, Matrix.mul_one, det_diagonal, norm_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hs]; simp only
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im]
    congr 1; ring
  · intro w
    have hx : cV ((U * diagonal s) *ᵥ w) = (cR U * diagonal (fun j => (s j : ℂ))) *ᵥ cV w := by
      ext i
      simp [cV, Matrix.mulVec, dotProduct, Matrix.mul_apply, diagonal_apply, cR]
    have hK : (cR U * diagonal (fun j => (s j : ℂ)))ᵀ * (hH v)⁻¹ * (cR U * diagonal (fun j => (s j : ℂ))) =
        diagonal (fun j => (μ j : ℂ) - I) := by
      rw [Matrix.transpose_mul, diagonal_transpose, hinv]
      have hTr : (cR U)ᵀ = cR Uᵀ := Matrix.transpose_map.symm
      rw [hTr]
      simp only [Matrix.mul_assoc]
      rw [hL, hL, diagonal_mul_diagonal, diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        have hsq : ((s i : ℂ)) ^ 2 = 1 + (μ i : ℂ) ^ 2 := by exact_mod_cast hss i
        have := hne i
        simp only [diagonal_apply_eq]
        field_simp
        linear_combination hsq + Complex.I_sq
      · simp [h]
    have key : cV ((U * diagonal s) *ᵥ w) ⬝ᵥ ((hH v)⁻¹ *ᵥ cV ((U * diagonal s) *ᵥ w)) =
        ∑ j, (w j : ℂ) ^ 2 * ((μ j : ℂ) - I) := by
      set P := cR U * diagonal (fun j => (s j : ℂ))
      have e1 : cV ((U * diagonal s) *ᵥ w) = cV w ᵥ* Pᵀ := by rw [hx, Matrix.vecMul_transpose]
      rw [hx, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← hx, e1, Matrix.vecMul_vecMul,
        ← Matrix.mul_assoc, hK]
      simp [dotProduct, sq, Matrix.vecMul_diagonal, cV]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [key]
    simp [Complex.im_sum, dotProduct, sq]

end QuadFormsKB.SiegelWeil.Forms.ArchR
