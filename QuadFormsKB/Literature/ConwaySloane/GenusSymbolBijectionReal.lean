/-
# Conway–Sloane, Ch. 15, §7.1.r1: the $(-1)$-adic symbol of a real form

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.1–7.2, p. 379
(`conwaysloane1999`): over $\mathbb R$ a nondegenerate form is equivalent to $\langle 1^r, (-1)^s\rangle$ for exactly one
$r$ (Sylvester's law of inertia), and $+^r-^s$ is its $(-1)$-adic symbol.

**Proves**, for the model `realVec n r` $= \langle 1^r, (-1)^{n-r}\rangle$ of `Theorem11.lean`:
* `exists_congrIn_realVec`: every nondegenerate symmetric real matrix is congruent to the model for some $r \le n$;
* `eq_of_congrIn_realVec`: the models for $r, r' \le n$ are congruent only if $r = r'$ (Sylvester's law of inertia,
  through Mathlib's `QuadraticForm.sigPos_of_equiv_weightedSumSquares`).
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem11
import QuadFormsKB.Literature.Hanke2005.ArchNormalForm

namespace QuadFormsKB.ConwaySloane

open Matrix

/-- Helper: spectral diagonalization of a nondegenerate symmetric real matrix, $P^{\mathsf T}MP = \mathrm{diag}(d)$
with $P$ invertible and all $d_i \ne 0$. -/
theorem exists_diag_of_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (hdet : M.det ≠ 0) :
    ∃ (P : GL (Fin n) ℝ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) ∧
      (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * M * P = diagonal d := by
  have hA : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hM
  set U := hA.eigenvectorUnitary
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set Um : Matrix (Fin n) (Fin n) ℝ := (U : Matrix (Fin n) (Fin n) ℝ) with hUm
  have hstar : star (U : Matrix (Fin n) (Fin n) ℝ) = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have h1 : star (U : Matrix (Fin n) (Fin n) ℝ) * U = 1 := Unitary.coe_star_mul_self U
  have h2 : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  refine ⟨⟨U, star (U : Matrix (Fin n) (Fin n) ℝ), h2, h1⟩, hA.eigenvalues, fun i => ?_, ?_⟩
  · have hd := hA.det_eq_prod_eigenvalues
    rw [hd] at hdet
    simpa using (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  · change (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * M * U = _
    rw [← hstar]
    conv_lhs => rw [hspec]
    rw [show star Um * (Um * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star Um) * Um
        = (star Um * Um) * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (star Um * Um) by
          simp only [Matrix.mul_assoc], h1, Matrix.one_mul, Matrix.mul_one]
    rfl

/-- Helper: the quadratic value of $g^{\mathsf T}\operatorname{diag}(\varepsilon)g$ at $y$ is
$\sum_i \varepsilon_i (gy)_i^2$. -/
theorem dot_conj_diag {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (ε y : Fin n → ℝ) :
    y ⬝ᵥ ((gᵀ * diagonal ε * g) *ᵥ y) = ∑ i, ε i * (g *ᵥ y) i ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

/-- Helper: the number of $i : \mathrm{Fin}\ n$ with $0 < \mathrm{realVec}\ n\ r\ i$ is $r$ when $r \le n$. -/
theorem ncard_pos_realVec {n r : ℕ} (hr : r ≤ n) :
    {i : Fin n | 0 < (((realVec n r i : ℤ)) : ℝ)}.ncard = r := by
  have : {i : Fin n | 0 < (((realVec n r i : ℤ)) : ℝ)} =
      ↑(Finset.univ.filter fun i : Fin n => (i : ℕ) < r) := by
    ext i
    simp only [realVec, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    split_ifs with h <;> simp [h]
  rw [this, Set.ncard_coe_finset, Fin.card_filter_val_lt]
  omega

/-- **Existence of the $(-1)$-adic symbol** (Conway–Sloane, §7.1–7.2, p. 379; Sylvester's normal form): a nondegenerate
symmetric real matrix $M$ is congruent over $\mathbb R$ to $\langle 1^r, (-1)^{n-r}\rangle$ for some $r \le n$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, p. 379"]
theorem exists_congrIn_realVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (hdet : M.det ≠ 0) :
    ∃ r ≤ n, CongrIn ℝ M (Matrix.diagonal fun i => ((realVec n r i : ℤ) : ℝ)) := by
  classical
  obtain ⟨P, d, hd, hP⟩ := exists_diag_of_symm M hM hdet
  set S : Fin n → ℝ := fun k => if 0 < d k then (1 : ℝ) else -1 with hS
  have hSpm : ∀ k, S k = 1 ∨ S k = -1 := fun k => by
    by_cases h : 0 < d k <;> simp [hS, h]
  set r' := (Finset.univ.filter fun k => S k = -1).card with hr'
  have hr'n : r' ≤ n := by
    simpa using Finset.card_le_univ (Finset.univ.filter fun k => S k = -1)
  obtain ⟨σ, hσ⟩ := QuadFormsKB.Hanke2005.exists_perm_signs hr'n S hSpm rfl
  set a : Fin n → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with ha
  have hapos : ∀ i, a i ≠ 0 := fun i => by
    have : 0 < |d i| := abs_pos.mpr (hd i)
    simp only [ha]; positivity
  have haS : ∀ i, a i * d i * a i = S i := fun i => by
    have h0 : 0 < |d i| := abs_pos.mpr (hd i)
    have h1 : Real.sqrt |d i| * Real.sqrt |d i| = |d i| := Real.mul_self_sqrt h0.le
    have h2 : Real.sqrt |d i| ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
    have e : (Real.sqrt |d i|)⁻¹ * d i * (Real.sqrt |d i|)⁻¹ =
        d i / (Real.sqrt |d i| * Real.sqrt |d i|) := by
      field_simp
    simp only [ha, hS]
    rw [e, h1]
    by_cases h : 0 < d i
    · simp only [h, ↓reduceIte, abs_of_pos h, div_self h.ne']
    · simp only [h, ↓reduceIte, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) (hd i)), div_neg, div_self (hd i)]
  set G1 : Matrix (Fin n) (Fin n) ℝ := (P : Matrix (Fin n) (Fin n) ℝ) * diagonal a with hG1
  have hG1S : G1ᵀ * M * G1 = diagonal S := by
    rw [hG1, transpose_mul, diagonal_transpose]
    calc diagonal a * (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * M * ((P : Matrix (Fin n) (Fin n) ℝ) * diagonal a)
        = diagonal a * ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ * M * (P : Matrix (Fin n) (Fin n) ℝ)) *
            diagonal a := by simp only [Matrix.mul_assoc]
      _ = diagonal S := by
        rw [hP, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1; funext i; exact haS i
  have hdetG1 : G1.det ≠ 0 := by
    rw [hG1, det_mul, det_diagonal]
    exact mul_ne_zero (P.isUnit.map Matrix.detMonoidHom |>.ne_zero)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hapos i)
  have hdetG : (G1.submatrix id σ).det ≠ 0 := by
    rw [Matrix.det_permute']
    exact mul_ne_zero (by simp) hdetG1
  refine ⟨n - r', by omega, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetG, ?_⟩
  show (G1.submatrix id σ)ᵀ * M * (G1.submatrix id σ) = _
  rw [QuadFormsKB.Hanke2005.congr_submatrix_perm, hG1S, QuadFormsKB.Hanke2005.diagonal_submatrix_perm]
  congr 1
  funext i
  rw [hσ i]
  unfold realVec
  split_ifs <;> simp

/-- **Sylvester's law of inertia for the models** (Conway–Sloane, §7.1–7.2, p. 379): for $r, r' \le n$, the models
$\langle 1^r, (-1)^{n-r}\rangle$ and $\langle 1^{r'}, (-1)^{n-r'}\rangle$ are congruent over $\mathbb R$ only if $r = r'$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, p. 379"]
theorem eq_of_congrIn_realVec {n r r' : ℕ} (hr : r ≤ n) (hr' : r' ≤ n)
    (h : CongrIn ℝ (Matrix.diagonal fun i => ((realVec n r i : ℤ) : ℝ))
      (Matrix.diagonal fun i => ((realVec n r' i : ℤ) : ℝ))) : r = r' := by
  obtain ⟨g, hg⟩ := h
  set C : Matrix (Fin n) (Fin n) ℝ := g.val
  have hCinv : Invertible C := Matrix.invertibleOfIsUnitDet C (by
    have := g.isUnit.map Matrix.detMonoidHom
    simpa using this)
  have e : QuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares ℝ fun i => ((realVec n r' i : ℤ) : ℝ))
      (QuadraticMap.weightedSumSquares ℝ fun i => ((realVec n r i : ℤ) : ℝ)) := by
    refine ⟨⟨Matrix.toLinearEquiv' C hCinv, fun y => ?_⟩⟩
    have h1 := dot_conj_diag C (fun i => ((realVec n r i : ℤ) : ℝ)) y
    rw [show Cᵀ * diagonal (fun i => ((realVec n r i : ℤ) : ℝ)) * C = _ from hg] at h1
    have h2 := dot_conj_diag 1 (fun i => ((realVec n r' i : ℤ) : ℝ)) y
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mulVec] at h2
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    change ∑ x, ((realVec n r x : ℤ) : ℝ) * ((C *ᵥ y) x * (C *ᵥ y) x) =
      ∑ x, ((realVec n r' x : ℤ) : ℝ) * (y x * y x)
    simp only [← pow_two]
    rw [← h1, h2]
  have h1 := QuadraticForm.sigPos_of_equiv_weightedSumSquares e
  have h2 := QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (Q := QuadraticMap.weightedSumSquares ℝ fun i => ((realVec n r' i : ℤ) : ℝ))
    (w := fun i => ((realVec n r' i : ℤ) : ℝ)) ⟨QuadraticMap.IsometryEquiv.refl _⟩
  rw [ncard_pos_realVec hr] at h1
  rw [ncard_pos_realVec hr'] at h2
  omega

end QuadFormsKB.ConwaySloane
