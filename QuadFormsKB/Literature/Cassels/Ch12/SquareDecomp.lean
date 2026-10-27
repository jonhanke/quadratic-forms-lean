/-
# Cassels, Chapter 12: completing the square (the decomposition $f = \sum_j h_j(x_j + c_{j,j+1}x_{j+1} + \cdots)^2$)

A strictly positive definite real form can be written uniquely as
$$f(\vec{x}) = \sum_{j=0}^{n-1} h_j\,\bigl(x_j + c_{j,j+1}x_{j+1} + \cdots + c_{j,n-1}x_{n-1}\bigr)^2, \qquad h_j > 0$$
(Cassels, Ch. 12, (1.8) and the definition of Siegel domains, p. 259; (3.1), p. 263; (4.1), p. 266). In matrix terms
$F = C^{\mathsf T}\,\mathrm{diag}(h)\,C$ with $C = (c_{ij})$ upper unitriangular (`IsSqDecomp`). It is Mathlib's $LDL^{\mathsf T}$
decomposition (`LDL.lower_conj_diag`) with $C = L^{\mathsf T}$. Consequences used in the chapter: $d(f) = \prod_j h_j$
((3.1)–(3.4), p. 265), $f_{jj} = \sum_{i \le j} h_i c_{ij}^2$ ((3.2), p. 264), and $f(\vec{a}) \ge h_k$ for an integral
$\vec{a}$ whose last nonzero coordinate is $a_k$ (proof of Lemma 4.1, p. 267).
-/
import QuadFormsKB.Literature.Cassels.Ch12.Basic

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **$F = C^{\mathsf T}\mathrm{diag}(h)C$ with $C$ upper unitriangular:** the real form with matrix $F$ is
$$f(\vec{x}) = \sum_{i} h_i\,\Bigl(x_i + \sum_{j > i} c_{ij}x_j\Bigr)^2$$
(`val_eq_of_isSqDecomp`). Cassels, Ch. 12, p. 259 and (3.1), p. 263 (his $h_j$ and $c_{ij}$, 0-based here). No sign
condition on $h$ is imposed; for strictly positive definite $F$ the $h_i$ are positive (`IsSqDecomp.pos`). -/
@[kb "cassels1978" "Ch. 12, §1, p. 259 (f = Σ h_j(x_j + c_{j,j+1}x_{j+1} + ⋯)²); §3, (3.1), p. 263"]
def IsSqDecomp (F : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, j < i → C i j = 0) ∧ (∀ i, C i i = 1) ∧ F = Cᵀ * diagonal h * C

/-- The value in completed-square form: $f(\vec{x}) = \sum_i h_i\,(C\vec{x})_i^2$, with
$(C\vec{x})_i = x_i + \sum_{j > i} c_{ij}x_j$. -/
theorem val_eq_of_isSqDecomp {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) (x : Fin n → ℝ) : val F x = ∑ i, h i * (C *ᵥ x) i ^ 2 := by
  unfold val
  rw [hd.2.2, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal, pow_two]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The matrix `C` of a decomposition has determinant `1` (unitriangular). -/
private theorem det_C {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) : C.det = 1 := by
  rw [det_of_isUpperTriangular (fun i j hij => hd.1 i j hij)]
  simp [hd.2.1]

/-- `C *ᵥ (C⁻¹ *ᵥ v) = v` for a decomposition matrix `C`. -/
private theorem mulVec_inv_C {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) (v : Fin n → ℝ) : C *ᵥ (C⁻¹ *ᵥ v) = v := by
  have hU : IsUnit C.det := by rw [det_C hd]; exact isUnit_one
  rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]

/-- Positivity of the `h_i` (proof of `IsSqDecomp.pos`, available before the existence theorem). -/
private theorem pos_aux {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {h : Fin n → ℝ}
    {C : Matrix (Fin n) (Fin n) ℝ} (hd : IsSqDecomp F h C) (i : Fin n) : 0 < h i := by
  classical
  have hCx := mulVec_inv_C hd (Pi.single i 1)
  have hx : C⁻¹ *ᵥ (Pi.single i 1 : Fin n → ℝ) ≠ 0 := fun h0 => by
    rw [h0, mulVec_zero] at hCx
    have := congrFun hCx i
    simp at this
  have := ((posDef_iff F).1 hF).2 _ hx
  rw [val_eq_of_isSqDecomp hd, hCx] at this
  simpa [Pi.single_apply] using this

/-- **Existence** (completing the square; Mathlib's $LDL^{\mathsf T}$): a strictly positive definite $F$ has a
decomposition $F = C^{\mathsf T}\mathrm{diag}(h)C$ with $C$ upper unitriangular and all $h_i > 0$. -/
theorem exists_isSqDecomp {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    ∃ h C, IsSqDecomp F h C ∧ ∀ i, 0 < h i := by
  classical
  have hlow := LDL.isLowerTriangular_lower hF
  have hLdiag : ∀ i, LDL.lower hF i i ≠ 0 := by
    intro i
    have hdet : (LDL.lower hF).det ≠ 0 := by
      have := (LDL.invertibleLowerInv hF)
      rw [LDL.lower]
      exact (isUnit_iff_ne_zero.1 (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_of_invertible _)))
    rw [det_of_isLowerTriangular _ hlow] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  set L := LDL.lower hF with hL
  set d : Fin n → ℝ := fun i => L i i with hd
  set C : Matrix (Fin n) (Fin n) ℝ := (L * diagonal (fun j => (d j)⁻¹))ᵀ with hC
  have hLC : L = Cᵀ * diagonal d := by
    rw [hC, transpose_transpose, Matrix.mul_assoc, diagonal_mul_diagonal]
    have : (fun j => (d j)⁻¹ * d j) = 1 := by
      funext j; exact inv_mul_cancel₀ (hLdiag j)
    rw [this]; simp
  have hS : F = L * diagonal (LDL.diagEntries hF) * Lᵀ := by
    have := (LDL.lower_conj_diag hF).symm
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdec : IsSqDecomp F (fun i => d i * LDL.diagEntries hF i * d i) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      simp only [hC, transpose_apply, mul_apply, diagonal_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have : L j i = 0 := hlow (by simpa using hij)
      rw [this, zero_mul]
    · intro i
      simp only [hC, transpose_apply, mul_apply, diagonal_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact mul_inv_cancel₀ (hLdiag i)
    · refine hS.trans ?_
      clear_value C d L
      rw [hLC, transpose_mul, transpose_transpose, diagonal_transpose]
      simp only [Matrix.mul_assoc, diagonal_mul_diagonal]
      rw [← Matrix.mul_assoc (diagonal _) (diagonal d) C, diagonal_mul_diagonal]
  exact ⟨_, C, hdec, pos_aux hF hdec⟩

/-- **Uniqueness:** if $F$ is strictly positive definite, its decomposition is unique. -/
theorem IsSqDecomp.unique {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {h h' : Fin n → ℝ}
    {C C' : Matrix (Fin n) (Fin n) ℝ} (hd : IsSqDecomp F h C) (hd' : IsSqDecomp F h' C') : h = h' ∧ C = C' := by
  classical
  have hU : IsUnit C.det := by rw [det_C hd]; exact isUnit_one
  have hU' : IsUnit C'.det := by rw [det_C hd']; exact isUnit_one
  have : Invertible C := invertibleOfIsUnitDet _ hU
  have : Invertible C' := invertibleOfIsUnitDet _ hU'
  have hup : ∀ {X : Matrix (Fin n) (Fin n) ℝ}, (∀ i j, j < i → X i j = 0) → X.BlockTriangular id :=
    fun hX i j hij => hX i j hij
  have hPup : ∀ i j, j < i → C⁻¹ i j = 0 := fun i j hij =>
    blockTriangular_inv_of_blockTriangular (hup hd.1) hij
  have hP'up : ∀ i j, j < i → C'⁻¹ i j = 0 := fun i j hij =>
    blockTriangular_inv_of_blockTriangular (hup hd'.1) hij
  -- diagonal of a product of upper triangular matrices
  have hmd : ∀ (X Y : Matrix (Fin n) (Fin n) ℝ), (∀ i j, j < i → X i j = 0) →
      (∀ i j, j < i → Y i j = 0) → ∀ i, (X * Y) i i = X i i * Y i i := by
    intro X Y hX hY i
    rw [mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hX i k hk, zero_mul]
      · rw [hY k i hk, mul_zero]
    · simp
  have hPd : ∀ i, C⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (mul_nonsing_inv C hU) i) i
    rw [hmd _ _ hd.1 hPup, hd.2.1] at this
    simpa using this
  have hP'd : ∀ i, C'⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (mul_nonsing_inv C' hU') i) i
    rw [hmd _ _ hd'.1 hP'up, hd'.2.1] at this
    simpa using this
  have hAup : ∀ i j, j < i → (C * C'⁻¹) i j = 0 := by
    intro i j hij
    rw [mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge j k with hjk | hjk
    · rw [hP'up k j hjk, mul_zero]
    · rw [hd.1 i k (lt_of_le_of_lt hjk hij), zero_mul]
  have hBup : ∀ i j, j < i → (C' * C⁻¹) i j = 0 := by
    intro i j hij
    rw [mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge j k with hjk | hjk
    · rw [hPup k j hjk, mul_zero]
    · rw [hd'.1 i k (lt_of_le_of_lt hjk hij), zero_mul]
  -- the key identity  (C C'⁻¹)ᵀ D = D' (C' C⁻¹)
  have key : (C * C'⁻¹)ᵀ * diagonal h = diagonal h' * (C' * C⁻¹) := by
    have e : Cᵀ * diagonal h * C = C'ᵀ * diagonal h' * C' := hd.2.2.symm.trans hd'.2.2
    have e1 : (C * C'⁻¹)ᵀ * diagonal h = diagonal h' * (C' * C⁻¹) := by
      calc (C * C'⁻¹)ᵀ * diagonal h
          = (C'⁻¹)ᵀ * (Cᵀ * diagonal h * C) * C⁻¹ := by
            rw [transpose_mul]
            simp only [Matrix.mul_assoc, mul_nonsing_inv _ hU, Matrix.mul_one]
        _ = (C'⁻¹)ᵀ * (C'ᵀ * diagonal h' * C') * C⁻¹ := by rw [e]
        _ = diagonal h' * (C' * C⁻¹) := by
            have : (C'⁻¹)ᵀ * C'ᵀ = 1 := by
              rw [← transpose_mul, mul_nonsing_inv _ hU', transpose_one]
            calc (C'⁻¹)ᵀ * (C'ᵀ * diagonal h' * C') * C⁻¹
                = ((C'⁻¹)ᵀ * C'ᵀ) * diagonal h' * C' * C⁻¹ := by simp only [Matrix.mul_assoc]
              _ = _ := by rw [this]; simp only [Matrix.one_mul, Matrix.mul_assoc]
    exact e1
  have hh0 : ∀ i, h i ≠ 0 := fun i => (pos_aux hF hd i).ne'
  have hA1 : C * C'⁻¹ = 1 := by
    ext p q
    rcases lt_trichotomy p q with hpq | rfl | hpq
    · have := congrFun (congrFun key q) p
      rw [mul_apply, mul_apply] at this
      simp only [transpose_apply, diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
      rw [hBup q p hpq, mul_zero] at this
      have h2 : (C * C'⁻¹) p q * h p = 0 := by simpa [mul_apply] using this
      simpa [hh0 p, one_apply_ne hpq.ne] using h2
    · rw [hmd _ _ hd.1 hP'up, hd.2.1, hP'd]; simp
    · rw [hAup p q hpq, one_apply_ne hpq.ne']
  have hCC : C = C' := by
    have := congrArg (· * C') hA1
    simpa [Matrix.mul_assoc, nonsing_inv_mul _ hU'] using this
  subst hCC
  refine ⟨?_, rfl⟩
  rw [hA1] at key
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at key
  funext i
  simpa using congrFun (congrFun key i) i

/-- For strictly positive definite $F$ every $h_i$ in a decomposition is positive. -/
theorem IsSqDecomp.pos {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {h : Fin n → ℝ}
    {C : Matrix (Fin n) (Fin n) ℝ} (hd : IsSqDecomp F h C) (i : Fin n) : 0 < h i := by
  exact pos_aux hF hd i

/-- Conversely, if all $h_i > 0$ then $F$ is strictly positive definite. -/
theorem IsSqDecomp.posDef {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) (hh : ∀ i, 0 < h i) : F.PosDef := by
  classical
  rw [posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hd.2.2]
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, diagonal_transpose, transpose_transpose, Matrix.mul_assoc]
  · rw [val_eq_of_isSqDecomp hd]
    have hU : IsUnit C.det := by rw [det_C hd]; exact isUnit_one
    have hCx : C *ᵥ x ≠ 0 := fun h0 => hx (by
      have := congrArg (C⁻¹ *ᵥ ·) h0
      simpa [mulVec_mulVec, nonsing_inv_mul _ hU] using this)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hCx
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hh j).le (sq_nonneg _)) ⟨i, Finset.mem_univ _, ?_⟩
    exact mul_pos (hh i) (by simpa using pow_pos (abs_pos.2 hi) 2 |>.trans_eq (sq_abs _))

/-- **The determinant** (Cassels, Ch. 12, p. 265, "on comparing determinants in (3.1)"): $d(f) = \det F = \prod_i h_i$. -/
theorem IsSqDecomp.det_eq {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) : F.det = ∏ i, h i := by
  rw [hd.2.2, det_mul, det_mul, det_transpose, det_C hd, det_diagonal]
  simp

/-- **The diagonal coefficients** (Cassels, Ch. 12, (3.2), p. 264): $f_{jj} = \sum_{i \le j} h_i c_{ij}^2$
(with $c_{jj} = 1$); in particular $f_{jj} \ge h_j$ when all $h_i \ge 0$. -/
theorem IsSqDecomp.diag_eq {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) (j : Fin n) : F j j = ∑ i ∈ Finset.Iic j, h i * C i j ^ 2 := by
  rw [hd.2.2, mul_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic j))]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_diagonal, transpose_apply]; ring
  · intro i _ hi
    have : C i j = 0 := hd.1 i j (by simpa using hi)
    simp [mul_diagonal, this]

/-- The entries above the diagonal (Cassels, Ch. 12, p. 265): $f_{ij} = h_i c_{ij} + \sum_{k < i} h_k c_{ki}c_{kj}$ for
$i < j$. -/
theorem IsSqDecomp.offdiag_eq {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) {i j : Fin n} (hij : i < j) :
    F i j = h i * C i j + ∑ k ∈ Finset.Iio i, h k * C k i * C k j := by
  rw [hd.2.2, mul_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic i)), ← Finset.Iio_insert,
    Finset.sum_insert Finset.notMem_Iio_self]
  · simp only [mul_diagonal, transpose_apply, hd.2.1]
    refine congrArg₂ _ (by ring) (Finset.sum_congr rfl fun k _ => ?_)
    ring
  · intro k _ hk
    have : C k i = 0 := hd.1 k i (by simpa using hk)
    simp [mul_diagonal, this]

/-- **Lower bound by the last coordinate** (Cassels, Ch. 12, proof of Lemma 4.1, p. 267): if all $h_i \ge 0$ and the
integral vector $\vec{a}$ has $a_k \ne 0$ and $a_i = 0$ for $i > k$, then $f(\vec{a}) \ge h_k$
(indeed $(C\vec{a})_k = a_k$ and $a_k^2 \ge 1$). -/
theorem IsSqDecomp.val_ge {F : Matrix (Fin n) (Fin n) ℝ} {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hd : IsSqDecomp F h C) (hh : ∀ i, 0 ≤ h i) {a : Fin n → ℤ} {k : Fin n} (hk : a k ≠ 0)
    (hz : ∀ i, k < i → a i = 0) : h k ≤ val F (cast a) := by
  rw [val_eq_of_isSqDecomp hd]
  have hCa : (C *ᵥ cast a) k = (a k : ℝ) := by
    rw [mulVec, dotProduct, Finset.sum_eq_single k]
    · rw [hd.2.1, one_mul]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [hd.1 k j hj, zero_mul]
      · rw [show cast a j = 0 by simp [hz j hj], mul_zero]
    · simp
  have h1 : (1 : ℝ) ≤ (a k : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ a k ^ 2 := by nlinarith [sq_pos_of_ne_zero hk]
    exact_mod_cast this
  calc h k = h k * 1 := (mul_one _).symm
    _ ≤ h k * (C *ᵥ cast a) k ^ 2 := by rw [hCa]; exact mul_le_mul_of_nonneg_left h1 (hh k)
    _ ≤ _ := Finset.single_le_sum (f := fun i => h i * (C *ᵥ cast a) i ^ 2)
        (fun i _ => mul_nonneg (hh i) (sq_nonneg _)) (Finset.mem_univ k)

end QuadFormsKB.Reduction
