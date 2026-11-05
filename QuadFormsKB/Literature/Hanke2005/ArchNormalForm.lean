/-
# Hanke 2005, (2.9): normal forms at archimedean places

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Defines** `phiQn n r` $=\mathrm{diag}[1_{n-r}, -1_r]$ on `Fin n`.

**Proves**
* `exists_normalForm_real`: a nondegenerate real form is $\cong c\cdot\mathrm{diag}[1_{n-r}, -1_r]$ with $c = \pm1$,
  $r$ = its Witt index, $2r\le n$ (Sylvester's law with Hanke's normalization (2.9));
* `exists_normalForm_complex`: a nondegenerate complex form is $\cong$ the sum of squares.
-/
import QuadFormsKB.Tamagawa.Measure.LerayReal
import QuadFormsKB.Tamagawa.Measure.LerayComplex
import QuadFormsKB.Literature.OMeara.Sec61
import QuadFormsKB.Literature.Hanke2005.MassFormula
import QuadFormsKB.Literature.Hanke2005.WittDiag

open Matrix
open QuadFormsKB.Siegel
open QuadFormsKB.Tamagawa.Measure.LerayComplex (gramC gramDetC)

noncomputable section

namespace QuadFormsKB.Hanke2005

/-- $\mathrm{diag}[1_{n-r}, -1_r]$ on `Fin n`. -/
def phiQn (n r : ℕ) : QuadForm ℝ n := QuadForm.diag fun i => if (i : ℕ) < n - r then 1 else -1

theorem hessian_diag_field {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → K) :
    (QuadForm.diag a).hessian = diagonal fun i => 2 * a i := by
  ext i j
  simp only [QuadForm.hessian, QuadForm.diag, Matrix.add_apply, transpose_apply, diagonal_apply]
  by_cases h : i = j
  · subst h; simp; ring
  · simp [h, Ne.symm h]

/-- A sign vector with $r$ entries $-1$ can be permuted to $\mathrm{diag}[1_{n-r}, -1_r]$. -/
theorem exists_perm_signs {n r : ℕ} (hr : r ≤ n) (D : Fin n → ℝ) (hD : ∀ k, D k = 1 ∨ D k = -1)
    (hcnt : (Finset.univ.filter fun k => D k = -1).card = r) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, D (σ i) = if (i : ℕ) < n - r then 1 else -1 := by
  classical
  let f : Fin n → Bool := fun i => decide ((i : ℕ) < n - r)
  let g : Fin n → Bool := fun k => decide (D k = 1)
  have hlt : (Finset.univ.filter fun i : Fin n => (i : ℕ) < n - r).card = n - r := by
    rw [Fin.card_filter_val_lt]; omega
  have hsplit : (Finset.univ.filter fun k => D k = 1).card + (Finset.univ.filter fun k => D k = -1).card = n := by
    have hdisj : Disjoint (Finset.univ.filter fun k => D k = 1) (Finset.univ.filter fun k => D k = -1) := by
      rw [Finset.disjoint_filter]; intro k _ h1 h2; rw [h1] at h2; norm_num at h2
    have hu : (Finset.univ.filter fun k => D k = 1) ∪ (Finset.univ.filter fun k => D k = -1) = Finset.univ := by
      ext k; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact hD k
    rw [← Finset.card_union_of_disjoint hdisj, hu, Finset.card_univ, Fintype.card_fin]
  have hone : (Finset.univ.filter fun k => D k = 1).card = n - r := by omega
  have e : ∀ b : Bool, {i // f i = b} ≃ {k // g k = b} := by
    intro b
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_subtype, Fintype.card_subtype]
    cases b
    · have h1 : (Finset.univ.filter fun i : Fin n => f i = false).card = r := by
        have : (Finset.univ.filter fun i : Fin n => f i = false) =
            Finset.univ \ (Finset.univ.filter fun i : Fin n => (i : ℕ) < n - r) := by
          ext i; simp [f]
        rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hlt]
        omega
      have h2 : (Finset.univ.filter fun k : Fin n => g k = false) = Finset.univ.filter fun k => D k = -1 := by
        ext k; rcases hD k with h | h <;> simp [g, h] <;> norm_num
      rw [h1, h2, hcnt]
    · have h2 : (Finset.univ.filter fun k : Fin n => g k = true) = Finset.univ.filter fun k => D k = 1 := by
        ext k; simp [g]
      have h1 : (Finset.univ.filter fun i : Fin n => f i = true) = Finset.univ.filter fun i : Fin n => (i : ℕ) < n - r := by
        ext i; simp [f]
      rw [h1, h2, hlt, hone]
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_⟩
  have := Equiv.ofFiberEquiv_map e i
  simp only [f, g] at this
  by_cases h : (i : ℕ) < n - r
  · simp only [h, decide_true, decide_eq_true_eq] at this ⊢; exact this
  · simp only [h, decide_false, decide_eq_false_iff_not] at this ⊢
    rcases hD (Equiv.ofFiberEquiv e i) with h' | h'
    · exact absurd h' this
    · exact h'

/-- The linear equivalence $y\mapsto Py$ of $\mathbb R^n$ for $P\in GL_n(\mathbb R)$. -/
def glEquiv {n : ℕ} (P : GL (Fin n) ℝ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun y := (P : Matrix (Fin n) (Fin n) ℝ) *ᵥ y
  invFun x := ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x
  map_add' x y := Matrix.mulVec_add _ _ _
  map_smul' c x := Matrix.mulVec_smul _ _ _
  left_inv y := by simp [Matrix.mulVec_mulVec]
  right_inv x := by simp [Matrix.mulVec_mulVec]

/-- **Witt index from a diagonalization**: if $P^{\mathsf T}AP = \mathrm{diag}(d)$ then the Witt index of $Q$ is
$\min(\#\{d_i>0\}, \#\{d_i<0\})$ (O'Meara §61A, `wittIndex_eq_min`, and Sylvester's law). -/
theorem wittIndex_of_diag {n : ℕ} (Q : QuadForm ℝ n) (hQ : gramDetR Q ≠ 0) (P : GL (Fin n) ℝ)
    (d : Fin n → ℝ) (hP : (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * P = diagonal d) :
    QuadraticForm.wittIndex Q.toQuadraticForm = min {i | 0 < d i}.ncard {i | d i < 0}.ncard := by
  have hnd : Q.Nondegenerate := fun h => hQ (by simp [gramDetR, h])
  have hnd' : (QuadraticMap.polarBilin Q.toQuadraticForm).Nondegenerate := by
    have h := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := ℝ) (Q := Q) hnd
    have e : Q.toQuadraticFormIn ℝ = Q.toQuadraticForm := by
      unfold QuadForm.toQuadraticFormIn
      congr 1
    rw [e] at h; exact h
  have hrad := QuadraticForm.radical_eq_bot_of_nondegenerate _ hnd'
  have e : (QuadraticMap.weightedSumSquares ℝ d).Equivalent Q.toQuadraticForm := by
    refine ⟨{ toLinearEquiv := glEquiv P, map_app' := ?_ }⟩
    intro y
    show Q.toQuadraticForm ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) = _
    rw [QuadForm.toQuadraticForm_apply, QuadFormsKB.Siegel.eval_real_eq_gramR, QuadraticMap.weightedSumSquares_apply]
    have : ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) ⬝ᵥ (gramMatrixR Q *ᵥ ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ y)) =
        y ⬝ᵥ ((diagonal d) *ᵥ y) := by
      rw [← hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec y ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ), Matrix.vecMul_transpose]
    rw [this]
    simp only [dotProduct, mulVec_diagonal, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e' := e.symm
  rw [QuadFormsKB.OMeara.wittIndex_eq_min _ hrad, QuadraticForm.sigPos_of_equiv_weightedSumSquares e',
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares e']

/-- Sign data of a nonvanishing real vector: $c = \pm1$, $r = \min(\#\{d>0\},\#\{d<0\})$ and $c\cdot\mathrm{sgn}(d)$ has
exactly $r$ entries $-1$. -/
theorem sign_data {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    ∃ (r : ℕ) (c : ℝ), r = min {i | 0 < d i}.ncard {i | d i < 0}.ncard ∧ 2 * r ≤ n ∧ (c = 1 ∨ c = -1) ∧
      (Finset.univ.filter fun k => c * (if 0 < d k then (1 : ℝ) else -1) = -1).card = r := by
  classical
  set pf := Finset.univ.filter fun k => 0 < d k with hpf
  set mf := Finset.univ.filter fun k => d k < 0 with hmf
  have hp : {i | 0 < d i}.ncard = pf.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext; simp [hpf]
  have hm : {i | d i < 0}.ncard = mf.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext; simp [hmf]
  have hsum : pf.card + mf.card = n := by
    have hdisj : Disjoint pf mf := by
      rw [hpf, hmf, Finset.disjoint_filter]; intro k _ h1 h2; linarith
    have hu : pf ∪ mf = Finset.univ := by
      ext k; simp only [hpf, hmf, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases lt_or_gt_of_ne (hd k) with h | h
      · exact Or.inr h
      · exact Or.inl h
    rw [← Finset.card_union_of_disjoint hdisj, hu, Finset.card_univ, Fintype.card_fin]
  rw [hp, hm]
  by_cases hle : mf.card ≤ pf.card
  · refine ⟨mf.card, 1, (min_eq_right hle).symm, by omega, Or.inl rfl, ?_⟩
    have : (Finset.univ.filter fun k => (1 : ℝ) * (if 0 < d k then (1 : ℝ) else -1) = -1) = mf := by
      ext k
      simp only [hmf, Finset.mem_filter, Finset.mem_univ, true_and, one_mul]
      by_cases h : 0 < d k
      · have h' : ¬ d k < 0 := not_lt.mpr h.le
        simp [h, h']; norm_num
      · have h' : d k < 0 := lt_of_le_of_ne (not_lt.mp h) (hd k)
        simp [h, h']
    rw [this]
  · refine ⟨pf.card, -1, (min_eq_left (by omega)).symm, by omega, Or.inr rfl, ?_⟩
    have : (Finset.univ.filter fun k => (-1 : ℝ) * (if 0 < d k then (1 : ℝ) else -1) = -1) = pf := by
      ext k
      simp only [hpf, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : 0 < d k
      · simp [h]
      · simp [h]; norm_num
    rw [this]

theorem diagonal_submatrix_perm {n : ℕ} (D : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    (diagonal D).submatrix σ σ = diagonal (fun i => D (σ i)) := by
  ext i j
  simp only [submatrix_apply, diagonal_apply, σ.injective.eq_iff]

theorem congr_submatrix_perm {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) :
    (P.submatrix id σ)ᵀ * A * (P.submatrix id σ) = (Pᵀ * A * P).submatrix σ σ := by
  ext i j
  simp [Matrix.mul_apply, transpose_apply, submatrix_apply]

/-- **Sylvester's law with Hanke's normalization (2.9)** (Hanke thesis, (2.9), p. 6; O'Meara 1963, §61A, p. 155): a
nondegenerate real form is $\cong c\cdot\mathrm{diag}[1_{n-r}, -1_r]$ with $c = \pm1$, where
$r$ is the Witt index of $Q$ (so $2r\le n$); precisely, $\mathrm{diag}[1_{n-r}, -1_r]$ has Hessian
$c\cdot{}^tG\,H_Q\,G$ for some $G\in GL_n(\mathbb R)$. -/
@[kb "hanke2005crelle" "(2.9), p. 6"]
theorem exists_normalForm_real {n : ℕ} (Q : QuadForm ℝ n) (hQ : gramDetR Q ≠ 0) :
    ∃ (r : ℕ) (G : GL (Fin n) ℝ) (c : ℝ), 2 * r ≤ n ∧ (c = 1 ∨ c = -1) ∧
      (phiQn n r).hessian = c • ((G : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℝ)) ∧
      r = QuadraticForm.wittIndex (QuadForm.toQuadraticForm Q) := by
  classical
  obtain ⟨P, d, hd, hP⟩ := QuadFormsKB.Tamagawa.Measure.LerayReal.exists_diag Q hQ
  obtain ⟨r, c, hr, h2r, hc, hcnt⟩ := sign_data d hd
  set S : Fin n → ℝ := fun k => if 0 < d k then (1 : ℝ) else -1 with hS
  obtain ⟨σ, hσ⟩ := exists_perm_signs (n := n) (r := r) (by omega) (fun k => c * S k)
    (fun k => by
      rcases hc with rfl | rfl <;> by_cases h : 0 < d k <;> simp [hS, h])
    hcnt
  set a : Fin n → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with ha
  have hapos : ∀ i, a i ≠ 0 := fun i => by
    have : 0 < |d i| := abs_pos.mpr (hd i)
    simp only [ha]; positivity
  have haS : ∀ i, a i * d i * a i = S i := fun i => by
    have h0 : 0 < |d i| := abs_pos.mpr (hd i)
    have h1 : Real.sqrt |d i| * Real.sqrt |d i| = |d i| := Real.mul_self_sqrt h0.le
    have h2 : Real.sqrt |d i| ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
    have e : (Real.sqrt |d i|)⁻¹ * d i * (Real.sqrt |d i|)⁻¹ = d i / (Real.sqrt |d i| * Real.sqrt |d i|) := by
      field_simp
    simp only [ha, hS]
    rw [e, h1]
    by_cases h : 0 < d i
    · simp only [h, ↓reduceIte, abs_of_pos h, div_self h.ne']
    · simp only [h, ↓reduceIte, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) (hd i)), div_neg, div_self (hd i)]
  set G1 : Matrix (Fin n) (Fin n) ℝ := (P : Matrix (Fin n) (Fin n) ℝ) * diagonal a with hG1
  have hG1S : G1ᵀ * gramMatrixR Q * G1 = diagonal S := by
    rw [hG1, transpose_mul, diagonal_transpose]
    calc diagonal a * (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * ((P : Matrix (Fin n) (Fin n) ℝ) * diagonal a)
        = diagonal a * ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * (P : Matrix (Fin n) (Fin n) ℝ)) *
            diagonal a := by simp only [Matrix.mul_assoc]
      _ = diagonal S := by
        rw [hP, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1; funext i; exact haS i
  have hdetG1 : G1.det ≠ 0 := by
    rw [hG1, det_mul, det_diagonal]
    exact mul_ne_zero (P.isUnit.map Matrix.detMonoidHom |>.ne_zero) (Finset.prod_ne_zero_iff.mpr fun i _ => hapos i)
  have hdetG : (G1.submatrix id σ).det ≠ 0 := by
    rw [Matrix.det_permute']
    exact mul_ne_zero (by simp) hdetG1
  refine ⟨r, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetG, c, h2r, hc, ?_, ?_⟩
  · show (phiQn n r).hessian = c • ((G1.submatrix id σ)ᵀ * Q.hessian * (G1.submatrix id σ))
    have hH : Q.hessian = (2 : ℝ) • gramMatrixR Q := by
      rw [gramMatrixR, smul_smul]; norm_num
    rw [hH, Matrix.mul_smul, Matrix.smul_mul, congr_submatrix_perm, hG1S, diagonal_submatrix_perm, phiQn,
      hessian_diag_field]
    ext i j
    by_cases h : i = j
    · subst h
      have := hσ i
      simp only [Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]
      rw [mul_left_comm, this]
    · simp [diagonal_apply_ne _ h]
  · have := wittIndex_of_diag Q hQ P d hP
    rw [this, ← hr]

/-- **Over $\mathbb C$ every nondegenerate form is a sum of squares** (Hanke thesis, (2.9), p. 6, complex places): there is
$G\in GL_n(\mathbb C)$ with $\mathrm{diag}[1,\dots,1]$ having Hessian ${}^tG\,H_Q\,G$. -/
@[kb "hanke2005crelle" "(2.9), p. 6 (complex places)"]
theorem exists_normalForm_complex {n : ℕ} (Q : QuadForm ℂ n) (hQ : gramDetC Q ≠ 0) :
    ∃ G : GL (Fin n) ℂ, (QuadForm.diag (fun _ : Fin n => (1 : ℂ))).hessian =
      (G : Matrix (Fin n) (Fin n) ℂ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨P, d, hd, hP⟩ := QuadFormsKB.Tamagawa.Measure.LerayComplex.exists_diag Q hQ
  have hs : ∀ i, ∃ z : ℂ, z ^ 2 = d i := fun i => IsAlgClosed.exists_pow_nat_eq (d i) two_pos
  choose s hs using hs
  have hs0 : ∀ i, s i ≠ 0 := fun i h => hd i (by rw [← hs i, h]; ring)
  set G1 : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) ℂ) * diagonal fun i => (s i)⁻¹ with hG1
  have hG1S : G1ᵀ * gramC Q * G1 = 1 := by
    rw [hG1, transpose_mul, diagonal_transpose]
    calc diagonal (fun i => (s i)⁻¹) * (P : Matrix (Fin n) (Fin n) ℂ)ᵀ *
          gramC Q *
          ((P : Matrix (Fin n) (Fin n) ℂ) * diagonal fun i => (s i)⁻¹)
        = diagonal (fun i => (s i)⁻¹) * ((P : Matrix (Fin n) (Fin n) ℂ)ᵀ *
            gramC Q * (P : Matrix (Fin n) (Fin n) ℂ)) *
            diagonal (fun i => (s i)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hP, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        rw [← hs i]; field_simp [hs0 i]
  have hdet : G1.det ≠ 0 := by
    rw [hG1, det_mul, det_diagonal]
    exact mul_ne_zero (P.isUnit.map Matrix.detMonoidHom |>.ne_zero)
      (Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hs0 i))
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  show (QuadForm.diag (fun _ : Fin n => (1 : ℂ))).hessian = G1ᵀ * Q.hessian * G1
  have hH : Q.hessian = (2 : ℂ) • gramC Q := by
    rw [gramC, smul_smul]; norm_num
  rw [hH, Matrix.mul_smul, Matrix.smul_mul, hG1S, hessian_diag_field]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

end QuadFormsKB.Hanke2005
