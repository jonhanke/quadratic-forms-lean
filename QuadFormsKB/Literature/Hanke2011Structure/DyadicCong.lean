/-
# Hanke 2011, §2: congruence of even symmetric matrices (infrastructure for the dyadic cases of Thm. 2.6)

Algebraic infrastructure, used by `DyadicBinary.lean` and `DyadicClassify.lean`. No result of the paper is stated here.

**Congruence.** `Cong H H'` for square matrices `H`, `H'` over a commutative ring, on possibly different finite index
types: there are mutually inverse matrices `U`, `U'` with $H' = U^{\mathsf T} H U$. It is reflexive, symmetric,
transitive, invariant under reindexing (`cong_submatrix`), and compatible with block sums (`Cong.fromBlocks`).

**Hessian matrices.** `IsHess H` ($H = G + G^{\mathsf T}$ for some matrix $G$) is the matrix property of being the
Hessian matrix $H = C + C^{\mathsf T}$ of a quadratic form (`QuadForm.hessian`). It is invariant under congruence
(`IsHess.cong`) and under taking the inverse (`IsHess.inv`), and a symmetric block matrix with an invertible Hessian
corner splits off that corner (`exists_cong_fromBlocks`, the Schur complement).
-/
import Mathlib

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure.Dyadic

section Cong

variable {R : Type*} [CommRing R]
variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

/-- **Congruence** of square matrices on possibly different finite index types: $H' = U^{\mathsf T}HU$ for mutually
inverse $U$ ($\iota \times \kappa$) and $U'$ ($\kappa \times \iota$). -/
def Cong (H : Matrix ι ι R) (H' : Matrix κ κ R) : Prop :=
  ∃ (U : Matrix ι κ R) (U' : Matrix κ ι R), U * U' = 1 ∧ U' * U = 1 ∧ H' = Uᵀ * H * U

theorem Cong.refl (H : Matrix ι ι R) : Cong H H := ⟨1, 1, by simp, by simp, by simp⟩

theorem Cong.symm {H : Matrix ι ι R} {H' : Matrix κ κ R} (h : Cong H H') : Cong H' H := by
  obtain ⟨U, U', h1, h2, h3⟩ := h
  refine ⟨U', U, h2, h1, ?_⟩
  rw [h3]
  calc H = (U * U')ᵀ * H * (U * U') := by rw [h1]; simp
    _ = U'ᵀ * (Uᵀ * H * U) * U' := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem Cong.trans {H : Matrix ι ι R} {H' : Matrix κ κ R} {H'' : Matrix μ μ R} (h : Cong H H')
    (h' : Cong H' H'') : Cong H H'' := by
  obtain ⟨U, U', h1, h2, h3⟩ := h
  obtain ⟨V, V', g1, g2, g3⟩ := h'
  refine ⟨U * V, V' * U', ?_, ?_, ?_⟩
  · calc U * V * (V' * U') = U * (V * V') * U' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [g1, Matrix.mul_one, h1]
  · calc V' * U' * (U * V) = V' * (U' * U) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, g2]
  · rw [g3, h3]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Reindexing by an equivalence is a congruence. -/
theorem cong_submatrix (H : Matrix ι ι R) (e : κ ≃ ι) : Cong H (H.submatrix e e) := by
  refine ⟨(1 : Matrix ι ι R).submatrix id e, (1 : Matrix ι ι R).submatrix e id, ?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv]; simp
  · ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply]
  · rw [Matrix.transpose_submatrix, Matrix.transpose_one]
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply]

/-- Conjugating by a matrix with unit determinant is a congruence. -/
theorem cong_of_isUnit_det (H : Matrix ι ι R) (U : Matrix ι ι R) (hU : IsUnit U.det) :
    Cong H (Uᵀ * H * U) :=
  ⟨U, U⁻¹, Matrix.mul_nonsing_inv U hU, Matrix.nonsing_inv_mul U hU, rfl⟩

/-- Congruent matrices live on index types of the same cardinality (for a nontrivial ring). -/
theorem Cong.card_eq [Nontrivial R] {H : Matrix ι ι R} {H' : Matrix κ κ R} (h : Cong H H') :
    Fintype.card ι = Fintype.card κ := by
  obtain ⟨U, U', h1, h2, -⟩ := h
  let e : (κ → R) ≃ₗ[R] (ι → R) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' U) (Matrix.toLin' U') (by
      rw [← Matrix.toLin'_mul, h1]; exact Matrix.toLin'_one) (by
      rw [← Matrix.toLin'_mul, h2]; exact Matrix.toLin'_one)
  have := LinearEquiv.finrank_eq e
  simpa using this.symm

/-- **Determinants of congruent matrices differ by a unit square.** -/
theorem Cong.det [Nontrivial R] {H : Matrix ι ι R} {H' : Matrix κ κ R} (h : Cong H H') :
    ∃ w : R, IsUnit w ∧ H'.det = w ^ 2 * H.det := by
  obtain ⟨U, U', h1, h2, h3⟩ := h
  obtain ⟨e⟩ : Nonempty (ι ≃ κ) := ⟨Fintype.equivOfCardEq (Cong.card_eq ⟨U, U', h1, h2, h3⟩)⟩
  let V : Matrix ι ι R := U.submatrix id e
  let V' : Matrix ι ι R := U'.submatrix e id
  have hV : V * V' = 1 := by
    simp only [V, V']; rw [Matrix.submatrix_mul_equiv]; simpa using h1
  have hV' : V' * V = 1 := by
    ext i j
    simp only [V, V', Matrix.mul_apply, Matrix.submatrix_apply]
    have := congrFun (congrFun h2 (e i)) (e j)
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hH : H'.submatrix e e = Vᵀ * H * V := by
    rw [h3]; simp only [V, Matrix.transpose_submatrix]
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  refine ⟨V.det, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse hV
  · have := congrArg Matrix.det hH
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
    rw [this]; ring

end Cong

section Blocks

variable {R : Type*} [CommRing R]
variable {ι κ μ ν : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  [DecidableEq μ] [DecidableEq ν]

/-- Congruent summands give congruent block-diagonal sums. -/
theorem Cong.fromBlocks {A : Matrix ι ι R} {A' : Matrix κ κ R} {S : Matrix μ μ R} {S' : Matrix ν ν R}
    (hA : Cong A A') (hS : Cong S S') :
    Cong (Matrix.fromBlocks A 0 0 S) (Matrix.fromBlocks A' 0 0 S') := by
  obtain ⟨U, U', h1, h2, h3⟩ := hA
  obtain ⟨V, V', g1, g2, g3⟩ := hS
  refine ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks U' 0 0 V', ?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply]; simp [h1, g1]
  · rw [Matrix.fromBlocks_multiply]; simp [h2, g2]
  · rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, h3, g3]
    simp

/-- Swapping the two summands is a congruence. -/
theorem cong_fromBlocks_swap (A : Matrix ι ι R) (S : Matrix μ μ R) :
    Cong (Matrix.fromBlocks A 0 0 S) (Matrix.fromBlocks S 0 0 A) := by
  have := cong_submatrix (Matrix.fromBlocks A 0 0 S) (Equiv.sumComm μ ι)
  simpa [Matrix.fromBlocks_submatrix_sum_swap_sum_swap] using this

/-- Reindexing a summand. -/
theorem cong_fromBlocks_reindex (A : Matrix ι ι R) (S : Matrix μ μ R) (e : ν ≃ μ) :
    Cong (Matrix.fromBlocks A 0 0 S) (Matrix.fromBlocks A 0 0 (S.submatrix e e)) :=
  Cong.fromBlocks (Cong.refl A) (cong_submatrix S e)

end Blocks

section Hess

variable {R : Type*} [CommRing R]
variable {ι κ μ ν : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  [DecidableEq μ] [DecidableEq ν]

/-- **Hessian matrices:** $H = G + G^{\mathsf T}$ for some matrix $G$, i.e. $H = C + C^{\mathsf T}$ is the Hessian
matrix of a quadratic form with coefficient matrix $C$ (`QuadForm.hessian`); equivalently $H$ is symmetric with
diagonal in $2R$ when $2$ is not a zero divisor. -/
def IsHess (H : Matrix ι ι R) : Prop := ∃ G : Matrix ι ι R, H = G + Gᵀ

theorem IsHess.symm_eq {H : Matrix ι ι R} (h : IsHess H) : Hᵀ = H := by
  obtain ⟨G, rfl⟩ := h
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem IsHess.cong {H : Matrix ι ι R} {H' : Matrix κ κ R} (h : IsHess H) (hc : Cong H H') : IsHess H' := by
  obtain ⟨G, rfl⟩ := h
  obtain ⟨U, U', -, -, h3⟩ := hc
  refine ⟨Uᵀ * G * U, ?_⟩
  rw [h3]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem IsHess.inv {A B : Matrix ι ι R} (hA : IsHess A) (_h1 : A * B = 1) (h2 : B * A = 1) : IsHess B := by
  have hAs := hA.symm_eq
  obtain ⟨G, hG⟩ := hA
  have hBs : Bᵀ = B := by
    have h3 : A * Bᵀ = 1 := by
      have := congrArg Matrix.transpose h2
      rwa [Matrix.transpose_mul, hAs, Matrix.transpose_one] at this
    calc Bᵀ = (B * A) * Bᵀ := by rw [h2, Matrix.one_mul]
      _ = B := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]
  refine ⟨B * G * B, ?_⟩
  have : B = B * A * B := by rw [h2, Matrix.one_mul]
  conv_lhs => rw [this, hG]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc, hBs]

theorem IsHess.fromBlocks {A : Matrix ι ι R} {S : Matrix μ μ R} (hA : IsHess A) (hS : IsHess S) :
    IsHess (Matrix.fromBlocks A 0 0 S) := by
  obtain ⟨G, rfl⟩ := hA
  obtain ⟨G', rfl⟩ := hS
  refine ⟨Matrix.fromBlocks G 0 0 G', ?_⟩
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_add]; simp

theorem IsHess.submatrix {H : Matrix ι ι R} (h : IsHess H) (e : κ → ι) : IsHess (H.submatrix e e) := by
  obtain ⟨G, rfl⟩ := h
  exact ⟨G.submatrix e e, by ext i j; simp⟩

/-- **Splitting off an invertible Hessian corner** (Schur complement): a Hessian matrix $H$ on $\iota \oplus \mu$
whose top-left block $A$ has unit determinant is congruent to $A \oplus S$, with $S$ again a Hessian matrix and
$\det H = \det A \det S$. -/
theorem exists_cong_fromBlocks (H : Matrix (ι ⊕ μ) (ι ⊕ μ) R) (hH : IsHess H)
    (hA : IsUnit H.toBlocks₁₁.det) :
    ∃ S : Matrix μ μ R, IsHess S ∧ Cong H (Matrix.fromBlocks H.toBlocks₁₁ 0 0 S) ∧
      H.det = H.toBlocks₁₁.det * S.det := by
  set A := H.toBlocks₁₁ with hAdef
  set B := H.toBlocks₁₂ with hBdef
  set D := H.toBlocks₂₂ with hDdef
  have hsym := hH.symm_eq
  have hC : H.toBlocks₂₁ = Bᵀ := by
    ext i j
    have := congrFun (congrFun hsym (Sum.inr i)) (Sum.inl j)
    simp only [Matrix.transpose_apply] at this
    simp [hBdef, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, this]
  have hHdecomp : H = Matrix.fromBlocks A B Bᵀ D := by
    rw [← hC, hAdef, hBdef, hDdef, Matrix.fromBlocks_toBlocks]
  obtain ⟨G, hG⟩ := hH
  have hAH : IsHess A := by
    refine ⟨G.toBlocks₁₁, ?_⟩
    ext i j
    have := congrFun (congrFun hG (Sum.inl i)) (Sum.inl j)
    simpa [hAdef, Matrix.toBlocks₁₁] using this
  have hDH : IsHess D := by
    refine ⟨G.toBlocks₂₂, ?_⟩
    ext i j
    have := congrFun (congrFun hG (Sum.inr i)) (Sum.inr j)
    simpa [hDdef, Matrix.toBlocks₂₂] using this
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  have hAinv1 : A * ⅟A = 1 := mul_invOf_self A
  have hAinv2 : ⅟A * A = 1 := invOf_mul_self A
  have hKH : IsHess (⅟A) := hAH.inv hAinv1 hAinv2
  have hKs := hKH.symm_eq
  obtain ⟨K, hK⟩ := hKH
  obtain ⟨GD, hGD⟩ := hDH
  have hLdecomp := Matrix.fromBlocks_eq_of_invertible₁₁ A B Bᵀ D
  refine ⟨D - Bᵀ * ⅟A * B, ⟨GD - Bᵀ * K * B, ?_⟩, ?_, ?_⟩
  · rw [hGD, hK]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  · have hc : Cong (Matrix.fromBlocks A 0 0 (D - Bᵀ * ⅟A * B)) H := by
      refine ⟨Matrix.fromBlocks 1 (⅟A * B) 0 1, Matrix.fromBlocks 1 (-(⅟A * B)) 0 1, ?_, ?_, ?_⟩
      · rw [Matrix.fromBlocks_multiply]; simp
      · rw [Matrix.fromBlocks_multiply]; simp
      · rw [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_mul,
          hKs]
        conv_lhs => rw [hHdecomp, hLdecomp]
        simp
    exact hc.symm
  · conv_lhs => rw [hHdecomp]
    rw [Matrix.det_fromBlocks₁₁]

end Hess

end QuadFormsKB.Hanke2011Structure.Dyadic
