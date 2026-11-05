/-
# Factorization of the symplectic group over a local ring
**Layer:** algebra over a commutative local ring.

Let $R$ be a commutative local ring and $M \in \mathrm{Sp}_{2r}(R)$. Writing
$n(X) = \begin{pmatrix}1&X\\0&1\end{pmatrix}$, $\bar n(Y) = \begin{pmatrix}1&0\\Y&1\end{pmatrix}$ and
$m(A) = \begin{pmatrix}A&0\\0&{}^tA^{-1}\end{pmatrix}$, there are symmetric $r\times r$ matrices
$X, Y, Z$ and an invertible $A$ with
$$M = n(-X)\,\bar n(Y)\,m(A)\,n(Z).$$
Since $\bar n(Y) = w\,n(-Y)\,w^{-1}$ for the standard Weyl element $w$, this gives generation of
$\mathrm{Sp}_{2r}(\mathcal O_v)$ by the elements $n(B)$, $m(A)$ and $w$.

The two auxiliary lemmas are copied from Mathlib's `Mathlib/LinearAlgebra/SymplecticGroup.lean`
(adapted, Apache 2.0), where they are private.
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix SymplecticGroup

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- Over a field, if the only vector annihilated by both square matrices $A$ and $C$ is $0$, and
${}^tA\,C = {}^tC\,A$, then there is a symmetric matrix $X$ with $A + XC$ invertible.

Adapted from the private lemma `exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot` in
Mathlib's `Mathlib/LinearAlgebra/SymplecticGroup.lean` (Apache 2.0). -/
lemma exists_symm_isUnit_add_mul_field {R : Type*} [Field R]
    {A C : Matrix l l R} (hker : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) ↦ x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x → IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card l - C.rank) → R)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
      smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using hker _ heq1 heq2
    · exact f_unit hV
    · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, heq, hf,
      ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card l - C.rank)) (Fin C.rank ⊕
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def, isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
    · exact f_unit <| isUnit_nonsing_inv_iff.2 hU

/-- For any symplectic matrix $\begin{pmatrix}A&B\\C&D\end{pmatrix}$ over a local ring $R$, there
is a symmetric matrix $X$ such that $\det(A + XC)$ is a unit.

Adapted from the private lemma `exists_symmetric_X_isUnit_det_add_mul_of_symplectic` in
Mathlib's `Mathlib/LinearAlgebra/SymplecticGroup.lean` (Apache 2.0). -/
lemma exists_symm_isUnit_det_add_mul {R : Type*} [CommRing R] [IsLocalRing R]
    {A B C D : Matrix l l R}
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C).det := by
  -- We utilize the previous result on field by mapping the symplectic matrix to residue field.
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set C' := f.mapMatrix C
  set F' := fromBlocks A' (f.mapMatrix B) C' (f.mapMatrix D) with F'_def
  have hF' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.fromBlocks_map]; rfl
  have hker (x : l → k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    have hv0 : F' *ᵥ (Sum.elim x 0) = F' *ᵥ (Sum.elim 0 0) := by
      simp [fromBlocks_mulVec, hx1, hx2, F'_def]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hF' hv0)).1
  -- Now we have a symmetric matrix `Y` over the residue field s.t. `A' + Y * C'` is invertible
  -- where `A'` and `C'` are images of `A` and `C` under quotient map from `R` to its residue field.
  obtain ⟨Y, hY_symm, hY_det⟩ :=
    exists_symm_isUnit_add_mul_field hker <| by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul, (fromBlocks_mem_iff.1 hA).1, map_mul]
  -- Lift `Y` back to the ring `R` and we have the `X` we need.
  obtain ⟨X, hX_symm, hXY⟩ : ∃ X : Matrix l l R, X.IsSymm ∧ X.map f = Y := by
    choose s hs using @IsLocalRing.residue_surjective R _ _
    exact ⟨Y.map s, hY_symm.map s, Matrix.ext fun i j ↦ hs (Y i j)⟩
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  -- Ensure `A + X * C` is still invertible in `R`.
  rw [RingHom.map_det, map_add, map_mul, RingHom.mapMatrix_apply _ X, hXY]
  exact ((isUnit_iff_isUnit_det _).1 hY_det).ne_zero

/-- **Factorization of $\mathrm{Sp}_{2r}(R)$ over a local ring.** Every symplectic matrix $M$ of
size $2r$ over a commutative local ring $R$ factors as
$$M = n(-X)\,\bar n(Y)\,m(A)\,n(Z),$$
where $X, Y, Z$ are symmetric $r \times r$ matrices, $A$ is an $r\times r$ matrix with
$\det A$ a unit, and
$n(X) = \begin{pmatrix}1&X\\0&1\end{pmatrix}$, $\bar n(Y) = \begin{pmatrix}1&0\\Y&1\end{pmatrix}$,
$m(A) = \begin{pmatrix}A&0\\0&{}^tA^{-1}\end{pmatrix}$. Row and column indices are the
$0$-based index types `Fin r ⊕ Fin r`.

Proof idea: choose $X$ symmetric with $A_0 + X C$ invertible (the upper-left block of
$n(X) M$), and write $n(X)M = \bar n(C A'^{-1})\, m(A')\, n(A'^{-1} B')$ using the symplectic
relations. -/
@[kb "klingen1990" "§I.2 (generation of the symplectic group) [unverified]"]
theorem symplectic_factor_local {R : Type*} [CommRing R] [IsLocalRing R] {r : ℕ}
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R} (hM : M ∈ Matrix.symplecticGroup (Fin r) R) :
    ∃ (X Y Z A : Matrix (Fin r) (Fin r) R), Xᵀ = X ∧ Yᵀ = Y ∧ Zᵀ = Z ∧ IsUnit A.det ∧
      M = Matrix.fromBlocks 1 (-X) 0 1 * Matrix.fromBlocks 1 0 Y 1 *
        Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * Matrix.fromBlocks 1 Z 0 1 := by
  have hMb : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
      ∈ Matrix.symplecticGroup (Fin r) R := by
    rw [Matrix.fromBlocks_toBlocks]; exact hM
  set A₀ := M.toBlocks₁₁
  set B₀ := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  obtain ⟨X, hXs, hu⟩ := exists_symm_isUnit_det_add_mul hMb
  have hXt : Xᵀ = X := hXs.eq
  set A' := A₀ + X * C with hA'
  set B' := B₀ + X * D with hB'
  have hn : (fromBlocks 1 X 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R)
      ∈ Matrix.symplecticGroup (Fin r) R := by
    rw [fromBlocks_mem_iff]
    simp [hXt]
  have hNeq : (fromBlocks 1 X 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R) * M
      = fromBlocks A' B' C D := by
    rw [← M.fromBlocks_toBlocks, fromBlocks_multiply]
    simp [hA', hB']
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hN : fromBlocks A' B' C D ∈ Matrix.symplecticGroup (Fin r) R := by
    rw [← hNeq]; exact Submonoid.mul_mem _ hn hM
  obtain ⟨h1, -, h3⟩ := fromBlocks_mem_iff.1 hN
  have hNt := SymplecticGroup.transpose_mem hN
  rw [fromBlocks_transpose] at hNt
  obtain ⟨h4, -, -⟩ := fromBlocks_mem_iff.1 hNt
  simp only [transpose_transpose] at h4
  -- inverse facts
  have e1 : A'⁻¹ * A' = 1 := Matrix.nonsing_inv_mul _ hu
  have e2 : A' * A'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  set T := (A'⁻¹)ᵀ with hT
  have t1 : T * A'ᵀ = 1 := by
    rw [hT, ← transpose_mul, e2, transpose_one]
  have t2 : A'ᵀ * T = 1 := by
    rw [hT, ← transpose_mul, e1, transpose_one]
  have hTC : T * Cᵀ = C * A'⁻¹ := by
    calc T * Cᵀ = T * (Cᵀ * (A' * A'⁻¹)) := by rw [e2, Matrix.mul_one]
      _ = T * (Cᵀ * A') * A'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = T * (A'ᵀ * C) * A'⁻¹ := by rw [h1]
      _ = (T * A'ᵀ) * C * A'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = C * A'⁻¹ := by rw [t1, Matrix.one_mul]
  have hYs : (C * A'⁻¹)ᵀ = C * A'⁻¹ := by
    rw [transpose_mul]; exact hTC
  have hZs : (A'⁻¹ * B')ᵀ = A'⁻¹ * B' := by
    rw [transpose_mul]
    calc B'ᵀ * T = (A'⁻¹ * A') * B'ᵀ * T := by rw [e1, Matrix.one_mul]
      _ = A'⁻¹ * (A' * B'ᵀ) * T := by simp only [Matrix.mul_assoc]
      _ = A'⁻¹ * (B' * A'ᵀ) * T := by rw [h4]
      _ = A'⁻¹ * B' * (A'ᵀ * T) := by simp only [Matrix.mul_assoc]
      _ = A'⁻¹ * B' := by rw [t2, Matrix.mul_one]
  have hD : D = T + T * (Cᵀ * B') := by
    have h3' : A'ᵀ * D = 1 + Cᵀ * B' := by rw [← h3]; abel
    calc D = (T * A'ᵀ) * D := by rw [t1, Matrix.one_mul]
      _ = T * (A'ᵀ * D) := by rw [Matrix.mul_assoc]
      _ = T + T * (Cᵀ * B') := by rw [h3', mul_add, Matrix.mul_one]
  have hfac : (fromBlocks 1 0 (C * A'⁻¹) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R) *
      fromBlocks A' 0 0 T * fromBlocks 1 (A'⁻¹ * B') 0 1 = fromBlocks A' B' C D := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    have hAZ : A' * (A'⁻¹ * B') = B' := by rw [← Matrix.mul_assoc, e2, Matrix.one_mul]
    have hYA : C * A'⁻¹ * A' = C := by rw [Matrix.mul_assoc, e1, Matrix.mul_one]
    have hDD : C * A'⁻¹ * (A' * (A'⁻¹ * B')) + T = D := by
      rw [hAZ, ← hTC, hD, Matrix.mul_assoc]; abel
    simp [hAZ, hYA]
    rw [hAZ] at hDD
    rw [← Matrix.mul_assoc]
    exact hDD
  have hinv : (fromBlocks 1 (-X) 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R) *
      fromBlocks 1 X 0 1 = 1 := by
    rw [fromBlocks_multiply]; simp
  refine ⟨X, C * A'⁻¹, A'⁻¹ * B', A', hXt, hYs, hZs, hu, ?_⟩
  calc M = fromBlocks 1 (-X) 0 1 * (fromBlocks 1 X 0 1 * M) := by
        rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = fromBlocks 1 (-X) 0 1 * (fromBlocks 1 0 (C * A'⁻¹) 1 * fromBlocks A' 0 0 T *
          fromBlocks 1 (A'⁻¹ * B') 0 1) := by rw [hNeq, hfac]
    _ = _ := by simp only [Matrix.mul_assoc]; rfl

/-- Corollary of `symplectic_factor_local` for an element of the symplectic group. -/
theorem symplectic_factor_local' {R : Type*} [CommRing R] [IsLocalRing R] {r : ℕ}
    (M : Matrix.symplecticGroup (Fin r) R) :
    ∃ (X Y Z A : Matrix (Fin r) (Fin r) R), Xᵀ = X ∧ Yᵀ = Y ∧ Zᵀ = Z ∧ IsUnit A.det ∧
      (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R) =
        Matrix.fromBlocks 1 (-X) 0 1 * Matrix.fromBlocks 1 0 Y 1 *
        Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * Matrix.fromBlocks 1 Z 0 1 :=
  symplectic_factor_local M.2

end QuadFormsKB.SiegelWeil.Forms
