/-
# The Siegel upper half space and simultaneous diagonalization

**Layer:** linear algebra over $\mathbb R$ and $\mathbb C$.

* `siegelH`: $\mathbb H_g = \{Z \in M_g(\mathbb C) : Z^{\mathsf T} = Z,\ \operatorname{Im}Z\ \text{positive definite}\}$.
* `exists_eq_transpose_mul`: a real positive definite $S$ is $C^{\mathsf T}C$ with $C$ invertible.
* `exists_siegel_diag`: every $Z \in \mathbb H_g$ is $P(\Lambda + iI)P^{\mathsf T}$ with $P$ real invertible and
  $\Lambda$ real diagonal (write $\operatorname{Im}Z = RR^{\mathsf T}$ and diagonalize the real symmetric
  $R^{-1}(\operatorname{Re}Z)R^{-\mathsf T}$ by an orthogonal matrix).
* `neg_inv_mem_siegelH`: $Z \mapsto -Z^{-1}$ preserves $\mathbb H_g$.

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I §1 [unverified]; Klingen, *Introductory lectures on
Siegel modular forms* (1990), §I.1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix Complex

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

variable {N g : ℕ}

/-- **The Siegel upper half space** $\mathbb H_g = \{Z \in M_g(\mathbb C) : Z^{\mathsf T} = Z,\ \operatorname{Im}Z\ \text{positive definite}\}$. -/
@[kb "freitag1983" "Ch. I, §1 (the Siegel half space $\\mathbb H_n$) [unverified]"]
def siegelH (g : ℕ) : Set (Matrix (Fin g) (Fin g) ℂ) := {Z | Zᵀ = Z ∧ (Z.map Complex.im).PosDef}

/-- The real matrix $S$ as a complex matrix. -/
abbrev cR {m n : Type*} (S : Matrix m n ℝ) : Matrix m n ℂ := S.map (↑)

/-- The integer matrix $X$ as a complex matrix. -/
abbrev cZ {m n : Type*} (X : Matrix m n ℤ) : Matrix m n ℂ := X.map (↑)

open scoped MatrixOrder in
/-- A real positive definite $S$ is $C^{\mathsf T}C$ with $C$ invertible. -/
lemma exists_eq_transpose_mul {S : Matrix (Fin N) (Fin N) ℝ} (hS : S.PosDef) :
    ∃ C : Matrix (Fin N) (Fin N) ℝ, S = Cᵀ * C ∧ C.det ≠ 0 := by
  have h0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef
  have hA : (CFC.sqrt S).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hsq : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S h0
  have hT : (CFC.sqrt S)ᵀ = CFC.sqrt S := hA.isHermitian.eq
  refine ⟨CFC.sqrt S, by rw [hT, hsq], ?_⟩
  intro hd
  have := hS.det_pos
  rw [← hsq, det_mul, hd] at this
  simp at this

/-- Complex congruence of a real diagonal-plus-`i` matrix by a real matrix, split into real and imaginary parts. -/
lemma cR_congr_diag {g : ℕ} (P : Matrix (Fin g) (Fin g) ℝ) (d : Fin g → ℝ) (e : Fin g → ℝ) :
    cR P * diagonal (fun k => (d k : ℂ) + (e k : ℂ) * I) * (cR P)ᵀ =
      cR (P * diagonal d * Pᵀ) + I • cR (P * diagonal e * Pᵀ) := by
  have h1 : (diagonal (fun k => (d k : ℂ) + (e k : ℂ) * I) : Matrix (Fin g) (Fin g) ℂ) =
      cR (diagonal d) + I • cR (diagonal e) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · simp [hij]
  rw [h1]
  have h2 : ∀ M : Matrix (Fin g) (Fin g) ℝ, cR (P * M * Pᵀ) = cR P * cR M * (cR P)ᵀ := by
    intro M
    have hm : ∀ A B : Matrix (Fin g) (Fin g) ℝ, cR (A * B) = cR A * cR B :=
      fun A B => Complex.ofRealHom.mapMatrix.map_mul A B
    rw [hm, hm]
    rfl
  rw [h2, h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Imaginary part of the splitting in `cR_congr_diag`. -/
lemma cR_congr_im {g : ℕ} (P : Matrix (Fin g) (Fin g) ℝ) (d : Fin g → ℝ) (e : Fin g → ℝ) :
    (cR (P * diagonal d * Pᵀ) + I • cR (P * diagonal e * Pᵀ)).map Complex.im =
      P * diagonal e * Pᵀ := by
  ext i j
  simp

/-- Core of `exists_siegel_diag`: from a factorization $\operatorname{Im}Z = C^{\mathsf T}C$. -/
lemma exists_diag_aux {g : ℕ} {Z : Matrix (Fin g) (Fin g) ℂ}
    (hS : Zᵀ = Z) (C : Matrix (Fin g) (Fin g) ℝ)
    (hC : Z.map Complex.im = Cᵀ * C) (hd : C.det ≠ 0) :
    ∃ (P : Matrix (Fin g) (Fin g) ℝ) (lam : Fin g → ℝ), P.det ≠ 0 ∧
      Z = cR P * diagonal (fun k => (lam k : ℂ) + I) * (cR P)ᵀ := by
  set R : Matrix (Fin g) (Fin g) ℝ := Cᵀ with hR
  have hRd : R.det ≠ 0 := by simpa [hR] using hd
  have hY : Z.map Complex.im = R * Rᵀ := by rw [hC]; simp [hR]
  set X : Matrix (Fin g) (Fin g) ℝ := Z.map Complex.re with hX
  have hXs : Xᵀ = X := by
    ext i j
    have h : Z i j = Z j i := congrFun (congrFun hS j) i
    simp only [hX, transpose_apply, Matrix.map_apply]
    rw [h]
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hRd
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  set T : Matrix (Fin g) (Fin g) ℝ := R⁻¹ * X * (R⁻¹)ᵀ with hTdef
  have hT : T.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hTdef]
    simp [Matrix.transpose_mul, hXs, Matrix.mul_assoc]
  have hs := hT.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix (Fin g) (Fin g) ℝ := (hT.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) with hU
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hT.eigenvectorUnitary
    simpa [hU, Matrix.star_eq_conjTranspose] using this
  have hTU : T = U * diagonal hT.eigenvalues * Uᵀ := by
    exact hs.trans (by simp [hU, Matrix.star_eq_conjTranspose])
  have hUd : U.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hUU
    rw [det_mul, h] at this
    simp at this
  refine ⟨R * U, hT.eigenvalues, ?_, ?_⟩
  · rw [det_mul]; exact mul_ne_zero hRd hUd
  · have hXe : (R * U) * diagonal hT.eigenvalues * (R * U)ᵀ = X := by
      have : (R * U) * diagonal hT.eigenvalues * (R * U)ᵀ = R * T * Rᵀ := by
        calc (R * U) * diagonal hT.eigenvalues * (R * U)ᵀ
            = R * (U * diagonal hT.eigenvalues * Uᵀ) * Rᵀ := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc]
          _ = R * T * Rᵀ := by rw [← hTU]
      rw [this, hTdef]
      have h2 : (R⁻¹)ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRR]; simp
      calc R * (R⁻¹ * X * (R⁻¹)ᵀ) * Rᵀ = (R * R⁻¹) * X * ((R⁻¹)ᵀ * Rᵀ) := by
            simp only [Matrix.mul_assoc]
        _ = X := by rw [hRR, h2]; simp
    have hYe : (R * U) * (1 : Matrix (Fin g) (Fin g) ℝ) * (R * U)ᵀ = Z.map Complex.im := by
      rw [hY]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U, hUU]; simp
    have key := cR_congr_diag (R * U) hT.eigenvalues (fun _ => 1)
    simp only [ofReal_one, one_mul] at key
    rw [key]
    have e1 : (diagonal (fun _ : Fin g => (1:ℝ))) = 1 := by ext i j; simp [diagonal_apply, one_apply]
    rw [e1, hXe, hYe]
    ext i j
    apply Complex.ext <;> simp [hX]

/-- **Simultaneous diagonalization** of $Z \in \mathbb H_g$: $Z = P(\Lambda + iI)P^{\mathsf T}$ with $P$ real invertible
and $\Lambda = \operatorname{diag}(\lambda_0, \dots, \lambda_{g-1})$ real. -/
lemma exists_siegel_diag {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelH g) :
    ∃ (P : Matrix (Fin g) (Fin g) ℝ) (lam : Fin g → ℝ), P.det ≠ 0 ∧
      Z = cR P * diagonal (fun k => (lam k : ℂ) + I) * (cR P)ᵀ := by
  obtain ⟨C, hC, hd⟩ := exists_eq_transpose_mul hZ.2
  exact exists_diag_aux hZ.1 C hC hd

/-- $-Z^{-1} \in \mathbb H_g$ for $Z \in \mathbb H_g$. -/
lemma neg_inv_mem_siegelH {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelH g) : -Z⁻¹ ∈ siegelH g := by
  obtain ⟨P, lam, hP, hZe⟩ := exists_siegel_diag hZ
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  set P' : Matrix (Fin g) (Fin g) ℝ := (P⁻¹)ᵀ with hP'
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hPP2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have hP'd : P'.det ≠ 0 := by
    have := congrArg Matrix.det hPP2
    rw [hP', det_transpose]
    intro h
    rw [det_mul, h] at this
    simp at this
  have hl : ∀ k, (lam k : ℝ) ^ 2 + 1 ≠ 0 := fun k => by positivity
  set d : Fin g → ℝ := fun k => -lam k / (lam k ^ 2 + 1) with hd
  set e : Fin g → ℝ := fun k => 1 / (lam k ^ 2 + 1) with he
  set W : Matrix (Fin g) (Fin g) ℂ :=
    cR P' * diagonal (fun k => (d k : ℂ) + (e k : ℂ) * I) * (cR P')ᵀ with hW
  have hm : ∀ A B : Matrix (Fin g) (Fin g) ℝ, cR (A * B) = cR A * cR B :=
    fun A B => Complex.ofRealHom.mapMatrix.map_mul A B
  have hc1 : (cR P)ᵀ * cR P' = 1 := by
    have : cR (Pᵀ * P') = 1 := by rw [hP', ← Matrix.transpose_mul, hPP2]; simp [cR]
    rw [hm] at this
    exact this
  have hc2 : cR P * (cR P')ᵀ = 1 := by
    have : cR (P * P'ᵀ) = 1 := by rw [hP', transpose_transpose, hPP]; simp [cR]
    rw [hm] at this
    exact this
  have hDF : diagonal (fun k => (lam k : ℂ) + I) * diagonal (fun k => (d k : ℂ) + (e k : ℂ) * I)
      = (-1 : Matrix (Fin g) (Fin g) ℂ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      have : ((lam i : ℂ) ^ 2 + 1) ≠ 0 := by exact_mod_cast hl i
      simp only [diagonal_apply_eq, hd, he]
      push_cast
      field_simp
      rw [Matrix.neg_apply, Matrix.one_apply_eq]
      linear_combination Complex.I_sq
    · simp [hij]
  have hZW : Z * (-W) = 1 := by
    rw [hZe, hW]
    calc _ = - (cR P * diagonal (fun k => (lam k : ℂ) + I) * ((cR P)ᵀ * cR P') *
          diagonal (fun k => (d k : ℂ) + (e k : ℂ) * I) * (cR P')ᵀ) := by
            simp only [Matrix.mul_neg, Matrix.mul_assoc]
      _ = 1 := by
            rw [hc1, Matrix.mul_one, Matrix.mul_assoc (cR P), hDF]
            simp [hc2]
  have hinv : Z⁻¹ = -W := Matrix.inv_eq_right_inv hZW
  rw [hinv, neg_neg]
  have key : W = cR (P' * diagonal d * P'ᵀ) + I • cR (P' * diagonal e * P'ᵀ) := cR_congr_diag P' d e
  refine ⟨?_, ?_⟩
  · rw [hW]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · rw [key, cR_congr_im]
    have hpd : (diagonal e : Matrix (Fin g) (Fin g) ℝ).PosDef := by
      rw [posDef_diagonal_iff]
      intro k
      simp only [he]; positivity
    have hinj : Function.Injective (P'ᵀ).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, det_transpose]
      exact isUnit_iff_ne_zero.mpr hP'd
    simpa using hpd.conjTranspose_mul_mul_same (B := P'ᵀ) hinj

end QuadFormsKB.WeilRep.Genus
