/-
# Cassels, Chapter 9, §7: Cayley's formula (Siegel's alternative approach to Theorem 7.1)

**Layer:** square matrices over a field $K$ with $2 \ne 0$; $F$ the (symmetric) matrix of a form, $T$ a matrix with
$\det(I + T) \ne 0$ (7.5).

**Proves** (9.r13, Cassels p. 156) Cayley's parametrization of automorphs: with $L = (I - T)(I + T)^{-1}$ (7.6),
$T = (I + L)^{-1}(I - L)$ (7.7), and $T$ is an automorph, $T^{\mathsf T}FT = F$ (7.4), iff
$L^{\mathsf T}F + FL = 0$ (7.8) — *a collection of linear conditions on the coefficients of $L$* (`cayley_automorph_iff`,
`cayley_inverse`). The formulas (7.6)–(7.8) are garbled in the scan and are reconstructed (the classical Cayley
transform; Cassels' $T'$ is the transpose $T^{\mathsf T}$).
-/
import QuadFormsKB.Defs.QuadForm

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {K : Type*} [Field K] {n : ℕ}

/-- **Cayley's formula, (7.4) ⟺ (7.8)** (Cassels, Ch. 9, §7, p. 156): if $\det(I + T) \ne 0$ and
$L = (I - T)(I + T)^{-1}$, then $T^{\mathsf T}FT = F$ iff $L^{\mathsf T}F + FL = 0$ (for any $F$; Cassels' $F$ is the
symmetric matrix of the form). Needs $2 \ne 0$ in $K$. -/
@[kb "cassels1978" "Ch. 9, §7, (7.4)–(7.8), p. 156 (Cayley's formula; formulas reconstructed)"]
theorem cayley_automorph_iff (h2 : (2 : K) ≠ 0) (F T : Matrix (Fin n) (Fin n) K) (hT : IsUnit (1 + T).det) :
    Tᵀ * F * T = F ↔ ((1 - T) * (1 + T)⁻¹)ᵀ * F + F * ((1 - T) * (1 + T)⁻¹) = 0 := by
  set A := 1 + T
  set B := 1 - T
  have hA : A⁻¹ * A = 1 := nonsing_inv_mul A hT
  have hA' : A * A⁻¹ = 1 := mul_nonsing_inv A hT
  have hAt : IsUnit Aᵀ.det := by rwa [det_transpose]
  have hAt' : (A⁻¹)ᵀ * Aᵀ = 1 := by rw [← transpose_mul, hA', transpose_one]
  have hAt'' : Aᵀ * (A⁻¹)ᵀ = 1 := by rw [← transpose_mul, hA, transpose_one]
  -- `Lᵀ F + F L = A⁻ᵀ (Bᵀ F A + Aᵀ F B) A⁻¹` and `Bᵀ F A + Aᵀ F B = 2 (F - Tᵀ F T)`
  have key : (B * A⁻¹)ᵀ * F + F * (B * A⁻¹) = (A⁻¹)ᵀ * ((2 : K) • (F - Tᵀ * F * T)) * A⁻¹ := by
    have e : (2 : K) • (F - Tᵀ * F * T) = Bᵀ * F * A + Aᵀ * F * B := by
      simp only [A, B, transpose_add, transpose_sub, transpose_one, add_mul, sub_mul, mul_add, mul_sub, one_mul,
        mul_one, two_smul]
      abel
    rw [e, transpose_mul]
    simp only [mul_add, add_mul, Matrix.mul_assoc]
    rw [hA', ← Matrix.mul_assoc (A⁻¹)ᵀ Aᵀ, hAt', Matrix.one_mul, Matrix.mul_one]
  rw [key]
  constructor
  · intro h; rw [h, sub_self, smul_zero, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    have h' : (2 : K) • (F - Tᵀ * F * T) = 0 := by
      have := congrArg (fun X => Aᵀ * X * A) h
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc] at this
      rw [hA, Matrix.mul_one, ← Matrix.mul_assoc, hAt'', Matrix.one_mul] at this
      simpa [Matrix.mul_assoc] using this
    have h'' : F - Tᵀ * F * T = 0 := by
      have := congrArg (fun X => (2 : K)⁻¹ • X) h'
      simpa [smul_smul, inv_mul_cancel₀ h2] using this
    exact (sub_eq_zero.mp h'').symm

/-- **Cayley's formula, (7.7)** (Cassels, Ch. 9, §7, p. 156): with $L = (I - T)(I + T)^{-1}$ one has
$\det(I + L) \ne 0$ and $T = (I + L)^{-1}(I - L)$. -/
@[kb "cassels1978" "Ch. 9, §7, (7.6)–(7.7), p. 156 (Cayley's formula; formulas reconstructed)"]
theorem cayley_inverse (h2 : (2 : K) ≠ 0) (T : Matrix (Fin n) (Fin n) K) (hT : IsUnit (1 + T).det) :
    IsUnit (1 + (1 - T) * (1 + T)⁻¹).det ∧
      T = (1 + (1 - T) * (1 + T)⁻¹)⁻¹ * (1 - (1 - T) * (1 + T)⁻¹) := by
  set A := 1 + T
  have hA' : A * A⁻¹ = 1 := mul_nonsing_inv A hT
  have hA : A⁻¹ * A = 1 := nonsing_inv_mul A hT
  have e1 : 1 + (1 - T) * A⁻¹ = (2 : K) • A⁻¹ := by
    have h : (2 : K) • A⁻¹ = (A + (1 - T)) * A⁻¹ := by
      rw [show A + (1 - T) = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) by simp only [A]; rw [two_smul]; abel,
        smul_mul_assoc, Matrix.one_mul]
    rw [h, add_mul, hA']
  have e2 : 1 - (1 - T) * A⁻¹ = (2 : K) • (T * A⁻¹) := by
    have h : (2 : K) • (T * A⁻¹) = (A - (1 - T)) * A⁻¹ := by
      rw [show A - (1 - T) = (2 : K) • T by simp only [A]; rw [two_smul]; abel, smul_mul_assoc]
    rw [h, sub_mul (A) (1 - T) A⁻¹, hA']
  have hinv : ((2 : K) • A⁻¹) * ((2 : K)⁻¹ • A) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ h2, one_smul, hA]
  have hM : ((2 : K) • A⁻¹)⁻¹ = (2 : K)⁻¹ • A := inv_eq_right_inv hinv
  have hcomm : A * T = T * A := by simp only [A, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · rw [e1]
    have h := congrArg Matrix.det hinv
    rw [det_mul, det_one] at h
    exact IsUnit.of_mul_eq_one _ h
  · rw [e1, e2, hM, smul_mul_smul_comm, inv_mul_cancel₀ h2, one_smul, ← Matrix.mul_assoc, hcomm,
      Matrix.mul_assoc, hA', Matrix.mul_one]

end QuadFormsKB.Siegel
