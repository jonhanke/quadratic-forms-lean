/-
# Kitaoka 1993, Theorem 7.5.1: `(R_K, tr)` of E-type implies splitting of minimal tensors

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.5, Theorem 7.5.1, p. 242 (printed page).

**Setting.** `Ch7ScalarExtension.lean` gives the trace Gram matrix `traceGram K` of $(R_K, \operatorname{tr}_{K/\mathbb Q})$
in the integral basis (indexed by `Module.Free.ChooseBasisIndex ℤ (𝓞 K)`); `Ch7Theorem751.lean` gives its Gram matrix
`Tg K` in the `Fin`-indexed basis `zb K`. This file transfers the E-type property from the first to the second by a
change of $\mathbb Z$-basis, and transposes the tensor factors.

**Proves**
* `tensorQ_transpose`: $Q_{A \otimes B}(X) = Q_{B \otimes A}(X^{\mathsf T})$;
* `tensorQ_congr_basis`: $Q_{C^{\mathsf T} A C \otimes B}(Y) = Q_{A \otimes B}(CY)$;
* `splitOK_of_traceGram`: if `traceGram K` is of E-type, then `SplitOK K B` for every positive Gram matrix `B`.
-/
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.NumberField.Basic
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem751
import QuadFormsKB.Literature.Kitaoka.Ch7ScalarExtension

open Matrix NumberField

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

section Transfer

/-- **Transposition of the tensor form**: $Q_{A \otimes B}(X) = Q_{B \otimes A}(X^{\mathsf T})$. -/
theorem tensorQ_transpose {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ)
    (X : Matrix ι κ ℤ) : tensorQ A B X = tensorQ B A Xᵀ := by
  unfold tensorQ
  simp only [transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Trace formula: $Q_{A \otimes B}(X) = \operatorname{tr}\bigl(A\,(X B X^{\mathsf T})^{\mathsf T}\bigr)$. -/
theorem tensorQ_eq_trace_tr {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ)
    (X : Matrix ι κ ℤ) :
    tensorQ A B X =
      Matrix.trace (A * (X.map (Int.cast : ℤ → ℚ) * B * (X.map (Int.cast : ℤ → ℚ))ᵀ)ᵀ) := by
  unfold tensorQ
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, transpose_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Change of basis in the tensor form**: for an integer matrix $C$,
$Q_{C^{\mathsf T} A C \otimes B}(Y) = Q_{A \otimes B}(C Y)$. -/
theorem tensorQ_congr_basis {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] (A : Matrix ι ι ℚ)
    (B : Matrix κ κ ℚ) (C : Matrix ι ι' ℤ) (Y : Matrix ι' κ ℤ) :
    tensorQ ((C.map (Int.cast : ℤ → ℚ))ᵀ * A * C.map (Int.cast : ℤ → ℚ)) B Y = tensorQ A B (C * Y) := by
  rw [tensorQ_eq_trace_tr, tensorQ_eq_trace_tr]
  have h : (C * Y).map (Int.cast : ℤ → ℚ) = C.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) :=
    (Matrix.map_mul (f := Int.castRingHom ℚ))
  rw [h]
  set C' := C.map (Int.cast : ℤ → ℚ)
  set Y' := Y.map (Int.cast : ℤ → ℚ)
  have e : (C' * Y' * B * (C' * Y')ᵀ)ᵀ = C' * (Y' * B * Y'ᵀ)ᵀ * C'ᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e]
  calc Matrix.trace (C'ᵀ * A * C' * (Y' * B * Y'ᵀ)ᵀ)
      = Matrix.trace (C'ᵀ * (A * C' * (Y' * B * Y'ᵀ)ᵀ)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((A * C' * (Y' * B * Y'ᵀ)ᵀ) * C'ᵀ) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

variable (K : Type) [Field K] [NumberField K]

/-- The change-of-basis matrix from `zb K` to the integral basis: `zb K j = ∑ i, C i j • b i`. -/
def cobC : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (Fin (rk K)) ℤ :=
  (RingOfIntegers.basis K).toMatrix (zb K)

/-- The inverse change-of-basis matrix. -/
def cobD : Matrix (Fin (rk K)) (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ :=
  (zb K).toMatrix (RingOfIntegers.basis K)

theorem cobD_mul_cobC : cobD K * cobC K = 1 := by
  classical
  exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem cobC_mul_cobD : cobC K * cobD K = 1 := by
  classical
  exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

/-- The trace Gram matrix in the two bases: $T_g = C^{\mathsf T}\, T\, C$. -/
theorem Tg_eq_cob : Tg K =
    ((cobC K).map (Int.cast : ℤ → ℚ))ᵀ * traceGram K * (cobC K).map (Int.cast : ℤ → ℚ) := by
  classical
  ext j j'
  have hz : ∀ j, ((zb K j : 𝓞 K) : K) =
      ∑ i, (cobC K i j : ℚ) • integralBasis K i := by
    intro j
    have h := (RingOfIntegers.basis K).sum_toMatrix_smul_self (zb K) j
    have h2 := congrArg (fun x : 𝓞 K => (algebraMap (𝓞 K) K x)) h
    simp only [map_sum] at h2
    rw [show ((zb K j : 𝓞 K) : K) = algebraMap (𝓞 K) K (zb K j) from rfl, ← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integralBasis_apply]
    simp [cobC, Algebra.smul_def]
  simp only [Tg, traceGram, Matrix.of_apply, Matrix.mul_apply, transpose_apply, Matrix.map_apply]
  rw [hz j, hz j', Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, smul_eq_mul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  simp [mul_comm]

/-- **Kitaoka 1993, Theorem 7.5.1 ingredient** (p. 242): if $(R_K, \operatorname{tr})$ is of E-type (in the
integral basis), then for every positive lattice $B$ every minimal vector of $B \otimes (R_K, \operatorname{tr})$ is
split in the basis `zb K`. -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.1, p. 242 ((R_K, B_K) of E-type, change of basis)"]
theorem splitOK_of_traceGram [IsTotallyReal K] (hE : IsEType (traceGram K)) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) (hB : IsPosGram B) : SplitOK K B := by
  classical
  intro X hX
  obtain ⟨hX0, hXmin⟩ := hX
  have hCD := cobC_mul_cobD K
  have hDC := cobD_mul_cobC K
  have hmin : IsMinimalTensor (traceGram K) B (cobC K * Xᵀ) := by
    refine ⟨?_, ?_⟩
    · intro h0
      have : Xᵀ = 0 := by
        have := congrArg (fun M => cobD K * M) h0
        simpa [← Matrix.mul_assoc, hDC] using this
      exact hX0 (by simpa using congrArg Matrix.transpose this)
    · intro Y hY
      have h1 := hXmin (cobD K * Y)ᵀ (by
        intro h0
        apply hY
        have h0' : cobD K * Y = 0 := by simpa using congrArg Matrix.transpose h0
        have := congrArg (fun M => cobC K * M) h0'
        simpa [← Matrix.mul_assoc, hCD] using this)
      rw [tensorQ_transpose B (Tg K) X, tensorQ_transpose B (Tg K) (cobD K * Y)ᵀ] at h1
      simp only [transpose_transpose] at h1
      rw [Tg_eq_cob, tensorQ_congr_basis, tensorQ_congr_basis] at h1
      simpa [← Matrix.mul_assoc, hCD] using h1
  obtain ⟨x, y, hxy⟩ := hE n B hB _ hmin
  refine ⟨y, cobD K *ᵥ x, ?_⟩
  have : Xᵀ = vecMulVec (cobD K *ᵥ x) y := by
    have := congrArg (fun M => cobD K * M) hxy
    simpa [← Matrix.mul_assoc, hDC, Matrix.mul_vecMulVec] using this
  have := congrArg Matrix.transpose this
  simpa using this

end Transfer

end QuadFormsKB.Kitaoka.EType
