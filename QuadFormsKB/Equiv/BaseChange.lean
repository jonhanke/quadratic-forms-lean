/-
# `RatQF` (polynomial model) versus Mathlib's quadratic forms and base change
-/
import QuadFormsKB.Defs.Rational
import QuadFormsKB.Equiv.Mathlib

open Matrix

namespace QuadFormsKB.RatQF

variable {n : ℕ}

/-- Isotropy over ℚ in the polynomial model agrees with Mathlib's `Anisotropic`. -/
@[kb "serre1973" "Ch. IV, §1.6"]
theorem isotropicIn_rat_iff (Q : RatQF n) :
    Q.IsotropicIn ℚ ↔ ¬ (QuadForm.toQuadraticForm Q).Anisotropic := by
  unfold QuadraticMap.Anisotropic
  simp only [QuadFormsKB.QuadForm.toQuadraticForm_apply, QuadFormsKB.QuadForm.eval, QuadFormsKB.QuadForm.IsotropicIn]
  constructor
  · rintro ⟨x, hx, h⟩ H
    exact hx (H x h)
  · intro H
    by_contra h'
    apply H
    intro x hx
    by_contra hne
    exact h' ⟨x, hne, hx⟩

/-- Isotropy over `K` in the polynomial model agrees with Mathlib's base change
`QuadraticForm.baseChange K` (on `K ⊗[ℚ] ℚⁿ`). -/
@[kb "serre1973" "Ch. IV, §1.6"]
theorem isotropicIn_iff_baseChange (K : Type) [Field K] [CharZero K] (Q : RatQF n) :
    Q.IsotropicIn K ↔ ¬ ((QuadForm.toQuadraticForm Q).baseChange K).Anisotropic := by
  have key : ∀ x : Fin n → K, ((QuadForm.toQuadraticForm Q).baseChange K) ((TensorProduct.piScalarRight ℚ K K (Fin n)).symm x)
        = QuadForm.evalIn K Q x := by
    intro x
    have hx : (TensorProduct.piScalarRight ℚ K K (Fin n)).symm x = ∑ i, x i ⊗ₜ[ℚ] (Pi.single i (1:ℚ) : Fin n → ℚ) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      simp [TensorProduct.piScalarRight_symm_single]
    rw [hx, ← QuadraticMap.associated_eq_self_apply K]
    erw [QuadraticForm.associated_baseChange]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.BilinForm.baseChange_tmul]
    have h2 : ∀ i j, QuadraticMap.associated (QuadForm.toQuadraticForm Q) (Pi.single i 1) (Pi.single j 1) = ⅟2 * (Q.coeff i j + Q.coeff j i) := by
      intro i j
      rw [QuadForm.toQuadraticForm, QuadraticMap.associated, QuadraticMap.associated_toQuadraticMap]
      simp [Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, Pi.single_apply]
      ring
    simp only [h2, QuadForm.evalIn]
    have hu : ∀ i j, j < i → Q.coeff i j = 0 := fun i j h => Q.upper h
    have e1 : ∀ i j, (if i ≤ j then algebraMap ℚ K (Q.coeff i j) * x i * x j else 0) = algebraMap ℚ K (Q.coeff i j) * x i * x j := by
      intro i j
      split_ifs with h
      · rfl
      · rw [hu i j (not_le.mp h)]; simp
    simp only [e1, Algebra.smul_def, map_mul, map_add, invOf_eq_inv, map_inv₀, map_ofNat, mul_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => (2:K)⁻¹ * algebraMap ℚ K (Q.coeff b a) * (x b * x a))]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  constructor
  · rintro ⟨x, hx0, hx⟩ hA
    apply hx0
    have := hA _ ((key x).trans hx)
    simpa using this
  · intro hA
    unfold QuadraticMap.Anisotropic at hA
    push_neg at hA
    obtain ⟨y, hy, hy0⟩ := hA
    refine ⟨TensorProduct.piScalarRight ℚ K K (Fin n) y, ?_, ?_⟩
    · exact (LinearEquiv.map_ne_zero_iff _).mpr hy0
    · rw [← key, LinearEquiv.symm_apply_apply]; exact hy

end QuadFormsKB.RatQF
