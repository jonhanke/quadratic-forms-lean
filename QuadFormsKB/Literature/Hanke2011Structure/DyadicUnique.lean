/-
# Hanke 2011, Thm. 2.6 (dyadic case): bridging Hessian-matrix congruence to isometry of forms

For a quadratic form $Q$ in $n$ variables over a domain $R$ with $2 \ne 0$, an isometry
$Q'(x) = Q(Ux)$ is the same as the congruence $H' = U^{\mathsf T} H U$ of Hessian matrices
(`two_mul_eval`: $2Q(x) = x^{\mathsf T}Hx$). So `Cong Q.hessian Q'.hessian` gives `Siegel.IsometricGL Q Q'`.
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicClassify
import QuadFormsKB.Literature.Hanke2011Structure.LocalGenera

open Matrix IsLocalRing

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure.Dyadic

section Bridge

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}

/-- $2Q(x) = x^{\mathsf T}Hx$ for the Hessian matrix $H = C + C^{\mathsf T}$. -/
theorem two_mul_eval (Q : QuadForm R n) (x : Fin n → R) :
    2 * Q.eval x = x ⬝ᵥ (Q.hessian *ᵥ x) := by
  have h1 := QuadForm.evalIn_eq_dotProduct R Q x
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
  have h2 : x ⬝ᵥ (Q.coeffᵀ *ᵥ x) = x ⬝ᵥ (Q.coeff *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  show 2 * Q.evalIn R x = _
  rw [h1, QuadForm.hessian, Matrix.add_mulVec, dotProduct_add, h2]; ring

/-- The Hessian matrix of a form is a Hessian matrix. -/
theorem isHess_hessian (Q : QuadForm R n) : IsHess Q.hessian := ⟨Q.coeff, rfl⟩

/-- A congruence of Hessian matrices is an isometry of the forms (for a domain with $2 \ne 0$). -/
theorem isometricGL_of_cong (h20 : (2 : R) ≠ 0) {Q Q' : QuadForm R n}
    (h : Cong Q.hessian Q'.hessian) : QuadFormsKB.Siegel.IsometricGL Q Q' := by
  obtain ⟨U, U', h1, h2, h3⟩ := h
  refine ⟨⟨U, U', h1, h2⟩, fun x => ?_⟩
  apply mul_left_cancel₀ h20
  show 2 * Q.eval (U *ᵥ x) = 2 * Q'.eval x
  rw [two_mul_eval Q (U *ᵥ x), two_mul_eval Q' x, h3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x Uᵀ, Matrix.vecMul_transpose]

end Bridge

section Even

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {n : ℕ}

/-- **Thm. 2.6, dyadic case, $n$ even** (= Sublemma 2.7: Hanke 2011, pp. 8--9), unconditional. -/
@[kb "hanke2011structure" "Sublemma 2.7 and Thm. 2.6, pp. 8-9 (dyadic, n even)"]
theorem uniqueNormalizedLocalGenus_even (h2 : ¬ IsUnit (2 : R)) (h20 : (2 : R) ≠ 0) (hn : Even n)
    (Q Q' : QuadForm R n) (hQ : IsPrimitiveForm Q) (hN : IsNormalizedHessian R Q) (u : R) (hu : IsUnit u)
    (hdet : Q'.hessian.det = u ^ 2 * Q.hessian.det) : QuadFormsKB.Siegel.IsometricGL Q Q' := by
  have h2m : (2 : R) ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h2
  obtain ⟨r, hr⟩ := hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have he : (Set.range fun p : Fin 0 × Fin 0 => Q.coeff p.1 p.2) = ∅ := Set.range_eq_empty _
    rw [IsPrimitiveForm, he, Ideal.span_empty] at hQ
    exact bot_ne_top hQ
  have hunit : IsUnit Q.hessian.det := by
    have hev : Even n := ⟨r, hr⟩
    simp only [IsNormalizedHessian, hev, ite_true] at hN
    exact IsDiscreteValuationRing.addVal_eq_zero_iff.1 hN
  have hunit' : IsUnit Q'.hessian.det := by rw [hdet]; exact (hu.pow 2).mul hunit
  exact isometricGL_of_cong h20 (even_cong h2m h20 r (by omega) n (by omega) Q.hessian Q'.hessian
    (isHess_hessian Q) (isHess_hessian Q') hunit hunit' u hu hdet)

end Even

end QuadFormsKB.Hanke2011Structure.Dyadic
