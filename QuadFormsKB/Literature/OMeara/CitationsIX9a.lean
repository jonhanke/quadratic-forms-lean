/-
# O'Meara §92–§93: citation tags for proof steps and running text

Tags for declarations, proved in earlier files, that state items that had no citation tag yet (proof steps or items
used without being cited), and one statement of running text,
93.r12: over a dyadic field, $2(\mathfrak sL) \subsetneq \mathfrak sL$ (`two_smul_scale_lt_scale`).
-/
import QuadFormsKB.Literature.OMeara.Sec93E

open Submodule IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

attribute [kb "omeara1963" "§93C, proof of 93:14, step 2, p. 257 (the case x = x' follows from 93:12)"]
  QuadFormsKB.OMeara.isometricLat_of_common_hyperbolic
attribute [kb "omeara1963" "§93C, proof of 93:14, step 3, p. 257 (B(x, y') a unit)"]
  QuadFormsKB.OMeara.isometricLat_of_unit_hyperbolic
attribute [kb "omeara1963" "§92, p. 246 (L = ox₁ ⊥ ⋯ ⊥ oxₙ by splitting off Q(x)o = nL = sL)"]
  QuadFormsKB.OMeara.exists_orth_family
attribute [kb "omeara1963" "§93, p. 250 (the residue field is perfect: ε' ≡ εδ² mod π)"]
  QuadFormsKB.OMeara.exists_sq_mod
attribute [kb "omeara1963" "§93, p. 251 (Δ = 1 + 4ρ, a unit of quadratic defect 4o)"]
  QuadFormsKB.OMeara.G93.exists_delta

section Strict

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]

/-- **$2(\mathfrak sL) \subsetneq \mathfrak sL$ over a dyadic field** (O'Meara 1963, §93, p. 251: "But we now have
$2(\mathfrak sL) \subset \mathfrak sL$, and it is this strict inclusion that makes the dyadic theory of quadratic
forms distinctly different from the non-dyadic theory"). Stated for any non-zero fractional ideal $\mathfrak s$
(here $\mathfrak s = R\sigma$, $\sigma \ne 0$), with $2$ not a unit of $R$. -/
@[kb "omeara1963" "§93, p. 251 (2(sL) ⊂ sL in the dyadic case)"]
theorem two_smul_scale_lt_scale (h2p : ¬ IsUnit (2 : R)) {σ : F} (hσ : σ ≠ 0) :
    (2 : F) • (R ∙ σ : Submodule R F) < R ∙ σ := by
  have key : ∀ r : R, (2 : F) • (r • σ) = ((2 : R) * r) • σ := fun r => by
    simp only [Algebra.smul_def, map_mul, map_ofNat]; ring
  refine lt_of_le_of_ne ?_ fun h => ?_
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hz
    rw [key]
    exact smul_mem _ _ (mem_span_singleton_self σ)
  · have hmem : σ ∈ (2 : F) • (R ∙ σ : Submodule R F) := by rw [h]; exact mem_span_singleton_self σ
    obtain ⟨z, hz, hzσ⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hmem
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hz
    rw [key, Algebra.smul_def] at hzσ
    have : algebraMap R F (2 * r) * σ = algebraMap R F 1 * σ := by rw [hzσ, map_one, one_mul]
    have h1 : (2 : R) * r = 1 := IsFractionRing.injective R F (mul_right_cancel₀ hσ this)
    exact h2p (isUnit_iff_exists_inv.mpr ⟨r, h1⟩)

end Strict

end QuadFormsKB.OMeara
