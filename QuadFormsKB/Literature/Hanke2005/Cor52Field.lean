import Mathlib

/-!
# The cubic field of the counterexample to Hanke's Corollary 5.2(ii)

$k = \mathbb Q(\alpha)$ with $\alpha^3-\alpha^2-10\alpha-7=0$ (discriminant $1489$), realised as `AdjoinRoot` of
the polynomial `poly` over $\mathbb Q$. This file: irreducibility, so `K` is a number field.
-/

open Polynomial

noncomputable section

namespace QuadFormsKB.Hanke2005.Cor52

/-- The minimal polynomial $y^3-y^2-10y-7$ of $\alpha$ over $\mathbb Z$. -/
def polyZ : ℤ[X] := X ^ 3 - X ^ 2 - C 10 * X - C 7

/-- The same polynomial over $\mathbb Q$. -/
def poly : ℚ[X] := X ^ 3 - X ^ 2 - C 10 * X - C 7

theorem poly_eq_map : poly = polyZ.map (Int.castRingHom ℚ) := by
  simp [poly, polyZ]
  rw [show (C 10 : ℚ[X]) = 10 from rfl, show (C 7 : ℚ[X]) = 7 from rfl]

theorem polyZ_monic : polyZ.Monic := by
  unfold polyZ; monicity!

theorem polyZ_natDegree : polyZ.natDegree = 3 := by
  unfold polyZ; compute_degree!

theorem polyZ_irreducible : Irreducible polyZ := by
  have hm : (polyZ.map (Int.castRingHom (ZMod 2))).Monic := polyZ_monic.map _
  have hd : (polyZ.map (Int.castRingHom (ZMod 2))).natDegree = 3 := by
    rw [polyZ_monic.natDegree_map, polyZ_natDegree]
  refine Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) polyZ polyZ_monic ?_
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  rw [mem_roots hm.ne_zero, IsRoot] at ha
  simp only [polyZ, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, map_C,
    eval_sub, eval_pow, eval_X, eval_mul, eval_C] at ha
  revert ha
  fin_cases a <;> decide

theorem poly_irreducible : Irreducible poly := by
  rw [poly_eq_map]
  exact (polyZ_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp polyZ_irreducible

instance : Fact (Irreducible poly) := ⟨poly_irreducible⟩

/-- **The field** $k=\mathbb Q(\alpha)$. -/
abbrev K : Type := AdjoinRoot poly

/-- The root $\alpha$. -/
def α : K := AdjoinRoot.root poly

theorem poly_monic : poly.Monic := by
  unfold poly; monicity!

theorem poly_natDegree : poly.natDegree = 3 := by
  unfold poly; compute_degree!

instance : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := (AdjoinRoot.powerBasis poly_irreducible.ne_zero).finite

/-- $\alpha^3=\alpha^2+10\alpha+7$. -/
theorem α_cube : α ^ 3 = α ^ 2 + 10 * α + 7 := by
  have e : (poly : ℚ[X]) = X ^ 3 - X ^ 2 - 10 * X - 7 := by
    simp [poly]; rw [show (C 10 : ℚ[X]) = 10 from rfl, show (C 7 : ℚ[X]) = 7 from rfl]
  have h : eval₂ (AdjoinRoot.of poly) (AdjoinRoot.root poly) (X ^ 3 - X ^ 2 - 10 * X - 7 : ℚ[X]) = 0 := by
    rw [← e]; exact AdjoinRoot.eval₂_root poly
  simp at h
  unfold α
  linear_combination h

/-- The unit $s=\alpha+2$. -/
def s : K := α + 2

/-- $d=-(\alpha+2)$. -/
def d : K := -(α + 2)

end QuadFormsKB.Hanke2005.Cor52
