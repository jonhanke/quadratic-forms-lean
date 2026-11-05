/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicFamily
import QuadFormsKB.Literature.Hanke2011Structure.SquareclassSeries

/-!
# Paper 6, Corollary 5.5 at $\mathfrak p \nmid 2$ for a distinguished family $\lambda$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Cor. 5.5, p. 24, with Def. 4.9 (distinguished families, p. 18).

For a distinguished family $\lambda$ (`DistinguishedFamily`: a homomorphism from the nonzero ideals to the adelic
squareclasses with $I(\lambda(\mathfrak a)) = \mathfrak a$) and a finite prime $\mathfrak p$, the component
$\lambda(\mathfrak p)_{\mathfrak p}$ has valuation $1$, so it is $[\pi u]$ for a unit $u$ (`exists_unit_comp_eq`), and
$\lambda(\mathfrak p^i)_{\mathfrak p} = [\pi u]^i$.  Hence the Euler factors
$$\sum_{i\ge0}A^*_{\mathfrak p;n}(\lambda(\mathfrak p^i))\,X^i,\qquad \sum_{i\ge0}B^*_{\mathfrak p;n}(\lambda(\mathfrak p^i))\,X^i
\qquad (X = q^{-s} = N_{F/\mathbb Q}(\mathfrak p)^{-s})$$
are rational functions of $X$ for $\mathfrak p \nmid 2$, every rank $n$, every number field (`cor_5_5_nd_A_family`,
`cor_5_5_nd_B_family`; from `cor_5_5_nd_A_unif`).  Unconditional.

Indices are 0-based.
-/

open Finset Matrix IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.RatND

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure
  QuadFormsKB.Hanke2011Structure.RatOdd QuadFormsKB.ConwaySloane QuadFormsKB.Odd7 QuadFormsKB.Siegel

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-- The prime $\mathfrak p$ of `v` as a nonzero ideal. -/
def primeNZ (v : HeightOneSpectrum (𝓞 F)) : (Ideal (𝓞 F))⁰ :=
  ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

variable {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem idealOrd_self : idealOrd v v.asIdeal = 1 := by
  unfold idealOrd
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible v.irreducible, normalize_eq,
    Multiset.count_singleton_self]
  rfl

theorem sqNF_mul {x y : 𝔬} (hx : x ≠ 0) (hy : y ≠ 0) : (sqNF (x * y) : LocalSqCl v) = sqNF x * sqNF y := by
  rw [sqNF_of_ne hx, sqNF_of_ne hy, sqNF_of_ne (mul_ne_zero hx hy), ← map_mul]
  congr 1
  apply Units.ext
  simp

theorem sqNF_one : (sqNF (1 : 𝔬) : LocalSqCl v) = 1 := by
  rw [sqNF_of_ne (one_ne_zero : (1 : 𝔬) ≠ 0), ← map_one SqCl.mk]
  congr 1
  apply Units.ext
  simp

theorem sqNF_pow {x : 𝔬} (hx : x ≠ 0) (i : ℕ) : (sqNF (x ^ i) : LocalSqCl v) = sqNF x ^ i := by
  induction i with
  | zero => rw [pow_zero, pow_zero, sqNF_one]
  | succ k ih => rw [pow_succ, sqNF_mul (pow_ne_zero _ hx) hx, ih, pow_succ]

theorem ordZ_sqNF_pi :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (sqNF (LocalDensity.NF.π v) : LocalSqCl v) = 1 := by
  rw [sqNF_of_ne (LocalDensity.NF.irreducible_π v).ne_zero, SqCl.ordZ_mk]
  change -WithZero.log (Valued.v (((LocalDensity.NF.π v : 𝔬) : Fv))) = 1
  rw [LocalDensity.NF.valued_π, WithZero.log_exp]
  rfl

/-- A local squareclass of valuation $0$ is the class of a unit of $\mathcal O_{\mathfrak p}$. -/
theorem exists_unit_of_ordZ_zero {t : LocalSqCl v} (ht : SqCl.ordZ (localOrd v) (localUnits_le_ker v) t = 0) :
    ∃ u : 𝔬, IsUnit u ∧ t = sqNF u := by
  obtain ⟨x, hx, rfl⟩ := mem_localUnitSqCl_of_ordZ v ht
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(y : 𝔬), y.isUnit, ?_⟩
  rw [sqNF_of_ne y.ne_zero]
  exact congrArg _ (Units.ext rfl)

/-- **The component of a distinguished family at $\mathfrak p$**: $\lambda(\mathfrak p^i)_{\mathfrak p} = [\pi u]^i$ for a
unit $u$ of $\mathcal O_{\mathfrak p}$. -/
@[kb "hanke2011structure" "Def. 4.9, p. 18 (lambda(p^i)_p = [π u]^i)"]
theorem exists_unit_comp_eq (lam : DistinguishedFamily F) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ u : v.adicCompletionIntegers F, IsUnit u ∧ ∀ i : ℕ,
      AdelicSqCl.comp v (lam.toHom (primeNZ v ^ i)) = sqNF ((LocalDensity.NF.π v * u) ^ i) := by
  have hπ := LocalDensity.NF.irreducible_π v
  set s := AdelicSqCl.comp v (lam.toHom (primeNZ v)) with hs
  have hord : SqCl.ordZ (localOrd v) (localUnits_le_ker v) s = 1 := by
    have := lam.ord_eq (primeNZ v) v
    rw [adelicOrd] at this
    rw [hs, this]
    exact idealOrd_self
  have ht : SqCl.ordZ (localOrd v) (localUnits_le_ker v)
      (s * (sqNF (LocalDensity.NF.π v) : LocalSqCl v) ^ (-1 : ℤ)) = 0 := by
    rw [SqCl.ordZ_mul, SqCl.ordZ_zpow, hord, ordZ_sqNF_pi]
    norm_num
  obtain ⟨u, hu, hut⟩ := exists_unit_of_ordZ_zero ht
  refine ⟨u, hu, fun i => ?_⟩
  have hs' : s = sqNF (LocalDensity.NF.π v * u) := by
    rw [sqNF_mul hπ.ne_zero hu.ne_zero, ← hut, _root_.zpow_neg, zpow_one, mul_comm s, mul_inv_cancel_left]
  rw [map_pow, map_pow, ← hs, hs', sqNF_pow (mul_ne_zero hπ.ne_zero hu.ne_zero)]

/-- **Corollary 5.5 for $A^*$ at $\mathfrak p \nmid 2$, every rank $n$, every number field, every distinguished family
$\lambda$**: the Euler factor $\sum_iA^*_{\mathfrak p;n}(\lambda(\mathfrak p^i))X^i$ is a rational function of
$X = q^{-s}$ (any nondegenerate reference genus $G_0$).  Unconditional. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (A*, every rank n, every number field, p ∤ 2, distinguished family lambda)"]
theorem cor_5_5_nd_A_family (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} (lam : DistinguishedFamily F)
    (G₀ : LocGenus v n) (hN₀ : G₀.Nondeg) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueAstarNF v n G₀ (AdelicSqCl.comp v (lam.toHom (primeNZ v ^ i)))) := by
  obtain ⟨u, hu, h⟩ := exists_unit_comp_eq lam v
  simp only [h]
  exact cor_5_5_nd_A_unif hv hu G₀ hN₀

/-- **Corollary 5.5 for $B^*$ at $\mathfrak p \nmid 2$, every rank $n$, every number field, every distinguished family
$\lambda$**.  Unconditional. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (B*, every rank n, every number field, p ∤ 2, distinguished family lambda)"]
theorem cor_5_5_nd_B_family (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} (lam : DistinguishedFamily F)
    (G₀ : LocGenus v n) (hN₀ : G₀.Nondeg) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueBstarNF v n G₀ (AdelicSqCl.comp v (lam.toHom (primeNZ v ^ i)))) := by
  obtain ⟨u, hu, h⟩ := exists_unit_comp_eq lam v
  simp only [h]
  exact cor_5_5_nd_B_unif hv hu G₀ hN₀

end

end QuadFormsKB.Hanke2011Structure.RatND

#print axioms QuadFormsKB.Hanke2011Structure.RatND.exists_unit_comp_eq
#print axioms QuadFormsKB.Hanke2011Structure.RatND.cor_5_5_nd_A_family
#print axioms QuadFormsKB.Hanke2011Structure.RatND.cor_5_5_nd_B_family
