/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicSeries

/-!
# Paper 6, Corollary 5.5 at $\mathfrak p \nmid 2$ for a general uniformizing squareclass

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Cor. 5.5, p. 24.

A distinguished family $\lambda$ (Def. 4.9) is a homomorphism, so its component at $\mathfrak p$ is
$\lambda(\mathfrak p^i)_{\mathfrak p} = S^i$ with $S = \lambda(\mathfrak p)_{\mathfrak p}$ of valuation $1$, i.e.
$S = [\pi u]$ for a unit $u$.  Then $S^i = [\pi^i]$ for $i$ even and $[\pi^iu]$ for $i$ odd, so the Euler factor
$\sum_iA^*_{\mathfrak p;n}(S^i)X^i$ is the even part of the fixed-unit series with $w = 1$ plus the odd part of the one
with $w = u$.  Both are rational (Thm. 5.4, `theorem_5_4_nd_A`), and the even and odd parts of a rational series are
rational ($\frac12(f(X) \pm f(-X))$; `RatSeries.rescale_neg`).  This is the paper's proof ("scaling of a power series
along congruence classes of powers ... by a rational transformation").

* `cor_5_5_nd_A_unif`, `cor_5_5_nd_B_unif`: for every unit $u$ the series $\sum_iA^*_{\mathfrak p;n}([\pi u]^i)X^i$,
  $\sum_iB^*_{\mathfrak p;n}([\pi u]^i)X^i$ are rational functions of $X = q^{-s}$ (reference genus $G_0$:
  any nondegenerate genus).  Unconditional.

Indices are 0-based.
-/

open Finset Matrix IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.RatND

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure
  QuadFormsKB.Hanke2011Structure.RatOdd QuadFormsKB.ConwaySloane QuadFormsKB.Odd7 QuadFormsKB.Siegel

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

/-! ### Rational series under $X \mapsto -X$, even and odd parts -/

open Polynomial in
theorem coe_comp_negX (Q : Polynomial ℝ) :
    ((Q.comp (-X) : Polynomial ℝ) : PowerSeries ℝ) = PowerSeries.rescale (-1) (Q : PowerSeries ℝ) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, Polynomial.coe_add, hp, hq, Polynomial.coe_add, map_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp]
    ext k
    rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_C_mul, coeff_C_mul,
      neg_pow, ← C_1, ← C_neg, ← C_pow, coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

/-- **A rational series stays rational under $X \mapsto -X$.** -/
theorem RatSeries.rescale_neg {S : PowerSeries ℝ} (hS : RatSeries S) :
    RatSeries (PowerSeries.rescale (-1) S) := by
  obtain ⟨P, Q, hQ, h⟩ := hS
  refine ⟨P.comp (-Polynomial.X), Q.comp (-Polynomial.X), ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, neg_zero,
      ← Polynomial.coeff_zero_eq_eval_zero]
    exact hQ
  · rw [coe_comp_negX, coe_comp_negX, ← map_mul, h]

/-- **Even/odd splicing**: if $\sum a_iX^i$ and $\sum b_iX^i$ are rational, so is $\sum c_iX^i$ with $c_i = a_i$ for
$i$ even and $c_i = b_i$ for $i$ odd. -/
theorem RatSeries.parity {a b : ℕ → ℝ} (ha : RatSeries (PowerSeries.mk a)) (hb : RatSeries (PowerSeries.mk b)) :
    RatSeries (PowerSeries.mk fun i => if Even i then a i else b i) := by
  have e : (PowerSeries.mk fun i => if Even i then a i else b i) =
      PowerSeries.C (1 / 2 : ℝ) * PowerSeries.X ^ 0 * PowerSeries.mk a +
        (PowerSeries.C (1 / 2 : ℝ) * PowerSeries.X ^ 0 * PowerSeries.rescale (-1) (PowerSeries.mk a) +
          (PowerSeries.C (1 / 2 : ℝ) * PowerSeries.X ^ 0 * PowerSeries.mk b +
            PowerSeries.C (-1 / 2 : ℝ) * PowerSeries.X ^ 0 * PowerSeries.rescale (-1) (PowerSeries.mk b))) := by
    ext i
    simp only [PowerSeries.coeff_mk, map_add, pow_zero, mul_one, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_rescale]
    rcases Nat.even_or_odd i with h | h
    · rw [if_pos h, h.neg_one_pow]; ring
    · rw [if_neg (Nat.not_even_iff_odd.2 h), h.neg_one_pow]; ring
  rw [e]
  exact (RatSeries.CXpowMul _ 0 ha).add ((RatSeries.CXpowMul _ 0 (RatSeries.rescale_neg ha)).add
    ((RatSeries.CXpowMul _ 0 hb).add (RatSeries.CXpowMul _ 0 (RatSeries.rescale_neg hb))))

section NF

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Theorem 5.4 for $A^*$ with any nondegenerate reference genus $G_0$ (the proof of `theorem_5_4_nd_A` uses only
nondegeneracy of $G_0$). -/
theorem ratA_nd (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} {w : 𝔬} (hw : IsUnit w) (G₀ : LocGenus v n)
    (hN₀ : G₀.Nondeg) :
    RatSeries (PowerSeries.mk fun ν : ℕ => trueAstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  obtain ⟨K, hK⟩ := sum_genStar_nd_eq hv hcU hc hw G₀ hN₀
  have hM : MND v 0 Sign.plus = 1 := Mq_zero _ _
  have ha : aND v 0 = 1 := aq_zero _
  have e : (PowerSeries.mk fun ν : ℕ => trueAstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) =
      PowerSeries.C K * PowerSeries.X ^ 0 *
        (ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) 1) n +
          ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) (-1)) n) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueAstarNF, hK ν 1, hK ν (-1)]
    simp [ser, PowerSeries.coeff_mk, mul_add]
  rw [e]
  exact RatSeries.CXpowMul K 0 ((rat_Pn hM ha n _).add (rat_Pn hM ha n _))

/-- Theorem 5.4 for $B^*$ with any nondegenerate reference genus $G_0$. -/
theorem ratB_nd (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} {w : 𝔬} (hw : IsUnit w) (G₀ : LocGenus v n)
    (hN₀ : G₀.Nondeg) :
    RatSeries (PowerSeries.mk fun ν : ℕ => trueBstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  obtain ⟨K, hK⟩ := sum_genStar_nd_eq hv hcU hc hw G₀ hN₀
  have hM : MND v 0 Sign.plus = 1 := Mq_zero _ _
  have ha : aND v 0 = 1 := aq_zero _
  have e : (PowerSeries.mk fun ν : ℕ => trueBstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) =
      PowerSeries.C K * PowerSeries.X ^ 0 *
        (ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) 1) n +
          PowerSeries.C (-1) * PowerSeries.X ^ 0 *
            ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) (-1)) n) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueBstarNF, hK ν 1, hK ν (-1)]
    simp [ser, PowerSeries.coeff_mk, mul_add]
    ring
  rw [e]
  exact RatSeries.CXpowMul K 0 ((rat_Pn hM ha n _).add (RatSeries.CXpowMul (-1) 0 (rat_Pn hM ha n _)))

/-- $[\pi u]^i = [\pi^i]$ for $i$ even and $[\pi^iu]$ for $i$ odd. -/
theorem sqNF_pi_mul_pow {u : 𝔬} (hu : IsUnit u) (i : ℕ) :
    (sqNF ((LocalDensity.NF.π v * u) ^ i) : LocalSqCl v) =
      sqNF (LocalDensity.NF.π v ^ i * (if Even i then 1 else u)) := by
  have hπ := LocalDensity.NF.irreducible_π v
  have hx : (LocalDensity.NF.π v * u) ^ i ≠ 0 := pow_ne_zero _ (mul_ne_zero hπ.ne_zero hu.ne_zero)
  have hy : LocalDensity.NF.π v ^ i * (if Even i then 1 else u) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hπ.ne_zero) ?_
    split_ifs
    · exact one_ne_zero
    · exact hu.ne_zero
  rw [sqNF_eq_iff hx hy]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
  · set U := hu.unit
    have key : ((U⁻¹ ^ k : 𝔬ˣ) : 𝔬) ^ 2 * (U : 𝔬) ^ (2 * k) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have : (U⁻¹ ^ k) ^ 2 * U ^ (2 * k) = 1 := by group
      rw [this, Units.val_one]
    refine ⟨U⁻¹ ^ k, ?_⟩
    have he : Even i := ⟨k, by omega⟩
    have hU : (U : 𝔬) = u := hu.unit_spec
    rw [if_pos he, mul_pow, hk, ← hU, mul_one]
    linear_combination (LocalDensity.NF.π v ^ (2 * k)) * key
  · set U := hu.unit
    have key : ((U⁻¹ ^ k : 𝔬ˣ) : 𝔬) ^ 2 * (U : 𝔬) ^ (2 * k) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have : (U⁻¹ ^ k) ^ 2 * U ^ (2 * k) = 1 := by group
      rw [this, Units.val_one]
    refine ⟨U⁻¹ ^ k, ?_⟩
    have ho : ¬ Even i := Nat.not_even_iff_odd.2 ⟨k, hk⟩
    have hU : (U : 𝔬) = u := hu.unit_spec
    rw [if_neg ho, mul_pow, hk, ← hU]
    linear_combination (LocalDensity.NF.π v ^ (2 * k + 1) * (U : 𝔬)) * key

/-- **Corollary 5.5 for $A^*$ at $\mathfrak p \nmid 2$ of a number field, every rank $n$, general distinguished
family**: for a unit $u$ (so $\lambda(\mathfrak p)_{\mathfrak p} = [\pi u]$ for a distinguished family $\lambda$) and
any nondegenerate reference genus $G_0$, the Euler factor $\sum_iA^*_{\mathfrak p;n}([\pi u]^i)X^i$ is a rational
function of $X = q^{-s}$.  Unconditional. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (A*, every rank n, every number field, p ∤ 2, lambda(p) = [π u])"]
theorem cor_5_5_nd_A_unif (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} {u : 𝔬} (hu : IsUnit u) (G₀ : LocGenus v n)
    (hN₀ : G₀.Nondeg) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueAstarNF v n G₀ (sqNF ((LocalDensity.NF.π v * u) ^ i))) := by
  have h := RatSeries.parity (ratA_nd hv isUnit_one G₀ hN₀) (ratA_nd hv hu G₀ hN₀)
  convert h using 2
  funext i
  rw [sqNF_pi_mul_pow hu i]
  split_ifs <;> rfl

/-- **Corollary 5.5 for $B^*$ at $\mathfrak p \nmid 2$ of a number field, every rank $n$, general distinguished
family** ($\lambda(\mathfrak p)_{\mathfrak p} = [\pi u]$).  Unconditional. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (B*, every rank n, every number field, p ∤ 2, lambda(p) = [π u])"]
theorem cor_5_5_nd_B_unif (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} {u : 𝔬} (hu : IsUnit u) (G₀ : LocGenus v n)
    (hN₀ : G₀.Nondeg) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueBstarNF v n G₀ (sqNF ((LocalDensity.NF.π v * u) ^ i))) := by
  have h := RatSeries.parity (ratB_nd hv isUnit_one G₀ hN₀) (ratB_nd hv hu G₀ hN₀)
  convert h using 2
  funext i
  rw [sqNF_pi_mul_pow hu i]
  split_ifs <;> rfl

end NF

end

end QuadFormsKB.Hanke2011Structure.RatND

#print axioms QuadFormsKB.Hanke2011Structure.RatND.cor_5_5_nd_A_unif
#print axioms QuadFormsKB.Hanke2011Structure.RatND.cor_5_5_nd_B_unif
