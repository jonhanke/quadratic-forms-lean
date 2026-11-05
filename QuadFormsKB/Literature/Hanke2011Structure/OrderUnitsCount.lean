/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Citation

/-!
# The number of units of $\mathcal O/I$ for a Dedekind domain (Euler's function for ideals)

For a Dedekind domain $S$ that is a free $\mathbb Z$-module of finite rank (e.g. the ring of integers of a number field)
and a nonzero ideal $I = \prod_{\mathfrak P}\mathfrak P^{e_{\mathfrak P}}$,
$$\#(S/I)^\times = N(I)\prod_{\mathfrak P \mid I}\Bigl(1 - \frac1{N\mathfrak P}\Bigr)$$
(`card_units_quot`), with $N = $ `Ideal.absNorm`. Proof: $(S/\mathfrak P^e)^\times$ is the complement of the kernel of
$S/\mathfrak P^e \to S/\mathfrak P$, of size $N\mathfrak P^{e-1}$ (`card_units_quot_pow`), and the Chinese remainder theorem
(`IsDedekindDomain.quotientEquivPiFactors`). Used for the class numbers of orders (Remark 8.8 of
Hanke 2011, `OrderClassNumber.lean`).

Source: Neukirch, *Algebraic Number Theory*, Ch. I, (12.12) and its proof (the factor $\#(\mathcal O_K/\mathfrak f)^\times$).
-/

open UniqueFactorizationMonoid

namespace QuadFormsKB.Hanke2011Structure.OrderCN

set_option linter.unusedSectionVars false

noncomputable section

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S] [Infinite S]

theorem finite_quot {I : Ideal S} (hI : I ≠ ⊥) : Finite (S ⧸ I) :=
  (Ideal.absNorm_ne_zero_iff I).mp (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem card_quot (I : Ideal S) : Nat.card (S ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- The units of a ring, as a subtype of the elements that are units. -/
def unitsEquivIsUnit (A : Type*) [Monoid A] : Aˣ ≃ {x : A // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext rfl
  right_inv x := Subtype.ext rfl

/-- **$\#(S/\mathfrak P^e)^\times\cdot N\mathfrak P = N\mathfrak P^e\,(N\mathfrak P - 1)$** for a nonzero prime $\mathfrak P$ and
$e \ge 1$. -/
theorem card_units_quot_pow {P : Ideal S} (hP0 : P ≠ ⊥) [hP : P.IsPrime] {e : ℕ} (he : 1 ≤ e) :
    Nat.card (S ⧸ P ^ e)ˣ * Ideal.absNorm P = Ideal.absNorm P ^ e * (Ideal.absNorm P - 1) := by
  classical
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have hPe0 : P ^ e ≠ ⊥ := pow_ne_zero _ hP0
  haveI := finite_quot hPe0
  haveI := finite_quot hP0
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  let f : S ⧸ P ^ e →+* S ⧸ P := Ideal.Quotient.factor (Ideal.pow_le_self (by omega))
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  -- units are the elements with nonzero image
  have hunit : ∀ x : S ⧸ P ^ e, IsUnit x ↔ f x ≠ 0 := by
    intro x
    constructor
    · intro hx h0
      have := hx.map f
      rw [h0] at this
      exact not_isUnit_zero this
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have ha : a ∉ P := by
        intro haP
        apply hx
        show Ideal.Quotient.mk P a = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr haP
      obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv ha
      have hnil : IsNilpotent (Ideal.Quotient.mk (P ^ e) i) :=
        ⟨e, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hi e)⟩
      have hu : IsUnit (Ideal.Quotient.mk (P ^ e) a * Ideal.Quotient.mk (P ^ e) y) := by
        rw [← map_mul, show a * y = 1 - i by linear_combination hyi, map_sub, map_one]
        exact hnil.isUnit_one_sub
      exact isUnit_of_mul_isUnit_left hu
  -- counting
  set N := Ideal.absNorm P with hN
  have hcardPe : Nat.card (S ⧸ P ^ e) = N ^ e := by rw [card_quot, map_pow]
  have hcardP : Nat.card (S ⧸ P) = N := card_quot P
  have hker : Nat.card (S ⧸ P ^ e) = N * Nat.card {x : S ⧸ P ^ e // f x = 0} := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (f.toAddMonoidHom.ker)
    have h2 : Nat.card ((S ⧸ P ^ e) ⧸ f.toAddMonoidHom.ker) = N := by
      rw [← hcardP]
      exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom hf).toEquiv
    rw [h1, h2]
    rfl
  have hsplit : Nat.card (S ⧸ P ^ e) =
      Nat.card {x : S ⧸ P ^ e // f x ≠ 0} + Nat.card {x : S ⧸ P ^ e // f x = 0} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun x : S ⧸ P ^ e => f x ≠ 0)).symm |>.trans
      (by congr 1; simp only [not_not])
  have hunits : Nat.card (S ⧸ P ^ e)ˣ = Nat.card {x : S ⧸ P ^ e // f x ≠ 0} := by
    rw [Nat.card_congr (unitsEquivIsUnit _)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hunit)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP0)
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hK : Nat.card {x : S ⧸ P ^ (k + 1) // f x = 0} = N ^ k := by
    have := hker
    rw [hcardPe, pow_succ, mul_comm] at this
    exact (Nat.eq_of_mul_eq_mul_left (by omega) this).symm
  rw [hunits]
  have hs := hsplit
  rw [hcardPe, hK] at hs
  have : Nat.card {x : S ⧸ P ^ (k + 1) // f x ≠ 0} = N ^ (k + 1) - N ^ k := by omega
  rw [this, Nat.sub_mul, pow_succ, Nat.mul_sub, mul_one]

/-- $I = \prod_{\mathfrak P}\mathfrak P^{e_{\mathfrak P}}$ over the distinct prime factors. -/
theorem prod_factors_pow {I : Ideal S} (hI : I ≠ ⊥) :
    ∏ P ∈ (factors I).toFinset, P ^ (factors I).count P = I := by
  classical
  have h := Finset.prod_multiset_map_count (factors I) id
  simp only [Multiset.map_id', id] at h
  rw [← h]
  exact associated_iff_eq.mp (factors_prod hI)

theorem mem_factors_ne_bot {I P : Ideal S} (hP : P ∈ factors I) : P ≠ ⊥ :=
  (prime_of_factor _ hP).ne_zero

theorem mem_factors_isPrime {I P : Ideal S} (hP : P ∈ factors I) : P.IsPrime :=
  Ideal.isPrime_of_prime (prime_of_factor _ hP)

/-- **Chinese remainder theorem for the units:** $\#(S/I)^\times = \prod_{\mathfrak P}\#(S/\mathfrak P^{e_\mathfrak P})^\times$. -/
theorem card_units_quot_eq_prod {I : Ideal S} (hI : I ≠ ⊥) :
    Nat.card (S ⧸ I)ˣ = ∏ P : (factors I).toFinset, Nat.card (S ⧸ (P : Ideal S) ^ (factors I).count (P : Ideal S))ˣ := by
  classical
  rw [Nat.card_congr (Units.mapEquiv (IsDedekindDomain.quotientEquivPiFactors hI).toMulEquiv).toEquiv,
    Nat.card_congr (MulEquiv.piUnits).toEquiv, Nat.card_pi]

/-- **Euler's function for ideals:** $\#(S/I)^\times = N(I)\prod_{\mathfrak P \mid I}(1 - N\mathfrak P^{-1})$ for $I \ne 0$. -/
@[kb "neukirch1999" "Ch. I, §12, proof of (12.12) (#(O/f)^×)"]
theorem card_units_quot {I : Ideal S} (hI : I ≠ ⊥) :
    (Nat.card (S ⧸ I)ˣ : ℚ) =
      Ideal.absNorm I * ∏ P ∈ (factors I).toFinset, (1 - 1 / (Ideal.absNorm P : ℚ)) := by
  classical
  have hN := congrArg Ideal.absNorm (prod_factors_pow hI)
  rw [map_prod] at hN
  rw [card_units_quot_eq_prod hI, ← hN, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
  rw [← Finset.prod_coe_sort (factors I).toFinset]
  refine Finset.prod_congr rfl fun P _ => ?_
  have hPm : (P : Ideal S) ∈ factors I := Multiset.mem_toFinset.mp P.2
  have hP0 := mem_factors_ne_bot hPm
  haveI := mem_factors_isPrime hPm
  have he : 1 ≤ (factors I).count (P : Ideal S) := Multiset.one_le_count_iff_mem.mpr hPm
  have h := card_units_quot_pow hP0 he
  have hN : (Ideal.absNorm (P : Ideal S) : ℚ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hP0
  have hN1 : 1 ≤ Ideal.absNorm (P : Ideal S) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP0)
  have hq : ((Nat.card (S ⧸ (P : Ideal S) ^ (factors I).count (P : Ideal S))ˣ : ℕ) : ℚ) * Ideal.absNorm (P : Ideal S) =
      (Ideal.absNorm (P : Ideal S) : ℚ) ^ (factors I).count (P : Ideal S) * ((Ideal.absNorm (P : Ideal S) : ℚ) - 1) := by
    have h' := congrArg (Nat.cast : ℕ → ℚ) h
    push_cast [Nat.cast_sub hN1] at h'
    exact h'
  rw [map_pow, Nat.cast_pow]
  field_simp
  linear_combination hq

end

end QuadFormsKB.Hanke2011Structure.OrderCN

#print axioms QuadFormsKB.Hanke2011Structure.OrderCN.card_units_quot
