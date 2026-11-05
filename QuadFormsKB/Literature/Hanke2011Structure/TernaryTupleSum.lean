/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Citation

/-!
# Sums over tuples of local data with a sign constraint (Hanke 2011, Thm. 4.8, eq. (12))

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), proof of Theorem 4.8, p. 18.

An abstract form of the computation behind Theorem 4.8, phrased for tuples indexed by an arbitrary type $\iota$ (in the
application: the primes of $\mathbb Q$). Let $P \subseteq \iota$ be finite; at each index $i$ a set $A_i$ of allowed local
data is given, with a sign $s_i : X_i \to \{\pm1\}$; outside $P$ the only allowed datum is a base point $b_i$, of sign $1$.
Then for weights $r_i$
$$\sum_{\substack{t \in \prod_i A_i\\ \prod_i s_i(t_i) = 1}}\ \prod_{i\in P}r_i(t_i)
  = \frac12\Bigl[\prod_{i\in P}\sum_{x\in A_i}r_i(x) + \prod_{i\in P}\sum_{x\in A_i}s_i(x)\,r_i(x)\Bigr]$$
(`finsum_tuple_sign`). *Proof:* the tuples are the extensions of the tuples on $P$ by the base points; the indicator of
$\prod_is_i = 1$ is $(1 + \prod_is_i)/2$, and a product of sums is a sum over the product set.

`invDensity_factor`: a product $\prod_i w_i(t_i)^{-1}$ over a tuple that agrees with the base tuple outside $P$ factors as
$\prod_i w_i(b_i)^{-1}\cdot\prod_{i\in P}w_i(b_i)/w_i(t_i)$, provided the base product is multipliable.
-/

open Finset

namespace QuadFormsKB.Hanke2011Structure

noncomputable section

variable {ι : Type*} {X : ι → Type*}

open Classical in
/-- Extension of a tuple on the finite set `P` by the base tuple `b`. -/
def extTuple (P : Finset ι) (b : ∀ i, X i) (y : ∀ i : P, X i) : ∀ i, X i :=
  fun i => if h : i ∈ P then y ⟨i, h⟩ else b i

theorem extTuple_of_mem {P : Finset ι} {b : ∀ i, X i} (y : ∀ i : P, X i) {i : ι} (h : i ∈ P) :
    extTuple P b y i = y ⟨i, h⟩ := by
  classical
  unfold extTuple; rw [dite_eq_left h]

theorem extTuple_of_not_mem {P : Finset ι} {b : ∀ i, X i} (y : ∀ i : P, X i) {i : ι} (h : i ∉ P) :
    extTuple P b y i = b i := by
  classical
  unfold extTuple; rw [dite_eq_right h]

theorem extTuple_injective (P : Finset ι) (b : ∀ i, X i) : Function.Injective (extTuple P b) := by
  intro y y' h
  funext ⟨i, hi⟩
  have := congrFun h i
  rwa [extTuple_of_mem y hi, extTuple_of_mem y' hi] at this

/-- The set of admissible tuples is finite. -/
theorem tupleSet_finite (P : Finset ι) (b : ∀ i, X i) (A : ∀ i, Set (X i)) (Q : (∀ i, X i) → Prop)
    (hout : ∀ i ∉ P, A i = {b i}) (hfin : ∀ i ∈ P, (A i).Finite) :
    {t : ∀ i, X i | (∀ i, t i ∈ A i) ∧ Q t}.Finite := by
  have hpi : (Set.pi Set.univ fun i : P => A i.1).Finite := Set.Finite.pi fun i => hfin i.1 i.2
  refine (hpi.image (extTuple P b)).subset ?_
  rintro t ⟨hA, -⟩
  refine ⟨fun i => t i.1, fun i _ => hA i.1, ?_⟩
  funext i
  by_cases hi : i ∈ P
  · rw [extTuple_of_mem _ hi]
  · rw [extTuple_of_not_mem _ hi]
    have := hA i; rw [hout i hi] at this; exact this.symm

/-- **The sign-constrained tuple sum** (Hanke 2011, proof of Thm. 4.8, eq. (12), abstract form). -/
@[kb "hanke2011structure" "Thm. 4.8, proof, eq. (12), p. 18 (tuples of local data)"]
theorem finsum_tuple_sign (P : Finset ι) (b : ∀ i, X i) (A : ∀ i, Set (X i)) (s : ∀ i, X i → ℤ)
    (r : ∀ i, X i → ℝ) (hout : ∀ i ∉ P, A i = {b i}) (hsb : ∀ i ∉ P, s i (b i) = 1)
    (hfin : ∀ i ∈ P, (A i).Finite) (hs : ∀ i x, s i x = 1 ∨ s i x = -1) :
    ∑ᶠ t ∈ {t : ∀ i, X i | (∀ i, t i ∈ A i) ∧ (Function.mulSupport fun i => s i (t i)).Finite ∧
        ∏ᶠ i, s i (t i) = 1}, ∏ i ∈ P, r i (t i) =
      ((∏ i ∈ P, ∑ᶠ x ∈ A i, r i x) + ∏ i ∈ P, ∑ᶠ x ∈ A i, (s i x : ℝ) * r i x) / 2 := by
  classical
  -- the finite sets on `P`
  let Af : ∀ i : P, Finset (X i) := fun i => (hfin i.1 i.2).toFinset
  have hAf : ∀ (i : P) x, x ∈ Af i ↔ x ∈ A i := fun i x => (hfin i.1 i.2).mem_toFinset
  let T' : Finset (∀ i : P, X i) := (Fintype.piFinset Af).filter fun y => ∏ i : P, s i (y i) = 1
  -- the set of tuples is the image of `T'`
  have hprod_ext : ∀ y : ∀ i : P, X i, (Function.mulSupport fun i => s i (extTuple P b y i)) ⊆ P := by
    intro y i hi
    by_contra h
    exact hi (by simp only; rw [extTuple_of_not_mem y h, hsb i h])
  have hfinprod : ∀ y : ∀ i : P, X i, ∏ᶠ i, s i (extTuple P b y i) = ∏ i : P, s i (y i) := by
    intro y
    rw [finprod_eq_prod_of_mulSupport_subset _ (hprod_ext y), ← Finset.prod_coe_sort P]
    exact Finset.prod_congr rfl fun i _ => by rw [extTuple_of_mem y i.2]
  have hset : {t : ∀ i, X i | (∀ i, t i ∈ A i) ∧ (Function.mulSupport fun i => s i (t i)).Finite ∧
      ∏ᶠ i, s i (t i) = 1} = extTuple P b '' (T' : Set (∀ i : P, X i)) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Fintype.mem_piFinset, T']
    constructor
    · rintro ⟨hA, -, hp⟩
      refine ⟨fun i => t i.1, ⟨fun i => (hAf i _).mpr (hA i.1), ?_⟩, ?_⟩
      · have ht : extTuple P b (fun i : P => t i.1) = t := by
          funext i
          by_cases hi : i ∈ P
          · rw [extTuple_of_mem _ hi]
          · rw [extTuple_of_not_mem _ hi]
            have := hA i; rw [hout i hi] at this; exact this.symm
        rw [← hfinprod, ht]; exact hp
      · funext i
        by_cases hi : i ∈ P
        · rw [extTuple_of_mem _ hi]
        · rw [extTuple_of_not_mem _ hi]
          have := hA i; rw [hout i hi] at this; exact this.symm
    · rintro ⟨y, ⟨hy, hp⟩, rfl⟩
      refine ⟨fun i => ?_, (P.finite_toSet.subset (hprod_ext y)), by rw [hfinprod]; exact hp⟩
      by_cases hi : i ∈ P
      · rw [extTuple_of_mem _ hi]; exact (hAf _ _).mp (hy ⟨i, hi⟩)
      · rw [extTuple_of_not_mem _ hi, hout i hi]; rfl
  rw [hset, finsum_mem_image (extTuple_injective P b).injOn, finsum_mem_coe_finset]
  have hterm : ∀ y : ∀ i : P, X i, ∏ i ∈ P, r i (extTuple P b y i) = ∏ i : P, r i (y i) := by
    intro y
    rw [← Finset.prod_coe_sort P]
    exact Finset.prod_congr rfl fun i _ => by rw [extTuple_of_mem y i.2]
  simp_rw [hterm]
  -- the indicator of `∏ s = 1` is `(1 + ∏ s)/2`
  have hind : ∀ y : ∀ i : P, X i, (if ∏ i : P, s i (y i) = 1 then (1 : ℝ) else 0) =
      (1 + ((∏ i : P, s i (y i) : ℤ) : ℝ)) / 2 := by
    intro y
    have hpm : ∏ i : P, s i (y i) = 1 ∨ ∏ i : P, s i (y i) = -1 := by
      have key : ∀ (S : Finset P), ∏ i ∈ S, s i (y i) = 1 ∨ ∏ i ∈ S, s i (y i) = -1 := by
        intro S
        induction S using Finset.induction_on with
        | empty => simp
        | insert a S ha ih =>
          rw [Finset.prod_insert ha]
          rcases hs a (y a) with h | h <;> rcases ih with h' | h' <;> simp [h, h']
      exact key _
    rcases hpm with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_filter]
  have e1 : ∀ y : ∀ i : P, X i, (if ∏ i : P, s i (y i) = 1 then ∏ i : P, r i (y i) else 0) =
      ((∏ i : P, r i (y i)) + ∏ i : P, ((s i (y i) : ℤ) : ℝ) * r i (y i)) / 2 := by
    intro y
    have := hind y
    rw [Finset.prod_mul_distrib, ← Int.cast_prod]
    by_cases h : ∏ i : P, s i (y i) = 1
    · rw [if_pos h] at this ⊢; rw [h]; push_cast; ring
    · rw [if_neg h] at this ⊢
      have : ((∏ i : P, s i (y i) : ℤ) : ℝ) = -1 := by linarith
      rw [this]; ring
  simp_rw [e1]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  congr 2
  · rw [← Finset.prod_coe_sort P]
    rw [Finset.prod_congr rfl fun (i : P) _ => finsum_mem_eq_finite_toFinset_sum (fun x => r i.1 x) (hfin i.1 i.2)]
    exact (Finset.prod_univ_sum (fun i : P => (hfin i.1 i.2).toFinset) (fun i x => r i.1 x)).symm
  · rw [← Finset.prod_coe_sort P]
    rw [Finset.prod_congr rfl fun (i : P) _ =>
      finsum_mem_eq_finite_toFinset_sum (fun x => ((s i.1 x : ℤ) : ℝ) * r i.1 x) (hfin i.1 i.2)]
    exact (Finset.prod_univ_sum (fun i : P => (hfin i.1 i.2).toFinset)
      (fun i x => ((s i.1 x : ℤ) : ℝ) * r i.1 x)).symm

/-- **Factorization of a density product over a tuple that is the base tuple outside a finite set.** If
$w_i(t_i) = w_i(b_i)$ for $i \notin P$, all $w_i(b_i), w_i(t_i)$ are nonzero and $\prod_iw_i(b_i)^{-1}$ is multipliable, then
$\prod_iw_i(t_i)^{-1}$ is multipliable and equals $\prod_iw_i(b_i)^{-1}\cdot\prod_{i\in P}w_i(b_i)/w_i(t_i)$. -/
theorem invDensity_factor (P : Finset ι) (wb wt : ι → ℝ) (hout : ∀ i ∉ P, wt i = wb i)
    (hb : ∀ i, wb i ≠ 0) (ht : ∀ i, wt i ≠ 0) (hm : Multipliable fun i => (wb i)⁻¹) :
    Multipliable (fun i => (wt i)⁻¹) ∧
      ∏' i, (wt i)⁻¹ = (∏' i, (wb i)⁻¹) * ∏ i ∈ P, wb i / wt i := by
  have hsupp : Function.mulSupport (fun i => wb i / wt i) ⊆ P := by
    intro i hi
    by_contra h
    exact hi (by simp only; rw [hout i h, div_self (hb i)])
  have hg : Multipliable fun i => wb i / wt i :=
    multipliable_of_hasFiniteMulSupport (P.finite_toSet.subset hsupp)
  have e : (fun i => (wt i)⁻¹) = fun i => (wb i)⁻¹ * (wb i / wt i) := by
    funext i; field_simp [hb i, ht i]
  rw [e]
  refine ⟨hm.mul hg, ?_⟩
  rw [hm.tprod_mul hg, tprod_eq_prod' hsupp]

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.finsum_tuple_sign
#print axioms QuadFormsKB.Hanke2011Structure.invDensity_factor
