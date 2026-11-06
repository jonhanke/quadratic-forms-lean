/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddSeries
import QuadFormsKB.Tamagawa.Odd7Symbol

/-!
# Paper 6, Theorem 5.4 at odd primes: the statistics of the symbol of a diagonal form

For a diagonal form $\operatorname{diag}(p^{z_i}w_i)$ ($i < n$) with unit entries and
$x_i = \left(\frac{w_i}{p}\right) \in \{\pm1\}$, the $p$-adic symbol (Conway–Sloane, §7.2) is
`Odd7.symC z x` (multiplicity $\#\{i : z_i = k\}$, sign $\prod_{z_i = k}x_i$ at the scale $p^k$).  This file computes
the statistics of `RationalityOddSeries` (total dimension, weighted scale, and the state
$(E, O, d_e, d_o)$) of such a symbol directly from $(z, x)$:
$$r = n,\quad \nu = \sum_iz_i,\quad E = \prod_{z_i\text{ even}}x_i,\quad O = \prod_{z_i\text{ odd}}x_i,\quad
  d_e = \#\{i : z_i \text{ even}\},\quad d_o = \#\{i : z_i\text{ odd}\}.$$

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Hanke2011Structure.RatOdd

open QuadFormsKB.ConwaySloane QuadFormsKB.Odd7

/-- **Fibering a sum over the scales by the exponents**: $\prod_{k<N}[q(k)]\prod_i[z_i = k]u_i = \prod_i[q(z_i)]u_i$
when all $z_i < N$. -/
@[to_additive]
theorem prod_range_fiber {M : Type*} [CommMonoid M] {n : ℕ} (N : ℕ) (z : Fin n → ℕ) (hz : ∀ i, z i < N)
    (q : ℕ → Prop) [DecidablePred q] (u : Fin n → M) :
    ∏ k ∈ range N, (if q k then ∏ i, (if z i = k then u i else 1) else 1) =
      ∏ i, (if q (z i) then u i else 1) := by
  have h1 : ∀ k, (if q k then ∏ i, (if z i = k then u i else 1) else 1) =
      ∏ i, (if z i = k then (if q (z i) then u i else 1) else 1) := by
    intro k
    split_ifs with hk
    · refine Finset.prod_congr rfl fun i _ => ?_
      split_ifs with h2 h3 <;> first | rfl | (subst h2; exact absurd hk h3)
    · refine (Finset.prod_eq_one fun i _ => ?_).symm
      split_ifs with h2 h3 <;> first | rfl | (subst h2; exact absurd h3 hk)
  rw [Finset.prod_congr rfl fun k _ => h1 k, Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_ite_eq]
  simp [hz i]

theorem signU_ite (P : ℤˣ) : signU (if P = 1 then Sign.plus else Sign.minus) = P := by
  rcases Int.units_eq_one_or P with h | h <;> simp [h, signU]

section Stats

variable {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ)

/-- A cutoff above all the exponents. -/
def bnd : ℕ := (Finset.univ.sup z) + 1

theorem lt_bnd (i : Fin n) : z i < bnd z := Nat.lt_succ_of_le (Finset.le_sup (f := z) (Finset.mem_univ i))

theorem symC_dim (k : ℕ) : (symC z x k).dim = ∑ i, if z i = k then 1 else 0 := rfl

theorem symC_signU (k : ℕ) : signU (symC z x k).sign = ∏ i, if z i = k then x i else 1 :=
  signU_ite _

theorem trivFrom_symC {N : ℕ} (hz : ∀ i, z i < N) : TrivFrom (symC z x) N := by
  intro k hk
  have h1 : ∀ i, z i ≠ k := fun i => by have := hz i; omega
  simp [symC, OddFactor.trivial, h1]

theorem valid_symC : Valid (symC z x) := by
  intro k hk
  have h1 : ∀ i, z i ≠ k := by
    intro i hi
    have : (symC z x k).dim = ∑ i, if z i = k then 1 else 0 := rfl
    rw [this] at hk
    have := (Finset.sum_eq_zero_iff.1 hk) i (Finset.mem_univ i)
    simp [hi] at this
  simp [symC, h1]

theorem rk_symC {N : ℕ} (hz : ∀ i, z i < N) : rk (symC z x) N = n := by
  unfold rk
  have := sum_range_fiber N z hz (fun _ => True) (fun _ => 1)
  simpa [symC_dim] using this

theorem zs_symC {N : ℕ} (hz : ∀ i, z i < N) : zs (symC z x) N = ∑ i, z i := by
  unfold zs
  have h1 : ∀ k, k * (symC z x k).dim = ∑ i, if z i = k then z i else 0 := by
    intro k
    rw [symC_dim, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · simp [h]
    · simp
  have := sum_range_fiber N z hz (fun _ => True) z
  simp only [if_true] at this
  rw [Finset.sum_congr rfl fun k _ => h1 k]
  exact this

/-- The product of the signs at the even scales, from $(z, x)$. -/
def evZ : ℤˣ := ∏ i, if z i % 2 = 0 then x i else 1
/-- The product of the signs at the odd scales, from $(z, x)$. -/
def odZ : ℤˣ := ∏ i, if z i % 2 = 1 then x i else 1
/-- The number of even exponents. -/
def deZ : ℕ := ∑ i, if z i % 2 = 0 then 1 else 0
/-- The number of odd exponents. -/
def ddZ : ℕ := ∑ i, if z i % 2 = 1 then 1 else 0

theorem ev_symC {N : ℕ} (hz : ∀ i, z i < N) : ev (symC z x) N = evZ z x := by
  unfold ev evZ
  simp only [symC_signU]
  exact prod_range_fiber N z hz (fun k => k % 2 = 0) x

theorem od_symC {N : ℕ} (hz : ∀ i, z i < N) : od (symC z x) N = odZ z x := by
  unfold od odZ
  simp only [symC_signU]
  exact prod_range_fiber N z hz (fun k => k % 2 = 1) x

theorem de_symC {N : ℕ} (hz : ∀ i, z i < N) : de (symC z x) N = deZ z := by
  unfold de deZ
  simp only [symC_dim]
  exact sum_range_fiber N z hz (fun k => k % 2 = 0) (fun _ => 1)

theorem dd_symC {N : ℕ} (hz : ∀ i, z i < N) : dd (symC z x) N = ddZ z := by
  unfold dd ddZ
  simp only [symC_dim]
  exact sum_range_fiber N z hz (fun k => k % 2 = 1) (fun _ => 1)

theorem finSupp_symC : FinSupp (symC z x) := ⟨bnd z, trivFrom_symC z x (lt_bnd z)⟩

theorem rkC_symC : rkC (symC z x) = n := by
  unfold rkC
  rw [stable_rk.cut_eq (trivFrom_symC z x (lt_bnd z)), rk_symC z x (lt_bnd z)]

theorem zsC_symC : zsC (symC z x) = ∑ i, z i := by
  unfold zsC
  rw [stable_zs.cut_eq (trivFrom_symC z x (lt_bnd z)), zs_symC z x (lt_bnd z)]

theorem statC_symC : statC (symC z x) = (evZ z x, odZ z x, deZ z, ddZ z) := by
  have h := trivFrom_symC z x (lt_bnd z)
  unfold statC evC odC deC ddC
  rw [stable_ev.cut_eq h, stable_od.cut_eq h, stable_de.cut_eq h, stable_dd.cut_eq h, ev_symC z x (lt_bnd z),
    od_symC z x (lt_bnd z), de_symC z x (lt_bnd z), dd_symC z x (lt_bnd z)]

/-- A symbol of the form `symC z x` lies in `symSet n (∑ z)`. -/
theorem symC_mem : symC z x ∈ symSet n (∑ i, z i) :=
  ⟨valid_symC z x, finSupp_symC z x, rkC_symC z x, zsC_symC z x⟩

end Stats

/-! ### The Hasse invariant of a diagonal form at an odd prime -/

/-- The Hilbert symbol `(p^a u, p^b v)` at an odd prime, as a unit: `ε^{ab} χ(u)^b χ(v)^a`. -/
def hp (e : ℤˣ) (a b : ℕ) (x y : ℤˣ) : ℤˣ := e ^ (a * b) * x ^ b * y ^ a

/-- The Hasse invariant of the diagonal form from the exponents and unit characters. -/
def hasseZ (e : ℤˣ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : ℤˣ :=
  ∏ i, ∏ j, if i < j then hp e (z i) (z j) (x i) (x j) else 1

theorem hasseZ_cons (e : ℤˣ) {n : ℕ} (a : ℕ) (z : Fin n → ℕ) (x0 : ℤˣ) (x : Fin n → ℤˣ) :
    hasseZ e (Fin.cons a z : Fin (n + 1) → ℕ) (Fin.cons x0 x : Fin (n + 1) → ℤˣ) =
      (∏ j, hp e a (z j) x0 (x j)) * hasseZ e z x := by
  unfold hasseZ
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]

theorem upow (u : ℤˣ) (k : ℕ) : u ^ k = if k % 2 = 0 then 1 else u := by
  rw [Int.units_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem sum_mod_two {n : ℕ} (z : Fin n → ℕ) : (∑ i, z i) % 2 = ddZ z % 2 := by
  rw [Finset.sum_nat_mod, ddZ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (z i) with h | h <;> simp [h]

theorem evZ_mul_odZ {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : evZ z x * odZ z x = ∏ i, x i := by
  unfold evZ odZ
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (z i) with h | h <;> simp [h]


/-- The closed form of the Hasse invariant. -/
def hclosed (e E O : ℤˣ) (D : ℕ) : ℤˣ := e ^ (D.choose 2) * (E * O) ^ D * O

theorem evZ_cons {n : ℕ} (a : ℕ) (z : Fin n → ℕ) (x0 : ℤˣ) (x : Fin n → ℤˣ) :
    evZ (Fin.cons a z : Fin (n + 1) → ℕ) (Fin.cons x0 x : Fin (n + 1) → ℤˣ) =
      (if a % 2 = 0 then x0 else 1) * evZ z x := by
  unfold evZ; rw [Fin.prod_univ_succ]; simp

theorem odZ_cons {n : ℕ} (a : ℕ) (z : Fin n → ℕ) (x0 : ℤˣ) (x : Fin n → ℤˣ) :
    odZ (Fin.cons a z : Fin (n + 1) → ℕ) (Fin.cons x0 x : Fin (n + 1) → ℤˣ) =
      (if a % 2 = 1 then x0 else 1) * odZ z x := by
  unfold odZ; rw [Fin.prod_univ_succ]; simp

theorem ddZ_cons {n : ℕ} (a : ℕ) (z : Fin n → ℕ) :
    ddZ (Fin.cons a z : Fin (n + 1) → ℕ) = (if a % 2 = 1 then 1 else 0) + ddZ z := by
  unfold ddZ; rw [Fin.sum_univ_succ]; simp

theorem step_alg (e x0 E O : ℤˣ) (a D S : ℕ) (hS : S % 2 = D % 2) :
    (e ^ (a * S) * x0 ^ S * (E * O) ^ a) * hclosed e E O D =
      hclosed e ((if a % 2 = 0 then x0 else 1) * E) ((if a % 2 = 1 then x0 else 1) * O)
        ((if a % 2 = 1 then 1 else 0) + D) := by
  unfold hclosed
  have e3 : x0 ^ S = x0 ^ D := by rw [upow, upow, hS]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · have h1 : ¬ (a % 2 = 1) := by omega
    have e1 : e ^ (a * S) = 1 := by rw [upow]; simp [Nat.mul_mod, ha]
    have e2 : (E * O) ^ a = 1 := by rw [upow]; simp [ha]
    simp only [ha, h1, if_true, if_false, e1, e2, e3, zero_add, one_mul, mul_pow, mul_one]
    apply Units.ext
    push_cast
    rcases Int.units_eq_one_or x0 with rfl | rfl <;> (simp only [Units.val_one, Units.val_neg]; ring_nf)
  · have h1 : ¬ (a % 2 = 0) := by omega
    have e1 : e ^ (a * S) = e ^ D := by rw [upow, upow]; simp [Nat.mul_mod, ha, hS]
    have e2 : (E * O) ^ a = E * O := by rw [upow]; simp [ha]
    have e4 : (1 + D).choose 2 = D + D.choose 2 := by
      rw [add_comm 1 D, Nat.choose_succ_succ' D 1]; simp
    simp only [ha, h1, if_true, if_false, e1, e2, e3, e4, one_mul, mul_pow]
    apply Units.ext
    push_cast
    rcases Int.units_eq_one_or x0 with rfl | rfl <;> (simp only [Units.val_one, Units.val_neg]; ring_nf)

theorem hasseZ_closed (e : ℤˣ) : ∀ {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ),
    hasseZ e z x = hclosed e (evZ z x) (odZ z x) (ddZ z) := by
  intro n
  induction n with
  | zero =>
    intro z x
    simp [hasseZ, hclosed, evZ, odZ, ddZ]
  | succ n ih =>
    intro z x
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail x, hasseZ_cons, evZ_cons, odZ_cons, ddZ_cons, ih,
      ← step_alg e _ _ _ _ _ (∑ i, Fin.tail z i) (by rw [sum_mod_two])]
    congr 1
    unfold hp
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow, ← Finset.mul_sum, evZ_mul_odZ]

end QuadFormsKB.Hanke2011Structure.RatOdd
