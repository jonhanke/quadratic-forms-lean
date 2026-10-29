/-
# O'Meara §73: the Hilbert symbol over $\mathbb Q_p$ and quadratic reciprocity (73:1, 73:3)

**Setting.** The Hilbert symbol $\big(\tfrac{a,b}{p}\big)$ over $\mathbb Q_p$ is `hilbertSymbol ℚ_[p] a b`, and the
local symbol of rationals at a place $v$ of $\mathbb Q$ is `RatPlace.hilbert v a b` (`QuadFormsKB/Defs/Hilbert.lean`).
The Legendre symbol $\big(\tfrac ap\big)$ is Mathlib's `legendreSym p a`.

**Proves**
* `hilbertSymbol_int_of_coprime`, `hilbertSymbol_int_prime` (**73:1**): for an odd prime $p$ and integers $a, b$
  prime to $p$, $\big(\tfrac{a,b}{p}\big) = 1$ and $\big(\tfrac{a,p}{p}\big) = \big(\tfrac ap\big)$;
* `quadratic_reciprocity_of_hilbert`, `legendreSym_neg_one_of_hilbert`, `legendreSym_two_of_hilbert` (**73:3**): the
  Quadratic Reciprocity Law $\big(\tfrac pq\big)\big(\tfrac qp\big) = (-1)^{\frac{p-1}2\frac{q-1}2}$ and its supplements
  $\big(\tfrac{-1}p\big) = (-1)^{\frac{p-1}2}$, $\big(\tfrac 2p\big) = (-1)^{\frac{p^2-1}8}$, derived as in the book from
  Hilbert's product formula $\prod_v \big(\tfrac{a,b}{v}\big) = 1$ (`hilbert_product_formula`) and the local formulas.

**Proof notes.** 73:1 is `HilbertLocal.hilbertSymbol_units` and the $p$-odd explicit formula
`HilbertLocal.hilbertSymbol_odd_formula`. For 73:3, the product formula is applied to $(p, q)$, $(-1, p)$, $(2, p)$; the
symbol is $1$ at $\infty$ (one entry is positive) and at every prime $\ell \notin \{2, p, q\}$ (73:1); at $2$ it is
computed by the dyadic formula `HilbertLocal.hilbertSymbol_two_formula` (O'Meara's 73:2), at $p$ and $q$ by 73:1.
*Caveat on independence:* in this library `hilbert_product_formula` over $\mathbb Q$ is itself proved from the explicit
local formulas and Mathlib's quadratic reciprocity, so the derivation here follows O'Meara's route but is not an
independent proof of quadratic reciprocity; it checks that the book's deduction is correct.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity

namespace QuadFormsKB.OMeara

open QuadFormsKB RatPlace

section Sec73

/-- An integer prime to $p$ is a $p$-adic unit. -/
private theorem exists_unit_eq_int (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    ∃ u : ℤ_[p]ˣ, (u : ℤ_[p]) = m := by
  have h1 : ‖(m : ℤ_[p])‖ = 1 := by
    have := PadicInt.norm_le_one (m : ℤ_[p])
    have h2 := (PadicInt.norm_int_lt_one_iff_dvd m).not.2 hm
    push Not at h2; linarith
  exact ⟨(PadicInt.isUnit_iff.2 h1).unit, rfl⟩

/-- **Proposition 73:1, first formula** (O'Meara 1963, p. 206): for an odd prime $p$ and rational integers $a, b$
prime to $p$, the Hilbert symbol over $\mathbb Q_p$ is $\big(\tfrac{a,b}{p}\big) = 1$. -/
@[kb "omeara1963" "§73, 73:1, p. 206 ((a,b/p) = 1)"]
theorem hilbertSymbol_int_of_coprime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) : hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = 1 := by
  obtain ⟨u, hu⟩ := exists_unit_eq_int p a ha
  obtain ⟨v, hv⟩ := exists_unit_eq_int p b hb
  have := HilbertLocal.hilbertSymbol_units hp2 u v
  rw [hu, hv] at this
  exact_mod_cast this

/-- **Proposition 73:1, second formula** (O'Meara 1963, p. 206): for an odd prime $p$ and a rational integer $a$
prime to $p$, $\big(\tfrac{a,p}{p}\big) = \big(\tfrac ap\big)$, the Legendre symbol. -/
@[kb "omeara1963" "§73, 73:1, p. 206 ((a,p/p) = (a/p))"]
theorem hilbertSymbol_int_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    hilbertSymbol ℚ_[p] (a : ℚ_[p]) (p : ℚ_[p]) = legendreSym p a := by
  obtain ⟨u, hu⟩ := exists_unit_eq_int p a ha
  have h := HilbertLocal.hilbertSymbol_odd_formula hp2 0 1 u 1
  simp only [pow_zero, one_mul, pow_one, Units.val_one, PadicInt.coe_one, mul_one, zero_mul] at h
  have h' : ((u : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) := by rw [hu]; push_cast; rfl
  rw [h'] at h
  rw [h]
  simp [HilbertLocal.unitChar, hu, map_intCast]
  rfl

/-! ### Local symbols at the places of $\mathbb Q$ -/

private theorem hilbert_pm (v : RatPlace) (a b : ℚ) : v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
  cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp

/-- The product formula, as a finite product: if $s$ contains every place where $(a,b)_v \ne 1$, then
$\prod_{v \in s}(a,b)_v = 1$. -/
private theorem prod_hilbert_eq_one (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (s : Finset RatPlace)
    (hs : ∀ v ∉ s, v.hilbert a b = 1) : ∏ v ∈ s, v.hilbert a b = 1 := by
  classical
  obtain ⟨hfin, heven⟩ := hilbert_product_formula a b ha hb
  have hsub : hfin.toFinset ⊆ s := by
    intro v hv
    by_contra hvs
    have h1 := hs v hvs
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    rw [h1] at hv; norm_num at hv
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ v ∈ s \ hfin.toFinset, v.hilbert a b = 1 := by
    refine Finset.prod_eq_one fun v hv => ?_
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    exact (hilbert_pm v a b).resolve_right hv.2
  have h2 : ∏ v ∈ hfin.toFinset, v.hilbert a b = (-1) ^ hfin.toFinset.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun v hv => by simpa using hv
  rw [h1, h2, one_mul, ← Set.ncard_eq_toFinset_card _ hfin]
  exact heven.neg_one_pow

private theorem hilbert_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (α β : ℕ) (m n : ℤ) (x y : ℚ)
    (hm : ¬ (p : ℤ) ∣ m) (hn : ¬ (p : ℤ) ∣ n) (hx : x = (p : ℚ) ^ α * m) (hy : y = (p : ℚ) ^ β * n) :
    (RatPlace.finite ⟨p, hp.out⟩).hilbert x y =
      (-1) ^ (α * β * ((p - 1) / 2)) * legendreSym p m ^ β * legendreSym p n ^ α := by
  obtain ⟨u, hu⟩ := exists_unit_eq_int p m hm
  obtain ⟨v, hv⟩ := exists_unit_eq_int p n hn
  have hx' : ((x : ℚ) : ℚ_[p]) = (p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]) := by
    rw [hu, hx]; push_cast; rfl
  have hy' : ((y : ℚ) : ℚ_[p]) = (p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p]) := by
    rw [hv, hy]; push_cast; rfl
  show hilbertSymbol ℚ_[p] (x : ℚ_[p]) (y : ℚ_[p]) = _
  rw [hx', hy', HilbertLocal.hilbertSymbol_odd_formula hp2]
  simp only [HilbertLocal.unitChar, hu, hv, map_intCast]
  rfl

private theorem hilbert_two (α β : ℕ) (m n : ℤ) (x y : ℚ) (hm : ¬ (2 : ℤ) ∣ m) (hn : ¬ (2 : ℤ) ∣ n)
    (hx : x = (2 : ℚ) ^ α * m) (hy : y = (2 : ℚ) ^ β * n) :
    (RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert x y = (-1) ^
      (HilbertLocal.twoEps (m : ZMod (2 ^ 3)) * HilbertLocal.twoEps (n : ZMod (2 ^ 3)) +
        α * HilbertLocal.twoOmega (n : ZMod (2 ^ 3)) + β * HilbertLocal.twoOmega (m : ZMod (2 ^ 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_unit_eq_int 2 m (by exact_mod_cast hm)
  obtain ⟨v, hv⟩ := exists_unit_eq_int 2 n (by exact_mod_cast hn)
  have hx' : ((x : ℚ) : ℚ_[2]) = (2 : ℚ_[2]) ^ α * ((u : ℤ_[2]) : ℚ_[2]) := by
    rw [hu, hx]; push_cast; rfl
  have hy' : ((y : ℚ) : ℚ_[2]) = (2 : ℚ_[2]) ^ β * ((v : ℤ_[2]) : ℚ_[2]) := by
    rw [hv, hy]; push_cast; rfl
  show hilbertSymbol ℚ_[2] (x : ℚ_[2]) (y : ℚ_[2]) = _
  rw [hx', hy', HilbertLocal.hilbertSymbol_two_formula]
  simp only [hu, hv, map_intCast]

private theorem hilbert_inf (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : 0 < y) :
    RatPlace.infinite.hilbert x y = 1 := by
  rcases hilbert_pm RatPlace.infinite x y with h | h
  · exact h
  · exfalso
    have := (hilbertSymbol_real (x : ℝ) (y : ℝ) (by exact_mod_cast hx) (by exact_mod_cast hy)).1 h
    have h2 : y < 0 := by exact_mod_cast this.2
    linarith

/-- Outside a finite set containing $\infty$, $2$ and the primes dividing $x, y$, the symbol is $1$. -/
private theorem hilbert_out (x y : ℚ) (s : Finset RatPlace) (hx : x ≠ 0) (hy : y ≠ 0)
    (h2 : RatPlace.finite ⟨2, Nat.prime_two⟩ ∈ s) (hinf : RatPlace.infinite ∈ s)
    (hval : ∀ ℓ : Nat.Primes, RatPlace.finite ℓ ∉ s → padicValRat ℓ x = 0 ∧ padicValRat ℓ y = 0) :
    ∀ v ∉ s, v.hilbert x y = 1 := by
  intro v hvs
  cases v with
  | infinite => exact absurd hinf hvs
  | finite ℓ =>
    obtain ⟨hx0, hy0⟩ := hval ℓ hvs
    have : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
    have hl2 : (ℓ : ℕ) ≠ 2 := by
      intro h; apply hvs
      have : ℓ = ⟨2, Nat.prime_two⟩ := Subtype.ext h
      rw [this]; exact h2
    exact HilbertLocal.hilbert_eq_one_of_padicValRat hl2 x y hx hy hx0 hy0

private theorem padicValRat_prime_eq_zero {ℓ p : ℕ} (hp : p.Prime) (hl : ℓ.Prime) (hlp : ℓ ≠ p) :
    padicValRat ℓ (p : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  have : ¬ ℓ ∣ p := fun h => hlp ((Nat.prime_dvd_prime_iff_eq hl hp).1 h)
  simp [padicValNat.eq_zero_of_not_dvd this]

private theorem ne_of_mem_not_mem {ℓ : Nat.Primes} {s : Finset RatPlace} {p : ℕ} (hp : p.Prime)
    (h1 : RatPlace.finite ⟨p, hp⟩ ∈ s) (h2 : RatPlace.finite ℓ ∉ s) : (ℓ : ℕ) ≠ p := by
  intro h; apply h2
  have : ℓ = ⟨p, hp⟩ := Subtype.ext h
  rw [this]; exact h1

private theorem place_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    RatPlace.finite ⟨p, hp⟩ ≠ RatPlace.finite ⟨q, hq⟩ := by
  intro e; injection e with e'; exact h (congrArg Subtype.val e')

private theorem not_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : ¬ (p : ℤ) ∣ (q : ℤ) :=
  fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 h))

private theorem not_dvd_one' {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ (1 : ℤ) :=
  fun h => hp.not_dvd_one (by exact_mod_cast h)

private theorem not_dvd_neg_one {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ (-1 : ℤ) := by
  intro h; rw [Int.dvd_neg] at h; exact hp.not_dvd_one (by exact_mod_cast h)

private theorem twoEps_nat (p : ℕ) (hp : p % 2 = 1) :
    HilbertLocal.twoEps ((p : ℤ) : ZMod (2 ^ 3)) = ((p - 1) / 2) % 2 := by
  have h8 : ((p : ℤ) : ZMod (2 ^ 3)) = ((p % 8 : ℕ) : ZMod (2 ^ 3)) := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_mod p (2 ^ 3)).symm
  rw [h8]
  rcases (by omega : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7) with h | h | h | h <;>
    rw [h] <;> [rw [show (p - 1) / 2 % 2 = 0 by omega]; rw [show (p - 1) / 2 % 2 = 1 by omega];
      rw [show (p - 1) / 2 % 2 = 0 by omega]; rw [show (p - 1) / 2 % 2 = 1 by omega]] <;> decide

private theorem twoOmega_nat (p : ℕ) (hp : p % 2 = 1) :
    HilbertLocal.twoOmega ((p : ℤ) : ZMod (2 ^ 3)) % 2 = ((p ^ 2 - 1) / 8) % 2 := by
  have h8 : ((p : ℤ) : ZMod (2 ^ 3)) = ((p % 8 : ℕ) : ZMod (2 ^ 3)) := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_mod p (2 ^ 3)).symm
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 8 ∧ p = 8 * k + r := ⟨p / 8, p % 8, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod p 8).symm⟩
  have hr1 : r % 2 = 1 := by omega
  have hmod : (8 * k + r) % 8 = r := by omega
  rw [h8, hmod]
  have hsq : (8 * k + r) ^ 2 - 1 = 8 * (8 * (k * k) + 2 * (r * k)) + (r ^ 2 - 1) := by
    have : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : 1 ≤ (8 * k + r) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [*]; ring
  rw [hsq, Nat.mul_add_div (by norm_num : 0 < 8)]
  have hw : HilbertLocal.twoOmega ((r : ℕ) : ZMod (2 ^ 3)) = (r ^ 2 - 1) / 8 % 2 := by
    interval_cases r <;> first | omega | decide
  rw [hw]
  omega

private theorem neg_one_pow_mod_two (n : ℕ) : (-1 : ℤ) ^ n = (-1) ^ (n % 2) := neg_one_pow_eq_pow_mod_two n

/-- **Theorem 73:3, the Quadratic Reciprocity Law** (O'Meara 1963, p. 207), derived from Hilbert's reciprocity law
$\prod_v \big(\tfrac{p,q}{v}\big) = 1$ as in the book: for distinct odd primes $p, q$,
$$\Big(\frac pq\Big)\Big(\frac qp\Big) = (-1)^{\frac{p-1}2 \cdot \frac{q-1}2}.$$
(See the module docstring for the independence caveat.) -/
@[kb "omeara1963" "§73, 73:3, p. 207 (quadratic reciprocity, from Hilbert reciprocity)"]
theorem quadratic_reciprocity_of_hilbert {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  classical
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  have hqodd : q % 2 = 1 := Nat.odd_iff.1 (hq.out.odd_of_ne_two hq2)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  set s : Finset RatPlace := {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩,
    RatPlace.finite ⟨p, hp.out⟩, RatPlace.finite ⟨q, hq.out⟩} with hs
  have H := prod_hilbert_eq_one p q hp0 hq0 s (hilbert_out p q s hp0 hq0 (by simp [hs]) (by simp [hs])
    fun ℓ hℓ => ⟨padicValRat_prime_eq_zero hp.out ℓ.2 (ne_of_mem_not_mem hp.out (by simp [hs]) hℓ),
      padicValRat_prime_eq_zero hq.out ℓ.2 (ne_of_mem_not_mem hq.out (by simp [hs]) hℓ)⟩)
  rw [hs, Finset.prod_insert (by simp), Finset.prod_insert (by simp [place_ne Nat.prime_two hp.out (Ne.symm hp2),
      place_ne Nat.prime_two hq.out (Ne.symm hq2)]),
    Finset.prod_insert (by simp [place_ne hp.out hq.out hpq]), Finset.prod_singleton] at H
  rw [hilbert_inf _ _ hp0 hq0 (by exact_mod_cast hq.out.pos),
    hilbert_two 0 0 p q p q (by omega) (by omega) (by simp) (by simp),
    hilbert_odd p hp2 1 0 1 q p q (not_dvd_one' hp.out) (not_dvd_prime hp.out hq.out hpq) (by simp) (by simp),
    hilbert_odd q hq2 0 1 p 1 p q (not_dvd_prime hq.out hp.out (Ne.symm hpq)) (not_dvd_one' hq.out) (by simp)
      (by simp)] at H
  simp only [twoEps_nat p hpodd, twoEps_nat q hqodd, zero_mul, mul_zero, add_zero, pow_one, pow_zero,
    legendreSym.at_one, one_mul, mul_one] at H
  have hsq : ∀ n : ℕ, (-1 : ℤ) ^ n * (-1) ^ n = 1 := fun n => by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [neg_one_pow_mod_two ((p - 1) / 2 * ((q - 1) / 2)), Nat.mul_mod]
  calc legendreSym q p * legendreSym p q
      = (-1) ^ ((p - 1) / 2 % 2 * ((q - 1) / 2 % 2)) * ((-1) ^ ((p - 1) / 2 % 2 * ((q - 1) / 2 % 2)) *
          (legendreSym p q * legendreSym q p)) := by rw [← mul_assoc, hsq, one_mul, mul_comm]
    _ = (-1) ^ ((p - 1) / 2 % 2 * ((q - 1) / 2 % 2) % 2) := by
        rw [H, mul_one, ← neg_one_pow_mod_two]

/-- **Theorem 73:3, first supplement** (O'Meara 1963, p. 207), from $\prod_v \big(\tfrac{-1,p}{v}\big) = 1$: for an
odd prime $p$, $\big(\tfrac{-1}p\big) = (-1)^{\frac{p-1}2}$. -/
@[kb "omeara1963" "§73, 73:3, p. 207 (first supplement, from Hilbert reciprocity)"]
theorem legendreSym_neg_one_of_hilbert {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (-1) = (-1) ^ ((p - 1) / 2) := by
  classical
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set s : Finset RatPlace := {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩,
    RatPlace.finite ⟨p, hp.out⟩} with hs
  have H := prod_hilbert_eq_one (-1) p (by norm_num) hp0 s (hilbert_out (-1) p s (by norm_num) hp0 (by simp [hs])
    (by simp [hs]) fun ℓ hℓ => ⟨by simp,
      padicValRat_prime_eq_zero hp.out ℓ.2 (ne_of_mem_not_mem hp.out (by simp [hs]) hℓ)⟩)
  rw [hs, Finset.prod_insert (by simp), Finset.prod_insert (by simp [place_ne Nat.prime_two hp.out (Ne.symm hp2)]),
    Finset.prod_singleton] at H
  rw [hilbert_inf _ _ (by norm_num) hp0 (by exact_mod_cast hp.out.pos),
    hilbert_two 0 0 (-1) p (-1) p (by decide) (by omega) (by simp) (by simp),
    hilbert_odd p hp2 0 1 (-1) 1 (-1) p (not_dvd_neg_one hp.out) (not_dvd_one' hp.out) (by simp) (by simp)] at H
  have h7 : HilbertLocal.twoEps ((-1 : ℤ) : ZMod (2 ^ 3)) = 1 := by decide
  simp only [twoEps_nat p hpodd, h7, one_mul, zero_mul, add_zero, pow_zero, pow_one, legendreSym.at_one,
    mul_one] at H
  have hsq : ∀ n : ℕ, (-1 : ℤ) ^ n * (-1) ^ n = 1 := fun n => by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [neg_one_pow_mod_two]
  calc legendreSym p (-1) = (-1) ^ ((p - 1) / 2 % 2) * ((-1) ^ ((p - 1) / 2 % 2) * legendreSym p (-1)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = _ := by rw [H, mul_one]

/-- **Theorem 73:3, second supplement** (O'Meara 1963, p. 207), from $\prod_v \big(\tfrac{2,p}{v}\big) = 1$: for an
odd prime $p$, $\big(\tfrac 2p\big) = (-1)^{\frac{p^2-1}8}$. -/
@[kb "omeara1963" "§73, 73:3, p. 207 (second supplement, from Hilbert reciprocity)"]
theorem legendreSym_two_of_hilbert {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  classical
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set s : Finset RatPlace := {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩,
    RatPlace.finite ⟨p, hp.out⟩} with hs
  have H := prod_hilbert_eq_one 2 p (by norm_num) hp0 s (hilbert_out 2 p s (by norm_num) hp0 (by simp [hs])
    (by simp [hs]) fun ℓ hℓ =>
      ⟨by
          have h := padicValRat_prime_eq_zero Nat.prime_two ℓ.2 (ne_of_mem_not_mem Nat.prime_two (by simp [hs]) hℓ)
          exact_mod_cast h,
        padicValRat_prime_eq_zero hp.out ℓ.2 (ne_of_mem_not_mem hp.out (by simp [hs]) hℓ)⟩)
  rw [hs, Finset.prod_insert (by simp), Finset.prod_insert (by simp [place_ne Nat.prime_two hp.out (Ne.symm hp2)]),
    Finset.prod_singleton] at H
  rw [hilbert_inf _ _ (by norm_num) hp0 (by exact_mod_cast hp.out.pos),
    hilbert_two 1 0 1 p 2 p (by decide) (by omega) (by simp) (by simp),
    hilbert_odd p hp2 0 1 2 1 2 p (not_dvd_prime hp.out Nat.prime_two hp2) (not_dvd_one' hp.out) (by simp)
      (by simp)] at H
  have h7 : HilbertLocal.twoEps ((1 : ℤ) : ZMod (2 ^ 3)) = 0 := by decide
  simp only [h7, zero_mul, zero_add, one_mul, add_zero, pow_one, pow_zero, legendreSym.at_one, mul_one] at H
  have hsq : ∀ n : ℕ, (-1 : ℤ) ^ n * (-1) ^ n = 1 := fun n => by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [neg_one_pow_mod_two, ← twoOmega_nat p hpodd, ← neg_one_pow_mod_two]
  set w := HilbertLocal.twoOmega ((p : ℤ) : ZMod (2 ^ 3))
  calc legendreSym p 2 = (-1) ^ w * ((-1) ^ w * legendreSym p 2) := by rw [← mul_assoc, hsq, one_mul]
    _ = _ := by rw [H, mul_one]

end Sec73

end QuadFormsKB.OMeara
