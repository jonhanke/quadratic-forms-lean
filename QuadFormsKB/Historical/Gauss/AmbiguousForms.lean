import QuadFormsKB.Historical.Gauss.Forms
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Properly primitive forms $(A, 0, C)$ and $(2B, B, C)$ of given determinant (*Disquisitiones Arithmeticae*, Art. 257)

Gauss's $(a, b, c)$ is the form $a x^2 + 2 b x y + c y^2$ (`gaussForm`) of determinant $b^2 - ac$ (`gaussDet`).
This file counts, for a nonzero determinant $D$, the properly primitive forms of the two shapes that occur in
Gauss's list of ambiguous forms:

* the historical sources, Art. 257 I: `ncard_properlyPrimitive_A0C`, the forms $(A, 0, C)$: exactly
  $2^{\omega(|D|)+1}$ of them;
* the historical sources, Art. 257 II: the forms $(2B, B, C)$: `properlyPrimitive_2BBC_eq_empty` (none unless
  $D \equiv 3 \pmod 4$ or $D \equiv 0 \pmod 8$), `ncard_properlyPrimitive_2BBC_of_mod_four`
  ($D \equiv 3 \pmod 4$: $2^{n+1}$) and `ncard_properlyPrimitive_2BBC_of_mod_eight`
  ($D \equiv 0 \pmod 8$: $2^{n+2}$), $n$ = number of odd primes dividing $D$.

Supporting: the number of (signed) unitary divisors, `ncard_signedUnitaryDivisors`: for $D \ne 0$ there are
$2^{\omega(|D|)+1}$ integers $A \mid D$ with $\gcd(A, D/A) = 1$. All results are unconditional.
-/

open Finset

namespace QuadFormsKB.Historical.Gauss

/-- The **unitary divisors** of $N$: the divisors $d$ of $N$ with $\gcd(d, N/d) = 1$. -/
def unitaryDivisors (N : ℕ) : Finset ℕ := N.divisors.filter fun d => Nat.Coprime d (N / d)

theorem mem_unitaryDivisors {N d : ℕ} :
    d ∈ unitaryDivisors N ↔ (d ∣ N ∧ N ≠ 0) ∧ Nat.Coprime d (N / d) := by
  rw [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]

theorem unitary_iff {N d : ℕ} (hN : N ≠ 0) (hd : d ∣ N) :
    Nat.Coprime d (N / d) ↔ ∀ p ∈ d.primeFactors, d.factorization p = N.factorization p := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hN
  have he0 : e ≠ 0 := right_ne_zero_of_mul hN
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  constructor
  · intro hc p hp
    have hpd := (Nat.mem_primeFactors.1 hp)
    have : ¬ p ∣ e := fun h => hpd.1.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hpd.2.1 h)
    rw [Nat.factorization_mul hd0 he0]
    simp [Nat.factorization_eq_zero_of_not_dvd this]
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpd hpe
    have h1 := h p (Nat.mem_primeFactors.2 ⟨hp, hpd, hd0⟩)
    rw [Nat.factorization_mul hd0 he0] at h1
    have h2 := hp.factorization_pos_of_dvd he0 hpe
    simp at h1
    omega

/-- **The unitary divisors of $N \ge 1$ number $2^{\omega(N)}$**, where $\omega(N)$ is the number of distinct
primes dividing $N$: $S \mapsto \prod_{p \in S} p^{v_p(N)}$ is a bijection from the subsets of the prime factors
of $N$ to the unitary divisors. -/
theorem card_unitaryDivisors {N : ℕ} (hN : N ≠ 0) :
    (unitaryDivisors N).card = 2 ^ N.primeFactors.card := by
  rw [← Finset.card_powerset]
  have hprod : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    have := Nat.prod_factorization_pow_eq_self hN
    simpa [Finsupp.prod, Nat.support_factorization] using this
  have hpr : ∀ S ⊆ N.primeFactors, ∀ q ∈ S, q.Prime := fun S hS q hq =>
    Nat.prime_of_mem_primeFactors (hS hq)
  have hg_ne : ∀ S ⊆ N.primeFactors, ∏ p ∈ S, p ^ N.factorization p ≠ 0 := fun S hS =>
    prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hpr S hS p hp).ne_zero
  have hg_pf : ∀ S ⊆ N.primeFactors, (∏ p ∈ S, p ^ N.factorization p).primeFactors = S := by
    intro S hS
    ext p
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, -⟩
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp (hpr S hS q hq)).1 (hp.dvd_of_dvd_pow hpq)
      rwa [this]
    · intro hp
      have hk : N.factorization p ≠ 0 := by
        have := hS hp
        rw [← Nat.support_factorization, Finsupp.mem_support_iff] at this
        exact this
      exact ⟨hpr S hS p hp, (dvd_pow_self p hk).trans (dvd_prod_of_mem _ hp), hg_ne S hS⟩
  have hg_fact : ∀ S ⊆ N.primeFactors, ∀ p ∈ S,
      (∏ q ∈ S, q ^ N.factorization q).factorization p = N.factorization p := by
    intro S hS p hp
    rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (hpr S hS q hq).ne_zero)]
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single p]
    · rw [(hpr S hS p hp).factorization_pow]; simp
    · intro q hq hqp
      rw [(hpr S hS q hq).factorization_pow]
      simp [Finsupp.single_apply, Ne.symm hqp]
    · intro h; exact absurd hp h
  have hg_dvd : ∀ S ⊆ N.primeFactors, (∏ p ∈ S, p ^ N.factorization p) ∣ N := by
    intro S hS
    calc (∏ p ∈ S, p ^ N.factorization p) ∣ ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
          prod_dvd_prod_of_subset _ _ _ hS
      _ = N := hprod
  apply Finset.card_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p ^ N.factorization p)
  · intro d hd
    simp only [Finset.mem_coe, mem_unitaryDivisors] at hd
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact Nat.primeFactors_mono hd.1.1 hN
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powerset] at hS
    simp only [Finset.mem_coe, mem_unitaryDivisors]
    refine ⟨⟨hg_dvd S hS, hN⟩, ?_⟩
    rw [unitary_iff hN (hg_dvd S hS), hg_pf S hS]
    exact hg_fact S hS
  · intro d hd
    simp only [Finset.mem_coe, mem_unitaryDivisors] at hd
    have hd0 : d ≠ 0 := fun h => hN (by simpa [h] using hd.1.1)
    have h := (unitary_iff hN hd.1.1).1 hd.2
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hd0]
    simp only [Finsupp.prod, Nat.support_factorization]
    exact prod_congr rfl fun p hp => by rw [h p hp]
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powerset] at hS
    exact hg_pf S hS


theorem isCoprime_iff_forall_dvd (a c : ℤ) :
    IsCoprime a c ↔ ∀ d : ℤ, d ∣ a → d ∣ c → IsUnit d := by
  constructor
  · rintro ⟨u, v, e⟩ d ha hc
    exact isUnit_of_dvd_one (e ▸ dvd_add (Dvd.dvd.mul_left ha u) (Dvd.dvd.mul_left hc v))
  · intro H
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h := H (Int.gcd a c) (Int.gcd_dvd_left a c) (Int.gcd_dvd_right a c)
    rw [Int.isUnit_iff_natAbs_eq] at h
    simpa using h

/-- The **signed unitary divisors** of $D$: the integers $A \mid D$ with $\gcd(A, D/A) = 1$. -/
def signedUnitaryDivisors (D : ℤ) : Set ℤ := {A | A ∣ D ∧ IsCoprime A (D / A)}

theorem mem_signedUnitaryDivisors_iff {D : ℤ} (hD : D ≠ 0) (A : ℤ) :
    A ∈ signedUnitaryDivisors D ↔ A.natAbs ∈ unitaryDivisors D.natAbs := by
  simp only [signedUnitaryDivisors, Set.mem_setOf_eq, unitaryDivisors, Finset.mem_filter,
    Nat.mem_divisors]
  constructor
  · rintro ⟨hA, hc⟩
    refine ⟨⟨Int.natAbs_dvd_natAbs.2 hA, Int.natAbs_ne_zero.2 hD⟩, ?_⟩
    rw [← Int.natAbs_ediv_of_dvd hA]
    exact Int.isCoprime_iff_gcd_eq_one.1 hc
  · rintro ⟨⟨hA, -⟩, hc⟩
    have hA' : A ∣ D := Int.natAbs_dvd_natAbs.1 hA
    refine ⟨hA', Int.isCoprime_iff_gcd_eq_one.2 ?_⟩
    rw [Int.gcd, Int.natAbs_ediv_of_dvd hA']
    exact hc

theorem signedUnitaryDivisors_eq {D : ℤ} (hD : D ≠ 0) :
    signedUnitaryDivisors D =
      ↑((unitaryDivisors D.natAbs).image (fun d : ℕ => (d : ℤ)) ∪
        (unitaryDivisors D.natAbs).image (fun d : ℕ => -(d : ℤ))) := by
  ext A
  rw [mem_signedUnitaryDivisors_iff hD]
  simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe]
  constructor
  · intro h
    rcases Int.natAbs_eq A with h' | h'
    · exact Or.inl ⟨A.natAbs, h, h'.symm⟩
    · exact Or.inr ⟨A.natAbs, h, by rw [h']; simp⟩
  · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩) <;> simpa using hd

/-- **Number of signed unitary divisors:** for $D \ne 0$ there are exactly $2^{\omega(|D|) + 1}$ integers
$A \mid D$ with $\gcd(A, D/A) = 1$ ($\omega$ = number of distinct prime divisors). -/
theorem ncard_signedUnitaryDivisors {D : ℤ} (hD : D ≠ 0) :
    (signedUnitaryDivisors D).ncard = 2 ^ (D.natAbs.primeFactors.card + 1) := by
  have hN : D.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hD
  rw [signedUnitaryDivisors_eq hD, Set.ncard_coe_finset, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ Nat.cast_injective,
    Finset.card_image_of_injective (f := fun d : ℕ => -(d : ℤ)) _
      (fun a b h => Nat.cast_injective (neg_injective h)),
    card_unitaryDivisors hN]
  · ring
  · rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨d, hd, rfl⟩ := h1
    obtain ⟨e, he, hde⟩ := h2
    simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors] at hd he
    have hd0 : d ≠ 0 := fun h => hN (by simpa [h] using hd.1.1)
    omega

/-- **Primitivity of $(a, b, c)$ in elementary terms:** $(a, b, c)$ is properly primitive iff every common divisor
of $a$, $2b$, $c$ is a unit (*Disq. Arith.* Art. 226). -/
theorem gaussForm_isPrimitive_iff (a b c : ℤ) :
    (gaussForm a b c).IsPrimitive ↔ ∀ d : ℤ, d ∣ a → d ∣ 2 * b → d ∣ c → IsUnit d :=
  Iff.rfl

/-- $(A, 0, C)$ is properly primitive iff $\gcd(A, C) = 1$. -/
theorem isPrimitive_gaussForm_zero_iff (A C : ℤ) : (gaussForm A 0 C).IsPrimitive ↔ IsCoprime A C := by
  rw [isCoprime_iff_forall_dvd, gaussForm_isPrimitive_iff]
  constructor
  · intro H d h1 h3
    exact H d h1 (by simp) h3
  · intro H d h1 _ h3
    exact H d h1 h3

/-- $(2B, B, C)$ is properly primitive iff $\gcd(2B, C) = 1$. -/
theorem isPrimitive_gaussForm_two_mul_iff (B C : ℤ) :
    (gaussForm (2 * B) B C).IsPrimitive ↔ IsCoprime (2 * B) C := by
  rw [isCoprime_iff_forall_dvd, gaussForm_isPrimitive_iff]
  constructor
  · intro H d h1 h3
    exact H d h1 h1 h3
  · intro H d h1 _ h3
    exact H d h1 h3

theorem isCoprime_sub_self {B X : ℤ} (h : IsCoprime B X) : IsCoprime B (B - X) := by
  obtain ⟨u, v, e⟩ := h
  exact ⟨u + v, -v, by linear_combination e⟩

theorem isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime 2 n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨-k, 1, by ring⟩

theorem odd_of_isCoprime_two_mul {B C : ℤ} (h : IsCoprime (2 * B) C) : Odd C := by
  rcases Int.even_or_odd C with he | ho
  · exfalso
    have hu := (isCoprime_iff_forall_dvd _ _).1 h 2 (dvd_mul_right 2 B) (even_iff_two_dvd.1 he)
    have := Int.isUnit_iff.1 hu
    omega
  · exact ho

/-- **Parity analysis for $(2B, B, C)$:** if $\gcd(2B, C) = 1$ and $B^2 - 2BC = D$, then either $B$ is odd and
$D \equiv 3 \pmod 4$, or $B = 2k$ is even and $D \equiv 0 \pmod 8$. -/
theorem parity_two_mul {B C D : ℤ} (h : IsCoprime (2 * B) C) (hD : B ^ 2 - 2 * B * C = D) :
    (Odd B ∧ D % 4 = 3) ∨ (∃ k, B = 2 * k ∧ D % 8 = 0) := by
  obtain ⟨m, hm⟩ := odd_of_isCoprime_two_mul h
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' B
  · right
    refine ⟨k, hk, ?_⟩
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
    · have : D = 8 * (j * (2 * j - C)) := by rw [← hD, hk, hj]; ring
      omega
    · have : D = 8 * ((2 * j + 1) * (j - m)) := by rw [← hD, hk, hj, hm]; ring
      omega
  · left
    refine ⟨⟨k, hk⟩, ?_⟩
    have : D = 4 * (k ^ 2 - 2 * k * m - m) - 1 := by rw [← hD, hk, hm]; ring
    omega

/-- **Number of odd primes versus all primes** for $N$ odd. -/
theorem card_filter_odd_primeFactors_of_odd {D : ℤ} (h : D % 2 = 1) :
    (D.natAbs.primeFactors.filter Odd).card = D.natAbs.primeFactors.card := by
  congr 1
  apply Finset.filter_true_of_mem
  intro p hp
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.1 hp
  rcases hpp.eq_two_or_odd' with rfl | ho
  · exfalso
    omega
  · exact ho

/-- **Odd primes of $4m$ for $m$ even:** $\omega(|m|) = 1 + \#\{\text{odd primes dividing } 4m\}$. -/
theorem card_primeFactors_eq_of_even {m : ℤ} (hm : m ≠ 0) (he : m % 2 = 0) :
    m.natAbs.primeFactors.card = ((4 * m).natAbs.primeFactors.filter Odd).card + 1 := by
  have hne : m.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hm
  have h2 : 2 ∈ m.natAbs.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, by omega, hne⟩
  have hpf : (4 * m).natAbs.primeFactors = m.natAbs.primeFactors := by
    rw [Int.natAbs_mul, Nat.primeFactors_mul (by simp) hne]
    apply Finset.union_eq_right.2
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.1 hp
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
      (hpp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hpd))
    rwa [this]
  rw [hpf, ← Finset.card_insert_of_notMem (a := 2) (by simp)]
  congr 1
  ext p
  simp only [Finset.mem_insert, Finset.mem_filter]
  constructor
  · intro hp
    obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.1 hp
    rcases hpp.eq_two_or_odd' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩
  · rintro (rfl | ⟨hp, -⟩)
    · exact h2
    · exact hp

/-- **Art. 257 I: the properly primitive forms $(A, 0, C)$ of determinant $D$** (the historical sources,
*Disq. Arith.* Art. 257). For $D \ne 0$ the forms $(A, 0, C)$ that are properly primitive
($\gcd(A, 2\cdot 0, C) = \gcd(A, C) = 1$) with determinant $0^2 - AC = D$ are obtained by taking for $A$ every signed
divisor of $D$ with $C = -D/A$ prime to $A$; with $n$ distinct primes dividing $D$ (counting $2$), there are exactly
$2^{n+1}$ of them. Here $n = \omega(|D|)$ is `D.natAbs.primeFactors.card`; the factor $2$ is the sign of $A$.

Proved unconditionally: the set of pairs $(A, C) \in \mathbb{Z}^2$ with $(A, 0, C)$ properly primitive and determinant $D$
has $2^{\omega(|D|)+1}$ elements, via the bijection $(A, C) \mapsto A$ onto `signedUnitaryDivisors D`.
Nothing differs from the source. -/
@[kb "gauss1801" "Art. 257 I"]
theorem ncard_properlyPrimitive_A0C {D : ℤ} (hD : D ≠ 0) :
    {p : ℤ × ℤ | (gaussForm p.1 0 p.2).IsPrimitive ∧ gaussDet p.1 0 p.2 = D}.ncard =
      2 ^ (D.natAbs.primeFactors.card + 1) := by
  rw [← ncard_signedUnitaryDivisors hD]
  have key : ∀ A C : ℤ, gaussDet A 0 C = D → A ≠ 0 ∧ D = A * -C := by
    intro A C h
    have h' : 0 ^ 2 - A * C = D := h
    refine ⟨?_, by linarith⟩
    rintro rfl
    apply hD
    rw [← h']
    ring
  apply Set.ncard_congr (fun p _ => p.1)
  · rintro ⟨A, C⟩ ⟨h1, h2⟩
    obtain ⟨hA, hDe⟩ := key A C h2
    rw [isPrimitive_gaussForm_zero_iff] at h1
    refine ⟨⟨-C, hDe⟩, ?_⟩
    rw [Int.ediv_eq_of_eq_mul_right hA hDe]
    exact h1.neg_right
  · rintro ⟨A, C⟩ ⟨A', C'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩ (heq : A = A')
    subst heq
    obtain ⟨hA, hDe⟩ := key A C h2
    obtain ⟨-, hDe'⟩ := key A C' h2'
    have : -C = -C' := mul_left_cancel₀ hA (hDe.symm.trans hDe')
    exact Prod.ext rfl (neg_injective this)
  · rintro A ⟨⟨E, hE⟩, hc⟩
    have hA : A ≠ 0 := by
      rintro rfl
      exact hD (by simpa using hE)
    have hdiv : D / A = E := Int.ediv_eq_of_eq_mul_right hA hE
    rw [hdiv] at hc
    refine ⟨(A, -E), ⟨?_, ?_⟩, rfl⟩
    · exact (isPrimitive_gaussForm_zero_iff _ _).2 hc.neg_right
    · show 0 ^ 2 - A * -E = D
      rw [hE]; ring

/-- **A half-size reduction for $(2B, B, C)$ with $D = 4m$, $m$ even.** If $(2B, B, C)$ is properly primitive with
determinant $4m$ ($m$ even), then $B = 2k$ with $m = k (k - C)$ and $\gcd(k, C) = 1$. -/
theorem half_two_mul {B C m : ℤ} (hm : m % 2 = 0) (h1 : IsCoprime (2 * B) C)
    (h2 : B ^ 2 - 2 * B * C = 4 * m) : ∃ k, B = 2 * k ∧ m = k * (k - C) ∧ IsCoprime k C := by
  rcases parity_two_mul h1 h2 with ⟨-, h⟩ | ⟨k, hk, -⟩
  · omega
  · subst hk
    refine ⟨k, rfl, by linarith, ?_⟩
    exact (h1.of_mul_left_right).of_mul_left_right

theorem odd_sub_of_coprime {k F m : ℤ} (hm : m % 2 = 0) (hF : m = k * F) (hc : IsCoprime k F) :
    Odd (k - F) := by
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' k <;> obtain ⟨b, hb | hb⟩ := Int.even_or_odd' F
  · exfalso
    have hu := (isCoprime_iff_forall_dvd _ _).1 hc 2 ⟨a, ha⟩ ⟨b, hb⟩
    have := Int.isUnit_iff.1 hu
    omega
  · exact ⟨a - b - 1, by omega⟩
  · exact ⟨a - b, by omega⟩
  · exfalso
    have : m = 4 * (a * b) + 2 * a + 2 * b + 1 := by rw [hF, ha, hb]; ring
    omega

/-- **Art. 257 II (non-existence):** there is no properly primitive $(2B, B, C)$ of determinant $D$ unless
$D \equiv 3 \pmod 4$ or $D \equiv 0 \pmod 8$ (*Disq. Arith.* Art. 257): for
$D \equiv 1, 2, 4, 5, 6 \pmod 8$ the set is empty. Proved unconditionally; nothing differs from the source. -/
@[kb "gauss1801" "Art. 257 II"]
theorem properlyPrimitive_2BBC_eq_empty {D : ℤ} (h4 : D % 4 ≠ 3) (h8 : D % 8 ≠ 0) :
    {p : ℤ × ℤ | (gaussForm (2 * p.1) p.1 p.2).IsPrimitive ∧ gaussDet (2 * p.1) p.1 p.2 = D} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨B, C⟩ ⟨h1, h2⟩
  rw [isPrimitive_gaussForm_two_mul_iff] at h1
  rcases parity_two_mul h1 h2 with ⟨-, h⟩ | ⟨k, -, h⟩
  · exact h4 h
  · exact h8 h

/-- **Art. 257 II, $D \equiv 3 \pmod 4$** (*Disq. Arith.* Art. 257): the properly primitive
forms $(2B, B, C) = 2B x^2 + 2B xy + C y^2$ of determinant $B^2 - 2BC = D \equiv 3 \pmod 4$ correspond to the
signed divisors $B$ of $D$ with $C = (B - D/B)/2$ prime to $2B$, and there are exactly $2^{n+1}$ of them, where $n$ is
the number of odd primes dividing $D$ (all primes dividing $D$, as $D$ is odd).

Proved unconditionally via $(B, C) \mapsto B$, a bijection onto `signedUnitaryDivisors D`. The source's
condition "$C$ prime to $2B$" is automatic from $\gcd(B, D/B) = 1$ when $D \equiv 3 \pmod 4$. $n$ is
`(D.natAbs.primeFactors.filter Odd).card`. Nothing differs from the source (the counts were also checked by
computer for $0 < |D| \le 200$). -/
@[kb "gauss1801" "Art. 257 II"]
theorem ncard_properlyPrimitive_2BBC_of_mod_four {D : ℤ} (hD : D ≠ 0) (h4 : D % 4 = 3) :
    {p : ℤ × ℤ | (gaussForm (2 * p.1) p.1 p.2).IsPrimitive ∧ gaussDet (2 * p.1) p.1 p.2 = D}.ncard =
      2 ^ ((D.natAbs.primeFactors.filter Odd).card + 1) := by
  rw [card_filter_odd_primeFactors_of_odd (by omega), ← ncard_signedUnitaryDivisors hD]
  have hB0 : ∀ B C : ℤ, B ^ 2 - 2 * B * C = D → B ≠ 0 := by
    intro B C h
    rintro rfl
    apply hD
    rw [← h]
    ring
  apply Set.ncard_congr (fun p _ => p.1)
  · rintro ⟨B, C⟩ ⟨h1, h2⟩
    rw [isPrimitive_gaussForm_two_mul_iff] at h1
    have h2' : B ^ 2 - 2 * B * C = D := h2
    have hB := hB0 B C h2'
    have hBo : Odd B := by
      rcases parity_two_mul h1 h2' with ⟨h, -⟩ | ⟨k, -, h⟩
      · exact h
      · omega
    have hDe : D = B * (B - 2 * C) := by rw [← h2']; ring
    refine ⟨⟨_, hDe⟩, ?_⟩
    rw [Int.ediv_eq_of_eq_mul_right hB hDe]
    have hBC : IsCoprime B C := h1.of_mul_left_right
    exact isCoprime_sub_self ((isCoprime_two_of_odd hBo).symm.mul_right hBC)
  · rintro ⟨B, C⟩ ⟨B', C'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩ (heq : B = B')
    subst heq
    have e1 : B ^ 2 - 2 * B * C = D := h2
    have e2 : B ^ 2 - 2 * B * C' = D := h2'
    have : B * C = B * C' := by linarith
    exact Prod.ext rfl (mul_left_cancel₀ (hB0 B C e1) this)
  · rintro B ⟨⟨E, hE⟩, hcop⟩
    have hB : B ≠ 0 := by
      rintro rfl
      exact hD (by simpa using hE)
    rw [Int.ediv_eq_of_eq_mul_right hB hE] at hcop
    have hBo : Odd B := by
      rcases Int.even_or_odd B with he | ho
      · exfalso
        obtain ⟨t, ht⟩ := he.mul_right E
        omega
      · exact ho
    have hEo : Odd E := by
      rcases Int.even_or_odd E with he | ho
      · exfalso
        obtain ⟨t, ht⟩ := he.mul_left B
        omega
      · exact ho
    obtain ⟨k, hk⟩ := hBo
    obtain ⟨l, hl⟩ := hEo
    have hDe : D = 4 * (k * l) + 2 * (k + l) + 1 := by rw [hE, hk, hl]; ring
    have hCo : Odd (k - l) := ⟨(k - l - 1) / 2, by omega⟩
    have hEB : E = B - 2 * (k - l) := by omega
    rw [hEB] at hcop
    have h2C : IsCoprime B (2 * (k - l)) := by
      have := isCoprime_sub_self hcop
      rwa [sub_sub_cancel] at this
    refine ⟨(B, k - l), ⟨?_, ?_⟩, rfl⟩
    · rw [isPrimitive_gaussForm_two_mul_iff]
      exact (isCoprime_two_of_odd hCo).mul_left h2C.of_mul_right_right
    · show B ^ 2 - 2 * B * (k - l) = D
      rw [hE, hEB]; ring

/-- **Art. 257 II, $D \equiv 0 \pmod 8$** (*Disq. Arith.* Art. 257): the properly
primitive forms $(2B, B, C)$ of determinant $B^2 - 2BC = D \equiv 0 \pmod 8$ number exactly $2^{n+2}$, where $n$ is the
number of odd primes dividing $D$.

Proved unconditionally. Writing $D = 4m$ ($m$ even) the forms have $B = 2k$, and $(B, C) \mapsto B/2$ is a
bijection onto the signed unitary divisors $k$ of $m = D/4$ (with $C = k - m/k$, automatically odd); there are
$2^{\omega(|m|)+1} = 2^{n+2}$ of them because $2 \mid m$. $n$ is `(D.natAbs.primeFactors.filter Odd).card`.
Nothing differs from the source (the counts were also checked by computer for $0 < |D| \le 200$). -/
@[kb "gauss1801" "Art. 257 II"]
theorem ncard_properlyPrimitive_2BBC_of_mod_eight {D : ℤ} (hD : D ≠ 0) (h8 : D % 8 = 0) :
    {p : ℤ × ℤ | (gaussForm (2 * p.1) p.1 p.2).IsPrimitive ∧ gaussDet (2 * p.1) p.1 p.2 = D}.ncard =
      2 ^ ((D.natAbs.primeFactors.filter Odd).card + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, D = 4 * m := ⟨D / 4, by omega⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hD (by simp)
  have hme : m % 2 = 0 := by omega
  rw [show ((4 * m).natAbs.primeFactors.filter Odd).card + 2 = m.natAbs.primeFactors.card + 1 by
    rw [card_primeFactors_eq_of_even hm0 hme]]
  rw [← ncard_signedUnitaryDivisors hm0]
  apply Set.ncard_congr (fun p _ => p.1 / 2)
  · rintro ⟨B, C⟩ ⟨h1, h2⟩
    rw [isPrimitive_gaussForm_two_mul_iff] at h1
    obtain ⟨k, rfl, hk, hkC⟩ := half_two_mul hme h1 h2
    have hk0 : k ≠ 0 := by rintro rfl; exact hm0 (by simpa using hk)
    show 2 * k / 2 ∈ signedUnitaryDivisors m
    rw [show 2 * k / 2 = k by omega]
    refine ⟨⟨k - C, hk⟩, ?_⟩
    rw [Int.ediv_eq_of_eq_mul_right hk0 hk]
    exact isCoprime_sub_self hkC
  · rintro ⟨B, C⟩ ⟨B', C'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩ (heq : B / 2 = B' / 2)
    rw [isPrimitive_gaussForm_two_mul_iff] at h1 h1'
    obtain ⟨k, rfl, hk, -⟩ := half_two_mul hme h1 h2
    obtain ⟨k', rfl, hk', -⟩ := half_two_mul hme h1' h2'
    have hkk : k = k' := by omega
    subst hkk
    have hk0 : k ≠ 0 := by rintro rfl; exact hm0 (by simpa using hk)
    have : k * (k - C) = k * (k - C') := hk.symm.trans hk'
    have := mul_left_cancel₀ hk0 this
    exact Prod.ext rfl (by linarith)
  · rintro k ⟨⟨F, hF⟩, hcop⟩
    have hk0 : k ≠ 0 := by rintro rfl; exact hm0 (by simpa using hF)
    rw [Int.ediv_eq_of_eq_mul_right hk0 hF] at hcop
    have hCo : Odd (k - F) := odd_sub_of_coprime hme hF hcop
    have h2C := isCoprime_two_of_odd hCo
    refine ⟨(2 * k, k - F), ⟨?_, ?_⟩, by show 2 * k / 2 = k; omega⟩
    · rw [isPrimitive_gaussForm_two_mul_iff]
      exact h2C.mul_left (h2C.mul_left (isCoprime_sub_self hcop))
    · show (2 * k) ^ 2 - 2 * (2 * k) * (k - F) = 4 * m
      linear_combination (-4) * hF
