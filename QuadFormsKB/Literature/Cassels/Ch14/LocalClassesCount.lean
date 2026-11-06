/-
# Cassels, Chapter 14, Lemma 3.4: the order of $\prod_{p \le \infty} \mathcal G_p$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, pp. 340–341: Lemmas 3.1–3.3 multiplied together. The
exponents are reconstructed from the scan (see `QuadFormsKB.Literature.Cassels.Ch14.LocalClasses`).
-/
import QuadFormsKB.Literature.Cassels.Ch14.LocalClassesTwo

namespace QuadFormsKB.Composition

open QuadForm Siegel

/-- The exponent $\lambda + \mu + \nu$ of Cassels, Ch. 14, Lemma 3.4 (p. 340, reconstructed): $\lambda$ the number of
distinct odd primes dividing $D$, $\mu = 1$ if $D < 0$ (else $0$), and $\nu = 0$ if $2 \nmid D$ or $D = 4d$ with
$d \equiv 1 \pmod 4$, $\nu = 2$ if $2^5 \mid D$, $\nu = 1$ otherwise. -/
@[kb "cassels1978" "Ch. 14, Lemma 3.4, p. 340 (the exponent λ + μ + ν, reconstructed)"]
def lemma34Exponent (D : ℤ) : ℕ :=
  (D.natAbs.primeFactors.filter (· ≠ 2)).card + (if D < 0 then 1 else 0) +
    (if D % 2 = 1 ∨ (D / 4) % 4 = 1 then 0 else if 32 ∣ D then 2 else 1)

/-- Local class count at a natural number (`1` if it is not prime); packages the `Fact` instance. -/
noncomputable def localCount (D : ℤ) (n : ℕ) : ℕ :=
  if h : n.Prime then haveI : Fact n.Prime := ⟨h⟩; Nat.card (LocalClasses n D) else 1

/-- The factor at an odd prime: `2` if the prime divides `D`, else `1`. -/
lemma localCount_odd {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : localCount D p = if (p : ℤ) ∣ D then 2 else 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold localCount
  rw [dif_pos hp]
  split_ifs with h
  · exact card_localClasses_odd_of_dvd hp2 hD hD4 h
  · exact card_localClasses_odd_of_not_dvd hp2 hD4 h

/-- The factor at `2` is `2 ^ ν`. -/
lemma localCount_two {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    localCount D 2 =
      2 ^ (if D % 2 = 1 ∨ (D / 4) % 4 = 1 then 0 else if 32 ∣ D then 2 else 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold localCount
  rw [dif_pos Nat.prime_two]
  rw [card_localClasses_two hD hD4]
  by_cases h1 : D % 2 = 1 ∨ (D / 4) % 4 = 1
  · simp [h1]
  · have h8 : (8 ∣ D / 4) ↔ 32 ∣ D := by omega
    simp only [h1, if_false, h8]
    split_ifs <;> norm_num

/-- If `D` is odd, the factor at `2` is `1`. -/
lemma localCount_two_of_odd {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1)
    (hodd : D % 2 = 1) : localCount D 2 = 1 := by
  rw [localCount_two hD hD4]; simp [hodd]

/-- The product of `localCount` over the prime factors of `D`. -/
lemma prod_primeFactors_localCount {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∏ n ∈ D.natAbs.primeFactors, localCount D n =
      2 ^ (D.natAbs.primeFactors.filter (· ≠ 2)).card *
        2 ^ (if D % 2 = 1 ∨ (D / 4) % 4 = 1 then 0 else if 32 ∣ D then 2 else 1) := by
  have hsplit : ∏ n ∈ D.natAbs.primeFactors, localCount D n =
      localCount D 2 * ∏ n ∈ D.natAbs.primeFactors.filter (· ≠ 2), localCount D n := by
    by_cases h2 : 2 ∈ D.natAbs.primeFactors
    · rw [← Finset.mul_prod_erase _ _ h2]
      congr 1
      rw [Finset.filter_ne']
    · have hodd : D % 2 = 1 := by
        have : ¬ (2 ∣ D.natAbs) := fun h => h2 (by simp [Nat.mem_primeFactors, h, hD, Nat.prime_two])
        omega
      rw [localCount_two_of_odd hD hD4 hodd, one_mul]
      congr 1
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx; exact ⟨hx, by rintro rfl; exact h2 hx⟩
      · exact fun h => h.1
  rw [hsplit, localCount_two hD hD4, mul_comm]
  congr 1
  rw [← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro n hn
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hn
  rw [localCount_odd hD hD4 hn.1.1 hn.2, if_pos]
  exact Int.natCast_dvd.mpr hn.1.2.1

/-- The `finprod` over `Nat.Primes` is the finite product over the prime factors of `D`. -/
lemma finprod_localClasses_eq {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (∏ᶠ p : Nat.Primes, haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; Nat.card (LocalClasses p D)) =
      ∏ n ∈ D.natAbs.primeFactors, localCount D n := by
  have h1 : ∀ p : Nat.Primes, (haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; Nat.card (LocalClasses p D)) =
      localCount D p := fun p => by
    unfold localCount; rw [dif_pos p.2]
  simp_rw [h1]
  change ∏ᶠ p : Subtype Nat.Prime, localCount D (p : ℕ) = _
  rw [finprod_eq_prod_of_mulSupport_subset (s := D.natAbs.primeFactors.subtype Nat.Prime)]
  · rw [Finset.prod_subtype_eq_prod_filter]
    refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, h⟩, _⟩; exact ⟨hp, h⟩
    · rintro ⟨hp, h⟩; exact ⟨⟨hp, h⟩, hp⟩
  · intro p hp
    rw [Function.mem_mulSupport] at hp
    rw [Finset.mem_coe, Finset.mem_subtype, Nat.mem_primeFactors]
    refine ⟨p.2, ?_, by simpa using hD⟩
    by_contra hn
    apply hp
    have hndvd : ¬ (p : ℤ) ∣ D := fun h => hn (Int.natCast_dvd.mp h)
    by_cases h2 : (p : ℕ) = 2
    · rw [h2] at hndvd ⊢
      apply localCount_two_of_odd hD hD4
      have : ¬ (2 : ℤ) ∣ D := by exact_mod_cast hndvd
      omega
    · rw [localCount_odd hD hD4 p.2 h2, if_neg hndvd]

/-- **Cassels, Ch. 14, Lemma 3.4** (pp. 340–341): *the order of the product group $\prod_{p \le \infty} \mathcal G_p$
is $2^{\lambda + \mu + \nu}$* (exponents reconstructed, `lemma34Exponent`). The product is over all primes and
$\infty$; all but finitely many factors are $1$ (Lemma 3.1 (i)). -/
@[kb "cassels1978" "Ch. 14, Lemma 3.4, pp. 340–341 (exponents reconstructed)"]
theorem card_prod_localClasses {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (∏ᶠ p : Nat.Primes, haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; Nat.card (LocalClasses p D)) *
      Nat.card (RealClasses D) = 2 ^ lemma34Exponent D := by
  have hr : (if 0 < D then 1 else 2) = 2 ^ (if D < 0 then 1 else 0) := by
    by_cases h : D < 0
    · have : ¬ 0 < D := by omega
      simp [h, this]
    · have : 0 < D := by omega
      simp [h, this]
  rw [finprod_localClasses_eq hD hD4, prod_primeFactors_localCount hD hD4, card_realClasses hD,
    hr, lemma34Exponent, pow_add, pow_add]
  ring


end QuadFormsKB.Composition
