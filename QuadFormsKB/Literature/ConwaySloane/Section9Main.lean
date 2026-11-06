/-
# Conway–Sloane, Ch. 15, §9.7: Theorems 19–21 and Corollary 22

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, pp. 393–396
(`conwaysloane1999`).

**Layer.** As in `Section9Theorems.lean`: Gram matrices $A$, the rational form `csQ A`, $\Lambda = \mathbb Z^n$, a
finite set $P$ of primes containing those dividing $2\det A$; spinor kernel and tractable primes as in
`Section9Kernel.lean`.

**Proves**
* **Theorem 20 (b)** (`theorem20b`): for an indefinite form of dimension $n \ge 3$, a prime $p \equiv 3 \pmod 4$
  cannot be the only intractable prime.
* `theorem21_core`: the case analysis of the proof of Theorem 21 for $n \ge 3$ ($k = p$, $pq$, $4p$ or $8$), from
  Thm. 20 (a), (b) and the $2$-adic divisibilities (41), (42) as hypotheses (discharged in `Section9Final2.lean`).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorems
import QuadFormsKB.Literature.ConwaySloane.Section9OddUnits

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

open scoped Classical

variable {n : ℕ}

section General

variable (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- A family with a square at $p$ and $1$ elsewhere is in the spinor kernel. -/
theorem mulSingle_mem_of_isSquare (p : P) {u : (p.1.adicCompletion ℚ)ˣ}
    (hu : IsSquare (u : p.1.adicCompletion ℚ)) : (Pi.mulSingle p u : CasselsR P) ∈ casselsST Q hQ L P := by
  obtain ⟨s, hs⟩ := hu
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have e : u = Units.mk0 s hs0 ^ 2 := Units.ext (by rw [hs]; simp [sq])
  rw [e, Pi.mulSingle_pow]
  exact Subgroup.mem_sup_left (sq_mem_casselsS Q hQ L P _)

/-- **Conway–Sloane, Theorem 20 (b)** (§9.7, p. 393): *a prime $p \equiv 3 \pmod 4$ cannot be the only intractable
prime* (for an indefinite form of dimension $n \ge 3$). *Proof* (the book's): if every other prime is tractable, the
kernel contains $\Delta_p(-1)$ (since $-1$ is $(-1)$-adically automorphous), and $-1$ is a non-residue mod $p$, so
every $\Delta_p(u)$ is in the kernel. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 20 (b), p. 393"]
theorem theorem20b (hn : 3 ≤ n) (hind : IsIndefinite Q) (p : P) (hp3 : primeOf p.1 % 4 = 3) :
    ¬ (¬ IsTractable Q hQ L P p ∧ ∀ q : P, q ≠ p → IsTractable Q hQ L P q) := by
  rintro ⟨hnt, hoth⟩
  apply hnt
  intro u hu
  rcases isSquare_or_isSquare_neg_of_three_mod_four p.1 hp3 u hu with hsq | hsq
  · exact mulSingle_mem_of_isSquare Q hQ L P p hsq
  · have e : u = -1 * (-u) := by simp
    rw [e, Pi.mulSingle_mul]
    refine (casselsST Q hQ L P).mul_mem (mulSingle_neg_one_mem_of_isTractable Q hQ L P hn hind p hoth) ?_
    exact mulSingle_mem_of_isSquare Q hQ L P p (by simpa using hsq)

end General

/-! ### Theorem 21: the case analysis -/

section Thm21

theorem primeOf_injective {v w : HeightOneSpectrum (𝓞 ℚ)} (h : primeOf v = primeOf w) : v = w :=
  natGen_injective' h

theorem primeOf_odd_mod_four {v : HeightOneSpectrum (𝓞 ℚ)} (h : primeOf v ≠ 2) :
    primeOf v % 4 = 1 ∨ primeOf v % 4 = 3 := by
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have hodd : primeOf v % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h)
  omega

theorem not_isSquare_prime {p : ℕ} (hp : p.Prime) : ¬ IsSquare p := Irreducible.not_isSquare hp

theorem not_isSquare_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : ¬ IsSquare (p * q) := by
  rintro ⟨m, hm⟩
  have hpm : p ∣ m := (hp.dvd_mul.mp (Dvd.intro q hm)).elim id id
  obtain ⟨a, rfl⟩ := hpm
  have : q = p * (a * a) := by
    have h := hm
    rw [show p * a * (p * a) = p * (p * (a * a)) by ring] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hpq' : p ∣ q := ⟨a * a, this⟩
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq')

theorem not_isSquare_four_mul_prime {q : ℕ} (hq : q.Prime) : ¬ IsSquare (4 * q) := by
  rintro ⟨m, hm⟩
  have h2 : 2 ∣ m := by
    have : 2 ∣ m * m := ⟨2 * q, by rw [← hm]; ring⟩
    exact (Nat.prime_two.dvd_mul.mp this).elim id id
  obtain ⟨a, rfl⟩ := h2
  exact not_isSquare_prime hq ⟨a, by linarith⟩

/-- **The case analysis of Theorem 21** (Conway–Sloane, proof of Thm. 21, p. 395), for $n \ge 3$, from Thm. 20 (a),
(b) and the two $2$-adic divisibilities (41), (42) given as hypotheses `h41`, `h42` (proved in Thm. 20 (c), (d)). -/
theorem theorem21_core (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hPd : ∀ v, v ∉ P → ¬ ((primeOf v : ℕ) : ℤ) ∣ 2 * (Cassels.Ch8Ex2.gramForm A).hessian.det)
    (h41 : ∀ p : P, primeOf p.1 = 2 → ¬ IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P p →
      (4 : ℤ) ^ n.choose 2 ∣ 4 ^ (n / 2) * A.det)
    (h42 : ∀ p : P, primeOf p.1 = 2 → (∀ q : P, q ≠ p → IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P q) →
      ¬ IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P p → (8 : ℤ) ^ n.choose 2 ∣ 4 ^ (n / 2) * A.det)
    (h : MoreThanOneClass A) :
    ∃ k : ℕ, ¬ IsSquare k ∧ (k % 4 = 0 ∨ k % 4 = 1) ∧ (k : ℤ) ^ (n.choose 2) ∣ 4 ^ (n / 2) * A.det := by
  set T := IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P with hT
  obtain ⟨p, hp⟩ := exists_not_isTractable hn hA hd hind P hPd h
  have h20a : ∀ q : P, primeOf q.1 ≠ 2 → ¬ T q → ((primeOf q.1 : ℕ) : ℤ) ^ n.choose 2 ∣ A.det :=
    fun q hq hnt => theorem20a hA hd P q hq hnt
  have hdvd : ∀ {x : ℤ}, x ∣ A.det → x ∣ 4 ^ (n / 2) * A.det := fun h => dvd_mul_of_dvd_right h _
  -- (A) an intractable prime `≡ 1 (mod 4)`: `k = p`
  by_cases hA1 : ∃ q : P, ¬ T q ∧ primeOf q.1 % 4 = 1
  · obtain ⟨q, hq, hq1⟩ := hA1
    have hq2 : primeOf q.1 ≠ 2 := by omega
    exact ⟨primeOf q.1, not_isSquare_prime (Rat.HeightOneSpectrum.prime_natGenerator q.1), Or.inr hq1,
      hdvd (h20a q hq2 hq)⟩
  push Not at hA1
  -- (B) two intractable primes `≡ 3 (mod 4)`: `k = pq`
  by_cases hB : ∃ q₁ q₂ : P, q₁ ≠ q₂ ∧ ¬ T q₁ ∧ ¬ T q₂ ∧ primeOf q₁.1 % 4 = 3 ∧ primeOf q₂.1 % 4 = 3
  · obtain ⟨q₁, q₂, hne, h1, h2, h31, h32⟩ := hB
    have hpr1 := Rat.HeightOneSpectrum.prime_natGenerator q₁.1
    have hpr2 := Rat.HeightOneSpectrum.prime_natGenerator q₂.1
    have hne' : primeOf q₁.1 ≠ primeOf q₂.1 := fun e => hne (Subtype.ext (primeOf_injective e))
    refine ⟨primeOf q₁.1 * primeOf q₂.1, not_isSquare_mul_primes hpr1 hpr2 hne', Or.inr (by
      rw [Nat.mul_mod, h31, h32]), hdvd ?_⟩
    have hc : IsCoprime (((primeOf q₁.1 : ℕ) : ℤ) ^ n.choose 2) (((primeOf q₂.1 : ℕ) : ℤ) ^ n.choose 2) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact_mod_cast (Nat.coprime_primes hpr1 hpr2).mpr hne'
    push_cast
    rw [mul_pow]
    exact hc.mul_dvd (h20a q₁ (by omega) h1) (h20a q₂ (by omega) h2)
  push Not at hB
  by_cases h2 : ∃ q : P, ¬ T q ∧ primeOf q.1 = 2
  · obtain ⟨q, hq, hq2⟩ := h2
    -- (C) `2` and a prime `≡ 3 (mod 4)` intractable: `k = 4p`
    by_cases hC : ∃ q' : P, ¬ T q' ∧ primeOf q'.1 % 4 = 3
    · obtain ⟨q', hq', hq'3⟩ := hC
      have hpr := Rat.HeightOneSpectrum.prime_natGenerator q'.1
      refine ⟨4 * primeOf q'.1, not_isSquare_four_mul_prime hpr, Or.inl (Nat.mul_mod_right 4 _), ?_⟩
      have hc : IsCoprime ((4 : ℤ) ^ n.choose 2) (((primeOf q'.1 : ℕ) : ℤ) ^ n.choose 2) := by
        apply IsCoprime.pow
        rw [Int.isCoprime_iff_gcd_eq_one]
        have : Nat.Coprime 4 (primeOf q'.1) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
          refine Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hpr).mpr fun h => ?_)
          have h' : primeOf q'.1 = 2 := h.symm
          rw [h'] at hq'3; norm_num at hq'3
        exact_mod_cast this
      push_cast
      rw [mul_pow]
      exact hc.mul_dvd (h41 q hq2 hq) (hdvd (h20a q' (by omega) hq'))
    -- (D) `2` the only intractable prime: `k = 8`
    · push Not at hC
      have h8 : ¬ IsSquare (8 : ℕ) := by
        rintro ⟨m, hm⟩
        have : m ≤ 3 := by nlinarith
        interval_cases m <;> omega
      refine ⟨8, h8, Or.inl (by norm_num), ?_⟩
      refine h42 q hq2 (fun q' hq'ne => ?_) hq
      by_contra hq'
      have hq'2 : primeOf q'.1 ≠ 2 := fun e => hq'ne (Subtype.ext (primeOf_injective (e.trans hq2.symm)))
      rcases primeOf_odd_mod_four hq'2 with h1 | h3
      · exact absurd h1 (hA1 q' hq')
      · exact hC q' hq' h3
  · -- `2` is tractable: `p` is odd, `≡ 3 (mod 4)`, and the only intractable prime, contradicting Thm. 20 (b)
    push Not at h2
    have hp2 : primeOf p.1 ≠ 2 := fun e => hp (by_contra fun h => h2 p h e)
    have hp3 : primeOf p.1 % 4 = 3 := by
      rcases primeOf_odd_mod_four hp2 with h1 | h3
      · exact absurd h1 (hA1 p hp)
      · exact h3
    exfalso
    refine theorem20b (csQ A) (csQ_nondegenerate hA hd) stdLat P hn hind p hp3 ⟨hp, fun q hqp => ?_⟩
    by_contra hq
    have hq2 : primeOf q.1 ≠ 2 := fun e => hq (by_contra fun h => h2 q h e)
    rcases primeOf_odd_mod_four hq2 with h1 | h3
    · exact hA1 q hq h1
    · exact hB q p hqp hq hp h3 hp3

end Thm21

end QuadFormsKB.ConwaySloane
