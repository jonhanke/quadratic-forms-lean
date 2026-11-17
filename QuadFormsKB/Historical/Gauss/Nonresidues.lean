import QuadFormsKB.Citation
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic

/-!
# Every non-square is a quadratic nonresidue of some prime (Disquisitiones Arithmeticae, Art. 125)

the historical sources (Gauss, *Disq. Arith.* Art. 125, opening statement; Gauss proves it in full only
later, via the fundamental theorem).

* `exists_prime_legendreSym_eq_neg_one`: for every integer $a$ that is not a perfect square there is an odd prime
  $p$ with Legendre symbol $\left(\frac{a}{p}\right) = -1$. Proved, unconditionally.
* `exists_prime_not_isSquare_zmod`: the same, stated as "$a$ is not a square in $\mathbb{Z}/p$".

The proof uses quadratic reciprocity for the Jacobi symbol (Mathlib), not Gauss's elementary route of Arts.
125-129. It first finds an odd $b > 0$ with Jacobi symbol $\left(\frac{a}{b}\right) = -1$ (Chinese remainder
theorem) and then a prime divisor of $b$ at which the Legendre symbol is $-1$.
-/

namespace QuadFormsKB.Historical.Gauss

open jacobiSym
open scoped NumberTheorySymbols

/-- Case of an odd prime `q` dividing `c` to an odd power: choose `b` a nonresidue mod `q`, `b ≡ 1` mod `8 |c|`. -/
private lemma nonres_caseA {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {k : ℕ} (hk : Odd k) {c : ℤ}
    (hc : ¬ (q : ℤ) ∣ c) : ∃ b : ℕ, Odd b ∧ J(((q : ℤ) ^ k * c) | b) = -1 := by
  haveI := Fact.mk hq
  have hc0 : c ≠ 0 := fun h => hc (h ▸ dvd_zero _)
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod q)
    (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  have h2 : Nat.Coprime q 2 := (Nat.coprime_primes hq Nat.prime_two).mpr hq2
  have h8 : Nat.Coprime q 8 := by simpa using Nat.Coprime.pow_right 3 h2
  have hcop : Nat.Coprime q (8 * c.natAbs) :=
    Nat.Coprime.mul_right h8 ((Nat.Prime.coprime_iff_not_dvd hq).mpr
      (fun h => hc (Int.natCast_dvd.mpr h)))
  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop g.val 1
  have hb8 : b % 8 = 1 := Nat.ModEq.of_dvd (Dvd.intro _ rfl) hb2
  have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
  have hb4 : b % 4 = 1 := by omega
  refine ⟨b, hbodd, ?_⟩
  have hJc : J(c | b) = 1 := by
    rw [jacobiSym.mod_right c hbodd]
    have h4 : b ≡ 1 [MOD 4 * c.natAbs] :=
      Nat.ModEq.of_dvd ⟨2, by ring⟩ hb2
    have : b % (4 * c.natAbs) = 1 := by
      have h5 : b % (4 * c.natAbs) = 1 % (4 * c.natAbs) := h4
      rw [h5]; exact Nat.mod_eq_of_lt (by omega)
    rw [this, jacobiSym.one_right]
  have hJq : J((q : ℤ) | b) = -1 := by
    have h1 : J(((q : ℕ) : ℤ) | b) = J((b : ℤ) | q) :=
      jacobiSym.quadratic_reciprocity_one_mod_four' (hq.odd_of_ne_two hq2) hb4
    have hmod : (b : ℤ) % (q : ℤ) = (g.val : ℤ) % (q : ℤ) := by
      have h := hb1
      unfold Nat.ModEq at h
      exact_mod_cast h
    rw [h1, jacobiSym.mod_left' hmod, ← legendreSym.to_jacobiSym,
      legendreSym.eq_neg_one_iff']
    simpa using hg
  rw [jacobiSym.mul_left, jacobiSym.pow_left, hJq, hJc, hk.neg_one_pow, mul_one]

/-- Case `a = σ 2^e t²` with `t` odd, `σ = ±1`, and `a` not a square. -/
private lemma nonres_caseB (e t : ℕ) (ht : Odd t) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (h : σ = -1 ∨ Odd e) : ∃ b : ℕ, Odd b ∧ J((σ * 2 ^ e * (t : ℤ) ^ 2) | b) = -1 := by
  have h8 : Nat.Coprime 8 t := by
    have : Nat.Coprime 2 t := (Nat.coprime_two_left).mpr ht
    simpa using Nat.Coprime.pow_left 3 this
  have key : ∀ r : ℕ, (r = 3 ∨ r = 5) → ∃ b : ℕ, b % 8 = r ∧ Odd b ∧ J((t : ℤ) ^ 2 | b) = 1 := by
    intro r hr
    obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder h8 r 1
    have hb8 : b % 8 = r := by
      have h5 : b % 8 = r % 8 := hb1
      rw [h5]; omega
    have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
    refine ⟨b, hb8, hbodd, ?_⟩
    apply jacobiSym.sq_one'
    have : Nat.gcd b t = 1 := by
      rw [Nat.ModEq.gcd_eq hb2]; simp
    rw [Int.gcd_natCast_natCast, Nat.gcd_comm]
    exact this
  by_cases he : Odd e
  · obtain ⟨b, hb8, hbodd, hJt⟩ := key 5 (Or.inr rfl)
    refine ⟨b, hbodd, ?_⟩
    have h4 : b % 4 = 1 := by omega
    have h2 : J(2 | b) = -1 := by
      rw [jacobiSym.at_two hbodd, ZMod.χ₈_nat_mod_eight, hb8]; decide
    have hm : J((-1 : ℤ) | b) = 1 := by
      rw [jacobiSym.at_neg_one hbodd, ZMod.χ₄_nat_mod_four, h4]; decide
    rcases hσ with rfl | rfl
    · rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left, hJt, h2, he.neg_one_pow]
      simp
    · rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left, hJt, h2, he.neg_one_pow, hm]
      simp
  · have hσ1 : σ = -1 := h.resolve_right he
    subst hσ1
    obtain ⟨b, hb8, hbodd, hJt⟩ := key 3 (Or.inl rfl)
    refine ⟨b, hbodd, ?_⟩
    have h4 : b % 4 = 3 := by omega
    have h2 : J(2 | b) = -1 := by
      rw [jacobiSym.at_two hbodd, ZMod.χ₈_nat_mod_eight, hb8]; decide
    have hm : J((-1 : ℤ) | b) = -1 := by
      rw [jacobiSym.at_neg_one hbodd, ZMod.χ₄_nat_mod_four, h4]; decide
    have hev : Even e := Nat.not_odd_iff_even.mp he
    rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left, hJt, h2, hev.neg_one_pow, hm]
    simp

/-- Every integer that is not a perfect square has an odd positive `b` with Jacobi symbol `J(a | b) = -1`. -/
private lemma nonres_exists_odd {a : ℤ} (ha : ¬ IsSquare a) :
    ∃ b : ℕ, Odd b ∧ J(a | b) = -1 := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, by simp⟩)
  have hn : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  obtain ⟨d, s, hd0, hs0, hds, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hsign := Int.natAbs_eq a
  by_cases hq : ∃ q, q.Prime ∧ q ≠ 2 ∧ q ∣ d
  · obtain ⟨q, hqp, hq2, d₁, rfl⟩ := hq
    have hqd₁ : ¬ q ∣ d₁ := fun h => by
      have := hsq q (Nat.mul_dvd_mul_left q h)
      exact hqp.one_lt.ne' (Nat.isUnit_iff.mp this)
    obtain ⟨j, s₁, hs₁, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hs0.ne' q hqp.one_lt.ne'
    have hqc : ¬ q ∣ s₁ ^ 2 * d₁ := fun h => by
      rcases (Nat.Prime.dvd_mul hqp).mp h with h | h
      · exact hs₁ (hqp.dvd_of_dvd_pow h)
      · exact hqd₁ h
    have key : (a.natAbs : ℤ) = (q : ℤ) ^ (2 * j + 1) * ((s₁ ^ 2 * d₁ : ℕ) : ℤ) := by
      rw [← hds]; push_cast; ring
    have hk : Odd (2 * j + 1) := odd_two_mul_add_one j
    rcases hsign with h | h
    · rw [h, key]
      exact nonres_caseA hqp hq2 hk (by exact_mod_cast hqc)
    · rw [h, key]
      have e : -((q : ℤ) ^ (2 * j + 1) * ((s₁ ^ 2 * d₁ : ℕ) : ℤ)) =
          (q : ℤ) ^ (2 * j + 1) * -((s₁ ^ 2 * d₁ : ℕ) : ℤ) := by ring
      rw [e]
      exact nonres_caseA hqp hq2 hk (c := -((s₁ ^ 2 * d₁ : ℕ) : ℤ))
        (by rw [dvd_neg]; exact_mod_cast hqc)
  · push_neg at hq
    obtain ⟨e', d₂, hd₂, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0.ne' 2 (by norm_num)
    have hd₂1 : d₂ = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p hp hpd
      have := hq p hp
      by_cases hp2 : p = 2
      · exact hd₂ (hp2 ▸ hpd)
      · exact this hp2 (Dvd.dvd.mul_left hpd _)
    subst hd₂1
    obtain ⟨f, t, ht, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hs0.ne' 2 (by norm_num)
    have hto : Odd t := Nat.odd_iff.mpr (by omega)
    have key : (a.natAbs : ℤ) = 2 ^ (2 * f + e') * (t : ℤ) ^ 2 := by
      rw [← hds]; push_cast; ring
    rcases hsign with h | h
    · have := nonres_caseB (2 * f + e') t hto 1 (Or.inl rfl) (by
        by_contra hc
        push_neg at hc
        apply ha
        have he : Even (2 * f + e') := Nat.not_odd_iff_even.mp hc.2
        obtain ⟨m, hm⟩ := he
        refine ⟨2 ^ m * t, ?_⟩
        rw [h, key, hm]; ring)
      rw [h, key]; simpa using this
    · have := nonres_caseB (2 * f + e') t hto (-1) (Or.inr rfl) (Or.inl rfl)
      rw [h, key]; simpa using this

/-- **Every integer that is not a perfect square is a quadratic nonresidue of some odd prime**
(Gauss, *Disq. Arith.* Art. 125, opening statement).

For $a \in \mathbb{Z}$ with $a$ not a square (so $a < 0$, or $a \ge 2$ not a square; $0$ and $1$ are squares, which
is Gauss's footnote excluding $+1$), there is a prime $p \ne 2$ with Legendre symbol
$\left(\frac{a}{p}\right) = -1$, i.e. $a$ is a quadratic nonresidue of $p$.

Proved unconditionally from Mathlib's quadratic reciprocity for the Jacobi symbol, not by Gauss's elementary route
of Arts. 125-129 (which Gauss carries out only for primes $\equiv 1 \pmod 4$ with either sign). The `Fact p.Prime`
instance of `legendreSym` is supplied from `hp`. -/
@[kb "gauss1801" "Art. 125"]
theorem exists_prime_legendreSym_eq_neg_one {a : ℤ} (ha : ¬ IsSquare a) :
    ∃ p : ℕ, ∃ hp : p.Prime, p ≠ 2 ∧ @legendreSym p ⟨hp⟩ a = -1 := by
  obtain ⟨b, hb, hJ⟩ := nonres_exists_odd ha
  obtain ⟨p, hp, hpb, hJp⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hJ
  refine ⟨p, hp, ?_, ?_⟩
  · rintro rfl
    exact (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr hpb)
  · haveI := Fact.mk hp
    rw [legendreSym.to_jacobiSym]; exact hJp

/-- The same statement as `exists_prime_legendreSym_eq_neg_one`, phrased as: $a$ is not a square in
$\mathbb{Z}/p$ (*Disq. Arith.* Art. 125). Since $0$ is a square, this also gives
$p \nmid a$. -/
@[kb "gauss1801" "Art. 125"]
theorem exists_prime_not_isSquare_zmod {a : ℤ} (ha : ¬ IsSquare a) :
    ∃ p : ℕ, ∃ _ : p.Prime, p ≠ 2 ∧ ¬ IsSquare (a : ZMod p) := by
  obtain ⟨p, hp, hp2, h⟩ := exists_prime_legendreSym_eq_neg_one ha
  haveI := Fact.mk hp
  exact ⟨p, hp, hp2, legendreSym.eq_neg_one_iff p |>.mp h⟩

end QuadFormsKB.Historical.Gauss
