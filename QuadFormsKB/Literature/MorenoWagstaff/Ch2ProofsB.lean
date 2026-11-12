/-
# Moreno–Wagstaff 2005, Chapter 2: further proofs

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Chapter 2.

**Proves**
* `theorem25` (Theorem 2.5, **proved**): from Jacobi's two-square formula
  `Tamagawa.Classical.dirichlet_sumTwoSq_r2` ($r_2(m) = 4\sum_{d \mid m}\chi_{-4}(d)$) and the values of $\chi_{-4}$.
* `corollary21` (Corollary 2.1, **proved**): existence from `Nat.Prime.sq_add_sq`, uniqueness by the elementary
  identity $(xv - yu)(xv + yu) = p(x^2 - u^2)$.
* `r4Multiplicative` (§2.7, **proved**): from Jacobi's $r_4(m) = 8\sum_{d \mid m,\,4 \nmid d} d$
  (`repNum_sumSq_four`) and multiplicativity of $d \mapsto d\cdot[4 \nmid d]$.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Proofs
import QuadFormsKB.Tamagawa.Classical.BinaryJacobi
import Mathlib.NumberTheory.SumTwoSquares

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-! ### Theorem 2.5 -/

private lemma sumSq_two_eq' : sumSq 2 = Tamagawa.Classical.sumTwoSqZ := by
  unfold sumSq Tamagawa.Classical.sumTwoSqZ
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma r2_chi (n : ℕ) (hn : 0 < n) :
    (repNum (sumSq 2) n : ℤ) = 4 * ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) := by
  have h := Tamagawa.Classical.dirichlet_sumTwoSq_r2 n hn
  rw [← sumSq_two_eq'] at h
  exact_mod_cast h

private lemma chi4_eq (d : ℕ) :
    (ZMod.χ₄ (d : ZMod 4) : ℤ) = if Odd d then (-1 : ℤ) ^ ((d - 1) / 2) else 0 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  by_cases hodd : Odd d
  · have hd2 := Nat.odd_iff.1 hodd
    rw [if_pos hodd, if_neg (by omega)]
    by_cases h : d % 4 = 1
    · rw [if_pos h]
      have : (d - 1) / 2 = 2 * (d / 4) := by omega
      rw [this, pow_mul]; simp
    · rw [if_neg h]
      have : (d - 1) / 2 = 2 * (d / 4) + 1 := by omega
      rw [this, pow_succ, pow_mul]; simp
  · rw [if_neg hodd, if_pos (by rw [Nat.not_odd_iff] at hodd; omega)]

private lemma sum_geom_neg_one (e : ℕ) :
    ∑ i ∈ Finset.range (e + 1), (-1 : ℤ) ^ i = if Even e then 1 else 0 := by
  induction e with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd n with h | h
    · have h' : ¬ Even (n + 1) := by rw [Nat.not_even_iff_odd]; exact h.add_one
      simp [h, h']
    · have h' : Even (n + 1) := h.add_one
      have h'' : ¬ Even n := by rw [Nat.not_even_iff_odd]; exact h
      simp [h', h'']

private lemma r2_prime_pow (p e : ℕ) (hp : p.Prime) :
    (repNum (sumSq 2) ((p : ℤ) ^ e) : ℤ) =
      4 * ∑ i ∈ Finset.range (e + 1), (ZMod.χ₄ (p : ZMod 4) : ℤ) ^ i := by
  have h1 : ((p : ℤ) ^ e) = ((p ^ e : ℕ) : ℤ) := by push_cast; rfl
  rw [h1, r2_chi _ (pow_pos hp.pos e), Nat.divisors_prime_pow hp, Finset.sum_map]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  push_cast
  rw [map_pow]

/-- **Moreno–Wagstaff, Theorem 2.5** (p. 27), proved: $r_2(n) = 4\sum_{d \mid n}\chi_{-4}(d)$ by Jacobi's formula
`Tamagawa.Classical.dirichlet_sumTwoSq_r2`; the two displayed forms follow by evaluating $\chi_{-4}$ on odd divisors,
and the prime-power table from $\chi_{-4}(p^i) = \chi_{-4}(p)^i$ and the geometric sum. -/
@[kb "morenowagstaff2005" "Theorem 2.5, p. 27"]
theorem theorem25 : Theorem25 := by
  refine ⟨fun n hn => ⟨?_, ?_⟩, fun p e hp => ?_⟩
  · rw [r2_chi n hn]
    congr 1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [chi4_eq]
  · rw [r2_chi n hn]
    congr 1
    have : ∀ d : ℕ, (ZMod.χ₄ (d : ZMod 4) : ℤ) =
        (if d % 4 = 1 then 1 else 0) - (if d % 4 = 3 then 1 else 0) := by
      intro d
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      split_ifs <;> omega
    simp only [this, Finset.sum_sub_distrib, Finset.sum_boole]
  · have key := r2_prime_pow p e hp
    have hc : (ZMod.χ₄ (p : ZMod 4) : ℤ) = if p % 2 = 0 then 0 else if p % 4 = 1 then 1 else -1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]
    by_cases h2 : p = 2
    · subst h2
      have : (ZMod.χ₄ ((2 : ℕ) : ZMod 4) : ℤ) = 0 := by rw [hc]; simp
      rw [this] at key
      have hs : ∑ i ∈ Finset.range (e + 1), (0 : ℤ) ^ i = 1 := by
        rw [Finset.sum_range_succ']; simp
      rw [hs] at key
      rw [if_pos (Or.inl rfl)]
      omega
    · rcases hp.eq_two_or_odd with h | hodd
      · exact absurd h h2
      have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases h4 with h4 | h4
      · have : (ZMod.χ₄ (p : ZMod 4) : ℤ) = 1 := by rw [hc]; simp [hodd, h4]
        rw [this] at key
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at key
        rw [if_neg (by rintro (h | ⟨h, _⟩) <;> omega), if_pos h4]
        push_cast at key
        omega
      · have : (ZMod.χ₄ (p : ZMod 4) : ℤ) = -1 := by rw [hc]; simp [hodd, h4]
        rw [this, sum_geom_neg_one] at key
        rw [if_neg (by omega : ¬ (p % 4 = 1))]
        by_cases he : Even e
        · rw [if_pos he] at key
          rw [if_pos (Or.inr ⟨h4, he⟩)]
          omega
        · rw [if_neg he] at key
          rw [if_neg (by rintro (h | ⟨_, h⟩); exact h2 h; exact he h)]
          omega

/-! ### Corollary 2.1 -/

private lemma sq_ne_prime (p a : ℕ) (hp : p.Prime) : a ^ 2 ≠ p := by
  intro h
  have hd : a ∣ p := ⟨a, by rw [← h]; ring⟩
  rcases hp.eq_one_or_self_of_dvd a hd with rfl | rfl
  · have := hp.one_lt; simp at h; omega
  · have := hp.two_le; nlinarith

private lemma cor21_uniq (p x y u v : ℕ) (hp : p.Prime) (hp1 : p % 4 = 1) (hx : 0 < x) (hy : 0 < y)
    (hu : 0 < u) (hv : 0 < v) (hye : Even y) (hve : Even v) (h1 : p = x ^ 2 + y ^ 2)
    (h2 : p = u ^ 2 + v ^ 2) : x = u ∧ y = v := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have e1 : (x : ℤ) ^ 2 + y ^ 2 = p := by exact_mod_cast h1.symm
  have e2 : (u : ℤ) ^ 2 + v ^ 2 = p := by exact_mod_cast h2.symm
  have hx' : (0 : ℤ) < x := by exact_mod_cast hx
  have hy' : (0 : ℤ) < y := by exact_mod_cast hy
  have hu' : (0 : ℤ) < u := by exact_mod_cast hu
  have hv' : (0 : ℤ) < v := by exact_mod_cast hv
  have hid : ((x : ℤ) * v - y * u) * (x * v + y * u) = p * (x ^ 2 - u ^ 2) := by
    linear_combination (x : ℤ) ^ 2 * e2 - (u : ℤ) ^ 2 * e1
  have hprod : ((x : ℤ) ^ 2 + y ^ 2) * ((u : ℤ) ^ 2 + v ^ 2) = p * p := by rw [e1, e2]
  have hsq1 : ((x : ℤ) * v + y * u) ^ 2 + ((x : ℤ) * u - y * v) ^ 2 = p ^ 2 := by
    linear_combination hprod
  have hsq2 : ((x : ℤ) * v - y * u) ^ 2 + ((x : ℤ) * u + y * v) ^ 2 = p ^ 2 := by
    linear_combination hprod
  rcases hpZ.dvd_or_dvd (⟨_, hid⟩ : (p : ℤ) ∣ _) with h | h
  · have h0 : (x : ℤ) * v - y * u = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h
      apply abs_lt_of_sq_lt_sq _ hp0.le
      have : 0 < ((x : ℤ) * u + y * v) ^ 2 := by positivity
      nlinarith
    have h3 : (p : ℤ) * (x ^ 2 - u ^ 2) = 0 := by rw [← hid, h0, zero_mul]
    have h4 : (x : ℤ) ^ 2 = u ^ 2 := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hp0.ne'
      · linarith
    have h5 : (y : ℤ) ^ 2 = v ^ 2 := by linarith
    have h4' : x ^ 2 = u ^ 2 := by exact_mod_cast h4
    have h5' : y ^ 2 = v ^ 2 := by exact_mod_cast h5
    exact ⟨Nat.pow_left_injective two_ne_zero h4', Nat.pow_left_injective two_ne_zero h5'⟩
  · exfalso
    have hs0 : (0 : ℤ) < x * v + y * u := by positivity
    have hsle : (x : ℤ) * v + y * u ≤ p := by
      by_contra hc
      push Not at hc
      nlinarith [sq_nonneg ((x : ℤ) * u - y * v)]
    obtain ⟨k, hk⟩ := h
    have hk0 : 0 < k := by
      by_contra hc
      push Not at hc
      nlinarith
    have hk1 : k = 1 := by
      by_contra hc
      have : 2 ≤ k := by omega
      nlinarith
    subst hk1
    obtain ⟨a, ha⟩ := hve
    obtain ⟨b, hb⟩ := hye
    have hv2 : (v : ℤ) = a + a := by exact_mod_cast ha
    have hy2 : (y : ℤ) = b + b := by exact_mod_cast hb
    obtain ⟨w, hw⟩ : ∃ w : ℤ, (p : ℤ) = 2 * w := ⟨x * a + b * u, by rw [mul_one] at hk; rw [← hk, hv2, hy2]; ring⟩
    omega

private lemma not_even_and_odd_sq (p a b : ℕ) (h : p % 4 = 1) (hab : a ^ 2 + b ^ 2 = p) :
    (Odd a ∧ Even b) ∨ (Even a ∧ Odd b) := by
  have hodd : Odd (a ^ 2 + b ^ 2) := by rw [hab]; exact Nat.odd_iff.2 (Nat.odd_of_mod_four_eq_one h)
  rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd b with hb | hb
  · exact absurd ((Nat.even_pow.2 ⟨ha, two_ne_zero⟩).add (Nat.even_pow.2 ⟨hb, two_ne_zero⟩))
      (Nat.not_even_iff_odd.2 hodd)
  · exact Or.inr ⟨ha, hb⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact absurd ((ha.pow (n := 2)).add_odd (hb.pow (n := 2))) (Nat.not_even_iff_odd.2 hodd)

/-- **Moreno–Wagstaff, Corollary 2.1** (p. 28), proved: existence from Fermat's two-square theorem
(`Nat.Prime.sq_add_sq`); uniqueness from $p \mid (xv - yu)(xv + yu) = p(x^2 - u^2)$: the factor $xv + yu$ is even
and in $(0, p]$, hence not divisible by the odd $p$, so $p \mid xv - yu$, whence $xv = yu$ and $(x, y) = (u, v)$. -/
@[kb "morenowagstaff2005" "Corollary 2.1, p. 28"]
theorem corollary21 : Corollary21 := by
  intro p hp hp1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (by omega : p % 4 ≠ 3)
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by
    rintro rfl; exact sq_ne_prime p b hp (by simpa using hab))
  have hb0 : 0 < b := Nat.pos_of_ne_zero (by
    rintro rfl; exact sq_ne_prime p a hp (by simpa using hab))
  rcases not_even_and_odd_sq p a b hp1 hab with ⟨hao, hbe⟩ | ⟨hae, hbo⟩
  · refine ⟨(a, b), ⟨ha0, hb0, hao, hbe, hab.symm⟩, ?_⟩
    rintro ⟨u, v⟩ ⟨hu, hv, _, hve, huv⟩
    have := cor21_uniq p a b u v hp hp1 ha0 hb0 hu hv hbe hve hab.symm huv
    exact Prod.ext this.1.symm this.2.symm
  · refine ⟨(b, a), ⟨hb0, ha0, hbo, hae, by rw [← hab]; ring⟩, ?_⟩
    rintro ⟨u, v⟩ ⟨hu, hv, _, hve, huv⟩
    have := cor21_uniq p b a u v hp hp1 hb0 ha0 hu hv hae hve (by rw [← hab]; ring) huv
    exact Prod.ext this.1.symm this.2.symm

/-! ### Multiplicativity of $r_4 / 8$ -/

/-- The arithmetic function $d \mapsto d\,[4 \nmid d]$. -/
private def notFour : ArithmeticFunction ℕ := ⟨fun d => if 4 ∣ d then 0 else d, by simp⟩

private lemma notFour_apply (d : ℕ) : notFour d = if 4 ∣ d then 0 else d := rfl

private lemma notFour_mult : notFour.IsMultiplicative := by
  refine ⟨by simp [notFour_apply], fun {a b} hab => ?_⟩
  have h4 : IsPrimePow 4 := ⟨2, 2, Nat.prime_two.prime, two_pos, by norm_num⟩
  have key := hab.isPrimePow_dvd_mul h4
  simp only [notFour_apply]
  by_cases ha : 4 ∣ a
  · have : 4 ∣ a * b := key.2 (Or.inl ha)
    simp [ha, this]
  · by_cases hb : 4 ∣ b
    · have : 4 ∣ a * b := key.2 (Or.inr hb)
      simp [hb, this]
    · have : ¬ 4 ∣ a * b := fun h => by tauto
      simp [ha, hb, this]

private lemma sum_filter_not_four (m : ℕ) :
    ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d = (ArithmeticFunction.zeta * notFour) m := by
  rw [ArithmeticFunction.zeta_mul_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [notFour_apply]
  split_ifs <;> rfl

/-- **Moreno–Wagstaff, §2.7** (p. 33), proved: by Jacobi's formula `repNum_sumSq_four`,
$r_4(m) = 8\sum_{d \mid m,\,4 \nmid d} d = 8\,(\zeta * g)(m)$ with $g(d) = d\,[4 \nmid d]$ multiplicative; the
cases $m = 0$ or $n = 0$ force the other factor to be $1$. -/
@[kb "morenowagstaff2005" "§2.7, r_4(n)/8 multiplicative, p. 33"]
theorem r4Multiplicative : R4Multiplicative := by
  intro m n hmn
  have hmult : (ArithmeticFunction.zeta * notFour).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul notFour_mult
  have r1 : repNum (sumSq 4) ((1 : ℕ) : ℤ) = 8 := by
    rw [repNum_sumSq_four (le_refl 1)]; decide
  by_cases hm : m = 0
  · subst hm
    have : n = 1 := by simpa using hmn
    subst this
    simp only [Nat.cast_zero, Nat.cast_one, mul_one]
    rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, r1]
  by_cases hn : n = 0
  · subst hn
    have : m = 1 := by simpa using hmn
    subst this
    simp only [Nat.cast_zero, Nat.cast_one, mul_zero]
    rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, r1]
    ring
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  have hmn1 : 1 ≤ m * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm hn)
  have e : ((m : ℤ) * n) = ((m * n : ℕ) : ℤ) := by push_cast; rfl
  rw [e, repNum_sumSq_four hmn1, repNum_sumSq_four hm1, repNum_sumSq_four hn1,
    sum_filter_not_four, sum_filter_not_four, sum_filter_not_four, hmult.2 hmn]
  ring

end QuadFormsKB.MorenoWagstaff
