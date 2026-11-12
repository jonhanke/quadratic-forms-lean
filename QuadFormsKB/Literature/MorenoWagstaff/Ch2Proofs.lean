/-
# Moreno–Wagstaff 2005, Chapter 2: proofs of the elementary statements

Proofs of the elementary statements of `Ch2Statements.lean`: Lemmas 2.1, 2.2, 2.3, 2.5, 2.7, Corollaries 2.2, 2.3,
Theorem 2.6 (from Jacobi's four-square formula `repNum_sumSq_four`) and Remark 2.1.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Statements

open scoped ArithmeticFunction.sigma

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-- Helper: an integer square is `0 mod 4` with even root or `1 mod 4` with odd root. -/
lemma sq_mod_four (x : ℤ) : (x ^ 2 % 4 = 0 ∧ x % 2 = 0) ∨ (x ^ 2 % 4 = 1 ∧ x % 2 = 1) := by
  have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases h with h | h | h | h <;> simp [pow_two, Int.mul_emod, h] <;> omega

/-- Helper: squares mod 8. -/
lemma sq_mod_eight (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
    omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- **Moreno–Wagstaff, Lemma 2.2** (p. 13), proved: case analysis of squares modulo 8, then `omega`. -/
@[kb "morenowagstaff2005" "Lemma 2.2, p. 13"]
theorem lemma22 : Lemma22 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have := sq_mod_eight x
    have h4 := sq_mod_four x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro x y
    have h1 := sq_mod_four x
    have h2 := sq_mod_four y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro x
    have := sq_mod_eight x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro x y
    have h1 := sq_mod_eight x
    have h2 := sq_mod_eight y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro x y z
    have h1 := sq_mod_eight x
    have h2 := sq_mod_eight y
    have h3 := sq_mod_eight z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-! ### Lemma 2.1 -/

lemma odd_sum_range_pow {p : ℕ} (hp : Odd p) (k : ℕ) :
    Odd (∑ i ∈ Finset.range (k + 1), p ^ i) ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.odd_add, ih]
    have : Odd (p ^ (k + 1)) := hp.pow
    have h2 : ¬ Even (p ^ (k + 1)) := Nat.not_even_iff_odd.mpr this
    simp [h2, Nat.not_even_iff_odd, Nat.even_add_one]

lemma odd_sigma_prime_pow {p : ℕ} (hp : p.Prime) (hodd : Odd p) (k : ℕ) :
    Odd (σ 1 (p ^ k)) ↔ Even k := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  exact odd_sum_range_pow hodd k

/-- **Moreno–Wagstaff, Lemma 2.1** (p. 13), proved: $\sigma$ is multiplicative, $\sigma(p^a) \equiv a + 1 \pmod 2$
for odd $p$, and $n$ is a square iff all exponents are even. -/
@[kb "morenowagstaff2005" "Lemma 2.1, p. 13"]
theorem lemma21 : Lemma21 := by
  intro n hn
  have hn0 : n ≠ 0 := hn.pos.ne'
  rw [Nat.isSquare_iff_even_factorization,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization (σ 1)
      ArithmeticFunction.isMultiplicative_sigma hn0]
  have hodd : ∀ p ∈ n.factorization.support, Odd p ∧ p.Prime := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpp.odd_of_ne_two ?_, hpp⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hdvd)
  constructor
  swap
  · intro h p hp
    by_cases hs : p ∈ n.factorization.support
    · -- the product is odd, so each factor is odd
      obtain ⟨ho, hpp'⟩ := hodd p hs
      rw [← odd_sigma_prime_pow hpp' ho]
      by_contra hne
      have hev : Even (σ 1 (p ^ n.factorization p)) := Nat.not_odd_iff_even.mp hne
      have hdv : σ 1 (p ^ n.factorization p) ∣ n.factorization.prod fun p k => σ 1 (p ^ k) :=
        Finset.dvd_prod_of_mem (fun p => σ 1 (p ^ n.factorization p)) hs
      exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr
        (dvd_trans (even_iff_two_dvd.mp hev) hdv))
    · have : n.factorization p = 0 := by
        by_contra h
        exact hs (Finsupp.mem_support_iff.mpr h)
      simp [this]
  · intro h
    unfold Finsupp.prod
    refine Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one fun p hp => ?_
    obtain ⟨ho, hpp'⟩ := hodd p hp
    exact (odd_sigma_prime_pow hpp' ho _).mpr (h p hpp')

/-! ### Lemma 2.3 -/

lemma sum_three (x : Fin 3 → ℤ) : ∑ i, x i ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  simp [Fin.sum_univ_three]

lemma sum_two (x : Fin 2 → ℤ) : ∑ i, x i ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp [Fin.sum_univ_two]

lemma mem_repSet_sumSq {k : ℕ} (x : Fin k → ℤ) (m : ℤ) :
    x ∈ repSet (sumSq k) m ↔ ∑ i, x i ^ 2 = m := by
  simp [repSet, eval_sumSq]

lemma r3_four (n : ℕ) : repNum (sumSq 3) (4 * n) = repNum (sumSq 3) n := by
  unfold repNum
  symm
  refine Nat.card_congr
    { toFun := fun y => ⟨fun i => 2 * y.1 i, ?_⟩
      invFun := fun x => ⟨fun i => x.1 i / 2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have := (mem_repSet_sumSq _ _).mp y.2
    rw [mem_repSet_sumSq, sum_three]
    rw [sum_three] at this
    nlinarith
  · have h := (mem_repSet_sumSq _ _).mp x.2
    rw [sum_three] at h
    have h0 := sq_mod_four (x.1 0)
    have h1 := sq_mod_four (x.1 1)
    have h2 := sq_mod_four (x.1 2)
    have e0 : x.1 0 = 2 * (x.1 0 / 2) := by omega
    have e1 : x.1 1 = 2 * (x.1 1 / 2) := by omega
    have e2 : x.1 2 = 2 * (x.1 2 / 2) := by omega
    rw [mem_repSet_sumSq, sum_three]
    rw [e0, e1, e2] at h
    nlinarith
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    funext i
    simp
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    funext i
    have h := (mem_repSet_sumSq _ _).mp hx
    rw [sum_three] at h
    have h0 := sq_mod_four (x 0)
    have h1 := sq_mod_four (x 1)
    have h2 := sq_mod_four (x 2)
    fin_cases i <;> simp <;> omega

lemma r2_two (n : ℕ) : repNum (sumSq 2) (2 * n) = repNum (sumSq 2) n := by
  unfold repNum
  symm
  refine Nat.card_congr
    { toFun := fun y => ⟨![y.1 0 + y.1 1, y.1 0 - y.1 1], ?_⟩
      invFun := fun x => ⟨![(x.1 0 + x.1 1) / 2, (x.1 0 - x.1 1) / 2], ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have := (mem_repSet_sumSq _ _).mp y.2
    rw [mem_repSet_sumSq, sum_two]
    rw [sum_two] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  · have h := (mem_repSet_sumSq _ _).mp x.2
    rw [sum_two] at h
    have h0 := sq_mod_four (x.1 0)
    have h1 := sq_mod_four (x.1 1)
    obtain ⟨a, ha⟩ : ∃ a, x.1 0 + x.1 1 = 2 * a := ⟨(x.1 0 + x.1 1) / 2, by
      have : (x.1 0 + x.1 1) % 2 = 0 := by
        have h2 : (x.1 0) ^ 2 + (x.1 1) ^ 2 = 2 * n := by simpa using h
        omega
      omega⟩
    obtain ⟨b, hb⟩ : ∃ b, x.1 0 - x.1 1 = 2 * b := ⟨(x.1 0 - x.1 1) / 2, by
      have : (x.1 0 - x.1 1) % 2 = 0 := by
        have h2 : (x.1 0) ^ 2 + (x.1 1) ^ 2 = 2 * n := by simpa using h
        omega
      omega⟩
    have e0 : x.1 0 = a + b := by omega
    have e1 : x.1 1 = a - b := by omega
    rw [mem_repSet_sumSq, sum_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ha, hb]
    rw [e0, e1] at h
    have : (2 * a / 2) = a := by omega
    have h' : (2 * b / 2) = b := by omega
    rw [this, h']
    nlinarith
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> omega
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    funext i
    have h := (mem_repSet_sumSq _ _).mp hx
    rw [sum_two] at h
    have h0 := sq_mod_four (x 0)
    have h1 := sq_mod_four (x 1)
    have h2 : (x 0) ^ 2 + (x 1) ^ 2 = 2 * n := h
    fin_cases i <;> simp <;> omega

/-- **Moreno–Wagstaff, Lemma 2.3** (p. 13), proved: explicit bijections $x \mapsto x/2$ (all coordinates are
even by residues mod 4) and $(x_1, x_2) \mapsto ((x_1+x_2)/2, (x_1-x_2)/2)$. -/
@[kb "morenowagstaff2005" "Lemma 2.3, p. 13"]
theorem lemma23 : Lemma23 := fun n => ⟨r3_four n, r2_two n⟩

/-! ### Corollary 2.2 -/

/-- **Moreno–Wagstaff, Corollary 2.2** (p. 28), proved: from `sum_chi4_nonneg`, since
$\sum_{d \mid n} \chi_{-4}(d) = \#\{d \equiv 1\} - \#\{d \equiv 3\}$. -/
@[kb "morenowagstaff2005" "Corollary 2.2, p. 28"]
theorem corollary22 : Corollary22 := by
  intro n hn
  have h := QuadFormsKB.Tamagawa.Classical.sum_chi4_nonneg hn.ne'
  have key : ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) =
      ((n.divisors.filter (· % 4 = 1)).card : ℝ) - ((n.divisors.filter (· % 4 = 3)).card : ℝ) := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have h4 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [ZMod.χ₄_nat_mod_four d]
    rcases h4 with h4 | h4 | h4 | h4 <;> rw [h4] <;> simp
  rw [key] at h
  have : ((n.divisors.filter (· % 4 = 3)).card : ℝ) ≤ ((n.divisors.filter (· % 4 = 1)).card : ℝ) := by
    linarith
  exact_mod_cast this

/-! ### Theorem 2.6 and Lemma 2.5 -/

lemma divisors_filter_not_four (a m : ℕ) (hm : Odd m) (ha : 1 ≤ a) :
    (2 ^ a * m).divisors.filter (¬ 4 ∣ ·) = m.divisors ∪ m.divisors.image (2 * ·) := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  have hmodd : m % 2 = 1 := Nat.odd_iff.mp hm
  constructor
  · rintro ⟨⟨hd, -⟩, h4⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hd
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
    have hzodd : z % 2 = 1 := by
      have := Nat.odd_iff.mpr hmodd
      rcases Nat.even_or_odd z with hze | hzo
      · exact absurd (hze.two_dvd.trans hz) (by omega)
      · exact Nat.odd_iff.mp hzo
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · left; simpa using ⟨hz, hm0⟩
      · right; exact ⟨z, ⟨hz, hm0⟩, by ring⟩
    · exfalso
      apply h4
      have : 4 ∣ 2 ^ i := by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]; exact pow_dvd_pow 2 hi2
      exact this.mul_right z
  · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
    · have heodd : d % 2 = 1 := by
        rcases Nat.even_or_odd d with hze | hzo
        · exact absurd (hze.two_dvd.trans hd) (by omega)
        · exact Nat.odd_iff.mp hzo
      refine ⟨⟨hd.mul_left _, by positivity⟩, ?_⟩
      omega
    · have heodd : e % 2 = 1 := by
        rcases Nat.even_or_odd e with hze | hzo
        · exact absurd (hze.two_dvd.trans he) (by omega)
        · exact Nat.odd_iff.mp hzo
      refine ⟨⟨?_, by positivity⟩, ?_⟩
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        rw [pow_succ]
        calc 2 * e ∣ 2 * m := Nat.mul_dvd_mul_left 2 he
          _ ∣ 2 ^ a' * 2 * m := ⟨2 ^ a', by ring⟩
      · omega

lemma sum_not_four (a m : ℕ) (hm : Odd m) (ha : 1 ≤ a) :
    ∑ d ∈ (2 ^ a * m).divisors.filter (¬ 4 ∣ ·), d = 3 * σ 1 m := by
  rw [divisors_filter_not_four a m hm ha, Finset.sum_union, Finset.sum_image,
    ← ArithmeticFunction.sigma_one_apply, ← Finset.mul_sum, ← ArithmeticFunction.sigma_one_apply]
  · ring
  · intro x _ y _ h; simpa using h
  · rw [Finset.disjoint_left]
    intro d hd hd2
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hd2
    have h2 : 2 ∣ m := (Dvd.intro e rfl).trans (Nat.dvd_of_mem_divisors hd)
    have hmodd : m % 2 = 1 := Nat.odd_iff.mp hm
    omega

lemma ordCompl_two_pow_mul (k m : ℕ) (hm : Odd m) : ordCompl[2] (2 ^ k * m) = m := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have : (2 ^ k * m).factorization 2 = k := by
    rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h; have := Nat.odd_iff.mp hm; omega)]
    simp
  rw [this]
  exact Nat.mul_div_cancel_left m (by positivity)

lemma r4_pow_mul (k m : ℕ) (hm : Odd m) (hk : 1 ≤ k) :
    repNum (sumSq 4) ((2 ^ k * m : ℕ) : ℤ) = 24 * σ 1 m := by
  rw [repNum_sumSq_four (Nat.one_le_iff_ne_zero.mpr (by have := hm.pos; positivity)),
    sum_not_four k m hm hk]
  ring

/-- **Moreno–Wagstaff, Theorem 2.6** (p. 29), proved: odd case is `repNum_sumSq_four_odd`; for
$n = 2^a m$ ($a \ge 1$, $m$ odd) the divisors of $n$ not divisible by $4$ are $e, 2e$ ($e \mid m$), giving
$r_4(n) = 8 \cdot 3\sigma(m)$ from Jacobi's formula `repNum_sumSq_four`. -/
@[kb "morenowagstaff2005" "Theorem 2.6, p. 29"]
theorem theorem26 : Theorem26 := by
  intro n hn
  by_cases h : Odd n
  · rw [if_pos h]; exact repNum_sumSq_four_odd h
  · rw [if_neg h]
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (by simpa using hm) h
      · exact hk
    rw [ordCompl_two_pow_mul k m hm]
    exact r4_pow_mul k m hm hk

/-- **Moreno–Wagstaff, Lemma 2.5** (p. 29), proved from the closed form of $r_4(2^k m)$ (Theorem 2.6). -/
@[kb "morenowagstaff2005" "Lemma 2.5, p. 29"]
theorem lemma25 : Lemma25 := by
  intro n hn
  by_cases h : Odd n
  · rw [if_pos h]
    have e : (2 : ℤ) * n = ((2 ^ 1 * n : ℕ) : ℤ) := by push_cast; ring
    rw [e, r4_pow_mul 1 n h le_rfl, repNum_sumSq_four_odd h]
    ring
  · rw [if_neg h]
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (by simpa using hm) h
      · exact hk
    have e : (2 : ℤ) * ((2 ^ k * m : ℕ) : ℤ) = ((2 ^ (k + 1) * m : ℕ) : ℤ) := by push_cast; ring
    rw [e, r4_pow_mul (k + 1) m hm (by omega), r4_pow_mul k m hm hk]

/-! ### Corollary 2.3 and Lemma 2.7 (from Legendre's three-squares theorem) -/

lemma sq_mod_eight_nat (a : ℕ) :
    (a % 2 = 1 ∧ a ^ 2 % 8 = 1) ∨ (a % 2 = 0 ∧ (a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 4)) := by
  have h : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  obtain ⟨r, hr, hra⟩ : ∃ r, r < 8 ∧ a % 8 = r := ⟨_, h, rfl⟩
  rw [Nat.pow_mod, hra]
  interval_cases r <;> omega

lemma not_form_of_mod (N : ℕ) (h : N % 8 = 3) : ¬ ∃ a b : ℕ, N = 4 ^ a * (8 * b + 7) := by
  rintro ⟨a, b, h'⟩
  cases a with
  | zero => simp at h'; omega
  | succ a =>
    have : 4 ∣ N := by
      rw [h']; exact Dvd.dvd.mul_right (dvd_pow_self 4 (Nat.succ_ne_zero a)) _
    omega

lemma odd3_of_mod (a b c : ℕ) (h : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 3) :
    a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 := by
  have h1 := sq_mod_eight_nat a
  have h2 := sq_mod_eight_nat b
  have h3 := sq_mod_eight_nat c
  omega

/-- **Moreno–Wagstaff, Corollary 2.3** (p. 43), proved: $8n + 3 = a^2 + b^2 + c^2$ by Legendre
(`legendre_three_squares`), with $a, b, c$ odd by residues mod 8, $a = 2x + 1$, etc. -/
@[kb "morenowagstaff2005" "Corollary 2.3, p. 43"]
theorem corollary23 : Corollary23 := by
  intro n _
  obtain ⟨a, b, c, h⟩ := (QuadFormsKB.Grosswald.legendre_three_squares (8 * n + 3)).mpr
    (not_form_of_mod _ (by omega))
  obtain ⟨ha, hb, hc⟩ := odd3_of_mod a b c (by omega)
  obtain ⟨x, rfl⟩ : ∃ x, a = 2 * x + 1 := ⟨a / 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 2 * y + 1 := ⟨b / 2, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, c = 2 * z + 1 := ⟨c / 2, by omega⟩
  refine ⟨x, y, z, ?_⟩
  have hx : x * (x + 1) = 2 * (x * (x + 1) / 2) := (Nat.mul_div_cancel' (Nat.even_mul_succ_self x).two_dvd).symm
  have hy : y * (y + 1) = 2 * (y * (y + 1) / 2) := (Nat.mul_div_cancel' (Nat.even_mul_succ_self y).two_dvd).symm
  have hz : z * (z + 1) = 2 * (z * (z + 1) / 2) := (Nat.mul_div_cancel' (Nat.even_mul_succ_self z).two_dvd).symm
  have e : 8 * n + 3 = 4 * (x * (x + 1) + y * (y + 1) + z * (z + 1)) + 3 := by rw [← h]; ring
  omega

/-- **Moreno–Wagstaff, Lemma 2.7** (Cauchy's lemma; p. 55), proved: $4k - s^2 \equiv 3 \pmod 8$ is a sum of three
odd squares $a^2+b^2+c^2$ (Legendre); choose the sign of $c$ with $s + a + b \pm c \equiv 0 \pmod 4$ and set
$t, u, v, w = (s + a + b + c')/4$, etc.; nonnegativity from $a + b + c < s + 4$. -/
@[kb "morenowagstaff2005" "Lemma 2.7, p. 55"]
theorem lemma27 : Lemma27 := by
  intro k s hk hs hlt hk3
  have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk
  have hs2 : s % 2 = 1 := Nat.odd_iff.mp hs
  have hss := sq_mod_eight_nat s
  have hN : (4 * k - s ^ 2) % 8 = 3 := by omega
  obtain ⟨a, b, c, h⟩ := (QuadFormsKB.Grosswald.legendre_three_squares (4 * k - s ^ 2)).mpr
    (not_form_of_mod _ hN)
  obtain ⟨ha, hb, hc⟩ := odd3_of_mod a b c (by omega)
  have hN' : (a : ℤ) ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 = 4 * k := by
    have : a ^ 2 + b ^ 2 + c ^ 2 + s ^ 2 = 4 * k := by omega
    exact_mod_cast this
  have hk3' : 3 * (k : ℤ) < s ^ 2 + 2 * s + 4 := by exact_mod_cast hk3
  have hsum : (a : ℤ) + b + c < s + 4 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [sq_nonneg ((a : ℤ) - b), sq_nonneg ((b : ℤ) - c), sq_nonneg ((a : ℤ) - c),
      (Nat.cast_nonneg s : (0 : ℤ) ≤ s)]
  -- choose the sign of c
  obtain ⟨c', hc', hmod⟩ : ∃ c' : ℤ, (c' = c ∨ c' = -c) ∧ ((s : ℤ) + a + b + c') % 4 = 0 := by
    by_cases hh : ((s : ℤ) + a + b + c) % 4 = 0
    · exact ⟨c, Or.inl rfl, hh⟩
    · exact ⟨-c, Or.inr rfl, by omega⟩
  have hc'2 : c' ^ 2 = (c : ℤ) ^ 2 := by rcases hc' with rfl | rfl <;> ring
  have hc2 : (c' + c) % 2 = 0 := by rcases hc' with rfl | rfl <;> omega
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (s : ℤ) + a + b + c' = 4 * t := ⟨((s : ℤ) + a + b + c') / 4, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℤ, (s : ℤ) + a - b - c' = 4 * u := ⟨((s : ℤ) + a - b - c') / 4, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v : ℤ, (s : ℤ) - a + b - c' = 4 * v := ⟨((s : ℤ) - a + b - c') / 4, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w : ℤ, (s : ℤ) - a - b + c' = 4 * w := ⟨((s : ℤ) - a - b + c') / 4, by omega⟩
  have t0 : 0 ≤ t := by omega
  have u0 : 0 ≤ u := by omega
  have v0 : 0 ≤ v := by omega
  have w0 : 0 ≤ w := by omega
  obtain ⟨t', rfl⟩ := Int.eq_ofNat_of_zero_le t0
  obtain ⟨u', rfl⟩ := Int.eq_ofNat_of_zero_le u0
  obtain ⟨v', rfl⟩ := Int.eq_ofNat_of_zero_le v0
  obtain ⟨w', rfl⟩ := Int.eq_ofNat_of_zero_le w0
  refine ⟨t', u', v', w', ?_, ?_⟩
  · have e : (4 * (t' : ℤ)) ^ 2 + (4 * (u' : ℤ)) ^ 2 + (4 * (v' : ℤ)) ^ 2 + (4 * (w' : ℤ)) ^ 2 =
        4 * ((s : ℤ) ^ 2 + a ^ 2 + b ^ 2 + c' ^ 2) := by
      rw [← ht, ← hu, ← hv, ← hw]; ring
    have : (k : ℤ) = t' ^ 2 + u' ^ 2 + v' ^ 2 + w' ^ 2 := by nlinarith
    exact_mod_cast this
  · omega

/-! ### Remark 2.1 -/

lemma par4 (x : Fin 4 → ℤ) (m : ℤ) (h : ∑ i, x i ^ 2 = 4 * m) :
    (∀ i, x i % 2 = 1) ∨ (∀ i, x i % 2 = 0) := by
  rw [Fin.sum_univ_four] at h
  have h0 := sq_mod_four (x 0)
  have h1 := sq_mod_four (x 1)
  have h2 := sq_mod_four (x 2)
  have h3 := sq_mod_four (x 3)
  have : (x 0 % 2 = 1 ∧ x 1 % 2 = 1 ∧ x 2 % 2 = 1 ∧ x 3 % 2 = 1) ∨
      (x 0 % 2 = 0 ∧ x 1 % 2 = 0 ∧ x 2 % 2 = 0 ∧ x 3 % 2 = 0) := by omega
  rcases this with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · left; intro i; fin_cases i <;> assumption
  · right; intro i; fin_cases i <;> assumption

lemma even_of_not_all_odd (x : Fin 4 → ℤ) (m : ℤ) (h : ∑ i, x i ^ 2 = 4 * m)
    (hn : ¬ ∀ i, Odd (x i)) (i : Fin 4) : x i = 2 * (x i / 2) := by
  rcases par4 x m h with h1 | h0
  · exact absurd (fun i => Int.odd_iff.mpr (h1 i)) hn
  · have := h0 i; omega

lemma card_not_all_odd (m : ℕ) (hm : Odd m) :
    Nat.card {x : {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = 4 * (m : ℤ)} // ¬ ∀ i, Odd (x.1 i)} = 8 * σ 1 m := by
  rw [← repNum_sumSq_four_odd hm]
  unfold repNum
  refine Nat.card_congr
    { toFun := fun x => ⟨fun i => x.1.1 i / 2, ?_⟩
      invFun := fun y => ⟨⟨fun i => 2 * y.1 i, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := x.1.2
    have e := even_of_not_all_odd x.1.1 m h x.2
    rw [mem_repSet_sumSq]
    rw [Fin.sum_univ_four] at h ⊢
    show (x.1.1 0 / 2) ^ 2 + (x.1.1 1 / 2) ^ 2 + (x.1.1 2 / 2) ^ 2 + (x.1.1 3 / 2) ^ 2 = m
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    have e3 := e 3
    generalize x.1.1 0 / 2 = a0 at e0 ⊢
    generalize x.1.1 1 / 2 = a1 at e1 ⊢
    generalize x.1.1 2 / 2 = a2 at e2 ⊢
    generalize x.1.1 3 / 2 = a3 at e3 ⊢
    rw [e0, e1, e2, e3] at h
    nlinarith
  · have h := (mem_repSet_sumSq _ _).mp y.2
    rw [Fin.sum_univ_four] at h ⊢
    nlinarith
  · intro hall
    have := Int.odd_iff.mp (hall 0)
    simp only at this
    omega
  · rintro ⟨⟨x, hx⟩, hn⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have := even_of_not_all_odd x m hx hn i
    simp only
    omega
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    funext i
    simp

lemma ne_zero_of_odd' (x : ℤ) (h : Odd x) : x ≠ 0 := by
  intro h0
  have := Int.odd_iff.mp h
  omega

lemma abs_odd (x : ℤ) (h : Odd x) : Odd |x| := by
  rcases abs_choice x with h' | h' <;> rw [h']
  · exact h
  · exact h.neg

/-- The sign/absolute-value bijection between all-odd solutions and (signs) × (positive odd solutions). -/
def signEquiv (m : ℤ) :
    {x : Fin 4 → ℤ // (∀ i, Odd (x i)) ∧ ∑ i, x i ^ 2 = m} ≃
      (Fin 4 → Bool) × {x : Fin 4 → ℤ // (∀ i, 0 < x i ∧ Odd (x i)) ∧ ∑ i, x i ^ 2 = m} where
  toFun x := (fun i => decide (0 < x.1 i), ⟨fun i => |x.1 i|,
    ⟨fun i => ⟨abs_pos.mpr (ne_zero_of_odd' _ (x.2.1 i)), abs_odd _ (x.2.1 i)⟩,
      by simpa only [sq_abs] using x.2.2⟩⟩)
  invFun p := ⟨fun i => if p.1 i then p.2.1 i else - p.2.1 i,
    fun i => by
      dsimp only
      split_ifs
      exacts [(p.2.2.1 i).2, (p.2.2.1 i).2.neg],
    by
      have h := p.2.2.2
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
      dsimp only
      split_ifs <;> ring⟩
  left_inv := by
    rintro ⟨x, ho, hs⟩
    apply Subtype.ext
    funext i
    dsimp only
    have := ne_zero_of_odd' _ (ho i)
    rcases lt_or_gt_of_ne this with h | h
    · simp [not_lt.mpr h.le, abs_of_neg h]
    · simp [h, abs_of_pos h]
  right_inv := by
    rintro ⟨b, y, hy, hs⟩
    refine Prod.ext ?_ (Subtype.ext ?_)
    · funext i
      have := (hy i).1
      show decide (0 < (if b i then y i else -y i)) = b i
      cases hb : b i <;> simp [this, this.le]
    · funext i
      have := (hy i).1
      show |(if b i then y i else -y i)| = y i
      cases hb : b i <;> simp [this, this.le, abs_of_pos]

/-- **Moreno–Wagstaff, Remark 2.1** (p. 33), proved: for odd $m$ the solutions of $\sum x_i^2 = 4m$ are all-odd or
all-even (mod 4); the all-even ones biject with representations of $m$ ($8\sigma(m)$), so the all-odd count is
$r_4(4m) - r_4(m) = 24\sigma(m) - 8\sigma(m) = 16\sigma(m)$; signs act freely, giving $\sigma(m)$ positive ones. -/
@[kb "morenowagstaff2005" "Remark 2.1, p. 33"]
theorem remark21 : Remark21 := by
  intro m hm
  have hT : Nat.card {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = 4 * (m : ℤ)} = 24 * σ 1 m := by
    have := r4_pow_mul 2 m hm (by norm_num)
    have e : ((2 ^ 2 * m : ℕ) : ℤ) = 4 * (m : ℤ) := by push_cast; ring
    rw [e] at this
    rw [← this]
    unfold repNum
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (mem_repSet_sumSq x _).symm)
  have hpos : 0 < σ 1 m := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd) ⟨1, Nat.one_mem_divisors.mpr hm.pos.ne'⟩
  haveI : Finite {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = 4 * (m : ℤ)} :=
    Nat.finite_of_card_ne_zero (by omega)
  have hsplit : Nat.card {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = 4 * (m : ℤ)} =
      Nat.card {x : Fin 4 → ℤ // (∀ i, Odd (x i)) ∧ ∑ i, x i ^ 2 = 4 * (m : ℤ)} +
      Nat.card {x : {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = 4 * (m : ℤ)} // ¬ ∀ i, Odd (x.1 i)} := by
    have e1 : {x : {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = 4 * (m : ℤ)} // ∀ i, Odd (x.1 i)} ≃
        {x : Fin 4 → ℤ // (∀ i, Odd (x i)) ∧ ∑ i, x i ^ 2 = 4 * (m : ℤ)} :=
      { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Nat.card_congr e1,
      ← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (fun x : {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = 4 * (m : ℤ)} =>
        ∀ i, Odd (x.1 i)))]
  have h1 : Nat.card {x : Fin 4 → ℤ // (∀ i, Odd (x i)) ∧ ∑ i, x i ^ 2 = 4 * (m : ℤ)} = 16 * σ 1 m := by
    have := card_not_all_odd m hm
    omega
  refine ⟨h1, ?_⟩
  have h2 := Nat.card_congr (signEquiv (4 * (m : ℤ)))
  rw [Nat.card_prod] at h2
  have h16 : Nat.card (Fin 4 → Bool) = 16 := by simp [Nat.card_eq_fintype_card]
  rw [h16] at h2
  unfold oddSqRep
  omega

end QuadFormsKB.MorenoWagstaff

