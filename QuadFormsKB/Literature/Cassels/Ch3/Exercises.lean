/-
# Cassels, Chapter 3: Examples (exercises), pp. 49–54

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *Examples*, pp. 49–54.

**Setting.** $p$ is a prime (`[Fact p.Prime]`), $\mathbb Q_p$ = `ℚ_[p]`, $\mathbb Z_p$ = `ℤ_[p]`, and $|\cdot|_p$ is the
norm `‖·‖` on `ℚ_[p]` (on rationals, `padicNorm p`). Matrices are `Matrix (Fin n) (Fin n) ℤ_[p]`; indices are $0$-based.

**Proves.**
* Ex. 5 (p. 49): $\binom{a}{n} = a(a-1)\cdots(a-n+1)/n! \in \mathbb Z_p$ for $a \in \mathbb Z_p$ (`ex5`).
* Ex. 6 (p. 49): for $p \ne 2$ and $|c|_p < 1$ the binomial series $\sum_n \binom{1/2}{n}c^{n}$ converges to a
  square root of $1 + c$ (`ex6`).
* Ex. 8 (p. 50): $|a^{2} - 1|_p = |a - 1|_p$ for $p \ne 2$; for $p = 2$, $\le |a-1|_2/2$ with equality when
  $|a-1|_2 < 1/2$ (`ex8_odd`, `ex8_two`).
* Ex. 14 (pp. 50–51): for $p > 2$, a matrix $A \equiv I \pmod p$, $A \ne I$ over $\mathbb Z_p$ has infinite order
  (`ex14_i`), and a finite group of invertible matrices over $\mathbb Z_p$ has order dividing
  $\prod_{j<n}(p^{n} - p^{j})$ (`ex14_ii`).
* Ex. 17 (p. 52): $ax^{2} + bx + c$ with integer coefficients, $a \ne 0$, has a root in $\mathbb Z_p$ for infinitely
  many primes $p$ (`ex17`, with the Hensel step `exists_root_of_dvd_value`, a variant of Ex. 13 for integer
  coefficients).
* Ex. 19 (p. 52): for $a_{ij} \to 0$ in $\mathbb Q_p$ the iterated sums agree, $\sum_i\sum_j a_{ij} =
  \sum_j\sum_i a_{ij}$ (`ex19`).
* Ex. 21 (pp. 52–53): Strassmann's theorem, a power series $\sum c_n x^{n}$ over $\mathbb Z_p$ with $c_n \to 0$ has
  at most $N$ zeros in $\mathbb Z_p$ where $N$ is the last index of the maximal $|c_n|_p$ (`ex21`; the index exists
  by `exists_strassmann_index`).
* Ex. 18 (p. 52): $|m!|_p = p^{-M}$ with $M = \sum_{j \ge 1}\lfloor m/p^{j}\rfloor$, and $M < m/(p-1)$
  (`ex18_norm_factorial`, `ex18_lt`).

**Elsewhere:** Ex. 1, 2, 3, 4, 7, 9 (read from the page images) are proved in `Ch3/ExamplesScan.lean`, Ex. 20 in
`Ch3/Ex20.lean`; Ex. 12, 13 and 15 in `Ch3/ExercisesHensel.lean`, Ex. 16 (Minkowski's bound) in `Ch3/Minkowski.lean`.
**Not formalized here:** Ex. 10 (proved in `Ch3/ExerciseTen.lean`), Ex. 11 (cited on
`HilbertLocal.hilbertSymbol_odd_formula`), Ex. 22, 23, 24 (the book calls Ex. 17–24 "unrelated to the main theme of
the book", p. 51; out of scope for now).
-/
import Mathlib
import QuadFormsKB.Citation

open Filter Topology

noncomputable section

namespace QuadFormsKB.Cassels.Ch3Ex

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Cassels, Ch. 3, Ex. 18 (p. 52).** For a positive integer $m$ and a prime $p$,
$|m!|_p = p^{-M}$ where $M = \sum_{j \ge 1}\lfloor m/p^{j}\rfloor$ (Legendre's formula). The sum is finite: terms with
$p^{j} > m$ vanish, so it is taken over $1 \le j \le m$. -/
@[kb "cassels1978" "Ch. 3, Ex. 18, p. 52"]
theorem ex18_norm_factorial (m : ℕ) :
    padicNorm p (m.factorial : ℚ) = (p : ℚ) ^ (-((∑ j ∈ Finset.Ico 1 (m + 1), m / p ^ j : ℕ) : ℤ)) := by
  have hne : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [padicNorm.eq_zpow_of_nonzero hne, padicValRat.of_nat,
    padicValNat_factorial (Nat.lt_succ_of_le (Nat.log_le_self p m))]

/-- **Cassels, Ch. 3, Ex. 18 (p. 52), second part.** With $M = \sum_{j \ge 1}\lfloor m/p^{j}\rfloor$ as above and
$m \ge 1$, $M < m/(p-1)$. -/
@[kb "cassels1978" "Ch. 3, Ex. 18, p. 52"]
theorem ex18_lt {m : ℕ} (hm : 1 ≤ m) :
    ((∑ j ∈ Finset.Ico 1 (m + 1), m / p ^ j : ℕ) : ℚ) < (m : ℚ) / ((p : ℚ) - 1) := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := m) (by omega)
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  rw [lt_div_iff₀ (by linarith)]
  have h' : ((p - 1 : ℕ) : ℚ) * (padicValNat p m.factorial : ℚ) < m := by exact_mod_cast h
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one] at h'
  rw [← padicValNat_factorial (Nat.lt_succ_of_le (Nat.log_le_self p m))]
  linarith

/-- For a natural number `m`, the falling product $\prod_{i<n}(m - i)$ in $\mathbb Q_p$ is the cast of
`Nat.descFactorial`. -/
theorem prod_range_natCast_sub (m n : ℕ) :
    ∏ i ∈ Finset.range n, ((m : ℚ_[p]) - i) = (m.descFactorial n : ℚ_[p]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
    by_cases h : n ≤ m
    · rw [Nat.cast_mul, Nat.cast_sub h]; ring
    · have h0 : m.descFactorial n = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0]; simp

/-- **Cassels, Ch. 3, Ex. 5 (p. 49).** For $a \in \mathbb Z_p$ and a positive integer $n$,
$\binom{a}{n} = a(a-1)\cdots(a-n+1)/n!$ lies in $\mathbb Z_p$: the element of $\mathbb Q_p$ given by this formula has
$p$-adic norm at most $1$. (Hint: approximate $a$ by positive integers.) -/
@[kb "cassels1978" "Ch. 3, Ex. 5, p. 49"]
theorem ex5 (a : ℤ_[p]) (n : ℕ) (_hn : 1 ≤ n) :
    ‖(∏ i ∈ Finset.range n, ((a : ℚ_[p]) - i)) / (n.factorial : ℚ_[p])‖ ≤ 1 := by
  refine (PadicInt.denseRange_natCast (p := p)).induction_on a ?_ ?_
  · exact isClosed_le (by fun_prop) continuous_const
  · intro m
    have hf : (n.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have : (∏ i ∈ Finset.range n, (((m : ℤ_[p]) : ℚ_[p]) - i)) / (n.factorial : ℚ_[p]) =
        (m.choose n : ℚ_[p]) := by
      rw [PadicInt.coe_natCast, prod_range_natCast_sub, Nat.descFactorial_eq_factorial_mul_choose,
        Nat.cast_mul]
      field_simp
    rw [this]
    have := PadicInt.norm_le_one (m.choose n : ℤ_[p])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this

/-- For $p \ne 2$ the binomial coefficients $\binom{1/2}{n}$ of $\mathbb Q_p$ have $p$-adic norm at most $1$
(the case $a = 1/2 \in \mathbb Z_p$ of Ex. 5). -/
theorem norm_choose_half_le_one (hp2 : p ≠ 2) (n : ℕ) :
    ‖Ring.choose (1 / 2 : ℚ_[p]) n‖ ≤ 1 := by
  have h2 : ‖(2 : ℚ_[p])‖ = 1 := by
    have h := Padic.norm_natCast_eq_one_iff (p := p) (n := 2)
    have : p.Coprime 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
    simpa using h.mpr this
  have hx : ‖(1 / 2 : ℚ_[p])‖ ≤ 1 := by simp [h2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h5 := ex5 (⟨1 / 2, hx⟩ : ℤ_[p]) n hn
  have hc : Ring.choose (1 / 2 : ℚ_[p]) n =
      (∏ i ∈ Finset.range n, ((((⟨1 / 2, hx⟩ : ℤ_[p])) : ℚ_[p]) - i)) / (n.factorial : ℚ_[p]) := by
    rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]
    simp [div_eq_inv_mul]
  rw [hc]
  exact h5

/-- **Cassels, Ch. 3, Ex. 6 (p. 49).** Let $p \ne 2$ and $c \in \mathbb Q_p$ with $|c|_p < 1$. Then the binomial
series $\sum_{n \ge 0}\binom{1/2}{n}c^{n}$, with $\binom{1/2}{n} = \tfrac12(\tfrac12 - 1)\cdots(\tfrac12 - n + 1)/n!$
(Mathlib's `Ring.choose`), converges to a square root of $1 + c$. (The "hence or otherwise" part of the book's
exercise, finding a specific square root, is garbled in the machine-read text and is not formalized.) -/
@[kb "cassels1978" "Ch. 3, Ex. 6, p. 49"]
theorem ex6 (hp2 : p ≠ 2) (c : ℚ_[p]) (hc : ‖c‖ < 1) :
    ∃ y : ℚ_[p], HasSum (fun n : ℕ => Ring.choose (1 / 2 : ℚ_[p]) n * c ^ n) y ∧ y ^ 2 = 1 + c := by
  set f : ℕ → ℚ_[p] := fun n => Ring.choose (1 / 2 : ℚ_[p]) n * c ^ n with hf
  have hnorm : Summable fun n => ‖f n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg c) hc)
    rw [hf]; dsimp only
    rw [norm_mul, norm_pow]
    calc _ ≤ 1 * ‖c‖ ^ n := by
          gcongr
          exact norm_choose_half_le_one hp2 n
      _ = ‖c‖ ^ n := one_mul _
  have hsum : Summable f := hnorm.of_norm
  refine ⟨∑' n, f n, hsum.hasSum, ?_⟩
  rw [pow_two, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm]
  have hser : PowerSeries.binomialSeries ℚ_[p] (1 / 2 : ℚ_[p]) *
      PowerSeries.binomialSeries ℚ_[p] (1 / 2 : ℚ_[p]) = 1 + PowerSeries.X := by
    rw [← PowerSeries.binomialSeries_add]
    have : (1 / 2 : ℚ_[p]) + 1 / 2 = ((1 : ℕ) : ℚ_[p]) := by
      have : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
      push_cast; field_simp; norm_num
    rw [this, PowerSeries.binomialSeries_nat, pow_one]
  have hcoef : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, f kl.1 * f kl.2 =
      c ^ n * PowerSeries.coeff n (1 + PowerSeries.X : PowerSeries ℚ_[p]) := by
    intro n
    have h := congrArg (PowerSeries.coeff n) hser
    rw [PowerSeries.coeff_mul] at h
    simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
    rw [hf]; dsimp only
    rw [← this, pow_add]; ring
  simp_rw [hcoef]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, PowerSeries.coeff_one, PowerSeries.coeff_X]
  · intro n hn
    have : 2 ≤ n := by simp at hn; omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le this
    have h1 : 2 + m ≠ 1 := by omega
    simp [PowerSeries.coeff_one, PowerSeries.coeff_X, h1]

/-- **Cassels, Ch. 3, Ex. 8 (p. 50), odd primes.** Let $p \ne 2$ and $a \in \mathbb Z_p$ with $|a - 1|_p < 1$. Then
$|a^{2} - 1|_p = |a - 1|_p$. -/
@[kb "cassels1978" "Ch. 3, Ex. 8, p. 50"]
theorem ex8_odd (hp2 : p ≠ 2) (a : ℤ_[p]) (ha : ‖a - 1‖ < 1) : ‖a ^ 2 - 1‖ = ‖a - 1‖ := by
  have h2 : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
  have h2' : ‖(2 : ℤ_[p])‖ = 1 := by simpa using h2
  have hne : ‖a - 1‖ ≠ ‖(2 : ℤ_[p])‖ := by rw [h2']; exact ha.ne
  have hadd : ‖a + 1‖ = 1 := by
    have : a + 1 = (a - 1) + 2 := by ring
    rw [this, PadicInt.norm_add_eq_max_of_ne hne, h2']
    exact max_eq_right ha.le
  have : a ^ 2 - 1 = (a - 1) * (a + 1) := by ring
  rw [this, norm_mul, hadd, mul_one]

/-- **Cassels, Ch. 3, Ex. 8 (p. 50), the prime $p = 2$.** The book asks only for "the corresponding result for
$p = 2$"; this is the reconstruction. Let $a \in \mathbb Z_2$ with $|a - 1|_2 < 1$. Then
$|a^{2} - 1|_2 \le |a - 1|_2 / 2$, with equality when $|a - 1|_2 < 1/2$. -/
@[kb "cassels1978" "Ch. 3, Ex. 8, p. 50"]
theorem ex8_two (a : ℤ_[2]) (ha : ‖a - 1‖ < 1) :
    ‖a ^ 2 - 1‖ ≤ ‖a - 1‖ / 2 ∧ (‖a - 1‖ < 1 / 2 → ‖a ^ 2 - 1‖ = ‖a - 1‖ / 2) := by
  have h2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
    have := PadicInt.norm_p (p := 2)
    simpa [one_div] using this
  obtain ⟨y, hy⟩ : (2 : ℤ_[2]) ∣ a - 1 := by
    have := (PadicInt.norm_lt_one_iff_dvd (p := 2) (a - 1)).mp ha
    simpa using this
  have hsq : a ^ 2 - 1 = (a - 1) * (a + 1) := by ring
  have hx : a + 1 = (a - 1) + 2 := by ring
  have hy1 : ‖y‖ ≤ 1 := PadicInt.norm_le_one y
  have hxy : ‖a + 1‖ ≤ 1 / 2 := by
    have : a + 1 = 2 * (y + 1) := by linear_combination hy
    rw [this, norm_mul, h2]
    have := PadicInt.norm_le_one (y + 1)
    nlinarith [norm_nonneg (y + 1)]
  constructor
  · rw [hsq, norm_mul]
    nlinarith [norm_nonneg (a - 1)]
  · intro hlt
    have hne : ‖a - 1‖ ≠ ‖(2 : ℤ_[2])‖ := by rw [h2]; exact hlt.ne
    have : ‖a + 1‖ = 1 / 2 := by
      rw [hx, PadicInt.norm_add_eq_max_of_ne hne, h2]
      exact max_eq_right hlt.le
    rw [hsq, norm_mul, this]
    ring

section Ex14

variable {n : ℕ}

/-- A matrix $A$ over $\mathbb Z_p$ is congruent to the identity modulo $p$: every entry of $A - 1$ is divisible
by $p$. -/
def CongOne (A : Matrix (Fin n) (Fin n) ℤ_[p]) : Prop :=
  ∀ i j, ((p : ℕ) : ℤ_[p]) ∣ (A - 1) i j

theorem CongOne.mul {A B : Matrix (Fin n) (Fin n) ℤ_[p]} (hA : CongOne A) (hB : CongOne B) :
    CongOne (A * B) := by
  intro i j
  have : (A * B - 1) i j = (A * (B - 1)) i j + (A - 1) i j := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.sub_apply]; ring
  rw [this]
  refine dvd_add ?_ (hA i j)
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hB k j) _

theorem CongOne.one : CongOne (1 : Matrix (Fin n) (Fin n) ℤ_[p]) := by
  intro i j; simp

theorem CongOne.pow {A : Matrix (Fin n) (Fin n) ℤ_[p]} (hA : CongOne A) (m : ℕ) : CongOne (A ^ m) := by
  induction m with
  | zero => simpa using CongOne.one
  | succ m ih => rw [pow_succ]; exact ih.mul hA

/-- An element of $\mathbb Z_p$ divisible by every power of $p$ is zero. -/
theorem eq_zero_of_forall_pow_dvd {x : ℤ_[p]} (h : ∀ r : ℕ, ((p : ℕ) : ℤ_[p]) ^ r ∣ x) : x = 0 := by
  by_contra hx
  have := (PadicInt.mem_span_pow_iff_le_valuation x hx (x.valuation + 1)).mp
    (Ideal.mem_span_singleton.mpr (h _))
  omega

theorem exists_smul_of_dvd {D : Matrix (Fin n) (Fin n) ℤ_[p]} (h : ∀ i j, ((p : ℕ) : ℤ_[p]) ∣ D i j) :
    ∃ D' : Matrix (Fin n) (Fin n) ℤ_[p], D = ((p : ℕ) : ℤ_[p]) • D' := by
  refine ⟨Matrix.of fun i j => (h i j).choose, ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (h i j).choose_spec

/-- Binomial expansion $(1 + C)^{s+2} = 1 + (s+2)C + C^{2}N$ with $N = \sum_{j \le s}\binom{s+2}{j+2}C^{j}$. -/
theorem one_add_pow_expand (C : Matrix (Fin n) (Fin n) ℤ_[p]) (s : ℕ) :
    (1 + C) ^ (s + 2) = 1 + (s + 2) • C +
      C ^ 2 * ∑ j ∈ Finset.range (s + 1), ((s + 2).choose (j + 2)) • C ^ j := by
  rw [add_comm 1 C, (Commute.one_right C).add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  have h2 : ∀ m ∈ Finset.range (s + 1), C ^ (m + 1 + 1) * 1 ^ (s + 2 - (m + 1 + 1)) *
      (((s + 2).choose (m + 1 + 1) : ℕ) : Matrix (Fin n) (Fin n) ℤ_[p]) =
      C ^ 2 * (((s + 2).choose (m + 2)) • C ^ m) := by
    intro m _
    rw [one_pow, mul_one, nsmul_eq_mul, show m + 1 + 1 = m + 2 from rfl, pow_add C m 2,
      (Commute.pow_pow_self C m 2).eq]
    simp only [mul_assoc]
    rw [(Nat.cast_commute _ (C ^ m)).eq]
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  simp only [zero_add, pow_one, pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, nsmul_eq_mul]
  rw [(Nat.cast_commute (s + 2) C).eq]
  abel

theorem p_ne_zero' : ((p : ℕ) : ℤ_[p]) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

/-- `p` does not divide a prime `q ≠ p`, as an element of $\mathbb Z_p$. -/
theorem not_dvd_natCast {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) : ¬ ((p : ℕ) : ℤ_[p]) ∣ (q : ℤ_[p]) := by
  rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff]
  intro h
  exact hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp h).symm

/-- Key step of Ex. 14 (i): if $C = p^{r}D$ with $r \ge 1$ and $(1 + C)^{q} = 1$ for a prime $q$ (with $p$ odd),
then every entry of $D$ is divisible by $p$. -/
theorem entries_dvd_of_pow_eq_one (hp2 : p ≠ 2) {s : ℕ} (hq : (s + 2).Prime)
    {C D : Matrix (Fin n) (Fin n) ℤ_[p]} {r : ℕ} (hr : 1 ≤ r)
    (hC : C = ((p : ℕ) : ℤ_[p]) ^ r • D) (hpow : (1 + C) ^ (s + 2) = 1) :
    ∀ i j, ((p : ℕ) : ℤ_[p]) ∣ D i j := by
  set P : ℤ_[p] := ((p : ℕ) : ℤ_[p]) with hP
  have hP0 : P ≠ 0 := p_ne_zero'
  set N := ∑ j ∈ Finset.range (s + 1), ((s + 2).choose (j + 2)) • C ^ j with hN
  have h0 : (s + 2) • C + C ^ 2 * N = 0 := by
    have h := one_add_pow_expand C s
    rw [hpow, add_assoc] at h
    exact left_eq_add.mp h
  by_cases hqp : s + 2 = p
  · -- the case q = p
    have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
    obtain ⟨C', hC'⟩ : ∃ C' : Matrix (Fin n) (Fin n) ℤ_[p], C = P • C' :=
      ⟨P ^ (r - 1) • D, by rw [hC, smul_smul, ← pow_succ' P (r - 1), Nat.sub_add_cancel hr]⟩
    have hNdiv : ∃ N' : Matrix (Fin n) (Fin n) ℤ_[p], N = P • N' := by
      refine Finset.sum_induction _ (fun M => ∃ M' : Matrix (Fin n) (Fin n) ℤ_[p], M = P • M')
        ?_ ⟨0, by simp⟩ ?_
      · rintro a b ⟨a', rfl⟩ ⟨b', rfl⟩
        exact ⟨a' + b', by rw [smul_add]⟩
      · intro j hj
        have hj' : j < s + 1 := Finset.mem_range.mp hj
        by_cases hlt : j + 2 < p
        · obtain ⟨m, hm⟩ := hp.out.dvd_choose_self (k := j + 2) (by omega) hlt
          refine ⟨m • C ^ j, ?_⟩
          rw [hqp, hm, mul_smul, hP, ← Nat.cast_smul_eq_nsmul ℤ_[p] p]
        · have hjs : j = s := by omega
          obtain ⟨t, ht⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
          have e : C ^ j = P • (C ^ t * C') := by
            have h3 : C ^ t * C = P • (C ^ t * C') := by rw [← Matrix.mul_smul, ← hC']
            rw [ht, pow_succ, h3]
          refine ⟨((s + 2).choose (j + 2)) • (C ^ t * C'), ?_⟩
          rw [e]
          exact smul_comm _ _ _
    obtain ⟨N', hN'⟩ := hNdiv
    have h1 : P ^ (r + 1) • (D + P ^ r • (D * D * N')) = 0 := by
      rw [← h0, hqp, hN', hC]
      simp only [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ← Nat.cast_smul_eq_nsmul ℤ_[p]]
      rw [← hP]
      module
    intro i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.add_apply] at h2
    have h3 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hP0)
    rw [eq_neg_of_add_eq_zero_left h3]
    exact dvd_neg.mpr (Dvd.dvd.mul_right (dvd_pow_self P (by omega)) _)
  · have h1 : P ^ r • (((s + 2 : ℕ) : ℤ_[p]) • D + P ^ r • (D * D * N)) = 0 := by
      rw [← h0, hC]
      simp only [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ← Nat.cast_smul_eq_nsmul ℤ_[p]]
      module
    intro i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.add_apply] at h2
    have h3 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hP0)
    have hdiv : P ∣ ((s + 2 : ℕ) : ℤ_[p]) * D i j := by
      rw [eq_neg_of_add_eq_zero_left h3]
      exact dvd_neg.mpr (Dvd.dvd.mul_right (dvd_pow_self P (by omega)) _)
    rcases (PadicInt.prime_p (p := p)).dvd_or_dvd hdiv with h | h
    · exact absurd h (not_dvd_natCast hq hqp)
    · exact h

/-- For $p$ odd, a matrix $A \equiv 1 \pmod p$ with $A \ne 1$ satisfies $A^{q} \ne 1$ for every prime $q$. -/
theorem pow_prime_ne_one (hp2 : p ≠ 2) {q : ℕ} (hq : q.Prime) {A : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hA : CongOne A) (hne : A ≠ 1) : A ^ q ≠ 1 := by
  intro hpow
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 2 := ⟨q - 2, by have := hq.two_le; omega⟩
  set P : ℤ_[p] := ((p : ℕ) : ℤ_[p]) with hP
  have hAC : A = 1 + (A - 1) := by abel
  have hpow' : (1 + (A - 1)) ^ (s + 2) = 1 := by rw [← hAC]; exact hpow
  have key : ∀ r : ℕ, 1 ≤ r → ∃ D : Matrix (Fin n) (Fin n) ℤ_[p], A - 1 = P ^ r • D := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
      obtain ⟨D, hD⟩ := exists_smul_of_dvd hA
      exact ⟨D, by rw [pow_one]; exact hD⟩
    | succ r hr ih =>
      obtain ⟨D, hD⟩ := ih
      obtain ⟨D', hD'⟩ := exists_smul_of_dvd
        (entries_dvd_of_pow_eq_one hp2 hq hr hD hpow')
      exact ⟨D', by rw [hD, hD', smul_smul, ← pow_succ]⟩
  apply hne
  have h0 : A - 1 = 0 := by
    refine Matrix.ext fun i j => eq_zero_of_forall_pow_dvd fun r => ?_
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · obtain ⟨D, hD⟩ := key r hr
      rw [hD]
      exact ⟨D i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩
  exact sub_eq_zero.mp h0

/-- **Cassels, Ch. 3, Ex. 14 (i) (p. 50).** Let $p > 2$ be prime and $A$ an $n \times n$ matrix over $\mathbb Z_p$
with $A \equiv I \pmod p$ (every entry of $A - I$ divisible by $p$) but $A \ne I$. Then $A$ has infinite order in the
multiplicative monoid of $n \times n$ matrices: $A^{k} \ne I$ for all $k \ge 1$. -/
@[kb "cassels1978" "Ch. 3, Ex. 14 (i), p. 50"]
theorem ex14_i (hp2 : p ≠ 2) {A : Matrix (Fin n) (Fin n) ℤ_[p]} (hA : ∀ i j, ((p : ℕ) : ℤ_[p]) ∣ (A - 1) i j)
    (hne : A ≠ 1) (k : ℕ) (hk : 1 ≤ k) : A ^ k ≠ 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1
    by_cases hk1' : k = 1
    · subst hk1'; exact hne (by simpa using hk1)
    · obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1'
      obtain ⟨m, rfl⟩ := hqk
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hk
        · exact h
      have hmlt : m < q * m := by
        have := hq.two_le; nlinarith
      have hBne : A ^ m ≠ 1 := ih m hmlt hm
      have hB : CongOne (A ^ m) := (show CongOne A from hA).pow m
      apply pow_prime_ne_one hp2 hq hB hBne
      rw [← pow_mul, mul_comm]; exact hk1

/-- An element of $\mathbb Z_p$ with zero residue modulo $p$ is divisible by $p$. -/
theorem dvd_of_toZMod_eq_zero {x : ℤ_[p]} (h : PadicInt.toZMod x = 0) : ((p : ℕ) : ℤ_[p]) ∣ x := by
  have hx : x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h
  rw [PadicInt.ker_toZMod] at hx
  rw [← PadicInt.norm_lt_one_iff_dvd]
  have hn : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hx
  rw [PadicInt.isUnit_iff] at hn
  exact lt_of_le_of_ne (PadicInt.norm_le_one x) hn

/-- **Cassels, Ch. 3, Ex. 14 (ii) (p. 51).** Let $p > 2$ be prime and $G$ a finite group of invertible $n \times n$
matrices over $\mathbb Z_p$. Then $|G|$ divides $|GL_n(\mathbb F_p)| = \prod_{j=0}^{n-1}(p^{n} - p^{j})$.
(Reduction modulo $p$ is injective on $G$ by part (i).) *Reconstruction:* the order bound is garbled in the
machine-read text; it is reconstructed from the hint (the order of $GL_n(\mathbb F_p)$, Ch. 2 Ex. 12). -/
@[kb "cassels1978" "Ch. 3, Ex. 14 (ii), p. 51"]
theorem ex14_ii (hp2 : p ≠ 2) (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℤ_[p])) [Finite G] :
    Nat.card G ∣ ∏ i ∈ Finset.range n, (p ^ n - p ^ i) := by
  let f : G →* Matrix.GeneralLinearGroup (Fin n) (ZMod p) :=
    (Matrix.GeneralLinearGroup.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).comp G.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg1 : ((g : Matrix.GeneralLinearGroup (Fin n) ℤ_[p]) : Matrix (Fin n) (Fin n) ℤ_[p]).map
        PadicInt.toZMod = 1 := by
      have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin n) (ZMod p) =>
        (u : Matrix (Fin n) (Fin n) (ZMod p))) hg
      simpa [f, Matrix.GeneralLinearGroup.map] using this
    have hcong : CongOne ((g : Matrix.GeneralLinearGroup (Fin n) ℤ_[p]) : Matrix (Fin n) (Fin n) ℤ_[p]) := by
      intro i j
      apply dvd_of_toZMod_eq_zero
      have := congrFun (congrFun hg1 i) j
      simp only [Matrix.map_apply] at this
      simp only [Matrix.sub_apply, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    obtain ⟨k, hk, hk1⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
    have hmat : (((g : Matrix.GeneralLinearGroup (Fin n) ℤ_[p]) : Matrix (Fin n) (Fin n) ℤ_[p])) = 1 := by
      by_contra hne
      refine ex14_i hp2 hcong hne k hk ?_
      have := congrArg (fun u : G => ((u : Matrix.GeneralLinearGroup (Fin n) ℤ_[p]) :
        Matrix (Fin n) (Fin n) ℤ_[p])) hk1
      simpa using this
    exact Subtype.ext (Units.ext hmat)
  have hdvd := Subgroup.card_dvd_of_injective f hinj
  have : Fintype (ZMod p) := ZMod.fintype p
  rw [Matrix.card_GL_field, ZMod.card] at hdvd
  rwa [Fin.prod_univ_eq_prod_range (fun i => p ^ n - p ^ i) n] at hdvd

end Ex14

/-- Hensel step for a quadratic: if a prime $q$ divides the value $f(m)$ of $f = ax^{2} + bx + c$ (integers) but not
its discriminant $b^{2} - 4ac$, then $f$ has a root in $\mathbb Z_q$. (Cf. Ex. 13.) -/
theorem exists_root_of_dvd_value {a b c m : ℤ} (hD : ¬ (p : ℤ) ∣ b ^ 2 - 4 * a * c)
    (hdvd : (p : ℤ) ∣ a * m ^ 2 + b * m + c) :
    ∃ u : ℤ_[p], (a : ℤ_[p]) * u ^ 2 + b * u + c = 0 := by
  let F : Polynomial ℤ_[p] :=
    Polynomial.C (a : ℤ_[p]) * Polynomial.X ^ 2 + Polynomial.C (b : ℤ_[p]) * Polynomial.X +
      Polynomial.C (c : ℤ_[p])
  have hF : F.aeval (m : ℤ_[p]) = ((a * m ^ 2 + b * m + c : ℤ) : ℤ_[p]) := by
    simp [F]
  have hF' : F.derivative.aeval (m : ℤ_[p]) = ((2 * a * m + b : ℤ) : ℤ_[p]) := by
    simp [F]
    ring
  have h1 : ‖F.aeval (m : ℤ_[p])‖ < 1 := by
    rw [hF, PadicInt.norm_int_lt_one_iff_dvd]; exact hdvd
  have h2 : ‖F.derivative.aeval (m : ℤ_[p])‖ = 1 := by
    rw [hF']
    refine (lt_or_eq_of_le (PadicInt.norm_le_one _)).resolve_left ?_
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro hd
    apply hD
    have : b ^ 2 - 4 * a * c = (2 * a * m + b) * (2 * a * m + b) - 4 * a * (a * m ^ 2 + b * m + c) := by
      ring
    rw [this]
    exact dvd_sub (hd.mul_right _) (hdvd.mul_left _)
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (m : ℤ_[p])) (by rw [h2]; simpa using h1)
  exact ⟨z, by simpa [F] using hz⟩

/-- **Cassels, Ch. 3, Ex. 17 (p. 52).** Let $f(x) = ax^{2} + bx + c$ with $a, b, c \in \mathbb Z$ and $a \ne 0$. Then
there are infinitely many primes $p$ for which $f$ has a root $u_p \in \mathbb Z_p$. -/
@[kb "cassels1978" "Ch. 3, Ex. 17, p. 52"]
theorem ex17 (a b c : ℤ) (ha : a ≠ 0) :
    {p : ℕ | ∃ _ : Fact p.Prime, ∃ u : ℤ_[p], (a : ℤ_[p]) * u ^ 2 + b * u + c = 0}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  by_cases hD : b ^ 2 - 4 * a * c = 0
  · -- the discriminant vanishes: the root is $-b/(2a)$, which is a $p$-adic integer for $p \nmid 2a$
    obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (N + (2 * a).natAbs + 1)
    have : Fact q.Prime := ⟨hq⟩
    have hqa : ¬ (q : ℤ) ∣ 2 * a := by
      intro h
      have := Int.le_of_dvd (by simpa using ha) ((Int.dvd_natAbs).mpr h)
      omega
    have hu : IsUnit ((2 * a : ℤ) : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff]
      refine (lt_or_eq_of_le (PadicInt.norm_le_one _)).resolve_left ?_
      rw [PadicInt.norm_int_lt_one_iff_dvd]; exact hqa
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    refine ⟨q, ⟨⟨hq⟩, -(b : ℤ_[q]) * w, ?_⟩, by omega⟩
    have h4 : (4 * a : ℤ_[q]) * ((a : ℤ_[q]) * (-(b : ℤ_[q]) * w) ^ 2 + b * (-(b : ℤ_[q]) * w) + c) = 0 := by
      have e : (4 * a * ((a : ℤ_[q]) * (-(b : ℤ_[q]) * w) ^ 2 + b * (-(b : ℤ_[q]) * w) + c)) =
          ((2 * a : ℤ) * (-(b : ℤ_[q]) * w) + b) ^ 2 - ((b ^ 2 - 4 * a * c : ℤ) : ℤ_[q]) := by
        push_cast; ring
      rw [e, hD]
      have : ((2 * a : ℤ) : ℤ_[q]) * (-(b : ℤ_[q]) * w) + b = 0 := by
        calc _ = -(b : ℤ_[q]) * (((2 * a : ℤ) : ℤ_[q]) * w) + b := by ring
          _ = 0 := by rw [hw]; ring
      rw [this]; simp
    have h4a : (4 * a : ℤ_[q]) ≠ 0 := by
      have : ((4 * a : ℤ) : ℤ_[q]) ≠ 0 := by exact_mod_cast (by omega : (4 * a : ℤ) ≠ 0)
      simpa using this
    exact (mul_eq_zero.mp h4).resolve_left h4a
  · by_cases hc : c = 0
    · obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (N + 1)
      have : Fact q.Prime := ⟨hq⟩
      exact ⟨q, ⟨⟨hq⟩, 0, by simp [hc]⟩, by omega⟩
    set Nn : ℕ := N + (b ^ 2 - 4 * a * c).natAbs with hNn
    set t : ℤ := (((b.natAbs + 2) * Nn.factorial : ℕ) : ℤ) with ht
    have htb : b.natAbs + 2 ≤ (b.natAbs + 2) * Nn.factorial :=
      Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
    have ht1 : t + b ≥ 2 := by
      have : (b.natAbs : ℤ) + 2 ≤ t := by rw [ht]; exact_mod_cast htb
      have := neg_abs_le b
      have : (b.natAbs : ℤ) = |b| := Int.natCast_natAbs b
      linarith
    have ht2 : t - b ≥ 2 := by
      have : (b.natAbs : ℤ) + 2 ≤ t := by rw [ht]; exact_mod_cast htb
      have := le_abs_self b
      have : (b.natAbs : ℤ) = |b| := Int.natCast_natAbs b
      linarith
    set x : ℤ := a * c with hx
    have hx0 : x ≠ 0 := mul_ne_zero ha hc
    set val : ℤ := x * t ^ 2 + b * t + 1 with hval
    have hval2 : 2 ≤ |val| := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have : val ≤ -3 := by
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ -x - 1 by omega) (sq_nonneg t),
            mul_nonneg (show (0 : ℤ) ≤ t by omega) (show (0 : ℤ) ≤ t - b - 2 by omega)]
        rw [abs_of_neg (by omega)]; omega
      · have : 3 ≤ val := by
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ x - 1 by omega) (sq_nonneg t),
            mul_nonneg (show (0 : ℤ) ≤ t by omega) (show (0 : ℤ) ≤ t + b - 2 by omega)]
        rw [abs_of_pos (by omega)]; omega
    have hne1 : val.natAbs ≠ 1 := by
      intro h
      have : |val| = 1 := by rw [← Int.natCast_natAbs, h]; rfl
      omega
    set q : ℕ := val.natAbs.minFac with hqdef
    have hq : q.Prime := Nat.minFac_prime hne1
    have : Fact q.Prime := ⟨hq⟩
    have hqv : (q : ℤ) ∣ val := Int.natCast_dvd.mpr (Nat.minFac_dvd _)
    have hqN : Nn < q := by
      by_contra hle
      push Not at hle
      have h1 : q ∣ (b.natAbs + 2) * Nn.factorial :=
        Dvd.dvd.mul_left (Nat.dvd_factorial hq.pos hle) _
      have h2 : (q : ℤ) ∣ t := by rw [ht]; exact_mod_cast h1
      have h3 : (q : ℤ) ∣ val - (x * t ^ 2 + b * t) := hqv.sub
        (dvd_add (Dvd.dvd.mul_left (dvd_pow h2 (by norm_num)) _) (Dvd.dvd.mul_left h2 _))
      have h4 : val - (x * t ^ 2 + b * t) = 1 := by rw [hval]; ring
      rw [h4] at h3
      exact hq.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h3)
    have hDq : ¬ (q : ℤ) ∣ b ^ 2 - 4 * a * c := by
      intro h
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hD) (Int.natCast_dvd.mp h)
      omega
    have hf : (q : ℤ) ∣ a * (c * t) ^ 2 + b * (c * t) + c := by
      have : a * (c * t) ^ 2 + b * (c * t) + c = c * val := by rw [hval, hx]; ring
      rw [this]; exact Dvd.dvd.mul_left hqv _
    exact ⟨q, ⟨⟨hq⟩, exists_root_of_dvd_value hDq hf⟩, by omega⟩

/-- **Cassels, Ch. 3, Ex. 19 (p. 52).** Let $a_{ij} \in \mathbb Q_p$ ($i, j = 0, 1, 2, \ldots$) with $a_{ij} \to 0$
$p$-adically as $i, j \to \infty$ independently, i.e. for each $\varepsilon > 0$ only finitely many pairs $(i, j)$ have
$|a_{ij}|_p \ge \varepsilon$ (`Tendsto ... cofinite`). Then the iterated sums converge and
$\sum_i\sum_j a_{ij} = \sum_j\sum_i a_{ij}$. *Reading:* the phrase "independently" is read as $a_{ij} \to 0$ as
$\max(i, j) \to \infty$, equivalently $i + j \to \infty$. -/
@[kb "cassels1978" "Ch. 3, Ex. 19, p. 52"]
theorem ex19 (a : ℕ → ℕ → ℚ_[p]) (ha : Tendsto (Function.uncurry a) Filter.cofinite (𝓝 0)) :
    (∀ i, Summable fun j => a i j) ∧ (∀ j, Summable fun i => a i j) ∧
      ∑' i, ∑' j, a i j = ∑' j, ∑' i, a i j := by
  have hsum : Summable (Function.uncurry a) :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha
  have h1 : ∀ i, Summable fun j => a i j := fun i => hsum.prod_factor i
  have h2 : ∀ j, Summable fun i => a i j := fun j => hsum.prod_symm.prod_factor j
  exact ⟨h1, h2, (Summable.tsum_comm' hsum h1 h2).symm⟩

section Strassmann

/-- A sequence in $\mathbb Z_p$ tending to $0$ and a point $x$ give a summable power series $\sum c_n x^{n}$. -/
theorem summable_mul_pow {c : ℕ → ℤ_[p]} (hc : Tendsto c atTop (𝓝 0)) (x : ℤ_[p]) :
    Summable fun n => c n * x ^ n := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have hc' := tendsto_zero_iff_norm_tendsto_zero.mp hc
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hc'
  rw [norm_mul, norm_pow]
  calc _ ≤ ‖c n‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one x)
    _ = _ := mul_one _

/-- In $\mathbb Z_p$, if $f \to 0$ and every $\|f_n\| < B$, then $\|\sum f_n\| < B$ (the supremum is attained
because $f \to 0$, and the norm is ultrametric). -/
theorem norm_tsum_lt {f : ℕ → ℤ_[p]} (hf : Tendsto f atTop (𝓝 0)) {B : ℝ} (hB : ∀ n, ‖f n‖ < B) :
    ‖∑' n, f n‖ < B := by
  have hB0 : 0 < B := lt_of_le_of_lt (norm_nonneg _) (hB 0)
  obtain ⟨n0, hn0⟩ := Metric.tendsto_atTop.mp hf (B / 2) (by positivity)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (n0 + 1)) (fun n => ‖f n‖)
    ⟨0, by simp⟩
  have hB' : max (B / 2) ‖f m‖ < B := max_lt (by linarith) (hB m)
  refine lt_of_le_of_lt ?_ hB'
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (le_max_of_le_left (by positivity)) fun n => ?_
  by_cases hn : n < n0 + 1
  · exact le_max_of_le_right (hmax n (Finset.mem_range.mpr hn))
  · exact le_max_of_le_left (by
      have := hn0 n (by omega)
      rw [dist_zero_right] at this
      exact this.le)

/-- The coefficients of the quotient $g$ in $f(x) - f(a) = (x - a)g(x)$ for $f = \sum c_n x^{n}$:
$g = \sum_k d_k x^{k}$ with $d_k = \sum_{n > k} c_n a^{n-1-k}$. -/
def quo (c : ℕ → ℤ_[p]) (a : ℤ_[p]) (k : ℕ) : ℤ_[p] := ∑' n, if k < n then c n * a ^ (n - 1 - k) else 0

theorem norm_quo_term_le (c : ℕ → ℤ_[p]) {a : ℤ_[p]} (ha : ‖a‖ ≤ 1) (k n : ℕ) :
    ‖(if k < n then c n * a ^ (n - 1 - k) else 0)‖ ≤ ‖c n‖ := by
  split_ifs
  · rw [norm_mul, norm_pow]
    calc _ ≤ ‖c n‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) ha
      _ = _ := mul_one _
  · simp

theorem summable_quo_term {c : ℕ → ℤ_[p]} (hc : Tendsto c atTop (𝓝 0)) {a : ℤ_[p]} (ha : ‖a‖ ≤ 1)
    (k : ℕ) : Summable fun n => if k < n then c n * a ^ (n - 1 - k) else 0 := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_quo_term_le c ha k n)
    (tendsto_zero_iff_norm_tendsto_zero.mp hc)

theorem norm_quo_le (c : ℕ → ℤ_[p]) {a : ℤ_[p]} (ha : ‖a‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B) (k : ℕ)
    (h : ∀ n, k < n → ‖c n‖ ≤ B) : ‖quo c a k‖ ≤ B := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB fun n => ?_
  by_cases hn : k < n
  · exact (norm_quo_term_le c ha k n).trans (h n hn)
  · simp [hn, hB]

theorem tendsto_quo {c : ℕ → ℤ_[p]} (hc : Tendsto c atTop (𝓝 0)) {a : ℤ_[p]} (ha : ‖a‖ ≤ 1) :
    Tendsto (quo c a) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n0, hn0⟩ := Metric.tendsto_atTop.mp hc (ε / 2) (by positivity)
  refine ⟨n0, fun k hk => ?_⟩
  rw [dist_zero_right]
  refine lt_of_le_of_lt (norm_quo_le c ha (B := ε / 2) (by positivity) k fun n hn => ?_) (by linarith)
  have := hn0 n (by omega)
  rw [dist_zero_right] at this
  exact this.le

/-- The factorisation $f(x) - f(a) = (x - a)\,g(x)$ for a power series $f = \sum c_n x^{n}$ with $c_n \to 0$
and $x, a \in \mathbb Z_p$, where $g = \sum_k d_k x^{k}$ with $d_k = \sum_{n>k} c_n a^{n-1-k}$ (`quo`). -/
theorem tsum_sub_eq_mul {c : ℕ → ℤ_[p]} (hc : Tendsto c atTop (𝓝 0)) (x a : ℤ_[p]) :
    (∑' n, c n * x ^ n) - (∑' n, c n * a ^ n) = (x - a) * ∑' k, quo c a k * x ^ k := by
  have hx : ‖x‖ ≤ 1 := PadicInt.norm_le_one x
  have ha : ‖a‖ ≤ 1 := PadicInt.norm_le_one a
  set u : ℕ × ℕ → ℤ_[p] := fun z => if z.2 < z.1 then c z.1 * (x ^ z.2 * a ^ (z.1 - 1 - z.2)) else 0
    with hu
  have hu_tend : Tendsto u Filter.cofinite (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_cofinite]
    have hT : {n : ℕ | ε ≤ ‖c n‖}.Finite := by
      have hc' : Tendsto c Filter.cofinite (𝓝 0) := by rwa [Nat.cofinite_eq_atTop]
      have := (Metric.tendsto_nhds.mp hc' ε hε)
      rw [Filter.eventually_cofinite] at this
      refine this.subset fun n hn => ?_
      simp only [Set.mem_ofPred_eq, dist_zero_right] at hn ⊢
      exact not_lt.mpr hn
    set M := hT.toFinset.sup id with hM
    refine (Set.finite_Iic M |>.prod (Set.finite_Iic M)).subset ?_
    rintro ⟨n, k⟩ hnk
    simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hnk
    have hkn : k < n := by
      by_contra h
      simp [hu, h] at hnk
      linarith
    have hcn : ε ≤ ‖c n‖ := by
      refine le_trans hnk ?_
      simp only [hu, hkn, ↓reduceIte, norm_mul, norm_pow]
      calc _ ≤ ‖c n‖ * (1 * 1) := by
            gcongr
            · exact pow_le_one₀ (norm_nonneg _) hx
            · exact pow_le_one₀ (norm_nonneg _) ha
        _ = _ := by ring
    have hnM : n ≤ M := Finset.le_sup (f := id) (hT.mem_toFinset.mpr hcn)
    exact ⟨hnM, by simp; omega⟩
  have hu_sum : Summable u := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hu_tend
  have hrows : ∀ n, Summable fun k => u (n, k) := fun n =>
    summable_of_ne_finset_zero (s := Finset.range n) fun k hk => by
      simp [hu, Finset.mem_range.not.mp hk |> not_lt.mp]
  have hcols : ∀ k, Summable fun n => u (n, k) := fun k =>
    hu_sum.prod_symm.prod_factor k
  have E1 : ∀ n, c n * x ^ n - c n * a ^ n = (x - a) * ∑' k, u (n, k) := by
    intro n
    rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
      simp [hu, Finset.mem_range.not.mp hk |> not_lt.mp])]
    have : ∑ k ∈ Finset.range n, u (n, k) = c n * ∑ k ∈ Finset.range n, x ^ k * a ^ (n - 1 - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp [hu, Finset.mem_range.mp hk]
    rw [this]
    have := geom_sum₂_mul x a n
    calc c n * x ^ n - c n * a ^ n = c n * (x ^ n - a ^ n) := by ring
      _ = _ := by rw [← this]; ring
  have hsx := summable_mul_pow hc x
  have hsa := summable_mul_pow hc a
  have hrowsum : Summable fun n => ∑' k, u (n, k) := hu_sum.prod
  have E5 : ∀ k, ∑' n, u (n, k) = quo c a k * x ^ k := by
    intro k
    have : ∀ n, u (n, k) = (if k < n then c n * a ^ (n - 1 - k) else 0) * x ^ k := by
      intro n
      by_cases h : k < n <;> simp [hu, h]
      ring
    simp_rw [this]
    exact (summable_quo_term hc ha k).tsum_mul_right _
  calc (∑' n, c n * x ^ n) - (∑' n, c n * a ^ n)
      = ∑' n, (c n * x ^ n - c n * a ^ n) := (hsx.tsum_sub hsa).symm
    _ = ∑' n, (x - a) * ∑' k, u (n, k) := tsum_congr E1
    _ = (x - a) * ∑' n, ∑' k, u (n, k) := hrowsum.tsum_mul_left _
    _ = (x - a) * ∑' k, ∑' n, u (n, k) := by
        rw [← Summable.tsum_comm' (f := fun n k => u (n, k)) hu_sum hrows hcols]
    _ = _ := by rw [tsum_congr E5]

/-- The quotient sequence `quo c a` of a sequence with a strict maximum at `N + 1` has a strict maximum at `N`. -/
theorem quo_properties {c : ℕ → ℤ_[p]} (hc : Tendsto c atTop (𝓝 0)) (a : ℤ_[p]) {N : ℕ}
    (hc0 : c (N + 1) ≠ 0) (hle : ∀ n, ‖c n‖ ≤ ‖c (N + 1)‖) (hlt : ∀ n, N + 1 < n → ‖c n‖ < ‖c (N + 1)‖) :
    quo c a N ≠ 0 ∧ (∀ m, ‖quo c a m‖ ≤ ‖quo c a N‖) ∧ (∀ m, N < m → ‖quo c a m‖ < ‖quo c a N‖) := by
  have ha : ‖a‖ ≤ 1 := PadicInt.norm_le_one a
  have hB : 0 < ‖c (N + 1)‖ := norm_pos_iff.mpr hc0
  -- the term sequences for `k ≥ N + 1` are small
  have hstrict : ∀ k, N < k → ‖quo c a k‖ < ‖c (N + 1)‖ := by
    intro k hk
    refine norm_tsum_lt ?_ fun n => ?_
    · exact (summable_quo_term hc ha k).tendsto_atTop_zero
    · by_cases hn : k < n
      · exact lt_of_le_of_lt (norm_quo_term_le c ha k n) (hlt n (by omega))
      · simp [hn, hB]
  have hdN : ‖quo c a N‖ = ‖c (N + 1)‖ := by
    have hsplit : ∀ n, (if N < n then c n * a ^ (n - 1 - N) else 0) =
        (if n = N + 1 then c (N + 1) else 0) +
          (if N + 1 < n then c n * a ^ (n - 1 - (N + 1)) * a else 0) := by
      intro n
      by_cases h1 : n = N + 1
      · subst h1; simp
      · by_cases h2 : N + 1 < n
        · have h3 : N < n := by omega
          have h4 : n - 1 - N = n - 1 - (N + 1) + 1 := by omega
          simp [h1, h2, h3, h4, pow_succ, mul_assoc]
        · have : ¬ N < n ∨ n = N + 1 := by omega
          rcases this with h | h
          · simp [h, h1, h2]
          · exact absurd h h1
    have hsum2 : Summable fun n => if N + 1 < n then c n * a ^ (n - 1 - (N + 1)) * a else 0 := by
      have := (summable_quo_term hc ha (N + 1)).mul_right a
      refine this.congr fun n => ?_
      by_cases h : N + 1 < n <;> simp [h]
    have hsum1 : Summable fun n => if n = N + 1 then c (N + 1) else 0 :=
      summable_of_ne_finset_zero (s := {N + 1}) fun n hn => by simp_all
    have he : ‖∑' n, if N + 1 < n then c n * a ^ (n - 1 - (N + 1)) * a else 0‖ < ‖c (N + 1)‖ := by
      refine norm_tsum_lt ?_ fun n => ?_
      · exact hsum2.tendsto_atTop_zero
      · by_cases h : N + 1 < n
        · simp only [h, ↓reduceIte, norm_mul]
          calc _ ≤ ‖c n‖ * 1 * 1 := by
                gcongr
                rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
            _ < _ := by rw [mul_one, mul_one]; exact hlt n h
        · simp [h, hB]
    unfold quo
    rw [tsum_congr hsplit, hsum1.tsum_add hsum2, tsum_ite_eq]
    rw [PadicInt.norm_add_eq_max_of_ne (ne_of_gt he), max_eq_left he.le]
  refine ⟨?_, ?_, ?_⟩
  · intro h; rw [h, norm_zero] at hdN; exact hB.ne hdN
  · intro m
    rw [hdN]
    exact norm_quo_le c ha hB.le m fun n _ => hle n
  · intro m hm
    rw [hdN]
    exact hstrict m hm

/-- Strassmann's theorem, by induction on `N`; the zeros are counted by a finset. -/
theorem strassmann_aux : ∀ N : ℕ, ∀ c : ℕ → ℤ_[p], Tendsto c atTop (𝓝 0) → c N ≠ 0 →
    (∀ n, ‖c n‖ ≤ ‖c N‖) → (∀ n, N < n → ‖c n‖ < ‖c N‖) →
    ∀ s : Finset ℤ_[p], (∀ x ∈ s, ∑' n, c n * x ^ n = 0) → s.card ≤ N := by
  classical
  intro N
  induction N with
  | zero =>
    intro c hc hc0 hle hlt s hs
    rw [Nat.le_zero, Finset.card_eq_zero]
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h := hs x hx
    have hsx := summable_mul_pow hc x
    rw [hsx.tsum_eq_zero_add] at h
    have hr : ‖∑' n, c (n + 1) * x ^ (n + 1)‖ < ‖c 0‖ := by
      refine norm_tsum_lt ?_ fun n => ?_
      · exact hsx.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
      · rw [norm_mul, norm_pow]
        calc _ ≤ ‖c (n + 1)‖ * 1 := by
              gcongr
              exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one x)
          _ < _ := by rw [mul_one]; exact hlt (n + 1) (by omega)
    have : ∑' n, c (n + 1) * x ^ (n + 1) = -c 0 := by
      simp only [pow_zero, mul_one] at h
      linear_combination h
    rw [this, norm_neg] at hr
    exact lt_irrefl _ hr
  | succ N ih =>
    intro c hc hc0 hle hlt s hs
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    obtain ⟨h1, h2, h3⟩ := quo_properties hc a hc0 hle hlt
    have hcard := ih (quo c a) (tendsto_quo hc (PadicInt.norm_le_one a)) h1 h2 h3 (s.erase a) (by
      intro x hx
      have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      have hxs := hs x (Finset.mem_of_mem_erase hx)
      have has := hs a ha
      have := tsum_sub_eq_mul hc x a
      rw [hxs, has, sub_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (sub_ne_zero.mpr hxa))
    have := Finset.card_erase_add_one ha
    omega

/-- A sequence in $\mathbb Z_p$ tending to $0$ and not identically $0$ has a largest index $N$ at which $\|c_n\|$
attains its maximum. -/
theorem exists_strassmann_index {c : ℕ → ℤ_[p]} (hc : Tendsto c atTop (𝓝 0)) (h : ∃ n, c n ≠ 0) :
    ∃ N, c N ≠ 0 ∧ (∀ n, ‖c n‖ ≤ ‖c N‖) ∧ ∀ n, N < n → ‖c n‖ < ‖c N‖ := by
  classical
  obtain ⟨n1, hn1⟩ := h
  have hε : 0 < ‖c n1‖ := norm_pos_iff.mpr hn1
  set ε := ‖c n1‖ with hεdef
  have hT : {n : ℕ | ε ≤ ‖c n‖}.Finite := by
    have hc' : Tendsto c Filter.cofinite (𝓝 0) := by rwa [Nat.cofinite_eq_atTop]
    have := (Metric.tendsto_nhds.mp hc' ε hε)
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun n hn => ?_
    simp only [Set.mem_ofPred_eq, dist_zero_right] at hn ⊢
    exact not_lt.mpr hn
  set T := hT.toFinset with hTdef
  have hn1T : n1 ∈ T := by simp [hTdef, hεdef]
  obtain ⟨m, hmT, hmax⟩ := Finset.exists_max_image T (fun n => ‖c n‖) ⟨n1, hn1T⟩
  have hmε : ε ≤ ‖c m‖ := by simpa [hTdef] using hmT
  set T' := T.filter (fun n => ‖c n‖ = ‖c m‖) with hT'
  have hmT' : m ∈ T' := by simp [hT', hmT]
  set N := T'.max' ⟨m, hmT'⟩ with hN
  have hNT' : N ∈ T' := Finset.max'_mem _ _
  have hNm : ‖c N‖ = ‖c m‖ := (Finset.mem_filter.mp hNT').2
  refine ⟨N, ?_, fun n => ?_, fun n hn => ?_⟩
  · intro h0
    rw [h0, norm_zero] at hNm
    linarith
  · by_cases hnT : n ∈ T
    · rw [hNm]; exact hmax n hnT
    · have : ‖c n‖ < ε := by simpa [hTdef] using hnT
      rw [hNm]; linarith
  · by_contra hge
    push Not at hge
    have hnε : ε ≤ ‖c n‖ := by rw [hNm] at hge; linarith
    have hnT : n ∈ T := by simpa [hTdef] using hnε
    have hnm : ‖c n‖ = ‖c m‖ := le_antisymm (hmax n hnT) (by rw [hNm] at hge; exact hge)
    have hnT' : n ∈ T' := Finset.mem_filter.mpr ⟨hnT, hnm⟩
    exact absurd (Finset.le_max' T' n hnT') (not_le.mpr hn)

/-- **Cassels, Ch. 3, Ex. 21 (p. 52–53), Strassmann's theorem.** Let $c_0, c_1, \ldots \in \mathbb Z_p$ with
$c_n \to 0$ and not all $0$, so that $f(x) = \sum_n c_n x^{n}$ converges for $x \in \mathbb Z_p$. Let $N$ be the largest
index with $|c_N|_p = \max_n |c_n|_p$ (so $|c_n|_p \le |c_N|_p$ for all $n$ and $|c_n|_p < |c_N|_p$ for $n > N$).
Then $f$ has at most $N$ zeros in $\mathbb Z_p$: every finite set of zeros has at most $N$ elements.
The existence of such an $N$ is `exists_strassmann_index`. -/
@[kb "cassels1978" "Ch. 3, Ex. 21, pp. 52-53"]
theorem ex21 {c : ℕ → ℤ_[p]} (hc : Tendsto c atTop (𝓝 0)) {N : ℕ} (hN0 : c N ≠ 0)
    (hmax : ∀ n, ‖c n‖ ≤ ‖c N‖) (hlt : ∀ n, N < n → ‖c n‖ < ‖c N‖)
    (s : Finset ℤ_[p]) (hs : ∀ x ∈ s, HasSum (fun n => c n * x ^ n) 0) : s.card ≤ N :=
  strassmann_aux N c hc hN0 hmax hlt s fun x hx => (hs x hx).tsum_eq

end Strassmann

end QuadFormsKB.Cassels.Ch3Ex
