/-
# Moreno–Wagstaff 2005: elementary identities

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005). Page numbers are the
printed ones. Notation: $r_k(n)$ = `Siegel.repNum (Siegel.sumSq k) n`.

**Proved here (all unconditional).**
* `eq61` ((6.1), p. 186): $r_2(n) = 4\sum_{d \mid n,\ d \text{ odd}} (-1)^{(d-1)/2}$ ($n \ge 1$), from Theorem 2.5.
* `eq62` ((6.2), p. 186): $r_4(n) = 2^3\cdot 3^{\delta}\sum_{d \mid n,\ d\text{ odd}} d$, $\delta = 1$ for even $n$,
  $\delta = 0$ for odd $n$, from Jacobi's $r_4(n) = 8\sum_{4 \nmid d \mid n} d$ (`repNum_sumSq_four`).
* `example65` (Example 6.5, p. 250): Euler's pentagonal identity
  $\prod_{n \ge 1}(1 - q^n) = \sum_{n \in \mathbb{Z}} (-1)^n q^{n(3n+1)/2}$ for complex $|q| < 1$, from Mathlib's
  pentagonal number theorem (reindexing $k \mapsto -k$).
* `rowD4` (§2.6, p. 26): the divisor sum $T(n) = \sum_{d \mid n}\chi(d)$, $\chi(d) = (-1/d)$, $T(0) = 1/4$:
  explicit values of $\chi$, the two odd-divisor forms, multiplicativity, and $T(p^e)$.
* `claim21` (Claim 2.1, p. 46): the symmetry $f(a,b,n) = f(b,a,n)$ of the lattice-point count for
  $ax + by = n$, $0 < x < b$, $a < y$, $a \nmid y$, by an explicit bijection.

(The remaining Ramanujan-sum results are in `Elementary2.lean`.)
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2ProofsB
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-! ### (6.1) and (6.2): $r_2$ and $r_4$ -/

/-- **Moreno–Wagstaff (6.1)** (p. 186): for every integer $n \ge 1$,
$r_2(n) = 4\sum_{d \mid n,\ d \text{ odd}} (-1)^{(d-1)/2}$ (the book writes $d = 2\ell + 1$ and $(-1)^\ell$). -/
@[kb "morenowagstaff2005" "(6.1), p. 186"]
def Eq61 : Prop :=
  ∀ n : ℕ, 0 < n →
    (repNum (sumSq 2) n : ℤ) = 4 * ∑ d ∈ n.divisors.filter Odd, (-1 : ℤ) ^ ((d - 1) / 2)

/-- **Moreno–Wagstaff (6.1)** (p. 186), proved: this is the first display of Theorem 2.5 (`theorem25`).
Hypothesis: $n \ge 1$. -/
theorem eq61 : Eq61 := fun n hn => (theorem25.1 n hn).1

/-- **Moreno–Wagstaff (6.2)** (p. 186): for every integer $n \ge 1$,
$r_4(n) = 2^3 \cdot 3^{\delta}\sum_{d \mid n,\ d \text{ odd}} d$, where $\delta = 1$ if $n$ is even and $\delta = 0$
if $n$ is odd (the book writes the odd divisors as $2\ell + 1$). -/
@[kb "morenowagstaff2005" "(6.2), p. 186"]
def Eq62 : Prop :=
  ∀ n : ℕ, 0 < n →
    repNum (sumSq 4) n = 2 ^ 3 * 3 ^ (if Even n then 1 else 0) * ∑ d ∈ n.divisors.filter Odd, d

/-- For even $n$, the divisors $d \equiv 2 \pmod 4$ of $n$ are exactly the doubles of the odd divisors of $n$. -/
private lemma filter_mod_four_two_eq {n : ℕ} (hev : Even n) :
    n.divisors.filter (fun d => d % 4 = 2) = (n.divisors.filter Odd).image (fun e => 2 * e) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors, Nat.odd_iff]
  constructor
  · rintro ⟨⟨hd, hn0⟩, h⟩
    refine ⟨d / 2, ⟨⟨?_, hn0⟩, by omega⟩, by omega⟩
    exact (Nat.div_dvd_of_dvd (by omega)).trans hd
  · rintro ⟨e, ⟨⟨he, hn0⟩, hodd⟩, rfl⟩
    refine ⟨⟨?_, hn0⟩, by omega⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd))
      hev.two_dvd he

/-- **Moreno–Wagstaff (6.2)** (p. 186), proved: from Jacobi's $r_4(n) = 8\sum_{d \mid n,\ 4 \nmid d} d$
(`repNum_sumSq_four`): the divisors with $4 \nmid d$ are the odd ones, together with (for even $n$) the doubles of
the odd ones, so the sum is $3^{\delta}\sum_{d \mid n,\ d\text{ odd}} d$. Hypothesis: $n \ge 1$. -/
theorem eq62 : Eq62 := by
  intro n hn
  rw [repNum_sumSq_four hn]
  have key : ∑ d ∈ n.divisors.filter (¬ 4 ∣ ·), d =
      3 ^ (if Even n then 1 else 0) * ∑ d ∈ n.divisors.filter Odd, d := by
    by_cases hev : Even n
    · rw [if_pos hev]
      have hsplit : n.divisors.filter (¬ 4 ∣ ·) =
          n.divisors.filter Odd ∪ n.divisors.filter (fun d => d % 4 = 2) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_union, Nat.odd_iff]
        constructor
        · rintro ⟨hd, h4⟩
          by_cases h : d % 2 = 1
          · exact Or.inl ⟨hd, h⟩
          · exact Or.inr ⟨hd, by omega⟩
        · rintro (⟨hd, h⟩ | ⟨hd, h⟩)
          · exact ⟨hd, by omega⟩
          · exact ⟨hd, by omega⟩
      have hdisj : Disjoint (n.divisors.filter Odd) (n.divisors.filter (fun d => d % 4 = 2)) :=
        Finset.disjoint_filter.2 fun d _ h1 h2 => by rw [Nat.odd_iff] at h1; omega
      rw [hsplit, Finset.sum_union hdisj, filter_mod_four_two_eq hev,
        Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h),
        ← Finset.mul_sum]
      ring
    · rw [if_neg hev]
      have hodd : Odd n := Nat.not_even_iff_odd.1 hev
      have : n.divisors.filter (¬ 4 ∣ ·) = n.divisors.filter Odd := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨hd, _⟩
          exact ⟨hd, Odd.of_dvd_nat hodd hd.1⟩
        · rintro ⟨hd, h⟩
          refine ⟨hd, ?_⟩
          rw [Nat.odd_iff] at h
          omega
      rw [this]; ring
  rw [key]; ring

/-! ### Example 6.5: Euler's pentagonal identity -/

/-- **Moreno–Wagstaff, Example 6.5** (p. 250), Euler's identity: for every complex number $q$ with $|q| < 1$,
the infinite product $\prod_{n \ge 1}(1 - q^n)$ is multipliable, the series
$\sum_{n \in \mathbb{Z}} (-1)^n q^{n(3n+1)/2}$ is summable (the exponent $n(3n+1)/2$ is a non-negative integer for
every $n \in \mathbb{Z}$; here it is an integer power), and
$\prod_{n \ge 1}(1 - q^n) = \sum_{n \in \mathbb{Z}} (-1)^n q^{n(3n+1)/2}$. (The book puts $q = e^{2\pi i z}$,
$z$ in the upper half plane, i.e. $0 < |q| < 1$; we allow all $|q| < 1$.) -/
@[kb "morenowagstaff2005" "Example 6.5, p. 250"]
def Example65 : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) ∧
    Summable (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2)) ∧
    ∏' n : ℕ, (1 - q ^ (n + 1)) = ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2)

/-- **Moreno–Wagstaff, Example 6.5** (p. 250), proved from Mathlib's pentagonal number theorem
(`hasSum_eulerFunction_pentagonal`, `hasProd_eulerFunction`, which sum over
$k(3k-1)/2$): substitute $k = -n$. Hypothesis: $|q| < 1$. -/
theorem example65 : Example65 := by
  intro q hq
  have hS := hasSum_eulerFunction_pentagonal (x := q) hq
  have hS' : HasSum (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2))
      (eulerFunction q) := by
    have h2 := (Equiv.neg ℤ).hasSum_iff.2 hS
    convert h2 using 1
    funext n
    simp only [Function.comp_apply, Equiv.neg_apply]
    have e : n * (3 * n + 1) / 2 = ((pentagonal (-n) : ℕ) : ℤ) := by
      rw [natCast_pentagonal]
      congr 1
      ring
    have key : ∀ m : ℤ, (-1 : ℂ) ^ m = (-1) ^ m.natAbs := by
      intro m
      obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
      · simp
      · simp only [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
        rcases neg_one_pow_eq_or ℂ k with h | h <;> simp [h]
    rw [e, zpow_natCast, Int.negOnePow_neg, Int.coe_negOnePow, key]
  have hP := hasProd_eulerFunction (x := q) hq
  refine ⟨hP.multipliable, hS'.summable, ?_⟩
  rw [hP.tprod_eq, hS'.tsum_eq]

/-! ### Row 2.d4: the divisor sum $T(n) = \sum_{d \mid n}\chi(d)$ -/

/-- **The function $T$ of §2.6** (p. 26): $T(0) = 1/4$ and, for $n \ge 1$, $T(n) = \sum_{d \mid n}\chi(d)$ over the
positive divisors $d$ of $n$, where $\chi = \chi_{-4}$ (Mathlib's `ZMod.χ₄`) is the character of conductor $4$,
$\chi(d) = (-1/d)$. -/
noncomputable def chiT (n : ℕ) : ℚ :=
  if n = 0 then 1 / 4 else ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℚ)

private lemma chi4_eq' (d : ℕ) :
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

private lemma sum_geom_neg_one' (e : ℕ) :
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

private lemma chiT_eq_int (n : ℕ) (hn : 0 < n) :
    chiT n = ((∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) : ℤ) : ℚ) := by
  simp [chiT, hn.ne']

private lemma sum_chi_prime_pow (p e : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ e).divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) =
      if p = 2 then 1 else if p % 4 = 1 then (e : ℤ) + 1 else if Even e then 1 else 0 := by
  have h : ∑ i ∈ Finset.range (e + 1), (ZMod.χ₄ ((p ^ i : ℕ) : ZMod 4) : ℤ) =
      ∑ i ∈ Finset.range (e + 1), (ZMod.χ₄ (p : ZMod 4) : ℤ) ^ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rw [map_pow]
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [h]
  have hc : (ZMod.χ₄ (p : ZMod 4) : ℤ) = if p % 2 = 0 then 0 else if p % 4 = 1 then 1 else -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
  by_cases h2 : p = 2
  · subst h2
    have : (ZMod.χ₄ ((2 : ℕ) : ZMod 4) : ℤ) = 0 := by rw [hc]; simp
    rw [this, Finset.sum_range_succ']
    simp
  · have hodd : p % 2 = 1 := by
      by_contra hne
      rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)) with h | h
      · omega
      · exact absurd h.symm h2
    by_cases h4 : p % 4 = 1
    · have h1 : (ZMod.χ₄ (p : ZMod 4) : ℤ) = 1 := by rw [hc]; simp [h4, hodd]
      rw [h1, if_neg h2, if_pos h4]
      simp
    · have h1 : (ZMod.χ₄ (p : ZMod 4) : ℤ) = -1 := by rw [hc]; simp [h4, hodd]
      rw [h1, if_neg h2, if_neg h4, sum_geom_neg_one']

/-- **Moreno–Wagstaff, §2.6, Row 2.d4** (p. 26). With $\chi(d) = (-1/d)$ (`ZMod.χ₄`) and $T(n) = \sum_{d \mid n}\chi(d)$,
$T(0) = 1/4$ (`chiT`):
1. $\chi(d) = 0$ for even $d$, $1$ for $d \equiv 1 \pmod 4$, $-1$ for $d \equiv 3 \pmod 4$, and $\chi$ is totally
   multiplicative;
2. for $n \ge 1$, $T(n) = \sum_{d \mid n,\ d \text{ odd}} (-1)^{(d-1)/2} = \#\{d \mid n : d \equiv 1 \pmod 4\} -
   \#\{d \mid n : d \equiv 3 \pmod 4\}$;
3. $T(0) = 1/4$, $T(1) = 1$ and $T(mn) = T(m)T(n)$ for coprime positive $m, n$;
4. for $p$ prime, $e \ge 0$: $T(p^e) = 1$ if $p = 2$, $e + 1$ if $p \equiv 1 \pmod 4$, and for $p \equiv 3 \pmod 4$ it is
   $1$ if $e$ is even, $0$ if $e$ is odd. -/
@[kb "morenowagstaff2005" "Row 2.d4 (§2.6), p. 26"]
def RowD4 : Prop :=
  ((∀ d : ℕ, (ZMod.χ₄ (d : ZMod 4) : ℤ) = if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1) ∧
    (∀ d e : ℕ, (ZMod.χ₄ ((d * e : ℕ) : ZMod 4) : ℤ) =
      (ZMod.χ₄ (d : ZMod 4) : ℤ) * (ZMod.χ₄ (e : ZMod 4) : ℤ))) ∧
  (∀ n : ℕ, 0 < n →
    chiT n = ∑ d ∈ n.divisors.filter Odd, (-1 : ℚ) ^ ((d - 1) / 2) ∧
    chiT n = ((n.divisors.filter (· % 4 = 1)).card : ℚ) - ((n.divisors.filter (· % 4 = 3)).card : ℚ)) ∧
  (chiT 0 = 1 / 4 ∧ chiT 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → chiT (m * n) = chiT m * chiT n) ∧
  (∀ p e : ℕ, p.Prime →
    chiT (p ^ e) = if p = 2 then 1 else if p % 4 = 1 then (e : ℚ) + 1 else if Even e then 1 else 0)

/-- $\chi_{-4}$ as an arithmetic function (zero at $0$). -/
private noncomputable def chiAF' : ArithmeticFunction ℤ :=
  ⟨fun d => if d = 0 then 0 else (ZMod.χ₄ (d : ZMod 4) : ℤ), by simp⟩

private lemma chiAF'_mult : chiAF'.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn _ => ?_⟩
  · simp [chiAF']
  · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    simp only [chiAF', ArithmeticFunction.coe_mk, hm, hn, hmn, ite_false, Nat.cast_mul]
    exact map_mul _ _ _

private noncomputable def divChi' : ArithmeticFunction ℤ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * chiAF'

private lemma divChi'_mult : divChi'.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul chiAF'_mult

private lemma divChi'_apply (n : ℕ) :
    divChi' n = ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) := by
  unfold divChi'
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  refine Finset.sum_congr rfl fun d hd => ?_
  have : d ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.pos_of_mem_divisors hd)
  simp [chiAF', this]

/-- **Row 2.d4** (p. 26), proved. Items 1 and 2 by evaluating `ZMod.χ₄`; item 3 from multiplicativity of $\chi$
(`map_mul`) and of the Dirichlet convolution with $\zeta$; item 4 from $\sum_{d \mid p^e}\chi(d) =
\sum_{i \le e}\chi(p)^i$. -/
theorem rowD4 : RowD4 := by
  refine ⟨⟨fun d => ?_, fun d e => ?_⟩, fun n hn => ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, fun p e hp => ?_⟩
  · rw [ZMod.χ₄_nat_eq_if_mod_four]
  · push_cast; exact map_mul _ _ _
  · rw [chiT_eq_int n hn]
    have : ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) =
        ∑ d ∈ n.divisors.filter Odd, (-1 : ℤ) ^ ((d - 1) / 2) := by
      rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun d _ => chi4_eq' d
    rw [this]; push_cast; rfl
  · rw [chiT_eq_int n hn]
    have : ∀ d : ℕ, (ZMod.χ₄ (d : ZMod 4) : ℤ) =
        (if d % 4 = 1 then 1 else 0) - (if d % 4 = 3 then 1 else 0) := by
      intro d
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      split_ifs <;> omega
    simp only [this, Finset.sum_sub_distrib, Finset.sum_boole]
    push_cast; rfl
  · simp [chiT]
  · simp [chiT]
  · intro m n hm hn hmn
    have h := divChi'_mult.map_mul_of_coprime hmn
    rw [divChi'_apply, divChi'_apply, divChi'_apply] at h
    rw [chiT_eq_int _ (Nat.mul_pos hm hn), chiT_eq_int _ hm, chiT_eq_int _ hn, h]
    push_cast; rfl
  · rw [chiT_eq_int _ (pow_pos hp.pos e), sum_chi_prime_pow p e hp]
    split_ifs <;> simp

/-! ### Claim 2.1: symmetry of a lattice-point count -/

/-- The solution set of (2.34) (Claim 2.1, p. 46): integer pairs $(x, y)$ with $ax + by = n$, $0 < x < b$,
$a < y$ and $y \not\equiv 0 \pmod a$ (i.e. $a \nmid y$). -/
def claim21Set (a b n : ℕ) : Set (ℤ × ℤ) :=
  {p | (a : ℤ) * p.1 + b * p.2 = n ∧ 0 < p.1 ∧ p.1 < b ∧ (a : ℤ) < p.2 ∧ ¬ (a : ℤ) ∣ p.2}

/-- **Moreno–Wagstaff, Claim 2.1** (p. 46): for positive integers $a, b, n$ let $f(a,b,n)$ be the number of integer
solutions $(x, y)$ of $ax + by = n$ with $0 < x < b$, $a < y$, $y \not\equiv 0 \pmod a$ (`claim21Set`, counted with
`Set.ncard`). Then $f(a,b,n) = f(b,a,n)$. (Note the congruence condition is $y \not\equiv 0$, not $a \mid y$:
numerically the version with $a \mid y$ is false.) -/
@[kb "morenowagstaff2005" "Claim 2.1 (Row 2.r7), p. 46"]
def Claim21 : Prop :=
  ∀ a b n : ℕ, 0 < a → 0 < b → 0 < n → (claim21Set a b n).ncard = (claim21Set b a n).ncard

/-- The bijection of Claim 2.1: $(x, y) \mapsto (y \bmod a,\ x + b\lfloor y/a\rfloor)$. -/
private def fwd (a b : ℕ) (p : ℤ × ℤ) : ℤ × ℤ := (p.2 % a, p.1 + b * (p.2 / a))

private lemma fwd_mem {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) {p : ℤ × ℤ} (hp : p ∈ claim21Set a b n) :
    fwd a b p ∈ claim21Set b a n := by
  obtain ⟨x, y⟩ := p
  simp only [claim21Set, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hy : y % a + a * (y / a) = y := Int.emod_add_mul_ediv y a
  have hr0 : 0 ≤ y % a := Int.emod_nonneg y ha'.ne'
  have hr1 : y % a < a := Int.emod_lt_of_pos y ha'
  have hr2 : y % a ≠ 0 := fun h => h5 (Int.dvd_of_emod_eq_zero h)
  have hq : 1 ≤ y / a := by
    by_contra hq
    push_neg at hq
    nlinarith
  unfold fwd
  simp only
  refine ⟨?_, lt_of_le_of_ne hr0 (Ne.symm hr2), hr1, ?_, ?_⟩
  · linear_combination h1 + (b : ℤ) * hy
  · nlinarith
  · intro hd
    have : (b : ℤ) ∣ x := (dvd_add_left (dvd_mul_right (b : ℤ) (y / a))).1 hd
    exact absurd (Int.le_of_dvd h2 this) (by omega)

private lemma fwd_inv {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) {p : ℤ × ℤ} (hp : p ∈ claim21Set a b n) :
    fwd b a (fwd a b p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [claim21Set, Set.mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hy : y % a + a * (y / a) = y := Int.emod_add_mul_ediv y a
  unfold fwd
  simp only
  have e1 : (x + b * (y / a)) % b = x := by
    rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt h2.le h3
  have e2 : (x + b * (y / a)) / b = y / a := by
    rw [Int.add_mul_ediv_left _ _ hb'.ne', Int.ediv_eq_zero_of_lt h2.le h3, zero_add]
  rw [e1, e2]
  ext
  · rfl
  · simp only
    linarith

/-- **Claim 2.1** (p. 46), proved by the book's bijection between the solution sets of (2.34) and (2.35):
$(x, y) \mapsto (y \bmod a,\ x + b\lfloor y/a\rfloor)$, with inverse of the same shape with $a, b$ swapped
(`Set.ncard_congr`). Hypotheses: $a, b, n$ positive integers. -/
theorem claim21 : Claim21 := by
  intro a b n ha hb _
  refine Set.ncard_congr (fun p _ => fwd a b p) (fun p hp => fwd_mem ha hb hp) ?_ ?_
  · intro p q hp hq h
    have h1 := fwd_inv ha hb hp
    have h2 := fwd_inv ha hb hq
    rw [← h1, ← h2, h]
  · intro q hq
    exact ⟨fwd b a q, fwd_mem hb ha hq, fwd_inv hb ha hq⟩

end QuadFormsKB.MorenoWagstaff
