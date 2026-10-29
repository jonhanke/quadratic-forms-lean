/-
# Cassels, Chapter 3: valuations, $p$-adic series, strong approximation, the product formula

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *$p$-adic numbers*, pp. 33–48.

**Setting.** $\mathbb Q_p$ = Mathlib's `ℚ_[p]` with its norm $\lvert\cdot\rvert_p$ (`‖·‖`), $\mathbb Z_p$ = `ℤ_[p]`;
on $\mathbb Q$ the $p$-adic absolute value is Mathlib's `padicNorm p` and the archimedean one is `|·|`. A finite set
of primes is a `Finset Nat.Primes`.

**Proves.**
* Lemma 1.1 (p. 35), `nonarch_add_eq_max` (any field with a non-archimedean absolute value) and
  `padic_norm_add_eq_max` ($\mathbb Q_p$): $\lvert a + b\rvert = \max(\lvert a\rvert, \lvert b\rvert)$ if
  $\lvert a\rvert \neq \lvert b\rvert$.
* Lemma 1.3 (p. 38), `padic_norm_eq_zpow`: $\lvert x\rvert_p$ is an integral power of $p$ for $x \in \mathbb Q_p^{\times}$.
* Lemma 1.4 (p. 39), `padic_summable_iff`: $\sum_{n \ge 0} a_n$ converges in $\mathbb Q_p$ iff $a_n \to 0$.
* Lemma 3.1 (p. 44, Strong Approximation), `strong_approximation`.
* Lemma 3.3 (p. 46), `product_formula`: for $a \in \mathbb Q^{\times}$, $\lvert a\rvert_p = 1$ for all primes
  $p \ge m$ and $\lvert a\rvert_\infty\prod_{p < m}\lvert a\rvert_p = 1$, for every $m$ exceeding $\lvert\mathrm{num}(a)\rvert$
  and $\mathrm{den}(a)$ (Cassels' "almost all $p$" made explicit).

**Proof notes.** Lemmas 1.1, 1.3 and 1.4 are Mathlib facts (`IsNonarchimedean.add_eq_max_of_ne`,
`Padic.norm_eq_zpow_neg_valuation`, `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`). Lemma 3.1 follows
Cassels: approximate each $z_p$ by an integer $a_p$ modulo $p^{N}$ (`PadicInt.appr`) and glue the $a_p$ by the Chinese
remainder theorem (`IsDedekindDomain.exists_forall_sub_mem_ideal`), with $2^{-N} < \varepsilon$. Lemma 3.3 is
Cassels' proof: $\lvert n\rvert_p = p^{-v_p(n)}$ and $\prod_p p^{v_p(n)} = n$ (`Nat.prod_pow_prime_padicValNat`).
-/
import Mathlib
import QuadFormsKB.Citation

open Filter Topology

namespace QuadFormsKB.Cassels

/-- Primes in `Nat.Primes` are prime. -/
local instance factPrimes' (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **Cassels, Ch. 3, Lemma 1.1.** Let $v$ be a non-archimedean absolute value on a field $K$
($v(a + b) \le \max(v(a), v(b))$). If $v(a) \neq v(b)$ then $v(a + b) = \max(v(a), v(b))$. -/
@[kb "cassels1978" "Ch. 3, Lemma 1.1, p. 35"]
theorem nonarch_add_eq_max {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a b : K} (h : v a ≠ v b) : v (a + b) = max (v a) (v b) :=
  hv.add_eq_max_of_ne (fun x => v.map_neg x) h

/-- **Cassels, Ch. 3, Lemma 1.1, for $\mathbb Q_p$.** For $a, b \in \mathbb Q_p$ with
$\lvert a\rvert_p \neq \lvert b\rvert_p$: $\lvert a + b\rvert_p = \max(\lvert a\rvert_p, \lvert b\rvert_p)$. -/
@[kb "cassels1978" "Ch. 3, Lemma 1.1, p. 35 (for $\\mathbb Q_p$)"]
theorem padic_norm_add_eq_max {p : ℕ} [Fact p.Prime] {a b : ℚ_[p]} (h : ‖a‖ ≠ ‖b‖) :
    ‖a + b‖ = max ‖a‖ ‖b‖ :=
  Padic.add_eq_max_of_ne h

/-- **Cassels, Ch. 3, Lemma 1.3.** For $x \in \mathbb Q_p^{\times}$, $\lvert x\rvert_p = p^{k}$ for some
$k \in \mathbb Z$ (namely $k = -v_p(x)$). -/
@[kb "cassels1978" "Ch. 3, Lemma 1.3, p. 38"]
theorem padic_norm_eq_zpow {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ k :=
  ⟨_, Padic.norm_eq_zpow_neg_valuation hx⟩

/-- **Cassels, Ch. 3, Lemma 1.4.** A series $\sum_{n \ge 0} a_n$ of elements of $\mathbb Q_p$ converges
(is summable) if and only if $a_n \to 0$ as $n \to \infty$. -/
@[kb "cassels1978" "Ch. 3, Lemma 1.4, p. 39"]
theorem padic_summable_iff {p : ℕ} [Fact p.Prime] (a : ℕ → ℚ_[p]) :
    Summable a ↔ Tendsto a atTop (𝓝 0) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]

/-- **Cassels, Ch. 3, Lemma 3.1 (Strong Approximation Theorem).** Let $P$ be a finite set of (finite)
primes, let $z_p \in \mathbb Z_p$ be given for $p \in P$, and let $\varepsilon > 0$. Then there is $z \in \mathbb Z$
with $\lvert z - z_p\rvert_p < \varepsilon$ for all $p \in P$. -/
@[kb "cassels1978" "Ch. 3, Lemma 3.1, p. 44"]
theorem strong_approximation (P : Finset Nat.Primes) (z : ∀ p : Nat.Primes, ℤ_[p]) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℤ, ∀ p ∈ P, ‖(x : ℤ_[p]) - z p‖ < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  let a : ∀ p : Nat.Primes, ℤ := fun p => (PadicInt.appr (z p) N : ℤ)
  have ha : ∀ p : Nat.Primes, ‖z p - (a p : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := fun p => by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow]
    simpa [a] using PadicInt.appr_spec N (z p)
  have hprime : ∀ p ∈ P, Prime (Ideal.span {((p : ℕ) : ℤ)}) := fun p _ => by
    have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
    rw [Ideal.prime_iff_isPrime (by simpa using hp.ne_zero)]
    exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hcop : ∀ᵉ (p ∈ P) (q ∈ P), p ≠ q →
      Ideal.span {((p : ℕ) : ℤ)} ≠ Ideal.span {((q : ℕ) : ℤ)} := by
    intro p _ q _ hpq h
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff] at h
    rcases h with h | h
    · exact hpq (Subtype.ext (by exact_mod_cast h))
    · have := p.2.pos; have := q.2.pos; omega
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := P)
    (fun p => Ideal.span {((p : ℕ) : ℤ)}) (fun _ => N) hprime hcop (fun p => a p)
  refine ⟨y, fun p hp => ?_⟩
  have h1 := hy p hp
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  have h2 : ‖((y - a p : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    PadicInt.norm_int_le_pow_iff_dvd.mpr (by exact_mod_cast h1)
  have h3 : (p : ℝ) ^ (-(N : ℤ)) ≤ (1 / 2 : ℝ) ^ N := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    gcongr
    exact_mod_cast p.2.two_le
  calc ‖(y : ℤ_[p]) - z p‖ = ‖((y - a p : ℤ) : ℤ_[p]) + (a p - z p)‖ := by push_cast; ring_nf
    _ ≤ max ‖((y - a p : ℤ) : ℤ_[p])‖ ‖(a p : ℤ_[p]) - z p‖ := PadicInt.nonarchimedean _ _
    _ ≤ (p : ℝ) ^ (-(N : ℤ)) := max_le h2 (by rw [norm_sub_rev]; exact ha p)
    _ < ε := h3.trans_lt hN

/-- $\lvert n\rvert_p = p^{-v_p(n)}$ for a positive integer $n$. -/
theorem padicNorm_natCast_eq (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    padicNorm p (n : ℚ) = ((p : ℚ) ^ padicValNat p n)⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat, zpow_neg, zpow_natCast]

/-- $\prod_{p < m}\lvert n\rvert_p = n^{-1}$ for $0 < n < m$, the product over the primes $p < m$. -/
theorem prod_padicNorm_natCast (n m : ℕ) (hn : n ≠ 0) (hm : n < m) :
    ∏ p ∈ Finset.range m with p.Prime, padicNorm p (n : ℚ) = (n : ℚ)⁻¹ := by
  have h := Nat.prod_pow_prime_padicValNat n hn m hm
  calc ∏ p ∈ Finset.range m with p.Prime, padicNorm p (n : ℚ)
      = ∏ p ∈ Finset.range m with p.Prime, ((p : ℚ) ^ padicValNat p n)⁻¹ := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have : Fact p.Prime := ⟨(Finset.mem_filter.mp hp).2⟩
        exact padicNorm_natCast_eq p n hn
    _ = (n : ℚ)⁻¹ := by
        rw [Finset.prod_inv_distrib]
        congr 1
        exact_mod_cast h

/-- **Cassels, Ch. 3, Lemma 3.3 (product formula).** Let $a \in \mathbb Q^{\times}$ and let $m$ exceed
both $\lvert\mathrm{num}(a)\rvert$ and $\mathrm{den}(a)$. Then $\lvert a\rvert_p = 1$ for every prime $p \ge m$, and
$$\lvert a\rvert_\infty \prod_{p < m \text{ prime}} \lvert a\rvert_p = 1,$$
i.e. $\prod_{p \le \infty}\lvert a\rvert_p = 1$ (Cassels' "almost all $p$" made explicit). -/
@[kb "cassels1978" "Ch. 3, Lemma 3.3, p. 46"]
theorem product_formula (a : ℚ) (ha : a ≠ 0) (m : ℕ) (hm1 : a.num.natAbs < m) (hm2 : a.den < m) :
    (∀ p : ℕ, p.Prime → m ≤ p → padicNorm p a = 1) ∧
      |a| * ∏ p ∈ Finset.range m with p.Prime, padicNorm p a = 1 := by
  have hnum : a.num.natAbs ≠ 0 := by simpa using ha
  have hden : a.den ≠ 0 := a.den_nz
  have hsplit : ∀ p : ℕ, p.Prime →
      padicNorm p a = padicNorm p (a.num.natAbs : ℚ) / padicNorm p (a.den : ℚ) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    conv_lhs => rw [← Rat.num_div_den a]
    rw [padicNorm.div]
    congr 1
    rw [Nat.cast_natAbs, Int.cast_abs]
    rcases abs_choice ((a.num : ℤ) : ℚ) with h | h <;> rw [h]
    exact (padicNorm.neg _).symm
  constructor
  · intro p hp hpm
    have : Fact p.Prime := ⟨hp⟩
    rw [hsplit p hp, padicNorm_natCast_eq p _ hnum, padicNorm_natCast_eq p _ hden,
      padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hnum) h; omega),
      padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hden) h; omega)]
    simp
  · rw [Finset.prod_congr rfl fun p hp => hsplit p (Finset.mem_filter.mp hp).2]
    rw [Finset.prod_div_distrib, prod_padicNorm_natCast _ m hnum hm1, prod_padicNorm_natCast _ m hden hm2]
    have : |a| = (a.num.natAbs : ℚ) / a.den := by
      conv_lhs => rw [← Rat.num_div_den a]
      rw [abs_div, Nat.cast_natAbs, Int.cast_abs, Nat.abs_cast]
    rw [this]
    have h1 : (a.num.natAbs : ℚ) ≠ 0 := by exact_mod_cast hnum
    have h2 : (a.den : ℚ) ≠ 0 := by exact_mod_cast hden
    field_simp

end QuadFormsKB.Cassels
