/-
# Moreno–Wagstaff 2005, §6.4.2: Ramanujan sums

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), §6.4.2 (Row 6.r6), p. 205
(printed page). The Ramanujan sum is $c_q(n) = \sum_{1 \le h \le q,\ \gcd(h,q)=1} e^{(2\pi i/q)hn}$ (`ramanujanSum`,
for natural numbers $q, n$).

**Proved here (all unconditional).**
* `ramanujanSum_eq_sum_gcd`: $c_q(n) = \sum_{d \mid \gcd(q,n)} d\,\mu(q/d)$ for $q \ge 1$ (in particular $c_q(n)$ is
  an integer), by Möbius inversion of the coprimality condition and the geometric sum over $q/d$-th roots of unity.
* `ramanujanSum_mul`: $c_{q_1q_2}(n) = c_{q_1}(n)c_{q_2}(n)$ for coprime $q_1, q_2 \ge 1$ (as the Dirichlet convolution
  of the multiplicative functions $d \mapsto d\,[d \mid n]$ and $\mu$).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2ProofsB
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace QuadFormsKB.MorenoWagstaff

/-- **The Ramanujan sum** (Moreno–Wagstaff §6.4.2, p. 205): for natural numbers $q, n$,
$c_q(n) = \sum_{1 \le h \le q,\ \gcd(h,q) = 1} e^{(2\pi i/q)\,h n}$. -/
noncomputable def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ h ∈ (Finset.Icc 1 q).filter (fun h => Nat.Coprime h q),
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ) * ((h : ℂ) * (n : ℂ)))

/-- $\omega_m = e^{2\pi i/m}$. -/
private noncomputable def omega (m : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ))

private lemma exp_term (q h n : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ) * ((h : ℂ) * (n : ℂ))) = omega q ^ (h * n) := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma ramanujanSum_eq_omega (q n : ℕ) :
    ramanujanSum q n = ∑ h ∈ (Finset.Icc 1 q).filter (fun h => Nat.Coprime h q), omega q ^ (h * n) :=
  Finset.sum_congr rfl fun h _ => exp_term q h n

private lemma omega_prim {m : ℕ} (hm : 0 < m) : IsPrimitiveRoot (omega m) m :=
  Complex.isPrimitiveRoot_exp m hm.ne'

/-- The geometric sum $\sum_{j < m}(\omega_m^k)^j$ is $m$ if $m \mid k$ and $0$ otherwise. -/
private lemma geom_omega {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∑ j ∈ Finset.range m, (omega m ^ k) ^ j = if m ∣ k then (m : ℂ) else 0 := by
  have hp := omega_prim hm
  split_ifs with h
  · have : omega m ^ k = 1 := (hp.pow_eq_one_iff_dvd k).2 h
    simp [this]
  · have h1 : omega m ^ k ≠ 1 := fun h' => h ((hp.pow_eq_one_iff_dvd k).1 h')
    have h2 : (omega m ^ k) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2]
    simp

private lemma sum_moebius (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℤ) = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- Sum over $1 \le h \le q$ equals the sum over $0 \le h < q$ (the summand is $q$-periodic). -/
private lemma ram_range {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ramanujanSum q n =
      ∑ h ∈ Finset.range q, if Nat.Coprime h q then omega q ^ (h * n) else 0 := by
  set g : ℕ → ℂ := fun h => if Nat.Coprime h q then omega q ^ (h * n) else 0 with hg
  have h1 : ramanujanSum q n = ∑ h ∈ Finset.Icc 1 q, g h := by
    rw [ramanujanSum_eq_omega, Finset.sum_filter]
  have hωq : omega q ^ q = 1 := (omega_prim hq).pow_eq_one
  have hper : g q = g 0 := by
    simp only [hg]
    by_cases hq1 : q = 1
    · have c1 : Nat.Coprime q q := by rw [Nat.coprime_self]; exact hq1
      have c2 : Nat.Coprime 0 q := by rw [Nat.coprime_zero_left]; exact hq1
      rw [if_pos c1, if_pos c2, zero_mul, pow_zero, mul_comm q n, pow_mul', hωq, one_pow]
    · have c1 : ¬ Nat.Coprime q q := by rw [Nat.coprime_self]; exact hq1
      have c2 : ¬ Nat.Coprime 0 q := by rw [Nat.coprime_zero_left]; exact hq1
      rw [if_neg c1, if_neg c2]
  have hIcc : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by
    ext x; simp
  have h3 : ∑ h ∈ Finset.range (q + 1), g h = g 0 + ∑ h ∈ Finset.Icc 1 q, g h := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos q), hIcc]
  rw [Finset.sum_range_succ, hper] at h3
  rw [h1]
  linear_combination (-1 : ℂ) * h3

/-- Möbius inversion of the coprimality condition: $c_q(n) = \sum_{d \mid q}\mu(d)\sum_{0 \le h < q,\ d \mid h}
\omega_q^{hn}$. -/
private lemma ram_moebius {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ramanujanSum q n = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        ∑ h ∈ (Finset.range q).filter (d ∣ ·), omega q ^ (h * n) := by
  rw [ram_range hq]
  have step : ∀ h : ℕ, (if Nat.Coprime h q then omega q ^ (h * n) else 0) =
      ∑ d ∈ (Nat.gcd h q).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * omega q ^ (h * n) := by
    intro h
    rw [← Finset.sum_mul]
    have h' : ∑ d ∈ (Nat.gcd h q).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
        if Nat.gcd h q = 1 then 1 else 0 := by
      exact_mod_cast sum_moebius (Nat.gcd h q)
    by_cases hc : Nat.Coprime h q
    · have e : Nat.gcd h q = 1 := hc
      rw [h', if_pos e, if_pos hc, one_mul]
    · have e : ¬ Nat.gcd h q = 1 := hc
      rw [h', if_neg e, if_neg hc, zero_mul]
  simp_rw [step]
  have hmem : ∀ h d : ℕ, (h ∈ Finset.range q ∧ d ∈ (Nat.gcd h q).divisors) ↔
      (h ∈ (Finset.range q).filter (d ∣ ·) ∧ d ∈ q.divisors) := by
    intro h d
    simp only [Finset.mem_range, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg0 : Nat.gcd h q ≠ 0 := (Nat.gcd_pos_of_pos_right h hq).ne'
    constructor
    · rintro ⟨hh, ⟨h1, h2⟩, _⟩
      exact ⟨⟨hh, h1⟩, h2, hq.ne'⟩
    · rintro ⟨⟨hh, h1⟩, h2, _⟩
      exact ⟨hh, ⟨h1, h2⟩, hg0⟩
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]

/-- The inner sum: for $d \mid q$, $\sum_{0 \le h < q,\ d \mid h}\omega_q^{hn}$ is $q/d$ if $q/d \mid n$ and $0$
otherwise. -/
private lemma inner_sum {q d : ℕ} (hq : 0 < q) (hd : d ∣ q) (n : ℕ) :
    ∑ h ∈ (Finset.range q).filter (d ∣ ·), omega q ^ (h * n) =
      if q / d ∣ n then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, hm⟩ := hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos ⟨m, hm⟩ hq
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  have hqd : q / d = m := by rw [hm]; exact Nat.mul_div_cancel_left m hdpos
  have himg : (Finset.range q).filter (d ∣ ·) = (Finset.range m).image (d * ·) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hh, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      rw [hm] at hh
      exact Nat.lt_of_mul_lt_mul_left hh
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, dvd_mul_right d k⟩
      rw [hm]
      nlinarith
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hω : omega q ^ d = omega m := by
    unfold omega
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [hm]
    push_cast
    field_simp
  rw [himg, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hdpos h)]
  have : ∀ k ∈ Finset.range m, omega q ^ (d * k * n) = (omega m ^ n) ^ k := by
    intro k _
    rw [show d * k * n = d * (n * k) by ring, pow_mul, hω, pow_mul]
  rw [Finset.sum_congr rfl this, geom_omega hmpos n, hqd]

private lemma divisors_gcd_eq {q : ℕ} (hq : 0 < q) (n : ℕ) :
    (Nat.gcd q n).divisors = q.divisors.filter (· ∣ n) := by
  ext e
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  have : Nat.gcd q n ≠ 0 := (Nat.gcd_pos_of_pos_left n hq).ne'
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    exact ⟨⟨h1, hq.ne'⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨⟨h1, h2⟩, this⟩

/-- **Ramanujan sums as divisor sums** (Moreno–Wagstaff §6.4.2, p. 205): for $q \ge 1$ and $n \ge 0$,
$c_q(n) = \sum_{d \mid \gcd(q,n)} d\,\mu(q/d)$ (an integer). Hypothesis: $q \ge 1$. -/
theorem ramanujanSum_eq_sum_gcd {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ramanujanSum q n =
      ((∑ d ∈ (Nat.gcd q n).divisors, (d : ℤ) * ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) := by
  rw [ram_moebius hq]
  have h1 : ∀ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ∑ h ∈ (Finset.range q).filter (d ∣ ·), omega q ^ (h * n) =
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (if q / d ∣ n then ((q / d : ℕ) : ℂ) else 0) :=
    fun d hd => by rw [inner_sum hq (Nat.dvd_of_mem_divisors hd) n]
  rw [Finset.sum_congr rfl h1]
  have h2 := Nat.sum_div_divisors q
    (fun e => ((ArithmeticFunction.moebius (q / e) : ℤ) : ℂ) * (if e ∣ n then (e : ℂ) else 0))
  have h3 : ∀ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      (if q / d ∣ n then ((q / d : ℕ) : ℂ) else 0) =
      (fun e => ((ArithmeticFunction.moebius (q / e) : ℤ) : ℂ) * (if e ∣ n then (e : ℂ) else 0)) (q / d) := by
    intro d hd
    have : q / (q / d) = d := Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne'
    simp only [this]
  rw [Finset.sum_congr rfl h3, h2, divisors_gcd_eq hq n, Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · ring
  · simp

/-- $d \mapsto d\,[d \mid n]$ (zero at $0$) as an arithmetic function. -/
private noncomputable def ramG (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun d => if d = 0 then 0 else if d ∣ n then (d : ℤ) else 0, by simp⟩

private lemma ramG_mult (n : ℕ) : (ramG n).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {a b} ha hb hab => ?_⟩
  · simp [ramG]
  · have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
    simp only [ramG, ArithmeticFunction.coe_mk, ha, hb, hab0, ite_false]
    by_cases h1 : a ∣ n <;> by_cases h2 : b ∣ n
    · have : a * b ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hab h1 h2
      simp [h1, h2, this]
    · have : ¬ a * b ∣ n := fun h => h2 (dvd_trans (dvd_mul_left b a) h)
      simp [h1, h2, this]
    · have : ¬ a * b ∣ n := fun h => h1 (dvd_trans (dvd_mul_right a b) h)
      simp [h1, h2, this]
    · have : ¬ a * b ∣ n := fun h => h1 (dvd_trans (dvd_mul_right a b) h)
      simp [h1, h2, this]

private lemma ramA_eq {q : ℕ} (hq : 0 < q) (n : ℕ) :
    (ramG n * ArithmeticFunction.moebius) q =
      ∑ d ∈ (Nat.gcd q n).divisors, (d : ℤ) * ArithmeticFunction.moebius (q / d) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun a b => (ramG n) a * ArithmeticFunction.moebius b),
    divisors_gcd_eq hq n, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  by_cases hdn : d ∣ n <;> simp [ramG, hd0, hdn]

private lemma ram_eq_conv {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ramanujanSum q n = (((ramG n * ArithmeticFunction.moebius) q : ℤ) : ℂ) := by
  rw [ramanujanSum_eq_sum_gcd hq n, ramA_eq hq n]

/-- **Multiplicativity of Ramanujan sums in $q$** (Moreno–Wagstaff §6.4.2, p. 205): for coprime $q_1, q_2 \ge 1$ and
every $n$, $c_{q_1q_2}(n) = c_{q_1}(n)\,c_{q_2}(n)$. -/
theorem ramanujanSum_mul {q₁ q₂ : ℕ} (h1 : 0 < q₁) (h2 : 0 < q₂) (h : Nat.Coprime q₁ q₂) (n : ℕ) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  rw [ram_eq_conv (Nat.mul_pos h1 h2), ram_eq_conv h1, ram_eq_conv h2]
  have hm : (ramG n * ArithmeticFunction.moebius).IsMultiplicative :=
    (ramG_mult n).mul ArithmeticFunction.isMultiplicative_moebius
  rw [hm.map_mul_of_coprime h]
  push_cast
  rfl

/-! ### The closed form $c_q(n) = \mu(q')\varphi(q)/\varphi(q')$ -/

private lemma mu_pp_zero {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    ArithmeticFunction.moebius (p ^ k) = 0 := by
  rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]

/-- The prime-power sum $\sum_{i \le j} p^i\mu(p^{a-i})$ ($j \le a$): it is $\varphi(p^a)$ if $j = a$, $-p^j$ if
$j + 1 = a$, and $0$ otherwise. -/
private lemma pp_sum {p : ℕ} (hp : p.Prime) {j a : ℕ} (hja : j ≤ a) :
    ∑ i ∈ Finset.range (j + 1), (p : ℤ) ^ i * ArithmeticFunction.moebius (p ^ (a - i)) =
      if j = a then ((p ^ a).totient : ℤ) else if j + 1 = a then -(p : ℤ) ^ j else 0 := by
  by_cases h1 : j = a
  · subst h1
    rw [if_pos rfl]
    rcases j with _ | j
    · simp
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have e0 : ∀ i ∈ Finset.range j,
          (p : ℤ) ^ i * ArithmeticFunction.moebius (p ^ (j + 1 - i)) = 0 := by
        intro i hi
        rw [mu_pp_zero hp (by have := Finset.mem_range.1 hi; omega), mul_zero]
      rw [Finset.sum_eq_zero e0]
      have e1 : j + 1 - j = 1 := by omega
      rw [e1, Nat.sub_self, pow_one, pow_zero, ArithmeticFunction.moebius_apply_prime hp,
        ArithmeticFunction.moebius_apply_one, Nat.totient_prime_pow_succ hp j]
      push_cast [Nat.cast_sub hp.one_le]
      ring
  · by_cases h2 : j + 1 = a
    · subst h2
      rw [if_neg h1, if_pos rfl, Finset.sum_range_succ]
      have e0 : ∀ i ∈ Finset.range j,
          (p : ℤ) ^ i * ArithmeticFunction.moebius (p ^ (j + 1 - i)) = 0 := by
        intro i hi
        rw [mu_pp_zero hp (by have := Finset.mem_range.1 hi; omega), mul_zero]
      rw [Finset.sum_eq_zero e0]
      have e1 : j + 1 - j = 1 := by omega
      rw [e1, pow_one, ArithmeticFunction.moebius_apply_prime hp]
      ring
    · rw [if_neg h1, if_neg h2]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [mu_pp_zero hp (by have := Finset.mem_range.1 hi; omega), mul_zero]

private lemma pp_identity {p : ℕ} (hp : p.Prime) {j a : ℕ} (hja : j ≤ a) :
    (∑ i ∈ Finset.range (j + 1), (p : ℤ) ^ i * ArithmeticFunction.moebius (p ^ (a - i))) *
        ((p ^ (a - j)).totient : ℤ) =
      ArithmeticFunction.moebius (p ^ (a - j)) * ((p ^ a).totient : ℤ) := by
  rw [pp_sum hp hja]
  by_cases h1 : j = a
  · subst h1; simp
  · by_cases h2 : j + 1 = a
    · subst h2
      rw [if_neg h1, if_pos rfl]
      have e1 : j + 1 - j = 1 := by omega
      rw [e1, pow_one, Nat.totient_prime hp, ArithmeticFunction.moebius_apply_prime hp,
        Nat.totient_prime_pow_succ hp j]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    · rw [if_neg h1, if_neg h2, zero_mul, mu_pp_zero hp (by omega), zero_mul]

/-- The cross-multiplied Hölder identity at a prime power $p^a$ (integers):
$c_{p^a}(n)\,\varphi(q') = \mu(q')\,\varphi(p^a)$ with $q' = p^a/\gcd(p^a, n)$. -/
private lemma ram_pp {p : ℕ} (a : ℕ) (hp : p.Prime) (n : ℕ) :
    ((ramG n * ArithmeticFunction.moebius) (p ^ a)) *
        (((p ^ a) / Nat.gcd (p ^ a) n).totient : ℤ) =
      ArithmeticFunction.moebius (p ^ a / Nat.gcd (p ^ a) n) * ((p ^ a).totient : ℤ) := by
  obtain ⟨j, hja, hj⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (p ^ a) n)
  have hsum : ∑ d ∈ (p ^ j).divisors, (d : ℤ) * ArithmeticFunction.moebius (p ^ a / d) =
      ∑ i ∈ Finset.range (j + 1), (p : ℤ) ^ i * ArithmeticFunction.moebius (p ^ (a - i)) := by
    rw [Nat.divisors_prime_pow hp, Finset.sum_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Function.Embedding.coeFn_mk]
    rw [Nat.pow_div (by have := Finset.mem_range.1 hi; omega) hp.pos]
    push_cast
    rfl
  rw [ramA_eq (pow_pos hp.pos a) n, hj, hsum, Nat.pow_div hja hp.pos]
  exact pp_identity hp hja

private lemma totient_quot_pos {q : ℕ} (hq : 0 < q) (n : ℕ) : 0 < (q / Nat.gcd q n).totient :=
  Nat.totient_pos.2 (Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q n)) (Nat.gcd_pos_of_pos_left n hq))

/-- The right-hand side of Hölder's formula as an arithmetic function of $q$ (zero at $q = 0$). -/
private noncomputable def ramR (n : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => if q = 0 then 0 else
    ((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℂ) * (q.totient : ℂ) /
      ((q / Nat.gcd q n).totient : ℂ), by simp⟩

private lemma ramR_mult (n : ℕ) : (ramR n).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {a b} ha hb hab => ?_⟩
  · simp [ramR]
  · have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
    simp only [ramR, ArithmeticFunction.coe_mk, ha, hb, hab0, ite_false]
    have hda : Nat.gcd a n ∣ a := Nat.gcd_dvd_left a n
    have hdb : Nat.gcd b n ∣ b := Nat.gcd_dvd_left b n
    have hg : Nat.gcd (a * b) n = Nat.gcd a n * Nat.gcd b n := by
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul n hab, Nat.gcd_comm n a, Nat.gcd_comm n b]
    have hQ : a * b / Nat.gcd (a * b) n = (a / Nat.gcd a n) * (b / Nat.gcd b n) := by
      rw [hg, Nat.div_mul_div_comm hda hdb]
    have hcop : Nat.Coprime (a / Nat.gcd a n) (b / Nat.gcd b n) :=
      (hab.coprime_dvd_left (Nat.div_dvd_of_dvd hda)).coprime_dvd_right (Nat.div_dvd_of_dvd hdb)
    rw [hQ, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      Nat.totient_mul hab, Nat.totient_mul hcop]
    push_cast
    rw [div_mul_div_comm]
    ring

private lemma ramR_eq (n : ℕ) :
    ramR n = ((ramG n * ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (ramR_mult n) _
    (((ramG_mult n).mul ArithmeticFunction.isMultiplicative_moebius).intCast)).2 ?_
  intro p a hp
  have hq : 0 < p ^ a := pow_pos hp.pos a
  rw [ArithmeticFunction.intCoe_apply]
  simp only [ramR, ArithmeticFunction.coe_mk, hq.ne', ite_false]
  have hφ : (((p ^ a / Nat.gcd (p ^ a) n).totient : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (totient_quot_pos hq n).ne'
  rw [div_eq_iff hφ]
  exact_mod_cast (ram_pp a hp n).symm

/-- **Hölder's formula** (Moreno–Wagstaff §6.4.2, p. 205): for $q \ge 1$ and $n \ge 0$,
$c_q(n) = \dfrac{\varphi(q)}{\varphi(q')}\,\mu(q')$ with $q' = q/\gcd(n,q)$. Hypothesis: $q \ge 1$. -/
theorem ramanujanSum_holder {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ramanujanSum q n = ((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℂ) * (q.totient : ℂ) /
      ((q / Nat.gcd q n).totient : ℂ) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f q) (ramR_eq n)
  simp only [ArithmeticFunction.intCoe_apply] at h
  rw [ram_eq_conv hq n, ← h]
  simp only [ramR, ArithmeticFunction.coe_mk, hq.ne', ite_false]

/-- **Moreno–Wagstaff, §6.4.2, Row 6.r6** (p. 205), Ramanujan sums $c_q(n) = \sum_{1 \le h \le q,\ (h,q)=1}
e^{(2\pi i/q)hn}$ (`ramanujanSum`). For $q, q_1, q_2 \ge 1$ and $n \ge 0$:
1. $c_q(n) = \sum_{d \mid \gcd(q,n)} d\,\mu(q/d)$;
2. $c_q(n)$ is multiplicative in $q$: $c_{q_1q_2}(n) = c_{q_1}(n)c_{q_2}(n)$ for coprime $q_1, q_2$;
3. $c_q(n) = \dfrac{\varphi(q)}{\varphi(q')}\mu(q')$, $q' = q/\gcd(n,q)$. -/
@[kb "morenowagstaff2005" "Row 6.r6 (§6.4.2), p. 205"]
def RowR6 : Prop :=
  (∀ q n : ℕ, 0 < q → ramanujanSum q n =
      ((∑ d ∈ (Nat.gcd q n).divisors, (d : ℤ) * ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)) ∧
  (∀ q₁ q₂ n : ℕ, 0 < q₁ → 0 < q₂ → Nat.Coprime q₁ q₂ →
      ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n) ∧
  (∀ q n : ℕ, 0 < q → ramanujanSum q n =
      ((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℂ) * (q.totient : ℂ) /
        ((q / Nat.gcd q n).totient : ℂ))

/-- **Row 6.r6** (p. 205), proved: `ramanujanSum_eq_sum_gcd`, `ramanujanSum_mul`, `ramanujanSum_holder`. -/
theorem rowR6 : RowR6 :=
  ⟨fun q n hq => ramanujanSum_eq_sum_gcd hq n,
    fun q₁ q₂ n h1 h2 h => ramanujanSum_mul h1 h2 h n,
    fun q n hq => ramanujanSum_holder hq n⟩

end QuadFormsKB.MorenoWagstaff
