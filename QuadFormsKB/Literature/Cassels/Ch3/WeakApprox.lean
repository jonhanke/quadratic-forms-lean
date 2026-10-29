/-
# Cassels, Chapter 3: weak approximation for $\mathbb Q$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *$p$-adic numbers*, p. 45.

**Setting.** $\mathbb Q_p$ = Mathlib's `ℚ_[p]` with its norm $\lvert\cdot\rvert_p$ (`‖·‖`); the archimedean absolute
value on $\mathbb R$ is `|·|`. A finite set of primes is a `Finset Nat.Primes`; rational numbers are cast into
$\mathbb Q_p$ and $\mathbb R$.

**Proves.**
* Lemma 3.2 (p. 45), `weak_approximation`: for a finite set $S$ of primes, $\alpha_p \in \mathbb Q_p$ ($p \in S$),
  $\alpha_\infty \in \mathbb R$ and $\varepsilon > 0$ there is $r \in \mathbb Q$ with $\lvert r - \alpha_p\rvert_p < \varepsilon$
  for all $p \in S$ and $\lvert r - \alpha_\infty\rvert < \varepsilon$. Checked against the printed page (p. 45) on 2026-10-27: the same
  statement (Cassels: $P$ a finite set of primes, possibly including $\infty$).

**Proof notes.** Fix $m$ with $\lvert\alpha_p\rvert_p \le 2^m$ for all $p \in S$ and put $M = \prod_{p \in S} p^m$,
so $M\alpha_p \in \mathbb Z_p$. The Chinese remainder theorem (as in strong approximation, repeated here so that the
file depends only on Mathlib) gives an integer $x$ with $x$ close to $M\alpha_p$ for all $p \in S$, hence $x/M$ close
to $\alpha_p$. Then correct the real place: with $q = \prod_{p \in S} p^K$ ($K$ large, so $q$ is $p$-adically tiny)
and a prime $\ell > M$ (so $\ell$ is a $p$-adic unit), the numbers $q u / \ell^j$ with $u \in \mathbb Z$ are $p$-adically
small and, for $j$ large, form a $q/\ell^j$-net of $\mathbb R$. Take $r = x/M + qu/\ell^j$.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

/-- Primes in `Nat.Primes` are prime. -/
local instance factPrimesWA (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- Chinese remainder step: for finitely many primes, each $z_p \in \mathbb Z_p$ and each $\varepsilon > 0$,
some integer is within $\varepsilon$ of every $z_p$. -/
theorem exists_int_close_padicInt (P : Finset Nat.Primes) (z : ∀ p : Nat.Primes, ℤ_[p]) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : ℤ, ∀ p ∈ P, ‖(x : ℤ_[p]) - z p‖ < ε := by
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

/-- A $p$-adic number of norm at most one is the image of an element of $\mathbb Z_p$. -/
theorem exists_padicInt_coe (p : ℕ) [Fact p.Prime] {a : ℚ_[p]} (h : ‖a‖ ≤ 1) :
    ∃ z : ℤ_[p], (z : ℚ_[p]) = a :=
  ⟨⟨a, h⟩, rfl⟩

/-- The $p$-adic norm of $\prod_{q \in S} q^k$ is at most $2^{-k}$ at each prime $p \in S$. -/
theorem norm_prod_pow_le (S : Finset Nat.Primes) (k : ℕ) {p : Nat.Primes} (hp : p ∈ S) :
    ‖((∏ q ∈ S, (q : ℕ) ^ k : ℕ) : ℚ_[p])‖ ≤ (1 / 2 : ℝ) ^ k := by
  rw [← Finset.mul_prod_erase S _ hp, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow, Padic.norm_p]
  have h2 : ‖(((∏ q ∈ S.erase p, (q : ℕ) ^ k : ℕ)) : ℚ_[p])‖ ≤ 1 := by
    exact_mod_cast Padic.norm_int_le_one (p := p) (((∏ q ∈ S.erase p, (q : ℕ) ^ k : ℕ)) : ℤ)
  have h1 : ((p : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    exact_mod_cast p.2.two_le
  calc ((p : ℕ) : ℝ)⁻¹ ^ k * ‖(((∏ q ∈ S.erase p, (q : ℕ) ^ k : ℕ)) : ℚ_[p])‖
      ≤ (1 / 2 : ℝ) ^ k * 1 := by gcongr
    _ = (1 / 2 : ℝ) ^ k := mul_one _

/-- A nonzero natural number has $p$-adic norm at least its reciprocal. -/
theorem inv_le_norm_natCast (p : Nat.Primes) {n : ℕ} (hn : n ≠ 0) :
    ((n : ℝ))⁻¹ ≤ ‖(n : ℚ_[p])‖ := by
  have h : ‖((n : ℚ) : ℚ_[p])‖ = padicNorm p (n : ℚ) := Padic.eq_padicNorm _
  rw [show ((n : ℕ) : ℚ_[p]) = ((n : ℚ) : ℚ_[p]) by simp, h,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat, zpow_neg, zpow_natCast]
  have hle : (p : ℕ) ^ padicValNat p n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ padicValNat p n := by have := p.2.pos; positivity
  push_cast
  exact inv_anti₀ hpos (by exact_mod_cast hle)

/-- A prime number $\ell$ larger than the prime $p$ has $p$-adic norm one. -/
theorem norm_natCast_eq_one_of_prime_gt (p : Nat.Primes) {ℓ : ℕ} (hℓ : ℓ.Prime) (h : (p : ℕ) < ℓ) :
    ‖(ℓ : ℚ_[p])‖ = 1 := by
  have h1 : ‖((ℓ : ℚ) : ℚ_[p])‖ = padicNorm p (ℓ : ℚ) := Padic.eq_padicNorm _
  rw [show ((ℓ : ℕ) : ℚ_[p]) = ((ℓ : ℚ) : ℚ_[p]) by simp, h1]
  have hf : padicNorm (p : ℕ) (ℓ : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq p.2 hℓ).mp hd
    omega
  rw [hf]; simp

/-- **Cassels, Ch. 3, Lemma 3.2 (Weak Approximation Theorem for $\mathbb Q$).** Let $S$ be a finite set of
primes, let $\alpha_p \in \mathbb Q_p$ for $p \in S$ and $\alpha_\infty \in \mathbb R$ be given, and let
$\varepsilon > 0$. Then there is a rational number $r$ with $\lvert r - \alpha_p\rvert_p < \varepsilon$ for all
$p \in S$ and $\lvert r - \alpha_\infty\rvert < \varepsilon$. (Checked against the printed page, p. 45,
on 2026-10-27: the same statement.) -/
@[kb "cassels1978" "Ch. 3, Lemma 3.2, p. 45"]
theorem weak_approximation (S : Finset Nat.Primes) (α : ∀ p : Nat.Primes, ℚ_[p]) (aInf : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℚ, (∀ p ∈ S, ‖(r : ℚ_[p]) - α p‖ < ε) ∧ |(r : ℝ) - aInf| < ε := by
  -- Step 1: choose m with ‖α p‖ ≤ 2^m on S, and set M = ∏ p^m.
  obtain ⟨m0, hm0⟩ := pow_unbounded_of_one_lt (∑ p ∈ S, ‖α p‖) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ ∑ p ∈ S, ‖α p‖ < 2 ^ m :=
    ⟨m0 + 1, by omega, lt_of_lt_of_le hm0 (pow_le_pow_right₀ (by norm_num) (by omega))⟩
  set M : ℕ := ∏ p ∈ S, (p : ℕ) ^ m with hMdef
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.2.ne_zero
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
  have hint : ∀ p ∈ S, ‖(M : ℚ_[p]) * α p‖ ≤ 1 := by
    intro p hp
    have hα : ‖α p‖ ≤ 2 ^ m :=
      (Finset.single_le_sum (f := fun p => ‖α p‖) (fun _ _ => norm_nonneg _) hp).trans hm.le
    rw [norm_mul]
    calc ‖(M : ℚ_[p])‖ * ‖α p‖ ≤ (1 / 2 : ℝ) ^ m * 2 ^ m :=
          mul_le_mul (norm_prod_pow_le S m hp) hα (norm_nonneg _) (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  -- Step 2: an integer x with x/M close to α p.
  have hεM : 0 < ε / M := div_pos hε hMpos
  have hz : ∀ p : Nat.Primes, ∃ z : ℤ_[p], p ∈ S → (z : ℚ_[p]) = M * α p := fun p => by
    by_cases hp : p ∈ S
    · obtain ⟨z, hz⟩ := exists_padicInt_coe p (hint p hp)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose z hzS using hz
  obtain ⟨x, hx⟩ := exists_int_close_padicInt S z hεM
  have hx' : ∀ p ∈ S, ‖(x : ℚ_[p]) - (M : ℚ_[p]) * α p‖ < ε / M := by
    intro p hp
    have := hx p hp
    rw [PadicInt.norm_def] at this
    rwa [PadicInt.coe_sub, PadicInt.coe_intCast, hzS p hp] at this
  have hr0 : ∀ p ∈ S, ‖(((x : ℚ) / M : ℚ) : ℚ_[p]) - α p‖ < ε := by
    intro p hp
    have hMne : (M : ℚ_[p]) ≠ 0 := by exact_mod_cast hM0
    have hnormpos : 0 < ‖(M : ℚ_[p])‖ := norm_pos_iff.mpr hMne
    have e : (((x : ℚ) / M : ℚ) : ℚ_[p]) - α p = ((x : ℚ_[p]) - (M : ℚ_[p]) * α p) / (M : ℚ_[p]) := by
      push_cast
      field_simp
    rw [e, norm_div, div_lt_iff₀ hnormpos]
    have hinv := inv_le_norm_natCast p hM0
    calc ‖(x : ℚ_[p]) - (M : ℚ_[p]) * α p‖ < ε / M := hx' p hp
      _ = ε * (M : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ ε * ‖(M : ℚ_[p])‖ := by gcongr
  -- Step 3: the real correction.
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  set q : ℕ := ∏ p ∈ S, (p : ℕ) ^ K with hqdef
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.2.ne_zero
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  obtain ⟨ℓ, hℓM, hℓ⟩ := Nat.exists_infinite_primes (M + 1)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((q : ℝ) / ε) hℓ1
  set β : ℝ := aInf - ((x : ℚ) / M : ℚ) with hβ
  set u : ℤ := ⌊β * (ℓ : ℝ) ^ j / q⌋ with hu
  refine ⟨(x : ℚ) / M + (q : ℚ) * u / (ℓ : ℚ) ^ j, fun p hp => ?_, ?_⟩
  · have hpM : (p : ℕ) < ℓ := by
      have h1 : (p : ℕ) ∣ M := by
        rw [hMdef]
        exact (dvd_pow_self _ (by omega)).trans (Finset.dvd_prod_of_mem _ hp)
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) h1
      omega
    have hl1 : ‖(ℓ : ℚ_[p])‖ = 1 := norm_natCast_eq_one_of_prime_gt p hℓ hpM
    have e : ((((x : ℚ) / M + (q : ℚ) * u / (ℓ : ℚ) ^ j : ℚ)) : ℚ_[p]) - α p
        = ((((x : ℚ) / M : ℚ)) : ℚ_[p]) - α p + (q : ℚ_[p]) * (u : ℚ_[p]) / (ℓ : ℚ_[p]) ^ j := by
      push_cast; ring
    have hc : ‖(q : ℚ_[p]) * (u : ℚ_[p]) / (ℓ : ℚ_[p]) ^ j‖ < ε := by
      rw [norm_div, norm_mul, norm_pow, hl1, one_pow, div_one]
      calc ‖(q : ℚ_[p])‖ * ‖(u : ℚ_[p])‖ ≤ (1 / 2 : ℝ) ^ K * 1 :=
            mul_le_mul (norm_prod_pow_le S K hp) (Padic.norm_int_le_one u) (norm_nonneg _)
              (by positivity)
        _ < ε := by rw [mul_one]; exact hK
    rw [e]
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt (hr0 p hp) hc)
  · have hℓj : (0 : ℝ) < (ℓ : ℝ) ^ j := by positivity
    have e : (((x : ℚ) / M + (q : ℚ) * u / (ℓ : ℚ) ^ j : ℚ) : ℝ) - aInf
        = (q : ℝ) * u / (ℓ : ℝ) ^ j - β := by
      rw [hβ]; push_cast; ring
    rw [e]
    have h1 : (u : ℝ) ≤ β * (ℓ : ℝ) ^ j / q := Int.floor_le _
    have h2 : β * (ℓ : ℝ) ^ j / q < u + 1 := Int.lt_floor_add_one _
    have key : (q : ℝ) * u / (ℓ : ℝ) ^ j - β =
        (q : ℝ) / (ℓ : ℝ) ^ j * ((u : ℝ) - β * (ℓ : ℝ) ^ j / q) := by
      field_simp
    have hlt : (q : ℝ) / (ℓ : ℝ) ^ j < ε := by
      rw [div_lt_iff₀ hℓj]
      rw [div_lt_iff₀ hε] at hj
      linarith
    have hpos : 0 < (q : ℝ) / (ℓ : ℝ) ^ j := div_pos hqpos hℓj
    rw [key, abs_mul, abs_of_pos hpos]
    have : |(u : ℝ) - β * (ℓ : ℝ) ^ j / q| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc (q : ℝ) / (ℓ : ℝ) ^ j * |(u : ℝ) - β * (ℓ : ℝ) ^ j / q|
        ≤ (q : ℝ) / (ℓ : ℝ) ^ j * 1 := by gcongr
      _ < ε := by rw [mul_one]; exact hlt

end QuadFormsKB.Cassels
