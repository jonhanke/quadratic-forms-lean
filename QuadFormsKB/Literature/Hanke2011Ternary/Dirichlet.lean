/-
# Hanke 2011 (ternary masses): formal Dirichlet series

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`).

A formal Dirichlet series $\sum_{n \ge 1} a_n n^{-s}$ with rational coefficients is an arithmetic function
`ArithmeticFunction ℚ` (Mathlib); the product of Dirichlet series is Dirichlet convolution `*`.

* `powPush k h`: the series $\sum_{m \ge 1} h(m)\,(m^k)^{-s}$ (coefficient $h(m)$ at $n = m^k$, else $0$).
* `zetaShift k j` $= \zeta(ks + j) = \sum_m m^{-j}(m^k)^{-s}$, `zetaShiftInv k j`
  $= \sum_m \mu(m)m^{-j}(m^k)^{-s}$, which is its inverse (`zetaShift_mul_zetaShiftInv`), i.e. $1/\zeta(ks + j)$;
  `twoPowNegS` $= 2^{-s}$ (coefficient $1$ at $n = 2$).
* `localSeries f p` $= \sum_k f(p^k)X^k$, the Euler factor of $f$ at $p$ in $X = p^{-s}$; for convolutions it is
  multiplicative (`localSeries_mul`), and a multiplicative $f$ is determined by its Euler factors.
-/
import QuadFormsKB.Literature.Hanke2011Ternary.Series

namespace QuadFormsKB.Hanke2011Ternary

open PowerSeries Finset ArithmeticFunction

/-- **The series $\sum_{m\ge1} h(m)(m^k)^{-s}$**: the coefficient of $n^{-s}$ is $h(m)$ if $n = m^k$, else $0$. -/
noncomputable def powPush (k : ℕ) (h : ℕ → ℚ) : ArithmeticFunction ℚ :=
  ⟨fun n => ∑ m ∈ n.divisors, if m ^ k = n then h m else 0, by simp⟩

theorem powPush_apply (k : ℕ) (h : ℕ → ℚ) (n : ℕ) :
    powPush k h n = ∑ m ∈ n.divisors, if m ^ k = n then h m else 0 := rfl

theorem powPush_apply_pow {k : ℕ} (hk : 0 < k) (h : ℕ → ℚ) {m : ℕ} (hm : m ≠ 0) :
    powPush k h (m ^ k) = h m := by
  rw [powPush_apply, Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro hbm
    exact hb (Nat.pow_left_injective hk.ne' hbm)
  · intro hm'
    exact absurd (Nat.mem_divisors.mpr ⟨dvd_pow_self m hk.ne', pow_ne_zero k hm⟩) hm'

theorem powPush_apply_of_not {k : ℕ} (h : ℕ → ℚ) {n : ℕ} (hn : ¬ ∃ m, m ^ k = n) : powPush k h n = 0 := by
  rw [powPush_apply]
  exact Finset.sum_eq_zero fun m _ => by rw [if_neg (fun hm => hn ⟨m, hm⟩)]

/-- `powPush k h` is multiplicative when $h$ is (and $k \ge 1$). -/
theorem isMultiplicative_powPush {k : ℕ} (hk : 0 < k) {h : ℕ → ℚ} (h1 : h 1 = 1)
    (hmul : ∀ a b, Nat.Coprime a b → h (a * b) = h a * h b) : IsMultiplicative (powPush k h) := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simpa [h1] using powPush_apply_pow hk h one_ne_zero, ?_⟩
  intro a b ha hb hab
  by_cases hA : ∃ x, x ^ k = a
  · by_cases hB : ∃ y, y ^ k = b
    · obtain ⟨x, rfl⟩ := hA
      obtain ⟨y, rfl⟩ := hB
      have hx : x ≠ 0 := by rintro rfl; simp [hk.ne'] at ha
      have hy : y ≠ 0 := by rintro rfl; simp [hk.ne'] at hb
      have hxy : Nat.Coprime x y := (Nat.coprime_pow_left_iff hk _ _).mp ((Nat.coprime_pow_right_iff hk _ _).mp hab)
      rw [← mul_pow, powPush_apply_pow hk h (mul_ne_zero hx hy), powPush_apply_pow hk h hx,
        powPush_apply_pow hk h hy, hmul x y hxy]
    · rw [powPush_apply_of_not h hB, mul_zero, powPush_apply_of_not h]
      rintro ⟨z, hz⟩
      apply hB
      obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (α := ℕ) (a := b) (b := a)
        (Nat.isUnit_iff.mpr (hab.symm : Nat.gcd b a = 1)) (by rw [mul_comm]; exact hz.symm)
      exact ⟨d, hd.symm⟩
  · rw [powPush_apply_of_not h hA, zero_mul, powPush_apply_of_not h]
    rintro ⟨z, hz⟩
    apply hA
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (α := ℕ) (a := a) (b := b)
      (Nat.isUnit_iff.mpr (hab : Nat.gcd a b = 1)) hz.symm
    exact ⟨d, hd.symm⟩

/-- The value of `powPush k h` at a prime power: $h(p^{j/k})$ if $k \mid j$, else $0$. -/
theorem powPush_apply_prime_pow {k : ℕ} (hk : 0 < k) (h : ℕ → ℚ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    powPush k h (p ^ j) = if k ∣ j then h (p ^ (j / k)) else 0 := by
  split_ifs with hkj
  · obtain ⟨i, rfl⟩ := hkj
    rw [Nat.mul_div_cancel_left _ hk, mul_comm, pow_mul, powPush_apply_pow hk h (pow_ne_zero _ hp.ne_zero)]
  · apply powPush_apply_of_not
    rintro ⟨m, hm⟩
    have hdvd : m ∣ p ^ j := hm ▸ dvd_pow_self m hk.ne'
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [← pow_mul] at hm
    exact hkj ⟨i, by have := Nat.pow_right_injective hp.two_le hm; rw [← this]; ring⟩

/-- **The Euler factor of $f$ at $p$**: $\sum_{k\ge0} f(p^k) X^k$ (with $X = p^{-s}$). -/
noncomputable def localSeries (f : ArithmeticFunction ℚ) (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => f (p ^ k)

/-- Dirichlet convolution at a prime power: $(f*g)(p^k) = \sum_{i \le k} f(p^i)g(p^{k-i})$. -/
theorem mul_apply_prime_pow (f g : ArithmeticFunction ℚ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]

/-- **Euler factors of a product of Dirichlet series multiply.** -/
theorem localSeries_mul (f g : ArithmeticFunction ℚ) {p : ℕ} (hp : p.Prime) :
    localSeries (f * g) p = localSeries f p * localSeries g p := by
  ext k
  rw [localSeries, coeff_mk, mul_apply_prime_pow f g hp, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [localSeries, coeff_mk]

theorem localSeries_powPush {k : ℕ} (hk : 0 < k) (h : ℕ → ℚ) {p : ℕ} (hp : p.Prime) :
    localSeries (powPush k h) p = spread k (fun i => h (p ^ i)) := by
  ext j
  rw [localSeries, coeff_mk, powPush_apply_prime_pow hk h hp, coeff_spread]

theorem localSeries_one {p : ℕ} (hp : p.Prime) : localSeries 1 p = 1 := by
  ext k
  rw [localSeries, coeff_mk, coeff_one, one_apply]
  rcases k with _ | k
  · simp
  · simp [hp.ne_one]

/-- Two multiplicative arithmetic functions with the same Euler factors at every prime are equal. -/
theorem eq_of_localSeries {f g : ArithmeticFunction ℚ} (hf : IsMultiplicative f) (hg : IsMultiplicative g)
    (h : ∀ p : ℕ, p.Prime → localSeries f p = localSeries g p) : f = g := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg]
  intro p k hp
  have := congrArg (coeff k) (h p hp)
  simpa [localSeries] using this

/-- **$\zeta(ks + j)$ as a formal Dirichlet series**: $\sum_{m\ge1} m^{-j}(m^k)^{-s}$. -/
@[kb "hanke2011ternary" "§1, Thm. 1.1 and §7–8 (zeta functions as formal Dirichlet series)"]
noncomputable def zetaShift (k j : ℕ) : ArithmeticFunction ℚ := powPush k fun m => ((m : ℚ)⁻¹) ^ j

/-- **$1/\zeta(ks + j)$ as a formal Dirichlet series**: $\sum_{m\ge1} \mu(m)m^{-j}(m^k)^{-s}$
(the inverse of `zetaShift k j`, `zetaShift_mul_zetaShiftInv`). -/
@[kb "hanke2011ternary" "§1, Thm. 1.1 and §7–8 (zeta functions as formal Dirichlet series)"]
noncomputable def zetaShiftInv (k j : ℕ) : ArithmeticFunction ℚ :=
  powPush k fun m => (ArithmeticFunction.moebius m : ℚ) * ((m : ℚ)⁻¹) ^ j

/-- **$2^{-s}$ as a formal Dirichlet series** (coefficient $1$ at $n = 2$). -/
@[kb "hanke2011ternary" "§1, Thm. 1.1 and §7–8"]
noncomputable def twoPowNegS : ArithmeticFunction ℚ := ⟨fun n => if n = 2 then 1 else 0, by simp⟩

theorem isMultiplicative_zetaShift {k : ℕ} (hk : 0 < k) (j : ℕ) : IsMultiplicative (zetaShift k j) :=
  isMultiplicative_powPush hk (by simp) (fun a b _ => by push_cast; rw [mul_inv, mul_pow])

theorem isMultiplicative_zetaShiftInv {k : ℕ} (hk : 0 < k) (j : ℕ) : IsMultiplicative (zetaShiftInv k j) :=
  isMultiplicative_powPush hk (by simp) (fun a b hab => by
    rw [isMultiplicative_moebius.map_mul_of_coprime hab]; push_cast; rw [mul_inv, mul_pow]; ring)

theorem localSeries_zetaShift {k : ℕ} (hk : 0 < k) (j : ℕ) {p : ℕ} (hp : p.Prime) :
    localSeries (zetaShift k j) p = spread k (fun i => ((p : ℚ)⁻¹ ^ j) ^ i) := by
  rw [zetaShift, localSeries_powPush hk _ hp]
  congr 1; funext i; push_cast; rw [← inv_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem localSeries_zetaShiftInv {k : ℕ} (hk : 0 < k) (j : ℕ) {p : ℕ} (hp : p.Prime) :
    localSeries (zetaShiftInv k j) p = 1 - C ((p : ℚ)⁻¹ ^ j) * X ^ k := by
  rw [zetaShiftInv, localSeries_powPush hk _ hp]
  ext n
  rw [coeff_spread, map_sub, coeff_one, coeff_C_mul_X_pow]
  by_cases hkn : k ∣ n
  · obtain ⟨i, rfl⟩ := hkn
    rw [if_pos (dvd_mul_right k i), Nat.mul_div_cancel_left _ hk]
    rcases i with _ | _ | i
    · simp [hk.ne'.symm]
    · simp [moebius_apply_prime hp, hk.ne']
    · have h1 : k * (i + 2) ≠ 0 := Nat.mul_ne_zero hk.ne' (by omega)
      have h2 : k * (i + 2) ≠ k := by
        intro h; have := Nat.eq_of_mul_eq_mul_left hk (h.trans (mul_one k).symm); omega
      rw [moebius_apply_prime_pow hp (by omega), if_neg h1, if_neg h2]
      simp
  · rw [if_neg hkn, if_neg (by rintro rfl; exact hkn (dvd_zero k)), if_neg (by rintro rfl; exact hkn dvd_rfl)]
    simp

/-- $\zeta(ks+j)\cdot\dfrac{1}{\zeta(ks+j)} = 1$: `zetaShiftInv k j` is the inverse of `zetaShift k j`. -/
theorem zetaShift_mul_zetaShiftInv {k : ℕ} (hk : 0 < k) (j : ℕ) : zetaShift k j * zetaShiftInv k j = 1 := by
  apply eq_of_localSeries ((isMultiplicative_zetaShift hk j).mul (isMultiplicative_zetaShiftInv hk j))
    isMultiplicative_one
  intro p hp
  rw [localSeries_mul _ _ hp, localSeries_zetaShift hk j hp, localSeries_zetaShiftInv hk j hp, localSeries_one hp]
  exact spread_geom_mul k hk _

end QuadFormsKB.Hanke2011Ternary
