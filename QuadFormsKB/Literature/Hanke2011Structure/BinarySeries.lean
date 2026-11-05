/-
# Hanke 2011, §7: the binary Euler factors (Theorem 7.6, Remark 7.7)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §7.

For $n = 2$ and a prime $\mathfrak p$ of a number field $F$ with residue field of size $q$, the proof of Theorem 7.6
tabulates the local quantities $A^*_{\mathfrak p;2}(u\pi_{\mathfrak p}^\nu)$ and $B^*_{\mathfrak p;2}(u\pi_{\mathfrak p}^\nu)$
(Definition 4.6) for a unit squareclass $u$ and $\nu = \operatorname{ord}_{\mathfrak p}(S) \ge 0$. With
$\chi = \chi_u(\mathfrak p) = \left(\frac{-u}{\mathfrak p}\right) \in \{\pm 1\}$ and $\gamma = \gamma_{\mathfrak p}(u) = 1 - \chi/q$,
the second table of the proof reads:

* $\mathfrak p \nmid 2$: $A^* = 1$ for $\nu = 0$ and $A^* = q^{-\nu}\gamma$ for $\nu \ge 1$; $B^* = A^*$ for $\nu$ even and $B^* = 0$
  for $\nu$ odd (`aNondyadic`, `bNondyadic`).
* $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$ (so $q = 2$): $\nu = 1$ does not occur; for $\nu = 0$ there is a genus
  only when $u \equiv 3 \pmod 4$, with $A^* = 1$, $B^* = -1$; for $\nu \ge 2$, $A^* = 2^{-\nu}\gamma$, and $B^* = 2^{-\nu}\gamma$
  when $\nu$ is even and $u \equiv 3 \pmod 4$, $B^* = 0$ otherwise (`aDyadic`, `bDyadic`).

These tables rest on the Conway–Sloane $2$-adic mass formula and on Lemmas 7.2–7.3 (Lemma 7.2 is formalized in
`DyadicHasseTable.lean`, where its row $(\bar 2)$ is corrected: the genus with $\nu = 0$, $u \equiv 3 \bmod 4$ has
$c_2 = +1$, so the value $B^* = -1$ at $\nu = 0$ below should be $+1$ (*erratum knock-on*, proposed by the
formalization; `bDyadic` keeps the printed value)); this file
takes the table values as the definitions and proves what Theorem 7.6 derives from them: the "fixed unit" local
Dirichlet series $\sum_{\nu\ge0} A^*(u\pi^\nu)X^\nu$ and $\sum_{\nu\ge0}B^*(u\pi^\nu)X^\nu$, $X = q^{-s}$, are rational
functions of $X$. A rational identity $f = P/D$ is stated as the power series identity $D\cdot f = P$
(`PowerSeries K`, $K$ a field of characteristic $0$; $X$ is `PowerSeries.X`).

* `theorem_7_6_A_nondyadic`, `theorem_7_6_B_nondyadic`: the printed formulas for $\mathfrak p \nmid 2$,
  $\frac{1-\chi q^{-(s+2)}}{1-q^{-(s+1)}}$ and $\frac{1-\chi q^{-(2s+3)}}{1-q^{-(2s+2)}}$, hold.
* `theorem_7_6_B_dyadic_one`: for $\mathfrak p \mid 2$ and $u \equiv 1 \pmod 4$, $B^* = 0$, as printed.
* *Erratum* (proposed by the formalization), `theorem_7_6_B_dyadic_three` and
  `theorem_7_6_B_dyadic_three_printed_false`: for $\mathfrak p \mid 2$, $u \equiv 3 \pmod 4$, the series is
  $\frac{-1 + 2q^{-(2s+2)} - \chi q^{-(2s+3)}}{1 - q^{-(2s+2)}}$, as in the last display of the proof; the printed
  statement has denominator $1 - q^{-(2s+3)}$, which is false.
* *Erratum* (proposed by the formalization), `theorem_7_6_A_dyadic` and
  `theorem_7_6_A_dyadic_printed_false`: for $\mathfrak p \mid 2$ the table gives
  $$\sum_{\nu\ge0}A^*(u\pi^\nu)X^\nu = [u \equiv 3 \ (4)] + \frac{\gamma X^2/q^2}{1 - X/q}
    = \frac{[u\equiv 3\ (4)]\,(1 - X/q) + (1 - \chi/q)X^2/q^2}{1 - X/q},$$
  not the printed $\frac{1-\chi q^{-(s+3)}}{1-q^{-(s+1)}}$, which is false for every $u$ and $\chi = \pm1$ (the printed
  series has a nonzero coefficient of $X^1$, while $\nu = 1$ does not occur). The printed proof also starts the sum
  with $1$ for every $u$, but for $u \equiv 1 \pmod 4$ there is no genus with $\nu = 0$.
* `remark_7_7_local`: the local relations behind Remark 7.7: $B^* = A^*$ or $0$ according as $\nu$ is even or odd
  ($\mathfrak p \nmid 2$); $B^* = 0$ ($\mathfrak p \mid 2$, $u \equiv 1$); $B^* = -A^*$ for $\nu = 0$, $A^*$ for $\nu$ even
  $\ge 2$, $0$ for $\nu$ odd ($\mathfrak p \mid 2$, $u \equiv 3$). `remark_7_7` multiplies these over finitely many primes.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Hanke2011Structure

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- $\gamma_{\mathfrak p}(u) = 1 - \chi/q$, for $\chi = \chi_u(\mathfrak p) = \left(\frac{-u}{\mathfrak p}\right)$ and $q$ the size of the residue
field at $\mathfrak p$. -/
def gammaP (χ q : K) : K := 1 - χ / q

/-- **The table value $A^*_{\mathfrak p;2}(u\pi^\nu)$ at a prime $\mathfrak p \nmid 2$** (proof of Theorem 7.6, second table):
$1$ for $\nu = 0$ and $q^{-\nu}\gamma_{\mathfrak p}(u)$ for $\nu \ge 1$. Here `χ` is $\chi_u(\mathfrak p)$ and `q` the size of the
residue field. -/
def aNondyadic (χ q : K) (ν : ℕ) : K := if ν = 0 then 1 else (q ^ ν)⁻¹ * gammaP χ q

/-- **The table value $B^*_{\mathfrak p;2}(u\pi^\nu)$ at a prime $\mathfrak p \nmid 2$**: $1$ for $\nu = 0$, $q^{-\nu}\gamma_{\mathfrak p}(u)$ for
$\nu \ge 2$ even, and $0$ for $\nu$ odd. -/
def bNondyadic (χ q : K) (ν : ℕ) : K :=
  if ν = 0 then 1 else if Even ν then (q ^ ν)⁻¹ * gammaP χ q else 0

/-- **The table value $A^*_{\mathfrak p;2}(u\pi^\nu)$ at $\mathfrak p \mid 2$ with $F_{\mathfrak p} = \mathbb{Q}_2$** ($q = 2$): for
$\nu = 0$ it is $1$ when $u \equiv 3 \pmod 4$ (`u3 = true`) and $0$ when $u \equiv 1 \pmod 4$ (no genus); $0$ for $\nu = 1$
(no genus); $2^{-\nu}\gamma_{\mathfrak p}(u)$ for $\nu \ge 2$. -/
def aDyadic (u3 : Bool) (χ : K) (ν : ℕ) : K :=
  if ν = 0 then (if u3 then 1 else 0) else if ν = 1 then 0 else ((2 : K) ^ ν)⁻¹ * gammaP χ 2

/-- **The table value $B^*_{\mathfrak p;2}(u\pi^\nu)$ at $\mathfrak p \mid 2$ with $F_{\mathfrak p} = \mathbb{Q}_2$** ($q = 2$): $0$
for every $\nu$ when $u \equiv 1 \pmod 4$ (`u3 = false`); when $u \equiv 3 \pmod 4$: $-1$ for $\nu = 0$,
$2^{-\nu}\gamma_{\mathfrak p}(u)$ for $\nu \ge 2$ even, $0$ for $\nu$ odd. -/
def bDyadic (u3 : Bool) (χ : K) (ν : ℕ) : K :=
  if u3 then (if ν = 0 then -1 else if Even ν then ((2 : K) ^ ν)⁻¹ * gammaP χ 2 else 0) else 0

/-- Coefficients of $(1 - cX)\,f$. -/
private theorem coeff_one_sub_mul_X (c : K) (f : PowerSeries K) (n : ℕ) :
    coeff (n + 1) ((1 - C c * X) * f) = coeff (n + 1) f - c * coeff n f := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul]

private theorem coeff_zero_one_sub_mul_X (c : K) (f : PowerSeries K) :
    coeff 0 ((1 - C c * X) * f) = coeff 0 f := by
  simp [sub_mul]

/-- Coefficients of $(1 - cX^2)\,f$. -/
private theorem coeff_one_sub_mul_X2 (c : K) (f : PowerSeries K) (n : ℕ) :
    coeff (n + 2) ((1 - C c * X ^ 2) * f) = coeff (n + 2) f - c * coeff n f := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, pow_two, mul_assoc, coeff_succ_X_mul,
    coeff_succ_X_mul]

private theorem coeff_small_one_sub_mul_X2 (c : K) (f : PowerSeries K) (n : ℕ) (hn : n < 2) :
    coeff n ((1 - C c * X ^ 2) * f) = coeff n f := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  interval_cases n
  · simp
  · rw [pow_two, mul_assoc, coeff_succ_X_mul]; simp

/-- **Theorem 7.6, $A^*$ at $\mathfrak p \nmid 2$.** With $X = q^{-s}$ and $q \ne 0$,
$$\Bigl(1 - \frac{X}{q}\Bigr)\sum_{\nu\ge0}A^*_{\mathfrak p;2}(u\pi^\nu)X^\nu = 1 - \frac{\chi_u(\mathfrak p)}{q^2}X,
\qquad\text{i.e.}\qquad \sum_{\nu\ge0}\frac{A^*_{\mathfrak p;2}(u\pi^\nu)}{q^{\nu s}} = \frac{1-\chi_u(\mathfrak p)q^{-(s+2)}}{1-q^{-(s+1)}}.$$ -/
@[kb "hanke2011structure" "Thm. 7.6, p. 30 (A, p ∤ 2)"]
theorem theorem_7_6_A_nondyadic (χ q : K) (hq : q ≠ 0) :
    (1 - C q⁻¹ * X) * mk (aNondyadic χ q) = 1 - C (χ / q ^ 2) * X := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_one_sub_mul_X, aNondyadic]
  · rw [coeff_one_sub_mul_X, coeff_mk, coeff_mk, map_sub, coeff_C_mul, coeff_one, coeff_X]
    rcases n with _ | n
    · simp [aNondyadic, gammaP]; field_simp; ring
    · simp only [aNondyadic, gammaP, Nat.add_one_ne_zero, if_false]
      simp
      field_simp
      ring

/-- **Theorem 7.6, $B^*$ at $\mathfrak p \nmid 2$.** With $X = q^{-s}$ and $q \ne 0$,
$$\Bigl(1 - \frac{X^2}{q^2}\Bigr)\sum_{\nu\ge0}B^*_{\mathfrak p;2}(u\pi^\nu)X^\nu = 1 - \frac{\chi_u(\mathfrak p)}{q^3}X^2,
\qquad\text{i.e.}\qquad \sum_{\nu\ge0}\frac{B^*_{\mathfrak p;2}(u\pi^\nu)}{q^{\nu s}} = \frac{1-\chi_u(\mathfrak p)q^{-(2s+3)}}{1-q^{-(2s+2)}}.$$ -/
@[kb "hanke2011structure" "Thm. 7.6, p. 30 (B, p ∤ 2)"]
theorem theorem_7_6_B_nondyadic (χ q : K) (hq : q ≠ 0) :
    (1 - C (q ^ 2)⁻¹ * X ^ 2) * mk (bNondyadic χ q) = 1 - C (χ / q ^ 3) * X ^ 2 := by
  ext n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [coeff_small_one_sub_mul_X2 _ _ _ hn, coeff_mk]
    interval_cases n
    · simp [bNondyadic]
    · simp [bNondyadic, coeff_X_pow]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [coeff_one_sub_mul_X2, coeff_mk, coeff_mk, map_sub, coeff_C_mul, coeff_one, coeff_X_pow]
    rcases Nat.even_or_odd m with hm | hm
    · have hm2 : Even (m + 2) := by rcases hm with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩
      rcases m with _ | m
      · simp [bNondyadic, gammaP]; field_simp; ring
      · simp only [bNondyadic, Nat.add_one_ne_zero, if_false, if_pos hm, if_pos hm2]
        have : m + 1 + 2 ≠ 2 := by omega
        simp [this]
        field_simp
        ring
    · have hm2 : ¬ Even (m + 2) := by
        rw [Nat.not_even_iff_odd]; rcases hm with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩
      have hm' : ¬ Even m := Nat.not_even_iff_odd.mpr hm
      have hm0 : m ≠ 0 := by rintro rfl; exact hm' (⟨0, rfl⟩ : Even 0)
      have : m + 2 ≠ 2 := by omega
      simp [bNondyadic, hm', hm2, hm0, this]

/-- **Theorem 7.6, $B^*$ at $\mathfrak p \mid 2$, $u \equiv 1 \pmod 4$.** The series $\sum_\nu B^*_{\mathfrak p;2}(u\pi^\nu)X^\nu$
is $0$, as printed. -/
@[kb "hanke2011structure" "Thm. 7.6, p. 30 (B, p | 2, u ≡ 1 mod 4)"]
theorem theorem_7_6_B_dyadic_one (χ : K) : mk (bDyadic false χ) = 0 := by
  ext n; simp [bDyadic]

/-- **Theorem 7.6, $B^*$ at $\mathfrak p \mid 2$, $u \equiv 3 \pmod 4$ (corrected).** With $q = 2$ and $X = q^{-s}$,
$$\Bigl(1 - \frac{X^2}{q^2}\Bigr)\sum_{\nu\ge0}B^*_{\mathfrak p;2}(u\pi^\nu)X^\nu = -1 + \frac{2X^2}{q^2} - \frac{\chi_u(\mathfrak p)X^2}{q^3},
\quad\text{i.e.}\quad \sum_{\nu\ge0}\frac{B^*_{\mathfrak p;2}(u\pi^\nu)}{q^{\nu s}} = \frac{-1+2q^{-(2s+2)}-\chi_u(\mathfrak p)q^{-(2s+3)}}{1-q^{-(2s+2)}}.$$
*Erratum* (proposed by the formalization): the printed statement has denominator
$1 - q^{-(2s+3)}$; the last display of the proof has the correct denominator $1 - X^2/q^2 = 1 - q^{-(2s+2)}$
(`theorem_7_6_B_dyadic_three_printed_false`). -/
@[kb "hanke2011structure" "Thm. 7.6, p. 30 (B, p | 2, u ≡ 3 mod 4; corrected)"]
theorem theorem_7_6_B_dyadic_three (χ : K) :
    (1 - C ((2 : K) ^ 2)⁻¹ * X ^ 2) * mk (bDyadic true χ) =
      -1 + C (2 / (2 : K) ^ 2 - χ / (2 : K) ^ 3) * X ^ 2 := by
  ext n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [coeff_small_one_sub_mul_X2 _ _ _ hn, coeff_mk]
    interval_cases n
    · simp [bDyadic]
    · simp [bDyadic, coeff_X_pow, sub_mul, coeff_C_mul]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [coeff_one_sub_mul_X2, coeff_mk, coeff_mk, map_add, map_neg, coeff_C_mul, coeff_one,
      coeff_X_pow]
    rcases Nat.even_or_odd m with hm | hm
    · have hm2 : Even (m + 2) := by rcases hm with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩
      rcases m with _ | m
      · simp [bDyadic, gammaP]; ring
      · simp only [bDyadic, if_true, Nat.add_one_ne_zero, if_false, if_pos hm, if_pos hm2]
        have : m + 1 + 2 ≠ 2 := by omega
        simp [this]
        field_simp
        ring
    · have hm2 : ¬ Even (m + 2) := by
        rw [Nat.not_even_iff_odd]; rcases hm with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩
      have hm' : ¬ Even m := Nat.not_even_iff_odd.mpr hm
      have hm0 : m ≠ 0 := by rintro rfl; exact hm' (⟨0, rfl⟩ : Even 0)
      have : m + 2 ≠ 2 := by omega
      simp [bDyadic, hm', hm2, hm0, this]

/-- **The printed dyadic $B^*$ formula of Theorem 7.6 is false** ($u \equiv 3 \pmod 4$, $q = 2$, $\chi = \pm1$): the
identity $(1 - X^2/q^3)\sum_\nu B^*X^\nu = -1 + 2X^2/q^2 - \chi X^2/q^3$ (denominator $1 - q^{-(2s+3)}$) fails; its
coefficients of $X^2$ are $\gamma/4 + 1/8 = 3/8 - \chi/8$ and $1/2 - \chi/8$. -/
@[kb "hanke2011structure" "Thm. 7.6, p. 30 (B, p | 2, u ≡ 3 mod 4; printed, false)"]
theorem theorem_7_6_B_dyadic_three_printed_false (χ : K) :
    (1 - C ((2 : K) ^ 3)⁻¹ * X ^ 2) * mk (bDyadic true χ) ≠
      -1 + C (2 / (2 : K) ^ 2 - χ / (2 : K) ^ 3) * X ^ 2 := by
  intro h
  have h2 := congrArg (coeff 2) h
  rw [coeff_one_sub_mul_X2 _ _ 0, coeff_mk, coeff_mk, map_add, map_neg, coeff_C_mul, coeff_one,
    coeff_X_pow] at h2
  simp [bDyadic, gammaP] at h2
  have h3 : (3 : K) / 8 = 1 / 2 := by linear_combination h2
  norm_num at h3

/-- **Theorem 7.6, $A^*$ at $\mathfrak p \mid 2$ (corrected).** With $q = 2$, $X = q^{-s}$, $\gamma = 1 - \chi_u(\mathfrak p)/q$ and
$[u \equiv 3\ (4)] \in \{0,1\}$,
$$\Bigl(1 - \frac{X}{q}\Bigr)\sum_{\nu\ge0}A^*_{\mathfrak p;2}(u\pi^\nu)X^\nu
  = [u \equiv 3\ (4)]\Bigl(1 - \frac{X}{q}\Bigr) + \frac{\gamma}{q^2}X^2.$$
*Erratum* (proposed by the formalization): the printed value $\frac{1-\chi q^{-(s+3)}}{1-q^{-(s+1)}}$
is false (`theorem_7_6_A_dyadic_printed_false`). -/
@[kb "hanke2011structure" "Thm. 7.6, p. 30 (A, p | 2; corrected)"]
theorem theorem_7_6_A_dyadic (u3 : Bool) (χ : K) :
    (1 - C (2 : K)⁻¹ * X) * mk (aDyadic u3 χ) =
      C (if u3 then (1 : K) else 0) * (1 - C (2 : K)⁻¹ * X) + C (gammaP χ 2 / (2 : K) ^ 2) * X ^ 2 := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_one_sub_mul_X, coeff_mk]; cases u3 <;> simp [aDyadic]
  · rw [coeff_one_sub_mul_X, coeff_mk, coeff_mk, map_add, coeff_C_mul, coeff_C_mul, map_sub,
      coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
    rcases n with _ | n
    · simp [aDyadic]
    · rcases n with _ | n
      · simp [aDyadic]; field_simp
      · simp only [aDyadic, Nat.add_one_ne_zero, if_false, show n + 1 + 1 ≠ 1 by omega,
          show n + 1 + 1 + 1 ≠ 1 by omega, show n + 1 + 1 + 1 ≠ 2 by omega]
        simp
        field_simp
        ring

/-- **The printed dyadic $A^*$ formula of Theorem 7.6 is false**, for both unit classes $u$ and $\chi = \pm1$:
$(1 - X/q)\sum_\nu A^*X^\nu \ne 1 - \chi X/q^3$ ($q = 2$). The coefficients of $X^1$ are $-[u\equiv3\ (4)]/2$ and $-\chi/8$. -/
@[kb "hanke2011structure" "Thm. 7.6, p. 30 (A, p | 2; printed, false)"]
theorem theorem_7_6_A_dyadic_printed_false (u3 : Bool) (χ : K) (hχ : χ = 1 ∨ χ = -1) :
    (1 - C (2 : K)⁻¹ * X) * mk (aDyadic u3 χ) ≠ 1 - C (χ / (2 : K) ^ 3) * X := by
  intro h
  have h1 := congrArg (coeff 1) h
  rw [coeff_one_sub_mul_X, coeff_mk, coeff_mk, map_sub, coeff_C_mul, coeff_one, coeff_X] at h1
  cases u3 <;> rcases hχ with rfl | rfl <;> simp [aDyadic] at h1 <;> norm_num at h1

/-- **The local relations behind Remark 7.7** (from the table in the proof of Theorem 7.6):
* $\mathfrak p \nmid 2$: $B^*(u\pi^\nu) = A^*(u\pi^\nu)$ for $\nu$ even and $0$ for $\nu$ odd;
* $\mathfrak p \mid 2$, $u \equiv 1 \pmod 4$: $B^* = 0$;
* $\mathfrak p \mid 2$, $u \equiv 3 \pmod 4$: $B^* = -A^*$ for $\nu = 0$, $B^* = A^*$ for $\nu \ge 2$ even, $B^* = 0$ for $\nu$ odd. -/
@[kb "hanke2011structure" "Rem. 7.7, p. 32 (local form)"]
theorem remark_7_7_local (χ q : K) (ν : ℕ) :
    bNondyadic χ q ν = (if Even ν then aNondyadic χ q ν else 0) ∧
    bDyadic false χ ν = 0 ∧
    bDyadic true χ ν = (if ν = 0 then -aDyadic true χ ν else if Even ν then aDyadic true χ ν else 0) := by
  refine ⟨?_, by simp [bDyadic], ?_⟩
  · rcases Nat.even_or_odd ν with h | h
    · simp [bNondyadic, aNondyadic, h]
    · have h' : ¬ Even ν := Nat.not_even_iff_odd.mpr h
      have h0 : ν ≠ 0 := by rintro rfl; exact h' (⟨0, rfl⟩ : Even 0)
      simp [bNondyadic, h', h0]
  · by_cases h0 : ν = 0
    · simp [bDyadic, aDyadic, h0]
    · rcases Nat.even_or_odd ν with h | h
      · have h1 : ν ≠ 1 := by rintro rfl; exact (Nat.not_even_one) h
        simp [bDyadic, aDyadic, h0, h, h1]
      · have h' : ¬ Even ν := Nat.not_even_iff_odd.mpr h
        simp [bDyadic, h0, h']

/-- **The local data at one prime for Remark 7.7**: whether $\mathfrak p \mid 2$ (`dyadic`), whether $u \equiv 3 \pmod 4$
there (`u3`, used only at dyadic primes), $\nu = \operatorname{ord}_{\mathfrak p}(S)$ (`nu`), $\chi = \chi_u(\mathfrak p)$ (`chi`), and the
residue field size $q$ (`q`; $q = 2$ at the dyadic primes, which split completely). -/
structure LocalDatum (K : Type*) where
  dyadic : Bool
  u3 : Bool
  nu : ℕ
  chi : K
  q : K

/-- $A^*_{\mathfrak p;2}$ at one prime, from the table. -/
def LocalDatum.a (d : LocalDatum K) : K := if d.dyadic then aDyadic d.u3 d.chi d.nu else aNondyadic d.chi d.q d.nu

/-- $B^*_{\mathfrak p;2}$ at one prime, from the table. -/
def LocalDatum.b (d : LocalDatum K) : K := if d.dyadic then bDyadic d.u3 d.chi d.nu else bNondyadic d.chi d.q d.nu

/-- **Remark 7.7** (Hanke). Over a finite set $T$ of primes (all primes where $S$ is not a unit square class, together
with the dyadic primes; elsewhere $A^* = B^* = 1$), put $A^*(S) = \prod_{\mathfrak p \in T}A^*_{\mathfrak p;2}(S_{\mathfrak p})$ and
$B^*(S) = \prod_{\mathfrak p\in T}B^*_{\mathfrak p;2}(S_{\mathfrak p})$. If every $\nu_{\mathfrak p} = \operatorname{ord}_{\mathfrak p}(S)$ is even ($I(S)$ is a
square) and $u \equiv 3 \pmod 4$ at every dyadic prime ($S \equiv 3 \pmod{4\mathcal O_F}$), then $A^*(S) = (-1)^\tau B^*(S)$, where
$\tau$ is the number of dyadic primes with $\mathfrak p \nmid I(S)$; otherwise $B^*(S) = 0$. -/
@[kb "hanke2011structure" "Rem. 7.7, p. 32"]
theorem remark_7_7 {ι : Type*} (T : Finset ι) (d : ι → LocalDatum K) :
    (∀ p ∈ T, Even (d p).nu ∧ ((d p).dyadic → (d p).u3)) →
      ∏ p ∈ T, (d p).a = (-1) ^ (T.filter fun p => (d p).dyadic ∧ (d p).nu = 0).card *
        ∏ p ∈ T, (d p).b := by
  intro h
  classical
  rw [Finset.card_filter, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  obtain ⟨he, hu⟩ := h p hp
  obtain ⟨-, h2, h3⟩ := remark_7_7_local (d p).chi (d p).q (d p).nu
  have h1 := (remark_7_7_local (d p).chi (d p).q (d p).nu).1
  unfold LocalDatum.a LocalDatum.b
  cases hd : (d p).dyadic
  · simp [h1, he]
  · have hu3 : (d p).u3 = true := hu hd
    rw [hu3, h3]
    by_cases h0 : (d p).nu = 0
    · simp [h0]
    · simp [h0, he]

/-- **Remark 7.7, vanishing case.** If some $\nu_{\mathfrak p}$ is odd, or $u \equiv 1 \pmod 4$ at some dyadic prime, then
$B^*(S) = \prod_{\mathfrak p \in T}B^*_{\mathfrak p;2}(S_{\mathfrak p}) = 0$. -/
@[kb "hanke2011structure" "Rem. 7.7, p. 32 (vanishing)"]
theorem remark_7_7_vanish {ι : Type*} (T : Finset ι) (d : ι → LocalDatum K)
    (h : ∃ p ∈ T, ¬ Even (d p).nu ∨ ((d p).dyadic ∧ ¬ (d p).u3)) :
    ∏ p ∈ T, (d p).b = 0 := by
  obtain ⟨p, hp, hbad⟩ := h
  refine Finset.prod_eq_zero hp ?_
  obtain ⟨h1, h2, h3⟩ := remark_7_7_local (d p).chi (d p).q (d p).nu
  unfold LocalDatum.b
  rcases hbad with hodd | ⟨hd, hu⟩
  · have h0 : (d p).nu ≠ 0 := by rintro h; exact hodd (h ▸ (⟨0, rfl⟩ : Even 0))
    cases hd : (d p).dyadic
    · simp [h1, hodd]
    · cases hu : (d p).u3
      · simp [h2]
      · simp [h3, h0, hodd]
  · simp only [hd, if_true]
    simp only [Bool.not_eq_true] at hu
    rw [hu, h2]

end QuadFormsKB.Hanke2011Structure
