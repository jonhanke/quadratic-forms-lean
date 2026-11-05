/-
# Conway–Sloane 1988, §8, Table 6: the rows $d = 9, 18, 21, 22, 23, 25$ for $s \ge 2$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, Table 6, pp. 270–271.

Table 6 lists the rational numbers $\zeta_D(s)\,d^{s-1}\sqrt d/\pi^s$, $D = (-1)^s d$. This file proves the entries
$2 \le s \le 12$ of the rows $d = 9, 18, 21, 22, 23, 25$
from `zetaD_eq_abs` (the closed formula (13) with the Gauss sum eliminated by the positivity of $\zeta_D$,
`Table6Abs.lean`). The entries $s = 1$ need class numbers and are not treated here.

**Characters (book $\to$ Lean).** For each $D$ the primitive character $\psi$ of (13) is the Kronecker character
$\left(\frac{\Delta}{\cdot}\right)$ (`Binary.kroneckerChar Δ`) of the fundamental discriminant $\Delta$ of
$\mathbb Q(\sqrt D)$, a character modulo $k_1 = \lvert\Delta\rvert$ (Table 4):

| $d$ | $D$ (even $s$) | $\Delta$ | $k_1$ | $\psi$ | $D$ (odd $s$) | $\Delta$ | $k_1$ | $\psi$ |
|---|---|---|---|---|---|---|---|---|
| $9$ | $9$ | $1$ | $1$ | trivial | $-9$ | $-4$ | $4$ | `psiNeg4` |
| $18$ | $18$ | $8$ | $8$ | `psi8` | $-18$ | $-8$ | $8$ | `psiNeg8` |
| $21$ | $21$ | $21$ | $21$ | `psi21` | $-21$ | $-84$ | $84$ | `psiNeg84` |
| $22$ | $22$ | $88$ | $88$ | `psi88` | $-22$ | $-88$ | $88$ | `psiNeg88` |
| $23$ | $23$ | $92$ | $92$ | `psi92` | $-23$ | $-23$ | $23$ | `psiNeg23` |
| $25$ | $25$ | $1$ | $1$ | trivial | $-25$ | $-4$ | $4$ | `psiNeg4` |

For $D \in \{9, -9, 18, -18, 25, -25\}$ (not of the form $\Delta$ or $\Delta/4$) $D = f^2D_0$ and $\psi$ is the
character of $D_0$; the Euler factor of (13) then also contains the primes dividing $f$. For a square $D$, $\psi$ is
the trivial character modulo $1$ (`(1 : DirichletCharacter ℂ 1)`).

**Proves**, for each $D$ above (names with $D$ written `neg7` for $-7$ etc.):
* for each new character: `isPrimitive_psiΔ` (primitivity, one witness per prime factor of $k_1$), `psiΔ_neg_one`
  ($\psi(-1)$);
* `chiD_eq_changeLevel_D`: $\chi_D = \chi_1\psi$ on $\mathbb Z/4\lvert D\rvert$ (checked over one period);
* `psiΔ_sum`: $\sum_{r=1}^{k_1}\psi(r)f(r)$ written out; `psiΔ_euler_D`: the Euler factor
  $E = \prod_{p \mid 4D}(1 - \psi(p)p^{-s})$ as a rational function of $s$;
* `table6_row_D`: $\zeta_D(s)\,d^{s-1}\sqrt d/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,d^{s-1}c/(2\,s!)$ for all $s \ge 2$ of the
  right parity, $S = \sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)$, $c = \sqrt{d/k_1}$;
* `table6_d_s` ($2 \le s \le 12$): the printed entries.

**Check against the scan.** Every entry is stated with the printed value; all of them were also recomputed independently
(exact rational arithmetic, Python) before the formal proof.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6Abs

namespace QuadFormsKB.ConwaySloane.Mass

open Complex ZMod Finset QuadFormsKB.Binary
open scoped Real

/-! ### Row $d = 9$ -/

theorem one1_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 1, (1 : DirichletCharacter ℂ 1) (r : ZMod 1) * ((f r : ℚ) : ℂ) =
      ((f 1 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, one_level_one_apply]
  norm_num [chiD]

theorem chiD_eq_changeLevel_9 :
    ∀ m : ℕ, (chiD 9 m : ℂ) = DirichletCharacter.changeLevel (show 1 ∣ 4 * (9 : ℤ).natAbs by decide)
      (1 : DirichletCharacter ℂ 1) (m : ZMod (4 * (9 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (9 : ℤ).natAbs) < 36 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (9 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [one_level_one_apply] <;> norm_num [chiD]

theorem one1_euler_9 (s : ℕ) :
    ∏ p ∈ (4 * (9 : ℤ).natAbs).primeFactors, (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 2 ^ s) * (1 - 1 / 3 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (9 : ℤ).natAbs).primeFactors = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [one_level_one_apply, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 9$, even $s$** ($D = 9$, $\psi = \left(\frac{1}{\cdot}\right)$ modulo
$k_1 = 1$): $\zeta_{9}(s)\,9^{s-1}\sqrt{9}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,9^{s-1}(3/1)/(2\,s!)$ with
$E = (1 - 2^{-s})(1 - 3^{-s})$ and $S = \sum_{r=1}^{1}\psi(r)B_s(r/1)$ (`zetaD_eq_abs`). -/
theorem table6_row_9 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 9 s * (9 : ℝ) ^ (s - 1) * Real.sqrt 9 / π ^ s =
      ((|(1 - 1 / 2 ^ s) * (1 - 1 / 3 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 1)| *
        9 ^ (s - 1) * (3 / 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 9) (by norm_num) DirichletCharacter.isPrimitive_one_level_one
    inv_one _ chiD_eq_changeLevel_9 hs
    (by rw [one_level_one_apply, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (one1_euler_9 s) (one1_sum _) 9 _
    (sqrt_eq_rat_mul_sqrt (a := 3) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 9$, $s = 2$** ($D = 9$): $\zeta_{9}(2)\,9^{1}\sqrt{9}/\pi^{2} = 3$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 2)"]
theorem table6_9_2 : zetaD 9 2 * 9 ^ 1 * Real.sqrt 9 / π ^ 2 = 3 := by
  rw [show zetaD 9 2 * 9 ^ 1 * Real.sqrt 9 / π ^ 2 =
      zetaD 9 ((2 : ℕ) : ℝ) * 9 ^ (2 - 1) * Real.sqrt 9 / π ^ 2 by norm_num,
    table6_row_9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 4$** ($D = 9$): $\zeta_{9}(4)\,9^{3}\sqrt{9}/\pi^{4} = 45/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 4)"]
theorem table6_9_4 : zetaD 9 4 * 9 ^ 3 * Real.sqrt 9 / π ^ 4 = 45 / 2 := by
  rw [show zetaD 9 4 * 9 ^ 3 * Real.sqrt 9 / π ^ 4 =
      zetaD 9 ((4 : ℕ) : ℝ) * 9 ^ (4 - 1) * Real.sqrt 9 / π ^ 4 by norm_num,
    table6_row_9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 6$** ($D = 9$): $\zeta_{9}(6)\,9^{5}\sqrt{9}/\pi^{6} = 7371/40$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 6)"]
theorem table6_9_6 : zetaD 9 6 * 9 ^ 5 * Real.sqrt 9 / π ^ 6 = 7371 / 40 := by
  rw [show zetaD 9 6 * 9 ^ 5 * Real.sqrt 9 / π ^ 6 =
      zetaD 9 ((6 : ℕ) : ℝ) * 9 ^ (6 - 1) * Real.sqrt 9 / π ^ 6 by norm_num,
    table6_row_9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 8$** ($D = 9$): $\zeta_{9}(8)\,9^{7}\sqrt{9}/\pi^{8} = 169371/112$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 8)"]
theorem table6_9_8 : zetaD 9 8 * 9 ^ 7 * Real.sqrt 9 / π ^ 8 = 169371 / 112 := by
  rw [show zetaD 9 8 * 9 ^ 7 * Real.sqrt 9 / π ^ 8 =
      zetaD 9 ((8 : ℕ) : ℝ) * 9 ^ (8 - 1) * Real.sqrt 9 / π ^ 8 by norm_num,
    table6_row_9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 10$** ($D = 9$): $\zeta_{9}(10)\,9^{9}\sqrt{9}/\pi^{10} = 55601073/4480$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 9, s = 10)"]
theorem table6_9_10 : zetaD 9 10 * 9 ^ 9 * Real.sqrt 9 / π ^ 10 = 55601073 / 4480 := by
  rw [show zetaD 9 10 * 9 ^ 9 * Real.sqrt 9 / π ^ 10 =
      zetaD 9 ((10 : ℕ) : ℝ) * 9 ^ (10 - 1) * Real.sqrt 9 / π ^ 10 by norm_num,
    table6_row_9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 12$** ($D = 9$): $\zeta_{9}(12)\,9^{11}\sqrt{9}/\pi^{12} = 1434144933/14080$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 9, s = 12)"]
theorem table6_9_12 : zetaD 9 12 * 9 ^ 11 * Real.sqrt 9 / π ^ 12 = 1434144933 / 14080 := by
  rw [show zetaD 9 12 * 9 ^ 11 * Real.sqrt 9 / π ^ 12 =
      zetaD 9 ((12 : ℕ) : ℝ) * 9 ^ (12 - 1) * Real.sqrt 9 / π ^ 12 by norm_num,
    table6_row_9 (by norm_num) (by norm_num)]
  bernoulli_eval

theorem psiNeg4_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 4, psiNeg4 (r : ZMod 4) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg4_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg9 :
    ∀ m : ℕ, (chiD (-9) m : ℂ) = DirichletCharacter.changeLevel (show 4 ∣ 4 * (-9 : ℤ).natAbs by decide)
      psiNeg4 (m : ZMod (4 * (-9 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-9 : ℤ).natAbs) < 36 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-9 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg4_natCast] <;> norm_num [chiD]

theorem psiNeg4_euler_neg9 (s : ℕ) :
    ∏ p ∈ (4 * (-9 : ℤ).natAbs).primeFactors, (1 - psiNeg4 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 + 1 / 3 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-9 : ℤ).natAbs).primeFactors = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg4_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 9$, odd $s$** ($D = -9$, $\psi = \left(\frac{-4}{\cdot}\right)$ modulo
$k_1 = 4$): $\zeta_{-9}(s)\,9^{s-1}\sqrt{9}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,9^{s-1}(3/2)/(2\,s!)$ with
$E = (1 + 3^{-s})$ and $S = \sum_{r=1}^{4}\psi(r)B_s(r/4)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg9 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-9) s * (9 : ℝ) ^ (s - 1) * Real.sqrt 9 / π ^ s =
      ((|(1 + 1 / 3 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 4) - (Polynomial.bernoulli s).eval (3 / 4)| *
        9 ^ (s - 1) * (3 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -9) (by norm_num) isPrimitive_psiNeg4
    psiNeg4_inv _ chiD_eq_changeLevel_neg9 hs
    (by rw [psiNeg4_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg4_euler_neg9 s) (psiNeg4_sum _) 9 _
    (sqrt_eq_rat_mul_sqrt (a := 3) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 9$, $s = 3$** ($D = -9$): $\zeta_{-9}(3)\,9^{2}\sqrt{9}/\pi^{3} = 63/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 3)"]
theorem table6_9_3 : zetaD (-9) 3 * 9 ^ 2 * Real.sqrt 9 / π ^ 3 = 63 / 8 := by
  rw [show zetaD (-9) 3 * 9 ^ 2 * Real.sqrt 9 / π ^ 3 =
      zetaD (-9) ((3 : ℕ) : ℝ) * 9 ^ (3 - 1) * Real.sqrt 9 / π ^ 3 by norm_num,
    table6_row_neg9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 5$** ($D = -9$): $\zeta_{-9}(5)\,9^{4}\sqrt{9}/\pi^{5} = 8235/128$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 5)"]
theorem table6_9_5 : zetaD (-9) 5 * 9 ^ 4 * Real.sqrt 9 / π ^ 5 = 8235 / 128 := by
  rw [show zetaD (-9) 5 * 9 ^ 4 * Real.sqrt 9 / π ^ 5 =
      zetaD (-9) ((5 : ℕ) : ℝ) * 9 ^ (5 - 1) * Real.sqrt 9 / π ^ 5 by norm_num,
    table6_row_neg9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 7$** ($D = -9$): $\zeta_{-9}(7)\,9^{6}\sqrt{9}/\pi^{7} = 2702727/5120$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 7)"]
theorem table6_9_7 : zetaD (-9) 7 * 9 ^ 6 * Real.sqrt 9 / π ^ 7 = 2702727 / 5120 := by
  rw [show zetaD (-9) 7 * 9 ^ 6 * Real.sqrt 9 / π ^ 7 =
      zetaD (-9) ((7 : ℕ) : ℝ) * 9 ^ (7 - 1) * Real.sqrt 9 / π ^ 7 by norm_num,
    table6_row_neg9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 9$** ($D = -9$): $\zeta_{-9}(9)\,9^{8}\sqrt{9}/\pi^{9} = 141958899/32768$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 9, s = 9)"]
theorem table6_9_9 : zetaD (-9) 9 * 9 ^ 8 * Real.sqrt 9 / π ^ 9 = 141958899 / 32768 := by
  rw [show zetaD (-9) 9 * 9 ^ 8 * Real.sqrt 9 / π ^ 9 =
      zetaD (-9) ((9 : ℕ) : ℝ) * 9 ^ (9 - 1) * Real.sqrt 9 / π ^ 9 by norm_num,
    table6_row_neg9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 9$, $s = 11$** ($D = -9$): $\zeta_{-9}(11)\,9^{10}\sqrt{9}/\pi^{11} = 1631081751183/45875200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 9, s = 11)"]
theorem table6_9_11 : zetaD (-9) 11 * 9 ^ 10 * Real.sqrt 9 / π ^ 11 = 1631081751183 / 45875200 := by
  rw [show zetaD (-9) 11 * 9 ^ 10 * Real.sqrt 9 / π ^ 11 =
      zetaD (-9) ((11 : ℕ) : ℝ) * 9 ^ (11 - 1) * Real.sqrt 9 / π ^ 11 by norm_num,
    table6_row_neg9 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 18$ -/

theorem psi8_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 8, psi8 (r : ZMod 8) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 - f 5 + f 7 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi8_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_18 :
    ∀ m : ℕ, (chiD 18 m : ℂ) = DirichletCharacter.changeLevel (show 8 ∣ 4 * (18 : ℤ).natAbs by decide)
      psi8 (m : ZMod (4 * (18 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (18 : ℤ).natAbs) < 72 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (18 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi8_natCast] <;> norm_num [chiD]

theorem psi8_euler_18 (s : ℕ) :
    ∏ p ∈ (4 * (18 : ℤ).natAbs).primeFactors, (1 - psi8 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 + 1 / 3 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (18 : ℤ).natAbs).primeFactors = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi8_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 18$, even $s$** ($D = 18$, $\psi = \left(\frac{8}{\cdot}\right)$ modulo
$k_1 = 8$): $\zeta_{18}(s)\,18^{s-1}\sqrt{18}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,18^{s-1}(3/2)/(2\,s!)$ with
$E = (1 + 3^{-s})$ and $S = \sum_{r=1}^{8}\psi(r)B_s(r/8)$ (`zetaD_eq_abs`). -/
theorem table6_row_18 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 18 s * (18 : ℝ) ^ (s - 1) * Real.sqrt 18 / π ^ s =
      ((|(1 + 1 / 3 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 8) - (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) + (Polynomial.bernoulli s).eval (7 / 8)| *
        18 ^ (s - 1) * (3 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 18) (by norm_num) isPrimitive_psi8
    psi8_inv _ chiD_eq_changeLevel_18 hs
    (by rw [psi8_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi8_euler_18 s) (psi8_sum _) 18 _
    (sqrt_eq_rat_mul_sqrt (a := 3) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 18$, $s = 2$** ($D = 18$): $\zeta_{18}(2)\,18^{1}\sqrt{18}/\pi^{2} = 15/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 2)"]
theorem table6_18_2 : zetaD 18 2 * 18 ^ 1 * Real.sqrt 18 / π ^ 2 = 15 / 2 := by
  rw [show zetaD 18 2 * 18 ^ 1 * Real.sqrt 18 / π ^ 2 =
      zetaD 18 ((2 : ℕ) : ℝ) * 18 ^ (2 - 1) * Real.sqrt 18 / π ^ 2 by norm_num,
    table6_row_18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 4$** ($D = 18$): $\zeta_{18}(4)\,18^{3}\sqrt{18}/\pi^{4} = 4059/16$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 4)"]
theorem table6_18_4 : zetaD 18 4 * 18 ^ 3 * Real.sqrt 18 / π ^ 4 = 4059 / 16 := by
  rw [show zetaD 18 4 * 18 ^ 3 * Real.sqrt 18 / π ^ 4 =
      zetaD 18 ((4 : ℕ) : ℝ) * 18 ^ (4 - 1) * Real.sqrt 18 / π ^ 4 by norm_num,
    table6_row_18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 6$** ($D = 18$): $\zeta_{18}(6)\,18^{5}\sqrt{18}/\pi^{6} = 2134593/256$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 6)"]
theorem table6_18_6 : zetaD 18 6 * 18 ^ 5 * Real.sqrt 18 / π ^ 6 = 2134593 / 256 := by
  rw [show zetaD 18 6 * 18 ^ 5 * Real.sqrt 18 / π ^ 6 =
      zetaD 18 ((6 : ℕ) : ℝ) * 18 ^ (6 - 1) * Real.sqrt 18 / π ^ 6 by norm_num,
    table6_row_18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 8$** ($D = 18$): $\zeta_{18}(8)\,18^{7}\sqrt{18}/\pi^{8} = 19621931913/71680$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 8)"]
theorem table6_18_8 : zetaD 18 8 * 18 ^ 7 * Real.sqrt 18 / π ^ 8 = 19621931913 / 71680 := by
  rw [show zetaD 18 8 * 18 ^ 7 * Real.sqrt 18 / π ^ 8 =
      zetaD 18 ((8 : ℕ) : ℝ) * 18 ^ (8 - 1) * Real.sqrt 18 / π ^ 8 by norm_num,
    table6_row_18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 10$** ($D = 18$): $\zeta_{18}(10)\,18^{9}\sqrt{18}/\pi^{10} = 4122569626515/458752$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 18, s = 10)"]
theorem table6_18_10 : zetaD 18 10 * 18 ^ 9 * Real.sqrt 18 / π ^ 10 = 4122569626515 / 458752 := by
  rw [show zetaD 18 10 * 18 ^ 9 * Real.sqrt 18 / π ^ 10 =
      zetaD 18 ((10 : ℕ) : ℝ) * 18 ^ (10 - 1) * Real.sqrt 18 / π ^ 10 by norm_num,
    table6_row_18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 12$** ($D = 18$): $\zeta_{18}(12)\,18^{11}\sqrt{18}/\pi^{12} = 297739178712207297/1009254400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 18, s = 12)"]
theorem table6_18_12 : zetaD 18 12 * 18 ^ 11 * Real.sqrt 18 / π ^ 12 = 297739178712207297 / 1009254400 := by
  rw [show zetaD 18 12 * 18 ^ 11 * Real.sqrt 18 / π ^ 12 =
      zetaD 18 ((12 : ℕ) : ℝ) * 18 ^ (12 - 1) * Real.sqrt 18 / π ^ 12 by norm_num,
    table6_row_18 (by norm_num) (by norm_num)]
  bernoulli_eval

theorem psiNeg8_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 8, psiNeg8 (r : ZMod 8) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 - f 5 - f 7 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg8_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg18 :
    ∀ m : ℕ, (chiD (-18) m : ℂ) = DirichletCharacter.changeLevel (show 8 ∣ 4 * (-18 : ℤ).natAbs by decide)
      psiNeg8 (m : ZMod (4 * (-18 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-18 : ℤ).natAbs) < 72 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-18 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg8_natCast] <;> norm_num [chiD]

theorem psiNeg8_euler_neg18 (s : ℕ) :
    ∏ p ∈ (4 * (-18 : ℤ).natAbs).primeFactors, (1 - psiNeg8 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 3 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-18 : ℤ).natAbs).primeFactors = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg8_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 18$, odd $s$** ($D = -18$, $\psi = \left(\frac{-8}{\cdot}\right)$ modulo
$k_1 = 8$): $\zeta_{-18}(s)\,18^{s-1}\sqrt{18}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,18^{s-1}(3/2)/(2\,s!)$ with
$E = (1 - 3^{-s})$ and $S = \sum_{r=1}^{8}\psi(r)B_s(r/8)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg18 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-18) s * (18 : ℝ) ^ (s - 1) * Real.sqrt 18 / π ^ s =
      ((|(1 - 1 / 3 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 8) + (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) - (Polynomial.bernoulli s).eval (7 / 8)| *
        18 ^ (s - 1) * (3 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -18) (by norm_num) isPrimitive_psiNeg8
    psiNeg8_inv _ chiD_eq_changeLevel_neg18 hs
    (by rw [psiNeg8_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg8_euler_neg18 s) (psiNeg8_sum _) 18 _
    (sqrt_eq_rat_mul_sqrt (a := 3) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 18$, $s = 3$** ($D = -18$): $\zeta_{-18}(3)\,18^{2}\sqrt{18}/\pi^{3} = 351/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 3)"]
theorem table6_18_3 : zetaD (-18) 3 * 18 ^ 2 * Real.sqrt 18 / π ^ 3 = 351 / 8 := by
  rw [show zetaD (-18) 3 * 18 ^ 2 * Real.sqrt 18 / π ^ 3 =
      zetaD (-18) ((3 : ℕ) : ℝ) * 18 ^ (3 - 1) * Real.sqrt 18 / π ^ 3 by norm_num,
    table6_row_neg18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 5$** ($D = -18$): $\zeta_{-18}(5)\,18^{4}\sqrt{18}/\pi^{5} = 186219/128$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 5)"]
theorem table6_18_5 : zetaD (-18) 5 * 18 ^ 4 * Real.sqrt 18 / π ^ 5 = 186219 / 128 := by
  rw [show zetaD (-18) 5 * 18 ^ 4 * Real.sqrt 18 / π ^ 5 =
      zetaD (-18) ((5 : ℕ) : ℝ) * 18 ^ (5 - 1) * Real.sqrt 18 / π ^ 5 by norm_num,
    table6_row_neg18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 7$** ($D = -18$): $\zeta_{-18}(7)\,18^{6}\sqrt{18}/\pi^{7} = 244616679/5120$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 7)"]
theorem table6_18_7 : zetaD (-18) 7 * 18 ^ 6 * Real.sqrt 18 / π ^ 7 = 244616679 / 5120 := by
  rw [show zetaD (-18) 7 * 18 ^ 6 * Real.sqrt 18 / π ^ 7 =
      zetaD (-18) ((7 : ℕ) : ℝ) * 18 ^ (7 - 1) * Real.sqrt 18 / π ^ 7 by norm_num,
    table6_row_neg18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 9$** ($D = -18$): $\zeta_{-18}(9)\,18^{8}\sqrt{18}/\pi^{9} = 1798809553593/1146880$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 18, s = 9)"]
theorem table6_18_9 : zetaD (-18) 9 * 18 ^ 8 * Real.sqrt 18 / π ^ 9 = 1798809553593 / 1146880 := by
  rw [show zetaD (-18) 9 * 18 ^ 8 * Real.sqrt 18 / π ^ 9 =
      zetaD (-18) ((9 : ℕ) : ℝ) * 18 ^ (9 - 1) * Real.sqrt 18 / π ^ 9 by norm_num,
    table6_row_neg18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 18$, $s = 11$** ($D = -18$): $\zeta_{-18}(11)\,18^{10}\sqrt{18}/\pi^{11} = 2362058587538991/45875200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 18, s = 11)"]
theorem table6_18_11 : zetaD (-18) 11 * 18 ^ 10 * Real.sqrt 18 / π ^ 11 = 2362058587538991 / 45875200 := by
  rw [show zetaD (-18) 11 * 18 ^ 10 * Real.sqrt 18 / π ^ 11 =
      zetaD (-18) ((11 : ℕ) : ℝ) * 18 ^ (11 - 1) * Real.sqrt 18 / π ^ 11 by norm_num,
    table6_row_neg18 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 21$ -/

/-! #### The character $\left(\frac{21}{\cdot}\right)$ modulo $21$ -/

instance isQuadDisc_21 : IsQuadDisc 21 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = 21$: the Kronecker character $\left(\frac{21}{\cdot}\right)$ modulo $21$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 21)"]
noncomputable def psi21 : DirichletCharacter ℂ 21 := kroneckerChar 21

theorem psi21_natCast (n : ℕ) : psi21 n = (jacobiSym n 21 : ℂ) :=
  kroneckerChar_natCast_of_one 21 (by norm_num) n

theorem psi21_inv : psi21⁻¹ = psi21 := kroneckerChar_inv 21

theorem psi21_neg_one : psi21 (-1) = 1 := by
  rw [show (-1 : ZMod 21) = ((20 : ℕ) : ZMod 21) by decide, psi21_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 21, conductor 21)"]
theorem isPrimitive_psi21 : psi21.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 21 = {3, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨8, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((8 : ℤ) : ZMod 21) = ((8 : ℕ) : ZMod 21) by norm_cast, psi21_natCast]; norm_num [chiD]⟩
  · exact ⟨10, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((10 : ℤ) : ZMod 21) = ((10 : ℕ) : ZMod 21) by norm_cast, psi21_natCast]; norm_num [chiD]⟩

theorem psi21_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 21, psi21 (r : ZMod 21) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 2 + f 4 + f 5 - f 8 - f 10 - f 11 - f 13 + f 16 + f 17 - f 19 + f 20 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi21_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_21 :
    ∀ m : ℕ, (chiD 21 m : ℂ) = DirichletCharacter.changeLevel (show 21 ∣ 4 * (21 : ℤ).natAbs by decide)
      psi21 (m : ZMod (4 * (21 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (21 : ℤ).natAbs) < 84 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (21 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi21_natCast] <;> norm_num [chiD]

theorem psi21_euler_21 (s : ℕ) :
    ∏ p ∈ (4 * (21 : ℤ).natAbs).primeFactors, (1 - psi21 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 + 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (21 : ℤ).natAbs).primeFactors = {2, 3, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi21_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 21$, even $s$** ($D = 21$, $\psi = \left(\frac{21}{\cdot}\right)$ modulo
$k_1 = 21$): $\zeta_{21}(s)\,21^{s-1}\sqrt{21}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,21^{s-1}/(2\,s!)$ with
$E = (1 + 2^{-s})$ and $S = \sum_{r=1}^{21}\psi(r)B_s(r/21)$ (`zetaD_eq_abs`). -/
theorem table6_row_21 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 21 s * (21 : ℝ) ^ (s - 1) * Real.sqrt 21 / π ^ s =
      ((|(1 + 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 21) - (Polynomial.bernoulli s).eval (2 / 21)
        + (Polynomial.bernoulli s).eval (4 / 21) + (Polynomial.bernoulli s).eval (5 / 21)
        - (Polynomial.bernoulli s).eval (8 / 21) - (Polynomial.bernoulli s).eval (10 / 21)
        - (Polynomial.bernoulli s).eval (11 / 21) - (Polynomial.bernoulli s).eval (13 / 21)
        + (Polynomial.bernoulli s).eval (16 / 21) + (Polynomial.bernoulli s).eval (17 / 21)
        - (Polynomial.bernoulli s).eval (19 / 21) + (Polynomial.bernoulli s).eval (20 / 21)| *
        21 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 21) (by norm_num) isPrimitive_psi21
    psi21_inv _ chiD_eq_changeLevel_21 hs
    (by rw [psi21_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi21_euler_21 s) (psi21_sum _) 21 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 21$, $s = 2$** ($D = 21$): $\zeta_{21}(2)\,21^{1}\sqrt{21}/\pi^{2} = 10$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 2)"]
theorem table6_21_2 : zetaD 21 2 * 21 ^ 1 * Real.sqrt 21 / π ^ 2 = 10 := by
  rw [show zetaD 21 2 * 21 ^ 1 * Real.sqrt 21 / π ^ 2 =
      zetaD 21 ((2 : ℕ) : ℝ) * 21 ^ (2 - 1) * Real.sqrt 21 / π ^ 2 by norm_num,
    table6_row_21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 4$** ($D = 21$): $\zeta_{21}(4)\,21^{3}\sqrt{21}/\pi^{4} = 1309/3$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 4)"]
theorem table6_21_4 : zetaD 21 4 * 21 ^ 3 * Real.sqrt 21 / π ^ 4 = 1309 / 3 := by
  rw [show zetaD 21 4 * 21 ^ 3 * Real.sqrt 21 / π ^ 4 =
      zetaD 21 ((4 : ℕ) : ℝ) * 21 ^ (4 - 1) * Real.sqrt 21 / π ^ 4 by norm_num,
    table6_row_21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 6$** ($D = 21$): $\zeta_{21}(6)\,21^{5}\sqrt{21}/\pi^{6} = 233623/12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 6)"]
theorem table6_21_6 : zetaD 21 6 * 21 ^ 5 * Real.sqrt 21 / π ^ 6 = 233623 / 12 := by
  rw [show zetaD 21 6 * 21 ^ 5 * Real.sqrt 21 / π ^ 6 =
      zetaD 21 ((6 : ℕ) : ℝ) * 21 ^ (6 - 1) * Real.sqrt 21 / π ^ 6 by norm_num,
    table6_row_21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 8$** ($D = 21$): $\zeta_{21}(8)\,21^{7}\sqrt{21}/\pi^{8} = 2192034469/2520$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 8)"]
theorem table6_21_8 : zetaD 21 8 * 21 ^ 7 * Real.sqrt 21 / π ^ 8 = 2192034469 / 2520 := by
  rw [show zetaD 21 8 * 21 ^ 7 * Real.sqrt 21 / π ^ 8 =
      zetaD 21 ((8 : ℕ) : ℝ) * 21 ^ (8 - 1) * Real.sqrt 21 / π ^ 8 by norm_num,
    table6_row_21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 10$** ($D = 21$): $\zeta_{21}(10)\,21^{9}\sqrt{21}/\pi^{10} = 201488196865/5184$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 21, s = 10)"]
theorem table6_21_10 : zetaD 21 10 * 21 ^ 9 * Real.sqrt 21 / π ^ 10 = 201488196865 / 5184 := by
  rw [show zetaD 21 10 * 21 ^ 9 * Real.sqrt 21 / π ^ 10 =
      zetaD 21 ((10 : ℕ) : ℝ) * 21 ^ (10 - 1) * Real.sqrt 21 / π ^ 10 by norm_num,
    table6_row_21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 12$** ($D = 21$): $\zeta_{21}(12)\,21^{11}\sqrt{21}/\pi^{12} = 34661642709351829/19958400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 21, s = 12)"]
theorem table6_21_12 : zetaD 21 12 * 21 ^ 11 * Real.sqrt 21 / π ^ 12 = 34661642709351829 / 19958400 := by
  rw [show zetaD 21 12 * 21 ^ 11 * Real.sqrt 21 / π ^ 12 =
      zetaD 21 ((12 : ℕ) : ℝ) * 21 ^ (12 - 1) * Real.sqrt 21 / π ^ 12 by norm_num,
    table6_row_21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-84}{\cdot}\right)$ modulo $84$ -/

instance isQuadDisc_neg84 : IsQuadDisc (-84) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-84 : ℤ) / 4 = -21 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -21$: the Kronecker character $\left(\frac{-84}{\cdot}\right)$ modulo $84$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -21)"]
noncomputable def psiNeg84 : DirichletCharacter ℂ 84 := kroneckerChar (-84)

theorem psiNeg84_natCast (n : ℕ) : psiNeg84 n = (chiD (-21) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-84) (by norm_num) n

theorem psiNeg84_inv : psiNeg84⁻¹ = psiNeg84 := kroneckerChar_inv (-84)

theorem psiNeg84_neg_one : psiNeg84 (-1) = -1 := by
  rw [show (-1 : ZMod 84) = ((83 : ℕ) : ZMod 84) by decide, psiNeg84_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -21, conductor 84)"]
theorem isPrimitive_psiNeg84 : psiNeg84.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 84 = {2, 3, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨43, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((43 : ℤ) : ZMod 84) = ((43 : ℕ) : ZMod 84) by norm_cast, psiNeg84_natCast]; norm_num [chiD]⟩
  · exact ⟨29, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((29 : ℤ) : ZMod 84) = ((29 : ℕ) : ZMod 84) by norm_cast, psiNeg84_natCast]; norm_num [chiD]⟩
  · exact ⟨13, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((13 : ℤ) : ZMod 84) = ((13 : ℕ) : ZMod 84) by norm_cast, psiNeg84_natCast]; norm_num [chiD]⟩

theorem psiNeg84_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 84, psiNeg84 (r : ZMod 84) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 5 + f 11 - f 13 + f 17 + f 19 + f 23 + f 25 - f 29 + f 31 + f 37 + f 41 - f 43
      - f 47 - f 53 + f 55 - f 59 - f 61 - f 65 - f 67 + f 71 - f 73 - f 79 - f 83 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg84_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg21 :
    ∀ m : ℕ, (chiD (-21) m : ℂ) = DirichletCharacter.changeLevel (show 84 ∣ 4 * (-21 : ℤ).natAbs by decide)
      psiNeg84 (m : ZMod (4 * (-21 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-21 : ℤ).natAbs) < 84 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-21 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg84_natCast] <;> norm_num [chiD]

theorem psiNeg84_euler_neg21 (s : ℕ) :
    ∏ p ∈ (4 * (-21 : ℤ).natAbs).primeFactors, (1 - psiNeg84 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-21 : ℤ).natAbs).primeFactors = {2, 3, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg84_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 21$, odd $s$** ($D = -21$, $\psi = \left(\frac{-84}{\cdot}\right)$ modulo
$k_1 = 84$): $\zeta_{-21}(s)\,21^{s-1}\sqrt{21}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,21^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{84}\psi(r)B_s(r/84)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg21 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-21) s * (21 : ℝ) ^ (s - 1) * Real.sqrt 21 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 84) + (Polynomial.bernoulli s).eval (5 / 84)
        + (Polynomial.bernoulli s).eval (11 / 84) - (Polynomial.bernoulli s).eval (13 / 84)
        + (Polynomial.bernoulli s).eval (17 / 84) + (Polynomial.bernoulli s).eval (19 / 84)
        + (Polynomial.bernoulli s).eval (23 / 84) + (Polynomial.bernoulli s).eval (25 / 84)
        - (Polynomial.bernoulli s).eval (29 / 84) + (Polynomial.bernoulli s).eval (31 / 84)
        + (Polynomial.bernoulli s).eval (37 / 84) + (Polynomial.bernoulli s).eval (41 / 84)
        - (Polynomial.bernoulli s).eval (43 / 84) - (Polynomial.bernoulli s).eval (47 / 84)
        - (Polynomial.bernoulli s).eval (53 / 84) + (Polynomial.bernoulli s).eval (55 / 84)
        - (Polynomial.bernoulli s).eval (59 / 84) - (Polynomial.bernoulli s).eval (61 / 84)
        - (Polynomial.bernoulli s).eval (65 / 84) - (Polynomial.bernoulli s).eval (67 / 84)
        + (Polynomial.bernoulli s).eval (71 / 84) - (Polynomial.bernoulli s).eval (73 / 84)
        - (Polynomial.bernoulli s).eval (79 / 84) - (Polynomial.bernoulli s).eval (83 / 84)| *
        21 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -21) (by norm_num) isPrimitive_psiNeg84
    psiNeg84_inv _ chiD_eq_changeLevel_neg21 hs
    (by rw [psiNeg84_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg84_euler_neg21 s) (psiNeg84_sum _) 21 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 21$, $s = 3$** ($D = -21$): $\zeta_{-21}(3)\,21^{2}\sqrt{21}/\pi^{3} = 263/4$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 3)"]
theorem table6_21_3 : zetaD (-21) 3 * 21 ^ 2 * Real.sqrt 21 / π ^ 3 = 263 / 4 := by
  rw [show zetaD (-21) 3 * 21 ^ 2 * Real.sqrt 21 / π ^ 3 =
      zetaD (-21) ((3 : ℕ) : ℝ) * 21 ^ (3 - 1) * Real.sqrt 21 / π ^ 3 by norm_num,
    table6_row_neg21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 5$** ($D = -21$): $\zeta_{-21}(5)\,21^{4}\sqrt{21}/\pi^{5} = 559345/192$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 5)"]
theorem table6_21_5 : zetaD (-21) 5 * 21 ^ 4 * Real.sqrt 21 / π ^ 5 = 559345 / 192 := by
  rw [show zetaD (-21) 5 * 21 ^ 4 * Real.sqrt 21 / π ^ 5 =
      zetaD (-21) ((5 : ℕ) : ℝ) * 21 ^ (5 - 1) * Real.sqrt 21 / π ^ 5 by norm_num,
    table6_row_neg21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 7$** ($D = -21$): $\zeta_{-21}(7)\,21^{6}\sqrt{21}/\pi^{7} = 2998225943/23040$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 7)"]
theorem table6_21_7 : zetaD (-21) 7 * 21 ^ 6 * Real.sqrt 21 / π ^ 7 = 2998225943 / 23040 := by
  rw [show zetaD (-21) 7 * 21 ^ 6 * Real.sqrt 21 / π ^ 7 =
      zetaD (-21) ((7 : ℕ) : ℝ) * 21 ^ (7 - 1) * Real.sqrt 21 / π ^ 7 by norm_num,
    table6_row_neg21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 9$** ($D = -21$): $\zeta_{-21}(9)\,21^{8}\sqrt{21}/\pi^{9} = 6001721823533/1032192$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 21, s = 9)"]
theorem table6_21_9 : zetaD (-21) 9 * 21 ^ 8 * Real.sqrt 21 / π ^ 9 = 6001721823533 / 1032192 := by
  rw [show zetaD (-21) 9 * 21 ^ 8 * Real.sqrt 21 / π ^ 9 =
      zetaD (-21) ((9 : ℕ) : ℝ) * 21 ^ (9 - 1) * Real.sqrt 21 / π ^ 9 by norm_num,
    table6_row_neg21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 21$, $s = 11$** ($D = -21$): $\zeta_{-21}(11)\,21^{10}\sqrt{21}/\pi^{11} = 482710780150102823/1857945600$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 21, s = 11)"]
theorem table6_21_11 : zetaD (-21) 11 * 21 ^ 10 * Real.sqrt 21 / π ^ 11 = 482710780150102823 / 1857945600 := by
  rw [show zetaD (-21) 11 * 21 ^ 10 * Real.sqrt 21 / π ^ 11 =
      zetaD (-21) ((11 : ℕ) : ℝ) * 21 ^ (11 - 1) * Real.sqrt 21 / π ^ 11 by norm_num,
    table6_row_neg21 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 22$ -/

/-! #### The character $\left(\frac{88}{\cdot}\right)$ modulo $88$ -/

instance isQuadDisc_88 : IsQuadDisc 88 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (88 : ℤ) / 4 = 22 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 22$: the Kronecker character $\left(\frac{88}{\cdot}\right)$ modulo $88$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 22)"]
noncomputable def psi88 : DirichletCharacter ℂ 88 := kroneckerChar 88

theorem psi88_natCast (n : ℕ) : psi88 n = (chiD 22 n : ℂ) :=
  kroneckerChar_natCast_of_zero 88 (by norm_num) n

theorem psi88_inv : psi88⁻¹ = psi88 := kroneckerChar_inv 88

theorem psi88_neg_one : psi88 (-1) = 1 := by
  rw [show (-1 : ZMod 88) = ((87 : ℕ) : ZMod 88) by decide, psi88_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 22, conductor 88)"]
theorem isPrimitive_psi88 : psi88.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 88 = {2, 11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨45, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((45 : ℤ) : ZMod 88) = ((45 : ℕ) : ZMod 88) by norm_cast, psi88_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 88) = ((17 : ℕ) : ZMod 88) by norm_cast, psi88_natCast]; norm_num [chiD]⟩

theorem psi88_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 88, psi88 (r : ZMod 88) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 - f 5 + f 7 + f 9 + f 13 - f 15 - f 17 - f 19 + f 21 - f 23 + f 25 + f 27 + f 29
      - f 31 - f 35 - f 37 + f 39 - f 41 - f 43 - f 45 - f 47 + f 49 - f 51 - f 53 - f 57 + f 59
      + f 61 + f 63 - f 65 + f 67 - f 69 - f 71 - f 73 + f 75 + f 79 + f 81 - f 83 + f 85 + f 87 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi88_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_22 :
    ∀ m : ℕ, (chiD 22 m : ℂ) = DirichletCharacter.changeLevel (show 88 ∣ 4 * (22 : ℤ).natAbs by decide)
      psi88 (m : ZMod (4 * (22 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (22 : ℤ).natAbs) < 88 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (22 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi88_natCast] <;> norm_num [chiD]

theorem psi88_euler_22 (s : ℕ) :
    ∏ p ∈ (4 * (22 : ℤ).natAbs).primeFactors, (1 - psi88 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (22 : ℤ).natAbs).primeFactors = {2, 11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi88_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 22$, even $s$** ($D = 22$, $\psi = \left(\frac{88}{\cdot}\right)$ modulo
$k_1 = 88$): $\zeta_{22}(s)\,22^{s-1}\sqrt{22}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,22^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{88}\psi(r)B_s(r/88)$ (`zetaD_eq_abs`). -/
theorem table6_row_22 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 22 s * (22 : ℝ) ^ (s - 1) * Real.sqrt 22 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 88) + (Polynomial.bernoulli s).eval (3 / 88)
        - (Polynomial.bernoulli s).eval (5 / 88) + (Polynomial.bernoulli s).eval (7 / 88)
        + (Polynomial.bernoulli s).eval (9 / 88) + (Polynomial.bernoulli s).eval (13 / 88)
        - (Polynomial.bernoulli s).eval (15 / 88) - (Polynomial.bernoulli s).eval (17 / 88)
        - (Polynomial.bernoulli s).eval (19 / 88) + (Polynomial.bernoulli s).eval (21 / 88)
        - (Polynomial.bernoulli s).eval (23 / 88) + (Polynomial.bernoulli s).eval (25 / 88)
        + (Polynomial.bernoulli s).eval (27 / 88) + (Polynomial.bernoulli s).eval (29 / 88)
        - (Polynomial.bernoulli s).eval (31 / 88) - (Polynomial.bernoulli s).eval (35 / 88)
        - (Polynomial.bernoulli s).eval (37 / 88) + (Polynomial.bernoulli s).eval (39 / 88)
        - (Polynomial.bernoulli s).eval (41 / 88) - (Polynomial.bernoulli s).eval (43 / 88)
        - (Polynomial.bernoulli s).eval (45 / 88) - (Polynomial.bernoulli s).eval (47 / 88)
        + (Polynomial.bernoulli s).eval (49 / 88) - (Polynomial.bernoulli s).eval (51 / 88)
        - (Polynomial.bernoulli s).eval (53 / 88) - (Polynomial.bernoulli s).eval (57 / 88)
        + (Polynomial.bernoulli s).eval (59 / 88) + (Polynomial.bernoulli s).eval (61 / 88)
        + (Polynomial.bernoulli s).eval (63 / 88) - (Polynomial.bernoulli s).eval (65 / 88)
        + (Polynomial.bernoulli s).eval (67 / 88) - (Polynomial.bernoulli s).eval (69 / 88)
        - (Polynomial.bernoulli s).eval (71 / 88) - (Polynomial.bernoulli s).eval (73 / 88)
        + (Polynomial.bernoulli s).eval (75 / 88) + (Polynomial.bernoulli s).eval (79 / 88)
        + (Polynomial.bernoulli s).eval (81 / 88) - (Polynomial.bernoulli s).eval (83 / 88)
        + (Polynomial.bernoulli s).eval (85 / 88) + (Polynomial.bernoulli s).eval (87 / 88)| *
        22 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 22) (by norm_num) isPrimitive_psi88
    psi88_inv _ chiD_eq_changeLevel_22 hs
    (by rw [psi88_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi88_euler_22 s) (psi88_sum _) 22 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 22$, $s = 2$** ($D = 22$): $\zeta_{22}(2)\,22^{1}\sqrt{22}/\pi^{2} = 23/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 2)"]
theorem table6_22_2 : zetaD 22 2 * 22 ^ 1 * Real.sqrt 22 / π ^ 2 = 23 / 2 := by
  rw [show zetaD 22 2 * 22 ^ 1 * Real.sqrt 22 / π ^ 2 =
      zetaD 22 ((2 : ℕ) : ℝ) * 22 ^ (2 - 1) * Real.sqrt 22 / π ^ 2 by norm_num,
    table6_row_22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 4$** ($D = 22$): $\zeta_{22}(4)\,22^{3}\sqrt{22}/\pi^{4} = 24889/48$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 4)"]
theorem table6_22_4 : zetaD 22 4 * 22 ^ 3 * Real.sqrt 22 / π ^ 4 = 24889 / 48 := by
  rw [show zetaD 22 4 * 22 ^ 3 * Real.sqrt 22 / π ^ 4 =
      zetaD 22 ((4 : ℕ) : ℝ) * 22 ^ (4 - 1) * Real.sqrt 22 / π ^ 4 by norm_num,
    table6_row_22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 6$** ($D = 22$): $\zeta_{22}(6)\,22^{5}\sqrt{22}/\pi^{6} = 96678263/3840$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 6)"]
theorem table6_22_6 : zetaD 22 6 * 22 ^ 5 * Real.sqrt 22 / π ^ 6 = 96678263 / 3840 := by
  rw [show zetaD 22 6 * 22 ^ 5 * Real.sqrt 22 / π ^ 6 =
      zetaD 22 ((6 : ℕ) : ℝ) * 22 ^ (6 - 1) * Real.sqrt 22 / π ^ 6 by norm_num,
    table6_row_22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 8$** ($D = 22$): $\zeta_{22}(8)\,22^{7}\sqrt{22}/\pi^{8} = 795567059929/645120$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 8)"]
theorem table6_22_8 : zetaD 22 8 * 22 ^ 7 * Real.sqrt 22 / π ^ 8 = 795567059929 / 645120 := by
  rw [show zetaD 22 8 * 22 ^ 7 * Real.sqrt 22 / π ^ 8 =
      zetaD 22 ((8 : ℕ) : ℝ) * 22 ^ (8 - 1) * Real.sqrt 22 / π ^ 8 by norm_num,
    table6_row_22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 10$** ($D = 22$): $\zeta_{22}(10)\,22^{9}\sqrt{22}/\pi^{10} = 11234585316623063/185794560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 22, s = 10)"]
theorem table6_22_10 : zetaD 22 10 * 22 ^ 9 * Real.sqrt 22 / π ^ 10 = 11234585316623063 / 185794560 := by
  rw [show zetaD 22 10 * 22 ^ 9 * Real.sqrt 22 / π ^ 10 =
      zetaD 22 ((10 : ℕ) : ℝ) * 22 ^ (10 - 1) * Real.sqrt 22 / π ^ 10 by norm_num,
    table6_row_22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 12$** ($D = 22$): $\zeta_{22}(12)\,22^{11}\sqrt{22}/\pi^{12} = 242409057451908699769/81749606400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 22, s = 12)"]
theorem table6_22_12 : zetaD 22 12 * 22 ^ 11 * Real.sqrt 22 / π ^ 12 = 242409057451908699769 / 81749606400 := by
  rw [show zetaD 22 12 * 22 ^ 11 * Real.sqrt 22 / π ^ 12 =
      zetaD 22 ((12 : ℕ) : ℝ) * 22 ^ (12 - 1) * Real.sqrt 22 / π ^ 12 by norm_num,
    table6_row_22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-88}{\cdot}\right)$ modulo $88$ -/

instance isQuadDisc_neg88 : IsQuadDisc (-88) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-88 : ℤ) / 4 = -22 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -22$: the Kronecker character $\left(\frac{-88}{\cdot}\right)$ modulo $88$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -22)"]
noncomputable def psiNeg88 : DirichletCharacter ℂ 88 := kroneckerChar (-88)

theorem psiNeg88_natCast (n : ℕ) : psiNeg88 n = (chiD (-22) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-88) (by norm_num) n

theorem psiNeg88_inv : psiNeg88⁻¹ = psiNeg88 := kroneckerChar_inv (-88)

theorem psiNeg88_neg_one : psiNeg88 (-1) = -1 := by
  rw [show (-1 : ZMod 88) = ((87 : ℕ) : ZMod 88) by decide, psiNeg88_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -22, conductor 88)"]
theorem isPrimitive_psiNeg88 : psiNeg88.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 88 = {2, 11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨45, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((45 : ℤ) : ZMod 88) = ((45 : ℕ) : ZMod 88) by norm_cast, psiNeg88_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 88) = ((17 : ℕ) : ZMod 88) by norm_cast, psiNeg88_natCast]; norm_num [chiD]⟩

theorem psiNeg88_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 88, psiNeg88 (r : ZMod 88) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 - f 5 - f 7 + f 9 + f 13 + f 15 - f 17 + f 19 + f 21 + f 23 + f 25 - f 27 + f 29
      + f 31 + f 35 - f 37 - f 39 - f 41 + f 43 - f 45 + f 47 + f 49 + f 51 - f 53 - f 57 - f 59
      + f 61 - f 63 - f 65 - f 67 - f 69 + f 71 - f 73 - f 75 - f 79 + f 81 + f 83 + f 85 - f 87 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg88_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg22 :
    ∀ m : ℕ, (chiD (-22) m : ℂ) = DirichletCharacter.changeLevel (show 88 ∣ 4 * (-22 : ℤ).natAbs by decide)
      psiNeg88 (m : ZMod (4 * (-22 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-22 : ℤ).natAbs) < 88 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-22 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg88_natCast] <;> norm_num [chiD]

theorem psiNeg88_euler_neg22 (s : ℕ) :
    ∏ p ∈ (4 * (-22 : ℤ).natAbs).primeFactors, (1 - psiNeg88 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-22 : ℤ).natAbs).primeFactors = {2, 11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg88_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 22$, odd $s$** ($D = -22$, $\psi = \left(\frac{-88}{\cdot}\right)$ modulo
$k_1 = 88$): $\zeta_{-22}(s)\,22^{s-1}\sqrt{22}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,22^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{88}\psi(r)B_s(r/88)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg22 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-22) s * (22 : ℝ) ^ (s - 1) * Real.sqrt 22 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 88) - (Polynomial.bernoulli s).eval (3 / 88)
        - (Polynomial.bernoulli s).eval (5 / 88) - (Polynomial.bernoulli s).eval (7 / 88)
        + (Polynomial.bernoulli s).eval (9 / 88) + (Polynomial.bernoulli s).eval (13 / 88)
        + (Polynomial.bernoulli s).eval (15 / 88) - (Polynomial.bernoulli s).eval (17 / 88)
        + (Polynomial.bernoulli s).eval (19 / 88) + (Polynomial.bernoulli s).eval (21 / 88)
        + (Polynomial.bernoulli s).eval (23 / 88) + (Polynomial.bernoulli s).eval (25 / 88)
        - (Polynomial.bernoulli s).eval (27 / 88) + (Polynomial.bernoulli s).eval (29 / 88)
        + (Polynomial.bernoulli s).eval (31 / 88) + (Polynomial.bernoulli s).eval (35 / 88)
        - (Polynomial.bernoulli s).eval (37 / 88) - (Polynomial.bernoulli s).eval (39 / 88)
        - (Polynomial.bernoulli s).eval (41 / 88) + (Polynomial.bernoulli s).eval (43 / 88)
        - (Polynomial.bernoulli s).eval (45 / 88) + (Polynomial.bernoulli s).eval (47 / 88)
        + (Polynomial.bernoulli s).eval (49 / 88) + (Polynomial.bernoulli s).eval (51 / 88)
        - (Polynomial.bernoulli s).eval (53 / 88) - (Polynomial.bernoulli s).eval (57 / 88)
        - (Polynomial.bernoulli s).eval (59 / 88) + (Polynomial.bernoulli s).eval (61 / 88)
        - (Polynomial.bernoulli s).eval (63 / 88) - (Polynomial.bernoulli s).eval (65 / 88)
        - (Polynomial.bernoulli s).eval (67 / 88) - (Polynomial.bernoulli s).eval (69 / 88)
        + (Polynomial.bernoulli s).eval (71 / 88) - (Polynomial.bernoulli s).eval (73 / 88)
        - (Polynomial.bernoulli s).eval (75 / 88) - (Polynomial.bernoulli s).eval (79 / 88)
        + (Polynomial.bernoulli s).eval (81 / 88) + (Polynomial.bernoulli s).eval (83 / 88)
        + (Polynomial.bernoulli s).eval (85 / 88) - (Polynomial.bernoulli s).eval (87 / 88)| *
        22 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -22) (by norm_num) isPrimitive_psiNeg88
    psiNeg88_inv _ chiD_eq_changeLevel_neg22 hs
    (by rw [psiNeg88_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg88_euler_neg22 s) (psiNeg88_sum _) 22 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 22$, $s = 3$** ($D = -22$): $\zeta_{-22}(3)\,22^{2}\sqrt{22}/\pi^{3} = 559/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 3)"]
theorem table6_22_3 : zetaD (-22) 3 * 22 ^ 2 * Real.sqrt 22 / π ^ 3 = 559 / 8 := by
  rw [show zetaD (-22) 3 * 22 ^ 2 * Real.sqrt 22 / π ^ 3 =
      zetaD (-22) ((3 : ℕ) : ℝ) * 22 ^ (3 - 1) * Real.sqrt 22 / π ^ 3 by norm_num,
    table6_row_neg22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 5$** ($D = -22$): $\zeta_{-22}(5)\,22^{4}\sqrt{22}/\pi^{5} = 1372577/384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 5)"]
theorem table6_22_5 : zetaD (-22) 5 * 22 ^ 4 * Real.sqrt 22 / π ^ 5 = 1372577 / 384 := by
  rw [show zetaD (-22) 5 * 22 ^ 4 * Real.sqrt 22 / π ^ 5 =
      zetaD (-22) ((5 : ℕ) : ℝ) * 22 ^ (5 - 1) * Real.sqrt 22 / π ^ 5 by norm_num,
    table6_row_neg22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 7$** ($D = -22$): $\zeta_{-22}(7)\,22^{6}\sqrt{22}/\pi^{7} = 8109725839/46080$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 7)"]
theorem table6_22_7 : zetaD (-22) 7 * 22 ^ 6 * Real.sqrt 22 / π ^ 7 = 8109725839 / 46080 := by
  rw [show zetaD (-22) 7 * 22 ^ 6 * Real.sqrt 22 / π ^ 7 =
      zetaD (-22) ((7 : ℕ) : ℝ) * 22 ^ (7 - 1) * Real.sqrt 22 / π ^ 7 by norm_num,
    table6_row_neg22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 9$** ($D = -22$): $\zeta_{-22}(9)\,22^{8}\sqrt{22}/\pi^{9} = 89121425517377/10321920$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 22, s = 9)"]
theorem table6_22_9 : zetaD (-22) 9 * 22 ^ 8 * Real.sqrt 22 / π ^ 9 = 89121425517377 / 10321920 := by
  rw [show zetaD (-22) 9 * 22 ^ 8 * Real.sqrt 22 / π ^ 9 =
      zetaD (-22) ((9 : ℕ) : ℝ) * 22 ^ (9 - 1) * Real.sqrt 22 / π ^ 9 by norm_num,
    table6_row_neg22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 22$, $s = 11$** ($D = -22$): $\zeta_{-22}(11)\,22^{10}\sqrt{22}/\pi^{11} = 1573439605792110319/3715891200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 22, s = 11)"]
theorem table6_22_11 : zetaD (-22) 11 * 22 ^ 10 * Real.sqrt 22 / π ^ 11 = 1573439605792110319 / 3715891200 := by
  rw [show zetaD (-22) 11 * 22 ^ 10 * Real.sqrt 22 / π ^ 11 =
      zetaD (-22) ((11 : ℕ) : ℝ) * 22 ^ (11 - 1) * Real.sqrt 22 / π ^ 11 by norm_num,
    table6_row_neg22 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 23$ -/

/-! #### The character $\left(\frac{92}{\cdot}\right)$ modulo $92$ -/

instance isQuadDisc_92 : IsQuadDisc 92 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (92 : ℤ) / 4 = 23 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 23$: the Kronecker character $\left(\frac{92}{\cdot}\right)$ modulo $92$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 23)"]
noncomputable def psi92 : DirichletCharacter ℂ 92 := kroneckerChar 92

theorem psi92_natCast (n : ℕ) : psi92 n = (chiD 23 n : ℂ) :=
  kroneckerChar_natCast_of_zero 92 (by norm_num) n

theorem psi92_inv : psi92⁻¹ = psi92 := kroneckerChar_inv 92

theorem psi92_neg_one : psi92 (-1) = 1 := by
  rw [show (-1 : ZMod 92) = ((91 : ℕ) : ZMod 92) by decide, psi92_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 23, conductor 92)"]
theorem isPrimitive_psi92 : psi92.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 92 = {2, 23} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨47, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((47 : ℤ) : ZMod 92) = ((47 : ℕ) : ZMod 92) by norm_cast, psi92_natCast]; norm_num [chiD]⟩
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 92) = ((5 : ℕ) : ZMod 92) by norm_cast, psi92_natCast]; norm_num [chiD]⟩

theorem psi92_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 92, psi92 (r : ZMod 92) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 - f 5 + f 7 + f 9 + f 11 + f 13 + f 15 - f 17 + f 19 - f 21 + f 25 - f 27 + f 29
      - f 31 - f 33 - f 35 - f 37 - f 39 + f 41 + f 43 - f 45 - f 47 + f 49 + f 51 - f 53 - f 55
      - f 57 - f 59 - f 61 + f 63 - f 65 + f 67 - f 71 + f 73 - f 75 + f 77 + f 79 + f 81 + f 83
      + f 85 - f 87 - f 89 + f 91 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi92_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_23 :
    ∀ m : ℕ, (chiD 23 m : ℂ) = DirichletCharacter.changeLevel (show 92 ∣ 4 * (23 : ℤ).natAbs by decide)
      psi92 (m : ZMod (4 * (23 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (23 : ℤ).natAbs) < 92 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (23 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi92_natCast] <;> norm_num [chiD]

theorem psi92_euler_23 (s : ℕ) :
    ∏ p ∈ (4 * (23 : ℤ).natAbs).primeFactors, (1 - psi92 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (23 : ℤ).natAbs).primeFactors = {2, 23} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi92_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 23$, even $s$** ($D = 23$, $\psi = \left(\frac{92}{\cdot}\right)$ modulo
$k_1 = 92$): $\zeta_{23}(s)\,23^{s-1}\sqrt{23}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,23^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{92}\psi(r)B_s(r/92)$ (`zetaD_eq_abs`). -/
theorem table6_row_23 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 23 s * (23 : ℝ) ^ (s - 1) * Real.sqrt 23 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 92) - (Polynomial.bernoulli s).eval (3 / 92)
        - (Polynomial.bernoulli s).eval (5 / 92) + (Polynomial.bernoulli s).eval (7 / 92)
        + (Polynomial.bernoulli s).eval (9 / 92) + (Polynomial.bernoulli s).eval (11 / 92)
        + (Polynomial.bernoulli s).eval (13 / 92) + (Polynomial.bernoulli s).eval (15 / 92)
        - (Polynomial.bernoulli s).eval (17 / 92) + (Polynomial.bernoulli s).eval (19 / 92)
        - (Polynomial.bernoulli s).eval (21 / 92) + (Polynomial.bernoulli s).eval (25 / 92)
        - (Polynomial.bernoulli s).eval (27 / 92) + (Polynomial.bernoulli s).eval (29 / 92)
        - (Polynomial.bernoulli s).eval (31 / 92) - (Polynomial.bernoulli s).eval (33 / 92)
        - (Polynomial.bernoulli s).eval (35 / 92) - (Polynomial.bernoulli s).eval (37 / 92)
        - (Polynomial.bernoulli s).eval (39 / 92) + (Polynomial.bernoulli s).eval (41 / 92)
        + (Polynomial.bernoulli s).eval (43 / 92) - (Polynomial.bernoulli s).eval (45 / 92)
        - (Polynomial.bernoulli s).eval (47 / 92) + (Polynomial.bernoulli s).eval (49 / 92)
        + (Polynomial.bernoulli s).eval (51 / 92) - (Polynomial.bernoulli s).eval (53 / 92)
        - (Polynomial.bernoulli s).eval (55 / 92) - (Polynomial.bernoulli s).eval (57 / 92)
        - (Polynomial.bernoulli s).eval (59 / 92) - (Polynomial.bernoulli s).eval (61 / 92)
        + (Polynomial.bernoulli s).eval (63 / 92) - (Polynomial.bernoulli s).eval (65 / 92)
        + (Polynomial.bernoulli s).eval (67 / 92) - (Polynomial.bernoulli s).eval (71 / 92)
        + (Polynomial.bernoulli s).eval (73 / 92) - (Polynomial.bernoulli s).eval (75 / 92)
        + (Polynomial.bernoulli s).eval (77 / 92) + (Polynomial.bernoulli s).eval (79 / 92)
        + (Polynomial.bernoulli s).eval (81 / 92) + (Polynomial.bernoulli s).eval (83 / 92)
        + (Polynomial.bernoulli s).eval (85 / 92) - (Polynomial.bernoulli s).eval (87 / 92)
        - (Polynomial.bernoulli s).eval (89 / 92) + (Polynomial.bernoulli s).eval (91 / 92)| *
        23 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 23) (by norm_num) isPrimitive_psi92
    psi92_inv _ chiD_eq_changeLevel_23 hs
    (by rw [psi92_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi92_euler_23 s) (psi92_sum _) 23 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 23$, $s = 2$** ($D = 23$): $\zeta_{23}(2)\,23^{1}\sqrt{23}/\pi^{2} = 10$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 2)"]
theorem table6_23_2 : zetaD 23 2 * 23 ^ 1 * Real.sqrt 23 / π ^ 2 = 10 := by
  rw [show zetaD 23 2 * 23 ^ 1 * Real.sqrt 23 / π ^ 2 =
      zetaD 23 ((2 : ℕ) : ℝ) * 23 ^ (2 - 1) * Real.sqrt 23 / π ^ 2 by norm_num,
    table6_row_23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 4$** ($D = 23$): $\zeta_{23}(4)\,23^{3}\sqrt{23}/\pi^{4} = 7093/12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 4)"]
theorem table6_23_4 : zetaD 23 4 * 23 ^ 3 * Real.sqrt 23 / π ^ 4 = 7093 / 12 := by
  rw [show zetaD 23 4 * 23 ^ 3 * Real.sqrt 23 / π ^ 4 =
      zetaD 23 ((4 : ℕ) : ℝ) * 23 ^ (4 - 1) * Real.sqrt 23 / π ^ 4 by norm_num,
    table6_row_23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 6$** ($D = 23$): $\zeta_{23}(6)\,23^{5}\sqrt{23}/\pi^{6} = 6155821/192$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 6)"]
theorem table6_23_6 : zetaD 23 6 * 23 ^ 5 * Real.sqrt 23 / π ^ 6 = 6155821 / 192 := by
  rw [show zetaD 23 6 * 23 ^ 5 * Real.sqrt 23 / π ^ 6 =
      zetaD 23 ((6 : ℕ) : ℝ) * 23 ^ (6 - 1) * Real.sqrt 23 / π ^ 6 by norm_num,
    table6_row_23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 8$** ($D = 23$): $\zeta_{23}(8)\,23^{7}\sqrt{23}/\pi^{8} = 277506449593/161280$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 8)"]
theorem table6_23_8 : zetaD 23 8 * 23 ^ 7 * Real.sqrt 23 / π ^ 8 = 277506449593 / 161280 := by
  rw [show zetaD 23 8 * 23 ^ 7 * Real.sqrt 23 / π ^ 8 =
      zetaD 23 ((8 : ℕ) : ℝ) * 23 ^ (8 - 1) * Real.sqrt 23 / π ^ 8 by norm_num,
    table6_row_23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 10$** ($D = 23$): $\zeta_{23}(10)\,23^{9}\sqrt{23}/\pi^{10} = 856862853365401/9289728$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 23, s = 10)"]
theorem table6_23_10 : zetaD 23 10 * 23 ^ 9 * Real.sqrt 23 / π ^ 10 = 856862853365401 / 9289728 := by
  rw [show zetaD 23 10 * 23 ^ 9 * Real.sqrt 23 / π ^ 10 =
      zetaD 23 ((10 : ℕ) : ℝ) * 23 ^ (10 - 1) * Real.sqrt 23 / π ^ 10 by norm_num,
    table6_row_23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 12$** ($D = 23$): $\zeta_{23}(12)\,23^{11}\sqrt{23}/\pi^{12} = 14434390886810961499/2919628800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 23, s = 12)"]
theorem table6_23_12 : zetaD 23 12 * 23 ^ 11 * Real.sqrt 23 / π ^ 12 = 14434390886810961499 / 2919628800 := by
  rw [show zetaD 23 12 * 23 ^ 11 * Real.sqrt 23 / π ^ 12 =
      zetaD 23 ((12 : ℕ) : ℝ) * 23 ^ (12 - 1) * Real.sqrt 23 / π ^ 12 by norm_num,
    table6_row_23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-23}{\cdot}\right)$ modulo $23$ -/

instance isQuadDisc_neg23 : IsQuadDisc (-23) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = -23$: the Kronecker character $\left(\frac{-23}{\cdot}\right)$ modulo $23$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -23)"]
noncomputable def psiNeg23 : DirichletCharacter ℂ 23 := kroneckerChar (-23)

theorem psiNeg23_natCast (n : ℕ) : psiNeg23 n = (jacobiSym n 23 : ℂ) :=
  kroneckerChar_natCast_of_one (-23) (by norm_num) n

theorem psiNeg23_inv : psiNeg23⁻¹ = psiNeg23 := kroneckerChar_inv (-23)

theorem psiNeg23_neg_one : psiNeg23 (-1) = -1 := by
  rw [show (-1 : ZMod 23) = ((22 : ℕ) : ZMod 23) by decide, psiNeg23_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -23, conductor 23)"]
theorem isPrimitive_psiNeg23 : psiNeg23.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 23 = {23} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_singleton] at hp
  rcases hp with rfl
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 23) = ((5 : ℕ) : ZMod 23) by norm_cast, psiNeg23_natCast]; norm_num [chiD]⟩

theorem psiNeg23_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 23, psiNeg23 (r : ZMod 23) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 2 + f 3 + f 4 - f 5 + f 6 - f 7 + f 8 + f 9 - f 10 - f 11 + f 12 + f 13 - f 14
      - f 15 + f 16 - f 17 + f 18 - f 19 - f 20 - f 21 - f 22 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg23_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg23 :
    ∀ m : ℕ, (chiD (-23) m : ℂ) = DirichletCharacter.changeLevel (show 23 ∣ 4 * (-23 : ℤ).natAbs by decide)
      psiNeg23 (m : ZMod (4 * (-23 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-23 : ℤ).natAbs) < 92 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-23 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg23_natCast] <;> norm_num [chiD]

theorem psiNeg23_euler_neg23 (s : ℕ) :
    ∏ p ∈ (4 * (-23 : ℤ).natAbs).primeFactors, (1 - psiNeg23 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-23 : ℤ).natAbs).primeFactors = {2, 23} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg23_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 23$, odd $s$** ($D = -23$, $\psi = \left(\frac{-23}{\cdot}\right)$ modulo
$k_1 = 23$): $\zeta_{-23}(s)\,23^{s-1}\sqrt{23}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,23^{s-1}/(2\,s!)$ with
$E = (1 - 2^{-s})$ and $S = \sum_{r=1}^{23}\psi(r)B_s(r/23)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg23 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-23) s * (23 : ℝ) ^ (s - 1) * Real.sqrt 23 / π ^ s =
      ((|(1 - 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 23) + (Polynomial.bernoulli s).eval (2 / 23)
        + (Polynomial.bernoulli s).eval (3 / 23) + (Polynomial.bernoulli s).eval (4 / 23)
        - (Polynomial.bernoulli s).eval (5 / 23) + (Polynomial.bernoulli s).eval (6 / 23)
        - (Polynomial.bernoulli s).eval (7 / 23) + (Polynomial.bernoulli s).eval (8 / 23)
        + (Polynomial.bernoulli s).eval (9 / 23) - (Polynomial.bernoulli s).eval (10 / 23)
        - (Polynomial.bernoulli s).eval (11 / 23) + (Polynomial.bernoulli s).eval (12 / 23)
        + (Polynomial.bernoulli s).eval (13 / 23) - (Polynomial.bernoulli s).eval (14 / 23)
        - (Polynomial.bernoulli s).eval (15 / 23) + (Polynomial.bernoulli s).eval (16 / 23)
        - (Polynomial.bernoulli s).eval (17 / 23) + (Polynomial.bernoulli s).eval (18 / 23)
        - (Polynomial.bernoulli s).eval (19 / 23) - (Polynomial.bernoulli s).eval (20 / 23)
        - (Polynomial.bernoulli s).eval (21 / 23) - (Polynomial.bernoulli s).eval (22 / 23)| *
        23 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -23) (by norm_num) isPrimitive_psiNeg23
    psiNeg23_inv _ chiD_eq_changeLevel_neg23 hs
    (by rw [psiNeg23_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg23_euler_neg23 s) (psiNeg23_sum _) 23 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 23$, $s = 3$** ($D = -23$): $\zeta_{-23}(3)\,23^{2}\sqrt{23}/\pi^{3} = 84$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 3)"]
theorem table6_23_3 : zetaD (-23) 3 * 23 ^ 2 * Real.sqrt 23 / π ^ 3 = 84 := by
  rw [show zetaD (-23) 3 * 23 ^ 2 * Real.sqrt 23 / π ^ 3 =
      zetaD (-23) ((3 : ℕ) : ℝ) * 23 ^ (3 - 1) * Real.sqrt 23 / π ^ 3 by norm_num,
    table6_row_neg23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 5$** ($D = -23$): $\zeta_{-23}(5)\,23^{4}\sqrt{23}/\pi^{5} = 4402$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 5)"]
theorem table6_23_5 : zetaD (-23) 5 * 23 ^ 4 * Real.sqrt 23 / π ^ 5 = 4402 := by
  rw [show zetaD (-23) 5 * 23 ^ 4 * Real.sqrt 23 / π ^ 5 =
      zetaD (-23) ((5 : ℕ) : ℝ) * 23 ^ (5 - 1) * Real.sqrt 23 / π ^ 5 by norm_num,
    table6_row_neg23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 7$** ($D = -23$): $\zeta_{-23}(7)\,23^{6}\sqrt{23}/\pi^{7} = 2351659/10$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 7)"]
theorem table6_23_7 : zetaD (-23) 7 * 23 ^ 6 * Real.sqrt 23 / π ^ 7 = 2351659 / 10 := by
  rw [show zetaD (-23) 7 * 23 ^ 6 * Real.sqrt 23 / π ^ 7 =
      zetaD (-23) ((7 : ℕ) : ℝ) * 23 ^ (7 - 1) * Real.sqrt 23 / π ^ 7 by norm_num,
    table6_row_neg23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 9$** ($D = -23$): $\zeta_{-23}(9)\,23^{8}\sqrt{23}/\pi^{9} = 755980919/60$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 23, s = 9)"]
theorem table6_23_9 : zetaD (-23) 9 * 23 ^ 8 * Real.sqrt 23 / π ^ 9 = 755980919 / 60 := by
  rw [show zetaD (-23) 9 * 23 ^ 8 * Real.sqrt 23 / π ^ 9 =
      zetaD (-23) ((9 : ℕ) : ℝ) * 23 ^ (9 - 1) * Real.sqrt 23 / π ^ 9 by norm_num,
    table6_row_neg23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 23$, $s = 11$** ($D = -23$): $\zeta_{-23}(11)\,23^{10}\sqrt{23}/\pi^{11} = 102105212194847/151200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 23, s = 11)"]
theorem table6_23_11 : zetaD (-23) 11 * 23 ^ 10 * Real.sqrt 23 / π ^ 11 = 102105212194847 / 151200 := by
  rw [show zetaD (-23) 11 * 23 ^ 10 * Real.sqrt 23 / π ^ 11 =
      zetaD (-23) ((11 : ℕ) : ℝ) * 23 ^ (11 - 1) * Real.sqrt 23 / π ^ 11 by norm_num,
    table6_row_neg23 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 25$ -/

theorem chiD_eq_changeLevel_25 :
    ∀ m : ℕ, (chiD 25 m : ℂ) = DirichletCharacter.changeLevel (show 1 ∣ 4 * (25 : ℤ).natAbs by decide)
      (1 : DirichletCharacter ℂ 1) (m : ZMod (4 * (25 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (25 : ℤ).natAbs) < 100 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (25 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [one_level_one_apply] <;> norm_num [chiD]

theorem one1_euler_25 (s : ℕ) :
    ∏ p ∈ (4 * (25 : ℤ).natAbs).primeFactors, (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 2 ^ s) * (1 - 1 / 5 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (25 : ℤ).natAbs).primeFactors = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [one_level_one_apply, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 25$, even $s$** ($D = 25$, $\psi = \left(\frac{1}{\cdot}\right)$ modulo
$k_1 = 1$): $\zeta_{25}(s)\,25^{s-1}\sqrt{25}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,25^{s-1}(5/1)/(2\,s!)$ with
$E = (1 - 2^{-s})(1 - 5^{-s})$ and $S = \sum_{r=1}^{1}\psi(r)B_s(r/1)$ (`zetaD_eq_abs`). -/
theorem table6_row_25 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 25 s * (25 : ℝ) ^ (s - 1) * Real.sqrt 25 / π ^ s =
      ((|(1 - 1 / 2 ^ s) * (1 - 1 / 5 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 1)| *
        25 ^ (s - 1) * (5 / 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 25) (by norm_num) DirichletCharacter.isPrimitive_one_level_one
    inv_one _ chiD_eq_changeLevel_25 hs
    (by rw [one_level_one_apply, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (one1_euler_25 s) (one1_sum _) 25 _
    (sqrt_eq_rat_mul_sqrt (a := 5) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 25$, $s = 2$** ($D = 25$): $\zeta_{25}(2)\,25^{1}\sqrt{25}/\pi^{2} = 15$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 2)"]
theorem table6_25_2 : zetaD 25 2 * 25 ^ 1 * Real.sqrt 25 / π ^ 2 = 15 := by
  rw [show zetaD 25 2 * 25 ^ 1 * Real.sqrt 25 / π ^ 2 =
      zetaD 25 ((2 : ℕ) : ℝ) * 25 ^ (2 - 1) * Real.sqrt 25 / π ^ 2 by norm_num,
    table6_row_25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 4$** ($D = 25$): $\zeta_{25}(4)\,25^{3}\sqrt{25}/\pi^{4} = 1625/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 4)"]
theorem table6_25_4 : zetaD 25 4 * 25 ^ 3 * Real.sqrt 25 / π ^ 4 = 1625 / 2 := by
  rw [show zetaD 25 4 * 25 ^ 3 * Real.sqrt 25 / π ^ 4 =
      zetaD 25 ((4 : ℕ) : ℝ) * 25 ^ (4 - 1) * Real.sqrt 25 / π ^ 4 by norm_num,
    table6_row_25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 6$** ($D = 25$): $\zeta_{25}(6)\,25^{5}\sqrt{25}/\pi^{6} = 406875/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 6)"]
theorem table6_25_6 : zetaD 25 6 * 25 ^ 5 * Real.sqrt 25 / π ^ 6 = 406875 / 8 := by
  rw [show zetaD 25 6 * 25 ^ 5 * Real.sqrt 25 / π ^ 6 =
      zetaD 25 ((6 : ℕ) : ℝ) * 25 ^ (6 - 1) * Real.sqrt 25 / π ^ 6 by norm_num,
    table6_row_25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 8$** ($D = 25$): $\zeta_{25}(8)\,25^{7}\sqrt{25}/\pi^{8} = 1080828125/336$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 8)"]
theorem table6_25_8 : zetaD 25 8 * 25 ^ 7 * Real.sqrt 25 / π ^ 8 = 1080828125 / 336 := by
  rw [show zetaD 25 8 * 25 ^ 7 * Real.sqrt 25 / π ^ 8 =
      zetaD 25 ((8 : ℕ) : ℝ) * 25 ^ (8 - 1) * Real.sqrt 25 / π ^ 8 by norm_num,
    table6_row_25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 10$** ($D = 25$): $\zeta_{25}(10)\,25^{9}\sqrt{25}/\pi^{10} = 4927316796875/24192$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 25, s = 10)"]
theorem table6_25_10 : zetaD 25 10 * 25 ^ 9 * Real.sqrt 25 / π ^ 10 = 4927316796875 / 24192 := by
  rw [show zetaD 25 10 * 25 ^ 9 * Real.sqrt 25 / π ^ 10 =
      zetaD 25 ((10 : ℕ) : ℝ) * 25 ^ (10 - 1) * Real.sqrt 25 / π ^ 10 by norm_num,
    table6_row_25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 12$** ($D = 25$): $\zeta_{25}(12)\,25^{11}\sqrt{25}/\pi^{12} = 326879439453125/25344$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 25, s = 12)"]
theorem table6_25_12 : zetaD 25 12 * 25 ^ 11 * Real.sqrt 25 / π ^ 12 = 326879439453125 / 25344 := by
  rw [show zetaD 25 12 * 25 ^ 11 * Real.sqrt 25 / π ^ 12 =
      zetaD 25 ((12 : ℕ) : ℝ) * 25 ^ (12 - 1) * Real.sqrt 25 / π ^ 12 by norm_num,
    table6_row_25 (by norm_num) (by norm_num)]
  bernoulli_eval

theorem chiD_eq_changeLevel_neg25 :
    ∀ m : ℕ, (chiD (-25) m : ℂ) = DirichletCharacter.changeLevel (show 4 ∣ 4 * (-25 : ℤ).natAbs by decide)
      psiNeg4 (m : ZMod (4 * (-25 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-25 : ℤ).natAbs) < 100 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-25 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg4_natCast] <;> norm_num [chiD]

theorem psiNeg4_euler_neg25 (s : ℕ) :
    ∏ p ∈ (4 * (-25 : ℤ).natAbs).primeFactors, (1 - psiNeg4 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 5 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-25 : ℤ).natAbs).primeFactors = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg4_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 25$, odd $s$** ($D = -25$, $\psi = \left(\frac{-4}{\cdot}\right)$ modulo
$k_1 = 4$): $\zeta_{-25}(s)\,25^{s-1}\sqrt{25}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,25^{s-1}(5/2)/(2\,s!)$ with
$E = (1 - 5^{-s})$ and $S = \sum_{r=1}^{4}\psi(r)B_s(r/4)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg25 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-25) s * (25 : ℝ) ^ (s - 1) * Real.sqrt 25 / π ^ s =
      ((|(1 - 1 / 5 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 4) - (Polynomial.bernoulli s).eval (3 / 4)| *
        25 ^ (s - 1) * (5 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -25) (by norm_num) isPrimitive_psiNeg4
    psiNeg4_inv _ chiD_eq_changeLevel_neg25 hs
    (by rw [psiNeg4_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg4_euler_neg25 s) (psiNeg4_sum _) 25 _
    (sqrt_eq_rat_mul_sqrt (a := 5) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 25$, $s = 3$** ($D = -25$): $\zeta_{-25}(3)\,25^{2}\sqrt{25}/\pi^{3} = 775/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 3)"]
theorem table6_25_3 : zetaD (-25) 3 * 25 ^ 2 * Real.sqrt 25 / π ^ 3 = 775 / 8 := by
  rw [show zetaD (-25) 3 * 25 ^ 2 * Real.sqrt 25 / π ^ 3 =
      zetaD (-25) ((3 : ℕ) : ℝ) * 25 ^ (3 - 1) * Real.sqrt 25 / π ^ 3 by norm_num,
    table6_row_neg25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 5$** ($D = -25$): $\zeta_{-25}(5)\,25^{4}\sqrt{25}/\pi^{5} = 2440625/384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 5)"]
theorem table6_25_5 : zetaD (-25) 5 * 25 ^ 4 * Real.sqrt 25 / π ^ 5 = 2440625 / 384 := by
  rw [show zetaD (-25) 5 * 25 ^ 4 * Real.sqrt 25 / π ^ 5 =
      zetaD (-25) ((5 : ℕ) : ℝ) * 25 ^ (5 - 1) * Real.sqrt 25 / π ^ 5 by norm_num,
    table6_row_neg25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 7$** ($D = -25$): $\zeta_{-25}(7)\,25^{6}\sqrt{25}/\pi^{7} = 3723096875/9216$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 7)"]
theorem table6_25_7 : zetaD (-25) 7 * 25 ^ 6 * Real.sqrt 25 / π ^ 7 = 3723096875 / 9216 := by
  rw [show zetaD (-25) 7 * 25 ^ 6 * Real.sqrt 25 / π ^ 7 =
      zetaD (-25) ((7 : ℕ) : ℝ) * 25 ^ (7 - 1) * Real.sqrt 25 / π ^ 7 by norm_num,
    table6_row_neg25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 9$** ($D = -25$): $\zeta_{-25}(9)\,25^{8}\sqrt{25}/\pi^{9} = 52833530078125/2064384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 25, s = 9)"]
theorem table6_25_9 : zetaD (-25) 9 * 25 ^ 8 * Real.sqrt 25 / π ^ 9 = 52833530078125 / 2064384 := by
  rw [show zetaD (-25) 9 * 25 ^ 8 * Real.sqrt 25 / π ^ 9 =
      zetaD (-25) ((9 : ℕ) : ℝ) * 25 ^ (9 - 1) * Real.sqrt 25 / π ^ 9 by norm_num,
    table6_row_neg25 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 25$, $s = 11$** ($D = -25$): $\zeta_{-25}(11)\,25^{10}\sqrt{25}/\pi^{11} = 240902895762109375/148635648$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 25, s = 11)"]
theorem table6_25_11 : zetaD (-25) 11 * 25 ^ 10 * Real.sqrt 25 / π ^ 11 = 240902895762109375 / 148635648 := by
  rw [show zetaD (-25) 11 * 25 ^ 10 * Real.sqrt 25 / π ^ 11 =
      zetaD (-25) ((11 : ℕ) : ℝ) * 25 ^ (11 - 1) * Real.sqrt 25 / π ^ 11 by norm_num,
    table6_row_neg25 (by norm_num) (by norm_num)]
  bernoulli_eval

end QuadFormsKB.ConwaySloane.Mass
