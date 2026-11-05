/-
# Conway–Sloane 1988, §8, Table 6: the rows $d = 5, 6, 7, 10, 11$ for $s \ge 2$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, Table 6, pp. 270–271.

Table 6 lists the rational numbers $\zeta_D(s)\,d^{s-1}\sqrt d/\pi^s$, $D = (-1)^s d$. This file proves the entries
$2 \le s \le 12$ of the rows $d = 5, 6, 7, 10, 11$
from `zetaD_eq_abs` (the closed formula (13) with the Gauss sum eliminated by the positivity of $\zeta_D$,
`Table6Abs.lean`). The entries $s = 1$ need class numbers and are not treated here.

**Characters (book $\to$ Lean).** For each $D$ the primitive character $\psi$ of (13) is the Kronecker character
$\left(\frac{\Delta}{\cdot}\right)$ (`Binary.kroneckerChar Δ`) of the fundamental discriminant $\Delta$ of
$\mathbb Q(\sqrt D)$, a character modulo $k_1 = \lvert\Delta\rvert$ (Table 4):

| $d$ | $D$ (even $s$) | $\Delta$ | $k_1$ | $\psi$ | $D$ (odd $s$) | $\Delta$ | $k_1$ | $\psi$ |
|---|---|---|---|---|---|---|---|---|
| $5$ | $5$ | $5$ | $5$ | `psi5` | $-5$ | $-20$ | $20$ | `psiNeg20` |
| $6$ | $6$ | $24$ | $24$ | `psi24` | $-6$ | $-24$ | $24$ | `psiNeg24` |
| $7$ | $7$ | $28$ | $28$ | `psi28` | $-7$ | $-7$ | $7$ | `psiNeg7` |
| $10$ | $10$ | $40$ | $40$ | `psi40` | $-10$ | $-40$ | $40$ | `psiNeg40` |
| $11$ | $11$ | $44$ | $44$ | `psi44` | $-11$ | $-11$ | $11$ | `psiNeg11` |

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

/-! ### Row $d = 5$ -/

/-! #### The character $\left(\frac{5}{\cdot}\right)$ modulo $5$ -/

instance isQuadDisc_5 : IsQuadDisc 5 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = 5$: the Kronecker character $\left(\frac{5}{\cdot}\right)$ modulo $5$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 5)"]
noncomputable def psi5 : DirichletCharacter ℂ 5 := kroneckerChar 5

theorem psi5_natCast (n : ℕ) : psi5 n = (jacobiSym n 5 : ℂ) :=
  kroneckerChar_natCast_of_one 5 (by norm_num) n

theorem psi5_inv : psi5⁻¹ = psi5 := kroneckerChar_inv 5

theorem psi5_neg_one : psi5 (-1) = 1 := by
  rw [show (-1 : ZMod 5) = ((4 : ℕ) : ZMod 5) by decide, psi5_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 5, conductor 5)"]
theorem isPrimitive_psi5 : psi5.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 5 = {5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_singleton] at hp
  rcases hp with rfl
  · exact ⟨2, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((2 : ℤ) : ZMod 5) = ((2 : ℕ) : ZMod 5) by norm_cast, psi5_natCast]; norm_num [chiD]⟩

theorem psi5_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 5, psi5 (r : ZMod 5) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 2 - f 3 + f 4 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi5_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_5 :
    ∀ m : ℕ, (chiD 5 m : ℂ) = DirichletCharacter.changeLevel (show 5 ∣ 4 * (5 : ℤ).natAbs by decide)
      psi5 (m : ZMod (4 * (5 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (5 : ℤ).natAbs) < 20 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (5 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi5_natCast] <;> norm_num [chiD]

theorem psi5_euler_5 (s : ℕ) :
    ∏ p ∈ (4 * (5 : ℤ).natAbs).primeFactors, (1 - psi5 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 + 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (5 : ℤ).natAbs).primeFactors = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi5_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 5$, even $s$** ($D = 5$, $\psi = \left(\frac{5}{\cdot}\right)$ modulo
$k_1 = 5$): $\zeta_{5}(s)\,5^{s-1}\sqrt{5}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,5^{s-1}/(2\,s!)$ with
$E = (1 + 2^{-s})$ and $S = \sum_{r=1}^{5}\psi(r)B_s(r/5)$ (`zetaD_eq_abs`). -/
theorem table6_row_5 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 5 s * (5 : ℝ) ^ (s - 1) * Real.sqrt 5 / π ^ s =
      ((|(1 + 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 5) - (Polynomial.bernoulli s).eval (2 / 5)
        - (Polynomial.bernoulli s).eval (3 / 5) + (Polynomial.bernoulli s).eval (4 / 5)| *
        5 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 5) (by norm_num) isPrimitive_psi5
    psi5_inv _ chiD_eq_changeLevel_5 hs
    (by rw [psi5_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi5_euler_5 s) (psi5_sum _) 5 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 5$, $s = 2$** ($D = 5$): $\zeta_{5}(2)\,5^{1}\sqrt{5}/\pi^{2} = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 2)"]
theorem table6_5_2 : zetaD 5 2 * 5 ^ 1 * Real.sqrt 5 / π ^ 2 = 1 := by
  rw [show zetaD 5 2 * 5 ^ 1 * Real.sqrt 5 / π ^ 2 =
      zetaD 5 ((2 : ℕ) : ℝ) * 5 ^ (2 - 1) * Real.sqrt 5 / π ^ 2 by norm_num,
    table6_row_5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 4$** ($D = 5$): $\zeta_{5}(4)\,5^{3}\sqrt{5}/\pi^{4} = 17/6$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 4)"]
theorem table6_5_4 : zetaD 5 4 * 5 ^ 3 * Real.sqrt 5 / π ^ 4 = 17 / 6 := by
  rw [show zetaD 5 4 * 5 ^ 3 * Real.sqrt 5 / π ^ 4 =
      zetaD 5 ((4 : ℕ) : ℝ) * 5 ^ (4 - 1) * Real.sqrt 5 / π ^ 4 by norm_num,
    table6_row_5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 6$** ($D = 5$): $\zeta_{5}(6)\,5^{5}\sqrt{5}/\pi^{6} = 871/120$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 6)"]
theorem table6_5_6 : zetaD 5 6 * 5 ^ 5 * Real.sqrt 5 / π ^ 6 = 871 / 120 := by
  rw [show zetaD 5 6 * 5 ^ 5 * Real.sqrt 5 / π ^ 6 =
      zetaD 5 ((6 : ℕ) : ℝ) * 5 ^ (6 - 1) * Real.sqrt 5 / π ^ 6 by norm_num,
    table6_row_5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 8$** ($D = 5$): $\zeta_{5}(8)\,5^{7}\sqrt{5}/\pi^{8} = 92777/5040$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 8)"]
theorem table6_5_8 : zetaD 5 8 * 5 ^ 7 * Real.sqrt 5 / π ^ 8 = 92777 / 5040 := by
  rw [show zetaD 5 8 * 5 ^ 7 * Real.sqrt 5 / π ^ 8 =
      zetaD 5 ((8 : ℕ) : ℝ) * 5 ^ (8 - 1) * Real.sqrt 5 / π ^ 8 by norm_num,
    table6_row_5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 10$** ($D = 5$): $\zeta_{5}(10)\,5^{9}\sqrt{5}/\pi^{10} = 16922791/362880$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 5, s = 10)"]
theorem table6_5_10 : zetaD 5 10 * 5 ^ 9 * Real.sqrt 5 / π ^ 10 = 16922791 / 362880 := by
  rw [show zetaD 5 10 * 5 ^ 9 * Real.sqrt 5 / π ^ 10 =
      zetaD 5 ((10 : ℕ) : ℝ) * 5 ^ (10 - 1) * Real.sqrt 5 / π ^ 10 by norm_num,
    table6_row_5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 12$** ($D = 5$): $\zeta_{5}(12)\,5^{11}\sqrt{5}/\pi^{12} = 4715323337/39916800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 5, s = 12)"]
theorem table6_5_12 : zetaD 5 12 * 5 ^ 11 * Real.sqrt 5 / π ^ 12 = 4715323337 / 39916800 := by
  rw [show zetaD 5 12 * 5 ^ 11 * Real.sqrt 5 / π ^ 12 =
      zetaD 5 ((12 : ℕ) : ℝ) * 5 ^ (12 - 1) * Real.sqrt 5 / π ^ 12 by norm_num,
    table6_row_5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-20}{\cdot}\right)$ modulo $20$ -/

instance isQuadDisc_neg20 : IsQuadDisc (-20) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-20 : ℤ) / 4 = -5 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -5$: the Kronecker character $\left(\frac{-20}{\cdot}\right)$ modulo $20$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -5)"]
noncomputable def psiNeg20 : DirichletCharacter ℂ 20 := kroneckerChar (-20)

theorem psiNeg20_natCast (n : ℕ) : psiNeg20 n = (chiD (-5) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-20) (by norm_num) n

theorem psiNeg20_inv : psiNeg20⁻¹ = psiNeg20 := kroneckerChar_inv (-20)

theorem psiNeg20_neg_one : psiNeg20 (-1) = -1 := by
  rw [show (-1 : ZMod 20) = ((19 : ℕ) : ZMod 20) by decide, psiNeg20_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -5, conductor 20)"]
theorem isPrimitive_psiNeg20 : psiNeg20.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 20 = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨11, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((11 : ℤ) : ZMod 20) = ((11 : ℕ) : ZMod 20) by norm_cast, psiNeg20_natCast]; norm_num [chiD]⟩
  · exact ⟨13, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((13 : ℤ) : ZMod 20) = ((13 : ℕ) : ZMod 20) by norm_cast, psiNeg20_natCast]; norm_num [chiD]⟩

theorem psiNeg20_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 20, psiNeg20 (r : ZMod 20) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 + f 7 + f 9 - f 11 - f 13 - f 17 - f 19 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg20_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg5 :
    ∀ m : ℕ, (chiD (-5) m : ℂ) = DirichletCharacter.changeLevel (show 20 ∣ 4 * (-5 : ℤ).natAbs by decide)
      psiNeg20 (m : ZMod (4 * (-5 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-5 : ℤ).natAbs) < 20 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-5 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg20_natCast] <;> norm_num [chiD]

theorem psiNeg20_euler_neg5 (s : ℕ) :
    ∏ p ∈ (4 * (-5 : ℤ).natAbs).primeFactors, (1 - psiNeg20 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-5 : ℤ).natAbs).primeFactors = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg20_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 5$, odd $s$** ($D = -5$, $\psi = \left(\frac{-20}{\cdot}\right)$ modulo
$k_1 = 20$): $\zeta_{-5}(s)\,5^{s-1}\sqrt{5}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,5^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{20}\psi(r)B_s(r/20)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg5 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-5) s * (5 : ℝ) ^ (s - 1) * Real.sqrt 5 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 20) + (Polynomial.bernoulli s).eval (3 / 20)
        + (Polynomial.bernoulli s).eval (7 / 20) + (Polynomial.bernoulli s).eval (9 / 20)
        - (Polynomial.bernoulli s).eval (11 / 20) - (Polynomial.bernoulli s).eval (13 / 20)
        - (Polynomial.bernoulli s).eval (17 / 20) - (Polynomial.bernoulli s).eval (19 / 20)| *
        5 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -5) (by norm_num) isPrimitive_psiNeg20
    psiNeg20_inv _ chiD_eq_changeLevel_neg5 hs
    (by rw [psiNeg20_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg20_euler_neg5 s) (psiNeg20_sum _) 5 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 5$, $s = 3$** ($D = -5$): $\zeta_{-5}(3)\,5^{2}\sqrt{5}/\pi^{3} = 15/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 3)"]
theorem table6_5_3 : zetaD (-5) 3 * 5 ^ 2 * Real.sqrt 5 / π ^ 3 = 15 / 8 := by
  rw [show zetaD (-5) 3 * 5 ^ 2 * Real.sqrt 5 / π ^ 3 =
      zetaD (-5) ((3 : ℕ) : ℝ) * 5 ^ (3 - 1) * Real.sqrt 5 / π ^ 3 by norm_num,
    table6_row_neg5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 5$** ($D = -5$): $\zeta_{-5}(5)\,5^{4}\sqrt{5}/\pi^{5} = 587/128$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 5)"]
theorem table6_5_5 : zetaD (-5) 5 * 5 ^ 4 * Real.sqrt 5 / π ^ 5 = 587 / 128 := by
  rw [show zetaD (-5) 5 * 5 ^ 4 * Real.sqrt 5 / π ^ 5 =
      zetaD (-5) ((5 : ℕ) : ℝ) * 5 ^ (5 - 1) * Real.sqrt 5 / π ^ 5 by norm_num,
    table6_row_neg5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 7$** ($D = -5$): $\zeta_{-5}(7)\,5^{6}\sqrt{5}/\pi^{7} = 11851/1024$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 7)"]
theorem table6_5_7 : zetaD (-5) 7 * 5 ^ 6 * Real.sqrt 5 / π ^ 7 = 11851 / 1024 := by
  rw [show zetaD (-5) 7 * 5 ^ 6 * Real.sqrt 5 / π ^ 7 =
      zetaD (-5) ((7 : ℕ) : ℝ) * 5 ^ (7 - 1) * Real.sqrt 5 / π ^ 7 by norm_num,
    table6_row_neg5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 9$** ($D = -5$): $\zeta_{-5}(9)\,5^{8}\sqrt{5}/\pi^{9} = 100822507/3440640$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 5, s = 9)"]
theorem table6_5_9 : zetaD (-5) 9 * 5 ^ 8 * Real.sqrt 5 / π ^ 9 = 100822507 / 3440640 := by
  rw [show zetaD (-5) 9 * 5 ^ 8 * Real.sqrt 5 / π ^ 9 =
      zetaD (-5) ((9 : ℕ) : ℝ) * 5 ^ (9 - 1) * Real.sqrt 5 / π ^ 9 by norm_num,
    table6_row_neg5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 5$, $s = 11$** ($D = -5$): $\zeta_{-5}(11)\,5^{10}\sqrt{5}/\pi^{11} = 3677397901/49545216$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 5, s = 11)"]
theorem table6_5_11 : zetaD (-5) 11 * 5 ^ 10 * Real.sqrt 5 / π ^ 11 = 3677397901 / 49545216 := by
  rw [show zetaD (-5) 11 * 5 ^ 10 * Real.sqrt 5 / π ^ 11 =
      zetaD (-5) ((11 : ℕ) : ℝ) * 5 ^ (11 - 1) * Real.sqrt 5 / π ^ 11 by norm_num,
    table6_row_neg5 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 6$ -/

/-! #### The character $\left(\frac{24}{\cdot}\right)$ modulo $24$ -/

instance isQuadDisc_24 : IsQuadDisc 24 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (24 : ℤ) / 4 = 6 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 6$: the Kronecker character $\left(\frac{24}{\cdot}\right)$ modulo $24$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 6)"]
noncomputable def psi24 : DirichletCharacter ℂ 24 := kroneckerChar 24

theorem psi24_natCast (n : ℕ) : psi24 n = (chiD 6 n : ℂ) :=
  kroneckerChar_natCast_of_zero 24 (by norm_num) n

theorem psi24_inv : psi24⁻¹ = psi24 := kroneckerChar_inv 24

theorem psi24_neg_one : psi24 (-1) = 1 := by
  rw [show (-1 : ZMod 24) = ((23 : ℕ) : ZMod 24) by decide, psi24_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 6, conductor 24)"]
theorem isPrimitive_psi24 : psi24.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 24 = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨13, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((13 : ℤ) : ZMod 24) = ((13 : ℕ) : ZMod 24) by norm_cast, psi24_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 24) = ((17 : ℕ) : ZMod 24) by norm_cast, psi24_natCast]; norm_num [chiD]⟩

theorem psi24_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 24, psi24 (r : ZMod 24) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 5 - f 7 - f 11 - f 13 - f 17 + f 19 + f 23 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi24_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_6 :
    ∀ m : ℕ, (chiD 6 m : ℂ) = DirichletCharacter.changeLevel (show 24 ∣ 4 * (6 : ℤ).natAbs by decide)
      psi24 (m : ZMod (4 * (6 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (6 : ℤ).natAbs) < 24 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (6 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi24_natCast] <;> norm_num [chiD]

theorem psi24_euler_6 (s : ℕ) :
    ∏ p ∈ (4 * (6 : ℤ).natAbs).primeFactors, (1 - psi24 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (6 : ℤ).natAbs).primeFactors = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi24_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 6$, even $s$** ($D = 6$, $\psi = \left(\frac{24}{\cdot}\right)$ modulo
$k_1 = 24$): $\zeta_{6}(s)\,6^{s-1}\sqrt{6}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,6^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{24}\psi(r)B_s(r/24)$ (`zetaD_eq_abs`). -/
theorem table6_row_6 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 6 s * (6 : ℝ) ^ (s - 1) * Real.sqrt 6 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 24) + (Polynomial.bernoulli s).eval (5 / 24)
        - (Polynomial.bernoulli s).eval (7 / 24) - (Polynomial.bernoulli s).eval (11 / 24)
        - (Polynomial.bernoulli s).eval (13 / 24) - (Polynomial.bernoulli s).eval (17 / 24)
        + (Polynomial.bernoulli s).eval (19 / 24) + (Polynomial.bernoulli s).eval (23 / 24)| *
        6 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 6) (by norm_num) isPrimitive_psi24
    psi24_inv _ chiD_eq_changeLevel_6 hs
    (by rw [psi24_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi24_euler_6 s) (psi24_sum _) 6 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 6$, $s = 2$** ($D = 6$): $\zeta_{6}(2)\,6^{1}\sqrt{6}/\pi^{2} = 3/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 2)"]
theorem table6_6_2 : zetaD 6 2 * 6 ^ 1 * Real.sqrt 6 / π ^ 2 = 3 / 2 := by
  rw [show zetaD 6 2 * 6 ^ 1 * Real.sqrt 6 / π ^ 2 =
      zetaD 6 ((2 : ℕ) : ℝ) * 6 ^ (2 - 1) * Real.sqrt 6 / π ^ 2 by norm_num,
    table6_row_6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 4$** ($D = 6$): $\zeta_{6}(4)\,6^{3}\sqrt{6}/\pi^{4} = 87/16$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 4)"]
theorem table6_6_4 : zetaD 6 4 * 6 ^ 3 * Real.sqrt 6 / π ^ 4 = 87 / 16 := by
  rw [show zetaD 6 4 * 6 ^ 3 * Real.sqrt 6 / π ^ 4 =
      zetaD 6 ((4 : ℕ) : ℝ) * 6 ^ (4 - 1) * Real.sqrt 6 / π ^ 4 by norm_num,
    table6_row_6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 6$** ($D = 6$): $\zeta_{6}(6)\,6^{5}\sqrt{6}/\pi^{6} = 25361/1280$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 6)"]
theorem table6_6_6 : zetaD 6 6 * 6 ^ 5 * Real.sqrt 6 / π ^ 6 = 25361 / 1280 := by
  rw [show zetaD 6 6 * 6 ^ 5 * Real.sqrt 6 / π ^ 6 =
      zetaD 6 ((6 : ℕ) : ℝ) * 6 ^ (6 - 1) * Real.sqrt 6 / π ^ 6 by norm_num,
    table6_row_6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 8$** ($D = 6$): $\zeta_{6}(8)\,6^{7}\sqrt{6}/\pi^{8} = 15540167/215040$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 8)"]
theorem table6_6_8 : zetaD 6 8 * 6 ^ 7 * Real.sqrt 6 / π ^ 8 = 15540167 / 215040 := by
  rw [show zetaD 6 8 * 6 ^ 7 * Real.sqrt 6 / π ^ 8 =
      zetaD 6 ((8 : ℕ) : ℝ) * 6 ^ (8 - 1) * Real.sqrt 6 / π ^ 8 by norm_num,
    table6_row_6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 10$** ($D = 6$): $\zeta_{6}(10)\,6^{9}\sqrt{6}/\pi^{10} = 1813875289/6881280$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 6, s = 10)"]
theorem table6_6_10 : zetaD 6 10 * 6 ^ 9 * Real.sqrt 6 / π ^ 10 = 1813875289 / 6881280 := by
  rw [show zetaD 6 10 * 6 ^ 9 * Real.sqrt 6 / π ^ 10 =
      zetaD 6 ((10 : ℕ) : ℝ) * 6 ^ (10 - 1) * Real.sqrt 6 / π ^ 10 by norm_num,
    table6_row_6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 12$** ($D = 6$): $\zeta_{6}(12)\,6^{11}\sqrt{6}/\pi^{12} = 3742891901521/3892838400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 6, s = 12)"]
theorem table6_6_12 : zetaD 6 12 * 6 ^ 11 * Real.sqrt 6 / π ^ 12 = 3742891901521 / 3892838400 := by
  rw [show zetaD 6 12 * 6 ^ 11 * Real.sqrt 6 / π ^ 12 =
      zetaD 6 ((12 : ℕ) : ℝ) * 6 ^ (12 - 1) * Real.sqrt 6 / π ^ 12 by norm_num,
    table6_row_6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-24}{\cdot}\right)$ modulo $24$ -/

instance isQuadDisc_neg24 : IsQuadDisc (-24) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-24 : ℤ) / 4 = -6 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -6$: the Kronecker character $\left(\frac{-24}{\cdot}\right)$ modulo $24$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -6)"]
noncomputable def psiNeg24 : DirichletCharacter ℂ 24 := kroneckerChar (-24)

theorem psiNeg24_natCast (n : ℕ) : psiNeg24 n = (chiD (-6) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-24) (by norm_num) n

theorem psiNeg24_inv : psiNeg24⁻¹ = psiNeg24 := kroneckerChar_inv (-24)

theorem psiNeg24_neg_one : psiNeg24 (-1) = -1 := by
  rw [show (-1 : ZMod 24) = ((23 : ℕ) : ZMod 24) by decide, psiNeg24_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -6, conductor 24)"]
theorem isPrimitive_psiNeg24 : psiNeg24.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 24 = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨13, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((13 : ℤ) : ZMod 24) = ((13 : ℕ) : ZMod 24) by norm_cast, psiNeg24_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 24) = ((17 : ℕ) : ZMod 24) by norm_cast, psiNeg24_natCast]; norm_num [chiD]⟩

theorem psiNeg24_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 24, psiNeg24 (r : ZMod 24) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 5 + f 7 + f 11 - f 13 - f 17 - f 19 - f 23 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg24_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg6 :
    ∀ m : ℕ, (chiD (-6) m : ℂ) = DirichletCharacter.changeLevel (show 24 ∣ 4 * (-6 : ℤ).natAbs by decide)
      psiNeg24 (m : ZMod (4 * (-6 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-6 : ℤ).natAbs) < 24 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-6 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg24_natCast] <;> norm_num [chiD]

theorem psiNeg24_euler_neg6 (s : ℕ) :
    ∏ p ∈ (4 * (-6 : ℤ).natAbs).primeFactors, (1 - psiNeg24 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-6 : ℤ).natAbs).primeFactors = {2, 3} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg24_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 6$, odd $s$** ($D = -6$, $\psi = \left(\frac{-24}{\cdot}\right)$ modulo
$k_1 = 24$): $\zeta_{-6}(s)\,6^{s-1}\sqrt{6}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,6^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{24}\psi(r)B_s(r/24)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg6 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-6) s * (6 : ℝ) ^ (s - 1) * Real.sqrt 6 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 24) + (Polynomial.bernoulli s).eval (5 / 24)
        + (Polynomial.bernoulli s).eval (7 / 24) + (Polynomial.bernoulli s).eval (11 / 24)
        - (Polynomial.bernoulli s).eval (13 / 24) - (Polynomial.bernoulli s).eval (17 / 24)
        - (Polynomial.bernoulli s).eval (19 / 24) - (Polynomial.bernoulli s).eval (23 / 24)| *
        6 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -6) (by norm_num) isPrimitive_psiNeg24
    psiNeg24_inv _ chiD_eq_changeLevel_neg6 hs
    (by rw [psiNeg24_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg24_euler_neg6 s) (psiNeg24_sum _) 6 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 6$, $s = 3$** ($D = -6$): $\zeta_{-6}(3)\,6^{2}\sqrt{6}/\pi^{3} = 23/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 3)"]
theorem table6_6_3 : zetaD (-6) 3 * 6 ^ 2 * Real.sqrt 6 / π ^ 3 = 23 / 8 := by
  rw [show zetaD (-6) 3 * 6 ^ 2 * Real.sqrt 6 / π ^ 3 =
      zetaD (-6) ((3 : ℕ) : ℝ) * 6 ^ (3 - 1) * Real.sqrt 6 / π ^ 3 by norm_num,
    table6_row_neg6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 5$** ($D = -6$): $\zeta_{-6}(5)\,6^{4}\sqrt{6}/\pi^{5} = 3985/384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 5)"]
theorem table6_6_5 : zetaD (-6) 5 * 6 ^ 4 * Real.sqrt 6 / π ^ 5 = 3985 / 384 := by
  rw [show zetaD (-6) 5 * 6 ^ 4 * Real.sqrt 6 / π ^ 5 =
      zetaD (-6) ((5 : ℕ) : ℝ) * 6 ^ (5 - 1) * Real.sqrt 6 / π ^ 5 by norm_num,
    table6_row_neg6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 7$** ($D = -6$): $\zeta_{-6}(7)\,6^{6}\sqrt{6}/\pi^{7} = 1743623/46080$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 7)"]
theorem table6_6_7 : zetaD (-6) 7 * 6 ^ 6 * Real.sqrt 6 / π ^ 7 = 1743623 / 46080 := by
  rw [show zetaD (-6) 7 * 6 ^ 6 * Real.sqrt 6 / π ^ 7 =
      zetaD (-6) ((7 : ℕ) : ℝ) * 6 ^ (7 - 1) * Real.sqrt 6 / π ^ 7 by norm_num,
    table6_row_neg6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 9$** ($D = -6$): $\zeta_{-6}(9)\,6^{8}\sqrt{6}/\pi^{9} = 284922989/2064384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 6, s = 9)"]
theorem table6_6_9 : zetaD (-6) 9 * 6 ^ 8 * Real.sqrt 6 / π ^ 9 = 284922989 / 2064384 := by
  rw [show zetaD (-6) 9 * 6 ^ 8 * Real.sqrt 6 / π ^ 9 =
      zetaD (-6) ((9 : ℕ) : ℝ) * 6 ^ (9 - 1) * Real.sqrt 6 / π ^ 9 by norm_num,
    table6_row_neg6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 6$, $s = 11$** ($D = -6$): $\zeta_{-6}(11)\,6^{10}\sqrt{6}/\pi^{11} = 1870693029623/3715891200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 6, s = 11)"]
theorem table6_6_11 : zetaD (-6) 11 * 6 ^ 10 * Real.sqrt 6 / π ^ 11 = 1870693029623 / 3715891200 := by
  rw [show zetaD (-6) 11 * 6 ^ 10 * Real.sqrt 6 / π ^ 11 =
      zetaD (-6) ((11 : ℕ) : ℝ) * 6 ^ (11 - 1) * Real.sqrt 6 / π ^ 11 by norm_num,
    table6_row_neg6 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 7$ -/

/-! #### The character $\left(\frac{28}{\cdot}\right)$ modulo $28$ -/

instance isQuadDisc_28 : IsQuadDisc 28 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (28 : ℤ) / 4 = 7 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 7$: the Kronecker character $\left(\frac{28}{\cdot}\right)$ modulo $28$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 7)"]
noncomputable def psi28 : DirichletCharacter ℂ 28 := kroneckerChar 28

theorem psi28_natCast (n : ℕ) : psi28 n = (chiD 7 n : ℂ) :=
  kroneckerChar_natCast_of_zero 28 (by norm_num) n

theorem psi28_inv : psi28⁻¹ = psi28 := kroneckerChar_inv 28

theorem psi28_neg_one : psi28 (-1) = 1 := by
  rw [show (-1 : ZMod 28) = ((27 : ℕ) : ZMod 28) by decide, psi28_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 7, conductor 28)"]
theorem isPrimitive_psi28 : psi28.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 28 = {2, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨15, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((15 : ℤ) : ZMod 28) = ((15 : ℕ) : ZMod 28) by norm_cast, psi28_natCast]; norm_num [chiD]⟩
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 28) = ((5 : ℕ) : ZMod 28) by norm_cast, psi28_natCast]; norm_num [chiD]⟩

theorem psi28_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 28, psi28 (r : ZMod 28) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 - f 5 + f 9 - f 11 - f 13 - f 15 - f 17 + f 19 - f 23 + f 25 + f 27 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi28_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_7 :
    ∀ m : ℕ, (chiD 7 m : ℂ) = DirichletCharacter.changeLevel (show 28 ∣ 4 * (7 : ℤ).natAbs by decide)
      psi28 (m : ZMod (4 * (7 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (7 : ℤ).natAbs) < 28 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (7 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi28_natCast] <;> norm_num [chiD]

theorem psi28_euler_7 (s : ℕ) :
    ∏ p ∈ (4 * (7 : ℤ).natAbs).primeFactors, (1 - psi28 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (7 : ℤ).natAbs).primeFactors = {2, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi28_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 7$, even $s$** ($D = 7$, $\psi = \left(\frac{28}{\cdot}\right)$ modulo
$k_1 = 28$): $\zeta_{7}(s)\,7^{s-1}\sqrt{7}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,7^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{28}\psi(r)B_s(r/28)$ (`zetaD_eq_abs`). -/
theorem table6_row_7 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 7 s * (7 : ℝ) ^ (s - 1) * Real.sqrt 7 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 28) + (Polynomial.bernoulli s).eval (3 / 28)
        - (Polynomial.bernoulli s).eval (5 / 28) + (Polynomial.bernoulli s).eval (9 / 28)
        - (Polynomial.bernoulli s).eval (11 / 28) - (Polynomial.bernoulli s).eval (13 / 28)
        - (Polynomial.bernoulli s).eval (15 / 28) - (Polynomial.bernoulli s).eval (17 / 28)
        + (Polynomial.bernoulli s).eval (19 / 28) - (Polynomial.bernoulli s).eval (23 / 28)
        + (Polynomial.bernoulli s).eval (25 / 28) + (Polynomial.bernoulli s).eval (27 / 28)| *
        7 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 7) (by norm_num) isPrimitive_psi28
    psi28_inv _ chiD_eq_changeLevel_7 hs
    (by rw [psi28_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi28_euler_7 s) (psi28_sum _) 7 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 7$, $s = 2$** ($D = 7$): $\zeta_{7}(2)\,7^{1}\sqrt{7}/\pi^{2} = 2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 2)"]
theorem table6_7_2 : zetaD 7 2 * 7 ^ 1 * Real.sqrt 7 / π ^ 2 = 2 := by
  rw [show zetaD 7 2 * 7 ^ 1 * Real.sqrt 7 / π ^ 2 =
      zetaD 7 ((2 : ℕ) : ℝ) * 7 ^ (2 - 1) * Real.sqrt 7 / π ^ 2 by norm_num,
    table6_row_7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 4$** ($D = 7$): $\zeta_{7}(4)\,7^{3}\sqrt{7}/\pi^{4} = 113/12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 4)"]
theorem table6_7_4 : zetaD 7 4 * 7 ^ 3 * Real.sqrt 7 / π ^ 4 = 113 / 12 := by
  rw [show zetaD 7 4 * 7 ^ 3 * Real.sqrt 7 / π ^ 4 =
      zetaD 7 ((4 : ℕ) : ℝ) * 7 ^ (4 - 1) * Real.sqrt 7 / π ^ 4 by norm_num,
    table6_row_7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 6$** ($D = 7$): $\zeta_{7}(6)\,7^{5}\sqrt{7}/\pi^{6} = 44461/960$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 6)"]
theorem table6_7_6 : zetaD 7 6 * 7 ^ 5 * Real.sqrt 7 / π ^ 6 = 44461 / 960 := by
  rw [show zetaD 7 6 * 7 ^ 5 * Real.sqrt 7 / π ^ 6 =
      zetaD 7 ((6 : ℕ) : ℝ) * 7 ^ (6 - 1) * Real.sqrt 7 / π ^ 6 by norm_num,
    table6_row_7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 8$** ($D = 7$): $\zeta_{7}(8)\,7^{7}\sqrt{7}/\pi^{8} = 37040933/161280$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 8)"]
theorem table6_7_8 : zetaD 7 8 * 7 ^ 7 * Real.sqrt 7 / π ^ 8 = 37040933 / 161280 := by
  rw [show zetaD 7 8 * 7 ^ 7 * Real.sqrt 7 / π ^ 8 =
      zetaD 7 ((8 : ℕ) : ℝ) * 7 ^ (8 - 1) * Real.sqrt 7 / π ^ 8 by norm_num,
    table6_row_7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 10$** ($D = 7$): $\zeta_{7}(10)\,7^{9}\sqrt{7}/\pi^{10} = 52955730841/46448640$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 7, s = 10)"]
theorem table6_7_10 : zetaD 7 10 * 7 ^ 9 * Real.sqrt 7 / π ^ 10 = 52955730841 / 46448640 := by
  rw [show zetaD 7 10 * 7 ^ 9 * Real.sqrt 7 / π ^ 10 =
      zetaD 7 ((10 : ℕ) : ℝ) * 7 ^ (10 - 1) * Real.sqrt 7 / π ^ 10 by norm_num,
    table6_row_7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 12$** ($D = 7$): $\zeta_{7}(12)\,7^{11}\sqrt{7}/\pi^{12} = 115679254803353/20437401600$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 7, s = 12)"]
theorem table6_7_12 : zetaD 7 12 * 7 ^ 11 * Real.sqrt 7 / π ^ 12 = 115679254803353 / 20437401600 := by
  rw [show zetaD 7 12 * 7 ^ 11 * Real.sqrt 7 / π ^ 12 =
      zetaD 7 ((12 : ℕ) : ℝ) * 7 ^ (12 - 1) * Real.sqrt 7 / π ^ 12 by norm_num,
    table6_row_7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-7}{\cdot}\right)$ modulo $7$ -/

instance isQuadDisc_neg7 : IsQuadDisc (-7) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = -7$: the Kronecker character $\left(\frac{-7}{\cdot}\right)$ modulo $7$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -7)"]
noncomputable def psiNeg7 : DirichletCharacter ℂ 7 := kroneckerChar (-7)

theorem psiNeg7_natCast (n : ℕ) : psiNeg7 n = (jacobiSym n 7 : ℂ) :=
  kroneckerChar_natCast_of_one (-7) (by norm_num) n

theorem psiNeg7_inv : psiNeg7⁻¹ = psiNeg7 := kroneckerChar_inv (-7)

theorem psiNeg7_neg_one : psiNeg7 (-1) = -1 := by
  rw [show (-1 : ZMod 7) = ((6 : ℕ) : ZMod 7) by decide, psiNeg7_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -7, conductor 7)"]
theorem isPrimitive_psiNeg7 : psiNeg7.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 7 = {7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_singleton] at hp
  rcases hp with rfl
  · exact ⟨3, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((3 : ℤ) : ZMod 7) = ((3 : ℕ) : ZMod 7) by norm_cast, psiNeg7_natCast]; norm_num [chiD]⟩

theorem psiNeg7_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 7, psiNeg7 (r : ZMod 7) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 2 - f 3 + f 4 - f 5 - f 6 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg7_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg7 :
    ∀ m : ℕ, (chiD (-7) m : ℂ) = DirichletCharacter.changeLevel (show 7 ∣ 4 * (-7 : ℤ).natAbs by decide)
      psiNeg7 (m : ZMod (4 * (-7 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-7 : ℤ).natAbs) < 28 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-7 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg7_natCast] <;> norm_num [chiD]

theorem psiNeg7_euler_neg7 (s : ℕ) :
    ∏ p ∈ (4 * (-7 : ℤ).natAbs).primeFactors, (1 - psiNeg7 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-7 : ℤ).natAbs).primeFactors = {2, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg7_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 7$, odd $s$** ($D = -7$, $\psi = \left(\frac{-7}{\cdot}\right)$ modulo
$k_1 = 7$): $\zeta_{-7}(s)\,7^{s-1}\sqrt{7}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,7^{s-1}/(2\,s!)$ with
$E = (1 - 2^{-s})$ and $S = \sum_{r=1}^{7}\psi(r)B_s(r/7)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg7 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-7) s * (7 : ℝ) ^ (s - 1) * Real.sqrt 7 / π ^ s =
      ((|(1 - 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 7) + (Polynomial.bernoulli s).eval (2 / 7)
        - (Polynomial.bernoulli s).eval (3 / 7) + (Polynomial.bernoulli s).eval (4 / 7)
        - (Polynomial.bernoulli s).eval (5 / 7) - (Polynomial.bernoulli s).eval (6 / 7)| *
        7 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -7) (by norm_num) isPrimitive_psiNeg7
    psiNeg7_inv _ chiD_eq_changeLevel_neg7 hs
    (by rw [psiNeg7_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg7_euler_neg7 s) (psiNeg7_sum _) 7 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 7$, $s = 3$** ($D = -7$): $\zeta_{-7}(3)\,7^{2}\sqrt{7}/\pi^{3} = 4$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 3)"]
theorem table6_7_3 : zetaD (-7) 3 * 7 ^ 2 * Real.sqrt 7 / π ^ 3 = 4 := by
  rw [show zetaD (-7) 3 * 7 ^ 2 * Real.sqrt 7 / π ^ 3 =
      zetaD (-7) ((3 : ℕ) : ℝ) * 7 ^ (3 - 1) * Real.sqrt 7 / π ^ 3 by norm_num,
    table6_row_neg7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 5$** ($D = -7$): $\zeta_{-7}(5)\,7^{4}\sqrt{7}/\pi^{5} = 62/3$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 5)"]
theorem table6_7_5 : zetaD (-7) 5 * 7 ^ 4 * Real.sqrt 7 / π ^ 5 = 62 / 3 := by
  rw [show zetaD (-7) 5 * 7 ^ 4 * Real.sqrt 7 / π ^ 5 =
      zetaD (-7) ((5 : ℕ) : ℝ) * 7 ^ (5 - 1) * Real.sqrt 7 / π ^ 5 by norm_num,
    table6_row_neg7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 7$** ($D = -7$): $\zeta_{-7}(7)\,7^{6}\sqrt{7}/\pi^{7} = 9271/90$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 7)"]
theorem table6_7_7 : zetaD (-7) 7 * 7 ^ 6 * Real.sqrt 7 / π ^ 7 = 9271 / 90 := by
  rw [show zetaD (-7) 7 * 7 ^ 6 * Real.sqrt 7 / π ^ 7 =
      zetaD (-7) ((7 : ℕ) : ℝ) * 7 ^ (7 - 1) * Real.sqrt 7 / π ^ 7 by norm_num,
    table6_row_neg7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 9$** ($D = -7$): $\zeta_{-7}(9)\,7^{8}\sqrt{7}/\pi^{9} = 644663/1260$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 7, s = 9)"]
theorem table6_7_9 : zetaD (-7) 9 * 7 ^ 8 * Real.sqrt 7 / π ^ 9 = 644663 / 1260 := by
  rw [show zetaD (-7) 9 * 7 ^ 8 * Real.sqrt 7 / π ^ 9 =
      zetaD (-7) ((9 : ℕ) : ℝ) * 7 ^ (9 - 1) * Real.sqrt 7 / π ^ 9 by norm_num,
    table6_row_neg7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 7$, $s = 11$** ($D = -7$): $\zeta_{-7}(11)\,7^{10}\sqrt{7}/\pi^{11} = 1152262441/453600$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 7, s = 11)"]
theorem table6_7_11 : zetaD (-7) 11 * 7 ^ 10 * Real.sqrt 7 / π ^ 11 = 1152262441 / 453600 := by
  rw [show zetaD (-7) 11 * 7 ^ 10 * Real.sqrt 7 / π ^ 11 =
      zetaD (-7) ((11 : ℕ) : ℝ) * 7 ^ (11 - 1) * Real.sqrt 7 / π ^ 11 by norm_num,
    table6_row_neg7 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 10$ -/

/-! #### The character $\left(\frac{40}{\cdot}\right)$ modulo $40$ -/

instance isQuadDisc_40 : IsQuadDisc 40 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (40 : ℤ) / 4 = 10 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 10$: the Kronecker character $\left(\frac{40}{\cdot}\right)$ modulo $40$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 10)"]
noncomputable def psi40 : DirichletCharacter ℂ 40 := kroneckerChar 40

theorem psi40_natCast (n : ℕ) : psi40 n = (chiD 10 n : ℂ) :=
  kroneckerChar_natCast_of_zero 40 (by norm_num) n

theorem psi40_inv : psi40⁻¹ = psi40 := kroneckerChar_inv 40

theorem psi40_neg_one : psi40 (-1) = 1 := by
  rw [show (-1 : ZMod 40) = ((39 : ℕ) : ZMod 40) by decide, psi40_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 10, conductor 40)"]
theorem isPrimitive_psi40 : psi40.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 40 = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨21, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((21 : ℤ) : ZMod 40) = ((21 : ℕ) : ZMod 40) by norm_cast, psi40_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 40) = ((17 : ℕ) : ZMod 40) by norm_cast, psi40_natCast]; norm_num [chiD]⟩

theorem psi40_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 40, psi40 (r : ZMod 40) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 - f 7 + f 9 - f 11 + f 13 - f 17 - f 19 - f 21 - f 23 + f 27 - f 29 + f 31 - f 33
      + f 37 + f 39 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi40_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_10 :
    ∀ m : ℕ, (chiD 10 m : ℂ) = DirichletCharacter.changeLevel (show 40 ∣ 4 * (10 : ℤ).natAbs by decide)
      psi40 (m : ZMod (4 * (10 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (10 : ℤ).natAbs) < 40 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (10 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi40_natCast] <;> norm_num [chiD]

theorem psi40_euler_10 (s : ℕ) :
    ∏ p ∈ (4 * (10 : ℤ).natAbs).primeFactors, (1 - psi40 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (10 : ℤ).natAbs).primeFactors = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi40_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 10$, even $s$** ($D = 10$, $\psi = \left(\frac{40}{\cdot}\right)$ modulo
$k_1 = 40$): $\zeta_{10}(s)\,10^{s-1}\sqrt{10}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,10^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{40}\psi(r)B_s(r/40)$ (`zetaD_eq_abs`). -/
theorem table6_row_10 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 10 s * (10 : ℝ) ^ (s - 1) * Real.sqrt 10 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 40) + (Polynomial.bernoulli s).eval (3 / 40)
        - (Polynomial.bernoulli s).eval (7 / 40) + (Polynomial.bernoulli s).eval (9 / 40)
        - (Polynomial.bernoulli s).eval (11 / 40) + (Polynomial.bernoulli s).eval (13 / 40)
        - (Polynomial.bernoulli s).eval (17 / 40) - (Polynomial.bernoulli s).eval (19 / 40)
        - (Polynomial.bernoulli s).eval (21 / 40) - (Polynomial.bernoulli s).eval (23 / 40)
        + (Polynomial.bernoulli s).eval (27 / 40) - (Polynomial.bernoulli s).eval (29 / 40)
        + (Polynomial.bernoulli s).eval (31 / 40) - (Polynomial.bernoulli s).eval (33 / 40)
        + (Polynomial.bernoulli s).eval (37 / 40) + (Polynomial.bernoulli s).eval (39 / 40)| *
        10 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 10) (by norm_num) isPrimitive_psi40
    psi40_inv _ chiD_eq_changeLevel_10 hs
    (by rw [psi40_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi40_euler_10 s) (psi40_sum _) 10 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 10$, $s = 2$** ($D = 10$): $\zeta_{10}(2)\,10^{1}\sqrt{10}/\pi^{2} = 7/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 2)"]
theorem table6_10_2 : zetaD 10 2 * 10 ^ 1 * Real.sqrt 10 / π ^ 2 = 7 / 2 := by
  rw [show zetaD 10 2 * 10 ^ 1 * Real.sqrt 10 / π ^ 2 =
      zetaD 10 ((2 : ℕ) : ℝ) * 10 ^ (2 - 1) * Real.sqrt 10 / π ^ 2 by norm_num,
    table6_row_10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 4$** ($D = 10$): $\zeta_{10}(4)\,10^{3}\sqrt{10}/\pi^{4} = 1577/48$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 4)"]
theorem table6_10_4 : zetaD 10 4 * 10 ^ 3 * Real.sqrt 10 / π ^ 4 = 1577 / 48 := by
  rw [show zetaD 10 4 * 10 ^ 3 * Real.sqrt 10 / π ^ 4 =
      zetaD 10 ((4 : ℕ) : ℝ) * 10 ^ (4 - 1) * Real.sqrt 10 / π ^ 4 by norm_num,
    table6_row_10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 6$** ($D = 10$): $\zeta_{10}(6)\,10^{5}\sqrt{10}/\pi^{6} = 1264807/3840$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 6)"]
theorem table6_10_6 : zetaD 10 6 * 10 ^ 5 * Real.sqrt 10 / π ^ 6 = 1264807 / 3840 := by
  rw [show zetaD 10 6 * 10 ^ 5 * Real.sqrt 10 / π ^ 6 =
      zetaD 10 ((6 : ℕ) : ℝ) * 10 ^ (6 - 1) * Real.sqrt 10 / π ^ 6 by norm_num,
    table6_row_10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 8$** ($D = 10$): $\zeta_{10}(8)\,10^{7}\sqrt{10}/\pi^{8} = 307191791/92160$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 8)"]
theorem table6_10_8 : zetaD 10 8 * 10 ^ 7 * Real.sqrt 10 / π ^ 8 = 307191791 / 92160 := by
  rw [show zetaD 10 8 * 10 ^ 7 * Real.sqrt 10 / π ^ 8 =
      zetaD 10 ((8 : ℕ) : ℝ) * 10 ^ (8 - 1) * Real.sqrt 10 / π ^ 8 by norm_num,
    table6_row_10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 10$** ($D = 10$): $\zeta_{10}(10)\,10^{9}\sqrt{10}/\pi^{10} = 6273958190407/185794560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 10, s = 10)"]
theorem table6_10_10 : zetaD 10 10 * 10 ^ 9 * Real.sqrt 10 / π ^ 10 = 6273958190407 / 185794560 := by
  rw [show zetaD 10 10 * 10 ^ 9 * Real.sqrt 10 / π ^ 10 =
      zetaD 10 ((10 : ℕ) : ℝ) * 10 ^ (10 - 1) * Real.sqrt 10 / π ^ 10 by norm_num,
    table6_row_10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 12$** ($D = 10$): $\zeta_{10}(12)\,10^{11}\sqrt{10}/\pi^{12} = 27969713330033897/81749606400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 10, s = 12)"]
theorem table6_10_12 : zetaD 10 12 * 10 ^ 11 * Real.sqrt 10 / π ^ 12 = 27969713330033897 / 81749606400 := by
  rw [show zetaD 10 12 * 10 ^ 11 * Real.sqrt 10 / π ^ 12 =
      zetaD 10 ((12 : ℕ) : ℝ) * 10 ^ (12 - 1) * Real.sqrt 10 / π ^ 12 by norm_num,
    table6_row_10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-40}{\cdot}\right)$ modulo $40$ -/

instance isQuadDisc_neg40 : IsQuadDisc (-40) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-40 : ℤ) / 4 = -10 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -10$: the Kronecker character $\left(\frac{-40}{\cdot}\right)$ modulo $40$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -10)"]
noncomputable def psiNeg40 : DirichletCharacter ℂ 40 := kroneckerChar (-40)

theorem psiNeg40_natCast (n : ℕ) : psiNeg40 n = (chiD (-10) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-40) (by norm_num) n

theorem psiNeg40_inv : psiNeg40⁻¹ = psiNeg40 := kroneckerChar_inv (-40)

theorem psiNeg40_neg_one : psiNeg40 (-1) = -1 := by
  rw [show (-1 : ZMod 40) = ((39 : ℕ) : ZMod 40) by decide, psiNeg40_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -10, conductor 40)"]
theorem isPrimitive_psiNeg40 : psiNeg40.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 40 = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨21, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((21 : ℤ) : ZMod 40) = ((21 : ℕ) : ZMod 40) by norm_cast, psiNeg40_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 40) = ((17 : ℕ) : ZMod 40) by norm_cast, psiNeg40_natCast]; norm_num [chiD]⟩

theorem psiNeg40_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 40, psiNeg40 (r : ZMod 40) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 + f 7 + f 9 + f 11 + f 13 - f 17 + f 19 - f 21 + f 23 - f 27 - f 29 - f 31 - f 33
      + f 37 - f 39 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg40_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg10 :
    ∀ m : ℕ, (chiD (-10) m : ℂ) = DirichletCharacter.changeLevel (show 40 ∣ 4 * (-10 : ℤ).natAbs by decide)
      psiNeg40 (m : ZMod (4 * (-10 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-10 : ℤ).natAbs) < 40 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-10 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg40_natCast] <;> norm_num [chiD]

theorem psiNeg40_euler_neg10 (s : ℕ) :
    ∏ p ∈ (4 * (-10 : ℤ).natAbs).primeFactors, (1 - psiNeg40 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-10 : ℤ).natAbs).primeFactors = {2, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg40_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 10$, odd $s$** ($D = -10$, $\psi = \left(\frac{-40}{\cdot}\right)$ modulo
$k_1 = 40$): $\zeta_{-10}(s)\,10^{s-1}\sqrt{10}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,10^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{40}\psi(r)B_s(r/40)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg10 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-10) s * (10 : ℝ) ^ (s - 1) * Real.sqrt 10 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 40) - (Polynomial.bernoulli s).eval (3 / 40)
        + (Polynomial.bernoulli s).eval (7 / 40) + (Polynomial.bernoulli s).eval (9 / 40)
        + (Polynomial.bernoulli s).eval (11 / 40) + (Polynomial.bernoulli s).eval (13 / 40)
        - (Polynomial.bernoulli s).eval (17 / 40) + (Polynomial.bernoulli s).eval (19 / 40)
        - (Polynomial.bernoulli s).eval (21 / 40) + (Polynomial.bernoulli s).eval (23 / 40)
        - (Polynomial.bernoulli s).eval (27 / 40) - (Polynomial.bernoulli s).eval (29 / 40)
        - (Polynomial.bernoulli s).eval (31 / 40) - (Polynomial.bernoulli s).eval (33 / 40)
        + (Polynomial.bernoulli s).eval (37 / 40) - (Polynomial.bernoulli s).eval (39 / 40)| *
        10 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -10) (by norm_num) isPrimitive_psiNeg40
    psiNeg40_inv _ chiD_eq_changeLevel_neg10 hs
    (by rw [psiNeg40_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg40_euler_neg10 s) (psiNeg40_sum _) 10 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 10$, $s = 3$** ($D = -10$): $\zeta_{-10}(3)\,10^{2}\sqrt{10}/\pi^{3} = 79/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 3)"]
theorem table6_10_3 : zetaD (-10) 3 * 10 ^ 2 * Real.sqrt 10 / π ^ 3 = 79 / 8 := by
  rw [show zetaD (-10) 3 * 10 ^ 2 * Real.sqrt 10 / π ^ 3 =
      zetaD (-10) ((3 : ℕ) : ℝ) * 10 ^ (3 - 1) * Real.sqrt 10 / π ^ 3 by norm_num,
    table6_row_neg10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 5$** ($D = -10$): $\zeta_{-10}(5)\,10^{4}\sqrt{10}/\pi^{5} = 39521/384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 5)"]
theorem table6_10_5 : zetaD (-10) 5 * 10 ^ 4 * Real.sqrt 10 / π ^ 5 = 39521 / 384 := by
  rw [show zetaD (-10) 5 * 10 ^ 4 * Real.sqrt 10 / π ^ 5 =
      zetaD (-10) ((5 : ℕ) : ℝ) * 10 ^ (5 - 1) * Real.sqrt 10 / π ^ 5 by norm_num,
    table6_row_neg10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 7$** ($D = -10$): $\zeta_{-10}(7)\,10^{6}\sqrt{10}/\pi^{7} = 48224239/46080$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 7)"]
theorem table6_10_7 : zetaD (-10) 7 * 10 ^ 6 * Real.sqrt 10 / π ^ 7 = 48224239 / 46080 := by
  rw [show zetaD (-10) 7 * 10 ^ 6 * Real.sqrt 10 / π ^ 7 =
      zetaD (-10) ((7 : ℕ) : ℝ) * 10 ^ (7 - 1) * Real.sqrt 10 / π ^ 7 by norm_num,
    table6_row_neg10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 9$** ($D = -10$): $\zeta_{-10}(9)\,10^{8}\sqrt{10}/\pi^{9} = 109493813441/10321920$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 10, s = 9)"]
theorem table6_10_9 : zetaD (-10) 9 * 10 ^ 8 * Real.sqrt 10 / π ^ 9 = 109493813441 / 10321920 := by
  rw [show zetaD (-10) 9 * 10 ^ 8 * Real.sqrt 10 / π ^ 9 =
      zetaD (-10) ((9 : ℕ) : ℝ) * 10 ^ (9 - 1) * Real.sqrt 10 / π ^ 9 by norm_num,
    table6_row_neg10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 10$, $s = 11$** ($D = -10$): $\zeta_{-10}(11)\,10^{10}\sqrt{10}/\pi^{11} = 399403566400399/3715891200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 10, s = 11)"]
theorem table6_10_11 : zetaD (-10) 11 * 10 ^ 10 * Real.sqrt 10 / π ^ 11 = 399403566400399 / 3715891200 := by
  rw [show zetaD (-10) 11 * 10 ^ 10 * Real.sqrt 10 / π ^ 11 =
      zetaD (-10) ((11 : ℕ) : ℝ) * 10 ^ (11 - 1) * Real.sqrt 10 / π ^ 11 by norm_num,
    table6_row_neg10 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 11$ -/

/-! #### The character $\left(\frac{44}{\cdot}\right)$ modulo $44$ -/

instance isQuadDisc_44 : IsQuadDisc 44 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (44 : ℤ) / 4 = 11 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 11$: the Kronecker character $\left(\frac{44}{\cdot}\right)$ modulo $44$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 11)"]
noncomputable def psi44 : DirichletCharacter ℂ 44 := kroneckerChar 44

theorem psi44_natCast (n : ℕ) : psi44 n = (chiD 11 n : ℂ) :=
  kroneckerChar_natCast_of_zero 44 (by norm_num) n

theorem psi44_inv : psi44⁻¹ = psi44 := kroneckerChar_inv 44

theorem psi44_neg_one : psi44 (-1) = 1 := by
  rw [show (-1 : ZMod 44) = ((43 : ℕ) : ZMod 44) by decide, psi44_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 11, conductor 44)"]
theorem isPrimitive_psi44 : psi44.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 44 = {2, 11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨23, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((23 : ℤ) : ZMod 44) = ((23 : ℕ) : ZMod 44) by norm_cast, psi44_natCast]; norm_num [chiD]⟩
  · exact ⟨13, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((13 : ℤ) : ZMod 44) = ((13 : ℕ) : ZMod 44) by norm_cast, psi44_natCast]; norm_num [chiD]⟩

theorem psi44_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 44, psi44 (r : ZMod 44) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 + f 5 + f 7 + f 9 - f 13 - f 15 - f 17 + f 19 - f 21 - f 23 + f 25 - f 27 - f 29
      - f 31 + f 35 + f 37 + f 39 - f 41 + f 43 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi44_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_11 :
    ∀ m : ℕ, (chiD 11 m : ℂ) = DirichletCharacter.changeLevel (show 44 ∣ 4 * (11 : ℤ).natAbs by decide)
      psi44 (m : ZMod (4 * (11 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (11 : ℤ).natAbs) < 44 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (11 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi44_natCast] <;> norm_num [chiD]

theorem psi44_euler_11 (s : ℕ) :
    ∏ p ∈ (4 * (11 : ℤ).natAbs).primeFactors, (1 - psi44 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (11 : ℤ).natAbs).primeFactors = {2, 11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi44_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 11$, even $s$** ($D = 11$, $\psi = \left(\frac{44}{\cdot}\right)$ modulo
$k_1 = 44$): $\zeta_{11}(s)\,11^{s-1}\sqrt{11}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,11^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{44}\psi(r)B_s(r/44)$ (`zetaD_eq_abs`). -/
theorem table6_row_11 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 11 s * (11 : ℝ) ^ (s - 1) * Real.sqrt 11 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 44) - (Polynomial.bernoulli s).eval (3 / 44)
        + (Polynomial.bernoulli s).eval (5 / 44) + (Polynomial.bernoulli s).eval (7 / 44)
        + (Polynomial.bernoulli s).eval (9 / 44) - (Polynomial.bernoulli s).eval (13 / 44)
        - (Polynomial.bernoulli s).eval (15 / 44) - (Polynomial.bernoulli s).eval (17 / 44)
        + (Polynomial.bernoulli s).eval (19 / 44) - (Polynomial.bernoulli s).eval (21 / 44)
        - (Polynomial.bernoulli s).eval (23 / 44) + (Polynomial.bernoulli s).eval (25 / 44)
        - (Polynomial.bernoulli s).eval (27 / 44) - (Polynomial.bernoulli s).eval (29 / 44)
        - (Polynomial.bernoulli s).eval (31 / 44) + (Polynomial.bernoulli s).eval (35 / 44)
        + (Polynomial.bernoulli s).eval (37 / 44) + (Polynomial.bernoulli s).eval (39 / 44)
        - (Polynomial.bernoulli s).eval (41 / 44) + (Polynomial.bernoulli s).eval (43 / 44)| *
        11 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 11) (by norm_num) isPrimitive_psi44
    psi44_inv _ chiD_eq_changeLevel_11 hs
    (by rw [psi44_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi44_euler_11 s) (psi44_sum _) 11 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 11$, $s = 2$** ($D = 11$): $\zeta_{11}(2)\,11^{1}\sqrt{11}/\pi^{2} = 7/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 2)"]
theorem table6_11_2 : zetaD 11 2 * 11 ^ 1 * Real.sqrt 11 / π ^ 2 = 7 / 2 := by
  rw [show zetaD 11 2 * 11 ^ 1 * Real.sqrt 11 / π ^ 2 =
      zetaD 11 ((2 : ℕ) : ℝ) * 11 ^ (2 - 1) * Real.sqrt 11 / π ^ 2 by norm_num,
    table6_row_11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 4$** ($D = 11$): $\zeta_{11}(4)\,11^{3}\sqrt{11}/\pi^{4} = 2153/48$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 4)"]
theorem table6_11_4 : zetaD 11 4 * 11 ^ 3 * Real.sqrt 11 / π ^ 4 = 2153 / 48 := by
  rw [show zetaD 11 4 * 11 ^ 3 * Real.sqrt 11 / π ^ 4 =
      zetaD 11 ((4 : ℕ) : ℝ) * 11 ^ (4 - 1) * Real.sqrt 11 / π ^ 4 by norm_num,
    table6_row_11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 6$** ($D = 11$): $\zeta_{11}(6)\,11^{5}\sqrt{11}/\pi^{6} = 2130727/3840$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 6)"]
theorem table6_11_6 : zetaD 11 6 * 11 ^ 5 * Real.sqrt 11 / π ^ 6 = 2130727 / 3840 := by
  rw [show zetaD 11 6 * 11 ^ 5 * Real.sqrt 11 / π ^ 6 =
      zetaD 11 ((6 : ℕ) : ℝ) * 11 ^ (6 - 1) * Real.sqrt 11 / π ^ 6 by norm_num,
    table6_row_11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 8$** ($D = 11$): $\zeta_{11}(8)\,11^{7}\sqrt{11}/\pi^{8} = 627658799/92160$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 8)"]
theorem table6_11_8 : zetaD 11 8 * 11 ^ 7 * Real.sqrt 11 / π ^ 8 = 627658799 / 92160 := by
  rw [show zetaD 11 8 * 11 ^ 7 * Real.sqrt 11 / π ^ 8 =
      zetaD 11 ((8 : ℕ) : ℝ) * 11 ^ (8 - 1) * Real.sqrt 11 / π ^ 8 by norm_num,
    table6_row_11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 10$** ($D = 11$): $\zeta_{11}(10)\,11^{9}\sqrt{11}/\pi^{10} = 15515203176007/185794560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 11, s = 10)"]
theorem table6_11_10 : zetaD 11 10 * 11 ^ 9 * Real.sqrt 11 / π ^ 10 = 15515203176007 / 185794560 := by
  rw [show zetaD 11 10 * 11 ^ 9 * Real.sqrt 11 / π ^ 10 =
      zetaD 11 ((10 : ℕ) : ℝ) * 11 ^ (10 - 1) * Real.sqrt 11 / π ^ 10 by norm_num,
    table6_row_11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 12$** ($D = 11$): $\zeta_{11}(12)\,11^{11}\sqrt{11}/\pi^{12} = 83695529627822633/81749606400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 11, s = 12)"]
theorem table6_11_12 : zetaD 11 12 * 11 ^ 11 * Real.sqrt 11 / π ^ 12 = 83695529627822633 / 81749606400 := by
  rw [show zetaD 11 12 * 11 ^ 11 * Real.sqrt 11 / π ^ 12 =
      zetaD 11 ((12 : ℕ) : ℝ) * 11 ^ (12 - 1) * Real.sqrt 11 / π ^ 12 by norm_num,
    table6_row_11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-11}{\cdot}\right)$ modulo $11$ -/

instance isQuadDisc_neg11 : IsQuadDisc (-11) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = -11$: the Kronecker character $\left(\frac{-11}{\cdot}\right)$ modulo $11$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -11)"]
noncomputable def psiNeg11 : DirichletCharacter ℂ 11 := kroneckerChar (-11)

theorem psiNeg11_natCast (n : ℕ) : psiNeg11 n = (jacobiSym n 11 : ℂ) :=
  kroneckerChar_natCast_of_one (-11) (by norm_num) n

theorem psiNeg11_inv : psiNeg11⁻¹ = psiNeg11 := kroneckerChar_inv (-11)

theorem psiNeg11_neg_one : psiNeg11 (-1) = -1 := by
  rw [show (-1 : ZMod 11) = ((10 : ℕ) : ZMod 11) by decide, psiNeg11_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -11, conductor 11)"]
theorem isPrimitive_psiNeg11 : psiNeg11.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 11 = {11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_singleton] at hp
  rcases hp with rfl
  · exact ⟨2, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((2 : ℤ) : ZMod 11) = ((2 : ℕ) : ZMod 11) by norm_cast, psiNeg11_natCast]; norm_num [chiD]⟩

theorem psiNeg11_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 11, psiNeg11 (r : ZMod 11) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 2 + f 3 + f 4 + f 5 - f 6 - f 7 - f 8 + f 9 - f 10 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg11_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg11 :
    ∀ m : ℕ, (chiD (-11) m : ℂ) = DirichletCharacter.changeLevel (show 11 ∣ 4 * (-11 : ℤ).natAbs by decide)
      psiNeg11 (m : ZMod (4 * (-11 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-11 : ℤ).natAbs) < 44 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-11 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg11_natCast] <;> norm_num [chiD]

theorem psiNeg11_euler_neg11 (s : ℕ) :
    ∏ p ∈ (4 * (-11 : ℤ).natAbs).primeFactors, (1 - psiNeg11 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 + 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-11 : ℤ).natAbs).primeFactors = {2, 11} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg11_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 11$, odd $s$** ($D = -11$, $\psi = \left(\frac{-11}{\cdot}\right)$ modulo
$k_1 = 11$): $\zeta_{-11}(s)\,11^{s-1}\sqrt{11}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,11^{s-1}/(2\,s!)$ with
$E = (1 + 2^{-s})$ and $S = \sum_{r=1}^{11}\psi(r)B_s(r/11)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg11 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-11) s * (11 : ℝ) ^ (s - 1) * Real.sqrt 11 / π ^ s =
      ((|(1 + 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 11) - (Polynomial.bernoulli s).eval (2 / 11)
        + (Polynomial.bernoulli s).eval (3 / 11) + (Polynomial.bernoulli s).eval (4 / 11)
        + (Polynomial.bernoulli s).eval (5 / 11) - (Polynomial.bernoulli s).eval (6 / 11)
        - (Polynomial.bernoulli s).eval (7 / 11) - (Polynomial.bernoulli s).eval (8 / 11)
        + (Polynomial.bernoulli s).eval (9 / 11) - (Polynomial.bernoulli s).eval (10 / 11)| *
        11 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -11) (by norm_num) isPrimitive_psiNeg11
    psiNeg11_inv _ chiD_eq_changeLevel_neg11 hs
    (by rw [psiNeg11_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg11_euler_neg11 s) (psiNeg11_sum _) 11 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 11$, $s = 3$** ($D = -11$): $\zeta_{-11}(3)\,11^{2}\sqrt{11}/\pi^{3} = 27/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 3)"]
theorem table6_11_3 : zetaD (-11) 3 * 11 ^ 2 * Real.sqrt 11 / π ^ 3 = 27 / 2 := by
  rw [show zetaD (-11) 3 * 11 ^ 2 * Real.sqrt 11 / π ^ 3 =
      zetaD (-11) ((3 : ℕ) : ℝ) * 11 ^ (3 - 1) * Real.sqrt 11 / π ^ 3 by norm_num,
    table6_row_neg11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 5$** ($D = -11$): $\zeta_{-11}(5)\,11^{4}\sqrt{11}/\pi^{5} = 1275/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 5)"]
theorem table6_11_5 : zetaD (-11) 5 * 11 ^ 4 * Real.sqrt 11 / π ^ 5 = 1275 / 8 := by
  rw [show zetaD (-11) 5 * 11 ^ 4 * Real.sqrt 11 / π ^ 5 =
      zetaD (-11) ((5 : ℕ) : ℝ) * 11 ^ (5 - 1) * Real.sqrt 11 / π ^ 5 by norm_num,
    table6_row_neg11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 7$** ($D = -11$): $\zeta_{-11}(7)\,11^{6}\sqrt{11}/\pi^{7} = 155703/80$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 7)"]
theorem table6_11_7 : zetaD (-11) 7 * 11 ^ 6 * Real.sqrt 11 / π ^ 7 = 155703 / 80 := by
  rw [show zetaD (-11) 7 * 11 ^ 6 * Real.sqrt 11 / π ^ 7 =
      zetaD (-11) ((7 : ℕ) : ℝ) * 11 ^ (7 - 1) * Real.sqrt 11 / π ^ 7 by norm_num,
    table6_row_neg11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 9$** ($D = -11$): $\zeta_{-11}(9)\,11^{8}\sqrt{11}/\pi^{9} = 21370725/896$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 11, s = 9)"]
theorem table6_11_9 : zetaD (-11) 9 * 11 ^ 8 * Real.sqrt 11 / π ^ 9 = 21370725 / 896 := by
  rw [show zetaD (-11) 9 * 11 ^ 8 * Real.sqrt 11 / π ^ 9 =
      zetaD (-11) ((9 : ℕ) : ℝ) * 11 ^ (9 - 1) * Real.sqrt 11 / π ^ 9 by norm_num,
    table6_row_neg11 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 11$, $s = 11$** ($D = -11$): $\zeta_{-11}(11)\,11^{10}\sqrt{11}/\pi^{11} = 117895594903/403200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 11, s = 11)"]
theorem table6_11_11 : zetaD (-11) 11 * 11 ^ 10 * Real.sqrt 11 / π ^ 11 = 117895594903 / 403200 := by
  rw [show zetaD (-11) 11 * 11 ^ 10 * Real.sqrt 11 / π ^ 11 =
      zetaD (-11) ((11 : ℕ) : ℝ) * 11 ^ (11 - 1) * Real.sqrt 11 / π ^ 11 by norm_num,
    table6_row_neg11 (by norm_num) (by norm_num)]
  bernoulli_eval

end QuadFormsKB.ConwaySloane.Mass
