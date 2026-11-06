/-
# Conway–Sloane 1988, §8, Table 6: the rows $d = 13, 14, 15, 17, 19$ for $s \ge 2$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, Table 6, pp. 270–271.

Table 6 lists the rational numbers $\zeta_D(s)\,d^{s-1}\sqrt d/\pi^s$, $D = (-1)^s d$. This file proves the entries
$2 \le s \le 12$ of the rows $d = 13, 14, 15, 17, 19$
from `zetaD_eq_abs` (the closed formula (13) with the Gauss sum eliminated by the positivity of $\zeta_D$,
`Table6Abs.lean`). The entries $s = 1$ need class numbers and are not treated here.

**Characters (book $\to$ Lean).** For each $D$ the primitive character $\psi$ of (13) is the Kronecker character
$\left(\frac{\Delta}{\cdot}\right)$ (`Binary.kroneckerChar Δ`) of the fundamental discriminant $\Delta$ of
$\mathbb Q(\sqrt D)$, a character modulo $k_1 = \lvert\Delta\rvert$ (Table 4):

| $d$ | $D$ (even $s$) | $\Delta$ | $k_1$ | $\psi$ | $D$ (odd $s$) | $\Delta$ | $k_1$ | $\psi$ |
|---|---|---|---|---|---|---|---|---|
| $13$ | $13$ | $13$ | $13$ | `psi13` | $-13$ | $-52$ | $52$ | `psiNeg52` |
| $14$ | $14$ | $56$ | $56$ | `psi56` | $-14$ | $-56$ | $56$ | `psiNeg56` |
| $15$ | $15$ | $60$ | $60$ | `psi60` | $-15$ | $-15$ | $15$ | `psiNeg15` |
| $17$ | $17$ | $17$ | $17$ | `psi17` | $-17$ | $-68$ | $68$ | `psiNeg68` |
| $19$ | $19$ | $76$ | $76$ | `psi76` | $-19$ | $-19$ | $19$ | `psiNeg19` |

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

/-! ### Row $d = 13$ -/

/-! #### The character $\left(\frac{13}{\cdot}\right)$ modulo $13$ -/

instance isQuadDisc_13 : IsQuadDisc 13 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = 13$: the Kronecker character $\left(\frac{13}{\cdot}\right)$ modulo $13$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 13)"]
noncomputable def psi13 : DirichletCharacter ℂ 13 := kroneckerChar 13

theorem psi13_natCast (n : ℕ) : psi13 n = (jacobiSym n 13 : ℂ) :=
  kroneckerChar_natCast_of_one 13 (by norm_num) n

theorem psi13_inv : psi13⁻¹ = psi13 := kroneckerChar_inv 13

theorem psi13_neg_one : psi13 (-1) = 1 := by
  rw [show (-1 : ZMod 13) = ((12 : ℕ) : ZMod 13) by decide, psi13_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 13, conductor 13)"]
theorem isPrimitive_psi13 : psi13.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 13 = {13} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_singleton] at hp
  rcases hp with rfl
  · exact ⟨2, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((2 : ℤ) : ZMod 13) = ((2 : ℕ) : ZMod 13) by norm_cast, psi13_natCast]; norm_num [chiD]⟩

theorem psi13_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 13, psi13 (r : ZMod 13) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 2 + f 3 + f 4 - f 5 - f 6 - f 7 - f 8 + f 9 + f 10 - f 11 + f 12 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi13_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_13 :
    ∀ m : ℕ, (chiD 13 m : ℂ) = DirichletCharacter.changeLevel (show 13 ∣ 4 * (13 : ℤ).natAbs by decide)
      psi13 (m : ZMod (4 * (13 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (13 : ℤ).natAbs) < 52 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (13 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi13_natCast] <;> norm_num [chiD]

theorem psi13_euler_13 (s : ℕ) :
    ∏ p ∈ (4 * (13 : ℤ).natAbs).primeFactors, (1 - psi13 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 + 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (13 : ℤ).natAbs).primeFactors = {2, 13} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi13_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 13$, even $s$** ($D = 13$, $\psi = \left(\frac{13}{\cdot}\right)$ modulo
$k_1 = 13$): $\zeta_{13}(s)\,13^{s-1}\sqrt{13}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,13^{s-1}/(2\,s!)$ with
$E = (1 + 2^{-s})$ and $S = \sum_{r=1}^{13}\psi(r)B_s(r/13)$ (`zetaD_eq_abs`). -/
theorem table6_row_13 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 13 s * (13 : ℝ) ^ (s - 1) * Real.sqrt 13 / π ^ s =
      ((|(1 + 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 13) - (Polynomial.bernoulli s).eval (2 / 13)
        + (Polynomial.bernoulli s).eval (3 / 13) + (Polynomial.bernoulli s).eval (4 / 13)
        - (Polynomial.bernoulli s).eval (5 / 13) - (Polynomial.bernoulli s).eval (6 / 13)
        - (Polynomial.bernoulli s).eval (7 / 13) - (Polynomial.bernoulli s).eval (8 / 13)
        + (Polynomial.bernoulli s).eval (9 / 13) + (Polynomial.bernoulli s).eval (10 / 13)
        - (Polynomial.bernoulli s).eval (11 / 13) + (Polynomial.bernoulli s).eval (12 / 13)| *
        13 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 13) (by norm_num) isPrimitive_psi13
    psi13_inv _ chiD_eq_changeLevel_13 hs
    (by rw [psi13_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi13_euler_13 s) (psi13_sum _) 13 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 13$, $s = 2$** ($D = 13$): $\zeta_{13}(2)\,13^{1}\sqrt{13}/\pi^{2} = 5$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 2)"]
theorem table6_13_2 : zetaD 13 2 * 13 ^ 1 * Real.sqrt 13 / π ^ 2 = 5 := by
  rw [show zetaD 13 2 * 13 ^ 1 * Real.sqrt 13 / π ^ 2 =
      zetaD 13 ((2 : ℕ) : ℝ) * 13 ^ (2 - 1) * Real.sqrt 13 / π ^ 2 by norm_num,
    table6_row_13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 4$** ($D = 13$): $\zeta_{13}(4)\,13^{3}\sqrt{13}/\pi^{4} = 493/6$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 4)"]
theorem table6_13_4 : zetaD 13 4 * 13 ^ 3 * Real.sqrt 13 / π ^ 4 = 493 / 6 := by
  rw [show zetaD 13 4 * 13 ^ 3 * Real.sqrt 13 / π ^ 4 =
      zetaD 13 ((4 : ℕ) : ℝ) * 13 ^ (4 - 1) * Real.sqrt 13 / π ^ 4 by norm_num,
    table6_row_13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 6$** ($D = 13$): $\zeta_{13}(6)\,13^{5}\sqrt{13}/\pi^{6} = 33463/24$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 6)"]
theorem table6_13_6 : zetaD 13 6 * 13 ^ 5 * Real.sqrt 13 / π ^ 6 = 33463 / 24 := by
  rw [show zetaD 13 6 * 13 ^ 5 * Real.sqrt 13 / π ^ 6 =
      zetaD 13 ((6 : ℕ) : ℝ) * 13 ^ (6 - 1) * Real.sqrt 13 / π ^ 6 by norm_num,
    table6_row_13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 8$** ($D = 13$): $\zeta_{13}(8)\,13^{7}\sqrt{13}/\pi^{8} = 120190933/5040$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 8)"]
theorem table6_13_8 : zetaD 13 8 * 13 ^ 7 * Real.sqrt 13 / π ^ 8 = 120190933 / 5040 := by
  rw [show zetaD 13 8 * 13 ^ 7 * Real.sqrt 13 / π ^ 8 =
      zetaD 13 ((8 : ℕ) : ℝ) * 13 ^ (8 - 1) * Real.sqrt 13 / π ^ 8 by norm_num,
    table6_row_13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 10$** ($D = 13$): $\zeta_{13}(10)\,13^{9}\sqrt{13}/\pi^{10} = 29632170055/72576$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 13, s = 10)"]
theorem table6_13_10 : zetaD 13 10 * 13 ^ 9 * Real.sqrt 13 / π ^ 10 = 29632170055 / 72576 := by
  rw [show zetaD 13 10 * 13 ^ 9 * Real.sqrt 13 / π ^ 10 =
      zetaD 13 ((10 : ℕ) : ℝ) * 13 ^ (10 - 1) * Real.sqrt 13 / π ^ 10 by norm_num,
    table6_row_13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 12$** ($D = 13$): $\zeta_{13}(12)\,13^{11}\sqrt{13}/\pi^{12} = 279065797700773/39916800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 13, s = 12)"]
theorem table6_13_12 : zetaD 13 12 * 13 ^ 11 * Real.sqrt 13 / π ^ 12 = 279065797700773 / 39916800 := by
  rw [show zetaD 13 12 * 13 ^ 11 * Real.sqrt 13 / π ^ 12 =
      zetaD 13 ((12 : ℕ) : ℝ) * 13 ^ (12 - 1) * Real.sqrt 13 / π ^ 12 by norm_num,
    table6_row_13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-52}{\cdot}\right)$ modulo $52$ -/

instance isQuadDisc_neg52 : IsQuadDisc (-52) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-52 : ℤ) / 4 = -13 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -13$: the Kronecker character $\left(\frac{-52}{\cdot}\right)$ modulo $52$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -13)"]
noncomputable def psiNeg52 : DirichletCharacter ℂ 52 := kroneckerChar (-52)

theorem psiNeg52_natCast (n : ℕ) : psiNeg52 n = (chiD (-13) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-52) (by norm_num) n

theorem psiNeg52_inv : psiNeg52⁻¹ = psiNeg52 := kroneckerChar_inv (-52)

theorem psiNeg52_neg_one : psiNeg52 (-1) = -1 := by
  rw [show (-1 : ZMod 52) = ((51 : ℕ) : ZMod 52) by decide, psiNeg52_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -13, conductor 52)"]
theorem isPrimitive_psiNeg52 : psiNeg52.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 52 = {2, 13} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨27, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((27 : ℤ) : ZMod 52) = ((27 : ℕ) : ZMod 52) by norm_cast, psiNeg52_natCast]; norm_num [chiD]⟩
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 52) = ((5 : ℕ) : ZMod 52) by norm_cast, psiNeg52_natCast]; norm_num [chiD]⟩

theorem psiNeg52_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 52, psiNeg52 (r : ZMod 52) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 - f 5 + f 7 + f 9 + f 11 + f 15 + f 17 + f 19 - f 21 - f 23 + f 25 - f 27 + f 29
      + f 31 - f 33 - f 35 - f 37 - f 41 - f 43 - f 45 + f 47 + f 49 - f 51 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg52_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg13 :
    ∀ m : ℕ, (chiD (-13) m : ℂ) = DirichletCharacter.changeLevel (show 52 ∣ 4 * (-13 : ℤ).natAbs by decide)
      psiNeg52 (m : ZMod (4 * (-13 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-13 : ℤ).natAbs) < 52 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-13 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg52_natCast] <;> norm_num [chiD]

theorem psiNeg52_euler_neg13 (s : ℕ) :
    ∏ p ∈ (4 * (-13 : ℤ).natAbs).primeFactors, (1 - psiNeg52 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-13 : ℤ).natAbs).primeFactors = {2, 13} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg52_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 13$, odd $s$** ($D = -13$, $\psi = \left(\frac{-52}{\cdot}\right)$ modulo
$k_1 = 52$): $\zeta_{-13}(s)\,13^{s-1}\sqrt{13}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,13^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{52}\psi(r)B_s(r/52)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg13 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-13) s * (13 : ℝ) ^ (s - 1) * Real.sqrt 13 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 52) - (Polynomial.bernoulli s).eval (3 / 52)
        - (Polynomial.bernoulli s).eval (5 / 52) + (Polynomial.bernoulli s).eval (7 / 52)
        + (Polynomial.bernoulli s).eval (9 / 52) + (Polynomial.bernoulli s).eval (11 / 52)
        + (Polynomial.bernoulli s).eval (15 / 52) + (Polynomial.bernoulli s).eval (17 / 52)
        + (Polynomial.bernoulli s).eval (19 / 52) - (Polynomial.bernoulli s).eval (21 / 52)
        - (Polynomial.bernoulli s).eval (23 / 52) + (Polynomial.bernoulli s).eval (25 / 52)
        - (Polynomial.bernoulli s).eval (27 / 52) + (Polynomial.bernoulli s).eval (29 / 52)
        + (Polynomial.bernoulli s).eval (31 / 52) - (Polynomial.bernoulli s).eval (33 / 52)
        - (Polynomial.bernoulli s).eval (35 / 52) - (Polynomial.bernoulli s).eval (37 / 52)
        - (Polynomial.bernoulli s).eval (41 / 52) - (Polynomial.bernoulli s).eval (43 / 52)
        - (Polynomial.bernoulli s).eval (45 / 52) + (Polynomial.bernoulli s).eval (47 / 52)
        + (Polynomial.bernoulli s).eval (49 / 52) - (Polynomial.bernoulli s).eval (51 / 52)| *
        13 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -13) (by norm_num) isPrimitive_psiNeg52
    psiNeg52_inv _ chiD_eq_changeLevel_neg13 hs
    (by rw [psiNeg52_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg52_euler_neg13 s) (psiNeg52_sum _) 13 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 13$, $s = 3$** ($D = -13$): $\zeta_{-13}(3)\,13^{2}\sqrt{13}/\pi^{3} = 151/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 3)"]
theorem table6_13_3 : zetaD (-13) 3 * 13 ^ 2 * Real.sqrt 13 / π ^ 3 = 151 / 8 := by
  rw [show zetaD (-13) 3 * 13 ^ 2 * Real.sqrt 13 / π ^ 3 =
      zetaD (-13) ((3 : ℕ) : ℝ) * 13 ^ (3 - 1) * Real.sqrt 13 / π ^ 3 by norm_num,
    table6_row_neg13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 5$** ($D = -13$): $\zeta_{-13}(5)\,13^{4}\sqrt{13}/\pi^{5} = 128657/384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 5)"]
theorem table6_13_5 : zetaD (-13) 5 * 13 ^ 4 * Real.sqrt 13 / π ^ 5 = 128657 / 384 := by
  rw [show zetaD (-13) 5 * 13 ^ 4 * Real.sqrt 13 / π ^ 5 =
      zetaD (-13) ((5 : ℕ) : ℝ) * 13 ^ (5 - 1) * Real.sqrt 13 / π ^ 5 by norm_num,
    table6_row_neg13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 7$** ($D = -13$): $\zeta_{-13}(7)\,13^{6}\sqrt{13}/\pi^{7} = 265394311/46080$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 7)"]
theorem table6_13_7 : zetaD (-13) 7 * 13 ^ 6 * Real.sqrt 13 / π ^ 7 = 265394311 / 46080 := by
  rw [show zetaD (-13) 7 * 13 ^ 6 * Real.sqrt 13 / π ^ 7 =
      zetaD (-13) ((7 : ℕ) : ℝ) * 13 ^ (7 - 1) * Real.sqrt 13 / π ^ 7 by norm_num,
    table6_row_neg13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 9$** ($D = -13$): $\zeta_{-13}(9)\,13^{8}\sqrt{13}/\pi^{9} = 1018375291937/10321920$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 13, s = 9)"]
theorem table6_13_9 : zetaD (-13) 9 * 13 ^ 8 * Real.sqrt 13 / π ^ 9 = 1018375291937 / 10321920 := by
  rw [show zetaD (-13) 9 * 13 ^ 8 * Real.sqrt 13 / π ^ 9 =
      zetaD (-13) ((9 : ℕ) : ℝ) * 13 ^ (9 - 1) * Real.sqrt 13 / π ^ 9 by norm_num,
    table6_row_neg13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 13$, $s = 11$** ($D = -13$): $\zeta_{-13}(11)\,13^{10}\sqrt{13}/\pi^{11} = 6277939539153271/3715891200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 13, s = 11)"]
theorem table6_13_11 : zetaD (-13) 11 * 13 ^ 10 * Real.sqrt 13 / π ^ 11 = 6277939539153271 / 3715891200 := by
  rw [show zetaD (-13) 11 * 13 ^ 10 * Real.sqrt 13 / π ^ 11 =
      zetaD (-13) ((11 : ℕ) : ℝ) * 13 ^ (11 - 1) * Real.sqrt 13 / π ^ 11 by norm_num,
    table6_row_neg13 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 14$ -/

/-! #### The character $\left(\frac{56}{\cdot}\right)$ modulo $56$ -/

instance isQuadDisc_56 : IsQuadDisc 56 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (56 : ℤ) / 4 = 14 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 14$: the Kronecker character $\left(\frac{56}{\cdot}\right)$ modulo $56$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 14)"]
noncomputable def psi56 : DirichletCharacter ℂ 56 := kroneckerChar 56

theorem psi56_natCast (n : ℕ) : psi56 n = (chiD 14 n : ℂ) :=
  kroneckerChar_natCast_of_zero 56 (by norm_num) n

theorem psi56_inv : psi56⁻¹ = psi56 := kroneckerChar_inv 56

theorem psi56_neg_one : psi56 (-1) = 1 := by
  rw [show (-1 : ZMod 56) = ((55 : ℕ) : ZMod 56) by decide, psi56_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 14, conductor 56)"]
theorem isPrimitive_psi56 : psi56.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 56 = {2, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨29, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((29 : ℤ) : ZMod 56) = ((29 : ℕ) : ZMod 56) by norm_cast, psi56_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 56) = ((17 : ℕ) : ZMod 56) by norm_cast, psi56_natCast]; norm_num [chiD]⟩

theorem psi56_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 56, psi56 (r : ZMod 56) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 3 + f 5 + f 9 + f 11 + f 13 - f 15 - f 17 - f 19 - f 23 + f 25 - f 27 - f 29 + f 31
      - f 33 - f 37 - f 39 - f 41 + f 43 + f 45 + f 47 + f 51 - f 53 + f 55 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi56_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_14 :
    ∀ m : ℕ, (chiD 14 m : ℂ) = DirichletCharacter.changeLevel (show 56 ∣ 4 * (14 : ℤ).natAbs by decide)
      psi56 (m : ZMod (4 * (14 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (14 : ℤ).natAbs) < 56 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (14 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi56_natCast] <;> norm_num [chiD]

theorem psi56_euler_14 (s : ℕ) :
    ∏ p ∈ (4 * (14 : ℤ).natAbs).primeFactors, (1 - psi56 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (14 : ℤ).natAbs).primeFactors = {2, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi56_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 14$, even $s$** ($D = 14$, $\psi = \left(\frac{56}{\cdot}\right)$ modulo
$k_1 = 56$): $\zeta_{14}(s)\,14^{s-1}\sqrt{14}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,14^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{56}\psi(r)B_s(r/56)$ (`zetaD_eq_abs`). -/
theorem table6_row_14 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 14 s * (14 : ℝ) ^ (s - 1) * Real.sqrt 14 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 56) - (Polynomial.bernoulli s).eval (3 / 56)
        + (Polynomial.bernoulli s).eval (5 / 56) + (Polynomial.bernoulli s).eval (9 / 56)
        + (Polynomial.bernoulli s).eval (11 / 56) + (Polynomial.bernoulli s).eval (13 / 56)
        - (Polynomial.bernoulli s).eval (15 / 56) - (Polynomial.bernoulli s).eval (17 / 56)
        - (Polynomial.bernoulli s).eval (19 / 56) - (Polynomial.bernoulli s).eval (23 / 56)
        + (Polynomial.bernoulli s).eval (25 / 56) - (Polynomial.bernoulli s).eval (27 / 56)
        - (Polynomial.bernoulli s).eval (29 / 56) + (Polynomial.bernoulli s).eval (31 / 56)
        - (Polynomial.bernoulli s).eval (33 / 56) - (Polynomial.bernoulli s).eval (37 / 56)
        - (Polynomial.bernoulli s).eval (39 / 56) - (Polynomial.bernoulli s).eval (41 / 56)
        + (Polynomial.bernoulli s).eval (43 / 56) + (Polynomial.bernoulli s).eval (45 / 56)
        + (Polynomial.bernoulli s).eval (47 / 56) + (Polynomial.bernoulli s).eval (51 / 56)
        - (Polynomial.bernoulli s).eval (53 / 56) + (Polynomial.bernoulli s).eval (55 / 56)| *
        14 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 14) (by norm_num) isPrimitive_psi56
    psi56_inv _ chiD_eq_changeLevel_14 hs
    (by rw [psi56_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi56_euler_14 s) (psi56_sum _) 14 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 14$, $s = 2$** ($D = 14$): $\zeta_{14}(2)\,14^{1}\sqrt{14}/\pi^{2} = 5$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 2)"]
theorem table6_14_2 : zetaD 14 2 * 14 ^ 1 * Real.sqrt 14 / π ^ 2 = 5 := by
  rw [show zetaD 14 2 * 14 ^ 1 * Real.sqrt 14 / π ^ 2 =
      zetaD 14 ((2 : ℕ) : ℝ) * 14 ^ (2 - 1) * Real.sqrt 14 / π ^ 2 by norm_num,
    table6_row_14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 4$** ($D = 14$): $\zeta_{14}(4)\,14^{3}\sqrt{14}/\pi^{4} = 2503/24$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 4)"]
theorem table6_14_4 : zetaD 14 4 * 14 ^ 3 * Real.sqrt 14 / π ^ 4 = 2503 / 24 := by
  rw [show zetaD 14 4 * 14 ^ 3 * Real.sqrt 14 / π ^ 4 =
      zetaD 14 ((4 : ℕ) : ℝ) * 14 ^ (4 - 1) * Real.sqrt 14 / π ^ 4 by norm_num,
    table6_row_14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 6$** ($D = 14$): $\zeta_{14}(6)\,14^{5}\sqrt{14}/\pi^{6} = 802729/384$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 6)"]
theorem table6_14_6 : zetaD 14 6 * 14 ^ 5 * Real.sqrt 14 / π ^ 6 = 802729 / 384 := by
  rw [show zetaD 14 6 * 14 ^ 5 * Real.sqrt 14 / π ^ 6 =
      zetaD 14 ((6 : ℕ) : ℝ) * 14 ^ (6 - 1) * Real.sqrt 14 / π ^ 6 by norm_num,
    table6_row_14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 8$** ($D = 14$): $\zeta_{14}(8)\,14^{7}\sqrt{14}/\pi^{8} = 13406231743/322560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 8)"]
theorem table6_14_8 : zetaD 14 8 * 14 ^ 7 * Real.sqrt 14 / π ^ 8 = 13406231743 / 322560 := by
  rw [show zetaD 14 8 * 14 ^ 7 * Real.sqrt 14 / π ^ 8 =
      zetaD 14 ((8 : ℕ) : ℝ) * 14 ^ (8 - 1) * Real.sqrt 14 / π ^ 8 by norm_num,
    table6_row_14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 10$** ($D = 14$): $\zeta_{14}(10)\,14^{9}\sqrt{14}/\pi^{10} = 15337101636817/18579456$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 14, s = 10)"]
theorem table6_14_10 : zetaD 14 10 * 14 ^ 9 * Real.sqrt 14 / π ^ 10 = 15337101636817 / 18579456 := by
  rw [show zetaD 14 10 * 14 ^ 9 * Real.sqrt 14 / π ^ 10 =
      zetaD 14 ((10 : ℕ) : ℝ) * 14 ^ (10 - 1) * Real.sqrt 14 / π ^ 10 by norm_num,
    table6_row_14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 12$** ($D = 14$): $\zeta_{14}(12)\,14^{11}\sqrt{14}/\pi^{12} = 670083304256329783/40874803200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 14, s = 12)"]
theorem table6_14_12 : zetaD 14 12 * 14 ^ 11 * Real.sqrt 14 / π ^ 12 = 670083304256329783 / 40874803200 := by
  rw [show zetaD 14 12 * 14 ^ 11 * Real.sqrt 14 / π ^ 12 =
      zetaD 14 ((12 : ℕ) : ℝ) * 14 ^ (12 - 1) * Real.sqrt 14 / π ^ 12 by norm_num,
    table6_row_14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-56}{\cdot}\right)$ modulo $56$ -/

instance isQuadDisc_neg56 : IsQuadDisc (-56) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-56 : ℤ) / 4 = -14 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -14$: the Kronecker character $\left(\frac{-56}{\cdot}\right)$ modulo $56$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -14)"]
noncomputable def psiNeg56 : DirichletCharacter ℂ 56 := kroneckerChar (-56)

theorem psiNeg56_natCast (n : ℕ) : psiNeg56 n = (chiD (-14) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-56) (by norm_num) n

theorem psiNeg56_inv : psiNeg56⁻¹ = psiNeg56 := kroneckerChar_inv (-56)

theorem psiNeg56_neg_one : psiNeg56 (-1) = -1 := by
  rw [show (-1 : ZMod 56) = ((55 : ℕ) : ZMod 56) by decide, psiNeg56_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -14, conductor 56)"]
theorem isPrimitive_psiNeg56 : psiNeg56.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 56 = {2, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨29, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((29 : ℤ) : ZMod 56) = ((29 : ℕ) : ZMod 56) by norm_cast, psiNeg56_natCast]; norm_num [chiD]⟩
  · exact ⟨17, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((17 : ℤ) : ZMod 56) = ((17 : ℕ) : ZMod 56) by norm_cast, psiNeg56_natCast]; norm_num [chiD]⟩

theorem psiNeg56_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 56, psiNeg56 (r : ZMod 56) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 + f 5 + f 9 - f 11 + f 13 + f 15 - f 17 + f 19 + f 23 + f 25 + f 27 - f 29 - f 31
      - f 33 - f 37 + f 39 - f 41 - f 43 + f 45 - f 47 - f 51 - f 53 - f 55 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg56_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg14 :
    ∀ m : ℕ, (chiD (-14) m : ℂ) = DirichletCharacter.changeLevel (show 56 ∣ 4 * (-14 : ℤ).natAbs by decide)
      psiNeg56 (m : ZMod (4 * (-14 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-14 : ℤ).natAbs) < 56 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-14 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg56_natCast] <;> norm_num [chiD]

theorem psiNeg56_euler_neg14 (s : ℕ) :
    ∏ p ∈ (4 * (-14 : ℤ).natAbs).primeFactors, (1 - psiNeg56 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-14 : ℤ).natAbs).primeFactors = {2, 7} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg56_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 14$, odd $s$** ($D = -14$, $\psi = \left(\frac{-56}{\cdot}\right)$ modulo
$k_1 = 56$): $\zeta_{-14}(s)\,14^{s-1}\sqrt{14}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,14^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{56}\psi(r)B_s(r/56)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg14 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-14) s * (14 : ℝ) ^ (s - 1) * Real.sqrt 14 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 56) + (Polynomial.bernoulli s).eval (3 / 56)
        + (Polynomial.bernoulli s).eval (5 / 56) + (Polynomial.bernoulli s).eval (9 / 56)
        - (Polynomial.bernoulli s).eval (11 / 56) + (Polynomial.bernoulli s).eval (13 / 56)
        + (Polynomial.bernoulli s).eval (15 / 56) - (Polynomial.bernoulli s).eval (17 / 56)
        + (Polynomial.bernoulli s).eval (19 / 56) + (Polynomial.bernoulli s).eval (23 / 56)
        + (Polynomial.bernoulli s).eval (25 / 56) + (Polynomial.bernoulli s).eval (27 / 56)
        - (Polynomial.bernoulli s).eval (29 / 56) - (Polynomial.bernoulli s).eval (31 / 56)
        - (Polynomial.bernoulli s).eval (33 / 56) - (Polynomial.bernoulli s).eval (37 / 56)
        + (Polynomial.bernoulli s).eval (39 / 56) - (Polynomial.bernoulli s).eval (41 / 56)
        - (Polynomial.bernoulli s).eval (43 / 56) + (Polynomial.bernoulli s).eval (45 / 56)
        - (Polynomial.bernoulli s).eval (47 / 56) - (Polynomial.bernoulli s).eval (51 / 56)
        - (Polynomial.bernoulli s).eval (53 / 56) - (Polynomial.bernoulli s).eval (55 / 56)| *
        14 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -14) (by norm_num) isPrimitive_psiNeg56
    psiNeg56_inv _ chiD_eq_changeLevel_neg14 hs
    (by rw [psiNeg56_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg56_euler_neg14 s) (psiNeg56_sum _) 14 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 14$, $s = 3$** ($D = -14$): $\zeta_{-14}(3)\,14^{2}\sqrt{14}/\pi^{3} = 99/4$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 3)"]
theorem table6_14_3 : zetaD (-14) 3 * 14 ^ 2 * Real.sqrt 14 / π ^ 3 = 99 / 4 := by
  rw [show zetaD (-14) 3 * 14 ^ 2 * Real.sqrt 14 / π ^ 3 =
      zetaD (-14) ((3 : ℕ) : ℝ) * 14 ^ (3 - 1) * Real.sqrt 14 / π ^ 3 by norm_num,
    table6_row_neg14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 5$** ($D = -14$): $\zeta_{-14}(5)\,14^{4}\sqrt{14}/\pi^{5} = 30195/64$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 5)"]
theorem table6_14_5 : zetaD (-14) 5 * 14 ^ 4 * Real.sqrt 14 / π ^ 5 = 30195 / 64 := by
  rw [show zetaD (-14) 5 * 14 ^ 4 * Real.sqrt 14 / π ^ 5 =
      zetaD (-14) ((5 : ℕ) : ℝ) * 14 ^ (5 - 1) * Real.sqrt 14 / π ^ 5 by norm_num,
    table6_row_neg14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 7$** ($D = -14$): $\zeta_{-14}(7)\,14^{6}\sqrt{14}/\pi^{7} = 23890611/2560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 7)"]
theorem table6_14_7 : zetaD (-14) 7 * 14 ^ 6 * Real.sqrt 14 / π ^ 7 = 23890611 / 2560 := by
  rw [show zetaD (-14) 7 * 14 ^ 6 * Real.sqrt 14 / π ^ 7 =
      zetaD (-14) ((7 : ℕ) : ℝ) * 14 ^ (7 - 1) * Real.sqrt 14 / π ^ 7 by norm_num,
    table6_row_neg14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 9$** ($D = -14$): $\zeta_{-14}(9)\,14^{8}\sqrt{14}/\pi^{9} = 21246124181/114688$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 14, s = 9)"]
theorem table6_14_9 : zetaD (-14) 9 * 14 ^ 8 * Real.sqrt 14 / π ^ 9 = 21246124181 / 114688 := by
  rw [show zetaD (-14) 9 * 14 ^ 8 * Real.sqrt 14 / π ^ 9 =
      zetaD (-14) ((9 : ℕ) : ℝ) * 14 ^ (9 - 1) * Real.sqrt 14 / π ^ 9 by norm_num,
    table6_row_neg14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 14$, $s = 11$** ($D = -14$): $\zeta_{-14}(11)\,14^{10}\sqrt{14}/\pi^{11} = 253143899134537/68812800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 14, s = 11)"]
theorem table6_14_11 : zetaD (-14) 11 * 14 ^ 10 * Real.sqrt 14 / π ^ 11 = 253143899134537 / 68812800 := by
  rw [show zetaD (-14) 11 * 14 ^ 10 * Real.sqrt 14 / π ^ 11 =
      zetaD (-14) ((11 : ℕ) : ℝ) * 14 ^ (11 - 1) * Real.sqrt 14 / π ^ 11 by norm_num,
    table6_row_neg14 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 15$ -/

/-! #### The character $\left(\frac{60}{\cdot}\right)$ modulo $60$ -/

instance isQuadDisc_60 : IsQuadDisc 60 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (60 : ℤ) / 4 = 15 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 15$: the Kronecker character $\left(\frac{60}{\cdot}\right)$ modulo $60$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 15)"]
noncomputable def psi60 : DirichletCharacter ℂ 60 := kroneckerChar 60

theorem psi60_natCast (n : ℕ) : psi60 n = (chiD 15 n : ℂ) :=
  kroneckerChar_natCast_of_zero 60 (by norm_num) n

theorem psi60_inv : psi60⁻¹ = psi60 := kroneckerChar_inv 60

theorem psi60_neg_one : psi60 (-1) = 1 := by
  rw [show (-1 : ZMod 60) = ((59 : ℕ) : ZMod 60) by decide, psi60_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 15, conductor 60)"]
theorem isPrimitive_psi60 : psi60.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 60 = {2, 3, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨31, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((31 : ℤ) : ZMod 60) = ((31 : ℕ) : ZMod 60) by norm_cast, psi60_natCast]; norm_num [chiD]⟩
  · exact ⟨41, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((41 : ℤ) : ZMod 60) = ((41 : ℕ) : ZMod 60) by norm_cast, psi60_natCast]; norm_num [chiD]⟩
  · exact ⟨13, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((13 : ℤ) : ZMod 60) = ((13 : ℕ) : ZMod 60) by norm_cast, psi60_natCast]; norm_num [chiD]⟩

theorem psi60_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 60, psi60 (r : ZMod 60) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 7 + f 11 - f 13 + f 17 - f 19 - f 23 - f 29 - f 31 - f 37 - f 41 + f 43 - f 47
      + f 49 + f 53 + f 59 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi60_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_15 :
    ∀ m : ℕ, (chiD 15 m : ℂ) = DirichletCharacter.changeLevel (show 60 ∣ 4 * (15 : ℤ).natAbs by decide)
      psi60 (m : ZMod (4 * (15 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (15 : ℤ).natAbs) < 60 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (15 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi60_natCast] <;> norm_num [chiD]

theorem psi60_euler_15 (s : ℕ) :
    ∏ p ∈ (4 * (15 : ℤ).natAbs).primeFactors, (1 - psi60 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (15 : ℤ).natAbs).primeFactors = {2, 3, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi60_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 15$, even $s$** ($D = 15$, $\psi = \left(\frac{60}{\cdot}\right)$ modulo
$k_1 = 60$): $\zeta_{15}(s)\,15^{s-1}\sqrt{15}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,15^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{60}\psi(r)B_s(r/60)$ (`zetaD_eq_abs`). -/
theorem table6_row_15 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 15 s * (15 : ℝ) ^ (s - 1) * Real.sqrt 15 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 60) + (Polynomial.bernoulli s).eval (7 / 60)
        + (Polynomial.bernoulli s).eval (11 / 60) - (Polynomial.bernoulli s).eval (13 / 60)
        + (Polynomial.bernoulli s).eval (17 / 60) - (Polynomial.bernoulli s).eval (19 / 60)
        - (Polynomial.bernoulli s).eval (23 / 60) - (Polynomial.bernoulli s).eval (29 / 60)
        - (Polynomial.bernoulli s).eval (31 / 60) - (Polynomial.bernoulli s).eval (37 / 60)
        - (Polynomial.bernoulli s).eval (41 / 60) + (Polynomial.bernoulli s).eval (43 / 60)
        - (Polynomial.bernoulli s).eval (47 / 60) + (Polynomial.bernoulli s).eval (49 / 60)
        + (Polynomial.bernoulli s).eval (53 / 60) + (Polynomial.bernoulli s).eval (59 / 60)| *
        15 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 15) (by norm_num) isPrimitive_psi60
    psi60_inv _ chiD_eq_changeLevel_15 hs
    (by rw [psi60_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi60_euler_15 s) (psi60_sum _) 15 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 15$, $s = 2$** ($D = 15$): $\zeta_{15}(2)\,15^{1}\sqrt{15}/\pi^{2} = 6$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 2)"]
theorem table6_15_2 : zetaD 15 2 * 15 ^ 1 * Real.sqrt 15 / π ^ 2 = 6 := by
  rw [show zetaD 15 2 * 15 ^ 1 * Real.sqrt 15 / π ^ 2 =
      zetaD 15 ((2 : ℕ) : ℝ) * 15 ^ (2 - 1) * Real.sqrt 15 / π ^ 2 by norm_num,
    table6_row_15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 4$** ($D = 15$): $\zeta_{15}(4)\,15^{3}\sqrt{15}/\pi^{4} = 537/4$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 4)"]
theorem table6_15_4 : zetaD 15 4 * 15 ^ 3 * Real.sqrt 15 / π ^ 4 = 537 / 4 := by
  rw [show zetaD 15 4 * 15 ^ 3 * Real.sqrt 15 / π ^ 4 =
      zetaD 15 ((4 : ℕ) : ℝ) * 15 ^ (4 - 1) * Real.sqrt 15 / π ^ 4 by norm_num,
    table6_row_15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 6$** ($D = 15$): $\zeta_{15}(6)\,15^{5}\sqrt{15}/\pi^{6} = 978941/320$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 6)"]
theorem table6_15_6 : zetaD 15 6 * 15 ^ 5 * Real.sqrt 15 / π ^ 6 = 978941 / 320 := by
  rw [show zetaD 15 6 * 15 ^ 5 * Real.sqrt 15 / π ^ 6 =
      zetaD 15 ((6 : ℕ) : ℝ) * 15 ^ (6 - 1) * Real.sqrt 15 / π ^ 6 by norm_num,
    table6_row_15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 8$** ($D = 15$): $\zeta_{15}(8)\,15^{7}\sqrt{15}/\pi^{8} = 3749253437/53760$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 8)"]
theorem table6_15_8 : zetaD 15 8 * 15 ^ 7 * Real.sqrt 15 / π ^ 8 = 3749253437 / 53760 := by
  rw [show zetaD 15 8 * 15 ^ 7 * Real.sqrt 15 / π ^ 8 =
      zetaD 15 ((8 : ℕ) : ℝ) * 15 ^ (8 - 1) * Real.sqrt 15 / π ^ 8 by norm_num,
    table6_row_15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 10$** ($D = 15$): $\zeta_{15}(10)\,15^{9}\sqrt{15}/\pi^{10} = 2735126857009/1720320$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 15, s = 10)"]
theorem table6_15_10 : zetaD 15 10 * 15 ^ 9 * Real.sqrt 15 / π ^ 10 = 2735126857009 / 1720320 := by
  rw [show zetaD 15 10 * 15 ^ 9 * Real.sqrt 15 / π ^ 10 =
      zetaD 15 ((10 : ℕ) : ℝ) * 15 ^ (10 - 1) * Real.sqrt 15 / π ^ 10 by norm_num,
    table6_row_15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 12$** ($D = 15$): $\zeta_{15}(12)\,15^{11}\sqrt{15}/\pi^{12} = 246919524028587937/6812467200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 15, s = 12)"]
theorem table6_15_12 : zetaD 15 12 * 15 ^ 11 * Real.sqrt 15 / π ^ 12 = 246919524028587937 / 6812467200 := by
  rw [show zetaD 15 12 * 15 ^ 11 * Real.sqrt 15 / π ^ 12 =
      zetaD 15 ((12 : ℕ) : ℝ) * 15 ^ (12 - 1) * Real.sqrt 15 / π ^ 12 by norm_num,
    table6_row_15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-15}{\cdot}\right)$ modulo $15$ -/

instance isQuadDisc_neg15 : IsQuadDisc (-15) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = -15$: the Kronecker character $\left(\frac{-15}{\cdot}\right)$ modulo $15$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -15)"]
noncomputable def psiNeg15 : DirichletCharacter ℂ 15 := kroneckerChar (-15)

theorem psiNeg15_natCast (n : ℕ) : psiNeg15 n = (jacobiSym n 15 : ℂ) :=
  kroneckerChar_natCast_of_one (-15) (by norm_num) n

theorem psiNeg15_inv : psiNeg15⁻¹ = psiNeg15 := kroneckerChar_inv (-15)

theorem psiNeg15_neg_one : psiNeg15 (-1) = -1 := by
  rw [show (-1 : ZMod 15) = ((14 : ℕ) : ZMod 15) by decide, psiNeg15_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -15, conductor 15)"]
theorem isPrimitive_psiNeg15 : psiNeg15.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 15 = {3, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨11, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((11 : ℤ) : ZMod 15) = ((11 : ℕ) : ZMod 15) by norm_cast, psiNeg15_natCast]; norm_num [chiD]⟩
  · exact ⟨7, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((7 : ℤ) : ZMod 15) = ((7 : ℕ) : ZMod 15) by norm_cast, psiNeg15_natCast]; norm_num [chiD]⟩

theorem psiNeg15_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 15, psiNeg15 (r : ZMod 15) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 2 + f 4 - f 7 + f 8 - f 11 - f 13 - f 14 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg15_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg15 :
    ∀ m : ℕ, (chiD (-15) m : ℂ) = DirichletCharacter.changeLevel (show 15 ∣ 4 * (-15 : ℤ).natAbs by decide)
      psiNeg15 (m : ZMod (4 * (-15 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-15 : ℤ).natAbs) < 60 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-15 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg15_natCast] <;> norm_num [chiD]

theorem psiNeg15_euler_neg15 (s : ℕ) :
    ∏ p ∈ (4 * (-15 : ℤ).natAbs).primeFactors, (1 - psiNeg15 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-15 : ℤ).natAbs).primeFactors = {2, 3, 5} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg15_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 15$, odd $s$** ($D = -15$, $\psi = \left(\frac{-15}{\cdot}\right)$ modulo
$k_1 = 15$): $\zeta_{-15}(s)\,15^{s-1}\sqrt{15}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,15^{s-1}/(2\,s!)$ with
$E = (1 - 2^{-s})$ and $S = \sum_{r=1}^{15}\psi(r)B_s(r/15)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg15 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-15) s * (15 : ℝ) ^ (s - 1) * Real.sqrt 15 / π ^ s =
      ((|(1 - 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 15) + (Polynomial.bernoulli s).eval (2 / 15)
        + (Polynomial.bernoulli s).eval (4 / 15) - (Polynomial.bernoulli s).eval (7 / 15)
        + (Polynomial.bernoulli s).eval (8 / 15) - (Polynomial.bernoulli s).eval (11 / 15)
        - (Polynomial.bernoulli s).eval (13 / 15) - (Polynomial.bernoulli s).eval (14 / 15)| *
        15 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -15) (by norm_num) isPrimitive_psiNeg15
    psiNeg15_inv _ chiD_eq_changeLevel_neg15 hs
    (by rw [psiNeg15_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg15_euler_neg15 s) (psiNeg15_sum _) 15 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 15$, $s = 3$** ($D = -15$): $\zeta_{-15}(3)\,15^{2}\sqrt{15}/\pi^{3} = 28$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 3)"]
theorem table6_15_3 : zetaD (-15) 3 * 15 ^ 2 * Real.sqrt 15 / π ^ 3 = 28 := by
  rw [show zetaD (-15) 3 * 15 ^ 2 * Real.sqrt 15 / π ^ 3 =
      zetaD (-15) ((3 : ℕ) : ℝ) * 15 ^ (3 - 1) * Real.sqrt 15 / π ^ 3 by norm_num,
    table6_row_neg15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 5$** ($D = -15$): $\zeta_{-15}(5)\,15^{4}\sqrt{15}/\pi^{5} = 1922/3$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 5)"]
theorem table6_15_5 : zetaD (-15) 5 * 15 ^ 4 * Real.sqrt 15 / π ^ 5 = 1922 / 3 := by
  rw [show zetaD (-15) 5 * 15 ^ 4 * Real.sqrt 15 / π ^ 5 =
      zetaD (-15) ((5 : ℕ) : ℝ) * 15 ^ (5 - 1) * Real.sqrt 15 / π ^ 5 by norm_num,
    table6_row_neg15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 7$** ($D = -15$): $\zeta_{-15}(7)\,15^{6}\sqrt{15}/\pi^{7} = 1314577/90$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 7)"]
theorem table6_15_7 : zetaD (-15) 7 * 15 ^ 6 * Real.sqrt 15 / π ^ 7 = 1314577 / 90 := by
  rw [show zetaD (-15) 7 * 15 ^ 6 * Real.sqrt 15 / π ^ 7 =
      zetaD (-15) ((7 : ℕ) : ℝ) * 15 ^ (7 - 1) * Real.sqrt 15 / π ^ 7 by norm_num,
    table6_row_neg15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 9$** ($D = -15$): $\zeta_{-15}(9)\,15^{8}\sqrt{15}/\pi^{9} = 59937599/180$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 15, s = 9)"]
theorem table6_15_9 : zetaD (-15) 9 * 15 ^ 8 * Real.sqrt 15 / π ^ 9 = 59937599 / 180 := by
  rw [show zetaD (-15) 9 * 15 ^ 8 * Real.sqrt 15 / π ^ 9 =
      zetaD (-15) ((9 : ℕ) : ℝ) * 15 ^ (9 - 1) * Real.sqrt 15 / π ^ 9 by norm_num,
    table6_row_neg15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 15$, $s = 11$** ($D = -15$): $\zeta_{-15}(11)\,15^{10}\sqrt{15}/\pi^{11} = 3443361870847/453600$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 15, s = 11)"]
theorem table6_15_11 : zetaD (-15) 11 * 15 ^ 10 * Real.sqrt 15 / π ^ 11 = 3443361870847 / 453600 := by
  rw [show zetaD (-15) 11 * 15 ^ 10 * Real.sqrt 15 / π ^ 11 =
      zetaD (-15) ((11 : ℕ) : ℝ) * 15 ^ (11 - 1) * Real.sqrt 15 / π ^ 11 by norm_num,
    table6_row_neg15 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 17$ -/

/-! #### The character $\left(\frac{17}{\cdot}\right)$ modulo $17$ -/

instance isQuadDisc_17 : IsQuadDisc 17 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = 17$: the Kronecker character $\left(\frac{17}{\cdot}\right)$ modulo $17$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 17)"]
noncomputable def psi17 : DirichletCharacter ℂ 17 := kroneckerChar 17

theorem psi17_natCast (n : ℕ) : psi17 n = (jacobiSym n 17 : ℂ) :=
  kroneckerChar_natCast_of_one 17 (by norm_num) n

theorem psi17_inv : psi17⁻¹ = psi17 := kroneckerChar_inv 17

theorem psi17_neg_one : psi17 (-1) = 1 := by
  rw [show (-1 : ZMod 17) = ((16 : ℕ) : ZMod 17) by decide, psi17_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 17, conductor 17)"]
theorem isPrimitive_psi17 : psi17.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 17 = {17} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_singleton] at hp
  rcases hp with rfl
  · exact ⟨3, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((3 : ℤ) : ZMod 17) = ((3 : ℕ) : ZMod 17) by norm_cast, psi17_natCast]; norm_num [chiD]⟩

theorem psi17_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 17, psi17 (r : ZMod 17) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 2 - f 3 + f 4 - f 5 - f 6 - f 7 + f 8 + f 9 - f 10 - f 11 - f 12 + f 13 - f 14
      + f 15 + f 16 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi17_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_17 :
    ∀ m : ℕ, (chiD 17 m : ℂ) = DirichletCharacter.changeLevel (show 17 ∣ 4 * (17 : ℤ).natAbs by decide)
      psi17 (m : ZMod (4 * (17 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (17 : ℤ).natAbs) < 68 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (17 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi17_natCast] <;> norm_num [chiD]

theorem psi17_euler_17 (s : ℕ) :
    ∏ p ∈ (4 * (17 : ℤ).natAbs).primeFactors, (1 - psi17 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 - 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (17 : ℤ).natAbs).primeFactors = {2, 17} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi17_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 17$, even $s$** ($D = 17$, $\psi = \left(\frac{17}{\cdot}\right)$ modulo
$k_1 = 17$): $\zeta_{17}(s)\,17^{s-1}\sqrt{17}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,17^{s-1}/(2\,s!)$ with
$E = (1 - 2^{-s})$ and $S = \sum_{r=1}^{17}\psi(r)B_s(r/17)$ (`zetaD_eq_abs`). -/
theorem table6_row_17 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 17 s * (17 : ℝ) ^ (s - 1) * Real.sqrt 17 / π ^ s =
      ((|(1 - 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 17) + (Polynomial.bernoulli s).eval (2 / 17)
        - (Polynomial.bernoulli s).eval (3 / 17) + (Polynomial.bernoulli s).eval (4 / 17)
        - (Polynomial.bernoulli s).eval (5 / 17) - (Polynomial.bernoulli s).eval (6 / 17)
        - (Polynomial.bernoulli s).eval (7 / 17) + (Polynomial.bernoulli s).eval (8 / 17)
        + (Polynomial.bernoulli s).eval (9 / 17) - (Polynomial.bernoulli s).eval (10 / 17)
        - (Polynomial.bernoulli s).eval (11 / 17) - (Polynomial.bernoulli s).eval (12 / 17)
        + (Polynomial.bernoulli s).eval (13 / 17) - (Polynomial.bernoulli s).eval (14 / 17)
        + (Polynomial.bernoulli s).eval (15 / 17) + (Polynomial.bernoulli s).eval (16 / 17)| *
        17 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 17) (by norm_num) isPrimitive_psi17
    psi17_inv _ chiD_eq_changeLevel_17 hs
    (by rw [psi17_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi17_euler_17 s) (psi17_sum _) 17 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 17$, $s = 2$** ($D = 17$): $\zeta_{17}(2)\,17^{1}\sqrt{17}/\pi^{2} = 6$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 2)"]
theorem table6_17_2 : zetaD 17 2 * 17 ^ 1 * Real.sqrt 17 / π ^ 2 = 6 := by
  rw [show zetaD 17 2 * 17 ^ 1 * Real.sqrt 17 / π ^ 2 =
      zetaD 17 ((2 : ℕ) : ℝ) * 17 ^ (2 - 1) * Real.sqrt 17 / π ^ 2 by norm_num,
    table6_row_17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 4$** ($D = 17$): $\zeta_{17}(4)\,17^{3}\sqrt{17}/\pi^{4} = 205$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 4)"]
theorem table6_17_4 : zetaD 17 4 * 17 ^ 3 * Real.sqrt 17 / π ^ 4 = 205 := by
  rw [show zetaD 17 4 * 17 ^ 3 * Real.sqrt 17 / π ^ 4 =
      zetaD 17 ((4 : ℕ) : ℝ) * 17 ^ (4 - 1) * Real.sqrt 17 / π ^ 4 by norm_num,
    table6_row_17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 6$** ($D = 17$): $\zeta_{17}(6)\,17^{5}\sqrt{17}/\pi^{6} = 121611/20$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 6)"]
theorem table6_17_6 : zetaD 17 6 * 17 ^ 5 * Real.sqrt 17 / π ^ 6 = 121611 / 20 := by
  rw [show zetaD 17 6 * 17 ^ 5 * Real.sqrt 17 / π ^ 6 =
      zetaD 17 ((6 : ℕ) : ℝ) * 17 ^ (6 - 1) * Real.sqrt 17 / π ^ 6 by norm_num,
    table6_row_17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 8$** ($D = 17$): $\zeta_{17}(8)\,17^{7}\sqrt{17}/\pi^{8} = 29950897/168$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 8)"]
theorem table6_17_8 : zetaD 17 8 * 17 ^ 7 * Real.sqrt 17 / π ^ 8 = 29950897 / 168 := by
  rw [show zetaD 17 8 * 17 ^ 7 * Real.sqrt 17 / π ^ 8 =
      zetaD 17 ((8 : ℕ) : ℝ) * 17 ^ (8 - 1) * Real.sqrt 17 / π ^ 8 by norm_num,
    table6_row_17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 10$** ($D = 17$): $\zeta_{17}(10)\,17^{9}\sqrt{17}/\pi^{10} = 315769666091/60480$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 17, s = 10)"]
theorem table6_17_10 : zetaD 17 10 * 17 ^ 9 * Real.sqrt 17 / π ^ 10 = 315769666091 / 60480 := by
  rw [show zetaD 17 10 * 17 ^ 9 * Real.sqrt 17 / π ^ 10 =
      zetaD 17 ((10 : ℕ) : ℝ) * 17 ^ (10 - 1) * Real.sqrt 17 / π ^ 10 by norm_num,
    table6_row_17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 12$** ($D = 17$): $\zeta_{17}(12)\,17^{11}\sqrt{17}/\pi^{12} = 9686758513133/63360$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 17, s = 12)"]
theorem table6_17_12 : zetaD 17 12 * 17 ^ 11 * Real.sqrt 17 / π ^ 12 = 9686758513133 / 63360 := by
  rw [show zetaD 17 12 * 17 ^ 11 * Real.sqrt 17 / π ^ 12 =
      zetaD 17 ((12 : ℕ) : ℝ) * 17 ^ (12 - 1) * Real.sqrt 17 / π ^ 12 by norm_num,
    table6_row_17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-68}{\cdot}\right)$ modulo $68$ -/

instance isQuadDisc_neg68 : IsQuadDisc (-68) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (-68 : ℤ) / 4 = -17 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = -17$: the Kronecker character $\left(\frac{-68}{\cdot}\right)$ modulo $68$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -17)"]
noncomputable def psiNeg68 : DirichletCharacter ℂ 68 := kroneckerChar (-68)

theorem psiNeg68_natCast (n : ℕ) : psiNeg68 n = (chiD (-17) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-68) (by norm_num) n

theorem psiNeg68_inv : psiNeg68⁻¹ = psiNeg68 := kroneckerChar_inv (-68)

theorem psiNeg68_neg_one : psiNeg68 (-1) = -1 := by
  rw [show (-1 : ZMod 68) = ((67 : ℕ) : ZMod 68) by decide, psiNeg68_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -17, conductor 68)"]
theorem isPrimitive_psiNeg68 : psiNeg68.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 68 = {2, 17} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨35, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((35 : ℤ) : ZMod 68) = ((35 : ℕ) : ZMod 68) by norm_cast, psiNeg68_natCast]; norm_num [chiD]⟩
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 68) = ((5 : ℕ) : ZMod 68) by norm_cast, psiNeg68_natCast]; norm_num [chiD]⟩

theorem psiNeg68_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 68, psiNeg68 (r : ZMod 68) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 - f 5 + f 7 + f 9 + f 11 + f 13 - f 15 - f 19 + f 21 + f 23 + f 25 + f 27 - f 29
      + f 31 + f 33 - f 35 - f 37 + f 39 - f 41 - f 43 - f 45 - f 47 + f 49 + f 53 - f 55 - f 57
      - f 59 - f 61 + f 63 - f 65 - f 67 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg68_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg17 :
    ∀ m : ℕ, (chiD (-17) m : ℂ) = DirichletCharacter.changeLevel (show 68 ∣ 4 * (-17 : ℤ).natAbs by decide)
      psiNeg68 (m : ZMod (4 * (-17 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-17 : ℤ).natAbs) < 68 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-17 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg68_natCast] <;> norm_num [chiD]

theorem psiNeg68_euler_neg17 (s : ℕ) :
    ∏ p ∈ (4 * (-17 : ℤ).natAbs).primeFactors, (1 - psiNeg68 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (-17 : ℤ).natAbs).primeFactors = {2, 17} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg68_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 17$, odd $s$** ($D = -17$, $\psi = \left(\frac{-68}{\cdot}\right)$ modulo
$k_1 = 68$): $\zeta_{-17}(s)\,17^{s-1}\sqrt{17}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,17^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{68}\psi(r)B_s(r/68)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg17 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-17) s * (17 : ℝ) ^ (s - 1) * Real.sqrt 17 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 68) + (Polynomial.bernoulli s).eval (3 / 68)
        - (Polynomial.bernoulli s).eval (5 / 68) + (Polynomial.bernoulli s).eval (7 / 68)
        + (Polynomial.bernoulli s).eval (9 / 68) + (Polynomial.bernoulli s).eval (11 / 68)
        + (Polynomial.bernoulli s).eval (13 / 68) - (Polynomial.bernoulli s).eval (15 / 68)
        - (Polynomial.bernoulli s).eval (19 / 68) + (Polynomial.bernoulli s).eval (21 / 68)
        + (Polynomial.bernoulli s).eval (23 / 68) + (Polynomial.bernoulli s).eval (25 / 68)
        + (Polynomial.bernoulli s).eval (27 / 68) - (Polynomial.bernoulli s).eval (29 / 68)
        + (Polynomial.bernoulli s).eval (31 / 68) + (Polynomial.bernoulli s).eval (33 / 68)
        - (Polynomial.bernoulli s).eval (35 / 68) - (Polynomial.bernoulli s).eval (37 / 68)
        + (Polynomial.bernoulli s).eval (39 / 68) - (Polynomial.bernoulli s).eval (41 / 68)
        - (Polynomial.bernoulli s).eval (43 / 68) - (Polynomial.bernoulli s).eval (45 / 68)
        - (Polynomial.bernoulli s).eval (47 / 68) + (Polynomial.bernoulli s).eval (49 / 68)
        + (Polynomial.bernoulli s).eval (53 / 68) - (Polynomial.bernoulli s).eval (55 / 68)
        - (Polynomial.bernoulli s).eval (57 / 68) - (Polynomial.bernoulli s).eval (59 / 68)
        - (Polynomial.bernoulli s).eval (61 / 68) + (Polynomial.bernoulli s).eval (63 / 68)
        - (Polynomial.bernoulli s).eval (65 / 68) - (Polynomial.bernoulli s).eval (67 / 68)| *
        17 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -17) (by norm_num) isPrimitive_psiNeg68
    psiNeg68_inv _ chiD_eq_changeLevel_neg17 hs
    (by rw [psiNeg68_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg68_euler_neg17 s) (psiNeg68_sum _) 17 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 17$, $s = 3$** ($D = -17$): $\zeta_{-17}(3)\,17^{2}\sqrt{17}/\pi^{3} = 159/4$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 3)"]
theorem table6_17_3 : zetaD (-17) 3 * 17 ^ 2 * Real.sqrt 17 / π ^ 3 = 159 / 4 := by
  rw [show zetaD (-17) 3 * 17 ^ 2 * Real.sqrt 17 / π ^ 3 =
      zetaD (-17) ((3 : ℕ) : ℝ) * 17 ^ (3 - 1) * Real.sqrt 17 / π ^ 3 by norm_num,
    table6_row_neg17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 5$** ($D = -17$): $\zeta_{-17}(5)\,17^{4}\sqrt{17}/\pi^{5} = 72299/64$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 5)"]
theorem table6_17_5 : zetaD (-17) 5 * 17 ^ 4 * Real.sqrt 17 / π ^ 5 = 72299 / 64 := by
  rw [show zetaD (-17) 5 * 17 ^ 4 * Real.sqrt 17 / π ^ 5 =
      zetaD (-17) ((5 : ℕ) : ℝ) * 17 ^ (5 - 1) * Real.sqrt 17 / π ^ 5 by norm_num,
    table6_row_neg17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 7$** ($D = -17$): $\zeta_{-17}(7)\,17^{6}\sqrt{17}/\pi^{7} = 84392231/2560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 7)"]
theorem table6_17_7 : zetaD (-17) 7 * 17 ^ 6 * Real.sqrt 17 / π ^ 7 = 84392231 / 2560 := by
  rw [show zetaD (-17) 7 * 17 ^ 6 * Real.sqrt 17 / π ^ 7 =
      zetaD (-17) ((7 : ℕ) : ℝ) * 17 ^ (7 - 1) * Real.sqrt 17 / π ^ 7 by norm_num,
    table6_row_neg17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 9$** ($D = -17$): $\zeta_{-17}(9)\,17^{8}\sqrt{17}/\pi^{9} = 1659961706539/1720320$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 17, s = 9)"]
theorem table6_17_9 : zetaD (-17) 9 * 17 ^ 8 * Real.sqrt 17 / π ^ 9 = 1659961706539 / 1720320 := by
  rw [show zetaD (-17) 9 * 17 ^ 8 * Real.sqrt 17 / π ^ 9 =
      zetaD (-17) ((9 : ℕ) : ℝ) * 17 ^ (9 - 1) * Real.sqrt 17 / π ^ 9 by norm_num,
    table6_row_neg17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 17$, $s = 11$** ($D = -17$): $\zeta_{-17}(11)\,17^{10}\sqrt{17}/\pi^{11} = 17497631131594933/619315200$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 17, s = 11)"]
theorem table6_17_11 : zetaD (-17) 11 * 17 ^ 10 * Real.sqrt 17 / π ^ 11 = 17497631131594933 / 619315200 := by
  rw [show zetaD (-17) 11 * 17 ^ 10 * Real.sqrt 17 / π ^ 11 =
      zetaD (-17) ((11 : ℕ) : ℝ) * 17 ^ (11 - 1) * Real.sqrt 17 / π ^ 11 by norm_num,
    table6_row_neg17 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### Row $d = 19$ -/

/-! #### The character $\left(\frac{76}{\cdot}\right)$ modulo $76$ -/

instance isQuadDisc_76 : IsQuadDisc 76 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    rw [show (76 : ℤ) / 4 = 19 by norm_num]
    exact int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])
  ne_one := by norm_num

/-- $\psi$ for $D = 19$: the Kronecker character $\left(\frac{76}{\cdot}\right)$ modulo $76$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 19)"]
noncomputable def psi76 : DirichletCharacter ℂ 76 := kroneckerChar 76

theorem psi76_natCast (n : ℕ) : psi76 n = (chiD 19 n : ℂ) :=
  kroneckerChar_natCast_of_zero 76 (by norm_num) n

theorem psi76_inv : psi76⁻¹ = psi76 := kroneckerChar_inv 76

theorem psi76_neg_one : psi76 (-1) = 1 := by
  rw [show (-1 : ZMod 76) = ((75 : ℕ) : ZMod 76) by decide, psi76_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 19, conductor 76)"]
theorem isPrimitive_psi76 : psi76.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 76 = {2, 19} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨39, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((39 : ℤ) : ZMod 76) = ((39 : ℕ) : ZMod 76) by norm_cast, psi76_natCast]; norm_num [chiD]⟩
  · exact ⟨13, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((13 : ℤ) : ZMod 76) = ((13 : ℕ) : ZMod 76) by norm_cast, psi76_natCast]; norm_num [chiD]⟩

theorem psi76_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 76, psi76 (r : ZMod 76) * ((f r : ℚ) : ℂ) =
      ((f 1 + f 3 + f 5 - f 7 + f 9 - f 11 - f 13 + f 15 + f 17 - f 21 - f 23 + f 25 + f 27 - f 29
      + f 31 - f 33 - f 35 - f 37 - f 39 - f 41 - f 43 + f 45 - f 47 + f 49 + f 51 - f 53 - f 55
      + f 59 + f 61 - f 63 - f 65 + f 67 - f 69 + f 71 + f 73 + f 75 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psi76_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_19 :
    ∀ m : ℕ, (chiD 19 m : ℂ) = DirichletCharacter.changeLevel (show 76 ∣ 4 * (19 : ℤ).natAbs by decide)
      psi76 (m : ZMod (4 * (19 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (19 : ℤ).natAbs) < 76 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (19 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi76_natCast] <;> norm_num [chiD]

theorem psi76_euler_19 (s : ℕ) :
    ∏ p ∈ (4 * (19 : ℤ).natAbs).primeFactors, (1 - psi76 p * (p : ℂ) ^ (-(s : ℂ))) =
      ((1 : ℚ) : ℂ) := by
  rw [show (4 * (19 : ℤ).natAbs).primeFactors = {2, 19} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psi76_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 19$, even $s$** ($D = 19$, $\psi = \left(\frac{76}{\cdot}\right)$ modulo
$k_1 = 76$): $\zeta_{19}(s)\,19^{s-1}\sqrt{19}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,19^{s-1}(1/2)/(2\,s!)$ with
$E = 1$ and $S = \sum_{r=1}^{76}\psi(r)B_s(r/76)$ (`zetaD_eq_abs`). -/
theorem table6_row_19 {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 19 s * (19 : ℝ) ^ (s - 1) * Real.sqrt 19 / π ^ s =
      ((|1| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 76) + (Polynomial.bernoulli s).eval (3 / 76)
        + (Polynomial.bernoulli s).eval (5 / 76) - (Polynomial.bernoulli s).eval (7 / 76)
        + (Polynomial.bernoulli s).eval (9 / 76) - (Polynomial.bernoulli s).eval (11 / 76)
        - (Polynomial.bernoulli s).eval (13 / 76) + (Polynomial.bernoulli s).eval (15 / 76)
        + (Polynomial.bernoulli s).eval (17 / 76) - (Polynomial.bernoulli s).eval (21 / 76)
        - (Polynomial.bernoulli s).eval (23 / 76) + (Polynomial.bernoulli s).eval (25 / 76)
        + (Polynomial.bernoulli s).eval (27 / 76) - (Polynomial.bernoulli s).eval (29 / 76)
        + (Polynomial.bernoulli s).eval (31 / 76) - (Polynomial.bernoulli s).eval (33 / 76)
        - (Polynomial.bernoulli s).eval (35 / 76) - (Polynomial.bernoulli s).eval (37 / 76)
        - (Polynomial.bernoulli s).eval (39 / 76) - (Polynomial.bernoulli s).eval (41 / 76)
        - (Polynomial.bernoulli s).eval (43 / 76) + (Polynomial.bernoulli s).eval (45 / 76)
        - (Polynomial.bernoulli s).eval (47 / 76) + (Polynomial.bernoulli s).eval (49 / 76)
        + (Polynomial.bernoulli s).eval (51 / 76) - (Polynomial.bernoulli s).eval (53 / 76)
        - (Polynomial.bernoulli s).eval (55 / 76) + (Polynomial.bernoulli s).eval (59 / 76)
        + (Polynomial.bernoulli s).eval (61 / 76) - (Polynomial.bernoulli s).eval (63 / 76)
        - (Polynomial.bernoulli s).eval (65 / 76) + (Polynomial.bernoulli s).eval (67 / 76)
        - (Polynomial.bernoulli s).eval (69 / 76) + (Polynomial.bernoulli s).eval (71 / 76)
        + (Polynomial.bernoulli s).eval (73 / 76) + (Polynomial.bernoulli s).eval (75 / 76)| *
        19 ^ (s - 1) * (1 / 2) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := 19) (by norm_num) isPrimitive_psi76
    psi76_inv _ chiD_eq_changeLevel_19 hs
    (by rw [psi76_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) _ _ (psi76_euler_19 s) (psi76_sum _) 19 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 2) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 19$, $s = 2$** ($D = 19$): $\zeta_{19}(2)\,19^{1}\sqrt{19}/\pi^{2} = 19/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 2)"]
theorem table6_19_2 : zetaD 19 2 * 19 ^ 1 * Real.sqrt 19 / π ^ 2 = 19 / 2 := by
  rw [show zetaD 19 2 * 19 ^ 1 * Real.sqrt 19 / π ^ 2 =
      zetaD 19 ((2 : ℕ) : ℝ) * 19 ^ (2 - 1) * Real.sqrt 19 / π ^ 2 by norm_num,
    table6_row_19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 4$** ($D = 19$): $\zeta_{19}(4)\,19^{3}\sqrt{19}/\pi^{4} = 14933/48$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 4)"]
theorem table6_19_4 : zetaD 19 4 * 19 ^ 3 * Real.sqrt 19 / π ^ 4 = 14933 / 48 := by
  rw [show zetaD 19 4 * 19 ^ 3 * Real.sqrt 19 / π ^ 4 =
      zetaD 19 ((4 : ℕ) : ℝ) * 19 ^ (4 - 1) * Real.sqrt 19 / π ^ 4 by norm_num,
    table6_row_19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 6$** ($D = 19$): $\zeta_{19}(6)\,19^{5}\sqrt{19}/\pi^{6} = 43171459/3840$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 6)"]
theorem table6_19_6 : zetaD 19 6 * 19 ^ 5 * Real.sqrt 19 / π ^ 6 = 43171459 / 3840 := by
  rw [show zetaD 19 6 * 19 ^ 5 * Real.sqrt 19 / π ^ 6 =
      zetaD 19 ((6 : ℕ) : ℝ) * 19 ^ (6 - 1) * Real.sqrt 19 / π ^ 6 by norm_num,
    table6_row_19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 8$** ($D = 19$): $\zeta_{19}(8)\,19^{7}\sqrt{19}/\pi^{8} = 264948072293/645120$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 8)"]
theorem table6_19_8 : zetaD 19 8 * 19 ^ 7 * Real.sqrt 19 / π ^ 8 = 264948072293 / 645120 := by
  rw [show zetaD 19 8 * 19 ^ 7 * Real.sqrt 19 / π ^ 8 =
      zetaD 19 ((8 : ℕ) : ℝ) * 19 ^ (8 - 1) * Real.sqrt 19 / π ^ 8 by norm_num,
    table6_row_19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 10$** ($D = 19$): $\zeta_{19}(10)\,19^{9}\sqrt{19}/\pi^{10} = 2790621100831219/185794560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 19, s = 10)"]
theorem table6_19_10 : zetaD 19 10 * 19 ^ 9 * Real.sqrt 19 / π ^ 10 = 2790621100831219 / 185794560 := by
  rw [show zetaD 19 10 * 19 ^ 9 * Real.sqrt 19 / π ^ 10 =
      zetaD 19 ((10 : ℕ) : ℝ) * 19 ^ (10 - 1) * Real.sqrt 19 / π ^ 10 by norm_num,
    table6_row_19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 12$** ($D = 19$): $\zeta_{19}(12)\,19^{11}\sqrt{19}/\pi^{12} = 44911176071936980853/81749606400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 19, s = 12)"]
theorem table6_19_12 : zetaD 19 12 * 19 ^ 11 * Real.sqrt 19 / π ^ 12 = 44911176071936980853 / 81749606400 := by
  rw [show zetaD 19 12 * 19 ^ 11 * Real.sqrt 19 / π ^ 12 =
      zetaD 19 ((12 : ℕ) : ℝ) * 19 ^ (12 - 1) * Real.sqrt 19 / π ^ 12 by norm_num,
    table6_row_19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-! #### The character $\left(\frac{-19}{\cdot}\right)$ modulo $19$ -/

instance isQuadDisc_neg19 : IsQuadDisc (-19) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    exact ⟨by norm_num, int_squarefree_of_nodup (by norm_num) (by simp [Nat.primeFactorsList_ofNat])⟩
  ne_one := by norm_num

/-- $\psi$ for $D = -19$: the Kronecker character $\left(\frac{-19}{\cdot}\right)$ modulo $19$. -/
@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -19)"]
noncomputable def psiNeg19 : DirichletCharacter ℂ 19 := kroneckerChar (-19)

theorem psiNeg19_natCast (n : ℕ) : psiNeg19 n = (jacobiSym n 19 : ℂ) :=
  kroneckerChar_natCast_of_one (-19) (by norm_num) n

theorem psiNeg19_inv : psiNeg19⁻¹ = psiNeg19 := kroneckerChar_inv (-19)

theorem psiNeg19_neg_one : psiNeg19 (-1) = -1 := by
  rw [show (-1 : ZMod 19) = ((18 : ℕ) : ZMod 19) by decide, psiNeg19_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -19, conductor 19)"]
theorem isPrimitive_psiNeg19 : psiNeg19.IsPrimitive := by
  refine isPrimitive_of_prime_witness _ (fun p hp => ?_)
  rw [show Nat.primeFactors 19 = {19} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]] at hp
  simp only [Finset.mem_singleton] at hp
  rcases hp with rfl
  · exact ⟨2, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((2 : ℤ) : ZMod 19) = ((2 : ℕ) : ZMod 19) by norm_cast, psiNeg19_natCast]; norm_num [chiD]⟩

theorem psiNeg19_sum (f : ℕ → ℚ) :
    ∑ r ∈ Icc (1 : ℕ) 19, psiNeg19 (r : ZMod 19) * ((f r : ℚ) : ℂ) =
      ((f 1 - f 2 - f 3 + f 4 + f 5 + f 6 + f 7 - f 8 + f 9 - f 10 + f 11 - f 12 - f 13 - f 14
      - f 15 + f 16 + f 17 - f 18 : ℚ) : ℂ) := by
  rw [sum_Icc_one_eq]
  simp only [sum_range_succ, sum_range_zero, psiNeg19_natCast]
  norm_num [chiD]
  ring

theorem chiD_eq_changeLevel_neg19 :
    ∀ m : ℕ, (chiD (-19) m : ℂ) = DirichletCharacter.changeLevel (show 19 ∣ 4 * (-19 : ℤ).natAbs by decide)
      psiNeg19 (m : ZMod (4 * (-19 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-19 : ℤ).natAbs) < 76 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-19 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg19_natCast] <;> norm_num [chiD]

theorem psiNeg19_euler_neg19 (s : ℕ) :
    ∏ p ∈ (4 * (-19 : ℤ).natAbs).primeFactors, (1 - psiNeg19 p * (p : ℂ) ^ (-(s : ℂ))) =
      (((1 + 1 / 2 ^ s) : ℚ) : ℂ) := by
  rw [show (4 * (-19 : ℤ).natAbs).primeFactors = {2, 19} by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat],
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psiNeg19_natCast, cpow_neg, cpow_natCast]
  norm_num [chiD]

/-- **Table 6, row $d = 19$, odd $s$** ($D = -19$, $\psi = \left(\frac{-19}{\cdot}\right)$ modulo
$k_1 = 19$): $\zeta_{-19}(s)\,19^{s-1}\sqrt{19}/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,19^{s-1}/(2\,s!)$ with
$E = (1 + 2^{-s})$ and $S = \sum_{r=1}^{19}\psi(r)B_s(r/19)$ (`zetaD_eq_abs`). -/
theorem table6_row_neg19 {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-19) s * (19 : ℝ) ^ (s - 1) * Real.sqrt 19 / π ^ s =
      ((|(1 + 1 / 2 ^ s)| * 2 ^ s *
        |(Polynomial.bernoulli s).eval (1 / 19) - (Polynomial.bernoulli s).eval (2 / 19)
        - (Polynomial.bernoulli s).eval (3 / 19) + (Polynomial.bernoulli s).eval (4 / 19)
        + (Polynomial.bernoulli s).eval (5 / 19) + (Polynomial.bernoulli s).eval (6 / 19)
        + (Polynomial.bernoulli s).eval (7 / 19) - (Polynomial.bernoulli s).eval (8 / 19)
        + (Polynomial.bernoulli s).eval (9 / 19) - (Polynomial.bernoulli s).eval (10 / 19)
        + (Polynomial.bernoulli s).eval (11 / 19) - (Polynomial.bernoulli s).eval (12 / 19)
        - (Polynomial.bernoulli s).eval (13 / 19) - (Polynomial.bernoulli s).eval (14 / 19)
        - (Polynomial.bernoulli s).eval (15 / 19) + (Polynomial.bernoulli s).eval (16 / 19)
        + (Polynomial.bernoulli s).eval (17 / 19) - (Polynomial.bernoulli s).eval (18 / 19)| *
        19 ^ (s - 1) / (2 * s.factorial) : ℚ) : ℝ) := by
  have h := table6_eq_abs (D := -19) (by norm_num) isPrimitive_psiNeg19
    psiNeg19_inv _ chiD_eq_changeLevel_neg19 hs
    (by rw [psiNeg19_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) _ _ (psiNeg19_euler_neg19 s) (psiNeg19_sum _) 19 _
    (sqrt_eq_rat_mul_sqrt (a := 1) (b := 1) (by norm_num) (by norm_num))
  push_cast at h ⊢
  exact h.trans (by norm_num)

/-- **Table 6, $d = 19$, $s = 3$** ($D = -19$): $\zeta_{-19}(3)\,19^{2}\sqrt{19}/\pi^{3} = 99/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 3)"]
theorem table6_19_3 : zetaD (-19) 3 * 19 ^ 2 * Real.sqrt 19 / π ^ 3 = 99 / 2 := by
  rw [show zetaD (-19) 3 * 19 ^ 2 * Real.sqrt 19 / π ^ 3 =
      zetaD (-19) ((3 : ℕ) : ℝ) * 19 ^ (3 - 1) * Real.sqrt 19 / π ^ 3 by norm_num,
    table6_row_neg19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 5$** ($D = -19$): $\zeta_{-19}(5)\,19^{4}\sqrt{19}/\pi^{5} = 14795/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 5)"]
theorem table6_19_5 : zetaD (-19) 5 * 19 ^ 4 * Real.sqrt 19 / π ^ 5 = 14795 / 8 := by
  rw [show zetaD (-19) 5 * 19 ^ 4 * Real.sqrt 19 / π ^ 5 =
      zetaD (-19) ((5 : ℕ) : ℝ) * 19 ^ (5 - 1) * Real.sqrt 19 / π ^ 5 by norm_num,
    table6_row_neg19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 7$** ($D = -19$): $\zeta_{-19}(7)\,19^{6}\sqrt{19}/\pi^{7} = 16288013/240$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 7)"]
theorem table6_19_7 : zetaD (-19) 7 * 19 ^ 6 * Real.sqrt 19 / π ^ 7 = 16288013 / 240 := by
  rw [show zetaD (-19) 7 * 19 ^ 6 * Real.sqrt 19 / π ^ 7 =
      zetaD (-19) ((7 : ℕ) : ℝ) * 19 ^ (7 - 1) * Real.sqrt 19 / π ^ 7 by norm_num,
    table6_row_neg19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 9$** ($D = -19$): $\zeta_{-19}(9)\,19^{8}\sqrt{19}/\pi^{9} = 2225066181/896$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 19, s = 9)"]
theorem table6_19_9 : zetaD (-19) 9 * 19 ^ 8 * Real.sqrt 19 / π ^ 9 = 2225066181 / 896 := by
  rw [show zetaD (-19) 9 * 19 ^ 8 * Real.sqrt 19 / π ^ 9 =
      zetaD (-19) ((9 : ℕ) : ℝ) * 19 ^ (9 - 1) * Real.sqrt 19 / π ^ 9 by norm_num,
    table6_row_neg19 (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 19$, $s = 11$** ($D = -19$): $\zeta_{-19}(11)\,19^{10}\sqrt{19}/\pi^{11} = 109876178454493/1209600$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 19, s = 11)"]
theorem table6_19_11 : zetaD (-19) 11 * 19 ^ 10 * Real.sqrt 19 / π ^ 11 = 109876178454493 / 1209600 := by
  rw [show zetaD (-19) 11 * 19 ^ 10 * Real.sqrt 19 / π ^ 11 =
      zetaD (-19) ((11 : ℕ) : ℝ) * 19 ^ (11 - 1) * Real.sqrt 19 / π ^ 11 by norm_num,
    table6_row_neg19 (by norm_num) (by norm_num)]
  bernoulli_eval

end QuadFormsKB.ConwaySloane.Mass
