/-
# Conway–Sloane 1988, §8, Table 6 and §1: values of $\zeta_D(s)$ for $d = 1, 2, 3$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, Table 6, pp. 270–271, and §1, p. 260.

Table 6 lists the rational numbers $\zeta_D(s)\,d^{s-1}\sqrt d/\pi^s$, $D = (-1)^s d$, for $d \le 25$ and $1 \le s \le 12$
($\zeta_D$ = `zetaD`). This file proves the rows $d = 1, 2, 3$ (all $s \le 12$), from the closed formula (13)
(`zetaD_formula`) with the characters and Gauss sums of `GaussSums.lean`; the even-$s$ entries of the row $d = 1$ come from
(15) (`zetaD_one_even`), and the entries $s = 1$ from Dirichlet's class number formula (`Binary.classNumberFormula_neg`).

**Proves**
* `zetaD_eq_real`: the real form of (13) used below: if $G(\psi) = i^{s \bmod 2}g$ with $g$ real, the Euler factor is the real
  number $E$ and $\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1) = S$, then $\zeta_D(s) = E\,(-1)^{\lfloor s/2\rfloor+1}(2\pi)^sS/(2\,s!\,g)$.
* The closed forms for all admissible $s \ge 2$:
  `zetaD_neg_three_odd` ($D = -3$), `zetaD_neg_one_odd` ($D = -1$), `zetaD_two_even` ($D = 2$), `zetaD_neg_two_odd`
  ($D = -2$), `zetaD_three_even` ($D = 3$).
* `table6_d_s` for $d \in \{1, 2, 3\}$, $1 \le s \le 12$: the printed entries.
* `zetaD_neg_three_one` (§1, p. 260): $1 - \frac15 + \frac17 - \frac1{11} + \frac1{13} - \cdots = \pi/(2\sqrt3)$.
* `zetaD_two_six` (§1, p. 260): $1 - 3^{-6} - 5^{-6} + 7^{-6} + 9^{-6} - \cdots = 361\pi^6/(245760\sqrt2)$.

**Check against the scan.** All $19 \times 12 = 228$ entries of Table 6 were recomputed independently (exact rational
arithmetic, formula (13) with the Kronecker character of the fundamental discriminant, Python) and agree with the printed
values; the 36 entries proved here are stated with the printed values.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GaussSums

namespace QuadFormsKB.ConwaySloane.Mass

open Complex ZMod Finset QuadFormsKB.Binary
open scoped Real

/-! ### The real form of (13) -/

theorem I_cpow_neg_add (s : ℕ) : I ^ (-(s : ℂ)) + (-1) ^ s * I ^ (s : ℂ) = 2 * (I ^ s)⁻¹ := by
  rw [cpow_neg, cpow_natCast]
  have : (I ^ s) ^ 2 = (-1) ^ s := by rw [← pow_mul, mul_comm, pow_mul, I_sq]
  have hI : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
  field_simp
  rw [this, ← mul_pow]
  norm_num

theorem I_pow_eq (s : ℕ) : I ^ s = (-1) ^ (s / 2) * I ^ (s % 2) := by
  conv_lhs => rw [← Nat.div_add_mod s 2, pow_add, pow_mul, I_sq]

/-- **(13) in real form.** Under the hypotheses of `zetaD_formula`, if the Gauss sum is $G(\psi) = i^{s \bmod 2}g$ with $g$ real
and nonzero, the Euler factor $\prod_{p \mid 4D}(1 - \psi(p)p^{-s})$ is the real number $E$ and
$\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)$ is the rational number $S$, then
$\zeta_D(s) = E\,(-1)^{\lfloor s/2\rfloor + 1}(2\pi)^s S/(2\,s!\,g)$. -/
theorem zetaD_eq_real {D : ℤ} (hD : D ≠ 0) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hreal : χ⁻¹ = χ) (hdvd : N ∣ 4 * D.natAbs)
    (hval : ∀ m : ℕ, (chiD D m : ℂ) = DirichletCharacter.changeLevel hdvd χ (m : ZMod (4 * D.natAbs)))
    {s : ℕ} (hs : 2 ≤ s) (hpar : χ (-1) = (-1) ^ s) (E g : ℝ) (S : ℚ)
    (hE : ∏ p ∈ (4 * D.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) = E)
    (hg : gaussSum χ stdAddChar = I ^ (s % 2) * g) (hg0 : g ≠ 0)
    (hS : ∑ r ∈ Icc 1 N, χ r * (((Polynomial.bernoulli s).eval ((r : ℚ) / N) : ℚ) : ℂ) = (S : ℂ)) :
    zetaD D s = E * (-1) ^ (s / 2 + 1) * (2 * π) ^ s * S / (2 * s.factorial * g) := by
  have hG : gaussSum χ stdAddChar ≠ 0 := by
    rw [hg]; exact mul_ne_zero (pow_ne_zero _ I_ne_zero) (by exact_mod_cast hg0)
  have h := zetaD_formula hD hχ hreal hdvd hval hs hpar hG
  rw [hE, hS, hg, hpar, I_cpow_neg_add, I_pow_eq] at h
  apply Complex.ofReal_injective
  rw [h]
  have hI : I ^ (s % 2) ≠ 0 := pow_ne_zero _ I_ne_zero
  have hm : ((-1 : ℂ) ^ (s / 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0
  push_cast
  field_simp
  ring

/-- $\sum_{r=1}^{N} f(r) = \sum_{r=0}^{N-1} f(r+1)$. -/
theorem sum_Icc_one_eq (N : ℕ) (f : ℕ → ℂ) : ∑ r ∈ Icc 1 N, f r = ∑ r ∈ range N, f (r + 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The Euler factor is $1$ when every prime factor $p$ of $4\lvert D\rvert$ divides the conductor ($\psi(p) = 0$). -/
theorem eulerFactor_eq_one {N M : ℕ} (χ : DirichletCharacter ℂ N) (h : ∀ p ∈ M.primeFactors, p ∣ N) (s : ℂ) :
    ∏ p ∈ M.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) = ((1 : ℝ) : ℂ) := by
  rw [Complex.ofReal_one]
  refine Finset.prod_eq_one (fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  have : χ (p : ZMod N) = 0 := by
    refine MulChar.map_nonunit _ ?_
    rw [ZMod.isUnit_iff_coprime]
    intro hc
    exact hp'.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc (h p hp))
  rw [this, zero_mul, sub_zero]

/-! ### $D = 2$, even $s$ -/

/-- **(13) for $D = 2$** ($\psi = \left(\frac8\cdot\right)$, $k_1 = 8$, $G(\psi) = 2\sqrt2$): for even $s \ge 2$,
$$\zeta_2(s) = (-1)^{s/2+1}\frac{(2\pi)^s}{4\,s!\,\sqrt2}\Bigl(B_s(\tfrac18) - B_s(\tfrac38) - B_s(\tfrac58) + B_s(\tfrac78)\Bigr).$$ -/
@[kb "conwaysloane1988" "§8 (13), p. 268 (D = 2)"]
theorem zetaD_two_even {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 2 s = (-1) ^ (s / 2 + 1) * (2 * π) ^ s *
      (((Polynomial.bernoulli s).eval (1 / 8) - (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) + (Polynomial.bernoulli s).eval (7 / 8) : ℚ) : ℝ) /
      (4 * s.factorial * Real.sqrt 2) := by
  have h := zetaD_eq_real (D := 2) (by norm_num) isPrimitive_psi8 psi8_inv _ chiD_eq_changeLevel_two hs
    (by rw [psi8_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) 1 (2 * Real.sqrt 2)
    ((Polynomial.bernoulli s).eval (1 / 8) - (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) + (Polynomial.bernoulli s).eval (7 / 8))
    (eulerFactor_eq_one _ (fun p hp => by
      have : p ∣ 4 * (2 : ℤ).natAbs := Nat.dvd_of_mem_primeFactors hp
      simpa using this) _)
    (by rw [gaussSum_psi8, he, pow_zero, one_mul]; push_cast; ring)
    (by positivity)
    (by
      rw [sum_Icc_one_eq]
      simp only [sum_range_succ, sum_range_zero, psi8_natCast]
      norm_num [chiD]
      ring)
  rw [h]
  ring

/-! ### Evaluating Bernoulli polynomials -/

theorem bo_3 : bernoulli 3 = 0 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bz_3]
theorem bo_5 : bernoulli 5 = 0 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bz_5]
theorem bo_7 : bernoulli 7 = 0 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bz_7]
theorem bo_9 : bernoulli 9 = 0 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bz_9]
theorem bo_11 : bernoulli 11 = 0 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bz_11]

/-- Expands $B_s(x) = \sum_k \binom sk B_k x^{s-k}$ and evaluates, for $s \le 12$. -/
macro "bernoulli_eval" : tactic =>
  `(tactic| ((simp only [Polynomial.bernoulli_def, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      Finset.sum_range_succ, Finset.sum_range_zero]) <;>
    norm_num [bernoulli_zero, bernoulli_one, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bo_3, bo_5, bo_7, bo_9,
      bo_11, Nat.choose]))


/-- Table 6 rows from the closed form: $\zeta_2(s)\,2^{s-1}\sqrt2/\pi^s$ is the rational number
$(-1)^{s/2+1}2^{2s-1}S/(4\,s!)$. -/
theorem table6_two_even {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 2 s * 2 ^ (s - 1) * Real.sqrt 2 / π ^ s =
      (((-1) ^ (s / 2 + 1) * 2 ^ s * 2 ^ (s - 1) / (4 * s.factorial) *
      ((Polynomial.bernoulli s).eval (1 / 8) - (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) + (Polynomial.bernoulli s).eval (7 / 8)) : ℚ) : ℝ) := by
  rw [zetaD_two_even hs he]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hπ : π ^ s ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  push_cast
  field_simp
  ring

/-! ### $D = -2$, odd $s$ -/

/-- **(13) for $D = -2$** ($\psi = \left(\frac{-8}\cdot\right)$, $k_1 = 8$, $G(\psi) = 2i\sqrt2$): for odd $s \ge 3$,
$$\zeta_{-2}(s) = (-1)^{\lfloor s/2\rfloor+1}\frac{(2\pi)^s}{4\,s!\,\sqrt2}\Bigl(B_s(\tfrac18) + B_s(\tfrac38) - B_s(\tfrac58)
- B_s(\tfrac78)\Bigr).$$ -/
@[kb "conwaysloane1988" "§8 (13), p. 268 (D = -2)"]
theorem zetaD_neg_two_odd {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-2) s = (-1) ^ (s / 2 + 1) * (2 * π) ^ s *
      (((Polynomial.bernoulli s).eval (1 / 8) + (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) - (Polynomial.bernoulli s).eval (7 / 8) : ℚ) : ℝ) /
      (4 * s.factorial * Real.sqrt 2) := by
  have h := zetaD_eq_real (D := -2) (by norm_num) isPrimitive_psiNeg8 psiNeg8_inv _ chiD_eq_changeLevel_neg2 hs
    (by rw [psiNeg8_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) 1 (2 * Real.sqrt 2)
    ((Polynomial.bernoulli s).eval (1 / 8) + (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) - (Polynomial.bernoulli s).eval (7 / 8))
    (eulerFactor_eq_one _ (fun p hp => by
      have : p ∣ 4 * (-2 : ℤ).natAbs := Nat.dvd_of_mem_primeFactors hp
      simpa using this) _)
    (by rw [gaussSum_psiNeg8, ho, pow_one]; push_cast; ring)
    (by positivity)
    (by
      rw [sum_Icc_one_eq]
      simp only [sum_range_succ, sum_range_zero, psiNeg8_natCast]
      norm_num [chiD]
      ring)
  rw [h]
  ring

theorem table6_neg_two_odd {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-2) s * 2 ^ (s - 1) * Real.sqrt 2 / π ^ s =
      (((-1) ^ (s / 2 + 1) * 2 ^ s * 2 ^ (s - 1) / (4 * s.factorial) *
      ((Polynomial.bernoulli s).eval (1 / 8) + (Polynomial.bernoulli s).eval (3 / 8)
        - (Polynomial.bernoulli s).eval (5 / 8) - (Polynomial.bernoulli s).eval (7 / 8)) : ℚ) : ℝ) := by
  rw [zetaD_neg_two_odd hs ho]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hπ : π ^ s ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  push_cast
  field_simp
  ring

/-! ### $D = -1$, odd $s$ -/

/-- **(13) for $D = -1$** ($\psi = \left(\frac{-4}\cdot\right)$, $k_1 = 4$, $G(\psi) = 2i$): for odd $s \ge 3$,
$$\zeta_{-1}(s) = (-1)^{\lfloor s/2\rfloor+1}\frac{(2\pi)^s}{4\,s!}\Bigl(B_s(\tfrac14) - B_s(\tfrac34)\Bigr).$$ -/
@[kb "conwaysloane1988" "§8 (13), p. 268 (D = -1)"]
theorem zetaD_neg_one_odd {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-1) s = (-1) ^ (s / 2 + 1) * (2 * π) ^ s *
      (((Polynomial.bernoulli s).eval (1 / 4) - (Polynomial.bernoulli s).eval (3 / 4) : ℚ) : ℝ) /
      (4 * s.factorial) := by
  have h := zetaD_eq_real (D := -1) (by norm_num) isPrimitive_psiNeg4 psiNeg4_inv _ chiD_eq_changeLevel_neg1 hs
    (by rw [psiNeg4_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) 1 2
    ((Polynomial.bernoulli s).eval (1 / 4) - (Polynomial.bernoulli s).eval (3 / 4))
    (eulerFactor_eq_one _ (fun p hp => by
      have : p ∣ 4 * (-1 : ℤ).natAbs := Nat.dvd_of_mem_primeFactors hp
      simpa using this) _)
    (by rw [gaussSum_psiNeg4, ho, pow_one]; push_cast; ring)
    (by norm_num)
    (by
      rw [sum_Icc_one_eq]
      simp only [sum_range_succ, sum_range_zero, psiNeg4_natCast]
      norm_num [chiD]
      ring)
  rw [h]
  ring

theorem table6_neg_one_odd {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-1) s / π ^ s =
      (((-1) ^ (s / 2 + 1) * 2 ^ s / (4 * s.factorial) *
      ((Polynomial.bernoulli s).eval (1 / 4) - (Polynomial.bernoulli s).eval (3 / 4)) : ℚ) : ℝ) := by
  rw [zetaD_neg_one_odd hs ho]
  have hπ : π ^ s ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  push_cast
  field_simp
  ring

/-! ### $D = 3$, even $s$ -/

/-- **(13) for $D = 3$** ($\psi = \left(\frac{12}\cdot\right)$, $k_1 = 12$, $G(\psi) = 2\sqrt3$): for even $s \ge 2$,
$$\zeta_3(s) = (-1)^{s/2+1}\frac{(2\pi)^s}{4\,s!\,\sqrt3}\Bigl(B_s(\tfrac1{12}) - B_s(\tfrac5{12}) - B_s(\tfrac7{12})
+ B_s(\tfrac{11}{12})\Bigr).$$ -/
@[kb "conwaysloane1988" "§8 (13), p. 268 (D = 3)"]
theorem zetaD_three_even {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 3 s = (-1) ^ (s / 2 + 1) * (2 * π) ^ s *
      (((Polynomial.bernoulli s).eval (1 / 12) - (Polynomial.bernoulli s).eval (5 / 12)
        - (Polynomial.bernoulli s).eval (7 / 12) + (Polynomial.bernoulli s).eval (11 / 12) : ℚ) : ℝ) /
      (4 * s.factorial * Real.sqrt 3) := by
  have h := zetaD_eq_real (D := 3) (by norm_num) isPrimitive_psi12 psi12_inv _ chiD_eq_changeLevel_three hs
    (by rw [psi12_neg_one, Even.neg_one_pow (Nat.even_iff.mpr he)]) 1 (2 * Real.sqrt 3)
    ((Polynomial.bernoulli s).eval (1 / 12) - (Polynomial.bernoulli s).eval (5 / 12)
        - (Polynomial.bernoulli s).eval (7 / 12) + (Polynomial.bernoulli s).eval (11 / 12))
    (eulerFactor_eq_one _ (fun p hp => by
      have : p ∣ 4 * (3 : ℤ).natAbs := Nat.dvd_of_mem_primeFactors hp
      simpa using this) _)
    (by rw [gaussSum_psi12, he, pow_zero, one_mul]; push_cast; ring)
    (by positivity)
    (by
      rw [sum_Icc_one_eq]
      simp only [sum_range_succ, sum_range_zero, psi12_natCast]
      norm_num [chiD]
      ring)
  rw [h]
  ring

theorem table6_three_even {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    zetaD 3 s * 3 ^ (s - 1) * Real.sqrt 3 / π ^ s =
      (((-1) ^ (s / 2 + 1) * 2 ^ s * 3 ^ (s - 1) / (4 * s.factorial) *
      ((Polynomial.bernoulli s).eval (1 / 12) - (Polynomial.bernoulli s).eval (5 / 12)
        - (Polynomial.bernoulli s).eval (7 / 12) + (Polynomial.bernoulli s).eval (11 / 12)) : ℚ) : ℝ) := by
  rw [zetaD_three_even hs he]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hπ : π ^ s ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  push_cast
  field_simp
  ring

/-! ### $D = -3$, odd $s$ -/

theorem primeFactors_twelve : Nat.primeFactors 12 = {2, 3} := by
  rw [show 12 = 2 ^ 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.prime_three.primeFactors]
  rfl

/-- **(13) for $D = -3$** ($\psi = \left(\frac{-3}\cdot\right)$, $k_1 = 3$, $G(\psi) = i\sqrt3$, Euler factor
$1 - \psi(2)2^{-s} = 1 + 2^{-s}$ at $p = 2$): for odd $s \ge 3$,
$$\zeta_{-3}(s) = (1 + 2^{-s})\,(-1)^{\lfloor s/2\rfloor+1}\frac{(2\pi)^s}{2\,s!\,\sqrt3}\Bigl(B_s(\tfrac13) - B_s(\tfrac23)\Bigr).$$ -/
@[kb "conwaysloane1988" "§8 (13), p. 268 (D = -3)"]
theorem zetaD_neg_three_odd {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-3) s = (1 + 1 / 2 ^ s) * (-1) ^ (s / 2 + 1) * (2 * π) ^ s *
      (((Polynomial.bernoulli s).eval (1 / 3) - (Polynomial.bernoulli s).eval (2 / 3) : ℚ) : ℝ) /
      (2 * s.factorial * Real.sqrt 3) := by
  have h := zetaD_eq_real (D := -3) (by norm_num) isPrimitive_psiNeg3 psiNeg3_inv _ chiD_eq_changeLevel_neg3 hs
    (by rw [psiNeg3_neg_one, Odd.neg_one_pow (Nat.odd_iff.mpr ho)]) (1 + 1 / 2 ^ s) (Real.sqrt 3)
    ((Polynomial.bernoulli s).eval (1 / 3) - (Polynomial.bernoulli s).eval (2 / 3))
    (by
      rw [show 4 * (-3 : ℤ).natAbs = 12 from rfl, primeFactors_twelve, Finset.prod_insert (by decide),
        Finset.prod_singleton, psiNeg3_natCast, psiNeg3_natCast, cpow_neg, cpow_neg, cpow_natCast,
        cpow_natCast]
      norm_num)
    (by rw [gaussSum_psiNeg3, ho, pow_one])
    (by positivity)
    (by
      rw [sum_Icc_one_eq]
      simp only [sum_range_succ, sum_range_zero, psiNeg3_natCast]
      norm_num
      ring)
  rw [h]

theorem table6_neg_three_odd {s : ℕ} (hs : 2 ≤ s) (ho : s % 2 = 1) :
    zetaD (-3) s * 3 ^ (s - 1) * Real.sqrt 3 / π ^ s =
      (((1 + 1 / 2 ^ s) * (-1) ^ (s / 2 + 1) * 2 ^ s * 3 ^ (s - 1) / (2 * s.factorial) *
      ((Polynomial.bernoulli s).eval (1 / 3) - (Polynomial.bernoulli s).eval (2 / 3)) : ℚ) : ℝ) := by
  rw [zetaD_neg_three_odd hs ho]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hπ : π ^ s ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  push_cast
  field_simp
  ring

/-! ### $D = 1$, even $s$ (from (15)) -/

theorem table6_one_even {k : ℕ} (hk : k ≠ 0) :
    zetaD 1 ((2 * k : ℕ) : ℝ) / π ^ (2 * k) =
      (((1 - 1 / 2 ^ (2 * k)) * 2 ^ (2 * k) * |bernoulli (2 * k)| / (2 * (2 * k).factorial) : ℚ) : ℝ) := by
  rw [zetaD_one_even hk, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have hπ : π ^ (2 * k) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : ((2 * k).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  field_simp
  ring

/-! ### $s = 1$: Dirichlet's class number formula -/

open NumberField in
instance isPrincipalIdealRing_QField_neg_three : IsPrincipalIdealRing (𝓞 (QField (-3))) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg (by norm_num)]
  have hπ := Real.pi_gt_three
  norm_num [Nat.factorial]
  nlinarith

open NumberField in
instance isPrincipalIdealRing_QField_neg_eight : IsPrincipalIdealRing (𝓞 (QField (-8))) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg (by norm_num)]
  have hπ := Real.pi_gt_d2
  norm_num [Nat.factorial]
  nlinarith

/-- $h(\mathbb Q(\sqrt{-3})) = 1$ (Minkowski's bound). -/
theorem classNumber_QField_neg_three : NumberField.classNumber (QField (-3)) = 1 :=
  NumberField.classNumber_eq_one_iff.2 inferInstance

/-- $h(\mathbb Q(\sqrt{-2})) = 1$ (Minkowski's bound). -/
theorem classNumber_QField_neg_eight : NumberField.classNumber (QField (-8)) = 1 :=
  NumberField.classNumber_eq_one_iff.2 inferInstance

/-- $L(1, \psi) = \pi/(3\sqrt3)$ for $\psi = \left(\frac{-3}\cdot\right)$ (class number formula, $h = 1$, $w = 6$). -/
theorem LFunction_psiNeg3_one : psiNeg3.LFunction 1 = ((π / (3 * Real.sqrt 3) : ℝ) : ℂ) := by
  have h := classNumberFormula_neg (D := -3) (by norm_num)
  rw [classNumber_QField_neg_three, torsionOrder_of_neg (by norm_num)] at h
  rw [show psiNeg3.LFunction 1 = (kroneckerChar (-3)).LFunction 1 from rfl, h]
  congr 1
  norm_num
  ring

/-- $L(1, \psi) = \pi/(2\sqrt2)$ for $\psi = \left(\frac{-8}\cdot\right)$ (class number formula, $h = 1$, $w = 2$). -/
theorem LFunction_psiNeg8_one : psiNeg8.LFunction 1 = ((π / (2 * Real.sqrt 2) : ℝ) : ℂ) := by
  have h := classNumberFormula_neg (D := -8) (by norm_num)
  rw [classNumber_QField_neg_eight, torsionOrder_of_neg (by norm_num)] at h
  rw [show psiNeg8.LFunction 1 = (kroneckerChar (-8)).LFunction 1 from rfl, h]
  congr 1
  have : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  norm_num [this]
  ring

theorem psiNeg3_ne_one : psiNeg3 ≠ 1 := by
  intro h
  have := congrArg (fun χ : DirichletCharacter ℂ 3 => χ ((2 : ℕ) : ZMod 3)) h
  simp only [psiNeg3_natCast] at this
  rw [MulChar.one_apply (by decide)] at this
  norm_num at this

theorem psiNeg8_ne_one : psiNeg8 ≠ 1 := by
  intro h
  have := congrArg (fun χ : DirichletCharacter ℂ 8 => χ ((5 : ℕ) : ZMod 8)) h
  simp only [psiNeg8_natCast] at this
  rw [MulChar.one_apply (by decide)] at this
  norm_num [chiD] at this

/-- The value at $s = 1$ of $L(s,\psi)\prod_{p \mid 12}(1 - \psi(p)p^{-s})$, $\psi = \left(\frac{-3}\cdot\right)$:
$\frac{\pi}{3\sqrt3}\cdot\frac32 = \frac{\pi}{2\sqrt3}$. -/
theorem neg_three_one_value :
    psiNeg3.LFunction 1 * ∏ p ∈ (4 * (-3 : ℤ).natAbs).primeFactors, (1 - psiNeg3 p * (p : ℂ) ^ (-(1 : ℂ))) =
      ((π / (2 * Real.sqrt 3) : ℝ) : ℂ) := by
  rw [LFunction_psiNeg3_one, show 4 * (-3 : ℤ).natAbs = 12 from rfl, primeFactors_twelve,
    Finset.prod_insert (by decide), Finset.prod_singleton, psiNeg3_natCast, psiNeg3_natCast,
    Complex.cpow_neg_one, Complex.cpow_neg_one]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  norm_num
  field_simp

/-- **§1, p. 260 ($d = 3$, $s = 1$, $D = -3$), value of $\zeta_{-3}$**: $\zeta_{-3}(1) = \pi/(2\sqrt3)$ (the analytic
continuation at $s = 1$; the series itself is `tendsto_zetaD_neg_three_one`). -/
@[kb "conwaysloane1988" "§1, p. 260; §8, Table 6, p. 270 (d = 3, s = 1)"]
theorem zetaD_neg_three_one : zetaD (-3) 1 = π / (2 * Real.sqrt 3) := by
  have hD : (-3 : ℤ) ≠ 0 := by norm_num
  rw [zetaD_eq hD, Complex.ofReal_one,
    LD_eq_LFunction_mul hD psiNeg3 _ chiD_eq_changeLevel_neg3 (Or.inl psiNeg3_ne_one), neg_three_one_value,
    Complex.ofReal_re]

open Filter Topology QuadFormsKB.Binary.EulerOne in
/-- **§1, p. 260**: $1 - \frac15 + \frac17 - \frac1{11} + \frac1{13} - \cdots = \frac{\pi}{2\sqrt3}$, i.e. the partial sums
$\sum_{m < M}\left(\frac{-3}{m}\right)/m$ over odd $m$ (the terms $\chi_{-3}(m)/m$, zero for even $m$ and for $3 \mid m$)
converge to $\pi/(2\sqrt3)$ (Dirichlet's class number formula for $\mathbb Q(\sqrt{-3})$, $h = 1$, $w = 6$, and the Euler
factor $1 + \frac12$ at $p = 2$). -/
@[kb "conwaysloane1988" "§1, p. 260"]
theorem tendsto_zetaD_neg_three_one :
    Tendsto (fun M : ℕ => ∑ m ∈ range M, (chiD (-3) m : ℝ) / m) atTop (𝓝 (π / (2 * Real.sqrt 3))) := by
  have hD : (-3 : ℤ) ≠ 0 := by norm_num
  have := neZero_four_natAbs hD
  set χ := DirichletCharacter.changeLevel (show 3 ∣ 4 * (-3 : ℤ).natAbs by decide) psiNeg3 with hχdef
  have hval : ∀ n : ℕ, χ n = (chiD (-3) n : ℂ) := fun n => (chiD_eq_changeLevel_neg3 n).symm
  have hne : χ ≠ 1 := by
    intro h
    have h5 := hval 5
    rw [h, MulChar.one_apply ((ZMod.isUnit_iff_coprime 5 _).mpr (by norm_num))] at h5
    norm_num [chiD] at h5
  have hL : χ.LFunction 1 = ((π / (2 * Real.sqrt 3) : ℝ) : ℂ) := by
    rw [hχdef, DirichletCharacter.LFunction_changeLevel _ _ (Or.inl psiNeg3_ne_one), neg_three_one_value]
  have hpart : ∀ M : ℕ, lpart χ M 1 = ((∑ m ∈ range M, (chiD (-3) m : ℝ) / m : ℝ) : ℂ) := by
    intro M
    unfold lpart
    push_cast
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hval]
    unfold wpow
    split_ifs with hm
    · simp [hm]
    · rw [Real.rpow_neg_one]; push_cast; ring
  have h1 : Tendsto (fun M : ℕ => lpart χ M 1) atTop (𝓝 (χ.LFunction 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun M => norm_nonneg _) (fun M => norm_lpart_one_sub_LFunction_le χ hne M) ?_
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (4 * ((4 * (-3 : ℤ).natAbs : ℕ) : ℝ))
  rw [hL] at h1
  simp_rw [hpart] at h1
  have := (Complex.continuous_re.tendsto _).comp h1
  rw [Complex.ofReal_re] at this
  refine this.congr (fun M => ?_)
  simp only [Function.comp_apply, Complex.ofReal_re]

/-- **Table 6, $d = 3$, $s = 1$** ($D = -3$): $\zeta_{-3}(1)\sqrt3/\pi = \tfrac12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 1)"]
theorem table6_3_1 : zetaD (-3) 1 * Real.sqrt 3 / π = 1 / 2 := by
  rw [zetaD_neg_three_one]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-2}(1) = \pi/(2\sqrt2)$ ($1 + \frac13 - \frac15 - \frac17 + \cdots$; class number formula for
$\mathbb Q(\sqrt{-2})$, $h = 1$, $w = 2$). -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 1)"]
theorem zetaD_neg_two_one : zetaD (-2) 1 = π / (2 * Real.sqrt 2) := by
  have hD : (-2 : ℤ) ≠ 0 := by norm_num
  rw [zetaD_eq hD, Complex.ofReal_one,
    LD_eq_LFunction_mul hD psiNeg8 _ chiD_eq_changeLevel_neg2 (Or.inl psiNeg8_ne_one),
    eulerFactor_eq_one _ (fun p hp => by
      have : p ∣ 4 * (-2 : ℤ).natAbs := Nat.dvd_of_mem_primeFactors hp
      simpa using this), LFunction_psiNeg8_one, ← Complex.ofReal_mul, Complex.ofReal_re, mul_one]

/-- **Table 6, $d = 2$, $s = 1$** ($D = -2$): $\zeta_{-2}(1)\sqrt2/\pi = \tfrac12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 1)"]
theorem table6_2_1 : zetaD (-2) 1 * Real.sqrt 2 / π = 1 / 2 := by
  rw [zetaD_neg_two_one]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- **Table 6, $d = 1$, $s = 1$** ($D = -1$): $\zeta_{-1}(1)/\pi = \tfrac14$ (Leibniz, `zetaD_neg_one_one`). -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 1)"]
theorem table6_1_1 : zetaD (-1) 1 / π = 1 / 4 := by
  rw [zetaD_neg_one_one]
  field_simp

/-! ### The entries of Table 6 for $s \ge 2$ -/

/-- **Table 6, $d = 1$, $s = 2$** ($D = 1$, from (15)): $\zeta_1(2)/\pi^{2} = 1/8$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 2)"]
theorem table6_1_2 : zetaD 1 2 / π ^ 2 = 1 / 8 := by
  rw [show zetaD 1 2 / π ^ 2 = zetaD 1 ((2 * 1 : ℕ) : ℝ) / π ^ (2 * 1) by norm_num,
    table6_one_even (by norm_num)]
  norm_num [bv_2]

/-- **Table 6, $d = 1$, $s = 3$** ($D = -1$): $\zeta_{-1}(3)/\pi^{3} = 1/32$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 3)"]
theorem table6_1_3 : zetaD (-1) 3 / π ^ 3 = 1 / 32 := by
  rw [show zetaD (-1) 3 / π ^ 3 =
      zetaD (-1) ((3 : ℕ) : ℝ) / π ^ 3 by norm_num,
    table6_neg_one_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 1$, $s = 4$** ($D = 1$, from (15)): $\zeta_1(4)/\pi^{4} = 1/96$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 4)"]
theorem table6_1_4 : zetaD 1 4 / π ^ 4 = 1 / 96 := by
  rw [show zetaD 1 4 / π ^ 4 = zetaD 1 ((2 * 2 : ℕ) : ℝ) / π ^ (2 * 2) by norm_num,
    table6_one_even (by norm_num)]
  norm_num [bv_4]

/-- **Table 6, $d = 1$, $s = 5$** ($D = -1$): $\zeta_{-1}(5)/\pi^{5} = 5/1536$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 5)"]
theorem table6_1_5 : zetaD (-1) 5 / π ^ 5 = 5 / 1536 := by
  rw [show zetaD (-1) 5 / π ^ 5 =
      zetaD (-1) ((5 : ℕ) : ℝ) / π ^ 5 by norm_num,
    table6_neg_one_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 1$, $s = 6$** ($D = 1$, from (15)): $\zeta_1(6)/\pi^{6} = 1/960$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 6)"]
theorem table6_1_6 : zetaD 1 6 / π ^ 6 = 1 / 960 := by
  rw [show zetaD 1 6 / π ^ 6 = zetaD 1 ((2 * 3 : ℕ) : ℝ) / π ^ (2 * 3) by norm_num,
    table6_one_even (by norm_num)]
  norm_num [bv_6]

/-- **Table 6, $d = 1$, $s = 7$** ($D = -1$): $\zeta_{-1}(7)/\pi^{7} = 61/184320$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 7)"]
theorem table6_1_7 : zetaD (-1) 7 / π ^ 7 = 61 / 184320 := by
  rw [show zetaD (-1) 7 / π ^ 7 =
      zetaD (-1) ((7 : ℕ) : ℝ) / π ^ 7 by norm_num,
    table6_neg_one_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 1$, $s = 8$** ($D = 1$, from (15)): $\zeta_1(8)/\pi^{8} = 17/161280$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 8)"]
theorem table6_1_8 : zetaD 1 8 / π ^ 8 = 17 / 161280 := by
  rw [show zetaD 1 8 / π ^ 8 = zetaD 1 ((2 * 4 : ℕ) : ℝ) / π ^ (2 * 4) by norm_num,
    table6_one_even (by norm_num)]
  norm_num [bv_8]

/-- **Table 6, $d = 1$, $s = 9$** ($D = -1$): $\zeta_{-1}(9)/\pi^{9} = 277/8257536$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 1, s = 9)"]
theorem table6_1_9 : zetaD (-1) 9 / π ^ 9 = 277 / 8257536 := by
  rw [show zetaD (-1) 9 / π ^ 9 =
      zetaD (-1) ((9 : ℕ) : ℝ) / π ^ 9 by norm_num,
    table6_neg_one_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 1$, $s = 10$** ($D = 1$, from (15)): $\zeta_1(10)/\pi^{10} = 31/2903040$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 1, s = 10)"]
theorem table6_1_10 : zetaD 1 10 / π ^ 10 = 31 / 2903040 := by
  rw [show zetaD 1 10 / π ^ 10 = zetaD 1 ((2 * 5 : ℕ) : ℝ) / π ^ (2 * 5) by norm_num,
    table6_one_even (by norm_num)]
  norm_num [bv_10]

/-- **Table 6, $d = 1$, $s = 11$** ($D = -1$): $\zeta_{-1}(11)/\pi^{11} = 50521/14863564800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 1, s = 11)"]
theorem table6_1_11 : zetaD (-1) 11 / π ^ 11 = 50521 / 14863564800 := by
  rw [show zetaD (-1) 11 / π ^ 11 =
      zetaD (-1) ((11 : ℕ) : ℝ) / π ^ 11 by norm_num,
    table6_neg_one_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 1$, $s = 12$** ($D = 1$, from (15)): $\zeta_1(12)/\pi^{12} = 691/638668800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 1, s = 12)"]
theorem table6_1_12 : zetaD 1 12 / π ^ 12 = 691 / 638668800 := by
  rw [show zetaD 1 12 / π ^ 12 = zetaD 1 ((2 * 6 : ℕ) : ℝ) / π ^ (2 * 6) by norm_num,
    table6_one_even (by norm_num)]
  norm_num [bv_12]

/-- **Table 6, $d = 2$, $s = 2$** ($D = 2$): $\zeta_{2}(2)\,2^{1}\sqrt{2}/\pi^{2} = 1/4$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 2)"]
theorem table6_2_2 : zetaD 2 2 * 2 ^ 1 * Real.sqrt 2 / π ^ 2 = 1 / 4 := by
  rw [show zetaD 2 2 * 2 ^ 1 * Real.sqrt 2 / π ^ 2 =
      zetaD 2 ((2 : ℕ) : ℝ) * 2 ^ (2 - 1) * Real.sqrt 2 / π ^ 2 by norm_num,
    table6_two_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 3$** ($D = -2$): $\zeta_{-2}(3)\,2^{2}\sqrt{2}/\pi^{3} = 3/16$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 3)"]
theorem table6_2_3 : zetaD (-2) 3 * 2 ^ 2 * Real.sqrt 2 / π ^ 3 = 3 / 16 := by
  rw [show zetaD (-2) 3 * 2 ^ 2 * Real.sqrt 2 / π ^ 3 =
      zetaD (-2) ((3 : ℕ) : ℝ) * 2 ^ (3 - 1) * Real.sqrt 2 / π ^ 3 by norm_num,
    table6_neg_two_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 4$** ($D = 2$): $\zeta_{2}(4)\,2^{3}\sqrt{2}/\pi^{4} = 11/96$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 4)"]
theorem table6_2_4 : zetaD 2 4 * 2 ^ 3 * Real.sqrt 2 / π ^ 4 = 11 / 96 := by
  rw [show zetaD 2 4 * 2 ^ 3 * Real.sqrt 2 / π ^ 4 =
      zetaD 2 ((4 : ℕ) : ℝ) * 2 ^ (4 - 1) * Real.sqrt 2 / π ^ 4 by norm_num,
    table6_two_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 5$** ($D = -2$): $\zeta_{-2}(5)\,2^{4}\sqrt{2}/\pi^{5} = 19/256$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 5)"]
theorem table6_2_5 : zetaD (-2) 5 * 2 ^ 4 * Real.sqrt 2 / π ^ 5 = 19 / 256 := by
  rw [show zetaD (-2) 5 * 2 ^ 4 * Real.sqrt 2 / π ^ 5 =
      zetaD (-2) ((5 : ℕ) : ℝ) * 2 ^ (5 - 1) * Real.sqrt 2 / π ^ 5 by norm_num,
    table6_neg_two_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 6$** ($D = 2$): $\zeta_{2}(6)\,2^{5}\sqrt{2}/\pi^{6} = 361/7680$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 6)"]
theorem table6_2_6 : zetaD 2 6 * 2 ^ 5 * Real.sqrt 2 / π ^ 6 = 361 / 7680 := by
  rw [show zetaD 2 6 * 2 ^ 5 * Real.sqrt 2 / π ^ 6 =
      zetaD 2 ((6 : ℕ) : ℝ) * 2 ^ (6 - 1) * Real.sqrt 2 / π ^ 6 by norm_num,
    table6_two_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 7$** ($D = -2$): $\zeta_{-2}(7)\,2^{6}\sqrt{2}/\pi^{7} = 307/10240$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 7)"]
theorem table6_2_7 : zetaD (-2) 7 * 2 ^ 6 * Real.sqrt 2 / π ^ 7 = 307 / 10240 := by
  rw [show zetaD (-2) 7 * 2 ^ 6 * Real.sqrt 2 / π ^ 7 =
      zetaD (-2) ((7 : ℕ) : ℝ) * 2 ^ (7 - 1) * Real.sqrt 2 / π ^ 7 by norm_num,
    table6_neg_two_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 8$** ($D = 2$): $\zeta_{2}(8)\,2^{7}\sqrt{2}/\pi^{8} = 24611/1290240$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 2, s = 8)"]
theorem table6_2_8 : zetaD 2 8 * 2 ^ 7 * Real.sqrt 2 / π ^ 8 = 24611 / 1290240 := by
  rw [show zetaD 2 8 * 2 ^ 7 * Real.sqrt 2 / π ^ 8 =
      zetaD 2 ((8 : ℕ) : ℝ) * 2 ^ (8 - 1) * Real.sqrt 2 / π ^ 8 by norm_num,
    table6_two_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 9$** ($D = -2$): $\zeta_{-2}(9)\,2^{8}\sqrt{2}/\pi^{9} = 83579/6881280$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 2, s = 9)"]
theorem table6_2_9 : zetaD (-2) 9 * 2 ^ 8 * Real.sqrt 2 / π ^ 9 = 83579 / 6881280 := by
  rw [show zetaD (-2) 9 * 2 ^ 8 * Real.sqrt 2 / π ^ 9 =
      zetaD (-2) ((9 : ℕ) : ℝ) * 2 ^ (9 - 1) * Real.sqrt 2 / π ^ 9 by norm_num,
    table6_neg_two_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 10$** ($D = 2$): $\zeta_{2}(10)\,2^{9}\sqrt{2}/\pi^{10} = 2873041/371589120$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 2, s = 10)"]
theorem table6_2_10 : zetaD 2 10 * 2 ^ 9 * Real.sqrt 2 / π ^ 10 = 2873041 / 371589120 := by
  rw [show zetaD 2 10 * 2 ^ 9 * Real.sqrt 2 / π ^ 10 =
      zetaD 2 ((10 : ℕ) : ℝ) * 2 ^ (10 - 1) * Real.sqrt 2 / π ^ 10 by norm_num,
    table6_two_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 11$** ($D = -2$): $\zeta_{-2}(11)\,2^{10}\sqrt{2}/\pi^{11} = 12193841/2477260800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 2, s = 11)"]
theorem table6_2_11 : zetaD (-2) 11 * 2 ^ 10 * Real.sqrt 2 / π ^ 11 = 12193841 / 2477260800 := by
  rw [show zetaD (-2) 11 * 2 ^ 10 * Real.sqrt 2 / π ^ 11 =
      zetaD (-2) ((11 : ℕ) : ℝ) * 2 ^ (11 - 1) * Real.sqrt 2 / π ^ 11 by norm_num,
    table6_neg_two_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 2$, $s = 12$** ($D = 2$): $\zeta_{2}(12)\,2^{11}\sqrt{2}/\pi^{12} = 512343611/163499212800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 2, s = 12)"]
theorem table6_2_12 : zetaD 2 12 * 2 ^ 11 * Real.sqrt 2 / π ^ 12 = 512343611 / 163499212800 := by
  rw [show zetaD 2 12 * 2 ^ 11 * Real.sqrt 2 / π ^ 12 =
      zetaD 2 ((12 : ℕ) : ℝ) * 2 ^ (12 - 1) * Real.sqrt 2 / π ^ 12 by norm_num,
    table6_two_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 2$** ($D = 3$): $\zeta_{3}(2)\,3^{1}\sqrt{3}/\pi^{2} = 1/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 2)"]
theorem table6_3_2 : zetaD 3 2 * 3 ^ 1 * Real.sqrt 3 / π ^ 2 = 1 / 2 := by
  rw [show zetaD 3 2 * 3 ^ 1 * Real.sqrt 3 / π ^ 2 =
      zetaD 3 ((2 : ℕ) : ℝ) * 3 ^ (2 - 1) * Real.sqrt 3 / π ^ 2 by norm_num,
    table6_three_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 3$** ($D = -3$): $\zeta_{-3}(3)\,3^{2}\sqrt{3}/\pi^{3} = 1/2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 3)"]
theorem table6_3_3 : zetaD (-3) 3 * 3 ^ 2 * Real.sqrt 3 / π ^ 3 = 1 / 2 := by
  rw [show zetaD (-3) 3 * 3 ^ 2 * Real.sqrt 3 / π ^ 3 =
      zetaD (-3) ((3 : ℕ) : ℝ) * 3 ^ (3 - 1) * Real.sqrt 3 / π ^ 3 by norm_num,
    table6_neg_three_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 4$** ($D = 3$): $\zeta_{3}(4)\,3^{3}\sqrt{3}/\pi^{4} = 23/48$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 4)"]
theorem table6_3_4 : zetaD 3 4 * 3 ^ 3 * Real.sqrt 3 / π ^ 4 = 23 / 48 := by
  rw [show zetaD 3 4 * 3 ^ 3 * Real.sqrt 3 / π ^ 4 =
      zetaD 3 ((4 : ℕ) : ℝ) * 3 ^ (4 - 1) * Real.sqrt 3 / π ^ 4 by norm_num,
    table6_three_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 5$** ($D = -3$): $\zeta_{-3}(5)\,3^{4}\sqrt{3}/\pi^{5} = 11/24$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 5)"]
theorem table6_3_5 : zetaD (-3) 5 * 3 ^ 4 * Real.sqrt 3 / π ^ 5 = 11 / 24 := by
  rw [show zetaD (-3) 5 * 3 ^ 4 * Real.sqrt 3 / π ^ 5 =
      zetaD (-3) ((5 : ℕ) : ℝ) * 3 ^ (5 - 1) * Real.sqrt 3 / π ^ 5 by norm_num,
    table6_neg_three_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 6$** ($D = 3$): $\zeta_{3}(6)\,3^{5}\sqrt{3}/\pi^{6} = 1681/3840$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 6)"]
theorem table6_3_6 : zetaD 3 6 * 3 ^ 5 * Real.sqrt 3 / π ^ 6 = 1681 / 3840 := by
  rw [show zetaD 3 6 * 3 ^ 5 * Real.sqrt 3 / π ^ 6 =
      zetaD 3 ((6 : ℕ) : ℝ) * 3 ^ (6 - 1) * Real.sqrt 3 / π ^ 6 by norm_num,
    table6_three_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 7$** ($D = -3$): $\zeta_{-3}(7)\,3^{6}\sqrt{3}/\pi^{7} = 301/720$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 7)"]
theorem table6_3_7 : zetaD (-3) 7 * 3 ^ 6 * Real.sqrt 3 / π ^ 7 = 301 / 720 := by
  rw [show zetaD (-3) 7 * 3 ^ 6 * Real.sqrt 3 / π ^ 7 =
      zetaD (-3) ((7 : ℕ) : ℝ) * 3 ^ (7 - 1) * Real.sqrt 3 / π ^ 7 by norm_num,
    table6_neg_three_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 8$** ($D = 3$): $\zeta_{3}(8)\,3^{7}\sqrt{3}/\pi^{8} = 257543/645120$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 3, s = 8)"]
theorem table6_3_8 : zetaD 3 8 * 3 ^ 7 * Real.sqrt 3 / π ^ 8 = 257543 / 645120 := by
  rw [show zetaD 3 8 * 3 ^ 7 * Real.sqrt 3 / π ^ 8 =
      zetaD 3 ((8 : ℕ) : ℝ) * 3 ^ (8 - 1) * Real.sqrt 3 / π ^ 8 by norm_num,
    table6_three_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 9$** ($D = -3$): $\zeta_{-3}(9)\,3^{8}\sqrt{3}/\pi^{9} = 15371/40320$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 3, s = 9)"]
theorem table6_3_9 : zetaD (-3) 9 * 3 ^ 8 * Real.sqrt 3 / π ^ 9 = 15371 / 40320 := by
  rw [show zetaD (-3) 9 * 3 ^ 8 * Real.sqrt 3 / π ^ 9 =
      zetaD (-3) ((9 : ℕ) : ℝ) * 3 ^ (9 - 1) * Real.sqrt 3 / π ^ 9 by norm_num,
    table6_neg_three_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 10$** ($D = 3$): $\zeta_{3}(10)\,3^{9}\sqrt{3}/\pi^{10} = 67637281/185794560$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 3, s = 10)"]
theorem table6_3_10 : zetaD 3 10 * 3 ^ 9 * Real.sqrt 3 / π ^ 10 = 67637281 / 185794560 := by
  rw [show zetaD 3 10 * 3 ^ 9 * Real.sqrt 3 / π ^ 10 =
      zetaD 3 ((10 : ℕ) : ℝ) * 3 ^ (10 - 1) * Real.sqrt 3 / π ^ 10 by norm_num,
    table6_three_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 11$** ($D = -3$): $\zeta_{-3}(11)\,3^{10}\sqrt{3}/\pi^{11} = 1261501/3628800$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 3, s = 11)"]
theorem table6_3_11 : zetaD (-3) 11 * 3 ^ 10 * Real.sqrt 3 / π ^ 11 = 1261501 / 3628800 := by
  rw [show zetaD (-3) 11 * 3 ^ 10 * Real.sqrt 3 / π ^ 11 =
      zetaD (-3) ((11 : ℕ) : ℝ) * 3 ^ (11 - 1) * Real.sqrt 3 / π ^ 11 by norm_num,
    table6_neg_three_odd (by norm_num) (by norm_num)]
  bernoulli_eval

/-- **Table 6, $d = 3$, $s = 12$** ($D = 3$): $\zeta_{3}(12)\,3^{11}\sqrt{3}/\pi^{12} = 27138236663/81749606400$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 271 (d = 3, s = 12)"]
theorem table6_3_12 : zetaD 3 12 * 3 ^ 11 * Real.sqrt 3 / π ^ 12 = 27138236663 / 81749606400 := by
  rw [show zetaD 3 12 * 3 ^ 11 * Real.sqrt 3 / π ^ 12 =
      zetaD 3 ((12 : ℕ) : ℝ) * 3 ^ (12 - 1) * Real.sqrt 3 / π ^ 12 by norm_num,
    table6_three_even (by norm_num) (by norm_num)]
  bernoulli_eval

/-! ### §1, p. 260: $d = D = 2$, $s = 6$ -/

/-- **§1, p. 260**: $1 - 3^{-6} - 5^{-6} + 7^{-6} + 9^{-6} - \cdots = \zeta_2(6) = \dfrac{361\pi^6}{245760\sqrt2}$
(the series is `hasSum_zetaD`; the value is Table 6, $d = 2$, $s = 6$). -/
@[kb "conwaysloane1988" "§1, p. 260"]
theorem zetaD_two_six : zetaD 2 6 = 361 * π ^ 6 / (245760 * Real.sqrt 2) := by
  have h := table6_2_6
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hπ : π ^ 6 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp at h ⊢
  nlinarith [h, h22]

end QuadFormsKB.ConwaySloane.Mass
