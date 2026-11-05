/-
# Conway–Sloane 1988: the standard mass (§7, (7)–(16), §8 Table 3, and the identities of §1)

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`). Section 7, formula (7), p. 266, defines the *standard mass* $\mathrm{std}(f)$ of a quadratic
form $f$ of dimension $n$ and determinant $d$; Table 3, p. 267, lists it for $n \le 25$.

**Conventions (book $\to$ Lean).**
* The book's "$(D/m)$ is a Jacobi symbol" is `jacobiSym D m`. The character $\chi_D$ is `chiD D : ℕ → ℤ`, extended by
  $\chi_D(m) = 0$ for even $m$ (the book sums only over odd $m$, so that even $m$ contribute nothing).
* The book's $\zeta_D(s) = \sum_{m = 1, 3, 5, \dots} (D/m)\, m^{-s}$ ((9), p. 266) is `zetaD D s` (real $s$). For $s > 1$ this
  is the sum of the series (`hasSum_zetaD`); for the other $s$ (the book needs $s = 1$ in dimension $n = 2$, where the series
  converges only conditionally) it is the real part of Mathlib's analytic continuation `ZMod.LFunction` of the periodic
  function $m \mapsto \chi_D(m)$ modulo $4\lvert D\rvert$. For $D = 0$ it is set to $0$ (the book never uses it).
* The dimension is `n : ℕ`, the determinant `d : ℤ`. The book's $s$ with "$n = 2s$ or $n = 2s - 1$" is the natural number
  `(n + 1) / 2` (rounded-down division), and $D = (-1)^s d$.
* Zeta values at even integers are `(riemannZeta (2 * i)).re`; $\Gamma$ is `Real.Gamma`; Bernoulli numbers are Mathlib's
  `bernoulli` ($B_1 = -\tfrac12$, irrelevant here as only even indices occur).

**Proves**
* `chiD_mul`, `chiD_mod`, `chiD_add_period`: $\chi_D$ is completely multiplicative and periodic modulo $4\lvert D\rvert$.
* `hasSum_zetaD` ((9)): for real $s > 1$ the series $\sum_m \chi_D(m) m^{-s}$ sums to $\zeta_D(s)$.
* `eulerProduct_zetaD` ((8)): for real $s > 1$, $\zeta_D(s) = \prod_p (1 - \chi_D(p)\,p^{-s})^{-1}$ over all primes $p$ (as a
  `HasProd`).
* `zetaD_four_mul`, `zetaD_cube_mul` ((14)): $\zeta_{4D} = \zeta_D$ and $\zeta_{p^3 D} = \zeta_{pD}$ for all real $s \ne 1$ (analytic
  continuation); `zetaD_four_mul_one`, `zetaD_cube_mul_one` give $s = 1$ under the hypothesis that the periodic functions have
  sum zero over a period (i.e. $D$ is not a square, when the L-function is entire).
* `zetaD_one_eq` ((15)): $\zeta_1(s) = (1 - 2^{-s})\,\zeta(s)$ for $s > 1$; `zetaD_one_even` ((15), even $s = 2k$):
  $\zeta_1(2k) = (1 - 2^{-2k})\,(2\pi)^{2k} \lvert B_{2k}\rvert / (2\,(2k)!)$.
* `zetaD_one_four` (§1, p. 260): $1 + 3^{-4} + 5^{-4} + 7^{-4} + \cdots = \pi^4/96$.
* `stdMass` ((7)), the closed forms `stdMass_odd`, `stdMass_even` and every entry of Table 3 (`stdMass_table_1`, …,
  `stdMass_table_25`), with the rational constants `cStd n` computed from `gR` ($\Gamma$ values) and `zR` (Bernoulli numbers).

**Elsewhere.** (16) (Euler numbers) is proved in `EulerNumbers.lean` (`zetaD_neg_one_euler`, odd $s \le 11$); the
evaluation $\zeta_{-3}(1) = \pi/(2\sqrt3)$ in `Table6.lean` (`zetaD_neg_three_one`); (11)–(13) in `ZetaFormula.lean`.

**Table 3 check.** The printed rational constants of Table 3 were recomputed independently (exact fractions) from (7) for
$1 \le n \le 25$ and agree with the printed values in every case; the Lean statements below are the printed values.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.MassCheck

open scoped Real

namespace QuadFormsKB.ConwaySloane.Mass

/-! ### Bernoulli numbers $B_2, \dots, B_{24}$ (by the recursion `sum_bernoulli'`) -/

theorem bz_3 : bernoulli' 3 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_5 : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_7 : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_9 : bernoulli' 9 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_11 : bernoulli' 11 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_13 : bernoulli' 13 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_15 : bernoulli' 15 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_17 : bernoulli' 17 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_19 : bernoulli' 19 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_21 : bernoulli' 21 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bz_23 : bernoulli' 23 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bp_2 : bernoulli' 2 = 1 / 6 := by simp
theorem bp_4 : bernoulli' 4 = -1 / 30 := by simp
theorem bp_6 : bernoulli' 6 = 1 / 42 := QuadFormsKB.Tamagawa.bernoulli'_six

theorem bp_8 : bernoulli' 8 = -1 / 30 := by
  have h := sum_bernoulli' 9
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bp_2, bp_4, bp_6] at h
  linarith

theorem bp_10 : bernoulli' 10 = 5 / 66 := by
  have h := sum_bernoulli' 11
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bp_2, bp_4, bp_6, bp_8] at h
  linarith

theorem bp_12 : bernoulli' 12 = -691 / 2730 := by
  have h := sum_bernoulli' 13
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bz_11, bp_2, bp_4, bp_6, bp_8, bp_10] at h
  linarith

theorem bp_14 : bernoulli' 14 = 7 / 6 := by
  have h := sum_bernoulli' 15
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bz_11, bz_13, bp_2, bp_4, bp_6, bp_8, bp_10, bp_12] at h
  linarith

theorem bp_16 : bernoulli' 16 = -3617 / 510 := by
  have h := sum_bernoulli' 17
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bz_11, bz_13, bz_15, bp_2, bp_4, bp_6, bp_8, bp_10, bp_12, bp_14] at h
  linarith

theorem bp_18 : bernoulli' 18 = 43867 / 798 := by
  have h := sum_bernoulli' 19
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bz_11, bz_13, bz_15, bz_17, bp_2, bp_4, bp_6, bp_8, bp_10, bp_12, bp_14, bp_16] at h
  linarith

theorem bp_20 : bernoulli' 20 = -174611 / 330 := by
  have h := sum_bernoulli' 21
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bz_11, bz_13, bz_15, bz_17, bz_19, bp_2, bp_4, bp_6, bp_8, bp_10, bp_12, bp_14, bp_16, bp_18] at h
  linarith

theorem bp_22 : bernoulli' 22 = 854513 / 138 := by
  have h := sum_bernoulli' 23
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bz_11, bz_13, bz_15, bz_17, bz_19, bz_21, bp_2, bp_4, bp_6, bp_8, bp_10, bp_12, bp_14, bp_16, bp_18, bp_20] at h
  linarith

theorem bp_24 : bernoulli' 24 = -236364091 / 2730 := by
  have h := sum_bernoulli' 25
  norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, bernoulli'_zero, bernoulli'_one, bz_3, bz_5, bz_7, bz_9, bz_11, bz_13, bz_15, bz_17, bz_19, bz_21, bz_23, bp_2, bp_4, bp_6, bp_8, bp_10, bp_12, bp_14, bp_16, bp_18, bp_20, bp_22] at h
  linarith

theorem bv_2 : bernoulli 2 = 1 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_2]

theorem bv_4 : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_4]

theorem bv_6 : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_6]

theorem bv_8 : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_8]

theorem bv_10 : bernoulli 10 = 5 / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_10]

theorem bv_12 : bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_12]

theorem bv_14 : bernoulli 14 = 7 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_14]

theorem bv_16 : bernoulli 16 = -3617 / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_16]

theorem bv_18 : bernoulli 18 = 43867 / 798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_18]

theorem bv_20 : bernoulli 20 = -174611 / 330 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_20]

theorem bv_22 : bernoulli 22 = 854513 / 138 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_22]

theorem bv_24 : bernoulli 24 = -236364091 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bp_24]


/-! ### The character $\chi_D$ -/

/-- The character $\chi_D$ of Conway–Sloane (9), p. 266: $\chi_D(m) = \left(\tfrac{D}{m}\right)$ (the Jacobi symbol `jacobiSym D m`)
for odd $m$, and $\chi_D(m) = 0$ for even $m$ (including $m = 0$). -/
@[kb "conwaysloane1988" "§7 (9), p. 266; §8, p. 267"]
def chiD (D : ℤ) (m : ℕ) : ℤ := if m % 2 = 0 then 0 else jacobiSym D m

theorem chiD_zero (D : ℤ) : chiD D 0 = 0 := by simp [chiD]

theorem chiD_one (D : ℤ) : chiD D 1 = 1 := by simp [chiD, jacobiSym.one_right]

theorem chiD_trichotomy (D : ℤ) (m : ℕ) : chiD D m = 0 ∨ chiD D m = 1 ∨ chiD D m = -1 := by
  unfold chiD
  split_ifs
  · exact Or.inl rfl
  · exact jacobiSym.trichotomy D m

theorem abs_chiD_le_one (D : ℤ) (m : ℕ) : |(chiD D m : ℝ)| ≤ 1 := by
  rcases chiD_trichotomy D m with h | h | h <;> simp [h]

/-- $\chi_D$ is completely multiplicative. -/
@[kb "conwaysloane1988" "§7 (9), p. 266"]
theorem chiD_mul (D : ℤ) (m n : ℕ) : chiD D (m * n) = chiD D m * chiD D n := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have : (m * n) % 2 = 0 := by rw [Nat.mul_mod, hm]; simp
    simp [chiD, hm, this]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have : (m * n) % 2 = 0 := by rw [Nat.mul_mod, hn]; simp
    simp [chiD, hn, this]
  have hmn : (m * n) % 2 = 1 := by rw [Nat.mul_mod, hm, hn]
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  simp only [chiD, hm, hn, hmn, one_ne_zero, ↓reduceIte]
  exact jacobiSym.mul_right' D hm0 hn0

/-- $\chi_D(m)$ depends only on $m$ modulo $4\lvert D\rvert$. -/
@[kb "conwaysloane1988" "§7 (9), p. 266"]
theorem chiD_mod (D : ℤ) (m : ℕ) : chiD D (m % (4 * D.natAbs)) = chiD D m := by
  have h2 : (m % (4 * D.natAbs)) % 2 = m % 2 :=
    Nat.mod_mod_of_dvd m (Dvd.dvd.mul_right (by norm_num) _)
  unfold chiD
  rw [h2]
  split_ifs with h
  · rfl
  · have hodd : Odd m := Nat.odd_iff.mpr (by omega)
    exact (jacobiSym.mod_right D hodd).symm

/-- $\chi_D$ is periodic with period $4\lvert D\rvert$. -/
@[kb "conwaysloane1988" "§7 (9), p. 266"]
theorem chiD_add_period (D : ℤ) (m : ℕ) : chiD D (m + 4 * D.natAbs) = chiD D m := by
  rw [← chiD_mod D (m + 4 * D.natAbs), Nat.add_mod_right, chiD_mod]

/-- For $4D$ the character is unchanged: $\chi_{4D} = \chi_D$. -/
theorem chiD_four_mul (D : ℤ) (m : ℕ) : chiD (4 * D) m = chiD D m := by
  unfold chiD
  split_ifs with h
  · rfl
  · have hodd : Odd m := Nat.odd_iff.mpr (by omega)
    have hg : (2 : ℤ).gcd (m : ℤ) = 1 := by
      have : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hodd
      show Int.gcd ((2 : ℕ) : ℤ) (m : ℤ) = 1
      rw [Int.gcd_natCast_natCast]
      exact this
    rw [jacobiSym.mul_left, show (4 : ℤ) = 2 ^ 2 by norm_num, jacobiSym.sq_one' hg, one_mul]

/-- $\chi_{p^3 D} = \chi_{pD}$. -/
theorem chiD_cube_mul (p D : ℤ) (m : ℕ) : chiD (p ^ 3 * D) m = chiD (p * D) m := by
  unfold chiD
  split_ifs with h
  · rfl
  · rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left]
    rcases jacobiSym.trichotomy p m with h | h | h <;> simp [h]

/-! ### The function $\zeta_D$ -/

/-- The periodic function $\chi_D$ on `ZMod (4 * |D|)`. -/
noncomputable def Phi (D : ℤ) : ZMod (4 * D.natAbs) → ℂ := fun x => (chiD D x.val : ℂ)

theorem Phi_natCast (D : ℤ) (n : ℕ) : Phi D (n : ZMod (4 * D.natAbs)) = (chiD D n : ℂ) := by
  unfold Phi
  rw [ZMod.val_natCast, chiD_mod]

/-- The sum of $\chi_D$ over one period $\mathbb Z/4\lvert D\rvert$ (the L-function is entire iff this is $0$). -/
noncomputable def PhiSum (D : ℤ) (hD : D ≠ 0) : ℂ :=
  haveI : NeZero (4 * D.natAbs) := ⟨by have := Int.natAbs_pos.mpr hD; omega⟩
  ∑ j, Phi D j

theorem neZero_four_natAbs {D : ℤ} (hD : D ≠ 0) : NeZero (4 * D.natAbs) :=
  ⟨by have := Int.natAbs_pos.mpr hD; omega⟩

/-- The complex L-function $s \mapsto \sum_{m\ \mathrm{odd}} \chi_D(m) m^{-s}$ (analytically continued to all
$s \in \mathbb C$), for $D \ne 0$. -/
noncomputable def LD (D : ℤ) (hD : D ≠ 0) (s : ℂ) : ℂ :=
  haveI := neZero_four_natAbs hD
  ZMod.LFunction (Phi D) s

/-- **The function $\zeta_D(s)$** of Conway–Sloane (9), p. 266, $\zeta_D(s) = \sum_{m = 1, 3, 5, \dots} (D/m)\,m^{-s}$, for real
$s$ and nonzero integer $D$: the real part of the analytic continuation `LD D` (so it is also defined at $s = 1$).
For $D = 0$ it is $0$. -/
@[kb "conwaysloane1988" "§7 (9), p. 266"]
noncomputable def zetaD (D : ℤ) (s : ℝ) : ℝ :=
  if h : D = 0 then 0 else (LD D h (s : ℂ)).re

theorem zetaD_eq {D : ℤ} (hD : D ≠ 0) (s : ℝ) : zetaD D s = (LD D hD (s : ℂ)).re := by
  simp [zetaD, hD]

theorem LD_eq_LSeries {D : ℤ} (hD : D ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LD D hD s = LSeries (fun n => (chiD D n : ℂ)) s := by
  haveI := neZero_four_natAbs hD
  unfold LD
  rw [ZMod.LFunction_eq_LSeries _ hs]
  congr 1
  funext n
  exact Phi_natCast D n

/-- **(9)**: for real $s > 1$, $\zeta_D(s) = \sum_{m} \chi_D(m)\, m^{-s}$ (sum over all $m \ge 0$; even $m$ contribute $0$). -/
@[kb "conwaysloane1988" "§7 (9), p. 266"]
theorem hasSum_zetaD {D : ℤ} (hD : D ≠ 0) {s : ℝ} (hs : 1 < s) :
    HasSum (fun m : ℕ => (chiD D m : ℝ) / (m : ℝ) ^ s) (zetaD D s) := by
  haveI := neZero_four_natAbs hD
  have hre : 1 < (s : ℂ).re := by simpa using hs
  have hsum : LSeriesSummable (fun n => (chiD D n : ℂ)) (s : ℂ) := by
    have := ZMod.LSeriesSummable_of_one_lt_re (Phi D) hre
    have e : (fun n : ℕ => Phi D (n : ZMod (4 * D.natAbs))) = fun n => (chiD D n : ℂ) :=
      funext (Phi_natCast D)
    simpa [e] using this
  have key : ∀ n : ℕ, (LSeries.term (fun n => (chiD D n : ℂ)) (s : ℂ) n).re
      = (chiD D n : ℝ) / (n : ℝ) ^ s := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [chiD_zero]
    · rw [LSeries.term_of_ne_zero hn.ne']
      have h1 : ((n : ℂ) ^ (s : ℂ)) = (((n : ℝ) ^ s : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
      have h2 : ((chiD D n : ℤ) : ℂ) = (((chiD D n : ℤ) : ℝ) : ℂ) := by simp
      rw [h1, h2, ← Complex.ofReal_div, Complex.ofReal_re]
  have h := Complex.reCLM.hasSum hsum.hasSum
  have h' : HasSum (fun n : ℕ => (chiD D n : ℝ) / (n : ℝ) ^ s)
      (∑' n : ℕ, LSeries.term (fun n => (chiD D n : ℂ)) (s : ℂ) n).re := by
    simpa [key] using h
  rw [zetaD_eq hD, LD_eq_LSeries hD hre]
  exact h'

/-- The completely multiplicative function $m \mapsto \chi_D(m)\,m^{-s}$ (real $s$). -/
noncomputable def chiTerm (D : ℤ) (s : ℝ) : ℕ →*₀ ℝ where
  toFun n := (chiD D n : ℝ) * (n : ℝ) ^ (-s)
  map_zero' := by simp [chiD_zero]
  map_one' := by simp [chiD_one]
  map_mul' m n := by
    rw [chiD_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    push_cast
    ring

theorem summable_chiTerm (D : ℤ) {s : ℝ} (hs : 1 < s) : Summable (fun n => ‖chiTerm D s n‖) := by
  have hsm : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsm
  show ‖(chiD D n : ℝ) * (n : ℝ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_chiD_le_one D n)

/-- **(8), the Euler product**: for real $s > 1$,
$\zeta_D(s) = \prod_{p\ \mathrm{prime}} \bigl(1 - \chi_D(p)\,p^{-s}\bigr)^{-1}$, where $\chi_D(p) = (D/p)$ for odd $p$ and
$\chi_D(2) = 0$ (so the factor at $p = 2$ is $1$). -/
@[kb "conwaysloane1988" "§7 (8), p. 266"]
theorem eulerProduct_zetaD {D : ℤ} (hD : D ≠ 0) {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => (1 - (chiD D p : ℝ) * (p : ℝ) ^ (-s))⁻¹) (zetaD D s) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_chiTerm D hs)
  have hsum : HasSum (fun n : ℕ => chiTerm D s n) (zetaD D s) := by
    have := hasSum_zetaD hD hs
    refine this.congr_fun ?_
    intro n
    show (chiD D n : ℝ) * (n : ℝ) ^ (-s) = (chiD D n : ℝ) / (n : ℝ) ^ s
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  rw [hsum.tsum_eq] at h
  exact h

/-! ### (14): $\zeta_{4D} = \zeta_D$ and $\zeta_{p^3 D} = \zeta_{pD}$ -/

theorem LD_congr {D D' : ℤ} (hD : D ≠ 0) (hD' : D' ≠ 0) (h : ∀ m, chiD D m = chiD D' m)
    {s : ℂ} (hs : s ≠ 1) : LD D hD s = LD D' hD' s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) := by
    refine (isConnected_compl_singleton_of_one_lt_rank ?_ _).isPreconnected
    rw [Complex.rank_real_complex]; norm_num
  have hdiff : ∀ (E : ℤ) (hE : E ≠ 0), AnalyticOnNhd ℂ (LD E hE) ({1}ᶜ : Set ℂ) := by
    intro E hE
    haveI := neZero_four_natAbs hE
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (ZMod.differentiableAt_LFunction (Phi E) z (Or.inl hz)).differentiableWithinAt
  have hev : LD D hD =ᶠ[nhds (2 : ℂ)] LD D' hD' := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    rw [LD_eq_LSeries hD hz, LD_eq_LSeries hD' hz]
    have : (fun n : ℕ => (chiD D n : ℂ)) = fun n => (chiD D' n : ℂ) := by
      funext n; rw [h n]
    rw [this]
  exact (hdiff D hD).eqOn_of_preconnected_of_eventuallyEq (hdiff D' hD') hconn
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by simp) hev hs

theorem LD_congr_one {D D' : ℤ} (hD : D ≠ 0) (hD' : D' ≠ 0) (h : ∀ m, chiD D m = chiD D' m)
    (h0 : PhiSum D hD = 0) (h0' : PhiSum D' hD' = 0) : LD D hD 1 = LD D' hD' 1 := by
  haveI := neZero_four_natAbs hD
  haveI := neZero_four_natAbs hD'
  have h0 : ∑ j, Phi D j = 0 := h0
  have h0' : ∑ j, Phi D' j = 0 := h0'
  have c1 : ContinuousAt (LD D hD) 1 :=
    (ZMod.differentiableAt_LFunction (Phi D) 1 (Or.inr h0)).continuousAt
  have c2 : ContinuousAt (LD D' hD') 1 :=
    (ZMod.differentiableAt_LFunction (Phi D') 1 (Or.inr h0')).continuousAt
  have t1 := c1.tendsto.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
  have t2 := c2.tendsto.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
  have heq : LD D hD =ᶠ[nhdsWithin (1 : ℂ) {1}ᶜ] LD D' hD' := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact LD_congr hD hD' h hz
  exact tendsto_nhds_unique (t1.congr' heq) t2

/-- **(14)**: $\zeta_{4D}(s) = \zeta_D(s)$ for every real $s \ne 1$ (and $D \ne 0$). -/
@[kb "conwaysloane1988" "§7 (14), p. 266"]
theorem zetaD_four_mul {D : ℤ} (hD : D ≠ 0) {s : ℝ} (hs : s ≠ 1) : zetaD (4 * D) s = zetaD D s := by
  have h4 : 4 * D ≠ 0 := mul_ne_zero (by norm_num) hD
  rw [zetaD_eq h4, zetaD_eq hD,
    LD_congr h4 hD (chiD_four_mul D) (by exact_mod_cast hs)]

/-- **(14) at $s = 1$**: $\zeta_{4D}(1) = \zeta_D(1)$, provided both periodic functions have sum zero over a period (so that
the L-functions are entire; this holds when $D$ is not a square). -/
@[kb "conwaysloane1988" "§7 (14), p. 266"]
theorem zetaD_four_mul_one {D : ℤ} (hD : D ≠ 0) (h4 : 4 * D ≠ 0) (h0 : PhiSum D hD = 0)
    (h0' : PhiSum (4 * D) h4 = 0) : zetaD (4 * D) 1 = zetaD D 1 := by
  rw [zetaD_eq h4, zetaD_eq hD, Complex.ofReal_one,
    LD_congr_one h4 hD (chiD_four_mul D) h0' h0]

/-- **(14)**: $\zeta_{p^3 D}(s) = \zeta_{pD}(s)$ for every real $s \ne 1$, for any nonzero integer $p$ (in particular an
odd prime) and $D \ne 0$. (The exponent is $3$; note $pD \ne 0$.) -/
@[kb "conwaysloane1988" "§7 (14), p. 266"]
theorem zetaD_cube_mul {p D : ℤ} (hp : p ≠ 0) (hD : D ≠ 0) {s : ℝ} (hs : s ≠ 1) :
    zetaD (p ^ 3 * D) s = zetaD (p * D) s := by
  have h3 : p ^ 3 * D ≠ 0 := mul_ne_zero (pow_ne_zero 3 hp) hD
  have h1 : p * D ≠ 0 := mul_ne_zero hp hD
  rw [zetaD_eq h3, zetaD_eq h1,
    LD_congr h3 h1 (chiD_cube_mul p D) (by exact_mod_cast hs)]

/-- **(14) at $s = 1$** for $p^3 D$ versus $pD$, under the sum-zero hypotheses (see `zetaD_four_mul_one`). -/
@[kb "conwaysloane1988" "§7 (14), p. 266"]
theorem zetaD_cube_mul_one {p D : ℤ} (hp : p ≠ 0) (hD : D ≠ 0)
    (h0 : PhiSum (p ^ 3 * D) (mul_ne_zero (pow_ne_zero 3 hp) hD) = 0)
    (h0' : PhiSum (p * D) (mul_ne_zero hp hD) = 0) : zetaD (p ^ 3 * D) 1 = zetaD (p * D) 1 := by
  have h3 : p ^ 3 * D ≠ 0 := mul_ne_zero (pow_ne_zero 3 hp) hD
  have h1 : p * D ≠ 0 := mul_ne_zero hp hD
  rw [zetaD_eq h3, zetaD_eq h1, Complex.ofReal_one,
    LD_congr_one h3 h1 (chiD_cube_mul p D) h0 h0']

/-! ### (15): $\zeta_1$ -/

theorem hasSum_zeta_re {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s) (riemannZeta (s : ℂ)).re := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s) := Real.summable_one_div_nat_rpow.mpr hs
  have hre : 1 < (s : ℂ).re := by simpa using hs
  have hc : ∀ n : ℕ, (1 : ℂ) / (n : ℂ) ^ (s : ℂ) = ((1 / (n : ℝ) ^ s : ℝ) : ℂ) := fun n => by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
  have : (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_cpow hre]
    simp_rw [hc]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [this]
  exact hsum.hasSum

/-- **(15)**: $\zeta_1(s) = (1 - 2^{-s})\,\zeta(s)$ for real $s > 1$ (the real part of the Riemann zeta function is the
value, which is real). -/
@[kb "conwaysloane1988" "§7 (15), p. 266"]
theorem zetaD_one_eq {s : ℝ} (hs : 1 < s) :
    zetaD 1 s = (1 - (2 : ℝ) ^ (-s)) * (riemannZeta (s : ℂ)).re := by
  set Z := (riemannZeta (s : ℂ)).re with hZ
  have hz := hasSum_zeta_re hs
  let e : ℕ → ℝ := fun m => if m % 2 = 0 then 1 / (m : ℝ) ^ s else 0
  have he : HasSum e ((2 : ℝ) ^ (-s) * Z) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
    rw [← hinj.hasSum_iff]
    · have h2 := hz.mul_left ((2 : ℝ) ^ (-s))
      refine h2.congr_fun ?_
      intro k
      show e (2 * k) = (2 : ℝ) ^ (-s) * (1 / (k : ℝ) ^ s)
      simp only [e]
      rw [if_pos (by omega), Nat.cast_mul, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _),
        Real.rpow_neg (by norm_num), Nat.cast_ofNat, one_div, one_div, mul_inv]
    · intro x hx
      simp only [e]
      rw [if_neg]
      intro h
      exact hx ⟨x / 2, by simp only; omega⟩
  have hdiff := hz.sub he
  have h9 := hasSum_zetaD (D := 1) one_ne_zero hs
  have : (fun m : ℕ => (chiD 1 m : ℝ) / (m : ℝ) ^ s) = fun m : ℕ => 1 / (m : ℝ) ^ s - e m := by
    funext m
    simp only [e, chiD]
    split_ifs with h
    · simp
    · simp [jacobiSym.one_left]
  rw [this] at h9
  rw [h9.unique hdiff]
  ring

theorem zeta_even_re {k : ℕ} (hk : k ≠ 0) :
    (riemannZeta (2 * (k : ℂ))).re
      = (-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) * 2 ^ (2 * k - 1) * π ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := by
  have h := riemannZeta_two_mul_nat hk
  have h2 : riemannZeta (2 * (k : ℂ)) = (((-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) * 2 ^ (2 * k - 1) * π ^ (2 * k)
      / (Nat.factorial (2 * k) : ℝ) : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  rw [h2, Complex.ofReal_re]

theorem zeta_even_pos {k : ℕ} : 0 < (riemannZeta (2 * (k : ℂ))).re ∨ k = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inr rfl
  · left
    have hs : (1 : ℝ) < ((2 * k : ℕ) : ℝ) := by
      have : (1 : ℕ) < 2 * k := by omega
      exact_mod_cast this
    have h := hasSum_zeta_re hs
    have e : ((((2 * k : ℕ) : ℝ) : ℂ)) = 2 * (k : ℂ) := by push_cast; ring
    rw [e] at h
    rw [← h.tsum_eq]
    refine h.summable.tsum_pos (fun n => by positivity) 1 ?_
    simp

/-- The real part of $\zeta(2k)$ as printed in the book: $\zeta(2k) = |B_{2k}|\,(2\pi)^{2k} / (2\,(2k)!)$. -/
theorem zeta_even_abs {k : ℕ} (hk : k ≠ 0) :
    (riemannZeta (2 * (k : ℂ))).re
      = |(bernoulli (2 * k) : ℝ)| * (2 * π) ^ (2 * k) / (2 * (Nat.factorial (2 * k) : ℝ)) := by
  have hpos : 0 < (riemannZeta (2 * (k : ℂ))).re := (zeta_even_pos (k := k)).resolve_right hk
  have h := zeta_even_re hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hf : (0 : ℝ) < (Nat.factorial (2 * (j + 1)) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hsign : (-1 : ℝ) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ) = |(bernoulli (2 * (j + 1)) : ℝ)| := by
    have hpos' : 0 < (-1 : ℝ) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ) := by
      rw [h] at hpos
      have h2 : (0 : ℝ) < 2 ^ (2 * (j + 1) - 1) * π ^ (2 * (j + 1)) := by positivity
      by_contra hneg
      push_neg at hneg
      have : (-1 : ℝ) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ) * 2 ^ (2 * (j + 1) - 1) * π ^ (2 * (j + 1))
          / (Nat.factorial (2 * (j + 1)) : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hf.le
        have := mul_nonpos_of_nonpos_of_nonneg hneg h2.le
        linarith [this]
      linarith
    have := abs_of_pos hpos'
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at this
    exact this.symm
  have step : (-1 : ℝ) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ) * 2 ^ (2 * (j + 1) - 1) * π ^ (2 * (j + 1))
      / (Nat.factorial (2 * (j + 1)) : ℝ)
      = ((-1 : ℝ) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ)) * (2 ^ (2 * (j + 1) - 1) * π ^ (2 * (j + 1)))
      / (Nat.factorial (2 * (j + 1)) : ℝ) := by ring
  rw [h, step, hsign]
  have e : (2 : ℝ) ^ (2 * (j + 1) - 1) = (2 : ℝ) ^ (2 * (j + 1)) / 2 := by
    rw [show 2 * (j + 1) = (2 * (j + 1) - 1) + 1 by omega, pow_succ]
    simp
  rw [mul_pow, e]
  field_simp

/-- **(15), even $s$**: $\zeta_1(2k) = (1 - 2^{-2k})\,(2\pi)^{2k}\,|B_{2k}| / (2\,(2k)!)$ for $k \ge 1$. -/
@[kb "conwaysloane1988" "§7 (15), p. 266"]
theorem zetaD_one_even {k : ℕ} (hk : k ≠ 0) :
    zetaD 1 ((2 * k : ℕ) : ℝ)
      = (1 - (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ))) * ((2 * π) ^ (2 * k) * |(bernoulli (2 * k) : ℝ)| /
          (2 * (Nat.factorial (2 * k) : ℝ))) := by
  have hs : (1 : ℝ) < ((2 * k : ℕ) : ℝ) := by
    have : (1 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  rw [zetaD_one_eq hs]
  have e : ((((2 * k : ℕ) : ℝ) : ℂ)) = 2 * (k : ℂ) := by push_cast; ring
  rw [e, zeta_even_abs hk]
  ring

/-- **§1, p. 260**: $1 + 3^{-4} + 5^{-4} + 7^{-4} + \cdots = \pi^4/96$, i.e. $\zeta_1(4) = \pi^4/96$. -/
@[kb "conwaysloane1988" "§1, p. 260"]
theorem zetaD_one_four : zetaD 1 4 = π ^ 4 / 96 := by
  have h := zetaD_one_eq (s := 4) (by norm_num)
  have hz : riemannZeta ((4 : ℝ) : ℂ) = (π : ℂ) ^ 4 / 90 := by
    rw [Complex.ofReal_ofNat]; exact riemannZeta_four
  have hr : (riemannZeta ((4 : ℝ) : ℂ)).re = π ^ 4 / 90 := by
    rw [hz]; norm_cast
  have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
    rw [Real.rpow_neg (by norm_num), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h, hr, h2]
  ring

/-! ### The standard mass (7) -/

/-- Rational factor from $\Gamma$: `hfac k` $= \Gamma(k + \tfrac12)/\sqrt\pi = (2k)!/(4^k k!)$ (by recursion). -/
def hfac : ℕ → ℚ
  | 0 => 1
  | k + 1 => ((k : ℚ) + 1 / 2) * hfac k

theorem gamma_nat_add_half (k : ℕ) : Real.Gamma ((k : ℝ) + 1 / 2) = (hfac k : ℝ) * √π := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_add]
    simp only [hfac, Rat.cast_one, one_mul]
    exact Real.Gamma_one_half_eq
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih]
    simp only [hfac]
    push_cast
    ring

/-- The rational part of $\prod_{j=1}^n \Gamma(j/2)$: `gR n` is defined by $\prod_{j=1}^{n}\Gamma(j/2) = $ `gR n` $\cdot\,
\pi^{\lceil n/2\rceil/2}$ (`prod_gamma`). Step $j = n + 1$: $\Gamma(k + \tfrac12)$ for $j = 2k+1$, $\Gamma(k) = (k-1)!$ for
$j = 2k$. -/
def gR : ℕ → ℚ
  | 0 => 1
  | n + 1 => gR n * (if n % 2 = 0 then hfac (n / 2) else ((n / 2).factorial : ℚ))

theorem prod_gamma (n : ℕ) :
    ∏ j ∈ Finset.Icc 1 n, Real.Gamma ((j : ℝ) / 2) = (gR n : ℝ) * √π ^ ((n + 1) / 2) := by
  induction n with
  | zero => simp [gR]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · have e1 : ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
      have hg : gR (2 * k + 1) = gR (2 * k) * hfac k := by
        rw [gR, if_pos (by omega)]
        congr 2
        omega
      rw [e1, gamma_nat_add_half, hg, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
        show (2 * k + 1) / 2 = k by omega, pow_succ]
      push_cast
      ring
    · have e1 : ((2 * k + 1 + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 := by push_cast; ring
      have hg : gR (2 * k + 1 + 1) = gR (2 * k + 1) * (k.factorial : ℚ) := by
        rw [gR, if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
      rw [e1, Real.Gamma_nat_eq_factorial, hg, show (2 * k + 1 + 1 + 1) / 2 = k + 1 by omega,
        show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      push_cast
      ring

/-- The rational coefficient of $\zeta(2k)$: $\zeta(2k) = $ `zc k` $\cdot \pi^{2k}$, `zc k` $= |B_{2k}|\,2^{2k}/(2\,(2k)!)$. -/
def zc (k : ℕ) : ℚ := |bernoulli (2 * k)| * 2 ^ (2 * k) / (2 * (2 * k).factorial)

/-- $\prod_{i=1}^{m}$ `zc i`, the rational part of $\zeta(2)\zeta(4)\cdots\zeta(2m)$. -/
def zR (m : ℕ) : ℚ := ∏ i ∈ Finset.range m, zc (i + 1)

theorem zeta_even_zc {k : ℕ} (hk : k ≠ 0) :
    (riemannZeta (2 * (k : ℂ))).re = (zc k : ℝ) * π ^ (2 * k) := by
  rw [zeta_even_abs hk, zc]
  push_cast
  rw [mul_pow]
  ring

theorem prod_zeta (m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (riemannZeta (2 * (i : ℂ))).re = (zR m : ℝ) * π ^ (m * (m + 1)) := by
  induction m with
  | zero => simp [zR]
  | succ m ih =>
    have hz : zR (m + 1) = zR m * zc (m + 1) := by simp [zR, Finset.prod_range_succ]
    rw [Finset.prod_Icc_succ_top (by omega), ih, zeta_even_zc (by omega), hz,
      show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring, pow_add]
    push_cast
    ring

/-- **The standard mass** (Conway–Sloane (7), p. 266) of a form of dimension $n$ and determinant $d$, with
$s = \lceil n/2 \rceil$ (`(n + 1) / 2`, so $n = 2s$ or $n = 2s - 1$) and $D = (-1)^s d$:
$$\mathrm{std}(n, d) = 2\,\pi^{-n(n+1)/4}\prod_{j=1}^{n}\Gamma(j/2)\;\zeta(2)\zeta(4)\cdots\zeta(2s-2)\;\cdot\;
\begin{cases}\zeta_D(s) & n\text{ even},\\ 1 & n\text{ odd}.\end{cases}$$ -/
@[kb "conwaysloane1988" "§7 (7), p. 266"]
noncomputable def stdMass (n : ℕ) (d : ℤ) : ℝ :=
  2 * π ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) * (∏ j ∈ Finset.Icc 1 n, Real.Gamma ((j : ℝ) / 2)) *
    (∏ i ∈ Finset.Icc 1 ((n + 1) / 2 - 1), (riemannZeta (2 * (i : ℂ))).re) *
    (if n % 2 = 0 then zetaD ((-1) ^ ((n + 1) / 2) * d) (((n + 1) / 2 : ℕ) : ℝ) else 1)

/-- The rational constant $c_n$ of the closed form of the standard mass:
$c_n = 2\prod_{j}\Gamma(j/2)/\pi^{\cdots}\cdot\prod_{i<s}\zeta(2i)/\pi^{2i}$, i.e. `2 * gR n * zR (s - 1)` with `s = (n+1)/2`;
`gR` records the factorials of the $\Gamma$ values and `zR` the Bernoulli numbers $|B_{2i}|2^{2i}/(2\,(2i)!)$. -/
def cStd (n : ℕ) : ℚ := 2 * gR n * zR ((n + 1) / 2 - 1)

theorem pi_aux (a : ℝ) (m u : ℕ) :
    π ^ a * √π ^ m * π ^ u = π ^ (a + (m : ℝ) / 2 + u) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (π ^ (1 / 2 : ℝ)) m, ← Real.rpow_mul Real.pi_pos.le,
    ← Real.rpow_natCast π u, ← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos]
  congr 1
  ring

/-- **Closed form, odd $n$**: $\mathrm{std}(n, d) = c_n$ (a rational number independent of $d$). -/
@[kb "conwaysloane1988" "§8, p. 267 (closed form of (7))"]
theorem stdMass_odd (n : ℕ) (d : ℤ) (hn : n % 2 = 1) : stdMass n d = (cStd n : ℝ) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t + 1 := ⟨n / 2, by omega⟩
  unfold stdMass
  rw [if_neg (by omega), prod_gamma, show (2 * t + 1 + 1) / 2 - 1 = t by omega, prod_zeta,
    show (2 * t + 1 + 1) / 2 = t + 1 by omega]
  have h := pi_aux (-(((2 * t + 1 : ℕ) : ℝ) * (((2 * t + 1 : ℕ) : ℝ) + 1)) / 4) (t + 1) (t * (t + 1))
  have h0 : -(((2 * t + 1 : ℕ) : ℝ) * (((2 * t + 1 : ℕ) : ℝ) + 1)) / 4 + ((t + 1 : ℕ) : ℝ) / 2
      + ((t * (t + 1) : ℕ) : ℝ) = 0 := by
    push_cast; ring
  rw [h0, Real.rpow_zero] at h
  have : cStd (2 * t + 1) = 2 * gR (2 * t + 1) * zR t := by
    rw [cStd, show (2 * t + 1 + 1) / 2 - 1 = t by omega]
  rw [this, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat]
  linear_combination (2 * (gR (2 * t + 1) : ℝ) * (zR t : ℝ)) * h

/-- **Closed form, even $n \ge 2$**: with $s = n/2$ and $D = (-1)^s d$,
$\mathrm{std}(n, d) = c_n\,\zeta_D(s)/\pi^{s}$. -/
@[kb "conwaysloane1988" "§8, p. 267 (closed form of (7))"]
theorem stdMass_even (n : ℕ) (d : ℤ) (hn : n % 2 = 0) (hpos : 0 < n) :
    stdMass n d = (cStd n : ℝ) * zetaD ((-1) ^ (n / 2) * d) ((n / 2 : ℕ) : ℝ) / π ^ (n / 2) := by
  obtain ⟨u, rfl⟩ : ∃ u, n = 2 * u + 2 := ⟨n / 2 - 1, by omega⟩
  unfold stdMass
  rw [if_pos (by omega), prod_gamma, show (2 * u + 2 + 1) / 2 - 1 = u by omega, prod_zeta,
    show (2 * u + 2 + 1) / 2 = u + 1 by omega, show (2 * u + 2) / 2 = u + 1 by omega]
  have h := pi_aux (-(((2 * u + 2 : ℕ) : ℝ) * (((2 * u + 2 : ℕ) : ℝ) + 1)) / 4) (u + 1) (u * (u + 1))
  have h0 : -(((2 * u + 2 : ℕ) : ℝ) * (((2 * u + 2 : ℕ) : ℝ) + 1)) / 4 + ((u + 1 : ℕ) : ℝ) / 2
      + ((u * (u + 1) : ℕ) : ℝ) = -((u + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [h0, Real.rpow_neg Real.pi_pos.le, Real.rpow_natCast] at h
  have : cStd (2 * u + 2) = 2 * gR (2 * u + 2) * zR u := by
    rw [cStd, show (2 * u + 2 + 1) / 2 - 1 = u by omega]
  rw [this, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat]
  have hp : (π : ℝ) ^ (u + 1) ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  have h' : π ^ (-(((2 * u + 2 : ℕ) : ℝ) * (((2 * u + 2 : ℕ) : ℝ) + 1)) / 4) * √π ^ (u + 1) * π ^ (u * (u + 1))
      * π ^ (u + 1) = 1 := by
    rw [h]; exact inv_mul_cancel₀ hp
  rw [eq_div_iff hp]
  linear_combination (2 * (gR (2 * u + 2) : ℝ) * (zR u : ℝ) * zetaD ((-1) ^ (u + 1) * d) ((u + 1 : ℕ) : ℝ)) * h'

/-! ### Table 3, p. 267: the standard mass for $n \le 25$

For odd $n$ the printed entry is the rational number $\mathrm{std}(n, d)$ (independent of $d$); for even $n = 2s$ the printed
entry is $c\,\zeta_D(s)/\pi^s$ with $D = (-1)^s d$. -/

theorem cStd_1 : cStd 1 = 2 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_2 : cStd 2 = 2 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_3 : cStd 3 = 1 / 6 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_4 : cStd 4 = 1 / 6 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_5 : cStd 5 = 1 / 720 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_6 : cStd 6 = 1 / 360 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_7 : cStd 7 = 1 / 181440 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_8 : cStd 8 = 1 / 30240 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_9 : cStd 9 = 1 / 43545600 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_10 : cStd 10 = 1 / 1814400 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_11 : cStd 11 = 1 / 5748019200 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_12 : cStd 12 = 1 / 47900160 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_13 : cStd 13 = 691 / 188305108992000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_14 : cStd 14 = 691 / 261534873600 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_15 : cStd 15 = 691 / 2259661307904000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_16 : cStd 16 = 691 / 448345497600 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_17 : cStd 17 = 2499347 / 18438836272496640000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_18 : cStd 18 = 2499347 / 457312407552000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_19 : cStd 19 = 109638854849 / 264855444218141736960000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_20 : cStd 20 = 109638854849 / 729870602452992000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_21 : cStd 21 = 19144150084038739 / 1748045931839735463936000000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_22 : cStd 22 = 19144150084038739 / 481714597618974720000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_23 : cStd 23 = 1487175010978381361737 / 482460677187766988046336000000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_24 : cStd 24 = 1487175010978381361737 / 12086657176621547520000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]

theorem cStd_25 : cStd 25 = 351514769627820131218308186067 / 31610823569342493056795934720000000 := by
  norm_num [cStd, gR, zR, zc, hfac, Finset.prod_range_succ, bv_2, bv_4, bv_6, bv_8, bv_10, bv_12, bv_14, bv_16, bv_18, bv_20, bv_22, bv_24]


@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_1 (d : ℤ) : stdMass 1 d = 2 := by
  rw [stdMass_odd 1 d (by norm_num), cStd_1]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_2 (d : ℤ) :
    stdMass 2 d = (2 : ℝ) * zetaD ((-1) ^ 1 * d) 1 / π ^ 1 := by
  rw [stdMass_even 2 d (by norm_num) (by norm_num), cStd_2]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_3 (d : ℤ) : stdMass 3 d = 1 / 6 := by
  rw [stdMass_odd 3 d (by norm_num), cStd_3]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_4 (d : ℤ) :
    stdMass 4 d = (1 / 6 : ℝ) * zetaD ((-1) ^ 2 * d) 2 / π ^ 2 := by
  rw [stdMass_even 4 d (by norm_num) (by norm_num), cStd_4]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_5 (d : ℤ) : stdMass 5 d = 1 / 720 := by
  rw [stdMass_odd 5 d (by norm_num), cStd_5]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_6 (d : ℤ) :
    stdMass 6 d = (1 / 360 : ℝ) * zetaD ((-1) ^ 3 * d) 3 / π ^ 3 := by
  rw [stdMass_even 6 d (by norm_num) (by norm_num), cStd_6]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_7 (d : ℤ) : stdMass 7 d = 1 / 181440 := by
  rw [stdMass_odd 7 d (by norm_num), cStd_7]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_8 (d : ℤ) :
    stdMass 8 d = (1 / 30240 : ℝ) * zetaD ((-1) ^ 4 * d) 4 / π ^ 4 := by
  rw [stdMass_even 8 d (by norm_num) (by norm_num), cStd_8]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_9 (d : ℤ) : stdMass 9 d = 1 / 43545600 := by
  rw [stdMass_odd 9 d (by norm_num), cStd_9]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_10 (d : ℤ) :
    stdMass 10 d = (1 / 1814400 : ℝ) * zetaD ((-1) ^ 5 * d) 5 / π ^ 5 := by
  rw [stdMass_even 10 d (by norm_num) (by norm_num), cStd_10]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_11 (d : ℤ) : stdMass 11 d = 1 / 5748019200 := by
  rw [stdMass_odd 11 d (by norm_num), cStd_11]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_12 (d : ℤ) :
    stdMass 12 d = (1 / 47900160 : ℝ) * zetaD ((-1) ^ 6 * d) 6 / π ^ 6 := by
  rw [stdMass_even 12 d (by norm_num) (by norm_num), cStd_12]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_13 (d : ℤ) : stdMass 13 d = 691 / 188305108992000 := by
  rw [stdMass_odd 13 d (by norm_num), cStd_13]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_14 (d : ℤ) :
    stdMass 14 d = (691 / 261534873600 : ℝ) * zetaD ((-1) ^ 7 * d) 7 / π ^ 7 := by
  rw [stdMass_even 14 d (by norm_num) (by norm_num), cStd_14]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_15 (d : ℤ) : stdMass 15 d = 691 / 2259661307904000 := by
  rw [stdMass_odd 15 d (by norm_num), cStd_15]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_16 (d : ℤ) :
    stdMass 16 d = (691 / 448345497600 : ℝ) * zetaD ((-1) ^ 8 * d) 8 / π ^ 8 := by
  rw [stdMass_even 16 d (by norm_num) (by norm_num), cStd_16]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_17 (d : ℤ) : stdMass 17 d = 2499347 / 18438836272496640000 := by
  rw [stdMass_odd 17 d (by norm_num), cStd_17]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_18 (d : ℤ) :
    stdMass 18 d = (2499347 / 457312407552000 : ℝ) * zetaD ((-1) ^ 9 * d) 9 / π ^ 9 := by
  rw [stdMass_even 18 d (by norm_num) (by norm_num), cStd_18]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_19 (d : ℤ) : stdMass 19 d = 109638854849 / 264855444218141736960000 := by
  rw [stdMass_odd 19 d (by norm_num), cStd_19]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_20 (d : ℤ) :
    stdMass 20 d = (109638854849 / 729870602452992000 : ℝ) * zetaD ((-1) ^ 10 * d) 10 / π ^ 10 := by
  rw [stdMass_even 20 d (by norm_num) (by norm_num), cStd_20]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_21 (d : ℤ) : stdMass 21 d = 19144150084038739 / 1748045931839735463936000000 := by
  rw [stdMass_odd 21 d (by norm_num), cStd_21]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_22 (d : ℤ) :
    stdMass 22 d = (19144150084038739 / 481714597618974720000 : ℝ) * zetaD ((-1) ^ 11 * d) 11 / π ^ 11 := by
  rw [stdMass_even 22 d (by norm_num) (by norm_num), cStd_22]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_23 (d : ℤ) : stdMass 23 d = 1487175010978381361737 / 482460677187766988046336000000 := by
  rw [stdMass_odd 23 d (by norm_num), cStd_23]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_24 (d : ℤ) :
    stdMass 24 d = (1487175010978381361737 / 12086657176621547520000 : ℝ) * zetaD ((-1) ^ 12 * d) 12 / π ^ 12 := by
  rw [stdMass_even 24 d (by norm_num) (by norm_num), cStd_24]
  norm_num

@[kb "conwaysloane1988" "Table 3, p. 267"]
theorem stdMass_table_25 (d : ℤ) : stdMass 25 d = 351514769627820131218308186067 / 31610823569342493056795934720000000 := by
  rw [stdMass_odd 25 d (by norm_num), cStd_25]
  norm_num


end QuadFormsKB.ConwaySloane.Mass
