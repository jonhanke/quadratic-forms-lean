/-
# Conway–Sloane 1988, §8, (16) for all odd $s$: Euler numbers and Bernoulli polynomials

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, formula (16), p. 268.

**Notation.** $E_n$ = `eulerNum n` (Euler numbers, $\operatorname{sech} t = \sum E_n t^n/n!$); $B_m(x)$ =
`Polynomial.bernoulli m` evaluated at $x$ (Bernoulli polynomials); $\zeta_{-1}(s)$ = `zetaD (-1) s`.

**Proves**
* `bernoulli_eval_add`: the addition formula $B_N(x+y) = \sum_{k=0}^N\binom Nk B_{N-k}(x)\,y^k$.
* `eulerNum_eq_bernoulli`: for every $n \ge 0$,
  $E_n = -\dfrac{4^{n+1}}{2(n+1)}\bigl(B_{n+1}(\tfrac14) - B_{n+1}(\tfrac34)\bigr)$.
  The right-hand side satisfies the defining recurrence of the Euler numbers (addition formula at $x = \frac14, \frac34$,
  $y = \frac14$) and the statement follows by strong induction.
* `zetaD_neg_one_euler_all`: (16) for **every** odd $s \ge 1$ (extends `zetaD_neg_one_euler`, which covers $s \le 11$),
  from the closed form (13) `zetaD_neg_one_odd` and the nonnegativity of $\zeta_D$ (for the absolute value).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.EulerNumbers
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6Abs

namespace QuadFormsKB.ConwaySloane.Mass

open Finset Polynomial
open scoped Real

theorem natDegree_bernoulli_le (N : ℕ) : (Polynomial.bernoulli N).natDegree ≤ N := by
  unfold Polynomial.bernoulli
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)

theorem iterate_derivative_bernoulli (N k : ℕ) :
    (Polynomial.derivative)^[k] (Polynomial.bernoulli N) =
      (N.descFactorial k : ℚ) • Polynomial.bernoulli (N - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_smul, Polynomial.derivative_bernoulli,
      Nat.descFactorial_succ, show N - (k + 1) = N - k - 1 by omega]
    simp only [smul_eq_C_mul, Nat.cast_mul, map_mul, map_natCast]
    ring

/-- **Addition formula for Bernoulli polynomials**: for $N \in \mathbb N$ and $x, y \in \mathbb Q$,
$$B_N(x+y) = \sum_{k=0}^{N}\binom Nk B_{N-k}(x)\,y^k.$$ -/
theorem bernoulli_eval_add (N : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli N).eval (x + y) =
      ∑ k ∈ range (N + 1), (N.choose k : ℚ) * (Polynomial.bernoulli (N - k)).eval x * y ^ k := by
  have h := Polynomial.taylor_eval x (Polynomial.bernoulli N) y
  rw [add_comm x y, ← h, Polynomial.eval_eq_sum_range' (n := N + 1)]
  · refine sum_congr rfl fun k _ => ?_
    rw [Polynomial.taylor_coeff]
    have h1 : ((k.factorial : ℕ) • Polynomial.hasseDeriv k (Polynomial.bernoulli N)) =
        (Polynomial.derivative)^[k] (Polynomial.bernoulli N) := by
      simpa using congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℚ) (k := k))
        (Polynomial.bernoulli N)
    rw [iterate_derivative_bernoulli, Nat.descFactorial_eq_factorial_mul_choose] at h1
    have h2 := congrArg (Polynomial.eval x) h1
    simp only [Polynomial.eval_smul, nsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Polynomial.eval_mul, Polynomial.eval_natCast] at h2
    have h3 : (Polynomial.hasseDeriv k (Polynomial.bernoulli N)).eval x =
        (N.choose k : ℚ) * (Polynomial.bernoulli (N - k)).eval x := by
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero : (k.factorial : ℚ) ≠ 0)
      linear_combination h2
    rw [h3]
  · rw [Polynomial.natDegree_taylor]
    exact Nat.lt_succ_of_le (natDegree_bernoulli_le N)

/-- The weighted sum $\sum_{m=0}^N\binom Nm 4^m\bigl(B_m(\frac14) - B_m(\frac34)\bigr)$ equals
$4^N\bigl(B_N(\frac12) - B_N(1)\bigr)$. -/
theorem sum_choose_four_pow_bernoulli (N : ℕ) :
    ∑ m ∈ range (N + 1), (N.choose m : ℚ) * 4 ^ m *
        ((Polynomial.bernoulli m).eval (1 / 4) - (Polynomial.bernoulli m).eval (3 / 4)) =
      4 ^ N * ((Polynomial.bernoulli N).eval (1 / 2) - (Polynomial.bernoulli N).eval 1) := by
  have key : ∀ x : ℚ, 4 ^ N * (Polynomial.bernoulli N).eval (x + 1 / 4) =
      ∑ m ∈ range (N + 1), (N.choose m : ℚ) * 4 ^ m * (Polynomial.bernoulli m).eval x := by
    intro x
    rw [bernoulli_eval_add, mul_sum]
    conv_rhs => rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k < N + 1 := mem_range.mp hk
    have e1 : N + 1 - 1 - k = N - k := by omega
    rw [e1, Nat.choose_symm (by omega)]
    have h4 : (4 : ℚ) ^ N = 4 ^ (N - k) * 4 ^ k := by rw [← pow_add]; congr 1; omega
    have h5 : (4 : ℚ) ^ k * (1 / 4) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [h4]
    linear_combination ((N.choose k : ℚ) * (Polynomial.bernoulli (N - k)).eval x * 4 ^ (N - k)) * h5
  have h1 := key (1 / 4)
  have h2 := key (3 / 4)
  rw [show (1 / 4 : ℚ) + 1 / 4 = 1 / 2 by norm_num] at h1
  rw [show (3 / 4 : ℚ) + 1 / 4 = 1 by norm_num] at h2
  simp only [mul_sub, sum_sub_distrib, ← h1, ← h2]

/-- For odd $N \ge 3$, $\sum_{m=0}^N\binom Nm 4^m\bigl(B_m(\frac14) - B_m(\frac34)\bigr) = 0$, since
$B_N(\frac12) = 0$ (reflection) and $B_N(1) = B_N = 0$. -/
theorem sum_choose_four_pow_bernoulli_odd {N : ℕ} (hN : N % 2 = 1) (h3 : 3 ≤ N) :
    ∑ m ∈ range (N + 1), (N.choose m : ℚ) * 4 ^ m *
        ((Polynomial.bernoulli m).eval (1 / 4) - (Polynomial.bernoulli m).eval (3 / 4)) = 0 := by
  rw [sum_choose_four_pow_bernoulli]
  have h1 : (Polynomial.bernoulli N).eval (1 / 2) = 0 := by
    have := Polynomial.bernoulli_eval_one_sub N (1 / 2)
    rw [show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num, Odd.neg_one_pow (Nat.odd_iff.mpr hN)] at this
    linarith
  have h2 : (Polynomial.bernoulli N).eval 1 = 0 := by
    rw [Polynomial.bernoulli_eval_one]
    exact bernoulli'_eq_zero_of_odd (Nat.odd_iff.mpr hN) (by omega)
  rw [h1, h2]; simp

/-- The rational number $-\dfrac{4^{n+1}}{2(n+1)}\bigl(B_{n+1}(\tfrac14) - B_{n+1}(\tfrac34)\bigr)$, which equals the Euler
number $E_n$ (`eulerNum_eq_bernoulli`); $n \in \mathbb N$ is the index. -/
noncomputable def eulerBernoulli (n : ℕ) : ℚ :=
  -(4 ^ (n + 1) / (2 * ((n : ℚ) + 1))) *
    ((Polynomial.bernoulli (n + 1)).eval (1 / 4) - (Polynomial.bernoulli (n + 1)).eval (3 / 4))

/-- The recurrence $\sum_{k=0}^{n}\binom nk a_k = 0$ for `eulerBernoulli` $= a$, $n \ge 2$ even. -/
theorem eulerBernoulli_rec {n : ℕ} (hn : n % 2 = 0) (h2 : n ≠ 0) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * eulerBernoulli k = 0 := by
  have hs := sum_choose_four_pow_bernoulli_odd (N := n + 1) (by omega) (by omega)
  rw [sum_range_succ'] at hs
  simp only [Polynomial.bernoulli_zero, Polynomial.eval_one, sub_self, mul_zero, add_zero] at hs
  have hterm : ∀ k ∈ range (n + 1), (n.choose k : ℚ) * eulerBernoulli k =
      -(1 / (2 * ((n : ℚ) + 1))) * (((n + 1).choose (k + 1) : ℚ) * 4 ^ (k + 1) *
        ((Polynomial.bernoulli (k + 1)).eval (1 / 4) - (Polynomial.bernoulli (k + 1)).eval (3 / 4))) := by
    intro k _
    have hc : ((n : ℚ) + 1) * (n.choose k : ℚ) = ((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    have hc' : (((n + 1).choose (k + 1) : ℕ) : ℚ) = ((n : ℚ) + 1) * (n.choose k : ℚ) / ((k : ℚ) + 1) := by
      field_simp; linear_combination -hc
    rw [hc']
    unfold eulerBernoulli
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, hs, mul_zero]

/-- **Euler numbers via Bernoulli polynomials**: for every $n \ge 0$,
$$E_n = -\frac{4^{n+1}}{2(n+1)}\Bigl(B_{n+1}(\tfrac14) - B_{n+1}(\tfrac34)\Bigr),$$
with $E_n$ = `eulerNum n` and $B_m$ = `Polynomial.bernoulli m`. (For even $n$ this is
$E_n = -\frac{4^{n+1}}{n+1}B_{n+1}(\frac14)$; for odd $n$ both sides vanish.) -/
@[kb "conwaysloane1988" "§8 (16), p. 268 (Euler numbers via Bernoulli polynomials)"]
theorem eulerNum_eq_bernoulli (n : ℕ) :
    (eulerNum n : ℚ) = -(4 ^ (n + 1) / (2 * ((n : ℚ) + 1))) *
      ((Polynomial.bernoulli (n + 1)).eval (1 / 4) - (Polynomial.bernoulli (n + 1)).eval (3 / 4)) := by
  show (eulerNum n : ℚ) = eulerBernoulli n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n % 2 = 1
    · rw [eulerNum_odd hn]
      have := Polynomial.bernoulli_eval_one_sub (n + 1) (1 / 4)
      rw [show (1 : ℚ) - 1 / 4 = 3 / 4 by norm_num, Even.neg_one_pow (by
        rw [Nat.even_iff]; omega), one_mul] at this
      unfold eulerBernoulli
      rw [this]; simp
    · have hn0 : n % 2 = 0 := by omega
      by_cases hz : n = 0
      · subst hz
        unfold eulerBernoulli
        simp [eulerNum_zero, Polynomial.bernoulli_one]
        norm_num
      · have r := eulerBernoulli_rec hn0 hz
        have e : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (eulerNum k : ℚ) = 0 := by
          exact_mod_cast eulerNum_rec hn0 hz
        rw [sum_range_succ] at r e
        have hsum : ∑ k ∈ range n, (n.choose k : ℚ) * eulerBernoulli k =
            ∑ k ∈ range n, (n.choose k : ℚ) * (eulerNum k : ℚ) :=
          sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk)]
        rw [hsum] at r
        simp only [Nat.choose_self, Nat.cast_one, one_mul] at r e
        linarith

/-- **(16), p. 268, for every odd $s$**: for odd $s \ge 1$,
$$\zeta_{-1}(s) = 1 - 3^{-s} + 5^{-s} - \cdots = \frac{(\frac12\pi)^s}{2\,(s-1)!}\,\lvert E_{s-1}\rvert,$$
$E_n$ the Euler numbers (`eulerNum`). Proved from the closed form (13) (`zetaD_neg_one_odd`) and
`eulerNum_eq_bernoulli`; the absolute value comes from $\zeta_{-1}(s) \ge 0$ (`zetaD_nonneg`). -/
@[kb "conwaysloane1988" "§8 (16), p. 268 (all odd s)"]
theorem zetaD_neg_one_euler_all {s : ℕ} (hs : s % 2 = 1) :
    zetaD (-1) s = (π / 2) ^ s / (2 * (s - 1).factorial) * |(eulerNum (s - 1) : ℝ)| := by
  by_cases h1 : s = 1
  · subst h1
    exact zetaD_neg_one_euler (by simp)
  have h3 : 2 ≤ s := by omega
  have hz := zetaD_neg_one_odd h3 hs
  have hE := eulerNum_eq_bernoulli (s - 1)
  rw [show s - 1 + 1 = s by omega] at hE
  have hE' : (eulerNum (s - 1) : ℝ) = -(4 ^ s / (2 * (s : ℝ))) *
      (((Polynomial.bernoulli s).eval (1 / 4) - (Polynomial.bernoulli s).eval (3 / 4) : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hE
    simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] at this
    have hs' : ((s - 1 : ℕ) : ℝ) + 1 = s := by
      have : 1 ≤ s := by omega
      rw [Nat.cast_sub this]; simp
    rw [hs'] at this
    rw [this]
  set D : ℝ := (((Polynomial.bernoulli s).eval (1 / 4) - (Polynomial.bernoulli s).eval (3 / 4) : ℚ) : ℝ)
    with hD
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hfac : (s.factorial : ℝ) = s * (s - 1).factorial := by
    conv_lhs => rw [show s = (s - 1) + 1 by omega]
    rw [Nat.factorial_succ]; push_cast
    congr 1
    rw [Nat.cast_sub (by omega)]; simp
  have hD' : D = -(2 * s / 4 ^ s) * (eulerNum (s - 1) : ℝ) := by
    rw [hE']; field_simp
  set c : ℝ := (π / 2) ^ s / (2 * (s - 1).factorial) with hc
  have hcpos : 0 < c := by
    have : (0 : ℝ) < (s - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hmain : zetaD (-1) s = (-1) ^ (s / 2) * (c * (eulerNum (s - 1) : ℝ)) := by
    have h4 : (2 * π) ^ s = 4 ^ s * (π / 2) ^ s := by
      rw [← mul_pow]; congr 1; ring
    have hfpos : (0 : ℝ) < (s - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [hz, hD', hfac, hc, h4, pow_succ]
    field_simp
    ring
  have hnn : 0 ≤ zetaD (-1) s := zetaD_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 < s))
  rw [← abs_of_nonneg hnn, hmain, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hcpos]

end QuadFormsKB.ConwaySloane.Mass
