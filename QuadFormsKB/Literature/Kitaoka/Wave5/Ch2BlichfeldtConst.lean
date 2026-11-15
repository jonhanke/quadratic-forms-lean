/-
# Kitaoka 1993, §2.2 and §7.1: Blichfeldt's constant and its numerical bounds

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.2, Theorem 2.2.1, p. 42; §7.1, proofs of
Lemma 7.1.2 (p. 192) and Lemma 7.1.4 (p. 194).

Blichfeldt's estimate (Theorem 2.2.1, proved in `Ch2Blichfeldt.lean`) bounds Hermite's constant by
$b_m = \frac 2\pi\,\Gamma(2 + m/2)^{2/m}$. Kitaoka's proofs of Lemmas 7.1.2 and 7.1.4 reduce them to the
numerical inequalities proved here:

* `blichfeldtConst_lt_sqrt`: $b_r < \sqrt r$ for $2 \le r < 43$ (proof of Lemma 7.1.2, p. 192);
* `blichfeldtConst_lt_div_six`: $b_n < n/6$ for $n \ge 40$ (proof of Lemma 7.1.4, p. 194).

**Proof notes.** Kitaoka uses Stirling's upper bound for $\Gamma$ and a calculus argument. Here:
$b_r < \sqrt r$ is equivalent to $\Gamma(2 + r/2)^4 < (\pi^2 r/4)^r$; for each $r$ the value $\Gamma(2 + r/2)$ is an
explicit factorial quotient (times $\sqrt\pi$ for odd $r$) and the inequality is checked with $\pi > 3.141592$.
For $b_n < n/6$, equivalent to $\Gamma(2 + n/2)^4 < (\pi n/12)^{2n}$, induction from $n$ to $n + 2$
($\Gamma(3 + n/2) = (2 + n/2)\,\Gamma(2 + n/2)$, and $(1 + 2/n)^{2n}$ is bounded below by its first binomial terms),
with base cases $n = 40, 41$.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QuadFormsKB.Citation

noncomputable section

namespace QuadFormsKB.Kitaoka.Blichfeldt

/-- **Blichfeldt's constant** $b_m = \frac 2\pi\,\Gamma(2 + m/2)^{2/m}$ (Kitaoka 1993, §2.2, Theorem 2.2.1, p. 42):
the bound for Hermite's constant $\mu_m$ in Theorem 2.2.1 (`Ch2Blichfeldt.lean`). For $m = 0$ the exponent $2/m$ is
$0$ in Lean, so $b_0 = 2/\pi$ (not used). -/
@[kb "kitaoka1993" "§2.2, Thm. 2.2.1, p. 42 (the bound 2π⁻¹Γ(2+m/2)^{2/m})"]
def blichfeldtConst (m : ℕ) : ℝ :=
  2 / Real.pi * Real.Gamma (2 + (m : ℝ) / 2) ^ ((2 : ℝ) / m)

open Real in
/-- Reduction: if $\Gamma(2 + n/2)^4 < (\pi Y/2)^{2n}$ (with $n \ge 1$, $Y > 0$), then $b_n < Y$ (raise
$\frac 2\pi\Gamma(2+n/2)^{2/n} < Y$ to the power $2n$). -/
theorem blichfeldtConst_lt_of_pow {n : ℕ} (hn : 1 ≤ n) {Y : ℝ} (hY : 0 < Y)
    (h : Gamma (2 + (n : ℝ) / 2) ^ 4 < (π * Y / 2) ^ (2 * n)) : blichfeldtConst n < Y := by
  have hG : 0 < Gamma (2 + (n : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  set t := Gamma (2 + (n : ℝ) / 2) ^ ((2 : ℝ) / n) with ht
  have ht0 : 0 < t := rpow_pos_of_pos hG _
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have htpow : t ^ (2 * n) = Gamma (2 + (n : ℝ) / 2) ^ 4 := by
    rw [ht, ← rpow_natCast, ← rpow_mul hG.le]
    have : (2 : ℝ) / n * ((2 * n : ℕ) : ℝ) = (4 : ℕ) := by push_cast; field_simp; ring
    rw [this, rpow_natCast]
  have hlt : t < π * Y / 2 := by
    by_contra hge
    push Not at hge
    have := pow_le_pow_left₀ (by positivity) hge (2 * n)
    rw [htpow] at this
    linarith
  unfold blichfeldtConst
  rw [← ht, div_mul_eq_mul_div, div_lt_iff₀ pi_pos]
  linarith

/-- $\Gamma(2 + 2k/2) = (k+1)!$. -/
theorem gamma_two_add_even (k : ℕ) : Real.Gamma (2 + ((2 * k : ℕ) : ℝ) / 2) = ((k + 1).factorial : ℝ) := by
  rw [show (2 : ℝ) + ((2 * k : ℕ) : ℝ) / 2 = ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]

/-- $\Gamma(2 + (2k+1)/2) = \sqrt\pi\,(2k+4)!/(4^{k+2}(k+2)!)$. -/
theorem gamma_two_add_odd (k : ℕ) : Real.Gamma (2 + ((2 * k + 1 : ℕ) : ℝ) / 2) =
    Real.sqrt Real.pi * ((2 * k + 4).factorial : ℝ) / (4 ^ (k + 2) * ((k + 2).factorial : ℝ)) := by
  induction k with
  | zero =>
    rw [show (2 : ℝ) + ((2 * 0 + 1 : ℕ) : ℝ) / 2 = (1 / 2 + 1) + 1 by push_cast; ring,
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    simp [Nat.factorial]
    ring
  | succ k ih =>
    rw [show (2 : ℝ) + ((2 * (k + 1) + 1 : ℕ) : ℝ) / 2 = (2 + ((2 * k + 1 : ℕ) : ℝ) / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih,
      show 2 * (k + 1) + 4 = (2 * k + 4 + 1) + 1 by ring, show k + 1 + 2 = (k + 2) + 1 by ring,
      Nat.factorial_succ (2 * k + 4 + 1), Nat.factorial_succ (2 * k + 4), Nat.factorial_succ (k + 2)]
    push_cast
    field_simp
    ring

theorem pi_pow_gt (k : ℕ) (hk : k ≠ 0) : (3.141592 : ℝ) ^ k < Real.pi ^ k :=
  pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num) hk

/-- $(\pi\sqrt r/2)^{2r} = \pi^{2r}(r/4)^r$. -/
theorem pi_sqrt_pow (r : ℕ) :
    (Real.pi * Real.sqrt r / 2) ^ (2 * r) = Real.pi ^ (2 * r) * ((r : ℝ) / 4) ^ r := by
  have h : (Real.pi * Real.sqrt r / 2) ^ 2 = Real.pi ^ 2 * ((r : ℝ) / 4) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)]; ring
  rw [pow_mul, h, mul_pow, ← pow_mul]

/-- The even case of the numerical check: $b_{2k} < \sqrt{2k}$ from a rational inequality. -/
theorem lt_sqrt_even (k : ℕ) (hk : 1 ≤ k)
    (h : ((k + 1).factorial : ℝ) ^ 4 < (3.141592 : ℝ) ^ (2 * (2 * k)) * (((2 * k : ℕ) : ℝ) / 4) ^ (2 * k)) :
    blichfeldtConst (2 * k) < Real.sqrt (2 * k : ℕ) := by
  have hr : (0 : ℝ) < (2 * k : ℕ) := by exact_mod_cast (by omega : 0 < 2 * k)
  refine blichfeldtConst_lt_of_pow (by omega) (Real.sqrt_pos.2 hr) ?_
  rw [gamma_two_add_even, pi_sqrt_pow]
  refine h.trans_le (mul_le_mul_of_nonneg_right (pi_pow_gt _ (by omega)).le (by positivity))

/-- The odd case of the numerical check: $b_{2k+1} < \sqrt{2k+1}$ from a rational inequality. -/
theorem lt_sqrt_odd (k : ℕ) (hk : 1 ≤ k)
    (h : (((2 * k + 4).factorial : ℝ) / (4 ^ (k + 2) * ((k + 2).factorial : ℝ))) ^ 4 <
      (3.141592 : ℝ) ^ (4 * k) * (((2 * k + 1 : ℕ) : ℝ) / 4) ^ (2 * k + 1)) :
    blichfeldtConst (2 * k + 1) < Real.sqrt (2 * k + 1 : ℕ) := by
  have hr : (0 : ℝ) < (2 * k + 1 : ℕ) := by exact_mod_cast (by omega : 0 < 2 * k + 1)
  refine blichfeldtConst_lt_of_pow (by omega) (Real.sqrt_pos.2 hr) ?_
  rw [gamma_two_add_odd, pi_sqrt_pow]
  set c := ((2 * k + 4).factorial : ℝ) / (4 ^ (k + 2) * ((k + 2).factorial : ℝ))
  have e1 : (Real.sqrt Real.pi * ((2 * k + 4).factorial : ℝ) / (4 ^ (k + 2) * ((k + 2).factorial : ℝ))) ^ 4 =
      Real.pi ^ 2 * c ^ 4 := by
    rw [mul_div_assoc, mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have e2 : Real.pi ^ (2 * (2 * k + 1)) = Real.pi ^ 2 * Real.pi ^ (4 * k) := by
    rw [← pow_add]; congr 1; ring
  rw [e1, e2, mul_assoc]
  refine mul_lt_mul_of_pos_left (h.trans_le (mul_le_mul_of_nonneg_right (pi_pow_gt _ (by omega)).le
    (by positivity))) (by positivity)

/-- **The numerical part of Lemma 7.1.2, extended**: $b_r < \sqrt r$ for $2 \le r \le 43$ (Blichfeldt's bound
gives the case $r = 43$ too; Kitaoka's Stirling estimate stops at $42$). -/
theorem blichfeldtConst_lt_sqrt_of_le (r : ℕ) (h2 : 2 ≤ r) (h43 : r ≤ 43) :
    blichfeldtConst r < Real.sqrt r := by
  rcases Nat.even_or_odd' r with ⟨k, rfl | rfl⟩
  · have hk1 : 1 ≤ k := by omega
    have hk2 : k ≤ 21 := by omega
    refine lt_sqrt_even k hk1 ?_
    interval_cases k <;> norm_num [Nat.factorial]
  · have hk1 : 1 ≤ k := by omega
    have hk2 : k ≤ 21 := by omega
    refine lt_sqrt_odd k hk1 ?_
    interval_cases k <;> norm_num [Nat.factorial]

/-- **Kitaoka 1993, proof of Lemma 7.1.2** (p. 192), the numerical part: $2\pi^{-1}\Gamma(2 + r/2)^{2/r} < \sqrt r$
for $2 \le r < 43$. -/
@[kb "kitaoka1993" "§7.1, proof of Lemma 7.1.2, p. 192 (2π⁻¹Γ(2+r/2)^{2/r} < √r for 2 ≤ r < 43)"]
theorem blichfeldtConst_lt_sqrt (r : ℕ) (h2 : 2 ≤ r) (h43 : r < 43) :
    blichfeldtConst r < Real.sqrt r :=
  blichfeldtConst_lt_sqrt_of_le r h2 (by omega)

/-! ### Lemma 7.1.4: $b_n < n/6$ for $n \ge 40$ -/

/-- The first four terms of the binomial expansion of $(1 + y)^m$. -/
def binomFour (y : ℝ) (m : ℕ) : ℝ :=
  1 + m * y + m * (m - 1) / 2 * y ^ 2 + m * (m - 1) * (m - 2) / 6 * y ^ 3

/-- The first four binomial terms bound $(1+y)^m$ from below for $y \ge 0$. -/
theorem binomFour_le (y : ℝ) (hy : 0 ≤ y) (m : ℕ) : binomFour y m ≤ (1 + y) ^ m := by
  induction m with
  | zero => simp [binomFour]
  | succ m ih =>
    have hm : 0 ≤ (m : ℝ) * (m - 1) * (m - 2) := by
      rcases Nat.lt_or_ge m 2 with h | h
      · interval_cases m <;> norm_num
      · have : (2 : ℝ) ≤ m := by exact_mod_cast h
        have h1 : 0 ≤ (m : ℝ) - 1 := by linarith
        have h2 : 0 ≤ (m : ℝ) - 2 := by linarith
        positivity
    have e : binomFour y (m + 1) = (1 + y) * binomFour y m - (m : ℝ) * (m - 1) * (m - 2) / 6 * y ^ 4 := by
      simp only [binomFour]; push_cast; ring
    have h4 : 0 ≤ (m : ℝ) * (m - 1) * (m - 2) / 6 * y ^ 4 := by positivity
    calc binomFour y (m + 1) ≤ (1 + y) * binomFour y m := by rw [e]; linarith
      _ ≤ (1 + y) * (1 + y) ^ m := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 + y) ^ (m + 1) := by ring

/-- $((n+2)/n)^{2n} \ge 20$ for $n \ge 40$. -/
theorem twenty_le_pow (n : ℕ) (hn : 40 ≤ n) : (20 : ℝ) ≤ (((n : ℝ) + 2) / n) ^ (2 * n) := by
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have e : ((n : ℝ) + 2) / n = 1 + 2 / n := by field_simp
  rw [e]
  refine le_trans ?_ (binomFour_le (2 / n) (by positivity) (2 * n))
  have key : binomFour (2 / n) (2 * n) - 20 = (11 * (n : ℝ) ^ 2 - 60 * n + 16) / (3 * n ^ 2) := by
    simp only [binomFour]
    push_cast
    field_simp
    ring
  have : 0 ≤ (11 * (n : ℝ) ^ 2 - 60 * n + 16) / (3 * n ^ 2) := div_nonneg (by nlinarith) (by positivity)
  linarith

/-- The inequality $\Gamma(2 + n/2)^4 < (\pi (n/6)/2)^{2n}$, equivalent to $b_n < n/6$. -/
def SixBound (n : ℕ) : Prop :=
  Real.Gamma (2 + (n : ℝ) / 2) ^ 4 < (Real.pi * ((n : ℝ) / 6) / 2) ^ (2 * n)

theorem sixBound_forty : SixBound 40 := by
  unfold SixBound
  rw [show ((40 : ℕ) : ℝ) = ((2 * 20 : ℕ) : ℝ) by norm_num, gamma_two_add_even]
  refine lt_of_lt_of_le ?_ (pow_le_pow_left₀ (by norm_num) (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right Real.pi_gt_d6.le (by norm_num)) (by norm_num)) _)
  norm_num [Nat.factorial]

theorem sixBound_forty_one : SixBound 41 := by
  unfold SixBound
  rw [show ((41 : ℕ) : ℝ) = ((2 * 20 + 1 : ℕ) : ℝ) by norm_num, gamma_two_add_odd]
  set c := ((2 * 20 + 4).factorial : ℝ) / (4 ^ (20 + 2) * ((20 + 2).factorial : ℝ))
  have e1 : (Real.sqrt Real.pi * ((2 * 20 + 4).factorial : ℝ) / (4 ^ (20 + 2) * ((20 + 2).factorial : ℝ))) ^ 4 =
      Real.pi ^ 2 * c ^ 4 := by
    rw [mul_div_assoc, mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have e2 : (Real.pi * (((2 * 20 + 1 : ℕ) : ℝ) / 6) / 2) ^ (2 * 41) =
      Real.pi ^ 2 * (Real.pi ^ 80 * (41 / 12 : ℝ) ^ 82) := by
    push_cast
    ring
  rw [e1, e2]
  refine mul_lt_mul_of_pos_left ?_ (by positivity)
  refine lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_right (pi_pow_gt 80 (by norm_num)).le (by positivity))
  simp only [c]
  norm_num [Nat.factorial]

/-- The induction step $n \to n + 2$ for $n \ge 40$. -/
theorem sixBound_step (n : ℕ) (hn : 40 ≤ n) (h : SixBound n) : SixBound (n + 2) := by
  unfold SixBound at h ⊢
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hπ := Real.pi_gt_d2
  have hG : Real.Gamma (2 + ((n + 2 : ℕ) : ℝ) / 2) = (2 + (n : ℝ) / 2) * Real.Gamma (2 + (n : ℝ) / 2) := by
    rw [show (2 : ℝ) + ((n + 2 : ℕ) : ℝ) / 2 = (2 + (n : ℝ) / 2) + 1 by push_cast; ring]
    exact Real.Gamma_add_one (by positivity)
  set a := Real.pi * ((n : ℝ) / 6) / 2 with ha
  set b := Real.pi * (((n + 2 : ℕ) : ℝ) / 6) / 2 with hb
  have hab : b = a * (((n : ℝ) + 2) / n) := by rw [hb, ha]; push_cast; field_simp
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hlin : 2 + (n : ℝ) / 2 ≤ 2.1 * b := by rw [hb]; push_cast; nlinarith
  have h4 : (2 + (n : ℝ) / 2) ^ 4 ≤ 20 * b ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hlin 4
    rw [mul_pow] at this
    have : (0 : ℝ) ≤ b ^ 4 := by positivity
    nlinarith
  have hbpow : b ^ (2 * n) = a ^ (2 * n) * (((n : ℝ) + 2) / n) ^ (2 * n) := by rw [hab, mul_pow]
  rw [hG, mul_pow, show 2 * (n + 2) = 4 + 2 * n by ring, pow_add, hbpow]
  have h20 := twenty_le_pow n hn
  have hapow : 0 < a ^ (2 * n) := by positivity
  have hG4 : 0 ≤ Real.Gamma (2 + (n : ℝ) / 2) ^ 4 := by positivity
  calc (2 + (n : ℝ) / 2) ^ 4 * Real.Gamma (2 + (n : ℝ) / 2) ^ 4
      < (2 + (n : ℝ) / 2) ^ 4 * a ^ (2 * n) := mul_lt_mul_of_pos_left h (by positivity)
    _ ≤ 20 * b ^ 4 * a ^ (2 * n) := mul_le_mul_of_nonneg_right h4 hapow.le
    _ = b ^ 4 * a ^ (2 * n) * 20 := by ring
    _ ≤ b ^ 4 * a ^ (2 * n) * (((n : ℝ) + 2) / n) ^ (2 * n) :=
        mul_le_mul_of_nonneg_left h20 (by positivity)
    _ = b ^ 4 * (a ^ (2 * n) * (((n : ℝ) + 2) / n) ^ (2 * n)) := by ring

theorem sixBound (n : ℕ) (hn : 40 ≤ n) : SixBound n := by
  have key : ∀ j : ℕ, SixBound (40 + 2 * j) ∧ SixBound (41 + 2 * j) := by
    intro j
    induction j with
    | zero => exact ⟨sixBound_forty, sixBound_forty_one⟩
    | succ j ih =>
      exact ⟨by simpa [Nat.mul_succ, add_assoc] using sixBound_step _ (by omega) ih.1,
        by simpa [Nat.mul_succ, add_assoc] using sixBound_step _ (by omega) ih.2⟩
  obtain ⟨j, hj | hj⟩ : ∃ j, n = 40 + 2 * j ∨ n = 41 + 2 * j := ⟨(n - 40) / 2, by omega⟩
  · exact hj ▸ (key j).1
  · exact hj ▸ (key j).2

/-- **Kitaoka 1993, proof of Lemma 7.1.4** (p. 194), the numerical part: $2\pi^{-1}\Gamma(2 + n/2)^{2/n} < n/6$ for
$n \ge 40$. -/
@[kb "kitaoka1993" "§7.1, proof of Lemma 7.1.4, p. 194 (2π⁻¹Γ(2+n/2)^{2/n} < n/6 for n ≥ 40)"]
theorem blichfeldtConst_lt_div_six (n : ℕ) (h : 40 ≤ n) :
    blichfeldtConst n < (n : ℝ) / 6 :=
  blichfeldtConst_lt_of_pow (by omega) (div_pos (by exact_mod_cast (by omega : 0 < n)) (by norm_num))
    (sixBound n h)

end QuadFormsKB.Kitaoka.Blichfeldt
