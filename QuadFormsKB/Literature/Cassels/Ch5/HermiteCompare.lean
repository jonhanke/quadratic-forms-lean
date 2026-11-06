/-
# Cassels, Chapter 5, §3, p. 73: Minkowski's constant versus Hermite's constant

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 5, §3, p. 73. After the bound
$m \le C_n\, d(g)^{1/n}$ of (3.7)–(3.8), with Minkowski's constant $C_n = 4 V_n^{-2/n}$ where $V_n$ is the volume of
the unit ball in $\mathbb R^n$, the text compares it with Hermite's constant $(4/3)^{(n-1)/2}$ of (3.9). It remarks
that Minkowski's estimate (3.8) is much smaller than Hermite's (3.9) for large $n$, while Hermite's is the better
one for $n < 8$.

**Conventions.** $n$ is the dimension; `minkowskiConst n` is $C_n$ (from `Ch5/Background.lean`) and
`Siegel.unitBallVol n` is $V_n$. Hermite's constant is written `(4/3 : ℝ) ^ (((n : ℝ) - 1) / 2)`
(real power). No indices occur.

**Proves**
* `hermite_lt_minkowskiConst`: $(4/3)^{(n-1)/2} < C_n$ for $2 \le n < 8$ (for $n = 1$ both sides equal $1$, since
  $V_1 = 2$ and $C_1 = 4 \cdot 2^{-2} = 1$, so $n = 1$ is excluded);
* `hermite_lt_minkowskiConst_eight`: the comparison still holds at $n = 8$ (a remark, not in the text);
* `tendsto_minkowskiConst_div_hermite`: $C_n / (4/3)^{(n-1)/2} \to 0$ as $n \to \infty$.

The proofs reduce, via the closed form $V_n = \sqrt\pi^{\,n}/\Gamma(n/2+1)$ (`Siegel.unitBallVol_eq`), the
comparison for fixed $n$ to a polynomial inequality in $\pi$ (checked with $3.14 < \pi < 3.15$), and use
$\Gamma(n/2 + 1) \le n^n$ (log-convexity of $\Gamma$) for the asymptotics, which gives $C_n \le 4 n^2$.
-/
import QuadFormsKB.Literature.Cassels.Ch5.Background

namespace QuadFormsKB.Cassels.Ch5

open Filter Topology

/-- Helper: for $1 \le n$ and $k \le n$, $k! \le n^n$ (as real numbers). -/
lemma factorial_le_pow_self {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) : (k.factorial : ℝ) ≤ (n : ℝ) ^ n := by
  have h1 : k.factorial ≤ n ^ n :=
    (Nat.factorial_le_pow k).trans ((Nat.pow_le_pow_left hk k).trans (Nat.pow_le_pow_right hn hk))
  exact_mod_cast h1

/-- Helper: for $n \ge 1$, $\Gamma(n/2 + 1) \le n^n$. For even $n = 2m$ this is $m! \le n^n$; for odd $n = 2m + 1$
it follows from the logarithmic convexity of $\Gamma$ (`Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`) applied
to $\Gamma(\tfrac12 (m+1) + \tfrac12 (m+2))$. Here `n` is the dimension. -/
lemma gamma_half_add_one_le (n : ℕ) (hn : 1 ≤ n) : Real.Gamma ((n : ℝ) / 2 + 1) ≤ (n : ℝ) ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h : ((2 * m : ℕ) : ℝ) / 2 + 1 = (m : ℝ) + 1 := by push_cast; ring
    rw [h, Real.Gamma_nat_eq_factorial]
    exact factorial_le_pow_self hn (by omega)
  · have h : ((2 * m + 1 : ℕ) : ℝ) / 2 + 1 = (1 / 2 : ℝ) * ((m : ℝ) + 1) + (1 / 2 : ℝ) * ((m : ℝ) + 2) := by
      push_cast; ring
    have h1 : Real.Gamma ((m : ℝ) + 1) ≤ ((2 * m + 1 : ℕ) : ℝ) ^ (2 * m + 1) := by
      rw [Real.Gamma_nat_eq_factorial]; exact factorial_le_pow_self hn (by omega)
    have h2 : Real.Gamma ((m : ℝ) + 2) ≤ ((2 * m + 1 : ℕ) : ℝ) ^ (2 * m + 1) := by
      have : ((m : ℝ) + 2) = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [this, Real.Gamma_nat_eq_factorial]; exact factorial_le_pow_self hn (by omega)
    have hN : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ (2 * m + 1) := by positivity
    have hg1 : 0 < Real.Gamma ((m : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hg2 : 0 < Real.Gamma ((m : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
    rw [h]
    refine (Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (by positivity) (by positivity)
      (by norm_num) (by norm_num) (by norm_num)).trans ?_
    calc Real.Gamma ((m : ℝ) + 1) ^ (1 / 2 : ℝ) * Real.Gamma ((m : ℝ) + 2) ^ (1 / 2 : ℝ)
        ≤ (((2 * m + 1 : ℕ) : ℝ) ^ (2 * m + 1)) ^ (1 / 2 : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ (2 * m + 1)) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ((2 * m + 1 : ℕ) : ℝ) ^ (2 * m + 1) := by
          rw [← Real.rpow_add hN]; norm_num

/-- Helper: for $n \ge 1$, $C_n \le 4 n^2$, i.e. `minkowskiConst n ≤ 4 * n ^ 2`. Proof: $V_n \ge \sqrt\pi^{\,n}/n^n \ge n^{-n}$
since $\sqrt\pi \ge 1$ and $\Gamma(n/2+1) \le n^n$ (`gamma_half_add_one_le`). Here `n` is the dimension. -/
lemma minkowskiConst_le (n : ℕ) (hn : 1 ≤ n) : minkowskiConst n ≤ 4 * (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hsq : 1 ≤ Real.sqrt Real.pi ^ n := by
    apply one_le_pow₀
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hV : ((n : ℝ) ^ (-(n : ℝ))) ≤ Siegel.unitBallVol n := by
    rw [Siegel.unitBallVol_eq hn, Real.rpow_neg hn'.le, Real.rpow_natCast, ← one_div]
    calc 1 / (n : ℝ) ^ n ≤ 1 / Real.Gamma ((n : ℝ) / 2 + 1) :=
          one_div_le_one_div_of_le hG (gamma_half_add_one_le n hn)
      _ ≤ _ := by
          rw [le_div_iff₀ hG]
          calc 1 / Real.Gamma ((n : ℝ) / 2 + 1) * Real.Gamma ((n : ℝ) / 2 + 1) = 1 := by field_simp
            _ ≤ _ := hsq
  have h2 : Siegel.unitBallVol n ^ (-(2 / n : ℝ)) ≤ (n : ℝ) ^ (2 : ℝ) := by
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hV (by
      have : (0 : ℝ) ≤ 2 / n := by positivity
      linarith)).trans_eq ?_
    rw [← Real.rpow_mul hn'.le]
    congr 1
    field_simp
  rw [minkowskiConst]
  have : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := by exact_mod_cast Real.rpow_natCast (n : ℝ) 2
  rw [this] at h2
  linarith

/-- **Cassels, Ch. 5, §3, p. 73** (Minkowski's estimate (3.8) is much smaller than Hermite's (3.9) for large $n$):
the ratio of Minkowski's constant $C_n = $ `minkowskiConst n` to Hermite's constant $(4/3)^{(n-1)/2}$ tends to $0$ as
the dimension $n \to \infty$. -/
@[kb "cassels1978" "Ch. 5, §3, p. 73 (Minkowski's estimate (3.8) is much smaller than Hermite's (3.9) for large n)"]
theorem tendsto_minkowskiConst_div_hermite :
    Tendsto (fun n : ℕ => minkowskiConst n / (4 / 3 : ℝ) ^ (((n : ℝ) - 1) / 2)) atTop (𝓝 0) := by
  set c : ℝ := Real.sqrt (4 / 3) with hc
  have hc1 : 1 < c := by
    rw [hc, Real.lt_sqrt (by norm_num)]; norm_num
  have hc0 : 0 < c := by linarith
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 2 hc1).const_mul (4 * c)
  rw [mul_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : 0 ≤ minkowskiConst n := by
      rw [minkowskiConst]
      have : 0 ≤ Siegel.unitBallVol n := ENNReal.toReal_nonneg
      positivity
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hH : (4 / 3 : ℝ) ^ (((n : ℝ) - 1) / 2) = c ^ n / c := by
      have h43 : (4 / 3 : ℝ) = c ^ (2 : ℝ) := by
        rw [hc, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt (by norm_num)]
      rw [h43, ← Real.rpow_mul hc0.le, show (2 : ℝ) * (((n : ℝ) - 1) / 2) = (n : ℝ) - 1 by ring,
        Real.rpow_sub hc0, Real.rpow_natCast, Real.rpow_one]
    rw [hH]
    have hcn : 0 < c ^ n := by positivity
    rw [div_div_eq_mul_div, div_le_iff₀ hcn]
    have := minkowskiConst_le n hn
    calc minkowskiConst n * c ≤ 4 * (n : ℝ) ^ 2 * c := by gcongr
      _ = 4 * c * ((n : ℝ) ^ 2 / c ^ n) * c ^ n := by field_simp

/-- Helper: $\Gamma(3/2) = \sqrt\pi/2$. -/
lemma gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, Real.Gamma_one_half_eq] at this
  rw [this]; ring

/-- Helper: $\Gamma(5/2) = \tfrac34\sqrt\pi$. -/
lemma gamma_five_halves : Real.Gamma (5 / 2) = 3 / 4 * Real.sqrt Real.pi := by
  have := Real.Gamma_add_one (s := 3 / 2) (by norm_num)
  rw [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num, gamma_three_halves] at this
  rw [this]; ring

/-- Helper: $\Gamma(7/2) = \tfrac{15}8\sqrt\pi$. -/
lemma gamma_seven_halves : Real.Gamma (7 / 2) = 15 / 8 * Real.sqrt Real.pi := by
  have := Real.Gamma_add_one (s := 5 / 2) (by norm_num)
  rw [show (5 / 2 : ℝ) + 1 = 7 / 2 by norm_num, gamma_five_halves] at this
  rw [this]; ring

/-- Helper: $\Gamma(9/2) = \tfrac{105}{16}\sqrt\pi$. -/
lemma gamma_nine_halves : Real.Gamma (9 / 2) = 105 / 16 * Real.sqrt Real.pi := by
  have := Real.Gamma_add_one (s := 7 / 2) (by norm_num)
  rw [show (7 / 2 : ℝ) + 1 = 9 / 2 by norm_num, gamma_seven_halves] at this
  rw [this]; ring

/-- Helper: $\sqrt\pi^{\,4} = \pi^2$. -/
lemma sqrt_pi_pow_four : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt Real.pi_pos.le]

/-- Helper: reduction of the comparison for a fixed dimension `n ≥ 1` to a polynomial inequality. If `g` is the value
$\Gamma(n/2 + 1)$ and $(4/3)^{(n-1)n}\,\pi^{2n} < 16^n g^4$, then Hermite's constant $(4/3)^{(n-1)/2}$ is smaller than
`minkowskiConst n`. (Proof: raise $H \cdot V_n^{2/n} < 4$ to the power $2n$ to remove the real powers.) -/
lemma hermite_lt_of_poly (n : ℕ) (hn : 1 ≤ n) (g : ℝ) (hg : Real.Gamma ((n : ℝ) / 2 + 1) = g)
    (h : (4 / 3 : ℝ) ^ ((n - 1) * n) * Real.pi ^ (2 * n) < 16 ^ n * g ^ 4) :
    (4 / 3 : ℝ) ^ (((n : ℝ) - 1) / 2) < minkowskiConst n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : 0 < g := hg ▸ Real.Gamma_pos_of_pos (by positivity)
  have hVe : Siegel.unitBallVol n = Real.sqrt Real.pi ^ n / g := by
    rw [Siegel.unitBallVol_eq hn, hg]
  have hV : 0 < Siegel.unitBallVol n := by
    rw [hVe]; have := Real.pi_pos; positivity
  have hV4 : Siegel.unitBallVol n ^ 4 * g ^ 4 = Real.pi ^ (2 * n) := by
    rw [hVe, div_pow, div_mul_cancel₀ _ (by positivity), ← pow_mul, mul_comm n 4, pow_mul, sqrt_pi_pow_four,
      ← pow_mul, mul_comm]
  set H : ℝ := (4 / 3 : ℝ) ^ (((n : ℝ) - 1) / 2) with hH
  set W : ℝ := Siegel.unitBallVol n ^ (2 / n : ℝ) with hW
  have hHpos : 0 < H := by positivity
  have hWpos : 0 < W := by positivity
  have hH2 : H ^ 2 = (4 / 3 : ℝ) ^ (n - 1) := by
    rw [hH, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn]; simp
    rw [show ((n : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) by rw [← this]; push_cast; ring,
      Real.rpow_natCast]
  have hWn : W ^ n = Siegel.unitBallVol n ^ 2 := by
    rw [hW, ← Real.rpow_natCast, ← Real.rpow_mul hV.le, div_mul_cancel₀ _ hn'.ne']
    exact_mod_cast Real.rpow_natCast _ 2
  have key : (H * W) ^ (2 * n) < 4 ^ (2 * n) := by
    have e : (H * W) ^ (2 * n) = (4 / 3 : ℝ) ^ ((n - 1) * n) * Siegel.unitBallVol n ^ 4 := by
      rw [mul_pow, pow_mul, mul_comm 2 n, pow_mul, hH2, hWn, ← pow_mul, ← pow_mul]
    rw [e, show (4 : ℝ) ^ (2 * n) = 16 ^ n by rw [pow_mul]; norm_num]
    have hg4 : 0 < g ^ 4 := by positivity
    rw [← mul_lt_mul_iff_of_pos_right hg4, mul_assoc, hV4]
    exact h
  have hHW : H * W < 4 := lt_of_pow_lt_pow_left₀ _ (by norm_num) key
  rw [minkowskiConst, Real.rpow_neg hV.le, ← hW, ← div_eq_mul_inv, lt_div_iff₀ hWpos]
  exact hHW

/-- Helper: from $a\,3.15^j < b$ conclude $a\,\pi^j < b$ for $a > 0$. -/
lemma pi_pow_aux (a b : ℝ) (j : ℕ) (ha : 0 < a) (h : a * (3.15 : ℝ) ^ j < b) : a * Real.pi ^ j < b := by
  have : Real.pi ^ j ≤ (3.15 : ℝ) ^ j := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le j
  nlinarith

/-- Helper: from $a\,3.15^j < b$ conclude $a\,\pi^{m} < b\,\pi^2$ for $a > 0$ and $m = j + 2$. -/
lemma pi_pow_aux2 (a b : ℝ) (j m : ℕ) (hm : m = j + 2) (ha : 0 < a) (h : a * (3.15 : ℝ) ^ j < b) :
    a * Real.pi ^ m < b * Real.pi ^ 2 := by
  rw [hm, pow_add, ← mul_assoc]
  exact mul_lt_mul_of_pos_right (pi_pow_aux a b j ha h) (by positivity)

/-- **Cassels, Ch. 5, §3, p. 73** (Hermite's bound (3.9) is better than Minkowski's (3.8) for $n < 8$): for the
dimensions $2 \le n < 8$, Hermite's constant $(4/3)^{(n-1)/2}$ is strictly smaller than Minkowski's constant
$C_n = 4V_n^{-2/n}$ (`minkowskiConst n`). For $n = 1$ the two constants are equal ($C_1 = 1$), so $n = 1$ is
excluded. -/
@[kb "cassels1978" "Ch. 5, §3, p. 73 (Hermite's bound (3.9) is better than (3.8) for n < 8)"]
theorem hermite_lt_minkowskiConst (n : ℕ) (h2 : 2 ≤ n) (h8 : n < 8) :
    (4 / 3 : ℝ) ^ (((n : ℝ) - 1) / 2) < minkowskiConst n := by
  interval_cases n
  · refine hermite_lt_of_poly 2 (by norm_num) 1 ?_ ?_
    · rw [show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num]; exact Real.Gamma_two
    · exact pi_pow_aux _ _ 4 (by norm_num) (by norm_num)
  · refine hermite_lt_of_poly 3 (by norm_num) (3 / 4 * Real.sqrt Real.pi) ?_ ?_
    · rw [show ((3 : ℕ) : ℝ) / 2 + 1 = 5 / 2 by norm_num]; exact gamma_five_halves
    · rw [mul_pow, sqrt_pi_pow_four, ← mul_assoc]
      exact pi_pow_aux2 _ _ 4 _ (by norm_num) (by norm_num) (by norm_num)
  · refine hermite_lt_of_poly 4 (by norm_num) 2 ?_ ?_
    · rw [show ((4 : ℕ) : ℝ) / 2 + 1 = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
    · exact pi_pow_aux _ _ 8 (by norm_num) (by norm_num)
  · refine hermite_lt_of_poly 5 (by norm_num) (15 / 8 * Real.sqrt Real.pi) ?_ ?_
    · rw [show ((5 : ℕ) : ℝ) / 2 + 1 = 7 / 2 by norm_num]; exact gamma_seven_halves
    · rw [mul_pow, sqrt_pi_pow_four, ← mul_assoc]
      exact pi_pow_aux2 _ _ 8 _ (by norm_num) (by norm_num) (by norm_num)
  · refine hermite_lt_of_poly 6 (by norm_num) 6 ?_ ?_
    · rw [show ((6 : ℕ) : ℝ) / 2 + 1 = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
    · exact pi_pow_aux _ _ 12 (by norm_num) (by norm_num)
  · refine hermite_lt_of_poly 7 (by norm_num) (105 / 16 * Real.sqrt Real.pi) ?_ ?_
    · rw [show ((7 : ℕ) : ℝ) / 2 + 1 = 9 / 2 by norm_num]; exact gamma_nine_halves
    · rw [mul_pow, sqrt_pi_pow_four, ← mul_assoc]
      exact pi_pow_aux2 _ _ 12 _ (by norm_num) (by norm_num) (by norm_num)

/-- **Cassels, Ch. 5, §3, p. 73** (a remark going slightly beyond the text, which only claims $n < 8$): Hermite's
constant $(4/3)^{(n-1)/2}$ is still strictly smaller than Minkowski's constant $C_n$ in dimension $n = 8$. -/
@[kb "cassels1978" "Ch. 5, §3, p. 73 (Hermite's bound (3.9) is still better than (3.8) at n = 8)"]
theorem hermite_lt_minkowskiConst_eight :
    (4 / 3 : ℝ) ^ ((((8 : ℕ) : ℝ) - 1) / 2) < minkowskiConst 8 := by
  refine hermite_lt_of_poly 8 (by norm_num) 24 ?_ ?_
  · rw [show ((8 : ℕ) : ℝ) / 2 + 1 = ((4 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  · exact pi_pow_aux _ _ 16 (by norm_num) (by norm_num)

end QuadFormsKB.Cassels.Ch5
