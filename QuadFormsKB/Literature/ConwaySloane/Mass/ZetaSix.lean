/-
# Conway–Sloane 1988, §9 (ii): $\zeta_{24}(2) = \zeta_6(2) = \pi^2\sqrt6/24$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §9 (ii), p. 273 (bibliography key `conwaysloane1988`): the mass of $a_3 \oplus I_1$ uses "table 6 for
$\zeta_{24}(2) = \zeta_6(2)$". Here
$$\zeta_D(s) = \sum_{m \text{ odd}}\Bigl(\frac Dm\Bigr)m^{-s}\qquad(\text{`zetaD`, (9), p. 266}),$$
and Table 6 (p. 270) lists $\zeta_D(s)d^{s-1}\sqrt d/\pi^s$; for $d = 6$, $s = 2$ the entry is $\frac32$, i.e.
$\zeta_6(2) = \frac{3\pi^2}{2\cdot6\sqrt6} = \frac{\pi^2\sqrt6}{24}$.

**Proof (finite Fourier expansion).** The character $\chi(m) = \left(\frac6m\right)$ ($m$ odd), $0$ ($m$ even) has period
$24$ and takes the value $+1$ on $m \equiv \pm1, \pm5$ and $-1$ on $m \equiv \pm7, \pm11 \pmod{24}$ (`chiD_eq_tab_p6`).
For $x = \pi m/12$,
$$\sum_{a=0}^{23}\chi(a)\cos(2\pi am/24) = 2(\cos x + \cos5x - \cos7x - \cos11x) = 8\sin\tfrac{\pi m}2\sin\tfrac{\pi m}4
\cos\tfrac{\pi m}6 = 2\sqrt6\,\chi(m),$$
by the sum-to-product formulas and a check modulo $24$ (`fourier_chi6`). With Mathlib's
$\sum_{m \ge 1}\cos(2\pi mx)/m^2 = \pi^2B_2(x)$, $0 \le x \le 1$ (`hasSum_one_div_nat_pow_mul_cos`),
$$2\sqrt6\,\zeta_6(2) = \pi^2\sum_{a=0}^{23}\chi(a)B_2(a/24) = \frac{\pi^2}2.$$

**Proves** `zetaD_six_two` ($\zeta_6(2) = \pi^2\sqrt6/24$) and `zetaD_twentyfour_two` ($\zeta_{24}(2) = \zeta_6(2)$,
the Table 6 entry used in §9 (ii)). Unconditional.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Characters

open Real Finset

namespace QuadFormsKB.ConwaySloane.Mass

/-! ### Trigonometric values -/

theorem sin_mul_pi_div_two (n : ℕ) :
    sin (n * π / 2) = if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0 := by
  have h : (n : ℝ) * π / 2 = ((n % 4 : ℕ) : ℝ) * π / 2 + ((n / 4 : ℕ) : ℝ) * (2 * π) := by
    have := Nat.mod_add_div n 4
    have h' : (n : ℝ) = ((n % 4 : ℕ) : ℝ) + 4 * ((n / 4 : ℕ) : ℝ) := by exact_mod_cast this.symm
    rw [h']; ring
  rw [h, sin_add_nat_mul_two_pi]
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize n % 4 = r at hr ⊢
  interval_cases r
  · simp
  · simp
  · simp [show (2 : ℝ) * π / 2 = π by ring]
  · simp only [show ((3 : ℕ) : ℝ) * π / 2 = π / 2 + π by push_cast; ring, sin_add_pi, sin_pi_div_two]
    norm_num

theorem sin_mul_pi_div_four (n : ℕ) :
    sin (n * π / 4) = if n % 8 = 1 ∨ n % 8 = 3 then √2 / 2 else if n % 8 = 5 ∨ n % 8 = 7 then -(√2 / 2)
      else if n % 8 = 2 then 1 else if n % 8 = 6 then -1 else 0 := by
  have h : (n : ℝ) * π / 4 = ((n % 8 : ℕ) : ℝ) * π / 4 + ((n / 8 : ℕ) : ℝ) * (2 * π) := by
    have := Nat.mod_add_div n 8
    have h' : (n : ℝ) = ((n % 8 : ℕ) : ℝ) + 8 * ((n / 8 : ℕ) : ℝ) := by exact_mod_cast this.symm
    rw [h']; ring
  rw [h, sin_add_nat_mul_two_pi]
  have hr : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have s3 : sin (3 * π / 4) = √2 / 2 := by
    rw [show (3 : ℝ) * π / 4 = π - π / 4 by ring, sin_pi_sub, sin_pi_div_four]
  generalize n % 8 = r at hr ⊢
  interval_cases r
  · simp
  · simp [sin_pi_div_four]
  · simp [show (2 : ℝ) * π / 4 = π / 2 by ring]
  · simp [s3]
  · simp [show (4 : ℝ) * π / 4 = π by ring]
  · simp only [show ((5 : ℕ) : ℝ) * π / 4 = π / 4 + π by push_cast; ring, sin_add_pi, sin_pi_div_four]
    norm_num
  · simp only [show ((6 : ℕ) : ℝ) * π / 4 = π / 2 + π by push_cast; ring, sin_add_pi, sin_pi_div_two]
    norm_num
  · simp only [show ((7 : ℕ) : ℝ) * π / 4 = 3 * π / 4 + π by push_cast; ring, sin_add_pi, s3]
    norm_num

theorem cos_mul_pi_div_six_odd (n : ℕ) (hn : n % 2 = 1) :
    cos (n * π / 6) = if n % 12 = 1 ∨ n % 12 = 11 then √3 / 2 else if n % 12 = 5 ∨ n % 12 = 7 then -(√3 / 2)
      else 0 := by
  have h : (n : ℝ) * π / 6 = ((n % 12 : ℕ) : ℝ) * π / 6 + ((n / 12 : ℕ) : ℝ) * (2 * π) := by
    have := Nat.mod_add_div n 12
    have h' : (n : ℝ) = ((n % 12 : ℕ) : ℝ) + 12 * ((n / 12 : ℕ) : ℝ) := by exact_mod_cast this.symm
    rw [h']; ring
  rw [h, cos_add_nat_mul_two_pi]
  have hr : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hodd : n % 12 % 2 = 1 := by omega
  have c5 : cos (5 * π / 6) = -(√3 / 2) := by
    rw [show (5 : ℝ) * π / 6 = π - π / 6 by ring, cos_pi_sub, cos_pi_div_six]
  generalize n % 12 = r at hr hodd ⊢
  interval_cases r <;> simp at hodd
  · simp [cos_pi_div_six]
  · simp [show (3 : ℝ) * π / 6 = π / 2 by ring]
  · simp [c5]
  · simp only [show ((7 : ℕ) : ℝ) * π / 6 = π / 6 + π by push_cast; ring, cos_add_pi, cos_pi_div_six]
    norm_num
  · simp only [show ((9 : ℕ) : ℝ) * π / 6 = π / 2 + π by push_cast; ring, cos_add_pi, cos_pi_div_two]
    norm_num
  · simp only [show ((11 : ℕ) : ℝ) * π / 6 = 5 * π / 6 + π by push_cast; ring, cos_add_pi, c5]
    norm_num

/-! ### The Fourier expansion of $\chi_6$ -/

/-- The character $\left(\frac6m\right)$ as a real function (`chiD 6`). -/
noncomputable def chi6 (m : ℕ) : ℝ := (fT tab_p6 m : ℝ)

theorem trig_identity (x : ℝ) :
    cos x + cos (5 * x) - cos (7 * x) - cos (11 * x) = 4 * sin (6 * x) * sin (3 * x) * cos (2 * x) := by
  have h1 : cos x - cos (11 * x) = 2 * sin (6 * x) * sin (5 * x) := by
    rw [cos_sub_cos, show (x + 11 * x) / 2 = 6 * x by ring, show (x - 11 * x) / 2 = -(5 * x) by ring, sin_neg]
    ring
  have h2 : cos (5 * x) - cos (7 * x) = 2 * sin (6 * x) * sin x := by
    rw [cos_sub_cos, show (5 * x + 7 * x) / 2 = 6 * x by ring, show (5 * x - 7 * x) / 2 = -x by ring, sin_neg]
    ring
  have h3 : sin (5 * x) + sin x = 2 * sin (3 * x) * cos (2 * x) := by
    rw [sin_add_sin, show (5 * x + x) / 2 = 3 * x by ring, show (5 * x - x) / 2 = 2 * x by ring]
  linear_combination h1 + h2 + 2 * sin (6 * x) * h3

/-- **The finite Fourier expansion of $\chi_6$:** $\sum_{a=0}^{23}\chi(a)\cos(2\pi m\,a/24) = 2\sqrt6\,\chi(m)$. -/
theorem fourier_chi6 (m : ℕ) :
    ∑ a ∈ range 24, chi6 a * cos (2 * π * m * ((a : ℝ) / 24)) = 2 * √6 * chi6 m := by
  set x : ℝ := π * m / 12 with hx
  have hc : ∀ a : ℕ, cos (2 * π * m * ((a : ℝ) / 24)) = cos (a * x) := fun a => by
    rw [hx]; ring_nf
  have hrefl : ∀ a : ℕ, a ≤ 24 → cos (((24 - a : ℕ) : ℝ) * x) = cos (a * x) := fun a ha => by
    rw [Nat.cast_sub ha, show ((24 : ℕ) - (a : ℝ)) * x = (m : ℕ) * (2 * π) - a * x by rw [hx]; push_cast; ring,
      cos_nat_mul_two_pi_sub]
  simp only [hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chi6, fT, tab_p6]
  norm_num
  have e23 := hrefl 1 (by norm_num)
  have e19 := hrefl 5 (by norm_num)
  have e17 := hrefl 7 (by norm_num)
  have e13 := hrefl 11 (by norm_num)
  norm_num at e23 e19 e17 e13
  rw [e23, e19, e17, e13]
  have key : cos x + cos (5 * x) - cos (7 * x) - cos (11 * x) = 4 * sin (6 * x) * sin (3 * x) * cos (2 * x) :=
    trig_identity x
  have h6 : sin (6 * x) = sin (m * π / 2) := by rw [hx]; ring_nf
  have h3 : sin (3 * x) = sin (m * π / 4) := by rw [hx]; ring_nf
  have h2 : cos (2 * x) = cos (m * π / 6) := by rw [hx]; ring_nf
  rw [h6, h3, h2] at key
  have hsum : cos x + cos (5 * x) + -cos (7 * x) + -cos (11 * x) + -cos (11 * x) + -cos (7 * x) + cos (5 * x) +
      cos x = 2 * (cos x + cos (5 * x) - cos (7 * x) - cos (11 * x)) := by ring
  rw [hsum, key]
  have hs6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hsq2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [sin_mul_pi_div_two, sin_mul_pi_div_four, hs6]
  have h24 : m % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have e4 : m % 4 = m % 24 % 4 := (Nat.mod_mod_of_dvd m (by norm_num)).symm
  have e8 : m % 8 = m % 24 % 8 := (Nat.mod_mod_of_dvd m (by norm_num)).symm
  have e12 : m % 12 = m % 24 % 12 := (Nat.mod_mod_of_dvd m (by norm_num)).symm
  have e2 : m % 2 = m % 24 % 2 := (Nat.mod_mod_of_dvd m (by norm_num)).symm
  rcases Nat.mod_two_eq_zero_or_one m with hev | hod
  · have hz : m % 4 = 0 ∨ m % 4 = 2 := by omega
    have hr : (if m % 4 = 1 then (1 : ℝ) else if m % 4 = 3 then -1 else 0) = 0 := by
      rcases hz with h | h <;> simp [h]
    rw [hr]
    rw [e2] at hev
    generalize m % 24 = r at h24 hev ⊢
    interval_cases r <;> simp_all
  · rw [cos_mul_pi_div_six_odd m hod, e4, e8, e12]
    rw [e2] at hod
    generalize m % 24 = r at h24 hod ⊢
    interval_cases r <;> simp at hod <;> norm_num <;> ring

/-! ### The value $\zeta_6(2)$ -/

theorem chiD_six_eq (m : ℕ) : (chiD 6 m : ℝ) = chi6 m := by
  rw [chi6, chiD_eq_tab_p6]

/-- $\sum_{a=0}^{23}\chi(a)B_2(a/24) = \frac12$. -/
theorem sum_chi6_bernoulli :
    ∑ a ∈ range 24, chi6 a * (π ^ 2 * bernoulliFun 2 ((a : ℝ) / 24)) = π ^ 2 / 2 := by
  simp only [bernoulliFun_two]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chi6, fT, tab_p6]
  norm_num
  ring

/-- **$\zeta_6(2) = \pi^2\sqrt6/24$** (Conway–Sloane 1988, Table 6, p. 270, $d = 6$, $s = 2$: entry $\frac32$;
§9 (ii), p. 273). -/
@[kb "conwaysloane1988" "Table 6, p. 270 (d = 6, s = 2); §9 (ii), p. 273"]
theorem zetaD_six_two : zetaD 6 2 = π ^ 2 * √6 / 24 := by
  have hcos : ∀ a ∈ range 24, HasSum (fun n : ℕ => chi6 a * (1 / (n : ℝ) ^ 2 * cos (2 * π * n * ((a : ℝ) / 24))))
      (chi6 a * (π ^ 2 * bernoulliFun 2 ((a : ℝ) / 24))) := by
    intro a ha
    have hx : (a : ℝ) / 24 ∈ Set.Icc (0 : ℝ) 1 := by
      have : a < 24 := Finset.mem_range.1 ha
      constructor
      · positivity
      · rw [div_le_one (by norm_num)]; exact_mod_cast this.le
    have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
    have e : ((-1 : ℝ) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / (2 * 1).factorial *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval ((a : ℝ) / 24)) =
        π ^ 2 * bernoulliFun 2 ((a : ℝ) / 24) := by
      simp only [bernoulliFun]; norm_num; left; ring
    rw [e] at h
    exact h.mul_left _
  have hS := hasSum_sum hcos
  rw [sum_chi6_bernoulli] at hS
  have hS' : HasSum (fun n : ℕ => 2 * √6 * ((chiD 6 n : ℝ) / (n : ℝ) ^ (2 : ℝ))) (π ^ 2 / 2) := by
    convert hS using 1
    funext n
    rw [chiD_six_eq, Real.rpow_two]
    have hf := fourier_chi6 n
    calc 2 * √6 * (chi6 n / (n : ℝ) ^ 2) = (2 * √6 * chi6 n) * (1 / (n : ℝ) ^ 2) := by ring
      _ = _ := by
        rw [← hf, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => by ring
  have hZ := (hasSum_zetaD (D := 6) (by norm_num) (s := 2) (by norm_num)).mul_left (2 * √6)
  have heq := hZ.unique hS'
  have h6 : (0 : ℝ) < √6 := by positivity
  have hsq : √6 * √6 = 6 := Real.mul_self_sqrt (by norm_num)
  field_simp at heq ⊢
  nlinarith [heq, hsq]

/-- **$\zeta_{24}(2) = \zeta_6(2) = \pi^2\sqrt6/24$** (Conway–Sloane 1988, §9 (ii), p. 273, with (14), p. 268:
$\zeta_{4D}(s) = \zeta_D(s)$). -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (ζ₂₄(2) = ζ₆(2)); (14), p. 268"]
theorem zetaD_twentyfour_two : zetaD 24 2 = π ^ 2 * √6 / 24 := by
  rw [show (24 : ℤ) = 4 * 6 by norm_num, zetaD_four_mul (by norm_num) (by norm_num), zetaD_six_two]

end QuadFormsKB.ConwaySloane.Mass
