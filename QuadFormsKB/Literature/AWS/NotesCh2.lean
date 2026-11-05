/-
# Hanke, AWS 2009 notes, Ch. 2: theta functions (§2.1–§2.6)

J. Hanke, *Quadratic Forms and Automorphic Forms*, arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed
page), Chapter 2, pp. 25–35. The library already proves most of §2.1–§2.5 (theta series, Poisson summation, the
$\Gamma_0(N)$ transformation for even $n$, Siegel's formula for quaternary forms, Jacobi's four squares theorem);
`AWS/NotesCitations.lean` tags those declarations. This file adds:

- **Lemma 2.1.1** (`lemma_2_1_1`): a Fourier series $\sum_{m\ge0} a(m)e^{2\pi imz}$ with $|a(m)| \le Cm^r$ converges
  absolutely and locally uniformly on $\mathcal H$ to a holomorphic function.
- **Theorem 2.4.1** (Tartakowski, $n \ge 5$): **proved for even $n$** (`theorem_2_4_1_even`, from the library's
  unconditional Hanke 2004 Thm 6.4 for even $n \ge 6$); the odd case is the named input `TartakowskiOdd`
  (it needs bounds for cusp forms of half-integral weight), and `theorem_2_4_1` gives the full statement from it.
- **Facts about modular forms, 3** (p. 31), at level one: the coefficients of the Eisenstein series $E_k$ satisfy
  $c\,m^{k-1} \le |a_E(m)| \le 2c\,m^{k-1}$ with $c = |2k/B_k|$ (`facts_3_level_one`), so the bound $c_\varepsilon m^{k-1+\varepsilon}$
  holds (`facts_3_level_one_eps`) and is attained up to $m^\varepsilon$.
- **Theorem 2.6.1** (Pfeuffer, Watson): stated as the named statement `ClassNumberOneFinite` (not used as a hypothesis).
-/
import QuadFormsKB.Siegel.Theta
import QuadFormsKB.Siegel.Tartakowsky
import QuadFormsKB.Literature.Cassels.AppB.Statements
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

open Complex Real Filter Topology

namespace QuadFormsKB.AWS.Notes

/-- The $m$-th term $a(m)e^{2\pi imz}$ of a Fourier series. -/
noncomputable def fourierTerm (a : ℕ → ℂ) (m : ℕ) (z : ℂ) : ℂ := a m * cexp (2 * π * I * m * z)

theorem norm_cexp_two_pi_I_mul (m : ℕ) (z : ℂ) : ‖cexp (2 * π * I * m * z)‖ = Real.exp (-(2 * π * m * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- Polynomially bounded coefficients are bounded by $|C|(m^k + 1)$ with $k = \lceil r\rceil$. -/
theorem norm_le_of_rpow_bound {a : ℕ → ℂ} {C r : ℝ} (ha : ∀ m : ℕ, ‖a m‖ ≤ C * (m : ℝ) ^ r) (m : ℕ) :
    ‖a m‖ ≤ |C| * ((m : ℝ) ^ ⌈r⌉₊ + 1) := by
  have h1 : C * (m : ℝ) ^ r ≤ |C| * (m : ℝ) ^ r :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (Nat.cast_nonneg m) r)
  refine (ha m).trans (h1.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero]
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    · rw [Real.zero_rpow hr]; positivity
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (m : ℝ) ^ r ≤ (m : ℝ) ^ (⌈r⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (Nat.le_ceil r)
    rw [Real.rpow_natCast] at this
    linarith

/-- The dominating series on $\{\operatorname{Im} z > y_0\}$ is summable. -/
theorem summable_bound (C : ℝ) (k : ℕ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    Summable fun m : ℕ => |C| * ((m : ℝ) ^ k + 1) * Real.exp (-(2 * π * m * y₀)) := by
  have hc : 0 < 2 * π * y₀ := by positivity
  have := ((Real.summable_pow_mul_exp_neg_nat_mul k hc).add
    (Real.summable_pow_mul_exp_neg_nat_mul 0 hc)).mul_left |C|
  refine this.congr fun m => ?_
  simp only [pow_zero, one_mul]
  ring_nf

/-- **Lemma 2.1.1 (Convergence of Fourier series), p. 26.** *The Fourier series $f(z) := \sum_{m=0}^\infty a(m)e^{2\pi imz}$
converges absolutely and uniformly on compact subsets of $\mathcal H$ to a holomorphic function $f : \mathcal H \to \mathbb C$
if all of its coefficients $a(m) \in \mathbb C$ satisfy $|a(m)| \le Cm^r$ for some constant $C > 0$.*

Here $r \in \mathbb R$ is any real exponent and $C$ any real constant (the sign of $C$ is not needed). The three
conclusions are: (1) absolute convergence at every $z \in \mathcal H$; (2) locally uniform convergence of the partial
sums on $\mathcal H$ (equivalent to uniform convergence on compact subsets, $\mathcal H$ being locally compact);
(3) holomorphy of the sum on $\mathcal H$. The notes cite Miyake, Lemma 4.3.3. -/
@[kb "hanke2011aws" "§2.1, Lemma 2.1.1, p. 26"]
theorem lemma_2_1_1 (a : ℕ → ℂ) (C r : ℝ) (ha : ∀ m : ℕ, ‖a m‖ ≤ C * (m : ℝ) ^ r) :
    (∀ z : ℂ, 0 < z.im → Summable fun m => ‖fourierTerm a m z‖) ∧
    TendstoLocallyUniformlyOn (fun s : Finset ℕ => fun z => ∑ m ∈ s, fourierTerm a m z)
      (fun z => ∑' m, fourierTerm a m z) atTop {z : ℂ | 0 < z.im} ∧
    DifferentiableOn ℂ (fun z => ∑' m, fourierTerm a m z) {z : ℂ | 0 < z.im} := by
  set k := ⌈r⌉₊
  -- the bound on `{Im z > y₀}`
  have hle : ∀ {y₀ : ℝ} (m : ℕ) (z : ℂ), y₀ ≤ z.im →
      ‖fourierTerm a m z‖ ≤ |C| * ((m : ℝ) ^ k + 1) * Real.exp (-(2 * π * m * y₀)) := by
    intro y₀ m z hz
    rw [fourierTerm, norm_mul, norm_cexp_two_pi_I_mul]
    refine mul_le_mul (norm_le_of_rpow_bound ha m) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      (by positivity)
    have : 0 ≤ 2 * π * m := by positivity
    nlinarith
  -- uniform convergence on each `{Im z > y₀}`
  have hunif : ∀ {y₀ : ℝ}, 0 < y₀ →
      TendstoUniformlyOn (fun s : Finset ℕ => fun z => ∑ m ∈ s, fourierTerm a m z)
        (fun z => ∑' m, fourierTerm a m z) atTop {z : ℂ | y₀ < z.im} := fun hy₀ =>
    tendstoUniformlyOn_tsum (summable_bound C k hy₀) fun m z hz => hle m z (le_of_lt hz)
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => hle m z le_rfl)
      (summable_bound C k hz)
  · intro u hu z hz
    have hz' : 0 < z.im / 2 := half_pos hz
    refine ⟨{w : ℂ | z.im / 2 < w.im}, ?_, (hunif hz') u hu⟩
    refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_)
    · exact isOpen_lt continuous_const Complex.continuous_im
    · show z.im / 2 < z.im; linarith
  · intro z hz
    have hz' : 0 < z.im / 2 := half_pos hz
    have hU : IsOpen {w : ℂ | z.im / 2 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have hd : DifferentiableOn ℂ (fun w => ∑' m, fourierTerm a m w) {w : ℂ | z.im / 2 < w.im} :=
      Complex.differentiableOn_tsum_of_summable_norm (summable_bound C k hz')
        (fun m => by unfold fourierTerm; fun_prop) hU (fun m w hw => hle m w (le_of_lt hw))
    have hzU : z ∈ {w : ℂ | z.im / 2 < w.im} := show z.im / 2 < z.im by linarith
    exact ((hd z hzU).differentiableAt (hU.mem_nhds hzU)).differentiableWithinAt

/-! ### Theorem 2.4.1 (Tartakowski) -/

open Siegel in
/-- **Theorem 2.4.1, $n$ even (p. 31).** *If $Q$ is a positive definite quadratic form over $\mathbb Z$ in $n \ge 5$
variables, then every sufficiently large number $m \in \mathbb N$ that is locally represented by $Q$ is represented
by $Q$*, for even $n$ (so $n \ge 6$). "Locally represented" is: $Q(\vec x) \equiv m \pmod{p^k}$ is solvable for all $k$ at
every prime $p$ (`LocalDensity.IsLocallyRepresentedAt`; by the Chinese remainder theorem this is solvability modulo every
$M$, and the real condition is automatic for $m \ge 0$). Unconditional (`Siegel.thm_6_4_even_uncond`); the threshold
is not explicit. -/
@[kb "hanke2011aws" "§2.4, Thm. 2.4.1, p. 31 (n even)"]
theorem theorem_2_4_1_even {n : ℕ} (Q : IntQF n) (hQ : Q.PosDef) (hn : 5 ≤ n) (heven : Even n) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → (∀ p : ℕ, p.Prime → LocalDensity.IsLocallyRepresentedAt Q p m) →
      IntQF.Represents Q m := by
  have h6 : 6 ≤ n := by
    obtain ⟨k, rfl⟩ := heven
    omega
  exact thm_6_4_even_uncond Q hQ h6 heven

/-- **Named input: Theorem 2.4.1 for odd $n \ge 5$** (Tartakowski 1929; cited, not proved, by the notes). Its proof
needs bounds for the Fourier coefficients of cusp forms of half-integral weight, which the library does not have. -/
@[kb "hanke2011aws" "§2.4, Thm. 2.4.1, p. 31 (n odd; named statement)"]
structure TartakowskiOdd : Prop where
  holds : ∀ {n : ℕ} (Q : IntQF n), Q.PosDef → 5 ≤ n → Odd n →
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → (∀ p : ℕ, p.Prime → LocalDensity.IsLocallyRepresentedAt Q p m) →
      IntQF.Represents Q m

/-- **Theorem 2.4.1 (Tartakowski), p. 31**, every $n \ge 5$: proved for even $n$, conditional on the named input
`TartakowskiOdd` for odd $n$. -/
@[kb "hanke2011aws" "§2.4, Thm. 2.4.1, p. 31"]
theorem theorem_2_4_1 (hT : TartakowskiOdd) {n : ℕ} (Q : IntQF n) (hQ : Q.PosDef) (hn : 5 ≤ n) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → (∀ p : ℕ, p.Prime → LocalDensity.IsLocallyRepresentedAt Q p m) →
      IntQF.Represents Q m := by
  rcases Nat.even_or_odd n with h | h
  · exact theorem_2_4_1_even Q hQ hn h
  · exact hT.holds Q hQ hn h

/-! ### Facts about modular forms 3: Eisenstein coefficients at level one -/

open ArithmeticFunction in
/-- $\sigma_j(m) \le 2m^j$ for $j \ge 2$, $m \ge 1$ (from $\sigma_j(m) = m^j\sum_{d\mid m}d^{-j}$ and $\sum_{d\ge1}d^{-2} \le 2$). -/
theorem sigma_le_two_mul_pow {j m : ℕ} (hj : 2 ≤ j) : (ArithmeticFunction.sigma j m : ℝ) ≤ 2 * (m : ℝ) ^ j := by
  rw [ArithmeticFunction.sigma_apply, ← Nat.sum_div_divisors]
  push_cast
  have hterm : ∀ d ∈ m.divisors, ((m / d : ℕ) : ℝ) ^ j ≤ (m : ℝ) ^ j * ((d : ℝ) ^ 2)⁻¹ := by
    intro d hd
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    rw [Nat.cast_div hdm (by positivity), div_pow, div_eq_mul_inv]
    gcongr
  calc ∑ d ∈ m.divisors, ((m / d : ℕ) : ℝ) ^ j ≤ ∑ d ∈ m.divisors, (m : ℝ) ^ j * ((d : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (m : ℝ) ^ j * ∑ d ∈ m.divisors, ((d : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (m : ℝ) ^ j * 2 := by
        gcongr
        calc ∑ d ∈ m.divisors, ((d : ℝ) ^ 2)⁻¹ ≤ ∑ d ∈ Finset.Ioo 0 (m + 1), ((d : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun _ _ _ => by positivity)
              have := Nat.divisor_le hd
              have := Nat.pos_of_mem_divisors hd
              simp only [Finset.mem_Ioo]; omega
          _ ≤ 2 / ((0 : ℕ) + 1) := sum_Ioo_inv_sq_le 0 (m + 1)
          _ = 2 := by norm_num
    _ = 2 * (m : ℝ) ^ j := by ring

open ArithmeticFunction in
/-- $m^j \le \sigma_j(m)$ for $m \ge 1$ ($m$ divides itself). -/
theorem pow_le_sigma (j : ℕ) {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) ^ j ≤ (ArithmeticFunction.sigma j m : ℝ) := by
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  exact Finset.single_le_sum (f := fun d : ℕ => (d : ℝ) ^ j) (fun _ _ => by positivity)
    (Nat.mem_divisors_self m (by omega))

open ModularFormClass UpperHalfPlane EisensteinSeries in
/-- **Facts about modular forms 3 (p. 31) and the remark after it, level one.** For even $k \ge 4$ (Mathlib needs
$k \ge 3$) the $m$-th Fourier coefficient $a_E(m) = -\frac{2k}{B_k}\sigma_{k-1}(m)$ of the normalized Eisenstein series
$E_k$ (2.4) satisfies $c\,m^{k-1} \le |a_E(m)| \le 2c\,m^{k-1}$ for $m \ge 1$, $c = |2k/B_k|$: the bound of Fact 3
holds (even with $\varepsilon = 0$) and "is attained by the Eisenstein series (2.4)". -/
@[kb "hanke2011aws" "§2.3, Facts about modular forms 3 and the remark after it, p. 31 (level one)"]
theorem facts_3_level_one {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (∀ m : ℕ, 1 ≤ m → ‖(qExpansion 1 (ModularForm.E hk)).coeff m‖ ≤ 2 * ‖(2 * k / bernoulli k : ℂ)‖ * (m : ℝ) ^ (k - 1)) ∧
    (∀ m : ℕ, 1 ≤ m → ‖(2 * k / bernoulli k : ℂ)‖ * (m : ℝ) ^ (k - 1) ≤ ‖(qExpansion 1 (ModularForm.E hk)).coeff m‖) := by
  have hcoeff : ∀ m : ℕ, 1 ≤ m →
      ‖(qExpansion 1 (ModularForm.E hk)).coeff m‖ = ‖(2 * k / bernoulli k : ℂ)‖ * (ArithmeticFunction.sigma (k - 1) m : ℝ) := by
    intro m hm
    rw [E_qExpansion_coeff hk hk2 m]
    simp only [show m ≠ 0 by omega, ↓reduceIte]
    rw [norm_mul, norm_neg, Complex.norm_natCast]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [hcoeff m hm, mul_comm (2 : ℝ), mul_assoc]
    exact mul_le_mul_of_nonneg_left (sigma_le_two_mul_pow (j := k - 1) (m := m) (by omega)) (norm_nonneg _)
  · rw [hcoeff m hm]
    exact mul_le_mul_of_nonneg_left (pow_le_sigma _ hm) (norm_nonneg _)

open ModularFormClass UpperHalfPlane EisensteinSeries in
/-- **Facts about modular forms 3 (p. 31), as printed, level one:** for every $\varepsilon > 0$ there is $c_\varepsilon$ with
$|a_E(m)| \le c_\varepsilon m^{k-1+\varepsilon}$ for all $m \ge 1$. -/
@[kb "hanke2011aws" "§2.3, Facts about modular forms 3, p. 31 (level one, as printed)"]
theorem facts_3_level_one_eps {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ m : ℕ, 1 ≤ m →
      ‖(qExpansion 1 (ModularForm.E hk)).coeff m‖ ≤ c * (m : ℝ) ^ ((k : ℝ) - 1 + ε) := by
  refine ⟨2 * ‖(2 * k / bernoulli k : ℂ)‖, by positivity, fun m hm => ?_⟩
  refine ((facts_3_level_one hk hk2).1 m hm).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [← Real.rpow_natCast, Nat.cast_sub (by omega), Nat.cast_one]
  exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

/-! ### Theorem 2.6.1 (Pfeuffer, Watson) -/

/-- **Theorem 2.6.1 (p. 35), named statement.** *There are only finitely many (classes of) primitive positive definite
quadratic forms $Q$ over $\mathbb Z$ in $n \ge 2$ variables with class number $h_Q = 1$*: the set of pairs
$(n, [Q])$, $n \ge 2$, $Q$ primitive (the values of $Q$ generate $\mathbb Z$, `Cassels.IsPrimitiveValues`) and positive
definite with exactly one class in its genus, is finite. Cited by the notes from Watson and Pfeuffer; not proved here
and not used as a hypothesis anywhere. -/
@[kb "hanke2011aws" "§2.6, Thm. 2.6.1, p. 35 (named statement)"]
structure ClassNumberOneFinite : Prop where
  finite : {c : Σ n : ℕ, Siegel.QClass n | 2 ≤ c.1 ∧ ∃ Q : IntQF c.1, Siegel.classOf Q = c.2 ∧
    Cassels.IsPrimitiveValues Q ∧ Q.PosDef ∧ (Siegel.genusClasses Q).ncard = 1}.Finite

end QuadFormsKB.AWS.Notes
