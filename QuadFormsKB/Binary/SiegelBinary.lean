import QuadFormsKB.Binary.BinaryDensitiesRam
import QuadFormsKB.Binary.ClassNumberFormula

/-!
# Siegel's formula for binary forms

For a fundamental discriminant $D < 0$, a primitive positive definite form $f$ of discriminant $D$ and every
$m \ge 1$, **Siegel's Hauptsatz for $n = 2$** with $\varepsilon = \frac12$:
$$r_{\mathcal G}(m) = \frac12\,\beta_\infty(m)\prod_p\beta_p(m).$$
The Euler product converges only conditionally, so its meaning is a convention. Both are given:

* **Convention "$L(1,\chi_D)^{-1}\times$ finite product" (unconditional):** `siegelFormula_binary`,
  `genusRepAvg f m = (1/2) * aEWith f m (binaryEulerValue f D m)` with
  $P_f(m) = L(1,\chi_D)^{-1}\prod_{p \mid mD}\beta_p(m)/(1 - \chi_D(p)/p)$ (`binaryEulerValue`).
* **Natural order of the primes:** `siegelFormula_binary_natural`, for every $P$ with
  $\prod_{p\le X}\beta_p(m) \to P$ (`IsEulerProductValue`), stated here with the hypothesis `EulerProductAtOne D`
  ($\prod_{p \le X}(1 - \chi_D(p)/p) \to L(1,\chi_D)^{-1}$). That hypothesis is **proved** in
  `EulerProductAtOne.lean` (`eulerProductAtOne`), which also gives the unconditional forms
  `siegelFormula_binary_natural'` and `isEulerProductValue_binary'`. Under it, $P_f(m)$ *is* the natural-order value
  (`isEulerProductValue_binary`).

**Ingredients.** $\beta_\infty(m) = 2\pi/\sqrt{|D|}$ (`betaInf_binary`); the local densities (`BinaryDensities.lean`);
$L(1,\chi_D) = 2\pi h/(w\sqrt{|D|})$ (`classNumberFormula_neg`); the genus average
$r_{\mathcal G}(m) = \frac{w2^{t-1}}{h}\sum_{d\mid m}\chi_D(d)\cdot[\psi_p(m) = \chi_p(f)\ \forall p \mid D]$
(`genusRepAvg_binary_coprime`). **$\varepsilon = \frac12$ exactly:** $\beta_\infty P_f(m) = \frac{2\pi}{\sqrt{|D|}}\cdot
\frac{w\sqrt{|D|}}{2\pi h}\cdot S\cdot 2^t[\ldots] = \frac{w2^t}{h}S[\ldots] = 2r_{\mathcal G}(m)$ ($S = \sum_{d \mid m}\chi_D(d)$,
$t$ = number of primes dividing $D$); `epsilon_eq_half` shows no other constant works.

*Structure:* `siegelFormula_binary_coprime` ($m$ prime to $D$, local data from `BinaryDensities.lean`) came first; the
general `siegelFormula_binary` uses the ramified densities for every $m$ (`BinaryDensitiesRam.lean`,
$\beta_p(f, m) = 1 + \chi_p(f)c_p(m)$) and `genus_represents_iff`: the genus of $f$ represents $m$ iff $c_p(m) = \chi_p(f)$
for all $p \mid D$ (when $\sum_{d\mid m}\chi_D(d) \ne 0$).

Sources: Siegel (1935), *Ann. of Math.* 36, Hauptsatz and the definition of $\varepsilon$ [unverified locator];
Siegel (1944), *Ann. of Math.* 45 [unverified locator]; Hanke (2004), (5.3)–(5.5), pp. 368–369 (the $n = 3$ analogue
of the convention question is (5.3)/(5.4)); Zagier, *Zetafunktionen und quadratische Körper*, §§8, 11; Cox, §§3, 7.
-/

open Filter Topology QuadFormsKB.LocalDensity QuadFormsKB.Siegel
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF

/-! ### The archimedean density -/

/-- $\det H = -D$ for a binary form ($H = \begin{pmatrix} 2a & b \\ b & 2c\end{pmatrix}$). -/
theorem hessian_det_eq_neg_disc (f : BinQF) : f.hessian.det = -f.disc := by
  rw [hessian_det_two, BinQF.disc]; simp only [BinQF.a, BinQF.b, BinQF.c]; ring

/-- Hanke's determinant of a binary form: $\det(H/2) = -D/4 = |D|/4$. -/
theorem gramDet_binary (f : BinQF) : gramDet f = -(f.disc : ℝ) / 4 := by
  rw [gramDet, hessian_det_eq_neg_disc]; push_cast; ring

/-- $\omega_2 = \pi$ (the area of the unit disc). -/
theorem unitBallVol_two : unitBallVol 2 = Real.pi := by
  rw [unitBallVol_eq (by norm_num)]
  rw [show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num, Real.Gamma_two, div_one,
    Real.sq_sqrt Real.pi_pos.le]

/-- **$\beta_\infty$ of a positive definite binary form** (Siegel's normalization, Hanke 2004 (5.5)): for $f$ of
discriminant $D < 0$ and every $m$,
$$\beta_\infty(m) = \frac{2\pi}{\sqrt{|D|}},$$
independent of $m$: the area of $\{f \le t\}$ is $2\pi t/\sqrt{|D|}$ (an ellipse), and $\beta_\infty$ is its
$t$-derivative (`Siegel.tendsto_volume_shell_div`). Here $n\,\omega_n D_Q^{-1/2}/2\cdot m^{0}$ with $n = 2$,
$\omega_2 = \pi$, $D_Q = \det(H/2) = |D|/4$. -/
@[kb "hanke2004" "(5.5), p. 369 (n = 2)"]
theorem betaInf_binary (f : BinQF) (hD : f.disc < 0) (m : ℝ) :
    betaInf f m = 2 * Real.pi / Real.sqrt (-(f.disc : ℝ)) := by
  have hD' : (0 : ℝ) < -(f.disc : ℝ) := by
    have : (f.disc : ℝ) < 0 := by exact_mod_cast hD
    linarith
  rw [betaInf, gramDet_binary, unitBallVol_two]
  rw [show (((2 : ℕ) : ℝ) - 2) / 2 = 0 by norm_num, Real.rpow_zero, mul_one]
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (-(f.disc : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hD').ne'
  field_simp
  push_cast
  ring

/-! ### The Kronecker character as a real function, and $L(1, \chi_D)$ -/

/-- $\chi_D(n)$ as a real number (`kronZ D n`). -/
noncomputable def kronR (D : ℤ) (n : ℕ) : ℝ := (kronZ D (n : ZMod D.natAbs) : ℝ)

variable {D : ℤ} [IsQuadDisc D]

theorem kronR_mul (a b : ℕ) : kronR D (a * b) = kronR D a * kronR D b := by
  simp only [kronR, Nat.cast_mul, kronZ_mul]; push_cast; ring

theorem kronR_one : kronR D 1 = 1 := by simp [kronR, kronZ_one]

theorem kronR_pow (a j : ℕ) : kronR D (a ^ j) = kronR D a ^ j := by
  induction j with
  | zero => simp [kronR_one]
  | succ j ih => rw [pow_succ, kronR_mul, ih, pow_succ]

theorem kronZ_trichotomy (x : ZMod D.natAbs) : kronZ D x = 0 ∨ kronZ D x = 1 ∨ kronZ D x = -1 := by
  unfold kronZ
  split_ifs
  · exact jacobiSym.trichotomy _ _
  · exact jacobiSym.trichotomy _ _
  · left; rfl

theorem kronR_trichotomy (n : ℕ) : kronR D n = 0 ∨ kronR D n = 1 ∨ kronR D n = -1 := by
  unfold kronR
  rcases kronZ_trichotomy (D := D) (n : ZMod D.natAbs) with h | h | h <;> simp [h]

theorem one_sub_kronR_div_ne_zero {p : ℕ} (hp : p.Prime) : 1 - kronR D p / p ≠ 0 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rcases kronR_trichotomy (D := D) p with h | h | h <;> rw [h]
  · simp
  · intro h'
    have : (1 : ℝ) / p = 1 := by linarith
    rw [div_eq_one_iff_eq (by positivity)] at this
    linarith
  · intro h'
    have : (1 : ℝ) + 1 / p = 0 := by rw [← h']; ring
    have : (0 : ℝ) < 1 / p := by positivity
    linarith

theorem kronR_eq_zero_of_dvd {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ D) : kronR D p = 0 := by
  unfold kronR
  rw [kronZ_nonunit]
  · simp
  · rw [ZMod.isUnit_iff_coprime]
    intro h
    have : p ∣ D.natAbs := Int.natCast_dvd.mp hpD
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl this)

/-- **Divisor sums of $\chi_D$ are multiplicative:** for $m \ne 0$,
$\sum_{d \mid m}\chi_D(d) = \prod_{p \mid m}\sum_{j=0}^{v_p(m)}\chi_D(p)^j$. -/
theorem sum_divisors_kronR {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, kronR D d =
      ∏ p ∈ m.primeFactors, ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j := by
  set χA : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else kronR D n, by simp⟩ with hχA
  have hχm : χA.IsMultiplicative := by
    refine ⟨by simp [χA, kronR_one], fun {a b} _ => ?_⟩
    simp only [χA, ArithmeticFunction.coe_mk, mul_eq_zero]
    split_ifs <;> simp_all [kronR_mul]
  have hg : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * χA).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul hχm
  have hval : ∀ n, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * χA) n = ∑ d ∈ n.divisors, kronR D d := by
    intro n
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    have : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    simp [χA, this]
  rw [← hval, hg.multiplicative_factorization _ hm, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hval, Nat.divisors_prime_pow (Nat.prime_of_mem_primeFactors hp), Finset.sum_map]
  simp [kronR_pow]

/-- $L(1, \chi_D)$ as a real number: the real part of Mathlib's `(kroneckerChar D).LFunction 1`. -/
noncomputable def LOne (D : ℤ) [IsQuadDisc D] : ℝ := ((kroneckerChar D).LFunction 1).re

/-- $L(1, \chi_D)$ is real (from the class number formula). -/
theorem LFunction_one_eq_ofReal : (kroneckerChar D).LFunction 1 = (LOne D : ℂ) := by
  have h3 := three_le_natAbs (D := D)
  rcases lt_or_gt_of_ne (show D ≠ 0 by omega) with h | h
  · rw [LOne, classNumberFormula_neg h, Complex.ofReal_re]
  · rw [LOne, classNumberFormula_pos h, Complex.ofReal_re]

/-- **$L(1, \chi_D)$ for $D < 0$** (Dirichlet's class number formula): $L(1,\chi_D) = 2\pi h/(w\sqrt{|D|})$. -/
theorem LOne_eq_of_neg (hD : D < 0) :
    LOne D = 2 * Real.pi * NumberField.classNumber (QField D) /
      (NumberField.Units.torsionOrder (QField D) * Real.sqrt |(D : ℝ)|) := by
  rw [LOne, classNumberFormula_neg hD, Complex.ofReal_re]

/-! ### The Euler product: the finite correction and the regularized value -/

/-- **The finite correction** to $L(1,\chi_D)^{-1}$:
$$C_f(m) = \prod_{p \mid mD}\frac{\beta_p(m)}{1 - \chi_D(p)/p},$$
a finite product (all other factors are $1$, `localDensity_div_eq_one`). -/
noncomputable def binaryEulerCorr (f : BinQF) (D m : ℤ) : ℝ :=
  ∏ p ∈ (m * D).natAbs.primeFactors, localDensity f p m / (1 - kronR D p / p)

/-- **The regularized value of $\prod_p\beta_p(m)$** for a binary form (convention "$L^{-1} \times$ finite product"): $P_f(m) = L(1,\chi_D)^{-1}\,C_f(m)$. It needs no analytic input; under `EulerProductAtOne D` it is the limit
of the partial products in the natural order (`isEulerProductValue_binary`). -/
@[kb "siegel1935" "§§1–2 (regularized product for n = 2) [unverified locator]"]
noncomputable def binaryEulerValue (f : BinQF) (D : ℤ) [IsQuadDisc D] (m : ℤ) : ℝ :=
  (LOne D)⁻¹ * binaryEulerCorr f D m

/-- **Input (now proved, `eulerProductAtOne`): the Euler product of $L(s, \chi_D)$ at $s = 1$, in the natural order
of the primes.**
$$\prod_{p \le X}\Big(1 - \frac{\chi_D(p)}{p}\Big) \longrightarrow L(1, \chi_D)^{-1} \qquad (X \to \infty),$$
with $L(1,\chi_D)$ the value at $1$ of Mathlib's `DirichletCharacter.LFunction`.

Field:
- `tendsto`: the partial products over the primes $p \le X$ (`Siegel.primesUpTo X`) tend to $L(1,\chi_D)^{-1}$ in $\mathbb{C}$.

*Status:* a classical theorem (Mertens/Landau for nonprincipal characters; equivalently $\sum_p\chi_D(p)/p$
converges, with the value fixed by Abel's theorem for Dirichlet series). Mathlib (v4.35) has the Euler product only
for $\operatorname{Re}s > 1$ (`DirichletCharacter.LSeries_eulerProduct_hasProd`) and $L(1,\chi) \ne 0$, not the
conditionally convergent product at $s = 1$; it is **proved** in `EulerProductAtOne.lean` (`eulerProductAtOne`, every
fundamental $D$) from $L(1,\chi) \ne 0$ by a Mertens-type bound and an Abelian argument, without the prime number
theorem. It is about $\chi_D$ alone, not about quadratic forms, and is not equivalent to Siegel's formula: it is used only to identify the natural-order value of $\prod_p\beta_p(m)$ with
`binaryEulerValue` (`isEulerProductValue_binary`). Sources: Montgomery–Vaughan, *Multiplicative Number Theory I*,
§4.3 [unverified locator]; Landau, *Handbuch* (1909) [unverified]. -/
@[kb "montgomeryvaughan2007" "§4.3 (Euler product at s = 1) [unverified locator]"]
structure EulerProductAtOne (D : ℤ) [IsQuadDisc D] : Prop where
  tendsto : Tendsto (fun X : ℕ => ∏ p ∈ primesUpTo X, (1 - kroneckerChar D ((p : ℕ) : ZMod D.natAbs) / ((p : ℕ) : ℂ)))
    atTop (𝓝 ((kroneckerChar D).LFunction 1)⁻¹)

/-- The real form of `EulerProductAtOne`: $\prod_{p \le X}(1 - \chi_D(p)/p) \to L(1,\chi_D)^{-1}$ in $\mathbb{R}$. -/
theorem EulerProductAtOne.tendsto_real (hE : EulerProductAtOne D) :
    Tendsto (fun X : ℕ => ∏ p ∈ primesUpTo X, (1 - kronR D p / p)) atTop (𝓝 (LOne D)⁻¹) := by
  have h := (Complex.continuous_re.tendsto _).comp hE.tendsto
  rw [LFunction_one_eq_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re] at h
  refine h.congr fun X => ?_
  simp only [Function.comp_apply]
  rw [show (∏ p ∈ primesUpTo X, (1 - kroneckerChar D ((p : ℕ) : ZMod D.natAbs) / ((p : ℕ) : ℂ))) =
      ((∏ p ∈ primesUpTo X, (1 - kronR D p / p) : ℝ) : ℂ) by
    push_cast
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [kroneckerChar_apply, kronR]; push_cast; ring, Complex.ofReal_re]

/-- At $p \nmid mD$: $\beta_p(m) = 1 - \chi_D(p)/p$. -/
theorem localDensity_of_not_dvd {f : BinQF} (hD : f.disc = D) {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : m ≠ 0)
    (hpm : ¬ (p : ℤ) ∣ m * D) : localDensity f p m = 1 - kronR D p / p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [localDensity_good_binary f hD p (fun h => hpm (h.mul_left m)) m hm,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hpm ((int_dvd_iff_natAbs.mpr h).mul_right D)),
    goodFactor_zero]
  rfl

/-- **The natural-order value of $\prod_p\beta_p(m)$ is `binaryEulerValue`**, given `EulerProductAtOne D`: for any
form $f$ of fundamental discriminant $D$ and $m \ne 0$, $\prod_{p \le X}\beta_p(m) \to L(1,\chi_D)^{-1}C_f(m)$. The partial
products are $\prod_{p\le X}(1 - \chi_D(p)/p)$ times $\prod_{p \le X,\ p \mid mD}\beta_p(m)/(1 - \chi_D(p)/p)$, and the
second factor is constant ($= C_f(m)$) for $X \ge |mD|$. -/
@[kb "siegel1935" "§§1–2 (n = 2: conditionally convergent product) [unverified locator]"]
theorem isEulerProductValue_binary (hE : EulerProductAtOne D) {f : BinQF} (hD : f.disc = D) {m : ℤ}
    (hm : m ≠ 0) : IsEulerProductValue f m (binaryEulerValue f D m) := by
  have hmD : m * D ≠ 0 := mul_ne_zero hm (by have := three_le_natAbs (D := D); omega)
  set S := (m * D).natAbs.primeFactors
  set g : ℕ → ℝ := fun p => localDensity f p m / (1 - kronR D p / p)
  have hsplit : ∀ X, eulerPartialProd f m X =
      (∏ p ∈ primesUpTo X, (1 - kronR D p / p)) * ∏ p ∈ primesUpTo X, g p := by
    intro X
    rw [eulerPartialProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [g, eulerFactor]
    rw [mul_div_cancel₀ _ (one_sub_kronR_div_ne_zero p.2)]
  have hconst : ∀ X, (m * D).natAbs ≤ X → ∏ p ∈ primesUpTo X, g p = binaryEulerCorr f D m := by
    intro X hX
    rw [binaryEulerCorr, primesUpTo, Finset.prod_subtype_eq_prod_filter]
    symm
    refine Finset.prod_subset (fun p hp => ?_) (fun p hp hpS => ?_)
    · have hpp := Nat.prime_of_mem_primeFactors hp
      have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hmD) (Nat.dvd_of_mem_primeFactors hp)
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hpp⟩
    · simp only [Finset.mem_filter] at hp
      have hpp := hp.2
      have hnd : ¬ (p : ℤ) ∣ m * D := fun h => hpS (Nat.mem_primeFactors.mpr
        ⟨hpp, int_dvd_iff_natAbs.mp h, Int.natAbs_ne_zero.mpr hmD⟩)
      rw [localDensity_of_not_dvd hD hpp hm hnd, div_self (one_sub_kronR_div_ne_zero hpp)]
  unfold IsEulerProductValue binaryEulerValue
  have hlim := hE.tendsto_real.mul (tendsto_const_nhds (x := binaryEulerCorr f D m))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (m * D).natAbs] with X hX
  rw [hsplit, hconst X hX]

/-! ### The value for $m$ prime to $D$ -/

/-- For $\chi, \psi \in \{\pm 1\}$: $1 + \chi\psi = 2$ if $\chi = \psi$, else $0$. -/
theorem one_add_mul_of_sq {x y : ℤ} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) :
    (1 + (x : ℝ) * y) = if y = x then 2 else 0 := by
  rcases sq_eq_one_iff.mp hx with rfl | rfl <;> rcases sq_eq_one_iff.mp hy with rfl | rfl <;> norm_num

/-- **The ramified part of the product:** for $f$ primitive of discriminant $D$ and $m$ prime to $D$,
$\prod_{p \mid D}(1 + \chi_p(f)\psi_p(m)) = 2^t$ if $\psi_p(m) = \chi_p(f)$ for all $p \mid D$, and $0$ otherwise
($t$ = the number of primes dividing $D$). -/
theorem prod_ram_eq {f : BinQF} (hf : Primitive f) (hD : f.disc = D) {m : ℕ} (hcop : Nat.Coprime m D.natAbs) :
    ∏ p ∈ D.natAbs.primeFactors, (1 + (formChar f p : ℝ) * (genusChar D p m : ℝ)) =
      if ∀ p ∈ D.natAbs.primeFactors, genusChar D p m = formChar f p then
        (2 : ℝ) ^ D.natAbs.primeFactors.card else 0 := by
  have hval : ∀ p ∈ D.natAbs.primeFactors, (1 + (formChar f p : ℝ) * (genusChar D p m : ℝ)) =
      if genusChar D p m = formChar f p then 2 else 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpD : (p : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    have hpm : ¬ (p : ℤ) ∣ (m : ℤ) := by
      intro h
      have h1 : p ∣ m := Int.natCast_dvd_natCast.mp h
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop h1 (Nat.dvd_of_mem_primeFactors hp))
    have hx : formChar f p ^ 2 = 1 := by
      unfold formChar; exact genusChar_sq _ hpp (not_dvd_charCoeff hf hpp (hD ▸ hpD))
    exact one_add_mul_of_sq hx (genusChar_sq D hpp hpm)
  rw [Finset.prod_congr rfl hval]
  split_ifs with h
  · rw [Finset.prod_congr rfl fun p hp => ite_eq_left (h p hp), Finset.prod_const]
  · push Not at h
    obtain ⟨p, hp, hne⟩ := h
    exact Finset.prod_eq_zero hp (ite_eq_right hne)

/-- **The finite correction for $m$ prime to $D$:**
$$C_f(m) = \Big(\sum_{d \mid m}\chi_D(d)\Big)\prod_{p \mid D}\big(1 + \chi_p(f)\psi_p(m)\big):$$
at $p \mid m$ the factor is $\sum_{j=0}^{v_p(m)}\chi_D(p)^j$ (`localDensity_good_binary`), whose product is the divisor
sum (`sum_divisors_kronR`); at $p \mid D$ it is $\beta_p(m) = 1 + \chi_p(f)\psi_p(m)$ (`localDensity_ram_unit`) since
$\chi_D(p) = 0$. -/
theorem binaryEulerCorr_coprime {f : BinQF} (hf : Primitive f) (hD : f.disc = D) {m : ℕ} (hm : m ≠ 0)
    (hcop : Nat.Coprime m D.natAbs) :
    binaryEulerCorr f D m = (∑ d ∈ m.divisors, kronR D d) *
      ∏ p ∈ D.natAbs.primeFactors, (1 + (formChar f p : ℝ) * (genusChar D p m : ℝ)) := by
  have hD0 : D.natAbs ≠ 0 := by have := three_le_natAbs (D := D); omega
  rw [binaryEulerCorr, show ((m : ℤ) * D).natAbs = m * D.natAbs by rw [Int.natAbs_mul, Int.natAbs_natCast],
    Nat.Coprime.primeFactors_mul hcop, Finset.prod_union hcop.disjoint_primeFactors, sum_divisors_kronR hm]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hpD : ¬ (p : ℤ) ∣ D := by
      intro h
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop (Nat.dvd_of_mem_primeFactors hp)
        (Int.natCast_dvd.mp h))
    rw [localDensity_good_binary f hD p hpD m (by exact_mod_cast hm), goodFactor, Int.natAbs_natCast]
    change ((1 - kronR D p / p) * ∑ j ∈ _, kronR D p ^ j) / (1 - kronR D p / p) = _
    rw [mul_div_cancel_left₀ _ (one_sub_kronR_div_ne_zero hpp)]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hpD : (p : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    have hpm : ¬ (p : ℤ) ∣ (m : ℤ) := by
      intro h
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop (Int.natCast_dvd_natCast.mp h)
        (Nat.dvd_of_mem_primeFactors hp))
    rw [localDensity_ram_unit hf hD p hpD m hpm, kronR_eq_zero_of_dvd hpp hpD]
    ring

/-! ### Siegel's formula for $n = 2$ -/

/-- $D$ has at least one prime factor ($t \ge 1$). -/
theorem one_le_card_primeFactors : 1 ≤ D.natAbs.primeFactors.card := by
  have h3 := three_le_natAbs (D := D)
  exact Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))

/-- **Siegel's formula for binary forms, $m$ prime to $D$** (the first step; the general case is
`siegelFormula_binary`). Siegel's Hauptsatz for $n = 2$, $\varepsilon = \frac12$, convention
"$L(1,\chi_D)^{-1}\times$ finite product"; unconditional. Let $D < 0$ be a fundamental discriminant,
$f$ a primitive positive definite form of discriminant $D$ (`PosForms D`) and $m \ge 1$ prime to $D$. Then
$$r_{\mathcal G}(m) = \frac12\,\beta_\infty(m)\,P_f(m), \qquad P_f(m) = L(1,\chi_D)^{-1}\prod_{p \mid mD}\frac{\beta_p(m)}{1 - \chi_D(p)/p},$$
with $r_{\mathcal G}$ = `Siegel.genusRepAvg` ($\mathrm{GL}_2(\mathbb{Z})$-classes, weights $1/|\mathrm{Aut}|$),
$\beta_\infty$, $\beta_p$ the repo's densities (`betaInf`, `localDensity`), and $P_f(m)$ = `binaryEulerValue`. In the
repo's notation: `genusRepAvg f m = (1/2) * aEWith f m (binaryEulerValue f D m)`.

**The constant $\varepsilon = \frac12$** (Siegel 1935, Hauptsatz: $\varepsilon = \frac12$ when $n = m + 1$, here $n = 2$ and
the represented form has rank $1$; $\varepsilon = 1$ otherwise). It comes out exactly: by the genus average formula,
$r_{\mathcal G}(m) = \frac{w\,2^{t-1}}{h}S\cdot[\psi_p(m) = \chi_p(f)\ \forall p \mid D]$ with $S = \sum_{d\mid m}\chi_D(d)$; on the
local side $\beta_\infty = 2\pi/\sqrt{|D|}$ (`betaInf_binary`), $L(1,\chi_D) = 2\pi h/(w\sqrt{|D|})$ and
$C_f(m) = S\cdot 2^t[\ldots]$ (`binaryEulerCorr_coprime`, `prod_ram_eq`), so
$\beta_\infty P_f(m) = \frac{w\,2^{t}}{h}S[\ldots] = 2\,r_{\mathcal G}(m)$. -/
@[kb "siegel1935" "Hauptsatz (ε = 1/2 for n = 2) [unverified locator]"]
theorem siegelFormula_binary_coprime [Fact (D < 0)] (f : PosForms D) {m : ℕ} (hm : m ≠ 0)
    (hcop : Nat.Coprime m D.natAbs) :
    Siegel.genusRepAvg f.1 m = (1 / 2 : ℝ) * aEWith f.1 m (binaryEulerValue f.1 D m) := by
  have hD : D < 0 := Fact.out
  obtain ⟨hf, hfD, -⟩ := f.2
  rw [genusRepAvg_binary_coprime f hm hcop, aEWith, binaryEulerValue,
    betaInf_binary f.1 (by rw [hfD]; exact hD), LOne_eq_of_neg hD,
    binaryEulerCorr_coprime hf hfD hm hcop, prod_ram_eq hf hfD hcop, hfD]
  have habs : |(D : ℝ)| = -(D : ℝ) := abs_of_neg (by exact_mod_cast hD)
  rw [habs]
  have hsq : Real.sqrt (-(D : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith)).ne'
  have hw : (NumberField.Units.torsionOrder (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have hh : (NumberField.classNumber (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (NumberField.RingOfIntegers (QField D)))).ne'
  have ht := one_le_card_primeFactors (D := D)
  obtain ⟨t, ht'⟩ : ∃ t, D.natAbs.primeFactors.card = t + 1 := ⟨_, (Nat.sub_add_cancel ht).symm⟩
  rw [ht', Nat.add_sub_cancel]
  have hS : ∑ d ∈ m.divisors, kronR D d = ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℝ) := rfl
  rw [hS]
  split_ifs
  · field_simp
    ring
  · simp

/-- **The genus average is nonzero at some $m$ prime to $D$** ($D < 0$): a value $m = f(x, y) > 0$ prime to $D$
(`exists_coprime_value`) is the norm of an ideal (`exists_ideal_of_eval`), so $\sum_{d \mid m}\chi_D(d) \ge 1$. -/
theorem exists_genusRepAvg_ne_zero [Fact (D < 0)] (f : PosForms D) :
    ∃ m : ℕ, m ≠ 0 ∧ Nat.Coprime m D.natAbs ∧ Siegel.genusRepAvg f.1 m ≠ 0 := by
  have hD : D < 0 := Fact.out
  have hD0 : D.natAbs ≠ 0 := by have := three_le_natAbs (D := D); omega
  obtain ⟨x, y, hx, -, -, hcopv⟩ := exists_coprime_value f.2.1 hD0
  have hpos : 0 < f.1.eval x y := f.toPrim.2.2.1 x y (by intro h; simp at h; omega)
  set m : ℕ := (f.1.eval x y).toNat
  have hm : (m : ℤ) = f.1.eval x y := Int.toNat_of_nonneg hpos.le
  have hm0 : m ≠ 0 := by omega
  have hcop : Nat.Coprime m D.natAbs := by
    refine Nat.coprime_of_dvd fun p hp hpm hpD => hcopv p hp hpD ?_
    rw [← hm]; exact_mod_cast hpm
  refine ⟨m, hm0, hcop, ?_⟩
  rw [genusRepAvg_binary f hm0, ite_eq_left ⟨f.1, Siegel.SameGenus.refl _, x, y, hm.symm⟩]
  have hw : (NumberField.Units.torsionOrder (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have hh : (NumberField.classNumber (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (NumberField.RingOfIntegers (QField D)))).ne'
  refine mul_ne_zero (div_ne_zero (mul_ne_zero hw (by positivity)) hh) ?_
  obtain ⟨𝔟, hN, -⟩ := exists_ideal_of_eval hD f.toPrim hm0 hm.symm
  have hcard := card_ideals_order_absNorm_eq (D := D) hm0
  have hpos' : 0 < Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} := by
    have : Finite {I : Ideal (QOrder D) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    exact Nat.card_pos_iff.mpr ⟨⟨⟨𝔟, hN⟩⟩, this⟩
  intro h0
  have : ((∑ d ∈ m.divisors, kronZ D (d : ZMod D.natAbs) : ℤ) : ℝ) = 0 := by push_cast; exact h0
  rw [← hcard] at this
  have : (Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} : ℝ) = 0 := by exact_mod_cast this
  exact hpos'.ne' (by exact_mod_cast this)

/-- **$\varepsilon = \frac12$ is the only constant**: if $r_{\mathcal G}(m) = \varepsilon\,\beta_\infty(m)P_f(m)$ for all $m \ge 1$
prime to $D$, then $\varepsilon = \frac12$ (in particular Siegel's $\varepsilon = 1$ of the case $n \ge 3$ is wrong for
$n = 2$). -/
@[kb "siegel1935" "Hauptsatz (the factor ε) [unverified locator]"]
theorem epsilon_eq_half [Fact (D < 0)] (f : PosForms D) (ε : ℝ)
    (h : ∀ m : ℕ, m ≠ 0 → Nat.Coprime m D.natAbs →
      Siegel.genusRepAvg f.1 m = ε * aEWith f.1 m (binaryEulerValue f.1 D m)) :
    ε = 1 / 2 := by
  obtain ⟨m, hm0, hcop, hne⟩ := exists_genusRepAvg_ne_zero f
  have h1 := h m hm0 hcop
  have h2 := siegelFormula_binary_coprime f hm0 hcop
  have hX : aEWith f.1 m (binaryEulerValue f.1 D m) ≠ 0 := by
    intro hX; rw [h2, hX, mul_zero] at hne; exact hne rfl
  have := h1.symm.trans h2
  exact mul_right_cancel₀ hX this

/-- **The Siegel side, explicitly** ($D < 0$ fundamental, $f$ primitive of discriminant $D$, $m \ge 1$ prime to $D$):
$$\tfrac12\,\beta_\infty(m)\,P_f(m) = \frac{w}{2h}\Big(\sum_{d \mid m}\chi_D(d)\Big)\prod_{p \mid D}\big(1 + \chi_p(f)\psi_p(m)\big).$$
(Used for the cross-checks; with `prod_ram_eq` it is $\frac{w2^{t-1}}{h}\sum_{d\mid m}\chi_D(d)$ or $0$.) -/
theorem siegelSide_explicit (hD : D < 0) {f : BinQF} (hf : Primitive f) (hfD : f.disc = D) {m : ℕ} (hm : m ≠ 0)
    (hcop : Nat.Coprime m D.natAbs) :
    (1 / 2 : ℝ) * aEWith f m (binaryEulerValue f D m) =
      NumberField.Units.torsionOrder (QField D) / (2 * NumberField.classNumber (QField D)) *
        ((∑ d ∈ m.divisors, kronR D d) *
          ∏ p ∈ D.natAbs.primeFactors, (1 + (formChar f p : ℝ) * (genusChar D p m : ℝ))) := by
  rw [aEWith, binaryEulerValue, betaInf_binary f (by rw [hfD]; exact hD), LOne_eq_of_neg hD,
    binaryEulerCorr_coprime hf hfD hm hcop, hfD, abs_of_neg (by exact_mod_cast hD : (D : ℝ) < 0)]
  have hsq : Real.sqrt (-(D : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith)).ne'
  have hw : (NumberField.Units.torsionOrder (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have hh : (NumberField.classNumber (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (NumberField.RingOfIntegers (QField D)))).ne'
  field_simp

/-! ### Siegel's formula for every $m \ge 1$ -/

/-- **The finite correction for every $m \ne 0$:** $C_f(m) = \big(\sum_{d \mid m}\chi_D(d)\big)\prod_{p \mid D}\beta_p(m)$ and
$\beta_p(m) = 1 + \chi_p(f)c_p(m)$ (`localDensity_ram`); at $p \mid m$, $p \nmid D$ the factor is $\sum_{j \le v_p(m)}\chi_D(p)^j$,
and at $p \mid \gcd(m, D)$ the divisor-sum factor is $1$. -/
theorem binaryEulerCorr_eq {f : BinQF} (hf : Primitive f) (hD : f.disc = D) {m : ℕ} (hm : m ≠ 0) :
    binaryEulerCorr f D m = (∑ d ∈ m.divisors, kronR D d) *
      ∏ p ∈ D.natAbs.primeFactors, (1 + (formChar f p : ℝ) * (ramChar p D m : ℝ)) := by
  have hD0 : D.natAbs ≠ 0 := by have := three_le_natAbs (D := D); omega
  set A := D.natAbs.primeFactors
  set B := m.primeFactors
  have hgood : ∀ p ∈ B \ A, localDensity f p m / (1 - kronR D p / p) =
      ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j := by
    intro p hp
    obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpB
    have : Fact p.Prime := ⟨hpp⟩
    have hpD : ¬ (p : ℤ) ∣ D := fun h => hpA (Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp h, hD0⟩)
    rw [localDensity_good_binary f hD p hpD m (by exact_mod_cast hm), goodFactor, Int.natAbs_natCast]
    change ((1 - kronR D p / p) * ∑ j ∈ _, kronR D p ^ j) / (1 - kronR D p / p) = _
    rw [mul_div_cancel_left₀ _ (one_sub_kronR_div_ne_zero hpp)]
  have hram : ∀ p ∈ A, localDensity f p m / (1 - kronR D p / p) =
      1 + (formChar f p : ℝ) * (ramChar p D m : ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hpD : (p : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    rw [localDensity_ram hf hD p hpD (by exact_mod_cast hm), kronR_eq_zero_of_dvd hpp hpD]
    simp
  have hsum : ∑ d ∈ m.divisors, kronR D d =
      ∏ p ∈ B \ A, ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j := by
    rw [sum_divisors_kronR hm, ← Finset.prod_sdiff (Finset.inter_subset_left : B ∩ A ⊆ B)]
    have h1 : ∏ p ∈ B ∩ A, ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨-, hpA⟩ := Finset.mem_inter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hpA
      rw [kronR_eq_zero_of_dvd hpp (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hpA)),
        Finset.sum_range_succ']
      simp
    rw [h1, mul_one]
    congr 1
    ext q; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [binaryEulerCorr, show ((m : ℤ) * D).natAbs = m * D.natAbs by rw [Int.natAbs_mul, Int.natAbs_natCast],
    Nat.primeFactors_mul hm hD0, Finset.union_comm, ← Finset.union_sdiff_self_eq_union,
    Finset.prod_union Finset.disjoint_sdiff, Finset.prod_congr rfl hgood, Finset.prod_congr rfl hram, hsum]
  ring

/-- **The ramified product, every $m \ne 0$:** $\prod_{p\mid D}(1 + \chi_p(f)c_p(m)) = 2^t$ if $c_p(m) = \chi_p(f)$ for all
$p \mid D$, and $0$ otherwise. -/
theorem prod_ram_eq_general {f : BinQF} (hf : Primitive f) (hD : f.disc = D) {m : ℤ} (hm : m ≠ 0) :
    ∏ p ∈ D.natAbs.primeFactors, (1 + (formChar f p : ℝ) * (ramChar p D m : ℝ)) =
      if ∀ p ∈ D.natAbs.primeFactors, ramChar p D m = formChar f p then
        (2 : ℝ) ^ D.natAbs.primeFactors.card else 0 := by
  have hval : ∀ p ∈ D.natAbs.primeFactors, (1 + (formChar f p : ℝ) * (ramChar p D m : ℝ)) =
      if ramChar p D m = formChar f p then 2 else 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hpD : (p : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    have hx : formChar f p ^ 2 = 1 := by
      unfold formChar; exact genusChar_sq _ hpp (not_dvd_charCoeff hf hpp (hD ▸ hpD))
    exact one_add_mul_of_sq hx (ramChar_sq p hpD hm)
  rw [Finset.prod_congr rfl hval]
  split_ifs with h
  · rw [Finset.prod_congr rfl fun p hp => ite_eq_left (h p hp), Finset.prod_const]
  · push Not at h
    obtain ⟨p, hp, hne⟩ := h
    exact Finset.prod_eq_zero hp (ite_eq_right hne)

/-- A global representation gives a positive local density. -/
theorem localDensity_pos_of_eval {g : BinQF} (hg : g.disc ≠ 0) (p : ℕ) [Fact p.Prime] {x y m : ℤ}
    (hm : m ≠ 0) (h : g.eval x y = m) : 0 < localDensity g p m := by
  refine localDensity_pos_of_isLocallyRepresentedAt g (by
    unfold QuadForm.Nondegenerate; rw [hessian_det_eq_neg_disc]; exact neg_ne_zero.mpr hg) p m hm ?_
  refine Filter.Eventually.of_forall fun k => ?_
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold repCount
  refine Nat.card_pos_iff.mpr ⟨⟨⟨![(x : ZMod (p ^ k)), (y : ZMod (p ^ k))], ?_⟩⟩, inferInstance⟩
  rw [evalIn_bin, ← h, BinQF.eval_eq]
  simp

/-- **The genus of $f$ represents $m$ iff $c_p(m) = \chi_p(f)$ for all $p \mid D$** (when some ideal has norm $m$, i.e.
$\sum_{d \mid m}\chi_D(d) \ne 0$). ($\Rightarrow$) a form $g$ of the genus with $g(x, y) = m$ has $\beta_p(g, m) > 0$, so
$\chi_p(f) = \chi_p(g) = c_p(m)$. ($\Leftarrow$) a form $F$ in the class inverse to an ideal of norm $m$ represents $m$, so $\chi_p(F) = c_p(m) = \chi_p(f)$ for all $p \mid D$, and $F$ is in the genus of $f$
(`sameGenus_iff_formChar_eq`). -/
theorem genus_represents_iff [Fact (D < 0)] (f : PosForms D) {m : ℕ} (hm : m ≠ 0)
    (hS : ∑ d ∈ m.divisors, kronR D d ≠ 0) :
    (∃ g : BinQF, SameGenus f.1 g ∧ g.Represents m) ↔
      ∀ p ∈ D.natAbs.primeFactors, ramChar p D m = formChar f.1 p := by
  have hD : D < 0 := Fact.out
  obtain ⟨hf, hfD, hfpos⟩ := f.2
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  -- a form of discriminant D representing m has c_p(m) = χ_p
  have key : ∀ g : BinQF, Primitive g → g.disc = D → g.Represents m →
      ∀ p ∈ D.natAbs.primeFactors, ramChar p D m = formChar g p := by
    intro g hg hgD ⟨x, y, hxy⟩ p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hpD : (p : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    have hpos := localDensity_pos_of_eval (by rw [hgD]; exact hD.ne) p hm' hxy
    rw [localDensity_ram hg hgD p hpD hm'] at hpos
    have hx : formChar g p ^ 2 = 1 := by
      unfold formChar; exact genusChar_sq _ hpp (not_dvd_charCoeff hg hpp (hgD ▸ hpD))
    have h := one_add_mul_of_sq hx (ramChar_sq p hpD hm')
    rw [h] at hpos
    by_contra hne
    rw [ite_eq_right hne] at hpos
    exact lt_irrefl _ hpos
  constructor
  · rintro ⟨g, hs, hrep⟩ p hp
    obtain ⟨h1, h2, h3⟩ := mem_primPosForm_of_sameGenus f.toPrim hs
    have hg : Primitive g := (primitive_iff_isPrimitive g).mpr h3
    have hgpos : g.PosDef' := (posDef_iff_posDef' g).mp h2
    rw [key g hg h1 hrep p hp,
      ((sameGenus_iff_formChar_eq hf hg hfD h1 hfpos hgpos).mp hs p hp).symm]
  · intro hall
    have hcard := card_ideals_order_absNorm_eq (D := D) hm
    have hne : Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} ≠ 0 := by
      intro h0
      apply hS
      have : ((∑ d ∈ m.divisors, kronZ D (d : ZMod D.natAbs) : ℤ) : ℝ) = 0 := by
        rw [← hcard, h0]; simp
      push_cast at this; exact this
    have : Finite {I : Ideal (QOrder D) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    obtain ⟨⟨𝔟, hN⟩⟩ := (Nat.card_ne_zero.mp hne).1
    have h0 := mem_nonZeroDivisors_of_absNorm (D := D) (I := 𝔟) (by rw [hN]; exact hm)
    set C := isFormClassGroupOrder hD
    set x := ClassGroup.mk0 (⟨𝔟, h0⟩ : (Ideal (QOrder D))⁰)
    set F := C.rep x⁻¹
    have hF : idealClass F.toPrim = x⁻¹ := C.cls_rep x⁻¹
    have hc' : ClassGroup.mk0 (⟨𝔟, h0⟩ : (Ideal (QOrder D))⁰) = (idealClass F.toPrim)⁻¹ := by rw [hF, inv_inv]
    obtain ⟨u, v, huv⟩ := exists_eval_of_ideal hD F.toPrim hN h0 hc'
    obtain ⟨hFp, hFD, hFpos⟩ := F.2
    refine ⟨F.1, (sameGenus_iff_formChar_eq hf hFp hfD hFD hfpos hFpos).mpr fun p hp => ?_, u, v, huv⟩
    rw [← hall p hp, key F.1 hFp hFD ⟨u, v, huv⟩ p hp]

/-- **Siegel's formula for binary forms (Siegel's Hauptsatz for $n = 2$, $\varepsilon = \frac12$), every $m \ge 1$;
convention "$L(1,\chi_D)^{-1}\times$ finite product"; unconditional.** Let $D < 0$ be a fundamental discriminant, $f$ a
primitive positive definite form of discriminant $D$ (`PosForms D`), and $m \ge 1$. Then
$$r_{\mathcal G}(m) = \frac12\,\beta_\infty(m)\,P_f(m), \qquad P_f(m) = L(1,\chi_D)^{-1}\prod_{p \mid mD}\frac{\beta_p(m)}{1 - \chi_D(p)/p},$$
i.e. `genusRepAvg f m = (1/2) * aEWith f m (binaryEulerValue f D m)`, with $r_{\mathcal G}$ = `Siegel.genusRepAvg`
($\mathrm{GL}_2(\mathbb{Z})$-classes of the genus, weights $1/|\mathrm{Aut}|$) and the repo's $\beta_\infty$, $\beta_p$.

**$\varepsilon = \frac12$ exactly:** the genus average formula gives $r_{\mathcal G}(m) = \frac{w2^{t-1}}{h}S\cdot[\text{the genus represents } m]$
($S = \sum_{d\mid m}\chi_D(d)$); the local side is $\frac12\cdot\frac{2\pi}{\sqrt{|D|}}\cdot\frac{w\sqrt{|D|}}{2\pi h}\cdot S\cdot
\prod_{p\mid D}(1 + \chi_p(f)c_p(m))$ (`betaInf_binary`, `binaryEulerCorr_eq`), the product is $2^t$ or $0$
(`prod_ram_eq_general`), and it is $2^t$ exactly when the genus represents $m$ (`genus_represents_iff`). Source:
Siegel (1935), Hauptsatz ($\varepsilon = \frac12$ for $n = m + 1$) [unverified locator]. -/
@[kb "siegel1935" "Hauptsatz (ε = 1/2 for n = 2) [unverified locator]"]
theorem siegelFormula_binary [Fact (D < 0)] (f : PosForms D) {m : ℕ} (hm : m ≠ 0) :
    Siegel.genusRepAvg f.1 m = (1 / 2 : ℝ) * aEWith f.1 m (binaryEulerValue f.1 D m) := by
  have hD : D < 0 := Fact.out
  obtain ⟨hf, hfD, -⟩ := f.2
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  rw [genusRepAvg_binary f hm, aEWith, binaryEulerValue, betaInf_binary f.1 (by rw [hfD]; exact hD),
    LOne_eq_of_neg hD, binaryEulerCorr_eq hf hfD hm, prod_ram_eq_general hf hfD hm', hfD,
    abs_of_neg (by exact_mod_cast hD : (D : ℝ) < 0)]
  have hsq : Real.sqrt (-(D : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith)).ne'
  have hw : (NumberField.Units.torsionOrder (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have hh : (NumberField.classNumber (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (NumberField.RingOfIntegers (QField D)))).ne'
  have ht := one_le_card_primeFactors (D := D)
  obtain ⟨t, ht'⟩ : ∃ t, D.natAbs.primeFactors.card = t + 1 := ⟨_, (Nat.sub_add_cancel ht).symm⟩
  have hS : ∑ d ∈ m.divisors, kronR D d = ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℝ) := rfl
  by_cases hS0 : ∑ d ∈ m.divisors, kronR D d = 0
  · rw [← hS, hS0]; simp
  · rw [← hS, propext (genus_represents_iff f hm hS0), ht', Nat.add_sub_cancel]
    split_ifs
    · field_simp; ring
    · simp

/-- **Siegel's formula for binary forms, natural-order convention, every $m \ge 1$; conditional on
`EulerProductAtOne D`.** For $D < 0$ fundamental, $f$ primitive positive definite of discriminant $D$, $m \ge 1$, and
**any** $P$ with $\prod_{p \le X}\beta_p(m) \to P$ (`IsEulerProductValue f m P`, the convention of `SiegelFormula3`):
$$r_{\mathcal G}(m) = \frac12\,\beta_\infty(m)\,P = \frac12\,\beta_\infty(m)\prod_p\beta_p(m).$$
Under the input such a $P$ exists and equals `binaryEulerValue f D m` (`isEulerProductValue_binary`). -/
@[kb "siegel1935" "Hauptsatz (ε = 1/2 for n = 2), natural-order product [unverified locator]"]
theorem siegelFormula_binary_natural [Fact (D < 0)] (hE : EulerProductAtOne D) (f : PosForms D) {m : ℕ}
    (hm : m ≠ 0) {P : ℝ} (hP : IsEulerProductValue f.1 m P) :
    Siegel.genusRepAvg f.1 m = (1 / 2 : ℝ) * aEWith f.1 m P := by
  have hval := isEulerProductValue_binary hE f.2.2.1 (m := (m : ℤ)) (by exact_mod_cast hm)
  rw [tendsto_nhds_unique hP hval]
  exact siegelFormula_binary f hm

/-- **The natural-order Euler product exists** (under `EulerProductAtOne D`) and Siegel's formula holds with it. -/
theorem exists_siegelFormula_binary_natural [Fact (D < 0)] (hE : EulerProductAtOne D) (f : PosForms D) {m : ℕ}
    (hm : m ≠ 0) :
    ∃ P : ℝ, IsEulerProductValue f.1 m P ∧ Siegel.genusRepAvg f.1 m = (1 / 2 : ℝ) * aEWith f.1 m P :=
  ⟨_, isEulerProductValue_binary hE f.2.2.1 (by exact_mod_cast hm), siegelFormula_binary f hm⟩

end QuadFormsKB.Binary
