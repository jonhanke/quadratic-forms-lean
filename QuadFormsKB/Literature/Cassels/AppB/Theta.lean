/-
# Cassels, Appendix B, §1: the theta function and Jacobi's identities

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), §1, pp. 368-369.

**Setting.** $\Theta(z) = \sum_{m\in\mathbb Z} z^{m^2}$ for complex $|z|<1$, and $\theta(s) = \Theta(e^{\pi i s})$ for
$\operatorname{Im} s>0$. Mathlib's `jacobiTheta` $\tau \mapsto \sum_{m\in\mathbb Z} e^{\pi i m^2\tau}$ is $\theta$.

**Formalized (proved).**
* `casselsTheta` $=\Theta$; summability for $|z|<1$ (`summable_casselsTheta`); $\theta(s) = $ `jacobiTheta` $s$
  (`casselsTheta_exp_eq_jacobiTheta`).
* $\theta(s+2)=\theta(s)$ (`casselsTheta_exp_add_two`).
* The transformation $\theta(-1/s) = \frac{\sqrt s}{\sqrt i}\theta(s)$ with both square roots normalized to have positive
  real and positive imaginary part (`casselsTheta_exp_neg_inv`), together with the existence and uniqueness of the
  normalized square root of a point of the upper half plane (`exists_unique_sqrt_firstQuadrant`).
* The coefficient forms of Jacobi's identities for two and four squares (`repNum_sumSq_two_coeff`,
  `repNum_sumSq_four_coeff`): comparing the coefficient of $z^N$ on both sides, after expanding every geometric series.

**Formalized as named statements** (coefficient forms; a full proof needs the theory of modular forms for $\Gamma_0(4)$ of
weights $3$, $4$, $12$ respectively): `JacobiSixSquares`, `JacobiEightSquares`, `RamanujanTwentyFourSquares`.

**Conventions.** For a natural number $N\ge 1$, $r_k(N) = $ `Siegel.repNum (Siegel.sumSq k) N` is the number of
$\vec x\in\mathbb Z^k$ with $x_0^2+\dots+x_{k-1}^2 = N$ (Cassels' $a_f(N)$ for $f=x_1^2+\dots+x_k^2$; the variables are
indexed from $0$ here). Expanding $\frac{z^m}{1-\varepsilon z^m} = \sum_{j\ge1}\varepsilon^{j-1}z^{mj}$ shows that the
coefficient of $z^N$ in each right-hand side is a divisor sum over $m\mid N$ with $j=N/m$; those divisor sums are what the
coefficient forms state. We write $\chi_{-4}$ for the nontrivial character modulo $4$ (Mathlib `ZMod.χ₄`, value $0$ on even
numbers).

**Erratum (identity (1.4), as printed in the copy used for this transcription).** The first sum of (1.4) has denominator
$1-z^{2m}$; Jacobi's identity has $1+z^{2m}$ there. With $1-z^{2m}$ the coefficient of $z^N$ would be
$16\sum_{m\mid N,\,N/m\ \mathrm{odd}}m^2$ without the sign $\chi_{-4}(N/m)$; this is false already for $N=3$ (it gives $192$,
but $r_6(3)=160$). Confirmed by brute-force counting of representations by six squares for $1\le N\le 30$ (the corrected
coefficient $16\sum_{m\mid N}\chi_{-4}(N/m)m^2-4\sum_{m\mid N}\chi_{-4}(m)m^2$ matches every value; the printed one fails at
$N=3,6,7,9,11,12,\dots$). See `JacobiSixSquares`.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import QuadFormsKB.Tamagawa.Classical.BinaryJacobi
import QuadFormsKB.Siegel.FourSquaresJacobi
import QuadFormsKB.Literature.Cassels.AppBSec5

open Complex Real
open scoped Real

noncomputable section

namespace QuadFormsKB.Cassels

/-! ### The theta series $\Theta$ and its relation to `jacobiTheta` -/

/-- **The series $\Theta(z)=\sum_{m\in\mathbb Z}z^{m^2}$** (Cassels, App. B, (1.1)). Argument: `z`, a complex number
(the series converges when $|z|<1$, `summable_casselsTheta`). The exponent $m^2$ is taken as the natural number
`m.natAbs ^ 2`. -/
def casselsTheta (z : ℂ) : ℂ := ∑' m : ℤ, z ^ (m.natAbs ^ 2)

/-- Helper: $\sum$ of $\|z\|^{|m|}$ over $m\in\mathbb Z$ converges for $\|z\|<1$. -/
lemma summable_norm_pow_natAbs {z : ℂ} (hz : ‖z‖ < 1) : Summable fun m : ℤ => ‖z‖ ^ m.natAbs := by
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_geometric_of_lt_one (norm_nonneg z) hz
  · simpa using summable_geometric_of_lt_one (norm_nonneg z) hz

/-- **Convergence of $\Theta$** (Cassels, App. B, §1, (1.1), pp. 368-369): for complex $z$ with $|z|<1$ the family
$(z^{m^2})_{m\in\mathbb Z}$ is summable. Argument: `z`, `hz : ‖z‖ < 1`. -/
@[kb "cassels1978" "App. B, §1, (1.1), pp. 368–369 (convergence of Θ for |z| < 1)"]
theorem summable_casselsTheta {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun m : ℤ => z ^ (m.natAbs ^ 2) := by
  refine Summable.of_norm_bounded (summable_norm_pow_natAbs hz) fun m => ?_
  rw [norm_pow]
  refine pow_le_pow_of_le_one (norm_nonneg z) hz.le ?_
  nlinarith [Nat.zero_le m.natAbs, Nat.le_mul_self m.natAbs, sq m.natAbs]

/-- Helper: $e^{\pi i m^2 s} = (e^{\pi i s})^{m^2}$ with the exponent `m.natAbs ^ 2`. -/
lemma cexp_pi_mul_sq (m : ℤ) (s : ℂ) :
    cexp (π * I * (m : ℂ) ^ 2 * s) = (cexp (π * I * s)) ^ (m.natAbs ^ 2) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have h : ((m.natAbs ^ 2 : ℕ) : ℂ) = (m : ℂ) ^ 2 := by
    rcases Int.natAbs_eq m with h | h <;> generalize m.natAbs = k at h ⊢ <;> subst h <;> simp
  rw [h]; ring

/-- **$\theta(s)=\Theta(e^{\pi i s})$ is Mathlib's `jacobiTheta`** (Cassels, App. B, §1, (1.1), pp. 368-369): for
$\operatorname{Im}s>0$ (argument `s`, hypothesis `hs`), $\Theta(e^{\pi i s}) = \sum_{m\in\mathbb Z}e^{\pi i m^2 s}$
(`jacobiTheta s`). -/
@[kb "cassels1978" "App. B, §1, (1.1), pp. 368–369"]
theorem casselsTheta_exp_eq_jacobiTheta (s : ℂ) (_hs : 0 < s.im) :
    casselsTheta (cexp (π * I * s)) = jacobiTheta s := by
  unfold casselsTheta jacobiTheta
  exact tsum_congr fun m => (cexp_pi_mul_sq m s).symm

/-! ### Periodicity -/

/-- **$\theta(s+2)=\theta(s)$** (Cassels, App. B, §1, p. 369): $\Theta(e^{\pi i(s+2)}) = \Theta(e^{\pi i s})$, for every
$s$ in the upper half plane (argument `s`, hypothesis `hs : 0 < s.im`; the hypothesis is only needed to identify the series
with `jacobiTheta`, from Mathlib's `jacobiTheta_two_add`). -/
@[kb "cassels1978" "App. B, §1, p. 369 (θ(s + 2) = θ(s))"]
theorem casselsTheta_exp_add_two (s : ℂ) (hs : 0 < s.im) :
    casselsTheta (cexp (π * I * (s + 2))) = casselsTheta (cexp (π * I * s)) := by
  rw [casselsTheta_exp_eq_jacobiTheta (s + 2) (by simpa using hs), casselsTheta_exp_eq_jacobiTheta s hs,
    add_comm, jacobiTheta_two_add]

/-! ### The transformation formula (1.1 bis) -/

/-- Helper: real and imaginary parts of the principal square root `x ^ (2⁻¹)` for `x ≠ 0`. -/
lemma cpow_half_re_im (x : ℂ) (hx : x ≠ 0) :
    (x ^ (2⁻¹ : ℂ)).re = Real.exp (Real.log ‖x‖ * 2⁻¹) * Real.cos (arg x / 2) ∧
    (x ^ (2⁻¹ : ℂ)).im = Real.exp (Real.log ‖x‖ * 2⁻¹) * Real.sin (arg x / 2) := by
  rw [cpow_def_of_ne_zero hx, Complex.exp_re, Complex.exp_im]
  have h1 : (Complex.log x * 2⁻¹).re = Real.log ‖x‖ * 2⁻¹ := by
    simp [Complex.log_re]
  have h2 : (Complex.log x * 2⁻¹).im = arg x / 2 := by
    simp [Complex.log_im]
    ring
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

/-- Helper: the square of the principal square root `x ^ (2⁻¹)` is `x`. -/
lemma cpow_half_sq (x : ℂ) : (x ^ (2⁻¹ : ℂ)) ^ 2 = x := by
  simp

/-- Helper: the principal square root of a point $s$ with $\operatorname{Im}s>0$ has positive real and imaginary part. -/
lemma sqrt_pos_parts {s : ℂ} (hs : 0 < s.im) :
    (s ^ (2⁻¹ : ℂ)) ^ 2 = s ∧ 0 < (s ^ (2⁻¹ : ℂ)).re ∧ 0 < (s ^ (2⁻¹ : ℂ)).im := by
  have hx : s ≠ 0 := fun h => by simp [h] at hs
  have hpos : 0 < arg s :=
    lt_of_le_of_ne (arg_nonneg_iff.mpr hs.le) fun h => by
      have := (arg_eq_zero_iff.mp h.symm).2
      linarith
  have hlt : arg s < π := arg_lt_pi_iff.mpr (Or.inr hs.ne')
  obtain ⟨hre, him⟩ := cpow_half_re_im s hx
  refine ⟨cpow_half_sq s, ?_, ?_⟩
  · rw [hre]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  · rw [him]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-- Helper: two complex numbers with positive real part and equal squares are equal. -/
lemma eq_of_sq_eq_of_re_pos {w w' : ℂ} (h : w ^ 2 = w' ^ 2) (hw : 0 < w.re) (hw' : 0 < w'.re) : w = w' := by
  have h0 : (w - w') * (w + w') = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · have := congrArg Complex.re h1
    simp only [add_re, zero_re] at this
    linarith

/-- **The normalized square root** (Cassels, App. B, §1, p. 369, the convention for $\sqrt s$ in (1.1 bis)): every $s$ with
$\operatorname{Im}s>0$ has exactly one square root $w$ (`w ^ 2 = s`) with positive real part, and this root also has
positive imaginary part; it is the principal branch `s ^ (2⁻¹)`. Argument: `s`, `hs : 0 < s.im`. In particular
$\sqrt i = (1+i)/\sqrt2$. -/
@[kb "cassels1978" "App. B, §1, (1.1 bis), p. 369 (normalization of the square roots)"]
theorem exists_unique_sqrt_firstQuadrant {s : ℂ} (hs : 0 < s.im) :
    ∃! w : ℂ, w ^ 2 = s ∧ 0 < w.re ∧ 0 < w.im := by
  obtain ⟨h1, h2, h3⟩ := sqrt_pos_parts hs
  exact ⟨s ^ (2⁻¹ : ℂ), ⟨h1, h2, h3⟩, fun w hw => eq_of_sq_eq_of_re_pos (hw.1.trans h1.symm) hw.2.1 h2⟩

/-- **$\sqrt i = (1+i)/\sqrt 2$:** this is the square root of $i$ with positive real and imaginary parts. -/
theorem sqrt_I_firstQuadrant {w : ℂ} (h : w ^ 2 = I) (hr : 0 < w.re) (_hi : 0 < w.im) :
    w = (1 + I) / (Real.sqrt 2 : ℂ) := by
  refine eq_of_sq_eq_of_re_pos (h.trans ?_) hr ?_
  · have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
    have h3 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt 2 := by positivity
      exact_mod_cast this.ne'
    rw [div_pow, h2]
    have : (1 + I) ^ 2 = 2 * I := by ring_nf; rw [I_sq]; ring
    rw [this]; ring
  · have : (0 : ℝ) < Real.sqrt 2 := by positivity
    simp [Complex.div_re, Complex.normSq_ofReal]

/-- **The transformation formula (1.1 bis)** (Cassels, App. B, §1, p. 369): $\theta(-1/s)=\dfrac{\sqrt s}{\sqrt i}\,\theta(s)$
for $\operatorname{Im}s>0$, where $\theta(s) = \Theta(e^{\pi i s})$. Arguments: `s` with `hs : 0 < s.im`; `ws` is
$\sqrt s$, a square root of `s` with positive real part `hwsr` and positive imaginary part `hwsi` (unique, by
`exists_unique_sqrt_firstQuadrant`); `wi` is $\sqrt i$, the square root of $i$ with positive real and imaginary parts
(`wi = (1 + I)/√2`, `sqrt_I_firstQuadrant`). Derived from Mathlib's `jacobiTheta_S_smul`, which uses the principal root of
$-is$. -/
@[kb "cassels1978" "App. B, §1, (1.1 bis), p. 369"]
theorem casselsTheta_exp_neg_inv (s : ℂ) (hs : 0 < s.im) (ws wi : ℂ) (hws : ws ^ 2 = s) (hwsr : 0 < ws.re)
    (hwsi : 0 < ws.im) (hwi : wi ^ 2 = I) (hwir : 0 < wi.re) (hwii : 0 < wi.im) :
    casselsTheta (cexp (π * I * (-1 / s))) = ws / wi * casselsTheta (cexp (π * I * s)) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have him : 0 < (-1 / s).im := by
    rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]
    have : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs0
    have : 0 < s.im / Complex.normSq s := div_pos hs this
    rw [neg_div, neg_neg]; exact this
  rw [casselsTheta_exp_eq_jacobiTheta _ him, casselsTheta_exp_eq_jacobiTheta _ hs]
  have h := jacobiTheta_S_smul (⟨s, hs⟩ : UpperHalfPlane)
  simp only [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk] at h
  have e : (-1 / s) = (-s)⁻¹ := by rw [inv_neg, neg_div, one_div]
  rw [e, h]
  congr 1
  -- both sides are square roots of `-I * s` with positive real part
  have hx : (-I * s) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs0
  have hxre : 0 < (-I * s).re := by simpa using hs
  rw [one_div]
  refine eq_of_sq_eq_of_re_pos ?_ ?_ ?_
  · rw [cpow_half_sq, div_pow, hws, hwi]
    have : (I : ℂ)⁻¹ = -I := by simp
    rw [div_eq_mul_inv, this]; ring
  · obtain ⟨hre, -⟩ := cpow_half_re_im (-I * s) hx
    rw [hre]
    have habs : |arg (-I * s)| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hxre)
    rw [abs_lt] at habs
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  · have hn : 0 < Complex.normSq wi := Complex.normSq_pos.mpr (fun h => by simp [h] at hwir)
    rw [Complex.div_re]
    have : 0 < ws.re * wi.re / Complex.normSq wi := div_pos (mul_pos hwsr hwir) hn
    have : 0 < ws.im * wi.im / Complex.normSq wi := div_pos (mul_pos hwsi hwii) hn
    linarith

/-! ### Jacobi's identities (1.2)-(1.5) and Ramanujan's (1.6)-(1.9), in coefficient form -/

/-- Helper: the sum of two squares $x_0^2+x_1^2$ (`Siegel.sumSq 2`) is the library's `sumTwoSqZ`. -/
lemma sumSq_two_eq : Siegel.sumSq 2 = Tamagawa.Classical.sumTwoSqZ := by
  unfold Siegel.sumSq Tamagawa.Classical.sumTwoSqZ
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **Jacobi's identity (1.2), coefficient form** (Cassels, App. B, §1, p. 369): for $N\ge1$ the number of
$\vec x\in\mathbb Z^2$ with $x_0^2+x_1^2=N$ is $4\sum_{d\mid N}\chi_{-4}(d)$, which is the coefficient of $z^N$ in
$4\sum_{m\ge0}(-1)^m z^{2m+1}/(1-z^{2m+1})$ (only odd divisors $d=2m+1$ contribute, with sign $(-1)^m=\chi_{-4}(d)$).
Arguments: `N` the integer represented, `hN : 1 ≤ N`; `ZMod.χ₄` is $\chi_{-4}$. Equivalent to
$\Theta(z)^2 = 1+4\sum_{m\ge0}\cdots$ as power series (the constant terms agree since $r_2(0)=1$). -/
@[kb "cassels1978" "App. B, §1, (1.2), p. 369 (coefficient form)"]
theorem repNum_sumSq_two_coeff {N : ℕ} (hN : 1 ≤ N) :
    (Siegel.repNum (Siegel.sumSq 2) N : ℤ) = 4 * ∑ d ∈ N.divisors, ZMod.χ₄ (d : ZMod 4) := by
  have h := Tamagawa.Classical.dirichlet_sumTwoSq_r2 N hN
  rw [← sumSq_two_eq] at h
  exact_mod_cast h

/-- **Jacobi's identity (1.3), coefficient form** (Cassels, App. B, §1, p. 369): for $N\ge1$ the number of
$\vec x\in\mathbb Z^4$ with $x_0^2+x_1^2+x_2^2+x_3^2=N$ is $8\sum_{d\mid N,\,4\nmid d}d$, the coefficient of $z^N$ in
$8\sum_{m\ge1,\,4\nmid m}m z^m/(1-z^m)$. Argument: `N`, `hN : 1 ≤ N`. -/
@[kb "cassels1978" "App. B, §1, (1.3), p. 369 (coefficient form)"]
theorem repNum_sumSq_four_coeff {N : ℕ} (hN : 1 ≤ N) :
    (Siegel.repNum (Siegel.sumSq 4) N : ℤ) = 8 * ∑ d ∈ N.divisors.filter (fun d => ¬ 4 ∣ d), (d : ℤ) := by
  rw [Siegel.repNum_sumSq_four hN]
  push_cast
  rfl

/-- **Jacobi's identity (1.4), coefficient form, assumed** (Cassels, App. B, §1, p. 369). Field `coeff`: for every
$N\ge1$, the number $r_6(N)$ of $\vec x\in\mathbb Z^6$ with $x_0^2+\dots+x_5^2=N$ equals
$$16\sum_{d\mid N}\chi_{-4}(N/d)\,d^2-4\sum_{d\mid N}\chi_{-4}(d)\,d^2,$$
the coefficient of $z^N$ in $16\sum_{m>0}m^2z^m/(1+z^{2m})-4\sum_{m\ge0}(-1)^m(2m+1)^2z^{2m+1}/(1-z^{2m+1})$.

*Erratum:* the denominator of the first sum is printed $1-z^{2m}$; it must be $1+z^{2m}$ (otherwise the factor
$\chi_{-4}(N/d)$ is missing, and the identity fails at $N=3$: $192$ against $r_6(3)=160$). Confirmed by brute-force counts
for $1\le N\le 30$, see the module docstring.

A full proof needs the space of modular forms of weight $3$ for $\Gamma_0(4)$ with character $\chi_{-4}$ (the theta series
of $I_6$ lies in it), its Eisenstein series, and the comparison of the first coefficients. -/
@[kb "cassels1978" "App. B, §1, (1.4), p. 369 (coefficient form; assumed; erratum: 1 + z^{2m})"]
structure JacobiSixSquares : Prop where
  /-- The coefficient identity for all $N\ge1$. -/
  coeff : ∀ N : ℕ, 1 ≤ N →
    (Siegel.repNum (Siegel.sumSq 6) N : ℤ) =
      16 * ∑ d ∈ N.divisors, ZMod.χ₄ ((N / d : ℕ) : ZMod 4) * (d : ℤ) ^ 2 -
        4 * ∑ d ∈ N.divisors, ZMod.χ₄ (d : ZMod 4) * (d : ℤ) ^ 2

/-- **Jacobi's identity (1.5), coefficient form, assumed** (Cassels, App. B, §1, p. 369). Field `coeff`: for every
$N\ge1$, the number $r_8(N)$ of $\vec x\in\mathbb Z^8$ with $x_0^2+\dots+x_7^2=N$ equals
$16\sum_{d\mid N}(-1)^{N+d}d^3$, the coefficient of $z^N$ in $16\sum_{m\ge1}m^3z^m/(1-(-1)^mz^m)$ (expanding,
the term $z^{mj}$ has sign $((-1)^m)^{j-1}=(-1)^{N-m}$ for $N=mj$).

A full proof needs the space $M_4(\Gamma_0(4))$ of modular forms of weight $4$ and level $4$ (the theta series of $I_8$
lies in it), its Eisenstein basis, and the comparison of the first coefficients. -/
@[kb "cassels1978" "App. B, §1, (1.5), p. 369 (coefficient form; assumed)"]
structure JacobiEightSquares : Prop where
  /-- The coefficient identity for all $N\ge1$. -/
  coeff : ∀ N : ℕ, 1 ≤ N →
    (Siegel.repNum (Siegel.sumSq 8) N : ℤ) = 16 * ∑ d ∈ N.divisors, (-1 : ℤ) ^ (N + d) * (d : ℤ) ^ 3

/-- **Ramanujan's formula (1.6)-(1.9) for twenty-four squares, coefficient form, assumed** (Cassels, App. B, §1, p. 369).
Field `coeff`: for every $N\ge1$, with $r_{24}(N)$ the number of $\vec x\in\mathbb Z^{24}$ with $x_0^2+\dots+x_{23}^2=N$
and $\tau$ Ramanujan's function (`Lattices.ramanujanTau`, the $q$-expansion coefficients of the discriminant form, equal to
the coefficients of $G(z)=z\prod_{m\ge1}(1-z^m)^{24}$),
$$691\,r_{24}(N) = 16\sum_{d\mid N}(-1)^{N+d}d^{11} - 33152\,(-1)^N\tau(N) - 65536\,[2\mid N]\,\tau(N/2),$$
the coefficient of $z^N$ in $E(z)+C(z)$, $C(z)=-33152\,G(-z)-65536\,G(z^2)$. The identity is stated in $\mathbb C$ (where
$\tau$ takes values). Checked by brute force for $1\le N\le 30$.

A full proof needs the space of modular forms of weight $12$ for $\Gamma_0(4)$: the theta series of $I_{24}$ lies in it, one
needs its decomposition into Eisenstein series and cusp forms (including the cusp forms $G(-z)$, $G(z^2)$), and the
comparison of enough initial coefficients (a Sturm-type bound at level $4$). -/
@[kb "cassels1978" "App. B, §1, (1.6)–(1.9), p. 369 (coefficient form; assumed)"]
structure RamanujanTwentyFourSquares : Prop where
  /-- The coefficient identity for all $N\ge1$. -/
  coeff : ∀ N : ℕ, 1 ≤ N →
    (691 : ℂ) * (Siegel.repNum (Siegel.sumSq 24) N : ℂ) =
      16 * ∑ d ∈ N.divisors, (-1 : ℂ) ^ (N + d) * (d : ℂ) ^ 11 - 33152 * (-1 : ℂ) ^ N * Lattices.ramanujanTau N -
        65536 * (if 2 ∣ N then Lattices.ramanujanTau (N / 2) else 0)

end QuadFormsKB.Cassels

