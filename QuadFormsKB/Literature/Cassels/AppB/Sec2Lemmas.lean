/-
# Cassels, Appendix B, §2: Lemma 2.1, its Corollary, the Corollary to Lemma 2.2, and Lemma 2.3

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), §2 (*Binary forms*),
pp. 370–374. Throughout $D$ is a fundamental discriminant ($D \ne 1$: `Binary.IsQuadDisc D`), $\chi_D = (D/\cdot)$ the
Kronecker symbol (`Binary.kroneckerChar D`; `Binary.kronZ D` is its integer value), $h(D)$ the number of proper classes of
primitive forms of discriminant $D$ (positive definite if $D < 0$). Forms are integral binary forms
$f = ax^2 + bxy + cy^2$ (`BinQF`), $f(x, y)$ = `f.eval x y`, $\mathrm{disc} f = b^2 - 4ac$; vectors are $(x, y) = (v_0, v_1)$
(0-based `Fin 2`). The orbit of a representation is taken under the group `Binary.AutSL f` of proper automorphs
(determinant $1$).

**What is formalized.**

* *Lemma 2.1* (pp. 371-372) $\lim M^{-1}A^*(M)$, with $A^*(M) = \sum_{0<m\le M,\,(m,D)=1}a^*(m)$ and $a^*(m)$ the number of
  orbits of the proper automorphs `Binary.AutSL f` on the representations of $m$ by $f$. Statements `Lemma21Neg` ($D < 0$)
  and `Lemma21Pos` ($D > 0$). **$D < 0$ is proved** (`lemma_2_1_neg`): lattice points in an ellipse with the congruence
  condition (2.12), via Mathlib's lattice-point count `ZLattice.covolume.tendsto_card_le_div`, a squeeze for the shifted
  cosets, the Chinese remainder theorem for the density $\prod_{p\mid D}(1-p^{-1})$, and orbit counting for the free
  action of the finite group of proper automorphs. **$D > 0$ is a named statement** (`Lemma21Pos`, hyperbolic sector),
  not proved; the docstring says what a proof needs.
* *Corollary to Lemma 2.1* (p. 372, (2.12 bis)): the weighted average $\lim_{s\to1+}(s-1)\sum a^*(m)m^{-s}$. **Proved**
  from the limit of Lemma 2.1 (`cor_lemma_2_1`: partial summation, Mathlib's
  `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg`); `cor_lemma_2_1_neg` is unconditional,
  `cor_lemma_2_1_pos` is conditional on the named statement `Lemma21Pos`.
* *Corollary to Lemma 2.2* (pp. 372–373, (2.13)): $\sum^*_f\sum_{m>0,(m,D)=1}a_f(m)m^{-s} = \prod_{(D/p)=+1}
  (1+p^{-s})/(1-p^{-s})$ (right-hand side reconstructed from the proof). **Proved** (`cor_lemma_2_2`) from the named
  statement `PrimRepOrbitCount` of Lemma 2.2 (the count $2^\mu$ of orbits of primitive representations, and finiteness
  of $h(D)$) and the Euler product `euler_product_two_pow_omega`.
* *Lemma 2.3* (p. 374): $\sum_m (D/m)m^{-1}$, the series being read as the limit of its partial sums. **Proved**
  (`lemma_2_3_pos`, `lemma_2_3_neg`) from the Gauss sum (2.20), which Cassels "assumes as known": the named structure
  `KroneckerGaussSum D`. The proof follows the book (interchange of sums, boundary series (2.21) by Dirichlet's test and
  Abel's limit theorem).

**Reconstructed / garbled in the machine-read text.** The right-hand sides of (2.12 bis), (2.13) and (2.19) are partly
lost; they are reconstructed from the proofs and checked numerically. The sign in (2.19), $D < 0$, and in Theorem 2.1(i)
(a minus sign) and the meaning of "fundamental unit" $\eta$ in Lemma 2.1 (the smallest unit $>1$ of norm $+1$) are
recorded in the docstrings as errata/updates to be checked against the page images.
-/
import QuadFormsKB.Binary.ClassNumberFormula
import QuadFormsKB.Binary.FormAut
import QuadFormsKB.Literature.Cassels.AppBSec2
import QuadFormsKB.Literature.Cassels.Ch14.Group

open Filter Topology Matrix
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

open QuadFormsKB.Binary

/-! ### Lemma 2.3: the value of $\sum_m (D/m)\,m^{-1}$ -/

section Lemma23

open Finset Complex

/-- Helper: **the boundary series of $-\log(1 - z)$** (the complex form of Cassels' (2.21), p. 374). For
$z \in \mathbb C$ with $|z| = 1$ and $z \ne 1$, the partial sums $\sum_{0 \le m < K} z^m/m$ (the term $m = 0$ read as
$0$) tend to $-\operatorname{Log}(1 - z)$ (principal branch) as $K \to \infty$. Proof: Dirichlet's test gives
convergence (the partial sums of $z^m$ are bounded by $2/|1 - z|$); Abel's limit theorem identifies the limit with
$\lim_{x \to 1^-}\big(-\operatorname{Log}(1 - xz)\big)$. -/
theorem lemma23_partial_sums {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun K : ℕ => ∑ m ∈ Finset.range K, z ^ m / (m : ℂ)) atTop (𝓝 (-Complex.log (1 - z))) := by
  -- partial sums of z^m, m ≥ 1, are bounded
  have hb : ∀ n, ‖∑ i ∈ Finset.range n, z ^ (i + 1)‖ ≤ 2 / ‖1 - z‖ := by
    intro n
    have h1 : (1 - z) * ∑ i ∈ Finset.range n, z ^ (i + 1) = z - z ^ (n + 1) := by
      calc (1 - z) * ∑ i ∈ Finset.range n, z ^ (i + 1) = z * ((1 - z) * ∑ i ∈ Finset.range n, z ^ i) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => by ring)
        _ = z - z ^ (n + 1) := by rw [mul_neg_geom_sum]; ring
    have hne : ‖1 - z‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr (Ne.symm hz1)
    rw [le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)), mul_comm, ← norm_mul, h1]
    calc ‖z - z ^ (n + 1)‖ ≤ ‖z‖ + ‖z ^ (n + 1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have hanti : Antitone (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) := by
    intro a b hab
    simp only
    gcongr
  have hf0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcs := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded (z := fun i : ℕ => z ^ (i + 1)) hf0 hb
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  -- the partial sums of f n = z^n/n
  set f : ℕ → ℂ := fun n => z ^ n / (n : ℂ) with hf
  have hsum : ∀ K, ∑ m ∈ Finset.range (K + 1), f m = ∑ i ∈ Finset.range K, ((1 : ℝ) / ((i : ℝ) + 1)) • z ^ (i + 1) := by
    intro K
    rw [Finset.sum_range_succ']
    simp only [hf, Nat.cast_zero, div_zero, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.real_smul]
    push_cast
    ring
  have hLf : Tendsto (fun K : ℕ => ∑ m ∈ Finset.range K, f m) atTop (𝓝 L) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa [hsum] using hL
  -- Abel
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hLf
  rw [tendsto_map'_iff] at hab
  -- the other side: -log(1 - x z)
  have hlog : Tendsto (fun x : ℝ => -Complex.log (1 - (x : ℂ) * z)) (𝓝[<] 1) (𝓝 (-Complex.log (1 - z))) := by
    have hslit : (1 - z) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
        have := Complex.sq_norm z
        rw [hz, Complex.normSq_apply] at this
        nlinarith
      have hre : z.re ≠ 1 := by
        intro h
        apply hz1
        have : z.im = 0 := by nlinarith
        exact Complex.ext (by simpa using h) (by simpa using this)
      have : z.re ≤ 1 := by nlinarith [sq_nonneg z.im]
      simp only [Complex.sub_re, Complex.one_re]
      exact sub_pos.mpr (lt_of_le_of_ne this hre)
    have hc : ContinuousAt (fun x : ℝ => -Complex.log (1 - (x : ℂ) * z)) 1 := by
      refine ContinuousAt.neg (ContinuousAt.clog (by fun_prop) ?_)
      simpa using hslit
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have heq : ((fun w : ℂ => ∑' n, f n * w ^ n) ∘ Complex.ofReal) =ᶠ[𝓝[<] 1]
      fun x : ℝ => -Complex.log (1 - (x : ℂ) * z) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hxz : ‖(x : ℂ) * z‖ < 1 := by
      rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith [hx.1], hx.2⟩
    have := (hasSum_taylorSeries_neg_log hxz).tsum_eq
    simp only [Function.comp_apply]
    rw [← this]
    refine tsum_congr (fun n => ?_)
    simp only [hf]
    rw [mul_pow]; ring
  have := tendsto_nhds_unique (hab.congr' heq) hlog
  rw [this] at hLf
  exact hLf

/-- Helper: **(2.21) in closed form** (Cassels, p. 374). For $0 < t < 1$,
$$-\operatorname{Log}\big(1 - e^{2\pi i t}\big) = -\log\big(2\sin(\pi t)\big) + i\,\frac{\pi(1 - 2t)}{2}$$
(Cassels' $\theta = 2\pi t$: $\sum_m \cos(m\theta)/m = -\log(2\sin\tfrac\theta2)$ and
$\sum_m \sin(m\theta)/m = \tfrac12(\pi - \theta)$). -/
theorem lemma23_neg_log_one_sub_exp {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    -Complex.log (1 - Complex.exp (2 * π * Complex.I * t)) =
      ((-Real.log (2 * Real.sin (π * t)) : ℝ) : ℂ) + ((π * (1 - 2 * t) / 2 : ℝ) : ℂ) * Complex.I := by
  have hs : 0 < Real.sin (π * t) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have key : 1 - Complex.exp (2 * π * Complex.I * t) =
      ((2 * Real.sin (π * t) : ℝ) : ℂ) * Complex.exp (((π * t - π / 2 : ℝ) : ℂ) * Complex.I) := by
    have e1 : Complex.exp (2 * π * Complex.I * t) =
        Complex.exp (((π * t - π / 2 : ℝ) : ℂ) * Complex.I) * Complex.exp (((π * t + π / 2 : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1]
    simp only [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have h1 : Real.cos (π * t - π / 2) = Real.sin (π * t) := by
      rw [Real.cos_sub_pi_div_two]
    have h2 : Real.sin (π * t - π / 2) = - Real.cos (π * t) := by
      rw [Real.sin_sub_pi_div_two]
    have h3 : Real.cos (π * t + π / 2) = - Real.sin (π * t) := by
      rw [Real.cos_add_pi_div_two]
    have h4 : Real.sin (π * t + π / 2) = Real.cos (π * t) := by
      rw [Real.sin_add_pi_div_two]
    rw [h1, h2, h3, h4]
    simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
    have := Real.sin_sq_add_cos_sq (π * t)
    have h5 : ((Real.sin (π * t) : ℝ) : ℂ) ^ 2 + ((Real.cos (π * t) : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast this
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-1 : ℂ) * h5 + ((Real.cos (π * t) : ℝ) : ℂ) ^ 2 * hI
  rw [key]
  have hr : (0 : ℝ) < 2 * Real.sin (π * t) := by positivity
  have hmem : (π * t - π / 2) ∈ Set.Ioc (-π) π := by
    constructor <;> nlinarith [Real.pi_pos]
  have harg : Complex.arg (((2 * Real.sin (π * t) : ℝ) : ℂ) * Complex.exp (((π * t - π / 2 : ℝ) : ℂ) * Complex.I)) = π * t - π / 2 := by
    rw [Complex.arg_real_mul _ hr, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have := Complex.arg_cos_add_sin_mul_I hmem
    simpa using this
  have hn : ‖((2 * Real.sin (π * t) : ℝ) : ℂ) * Complex.exp (((π * t - π / 2 : ℝ) : ℂ) * Complex.I)‖ = 2 * Real.sin (π * t) := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  apply Complex.ext
  · simp only [Complex.neg_re, Complex.log_re, hn, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  · simp only [Complex.neg_im, Complex.log_im, harg, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
    ring

/-- Helper: for $g(0) = 0$, $\sum_{m=1}^{K} g(m) = \sum_{0 \le m < K+1} g(m)$. -/
theorem lemma23_sum_Icc_eq_range (g : ℕ → ℂ) (hg : g 0 = 0) (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, g m = ∑ m ∈ Finset.range (K + 1), g m := by
  induction K with
  | zero => simp [hg]
  | succ K ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (K + 1)]

/-- Helper: **the abstract core of Lemma 2.3.** Let $N > 0$, let $a : \mathbb N \to \mathbb C$ with $a(0) = 0$, and
let $c \ne 0$ satisfy the Gauss-sum relation $\sum_{0 \le r < N} a(r)\,e^{2\pi i rm/N} = c\,a(m)$ for every
$m \in \mathbb N$ (the shape of Cassels' (2.20)). Then the partial sums $\sum_{1 \le m \le K} a(m)/m$ converge to
$$c^{-1}\sum_{0 < r < N} a(r)\Big(-\log\big(2\sin\tfrac{\pi r}{N}\big) + i\,\tfrac{\pi}{2}\big(1 - \tfrac{2r}{N}\big)\Big).$$
Proof: interchange the sums over $m$ and $r$ and apply `lemma23_partial_sums` and `lemma23_neg_log_one_sub_exp` to
each $r$. -/
theorem lemma23_series_of_gauss (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) (c : ℂ) (hc : c ≠ 0) (ha0 : a 0 = 0)
    (hgauss : ∀ m : ℕ, ∑ r ∈ Finset.range N, a r * Complex.exp (2 * π * Complex.I * ((r * m : ℕ) : ℂ) / N) = a m * c) :
    Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, a m / (m : ℂ)) atTop
      (𝓝 (c⁻¹ * ∑ r ∈ Finset.Ioo 0 N, a r * (((-Real.log (2 * Real.sin (π * (r / N : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / N : ℝ)) / 2 : ℝ) : ℂ) * Complex.I))) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  -- c * S_K as a sum over r
  have hcS : ∀ K : ℕ, c * ∑ m ∈ Finset.Icc 1 K, a m / (m : ℂ) =
      ∑ r ∈ Finset.range N, a r * ∑ m ∈ Finset.range (K + 1),
        (Complex.exp (2 * π * Complex.I * (r / N : ℝ))) ^ m / (m : ℂ) := by
    intro K
    have hg0 : (fun m : ℕ => a m / (m : ℂ)) 0 = 0 := by simp
    rw [lemma23_sum_Icc_eq_range _ hg0, Finset.mul_sum]
    have : ∀ m ∈ Finset.range (K + 1), c * (a m / (m : ℂ)) =
        ∑ r ∈ Finset.range N, a r * ((Complex.exp (2 * π * Complex.I * (r / N : ℝ))) ^ m / (m : ℂ)) := by
      intro m _
      by_cases hm : m = 0
      · subst hm
        simp [ha0]
      · have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
        have h := hgauss m
        calc c * (a m / (m : ℂ)) = (a m * c) / (m : ℂ) := by ring
          _ = (∑ r ∈ Finset.range N, a r * Complex.exp (2 * π * Complex.I * ((r * m : ℕ) : ℂ) / N)) / (m : ℂ) := by rw [h]
          _ = _ := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun r _ => ?_)
            rw [mul_div_assoc, ← Complex.exp_nat_mul]
            congr 3
            push_cast
            field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.mul_sum]
  -- limits
  have hIoo : ∀ r ∈ Finset.Ioo 0 N, Tendsto (fun K : ℕ => a r * ∑ m ∈ Finset.range (K + 1),
        (Complex.exp (2 * π * Complex.I * (r / N : ℝ))) ^ m / (m : ℂ)) atTop
      (𝓝 (a r * (((-Real.log (2 * Real.sin (π * (r / N : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / N : ℝ)) / 2 : ℝ) : ℂ) * Complex.I))) := by
    intro r hr
    rw [Finset.mem_Ioo] at hr
    have hrN : (r : ℝ) / N < 1 := by
      rw [div_lt_one (by exact_mod_cast hN)]; exact_mod_cast hr.2
    have hr0 : (0 : ℝ) < (r : ℝ) / N := by
      apply div_pos <;> [exact_mod_cast hr.1; exact_mod_cast hN]
    set t : ℝ := (r : ℝ) / N with ht
    have hz : ‖Complex.exp (2 * π * Complex.I * t)‖ = 1 := by
      have : (2 * π * Complex.I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hz1 : Complex.exp (2 * π * Complex.I * t) ≠ 1 := by
      intro h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have h2 : (t : ℂ) = n := by
        have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero]
        apply mul_left_cancel₀ hpi
        rw [hn]; ring
      have h3 : t = n := by exact_mod_cast h2
      have h4 : (0 : ℝ) < n := by rw [← h3]; exact hr0
      have h5 : (n : ℝ) < 1 := by rw [← h3]; exact hrN
      have h6 : 0 < n := by exact_mod_cast h4
      have h7 : n < 1 := by exact_mod_cast h5
      omega
    have hA := lemma23_partial_sums hz hz1
    rw [← tendsto_add_atTop_iff_nat 1] at hA
    have := (hA.const_mul (a r))
    rw [lemma23_neg_log_one_sub_exp hr0 hrN] at this
    exact this
  have h0 : Tendsto (fun K : ℕ => a 0 * ∑ m ∈ Finset.range (K + 1),
        (Complex.exp (2 * π * Complex.I * ((0 : ℕ) / N : ℝ))) ^ m / (m : ℂ)) atTop (𝓝 0) := by
    simp [ha0]
  have hsum := tendsto_finsetSum (Finset.range N) (f := fun r K => a r * ∑ m ∈ Finset.range (K + 1),
        (Complex.exp (2 * π * Complex.I * (r / N : ℝ))) ^ m / (m : ℂ))
    (a := fun r => if r = 0 then 0 else a r * (((-Real.log (2 * Real.sin (π * (r / N : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / N : ℝ)) / 2 : ℝ) : ℂ) * Complex.I)) (by
      intro r hr
      by_cases hr0 : r = 0
      · subst hr0; simpa using h0
      · simp only [hr0, ite_false]
        exact hIoo r (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hr0, Finset.mem_range.mp hr⟩))
  have hS := hsum.const_mul c⁻¹
  have hfin : ∑ r ∈ Finset.range N, (if r = 0 then (0 : ℂ) else a r * (((-Real.log (2 * Real.sin (π * (r / N : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / N : ℝ)) / 2 : ℝ) : ℂ) * Complex.I)) = ∑ r ∈ Finset.Ioo 0 N, a r * (((-Real.log (2 * Real.sin (π * (r / N : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / N : ℝ)) / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
    simp only [ite_true, zero_add]
    have : Finset.Ioo 0 N = Finset.Ico 1 N := by ext x; simp; omega
    rw [this]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have : r ≠ 0 := by have := (Finset.mem_Ico.mp hr).1; omega
    simp [this]
  rw [hfin] at hS
  refine hS.congr (fun K => ?_)
  rw [← hcS K]
  field_simp


/-- **The constant on the right of Cassels' Gauss sum (2.20)** (p. 374): $\sqrt D$ for $D > 0$ and $i\sqrt{|D|}$ for
$D < 0$ (the case $D = 0$ of the printed text is a misprint for $D < 0$). -/
noncomputable def gaussConst (D : ℤ) : ℂ :=
  if 0 < D then ((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) else ((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) * Complex.I

variable (D : ℤ) [IsQuadDisc D]

/-- **The Gauss sum of a fundamental discriminant, Cassels' (2.20)** (p. 374), a cited result that Cassels "assumes as
known" (Appendix B, Example 5): for the Kronecker character $\chi_D = (D/\cdot)$ (`kroneckerChar D`) modulo
$N = |D|$ and every integer $m$,
$$\sum_{0 \le r < |D|} \chi_D(r)\, e^{2\pi i rm/|D|} = \chi_D(m)\cdot\begin{cases}\sqrt D & D > 0,\\ i\sqrt{|D|} &
D < 0.\end{cases}$$
**Proved** in `AppB/GaussSum.lean` (`kroneckerGaussSum_holds`), with unconditional forms of `lemma_2_3_pos`,
`lemma_2_3_neg` there. The proof needs (i) that $\chi_D$ is a primitive character of conductor $|D|$ (this
is where "$D$ fundamental" is used) and (ii) the sign of the quadratic Gauss sum (Gauss), which Mathlib does not
contain; (i) and Mathlib's `gaussSum_mulShift_of_isPrimitive` would reduce the statement to the case $m = 1$.
Used (as a hypothesis, never a conclusion) by `lemma_2_3_pos` and `lemma_2_3_neg`.

Field `gauss`: the displayed identity, for all $m \in \mathbb Z$ (with $\chi_D(r)$ and $\chi_D(m)$ read in
$\mathbb Z/|D|$). -/
@[kb "cassels1978" "App. B, §2, (2.20), p. 374 (the Gauss sum of a fundamental discriminant, assumed in the book)"]
structure KroneckerGaussSum : Prop where
  gauss : ∀ m : ℤ, ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * π * Complex.I * ((r : ℂ) * (m : ℂ)) / (D.natAbs : ℂ)) =
    kroneckerChar D (m : ZMod D.natAbs) * gaussConst D

variable {D}

/-- Helper: $|D| > 0$ for a fundamental discriminant. -/
theorem lemma23_natAbs_pos : 0 < D.natAbs := by have := three_le_natAbs (D := D); omega

/-- Helper: $\chi_D$ is real valued: $\overline{\chi_D(x)} = \chi_D(x)$. -/
theorem lemma23_kroneckerChar_conj (x : ZMod D.natAbs) : (starRingEnd ℂ) (kroneckerChar D x) = kroneckerChar D x := by
  rw [kroneckerChar_apply]; simp

/-- Helper: $\chi_D(0) = 0$ in $\mathbb Z/|D|$ ($|D| \ge 3$). -/
theorem lemma23_kroneckerChar_zero : kroneckerChar D (0 : ZMod D.natAbs) = 0 := by
  have : NeZero D.natAbs := ⟨lemma23_natAbs_pos.ne'⟩
  have : Nontrivial (ZMod D.natAbs) := ZMod.nontrivial_iff.mpr (by have := three_le_natAbs (D := D); omega)
  exact MulChar.map_zero _

/-- Helper: $\sum_{0 \le r < |D|}\chi_D(r) = 0$ ($\chi_D$ is a nontrivial character, `kroneckerChar_ne_one`). -/
theorem lemma23_sum_range_kroneckerChar : ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) = 0 := by
  have : NeZero D.natAbs := ⟨lemma23_natAbs_pos.ne'⟩
  have h := MulChar.sum_eq_zero_of_ne_one (kroneckerChar_ne_one (D := D))
  rw [← h]
  symm
  refine Finset.sum_nbij' (fun x => x.val) (fun r => (r : ZMod D.natAbs)) ?_ ?_ ?_ ?_ ?_
  · intro x _; simpa using ZMod.val_lt x
  · intro r _; simp
  · intro x _; simp
  · intro r hr; simpa using ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)
  · intro x _; simp

/-- Helper: the reflection $r \mapsto N - r$ permutes $\{1, \dots, N-1\}$. -/
theorem lemma23_sum_Ioo_reflect (N : ℕ) (g : ℕ → ℂ) :
    ∑ r ∈ Finset.Ioo 0 N, g (N - r) = ∑ r ∈ Finset.Ioo 0 N, g r := by
  refine Finset.sum_nbij' (fun r => N - r) (fun r => N - r) ?_ ?_ ?_ ?_ ?_
  · intro r hr; simp only [Finset.mem_Ioo] at hr ⊢; omega
  · intro r hr; simp only [Finset.mem_Ioo] at hr ⊢; omega
  · intro r hr; simp only [Finset.mem_Ioo] at hr ⊢; omega
  · intro r hr; simp only [Finset.mem_Ioo] at hr ⊢; omega
  · intro r hr; rfl

/-- Helper: $\chi_D(N - r) = \chi_D(-1)\chi_D(r)$ for $r \le N = |D|$. -/
theorem lemma23_kroneckerChar_reflect {r : ℕ} (hr : r ≤ D.natAbs) :
    kroneckerChar D ((D.natAbs - r : ℕ) : ZMod D.natAbs) = kroneckerChar D (-1) * kroneckerChar D (r : ZMod D.natAbs) := by
  rw [Nat.cast_sub hr, ZMod.natCast_self, zero_sub, ← map_mul, neg_one_mul]

/-- Helper: the constant `gaussConst D` of (2.20) is nonzero. -/
theorem lemma23_gaussConst_ne_zero : gaussConst D ≠ 0 := by
  have : (0 : ℝ) < |(D : ℝ)| := by
    have := three_le_natAbs (D := D)
    rw [abs_pos]; intro h; have : D = 0 := by exact_mod_cast h
    subst this; simp at *
  have hs : (Real.sqrt |(D : ℝ)|) ≠ 0 := (Real.sqrt_pos.mpr this).ne'
  unfold gaussConst
  split_ifs
  · exact_mod_cast hs
  · simp [hs]

/-- Helper: the Gauss sum relation (2.20) at $m = \pm1$ and reality of $\chi_D$ give
$\overline{c} = \chi_D(-1)\,c$ for $c$ = `gaussConst D`. -/
theorem lemma23_conj_gauss_sum (G : KroneckerGaussSum D) :
    (starRingEnd ℂ) (gaussConst D) = kroneckerChar D (-1) * gaussConst D := by
  have h1 := G.gauss 1
  have h2 := G.gauss (-1)
  simp only [Int.cast_one, Int.cast_neg, map_one, one_mul] at h1 h2
  rw [← h2, ← h1, map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_mul, lemma23_kroneckerChar_conj, ← Complex.exp_conj]
  congr 2
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast, map_ofNat, map_one]
  ring

/-- Helper: given (2.20), $\chi_D(-1) = +1$ for $D > 0$ (Cassels' "$(D\,/\,{-1}) = 1$ if $D > 0$", Ch. 14, Ex. 2). -/
theorem lemma23_kroneckerChar_neg_one_of_pos (G : KroneckerGaussSum D) (hD : 0 < D) : kroneckerChar D (-1) = 1 := by
  have h := lemma23_conj_gauss_sum G
  have hc : gaussConst D = ((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) := by simp [gaussConst, hD]
  rw [hc, Complex.conj_ofReal] at h
  have hne := lemma23_gaussConst_ne_zero (D := D)
  rw [hc] at hne
  exact (mul_right_cancel₀ hne (by rw [one_mul]; exact h.symm))

/-- Helper: given (2.20), $\chi_D(-1) = -1$ for $D < 0$ (Cassels' "$(D\,/\,{-1}) = -1$ if $D < 0$", Ch. 14, Ex. 2). -/
theorem lemma23_kroneckerChar_neg_one_of_neg (G : KroneckerGaussSum D) (hD : D < 0) : kroneckerChar D (-1) = -1 := by
  have h := lemma23_conj_gauss_sum G
  have hc : gaussConst D = ((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) * Complex.I := by simp [gaussConst, not_lt.mpr hD.le]
  rw [hc, map_mul, Complex.conj_ofReal, Complex.conj_I] at h
  have hne := lemma23_gaussConst_ne_zero (D := D)
  rw [hc] at hne
  refine mul_right_cancel₀ hne ?_
  rw [← h]; ring

/-- Helper: given (2.20), the partial sums $\sum_{m \le K}\chi_D(m)/m$ converge in $\mathbb C$ to
$c^{-1}\sum_{0<r<|D|}\chi_D(r)\big(-\log(2\sin\tfrac{\pi r}{|D|}) + i\tfrac\pi2(1 - \tfrac{2r}{|D|})\big)$,
$c$ = `gaussConst D` (`lemma23_series_of_gauss`). -/
theorem lemma23_limit_complex (G : KroneckerGaussSum D) :
    Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, kroneckerChar D (m : ZMod D.natAbs) / (m : ℂ)) atTop
      (𝓝 ((gaussConst D)⁻¹ * ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        (((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) * Complex.I))) := by
  refine lemma23_series_of_gauss D.natAbs lemma23_natAbs_pos (fun r => kroneckerChar D (r : ZMod D.natAbs))
    (gaussConst D) (lemma23_gaussConst_ne_zero (D := D)) (by simpa using lemma23_kroneckerChar_zero (D := D)) ?_
  intro m
  have := G.gauss (m : ℤ)
  simp only [Int.cast_natCast] at this
  rw [← this]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  push_cast
  rfl

/-- Helper: $\sum_{0<r<|D|}\chi_D(r) = 0$. -/
theorem lemma23_sum_Ioo_kroneckerChar : ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) = 0 := by
  have h := lemma23_sum_range_kroneckerChar (D := D)
  have hr : Finset.range D.natAbs = insert 0 (Finset.Ioo 0 D.natAbs) := by
    ext x; simp; have := lemma23_natAbs_pos (D := D); omega
  rw [hr, Finset.sum_insert (by simp)] at h
  simpa [lemma23_kroneckerChar_zero] using h

/-- Helper: if $\chi_D(-1) = \varepsilon$ then $\sum_{0<r<N}\chi_D(r)\tfrac\pi2(1 - 2r/N) = -\varepsilon$ times itself
(the weight $\tfrac\pi2(1 - 2r/N)$ is odd under $r \mapsto N - r$). -/
theorem lemma23_sum_u_reflect (ε : ℂ) (hε : kroneckerChar D (-1) = ε) :
    ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) =
      -ε * ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) := by
  set N := D.natAbs with hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast lemma23_natAbs_pos.ne'
  set g : ℕ → ℂ := fun r => kroneckerChar D (r : ZMod N) * ((π * (1 - 2 * (r / N : ℝ)) / 2 : ℝ) : ℂ) with hg
  conv_lhs => rw [← lemma23_sum_Ioo_reflect N g]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrN : r ≤ N := (Finset.mem_Ioo.mp hr).2.le
  simp only [hg]
  rw [lemma23_kroneckerChar_reflect hrN, hε, Nat.cast_sub hrN]
  have : (π * (1 - 2 * (((N : ℝ) - r) / N)) / 2 : ℝ) = -(π * (1 - 2 * (r / N : ℝ)) / 2) := by
    field_simp; ring
  rw [this]; push_cast; ring

/-- Helper: if $\chi_D(-1) = \varepsilon$ then $\sum_{0<r<N}\chi_D(r)\big(-\log(2\sin\tfrac{\pi r}{N})\big)$ equals
$\varepsilon$ times itself (the weight is even under $r \mapsto N - r$). -/
theorem lemma23_sum_l_reflect (ε : ℂ) (hε : kroneckerChar D (-1) = ε) :
    ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) =
      ε * ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) := by
  set N := D.natAbs with hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast lemma23_natAbs_pos.ne'
  set g : ℕ → ℂ := fun r => kroneckerChar D (r : ZMod N) * ((-Real.log (2 * Real.sin (π * (r / N : ℝ))) : ℝ) : ℂ) with hg
  conv_lhs => rw [← lemma23_sum_Ioo_reflect N g]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrN : r ≤ N := (Finset.mem_Ioo.mp hr).2.le
  simp only [hg]
  rw [lemma23_kroneckerChar_reflect hrN, hε, Nat.cast_sub hrN]
  have : Real.sin (π * (((N : ℝ) - r) / N)) = Real.sin (π * (r / N : ℝ)) := by
    rw [← Real.sin_pi_sub]; congr 1; field_simp; ring
  rw [this]; ring

/-- Helper: a real sequence whose complex image tends to the image of a real number tends to that number. -/
theorem lemma23_tendsto_real_of_complex {f : ℕ → ℝ} {v : ℝ}
    (h : Tendsto (fun K => (f K : ℂ)) atTop (𝓝 (v : ℂ))) : Tendsto f atTop (𝓝 v) := by
  have := (Complex.continuous_re.tendsto _).comp h
  simpa [Function.comp_def] using this

/-- Helper: the real partial sums $\sum_{m \le K}\mathrm{kronZ}(m)/m$ equal the complex ones $\sum \chi_D(m)/m$. -/
theorem lemma23_series_cast (K : ℕ) :
    (((∑ m ∈ Finset.Icc 1 K, (kronZ D (m : ZMod D.natAbs) : ℝ) / (m : ℝ) : ℝ)) : ℂ) =
      ∑ m ∈ Finset.Icc 1 K, kroneckerChar D (m : ZMod D.natAbs) / (m : ℂ) := by
  push_cast
  simp [kroneckerChar_apply]

/-- **Cassels, Appendix B, §2, Lemma 2.3, $D > 0$ (p. 374).** For a fundamental discriminant $D > 0$, the series
$\sum_{m \ge 1}(D/m)\,m^{-1}$ converges (as the limit of its partial sums) and
$$\sum_{m \ge 1}\frac{(D/m)}{m} = -\frac{1}{\sqrt D}\sum_{0 < r < D}(D/r)\,\log\sin\frac{\pi r}{D},$$
where $(D/m)$ is the Kronecker symbol, here the integer `kronZ D m` $= \chi_D(m)$ (`kroneckerChar`). Arguments: `D`
the fundamental discriminant (`IsQuadDisc D`), `G` the Gauss sum (2.20) (`KroneckerGaussSum D`, the one assumption,
as in the book), `hD : 0 < D`. The limit is over $K \to \infty$ of $\sum_{1 \le m \le K}$.

Proof as in the book: multiply by the Gauss sum (2.20), interchange the sums and sum (2.21) over $r$. Together with
$L(1, \chi_D) = 2h\log\eta_D/\sqrt D$ (`classNumberFormula_pos`) this gives Theorem 2.1(ii). -/
@[kb "cassels1978" "App. B, §2, Lemma 2.3 (D > 0), p. 374 (conditional on the Gauss sum (2.20))"]
theorem lemma_2_3_pos (G : KroneckerGaussSum D) (hD : 0 < D) :
    Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, (kronZ D (m : ZMod D.natAbs) : ℝ) / (m : ℝ)) atTop
      (𝓝 (-(Real.sqrt (D : ℝ))⁻¹ * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * Real.log (Real.sin (π * r / D)))) := by
  apply lemma23_tendsto_real_of_complex
  have h := lemma23_limit_complex G
  have hε := lemma23_kroneckerChar_neg_one_of_pos G hD
  have hc : gaussConst D = ((Real.sqrt (D : ℝ) : ℝ) : ℂ) := by
    simp [gaussConst, hD, abs_of_pos (by exact_mod_cast hD : (0 : ℝ) < D)]
  have hu := lemma23_sum_u_reflect 1 hε
  have hl := lemma23_sum_Ioo_kroneckerChar (D := D)
  have hNR : (D.natAbs : ℝ) = (D : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]; exact abs_of_pos (by exact_mod_cast hD)
  have hsin : ∀ r ∈ Finset.Ioo 0 D.natAbs, 0 < Real.sin (π * (r / D.natAbs : ℝ)) := by
    intro r hr
    rw [Finset.mem_Ioo] at hr
    have hN : (0 : ℝ) < D.natAbs := by exact_mod_cast lemma23_natAbs_pos
    have h1 : (0 : ℝ) < r := by exact_mod_cast hr.1
    have h2 : (r : ℝ) < D.natAbs := by exact_mod_cast hr.2
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    have : (r : ℝ) / D.natAbs < 1 := (div_lt_one hN).mpr h2
    nlinarith [Real.pi_pos]
  have hT : ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) =
      (((-∑ r ∈ Finset.Ioo 0 D.natAbs, (kronZ D (r : ZMod D.natAbs) : ℝ) *
        Real.log (Real.sin (π * (r / D.natAbs : ℝ)))) : ℝ) : ℂ) := by
    have hterm : ∀ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) =
        (-(Real.log 2 : ℂ)) * kroneckerChar D (r : ZMod D.natAbs) -
          (((kronZ D (r : ZMod D.natAbs) : ℝ) * Real.log (Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) := by
      intro r hr
      rw [Real.log_mul (by norm_num) (hsin r hr).ne']
      rw [kroneckerChar_apply]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hl]
    push_cast
    ring
  have hval : (gaussConst D)⁻¹ * ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        (((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) * Complex.I) =
      (((-(Real.sqrt (D : ℝ))⁻¹ * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * Real.log (Real.sin (π * r / D))) : ℝ) : ℂ) := by
    have hsplit : ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        (((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) * Complex.I) =
        (∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ)) +
        (∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ)) * Complex.I := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun r _ => by ring)
    have hu0 : ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) = 0 := by
      have : (2 : ℂ) * ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) = 0 := by
        linear_combination hu
      simpa using this
    rw [hsplit, hu0, hT, hc, zero_mul, add_zero]
    have hNR : (D.natAbs : ℝ) = (D : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact abs_of_pos (by exact_mod_cast hD)
    rw [hNR]
    simp only [mul_div_assoc]
    push_cast
    ring
  rw [show (fun K : ℕ => (((∑ m ∈ Finset.Icc 1 K, (kronZ D (m : ZMod D.natAbs) : ℝ) / (m : ℝ) : ℝ)) : ℂ)) =
      fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, kroneckerChar D (m : ZMod D.natAbs) / (m : ℂ) from funext lemma23_series_cast, ← hval]
  exact h

/-- **Cassels, Appendix B, §2, Lemma 2.3, $D < 0$ (p. 374).** For a fundamental discriminant $D < 0$, the series
$\sum_{m \ge 1}(D/m)\,m^{-1}$ converges (as the limit of its partial sums) and
$$\sum_{m \ge 1}\frac{(D/m)}{m} = -\frac{\pi}{|D|^{3/2}}\sum_{0 < r < |D|}(D/r)\,r.$$
Arguments as in `lemma_2_3_pos` (`G` is the Gauss sum (2.20), `hD : D < 0`).

*Erratum (to be checked against the page image):* the machine-read text of the printed formula (2.19), $D < 0$, shows
no minus sign in front of $\pi|D|^{-3/2}$; the correct value has one. Check: $D = -4$, $(D/1) = 1$, $(D/3) = -1$,
$\sum_m (D/m)/m = \pi/4$ (Leibniz) while $\sum_{0<r<4}(D/r)r = -2$, so the value is $-\frac{\pi}{8}\cdot(-2)$. The
same sign is needed in Theorem 2.1(i) ($2|D|h(D) = -w\sum_{0<r<|D|}(D/r)r$; for $D = -4$: $8 = -4\cdot(-2)$). -/
@[kb "cassels1978" "App. B, §2, Lemma 2.3 (D < 0), p. 374 (conditional on the Gauss sum (2.20))"]
theorem lemma_2_3_neg (G : KroneckerGaussSum D) (hD : D < 0) :
    Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, (kronZ D (m : ZMod D.natAbs) : ℝ) / (m : ℝ)) atTop
      (𝓝 (-π / |(D : ℝ)| ^ (3 / 2 : ℝ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * r)) := by
  apply lemma23_tendsto_real_of_complex
  have h := lemma23_limit_complex G
  have hε := lemma23_kroneckerChar_neg_one_of_neg G hD
  have hc : gaussConst D = ((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) * Complex.I := by
    simp [gaussConst, not_lt.mpr hD.le]
  have hl := lemma23_sum_l_reflect (D := D) (-1) hε
  have hs := lemma23_sum_Ioo_kroneckerChar (D := D)
  have hNR : (D.natAbs : ℝ) = |(D : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNpos : (0 : ℝ) < |(D : ℝ)| := by
    rw [← hNR]; exact_mod_cast lemma23_natAbs_pos
  have hsq : (0 : ℝ) < Real.sqrt |(D : ℝ)| := Real.sqrt_pos.mpr hNpos
  have hval : (gaussConst D)⁻¹ * ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        (((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) * Complex.I) =
      ((-π / |(D : ℝ)| ^ (3 / 2 : ℝ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * r : ℝ) : ℂ) := by
    have hsplit : ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        (((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) +
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) * Complex.I) =
        (∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ)) +
        (∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ)) * Complex.I := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun r _ => by ring)
    have hl0 : ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) = 0 := by
      have : (2 : ℂ) * ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((-Real.log (2 * Real.sin (π * (r / D.natAbs : ℝ))) : ℝ) : ℂ) = 0 := by
        linear_combination hl
      simpa using this
    have hTu : ∑ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) =
        ((-(π / |(D : ℝ)|) * ∑ r ∈ Finset.Ioo 0 D.natAbs, (kronZ D (r : ZMod D.natAbs) : ℝ) * r : ℝ) : ℂ) := by
      have hterm : ∀ r ∈ Finset.Ioo 0 D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
          ((π * (1 - 2 * (r / D.natAbs : ℝ)) / 2 : ℝ) : ℂ) =
          ((π / 2 : ℝ) : ℂ) * kroneckerChar D (r : ZMod D.natAbs) -
            ((π / |(D : ℝ)| * ((kronZ D (r : ZMod D.natAbs) : ℝ) * r) : ℝ) : ℂ) := by
        intro r _
        rw [kroneckerChar_apply, ← hNR]
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, ← Complex.ofReal_sum,
        ← Finset.mul_sum]
      push_cast
      ring
    rw [hsplit, hl0, hTu, hc, zero_add]
    have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
    have hsq' : ((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
    have h32 : |(D : ℝ)| ^ (3 / 2 : ℝ) = |(D : ℝ)| * Real.sqrt |(D : ℝ)| := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hNpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [h32]
    have hN' : ((|(D : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    push_cast
    field_simp
  rw [show (fun K : ℕ => (((∑ m ∈ Finset.Icc 1 K, (kronZ D (m : ZMod D.natAbs) : ℝ) / (m : ℝ) : ℝ)) : ℂ)) =
      fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, kroneckerChar D (m : ZMod D.natAbs) / (m : ℂ) from funext lemma23_series_cast, ← hval]
  exact h


end Lemma23

/-! ### Orbits of representations, the groups of proper automorphs, and the forms of discriminant $D$ -/

/-- **The orbit relation of the proper automorphs of $f$ on $\mathbb Z^2$.** Two vectors $v, w \in \mathbb Z^2$ are
related iff $w = \gamma v$ for some $\gamma$ in `AutSL f`, the group of proper automorphs of $f$ (matrices of
determinant $1$ with $f \circ \gamma = f$; for $D < 0$ it is the finite group of order $w$ of `Binary.card_autSL`, for
$D > 0$ it is infinite). Argument `f`: the integral binary form $f = ax^2 + bxy + cy^2$ (`BinQF`). -/
def autOrbitSetoid (f : BinQF) : Setoid (Fin 2 → ℤ) where
  r v w := ∃ γ ∈ AutSL f, γ.val *ᵥ v = w
  iseqv := by
    refine ⟨fun v => ⟨1, one_mem _, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨γ, hγ, rfl⟩
      refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    · rintro u v w ⟨γ, hγ, rfl⟩ ⟨γ', hγ', rfl⟩
      refine ⟨γ' * γ, mul_mem hγ' hγ, ?_⟩
      rw [Units.val_mul, mulVec_mulVec]

/-- **The representations of $m$ by $f$:** the vectors $v = (x, y) \in \mathbb Z^2$ with $f(x, y) = m$ (primitive or
not). Arguments: `f` the integral binary form, `m` the represented integer. -/
def repVecs (f : BinQF) (m : ℕ) : Set (Fin 2 → ℤ) := {v | f.eval (v 0) (v 1) = m}

/-- **The primitive representations of $m$ by $f$:** the vectors $v = (x, y)$ with $f(x, y) = m$ and
$\gcd(x, y) = 1$ (`IsCoprime`). Arguments as for `repVecs`. -/
def primRepVecs (f : BinQF) (m : ℕ) : Set (Fin 2 → ℤ) := {v | f.eval (v 0) (v 1) = m ∧ IsCoprime (v 0) (v 1)}

/-- **$a^*_f(m)$, Cassels' number of orbits of representations of $m$ by $f$** (Appendix B, §2, p. 371, before (2.9)):
the number of orbits of the proper automorphs `AutSL f` on the set `repVecs f m` of all representations of $m$ (primitive
or not). Arguments: `f` the form, `m` the integer. (If the number of orbits were infinite this would be $0$; it is finite
for every nonzero $m$.) -/
noncomputable def repOrbitCount (f : BinQF) (m : ℕ) : ℕ :=
  Nat.card (Quotient ((autOrbitSetoid f).comap (Subtype.val : repVecs f m → Fin 2 → ℤ)))

/-- **$a_f(m)$, Cassels' number of orbits of primitive representations of $m$ by $f$** (Appendix B, §2, p. 372,
Corollary to Lemma 2.2): the number of orbits of `AutSL f` on `primRepVecs f m`. Arguments as for `repOrbitCount`. -/
noncomputable def primRepOrbitCount (f : BinQF) (m : ℕ) : ℕ :=
  Nat.card (Quotient ((autOrbitSetoid f).comap (Subtype.val : primRepVecs f m → Fin 2 → ℤ)))

/-- **$A^*(M)$ of (2.9), p. 371:** $A^*_f(M) = \sum_{0 < m \le M,\ (m, D) = 1} a^*_f(m)$, $D = $ `f.disc`
($(m, D)$ is the greatest common divisor, `Nat.Coprime m D.natAbs`). Arguments: `f` the form, `M` the bound. -/
noncomputable def orbitCountSum (f : BinQF) (M : ℕ) : ℕ :=
  ∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs), repOrbitCount f m

/-- **The number $w$ of proper automorphs of a definite binary form of fundamental discriminant $D < 0$** (Cassels
(2.7), p. 371): $6$ if $D = -3$, $4$ if $D = -4$, $2$ otherwise. (For a positive definite form of discriminant $D$ this is
the order of `AutSL f`, `Binary.card_autSL`; the printed text of (2.7) is garbled but the values $6, 4, 2$ are those of
the roots of unity of $\mathbb Q(\sqrt D)$.) -/
def properAutomorphCount (D : ℤ) : ℕ := if D = -3 then 6 else if D = -4 then 4 else 2

/-- **The Euler factor $\prod_{p \mid D}(1 - p^{-1})$** of (2.10) and (2.12 bis), $p$ over the distinct primes dividing
$D$ (`D.natAbs.primeFactors`). -/
noncomputable def coprimeDensity (D : ℤ) : ℝ := ∏ p ∈ D.natAbs.primeFactors, (1 - 1 / (p : ℝ))

/-- **The fundamental unit $\eta$ of Lemma 2.1 for $D > 0$**, read as the smallest unit $\eta > 1$ of norm $+1$ of
$\mathbb Z[(D + \sqrt D)/2]$ (the generator of the proper automorphs, $\mathrm{Aut}^+ = \{\pm\eta^k\}$): the least real
$\eta = (t + u\sqrt D)/2 > 1$ with integers $t, u \ge 1$ and $t^2 - Du^2 = 4$. Arguments: `D` the fundamental
discriminant, `η` the real number.

*Update:* with $\eta$ the fundamental unit in the usual sense (smallest unit $> 1$, of norm $\pm1$) the constant in (2.10)
is wrong by the factor $2$ when that unit has norm $-1$ (e.g. $D = 5$: $\eta = (1 + \sqrt5)/2$, but the count needs
$((3 + \sqrt5)/2)$); checked numerically for $D = 5$ ($A^*(M)/M \to 0.3443$, not $0.1722$, for $M = 3000$). -/
def IsNormOneFundamentalUnit (D : ℤ) (η : ℝ) : Prop :=
  1 < η ∧ (∃ t u : ℕ, 0 < u ∧ (t : ℤ) ^ 2 - D * (u : ℤ) ^ 2 = 4 ∧ η = (t + u * Real.sqrt D) / 2) ∧
    ∀ t u : ℕ, 0 < u → (t : ℤ) ^ 2 - D * (u : ℤ) ^ 2 = 4 → η ≤ (t + u * Real.sqrt D) / 2

/-- **Cassels, Appendix B, §2, Lemma 2.1, case $D < 0$ (pp. 371-372): the statement** (proved as `lemma_2_1_neg`): for a
fundamental discriminant $D < 0$ and every positive definite integral binary form $f$ of discriminant $D$,
$$\lim_{M \to \infty} M^{-1}A^*_f(M) = \frac{2\pi}{w\sqrt{|D|}}\prod_{p \mid D}\big(1 - p^{-1}\big),$$
$w$ = `properAutomorphCount D`. Argument: `D` the fundamental discriminant (`IsQuadDisc D`); the form `f` (with
`f.disc = D` and `f.PosDef`) is quantified inside. -/
def Lemma21Neg (D : ℤ) [IsQuadDisc D] : Prop :=
  ∀ f : BinQF, f.disc = D → f.PosDef →
    Tendsto (fun M : ℕ => (orbitCountSum f M : ℝ) / M) atTop
      (𝓝 (2 * π / (properAutomorphCount D * Real.sqrt |(D : ℝ)|) * coprimeDensity D))

/-- **Cassels, Appendix B, §2, Lemma 2.1, case $D > 0$ (pp. 371–372), as a named statement** (not proved in the
library): for a fundamental discriminant $D > 0$, every integral binary form $f$ of discriminant $D$ and the fundamental
unit $\eta$ of norm $+1$ (`IsNormOneFundamentalUnit D η`),
$$\lim_{M \to \infty} M^{-1}A^*_f(M) = \frac{\log\eta}{\sqrt D}\prod_{p \mid D}\big(1 - p^{-1}\big).$$
A full proof needs the book's argument "similar to $D < 0$" with the ellipse replaced by a region bounded by two rays
and a segment of the hyperbola $f = M$ (one representative of each orbit of `AutSL f = \{\pm\eta^k\}`, Cassels Ch. 13,
Lemma 3.3), whose area is $M\log\eta/\sqrt D$: Mathlib's `ZLattice.covolume.tendsto_card_le_div` applies to the cone
$X$ = sector with the homogeneous function $F = f$, but the structure of `AutSL f` for indefinite $f$ (generated by
$-1$ and one matrix of the unit $\eta$) and the congruence conditions are not in the library. Arguments: `D` the
fundamental discriminant (`IsQuadDisc D`). -/
@[kb "cassels1978" "App. B, §2, Lemma 2.1 (D > 0), (2.10), pp. 371–372 (named statement)"]
def Lemma21Pos (D : ℤ) [IsQuadDisc D] : Prop :=
  ∀ f : BinQF, f.disc = D → ∀ η : ℝ, IsNormOneFundamentalUnit D η →
    Tendsto (fun M : ℕ => (orbitCountSum f M : ℝ) / M) atTop
      (𝓝 (Real.log η / Real.sqrt D * coprimeDensity D))


/-! ### Lemma 2.1 for $D < 0$: lattice points in an ellipse with congruence conditions -/

namespace Lemma21Aux

section Lattice

open MeasureTheory Filter Topology



/-- Helper: **the real quadratic form** $q_{a,b,c}(x) = ax_0^2 + bx_0x_1 + cx_1^2$ on $\mathbb R^2$ with real
coefficients (Cassels' $f$ evaluated at real vectors; the area of the ellipse $f \le M$ is computed with it). -/
def qf2 (a b c : ℝ) (x : Fin 2 → ℝ) : ℝ := a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2

/-- Helper: **the upper triangular matrix $T$ with $|Tx|^2 = q_{a,b,c}(x)$:**
$T = \begin{pmatrix}\sqrt a & b/(2\sqrt a)\\ 0 & \sqrt{(4ac - b^2)/(4a)}\end{pmatrix}$ (completing the square), for
$a > 0$ and $4ac - b^2 > 0$. -/
noncomputable def qfMat (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt a, b / (2 * Real.sqrt a); 0, Real.sqrt ((4 * a * c - b ^ 2) / (4 * a))]

/-- Helper: $\sum_i |(Tx)_i|^2 = q_{a,b,c}(x)$ for $a > 0$, $4ac - b^2 > 0$ (arguments `ha`, `hN`; `x` the vector). -/
theorem qf2_eq_sum {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) (x : Fin 2 → ℝ) :
    ∑ i, |(qfMat a b c).mulVec x i| ^ (2 : ℝ) = qf2 a b c x := by
  have h1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h2 : 0 ≤ (4 * a * c - b ^ 2) / (4 * a) := by positivity
  simp only [qfMat, Fin.sum_univ_two, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Real.rpow_two, sq_abs]
  simp [qf2]
  have e1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have e2 : Real.sqrt ((4 * a * c - b ^ 2) / (4 * a)) ^ 2 = (4 * a * c - b ^ 2) / (4 * a) := Real.sq_sqrt h2
  rw [mul_pow (Real.sqrt _) (x 1), e2]
  have e3 : (Real.sqrt a * x 0 + b / (2 * Real.sqrt a) * x 1) ^ 2 =
      Real.sqrt a ^ 2 * x 0 ^ 2 + b * x 0 * x 1 + b ^ 2 / (4 * Real.sqrt a ^ 2) * x 1 ^ 2 := by
    field_simp
    ring
  rw [e3, e1]
  field_simp
  ring

/-- Helper: $\det T = \sqrt{4ac - b^2}/2$ for $a > 0$, $4ac - b^2 > 0$. -/
theorem det_qfMat {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) :
    (qfMat a b c).det = Real.sqrt (4 * a * c - b ^ 2) / 2 := by
  simp only [qfMat, Matrix.det_fin_two_of, mul_zero, sub_zero]
  have h1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [← Real.sqrt_mul ha.le]
  have : a * ((4 * a * c - b ^ 2) / (4 * a)) = (4 * a * c - b ^ 2) / 4 := by field_simp
  rw [this, Real.sqrt_div hN.le, show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]

open ZLattice

/-- Helper: **the lattice $\mathbb Z^2$** as a $\mathbb Z$-submodule of $\mathbb R^2$ (`Fin 2 → ℝ`), the span of the standard
basis. -/
noncomputable def Lz : Submodule ℤ (Fin 2 → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))

/-- Helper: `Lz` is discrete. -/
instance : DiscreteTopology Lz := by unfold Lz; infer_instance
/-- Helper: `Lz` is a $\mathbb Z$-lattice of full rank. -/
instance : IsZLattice ℝ Lz := by unfold Lz; infer_instance

/-- Helper: the covolume of $\mathbb Z^2$ is $1$. -/
theorem covolume_Lz : covolume Lz = 1 := by
  have hli : LinearIndependent ℤ (Pi.basisFun ℝ (Fin 2)) := by
    exact (Pi.basisFun ℝ (Fin 2)).linearIndependent.restrict_scalars' ℤ
  let b : Module.Basis (Fin 2) ℤ Lz := Module.Basis.span hli
  rw [ZLattice.covolume_eq_det _ b]
  have : (Matrix.of ((↑) ∘ b) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    ext i j
    have h := Module.Basis.coe_span_apply hli i
    simp only [Matrix.of_apply, Function.comp_apply]
    rw [show ((b i : Lz) : Fin 2 → ℝ) = Pi.basisFun ℝ (Fin 2) i from h]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]; simp

/-- Helper: a vector of $\mathbb R^2$ lies in `Lz` iff it is the image of an integer vector. Argument `x`: the real
vector. -/
theorem mem_Lz (x : Fin 2 → ℝ) : x ∈ Lz ↔ ∃ v : Fin 2 → ℤ, x = fun i => (v i : ℝ) := by
  unfold Lz
  rw [Module.Basis.mem_span_iff_repr_mem ℤ]
  simp only [Pi.basisFun_repr, Set.mem_range, eq_intCast]
  constructor
  · intro h
    choose v hv using h
    exact ⟨v, funext fun i => (hv i).symm⟩
  · rintro ⟨v, rfl⟩ i
    exact ⟨v i, rfl⟩


/-- Helper: **the area of the ellipse $q_{a,b,c} \le 1$** is $2\pi/\sqrt{4ac - b^2}$ ($a > 0$, $4ac - b^2 > 0$): the
preimage of the unit disc (Mathlib's `volume_sum_rpow_le` with $p = 2$) under the linear map $T$ of determinant
$\sqrt{4ac - b^2}/2$. -/
theorem ellipse_volume {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) :
    volume.real {x : Fin 2 → ℝ | qf2 a b c x ≤ 1} = 2 * Real.pi / Real.sqrt (4 * a * c - b ^ 2) := by
  have hdet := det_qfMat ha hN
  have hsq : 0 < Real.sqrt (4 * a * c - b ^ 2) := Real.sqrt_pos.mpr hN
  set T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' (qfMat a b c) with hT
  have hTdet : LinearMap.det T = Real.sqrt (4 * a * c - b ^ 2) / 2 := by
    rw [hT, LinearMap.det_toLin', hdet]
  have hset : {x : Fin 2 → ℝ | qf2 a b c x ≤ 1} =
      T ⁻¹' {y : Fin 2 → ℝ | (∑ i, |y i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hT, Matrix.toLin'_apply]
    rw [qf2_eq_sum ha hN x]
    have hnn : 0 ≤ qf2 a b c x := by
      rw [← qf2_eq_sum ha hN x]; positivity
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    constructor
    · intro h
      exact ⟨by norm_num, by simpa using h⟩
    · intro h
      simpa using h.2
  have hS : volume {y : Fin 2 → ℝ | (∑ i, |y i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ 1} = ENNReal.ofReal Real.pi := by
    rw [MeasureTheory.volume_sum_rpow_le (ι := Fin 2) (p := 2) (by norm_num) 1]
    have hG : Real.Gamma (1 / (2 : ℝ) + 1) = Real.sqrt Real.pi / 2 := by
      rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
    have hG2 : Real.Gamma ((Fintype.card (Fin 2) : ℝ) / 2 + 1) = 1 := by
      have h2 : ((Fintype.card (Fin 2) : ℝ) / 2 + 1) = 2 := by simp; norm_num
      rw [h2, Real.Gamma_two]
    rw [hG, hG2]
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul, div_one]
    congr 1
    have : (2 * (Real.sqrt Real.pi / 2)) ^ 2 = Real.pi := by
      rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.sq_sqrt Real.pi_pos.le]
    exact this
  have hdne : LinearMap.det T ≠ 0 := by rw [hTdet]; positivity
  unfold Measure.real
  rw [hset, MeasureTheory.Measure.addHaar_preimage_linearMap volume hdne, hS, hTdet]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [abs_of_pos (by positivity)]
  field_simp

/-- Helper: $q_{a,b,c} \ge 0$ ($a > 0$, $4ac - b^2 > 0$). -/
theorem qf2_nonneg {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) (x : Fin 2 → ℝ) : 0 ≤ qf2 a b c x := by
  rw [← qf2_eq_sum ha hN x]; positivity

/-- Helper: the ellipse $\{q_{a,b,c} \le 1\}$ is convex (so its frontier is null for Lebesgue measure). -/
theorem qf2_convex {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) :
    Convex ℝ {x : Fin 2 → ℝ | qf2 a b c x ≤ 1} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hid : qf2 a b c (s • x + t • y) = s * qf2 a b c x + t * qf2 a b c y - s * t * qf2 a b c (x - y) := by
    have ht' : t = 1 - s := by linarith
    subst ht'
    simp only [qf2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hid]
  have h0 := qf2_nonneg ha hN (x - y)
  nlinarith [mul_nonneg hs ht, mul_nonneg (mul_nonneg hs ht) h0, mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]

/-- Helper: the ellipse $\{q_{a,b,c} \le 1\}$ is bounded. -/
theorem qf2_bounded {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) :
    Bornology.IsBounded {x : Fin 2 → ℝ | qf2 a b c x ≤ 1} := by
  have hdet := det_qfMat ha hN
  have hsq : 0 < Real.sqrt (4 * a * c - b ^ 2) := Real.sqrt_pos.mpr hN
  have hu : IsUnit (qfMat a b c).det := by rw [hdet]; exact isUnit_iff_ne_zero.mpr (by positivity)
  let Λ : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' (qfMat a b c)⁻¹)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨‖Λ‖, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx
  rw [mem_closedBall_zero_iff]
  set y := (qfMat a b c).mulVec x with hy
  have hxy : x = Λ y := by
    simp only [Λ, hy, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hy1 : ‖y‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hs := qf2_eq_sum ha hN x
    rw [← hy] at hs
    simp only [Fin.sum_univ_two, Real.rpow_two, sq_abs] at hs
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    have hs1 : y 0 ^ 2 + y 1 ^ 2 ≤ 1 := by linarith
    fin_cases i
    · show y 0 ^ 2 ≤ 1
      nlinarith [sq_nonneg (y 1)]
    · show y 1 ^ 2 ≤ 1
      nlinarith [sq_nonneg (y 0)]
  calc ‖x‖ = ‖Λ y‖ := by rw [← hxy]
    _ ≤ ‖Λ‖ * ‖y‖ := Λ.le_opNorm y
    _ ≤ ‖Λ‖ * 1 := by gcongr
    _ = ‖Λ‖ := mul_one _

/-- Helper: **the Gauss circle problem for a positive definite binary form.** For $a > 0$ and $4ac - b^2 > 0$,
$$\frac{\#\{v \in \mathbb Z^2 : q_{a,b,c}(v) \le t\}}{t} \longrightarrow \frac{2\pi}{\sqrt{4ac - b^2}}
\quad (t \to \infty),$$
the area of the ellipse $q \le 1$ (Mathlib's `ZLattice.covolume.tendsto_card_le_div` for the lattice $\mathbb Z^2$ of
covolume $1$). -/
theorem ellipse_card_tendsto {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) :
    Tendsto (fun t : ℝ => (Nat.card {v : Fin 2 → ℤ // qf2 a b c (fun i => (v i : ℝ)) ≤ t} : ℝ) / t) atTop
      (𝓝 (2 * Real.pi / Real.sqrt (4 * a * c - b ^ 2))) := by
  have hcont : Continuous (qf2 a b c) := by
    unfold qf2; fun_prop
  have h := ZLattice.covolume.tendsto_card_le_div Lz (X := Set.univ) (F := qf2 a b c)
    (fun _ _ _ _ => Set.mem_univ _)
    (fun x r hr => by simp only [qf2, Pi.smul_apply, smul_eq_mul, Fintype.card_fin]; ring)
    (by simpa using qf2_bounded ha hN)
    (by simpa using (isClosed_le hcont continuous_const).measurableSet)
    (by simpa using Convex.addHaar_frontier (μ := volume) (qf2_convex ha hN))
  simp only [Set.mem_univ, true_and, covolume_Lz, div_one] at h
  have hv := ellipse_volume ha hN
  rw [hv] at h
  refine h.congr (fun t => ?_)
  congr 1
  rw [← Nat.card_congr (Equiv.ofBijective (fun v : {v : Fin 2 → ℤ // qf2 a b c (fun i => (v i : ℝ)) ≤ t} =>
      (⟨fun i => (v.1 i : ℝ), ⟨v.2, (mem_Lz _).mpr ⟨v.1, rfl⟩⟩⟩ :
        ↥({x : Fin 2 → ℝ | qf2 a b c x ≤ t} ∩ (Lz : Set (Fin 2 → ℝ))))) ⟨?_, ?_⟩)]
  · intro v w hvw
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val hvw) i
    simp only at this
    exact_mod_cast this
  · rintro ⟨x, hx1, hx2⟩
    obtain ⟨v, rfl⟩ := (mem_Lz x).mp hx2
    exact ⟨⟨v, hx1⟩, rfl⟩

end Lattice

section Shift

open MeasureTheory Filter Topology



/-- Helper: $q_{a,b,c}(z) = (Tz)_0^2 + (Tz)_1^2$ (arguments as for `qf2_eq_sum`). -/
theorem qf2_eq_sq {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) (z : Fin 2 → ℝ) :
    qf2 a b c z = ((qfMat a b c).mulVec z 0) ^ 2 + ((qfMat a b c).mulVec z 1) ^ 2 := by
  have := qf2_eq_sum ha hN z
  simpa [Fin.sum_univ_two, Real.rpow_two, sq_abs] using this.symm

/-- Helper: **the triangle inequality for $\sqrt q$:** $\sqrt{q(x + y)} \le \sqrt{q(x)} + \sqrt{q(y)}$ (Cauchy-Schwarz
in the coordinates $Tx$). -/
theorem qf2_sqrt_add_le {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) (x y : Fin 2 → ℝ) :
    Real.sqrt (qf2 a b c (x + y)) ≤ Real.sqrt (qf2 a b c x) + Real.sqrt (qf2 a b c y) := by
  rw [qf2_eq_sq ha hN (x + y), qf2_eq_sq ha hN x, qf2_eq_sq ha hN y, Matrix.mulVec_add]
  simp only [Pi.add_apply]
  generalize (qfMat a b c).mulVec x 0 = u0
  generalize (qfMat a b c).mulVec x 1 = u1
  generalize (qfMat a b c).mulVec y 0 = v0
  generalize (qfMat a b c).mulVec y 1 = v1
  have hA : 0 ≤ u0 ^ 2 + u1 ^ 2 := by positivity
  have hB : 0 ≤ v0 ^ 2 + v1 ^ 2 := by positivity
  have hcs : (u0 * v0 + u1 * v1) ≤ Real.sqrt (u0 ^ 2 + u1 ^ 2) * Real.sqrt (v0 ^ 2 + v1 ^ 2) := by
    rw [← Real.sqrt_mul hA]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    nlinarith [sq_nonneg (u0 * v1 - u1 * v0)]
  rw [Real.sqrt_le_left (by positivity)]
  have e1 := Real.sq_sqrt hA
  have e2 := Real.sq_sqrt hB
  nlinarith [hcs]

/-- Helper: there is a constant $K \ge 0$ with $\|x\| \le K\sqrt{q(x)}$ for all $x \in \mathbb R^2$ (sup norm; $T^{-1}$ is
bounded). -/
theorem qf2_norm_le {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Fin 2 → ℝ, ‖x‖ ≤ K * Real.sqrt (qf2 a b c x) := by
  have hdet := det_qfMat ha hN
  have hsq : 0 < Real.sqrt (4 * a * c - b ^ 2) := Real.sqrt_pos.mpr hN
  have hu : IsUnit (qfMat a b c).det := by rw [hdet]; exact isUnit_iff_ne_zero.mpr (by positivity)
  let Λ : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' (qfMat a b c)⁻¹)
  refine ⟨‖Λ‖, norm_nonneg _, fun x => ?_⟩
  set y := (qfMat a b c).mulVec x with hy
  have hxy : x = Λ y := by
    simp only [Λ, hy, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hQ := qf2_eq_sq ha hN x
  rw [← hy] at hQ
  have hy1 : ‖y‖ ≤ Real.sqrt (qf2 a b c x) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    fin_cases i
    · show y 0 ^ 2 ≤ _
      nlinarith [sq_nonneg (y 1)]
    · show y 1 ^ 2 ≤ _
      nlinarith [sq_nonneg (y 0)]
  calc ‖x‖ = ‖Λ y‖ := by rw [← hxy]
    _ ≤ ‖Λ‖ * ‖y‖ := Λ.le_opNorm y
    _ ≤ ‖Λ‖ * Real.sqrt (qf2 a b c x) := by gcongr

/-- Helper: for every real $\tau$ only finitely many $w \in \mathbb Z^2$ have $q_{a,b,c}(w) \le \tau$. -/
theorem finite_ellipse_int {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) (τ : ℝ) :
    Set.Finite {w : Fin 2 → ℤ | qf2 a b c (fun i => (w i : ℝ)) ≤ τ} := by
  obtain ⟨K, hK0, hK⟩ := qf2_norm_le ha hN
  set m : ℤ := ⌈K * Real.sqrt τ⌉ with hm
  refine (Set.Finite.pi (t := fun _ : Fin 2 => Set.Icc (-m) m) (fun _ => Set.finite_Icc _ _)).subset ?_
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have h1 : ‖(fun i => (w i : ℝ))‖ ≤ K * Real.sqrt τ :=
    (hK _).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hw) hK0)
  have h2 : |(w i : ℝ)| ≤ K * Real.sqrt τ := by
    refine le_trans ?_ h1
    have := norm_le_pi_norm (fun i => (w i : ℝ)) i
    simpa [Real.norm_eq_abs] using this
  have h3 : K * Real.sqrt τ ≤ m := Int.le_ceil _
  have h4 : |(w i : ℝ)| ≤ m := h2.trans h3
  rw [abs_le] at h4
  constructor
  · exact_mod_cast h4.1
  · exact_mod_cast h4.2

/-- Helper: $q(rz) = r^2q(z)$. -/
theorem qf2_smul {a b c : ℝ} (r : ℝ) (z : Fin 2 → ℝ) :
    qf2 a b c (fun i => r * z i) = r ^ 2 * qf2 a b c z := by
  simp only [qf2]; ring

/-- Helper: $q(-z) = q(z)$. -/
theorem qf2_neg {a b c : ℝ} (z : Fin 2 → ℝ) : qf2 a b c (-z) = qf2 a b c z := by
  simp only [qf2, Pi.neg_apply]; ring

/-- Helper: for $R > 0$ and real $\sigma$, $(\sqrt t/R + \sigma)^2 \to \infty$ and
$(\sqrt t/R + \sigma)^2/t \to 1/R^2$ as $t \to \infty$. -/
theorem tendsto_sq_shift (R : ℝ) (hR : 0 < R) (σ : ℝ) :
    Tendsto (fun t : ℝ => (Real.sqrt t / R + σ) ^ 2) atTop atTop ∧
    Tendsto (fun t : ℝ => (Real.sqrt t / R + σ) ^ 2 / t) atTop (𝓝 (1 / R ^ 2)) := by
  have h1 : Tendsto (fun t : ℝ => Real.sqrt t / R + σ) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Real.tendsto_sqrt_atTop.atTop_div_const hR)
  refine ⟨(tendsto_pow_atTop (two_ne_zero)).comp h1, ?_⟩
  have h2 : Tendsto (fun t : ℝ => σ / Real.sqrt t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h3 : Tendsto (fun t : ℝ => (1 / R + σ / Real.sqrt t) ^ 2) atTop (𝓝 ((1 / R + 0) ^ 2)) :=
    (tendsto_const_nhds.add h2).pow 2
  rw [add_zero] at h3
  have h3' : Tendsto (fun t : ℝ => (1 / R + σ / Real.sqrt t) ^ 2) atTop (𝓝 (1 / R ^ 2)) := by
    simpa [one_div, inv_pow] using h3
  refine h3'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have : Real.sqrt t / R + σ = Real.sqrt t * (1 / R + σ / Real.sqrt t) := by
    field_simp
  rw [this, mul_pow, Real.sq_sqrt ht.le]
  field_simp

/-- Helper: **lattice points of a congruence class in the ellipse.** For $a > 0$, $4ac - b^2 > 0$, a positive integer
$R$ and an integer vector $\rho$,
$$\frac{\#\{w \in \mathbb Z^2 : q(\rho + Rw) \le t\}}{t} \longrightarrow \frac{2\pi}{R^2\sqrt{4ac - b^2}}.$$
Proof: the shift by $\rho/R$ changes the radius of the ellipse $q(w + \rho/R) \le t/R^2$ by at most $\sqrt{q(\rho)}/R$
(triangle inequality for $\sqrt q$), and `ellipse_card_tendsto` applies to the two squeezing ellipses. -/
theorem shifted_card_tendsto {a b c : ℝ} (ha : 0 < a) (hN : 0 < 4 * a * c - b ^ 2) (R : ℕ) (hR : 0 < R)
    (ρ : Fin 2 → ℤ) :
    Tendsto (fun t : ℝ => (Nat.card {w : Fin 2 → ℤ // qf2 a b c (fun i => ((ρ i + R * w i : ℤ) : ℝ)) ≤ t} : ℝ) / t)
      atTop (𝓝 (2 * Real.pi / Real.sqrt (4 * a * c - b ^ 2) / (R : ℝ) ^ 2)) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  set A : ℝ := 2 * Real.pi / Real.sqrt (4 * a * c - b ^ 2) with hA
  set C0 : ℝ → ℕ := fun τ => Nat.card {w : Fin 2 → ℤ // qf2 a b c (fun i => (w i : ℝ)) ≤ τ} with hC0
  have h0 : Tendsto (fun τ : ℝ => (C0 τ : ℝ) / τ) atTop (𝓝 A) := ellipse_card_tendsto ha hN
  set u : Fin 2 → ℝ := fun i => (ρ i : ℝ) / R with hu
  set r : ℝ := Real.sqrt (qf2 a b c u) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- cast identity
  have hcast : ∀ w : Fin 2 → ℤ, (fun i => ((ρ i + R * w i : ℤ) : ℝ)) = fun i => (R : ℝ) * ((w i : ℝ) + u i) := by
    intro w; funext i; simp only [hu]; push_cast; field_simp; ring
  have hQ : ∀ w : Fin 2 → ℤ, qf2 a b c (fun i => ((ρ i + R * w i : ℤ) : ℝ)) =
      (R : ℝ) ^ 2 * qf2 a b c ((fun i => (w i : ℝ)) + u) := by
    intro w; rw [hcast w, qf2_smul]; rfl
  -- upper and lower inclusions
  have hup : ∀ t : ℝ, 0 ≤ t → {w : Fin 2 → ℤ | qf2 a b c (fun i => ((ρ i + R * w i : ℤ) : ℝ)) ≤ t} ⊆
      {w : Fin 2 → ℤ | qf2 a b c (fun i => (w i : ℝ)) ≤ (Real.sqrt t / R + r) ^ 2} := by
    intro t ht w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [hQ] at hw
    have h1 : qf2 a b c ((fun i => (w i : ℝ)) + u) ≤ (Real.sqrt t / R) ^ 2 := by
      rw [div_pow, Real.sq_sqrt ht]
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : Real.sqrt (qf2 a b c ((fun i => (w i : ℝ)) + u)) ≤ Real.sqrt t / R := by
      rw [Real.sqrt_le_left (by positivity)]; exact h1
    have h3 := qf2_sqrt_add_le ha hN ((fun i => (w i : ℝ)) + u) (-u)
    rw [add_neg_cancel_right, qf2_neg] at h3
    have h4 : Real.sqrt (qf2 a b c (fun i => (w i : ℝ))) ≤ Real.sqrt t / R + r := by linarith
    rw [Real.sqrt_le_left (by positivity)] at h4
    exact h4
  have hlow : ∀ t : ℝ, 0 ≤ t → r ≤ Real.sqrt t / R →
      {w : Fin 2 → ℤ | qf2 a b c (fun i => (w i : ℝ)) ≤ (Real.sqrt t / R + -r) ^ 2} ⊆
      {w : Fin 2 → ℤ | qf2 a b c (fun i => ((ρ i + R * w i : ℤ) : ℝ)) ≤ t} := by
    intro t ht hrt w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [hQ]
    have h1 : Real.sqrt (qf2 a b c (fun i => (w i : ℝ))) ≤ Real.sqrt t / R - r := by
      rw [Real.sqrt_le_left (by linarith)]; simpa [sub_eq_add_neg] using hw
    have h3 := qf2_sqrt_add_le ha hN (fun i => (w i : ℝ)) u
    have h4 : Real.sqrt (qf2 a b c ((fun i => (w i : ℝ)) + u)) ≤ Real.sqrt t / R := by linarith
    rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt ht, le_div_iff₀ (by positivity)] at h4
    linarith
  -- squeeze
  obtain ⟨hτ1, hτ2⟩ := tendsto_sq_shift R hR' r
  obtain ⟨hτ1', hτ2'⟩ := tendsto_sq_shift R hR' (-r)
  have hU : Tendsto (fun t : ℝ => (C0 ((Real.sqrt t / R + r) ^ 2) : ℝ) / t) atTop (𝓝 (A * (1 / (R : ℝ) ^ 2))) := by
    have := (h0.comp hτ1).mul hτ2
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0, hτ1.eventually_gt_atTop 0] with t ht hτ
    simp only [Function.comp_apply]
    field_simp
  have hL : Tendsto (fun t : ℝ => (C0 ((Real.sqrt t / R + -r) ^ 2) : ℝ) / t) atTop (𝓝 (A * (1 / (R : ℝ) ^ 2))) := by
    have := (h0.comp hτ1').mul hτ2'
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0, hτ1'.eventually_gt_atTop 0] with t ht hτ
    simp only [Function.comp_apply]
    generalize (Real.sqrt t / R + -r) ^ 2 = τ at hτ ⊢
    field_simp
  rw [show A / (R : ℝ) ^ 2 = A * (1 / (R : ℝ) ^ 2) by ring]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · have hev : ∀ᶠ t : ℝ in atTop, (R * r) ^ 2 ≤ t := eventually_ge_atTop _
    filter_upwards [hev, eventually_gt_atTop 0] with t hrt ht
    have hrt' : r ≤ Real.sqrt t / R := by
      rw [le_div_iff₀ hR']
      calc r * R = R * r := by ring
        _ = Real.sqrt ((R * r) ^ 2) := by rw [Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt t := Real.sqrt_le_sqrt hrt
    have hfin : Set.Finite {w : Fin 2 → ℤ | qf2 a b c (fun i => ((ρ i + R * w i : ℤ) : ℝ)) ≤ t} :=
      (finite_ellipse_int ha hN _).subset (hup t ht.le)
    have := Nat.card_mono hfin (hlow t ht.le hrt')
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) ht.le
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have := Nat.card_mono (finite_ellipse_int ha hN _) (hup t ht.le)
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) ht.le

end Shift

section Local

open Finset



/-- Helper: a nonzero linear form $\alpha x_0 + \beta x_1$ on $\mathbb F_p^2$ has exactly $p$ zeros. Arguments: `p` the
prime, `α`, `β` the coefficients, `h` that they are not both zero. -/
theorem kernel_card (p : ℕ) [Fact p.Prime] (α β : ZMod p) (h : α ≠ 0 ∨ β ≠ 0) :
    Fintype.card {σ : Fin 2 → ZMod p // α * σ 0 + β * σ 1 = 0} = p := by
  by_cases hβ : β = 0
  · have hα : α ≠ 0 := by tauto
    refine Eq.trans (Fintype.card_congr (Equiv.symm ?_)) (ZMod.card p)
    refine
      { toFun := fun t => ⟨![0, t], by simp [hβ]⟩
        invFun := fun σ => σ.1 1
        left_inv := fun t => by simp
        right_inv := fun σ => ?_ }
    apply Subtype.ext
    have h0 : σ.1 0 = 0 := by
      have := σ.2
      simp only [hβ, zero_mul, add_zero, mul_eq_zero, hα, false_or] at this
      exact this
    funext i
    fin_cases i
    · simp [h0]
    · simp
  · refine Eq.trans (Fintype.card_congr (Equiv.symm ?_)) (ZMod.card p)
    refine
      { toFun := fun t => ⟨![t, -(α * t) / β], by simp; field_simp; ring⟩
        invFun := fun σ => σ.1 0
        left_inv := fun t => by simp
        right_inv := fun σ => ?_ }
    apply Subtype.ext
    funext i
    have h1 : σ.1 1 = -(α * σ.1 0) / β := by
      have := σ.2
      field_simp
      linear_combination this
    fin_cases i
    · simp
    · simp [h1]

/-- Helper: over $\mathbb F_2$, $xs^2 + yt^2 = 0 \iff xs + yt = 0$ (as $s^2 = s$). -/
theorem zmod2_key : ∀ x y s t : ZMod 2, x * s ^ 2 + y * t ^ 2 = 0 ↔ x * s + y * t = 0 := by decide

/-- Helper: $4 = 0$ in $\mathbb Z/2$. -/
theorem zmod2_four : (4 : ZMod 2) = 0 := by decide

/-- Helper: **a form of discriminant divisible by $p$ vanishes on a line mod $p$.** If the prime $p$ divides
$b^2 - 4ac$ and does not divide all of $a, b, c$, then the zeros of $ax^2 + bxy + cy^2$ on $\mathbb F_p^2$ are the zeros
of a nonzero linear form (for $p$ odd: $2ax + by$ if $p \nmid a$, else $y$; for $p = 2$: $ax + cy$). -/
theorem local_zero_form (p : ℕ) [Fact p.Prime] (a b c : ℤ) (hD : (p : ℤ) ∣ b ^ 2 - 4 * a * c)
    (hprim : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    ∃ α β : ZMod p, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ σ : Fin 2 → ZMod p,
      ((a : ZMod p) * σ 0 ^ 2 + (b : ZMod p) * σ 0 * σ 1 + (c : ZMod p) * σ 1 ^ 2 = 0 ↔
        α * σ 0 + β * σ 1 = 0) := by
  have hD' : (b : ZMod p) ^ 2 - 4 * (a : ZMod p) * (c : ZMod p) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hD
    push_cast at this
    exact this
  have hprim' : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0 ∨ (c : ZMod p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hprim
    refine ⟨?_, ?_, ?_⟩ <;> rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] <;> tauto
  by_cases hp2 : p = 2
  · subst hp2
    have hb : (b : ZMod 2) = 0 := by
      rw [zmod2_four] at hD'
      simpa using hD'
    have key := zmod2_key
    refine ⟨(a : ZMod 2), (c : ZMod 2), ?_, fun σ => ?_⟩
    · rcases hprim' with h | h | h
      · exact Or.inl h
      · exact absurd hb h
      · exact Or.inr h
    · rw [hb]
      simp
  · have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this
      exact hp2 this
    by_cases ha : (a : ZMod p) = 0
    · have hb : (b : ZMod p) = 0 := by
        rw [ha] at hD'
        simpa using hD'
      have hc : (c : ZMod p) ≠ 0 := by
        rcases hprim' with h | h | h
        · exact absurd ha h
        · exact absurd hb h
        · exact h
      refine ⟨0, 1, Or.inr one_ne_zero, fun σ => ?_⟩
      rw [ha, hb]
      simp [hc]
    · refine ⟨2 * (a : ZMod p), (b : ZMod p), Or.inl (mul_ne_zero h2 ha), fun σ => ?_⟩
      have h4 : (4 : ZMod p) * (a : ZMod p) ≠ 0 := by
        have : (4 : ZMod p) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) ha
      have hid : (4 : ZMod p) * (a : ZMod p) * ((a : ZMod p) * σ 0 ^ 2 + (b : ZMod p) * σ 0 * σ 1 + (c : ZMod p) * σ 1 ^ 2) =
          (2 * (a : ZMod p) * σ 0 + (b : ZMod p) * σ 1) ^ 2 := by
        linear_combination (-(σ 1) ^ 2) * hD'
      constructor
      · intro h
        rw [h, mul_zero] at hid
        exact pow_eq_zero_iff (two_ne_zero) |>.mp hid.symm
      · intro h
        rw [h] at hid
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hid
        exact (mul_eq_zero.mp (by simpa using hid)).resolve_left h4

/-- Helper: **a form of discriminant divisible by $p$ has exactly $p$ zeros on $\mathbb F_p^2$** (same hypotheses as
`local_zero_form`). -/
theorem zero_count (p : ℕ) [Fact p.Prime] (a b c : ℤ) (hD : (p : ℤ) ∣ b ^ 2 - 4 * a * c)
    (hprim : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    Fintype.card {σ : Fin 2 → ZMod p //
      (a : ZMod p) * σ 0 ^ 2 + (b : ZMod p) * σ 0 * σ 1 + (c : ZMod p) * σ 1 ^ 2 = 0} = p := by
  obtain ⟨α, β, hαβ, hiff⟩ := local_zero_form p a b c hD hprim
  exact (Fintype.card_congr (Equiv.subtypeEquivRight hiff)).trans (kernel_card p α β hαβ)

end Local

section CRT

open Finset



/-- Helper: the product $R$ of the distinct primes dividing $n$ (the radical of $n$). -/
def primeProd (n : ℕ) : ℕ := ∏ p : n.primeFactors, (p : ℕ)

/-- Helper: $R > 0$. -/
theorem primeProd_pos (n : ℕ) : 0 < primeProd n :=
  Finset.prod_pos (fun p _ => (Nat.prime_of_mem_primeFactors p.2).pos)

/-- Helper: the distinct primes dividing $n$ are pairwise coprime. -/
theorem primeProd_coprime (n : ℕ) :
    Pairwise (Function.onFun Nat.Coprime fun p : n.primeFactors => (p : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2) (Nat.prime_of_mem_primeFactors q.2)).mpr
    (fun h => hpq (Subtype.ext h))

/-- Helper: the form $ax^2 + bxy + cy^2$ evaluated at a vector of $(\mathbb Z/p)^2$. -/
def fbar (a b c : ℤ) (p : ℕ) (σ : Fin 2 → ZMod p) : ZMod p :=
  (a : ZMod p) * σ 0 ^ 2 + (b : ZMod p) * σ 0 * σ 1 + (c : ZMod p) * σ 1 ^ 2

/-- Helper: **the Chinese remainder isomorphism on vectors:** $(\mathbb Z/R)^2 \simeq \prod_{p \mid n}(\mathbb Z/p)^2$,
$R$ = `primeProd n`. -/
noncomputable def crtVec (n : ℕ) :
    (Fin 2 → ZMod (primeProd n)) ≃ ((p : n.primeFactors) → (Fin 2 → ZMod (p : ℕ))) :=
  (Equiv.arrowCongr (Equiv.refl (Fin 2)) (ZMod.prodEquivPi (fun p : n.primeFactors => (p : ℕ)) (primeProd_coprime n)).toEquiv).trans
    (Equiv.piComm (fun (_ : Fin 2) (p : n.primeFactors) => ZMod (p : ℕ)))

/-- Helper: the $p$-component of `crtVec n` is reduction mod $p$. -/
theorem crtVec_apply (n : ℕ) (ρ : Fin 2 → ZMod (primeProd n)) (p : n.primeFactors) (i : Fin 2) :
    crtVec n ρ p i = ZMod.castHom (dvd_prod_of_mem (fun p : n.primeFactors => (p : ℕ)) (mem_univ p)) (ZMod (p : ℕ)) (ρ i) := by
  show (ZMod.prodEquivPi (fun p : n.primeFactors => (p : ℕ)) (primeProd_coprime n) (ρ i)) p = _
  exact ZMod.prodEquivPi_apply _ _ (ρ i) p

/-- Helper: a residue class $\rho \in (\mathbb Z/R)^2$ is **good** if the form does not vanish mod any prime $p \mid n$ on the
reduction of $\rho$. -/
def goodClass (a b c : ℤ) (n : ℕ) (ρ : Fin 2 → ZMod (primeProd n)) : Prop :=
  ∀ p : n.primeFactors, fbar a b c (p : ℕ) (crtVec n ρ p) ≠ 0

/-- Helper: **the number of good residue classes** is $\prod_{p \mid n}(p^2 - p)$ (Chinese remainder theorem and
`zero_count`; hypotheses: each $p \mid n$ divides $b^2 - 4ac$ and does not divide all of $a, b, c$). -/
theorem card_goodClass (a b c : ℤ) (n : ℕ)
    (hD : ∀ p ∈ n.primeFactors, (p : ℤ) ∣ b ^ 2 - 4 * a * c)
    (hprim : ∀ p ∈ n.primeFactors, ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) [NeZero (primeProd n)] :
    Nat.card {ρ : Fin 2 → ZMod (primeProd n) // goodClass a b c n ρ} = ∏ p ∈ n.primeFactors, (p ^ 2 - p) := by
  classical
  have h1 : Nat.card {ρ : Fin 2 → ZMod (primeProd n) // goodClass a b c n ρ} =
      Nat.card {τ : (p : n.primeFactors) → (Fin 2 → ZMod (p : ℕ)) // ∀ p : n.primeFactors, fbar a b c (p : ℕ) (τ p) ≠ 0} :=
    Nat.card_congr ((crtVec n).subtypeEquiv (fun ρ => by simp [goodClass]))
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi (β := fun p : n.primeFactors => Fin 2 → ZMod (p : ℕ)) (p := fun p σ => fbar a b c (p : ℕ) σ ≠ 0)), Nat.card_pi]
  rw [← Finset.prod_coe_sort n.primeFactors (fun p => p ^ 2 - p)]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hz : Fintype.card {σ : Fin 2 → ZMod (p : ℕ) // fbar a b c (p : ℕ) σ = 0} = p :=
    zero_count (p : ℕ) a b c (hD p p.2) (hprim p p.2)
  have hcompl := Fintype.card_subtype_compl (fun σ : Fin 2 → ZMod (p : ℕ) => fbar a b c (p : ℕ) σ = 0)
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, hz] at hcompl
  rw [Nat.card_eq_fintype_card]
  convert hcompl using 1

end CRT

section Classes

open MeasureTheory Filter Topology Finset



/-- Helper: the integer value $ax_0^2 + bx_0x_1 + cx_1^2$ of the form at an integer vector. -/
def Fint (a b c : ℤ) (v : Fin 2 → ℤ) : ℤ := a * v 0 ^ 2 + b * v 0 * v 1 + c * v 1 ^ 2

/-- Helper: an integer vector $v$ is **good** if no prime $p \mid n$ divides $f(v)$ (i.e. $(f(v), n) = 1$ when $n \ne 0$). -/
def goodVec (a b c : ℤ) (n : ℕ) (v : Fin 2 → ℤ) : Prop :=
  ∀ p ∈ n.primeFactors, ¬ (p : ℤ) ∣ Fint a b c v

/-- Helper: the residue class of an integer vector in $(\mathbb Z/R)^2$. -/
def resVec (n : ℕ) (v : Fin 2 → ℤ) : Fin 2 → ZMod (primeProd n) := fun i => (v i : ZMod (primeProd n))

/-- Helper: the $p$-component of the class of $v$ is $v$ mod $p$. -/
theorem crtVec_resVec (n : ℕ) (v : Fin 2 → ℤ) (p : n.primeFactors) :
    crtVec n (resVec n v) p = fun i => (v i : ZMod (p : ℕ)) := by
  funext i
  rw [crtVec_apply]
  exact map_intCast _ _

/-- Helper: $v$ is good iff its residue class is good. -/
theorem goodVec_iff (a b c : ℤ) (n : ℕ) (v : Fin 2 → ℤ) :
    goodVec a b c n v ↔ goodClass a b c n (resVec n v) := by
  unfold goodVec goodClass
  have key : ∀ p : n.primeFactors, fbar a b c (p : ℕ) (crtVec n (resVec n v) p) = ((Fint a b c v : ℤ) : ZMod (p : ℕ)) := by
    intro p
    rw [crtVec_resVec]
    simp [fbar, Fint]
  constructor
  · intro h p
    rw [key, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h p p.2
  · intro h p hp
    have := h ⟨p, hp⟩
    rw [key, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact this

/-- Helper: the cardinality of $\{v : P(v) \wedge G(v)\}$ for a finite set $\{P\}$ is the cardinality of the filter of
the finset of `hS.toFinset` by `G`. -/
theorem natCard_subtype_and {α : Type*} {P : α → Prop} (hS : Set.Finite {v | P v}) (G : α → Prop) [DecidablePred G] :
    Nat.card {v // P v ∧ G v} = (hS.toFinset.filter G).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun v => by simp))

/-- Helper: the canonical integer lift (entries in $[0, R)$) of a residue vector. -/
def liftVec (n : ℕ) [NeZero (primeProd n)] (ρ : Fin 2 → ZMod (primeProd n)) : Fin 2 → ℤ :=
  fun i => ((ρ i).val : ℤ)

/-- Helper: the class of the lift of $\rho$ is $\rho$. -/
theorem resVec_liftVec (n : ℕ) [NeZero (primeProd n)] (ρ : Fin 2 → ZMod (primeProd n)) :
    resVec n (liftVec n ρ) = ρ := by
  funext i
  simp [resVec, liftVec]

/-- Helper: $v \equiv \rho \pmod R$ iff $v = \operatorname{lift}(\rho) + Rw$ for some integer vector $w$. -/
theorem resVec_eq_iff (n : ℕ) [NeZero (primeProd n)] (ρ : Fin 2 → ZMod (primeProd n)) (v : Fin 2 → ℤ) :
    resVec n v = ρ ↔ ∃ w : Fin 2 → ℤ, v = fun i => liftVec n ρ i + (primeProd n : ℤ) * w i := by
  constructor
  · intro h
    have hi : ∀ i, (primeProd n : ℤ) ∣ v i - liftVec n ρ i := by
      intro i
      have h1 : (v i : ZMod (primeProd n)) = ((liftVec n ρ i : ℤ) : ZMod (primeProd n)) := by
        have := congrFun h i
        have h2 := congrFun (resVec_liftVec n ρ) i
        simp only [resVec] at this h2
        rw [this, h2]
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1.symm
      exact this
    choose w hw using hi
    refine ⟨w, funext fun i => ?_⟩
    have := hw i
    linarith
  · rintro ⟨w, rfl⟩
    funext i
    simp only [resVec, liftVec]
    push_cast
    simp

/-- Helper: the real value of the form $q_{a,b,c}$ (integer coefficients) at an integer vector. -/
noncomputable def Qr (a b c : ℤ) (v : Fin 2 → ℤ) : ℝ := qf2 (a : ℝ) (b : ℝ) (c : ℝ) (fun i => (v i : ℝ))

open scoped Classical in
/-- Helper: **decomposition by residue classes:** the number of good integer vectors $v$ with $q(v) \le t$ is the sum over
good classes $\rho$ of the number of $w$ with $q(\operatorname{lift}\rho + Rw) \le t$. -/
theorem card_good_decomp (a b c : ℤ) (n : ℕ) (ha : 0 < a) (hn : (n : ℤ) = 4 * a * c - b ^ 2) (hn0 : 0 < n) (t : ℝ) [NeZero (primeProd n)] :
    Nat.card {v : Fin 2 → ℤ // Qr a b c v ≤ t ∧ goodVec a b c n v} =
      ∑ ρ ∈ Finset.univ.filter (goodClass a b c n),
        Nat.card {w : Fin 2 → ℤ // qf2 (a : ℝ) b c (fun i => ((liftVec n ρ i + (primeProd n : ℤ) * w i : ℤ) : ℝ)) ≤ t} := by
  classical
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hN' : (0 : ℝ) < 4 * (a : ℝ) * c - (b : ℝ) ^ 2 := by
    have : (0 : ℤ) < 4 * a * c - b ^ 2 := by rw [← hn]; exact_mod_cast (show (0:ℤ) < n by exact_mod_cast hn0)
    exact_mod_cast this
  have hS : Set.Finite {v : Fin 2 → ℤ | Qr a b c v ≤ t} := finite_ellipse_int ha' hN' t
  rw [natCard_subtype_and hS]
  rw [Finset.card_eq_sum_card_fiberwise (f := resVec n) (t := Finset.univ.filter (goodClass a b c n))]
  · refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have hρ' : goodClass a b c n ρ := (Finset.mem_filter.mp hρ).2
    have hfilt : (hS.toFinset.filter (goodVec a b c n)).filter (fun v => resVec n v = ρ) =
        hS.toFinset.filter (fun v => resVec n v = ρ) := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, (goodVec_iff a b c n v).mpr (h3 ▸ hρ')⟩, h3⟩
    rw [hfilt, ← natCard_subtype_and (G := fun v => resVec n v = ρ) hS]
    have hR0 : (primeProd n : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne (primeProd n))
    let f : {w : Fin 2 → ℤ // qf2 (a : ℝ) b c (fun i => ((liftVec n ρ i + (primeProd n : ℤ) * w i : ℤ) : ℝ)) ≤ t} →
        {v : Fin 2 → ℤ // Qr a b c v ≤ t ∧ resVec n v = ρ} := fun w =>
      ⟨fun i => liftVec n ρ i + (primeProd n : ℤ) * w.1 i, w.2,
        (resVec_eq_iff n ρ _).mpr ⟨w.1, rfl⟩⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro w w' h
        apply Subtype.ext
        funext i
        have := congrFun (congrArg Subtype.val h) i
        simp only [f] at this
        exact mul_left_cancel₀ hR0 (by linarith)
      · rintro ⟨v, hv1, hv2⟩
        obtain ⟨w, hw⟩ := (resVec_eq_iff n ρ v).mp hv2
        refine ⟨⟨w, ?_⟩, Subtype.ext hw.symm⟩
        subst hw
        exact hv1
    exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, (goodVec_iff a b c n v).mp hv.2⟩

/-- Helper: `primeProd n` as a product over the finset of prime divisors. -/
theorem primeProd_eq (n : ℕ) : primeProd n = ∏ p ∈ n.primeFactors, p := by
  unfold primeProd
  exact Finset.prod_coe_sort n.primeFactors (fun p => p)

open scoped Classical in
/-- Helper: **the density of good lattice points in the ellipse.** For integers $a > 0$, $b$, $c$ and $n > 0$ with
$n = 4ac - b^2$ such that no prime $p \mid n$ divides all of $a, b, c$,
$$\frac{\#\{v \in \mathbb Z^2 : q(v) \le t,\ (f(v), n) = 1\}}{t} \longrightarrow
\frac{2\pi}{\sqrt n}\prod_{p \mid n}\Big(1 - \frac1p\Big).$$
(Sum of `shifted_card_tendsto` over the $\prod_{p \mid n}(p^2 - p)$ good classes mod $R = \prod_{p \mid n}p$.) -/
theorem good_count_tendsto (a b c : ℤ) (n : ℕ) (ha : 0 < a) (hn : (n : ℤ) = 4 * a * c - b ^ 2) (hn0 : 0 < n)
    (hprim : ∀ p ∈ n.primeFactors, ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    Tendsto (fun t : ℝ => (Nat.card {v : Fin 2 → ℤ // Qr a b c v ≤ t ∧ goodVec a b c n v} : ℝ) / t) atTop
      (𝓝 (2 * Real.pi / Real.sqrt n * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)))) := by
  have hRne : NeZero (primeProd n) := ⟨(primeProd_pos n).ne'⟩
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hnR : (n : ℝ) = 4 * (a : ℝ) * c - (b : ℝ) ^ 2 := by exact_mod_cast hn
  have hN' : (0 : ℝ) < 4 * (a : ℝ) * c - (b : ℝ) ^ 2 := by rw [← hnR]; exact_mod_cast hn0
  have hD : ∀ p ∈ n.primeFactors, (p : ℤ) ∣ b ^ 2 - 4 * a * c := by
    intro p hp
    have h1 : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    rw [hn] at h1
    have := dvd_neg.mpr h1
    convert this using 1; ring
  have hcard := card_goodClass a b c n hD hprim
  have hfun : (fun t : ℝ => (Nat.card {v : Fin 2 → ℤ // Qr a b c v ≤ t ∧ goodVec a b c n v} : ℝ) / t) =
      fun t : ℝ => ∑ ρ ∈ Finset.univ.filter (goodClass a b c n),
        (Nat.card {w : Fin 2 → ℤ // qf2 (a : ℝ) b c (fun i => ((liftVec n ρ i + (primeProd n : ℤ) * w i : ℤ) : ℝ)) ≤ t} : ℝ) / t := by
    funext t
    rw [card_good_decomp a b c n ha hn hn0 t, Nat.cast_sum, Finset.sum_div]
  rw [hfun]
  have hsum := tendsto_finsetSum (Finset.univ.filter (goodClass a b c n))
    (f := fun ρ t => (Nat.card {w : Fin 2 → ℤ // qf2 (a : ℝ) b c (fun i => ((liftVec n ρ i + (primeProd n : ℤ) * w i : ℤ) : ℝ)) ≤ t} : ℝ) / t)
    (a := fun _ => 2 * Real.pi / Real.sqrt (4 * (a : ℝ) * c - (b : ℝ) ^ 2) / (primeProd n : ℝ) ^ 2)
    (fun ρ _ => shifted_card_tendsto ha' hN' (primeProd n) (primeProd_pos n) (liftVec n ρ))
  have hU : (Finset.univ.filter (goodClass a b c n)).card = ∏ p ∈ n.primeFactors, (p ^ 2 - p) := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_const, hU, nsmul_eq_mul, ← hnR] at hsum
  convert hsum using 2
  rw [Nat.cast_prod, primeProd_eq, Nat.cast_prod]
  have hP : ∀ p ∈ n.primeFactors, ((p ^ 2 - p : ℕ) : ℝ) = (p : ℝ) ^ 2 * (1 - 1 / (p : ℝ)) := by
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [Nat.cast_sub (Nat.le_self_pow two_ne_zero p)]
    push_cast
    field_simp
  rw [Finset.prod_congr rfl hP, Finset.prod_mul_distrib, ← Finset.prod_pow]
  have hp0 : ∀ p ∈ n.primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have : (∏ p ∈ n.primeFactors, (p : ℝ) ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero 2 (hp0 p hp))
  field_simp

end Classes

section Orbits

open Matrix Filter Topology Finset

/-- Helper: a proper automorph preserves the value of the form on vectors. -/
theorem eval_mulVec_aut (f : BinQF) {γ : GL (Fin 2) ℤ} (hγ : γ ∈ AutSL f) (v : Fin 2 → ℤ) :
    f.eval ((γ.val *ᵥ v) 0) ((γ.val *ᵥ v) 1) = f.eval (v 0) (v 1) := by
  have h : ∀ x, QuadForm.eval f (γ.val *ᵥ x) = QuadForm.eval f x := (mem_autSL.mp hγ).1
  have := h v
  have e1 : (γ.val *ᵥ v) = ![(γ.val *ᵥ v) 0, (γ.val *ᵥ v) 1] := vec_two_eq _
  have e2 : v = ![v 0, v 1] := vec_two_eq _
  unfold BinQF.eval
  rw [← e1, ← e2]
  exact this

/-- Helper: **the action of the proper automorphs `AutSL f` on the representations `repVecs f m`** of $m$ by matrix
multiplication. -/
instance autSLAction (f : BinQF) (m : ℕ) : MulAction (AutSL f) (repVecs f m) where
  smul g x := ⟨g.1.val *ᵥ x.1, by
    have hx : f.eval (x.1 0) (x.1 1) = m := x.2
    show f.eval ((g.1.val *ᵥ x.1) 0) ((g.1.val *ᵥ x.1) 1) = m
    rw [eval_mulVec_aut f g.2, hx]⟩
  one_smul x := by
    apply Subtype.ext
    show (1 : AutSL f).1.val *ᵥ x.1 = x.1
    simp
  mul_smul g h x := by
    apply Subtype.ext
    show (g.1 * h.1).val *ᵥ x.1 = g.1.val *ᵥ (h.1.val *ᵥ x.1)
    rw [Units.val_mul, mulVec_mulVec]

/-- Helper: the action is matrix-vector multiplication. -/
theorem smul_val (f : BinQF) (m : ℕ) (g : AutSL f) (x : repVecs f m) :
    ((g • x : repVecs f m) : Fin 2 → ℤ) = g.1.val *ᵥ x.1 := rfl

/-- Helper: a matrix $M \in \mathrm{SL}_2(\mathbb Z)$ of finite order ($M^k = 1$, $k > 0$) fixing a nonzero vector is the
identity (it is unipotent, $M = 1 + N$ with $N^2 = 0$, so $M^k = 1 + kN$). -/
theorem unip_eq_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (v : Fin 2 → ℤ) (hv : v ≠ 0)
    (hMv : M *ᵥ v = v) (k : ℕ) (hk : 0 < k) (hMk : M ^ k = 1) : M = 1 := by
  have hdet' := Matrix.det_fin_two M
  rw [hdet] at hdet'
  have h0 : M 0 0 * v 0 + M 0 1 * v 1 = v 0 := by
    have := congrFun hMv 0
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using this
  have h1 : M 1 0 * v 0 + M 1 1 * v 1 = v 1 := by
    have := congrFun hMv 1
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdz : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 = 0 := by
    by_contra hne
    apply hv
    funext i
    fin_cases i
    · show v 0 = 0
      apply mul_left_cancel₀ hne
      linear_combination (M 1 1 - 1) * h0 - M 0 1 * h1
    · show v 1 = 0
      apply mul_left_cancel₀ hne
      linear_combination (M 0 0 - 1) * h1 - M 1 0 * h0
  have htr : M 0 0 + M 1 1 = 2 := by linarith
  -- N = M - 1 satisfies N^2 = 0
  set N : Matrix (Fin 2) (Fin 2) ℤ := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  have hN2 : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hN, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination hdet' + M 0 0 * htr
        | linear_combination hdet' + M 1 1 * htr
        | linear_combination M 0 1 * htr
        | linear_combination M 1 0 * htr
  have hpow : ∀ j : ℕ, M ^ j = 1 + (j : ℤ) • N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, hMN]
      have : (1 + (j : ℤ) • N) * (1 + N) = 1 + ((j + 1 : ℕ) : ℤ) • N + (j : ℤ) • (N * N) := by
        simp only [mul_add, add_mul, one_mul, mul_one, Matrix.smul_mul]
        push_cast
        module
      rw [this, hN2]; simp
  rw [hpow k] at hMk
  have hkN : (k : ℤ) • N = 0 := by
    have := congrArg (fun X => X - 1) hMk
    simpa using this
  have hN0 : N = 0 := by
    ext i j
    have := congrFun (congrFun hkN i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast h : k = 0) hk.ne'
    · exact h
  rw [hMN, hN0, add_zero]

/-- Helper: **the action of `AutSL f` on the nonzero representations is free** ($f$ definite, so `AutSL f` is finite):
an element fixing a representation of $m > 0$ is the identity. -/
theorem autSL_free (f : BinQF) [Finite (AutSL f)] (m : ℕ) (hm : 0 < m) (g : AutSL f) (x : repVecs f m)
    (hgx : g • x = x) : g = 1 := by
  have hxne : x.1 ≠ 0 := by
    intro h0
    have hx : f.eval (x.1 0) (x.1 1) = m := x.2
    rw [h0] at hx
    simp [BinQF.eval_eq] at hx
    omega
  have hord : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hk : 0 < orderOf g := hord.orderOf_pos
  have hpow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hM : (g.1.val) ^ orderOf g = 1 := by
    have h1 : ((g ^ orderOf g : AutSL f) : GL (Fin 2) ℤ) = 1 := by rw [hpow]; rfl
    rw [Subgroup.coe_pow] at h1
    rw [← Units.val_pow_eq_pow_val, h1]
    rfl
  have hdet : g.1.val.det = 1 := (mem_autSL.mp g.2).2
  have hMv : g.1.val *ᵥ x.1 = x.1 := by
    have := congrArg Subtype.val hgx
    exact this
  have := unip_eq_one g.1.val hdet x.1 hxne hMv (orderOf g) hk hM
  apply Subtype.ext
  apply Units.ext
  simpa using this

/-- Helper: **orbit counting:** for $m > 0$ and `AutSL f` finite acting freely, the number of representations of $m$ by $f$
is $|\mathrm{Aut}^+(f)|$ times the number $a^*_f(m)$ of orbits (`MulAction.selfEquivSigmaOrbitsQuotientStabilizer`). -/
theorem card_repVecs (f : BinQF) [Finite (AutSL f)] (m : ℕ) (hm : 0 < m) [Finite (repVecs f m)] :
    Nat.card (repVecs f m) = Nat.card (AutSL f) * repOrbitCount f m := by
  classical
  have : Fintype (AutSL f) := Fintype.ofFinite _
  have hfin : Fintype (Quotient (MulAction.orbitRel (AutSL f) (repVecs f m))) := Fintype.ofFinite _
  -- the setoids agree
  have hsetoid : Nat.card (Quotient ((autOrbitSetoid f).comap (Subtype.val : repVecs f m → Fin 2 → ℤ))) =
      Nat.card (Quotient (MulAction.orbitRel (AutSL f) (repVecs f m))) := by
    refine Nat.card_congr (Quotient.congrRight (fun x y => ?_))
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨(⟨γ, hγ⟩ : AutSL f)⁻¹, ?_⟩
      apply Subtype.ext
      show (γ⁻¹).val *ᵥ y.1 = x.1
      rw [← h, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    · rintro ⟨g, hg⟩
      refine ⟨g.1⁻¹, inv_mem g.2, ?_⟩
      have hg' : g.1.val *ᵥ y.1 = x.1 := congrArg Subtype.val hg
      show (g.1⁻¹).val *ᵥ x.1 = y.1
      rw [← hg', mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  unfold repOrbitCount
  rw [hsetoid, Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (AutSL f) (repVecs f m)),
    Nat.card_sigma]
  have hcard : ∀ ω : Quotient (MulAction.orbitRel (AutSL f) (repVecs f m)),
      Nat.card (AutSL f ⧸ MulAction.stabilizer (AutSL f) ω.out) = Nat.card (AutSL f) := by
    intro ω
    have hstab : MulAction.stabilizer (AutSL f) ω.out = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact autSL_free f m hm g _ (MulAction.mem_stabilizer_iff.mp hg)
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer (AutSL f) ω.out)
    rw [hstab, Subgroup.card_bot, mul_one] at this
    rw [hstab]
    exact this.symm
  rw [Finset.sum_congr rfl (fun ω _ => hcard ω), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, mul_comm]
  simp


/-- Helper: $(m, N) = 1$ iff no prime divisor of $N$ divides $m$ ($N \ne 0$). -/
theorem coprime_iff_noPrime (m N : ℕ) (hN : N ≠ 0) :
    Nat.Coprime m N ↔ ∀ p ∈ N.primeFactors, ¬ p ∣ m := by
  constructor
  · intro h p hp hpm
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have := Nat.eq_one_of_dvd_coprimes h hpm hpN
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' this
  · intro h
    apply Nat.coprime_of_dvd
    intro k hk hkm hkN
    exact h k (Nat.mem_primeFactors.mpr ⟨hk, hkN, hN⟩) hkm

/-- Helper: `Qr a b c v` is the integer `Fint a b c v` cast to $\mathbb R$. -/
theorem Qr_eq (a b c : ℤ) (v : Fin 2 → ℤ) : Qr a b c v = (Fint a b c v : ℝ) := by
  simp only [Qr, qf2, Fint]
  push_cast
  ring

/-- Helper: `f.eval` at a vector is `Fint f.a f.b f.c`. -/
theorem eval_eq_Fint (f : BinQF) (v : Fin 2 → ℤ) : f.eval (v 0) (v 1) = Fint f.a f.b f.c v := by
  rw [BinQF.eval_eq]
  simp [Fint]

/-- Helper: **$w\cdot A^*_f(M)$ is the number of lattice points of the ellipse:** for a positive definite $f$ of
fundamental discriminant $D < 0$ (finite `AutSL f`),
$|\mathrm{Aut}^+(f)|\cdot A^*_f(M) = \#\{v : f(v) \le M,\ (f(v), D) = 1\}$ (Cassels, proof of Lemma 2.1: "$wA^*(M)$ is the
number of integer solutions of (2.11) subject to (2.12)"). -/
theorem orbitCount_mul_card (f : BinQF) (D : ℤ) [IsQuadDisc D] (hD : D < 0) (hf : f.disc = D) (hpos : f.PosDef)
    (M : ℕ) [Finite (AutSL f)] :
    Nat.card (AutSL f) * (∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs), repOrbitCount f m) =
      Nat.card {v : Fin 2 → ℤ // Qr f.a f.b f.c v ≤ M ∧ goodVec f.a f.b f.c f.disc.natAbs v} := by
  classical
  have ha : 0 < f.a := ((BinQF.posDef_iff_posDef' f).mp hpos).1
  have hdisc : f.disc < 0 := hf ▸ hD
  have hN : (f.disc.natAbs : ℤ) = 4 * f.a * f.c - f.b ^ 2 := by
    have h1 : ((f.disc.natAbs : ℕ) : ℤ) = - f.disc := by omega
    rw [h1]
    simp only [BinQF.disc]; ring
  have h3 : 3 ≤ f.disc.natAbs := by rw [hf]; exact three_le_natAbs
  have hN0 : f.disc.natAbs ≠ 0 := by omega
  have ha' : (0 : ℝ) < f.a := by exact_mod_cast ha
  have hN' : (0 : ℝ) < 4 * (f.a : ℝ) * f.c - (f.b : ℝ) ^ 2 := by
    have : (0 : ℤ) < 4 * f.a * f.c - f.b ^ 2 := by rw [← hN]; exact_mod_cast Nat.pos_of_ne_zero hN0
    exact_mod_cast this
  have hnn : ∀ v : Fin 2 → ℤ, 0 ≤ Fint f.a f.b f.c v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [Fint]
    · have := hpos (v 0) (v 1) (by
        intro h
        apply hv
        funext i
        fin_cases i
        · exact (Prod.mk.inj h).1
        · exact (Prod.mk.inj h).2)
      rw [eval_eq_Fint] at this
      exact this.le
  have hS : Set.Finite {v : Fin 2 → ℤ | Qr f.a f.b f.c v ≤ M} := finite_ellipse_int ha' hN' M
  rw [natCard_subtype_and hS]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v => (Fint f.a f.b f.c v).toNat)
    (t := (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs))]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmM⟩, hmcop⟩ := hm
    have hfinm : Finite (repVecs f m) := by
      refine Set.Finite.subset hS ?_
      intro v hv
      have hv' : f.eval (v 0) (v 1) = m := hv
      rw [eval_eq_Fint] at hv'
      show Qr f.a f.b f.c v ≤ M
      rw [Qr_eq, hv']
      exact_mod_cast hmM
    have hcard := @card_repVecs f _ m hm1 hfinm
    have hset : repVecs f m = ↑((hS.toFinset.filter (goodVec f.a f.b f.c f.disc.natAbs)).filter
        (fun v => (Fint f.a f.b f.c v).toNat = m)) := by
      ext v
      simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have hrep : v ∈ repVecs f m ↔ Fint f.a f.b f.c v = m := by
        show f.eval (v 0) (v 1) = m ↔ _
        rw [eval_eq_Fint]
      rw [hrep]
      have hv0 := hnn v
      constructor
      · intro h
        refine ⟨⟨?_, ?_⟩, by omega⟩
        · rw [Qr_eq, h]; exact_mod_cast hmM
        · intro p hp hpv
          rw [h] at hpv
          have hpm : p ∣ m := by exact_mod_cast hpv
          exact (coprime_iff_noPrime m _ hN0).mp hmcop p hp hpm
      · rintro ⟨_, h⟩
        omega
    rw [← hcard, hset]
    exact Nat.card_eq_finsetCard _
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    obtain ⟨hvM, hvg⟩ := hv
    rw [Qr_eq] at hvM
    have hvM' : Fint f.a f.b f.c v ≤ M := by exact_mod_cast hvM
    have hv0 := hnn v
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Fint f.a f.b f.c v = m := ⟨(Fint f.a f.b f.c v).toNat, by omega⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    rw [hm, Int.toNat_natCast]
    have hcop : Nat.Coprime m f.disc.natAbs := by
      rw [coprime_iff_noPrime m _ hN0]
      intro p hp hpm
      apply hvg p hp
      rw [hm]
      exact_mod_cast hpm
    refine ⟨⟨?_, by omega⟩, hcop⟩
    by_contra h0
    have hm0 : m = 0 := by omega
    obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (show f.disc.natAbs ≠ 1 by omega)
    apply hvg p (Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩)
    rw [hm, hm0]
    simp

/-- Helper: the limit of Lemma 2.1 for $D < 0$ in the form with the explicit value of $w$ (arguments: `D` the fundamental
discriminant, `hD : D < 0`, the form `f` with `hf : f.disc = D` and `hpos : f.PosDef`). -/
theorem lemma21_neg_of (D : ℤ) [IsQuadDisc D] (hD : D < 0) (f : BinQF) (hf : f.disc = D) (hpos : f.PosDef) :
    Tendsto (fun M : ℕ => ((∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs), repOrbitCount f m : ℕ) : ℝ) / M)
      atTop (𝓝 (2 * Real.pi / ((if D = -3 then 6 else if D = -4 then 4 else 2 : ℕ) * Real.sqrt |(D : ℝ)|) *
        ∏ p ∈ D.natAbs.primeFactors, (1 - 1 / (p : ℝ)))) := by
  classical
  have hprimf : f.IsPrimitive := isPrimitive_of_fund (IsQuadDisc.fund (D := D)) hf
  let f' : PrimPosForm D := ⟨f, hf, hpos, hprimf⟩
  have hcardw : Nat.card (AutSL f) = if D = -3 then 6 else if D = -4 then 4 else 2 := by
    have := card_autSL (D := D) hD f'
    rw [torsionOrder_of_neg hD] at this
    exact this
  have hw0 : Nat.card (AutSL f) ≠ 0 := by rw [hcardw]; split_ifs <;> norm_num
  have : Finite (AutSL f) := Nat.finite_of_card_ne_zero hw0
  have ha : 0 < f.a := ((BinQF.posDef_iff_posDef' f).mp hpos).1
  have hdisc : f.disc < 0 := hf ▸ hD
  have h3 : 3 ≤ f.disc.natAbs := by rw [hf]; exact three_le_natAbs
  have hN : (f.disc.natAbs : ℤ) = 4 * f.a * f.c - f.b ^ 2 := by
    have h1 : ((f.disc.natAbs : ℕ) : ℤ) = - f.disc := by omega
    rw [h1]
    simp only [BinQF.disc]; ring
  have hprim : ∀ p ∈ f.disc.natAbs.primeFactors, ¬ ((p : ℤ) ∣ f.a ∧ (p : ℤ) ∣ f.b ∧ (p : ℤ) ∣ f.c) := by
    rintro p hp ⟨h1, h2, h3⟩
    have hu := hprimf (p : ℤ) h1 h2 h3
    have hp1 := (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [Int.isUnit_iff] at hu
    omega
  have hgood := good_count_tendsto f.a f.b f.c f.disc.natAbs ha hN (by omega) hprim
  have hnat := hgood.comp tendsto_natCast_atTop_atTop
  have hw : (Nat.card (AutSL f) : ℝ) ≠ 0 := by exact_mod_cast hw0
  have hlim := hnat.div_const (Nat.card (AutSL f) : ℝ)
  have key : ∀ M : ℕ, ((∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs), repOrbitCount f m : ℕ) : ℝ) / M =
      ((Nat.card {v : Fin 2 → ℤ // Qr f.a f.b f.c v ≤ (M : ℝ) ∧ goodVec f.a f.b f.c f.disc.natAbs v} : ℝ) / M) /
        (Nat.card (AutSL f) : ℝ) := by
    intro M
    have h1 := orbitCount_mul_card f D hD hf hpos M
    have h2 : (Nat.card (AutSL f) : ℝ) * ((∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs),
        repOrbitCount f m : ℕ) : ℝ) = (Nat.card {v : Fin 2 → ℤ // Qr f.a f.b f.c v ≤ (M : ℝ) ∧
        goodVec f.a f.b f.c f.disc.natAbs v} : ℝ) := by exact_mod_cast h1
    rw [← h2]
    field_simp
  have hlim' : Tendsto (fun M : ℕ => ((∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs),
      repOrbitCount f m : ℕ) : ℝ) / M) atTop
      (𝓝 ((2 * Real.pi / Real.sqrt f.disc.natAbs * ∏ p ∈ f.disc.natAbs.primeFactors, (1 - 1 / (p : ℝ))) /
        (Nat.card (AutSL f) : ℝ))) := by
    refine hlim.congr (fun M => ?_)
    rw [key M]
    rfl
  have hDabs : f.disc.natAbs = D.natAbs := by rw [hf]
  have hcastabs : ((D.natAbs : ℕ) : ℝ) = |(D : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hval : (2 * Real.pi / Real.sqrt f.disc.natAbs * ∏ p ∈ f.disc.natAbs.primeFactors, (1 - 1 / (p : ℝ))) /
        (Nat.card (AutSL f) : ℝ) =
      2 * Real.pi / (((if D = -3 then 6 else if D = -4 then 4 else 2 : ℕ) : ℝ) * Real.sqrt |(D : ℝ)|) *
        ∏ p ∈ D.natAbs.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [hDabs, hcastabs, hcardw]
    ring
  rw [hval] at hlim'
  exact hlim'

end Orbits

end Lemma21Aux


/-- **Cassels, Appendix B, §2, Lemma 2.1, case $D < 0$ (pp. 371-372), proved.** For a fundamental discriminant
$D < 0$ and every positive definite integral binary form $f$ of discriminant $D$,
$$\lim_{M \to \infty} M^{-1}A^*_f(M) = \frac{2\pi}{w\sqrt{|D|}}\prod_{p \mid D}\big(1 - p^{-1}\big),$$
$w$ = `properAutomorphCount D` the number of proper automorphs. Proof as in the book: $wA^*_f(M)$ is the number of integer
points $(x, y)$ in the ellipse $f \le M$ with $(f(x, y), D) = 1$ (`orbitCount_mul_card`, the group of proper automorphs
acting freely on nonzero vectors), and these points have density $\prod_{p \mid D}(1 - p^{-1})$ in the ellipse, whose
area is $2\pi M/\sqrt{|D|}$ (`good_count_tendsto`; the congruence condition (2.12) is, for $p \mid D$, the condition that a
nonzero linear form is nonzero mod $p$, `zero_count`). Argument: `D` the fundamental discriminant (`IsQuadDisc D`). -/
@[kb "cassels1978" "App. B, §2, Lemma 2.1 (D < 0), (2.10), pp. 371-372"]
theorem lemma_2_1_neg (D : ℤ) [IsQuadDisc D] : Lemma21Neg D := by
  intro f hf hpos
  have hD : D < 0 := by
    have := ((BinQF.posDef_iff_posDef' f).mp hpos).2
    rwa [hf] at this
  exact Lemma21Aux.lemma21_neg_of D hD f hf hpos

/-- **Cassels, Appendix B, §2, Corollary to Lemma 2.1 (p. 372), the partial summation step.** If
$M^{-1}A^*_f(M) \to c$ then the weighted average satisfies
$\lim_{s \to 1+}(s - 1)\sum_{m > 0,\ (m, D) = 1}a^*_f(m)\,m^{-s} = c$. Arguments: `f` the integral binary form, `c` the
limit, `h` the hypothesis $M^{-1}A^*_f(M) \to c$ (here `Lemma21Neg`/`Lemma21Pos` supply it; see the two corollaries
below). The proof is Mathlib's `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg` ("partial summation"). -/
@[kb "cassels1978" "App. B, §2, Cor. to Lemma 2.1 (partial summation), p. 372"]
theorem cor_lemma_2_1 (f : BinQF) {c : ℝ}
    (h : Tendsto (fun M : ℕ => (orbitCountSum f M : ℝ) / M) atTop (𝓝 c)) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' m : ℕ,
      (if 0 < m ∧ Nat.Coprime m f.disc.natAbs then (repOrbitCount f m : ℝ) else 0) * (m : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 c) := by
  classical
  set a : ℕ → ℝ := fun m => if 0 < m ∧ Nat.Coprime m f.disc.natAbs then (repOrbitCount f m : ℝ) else 0 with ha
  have hnn : ∀ n, 0 ≤ a n := by
    intro n; simp only [ha]; split_ifs <;> positivity
  have hsum : ∀ n, ∑ k ∈ Finset.Icc 1 n, a k = (orbitCountSum f n : ℝ) := by
    intro n
    unfold orbitCountSum
    rw [Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have : 0 < k := (Finset.mem_Icc.mp hk).1
    simp [ha, this]
  have h1 := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg a
    (by simpa [hsum] using h) hnn
  have h2 := (Complex.continuous_re.tendsto _).comp h1
  refine h2.congr (fun s => ?_)
  simp only [Function.comp_apply]
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (a n : ℂ)) (s : ℂ) n = ((a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, ha]
    · rw [LSeries.term_of_ne_zero hn.ne']
      rw [Complex.ofReal_mul, Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, div_eq_mul_inv]
  have hL : LSeries (fun n => (a n : ℂ)) (s : ℂ) = ((∑' n : ℕ, a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    exact tsum_congr hterm
  rw [hL]
  have : ((s : ℂ) - 1) * ((∑' n : ℕ, a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) =
      (((s - 1) * ∑' n : ℕ, a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- **Cassels, Appendix B, §2, Corollary to Lemma 2.1, $D < 0$ (p. 372, (2.12 bis)):** for a fundamental discriminant
$D < 0$ and every positive definite integral binary form $f$ of discriminant $D$,
$$\lim_{s \to 1+}(s - 1)\sum_{m > 0,\ (m, D) = 1}a^*_f(m)\,m^{-s} = \frac{2\pi}{w\sqrt{|D|}}\prod_{p \mid D}\big(1 - p^{-1}\big).$$
Arguments: `D` the fundamental discriminant (`IsQuadDisc D`), the form `f` with `hf : f.disc = D` and `hpos : f.PosDef`.
Unconditional: from `lemma_2_1_neg` by partial summation. -/
@[kb "cassels1978" "App. B, §2, Cor. to Lemma 2.1 (D < 0), (2.12 bis), p. 372"]
theorem cor_lemma_2_1_neg (D : ℤ) [IsQuadDisc D] (f : BinQF) (hf : f.disc = D) (hpos : f.PosDef) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' m : ℕ,
      (if 0 < m ∧ Nat.Coprime m f.disc.natAbs then (repOrbitCount f m : ℝ) else 0) * (m : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (2 * π / (properAutomorphCount D * Real.sqrt |(D : ℝ)|) * coprimeDensity D)) :=
  cor_lemma_2_1 f (lemma_2_1_neg D f hf hpos)

/-- **Cassels, Appendix B, §2, Corollary to Lemma 2.1, $D > 0$ (p. 372, (2.12 bis)):** given Lemma 2.1 for $D > 0$
(`Lemma21Pos D`), for every integral binary form $f$ of discriminant $D$ and the fundamental unit $\eta$ of norm $+1$,
$$\lim_{s \to 1+}(s - 1)\sum_{m > 0,\ (m, D) = 1}a^*_f(m)\,m^{-s} = \frac{\log\eta}{\sqrt D}\prod_{p \mid D}\big(1 - p^{-1}\big).$$
Arguments: `D` the fundamental discriminant, `h` the named statement `Lemma21Pos D`, `f` the form with
`hf : f.disc = D`, `η` with `hη : IsNormOneFundamentalUnit D η`. -/
@[kb "cassels1978" "App. B, §2, Cor. to Lemma 2.1 (D > 0), (2.12 bis), p. 372 (conditional on Lemma21Pos)"]
theorem cor_lemma_2_1_pos (D : ℤ) [IsQuadDisc D] (h : Lemma21Pos D) (f : BinQF) (hf : f.disc = D) (η : ℝ)
    (hη : IsNormOneFundamentalUnit D η) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' m : ℕ,
      (if 0 < m ∧ Nat.Coprime m f.disc.natAbs then (repOrbitCount f m : ℝ) else 0) * (m : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (Real.log η / Real.sqrt D * coprimeDensity D)) :=
  cor_lemma_2_1 f (h f hf η hη)

/-- **Cassels, Appendix B, §2, Lemma 2.2 (p. 372), as a named statement:** for a fundamental discriminant $D$ and every integer $m > 0$
prime to $D$ the total number of orbits of primitive representations of $m$ by (representatives of) all classes of forms is
$2^{\mu}$ if every prime divisor $p$ of $m$ has $(D/p) = +1$, where $\mu$ is the number of distinct prime divisors of $m$,
and $0$ otherwise (the first sentence of the lemma: $m$ is represented primitively only if every prime divisor $p$ of $m$
has $(D/p) = +1$).

A full proof needs the bijection of the book's proof: orbits of primitive representations of $m$ by all classes
$\leftrightarrow$ forms $mx^2 + uxy + vy^2$ with $u^2 - 4mv = D$ modulo $u \mapsto u + 2m$ (`exists_sq_mod_of_primRep`
in `PrimRep.lean` is the existence half), and the count $2^\mu$ of the solutions $u \bmod 2m$ of $u^2 \equiv D \pmod{4m}$
for $D$ fundamental, $m$ prime to $D$ (Hensel and the Chinese remainder theorem). For $D < 0$ the library's
`Binary.card_ideals_eq_sum_classes` and `Binary.dirichlet_sum_repNum` count representations through ideals instead.
Used only as a hypothesis, by `cor_lemma_2_2`. **Proved** in `AppB/Lemma22.lean` (`primRepOrbitCount_holds`, with the
unconditional corollary `cor_lemma_2_2_uncond`).

The classes are those of `Composition.FormClass D` (Ch. 14: proper classes of all primitive forms of discriminant $D$,
finite by `Composition.FormClass.finite`). For $D < 0$ this includes the negative definite classes, whose forms represent no
$m > 0$ and so contribute $0$; the positive definite ones are those counted by Cassels' $h(D)$.

Field `count`: the displayed count for each `m` (`0 < m`,
`Nat.Coprime m D.natAbs`), with the representative `Quotient.out c` of the class `c` (the count of a class does not
depend on the representative). Argument: `D` the fundamental discriminant (`IsQuadDisc D`). -/
@[kb "cassels1978" "App. B, §2, Lemma 2.2, p. 372 (named statement: the count 2^μ of orbits of primitive representations)"]
structure PrimRepOrbitCount (D : ℤ) [IsQuadDisc D] : Prop where
  count : ∀ m : ℕ, 0 < m → Nat.Coprime m D.natAbs →
    ∑ᶠ c : Composition.FormClass D, primRepOrbitCount (Quotient.out c).1 m =
      if ∀ p ∈ m.primeFactors, kroneckerChar D p = 1 then 2 ^ m.primeFactors.card else 0

/-- Helper: $2^{\omega(m)} \le d(m)$ ($\omega$ the number of distinct prime factors, $d$ the number of divisors). -/
private lemma two_pow_card_primeFactors_le' (m : ℕ) (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ (Nat.divisors m).card := by
  rw [Nat.card_divisors hm]
  calc 2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by simp
    _ ≤ _ := Finset.prod_le_prod (fun p hp => by
        have := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hm
          (Nat.dvd_of_mem_primeFactors hp)
        omega)

open scoped LSeries.notation in
/-- Helper: $\sum_n d(n)\,n^{-s}$ converges for real $s > 1$. -/
private lemma summable_card_divisors_rpow' {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-s)) := by
  have hz : LSeriesSummable (↗(ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (s : ℂ) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by simpa using hs)
  have h := ArithmeticFunction.LSeriesSummable_mul hz hz
  have h2 := (summable_norm_iff.mpr h)
  refine h2.congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.norm_term_eq, ite_eq_right hn.ne']
    have : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * ArithmeticFunction.zeta) n
        = ((Nat.divisors n).card : ℂ) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp [ArithmeticFunction.zeta_apply, (Nat.pos_of_mem_divisors hi).ne']
    rw [this]
    simp [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- Helper: a positive integer $m$ all of whose prime divisors $p$ have $\chi_D(p) = 1$ is prime to $D$ (since
$\chi_D(p) = 0$ for $p \mid D$). -/
theorem coprime_of_kroneckerChar_eq_one {D : ℤ} [IsQuadDisc D] {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p ∈ m.primeFactors, kroneckerChar D p = 1) : Nat.Coprime m D.natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpD
  have h1 := h p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩)
  have : NeZero D.natAbs := ⟨by have := three_le_natAbs (D := D); omega⟩
  have hnu : ¬ IsUnit (p : ZMod D.natAbs) := by
    rw [ZMod.isUnit_iff_coprime]
    intro hc
    have := Nat.eq_one_of_dvd_coprimes hc (dvd_refl p) hpD
    exact hp.one_lt.ne' this
  rw [MulChar.map_nonunit _ hnu] at h1
  exact zero_ne_one h1

/-- **Cassels, Appendix B, §2, Corollary to Lemma 2.2, (2.13) (pp. 372–373):** for real $s > 1$,
$$\sum_{f}{}^{*}\ \sum_{\substack{m > 0\\ (m, D) = 1}}a_f(m)\,m^{-s} = \prod_{(D/p) = +1}\frac{1 + p^{-s}}{1 - p^{-s}},$$
where $\sum^*_f$ runs over the classes of forms of discriminant $D$ (`Composition.FormClass D`, finite by `Composition.FormClass.finite`, with a representative
`Quotient.out c`), $a_f(m)$ = `primRepOrbitCount f m`, and the product is over all primes $p$ with the factor $1$ when
$(D/p) \ne +1$. (The right-hand side is lost in the machine-read text and reconstructed from the proof, p. 373.)
Conditional on Lemma 2.2's orbit count (`PrimRepOrbitCount D`); the rest of the proof is the Euler product
`euler_product_two_pow_omega`. Arguments: `D` the fundamental discriminant, `S` the named statement, `s` real with
`hs : 1 < s`. -/
@[kb "cassels1978" "App. B, §2, Cor. to Lemma 2.2, (2.13), pp. 372–373 (conditional on PrimRepOrbitCount)"]
theorem cor_lemma_2_2 (D : ℤ) [IsQuadDisc D] (S : PrimRepOrbitCount D) {s : ℝ} (hs : 1 < s) :
    ∑ᶠ c : Composition.FormClass D, ∑' m : ℕ,
        (if 0 < m ∧ Nat.Coprime m D.natAbs then (primRepOrbitCount (Quotient.out c).1 m : ℝ) * (m : ℝ) ^ (-s) else 0) =
      ∏' p : Nat.Primes, (if kroneckerChar D p = 1 then
        (1 + ((p : ℕ) : ℝ) ^ (-s)) / (1 - ((p : ℕ) : ℝ) ^ (-s)) else 1) := by
  classical
  have : Composition.NonzeroDisc D :=
    ⟨fun h => by have := (IsQuadDisc.fund (D := D)).1; have h3 := three_le_natAbs (D := D); rw [h] at h3; simp at h3,
      (IsQuadDisc.fund (D := D)).1⟩
  have := Composition.FormClass.finite (D := D)
  have : Fintype (Composition.FormClass D) := Fintype.ofFinite _
  rw [← euler_product_two_pow_omega D hs]
  set F : Composition.FormClass D → ℕ → ℝ := fun c m =>
    (if 0 < m ∧ Nat.Coprime m D.natAbs then (primRepOrbitCount (Quotient.out c).1 m : ℝ) * (m : ℝ) ^ (-s) else 0) with hF
  set G : ℕ → ℝ := fun m => (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, kroneckerChar D p = 1 then
        (2 : ℝ) ^ m.primeFactors.card * (m : ℝ) ^ (-s) else 0) with hG
  have hsumF : ∀ m, ∑ c : Composition.FormClass D, F c m = G m := by
    intro m
    by_cases hc : 0 < m ∧ Nat.Coprime m D.natAbs
    · have h1 := S.count m hc.1 hc.2
      rw [finsum_eq_sum_of_fintype] at h1
      have h1' : (∑ c : Composition.FormClass D, (primRepOrbitCount (Quotient.out c).1 m : ℝ)) =
          if ∀ p ∈ m.primeFactors, kroneckerChar D p = 1 then (2 : ℝ) ^ m.primeFactors.card else 0 := by
        have := congrArg (fun n : ℕ => (n : ℝ)) h1
        simp only [Nat.cast_sum] at this
        rw [this]
        split_ifs <;> simp
      have hsum1 : ∑ c : Composition.FormClass D, F c m = (∑ c : Composition.FormClass D, (primRepOrbitCount (Quotient.out c).1 m : ℝ)) * (m : ℝ) ^ (-s) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun c _ => ite_eq_left hc)
      rw [hsum1, h1']
      simp only [hG]
      by_cases hall : ∀ p ∈ m.primeFactors, kroneckerChar D p = 1
      · simp [hc.1.ne']
      · rw [ite_eq_right hall, ite_eq_right (fun h => hall h.2)]; simp
    · simp only [hF, hc, ite_false, Finset.sum_const_zero]
      simp only [hG]
      rw [ite_eq_right]
      rintro ⟨hm0, hall⟩
      exact hc ⟨Nat.pos_of_ne_zero hm0, coprime_of_kroneckerChar_eq_one hm0 hall⟩
  have hGs : Summable G := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (summable_card_divisors_rpow' hs)
    · simp only [hG]; split_ifs <;> positivity
    · by_cases hm : m = 0
      · subst hm; simp [hG]
      · have hnn : 0 ≤ (m : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg m) _
        have hle : (2 : ℝ) ^ m.primeFactors.card ≤ ((Nat.divisors m).card : ℝ) := by
          exact_mod_cast two_pow_card_primeFactors_le' m hm
        simp only [hG]
        split_ifs
        · exact mul_le_mul_of_nonneg_right hle hnn
        · positivity
  have hFs : ∀ c, Summable (F c) := by
    intro c
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hGs
    · simp only [hF]; split_ifs <;> positivity
    · rw [← hsumF m]
      refine Finset.single_le_sum (f := fun c => F c m) (fun c' _ => ?_) (Finset.mem_univ c)
      simp only [hF]; split_ifs <;> positivity
  rw [finsum_eq_sum_of_fintype]
  rw [← Summable.tsum_finsetSum (fun c _ => hFs c)]
  exact tsum_congr hsumF

end QuadFormsKB.Cassels
