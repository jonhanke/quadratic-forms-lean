/-
# Conway–Sloane 1988, §8, (12) at $s = 1$: the Hurwitz zeta function at $s = 0$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, p. 268. (Apostol, *Introduction to analytic number theory* (1976), Theorem 12.13.)

Mathlib's `HurwitzZeta.hurwitzZeta_neg_nat` gives the values of the Hurwitz zeta function $\zeta(s, x)$ at $s = -k$ only for
$k \ne 0$ (its docstring has a TODO for $k = 0$). This file fills that TODO: the formula
$\zeta(0, x) = -B_1(x) = \tfrac12 - x$ holds for $x \in (0, 1]$ (and **not** at $x = 0$, where
$\zeta(0, 0) = \zeta(0) = -\tfrac12$), which is what is needed for the case $s = 1$ of (12) with the representatives
$r = 1, \dots, N$ of $\mathbb Z/N$.

**Method.** Analytic continuation. For $x = a \in (0, 1]$, the function $\zeta(s, a) - \zeta(s)$ is entire (Mathlib), and for
$\operatorname{Re} s > 2$
$$\zeta(s, a) - \zeta(s) = (1 - a)\, s\,\zeta(s+1) + \sum_{n \ge 0}\bigl[(n+a)^{-s} - (n+1)^{-s} - (1-a)\,s\,(n+1)^{-s-1}\bigr].$$
The series converges locally uniformly (second-order Taylor bound, terms $O(n^{-3/2})$) to a holomorphic function on
$\operatorname{Re} s > -1/2$ vanishing at $s = 0$, and $s\zeta(s+1)$ extends to the entire function `zetaShift` with value $1$
at $0$. The identity theorem on the half plane gives $\zeta(0, a) - \zeta(0) = 1 - a$, i.e. $\zeta(0, a) = \tfrac12 - a$.

**Proves**
* `hurwitzZeta_zero_of_mem_Ioc`: for $a \in (0, 1]$, $\zeta(0, a) = \tfrac12 - a$.
* `hurwitzZeta_neg_nat'`: Mathlib's formula $\zeta(-k, x) = -\frac{1}{k+1}B_{k+1}(x)$ for **all** $k \in \mathbb N$
  (including $k = 0$) and $x \in (0, 1]$.
* `LFunction_one_sub_bernoulli'` ((12), all $s \ge 1$): for $\Phi : \mathbb Z/N \to \mathbb C$ and natural $s \ge 1$,
  $L(1 - s, \Phi) = -\frac{N^{s-1}}{s}\sum_{r=1}^{N}\Phi(r)B_s(r/N)$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.ZetaFormula

namespace QuadFormsKB.ConwaySloane.Mass

open Complex Set HurwitzZeta Filter
open scoped Real

/-- The derivative of $t \mapsto t^c$ on the positive reals, $c \in \mathbb C$ a constant. -/
theorem hasDerivAt_ofReal_cpow_const (c : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have h : HasDerivAt (fun z : ℂ => z ^ c) (c * (t : ℂ) ^ (c - 1)) (t : ℂ) :=
    (hasStrictDerivAt_cpow_const (Or.inl (by simpa using ht))).hasDerivAt
  exact h.comp_ofReal

/-- Second-order Taylor remainder bound for $t \mapsto t^c$ ($c \in \mathbb C$) on $[x, y] \subset (0, \infty)$: if
$\lVert c(c-1)t^{c-2}\rVert \le M$ on $[x, y]$ then
$\lVert x^c - y^c - c\,y^{c-1}(x - y)\rVert \le M (y-x)^2$. -/
theorem cpow_taylor_bound (c : ℂ) {x y M : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hM : ∀ t ∈ Icc x y, ‖c * (c - 1) * (t : ℂ) ^ (c - 2)‖ ≤ M) :
    ‖(x : ℂ) ^ c - (y : ℂ) ^ c - c * (y : ℂ) ^ (c - 1) * ((x : ℂ) - y)‖ ≤ M * (y - x) ^ 2 := by
  have hpos : ∀ t ∈ Icc x y, 0 < t := fun t ht => hx.trans_le ht.1
  -- step 1
  have step1 : ∀ t ∈ Icc x y, ‖c * (t : ℂ) ^ (c - 1) - c * (y : ℂ) ^ (c - 1)‖ ≤ M * (y - t) := by
    intro t ht
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => c * (u : ℂ) ^ (c - 1))
      (f' := fun u : ℝ => c * (c - 1) * (u : ℂ) ^ (c - 1 - 1)) (C := M) (a := t) (b := y)
      (fun u hu => by
        have := ((hasDerivAt_ofReal_cpow_const (c - 1) (lt_of_lt_of_le (hpos t ht) hu.1)).const_mul c)
        rw [← mul_assoc] at this
        exact this.hasDerivWithinAt)
      (fun u hu => by
        have := hM u ⟨ht.1.trans hu.1, hu.2.le⟩
        rwa [show c - 1 - 1 = c - 2 by ring])
      y ⟨ht.2, le_rfl⟩
    simpa [norm_sub_rev] using key
  have step2 := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun u : ℝ => (u : ℂ) ^ c - c * (y : ℂ) ^ (c - 1) * ((u : ℂ) - y))
    (f' := fun u : ℝ => c * (u : ℂ) ^ (c - 1) - c * (y : ℂ) ^ (c - 1)) (C := M * (y - x))
    (a := x) (b := y)
    (fun u hu => by
      have h1 := hasDerivAt_ofReal_cpow_const c (lt_of_lt_of_le hx hu.1)
      have h2 : HasDerivAt (fun u : ℝ => c * (y : ℂ) ^ (c - 1) * ((u : ℂ) - y))
          (c * (y : ℂ) ^ (c - 1)) u := by
        have := ((hasDerivAt_id (u : ℂ)).sub_const (y : ℂ)).const_mul (c * (y : ℂ) ^ (c - 1))
        simpa using this.comp_ofReal
      exact (h1.sub h2).hasDerivWithinAt)
    (fun u hu => by
      refine (step1 u ⟨hu.1, hu.2.le.trans le_rfl⟩).trans ?_
      have hM0 : 0 ≤ M := by
        have := hM x ⟨le_rfl, hxy⟩
        exact (norm_nonneg _).trans this
      exact mul_le_mul_of_nonneg_left (by linarith [hu.1]) hM0)
    y ⟨hxy, le_rfl⟩
  have e : (fun u : ℝ => (u : ℂ) ^ c - c * (y : ℂ) ^ (c - 1) * ((u : ℂ) - y)) y = (y : ℂ) ^ c := by
    simp
  simp only [sub_self, mul_zero, sub_zero] at step2
  rw [show M * (y - x) ^ 2 = M * (y - x) * (y - x) by ring]
  have e2 : (x : ℂ) ^ c - (y : ℂ) ^ c - c * (y : ℂ) ^ (c - 1) * ((x : ℂ) - y) =
      -((y : ℂ) ^ c - ((x : ℂ) ^ c - c * (y : ℂ) ^ (c - 1) * ((x : ℂ) - y))) := by ring
  rw [e2, norm_neg]
  exact step2

/-- The $n$-th term $(n+a)^{-s} - (n+1)^{-s} - (1-a)\,s\,(n+1)^{-s-1}$ of the remainder series (module docstring). -/
noncomputable def hzTerm (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n : ℝ) + a : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
    (1 - a) * s * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1)

/-- Bound of the terms on $\{\operatorname{Re}s > -1/2,\ \lVert s\rVert < K\}$ by $K(K+1)(n+a)^{-\operatorname{Re}s-2}$. -/
theorem hzTerm_bound {a : ℝ} (ha : a ∈ Ioc 0 1) (n : ℕ) {s : ℂ} (hs : -1 / 2 < s.re) {K : ℝ}
    (hK : ‖s‖ < K) :
    ‖hzTerm a n s‖ ≤ K * (K + 1) * ((n : ℝ) + a) ^ (-s.re - 2) := by
  have hx : 0 < (n : ℝ) + a := by have := ha.1; positivity
  have hxy : (n : ℝ) + a ≤ (n : ℝ) + 1 := by linarith [ha.2]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK.le
  have hb := cpow_taylor_bound (-s) hx hxy (M := K * (K + 1) * ((n : ℝ) + a) ^ (-s.re - 2)) (by
    intro t ht
    have ht0 : 0 < t := hx.trans_le ht.1
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    have e1 : ‖-s * (-s - 1)‖ ≤ K * (K + 1) := by
      rw [norm_mul, norm_neg]
      have : ‖-s - 1‖ ≤ K + 1 := by
        calc ‖-s - 1‖ ≤ ‖-s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ K + 1 := by simp; exact hK.le
      exact mul_le_mul hK.le this (norm_nonneg _) hK0
    have e2 : t ^ ((-s - 2).re) ≤ ((n : ℝ) + a) ^ (-s.re - 2) := by
      have : (-s - 2).re = -s.re - 2 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
    exact mul_le_mul e1 e2 (Real.rpow_nonneg ht0.le _) (by positivity))
  have h2 : ((n : ℝ) + 1 - ((n : ℝ) + a)) ^ 2 ≤ 1 := by
    have := ha.1; have := ha.2
    nlinarith
  have hM0 : 0 ≤ K * (K + 1) * ((n : ℝ) + a) ^ (-s.re - 2) := by positivity
  refine le_trans (le_of_eq ?_) (hb.trans (mul_le_of_le_one_right hM0 h2))
  congr 1
  unfold hzTerm
  push_cast
  ring

/-- Each term of the remainder series is entire in $s$. -/
theorem differentiable_hzTerm {a : ℝ} (ha : a ∈ Ioc 0 1) (n : ℕ) : Differentiable ℂ (hzTerm a n) := by
  have hx : (((n : ℝ) + a : ℝ) : ℂ) ≠ 0 := by
    have := ha.1
    exact_mod_cast (by positivity : ((n : ℝ) + a) ≠ 0)
  have hy : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
  unfold hzTerm
  refine Differentiable.sub (Differentiable.sub ?_ ?_) ?_
  · exact differentiable_id.neg.const_cpow (Or.inl hx)
  · exact differentiable_id.neg.const_cpow (Or.inl hy)
  · exact (differentiable_const _).mul differentiable_id |>.mul
      ((differentiable_id.neg.sub_const 1).const_cpow (Or.inl hy))

/-- The summable majorant of the remainder series on `{‖s‖ < K, -1/2 < re s}`. -/
noncomputable def hzMajorant (a K : ℝ) (n : ℕ) : ℝ :=
  K * (K + 1) * (((n : ℝ)) ^ (-3 / 2 : ℝ) + if n = 0 then a ^ (-K - 2) else 0)

/-- The majorant is summable (it is $O(n^{-3/2})$). -/
theorem summable_hzMajorant (a K : ℝ) : Summable (hzMajorant a K) := by
  unfold hzMajorant
  refine Summable.mul_left _ (Summable.add ?_ ?_)
  · exact Real.summable_nat_rpow.2 (by norm_num)
  · exact (hasSum_ite_eq 0 (a ^ (-K - 2))).summable.congr (fun n => by simp)

/-- Uniform bound of the terms by the summable majorant. -/
theorem hzTerm_le_majorant {a : ℝ} (ha : a ∈ Ioc 0 1) (n : ℕ) {s : ℂ} (hs : -1 / 2 < s.re) {K : ℝ}
    (hK : ‖s‖ < K) : ‖hzTerm a n s‖ ≤ hzMajorant a K n := by
  refine (hzTerm_bound ha n hs hK).trans ?_
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK.le
  have hre : s.re < K := (Complex.re_le_norm s).trans_lt hK
  unfold hzMajorant
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_add, ite_true]
    rw [Real.zero_rpow (by norm_num), zero_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_ge ha.1 ha.2 (by linarith)
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnx : (n : ℝ) ≤ n + a := by linarith [ha.1]
    simp only [hn.ne', ite_false, add_zero]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((n : ℝ) + a) ^ (-s.re - 2) ≤ (n : ℝ) ^ (-s.re - 2) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hnx (by linarith)
      _ ≤ (n : ℝ) ^ (-3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-- The remainder series is holomorphic on `{-1/2 < re s}`. -/
theorem differentiableOn_hzRemainder {a : ℝ} (ha : a ∈ Ioc 0 1) :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, hzTerm a n s) {s : ℂ | -1 / 2 < s.re} := by
  intro s₀ hs₀
  set K : ℝ := ‖s₀‖ + 1
  have hU : IsOpen {s : ℂ | -1 / 2 < s.re ∧ ‖s‖ < K} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have h := differentiableOn_tsum_of_summable_norm (summable_hzMajorant a K)
    (fun n => (differentiable_hzTerm ha n).differentiableOn) hU
    (fun n s hs => hzTerm_le_majorant ha n hs.1 hs.2)
  exact (h.differentiableAt (hU.mem_nhds ⟨hs₀, by simp [K]⟩)).differentiableWithinAt

/-- The entire function agreeing with `s ↦ s * ζ(s + 1)` for `s ≠ 0`, and equal to `1` at `s = 0`. -/
noncomputable def zetaShift (s : ℂ) : ℂ :=
  s * (riemannZeta (s + 1) - 1 / s / Gammaℝ (s + 1)) + (Gammaℝ (s + 1))⁻¹

/-- Value at $0$. -/
theorem zetaShift_zero : zetaShift 0 = 1 := by
  simp [zetaShift, Gammaℝ_one]

/-- For $s \ne 0$, `zetaShift s` $= s\,\zeta(s+1)$. -/
theorem zetaShift_of_ne_zero {s : ℂ} (hs : s ≠ 0) : zetaShift s = s * riemannZeta (s + 1) := by
  unfold zetaShift
  field_simp
  ring

/-- Differentiability is stable under the shift $t \mapsto t + 1$. -/
theorem differentiableAt_comp_add_one {g : ℂ → ℂ} {s : ℂ} (h : DifferentiableAt ℂ g (s + 1)) :
    DifferentiableAt ℂ (fun t => g (t + 1)) s :=
  DifferentiableAt.comp s (g := g) (f := fun t : ℂ => t + 1) h (differentiableAt_id.add_const 1)

/-- `zetaShift` is entire. -/
theorem differentiable_zetaShift : Differentiable ℂ zetaShift := by
  intro s
  have hg : DifferentiableAt ℂ (fun t : ℂ => (Gammaℝ (t + 1))⁻¹) s :=
    differentiableAt_comp_add_one (g := fun t => (Gammaℝ t)⁻¹) differentiable_Gammaℝ_inv.differentiableAt
  by_cases hs : s = 0
  · subst hs
    have h := differentiableAt_comp_add_one (s := 0)
      (g := fun s => hurwitzZeta (0 : UnitAddCircle) s - 1 / (s - 1) / Gammaℝ s)
      (by simpa using differentiableAt_hurwitzZeta_sub_one_div (0 : UnitAddCircle))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (s + 1) - 1 / s / Gammaℝ (s + 1)) 0 := by
      convert h using 2 with t
      simp [hurwitzZeta_zero]
    exact (differentiableAt_id.mul h2).add hg
  · have hs1 : s + 1 ≠ 1 := by simpa using hs
    have hz : DifferentiableAt ℂ (fun t : ℂ => riemannZeta (t + 1)) s :=
      differentiableAt_comp_add_one (g := riemannZeta) (differentiableAt_riemannZeta hs1)
    have : DifferentiableAt ℂ (fun t : ℂ => t * (riemannZeta (t + 1) -
        t⁻¹ * (Gammaℝ (t + 1))⁻¹) + (Gammaℝ (t + 1))⁻¹) s :=
      (differentiableAt_id.mul (hz.sub ((differentiableAt_inv hs).mul hg))).add hg
    convert this using 2 with t
    simp [zetaShift, div_eq_mul_inv]

/-- **The Hurwitz zeta function at $s = 0$.** For $a \in (0, 1]$, $\zeta(0, a) = \tfrac12 - a = -B_1(a)$. (False at $a = 0$,
where $\zeta(0, 0) = -\tfrac12$.) Proof: analytic continuation, see the module docstring. -/
@[kb "conwaysloane1988" "§8 (12), p. 268 (s = 1: the Hurwitz zeta function at 0)"]
theorem hurwitzZeta_zero_of_mem_Ioc {a : ℝ} (ha : a ∈ Ioc 0 1) :
    hurwitzZeta (a : UnitAddCircle) 0 = 1 / 2 - a := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2⟩
  set H : Set ℂ := {s : ℂ | -1 / 2 < s.re} with hH
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHc : IsPreconnected H := (convex_halfSpace_re_gt (-1 / 2)).isPreconnected
  let T : ℂ → ℂ := fun s => hurwitzZeta (a : UnitAddCircle) s - riemannZeta s
  let Rhs : ℂ → ℂ := fun s => (1 - (a : ℂ)) * zetaShift s + ∑' n : ℕ, hzTerm a n s
  have hT : Differentiable ℂ T := by
    have := differentiable_hurwitzZeta_sub_hurwitzZeta (a : UnitAddCircle) 0
    simpa [hurwitzZeta_zero, T] using this
  have hRhs : DifferentiableOn ℂ Rhs H :=
    ((differentiable_zetaShift.const_mul _).differentiableOn).add (differentiableOn_hzRemainder ha)
  have hev : T =ᶠ[nhds (3 : ℂ)] Rhs := by
    have hopen : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (3 : ℂ) ∈ {s : ℂ | 2 < s.re} by
      show (2 : ℝ) < (3 : ℂ).re; norm_num)] with s hs
    have hs : 2 < s.re := hs
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
    have h1 := hasSum_hurwitzZeta_of_one_lt_re haI (s := s) (by linarith)
    have h2 := hasSum_hurwitzZeta_of_one_lt_re (a := 1) ⟨zero_le_one, le_rfl⟩ (s := s) (by linarith)
    have h3 := hasSum_hurwitzZeta_of_one_lt_re (a := 1) ⟨zero_le_one, le_rfl⟩ (s := s + 1)
      (by simp; linarith)
    have e0 : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period (1 : ℝ)
    rw [e0, hurwitzZeta_zero] at h2 h3
    simp only [Complex.ofReal_one] at h2 h3
    have h4 := (h1.sub h2).sub (h3.mul_left ((1 - (a : ℂ)) * s))
    have h5 : HasSum (fun n : ℕ => hzTerm a n s)
        (hurwitzZeta (a : UnitAddCircle) s - riemannZeta s - (1 - (a : ℂ)) * s * riemannZeta (s + 1)) := by
      convert h4 using 1
      funext n
      unfold hzTerm
      rw [show -s - 1 = -(s + 1) by ring]
      simp only [cpow_neg]
      push_cast
      ring
    show hurwitzZeta (a : UnitAddCircle) s - riemannZeta s = _
    show _ = (1 - (a : ℂ)) * zetaShift s + ∑' n : ℕ, hzTerm a n s
    rw [h5.tsum_eq, zetaShift_of_ne_zero hs0]
    ring
  have heq := (hRhs.analyticOnNhd hHo).eqOn_of_preconnected_of_eventuallyEq
    (hT.differentiableOn.analyticOnNhd hHo) hHc (show (3 : ℂ) ∈ H by
      show (-1 / 2 : ℝ) < (3 : ℂ).re; norm_num) hev.symm
  have h0 := heq (show (0 : ℂ) ∈ H by show (-1 / 2 : ℝ) < (0 : ℂ).re; norm_num)
  have hR0 : ∑' n : ℕ, hzTerm a n 0 = 0 := by simp [hzTerm]
  simp only [Rhs, T, zetaShift_zero, hR0, riemannZeta_zero] at h0
  linear_combination -h0

/-- **Values of the Hurwitz zeta function at non-positive integers, all $k$.** For $k \in \mathbb N$ and $x \in (0, 1]$,
$\zeta(-k, x) = -\frac{1}{k+1}B_{k+1}(x)$. This is Mathlib's `hurwitzZeta_neg_nat` extended to $k = 0$
(there $k \ne 0$ is required but $x = 0$ is allowed; at $k = 0$ the formula fails at $x = 0$). -/
@[kb "conwaysloane1988" "§8 (12), p. 268 (Hurwitz zeta at non-positive integers)"]
theorem hurwitzZeta_neg_nat' (k : ℕ) {x : ℝ} (hx : x ∈ Ioc 0 1) :
    hurwitzZeta (x : UnitAddCircle) (-k) =
      -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, hurwitzZeta_zero_of_mem_Ioc hx]
    simp [Polynomial.bernoulli_one]
  · exact hurwitzZeta_neg_nat hk ⟨hx.1.le, hx.2⟩

/-- The formula of `hurwitzZeta_neg_nat'` at the point $r/N$ of the circle, $1 \le r \le N$ (for $r = N$ the point is $0$). -/
theorem hurwitzZeta_toAddCircle_natCast {N : ℕ} [NeZero N] (k : ℕ) {r : ℕ} (hr : 0 < r) (hrN : r ≤ N) :
    hurwitzZeta (ZMod.toAddCircle (r : ZMod N)) (-k) =
      -1 / ((k : ℂ) + 1) * (((Polynomial.bernoulli (k + 1)).eval ((r : ℚ) / N) : ℚ) : ℂ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hx : ((r : ℝ) / N) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hNr).mpr (Nat.cast_le.mpr hrN)⟩
  have hc : ZMod.toAddCircle (r : ZMod N) = (((r : ℝ) / N : ℝ) : UnitAddCircle) := by
    rcases eq_or_lt_of_le hrN with rfl | hlt
    · rw [ZMod.natCast_self, map_zero, div_self hNr.ne']
      exact (AddCircle.coe_period (1 : ℝ)).symm
    · rw [ZMod.toAddCircle_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  rw [hc, hurwitzZeta_neg_nat' k hx]
  congr 1
  have e : ((((r : ℝ) / N : ℝ)) : ℂ) = algebraMap ℚ ℂ ((r : ℚ) / N) := by
    simp only [eq_ratCast, Rat.cast_div, Rat.cast_natCast, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [e, Polynomial.eval_map, Polynomial.eval₂_hom]
  simp

/-- **(12), p. 268, all $s \ge 1$** (Apostol, Theorem 12.13): for a function $\Phi$ on $\mathbb Z/N$ and a natural number
$s \ge 1$,
$$L(1-s,\Phi) = -\frac{N^{s-1}}{s}\sum_{r=1}^{N}\Phi(r)\,B_s\!\Bigl(\frac rN\Bigr),$$
$B_s$ the Bernoulli polynomial. Extends `LFunction_one_sub_bernoulli` ($s \ge 2$) to $s = 1$, using
`hurwitzZeta_zero_of_mem_Ioc`; the representatives $r = 1, \dots, N$ (so $x = r/N \in (0, 1]$) matter. -/
@[kb "conwaysloane1988" "§8 (12), p. 268 (all s ≥ 1)"]
theorem LFunction_one_sub_bernoulli' {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) {s : ℕ} (hs : 1 ≤ s) :
    ZMod.LFunction Φ (1 - s) = -((N : ℂ) ^ (s - 1) / s) *
      ∑ r ∈ Finset.Icc 1 N, Φ r * (((Polynomial.bernoulli s).eval ((r : ℚ) / N) : ℚ) : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have e1 : (1 : ℂ) - ((k + 1 : ℕ) : ℂ) = -(k : ℂ) := by push_cast; ring
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [e1, ZMod.LFunction, neg_neg, Nat.add_sub_cancel, Finset.mul_sum, Finset.mul_sum]
  simp_rw [Complex.cpow_natCast]
  apply sum_zmod_eq_sum_Icc
  · have h := hurwitzZeta_toAddCircle_natCast (N := N) k hN le_rfl
    rw [ZMod.natCast_self] at h
    simp only [ZMod.natCast_self, h]
    push_cast
    ring
  · intro r hr hrN
    rw [hurwitzZeta_toAddCircle_natCast k hr hrN.le]
    push_cast
    ring

end QuadFormsKB.ConwaySloane.Mass
