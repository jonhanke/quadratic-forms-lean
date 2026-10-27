/-
# Local densities over $\mathbb{Q}$: per-place lower bounds (the local core of Thms 5.7, 5.9)

**Layer:** $\mathbb{Q}$ (integral forms `QuadForm ℤ n` at a prime $p$, $q = p$). The DVR versions (every prime of a
number field, dyadic included where the explicit dyadic results allow) are in `DVRLowerBounds.lean`.
**Depends on** `Table2.lean` (hence `Explicit.lean`: (5.6), (5.7), Lemma 3.8 corrected, Defs. 3.5–3.7, 5.1).

## The local inequalities used in the proofs of Thms 5.7 and 5.9 (Hanke 2004, §5, pp. 368–379)

Notation: $m = T'(m')^2$, $T'$ $p$-stable (Def. 3.6) at the primes of $m'$, $\nu = \nu_p = \mathrm{ord}_p(m')$,
$K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2T')$, $C = C_p(T') = \frac{q^{n-2}}{q^{n-2}-1}\frac{K}{\beta_p(T')}$ ((5.8)), $C' = \min\{1, C\}$
((5.11)); "good" means $p \nmid 2N$ (here: $Q$ has the counts of a unimodular diagonal form at odd $p$).

| | Paper (locator) | Local statement | Lean | Status |
|---|---|---|---|---|
| L1 | (5.6), p. 369 | $\beta_p(p^2m) \ge q^{2-n}\beta_p(m)$ | `localDensity_le_mul_sq` | done |
| L2 | (5.7), p. 369 | $\beta_p(T'p^{2\nu}) = K\sum_{i<\nu}q^{-(n-2)i} + \beta_p(T')q^{-(n-2)\nu}$ | `localDensity_pow_sq`; without isotropy `localDensity_pow_sq_of_stable` | done; *update*: no isotropy needed |
| L3 | (5.8), p. 369 | $\beta_p(T'p^{2\nu})/\beta_p(T') = C + (1-C)q^{-(n-2)\nu}$ | `localDensity_pow_sq_div` | done |
| L4 | p. 370 ("Lemma 3.8 tells us $C_\mathfrak{p} > 0$") | $p$ isotropic $\Rightarrow K > 0$, $C > 0$; $p$ anisotropic $\Rightarrow K = C = 0$ | `localConstC_pos`, `localConstC_eq_zero_of_anisotropic` | done |
| L5 | Remark 5.4.1(a), p. 370 | $\beta_p(T'p^{2\nu}) \to C\beta_p(T')$, monotonically; $= \beta_p(T')q^{-(n-2)\nu}$ at anisotropic $p$; $\beta^*_p(T'p^{2\nu}) = K$ ($\nu \ge 1$) | `tendsto_localDensity_pow_sq`, `localDensity_pow_sq_mono`, `localDensity_pow_sq_of_anisotropic`, `localDensityOf_nonZero_pow_sq` | done; *errata (candidates)*: normalization $q^{(n-2)\nu}$, and the $a^*_E$ limit is $(K/\beta^*_p(m))a^*_E(m)$ (`primitive_density_check`) |
| L6 | Remark 5.4.1(b), (5.9), Table 2, p. 370; (5.10), p. 371 | explicit $C$ at good $p$, $\mathrm{ord}_p T' \le 1$ | `table2_odd_unit`, `table2_even_unit`, `table2_ord_one`, `eq_5_10` | done |
| L7 | (5.11), p. 371 | $\beta_p(T'p^{2\nu}) \ge C'\beta_p(T')$, all $\nu \ge 0$ | `localDensity_pow_sq_ge`, `localDensity_pow_sq_div_ge` | done; needs $T'$ $p$-stable; also at anisotropic $p$ ($C' = 0$) |
| L8 | (5.12), p. 371 | $C' = 1 \iff n = 3 \lor p \mid T' \lor \Phi_n(p) = (-1)^n$ (good $p$, $\mathrm{ord}_p T' \le 1$) | `eq_5_12`, `localConstC'_diag_three`, `localConstC'_diag_ord_one`, `localConstC'_diag_odd_unit`, `localConstC'_diag_even_unit` | done; **erratum (candidate)**: printed with $(-1)^{n-1}$ and without $p \mid T'$ (`eq_5_12_printed_counterexample`) |
| L9 | (5.13), p. 373; Thm 5.7(a) first part, pp. 372, 374 | $\prod_{p\in S}q^{(n-2)\nu_p}\beta_p(m) \ge ((m')_{\mathrm{Iso}})^{n-2}\prod_{S\cap\mathrm{Iso}}C'_p\prod_S\beta_p(T')$ | `prod_localDensity_ge`, `prod_localDensity_ge_of_good` | done |
| L10 | proof of Thm 5.7, pp. 374–376 (good $p$) | $\beta_p(T')$ = local factor of $L(n/2,\Phi_n)^{-1}$ resp. $L((n-1)/2,\Phi_n)/\zeta(n-1)$; per prime $\beta_p(m) \ge$ that factor times $C'$, i.e. $\frac{X-1}{X+1}$ ($n$ even, $\Phi = -1$, $p \mid m$; $\frac{q-1}{q+1}$ for $n = 4$) resp. $\frac{1 - q^{-(n-1)/2}}{1 - q^{-(n-2)}}$ ($n$ odd, $\Phi = 1$) | `localDensity_diag_odd_unit`, `localDensity_diag_odd_ord_one`, `localDensity_diag_even_unit`, `localDensity_diag_even_ord_one`, `localDensity_ge_even`, `localDensity_ge_even_sharp`, `localDensity_ge_odd`, `localDensity_ge_three` | done; *update*: per prime $\frac{X-1}{X}$ |
| L11 | Thm 5.7(b), p. 373; (c), p. 373 (good part) | $\prod_{p\in S}\beta_p(m) \ge \prod_S(1-\chi(p)p^{-2})\prod_{p\in S, p\mid m, \chi(p)=-1}\frac{p-1}{p+1}$ ($n = 4$), and the analogues for $n$ even / odd | `prod_localDensity_ge_four`, `prod_localDensity_ge_even`, `prod_localDensity_ge_odd` | done |
| L12 | (5.14), p. 375 (factor at $p \mid N$) | $\frac{1-\Phi y}{1-y^2} \ge \frac{1}{1+y} \ge \frac{1}{1+q^{(n-1)/2}}$, $y = q^{-(n-1)/2}$ | `euler_factor_ge` | done; *update*: sharper $\frac1{1+y}$ |
| L13 | proof of Thm 5.9(b)(ii), p. 379 | $q^\nu\beta_p(Tp^{2\nu})/\beta_p(T) = 1 + C(q^\nu-1)$ ($n = 3$) and $1 + C(q^\nu - 1) - q^\nu \ge \frac{(C-1)(q-1)}{q}q^\nu$ for $C \ge 1$, $\nu \ge 1$ | `thm_5_9_local` | done |

Also used: $\beta_p$ depends only on the $p$-adic square class (`localDensity_mul_sq_of_not_dvd`), every $T$ is
$p$-stable at good $p$ (`isPStable_diag`), locally represented $\Rightarrow \beta_p > 0$
(`localDensity_pos_of_isLocallyRepresentedAt`), and equal counts give equal $\beta_p$, $C_p$
(`localDensity_congr_of_repCount`).

## How the paper's statements follow (not formalized)

Siegel's formula (5.3) $a_E(m) = \prod_v\beta_v(m)$ and (5.5) $\beta_\infty(T'(m')^2) = N(m')^{n-2}\beta_\infty(T')$ turn
L9 into (5.13): $a_E(m) \ge a_E(T')\,N((m')_{\mathrm{Iso}})^{n-2}\prod_{p\in S\cap\mathrm{Iso}}C'_p(T')$, and with L8
($C' = 1$ at good $p$ for $n = 3$) into the first part of Thm 5.7(a). Thm 5.7(b), (c) and the second part of (a) combine
L10–L12 over all good primes into $L$-values ($L(n/2,\Phi_n)$, $L((n-1)/2,\Phi_n)$, $L(1,\psi)$, $\zeta_F$), bound those
(Siegel's / effective $L(1,\psi_t)$ bounds; $E_n(X)$), and take the minimum over $T' \in B_{\mathbb T}$. Lemma 5.8 and the
rest of Thm 5.9 concern $a_H$ (cusp forms, Schulze-Pillot): global. Remark 5.7.1 (class number one: square classes
$t\mathbb{Z}^2$) is built into the $\mathbb{Q}$ layer. Remark 5.8.1 is a consequence of Lemma 5.8 (global).
-/
import QuadFormsKB.LocalDensity.Table2

namespace QuadFormsKB.LocalDensity

open QuadForm Filter Topology

variable {n : ℕ}

/-! ### The algebra of (5.7) ⟹ (5.8), (5.11) and Remark 5.4.1(a)

Write $Y = q^{n-2} > 1$, $K \ge 0$, $\beta_0 \ge 0$ and
$f(e) = K \sum_{i<e} Y^{-i} + \beta_0 / Y^e$ (the right side of (5.7)), and
$C = \frac{Y}{Y-1}\cdot\frac{K}{\beta_0}$ (the local constant). -/

section Algebra

/-- $\sum_{i<e} Y^{-i} = \frac{Y}{Y-1}\,(1 - Y^{-e})$ for $Y > 1$. -/
theorem geom_sum_inv_eq (Y : ℝ) (hY : 1 < Y) (e : ℕ) :
    ∑ i ∈ Finset.range e, Y⁻¹ ^ i = Y / (Y - 1) * (1 - 1 / Y ^ e) := by
  have hY0 : Y ≠ 0 := by positivity
  have hY1 : Y - 1 ≠ 0 := by linarith
  have h1 : Y⁻¹ ≠ 1 := by
    intro h; rw [inv_eq_one] at h; linarith
  have h2 : Y⁻¹ - 1 ≠ 0 := sub_ne_zero.2 h1
  have h3 : 1 - Y ≠ 0 := fun h => hY1 (by linarith)
  rw [geom_sum_eq h1, inv_pow]
  field_simp
  ring

/-- **(5.7) ⟹ (5.8)** (algebra): $f(e) = \beta_0\,(C + (1 - C)/Y^e)$ when $\beta_0 \ne 0$. -/
theorem pow_sq_closed_form (Y K β₀ : ℝ) (hY : 1 < Y) (hβ : β₀ ≠ 0) (e : ℕ) :
    K * ∑ i ∈ Finset.range e, Y⁻¹ ^ i + β₀ / Y ^ e =
      β₀ * (Y / (Y - 1) * (K / β₀) + (1 - Y / (Y - 1) * (K / β₀)) / Y ^ e) := by
  have hY0 : Y ≠ 0 := by positivity
  have hY1 : Y - 1 ≠ 0 := by linarith
  rw [geom_sum_inv_eq Y hY e]
  field_simp
  ring

/-- **(5.11)** (algebra): $f(e) \ge \min\{1, C\}\,\beta_0$. If $\beta_0 = 0$ then $C = 0$ (Lean's $x/0 = 0$) and
this is $f(e) \ge 0$. -/
theorem pow_sq_ge_min (Y K β₀ : ℝ) (hY : 1 < Y) (hK : 0 ≤ K) (hβ : 0 ≤ β₀) (e : ℕ) :
    min 1 (Y / (Y - 1) * (K / β₀)) * β₀ ≤ K * ∑ i ∈ Finset.range e, Y⁻¹ ^ i + β₀ / Y ^ e := by
  have hYp : 0 < Y := by linarith
  have hs : 0 ≤ ∑ i ∈ Finset.range e, Y⁻¹ ^ i :=
    Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.2 hYp.le) _
  rcases hβ.eq_or_lt with h0 | hpos
  · subst h0; simp only [mul_zero, zero_div]; positivity
  rw [pow_sq_closed_form Y K β₀ hY hpos.ne' e]
  set C := Y / (Y - 1) * (K / β₀)
  have ht0 : 0 < 1 / Y ^ e := by positivity
  have ht1 : 1 / Y ^ e ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hY.le
  have h1 := min_le_left 1 C
  have h2 := min_le_right 1 C
  have : min 1 C ≤ C + (1 - C) / Y ^ e := by
    rw [div_eq_mul_one_div (1 - C)]
    nlinarith
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left this hpos.le

/-- $C \ge 0$. -/
theorem localConst_alg_nonneg (Y K β₀ : ℝ) (hY : 1 < Y) (hK : 0 ≤ K) (hβ : 0 ≤ β₀) :
    0 ≤ Y / (Y - 1) * (K / β₀) := by
  have : 0 < Y - 1 := by linarith
  positivity

/-- **Remark 5.4.1(a)** (algebra): $f(e) \to C\beta_0$ as $e \to \infty$ when $\beta_0 \ne 0$. -/
theorem pow_sq_tendsto (Y K β₀ : ℝ) (hY : 1 < Y) (hβ : β₀ ≠ 0) :
    Tendsto (fun e : ℕ => K * ∑ i ∈ Finset.range e, Y⁻¹ ^ i + β₀ / Y ^ e) atTop
      (𝓝 (Y / (Y - 1) * (K / β₀) * β₀)) := by
  simp_rw [pow_sq_closed_form Y K β₀ hY hβ]
  have hY0 : 0 < Y := by linarith
  have h : Tendsto (fun e : ℕ => 1 / Y ^ e) atTop (𝓝 0) := by
    simp_rw [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hY0.le) (inv_lt_one_of_one_lt₀ hY)
  have := ((h.const_mul (1 - Y / (Y - 1) * (K / β₀))).const_add (Y / (Y - 1) * (K / β₀))).const_mul β₀
  simp only [mul_zero, add_zero] at this
  rw [show Y / (Y - 1) * (K / β₀) * β₀ = β₀ * (Y / (Y - 1) * (K / β₀)) by ring]
  refine this.congr fun e => ?_
  ring

/-- **Remark 5.4.1(a)** (algebra, monotonicity): $f$ is antitone if $C \le 1$ (and $\beta_0 \ge 0$). -/
theorem pow_sq_antitone (Y K β₀ : ℝ) (hY : 1 < Y) (hβ : 0 < β₀)
    (hC : Y / (Y - 1) * (K / β₀) ≤ 1) :
    Antitone (fun e : ℕ => K * ∑ i ∈ Finset.range e, Y⁻¹ ^ i + β₀ / Y ^ e) := by
  intro a b hab
  simp only [pow_sq_closed_form Y K β₀ hY hβ.ne']
  have hY0 : 0 < Y := by linarith
  have : 1 / Y ^ b ≤ 1 / Y ^ a :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hY.le hab)
  rw [div_eq_mul_one_div (1 - _), div_eq_mul_one_div (1 - _)]
  apply mul_le_mul_of_nonneg_left _ hβ.le
  nlinarith

/-- **Remark 5.4.1(a)** (algebra, monotonicity): $f$ is monotone if $C \ge 1$. -/
theorem pow_sq_monotone (Y K β₀ : ℝ) (hY : 1 < Y) (hβ : 0 < β₀)
    (hC : 1 ≤ Y / (Y - 1) * (K / β₀)) :
    Monotone (fun e : ℕ => K * ∑ i ∈ Finset.range e, Y⁻¹ ^ i + β₀ / Y ^ e) := by
  intro a b hab
  simp only [pow_sq_closed_form Y K β₀ hY hβ.ne']
  have hY0 : 0 < Y := by linarith
  have : 1 / Y ^ b ≤ 1 / Y ^ a :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hY.le hab)
  rw [div_eq_mul_one_div (1 - _), div_eq_mul_one_div (1 - _)]
  apply mul_le_mul_of_nonneg_left _ hβ.le
  nlinarith

end Algebra

/-! ### General local facts over $\mathbb{Q}$ (every prime $p$, no normal form) -/

section General

/-- $\beta_p(m) \ge 0$ for $Q$ nondegenerate and $m \ne 0$ (the limit is attained). -/
theorem localDensity_nonneg (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (m : ℤ) (hm : m ≠ 0) : 0 ≤ localDensity Q p m := by
  obtain ⟨k, hk⟩ := (localDensity_eventually_eq Q hQ p m hm).exists
  rw [← hk]; positivity

/-- **Locally represented ⟹ $\beta_p(m) > 0$** (Hanke 2004, Def. 5.2, p. 368, agrees with Def. 3.5): for $Q$
nondegenerate, $m \ne 0$ and $m$ locally represented at $p$ (Def. 3.5), $\beta_p(m) > 0$. -/
@[kb "hanke2004" "Def. 5.2, p. 368"]
theorem localDensity_pos_of_isLocallyRepresentedAt (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate)
    (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) (h : IsLocallyRepresentedAt Q p m) :
    0 < localDensity Q p m := by
  obtain ⟨k, hk, hpos⟩ := ((localDensity_eventually_eq Q hQ p m hm).and h).exists
  rw [← hk]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact div_pos (by exact_mod_cast hpos) (pow_pos hp _)

/-- $K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2T) \ge 0$ (for $n \ge 3$, by (5.6)). -/
theorem localDensityOf_nonZero_sq_nonneg (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (p : ℕ) [Fact p.Prime] (T : ℤ) (hT0 : T ≠ 0) :
    0 ≤ localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) := by
  rw [localDensityOf_nonZero_eq Q hQ p (by omega) T hT0, sub_nonneg]
  have h := localDensity_le_mul_sq Q hQ hn p T hT0
  have hp : (0 : ℝ) < (p : ℝ) ^ (n - 2) := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  rw [inv_mul_le_iff₀ hp]; exact h

/-- $q^{n-2} > 1$ for $n \ge 3$. -/
theorem one_lt_prime_pow_sub_two (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime] : 1 < (p : ℝ) ^ (n - 2) :=
  one_lt_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt) (by omega)

/-- **(5.7) without the isotropy hypothesis.** For $Q$ nondegenerate, $n \ne 1$, $T \ne 0$ and the
stability condition of Def. 3.6 at $T$,
$\beta_p(p^{2e}T) = K\sum_{i<e} p^{-(n-2)i} + \beta_p(T)/p^{(n-2)e}$, $K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2T)$.
*Update:* the paper derives (5.7) in case (3) ($p$ isotropic) of the proof of Thm 5.4; the
derivation uses only stability, and in the anisotropic case $K = 0$ (`localConstC_eq_zero_of_anisotropic`). -/
theorem localDensity_pow_sq_of_stable (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : n ≠ 1)
    (p : ℕ) [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ p T) (e : ℕ) :
    localDensity Q p ((p : ℤ) ^ (2 * e) * T) =
      localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) *
          ∑ i ∈ Finset.range e, ((p : ℝ) ^ (n - 2))⁻¹ ^ i +
        localDensity Q p T / ((p : ℝ) ^ (n - 2)) ^ e := by
  rw [localDensityOf_nonZero_eq Q hQ p hn T hT0]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [localDensity_pow_sq_step Q hQ p hn T hT0 hT.2 e, ih, Finset.sum_range_succ',
      Finset.sum_congr rfl (fun i _ => pow_succ ((p : ℝ) ^ (n - 2))⁻¹ i), ← Finset.sum_mul,
      pow_succ (_ ^ _) e, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

/-- The local constant in the algebraic shape of the section `Algebra`. -/
theorem localConstC_eq_alg (Q : QuadForm ℤ n) (p : ℕ) (T : ℤ) :
    localConstC Q p T = (p : ℝ) ^ (n - 2) / ((p : ℝ) ^ (n - 2) - 1) *
      (localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) / localDensity Q p T) :=
  rfl

/-- **The modified local constant** $C'_p(T') = \min\{1, C_p(T')\}$ (Hanke 2004, (5.11), p. 371). -/
noncomputable def localConstC' (Q : QuadForm ℤ n) (p : ℕ) (T : ℤ) : ℝ := min 1 (localConstC Q p T)

/-- $C_p(T') \ge 0$ (for $n \ge 3$, $T' \ne 0$). -/
theorem localConstC_nonneg (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (T : ℤ) (hT0 : T ≠ 0) : 0 ≤ localConstC Q p T :=
  localConst_alg_nonneg _ _ _ (one_lt_prime_pow_sub_two hn p)
    (localDensityOf_nonZero_sq_nonneg Q hQ hn p T hT0) (localDensity_nonneg Q hQ p T hT0)

/-- **(5.8)** (Hanke 2004, p. 369): for $Q$ nondegenerate, $n \ge 3$ and $T'$ $p$-stable ($T' \ne 0$),
$$\frac{\beta_p(T'p^{2\nu})}{\beta_p(T')} = \frac{(1 - C_p) + C_p\,q^{(n-2)\nu}}{q^{(n-2)\nu}}
  = C_p(T') + \frac{1 - C_p(T')}{q^{(n-2)\nu}}, \qquad q = p.$$
($\beta_p(T') > 0$ since $T'$ is locally represented.) *Update:* valid also when $p$ is anisotropic, where
$C_p(T') = 0$; the paper states it for $p$ isotropic (case (3) of the proof of Thm 5.4). -/
@[kb "hanke2004" "(5.8), p. 369"]
theorem localDensity_pow_sq_div (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T)
    (ν : ℕ) :
    localDensity Q p ((p : ℤ) ^ (2 * ν) * T) / localDensity Q p T =
      localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν) := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT0 hT.1
  rw [localDensity_pow_sq_of_stable Q hQ (by omega) p S₀ T hT0 hT ν,
    pow_sq_closed_form _ _ _ (one_lt_prime_pow_sub_two hn p) hβ.ne', localConstC_eq_alg, pow_mul]
  field_simp

/-- **$C_p(T') > 0$ at isotropic primes** (Hanke 2004, p. 370: "Lemma 3.8 tells us that $C_\mathfrak{p} > 0$"):
for $Q$ nondegenerate in local normal form, $n \ge 3$, $Q$ isotropic over $\mathbb{Q}_p$ and $T'$ $p$-stable,
$K > 0$ and hence $C_p(T') > 0$. *Proof:* if $K = 0$ then, by stabilization, the non-Zero-type counts at $p^2T'$
vanish for large $k$, so all solutions at $p^2T'$ are of Zero type, and the (corrected) Lemma 3.8 makes $Q$
anisotropic. -/
@[kb "hanke2004" "Proof of Thm 5.4, p. 370 (C_p > 0)"]
theorem localConstC_pos (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν)
    (hiso : Q.IsotropicIn ℚ_[p]) (T : ℤ) (hT0 : T ≠ 0)
    (hT : IsPStable Q (unimodularCoords ν) p T) : 0 < localConstC Q p T := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT0 hT.1
  have hK0 := localDensityOf_nonZero_sq_nonneg Q hQ hn p T hT0
  have hY := one_lt_prime_pow_sub_two hn p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hKpos : 0 < localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) := by
    refine lt_of_le_of_ne hK0 fun hK => ((anisotropic_iff_zeroType Q hQ p P ν hJ T hT).2 ?_) hiso
    have hpZ : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have h1 := localDensity_eventually_eq Q hQ p ((p : ℤ) ^ 2 * T) (mul_ne_zero hpZ hT0)
    have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually (localDensity_eventually_eq Q hQ p T hT0)
    filter_upwards [h1, h2, Filter.eventually_ge_atTop 2] with k hk1 hk2 hk
    have hs := normalized_split Q p (by omega) T k hk
    rw [hk1, hk2, ← sub_eq_iff_eq_add', ← localDensityOf_nonZero_eq Q hQ p (by omega) T hT0,
      ← hK, eq_comm, div_eq_zero_iff] at hs
    rcases hs with hs | hs
    · rw [repCount_eq_zero_add_nonZero Q p k]
      exact_mod_cast (show _ = 0 from by exact_mod_cast hs) ▸ (add_zero _)
    · exact absurd hs (pow_ne_zero _ hp0.ne')
  rw [localConstC_eq_alg]
  have : 0 < (p : ℝ) ^ (n - 2) - 1 := by linarith
  positivity

/-- **$C_p(T') = 0$ at anisotropic primes**: for $Q$ anisotropic over $\mathbb{Q}_p$ and $T'$ $p$-stable, $K = 0$
(Lemma 3.8: all solutions at $p^2T'$ are of Zero type), so $C_p(T') = 0$ and $C'_p(T') = 0$. -/
theorem localConstC_eq_zero_of_anisotropic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (S₀ : Finset (Fin n)) (haniso : ¬ Q.IsotropicIn ℚ_[p]) (T : ℤ) (hT : IsPStable Q S₀ p T) :
    localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) = 0 ∧
      localConstC Q p T = 0 := by
  have hK : localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) = 0 := by
    apply limUnder_eq_of_eventually
    filter_upwards [eventually_repCountOf_nonZero_eq_zero Q p haniso T hT.2] with k hk
    have := hk 1 le_rfl
    rw [mul_one] at this
    rw [this]; simp
  refine ⟨hK, ?_⟩
  rw [localConstC_eq_alg, hK]; simp

/-- **Remark 5.4.1(a), anisotropic case** (local form; Hanke 2004, p. 370): for $Q$ nondegenerate, $n \ge 3$,
anisotropic over $\mathbb{Q}_p$ and $T'$ $p$-stable, $\beta_p(T'p^{2\nu}) = \beta_p(T')/q^{(n-2)\nu}$ (equality in (5.6)
for every $\nu$). With Siegel's formula and $\beta_\infty(T'p^{2\nu}) = q^{(n-2)\nu}\beta_\infty(T')$ ((5.5)), this is the
printed $a_E(m\pi_\mathfrak{p}^{2\nu}) = a_E(m)$. -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370 (anisotropic)"]
theorem localDensity_pow_sq_of_anisotropic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (p : ℕ) [Fact p.Prime] (S₀ : Finset (Fin n)) (haniso : ¬ Q.IsotropicIn ℚ_[p]) (T : ℤ)
    (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T) (ν : ℕ) :
    localDensity Q p ((p : ℤ) ^ (2 * ν) * T) = localDensity Q p T / (p : ℝ) ^ ((n - 2) * ν) := by
  rw [localDensity_pow_sq_of_stable Q hQ (by omega) p S₀ T hT0 hT ν,
    (localConstC_eq_zero_of_anisotropic Q p S₀ haniso T hT).1, pow_mul]
  simp

/-- **(5.11)** (Hanke 2004, p. 371), multiplied out: for $Q$ nondegenerate, $n \ge 3$ and $T'$ $p$-stable,
$\beta_p(T'p^{2\nu}) \ge C'_p(T')\,\beta_p(T')$ for all $\nu \ge 0$, $C'_p = \min\{1, C_p\}$.
*Clarification:* (5.11) needs $T'$ $p$-stable (as in its context, Thm 5.4); it holds at anisotropic $p$ too
(there $C'_p = 0$). -/
@[kb "hanke2004" "(5.11), p. 371"]
theorem localDensity_pow_sq_ge (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T)
    (ν : ℕ) :
    localConstC' Q p T * localDensity Q p T ≤ localDensity Q p ((p : ℤ) ^ (2 * ν) * T) := by
  rw [localDensity_pow_sq_of_stable Q hQ (by omega) p S₀ T hT0 hT ν, localConstC',
    localConstC_eq_alg]
  exact pow_sq_ge_min _ _ _ (one_lt_prime_pow_sub_two hn p)
    (localDensityOf_nonZero_sq_nonneg Q hQ hn p T hT0) (localDensity_nonneg Q hQ p T hT0) ν

/-- **(5.11)** (Hanke 2004, p. 371), as printed:
$\dfrac{\beta_p(T'p^{2\nu})}{\beta_p(T')} \ge C'_p(T')$ for all $\nu \ge 0$ ($T'$ $p$-stable). -/
@[kb "hanke2004" "(5.11), p. 371"]
theorem localDensity_pow_sq_div_ge (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T)
    (ν : ℕ) :
    localConstC' Q p T ≤ localDensity Q p ((p : ℤ) ^ (2 * ν) * T) / localDensity Q p T := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT0 hT.1
  rw [le_div_iff₀ hβ]
  exact localDensity_pow_sq_ge Q hQ hn p S₀ T hT0 hT ν

/-- **Remark 5.4.1(a), isotropic case** (local form; Hanke 2004, p. 370): for $T'$ $p$-stable,
$\beta_p(T'p^{2\nu}) \to C_p(T')\,\beta_p(T')$ as $\nu \to \infty$. With Siegel's formula and (5.5) this gives
$a_E(m\pi^{2\nu})/q^{(n-2)\nu} \to C_\mathfrak{p}(m)\,a_E(m)$.
*Erratum (candidate; pending author):* the paper prints the normalization $q^\nu$; it is $q^{(n-2)\nu}$ (equal to
$q^\nu$ only for $n = 3$). -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370"]
theorem tendsto_localDensity_pow_sq (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T) :
    Tendsto (fun ν : ℕ => localDensity Q p ((p : ℤ) ^ (2 * ν) * T)) atTop
      (𝓝 (localConstC Q p T * localDensity Q p T)) := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT0 hT.1
  simp_rw [localDensity_pow_sq_of_stable Q hQ (by omega) p S₀ T hT0 hT]
  exact pow_sq_tendsto _ _ _ (one_lt_prime_pow_sub_two hn p) hβ.ne'

/-- **Remark 5.4.1(a), monotonicity** (Hanke 2004, p. 370): $\nu \mapsto \beta_p(T'p^{2\nu})$ is antitone when
$C_p(T') \le 1$ and monotone when $C_p(T') \ge 1$ ($T'$ $p$-stable). -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370 (monotonically)"]
theorem localDensity_pow_sq_mono (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T) :
    (localConstC Q p T ≤ 1 → Antitone fun ν : ℕ => localDensity Q p ((p : ℤ) ^ (2 * ν) * T)) ∧
    (1 ≤ localConstC Q p T → Monotone fun ν : ℕ => localDensity Q p ((p : ℤ) ^ (2 * ν) * T)) := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT0 hT.1
  simp_rw [localDensity_pow_sq_of_stable Q hQ (by omega) p S₀ T hT0 hT]
  exact ⟨pow_sq_antitone _ _ _ (one_lt_prime_pow_sub_two hn p) hβ,
    pow_sq_monotone _ _ _ (one_lt_prime_pow_sub_two hn p) hβ⟩

/-- **Remark 5.4.1(a), primitive densities** (local form; Hanke 2004, p. 370): for $T'$ $p$-stable and $\nu \ge 1$,
the primitive ($p$-primitive = non-Zero-type, Def. 5.3) density is constant:
$\beta^{*}_p(T'p^{2\nu}) = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(T'p^{2\nu}) = K$.
*Erratum (candidate; pending author):* the paper says $a^*_E(m\pi^{2\nu})/q^{\nu} \to a^*_E(m)$. By this lemma and
(5.4), $a^*_E(m\pi^{2\nu})/q^{(n-2)\nu} = (K/\beta^*_\mathfrak{p}(m))\,a^*_E(m)$ for every $\nu \ge 1$, and
$K \ne \beta^*_\mathfrak{p}(m)$ in general: for $Q = x^2 + y^2 + z^2$ (one class), $p = 3$, $m = 1$, the $3$-primitive
counts are $r^*(9^\nu) = 6, 24, 72, 216$ ($\nu = 0, \dots, 3$), so $r^*(9^\nu)/3^\nu = 6, 8, 8, 8$, with
$K/\beta^*_3(1) = (8/9)/(2/3) = 4/3$. -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370 (primitive)"]
theorem localDensityOf_nonZero_pow_sq (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (S₀ : Finset (Fin n)) (T : ℤ) (hT : IsPStable Q S₀ p T) (ν : ℕ) (hν : 1 ≤ ν) :
    localDensityOf Q p ((p : ℤ) ^ (2 * ν) * T) (fun k x => ¬ IsZeroType p k x) =
      localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) := by
  unfold localDensityOf Filter.limUnder
  congr 1
  refine Filter.map_congr ?_
  filter_upwards [hT.2] with k hk
  rw [hk ν hν]

/-! ### Square classes: $\beta_p(u^2m) = \beta_p(m)$ for $p \nmid u$ -/

/-- $Q(c\vec{x}) = c^2 Q(\vec{x})$. -/
theorem evalIn_smul (Q : QuadForm ℤ n) {A : Type*} [CommRing A] (c : A) (x : Fin n → A) :
    Q.evalIn A (c • x) = c ^ 2 * Q.evalIn A x := by
  simp only [evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **Counts depend only on the $p$-adic square class**: $r_{p^k}(u^2m) = r_{p^k}(m)$ for $p \nmid u$
(the map $\vec{x} \mapsto u\vec{x}$ is a bijection of $(\mathbb{Z}/p^k)^n$). -/
theorem repCount_mul_sq_of_not_dvd (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (k : ℕ) (m : ℤ) : repCount Q p k (u ^ 2 * m) = repCount Q p k m := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hcop : IsCoprime ((p : ℤ) ^ k) u := ((hpZ.coprime_iff_not_dvd).2 hu).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have hb : (b : ZMod (p ^ k)) * (u : ZMod (p ^ k)) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod (p ^ k))) hab
    push_cast at this
    rwa [← Nat.cast_pow, ZMod.natCast_self, mul_zero, zero_add] at this
  unfold repCount
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun x => (b : ZMod (p ^ k)) • x
      invFun := fun x => (u : ZMod (p ^ k)) • x
      left_inv := fun x => by simp only [smul_smul]; rw [mul_comm, hb, one_smul]
      right_inv := fun x => by simp only [smul_smul, hb, one_smul] } ?_)
  intro x
  simp only [Equiv.coe_fn_mk, evalIn_smul]
  push_cast
  constructor
  · intro h; rw [h, ← mul_assoc, ← mul_pow, hb]; ring
  · intro h
    calc Q.evalIn (ZMod (p ^ k)) x
        = ((u : ZMod (p ^ k)) * b) ^ 2 * Q.evalIn (ZMod (p ^ k)) x := by
          rw [mul_comm (u : ZMod (p ^ k)), hb]; ring
      _ = (u : ZMod (p ^ k)) ^ 2 * m := by rw [mul_pow, mul_assoc, h]

/-- **$\beta_p$ depends only on the $p$-adic square class** of $m$: $\beta_p(u^2m) = \beta_p(m)$ for $p \nmid u$. This
is what lets the paper write $\beta_\mathfrak{p}(m) = \beta_\mathfrak{p}(T'\pi^{2\nu_\mathfrak{p}})$ for $m = T'(m')^2$, $\nu_\mathfrak{p} =
\mathrm{ord}_\mathfrak{p}(m')$ (proofs of Thms 5.4, 5.7). -/
theorem localDensity_mul_sq_of_not_dvd (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (m : ℤ) : localDensity Q p (u ^ 2 * m) = localDensity Q p m := by
  unfold localDensity
  simp_rw [repCount_mul_sq_of_not_dvd Q p u hu]

/-! ### Transfer along equal counts -/

/-- **Equal counts ⟹ equal densities and local constants.** If $r_{p^k}(Q, m) = r_{p^k}(Q', m)$ for all $k, m$
(e.g. $Q'$ a diagonal form with the same counts, `exists_diag_same_counts`), then $\beta_p$, the non-Zero-type
densities $\beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2T)$ (Zero-type counts are counts of $Q$ at a lower level, map
$\pi_Z$) and $C_p$ agree. -/
theorem localDensity_congr_of_repCount (Q Q' : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (h : ∀ k m, repCount Q p k m = repCount Q' p k m) (T : ℤ) :
    localDensity Q p T = localDensity Q' p T ∧
      localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) =
        localDensityOf Q' p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) ∧
      localConstC Q p T = localConstC Q' p T := by
  have h1 : localDensity Q p T = localDensity Q' p T := by
    unfold localDensity; simp_rw [h]
  have h2 : localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) =
      localDensityOf Q' p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) := by
    unfold localDensityOf Filter.limUnder
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have e1 := repCount_eq_zero_add_nonZero Q p k ((p : ℤ) ^ 2 * T)
    have e2 := repCount_eq_zero_add_nonZero Q' p k ((p : ℤ) ^ 2 * T)
    rw [repCountZero_eq Q p _ k hk] at e1
    rw [repCountZero_eq Q' p _ k hk] at e2
    rw [h, h] at e1
    have : repCountOf Q p k ((p : ℤ) ^ 2 * T) (fun x => ¬ IsZeroType p k x) =
        repCountOf Q' p k ((p : ℤ) ^ 2 * T) (fun x => ¬ IsZeroType p k x) := by omega
    rw [this]
  refine ⟨h1, h2, ?_⟩
  rw [localConstC_eq_alg, localConstC_eq_alg, h1, h2]

end General

/-! ### Products over primes: the local part of (5.13) -/

section Products

/-- **Isotropic primes** (`Iso`, Hanke 2004, §5): $p$ is prime and $Q$ is isotropic over $\mathbb{Q}_p$ (Def. 3.7). -/
def IsIsotropicPrime (Q : QuadForm ℤ n) (p : ℕ) : Prop :=
  ∃ h : p.Prime, haveI := Fact.mk h; Q.IsotropicIn ℚ_[p]

theorem isIsotropicPrime_iff (Q : QuadForm ℤ n) (p : ℕ) [hp : Fact p.Prime] :
    IsIsotropicPrime Q p ↔ Q.IsotropicIn ℚ_[p] :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hp.out, h⟩⟩

/-- $p \nmid \prod_{p' \in S \setminus \{p\}} p'^{\nu(p')}$ for a set $S$ of primes. -/
theorem not_dvd_prod_erase (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) (p : ℕ)
    (hp : p.Prime) : ¬ (p : ℤ) ∣ ∏ p' ∈ S.erase p, (p' : ℤ) ^ ν p' := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [Prime.dvd_finsetProd_iff hpZ]
  rintro ⟨p', hp', hdvd⟩
  have h1 : p ∣ p' := by exact_mod_cast hpZ.dvd_of_dvd_pow hdvd
  have h2 := (Nat.prime_dvd_prime_iff_eq hp (hS p' (Finset.mem_of_mem_erase hp'))).1 h1
  exact (Finset.ne_of_mem_erase hp') h2.symm

/-- For $m = T'(m')^2$ with $m' = \prod_{p' \in S} p'^{\nu(p')}$ and $p \in S$:
$\beta_p(m) = \beta_p(T'p^{2\nu(p)})$ (the other primes are $p$-adic units). -/
theorem localDensity_prod_sq (Q : QuadForm ℤ n) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (ν : ℕ → ℕ) (T : ℤ) (p : ℕ) (hpS : p ∈ S) [Fact p.Prime] :
    localDensity Q p (T * (∏ p' ∈ S, (p' : ℤ) ^ ν p') ^ 2) =
      localDensity Q p ((p : ℤ) ^ (2 * ν p) * T) := by
  rw [← Finset.mul_prod_erase S _ hpS,
    show T * ((p : ℤ) ^ ν p * ∏ p' ∈ S.erase p, (p' : ℤ) ^ ν p') ^ 2 =
      (∏ p' ∈ S.erase p, (p' : ℤ) ^ ν p') ^ 2 * ((p : ℤ) ^ (2 * ν p) * T) by ring]
  exact localDensity_mul_sq_of_not_dvd Q p _ (not_dvd_prod_erase S hS ν p Fact.out) _

open Classical in
/-- **The local part of (5.13)** (Hanke 2004, p. 373; with (5.11) and Remark 5.4.1(a)). Let $Q$ be nondegenerate,
$n \ge 3$, $S$ a finite set of primes, $T' \ne 0$ $p$-stable for every $p \in S$, and
$m = T'(m')^2$ with $m' = \prod_{p \in S} p^{\nu_p}$ (so $m'$ is supported on $S \subseteq \mathrm{Stable}(T')$). Then
$$\prod_{p \in S} q^{(n-2)\nu_p}\,\beta_p(m) \;\ge\; \big((m')_{\mathrm{Iso}}\big)^{n-2}
  \prod_{p \in S \cap \mathrm{Iso}} C'_p(T') \prod_{p \in S} \beta_p(T'),$$
$(m')_{\mathrm{Iso}} = \prod_{p \in S \cap \mathrm{Iso}} p^{\nu_p}$. *How (5.13) follows (not formalized):* Siegel's
formula (5.3) $a_E(m) = \prod_v \beta_v(m)$, (5.5) $\beta_\infty(m) = \beta_\infty(T')\,N(m')^{n-2}$, and
$\beta_p(m) = \beta_p(T')$ for $p \notin S$ (`localDensity_mul_sq_of_not_dvd`) give
$a_E(m)/a_E(T') = \prod_{p \in S} q^{(n-2)\nu_p}\beta_p(m)/\beta_p(T')$. At anisotropic $p \in S$ the factor is exactly
$\beta_p(T')$ (`localDensity_pow_sq_of_anisotropic`). -/
@[kb "hanke2004" "(5.13), p. 373 (local part)"]
theorem prod_localDensity_ge (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0)
    (hT : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ S.filter (IsIsotropicPrime Q), localConstC' Q p T) * ∏ p ∈ S, localDensity Q p T ≤
      ∏ p ∈ S, (p : ℝ) ^ ((n - 2) * ν p) *
        localDensity Q p (T * (∏ p' ∈ S, (p' : ℤ) ^ ν p') ^ 2) := by
  have hL : (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ S.filter (IsIsotropicPrime Q), localConstC' Q p T) * ∏ p ∈ S, localDensity Q p T =
      ∏ p ∈ S, (if IsIsotropicPrime Q p then (p : ℝ) ^ ((n - 2) * ν p) * localConstC' Q p T else 1) *
        localDensity Q p T := by
    rw [Finset.prod_mul_distrib, ← Finset.prod_filter, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm (ν p)]
  rw [hL]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have : Fact p.Prime := ⟨hS p hp⟩
    have hC : 0 ≤ localConstC' Q p T :=
      le_min zero_le_one (localConstC_nonneg Q hQ hn p T hT0)
    have := localDensity_nonneg Q hQ p T hT0
    split_ifs <;> positivity
  · have : Fact p.Prime := ⟨hS p hp⟩
    rw [localDensity_prod_sq Q S hS ν T p hp]
    have hpp : (0 : ℝ) < (p : ℝ) ^ ((n - 2) * ν p) :=
      pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
    split_ifs with hiso
    · rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (localDensity_pow_sq_ge Q hQ hn p S₀ T hT0 (hT p hp) (ν p))
        hpp.le
    · rw [localDensity_pow_sq_of_anisotropic Q hQ hn p S₀
        (fun h => hiso ((isIsotropicPrime_iff Q p).2 h)) T hT0 (hT p hp), one_mul,
        mul_div_cancel₀ _ hpp.ne']

open Classical in
/-- **The local part of (5.13) with known good primes** (Hanke 2004, p. 373; first part of Thm 5.7(a)): as
`prod_localDensity_ge`, when $C'_p(T') = 1$ for the primes $p$ in a set $G$ (e.g. $p \nmid 2N$ when $n = 3$, by
(5.12); `localConstC'_diag_three`), the product of the $C'_p$ runs only over $p \in S \cap \mathrm{Iso}$, $p \notin G$.
For $n = 3$ and $G = \{p \nmid 2N\}$ this is the local content of $a_E(m) \ge \Lambda_3(T')\,N((m')_{\mathrm{Iso}})$ in
Thm 5.7(a); the paper's product is over $p \in S$, $p \mid N$, $p \in \mathrm{Iso}$ (at $p = 2 \nmid N$, $n = 3$ is
impossible). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (local part)"]
theorem prod_localDensity_ge_of_good (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0)
    (hT : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) (G : Finset ℕ)
    (hG : ∀ p ∈ S, p ∈ G → localConstC' Q p T = 1) :
    (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (· ∉ G), localConstC' Q p T) *
        ∏ p ∈ S, localDensity Q p T ≤
      ∏ p ∈ S, (p : ℝ) ^ ((n - 2) * ν p) *
        localDensity Q p (T * (∏ p' ∈ S, (p' : ℤ) ^ ν p') ^ 2) := by
  refine le_of_eq_of_le ?_ (prod_localDensity_ge Q hQ hn S hS S₀ T hT0 hT ν)
  congr 2
  have h1 : ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (· ∈ G), localConstC' Q p T = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    exact hG p hp.1.1 hp.2
  rw [← Finset.prod_filter_mul_prod_filter_not (S.filter (IsIsotropicPrime Q)) (· ∈ G), h1, one_mul]

end Products

/-! ### Good primes $p \nmid 2N$: explicit local factors

Here $Q = \langle a_0, \dots, a_{n-1}\rangle$ is diagonal with $p \nmid 2\prod_i a_i$ (a general form with $p \nmid 2N$
has the same counts as such a form, `exists_diag_same_counts`, and then the same $\beta_p$ and $C_p$,
`localDensity_congr_of_repCount`). $D = \prod_i a_i$, and $\Phi_n(p)$ is the character of p. 357:
$\Phi_n(p) = \left(\frac{(-1)^{n/2} D}{p}\right)$ for $n$ even, $\left(\frac{(-1)^{(n-1)/2} D T'}{p}\right)$ for $n$ odd. -/

section Good

/-- A diagonal form with nonzero coefficients is nondegenerate. -/
theorem nondegenerate_diag (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) : (QuadForm.diag a).Nondegenerate := by
  unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by have := ha i; omega

theorem ne_zero_of_not_dvd {p : ℕ} {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : a ≠ 0 := by
  rintro rfl; exact ha (dvd_zero _)

/-- **Every $T$ is $p$-stable at a good prime** (Def. 3.6; Remark 3.5.1 and Lemma 3.2): for a unimodular diagonal
form at odd $p$ and $n \ge 3$, every $T$ is locally represented, and the non-Zero-type counts at $p^{2\nu}T$,
$\nu \ge 1$, are all $p^{(n-1)(k-1)}\,r^{\mathrm{Good}}_p(0)$. -/
theorem isPStable_diag (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 3 ≤ n) (S₀ : Finset (Fin n)) (T : ℤ) :
    IsPStable (QuadForm.diag a) S₀ p T := by
  refine ⟨isLocallyRepresentedAt_of_good a hn p hp ha T, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk ν hν
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  rw [repCountOf_nonZero_diag_succ a p hp ha, repCountOf_nonZero_diag_succ a p hp ha]
  congr 1
  apply repCountOf_congr
  rw [intCast_zmod_pow_one_eq_zero.2, intCast_zmod_pow_one_eq_zero.2]
  · exact Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _
  · exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _

/-- $\mathrm{ord}_p(T) = 1$ from $p \mid T$, $p^2 \nmid T$. -/
theorem padicValInt_eq_one (p : ℕ) [Fact p.Prime] (T : ℤ) (h1 : (p : ℤ) ∣ T)
    (h2 : ¬ (p : ℤ) ^ 2 ∣ T) : padicValInt p T = 1 := by
  have hT0 : T ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have a1 := (padicValInt_dvd_iff (p := p) 1 T).1 (by simpa using h1)
  have a2 : ¬ 2 ≤ padicValInt p T := fun h => h2 ((padicValInt_dvd_iff 2 T).2 (Or.inr h))
  omega

/-- **Writing $m = p^{2e}T'$ with $\mathrm{ord}_p(T') \le 1$** (the choice of $T'$ in Thm 5.7). -/
theorem exists_pow_sq_mul (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ∃ e : ℕ, ∃ T : ℤ, m = (p : ℤ) ^ (2 * e) * T ∧ ¬ (p : ℤ) ^ 2 ∣ T := by
  induction h : m.natAbs using Nat.strong_induction_on generalizing m with
  | _ N ih =>
    by_cases hd : (p : ℤ) ^ 2 ∣ m
    · obtain ⟨m', rfl⟩ := hd
      have hp2 : (1 : ℕ) < ((p : ℤ) ^ 2).natAbs := by
        rw [Int.natAbs_pow, Int.natAbs_natCast]
        exact one_lt_pow₀ (Fact.out : p.Prime).one_lt two_ne_zero
      have hm' : m' ≠ 0 := by rintro rfl; simp at hm
      have hlt : m'.natAbs < N := by
        rw [← h, Int.natAbs_mul]
        exact lt_mul_left (Int.natAbs_pos.2 hm') hp2
      obtain ⟨e, T, rfl, hT⟩ := ih _ hlt m' hm' rfl
      exact ⟨e + 1, T, by ring, hT⟩
    · exact ⟨0, m, by simp, hd⟩

/-- $\Phi = \pm 1$ for a unit argument. -/
theorem legendreSym_sq_one_real (p : ℕ) [Fact p.Prime] (x : ℤ) (hx : ¬ (p : ℤ) ∣ x) :
    (legendreSym p x : ℝ) = 1 ∨ (legendreSym p x : ℝ) = -1 := by
  rcases legendreSym.eq_one_or_neg_one p (a := x) (by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]) with h | h <;> simp [h]

theorem not_dvd_sign_prod (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (ha : ∀ i, ¬ (p : ℤ) ∣ a i)
    (s : ℕ) : ¬ (p : ℤ) ∣ (-1) ^ s * ∏ i, a i := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact mul_ne_zero (by exact_mod_cast neg_one_pow_ne_zero_zmod p s)
    (by exact_mod_cast prod_ne_zero_zmod a p ha)

theorem not_dvd_sign_prod_mul (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (ha : ∀ i, ¬ (p : ℤ) ∣ a i)
    (s : ℕ) (T : ℤ) (hT : ¬ (p : ℤ) ∣ T) : ¬ (p : ℤ) ∣ (-1) ^ s * (∏ i, a i) * T := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  intro h
  rcases hpZ.dvd_or_dvd h with h | h
  · exact not_dvd_sign_prod a p ha s h
  · exact hT h

/-- **$\beta_p(T')$, $n$ odd, $p \nmid T'$** (Remark 3.4.1(a) with Table 1; the factor of
$L((n-1)/2, \Phi_n)/\zeta(n-1)$ in the proof of Thm 5.7): $\beta_p(T') = 1 + \Phi_n(p)\,p^{-(n-1)/2}$. -/
theorem localDensity_diag_odd_unit (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hodd : Odd n) (T : ℤ) (hT : ¬ (p : ℤ) ∣ T) :
    localDensity (QuadForm.diag a) p T =
      1 + (legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) : ℝ) / (p : ℝ) ^ ((n - 1) / 2) := by
  obtain ⟨j, rfl⟩ := hodd
  have hr := ((card_diag_mod_p a p hp ha (by omega) T hT).2 ⟨j, rfl⟩).2
  rw [localDensity_unit a p hp ha T hT]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [show 2 * j + 1 - 1 = 2 * j by omega, show 2 * j / 2 = j by omega] at hr ⊢
  have hr' : (repCount (QuadForm.diag a) p 1 T : ℝ) = (p : ℝ) ^ (2 * j) +
      (legendreSym p ((-1) ^ j * (∏ i, a i) * T) : ℝ) * (p : ℝ) ^ j := by
    exact_mod_cast hr
  rw [hr']
  field_simp
  ring

/-- **$\beta_p(T')$, $n$ odd, $\mathrm{ord}_p(T') = 1$**: $\beta_p(T') = 1 - p^{-(n-1)}$. -/
theorem localDensity_diag_odd_ord_one (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hodd : Odd n) (T : ℤ) (h1 : (p : ℤ) ∣ T)
    (h2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localDensity (QuadForm.diag a) p T = 1 - 1 / (p : ℝ) ^ (n - 1) := by
  have hr := ((card_diag_mod_p a p hp ha (by obtain ⟨j, rfl⟩ := hodd; omega) 1
    (by exact_mod_cast (Fact.out : p.Prime).not_dvd_one)).2 hodd).1
  rw [localDensity_diag_ord_one a p hp ha T (padicValInt_eq_one p T h1 h2), hr]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  push_cast
  field_simp

/-- **$\beta_p(T')$, $n$ even, $p \nmid T'$** (Remark 3.4.1(a) with Table 1; the factor of $L(n/2, \Phi_n)^{-1}$):
$\beta_p(T') = 1 - \Phi_n(p)\,p^{-n/2}$. -/
theorem localDensity_diag_even_unit (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 2 ≤ n) (heven : Even n) (T : ℤ) (hT : ¬ (p : ℤ) ∣ T) :
    localDensity (QuadForm.diag a) p T =
      1 - (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) : ℝ) / (p : ℝ) ^ (n / 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 2 := by obtain ⟨m, rfl⟩ := heven; exact ⟨m - 1, by omega⟩
  have hr := ((card_diag_mod_p a p hp ha (by omega) T hT).1 heven).2
  rw [localDensity_unit a p hp ha T hT]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [show (2 * j + 2) / 2 - 1 = j by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega] at hr
  have hr' : (repCount (QuadForm.diag a) p 1 T : ℝ) = (p : ℝ) ^ (2 * j + 1) -
      (legendreSym p ((-1) ^ ((2 * j + 2) / 2) * ∏ i, a i) : ℝ) * (p : ℝ) ^ j := by
    exact_mod_cast hr
  rw [hr', show 2 * j + 2 - 1 = 2 * j + 1 by omega, show (2 * j + 2) / 2 = j + 1 by omega]
  field_simp
  ring

/-- **$\beta_p(T')$, $n$ even, $\mathrm{ord}_p(T') = 1$** (the factor in the proof of Thm 5.7, p. 374):
$\beta_p(T') = (1 - \Phi_n(p)\,p^{-n/2})(1 + \Phi_n(p)\,p^{-(n-2)/2})
 = \dfrac{(p^{(n-2)/2} + \Phi_n(p))(p^{n/2} - \Phi_n(p))}{p^{n-1}}$. -/
theorem localDensity_diag_even_ord_one (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 2 ≤ n) (heven : Even n) (T : ℤ) (h1 : (p : ℤ) ∣ T)
    (h2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localDensity (QuadForm.diag a) p T =
      (1 - (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) : ℝ) / (p : ℝ) ^ (n / 2)) *
        (1 + (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) : ℝ) / (p : ℝ) ^ ((n - 2) / 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 2 := by obtain ⟨m, rfl⟩ := heven; exact ⟨m - 1, by omega⟩
  have hr := ((card_diag_mod_p a p hp ha (by omega) 1
    (by exact_mod_cast (Fact.out : p.Prime).not_dvd_one)).1 heven).1
  rw [localDensity_diag_ord_one a p hp ha T (padicValInt_eq_one p T h1 h2)]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [show (2 * j + 2) / 2 - 1 = j by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega] at hr
  have hc := legendreSym_sq_one_real p _ (not_dvd_sign_prod a p ha ((2 * j + 2) / 2))
  have hr' : (repCount (QuadForm.diag a) p 1 0 : ℝ) = (p : ℝ) ^ (2 * j + 1) +
      (legendreSym p ((-1) ^ ((2 * j + 2) / 2) * ∏ i, a i) : ℝ) * ((p : ℝ) - 1) * (p : ℝ) ^ j := by
    exact_mod_cast hr
  rw [hr', show 2 * j + 2 - 1 = 2 * j + 1 by omega, show (2 * j + 2) / 2 = j + 1 by omega,
    show (2 * j + 2 - 2) / 2 = j by omega]
  rw [show (2 * j + 2) / 2 = j + 1 by omega] at hc
  generalize (legendreSym p ((-1) ^ (j + 1) * ∏ i, a i) : ℝ) = c at hc ⊢
  field_simp
  rcases hc with rfl | rfl <;> ring

theorem three_le_prime_real (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : (3 : ℝ) ≤ p := by
  have := (Fact.out : p.Prime).two_le; exact_mod_cast (show 3 ≤ p by omega)

/-- **$C'_p(T')$, $\mathrm{ord}_p(T') = 1$** (Table 2): $C_p(T') = \frac{q^{n-2}}{q^{n-2}-1} > 1$, so $C'_p(T') = 1$. -/
theorem localConstC'_diag_ord_one (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 3 ≤ n) (T : ℤ) (h1 : (p : ℤ) ∣ T) (h2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localConstC' (QuadForm.diag a) p T = 1 := by
  rw [localConstC', table2_ord_one a p hp ha hn T (padicValInt_eq_one p T h1 h2)]
  have hY := one_lt_prime_pow_sub_two hn p
  refine min_eq_left ?_
  rw [le_div_iff₀ (by linarith)]; linarith

/-- **$C'_p(T')$, $n$ odd, $p \nmid T'$** (Table 2): $C'_p(T') = 1$ if $\Phi_n(p) = -1$, and if $\Phi_n(p) = 1$ then
$C'_p(T') = C_p(T') = \dfrac{1 - q^{-(n-1)/2}}{1 - q^{-(n-2)}}$, the local factor at $p$ of
$\zeta(n-2)/\zeta((n-1)/2)$ (proof of Thm 5.7(c), p. 375). -/
theorem localConstC'_diag_odd_unit (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 3 ≤ n) (hodd : Odd n) (T : ℤ) (hT : ¬ (p : ℤ) ∣ T) :
    (legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) = -1 →
      localConstC' (QuadForm.diag a) p T = 1) ∧
    (legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) = 1 →
      localConstC' (QuadForm.diag a) p T = localConstC (QuadForm.diag a) p T ∧
      localConstC (QuadForm.diag a) p T =
        (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2))) := by
  have hC := table2_odd_unit a p hp ha hn hodd T hT
  have hP := three_le_prime_real p hp
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 3 := by obtain ⟨m, rfl⟩ := hodd; exact ⟨m - 1, by omega⟩
  simp only [show 2 * j + 3 - 2 = 2 * j + 1 by omega, show (2 * j + 3 - 3) / 2 = j by omega,
    show (2 * j + 3 - 1) / 2 = j + 1 by omega] at hC ⊢
  have hYj : (1 : ℝ) ≤ (p : ℝ) ^ j := one_le_pow₀ (by linarith)
  have hY : (p : ℝ) ^ j * 3 ≤ (p : ℝ) ^ (2 * j + 1) := by
    rw [show 2 * j + 1 = j + j + 1 by ring, pow_succ, pow_add]; nlinarith
  refine ⟨fun hΦ => ?_, fun hΦ => ?_⟩
  · rw [hΦ] at hC; push_cast at hC
    rw [localConstC', hC]
    refine min_eq_left ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  · rw [hΦ] at hC; push_cast at hC
    refine ⟨min_eq_right ?_, ?_⟩
    · rw [hC, div_le_one (by linarith)]; linarith
    · rw [hC]
      have h0 : (p : ℝ) ≠ 0 := by linarith
      have h1 : (p : ℝ) ^ (2 * j + 1) - 1 ≠ 0 := by linarith
      have h2 : 1 - 1 / (p : ℝ) ^ (2 * j + 1) ≠ 0 := by
        have : 1 / (p : ℝ) ^ (2 * j + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        linarith
      field_simp
      ring

/-- **$C'_p(T')$, $n$ even, $p \nmid T'$** (Table 2): with $X = q^{(n-2)/2}$, $C_p(T') = X/(X - \Phi_n(p))$, so
$C'_p(T') = 1$ if $\Phi_n(p) = 1$ and $C'_p(T') = X/(X+1) = (1 - X^{-1})/(1 - X^{-2})$ (the local factor of
$\zeta(n-2)/\zeta((n-2)/2)$, proof of Thm 5.7, p. 374) if $\Phi_n(p) = -1$. -/
theorem localConstC'_diag_even_unit (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 4 ≤ n) (heven : Even n) (T : ℤ) (hT : ¬ (p : ℤ) ∣ T) :
    (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = 1 → localConstC' (QuadForm.diag a) p T = 1) ∧
    (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = -1 →
      localConstC' (QuadForm.diag a) p T =
        (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1)) := by
  have hC := table2_even_unit a p hp ha (by omega) heven T hT
  have hP := three_le_prime_real p hp
  have hX : (p : ℝ) ≤ (p : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
  refine ⟨fun hΦ => ?_, fun hΦ => ?_⟩
  · rw [hΦ] at hC; push_cast at hC
    rw [localConstC', hC]
    refine min_eq_left ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  · rw [hΦ] at hC; push_cast at hC
    rw [localConstC', hC, sub_neg_eq_add]
    refine min_eq_right ?_
    rw [div_le_one (by linarith)]; linarith

/-- **$\Phi_n(p)$** (Hanke 2004, p. 357) for $Q = \langle a_0, \dots, a_{n-1}\rangle$ at $p \nmid 2D$:
$\left(\frac{(-1)^{n/2}D}{p}\right)$ for $n$ even, $\left(\frac{(-1)^{(n-1)/2}DT'}{p}\right)$ for $n$ odd ($= 0$ if $p \mid T'$). -/
noncomputable def phiN (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (T : ℤ) : ℤ :=
  if Even n then legendreSym p ((-1) ^ (n / 2) * ∏ i, a i)
  else legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)

/-- **(5.12), corrected** (Hanke 2004, p. 371). For $n \ge 3$, $p \nmid 2N$ (a unimodular diagonal form at odd $p$)
and $\mathrm{ord}_p(T') \le 1$:
$$C'_p(T') = 1 \iff n = 3 \ \text{ or } \ p \mid T' \ \text{ or } \ \Phi_n(p) = (-1)^n;$$
equivalently, $C'_p(T') < 1 \iff n \ge 4,\ p \nmid T',\ \Phi_n(p) = (-1)^{n-1}$.
*Erratum (confirmed by the author, Jon Hanke, 2026-10-15):* the paper prints
"$C'_\mathfrak{p}(T') = 1 \iff n = 3$ or ($n \ge 4$, $\mathfrak{p} \nmid T'$, $\Phi_n(\mathfrak{p}) = (-1)^{n-1}$)", which gives the condition
for $C'_\mathfrak{p}(T') < 1$ (when $n \ge 4$). Counterexample to the printed form: $n = 4$, $Q = x_0^2 + x_1^2 + x_2^2 + x_3^2$,
$p = 3$, $T' = 1$: $\Phi_4(3) = \left(\frac{1}{3}\right) = 1 \ne (-1)^{3}$, yet $C_3(1) = 3/(3-1) = 3/2$ by Table 2, so
$C'_3(1) = 1$. (The later uses in the proof of Thm 5.7, "$C'_\mathfrak{p}(T') = 1$ unless $\mathfrak{p} \nmid T'$ and
$\Phi_n(\mathfrak{p}) = -1$" for $n$ even and "unless $n \ge 5$ and $\Phi_n(\mathfrak{p}) = 1$" for $n$ odd, agree with the
corrected form.) -/
@[kb "hanke2004" "(5.12), p. 371 (corrected)"]
theorem eq_5_12 (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ha : ∀ i, ¬ (p : ℤ) ∣ a i)
    (hn : 3 ≤ n) (T : ℤ) (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localConstC' (QuadForm.diag a) p T = 1 ↔ n = 3 ∨ (p : ℤ) ∣ T ∨ phiN a p T = (-1) ^ n := by
  by_cases hpT : (p : ℤ) ∣ T
  · exact ⟨fun _ => Or.inr (Or.inl hpT), fun _ => localConstC'_diag_ord_one a p hp ha hn T hpT hT2⟩
  have hP := three_le_prime_real p hp
  rcases Nat.even_or_odd n with he | ho
  · have hn4 : 4 ≤ n := by obtain ⟨m, rfl⟩ := he; omega
    have hn3 : n ≠ 3 := by omega
    have hpow : ((-1 : ℤ)) ^ n = 1 := he.neg_one_pow
    simp only [phiN, he, ite_true, hpow, hn3, hpT, false_or]
    obtain ⟨h1, h2⟩ := localConstC'_diag_even_unit a p hp ha hn4 he T hpT
    rcases legendreSym.eq_one_or_neg_one p (a := (-1) ^ (n / 2) * ∏ i, a i)
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_sign_prod a p ha _) with hΦ | hΦ
    · exact ⟨fun _ => hΦ, fun _ => h1 hΦ⟩
    · rw [h2 hΦ, hΦ]
      have hX : (p : ℝ) ≤ (p : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
      constructor
      · intro h
        rw [div_eq_one_iff_eq (by linarith)] at h; linarith
      · intro h; exact absurd h (by decide)
  · have hpow : ((-1 : ℤ)) ^ n = -1 := ho.neg_one_pow
    have hne : ¬ Even n := Nat.not_even_iff_odd.2 ho
    simp only [phiN, hne, ite_false, hpow, hpT, false_or]
    obtain ⟨h1, h2⟩ := localConstC'_diag_odd_unit a p hp ha hn ho T hpT
    rcases legendreSym.eq_one_or_neg_one p (a := (-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_sign_prod_mul a p ha _ T hpT)
      with hΦ | hΦ
    · obtain ⟨h21, h22⟩ := h2 hΦ
      rw [h21, h22, hΦ]
      constructor
      · intro h
        left
        by_contra h3
        have hn5 : 5 ≤ n := by obtain ⟨m, rfl⟩ := ho; omega
        have hA : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ ((n - 1) / 2) := pow_le_pow_right₀ (by linarith) (by omega)
        have hB : (p : ℝ) ^ ((n - 1) / 2) < (p : ℝ) ^ (n - 2) :=
          pow_lt_pow_right₀ (by linarith) (by omega)
        have hB0 : (0 : ℝ) < (p : ℝ) ^ ((n - 1) / 2) := by positivity
        rw [div_eq_one_iff_eq] at h
        · have : 1 / (p : ℝ) ^ (n - 2) < 1 / (p : ℝ) ^ ((n - 1) / 2) :=
            one_div_lt_one_div_of_lt hB0 hB
          linarith
        · have : 1 / (p : ℝ) ^ (n - 2) < 1 := by
            rw [div_lt_one (by positivity)]; nlinarith
          linarith
      · rintro (h | h)
        · subst h; norm_num
          have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
          linarith
        · exact absurd h (by decide)
    · exact ⟨fun _ => Or.inr hΦ, fun _ => h1 hΦ⟩

/-- **$C'_p(T') = 1$ for $n = 3$ at good primes** (Hanke 2004, (5.12), p. 371, and the first part of Thm 5.7(a):
"$C'_\mathfrak{p}(T') = 1$ for all $\mathfrak{p} \nmid N$ when $n = 3$"); $\mathrm{ord}_p(T') \le 1$. -/
@[kb "hanke2004" "(5.12), p. 371 (n = 3)"]
theorem localConstC'_diag_three (a : Fin 3 → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (T : ℤ) (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localConstC' (QuadForm.diag a) p T = 1 :=
  (eq_5_12 a p hp ha le_rfl T hT2).2 (Or.inl rfl)

/-- **Per-prime lower bound, $n$ even, $p \nmid 2N$, sharp form** (from the proof of Thm 5.7(b), (c),
pp. 374–375): as `localDensity_ge_even` with $\frac{X-1}{X}$ in place of $\frac{X-1}{X+1}$. The two cases are
$C'_p(T') = X/(X+1)$ ($p \nmid T'$, $\nu \ge 1$) and $\beta_p(T')/(1 - \Phi_n q^{-n/2}) = 1 - X^{-1}$ ($p \mid T'$), and
$\min\{X/(X+1), 1 - X^{-1}\} = 1 - X^{-1}$. -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (local factor at p ∤ 2N, n even; sharper)"]
theorem localDensity_ge_even_sharp (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 4 ≤ n) (heven : Even n) (m : ℤ) (hm : m ≠ 0) :
    (1 - (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) : ℝ) / (p : ℝ) ^ (n / 2)) *
        (if legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = -1 ∧ (p : ℤ) ∣ m then
          ((p : ℝ) ^ ((n - 2) / 2) - 1) / (p : ℝ) ^ ((n - 2) / 2) else 1) ≤
      localDensity (QuadForm.diag a) p m := by
  obtain ⟨e, T, rfl, hT2⟩ := exists_pow_sq_mul p m hm
  have hT0 : T ≠ 0 := by rintro rfl; simp at hm
  have hQ := nondegenerate_diag a (fun i => ne_zero_of_not_dvd (ha i))
  have hst := isPStable_diag a p hp ha (by omega) ∅ T
  have h511 := localDensity_pow_sq_ge (QuadForm.diag a) hQ (by omega) p ∅ T hT0 hst e
  have hP := three_le_prime_real p hp
  have hX : (p : ℝ) ≤ (p : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
  have hN : (p : ℝ) ≤ (p : ℝ) ^ (n / 2) := le_self_pow₀ (by linarith) (by omega)
  set X := (p : ℝ) ^ ((n - 2) / 2) with hXdef
  set N2 := (p : ℝ) ^ (n / 2)
  rcases legendreSym.eq_one_or_neg_one p (a := (-1) ^ (n / 2) * ∏ i, a i)
    (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_sign_prod a p ha _) with hΦ | hΦ
  · -- $\Phi_n(p) = 1$: $C'_p = 1$ and $\beta_p(T') \ge 1 - q^{-n/2}$
    have hif : ¬ (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = -1 ∧ (p : ℤ) ∣ (p : ℤ) ^ (2 * e) * T) := by
      rw [hΦ]; simp
    rw [if_neg hif, mul_one, hΦ]
    push_cast
    by_cases hpT : (p : ℤ) ∣ T
    · rw [localConstC'_diag_ord_one a p hp ha (by omega) T hpT hT2, one_mul,
        localDensity_diag_even_ord_one a p hp ha (by omega) heven T hpT hT2, hΦ] at h511
      push_cast at h511
      have h1 : 0 < 1 - 1 / N2 := by
        have : 1 / N2 < 1 := by rw [div_lt_one (by linarith)]; linarith
        linarith
      have h2 : 0 ≤ 1 / X := by positivity
      nlinarith
    · rw [(localConstC'_diag_even_unit a p hp ha hn heven T hpT).1 hΦ, one_mul,
        localDensity_diag_even_unit a p hp ha (by omega) heven T hpT, hΦ] at h511
      push_cast at h511
      exact h511
  · have hL : 0 < 1 - ((-1 : ℤ) : ℝ) / N2 := by
      have : 0 < 1 / N2 := by positivity
      push_cast; rw [neg_div]; linarith
    by_cases hpT : (p : ℤ) ∣ T
    · have hif : (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = -1 ∧ (p : ℤ) ∣ (p : ℤ) ^ (2 * e) * T) :=
        ⟨hΦ, Dvd.dvd.mul_left hpT _⟩
      rw [if_pos hif, hΦ]
      rw [localConstC'_diag_ord_one a p hp ha (by omega) T hpT hT2, one_mul,
        localDensity_diag_even_ord_one a p hp ha (by omega) heven T hpT hT2, hΦ] at h511
      refine le_trans ?_ h511
      apply mul_le_mul_of_nonneg_left _ hL.le
      have hX0 : 0 < X := by linarith
      have key : (X - 1) / X ≤ 1 + (-1) / X := by
        rw [div_le_iff₀ hX0]; field_simp; ring_nf; rfl
      rw [← hXdef]; push_cast; exact key
    · rw [(localConstC'_diag_even_unit a p hp ha hn heven T hpT).2 hΦ,
        localDensity_diag_even_unit a p hp ha (by omega) heven T hpT, hΦ] at h511
      split_ifs with hif
      · rw [hΦ]
        refine le_trans ?_ h511
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ hL.le
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
      · -- $p \nmid m$, so $\nu = 0$ and $m = T'$
        have he : e = 0 := by
          by_contra he
          exact hif ⟨hΦ, Dvd.dvd.mul_right (dvd_pow (dvd_refl _) (by omega)) _⟩
        subst he
        rw [mul_one, hΦ, mul_zero, pow_zero, one_mul,
          localDensity_diag_even_unit a p hp ha (by omega) heven T hpT, hΦ]


/-- **Per-prime lower bound, $n$ even, $p \nmid 2N$** (Hanke 2004, proof of Thm 5.7(b), (c), pp. 374–375). For
$n \ge 4$ even, a unimodular diagonal form at odd $p$, and any $m \ne 0$, with $X = q^{(n-2)/2}$:
$$\beta_p(m) \;\ge\; \Big(1 - \frac{\Phi_n(p)}{q^{n/2}}\Big) \cdot
  \begin{cases} \dfrac{X-1}{X+1} & \Phi_n(p) = -1 \text{ and } p \mid m,\\ 1 & \text{otherwise.}\end{cases}$$
The first factor is the local factor of $L(n/2, \Phi_n)^{-1}$; for $n = 4$ the second is $\frac{q-1}{q+1}$, the factor of
Thm 5.7(b). *Proof:* write $m = T'p^{2\nu}$ with $\mathrm{ord}_p(T') \le 1$; then $\beta_p(m) \ge C'_p(T')\beta_p(T')$ by (5.11),
with $\beta_p(T')$ from Table 1 and $C'_p(T')$ from Table 2. *Update (candidate; pending author):* the paper's proof combines
$\prod_{p \mid T'}(1 - q^{-(n-2)/2})$ (from $\beta_p(T')$) with $\prod_{p \mid m'} C'_p(T')$ (at $p \mid m'$ even when
$p \mid T'$, where $C'_p = 1$); per prime the bound is in fact $1 - X^{-1} = \frac{X-1}{X}$
(`localDensity_ge_even_sharp`), slightly better than $\frac{X-1}{X+1}$. -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (local factor at p ∤ 2N, n even)"]
theorem localDensity_ge_even (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 4 ≤ n) (heven : Even n) (m : ℤ) (hm : m ≠ 0) :
    (1 - (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) : ℝ) / (p : ℝ) ^ (n / 2)) *
        (if legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = -1 ∧ (p : ℤ) ∣ m then
          ((p : ℝ) ^ ((n - 2) / 2) - 1) / ((p : ℝ) ^ ((n - 2) / 2) + 1) else 1) ≤
      localDensity (QuadForm.diag a) p m := by
  refine le_trans ?_ (localDensity_ge_even_sharp a p hp ha hn heven m hm)
  have hP := three_le_prime_real p hp
  have hX : (p : ℝ) ≤ (p : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
  have hN : (p : ℝ) ≤ (p : ℝ) ^ (n / 2) := le_self_pow₀ (by linarith) (by omega)
  have hL : 0 ≤ 1 - (legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) : ℝ) / (p : ℝ) ^ (n / 2) := by
    rcases legendreSym_sq_one_real p _ (not_dvd_sign_prod a p ha (n / 2)) with h | h <;> rw [h]
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · have : 0 ≤ (1 : ℝ) / (p : ℝ) ^ (n / 2) := by positivity
      rw [neg_div]; linarith
  apply mul_le_mul_of_nonneg_left _ hL
  split_ifs
  · exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  · exact le_rfl

/-- **Per-prime lower bound, $n$ odd, $p \nmid 2N$** (Hanke 2004, proof of Thm 5.7(a), (c), pp. 375–376). For $n \ge 3$
odd, a unimodular diagonal form at odd $p$, $\mathrm{ord}_p(T') \le 1$ and $\nu \ge 0$, with
$\Phi = \Phi_n(p) = \left(\frac{(-1)^{(n-1)/2}DT'}{p}\right)$:
$$\beta_p(T'p^{2\nu}) \;\ge\; \beta_p(T') \cdot \begin{cases}\dfrac{1 - q^{-(n-1)/2}}{1 - q^{-(n-2)}} & p \nmid T',\ \Phi = 1,\\
1 & \text{otherwise,}\end{cases} \qquad
\beta_p(T') = \begin{cases} 1 - q^{-(n-1)} & p \mid T',\\ 1 + \Phi\, q^{-(n-1)/2} & p \nmid T'. \end{cases}$$
$\beta_p(T')$ is the local factor of $L((n-1)/2, \Phi_n)/\zeta(n-1)$ and the second factor that of
$\zeta(n-2)/\zeta((n-1)/2)$ (it is $1$ for $n = 3$). -/
@[kb "hanke2004" "Proof of Thm 5.7(a),(c), p. 375 (local factor at p ∤ 2N, n odd)"]
theorem localDensity_ge_odd (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 3 ≤ n) (hodd : Odd n) (T : ℤ) (hT0 : T ≠ 0)
    (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ) :
    (if (p : ℤ) ∣ T then 1 - 1 / (p : ℝ) ^ (n - 1) else
        1 + (legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) : ℝ) / (p : ℝ) ^ ((n - 1) / 2)) *
      (if ¬ (p : ℤ) ∣ T ∧ legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) = 1 then
        (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)) else 1) ≤
      localDensity (QuadForm.diag a) p ((p : ℤ) ^ (2 * ν) * T) := by
  have hQ := nondegenerate_diag a (fun i => ne_zero_of_not_dvd (ha i))
  have hst := isPStable_diag a p hp ha hn ∅ T
  have h511 := localDensity_pow_sq_ge (QuadForm.diag a) hQ hn p ∅ T hT0 hst ν
  refine le_trans (le_of_eq ?_) h511
  by_cases hpT : (p : ℤ) ∣ T
  · simp only [hpT, if_true, not_true_eq_false, false_and, if_false, mul_one]
    rw [localConstC'_diag_ord_one a p hp ha hn T hpT hT2, one_mul,
      localDensity_diag_odd_ord_one a p hp ha hodd T hpT hT2]
  · simp only [hpT, if_false, not_false_eq_true, true_and]
    rw [localDensity_diag_odd_unit a p hp ha hodd T hpT]
    obtain ⟨h1, h2⟩ := localConstC'_diag_odd_unit a p hp ha hn hodd T hpT
    rcases legendreSym.eq_one_or_neg_one p (a := (-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_sign_prod_mul a p ha _ T hpT)
      with hΦ | hΦ
    · rw [if_pos hΦ, (h2 hΦ).1, (h2 hΦ).2, mul_comm]
    · rw [if_neg (by rw [hΦ]; decide), h1 hΦ, one_mul, mul_one]

/-- **$n = 3$, $p \nmid 2N$:** $\beta_p(T'p^{2\nu}) \ge \beta_p(T')$ (Hanke 2004, first part of Thm 5.7(a), p. 374:
$C'_\mathfrak{p}(T') = 1$ for $\mathfrak{p} \nmid N$ when $n = 3$). -/
@[kb "hanke2004" "Thm 5.7(a), p. 374 (p ∤ 2N, n = 3)"]
theorem localDensity_ge_three (a : Fin 3 → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (T : ℤ) (hT0 : T ≠ 0) (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ) :
    localDensity (QuadForm.diag a) p T ≤ localDensity (QuadForm.diag a) p ((p : ℤ) ^ (2 * ν) * T) := by
  have hQ := nondegenerate_diag a (fun i => ne_zero_of_not_dvd (ha i))
  have h := localDensity_pow_sq_ge (QuadForm.diag a) hQ le_rfl p ∅ T hT0
    (isPStable_diag a p hp ha le_rfl ∅ T) ν
  rwa [localConstC'_diag_three a p hp ha T hT2, one_mul] at h

end Good

/-! ### Products over good primes: the local parts of Thm 5.7(b), (c)

$S$ is a finite set of odd primes at each of which $Q$ has the counts of a unimodular diagonal form
$\langle a_p \rangle$ (i.e. $p \nmid 2N$); $\Phi_n(p)$ is written with the Jacobi symbol $J(\cdot \mid p)$, which equals the
Legendre symbol at primes (`jacobiSym.legendreSym.to_jacobiSym`). -/

section GoodProducts

open Classical in
/-- **The local part of Thm 5.7(b)–(c) at good primes, $n$ even** (Hanke 2004, pp. 373–374). For $n \ge 4$ even,
$m \ne 0$, and $S$ as above, with $\Phi_n(p) = J((-1)^{n/2}D_p \mid p)$, $D_p = \prod_i a_{p,i}$, $X_p = p^{(n-2)/2}$:
$$\prod_{p \in S} \beta_p(m) \;\ge\; \prod_{p \in S}\Big(1 - \frac{\Phi_n(p)}{p^{n/2}}\Big)
  \prod_{\substack{p \in S,\ p \mid m\\ \Phi_n(p) = -1}} \frac{X_p - 1}{X_p + 1}.$$
*How Thm 5.7(b), (c) follow (not formalized):* with Siegel's formula (5.3), (5.5), the product of the first factors
over all $p \nmid N$ is $L(n/2, \Phi_n)^{-1}$ up to the finitely many $p \mid N$, and
$\prod_p \frac{X_p - 1}{X_p + 1} \ge \zeta(n-2)/\zeta((n-2)/2)^2$; at $p \mid N$ one uses (5.11) and (5.13). -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (local part at p ∤ 2N, n even)"]
theorem prod_localDensity_ge_even (Q : QuadForm ℤ n) (hn : 4 ≤ n) (heven : Even n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (a : ℕ → Fin n → ℤ)
    (ha : ∀ p ∈ S, ∀ i, ¬ (p : ℤ) ∣ a p i)
    (hQa : ∀ p ∈ S, ∀ k m, repCount Q p k m = repCount (QuadForm.diag (a p)) p k m)
    (m : ℤ) (hm : m ≠ 0) :
    (∏ p ∈ S, (1 - (jacobiSym ((-1) ^ (n / 2) * ∏ i, a p i) p : ℝ) / (p : ℝ) ^ (n / 2))) *
        ∏ p ∈ S.filter (fun p => jacobiSym ((-1) ^ (n / 2) * ∏ i, a p i) p = -1 ∧ (p : ℤ) ∣ m),
          (((p : ℝ) ^ ((n - 2) / 2) - 1) / ((p : ℝ) ^ ((n - 2) / 2) + 1)) ≤
      ∏ p ∈ S, localDensity Q p m := by
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have : Fact p.Prime := ⟨(hS p hp).1⟩
    have hP := three_le_prime_real p (hS p hp).2
    have hX : (p : ℝ) ≤ (p : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
    have hN : (p : ℝ) ≤ (p : ℝ) ^ (n / 2) := le_self_pow₀ (by linarith) (by omega)
    have hJ : (jacobiSym ((-1) ^ (n / 2) * ∏ i, a p i) p : ℝ) ≤ 1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      rcases legendreSym_sq_one_real p _ (not_dvd_sign_prod (a p) p (ha p hp) (n / 2)) with h | h
      · rw [h]
      · rw [h]; norm_num
    have : (jacobiSym ((-1) ^ (n / 2) * ∏ i, a p i) p : ℝ) / (p : ℝ) ^ (n / 2) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    apply mul_nonneg (by linarith)
    split_ifs
    · exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  · have : Fact p.Prime := ⟨(hS p hp).1⟩
    rw [(localDensity_congr_of_repCount Q (QuadForm.diag (a p)) p (hQa p hp) m).1]
    have h := localDensity_ge_even (a p) p (hS p hp).2 (ha p hp) hn heven m hm
    simp only [jacobiSym.legendreSym.to_jacobiSym] at h
    exact h

open Classical in
/-- **The local part of Thm 5.7(b) at good primes** (Hanke 2004, p. 373, $n = 4$): with
$\chi(p) = J(D_p \mid p)$ (the character of $Q$ at $p \nmid 2N$, $D_p = \prod_i a_{p,i}$),
$$\prod_{p \in S} \beta_p(m) \;\ge\; \prod_{p \in S}\Big(1 - \frac{\chi(p)}{p^{2}}\Big)
  \prod_{\substack{p \in S,\ p \mid m\\ \chi(p) = -1}} \frac{p - 1}{p + 1}.$$
The first product is the part at $p \in S$ of $L_F(2, \chi)^{-1}$; the second is the factor
$\prod_{p \mid m,\ p \nmid N,\ \chi(p) = -1} \frac{q-1}{q+1}$ of Thm 5.7(b). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (local part at p ∤ 2N)"]
theorem prod_localDensity_ge_four (Q : QuadForm ℤ 4) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (a : ℕ → Fin 4 → ℤ) (ha : ∀ p ∈ S, ∀ i, ¬ (p : ℤ) ∣ a p i)
    (hQa : ∀ p ∈ S, ∀ k m, repCount Q p k m = repCount (QuadForm.diag (a p)) p k m)
    (m : ℤ) (hm : m ≠ 0) :
    (∏ p ∈ S, (1 - (jacobiSym (∏ i, a p i) p : ℝ) / (p : ℝ) ^ 2)) *
        ∏ p ∈ S.filter (fun p => jacobiSym (∏ i, a p i) p = -1 ∧ (p : ℤ) ∣ m),
          (((p : ℝ) - 1) / ((p : ℝ) + 1)) ≤
      ∏ p ∈ S, localDensity Q p m := by
  have h := prod_localDensity_ge_even Q le_rfl (by decide) S hS a ha hQa m hm
  simp only [show (4 : ℕ) / 2 = 2 from rfl, show (4 - 2) / 2 = 1 from rfl, pow_one, neg_one_sq,
    one_mul] at h
  exact h

open Classical in
/-- **The local part of Thm 5.7(a) (second part) and (c) at good primes, $n$ odd** (Hanke 2004, pp. 375–376).
For $n \ge 3$ odd, $S$ as above, $T' \ne 0$ with $\mathrm{ord}_p(T') \le 1$ for $p \in S$, and
$m = T'(m')^2$, $m' = \prod_{p \in S} p^{\nu_p}$:
$$\prod_{p \in S} \beta_p(m) \;\ge\; \prod_{p \in S} \beta_p(T') \prod_{\substack{p \in S,\ p \nmid T'\\ \Phi_n(p) = 1}}
  \frac{1 - p^{-(n-1)/2}}{1 - p^{-(n-2)}},$$
$\Phi_n(p) = J((-1)^{(n-1)/2}D_pT' \mid p)$, and $\beta_p(T') = 1 + \Phi_n(p)p^{-(n-1)/2}$ ($p \nmid T'$),
$1 - p^{-(n-1)}$ ($p \mid T'$) (`localDensity_diag_odd_unit`, `localDensity_diag_odd_ord_one`): the local factors of
$L((n-1)/2, \Phi_n)/\zeta(n-1)$ and of $\zeta(n-2)/\zeta((n-1)/2)$ in (5.14) and in the proof of Thm 5.7(c).
For $n = 3$ the second product is $1$ ($C'_p = 1$). -/
@[kb "hanke2004" "Thm 5.7(a),(c), pp. 375-376 (local part at p ∤ 2N, n odd)"]
theorem prod_localDensity_ge_odd (Q : QuadForm ℤ n) (hn : 3 ≤ n) (hodd : Odd n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (a : ℕ → Fin n → ℤ)
    (ha : ∀ p ∈ S, ∀ i, ¬ (p : ℤ) ∣ a p i)
    (hQa : ∀ p ∈ S, ∀ k m, repCount Q p k m = repCount (QuadForm.diag (a p)) p k m)
    (T : ℤ) (hT0 : T ≠ 0) (hT2 : ∀ p ∈ S, ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    (∏ p ∈ S, localDensity Q p T) *
        ∏ p ∈ S.filter (fun p : ℕ => ¬ (p : ℤ) ∣ T ∧
            jacobiSym ((-1) ^ ((n - 1) / 2) * (∏ i, a p i) * T) p = 1),
          ((1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2))) ≤
      ∏ p ∈ S, localDensity Q p (T * (∏ p' ∈ S, (p' : ℤ) ^ ν p') ^ 2) := by
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have : Fact p.Prime := ⟨(hS p hp).1⟩
    have hP := three_le_prime_real p (hS p hp).2
    have hQ := nondegenerate_diag (a p) (fun i => ne_zero_of_not_dvd (ha p hp i))
    rw [(localDensity_congr_of_repCount Q (QuadForm.diag (a p)) p (hQa p hp) T).1]
    have := localDensity_nonneg _ hQ p T hT0
    have h1 : 1 / (p : ℝ) ^ (n - 2) < 1 := by
      rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by linarith) (by omega)
    have h2 : 1 / (p : ℝ) ^ ((n - 1) / 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith)
    split_ifs
    · exact mul_nonneg this (div_nonneg (by linarith) (by linarith))
    · simpa using this
  · have : Fact p.Prime := ⟨(hS p hp).1⟩
    rw [localDensity_prod_sq Q S (fun p hp => (hS p hp).1) ν T p hp,
      (localDensity_congr_of_repCount Q (QuadForm.diag (a p)) p (hQa p hp) _).1,
      (localDensity_congr_of_repCount Q (QuadForm.diag (a p)) p (hQa p hp) _).1]
    have h := localDensity_ge_odd (a p) p (hS p hp).2 (ha p hp) hn hodd T hT0 (hT2 p hp) (ν p)
    simp only [jacobiSym.legendreSym.to_jacobiSym] at h
    refine le_trans (le_of_eq ?_) h
    by_cases hpT : (p : ℤ) ∣ T
    · simp only [hpT, not_true_eq_false, false_and, if_false, if_true, mul_one]
      exact localDensity_diag_odd_ord_one (a p) p (hS p hp).2 (ha p hp) hodd T hpT (hT2 p hp)
    · simp only [hpT, not_false_eq_true, true_and, if_false]
      rw [localDensity_diag_odd_unit (a p) p (hS p hp).2 (ha p hp) hodd T hpT,
        jacobiSym.legendreSym.to_jacobiSym]

end GoodProducts

/-! ### Theorem 5.9 and the Euler factors at $p \mid N$: the local inequalities -/

section Thm59

/-- **The local inequality in the proof of Thm 5.9(b)(ii)** (Hanke 2004, p. 379): for $n = 3$, $T$ $p$-stable and
$C = C_p(T) \ge 1$ (which holds at the primes of $\tilde m_2$ when $\tilde T$ is of exceptional type, Lemma 5.8(d)) and
$\nu \ge 1$, the normalized ratio $q^{\nu}\beta_p(Tp^{2\nu})/\beta_p(T) = 1 + C(q^\nu - 1)$ (by (5.8)) satisfies
$$1 + C\,(q^\nu - 1) - q^\nu = (C - 1)(q^\nu - 1) \;\ge\; \frac{(C-1)(q-1)}{q}\, q^\nu,$$
with equality iff $C = 1$ or $\nu = 1$. In the paper these are the second and third lines of the chain
$a_E(\tilde T_ip^{2\nu}) + a_H(\tilde T_ip^{2\nu}) \ge \dots$ (after $|a_H(\tilde T_i)| \le a_E(\tilde T_i)$, Lemma 5.8(a)). -/
@[kb "hanke2004" "Proof of Thm 5.9(b)(ii), p. 379 (local inequality)"]
theorem thm_5_9_local (Q : QuadForm ℤ 3) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (S₀ : Finset (Fin 3)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T)
    (hC : 1 ≤ localConstC Q p T) (ν : ℕ) (hν : 1 ≤ ν) :
    (p : ℝ) ^ ν * (localDensity Q p ((p : ℤ) ^ (2 * ν) * T) / localDensity Q p T) =
        1 + localConstC Q p T * ((p : ℝ) ^ ν - 1) ∧
      (localConstC Q p T - 1) * ((p : ℝ) - 1) / p * (p : ℝ) ^ ν ≤
        1 + localConstC Q p T * ((p : ℝ) ^ ν - 1) - (p : ℝ) ^ ν ∧
      ((localConstC Q p T - 1) * ((p : ℝ) - 1) / p * (p : ℝ) ^ ν =
          1 + localConstC Q p T * ((p : ℝ) ^ ν - 1) - (p : ℝ) ^ ν ↔
        localConstC Q p T = 1 ∨ ν = 1) := by
  have h58 := localDensity_pow_sq_div Q hQ le_rfl p S₀ T hT0 hT ν
  simp only [show 3 - 2 = 1 by rfl, one_mul] at h58
  set C := localConstC Q p T
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hpν : (p : ℝ) ^ ν ≠ 0 := pow_ne_zero _ (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [h58]; field_simp; ring
  · -- $(q^\nu - 1) \ge (q - 1) q^{\nu - 1}$
    obtain ⟨μ, rfl⟩ : ∃ μ, ν = μ + 1 := ⟨ν - 1, by omega⟩
    have hμ : (1 : ℝ) ≤ (p : ℝ) ^ μ := one_le_pow₀ (by linarith)
    have : ((p : ℝ) - 1) / p * (p : ℝ) ^ (μ + 1) = ((p : ℝ) - 1) * (p : ℝ) ^ μ := by
      rw [pow_succ]; field_simp
    rw [mul_div_assoc, mul_assoc, this, pow_succ]
    nlinarith
  · obtain ⟨μ, rfl⟩ : ∃ μ, ν = μ + 1 := ⟨ν - 1, by omega⟩
    have : ((p : ℝ) - 1) / p * (p : ℝ) ^ (μ + 1) = ((p : ℝ) - 1) * (p : ℝ) ^ μ := by
      rw [pow_succ]; field_simp
    rw [mul_div_assoc, mul_assoc, this, pow_succ]
    constructor
    · intro h
      have h' : (C - 1) * ((p : ℝ) ^ μ - 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.1 h' with h1 | h1
      · left; linarith
      · right
        by_contra hμ
        have hμ0 : μ ≠ 0 := by omega
        have := (pow_eq_one_iff_of_nonneg (by linarith : (0 : ℝ) ≤ p) hμ0).1 (by linarith)
        linarith
    · rintro (h | h)
      · rw [h]; ring
      · obtain rfl : μ = 0 := by omega
        ring

/-- **The Euler factor at $p \mid N$ in (5.14)** (Hanke 2004, p. 375; used in $\hat\Lambda_3$ of Thm 5.7(a) and in
$\hat B_n$ of Thm 5.7(c), $n$ odd). For $q \ge 2$, $y = q^{-(n-1)/2}$ and $\Phi \in \{-1, 0, 1\}$:
$$\frac{1 - \Phi y}{1 - y^2} \;\ge\; \frac{1}{1 + y} \;\ge\; \frac{1}{1 + q^{(n-1)/2}}$$
(here $k = (n-1)/2 \ge 1$).
The paper uses the weaker bound $\beta_\mathfrak{p}(T')/(1 + q^{(n-1)/2})$ at $\mathfrak{p} \mid N$.
*Update (candidate; pending author):* $1/(1 + q^{-(n-1)/2})$ is the sharp bound; the printed one is valid but loses a
factor $q^{(n-1)/2}$ at each $\mathfrak{p} \mid N$ (possibly a sign typo in the exponent). -/
@[kb "hanke2004" "(5.14), p. 375 (Euler factor at p | N)"]
theorem euler_factor_ge (q : ℝ) (hq : 2 ≤ q) (k : ℕ) (hk : 1 ≤ k) (Φ : ℝ)
    (hΦ : Φ = -1 ∨ Φ = 0 ∨ Φ = 1) :
    1 / (1 + q ^ k) ≤ 1 / (1 + 1 / q ^ k) ∧
      1 / (1 + 1 / q ^ k) ≤ (1 - Φ / q ^ k) / (1 - (1 / q ^ k) ^ 2) := by
  have hqk : q ≤ q ^ k := le_self_pow₀ (by linarith) (by omega)
  have hy0 : 0 < 1 / q ^ k := by positivity
  have hy1 : 1 / q ^ k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  rw [div_eq_mul_one_div Φ]
  set y := 1 / q ^ k with hy
  have hqy : q ^ k * y = 1 := by rw [hy]; field_simp
  refine ⟨?_, ?_⟩
  · apply one_div_le_one_div_of_le (by linarith)
    nlinarith
  · rw [div_le_div_iff₀ (by linarith) (by nlinarith)]
    rcases hΦ with rfl | rfl | rfl <;> nlinarith

end Thm59

/-! ### Checks of the errata candidates -/

section Checks

/-- **(5.12) as printed fails** (counterexample for the erratum at `eq_5_12`): for $Q = x_0^2 + x_1^2 + x_2^2 + x_3^2$,
$p = 3$, $T' = 1$, $C'_3(1) = 1$, but the printed right side
"$n = 3$ or ($n \ge 4$, $p \nmid T'$, $\Phi_4(3) = (-1)^{n-1}$)" is false ($\Phi_4(3) = (\frac{1}{3}) = 1$). -/
theorem eq_5_12_printed_counterexample :
    localConstC' (QuadForm.diag ![(1 : ℤ), 1, 1, 1]) 3 1 = 1 ∧
      ¬ ((4 : ℕ) = 3 ∨ (4 ≤ 4 ∧ ¬ ((3 : ℕ) : ℤ) ∣ 1 ∧
        legendreSym 3 ((-1) ^ (4 / 2) * ∏ i, ![(1 : ℤ), 1, 1, 1] i) = (-1) ^ (4 - 1))) := by
  have ha : ∀ i, ¬ ((3 : ℕ) : ℤ) ∣ ![(1 : ℤ), 1, 1, 1] i := by
    intro i; fin_cases i <;> decide
  have hΦ : legendreSym 3 ((-1) ^ (4 / 2) * ∏ i, ![(1 : ℤ), 1, 1, 1] i) = 1 := by
    simp [Fin.prod_univ_four, legendreSym.at_one]
  refine ⟨(localConstC'_diag_even_unit _ 3 (by norm_num) ha le_rfl (by decide) 1 (by decide)).1 hΦ,
    ?_⟩
  rw [hΦ]
  decide

/-- **Remark 5.4.1(a), primitive limit, fails as printed** (local check for the erratum at
`localDensityOf_nonZero_pow_sq`): for $Q = x_0^2 + x_1^2 + x_2^2$ at $p = 3$, $K = \beta^*_3(9) = 8/9$ while
$\beta^*_3(1) = 2/3$, so $a^*_E(9^\nu)/3^\nu = (4/3)\,a^*_E(1)$ for $\nu \ge 1$, not $a^*_E(1)$. -/
theorem primitive_density_check :
    localDensityOf (QuadForm.diag ![(1 : ℤ), 1, 1]) 3 ((3 : ℤ) ^ 2 * 1)
        (fun k x => ¬ IsZeroType 3 k x) = 8 / 9 ∧
      localDensityOf (QuadForm.diag ![(1 : ℤ), 1, 1]) 3 1 (fun k x => ¬ IsZeroType 3 k x) = 2 / 3 := by
  have ha : ∀ i, ¬ ((3 : ℕ) : ℤ) ∣ ![(1 : ℤ), 1, 1] i := by
    intro i; fin_cases i <;> decide
  obtain ⟨h0, h1⟩ := table1_three 1 1 1 3 (by norm_num) (by decide) (by decide) (by decide) 1
    (by decide)
  have hl : legendreSym 3 (-(1 * 1 * 1 * 1)) = -1 := by
    rw [show (-(1 * 1 * 1 * 1) : ℤ) = -1 by norm_num, legendreSym.at_neg_one (by norm_num)]; rfl
  rw [hl] at h1
  have hd : QuadForm.diag ![(1 : ℤ), 1, 1] = QuadForm.diag ![1, 1, 1] := rfl
  refine ⟨?_, ?_⟩
  · have := localDensityOf_nonZero_diag_sq ![(1 : ℤ), 1, 1] 3 (by norm_num) ha 1
    push_cast at this ⊢
    rw [this, h0]; norm_num
  · rw [localDensityOf_nonZero_diag ![(1 : ℤ), 1, 1] 3 (by norm_num) ha 1]
    have h2 := repCount_one_eq_nonZero_add (QuadForm.diag ![(1 : ℤ), 1, 1]) 3 1
    rw [if_neg (by rw [intCast_zmod_pow_one_eq_zero]; decide), add_zero] at h2
    rw [← h2]
    have : (repCount (QuadForm.diag ![(1 : ℤ), 1, 1]) 3 1 1 : ℤ) = 6 := by rw [h1]; norm_num
    have : (repCount (QuadForm.diag ![(1 : ℤ), 1, 1]) 3 1 1 : ℝ) = 6 := by exact_mod_cast this
    rw [this]; norm_num

end Checks

end QuadFormsKB.LocalDensity
