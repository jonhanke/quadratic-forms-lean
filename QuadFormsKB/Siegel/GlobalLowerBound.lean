/-
# The global lower bound for $a_E(T')$ at $n = 4$ (Hanke 2004, Thm 5.7(b))

`thm_6_3` (Thm 6.3, $n = 4$) takes the **global** lower bound for the main term $a_E(T')$ as a hypothesis `hglob`:
$$\hat\Lambda_4\,(T')_{\mathrm{Iso}}\prod_{\substack{p \mid T'\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \;\le\; a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T').$$
This file **proves** it from Siegel's formula (`SiegelFormula`), with the explicit constant (`lambdaHat4`)
$$\hat\Lambda_4(S, T') = 6\,D^{-1/2}\,(T')_{\mathrm{Aniso}}\prod_{p \mid 2\det H}\beta_p(T')
  \prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T'), \qquad D = \det H/2^4 .$$

**Argument** (Hanke 2004, proof of Thm 5.7(b), pp. 374–375, with $1/L(2, \chi)$ replaced by $1/\zeta(2)$):
- $\beta_\infty(T') = \pi^2 D^{-1/2}\,T'$ for $n = 4$ (`betaInf_four`; (5.5) with $\omega_4 = \pi^2/2$);
- at a good prime $p$ (odd, $p \nmid \det H$), with $\chi(p) = \left(\frac{\det H}{p}\right)$:
  $\beta_p(m) \ge (1 - p^{-2})\cdot\frac{p-1}{p+1}$ if $\chi(p) = -1$ and $p \mid m$, and $\beta_p(m) \ge 1 - p^{-2}$ otherwise
  (`localDensity_good_four_ge`; from Table 1 and the recursion $\beta_p(p^2T) = \beta_p(T)/p^2 + K$, (3.x)/(5.8));
- $\prod_{p \in S}(1 - p^{-2}) \ge 1/\zeta(2) = 6/\pi^2$ for every finite set $S$ of primes
  (`six_div_pi_sq_le_prod`; Mathlib's Euler product `riemannZeta_eulerProduct` and `riemannZeta_two`);
- the finitely many bad factors $\beta_p(T')$, $p \mid 2\det H$, are kept as they are (Hanke keeps them too, as
  $\beta_p(T')/(1 - \chi(p)/q^2)$, $p \mid N$).
So $a_E(T') \ge 6D^{-1/2}\,T'\prod_{p \mid 2\det H}\beta_p(T')\prod_{p \mid T'\ \mathrm{good},\ \chi(p) = -1}\frac{p-1}{p+1}$
(`aE_four_ge`), and `hglob_four` is this times $\prod C'_p(T') \ge 0$, using $T' = (T')_{\mathrm{Iso}}(T')_{\mathrm{Aniso}}$.

*Positivity:* $\hat\Lambda_4 > 0$ when $T'$ is locally represented at every $p \mid 2\det H$ and $C'_p(T') > 0$ at the bad
isotropic $p \in S$ (`lambdaHat4_pos`). The second condition is not derived here.

*Comparison with the paper's $\hat\Lambda_4$:* Hanke's generic factor is $1/L(2, \chi) \ge 1/\zeta(2)$ (here the
cruder $\prod_{p\ \mathrm{good}}(1 - p^{-2}) \ge 6/\pi^2$ is used for every good prime, losing at most the factor
$\prod_p\frac{1 + p^{-2}}{1 - p^{-2}} = \zeta(2)^2/\zeta(4) = 5/2$), and Hanke's good-prime factor at $p \mid T'$ is $1 - \frac1q$, sharper than
$\frac{q-1}{q+1}$; Thm 6.3 only uses $\frac{q-1}{q+1}$.
-/
import QuadFormsKB.Siegel.MainResults
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

open Filter Topology

namespace QuadFormsKB.Siegel

open LocalDensity

/-! ### $1/\zeta(2) = 6/\pi^2$ bounds every finite Euler product $\prod(1 - p^{-2})$ -/

/-- **The real Euler product of $\zeta(2)$:** $\prod_{p < N}(1 - p^{-2})^{-1} \to \pi^2/6$ as $N \to \infty$ (Mathlib's
`riemannZeta_eulerProduct` at $s = 2$ and `riemannZeta_two`). -/
theorem tendsto_prod_primesBelow_inv :
    Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - 1 / (p : ℝ) ^ 2)⁻¹) atTop
      (𝓝 (Real.pi ^ 2 / 6)) := by
  have h := riemannZeta_eulerProduct (s := 2) (by norm_num)
  rw [riemannZeta_two] at h
  have h2 := (Complex.continuous_re.tendsto _).comp h
  have e : (Real.pi ^ 2 / 6 : ℝ) = ((Real.pi : ℂ) ^ 2 / 6).re := by
    rw [show ((Real.pi : ℂ) ^ 2 / 6) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [e]
  refine h2.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [show (∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-(2 : ℂ)))⁻¹) =
      ((∏ p ∈ Nat.primesBelow N, (1 - 1 / (p : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) by
    push_cast
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [show (-(2 : ℂ)) = ((-2 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
    simp [zpow_neg]]
  exact Complex.ofReal_re _

theorem one_sub_inv_sq_mem {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) ^ 2 ∧ 1 - 1 / (p : ℝ) ^ 2 ≤ 1 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine ⟨?_, by have : 0 < 1 / (p : ℝ) ^ 2 := by positivity
                 linarith⟩
  rw [sub_pos, div_lt_one (by positivity)]; nlinarith

theorem one_le_inv_one_sub_inv_sq {p : ℕ} (hp : p.Prime) : (1 : ℝ) ≤ (1 - 1 / (p : ℝ) ^ 2)⁻¹ :=
  (one_le_inv₀ (one_sub_inv_sq_mem hp).1).2 (one_sub_inv_sq_mem hp).2

/-- $\prod_{p < N}(1 - p^{-2})^{-1} \le \zeta(2) = \pi^2/6$ (the partial products increase to $\zeta(2)$). -/
theorem prod_primesBelow_inv_le (N : ℕ) :
    ∏ p ∈ Nat.primesBelow N, (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
  refine Monotone.ge_of_tendsto (fun a b hab => ?_) tendsto_prod_primesBelow_inv N
  have hsub := Nat.primesBelow_mono hab
  rw [← Finset.prod_sdiff hsub]
  refine le_mul_of_one_le_left (Finset.prod_nonneg fun p hp =>
      le_trans zero_le_one (one_le_inv_one_sub_inv_sq (Nat.prime_of_mem_primesBelow hp)))
    (Finset.one_le_prod₀ fun p hp =>
      one_le_inv_one_sub_inv_sq (Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.1 hp).1))

/-- **$1/\zeta(2)$ bounds every finite Euler product** (Hanke 2004, Thm 5.7(b), with $L(2,\chi) \le \zeta(2)$): for a
finite set $S$ of primes, $\prod_{p \in S}(1 - p^{-2}) \ge 6/\pi^2$. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (1/L(2,χ) ≥ 1/ζ(2) = 6/π²)"]
theorem six_div_pi_sq_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    6 / Real.pi ^ 2 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := by
  set N := S.sup id + 1
  have hsub : S ⊆ Nat.primesBelow N := fun p hp => Nat.mem_primesBelow.2
    ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hp), hS p hp⟩
  refine le_trans ?_ (prod_le_prod_of_subset_of_le_one hsub
    (fun p hp => (one_sub_inv_sq_mem (Nat.prime_of_mem_primesBelow hp)).1.le)
    (fun p hp => (one_sub_inv_sq_mem (Nat.prime_of_mem_primesBelow hp)).2))
  have hpos : 0 < ∏ p ∈ Nat.primesBelow N, (1 - 1 / (p : ℝ) ^ 2) := Finset.prod_pos fun p hp =>
    (one_sub_inv_sq_mem (Nat.prime_of_mem_primesBelow hp)).1
  have h := prod_primesBelow_inv_le N
  rw [Finset.prod_inv_distrib] at h
  have hpi : 0 < Real.pi ^ 2 := by positivity
  rw [div_le_iff₀ hpi]
  rw [inv_le_iff_one_le_mul₀ hpos] at h
  nlinarith

/-! ### $\beta_\infty$ for $n = 4$ -/

/-- **$\beta_\infty(m) = \pi^2 D^{-1/2}\,m$ for $n = 4$** (Hanke 2004, (5.5), p. 369, with $\omega_4 = \pi^2/2$):
$\frac{n\omega_nD^{-1/2}}{2}m^{(n-2)/2} = \frac{4\cdot\pi^2/2}{2}D^{-1/2}m$. -/
theorem betaInf_four (Q : QuadForm ℤ 4) (m : ℝ) :
    betaInf Q m = Real.pi ^ 2 * gramDet Q ^ (-(1 / 2 : ℝ)) * m := by
  rw [betaInf, unitBallVol_eq (by norm_num)]
  have hG : Real.Gamma ((4 : ℕ) / 2 + 1 : ℝ) = 2 := by
    rw [show ((4 : ℕ) / 2 + 1 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hG]
  have hs : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hs, show (((4 : ℕ) : ℝ) - 2) / 2 = 1 by norm_num, Real.rpow_one]
  push_cast
  ring

/-! ### Good primes, $n = 4$ -/

/-- **Lower bound for $\beta_p(m)$ at a good prime, $n = 4$** (Hanke 2004, Table 1, p. 363, and the computation in the
proof of Thm 5.7(b), p. 374): for $Q$ nondegenerate quaternary, $p$ odd, $p \nmid \det H$, $m \ne 0$, and
$\chi(p) = \left(\frac{\det H}{p}\right)$,
$$\beta_p(m) \;\ge\; \Big(1 - \frac1{p^2}\Big)\cdot\begin{cases}\frac{p-1}{p+1} & \chi(p) = -1,\ p \mid m,\\ 1 & \text{otherwise.}\end{cases}$$
*Proof:* for $p \nmid m$, $\beta_p(m) = 1 - \chi(p)/p^2$; for $p \mid m$, $\beta_p(m) \ge K = (1 - \chi(p)/p^2)(1 + \chi(p)/p)$
(equality if $p \,\|\, m$; if $p^2 \mid m$, $\beta_p(m) = \beta_p(m/p^2)/p^2 + K$); and
$(1 + p^{-2})(1 - p^{-1}) \ge (1 - p^{-1})^2 = (1 - p^{-2})\frac{p-1}{p+1}$. -/
@[kb "hanke2004" "Table 1, p. 363; proof of Thm 5.7(b), p. 374"]
theorem localDensity_good_four_ge (Q : QuadForm ℤ 4) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (m : ℤ) (hm : m ≠ 0) :
    (1 - 1 / (p : ℝ) ^ 2) *
        (if jacobiSym Q.hessian.det p = -1 ∧ (p : ℤ) ∣ m then ((p : ℝ) - 1) / ((p : ℝ) + 1) else 1) ≤
      localDensity Q p m := by
  have hpp : p.Prime := Fact.out
  obtain ⟨a, ha, hcnt, u, hu, hprod⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  have hχ : jacobiSym Q.hessian.det p = legendreSym p (∏ i, a i) := by
    have := legendreSym_prod_eq_even Q (by decide) p hp a hu hprod 0
    rw [pow_zero, one_mul, one_mul] at this
    rw [this, jacobiSym.legendreSym.to_jacobiSym]
  have hL := legendreSym.eq_one_or_neg_one p (LocalDensity.prod_ne_zero_zmod a p ha)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpp2 : ¬ (p : ℤ) ^ 2 ∣ (p : ℤ) := by
    intro h
    have h' : p ^ 2 ∣ p := by exact_mod_cast h
    have := Nat.le_of_dvd hpp.pos h'
    nlinarith [hpp.two_le]
  have hV : localDensity (QuadForm.diag a) p p =
      (1 - (legendreSym p (∏ i, a i) : ℝ) / (p : ℝ) ^ 2) * (1 + (legendreSym p (∏ i, a i) : ℝ) / p) := by
    have := localDensity_diag_even_ord_one a p hp ha (by norm_num) (by decide) (p : ℤ) dvd_rfl hpp2
    rw [this]; norm_num
  by_cases hpm : (p : ℤ) ∣ m
  · have hge : (1 - (legendreSym p (∏ i, a i) : ℝ) / (p : ℝ) ^ 2) *
        (1 + (legendreSym p (∏ i, a i) : ℝ) / p) ≤ localDensity Q p m := by
      by_cases hsq : (p : ℤ) ^ 2 ∣ m
      · obtain ⟨T, rfl⟩ := hsq
        have hT0 : T ≠ 0 := by rintro rfl; simp at hm
        have hK := localDensityOf_nonZero_eq Q hQ p (by norm_num) T hT0
        have h1 : padicValInt p (p : ℤ) = 1 := by simp [padicValInt, padicValNat_self]
        rw [(localDensity_congr_of_repCount Q _ p hcnt T).2.1,
          localDensityOf_nonZero_diag_sq a p hp ha T,
          ← localDensity_diag_ord_one a p hp ha _ h1, hV] at hK
        have hβT := LocalDensity.localDensity_nonneg Q hQ p T hT0
        have : 0 ≤ ((p : ℝ) ^ (4 - 2))⁻¹ * localDensity Q p T := by positivity
        linarith
      · rw [(localDensity_congr_of_repCount Q _ p hcnt m).1,
          localDensity_diag_even_ord_one a p hp ha (by norm_num) (by decide) m hpm hsq]
        norm_num
    rcases hL with h | h
    · have hc : ¬ (jacobiSym Q.hessian.det p = -1 ∧ (p : ℤ) ∣ m) := by
        rw [hχ, h]; rintro ⟨h', -⟩; exact absurd h' (by decide)
      rw [ite_eq_right hc, mul_one]
      rw [h] at hge
      push_cast at hge
      have : 0 ≤ (1 - 1 / (p : ℝ) ^ 2) * (1 / p) :=
        mul_nonneg (one_sub_inv_sq_mem hpp).1.le (by positivity)
      nlinarith
    · rw [ite_eq_left ⟨by rw [hχ, h], hpm⟩]
      rw [h] at hge
      push_cast at hge
      have e : (1 - 1 / (p : ℝ) ^ 2) * (((p : ℝ) - 1) / ((p : ℝ) + 1)) = (1 - 1 / (p : ℝ)) ^ 2 := by
        field_simp; ring
      rw [e]
      refine le_trans ?_ hge
      have h3 : 0 ≤ 1 - 1 / (p : ℝ) := by
        rw [sub_nonneg, div_le_one hp0]; linarith
      have h4 : 1 - 1 / (p : ℝ) ≤ 1 + 1 / (p : ℝ) ^ 2 := by
        have : 0 ≤ 1 / (p : ℝ) := by positivity
        have : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
        linarith
      calc (1 - 1 / (p : ℝ)) ^ 2 = (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := sq _
        _ ≤ (1 + 1 / (p : ℝ) ^ 2) * (1 - 1 / (p : ℝ)) := mul_le_mul_of_nonneg_right h4 h3
        _ = (1 - (-1) / (p : ℝ) ^ 2) * (1 + (-1) / (p : ℝ)) := by ring
  · rw [ite_eq_right (fun h => hpm h.2), mul_one, (localDensity_congr_of_repCount Q _ p hcnt m).1,
      localDensity_diag_even_unit a p hp ha (by norm_num) (by decide) m hpm]
    norm_num
    have : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
    rcases hL with h | h <;> rw [h] <;> simp only [Int.cast_one, Int.cast_neg, neg_div, one_div] <;>
      linarith

/-! ### The Euler product at $n = 4$ -/

variable {n : ℕ}

/-- **The bad primes** $\{p : p \mid 2\det H\}$ (the primes that are not `IsGoodPrime`, for $Q$ nondegenerate:
`mem_badPrimes`). -/
noncomputable def badPrimes (Q : QuadForm ℤ n) : Finset ℕ := (2 * Q.hessian.det).natAbs.primeFactors

theorem mem_badPrimes {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {p : ℕ} :
    p ∈ badPrimes Q ↔ p.Prime ∧ ¬ IsGoodPrime Q p := by
  have h0 : (2 * Q.hessian.det).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (mul_ne_zero two_ne_zero hQ)
  rw [badPrimes, Nat.mem_primeFactors, IsGoodPrime]
  constructor
  · rintro ⟨hp, hd, -⟩
    refine ⟨hp, fun ⟨_, h2, hdet⟩ => ?_⟩
    have hd' : (p : ℤ) ∣ 2 * Q.hessian.det := Int.natCast_dvd.2 hd
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd' with h | h
    · have : p ∣ 2 := by exact_mod_cast h
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · exact hdet h
  · rintro ⟨hp, hng⟩
    refine ⟨hp, ?_, h0⟩
    rw [← Int.natCast_dvd]
    by_cases h2 : p = 2
    · subst h2; exact dvd_mul_right _ _
    · have : (p : ℤ) ∣ Q.hessian.det := by
        by_contra h; exact hng ⟨hp, h2, h⟩
      exact this.mul_left 2

theorem le_of_mem_badPrimes {Q : QuadForm ℤ n} {p : ℕ} (hp : p ∈ badPrimes Q) :
    p ≤ (2 * Q.hessian.det).natAbs :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_primeFactors.1 hp).2.2) (Nat.dvd_of_mem_primeFactors hp)

open Classical in
/-- **Lower bound for the partial Euler products, $n = 4$:** for $Q$ nondegenerate quaternary, $T \ge 1$ and
$X \ge \max(|2\det H|, T)$,
$$\prod_{p \le X}\beta_p(T) \;\ge\; \frac{6}{\pi^2}\prod_{p \mid 2\det H}\beta_p(T)
  \prod_{\substack{p \mid T\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}.$$ -/
theorem eulerPartialProd_four_ge (Q : QuadForm ℤ 4) (hQ : Q.Nondegenerate) {T : ℕ} (hT : 0 < T)
    {X : ℕ} (hX1 : (2 * Q.hessian.det).natAbs ≤ X) (hX2 : T ≤ X) :
    6 / Real.pi ^ 2 * (∏ p ∈ badPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      eulerPartialProd Q T X := by
  set P := Nat.primesBelow (X + 1) with hP
  have hPmem : ∀ {p}, p ∈ P ↔ p ≤ X ∧ p.Prime := by
    intro p; rw [hP, Nat.mem_primesBelow, Nat.lt_succ_iff]
  have hE : eulerPartialProd Q T X = ∏ p ∈ P, localDensity Q p T := by
    rw [eulerPartialProd, primesUpTo]
    exact Finset.prod_subtype_eq_prod_filter (s := Finset.range (X + 1)) (p := Nat.Prime)
      (fun q : ℕ => localDensity Q q (T : ℤ))
  rw [hE, ← Finset.prod_filter_mul_prod_filter_not P (fun p => IsGoodPrime Q p)]
  have hbad : P.filter (fun p => ¬ IsGoodPrime Q p) = badPrimes Q := by
    ext p
    rw [Finset.mem_filter, hPmem, mem_badPrimes hQ]
    constructor
    · rintro ⟨⟨-, hp⟩, hg⟩; exact ⟨hp, hg⟩
    · rintro ⟨hp, hg⟩
      exact ⟨⟨le_trans (le_of_mem_badPrimes ((mem_badPrimes hQ).2 ⟨hp, hg⟩)) hX1, hp⟩, hg⟩
  rw [hbad]
  set G := P.filter (fun p => IsGoodPrime Q p) with hG
  set g : ℕ → ℝ := fun p =>
    if jacobiSym Q.hessian.det p = -1 ∧ (p : ℤ) ∣ (T : ℤ) then ((p : ℝ) - 1) / ((p : ℝ) + 1) else 1
  have hGprime : ∀ p ∈ G, p.Prime := fun p hp => (hPmem.1 (Finset.mem_filter.1 hp).1).2
  -- the good part
  have hgood : (∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2)) * ∏ p ∈ G, g p ≤ ∏ p ∈ G, localDensity Q p T := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have hp := hGprime p hp
      refine mul_nonneg (one_sub_inv_sq_mem hp).1.le ?_
      simp only [g]
      split_ifs
      · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        exact div_nonneg (by linarith) (by linarith)
      · exact zero_le_one
    · have hpG := (Finset.mem_filter.1 hp).2
      have : Fact p.Prime := ⟨hpG.1⟩
      exact localDensity_good_four_ge Q hQ p hpG.2.1 hpG.2.2 T (by exact_mod_cast hT.ne')
  -- the character product
  have hgG : ∏ p ∈ G, g p =
      ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
        ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
    simp only [g]
    rw [← Finset.prod_filter]
    refine Finset.prod_congr (Finset.ext fun p => ?_) fun _ _ => rfl
    simp only [Finset.mem_filter, hG, hPmem, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨⟨-, hp⟩, hg⟩, hχ, hd⟩
      exact ⟨⟨hp, Int.natCast_dvd_natCast.1 hd, hT.ne'⟩, hg, hχ⟩
    · rintro ⟨⟨hp, hd, -⟩, hg, hχ⟩
      exact ⟨⟨⟨le_trans (Nat.le_of_dvd hT hd) hX2, hp⟩, hg⟩, hχ, Int.natCast_dvd_natCast.2 hd⟩
  -- assemble
  have hz : 6 / Real.pi ^ 2 ≤ ∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2) := six_div_pi_sq_le_prod G hGprime
  have hB0 : 0 ≤ ∏ p ∈ badPrimes Q, localDensity Q p T := Finset.prod_nonneg fun p hp => by
    have : Fact p.Prime := ⟨((mem_badPrimes hQ).1 hp).1⟩
    exact LocalDensity.localDensity_nonneg Q hQ p T (by exact_mod_cast hT.ne')
  have hg0 : 0 ≤ ∏ p ∈ G, g p := by
    rw [hgG]
    refine Finset.prod_nonneg fun p hp => ?_
    have : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
    exact div_nonneg (by linarith) (by linarith)
  rw [← hgG]
  calc 6 / Real.pi ^ 2 * (∏ p ∈ badPrimes Q, localDensity Q p T) * ∏ p ∈ G, g p
      ≤ (∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2)) * (∏ p ∈ badPrimes Q, localDensity Q p T) *
          ∏ p ∈ G, g p := by gcongr
    _ = ((∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2)) * ∏ p ∈ G, g p) *
          ∏ p ∈ badPrimes Q, localDensity Q p T := by ring
    _ ≤ (∏ p ∈ G, localDensity Q p T) * ∏ p ∈ badPrimes Q, localDensity Q p T :=
        mul_le_mul_of_nonneg_right hgood hB0

open Classical in
/-- **The global lower bound for $a_E^{\mathrm{loc}}(T')$, $n = 4$** (Hanke 2004, Thm 5.7(b), p. 373, proof pp. 374–375,
with $1/L(2,\chi) \ge 1/\zeta(2) = 6/\pi^2$): for $Q$ positive definite quaternary and $T' \ge 1$,
$$\beta_\infty(T')\prod_p\beta_p(T') \;\ge\; 6\,D^{-1/2}\,T'\prod_{p \mid 2\det H}\beta_p(T')
  \prod_{\substack{p \mid T'\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1},\qquad D = \det H/2^4,\ \chi(p) = \Big(\frac{\det H}{p}\Big).$$ -/
@[kb "hanke2004" "Thm 5.7(b), p. 373; proof pp. 374–375"]
theorem aE_four_ge (Q : IntQF 4) (hQ : IntQF.PosDef Q) {T : ℕ} (hT : 0 < T) :
    6 * gramDet Q ^ (-(1 / 2 : ℝ)) * T * (∏ p ∈ badPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      aE Q T := by
  have hT0 : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
  have hlim := isEulerProductValue_eulerProduct Q hQ.nondegenerate le_rfl hT0
  have hle := ge_of_tendsto hlim (Filter.eventually_atTop.2
    ⟨max (2 * Q.hessian.det).natAbs T, fun X hX =>
      eulerPartialProd_four_ge Q hQ.nondegenerate hT (le_of_max_le_left hX)
        (le_of_max_le_right hX)⟩)
  rw [aE, aEWith, betaInf_four]
  have hD : 0 ≤ gramDet Q ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (gramDet_pos hQ).le _
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  have hTr : (((T : ℤ) : ℝ)) = (T : ℝ) := by push_cast; rfl
  rw [hTr]
  calc 6 * gramDet Q ^ (-(1 / 2 : ℝ)) * T * (∏ p ∈ badPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1)
      = Real.pi ^ 2 * gramDet Q ^ (-(1 / 2 : ℝ)) * T *
        (6 / Real.pi ^ 2 * (∏ p ∈ badPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1)) := by field_simp
    _ ≤ Real.pi ^ 2 * gramDet Q ^ (-(1 / 2 : ℝ)) * T * eulerProduct Q T :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-! ### The hypothesis `hglob` of `thm_6_3` -/

open Classical in
/-- **The constant $\hat\Lambda_4$ of Thm 5.7(b)/Thm 6.3 for a fixed $T'$** (Hanke 2004, p. 373, for the single square
class $T'(\mathbb{Z}^\times)^2$): for $S$ a finite set of primes and $T' \ge 1$,
$$\hat\Lambda_4(S, T') = 6\,D^{-1/2}\,(T')_{\mathrm{Aniso}}\prod_{p \mid 2\det H}\beta_p(T')
  \prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T'), \qquad D = \det H/2^4.$$
Hanke's $\hat\Lambda_4$ is the minimum of such constants over the finitely many $T' \in B_{\mathbb T}$, with $2\omega_4 D^{-1/2}/L(2,\chi)$
and $\beta_p(T')/(1 - \chi(p)/q^2)$, $p \mid N$, in place of $6D^{-1/2} = \pi^2D^{-1/2}\cdot\frac{6}{\pi^2}$ and $\beta_p(T')$,
$p \mid 2\det H$ (`aE_four_ge`). Positive under local conditions (`lambdaHat4_pos`). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (Λ̂₄ for one T')"]
noncomputable def lambdaHat4 (Q : QuadForm ℤ 4) (S : Finset ℕ) (T : ℕ) : ℝ :=
  6 * gramDet Q ^ (-(1 / 2 : ℝ)) * anisoPart Q T * (∏ p ∈ badPrimes Q, localDensity Q p T) *
    ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p), localConstC' Q p T

open Classical in
/-- **The global input `hglob` of `thm_6_3`, proved from Siegel's formula** (Hanke 2004, Thm 5.7(b), p. 373): for $Q$
positive definite quaternary, $S$ a finite set of primes and $T' \ge 1$,
$$\hat\Lambda_4(S, T')\,(T')_{\mathrm{Iso}}\prod_{\substack{p \mid T'\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \;\le\; a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T'),$$
with $\hat\Lambda_4$ = `lambdaHat4` and $a_E$ the genus average (`genusRepAvg`). This is exactly the hypothesis `hglob` of
`thm_6_3` with $\Lambda = \hat\Lambda_4(S, T')$. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global bound, n = 4)"]
theorem hglob_four (Q : IntQF 4) (hQ : IntQF.PosDef Q) (hSF : SiegelFormula Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {T : ℕ} (hT : 0 < T) :
    lambdaHat4 Q S T * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T := by
  have hCb0 : 0 ≤ ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
      localConstC' Q p T := Finset.prod_nonneg fun p hp => by
    have : Fact p.Prime := ⟨hS p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1⟩
    exact localConstC'_nonneg Q hQ.nondegenerate (by norm_num) p T (by exact_mod_cast hT.ne')
  rw [hSF.1 _ (by exact_mod_cast hT)]
  have hT' : (T : ℝ) = isoPart Q T * anisoPart Q T := by
    exact_mod_cast (isoPart_mul_anisoPart Q hT.ne').symm
  have h := mul_le_mul_of_nonneg_right (aE_four_ge Q hQ hT) hCb0
  refine le_of_eq_of_le ?_ h
  rw [lambdaHat4, hT']
  ring

/-- **$\hat\Lambda_4(S, T') > 0$** when $T'$ is locally represented at every $p \mid 2\det H$ (Def. 3.5, so $\beta_p(T') > 0$)
and $C'_p(T') > 0$ at the bad isotropic $p \in S$ (`hC`, not derived here). -/
theorem lambdaHat4_pos (Q : IntQF 4) (hQ : IntQF.PosDef Q) (S : Finset ℕ) {T : ℕ} (hT : 0 < T)
    (hloc : ∀ p ∈ badPrimes Q, IsLocallyRepresentedAt Q p T)
    (hC : ∀ p ∈ S, IsIsotropicPrime Q p → ¬ IsGoodPrime Q p → 0 < localConstC' Q p T) :
    0 < lambdaHat4 Q S T := by
  classical
  unfold lambdaHat4
  have hD : 0 < gramDet Q ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (gramDet_pos hQ) _
  have hA : (0 : ℝ) < anisoPart Q T := by exact_mod_cast anisoPart_pos Q T
  have hB : 0 < ∏ p ∈ badPrimes Q, localDensity Q p T := Finset.prod_pos fun p hp => by
    have : Fact p.Prime := ⟨((mem_badPrimes hQ.nondegenerate).1 hp).1⟩
    exact localDensity_pos_of_isLocallyRepresentedAt Q hQ.nondegenerate p T
      (by exact_mod_cast hT.ne') (hloc p hp)
  have hCb : 0 < ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
      localConstC' Q p T := Finset.prod_pos fun p hp => by
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpS, hpI⟩ := Finset.mem_filter.1 hp1
    exact hC p hpS hpI hp2
  positivity

end QuadFormsKB.Siegel
