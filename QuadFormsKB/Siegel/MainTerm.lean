/-
# Siegel's formula: Theorems 5.4 and 5.7 of Hanke 2004 in ratio form

The local side of Siegel's formula is $a_E^{\mathrm{loc}}(m) = \beta_\infty(m)\prod_p\beta_p(m)$ (`aE`, `aEWith`). For
$m = T'(m')^2$ with $m' = \prod_{p \in S} p^{\nu_p}$, only finitely many factors change:
$\beta_\infty(m) = (m')^{n-2}\beta_\infty(T')$ ((5.5)) and $\beta_p(m) = \beta_p(T')$ for $p \notin S$. So
$$a_E^{\mathrm{loc}}(m) = a_E^{\mathrm{loc}}(T') \prod_{p \in S} F_p, \qquad
  F_p = q^{(n-2)\nu_p}\,\frac{\beta_p(T'p^{2\nu_p})}{\beta_p(T')} \quad (q = p)$$
(`aEWith_mul_sq`, `aE_mul_sq`), and the local results of `LocalDensity/LowerBounds.lean` evaluate or bound
each $F_p$. This file proves, **unconditionally** (no Siegel formula needed, since everything is about the local
product):

| Paper | Lean |
|---|---|
| Thm 5.4, p. 369 (exact formula) | `thm_5_4`, `thm_5_4_aE`; uniform form `aEWith_mul_sq_eq_localConst` |
| (5.13), p. 373 | `eq_5_13`, `eq_5_13_aE` |
| Thm 5.7(a), first part, p. 372 ($n = 3$) | `thm_5_7_a` |
| Thm 5.7(b), p. 373 ($n = 4$), local-product form | `thm_5_7_b` |
| Thm 5.7(c), p. 373 ($n \ge 5$), local-product form | `thm_5_7_c_even`, `thm_5_7_c_odd` |

The $L$-function and $\zeta_F$ factors of Thm 5.7 belong to the global lower bound for $a_E(T')$ (the minimum over
$T' \in B_{\mathbb T}$) and are **not** part of these statements; what is proved is the ratio $a_E(m)/a_E(T')$.

**$n = 3$ (product convention undecided).** Statements valid for $n = 3$ use `aEWith Q m P` with
hypotheses `IsEulerProductValue Q m P` (natural-order limit of the partial Euler products) for both $m$ and $T'$;
`tprod` is never used for $n = 3$. For $n \ge 4$ the `aE` versions follow.
-/
import QuadFormsKB.Siegel.Archimedean

open Matrix Filter Topology

namespace QuadFormsKB.Siegel

open LocalDensity

variable {n : ℕ}

/-! ### The square part $m'$ and the per-prime factor $F_p$ -/

/-- **The square part** $m' = \prod_{p \in S} p^{\nu_p}$ of $m = T'(m')^2$ (supported on the finite set $S$). -/
def sqPart (S : Finset ℕ) (ν : ℕ → ℕ) : ℤ := ∏ p ∈ S, (p : ℤ) ^ ν p

theorem sqPart_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) : 0 < sqPart S ν :=
  Finset.prod_pos fun p hp => pow_pos (by exact_mod_cast (hS p hp).pos) _

/-- A prime outside $S$ does not divide $m' = \prod_{p \in S} p^{\nu_p}$. -/
theorem not_dvd_sqPart {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) : ¬ (p : ℤ) ∣ sqPart S ν := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [sqPart, Prime.dvd_finsetProd_iff hpZ]
  rintro ⟨p', hp', hdvd⟩
  have h1 : p ∣ p' := by exact_mod_cast hpZ.dvd_of_dvd_pow hdvd
  rw [(Nat.prime_dvd_prime_iff_eq hp (hS p' hp')).1 h1] at hpS
  exact hpS hp'

/-- $\beta_p(T'(m')^2) = \beta_p(T')$ for $p \notin S$ ($m'$ is a $p$-adic unit). -/
theorem localDensity_mul_sqPart_of_not_mem (Q : QuadForm ℤ n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (ν : ℕ → ℕ) (T : ℤ) (p : ℕ) [Fact p.Prime] (hpS : p ∉ S) :
    localDensity Q p (T * sqPart S ν ^ 2) = localDensity Q p T := by
  rw [mul_comm]
  exact localDensity_mul_sq_of_not_dvd Q p _ (not_dvd_sqPart hS ν Fact.out hpS) T

/-- $\beta_p(T'(m')^2) = \beta_p(T'p^{2\nu_p})$ for $p \in S$. -/
theorem localDensity_mul_sqPart_of_mem (Q : QuadForm ℤ n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (ν : ℕ → ℕ) (T : ℤ) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) :
    localDensity Q p (T * sqPart S ν ^ 2) = localDensity Q p ((p : ℤ) ^ (2 * ν p) * T) :=
  localDensity_prod_sq Q S hS ν T p hpS

/-- **The local ratio factor** $F_p(T', \nu) = q^{(n-2)\nu}\,\beta_p(T'p^{2\nu})/\beta_p(T')$, $q = p$: the factor by which
$a_E^{\mathrm{loc}}$ changes at $p$ when $T'$ is multiplied by $p^{2\nu}$ (the $q^{(n-2)\nu}$ comes from $\beta_\infty$, (5.5)).
It is $1$ for $\nu = 0$ (when $\beta_p(T') \ne 0$). -/
noncomputable def sqShiftFactor (Q : QuadForm ℤ n) (T : ℤ) (p ν : ℕ) : ℝ :=
  (p : ℝ) ^ ((n - 2) * ν) * (localDensity Q p ((p : ℤ) ^ (2 * ν) * T) / localDensity Q p T)

/-! ### The Euler product and $\beta_\infty$ along a square class -/

/-- The natural-order value of the Euler product is unique. -/
theorem IsEulerProductValue.unique {Q : QuadForm ℤ n} {m : ℤ} {P P' : ℝ}
    (h : IsEulerProductValue Q m P) (h' : IsEulerProductValue Q m P') : P = P' :=
  tendsto_nhds_unique h h'

/-- **The Euler product along a square class.** If $\prod_p \beta_p(T')$ has the natural-order value $P$, then
$\prod_p \beta_p(T'(m')^2)$ has the natural-order value $\prod_{p \in S}\frac{\beta_p(T'p^{2\nu_p})}{\beta_p(T')} \cdot P$
(all but the finitely many factors at $p \in S$ are unchanged). Needs $\beta_p(T') \ne 0$ for $p \in S$. Valid for
every $n$ (in particular $n = 3$). -/
theorem isEulerProductValue_mul_sq {Q : QuadForm ℤ n} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (ν : ℕ → ℕ) {T : ℤ} (hβ : ∀ p ∈ S, localDensity Q p T ≠ 0) {P : ℝ}
    (hP : IsEulerProductValue Q T P) :
    IsEulerProductValue Q (T * sqPart S ν ^ 2)
      ((∏ p ∈ S, localDensity Q p ((p : ℤ) ^ (2 * ν p) * T) / localDensity Q p T) * P) := by
  classical
  set h : ℕ → ℝ := fun p =>
    if p ∈ S then localDensity Q p ((p : ℤ) ^ (2 * ν p) * T) / localDensity Q p T else 1 with hh
  set g : AWS.PrimeIdx → ℝ := fun p => h p with hg
  have hfac : ∀ p : AWS.PrimeIdx,
      eulerFactor Q (T * sqPart S ν ^ 2) p = g p * eulerFactor Q T p := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    simp only [eulerFactor, hg, hh]
    split_ifs with hpS
    · rw [localDensity_mul_sqPart_of_mem Q hS ν T p hpS, div_mul_cancel₀ _ (hβ p hpS)]
    · rw [localDensity_mul_sqPart_of_not_mem Q hS ν T p hpS, one_mul]
  have hgP : HasProd g (∏ p ∈ S.subtype Nat.Prime, g p) :=
    hasProd_prod_of_ne_finset_one fun p hp => by
      simp only [hg, hh]
      split_ifs with hpS
      · exact absurd (Finset.mem_subtype.mpr hpS) hp
      · rfl
  have hval : ∏ p ∈ S.subtype Nat.Prime, g p =
      ∏ p ∈ S, localDensity Q p ((p : ℤ) ^ (2 * ν p) * T) / localDensity Q p T := by
    rw [Finset.prod_subtype_eq_prod_filter (f := h), Finset.filter_true_of_mem hS]
    exact Finset.prod_congr rfl fun p hp => by simp [hh, hp]
  have hlim : Tendsto (fun X => ∏ p ∈ primesUpTo X, g p) atTop
      (𝓝 (∏ p ∈ S, localDensity Q p ((p : ℤ) ^ (2 * ν p) * T) / localDensity Q p T)) := by
    rw [← hval]
    exact (show Tendsto (fun s : Finset AWS.PrimeIdx => ∏ p ∈ s, g p) atTop _ from hgP).comp
      tendsto_primesUpTo
  refine (hlim.mul hP).congr fun X => ?_
  simp only [eulerPartialProd, hfac, Finset.prod_mul_distrib]

/-- **$n \ge 4$: the Euler product along a square class** (absolutely convergent case):
$\prod_p\beta_p(T'(m')^2) = \prod_{p \in S}\frac{\beta_p(T'p^{2\nu_p})}{\beta_p(T')}\prod_p\beta_p(T')$. -/
theorem eulerProduct_mul_sq {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) {T : ℤ} (hT0 : T ≠ 0)
    (hβ : ∀ p ∈ S, localDensity Q p T ≠ 0) :
    eulerProduct Q (T * sqPart S ν ^ 2) =
      (∏ p ∈ S, localDensity Q p ((p : ℤ) ^ (2 * ν p) * T) / localDensity Q p T) *
        eulerProduct Q T := by
  have hm : T * sqPart S ν ^ 2 ≠ 0 := mul_ne_zero hT0 (pow_ne_zero _ (sqPart_pos hS ν).ne')
  exact (isEulerProductValue_eulerProduct Q hQ hn hm).unique
    (isEulerProductValue_mul_sq hS ν hβ (isEulerProductValue_eulerProduct Q hQ hn hT0))

/-- **(5.5) along a square class:** $\beta_\infty(T'(m')^2) = \beta_\infty(T')\,(m')^{n-2}
= \beta_\infty(T')\prod_{p \in S} q^{(n-2)\nu_p}$ for $T' \ge 0$, $n \ge 2$ (Hanke 2004, p. 369, used in the proofs of
Thms 5.4 and 5.7). -/
@[kb "hanke2004" "(5.5), p. 369 (along a square class)"]
theorem betaInf_mul_sq (Q : QuadForm ℤ n) (hn : 2 ≤ n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (ν : ℕ → ℕ) {T : ℤ} (hT : 0 ≤ T) :
    betaInf Q ((T * sqPart S ν ^ 2 : ℤ) : ℝ) =
      betaInf Q T * ∏ p ∈ S, (p : ℝ) ^ ((n - 2) * ν p) := by
  have hm' : (0 : ℝ) ≤ (sqPart S ν : ℝ) := by exact_mod_cast (sqPart_pos hS ν).le
  have hT' : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hpow : ((sqPart S ν : ℝ) ^ 2) ^ (((n : ℝ) - 2) / 2) = (sqPart S ν : ℝ) ^ (n - 2) := by
    rw [← Real.rpow_natCast (sqPart S ν : ℝ) 2, ← Real.rpow_mul hm', ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub hn]; push_cast; ring
  have hprod : (sqPart S ν : ℝ) ^ (n - 2) = ∏ p ∈ S, (p : ℝ) ^ ((n - 2) * ν p) := by
    rw [sqPart]; push_cast
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun p _ => by rw [← pow_mul, mul_comm]
  simp only [betaInf]
  push_cast
  rw [Real.mul_rpow hT' (sq_nonneg _), hpow, hprod]
  ring

/-! ### The ratio identity -/

/-- **The ratio identity for the local product** ($n \ge 2$, any Euler-product convention given by natural-order
values): if $\prod_p\beta_p(T') = P$ and $\prod_p\beta_p(T'(m')^2) = P_m$ (natural-order limits), $T' \ge 0$ and
$\beta_p(T') \ne 0$ for $p \in S$, then
$$\beta_\infty(T'(m')^2)\,P_m = \beta_\infty(T')\,P \cdot \prod_{p \in S} F_p(T', \nu_p).$$
This is "$a_E(m)/a_E(T') = \prod_{p \mid m'} F_p$", the common core of Thms 5.4 and 5.7 (Hanke 2004, pp. 369–374). -/
theorem aEWith_mul_sq (Q : QuadForm ℤ n) (hn : 2 ≤ n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (ν : ℕ → ℕ) {T : ℤ} (hT : 0 ≤ T) (hβ : ∀ p ∈ S, localDensity Q p T ≠ 0) {P Pm : ℝ}
    (hP : IsEulerProductValue Q T P) (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) Pm) :
    aEWith Q (T * sqPart S ν ^ 2) Pm = aEWith Q T P * ∏ p ∈ S, sqShiftFactor Q T p (ν p) := by
  rw [hPm.unique (isEulerProductValue_mul_sq hS ν hβ hP), aEWith, aEWith, betaInf_mul_sq Q hn hS ν hT]
  simp only [sqShiftFactor, Finset.prod_mul_distrib]
  ring

/-- **The ratio identity for $n \ge 4$** (`aE`, absolutely convergent Euler products):
$a_E^{\mathrm{loc}}(T'(m')^2) = a_E^{\mathrm{loc}}(T')\prod_{p \in S}F_p(T', \nu_p)$ for $Q$ nondegenerate, $T' > 0$,
$\beta_p(T') \ne 0$ ($p \in S$). -/
theorem aE_mul_sq (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) {T : ℤ} (hT : 0 < T)
    (hβ : ∀ p ∈ S, localDensity Q p T ≠ 0) :
    aE Q (T * sqPart S ν ^ 2) = aE Q T * ∏ p ∈ S, sqShiftFactor Q T p (ν p) := by
  have hm : T * sqPart S ν ^ 2 ≠ 0 := mul_ne_zero hT.ne' (pow_ne_zero _ (sqPart_pos hS ν).ne')
  exact aEWith_mul_sq Q (by omega) hS ν hT.le hβ (isEulerProductValue_eulerProduct Q hQ hn hT.ne')
    (isEulerProductValue_eulerProduct Q hQ hn hm)

/-! ### Theorem 5.4: the exact formula -/

/-- **$F_p$ in terms of $C_p(T')$** (Hanke 2004, (5.8), p. 369, times $q^{(n-2)\nu}$): for $Q$ nondegenerate, $n \ge 3$
and $T' \ne 0$ $p$-stable, $F_p(T', \nu) = C_p(T')\,q^{(n-2)\nu} + (1 - C_p(T'))$. Valid at isotropic and anisotropic
$p$ (at anisotropic $p$, $C_p(T') = 0$ and $F_p = 1$). -/
theorem sqShiftFactor_eq_localConst (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T) (ν : ℕ) :
    sqShiftFactor Q T p ν = localConstC Q p T * (p : ℝ) ^ ((n - 2) * ν) + (1 - localConstC Q p T) := by
  have hp : (0 : ℝ) < (p : ℝ) ^ ((n - 2) * ν) :=
    pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  rw [sqShiftFactor, localDensity_pow_sq_div Q hQ hn p S₀ T hT0 hT ν]
  field_simp

/-- $F_p(T', \nu) = q^{(n-2)\nu}\big(C_p(T') + (1 - C_p(T'))/q^{(n-2)\nu}\big)$ ((5.8)). -/
theorem sqShiftFactor_eq_bracket (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T) (ν : ℕ) :
    sqShiftFactor Q T p ν = (p : ℝ) ^ ((n - 2) * ν) *
      (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν)) := by
  rw [sqShiftFactor, localDensity_pow_sq_div Q hQ hn p S₀ T hT0 hT ν]

/-- **$F_p = 1$ at anisotropic primes** (Hanke 2004, Remark 5.4.1(a), p. 370, "$a_E(m\pi_\mathfrak{p}^{2\nu}) = a_E(m)$"):
for $Q$ nondegenerate, $n \ge 3$, anisotropic over $\mathbb{Q}_p$ and $T' \ne 0$ $p$-stable. -/
theorem sqShiftFactor_of_anisotropic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (haniso : ¬ IsIsotropicPrime Q p) (T : ℤ) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ p T) (ν : ℕ) : sqShiftFactor Q T p ν = 1 := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT0 hT.1
  have hp : (0 : ℝ) < (p : ℝ) ^ ((n - 2) * ν) :=
    pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  rw [sqShiftFactor, localDensity_pow_sq_of_anisotropic Q hQ hn p S₀
    (fun h => haniso ((isIsotropicPrime_iff Q p).2 h)) T hT0 hT ν]
  field_simp

/-- **Theorem 5.4, uniform form** (Hanke 2004, p. 369, with the update that anisotropic primes need no separate
treatment): for $Q$ nondegenerate, $n \ge 3$, $T' > 0$ $p$-stable at every $p \in S$, $m = T'(m')^2$,
$m' = \prod_{p \in S}p^{\nu_p}$, and natural-order Euler-product values $P$ (at $T'$) and $P_m$ (at $m$):
$$\beta_\infty(m)P_m = \beta_\infty(T')P \cdot \prod_{p \in S}\Big(C_p(T')\,q^{(n-2)\nu_p} + 1 - C_p(T')\Big).$$ -/
theorem aEWith_mul_sq_eq_localConst (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) {P Pm : ℝ}
    (hP : IsEulerProductValue Q T P) (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) Pm) :
    aEWith Q (T * sqPart S ν ^ 2) Pm = aEWith Q T P *
      ∏ p ∈ S, (localConstC Q p T * (p : ℝ) ^ ((n - 2) * ν p) + (1 - localConstC Q p T)) := by
  have hβ : ∀ p ∈ S, localDensity Q p T ≠ 0 := fun p hp => by
    have : Fact p.Prime := ⟨hS p hp⟩
    exact (localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT.ne' (hst p hp).1).ne'
  rw [aEWith_mul_sq Q (by omega) hS ν hT.le hβ hP hPm]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have : Fact p.Prime := ⟨hS p hp⟩
  exact sqShiftFactor_eq_localConst Q hQ hn p S₀ T hT.ne' (hst p hp) (ν p)

open Classical in
/-- **Theorem 5.4** (Hanke 2004, p. 369), local product $a_E^{\mathrm{loc}}$, any $n \ge 3$. Let $Q$ be nondegenerate,
$n \ge 3$, $S$ a finite set of primes, $T' > 0$ $p$-stable at every $p \in S$ (Def. 3.6), $\nu_p \ge 0$,
$m' = \prod_{p \in S}p^{\nu_p}$ and $m = T'(m')^2$. If $P$ and $P_m$ are the natural-order values of
$\prod_p\beta_p(T')$ and $\prod_p\beta_p(m)$, then
$$\beta_\infty(m)P_m = \beta_\infty(T')P\prod_{p \in S \cap \mathrm{Iso}}\Big[C_p(T') + \frac{1 - C_p(T')}{q^{(n-2)\nu_p}}\Big]
  \cdot \big((m')_{\mathrm{Iso}}\big)^{n-2}, \qquad (m')_{\mathrm{Iso}} = \prod_{p \in S \cap \mathrm{Iso}} p^{\nu_p}.$$
With $S$ the set of primes dividing $m'$ this is the printed formula, with $a_E(\cdot) = \beta_\infty(\cdot)\prod_p\beta_p(\cdot)$.
*Differences from the paper:* proved over $\mathbb{Q}$ (the paper: totally real $F$); Siegel's formula (5.3)
identifies the local product with the genus average (`thm_5_4_genus`, under `SiegelFormula`).
*Update (candidate; pending author):* as a statement about the local product only nondegeneracy of $Q$ is used (the
paper: totally definite), and since $C_p(T') = 0$ at anisotropic $p$ the formula can be written uniformly over all
$p \mid m'$ as $\prod_{p \mid m'}(C_p(T')q^{(n-2)\nu_p} + 1 - C_p(T'))$ (`aEWith_mul_sq_eq_localConst`). -/
@[kb "hanke2004" "Thm 5.4, p. 369"]
theorem thm_5_4 (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) {P Pm : ℝ}
    (hP : IsEulerProductValue Q T P) (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) Pm) :
    aEWith Q (T * sqPart S ν ^ 2) Pm = aEWith Q T P *
      (∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν p))) *
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) := by
  have hβ : ∀ p ∈ S, localDensity Q p T ≠ 0 := fun p hp => by
    have : Fact p.Prime := ⟨hS p hp⟩
    exact (localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT.ne' (hst p hp).1).ne'
  rw [aEWith_mul_sq Q (by omega) hS ν hT.le hβ hP hPm,
    ← Finset.prod_filter_mul_prod_filter_not S (IsIsotropicPrime Q)]
  have h1 : ∏ p ∈ S.filter (fun p => ¬ IsIsotropicPrime Q p), sqShiftFactor Q T p (ν p) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    rw [Finset.mem_filter] at hp
    have : Fact p.Prime := ⟨hS p hp.1⟩
    exact sqShiftFactor_of_anisotropic Q hQ hn p S₀ hp.2 T hT.ne' (hst p hp.1) (ν p)
  have h2 : ∏ p ∈ S.filter (IsIsotropicPrime Q), sqShiftFactor Q T p (ν p) =
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
      ∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν p)) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    have : Fact p.Prime := ⟨hS p hp.1⟩
    rw [sqShiftFactor_eq_bracket Q hQ hn p S₀ T hT.ne' (hst p hp.1) (ν p), ← pow_mul, mul_comm (ν p)]
  rw [h1, h2]
  ring

open Classical in
/-- **Theorem 5.4 for $n \ge 4$** (Hanke 2004, p. 369), with `aE` (absolutely convergent Euler products):
$$a_E^{\mathrm{loc}}(T'(m')^2) = a_E^{\mathrm{loc}}(T')\prod_{p \in S \cap \mathrm{Iso}}\Big[C_p(T') +
  \frac{1 - C_p(T')}{q^{(n-2)\nu_p}}\Big]\big((m')_{\mathrm{Iso}}\big)^{n-2}.$$ -/
@[kb "hanke2004" "Thm 5.4, p. 369"]
theorem thm_5_4_aE (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    aE Q (T * sqPart S ν ^ 2) = aE Q T *
      (∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν p))) *
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) := by
  have hm : T * sqPart S ν ^ 2 ≠ 0 := mul_ne_zero hT.ne' (pow_ne_zero _ (sqPart_pos hS ν).ne')
  exact thm_5_4 Q hQ (by omega) hS S₀ hT hst ν (isEulerProductValue_eulerProduct Q hQ hn hT.ne')
    (isEulerProductValue_eulerProduct Q hQ hn hm)

/-! ### Lower bounds: (5.13) and Theorem 5.7 -/

/-- **(5.11) times $q^{(n-2)\nu}$:** $C'_p(T')\,q^{(n-2)\nu} \le F_p(T', \nu)$ for $T' \ne 0$ $p$-stable ($n \ge 3$). -/
theorem sqShiftFactor_ge (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ p T) (ν : ℕ) :
    localConstC' Q p T * (p : ℝ) ^ ((n - 2) * ν) ≤ sqShiftFactor Q T p ν := by
  have hp : (0 : ℝ) ≤ (p : ℝ) ^ ((n - 2) * ν) :=
    pow_nonneg (by exact_mod_cast (Fact.out : p.Prime).pos.le) _
  rw [sqShiftFactor, mul_comm]
  exact mul_le_mul_of_nonneg_left (localDensity_pow_sq_div_ge Q hQ hn p S₀ T hT0 hT ν) hp

/-- $C'_p(T') \ge 0$. -/
theorem localConstC'_nonneg (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (T : ℤ) (hT0 : T ≠ 0) : 0 ≤ localConstC' Q p T :=
  le_min zero_le_one (localConstC_nonneg Q hQ hn p T hT0)

/-- **A prime with $C'_p(T') > 0$ is isotropic** (contrapositive of `localConstC_eq_zero_of_anisotropic`). -/
theorem isIsotropicPrime_of_localConstC'_pos (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (S₀ : Finset (Fin n)) (T : ℤ) (hT : IsPStable Q S₀ p T) (h : 0 < localConstC' Q p T) :
    IsIsotropicPrime Q p := by
  rw [isIsotropicPrime_iff]
  by_contra haniso
  have h0 := (localConstC_eq_zero_of_anisotropic Q p S₀ haniso T hT).2
  rw [localConstC', h0, min_eq_right zero_le_one] at h
  exact lt_irrefl _ h

open Classical in
/-- **The product of the $F_p$, bounded below** (the local engine of (5.13) and Thm 5.7). Let $Q$ be nondegenerate,
$n \ge 3$, $T' \ne 0$ $p$-stable at every $p \in S$, and let $G$ be a set of primes ("good" primes) with known lower
bounds $0 < c_p \le C'_p(T')$ for $p \in S \cap G$. Then
$$\big((m')_{\mathrm{Iso}}\big)^{n-2}\prod_{p \in S \cap \mathrm{Iso},\ p \notin G} C'_p(T')\prod_{p \in S \cap G} c_p
  \;\le\; \prod_{p \in S} F_p(T', \nu_p).$$
(Every $p \in S \cap G$ is isotropic, since $C'_p(T') > 0$.) -/
theorem prod_sqShiftFactor_ge (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT0 : T ≠ 0)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) (G : ℕ → Prop) (c : ℕ → ℝ)
    (hc : ∀ p ∈ S, G p → 0 < c p ∧ c p ≤ localConstC' Q p T) :
    (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ G p), localConstC' Q p T) *
        ∏ p ∈ S.filter G, c p ≤
      ∏ p ∈ S, sqShiftFactor Q T p (ν p) := by
  have hiso : ∀ p ∈ S, G p → IsIsotropicPrime Q p := fun p hp hG => by
    have : Fact p.Prime := ⟨hS p hp⟩
    exact isIsotropicPrime_of_localConstC'_pos Q p S₀ T (hst p hp)
      ((hc p hp hG).1.trans_le (hc p hp hG).2)
  set d : ℕ → ℝ := fun p => if G p then c p else localConstC' Q p T with hd
  have hGeq : (S.filter (IsIsotropicPrime Q)).filter G = S.filter G := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hiso p h1 h3⟩, h3⟩
  have e1 : (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ G p), localConstC' Q p T) *
        ∏ p ∈ S.filter G, c p = ∏ p ∈ S.filter (IsIsotropicPrime Q), d p := by
    rw [← Finset.prod_filter_mul_prod_filter_not (S.filter (IsIsotropicPrime Q)) G, hGeq, mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun p hp => by
        rw [Finset.mem_filter] at hp; simp [hd, hp.2]
    · exact Finset.prod_congr rfl fun p hp => by
        rw [Finset.mem_filter] at hp; simp [hd, hp.2]
  rw [mul_assoc, e1, ← Finset.prod_pow, ← Finset.prod_mul_distrib, Finset.prod_filter]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have : Fact p.Prime := ⟨hS p hp⟩
    have hd0 : 0 ≤ d p := by
      simp only [hd]; split_ifs with hG
      · exact (hc p hp hG).1.le
      · exact localConstC'_nonneg Q hQ hn p T hT0
    split_ifs <;> positivity
  · have : Fact p.Prime := ⟨hS p hp⟩
    split_ifs with hI
    · have hdC : d p ≤ localConstC' Q p T := by
        simp only [hd]; split_ifs with hG
        · exact (hc p hp hG).2
        · exact le_rfl
      have hp0 : (0 : ℝ) ≤ (p : ℝ) ^ ν p := pow_nonneg (by exact_mod_cast (hS p hp).pos.le) _
      calc ((p : ℝ) ^ ν p) ^ (n - 2) * d p
          ≤ localConstC' Q p T * (p : ℝ) ^ ((n - 2) * ν p) := by
            rw [mul_comm, mul_comm (n - 2), pow_mul]
            exact mul_le_mul_of_nonneg_right hdC (pow_nonneg hp0 _)
        _ ≤ _ := sqShiftFactor_ge Q hQ hn p S₀ T hT0 (hst p hp) (ν p)
    · exact (sqShiftFactor_of_anisotropic Q hQ hn p S₀ hI T hT0 (hst p hp) (ν p)).ge

/-- **Hanke's $D$ is positive for positive definite $Q$** (`exists_sqrt_factor`). -/
theorem gramDet_pos {Q : IntQF n} (hQ : IntQF.PosDef Q) : 0 < gramDet Q := by
  obtain ⟨_, -, hdetpos, -⟩ := exists_sqrt_factor (gramMatrix Q) (gramMatrix_isHermitian Q)
    (fun x hx => by rw [← evalIn_real_eq_gram]; exact hQ.evalIn_real_pos x hx)
  rw [gramDet_eq_det]; exact hdetpos

/-- $\beta_\infty(m) \ge 0$ for $Q$ positive definite and $m \ge 0$. -/
theorem betaInf_nonneg {Q : IntQF n} (hQ : IntQF.PosDef Q) {m : ℝ} (hm : 0 ≤ m) : 0 ≤ betaInf Q m := by
  have h1 : 0 ≤ unitBallVol n := ENNReal.toReal_nonneg
  have h2 : 0 ≤ gramDet Q ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (gramDet_pos hQ).le _
  have h3 : 0 ≤ m ^ (((n : ℝ) - 2) / 2) := Real.rpow_nonneg hm _
  unfold betaInf
  positivity

/-- A natural-order value of the Euler product is $\ge 0$ ($Q$ nondegenerate, $m \ne 0$). -/
theorem IsEulerProductValue.nonneg {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {m : ℤ} (hm : m ≠ 0)
    {P : ℝ} (hP : IsEulerProductValue Q m P) : 0 ≤ P :=
  ge_of_tendsto' hP fun X => Finset.prod_nonneg fun p _ => by
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact localDensity_nonneg Q hQ p m hm

/-- $\beta_\infty(T')P \ge 0$ for $Q$ positive definite, $T' > 0$, $P$ a natural-order Euler-product value. -/
theorem aEWith_nonneg {Q : IntQF n} (hQ : IntQF.PosDef Q) {T : ℤ} (hT : 0 < T) {P : ℝ}
    (hP : IsEulerProductValue Q T P) : 0 ≤ aEWith Q T P :=
  mul_nonneg (betaInf_nonneg hQ (by exact_mod_cast hT.le)) (hP.nonneg hQ.nondegenerate hT.ne')

open Classical in
/-- **Lower bound for $a_E^{\mathrm{loc}}(m)/a_E^{\mathrm{loc}}(T')$ with good primes** (the common form of (5.13) and
Thm 5.7): for $Q$ positive definite, $n \ge 3$, $T' > 0$ $p$-stable at every $p \in S$, natural-order Euler-product values
$P$, $P_m$, and $0 < c_p \le C'_p(T')$ for $p \in S \cap G$:
$$\beta_\infty(T')P\,\big((m')_{\mathrm{Iso}}\big)^{n-2}\prod_{p \in S \cap \mathrm{Iso},\ p \notin G}C'_p(T')\prod_{p \in S \cap G}c_p
  \;\le\; \beta_\infty(m)P_m.$$ -/
theorem aEWith_mul_sq_ge (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 3 ≤ n) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) (G : ℕ → Prop) (c : ℕ → ℝ)
    (hc : ∀ p ∈ S, G p → 0 < c p ∧ c p ≤ localConstC' Q p T) {P Pm : ℝ}
    (hP : IsEulerProductValue Q T P) (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) Pm) :
    aEWith Q T P * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ G p), localConstC' Q p T) *
        ∏ p ∈ S.filter G, c p ≤
      aEWith Q (T * sqPart S ν ^ 2) Pm := by
  have hQnd := hQ.nondegenerate
  have hβ : ∀ p ∈ S, localDensity Q p T ≠ 0 := fun p hp => by
    have : Fact p.Prime := ⟨hS p hp⟩
    exact (localDensity_pos_of_isLocallyRepresentedAt Q hQnd p T hT.ne' (hst p hp).1).ne'
  rw [aEWith_mul_sq Q (by omega) hS ν hT.le hβ hP hPm, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (aEWith_nonneg hQ hT hP)
  rw [← mul_assoc]
  exact prod_sqShiftFactor_ge Q hQnd hn hS S₀ hT.ne' hst ν G c hc

open Classical in
/-- **(5.13)** (Hanke 2004, p. 373), local product, any $n \ge 3$: for $Q$ positive definite, $T' > 0$ $p$-stable at
every $p \in S$, $m = T'(m')^2$ with $m' = \prod_{p \in S}p^{\nu_p}$, and natural-order Euler-product values $P$, $P_m$,
$$\beta_\infty(m)P_m \;\ge\; \beta_\infty(T')P\,\big((m')_{\mathrm{Iso}}\big)^{n-2}\prod_{p \in S \cap \mathrm{Iso}}C'_p(T').$$
The paper's product runs over all $p \in \mathrm{Stable}(T') \cap \mathrm{Iso}$; since $C'_p \le 1$, the product over
$S \subseteq \mathrm{Stable}(T')$ gives a stronger bound. -/
@[kb "hanke2004" "(5.13), p. 373"]
theorem eq_5_13 (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 3 ≤ n) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) {P Pm : ℝ}
    (hP : IsEulerProductValue Q T P) (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) Pm) :
    aEWith Q T P * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), localConstC' Q p T ≤
      aEWith Q (T * sqPart S ν ^ 2) Pm := by
  have h := aEWith_mul_sq_ge Q hQ hn hS S₀ hT hst ν (fun _ => False) (fun _ => 1)
    (fun _ _ h => h.elim) hP hPm
  simpa using h

open Classical in
/-- **(5.13) for $n \ge 4$** (Hanke 2004, p. 373), with `aE`:
$a_E^{\mathrm{loc}}(m) \ge a_E^{\mathrm{loc}}(T')\,((m')_{\mathrm{Iso}})^{n-2}\prod_{p \in S \cap \mathrm{Iso}}C'_p(T')$. -/
@[kb "hanke2004" "(5.13), p. 373"]
theorem eq_5_13_aE (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    aE Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), localConstC' Q p T ≤
      aE Q (T * sqPart S ν ^ 2) := by
  have hm : T * sqPart S ν ^ 2 ≠ 0 := mul_ne_zero hT.ne' (pow_ne_zero _ (sqPart_pos hS ν).ne')
  exact eq_5_13 Q hQ (by omega) hS S₀ hT hst ν
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate hn hT.ne')
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate hn hm)

/-! ### Good primes and the character -/

/-- **Good primes** for the local results over $\mathbb{Q}$: $p$ odd prime with $p \nmid \det H$. At such $p$ the form has
the counts of a $p$-unimodular diagonal form (`exists_diag_unimodular_same_counts_det`), and Table 2 applies.
*Relation to the paper's $p \nmid N$ ($N$ the level):* for odd $p$, $p \mid N \iff p \mid \det H$; for $n$ odd also
$2 \mid N$, so "good" is exactly $p \nmid N$ when $n$ is odd. For $n$ even, $p = 2 \nmid N$ can happen; such $p = 2$ is
treated as bad here (the dyadic Table 2 is not formalized over $\mathbb{Q}$), which only weakens the bounds by the factor
$C'_2(T') \le 1$. -/
def IsGoodPrime (Q : QuadForm ℤ n) (p : ℕ) : Prop := p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ Q.hessian.det

theorem two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ((2 : ℤ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have : p ∣ 2 := by exact_mod_cast h
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem two_ne_zero_zmod' (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have := two_ne_zero_zmod p hp; push_cast at this; exact this

theorem intCast_ne_zero_zmod {p : ℕ} {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) : (u : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hu

/-- **The character at a good prime, $n$ even:** if $2^n\prod_i a_i = u^2\det H$ with $p \nmid u$, then
$\left(\frac{\prod_i a_i}{p}\right) = \left(\frac{\det H}{p}\right)$; so $\Phi_n(p) = \left(\frac{(-1)^{n/2}D}{p}\right)$ with Hanke's
$D = \det H/2^n$ (p. 357) is $\left(\frac{(-1)^{n/2}\det H}{p}\right)$. -/
theorem legendreSym_prod_eq_even (Q : QuadForm ℤ n) (heven : Even n) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (a : Fin n → ℤ) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u)
    (h : 2 ^ n * ∏ i, a i = u ^ 2 * Q.hessian.det) (s : ℕ) :
    legendreSym p ((-1) ^ s * ∏ i, a i) = legendreSym p ((-1) ^ s * Q.hessian.det) := by
  obtain ⟨k, rfl⟩ := heven
  have e := congrArg (legendreSym p) h
  rw [show (2 : ℤ) ^ (k + k) = (2 ^ k) ^ 2 by ring, legendreSym.mul, legendreSym.mul,
    legendreSym.sq_one' p (by push_cast; exact pow_ne_zero _ (two_ne_zero_zmod' p hp)),
    legendreSym.sq_one' p (intCast_ne_zero_zmod hu), one_mul, one_mul] at e
  rw [legendreSym.mul, legendreSym.mul, e]

/-- **The character at a good prime, $n$ odd:** if $2^n\prod_i a_i = u^2\det H$ with $p \nmid u$, then
$\left(\frac{\prod_i a_i}{p}\right) = \left(\frac{2\det H}{p}\right)$; so $\Phi_n(p) = \left(\frac{(-1)^{(n-1)/2}DT'}{p}\right)$ is
$\left(\frac{(-1)^{(n-1)/2}\,2\det H\,T'}{p}\right)$. -/
theorem legendreSym_prod_eq_odd (Q : QuadForm ℤ n) (hodd : Odd n) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (a : Fin n → ℤ) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u)
    (h : 2 ^ n * ∏ i, a i = u ^ 2 * Q.hessian.det) (s : ℕ) (T : ℤ) :
    legendreSym p ((-1) ^ s * (∏ i, a i) * T) =
      legendreSym p ((-1) ^ s * (2 * Q.hessian.det) * T) := by
  obtain ⟨k, rfl⟩ := hodd
  have e := congrArg (legendreSym p) h
  rw [show (2 : ℤ) ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 by ring, legendreSym.mul, legendreSym.mul,
    legendreSym.mul,
    legendreSym.sq_one' p (by push_cast; exact pow_ne_zero _ (two_ne_zero_zmod' p hp)),
    legendreSym.sq_one' p (intCast_ne_zero_zmod hu), mul_one, one_mul] at e
  have h2 := legendreSym.sq_one p (two_ne_zero_zmod p hp)
  have : legendreSym p (∏ i, a i) = legendreSym p 2 * legendreSym p Q.hessian.det := by
    linear_combination (-(legendreSym p (∏ i, a i))) * h2 + legendreSym p 2 * e
  rw [legendreSym.mul p ((-1) ^ s * ∏ i, a i) T, legendreSym.mul p ((-1) ^ s) (∏ i, a i),
    legendreSym.mul p ((-1) ^ s * (2 * Q.hessian.det)) T, legendreSym.mul p ((-1) ^ s),
    legendreSym.mul p 2, this]

/-- **$C'_p(T') = 1$ at good primes for $n = 3$** (Hanke 2004, (5.12), p. 371; first part of Thm 5.7(a)), for
$\mathrm{ord}_p(T') \le 1$. -/
theorem localConstC'_good_three (Q : QuadForm ℤ 3) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (T : ℤ) (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localConstC' Q p T = 1 := by
  obtain ⟨a, ha, hcnt, -⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  rw [localConstC', (localDensity_congr_of_repCount Q _ p hcnt T).2.2, ← localConstC']
  exact localConstC'_diag_three a p hp ha T hT2

/-- **$C'_p(T')$ at good primes, $n \ge 4$ even** (Table 2, p. 370; (5.12) corrected): with $X = q^{(n-2)/2}$ and
$\Phi_n(p) = \left(\frac{(-1)^{n/2}\det H}{p}\right)$, for $\mathrm{ord}_p(T') \le 1$,
$C'_p(T') = X/(X+1)$ if $\Phi_n(p) = -1$ and $p \nmid T'$, and $C'_p(T') = 1$ otherwise. -/
theorem localConstC'_good_even (Q : QuadForm ℤ n) (hn : 4 ≤ n) (heven : Even n) (p : ℕ)
    [Fact p.Prime] (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (T : ℤ)
    (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localConstC' Q p T =
      if jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T then
        (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) else 1 := by
  obtain ⟨a, ha, hcnt, u, hu, hprod⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  rw [localConstC', (localDensity_congr_of_repCount Q _ p hcnt T).2.2, ← localConstC']
  have hχ : jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p =
      legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) := by
    rw [legendreSym_prod_eq_even Q heven p hp a hu hprod, jacobiSym.legendreSym.to_jacobiSym]
  by_cases hpT : (p : ℤ) ∣ T
  · split_ifs with hc
    · exact absurd hpT hc.2
    · exact localConstC'_diag_ord_one a p hp ha (by omega) T hpT hT2
  · have h0 : (((-1) ^ (n / 2) * ∏ i, a i : ℤ) : ZMod p) ≠ 0 := by
      push_cast
      exact mul_ne_zero (by exact_mod_cast LocalDensity.neg_one_pow_ne_zero_zmod p _)
        (by exact_mod_cast LocalDensity.prod_ne_zero_zmod a p ha)
    have hC := localConstC'_diag_even_unit a p hp ha hn heven T hpT
    rcases legendreSym.eq_one_or_neg_one p h0 with h | h
    · rw [hC.1 h]
      split_ifs with hc
      · rw [hχ, h] at hc; exact absurd hc.1 (by decide)
      · rfl
    · rw [hC.2 h]
      split_ifs with hc
      · rfl
      · exact absurd ⟨by rw [hχ, h], hpT⟩ hc

/-- **$C'_p(T')$ at good primes, $n \ge 3$ odd** (Table 2, p. 370; (5.12) corrected): with
$\Phi_n(p) = \left(\frac{(-1)^{(n-1)/2}\,2\det H\,T'}{p}\right)$, for $\mathrm{ord}_p(T') \le 1$,
$C'_p(T') = \frac{1 - q^{-(n-1)/2}}{1 - q^{-(n-2)}}$ (the local factor of $\zeta(n-2)/\zeta((n-1)/2)$) if $p \nmid T'$ and
$\Phi_n(p) = 1$, and $C'_p(T') = 1$ otherwise. -/
theorem localConstC'_good_odd (Q : QuadForm ℤ n) (hn : 3 ≤ n) (hodd : Odd n) (p : ℕ)
    [Fact p.Prime] (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (T : ℤ)
    (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localConstC' Q p T =
      if ¬ (p : ℤ) ∣ T ∧ jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1 then
        (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)) else 1 := by
  obtain ⟨a, ha, hcnt, u, hu, hprod⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  rw [localConstC', (localDensity_congr_of_repCount Q _ p hcnt T).2.2, ← localConstC']
  by_cases hpT : (p : ℤ) ∣ T
  · split_ifs with hc
    · exact absurd hpT hc.1
    · exact localConstC'_diag_ord_one a p hp ha hn T hpT hT2
  · have hχ : jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p =
        legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) := by
      rw [legendreSym_prod_eq_odd Q hodd p hp a hu hprod, jacobiSym.legendreSym.to_jacobiSym]
    have h0 : (((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T : ℤ) : ZMod p) ≠ 0 := by
      push_cast
      refine mul_ne_zero (mul_ne_zero ?_ ?_) (intCast_ne_zero_zmod hpT)
      · exact_mod_cast LocalDensity.neg_one_pow_ne_zero_zmod p _
      · exact_mod_cast LocalDensity.prod_ne_zero_zmod a p ha
    have hC := localConstC'_diag_odd_unit a p hp ha hn hodd T hpT
    rcases legendreSym.eq_one_or_neg_one p h0 with h | h
    · rw [(hC.2 h).1, (hC.2 h).2]
      split_ifs with hc
      · rfl
      · exact absurd ⟨hpT, by rw [hχ, h]⟩ hc
    · rw [hC.1 h]
      split_ifs with hc
      · rw [hχ, h] at hc; exact absurd hc.2 (by decide)
      · rfl

/-! ### Theorem 5.7 in ratio form -/

open Classical in
/-- **Theorem 5.7(a), first part** (Hanke 2004, p. 372; proof p. 374), ratio form, $n = 3$. Let $Q$ be a positive
definite ternary form, $S$ a finite set of primes, $T' > 0$ $p$-stable at every $p \in S$ with $\mathrm{ord}_p(T') \le 1$ at
the good $p \in S$, $m = T'(m')^2$ with $m' = \prod_{p \in S}p^{\nu_p}$, and $P$, $P_m$ the values of $\prod_p\beta_p(T')$,
$\prod_p\beta_p(m)$ in the natural order of the primes (the $n = 3$ convention is left open). Then
$$\beta_\infty(m)P_m \;\ge\; \Lambda_3(T')\,N\big((m')_{\mathrm{Iso}}\big), \qquad
  \Lambda_3(T') = \beta_\infty(T')P\prod_{p \in S \cap \mathrm{Iso},\ p \text{ bad}}C'_p(T'),$$
"bad" meaning $p = 2$ or $p \mid \det H$ (for $n = 3$: $p \mid N$). *Differences from the paper:* over $\mathbb{Q}$.
*Update (candidate; pending author):* the hypothesis "$T'$ not contained in a spinor square class" concerns $a_H$ and
is not needed for this $a_E$ bound; the
paper's product over $p \in S$, $p \mid N$, $p \in \mathrm{Iso}$ is the same. The second part of (a) (via
$L_F(1, \psi_t)$) is a global bound for $a_E(T')$ and is not formalized. -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part)"]
theorem thm_5_7_a (Q : IntQF 3) (hQ : IntQF.PosDef Q) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (S₀ : Finset (Fin 3)) {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {P Pm : ℝ}
    (hP : IsEulerProductValue Q T P) (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) Pm) :
    aEWith Q T P *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤
      aEWith Q (T * sqPart S ν ^ 2) Pm := by
  have h := aEWith_mul_sq_ge Q hQ le_rfl hS S₀ hT hst ν (IsGoodPrime Q) (fun _ => 1)
    (fun p hp hG => by
      have : Fact p.Prime := ⟨hS p hp⟩
      exact ⟨one_pos, (localConstC'_good_three Q p hG.2.1 hG.2.2 T (hT2 p hp hG)).ge⟩) hP hPm
  simp only [show 3 - 2 = 1 from rfl, pow_one, Finset.prod_const_one, mul_one] at h
  refine le_of_eq_of_le ?_ h
  ring

open Classical in
/-- **Theorem 5.7(c), $n \ge 4$ even (and (b) for $n = 4$), ratio form** (Hanke 2004, p. 373; proof pp. 374–375).
Let $Q$ be positive definite, $n \ge 4$ even, $S$ a finite set of primes, $T' > 0$ $p$-stable at every $p \in S$ with
$\mathrm{ord}_p(T') \le 1$ at the good $p \in S$, and $m = T'(m')^2$, $m' = \prod_{p \in S}p^{\nu_p}$. With
$X_p = q^{(n-2)/2}$ and $\Phi_n(p) = \left(\frac{(-1)^{n/2}\det H}{p}\right)$,
$$a_E^{\mathrm{loc}}(m) \;\ge\; a_E^{\mathrm{loc}}(T')\,\big((m')_{\mathrm{Iso}}\big)^{n-2}
  \prod_{p \in S \cap \mathrm{Iso},\ p\text{ bad}}C'_p(T')
  \prod_{\substack{p \in S\text{ good},\ p \nmid T'\\ \Phi_n(p) = -1}}\frac{X_p}{X_p + 1}.$$
$X/(X+1) = (1 - X^{-1})/(1 - X^{-2})$ is the local factor of $\zeta(n-2)/\zeta((n-2)/2)$ (proof of Thm 5.7, p. 374).
*What is left out:* the lower bound for $a_E(T')$ itself (the $L_F(n/2, \Phi_n)$, $\zeta_F$ factors and $\hat B_n(T')$)
and the minimum over $T' \in B_{\mathbb T}$; for $n \ge 5$ every prime is isotropic, so $(m')_{\mathrm{Iso}} = m'$ there
(not used here). Over $\mathbb{Q}$. -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even)"]
theorem thm_5_7_c_even (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n) (heven : Even n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    aE Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) ≤
      aE Q (T * sqPart S ν ^ 2) := by
  have hm : T * sqPart S ν ^ 2 ≠ 0 := mul_ne_zero hT.ne' (pow_ne_zero _ (sqPart_pos hS ν).ne')
  have h := aEWith_mul_sq_ge Q hQ (by omega) hS S₀ hT hst ν (IsGoodPrime Q)
    (fun p : ℕ => if jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T then
        (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) else 1)
    (fun p hp hG => by
      have : Fact p.Prime := ⟨hS p hp⟩
      rw [localConstC'_good_even Q hn heven p hG.2.1 hG.2.2 T (hT2 p hp hG)]
      refine ⟨?_, le_rfl⟩
      have : (0 : ℝ) < (p : ℝ) ^ ((n - 2) / 2) := pow_pos (by exact_mod_cast (hS p hp).pos) _
      split_ifs <;> positivity)
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate (by omega) hT.ne')
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate (by omega) hm)
  rwa [← Finset.prod_filter] at h

open Classical in
/-- **Theorem 5.7(b)** (Hanke 2004, p. 373; proof p. 375), ratio form, $n = 4$: with $\chi(p) = \left(\frac{\det H}{p}\right)$
(the character of $\mathbb{Q}(\sqrt{D})$, $D = \det H/16$), under the hypotheses of `thm_5_7_c_even`,
$$a_E^{\mathrm{loc}}(m) \;\ge\; a_E^{\mathrm{loc}}(T')\,N\big((m')_{\mathrm{Iso}}\big)^{2}\prod_{p \in S \cap \mathrm{Iso},\ p\text{ bad}}C'_p(T')
  \prod_{\substack{p \in S\text{ good},\ p \nmid T'\\ \chi(p) = -1}}\Big(1 + \frac1q\Big)^{-1}.$$
This is the paper's display on p. 375 divided by its lower bound for $a_E(T')$: there the last product runs over
$p \mid m'$, $p \nmid N$, $\chi(p) = -1$ (here additionally $p \nmid T'$, where $C'_p(T') = 1$, so the bound is slightly
sharper); with $S$ the set of primes dividing $m'$ it is that product. The factor $\frac{q-1}{q+1}$ of the statement
of (b) combines this with the factor $1 - \frac1q$ at $p \mid T'$ from the bound for $a_E(T')$ (global, not formalized). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form)"]
theorem thm_5_7_b (Q : IntQF 4) (hQ : IntQF.PosDef Q) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (S₀ : Finset (Fin 4)) {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    aE Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ 2 *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym Q.hessian.det p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (1 + 1 / (p : ℝ))⁻¹ ≤
      aE Q (T * sqPart S ν ^ 2) := by
  have h := thm_5_7_c_even Q hQ le_rfl (by decide) hS S₀ hT hst hT2 ν
  simp only [show 4 / 2 = 2 from rfl, show (4 - 2) / 2 = 1 from rfl, show 4 - 2 = 2 from rfl,
    pow_one, neg_one_sq, one_mul] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have : (0 : ℝ) < p := by
    simp only [Finset.mem_filter] at hp; exact_mod_cast hp.1.2.1.pos
  field_simp

open Classical in
/-- **Theorem 5.7(c), $n \ge 5$ odd (and $n = 3$), ratio form** (Hanke 2004, p. 373; proof pp. 375–376). Under the
hypotheses of `thm_5_7_c_even` with $n$ odd, and $\Phi_n(p) = \left(\frac{(-1)^{(n-1)/2}\,2\det H\,T'}{p}\right)$ (Hanke's
$\left(\frac{(-1)^{(n-1)/2}DT'}{p}\right)$, $D = \det H/2^n$),
$$a_E^{\mathrm{loc}}(m) \;\ge\; a_E^{\mathrm{loc}}(T')\,\big((m')_{\mathrm{Iso}}\big)^{n-2}\prod_{p \in S \cap \mathrm{Iso},\ p\text{ bad}}C'_p(T')
  \prod_{\substack{p \in S\text{ good},\ p \nmid T'\\ \Phi_n(p) = 1}}\frac{1 - q^{-(n-1)/2}}{1 - q^{-(n-2)}},$$
the last factor being the local factor of $\zeta(n-2)/\zeta((n-1)/2)$ (p. 375). Stated with `aE`, so for $n \ge 4$
(i.e. $n \ge 5$); for $n = 3$ see `thm_5_7_a` (where the last product is $1$). Left out: the global bound (5.14)
for $a_E(T')$ ($L_F((n-1)/2, \Phi_n)/\zeta_F(n-1)$, $\hat B_n(T')$) and the minimum over $B_{\mathbb T}$. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (ratio form, n odd)"]
theorem thm_5_7_c_odd (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n) (hodd : Odd n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    aE Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter (fun p : ℕ => ¬ (p : ℤ) ∣ T ∧
            jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1),
          (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)) ≤
      aE Q (T * sqPart S ν ^ 2) := by
  have hm : T * sqPart S ν ^ 2 ≠ 0 := mul_ne_zero hT.ne' (pow_ne_zero _ (sqPart_pos hS ν).ne')
  have h := aEWith_mul_sq_ge Q hQ (by omega) hS S₀ hT hst ν (IsGoodPrime Q)
    (fun p : ℕ => if ¬ (p : ℤ) ∣ T ∧
        jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1 then
        (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)) else 1)
    (fun p hp hG => by
      have : Fact p.Prime := ⟨hS p hp⟩
      rw [localConstC'_good_odd Q (by omega) hodd p hG.2.1 hG.2.2 T (hT2 p hp hG)]
      refine ⟨?_, le_rfl⟩
      have h1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
      have h2 : 1 / (p : ℝ) ^ ((n - 1) / 2) < 1 := by
        rw [div_lt_one (by positivity)]; exact one_lt_pow₀ h1 (by omega)
      have h3 : 1 / (p : ℝ) ^ (n - 2) < 1 := by
        rw [div_lt_one (by positivity)]; exact one_lt_pow₀ h1 (by omega)
      split_ifs
      · exact div_pos (by linarith) (by linarith)
      · exact one_pos)
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate hn hT.ne')
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate hn hm)
  rwa [← Finset.prod_filter] at h

end QuadFormsKB.Siegel
