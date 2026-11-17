/-
# Jacobi's theta-series identities for two and four squares (historical library)

**Library** `QuadFormsKB.Historical.Jacobi` (a separate `lean_lib`, not imported by `QuadFormsKB`).  Targets
:

* (Jacobi, letter to Legendre, 9 Sept. 1828; *Fundamenta nova* (1829), § 40; reported by Dickson,
  *History of the Theory of Numbers* II (1920), ch. VI, p. 235, occurrences `dickson1920-history2:p235.1`, `p235.4`):
  for $|q| < 1$,
  $$\Bigl(\sum_{n\in\mathbb Z} q^{n^2}\Bigr)^2 = 1 + 4\sum_{k\ge0} (-1)^k\,\frac{q^{2k+1}}{1-q^{2k+1}}
    = 1 + 4\sum_{x \ge 1} A(x)\,q^x,$$
  $A(x)$ = (number of divisors $\equiv 1 \bmod 4$) $-$ (number of divisors $\equiv 3 \bmod 4$) of $x$:
  `jacobi_theta_sq_lambert`, `jacobi_theta_sq_divisor_excess`. **Proved.**
* (Gauss, posthumous manuscript, *Werke* 3, pp. 383–384; Jacobi, *J. reine angew. Math.* 3 (1828),
  p. 191; Dickson II, ch. VIII, pp. 283, 285, occurrences `dickson1920-history2:p283.1c`, `p285.4`, `p285.4b`): for $|y| < 1$,
  $$\Bigl(\sum_{n\in\mathbb Z} y^{n^2}\Bigr)^4 = 1 + 8\sum_{n\ge1}\frac{n\,y^n}{1+(-y)^n},$$
  equivalently $r_4(m) = 8\sum_{d\mid m,\ 4\nmid d} d$ for $m \ge 1$, and $r_4(2^\alpha p) = 8\sigma(p)$ or $24\sigma(p)$
  ($p$ odd) according as $\alpha = 0$ or $\alpha > 0$: `gauss_theta_four_lambert` (**proved**),
  `jacobi_four_squares_count` (**wrapper** of `Siegel.repNum_sumSq_four`), `jacobi_four_squares_two_pow_mul`
  (**wrapper** of `MorenoWagstaff.theorem26`, Moreno–Wagstaff Theorem 2.6).

**Notation.** $\theta(q) = \sum_{n\in\mathbb Z} q^{n^2}$ is `thetaQ q` (exponent written $|n|^2$ so that it is a natural
number); it is Mathlib's `jacobiTheta τ` at $q = e^{\pi i \tau}$ (`jacobiTheta_eq_thetaQ`). The number of representations
$r_k(m) = \#\{\vec x\in\mathbb Z^k : x_0^2+\dots+x_{k-1}^2 = m\}$ is the library's `Siegel.repNum (Siegel.sumSq k) m`
(variables indexed from $0$).

**Proof route.** $\theta(q)^k = \sum_m r_k(m) q^m$ for $k = 2, 4$ (`hasSum_thetaQ_sq`, `hasSum_thetaQ_pow_four`: products
of absolutely convergent series, regrouped by the value of the form), then the closed forms of $r_2$ (Moreno–Wagstaff
Theorem 2.5, `MorenoWagstaff.theorem25`) and $r_4$ (`Siegel.repNum_sumSq_four`), and the expansion of a Lambert series
$\sum_d \sum_{j\ge1} f(d, j) q^{dj}$ as a power series (`hasSum_lambert`, regrouping by $n = dj$).

*Credit:* `hasSum_sum_divisorsAntidiagonal` is copied from Tau Ceti (`TauCeti/NumberTheory/TsumDivisorsAntidiagonal.lean`,
`HasSum.sum_divisorsAntidiagonal`, The Tau Ceti contributors, Apache 2.0), not imported.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2ProofsB
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

open scoped ArithmeticFunction.sigma

namespace QuadFormsKB.Historical.Jacobi

open QuadFormsKB.Siegel Complex

/-! ### The theta series $\theta(q) = \sum_{n\in\mathbb Z} q^{n^2}$ -/

/-- **The theta series** $\theta(q) = \sum_{n\in\mathbb Z} q^{n^2} = 1 + 2q + 2q^4 + 2q^9 + \cdots$ (Jacobi's
$\sqrt{2K/\pi}$; Dickson II, ch. VI, p. 235 and ch. VIII, p. 285), for $q \in \mathbb C$; it converges absolutely for
$|q| < 1$ (`summable_norm_thetaQ`). The exponent $n^2$ is written $|n|^2$, a natural number. -/
@[kb "jacobi1829" "Fundamenta nova, § 40, the series 1 + 2q + 2q^4 + 2q^9 + ⋯ [unverified locator]"]
noncomputable def thetaQ (q : ℂ) : ℂ := ∑' n : ℤ, q ^ (n.natAbs ^ 2)

/-- The modern normalization: Mathlib's `jacobiTheta τ` $= \sum_n e^{\pi i n^2\tau}$ is $\theta(e^{\pi i\tau})$. -/
theorem jacobiTheta_eq_thetaQ (τ : ℂ) : jacobiTheta τ = thetaQ (cexp (Real.pi * I * τ)) := by
  unfold jacobiTheta thetaQ
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  have h1 : ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := by rw [Nat.cast_pow]; exact Int.natAbs_sq n
  have h : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
    rw [← Int.cast_natCast, h1]; push_cast; ring
  rw [h]; ring

lemma summable_geometric_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℤ => r ^ n.natAbs := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_geometric_of_lt_one hr0 hr
  · simpa using summable_geometric_of_lt_one hr0 hr

/-- $\theta(q)$ converges absolutely for $|q| < 1$. -/
theorem summable_norm_thetaQ {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℤ => ‖q ^ (n.natAbs ^ 2)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_natAbs (norm_nonneg q) hq)
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hq.le (Nat.le_self_pow two_ne_zero _)

/-- Regrouping $\sum_x q^{v(x)}$ by the value $m = v(x)$: the coefficient of $q^m$ is $\#v^{-1}(m)$. -/
lemma hasSum_fiber {X : Type*} (v : X → ℕ) {q : ℂ} {f : X → ℂ} (hf : ∀ x, f x = q ^ v x) {a : ℂ}
    (h : HasSum f a) : HasSum (fun m : ℕ => (Nat.card (v ⁻¹' {m}) : ℂ) * q ^ m) a := by
  have h' := h.tsum_fiberwise v
  convert h' using 1
  funext m
  have hc : ∀ b : v ⁻¹' {m}, f b = q ^ m := fun b => by
    rw [hf, show v b = m from b.2]
  rw [tsum_congr hc, tsum_const, nsmul_eq_mul]

/-- $r_2(m)$ counts pairs $(a, b) \in \mathbb Z^2$ with $|a|^2 + |b|^2 = m$. -/
lemma repNum_sumSq_two_eq_card (m : ℕ) :
    repNum (sumSq 2) m =
      Nat.card ((fun p : ℤ × ℤ => p.1.natAbs ^ 2 + p.2.natAbs ^ 2) ⁻¹' {m}) := by
  unfold repNum
  refine Nat.card_congr (Equiv.subtypeEquiv (finTwoArrowEquiv ℤ) fun x => ?_)
  show (sumSq 2).eval x = (m : ℤ) ↔ (x 0).natAbs ^ 2 + (x 1).natAbs ^ 2 = m
  rw [eval_sumSq, Fin.sum_univ_two, ← Nat.cast_inj (R := ℤ)]
  push_cast
  simp only [sq_abs]

/-- The equivalence $\mathbb Z^4 \simeq \mathbb Z^2 \times \mathbb Z^2$, $\vec x \mapsto ((x_0, x_1), (x_2, x_3))$. -/
def fin4Pairs : (Fin 4 → ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun x := ((x 0, x 1), (x 2, x 3))
  invFun P := ![P.1.1, P.1.2, P.2.1, P.2.2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- $r_4(m)$ counts pairs of pairs with $(|a|^2 + |b|^2) + (|c|^2 + |d|^2) = m$. -/
lemma repNum_sumSq_four_eq_card (m : ℕ) :
    repNum (sumSq 4) m =
      Nat.card ((fun P : (ℤ × ℤ) × (ℤ × ℤ) =>
        (P.1.1.natAbs ^ 2 + P.1.2.natAbs ^ 2) + (P.2.1.natAbs ^ 2 + P.2.2.natAbs ^ 2)) ⁻¹' {m}) := by
  unfold repNum
  refine Nat.card_congr (Equiv.subtypeEquiv fin4Pairs fun x => ?_)
  show (sumSq 4).eval x = (m : ℤ) ↔
    ((x 0).natAbs ^ 2 + (x 1).natAbs ^ 2) + ((x 2).natAbs ^ 2 + (x 3).natAbs ^ 2) = m
  rw [eval_sumSq, Fin.sum_univ_four, ← Nat.cast_inj (R := ℤ)]
  push_cast
  simp only [sq_abs]
  constructor <;> intro h <;> linarith

/-- **$\theta(q)^2 = \sum_{m\ge0} r_2(m)\,q^m$** for $|q| < 1$. -/
theorem hasSum_thetaQ_sq {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => (repNum (sumSq 2) m : ℂ) * q ^ m) (thetaQ q ^ 2) := by
  have hs := summable_norm_thetaQ hq
  have hprod : HasSum (fun p : ℤ × ℤ => q ^ (p.1.natAbs ^ 2) * q ^ (p.2.natAbs ^ 2)) (thetaQ q ^ 2) := by
    rw [sq, thetaQ, tsum_mul_tsum_of_summable_norm hs hs]
    exact (summable_mul_of_summable_norm hs hs).hasSum
  have h := hasSum_fiber (q := q) (fun p : ℤ × ℤ => p.1.natAbs ^ 2 + p.2.natAbs ^ 2)
    (fun p => (pow_add _ _ _).symm) hprod
  simpa only [repNum_sumSq_two_eq_card] using h

/-- **$\theta(q)^4 = \sum_{m\ge0} r_4(m)\,q^m$** for $|q| < 1$. -/
theorem hasSum_thetaQ_pow_four {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => (repNum (sumSq 4) m : ℂ) * q ^ m) (thetaQ q ^ 4) := by
  have hs := summable_norm_thetaQ hq
  set F : ℤ × ℤ → ℂ := fun p => q ^ (p.1.natAbs ^ 2) * q ^ (p.2.natAbs ^ 2) with hFdef
  have hF : Summable fun p : ℤ × ℤ => ‖F p‖ := by
    simp only [hFdef, norm_mul]
    exact hs.mul_of_nonneg hs (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have h2 : ∑' p : ℤ × ℤ, F p = thetaQ q ^ 2 := by
    rw [sq, thetaQ, tsum_mul_tsum_of_summable_norm hs hs]
  have hprod : HasSum (fun P : (ℤ × ℤ) × (ℤ × ℤ) => F P.1 * F P.2) (thetaQ q ^ 4) := by
    rw [show thetaQ q ^ 4 = thetaQ q ^ 2 * thetaQ q ^ 2 by ring, ← h2,
      tsum_mul_tsum_of_summable_norm hF hF]
    exact (summable_mul_of_summable_norm hF hF).hasSum
  have h := hasSum_fiber (q := q) (fun P : (ℤ × ℤ) × (ℤ × ℤ) =>
      (P.1.1.natAbs ^ 2 + P.1.2.natAbs ^ 2) + (P.2.1.natAbs ^ 2 + P.2.2.natAbs ^ 2))
    (fun P => by simp only [hFdef, ← pow_add]) hprod
  simpa only [repNum_sumSq_four_eq_card] using h

/-! ### Lambert series as power series -/

/-- **Regrouping a double series by the product of the indices.** Copied from Tau Ceti
(`HasSum.sum_divisorsAntidiagonal`, The Tau Ceti contributors, Apache 2.0). -/
theorem hasSum_sum_divisorsAntidiagonal {f : ℕ → ℕ → ℂ} {a : ℂ}
    (hf : HasSum (fun p : ℕ+ × ℕ+ ↦ f p.1 p.2) a) :
    HasSum (fun n : ℕ+ ↦ ∑ x ∈ (n : ℕ).divisorsAntidiagonal, f x.1 x.2) a := by
  refine (sigmaAntidiagonalEquivProd.hasSum_iff.mpr hf).sigma fun n ↦ ?_
  have h := hasSum_fintype fun x : (n : ℕ).divisorsAntidiagonal ↦ f x.1.1 x.1.2
  rw [Finset.univ_eq_attach, Finset.sum_attach _ fun x : ℕ × ℕ ↦ f x.1 x.2] at h
  simpa [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors] using h

/-- **Lambert-type series as power series.** If $|f(d, j)| \le C d$ and $|q| < 1$, then
$$\sum_{d\ge1}\sum_{j\ge1} f(d, j)\,q^{dj} = \sum_{n\ge0}\Bigl(\sum_{dj = n} f(d, j)\Bigr) q^n.$$ -/
theorem hasSum_lambert {f : ℕ → ℕ → ℂ} {C : ℝ} (hf : ∀ d j, ‖f d j‖ ≤ C * d) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (∑ x ∈ n.divisorsAntidiagonal, f x.1 x.2) * q ^ n)
      (∑' d : ℕ+, ∑' j : ℕ+, f d j * q ^ ((d : ℕ) * j)) := by
  have hs : Summable (fun p : ℕ+ × ℕ+ => f p.1 p.2 * q ^ ((p.1 : ℕ) * p.2)) := by
    have hg := ((summable_prod_mul_pow 1 (r := ‖q‖) (by simpa using hq)).prod_symm).mul_left C
    refine Summable.of_norm_bounded hg fun p => ?_
    rw [norm_mul, norm_pow]
    simp only [Prod.fst_swap, Prod.snd_swap, pow_one]
    rw [mul_comm (p.2 : ℕ) (p.1 : ℕ), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by simpa using hf p.1 p.2) (by positivity)
  have h := hasSum_sum_divisorsAntidiagonal (f := fun d j => f d j * q ^ (d * j)) hs.hasSum
  rw [hs.tsum_prod] at h
  rw [← Function.Injective.hasSum_iff PNat.coe_injective]
  · convert h using 1
    funext n
    simp only [Function.comp_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  · intro n hn
    have : n = 0 := by
      by_contra h0
      exact hn ⟨⟨n, Nat.pos_of_ne_zero h0⟩, rfl⟩
    subst this
    simp

/-- $\sum_{j\ge1} q^{dj} = \dfrac{q^d}{1-q^d}$ for $d \ge 1$, $|q| < 1$. -/
lemma tsum_pnat_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ+) :
    ∑' j : ℕ+, q ^ ((d : ℕ) * j) = q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) := by
  have hd : ‖q ^ (d : ℕ)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq d.ne_zero
  rw [tsum_pnat_eq_tsum_succ (f := fun j => q ^ ((d : ℕ) * j))]
  have e : ∀ j : ℕ, q ^ ((d : ℕ) * (j + 1)) = q ^ (d : ℕ) * (q ^ (d : ℕ)) ^ j := by
    intro j; rw [mul_add, mul_one, pow_add, pow_mul]; ring
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hd, div_eq_mul_inv]

/-! ### Two squares -/

/-- **Jacobi's divisor excess** $A(x) = \#\{d \mid x : d \equiv 1 \bmod 4\} - \#\{d \mid x : d \equiv 3 \bmod 4\}$
(Dickson II, ch. VI, p. 235, the $A^{(x)}$ of Jacobi's *Fundamenta nova*); $A(0) = 0$. -/
def divisorExcess (x : ℕ) : ℤ :=
  ((x.divisors.filter (· % 4 = 1)).card : ℤ) - (x.divisors.filter (· % 4 = 3)).card

/-- $r_2(m) = 4A(m)$ for $m \ge 1$ (Moreno–Wagstaff Theorem 2.5, `MorenoWagstaff.theorem25`). -/
lemma repNum_sumSq_two_eq (m : ℕ) (hm : 1 ≤ m) : (repNum (sumSq 2) m : ℤ) = 4 * divisorExcess m :=
  (MorenoWagstaff.theorem25.1 m hm).2

/-- $\sum_{x} A(x)\,q^x = (\theta(q)^2 - 1)/4$. -/
theorem hasSum_divisorExcess {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun x : ℕ => (divisorExcess x : ℂ) * q ^ x) ((thetaQ q ^ 2 - 1) / 4) := by
  have h := ((hasSum_thetaQ_sq hq).sub (hasSum_ite_eq (0 : ℕ) (1 : ℂ))).div_const 4
  convert h using 2 with x
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [divisorExcess, repNum_zero_of_posDef posDef_sumSq]
  · have := repNum_sumSq_two_eq x hx
    rw [ite_eq_right hx.ne', sub_zero, show (repNum (sumSq 2) x : ℂ) = ((repNum (sumSq 2) x : ℤ) : ℂ) by simp,
      this]
    push_cast; ring

/-- **Jacobi's two-squares series, divisor form** (Dickson II, ch. VI, p. 235,
`dickson1920-history2:p235.4`: Jacobi's $2K/\pi = 1 + 4\sum_{x\ge1} A^{(x)} q^x$ with $2K/\pi = \theta(q)^2$): for $|q| < 1$,
$$\theta(q)^2 = 1 + 4\sum_{x \ge 0} A(x)\,q^x,$$
$A(x)$ the excess of the divisors $\equiv 1$ over those $\equiv 3 \pmod 4$ (`divisorExcess`; the $x = 0$ term is $0$).
**Proved** from Moreno–Wagstaff Theorem 2.5 (`MorenoWagstaff.theorem25`). -/
@[kb "dickson1920" "ch. VI, p. 235 (Jacobi, Fund. Nova § 40; occurrence dickson1920-history2:p235.4)"]
theorem jacobi_theta_sq_divisor_excess {q : ℂ} (hq : ‖q‖ < 1) :
    thetaQ q ^ 2 = 1 + 4 * ∑' x : ℕ, (divisorExcess x : ℂ) * q ^ x := by
  rw [(hasSum_divisorExcess hq).tsum_eq]; ring

/-- $\chi(d) = (-1)^{(d-1)/2}$ for odd $d$, $0$ for even $d$ (the character $\chi_{-4}$). -/
def chiOdd (d : ℕ) : ℂ := if Odd d then (-1) ^ ((d - 1) / 2) else 0

lemma norm_chiOdd_le (d : ℕ) : ‖chiOdd d‖ ≤ 1 * d := by
  unfold chiOdd
  split_ifs with h
  · simpa using (Nat.one_le_cast (α := ℝ)).mpr h.pos
  · simp

lemma sum_antidiag_chiOdd (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal, chiOdd x.1 = (divisorExcess n : ℂ) := by
  rw [Nat.sum_divisorsAntidiagonal (f := fun d _ => chiOdd d)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [divisorExcess]
  have h := (MorenoWagstaff.theorem25.1 n hn)
  have e : (divisorExcess n : ℤ) = ∑ d ∈ n.divisors.filter Odd, (-1 : ℤ) ^ ((d - 1) / 2) := by
    have := h.1.symm.trans h.2
    unfold divisorExcess; linarith
  rw [e, Finset.sum_filter]
  push_cast
  rfl

/-- **Jacobi's two-squares series, Lambert form** (Jacobi, letter to Legendre,
9 Sept. 1828, *J. reine angew. Math.* 80 (1875), p. 241, *Werke* 1, p. 424; Dickson II, ch. VI, p. 235,
`dickson1920-history2:p235.1`): for $|q| < 1$,
$$(1 + 2q + 2q^4 + 2q^9 + \cdots)^2 = 1 + \frac{4q}{1-q} - \frac{4q^3}{1-q^3} + \frac{4q^5}{1-q^5} - \cdots
  = 1 + 4\sum_{k\ge0}(-1)^k\frac{q^{2k+1}}{1-q^{2k+1}}.$$
**Proved** (Lambert expansion, `hasSum_lambert`, plus `jacobi_theta_sq_divisor_excess`). -/
@[kb "dickson1920" "ch. VI, p. 235 (Jacobi to Legendre, 9 Sept. 1828; occurrence dickson1920-history2:p235.1)"]
theorem jacobi_theta_sq_lambert {q : ℂ} (hq : ‖q‖ < 1) :
    thetaQ q ^ 2 = 1 + 4 * ∑' k : ℕ, (-1 : ℂ) ^ k * (q ^ (2 * k + 1) / (1 - q ^ (2 * k + 1))) := by
  have hL := hasSum_lambert (f := fun d _ => chiOdd d) (C := 1) (fun d _ => norm_chiOdd_le d) hq
  simp only [sum_antidiag_chiOdd] at hL
  have hu := hL.unique (hasSum_divisorExcess hq)
  -- the Lambert sum in the source's form
  have e : ∑' d : ℕ+, ∑' j : ℕ+, chiOdd d * q ^ ((d : ℕ) * j) =
      ∑' k : ℕ, (-1 : ℂ) ^ k * (q ^ (2 * k + 1) / (1 - q ^ (2 * k + 1))) := by
    simp_rw [tsum_mul_left, tsum_pnat_pow_mul hq]
    let g : ℕ → ℕ+ := fun k => ⟨2 * k + 1, Nat.succ_pos _⟩
    have hg : Function.Injective g := fun a b h => by
      have := congrArg PNat.val h; simp [g] at this; omega
    rw [← Function.Injective.tsum_eq hg (f := fun d : ℕ+ => chiOdd d * (q ^ (d : ℕ) / (1 - q ^ (d : ℕ))))]
    · refine tsum_congr fun k => ?_
      have hk : ((g k : ℕ)) = 2 * k + 1 := rfl
      simp only [hk, chiOdd, ite_eq_left (odd_two_mul_add_one k), show (2 * k + 1 - 1) / 2 = k by omega]
    · intro d hd
      have hodd : Odd (d : ℕ) := by
        by_contra h; exact hd (by simp [chiOdd, h])
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, PNat.coe_injective (by simp [g, hk])⟩
  rw [← e, hu]; ring

/-! ### Four squares -/

/-- $\sum_{d\mid m,\ 4\nmid d} d$ (Jacobi's divisor sum; $0$ at $m = 0$). -/
def sumDivNotFour (m : ℕ) : ℕ := ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d

/-- $\sum_m \bigl(\sum_{d\mid m, 4\nmid d} d\bigr) q^m = (\theta(q)^4 - 1)/8$. -/
theorem hasSum_sumDivNotFour {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => (sumDivNotFour m : ℂ) * q ^ m) ((thetaQ q ^ 4 - 1) / 8) := by
  have h := ((hasSum_thetaQ_pow_four hq).sub (hasSum_ite_eq (0 : ℕ) (1 : ℂ))).div_const 8
  convert h using 2 with m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sumDivNotFour, repNum_zero_of_posDef posDef_sumSq]
  · rw [ite_eq_right hm.ne', sub_zero, repNum_sumSq_four hm, sumDivNotFour]
    push_cast; ring

/-- The pairs $(d, j)$ with $dj = n$ and $d, j$ both even: $2 \sum d = \sum_{e \mid n,\ 4 \mid e} e$. -/
lemma sum_antidiag_both_even (n : ℕ) :
    2 * ∑ x ∈ n.divisorsAntidiagonal.filter (fun x => 2 ∣ x.1 ∧ 2 ∣ x.2), x.1 =
      ∑ d ∈ n.divisors.filter (4 ∣ ·), d := by
  rw [sum_divisors_four_dvd]
  split_ifs with h4
  · obtain ⟨k, rfl⟩ := h4
    have e : (4 * k).divisorsAntidiagonal.filter (fun x => 2 ∣ x.1 ∧ 2 ∣ x.2) =
        k.divisorsAntidiagonal.map ⟨fun x => (2 * x.1, 2 * x.2), fun a b h => by
          simp only [Prod.mk.injEq] at h; ext <;> omega⟩ := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_map,
        Prod.exists]
      constructor
      · rintro ⟨⟨hab, hk⟩, h1, h2⟩
        obtain ⟨a', rfl⟩ := h1
        obtain ⟨b', rfl⟩ := h2
        exact ⟨a', b', ⟨by nlinarith, by omega⟩, rfl⟩
      · rintro ⟨a', b', ⟨hab, hk⟩, he⟩
        change (2 * a', 2 * b') = (a, b) at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨⟨by rw [← hab]; ring, by omega⟩, dvd_mul_right 2 a', dvd_mul_right 2 b'⟩
    rw [e, Finset.sum_map, show 4 * k / 4 = k by omega, ArithmeticFunction.sigma_one_apply,
      ← Nat.sum_divisorsAntidiagonal (f := fun a _ => a)]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show 2 * (2 * x.1) = 4 * x.1
    ring
  · rw [Finset.sum_eq_zero, mul_zero]
    intro x hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hab, -⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
    exact absurd ⟨a * b, by rw [← hab, ha, hb]; ring⟩ h4

/-- The coefficient of the Gauss–Jacobi Lambert series: $\sum_{dj = n} d\,(-1)^{(d+1)(j+1)} = \sum_{d\mid n,\ 4\nmid d} d$. -/
lemma sum_antidiag_gauss (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal, (x.1 : ℂ) * (-1) ^ ((x.1 + 1) * (x.2 + 1)) = (sumDivNotFour n : ℂ) := by
  have hpt : ∀ x : ℕ × ℕ, (x.1 : ℂ) * (-1) ^ ((x.1 + 1) * (x.2 + 1)) =
      x.1 - 2 * (if 2 ∣ x.1 ∧ 2 ∣ x.2 then (x.1 : ℂ) else 0) := by
    intro x
    split_ifs with h
    · have : Odd ((x.1 + 1) * (x.2 + 1)) :=
        Nat.odd_mul.mpr ⟨(even_iff_two_dvd.mpr h.1).add_one, (even_iff_two_dvd.mpr h.2).add_one⟩
      rw [this.neg_one_pow]; ring
    · have : Even ((x.1 + 1) * (x.2 + 1)) := by
        rcases not_and_or.mp h with h1 | h2
        · exact (Nat.even_add_one.mpr fun he => h1 (even_iff_two_dvd.mp he)).mul_right _
        · exact (Nat.even_add_one.mpr fun he => h2 (even_iff_two_dvd.mp he)).mul_left _
      rw [this.neg_one_pow]; ring
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  have h1 : ∑ x ∈ n.divisorsAntidiagonal, (x.1 : ℂ) = (σ 1 n : ℕ) := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun a _ => (a : ℂ)), ArithmeticFunction.sigma_one_apply]
    push_cast; rfl
  have h2 : (2 : ℂ) * ∑ x ∈ n.divisorsAntidiagonal.filter (fun x => 2 ∣ x.1 ∧ 2 ∣ x.2), (x.1 : ℂ) =
      ((∑ d ∈ n.divisors.filter (4 ∣ ·), d : ℕ) : ℂ) := by
    rw [← sum_antidiag_both_even]; push_cast; rfl
  rw [h1, h2, sigma_one_eq_four, ← sum_divisors_four_dvd, sumDivNotFour]
  push_cast; ring

/-- The inner sum: $\sum_{j\ge1} d\,(-1)^{(d+1)(j+1)} q^{dj} = \dfrac{d\,q^d}{1+(-q)^d}$ for $d \ge 1$, $|q| < 1$. -/
lemma tsum_pnat_gauss {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ+) :
    ∑' j : ℕ+, ((d : ℕ) : ℂ) * (-1) ^ (((d : ℕ) + 1) * ((j : ℕ) + 1)) * q ^ ((d : ℕ) * j) =
      (d : ℂ) * q ^ (d : ℕ) / (1 + (-q) ^ (d : ℕ)) := by
  set s : ℂ := (-1) ^ ((d : ℕ) + 1) with hs
  have hs2 : s ^ 2 = 1 := by rw [hs, ← pow_mul, mul_comm, pow_mul]; simp
  have hsq : ‖s * q ^ (d : ℕ)‖ < 1 := by
    rw [norm_mul, hs, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq d.ne_zero
  have hterm : ∀ i : ℕ, ((d : ℕ) : ℂ) * (-1) ^ (((d : ℕ) + 1) * ((i + 1) + 1)) * q ^ ((d : ℕ) * (i + 1)) =
      ((d : ℕ) : ℂ) * q ^ (d : ℕ) * (s * q ^ (d : ℕ)) ^ i := by
    intro i
    have e1 : (-1 : ℂ) ^ (((d : ℕ) + 1) * ((i + 1) + 1)) = s ^ i := by
      rw [pow_mul, ← hs, show i + 1 + 1 = i + 2 by ring, pow_add, hs2, mul_one]
    rw [e1, show (d : ℕ) * (i + 1) = (d : ℕ) * i + (d : ℕ) by ring, pow_add, pow_mul]
    ring
  rw [tsum_pnat_eq_tsum_succ (f := fun j => ((d : ℕ) : ℂ) * (-1) ^ (((d : ℕ) + 1) * (j + 1)) *
    q ^ ((d : ℕ) * j))]
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hsq, ← div_eq_mul_inv]
  congr 1
  rw [hs, neg_pow q, pow_succ]; ring

/-- **The Gauss–Jacobi four-squares series** (Gauss, posthumous manuscript, *Werke* 3
(1876), pp. 383–384, Dickson II, ch. VIII, p. 283, (7), `dickson1920-history2:p283.1c`; Jacobi, *J. reine angew. Math.* 3
(1828), p. 191, Dickson II, ch. VIII, p. 285, `dickson1920-history2:p285.4`): for $|y| < 1$,
$$(1 + 2y + 2y^4 + 2y^9 + \cdots)^4 = 1 + 8\Bigl(\frac{y}{1-y} + \frac{2y^2}{1+y^2} + \frac{3y^3}{1-y^3} + \cdots\Bigr)
  = 1 + 8\sum_{n\ge1}\frac{n\,y^n}{1+(-y)^n}.$$
**Proved** (Lambert expansion `hasSum_lambert`, the divisor identity `sum_antidiag_gauss`, and Jacobi's four-squares
theorem `Siegel.repNum_sumSq_four` of this library). -/
@[kb "dickson1920" "ch. VIII, p. 283, (7) (Gauss, Werke 3, 383–384; occurrence dickson1920-history2:p283.1c), p. 285 (Jacobi; p285.4)"]
theorem gauss_theta_four_lambert {y : ℂ} (hy : ‖y‖ < 1) :
    thetaQ y ^ 4 = 1 + 8 * ∑' n : ℕ+, (n : ℂ) * y ^ (n : ℕ) / (1 + (-y) ^ (n : ℕ)) := by
  have hL := hasSum_lambert (f := fun d j => (d : ℂ) * (-1) ^ ((d + 1) * (j + 1))) (C := 1)
    (fun d j => by simp) hy
  simp only [sum_antidiag_gauss] at hL
  have hu := hL.unique (hasSum_sumDivNotFour hy)
  have e : ∑' d : ℕ+, ∑' j : ℕ+, ((d : ℕ) : ℂ) * (-1) ^ (((d : ℕ) + 1) * ((j : ℕ) + 1)) *
      y ^ ((d : ℕ) * j) = ∑' n : ℕ+, (n : ℂ) * y ^ (n : ℕ) / (1 + (-y) ^ (n : ℕ)) :=
    tsum_congr fun d => tsum_pnat_gauss hy d
  rw [← e, hu]; ring

/-- **Jacobi's four-squares theorem** (counting form; Dickson II, ch. VIII, p. 285,
`dickson1920-history2:p285.4`): for $m \ge 1$, $r_4(m) = 8\sum_{d\mid m,\ 4\nmid d} d$.
**Wrapper** of `Siegel.repNum_sumSq_four` (proved in this library from $\theta^4 = -\frac13(E_2(\tau) - 4E_2(4\tau))$). -/
@[kb "dickson1920" "ch. VIII, p. 285 (Jacobi, J. reine angew. Math. 3, 1828, 191; occurrence dickson1920-history2:p285.4)"]
theorem jacobi_four_squares_count (m : ℕ) (hm : 1 ≤ m) :
    repNum (sumSq 4) m = 8 * ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d :=
  repNum_sumSq_four hm

/-- **Jacobi's four-squares count for $2^\alpha p$** (Dickson II, ch. VIII, p. 285,
`dickson1920-history2:p285.4b`): for $p$ odd and $\alpha \ge 0$, the number of representations of $2^\alpha p$ as an
ordered sum of four integer squares is $8\sigma(p)$ if $\alpha = 0$ and $24\sigma(p)$ if $\alpha > 0$.
**Wrapper** of `MorenoWagstaff.theorem26` (Moreno–Wagstaff, Theorem 2.6). -/
@[kb "dickson1920" "ch. VIII, p. 285 (Jacobi, fn. 25; occurrence dickson1920-history2:p285.4b)"]
theorem jacobi_four_squares_two_pow_mul (α p : ℕ) (hp : Odd p) :
    repNum (sumSq 4) ((2 ^ α * p : ℕ) : ℤ) = if α = 0 then 8 * σ 1 p else 24 * σ 1 p := by
  have hpos : 0 < 2 ^ α * p := Nat.mul_pos (by positivity) hp.pos
  rw [MorenoWagstaff.theorem26 _ hpos]
  rcases Nat.eq_zero_or_pos α with rfl | hα
  · simp [hp]
  · have hev : ¬ Odd (2 ^ α * p) := by
      rw [Nat.not_odd_iff_even]
      exact (Nat.even_pow.mpr ⟨even_two, hα.ne'⟩).mul_right p
    rw [ite_eq_right hev, ite_eq_right hα.ne', MorenoWagstaff.ordCompl_two_pow_mul α p hp]

/-! ### The *Fundamenta nova* statement -/

/-- **Jacobi's four-squares formula, *Fundamenta nova* § 66** (Jacobi, *Fundamenta nova
theoriae functionum ellipticarum* (1829), § 66, p. 188, and § 40, formula (34), p. 106): with
$\sqrt{2K/\pi} = \theta(q) = \sum_{n\in\mathbb Z}q^{n^2}$ (§ 65),
$$\Bigl(\frac{2K}{\pi}\Bigr)^2 = \theta(q)^4 = 1 + 8\sum_{n\ge1}\frac{n\,q^n}{1+(-q)^n}
  = 1 + 8\sum_{p\ \mathrm{odd}}\sigma(p)\bigl\{q^p + 3q^{2p} + 3q^{4p} + \cdots\bigr\},$$
i.e. (the three conjuncts) the Lambert-series identity for $|q| < 1$; the number of ordered representations of $m \ge 1$
as a sum of four integer squares is $8\sum_{d\mid m,\ 4\nmid d}d$; and its value at $2^\alpha p$ ($p$ odd) is $8\sigma(p)$
for $\alpha = 0$ and $24\sigma(p)$ for $\alpha \ge 1$, which is the last series. **Wrapper** of
`gauss_theta_four_lambert`, `jacobi_four_squares_count` and `jacobi_four_squares_two_pow_mul` (above).
*Note* (the historical sources): in the scan of § 66 the numerators $1, 2, 3, 4, \ldots$ of the middle series are not visible; the
correct series has $n q^n$, as proved here. -/
@[kb "jacobi1829" "§ 66, p. 188, and § 40, (34), p. 106 (occurrence jacobi1829-fundamentanova:s66) [unverified locator]"]
theorem fundamenta_nova_four_squares {q : ℂ} (hq : ‖q‖ < 1) :
    thetaQ q ^ 4 = 1 + 8 * ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 + (-q) ^ (n : ℕ)) ∧
      (∀ m : ℕ, 1 ≤ m → repNum (sumSq 4) m = 8 * ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d) ∧
      (∀ α p : ℕ, Odd p →
        repNum (sumSq 4) ((2 ^ α * p : ℕ) : ℤ) = if α = 0 then 8 * σ 1 p else 24 * σ 1 p) :=
  ⟨gauss_theta_four_lambert hq, jacobi_four_squares_count, jacobi_four_squares_two_pow_mul⟩

end QuadFormsKB.Historical.Jacobi
