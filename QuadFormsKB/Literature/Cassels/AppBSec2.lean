/-
# Cassels, Appendix B, §2: the Euler product in the Corollary to Lemma 2.2

**Layer:** a fundamental discriminant $D$ (`Binary.IsQuadDisc D`) with its Kronecker character $\chi_D = (D/\cdot)$
(`Binary.kroneckerChar D`), real $s > 1$.

Cassels' Corollary to Lemma 2.2 (p. 372) is the identity (2.13)
$$\sum_f{}^{*}\sum_{\substack{m > 0\\(m, D) = 1}} a_f(m)\,m^{-s} = \prod_{(D/p) = +1}\frac{1 + p^{-s}}{1 - p^{-s}}$$
(reconstructed: the right-hand side is lost in the machine-read text; it is the value forced by the proof, p. 373),
where $\sum^*$ runs over the classes of forms of discriminant $D$ and $a_f(m)$ is the number of orbits of primitive
representations of $m$ by $f$. Its proof has two steps: by Lemma 2.2 the left-hand side is
$\sum 2^{\mu(m)}m^{-s}$ over the $m \ge 1$ all of whose prime factors $p$ have $(D/p) = +1$ ($\mu(m)$ the number of
distinct prime factors), and this series has the Euler product on the right. This file proves the second step
(`euler_product_two_pow_omega`); the first (Lemma 2.2 in terms of orbits of representations) is not formalized.
-/
import QuadFormsKB.Binary.KroneckerChar

open Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary

/-- Helper: `2^ω(m) ≤ d(m)`. -/
private lemma two_pow_card_primeFactors_le (m : ℕ) (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ (Nat.divisors m).card := by
  rw [Nat.card_divisors hm]
  calc 2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by simp
    _ ≤ _ := Finset.prod_le_prod (fun p hp => by
        have := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hm
          (Nat.dvd_of_mem_primeFactors hp)
        omega)

open scoped LSeries.notation in
/-- Helper: summability of the divisor-count Dirichlet series. -/
private lemma summable_card_divisors_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-s)) := by
  have hz : LSeriesSummable (↗(ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (s : ℂ) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by simpa using hs)
  have h := ArithmeticFunction.LSeriesSummable_mul hz hz
  have h2 := (summable_norm_iff.mpr h)
  refine h2.congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.norm_term_eq, if_neg hn.ne']
    have : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * ArithmeticFunction.zeta) n
        = ((Nat.divisors n).card : ℂ) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp [ArithmeticFunction.zeta_apply, (Nat.pos_of_mem_divisors hi).ne']
    rw [this]
    simp [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- Helper: the Euler product identity for an arbitrary predicate `P` on primes. -/
private lemma euler_product_aux (P : ℕ → Prop) [DecidablePred P] {s : ℝ} (hs : 1 < s) :
    ∑' m : ℕ, (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p then
        (2 : ℝ) ^ m.primeFactors.card * (m : ℝ) ^ (-s) else 0) =
      ∏' p : Nat.Primes, (if P p then
        (1 + ((p : ℕ) : ℝ) ^ (-s)) / (1 - ((p : ℕ) : ℝ) ^ (-s)) else 1) := by
  set f : ℕ → ℝ := fun m => (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p then
        (2 : ℝ) ^ m.primeFactors.card * (m : ℝ) ^ (-s) else 0) with hf
  have hf0 : f 0 = 0 := by simp [hf]
  have hf1 : f 1 = 1 := by simp [hf]
  have hfp : ∀ m : ℕ, (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p) →
      f m = 2 ^ m.primeFactors.card * (m : ℝ) ^ (-s) := fun m h => if_pos h
  have hfn : ∀ m : ℕ, ¬ (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p) → f m = 0 := fun m h => if_neg h
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    by_cases hm : m = 0
    · subst hm; simp [hf0]
    by_cases hn : n = 0
    · subst hn; simp [hf0]
    have hdisj := Nat.Coprime.disjoint_primeFactors hmn
    have hcard : (m * n).primeFactors.card = m.primeFactors.card + n.primeFactors.card := by
      rw [Nat.primeFactors_mul hm hn, Finset.card_union_of_disjoint hdisj]
    have hc : (m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, P p) ↔
        (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p) ∧ (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p) := by
      rw [Nat.primeFactors_mul hm hn]
      constructor
      · rintro ⟨_, h⟩
        exact ⟨⟨hm, fun p hp => h p (Finset.mem_union_left _ hp)⟩,
          ⟨hn, fun p hp => h p (Finset.mem_union_right _ hp)⟩⟩
      · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
        refine ⟨mul_ne_zero hm hn, fun p hp => ?_⟩
        rcases Finset.mem_union.mp hp with hp | hp
        · exact h1 p hp
        · exact h2 p hp
    by_cases cm : m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p
    · by_cases cn : n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p
      · rw [hfp _ (hc.mpr ⟨cm, cn⟩), hfp _ cm, hfp _ cn, hcard, pow_add, Nat.cast_mul,
          Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
        ring
      · rw [hfn _ cn, mul_zero, hfn _ (fun h => cn (hc.mp h).2)]
    · rw [hfn _ cm, zero_mul, hfn _ (fun h => cm (hc.mp h).1)]
  have hsum : Summable (fun m => ‖f m‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_card_divisors_rpow hs)
    by_cases hm : m = 0
    · subst hm; simp [hf0]
    have hnn : 0 ≤ (m : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg m) _
    have hle : (2 : ℝ) ^ m.primeFactors.card ≤ ((Nat.divisors m).card : ℝ) := by
      exact_mod_cast two_pow_card_primeFactors_le m hm
    by_cases hc : m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p
    · rw [hfp _ hc, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right hle hnn
    · rw [hfn _ hc, norm_zero]
      positivity
  rw [← EulerProduct.eulerProduct_tprod hf1 hmul hsum hf0]
  refine tprod_congr (fun p => ?_)
  have hp : (p : ℕ).Prime := p.2
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr1 : ((p : ℕ) : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hpow : ∀ e : ℕ, (((p : ℕ) ^ e : ℕ) : ℝ) ^ (-s) = (((p : ℕ) : ℝ) ^ (-s)) ^ e := by
    intro e
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm,
      Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
  by_cases hPp : P p
  · rw [if_pos hPp]
    have hfe : ∀ e : ℕ, f ((p : ℕ) ^ e) =
        2 * (((p : ℕ) : ℝ) ^ (-s)) ^ e - (if e = 0 then 1 else 0) := by
      intro e
      by_cases he : e = 0
      · subst he; simp [hf1]; norm_num
      · have hpf : ((p : ℕ) ^ e).primeFactors = {(p : ℕ)} := Nat.primeFactors_prime_pow he hp
        have hne : (p : ℕ) ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
        simp only [hf, hpf, ne_eq, hne, not_false_eq_true, Finset.mem_singleton, forall_eq,
          hPp, and_self, if_true, Finset.card_singleton, pow_one, he, if_false, sub_zero, hpow]
    have h1 := (hasSum_geometric_of_lt_one hr0 hr1).mul_left 2
    have h2 := h1.sub (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
    have h3 : HasSum (fun e => f ((p : ℕ) ^ e))
        (2 * (1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹ - 1) := by
      simpa [hfe] using h2
    rw [h3.tsum_eq]
    have : (1 - ((p : ℕ) : ℝ) ^ (-s)) ≠ 0 := by linarith
    field_simp
    ring
  · rw [if_neg hPp]
    rw [tsum_eq_single 0]
    · simpa using hf1
    · intro e he
      have hpf : ((p : ℕ) ^ e).primeFactors = {(p : ℕ)} := Nat.primeFactors_prime_pow he hp
      simp [hf, hpf, hPp]

/-- **The Euler product of $\sum 2^{\mu(m)}m^{-s}$** (Cassels, App. B, §2, proof of the Corollary to Lemma 2.2,
pp. 372–373): for a fundamental discriminant $D$ and real $s > 1$,
$$\sum_{\substack{m \ge 1\\ p \mid m \Rightarrow (D/p) = +1}} 2^{\mu(m)}\,m^{-s} = \prod_{p\,:\,(D/p) = +1}
\frac{1 + p^{-s}}{1 - p^{-s}},$$
$\mu(m)$ the number of distinct prime factors of $m$; the product is over all primes, with the factor $1$ when
$(D/p) \ne +1$. -/
@[kb "cassels1978" "App. B, §2, proof of the Cor. to Lemma 2.2, (2.13), pp. 372–373 (the Euler product of Σ 2^μ(m) m^(-s))"]
theorem euler_product_two_pow_omega (D : ℤ) [IsQuadDisc D] {s : ℝ} (hs : 1 < s) :
    ∑' m : ℕ, (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, kroneckerChar D p = 1 then
        (2 : ℝ) ^ m.primeFactors.card * (m : ℝ) ^ (-s) else 0) =
      ∏' p : Nat.Primes, (if kroneckerChar D p = 1 then
        (1 + ((p : ℕ) : ℝ) ^ (-s)) / (1 - ((p : ℕ) : ℝ) ^ (-s)) else 1) := by
  classical
  exact euler_product_aux (fun p => kroneckerChar D p = 1) hs

end QuadFormsKB.Binary
