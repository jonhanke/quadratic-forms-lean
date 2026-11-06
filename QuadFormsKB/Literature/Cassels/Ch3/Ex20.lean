/-
# Cassels, Chapter 3, Example 20 (p. 52): $(1+b)^m$ as a power series in $m$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *Examples*, Ex. 20, p. 52.

**Statement.** Let $p$ be a prime and $b \in \mathbb Q_p$ with $|b|_p \le p^{-1}$ if $p \ne 2$ and $|b|_2 \le 1/4$ if
$p = 2$. Then there are $c_1, c_2, \ldots \in \mathbb Z_p$ with
$(1+b)^m = 1 + c_1 m + c_2 m^{2} + \cdots + c_n m^{n} + \cdots$ for every positive integer $m$ (the series converges
$p$-adically).

**Conventions.** Cassels' coefficients $c_1, c_2, \ldots$ are `c 0, c 1, …` here (shift by one): the headline
`ex20` asserts that $\sum_{n \ge 0} c_n\, m^{n+1}$ (`c n` times `m ^ (n + 1)`) has sum $(1+b)^m - 1$ in $\mathbb Q_p$.
The hypothesis on $b$ is stated inline as `‖b‖ ≤ if p = 2 then 1/4 else p⁻¹`.

**Proof (following Cassels' hint).** Put $e_s = b^s/s! \in \mathbb Z_p$. With $v = $ the $p$-adic valuation of $s!$
(Ex. 18: $(p-1)v < s$) one gets $|e_s|_p \le p^{-\lfloor s/2 \rfloor}$, so $e_s \to 0$. The falling product
$m(m-1)\cdots(m-s+1)$ is the value at $m$ of `descPochhammer ℤ s`, a polynomial with integer coefficients
$a_{s,n}$ (zero for $n > s$). The family $a_{s,n}\, e_s\, m^{n}$ over $\mathbb N \times \mathbb N$ tends to $0$ along the
cofinite filter, hence is summable in the complete non-archimedean group $\mathbb Z_p$, and can be summed in either
order (the content of Ex. 19, here from Mathlib's `HasSum.prod_fiberwise`). Summing over $n$ first gives
$\sum_s \binom{m}{s} b^s = (1+b)^m$; summing over $s$ first gives $\sum_n c_n' m^n$ with
$c_n' = \sum_s a_{s,n}\, e_s$, and $c_0' = 1$.

**Proves (no ``).** `ex20` (the statement), and the stronger `ex20_tendsto`: the sequence can be chosen with
$c_n \to 0$, and the expansion holds also for $m = 0$.
Ex. 18 is used in the form of Mathlib's `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`
(the same fact as `Ch3Ex.ex18_lt`, stated there for $M$ in Cassels' summation form).
-/
import Mathlib
import QuadFormsKB.Citation

open Filter Topology

noncomputable section

namespace QuadFormsKB.Cassels.Ch3Ex20

variable {p : ℕ} [hp : Fact p.Prime]

/-- Helper: $|s!|_p = p^{-v}$ where $v$ is the $p$-adic valuation of $s!$ ($s$ a natural number, `s.factorial` cast into $\mathbb Q_p$). -/
theorem norm_fact (s : ℕ) :
    ‖((s.factorial : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p s.factorial : ℤ)) := by
  have hne : ((s.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  have h := Padic.eq_padicNorm (p := p) ((s.factorial : ℕ) : ℚ)
  rw [Rat.cast_natCast] at h
  rw [h, padicNorm.eq_zpow_of_nonzero hne, padicValRat.of_nat]
  push_cast
  rfl

/-- Helper: for a natural number $s$ and $k = 2$ if $p = 2$, $k = 1$ otherwise, with $v$ the $p$-adic valuation of $s!$: $s \le 2(ks - v)$ and $v \le ks$ (from $(p-1)v < s$ for $s \ge 1$). -/
theorem two_mul_le (s : ℕ) :
    s ≤ 2 * ((if p = 2 then 2 else 1) * s - padicValNat p s.factorial : ℕ) ∧
    padicValNat p s.factorial ≤ (if p = 2 then 2 else 1) * s := by
  rcases s.eq_zero_or_pos with rfl | hs
  · simp
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := s) (by omega)
  have hp2 := hp.out.two_le
  by_cases h2 : p = 2
  · subst h2
    simp at h ⊢
    omega
  · have h3 : 3 ≤ p := by
      have := hp.out.two_le
      omega
    simp only [h2, ite_false, one_mul]
    have : 2 * padicValNat p s.factorial ≤ (p - 1) * padicValNat p s.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- Helper: for $b \in \mathbb Q_p$ satisfying the hypothesis `hb` of Ex. 20 and $s \in \mathbb N$, $|b^s/s!|_p \le p^{-\lfloor s/2 \rfloor}$. -/
theorem norm_e_le (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (s : ℕ) :
    ‖b ^ s / (s.factorial : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((s / 2 : ℕ) : ℤ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨h1, h2⟩ := two_mul_le (p := p) s
  set k : ℕ := if p = 2 then 2 else 1 with hk
  set v := padicValNat p s.factorial with hv
  have hbk : ‖b‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    refine hb.trans (le_of_eq ?_)
    by_cases h2 : p = 2
    · subst h2; simp [hk]; norm_num
    · simp [hk, h2]
  rw [norm_div, norm_pow, norm_fact, div_eq_mul_inv, ← zpow_neg, neg_neg]
  calc ‖b‖ ^ s * (p : ℝ) ^ (v : ℤ) ≤ ((p : ℝ) ^ (-(k : ℤ))) ^ s * (p : ℝ) ^ (v : ℤ) := by
        gcongr
    _ = (p : ℝ) ^ (-((k * s : ℕ) : ℤ) + v) := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp0.ne']
        push_cast; ring_nf
    _ ≤ (p : ℝ) ^ (-((s / 2 : ℕ) : ℤ)) := by
        apply zpow_le_zpow_right₀ hp1.le
        omega


/-- Helper: the hypothesis of Ex. 20 implies $|b|_p \le 1$. -/
theorem norm_b_le_one (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) : ‖b‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  refine hb.trans ?_
  split_ifs
  · norm_num
  · exact inv_le_one_of_one_le₀ hp1.le

/-- Helper: for $b$, `hb` as in `norm_e_le` and $s \in \mathbb N$, $|b^s/s!|_p \le 1$. -/
theorem norm_e_le_one (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (s : ℕ) :
    ‖b ^ s / (s.factorial : ℚ_[p])‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  refine (norm_e_le b hb s).trans ?_
  exact zpow_le_one_of_nonpos₀ hp1.le (by omega)

/-- Helper: $b^s/s!$ as an element of $\mathbb Z_p$ ($b$ with the bound `hb`, $s \in \mathbb N$). -/
def eInt (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (s : ℕ) : ℤ_[p] :=
  ⟨b ^ s / (s.factorial : ℚ_[p]), norm_e_le_one b hb s⟩

/-- Helper: $|b^s/s!|_p \le p^{-\lfloor s/2 \rfloor}$ for the element `eInt b hb s` of $\mathbb Z_p$. -/
theorem norm_eInt_le (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (s : ℕ) :
    ‖eInt b hb s‖ ≤ (p : ℝ) ^ (-((s / 2 : ℕ) : ℤ)) := norm_e_le b hb s

/-- Helper: $b^s/s! \to 0$: for $\varepsilon > 0$ there is $S$ with $|b^s/s!|_p < \varepsilon$ for all $s \ge S$. -/
theorem exists_bound (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) {ε : ℝ}
    (hε : 0 < ε) : ∃ S : ℕ, ∀ s, S ≤ s → ‖eInt b hb s‖ < ε := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨2 * j, fun s hs => ?_⟩
  refine (norm_eInt_le b hb s).trans_lt (lt_of_le_of_lt ?_ hj)
  rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  apply zpow_le_zpow_right₀ hp1.le
  omega

/-- Helper: the family $(s, n) \mapsto a_{s,n}\, (b^s/s!)\, x^{n}$ on $\mathbb N \times \mathbb N$ in $\mathbb Z_p$, where $a_{s,n}$ is the coefficient of $X^n$ in `descPochhammer ℤ s` (the falling factorial $X(X-1)\cdots(X-s+1)$) and $x \in \mathbb Z_p$. -/
def fam (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (x : ℤ_[p]) (q : ℕ × ℕ) :
    ℤ_[p] := (((descPochhammer ℤ q.1).coeff q.2 : ℤ) : ℤ_[p]) * eInt b hb q.1 * x ^ q.2

/-- Helper: $|{\tt fam}(s,n)|_p \le |b^s/s!|_p$ (integer coefficients and $|x|_p \le 1$). -/
theorem norm_fam_le (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (x : ℤ_[p])
    (q : ℕ × ℕ) : ‖fam b hb x q‖ ≤ ‖eInt b hb q.1‖ := by
  unfold fam
  rw [norm_mul, norm_mul, norm_pow]
  have h1 := PadicInt.norm_le_one ((((descPochhammer ℤ q.1).coeff q.2 : ℤ)) : ℤ_[p])
  have h2 := PadicInt.norm_le_one x
  have h3 : ‖x‖ ^ q.2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h2
  calc _ ≤ 1 * ‖eInt b hb q.1‖ * 1 := by gcongr
    _ = _ := by ring

/-- Helper: the family vanishes for $n > s$ (the falling factorial has degree $s$). -/
theorem fam_eq_zero (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (x : ℤ_[p])
    (s n : ℕ) (h : s < n) : fam b hb x (s, n) = 0 := by
  unfold fam
  have : (descPochhammer ℤ s).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [descPochhammer_natDegree]; exact h
  simp [this]

/-- Helper: the family `fam b hb x` is summable over $\mathbb N \times \mathbb N$ (it tends to $0$ along the cofinite filter in a complete non-archimedean group). -/
theorem summable_fam (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (x : ℤ_[p]) :
    Summable (fam b hb x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS⟩ := exists_bound b hb hε
  rw [Filter.eventually_cofinite]
  refine ((Finset.range S ×ˢ Finset.range S).finite_toSet).subset ?_
  intro ⟨s, n⟩ hq
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hq
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  have hs : s < S := by
    by_contra h
    exact absurd (hS s (not_lt.mp h)) (not_lt.mpr (hq.trans (norm_fam_le b hb x (s, n))))
  refine ⟨hs, ?_⟩
  by_contra h
  have : fam b hb x (s, n) = 0 := fam_eq_zero b hb x s n (by omega)
  rw [this, norm_zero] at hq
  linarith


/-- Helper: `b` as an element of $\mathbb Z_p$ (valid since $|b|_p \le 1$). -/
def bInt (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) : ℤ_[p] :=
  ⟨b, norm_b_le_one b hb⟩

/-- Helper: $(b^s/s!)\cdot s! = b^s$ in $\mathbb Z_p$. -/
theorem eInt_mul_factorial (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (s : ℕ) :
    eInt b hb s * (s.factorial : ℤ_[p]) = bInt b hb ^ s := by
  apply PadicInt.ext
  have hf : (s.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  show b ^ s / (s.factorial : ℚ_[p]) * (s.factorial : ℚ_[p]) = b ^ s
  field_simp

/-- Helper: $\sum_{n \le s} a_{s,n}\, m^{n} = m(m-1)\cdots(m-s+1)$ (the descending factorial of the natural number $m$), in $\mathbb Z_p$. -/
theorem eval_descPochhammer (m s : ℕ) :
    ∑ n ∈ Finset.range (s + 1), (((descPochhammer ℤ s).coeff n : ℤ) : ℤ_[p]) * (m : ℤ_[p]) ^ n
      = (m.descFactorial s : ℤ_[p]) := by
  have h := Polynomial.eval₂_eq_sum_range (f := Int.castRingHom ℤ_[p]) (p := descPochhammer ℤ s) (m : ℤ_[p])
  rw [descPochhammer_natDegree] at h
  rw [← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_descFactorial] at h
  rw [h]
  simp

/-- Helper: for fixed $s$, $\sum_n {\tt fam}(s,n) = (b^s/s!)\, m(m-1)\cdots(m-s+1)$ (a finite sum). -/
theorem hasSum_fiber_s (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (m s : ℕ) :
    HasSum (fun n => fam b hb (m : ℤ_[p]) (s, n)) (eInt b hb s * (m.descFactorial s : ℤ_[p])) := by
  have : HasSum (fun n => fam b hb (m : ℤ_[p]) (s, n))
      (∑ n ∈ Finset.range (s + 1), fam b hb (m : ℤ_[p]) (s, n)) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => fam_eq_zero b hb _ s n (by simpa using hn))
  convert this using 1
  rw [← eval_descPochhammer, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold fam; ring

/-- Helper: $\sum_s (b^s/s!)\, m(m-1)\cdots(m-s+1) = (1+b)^m$ in $\mathbb Z_p$ (binomial theorem; terms with $s > m$ vanish). -/
theorem hasSum_binomial (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (m : ℕ) :
    HasSum (fun s => eInt b hb s * (m.descFactorial s : ℤ_[p])) ((1 + bInt b hb) ^ m) := by
  have : HasSum (fun s => eInt b hb s * (m.descFactorial s : ℤ_[p]))
      (∑ s ∈ Finset.range (m + 1), eInt b hb s * (m.descFactorial s : ℤ_[p])) :=
    hasSum_sum_of_ne_finset_zero (fun s hs => by
      have : m.descFactorial s = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by simpa using hs)
      simp [this])
  convert this using 1
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc, eInt_mul_factorial]
  simp


/-- Helper: the coefficient $c'_n = \sum_{s} a_{s,n}\, b^s/s! \in \mathbb Z_p$ (sum over $s \ge 0$). -/
def coef (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (n : ℕ) : ℤ_[p] :=
  ∑' s, (((descPochhammer ℤ s).coeff n : ℤ) : ℤ_[p]) * eInt b hb s

/-- Helper: $c'_0 = 1$. -/
theorem coef_zero (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) :
    coef b hb 0 = 1 := by
  unfold coef
  rw [tsum_eq_single 0]
  · have : eInt b hb 0 = 1 := Subtype.ext (by simp [eInt])
    simp [this]
  · intro s hs
    have : (descPochhammer ℤ s).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, descPochhammer_eval_zero]
      simp [hs]
    simp [this]

/-- Helper: the series defining `coef b hb n` is summable. -/
theorem summable_coef_term (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (n : ℕ) :
    Summable (fun s => (((descPochhammer ℤ s).coeff n : ℤ) : ℤ_[p]) * eInt b hb s) := by
  have h : Summable (fun s : ℕ => (fam b hb 1 ∘ (Equiv.prodComm ℕ ℕ)) (n, s)) :=
    ((Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).mpr (summable_fam b hb 1)).prod_factor n
  refine h.congr fun s => ?_
  simp [fam]

/-- Helper: $\sum_{n \ge 0} c'_n m^{n} = (1+b)^m$ in $\mathbb Z_p$: rearrangement of the double series. -/
theorem hasSum_coef (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (m : ℕ) :
    HasSum (fun n => coef b hb n * (m : ℤ_[p]) ^ n) ((1 + bInt b hb) ^ m) := by
  have hF := (summable_fam b hb (m : ℤ_[p])).hasSum
  have hA : HasSum (fun s => ∑' n, fam b hb (m : ℤ_[p]) (s, n)) (∑' q, fam b hb (m : ℤ_[p]) q) :=
    hF.prod_fiberwise fun s => (hasSum_fiber_s b hb m s).summable.hasSum
  have hA' : ∀ s, ∑' n, fam b hb (m : ℤ_[p]) (s, n) = eInt b hb s * (m.descFactorial s : ℤ_[p]) :=
    fun s => (hasSum_fiber_s b hb m s).tsum_eq
  simp_rw [hA'] at hA
  have hT : ∑' q, fam b hb (m : ℤ_[p]) q = (1 + bInt b hb) ^ m := hA.unique (hasSum_binomial b hb m)
  have hF' : HasSum (fam b hb (m : ℤ_[p]) ∘ (Equiv.prodComm ℕ ℕ)) (∑' q, fam b hb (m : ℤ_[p]) q) :=
    (Equiv.hasSum_iff (Equiv.prodComm ℕ ℕ)).mpr hF
  have hS' : Summable (fam b hb (m : ℤ_[p]) ∘ (Equiv.prodComm ℕ ℕ)) :=
    (Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).mpr (summable_fam b hb _)
  have hB : HasSum (fun n => ∑' s, (fam b hb (m : ℤ_[p]) ∘ (Equiv.prodComm ℕ ℕ)) (n, s))
      (∑' q, fam b hb (m : ℤ_[p]) q) :=
    hF'.prod_fiberwise fun n => (hS'.prod_factor n).hasSum
  rw [hT] at hB
  convert hB using 1
  funext n
  simp only [Function.comp, Equiv.prodComm_apply, Prod.swap_prod_mk]
  unfold coef
  rw [← (summable_coef_term b hb n).tsum_mul_right]
  refine tsum_congr fun s => ?_
  simp only [fam]


/-- Helper: $c'_{n+1} \to 0$ as $n \to \infty$. -/
theorem tendsto_coef (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) :
    Tendsto (fun n => coef b hb (n + 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S, hS⟩ := exists_bound b hb (half_pos hε)
  refine ⟨S, fun n hn => ?_⟩
  rw [dist_zero_right]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le fun s => ?_
  by_cases hsn : s < n + 1
  · have : (descPochhammer ℤ s).coeff (n + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [descPochhammer_natDegree]; exact hsn
    simp [this, (half_pos hε).le]
  · have h1 := PadicInt.norm_le_one ((((descPochhammer ℤ s).coeff (n + 1) : ℤ)) : ℤ_[p])
    rw [norm_mul]
    calc _ ≤ 1 * ‖eInt b hb s‖ := by gcongr
      _ ≤ _ := by rw [one_mul]; exact (hS s (by omega)).le

/-- Helper: in $\mathbb Q_p$, $\sum_{n \ge 0} c'_{n+1} m^{n+1} = (1+b)^m - 1$. -/
theorem hasSum_coef_shift (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) (m : ℕ) :
    HasSum (fun n => (coef b hb (n + 1) : ℚ_[p]) * (m : ℚ_[p]) ^ (n + 1)) ((1 + b) ^ m - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_coef b hb m)
  simp only [Finset.sum_range_one, pow_zero, mul_one, coef_zero] at h
  have h2 := h.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) continuous_subtype_val
  convert h2 using 1
  · funext n
    simp
  · rw [map_sub, map_pow, map_add, map_one]
    rfl

/-- **Cassels, Ch. 3, Ex. 20 (p. 52), stronger form.** Let $p$ be a prime (`[Fact p.Prime]`) and $b \in \mathbb Q_p$
with $|b|_p \le p^{-1}$ if $p \ne 2$ and $|b|_2 \le 1/4$ if $p = 2$ (hypothesis `hb`). Then there is a sequence
`c : ℕ → ℤ_[p]` ($c_n$ here is Cassels' $c_{n+1}$) with $c_n \to 0$ such that for every natural number $m$
(including $0$) the series $\sum_{n \ge 0} c_n\, m^{n+1}$ converges in $\mathbb Q_p$ to $(1+b)^m - 1$. -/
@[kb "cassels1978" "Ch. 3, Ex. 20, p. 52"]
theorem ex20_tendsto (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) :
    ∃ c : ℕ → ℤ_[p], Tendsto c atTop (𝓝 0) ∧ ∀ m : ℕ,
      HasSum (fun n => (c n : ℚ_[p]) * (m : ℚ_[p]) ^ (n + 1)) ((1 + b) ^ m - 1) :=
  ⟨fun n => coef b hb (n + 1), tendsto_coef b hb, hasSum_coef_shift b hb⟩

/-- **Cassels, Ch. 3, Ex. 20 (p. 52).** Let $p$ be a prime (`[Fact p.Prime]`) and $b \in \mathbb Q_p$ with
$|b|_p \le p^{-1}$ if $p \ne 2$ and $|b|_2 \le 1/4$ if $p = 2$ (hypothesis `hb`). Then there is a sequence
`c : ℕ → ℤ_[p]` of elements of $\mathbb Z_p$ (`c n` is Cassels' $c_{n+1}$, the sequence being indexed from $0$) such that
for every positive integer $m$,
$(1+b)^m = 1 + \sum_{n \ge 0} c_n\, m^{n+1}$, i.e. the series $\sum_{n \ge 0} c_n\, m^{n+1}$ converges in $\mathbb Q_p$
to $(1+b)^m - 1$. -/
@[kb "cassels1978" "Ch. 3, Ex. 20, p. 52"]
theorem ex20 (b : ℚ_[p]) (hb : ‖b‖ ≤ if p = 2 then (1/4 : ℝ) else (p : ℝ)⁻¹) :
    ∃ c : ℕ → ℤ_[p], ∀ m : ℕ, 0 < m →
      HasSum (fun n => (c n : ℚ_[p]) * (m : ℚ_[p]) ^ (n + 1)) ((1 + b) ^ m - 1) := by
  obtain ⟨c, -, hc⟩ := ex20_tendsto b hb
  exact ⟨c, fun m _ => hc m⟩

end QuadFormsKB.Cassels.Ch3Ex20
