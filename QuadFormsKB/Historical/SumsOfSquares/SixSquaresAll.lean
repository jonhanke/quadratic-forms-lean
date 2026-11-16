/-
# Six squares for every number (Smith's form of Jacobi's formula)

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`).  Target
(Smith, *Collected Mathematical Papers* I,
p. 307, occurrence `smith1894-papers1:p307`): for $N \ge 1$, with $\delta' = N/\delta$,
$$r_6(N) = 4\sum_{\delta \mid N,\ \delta\ \mathrm{odd}} (-1)^{(\delta-1)/2}\,(4\delta'^2 - \delta^2).$$
`six_squares`: **proved** (unconditional). The special cases $N \equiv \pm 1 \pmod 4$ are `six_squares_odd`
(`SixSquares.lean`). The second sentence of the row (six *positive odd* squares summing to $2N$) is not formalized
(loose end).

**Route.** As for `six_squares_odd`: $r_6(N) = \beta_\infty(N)\prod_p\beta_p(N)$ (`repNum_sumSq_eq_siegel`), the odd-prime
densities `localDensity_sumSq_six_odd` (all valuations), and at $p = 2$ the recursion
$\beta_2(4T) = \beta_2(T)/2^4 + \beta^{\ne 0}_2(4T)$ (`localDensityOf_nonZero_eq`) with the non-Zero-type density at
level $3$ (`localDensityOf_nonZero_sumSq_two`).
-/
import QuadFormsKB.Historical.SumsOfSquares.SixSquares

namespace QuadFormsKB.Historical.SumsOfSquares

open QuadFormsKB.Siegel QuadFormsKB.LocalDensity

/-! ### The 2-adic density at every valuation -/

theorem sqTable8_six_four (T : ZMod 8) : sqTable8 6 (4 * T) = 32768 := by
  revert T; decide

theorem sqTable8_six_two : ∀ r : ZMod 8, r.val % 4 = 2 →
    sqTable8 6 r = if r.val % 8 = 2 then 30720 else 34816 := by
  decide

theorem card_sumSq_six_mod_two : ∀ c : ZMod (2 ^ 1),
    Fintype.card {x : Fin 6 → ZMod (2 ^ 1) // ∑ i, x i ^ 2 = c} = 32 := by
  decide

/-- The non-Zero-type count at level $3$ for $4 \mid m$ is $32768 - 2048 = 30720$. -/
theorem repCountOf_nonZero_six_four (T : ℤ) :
    repCountOf (sumSq 6) 2 3 (4 * T) (fun x => ¬ IsZeroType 2 3 x) = 30720 := by
  have hsplit := repCount_eq_zero_add_nonZero (sumSq 6) 2 3 (4 * T)
  have hz := repCountZero_eq (sumSq 6) 2 (4 * T) 3 (by norm_num)
  have hd : ((2 : ℕ) : ℤ) ^ 2 ∣ 4 * T := ⟨T, by norm_num⟩
  rw [if_pos hd] at hz
  have h1 : repCount (sumSq 6) 2 1 (4 * T / ((2 : ℕ) : ℤ) ^ 2) = 32 := by
    unfold repCount
    rw [Nat.card_eq_fintype_card]
    rw [← card_sumSq_six_mod_two ((4 * T / ((2 : ℕ) : ℤ) ^ 2 : ℤ) : ZMod (2 ^ 1))]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [evalIn_sumSq]
  have h2 : repCount (sumSq 6) 2 3 (4 * T) = 32768 := by
    unfold repCount
    rw [Nat.card_eq_fintype_card]
    have := sqCount8_eq 6 (by norm_num) (((4 * T : ℤ)) : ZMod 8)
    have h3 : sqTable8 6 (((4 * T : ℤ)) : ZMod 8) = 32768 := by
      have : (((4 * T : ℤ)) : ZMod 8) = 4 * (T : ZMod 8) := by push_cast; rfl
      rw [this, sqTable8_six_four]
    rw [← h3, ← this]
    unfold sqCount8
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by rw [evalIn_sumSq])
  rw [hz, h1, h2] at hsplit
  norm_num at hsplit
  omega

/-- $\beta_2(4T) = \beta_2(T)/16 + 15/16$ for $T \ne 0$. -/
theorem localDensity_sumSq_six_two_rec (T : ℤ) (hT : T ≠ 0) :
    localDensity (sumSq 6) 2 (4 * T) = localDensity (sumSq 6) 2 T / 16 + 15 / 16 := by
  have hK := localDensityOf_nonZero_eq (sumSq 6) posDef_sumSq.nondegenerate 2 (by norm_num) T hT
  rw [localDensityOf_nonZero_sumSq_two] at hK
  have e : (((2 : ℕ) : ℤ) ^ 2 * T) = 4 * T := by norm_num
  rw [e, repCountOf_nonZero_six_four] at hK
  norm_num at hK
  linarith

/-- **$\beta_2$ of $I_6$, all valuations:** for odd $u$, $\beta_2(2^a u) = 1 - \chi_{-4}(u)/4^{a+1}$. -/
theorem localDensity_sumSq_six_two_all (a : ℕ) (u : ℕ) (hu : Odd u) :
    localDensity (sumSq 6) 2 ((2 : ℤ) ^ a * u) = 1 - chi4 u / 4 ^ (a + 1) := by
  have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu
  have hu0 : u ≠ 0 := by rintro rfl; omega
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 =>
      rw [pow_zero, one_mul, localDensity_sumSq_six_two (u : ℤ) (by exact_mod_cast hu)]
      have : ((u : ℤ) % 4 = 1) ↔ u % 4 = 1 := by omega
      simp only [this]
      unfold chi4
      split_ifs <;> first | omega | norm_num
    | 1 =>
      have hnd : ¬ (4 : ℤ) ∣ (2 : ℤ) ^ 1 * u := by omega
      have hv : (((((2 : ℤ) ^ 1 * u : ℤ) : ZMod 8)).val : ℤ) = (2 : ℤ) ^ 1 * u % 8 := ZMod.val_intCast _
      have hr : (((2 : ℤ) ^ 1 * u : ℤ) : ZMod 8).val % 4 = 2 := by omega
      rw [localDensity_sumSq_two 6 _ hnd, sqCount8_eq 6 (by norm_num), sqTable8_six_two _ hr]
      generalize (((2 : ℤ) ^ 1 * u : ℤ) : ZMod 8).val = v at hv hr ⊢
      unfold chi4
      by_cases h4 : u % 4 = 1
      · have : v % 8 = 2 := by omega
        rw [if_pos this, if_pos h4]; norm_num
      · have h3 : u % 4 = 3 := by omega
        have : ¬ v % 8 = 2 := by omega
        rw [if_neg this, if_neg h4, if_pos h3]; norm_num
    | a + 2 =>
      have hT : (2 : ℤ) ^ a * u ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hu0)
      have e : (2 : ℤ) ^ (a + 2) * u = 4 * ((2 : ℤ) ^ a * u) := by ring
      rw [e, localDensity_sumSq_six_two_rec _ hT, ih a (by omega)]
      rw [show a + 2 + 1 = (a + 1) + 2 by ring, pow_add]
      field_simp
      ring

/-! ### The Euler product for every $m$ -/

/-- The Euler factor of $I_6$ at any $m \ne 0$. -/
theorem eulerFactor_sumSq_six_all (m : ℕ) (hm0 : m ≠ 0) (p : AWS.PrimeIdx) :
    eulerFactor (sumSq 6) (m : ℤ) p =
      (if (p : ℕ) = 2 then localDensity (sumSq 6) 2 (m : ℤ) else 1) *
        ((1 - chi4 p / ((p : ℕ) : ℝ) ^ 3) * sixG m p) := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases h2 : (p : ℕ) = 2
  · have hG : sixG m p = 1 := by
      rw [sixG, h2]
      simp [chi4, Finset.sum_range_succ']
    have hc : chi4 (p : ℕ) = 0 := by rw [h2]; simp [chi4]
    rw [if_pos h2, hG, hc]
    show localDensity (sumSq 6) (p : ℕ) (m : ℤ) = _
    rw [h2]
    simp
  · rw [if_neg h2, one_mul]
    show localDensity (sumSq 6) (p : ℕ) (m : ℤ) = _
    have hu : ¬ ((p : ℕ) : ℤ) ∣ ((m / (p : ℕ) ^ m.factorization p : ℕ) : ℤ) := by
      exact_mod_cast Nat.not_dvd_ordCompl p.2 hm0
    have e : (m : ℤ) = ((p : ℕ) : ℤ) ^ m.factorization p * ((m / (p : ℕ) ^ m.factorization p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self m p).symm
    rw [e, localDensity_sumSq_six_odd (p : ℕ) h2 _ _ hu]
    rfl

/-- **The Euler product of $I_6$ at any $m \ne 0$:**
$\prod_p\beta_p(m) = \beta_2(m)\cdot\frac{32}{\pi^3}\sum_{d \mid m}\chi_{-4}(d)d^{-2}$. -/
theorem eulerProduct_sumSq_six_all (m : ℕ) (hm0 : m ≠ 0) :
    eulerProduct (sumSq 6) m =
      localDensity (sumSq 6) 2 (m : ℤ) * (32 / Real.pi ^ 3) *
        ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2 := by
  set c : ℝ := localDensity (sumSq 6) 2 (m : ℤ) with hc_def
  have hc : HasProd (fun p : AWS.PrimeIdx => if (p : ℕ) = 2 then c else 1) c := by
    have h : HasProd (fun p : AWS.PrimeIdx => if (p : ℕ) = 2 then c else 1)
        (∏ p ∈ ({⟨2, Nat.prime_two⟩} : Finset AWS.PrimeIdx), if (p : ℕ) = 2 then c else 1) :=
      hasProd_prod_of_ne_finset_one fun p hp => by
        rw [if_neg]
        intro h2; exact hp (Finset.mem_singleton.mpr (Subtype.ext h2))
    rw [Finset.prod_singleton] at h
    simpa using h
  have hall := hc.mul (hasProd_one_sub_chi4_cube.mul (hasProd_sixG m hm0))
  have hfun : eulerFactor (sumSq 6) (m : ℤ) = fun p : AWS.PrimeIdx =>
      (if (p : ℕ) = 2 then c else 1) * ((1 - chi4 p / ((p : ℕ) : ℝ) ^ 3) * sixG m p) :=
    funext (eulerFactor_sumSq_six_all m hm0)
  have hE : eulerProduct (sumSq 6) (m : ℤ) =
      c * (32 / Real.pi ^ 3 * ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2) := by
    unfold eulerProduct
    rw [hfun]
    exact hall.tprod_eq
  rw [hE]
  ring

/-! ### Divisor-sum algebra -/

/-- Splitting off the power of two: $\sum_{d \mid 2^a u}\chi_{-4}(d)d^{-2} = \sum_{d \mid u}\chi_{-4}(d)d^{-2}$. -/
theorem sum_divisors_two_pow_mul (a u : ℕ) (hu : Odd u) :
    ∑ d ∈ (2 ^ a * u).divisors, chi4 d / (d : ℝ) ^ 2 = ∑ d ∈ u.divisors, chi4 d / (d : ℝ) ^ 2 := by
  have hcop : Nat.Coprime (2 ^ a) u := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hu)
  have hmul := (isMultiplicative_chiDiv2.mul ArithmeticFunction.isMultiplicative_zeta.natCast)
  have h := hmul.map_mul_of_coprime hcop
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.coe_mul_zeta_apply] at h
  have h2 : ∑ d ∈ (2 ^ a).divisors, chiDiv2 d = 1 := by
    rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map, Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range a, chiDiv2 (2 ^ (i + 1)) = 0 := by
      intro i _
      show chi4 (2 ^ (i + 1)) / _ = 0
      rw [pow_succ', chi4_mul]
      simp [chi4]
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.sum_eq_zero this]
    simp [chiDiv2, chi4]
  rw [h2, one_mul] at h
  exact h

/-- $u^2\sum_{d \mid u}\chi_{-4}(d)d^{-2} = \sum_{d \mid u}\chi_{-4}(d)(u/d)^2$. -/
theorem sq_mul_sum_chi4_eq (u : ℕ) (hu0 : u ≠ 0) :
    (u : ℝ) ^ 2 * ∑ d ∈ u.divisors, chi4 d / (d : ℝ) ^ 2 =
      ∑ d ∈ u.divisors, chi4 d * ((u / d : ℕ) : ℝ) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨k, hk⟩ := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := by rintro rfl; simp at hk; exact hu0 hk
  have : u / d = k := by rw [hk]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)
  rw [this, hk]
  push_cast
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  field_simp

/-- For odd $u$: $\sum_{d \mid u}\chi_{-4}(d)d^2 = \sum_{d \equiv 1}d^2 - \sum_{d \equiv 3}d^2$. -/
theorem sum_chi4_sq_eq (u : ℕ) (hu : Odd u) :
    ∑ d ∈ u.divisors, chi4 d * (d : ℝ) ^ 2 =
      ∑ d ∈ u.divisors.filter (· % 4 = 1), (d : ℝ) ^ 2 -
        ∑ d ∈ u.divisors.filter (· % 4 = 3), (d : ℝ) ^ 2 := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  have heo : Odd e := Odd.of_dvd_nat hu (Nat.mem_divisors.mp he).1
  have : e % 2 = 1 := Nat.odd_iff.mp heo
  unfold chi4
  split_ifs <;> first | omega | (push_cast; ring)

/-- The odd divisors of $2^a u$ ($u$ odd) are the divisors of $u$. -/
theorem odd_divisors_two_pow_mul (a u : ℕ) (hu : Odd u) :
    (2 ^ a * u).divisors.filter Odd = u.divisors := by
  have hu0 : u ≠ 0 := by rintro rfl; exact absurd hu (by decide)
  ext δ
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, ho⟩
    have hcop : Nat.Coprime δ (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr ho)
    exact ⟨hcop.dvd_of_dvd_mul_left hd, hu0⟩
  · rintro ⟨hd, _⟩
    exact ⟨⟨dvd_mul_of_dvd_right hd _, by positivity⟩, Odd.of_dvd_nat hu hd⟩

/-- $(-1)^{(\delta-1)/2} = \chi_{-4}(\delta)$ for odd $\delta$. -/
theorem neg_one_pow_eq_chi4 (δ : ℕ) (h : Odd δ) : (-1 : ℝ) ^ ((δ - 1) / 2) = chi4 δ := by
  obtain ⟨k, rfl⟩ := h
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have : (2 * (j + j) + 1 - 1) / 2 = 2 * j := by omega
    rw [this, pow_mul]
    have : chi4 (2 * (j + j) + 1) = 1 := by unfold chi4; rw [if_pos (by omega)]
    rw [this]; norm_num
  · subst hj
    have : (2 * (2 * j + 1) + 1 - 1) / 2 = 2 * j + 1 := by omega
    rw [this, pow_succ, pow_mul]
    have : chi4 (2 * (2 * j + 1) + 1) = -1 := by unfold chi4; rw [if_neg (by omega), if_pos (by omega)]
    rw [this]; norm_num

/-- **Jacobi's six-squares formula for every $N \ge 1$, in Smith's form** (Smith,
*Collected Mathematical Papers* I, p. 307): the number of $\vec x \in \mathbb Z^6$ with $x_0^2 + \dots + x_5^2 = N$ is
$$4\sum_{\delta \mid N,\ \delta\ \mathrm{odd}} (-1)^{(\delta-1)/2}\Bigl(4\Bigl(\frac N\delta\Bigr)^2 - \delta^2\Bigr).$$
**Proved** (unconditional). -/
@[kb "smith1894a" "p. 307 (occurrence smith1894-papers1:p307.2) [unverified locator]"]
theorem six_squares (N : ℕ) (hN : 1 ≤ N) :
    (sqRep 6 N : ℤ) = 4 * ∑ δ ∈ N.divisors.filter Odd,
      (-1 : ℤ) ^ ((δ - 1) / 2) * (4 * ((N / δ : ℕ) : ℤ) ^ 2 - (δ : ℤ) ^ 2) := by
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := N) (by omega)
  have hu0 : u ≠ 0 := by rintro rfl; exact absurd hu (by decide)
  have hm0 : 2 ^ a * u ≠ 0 := by positivity
  have h1 := repNum_sumSq_eq_siegel (n := 6) (by norm_num) (by norm_num) (m := ((2 ^ a * u : ℕ) : ℤ))
    (by exact_mod_cast Nat.pos_of_ne_zero hm0)
  have hE := eulerProduct_sumSq_six_all (2 ^ a * u) hm0
  rw [← sqRep_eq_repNum] at h1
  rw [betaInf_sumSq_six, hE, sum_divisors_two_pow_mul a u hu] at h1
  have e2' : ((2 ^ a * u : ℕ) : ℤ) = (2 : ℤ) ^ a * u := by push_cast; ring
  rw [e2', localDensity_sumSq_six_two_all a u hu] at h1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  set S := ∑ d ∈ u.divisors, chi4 d / (d : ℝ) ^ 2 with hS
  set A := (u : ℝ) ^ 2 * S with hA
  have hq := sq_mul_sum_chi4 u hu
  have hAeq := sq_mul_sum_chi4_eq u hu0
  have hD := sum_chi4_sq_eq u hu
  have hsq := chi4_sq_odd hu
  have hAD : A = chi4 u * ∑ d ∈ u.divisors, chi4 d * (d : ℝ) ^ 2 := by
    rw [hD]; exact hq
  have hreal : (sqRep 6 (2 ^ a * u) : ℝ) = 16 * (1 - chi4 u / 4 ^ (a + 1)) * (4 ^ a * A) := by
    rw [h1]
    push_cast
    have : ((2 : ℝ) ^ a * u) ^ 2 = 4 ^ a * (u : ℝ) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm a 2, pow_mul]; norm_num
    rw [this, hA]
    field_simp
    ring
  have hR : ((4 * ∑ δ ∈ (2 ^ a * u).divisors.filter Odd,
      (-1 : ℤ) ^ ((δ - 1) / 2) * (4 * (((2 ^ a * u) / δ : ℕ) : ℤ) ^ 2 - (δ : ℤ) ^ 2) : ℤ) : ℝ) =
      4 * (4 * 4 ^ a * ∑ d ∈ u.divisors, chi4 d * ((u / d : ℕ) : ℝ) ^ 2 -
        ∑ d ∈ u.divisors, chi4 d * (d : ℝ) ^ 2) := by
    rw [odd_divisors_two_pow_mul a u hu]
    push_cast
    have hrhs : ∀ f g : ℕ → ℝ, 4 * 4 ^ a * ∑ d ∈ u.divisors, f d - ∑ d ∈ u.divisors, g d =
        ∑ d ∈ u.divisors, (4 * 4 ^ a * f d - g d) := by
      intro f g; rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hrhs (fun d => chi4 d * ((u / d : ℕ) : ℝ) ^ 2) (fun d => chi4 d * (d : ℝ) ^ 2), Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro δ hδ
    have hdv := (Nat.mem_divisors.mp hδ).1
    have ho : Odd δ := Odd.of_dvd_nat hu hdv
    have hz : ((2 : ℤ) ^ a * (u : ℤ) / (δ : ℤ)) = 2 ^ a * ((u / δ : ℕ) : ℤ) := by
      rw [Int.mul_ediv_assoc _ (by exact_mod_cast hdv)]
      push_cast; rfl
    rw [hz, neg_one_pow_eq_chi4 δ ho]
    push_cast
    rw [← Int.natCast_div, Int.cast_natCast] at *
    have e4 : ((2 : ℝ) ^ a) ^ 2 = 4 ^ a := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, e4]
    ring
  have hfin : ((sqRep 6 (2 ^ a * u) : ℤ) : ℝ) = ((4 * ∑ δ ∈ (2 ^ a * u).divisors.filter Odd,
      (-1 : ℤ) ^ ((δ - 1) / 2) * (4 * (((2 ^ a * u) / δ : ℕ) : ℤ) ^ 2 - (δ : ℤ) ^ 2) : ℤ) : ℝ) := by
    rw [hR, ← hAeq, ← hA]
    have e1 : ((sqRep 6 (2 ^ a * u) : ℤ) : ℝ) = (sqRep 6 (2 ^ a * u) : ℝ) := by push_cast; rfl
    rw [e1, hreal]
    have hAD' : chi4 u * A = ∑ d ∈ u.divisors, chi4 d * (d : ℝ) ^ 2 := by
      rw [hAD, ← mul_assoc, ← sq, hsq, one_mul]
    rw [← hAD']
    field_simp
    ring
  exact_mod_cast hfin

end QuadFormsKB.Historical.SumsOfSquares
