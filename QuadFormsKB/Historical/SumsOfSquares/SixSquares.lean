/-
# Jacobi's six-squares formula for odd numbers (Eisenstein's wording, 1847)

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`).  Target
(Eisenstein, *Mathematische Abhandlungen*
(1847), 6. *Neue Theoreme der höhern Arithmetik*, p. 195, occurrence `eisenstein1847-abhandlungen:p195.3`, from
Jacobi's expansion of $(2K/\pi)^3$ in the *Fundamenta nova*): for odd $m$,
$$r_6(m) = \begin{cases} 12 & (m \equiv 1 \bmod 4)\\ -20 & (m \equiv 3 \bmod 4)\end{cases}\cdot
  \Bigl(\sum_{d \mid m,\ d \equiv 1 (4)} d^2 - \sum_{d \mid m,\ d \equiv 3 (4)} d^2\Bigr).$$
**Proved** (`six_squares_odd`, unconditional).

**Route** (not Jacobi's): $r_6(m) = \beta_\infty(m)\prod_p\beta_p(m)$ (`repNum_sumSq_eq_siegel`), $\beta_\infty(m) =
\tfrac12\pi^3m^2$, and with $\chi = \chi_{-4}$ and $\nu = \mathrm{ord}_p(m)$:
$\beta_p(m) = (1 - \chi(p)p^{-3})\sum_{i=0}^{\nu}(\chi(p)p^{-2})^i$ for odd $p$ (Hanke's Table 2 and the recursion
(5.7)), $\beta_2(m) = \tfrac34$ or $\tfrac54$ for $m \equiv 1$ or $3 \bmod 4$ (count modulo $8$). With
$\prod_{p}(1 - \chi(p)p^{-3}) = 1/L(3,\chi) = 32/\pi^3$ this gives
$r_6(m) = 16\beta_2(m)\sum_{d \mid m}\chi(d)(m/d)^2$, which is the formula above.
-/
import QuadFormsKB.Historical.SumsOfSquares.Siegel
import QuadFormsKB.Historical.SumsOfSquares.JacobiCounts

namespace QuadFormsKB.Historical.SumsOfSquares

open QuadFormsKB.Siegel QuadFormsKB.LocalDensity

/-- $\chi_{-4}$ as a real function on $\mathbb N$: $1, -1, 0$ for $d \equiv 1, 3$, even. -/
def chi4 (d : ℕ) : ℝ := if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

/-! ### $L(3, \chi_{-4}) = \pi^3/32$ -/

/-- $\sin(\pi n/2) = \chi_{-4}(n)$. -/
theorem sin_pi_mul_nat_div_two_eq_chi4 (n : ℕ) : Real.sin (Real.pi * n / 2) = chi4 n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ n = 4 * q + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have h : Real.pi * ((4 * q + r : ℕ) : ℝ) / 2 = Real.pi * r / 2 + (q : ℤ) * (2 * Real.pi) := by
    push_cast; ring
  rw [h, Real.sin_add_int_mul_two_pi]
  interval_cases r
  · simp [chi4]
  · simp [chi4]
  · simp [chi4]
  · have h3 : Real.pi * ((3 : ℕ) : ℝ) / 2 = Real.pi / 2 + Real.pi := by push_cast; ring
    rw [h3, Real.sin_add_pi, Real.sin_pi_div_two]
    simp [chi4]

/-- **$L(3, \chi_{-4}) = \sum_{n \ge 1}\chi_{-4}(n)n^{-3} = \pi^3/32$** (from Mathlib's `hasSum_one_div_nat_pow_mul_sin`
at $k = 1$, $x = 1/4$: $\sin(\pi n/2) = \chi_{-4}(n)$ and $B_3(1/4) = 3/64$). -/
theorem hasSum_chi4_div_cube : HasSum (fun n : ℕ => chi4 n / (n : ℝ) ^ 3) (Real.pi ^ 3 / 32) := by
  convert hasSum_L_function_mod_four_eval_three using 1
  funext n
  rw [sin_pi_mul_nat_div_two_eq_chi4 n, div_eq_mul_inv, one_div, mul_comm]

/-! ### Local densities -/

/-- For odd $p$, $\bigl(\frac{-1}{p}\bigr) = \chi_{-4}(p)$ (as reals). -/
theorem legendreSym_neg_one_real (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : (legendreSym p (-1) : ℝ) = chi4 p := by
  have hpp : p.Prime := Fact.out
  have h2 : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  rw [legendreSym.at_neg_one hp, ZMod.χ₄_nat_eq_if_mod_four]
  unfold chi4
  rw [if_neg (by omega)]
  split_ifs <;> first | omega | simp

/-- $\chi_{-4}(p)^2 = 1$ for odd $p$. -/
theorem chi4_sq_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : chi4 p ^ 2 = 1 := by
  have hpp : p.Prime := Fact.out
  have h2 : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  unfold chi4
  split_ifs <;> first | omega | norm_num

theorem legendre_six (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (legendreSym p ((-1) ^ (6 / 2) * ∏ i : Fin 6, (1 : ℤ)) : ℝ) = chi4 p := by
  rw [show ((-1 : ℤ) ^ (6 / 2) * ∏ i : Fin 6, (1 : ℤ)) = -1 by simp]
  exact legendreSym_neg_one_real p hp

/-- The non-Zero-type density of $I_6$ at $p^2T$ is $\beta_p(p) = (1 - \chi p^{-3})(1 + \chi p^{-2})$. -/
theorem localDensityOf_nonZero_sumSq_six_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (T : ℤ) :
    localDensityOf (sumSq 6) p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) =
      (1 - chi4 p / (p : ℝ) ^ 3) * (1 + chi4 p / (p : ℝ) ^ 2) := by
  have hpp : p.Prime := Fact.out
  have h1 : padicValInt p (p : ℤ) = 1 := by simp [padicValInt, padicValNat_self]
  have ha := not_dvd_one_sumSq (n := 6) p
  rw [sumSq_eq_diag, localDensityOf_nonZero_diag_sq _ p hp ha T,
    ← localDensity_diag_ord_one (fun _ : Fin 6 => (1 : ℤ)) p hp ha (p : ℤ) h1,
    localDensity_diag_even_ord_one (fun _ : Fin 6 => (1 : ℤ)) p hp ha (by norm_num) (by decide) (p : ℤ)
      dvd_rfl (by
        intro h
        have h' : p ^ 2 ∣ p := by exact_mod_cast h
        have := Nat.le_of_dvd hpp.pos h'
        nlinarith [hpp.two_le]),
    legendre_six p hp]

/-- **$\beta_p$ of $I_6$ at an odd prime, all valuations:** for $p \nmid u$,
$\beta_p(p^a u) = (1 - \chi(p)p^{-3})\sum_{i=0}^{a}(\chi(p)p^{-2})^i$, $\chi = \chi_{-4}$. -/
theorem localDensity_sumSq_six_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ℕ) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    localDensity (sumSq 6) p ((p : ℤ) ^ a * u) =
      (1 - chi4 p / (p : ℝ) ^ 3) * ∑ i ∈ Finset.range (a + 1), (chi4 p / (p : ℝ) ^ 2) ^ i := by
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have ha := not_dvd_one_sumSq (n := 6) p
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 =>
      rw [pow_zero, one_mul, sumSq_eq_diag,
        localDensity_diag_even_unit (fun _ : Fin 6 => (1 : ℤ)) p hp ha (by norm_num) (by decide) u hu,
        legendre_six p hp]
      simp
    | 1 =>
      rw [pow_one, sumSq_eq_diag,
        localDensity_diag_even_ord_one (fun _ : Fin 6 => (1 : ℤ)) p hp ha (by norm_num) (by decide) _
          (dvd_mul_right _ _) (by
            rintro ⟨c, hc⟩
            apply hu
            refine ⟨c, mul_left_cancel₀ (by exact_mod_cast hpp.ne_zero : (p : ℤ) ≠ 0) ?_⟩
            rw [hc]; ring),
        legendre_six p hp]
      simp [Finset.sum_range_succ]
    | a + 2 =>
      have hT : (p : ℤ) ^ a * u ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hpp.ne_zero)) hu0
      have hK := localDensityOf_nonZero_eq (sumSq 6) posDef_sumSq.nondegenerate p (by norm_num) _ hT
      rw [localDensityOf_nonZero_sumSq_six_sq p hp] at hK
      have e : (p : ℤ) ^ (a + 2) * u = (p : ℤ) ^ 2 * ((p : ℤ) ^ a * u) := by ring
      rw [e]
      have hloc : localDensity (sumSq 6) p ((p : ℤ) ^ 2 * ((p : ℤ) ^ a * u)) =
          localDensity (sumSq 6) p ((p : ℤ) ^ a * u) / (p : ℝ) ^ 4 +
            (1 - chi4 p / (p : ℝ) ^ 3) * (1 + chi4 p / (p : ℝ) ^ 2) := by
        rw [show (6 : ℕ) - 2 = 4 from rfl] at hK
        rw [div_eq_mul_inv, mul_comm (localDensity _ _ _)]
        linarith
      rw [hloc, ih a (by omega), sum_range_add_two]
      have hx : (chi4 p / (p : ℝ) ^ 2) ^ 2 = 1 / (p : ℝ) ^ 4 := by
        rw [div_pow, chi4_sq_prime p hp]; ring
      rw [hx]
      field_simp
      ring

/-- Solutions of $\sum_{i<6} x_i^2 \equiv r \pmod 8$ for odd $r$: $24576$ ($r \equiv 1 \bmod 4$), else $40960$. -/
theorem sqTable8_six_odd : ∀ r : ZMod 8, r.val % 2 = 1 →
    sqTable8 6 r = if r.val % 4 = 1 then 24576 else 40960 := by
  decide

/-- **$\beta_2$ of $I_6$ at odd $m$:** $\tfrac34$ for $m \equiv 1 \pmod 4$, $\tfrac54$ for $m \equiv 3 \pmod 4$. -/
theorem localDensity_sumSq_six_two (m : ℤ) (hm : Odd m) :
    localDensity (sumSq 6) 2 m = if m % 4 = 1 then 3 / 4 else 5 / 4 := by
  have hnd : ¬ (4 : ℤ) ∣ m := by obtain ⟨k, rfl⟩ := hm; omega
  have hv : ((((m : ℤ) : ZMod 8)).val : ℤ) = m % 8 := ZMod.val_intCast m
  have hodd : (((m : ℤ) : ZMod 8)).val % 2 = 1 := by obtain ⟨k, rfl⟩ := hm; omega
  rw [localDensity_sumSq_two 6 m hnd, sqCount8_eq 6 (by norm_num), sqTable8_six_odd _ hodd]
  generalize (((m : ℤ) : ZMod 8)).val = v at hv hodd ⊢
  by_cases h4 : m % 4 = 1
  · have : v % 4 = 1 := by omega
    rw [if_pos this, if_pos h4]; norm_num
  · have : ¬ v % 4 = 1 := by omega
    rw [if_neg this, if_neg h4]; norm_num

/-! ### The Euler product -/

/-- $\chi_{-4}$ is multiplicative. -/
theorem chi4_mul (m n : ℕ) : chi4 (m * n) = chi4 m * chi4 n := by
  have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hmn : m * n % 4 = (m % 4) * (n % 4) % 4 := Nat.mul_mod _ _ _
  unfold chi4
  rcases h1 with h | h | h | h <;> rcases h2 with h' | h' | h' | h' <;> simp [hmn, h, h']

/-- $\chi_{-4}$ as a monoid-with-zero homomorphism $\mathbb N \to \mathbb R$. -/
noncomputable def chi4M : ℕ →*₀ ℝ where
  toFun := chi4
  map_zero' := by simp [chi4]
  map_one' := by simp [chi4]
  map_mul' := chi4_mul

/-- $n \mapsto \chi_{-4}(n)/n^3$: completely multiplicative. -/
noncomputable def chi4Cube : ℕ →*₀ ℝ where
  toFun n := chi4 n / (n : ℝ) ^ 3
  map_zero' := by simp [chi4]
  map_one' := by simp [chi4]
  map_mul' m n := by simp only [chi4_mul, Nat.cast_mul, mul_pow, div_mul_div_comm]

/-- $d \mapsto \chi_{-4}(d)/d^2$ as an arithmetic function. -/
noncomputable def chiDiv2 : ArithmeticFunction ℝ := ⟨fun d => chi4 d / (d : ℝ) ^ 2, by simp [chi4]⟩

theorem isMultiplicative_chiDiv2 : ArithmeticFunction.IsMultiplicative chiDiv2 := by
  refine ⟨by simp [chiDiv2, chi4], fun {m n} _ => ?_⟩
  simp only [chiDiv2, ArithmeticFunction.coe_mk, chi4_mul, Nat.cast_mul, mul_pow, div_mul_div_comm]

/-- $\sum_{d \mid m}\chi_{-4}(d)d^{-2} = \prod_{p \mid m}\sum_{i \le v_p(m)}(\chi_{-4}(p)p^{-2})^i$. -/
theorem sum_divisors_chi4_div_sq (m : ℕ) (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2 =
      ∏ p ∈ m.primeFactors, ∑ i ∈ Finset.range (m.factorization p + 1), (chi4 p / (p : ℝ) ^ 2) ^ i := by
  have hmul := (isMultiplicative_chiDiv2.mul ArithmeticFunction.isMultiplicative_zeta.natCast)
  have h := hmul.multiplicative_factorization _ hm
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  have hz : ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2 = ∑ d ∈ m.divisors, chiDiv2 d := rfl
  rw [hz, h, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.divisors_prime_pow hpp, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  show chi4 (p ^ i) / (((p ^ i : ℕ)) : ℝ) ^ 2 = _
  have : chi4 (p ^ i) = chi4 p ^ i := chi4M.map_pow p i
  simp only [Function.Embedding.coeFn_mk, this, Nat.cast_pow, ← pow_mul, div_pow]
  rw [mul_comm]

/-- **Euler product** $\prod_p(1 - \chi_{-4}(p)p^{-3}) = 32/\pi^3$. -/
theorem hasProd_one_sub_chi4_cube :
    HasProd (fun p : AWS.PrimeIdx => 1 - chi4 p / ((p : ℕ) : ℝ) ^ 3) (32 / Real.pi ^ 3) := by
  have hs : Summable fun n : ℕ => chi4 n / (n : ℝ) ^ 3 := hasSum_chi4_div_cube.summable
  have hsn : Summable fun n : ℕ => ‖chi4Cube n‖ := by
    have hs3 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 3 := Real.summable_one_div_nat_pow.mpr (by norm_num)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs3
    show ‖chi4 n / (n : ℝ) ^ 3‖ ≤ 1 / (n : ℝ) ^ 3
    rw [norm_div, norm_pow, Real.norm_natCast]
    have : ‖chi4 n‖ ≤ 1 := by unfold chi4; split_ifs <;> simp
    exact div_le_div_of_nonneg_right this (by positivity)
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsn
  have hval : (∑' n : ℕ, chi4Cube n) = Real.pi ^ 3 / 32 := hasSum_chi4_div_cube.tsum_eq
  rw [hval] at h
  have hpos : Real.pi ^ 3 / 32 ≠ 0 := by positivity
  have h2 := h.inv₀ hpos
  have h3 : HasProd (fun p : Nat.Primes => 1 - chi4 p / ((p : ℕ) : ℝ) ^ 3) (32 / Real.pi ^ 3) := by
    simpa [chi4Cube] using h2
  exact h3

/-- The correction factor $\sum_{i \le v_p(m)}(\chi_{-4}(p)p^{-2})^i$ at the prime $p$. -/
noncomputable def sixG (m : ℕ) (p : AWS.PrimeIdx) : ℝ :=
  ∑ i ∈ Finset.range (m.factorization p + 1), (chi4 p / ((p : ℕ) : ℝ) ^ 2) ^ i

theorem hasProd_sixG (m : ℕ) (hm : m ≠ 0) :
    HasProd (sixG m) (∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2) := by
  let s : Finset AWS.PrimeIdx :=
    m.primeFactors.preimage (fun p : AWS.PrimeIdx => (p : ℕ)) Subtype.val_injective.injOn
  have h : HasProd (sixG m) (∏ p ∈ s, sixG m p) :=
    hasProd_prod_of_ne_finset_one fun p hp => by
      have hnd : ¬ (p : ℕ) ∣ m := fun hd => hp (Finset.mem_preimage.mpr
        (Nat.mem_primeFactors.mpr ⟨p.2, hd, hm⟩))
      rw [sixG, Nat.factorization_eq_zero_of_not_dvd hnd]
      simp
  convert h using 1
  rw [sum_divisors_chi4_div_sq m hm]
  have e : ∀ p ∈ s, sixG m p = (fun x : ℕ =>
      ∑ i ∈ Finset.range (m.factorization x + 1), (chi4 x / (x : ℝ) ^ 2) ^ i) (p : ℕ) :=
    fun p _ => rfl
  rw [Finset.prod_congr rfl e, Finset.prod_preimage (fun p : AWS.PrimeIdx => (p : ℕ)) m.primeFactors
    Subtype.val_injective.injOn (fun x : ℕ =>
      ∑ i ∈ Finset.range (m.factorization x + 1), (chi4 x / (x : ℝ) ^ 2) ^ i)
    (fun x hx hxr => absurd ⟨⟨x, Nat.prime_of_mem_primeFactors hx⟩, rfl⟩ hxr)]

/-- The Euler factor of $I_6$ at $m$ odd, in product form. -/
theorem eulerFactor_sumSq_six (m : ℕ) (hm : Odd m) (p : AWS.PrimeIdx) :
    eulerFactor (sumSq 6) (m : ℤ) p =
      (if (p : ℕ) = 2 then (if m % 4 = 1 then (3 / 4 : ℝ) else 5 / 4) else 1) *
        ((1 - chi4 p / ((p : ℕ) : ℝ) ^ 3) * sixG m p) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases h2 : (p : ℕ) = 2
  · have hnd : ¬ (p : ℕ) ∣ m := by rw [h2]; exact fun h => by obtain ⟨k, rfl⟩ := hm; omega
    have hG : sixG m p = 1 := by
      rw [sixG, Nat.factorization_eq_zero_of_not_dvd hnd]; simp
    have hc : chi4 (p : ℕ) = 0 := by rw [h2]; simp [chi4]
    rw [if_pos h2, hG, hc]
    show localDensity (sumSq 6) (p : ℕ) (m : ℤ) = _
    rw [h2, localDensity_sumSq_six_two (m : ℤ) (by exact_mod_cast hm)]
    have : ((m : ℤ) % 4 = 1) ↔ m % 4 = 1 := by omega
    simp only [this]
    simp
  · rw [if_neg h2, one_mul]
    show localDensity (sumSq 6) (p : ℕ) (m : ℤ) = _
    have hu : ¬ ((p : ℕ) : ℤ) ∣ ((m / (p : ℕ) ^ m.factorization p : ℕ) : ℤ) := by
      exact_mod_cast Nat.not_dvd_ordCompl p.2 hm0
    have e : (m : ℤ) = ((p : ℕ) : ℤ) ^ m.factorization p * ((m / (p : ℕ) ^ m.factorization p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self m p).symm
    rw [e, localDensity_sumSq_six_odd (p : ℕ) h2 _ _ hu]
    rfl

/-- **The Euler product of $I_6$ at odd $m$:**
$\prod_p\beta_p(m) = \beta_2(m)\cdot\frac{32}{\pi^3}\sum_{d \mid m}\chi_{-4}(d)d^{-2}$. -/
theorem eulerProduct_sumSq_six (m : ℕ) (hm : Odd m) :
    eulerProduct (sumSq 6) m =
      (if m % 4 = 1 then 3 / 4 else 5 / 4) * (32 / Real.pi ^ 3) *
        ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  set c : ℝ := if m % 4 = 1 then 3 / 4 else 5 / 4 with hc_def
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
    funext (eulerFactor_sumSq_six m hm)
  have hE : eulerProduct (sumSq 6) (m : ℤ) =
      c * (32 / Real.pi ^ 3 * ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2) := by
    unfold eulerProduct
    rw [hfun]
    exact hall.tprod_eq
  rw [hE]
  ring

/-! ### The headline -/

/-- $\chi_{-4}(n)^2 = 1$ for odd $n$. -/
theorem chi4_sq_odd {n : ℕ} (hn : Odd n) : chi4 n ^ 2 = 1 := by
  have : n % 2 = 1 := Nat.odd_iff.mp hn
  unfold chi4
  split_ifs <;> first | omega | norm_num

/-- $m^2\sum_{d \mid m}\chi_{-4}(d)d^{-2} = \chi_{-4}(m)\bigl(\sum_{d \equiv 1}d^2 - \sum_{d \equiv 3}d^2\bigr)$
for odd $m$ (sums over divisors). -/
theorem sq_mul_sum_chi4 (m : ℕ) (hm : Odd m) :
    (m : ℝ) ^ 2 * ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2 =
      chi4 m * (∑ d ∈ m.divisors.filter (· % 4 = 1), (d : ℝ) ^ 2 -
        ∑ d ∈ m.divisors.filter (· % 4 = 3), (d : ℝ) ^ 2) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have step1 : (m : ℝ) ^ 2 * ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2 =
      ∑ d ∈ m.divisors, chi4 d * ((m / d : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨k, hk⟩ := (Nat.mem_divisors.mp hd).1
    have hd0 : d ≠ 0 := by rintro rfl; simp at hk; exact hm0 hk
    have : m / d = k := by rw [hk]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)
    rw [this, hk]
    push_cast
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    field_simp
  have step2 : ∑ d ∈ m.divisors, chi4 d * ((m / d : ℕ) : ℝ) ^ 2 =
      ∑ e ∈ m.divisors, chi4 (m / e) * (e : ℝ) ^ 2 := by
    rw [← Nat.sum_div_divisors m (fun e => chi4 (m / e) * (e : ℝ) ^ 2)]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.div_div_self (Nat.mem_divisors.mp hd).1 hm0]
  have step3 : ∀ e ∈ m.divisors, chi4 (m / e) * (e : ℝ) ^ 2 =
      chi4 m * ((if e % 4 = 1 then (e : ℝ) ^ 2 else 0) - (if e % 4 = 3 then (e : ℝ) ^ 2 else 0)) := by
    intro e he
    have hed := (Nat.mem_divisors.mp he).1
    have heo : Odd e := Odd.of_dvd_nat hm hed
    have hmul : chi4 m = chi4 e * chi4 (m / e) := by
      rw [← chi4_mul, Nat.mul_div_cancel' hed]
    have hsq := chi4_sq_odd heo
    have h1 : chi4 (m / e) = chi4 e * chi4 m := by
      rw [hmul, ← mul_assoc, ← sq, hsq, one_mul]
    rw [h1]
    have : e % 2 = 1 := Nat.odd_iff.mp heo
    unfold chi4
    split_ifs <;> first | omega | (push_cast; ring)
  rw [step1, step2, Finset.sum_congr rfl step3, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_filter, Finset.sum_filter]

/-- **Jacobi's six-squares formula for odd numbers** (Eisenstein, *Mathematische
Abhandlungen* (1847), 6. *Neue Theoreme der höhern Arithmetik*, p. 195, after Jacobi's *Fundamenta nova*): for odd
$m$, the number of representations of $m$ as an ordered sum of six integer squares is $12$ times (for
$m \equiv 1 \bmod 4$), resp. $-20$ times (for $m \equiv 3 \bmod 4$), the difference between the sum of the squares of the
divisors $\equiv 1 \pmod 4$ and the sum of the squares of the divisors $\equiv 3 \pmod 4$:
$$r_6(m) = \{12, -20\}\cdot\Bigl(\sum_{d \mid m,\ d \equiv 1 (4)} d^2 - \sum_{d \mid m,\ d \equiv 3 (4)} d^2\Bigr).$$
**Proved** (unconditional). -/
@[kb "eisenstein1847" "6. Neue Theoreme der höhern Arithmetik, p. 195 (occurrence eisenstein1847-abhandlungen:p195.3)"]
theorem six_squares_odd (m : ℕ) (hm : Odd m) :
    (sqRep 6 m : ℤ) = (if m % 4 = 1 then 12 else -20) *
      (∑ d ∈ m.divisors.filter (· % 4 = 1), (d : ℤ) ^ 2 - ∑ d ∈ m.divisors.filter (· % 4 = 3), (d : ℤ) ^ 2) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have h1 := repNum_sumSq_eq_siegel (n := 6) (by norm_num) (by norm_num) (m := (m : ℤ))
    (by exact_mod_cast Nat.pos_of_ne_zero hm0)
  have hE := eulerProduct_sumSq_six m hm
  rw [← sqRep_eq_repNum] at h1
  rw [betaInf_sumSq_six, hE] at h1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hq := sq_mul_sum_chi4 m hm
  have hcast : ((sqRep 6 m : ℤ) : ℝ) =
      (if m % 4 = 1 then 12 else -20 : ℝ) *
        (∑ d ∈ m.divisors.filter (· % 4 = 1), (d : ℝ) ^ 2 - ∑ d ∈ m.divisors.filter (· % 4 = 3), (d : ℝ) ^ 2) := by
    have e1 : ((sqRep 6 m : ℤ) : ℝ) = (sqRep 6 m : ℝ) := by push_cast; rfl
    rw [e1, h1]
    push_cast
    have : (16 : ℝ) * ((if m % 4 = 1 then 3 / 4 else 5 / 4 : ℝ) * (m : ℝ) ^ 2 *
        ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2) =
        16 * (if m % 4 = 1 then 3 / 4 else 5 / 4 : ℝ) * ((m : ℝ) ^ 2 * ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2) := by
      ring
    have e2 : Real.pi ^ 3 / 2 * (m : ℝ) ^ 2 * ((if m % 4 = 1 then 3 / 4 else 5 / 4 : ℝ) * (32 / Real.pi ^ 3) *
        ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2) = 16 * (if m % 4 = 1 then 3 / 4 else 5 / 4 : ℝ) *
          ((m : ℝ) ^ 2 * ∑ d ∈ m.divisors, chi4 d / (d : ℝ) ^ 2) := by
      field_simp
      ring
    rw [e2, hq]
    have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by obtain ⟨k, rfl⟩ := hm; omega
    rcases hm4 with h | h
    · have : chi4 m = 1 := by unfold chi4; rw [if_pos h]
      rw [this, if_pos h, if_pos h]; ring
    · have : chi4 m = -1 := by unfold chi4; rw [if_neg (by omega), if_pos h]
      rw [this, if_neg (by omega), if_neg (by omega)]; ring
  have : (((sqRep 6 m : ℤ) : ℝ)) = ((((if m % 4 = 1 then 12 else -20 : ℤ) *
      (∑ d ∈ m.divisors.filter (· % 4 = 1), (d : ℤ) ^ 2 - ∑ d ∈ m.divisors.filter (· % 4 = 3), (d : ℤ) ^ 2) : ℤ)) : ℝ) := by
    rw [hcast]
    push_cast
    split_ifs <;> simp
  exact_mod_cast this

end QuadFormsKB.Historical.SumsOfSquares
