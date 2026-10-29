/-
# Siegel's formula for the sum of four squares, proved

For $I_4 = x_0^2 + x_1^2 + x_2^2 + x_3^2$ and every $m \ge 1$:
$$r_{I_4}(m) = \beta_\infty(m)\prod_p \beta_p(m) = \pi^2 m\prod_p\beta_p(m)$$
(`repNum_Q4_eq_aE`, `fourSquares_siegel`). *Proof:* by the local densities of `Siegel/FourSquaresDensities.lean`,
$\beta_p(m) = (1 - p^{-2})\,c_2(p)\,F(p^{\nu_p})/p^{\nu_p}$ (`localDensity_Q4_eq`), with $c_2(2) = 4/3$, $c_2(p) = 1$ otherwise,
$\nu_p = \mathrm{ord}_p(m)$ and $F(m) = \sum_{d \mid m,\, 4 \nmid d} d$ (multiplicative, `isMultiplicative_sumNotFourDvd`).
So $\prod_p\beta_p(m) = \frac{6}{\pi^2}\cdot\frac43\cdot\frac{F(m)}{m}$ ($\prod_p(1 - p^{-2}) = 1/\zeta(2) = 6/\pi^2$,
`AWS.hasProd_one_sub_inv_sq`), and $\pi^2 m \prod_p\beta_p(m) = 8F(m) = r_{I_4}(m)$ by Jacobi's four-square theorem
(`repNum_sumSq_four`).

Consequences:
* `fourSquaresInputs`: **both fields of the AWS notes' `FourSquaresInputs` are proved**, so the notes' (2.10)–(2.23)
  (`AWS.r4_one`, `AWS.r4_prime`, `AWS.r4_squarefree`) hold unconditionally.
* `siegelFormula_Q4`: `SiegelFormula AWS.Q4` (genus average $a_E(m) = $ `aE`) **given class number one**
  (`FourSquaresClassNumberOne`); class number one is proved in `Siegel/FourSquaresClassNumber.lean`, which gives the
  unconditional `siegelFormula_Q4'`.

Logically this is Siegel's formula for $I_4$ *deduced from* Jacobi's theorem and the local densities, not Siegel's
general proof.
-/
import QuadFormsKB.Siegel.FourSquaresDensities
import QuadFormsKB.Siegel.Formula

namespace QuadFormsKB.Siegel

open LocalDensity ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-! ### The divisor sum $F(m) = \sum_{d \mid m,\ 4 \nmid d} d$ -/

/-- $d \mapsto d$ if $4 \nmid d$, else $0$. -/
def notFourDvd : ArithmeticFunction ℕ := ⟨fun d => if 4 ∣ d then 0 else d, by simp⟩

lemma notFourDvd_apply (d : ℕ) : notFourDvd d = if 4 ∣ d then 0 else d := rfl

lemma four_dvd_of_coprime {a b : ℕ} (h : a.Coprime b) (h4 : 4 ∣ a * b) : 4 ∣ a ∨ 4 ∣ b := by
  have hc : ∀ {x y : ℕ}, ¬ 2 ∣ y → 4 ∣ x * y → 4 ∣ x := fun {x y} hy hxy => by
    have : Nat.Coprime (2 ^ 2) y :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hy)
    exact this.dvd_of_dvd_mul_right hxy
  by_cases hb : 2 ∣ b
  · have ha : ¬ 2 ∣ a := fun ha => Nat.not_coprime_of_dvd_of_dvd (by norm_num) ha hb h
    exact Or.inr (hc ha (by rwa [mul_comm]))
  · exact Or.inl (hc hb h4)

lemma isMultiplicative_notFourDvd : IsMultiplicative notFourDvd := by
  refine ⟨by simp [notFourDvd_apply], fun {a b} h => ?_⟩
  by_cases ha : 4 ∣ a
  · simp [notFourDvd_apply, ha, Dvd.dvd.mul_right ha b]
  by_cases hb : 4 ∣ b
  · simp [notFourDvd_apply, hb, Dvd.dvd.mul_left hb a]
  have hab : ¬ 4 ∣ a * b := fun h4 => (four_dvd_of_coprime h h4).elim ha hb
  simp [notFourDvd_apply, ha, hb, hab]

/-- $F = $ `notFourDvd` $* \zeta$, i.e. $F(m) = \sum_{d \mid m,\ 4 \nmid d} d$. -/
def sumNotFourDvd : ArithmeticFunction ℕ := notFourDvd * ζ

lemma sumNotFourDvd_apply (m : ℕ) :
    sumNotFourDvd m = ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d := by
  rw [sumNotFourDvd, ← natCoe_nat ζ, coe_mul_zeta_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [notFourDvd_apply]
  split_ifs <;> rfl

lemma isMultiplicative_sumNotFourDvd : IsMultiplicative sumNotFourDvd :=
  isMultiplicative_notFourDvd.mul isMultiplicative_zeta

lemma sumNotFourDvd_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) :
    sumNotFourDvd (p ^ k) = ∑ i ∈ Finset.range (k + 1), notFourDvd (p ^ i) := by
  rw [sumNotFourDvd, ← natCoe_nat ζ, coe_mul_zeta_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl

/-- $F(p^k) = 1 + p + \dots + p^k$ for odd $p$. -/
lemma sumNotFourDvd_odd_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    sumNotFourDvd (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  rw [sumNotFourDvd_prime_pow p hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [notFourDvd_apply, if_neg]
  intro h4
  have h2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow ((dvd_trans (by norm_num) h4 : 2 ∣ p ^ i))
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm

/-- $F(2^k) = 1$ for $k = 0$ and $3$ for $k \ge 1$. -/
lemma sumNotFourDvd_two_pow (k : ℕ) : sumNotFourDvd (2 ^ k) = if k = 0 then 1 else 3 := by
  rw [sumNotFourDvd_prime_pow 2 Nat.prime_two]
  rcases k with _ | k
  · simp [notFourDvd_apply]
  · rw [if_neg (Nat.succ_ne_zero k)]
    induction k with
    | zero => simp [Finset.sum_range_succ, notFourDvd_apply]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, notFourDvd_apply, if_pos]
      exact ⟨2 ^ k, by ring⟩

/-! ### The Euler factors -/

/-- The factor $F(p^{\nu})/p^{\nu}$, $\nu = \mathrm{ord}_p(m)$ (equal to $1$ for $p \nmid m$). -/
noncomputable def corrF (m : ℕ) (p : AWS.PrimeIdx) : ℂ :=
  (sumNotFourDvd ((p : ℕ) ^ m.factorization p) : ℂ) / ((p : ℕ) : ℂ) ^ m.factorization p

/-- **The Euler factors of $I_4$:** $\beta_p(m) = (1 - p^{-2})\,c_2(p)\,F(p^{\nu})/p^{\nu}$ for $m \ge 1$, with
$c_2(2) = 4/3$ and $c_2(p) = 1$ for odd $p$ (`AWS.corr2`). -/
theorem localDensity_Q4_eq (m : ℕ) (hm : m ≠ 0) (p : AWS.PrimeIdx) :
    ((localDensity AWS.Q4 p m : ℝ) : ℂ) =
      (1 - 1 / ((p : ℕ) : ℂ) ^ 2) * AWS.corr2 p * corrF m p := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  by_cases h2 : (p : ℕ) = 2
  · have e1 : AWS.corr2 p = 4 / 3 := if_pos h2
    rw [e1, corrF, h2, localDensity_Q4_two_nat m hm, sumNotFourDvd_two_pow]
    split_ifs with hν
    · simp [hν]; norm_num
    · push_cast
      field_simp
      norm_num
  · have e1 : AWS.corr2 p = 1 := if_neg h2
    rw [e1, corrF, localDensity_Q4_odd (p : ℕ) h2 m hm,
      sumNotFourDvd_odd_prime_pow (p : ℕ) p.2 h2]
    set ν := m.factorization p
    push_cast
    rw [mul_one]
    congr 1
    rw [← Finset.sum_range_reflect (fun i => ((p : ℕ) : ℂ) ^ i) (ν + 1), Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ ν := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show ν + 1 - 1 - j = ν - j by omega]
    have hpow : ((p : ℕ) : ℂ) ^ ν = ((p : ℕ) : ℂ) ^ (ν - j) * ((p : ℕ) : ℂ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj']
    rw [hpow, one_div_pow]
    field_simp

theorem hasProd_corrF (m : ℕ) (hm : m ≠ 0) :
    HasProd (corrF m) ((sumNotFourDvd m : ℂ) / (m : ℂ)) := by
  let s : Finset AWS.PrimeIdx :=
    m.primeFactors.preimage (fun p : AWS.PrimeIdx => (p : ℕ)) Subtype.val_injective.injOn
  have h : HasProd (corrF m) (∏ p ∈ s, corrF m p) :=
    hasProd_prod_of_ne_finset_one fun p hp => by
      have hnd : ¬ (p : ℕ) ∣ m := fun hd => hp (Finset.mem_preimage.mpr
        (Nat.mem_primeFactors.mpr ⟨p.2, hd, hm⟩))
      rw [corrF, Nat.factorization_eq_zero_of_not_dvd hnd]
      simp [isMultiplicative_sumNotFourDvd.map_one]
  convert h using 1
  have e : ∀ p ∈ s, corrF m p = (fun x : ℕ =>
      (sumNotFourDvd (x ^ m.factorization x) : ℂ) / (x : ℂ) ^ m.factorization x) (p : ℕ) :=
    fun p _ => rfl
  rw [Finset.prod_congr rfl e, Finset.prod_preimage (fun p : AWS.PrimeIdx => (p : ℕ)) m.primeFactors
    Subtype.val_injective.injOn (fun x : ℕ =>
      (sumNotFourDvd (x ^ m.factorization x) : ℂ) / (x : ℂ) ^ m.factorization x)
    (fun x hx hxr => absurd ⟨⟨x, Nat.prime_of_mem_primeFactors hx⟩, rfl⟩ hxr)]
  rw [Finset.prod_div_distrib, eq_comm]
  congr 1
  · conv_rhs => rw [isMultiplicative_sumNotFourDvd.multiplicative_factorization _ hm]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl

/-- **The Euler product of $I_4$:** $\prod_p\beta_p(m) = \frac{6}{\pi^2}\cdot\frac43\cdot\frac{F(m)}{m} = \frac{8F(m)}{\pi^2 m}$
for $m \ge 1$, $F(m) = \sum_{d \mid m,\ 4 \nmid d} d$. -/
theorem hasProd_localDensity_Q4 (m : ℕ) (hm : m ≠ 0) :
    HasProd (fun p : AWS.PrimeIdx => ((localDensity AWS.Q4 p m : ℝ) : ℂ))
      (6 / (Real.pi : ℂ) ^ 2 * (4 / 3) * ((sumNotFourDvd m : ℂ) / (m : ℂ))) := by
  have := (AWS.hasProd_one_sub_inv_sq.mul AWS.hasProd_corr2).mul (hasProd_corrF m hm)
  convert this using 1
  funext p
  exact localDensity_Q4_eq m hm p

/-! ### Siegel's formula for $I_4$ -/

/-- **Siegel's formula for the sum of four squares (AWS form):** for every $m \ge 1$,
$$r_{I_4}(m) = \pi^2 m\prod_p\beta_p(m)$$
(the product a `tprod` over the primes, in $\mathbb{C}$). This is the field `siegel` of `AWS.FourSquaresInputs`.
*Proof:* `hasProd_localDensity_Q4` and Jacobi's $r_{I_4}(m) = 8F(m)$ (`repNum_sumSq_four`). -/
@[kb "hanke2011aws" "§2.7.2, Thm 2.5.1 for Q = x^2+y^2+z^2+w^2, p. 36"]
theorem fourSquares_siegel (m : ℕ) (hm : 0 < m) :
    (AWS.r4 m : ℂ) = ((Real.pi ^ 2 * m : ℝ) : ℂ) *
      ∏' p : AWS.PrimeIdx, ((localDensity AWS.Q4 p m : ℝ) : ℂ) := by
  rw [(hasProd_localDensity_Q4 m hm.ne').tprod_eq, ← repNum_Q4, ← sumSq_four,
    repNum_sumSq_four (by omega), ← sumNotFourDvd_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
  ring

/-- **The AWS notes' four-squares inputs are proved** (both fields: `siegel` here, `beta_two` in
`localDensity_Q4_two`), so (2.10)–(2.23) (`AWS.r4_one`, `AWS.r4_prime`, `AWS.r4_squarefree`) hold unconditionally. -/
theorem fourSquaresInputs : AWS.FourSquaresInputs :=
  fourSquaresInputs_of_siegel fourSquares_siegel

/-- **$r_{I_4}(m) = a_E^{\mathrm{loc}}(m) = \beta_\infty(m)\prod_p\beta_p(m)$** (`aE`) for every $m \ge 1$, unconditionally. -/
@[kb "hanke2004" "(5.3), p. 368, for x_0^2+x_1^2+x_2^2+x_3^2"]
theorem repNum_Q4_eq_aE (m : ℕ) (hm : 0 < m) : (repNum AWS.Q4 m : ℝ) = aE AWS.Q4 m :=
  fourSquaresInputs_siegel_iff.mp fourSquares_siegel m hm

/-- **Siegel's formula for $I_4$** (`SiegelFormula AWS.Q4`: genus average $a_E(m) = $ `aE`), given that the genus
of $I_4$ has one class (`FourSquaresClassNumberOne`; proved, see `siegelFormula_Q4'`). -/
@[kb "siegel1935" "Hauptsatz, for x_0^2+x_1^2+x_2^2+x_3^2"]
theorem siegelFormula_Q4 (h : FourSquaresClassNumberOne) : SiegelFormula AWS.Q4 := by
  refine ⟨fun m hm => ?_⟩
  rw [genusRepAvg_Q4 h]
  lift m to ℕ using (by omega)
  exact repNum_Q4_eq_aE m (by omega)

/-- Sanity check: the AWS notes' (2.17)–(2.20) now hold without inputs, $r_{I_4}(3) = 8 \cdot 4 = 32$. -/
example : (AWS.r4 3 : ℂ) = 32 := by
  rw [AWS.r4_prime fourSquaresInputs 3 Nat.prime_three (by norm_num)]
  norm_num

end QuadFormsKB.Siegel

/-! ### The AWS notes' four-squares results without inputs

The theorems of `Literature/AWS/FourSquares.lean` take `FourSquaresInputs` as a hypothesis because that directory
does not import `Siegel/`. Here the input is discharged by `Siegel.fourSquaresInputs`. -/

namespace QuadFormsKB.AWS

/-- **The AWS notes' four-squares inputs hold** (`FourSquaresInputs`: Siegel's formula
$r_{I_4}(m) = \pi^2 m\prod_p\beta_p(m)$ for $m \ge 1$ and $\beta_2(m) = 1$ for odd $m$), unconditionally. -/
@[kb "hanke2011aws" "§2.7.2–§2.7.5, pp. 37–40"]
theorem fourSquaresInputs_holds : FourSquaresInputs :=
  Siegel.fourSquaresInputs

/-- **The local densities of $I_4 = x_0^2+x_1^2+x_2^2+x_3^2$ at an odd squarefree $t$** (Lemmas 2.7.4, 2.7.6),
unconditionally: $\beta_p(t) = (1 - p^{-2})\cdot c_2(p)\cdot c_t(p)$ with $c_2(2) = 4/3$, $c_2(p) = 1$ for odd $p$,
$c_t(p) = 1 + 1/p$ for $p \mid t$ and $c_t(p) = 1$ otherwise. -/
@[kb "hanke2011aws" "§2.7.4, Lemmas 2.7.4 and 2.7.6, p. 38"]
theorem beta_eq_uncond (t : ℕ) (ht : Odd t) (hsq : Squarefree t) (p : PrimeIdx) :
    ((LocalDensity.localDensity Q4 p t : ℝ) : ℂ) =
      (1 - 1 / ((p : ℕ) : ℂ) ^ 2) * corr2 p * corrT t p :=
  beta_eq fourSquaresInputs_holds t ht hsq p

/-- **(2.21)–(2.23), p. 40: $r_{I_4}(t) = 8\prod_{p \mid t}(p+1)$ for every odd squarefree $t$**, unconditionally
($r_{I_4}(t)$ is the number of $x \in \mathbb Z^4$ with $x_0^2+x_1^2+x_2^2+x_3^2 = t$). -/
@[kb "hanke2011aws" "§2.7.5, (2.21)-(2.23), p. 40"]
theorem r4_squarefree_uncond (t : ℕ) (ht : Odd t) (hsq : Squarefree t) :
    (r4 t : ℂ) = 8 * ∏ p ∈ t.primeFactors, ((p : ℂ) + 1) :=
  r4_squarefree fourSquaresInputs_holds t ht hsq

/-- **(2.10)–(2.16), p. 39: $r_{I_4}(1) = 8$**, unconditionally. -/
@[kb "hanke2011aws" "§2.7.5, (2.10)-(2.16), p. 39"]
theorem r4_one_uncond : (r4 1 : ℂ) = 8 :=
  r4_one fourSquaresInputs_holds

/-- **(2.17)–(2.20), p. 40: $r_{I_4}(p) = 8(p+1)$ for every odd prime $p$**, unconditionally. -/
@[kb "hanke2011aws" "§2.7.5, (2.17)-(2.20), p. 40"]
theorem r4_prime_uncond (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (r4 p : ℂ) = 8 * ((p : ℂ) + 1) :=
  r4_prime fourSquaresInputs_holds p hp hp2

end QuadFormsKB.AWS
