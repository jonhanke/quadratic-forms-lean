/-
# Hanke 2011 (ternary masses), §7: the Dirichlet series $D_{A^*,\lambda;3}$ and $D_{B^*,\lambda;3}$ over $\mathbb{Q}$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §7, pp. 25–26, and Theorem 1.4, p. 2.

**Setting** ($F = \mathbb{Q}$, Corollary 7.2): the distinguished family of square classes is $\lambda(a\mathbb{Z}) = |a|$,
so the coefficient of $N^{-s}$ of $D_{A^*,\lambda;3}(s)$ is $A^*_3(N) = \prod_p A^*_p(N)$ (paper 6, Lemma 4.7), with
$N$ viewed in $\mathbb{Q}_p$: at odd $p$ the factor is $A^*_p(p^{\nu}u)$, $\nu = \operatorname{ord}_p N$ (Table 2;
it depends only on $\nu$), and at $p = 2$ it is `dyadicA` $(\operatorname{ord}_2 N)$ (Table 5.3). For $B^*$ the factor
at $2$ depends on the unit part $u = N/2^{\operatorname{ord}_2 N}$ through $\varepsilon_u = (-1,u)_2$, which is $+1$
iff $u \equiv 1 \pmod 4$ (`negOneChar`). These are `globalA`, `globalB`.

* `cor_7_2_A` (**Corollary 7.2 / Theorem 1.4**, $A^*$ part, **proved**):
  $D_{A^*,\lambda;3}(s) = \dfrac{\zeta(s+1)\zeta(2s+3)}{2^s\,\zeta(3s+6)}$.
* `cor_7_2_B` (**Corollary 7.2 / Theorem 1.4**, $B^*$ part, **corrected**, proved):
  $D_{B^*,\lambda;3}(s) = -\dfrac{\zeta(2s+2)\zeta(s+2)}{2^s\,\zeta(3s+6)}$.
  *Erratum (proposed by the formalization, not yet confirmed by the author):* Corollary 7.2 prints the sign $(-1)^{1+\sigma_-}$,
  depending on the signature $\sigma = (\sigma_+,\sigma_-)$. But $D_{B^*,\lambda;3}$ is built from local data only
  and does not depend on $\sigma$; for $\lambda(a) = |a| > 0$ the sign is $-1$ for every signature (it agrees with
  $(-1)^{1+\sigma_-}$ only when $\sigma_-$ is even). In Theorem 7.1 the sign
  $(-1)^{[F:\mathbb{Q}] + \sum_v \sigma_{v,-}}$ is right when each $\lambda(\mathfrak a)$ is the square class of an
  element of $F^\times$ of sign $(-1)^{\sigma_{v,-}}$ at every real place $v$ (in general it is
  $(-1)^{[F:\mathbb{Q}]}\prod_{v \text{ real}} (-1, \lambda(\mathfrak a))_v$).

Here $\zeta(ks+j)$ is `zetaShift k j`, $1/\zeta(3s+6)$ is `zetaShiftInv 3 6`, and $2^{-s}$ is `twoPowNegS`.
-/
import QuadFormsKB.Literature.Hanke2011Ternary.DyadicEuler
import QuadFormsKB.Literature.Hanke2011Ternary.Dirichlet

namespace QuadFormsKB.Hanke2011Ternary

open PowerSeries Finset ArithmeticFunction

/-- **$\left(\frac{-1}{p}\right)$ for odd $p$, and $(-1, u)_2$ for odd $u$**: $+1$ if $n \equiv 1 \pmod 4$, else $-1$
(as a unit `ℤˣ`). -/
def negOneChar (n : ℕ) : ℤˣ := if n % 4 = 1 then 1 else -1

/-- **The coefficients of $D_{A^*,\lambda;3}(s)$ over $\mathbb{Q}$**, $\lambda(N\mathbb{Z}) = N$:
$A^*_3(N) = A^*_2(N)\prod_{p \mid N,\ p \ne 2} A^*_p(N)$ (for $p \nmid 2N$ the factor is $A^*_p = 1$). -/
@[kb "hanke2011ternary" "§7, Cor. 7.2, p. 26 (coefficients; paper 6, Lemma 4.7)"]
noncomputable def globalA : ArithmeticFunction ℚ :=
  ⟨fun N => if N = 0 then 0 else
    dyadicA (N.factorization 2) * ∏ p ∈ N.primeFactors.erase 2, Astar p (negOneChar p) (N.factorization p) 1,
    by simp⟩

/-- **The coefficients of $D_{B^*,\lambda;3}(s)$ over $\mathbb{Q}$**, $\lambda(N\mathbb{Z}) = N$:
$B^*_3(N) = B^*_2(N)\prod_{p \mid N,\ p \ne 2} B^*_p(N)$, where $B^*_2(N)$ uses $\varepsilon_u = (-1, u)_2$ for the
unit part $u = N/2^{\operatorname{ord}_2 N}$ of $N$ in $\mathbb{Q}_2$. -/
@[kb "hanke2011ternary" "§7, Cor. 7.2, p. 26 (coefficients; paper 6, Lemma 4.7)"]
noncomputable def globalB : ArithmeticFunction ℚ :=
  ⟨fun N => if N = 0 then 0 else
    dyadicB (negOneChar (N / 2 ^ N.factorization 2)) (N.factorization 2) *
      ∏ p ∈ N.primeFactors.erase 2, Bstar p (negOneChar p) (N.factorization p) 1,
    by simp⟩

/-! ### Euler factors -/

theorem prime_one_lt {p : ℕ} (hp : p.Prime) : (1 : ℚ) < p := by exact_mod_cast hp.one_lt

theorem powerSeries_cancel {S T D : PowerSeries ℚ} (hD : constantCoeff D = 1) (h : S * D = T * D) : S = T :=
  mul_right_cancel₀ (fun h0 => by simp [h0] at hD) h

/-- The Euler factor of $\zeta(s+1)\zeta(2s+3)/\zeta(3s+6)$ at $p$. -/
theorem localSeries_gA {p : ℕ} (hp : p.Prime) :
    localSeries (zetaShift 1 1 * zetaShift 2 3 * zetaShiftInv 3 6) p =
      geom 1 (p : ℚ)⁻¹ * geom 2 ((p : ℚ)⁻¹ ^ 3) * (1 - C ((p : ℚ)⁻¹ ^ 6) * X ^ 3) := by
  rw [localSeries_mul _ _ hp, localSeries_mul _ _ hp, localSeries_zetaShift one_pos _ hp,
    localSeries_zetaShift two_pos _ hp, localSeries_zetaShiftInv (by norm_num) _ hp]
  simp only [pow_one, geom]

/-- The Euler factor of $\zeta(2s+2)\zeta(s+2)/\zeta(3s+6)$ at $p$. -/
theorem localSeries_gB {p : ℕ} (hp : p.Prime) :
    localSeries (zetaShift 2 2 * zetaShift 1 2 * zetaShiftInv 3 6) p =
      geom 2 ((p : ℚ)⁻¹ ^ 2) * geom 1 ((p : ℚ)⁻¹ ^ 2) * (1 - C ((p : ℚ)⁻¹ ^ 6) * X ^ 3) := by
  rw [localSeries_mul _ _ hp, localSeries_mul _ _ hp, localSeries_zetaShift two_pos _ hp,
    localSeries_zetaShift one_pos _ hp, localSeries_zetaShiftInv (by norm_num) _ hp]

/-- At an odd prime, $A^*_p(p^\nu) = $ the coefficient of $p^{-\nu s}$ in
$\zeta(s+1)\zeta(2s+3)/\zeta(3s+6)$ (Lemma 3.1). -/
theorem Astar_eq_gA {p : ℕ} (hp : p.Prime) (ε' : ℤˣ) (ν : ℕ) :
    Astar p ε' ν 1 = (zetaShift 1 1 * zetaShift 2 3 * zetaShiftInv 3 6) (p ^ ν) := by
  have h := lemma_3_1 (prime_one_lt hp) ε' 1
  have hS : PowerSeries.mk (fun ν => Astar p ε' ν 1) =
      localSeries (zetaShift 1 1 * zetaShift 2 3 * zetaShiftInv 3 6) p := by
    refine powerSeries_cancel (D := (1 - C (p : ℚ)⁻¹ * X) * (1 - C ((p : ℚ)⁻¹ ^ 3) * X ^ 2)) (by simp) ?_
    rw [h, localSeries_gA hp]
    have h1 := geom_mul 1 one_pos (p : ℚ)⁻¹
    have h2 := geom_mul 2 two_pos ((p : ℚ)⁻¹ ^ 3)
    rw [pow_one] at h1
    linear_combination (-(1 - C ((p : ℚ)⁻¹ ^ 6) * X ^ 3)) * (geom 2 ((p : ℚ)⁻¹ ^ 3) *
      (1 - C ((p : ℚ)⁻¹ ^ 3) * X ^ 2)) * h1 - (1 - C ((p : ℚ)⁻¹ ^ 6) * X ^ 3) * h2
  have := congrArg (coeff ν) hS
  simpa [localSeries] using this

/-- At $p = 2$: `dyadicA (k+1)` is the coefficient of $2^{-ks}$ in $\zeta(s+1)\zeta(2s+3)/\zeta(3s+6)$, and
`dyadicA 0 = 0` (Lemma 6.1). -/
theorem dyadicA_eq_gA :
    PowerSeries.mk dyadicA = X * localSeries (zetaShift 1 1 * zetaShift 2 3 * zetaShiftInv 3 6) 2 := by
  refine powerSeries_cancel (D := (1 - C (1 / 2 : ℚ) * X) * (1 - C (1 / 8 : ℚ) * X ^ 2)) (by simp) ?_
  rw [lemma_6_1, localSeries_gA Nat.prime_two]
  have h1 := geom_mul 1 one_pos ((2 : ℕ) : ℚ)⁻¹
  have h2 := geom_mul 2 two_pos (((2 : ℕ) : ℚ)⁻¹ ^ 3)
  rw [pow_one] at h1
  have e1 : ((2 : ℕ) : ℚ)⁻¹ = 1 / 2 := by norm_num
  have e3 : ((2 : ℕ) : ℚ)⁻¹ ^ 3 = 1 / 8 := by norm_num
  have e6 : ((2 : ℕ) : ℚ)⁻¹ ^ 6 = 1 / 64 := by norm_num
  rw [e3] at h2 ⊢; rw [e6]; rw [e1] at h1 ⊢
  linear_combination (-(X * (1 - C (1 / 64 : ℚ) * X ^ 3))) * (geom 2 (1 / 8) * (1 - C (1 / 8 : ℚ) * X ^ 2)) * h1 -
    X * (1 - C (1 / 64 : ℚ) * X ^ 3) * h2

/-- At an odd prime, $\left(\frac{-1}{p}\right)^\nu B^*_p(p^\nu)$ is the coefficient of $p^{-\nu s}$ in
$\zeta(2s+2)\zeta(s+2)/\zeta(3s+6)$ (Lemma 3.2, rescaled by $X \mapsto \varepsilon' X$). -/
theorem Bstar_eq_gB {p : ℕ} (hp : p.Prime) (ε' : ℤˣ) (ν : ℕ) :
    ((ε' : ℤ) : ℚ) ^ ν * Bstar p ε' ν 1 = (zetaShift 2 2 * zetaShift 1 2 * zetaShiftInv 3 6) (p ^ ν) := by
  have hε : ((ε' : ℤ) : ℚ) ^ 2 = 1 := by rcases Int.units_eq_one_or ε' with h | h <;> simp [h]
  have h := congrArg (rescale ((ε' : ℤ) : ℚ)) (lemma_3_2 (prime_one_lt hp) ε' 1)
  simp only [map_mul, map_add, map_sub, map_one, rescale_X, rescale_C', map_pow] at h
  have hS : PowerSeries.mk (fun ν => ((ε' : ℤ) : ℚ) ^ ν * Bstar p ε' ν 1) =
      localSeries (zetaShift 2 2 * zetaShift 1 2 * zetaShiftInv 3 6) p := by
    refine powerSeries_cancel (D := 1 - C ((p : ℚ)⁻¹ ^ 2) * X ^ 2) (by simp) ?_
    have hr : rescale ((ε' : ℤ) : ℚ) (PowerSeries.mk fun ν => Bstar p ε' ν 1) =
        PowerSeries.mk (fun ν => ((ε' : ℤ) : ℚ) ^ ν * Bstar p ε' ν 1) := by
      rw [rescale_mk]
    rw [← hr, localSeries_gB hp]
    have h1 := geom_mul 1 one_pos ((p : ℚ)⁻¹ ^ 2)
    have h2 := geom_mul 2 two_pos ((p : ℚ)⁻¹ ^ 2)
    rw [pow_one] at h1
    have hX : (C ((ε' : ℤ) : ℚ) * X) ^ 2 = X ^ 2 := by
      rw [mul_pow, ← map_pow, hε, map_one, one_mul]
    rw [hX] at h
    simp only [map_pow]
    rw [h]
    set t := (p : ℚ)⁻¹
    set e := ((ε' : ℤ) : ℚ)
    have hC : C e * C e = (1 : PowerSeries ℚ) := by rw [← map_mul, ← sq, hε, map_one]
    simp only [map_mul, map_pow] at h1 h2 ⊢
    linear_combination (C t ^ 2 * X) * hC - (1 + C t ^ 2 * X + C t ^ 4 * X ^ 2) * h2 -
      (1 + C t ^ 2 * X + C t ^ 4 * X ^ 2) * (geom 2 (t ^ 2) * (1 - C t ^ 2 * X ^ 2)) * h1
  have := congrArg (coeff ν) hS
  simpa [localSeries] using this

/-- At $p = 2$: `dyadicB 1 (k+1)` is minus the coefficient of $2^{-ks}$ in $\zeta(2s+2)\zeta(s+2)/\zeta(3s+6)$, and
`dyadicB 1 0 = 0` (Lemma 6.2 with $\varepsilon_u = 1$). -/
theorem dyadicB_eq_gB :
    PowerSeries.mk (dyadicB 1) = -(X * localSeries (zetaShift 2 2 * zetaShift 1 2 * zetaShiftInv 3 6) 2) := by
  refine powerSeries_cancel (D := 1 - C (1 / 4 : ℚ) * X ^ 2) (by simp) ?_
  rw [lemma_6_2, localSeries_gB Nat.prime_two]
  have h1 := geom_mul 1 one_pos (((2 : ℕ) : ℚ)⁻¹ ^ 2)
  have h2 := geom_mul 2 two_pos (((2 : ℕ) : ℚ)⁻¹ ^ 2)
  rw [pow_one] at h1
  have e2 : ((2 : ℕ) : ℚ)⁻¹ ^ 2 = 1 / 4 := by norm_num
  have e6 : ((2 : ℕ) : ℚ)⁻¹ ^ 6 = 1 / 64 := by norm_num
  rw [e2] at h1 h2 ⊢; rw [e6]
  simp only [Units.val_one, Int.cast_one, map_one, one_mul]
  have e16 : (C (1 / 16 : ℚ) : PowerSeries ℚ) = C (1 / 4) * C (1 / 4) := by rw [← map_mul]; norm_num
  have e64 : (C (1 / 64 : ℚ) : PowerSeries ℚ) = C (1 / 4) * C (1 / 4) * C (1 / 4) := by
    rw [← map_mul, ← map_mul]; norm_num
  rw [e16, e64]
  linear_combination (X * geom 1 (1 / 4) * (1 - C (1 / 4) * C (1 / 4) * C (1 / 4) * X ^ 3)) * h2 +
    (X * (1 + C (1 / 4 : ℚ) * X + C (1 / 4) * C (1 / 4) * X ^ 2)) * h1

/-! ### Assembling the Euler products -/

theorem twoPowNegS_mul_apply (g : ArithmeticFunction ℚ) {N : ℕ} (hN : N ≠ 0) :
    (twoPowNegS * g) N = if 2 ∣ N then g (N / 2) else 0 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => twoPowNegS x * g y)]
  have : ∀ i, twoPowNegS i = if i = 2 then 1 else 0 := fun i => rfl
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Nat.mem_divisors]
  simp [hN]

theorem factorization_two_mul_of_ne {m p : ℕ} (hm : m ≠ 0) (hp : p ≠ 2) :
    (2 * m).factorization p = m.factorization p := by
  rw [Nat.factorization_mul two_ne_zero hm, Finsupp.add_apply, Nat.Prime.factorization Nat.prime_two,
    Finsupp.single_apply, if_neg (Ne.symm hp), zero_add]

theorem factorization_two_mul_two {m : ℕ} (hm : m ≠ 0) : (2 * m).factorization 2 = m.factorization 2 + 1 := by
  rw [Nat.factorization_mul two_ne_zero hm, Finsupp.add_apply, Nat.Prime.factorization Nat.prime_two,
    Finsupp.single_eq_same, add_comm]

theorem primeFactors_two_mul_erase {m : ℕ} (hm : m ≠ 0) :
    (2 * m).primeFactors.erase 2 = m.primeFactors.erase 2 := by
  rw [Nat.primeFactors_mul two_ne_zero hm, Nat.Prime.primeFactors Nat.prime_two]
  ext p; simp only [mem_erase, mem_union, mem_singleton]; tauto

/-- For multiplicative $g$ and $m \ne 0$: $g(m) = g(2^{\operatorname{ord}_2 m})\prod_{p\mid m,\,p\ne2}g(p^{\operatorname{ord}_p m})$. -/
theorem mult_split_two {g : ArithmeticFunction ℚ} (hg : IsMultiplicative g) {m : ℕ} (hm : m ≠ 0) :
    g m = g (2 ^ m.factorization 2) * ∏ p ∈ m.primeFactors.erase 2, g (p ^ m.factorization p) := by
  rw [hg.multiplicative_factorization g hm, Finsupp.prod, Nat.support_factorization]
  by_cases h2 : 2 ∈ m.primeFactors
  · rw [← Finset.mul_prod_erase _ _ h2]
  · rw [Finset.erase_eq_of_notMem h2, Nat.factorization_eq_zero_of_not_dvd
      (fun hd => h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hm⟩)), pow_zero, hg.map_one, one_mul]

/-- **Corollary 7.2 / Theorem 1.4, $A^*$ part** (Hanke 2011, pp. 2 and 26), $F = \mathbb{Q}$,
$\lambda(a\mathbb{Z}) = |a|$:
$$D_{A^*,\lambda;3}(s) = \frac{\zeta(s+1)\,\zeta(2s+3)}{2^s\,\zeta(3s+6)}$$
as formal Dirichlet series. -/
@[kb "hanke2011ternary" "§7, Cor. 7.2, p. 26; Thm. 1.4, p. 2"]
theorem cor_7_2_A : globalA = twoPowNegS * (zetaShift 1 1 * zetaShift 2 3 * zetaShiftInv 3 6) := by
  set g := zetaShift 1 1 * zetaShift 2 3 * zetaShiftInv 3 6
  have hg : IsMultiplicative g :=
    ((isMultiplicative_zetaShift one_pos 1).mul (isMultiplicative_zetaShift two_pos 3)).mul
      (isMultiplicative_zetaShiftInv (by norm_num) 6)
  have h2 : ∀ k, dyadicA (k + 1) = g (2 ^ k) := fun k => by
    have := congrArg (coeff (k + 1)) dyadicA_eq_gA
    simp only [coeff_mk, coeff_succ_X_mul, localSeries] at this
    exact this
  have h0 : dyadicA 0 = 0 := by
    have := congrArg (coeff 0) dyadicA_eq_gA
    simpa using this
  ext N
  by_cases hN : N = 0
  · subst hN; simp
  rw [twoPowNegS_mul_apply g hN]
  show (if N = 0 then 0 else _) = _
  rw [if_neg hN]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; simp at hN
    rw [Nat.mul_div_cancel_left _ two_pos, factorization_two_mul_two hm, h2, primeFactors_two_mul_erase hm,
      mult_split_two hg hm]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' := Finset.mem_erase.mp hp
    rw [factorization_two_mul_of_ne hm hp'.1, Astar_eq_gA (Nat.prime_of_mem_primeFactors hp'.2)]
  · rw [Nat.factorization_eq_zero_of_not_dvd hd, h0, zero_mul]

theorem negOneChar_mul {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    negOneChar (a * b) = negOneChar a * negOneChar b := by
  have ha' : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hb' : b % 4 = 1 ∨ b % 4 = 3 := by omega
  unfold negOneChar
  rw [Nat.mul_mod]
  rcases ha' with h | h <;> rcases hb' with h' | h' <;> simp [h, h'] <;> decide

theorem negOneChar_pow {a : ℕ} (ha : a % 2 = 1) (e : ℕ) : negOneChar (a ^ e) = negOneChar a ^ e := by
  induction e with
  | zero => simp [negOneChar]
  | succ e ih =>
    rw [pow_succ, negOneChar_mul (by simp [Nat.pow_mod, ha]) ha, ih, pow_succ]

theorem negOneChar_prod (S : Finset ℕ) (e : ℕ → ℕ) (hS : ∀ p ∈ S, p % 2 = 1) :
    negOneChar (∏ p ∈ S, p ^ e p) = ∏ p ∈ S, negOneChar p ^ e p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [negOneChar]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hS' : ∀ p ∈ S, p % 2 = 1 := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hodd : (∏ p ∈ S, p ^ e p) % 2 = 1 := by
      rw [Finset.prod_nat_mod]
      rw [Finset.prod_congr rfl (fun p hp => by rw [Nat.pow_mod, hS' p hp, one_pow])]
      simp
    have ha2 := hS a (Finset.mem_insert_self a S)
    rw [negOneChar_mul (by simp [Nat.pow_mod, ha2]) hodd, negOneChar_pow ha2, ih hS']

/-- The odd part $N/2^{\operatorname{ord}_2 N}$ of $N \ne 0$ is $\prod_{p \mid N,\, p \ne 2} p^{\operatorname{ord}_p N}$. -/
theorem oddPart_eq_prod {N : ℕ} (hN : N ≠ 0) :
    N / 2 ^ N.factorization 2 = ∏ p ∈ N.primeFactors.erase 2, p ^ N.factorization p := by
  have hN' := Nat.prod_factorization_pow_eq_self hN
  rw [Finsupp.prod, Nat.support_factorization] at hN'
  by_cases h2 : 2 ∈ N.primeFactors
  · have hsplit : N = 2 ^ N.factorization 2 * ∏ p ∈ N.primeFactors.erase 2, p ^ N.factorization p := by
      conv_lhs => rw [← hN']
      rw [← Finset.mul_prod_erase _ _ h2]
    nth_rewrite 1 [hsplit]
    rw [Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  · rw [Finset.erase_eq_of_notMem h2, hN', Nat.factorization_eq_zero_of_not_dvd
      (fun hd => h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hN⟩)), pow_zero, Nat.div_one]

/-- **Corollary 7.2 / Theorem 1.4, $B^*$ part, corrected** (Hanke 2011, pp. 2 and 26), $F = \mathbb{Q}$,
$\lambda(a\mathbb{Z}) = |a|$:
$$D_{B^*,\lambda;3}(s) = -\,\frac{\zeta(2s+2)\,\zeta(s+2)}{2^s\,\zeta(3s+6)}$$
as formal Dirichlet series, for every signature. *Erratum (proposed by the formalization, not yet confirmed by the author):* the
paper prints the sign $(-1)^{1+\sigma_-}$; see the module docstring. Theorem 1.4 (positive definite,
$\sigma_- = 0$) agrees. -/
@[kb "hanke2011ternary" "§7, Cor. 7.2, p. 26 (sign corrected); Thm. 1.4, p. 2"]
theorem cor_7_2_B : globalB = -(twoPowNegS * (zetaShift 2 2 * zetaShift 1 2 * zetaShiftInv 3 6)) := by
  set g := zetaShift 2 2 * zetaShift 1 2 * zetaShiftInv 3 6
  have hg : IsMultiplicative g :=
    ((isMultiplicative_zetaShift two_pos 2).mul (isMultiplicative_zetaShift one_pos 2)).mul
      (isMultiplicative_zetaShiftInv (by norm_num) 6)
  have h2 : ∀ k, dyadicB 1 (k + 1) = -g (2 ^ k) := fun k => by
    have := congrArg (coeff (k + 1)) dyadicB_eq_gB
    simp only [coeff_mk, map_neg, coeff_succ_X_mul, localSeries] at this
    exact this
  have h0 : ∀ εu, dyadicB εu 0 = 0 := fun εu => by
    have := congrArg (coeff 0) dyadicB_eq_gB
    simp only [coeff_mk, map_neg, coeff_zero_X_mul, neg_zero, dyadicB, Units.val_one, Int.cast_one] at this
    simp only [dyadicB]
    have hm : dyadicBmag 0 = 0 := by linarith
    rw [hm]; ring
  have hsign : ∀ εu h, dyadicB εu h = ((εu : ℤ) : ℚ) * dyadicB 1 h := fun εu h => by
    simp only [dyadicB, Units.val_one, Int.cast_one]; ring
  ext N
  by_cases hN : N = 0
  · subst hN; simp
  rw [ArithmeticFunction.neg_apply, twoPowNegS_mul_apply g hN]
  show (if N = 0 then 0 else _) = _
  rw [if_neg hN]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; simp at hN
    rw [Nat.mul_div_cancel_left _ two_pos, oddPart_eq_prod hN, factorization_two_mul_two hm, hsign, h2,
      primeFactors_two_mul_erase hm, mult_split_two hg hm]
    have hodd : ∀ p ∈ m.primeFactors.erase 2, p % 2 = 1 := fun p hp => by
      have hp' := Finset.mem_erase.mp hp
      exact (Nat.prime_of_mem_primeFactors hp'.2).eq_two_or_odd.resolve_left hp'.1
    rw [Finset.prod_congr rfl (fun p hp => by rw [factorization_two_mul_of_ne hm (Finset.mem_erase.mp hp).1]),
      negOneChar_prod _ _ hodd]
    push_cast
    have key : (∏ p ∈ m.primeFactors.erase 2, ((negOneChar p : ℤ) : ℚ) ^ m.factorization p) *
        ∏ p ∈ m.primeFactors.erase 2, Bstar p (negOneChar p) ((2 * m).factorization p) 1 =
        ∏ p ∈ m.primeFactors.erase 2, g (p ^ m.factorization p) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp' := Finset.mem_erase.mp hp
      rw [factorization_two_mul_of_ne hm hp'.1, ← Bstar_eq_gB (Nat.prime_of_mem_primeFactors hp'.2)]
    linear_combination (-g (2 ^ m.factorization 2)) * key
  · rw [Nat.factorization_eq_zero_of_not_dvd hd, h0, zero_mul, neg_zero]

end QuadFormsKB.Hanke2011Ternary
