/-
# Conway–Sloane, Ch. 15, §9.7: Corollary 22

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, Cor. 22, p. 395
(`conwaysloane1999`).

**Proves**
* `corollary22_ge_three` (unconditional) and `corollary22 : BinaryOneClassUpTo16 → Corollary22Statement` (the case
  $n = 2$ from the named statement `BinaryOneClassUpTo16`, the book's appeal to Table 15.2).
* `corollary22_core`: for $n \ge 3$, an indefinite form with more than one class in its genus has
  $\lvert d\rvert \ge d_0(n)$, given (for odd $n$ and odd $d$) an element of odd order in $\theta(\Lambda_2)$.
  The case analysis is the one of Thm. 21 with the sizes of the bounds of Thm. 20; for odd $n$ and $k = 5$ the book's
  bound $2 \cdot 5^{\binom n2}$ needs the extra step `isTractable_five_of_odd_order`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Final2
import QuadFormsKB.Literature.ConwaySloane.Section9Cor22Aux

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

open scoped Classical

variable {n : ℕ}

/-! ### Sizes -/

theorem d0_le_two_mul_five_pow (hn : 3 ≤ n) : d0 n ≤ 2 * 5 ^ n.choose 2 := by
  unfold d0
  rw [if_neg (by omega)]
  split_ifs with h3 h
  · subst h3; norm_num [Nat.choose]
  · omega
  · exact le_rfl

theorem d0_mul_four_pow_le (hn : 3 ≤ n) : d0 n * 4 ^ (n / 2) ≤ 2 ^ n * 5 ^ n.choose 2 := by
  unfold d0
  rw [if_neg (by omega)]
  split_ifs with h3 h
  · subst h3; norm_num [Nat.choose]
  · have : 4 ^ (n / 2) = 2 ^ n := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; omega
    rw [this, mul_comm]
  · have : 2 * 4 ^ (n / 2) = 2 ^ n := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']; congr 1; omega
    rw [show 2 * 5 ^ n.choose 2 * 4 ^ (n / 2) = (2 * 4 ^ (n / 2)) * 5 ^ n.choose 2 by ring, this]

theorem d0_mul_four_pow_le_eight (hn : 3 ≤ n) : d0 n * 4 ^ (n / 2) ≤ 8 ^ n.choose 2 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · obtain rfl : n = 3 := by omega
    norm_num [d0, Nat.choose]
  · exact (d0_mul_four_pow_le hn).trans (two_pow_mul_five_pow_le_eight_pow n h)

theorem two_mul_five_pow_le_thirteen_pow : ∀ m : ℕ, 1 ≤ m → 2 * 5 ^ m ≤ 13 ^ m
  | 0, h => by omega
  | 1, _ => by norm_num
  | m + 2, _ => by
    have := two_mul_five_pow_le_thirteen_pow (m + 1) (by omega)
    rw [pow_succ 5 (m + 1), pow_succ 13 (m + 1)]
    calc 2 * (5 ^ (m + 1) * 5) = (2 * 5 ^ (m + 1)) * 5 := by ring
      _ ≤ 13 ^ (m + 1) * 13 := Nat.mul_le_mul this (by norm_num)

theorem one_le_choose_two (hn : 3 ≤ n) : 1 ≤ n.choose 2 := Nat.choose_pos (by omega)

theorem natAbs_le_of_dvd {d : ℤ} (hd : d ≠ 0) {x : ℕ} (h : (x : ℤ) ∣ d) : x ≤ d.natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr hd) (Int.natCast_dvd.mp h)

/-- A large prime power factor of $d$ gives $\lvert d\rvert \ge d_0(n)$. -/
theorem d0_le_of_dvd (hn : 3 ≤ n) {d : ℤ} (hd : d ≠ 0) {k : ℕ} (hk : 13 ≤ k) (h : (k : ℤ) ^ n.choose 2 ∣ d) :
    d0 n ≤ d.natAbs := by
  have h1 : k ^ n.choose 2 ≤ d.natAbs := natAbs_le_of_dvd hd (by exact_mod_cast h)
  calc d0 n ≤ 2 * 5 ^ n.choose 2 := d0_le_two_mul_five_pow hn
    _ ≤ 13 ^ n.choose 2 := two_mul_five_pow_le_thirteen_pow _ (one_le_choose_two hn)
    _ ≤ k ^ n.choose 2 := Nat.pow_le_pow_left hk _
    _ ≤ _ := h1

/-! ### The $2$-adic divisibilities in the form $2^m \mid d$ -/

theorem two_pow_dvd_of_four_dvd {d : ℤ} (h : (4 : ℤ) ^ n.choose 2 ∣ 4 ^ (n / 2) * d) :
    (2 : ℤ) ^ (2 * n.choose 2 - 2 * (n / 2)) ∣ d := by
  rw [four_pow_choose_eq] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp h

theorem two_pow_dvd_of_eight_dvd {d : ℤ} (h : (8 : ℤ) ^ n.choose 2 ∣ 4 ^ (n / 2) * d) :
    (2 : ℤ) ^ (3 * n.choose 2 - 2 * (n / 2)) ∣ d := by
  rw [eight_pow_choose_eq] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp h

/-- The place of $2$ lies in the set of primes dividing $2\det H$. -/
theorem exists_two_mem_primeSet {m : ℤ} (hm : m ≠ 0) :
    ∃ p : primeSet (2 * m), primeOf p.1 = 2 := by
  let v2 := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩
  have hv2 : primeOf v2 = 2 :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨2, Nat.prime_two⟩)
  have hv2' : Rat.HeightOneSpectrum.natGenerator v2 = 2 := hv2
  refine ⟨⟨v2, ?_⟩, hv2⟩
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors]
  refine ⟨by rw [hv2']; exact Nat.prime_two, ?_, by simp [hm]⟩
  rw [hv2', Int.natAbs_mul]
  exact dvd_mul_right _ _

/-! ### Corollary 22 for $n \ge 3$ -/

/-- **Corollary 22, $n \ge 3$, core** (the odd-order element of $\theta(\Lambda_2)$ for odd $n$ and odd $d$ as the
hypothesis `hodd`). -/
theorem corollary22_core (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (h : MoreThanOneClass A)
    (hodd : ∀ p2 : HeightOneSpectrum (𝓞 ℚ), primeOf p2 = 2 → n % 2 = 1 → ¬ (2 : ℤ) ∣ A.det →
      ∃ c : (p2.adicCompletion ℚ)ˣ, c ∈ localSpinorNormGroup (csQ A) (csQ_nondegenerate hA hd) p2 stdLat ∧
        Valued.v (c : p2.adicCompletion ℚ) = exp (-1 : ℤ)) :
    d0 n ≤ A.det.natAbs := by
  set P := primeSet (2 * (Cassels.Ch8Ex2.gramForm A).hessian.det)
  have hQ := csQ_nondegenerate hA hd
  set T := IsTractable (csQ A) hQ stdLat P with hT
  have hPd := primeSet_spec hA hd
  obtain ⟨p, hp⟩ := exists_not_isTractable hn hA hd hind P hPd h
  have h20a : ∀ q : P, primeOf q.1 ≠ 2 → ¬ T q → ((primeOf q.1 : ℕ) : ℤ) ^ n.choose 2 ∣ A.det :=
    fun q hq hnt => theorem20a hA hd P q hq hnt
  have hC1 := one_le_choose_two hn
  have hprime : ∀ q : P, (primeOf q.1).Prime := fun q => Rat.HeightOneSpectrum.prime_natGenerator q.1
  have hcop : ∀ a b : ℕ, Nat.Coprime a b → ∀ m : ℕ, IsCoprime ((a : ℤ) ^ m) ((b : ℤ) ^ m) := by
    intro a b hab m
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hab
  -- two intractable odd primes give `|d| ≥ (pq)^C ≥ 15^C`
  have two_odd : ∀ q₁ q₂ : P, q₁ ≠ q₂ → primeOf q₁.1 ≠ 2 → primeOf q₂.1 ≠ 2 → ¬ T q₁ → ¬ T q₂ →
      d0 n ≤ A.det.natAbs := by
    intro q₁ q₂ hne h1 h2 n1 n2
    have hne' : primeOf q₁.1 ≠ primeOf q₂.1 := fun e => hne (Subtype.ext (primeOf_injective e))
    have hd12 : (((primeOf q₁.1 * primeOf q₂.1 : ℕ) : ℤ)) ^ n.choose 2 ∣ A.det := by
      push_cast; rw [mul_pow]
      exact (hcop _ _ ((Nat.coprime_primes (hprime q₁) (hprime q₂)).mpr hne') _).mul_dvd (h20a q₁ h1 n1)
        (h20a q₂ h2 n2)
    refine d0_le_of_dvd hn hd ?_ hd12
    have a1 := (hprime q₁).two_le
    have a2 := (hprime q₂).two_le
    have b1 : 3 ≤ primeOf q₁.1 := by omega
    have b2 : 3 ≤ primeOf q₂.1 := by omega
    have f1 : primeOf q₁.1 ≠ 4 := fun e => by have := hprime q₁; rw [e] at this; norm_num at this
    have f2 : primeOf q₂.1 ≠ 4 := fun e => by have := hprime q₂; rw [e] at this; norm_num at this
    rcases Nat.lt_or_ge (primeOf q₁.1) 5 with c1 | c1 <;> rcases Nat.lt_or_ge (primeOf q₂.1) 5 with c2 | c2
    · exfalso; exact hne' (by omega)
    · nlinarith
    · nlinarith
    · nlinarith
  by_cases hA1 : ∃ q : P, ¬ T q ∧ primeOf q.1 % 4 = 1
  · obtain ⟨q, hq, hq1⟩ := hA1
    have hq2 : primeOf q.1 ≠ 2 := by omega
    by_cases hq5 : primeOf q.1 = 5
    · have h5d : (5 : ℤ) ^ n.choose 2 ∣ A.det := by
        have := h20a q hq2 hq; rw [hq5] at this; exact_mod_cast this
      by_cases hev : n % 2 = 0
      · have : d0 n = 5 ^ n.choose 2 := by
          unfold d0; rw [if_neg (by omega), if_neg (by omega), if_pos hev]
        rw [this]; exact natAbs_le_of_dvd hd (by exact_mod_cast h5d)
      · have hodd' : n % 2 = 1 := by omega
        by_cases h2d : (2 : ℤ) ∣ A.det
        · have h25 : ((2 * 5 ^ n.choose 2 : ℕ) : ℤ) ∣ A.det := by
            push_cast
            have hc : IsCoprime (2 : ℤ) ((5 : ℤ) ^ n.choose 2) := IsCoprime.pow_right ⟨-2, 1, by norm_num⟩
            exact hc.mul_dvd h2d h5d
          exact (d0_le_two_mul_five_pow hn).trans (natAbs_le_of_dvd hd h25)
        · -- `d` odd: `5` would be tractable
          by_cases hother : ∃ r : P, r ≠ q ∧ ¬ T r
          · obtain ⟨r, hrq, hr⟩ := hother
            by_cases hr2 : primeOf r.1 = 2
            · exfalso
              have h4 := two_pow_dvd_of_four_dvd (theorem20c hA hd P r hr2 hr)
              have hm : 1 ≤ 2 * n.choose 2 - 2 * (n / 2) := by
                have : n ≤ n.choose 2 := by
                  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
                  exact Nat.mul_le_mul_left n (by omega)
                omega
              exact h2d (dvd_trans (dvd_pow_self 2 (by omega)) h4)
            · exact two_odd q r (Ne.symm hrq) hq2 hr2 hq hr
          · push Not at hother
            exfalso
            obtain ⟨p2, hp2⟩ := exists_two_mem_primeSet (hessian_det_csForm_ne_zero hA hd)
            obtain ⟨c, hc, hcv⟩ := hodd p2.1 hp2 hodd' h2d
            exact hq (isTractable_five_of_odd_order (csQ A) hQ stdLat P hn q p2 hq5 hp2
              hother hc hcv)
    · refine d0_le_of_dvd hn hd ?_ (h20a q hq2 hq)
      have := (hprime q).two_le
      by_contra hlt
      push Not at hlt
      have hq' := hprime q
      interval_cases h : primeOf q.1 <;> simp_all <;> norm_num at hq'
  push Not at hA1
  -- (B) two odd intractable primes
  by_cases hB : ∃ q₁ q₂ : P, q₁ ≠ q₂ ∧ primeOf q₁.1 ≠ 2 ∧ primeOf q₂.1 ≠ 2 ∧ ¬ T q₁ ∧ ¬ T q₂
  · obtain ⟨q₁, q₂, hne, h1, h2, n1, n2⟩ := hB
    exact two_odd q₁ q₂ hne h1 h2 n1 n2
  push Not at hB
  have hC4 : 4 ^ n.choose 2 = 4 ^ (n / 2) * 2 ^ (2 * n.choose 2 - 2 * (n / 2)) := by
    have := four_pow_choose_eq n; exact_mod_cast this
  have hC8 : 8 ^ n.choose 2 = 4 ^ (n / 2) * 2 ^ (3 * n.choose 2 - 2 * (n / 2)) := by
    have := eight_pow_choose_eq n; exact_mod_cast this
  have h4pos : 0 < 4 ^ (n / 2) := by positivity
  by_cases h2 : ∃ q : P, ¬ T q ∧ primeOf q.1 = 2
  · obtain ⟨q, hq, hq2⟩ := h2
    have hm := two_pow_dvd_of_four_dvd (theorem20c hA hd P q hq2 hq)
    by_cases hC : ∃ q' : P, ¬ T q' ∧ primeOf q'.1 ≠ 2
    · -- (C) `2` and an odd prime intractable
      obtain ⟨q', hq', hq'2⟩ := hC
      have hdq : ((2 ^ (2 * n.choose 2 - 2 * (n / 2)) * primeOf q'.1 ^ n.choose 2 : ℕ) : ℤ) ∣ A.det := by
        push_cast
        have hc : IsCoprime ((2 : ℤ) ^ (2 * n.choose 2 - 2 * (n / 2))) (((primeOf q'.1 : ℕ) : ℤ) ^ n.choose 2) := by
          apply IsCoprime.pow
          rw [Int.isCoprime_iff_gcd_eq_one]
          exact_mod_cast (Nat.coprime_primes Nat.prime_two (hprime q')).mpr (Ne.symm hq'2)
        exact hc.mul_dvd hm (h20a q' hq'2 hq')
      have hle := natAbs_le_of_dvd hd hdq
      have h3 : 3 ≤ primeOf q'.1 := by have := (hprime q').two_le; omega
      have key : d0 n * 4 ^ (n / 2) ≤ 2 ^ (2 * n.choose 2 - 2 * (n / 2)) * 3 ^ n.choose 2 * 4 ^ (n / 2) := by
        calc d0 n * 4 ^ (n / 2) ≤ 2 ^ n * 5 ^ n.choose 2 := d0_mul_four_pow_le hn
          _ ≤ 12 ^ n.choose 2 := two_pow_mul_five_pow_le_twelve_pow n hn
          _ = 4 ^ n.choose 2 * 3 ^ n.choose 2 := by rw [← mul_pow]; norm_num
          _ = _ := by rw [hC4]; ring
      have key' := Nat.le_of_mul_le_mul_right key h4pos
      calc d0 n ≤ 2 ^ (2 * n.choose 2 - 2 * (n / 2)) * 3 ^ n.choose 2 := key'
        _ ≤ 2 ^ (2 * n.choose 2 - 2 * (n / 2)) * primeOf q'.1 ^ n.choose 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
        _ ≤ _ := hle
    · -- (D) `2` the only intractable prime
      push Not at hC
      have hoth : ∀ q' : P, q' ≠ q → T q' := fun q' hq' => by
        by_contra hnt
        exact hq' (Subtype.ext (primeOf_injective ((hC q' hnt).trans hq2.symm)))
      have h8 := two_pow_dvd_of_eight_dvd (theorem20d hn hA hd hind P q hq2 hoth hq)
      have hle := natAbs_le_of_dvd hd (x := 2 ^ (3 * n.choose 2 - 2 * (n / 2))) (by exact_mod_cast h8)
      have key : d0 n * 4 ^ (n / 2) ≤ 2 ^ (3 * n.choose 2 - 2 * (n / 2)) * 4 ^ (n / 2) := by
        calc d0 n * 4 ^ (n / 2) ≤ 8 ^ n.choose 2 := d0_mul_four_pow_le_eight hn
          _ = _ := by rw [hC8, mul_comm]
      exact (Nat.le_of_mul_le_mul_right key h4pos).trans hle
  · -- (E) `2` tractable: the intractable `p` is odd, `≡ 3 (mod 4)`, and the only one: Thm. 20 (b)
    push Not at h2
    exfalso
    have hp2 : primeOf p.1 ≠ 2 := fun e => h2 p hp e
    have hp3 : primeOf p.1 % 4 = 3 := by
      rcases primeOf_odd_mod_four hp2 with h1 | h3
      · exact absurd h1 (hA1 p hp)
      · exact h3
    refine theorem20b (csQ A) hQ stdLat P hn hind p hp3 ⟨hp, fun q hqp => ?_⟩
    by_contra hq
    have hq2 : primeOf q.1 ≠ 2 := fun e => h2 q hq e
    exact hq (hB p q (Ne.symm hqp) hp2 hq2 hp)

section Hci

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- On $\mathbb Z_p^n$ the polar form $B = 2\,xAy^{\mathsf T}$ of a Gram matrix takes values in $2\mathbb Z_p$. -/
theorem hci_std {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ x ∈ loc v (stdLat : Lat ℚ n).1, ∀ y ∈ loc v (stdLat : Lat ℚ n).1,
      Valued.v (qbil (csQ A) (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ) := by
  intro x hx y hy
  rw [loc_std_eq_locAct_one, mem_locAct] at hx hy
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  rw [mem_std_iff] at hc hd
  rw [qbil_mulVec_locGram, dotProduct]
  refine Valuation.map_sum_le _ fun k _ => ?_
  have hrow : Valued.v ((locGram (csQ A) v 1 *ᵥ d) k) ≤ Valued.v (2 : v.adicCompletion ℚ) := by
    rw [Matrix.mulVec, dotProduct]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [locGram_one_int, hessian_csForm hA, map_mul]
    have e : (((((2 : ℤ) • A) k l : ℤ)) : v.adicCompletion ℚ) = 2 * ((A k l : ℤ) : v.adicCompletion ℚ) := by
      simp [Matrix.smul_apply]
    rw [e, map_mul]
    calc Valued.v (2 : v.adicCompletion ℚ) * Valued.v ((A k l : ℤ) : v.adicCompletion ℚ) * Valued.v (d l)
        ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl (valued_intCast_le_one' v _)) (hd l)
      _ = _ := by rw [mul_one, mul_one]
  rw [map_mul]
  calc Valued.v (c k) * Valued.v ((locGram (csQ A) v 1 *ᵥ d) k) ≤ 1 * Valued.v (2 : v.adicCompletion ℚ) :=
        mul_le_mul' (hc k) hrow
    _ = _ := one_mul _

end Hci

/-- **Corollary 22 for $n \ge 3$** (Conway–Sloane, §9.7, p. 395): an indefinite form of dimension $n \ge 3$ with more
than one class in its genus has $\lvert d\rvert \ge d_0(n)$ ($128$ for $n = 3$, $5^{\binom n2}$ for even $n \ge 4$,
$2\cdot5^{\binom n2}$ for odd $n \ge 5$). Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Cor. 22, p. 395 (n ≥ 3)"]
theorem corollary22_ge_three (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (h : MoreThanOneClass A) : d0 n ≤ A.det.natAbs := by
  refine corollary22_core hn hA hd hind h fun p2 hp2 hnodd h2d => ?_
  have h2 : (2 : 𝓞 ℚ) ∈ p2.asIdeal := (two_mem_iff_natGenerator p2).mpr hp2
  refine exists_odd_order_of_unimodular (csQ_nondegenerate hA hd) h2 stdLat
    (by convert hint_std' A p2; exact Subsingleton.elim _ _) (Nat.odd_iff.mpr hnodd) hn
    (by convert hci_std hA p2 using 4) 1 (loc_std_eq_locAct_one p2) ?_
  rw [locGram_one_int_det, hessian_det_csForm hA]
  have hodd : Valued.v ((A.det : ℤ) : p2.adicCompletion ℚ) = 1 :=
    valued_intCast_eq_one p2 _ (by rw [show ((primeOf p2 : ℕ) : ℤ) = 2 by rw [hp2]; norm_num]; exact h2d)
  rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, map_mul, hodd, mul_one]

/-- **Named statement: indefinite binary genera of small determinant have one class** (Conway–Sloane, §9.7, Cor. 22
for $n = 2$, "we find from Table 15.2", p. 396; Table 15.2 is in §3): every indefinite classically integral binary form
with $\lvert d\rvert \le 16$ has only one class in its genus. Proved in `Section9BinarySmall.lean`
(`binaryOneClassUpTo16`, by reduction and finite certificates); a numerical check found one class in every such genus for $\lvert d\rvert \le 20$.
The book's example for $\lvert d\rvert = 17$ is wrong. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Cor. 22, p. 395, n = 2 (from Table 15.2, §3, p. 362) (stated)"]
structure BinaryOneClassUpTo16 : Prop where
  one_class : ∀ A : Matrix (Fin 2) (Fin 2) ℤ, Aᵀ = A → A.det ≠ 0 → IsIndefinite (csQ A) →
    A.det.natAbs ≤ 16 → ¬ MoreThanOneClass A

/-- **Conway–Sloane, Corollary 22** (§9.7, p. 395): *suppose $f$ is an indefinite form of dimension $n$ and
determinant $d$, with more than one class in its genus. Then $\lvert d\rvert \ge d_0$*, $d_0 = 17, 128, 5^{\binom n2},
2\cdot5^{\binom n2}$ for $n = 2$, $3$, even $n \ge 4$, odd $n \ge 5$. Unconditional for $n \ge 3$
(`corollary22_ge_three`); for $n = 2$ it uses the named statement `BinaryOneClassUpTo16` (Table 15.2). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Cor. 22, p. 395"]
theorem corollary22 (hbin : BinaryOneClassUpTo16) : Corollary22Statement := by
  intro n A hn2 hA hd hind h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    by_contra hlt
    push Not at hlt
    exact hbin.one_class A hA hd hind (by simp [d0] at hlt; omega) h
  · exact corollary22_ge_three h3 hA hd hind h

end QuadFormsKB.ConwaySloane
