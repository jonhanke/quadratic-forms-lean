/-
# Classical special cases: local densities of $x_0^2 + x_1^2$ and $x_0^2 - 2x_1^2$

**Layer:** $\mathbb Q$ / $\mathcal O_\mathbb Q$. The local identities behind Dirichlet's formula for the two binary forms
`sumTwoSqZ` (disc $-4$) and `pell2Z` (disc $8$): for $m \ne 0$ and every prime $p$,
$\beta_p(m) = \beta_p(1)\cdot\rho_p(m)$ with $\rho_p$ = `locRatio₄` / `locRatio₈`, $\beta_p(1) > 0$, and
$\prod_{p \mid 2m}\rho_p(m) = \sum_{d \mid m}\chi(d)$ ($\chi = \chi_{-4}$, resp. $\chi_8$).
-/
import QuadFormsKB.Tamagawa.Classical.Basic
import QuadFormsKB.Binary.SiegelBinaryChecks
import QuadFormsKB.Binary.BinaryDensitiesRam
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.LocalDensity.NFLocal

open QuadFormsKB.Binary

namespace QuadFormsKB.Tamagawa.Classical

instance isQuadDisc_eight : IsQuadDisc 8 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  ne_one := by norm_num

theorem sumTwoSqZ_eq : sumTwoSqZ = BinQF.mk 1 0 1 := diag_two_eq_mk 1 1
theorem pell2Z_eq : pell2Z = BinQF.mk 1 0 (-2) := diag_two_eq_mk 1 (-2)

theorem sumTwoSqZ_disc : (BinQF.mk 1 0 1).disc = -4 := by simp [BinQF.disc]
theorem pell2Z_disc : (BinQF.mk 1 0 (-2)).disc = 8 := by simp [BinQF.disc]

theorem kronZ_neg_four_odd {p : ℕ} (hp : Odd p) :
    kronZ (-4) (p : ZMod (-4 : ℤ).natAbs) = ZMod.χ₄ (p : ZMod 4) := by
  rw [kronZ_natCast_of_zero (by norm_num) hp, show (-4 : ℤ) / 4 = -1 by norm_num,
    jacobiSym.at_neg_one hp]

theorem kronZ_eight_odd {p : ℕ} (hp : Odd p) :
    kronZ 8 (p : ZMod (8 : ℤ).natAbs) = ZMod.χ₈ (p : ZMod 8) := by
  rw [kronZ_natCast_of_zero (by norm_num) hp, show (8 : ℤ) / 4 = 2 by norm_num,
    jacobiSym.at_two hp]

open QuadFormsKB.LocalDensity in
/-- Local ratio for $x_0^2 + x_1^2$: at $p = 2$ it is $1$ if the odd part of $m$ is $\equiv 1 \pmod 4$ and $0$
otherwise; at odd $p$ it is $\sum_{j \le v_p(m)} \chi_{-4}(p)^j$. -/
noncomputable def locRatio₄ (p m : ℕ) : ℝ :=
  if p = 2 then (if (m / 2 ^ m.factorization 2) % 4 = 1 then 1 else 0)
  else ∑ j ∈ Finset.range (m.factorization p + 1), (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ j

open QuadFormsKB.LocalDensity in
/-- Local ratio for $x_0^2 - 2x_1^2$: at $p = 2$ it is $1$ if the odd part of $m$ is $\equiv \pm 1 \pmod 8$, else $0$;
at odd $p$ it is $\sum_{j \le v_p(m)} \chi_8(p)^j$. -/
noncomputable def locRatio₈ (p m : ℕ) : ℝ :=
  if p = 2 then (if (m / 2 ^ m.factorization 2) % 8 = 1 ∨ (m / 2 ^ m.factorization 2) % 8 = 7 then 1 else 0)
  else ∑ j ∈ Finset.range (m.factorization p + 1), (ZMod.χ₈ (p : ZMod 8) : ℝ) ^ j

/-- The odd part of a nonzero natural number is odd. -/
theorem odd_ordCompl {m : ℕ} (hm : m ≠ 0) : (m / 2 ^ m.factorization 2) % 2 = 1 := by
  have := Nat.not_dvd_ordCompl Nat.prime_two hm
  omega

theorem pFree_two_natCast {m : ℕ} :
    pFree 2 (m : ℤ) = ((m / 2 ^ m.factorization 2 : ℕ) : ℤ) := by
  unfold pFree
  rw [Int.natAbs_natCast]
  have := Nat.ordProj_dvd m 2
  rw [Int.natCast_div]; push_cast; rfl

/-! ### Odd primes -/

theorem localDensity_odd_aux {D : ℤ} [IsQuadDisc D] {f : BinQF} (hD : f.disc = D) (p : ℕ) [Fact p.Prime]
    (hpD : ¬ (p : ℤ) ∣ D) {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.localDensity f p (m : ℤ) =
      goodFactor (kronZ D (p : ZMod D.natAbs)) p (m.factorization p) := by
  rw [localDensity_good_binary f hD p hpD _ (by exact_mod_cast hm), Int.natAbs_natCast]

theorem goodFactor_ratio (χ : ℤ) (p v : ℕ) :
    goodFactor χ p v = goodFactor χ p 0 * ∑ j ∈ Finset.range (v + 1), (χ : ℝ) ^ j := by
  simp [goodFactor]

theorem goodFactor_zero_pos {χ : ℤ} (hχ : χ = 1 ∨ χ = -1) {p : ℕ} (hp : 2 ≤ p) :
    0 < goodFactor χ p 0 := by
  rw [goodFactor_zero]
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have : (χ : ℝ) / p ≤ 1 / 2 := by
    rcases hχ with rfl | rfl
    · simp; exact (inv_anti₀ (by norm_num) hp')
    · have : (0:ℝ) ≤ (p : ℝ)⁻¹ := by positivity
      simp [neg_div]; linarith
  linarith

theorem not_dvd_of_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {k : ℕ} (hk : k = 2 ^ 2 ∨ k = 2 ^ 3) :
    ¬ p ∣ k := by
  intro h
  have : p ∣ 2 := by
    rcases hk with rfl | rfl <;> exact hp.dvd_of_dvd_pow h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

theorem not_dvd_neg_four {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : ¬ (p : ℤ) ∣ -4 := by
  intro h
  have : p ∣ 2 ^ 2 := by
    have := Int.natCast_dvd.mp (by simpa using h : (p : ℤ) ∣ ((4 : ℕ) : ℤ))
    simpa using this
  exact not_dvd_of_odd_prime hp h2 (Or.inl rfl) (by simpa using this)

theorem not_dvd_eight {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : ¬ (p : ℤ) ∣ 8 := by
  intro h
  exact not_dvd_of_odd_prime hp h2 (Or.inr rfl) (by exact_mod_cast h)

theorem chi4_pm {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ZMod.χ₄ (p : ZMod 4) = 1 ∨ ZMod.χ₄ (p : ZMod 4) = -1 := by
  have hodd := hp.odd_of_ne_two h2
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  have : p % 2 = 1 := Nat.odd_iff.mp hodd
  have : p % 2 ≠ 0 := by omega
  simp only [this, ite_false]
  split_ifs <;> simp

theorem chi8_pm {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ZMod.χ₈ (p : ZMod 8) = 1 ∨ ZMod.χ₈ (p : ZMod 8) = -1 := by
  have hodd := hp.odd_of_ne_two h2
  rw [ZMod.χ₈_nat_eq_if_mod_eight]
  have : p % 2 = 1 := Nat.odd_iff.mp hodd
  have : p % 2 ≠ 0 := by omega
  simp only [this, ite_false]
  split_ifs <;> simp

/-! ### The prime 2 -/

theorem localDensity_sumTwoSq_two {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.localDensity sumTwoSqZ 2 (m : ℤ) =
      1 + (ZMod.χ₄ (((m / 2 ^ m.factorization 2 : ℕ)) : ZMod 4) : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sumTwoSqZ_eq]
  have hprim : Primitive (BinQF.mk 1 0 1) := by simp [Primitive]
  rw [localDensity_ram hprim sumTwoSqZ_disc 2 (by norm_num) (by exact_mod_cast hm)]
  have h1 : formChar (BinQF.mk 1 0 1) 2 = 1 := by
    simp [formChar, charCoeff, genusChar, BinQF.disc]
  have h2 : ramChar 2 (-4) (m : ℤ) = ZMod.χ₄ (((m / 2 ^ m.factorization 2 : ℕ)) : ZMod 4) := by
    unfold ramChar ramUnit
    rw [pFree_two_natCast, Int.natAbs_natCast]
    generalize (m / 2 ^ m.factorization 2 : ℕ) = n0
    split_ifs <;> first | (exfalso; omega) | simp [genusChar]
  rw [h1, h2]; simp

theorem chi8_neg (x : ZMod 8) : ZMod.χ₈ (-x) = ZMod.χ₈ x := by revert x; decide

theorem localDensity_pell2_two {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.localDensity pell2Z 2 (m : ℤ) =
      1 + (ZMod.χ₈ (((m / 2 ^ m.factorization 2 : ℕ)) : ZMod 8) : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pell2Z_eq]
  have hprim : Primitive (BinQF.mk 1 0 (-2)) := by simp [Primitive]
  rw [localDensity_ram hprim pell2Z_disc 2 (by norm_num) (by exact_mod_cast hm)]
  have h1 : formChar (BinQF.mk 1 0 (-2)) 2 = 1 := by
    simp [formChar, charCoeff, genusChar, BinQF.disc]
  have h2 : ramChar 2 8 (m : ℤ) = ZMod.χ₈ (((m / 2 ^ m.factorization 2 : ℕ)) : ZMod 8) := by
    unfold ramChar ramUnit
    rw [pFree_two_natCast, Int.natAbs_natCast]
    generalize (m / 2 ^ m.factorization 2 : ℕ) = n0
    split_ifs <;> first | (exfalso; omega) | (simp [genusChar]; done) |
      (simp [genusChar]; generalize (n0 : ZMod 8) = x; revert x; decide)
  rw [h1, h2]; simp

/-! ### The product over primes dividing $2m$ -/

theorem kronR_ordCompl (D : ℤ) [IsQuadDisc D] {m : ℕ} (hm : m ≠ 0) :
    kronR D (m / 2 ^ m.factorization 2) =
      ∏ p ∈ m.primeFactors.erase 2, kronR D p ^ m.factorization p := by
  let ψ : ℕ →* ℝ := ⟨⟨kronR D, kronR_one⟩, kronR_mul⟩
  have hψ : ∀ n, ψ n = kronR D n := fun _ => rfl
  have hm0 : m / 2 ^ m.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hm).ne'
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm0]
  rw [← hψ, map_prod]
  have hsupp : (m / 2 ^ m.factorization 2).primeFactors = m.primeFactors.erase 2 := by
    rw [← Nat.support_factorization, Nat.factorization_ordCompl, Finsupp.support_erase,
      Nat.support_factorization]
  rw [hsupp]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [map_pow, hψ, Nat.factorization_ordCompl, Finsupp.erase_ne (Finset.mem_erase.mp hp).1]

theorem prod_core (D : ℤ) [IsQuadDisc D] (loc : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0)
    (hloc : ∀ p, p ≠ 2 → loc p = ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j)
    (h2 : kronR D 2 = 0) (hpm : ∀ p, p.Prime → p ≠ 2 → kronR D p = 1 ∨ kronR D p = -1)
    (hl2 : loc 2 = 1 ∨ (loc 2 = 0 ∧ kronR D (m / 2 ^ m.factorization 2) = -1)) :
    ∏ p ∈ (2 * m).primeFactors, loc p = ∑ d ∈ m.divisors, kronR D d := by
  have hS2 : ∑ j ∈ Finset.range (m.factorization 2 + 1), kronR D 2 ^ j = 1 := by
    rw [Finset.sum_range_succ']; simp [h2]
  have hC : (2 * m).primeFactors.erase 2 = m.primeFactors.erase 2 := by
    rw [Nat.primeFactors_mul (by norm_num) hm, Nat.Prime.primeFactors Nat.prime_two]
    ext p; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]; tauto
  have h2mem : 2 ∈ (2 * m).primeFactors := by
    simp [Nat.mem_primeFactors, hm, Nat.prime_two]
  have e1 : ∏ p ∈ m.primeFactors, ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j =
      ∏ p ∈ m.primeFactors.erase 2, ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j :=
    (Finset.prod_erase (m.primeFactors) (f := fun p => ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j)
      hS2).symm
  have e2 : ∏ p ∈ (2 * m).primeFactors, loc p = loc 2 * ∏ p ∈ (2 * m).primeFactors.erase 2, loc p :=
    (Finset.mul_prod_erase _ loc h2mem).symm
  rw [sum_divisors_kronR hm, e1, e2, hC]
  have hcongr : ∏ p ∈ m.primeFactors.erase 2, loc p =
      ∏ p ∈ m.primeFactors.erase 2, ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j :=
    Finset.prod_congr rfl fun p hp => hloc p (Finset.mem_erase.mp hp).1
  rw [hcongr]
  rcases hl2 with h | ⟨h, hg⟩
  · rw [h, one_mul]
  · rw [h, zero_mul]
    symm
    by_contra hne
    rw [kronR_ordCompl D hm] at hg
    have hall : ∀ p ∈ m.primeFactors.erase 2, kronR D p ^ m.factorization p = 1 := by
      intro p hp
      have hne' : ∑ j ∈ Finset.range (m.factorization p + 1), kronR D p ^ j ≠ 0 :=
        fun h0 => hne ((Finset.prod_eq_zero hp h0))
      have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
      rcases hpm p hpp (Finset.mem_erase.mp hp).1 with h1 | h1
      · rw [h1]; simp
      · rw [h1] at hne' ⊢
        rcases Nat.even_or_odd (m.factorization p) with he | ho
        · exact he.neg_one_pow
        · exfalso; apply hne'
          obtain ⟨k, hk⟩ := ho
          rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
          clear hne' hk
          induction k with
          | zero => simp [Finset.sum_range_succ]
          | succ n ih =>
            rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 1 + 1 by ring, Finset.sum_range_succ,
              Finset.sum_range_succ, ih]
            simp [pow_succ, pow_mul]
    rw [Finset.prod_eq_one hall] at hg
    norm_num at hg

/-! ### The main identities -/

theorem kronR_neg_four (d : ℕ) : kronR (-4) d = (ZMod.χ₄ (d : ZMod 4) : ℝ) := by
  unfold kronR
  rcases Nat.even_or_odd d with he | ho
  · have h0 : kronZ (-4) (d : ZMod (-4 : ℤ).natAbs) = 0 := by
      have h4 : (-4 : ℤ) % 4 ≠ 1 := by norm_num
      rw [kronZ, if_neg h4]
      have : ¬ Odd ((d : ZMod (-4 : ℤ).natAbs).val) := by
        rw [ZMod.val_natCast, Nat.odd_iff]
        have := he.two_dvd
        change ¬ d % 4 % 2 = 1
        omega
      rw [if_neg this]
    have h1 : ZMod.χ₄ (d : ZMod 4) = 0 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      have : d % 2 = 0 := Nat.even_iff.mp he
      simp [this]
    rw [h0, h1]
  · rw [kronZ_neg_four_odd ho]

theorem kronR_eight (d : ℕ) : kronR 8 d = (ZMod.χ₈ (d : ZMod 8) : ℝ) := by
  unfold kronR
  rcases Nat.even_or_odd d with he | ho
  · have h0 : kronZ 8 (d : ZMod (8 : ℤ).natAbs) = 0 := by
      have h4 : (8 : ℤ) % 4 ≠ 1 := by norm_num
      rw [kronZ, if_neg h4]
      have : ¬ Odd ((d : ZMod (8 : ℤ).natAbs).val) := by
        rw [ZMod.val_natCast, Nat.odd_iff]
        have := he.two_dvd
        change ¬ d % 8 % 2 = 1
        omega
      rw [if_neg this]
    have h1 : ZMod.χ₈ (d : ZMod 8) = 0 := by
      rw [ZMod.χ₈_nat_eq_if_mod_eight]
      have : d % 2 = 0 := Nat.even_iff.mp he
      simp [this]
    rw [h0, h1]
  · rw [kronZ_eight_odd ho]

theorem localDensity_sumTwoSq_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.localDensity sumTwoSqZ p (m : ℤ) =
      goodFactor (ZMod.χ₄ (p : ZMod 4)) p (m.factorization p) := by
  have hp : p.Prime := Fact.out
  rw [sumTwoSqZ_eq, localDensity_odd_aux (D := -4) sumTwoSqZ_disc p (not_dvd_neg_four hp hp2) hm,
    kronZ_neg_four_odd (hp.odd_of_ne_two hp2)]

theorem localDensity_pell2_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.localDensity pell2Z p (m : ℤ) =
      goodFactor (ZMod.χ₈ (p : ZMod 8)) p (m.factorization p) := by
  have hp : p.Prime := Fact.out
  rw [pell2Z_eq, localDensity_odd_aux (D := 8) pell2Z_disc p (not_dvd_eight hp hp2) hm,
    kronZ_eight_odd (hp.odd_of_ne_two hp2)]

theorem localDensity_sumTwoSq_one_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    LocalDensity.localDensity sumTwoSqZ p 1 = goodFactor (ZMod.χ₄ (p : ZMod 4)) p 0 := by
  have := localDensity_sumTwoSq_odd (p := p) hp2 (m := 1) one_ne_zero
  simpa using this

theorem localDensity_pell2_one_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    LocalDensity.localDensity pell2Z p 1 = goodFactor (ZMod.χ₈ (p : ZMod 8)) p 0 := by
  have := localDensity_pell2_odd (p := p) hp2 (m := 1) one_ne_zero
  simpa using this

theorem localDensity_sumTwoSq_one_two : LocalDensity.localDensity sumTwoSqZ 2 1 = 2 := by
  have := localDensity_sumTwoSq_two (m := 1) one_ne_zero
  simp at this; rw [this]; norm_num

theorem localDensity_pell2_one_two : LocalDensity.localDensity pell2Z 2 1 = 2 := by
  have := localDensity_pell2_two (m := 1) one_ne_zero
  simp at this; rw [this]; norm_num

/-- $\beta_p(1) > 0$ for $x_0^2 + x_1^2$ at every prime. -/
theorem localDensity_sumTwoSq_one_pos (p : ℕ) [Fact p.Prime] :
    0 < LocalDensity.localDensity sumTwoSqZ p 1 := by
  by_cases hp2 : p = 2
  · subst hp2; rw [localDensity_sumTwoSq_one_two]; norm_num
  · rw [localDensity_sumTwoSq_one_odd hp2]
    exact goodFactor_zero_pos (chi4_pm Fact.out hp2) (Fact.out : p.Prime).two_le

/-- $\beta_p(1) > 0$ for $x_0^2 - 2x_1^2$ at every prime. -/
theorem localDensity_pell2_one_pos (p : ℕ) [Fact p.Prime] :
    0 < LocalDensity.localDensity pell2Z p 1 := by
  by_cases hp2 : p = 2
  · subst hp2; rw [localDensity_pell2_one_two]; norm_num
  · rw [localDensity_pell2_one_odd hp2]
    exact goodFactor_zero_pos (chi8_pm Fact.out hp2) (Fact.out : p.Prime).two_le

/-- $\beta_p(m) = \beta_p(1)\,\rho_p(m)$ for $x_0^2 + x_1^2$, $m \ne 0$. -/
theorem localDensity_sumTwoSq_eq (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.localDensity sumTwoSqZ p m = LocalDensity.localDensity sumTwoSqZ p 1 * locRatio₄ p m := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [localDensity_sumTwoSq_two hm, localDensity_sumTwoSq_one_two, locRatio₄,
      if_pos rfl, ZMod.χ₄_nat_eq_if_mod_four]
    have := odd_ordCompl hm
    have h2 : ¬ (m / 2 ^ m.factorization 2) % 2 = 0 := by omega
    simp only [h2, ite_false]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [localDensity_sumTwoSq_odd hp2 hm, localDensity_sumTwoSq_one_odd hp2, locRatio₄, if_neg hp2,
      goodFactor_ratio]

/-- $\beta_p(m) = \beta_p(1)\,\rho_p(m)$ for $x_0^2 - 2x_1^2$, $m \ne 0$. -/
theorem localDensity_pell2_eq (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.localDensity pell2Z p m = LocalDensity.localDensity pell2Z p 1 * locRatio₈ p m := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [localDensity_pell2_two hm, localDensity_pell2_one_two, locRatio₈,
      if_pos rfl, ZMod.χ₈_nat_eq_if_mod_eight]
    have := odd_ordCompl hm
    have h2 : ¬ (m / 2 ^ m.factorization 2) % 2 = 0 := by omega
    simp only [h2, ite_false]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [localDensity_pell2_odd hp2 hm, localDensity_pell2_one_odd hp2, locRatio₈, if_neg hp2,
      goodFactor_ratio]

/-- Outside $2m$ the ratio is $1$. -/
theorem locRatio₄_eq_one {p m : ℕ} (hp : p.Prime) (h : ¬ p ∣ 2 * m) : locRatio₄ p m = 1 := by
  have hp2 : p ≠ 2 := fun e => h (e ▸ dvd_mul_right _ _)
  have : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (fun d => h (dvd_mul_of_dvd_right d _))
  simp [locRatio₄, hp2, this]

/-- Outside $2m$ the ratio is $1$. -/
theorem locRatio₈_eq_one {p m : ℕ} (hp : p.Prime) (h : ¬ p ∣ 2 * m) : locRatio₈ p m = 1 := by
  have hp2 : p ≠ 2 := fun e => h (e ▸ dvd_mul_right _ _)
  have : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (fun d => h (dvd_mul_of_dvd_right d _))
  simp [locRatio₈, hp2, this]

/-- $\prod_{p \mid 2m}\rho_p(m) = \sum_{d \mid m}\chi_{-4}(d)$. -/
theorem prod_locRatio₄ {m : ℕ} (hm : m ≠ 0) :
    ∏ p ∈ (2 * m).primeFactors, locRatio₄ p m = ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) := by
  have h := prod_core (-4) (fun p => locRatio₄ p m) hm
    (fun p hp => by
      simp only [locRatio₄, if_neg hp, kronR_neg_four])
    (by rw [kronR_neg_four]; simp [ZMod.χ₄_nat_eq_if_mod_four])
    (fun p hp hp2 => by
      rw [kronR_neg_four]; rcases chi4_pm hp hp2 with h | h <;> simp [h])
    (by
      have hodd := odd_ordCompl hm
      simp only [locRatio₄, if_true, kronR_neg_four, ZMod.χ₄_nat_eq_if_mod_four]
      have h2 : ¬ (m / 2 ^ m.factorization 2) % 2 = 0 := by omega
      simp only [h2, ite_false]
      split_ifs <;> first | (exfalso; omega) | simp)
  simpa [kronR_neg_four] using h

/-- $\prod_{p \mid 2m}\rho_p(m) = \sum_{d \mid m}\chi_8(d)$. -/
theorem prod_locRatio₈ {m : ℕ} (hm : m ≠ 0) :
    ∏ p ∈ (2 * m).primeFactors, locRatio₈ p m = ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) := by
  have h := prod_core 8 (fun p => locRatio₈ p m) hm
    (fun p hp => by
      simp only [locRatio₈, if_neg hp, kronR_eight])
    (by rw [kronR_eight]; simp [ZMod.χ₈_nat_eq_if_mod_eight])
    (fun p hp hp2 => by
      rw [kronR_eight]; rcases chi8_pm hp hp2 with h | h <;> simp [h])
    (by
      have hodd := odd_ordCompl hm
      simp only [locRatio₈, if_true, kronR_eight, ZMod.χ₈_nat_eq_if_mod_eight]
      have h2 : ¬ (m / 2 ^ m.factorization 2) % 2 = 0 := by omega
      simp only [h2, ite_false]
      split_ifs <;> first | (exfalso; omega) | simp)
  simpa [kronR_eight] using h

/-! ### Over $\mathcal O_\mathbb Q$ -/

section OQ

open IsDedekindDomain NumberField QuadFormsKB.Tamagawa.RatBridge

theorem natGenerator_inj :
    Function.Injective fun v : HeightOneSpectrum (𝓞 ℚ) => Rat.HeightOneSpectrum.natGenerator v :=
  fun _ _ h => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem finite_natGenerator_dvd' {N : ℕ} (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | Rat.HeightOneSpectrum.natGenerator v ∣ N}.Finite :=
  ((Nat.divisors N).finite_toSet.preimage natGenerator_inj.injOn).subset fun v hv => by
    simp only [Finset.mem_coe, Set.mem_preimage, Nat.mem_divisors]
    exact ⟨hv, hN⟩

theorem nfLocalDensity_up (v : HeightOneSpectrum (𝓞 ℚ)) (Q : QuadForm ℤ 2) (m : ℤ) :
    LocalDensity.NF.localDensity v (up Q) (m : 𝓞 ℚ) =
      LocalDensity.localDensity Q (Rat.HeightOneSpectrum.natGenerator v) m :=
  LocalDensity.NF.localDensity_rat v Q m

/-- $\beta_\mathfrak p(m) = \beta_\mathfrak p(1)\rho_p(m)$ over $\mathcal O_\mathbb Q$ for $x_0^2 + x_1^2$. -/
theorem nfLocalDensity_sumTwoSq_eq (v : HeightOneSpectrum (𝓞 ℚ)) {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.NF.localDensity v (up sumTwoSqZ) ((m : ℤ) : 𝓞 ℚ) =
      LocalDensity.NF.localDensity v (up sumTwoSqZ) 1 *
        locRatio₄ (Rat.HeightOneSpectrum.natGenerator v) m := by
  have : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have h1 := nfLocalDensity_up v sumTwoSqZ 1
  rw [Int.cast_one] at h1
  rw [nfLocalDensity_up, h1]
  exact localDensity_sumTwoSq_eq _ hm

/-- $\beta_\mathfrak p(m) = \beta_\mathfrak p(1)\rho_p(m)$ over $\mathcal O_\mathbb Q$ for $x_0^2 - 2x_1^2$. -/
theorem nfLocalDensity_pell2_eq (v : HeightOneSpectrum (𝓞 ℚ)) {m : ℕ} (hm : m ≠ 0) :
    LocalDensity.NF.localDensity v (up pell2Z) ((m : ℤ) : 𝓞 ℚ) =
      LocalDensity.NF.localDensity v (up pell2Z) 1 *
        locRatio₈ (Rat.HeightOneSpectrum.natGenerator v) m := by
  have : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have h1 := nfLocalDensity_up v pell2Z 1
  rw [Int.cast_one] at h1
  rw [nfLocalDensity_up, h1]
  exact localDensity_pell2_eq _ hm

/-- Positivity of $\beta_\mathfrak p(1)$ over $\mathcal O_\mathbb Q$ for $x_0^2 + x_1^2$. -/
theorem nfLocalDensity_sumTwoSq_one_pos (v : HeightOneSpectrum (𝓞 ℚ)) :
    0 < LocalDensity.NF.localDensity v (up sumTwoSqZ) 1 := by
  have : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have h1 := nfLocalDensity_up v sumTwoSqZ 1
  rw [Int.cast_one] at h1
  rw [h1]; exact localDensity_sumTwoSq_one_pos _

/-- Positivity of $\beta_\mathfrak p(1)$ over $\mathcal O_\mathbb Q$ for $x_0^2 - 2x_1^2$. -/
theorem nfLocalDensity_pell2_one_pos (v : HeightOneSpectrum (𝓞 ℚ)) :
    0 < LocalDensity.NF.localDensity v (up pell2Z) 1 := by
  have : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have h1 := nfLocalDensity_up v pell2Z 1
  rw [Int.cast_one] at h1
  rw [h1]; exact localDensity_pell2_one_pos _

/-- Generic: a family equal to $1$ outside the primes dividing $2m$ has finite multiplicative support and its
`tprod` is the finite product over $(2m)$'s prime factors. -/
theorem tprod_natGenerator_aux {m : ℕ} (hm : m ≠ 0) (loc : ℕ → ℝ)
    (h1 : ∀ p, p.Prime → ¬ p ∣ 2 * m → loc p = 1) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => loc (Rat.HeightOneSpectrum.natGenerator v)).Finite ∧
    ∏' v : HeightOneSpectrum (𝓞 ℚ), loc (Rat.HeightOneSpectrum.natGenerator v) =
      ∏ p ∈ (2 * m).primeFactors, loc p := by
  have hN : 2 * m ≠ 0 := by omega
  have hfin := finite_natGenerator_dvd' hN
  have hsub : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => loc (Rat.HeightOneSpectrum.natGenerator v))
      ⊆ {v | Rat.HeightOneSpectrum.natGenerator v ∣ 2 * m} := by
    intro v hv
    by_contra hd
    exact hv (h1 _ (Rat.HeightOneSpectrum.prime_natGenerator v) hd)
  refine ⟨hfin.subset hsub, ?_⟩
  rw [tprod_eq_prod (s := hfin.toFinset) (fun v hv =>
    h1 _ (Rat.HeightOneSpectrum.prime_natGenerator v) (by simpa using hv))]
  refine Finset.prod_bij (fun v _ => Rat.HeightOneSpectrum.natGenerator v) ?_ ?_ ?_ ?_
  · intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    exact Nat.mem_primeFactors.mpr ⟨Rat.HeightOneSpectrum.prime_natGenerator v, hv, hN⟩
  · intro a _ b _ h
    exact natGenerator_inj h
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hpp⟩, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      have : Rat.HeightOneSpectrum.natGenerator
          ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hpp⟩) = p :=
        congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hpp⟩)
      show Rat.HeightOneSpectrum.natGenerator _ ∣ _
      rw [this]; exact Nat.dvd_of_mem_primeFactors hp
    · exact congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hpp⟩)
  · intro a _; rfl

/-- Finite multiplicative support of $v \mapsto \rho_p(m)$, $p = $ `natGenerator v` ($x_0^2 + x_1^2$). -/
theorem mulSupport_locRatio₄_finite {m : ℕ} (hm : m ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      locRatio₄ (Rat.HeightOneSpectrum.natGenerator v) m).Finite :=
  (tprod_natGenerator_aux hm (fun p => locRatio₄ p m) fun _ hp h => locRatio₄_eq_one hp h).1

/-- Finite multiplicative support of $v \mapsto \rho_p(m)$ ($x_0^2 - 2x_1^2$). -/
theorem mulSupport_locRatio₈_finite {m : ℕ} (hm : m ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      locRatio₈ (Rat.HeightOneSpectrum.natGenerator v) m).Finite :=
  (tprod_natGenerator_aux hm (fun p => locRatio₈ p m) fun _ hp h => locRatio₈_eq_one hp h).1

/-- $\prod'_{\mathfrak p}\rho_p(m) = \sum_{d \mid m}\chi_{-4}(d)$. -/
theorem tprod_locRatio₄ {m : ℕ} (hm : m ≠ 0) :
    ∏' v : HeightOneSpectrum (𝓞 ℚ), locRatio₄ (Rat.HeightOneSpectrum.natGenerator v) m =
      ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) := by
  rw [(tprod_natGenerator_aux hm (fun p => locRatio₄ p m) fun _ hp h => locRatio₄_eq_one hp h).2]
  exact prod_locRatio₄ hm

/-- $\prod'_{\mathfrak p}\rho_p(m) = \sum_{d \mid m}\chi_8(d)$. -/
theorem tprod_locRatio₈ {m : ℕ} (hm : m ≠ 0) :
    ∏' v : HeightOneSpectrum (𝓞 ℚ), locRatio₈ (Rat.HeightOneSpectrum.natGenerator v) m =
      ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) := by
  rw [(tprod_natGenerator_aux hm (fun p => locRatio₈ p m) fun _ hp h => locRatio₈_eq_one hp h).2]
  exact prod_locRatio₈ hm

end OQ

end QuadFormsKB.Tamagawa.Classical
