/-
# Moreno–Wagstaff 2005, Chapter 2: further proofs (D)

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Chapter 2.

**Proves**
* `lemma26` (Lemma 2.6, **proved**): the book's bijection
  $(x, y) \mapsto (y - 2au,\ x + 2bu)$ with $u - 1 < (y-a)/(2a) < u$, whose inverse is the same
  construction with $a, b$ swapped.
* `theorem25Tau` (Theorem 2.5, $\tau$ form, **proved**): from `theorem25` and multiplicativity of
  $n \mapsto \sum_{d \mid n}\chi_{-4}(d)$.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2ProofsB

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-! ### Lemma 2.6 -/

/-- The conditions defining a solution counted by `phiCount`. -/
private def Good (a b α β m : ℤ) (p : ℤ × ℤ) : Prop :=
  a * p.1 + b * p.2 = m ∧ |p.1| < b ∧ a < p.2 ∧ p.1 ≡ α [ZMOD 2] ∧
    p.2 ≡ β [ZMOD 2] ∧ ¬ p.2 ≡ a [ZMOD 2 * a]

/-- The book's map $(x, y) \mapsto (y - 2au, x + 2bu)$ with $u = \lfloor (y-a)/(2a) \rfloor + 1$. -/
private def fwd (a b : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((p.2 - a) % (2 * a) - a, p.1 + 2 * b * ((p.2 - a) / (2 * a) + 1))

private lemma decomp (a y : ℤ) (ha : 0 < a) (hy : a < y) (hn : ¬ y ≡ a [ZMOD 2 * a]) :
    ∃ q r : ℤ, 0 < r ∧ r < 2 * a ∧ y - a = r + 2 * a * q ∧ 0 ≤ q ∧
      (y - a) % (2 * a) = r ∧ (y - a) / (2 * a) = q := by
  have h1 : (y - a) % (2 * a) + 2 * a * ((y - a) / (2 * a)) = y - a := by
    rw [Int.emod_def]; ring
  have hr0 : 0 ≤ (y - a) % (2 * a) := Int.emod_nonneg _ (by omega)
  have hr1 : (y - a) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ (by omega)
  have hq : 0 ≤ (y - a) / (2 * a) := Int.ediv_nonneg (by omega) (by omega)
  have hne : (y - a) % (2 * a) ≠ 0 := by
    intro h0
    apply hn
    rw [Int.modEq_iff_dvd]
    exact ⟨-((y - a) / (2 * a)), by rw [mul_neg]; linarith⟩
  exact ⟨(y - a) / (2 * a), (y - a) % (2 * a), by omega, hr1, by linarith, hq, rfl, rfl⟩

private lemma fwd_good (a b α β m : ℤ) (ha : 0 < a) (hb : 0 < b) (p : ℤ × ℤ)
    (hp : Good a b α β m p) : Good b a β α m (fwd a b p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  simp only at h1 h2 h3 h4 h5 h6
  obtain ⟨q, r, hr0, hr1, hyq, hq, he, hd⟩ := decomp a y ha h3 h6
  unfold fwd Good
  simp only
  rw [he, hd]
  obtain ⟨k, hk⟩ : ∃ k, k = a * q := ⟨_, rfl⟩
  have hk2 : 2 * a * q = 2 * k := by rw [hk]; ring
  rw [hk2] at hyq
  have hx := abs_lt.1 h2
  refine ⟨by nlinarith, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · nlinarith
  · unfold Int.ModEq at *; omega
  · unfold Int.ModEq at *
    have : 2 * b * (q + 1) = 2 * (b * (q + 1)) := by ring
    omega
  · intro h
    obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.1 h
    have hbd : b - x = 2 * b * (c + (q + 1)) := by linarith
    rcases le_or_gt (c + (q + 1)) 0 with hle | hgt
    · nlinarith
    · nlinarith

private lemma fwd_fwd (a b α β m : ℤ) (ha : 0 < a) (hb : 0 < b) (p : ℤ × ℤ)
    (hp : Good a b α β m p) : fwd b a (fwd a b p) = p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  simp only at h1 h2 h3 h4 h5 h6
  obtain ⟨q, r, hr0, hr1, hyq, hq, he, hd⟩ := decomp a y ha h3 h6
  have hx := abs_lt.1 h2
  have key : (x + 2 * b * (q + 1) - b) / (2 * b) = q ∧ (x + 2 * b * (q + 1) - b) % (2 * b) = x + b :=
    Int.ediv_emod_unique (by omega) |>.2 ⟨by linarith, by omega, by omega⟩
  unfold fwd
  simp only
  rw [he, hd, key.1, key.2]
  ext
  · simp only; ring
  · simp only; linarith

/-- **Moreno–Wagstaff, Lemma 2.6** (p. 48), proved: the book's bijection
$(x, y) \mapsto (y - 2au,\ x + 2bu)$, $u - 1 < (y-a)/(2a) < u$, between the solution sets, with inverse
the same construction for $(b, a)$. -/
@[kb "morenowagstaff2005" "Lemma 2.6, p. 48"]
theorem lemma26 : Lemma26 := by
  intro a b m α β ha hb _ _
  unfold phiCount
  refine Nat.card_congr
    { toFun := fun p => ⟨fwd a b p.1, fwd_good a b α β m ha hb p.1 p.2⟩
      invFun := fun p => ⟨fwd b a p.1, fwd_good b a β α m hb ha p.1 p.2⟩
      left_inv := fun p => Subtype.ext (fwd_fwd a b α β m ha hb p.1 p.2)
      right_inv := fun p => Subtype.ext (fwd_fwd b a β α m hb ha p.1 p.2) }

/-! ### Theorem 2.5, the $\tau$ form -/

/-- $\chi_{-4}$ as an arithmetic function (zero at $0$). -/
private noncomputable def chiAF : ArithmeticFunction ℤ :=
  ⟨fun d => if d = 0 then 0 else (ZMod.χ₄ (d : ZMod 4) : ℤ), by simp⟩

private lemma chiAF_mult : chiAF.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn _ => ?_⟩
  · simp [chiAF]
  · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    simp only [chiAF, ArithmeticFunction.coe_mk, hm, hn, hmn, ite_false, Nat.cast_mul]
    exact map_mul _ _ _

/-- $\zeta * \chi_{-4}$, the divisor sum of $\chi_{-4}$. -/
private noncomputable def divChi : ArithmeticFunction ℤ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * chiAF

private lemma divChi_mult : divChi.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul chiAF_mult

private lemma divChi_apply (n : ℕ) :
    divChi n = ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) := by
  unfold divChi
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  refine Finset.sum_congr rfl fun d hd => ?_
  have : d ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.pos_of_mem_divisors hd)
  simp [chiAF, this]

/-- The value of $\sum_{d \mid p^e} \chi_{-4}(d)$. -/
private def hval (p e : ℕ) : ℤ :=
  if p = 2 ∨ (p % 4 = 3 ∧ Even e) then 1 else if p % 4 = 1 then (e : ℤ) + 1 else 0

private lemma r2_divChi (n : ℕ) (hn : 0 < n) : (repNum (sumSq 2) n : ℤ) = 4 * divChi n := by
  rw [(theorem25.1 n hn).2, divChi_apply n]
  congr 1
  have : ∀ d : ℕ, (ZMod.χ₄ (d : ZMod 4) : ℤ) =
      (if d % 4 = 1 then 1 else 0) - (if d % 4 = 3 then 1 else 0) := by
    intro d
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    split_ifs <;> omega
  simp only [this, Finset.sum_sub_distrib, Finset.sum_boole]

private lemma divChi_prime_pow (p e : ℕ) (hp : p.Prime) : divChi (p ^ e) = hval p e := by
  have h2 := r2_divChi (p ^ e) (pow_pos hp.pos e)
  rw [Nat.cast_pow, theorem25.2 p e hp] at h2
  unfold hval
  split_ifs at h2 ⊢ <;> push_cast at h2 <;> omega

/-- Product formula for the divisor sum of $\chi_{-4}$ over the prime factorization. -/
private lemma divChi_eq (n : ℕ) (hn : 0 < n) :
    divChi n = ∏ p ∈ n.primeFactors, hval p (n.factorization p) := by
  rw [divChi_mult.multiplicative_factorization _ hn.ne', Finsupp.prod, Nat.support_factorization]
  exact Finset.prod_congr rfl fun p hp => divChi_prime_pow p _ (Nat.prime_of_mem_primeFactors hp)

/-- **Moreno–Wagstaff, Theorem 2.5** (p. 27), $\tau$-product form, proved: from `theorem25` ($r_2(n) =
4\sum_{d \mid n}\chi_{-4}(d)$ and the prime-power table), multiplicativity of the divisor sum of $\chi_{-4}$
(`ArithmeticFunction`, $\zeta * \chi_{-4}$), evaluation over `n.factorization`, and
$\tau(\prod p^{a_p}) = \prod (a_p + 1)$ (`σ 0` is multiplicative). -/
@[kb "morenowagstaff2005" "Theorem 2.5 (tau form), p. 27"]
theorem theorem25Tau : Theorem25Tau := by
  intro n hn
  have h := r2_divChi n hn
  rw [divChi_eq n hn] at h
  have htau : ((∏ p ∈ n.primeFactors.filter (· % 4 = 1), p ^ n.factorization p).divisors.card : ℤ) =
      ∏ p ∈ n.primeFactors.filter (· % 4 = 1), ((n.factorization p : ℤ) + 1) := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_prod]
    · push_cast
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [ArithmeticFunction.sigma_zero_apply_prime_pow
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)]
      push_cast; rfl
    · intro p hp q hq hpq
      have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
      have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1
      exact ((Nat.coprime_primes hp' hq').2 hpq).pow _ _
  split_ifs with hc
  · have : (repNum (sumSq 2) n : ℤ) = 4 * ((∏ p ∈ n.primeFactors.filter (· % 4 = 1),
        p ^ n.factorization p).divisors.card : ℤ) := by
      rw [h, htau, Finset.prod_filter]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpp := Nat.prime_of_mem_primeFactors hp
      unfold hval
      by_cases h1 : p % 4 = 1
      · have : p ≠ 2 := by omega
        simp [h1, this]
      · have h2 : p = 2 ∨ p % 4 = 3 := by
          rcases hpp.eq_two_or_odd with h | h
          · exact Or.inl h
          · right; omega
        rcases h2 with h2 | h2
        · simp [h2]
        · have := hc p hp h2
          simp [h2, this]
    exact_mod_cast this
  · push Not at hc
    obtain ⟨q, hq, hq3, hqe⟩ := hc
    have : (repNum (sumSq 2) n : ℤ) = 0 := by
      rw [h]
      have : hval q (n.factorization q) = 0 := by
        unfold hval
        have : q ≠ 2 := by omega
        simp [this, hq3, hqe]
      rw [Finset.prod_eq_zero hq this]; simp
    exact_mod_cast this

end QuadFormsKB.MorenoWagstaff
