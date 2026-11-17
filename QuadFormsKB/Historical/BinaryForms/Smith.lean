/-
# Smith's and Dickson's representation counts for $x^2 + 2y^2$, $x^2 + 3y^2$, $x^2 + 7y^2$

**Library** `QuadFormsKB.Historical.BinaryForms` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Smith, *Collected Mathematical Papers* I): for odd $M \ge 1$,
  $\#\{(x, y) \in \mathbb Z^2 : x^2 + 2y^2 = M\} = 2(d_{1,3}(M) - d_{5,7}(M))$, $d_{i,j}(M)$ the number of divisors of
  $M$ congruent to $i$ or $j$ modulo $8$ (`smith_x2_add_2y2_odd`). The row's second sentence (primes) is
  `Primes.prime_x2_add_2y2_existsUnique`.
* (same): for odd $M$,
  $\#\{x^2 + 3y^2 = M\} = 2(\#\{d \mid M : d \equiv 1 \ (3)\} - \#\{d \mid M : d \equiv 2\ (3)\})$
  (`smith_x2_add_3y2_odd`) and $\#\{x^2 + 7y^2 = M\} = 2(\#\{d \mid M : d \equiv 1, 2, 4\ (7)\} -
  \#\{d \mid M : d \equiv 3, 5, 6\ (7)\})$ (`smith_x2_add_7y2_odd`).
* (Dickson, *History* III): for every $n \ge 1$,
  $\#\{x^2 + 3y^2 = n\} = 2\sum_{d \mid n}\bigl(\frac d3\bigr) + 4\sum_{d \mid n/4}\bigl(\frac d3\bigr)$, the second sum
  empty unless $4 \mid n$ (`card_x2_add_3y2`).

All **proved**, unconditional: from Dirichlet's formula for the forms of class number one $x^2 + 2y^2$,
$x^2 + xy + y^2$, $x^2 + xy + 2y^2$ (`Dirichlet.lean`), by the substitutions $(x, y) \mapsto (x - y, 2y)$
(odd $M$: $x^2 + 3y^2$ and $x^2 + 7y^2$ are $a^2 + ab + b^2$, $a^2 + ab + 2b^2$ with $b$ even) and
$(a, b) \mapsto (2a + b, b)$ ($x^2 + 3y^2 = 4N$ iff $a^2 + ab + b^2 = N$), and the rotation
$(a, b) \mapsto (-b, a + b)$ of $a^2 + ab + b^2$, which permutes the three parity classes of $(a, b)$ cyclically.

Counts are of ordered pairs $(x, y) \in \mathbb Z^2$, signs included.
-/
import QuadFormsKB.Historical.BinaryForms.Dirichlet

namespace QuadFormsKB.Historical.BinaryForms

open Finset

/-! ### Helper lemmas -/

private theorem sum_chiNeg8 (s : Finset ℕ) :
    ∑ d ∈ s, chiNeg8 d = ((s.filter fun d => d % 8 = 1 ∨ d % 8 = 3).card : ℤ) -
      (s.filter fun d => d % 8 = 5 ∨ d % 8 = 7).card := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold chiNeg8
  split_ifs <;> omega

private theorem sum_chi3 (s : Finset ℕ) :
    ∑ d ∈ s, chi3 d = ((s.filter fun d => d % 3 = 1).card : ℤ) - (s.filter fun d => d % 3 = 2).card := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold chi3
  split_ifs <;> omega

private theorem sum_chi7 (s : Finset ℕ) :
    ∑ d ∈ s, chi7 d = ((s.filter fun d => d % 7 = 1 ∨ d % 7 = 2 ∨ d % 7 = 4).card : ℤ) -
      (s.filter fun d => d % 7 = 3 ∨ d % 7 = 5 ∨ d % 7 = 6).card := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold chi7
  split_ifs <;> omega

/-- The box $[-K, K]^2$. -/
private def box (K : ℤ) : Finset (ℤ × ℤ) := Finset.Icc (-K) K ×ˢ Finset.Icc (-K) K

private theorem mem_box {K : ℤ} {p : ℤ × ℤ} : p ∈ box K ↔ -K ≤ p.1 ∧ p.1 ≤ K ∧ -K ≤ p.2 ∧ p.2 ≤ K := by
  simp [box, and_assoc]

private theorem natCard_eq_card_filter (K : ℤ) (P : ℤ × ℤ → Prop) [DecidablePred P]
    (h : ∀ p, P p → p ∈ box K) : Nat.card {p : ℤ × ℤ // P p} = ((box K).filter P).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p =>
    ⟨fun hp => Finset.mem_filter.2 ⟨h p hp, hp⟩, fun hp => (Finset.mem_filter.1 hp).2⟩)

private theorem Q_bound {a b m : ℤ} (hm : 0 ≤ m) (h : a ^ 2 + a * b + b ^ 2 = m) :
    -(2 * m) ≤ a ∧ a ≤ 2 * m ∧ -(2 * m) ≤ b ∧ b ≤ 2 * m := by
  have ha : 3 * a ^ 2 ≤ 4 * m := by nlinarith [sq_nonneg (a + 2 * b)]
  have hb : 3 * b ^ 2 ≤ 4 * m := by nlinarith [sq_nonneg (b + 2 * a)]
  have h1 := Int.le_self_sq a
  have h2 := Int.le_self_sq (-a)
  have h3 := Int.le_self_sq b
  have h4 := Int.le_self_sq (-b)
  rw [neg_sq] at h2 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The solutions of $a^2 + ab + b^2 = M$, as a finset. -/
private def Qs (M : ℕ) : Finset (ℤ × ℤ) :=
  (box (2 * (M : ℤ))).filter fun p => p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = M

private theorem mem_Qs {M : ℕ} {p : ℤ × ℤ} : p ∈ Qs M ↔ p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = M := by
  refine ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨mem_box.2 ?_, h⟩⟩
  exact Q_bound (by positivity) h

private theorem Qs_card (M : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = M} = (Qs M).card := by
  rw [Qs]
  exact natCard_eq_card_filter _ _ fun p hp => mem_box.2 (Q_bound (by positivity) hp)

private theorem Qs_filter_card (M : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = M ∧ p.2 % 2 = 0} =
      ((Qs M).filter fun p => p.2 % 2 = 0).card := by
  rw [Qs, Finset.filter_filter]
  exact natCard_eq_card_filter _ _ fun p hp => mem_box.2 (Q_bound (by positivity) hp.1)

/-- The rotation $(a, b) \mapsto (-b, a + b)$ preserves $a^2 + ab + b^2$. -/
private theorem rot_mem {M : ℕ} {p : ℤ × ℤ} (h : p ∈ Qs M) : ((-p.2, p.1 + p.2) : ℤ × ℤ) ∈ Qs M := by
  rw [mem_Qs] at h ⊢
  rw [← h]; ring

private theorem rot'_mem {M : ℕ} {p : ℤ × ℤ} (h : p ∈ Qs M) : ((p.1 + p.2, -p.1) : ℤ × ℤ) ∈ Qs M := by
  rw [mem_Qs] at h ⊢
  rw [← h]; ring

private theorem Qs_not_even {M : ℕ} (hM : Odd M) {p : ℤ × ℤ} (h : p ∈ Qs M) :
    ¬ (p.1 % 2 = 0 ∧ p.2 % 2 = 0) := by
  rintro ⟨h1, h2⟩
  rw [mem_Qs] at h
  obtain ⟨k, hk⟩ : ∃ k, p.1 = 2 * k := ⟨p.1 / 2, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, p.2 = 2 * l := ⟨p.2 / 2, by omega⟩
  have : (M : ℤ) = 4 * (k ^ 2 + k * l + l ^ 2) := by rw [← h, hk, hl]; ring
  obtain ⟨j, hj⟩ := hM
  generalize k ^ 2 + k * l + l ^ 2 = t at this
  omega

private theorem Qs_three (M : ℕ) (hM : Odd M) :
    (Qs M).card = 3 * ((Qs M).filter fun p => p.2 % 2 = 0).card := by
  have hne := fun p (hp : p ∈ Qs M) => Qs_not_even hM hp
  set c10 := (Qs M).filter fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 0 with hc10
  set c01 := (Qs M).filter fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 1 with hc01
  set c11 := (Qs M).filter fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1 with hc11
  have hsplit : (Qs M).card = c10.card + c01.card + c11.card := by
    rw [hc10, hc01, hc11, Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := hne p hp
    split_ifs <;> omega
  have hf : ((Qs M).filter fun p => p.2 % 2 = 0) = c10 := by
    ext p
    simp only [Finset.mem_filter, hc10]
    constructor
    · rintro ⟨hp, h2⟩
      refine ⟨hp, ?_, h2⟩
      have := hne p hp
      omega
    · rintro ⟨hp, -, h2⟩; exact ⟨hp, h2⟩
  have h01 : c10.card = c01.card := by
    refine Finset.card_nbij' (fun p => ((-p.2, p.1 + p.2) : ℤ × ℤ)) (fun p => ((p.1 + p.2, -p.1) : ℤ × ℤ))
      ?_ ?_ ?_ ?_
    · intro p hp
      simp only [hc10, hc01, Finset.coe_filter, Set.mem_setOf_eq] at hp ⊢
      exact ⟨rot_mem hp.1, by omega, by omega⟩
    · intro p hp
      simp only [hc10, hc01, Finset.coe_filter, Set.mem_setOf_eq] at hp ⊢
      exact ⟨rot'_mem hp.1, by omega, by omega⟩
    · intro p _; ext <;> simp
    · intro p _; ext <;> simp
  have h11 : c01.card = c11.card := by
    refine Finset.card_nbij' (fun p => ((-p.2, p.1 + p.2) : ℤ × ℤ)) (fun p => ((p.1 + p.2, -p.1) : ℤ × ℤ))
      ?_ ?_ ?_ ?_
    · intro p hp
      simp only [hc11, hc01, Finset.coe_filter, Set.mem_setOf_eq] at hp ⊢
      exact ⟨rot_mem hp.1, by omega, by omega⟩
    · intro p hp
      simp only [hc11, hc01, Finset.coe_filter, Set.mem_setOf_eq] at hp ⊢
      exact ⟨rot'_mem hp.1, by omega, by omega⟩
    · intro p _; ext <;> simp
    · intro p _; ext <;> simp
  rw [hsplit, hf, h01, ← h11]; ring

/-- $(x, y) \mapsto (x - y, 2y)$: $x^2 + 3y^2 = M$ iff $a^2 + ab + b^2 = M$ with $b$ even. -/
private def equiv3 (M : ℤ) : {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = M} ≃
    {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = M ∧ p.2 % 2 = 0} where
  toFun p := ⟨(p.1.1 - p.1.2, 2 * p.1.2), by
    refine ⟨?_, by simp⟩
    linear_combination p.2⟩
  invFun p := ⟨(p.1.1 + p.1.2 / 2, p.1.2 / 2), by
    obtain ⟨c, hc⟩ : ∃ c, p.1.2 = 2 * c := ⟨p.1.2 / 2, by have := p.2.2; omega⟩
    have h := p.2.1
    rw [hc] at h ⊢
    rw [show 2 * c / 2 = c by omega]; linear_combination h⟩
  left_inv p := by
    apply Subtype.ext; ext <;> simp
  right_inv p := by
    have := p.2.2
    apply Subtype.ext; ext <;> simp <;> omega

private theorem card_S3_eq (M : ℤ) : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = M} =
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = M ∧ p.2 % 2 = 0} :=
  Nat.card_congr (equiv3 M)

private theorem even_of_odd_value (a b : ℤ) (h : (a ^ 2 + a * b + 2 * b ^ 2) % 2 = 1) : b % 2 = 0 := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb] at h ⊢

private theorem card_S7_eq (M : ℕ) (hM : Odd M) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 7 * p.2 ^ 2 = M} =
      Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + 2 * p.2 ^ 2 = M} := by
  have hM2 : (M : ℤ) % 2 = 1 := by obtain ⟨j, hj⟩ := hM; omega
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1.1 - p.1.2, 2 * p.1.2), by linear_combination p.2⟩
      invFun := fun p => ⟨(p.1.1 + p.1.2 / 2, p.1.2 / 2), ?_⟩
      left_inv := fun p => ?_
      right_inv := fun p => ?_ }
  · have hb : p.1.2 % 2 = 0 := even_of_odd_value _ _ (by rw [p.2, hM2])
    obtain ⟨c, hc⟩ : ∃ c, p.1.2 = 2 * c := ⟨p.1.2 / 2, by omega⟩
    have h := p.2
    rw [hc] at h ⊢
    rw [show 2 * c / 2 = c by omega]; linear_combination h
  · apply Subtype.ext; ext <;> simp
  · have hb : p.1.2 % 2 = 0 := even_of_odd_value _ _ (by rw [p.2, hM2])
    apply Subtype.ext; ext <;> simp <;> omega

/-- $(a, b) \mapsto (2a + b, b)$: $a^2 + ab + b^2 = N$ iff $x^2 + 3y^2 = 4N$. -/
private theorem card_S3_four (N : ℤ) : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = 4 * N} =
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = N} := by
  have key : ∀ x y : ℤ, x ^ 2 + 3 * y ^ 2 = 4 * N → (x - y) % 2 = 0 := by
    intro x y h
    have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
    have h2 : (x ^ 2 + 3 * y ^ 2) % 2 = 0 := by omega
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [pow_two, Int.add_emod, Int.mul_emod, hx, hy] at h2 <;> omega
  refine Nat.card_congr
    { toFun := fun p => ⟨((p.1.1 - p.1.2) / 2, p.1.2), ?_⟩
      invFun := fun p => ⟨(2 * p.1.1 + p.1.2, p.1.2), by linear_combination 4 * p.2⟩
      left_inv := fun p => ?_
      right_inv := fun p => ?_ }
  · have h2 := key _ _ p.2
    obtain ⟨c, hc⟩ : ∃ c, p.1.1 - p.1.2 = 2 * c := ⟨(p.1.1 - p.1.2) / 2, by omega⟩
    have hx : p.1.1 = 2 * c + p.1.2 := by omega
    have h := p.2
    rw [hc, show 2 * c / 2 = c by omega]
    rw [hx] at h
    linarith
  · have h2 := key _ _ p.2
    apply Subtype.ext; ext <;> simp <;> omega
  · apply Subtype.ext; ext <;> simp

private theorem four_dvd_of_two_dvd (x y : ℤ) (h : (x ^ 2 + 3 * y ^ 2) % 2 = 0) :
    (x ^ 2 + 3 * y ^ 2) % 4 = 0 := by
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  have hd : (x - y) % 2 = 0 := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [pow_two, Int.add_emod, Int.mul_emod, hx, hy] at h <;> omega
  obtain ⟨t, ht⟩ : ∃ t, x = y + 2 * t := ⟨(x - y) / 2, by omega⟩
  subst ht
  have : (y + 2 * t) ^ 2 + 3 * y ^ 2 = 4 * (y ^ 2 + y * t + t ^ 2) := by ring
  rw [this]; omega

private theorem chi3_mul (a b : ℕ) : chi3 (a * b) = chi3 a * chi3 b := by
  simp only [chi3, Nat.mul_mod a b 3]
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> simp [ha, hb]

private def chi3AF : ArithmeticFunction ℤ := ⟨chi3, by decide⟩

private theorem chi3AF_mult : chi3AF.IsMultiplicative :=
  ⟨by decide, fun {m n} _ => chi3_mul m n⟩

private theorem sum_divisors_chi3_mult :
    ((chi3AF * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) : ArithmeticFunction ℤ).IsMultiplicative :=
  chi3AF_mult.mul (ArithmeticFunction.isMultiplicative_zeta.natCast)

private theorem sum_divisors_chi3 (n : ℕ) :
    ∑ d ∈ n.divisors, chi3 d = (chi3AF * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]; rfl

private theorem sum_divisors_chi3_pow_two (k : ℕ) :
    ∑ d ∈ (2 ^ k).divisors, chi3 d = if Even k then 1 else 0 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  have h : ∀ j, chi3 (2 ^ j) = (-1) ^ j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ, chi3_mul, ih, pow_succ]; simp [chi3]
  simp only [h]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · simp [hk, hk.neg_one_pow, Nat.even_add_one]
    · simp [Nat.not_even_iff_odd.2 hk, hk.neg_one_pow, Nat.even_add_one]

private theorem sum_divisors_chi3_two_pow_mul (k m : ℕ) (hm : Odd m) :
    ∑ d ∈ (2 ^ k * m).divisors, chi3 d =
      (if Even k then 1 else 0) * ∑ d ∈ m.divisors, chi3 d := by
  rw [sum_divisors_chi3, sum_divisors_chi3_mult.map_mul_of_coprime
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)), ← sum_divisors_chi3, ← sum_divisors_chi3,
    sum_divisors_chi3_pow_two]

/-- **Smith's count for $x^2 + 2y^2$**: for odd $M$,
$\#\{(x, y) \in \mathbb Z^2 : x^2 + 2y^2 = M\} = 2(d_{1,3}(M) - d_{5,7}(M))$, where $d_{1,3}(M)$ and $d_{5,7}(M)$ count the
divisors of $M$ that are $\equiv 1, 3$ resp. $\equiv 5, 7 \pmod 8$. -/
@[kb "smith1894a" "[unverified locator]"]
theorem smith_x2_add_2y2_odd (M : ℕ) (hM : Odd M) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = M} : ℤ) =
      2 * (((M.divisors.filter fun d => d % 8 = 1 ∨ d % 8 = 3).card : ℤ) -
        (M.divisors.filter fun d => d % 8 = 5 ∨ d % 8 = 7).card) := by
  rw [card_x2_add_2y2 M hM.pos, sum_chiNeg8]

/-- **Smith's count for $x^2 + 3y^2$** (first formula): for odd $M$,
$\#\{(x, y) \in \mathbb Z^2 : x^2 + 3y^2 = M\} = 2(\#\{d \mid M : d \equiv 1 \pmod 3\} - \#\{d \mid M : d \equiv 2 \pmod 3\})$. -/
@[kb "smith1894a" "[unverified locator]"]
theorem smith_x2_add_3y2_odd (M : ℕ) (hM : Odd M) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = M} : ℤ) =
      2 * (((M.divisors.filter fun d => d % 3 = 1).card : ℤ) - (M.divisors.filter fun d => d % 3 = 2).card) := by
  have h6 := card_x2_add_xy_add_y2 M hM.pos
  rw [Qs_card, Qs_three M hM, sum_chi3] at h6
  have h3 : (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = (M : ℤ)} : ℤ) =
      (((Qs M).filter fun p => p.2 % 2 = 0).card : ℤ) := by
    rw [card_S3_eq, Qs_filter_card]
  rw [h3]
  push_cast at h6
  linarith

/-- **Smith's count for $x^2 + 7y^2$** (second formula): for odd $M$,
$\#\{(x, y) \in \mathbb Z^2 : x^2 + 7y^2 = M\} = 2(\#\{d \mid M : d \equiv 1, 2, 4 \pmod 7\} -
\#\{d \mid M : d \equiv 3, 5, 6 \pmod 7\})$. -/
@[kb "smith1894a" "[unverified locator]"]
theorem smith_x2_add_7y2_odd (M : ℕ) (hM : Odd M) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 7 * p.2 ^ 2 = M} : ℤ) =
      2 * (((M.divisors.filter fun d => d % 7 = 1 ∨ d % 7 = 2 ∨ d % 7 = 4).card : ℤ) -
        (M.divisors.filter fun d => d % 7 = 3 ∨ d % 7 = 5 ∨ d % 7 = 6).card) := by
  rw [card_S7_eq M hM, card_x2_add_xy_add_2y2 M hM.pos, sum_chi7]

/-- **The count for $x^2 + 3y^2$ for every $n$** (Dickson, *History* III, reporting
Dirichlet, Cauchy, Genocchi, Lorenz): for $n \ge 1$,
$$\#\{(x, y) \in \mathbb Z^2 : x^2 + 3y^2 = n\} = 2\sum_{d \mid n}\Bigl(\frac d3\Bigr) + 4\sum_{d \mid n/4}\Bigl(\frac d3\Bigr),$$
the second sum present only when $4 \mid n$; $\bigl(\frac d3\bigr)$ = `chi3 d` (Legendre's symbol). -/
@[kb "dickson1923" "[unverified locator]"]
theorem card_x2_add_3y2 (n : ℕ) (hn : 1 ≤ n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = n} : ℤ) =
      2 * ∑ d ∈ n.divisors, chi3 d + (if 4 ∣ n then 4 * ∑ d ∈ (n / 4).divisors, chi3 d else 0) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hm4 : ¬ 4 ∣ m := by obtain ⟨j, hj⟩ := hm; omega
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk2
  · have h := smith_x2_add_3y2_odd m hm
    have hs := sum_chi3 m.divisors
    have h0 : Even (0 : ℕ) := ⟨0, rfl⟩
    simp only [pow_zero, one_mul, h0, if_true, if_neg hm4]
    rw [h, hs]; ring
  · have hne : ¬ 4 ∣ 2 ^ 1 * m := by obtain ⟨j, hj⟩ := hm; omega
    have hemp : IsEmpty {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = ((2 ^ 1 * m : ℕ) : ℤ)} := by
      refine ⟨fun p => ?_⟩
      have e : ((2 ^ 1 * m : ℕ) : ℤ) = 2 * m := by push_cast; ring
      have h2 : (p.1.1 ^ 2 + 3 * p.1.2 ^ 2) % 2 = 0 := by rw [p.2, e]; omega
      have h4 := four_dvd_of_two_dvd _ _ h2
      rw [p.2, e] at h4
      obtain ⟨j, hj⟩ := hm
      omega
    rw [Nat.card_of_isEmpty, if_neg hne, sum_divisors_chi3_two_pow_mul 1 m hm]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hN : 1 ≤ 2 ^ j * m := Nat.mul_pos (by positivity) hm.pos
    have hn4 : 2 ^ (j + 2) * m = 4 * (2 ^ j * m) := by ring
    have e : ((2 ^ (j + 2) * m : ℕ) : ℤ) = 4 * ((2 ^ j * m : ℕ) : ℤ) := by push_cast; ring
    rw [e, card_S3_four, card_x2_add_xy_add_y2 _ hN, if_pos ⟨_, hn4⟩, hn4,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 4), sum_divisors_chi3_two_pow_mul j m hm]
    rw [← hn4, sum_divisors_chi3_two_pow_mul (j + 2) m hm]
    have hev : Even (j + 2) ↔ Even j := by simp [Nat.even_add]
    by_cases hj : Even j
    · simp [hj, hev.2 hj]; ring
    · simp [hj, mt hev.1 hj]

end QuadFormsKB.Historical.BinaryForms
