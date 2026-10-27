/-
# Cassels, Chapter 9, §5: primitive representations by sums of two, three and four squares

**Layer:** the forms $x_0^2 + \dots + x_{n-1}^2$ = `Siegel.sumSq n`; a primitive representation of $a$ is
$b \in \mathbb Z^n$ with $\gcd(b_0, \dots, b_{n-1}) = 1$ and $\sum b_i^2 = a$.

**Proves** (9.r10, Cassels p. 144) the three statements obtained from Theorem 5.1, Corollary, *together with a simple
$p$-adic study (which we omit)*:
* (i) `primRep_sumSq_two_iff`: $a > 0$ is primitively $x_1^2 + x_2^2$ iff $4 \nmid a$ and no prime $p \equiv 3
  \pmod 4$ divides $a$;
* (ii) `primRep_sumSq_three_iff`: $a > 0$ is primitively $x_1^2 + x_2^2 + x_3^2$ iff $a \equiv 1, 2, 3, 5, 6 \pmod 8$;
* (iii) `primRep_sumSq_four_iff`: $a > 0$ is primitively $x_1^2 + \dots + x_4^2$ iff $8 \nmid a$.

*Proof:* the genera of $x_1^2 + \dots + x_n^2$, $n \le 5$, have one class (`Siegel.sameGenus_sumSq_intEquiv`, Lemma 3.2,
Corollary 2), so Theorem 5.1, Corollary (`exists_primRep_of_one_class`) reduces sufficiency to primitive representations
over $\mathbb Z_2$ (and over $\mathbb Z_p$, $p \mid a$, for $n = 2$): a $2$-adic unit $\equiv 1 \pmod 8$ is a square
(`HilbertLocal.isSquare_two_adic_unit_iff`), and $-1$ is a square in $\mathbb Z_p$ for $p \equiv 1 \pmod 4$. The
necessity is a congruence computation modulo $8$ (resp. modulo $p$).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-- The value of $I_n$ over $\mathbb Z$ is the sum of squares. -/
theorem eval_sumSq_int {n : ℕ} (x : Fin n → ℤ) : (sumSq n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSq, Kneser.eval_diag]; simp

/-- The value of the base change of $I_n$ to any commutative ring is the sum of squares. -/
theorem eval_map_sumSq {n : ℕ} {R : Type*} [CommRing R] (x : Fin n → R) :
    ((sumSq n).map (Int.castRingHom R)).eval x = ∑ i, x i ^ 2 := by
  have : (sumSq n).map (Int.castRingHom R) = QuadForm.diag fun _ => (1 : R) := by
    ext i j
    simp only [sumSq, QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [this, Kneser.eval_diag]; simp

/-- $I_n$ ($n \ge 1$) represents every positive integer over $\mathbb R$. -/
theorem sumSq_real {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : 0 < a) :
    ∃ x : Fin n → ℝ, (sumSq n).evalIn ℝ x = a := by
  refine ⟨Pi.single ⟨0, hn⟩ (Real.sqrt a), ?_⟩
  have e : (sumSq n).evalIn ℝ (Pi.single ⟨0, hn⟩ (Real.sqrt a)) =
      ((sumSq n).map (Int.castRingHom ℝ)).eval (Pi.single ⟨0, hn⟩ (Real.sqrt a)) := by
    simp [QuadForm.evalIn, QuadForm.map]
  rw [e, eval_map_sumSq, Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp [Real.sq_sqrt (by exact_mod_cast ha.le : (0:ℝ) ≤ a)]
  · intro b _ hb; simp [hb]
  · simp

/-- Squares modulo $8$: odd squares are $1$, even squares are $0$ or $4$. -/
theorem sq_mod_eight (x : ℤ) :
    (x % 2 = 1 ∧ x ^ 2 % 8 = 1) ∨ (x % 2 = 0 ∧ (x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4)) := by
  have h : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨
      x % 8 = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h] <;> omega

/-- A primitive vector is not entirely even. -/
theorem not_forall_even_of_gcd {n : ℕ} (x : Fin n → ℤ) (h : Finset.univ.gcd x = 1) :
    ¬ ∀ i, x i % 2 = 0 := by
  intro hall
  have : (2 : ℤ) ∣ Finset.univ.gcd x :=
    Finset.dvd_gcd fun i _ => Int.dvd_of_emod_eq_zero (hall i)
  rw [h] at this; omega

/-- A $\mathbb Z_p$-integer is a unit iff its residue is nonzero. -/
theorem isUnit_intCast_padic {p : ℕ} [Fact p.Prime] (c : ℤ) :
    IsUnit (c : ℤ_[p]) ↔ ¬ (p : ℤ) ∣ c := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- A unit of $\mathbb Z_p$ that is a square in $\mathbb Q_p$ is the square of a unit of $\mathbb Z_p$. -/
theorem exists_sq_root_of_isSquare {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ)
    (h : IsSquare ((u : ℤ_[p]) : ℚ_[p])) : ∃ w : ℤ_[p], w * w = u ∧ IsUnit w := by
  obtain ⟨x, hx⟩ := h
  have hu : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.norm_coe]; exact (PadicInt.isUnit_iff).mp u.isUnit
  have hx1 : ‖x‖ = 1 := by
    rw [hx, norm_mul] at hu
    nlinarith [norm_nonneg x]
  obtain ⟨w, hwx⟩ : ∃ w : ℤ_[p], (w : ℚ_[p]) = x := ⟨⟨x, hx1.le⟩, rfl⟩
  refine ⟨w, ?_, PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def, hwx]; exact hx1)⟩
  apply PadicInt.ext
  rw [PadicInt.coe_mul, hwx]
  exact hx.symm

/-- An integer $\equiv 1 \pmod 8$ is the square of a unit of $\mathbb Z_2$. -/
theorem two_adic_sq (c : ℤ) (hc : c % 8 = 1) : ∃ z : ℤ_[2], IsUnit z ∧ z * z = c := by
  have hu : IsUnit (c : ℤ_[2]) := by
    rw [isUnit_intCast_padic]; omega
  have hsq := (HilbertLocal.isSquare_two_adic_unit_iff hu.unit).mpr (by
    show PadicInt.toZModPow 3 (c : ℤ_[2]) = 1
    rw [map_intCast, ← ZMod.intCast_mod c (2 ^ 3)]
    have : c % ((2 ^ 3 : ℕ) : ℤ) = 1 := by norm_num; exact hc
    rw [this]; simp)
  obtain ⟨w, hw, hwu⟩ := exists_sq_root_of_isSquare hu.unit hsq
  exact ⟨w, hwu, by rw [hw]; rfl⟩

/-- A $2$-adic primitive representation with prescribed integer tail, whenever the head is $\equiv 1 \pmod 8$. -/
theorem two_adic_rep {m : ℕ} (w : Fin m → ℤ) (a : ℤ) (h : (a - ∑ i, w i ^ 2) % 8 = 1) :
    ∃ x : Fin (m + 1) → ℤ_[2], (∃ i, IsUnit (x i)) ∧ ∑ i, x i ^ 2 = a := by
  obtain ⟨z, hz, hzz⟩ := two_adic_sq _ h
  refine ⟨Fin.cons z (fun i => (w i : ℤ_[2])), ⟨0, by simpa using hz⟩, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  push_cast at hzz
  linear_combination hzz

/-- Reduction of a primitive representation by $I_n$ ($2 \le n \le 5$) to local data at $2$ (and at odd $p \mid a$ if
$n = 2$). -/
theorem exists_primRep_sumSq {n : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5) {a : ℤ} (ha : 0 < a)
    (h2 : ∃ x : Fin n → ℤ_[2], (∃ i, IsUnit (x i)) ∧ ∑ i, x i ^ 2 = a)
    (hp : n = 2 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → (p : ℤ) ∣ a →
      ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ ∑ i, x i ^ 2 = a) :
    ∃ x : Fin n → ℤ, Finset.univ.gcd x = 1 ∧ (sumSq n).eval x = a := by
  refine exists_primRep_of_one_class (sumSq n) hn2 ?_ (fun f' h => sameGenus_sumSq_intEquiv hn5 h)
    ha.ne' (sumSq_real (by omega) ha) ?_
  · rw [det_hessian_sumSq]; exact pow_ne_zero _ two_ne_zero
  · intro p _ hpc
    simp_rw [eval_map_sumSq]
    have h2' : p = 2 → ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ ∑ i, x i ^ 2 = a := by
      rintro rfl; exact h2
    by_cases hp2 : p = 2
    · exact h2' hp2
    · rcases hpc with h | h | ⟨hn, h⟩
      · exact absurd h hp2
      · rw [det_hessian_sumSq] at h
        have := (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_of_dvd_pow h
        exact absurd (by exact_mod_cast (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          Nat.prime_two).mp (by exact_mod_cast this)) hp2
      · exact hp hn p hp2 h

/-- For $p \equiv 1 \pmod 4$ and $p \mid a$, $a$ is represented primitively over $\mathbb Z_p$ by $x^2 + y^2$. -/
theorem odd_p_rep (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 1) (a : ℤ) (hpa : (p : ℤ) ∣ a) :
    ∃ x : Fin 2 → ℤ_[p], (∃ i, IsUnit (x i)) ∧ ∑ i, x i ^ 2 = a := by
  have hp2 : p ≠ 2 := by omega
  have hsq : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have h2 := (HilbertLocal.isSquare_unit_iff hp2 (-1)).mpr (by simpa using hsq)
  obtain ⟨i, hi, hiu⟩ := exists_sq_root_of_isSquare (-1) h2
  simp only [Units.val_neg, Units.val_one] at hi
  have h2u : IsUnit (2 : ℤ_[p]) := by
    simpa using (isUnit_intCast_padic (p := p) 2).mpr (by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      have := (Fact.out : p.Prime).two_le
      have h' : p ∣ 2 := by exact_mod_cast h
      omega)
  obtain ⟨e, he⟩ := h2u.exists_right_inv
  have ha1 : IsUnit (a + 1 : ℤ_[p]) := by
    have := (isUnit_intCast_padic (p := p) (a + 1)).mpr (by
      intro h
      have h1 : (p : ℤ) ∣ 1 := by simpa using (dvd_sub h hpa)
      have := Int.le_of_dvd (by norm_num) h1
      have := (Fact.out : p.Prime).two_le
      omega)
    simpa using this
  refine ⟨![(a + 1) * e, (a - 1) * e * (-i)], ⟨0, ?_⟩, ?_⟩
  · simpa using ha1.mul (IsUnit.of_mul_eq_one 2 (by rw [mul_comm]; exact he))
  · simp only [Fin.sum_univ_two]
    simp
    linear_combination (e ^ 2 * (a - 1) ^ 2) * hi + (a : ℤ_[p]) * (2 * e + 1) * he

/-- An odd positive integer with no prime factor $\equiv 3 \pmod 4$ is $\equiv 1 \pmod 4$. -/
theorem mod_four_of_no_three (m : ℕ) (hodd : m % 2 = 1) (h : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 ≠ 3) :
    m % 4 = 1 := by
  induction m using induction_on_primes with
  | zero => omega
  | one => rfl
  | prime_mul p a hp ih =>
    have ho : Odd (p * a) := Nat.odd_iff.mpr hodd
    rw [Nat.odd_mul] at ho
    have hp1 := Nat.odd_iff.mp ho.1
    have ha1 := Nat.odd_iff.mp ho.2
    have hp3 := h p hp (dvd_mul_right _ _)
    have ha4 := ih ha1 (fun q hq hqa => h q hq (dvd_mul_of_dvd_right hqa p))
    rw [Nat.mul_mod, ha4]
    omega

/-- **Cassels, Ch. 9, §5, p. 144 (i):** *a positive integer $a$ is represented primitively by $x_1^2 + x_2^2$ if and
only if it is not divisible by $4$ or by any prime $p \equiv 3 \pmod 4$.* -/
@[kb "cassels1978" "Ch. 9, §5, p. 144 (i) (primitive sums of two squares)"]
theorem primRep_sumSq_two_iff {a : ℤ} (ha : 0 < a) :
    (∃ x : Fin 2 → ℤ, Finset.univ.gcd x = 1 ∧ (sumSq 2).eval x = a) ↔
      ¬ (4 : ℤ) ∣ a ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → p % 4 ≠ 3 := by
  constructor
  · rintro ⟨x, hg, hx⟩
    rw [eval_sumSq_int, Fin.sum_univ_two] at hx
    have hne : ¬ (x 0 % 2 = 0 ∧ x 1 % 2 = 0) :=
      fun ⟨e0, e1⟩ => not_forall_even_of_gcd x hg (by
        intro i; fin_cases i <;> assumption)
    have h0 := sq_mod_eight (x 0)
    have h1 := sq_mod_eight (x 1)
    refine ⟨by omega, fun p hp hpa hp3 => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    have hz : ((x 0 : ℤ) : ZMod p) ^ 2 + ((x 1 : ℤ) : ZMod p) ^ 2 = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod p) hx
      push_cast at this
      rw [this]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpa
    have hx0 : ((x 0 : ℤ) : ZMod p) ≠ 0 := by
      intro h0'
      rw [h0'] at hz
      have h1' : ((x 1 : ℤ) : ZMod p) = 0 := by simpa using hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0' h1'
      have : (p : ℤ) ∣ Finset.univ.gcd x :=
        Finset.dvd_gcd fun i _ => by fin_cases i <;> assumption
      rw [hg] at this
      have := Int.le_of_dvd (by norm_num) this
      have := hp.two_le
      omega
    have hsq : IsSquare (-1 : ZMod p) := by
      refine ⟨((x 1 : ℤ) : ZMod p) / ((x 0 : ℤ) : ZMod p), ?_⟩
      field_simp
      linear_combination -hz
    exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp3
  · rintro ⟨h4, hp⟩
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
    have hp' : ∀ q : ℕ, q.Prime → q ∣ m → q % 4 ≠ 3 := fun q hq hqm =>
      hp q hq (by exact_mod_cast hqm)
    have hr : (m : ℤ) % 8 = 1 ∨ (m : ℤ) % 8 = 5 ∨ (m : ℤ) % 8 = 2 := by
      by_cases hm : m % 2 = 1
      · have := mod_four_of_no_three m hm hp'
        omega
      · have hm2 : (m / 2) % 2 = 1 := by omega
        have := mod_four_of_no_three (m / 2) hm2 (fun q hq hqm => hp' q hq
          (dvd_trans hqm (Nat.div_dvd_of_dvd (by omega))))
        omega
    refine exists_primRep_sumSq (n := 2) le_rfl (by norm_num) ha ?_ ?_
    · have key := fun w : Fin 1 → ℤ => fun hw : ((m : ℤ) - ∑ i, w i ^ 2) % 8 = 1 =>
        two_adic_rep w (m : ℤ) hw
      rcases hr with hr | hr | hr
      · exact key ![0] (by simp; omega)
      · exact key ![2] (by simp; omega)
      · exact key ![1] (by simp; omega)
    · intro _ p _ hp2 hpa
      have hodd := (Fact.out : p.Prime).eq_two_or_odd
      exact odd_p_rep p (by have := hp p (Fact.out) hpa; omega) _ hpa

/-- **Cassels, Ch. 9, §5, p. 144 (ii):** *a positive integer $a$ is represented primitively by
$x_1^2 + x_2^2 + x_3^2$ if and only if $a \equiv 1, 2, 3, 5, 6 \pmod 8$.* -/
@[kb "cassels1978" "Ch. 9, §5, p. 144 (ii) (primitive sums of three squares)"]
theorem primRep_sumSq_three_iff {a : ℤ} (ha : 0 < a) :
    (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ (sumSq 3).eval x = a) ↔
      a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 6 := by
  constructor
  · rintro ⟨x, hg, hx⟩
    rw [eval_sumSq_int, Fin.sum_univ_three] at hx
    have hne : ¬ (x 0 % 2 = 0 ∧ x 1 % 2 = 0 ∧ x 2 % 2 = 0) :=
      fun ⟨e0, e1, e2⟩ => not_forall_even_of_gcd x hg (by
        intro i; fin_cases i <;> assumption)
    have h0 := sq_mod_eight (x 0)
    have h1 := sq_mod_eight (x 1)
    have h2 := sq_mod_eight (x 2)
    omega
  · intro h
    have key := fun w : Fin 2 → ℤ => fun hw : (a - ∑ i, w i ^ 2) % 8 = 1 =>
      exists_primRep_sumSq (n := 3) (by norm_num) (by norm_num) ha (two_adic_rep w a hw)
        (fun h => absurd h (by norm_num))
    rcases h with hr | hr | hr | hr | hr
    · exact key ![0, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 1] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![2, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 2] (by simp [Fin.sum_univ_succ]; omega)

/-- **Cassels, Ch. 9, §5, p. 144 (iii):** *a positive integer $a$ is represented primitively by
$x_1^2 + x_2^2 + x_3^2 + x_4^2$ if and only if $a \not\equiv 0 \pmod 8$.* -/
@[kb "cassels1978" "Ch. 9, §5, p. 144 (iii) (primitive sums of four squares)"]
theorem primRep_sumSq_four_iff {a : ℤ} (ha : 0 < a) :
    (∃ x : Fin 4 → ℤ, Finset.univ.gcd x = 1 ∧ (sumSq 4).eval x = a) ↔ ¬ (8 : ℤ) ∣ a := by
  constructor
  · rintro ⟨x, hg, hx⟩
    rw [eval_sumSq_int, Fin.sum_univ_four] at hx
    have hne : ¬ (x 0 % 2 = 0 ∧ x 1 % 2 = 0 ∧ x 2 % 2 = 0 ∧ x 3 % 2 = 0) :=
      fun ⟨e0, e1, e2, e3⟩ => not_forall_even_of_gcd x hg (by
        intro i; fin_cases i <;> assumption)
    have h0 := sq_mod_eight (x 0)
    have h1 := sq_mod_eight (x 1)
    have h2 := sq_mod_eight (x 2)
    have h3 := sq_mod_eight (x 3)
    omega
  · intro h
    have key := fun w : Fin 3 → ℤ => fun hw : (a - ∑ i, w i ^ 2) % 8 = 1 =>
      exists_primRep_sumSq (n := 4) (by norm_num) (by norm_num) ha (two_adic_rep w a hw)
        (fun h => by omega)
    have hr : a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨
        a % 8 = 7 := by omega
    rcases hr with hr | hr | hr | hr | hr | hr | hr
    · exact key ![0, 0, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 0, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 1, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 1, 1] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![2, 0, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 2, 0] (by simp [Fin.sum_univ_succ]; omega)
    · exact key ![1, 1, 2] (by simp [Fin.sum_univ_succ]; omega)

end QuadFormsKB.Siegel
