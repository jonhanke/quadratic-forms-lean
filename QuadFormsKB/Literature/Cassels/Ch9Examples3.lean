/-
# Cassels, Chapter 9, Example 23: a ternary form failing the local-global principle for primitive representations

**Layer:** the integer-valued form $x_0^2 - 2x_1^2 + 64x_2^2$ (`ex23Form`, `QuadForm.diag`), primitive representations
over $\mathbb Z$ (`primRepSet`, $\gcd = 1$) and over $\mathbb Z_p$ (some coordinate a unit, as in
`Siegel.exists_sameGenus_primRep`).

**Proves** Example 23 (p. 167): for $m \equiv \pm 3 \pmod 8$, $m^2$ is primitively represented by
$x_0^2 - 2x_1^2 + 64x_2^2$ over every $\mathbb Z_p$ (`ex23_local`) and over $\mathbb R$, but not over $\mathbb Z$
(`ex23_not_primRep`). This shows that Theorem 1.5 fails for $n = 3$ (9.r14).

*Proof (Cassels' hint).* Globally: if $x_0^2 - 2x_1^2 = (m - 8x_2)(m + 8x_2)$, every prime $p \equiv \pm 3 \pmod 8$
divides $x_0^2 - 2x_1^2$ to an even power (`even_padicValInt_sub`, since $2$ is not a square modulo $p$), while
$m - 8x_2 \equiv \pm 3 \pmod 8$ has such a prime to an odd power (`exists_odd_padicValInt`, via the character
$\chi_8$); this prime cannot divide $m + 8x_2$, else it divides $m$, $x_2$, $x_0$, $x_1$. Locally: $(m, 0, 0)$ if
$p \nmid m$; if $p \mid m$ ($p$ odd), choose $y, z$ with $2y^2 - 64z^2 \equiv 1 \pmod p$ (`FiniteField.exists_root_sum_quadratic`)
and solve $x^2 = m^2 + 2y^2 - 64z^2 \equiv 1$ by Hensel.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec6
import QuadFormsKB.Siegel.UnimodularPadic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.FieldTheory.Finite.Basic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-- The form $x_0^2 - 2x_1^2 + 64x_2^2$ of Cassels' Example 23 (Ch. 9, p. 167). -/
def ex23Form : QuadForm ℤ 3 := QuadForm.diag ![1, -2, 64]

/-- Evaluation of $x_0^2 - 2x_1^2 + 64x_2^2$ over any commutative ring. -/
theorem eval_map_ex23Form {R : Type*} [CommRing R] (x : Fin 3 → R) :
    (ex23Form.map (Int.castRingHom R)).eval x = x 0 ^ 2 - 2 * x 1 ^ 2 + 64 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ex23Form, QuadForm.diag, QuadForm.map,
    Matrix.diagonal_apply]
  ring

/-- Evaluation of $x_0^2 - 2x_1^2 + 64x_2^2$ over $\mathbb Z$. -/
theorem eval_ex23Form (x : Fin 3 → ℤ) : ex23Form.eval x = x 0 ^ 2 - 2 * x 1 ^ 2 + 64 * x 2 ^ 2 := by
  have h := eval_map_ex23Form (R := ℤ) x
  simpa [QuadForm.map] using h

/-! ### Primes $p \equiv \pm 3 \pmod 8$ and $x^2 - 2y^2$ -/

/-- For $p \equiv \pm 3 \pmod 8$, $p \mid x^2 - 2y^2$ implies $p \mid x$ and $p \mid y$ ($2$ is not a square
modulo $p$). -/
theorem dvd_of_dvd_sq_sub_two_sq {p : ℕ} [hp : Fact p.Prime] (hp8 : p % 8 = 3 ∨ p % 8 = 5) {x y : ℤ}
    (h : (p : ℤ) ∣ x ^ 2 - 2 * y ^ 2) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hns : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]; omega
  have hy : (p : ℤ) ∣ y := by
    by_contra hy
    have hy0 : (y : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply hns
    have h' : ((x ^ 2 - 2 * y ^ 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
    push_cast at h'
    refine ⟨(x : ZMod p) / y, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy0 hy0)]
    linear_combination (-1 : ZMod p) * h'
  refine ⟨?_, hy⟩
  have h2 : (p : ℤ) ∣ x ^ 2 := by
    have : (p : ℤ) ∣ 2 * y ^ 2 := dvd_mul_of_dvd_right (dvd_pow hy two_ne_zero) 2
    simpa using dvd_add h this
  exact Int.Prime.dvd_pow' hp.out h2

/-- For $p \equiv \pm 3 \pmod 8$ and $x^2 - 2y^2 \ne 0$, the exponent of $p$ in $x^2 - 2y^2$ is even. -/
theorem even_padicValInt_sub {p : ℕ} [hp : Fact p.Prime] (hp8 : p % 8 = 3 ∨ p % 8 = 5) :
    ∀ (k : ℕ) (x y : ℤ), padicValInt p (x ^ 2 - 2 * y ^ 2) = k → x ^ 2 - 2 * y ^ 2 ≠ 0 →
      Even (padicValInt p (x ^ 2 - 2 * y ^ 2)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x y hk h0
    by_cases hd : (p : ℤ) ∣ x ^ 2 - 2 * y ^ 2
    · obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ := dvd_of_dvd_sq_sub_two_sq hp8 hd
      have he : (p * x') ^ 2 - 2 * (p * y') ^ 2 = (p : ℤ) ^ 2 * (x' ^ 2 - 2 * y' ^ 2) := by ring
      have h0' : x' ^ 2 - 2 * y' ^ 2 ≠ 0 := by
        intro h; apply h0; rw [he, h, mul_zero]
      have hv : padicValInt p ((p * x') ^ 2 - 2 * (p * y') ^ 2) = 2 + padicValInt p (x' ^ 2 - 2 * y' ^ 2) := by
        rw [he, padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) h0']
        congr 1
        rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
          padicValNat.prime_pow]
      rw [hv]
      have := ih (padicValInt p (x' ^ 2 - 2 * y' ^ 2)) (by omega) x' y' rfl h0'
      exact (even_two.add this)
    · rw [padicValInt.eq_zero_of_not_dvd hd]; exact ⟨0, rfl⟩

/-- For odd $N \equiv \pm 3 \pmod 8$ some prime $p \equiv \pm 3 \pmod 8$ divides $N$ to an odd power (the character
$\chi_8$ is multiplicative, $\chi_8(N) = -1$). -/
theorem exists_odd_padicValInt {N : ℤ} (hN : N % 8 = 3 ∨ N % 8 = 5) :
    ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ Odd (N.natAbs.factorization p) := by
  by_contra hno
  push Not at hno
  have hN0 : N.natAbs ≠ 0 := by intro h; rw [Int.natAbs_eq_zero.1 h] at hN; omega
  have hχ : ZMod.χ₈ (N.natAbs : ZMod 8) = 1 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod, Nat.cast_prod, map_prod]
    refine Finset.prod_eq_one fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (2 : ℤ) ∣ N := Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactors hp)
      omega
    rw [Nat.cast_pow, map_pow]
    have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      have := hpp.eq_one_or_self_of_dvd 2
      have h2 : ¬ 2 ∣ p := fun h => hp2 ((hpp.eq_one_or_self_of_dvd 2 h).resolve_left (by norm_num)).symm
      omega
    have hc : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
    rcases hp8 with h | h | h | h
    · rw [hc, h]; simp
    · have he := Nat.not_odd_iff_even.1 (hno p hpp (Or.inl h))
      obtain ⟨k, hk⟩ := he
      rw [hk, hc, h, pow_add, ← sq]
      have : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 := by decide
      rw [this]; ring_nf; simp
    · have he := Nat.not_odd_iff_even.1 (hno p hpp (Or.inr h))
      obtain ⟨k, hk⟩ := he
      rw [hk, hc, h, pow_add, ← sq]
      have : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
      rw [this]; ring_nf; simp
    · rw [hc, h]; simp
  have hχN : ZMod.χ₈ (N.natAbs : ZMod 8) = -1 := by
    have hc : ((N.natAbs : ℕ) : ZMod 8) = ((N.natAbs % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
    rw [hc]
    rcases Int.natAbs_eq N with h | h
    · have : N.natAbs % 8 = 3 ∨ N.natAbs % 8 = 5 := by omega
      rcases this with h' | h' <;> rw [h'] <;> decide
    · have : N.natAbs % 8 = 3 ∨ N.natAbs % 8 = 5 := by omega
      rcases this with h' | h' <;> rw [h'] <;> decide
  rw [hχ] at hχN
  exact absurd hχN (by decide)

/-! ### Example 23 -/

/-- **Cassels, Ch. 9, Example 23** (p. 167), global part: *let $m \equiv \pm 3 \pmod 8$. Then $m^2$ is not
represented primitively by $x^2 - 2y^2 + 64z^2$ over $\mathbb Z$.* -/
@[kb "cassels1978" "Ch. 9, Ex. 23, p. 167 (not over ℤ)"]
theorem ex23_not_primRep {m : ℤ} (hm : m % 8 = 3 ∨ m % 8 = 5) : primRepSet ex23Form (m ^ 2) = ∅ := by
  ext x
  simp only [primRepSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hgcd hx
  rw [eval_ex23Form] at hx
  set N₁ := m - 8 * x 2
  set N₂ := m + 8 * x 2
  have hprod : x 0 ^ 2 - 2 * x 1 ^ 2 = N₁ * N₂ := by simp only [N₁, N₂]; linear_combination hx
  have hN₁ : N₁ % 8 = 3 ∨ N₁ % 8 = 5 := by simp only [N₁]; omega
  have hN₁0 : N₁ ≠ 0 := by intro h; rw [h] at hN₁; omega
  have hN₂0 : N₂ ≠ 0 := by intro h; simp only [N₂] at h; omega
  obtain ⟨p, hpp, hp8, hodd⟩ := exists_odd_padicValInt hN₁
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : (p : ℤ) ≠ 2 := by intro h; have : p = 2 := by exact_mod_cast h
                               subst this; omega
  -- `p ∤ N₂`
  have hnd : ¬ (p : ℤ) ∣ N₂ := by
    intro hd₂
    have hd₁ : (p : ℤ) ∣ N₁ := by
      have hv : 0 < N₁.natAbs.factorization p := Nat.pos_of_ne_zero (fun h => by rw [h] at hodd; exact absurd hodd (by decide))
      exact Int.natCast_dvd.2 (Nat.dvd_of_factorization_pos (Nat.pos_iff_ne_zero.1 hv))
    have hcop : IsCoprime (p : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := (Nat.coprime_primes hpp Nat.prime_two).2 (by intro h; apply hp2; exact_mod_cast h)
      exact_mod_cast this
    have hm' : (p : ℤ) ∣ m := by
      have : (p : ℤ) ∣ 2 * m := by
        have := dvd_add hd₁ hd₂; simp only [N₁, N₂] at this; convert this using 1; ring
      exact hcop.dvd_of_dvd_mul_left this
    have hz : (p : ℤ) ∣ x 2 := by
      have h16 : (p : ℤ) ∣ 2 ^ 4 * x 2 := by
        have := dvd_sub hd₂ hd₁; simp only [N₁, N₂] at this; convert this using 1; ring
      exact (hcop.pow_right (n := 4)).dvd_of_dvd_mul_left h16
    have hxy := dvd_of_dvd_sq_sub_two_sq hp8 (show (p : ℤ) ∣ x 0 ^ 2 - 2 * x 1 ^ 2 by
      rw [hprod]; exact dvd_mul_of_dvd_left hd₁ _)
    have : (p : ℤ) ∣ Finset.univ.gcd x := by
      refine Finset.dvd_gcd fun i _ => ?_
      fin_cases i
      · exact hxy.1
      · exact hxy.2
      · exact hz
    rw [hgcd] at this
    exact hpp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  -- the exponent of `p` in `x₀² - 2x₁²` is odd and even
  have hev := even_padicValInt_sub hp8 _ (x 0) (x 1) rfl (by rw [hprod]; exact mul_ne_zero hN₁0 hN₂0)
  rw [hprod, padicValInt.mul hN₁0 hN₂0, padicValInt.eq_zero_of_not_dvd hnd, add_zero, padicValInt,
    ← Nat.factorization_def _ hpp] at hev
  exact (Nat.not_even_iff_odd.2 hodd) hev

/-- **Cassels, Ch. 9, Example 23** (p. 167), local part: *let $m \equiv \pm 3 \pmod 8$. Then $m^2$ is represented
primitively by $x^2 - 2y^2 + 64z^2$ over every $\mathbb Z_p$* (some coordinate a unit of $\mathbb Z_p$). Over
$\mathbb R$, $(m, 0, 0)$ is a representation. -/
@[kb "cassels1978" "Ch. 9, Ex. 23, p. 167 (over every ℤ_p)"]
theorem ex23_local {m : ℤ} (hm : m % 8 = 3 ∨ m % 8 = 5) (p : ℕ) [hp : Fact p.Prime] :
    ∃ x : Fin 3 → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (ex23Form.map (Int.castRingHom ℤ_[p])).eval x = (m : ℤ_[p]) ^ 2 := by
  have hunit : ∀ c : ℤ_[p], PadicInt.toZMod c ≠ 0 → IsUnit c := fun c hc => by
    by_contra h
    apply hc
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact h
  by_cases hpm : (p : ℤ) ∣ m
  · -- `p` is odd
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    have hcard : Fintype.card (ZMod p) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
    have h64 : (64 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 ^ 6 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow this))
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h; apply h64; rw [show (64 : ZMod p) = 2 * 32 by norm_num, h, zero_mul]
    obtain ⟨y, z, hyz⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C 2 * Polynomial.X ^ 2) (g := Polynomial.C (-64) * Polynomial.X ^ 2 - Polynomial.C 1)
      (by rw [Polynomial.degree_C_mul_X_pow 2 h2]; rfl)
      (by
        rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
          rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 h64)]
        · rfl
        · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide))
      hcard
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X] at hyz
    set Y : ℤ_[p] := (y.val : ℤ_[p])
    set Z : ℤ_[p] := (z.val : ℤ_[p])
    set u : ℤ_[p] := (m : ℤ_[p]) ^ 2 + 2 * Y ^ 2 - 64 * Z ^ 2
    have hmz : PadicInt.toZMod (m : ℤ_[p]) = 0 := by
      rw [map_intCast]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpm
    have hY : PadicInt.toZMod Y = y := by rw [map_natCast, ZMod.natCast_zmod_val]
    have hZ : PadicInt.toZMod Z = z := by rw [map_natCast, ZMod.natCast_zmod_val]
    have hu : PadicInt.toZMod u = 1 ^ 2 := by
      simp only [u, map_add, map_sub, map_mul, map_pow, hmz, hY, hZ, map_ofNat]
      linear_combination hyz
    obtain ⟨X, hX⟩ := Kneser.exists_sq_eq_of_toZMod hp2 u one_ne_zero hu
    refine ⟨![X, Y, Z], ⟨0, ?_⟩, ?_⟩
    · apply hunit
      intro h0
      have : PadicInt.toZMod (X ^ 2) = 0 := by rw [map_pow, show PadicInt.toZMod X = 0 from h0]; ring
      rw [hX, hu] at this
      simp at this
    · rw [eval_map_ex23Form]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      rw [hX]; ring
  · refine ⟨![(m : ℤ_[p]), 0, 0], ⟨0, ?_⟩, ?_⟩
    · apply hunit
      simp only [Matrix.cons_val_zero, map_intCast]
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    · rw [eval_map_ex23Form]; simp

/-- Example 23 over $\mathbb R$: for $m \ne 0$, $(m, 0, 0)$ is a nonzero real representation of $m^2$. -/
theorem ex23_real {m : ℤ} (hm : m ≠ 0) :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ (ex23Form.map (Int.castRingHom ℝ)).eval x = (m : ℝ) ^ 2 := by
  refine ⟨![(m : ℝ), 0, 0], fun h => hm (by simpa using congrFun h 0), ?_⟩
  rw [eval_map_ex23Form]; simp

end QuadFormsKB.Siegel
