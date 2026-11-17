/-
# Dickson, *History* III (1923): sums of three squares and quaternary representation numbers

**Library** `QuadFormsKB.Historical.Dickson` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Dickson, *History of the Theory of Numbers* III (1923), ch. on ternary forms): if $p = 8n - 1$ is prime, then $2p = x^2 + y^2 + z^2$
  (`two_mul_prime_eq_sum_three_sq`).
* (same): every odd positive integer $n$ is
  $2x^2 + y^2 + z^2$ (`odd_eq_two_sq_add_sq_add_sq`).
* (same): for odd $m$ the number of representations of $m$
  as a sum of four squares is twice the number of representations by $x^2 + y^2 + 2z^2 + 2t^2$
  (`card_sum_four_sq_eq_two_mul`), and the number of representations by $x^2 + 2y^2 + 2z^2 + 2t^2$ equals the number of
  representations by $x^2 + y^2 + z^2 + 2t^2$ with $x$ odd (`card_1222_eq_card_1112_odd`).

Representation numbers are `Nat.card` of the solution sets in $\mathbb Z^4$ (`repCount4`); the forms are positive
definite, so these sets are finite. Variables are $x_0, \dots, x_3$ in the Lean statements (0-based, `Fin 4`); the
source's $x, y, z, t$ are $x_0, x_1, x_2, x_3$.
-/
import QuadFormsKB.Literature.Classical.SumsOfSquares

namespace QuadFormsKB.Historical.Dickson

/-! ### Sums of three squares -/

private theorem three_sq_of_not_form (n : ℕ) (h : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨a, b, c, habc⟩ := (QuadFormsKB.Grosswald.legendre_three_squares n).2 h
  exact ⟨a, b, c, by exact_mod_cast habc.symm⟩

private theorem not_form_of_mod (n : ℕ) (h : n % 8 = 6 ∨ n % 8 = 2 ∨ n % 8 = 14 % 8 ∨ n % 4 = 2) :
    ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  rintro ⟨a, b, hab⟩
  rcases a with _ | a
  · simp at hab; omega
  · rw [pow_succ] at hab
    have : n = 4 * (4 ^ a * (8 * b + 7)) := by rw [hab]; ring
    generalize 4 ^ a * (8 * b + 7) = t at this
    omega

private theorem par_sq2 (a b : ℤ) : Even (a ^ 2 + b ^ 2) ↔ Even (a + b) := by
  simp [Int.even_add, Int.even_pow]

private theorem par_sq4 (a b c d : ℤ) :
    Even (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ↔ (Even (a + b) ↔ Even (c + d)) := by
  simp [Int.even_add, Int.even_pow]
  tauto

private theorem split_sq (a b : ℤ) (h : Even (a + b)) :
    a ^ 2 + b ^ 2 = 2 * ((a + b) / 2) ^ 2 + 2 * ((a - b) / 2) ^ 2 := by
  obtain ⟨r, hr⟩ := h
  have e1 : (a + b) / 2 = r := by omega
  have e2 : (a - b) / 2 = r - b := by omega
  rw [e1, e2]
  have : a = 2 * r - b := by omega
  subst this
  ring

private theorem odd_rep (n m u v w : ℤ) (hm : n = 2 * m + 1) (h : 2 * n = u ^ 2 + v ^ 2 + w ^ 2) :
    ∃ x y z : ℤ, n = 2 * x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨i, hi | hi⟩ := Int.even_or_odd' u <;> obtain ⟨j, hj | hj⟩ := Int.even_or_odd' v <;>
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' w <;> subst hi hj hk
  · exfalso
    have : 4 * m + 2 = 4 * (i ^ 2 + j ^ 2 + k ^ 2) := by nlinarith
    generalize i ^ 2 + j ^ 2 + k ^ 2 = q at this; omega
  · exfalso
    have : 4 * m + 2 = 4 * (i ^ 2 + j ^ 2 + k ^ 2 + k) + 1 := by nlinarith
    generalize i ^ 2 + j ^ 2 + k ^ 2 + k = q at this; omega
  · exfalso
    have : 4 * m + 2 = 4 * (i ^ 2 + j ^ 2 + k ^ 2 + j) + 1 := by nlinarith
    generalize i ^ 2 + j ^ 2 + k ^ 2 + j = q at this; omega
  · exact ⟨i, j + k + 1, j - k, by nlinarith⟩
  · exfalso
    have : 4 * m + 2 = 4 * (i ^ 2 + j ^ 2 + k ^ 2 + i) + 1 := by nlinarith
    generalize i ^ 2 + j ^ 2 + k ^ 2 + i = q at this; omega
  · exact ⟨j, i + k + 1, i - k, by nlinarith⟩
  · exact ⟨k, i + j + 1, i - j, by nlinarith⟩
  · exfalso
    have : 4 * m + 2 = 4 * (i ^ 2 + j ^ 2 + k ^ 2 + k + j + i) + 3 := by nlinarith
    generalize i ^ 2 + j ^ 2 + k ^ 2 + k + j + i = q at this; omega


/-- (Dickson, *History* III): if $p = 8n - 1$ is
prime, then $2p$ is a sum of three squares. Here $p \equiv 7 \pmod 8$ is the source's $p = 8n - 1$. -/
@[kb "dickson1923" "[unverified locator]"]
theorem two_mul_prime_eq_sum_three_sq (p : ℕ) (hp : p.Prime) (h7 : p % 8 = 7) :
    ∃ x y z : ℤ, 2 * (p : ℤ) = x ^ 2 + y ^ 2 + z ^ 2 := by
  have : ¬ ∃ a b : ℕ, 2 * p = 4 ^ a * (8 * b + 7) := not_form_of_mod _ (by omega)
  obtain ⟨x, y, z, h⟩ := three_sq_of_not_form (2 * p) this
  exact ⟨x, y, z, by exact_mod_cast h⟩

/-- (Dickson, *History* III): every odd positive
integer $n$ is $2x^2 + y^2 + z^2$ with integers $x, y, z$ (because $2n$ is a sum of three squares). -/
@[kb "dickson1923" "[unverified locator]"]
theorem odd_eq_two_sq_add_sq_add_sq (n : ℕ) (hn : Odd n) :
    ∃ x y z : ℤ, (n : ℤ) = 2 * x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨m, hm⟩ := hn
  have : ¬ ∃ a b : ℕ, 2 * n = 4 ^ a * (8 * b + 7) := not_form_of_mod _ (by omega)
  obtain ⟨u, v, w, h⟩ := three_sq_of_not_form (2 * n) this
  exact odd_rep n m u v w (by exact_mod_cast hm) (by exact_mod_cast h)

/-! ### Quaternary representation numbers -/


private abbrev W4 (m : ℤ) : Type := {x : Fin 4 → ℤ // x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = m}

private theorem finite_W4 (m : ℤ) : Finite (W4 m) := by
  have hb : ∀ x : W4 m, ∀ i, x.1 i ∈ Set.Icc (-m) m := by
    intro ⟨x, hx⟩ i
    have h0 := sq_nonneg (x 0)
    have h1 := sq_nonneg (x 1)
    have h2 := sq_nonneg (x 2)
    have h3 := sq_nonneg (x 3)
    have hi : x i ^ 2 ≤ m := by
      fin_cases i <;> simp <;> nlinarith
    have e1 := Int.le_self_sq (x i)
    have e2 := Int.le_self_sq (-x i)
    refine ⟨by nlinarith, by nlinarith⟩
  refine Finite.of_injective (fun x : W4 m => fun i => (⟨x.1 i, hb x i⟩ : Set.Icc (-m) m)) ?_
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

private def eA (m : ℤ) : {x : Fin 4 → ℤ // ∑ i, (![1, 1, 2, 2] : Fin 4 → ℤ) i * x i ^ 2 = m} ≃
    {y : W4 m // Even (y.1 2 + y.1 3)} where
  toFun x := ⟨⟨![x.1 0, x.1 1, x.1 2 + x.1 3, x.1 2 - x.1 3], by
      have := x.2
      simp [Fin.sum_univ_four] at this ⊢
      linear_combination this⟩, ⟨x.1 2, by simp⟩⟩
  invFun y := ⟨![y.1.1 0, y.1.1 1, (y.1.1 2 + y.1.1 3) / 2, (y.1.1 2 - y.1.1 3) / 2], by
      have := y.1.2
      have h := split_sq _ _ y.2
      simp [Fin.sum_univ_four]
      linear_combination this - h⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> omega
  right_inv y := by
    obtain ⟨r, hr⟩ := y.2
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> omega

private theorem key4 {m : ℤ} (hm : Odd m) (y : W4 m) :
    Even (y.1 0 + y.1 1) ↔ ¬ Even (y.1 2 + y.1 3) := by
  have h := par_sq4 (y.1 0) (y.1 1) (y.1 2) (y.1 3)
  rw [y.2] at h
  have := Int.not_even_iff_odd.2 hm
  tauto

private def eB {m : ℤ} (hm : Odd m) : {y : W4 m // ¬ Even (y.1 2 + y.1 3)} ≃
    {y : W4 m // Even (y.1 2 + y.1 3)} where
  toFun y := ⟨⟨![y.1.1 2, y.1.1 3, y.1.1 0, y.1.1 1], by
      have := y.1.2
      simp
      linarith⟩, by simpa using (key4 hm y.1).2 y.2⟩
  invFun z := ⟨⟨![z.1.1 2, z.1.1 3, z.1.1 0, z.1.1 1], by
      have := z.1.2
      simp
      linarith⟩, by
      have := (key4 hm z.1).not.2 (not_not.2 z.2)
      simpa using this⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i <;> simp

private theorem ev12 {m : ℤ} (hm : Odd m) (z : Fin 4 → ℤ)
    (hz : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + 2 * z 3 ^ 2 = m ∧ Odd (z 0)) : Even (z 1 + z 2) := by
  obtain ⟨h1, h0⟩ := hz
  have ho : Odd (z 0 ^ 2) := by
    rw [sq]; exact h0.mul h0
  have : z 1 ^ 2 + z 2 ^ 2 = m - z 0 ^ 2 - 2 * z 3 ^ 2 := by linarith
  have he : Even (z 1 ^ 2 + z 2 ^ 2) := by
    rw [this]
    exact (hm.sub_odd ho).sub (even_two_mul _)
  exact (par_sq2 _ _).1 he

private def e4 {m : ℤ} (hm : Odd m) :
    {x : Fin 4 → ℤ // ∑ i, (![1, 2, 2, 2] : Fin 4 → ℤ) i * x i ^ 2 = m} ≃
    {x : Fin 4 → ℤ // x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + 2 * x 3 ^ 2 = m ∧ Odd (x 0)} where
  toFun x := ⟨![x.1 0, x.1 1 + x.1 2, x.1 1 - x.1 2, x.1 3], by
      have := x.2
      simp [Fin.sum_univ_four] at this ⊢
      refine ⟨by linear_combination this, ?_⟩
      have h2 : x.1 0 ^ 2 = m - 2 * (x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2) := by linarith
      have : Odd (x.1 0 ^ 2) := by
        rw [h2]; exact hm.sub_even (even_two_mul _)
      rw [sq] at this
      exact (Int.odd_mul.1 this).1⟩
  invFun z := ⟨![z.1 0, (z.1 1 + z.1 2) / 2, (z.1 1 - z.1 2) / 2, z.1 3], by
      have := z.2.1
      have h := split_sq _ _ (ev12 hm z.1 z.2)
      simp [Fin.sum_univ_four]
      linear_combination this - h⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> omega
  right_inv z := by
    obtain ⟨r, hr⟩ := ev12 hm z.1 z.2
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> omega

/-- The number of representations of $m$ by the diagonal quaternary form $\sum_{i<4} a_i x_i^2$: the cardinality of
$\{x \in \mathbb Z^4 : \sum_i a_i x_i^2 = m\}$ (`Nat.card`, so $0$ if the set were infinite; for positive $a_i$ it is
finite). -/
noncomputable def repCount4 (a : Fin 4 → ℤ) (m : ℤ) : ℕ :=
  Nat.card {x : Fin 4 → ℤ // ∑ i, a i * x i ^ 2 = m}

/-- first part (Dickson, *History* III): for odd
$m$, the number of representations of $m$ as a sum of four squares is twice the number of representations by
$x^2 + y^2 + 2z^2 + 2t^2$. -/
@[kb "dickson1923" "[unverified locator]"]
theorem card_sum_four_sq_eq_two_mul (m : ℤ) (hm : Odd m) :
    repCount4 ![1, 1, 1, 1] m = 2 * repCount4 ![1, 1, 2, 2] m := by
  classical
  haveI := finite_W4 m
  have hW : repCount4 ![1, 1, 1, 1] m = Nat.card (W4 m) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [Fin.sum_univ_four]))
  have hA : repCount4 ![1, 1, 2, 2] m = Nat.card {y : W4 m // Even (y.1 2 + y.1 3)} :=
    Nat.card_congr (eA m)
  have hB : Nat.card {y : W4 m // ¬ Even (y.1 2 + y.1 3)} = Nat.card {y : W4 m // Even (y.1 2 + y.1 3)} :=
    Nat.card_congr (eB hm)
  rw [hW, hA, ← Nat.card_congr (Equiv.sumCompl (fun y : W4 m => Even (y.1 2 + y.1 3))), Nat.card_sum, hB]
  ring

/-- second part (Dickson, *History* III): for odd
$m$, the number of solutions of $m = x^2 + 2y^2 + 2z^2 + 2t^2$ equals the number of solutions of
$m = x^2 + y^2 + z^2 + 2t^2$ with $x$ odd ($x = x_0$). -/
@[kb "dickson1923" "[unverified locator]"]
theorem card_1222_eq_card_1112_odd (m : ℤ) (hm : Odd m) :
    repCount4 ![1, 2, 2, 2] m =
      Nat.card {x : Fin 4 → ℤ // x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + 2 * x 3 ^ 2 = m ∧ Odd (x 0)} := by
  exact Nat.card_congr (e4 hm)

end QuadFormsKB.Historical.Dickson
