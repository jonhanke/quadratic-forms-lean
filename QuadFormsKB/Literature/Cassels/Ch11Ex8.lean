/-
# Cassels, Chapter 11, Example 8 (p. 253): odd squares primitively represented by two forms of one genus

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Example 8, p. 253: apply the methods of the
two preceding examples (6 and 7: in a genus with two spinor genera, an odd square $m^2$ is primitively represented by
exactly one of the two forms, according to a congruence of $m$) to the squares represented primitively by
$$f = x_0^2 - 2x_1^2 + 64x_2^2 \qquad\text{and}\qquad g = (2x_0 + x_2)^2 - 2x_1^2 + 16x_2^2 .$$
The book refers to Chapter 9, Example 23 and Siegel (1951), Section 1, paragraph 7.

**Layer.** Integer-valued ternary forms `QuadForm ℤ 3` (variables $x_0, x_1, x_2$; the book's $x, y, z$), primitive
representation over $\mathbb Z$ = `primRepSet` (the greatest common divisor of the coordinates is $1$). The form $f$
is `Siegel.ex23Form` of Chapter 9, Example 23; $g$ is `ex8G`, i.e. $4x_0^2 + 4x_0x_2 + 17x_2^2 - 2x_1^2$.

**Answer (reconstructed; the book leaves it to the reader).** For odd $m$ (only $m^2$ matters, so the sign of $m$
is irrelevant):
* $f$ represents $m^2$ primitively if and only if $m \equiv \pm 1 \pmod 8$;
* $g$ represents $m^2$ primitively if and only if $m \equiv \pm 3 \pmod 8$.
So exactly one of $f, g$ does. Checked by computer search for all odd $m$ with $1 \le m \le 129$.

**Formalized.**
* `ex8_f_not_primRep` (proved): $f$ does not represent $m^2$ primitively for $m \equiv \pm 3 \pmod 8$. This is Chapter 9,
  Example 23 (`Siegel.ex23_not_primRep`), restated.
* `ex8_g_not_primRep` (proved): $g$ does not represent $m^2$ primitively for $m \equiv \pm 1 \pmod 8$.
  *Proof.* With $u = 2x_0 + x_2$, $u^2 - 2x_1^2 = (m - 4x_2)(m + 4x_2)$. Parity of the equation forces $x_2$ odd, so
  both factors are $\equiv \pm 3 \pmod 8$; a prime $p \equiv \pm 3 \pmod 8$ divides the first factor to an odd power, but
  divides $u^2 - 2x_1^2$ to an even power, so $p$ divides the second factor too, hence $p \mid m, x_2, u, x_1, x_0$,
  contradicting primitivity.
* `ex8_hessian_det_f`, `ex8_hessian_det_g`: both forms have Hessian determinant $-1024 = 8 \cdot (-128)$, i.e. the same
  determinant $-128$ (the necessary condition for the same genus; the full statement that they lie in one genus is not
  formalized here).
* `Ex8Existence` (named statement): the positive halves (explicit primitive representations). Not proved here; proved in
  `Ch11Ex8Exist.lean` (`ex8Existence_holds`, with the unconditional answer `ex8_primRep_iff'`), not by spinor genera but
  by showing that every form of the genus is equivalent to $f$ or $g$ (isotropic reduction and a finite check).
* `ex8_primRep_iff` (proved, conditional on `Ex8Existence`): the two iff statements above.

**What the positive halves need.** Both forms are indefinite with determinant $-128$, and the genus has two spinor
genera (Examples 6, 7). The local conditions hold for every odd $m$ (cf. `Siegel.ex23_local`), so by the Hasse principle
for spinor genera (Chapter 11, Theorem 1.4 and Chapter 9, Theorem 5.1 for primitive representations by a spinor genus
with the class number of a spinor genus equal to one) $m^2$ is primitively represented by *some* form of the genus;
then Examples 6, 7 (determination of the spinor genus of the representation by a congruence in $m$) say which one.
No parametric family of representations exists in elementary terms: for $m$ prime, $m \equiv 1 \pmod 8$, a primitive
representation of $m^2$ by $f$ requires $z$ with $(m - 8z)(m + 8z)$ a norm from $\mathbb Z[\sqrt 2]$, which is an
existence statement of the same depth as the local-global principle.
-/
import QuadFormsKB.Literature.Cassels.Ch9Examples3

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex8

open QuadFormsKB QuadFormsKB.Siegel

/-- The form $g = (2x_0 + x_2)^2 - 2x_1^2 + 16x_2^2 = 4x_0^2 + 4x_0x_2 + 17x_2^2 - 2x_1^2$ of Cassels' Chapter 11,
Example 8 (p. 253), in the variables $x_0, x_1, x_2$. -/
def ex8G : QuadForm ℤ 3 := QuadForm.ofUpper ![![4, 0, 4], ![0, -2, 0], ![0, 0, 17]]

/-- Helper: evaluation of $g$ over $\mathbb Z$, $g(x) = 4x_0^2 + 4x_0x_2 + 17x_2^2 - 2x_1^2$. -/
theorem eval_ex8G (x : Fin 3 → ℤ) :
    ex8G.eval x = 4 * x 0 ^ 2 + 4 * x 0 * x 2 + 17 * x 2 ^ 2 - 2 * x 1 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ex8G, QuadForm.ofUpper]
  ring

/-- Helper: the Hessian determinant of $f = x_0^2 - 2x_1^2 + 64x_2^2$ is $-1024$. -/
theorem ex8_hessian_det_f : ex23Form.hessian.det = -1024 := by
  rw [ex23Form, hessian_diag, det_diagonal, Fin.prod_univ_three]
  simp

/-- Helper: the Hessian determinant of $g$ is $-1024$, the same as that of $f$ (`ex8_hessian_det_f`); both forms
have determinant $-128$. -/
theorem ex8_hessian_det_g : ex8G.hessian.det = -1024 := by
  simp [QuadForm.hessian, ex8G, QuadForm.ofUpper, Matrix.det_fin_three]

/-- **Cassels, Ch. 11, Example 8** (p. 253), negative half for $f = x_0^2 - 2x_1^2 + 64x_2^2$: for $m \equiv \pm 3
\pmod 8$ (here `m % 8 = 3 ∨ m % 8 = 5`), $m^2$ is not represented primitively by $f$ over $\mathbb Z$. This is
Chapter 9, Example 23 (`Siegel.ex23_not_primRep`). -/
@[kb "cassels1978" "Ch. 11, Ex. 8, p. 253 (f, m ≡ ±3 mod 8)"]
theorem ex8_f_not_primRep {m : ℤ} (hm : m % 8 = 3 ∨ m % 8 = 5) : primRepSet ex23Form (m ^ 2) = ∅ :=
  ex23_not_primRep hm

/-- **Cassels, Ch. 11, Example 8** (p. 253), negative half for $g = (2x_0 + x_2)^2 - 2x_1^2 + 16x_2^2$: for
$m \equiv \pm 1 \pmod 8$ (here `m % 8 = 1 ∨ m % 8 = 7`), $m^2$ is not represented primitively by $g$ over
$\mathbb Z$. -/
@[kb "cassels1978" "Ch. 11, Ex. 8, p. 253 (g, m ≡ ±1 mod 8)"]
theorem ex8_g_not_primRep {m : ℤ} (hm : m % 8 = 1 ∨ m % 8 = 7) : primRepSet ex8G (m ^ 2) = ∅ := by
  ext x
  simp only [primRepSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hgcd hx
  rw [eval_ex8G] at hx
  -- `x₂` is odd
  have hz : x 2 % 2 = 1 := by
    by_contra hz
    have hz' : x 2 % 2 = 0 := by omega
    obtain ⟨k, hk⟩ : ∃ k, x 2 = 2 * k := ⟨x 2 / 2, by omega⟩
    have hm2 : m ^ 2 = 2 * (2 * x 0 ^ 2 + 4 * x 0 * k + 34 * k ^ 2 - x 1 ^ 2) := by
      rw [hk] at hx; linear_combination -hx
    have hodd : Odd (m ^ 2) := (Int.odd_iff.2 (by omega : m % 2 = 1)).pow
    rw [hm2] at hodd
    exact (Int.not_even_iff_odd.2 hodd) (even_two_mul _)
  set N₁ := m - 4 * x 2
  set N₂ := m + 4 * x 2
  have hprod : (2 * x 0 + x 2) ^ 2 - 2 * x 1 ^ 2 = N₁ * N₂ := by
    simp only [N₁, N₂]; linear_combination hx
  have hN₁ : N₁ % 8 = 3 ∨ N₁ % 8 = 5 := by simp only [N₁]; omega
  have hN₁0 : N₁ ≠ 0 := by intro h; rw [h] at hN₁; omega
  have hN₂0 : N₂ ≠ 0 := by intro h; simp only [N₂] at h; omega
  obtain ⟨p, hpp, hp8, hodd⟩ := exists_odd_padicValInt hN₁
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : (p : ℤ) ≠ 2 := by
    intro h
    have : p = 2 := by exact_mod_cast h
    subst this; omega
  have hnd : ¬ (p : ℤ) ∣ N₂ := by
    intro hd₂
    have hd₁ : (p : ℤ) ∣ N₁ := by
      have hv : 0 < N₁.natAbs.factorization p :=
        Nat.pos_of_ne_zero (fun h => by rw [h] at hodd; exact absurd hodd (by decide))
      exact Int.natCast_dvd.2 (Nat.dvd_of_factorization_pos (Nat.pos_iff_ne_zero.1 hv))
    have hcop : IsCoprime (p : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := (Nat.coprime_primes hpp Nat.prime_two).2 (by intro h; apply hp2; exact_mod_cast h)
      exact_mod_cast this
    have hz' : (p : ℤ) ∣ x 2 := by
      have h8 : (p : ℤ) ∣ 2 ^ 3 * x 2 := by
        have := dvd_sub hd₂ hd₁; simp only [N₁, N₂] at this; convert this using 1; ring
      exact (hcop.pow_right (n := 3)).dvd_of_dvd_mul_left h8
    have hxy := dvd_of_dvd_sq_sub_two_sq hp8 (show (p : ℤ) ∣ (2 * x 0 + x 2) ^ 2 - 2 * x 1 ^ 2 by
      rw [hprod]; exact dvd_mul_of_dvd_left hd₁ _)
    have hx0 : (p : ℤ) ∣ x 0 := by
      have : (p : ℤ) ∣ 2 * x 0 := by
        have := dvd_sub hxy.1 hz'; convert this using 1; ring
      exact hcop.dvd_of_dvd_mul_left this
    have : (p : ℤ) ∣ Finset.univ.gcd x := by
      refine Finset.dvd_gcd fun i _ => ?_
      fin_cases i
      · exact hx0
      · exact hxy.2
      · exact hz'
    rw [hgcd] at this
    exact hpp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  have hev := even_padicValInt_sub hp8 _ (2 * x 0 + x 2) (x 1) rfl
    (by rw [hprod]; exact mul_ne_zero hN₁0 hN₂0)
  rw [hprod, padicValInt.mul hN₁0 hN₂0, padicValInt.eq_zero_of_not_dvd hnd, add_zero, padicValInt,
    ← Nat.factorization_def _ hpp] at hev
  exact (Nat.not_even_iff_odd.2 hodd) hev

/-- **Named statement: the positive halves of Cassels, Ch. 11, Example 8** (p. 253). For every integer $m$:
if $m \equiv \pm 1 \pmod 8$ then $m^2$ is primitively represented by $f = x_0^2 - 2x_1^2 + 64x_2^2$, and if
$m \equiv \pm 3 \pmod 8$ then $m^2$ is primitively represented by $g = (2x_0 + x_2)^2 - 2x_1^2 + 16x_2^2$.
Fields: `f_rep` and `g_rep`. *Proved* in `Ch11Ex8Exist.lean` (`ex8Existence_holds`). Originally noted: proving it needs the spinor genus theory of Examples 6 and 7 (the genus of $f$ and $g$ has
two spinor genera and $m^2$ is primitively represented over every $\mathbb Z_p$); verified numerically for odd
$m \le 129$. -/
structure Ex8Existence : Prop where
  /-- $m \equiv \pm 1 \pmod 8$ implies that $f$ represents $m^2$ primitively. -/
  f_rep : ∀ m : ℤ, (m % 8 = 1 ∨ m % 8 = 7) → (primRepSet ex23Form (m ^ 2)).Nonempty
  /-- $m \equiv \pm 3 \pmod 8$ implies that $g$ represents $m^2$ primitively. -/
  g_rep : ∀ m : ℤ, (m % 8 = 3 ∨ m % 8 = 5) → (primRepSet ex8G (m ^ 2)).Nonempty

/-- **Cassels, Ch. 11, Example 8** (p. 253), the full answer, conditional on the named statement `Ex8Existence`
(the positive halves): for odd $m$, $m^2$ is primitively represented by $f$ if and only if $m \equiv \pm 1 \pmod 8$,
and by $g$ if and only if $m \equiv \pm 3 \pmod 8$. In particular exactly one of $f, g$ represents $m^2$ primitively. -/
@[kb "cassels1978" "Ch. 11, Ex. 8, p. 253 (answer, given positive halves)"]
theorem ex8_primRep_iff (h : Ex8Existence) (m : ℤ) (hodd : m % 2 = 1) :
    ((primRepSet ex23Form (m ^ 2)).Nonempty ↔ (m % 8 = 1 ∨ m % 8 = 7)) ∧
      ((primRepSet ex8G (m ^ 2)).Nonempty ↔ (m % 8 = 3 ∨ m % 8 = 5)) := by
  have h8 : m % 8 = 1 ∨ m % 8 = 7 ∨ m % 8 = 3 ∨ m % 8 = 5 := by omega
  constructor
  · constructor
    · intro hne
      by_contra hc
      have := ex8_f_not_primRep (m := m) (by omega)
      rw [this] at hne
      exact Set.not_nonempty_empty hne
    · exact h.f_rep m
  · constructor
    · intro hne
      by_contra hc
      have := ex8_g_not_primRep (m := m) (by omega)
      rw [this] at hne
      exact Set.not_nonempty_empty hne
    · exact h.g_rep m

end QuadFormsKB.Cassels.Ch11Ex8
