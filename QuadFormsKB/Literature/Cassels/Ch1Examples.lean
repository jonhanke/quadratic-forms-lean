/-
# Cassels, Chapter 1, §1: the introductory examples and the properties of the $p$-adic valuation

Small items of Cassels, *Rational Quadratic Forms*, Ch. 1, §1, pp. 1-4, mostly running text: Pythagorean triples
(1.1)-(1.2), clearing denominators in a homogeneous equation, the Fermat-Lagrange claim about (1.3), the
non-existence of integral solutions of (1.7) and (1.9) by reduction modulo $4$ and $3$ ((1.8)), and the properties
(i)-(iii) and the definition (1.15) of the $p$-adic valuation (Mathlib's `padicNorm`).

Indices are $0$-based ($x_0, \dots, x_{n-1}$; Cassels' $x_1, \dots, x_n$). The $p$-adic valuation is written
$|a|_p$ in Cassels; here `padicNorm p a`.
-/
import QuadFormsKB.Literature.Cassels.Ch1Sec1
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.Padics.PadicNorm

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Ch1

/-! ### Pythagorean triples (1.1)-(1.2) -/

/-- **(1.1)** (Cassels, Ch. 1, §1, p. 1): integral solutions of $x^2 + y^2 - z^2 = 0$ are the right-angled triangles
with integral sides, i.e. Pythagorean triples (Mathlib's `PythagoreanTriple x y z`: $x \cdot x + y \cdot y = z \cdot z$). -/
@[kb "cassels1978" "Ch. 1, §1, (1.1), p. 1"]
theorem sq_add_sq_sub_sq_eq_zero_iff (x y z : ℤ) : x ^ 2 + y ^ 2 - z ^ 2 = 0 ↔ PythagoreanTriple x y z := by
  unfold PythagoreanTriple
  constructor <;> intro h <;> linarith

/-- **(1.2)** (Cassels, Ch. 1, §1, p. 1): $x^2 + y^2 - 2z^2 = 0$ says that $x^2, z^2, y^2$ are in arithmetic
progression: $z^2 - x^2 = y^2 - z^2$. -/
@[kb "cassels1978" "Ch. 1, §1, (1.2), p. 1"]
theorem sq_add_sq_sub_two_sq_eq_zero_iff (x y z : ℤ) :
    x ^ 2 + y ^ 2 - 2 * z ^ 2 = 0 ↔ z ^ 2 - x ^ 2 = y ^ 2 - z ^ 2 := by
  constructor <;> intro h <;> linarith

/-! ### Clearing denominators in homogeneous equations -/

/-- **Clearing denominators** (Cassels, Ch. 1, §1, p. 1, running text): a rational vector $v \in \mathbb Q^n$ can be
multiplied by a non-zero integer $l$ (the product of the denominators) to give an integral vector $w$,
$w_i = l v_i$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 1 (a rational solution of a homogeneous equation can be scaled to an integral one)"]
theorem exists_int_smul_of_rat {n : ℕ} (v : Fin n → ℚ) :
    ∃ (l : ℤ) (w : Fin n → ℤ), l ≠ 0 ∧ ∀ i, (w i : ℚ) = l * v i := by
  set D : ℕ := ∏ i, (v i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (v i).den_pos
  refine ⟨D, fun i => (v i).num * ((D / (v i).den : ℕ) : ℤ), by exact_mod_cast hDpos.ne', ?_⟩
  intro i
  obtain ⟨k, hk⟩ : (v i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hk' : D / (v i).den = k := by
    rw [hk]; exact Nat.mul_div_cancel_left _ (v i).den_pos
  simp only [hk']
  push_cast
  have h1 : ((v i).den : ℚ) * v i = (v i).num := Rat.den_mul_eq_num _
  rw [hk]
  push_cast
  calc ((v i).num : ℚ) * k = ((v i).den * v i) * k := by rw [h1]
    _ = _ := by ring

/-- **A non-trivial rational zero of an integral form gives a non-trivial integral zero** (Cassels, Ch. 1, §1, p. 1,
running text: "if the equation is homogeneous, a rational solution $(a, b, c)$ can be multiplied by a common
denominator to give an integral solution"). For $Q$ an integral form in $n$ variables and $\vec v \in \mathbb Q^n$,
$\vec v \ne 0$, with $Q(\vec v) = 0$ there is $\vec w \in \mathbb Z^n$, $\vec w \ne 0$, with $Q(\vec w) = 0$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 1 (rational zero of a form gives an integral zero)"]
theorem exists_int_zero_of_rat_zero {n : ℕ} (Q : QuadForm ℤ n) {v : Fin n → ℚ} (hv : v ≠ 0)
    (h : Q.evalIn ℚ v = 0) : ∃ w : Fin n → ℤ, w ≠ 0 ∧ Q.eval w = 0 := by
  obtain ⟨l, w, hl, hw⟩ := exists_int_smul_of_rat v
  have hw' : (fun i => (w i : ℚ)) = fun i => (l : ℚ) * v i := funext hw
  have hscale : Q.evalIn ℚ (fun i => (l : ℚ) * v i) = (l : ℚ) ^ 2 * Q.evalIn ℚ v := by
    simp only [QuadForm.evalIn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hcast : Q.evalIn ℚ (fun i => (w i : ℚ)) = ((Q.eval w : ℤ) : ℚ) := by
    simp [QuadForm.eval, QuadForm.evalIn, apply_ite (Int.cast : ℤ → ℚ)]
  refine ⟨w, ?_, ?_⟩
  · intro h0
    apply hv
    funext i
    have h2 : (w i : ℚ) = 0 := by simp [h0]
    rw [hw i] at h2
    have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
    simpa [hl'] using h2
  · rw [hw', hscale, h, mul_zero] at hcast
    exact_mod_cast hcast.symm

/-! ### Fermat's claim for (1.3) -/

/-- **Necessity of "$C$ not a square"** (Cassels, Ch. 1, §1, p. 2, footnote): if $C = c^2$ with $c \ne 0$, then
$x^2 - Cy^2 = (x + cy)(x - cy) = 1$ forces $x + cy = x - cy = \pm 1$, hence $y = 0$. So for a square $C$ the
equation (1.3) $x^2 - Cy^2 = 1$ has only the trivial solutions $y = 0$, and the hypothesis "$C$ not a square" in the
Fermat-Lagrange theorem cannot be dropped. -/
@[kb "cassels1978" "Ch. 1, §1, p. 2 (footnote: C a square, then y = 0)"]
theorem eq_zero_of_sq_sub_sq_mul_sq_eq_one {c : ℤ} (hc : c ≠ 0) {x y : ℤ} (h : x ^ 2 - c ^ 2 * y ^ 2 = 1) :
    y = 0 := by
  have h1 : (x + c * y) * (x - c * y) = 1 := by linear_combination h
  have h2 : c * y = 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
  exact (mul_eq_zero.mp h2).resolve_left hc

/-- **Fermat's claim, proved by Lagrange** (Cassels, Ch. 1, §1, (1.3), pp. 1-2): for an integer $C > 0$ that is not a
square, $x^2 - Cy^2 = 1$ has an integral solution with $y \ne 0$. Comparison lemma: this is Mathlib's
`Pell.exists_of_not_isSquare`. -/
@[kb "cassels1978" "Ch. 1, §1, (1.3), pp. 1–2 (Fermat's claim, Lagrange's proof)"]
theorem exists_pell_solution {C : ℤ} (hC : 0 < C) (hnsq : ¬ IsSquare C) :
    ∃ x y : ℤ, x ^ 2 - C * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare hC hnsq

/-! ### (1.7)-(1.9): $x^2 + y^2 = -3$ and $x^2 + y^2 = 21$ -/

/-- **(1.7), reason** (Cassels, Ch. 1, §1, p. 2): $x^2 + y^2 = -3$ has no real solution. -/
@[kb "cassels1978" "Ch. 1, §1, (1.7), p. 2 (no real solution)"]
theorem not_exists_real_sq_add_sq_eq_neg_three : ¬ ∃ x y : ℝ, x ^ 2 + y ^ 2 = -3 := by
  rintro ⟨x, y, h⟩
  nlinarith [sq_nonneg x, sq_nonneg y]

/-- **(1.7)** (Cassels, Ch. 1, §1, p. 2): $x^2 + y^2 = -3$ has no integral solution (since it has no real one). -/
@[kb "cassels1978" "Ch. 1, §1, (1.7), p. 2"]
theorem not_exists_int_sq_add_sq_eq_neg_three : ¬ ∃ x y : ℤ, x ^ 2 + y ^ 2 = -3 := by
  rintro ⟨x, y, h⟩
  exact not_exists_real_sq_add_sq_eq_neg_three ⟨x, y, by exact_mod_cast h⟩

/-- **(1.8)** (Cassels, Ch. 1, §1, p. 2): the square of an integer is $\equiv 0$ or $1 \pmod 4$. -/
@[kb "cassels1978" "Ch. 1, §1, (1.8), p. 2"]
theorem sq_emod_four (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases h with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- **A sum of two squares is not $\equiv 3 \pmod 4$** (Cassels, Ch. 1, §1, p. 2, after (1.8)): if $a = x^2 + y^2$
with $x, y, a \in \mathbb Z$, then $a \not\equiv 3 \pmod 4$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 2 (a = x² + y² is not ≡ 3 mod 4)"]
theorem not_modEq_three_of_sq_add_sq {a x y : ℤ} (h : a = x ^ 2 + y ^ 2) : ¬ a ≡ 3 [ZMOD 4] := by
  intro h3
  have hx := sq_emod_four x
  have hy := sq_emod_four y
  unfold Int.ModEq at h3
  subst h
  generalize x ^ 2 = X at *
  generalize y ^ 2 = Y at *
  omega

/-- **The prime $3$** (Cassels, Ch. 1, §1, pp. 2-3, argument for (1.9)): $3 \mid x^2 + y^2$ forces $3 \mid x$ and
$3 \mid y$. -/
@[kb "cassels1978" "Ch. 1, §1, (1.9), pp. 2–3 (3 ∣ x² + y² forces 3 ∣ x and 3 ∣ y)"]
theorem three_dvd_of_three_dvd_sq_add_sq {x y : ℤ} (h : 3 ∣ x ^ 2 + y ^ 2) : 3 ∣ x ∧ 3 ∣ y := by
  have h3 : (x ^ 2 + y ^ 2) % 3 = 0 := Int.emod_eq_zero_of_dvd h
  have hx : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  have hy : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
    simp [pow_two, Int.add_emod, Int.mul_emod, hx, hy] at h3 <;> omega

/-- **(1.9)** (Cassels, Ch. 1, §1, pp. 2-3): $x^2 + y^2 = 21$ has no integral solution, although $21 \equiv 1 \pmod 4$
(so the obstruction (1.8) does not apply). Proof as in the book: $x^2 + y^2 \equiv 0 \pmod 3$ forces $3 \mid x$ and
$3 \mid y$, so $9 \mid 21$, a contradiction. -/
@[kb "cassels1978" "Ch. 1, §1, (1.9), pp. 2–3"]
theorem not_exists_int_sq_add_sq_eq_21 : ¬ ∃ x y : ℤ, x ^ 2 + y ^ 2 = 21 := by
  rintro ⟨x, y, h⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := three_dvd_of_three_dvd_sq_add_sq (x := x) (y := y) ⟨7, by omega⟩
  subst ha hb
  have : 9 * (a ^ 2 + b ^ 2) = 21 := by linear_combination h
  omega

/-! ### The $p$-adic valuation: properties (i)-(iii) and the definition (1.15) -/

section PAdic

variable (p : ℕ) [Fact p.Prime]

/-- **Property (i), non-negativity** (Cassels, Ch. 1, §1, p. 4): $|a|_p \ge 0$. Comparison lemma: `padicNorm.nonneg`. -/
@[kb "cassels1978" "Ch. 1, §1, p. 4, (i)"]
theorem padicNorm_nonneg (a : ℚ) : 0 ≤ padicNorm p a := padicNorm.nonneg a

/-- **Property (i), definiteness** (Cassels, Ch. 1, §1, p. 4): $|a|_p = 0$ if and only if $a = 0$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 4, (i)"]
theorem padicNorm_eq_zero_iff (a : ℚ) : padicNorm p a = 0 ↔ a = 0 :=
  ⟨padicNorm.zero_of_padicNorm_eq_zero, fun h => by rw [h]; exact padicNorm.zero⟩

/-- **Property (ii), multiplicativity** (Cassels, Ch. 1, §1, p. 4): $|ab|_p = |a|_p |b|_p$. Comparison lemma:
`padicNorm.mul`. -/
@[kb "cassels1978" "Ch. 1, §1, p. 4, (ii)"]
theorem padicNorm_mul (a b : ℚ) : padicNorm p (a * b) = padicNorm p a * padicNorm p b := padicNorm.mul a b

/-- **Property (iii), the ultrametric inequality** (Cassels, Ch. 1, §1, p. 4): $|a + b|_p \le \max(|a|_p, |b|_p)$.
Comparison lemma: `padicNorm.nonarchimedean`. -/
@[kb "cassels1978" "Ch. 1, §1, p. 4, (iii)"]
theorem padicNorm_add_le_max (a b : ℚ) : padicNorm p (a + b) ≤ max (padicNorm p a) (padicNorm p b) :=
  padicNorm.nonarchimedean

end PAdic

/-- **(iii) implies the triangle inequality (iii)\*** (Cassels, Ch. 1, §1, p. 4: "(iii) trivially implies the triangle
inequality (iii)\*"): a non-negative function $f$ on $\mathbb Q$ with $f(a + b) \le \max(f(a), f(b))$ satisfies
$f(a + b) \le f(a) + f(b)$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 4, (iii) implies (iii)*"]
theorem triangle_of_ultrametric (f : ℚ → ℚ) (hnn : ∀ a, 0 ≤ f a)
    (h : ∀ a b, f (a + b) ≤ max (f a) (f b)) (a b : ℚ) : f (a + b) ≤ f a + f b := by
  refine (h a b).trans ?_
  rcases max_choice (f a) (f b) with e | e <;> rw [e] <;> linarith [hnn a, hnn b]

/-- **The triangle inequality (iii)\* for $|\cdot|_p$** (Cassels, Ch. 1, §1, p. 4): $|a + b|_p \le |a|_p + |b|_p$,
here deduced from (iii) by `triangle_of_ultrametric` (Mathlib also has it as `padicNorm.triangle_ineq`). -/
@[kb "cassels1978" "Ch. 1, §1, p. 4, (iii)*"]
theorem padicNorm_triangle (p : ℕ) [Fact p.Prime] (a b : ℚ) :
    padicNorm p (a + b) ≤ padicNorm p a + padicNorm p b :=
  triangle_of_ultrametric (padicNorm p) (padicNorm.nonneg) (fun a b => padicNorm.nonarchimedean) a b

/-- **The ordinary absolute value satisfies (i), (ii), (iii)\*** (Cassels, Ch. 1, §1, p. 4): on $\mathbb Q$,
$|a| \ge 0$ with equality iff $a = 0$; $|ab| = |a||b|$; $|a + b| \le |a| + |b|$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 4 (the ordinary absolute value satisfies (i), (ii), (iii)*)"]
theorem abs_satisfies_i_ii_iii_star :
    (∀ a : ℚ, 0 ≤ |a| ∧ (|a| = 0 ↔ a = 0)) ∧ (∀ a b : ℚ, |a * b| = |a| * |b|) ∧
      (∀ a b : ℚ, |a + b| ≤ |a| + |b|) :=
  ⟨fun a => ⟨abs_nonneg a, abs_eq_zero⟩, abs_mul, abs_add_le⟩

/-- **The ordinary absolute value does not satisfy (iii)** (Cassels, Ch. 1, §1, p. 4): $|1 + 1| = 2 >
\max(|1|, |1|) = 1$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 4 (the ordinary absolute value does not satisfy (iii))"]
theorem abs_not_ultrametric : ¬ ∀ a b : ℚ, |a + b| ≤ max |a| |b| := by
  intro h
  have := h 1 1
  norm_num at this

/-- The decomposition in (1.15) determines $|a|_p$: if $a = p^\alpha u / v$ with $p \nmid u$, $p \nmid v$, then
$|a|_p = p^{-\alpha}$. -/
theorem padicNorm_of_decomp (p : ℕ) [hp : Fact p.Prime] {α : ℤ} {u v : ℤ} (hu : ¬ (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) {a : ℚ} (ha : a = (p : ℚ) ^ α * u / v) : padicNorm p a = (p : ℚ) ^ (-α) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpα : padicNorm p ((p : ℚ) ^ α) = (p : ℚ) ^ (-α) := by
    rw [padicNorm.eq_zpow_of_nonzero (zpow_ne_zero _ hp0), padicValRat.zpow, padicValRat.self hp.out.one_lt]
    simp
  rw [ha, padicNorm.div, padicNorm.mul, hpα, (padicNorm.int_eq_one_iff (p := p) u).mpr hu,
    (padicNorm.int_eq_one_iff (p := p) v).mpr hv]
  simp

/-- **Definition (1.15) of the $p$-adic valuation** (Cassels, Ch. 1, §1, p. 4): every rational $a \ne 0$ can be
written $a = p^\alpha u / v$ with integers $u, v$ prime to $p$ and $\alpha \in \mathbb Z$; $\alpha$ is unique, and
$|a|_p = p^{-\alpha}$ (Mathlib's `padicNorm`, $\alpha$ = `padicValRat`). -/
@[kb "cassels1978" "Ch. 1, §1, (1.15), p. 4"]
theorem padicNorm_def (p : ℕ) [hp : Fact p.Prime] {a : ℚ} (ha : a ≠ 0) :
    ∃ (α : ℤ) (u v : ℤ), ¬ (p : ℤ) ∣ u ∧ ¬ (p : ℤ) ∣ v ∧ a = (p : ℚ) ^ α * u / v ∧
      padicNorm p a = (p : ℚ) ^ (-α) ∧
      ∀ (α' : ℤ) (u' v' : ℤ), ¬ (p : ℤ) ∣ u' → ¬ (p : ℤ) ∣ v' → a = (p : ℚ) ^ α' * u' / v' → α' = α := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have key : ∀ z : ℤ, z ≠ 0 → ∃ (e : ℕ) (u : ℤ), ¬ (p : ℤ) ∣ u ∧ z = (p : ℤ) ^ e * u := by
    intro z hz
    obtain ⟨e, m, hm, hzm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hz) p hp.out.ne_one
    have hm' : ¬ (p : ℤ) ∣ (m : ℤ) := fun h => hm (Int.natCast_dvd_natCast.mp h)
    rcases Int.natAbs_eq z with h | h
    · exact ⟨e, m, hm', by rw [h, hzm]; push_cast; ring⟩
    · refine ⟨e, -m, fun h' => hm' (dvd_neg.mp h'), ?_⟩
      rw [h, hzm]; push_cast; ring
  have hnum : a.num ≠ 0 := Rat.num_ne_zero.mpr ha
  have hden : (a.den : ℤ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  obtain ⟨e1, u1, hu1, h1⟩ := key a.num hnum
  obtain ⟨e2, u2, hu2, h2⟩ := key a.den hden
  have hu2z : (u2 : ℚ) ≠ 0 := by
    intro h0
    apply hu2
    have : u2 = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  have hdec : a = (p : ℚ) ^ ((e1 : ℤ) - e2) * u1 / u2 := by
    have e : a = (a.num : ℚ) / (a.den : ℚ) := (Rat.num_div_den a).symm
    have h2' : ((a.den : ℤ) : ℚ) = (p : ℚ) ^ e2 * u2 := by exact_mod_cast h2
    have h1' : (a.num : ℚ) = (p : ℚ) ^ e1 * u1 := by exact_mod_cast h1
    rw [e, show ((a.den : ℕ) : ℚ) = ((a.den : ℤ) : ℚ) by norm_cast, h2', h1', zpow_sub₀ hp0]
    simp only [zpow_natCast]
    field_simp
  have hnorm := padicNorm_of_decomp p hu1 hu2 hdec
  refine ⟨(e1 : ℤ) - e2, u1, u2, hu1, hu2, hdec, hnorm, ?_⟩
  intro α' u' v' hu' hv' h'
  have := padicNorm_of_decomp p hu' hv' h'
  rw [hnorm] at this
  have hp1 : 1 < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  have := zpow_right_injective₀ (by linarith : (0 : ℚ) < p) (by linarith : (p : ℚ) ≠ 1) this
  omega

end QuadFormsKB.Cassels.Ch1
