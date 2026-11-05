/-
# Conway–Sloane 1988, §8, Table 6: entries $s = 1$ for $d = 7, 9, 11, 18, 19, 25$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, Table 6, p. 270.

The column $s = 1$ of Table 6 is $\zeta_{-d}(1)\sqrt d/\pi$, where $\zeta_{-d}(1)$ is the value at $s = 1$ of the analytic
continuation `LD` (the sum of the conditionally convergent series $\sum_m\chi_{-d}(m)/m$). By (10),
$\zeta_{-d}(1) = L(1, \psi)\prod_{p \mid 4d}(1 - \psi(p)/p)$, and Dirichlet's class number formula
(`Binary.classNumberFormula_neg`) gives $L(1, \psi) = 2\pi h/(w\sqrt{k_1})$. This file treats the rows whose class
number is $1$: $d = 7, 11, 19$ ($h(\mathbb Q(\sqrt{-d})) = 1$), and $d = 9, 18, 25$, where $-d = f^2 D_0$ with
$D_0 = -1, -2, -1$ already treated in `Table6.lean` (only the Euler factor at the primes dividing $f$ changes).

**Proves**
* `isPrincipalIdealRing_of_two_inert`: for a fundamental discriminant $-19 \le D < 0$ with $D \equiv 5 \pmod 8$,
  $\mathcal O_{\mathbb Q(\sqrt D)}$ is a principal ideal ring: the Minkowski bound $\frac2\pi\sqrt{\lvert D\rvert}$ is
  $< 3$, and an ideal of norm $2$ would give a ring $\mathcal O/I$ with two elements in which
  $\theta = \frac{1 + \sqrt D}2$ satisfies $\theta^2 - \theta - \frac{D-1}4 = 0$ with $\frac{D-1}4$ odd, impossible.
  Hence $h(\mathbb Q(\sqrt{-11})) = h(\mathbb Q(\sqrt{-19})) = 1$ (`classNumber_QField_neg_eleven`, `…_neg_nineteen`);
  $h(\mathbb Q(\sqrt{-7})) = 1$ by Mathlib's $\lvert\mathrm{disc}\rvert < \pi^2$ criterion.
* `LFunction_kronecker_one_of_classNumber_one`: $L(1, \psi) = \pi/\sqrt{\lvert D\rvert}$ when $h = 1$ and $D < -4$.
* `zetaD_neg_seven_one`, `zetaD_neg_eleven_one`, `zetaD_neg_nineteen_one`, `zetaD_neg_nine_one`,
  `zetaD_neg_eighteen_one`, `zetaD_neg_twentyfive_one`: the values $\frac{\pi}{2\sqrt7}$, $\frac{3\pi}{2\sqrt{11}}$,
  $\frac{3\pi}{2\sqrt{19}}$, $\frac\pi3$, $\frac{\pi}{3\sqrt2}$, $\frac\pi5$.
* `table6_d_1` for $d = 7, 9, 11, 18, 19, 25$: the printed entries $\frac12, 1, \frac32, 1, \frac32, 1$.

The remaining entries $s = 1$ ($d = 5, 6, 10, 13, 14, 15, 17, 21, 22, 23$) need class numbers $h > 1$; they are
proved in `Table6OneMore.lean` (class numbers by counting reduced forms).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6RowsA
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6RowsB
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6RowsC

namespace QuadFormsKB.ConwaySloane.Mass

open Complex Finset QuadFormsKB.Binary
open scoped Real

/-! ### Class number one -/

/-- In a ring with exactly two elements every element is $0$ or $1$, and $0 \ne 1$. -/
theorem eq_zero_or_one_of_card_two {R : Type*} [Ring R] [Fintype R] (h : Fintype.card R = 2) (x : R) :
    ((0 : R) ≠ 1) ∧ (x = 0 ∨ x = 1) := by
  classical
  have h01 : (0 : R) ≠ 1 := by
    intro h01
    have : Subsingleton R := subsingleton_of_zero_eq_one h01
    have := Fintype.card_le_one_iff_subsingleton.mpr this
    omega
  refine ⟨h01, ?_⟩
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  by_cases hx1 : x = 1
  · exact Or.inr hx1
  exfalso
  have h3 : ({0, 1, x} : Finset R).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, Ne.symm hx0]), Finset.card_pair (Ne.symm hx1)]
  have := Finset.card_le_univ ({0, 1, x} : Finset R)
  omega

open NumberField in
/-- **Class number one when $2$ is inert and the Minkowski bound is $< 3$**: for a fundamental discriminant $D$ with
$-19 \le D < 0$ and $D \equiv 5 \pmod 8$ (i.e. $D = -3, -11, -19$), $\mathcal O_{\mathbb Q(\sqrt D)}$ is a principal ideal
ring. Every ideal class contains an ideal of norm at most $\frac2\pi\sqrt{\lvert D\rvert} < 3$; norm $1$ is the unit ideal,
and an ideal $I$ of norm $2$ is impossible: in the two-element ring $\mathcal O/I$ the image $t$ of
$\theta = \frac{1+\sqrt D}2$ would satisfy $t^2 - t - \frac{D-1}4 = 0$ with $\frac{D-1}4$ odd and $2 = 0$, i.e.
$t^2 - t = 1$, while $t \in \{0, 1\}$. -/
theorem isPrincipalIdealRing_of_two_inert (D : ℤ) [IsQuadDisc D] (hD : D < 0) (h8 : D % 8 = 5) (hb : -19 ≤ D) :
    IsPrincipalIdealRing (𝓞 (QField D)) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI => ?_)
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg hD] at hI
  set J : Ideal (𝓞 (QField D)) := (I : Ideal (𝓞 (QField D))) with hJ
  have hlt : Ideal.absNorm J < 3 := by
    have hπ := Real.pi_gt_three
    have habs : |(D : ℝ)| ≤ 19 := by
      have hD' : (D : ℝ) < 0 := by exact_mod_cast hD
      have hb' : (-19 : ℝ) ≤ D := by exact_mod_cast hb
      rw [abs_of_neg hD']
      linarith
    have hs : Real.sqrt |(D : ℝ)| < 9 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    have h3 : (4 / π) ^ 1 * ((Nat.factorial 2 : ℝ) / (2 : ℝ) ^ 2 * Real.sqrt |(D : ℝ)|) < 3 := by
      norm_num [Nat.factorial]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg |(D : ℝ)|]
    have : ((Ideal.absNorm J : ℕ) : ℝ) < 3 := lt_of_le_of_lt (by exact_mod_cast hI) h3
    exact_mod_cast this
  have h0 : Ideal.absNorm J ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact nonZeroDivisors.coe_ne_zero I
  have hcases : Ideal.absNorm J = 1 ∨ Ideal.absNorm J = 2 := by omega
  rcases hcases with h1 | h2
  · rw [Ideal.absNorm_eq_one_iff] at h1
    rw [h1]
    exact ⟨⟨1, by simp⟩⟩
  · exfalso
    have hcard : Nat.card (𝓞 (QField D) ⧸ J) = 2 := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h2]
    have : Finite (𝓞 (QField D) ⧸ J) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    let := Fintype.ofFinite (𝓞 (QField D) ⧸ J)
    have hc : Fintype.card (𝓞 (QField D) ⧸ J) = 2 := by rw [Fintype.card_eq_nat_card, hcard]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, qa D = 2 * k + 1 := ⟨(D / 4 - 1) / 2, by simp only [qa]; omega⟩
    have hb1 : qb D = 1 := by simp only [qb]; omega
    set t := Ideal.Quotient.mk J (theta D) with ht
    have hθ : t ^ 2 - t - (2 * (k : 𝓞 (QField D) ⧸ J) + 1) = 0 := by
      have h := aeval_theta (D := D)
      simp only [qpoly, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_pow, hk, hb1] at h
      have h' := congrArg (Ideal.Quotient.mk J) h
      simp only [map_sub, map_mul, map_pow, map_zero, map_add, map_one, algebraMap_int_eq,
        Int.coe_castRingHom, map_intCast, map_ofNat] at h'
      rw [ht]
      linear_combination h'
    obtain ⟨h01, ht01⟩ := eq_zero_or_one_of_card_two hc t
    have h2' : (2 : 𝓞 (QField D) ⧸ J) = 0 := by
      rcases (eq_zero_or_one_of_card_two hc (2 : 𝓞 (QField D) ⧸ J)).2 with h | h
      · exact h
      · exfalso; apply h01; linear_combination -h
    apply h01
    rcases ht01 with h | h <;> rw [h] at hθ <;> linear_combination hθ + (k : 𝓞 (QField D) ⧸ J) * h2'

instance isPrincipalIdealRing_QField_neg_eleven : IsPrincipalIdealRing (NumberField.RingOfIntegers (QField (-11))) :=
  isPrincipalIdealRing_of_two_inert (-11) (by norm_num) (by norm_num) (by norm_num)

instance isPrincipalIdealRing_QField_neg_nineteen :
    IsPrincipalIdealRing (NumberField.RingOfIntegers (QField (-19))) :=
  isPrincipalIdealRing_of_two_inert (-19) (by norm_num) (by norm_num) (by norm_num)

open NumberField in
instance isPrincipalIdealRing_QField_neg_seven : IsPrincipalIdealRing (𝓞 (QField (-7))) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg (by norm_num)]
  have hπ := Real.pi_gt_d2
  norm_num [Nat.factorial]
  nlinarith

/-- $h(\mathbb Q(\sqrt{-7})) = 1$. -/
theorem classNumber_QField_neg_seven : NumberField.classNumber (QField (-7)) = 1 :=
  NumberField.classNumber_eq_one_iff.2 inferInstance

/-- $h(\mathbb Q(\sqrt{-11})) = 1$. -/
theorem classNumber_QField_neg_eleven : NumberField.classNumber (QField (-11)) = 1 :=
  NumberField.classNumber_eq_one_iff.2 inferInstance

/-- $h(\mathbb Q(\sqrt{-19})) = 1$. -/
theorem classNumber_QField_neg_nineteen : NumberField.classNumber (QField (-19)) = 1 :=
  NumberField.classNumber_eq_one_iff.2 inferInstance

/-! ### $L(1, \psi)$ and $\zeta_{-d}(1)$ -/

/-- **$L(1, \psi) = \pi/\sqrt{\lvert D\rvert}$** for the Kronecker character of a fundamental discriminant $D < -4$ with
class number $1$ (class number formula, $w = 2$). -/
theorem LFunction_kronecker_one_of_classNumber_one (D : ℤ) [IsQuadDisc D] (hD : D < -4)
    (h1 : NumberField.classNumber (QField D) = 1) :
    (kroneckerChar D).LFunction 1 = ((π / Real.sqrt |(D : ℝ)| : ℝ) : ℂ) := by
  have h := classNumberFormula_neg (D := D) (by omega)
  have h3 : D ≠ -3 := by omega
  have h4 : D ≠ -4 := by omega
  rw [h1, torsionOrder_of_neg (by omega)] at h
  simp only [h3, h4, ↓reduceIte] at h
  rw [h]
  congr 1
  have : Real.sqrt |(D : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast (show D ≠ 0 by omega)))).ne'
  push_cast
  field_simp

/-- A character which takes a value $\ne 1$ at a unit is not the trivial character. -/
theorem ne_one_of_apply {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ℕ) (ha : IsUnit (a : ZMod N))
    (h : χ a ≠ 1) : χ ≠ 1 := by
  rintro rfl
  exact h (MulChar.one_apply ha)

/-- $\zeta_{-d}(1) = L(1,\psi)\,E$ from (10), for a nontrivial $\psi$ and an Euler factor $E$ at $s = 1$ given as a rational
number, when $L(1, \psi) = \ell$ is real. -/
theorem zetaD_one_of_LFunction {D : ℤ} (hD : D ≠ 0) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hdvd : N ∣ 4 * D.natAbs)
    (hval : ∀ m : ℕ, (chiD D m : ℂ) = DirichletCharacter.changeLevel hdvd χ (m : ZMod (4 * D.natAbs)))
    (hne : χ ≠ 1) (ℓ : ℝ) (hℓ : χ.LFunction 1 = (ℓ : ℂ)) (E : ℚ)
    (hE : ∏ p ∈ (4 * D.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) = (E : ℂ)) :
    zetaD D 1 = ℓ * E := by
  rw [Nat.cast_one] at hE
  rw [zetaD_eq hD, Complex.ofReal_one, LD_eq_LFunction_mul hD χ hdvd hval (Or.inl hne), hℓ, hE,
    show ((E : ℚ) : ℂ) = ((E : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- $\zeta_D(1) = (E/E')\,\zeta_{D'}(1)$ when $\chi_D$ and $\chi_{D'}$ come from the same nontrivial primitive character
$\psi$ by (10), with Euler factors $E$, $E' \ne 0$ at $s = 1$ (no knowledge of $L(1, \psi)$ is needed). -/
theorem zetaD_one_of_zetaD_one {D D' : ℤ} (hD : D ≠ 0) (hD' : D' ≠ 0) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hdvd : N ∣ 4 * D.natAbs) (hdvd' : N ∣ 4 * D'.natAbs)
    (hval : ∀ m : ℕ, (chiD D m : ℂ) = DirichletCharacter.changeLevel hdvd χ (m : ZMod (4 * D.natAbs)))
    (hval' : ∀ m : ℕ, (chiD D' m : ℂ) = DirichletCharacter.changeLevel hdvd' χ (m : ZMod (4 * D'.natAbs)))
    (hne : χ ≠ 1) (E E' : ℚ) (hE'0 : E' ≠ 0)
    (hE : ∏ p ∈ (4 * D.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) = (E : ℂ))
    (hE' : ∏ p ∈ (4 * D'.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) = (E' : ℂ)) :
    zetaD D 1 = ((E / E' : ℚ) : ℝ) * zetaD D' 1 := by
  rw [Nat.cast_one] at hE hE'
  have h1 := LD_eq_LFunction_mul hD χ hdvd hval (s := 1) (Or.inl hne)
  have h2 := LD_eq_LFunction_mul hD' χ hdvd' hval' (s := 1) (Or.inl hne)
  rw [hE] at h1
  rw [hE'] at h2
  have hE'c : (E' : ℂ) ≠ 0 := by exact_mod_cast hE'0
  have h3 : LD D hD 1 = (((E / E' : ℚ) : ℝ) : ℂ) * LD D' hD' 1 := by
    rw [h1, h2]; push_cast; field_simp
  rw [zetaD_eq hD, zetaD_eq hD', Complex.ofReal_one, h3, Complex.re_ofReal_mul]

/-! ### The entries -/

/-- $\zeta_{-7}(1) = \pi/(2\sqrt7)$: $L(1,\psi) = \pi/\sqrt7$ ($h = 1$) times $1 - \psi(2)/2 = \frac12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 1)"]
theorem zetaD_neg_seven_one : zetaD (-7) 1 = π / (2 * Real.sqrt 7) := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg7 _ chiD_eq_changeLevel_neg7
    (ne_one_of_apply _ 3 (by decide) (by rw [psiNeg7_natCast]; norm_num))
    _ (LFunction_kronecker_one_of_classNumber_one (-7) (by norm_num) classNumber_QField_neg_seven) _
    (psiNeg7_euler_neg7 1)]
  norm_num
  ring

/-- **Table 6, $d = 7$, $s = 1$** ($D = -7$): $\zeta_{-7}(1)\sqrt7/\pi = \tfrac12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 7, s = 1)"]
theorem table6_7_1 : zetaD (-7) 1 * Real.sqrt 7 / π = 1 / 2 := by
  rw [zetaD_neg_seven_one]
  have h : Real.sqrt 7 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-11}(1) = 3\pi/(2\sqrt{11})$: $L(1,\psi) = \pi/\sqrt{11}$ ($h = 1$) times $1 - \psi(2)/2 = \frac32$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 1)"]
theorem zetaD_neg_eleven_one : zetaD (-11) 1 = 3 * π / (2 * Real.sqrt 11) := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg11 _ chiD_eq_changeLevel_neg11
    (ne_one_of_apply _ 2 (by decide) (by rw [psiNeg11_natCast]; norm_num))
    _ (LFunction_kronecker_one_of_classNumber_one (-11) (by norm_num) classNumber_QField_neg_eleven) _
    (psiNeg11_euler_neg11 1)]
  norm_num
  ring

/-- **Table 6, $d = 11$, $s = 1$** ($D = -11$): $\zeta_{-11}(1)\sqrt{11}/\pi = \tfrac32$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 11, s = 1)"]
theorem table6_11_1 : zetaD (-11) 1 * Real.sqrt 11 / π = 3 / 2 := by
  rw [zetaD_neg_eleven_one]
  have h : Real.sqrt 11 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-19}(1) = 3\pi/(2\sqrt{19})$: $L(1,\psi) = \pi/\sqrt{19}$ ($h = 1$) times $1 - \psi(2)/2 = \frac32$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 1)"]
theorem zetaD_neg_nineteen_one : zetaD (-19) 1 = 3 * π / (2 * Real.sqrt 19) := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg19 _ chiD_eq_changeLevel_neg19
    (ne_one_of_apply _ 2 (by decide) (by rw [psiNeg19_natCast]; norm_num))
    _ (LFunction_kronecker_one_of_classNumber_one (-19) (by norm_num) classNumber_QField_neg_nineteen) _
    (psiNeg19_euler_neg19 1)]
  norm_num
  ring

/-- **Table 6, $d = 19$, $s = 1$** ($D = -19$): $\zeta_{-19}(1)\sqrt{19}/\pi = \tfrac32$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 19, s = 1)"]
theorem table6_19_1 : zetaD (-19) 1 * Real.sqrt 19 / π = 3 / 2 := by
  rw [zetaD_neg_nineteen_one]
  have h : Real.sqrt 19 ≠ 0 := by positivity
  field_simp

theorem psiNeg4_ne_one : psiNeg4 ≠ 1 :=
  ne_one_of_apply _ 3 (by decide) (by rw [psiNeg4_natCast]; norm_num [chiD])

theorem psiNeg4_euler_neg1_one :
    ∏ p ∈ (4 * (-1 : ℤ).natAbs).primeFactors, (1 - psiNeg4 p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) = ((1 : ℚ) : ℂ) := by
  rw [Rat.cast_one, ← Complex.ofReal_one]
  exact eulerFactor_eq_one _ (fun p hp => by
    have : p ∣ 4 * (-1 : ℤ).natAbs := Nat.dvd_of_mem_primeFactors hp
    simpa using this) _

theorem psiNeg8_euler_neg2_one :
    ∏ p ∈ (4 * (-2 : ℤ).natAbs).primeFactors, (1 - psiNeg8 p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) = ((1 : ℚ) : ℂ) := by
  rw [Rat.cast_one, ← Complex.ofReal_one]
  exact eulerFactor_eq_one _ (fun p hp => by
    have : p ∣ 4 * (-2 : ℤ).natAbs := Nat.dvd_of_mem_primeFactors hp
    simpa using this) _

/-- $\zeta_{-9}(1) = \frac43\zeta_{-1}(1) = \pi/3$ ($\chi_{-9} = \chi_{-1}$ away from $3$; Euler factor $1 + \frac13$). -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 1)"]
theorem zetaD_neg_nine_one : zetaD (-9) 1 = π / 3 := by
  rw [zetaD_one_of_zetaD_one (D' := -1) (by norm_num) (by norm_num) psiNeg4 _ _ chiD_eq_changeLevel_neg9
    chiD_eq_changeLevel_neg1 psiNeg4_ne_one _ _ one_ne_zero (psiNeg4_euler_neg9 1) psiNeg4_euler_neg1_one,
    zetaD_neg_one_one]
  norm_num

/-- **Table 6, $d = 9$, $s = 1$** ($D = -9$): $\zeta_{-9}(1)\sqrt9/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 9, s = 1)"]
theorem table6_9_1 : zetaD (-9) 1 * Real.sqrt 9 / π = 1 := by
  rw [zetaD_neg_nine_one, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  field_simp

/-- $\zeta_{-25}(1) = \frac45\zeta_{-1}(1) = \pi/5$ (Euler factor $1 - \psi(5)/5 = \frac45$). -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 1)"]
theorem zetaD_neg_twentyfive_one : zetaD (-25) 1 = π / 5 := by
  rw [zetaD_one_of_zetaD_one (D' := -1) (by norm_num) (by norm_num) psiNeg4 _ _ chiD_eq_changeLevel_neg25
    chiD_eq_changeLevel_neg1 psiNeg4_ne_one _ _ one_ne_zero (psiNeg4_euler_neg25 1) psiNeg4_euler_neg1_one,
    zetaD_neg_one_one]
  norm_num

/-- **Table 6, $d = 25$, $s = 1$** ($D = -25$): $\zeta_{-25}(1)\sqrt{25}/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 25, s = 1)"]
theorem table6_25_1 : zetaD (-25) 1 * Real.sqrt 25 / π = 1 := by
  rw [zetaD_neg_twentyfive_one, show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  field_simp

/-- $\zeta_{-18}(1) = \frac23\zeta_{-2}(1) = \pi/(3\sqrt2)$ (Euler factor $1 - \psi(3)/3 = \frac23$). -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 1)"]
theorem zetaD_neg_eighteen_one : zetaD (-18) 1 = π / (3 * Real.sqrt 2) := by
  rw [zetaD_one_of_zetaD_one (D' := -2) (by norm_num) (by norm_num) psiNeg8 _ _ chiD_eq_changeLevel_neg18
    chiD_eq_changeLevel_neg2 psiNeg8_ne_one _ _ one_ne_zero (psiNeg8_euler_neg18 1) psiNeg8_euler_neg2_one,
    zetaD_neg_two_one]
  have h : Real.sqrt 2 ≠ 0 := by positivity
  norm_num
  field_simp

/-- **Table 6, $d = 18$, $s = 1$** ($D = -18$): $\zeta_{-18}(1)\sqrt{18}/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 18, s = 1)"]
theorem table6_18_1 : zetaD (-18) 1 * Real.sqrt 18 / π = 1 := by
  rw [zetaD_neg_eighteen_one, show (18 : ℝ) = 3 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

end QuadFormsKB.ConwaySloane.Mass
