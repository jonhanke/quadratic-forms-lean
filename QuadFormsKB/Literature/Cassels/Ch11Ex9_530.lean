/-
# Cassels, Chapter 11, Example 9 (p. 253): the genus of $x^2 + xy + 7y^2 + 3(z^2 + zt + t^2)$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Example 9 (p. 253). Variables
$x, y, z, t$ are $x_0, x_1, x_2, x_3$.

**Proved here (unconditionally).** `ex9_sameGenus₂`, `ex9_sameGenus₃` (neighbour certificates), the three
inequivalences, and `ex9_moreThanOneSpinorGenus`.

**Open input.** `Ex9Classes`: every form of the genus is equivalent to one of the three. This is a classification of a
quaternary genus (reduction theory or a mass computation), out of scope; `ex9Statement_of_classes` assembles
`Ex9Statement` from it.
-/
import QuadFormsKB.Literature.Cassels.Ch11Examples4
import QuadFormsKB.Siegel.KneserCert

open Matrix QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

set_option linter.style.longLine false

namespace QuadFormsKB.Cassels.Ch11Ex4

namespace Ex9Data

/-- A $5$-neighbour certificate for `ex9f₂` as the Gram form of the $5$-neighbour $L(\vec v)$,
$\vec v = (1, 13, 1, 0)$, of $(\mathbb Z^4, f)$ (generator output; see `NbCert`). -/
def nbCert₂ : NbCert 4 := ⟨![1, 13, 1, 0], !![5, 3, 2, 2; 0, -1, -4, -4; 0, -2, 2, 7; 0, 0, 5, -5], ![0, 3, 2, 2], ![0, 2, 0, 0], !![-41, -511, -16, -8; 54, 657, 20, 10; 12, 146, 5, 3; 12, 146, 5, 2], ![14, -18, -4, -4], ![4, -5, -1, -1], !![5, 7, 4, 2; 0, -9, -8, -4; 0, -2, 1, 3; 0, -2, 1, -2]⟩

/-- A $5$-neighbour certificate for `ex9f₃`, with $\vec v = (15, 1, 1, 0)$ (generator output). -/
def nbCert₃ : NbCert 4 := ⟨![15, 1, 1, 0], !![-5, 5, 5, 5; 1, 2, -2, -2; -4, 2, -2, 3; 0, 0, 5, -5], ![1, 2, 3, 3], ![1, 0, 0, 0], !![-12, -11, -4, -2; -18, -16, -4, -2; -12, -12, -3, -1; -12, -12, -3, -2], ![2, 3, 2, 2], ![1, 2, 1, 1], !![2, 3, -8, -4; 3, 7, -2, -1; 2, -2, -3, 1; 2, -2, -3, -4]⟩

end Ex9Data

open Ex9Data

/-- **$5 \nmid \det H_f = 729$** for $f = $ `ex9f` (determinant certificate $X = 27\operatorname{adj}$-blocks, $d = 729$). -/
theorem ex9_not_five_dvd_det : ¬ ((5 : ℕ) : ℤ) ∣ ex9f.hessian.det :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  DetCert.not_dvd_det (c := ⟨!![378, -27, 0, 0; -27, 54, 0, 0; 0, 0, 162, -81; 0, 0, -81, 162], 729⟩)
    (by decide +kernel)

/-- **`ex9f₂` is in the genus of `ex9f`** (Cassels, Ch. 11, Ex. 9, reconstruction): the Gram form of the $5$-neighbour
of $(\mathbb Z^4, f)$ given by the kernel-checked certificate `Ex9Data.nbCert₂`; $5 \nmid 2 \cdot 729$. -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (ex9f₂ is in the genus of ex9f; reconstruction)"]
theorem ex9_sameGenus₂ : SameGenus ex9f ex9f₂ :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  NbCert.sameGenus (p := 5) (c := nbCert₂) (by norm_num) ex9_not_five_dvd_det (by decide +kernel)

/-- **`ex9f₃` is in the genus of `ex9f`** (Cassels, Ch. 11, Ex. 9, reconstruction): the Gram form of the $5$-neighbour
of $(\mathbb Z^4, f)$ given by the kernel-checked certificate `Ex9Data.nbCert₃`. -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (ex9f₃ is in the genus of ex9f; reconstruction)"]
theorem ex9_sameGenus₃ : SameGenus ex9f ex9f₃ :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  NbCert.sameGenus (p := 5) (c := nbCert₃) (by norm_num) ex9_not_five_dvd_det (by decide +kernel)

/-! ### The three forms are pairwise inequivalent -/

/-- Helper: values of $f$ = `ex9f`, $x_0^2 + x_0x_1 + 7x_1^2 + 3(x_2^2 + x_2x_3 + x_3^2)$. -/
theorem eval_ex9f (x : Fin 4 → ℤ) :
    ex9f.eval x = x 0 ^ 2 + x 0 * x 1 + 7 * x 1 ^ 2 + 3 * (x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2) := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_four, ex9f]
  ring

/-- Helper: values of `ex9f₂`, $x_0^2 + x_0x_1 + x_1^2 + 9(x_2^2 + x_2x_3 + x_3^2)$. -/
theorem eval_ex9f₂ (x : Fin 4 → ℤ) :
    ex9f₂.eval x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + 9 * (x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2) := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_four, ex9f₂]
  ring

/-- Helper: values of `ex9f₃`. -/
theorem eval_ex9f₃ (x : Fin 4 → ℤ) :
    ex9f₃.eval x = 3 * x 0 ^ 2 + 3 * x 1 ^ 2 + 4 * x 2 ^ 2 + 4 * x 3 ^ 2 - 3 * x 0 * x 1 - 3 * x 0 * x 2
      - 3 * x 0 * x 3 - x 2 * x 3 := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_four, ex9f₃]
  ring

/-- Helper: `ex9f₃` does not represent $1$ (indeed
$f_3 = 3(x_0 - \tfrac{x_1 + x_2 + x_3}{2})^2 + \tfrac94(x_1 - \tfrac{x_2 + x_3}{3})^2 + 3(x_2 - \tfrac{x_3}{2})^2
+ \tfrac94x_3^2$, whose minimum on nonzero integer vectors is $3$). -/
theorem ex9f₃_ne_one (x : Fin 4 → ℤ) : ex9f₃.eval x ≠ 1 := by
  rw [eval_ex9f₃]
  intro h
  have h3 : x 3 = 0 := by
    by_contra hx
    have : 1 ≤ x 3 ^ 2 := by nlinarith [sq_pos_of_ne_zero hx]
    nlinarith [sq_nonneg (2 * x 0 - x 1 - x 2 - x 3), sq_nonneg (3 * x 1 - x 2 - x 3),
      sq_nonneg (2 * x 2 - x 3)]
  have h2 : x 2 = 0 := by
    by_contra hx
    have : 1 ≤ x 2 ^ 2 := by nlinarith [sq_pos_of_ne_zero hx]
    rw [h3] at h
    nlinarith [sq_nonneg (2 * x 0 - x 1 - x 2), sq_nonneg (3 * x 1 - x 2)]
  have h1 : x 1 = 0 := by
    by_contra hx
    have : 1 ≤ x 1 ^ 2 := by nlinarith [sq_pos_of_ne_zero hx]
    rw [h3, h2] at h
    nlinarith [sq_nonneg (2 * x 0 - x 1)]
  rw [h3, h2, h1] at h
  have : x 0 ^ 2 * 3 = 1 := by linarith
  omega

/-- Helper: the only vectors of value $1$ of `ex9f` are $\pm\vec e_0$. -/
theorem ex9f_eq_one {x : Fin 4 → ℤ} (h : ex9f.eval x = 1) : x 0 ^ 2 = 1 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 := by
  rw [eval_ex9f] at h
  have hq : 0 ≤ x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2 := by nlinarith [sq_nonneg (x 2 + x 3), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h1 : x 1 = 0 := by
    by_contra hx
    have : 1 ≤ x 1 ^ 2 := by nlinarith [sq_pos_of_ne_zero hx]
    nlinarith [sq_nonneg (2 * x 0 + x 1)]
  rw [h1] at h
  have h23 : x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2 = 0 := by
    by_contra hx
    have : 1 ≤ x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2 := by omega
    nlinarith [sq_nonneg (x 0)]
  have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 2 + 2 * x 3), sq_nonneg (x 3)]
  have h3 : x 3 = 0 := by nlinarith [sq_nonneg (x 3 + 2 * x 2), sq_nonneg (x 2)]
  refine ⟨?_, h1, h2, h3⟩
  rw [h23] at h
  linarith

/-- Helper: an invertible integer matrix has trivial kernel. -/
theorem ex9_mulVec_eq_zero {g : GL (Fin 4) ℤ} {y : Fin 4 → ℤ} (h : g.val *ᵥ y = 0) : y = 0 := by
  have e : y = (g⁻¹ : GL (Fin 4) ℤ).val *ᵥ (g.val *ᵥ y) := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [e, h, mulVec_zero]

/-- **`ex9f` and `ex9f₂` are not integrally equivalent** (Cassels, Ch. 11, Ex. 9, reconstruction). `ex9f₂` has the two
linearly independent vectors $\vec e_0, \vec e_1$ of value $1$ (its numbers of value-$1$ vectors is $6$), while the
value-$1$ vectors of `ex9f` are only $\pm\vec e_0$ (`ex9f_eq_one`; it has $2$); an equivalence would carry the
two to value-$1$ vectors $\vec v, \vec w$ of `ex9f` with $\vec v \ne \pm\vec w$. -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (ex9f and ex9f₂ are not equivalent; reconstruction)"]
theorem ex9_not_equiv₁₂ : ¬ IntEquiv ex9f ex9f₂ := by
  rintro ⟨g, hg⟩
  have hv := ex9f_eq_one (x := g.val *ᵥ ![1, 0, 0, 0]) (by rw [hg, eval_ex9f₂]; simp)
  have hw := ex9f_eq_one (x := g.val *ᵥ ![0, 1, 0, 0]) (by rw [hg, eval_ex9f₂]; simp)
  have hy : ∀ s : ℤ, g.val *ᵥ ![1, s, 0, 0] = g.val *ᵥ ![1, 0, 0, 0] + s • g.val *ᵥ ![0, 1, 0, 0] := by
    intro s
    have : (![1, s, 0, 0] : Fin 4 → ℤ) = ![1, 0, 0, 0] + s • ![0, 1, 0, 0] := by
      ext i; fin_cases i <;> simp
    rw [this, mulVec_add, mulVec_smul]
  have pm : ∀ a : ℤ, a ^ 2 = 1 → a = 1 ∨ a = -1 := by
    intro a ha
    have : (a - 1) * (a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; omega
    · right; omega
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  obtain ⟨hw0, hw1, hw2, hw3⟩ := hw
  have key : ∀ s : ℤ, (g.val *ᵥ ![1, s, 0, 0]) 0 = 0 → (g.val *ᵥ ![1, s, 0, 0]) 1 = 0 →
      (g.val *ᵥ ![1, s, 0, 0]) 2 = 0 → (g.val *ᵥ ![1, s, 0, 0]) 3 = 0 → False := by
    intro s h0 h1 h2 h3
    have : g.val *ᵥ ![1, s, 0, 0] = 0 := by
      ext i; fin_cases i <;> simpa
    have := congrFun (ex9_mulVec_eq_zero this) 0
    simp at this
  rcases pm _ hv0 with a | a <;> rcases pm _ hw0 with b | b
  · exact key (-1) (by rw [hy]; simp [a, b]) (by rw [hy]; simp [hv1, hw1]) (by rw [hy]; simp [hv2, hw2])
      (by rw [hy]; simp [hv3, hw3])
  · exact key 1 (by rw [hy]; simp [a, b]) (by rw [hy]; simp [hv1, hw1]) (by rw [hy]; simp [hv2, hw2])
      (by rw [hy]; simp [hv3, hw3])
  · exact key 1 (by rw [hy]; simp [a, b]) (by rw [hy]; simp [hv1, hw1]) (by rw [hy]; simp [hv2, hw2])
      (by rw [hy]; simp [hv3, hw3])
  · exact key (-1) (by rw [hy]; simp [a, b]) (by rw [hy]; simp [hv1, hw1]) (by rw [hy]; simp [hv2, hw2])
      (by rw [hy]; simp [hv3, hw3])

/-- Helper: `ex9f` represents $1$ ($\vec x = \vec e_0$). -/
theorem ex9f_eval_e0 : ex9f.eval ![1, 0, 0, 0] = 1 := by rw [eval_ex9f]; simp

/-- Helper: `ex9f₂` represents $1$ ($\vec x = \vec e_0$). -/
theorem ex9f₂_eval_e0 : ex9f₂.eval ![1, 0, 0, 0] = 1 := by rw [eval_ex9f₂]; simp

/-- **`ex9f` and `ex9f₃` are not integrally equivalent** (Cassels, Ch. 11, Ex. 9, reconstruction): `ex9f` represents
$1$ (at $\vec e_0$) while `ex9f₃` does not (`ex9f₃_ne_one`; it has no vector of value $1$). -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (ex9f and ex9f₃ are not equivalent; reconstruction)"]
theorem ex9_not_equiv₁₃ : ¬ IntEquiv ex9f ex9f₃ := by
  intro h
  obtain ⟨g, hg⟩ := (IsometricGL.symm h : IntEquiv ex9f₃ ex9f)
  exact ex9f₃_ne_one _ ((hg _).trans ex9f_eval_e0)

/-- **`ex9f₂` and `ex9f₃` are not integrally equivalent** (Cassels, Ch. 11, Ex. 9, reconstruction): `ex9f₂` represents
$1$ (at $\vec e_0$) while `ex9f₃` does not (`ex9f₃_ne_one`). -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (ex9f₂ and ex9f₃ are not equivalent; reconstruction)"]
theorem ex9_not_equiv₂₃ : ¬ IntEquiv ex9f₂ ex9f₃ := by
  intro h
  obtain ⟨g, hg⟩ := (IsometricGL.symm h : IntEquiv ex9f₃ ex9f₂)
  exact ex9f₃_ne_one _ ((hg _).trans ex9f₂_eval_e0)

end QuadFormsKB.Cassels.Ch11Ex4
