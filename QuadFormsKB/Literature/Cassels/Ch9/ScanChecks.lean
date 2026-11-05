/-
# Cassels, Chapter 9: two formulas as printed (read from the page images)

Two formulas of Chapter 9 were garbled in the machine-read text and were reconstructed differently from the book in
`Ch9Sec1.lean` and `Ch9Sec7Cayley.lean`. After reading the page images, this file formalizes the printed versions and
keeps the earlier declarations.

**Proves**
* (Ch. 9, §1, p. 128) the form $3x^{2} + 2xy + 101y^{2}$ (not $3x^{2} + 2xy + 10y^{2}$) has no improper automorph; its
  only integral automorphs are $\pm I$ (`automorph_eq_one_or_neg_one_ex'`, `not_hasImproperAut_ex'`);
* (Ch. 9, §7, p. 156) Cayley's formula with the sign convention as printed: for $\det(I + T) \ne 0$ and
  $L = (T - I)(I + T)^{-1}$ (7.6), $T^{\mathsf T}FT = F$ (7.4) iff $L^{\mathsf T}F + FL = 0$ (7.8)
  (`cayley_automorph_iff'`), and $\det(I - L) \ne 0$ with $T = (I + L)(I - L)^{-1}$ (7.7) (`cayley_inverse'`).

Cassels' $T'$ is the transpose $T^{\mathsf T}$. The earlier versions (`exForm2`, `cayley_automorph_iff`, `cayley_inverse`)
used reconstructions that differ from the book.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec7Cayley

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-! ### Ch. 9, §1, p. 128: the form $3x^2 + 2xy + 101y^2$ -/

/-- $3x^{2} + 2xy + 101y^{2}$ (variables $x_0, x_1$), the form printed in Cassels, Ch. 9, §1, p. 128. -/
def exForm2' : QuadForm ℤ 2 := QuadForm.ofUpper ![![3, 2], ![0, 101]]

/-- Helper: the values of `exForm2'`: $Q(x_0, x_1) = 3x_0^2 + 2x_0x_1 + 101x_1^2$. -/
theorem eval_exForm2' (x : Fin 2 → ℤ) : exForm2'.eval x = 3 * x 0 ^ 2 + 2 * x 0 * x 1 + 101 * x 1 ^ 2 := by
  simp [exForm2', QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]; ring

/-- **Cassels, Ch. 9, §1, p. 128:** the only integral automorphs of $3x^{2} + 2xy + 101y^{2}$ are $\pm I$. (The
book's argument: the only integral representations of $3$ are $\pm(1, 0)$, so an automorph sends $(1, 0)$ to
$\pm(1, 0)$.) -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (a form with no improper automorph: 3x² + 2xy + 101y², read from the page image)"]
theorem automorph_eq_one_or_neg_one_ex' {T : GL (Fin 2) ℤ} (hT : T ∈ Aut exForm2') :
    T.val = 1 ∨ T.val = -1 := by
  have hev : ∀ x, exForm2'.eval (T.val *ᵥ x) = exForm2'.eval x := hT
  have h3 := hev ![1, 0]
  have h3' := hev ![0, 1]
  have h3'' := hev ![1, 1]
  simp only [eval_exForm2', mulVec, dotProduct, Fin.sum_univ_two] at h3 h3' h3''
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3 h3' h3''
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : ℤ, T.val = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two T.val⟩
  simp only [hM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h3 h3' h3''
  have hc : c = 0 := by
    by_contra hc
    have : 1 ≤ c ^ 2 := by nlinarith [sq_pos_of_ne_zero hc]
    nlinarith [sq_nonneg (a + c), sq_nonneg a]
  subst hc
  have key : 3 * a * b + a * d = 1 := by nlinarith
  have ha : a = 1 ∨ a = -1 := by
    have : a * (3 * b + d) = 1 := by linarith
    exact Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ this)
  have hd : d = a - 3 * b := by
    rcases ha with rfl | rfl <;> nlinarith
  have hb : b * (906 * b - 604 * a) = 0 := by
    subst hd
    rcases ha with rfl | rfl <;> nlinarith
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact h
    · exfalso
      rcases ha with rfl | rfl <;> omega
  subst hb0
  rcases ha with rfl | rfl
  · left; rw [hM, hd]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · right; rw [hM, hd]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **Cassels, Ch. 9, §1, p. 128:** $3x^{2} + 2xy + 101y^{2}$ *has no improper automorphs*. Follows from
`automorph_eq_one_or_neg_one_ex'`, since $\det(\pm I) = 1$ in dimension $2$. -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (a form with no improper automorph: 3x² + 2xy + 101y², read from the page image)"]
theorem not_hasImproperAut_ex' : ¬ HasImproperAut exForm2' := by
  rintro ⟨T, hT, hd⟩
  rcases automorph_eq_one_or_neg_one_ex' hT with h | h
  · rw [h, det_one] at hd; omega
  · rw [h, det_neg, det_one] at hd; norm_num at hd

/-! ### Ch. 9, §7, p. 156: Cayley's formula as printed -/

section Cayley

variable {K : Type*} [Field K] {n : ℕ}

/-- **Cayley's formula (7.4) $\iff$ (7.8), as printed** (Cassels, Ch. 9, §7, p. 156): if $\det(I + T) \ne 0$ (7.5)
and $L = (T - I)(I + T)^{-1}$ (7.6), then $T^{\mathsf T}FT = F$ iff $L^{\mathsf T}F + FL = 0$. Arguments: `h2`
the hypothesis $2 \ne 0$ in the field $K$; $F$ any square matrix (in the book, the symmetric matrix of the form);
$T$ a square matrix with `hT` the invertibility of $I + T$. -/
@[kb "cassels1978" "Ch. 9, §7, (7.4)–(7.8), p. 156 (Cayley's formula as printed)"]
theorem cayley_automorph_iff' (h2 : (2 : K) ≠ 0) (F T : Matrix (Fin n) (Fin n) K) (hT : IsUnit (1 + T).det) :
    Tᵀ * F * T = F ↔ ((T - 1) * (1 + T)⁻¹)ᵀ * F + F * ((T - 1) * (1 + T)⁻¹) = 0 := by
  have e : (T - 1) * (1 + T)⁻¹ = -((1 - T) * (1 + T)⁻¹) := by
    rw [← neg_mul, neg_sub]
  rw [cayley_automorph_iff h2 F T hT, e, transpose_neg, neg_mul, Matrix.mul_neg, ← neg_add, neg_eq_zero]

/-- **Cayley's formula (7.6)–(7.7), as printed** (Cassels, Ch. 9, §7, p. 156): if $\det(I + T) \ne 0$ and
$L = (T - I)(I + T)^{-1}$, then $\det(I - L) \ne 0$ and $T = (I + L)(I - L)^{-1}$. Arguments: `h2` the hypothesis
$2 \ne 0$ in the field $K$; $T$ a square matrix with `hT` the invertibility of $I + T$. -/
@[kb "cassels1978" "Ch. 9, §7, (7.6)–(7.7), p. 156 (as printed)"]
theorem cayley_inverse' (h2 : (2 : K) ≠ 0) (T : Matrix (Fin n) (Fin n) K) (hT : IsUnit (1 + T).det) :
    IsUnit (1 - (T - 1) * (1 + T)⁻¹).det ∧
      T = (1 + (T - 1) * (1 + T)⁻¹) * (1 - (T - 1) * (1 + T)⁻¹)⁻¹ := by
  set A := 1 + T
  have hA' : A * A⁻¹ = 1 := mul_nonsing_inv A hT
  have hA : A⁻¹ * A = 1 := nonsing_inv_mul A hT
  have e1 : 1 - (T - 1) * A⁻¹ = (2 : K) • A⁻¹ := by
    have h : (2 : K) • A⁻¹ = (A - (T - 1)) * A⁻¹ := by
      rw [show A - (T - 1) = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) by simp only [A]; rw [two_smul]; abel,
        smul_mul_assoc, Matrix.one_mul]
    rw [h, sub_mul A (T - 1) A⁻¹, hA']
  have e2 : 1 + (T - 1) * A⁻¹ = (2 : K) • (T * A⁻¹) := by
    have h : (2 : K) • (T * A⁻¹) = (A + (T - 1)) * A⁻¹ := by
      rw [show A + (T - 1) = (2 : K) • T by simp only [A]; rw [two_smul]; abel, smul_mul_assoc]
    rw [h, add_mul, hA']
  have hinv : ((2 : K) • A⁻¹) * ((2 : K)⁻¹ • A) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ h2, one_smul, hA]
  have hM : ((2 : K) • A⁻¹)⁻¹ = (2 : K)⁻¹ • A := inv_eq_right_inv hinv
  refine ⟨?_, ?_⟩
  · rw [e1]
    have h := congrArg Matrix.det hinv
    rw [det_mul, det_one] at h
    exact IsUnit.of_mul_eq_one _ h
  · rw [e1, e2, hM, smul_mul_smul_comm, mul_inv_cancel₀ h2, one_smul, Matrix.mul_assoc, hA, Matrix.mul_one]

end Cayley

end QuadFormsKB.Siegel
