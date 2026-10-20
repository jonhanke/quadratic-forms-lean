/-
# Positive definiteness of binary forms: analytic vs. invariant definitions

For $f(x, y) = a x^2 + b x y + c y^2$ with $a, b, c \in \mathbb{Z}$: positive at every nonzero
integer vector (`PosDef`) $\iff$ $a > 0$ and $\operatorname{disc}(f) = b^2 - 4ac < 0$ (`PosDef'`),
via completing the square. Also, $\operatorname{disc}(f) = -\det$ of the Hessian.
-/
import QuadFormsKB.Defs.Binary
import QuadFormsKB.Defs.QuadForm

namespace QuadFormsKB.BinQF

/-- **Completing the square:** $4a\, f(x, y) = (2a x + b y)^2 - D\, y^2$ with
$D = \operatorname{disc}(f) = b^2 - 4ac$, for all $x, y \in \mathbb{Z}$. -/
@[kb "buell1989" "Ch. 1"]
theorem four_a_mul_eval (f : BinQF) (x y : ℤ) :
    4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.disc * y ^ 2 := by
  simp only [eval_eq, disc]; ring

/-- **Invariant $\Rightarrow$ analytic:** if $a > 0$ and $b^2 - 4ac < 0$, then $f(x, y) > 0$ for
every integer vector $(x, y) \ne (0, 0)$. -/
@[kb "buell1989" "Ch. 1"]
theorem posDef_of_posDef' (f : BinQF) (h : f.PosDef') : f.PosDef := by
  obtain ⟨ha, hD⟩ := h
  intro x y hxy
  have key := four_a_mul_eval f x y
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := by rintro rfl; exact hxy rfl
    simp only [eval_eq]
    have : 0 < x ^ 2 := by positivity
    nlinarith
  · have hy2 : 0 < y ^ 2 := by positivity
    have h1 : 0 < -f.disc * y ^ 2 := mul_pos (by linarith) hy2
    have h2 : 0 ≤ (2 * f.a * x + f.b * y) ^ 2 := sq_nonneg _
    have h3 : 0 < 4 * f.a * f.eval x y := by nlinarith
    by_contra hc
    push Not at hc
    nlinarith

/-- **Analytic $\Rightarrow$ invariant:** if $f(x, y) > 0$ for every integer vector
$(x, y) \ne (0, 0)$, then $a > 0$ and $b^2 - 4ac < 0$. -/
@[kb "buell1989" "Ch. 1"]
theorem posDef'_of_posDef (f : BinQF) (h : f.PosDef) : f.PosDef' := by
  have ha := h 1 0 (by simp)
  have hb := h f.b (-2 * f.a) (by
    intro e
    simp only [Prod.mk.injEq] at e
    simp only [eval_eq] at ha
    omega)
  simp only [eval_eq] at ha hb
  refine ⟨by simpa using ha, ?_⟩
  simp only [disc]
  have ha' : 0 < f.a := by simpa using ha
  have : f.a * (4 * f.a * f.c - f.b ^ 2) > 0 := by nlinarith
  by_contra hc
  push Not at hc
  nlinarith

/-- **The two definitions of positive definite agree:** `PosDef f` $\iff$ `PosDef' f`. -/
@[kb "buell1989" "Ch. 1"]
theorem posDef_iff_posDef' (f : BinQF) : f.PosDef ↔ f.PosDef' :=
  ⟨posDef'_of_posDef f, posDef_of_posDef' f⟩

/-- **The discriminant is minus the Hessian determinant:**
$\operatorname{disc}(f) = b^2 - 4ac = -\det\begin{pmatrix} 2a & b \\ b & 2c \end{pmatrix}$. -/
@[kb "buell1989" "Ch. 1"]
theorem disc_eq_neg_det_hessian (f : BinQF) : f.disc = -(QuadForm.hessian f).det := by
  have h10 : f.coeff 1 0 = 0 := f.upper (show id (0 : Fin 2) < id 1 by decide)
  simp [disc, QuadForm.hessian, Matrix.det_fin_two, BinQF.a, BinQF.b, BinQF.c, h10]
  ring

end QuadFormsKB.BinQF
