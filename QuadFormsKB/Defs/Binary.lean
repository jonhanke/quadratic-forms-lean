/-
# Integral binary quadratic forms (Gauss / Lagrange)

A binary form is just a `QuadForm ℤ 2`: `f(x, y) = a x² + b x y + c y²` with upper-triangular
coefficient matrix `!![a, b; 0, c]`. The classical names `a, b, c` are accessors, and
`BinQF.mk a b c` builds a form. `b` is not required to be even (Gauss required it; the
integer-coefficient convention here does not).
-/
import Mathlib
import QuadFormsKB.Defs.QuadForm

namespace QuadFormsKB

/-- An integral binary quadratic form `a x² + b x y + c y²`: a `QuadForm ℤ 2`. -/
abbrev BinQF := QuadForm ℤ 2

namespace BinQF

/-- **The coefficient $a$ of $x^2$** in $f(x, y) = a x^2 + b x y + c y^2$, i.e. $c_{00}$. -/
def a (f : BinQF) : ℤ := f.coeff 0 0

/-- **The coefficient $b$ of $x y$** in $f(x, y) = a x^2 + b x y + c y^2$, i.e. $c_{01}$.
Not required to be even. -/
def b (f : BinQF) : ℤ := f.coeff 0 1

/-- **The coefficient $c$ of $y^2$** in $f(x, y) = a x^2 + b x y + c y^2$, i.e. $c_{11}$. -/
def c (f : BinQF) : ℤ := f.coeff 1 1

/-- **The binary form $a x^2 + b x y + c y^2$** with $a, b, c \in \mathbb{Z}$ (`a_mk`, `b_mk`,
`c_mk` recover them). -/
def mk (a b c : ℤ) : BinQF := QuadForm.ofUpper ![![a, b], ![0, c]]

@[simp] theorem a_mk (a b c : ℤ) : (mk a b c).a = a := by simp [mk, BinQF.a, QuadForm.ofUpper]
@[simp] theorem b_mk (a b c : ℤ) : (mk a b c).b = b := by simp [mk, BinQF.b, QuadForm.ofUpper]
@[simp] theorem c_mk (a b c : ℤ) : (mk a b c).c = c := by simp [mk, BinQF.c, QuadForm.ofUpper]

/-- **The value $f(x, y)$** at $x, y \in \mathbb{Z}$ (the general `QuadForm.eval` at the vector
$(x, y)$). In coordinates it is $a x^2 + b x y + c y^2$ (`eval_eq`). -/
def eval (f : BinQF) (x y : ℤ) : ℤ := QuadForm.eval f ![x, y]

/-- **In coordinates:** $f(x, y) = a x^2 + b x y + c y^2$ for all $x, y \in \mathbb{Z}$. -/
@[kb "buell1989" "Ch. 1"]
theorem eval_eq (f : BinQF) (x y : ℤ) : f.eval x y = f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2 := by
  simp [eval, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, BinQF.a, BinQF.b, BinQF.c]
  ring

/-- **The discriminant** $\operatorname{disc}(f) = b^2 - 4ac \in \mathbb{Z}$ (Buell's sign
convention). It equals $-\det$ of the Hessian $\begin{pmatrix} 2a & b \\ b & 2c \end{pmatrix}$
(`disc_eq_neg_det_hessian`), and is always $\equiv 0$ or $1 \pmod 4$ (`disc_mod_four`). -/
@[kb "buell1989" "Ch. 1"]
def disc (f : BinQF) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- **$f$ represents $n \in \mathbb{Z}$:** $f(x, y) = n$ for some **integers** $x, y$.
Every form represents $0$ (take $x = y = 0$). -/
def Represents (f : BinQF) (n : ℤ) : Prop := ∃ x y : ℤ, f.eval x y = n

/-- **Positive definite** (analytic definition): $f(x, y) > 0$ for every integer vector
$(x, y) \ne (0, 0)$. Equivalent to `PosDef'` (`posDef_iff_posDef'`). -/
def PosDef (f : BinQF) : Prop := ∀ x y : ℤ, (x, y) ≠ (0, 0) → 0 < f.eval x y

/-- **Positive definite** (invariant definition): $a > 0$ and $\operatorname{disc}(f) =
b^2 - 4ac < 0$. Equivalent to `PosDef` (`posDef_iff_posDef'`). -/
def PosDef' (f : BinQF) : Prop := 0 < f.a ∧ f.disc < 0

/-- **Substitution by an integer matrix** $g = \begin{pmatrix} p & q \\ r & s \end{pmatrix}$:
$$(\mathrm{subst}\ g\ f)(x, y) = f(p x + q y,\ r x + s y),$$
i.e. $f \mapsto f \circ g$ (`eval_subst`). This is a **right** action,
$\mathrm{subst}(gh) = \mathrm{subst}\,h \circ \mathrm{subst}\,g$, and $g$ is **any** integer
matrix, not restricted to $\mathrm{SL}_2(\mathbb{Z})$ or $\mathrm{GL}_2(\mathbb{Z})$.
Equivalence of forms under $\mathrm{SL}_2(\mathbb{Z})$ is a separate notion (not yet defined). -/
def subst (p q r s : ℤ) (f : BinQF) : BinQF :=
  mk (f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2)
    (2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s)
    (f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2)

/-- **The defining property of `subst`:** $(\mathrm{subst}\ g\ f)(x, y) = f(p x + q y,\ r x + s y)$
for all $x, y \in \mathbb{Z}$. -/
theorem eval_subst (p q r s : ℤ) (f : BinQF) (x y : ℤ) :
    (subst p q r s f).eval x y = f.eval (p * x + q * y) (r * x + s * y) := by
  simp only [eval_eq, subst, a_mk, b_mk, c_mk]; ring

/-- **The discriminant scales by $\det(g)^2$:**
$\operatorname{disc}(\mathrm{subst}\ g\ f) = (ps - qr)^2 \operatorname{disc}(f)$ for every integer
matrix $g$. -/
@[kb "buell1989" "Ch. 1, eq. (1.2)"]
theorem disc_subst (p q r s : ℤ) (f : BinQF) :
    (subst p q r s f).disc = (p * s - q * r) ^ 2 * f.disc := by
  simp only [disc, subst, a_mk, b_mk, c_mk]; ring

/-- **The discriminant is invariant under $\mathrm{GL}_2(\mathbb{Z})$:** if $(ps - qr)^2 = 1$,
i.e. $\det g = \pm 1$, then $\operatorname{disc}(\mathrm{subst}\ g\ f) = \operatorname{disc}(f)$. -/
@[kb "buell1989" "Ch. 1"]
theorem disc_subst_of_det (p q r s : ℤ) (f : BinQF) (h : (p * s - q * r) ^ 2 = 1) :
    (subst p q r s f).disc = f.disc := by
  rw [disc_subst, h, one_mul]

/-- **Discriminants are $0$ or $1$ mod $4$:** $\operatorname{disc}(f) \equiv 0$ or $1 \pmod 4$
for every integral binary form (since $b^2 \equiv 0, 1 \pmod 4$). -/
@[kb "buell1989" "Ch. 1"]
theorem disc_mod_four (f : BinQF) : f.disc % 4 = 0 ∨ f.disc % 4 = 1 := by
  simp only [disc]
  rcases Int.even_or_odd f.b with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk] <;> ring_nf <;> omega

end BinQF

end QuadFormsKB
