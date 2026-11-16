import QuadFormsKB.Binary.ClassBijection

/-!
# Gauss's forms $(a, b, c) = a x^2 + 2 b x y + c y^2$ (Disquisitiones Arithmeticae, Section V)

Gauss writes a binary form as $(a, b, c)$ for $a x^2 + 2 b x y + c y^2$, with an **even** middle coefficient
$2b$ (*Disq. Arith.* Art. 153), and calls $b^2 - a c$ its **determinant** (Art. 154). This library's binary forms
(`BinQF`, $a x^2 + b x y + c y^2$, discriminant $b^2 - 4ac$) allow an odd middle coefficient. This file is the
dictionary between the two conventions:

* `gaussForm a b c` is Gauss's $(a, b, c)$, i.e. the library form `BinQF.mk a (2 b) c`;
* `gaussDet a b c = b^2 - a c` is Gauss's determinant, and $\operatorname{disc}(a, b, c) = 4\,(b^2 - ac)$
  (`disc_gaussForm`);
* a library form is one of Gauss's forms exactly when its middle coefficient is even (`exists_gaussForm_iff`), and
  this is preserved by every integral substitution (`even_b_subst`), so Gauss's classes are unions of library
  classes of forms with even middle coefficient;
* Gauss's transformation formulas (Art. 157) are `subst_gaussForm`, and his **proper equivalence** (equivalence by
  a substitution of determinant $+1$, Art. 158) is the library's `Binary.SLEquiv` (`sLEquiv_iff`);
* **properly primitive** (Art. 226: $\gcd(a, 2b, c) = 1$) is the library's `BinQF.IsPrimitive` of `gaussForm a b c`.

Gauss numbers his substitutions $x = \alpha x' + \beta y'$, $y = \gamma x' + \delta y'$; the library's
`BinQF.subst α β γ δ f` is exactly $f(\alpha x + \beta y, \gamma x + \delta y)$ (`BinQF.eval_subst`).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- **Gauss's form $(a, b, c)$** (*Disq. Arith.* Art. 153): the binary form $a x^2 + 2 b x y + c y^2$, i.e. the
library form with coefficients $a$, $2b$, $c$ (`BinQF.mk a (2 * b) c`). -/
@[kb "gauss1801" "Art. 153, p. 165"]
def gaussForm (a b c : ℤ) : BinQF := BinQF.mk a (2 * b) c

/-- **Gauss's determinant** of $(a, b, c)$ (*Disq. Arith.* Art. 154): $b^2 - a c$. -/
@[kb "gauss1801" "Art. 154, p. 166"]
def gaussDet (a b c : ℤ) : ℤ := b ^ 2 - a * c

@[simp] theorem a_gaussForm (a b c : ℤ) : (gaussForm a b c).a = a := by simp [gaussForm]
@[simp] theorem b_gaussForm (a b c : ℤ) : (gaussForm a b c).b = 2 * b := by simp [gaussForm]
@[simp] theorem c_gaussForm (a b c : ℤ) : (gaussForm a b c).c = c := by simp [gaussForm]

/-- **Values of Gauss's form:** $(a, b, c)(x, y) = a x^2 + 2 b x y + c y^2$. -/
theorem eval_gaussForm (a b c x y : ℤ) : (gaussForm a b c).eval x y = a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  rw [eval_eq]; simp only [a_gaussForm, b_gaussForm, c_gaussForm]

/-- **Discriminant versus determinant:** $\operatorname{disc}(a, b, c) = (2b)^2 - 4ac = 4\,(b^2 - ac)$, four times
Gauss's determinant. -/
@[kb "gauss1801" "Art. 154, p. 166"]
theorem disc_gaussForm (a b c : ℤ) : (gaussForm a b c).disc = 4 * gaussDet a b c := by
  simp only [disc, a_gaussForm, b_gaussForm, c_gaussForm, gaussDet]; ring

/-- **Gauss's forms are the forms with even middle coefficient:** a library form $a x^2 + b x y + c y^2$ is of
the form $(a', b', c')$ in Gauss's notation iff $b$ is even. -/
theorem exists_gaussForm_iff (f : BinQF) : (∃ a b c, f = gaussForm a b c) ↔ Even f.b := by
  constructor
  · rintro ⟨a, b, c, rfl⟩; simp
  · rintro ⟨k, hk⟩
    exact ⟨f.a, k, f.c, ext_abc (by simp) (by simp [hk]; ring) (by simp)⟩

/-- **Integral substitutions keep the middle coefficient even:** the middle coefficient of
$f(p x + q y, r x + s y)$ is $2apq + b(ps + qr) + 2crs$, even when $b$ is. So a form equivalent (in any sense)
to one of Gauss's forms is again one of Gauss's forms. -/
theorem even_b_subst {f : BinQF} (hf : Even f.b) (p q r s : ℤ) : Even (subst p q r s f).b := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨f.a * p * q + k * (p * s + q * r) + f.c * r * s, ?_⟩
  simp only [subst, b_mk, hk]; ring

/-- **Gauss's transformation formulas** (*Disq. Arith.* Art. 157): the substitution $x = \alpha x' + \beta y'$,
$y = \gamma x' + \delta y'$ carries $(a, b, c)$ to $(a', b', c')$ with
$$a' = a\alpha^2 + 2b\alpha\gamma + c\gamma^2,\quad b' = a\alpha\beta + b(\alpha\delta + \beta\gamma) + c\gamma\delta,
\quad c' = a\beta^2 + 2b\beta\delta + c\delta^2 .$$ -/
@[kb "gauss1801" "Art. 157, pp. 170-171"]
theorem subst_gaussForm (a b c α β γ δ : ℤ) :
    subst α β γ δ (gaussForm a b c) =
      gaussForm (a * α ^ 2 + 2 * b * α * γ + c * γ ^ 2) (a * α * β + b * (α * δ + β * γ) + c * γ * δ)
        (a * β ^ 2 + 2 * b * β * δ + c * δ ^ 2) := by
  apply ext_abc <;> simp [subst]; ring

/-- **Gauss's determinant changes by the square of the determinant of the substitution** (*Disq. Arith.*
Art. 157): $b'^2 - a'c' = (\alpha\delta - \beta\gamma)^2 (b^2 - ac)$. -/
@[kb "gauss1801" "Art. 157, p. 171"]
theorem gaussDet_subst (a b c α β γ δ : ℤ) :
    gaussDet (a * α ^ 2 + 2 * b * α * γ + c * γ ^ 2) (a * α * β + b * (α * δ + β * γ) + c * γ * δ)
        (a * β ^ 2 + 2 * b * β * δ + c * δ ^ 2) = (α * δ - β * γ) ^ 2 * gaussDet a b c := by
  simp only [gaussDet]; ring

/-- **Substitutions compose:** substituting $\begin{pmatrix} p & q \\ r & s \end{pmatrix}$ and then
$\begin{pmatrix} p' & q' \\ r' & s' \end{pmatrix}$ is substituting the product
$\begin{pmatrix} p & q \\ r & s \end{pmatrix}\begin{pmatrix} p' & q' \\ r' & s' \end{pmatrix}$:
$(f \circ g) \circ h = f \circ (g h)$. -/
theorem subst_subst (p q r s p' q' r' s' : ℤ) (f : BinQF) :
    subst p' q' r' s' (subst p q r s f) =
      subst (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') f := by
  apply ext_eval; intro x y
  simp only [eval_subst]; ring_nf

/-- The identity substitution. -/
theorem subst_one (f : BinQF) : subst 1 0 0 1 f = f := by
  apply ext_eval; intro x y; simp only [eval_subst]; ring_nf

end QuadFormsKB.Historical.Gauss
