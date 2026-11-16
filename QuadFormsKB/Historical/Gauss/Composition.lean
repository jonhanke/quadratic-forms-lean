import QuadFormsKB.Historical.Gauss.Forms
import QuadFormsKB.Literature.Cassels.Ch14.Group

/-!
# Gauss's composition of binary forms (Disquisitiones Arithmeticae, Arts. 235-236, 249)

(Gauss's existence of composition, Art. 236), with the definition of Art. 235
 and the group structure of Art. 249.

## Gauss's definition (Art. 235)

A form $F$ is **transformable into the product** $f f'$ (`TransformsInto`) if a bilinear substitution
$$X = p\,xx' + p'\,xy' + p''\,yx' + p'''\,yy', \qquad Y = q\,xx' + q'\,xy' + q''\,yx' + q'''\,yy'$$
carries $F(X, Y)$ into $f(x, y) f'(x', y')$. Its six numbers (`minors`)
$P = pq' - qp'$, $Q = pq'' - qp''$, $R = pq''' - qp'''$, $S = p'q'' - q'p''$, $T = p'q''' - q'p'''$,
$U = p''q''' - q''p'''$ satisfy (third conclusion of Art. 235) $P = an'$, $R - S = 2bn'$, $U = cn'$,
$Q = a'n$, $R + S = 2b'n$, $T = c'n$ for rational $n, n'$ with $d = Dn^2$, $d' = Dn'^2$. $F$ is **compounded of**
$f$ and $f'$ (`IsCompounded`) if moreover the six numbers have no common divisor; it is compounded **directly** of
both if $n, n' > 0$. In the library's coefficients ($b_{\text{lib}} = 2b$) the relations read
$R - S = b_{\text{lib}}\,n'$, $R + S = b'_{\text{lib}}\,n$. Indices of $p, q$ are $0$-based: Gauss's
$p, p', p'', p'''$ are `p 0, p 1, p 2, p 3`.

`IsCompounded` is Gauss's definition in full (coprime minors and direct orientation), stricter than the library's
`Composition.IsGaussComposite` (Cassels' paraphrase, no orientation and no coprimality).

## What is proved

* `isCompounded_comp`: Dirichlet's composite $[a_1a_2, b, c]$ of concordant forms $[a_1, b, a_2c]$,
  $[a_2, b, a_1c]$ (the library's `Composition.comp`, Cassels Ch. 14, (2.9)) is compounded directly of them in
  Gauss's sense, with $n = n' = 1$.
* `art236_exists_compounded_of_classes`: for primitive forms $f, f'$ of the same discriminant $D \ne 0$ there are
  forms properly equivalent to them and a form compounded of these directly (Art. 236 for the classes of primitive
  forms of equal determinant).
* `art249_classes_group`: composition makes the proper classes of primitive forms of discriminant $D$ an abelian group
  in which the class of a Gauss composite is the product (wrapper of the library's
  `Composition.FormClass.instCommGroup` and `FormClass.mk_mul_mk`, Cassels Ch. 14, Thm. 2.1). For fundamental
  $D < 0$ this group is identified with the ideal class group by `Binary.slClassEquiv` and `Binary.isFormClassGroup`.

## What is stated only

* `GaussCompositionExistence` (Art. 236 as Gauss states it): **any** two forms, primitive or not, whose determinants
  are in the ratio of two squares, have a form compounded directly of them (of the given forms themselves, not of
  equivalent ones). Gauss's proof (the parameters $\Omega$, the Bezout step $\mathfrak P$, the integrality of
  $A, B, C$) is a long explicit computation not carried out here.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-- **The bilinear form** $p_0\,xx' + p_1\,xy' + p_2\,yx' + p_3\,yy'$ (Gauss's
$p\,xx' + p'\,xy' + p''\,yx' + p'''\,yy'$, Art. 235). -/
def bilin (p : Fin 4 → ℤ) (x y x' y' : ℤ) : ℤ := p 0 * x * x' + p 1 * x * y' + p 2 * y * x' + p 3 * y * y'

/-- **$F$ is transformable into the product $f f'$** (Gauss, *Disq. Arith.* Art. 235): the bilinear substitution
$X = \sum p_i (\cdot)$, $Y = \sum q_i (\cdot)$ (`bilin`) gives $F(X, Y) = f(x, y)\,f'(x', y')$ identically. -/
@[kb "gauss1801" "Art. 235, p. 340"]
def TransformsInto (F f f' : BinQF) (p q : Fin 4 → ℤ) : Prop :=
  ∀ x y x' y' : ℤ, F.eval (bilin p x y x' y') (bilin q x y x' y') = f.eval x y * f'.eval x' y'

/-- **Gauss's six numbers** $P, Q, R, S, T, U$ (Art. 235): the $2 \times 2$ minors
$P = p_0q_1 - q_0p_1$, $Q = p_0q_2 - q_0p_2$, $R = p_0q_3 - q_0p_3$, $S = p_1q_2 - q_1p_2$, $T = p_1q_3 - q_1p_3$,
$U = p_2q_3 - q_2p_3$, as the vector $(P, Q, R, S, T, U)$ indexed $0, \dots, 5$. -/
@[kb "gauss1801" "Art. 235, p. 340"]
def minors (p q : Fin 4 → ℤ) : Fin 6 → ℤ :=
  ![p 0 * q 1 - q 0 * p 1, p 0 * q 2 - q 0 * p 2, p 0 * q 3 - q 0 * p 3,
    p 1 * q 2 - q 1 * p 2, p 1 * q 3 - q 1 * p 3, p 2 * q 3 - q 2 * p 3]

/-- **$F$ is compounded directly of $f$ and $f'$** (Gauss, *Disq. Arith.* Art. 235, pp. 340-344): there is a bilinear
substitution transforming $F$ into $f f'$ (`TransformsInto`) whose six numbers $P, \dots, U$ have no common divisor
other than $\pm 1$, and with **positive** rationals $n, n'$ ("directly" in both factors)
$$P = a n',\quad R - S = b n',\quad U = c n',\qquad Q = a' n,\quad R + S = b' n,\quad T = c' n,$$
where $f = a x^2 + b x y + c y^2$ and $f' = a' x^2 + b' x y + c' y^2$ in the library's coefficients (Gauss's
$2b$, $2b'$ are the library's $b$, $b'$). -/
@[kb "gauss1801" "Art. 235, pp. 340-344"]
def IsCompounded (F f f' : BinQF) : Prop :=
  ∃ p q : Fin 4 → ℤ, TransformsInto F f f' p q ∧ (∀ d : ℤ, (∀ i, d ∣ minors p q i) → IsUnit d) ∧
    ∃ n n' : ℚ, 0 < n ∧ 0 < n' ∧
      (minors p q 0 : ℚ) = f.a * n' ∧ ((minors p q 2 : ℚ) - minors p q 3) = f.b * n' ∧
      (minors p q 5 : ℚ) = f.c * n' ∧ (minors p q 1 : ℚ) = f'.a * n ∧
      ((minors p q 2 : ℚ) + minors p q 3) = f'.b * n ∧ (minors p q 4 : ℚ) = f'.c * n

/-- **Gauss, *Disq. Arith.* Art. 236, as stated:** for **any** two of Gauss's forms
$f = (a, b, c)$, $f' = (a', b', c')$ with nonzero determinants $d, d'$ in the ratio of two squares
($d k^2 = d' k'^2$ for some nonzero integers $k, k'$) there is a form $F = (A, B, C)$ compounded directly of $f$ and
$f'$. Stated, not proved: see `art236_exists_compounded_of_classes` for what is proved. -/
@[kb "gauss1801" "Art. 236, pp. 350-353"]
def GaussCompositionExistence : Prop :=
  ∀ a b c a' b' c' : ℤ, gaussDet a b c ≠ 0 → gaussDet a' b' c' ≠ 0 →
    (∃ k k' : ℤ, k ≠ 0 ∧ k' ≠ 0 ∧ gaussDet a b c * k ^ 2 = gaussDet a' b' c' * k' ^ 2) →
    ∃ A B C : ℤ, IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c')

/-- **Dirichlet's composite is compounded in Gauss's sense** (Gauss, *Disq. Arith.* Arts. 235-236; Dirichlet's
united forms): for concordant forms $f_1 = [a_1, b, a_2c]$, $f_2 = [a_2, b, a_1c]$ (`Composition.Concordant`) with
$f_1$ primitive, the form $[a_1a_2, b, c]$ (`Composition.comp`) is compounded directly of $f_1$ and $f_2$, by
$X = xx' - c\,yy'$, $Y = a_1\,xy' + a_2\,yx' + b\,yy'$; its six numbers are
$(a_1, a_2, b, 0, a_1c, a_2c)$ and $n = n' = 1$. -/
@[kb "gauss1801" "Arts. 235-236, pp. 340-353"]
theorem isCompounded_comp {f₁ f₂ : BinQF} (h : Concordant f₁ f₂) (h₁ : f₁.IsPrimitive) :
    IsCompounded (comp f₁ f₂) f₁ f₂ := by
  obtain ⟨h0, hb, hD, k, hk⟩ := h
  have ha₁ : f₁.a ≠ 0 := left_ne_zero_of_mul h0
  have ha₂ : f₂.a ≠ 0 := right_ne_zero_of_mul h0
  have h4 : 4 * f₁.a * f₂.a ≠ 0 := by
    intro h'; apply h0; linarith
  have hq : (f₁.b ^ 2 - f₁.disc) / (4 * f₁.a * f₂.a) = k := by
    rw [hk]; exact Int.mul_ediv_cancel_left _ h4
  have d1 : f₁.disc = f₁.b ^ 2 - 4 * f₁.a * f₁.c := rfl
  have d2 : f₂.disc = f₂.b ^ 2 - 4 * f₂.a * f₂.c := rfl
  have e1 : f₁.c = f₂.a * k := by
    apply mul_left_cancel₀ (show (4 * f₁.a : ℤ) ≠ 0 by intro h'; apply ha₁; linarith)
    linear_combination d1 + hk
  have e2 : f₂.c = f₁.a * k := by
    apply mul_left_cancel₀ (show (4 * f₂.a : ℤ) ≠ 0 by intro h'; apply ha₂; linarith)
    linear_combination d2 + hk - (f₁.b + f₂.b) * hb + hD
  refine ⟨![1, 0, 0, -k], ![0, f₁.a, f₂.a, f₁.b], ?_, ?_, 1, 1, one_pos, one_pos, ?_⟩
  · intro x y x' y'
    simp only [bilin, BinQF.eval_eq, comp, a_mk, b_mk, c_mk, hq, e1, e2, ← hb]
    simp
    ring
  · intro d hd
    have h0' := hd 0
    have h2' := hd 2
    have h5' := hd 5
    simp [minors] at h0' h2' h5'
    exact h₁ d h0' h2' (by rw [e1]; simpa [mul_comm] using h5')
  · simp [minors, e1, e2, ← hb]

/-- **Art. 236 for classes of primitive forms of the same determinant:** if $f, f'$ are primitive of the same
discriminant $D \ne 0$, there are $g \sim f$, $g' \sim f'$ (proper equivalence) and a primitive form $F$ of
discriminant $D$ compounded directly of $g$ and $g'$. (Gauss composes the given forms themselves; by his Art. 239
the class of the composite depends only on the classes, which is how the group law below is used.) -/
@[kb "gauss1801" "Art. 236, pp. 350-353"]
theorem art236_exists_compounded_of_classes {f f' : BinQF} (hf : f.IsPrimitive) (hf' : f'.IsPrimitive)
    (hD : f.disc = f'.disc) (hD0 : f.disc ≠ 0) :
    ∃ g g' F : BinQF, SLEquiv f g ∧ SLEquiv f' g' ∧ IsCompounded F g g' ∧ F.IsPrimitive ∧ F.disc = f.disc := by
  obtain ⟨g, g', e, e', hc, -, -⟩ := Composition.exists_concordant hf hf' hD hD0 (M := 1) one_ne_zero
  have hg : g.IsPrimitive := Composition.SLEquiv.isPrimitive e hf
  have hg' : g'.IsPrimitive := Composition.SLEquiv.isPrimitive e' hf'
  exact ⟨g, g', comp g g', e, e', isCompounded_comp hc hg, isPrimitive_comp hc hg hg',
    (disc_comp hc).trans (Composition.SLEquiv.disc_eq e).symm⟩

/-- **Composition makes the classes a group** (Gauss, *Disq. Arith.* Art. 249; wrapper of the library's
`Composition.FormClass.instCommGroup`, Cassels Ch. 14, Thm. 2.1): for a discriminant $D \ne 0$, $D \equiv 0, 1
\pmod 4$, the proper classes of primitive forms of discriminant $D$ (`Composition.FormClass D`) form a finite abelian
group whose unit is the principal class and in which, for any classes $\mathfrak C_1, \mathfrak C_2$, there are
representatives $f_1 \in \mathfrak C_1$, $f_2 \in \mathfrak C_2$ and a form $F$ compounded directly of $f_1, f_2$ in
Gauss's sense whose class is $\mathfrak C_1 \mathfrak C_2$. -/
@[kb "gauss1801" "Art. 249, pp. 381-383"]
theorem art249_classes_group (D : ℤ) [NonzeroDisc D] (C₁ C₂ : FormClass D) :
    ∃ f₁ f₂ F : PrimForm D, FormClass.mk f₁ = C₁ ∧ FormClass.mk f₂ = C₂ ∧ IsCompounded F.1 f₁.1 f₂.1 ∧
      FormClass.mk F = C₁ * C₂ := by
  obtain ⟨f₁, rfl⟩ := FormClass.mk_surjective C₁
  obtain ⟨f₂, rfl⟩ := FormClass.mk_surjective C₂
  have hD0 : f₁.1.disc ≠ 0 := by rw [f₁.2.2]; exact NonzeroDisc.ne_zero
  obtain ⟨g₁, g₂, e₁, e₂, hc, -, -⟩ :=
    Composition.exists_concordant f₁.2.1 f₂.2.1 (f₁.2.2.trans f₂.2.2.symm) hD0 (M := 1) one_ne_zero
  let G₁ : PrimForm D := ⟨g₁, Composition.SLEquiv.isPrimitive e₁ f₁.2.1, (Composition.SLEquiv.disc_eq e₁).symm.trans f₁.2.2⟩
  let G₂ : PrimForm D := ⟨g₂, Composition.SLEquiv.isPrimitive e₂ f₂.2.1, (Composition.SLEquiv.disc_eq e₂).symm.trans f₂.2.2⟩
  have m₁ : FormClass.mk G₁ = FormClass.mk f₁ := FormClass.mk_eq_mk.mpr e₁.symm
  have m₂ : FormClass.mk G₂ = FormClass.mk f₂ := FormClass.mk_eq_mk.mpr e₂.symm
  refine ⟨G₁, G₂, FormClass.PrimForm.comp G₁ G₂ hc, m₁, m₂, isCompounded_comp hc G₁.2.1, ?_⟩
  rw [← FormClass.mk_mul_mk G₁ G₂ hc, m₁, m₂]

/-- **The class group of forms is finite** (Gauss, *Disq. Arith.* Art. 223 and Section V passim; wrapper of the
library's `Composition.FormClass.finite`). -/
theorem finite_classes (D : ℤ) [NonzeroDisc D] : Finite (FormClass D) := FormClass.finite

end QuadFormsKB.Historical.Gauss
