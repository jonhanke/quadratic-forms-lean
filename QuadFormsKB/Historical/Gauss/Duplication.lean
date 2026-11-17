import QuadFormsKB.Historical.Gauss.Composition
import QuadFormsKB.Literature.Cassels.Ch14.Genus

/-!
# Arndt's principal genus theorem: every form of the principal genus is a duplicate (Gauss, Arts. 286-287)

(F. Arndt, J. reine angew. Math. 56 (1859), 72-78, reported in Dickson, *History*
III, p. 84, footnote 5), Arndt's elementary proof of Gauss's theorem (*Disq. Arith.* Art. 287 III,
): every properly primitive class of the principal genus arises by duplication.

**Arndt's statement.** Let $f = (a, b, c)$ (Gauss's $a x^2 + 2bxy + cy^2$) be properly primitive and positive, of the
principal genus, with determinant $D$ divisible by no square $> 1$. Then $f$ represents a square $h^2$ prime to $D$,
and $f$ is properly equivalent to a form $(h^2, l, n)$, which is the duplicate of the properly primitive form
$(h, l, nh)$ if $h$ is odd (of $(2h, l + h, l + \frac h2(n + 1))$ if $h$ is even).

**What is proved** (`arndt_principal_genus`): Arndt's statement **without** the hypotheses "positive" and "$D$
squarefree" (any nonzero determinant), and always with $h$ **odd** (prime to $2D$), so that Arndt's even case is not
needed. "Principal genus" is the library's `Composition.InPrincipalGenus`: equivalent to the principal form
$(1, 0, -D)$ over $\mathbb{R}$ and over every $\mathbb{Z}_p$ (the modern form of Gauss's "all characters equal to those
of the principal form"; the two agree for primitive forms by Gauss's Arts. 229-231 and the local classification of
binary forms, which is not re-proved here). The ingredients are the library's
`Composition.exists_eval_sq_of_inPrincipalGenus` (Cassels Ch. 14, proof of Thm. 3.1: $f$ represents properly a
square $w^2$ with $w$ prime to $2D$), Gauss's Art. 168 (a properly represented number is the first coefficient of a
properly equivalent form), and the explicit duplication `duplicate_isCompounded` below.

The class-level statement (a class lies in the principal genus iff it is a square in the class group) is
`principal_genus_iff_square` (wrapper of the library's `Composition.thm_3_1`, every discriminant $D \ne 0$; for
fundamental $D < 0$ also `Binary.principalGenus_eq_sq`).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-- **Arndt's duplication formula** (Arndt 1859; Gauss, *Disq. Arith.* Art. 286 II): if Gauss's form $(h, l, nh)$
(i.e. $h x^2 + 2l xy + nh y^2$) is properly primitive, then $(h^2, l, n)$ is compounded directly of $(h, l, nh)$ with
itself, i.e. is its duplicate, by $X = xx' - n\,yy'$, $Y = h\,xy' + h\,yx' + 2l\,yy'$. -/
@[kb "arndt1859" "pp. 72-78 (via Dickson, History III, p. 84, fn. 5)"]
theorem duplicate_isCompounded (h l n : ℤ) (hp : (gaussForm h l (n * h)).IsPrimitive) :
    IsCompounded (gaussForm (h ^ 2) l n) (gaussForm h l (n * h)) (gaussForm h l (n * h)) := by
  have hh : h ≠ 0 := by
    rintro rfl
    have := hp 2 (by simp) (by simp) (by simp)
    exact absurd this (by decide)
  have hc : Concordant (gaussForm h l (n * h)) (gaussForm h l (n * h)) := by
    refine ⟨mul_ne_zero (by simpa using hh) (by simpa using hh), rfl, rfl, ⟨n, ?_⟩⟩
    simp only [disc, a_gaussForm, b_gaussForm, c_gaussForm]; ring
  have hcomp : comp (gaussForm h l (n * h)) (gaussForm h l (n * h)) = gaussForm (h ^ 2) l n := by
    have h4 : (4 * h * h : ℤ) ≠ 0 := by positivity
    apply ext_abc
    · simp [comp]; ring
    · simp [comp]
    · simp only [comp, c_mk, c_gaussForm, disc, a_gaussForm, b_gaussForm, c_gaussForm]
      rw [show (2 * l) ^ 2 - ((2 * l) ^ 2 - 4 * h * (n * h)) = 4 * h * h * n by ring]
      exact Int.mul_ediv_cancel_left _ h4
  rw [← hcomp]
  exact isCompounded_comp hc hp

/-- **Arndt's principal genus theorem** (Arndt, J. reine angew. Math. 56 (1859), 72-78;
Gauss, *Disq. Arith.* Art. 287 III), generalized to every nonzero determinant: let $f = (a, b, c)$ be one of Gauss's
forms, properly primitive, of determinant $D = b^2 - ac \ne 0$, in the principal genus. Then there are integers
$h, l, n$ with $h$ odd and prime to $D$ such that

* $f$ represents $h^2$ properly ($f(x, y) = h^2$ with $\gcd(x, y) = 1$),
* $f$ is properly equivalent to $(h^2, l, n)$,
* $(h, l, nh)$ is properly primitive and $(h^2, l, n)$ is compounded directly of $(h, l, nh)$ with itself.

So every form of the principal genus arises by duplication. Arndt's hypothesis that $f$ is properly primitive is kept
as in the source (`_hp`) but is not needed by the proof. -/
@[kb "arndt1859" "pp. 72-78 (via Dickson, History III, p. 84, fn. 5)"]
theorem arndt_principal_genus {a b c : ℤ} (_hp : (gaussForm a b c).IsPrimitive) (hD : gaussDet a b c ≠ 0)
    (hg : InPrincipalGenus (gaussForm a b c)) :
    ∃ h l n : ℤ, Odd h ∧ IsCoprime h (gaussDet a b c) ∧
      (∃ x y : ℤ, IsCoprime x y ∧ (gaussForm a b c).eval x y = h ^ 2) ∧
      SLEquiv (gaussForm a b c) (gaussForm (h ^ 2) l n) ∧
      (gaussForm h l (n * h)).IsPrimitive ∧
      IsCompounded (gaussForm (h ^ 2) l n) (gaussForm h l (n * h)) (gaussForm h l (n * h)) := by
  set f := gaussForm a b c with hf
  have hdisc : f.disc = 4 * gaussDet a b c := disc_gaussForm a b c
  have hD' : f.disc ≠ 0 := by rw [hdisc]; exact mul_ne_zero (by norm_num) hD
  obtain ⟨w, x, y, hxy, hw, hv⟩ := exists_eval_sq_of_inPrincipalGenus hD' hg
  obtain ⟨g, e, ha⟩ := Composition.exists_sLEquiv_a_of_eval (f := f) hxy
  -- `g` is again one of Gauss's forms
  have hev : Even g.b := by
    obtain ⟨p, q, r, s, -, rfl⟩ := (sLEquiv_iff _ _).1 e
    exact even_b_subst (by simp [hf]) p q r s
  obtain ⟨l, hl⟩ := hev
  have hgdisc : g.disc = f.disc := (Composition.SLEquiv.disc_eq e).symm
  have hgeq : g = gaussForm (w ^ 2) l g.c := ext_abc (by simp [ha, hv]) (by simp [hl]; ring) (by simp)
  -- `D = l² - w² n`
  have hdet : gaussDet a b c = l ^ 2 - w ^ 2 * g.c := by
    have : g.disc = 4 * (l ^ 2 - w ^ 2 * g.c) := by rw [hgeq, disc_gaussForm]; rfl
    linarith
  have hw2 : IsCoprime w 2 := hw.of_mul_right_left
  have hwD : IsCoprime w (gaussDet a b c) := by
    rw [hdisc] at hw
    exact (hw.of_mul_right_right).of_mul_right_right
  have hodd : Odd w := by
    rcases Int.even_or_odd w with ⟨k, hk⟩ | ho
    · exfalso
      have : (2 : ℤ) ∣ w := ⟨k, by rw [hk]; ring⟩
      exact absurd (hw2.isUnit_of_dvd' this (dvd_refl 2)) (by decide)
    · exact ho
  have hprim : (gaussForm w l (g.c * w)).IsPrimitive := by
    intro d hd1 hd2 _
    simp only [a_gaussForm, b_gaussForm] at hd1 hd2
    have hdD : d ∣ 2 * f.disc := by
      rw [hdisc, hdet]
      have h1 : d ∣ (2 * l) * (2 * l) := dvd_mul_of_dvd_left hd2 _
      have h2 : d ∣ w * (4 * w * g.c) := dvd_mul_of_dvd_left hd1 _
      have : 2 * (4 * (l ^ 2 - w ^ 2 * g.c)) = 2 * ((2 * l) * (2 * l)) - 2 * (w * (4 * w * g.c)) := by ring
      rw [this]
      exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
    exact hw.isUnit_of_dvd' hd1 hdD
  refine ⟨w, l, g.c, hodd, hwD, ⟨x, y, hxy, hv⟩, ?_, hprim, duplicate_isCompounded w l g.c hprim⟩
  rw [← hgeq]; exact e

/-- **Gauss's duplication theorem for classes** (*Disq. Arith.* Arts. 247 and 287 III; wrapper of the library's
`Composition.thm_3_1`, Cassels Ch. 14, Thm. 3.1): for every discriminant $D \ne 0$, the class of a primitive form
of discriminant $D$ is a square in the class group iff the form lies in the principal genus. -/
@[kb "gauss1801" "Art. 287 III, pp. 479-480"]
theorem principal_genus_iff_square {D : ℤ} [NonzeroDisc D] (f : PrimForm D) :
    (∃ C₁ : FormClass D, C₁ ^ 2 = FormClass.mk f) ↔ InPrincipalGenus f.1 :=
  thm_3_1 f

end QuadFormsKB.Historical.Gauss
