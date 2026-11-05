/-
# Conway–Sloane 1988, §8, Table 6: entries $s = 1$ with class number $h > 1$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, Table 6, p. 270.

The column $s = 1$ of Table 6 is $\zeta_{-d}(1)\sqrt d/\pi$. By (10), $\zeta_{-d}(1) = L(1, \psi)\,E$ with the Euler
factor $E = \prod_{p \mid 4d}(1 - \psi(p)/p)$, and Dirichlet's class number formula (`Binary.classNumberFormula_neg`)
gives $L(1, \psi) = \pi h/\sqrt{\lvert D\rvert}$ for a fundamental discriminant $D < -4$ (where $w = 2$). This file
treats the rows $d = 5, 6, 10, 13, 14, 15, 17, 21, 22, 23$, whose fundamental discriminants
$D = -20, -24, -40, -52, -56, -15, -68, -84, -88, -23$ have class numbers $h = 2, 2, 2, 2, 4, 2, 4, 4, 2, 3$.

**Class numbers.** By `Binary.card_slClasses`, $h(\mathbb Q(\sqrt D))$ is the number of proper
($\mathrm{SL}_2(\mathbb Z)$-) classes of primitive positive definite forms $ax^2 + bxy + cy^2$ of discriminant
$b^2 - 4ac = D$. Every such class contains exactly one *reduced* form, $-a < b \le a \le c$ with $b \ge 0$ if $a = c$
(Gauss). We obtain this from Conway–Sloane's reduction theory for forms $a^{b}c = ax^2 + 2bxy + cy^2$
(`ConwaySloane.Binary.exists_unique_reduced_pos`, condition (11), Sphere Packings Ch. 15) applied to the doubled form
$(2a)^{b}(2c) = 2(ax^2 + bxy + cy^2)$ (`dblForm`); condition (11) for $(2a)^{b}(2c)$ is exactly Gauss' condition.
The reduced forms of each discriminant are then listed by a finite search ($3a^2 \le \lvert D\rvert$, $\lvert b\rvert \le a$).

**Proves**
* `sLEquiv_iff_properEquiv_dblForm`, `exists_sLEquiv_reduced`, `eq_of_reduced_of_sLEquiv`: the comparison with the
  doubled forms, existence and uniqueness of reduced forms in each proper class.
* `classNumber_eq_card_of_reduced`: $h(\mathbb Q(\sqrt D))$ is the number of reduced forms of discriminant $D$.
* `classNumber_QField_neg_twenty`, … : $h(-20) = h(-24) = h(-40) = h(-52) = h(-15) = h(-88) = 2$,
  $h(-56) = h(-68) = h(-84) = 4$, $h(-23) = 3$.
* `LFunction_kronecker_one_of_classNumber`: $L(1, \psi) = h\pi/\sqrt{\lvert D\rvert}$ for $D < -4$.
* `table6_d_1` for $d = 5, 6, 10, 13, 14, 15, 17, 21, 22, 23$: the printed entries
  $1, 1, 1, 1, 2, 1, 2, 2, 1, \frac32$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6One
import QuadFormsKB.Literature.ConwaySloane.NormedIdealsForms

namespace QuadFormsKB.ConwaySloane.Mass

open Complex Finset QuadFormsKB.Binary
open QuadFormsKB.ConwaySloane.Binary (BinForm ProperEquiv IsReducedPos)
open scoped Real

/-! ### Reduced forms via the doubled form -/

/-- **The doubled form** of $f = ax^2 + bxy + cy^2$: Conway–Sloane's $(2a)^{b}(2c)$, i.e. the form
$2ax^2 + 2bxy + 2cy^2 = 2f$ with Gram matrix $\begin{pmatrix} 2a & b\\ b & 2c\end{pmatrix}$ (the Hessian of $f$). -/
def dblForm (f : BinQF) : BinForm := ⟨2 * f.a, f.b, 2 * f.c⟩

/-- **Proper equivalence is preserved by doubling:** $f \sim_{\mathrm{SL}} g$ iff the doubled forms are properly
equivalent in Conway–Sloane's sense ($B = MAM^{\mathrm t}$, $\det M = 1$). -/
theorem sLEquiv_iff_properEquiv_dblForm (f g : BinQF) :
    SLEquiv f g ↔ ProperEquiv (dblForm f) (dblForm g) := by
  rw [properEquiv_iff_sLEquiv, sLEquiv_iff, sLEquiv_iff]
  constructor
  · rintro ⟨p, q, r, s, hd, rfl⟩
    refine ⟨p, q, r, s, hd, BinQF.ext_abc ?_ ?_ ?_⟩ <;> simp [dblForm, toBinQF, BinQF.subst] <;> ring
  · rintro ⟨p, q, r, s, hd, h⟩
    have ha := congrArg BinQF.a h
    have hb := congrArg BinQF.b h
    have hc := congrArg BinQF.c h
    simp [dblForm, toBinQF, BinQF.subst] at ha hb hc
    refine ⟨p, q, r, s, hd, BinQF.ext_abc ?_ ?_ ?_⟩ <;> simp [BinQF.subst] <;> linarith

/-- **Existence of a reduced form** (Gauss): every positive definite form $f$ ($a > 0$, $b^2 - 4ac < 0$) is properly
equivalent to a form $g$ with $-a < b \le a \le c$ and $b \ge 0$ if $a = c$ (condition (11) of Conway–Sloane for the
doubled form $(2a)^{b}(2c)$). -/
theorem exists_sLEquiv_reduced (f : BinQF) (ha : 0 < f.a) (hd : f.disc < 0) :
    ∃ g : BinQF, SLEquiv f g ∧ IsReducedPos (2 * g.a) g.b (2 * g.c) := by
  have hdet : 0 < (dblForm f).det := by
    simp only [BinQF.disc] at hd
    simp only [dblForm, ConwaySloane.Binary.BinForm.det]
    linarith
  obtain ⟨g', e, hg'⟩ := ConwaySloane.Binary.exists_reduced_pos (dblForm f) (by simp [dblForm]; omega) hdet
  rw [properEquiv_iff_sLEquiv, sLEquiv_iff] at e
  obtain ⟨p, q, r, s, hps, h⟩ := e
  refine ⟨BinQF.subst p q r s f, (sLEquiv_iff _ _).2 ⟨p, q, r, s, hps, rfl⟩, ?_⟩
  have ha' := congrArg BinQF.a h
  have hb' := congrArg BinQF.b h
  have hc' := congrArg BinQF.c h
  simp [dblForm, toBinQF, BinQF.subst] at ha' hb' hc'
  have e1 : 2 * (BinQF.subst p q r s f).a = g'.a := by simp [BinQF.subst]; linarith
  have e2 : (BinQF.subst p q r s f).b = g'.b := by simp [BinQF.subst]; linarith
  have e3 : 2 * (BinQF.subst p q r s f).c = g'.c := by simp [BinQF.subst]; linarith
  rw [e1, e2, e3]
  exact hg'

/-- **Uniqueness of the reduced form** (Gauss): two properly equivalent forms that are both reduced
($-a < b \le a \le c$, $b \ge 0$ if $a = c$) are equal (`ConwaySloane.Binary.reduced_pos_unique` for the doubled
forms). -/
theorem eq_of_reduced_of_sLEquiv {f g : BinQF} (hf : IsReducedPos (2 * f.a) f.b (2 * f.c))
    (hg : IsReducedPos (2 * g.a) g.b (2 * g.c)) (h : SLEquiv f g) : f = g := by
  have := ConwaySloane.Binary.reduced_pos_unique (f := dblForm f) (g := dblForm g) hf hg
    ((sLEquiv_iff_properEquiv_dblForm f g).1 h)
  simp only [dblForm, BinForm.mk.injEq] at this
  exact BinQF.ext_abc (by omega) (by omega) (by omega)

/-- **The class number is the number of reduced forms:** for a fundamental discriminant $D < 0$ and a finite set $S$
of triples $(a, b, c)$ which is exactly the set of reduced forms $ax^2 + bxy + cy^2$ ($-a < b \le a \le c$, $b \ge 0$
if $a = c$) with $b^2 - 4ac = D$, $h(\mathbb Q(\sqrt D)) = \lvert S\rvert$. The hypothesis `hsound` says every element
of $S$ is reduced of discriminant $D$, and `hcomp` that every reduced form of discriminant $D$ lies in $S$. -/
theorem classNumber_eq_card_of_reduced (D : ℤ) [IsQuadDisc D] (hD : D < 0) (S : Finset (ℤ × ℤ × ℤ))
    (hsound : ∀ t ∈ S, IsReducedPos (2 * t.1) t.2.1 (2 * t.2.2) ∧ t.2.1 ^ 2 - 4 * t.1 * t.2.2 = D)
    (hcomp : ∀ a b c : ℤ, IsReducedPos (2 * a) b (2 * c) → b ^ 2 - 4 * a * c = D → (a, b, c) ∈ S) :
    NumberField.classNumber (QField D) = S.card := by
  have hmem : ∀ t : S, (BinQF.mk t.1.1 t.1.2.1 t.1.2.2).disc = D ∧ (BinQF.mk t.1.1 t.1.2.1 t.1.2.2).PosDef ∧
      (BinQF.mk t.1.1 t.1.2.1 t.1.2.2).IsPrimitive := by
    intro t
    obtain ⟨hr, hd⟩ := hsound t.1 t.2
    refine (mem_primPosForm_iff IsQuadDisc.fund hD _).2 ⟨?_, ?_⟩
    · simp [BinQF.disc, hd]
    · simp only [BinQF.a_mk]; obtain ⟨h1, h2, -⟩ := hr; omega
  let Φ : S → Quotient (slSetoid D) := fun t => Quotient.mk _ ⟨_, hmem t⟩
  have hinj : Function.Injective Φ := by
    intro t t' h
    have h' := Quotient.exact h
    have := eq_of_reduced_of_sLEquiv (by simpa using (hsound t.1 t.2).1) (by simpa using (hsound t'.1 t'.2).1) h'
    have ha := congrArg BinQF.a this
    have hb := congrArg BinQF.b this
    have hc := congrArg BinQF.c this
    simp only [BinQF.a_mk, BinQF.b_mk, BinQF.c_mk] at ha hb hc
    exact Subtype.ext (Prod.ext ha (Prod.ext hb hc))
  have hsurj : Function.Surjective Φ := by
    intro x
    induction x using Quotient.inductionOn with
    | h f =>
      obtain ⟨g, hfg, hg⟩ := exists_sLEquiv_reduced f.1 f.a_pos (by rw [f.2.1]; exact hD)
      have hdg : g.disc = D := by
        obtain ⟨p, q, r, s, hps, rfl⟩ := (sLEquiv_iff _ _).1 hfg
        rw [BinQF.disc_subst_of_det _ _ _ _ _ (by rw [hps]; norm_num), f.2.1]
      have hgS : (g.a, g.b, g.c) ∈ S := hcomp _ _ _ hg (by rw [← hdg, BinQF.disc])
      refine ⟨⟨_, hgS⟩, Quotient.sound ?_⟩
      have hg' : BinQF.mk g.a g.b g.c = g := BinQF.ext_abc (by simp) (by simp) (by simp)
      change SLEquiv (BinQF.mk g.a g.b g.c) f.1
      rw [hg']
      exact hfg.symm
  rw [← card_slClasses hD, ← Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe]

/-! ### The class numbers -/

/-- $h(\mathbb Q(\sqrt{-20})) = h(\mathbb Q(\sqrt{-5})) = 2$: the reduced forms of discriminant $-20$ are
$x^2 + 5y^2$ and $2x^2 + 2xy + 3y^2$. -/
theorem classNumber_QField_neg_twenty : NumberField.classNumber (QField (-20)) = 2 := by
  rw [classNumber_eq_card_of_reduced (-20) (by norm_num) {(1, 0, 5), (2, 2, 3)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 2 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-24})) = h(\mathbb Q(\sqrt{-6})) = 2$: the reduced forms of discriminant $-24$ are
$x^2 + 6y^2$ and $2x^2 + 3y^2$. -/
theorem classNumber_QField_neg_twentyfour : NumberField.classNumber (QField (-24)) = 2 := by
  rw [classNumber_eq_card_of_reduced (-24) (by norm_num) {(1, 0, 6), (2, 0, 3)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 2 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-40})) = h(\mathbb Q(\sqrt{-10})) = 2$: the reduced forms of discriminant $-40$ are
$x^2 + 10y^2$ and $2x^2 + 5y^2$. -/
theorem classNumber_QField_neg_forty : NumberField.classNumber (QField (-40)) = 2 := by
  rw [classNumber_eq_card_of_reduced (-40) (by norm_num) {(1, 0, 10), (2, 0, 5)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 3 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-52})) = h(\mathbb Q(\sqrt{-13})) = 2$: the reduced forms of discriminant $-52$ are
$x^2 + 13y^2$ and $2x^2 + 2xy + 7y^2$. -/
theorem classNumber_QField_neg_fiftytwo : NumberField.classNumber (QField (-52)) = 2 := by
  rw [classNumber_eq_card_of_reduced (-52) (by norm_num) {(1, 0, 13), (2, 2, 7)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 4 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-56})) = h(\mathbb Q(\sqrt{-14})) = 4$: the reduced forms of discriminant $-56$ are
$x^2 + 14y^2$, $2x^2 + 7y^2$ and $3x^2 \pm 2xy + 5y^2$. -/
theorem classNumber_QField_neg_fiftysix : NumberField.classNumber (QField (-56)) = 4 := by
  rw [classNumber_eq_card_of_reduced (-56) (by norm_num) {(1, 0, 14), (2, 0, 7), (3, 2, 5), (3, -2, 5)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl | rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 4 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-15})) = 2$: the reduced forms of discriminant $-15$ are $x^2 + xy + 4y^2$ and
$2x^2 + xy + 2y^2$. -/
theorem classNumber_QField_neg_fifteen : NumberField.classNumber (QField (-15)) = 2 := by
  rw [classNumber_eq_card_of_reduced (-15) (by norm_num) {(1, 1, 4), (2, 1, 2)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 2 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-68})) = h(\mathbb Q(\sqrt{-17})) = 4$: the reduced forms of discriminant $-68$ are
$x^2 + 17y^2$, $2x^2 + 2xy + 9y^2$ and $3x^2 \pm 2xy + 6y^2$. -/
theorem classNumber_QField_neg_sixtyeight : NumberField.classNumber (QField (-68)) = 4 := by
  rw [classNumber_eq_card_of_reduced (-68) (by norm_num) {(1, 0, 17), (2, 2, 9), (3, 2, 6), (3, -2, 6)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl | rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 4 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-84})) = h(\mathbb Q(\sqrt{-21})) = 4$: the reduced forms of discriminant $-84$ are
$x^2 + 21y^2$, $2x^2 + 2xy + 11y^2$, $3x^2 + 7y^2$ and $5x^2 + 4xy + 5y^2$. -/
theorem classNumber_QField_neg_eightyfour : NumberField.classNumber (QField (-84)) = 4 := by
  rw [classNumber_eq_card_of_reduced (-84) (by norm_num) {(1, 0, 21), (2, 2, 11), (3, 0, 7), (5, 4, 5)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl | rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 5 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-88})) = h(\mathbb Q(\sqrt{-22})) = 2$: the reduced forms of discriminant $-88$ are
$x^2 + 22y^2$ and $2x^2 + 11y^2$. -/
theorem classNumber_QField_neg_eightyeight : NumberField.classNumber (QField (-88)) = 2 := by
  rw [classNumber_eq_card_of_reduced (-88) (by norm_num) {(1, 0, 22), (2, 0, 11)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 5 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-- $h(\mathbb Q(\sqrt{-23})) = 3$: the reduced forms of discriminant $-23$ are $x^2 + xy + 6y^2$ and
$2x^2 \pm xy + 3y^2$. -/
theorem classNumber_QField_neg_twentythree : NumberField.classNumber (QField (-23)) = 3 := by
  rw [classNumber_eq_card_of_reduced (-23) (by norm_num) {(1, 1, 6), (2, 1, 3), (2, -1, 3)}]
  · rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro t (rfl | rfl | rfl) <;> decide
  · intro a b c hr hd
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have ha : a ≤ 2 := by nlinarith
    have ha0 : 0 < a := by omega
    have hb1 : -a < b := by omega
    have hb2 : b ≤ a := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    interval_cases a <;> interval_cases b <;> omega

/-! ### $L(1, \psi)$ -/

/-- **$L(1, \psi) = h\pi/\sqrt{\lvert D\rvert}$** for the Kronecker character $\psi$ of a fundamental discriminant
$D < -4$ with class number $h$ (Dirichlet's class number formula `classNumberFormula_neg`, with $w = 2$). -/
theorem LFunction_kronecker_one_of_classNumber (D : ℤ) [IsQuadDisc D] (hD : D < -4) (h : ℕ)
    (hh : NumberField.classNumber (QField D) = h) :
    (kroneckerChar D).LFunction 1 = (((h : ℝ) * π / Real.sqrt |(D : ℝ)| : ℝ) : ℂ) := by
  have hf := classNumberFormula_neg (D := D) (by omega)
  have h3 : D ≠ -3 := by omega
  have h4 : D ≠ -4 := by omega
  rw [hh, torsionOrder_of_neg (by omega)] at hf
  simp only [h3, h4, ↓reduceIte] at hf
  rw [hf]
  congr 1
  have : Real.sqrt |(D : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast (show D ≠ 0 by omega)))).ne'
  push_cast
  field_simp

/-- A character with $\chi(-1) = -1$ is not the trivial character. -/
theorem ne_one_of_apply_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ (-1) = -1) : χ ≠ 1 := by
  rintro rfl
  rw [MulChar.one_apply isUnit_one.neg] at h
  norm_num at h

/-- $\sqrt{k^2 m} = k\sqrt m$ for $k \ge 0$ (to simplify $\sqrt{\lvert D\rvert}$). -/
theorem sqrt_sq_mul (k m : ℝ) (hk : 0 ≤ k) : Real.sqrt (k ^ 2 * m) = k * Real.sqrt m := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hk]

/-! ### The entries -/

/-- $\zeta_{-5}(1) = \pi/\sqrt5$: $L(1,\psi) = 2\pi/\sqrt{20}$ ($h(-20) = 2$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 1)"]
theorem zetaD_neg_five_one : zetaD (-5) 1 = π / Real.sqrt 5 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg20 _ chiD_eq_changeLevel_neg5
    (ne_one_of_apply_neg_one _ psiNeg20_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-20) (by norm_num) 2 classNumber_QField_neg_twenty) _
    (psiNeg20_euler_neg5 1)]
  rw [show |((-20 : ℤ) : ℝ)| = 2 ^ 2 * 5 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 5 ≠ 0 := by positivity
  field_simp
  norm_num

/-- **Table 6, $d = 5$, $s = 1$** ($D = -5$): $\zeta_{-5}(1)\sqrt5/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 5, s = 1)"]
theorem table6_5_1 : zetaD (-5) 1 * Real.sqrt 5 / π = 1 := by
  rw [zetaD_neg_five_one]
  have h : Real.sqrt 5 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-6}(1) = \pi/\sqrt6$: $L(1,\psi) = 2\pi/\sqrt{24}$ ($h(-24) = 2$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 1)"]
theorem zetaD_neg_six_one : zetaD (-6) 1 = π / Real.sqrt 6 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg24 _ chiD_eq_changeLevel_neg6
    (ne_one_of_apply_neg_one _ psiNeg24_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-24) (by norm_num) 2 classNumber_QField_neg_twentyfour) _
    (psiNeg24_euler_neg6 1)]
  rw [show |((-24 : ℤ) : ℝ)| = 2 ^ 2 * 6 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 6 ≠ 0 := by positivity
  field_simp
  norm_num

/-- **Table 6, $d = 6$, $s = 1$** ($D = -6$): $\zeta_{-6}(1)\sqrt6/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 6, s = 1)"]
theorem table6_6_1 : zetaD (-6) 1 * Real.sqrt 6 / π = 1 := by
  rw [zetaD_neg_six_one]
  have h : Real.sqrt 6 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-10}(1) = \pi/\sqrt{10}$: $L(1,\psi) = 2\pi/\sqrt{40}$ ($h(-40) = 2$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 1)"]
theorem zetaD_neg_ten_one : zetaD (-10) 1 = π / Real.sqrt 10 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg40 _ chiD_eq_changeLevel_neg10
    (ne_one_of_apply_neg_one _ psiNeg40_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-40) (by norm_num) 2 classNumber_QField_neg_forty) _
    (psiNeg40_euler_neg10 1)]
  rw [show |((-40 : ℤ) : ℝ)| = 2 ^ 2 * 10 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 10 ≠ 0 := by positivity
  field_simp
  norm_num

/-- **Table 6, $d = 10$, $s = 1$** ($D = -10$): $\zeta_{-10}(1)\sqrt{10}/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 10, s = 1)"]
theorem table6_10_1 : zetaD (-10) 1 * Real.sqrt 10 / π = 1 := by
  rw [zetaD_neg_ten_one]
  have h : Real.sqrt 10 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-13}(1) = \pi/\sqrt{13}$: $L(1,\psi) = 2\pi/\sqrt{52}$ ($h(-52) = 2$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 1)"]
theorem zetaD_neg_thirteen_one : zetaD (-13) 1 = π / Real.sqrt 13 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg52 _ chiD_eq_changeLevel_neg13
    (ne_one_of_apply_neg_one _ psiNeg52_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-52) (by norm_num) 2 classNumber_QField_neg_fiftytwo) _
    (psiNeg52_euler_neg13 1)]
  rw [show |((-52 : ℤ) : ℝ)| = 2 ^ 2 * 13 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 13 ≠ 0 := by positivity
  field_simp
  norm_num

/-- **Table 6, $d = 13$, $s = 1$** ($D = -13$): $\zeta_{-13}(1)\sqrt{13}/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 13, s = 1)"]
theorem table6_13_1 : zetaD (-13) 1 * Real.sqrt 13 / π = 1 := by
  rw [zetaD_neg_thirteen_one]
  have h : Real.sqrt 13 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-14}(1) = 2\pi/\sqrt{14}$: $L(1,\psi) = 4\pi/\sqrt{56}$ ($h(-56) = 4$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 1)"]
theorem zetaD_neg_fourteen_one : zetaD (-14) 1 = 2 * π / Real.sqrt 14 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg56 _ chiD_eq_changeLevel_neg14
    (ne_one_of_apply_neg_one _ psiNeg56_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-56) (by norm_num) 4 classNumber_QField_neg_fiftysix) _
    (psiNeg56_euler_neg14 1)]
  rw [show |((-56 : ℤ) : ℝ)| = 2 ^ 2 * 14 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 14 ≠ 0 := by positivity
  field_simp
  ring

/-- **Table 6, $d = 14$, $s = 1$** ($D = -14$): $\zeta_{-14}(1)\sqrt{14}/\pi = 2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 14, s = 1)"]
theorem table6_14_1 : zetaD (-14) 1 * Real.sqrt 14 / π = 2 := by
  rw [zetaD_neg_fourteen_one]
  have h : Real.sqrt 14 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-15}(1) = \pi/\sqrt{15}$: $L(1,\psi) = 2\pi/\sqrt{15}$ ($h(-15) = 2$) times $1 - \psi(2)/2 = \frac12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 1)"]
theorem zetaD_neg_fifteen_one : zetaD (-15) 1 = π / Real.sqrt 15 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg15 _ chiD_eq_changeLevel_neg15
    (ne_one_of_apply_neg_one _ psiNeg15_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-15) (by norm_num) 2 classNumber_QField_neg_fifteen) _
    (psiNeg15_euler_neg15 1)]
  rw [show |((-15 : ℤ) : ℝ)| = 15 by norm_num]
  have h : Real.sqrt 15 ≠ 0 := by positivity
  norm_num
  field_simp

/-- **Table 6, $d = 15$, $s = 1$** ($D = -15$): $\zeta_{-15}(1)\sqrt{15}/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 15, s = 1)"]
theorem table6_15_1 : zetaD (-15) 1 * Real.sqrt 15 / π = 1 := by
  rw [zetaD_neg_fifteen_one]
  have h : Real.sqrt 15 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-17}(1) = 2\pi/\sqrt{17}$: $L(1,\psi) = 4\pi/\sqrt{68}$ ($h(-68) = 4$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 1)"]
theorem zetaD_neg_seventeen_one : zetaD (-17) 1 = 2 * π / Real.sqrt 17 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg68 _ chiD_eq_changeLevel_neg17
    (ne_one_of_apply_neg_one _ psiNeg68_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-68) (by norm_num) 4 classNumber_QField_neg_sixtyeight) _
    (psiNeg68_euler_neg17 1)]
  rw [show |((-68 : ℤ) : ℝ)| = 2 ^ 2 * 17 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 17 ≠ 0 := by positivity
  field_simp
  ring

/-- **Table 6, $d = 17$, $s = 1$** ($D = -17$): $\zeta_{-17}(1)\sqrt{17}/\pi = 2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 17, s = 1)"]
theorem table6_17_1 : zetaD (-17) 1 * Real.sqrt 17 / π = 2 := by
  rw [zetaD_neg_seventeen_one]
  have h : Real.sqrt 17 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-21}(1) = 2\pi/\sqrt{21}$: $L(1,\psi) = 4\pi/\sqrt{84}$ ($h(-84) = 4$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 1)"]
theorem zetaD_neg_twentyone_one : zetaD (-21) 1 = 2 * π / Real.sqrt 21 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg84 _ chiD_eq_changeLevel_neg21
    (ne_one_of_apply_neg_one _ psiNeg84_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-84) (by norm_num) 4 classNumber_QField_neg_eightyfour) _
    (psiNeg84_euler_neg21 1)]
  rw [show |((-84 : ℤ) : ℝ)| = 2 ^ 2 * 21 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 21 ≠ 0 := by positivity
  field_simp
  ring

/-- **Table 6, $d = 21$, $s = 1$** ($D = -21$): $\zeta_{-21}(1)\sqrt{21}/\pi = 2$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 21, s = 1)"]
theorem table6_21_1 : zetaD (-21) 1 * Real.sqrt 21 / π = 2 := by
  rw [zetaD_neg_twentyone_one]
  have h : Real.sqrt 21 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-22}(1) = \pi/\sqrt{22}$: $L(1,\psi) = 2\pi/\sqrt{88}$ ($h(-88) = 2$) and Euler factor $1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 1)"]
theorem zetaD_neg_twentytwo_one : zetaD (-22) 1 = π / Real.sqrt 22 := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg88 _ chiD_eq_changeLevel_neg22
    (ne_one_of_apply_neg_one _ psiNeg88_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-88) (by norm_num) 2 classNumber_QField_neg_eightyeight) _
    (psiNeg88_euler_neg22 1)]
  rw [show |((-88 : ℤ) : ℝ)| = 2 ^ 2 * 22 by norm_num, sqrt_sq_mul _ _ (by norm_num)]
  have h : Real.sqrt 22 ≠ 0 := by positivity
  field_simp
  norm_num

/-- **Table 6, $d = 22$, $s = 1$** ($D = -22$): $\zeta_{-22}(1)\sqrt{22}/\pi = 1$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 22, s = 1)"]
theorem table6_22_1 : zetaD (-22) 1 * Real.sqrt 22 / π = 1 := by
  rw [zetaD_neg_twentytwo_one]
  have h : Real.sqrt 22 ≠ 0 := by positivity
  field_simp

/-- $\zeta_{-23}(1) = 3\pi/(2\sqrt{23})$: $L(1,\psi) = 3\pi/\sqrt{23}$ ($h(-23) = 3$) times
$1 - \psi(2)/2 = \frac12$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 1)"]
theorem zetaD_neg_twentythree_one : zetaD (-23) 1 = 3 * π / (2 * Real.sqrt 23) := by
  rw [zetaD_one_of_LFunction (by norm_num) psiNeg23 _ chiD_eq_changeLevel_neg23
    (ne_one_of_apply_neg_one _ psiNeg23_neg_one)
    _ (LFunction_kronecker_one_of_classNumber (-23) (by norm_num) 3 classNumber_QField_neg_twentythree) _
    (psiNeg23_euler_neg23 1)]
  rw [show |((-23 : ℤ) : ℝ)| = 23 by norm_num]
  have h : Real.sqrt 23 ≠ 0 := by positivity
  norm_num
  field_simp

/-- **Table 6, $d = 23$, $s = 1$** ($D = -23$): $\zeta_{-23}(1)\sqrt{23}/\pi = \tfrac32$. -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 23, s = 1)"]
theorem table6_23_1 : zetaD (-23) 1 * Real.sqrt 23 / π = 3 / 2 := by
  rw [zetaD_neg_twentythree_one]
  have h : Real.sqrt 23 ≠ 0 := by positivity
  field_simp

end QuadFormsKB.ConwaySloane.Mass
