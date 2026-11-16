import QuadFormsKB.Historical.Gauss.GenusGroup
import QuadFormsKB.Historical.Gauss.ReductionNegative

/-!
# Euler's idoneal numbers, for positive forms only (*Disq. Arith.* Art. 303)

(Art. 303, first half).

`art303_idoneal` (`GenusGroup.lean`) is proved for the group of *all* primitive classes of a discriminant $D$,
which for $D < 0$ contains the classes of positive definite and of negative definite forms together. Gauss speaks
of positive forms only. This file deduces his version for $D < 0$:

> each genus of positive (primitive, positive definite) forms of discriminant $D$ consists of a single class
> $\iff$ $C^2 = 1$ for every positive class $C$ $\iff$ every positive class is ambiguous (properly equivalent to its
> opposite form).

The deduction uses two facts, both proved here: (i) a primitive form of the principal genus of negative
discriminant is positive definite (it represents a nonzero square); (ii) the map $f \mapsto -f$ (`negForm`)
sends primitive forms of discriminant $D$ to primitive forms of discriminant $D$, positive definite ones to
negative definite ones and conversely, preserves proper equivalence, and commutes with the opposite form
$f \mapsto \bar f$. Compatibility of `Siegel.SameGenus` with negation is **not** needed and is not proved.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition FormClass

set_option linter.unusedSectionVars false

variable {D : ℤ} [NonzeroDisc D]

/-- The negative $-f$ of a primitive form, as a primitive form of the same discriminant. -/
def negPrim (f : PrimForm D) : PrimForm D :=
  ⟨negForm f.1, by
    intro d h1 h2 h3
    refine f.2.1 d ?_ ?_ ?_
    · simpa [negForm] using h1
    · simpa [negForm] using h2
    · simpa [negForm] using h3, by
    have := f.2.2
    simpa [BinQF.disc, negForm] using this⟩

theorem negForm_negForm (f : BinQF) : negForm (negForm f) = f := by
  apply ext_abc <;> simp [negForm]

theorem conjForm_negForm (f : BinQF) : conjForm (negForm f) = negForm (conjForm f) := by
  apply ext_abc <;> simp [negForm, conjForm]

/-- A primitive class is ambiguous ($C^2 = 1$) iff its form is properly equivalent to its opposite form. -/
theorem sq_eq_one_iff_sLEquiv_conj (f : PrimForm D) : mk f ^ 2 = 1 ↔ SLEquiv f.1 (conjForm f.1) := by
  rw [sq, mul_eq_one_iff_eq_inv, mk_inv]
  exact mk_eq_mk

/-- For negative discriminant, a primitive form is positive definite or its negative is. -/
theorem posDef_or_neg_posDef (hD : D < 0) (f : PrimForm D) : f.1.PosDef ∨ (negForm f.1).PosDef := by
  have hd : f.1.b ^ 2 - 4 * f.1.a * f.1.c = D := f.2.2
  rcases lt_trichotomy f.1.a 0 with ha | ha | ha
  · right
    refine (posDef_iff_posDef' _).2 ⟨by simpa [negForm] using ha, ?_⟩
    have := (negPrim f).2.2
    change (negForm f.1).disc = D at this
    omega
  · exfalso; rw [ha] at hd; nlinarith [sq_nonneg f.1.b]
  · left; exact (posDef_iff_posDef' _).2 ⟨ha, by rw [f.2.2]; exact hD⟩

/-- A primitive form of negative discriminant in the principal genus is positive definite: it represents a nonzero
square $w^2$ with $w$ prime to $2D$, and $4 a f(x, y) = (2 a x + b y)^2 - D y^2$. -/
theorem posDef_of_principal_genus (hD : D < 0) (f : PrimForm D) (hf : InPrincipalGenus f.1) : f.1.PosDef := by
  have hdisc : f.1.disc = D := f.2.2
  obtain ⟨w, x, y, -, hw, hv⟩ := exists_eval_sq_of_inPrincipalGenus (f := f.1) (by rw [hdisc]; omega) hf
  have hw0 : w ≠ 0 := by
    rintro rfl
    have := Int.isUnit_iff.1 (isCoprime_zero_left.1 hw)
    rw [hdisc] at this
    omega
  have hpos : 0 < f.1.eval x y := by rw [hv]; positivity
  have hd : f.1.b ^ 2 - 4 * f.1.a * f.1.c = D := hdisc
  have key : 4 * f.1.a * f.1.eval x y = (2 * f.1.a * x + f.1.b * y) ^ 2 + (-D) * y ^ 2 := by
    rw [eval_eq]; linear_combination (-(y ^ 2)) * hd
  refine (posDef_iff_posDef' _).2 ⟨?_, by rw [hdisc]; exact hD⟩
  by_contra hneg
  rcases (not_lt.1 hneg).lt_or_eq with ha | ha
  · have h1 : 4 * f.1.a * f.1.eval x y < 0 := by nlinarith
    nlinarith [sq_nonneg (2 * f.1.a * x + f.1.b * y), sq_nonneg y]
  · rw [ha] at hd; nlinarith [sq_nonneg f.1.b]

/-- **Gauss, *Disq. Arith.* Art. 303, for positive forms (a recorded loose end, first
half; Euler's idoneal numbers):** for a discriminant $D < 0$ (Gauss's determinant $D/4$; the idoneal numbers $n$
are $D = -4n$) the following are equivalent, where all forms are primitive and **positive definite**:

0. any two positive forms of one genus (`Siegel.SameGenus`) are properly equivalent, i.e. each genus of positive
   forms consists of a single class;
1. $C^2 = 1$ for every class $C$ of a positive form;
2. every positive form is properly equivalent to its opposite form $[a, -b, c]$ (every positive class is
   ambiguous, i.e. equal to its opposite).

This is Gauss's own formulation (positive forms only). It is deduced from `art303_idoneal` (all classes, positive
and negative forms together) through $f \mapsto -f$ (`negForm`) and the fact that the principal genus consists of
positive forms (`posDef_of_principal_genus`). Gauss's "the list of the $65$ idoneal numbers" is not formalized.
Gauss's index $1, \ldots$ is irrelevant here (no indices). -/
@[kb "gauss1801" "Art. 303"]
theorem art303_idoneal_positive (hD : D < 0) :
    List.TFAE [∀ f g : PrimForm D, f.1.PosDef → g.1.PosDef → Siegel.SameGenus f.1 g.1 → SLEquiv f.1 g.1,
      ∀ f : PrimForm D, f.1.PosDef → mk f ^ 2 = 1,
      ∀ f : PrimForm D, f.1.PosDef → SLEquiv f.1 (conjForm f.1)] := by
  -- all positive classes ambiguous implies all classes ambiguous
  have hall : (∀ f : PrimForm D, f.1.PosDef → SLEquiv f.1 (conjForm f.1)) → ∀ C : FormClass D, C ^ 2 = 1 := by
    intro h C
    obtain ⟨f, rfl⟩ := mk_surjective C
    rw [sq_eq_one_iff_sLEquiv_conj]
    rcases posDef_or_neg_posDef hD f with hp | hp
    · exact h f hp
    · have := sLEquiv_negForm (h (negPrim f) hp)
      change SLEquiv (negForm (negForm f.1)) (negForm (conjForm (negForm f.1))) at this
      rwa [negForm_negForm, conjForm_negForm, negForm_negForm] at this
  tfae_have 1 → 2 := by
    intro h f hf
    obtain ⟨k, hk⟩ := mk_surjective (mk f ^ 2)
    have hg : InPrincipalGenus k.1 := (thm_3_1 k).1 ⟨mk f, by rw [hk]⟩
    have hkp := posDef_of_principal_genus hD k hg
    have hpp := posDef_of_principal_genus hD (principal D) (by
      refine (thm_3_1 (principal D)).1 ⟨1, ?_⟩
      rw [one_pow]; rfl)
    have hsg : Siegel.SameGenus k.1 (principal D).1 := by
      rw [sameGenus_iff_mul_inv_sq, ← one_def, inv_one, mul_one]
      exact ⟨mk f, hk.symm⟩
    rw [← hk, one_def]
    exact mk_eq_mk.2 (h k (principal D) hkp hpp hsg)
  tfae_have 2 → 3 := fun h f hf => (sq_eq_one_iff_sLEquiv_conj f).1 (h f hf)
  tfae_have 3 → 1 := by
    intro h f g _ _ hfg
    have h1 := (art303_idoneal (D := D)).out 1 2 |>.2 (hall h)
    exact h1 f g hfg
  tfae_finish

end QuadFormsKB.Historical.Gauss

