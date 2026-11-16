import QuadFormsKB.Historical.Gauss.Reduction

/-!
# Representatives of classes: negative forms and positive determinants (Disquisitiones Arithmeticae, Art. 223)

(Art. 223, the canonical representative of each class: for $D < 0$ the reduced
form, for $D > 0$ nonsquare a form chosen from the period of a reduced form, for $D = k^2$ a form $(A, k, 0)$).
For positive forms of negative determinant this is `art223_rule_one_gauss` (`Reduction.lean`). Here:

* `art223_negative_gauss` (proved): a class of **negative** forms of negative determinant is represented by the
  negative of the form chosen for the class of the positive form $(-a, -b, -c)$.
* `Art223PositiveNonsquareReduced` (stated, not proved): every form of positive nonsquare determinant is properly
  equivalent to a reduced form (Art. 183), the basis of Gauss's choice from the period. Gauss's theory of reduced
  indefinite forms and periods (Arts. 183-195) is not in the library (Tau Ceti has it for its own type).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- The negative $-f$ of a form. -/
def negForm (f : BinQF) : BinQF := BinQF.mk (-f.a) (-f.b) (-f.c)

theorem negForm_gaussForm (a b c : ℤ) : negForm (gaussForm a b c) = gaussForm (-a) (-b) (-c) := by
  apply ext_abc <;> simp [negForm]

theorem subst_negForm (p q r s : ℤ) (f : BinQF) : subst p q r s (negForm f) = negForm (subst p q r s f) := by
  apply ext_abc <;> simp [negForm, subst] <;> ring

theorem sLEquiv_negForm {f g : BinQF} (h : SLEquiv f g) : SLEquiv (negForm f) (negForm g) := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  exact (sLEquiv_iff _ _).mpr ⟨p, q, r, s, hd, subst_negForm p q r s f⟩

theorem sLEquiv_gauss_neg {a b c a' b' c' : ℤ}
    (h : SLEquiv (gaussForm (-a) (-b) (-c)) (gaussForm a' b' c')) :
    SLEquiv (gaussForm a b c) (gaussForm (-a') (-b') (-c')) := by
  have := sLEquiv_negForm h
  rwa [negForm_gaussForm, negForm_gaussForm, neg_neg, neg_neg, neg_neg] at this

theorem sLEquiv_gauss_neg' {a b c a' b' c' : ℤ}
    (h : SLEquiv (gaussForm a b c) (gaussForm (-a') (-b') (-c'))) :
    SLEquiv (gaussForm (-a) (-b) (-c)) (gaussForm a' b' c') := by
  have := sLEquiv_negForm h
  rwa [negForm_gaussForm, negForm_gaussForm, neg_neg, neg_neg, neg_neg] at this

/-- **Gauss, *Disq. Arith.* Art. 223, negative forms of negative determinant:** for a negative form
$(a, b, c)$ ($a < 0$) of negative determinant there is exactly one reduced form $(A, B, C)$ (Art. 171) such that
$(a, b, c)$ is properly equivalent to $(-A, -B, -C)$, and $B \ge 0$ whenever $(a, b, c)$ is also properly
equivalent to $(-A, B, -C)$. -/
@[kb "gauss1801" "Art. 223"]
theorem art223_negative_gauss {a b c : ℤ} (ha : a < 0) (hdet : gaussDet a b c < 0) :
    ∃! t : ℤ × ℤ × ℤ, SLEquiv (gaussForm a b c) (gaussForm (-t.1) (-t.2.1) (-t.2.2)) ∧
      GaussReduced t.1 t.2.1 t.2.2 ∧
      (SLEquiv (gaussForm a b c) (gaussForm (-t.1) t.2.1 (-t.2.2)) → 0 ≤ t.2.1) := by
  have hdet' : gaussDet (-a) (-b) (-c) < 0 := by simp only [gaussDet] at hdet ⊢; nlinarith
  obtain ⟨t, ⟨h1, h2, h3⟩, hu⟩ := art223_rule_one_gauss (b := -b) (c := -c) (neg_pos.mpr ha) hdet'
  refine ⟨t, ⟨sLEquiv_gauss_neg h1, h2, fun hc => h3 ?_⟩, fun t' ⟨k1, k2, k3⟩ =>
    hu t' ⟨sLEquiv_gauss_neg' k1, k2, fun hc => k3 ?_⟩⟩
  · have := sLEquiv_gauss_neg' (a' := t.1) (b' := -t.2.1) (c' := t.2.2) (by rwa [neg_neg])
    exact this
  · have := sLEquiv_gauss_neg (a' := t'.1) (b' := -t'.2.1) (c' := t'.2.2) hc
    rwa [neg_neg] at this

/-- **Gauss's reduced forms of positive nonsquare determinant** (*Disq. Arith.* Art. 183): $(a, b, c)$ with
$0 < b < \sqrt D$ and $\sqrt D - b < |a| < \sqrt D + b$, $D = b^2 - ac$ (written without square roots:
$b > 0$, $b^2 < D$, $(\,|a| + b)^2 > D$ and $(\,|a| - b)^2 < D$). -/
@[kb "gauss1801" "Art. 183"]
def GaussReducedIndef (a b c : ℤ) : Prop :=
  0 < b ∧ b ^ 2 < gaussDet a b c ∧ gaussDet a b c < (|a| + b) ^ 2 ∧ (|a| - b) ^ 2 < gaussDet a b c

/-- **The basis of Art. 223 for positive nonsquare determinants, stated, not
proved:** every form of positive nonsquare determinant is properly equivalent to a reduced form (Art. 183), from
whose period Gauss selects the representative. Gauss's selection inside the period (the ambiguous form if there
is one, else the form with the least first coefficient, with middle coefficient replaced by its least residue) is not
formalized. -/
@[kb "gauss1801" "Arts. 183, 223"]
def Art223PositiveNonsquareReduced : Prop :=
  ∀ a b c : ℤ, 0 < gaussDet a b c → ¬ IsSquare (gaussDet a b c) →
    ∃ A B C : ℤ, SLEquiv (gaussForm a b c) (gaussForm A B C) ∧ GaussReducedIndef A B C

end QuadFormsKB.Historical.Gauss
