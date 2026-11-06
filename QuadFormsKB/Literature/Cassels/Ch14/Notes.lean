/-
# Cassels, Chapter 14, Notes

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, Notes, pp. 354–357.

* Irregular discriminants (14.d2, p. 357, `IsIrregular`): the $p$-component of the class group $\mathcal G$
  (`FormClass D`) is non-cyclic for some odd prime $p$.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Group

namespace QuadFormsKB.Composition

/-- **Irregular discriminants** (Cassels, Ch. 14, Notes, p. 357): *a discriminant $D$ is said to be irregular if the
$p$-component of the class-group is non-cyclic for some $p \ne 2$.* The class group is $\mathcal G$ = `FormClass D`
(all primitive forms of discriminant $D$, for $D < 0$ both positive and negative definite ones) and
the $p$-component is Mathlib's `CommGroup.primaryComponent`. -/
@[kb "cassels1978" "Ch. 14, Notes, p. 357 (irregular discriminants)"]
def IsIrregular (D : ℤ) [NonzeroDisc D] : Prop :=
  ∃ p : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ ¬ IsCyclic (CommGroup.primaryComponent (FormClass D) p)

end QuadFormsKB.Composition
