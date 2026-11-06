/-
# Conway–Sloane, Ch. 15, §10.1: Table 15.7, indecomposable indefinite ternary forms

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §10.1,
Table 15.7 (p. 399) (`conwaysloane1999`).

**The printed notation.** An entry $\pm a_b\,\pm c_f\,\mp g$ with determinant $\mp d$ stands for two forms: the upper
signs give the Gram matrix $\begin{pmatrix} a & b & 0\\ b & c & f\\ 0 & f & g\end{pmatrix}$ (`Examples.mk a b c f g`,
with the printed signs on the diagonal) of determinant $-d$, the lower signs the form with the diagonal entries
negated, of determinant $+d$; it is the negative of the first form after changing the sign of the second basis vector.

**Formalization.** `table157` lists the upper-sign forms; `table157_correct` checks by `decide` that each has the
printed determinant $-d$, that the lower-sign form has determinant $+d$, and that both are indefinite (neither the form
nor its negative is positive definite). Not checked: that the forms are indecomposable and that the table is complete
(it lists all indecomposable indefinite ternary forms with $\lvert d\rvert \le 100$ up to equivalence); both need the
classification of indefinite ternary forms, which the library does not have.
-/
import QuadFormsKB.Literature.ConwaySloane.Examples

namespace QuadFormsKB
namespace ConwaySloane
namespace Examples

/-- Negate the diagonal entries (the lower signs of a Table 15.7 entry). -/
def Tern.negDiag (t : Tern) : Tern := ⟨-t.a, t.b, -t.c, t.f, -t.g, t.h⟩

/-- The negative form $-f$. -/
def Tern.neg (t : Tern) : Tern := ⟨-t.a, -t.b, -t.c, -t.f, -t.g, -t.h⟩

/-- A ternary form is indefinite: neither it nor its negative is positive definite. -/
def Tern.IsIndef (t : Tern) : Prop := ¬ t.IsPosDef ∧ ¬ t.neg.IsPosDef

instance (t : Tern) : Decidable t.IsIndef := by unfold Tern.IsIndef; infer_instance

/-- **Table 15.7** (upper signs): the indecomposable indefinite ternary forms with $\lvert d\rvert \le 100$, as printed,
paired with the printed $d$ (the upper-sign form has determinant $-d$). -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, Table 15.7, p. 399"]
def table157 : List (ℕ × Tern) := [
  (8, mk 2 1 2 1 (-2)),
  (28, mk 2 1 (-6) 1 2),
  (32, mk 2 1 (-2) 1 6),
  (56, mk 2 1 14 1 (-2)),
  (64, mk 4 1 4 1 (-4)),
  (64, mk 4 2 4 2 (-4)),
  (68, mk 2 1 6 1 (-6)),
  (72, mk 6 1 2 1 (-6)),
  (72, mk 2 1 (-2) 1 14),
  (84, mk 2 1 (-20) 1 2),
  (92, mk 2 1 (-22) 1 2)]

/-- **Table 15.7 checked entry by entry:** for every entry, the upper-sign form has determinant $-d$, the lower-sign
form has determinant $+d$, and both are indefinite. (Indecomposability and completeness are not checked; see the file
header.) -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, Table 15.7, p. 399"]
theorem table157_correct : ∀ e ∈ table157,
    e.2.det = -(e.1 : ℤ) ∧ e.2.negDiag.det = (e.1 : ℤ) ∧ e.2.IsIndef ∧ e.2.negDiag.IsIndef := by
  decide +kernel

/-- The lower-sign form is the negative of the upper-sign form after changing the sign of the second basis vector. -/
theorem Tern.negDiag_eq_transform_neg (t : Tern) (ht : t.h = 0) :
    t.negDiag = t.neg.transform ![0, 1, 2] ![1, -1, 1] := by
  obtain ⟨a, b, c, f, g, h⟩ := t
  simp only at ht
  subst ht
  simp [Tern.negDiag, Tern.neg, Tern.transform, Tern.mat]

end Examples
end ConwaySloane
end QuadFormsKB
