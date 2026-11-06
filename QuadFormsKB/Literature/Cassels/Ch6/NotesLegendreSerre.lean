/-
# Cassels, Chapter 6, Notes (Gauss): indefinite ternary forms of determinant $1$, unconditionally

Companion to `Ch6/NotesLegendre.lean`, where Gauss' statement `gauss_indefinite_det_one` is proved conditional on the named
statement `Ch9Ex11.Ex11_ii` (Cassels, Ch. 9, Ex. 11 (ii)). That statement is now proved (`Ch9Ex11.ex11_ii_holds`,
`Ch9/Ex11Serre.lean`), so Gauss' statement holds unconditionally.

**Proves** `gauss_indefinite_det_one'`.
-/
import QuadFormsKB.Literature.Cassels.Ch6.NotesLegendre
import QuadFormsKB.Literature.Cassels.Ch9.Ex11Serre

namespace QuadFormsKB.Cassels.Ch6

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Cassels.Ch9Ex11

/-- **Cassels, Ch. 6, Notes, p. 98 (Gauss)**, unconditional: an indefinite classically integral ternary form of determinant $+1$ is
integrally equivalent to $-x_0^2 + 2x_1x_2$ (`gaussForm`). Arguments: `f` the form, `hf` classically integral of determinant
$\pm 1$, `hdet` the determinant of its matrix is $+1$, `hind` indefinite. *Proof:* `gauss_indefinite_det_one` with
`ex11_ii_holds`. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 98 (Gauss: indefinite ternary of determinant 1; unconditional)"]
theorem gauss_indefinite_det_one' (f : QuadForm ℤ 3) (hf : IsUnimodularCI f) (hdet : (Siegel.casselsMat f).det = 1)
    (hind : IsIndefinite f) : IntEquiv f gaussForm :=
  gauss_indefinite_det_one ex11_ii_holds f hf hdet hind

end QuadFormsKB.Cassels.Ch6
