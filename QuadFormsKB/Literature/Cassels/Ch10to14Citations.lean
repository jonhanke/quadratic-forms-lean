/-
# Cassels, Chapters 10–14 and Appendices: citations for declarations elsewhere in the library

Declarations outside the files of these chapters that state (variants of) numbered items of Cassels' Chapters 10–14 and
Appendices A–B but carried no tag with the item's number. The tags are added here with `attribute [kb …]`, so the
files where the declarations live are unchanged.

* Ch. 12, Lemma 5.2 (p. 270): `Reduction.exists_val_ge` (the docstring names Lemma 5.2; it carried no tag).
* Appendix A, Theorem 2.1 (Eichler, p. 363): `Lattices.indecomposable_splitting_unique` (O'Meara 105:1), over a
  number field $F$ with $V$ totally positive definite; Cassels' case is $F = \mathbb Q$, $V$ positive definite.
  The existence of an indecomposable splitting (the first half of Cassels' statement) is
  `Lattices.exists_indecomposable_splitting`.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Basic
import QuadFormsKB.Literature.OMeara.Sec105

namespace QuadFormsKB

-- Ch. 12, Lemma 5.2: a strictly positive definite form satisfies f(x) ≥ K|x|²
attribute [kb "cassels1978" "Ch. 12, Lemma 5.2, p. 270"] Reduction.exists_val_ge

-- Appendix A, Theorem 2.1 (Eichler): uniqueness of the decomposition into indecomposable lattices
attribute [kb "cassels1978" "App. A, §2, p. 363 (existence of a decomposition into indecomposables, before Thm. 2.1)"]
  Lattices.exists_indecomposable_splitting
attribute [kb "cassels1978" "App. A, Thm. 2.1, p. 363 (uniqueness; generalization: number field, totally positive definite)"]
  Lattices.indecomposable_splitting_unique

end QuadFormsKB
