/-
# O'Meara Chapter VIII: citations for existing declarations

Declarations defined elsewhere that formalize items of O'Meara's Chapter VIII (1973 printing) but carried no tag for
that item; the tags are added here with `attribute [kb …]`, so the files where the declarations live are unchanged.
-/
import QuadFormsKB.Literature.OMeara.Sec82Max

namespace QuadFormsKB.OMeara

/-! ### §82A -/

/- O'Meara's fundamental question (§82A, p. 220): determine whether two lattices are isometric, i.e. describe the
class `cls L` by invariants. -/
attribute [kb "omeara1963" "§82A, p. 220 (the fundamental question: determine cls L)"] cls

/-! ### §82 (introduction): binary lattices -/

/- O'Meara (§82, p. 220) calls a lattice binary, ternary, … according as its rank is 2, 3, …; in 82:16 and 82:20 the
binary lattice $J$ is expressed by `finrank R J = 2`. -/
attribute [kb "omeara1963" "§82, p. 220 (binary lattice: rank 2)"] exists_binary_split_of_isModular
  Dedekind.exists_binary_split_of_isMaximal

end QuadFormsKB.OMeara
