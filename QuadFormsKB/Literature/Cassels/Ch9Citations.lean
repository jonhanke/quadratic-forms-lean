/-
# Cassels, Chapter 9: citations for declarations elsewhere in the library

Declarations outside `Literature/Cassels/Ch9*` that state (variants of) items of Cassels' Chapter 9 (*Integral forms
over the rational integers*, pp. 127–167) but carried no Cassels tag. The tags are added with `attribute [kb …]`, so
the files where the declarations live are unchanged. Each locator says how the declaration differs from Cassels' item.
-/
import QuadFormsKB.Lattices.SAVectorsAnisotropic
import QuadFormsKB.Lattices.SAVectorsAway
import QuadFormsKB.Lattices.SAVecAux
import QuadFormsKB.Binary.FormAut

namespace QuadFormsKB

/-! ### §8: the proof of Theorem 1.5 (9.p2) -/

-- The library proves Theorem 1.5 by O'Meara's argument for 104:3 (over a number field), not by Watson's argument that
-- Cassels follows; these are the steps of that argument which play the roles of Cassels' steps on pp. 158–161.
attribute [kb "cassels1978" "Ch. 9, §8, pp. 158–161 (proof of Thm. 1.5: core approximation step, O'Meara's argument)"]
  Lattices.vecApprox_core
attribute [kb "cassels1978" "Ch. 9, §8, pp. 158–161 (proof of Thm. 1.5 away from a prime, O'Meara's argument)"]
  Lattices.vecApprox_core_at
attribute [kb "cassels1978" "Ch. 9, §8, p. 160 (proof of Thm. 1.5, case (ii): the local choice, O'Meara's argument)"]
  Lattices.exists_beta_local
attribute [kb "cassels1978" "Ch. 9, §8, pp. 160–161 (proof of Thm. 1.5, case (iii): local representation by the complement)"]
  Lattices.representsIn_of_isotropic_perp

/-! ### Example 14 -/

attribute [kb "cassels1978" "Ch. 9, Ex. 14, p. 165 (proper automorphs of a positive definite binary form; fundamental discriminants)"]
  Binary.card_autSL

end QuadFormsKB
