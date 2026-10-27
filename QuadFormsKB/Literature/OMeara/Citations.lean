/-
# O'Meara Chapter IX: citations for declarations elsewhere in the library

Declarations outside `Literature/OMeara/` that state (special cases of) items of O'Meara's Chapter IX but carried no
O'Meara tag.
The tags are added here with `attribute [kb …]`, so the files where the declarations live are unchanged.
-/
import QuadFormsKB.Tamagawa.Reflection
import QuadFormsKB.Lattices.SpinorLocal
import QuadFormsKB.Lattices.SARotations
import QuadFormsKB.Lattices.SALocalRep
import QuadFormsKB.Lattices.KneserLocal
import QuadFormsKB.LocalDensity.DVRExplicit
import QuadFormsKB.LocalDensity.Explicit
import QuadFormsKB.LocalDensity.DyadicJordan
import QuadFormsKB.LocalDensity.DyadicBad
import QuadFormsKB.Binary.GenusLocal

namespace QuadFormsKB

-- 91:4: a symmetry in O(L) (any discrete valuation ring, dyadic included)
attribute [kb "omeara1963" "§91B, 91:4, p. 241 (a symmetry in O(L); special case)"] QuadForm.exists_refl_data_dvr

-- §91B criterion: τ_u ∈ O(L) for 2B(u, L) ⊆ Q(u)o
attribute [kb "omeara1963" "§91B, p. 241 (τ_u ∈ O(L) when 2B(u,L) ⊆ Q(u)o; special case)"]
  Lattices.symm_mem_stdStab Lattices.symm_mem_stdStab'

-- 91:1, proof route: {x : Q(x) ∈ a} on an anisotropic space
attribute [kb "omeara1963" "§91A, 91:1, p. 239 (proof route)"]
  LocalDensity.DVR.exists_isZeroType_of_anisotropic LocalDensity.exists_isZeroType_of_anisotropic

-- 92:1b: a unimodular lattice represents every unit (and every integer in rank ≥ 3)
attribute [kb "omeara1963" "§92, 92:1b, p. 247 (special case)"]
  Lattices.exists_eval_eq_unit_dvr Lattices.LocRep.exists_eval_eq_dvr Lattices.isotropicIn_formF_of_unimodular

-- 92:2: classification of binary unimodular forms over ℤ_p, p odd
attribute [kb "omeara1963" "§92, 92:2, p. 247 (special case)"] Binary.isometricGL_padic_of_not_dvd

-- §91C: Jordan splittings in matrix form
attribute [kb "omeara1963" "§91C, p. 243 (Jordan splitting, matrix form; existence)"]
  LocalDensity.DVR.exists_jordanFormGen LocalDensity.DVR.dvr_stepGen LocalDensity.DVR.IsJordanFormW

-- 63:1: the Local Square Theorem
attribute [kb "omeara1963" "§63A, 63:1, p. 159 (special case)"] LocalDensity.DVR.isSquare_of_pow_dvd_sub_one

end QuadFormsKB
