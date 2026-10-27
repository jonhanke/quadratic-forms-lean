/-
# O'Meara Chapter VI: citations for declarations elsewhere in the library

Declarations outside `Literature/OMeara/` that state (special cases of) items of O'Meara's Chapter VI (1973 printing)
but carried no tag for that item. The tags are added here with
`attribute [kb …]`, so the files where the declarations live are unchanged.
-/
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Literature.HasseNorm.Places

namespace QuadFormsKB

-- 63.r1: the fractional ideals of a local field are the powers 𝔭^ν (recalled from §22E); in valuation form, every
-- nonzero x has |x|_𝔭 = exp(k) for an integer k
attribute [kb "omeara1963" "§63, p. 158 (fractional ideals are 𝔭^ν = π^ν 𝔬, recalled from §22E; valuation form)"]
  HN.exists_exp_eq

-- 65.r5: E/F unramified at a discrete spot (e = 1); the library proves that F(√θ)/F is unramified at the spots not
-- dividing 2θ
attribute [kb "omeara1963" "§65A, p. 176 (E/F unramified at 𝔭: e_𝔭 = 1; proved outside 2θ)"]
  HN.ramificationIdx_eq_one

end QuadFormsKB
