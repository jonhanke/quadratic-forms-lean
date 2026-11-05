/-
# O'Meara Chapter VII: citations for declarations elsewhere in the library

Declarations outside `Literature/OMeara/` that state (special cases of) items of O'Meara's Chapter VII (1973 printing)
but carried no tag for that item yet. The tags are added here with
`attribute [kb …]`, so the files where the declarations live are unchanged.
-/
import QuadFormsKB.Literature.OMeara.Citations6

namespace QuadFormsKB

-- 71.r3: an extension is unramified at a discrete spot when e = 1 (and f = n); the library proves it for the
-- quadratic extension F(√θ)/F at the spots not dividing 2θ
attribute [kb "omeara1963" "§71A, p. 191 (H/F unramified at 𝔓: e = 1; quadratic case, outside 2θ)"]
  HN.ramificationIdx_eq_one

end QuadFormsKB
