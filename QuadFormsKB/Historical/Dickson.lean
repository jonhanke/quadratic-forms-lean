/-
# Historical library: Dickson, *History of the Theory of Numbers* III (1923) and *Studies in the Theory of Numbers* (1930)

Root of the lean_lib `QuadFormsKB.Historical.Dickson` (not imported by `QuadFormsKB`; build with
`lake build QuadFormsKB.Historical.Dickson`). Targets taken from the historical sources:
* `Legendre.lean`: Legendre's theorem on $ax^2 + by^2 + cz^2 = 0$ (corrected form); Hasse–Minkowski
  and Meyer;
* `Minima.lean`: Hermite's inequality, Gauss–Seeber,
  Korkine–Zolotarev, unimodular forms of rank at most $7$;
* `Universal.lean`: Dickson's universal diagonal ternary forms;
* `Elementary.lean`: sums of three squares and quaternary representation numbers
 .
-/
import QuadFormsKB.Historical.Dickson.Legendre
import QuadFormsKB.Historical.Dickson.Minima
import QuadFormsKB.Historical.Dickson.Universal
import QuadFormsKB.Historical.Dickson.Elementary
