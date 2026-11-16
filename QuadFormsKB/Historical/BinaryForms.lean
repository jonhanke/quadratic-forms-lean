/-
# Historical library: binary forms $x^2 + ny^2$ (Fermat, Euler, Lagrange, Gauss, Dirichlet, Eisenstein, Smith)

Root of the lean_lib `QuadFormsKB.Historical.BinaryForms` (not imported by `QuadFormsKB`; build with
`lake build QuadFormsKB.Historical.BinaryForms`). Targets taken from the historical sources:
* `Dirichlet.lean`: Dirichlet's formula for the class-number-one forms $x^2 + 2y^2$, $x^2 + xy + y^2$, $x^2 + xy + 2y^2$;
* `Smith.lean`: Smith's counts and the count for $x^2 + 3y^2$;
* `Primes.lean`: primes of the form $x^2 + 2y^2$, $x^2 + 3y^2$, $x^2 + 5y^2$, $x^2 + 7y^2$ (00210, 00002,
  00634, 00001, 00608, 00635, 00007).
-/
import QuadFormsKB.Historical.BinaryForms.Dirichlet
import QuadFormsKB.Historical.BinaryForms.Smith
import QuadFormsKB.Historical.BinaryForms.Primes
