/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.HClassFinite

/-!
# Headline statements, proved: G. Shimura, Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups

The declarations of `Challenge_Shimura.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/Shimura.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_Shimura.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

/-! ## Shimura's fundamental theorem on representations and the mass formula (13.18) (new in 0.6.0)

G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups* (2004): Theorem 11.6 (i) and
(v) and the formula (13.18), over every number field, with Theorem 10.5 (the local transitivity theorem) proved at
every finite place, the dyadic ones included. The statements are the library's named propositions; their content
is given in each docstring. -/

section ShimuraFundamental

theorem shimura_theorem11_6_i : Shimura2004.Theorem11_6_i :=
  QuadFormsKB.Shimura2004.theorem11_6_i_of_local

theorem shimura_theorem11_6_v : Shimura2004.Theorem11_6_v :=
  QuadFormsKB.Shimura2004.theorem11_6_v_holds

theorem shimura_formula13_18 : Shimura2004.Formula13_18 :=
  QuadFormsKB.Shimura2004.formula_13_18_holds

end ShimuraFundamental

end QuadFormsKB.Headlines
