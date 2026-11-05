/-
# O'Meara Chapters II and III: citations for declarations elsewhere

Tags for earlier declarations that state (special cases of) items of §21-§33:
* 31:2 for $\mathbb Z \subset \mathbb Q$: `OMeara.rat_dedekindAxioms` (proved with 21:1);
* 32:5: the residue field of a completion has $N\mathfrak p$ elements and $|\mathcal O_v/\varpi^n| = (N\mathfrak p)^n$:
  `HN.card_residueField`, `HN.card_quot_ϖ_pow`;
* 33:1 (Product Formula): `OMeara.product_formula`, Mathlib's `NumberField.prod_abs_eq_one`;
* 33:11a: the very strong approximation theorems `Lattices.exists_very_strong_approx` (free
  infinite spot: $|\beta|_w > R$ at the infinite places outside $S$) and `Lattices.exists_very_strong_approx_at` (free
  finite spot $\mathfrak p$: $|\beta|_{\mathfrak p} > e^{K}$) include the extra condition of 33:11a.
-/
import QuadFormsKB.Literature.OMeara.Sec21
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import Mathlib.NumberTheory.NumberField.ProductFormula
import QuadFormsKB.Lattices.SAVSA

attribute [kb "omeara1963" "§31, 31:2, p. 57 (rational number field case)"]
  QuadFormsKB.OMeara.rat_dedekindAxioms

attribute [kb "omeara1963" "§32A, 32:5, p. 60 (the residue field has Np elements; number field completion)"]
  QuadFormsKB.HN.card_residueField

attribute [kb "omeara1963" "§32A, 32:5, p. 60 ((o : p^ν) = (Np)^ν; number field completion)"]
  QuadFormsKB.HN.card_quot_ϖ_pow

attribute [kb "omeara1963" "§33G, 33:11a, p. 78 (|A| large at the free infinite spots)"]
  QuadFormsKB.Lattices.exists_very_strong_approx

attribute [kb "omeara1963" "§33G, 33:11a, p. 78 (|A|_p large at the free finite spot p)"]
  QuadFormsKB.Lattices.exists_very_strong_approx_at


namespace QuadFormsKB.OMeara

open NumberField in
/-- **33:1 (Product Formula).** For a non-zero element $a$ of a number field $F$,
$\prod_{\mathfrak p \in \Omega}|a|_{\mathfrak p} = 1$ with the normalized valuations: $|a|_w^{m_w}$ at the infinite places
($m_w = 1$ real, $2$ complex) and the normalized absolute values at the finite places. Mathlib's
`NumberField.prod_abs_eq_one`. (The first half of 33:1, $|a|_{\mathfrak p} = 1$ for almost all $\mathfrak p$, is
`NFLocal.finite_bad_places_nf`.) -/
@[kb "omeara1963" "§33B, 33:1, p. 66 (Product Formula)"]
theorem product_formula {F : Type*} [Field F] [NumberField F] {a : F} (ha : a ≠ 0) :
    (∏ w : InfinitePlace F, w a ^ w.mult) * ∏ᶠ w : FinitePlace F, w a = 1 :=
  prod_abs_eq_one ha

end QuadFormsKB.OMeara
