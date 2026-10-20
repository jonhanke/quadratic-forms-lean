/-
# Local–global statements over a number field $F$ (O'Meara, *Introduction to Quadratic Forms*)

Stated over an arbitrary number field $F$ with its places `NFPlace F`. Hasse–Minkowski itself,
`hasseMinkowski_nf`, lives in `HasseMinkowskiNF.lean` with its blueprint. Proofs over general $F$
are a long-term goal: Hilbert reciprocity over $F$ is usually derived from class field
theory, which Mathlib does not have yet. For $F = \mathbb{Q}$ these statements follow from the
proved $\mathbb{Q}$ theorems through the bridge in `Equiv/NumberFieldRat.lean`.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Defs.NumberField

open NumberField

namespace QuadFormsKB

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! The two statements first stated here, `hilbert_reciprocity_nf` and `represents_iff_everywhere_nf`,
now live in `NumberFieldMain.lean` (same names, docstrings and `@[kb]` tags), downstream of their proofs
: this low-level file is imported by those proofs, so it cannot use them. -/

end QuadFormsKB
