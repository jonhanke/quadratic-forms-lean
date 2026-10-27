/-
# Input theorems for Hasse–Minkowski over a number field

This file defines the two input bundles for Hasse–Minkowski over a number field $F$:
`HMInputs F` (Serre's route) and `LamInputs` (Lam's route). The input statements themselves, first
stated here with `sorry`, now live in `NumberFieldMain.lean`, downstream of their proofs:

- quadratic Hilbert reciprocity over $F$: `hilbert_reciprocity_nf`, proved as
  `HN.hilbert_product_formula_nf` (`HasseNorm/Reciprocity.lean`);
- squares are local–global: `isSquare_iff_everywhere_nf`, proved as `SqLG.isSquare_iff_everywhere`;
- elements with prescribed local Hilbert symbols: `exists_prescribed_hilbert_nf`, proved as
  `PresNF.exists_prescribed_hilbert`;
- the Hasse norm theorem for quadratic extensions: `hilbert_eq_one_of_everywhere_nf`, proved as
  `HasseNorm.hilbert_eq_one_of_everywhere`;
- local: the Hilbert symbol at a finite place is multiplicative: `hilbertSymbol_mul_left_finite_nf`,
  proved as `HN.hilbertSymbol_mul_left_finite_nf`.

`LamInputs` holds unconditionally (`lamInputs`, `HasseMinkowskiNFMain.lean`), so `hasseMinkowski_nf` is
fully proved. `HMInputs F` holds unconditionally too (`hmInputs`, `NumberFieldMain.lean`).

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.NumberField

open NumberField

namespace QuadFormsKB.NFInputs

variable {F : Type} [Field F] [NumberField F]

/-! The four input statements first stated here (`isSquare_iff_everywhere_nf`,
`exists_prescribed_hilbert_nf`, `hilbert_eq_one_of_everywhere_nf`, `hilbertSymbol_mul_left_finite_nf`)
and the bundle `hmInputs` now live in `NumberFieldMain.lean` (same names, docstrings and `@[kb]` tags),
downstream of the proofs. All four are proved there (including `exists_prescribed_hilbert_nf`). -/

/-- **The inputs for Hasse–Minkowski over $F$, as one hypothesis.** `HMInputs F` bundles the five
input statements (stated in `NumberFieldMain.lean`; fields named after them), so that the reduction of Hasse–Minkowski to the
inputs can be proved **without** `sorry`. Every step in `HasseMinkowskiNF.lean` takes `I : HMInputs F`
as an explicit hypothesis and is therefore kernel-checked and shown as *proved*. (`hasseMinkowski_nf`
itself uses Lam's route, `LamInputs`, which is proved; `hmInputs` in `NumberFieldMain.lean` is proved too.)

- `reciprocity`: `hilbert_reciprocity_nf`;
- `isSquare_iff_everywhere`: `isSquare_iff_everywhere_nf`;
- `prescribed_hilbert`: `exists_prescribed_hilbert_nf`;
- `hasse_norm`: `hilbert_eq_one_of_everywhere_nf`;
- `mul_left_finite`: `hilbertSymbol_mul_left_finite_nf`. -/
structure HMInputs (F : Type) [Field F] [NumberField F] : Prop where
  reciprocity : ∀ a b : F, a ≠ 0 → b ≠ 0 →
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard
  isSquare_iff_everywhere : ∀ a : F,
    IsSquare a ↔ NFPlace.Everywhere (F := F) fun K _ _ => IsSquare (algebraMap F K a)
  prescribed_hilbert : ∀ {ι : Type} [Fintype ι] (a : ι → F), (∀ i, a i ≠ 0) →
    ∀ ε : ι → NFPlace F → ℤ, (∀ i v, ε i v = 1 ∨ ε i v = -1) →
    {v : NFPlace F | ∃ i, ε i v = -1}.Finite →
    (∀ i, Even {v : NFPlace F | ε i v = -1}.ncard) →
    (∀ v : NFPlace F, v.atPlace fun K _ _ =>
      ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap F K (a i)) x = ε i v) →
    ∃ x : F, x ≠ 0 ∧ ∀ i v, v.hilbert (a i) x = ε i v
  hasse_norm : ∀ a b : F, a ≠ 0 → b ≠ 0 → (∀ v : NFPlace F, v.hilbert a b = 1) →
    hilbertSymbol F a b = 1
  mul_left_finite : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a b c : v.adicCompletion F), a ≠ 0 → b ≠ 0 → c ≠ 0 →
    hilbertSymbol (v.adicCompletion F) (a * b) c =
      hilbertSymbol (v.adicCompletion F) a c * hilbertSymbol (v.adicCompletion F) b c

/-- **The two inputs of Lam's proof, for every number field.** Lam's proof of Hasse–Minkowski
(Ch. VI, Thm. 3.1) needs only the binary and ternary cases, i.e. these two statements, but for
**all** number fields (the $n = 4$ step passes to a quadratic extension $L = F(\sqrt d)$):

- `isSquare_iff_everywhere`: `isSquare_iff_everywhere_nf` for every number field $L$;
- `hasse_norm`: `hilbert_eq_one_of_everywhere_nf` for every number field $L$.

Reciprocity, prescribed symbols and multiplicativity of the local symbol are **not** needed on this
route (compare `HMInputs`). -/
structure LamInputs : Prop where
  isSquare_iff_everywhere : ∀ (L : Type) [Field L] [NumberField L] (a : L),
    IsSquare a ↔ NFPlace.Everywhere (F := L) fun K _ _ => IsSquare (algebraMap L K a)
  hasse_norm : ∀ (L : Type) [Field L] [NumberField L] (a b : L), a ≠ 0 → b ≠ 0 →
    (∀ v : NFPlace L, v.hilbert a b = 1) → hilbertSymbol L a b = 1

end QuadFormsKB.NFInputs
