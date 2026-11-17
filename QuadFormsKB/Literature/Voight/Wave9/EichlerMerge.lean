/-
# Eichler orders: one definition (Voight, Definition 23.4.1)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 23.4.1 (p. 382).

**Setting.** $F$ a number field, $B = (a,b)_F$ = `QuatF F a b`, orders are `Subalgebra (𝓞 F) (QuatF F a b)`.
Two predicates existed for Definition 23.4.1: `Voight.IsEichlerOrder` (global, for the order of $B$) and
`Voight.Wave3.IsEichler` (any ring $R$ with fraction field $K$ and any $K$-algebra; used at the completions).

**Contents (proved).**
* `isEichlerOrder_iff_isEichler`: for a number field, `IsEichlerOrder O ↔ IsEichler (𝓞 F) F O`; so the global predicate is the
  case $R = \mathbb Z_F$, $K = F$ of the general one (they have the same body, so this is definitional).
* `isEichlerOrder_iff_exists_inf`: $\mathcal O$ is an Eichler order iff $\mathcal O = \mathcal O_1 \cap \mathcal O_2$ for two maximal
  orders $\mathcal O_1, \mathcal O_2$ (Definition 23.4.1 verbatim).
* `IsEichlerOrder.le_maximal`: an Eichler order is contained in a maximal order (each factor of the intersection).
-/
import QuadFormsKB.Literature.Voight.Wave4.LocalGlobalEichler

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.Voight.Wave9

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight QuadFormsKB.Voight.Wave3

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-- **One definition of Eichler orders** (Voight 2021, Definition 23.4.1): over a number field the global predicate
`IsEichlerOrder` is the general predicate `Wave3.IsEichler` with $R = \mathbb Z_F$, $K = F$, $A = (a,b)_F$. -/
@[kb "voight2021" "Definition 23.4.1, p. 382"]
theorem isEichlerOrder_iff_isEichler {O : Subalgebra (𝓞 F) (QuatF F a b)} :
    IsEichlerOrder O ↔ IsEichler (𝓞 F) F O :=
  Iff.rfl

/-- **Eichler orders are the intersections of two maximal orders** (Voight 2021, Definition 23.4.1), over a number field. -/
@[kb "voight2021" "Definition 23.4.1, p. 382"]
theorem isEichlerOrder_iff_exists_inf {O : Subalgebra (𝓞 F) (QuatF F a b)} :
    IsEichlerOrder O ↔ ∃ O₁ O₂ : Subalgebra (𝓞 F) (QuatF F a b),
      IsMaximalOrder (𝓞 F) F O₁ ∧ IsMaximalOrder (𝓞 F) F O₂ ∧ O = O₁ ⊓ O₂ :=
  Iff.rfl

/-- An Eichler order lies in a maximal order. -/
theorem IsEichlerOrder.exists_maximal_ge {O : Subalgebra (𝓞 F) (QuatF F a b)} (h : IsEichlerOrder O) :
    ∃ O' : Subalgebra (𝓞 F) (QuatF F a b), IsMaximalOrder (𝓞 F) F O' ∧ O ≤ O' := by
  obtain ⟨O₁, O₂, h₁, -, rfl⟩ := h
  exact ⟨O₁, h₁, inf_le_left⟩

end QuadFormsKB.Voight.Wave9
