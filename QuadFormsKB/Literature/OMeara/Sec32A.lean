/-
# O'Meara §32A: local fields

**Setting.** A *local field* is a field with a $\mathbb Z_{m0}$-valued (hence discrete) valuation, complete, with
finite residue class field (`IsLocalFieldSpot`). The local fields at non-archimedean spots of a number field are
the completions `v.adicCompletion F` (function fields and archimedean completions are not covered).

**Proves** 32:1 (definition), 32:2 ($\mathbb Q_p$), 32:4 (completions of a number field at a finite prime).
Reuses `HN.card_residueField` (finiteness of the residue field, $N\mathfrak p$ elements) from
`Literature/HasseNorm/SquareClasses.lean`. Not formalized: 32:3 (extensions of local fields), the ramification
theory 32:6, 32:6a, 32:9-32:15 (see `Sec32B.lean` for 32:7, 32:8, 32:8a).
-/
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField WithZero
open scoped Valued

noncomputable section

namespace QuadFormsKB.OMeara

/-- **O'Meara 32:1 (definition of a local field).** A field $F$ with a discrete valuation (values in $\mathbb
Z_{m0}$, so the spot is discrete as soon as the valuation is non-trivial) is a *local field* when it is complete
and the residue class field is finite. -/
@[kb "omeara1963" "§32A, 32:1, p. 59"]
def IsLocalFieldSpot (F : Type*) [Field F] [Valued F ℤᵐ⁰] : Prop :=
  CompleteSpace F ∧ (Valued.v : Valuation F ℤᵐ⁰).IsNontrivial ∧ Finite 𝓀[F]

/-- **O'Meara 32:4 (and 32:2 for $F = \mathbb Q$).** The completion of a number field at a non-trivial
non-archimedean spot is a local field; in particular the field $\mathbb Q_p$ of $p$-adic numbers is a local field
(take $F = \mathbb Q$ and $\mathfrak p$ the $p$-adic prime). -/
@[kb "omeara1963" "§32A, 32:4, p. 60"]
theorem isLocalFieldSpot_adicCompletion (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : IsLocalFieldSpot (v.adicCompletion F) :=
  ⟨inferInstance, inferInstance, inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩

/-- **O'Meara 32:2.** The field $\mathbb Q_p$ of $p$-adic numbers, as the completion of $\mathbb Q$ at the prime
$\mathfrak p$ of $\mathbb Z$ above $p$, is a local field. -/
@[kb "omeara1963" "§32A, 32:2, p. 59"]
theorem isLocalFieldSpot_padic (v : HeightOneSpectrum (𝓞 ℚ)) : IsLocalFieldSpot (v.adicCompletion ℚ) :=
  isLocalFieldSpot_adicCompletion ℚ v

end QuadFormsKB.OMeara
