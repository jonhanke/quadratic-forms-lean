/-
# O'Meara 93:28 over a 2-adic field: the remaining case

**Setting** (as in `Sec93E.lean`), with $2$ a prime element of $R$ (a 2-adic field, §93G).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–8, and §93G, proof of 93:29, pp. 278–279)
* the named statement `TwoAdicCoreRest4`: the core of the sufficiency in the single case
  $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$ (O'Meara p. 278: "We therefore assume that
  $\mathfrak n_1 = \mathfrak o$ ... A computation of Hasse symbols ... will show that $\mu = 0$");
* `suffCoreHypRest4_of_twoAdic`: over a 2-adic field, `Core4.SuffCoreHypRest4` follows from it (the case
  $\mathfrak n_2 = 2\mathfrak o$ is `CoreTwo.core_twoAdic_two`, the cases with $\mathfrak f_1 \subseteq 8\mathfrak o$
  are decided by (iii), `CoreTwo.decided_of_le_eight`);
* `dyadicClassification_twoAdic`, `dyadicClassification_twoAdic_nf`: Theorem 93:28 over a 2-adic field from
  `TwoAdicCoreRest4`.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCore4
import QuadFormsKB.Literature.OMeara.Sec93FCoreTwo

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreTwoMain

universe u v

open Suff28 CoreTwo

section Core

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The core of 93:28 over a 2-adic field, case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$**
(O'Meara 1963, §93G, proof of 93:29, sufficiency, p. 278), *named statement*: `Core4.SuffCoreHypRest4` for a 2-adic
field with the additional hypotheses $a_1\mathfrak o = \mathfrak o$ and $a_2\mathfrak o = 4\mathfrak o$ ($0$-based
`a 0`, `a 1`). O'Meara: "$K_1 \cong \langle A(1, 4\lambda)\rangle \perp \langle A(2, 2\mu)\rangle$ with $\lambda$ equal
to $0$ or $\rho$, and the same with $\mu$. But $\mathfrak n_2 = 4\mathfrak o \subsetneq 4\mathfrak n_1$, hence
$FL_1 \perp \langle\varepsilon\rangle \cong FK_1 \perp \langle 1\rangle$ ... A computation of Hasse symbols ... will
show that $\mu = 0$. Then $K_1 \perp K_2 \cong \langle A(1, 0)\rangle \perp \langle A(2, 0)\rangle \perp K_2'$." All
other cases of the core over a 2-adic field are proved (`suffCoreHypRest4_of_twoAdic`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
structure TwoAdicCoreRest4 : Prop where
  core : IsTwoAdic R → ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, finrank R (Ls k) = 4) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      R ∙ a 0 = 1 → R ∙ a 1 = R ∙ (4 : F) →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
        ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
          finrank R (Ks' 0) ≤ 2 * finrank F T

variable {R F}

/-- **The core of 93:28 over a 2-adic field from its single remaining case** (O'Meara 1963, §93G, pp. 278–279):
by `CoreTwo.twoAdic_cases` either $\mathfrak n_2 = 2\mathfrak o$ (proved: `CoreTwo.core_twoAdic_two`), or
$\mathfrak f_1 \subseteq 8\mathfrak o$ (then (iii) decides, `CoreTwo.decided_of_le_eight`, excluded by the hypothesis of
`SuffCoreHypRest4`), or $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$ (`TwoAdicCoreRest4`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 278–279"]
theorem suffCoreHypRest4_of_twoAdic (hHil : PadicClass.LocalHilbertField F) (h2 : IsTwoAdic R)
    (h : TwoAdicCoreRest4.{u, v} R F) : Core4.SuffCoreHypRest4.{u, v} R F := by
  refine ⟨fun {V} _ _ _ _ _ Q h2p hQ L K _ _ m Ls Ks a hLs hKs hd hT hsc hS hC hdec => ?_⟩
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hLreg : IsRegular Q L := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha : ∀ i, R ∙ a i = normIdeal Q (Ls i) := fun i => by
    rw [(hS.2.1 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hLfg hLs.1 i]; rfl
  rcases twoAdic_cases Q h2 hLfg hLreg hLs.1 hsc ha with h2o | ⟨h0, h1⟩ | h8
  · exact core_twoAdic_two hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs (fun k => (hd k).symm ▸ by norm_num) hT hsc
      hS h2o
  · exact h.core h2 Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC h0 h1
  · exfalso
    obtain ⟨hX, hlt⟩ := decided_of_le_eight Q h2 hLfg hLreg hLs.1 0 1 (by simp) hsc (ha 0) h8
    exact hdec ⟨hX, Or.inr hlt⟩

end Core

section Final

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28 over a 2-adic field** (O'Meara 1963, §93F, pp. 267–276; 2 prime), from the named statement
`TwoAdicCoreRest4` (the case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$ of the core). -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (2-adic field)"]
theorem dyadicClassification_twoAdic (Q : QuadraticForm F V) (h2 : IsTwoAdic R)
    (hHil : ∀ [CharZero F], PadicClass.LocalHilbertField F)
    (h : ∀ [CharZero F], TwoAdicCoreRest4.{u, v} R F) : DyadicClassification R Q :=
  Core4.dyadicClassification_of_rest4 Q hHil (fun [CharZero F] => suffCoreHypRest4_of_twoAdic hHil h2 h)

end Final

section NumberField

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:28 over a 2-adic completion of a number field** (O'Meara 1963, §93F, pp. 267–276): at a place
$\mathfrak p$ over $2$ with $2$ prime in $F_\mathfrak p$ (unramified over $\mathbb Q_2$, e.g. $\mathbb Q_2$ itself),
only the named statement `TwoAdicCoreRest4` for $F_\mathfrak p$ is assumed. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (2-adic completion of a number field)"]
theorem dyadicClassification_twoAdic_nf (h2 : IsTwoAdic (v.adicCompletionIntegers F))
    (h : TwoAdicCoreRest4.{0, v} (v.adicCompletionIntegers F) (v.adicCompletion F))
    (Q : QuadraticForm (v.adicCompletion F) V) :
    DyadicClassification (v.adicCompletionIntegers F) Q :=
  dyadicClassification_twoAdic Q h2 (HasseIsoNF.localHilbertField_adicCompletion v) h

end NumberField

end QuadFormsKB.OMeara.CoreTwoMain
