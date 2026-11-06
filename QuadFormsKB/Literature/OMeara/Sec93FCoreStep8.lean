/-
# O'Meara 93:28 over a general dyadic field: everything except step 8 proved

**Setting** (as in `Sec93FCore8.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276)
* `CoreStep8` (*named statement*): the core of the sufficiency (`Core8.SuffCoreHypRestN 8`) restricted to O'Meara's
  step 8: $a_1\mathfrak o \supsetneq 2\mathfrak o$, $u_2 \ge u_1 + 2$ and $\mathfrak s_2 \subseteq \mathfrak p^2$
  (O'Meara: "$s_2 > 1$, $a_2\mathfrak o \subseteq a_1\mathfrak p^2$, $a_1\mathfrak o \supset 2\mathfrak o$");
* `suffCoreHypRest8_of_step8`: `CoreStep8` implies `Core8.SuffCoreHypRestN 8`. Steps 4–7 are proved:
  `CoreGen.case_split` (the case distinction), `CoreGen.exists_sat_sq` ($dK_1 = dL_1$ by one move),
  `CoreGen.route_cond` (when (ii) or (iii) applies) and `CoreRouteD.route_aniso` (otherwise);
* `dyadicClassification_of_step8`, `dyadicClassification_step8_nf`: Theorem 93:28 over a dyadic field with
  `LocalHilbertField` (resp. over the completion of a number field at a dyadic place) from `CoreStep8` alone.

O'Meara's step 8 adjoins $\pi A(0,0)$ to $L$ and $K$ and applies steps 2 and 7 together with the induction hypothesis
to lattices with the same number $s_t - s_1$ but more components; our induction (`Core8.suff_all8`) runs over the
number of components, so step 8 is stated here as the named statement `CoreStep8`.

*Update:* step 8 is now proved: `QuadFormsKB.OMeara.Step8.coreStep8` (`Sec93FStep8.lean`) is a theorem
`CoreStep8`, and `Step8.dyadicClassification_nf` is Theorem 93:28 without any hypothesis.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreRouteD

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreStep8

universe u v

open Sat93 Suff28 SuffStep SuffMain PadicClass Core8

section Core

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **O'Meara's step 8 of the sufficiency in 93:28** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8,
pp. 275–276), *named statement*: `Core8.SuffCoreHypRestN 8` (both splittings saturated, all components of rank $8$,
every $FL_k$ hyperbolic, $L_1$ unimodular, the same fundamental invariants and conditions (i)–(iii), the conditions at
the first index not deciding $FK_1$) in the remaining configuration: for an irreducible $\pi$, with
$u_i = \operatorname{ord}_\pi a_i$ ($0$-based `a 0`, `a 1` are O'Meara's $a_1, a_2$), $u_1 < \operatorname{ord} 2$
($a_1\mathfrak o \supsetneq 2\mathfrak o$), $u_2 \ge u_1 + 2$ and $\mathfrak s_2 = \tau\mathfrak o$ with
$\operatorname{ord}\tau \ge 2$. Conclusion: $K$ has a saturated Jordan splitting whose first space is hyperbolic.
*Update:* proved as `Step8.coreStep8` (`Sec93FStep8.lean`); the final result is `Step8.dyadicClassification_nf`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, pp. 275–276"]
structure CoreStep8 : Prop where
  core : ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, finrank R (Ls k) = 8) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ¬ ((∀ x ∈ fIdeal Q L Ls 0 1, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
        (fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
          fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))) →
      ∀ (π : R) (hπ : Irreducible π), dord hπ (a 0) < dord hπ (2 : F) → dord hπ (a 0) + 2 ≤ dord hπ (a 1) →
        (∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ 2 ≤ dord hπ τ) →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
        ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
          finrank R (Ks' 0) ≤ 2 * finrank F T

variable {R F}

/-- **The core of 93:28 from step 8** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276):
`CoreStep8` implies `Core8.SuffCoreHypRestN 8`; steps 4–7 are proved here (`CoreGen.case_split`,
`CoreGen.exists_sat_sq`, `CoreGen.route_cond`, `CoreRouteD.route_aniso`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276 (steps 4–7 proved)"]
theorem suffCoreHypRest8_of_step8 (hHil : LocalHilbertField F) (h8 : CoreStep8.{u, v} R F) :
    SuffCoreHypRestN.{u, v} R F 8 := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ m Ls Ks a hLs hKs hd hT hsc hS hC hdec
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  rcases CoreGen.case_split Q hπ hLfg hLs.1 hS.2.1 hsc with hcase | ⟨h8a, h8b, h8c⟩
  · obtain ⟨Ks', hKs', hsq, x, y, D, hQx, hQy, hxy, hPD⟩ :=
      CoreGen.exists_sat_sq Q hHil h2p hQ hLs hKs hd hsc hS hC hπ hcase
    by_cases hlt : fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
        fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0)
    · exact ⟨Ks', hKs', CoreGen.route_cond Q hHil h2p hQ hLs hKs.1 hKs'.1 hS hC (hT 0) hsq hlt⟩
    · push Not at hlt
      have hS' := sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
      exact CoreRouteD.route_aniso Q hHil h2p hQ hLs hKs' hd (hT 0) hsc hS' hπ hcase hlt.1 hlt.2 hsq hQx hQy hxy
        hPD
  · exact h8.core Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC hdec π hπ h8a h8b h8c

end Core

section Final

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28 from step 8 alone** (O'Meara 1963, §93F, pp. 267–276): over a dyadic field with
`LocalHilbertField`, the named statement `CoreStep8` (O'Meara's step 8) implies `DyadicClassification`. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (from step 8)"]
theorem dyadicClassification_of_step8 (Q : QuadraticForm F V)
    (hHil : ∀ [CharZero F], LocalHilbertField F)
    (h : ∀ [CharZero F], CoreStep8.{u, v} R F) : DyadicClassification R Q :=
  dyadicClassification_of_rest8 Q hHil (fun [CharZero F] => suffCoreHypRest8_of_step8 hHil h)

end Final

section NumberField

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:28 over the completion $F_\mathfrak p$ of a number field, from step 8 alone**: only the named
statement `CoreStep8` for $F_\mathfrak p$ is assumed. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (completion of a number field, from step 8)"]
theorem dyadicClassification_step8_nf
    (h : CoreStep8.{0, v} (v.adicCompletionIntegers F) (v.adicCompletion F))
    (Q : QuadraticForm (v.adicCompletion F) V) :
    DyadicClassification (v.adicCompletionIntegers F) Q :=
  dyadicClassification_of_step8 Q (HasseIsoNF.localHilbertField_adicCompletion v) h

end NumberField

end QuadFormsKB.OMeara.CoreStep8
