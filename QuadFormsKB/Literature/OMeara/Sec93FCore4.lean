/-
# O'Meara 93:28, sufficiency: the named core in dimension exactly $4$

**Setting** (as in `Sec93FCoreCases.lean`).

O'Meara runs steps 4–8 of the sufficiency after reducing to all components of dimension $4$ (p. 272: "we can assume
that $\dim L_i = \dim K_i = 4$"). This file makes the named core assume exactly that.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, pp. 272–276)
* `SuffCoreHypRest4`: `CoreCases.SuffCoreHypRest` with the hypothesis $\dim L_k \ge 3$ replaced by $\dim L_k = 4$;
* `suffCore4_of_rest4`, `good_succ4`, `suff_all4`: the chain `SuffCoreHypRest4` $\Rightarrow$ the core in dimension $4$
  $\Rightarrow$ `GoodSuff4` $\Rightarrow$ `GoodSuff` (`Dim4.goodSuff_of_goodSuff4`) $\Rightarrow$ `Suff`;
* `dyadicClassification_of_rest4`, `dyadicClassification_rest4_nf`: Theorem 93:28 from `SuffCoreHypRest4`.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffDim4
import QuadFormsKB.Literature.OMeara.Sec93FCoreCases

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Core4

universe u v

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass

section Core

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The core of 93:28 outside the directly decided cases, in dimension $4$** (O'Meara 1963, §93F, proof of the
sufficiency, steps 4–8, pp. 274–276, after the reduction of p. 272 to $\dim L_i = \dim K_i = 4$), *named statement*:
`CoreCases.SuffCoreHypRest` with the hypothesis that all fundamental dimensions are $\ge 3$ replaced by: all
fundamental dimensions are exactly $4$. Both splittings saturated, every $FL_k$ hyperbolic, $L_1$ unimodular, the same
fundamental invariants and conditions (i)–(iii), and the conditions at the first index do not already decide $FK_1$;
then $K$ has a saturated splitting whose first space $FK_1'$ is hyperbolic. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276 (dimension 4)"]
structure SuffCoreHypRest4 : Prop where
  core : ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, finrank R (Ls k) = 4) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ¬ ((∀ x ∈ fIdeal Q L Ls 0 1, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
        (fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
          fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))) →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
        ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
          finrank R (Ks' 0) ≤ 2 * finrank F T

/-- The core of the sufficiency in dimension $4$ (the form of `SuffCore` used in `good_succ4`; derived from
`SuffCoreHypRest4`, not a named statement). -/
def SuffCore4 : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, finrank R (Ls k) = 4) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧ IsometricLat Q Q (Ls 0) (Ks' 0) ∧
        Cond93 Q L Ls Ks' a

variable {R F}

/-- **The core in dimension $4$ from `SuffCoreHypRest4`**: in the cases decided by the conditions at the first index
the given splitting already has $FK_1$ hyperbolic (`CoreCases.exists_lagrangian_of_cond`); then
`CoreHyp.isometricLat_of_hyp` gives $K_1' \cong L_1$, and `Resplit.cond93_resplit` keeps (i)–(iii). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 273–276 (dimension 4)"]
theorem suffCore4_of_rest4 (hHil : LocalHilbertField F) (h : SuffCoreHypRest4.{u, v} R F) :
    SuffCore4.{u, v} R F := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ m Ls Ks a hLs hKs hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls 0)
  have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  obtain ⟨Ks', hKs', hTK⟩ : ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
      ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
        finrank R (Ks' 0) ≤ 2 * finrank F T := by
    by_cases hdec : (∀ x ∈ fIdeal Q L Ls 0 1, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
        (fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
          fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))
    · refine ⟨Ks, hKs, ?_⟩
      have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
      have ha0 : ∀ k, a k ≠ 0 := fun k =>
        (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
      have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKs.1.split.iSup_eq ▸ le_iSup Ks 0)
      have hK0reg : IsRegular Q (Ks 0) := (hKs.1.modular 0).isRegular Q hK0fg
      obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
      have hc : Fin.cast h0 0 = 0 := Fin.ext (by simp)
      have hrk : finrank R (Ls 0) = finrank R (Ks 0) := by have := (hTy 0).1; rwa [hc] at this
      obtain ⟨h1, h2, h3⟩ := hC 0 1 (by simp)
      have hjL : jordanChain Ls 0 = Ls 0 := jordanChain_zero Ls 0 rfl
      have hjK : jordanChain Ks 0 = Ks 0 := jordanChain_zero Ks 0 rfl
      rw [hjL, hjK] at h1 h2 h3
      rcases hdec with ⟨hX, hlt | hlt⟩
      · exact CoreCases.exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX h1 (ha0 1) (h2 hlt) (hT 0)
      · exact CoreCases.exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX h1 (ha0 0) (h3 hlt) (hT 0)
    · exact h.core Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC hdec
  refine ⟨Ks', hKs', ?_, Resplit.cond93_resplit Q hHil h2p hQ hLs.1 hKs.1 hKs'.1 hS hC⟩
  have hS' := sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := hS'
  have hc : Fin.cast h0 0 = 0 := Fin.ext (by simp)
  obtain ⟨hrk, hsc', hg⟩ := hTy 0
  rw [hc] at hrk hsc' hg
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKs'.1.split.iSup_eq ▸ le_iSup Ks' 0)
  have hLU : IsUnimodular Q (Ls 0) := by
    have := hLs.1.modular 0; rwa [hsc] at this
  have hKU : IsUnimodular Q (Ks' 0) := by
    have := hKs'.1.modular 0; rwa [← hsc', hsc] at this
  exact CoreHyp.isometricLat_of_hyp Q hQ hL0fg hK0fg hLU hKU hrk (by rw [hLs.2 0, hKs'.2 0, hg]) (hT 0) hTK

/-- **The induction step of the sufficiency in dimension $4$** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
step 3, p. 273): `SuffMain.good_succ` with the core in dimension $4$, giving `GoodSuff4`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (the induction step, dimension 4)"]
theorem good_succ4 (hcore : SuffCore4.{u, v} R F) {m : ℕ} (ih : Suff.{u, v} R F (m + 1)) :
    Dim4.GoodSuff4.{u, v} R F (m + 2) := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hd3 hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  obtain ⟨Ks', hKs', hiso0, hC'⟩ := hcore Q h2p hQ L K m Ls Ks a hLs hKs hd hT (hsc 0 rfl) hS hC
  have hS' := sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
  have hKle : ∀ k, Ks' k ≤ K := fun k => hKs'.1.split.iSup_eq ▸ le_iSup Ks' k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKle 0)
  have hK0reg : IsRegular Q (Ks' 0) := (hKs'.1.modular 0).isRegular Q hK0fg
  obtain ⟨σ, hσ, hσK⟩ := SuffWitt.exists_orth_latMap_eq Q hQ hK0fg hK0reg (adj_isometricLat_symm Q Q hiso0)
  set Ks'' : Fin (m + 2) → Submodule R V := fun k => latMap σ (Ks' k) with hKs''
  have hK'lat : (latMap σ K).IsLattice F := SuffSub.isLattice_latMap
  have hK'fg : (latMap σ K).FG := Submodule.IsLattice.fg (A := F)
  have hK'sat : IsSaturated Q (latMap σ K) Ks'' := SuffSub.isSaturated_latMap Q hσ hKle hKfg hKs'
  have hS'' : SameFundamentalInvariants Q Q L (latMap σ K) Ls Ks'' a := sameFund_moveK Q hσ hKle hS'
  have hchfg : ∀ {X : Submodule R V} {Xs : Fin (m + 2) → Submodule R V}, X.FG → (∀ k, Xs k ≤ X) →
      ∀ i, (jordanChain Xs i).FG := fun hX hle i => FG.of_le hX (iSup₂_le fun j _ => hle j)
  have hC'' : Cond93 Q L Ls Ks'' a := cond93_congr_right Q (hchfg hLfg hLle) (hchfg hKfg hKle)
    (fun i => by rw [hKs'', ← SuffSub.jordanChain_latMap]; exact isometricLat_latMap Q hσ _) hC'
  have h0 : Ls 0 = Ks'' 0 := hσK.symm
  obtain ⟨hSt, hCt⟩ := tail_conds Q hLfg hK'fg hLs hK'sat h0 ha0 hS'' hC''
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hLreg0 : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  have hoL := isOrthSum_zero_tail Q hLfg hLs.1
  have hoK := isOrthSum_zero_tail Q hK'fg hK'sat.1
  rw [← h0] at hoK
  set W := perpF Q (Ls 0) with hW
  have hspL : span F (tailLat Ls : Set V) = W := span_eq_perpF Q hLreg0 hoL
  have hspK : span F (tailLat Ks'' : Set V) = W := span_eq_perpF Q hLreg0 hoK
  have hLW : tailLat Ls ≤ W.restrictScalars R := fun x hx => hspL ▸ subset_span hx
  have hKW : tailLat Ks'' ≤ W.restrictScalars R := fun x hx => hspK ▸ subset_span hx
  have hLtfg : (tailLat Ls).FG := FG.of_le hLfg (tailLat_le Q hLs.1.split)
  have hKtfg : (tailLat Ks'').FG := FG.of_le hK'fg (tailLat_le Q hK'sat.1.split)
  have hLWl := SuffSub.isLattice_subLatIn hLW hLtfg hspL
  have hKWl := SuffSub.isLattice_subLatIn hKW hKtfg hspK
  have hQW : (QuadraticMap.associated (SuffSub.QW Q W)).Nondegenerate :=
    SuffSub.nondegenerate_QW Q hQ (span_sup_perpF Q hLreg0 hoL) fun w hw u hu => perpF_orth_span Q hw hu
  have hsLs : ∀ i : Fin (m + 1), Ls i.succ ≤ tailLat Ls := fun i => le_iSup (fun k : Fin (m + 1) => Ls k.succ) i
  have hsKs : ∀ i : Fin (m + 1), Ks'' i.succ ≤ tailLat Ks'' := fun i =>
    le_iSup (fun k : Fin (m + 1) => Ks'' k.succ) i
  have hJL := SuffSub.isJordanSplitting_subLatIn Q hLW hsLs hLtfg (isJordanSplitting_tail Q hLs.1)
  have hJK := SuffSub.isJordanSplitting_subLatIn Q hKW hsKs hKtfg (isJordanSplitting_tail Q hK'sat.1)
  have hSW := (SuffSub.sameFundamentalInvariants_subLatIn Q hLW hKW hsLs hsKs _).mp hSt
  have hCW := (SuffSub.cond93_subLatIn Q hLW hKW hsLs hsKs hLtfg hKtfg _).mp hCt
  have hisoW := ih (SuffSub.QW Q W) h2p hQW _ _ _ _ _ hJL hJK hSW hCW
  have hisoT := (SuffSub.isometricLat_subLatIn Q hLW hKW).mpr hisoW
  have hLK' := isometricLat_of_tail Q hL0fg hLtfg hoL hoK hisoT
  exact adj_isometricLat_trans Q Q Q hLK' (adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K))

/-- **The sufficiency in 93:28 from the core in dimension $4$**, for every number of Jordan components. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, pp. 272–273 (dimension 4)"]
theorem suff_all4 (hHil : LocalHilbertField F) (hcore : SuffCore4.{u, v} R F) : ∀ t, Suff.{u, v} R F t
  | 0 => suff_zero
  | 1 => suff_one
  | m + 2 =>
    suff_of_good hHil (Dim4.goodSuff_of_goodSuff4 hHil (good_succ4 hcore (suff_all4 hHil hcore (m + 1))))

end Core

section Final

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28 from the core in dimension $4$** (O'Meara 1963, §93F, pp. 267–276): over a dyadic field with
`LocalHilbertField`, the named statement `SuffCoreHypRest4` implies `DyadicClassification`. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (dimension 4)"]
theorem dyadicClassification_of_rest4 (Q : QuadraticForm F V)
    (hHil : ∀ [CharZero F], LocalHilbertField F)
    (h : ∀ [CharZero F], SuffCoreHypRest4.{u, v} R F) : DyadicClassification R Q := by
  refine ⟨fun h2p hQ L K _ _ t Ls Ks a hL hK hS => ?_⟩
  have : CharZero F := Main28.charZero_of_dyadic (R := R) h2p
  refine ⟨Main28.necessity Q hHil h2p hQ hL hK hS, fun hC => ?_⟩
  exact (cls_eq_of_mem Q (mem_cls_of_isometricLat Q
    (suff_all4 hHil (suffCore4_of_rest4 hHil h) t Q h2p hQ L K Ls Ks a hL hK hS hC))).symm

end Final

section NumberField

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:28 over the completion $F_\mathfrak p$ of a number field, from the core in dimension $4$**: only the
named statement `SuffCoreHypRest4` for $F_\mathfrak p$ is assumed. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (completion of a number field, dimension 4)"]
theorem dyadicClassification_rest4_nf
    (h : SuffCoreHypRest4.{0, v} (v.adicCompletionIntegers F) (v.adicCompletion F))
    (Q : QuadraticForm (v.adicCompletion F) V) :
    DyadicClassification (v.adicCompletionIntegers F) Q :=
  dyadicClassification_of_rest4 Q (HasseIsoNF.localHilbertField_adicCompletion v) h

end NumberField

end QuadFormsKB.OMeara.Core4
