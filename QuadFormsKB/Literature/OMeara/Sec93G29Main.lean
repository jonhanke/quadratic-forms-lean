/-
# O'Meara 93:29 over a 2-adic field: the induction and the final theorems

**Setting** (as in `Sec93G29Core.lean`).

**Proves** (O'Meara 1963, §93G, proof of 93:29, sufficiency, pp. 277–279: "as in 93:28")
* `suffCore29`: the core with conditions (i), (ii): $K$ has a Jordan splitting with $K_1' \cong L_1$ (and conditions (i),
  (ii) for the new splitting, `resplit29`);
* `good_succ29`, `suff29_all`: the induction on the number $t$ of components (mirror of `Core4.good_succ4`,
  `Core4.suff_all4`), for every $t$;
* `twoAdicClassificationLe_twoAdic`, `twoAdicClassificationLe_twoAdic_nf`: **Theorem 93:29** (non-strict reading of (ii),
  `TwoAdicClassificationLe`) over a 2-adic field and over a 2-adic completion of a number field, unconditionally.
-/
import QuadFormsKB.Literature.OMeara.Sec93G29Core

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.G29

universe u v

section Induction

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass Nec93

/-- **The core of the induction step for 93:29** (O'Meara 1963, §93G, proof of 93:29, sufficiency, pp. 278–279, and
§93F, steps 4–8): in the situation of `core29`, $K$ has a saturated splitting $K_\bullet'$ with $K_1' \cong L_1$ which
still satisfies conditions (i), (ii) (`resplit29`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 278–279 (the core: K₁' ≅ L₁)"]
theorem suffCore29 (hHil : LocalHilbertField F) (h2 : IsTwoAdic R) (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ)
    (Ls Ks : Fin (m + 2) → Submodule R V) (a : Fin (m + 2) → F) (hLs : IsSaturated Q L Ls)
    (hKs : IsSaturated Q K Ks) (hd : ∀ k, finrank R (Ls k) = 4)
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond29 Q Ls Ks) :
    ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧ IsometricLat Q Q (Ls 0) (Ks' 0) ∧
      Cond29 Q Ls Ks' := by
  have h2p : ¬ IsUnit (2 : R) := (twoAdic_irreducible h2).not_isUnit
  have hDC : DyadicClassification R Q :=
    CoreTwoLast.dyadicClassification_twoAdic_unconditional Q h2 (fun [CharZero F] => hHil)
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  obtain ⟨Ks', hKs', hTK⟩ := core29 hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hDC hS hC
  refine ⟨Ks', hKs', ?_, resplit29 Q hHil hDC h2 hQ hLs.1 hKs.1 hKs'.1
    (sameJordan_of_sameFund Q h2 hLfg hKfg hLs.1 hKs.1 hS) hC⟩
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls 0)
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

/-- **The tails have the same fundamental invariants** (O'Meara 1963, p. 273, step 3): with $L_1 = K_1$, saturated
splittings, the tails $L^*$, $K^*$ have the same fundamental invariants. (The part of `SuffMain.tail_conds` not
involving the conditions.) -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (tails, fundamental invariants)"]
theorem sameFund_tail29 (Q : QuadraticForm F V) {L K : Submodule R V} {m : ℕ} {Ls Ks : Fin (m + 2) → Submodule R V}
    (hL : IsSaturated Q L Ls) (hK : IsSaturated Q K Ks) (a : Fin (m + 2) → F)
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    SameFundamentalInvariants Q Q (tailLat Ls) (tailLat Ks) (fun k : Fin (m + 1) => Ls k.succ)
      (fun k : Fin (m + 1) => Ks k.succ) (fun k => a k.succ) := by
  obtain ⟨⟨hh, hT⟩, haL, haK⟩ := hS
  have hc : ∀ k : Fin (m + 2), Fin.cast hh k = k := fun k => Fin.ext (by simp)
  refine ⟨⟨rfl, fun k => ⟨?_, ?_, ?_⟩⟩, isFundNormGenerators_tail Q hL a haL, isFundNormGenerators_tail Q hK a haK⟩
  · have := (hT k.succ).1; rw [hc] at this; exact this
  · have := (hT k.succ).2.1; rw [hc] at this; exact this
  · have := (hT k.succ).2.2; rw [hc] at this
    simp only [Fin.cast_eq_self]
    rw [fund_tail Q hL k, fund_tail Q hK k]; exact this

/-- **The induction step of the sufficiency of 93:29 in dimension $4$** (O'Meara 1963, §93G, proof of 93:29, p. 278,
"as in 93:28", step 3 of 93:28, p. 273): `Suff29` for $m + 1$ components gives `GoodSuff29Four` for $m + 2$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the induction step, dimension 4)"]
theorem good_succ29 (hHil : LocalHilbertField F) {m : ℕ} (ih : Suff29.{u, v} R F (m + 1)) :
    GoodSuff29Four.{u, v} R F (m + 2) := by
  intro V _ _ _ _ _ Q h2 hQ L K _ _ Ls Ks a hLs hKs hd3 hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  obtain ⟨Ks', hKs', hiso0, hC'⟩ := suffCore29 hHil h2 Q hQ L K m Ls Ks a hLs hKs hd hT (hsc 0 rfl) hS hC
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
  have hC'' : Cond29 Q Ls Ks'' := cond29_congr_right Q (hchfg hLfg hLle) (hchfg hKfg hKle)
    (fun i => by rw [hKs'', ← SuffSub.jordanChain_latMap]; exact isometricLat_latMap Q hσ _) hC'
  have h0 : Ls 0 = Ks'' 0 := hσK.symm
  have hSt := sameFund_tail29 Q hLs hK'sat a hS''
  have hCt := cond29_tail Q ⟨hLs, hK'sat.1, hLfg, hK'fg, h0⟩ hC''
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
  have hCW := (cond29_subLatIn Q hLW hKW hsLs hsKs hLtfg hKtfg).mp hCt
  have hisoW := ih (SuffSub.QW Q W) h2 hQW _ _ _ _ _ hJL hJK hSW hCW
  have hisoT := (SuffSub.isometricLat_subLatIn Q hLW hKW).mpr hisoW
  have hLK' := isometricLat_of_tail Q hL0fg hLtfg hoL hoK hisoT
  exact adj_isometricLat_trans Q Q Q hLK' (adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K))


/-- **The case $t = 0$ of 93:29.** -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (t = 0)"]
theorem suff29_zero : Suff29.{u, v} R F 0 := by
  intro V _ _ _ _ _ Q _ _ L K _ _ Ls Ks a hL hK _ _
  have h1 := hL.split.iSup_eq; have h2 := hK.split.iSup_eq
  rw [iSup_of_empty] at h1 h2
  rw [← h1, ← h2]; exact ⟨LinearEquiv.refl R _, fun x => rfl⟩

/-- **The case $t = 1$ of 93:29** (two modular lattices with the same norm group, 93:16). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (t = 1)"]
theorem suff29_one : Suff29.{u, v} R F 1 := by
  intro V _ _ _ _ _ Q _ _ L K _ _ Ls Ks a hL hK hS _
  have hL0 : Ls 0 = L := by have := hL.split.iSup_eq; rwa [iSup_unique] at this
  have hK0 : Ks 0 = K := by have := hK.split.iSup_eq; rwa [iSup_unique] at this
  obtain ⟨⟨h0, hT⟩, -, -⟩ := hS
  have hsc : scale Q (Ls 0) = scale Q (Ks 0) := (hT 0).2.1
  have hfg : fundNormGroup Q L Ls 0 = fundNormGroup Q K Ks 0 := (hT 0).2.2
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  simp only [fundNormGroup, fundSub] at hfg
  rw [← hL0, NecMerge.subA_eq_self Q le_rfl, ← hK0, NecMerge.subA_eq_self Q le_rfl, hK0, hL0] at hfg
  obtain ⟨x, -, y, -, hxy⟩ := exists_scale_eq Q (hL0 ▸ hLfg)
  have hmL := hL.modular 0
  have hmK := hK.modular 0
  rw [hL0] at hmL; rw [hK0] at hmK
  have hne : bil Q x y ≠ 0 := fun h => hmL.1 (by rw [← hL0, hxy, h, span_singleton_eq_bot])
  rw [hL0] at hxy hsc; rw [hK0] at hsc
  rw [← hsc, hxy] at hmK; rw [hxy] at hmL
  exact isometricLat_of_cls_eq Q (suff_base Q hne hmL hmK hfg)

/-- **The sufficiency of 93:29 for every number $t$ of components** (O'Meara 1963, §93G, proof of 93:29, pp. 277–279),
by induction on $t$: `good_succ29`, the reduction to dimension $4$ (`goodSuff29_of_four`) and to good lattices
(`suff29_of_good`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 277–279 (all t)"]
theorem suff29_all (hHil : LocalHilbertField F) : ∀ t, Suff29.{u, v} R F t
  | 0 => suff29_zero
  | 1 => suff29_one
  | m + 2 =>
    suff29_of_good (goodSuff29_of_four hHil (good_succ29 hHil (suff29_all hHil (m + 1))))

end Induction

section Final

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass Nec93

/-- **Theorem 93:29 over a 2-adic field** (O'Meara 1963, §93G, p. 277, with the non-strict reading of (ii), see
`TwoAdicClassificationLe`): for lattices $L$, $K$ on a regular quadratic space over a 2-adic field with Jordan
splittings of the same Jordan invariants, $\operatorname{cls} L = \operatorname{cls} K$ if and only if conditions (i), (ii)
hold. Unconditional: necessity from 93:28 (`cond29_of_cls_eq`, `CoreTwoLast.dyadicClassification_twoAdic_unconditional`),
sufficiency by `suff29_all`. Only the Hilbert symbol axioms (`LocalHilbertField`) are used. -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (2-adic field, non-strict reading of (ii), unconditional)"]
theorem twoAdicClassificationLe_twoAdic (Q : QuadraticForm F V)
    (hHil : ∀ [CharZero F], LocalHilbertField F) : TwoAdicClassificationLe R Q := by
  refine ⟨fun h2 hQ L K _ _ t Ls Ks hL hK hJ => ?_⟩
  have h2p : ¬ IsUnit (2 : R) := (twoAdic_irreducible h2).not_isUnit
  have : CharZero F := Main28.charZero_of_dyadic (R := R) h2p
  have hDC : DyadicClassification R Q := CoreTwoLast.dyadicClassification_twoAdic_unconditional Q h2 hHil
  refine ⟨fun hcls => cond29_of_cls_eq Q hDC h2 hQ L K Ls Ks hL hK hJ hcls, fun hC => ?_⟩
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_isLattice Q hQ ‹L.IsLattice F›
  have hregK := isRegular_of_isLattice Q hQ ‹K.IsLattice F›
  obtain ⟨u, hu⟩ : ∃ u : Fin t → ℤ, ∀ k, R ∙ ((2 : F) ^ u k) = normIdeal Q (Ls k) :=
    ⟨fun k => (Nec93.exists_two_pow_eq Q h2 hLfg hL k).choose,
      fun k => (Nec93.exists_two_pow_eq Q h2 hLfg hL k).choose_spec⟩
  have hS := sameFundamentalInvariants_of_sameJordanInvariants Q Q h2 hLfg hKfg hregL hregK hL hK hJ hu
  exact (cls_eq_of_mem Q (mem_cls_of_isometricLat Q
    (suff29_all hHil t Q h2 hQ L K Ls Ks _ hL hK hS hC))).symm

/-- **Theorem 93:29 over a 2-adic field, as stated in `Sec93G.lean`** (`TwoAdicClassification`, whose condition (ii) is
the same non-strict condition as in `Cond29`). -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (2-adic field, unconditional)"]
theorem twoAdicClassification_twoAdic (Q : QuadraticForm F V)
    (hHil : ∀ [CharZero F], LocalHilbertField F) : TwoAdicClassification R Q :=
  ⟨fun h2 hQ L K _ _ _ Ls Ks hL hK hJ => (twoAdicClassificationLe_twoAdic Q hHil).cls_eq_iff h2 hQ L K Ls Ks hL hK hJ⟩

end Final

section NumberField

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:29 over a 2-adic completion of a number field** (O'Meara 1963, §93G, p. 277, non-strict reading of
(ii)): at a place $\mathfrak p$ over $2$ with $2$ prime in $F_\mathfrak p$ (e.g. $\mathbb Q_2$), unconditionally (the
Hilbert symbol axioms are proved for completions of number fields). -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (2-adic completion of a number field, non-strict reading of (ii), unconditional)"]
theorem twoAdicClassificationLe_twoAdic_nf (Q : QuadraticForm (v.adicCompletion F) V) :
    TwoAdicClassificationLe (v.adicCompletionIntegers F) Q :=
  twoAdicClassificationLe_twoAdic Q (HasseIsoNF.localHilbertField_adicCompletion v)

/-- **Theorem 93:29 over a 2-adic completion of a number field, as stated in `Sec93G.lean`**, unconditionally. -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (2-adic completion of a number field, unconditional)"]
theorem twoAdicClassification_twoAdic_nf (Q : QuadraticForm (v.adicCompletion F) V) :
    TwoAdicClassification (v.adicCompletionIntegers F) Q :=
  twoAdicClassification_twoAdic Q (HasseIsoNF.localHilbertField_adicCompletion v)

end NumberField

end QuadFormsKB.OMeara.G29
