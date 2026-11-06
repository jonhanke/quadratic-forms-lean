/-
# O'Meara 93:28, sufficiency: the core with components of rank $8$

**Setting** (as in `Sec93FCore4.lean`).

O'Meara's steps 4, 6 and 7 (pp. 274–275) adjoin a unimodular hyperbolic plane $\langle A(0,0)\rangle$ to $K_1 \perp K_2$,
move it by 93:13 and 93:19, split a plane off again by 93:18 (v) and cancel it by 93:14. To do this inside the lattice
$K$ itself, we let the core start from components of rank $8$ (instead of O'Meara's $4$): then $K_1$ already contains
such a plane (93:18 (v)). A good situation of rank $4$ becomes one of rank $8$ by adjoining $L$ with the form $-Q$ to
both lattices (`SuffRed.suff_adj_hyp`), which keeps saturation, the hyperbolic spaces, the invariants and (i)–(iii).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, pp. 272–276)
* `GoodSuffN n t`, `SuffCoreN n`, `SuffCoreHypRestN n`: `Dim4.GoodSuff4`, `Core4.SuffCore4`, `Core4.SuffCoreHypRest4`
  with rank $4$ replaced by rank $n$;
* `suffCoreN_of_restN`, `good_succN`: as `Core4.suffCore4_of_rest4`, `Core4.good_succ4`, for every rank $n$;
* `goodSuff4_of_goodSuff8`: `GoodSuffN 8 t` implies `Dim4.GoodSuff4 t`;
* `suff_all8`, `dyadicClassification_of_rest8`, `dyadicClassification_rest8_nf`: Theorem 93:28 from
  `SuffCoreHypRestN 8`.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCore4

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Core8

universe u v

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass

section Core

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The sufficiency for good lattices with all components of rank $n$** (`Dim4.GoodSuff4` with $4$ replaced by
$n$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (components of rank n)"]
def GoodSuffN (n t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, finrank R (Ls k) = n) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

/-- **The core of the sufficiency with components of rank $n$** (`Core4.SuffCore4` with $4$ replaced by $n$; derived,
not a named statement). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 3–8, pp. 273–276 (components of rank n)"]
def SuffCoreN (n : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, finrank R (Ls k) = n) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧ IsometricLat Q Q (Ls 0) (Ks' 0) ∧
        Cond93 Q L Ls Ks' a

/-- **The core of 93:28 outside the directly decided cases, components of rank $n$** (`Core4.SuffCoreHypRest4` with
$4$ replaced by $n$): both splittings saturated, every $FL_k$ hyperbolic, $L_1$ unimodular, the same fundamental
invariants and conditions (i)–(iii), and the conditions at the first index do not already decide $FK_1$; then $K$ has
a saturated splitting whose first space $FK_1'$ is hyperbolic. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276 (components of rank n)"]
def SuffCoreHypRestN (n : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, finrank R (Ls k) = n) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ¬ ((∀ x ∈ fIdeal Q L Ls 0 1, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
        (fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
          fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))) →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
        ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
          finrank R (Ks' 0) ≤ 2 * finrank F T

variable {R F}

/-- **The core with components of rank $n$ from `SuffCoreHypRestN n`** (as `Core4.suffCore4_of_rest4`): in the cases
decided by the conditions at the first index the given splitting already has $FK_1$ hyperbolic
(`CoreCases.exists_lagrangian_of_cond`); then `CoreHyp.isometricLat_of_hyp` gives $K_1' \cong L_1$, and
`Resplit.cond93_resplit` keeps (i)–(iii). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 273–276 (components of rank n)"]
theorem suffCoreN_of_restN (hHil : LocalHilbertField F) {n : ℕ} (h : SuffCoreHypRestN.{u, v} R F n) :
    SuffCoreN.{u, v} R F n := by
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
    · exact h Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC hdec
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

/-- **The induction step of the sufficiency, components of rank $n$** (as `Core4.good_succ4`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (the induction step, components of rank n)"]
theorem good_succN {n : ℕ} (hcore : SuffCoreN.{u, v} R F n) {m : ℕ} (ih : Suff.{u, v} R F (m + 1)) :
    GoodSuffN.{u, v} R F n (m + 2) := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hd hT hsc hS hC
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

/-- **From rank $8$ to rank $4$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 2, p. 272: the adjunction
of $L^{-1}$-type lattices): a good situation with all components of rank $4$ becomes one with all components of rank
$8$ by adjoining $L$ with the form $-Q$ to both lattices (`SuffRed.suff_adj_hyp`); an isometry of the enlarged lattices
gives one of $L$ and $K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (adjoining L with -Q: rank 4 to rank 8)"]
theorem goodSuff4_of_goodSuff8 {t : ℕ} (h8 : GoodSuffN.{u, v} R F 8 t) : Dim4.GoodSuff4.{u, v} R F t := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs _ hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  obtain ⟨h3L, h3K, h3S, h3C, -, h3s, h3T, h3b⟩ := suff_adj_hyp Q hLfg hKfg hLs hKs ha0 hS hC
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls k)
  have hLL : (L.prod L).IsLattice F := isLattice_prod ‹_› ‹_›
  have hKL : (K.prod L).IsLattice F := isLattice_prod ‹_› ‹_›
  have hQn : (QuadraticMap.associated (Q.prod ((-1 : F) • Q))).Nondegenerate :=
    nondegenerate_prod Q _ hQ (nondegenerate_smul Q (by norm_num) hQ)
  refine h3b (h8 (Q.prod ((-1 : F) • Q)) h2p hQn (L.prod L) (K.prod L) _ _ a h3L h3K (fun k => ?_) h3T
    (fun k hk => by rw [h3s k]; exact hsc k hk) h3S h3C)
  have hm1 : (-1 : F) ≠ 0 := by norm_num
  have hspan1 : (R ∙ (-1 : F)) = 1 := by
    rw [Submodule.one_eq_span]; apply le_antisymm
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
  have hLn : IsJordanSplitting ((-1 : F) • Q) L Ls := isJordanSplitting_smul_form Q hm1 hLs.1
  have hscn : scale ((-1 : F) • Q) (Ls k) = scale Q (Ls k) := by rw [scale_smul_form, hspan1, one_mul]
  have hmod : IsModular ((-1 : F) • Q) (scale Q (Ls k)) (Ls k) := hscn ▸ hLn.modular k
  rw [(isModular_prod Q ((-1 : F) • Q) (hLs.1.modular k) hmod (hLk k) (hLk k)).2, hd k]

/-- **The sufficiency in 93:28 from the core with components of rank $8$**, for every number of Jordan components
(as `Core4.suff_all4`, through `goodSuff4_of_goodSuff8`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, pp. 272–273 (components of rank 8)"]
theorem suff_all8 (hHil : LocalHilbertField F) (hcore : SuffCoreN.{u, v} R F 8) : ∀ t, Suff.{u, v} R F t
  | 0 => suff_zero
  | 1 => suff_one
  | m + 2 => suff_of_good hHil (Dim4.goodSuff_of_goodSuff4 hHil
      (goodSuff4_of_goodSuff8 (good_succN hcore (suff_all8 hHil hcore (m + 1)))))

end Core

section Final

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28 from the core with components of rank $8$** (O'Meara 1963, §93F, pp. 267–276): over a dyadic
field with `LocalHilbertField`, `SuffCoreHypRestN 8` implies `DyadicClassification`. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (components of rank 8)"]
theorem dyadicClassification_of_rest8 (Q : QuadraticForm F V)
    (hHil : ∀ [CharZero F], LocalHilbertField F)
    (h : ∀ [CharZero F], SuffCoreHypRestN.{u, v} R F 8) : DyadicClassification R Q := by
  refine ⟨fun h2p hQ L K _ _ t Ls Ks a hL hK hS => ?_⟩
  have : CharZero F := Main28.charZero_of_dyadic (R := R) h2p
  refine ⟨Main28.necessity Q hHil h2p hQ hL hK hS, fun hC => ?_⟩
  exact (cls_eq_of_mem Q (mem_cls_of_isometricLat Q
    (suff_all8 hHil (suffCoreN_of_restN hHil h) t Q h2p hQ L K Ls Ks a hL hK hS hC))).symm

end Final

end QuadFormsKB.OMeara.Core8
