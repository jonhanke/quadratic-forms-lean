/-
# O'Meara 93:28, necessity of (ii) and (iii): the hyperbolic adjunctions

**Setting** (as in `Sec93FNecI.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, step 2, p. 270: "By making suitable hyperbolic adjunctions ... we can
assume that all fundamental dimensions are $\ge 3$ ... that the given Jordan splittings are saturated")
* `adjoin_sat`: for Jordan splittings `Ls`, `Ks` of the same lattice $L$ with fundamental norm generators $a$ of `Ls`,
  there is a lattice $L_2$ on a quadratic space $V_2 = (V \times (V \times V)) \times (V \times (V \times V))$ with
  Jordan splittings `Ls₂`, `Ks₂`, `Ls₂` saturated with all dimensions $\ge 3$, with the same $\mathfrak f_i$,
  $\mathfrak w_i$, $a_i$ as `Ls`, such that a representation $FL_{2,(i)} \to FK_{2,(i)} \perp \langle c\rangle$
  (resp. $FK_{2,(i)} \to FL_{2,(i)} \perp \langle c\rangle$) implies the same for $L$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecRepSat

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecRepAdjoin

open Sat93 Transfer28 NecBase NecBlock Merge28 NecDual NecMerge Adjoin28 NecI NecII RepTransfer NecRepMerge NecRepSat

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

set_option maxHeartbeats 1000000 in
/-- **The adjunctions of step 2** (O'Meara 1963, p. 270): see the file header. -/
theorem adjoin_sat {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) :
    ∃ (L₂ : Submodule R ((V × (V × V)) × (V × (V × V)))) (_ : L₂.IsLattice F)
      (Ls₂ Ks₂ : Fin t → Submodule R ((V × (V × V)) × (V × (V × V)))),
      (QuadraticMap.associated ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q)))).Nondegenerate ∧
      IsJordanSplitting ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) L₂ Ls₂ ∧
      IsJordanSplitting ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) L₂ Ks₂ ∧
      (∀ k, 3 ≤ finrank R (Ls₂ k)) ∧ IsSaturated ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) L₂ Ls₂ ∧
      IsFundNormGenerators ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) L₂ Ls₂ a ∧
      (∀ k l, fIdeal ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) L₂ Ls₂ k l = fIdeal Q L Ls k l) ∧
      (∀ k, fundWeight ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) L₂ Ls₂ k = fundWeight Q L Ls k) ∧
      (∀ (c : F), c ≠ 0 → ∀ i : Fin t,
        SpanRepresents ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) (jordanChain Ls₂ i) (jordanChain Ks₂ i) c →
          SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) c) ∧
      (∀ (c : F), c ≠ 0 → ∀ i : Fin t,
        SpanRepresents ((Q.prod (Q.prod Q)).prod (Q.prod (Q.prod Q))) (jordanChain Ks₂ i) (jordanChain Ls₂ i) c →
          SpanRepresents Q (jordanChain Ks i) (jordanChain Ls i) c) := by
  classical
  have hfg : L.FG := hLl.fg
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hscKL : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [show Fin.cast hT k = k from Fin.ext (by simp)] at this; exact this.symm
  -- (A1) `L ⊥ (L ⊥ L)`: all dimensions `≥ 3`
  set QW : QuadraticForm F (V × V) := Q.prod Q with hQW
  set H := L.prod L with hH
  set Hs : Fin t → Submodule R (V × V) := fun k => (Ls k).prod (Ls k) with hHs
  obtain ⟨hJH, hrkH⟩ := isJordanSplitting_prod Q Q hfg hfg hL hL.split (fun k => hL.modular k)
  have hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k) := fun k =>
    (isModular_prod Q Q (hL.modular k) (hL.modular k) (hLk k) (hLk k)).1
  have hgH : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L) := by
    intro k; rw [hQW, hH, subA_prod, normGroup_prod, sup_idem]
  have hHl : H.IsLattice F := isLattice_prod hLl hLl
  have hHk : ∀ k, (Hs k).FG := fun k => by
    show ((Ls k).prod (Ls k)).FG
    rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]
    exact ((hLk k).map _).sup ((hLk k).map _)
  obtain ⟨hJ₁, hrk₁⟩ := isJordanSplitting_prod Q QW hfg hHl.fg hL hJH.split hHmod
  obtain ⟨hJK₁, -⟩ := isJordanSplitting_prod Q QW hfg hHl.fg hK' hJH.split (fun k => (hscKL k).symm ▸ hHmod k)
  set Q₁ : QuadraticForm F (V × (V × V)) := Q.prod QW with hQ₁
  set L₁ := L.prod H with hL₁
  set Ls₁ : Fin t → Submodule R (V × (V × V)) := fun k => (Ls k).prod (Hs k) with hLs₁
  set Ks₁ : Fin t → Submodule R (V × (V × V)) := fun k => (Ks k).prod (Hs k) with hKs₁
  have hL₁l : L₁.IsLattice F := isLattice_prod hLl hHl
  have hQ₁nd : (QuadraticMap.associated Q₁).Nondegenerate :=
    nondegenerate_prod Q QW hQ (nondegenerate_prod Q Q hQ hQ)
  have hdim₁ : ∀ k, 3 ≤ finrank R (Ls₁ k) := by
    intro k
    rw [hrk₁ k, show finrank R ((Ls k).prod (Ls k)) = _ from hrkH k]
    have : 1 ≤ finrank R (Ls k) := Nat.one_le_iff_ne_zero.mpr fun h0 => by
      have hb := (hL.modular k).1
      obtain ⟨b⟩ := exists_basis (R := R) (F := F) (hLk k)
      have : Ls k = ⊥ := by
        rw [← span_basis_eq b, span_eq_bot]; rintro _ ⟨k', rfl⟩; exact Fin.elim0 (h0 ▸ k')
      rw [(hL.modular k).2.1.symm, this, scale_bot] at hb; exact hb rfl
    omega
  have hsc₁ : ∀ k, scale Q₁ (Ls₁ k) = scale Q (Ls k) := fun k =>
    (isModular_prod Q QW (hL.modular k) (hHmod k) (hLk k) (hHk k)).1.2.1
  have ha₁ : IsFundNormGenerators Q₁ L₁ Ls₁ a := isFundNormGenerators_prod Q QW hgH hsc₁ ha
  have hfI₁ : ∀ k l, fIdeal Q₁ L₁ Ls₁ k l = fIdeal Q L Ls k l := fun k l =>
    fIdeal_prod_eq Q QW hfg hHl.fg hL hJH.split hHmod hgH k l
  have hfw₁ : ∀ k, fundWeight Q₁ L₁ Ls₁ k = fundWeight Q L Ls k := fun k =>
    fundWeight_prod_eq Q QW hfg hHl.fg hL hJH.split hHmod hgH k
  -- (A2) a saturated splitting `Js` of `L₁` (93:21), adjoined
  obtain ⟨Js, hJs⟩ := (Sat93.saturatedSplittingExistence (R := R) hK Q₁).exists_saturated h2p hQ₁nd L₁ Ls₁ hJ₁ hdim₁
  have hL₁fg : L₁.FG := hL₁l.fg
  obtain ⟨hT₁, hJT₁⟩ := hJ₁.sameJordanType Q₁ hL₁fg hJs.1
  have hscJs : ∀ k, scale Q₁ (Js k) = scale Q₁ (Ls₁ k) := fun k => by
    have := (hJT₁ k).1; rw [show Fin.cast hT₁ k = k from Fin.ext (by simp)] at this; exact this.symm
  have hJsmod : ∀ k, IsModular Q₁ (scale Q₁ (Ls₁ k)) (Js k) := fun k => hscJs k ▸ hJs.1.modular k
  obtain ⟨hJ₂, hrk₂⟩ := isJordanSplitting_prod Q₁ Q₁ hL₁fg hL₁fg hJ₁ hJs.1.split hJsmod
  have hscK₁ : ∀ k, scale Q₁ (Ks₁ k) = scale Q₁ (Ls₁ k) := fun k => by
    obtain ⟨hT', hJT'⟩ := hJ₁.sameJordanType Q₁ hL₁fg hJK₁
    have := (hJT' k).1; rw [show Fin.cast hT' k = k from Fin.ext (by simp)] at this
    exact this.symm
  obtain ⟨hJK₂, -⟩ := isJordanSplitting_prod Q₁ Q₁ hL₁fg hL₁fg hJK₁ hJs.1.split (fun k => by
    rw [hscK₁ k]; exact hJsmod k)
  have hsc₂ : ∀ k, scale (Q₁.prod Q₁) ((Ls₁ k).prod (Js k)) = scale Q₁ (Ls₁ k) := fun k =>
    (isModular_prod Q₁ Q₁ (hJ₁.modular k) (hJsmod k) (FG.of_le hL₁fg (hJ₁.split.iSup_eq ▸ le_iSup Ls₁ k))
      (FG.of_le hL₁fg (hJs.1.split.iSup_eq ▸ le_iSup Js k))).1.2.1
  have hsat₂ : IsSaturated (Q₁.prod Q₁) (L₁.prod L₁) (fun k => (Ls₁ k).prod (Js k)) := by
    refine ⟨hJ₂, fun k => ?_⟩
    rw [fundNormGroup_prod Q₁ Q₁ Ls₁ Js (fun k => le_rfl) k (hsc₂ k), normGroup_prod,
      fundNormGroup_eq_of_isJordanSplitting hL₁fg hJs.1 hJ₁ k k rfl, ← hJs.2 k]
    exact sup_eq_right.mpr (hJs.2 k ▸ (fundNormGroup_eq_of_isJordanSplitting hL₁fg hJs.1 hJ₁ k k rfl).symm ▸
      normGroup_le_fundNormGroup Q₁ hL₁fg hJ₁ k)
  have hdim₂ : ∀ k, 3 ≤ finrank R ((Ls₁ k).prod (Js k)) := fun k => by rw [hrk₂ k]; have := hdim₁ k; omega
  have hL₂l : (L₁.prod L₁).IsLattice F := isLattice_prod hL₁l hL₁l
  have ha₂ : IsFundNormGenerators (Q₁.prod Q₁) (L₁.prod L₁) (fun k => (Ls₁ k).prod (Js k)) a :=
    isFundNormGenerators_prod Q₁ Q₁ (fun k => le_rfl) hsc₂ ha₁
  refine ⟨L₁.prod L₁, hL₂l, fun k => (Ls₁ k).prod (Js k), fun k => (Ks₁ k).prod (Js k),
    nondegenerate_prod Q₁ Q₁ hQ₁nd hQ₁nd, hJ₂, hJK₂, hdim₂, hsat₂, ha₂, fun k l => ?_, fun k => ?_, ?_, ?_⟩
  · rw [fIdeal_prod_eq Q₁ Q₁ hL₁fg hL₁fg hJ₁ hJs.1.split hJsmod (fun k => le_rfl) k l, hfI₁]
  · rw [fundWeight_prod_eq Q₁ Q₁ hL₁fg hL₁fg hJ₁ hJs.1.split hJsmod (fun k => le_rfl) k, hfw₁]
  · intro c hc i h
    have h₁ := rep_of_prod Q₁ Q₁ hL₁fg hL₁fg hJ₁ hJK₁ hJs.1.split hJsmod i hc h
    exact rep_of_prod Q QW hfg hHl.fg hL hK' hJH.split hHmod i hc h₁
  · intro c hc i h
    have h₁ := rep_of_prod Q₁ Q₁ hL₁fg hL₁fg hJK₁ hJ₁ hJs.1.split (fun k => by rw [hscK₁ k]; exact hJsmod k) i hc h
    exact rep_of_prod Q QW hfg hHl.fg hK' hL hJH.split (fun k => by rw [hscKL k]; exact hHmod k) i hc h₁

end Main

end QuadFormsKB.OMeara.NecRepAdjoin
