/-
# O'Meara 93:28, sufficiency, step 2: the conditions pass to adjoined lattices

**Setting** (as in `Sec93FAdjoin.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 2, p. 272: "if the given conditions hold for $L$ and
$K$ they will also hold for $L \perp \tilde L$ and $K \perp \tilde L$")
* `sameFund_prod`: the same fundamental invariants for $L \perp H$, $K \perp H$;
* `cond_prod`: the conditions (i)–(iii) for $L \perp H$, $K \perp H$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuff
import QuadFormsKB.Literature.OMeara.Sec93FSuffCancel

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.SuffRed

open Sat93 Transfer28 Adjoin28 NecI NecII RepTransfer Suff28 SuffCancel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

/-- **The fundamental invariants of $L \perp H$ and $K \perp H$** agree when those of $L$ and $K$ do and
$\mathfrak g(H^{\mathfrak s_k}) \subseteq \mathfrak g_k$. -/
theorem sameFund_prod {L K : Submodule R V} {H : Submodule R W} (hLfg : L.FG) (hKfg : K.FG) (hHfg : H.FG)
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} {Hs : Fin t → Submodule R W} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hH : IsOrthSplit QW H Hs) (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k))
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L))
    {a : Fin t → F} (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    SameFundamentalInvariants (Q.prod QW) (Q.prod QW) (L.prod H) (K.prod H) (fun k => (Ls k).prod (Hs k))
      (fun k => (Ks k).prod (Hs k)) a := by
  obtain ⟨⟨h0, hT⟩, haL, haK⟩ := hS
  have hc : ∀ k, Fin.cast h0 k = k := fun k => Fin.ext (by simp)
  have hsc : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by have := (hT k).2.1; rw [hc] at this; exact this.symm
  have hfund : ∀ k, fundNormGroup Q K Ks k = fundNormGroup Q L Ls k := fun k => by
    have := (hT k).2.2; rw [hc] at this; exact this.symm
  have hrk : ∀ k, finrank R (Ls k) = finrank R (Ks k) := fun k => by have := (hT k).1; rwa [hc] at this
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hKk : ∀ k, (Ks k).FG := fun k => FG.of_le hKfg (hK.split.iSup_eq ▸ le_iSup Ks k)
  have hHk : ∀ k, (Hs k).FG := fun k => FG.of_le hHfg (hH.iSup_eq ▸ le_iSup Hs k)
  have hHmodK : ∀ k, IsModular QW (scale Q (Ks k)) (Hs k) := fun k => (hsc k).symm ▸ hHmod k
  have hgK : ∀ k, normGroup QW (subA QW (scale Q (Ks k)) H) ≤ normGroup Q (subA Q (scale Q (Ks k)) K) := by
    intro k
    have := hfund k
    simp only [fundNormGroup, fundSub] at this
    rw [hsc k] at this ⊢; rw [this]; exact hg k
  have hscL : ∀ k, scale (Q.prod QW) ((Ls k).prod (Hs k)) = scale Q (Ls k) := fun k =>
    (isModular_prod Q QW (hL.modular k) (hHmod k) (hLk k) (hHk k)).1.2.1
  have hscK : ∀ k, scale (Q.prod QW) ((Ks k).prod (Hs k)) = scale Q (Ks k) := fun k =>
    (isModular_prod Q QW (hK.modular k) (hHmodK k) (hKk k) (hHk k)).1.2.1
  have hfL : ∀ k, fundNormGroup (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) k = fundNormGroup Q L Ls k :=
    fun k => fundNormGroup_prod Q QW Ls Hs hg k (hscL k)
  have hfK : ∀ k, fundNormGroup (Q.prod QW) (K.prod H) (fun k => (Ks k).prod (Hs k)) k = fundNormGroup Q K Ks k :=
    fun k => fundNormGroup_prod Q QW Ks Hs hgK k (hscK k)
  have hrkL := (isJordanSplitting_prod Q QW hLfg hHfg hL hH hHmod).2
  have hrkK := (isJordanSplitting_prod Q QW hKfg hHfg hK hH hHmodK).2
  refine ⟨⟨rfl, fun k => ⟨?_, ?_, ?_⟩⟩, fun k => ?_, fun k => ?_⟩
  · simp only [Fin.cast_eq_self]; rw [hrkL, hrkK, hrk]
  · simp only [Fin.cast_eq_self]; rw [hscL, hscK, hsc]
  · simp only [Fin.cast_eq_self]; rw [hfL, hfK, hfund]
  · exact isNormGenerator_fundSub_of_eq _ Q (hfL k) (haL k)
  · exact isNormGenerator_fundSub_of_eq _ Q (hfK k) (haK k)

/-- **The conditions (i)–(iii) pass to $L \perp H$, $K \perp H$** (O'Meara 1963, p. 272). -/
theorem cond_prod [FiniteDimensional F V] [FiniteDimensional F W] {L K : Submodule R V} {H : Submodule R W}
    (hLfg : L.FG) (hKfg : K.FG) (hHfg : H.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V} {Hs : Fin t → Submodule R W}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks) (hH : IsOrthSplit QW H Hs)
    (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k))
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L))
    {a : Fin t → F} (ha0 : ∀ k, a k ≠ 0) (hC : Cond93 Q L Ls Ks a) :
    Cond93 (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) (fun k => (Ks k).prod (Hs k)) a := by
  intro i j hij
  have hJH : IsJordanSplitting QW H Hs := isJordanSplitting_of_scales QW hH hL.scale_strictAnti hHmod
  rw [fIdeal_prod_eq Q QW hLfg hHfg hL hH hHmod hg, fundWeight_prod_eq Q QW hLfg hHfg hL hH hHmod hg,
    fundWeight_prod_eq Q QW hLfg hHfg hL hH hHmod hg, jordanChain_prod, jordanChain_prod]
  obtain ⟨h1, h2, h3⟩ := hC i j hij
  have hLfg' : (jordanChain Ls i).FG := FG.of_le hLfg (jordanChain_le hL.split i)
  have hKfg' : (jordanChain Ks i).FG := FG.of_le hKfg (jordanChain_le hK.split i)
  have hHfg' : (jordanChain Hs i).FG := FG.of_le hHfg (jordanChain_le hH i)
  have hKreg := isRegular_of_isJordanSplitting Q hKfg' (isJordanSplitting_jordanChain Q hK i)
  have hHreg := isRegular_of_isJordanSplitting QW hHfg' (isJordanSplitting_jordanChain QW hJH i)
  exact ⟨(discQuot_prod_iff Q QW hLfg' hKfg' hHfg' hKreg hHreg).mpr h1,
    fun h => (spanRepresents_prod_iff Q QW hKreg hHreg (ha0 j)).mpr (h2 h),
    fun h => (spanRepresents_prod_iff Q QW hKreg hHreg (ha0 i)).mpr (h3 h)⟩

/-- **One adjunction step of the sufficiency** (O'Meara 1963, p. 272): adjoining $H = H_1 \perp \cdots \perp H_t$
($H_k$ $\mathfrak s_k$-modular, $\mathfrak gH_k \subseteq \mathfrak g_k$) to $L$ and to $K$ preserves the Jordan
splittings, the fundamental invariants and the conditions, and an isometry $L \perp H \cong K \perp H$ gives
$L \cong K$ (93:14a). -/
theorem suff_adjoin_step [FiniteDimensional F V] [FiniteDimensional F W] {L K : Submodule R V}
    {H : Submodule R W} (hLfg : L.FG) (hKfg : K.FG) (hHfg : H.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    {Hs : Fin t → Submodule R W} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    (hH : IsOrthSplit QW H Hs) (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k))
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L))
    (hgk : ∀ k, normGroup QW (Hs k) ≤ fundNormGroup Q L Ls k) {a : Fin t → F} (ha0 : ∀ k, a k ≠ 0)
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) :
    IsJordanSplitting (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) ∧
    IsJordanSplitting (Q.prod QW) (K.prod H) (fun k => (Ks k).prod (Hs k)) ∧
    SameFundamentalInvariants (Q.prod QW) (Q.prod QW) (L.prod H) (K.prod H) (fun k => (Ls k).prod (Hs k))
      (fun k => (Ks k).prod (Hs k)) a ∧
    Cond93 (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) (fun k => (Ks k).prod (Hs k)) a ∧
    (IsometricLat (Q.prod QW) (Q.prod QW) (L.prod H) (K.prod H) → IsometricLat Q Q L K) := by
  obtain ⟨⟨h0, hT⟩, -, -⟩ := id hS
  have hc : ∀ k, Fin.cast h0 k = k := fun k => Fin.ext (by simp)
  have hsc : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by have := (hT k).2.1; rw [hc] at this; exact this.symm
  have hfund : ∀ k, fundNormGroup Q K Ks k = fundNormGroup Q L Ls k := fun k => by
    have := (hT k).2.2; rw [hc] at this; exact this.symm
  have hJH : IsJordanSplitting QW H Hs := isJordanSplitting_of_scales QW hH hL.scale_strictAnti hHmod
  have hHmodK : ∀ k, IsModular QW (scale Q (Ks k)) (Hs k) := fun k => (hsc k).symm ▸ hHmod k
  refine ⟨(isJordanSplitting_prod Q QW hLfg hHfg hL hH hHmod).1, (isJordanSplitting_prod Q QW hKfg hHfg hK hH
    hHmodK).1, sameFund_prod Q QW hLfg hKfg hHfg hL hK hH hHmod hg hS, ?_, ?_⟩
  · exact cond_prod Q QW hLfg hKfg hHfg hL hK hH hHmod hg ha0 hC
  · intro hiso
    have hHmod' : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k) := hHmod
    refine isometricLat_cancel_prod Q QW hLfg hKfg hHfg hH hHmod' (fun k => hgk k) (fun k => ?_) hiso
    have := hfund k
    simp only [fundNormGroup, fundSub] at this
    rw [hsc k] at this
    rw [this]; exact hgk k

/-- **Goodification, step (A1)** (O'Meara 1963, p. 272, "by making suitable hyperbolic adjunctions we can increase
all the fundamental dimensions"; here the adjoined lattice is $L \perp L$): the data for $L \perp (L \perp L)$ and
$K \perp (L \perp L)$, with all dimensions $\ge 3$. -/
theorem suff_adj_dims [FiniteDimensional F V] {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    {a : Fin t → F} (ha0 : ∀ k, a k ≠ 0) (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (hC : Cond93 Q L Ls Ks a) :
    IsJordanSplitting (Q.prod (Q.prod Q)) (L.prod (L.prod L)) (fun k => (Ls k).prod ((Ls k).prod (Ls k))) ∧
    IsJordanSplitting (Q.prod (Q.prod Q)) (K.prod (L.prod L)) (fun k => (Ks k).prod ((Ls k).prod (Ls k))) ∧
    SameFundamentalInvariants (Q.prod (Q.prod Q)) (Q.prod (Q.prod Q)) (L.prod (L.prod L)) (K.prod (L.prod L))
      (fun k => (Ls k).prod ((Ls k).prod (Ls k))) (fun k => (Ks k).prod ((Ls k).prod (Ls k))) a ∧
    Cond93 (Q.prod (Q.prod Q)) (L.prod (L.prod L)) (fun k => (Ls k).prod ((Ls k).prod (Ls k)))
      (fun k => (Ks k).prod ((Ls k).prod (Ls k))) a ∧
    (∀ k, 3 ≤ finrank R ((Ls k).prod ((Ls k).prod (Ls k)))) ∧
    (∀ k, scale (Q.prod (Q.prod Q)) ((Ls k).prod ((Ls k).prod (Ls k))) = scale Q (Ls k)) ∧
    (IsometricLat (Q.prod (Q.prod Q)) (Q.prod (Q.prod Q)) (L.prod (L.prod L)) (K.prod (L.prod L)) →
      IsometricLat Q Q L K) := by
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  obtain ⟨hJH, hrkH⟩ := isJordanSplitting_prod Q Q hLfg hLfg hL hL.split (fun k => hL.modular k)
  have hHmod : ∀ k, IsModular (Q.prod Q) (scale Q (Ls k)) ((Ls k).prod (Ls k)) := fun k =>
    (isModular_prod Q Q (hL.modular k) (hL.modular k) (hLk k) (hLk k)).1
  have hHfg : (L.prod L).FG := by
    rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]; exact (hLfg.map _).sup (hLfg.map _)
  have hg : ∀ k, normGroup (Q.prod Q) (subA (Q.prod Q) (scale Q (Ls k)) (L.prod L)) ≤
      normGroup Q (subA Q (scale Q (Ls k)) L) := fun k => by rw [subA_prod, normGroup_prod, sup_idem]
  have hgk : ∀ k, normGroup (Q.prod Q) ((Ls k).prod (Ls k)) ≤ fundNormGroup Q L Ls k := fun k => by
    rw [normGroup_prod, sup_idem]; exact normGroup_le_fundNormGroup Q hLfg hL k
  obtain ⟨h1, h2, h3, h4, h5⟩ := suff_adjoin_step Q (Q.prod Q) hLfg hKfg hHfg hL hK hJH.split hHmod hg hgk ha0 hS hC
  refine ⟨h1, h2, h3, h4, fun k => ?_, fun k => ?_, h5⟩
  · rw [(isJordanSplitting_prod Q (Q.prod Q) hLfg hHfg hL hJH.split hHmod).2, hrkH k]
    have : 1 ≤ finrank R (Ls k) := Nat.one_le_iff_ne_zero.mpr fun h0 => by
      have hb := (hL.modular k).1
      obtain ⟨b⟩ := exists_basis (R := R) (F := F) (hLk k)
      have : Ls k = ⊥ := by
        rw [← span_basis_eq b, span_eq_bot]; rintro _ ⟨k', rfl⟩; exact Fin.elim0 (h0 ▸ k')
      rw [(hL.modular k).2.1.symm, this, scale_bot] at hb; exact hb rfl
    omega
  · exact (isModular_prod Q (Q.prod Q) (hL.modular k) (hHmod k) (hLk k) (FG.of_le hHfg
      (hJH.split.iSup_eq ▸ le_iSup (fun i => (Ls i).prod (Ls i)) k))).1.2.1

/-- **Goodification, step (A2)** (O'Meara 1963, p. 272: "take a saturated splitting $L = J_1 \perp \cdots \perp J_t$ and
make the adjunction of $J_1 \perp \cdots \perp J_t$ to $L$ and to $K$"): with a saturated splitting `Js` of $L$
(93:21), the splittings $(L_k \perp J_k)$ of $L \perp L$ and $(K_k \perp J_k)$ of $K \perp L$ are saturated. -/
theorem suff_adj_sat [FiniteDimensional F V] {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls Ks Js : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    (hJs : IsSaturated Q L Js) {a : Fin t → F} (ha0 : ∀ k, a k ≠ 0)
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) :
    IsSaturated (Q.prod Q) (L.prod L) (fun k => (Ls k).prod (Js k)) ∧
    IsSaturated (Q.prod Q) (K.prod L) (fun k => (Ks k).prod (Js k)) ∧
    SameFundamentalInvariants (Q.prod Q) (Q.prod Q) (L.prod L) (K.prod L) (fun k => (Ls k).prod (Js k))
      (fun k => (Ks k).prod (Js k)) a ∧
    Cond93 (Q.prod Q) (L.prod L) (fun k => (Ls k).prod (Js k)) (fun k => (Ks k).prod (Js k)) a ∧
    (∀ k, finrank R (Ls k) ≤ finrank R ((Ls k).prod (Js k))) ∧
    (∀ k, scale (Q.prod Q) ((Ls k).prod (Js k)) = scale Q (Ls k)) ∧
    (IsometricLat (Q.prod Q) (Q.prod Q) (L.prod L) (K.prod L) → IsometricLat Q Q L K) := by
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hJk : ∀ k, (Js k).FG := fun k => FG.of_le hLfg (hJs.1.split.iSup_eq ▸ le_iSup Js k)
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hLfg hJs.1
  have hscJ : ∀ k, scale Q (Js k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [show Fin.cast hT k = k from Fin.ext (by simp)] at this; exact this.symm
  have hHmod : ∀ k, IsModular Q (scale Q (Ls k)) (Js k) := fun k => hscJ k ▸ hJs.1.modular k
  have hfJ : ∀ k, fundNormGroup Q L Js k = fundNormGroup Q L Ls k := fun k =>
    fundNormGroup_eq_of_isJordanSplitting hLfg hL hJs.1 k k rfl
  have hgk : ∀ k, normGroup Q (Js k) ≤ fundNormGroup Q L Ls k := fun k => by rw [hJs.2 k, hfJ k]
  obtain ⟨h1, h2, h3, h4, h5⟩ := suff_adjoin_step Q Q hLfg hKfg hLfg hL hK hJs.1.split hHmod (fun k => le_rfl)
    hgk ha0 hS hC
  have hsc : ∀ k, scale (Q.prod Q) ((Ls k).prod (Js k)) = scale Q (Ls k) := fun k =>
    (isModular_prod Q Q (hL.modular k) (hHmod k) (hLk k) (hJk k)).1.2.1
  obtain ⟨⟨h0, hTK⟩, -, -⟩ := id hS
  have hfund : ∀ k, fundNormGroup Q K Ks k = fundNormGroup Q L Ls k := fun k => by
    have := (hTK k).2.2; rw [show Fin.cast h0 k = k from Fin.ext (by simp)] at this; exact this.symm
  obtain ⟨⟨h0', hT'⟩, -, -⟩ := id h3
  have hfund' : ∀ k, fundNormGroup (Q.prod Q) (K.prod L) (fun k => (Ks k).prod (Js k)) k =
      fundNormGroup (Q.prod Q) (L.prod L) (fun k => (Ls k).prod (Js k)) k := fun k => by
    have := (hT' k).2.2; rw [show Fin.cast h0' k = k from Fin.ext (by simp)] at this; exact this.symm
  have hfL : ∀ k, fundNormGroup (Q.prod Q) (L.prod L) (fun k => (Ls k).prod (Js k)) k = fundNormGroup Q L Ls k :=
    fun k => fundNormGroup_prod Q Q Ls Js (fun k => le_rfl) k (hsc k)
  refine ⟨⟨h1, fun k => ?_⟩, ⟨h2, fun k => ?_⟩, h3, h4, fun k => ?_, hsc, h5⟩
  · rw [hfL, normGroup_prod, hJs.2 k, hfJ k]
    exact sup_eq_right.mpr (normGroup_le_fundNormGroup Q hLfg hL k)
  · rw [hfund', hfL, normGroup_prod, hJs.2 k, hfJ k]
    exact sup_eq_right.mpr ((hfund k) ▸ normGroup_le_fundNormGroup Q hKfg hK k)
  · rw [(isJordanSplitting_prod Q Q hLfg hLfg hL hJs.1.split hHmod).2]; omega

set_option maxHeartbeats 1000000 in
/-- **Goodification, step (A3)** (O'Meara 1963, p. 272: "A similar argument involving the adjunction of the lattice
$L^{-1} = L_1^{-1} \perp \cdots \perp L_t^{-1}$ allows us to assume that each space $FL_i$ is hyperbolic"): adjoin $L$
with the form $-Q$ to $L$ and to $K$ (saturated splittings stay saturated). -/
theorem suff_adj_hyp [FiniteDimensional F V] {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsSaturated Q L Ls) (hK : IsSaturated Q K Ks) {a : Fin t → F}
    (ha0 : ∀ k, a k ≠ 0) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) :
    IsSaturated (Q.prod ((-1 : F) • Q)) (L.prod L) (fun k => (Ls k).prod (Ls k)) ∧
    IsSaturated (Q.prod ((-1 : F) • Q)) (K.prod L) (fun k => (Ks k).prod (Ls k)) ∧
    SameFundamentalInvariants (Q.prod ((-1 : F) • Q)) (Q.prod ((-1 : F) • Q)) (L.prod L) (K.prod L)
      (fun k => (Ls k).prod (Ls k)) (fun k => (Ks k).prod (Ls k)) a ∧
    Cond93 (Q.prod ((-1 : F) • Q)) (L.prod L) (fun k => (Ls k).prod (Ls k)) (fun k => (Ks k).prod (Ls k)) a ∧
    (∀ k, finrank R (Ls k) ≤ finrank R ((Ls k).prod (Ls k))) ∧
    (∀ k, scale (Q.prod ((-1 : F) • Q)) ((Ls k).prod (Ls k)) = scale Q (Ls k)) ∧
    (∀ k, ∃ T : Submodule F (V × V), (∀ x ∈ T, (Q.prod ((-1 : F) • Q)) x = 0) ∧
      (∀ x ∈ T, x ∈ span F (((Ls k).prod (Ls k) : Submodule R (V × V)) : Set (V × V))) ∧
      finrank R ((Ls k).prod (Ls k)) ≤ 2 * finrank F T) ∧
    (IsometricLat (Q.prod ((-1 : F) • Q)) (Q.prod ((-1 : F) • Q)) (L.prod L) (K.prod L) → IsometricLat Q Q L K) := by
  set Qn : QuadraticForm F V := (-1 : F) • Q with hQn
  have hm1 : (-1 : F) ≠ 0 := by norm_num
  have hspan1 : (R ∙ (-1 : F)) = 1 := by
    rw [Submodule.one_eq_span]; apply le_antisymm
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.1.split.iSup_eq ▸ le_iSup Ls k)
  have hLn : IsJordanSplitting Qn L Ls := isJordanSplitting_smul_form Q hm1 hL.1
  have hscn : ∀ k, scale Qn (Ls k) = scale Q (Ls k) := fun k => by
    rw [hQn, scale_smul_form, hspan1, one_mul]
  have hHmod : ∀ k, IsModular Qn (scale Q (Ls k)) (Ls k) := fun k => (hscn k) ▸ hLn.modular k
  have hg : ∀ k, normGroup Qn (subA Qn (scale Q (Ls k)) L) ≤ normGroup Q (subA Q (scale Q (Ls k)) L) := by
    intro k
    have h1 := FundAux.subA_smul_form Q hm1 (scale Q (Ls k)) L
    rw [hspan1, one_mul] at h1
    rw [h1, hQn, normGroup_neg_form]
  have hgk : ∀ k, normGroup Qn (Ls k) ≤ fundNormGroup Q L Ls k := fun k => by
    rw [hQn, normGroup_neg_form, hL.2 k]
  obtain ⟨h1, h2, h3, h4, h5⟩ := suff_adjoin_step Q Qn hLfg hKfg hLfg hL.1 hK.1 hLn.split hHmod hg hgk ha0 hS hC
  have hsc : ∀ k, scale (Q.prod Qn) ((Ls k).prod (Ls k)) = scale Q (Ls k) := fun k =>
    (isModular_prod Q Qn (hL.1.modular k) (hHmod k) (hLk k) (hLk k)).1.2.1
  have hfL : ∀ k, fundNormGroup (Q.prod Qn) (L.prod L) (fun k => (Ls k).prod (Ls k)) k = fundNormGroup Q L Ls k :=
    fun k => fundNormGroup_prod Q Qn Ls Ls hg k (hsc k)
  obtain ⟨⟨h0, hTK⟩, -, -⟩ := id hS
  have hfund : ∀ k, fundNormGroup Q K Ks k = fundNormGroup Q L Ls k := fun k => by
    have := (hTK k).2.2; rw [show Fin.cast h0 k = k from Fin.ext (by simp)] at this; exact this.symm
  obtain ⟨⟨h0', hT'⟩, -, -⟩ := id h3
  have hfund' : ∀ k, fundNormGroup (Q.prod Qn) (K.prod L) (fun k => (Ks k).prod (Ls k)) k =
      fundNormGroup (Q.prod Qn) (L.prod L) (fun k => (Ls k).prod (Ls k)) k := fun k => by
    have := (hT' k).2.2; rw [show Fin.cast h0' k = k from Fin.ext (by simp)] at this; exact this.symm
  have hnG : ∀ k, normGroup Qn (Ls k) = normGroup Q (Ls k) := fun k => by rw [hQn, normGroup_neg_form]
  refine ⟨⟨h1, fun k => ?_⟩, ⟨h2, fun k => ?_⟩, h3, h4, fun k => ?_, hsc, fun k => ?_, h5⟩
  · rw [hfL, normGroup_prod, hnG, sup_idem, hL.2 k]
  · rw [hfund', hfL, normGroup_prod, hnG, hK.2 k, hfund k, hL.2 k, sup_idem]
  · rw [(isJordanSplitting_prod Q Qn hLfg hLfg hL.1 hLn.split hHmod).2]; omega
  · -- the diagonal of `F L_k ⊥ F L_k⁻¹` is totally isotropic of half the dimension
    set M := Ls k
    refine ⟨(span F (M : Set V)).map (LinearMap.prod LinearMap.id LinearMap.id), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨v, -, rfl⟩ := Submodule.mem_map.mp hx
      show (Q.prod ((-1 : F) • Q)) (v, v) = 0
      rw [QuadraticMap.prod_apply, smul_apply]; simp
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      have hs1 : ∀ v ∈ span F (M : Set V), (v, (0 : V)) ∈ span F ((M.prod M : Submodule R (V × V)) : Set (V × V)) :=
        fun v hv => span_induction (p := fun v _ => (v, (0 : V)) ∈ span F ((M.prod M : Submodule R (V × V)) : Set _))
          (fun x hx => subset_span (show (x, (0 : V)) ∈ ((M.prod M : Submodule R (V × V)) : Set (V × V)) from
            ⟨hx, zero_mem _⟩)) (zero_mem _) (fun a b _ _ ha hb => by simpa using add_mem ha hb)
          (fun c a _ ha => by simpa using smul_mem _ c ha) hv
      have hs2 : ∀ v ∈ span F (M : Set V), ((0 : V), v) ∈ span F ((M.prod M : Submodule R (V × V)) : Set (V × V)) :=
        fun v hv => span_induction (p := fun v _ => ((0 : V), v) ∈ span F ((M.prod M : Submodule R (V × V)) : Set _))
          (fun x hx => subset_span (show ((0 : V), x) ∈ ((M.prod M : Submodule R (V × V)) : Set (V × V)) from
            ⟨zero_mem _, hx⟩)) (zero_mem _) (fun a b _ _ ha hb => by simpa using add_mem ha hb)
          (fun c a _ ha => by simpa using smul_mem _ c ha) hv
      simpa using add_mem (hs1 v hv) (hs2 v hv)
    · have hprod : finrank R (M.prod M) = finrank R M + finrank R M := by
        rw [(isModular_prod Q Qn (hL.1.modular k) (hHmod k) (hLk k) (hLk k)).2]
      have hinj : Function.Injective (LinearMap.prod (LinearMap.id : V →ₗ[F] V) LinearMap.id) :=
        fun a b h => by simpa using congrArg Prod.fst h
      rw [hprod, ← (Submodule.equivMapOfInjective _ hinj (span F (M : Set V))).finrank_eq,
        ← finrank_eq_finrank_span (F := F) M]
      omega

section ScaleCond

variable [CharZero F] [FiniteDimensional F V]

/-- The threshold $4a\mathfrak w^{-1}$ of conditions (ii), (iii) is unchanged by scaling: $(4\alpha a)(\alpha
\mathfrak w)^{-1} = 4a\mathfrak w^{-1}$ for $\mathfrak w = b\mathfrak o$, $b \ne 0$. -/
theorem threshold_smul {α : F} (hα : α ≠ 0) (a : F) {b : F} (hb : b ≠ 0) :
    (4 * (α * a)) • ((1 : Submodule R F) / (α • (R ∙ b))) = (4 * a) • ((1 : Submodule R F) / (R ∙ b)) := by
  rw [FIdealAux.smul_span_singleton, Dual93.one_div_span (mul_ne_zero hα hb), Dual93.one_div_span hb,
    FIdealAux.smul_span_singleton, FIdealAux.smul_span_singleton]
  congr 1; field_simp

/-- **The conditions under scaling of the space** (O'Meara 1963, 93:23): (i)–(iii) for $L, K$ on $V$ with norm
generators $a_k$ hold iff they hold on $V^\alpha$ with $\alpha a_k$. -/
theorem cond_smul {α : F} (hα : α ≠ 0) {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) (h2p : ¬ IsUnit (2 : R))
    (hreg : IsRegular Q L) {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hrk : ∀ k, finrank R (Ls k) = finrank R (Ks k)) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (hC : Cond93 Q L Ls Ks a) :
    Cond93 (α • Q) L Ls Ks (fun k => α * a k) := by
  have hwgen : ∀ k, ∃ b : F, b ≠ 0 ∧ fundWeight Q L Ls k = R ∙ b := by
    intro k
    obtain ⟨b, hb⟩ := Sat93.exists_weightGen Q h2p (fundSub_fg Q hLfg Ls k) (isRegular_fundSub Q hLfg hreg hL k)
      (fundSub_ne_bot Q hLfg hL k)
    have ha0 := (ha k).ne_zero Q (isRegular_fundSub Q hLfg hreg hL k) (fundSub_ne_bot Q hLfg hL k)
    exact ⟨b, weight_gen_ne_zero Q (ha k) ha0 hb, hb.symm⟩
  intro i j hij
  obtain ⟨h1, h2, h3⟩ := hC i j hij
  obtain ⟨bj, hbj, hwj⟩ := hwgen j
  obtain ⟨bi, hbi, hwi⟩ := hwgen i
  have hrkc : finrank R (jordanChain Ls i) = finrank R (jordanChain Ks i) := by
    rw [(isJordanSplitting_jordanChain Q hL i).split.finrank_eq_sum (F := F),
      (isJordanSplitting_jordanChain Q hK i).split.finrank_eq_sum (F := F)]
    exact Finset.sum_congr rfl fun k _ => hrk _
  rw [fIdeal_smul_form Q hα, fundWeight_smul_form Q hα, fundWeight_smul_form Q hα, hwj, hwi,
    threshold_smul hα (a j) hbj, threshold_smul hα (a i) hbi]
  rw [hwj] at h2; rw [hwi] at h3
  exact ⟨(discQuot_smul_iff Q hα hrkc).mpr h1, fun h => (spanRepresents_smul_iff Q hα _ _ (a j)).mpr (h2 h),
    fun h => (spanRepresents_smul_iff Q hα _ _ (a i)).mpr (h3 h)⟩

/-- **The fundamental invariants under scaling** (O'Meara 1963, 93:23): the same fundamental invariants on $V$ with
norm generators $a_k$ give the same ones on $V^\alpha$ with $\alpha a_k$. -/
theorem sameFund_smul {α : F} (hα : α ≠ 0) {L K : Submodule R V} {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    {a : Fin t → F} (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    SameFundamentalInvariants (α • Q) (α • Q) L K Ls Ks (fun k => α * a k) := by
  obtain ⟨⟨h0, hT⟩, haL, haK⟩ := hS
  refine ⟨⟨h0, fun k => ⟨(hT k).1, ?_, ?_⟩⟩, isFundNormGenerators_smul_form Q hα haL,
    isFundNormGenerators_smul_form Q hα haK⟩
  · rw [scale_smul_form, scale_smul_form, (hT k).2.1]
  · rw [fundNormGroup_smul_form Q hα, fundNormGroup_smul_form Q hα, (hT k).2.2]

end ScaleCond

end QuadFormsKB.OMeara.SuffRed
