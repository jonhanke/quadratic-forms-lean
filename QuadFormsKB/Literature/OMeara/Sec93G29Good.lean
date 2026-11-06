/-
# O'Meara 93:29 over a 2-adic field: reduction to good lattices

**Setting** (as in `Sec93G29Trans.lean`).

**Defines** `Suff29`, `GoodSuff29`: the sufficiency of 93:29 for $t$ Jordan components, and for good lattices
(saturated splittings, dimensions $\ge 3$, hyperbolic spaces $FL_k$, $\mathfrak sL_1 = \mathfrak o$).

**Proves** (O'Meara 1963, §93G, proof of 93:29, sufficiency, p. 278: "as in 93:28")
* `suff29_adjoin_step`, `suff29_adj_dims`, `suff29_adj_hyp`: the adjunctions $L \perp (L \perp L)$ and $L^{-1}$ keep the
  Jordan splittings, fundamental invariants and conditions (i), (ii);
* `suff29_of_good`: `GoodSuff29 t` implies `Suff29 t` (the saturation of the splittings, step (A2) of 93:28, is automatic
  over a 2-adic field; scaling by $2^{-k}$ makes $L_1$ unimodular).
-/
import QuadFormsKB.Literature.OMeara.Sec93G29Trans

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.G29

universe u v

section Adjoin

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

open Sat93 Adjoin28 NecI NecII RepTransfer Transfer28 SuffCancel SuffRed Nec93

/-- Over a 2-adic field the norms of the components are determined by the fundamental invariants. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to good lattices)"]
theorem normIdeal_eq_of_sameFund (h2 : IsTwoAdic R) {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} {a : Fin t → F} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (k : Fin t) :
    normIdeal Q (Ks k) = normIdeal Q (Ls k) := by
  obtain ⟨⟨h0, hT⟩, -, -⟩ := id hS
  have e := (hT k).2.2
  rw [show Fin.cast h0 k = k from Fin.ext rfl] at e
  rw [← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hKfg hK k, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hLfg hL k]
  unfold fundNormIdeal
  rw [normIdeal_eq_span_normGroup, normIdeal_eq_span_normGroup]
  exact congrArg (fun g : AddSubgroup F => span R (g : Set F)) e.symm

/-- **One adjunction step of the sufficiency of 93:29** (O'Meara 1963, p. 278, as for 93:28, p. 272): adjoining
$H = H_1 \perp \cdots \perp H_t$ ($H_k$ $\mathfrak s_k$-modular, $\mathfrak nH_k \subseteq \mathfrak nL_k$,
$\mathfrak gH_k \subseteq \mathfrak g_k$) to $L$ and to $K$ preserves the Jordan splittings, the fundamental invariants and
conditions (i), (ii), and an isometry $L \perp H \cong K \perp H$ gives $L \cong K$ (93:14a). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to good lattices)"]
theorem suff29_adjoin_step [FiniteDimensional F V] [FiniteDimensional F W] (h2 : IsTwoAdic R) {L K : Submodule R V}
    {H : Submodule R W} (hLfg : L.FG) (hKfg : K.FG) (hHfg : H.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    {Hs : Fin t → Submodule R W} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    (hH : IsOrthSplit QW H Hs) (hHmod : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k))
    (hg : ∀ k, normGroup QW (subA QW (scale Q (Ls k)) H) ≤ normGroup Q (subA Q (scale Q (Ls k)) L))
    (hgk : ∀ k, normGroup QW (Hs k) ≤ fundNormGroup Q L Ls k)
    (hnL : ∀ k, normIdeal QW (Hs k) ≤ normIdeal Q (Ls k)) {a : Fin t → F}
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond29 Q Ls Ks) :
    IsJordanSplitting (Q.prod QW) (L.prod H) (fun k => (Ls k).prod (Hs k)) ∧
    IsJordanSplitting (Q.prod QW) (K.prod H) (fun k => (Ks k).prod (Hs k)) ∧
    SameFundamentalInvariants (Q.prod QW) (Q.prod QW) (L.prod H) (K.prod H) (fun k => (Ls k).prod (Hs k))
      (fun k => (Ks k).prod (Hs k)) a ∧
    Cond29 (Q.prod QW) (fun k => (Ls k).prod (Hs k)) (fun k => (Ks k).prod (Hs k)) ∧
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
  · refine cond29_prod Q QW hLfg hKfg hHfg hL hK hH hHmod hHmodK hnL (fun k => ?_) hC
    rw [normIdeal_eq_of_sameFund Q h2 hLfg hKfg hL hK hS k]; exact hnL k
  · intro hiso
    have hHmod' : ∀ k, IsModular QW (scale Q (Ls k)) (Hs k) := hHmod
    refine isometricLat_cancel_prod Q QW hLfg hKfg hHfg hH hHmod' (fun k => hgk k) (fun k => ?_) hiso
    have := hfund k
    simp only [fundNormGroup, fundSub] at this
    rw [hsc k] at this
    rw [this]; exact hgk k

end Adjoin

section Reductions

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

open Sat93 Adjoin28 NecI NecII RepTransfer Transfer28 SuffCancel SuffRed Nec93

/-- **Goodification, step (A1) for 93:29** (O'Meara 1963, p. 278, "by suitable hyperbolic adjunctions we can assume
$\dim L_i \ge 3$"; the adjoined lattice is $L \perp L$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to good lattices)"]
theorem suff29_adj_dims [FiniteDimensional F V] (h2 : IsTwoAdic R) {L K : Submodule R V} (hLfg : L.FG)
    (hKfg : K.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) {a : Fin t → F} (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (hC : Cond29 Q Ls Ks) :
    IsJordanSplitting (Q.prod (Q.prod Q)) (L.prod (L.prod L)) (fun k => (Ls k).prod ((Ls k).prod (Ls k))) ∧
    IsJordanSplitting (Q.prod (Q.prod Q)) (K.prod (L.prod L)) (fun k => (Ks k).prod ((Ls k).prod (Ls k))) ∧
    SameFundamentalInvariants (Q.prod (Q.prod Q)) (Q.prod (Q.prod Q)) (L.prod (L.prod L)) (K.prod (L.prod L))
      (fun k => (Ls k).prod ((Ls k).prod (Ls k))) (fun k => (Ks k).prod ((Ls k).prod (Ls k))) a ∧
    Cond29 (Q.prod (Q.prod Q)) (fun k => (Ls k).prod ((Ls k).prod (Ls k)))
      (fun k => (Ks k).prod ((Ls k).prod (Ls k))) ∧
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
  have hnL : ∀ k, normIdeal (Q.prod Q) ((Ls k).prod (Ls k)) ≤ normIdeal Q (Ls k) := fun k => by
    rw [normIdeal_prod, sup_idem]
  obtain ⟨h1, h2', h3, h4, h5⟩ :=
    suff29_adjoin_step Q (Q.prod Q) h2 hLfg hKfg hHfg hL hK hJH.split hHmod hg hgk hnL hS hC
  refine ⟨h1, h2', h3, h4, fun k => ?_, fun k => ?_, h5⟩
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

set_option maxHeartbeats 1000000 in
/-- **Goodification, step (A3) for 93:29** (O'Meara 1963, p. 278, "adjoining $L^{-1}$ we can assume that each $FL_i$ is
hyperbolic"): adjoin $L$ with the form $-Q$ to $L$ and to $K$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to good lattices)"]
theorem suff29_adj_hyp [FiniteDimensional F V] (h2 : IsTwoAdic R) {L K : Submodule R V} (hLfg : L.FG)
    (hKfg : K.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsSaturated Q L Ls) (hK : IsSaturated Q K Ks)
    {a : Fin t → F} (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond29 Q Ls Ks) :
    IsSaturated (Q.prod ((-1 : F) • Q)) (L.prod L) (fun k => (Ls k).prod (Ls k)) ∧
    IsSaturated (Q.prod ((-1 : F) • Q)) (K.prod L) (fun k => (Ks k).prod (Ls k)) ∧
    SameFundamentalInvariants (Q.prod ((-1 : F) • Q)) (Q.prod ((-1 : F) • Q)) (L.prod L) (K.prod L)
      (fun k => (Ls k).prod (Ls k)) (fun k => (Ks k).prod (Ls k)) a ∧
    Cond29 (Q.prod ((-1 : F) • Q)) (fun k => (Ls k).prod (Ls k)) (fun k => (Ks k).prod (Ls k)) ∧
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
  have hnG : ∀ k, normGroup Qn (Ls k) = normGroup Q (Ls k) := fun k => by rw [hQn, normGroup_neg_form]
  have hnL : ∀ k, normIdeal Qn (Ls k) ≤ normIdeal Q (Ls k) := fun k => by
    rw [normIdeal_eq_span_normGroup, normIdeal_eq_span_normGroup, hnG]
  obtain ⟨h1, h2', h3, h4, h5⟩ :=
    suff29_adjoin_step Q Qn h2 hLfg hKfg hLfg hL.1 hK.1 hLn.split hHmod hg hgk hnL hS hC
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
  refine ⟨⟨h1, fun k => ?_⟩, ⟨h2', fun k => ?_⟩, h3, h4, fun k => ?_, hsc, fun k => ?_, h5⟩
  · rw [hfL, normGroup_prod, hnG, sup_idem, hL.2 k]
  · rw [hfund', hfL, normGroup_prod, hnG, hK.2 k, hfund k, hL.2 k, sup_idem]
  · rw [(isJordanSplitting_prod Q Qn hLfg hLfg hL.1 hLn.split hHmod).2]; omega
  · set M := Ls k
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

end Reductions

section Engine

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The sufficiency of 93:29 for $t$ Jordan components** (O'Meara 1963, §93G, p. 277): lattices on a regular space over
a 2-adic field with Jordan splittings of the same fundamental invariants (`a`; over a 2-adic field these are equivalent to
the same Jordan invariants) satisfying conditions (i), (ii) are isometric. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to good lattices)"]
def Suff29 (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), IsTwoAdic R → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsJordanSplitting Q L Ls → IsJordanSplitting Q K Ks → SameFundamentalInvariants Q Q L K Ls Ks a →
      Cond29 Q Ls Ks → IsometricLat Q Q L K

/-- **The sufficiency of 93:29 for good lattices** (O'Meara 1963, p. 278, the situation after the reductions): saturated
splittings (automatic over a 2-adic field), all dimensions $\ge 3$, every $FL_k$ hyperbolic, $\mathfrak sL_1 = \mathfrak o$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to good lattices)"]
def GoodSuff29 (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), IsTwoAdic R → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond29 Q Ls Ks → IsometricLat Q Q L K

variable {R F}

open Sat93 Adjoin28 NecI NecII RepTransfer Transfer28 SuffCancel SuffRed SuffGood Nec93

set_option maxHeartbeats 1000000 in
/-- **Reduction to good lattices for 93:29** (O'Meara 1963, §93G, p. 278: "as in 93:28"): the sufficiency for good lattices
implies the sufficiency for all lattices with $t$ components (adjunctions $L \perp (L \perp L)$ and $L^{-1}$, then
scaling by a power of $2$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to good lattices)"]
theorem suff29_of_good {t : ℕ} (hG : GoodSuff29.{u, v} R F t) : Suff29.{u, v} R F t := by
  intro V _ _ _ _ _ Q h2 hQ L K _ _ Ls Ks a hL hK hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hπ := twoAdic_irreducible h2
  have h2p : ¬ IsUnit (2 : R) := hπ.not_isUnit
  -- (A1) all dimensions `≥ 3`
  obtain ⟨h1L, h1K, h1S, h1C, h1d, -, h1b⟩ := suff29_adj_dims Q h2 hLfg hKfg hL hK hS hC
  set Q1 := Q.prod (Q.prod Q) with hQ1
  have hQ1n : (QuadraticMap.associated Q1).Nondegenerate :=
    nondegenerate_prod Q (Q.prod Q) hQ (nondegenerate_prod Q Q hQ hQ)
  have hLL : (L.prod L).IsLattice F := isLattice_prod ‹_› ‹_›
  have hL1 : (L.prod (L.prod L)).IsLattice F := isLattice_prod ‹_› hLL
  have hK1 : (K.prod (L.prod L)).IsLattice F := isLattice_prod ‹_› hLL
  have hL1fg : (L.prod (L.prod L)).FG := Submodule.IsLattice.fg (A := F)
  have hK1fg : (K.prod (L.prod L)).FG := Submodule.IsLattice.fg (A := F)
  have hreg1L := isRegular_of_lattice_max Q1 hQ1n hL1
  have hreg1K := isRegular_of_lattice_max Q1 hQ1n hK1
  have hL1s := CoreTwoLast.isSaturated_of_twoAdic Q1 h2 hL1fg hreg1L h1L
  have hK1s := CoreTwoLast.isSaturated_of_twoAdic Q1 h2 hK1fg hreg1K h1K
  -- (A3) hyperbolic spaces
  obtain ⟨h3L, h3K, h3S, h3C, h3d, -, h3T, h3b⟩ := suff29_adj_hyp Q1 h2 hL1fg hK1fg hL1s hK1s h1S h1C
  set Q3 := Q1.prod ((-1 : F) • Q1) with hQ3
  have hQ3n : (QuadraticMap.associated Q3).Nondegenerate :=
    nondegenerate_prod Q1 _ hQ1n (nondegenerate_smul Q1 (by norm_num) hQ1n)
  set L2 := L.prod (L.prod L) with hL2def
  have hL3 : (L2.prod L2).IsLattice F := isLattice_prod ‹_› ‹_›
  set Ls3 := fun k => (Ls k).prod ((Ls k).prod (Ls k)) with hLs3
  have hK3 : ((K.prod (L.prod L)).prod L2).IsLattice F := isLattice_prod ‹_› ‹_›
  have hL3fg : (L2.prod L2).FG := Submodule.IsLattice.fg (A := F)
  -- scaling by `2^{-k}`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ∀ i : Fin t, (i : ℕ) = 0 → scale Q3 ((Ls3 i).prod (Ls3 i)) = R ∙ ((2 : F) ^ k) := by
    rcases t with _ | t
    · exact ⟨0, fun k => k.elim0⟩
    · have hk0 : ((Ls3 0).prod (Ls3 0)).FG :=
        FG.of_le hL3fg (h3L.1.split.iSup_eq ▸ le_iSup (fun k => (Ls3 k).prod (Ls3 k)) 0)
      obtain ⟨x, -, y, -, hxy⟩ := exists_scale_eq Q3 hk0
      have hne : scale Q3 ((Ls3 0).prod (Ls3 0)) ≠ ⊥ := (h3L.1.modular 0).2.1 ▸ (h3L.1.modular 0).1
      have hσ0 : bil Q3 x y ≠ 0 := fun h => hne (by rw [hxy, h, span_singleton_eq_bot])
      refine ⟨dord hπ (bil Q3 x y), fun i hi => ?_⟩
      rw [show i = 0 from Fin.ext hi, hxy]
      exact span_eq_of_dord_eq hπ hσ0 (two_zpow_ne_zero _) (by rw [dord_two_zpow h2])
  set α : F := (2 : F) ^ (-k) with hα
  have hα0 : α ≠ 0 := two_zpow_ne_zero _
  have hreg3 := isRegular_of_lattice_max Q3 hQ3n hL3
  have hrk3 : ∀ k, finrank R ((Ls3 k).prod (Ls3 k)) = finrank R ((((Ks k).prod ((Ls k).prod (Ls k)))).prod (Ls3 k)) :=
    fun k => by
      obtain ⟨⟨h0, hT⟩, -, -⟩ := h3S
      have := (hT k).1; rwa [show Fin.cast h0 k = k from Fin.ext (by simp)] at this
  have hrkc : ∀ i, finrank R (jordanChain (fun k => (Ls3 k).prod (Ls3 k)) i) =
      finrank R (jordanChain (fun k => (((Ks k).prod ((Ls k).prod (Ls k)))).prod (Ls3 k)) i) := fun i => by
    rw [(isJordanSplitting_jordanChain Q3 h3L.1 i).split.finrank_eq_sum (F := F),
      (isJordanSplitting_jordanChain Q3 h3K.1 i).split.finrank_eq_sum (F := F)]
    exact Finset.sum_congr rfl fun k _ => hrk3 _
  have hiso := hG (α • Q3) h2 (nondegenerate_smul Q3 hα0 hQ3n) (L2.prod L2) (((K.prod (L.prod L))).prod L2) _ _ (fun k => α * a k)
    ((isSaturated_smul_form_iff Q3 hα0).mpr h3L) ((isSaturated_smul_form_iff Q3 hα0).mpr h3K)
    (fun i => le_trans (h1d i) (h3d i))
    (fun i => by
      obtain ⟨T, hT0, hTs, hTd⟩ := h3T i
      exact ⟨T, fun x hx => by simp [hT0 x hx], hTs, hTd⟩)
    (fun i hi => by
      rw [scale_smul_form, hk i hi, Submodule.span_mul_span, Set.singleton_mul_singleton, hα,
        ← zpow_add₀ (two_ne_zero' F), neg_add_cancel, zpow_zero, ← Submodule.one_eq_span])
    (sameFund_smul Q3 hα0 h3S)
    (by
      have := cond29_smul Q3 h2 (-k) hrkc h3C
      exact this)
  exact h1b (h3b (isometricLat_of_smul Q3 hα0 hiso))

end Engine

end QuadFormsKB.OMeara.G29
