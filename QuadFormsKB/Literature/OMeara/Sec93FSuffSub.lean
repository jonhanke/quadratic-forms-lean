/-
# O'Meara 93:28, proof of the sufficiency: step 3, restriction to a subspace

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2\in F^\times$, a finite
dimensional quadratic space $(V,Q)$, and an $F$-subspace $W$ of $V$ with the restricted form $Q_W=Q\circ\iota$.

After Witt's theorem the lattices $L^*$ and $K^*$ of the proof (p. 273) both lie in the subspace
$W=(FL_1)^\perp$ and span it, so the induction hypothesis is applied on the space $(W,Q_W)$. For a lattice $X\le W$ put
$X_W=\iota^{-1}X\subseteq W$ (`subLatIn W X`). This file shows that everything the statement of 93:28 mentions is
unchanged by this transport:

* `toSub`: the isometry $X\cong X_W$; `subLatIn_eq_imgLat`: $J_W$ is the image of $J\le X$ under it, so the invariance lemmas of
  `Sec91Gap.lean` (`imgLat`) apply: scale, norm ideal, norm group, weight, rank, modularity, `subA`, Jordan splittings;
* `fundNormGroup_subLatIn`, `fundWeight_subLatIn`, `fIdeal_subLatIn`, `isSaturated_subLatIn`,
  `isFundNormGenerators_subLatIn`, `sameFundamentalInvariants_subLatIn`;
* `discQuot_subLatIn`, `spanRepresents_subLatIn`, `isometricLat_subLatIn`, `cond93_subLatIn`;
* `isLattice_subLatIn`: $X_W$ is a lattice on $W$ when $X$ is finitely generated and spans $W$;
* `nondegenerate_comp_of_isCompl`: $Q_W$ is nondegenerate when $W$ is a complement of a subspace orthogonal to it.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffStep
import QuadFormsKB.Literature.OMeara.Sec91Max

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.SuffSub

open QuadFormsKB.OMeara.NecMerge QuadFormsKB.OMeara.Transfer28 QuadFormsKB.OMeara.RepTransfer
  QuadFormsKB.OMeara.SuffStep QuadFormsKB.OMeara.Suff28

section Sub

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V) (W : Submodule F V)

/-- **The restriction $Q_W$ of $Q$ to a subspace.** -/
def QW : QuadraticForm F W := Q.comp W.subtype

/-- **A lattice of $V$ inside $W$, as a lattice on $W$:** $X_W=\{w\in W : w\in X\}$. -/
def subLatIn (X : Submodule R V) : Submodule R W := X.comap (W.subtype.restrictScalars R)

variable {W}

theorem mem_subLatIn {X : Submodule R V} {w : W} : w ∈ subLatIn W X ↔ (w : V) ∈ X := Iff.rfl

theorem subLatIn_mono {X Y : Submodule R V} (h : X ≤ Y) : subLatIn W X ≤ subLatIn W Y :=
  fun _ hw => h hw

variable {X : Submodule R V} (hX : X ≤ W.restrictScalars R)
include hX

/-- **The isometry $X\cong X_W$.** -/
def toSub : X ≃ₗ[R] subLatIn W X where
  toFun x := ⟨⟨x.1, hX x.2⟩, x.2⟩
  invFun y := ⟨(y.1 : V), y.2⟩
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)
  left_inv _ := rfl
  right_inv _ := rfl

theorem toSub_Q (x : X) : QW Q W ((toSub hX x : subLatIn W X) : W) = Q (x : V) := rfl

omit hX in
theorem subLatIn_le {J : Submodule R V} (hJ : J ≤ W.restrictScalars R) : J ≤ W.restrictScalars R := hJ

theorem subLatIn_eq_imgLat {J : Submodule R V} (hJ : J ≤ X) :
    subLatIn W J = imgLat (toSub hX) J := by
  ext y
  rw [mem_imgLat]
  constructor
  · intro hy
    exact ⟨⟨(y : V), hJ hy⟩, hy, Subtype.ext rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

theorem scale_subLatIn {J : Submodule R V} (hJ : J ≤ X) :
    scale (QW Q W) (subLatIn W J) = scale Q J := by
  rw [subLatIn_eq_imgLat hX hJ]; exact scale_imgLat Q (QW Q W) (toSub hX) (toSub_Q Q hX) hJ

theorem normIdeal_subLatIn {J : Submodule R V} (hJ : J ≤ X) :
    normIdeal (QW Q W) (subLatIn W J) = normIdeal Q J := by
  rw [subLatIn_eq_imgLat hX hJ]; exact normIdeal_imgLat Q (QW Q W) (toSub hX) (toSub_Q Q hX) hJ

theorem normGroup_subLatIn {J : Submodule R V} (hJ : J ≤ X) :
    normGroup (QW Q W) (subLatIn W J) = normGroup Q J := by
  rw [subLatIn_eq_imgLat hX hJ]; exact normGroup_imgLat Q (QW Q W) (toSub hX) (toSub_Q Q hX) hJ

theorem weight_subLatIn {J : Submodule R V} (hJ : J ≤ X) :
    weight (QW Q W) (subLatIn W J) = weight Q J := by
  rw [subLatIn_eq_imgLat hX hJ]; exact weight_imgLat Q (QW Q W) (toSub hX) (toSub_Q Q hX) hJ

theorem finrank_subLatIn {J : Submodule R V} (hJ : J ≤ X) :
    finrank R (subLatIn W J) = finrank R J := by
  rw [subLatIn_eq_imgLat hX hJ]; exact finrank_imgLat (toSub hX) hJ

theorem subA_subLatIn (a : Submodule R F) :
    subA (QW Q W) a (subLatIn W X) = subLatIn W (subA Q a X) := by
  have hle : subA Q a X ≤ X := fun x (hx : x ∈ subA Q a X) => hx.1
  rw [subLatIn_eq_imgLat hX hle]
  exact subA_imgLat Q (QW Q W) (toSub hX) (toSub_Q Q hX) a

omit hX in
theorem subLatIn_biSup {ι : Type*} (P : ι → Prop) (J : ι → Submodule R V)
    (hJ : ∀ k, J k ≤ W.restrictScalars R) :
    subLatIn W (⨆ k, ⨆ _ : P k, J k) = ⨆ k, ⨆ _ : P k, subLatIn W (J k) := by
  apply le_antisymm
  · intro y hy
    set S : Submodule R W := ⨆ k, ⨆ _ : P k, subLatIn W (J k) with hS
    have key : ∀ z, z ∈ (⨆ k, ⨆ _ : P k, J k : Submodule R V) → ∃ hz : z ∈ W, (⟨z, hz⟩ : W) ∈ S := by
      intro z hz
      refine Submodule.iSup_induction _ (motive := fun z => ∃ hz : z ∈ W, (⟨z, hz⟩ : W) ∈ S) hz
        (fun k z hz => ?_) ⟨zero_mem _, zero_mem _⟩
        (fun a b ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨add_mem ha hb, add_mem ha' hb'⟩)
      refine Submodule.iSup_induction _ (motive := fun z => ∃ hz : z ∈ W, (⟨z, hz⟩ : W) ∈ S) hz
        (fun hk z hz => ⟨hJ k hz, mem_iSup_of_mem k (mem_iSup_of_mem hk hz)⟩) ⟨zero_mem _, zero_mem _⟩
        (fun a b ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨add_mem ha hb, add_mem ha' hb'⟩)
    obtain ⟨hz, h⟩ := key (y : V) hy
    exact h
  · exact iSup_le fun k => iSup_le fun hk => subLatIn_mono (le_iSup₂_of_le k hk le_rfl)

variable {t : ℕ} {Ls : Fin t → Submodule R V} (hLs : ∀ i, Ls i ≤ X)

include hLs

theorem isJordanSplitting_subLatIn (hfg : X.FG) (hL : IsJordanSplitting Q X Ls) :
    IsJordanSplitting (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) := by
  have := isJordanSplitting_imgLat Q (QW Q W) (toSub hX) (toSub_Q Q hX) hfg hL
  have h2 : (fun i => subLatIn W (Ls i)) = fun i => imgLat (toSub hX) (Ls i) :=
    funext fun i => subLatIn_eq_imgLat hX (hLs i)
  rw [h2]; exact this

theorem jordanChain_subLatIn (i : Fin t) :
    subLatIn W (jordanChain Ls i) = jordanChain (fun j => subLatIn W (Ls j)) i :=
  subLatIn_biSup (fun j => j ≤ i) Ls fun k => (hLs k).trans hX

theorem scale_comp_subLatIn (i : Fin t) :
    scale (QW Q W) (subLatIn W (Ls i)) = scale Q (Ls i) := scale_subLatIn Q hX (hLs i)

theorem fundSub_subLatIn (i : Fin t) :
    fundSub (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) i = subLatIn W (fundSub Q X Ls i) := by
  unfold fundSub
  rw [scale_subLatIn Q hX (hLs i), subA_subLatIn Q hX]

theorem fundNormGroup_subLatIn (i : Fin t) :
    fundNormGroup (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) i = fundNormGroup Q X Ls i := by
  unfold fundNormGroup
  rw [fundSub_subLatIn Q hX hLs i]
  exact normGroup_subLatIn Q hX (fun x (hx : x ∈ fundSub Q X Ls i) => hx.1)

theorem fundNormIdeal_subLatIn (i : Fin t) :
    fundNormIdeal (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) i = fundNormIdeal Q X Ls i := by
  unfold fundNormIdeal
  rw [fundSub_subLatIn Q hX hLs i]
  exact normIdeal_subLatIn Q hX (fun x (hx : x ∈ fundSub Q X Ls i) => hx.1)

theorem fundWeight_subLatIn (i : Fin t) :
    fundWeight (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) i = fundWeight Q X Ls i := by
  unfold fundWeight
  rw [fundSub_subLatIn Q hX hLs i]
  exact weight_subLatIn Q hX (fun x (hx : x ∈ fundSub Q X Ls i) => hx.1)

theorem fIdeal_subLatIn (i j : Fin t) :
    fIdeal (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) i j = fIdeal Q X Ls i j := by
  unfold fIdeal
  rw [scale_subLatIn Q hX (hLs i), fundNormGroup_subLatIn Q hX hLs i, fundNormGroup_subLatIn Q hX hLs j,
    fundNormIdeal_subLatIn Q hX hLs i, fundNormIdeal_subLatIn Q hX hLs j]

theorem isFundNormGenerators_subLatIn (a : Fin t → F) :
    IsFundNormGenerators (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) a ↔
      IsFundNormGenerators Q X Ls a := by
  unfold IsFundNormGenerators IsNormGenerator
  refine forall_congr' fun i => ?_
  rw [fundSub_subLatIn Q hX hLs i,
    normGroup_subLatIn Q hX (fun x (hx : x ∈ fundSub Q X Ls i) => hx.1),
    normIdeal_subLatIn Q hX (fun x (hx : x ∈ fundSub Q X Ls i) => hx.1)]

theorem isSaturated_subLatIn (hfg : X.FG) (hS : IsSaturated Q X Ls) :
    IsSaturated (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i)) := by
  refine ⟨isJordanSplitting_subLatIn Q hX hLs hfg hS.1, fun i => ?_⟩
  rw [normGroup_subLatIn Q hX (hLs i), fundNormGroup_subLatIn Q hX hLs i]
  exact hS.2 i

end Sub

/-! ### The general transport along an injective isometry -/

section Map

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V') (φ : V' →ₗ[F] V)

/-- **The image of a lattice under an injective $F$-linear map** $\varphi : V'\to V$ (`latMap` when $V'=V$). -/
abbrev mapLat (X' : Submodule R V') : Submodule R V := X'.map (φ.restrictScalars R)

variable {φ}
variable (hinj : Function.Injective φ) (hφ : ∀ x, Q (φ x) = Q' x)

/-- The isometry $J\cong\varphi J$ of lattices. -/
def isoMap (J : Submodule R V') : J ≃ₗ[R] mapLat φ J :=
  Submodule.equivMapOfInjective (φ.restrictScalars R) hinj J

include hφ in
theorem isoMap_Q (J : Submodule R V') (x : J) :
    Q ((isoMap hinj J x : mapLat φ J) : V) = Q' (x : V') := by
  exact hφ (x : V')

theorem imgLat_isoMap (X' : Submodule R V') {J : Submodule R V'} (hJ : J ≤ X') :
    imgLat (isoMap hinj X') J = mapLat φ J := by
  ext y
  rw [mem_imgLat]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : V'), hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hJ ha⟩, ha, rfl⟩

variable {X' : Submodule R V'}

include hinj hφ in
theorem isometricLat_map (J : Submodule R V') : IsometricLat Q' Q J (mapLat φ J) :=
  ⟨isoMap hinj J, isoMap_Q Q Q' hinj hφ J⟩

include hinj hφ in
theorem scale_map {J : Submodule R V'} (hJ : J ≤ X') : scale Q (mapLat φ J) = scale Q' J := by
  rw [← imgLat_isoMap hinj X' hJ]; exact scale_imgLat Q' Q (isoMap hinj X') (isoMap_Q Q Q' hinj hφ X') hJ

include hinj hφ in
theorem normIdeal_map {J : Submodule R V'} (hJ : J ≤ X') : normIdeal Q (mapLat φ J) = normIdeal Q' J := by
  rw [← imgLat_isoMap hinj X' hJ]
  exact normIdeal_imgLat Q' Q (isoMap hinj X') (isoMap_Q Q Q' hinj hφ X') hJ

include hinj hφ in
theorem normGroup_map {J : Submodule R V'} (hJ : J ≤ X') : normGroup Q (mapLat φ J) = normGroup Q' J := by
  rw [← imgLat_isoMap hinj X' hJ]
  exact normGroup_imgLat Q' Q (isoMap hinj X') (isoMap_Q Q Q' hinj hφ X') hJ

include hinj hφ in
theorem weight_map {J : Submodule R V'} (hJ : J ≤ X') : weight Q (mapLat φ J) = weight Q' J := by
  rw [← imgLat_isoMap hinj X' hJ]
  exact weight_imgLat Q' Q (isoMap hinj X') (isoMap_Q Q Q' hinj hφ X') hJ

include hinj hφ in
theorem finrank_map {J : Submodule R V'} (hJ : J ≤ X') : finrank R (mapLat φ J) = finrank R J := by
  rw [← imgLat_isoMap hinj X' hJ]; exact finrank_imgLat (isoMap hinj X') hJ

include hinj hφ in
theorem subA_map (a : Submodule R F) : subA Q a (mapLat φ X') = mapLat φ (subA Q' a X') := by
  have hle : subA Q' a X' ≤ X' := fun x (hx : x ∈ subA Q' a X') => hx.1
  rw [← imgLat_isoMap hinj X' hle]
  exact subA_imgLat Q' Q (isoMap hinj X') (isoMap_Q Q Q' hinj hφ X') a

include hinj hφ in
theorem isJordanSplitting_map {t : ℕ} {Ls : Fin t → Submodule R V'} (hfg : X'.FG)
    (hL : IsJordanSplitting Q' X' Ls) : IsJordanSplitting Q (mapLat φ X') (fun i => mapLat φ (Ls i)) := by
  have hle : ∀ i, Ls i ≤ X' := fun i => hL.split.iSup_eq ▸ le_iSup Ls i
  have := isJordanSplitting_imgLat Q' Q (isoMap hinj X') (isoMap_Q Q Q' hinj hφ X') hfg hL
  have h1 : imgLat (isoMap hinj X') X' = mapLat φ X' := imgLat_isoMap hinj X' le_rfl
  have h2 : (fun i => mapLat φ (Ls i)) = fun i => imgLat (isoMap hinj X') (Ls i) :=
    funext fun i => (imgLat_isoMap hinj X' (hle i)).symm
  rw [h2]
  exact this

theorem jordanChain_map {t : ℕ} (Ls : Fin t → Submodule R V') (i : Fin t) :
    mapLat φ (jordanChain Ls i) = jordanChain (fun j => mapLat φ (Ls j)) i := by
  unfold jordanChain
  simp only [Submodule.map_iSup]

variable {t : ℕ} {Ls : Fin t → Submodule R V'} (hLs : ∀ i, Ls i ≤ X')

include hinj hφ hLs in
theorem fundSub_map (i : Fin t) :
    fundSub Q (mapLat φ X') (fun i => mapLat φ (Ls i)) i = mapLat φ (fundSub Q' X' Ls i) := by
  unfold fundSub
  rw [scale_map Q Q' hinj hφ (hLs i), subA_map Q Q' hinj hφ]

include hinj hφ hLs in
theorem fundNormGroup_map (i : Fin t) :
    fundNormGroup Q (mapLat φ X') (fun i => mapLat φ (Ls i)) i = fundNormGroup Q' X' Ls i := by
  unfold fundNormGroup
  rw [fundSub_map Q Q' hinj hφ hLs i]
  exact normGroup_map Q Q' hinj hφ (fun x (hx : x ∈ fundSub Q' X' Ls i) => hx.1)

include hinj hφ hLs in
theorem fundNormIdeal_map (i : Fin t) :
    fundNormIdeal Q (mapLat φ X') (fun i => mapLat φ (Ls i)) i = fundNormIdeal Q' X' Ls i := by
  unfold fundNormIdeal
  rw [fundSub_map Q Q' hinj hφ hLs i]
  exact normIdeal_map Q Q' hinj hφ (fun x (hx : x ∈ fundSub Q' X' Ls i) => hx.1)

include hinj hφ hLs in
theorem fundWeight_map (i : Fin t) :
    fundWeight Q (mapLat φ X') (fun i => mapLat φ (Ls i)) i = fundWeight Q' X' Ls i := by
  unfold fundWeight
  rw [fundSub_map Q Q' hinj hφ hLs i]
  exact weight_map Q Q' hinj hφ (fun x (hx : x ∈ fundSub Q' X' Ls i) => hx.1)

include hinj hφ hLs in
theorem fIdeal_map (i j : Fin t) :
    fIdeal Q (mapLat φ X') (fun i => mapLat φ (Ls i)) i j = fIdeal Q' X' Ls i j := by
  unfold fIdeal
  rw [scale_map Q Q' hinj hφ (hLs i), fundNormGroup_map Q Q' hinj hφ hLs i, fundNormGroup_map Q Q' hinj hφ hLs j,
    fundNormIdeal_map Q Q' hinj hφ hLs i, fundNormIdeal_map Q Q' hinj hφ hLs j]

include hinj hφ hLs in
theorem isFundNormGenerators_map (a : Fin t → F) :
    IsFundNormGenerators Q (mapLat φ X') (fun i => mapLat φ (Ls i)) a ↔ IsFundNormGenerators Q' X' Ls a := by
  unfold IsFundNormGenerators IsNormGenerator
  refine forall_congr' fun i => ?_
  rw [fundSub_map Q Q' hinj hφ hLs i,
    normGroup_map Q Q' hinj hφ (fun x (hx : x ∈ fundSub Q' X' Ls i) => hx.1),
    normIdeal_map Q Q' hinj hφ (fun x (hx : x ∈ fundSub Q' X' Ls i) => hx.1)]

include hinj hφ hLs in
theorem isSaturated_map (hfg : X'.FG) (hS : IsSaturated Q' X' Ls) :
    IsSaturated Q (mapLat φ X') (fun i => mapLat φ (Ls i)) := by
  refine ⟨isJordanSplitting_map Q Q' hinj hφ hfg hS.1, fun i => ?_⟩
  rw [normGroup_map Q Q' hinj hφ (hLs i), fundNormGroup_map Q Q' hinj hφ hLs i]
  exact hS.2 i

/-! #### Pairs of lattices -/

include hinj hφ in
theorem discQuot_map {M N : Submodule R V'} (a : Submodule R F) :
    DiscQuotSqEquivMod Q (mapLat φ M) (mapLat φ N) a ↔ DiscQuotSqEquivMod Q' M N a := by
  have hM := isometricLat_map Q Q' hinj hφ M
  have hN := isometricLat_map Q Q' hinj hφ N
  exact ⟨fun h => discQuot_of_isometricLat Q Q' (QuadFormsKB.OMeara.adj_isometricLat_symm _ _ hM)
      (QuadFormsKB.OMeara.adj_isometricLat_symm _ _ hN) h,
    fun h => discQuot_of_isometricLat Q' Q hM hN h⟩

include hinj hφ in
theorem spanRepresents_map {M N : Submodule R V'} (hM : M.FG) (hN : N.FG) (c : F) :
    SpanRepresents Q (mapLat φ M) (mapLat φ N) c ↔ SpanRepresents Q' M N c :=
  (spanRepresents_iff_of_isometricLat Q' Q hM hN (isometricLat_map Q Q' hinj hφ M)
    (isometricLat_map Q Q' hinj hφ N) c).symm

include hinj hφ in
theorem isometricLat_map_iff {M N : Submodule R V'} :
    IsometricLat Q Q (mapLat φ M) (mapLat φ N) ↔ IsometricLat Q' Q' M N := by
  have hM := isometricLat_map Q Q' hinj hφ M
  have hN := isometricLat_map Q Q' hinj hφ N
  constructor
  · intro h
    exact QuadFormsKB.OMeara.adj_isometricLat_trans Q' Q Q' (QuadFormsKB.OMeara.adj_isometricLat_trans Q' Q Q hM h)
      (QuadFormsKB.OMeara.adj_isometricLat_symm _ _ hN)
  · intro h
    exact QuadFormsKB.OMeara.adj_isometricLat_trans Q Q' Q (QuadFormsKB.OMeara.adj_isometricLat_symm _ _ hM)
      (QuadFormsKB.OMeara.adj_isometricLat_trans Q' Q' Q h hN)

variable {Y' : Submodule R V'} {Ks : Fin t → Submodule R V'} (hKs : ∀ i, Ks i ≤ Y')

include hinj hφ hLs hKs in
theorem sameFundamentalInvariants_map (a : Fin t → F) :
    SameFundamentalInvariants Q Q (mapLat φ X') (mapLat φ Y') (fun i => mapLat φ (Ls i))
        (fun i => mapLat φ (Ks i)) a ↔
      SameFundamentalInvariants Q' Q' X' Y' Ls Ks a := by
  unfold SameFundamentalInvariants SameFundamentalType
  simp only [finrank_map Q Q' hinj hφ (hLs _), finrank_map Q Q' hinj hφ (hKs _),
    scale_map Q Q' hinj hφ (hLs _), scale_map Q Q' hinj hφ (hKs _), fundNormGroup_map Q Q' hinj hφ hLs,
    fundNormGroup_map Q Q' hinj hφ hKs, isFundNormGenerators_map Q Q' hinj hφ hLs,
    isFundNormGenerators_map Q Q' hinj hφ hKs]

include hinj hφ hLs hKs in
theorem cond93_map (hXfg : X'.FG) (hYfg : Y'.FG) (a : Fin t → F) :
    Cond93 Q (mapLat φ X') (fun i => mapLat φ (Ls i)) (fun i => mapLat φ (Ks i)) a ↔
      Cond93 Q' X' Ls Ks a := by
  have hcL : ∀ i, jordanChain Ls i ≤ X' := fun i => iSup₂_le fun j _ => hLs j
  have hcK : ∀ i, jordanChain Ks i ≤ Y' := fun i => iSup₂_le fun j _ => hKs j
  unfold Cond93
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => ?_
  rw [← jordanChain_map Ls i, ← jordanChain_map Ks i, fIdeal_map Q Q' hinj hφ hLs i j,
    fundWeight_map Q Q' hinj hφ hLs j, fundWeight_map Q Q' hinj hφ hLs i]
  refine and_congr (discQuot_map Q Q' hinj hφ _) (and_congr (imp_congr_right fun _ => ?_)
    (imp_congr_right fun _ => ?_))
  · exact spanRepresents_map Q Q' hinj hφ (Submodule.FG.of_le hXfg (hcL i)) (Submodule.FG.of_le hYfg (hcK i)) _
  · exact spanRepresents_map Q Q' hinj hφ (Submodule.FG.of_le hXfg (hcL i)) (Submodule.FG.of_le hYfg (hcK i)) _

end Map

/-! ### Specialization (a): the inclusion of a subspace -/

section Subspace

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V) {W : Submodule F V}

theorem map_subLatIn {X : Submodule R V} (hX : X ≤ W.restrictScalars R) :
    mapLat W.subtype (subLatIn W X) = X := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hy; exact ⟨⟨y, hX hy⟩, hy, rfl⟩

theorem fg_subLatIn {X : Submodule R V} (hX : X ≤ W.restrictScalars R) (hfg : X.FG) : (subLatIn W X).FG := by
  have : Module.Finite R X := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.iff_fg.mp (Module.Finite.equiv (toSub hX))

/-- **$X_W$ is a lattice on $W$** when $X$ is finitely generated and spans $W$. -/
theorem isLattice_subLatIn {X : Submodule R V} (hX : X ≤ W.restrictScalars R) (hfg : X.FG)
    (hspan : span F (X : Set V) = W) : (subLatIn W X).IsLattice F := by
  refine ⟨fg_subLatIn hX hfg, ?_⟩
  apply Submodule.map_injective_of_injective W.injective_subtype
  have himg : W.subtype '' ((subLatIn W X : Submodule R W) : Set W) = (X : Set V) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hy; exact ⟨⟨y, hX hy⟩, hy, rfl⟩
  rw [Submodule.map_span, himg, hspan, Submodule.map_top, Submodule.range_subtype]

variable {t : ℕ} {Ls Ks : Fin t → Submodule R V} {X Y : Submodule R V}

/-- **Cond93 on the subspace:** for lattices $X, Y\le W$ with splittings, conditions (i)–(iii) hold on $V$ iff they hold on
$(W,Q_W)$ for the transported lattices and splittings. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (conditions (i)-(iii) on the subspace)"]
theorem cond93_subLatIn (hX : X ≤ W.restrictScalars R) (hY : Y ≤ W.restrictScalars R)
    (hLs : ∀ i, Ls i ≤ X) (hKs : ∀ i, Ks i ≤ Y) (hXfg : X.FG) (hYfg : Y.FG) (a : Fin t → F) :
    Cond93 Q X Ls Ks a ↔ Cond93 (QW Q W) (subLatIn W X) (fun i => subLatIn W (Ls i))
      (fun i => subLatIn W (Ks i)) a := by
  have h := cond93_map Q (QW Q W) (φ := W.subtype) W.injective_subtype (fun x => rfl) (X' := subLatIn W X)
    (Ls := fun i => subLatIn W (Ls i)) (Y' := subLatIn W Y) (Ks := fun i => subLatIn W (Ks i))
    (fun i => subLatIn_mono (hLs i)) (fun i => subLatIn_mono (hKs i)) (fg_subLatIn hX hXfg)
    (fg_subLatIn hY hYfg) a
  have e1 : (fun i => mapLat W.subtype (subLatIn W (Ls i))) = Ls :=
    funext fun i => map_subLatIn ((hLs i).trans hX)
  have e2 : (fun i => mapLat W.subtype (subLatIn W (Ks i))) = Ks :=
    funext fun i => map_subLatIn ((hKs i).trans hY)
  rw [e1, e2, map_subLatIn hX] at h
  exact h

/-- **The same fundamental invariants on the subspace.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (fundamental invariants on the subspace)"]
theorem sameFundamentalInvariants_subLatIn (hX : X ≤ W.restrictScalars R) (hY : Y ≤ W.restrictScalars R)
    (hLs : ∀ i, Ls i ≤ X) (hKs : ∀ i, Ks i ≤ Y) (a : Fin t → F) :
    SameFundamentalInvariants Q Q X Y Ls Ks a ↔ SameFundamentalInvariants (QW Q W) (QW Q W) (subLatIn W X)
      (subLatIn W Y) (fun i => subLatIn W (Ls i)) (fun i => subLatIn W (Ks i)) a := by
  have h := sameFundamentalInvariants_map Q (QW Q W) (φ := W.subtype) W.injective_subtype (fun x => rfl)
    (X' := subLatIn W X) (Ls := fun i => subLatIn W (Ls i)) (Y' := subLatIn W Y)
    (Ks := fun i => subLatIn W (Ks i)) (fun i => subLatIn_mono (hLs i)) (fun i => subLatIn_mono (hKs i)) a
  have e1 : (fun i => mapLat W.subtype (subLatIn W (Ls i))) = Ls :=
    funext fun i => map_subLatIn ((hLs i).trans hX)
  have e2 : (fun i => mapLat W.subtype (subLatIn W (Ks i))) = Ks :=
    funext fun i => map_subLatIn ((hKs i).trans hY)
  rw [e1, e2, map_subLatIn hX, map_subLatIn hY] at h
  exact h

/-- **Isometry of lattices on the subspace and on $V$ agree.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (isometry of lattices on the subspace)"]
theorem isometricLat_subLatIn (hX : X ≤ W.restrictScalars R) (hY : Y ≤ W.restrictScalars R) :
    IsometricLat Q Q X Y ↔ IsometricLat (QW Q W) (QW Q W) (subLatIn W X) (subLatIn W Y) := by
  have h := isometricLat_map_iff Q (QW Q W) (φ := W.subtype) W.injective_subtype (fun x => rfl)
    (M := subLatIn W X) (N := subLatIn W Y)
  rw [map_subLatIn hX, map_subLatIn hY] at h
  exact h

/-- **The restricted form is nondegenerate on a complement of an orthogonal subspace** (e.g. $W=(FA)^\perp$ for a regular
$A$ in a nondegenerate $V$, where $FA\oplus W=V$): if $Q$ is nondegenerate on $V$, $U\sqcup W=V$ and $W\perp U$, then
$Q_W$ is nondegenerate. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (the orthogonal complement is regular)"]
theorem nondegenerate_QW (hQ : (QuadraticMap.associated Q).Nondegenerate) {U : Submodule F V}
    (hsup : U ⊔ W = ⊤) (horth : ∀ w ∈ W, ∀ u ∈ U, QuadraticMap.associated Q w u = 0) :
    (QuadraticMap.associated (QW Q W)).Nondegenerate := by
  have hrefl : (QuadraticMap.associated (QW Q W)).IsRefl :=
    fun x y h => (QuadraticMap.associated_isSymm F (QW Q W) y x).trans h
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl]
  intro w hw
  have hall : ∀ v : V, QuadraticMap.associated Q (w : V) v = 0 := by
    intro v
    have hv : v ∈ U ⊔ W := by rw [hsup]; trivial
    obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, horth w w.2 u hu, zero_add]
    exact hw ⟨w', hw'⟩
  exact Subtype.ext (hQ.1 _ hall)

end Subspace

/-! ### Specialization (b): an orthogonal transformation of $V$ -/

section Latmap

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q)
variable {t : ℕ} {Ls Ks : Fin t → Submodule R V} {X Y : Submodule R V}

include hσ in
theorem latMap_hφ (x : V) : Q ((σ : V →ₗ[F] V) x) = Q x := hσ x

include hσ in
/-- **Moving a Jordan splitting by $\sigma\in O(V)$.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (σ K_i)"]
theorem isJordanSplitting_latMap (hfg : X.FG) (hL : IsJordanSplitting Q X Ls) :
    IsJordanSplitting Q (latMap σ X) (fun i => latMap σ (Ls i)) :=
  isJordanSplitting_map Q Q (φ := (σ : V →ₗ[F] V)) σ.injective (latMap_hφ Q hσ) hfg hL

include hσ in
theorem sameFundamentalInvariants_latMap (hLs : ∀ i, Ls i ≤ X) (hKs : ∀ i, Ks i ≤ Y) (a : Fin t → F) :
    SameFundamentalInvariants Q Q (latMap σ X) (latMap σ Y) (fun i => latMap σ (Ls i))
        (fun i => latMap σ (Ks i)) a ↔ SameFundamentalInvariants Q Q X Y Ls Ks a :=
  sameFundamentalInvariants_map Q Q (φ := (σ : V →ₗ[F] V)) σ.injective (latMap_hφ Q hσ) hLs hKs a

include hσ in
theorem cond93_latMap (hLs : ∀ i, Ls i ≤ X) (hKs : ∀ i, Ks i ≤ Y) (hXfg : X.FG) (hYfg : Y.FG)
    (a : Fin t → F) :
    Cond93 Q (latMap σ X) (fun i => latMap σ (Ls i)) (fun i => latMap σ (Ks i)) a ↔ Cond93 Q X Ls Ks a :=
  cond93_map Q Q (φ := (σ : V →ₗ[F] V)) σ.injective (latMap_hφ Q hσ) hLs hKs hXfg hYfg a

include hσ in
theorem isometricLat_latMap {M N : Submodule R V} :
    IsometricLat Q Q (latMap σ M) (latMap σ N) ↔ IsometricLat Q Q M N :=
  isometricLat_map_iff Q Q (φ := (σ : V →ₗ[F] V)) σ.injective (latMap_hφ Q hσ)

include hσ in
theorem isSaturated_latMap (hLs : ∀ i, Ls i ≤ X) (hfg : X.FG) (hS : IsSaturated Q X Ls) :
    IsSaturated Q (latMap σ X) (fun i => latMap σ (Ls i)) :=
  isSaturated_map Q Q (φ := (σ : V →ₗ[F] V)) σ.injective (latMap_hφ Q hσ) hLs hfg hS

theorem jordanChain_latMap (i : Fin t) :
    latMap σ (jordanChain Ls i) = jordanChain (fun j => latMap σ (Ls j)) i :=
  jordanChain_map (φ := (σ : V →ₗ[F] V)) Ls i

/-- **A lattice moved by $\sigma\in O(V)$ is a lattice.** -/
theorem isLattice_latMap {X : Submodule R V} [X.IsLattice F] : (latMap σ X).IsLattice F := by
  refine ⟨?_, ?_⟩
  · exact Submodule.FG.map _ Submodule.IsLattice.fg
  · rw [span_latMap, Submodule.IsLattice.span_eq_top (A := F) (M := X), Submodule.map_top]
    exact LinearMap.range_eq_top.mpr σ.surjective

end Latmap

end QuadFormsKB.OMeara.SuffSub
