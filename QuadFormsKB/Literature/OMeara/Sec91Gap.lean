/-
# O'Meara §91C: gaps in the formalization of Jordan types (pp. 244-246)

**Setting** (as in `Sec91Type.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, quadratic
spaces $(V, Q)$, $(V', Q')$ over $F$, $B$ = `bil Q`, lattices = `Submodule R V`. Indices are $0$-based.

**Proves**
* `imgLat` and `isJordanSplitting_imgLat`, `exists_jordanSplitting_of_isometricLat` (§91C, p. 245; §93E, p. 264):
  an isometry $L \to K$ transports a Jordan splitting of $L$ to one of $K$ of the same Jordan type, and preserves
  the fundamental invariants ($\mathfrak g_i$, $\mathfrak w_i$, the norm generators $a_i$);
* `SameJordanType.symm`, `SameJordanType.trans`, `HasSameJordanType` and its characterization
  `hasSameJordanType_iff` (§91C, p. 245), `HasSameJordanType.symm`, `.trans`;
* `IsometricLat.hasSameJordanType` (§91C, p. 245): isometric lattices are of the same Jordan type;
* `exists_isJordanSplitting_subA` (§91C, p. 244): a modular component is the first component of a Jordan splitting
  of $L^{\mathfrak a}$;
* `hasSameJordanType_jordanChain`, `hasSameJordanType_invJordanChain` (91:11): chains of lattices of the same type
  are of the same type; `volume_invJordanChain_eq`, `exists_unit_det_invJordanChain` (91:11 for inverse chains);
* `eq_splitComp_jordanChain`, `eq_of_jordanChain_eq` (§91C, p. 246): a Jordan chain determines the Jordan splitting.
-/
import QuadFormsKB.Literature.OMeara.Sec93E
import QuadFormsKB.Literature.OMeara.Sec91Chain
import QuadFormsKB.Literature.OMeara.Sec82Isom

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Transport

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Image of a sublattice under an isometry** $f : L \to K$ of lattices: for $J \subseteq V$ the sublattice
$f(J \cap L) \subseteq K \subseteq V'$. -/
def imgLat {L : Submodule R V} {K : Submodule R V'} (f : L ≃ₗ[R] K) (J : Submodule R V) : Submodule R V' :=
  (J.comap L.subtype).map (K.subtype ∘ₗ f.toLinearMap)

theorem mem_imgLat {L : Submodule R V} {K : Submodule R V'} (f : L ≃ₗ[R] K) {J : Submodule R V} {y : V'} :
    y ∈ imgLat f J ↔ ∃ x : L, (x : V) ∈ J ∧ (f x : V') = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem imgLat_le {L : Submodule R V} {K : Submodule R V'} (f : L ≃ₗ[R] K) (J : Submodule R V) :
    imgLat f J ≤ K := by
  rintro y hy
  obtain ⟨x, -, rfl⟩ := (mem_imgLat f).mp hy
  exact (f x).2

theorem imgLat_top {L : Submodule R V} {K : Submodule R V'} (f : L ≃ₗ[R] K) : imgLat f L = K := by
  apply le_antisymm (imgLat_le f L)
  intro y hy
  exact (mem_imgLat f).mpr ⟨f.symm ⟨y, hy⟩, (f.symm ⟨y, hy⟩).2, by simp⟩

variable {L : Submodule R V} {K : Submodule R V'} (f : L ≃ₗ[R] K) (hf : ∀ x : L, Q' (f x : V') = Q (x : V))
include hf

theorem scale_imgLat {J : Submodule R V} (hJL : J ≤ L) : scale Q' (imgLat f J) = scale Q J := by
  apply le_antisymm
  · rw [scale, span_le]
    rintro _ ⟨y, hy, z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_imgLat f).mp hy
    obtain ⟨x', hx', rfl⟩ := (mem_imgLat f).mp hz
    rw [bil_eq_of_isometricLat Q Q' f hf]
    exact bil_mem_scale Q hx hx'
  · rw [scale, span_le]
    rintro _ ⟨x, hx, z, hz, rfl⟩
    rw [← bil_eq_of_isometricLat Q Q' f hf ⟨x, hJL hx⟩ ⟨z, hJL hz⟩]
    exact bil_mem_scale Q' ((mem_imgLat f).mpr ⟨⟨x, hJL hx⟩, hx, rfl⟩)
      ((mem_imgLat f).mpr ⟨⟨z, hJL hz⟩, hz, rfl⟩)

theorem normIdeal_imgLat {J : Submodule R V} (hJL : J ≤ L) :
    normIdeal Q' (imgLat f J) = normIdeal Q J := by
  apply le_antisymm
  · rw [normIdeal, span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_imgLat f).mp hy
    rw [hf]
    exact Q_mem_normIdeal Q hx
  · rw [normIdeal, span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hf ⟨x, hJL hx⟩]
    exact Q_mem_normIdeal Q' ((mem_imgLat f).mpr ⟨⟨x, hJL hx⟩, hx, rfl⟩)

theorem normGroup_imgLat {J : Submodule R V} (hJL : J ≤ L) :
    normGroup Q' (imgLat f J) = normGroup Q J := by
  ext z
  constructor
  · rintro ⟨y, hy, c, hc, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_imgLat f).mp hy
    rw [scale_imgLat Q Q' f hf hJL] at hc
    exact ⟨x, hx, c, hc, by rw [hf]⟩
  · rintro ⟨x, hx, c, hc, rfl⟩
    refine ⟨f ⟨x, hJL hx⟩, (mem_imgLat f).mpr ⟨_, hx, rfl⟩, c, ?_, by rw [hf]⟩
    rwa [scale_imgLat Q Q' f hf hJL]

theorem weight_imgLat {J : Submodule R V} (hJL : J ≤ L) : weight Q' (imgLat f J) = weight Q J := by
  have h : normGroupIdeal Q' (imgLat f J) = normGroupIdeal Q J := by
    ext z
    show (∀ r : R, r • z ∈ normGroup Q' (imgLat f J)) ↔ ∀ r : R, r • z ∈ normGroup Q J
    simp only [normGroup_imgLat Q Q' f hf hJL]
  unfold weight
  rw [h, scale_imgLat Q Q' f hf hJL]

omit hf in
theorem finrank_imgLat {J : Submodule R V} (hJL : J ≤ L) : finrank R (imgLat f J) = finrank R J := by
  have hinj : Function.Injective (K.subtype ∘ₗ f.toLinearMap) := fun a b h => f.injective (Subtype.ext h)
  exact ((equivMapOfInjective _ hinj (J.comap L.subtype)).symm.trans (comapSubtypeEquivOfLe hJL)).finrank_eq

theorem volume_imgLat {J : Submodule R V} (hJL : J ≤ L) : volume Q' (imgLat f J) = volume Q J := by
  unfold volume
  rw [finrank_imgLat f hJL]
  congr 1
  ext d
  constructor
  · rintro ⟨x, hx, rfl⟩
    choose z hz hzf using fun i => (mem_imgLat f).mp (hx i)
    refine ⟨fun i => (z i : V), hz, ?_⟩
    congr 1
    ext i j
    simp only [gram, Matrix.of_apply]
    rw [← hzf i, ← hzf j, bil_eq_of_isometricLat Q Q' f hf]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun i => (f ⟨x i, hJL (hx i)⟩ : V'), fun i => (mem_imgLat f).mpr ⟨_, hx i, rfl⟩, ?_⟩
    congr 1
    ext i j
    simp only [gram, Matrix.of_apply]
    rw [bil_eq_of_isometricLat Q Q' f hf]

theorem isModular_imgLat {J : Submodule R V} (hJL : J ≤ L) (a : Submodule R F) :
    IsModular Q' a (imgLat f J) ↔ IsModular Q a J := by
  simp only [IsModular, scale_imgLat Q Q' f hf hJL, volume_imgLat Q Q' f hf hJL, finrank_imgLat f hJL]

theorem subA_imgLat (a : Submodule R F) : subA Q' a K = imgLat f (subA Q a L) := by
  ext y
  constructor
  · rintro ⟨hyK, hy⟩
    have hyK' : y ∈ imgLat f L := by rw [imgLat_top]; exact hyK
    obtain ⟨x, hx, rfl⟩ := (mem_imgLat f).mp hyK'
    refine (mem_imgLat f).mpr ⟨x, ⟨hx, fun z hz => ?_⟩, rfl⟩
    have := hy (f ⟨z, hz⟩) (f ⟨z, hz⟩).2
    rwa [bil_eq_of_isometricLat Q Q' f hf] at this
  · intro hy
    obtain ⟨x, ⟨hxL, hx⟩, rfl⟩ := (mem_imgLat f).mp hy
    refine ⟨(f x).2, fun w hw => ?_⟩
    have hw' : w ∈ imgLat f L := by rw [imgLat_top]; exact hw
    obtain ⟨x', hx', rfl⟩ := (mem_imgLat f).mp hw'
    rw [bil_eq_of_isometricLat Q Q' f hf]
    exact hx _ hx'

theorem isJordanSplitting_imgLat (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) : IsJordanSplitting Q' K (fun i => imgLat f (Ls i)) := by
  have hle : ∀ i, Ls i ≤ L := fun i => hL.split.iSup_eq ▸ le_iSup Ls i
  have hKfg : K.FG := by
    have : Module.Finite R L := Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.iff_fg.mp (Module.Finite.equiv f)
  have horth : ∀ i j, i ≠ j → ∀ x ∈ imgLat f (Ls i), ∀ y ∈ imgLat f (Ls j), bil Q' x y = 0 := by
    intro i j hij x₀ hx₀ y₀ hy₀
    obtain ⟨x, hx, rfl⟩ := (mem_imgLat f).mp hx₀
    obtain ⟨y, hy, rfl⟩ := (mem_imgLat f).mp hy₀
    rw [bil_eq_of_isometricLat Q Q' f hf]
    exact hL.split.orth i j hij _ hx _ hy
  have hmod : ∀ i, IsModular Q' (scale Q' (imgLat f (Ls i))) (imgLat f (Ls i)) := by
    intro i
    rw [scale_imgLat Q Q' f hf (hle i)]
    exact (isModular_imgLat Q Q' f hf (hle i) _).mpr (hL.modular i)
  refine ⟨⟨horth, ?_, ?_⟩, hmod, ?_⟩
  · exact iSupIndep_of_orth Q' horth fun i =>
      (hmod i).isRegular Q' (FG.of_le hKfg (imgLat_le f _))
  · apply le_antisymm (iSup_le fun i => imgLat_le f _)
    refine (imgLat_top f).symm.le.trans ?_
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_imgLat f).mp hy
    have hx2 : (x : V) ∈ ⨆ i, Ls i := hL.split.iSup_eq ▸ hx
    obtain ⟨μ, hμ⟩ := (mem_iSup_fin_iff (Ls) (x : V)).mp hx2
    have hx' : x = ∑ i, (⟨(μ i : V), hle i (μ i).2⟩ : L) :=
      Subtype.ext (by rw [Submodule.coe_sum]; exact hμ.symm)
    rw [hx', map_sum, Submodule.coe_sum]
    exact sum_mem fun i _ => mem_iSup_of_mem i ((mem_imgLat f).mpr ⟨_, (μ i).2, rfl⟩)
  · have : (fun i => scale Q' (imgLat f (Ls i))) = fun i => scale Q (Ls i) :=
      funext fun i => scale_imgLat Q Q' f hf (hle i)
    rw [this]
    exact hL.scale_strictAnti

theorem isometricLat_imgLat {J : Submodule R V} (hJL : J ≤ L) : IsometricLat Q Q' J (imgLat f J) := by
  have hinj : Function.Injective (K.subtype ∘ₗ f.toLinearMap) := fun a b h => f.injective (Subtype.ext h)
  refine ⟨(comapSubtypeEquivOfLe hJL).symm.trans (equivMapOfInjective _ hinj (J.comap L.subtype)), fun x => ?_⟩
  have := hf ⟨(x : V), hJL x.2⟩
  exact this

end Transport

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable {V'' : Type*} [AddCommGroup V''] [Module F V''] [Module R V''] [IsScalarTower R F V'']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V') (Q'' : QuadraticForm F V'')

/-- **Isometric lattices have Jordan splittings of the same type, and the same fundamental invariants**
(O'Meara 1963, §91C, p. 245, and §93E, p. 264). If $L \cong K$ and $L = L_1 \perp \cdots \perp L_t$ is a Jordan
splitting, then the images $K_i$ of the $L_i$ under the isometry form a Jordan splitting $K = K_1 \perp \cdots \perp
K_t$ with $L_i \cong K_i$, of the same Jordan type (`SameJordanType`), of the same fundamental type
(`SameFundamentalType`), with $\mathfrak w_i(L) = \mathfrak w_i(K)$, and with the same fundamental norm generators:
an isometry preserves $B$, hence the scales, norms, volumes, modularity, orthogonality, the lattices
$L^{\mathfrak a}$ and so $\mathfrak g_i$, $\mathfrak w_i$, $a_i$. -/
@[kb "omeara1963" "§93E, p. 264 (isometric lattices are of the same fundamental type; an isometry preserves the fundamental invariants)"]
theorem exists_jordanSplitting_of_isometricLat {L : Submodule R V} {K : Submodule R V'}
    (h : IsometricLat Q Q' L K) (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) :
    ∃ Ks : Fin t → Submodule R V', IsJordanSplitting Q' K Ks ∧ (∀ i, IsometricLat Q Q' (Ls i) (Ks i)) ∧
      SameJordanType Q Q' Ls Ks ∧ SameFundamentalType Q Q' L K Ls Ks ∧
      (∀ i, fundWeight Q L Ls i = fundWeight Q' K Ks i) ∧
      ∀ a, IsFundNormGenerators Q L Ls a ↔ IsFundNormGenerators Q' K Ks a := by
  obtain ⟨f, hf⟩ := h
  have hle : ∀ i, Ls i ≤ L := fun i => hL.split.iSup_eq ▸ le_iSup Ls i
  have hsc : ∀ i, scale Q' (imgLat f (Ls i)) = scale Q (Ls i) := fun i => scale_imgLat Q Q' f hf (hle i)
  have hfs : ∀ i, fundSub Q' K (fun i => imgLat f (Ls i)) i = imgLat f (fundSub Q L Ls i) := by
    intro i
    unfold fundSub
    rw [hsc i]
    exact subA_imgLat Q Q' f hf _
  have hfsle : ∀ i, fundSub Q L Ls i ≤ L := fun i x hx => hx.1
  have hg : ∀ i, fundNormGroup Q' K (fun i => imgLat f (Ls i)) i = fundNormGroup Q L Ls i := by
    intro i
    unfold fundNormGroup
    rw [hfs i]
    exact normGroup_imgLat Q Q' f hf (hfsle i)
  refine ⟨fun i => imgLat f (Ls i), isJordanSplitting_imgLat Q Q' f hf hfg hL,
    fun i => isometricLat_imgLat Q Q' f hf (hle i), ⟨rfl, fun i => ?_⟩, ⟨rfl, fun i => ?_⟩, fun i => ?_,
    fun a => ?_⟩
  · exact ⟨(hsc i).symm, (finrank_imgLat f (hle i)).symm, by
      show _ ↔ normIdeal Q' (imgLat f (Ls i)) = scale Q' (imgLat f (Ls i))
      rw [hsc i, normIdeal_imgLat Q Q' f hf (hle i)]⟩
  · exact ⟨(finrank_imgLat f (hle i)).symm, (hsc i).symm, (hg i).symm⟩
  · unfold fundWeight
    rw [hfs i]
    exact (weight_imgLat Q Q' f hf (hfsle i)).symm
  · unfold IsFundNormGenerators
    refine forall_congr' fun i => ?_
    unfold IsNormGenerator
    rw [hfs i, normGroup_imgLat Q Q' f hf (hfsle i), normIdeal_imgLat Q Q' f hf (hfsle i)]

/-- **Isometric lattices have a Jordan splitting of the same type** (O'Meara 1963, §91C, p. 245): the Jordan-type part
of `exists_jordanSplitting_of_isometricLat`. -/
@[kb "omeara1963" "§91C, p. 245 (isometric lattices are of the same Jordan type)"]
theorem exists_sameJordanType_of_isometricLat {L : Submodule R V} {K : Submodule R V'}
    (h : IsometricLat Q Q' L K) (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) :
    ∃ Ks : Fin t → Submodule R V', IsJordanSplitting Q' K Ks ∧ (∀ i, IsometricLat Q Q' (Ls i) (Ks i)) ∧
      SameJordanType Q Q' Ls Ks := by
  obtain ⟨Ks, h1, h2, h3, -⟩ := exists_jordanSplitting_of_isometricLat Q Q' h hfg hL
  exact ⟨Ks, h1, h2, h3⟩

/-- **`SameJordanType` is symmetric** (O'Meara 1963, §91C, p. 245). -/
@[kb "omeara1963" "§91C, p. 245 (lattices of the same Jordan type)"]
theorem SameJordanType.symm {t t' : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'}
    (h : SameJordanType Q Q' Ls Ks) : SameJordanType Q' Q Ks Ls := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, fun i => by obtain ⟨a, b, c⟩ := h i; exact ⟨a.symm, b.symm, c.symm⟩⟩

/-- **`SameJordanType` is transitive** (O'Meara 1963, §91C, p. 245). -/
@[kb "omeara1963" "§91C, p. 245 (lattices of the same Jordan type)"]
theorem SameJordanType.trans {t t' t'' : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'}
    {Ms : Fin t'' → Submodule R V''} (h : SameJordanType Q Q' Ls Ks) (h' : SameJordanType Q' Q'' Ks Ms) :
    SameJordanType Q Q'' Ls Ms := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  exact ⟨rfl, fun i => by
    obtain ⟨a, b, c⟩ := h i
    obtain ⟨a', b', c'⟩ := h' i
    exact ⟨a.trans a', b.trans b', c.trans c'⟩⟩

/-- **Lattices of the same Jordan type** (O'Meara 1963, §91C, p. 245): $L$ and $K$ have Jordan splittings
$L = L_1 \perp \cdots \perp L_t$ and $K = K_1 \perp \cdots \perp K_{t'}$ that are of the same Jordan type
(`SameJordanType`). For finitely generated regular non-zero lattices this does not depend on the choice of the
splittings (`hasSameJordanType_iff`, by Theorem 91:9). -/
@[kb "omeara1963" "§91C, p. 245 (lattices of the same Jordan type)"]
def HasSameJordanType (L : Submodule R V) (K : Submodule R V') : Prop :=
  ∃ (t t' : ℕ) (Ls : Fin t → Submodule R V) (Ks : Fin t' → Submodule R V'),
    IsJordanSplitting Q L Ls ∧ IsJordanSplitting Q' K Ks ∧ SameJordanType Q Q' Ls Ks

/-- **Same Jordan type does not depend on the splittings** (O'Meara 1963, §91C, p. 245, with 91:9): for finitely
generated regular non-zero lattices $L$, $K$, they are of the same Jordan type if and only if every pair of Jordan
splittings of $L$ and $K$ is of the same type. -/
@[kb "omeara1963" "§91C, p. 245 (lattices of the same Jordan type)"]
theorem hasSameJordanType_iff {L : Submodule R V} {K : Submodule R V'} (hL : L.FG) (hK : K.FG)
    (hLreg : IsRegular Q L) (hKreg : IsRegular Q' K) (hLne : L ≠ ⊥) (hKne : K ≠ ⊥) :
    HasSameJordanType Q Q' L K ↔ ∀ (t t' : ℕ) (Ls : Fin t → Submodule R V) (Ks : Fin t' → Submodule R V'),
      IsJordanSplitting Q L Ls → IsJordanSplitting Q' K Ks → SameJordanType Q Q' Ls Ks := by
  constructor
  · rintro ⟨t₀, t₀', Ls₀, Ks₀, hL₀, hK₀, h₀⟩ t t' Ls Ks hLs hKs
    have h1 := IsJordanSplitting.sameJordanType Q hL hLs hL₀
    have h2 := IsJordanSplitting.sameJordanType Q' hK hK₀ hKs
    exact (h1.trans Q Q Q' h₀).trans Q Q' Q' h2
  · intro h
    obtain ⟨t, Ls, hLs⟩ := exists_isJordanSplitting Q hL hLreg hLne
    obtain ⟨t', Ks, hKs⟩ := exists_isJordanSplitting Q' hK hKreg hKne
    exact ⟨t, t', Ls, Ks, hLs, hKs, h t t' Ls Ks hLs hKs⟩

/-- **`HasSameJordanType` is symmetric** (O'Meara 1963, §91C, p. 245). -/
@[kb "omeara1963" "§91C, p. 245 (lattices of the same Jordan type)"]
theorem HasSameJordanType.symm {L : Submodule R V} {K : Submodule R V'} (h : HasSameJordanType Q Q' L K) :
    HasSameJordanType Q' Q K L := by
  obtain ⟨t, t', Ls, Ks, h1, h2, h3⟩ := h
  exact ⟨t', t, Ks, Ls, h2, h1, h3.symm Q Q'⟩

/-- **`HasSameJordanType` is transitive** (O'Meara 1963, §91C, p. 245), for $K$ finitely generated (the middle
lattice's two Jordan splittings are compared by Theorem 91:9, which needs $K$ finitely generated). -/
@[kb "omeara1963" "§91C, p. 245 (lattices of the same Jordan type)"]
theorem HasSameJordanType.trans {L : Submodule R V} {K : Submodule R V'} {M : Submodule R V''}
    (hK : K.FG) (h : HasSameJordanType Q Q' L K) (h' : HasSameJordanType Q' Q'' K M) :
    HasSameJordanType Q Q'' L M := by
  obtain ⟨t, s, Ls, Ks, hL, hK1, h1⟩ := h
  obtain ⟨s', u, Ks', Ms, hK2, hM, h2⟩ := h'
  have h3 := IsJordanSplitting.sameJordanType Q' hK hK1 hK2
  exact ⟨t, u, Ls, Ms, hL, hM, (h1.trans Q Q' Q' h3).trans Q Q' Q'' h2⟩

/-- **Isometric lattices are of the same Jordan type** (O'Meara 1963, §91C, p. 245) for finitely generated regular
non-zero $L$. -/
@[kb "omeara1963" "§91C, p. 245 (isometric lattices are of the same Jordan type)"]
theorem IsometricLat.hasSameJordanType {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K)
    (hfg : L.FG) (hreg : IsRegular Q L) (hne : L ≠ ⊥) : HasSameJordanType Q Q' L K := by
  obtain ⟨t, Ls, hL⟩ := exists_isJordanSplitting Q hfg hreg hne
  obtain ⟨Ks, hK, -, hsame⟩ := exists_sameJordanType_of_isometricLat Q Q' h hfg hL
  exact ⟨t, t, Ls, Ks, hL, hK, hsame⟩

end Main

section Chains

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- A strictly monotone subfamily of a Jordan splitting is a Jordan splitting (of its sum). -/
theorem IsJordanSplitting.comp {L : Submodule R V} {t k : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (g : Fin k → Fin t) (hg : StrictMono g) :
    IsJordanSplitting Q (⨆ j, Ls (g j)) (fun j => Ls (g j)) :=
  ⟨⟨fun i j hij => hL.split.orth (g i) (g j) (hg.injective.ne hij), hL.split.indep.comp hg.injective, rfl⟩,
   fun j => hL.modular (g j), hL.scale_strictAnti.comp_strictMono hg⟩

/-- The index map $j \mapsto j$ from `Fin (i+1)` into `Fin t` (the components $L_1, \dots, L_i$ of the Jordan chain
$L_{(i)}$). -/
def chainIdx {t : ℕ} (i : Fin t) : Fin (i.val + 1) → Fin t := Fin.castLE (Nat.succ_le_of_lt i.isLt)

theorem chainIdx_strictMono {t : ℕ} (i : Fin t) : StrictMono (chainIdx i) := by
  intro a b h
  rw [Fin.lt_def] at h ⊢
  exact h

/-- The index map $j \mapsto i + j$ from `Fin (t - i)` into `Fin t` (the components $L_i, \dots, L_t$ of the inverse
Jordan chain $L^{(i)}$). -/
def tailIdx {t : ℕ} (i : Fin t) : Fin (t - i.val) → Fin t := fun j =>
  ⟨i.val + j.val, by have := j.isLt; have := i.isLt; omega⟩

theorem tailIdx_strictMono {t : ℕ} (i : Fin t) : StrictMono (tailIdx i) := by
  intro a b h
  rw [Fin.lt_def] at h ⊢
  simp only [tailIdx]
  omega

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
theorem jordanChain_eq_iSup {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) :
    jordanChain Ls i = ⨆ j, Ls (chainIdx i j) := by
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    refine le_iSup_of_le (f := fun j => Ls (chainIdx i j)) ⟨k.val, by rw [Fin.le_def] at hk; omega⟩ ?_
    exact le_of_eq (congrArg Ls (Fin.ext rfl)).symm
  · exact iSup_le fun j => le_iSup₂_of_le (chainIdx i j) (by rw [Fin.le_def]; simp [chainIdx]; omega) le_rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
theorem invJordanChain_eq_iSup {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) :
    invJordanChain Ls i = ⨆ j, Ls (tailIdx i j) := by
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    refine le_iSup_of_le (f := fun j => Ls (tailIdx i j))
      ⟨k.val - i.val, by rw [Fin.le_def] at hk; have := k.isLt; omega⟩ ?_
    refine le_of_eq (congrArg Ls (Fin.ext ?_)).symm
    simp only [tailIdx]
    rw [Fin.le_def] at hk
    omega
  · exact iSup_le fun j => le_iSup₂_of_le (tailIdx i j) (by rw [Fin.le_def]; simp [tailIdx]) le_rfl

/-- The first $i$ components of a Jordan splitting of $L$ form a Jordan splitting of the Jordan chain $L_{(i)}$
(O'Meara 1963, §91C, p. 245). -/
theorem isJordanSplitting_jordanChain {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    IsJordanSplitting Q (jordanChain Ls i) (fun j => Ls (chainIdx i j)) := by
  rw [jordanChain_eq_iSup]
  exact hL.comp Q _ (chainIdx_strictMono i)

/-- The last components of a Jordan splitting of $L$ form a Jordan splitting of the inverse Jordan chain
$L^{(i)}$ (O'Meara 1963, §91C, p. 246). -/
theorem isJordanSplitting_invJordanChain {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    IsJordanSplitting Q (invJordanChain Ls i) (fun j => Ls (tailIdx i j)) := by
  rw [invJordanChain_eq_iSup]
  exact hL.comp Q _ (tailIdx_strictMono i)

/-- A lattice with a Jordan splitting is regular (its components are regular and orthogonal). -/
theorem isRegular_of_isJordanSplitting {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) : IsRegular Q L := by
  have hle : ∀ j, Ls j ≤ L := fun j => hL.split.iSup_eq ▸ le_iSup Ls j
  intro x hx h0
  have hx2 : x ∈ ⨆ i, Ls i := hL.split.iSup_eq ▸ hx
  obtain ⟨μ, hμ⟩ := (mem_iSup_fin_iff Ls x).mp hx2
  have hμ0 : ∀ j, (μ j : V) = 0 := fun j =>
    (hL.modular j).isRegular Q (FG.of_le hfg (hle j)) _ (μ j).2 fun z hz => by
      have := h0 z (hle j hz)
      rw [← hμ, bil_sum_left, Finset.sum_eq_single j] at this
      · exact this
      · intro k _ hk; exact hL.split.orth k j hk _ (μ k).2 z hz
      · simp
  rw [← hμ]
  exact Finset.sum_eq_zero fun j _ => hμ0 j

/-- **A Jordan chain is a Jordan splitting's partial sums, with the new component the orthogonal complement**
(O'Meara 1963, §91C, p. 246): for $i + 1 = j$, $L_j = \{x \in L_{(j)} : B(x, L_{(i)}) = 0\}$ (`splitComp`). -/
@[kb "omeara1963" "§91C, p. 246 (a Jordan chain is determined by one and only one Jordan splitting)"]
theorem eq_splitComp_jordanChain {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i j : Fin t) (hij : i.val + 1 = j.val) :
    Ls j = splitComp Q (jordanChain Ls j) (jordanChain Ls i) := by
  have hsum := isOrthSum_jordanChain_succ Q hfg hL i j hij
  have hle : ∀ j, Ls j ≤ L := fun j => hL.split.iSup_eq ▸ le_iSup Ls j
  have hcfg : (jordanChain Ls i).FG := FG.of_le hfg (iSup₂_le fun k _ => hle k)
  have hreg : IsRegular Q (jordanChain Ls i) :=
    (isRegular_of_isJordanSplitting Q hcfg (isJordanSplitting_jordanChain Q hL i))
  ext x
  constructor
  · intro hx
    refine ⟨hsum.sup_eq ▸ mem_sup_right hx, fun z hz => ?_⟩
    rw [bil_comm]; exact hsum.orth z hz x hx
  · rintro ⟨hx, hx2⟩
    rw [← hsum.sup_eq] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
    have ha0 : a = 0 := hreg a ha fun z hz => by
      have := hx2 z hz
      rwa [bil_add_left, bil_comm Q b z, hsum.orth z hz b hb, add_zero] at this
    rw [ha0, zero_add]
    exact hb

/-- **A Jordan chain is determined by one and only one Jordan splitting** (O'Meara 1963, §91C, p. 246): if two
Jordan splittings $L = L_1 \perp \cdots \perp L_t$ and $L = K_1 \perp \cdots \perp K_t$ of the same lattice have the
same Jordan chain $L_{(i)} = K_{(i)}$ for all $i$, then $L_i = K_i$ for all $i$. -/
@[kb "omeara1963" "§91C, p. 246 (a Jordan chain is determined by one and only one Jordan splitting)"]
theorem eq_of_jordanChain_eq {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q L Ks)
    (h : jordanChain Ls = jordanChain Ks) : Ls = Ks := by
  funext j
  by_cases hj : j.val = 0
  · rw [← jordanChain_zero Ls j hj, ← jordanChain_zero Ks j hj, h]
  · have hij : (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin t).val + 1 = j.val := by
      simp only; omega
    rw [eq_splitComp_jordanChain Q hfg hL _ j hij, eq_splitComp_jordanChain Q hfg hK _ j hij, h]

/-- In a valuation ring, two finitely generated submodules of $F$ are comparable. -/
theorem le_total_of_fg {s s' : Submodule R F} (hs : s.FG) (hs' : s'.FG) : s ≤ s' ∨ s' ≤ s := by
  obtain ⟨a, -, ha⟩ := exists_mem_span_eq_singleton (R := R) (S := (s : Set F)) (by rwa [span_eq])
  obtain ⟨b, -, hb⟩ := exists_mem_span_eq_singleton (R := R) (S := (s' : Set F)) (by rwa [span_eq])
  rw [span_eq] at ha hb
  rw [ha, hb]
  rcases span_pair_eq (R := R) a b with h | h
  · right; exact sup_eq_left.mp h
  · left; exact sup_eq_right.mp h

theorem exists_mul_bil_mem {L : Submodule R V} (hfg : L.FG) {a : Submodule R F} (haf : a.FG) (ha0 : a ≠ ⊥) :
    ∃ c : R, c ≠ 0 ∧ ∀ y ∈ L, ∀ z ∈ L, algebraMap R F c * bil Q y z ∈ a := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_span_singleton haf ha0
  obtain ⟨x, hx, y, hy, hs⟩ := exists_scale_eq Q hfg
  have hmem : ∀ y' ∈ L, ∀ z' ∈ L, bil Q y' z' ∈ R ∙ bil Q x y :=
    fun y' hy' z' hz' => hs ▸ bil_mem_scale Q hy' hz'
  by_cases hβ : bil Q x y = 0
  · refine ⟨1, one_ne_zero, fun y' hy' z' hz' => ?_⟩
    have := hmem y' hy' z' hz'
    rw [hβ, Submodule.span_zero_singleton, Submodule.mem_bot] at this
    rw [this, mul_zero]
    exact zero_mem _
  · rcases ValuationRing.isInteger_or_isInteger R (α / bil Q x y) with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hαr : α = algebraMap R F r * bil Q x y := by rw [hr]; field_simp
      refine ⟨r, ?_, fun y' hy' z' hz' => ?_⟩
      · rintro rfl; rw [map_zero, zero_mul] at hαr; exact hα hαr
      · obtain ⟨s, hs'⟩ := mem_span_singleton.mp (hmem y' hy' z' hz')
        rw [← hs', Algebra.smul_def]
        exact mem_span_singleton.mpr ⟨s, by rw [Algebra.smul_def, hαr]; ring⟩
    · have hβα : bil Q x y = algebraMap R F r * α := by rw [hr, inv_div]; field_simp
      refine ⟨1, one_ne_zero, fun y' hy' z' hz' => ?_⟩
      obtain ⟨s, hs'⟩ := mem_span_singleton.mp (hmem y' hy' z' hz')
      rw [← hs', Algebra.smul_def, hβα, map_one, one_mul]
      exact mem_span_singleton.mpr ⟨s * r, by rw [Algebra.smul_def, map_mul]; ring⟩

/-- $L^{\mathfrak a}$ of a regular finitely generated lattice is regular, for $\mathfrak a \ne 0$ finitely generated
(some non-zero multiple of every vector of $L$ lies in $L^{\mathfrak a}$). -/
theorem isRegular_subA {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {a : Submodule R F}
    (haf : a.FG) (ha0 : a ≠ ⊥) : IsRegular Q (subA Q a L) := by
  obtain ⟨c, hc, hcm⟩ := exists_mul_bil_mem Q hfg haf ha0
  intro x hx h0
  refine hreg x hx.1 fun y hy => ?_
  have hcy : c • y ∈ subA Q a L :=
    ⟨L.smul_mem c hy, fun z hz => by rw [bil_rsmul_left]; exact hcm y hy z hz⟩
  have := h0 _ hcy
  rw [bil_rsmul_right] at this
  have hc' : algebraMap R F c ≠ 0 := fun h => hc (IsFractionRing.injective R F (by rw [h, map_zero]))
  exact (mul_eq_zero.mp this).resolve_left hc'

/-- **An $\mathfrak a$-modular component is the first component of a Jordan splitting of $L^{\mathfrak a}$**
(O'Meara 1963, §91C, p. 244): for a Jordan splitting $L = L_1 \perp \cdots \perp L_t$ of a finitely generated lattice
and $\mathfrak a = \mathfrak sL_i$, there is a Jordan splitting $L^{\mathfrak a} = M_0 \perp M_1 \perp \cdots \perp M_k$
with $M_0 = L_i$ (`Ms 0 = Ls i`; the other components have scales strictly inside $\mathfrak a$). -/
@[kb "omeara1963" "§91C, p. 244 (an a-modular component of a Jordan splitting of L is the first component of some Jordan splitting of L^a)"]
theorem exists_isJordanSplitting_subA {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    ∃ (k : ℕ) (Ms : Fin (k + 1) → Submodule R V),
      IsJordanSplitting Q (subA Q (scale Q (Ls i)) L) Ms ∧ Ms 0 = Ls i := by
  obtain ⟨hsum, hnot⟩ := isOrthSum_subA Q hfg hL i
  have hle : ∀ j, Ls j ≤ L := fun j => hL.split.iSup_eq ▸ le_iSup Ls j
  have hfgj : ∀ j, (Ls j).FG := fun j => FG.of_le hfg (hle j)
  set a := scale Q (Ls i) with ha
  set M' := ⨆ j : {j // j ≠ i}, subA Q a (Ls j) with hM'
  have hLreg := isRegular_of_isJordanSplitting Q hfg hL
  have hai : a ≠ ⊥ := (hL.modular i).1
  have hafg : a.FG := scale_fg Q (hfgj i)
  have hreg : IsRegular Q (subA Q a L) := isRegular_subA Q hfg hLreg hafg hai
  have hM'reg : IsRegular Q M' := IsOrthSum.isRegular_right Q hsum hreg
  have hLafg : (subA Q a L).FG := FG.of_le hfg (fun x hx => hx.1)
  have hM'le : M' ≤ subA Q a L := hsum.sup_eq ▸ le_sup_right
  have hM'fg : M'.FG := FG.of_le hLafg hM'le
  obtain ⟨t', Ms', hMs'⟩ : ∃ t', ∃ Ms' : Fin t' → Submodule R V, IsJordanSplitting Q M' Ms' := by
    by_cases h0 : M' = ⊥
    · refine ⟨0, fun j => j.elim0, ⟨⟨fun i => i.elim0, iSupIndep_of_orth Q (fun i => i.elim0)
        (fun i => i.elim0), ?_⟩, fun i => i.elim0, fun i => i.elim0⟩⟩
      rw [h0]; exact iSup_of_empty _
    · exact exists_isJordanSplitting Q hM'fg hM'reg h0
  have hMsle : ∀ j, Ms' j ≤ M' := fun j => hMs'.split.iSup_eq ▸ le_iSup Ms' j
  have hscM : scale Q M' < a := by
    rcases le_total_of_fg (scale_fg Q hM'fg) hafg with h | h
    · exact lt_of_le_not_ge h hnot
    · exact absurd h hnot
  let Ms : Fin (t' + 1) → Submodule R V := Fin.cons (Ls i) Ms'
  have horth : ∀ p q, p ≠ q → ∀ x ∈ Ms p, ∀ y ∈ Ms q, bil Q x y = 0 := by
    intro p q hpq
    refine Fin.cases (fun hpq => ?_) (fun p hpq => ?_) p hpq
    · refine Fin.cases (fun h => absurd rfl h) (fun q _ => ?_) q hpq
      intro x hx y hy
      exact hsum.orth x hx y (hMsle q hy)
    · refine Fin.cases (fun _ => ?_) (fun q hpq => ?_) q hpq
      · intro x hx y hy
        rw [bil_comm]; exact hsum.orth y hy x (hMsle p hx)
      · exact hMs'.split.orth p q (fun h => hpq (h ▸ rfl))
  have hmod : ∀ p, IsModular Q (scale Q (Ms p)) (Ms p) := by
    intro p
    refine Fin.cases ?_ (fun p => ?_) p
    · simp only [Ms, Fin.cons_zero]; exact hL.modular i
    · simp only [Ms, Fin.cons_succ]; exact hMs'.modular p
  refine ⟨t', Ms, ⟨⟨horth, ?_, ?_⟩, hmod, ?_⟩, by simp [Ms]⟩
  · refine iSupIndep_of_orth Q horth fun p => (hmod p).isRegular Q ?_
    refine Fin.cases ?_ (fun p => ?_) p
    · simp only [Ms, Fin.cons_zero]; exact hfgj i
    · simp only [Ms, Fin.cons_succ]; exact FG.of_le hM'fg (hMsle p)
  · rw [iSup_fin_cons, hMs'.split.iSup_eq, hsum.sup_eq]
  · intro p q hpq
    refine Fin.cases (fun hpq => ?_) (fun p hpq => ?_) p hpq
    · obtain ⟨q, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hpq)
      simp only [Ms, Fin.cons_zero, Fin.cons_succ]
      exact lt_of_le_of_lt (scale_mono Q (hMsle q)) hscM
    · obtain ⟨q, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hpq))
      simp only [Ms, Fin.cons_succ]
      exact hMs'.scale_strictAnti (Fin.succ_lt_succ_iff.mp hpq)

/-- **The chains $L_{(i)}$, $K_{(i)}$ of Jordan splittings of the same type are of the same Jordan type**
(O'Meara 1963, §91C, 91:11, p. 246): if $L = L_1 \perp \cdots \perp L_t$ and $K = K_1 \perp \cdots \perp K_t$ are
Jordan splittings of the same type, then $L_{(i)}$ and $K_{(i)}$ are of the same Jordan type; here `i'` is the index
`i` in the second splitting (`i'.val = i.val`). -/
@[kb "omeara1963" "§91C, 91:11, p. 246 (L_(i), K_(i) are of the same Jordan type)"]
theorem hasSameJordanType_jordanChain {L : Submodule R V} {K : Submodule R V'} {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (h : SameJordanType Q Q' Ls Ks) (i : Fin t) (i' : Fin t')
    (hi : i.val = i'.val) : HasSameJordanType Q Q' (jordanChain Ls i) (jordanChain Ks i') := by
  obtain ⟨rfl, hty⟩ := h
  refine ⟨i.val + 1, i'.val + 1, _, _, isJordanSplitting_jordanChain Q hL i,
    isJordanSplitting_jordanChain Q' hK i', by omega, fun j => ?_⟩
  have e : chainIdx i' (Fin.cast (by omega) j) = Fin.cast rfl (chainIdx i j) := Fin.ext rfl
  have := hty (chainIdx i j)
  simp only [e]
  exact this

/-- **The analogue for inverse Jordan chains** (O'Meara 1963, §91C, 91:11, p. 246): $L^{(i)}$ and $K^{(i)}$ are of
the same Jordan type for Jordan splittings of the same type. -/
@[kb "omeara1963" "§91C, 91:11, p. 246 (the same applies to inverse Jordan chains)"]
theorem hasSameJordanType_invJordanChain {L : Submodule R V} {K : Submodule R V'} {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (h : SameJordanType Q Q' Ls Ks) (i : Fin t) (i' : Fin t')
    (hi : i.val = i'.val) : HasSameJordanType Q Q' (invJordanChain Ls i) (invJordanChain Ks i') := by
  obtain ⟨rfl, hty⟩ := h
  have ht : t - i.val = t - i'.val := by omega
  refine ⟨t - i.val, t - i'.val, _, _, isJordanSplitting_invJordanChain Q hL i,
    isJordanSplitting_invJordanChain Q' hK i', ht, fun j => ?_⟩
  have e : tailIdx i' (Fin.cast ht j) = Fin.cast rfl (tailIdx i j) := Fin.ext (by simp [tailIdx]; omega)
  have := hty (tailIdx i j)
  beta_reduce
  rw [e]
  exact this

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
theorem invJordanChain_last' {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) (hi : i.val + 1 = t) :
    invJordanChain Ls i = Ls i := by
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    have : k = i := Fin.ext (by rw [Fin.le_def] at hk; have := k.isLt; omega)
    rw [this]
  · exact le_iSup₂_of_le i le_rfl le_rfl

/-- $L^{(i)} = L_i \perp L^{(i+1)}$ for a Jordan splitting. -/
theorem isOrthSum_invJordanChain_succ {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i j : Fin t) (hij : i.val + 1 = j.val) :
    IsOrthSum Q (invJordanChain Ls i) (Ls i) (invJordanChain Ls j) := by
  have hle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  have hreg : IsRegular Q (Ls i) := (hL.modular i).isRegular Q (FG.of_le hfg (hle i))
  have horth : ∀ x ∈ invJordanChain Ls j, ∀ y ∈ Ls i, bil Q x y = 0 := by
    intro x hx y hy
    refine bil_eq_zero_of_mem_iSup Q (P := fun k => j ≤ k) (fun k hk z hz => ?_) hx
    exact hL.split.orth k i (fun h => by subst h; rw [Fin.le_def] at hk; omega) z hz y hy
  refine ⟨fun x hx y hy => by rw [bil_comm]; exact horth y hy x hx, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (mem_bot R).mpr (hreg x hx1 fun y hy => horth x hx2 y hy)
  · apply le_antisymm
    · exact sup_le (le_iSup₂_of_le i le_rfl le_rfl)
        (iSup₂_mono' fun k hk => ⟨k, by rw [Fin.le_def] at hk ⊢; omega, le_rfl⟩)
    · refine iSup₂_le fun k hk => ?_
      by_cases hki : k = i
      · subst hki; exact le_sup_left
      · refine le_sup_of_le_right (le_iSup₂_of_le k ?_ le_rfl)
        rw [Fin.le_def] at hk ⊢
        have : k.val ≠ i.val := fun h => hki (Fin.ext h)
        omega

/-- **Volumes along inverse Jordan chains** (O'Meara 1963, §91C, 91:11, p. 246): for Jordan splittings with
$\mathfrak sL_i = \mathfrak sK_i$ and $\dim L_i = \dim K_i$, the inverse Jordan chains have
$\mathfrak vL^{(i)} = \mathfrak vK^{(i)}$. -/
theorem volume_invJordanChain_eq {L : Submodule R V} {K : Submodule R V'} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (hsc : ∀ i, scale Q (Ls i) = scale Q' (Ks i))
    (hrk : ∀ i, finrank R (Ls i) = finrank R (Ks i)) (i : Fin t) :
    volume Q (invJordanChain Ls i) = volume Q' (invJordanChain Ks i) := by
  have hcomp : ∀ i, volume Q (Ls i) = volume Q' (Ks i) := by
    intro i; rw [(hL.modular i).2.2, (hK.modular i).2.2, hsc, hrk]
  have hLle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  have hKle : ∀ k, Ks k ≤ K := fun k => hK.split.iSup_eq ▸ le_iSup Ks k
  obtain ⟨n, hn⟩ : ∃ n, i.val + n + 1 = t := ⟨t - 1 - i.val, by have := i.isLt; omega⟩
  induction n generalizing i with
  | zero =>
    rw [invJordanChain_last' Ls i (by omega), invJordanChain_last' Ks i (by omega), hcomp]
  | succ n ih =>
    let j : Fin t := ⟨i.val + 1, by omega⟩
    have h1 := isOrthSum_invJordanChain_succ Q hLfg hL i j rfl
    have h2 := isOrthSum_invJordanChain_succ Q' hKfg hK i j rfl
    have hcL : (invJordanChain Ls j).FG := FG.of_le hLfg (iSup₂_le fun k _ => hLle k)
    have hcK : (invJordanChain Ks j).FG := FG.of_le hKfg (iSup₂_le fun k _ => hKle k)
    rw [volume_eq_mul_of_isOrthSum Q h1 (FG.of_le hLfg (hLle i)) hcL,
      volume_eq_mul_of_isOrthSum Q' h2 (FG.of_le hKfg (hKle i)) hcK,
      ih j (by show i.val + 1 + n + 1 = t; omega), hcomp]

/-- **Example 91:11 for inverse Jordan chains** (O'Meara 1963, §91C, p. 246: "the same applies to inverse Jordan
chains"): let $L^{(1)} \supseteq \cdots \supseteq L^{(t)}$ and $K^{(1)} \supseteq \cdots \supseteq K^{(t)}$ be the inverse
Jordan chains of lattices of the same Jordan type. Then $\mathfrak vL^{(i)} = \mathfrak vK^{(i)}$, and hence
$dL^{(i)}/dK^{(i)}$ is a unit: for all bases $b$ of $L^{(i)}$ and $b'$ of $K^{(i)}$, $d(b) = \varepsilon\, d(b')$ with
$\varepsilon \in \mathfrak u$. (That $L^{(i)}$ and $K^{(i)}$ are of the same Jordan type is
`hasSameJordanType_invJordanChain`.) -/
@[kb "omeara1963" "§91C, 91:11, p. 246 (the same applies to inverse Jordan chains)"]
theorem exists_unit_det_invJordanChain {L : Submodule R V} {K : Submodule R V'} (hLfg : L.FG) (hKfg : K.FG)
    {t : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (htype : SameJordanType Q Q' Ls Ks) (i : Fin t) :
    volume Q (invJordanChain Ls i) = volume Q' (invJordanChain Ks i) ∧
      ∀ (b : Basis (Fin (finrank R (invJordanChain Ls i))) R (invJordanChain Ls i))
        (b' : Basis (Fin (finrank R (invJordanChain Ks i))) R (invJordanChain Ks i)),
        ∃ ε : R, IsUnit ε ∧ (gram Q fun k => (b k : V)).det =
          algebraMap R F ε * (gram Q' fun k => (b' k : V')).det := by
  obtain ⟨htt, hty⟩ := htype
  have hsc : ∀ i, scale Q (Ls i) = scale Q' (Ks i) := fun i => by simpa using (hty i).1
  have hrk : ∀ i, finrank R (Ls i) = finrank R (Ks i) := fun i => by simpa using (hty i).2.1
  have hv := volume_invJordanChain_eq Q Q' hLfg hKfg hL hK hsc hrk i
  refine ⟨hv, fun b b' => ?_⟩
  rw [volume_eq_span_det Q b, volume_eq_span_det Q' b'] at hv
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := F)
  obtain ⟨u, hu⟩ := (span_singleton_eq_span_singleton).mp hv
  refine ⟨↑u⁻¹, Units.isUnit _, ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

end Chains

end QuadFormsKB.OMeara
