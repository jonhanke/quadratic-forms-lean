import QuadFormsKB.Tamagawa.Measure.Weil.ConeAdelicGroup
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCoord
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereBoxFormula

/-!
# The adelic punctured cone, its section and the orbit coordinates

$F$ a number field, $Q_0$ a form over $\mathcal O_F$ in $n = m+1$ variables, $e\in F^n$ isotropic with an isotropic frame
(`IsoFrame`). Then:

* **`adelicCone Q₀`** $= C(\mathbb A) = \{y\in\mathbb A^n : q(y_v) = 0,\ y_v\ne0$ at every place, $y_v$ primitive in
  $\mathfrak o_v^n$ for almost every finite $v\}$ (`PrimV`), a measurable set (`measurableSet_adelicCone`) preserved by
  $SO(V)(\mathbb A)$ (`smul_mem_adelicCone`).
* **`ConeSecData.secA`**: a measurable section $s : C(\mathbb A)\to SO(V)(\mathbb A)$, $s(y)\,e = y$ (`secA_smul`), at every
  place the two-reflection map $\tau_{y-\zeta}\tau_{\zeta - e}$ of `ConeAdelicFrame.lean` with the branch `bestIdx`; it is
  integral at every good place on primitive vectors (`secM_mem_intMat`), which puts it in the restricted product.
* **`ConeSecData.coordEquiv`**: the orbit coordinates $C(\mathbb A)\times P\simeq SO(V)(\mathbb A)$,
  $(y, p)\mapsto p\,s(y)^{-1}$, $P = \operatorname{Stab}(e)$ (`stabP`), a measurable equivalence (Lusin–Souslin).
In particular $C(\mathbb A)$ is the $SO(V)(\mathbb A)$-orbit of $e$.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

/-! ### Primitive vectors -/

section Prim

variable (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F

/-- **Primitive integral vectors** at $v$: $x\in\mathfrak o_v^n\setminus\mathfrak p_v\mathfrak o_v^n$. -/
def PrimV (x : Fin n → Fv) : Prop := IntVec v x ∧ ∃ i, Valued.v (x i) = 1

theorem measurableSet_valued_eq_one : MeasurableSet {a : Fv | Valued.v a = 1} := by
  have h1 : MeasurableSet {a : Fv | Valued.v a ≤ Valued.v (1 : Fv)} :=
    (measurable_id.prodMk measurable_const) (measurableSet_valued_le v)
  have h2 : MeasurableSet {a : Fv | Valued.v (1 : Fv) ≤ Valued.v a} :=
    (measurable_const.prodMk measurable_id) (measurableSet_valued_le v)
  have : {a : Fv | Valued.v a = 1} = {a | Valued.v a ≤ Valued.v (1 : Fv)} ∩ {a | Valued.v (1 : Fv) ≤ Valued.v a} := by
    ext a; simp only [mem_setOf_eq, mem_inter_iff, map_one]; exact le_antisymm_iff
  rw [this]; exact h1.inter h2

theorem measurableSet_primVec : MeasurableSet {x : Fin n → Fv | PrimV v x} := by
  have : {x : Fin n → Fv | PrimV v x} = {x | IntVec v x} ∩ ⋃ i, (fun x => x i) ⁻¹' {a | Valued.v a = 1} := by
    ext x; simp [PrimV]
  rw [this]
  exact (measurableSet_intVec v).inter (MeasurableSet.iUnion fun i => (measurable_pi_apply i)
    (measurableSet_valued_eq_one v))

/-- If $y$ is integral with all coordinates in $\mathfrak p_v$ and $A$ is integral, so is $Ay$. -/
theorem lt_one_mulVec {A : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intMat v) {y : Fin n → Fv}
    (hy : ∀ i, Valued.v (y i) < 1) (i : Fin n) : Valued.v ((A *ᵥ y) i) < 1 := by
  simp only [mulVec, dotProduct]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [Valuation.map_mul]
  calc Valued.v (A i l) * Valued.v (y l) ≤ 1 * Valued.v (y l) := mul_le_mul_left (hA i l) _
    _ = Valued.v (y l) := one_mul _
    _ < 1 := hy l

/-- **An integral matrix with integral inverse preserves primitivity.** -/
theorem PrimV.mulVec {A : GL (Fin n) Fv} (hA : A.val ∈ intMat v) (hA' : A⁻¹.val ∈ intMat v) {x : Fin n → Fv}
    (hx : PrimV v x) : PrimV v (A.val *ᵥ x) := by
  refine ⟨hx.1.mulVec v hA, ?_⟩
  by_contra h
  push Not at h
  have hlt : ∀ i, Valued.v ((A.val *ᵥ x) i) < 1 := fun i =>
    lt_of_le_of_ne ((hx.1.mulVec v hA) i) (h i)
  obtain ⟨i, hi⟩ := hx.2
  have := lt_one_mulVec v hA' hlt i
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec, hi] at this
  exact lt_irrefl _ this

end Prim

/-! ### The adelic punctured cone -/

section Cone

variable {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

/-- **The adelic punctured cone** $C(\mathbb A)$: isotropic and nonzero at every place, primitive at almost every
finite place. -/
@[kb "weil1982" "§4.5, p. 108 (the adelic cone C°_A) [unverified page]"]
def adelicCone : Set (AdeleSpace F (Fin n)) :=
  {y | (∀ w, qH (hesAt Q₀ (σR w)) (adR y w) = 0 ∧ adR y w ≠ 0) ∧
    (∀ w, qH (hesAt Q₀ (σC w)) (adC y w) = 0 ∧ adC y w ≠ 0) ∧
    (∀ v, qH (hesAt Q₀ (σV v)) (adV y v) = 0 ∧ adV y v ≠ 0) ∧ ∀ᶠ v in Filter.cofinite, PrimV v (adV y v)}

theorem continuous_adR (w : {w : InfinitePlace F // w.IsReal}) :
    Continuous fun y : AdeleSpace F (Fin n) => adR y w :=
  continuous_pi fun j => (continuous_apply w).comp (continuous_fst.comp (continuous_fst.comp (continuous_apply j)))

theorem continuous_adC (w : {w : InfinitePlace F // w.IsComplex}) :
    Continuous fun y : AdeleSpace F (Fin n) => adC y w :=
  continuous_pi fun j => (continuous_apply w).comp (continuous_snd.comp (continuous_fst.comp (continuous_apply j)))

theorem continuous_adV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun y : AdeleSpace F (Fin n) => adV y v :=
  continuous_pi fun j => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply j))

theorem measurableSet_adelicCone : MeasurableSet (adelicCone Q₀) := by
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal},
      MeasurableSet {y : AdeleSpace F (Fin n) | qH (hesAt Q₀ (σR w)) (adR y w) = 0 ∧ adR y w ≠ 0} := fun w =>
    (((continuous_qH _).comp (continuous_adR w)).measurable (measurableSet_singleton 0)).inter
      ((continuous_adR w).measurable (measurableSet_singleton 0).compl)
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      MeasurableSet {y : AdeleSpace F (Fin n) | qH (hesAt Q₀ (σC w)) (adC y w) = 0 ∧ adC y w ≠ 0} := fun w =>
    (((continuous_qH _).comp (continuous_adC w)).measurable (measurableSet_singleton 0)).inter
      ((continuous_adC w).measurable (measurableSet_singleton 0).compl)
  have hV : ∀ v : HeightOneSpectrum (𝓞 F),
      MeasurableSet {y : AdeleSpace F (Fin n) | qH (hesAt Q₀ (σV v)) (adV y v) = 0 ∧ adV y v ≠ 0} := fun v =>
    (((continuous_qH _).comp (continuous_adV v)).measurable (measurableSet_singleton 0)).inter
      ((continuous_adV v).measurable (measurableSet_singleton 0).compl)
  have hP : MeasurableSet {y : AdeleSpace F (Fin n) | ∀ᶠ v in Filter.cofinite, PrimV v (adV y v)} := by
    have : {y : AdeleSpace F (Fin n) | ∀ᶠ v in Filter.cofinite, PrimV v (adV y v)} =
        ⋃ s : Finset (HeightOneSpectrum (𝓞 F)), ⋂ v, ⋂ (_ : v ∉ s), {y | PrimV v (adV y v)} := by
      ext y
      simp only [mem_setOf_eq, mem_iUnion, mem_iInter, Filter.eventually_cofinite]
      constructor
      · intro h
        exact ⟨h.toFinset, fun v hv => by by_contra h'; exact hv (h.mem_toFinset.mpr h')⟩
      · rintro ⟨s, hs⟩
        exact s.finite_toSet.subset fun v hv => by by_contra h'; exact hv (hs v h')
    rw [this]
    exact MeasurableSet.iUnion fun s => MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
      (continuous_adV v).measurable (measurableSet_primVec v)
  have heq : adelicCone Q₀ = (⋂ w, {y : AdeleSpace F (Fin n) | qH (hesAt Q₀ (σR w)) (adR y w) = 0 ∧ adR y w ≠ 0}) ∩
      ((⋂ w, {y | qH (hesAt Q₀ (σC w)) (adC y w) = 0 ∧ adC y w ≠ 0}) ∩
        ((⋂ v, {y | qH (hesAt Q₀ (σV v)) (adV y v) = 0 ∧ adV y v ≠ 0}) ∩
          {y | ∀ᶠ v in Filter.cofinite, PrimV v (adV y v)})) := by
    ext y; simp [adelicCone]
  rw [heq]
  exact (MeasurableSet.iInter hR).inter ((MeasurableSet.iInter hC).inter ((MeasurableSet.iInter hV).inter hP))

instance standardBorel_adelicCone : StandardBorelSpace (adelicCone Q₀) := by
  have : BorelSpace (AdeleSpace F (Fin n)) := inferInstance
  have : StandardBorelSpace (AdeleSpace F (Fin n)) := inferInstance
  exact (measurableSet_adelicCone Q₀).standardBorel

theorem mulVec_ne_zero_of_GL {K : Type*} [Field K] {M : GL (Fin n) K} {x : Fin n → K} (hx : x ≠ 0) :
    M.val *ᵥ x ≠ 0 := fun h => hx (by rw [← one_mulVec x, ← Units.inv_mul M, ← mulVec_mulVec, h, mulVec_zero])

/-- **$SO(V)(\mathbb A)$ preserves the adelic cone.** -/
theorem smul_mem_adelicCone (g : SOAdele Q₀) {y : AdeleSpace F (Fin n)} (hy : y ∈ adelicCone Q₀) :
    g • y ∈ adelicCone Q₀ := by
  refine ⟨fun w => ⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩, fun v => ⟨?_, ?_⟩, ?_⟩
  · rw [smul_apply_fst_fst, ← (hy.1 w).1]
    exact qH_mulVec_of_orth (AdelicSphereSetup.hes_of_mem_soReal Q₀ (σR w) (g.1.1 w).2).1 (adR y w)
  · exact mulVec_ne_zero_of_GL (M := ArchSO.incl _ (g.1.1 w)) (hy.1 w).2
  · rw [smul_apply_fst_snd, ← (hy.2.1 w).1]
    exact qH_mulVec_of_orth (AdelicSphereSetup.hes_of_mem_soC Q₀ (σC w) (g.1.2 w).2).1 (adC y w)
  · exact mulVec_ne_zero_of_GL (M := ArchSOC.incl _ (g.1.2 w)) (hy.2.1 w).2
  · rw [smul_apply_snd, ← (hy.2.2.1 v).1]
    exact qH_mulVec_of_orth ((mem_orthGroup _).mp ((g.2 : OAf (Q₀.map (algebraMap (𝓞 F) F))) v).2) (adV y v)
  · exact mulVec_ne_zero_of_GL (hy.2.2.1 v).2
  · filter_upwards [(g.2 : OAf (Q₀.map (algebraMap (𝓞 F) F))).2, hy.2.2.2] with v hv hp
    have hv' := (mem_glInt_iff v).mp hv
    rw [smul_apply_snd]
    exact hp.mulVec v hv'.1 hv'.2

end Cone

/-! ### Section data: an isotropic base point with a frame -/

section SecData

variable {m : ℕ} (Q₀ : QuadForm (𝓞 F) (m + 1))

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **Data for the adelic section**: an isotropic $e\in F^n$ and an isotropic frame for it. Fields: `e`, `e_iso`, `Z`. -/
structure ConeSecData where
  /-- The base point $e$. -/
  e : Fin (m + 1) → F
  /-- $q(e) = 0$. -/
  e_iso : qH (QF).hessian e = 0
  /-- An isotropic frame for $e$. -/
  Z : IsoFrame (QF).hessian e

namespace ConeSecData

variable {Q₀} (D : ConeSecData Q₀)

/-- $e$ at an embedding $\sigma$. -/
def eAt {K : Type*} [Field K] (σ : F →+* K) : Fin (m + 1) → K := fun i => σ (D.e i)

/-- The frame at an embedding $\sigma$. -/
def ZAt {K : Type*} [Field K] (σ : F →+* K) : IsoFrame (hesAt Q₀ σ) (D.eAt σ) := D.Z.map σ

theorem qH_eAt {K : Type*} [Field K] (σ : F →+* K) : qH (hesAt Q₀ σ) (D.eAt σ) = 0 := by
  show qH (hesAt Q₀ σ) (fun i => σ (D.e i)) = 0
  rw [qH_hesAt_map, D.e_iso, map_zero]

/-- $e$ as an adelic vector. -/
abbrev eAd : AdeleSpace F (Fin (m + 1)) := diagVec F (Fin (m + 1)) D.e

theorem adR_eAd (w : {w : InfinitePlace F // w.IsReal}) : adR D.eAd w = D.eAt (σR w) := rfl
theorem adC_eAd (w : {w : InfinitePlace F // w.IsComplex}) : adC D.eAd w = D.eAt (σC w) := rfl
theorem adV_eAd (v : HeightOneSpectrum (𝓞 F)) : adV D.eAd v = D.eAt (σV v) := rfl

section Local

variable {K : Type*} [NormedField K] [CharZero K] (σ : F →+* K)

/-- **The local section matrix** $\tau_{x-\zeta}\tau_{\zeta-e}$, $\zeta = \zeta_{\mathrm{best}(x)}$. -/
def secM (x : Fin (m + 1) → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  coneSec2 (hesAt Q₀ σ) (D.eAt σ) ((D.ZAt σ).ζ (bestIdx (hesAt Q₀ σ) (D.ZAt σ).ζ x)) x

/-- Its inverse. -/
def secMInv (x : Fin (m + 1) → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  coneSec2Inv (hesAt Q₀ σ) (D.eAt σ) ((D.ZAt σ).ζ (bestIdx (hesAt Q₀ σ) (D.ZAt σ).ζ x)) x

variable {σ}

theorem bH_best_ne {x : Fin (m + 1) → K} (hx : x ≠ 0) :
    bH (hesAt Q₀ σ) x ((D.ZAt σ).ζ (bestIdx (hesAt Q₀ σ) (D.ZAt σ).ζ x)) ≠ 0 := by
  obtain ⟨j, hj⟩ := (D.ZAt σ).exists_bH_ne_zero (hesAt_transpose Q₀ σ) hx
  exact bH_bestIdx_ne_zero _ _ hj

theorem two_ne : (2 : K) ≠ 0 := two_ne_zero

theorem secM_mul_inv {x : Fin (m + 1) → K} (hq : qH (hesAt Q₀ σ) x = 0) (hx : x ≠ 0) :
    D.secM σ x * D.secMInv σ x = 1 ∧ D.secMInv σ x * D.secM σ x = 1 :=
  coneSec2_mul_inv (hesAt_transpose Q₀ σ) two_ne hq ((D.ZAt σ).iso _) (D.qH_eAt σ) (D.bH_best_ne hx)
    ((D.ZAt σ).pair_ne _)

/-- The local section as an invertible matrix (on the punctured cone). -/
def secGL (x : Fin (m + 1) → K) (hq : qH (hesAt Q₀ σ) x = 0) (hx : x ≠ 0) : GL (Fin (m + 1)) K :=
  ⟨D.secM σ x, D.secMInv σ x, (D.secM_mul_inv hq hx).1, (D.secM_mul_inv hq hx).2⟩

theorem isSOAt_secGL {x : Fin (m + 1) → K} (hq : qH (hesAt Q₀ σ) x = 0) (hx : x ≠ 0) :
    IsSOAt Q₀ σ (D.secGL x hq hx) :=
  coneSec2_mem (hesAt_transpose Q₀ σ) two_ne hq ((D.ZAt σ).iso _) (D.qH_eAt σ) (D.bH_best_ne hx)
    ((D.ZAt σ).pair_ne _)

/-- **$s(x)\,e = x$.** -/
theorem secGL_mulVec {x : Fin (m + 1) → K} (hq : qH (hesAt Q₀ σ) x = 0) (hx : x ≠ 0) :
    (D.secGL x hq hx).val *ᵥ D.eAt σ = x :=
  coneSec2_mulVec (hesAt_transpose Q₀ σ) two_ne hq ((D.ZAt σ).iso _) (D.qH_eAt σ) (D.bH_best_ne hx)
    ((D.ZAt σ).pair_ne _)

variable [MeasurableSpace K] [MeasurableAdd₂ K] [MeasurableSub₂ K] [MeasurableMul₂ K] [MeasurableInv K]
  [MeasurableSingletonClass K] [OpensMeasurableSpace K]

variable (σ) in
theorem measurable_secM : Measurable (D.secM σ) :=
  measurable_comp_bestIdx (hesAt Q₀ σ) (D.ZAt σ).ζ (G := fun j x => coneSec2 (hesAt Q₀ σ) (D.eAt σ) ((D.ZAt σ).ζ j) x)
    fun j => measurable_matMul (measurable_refl_comp (measurable_id.sub_const _)) measurable_const

variable (σ) in
theorem measurable_secMInv : Measurable (D.secMInv σ) :=
  measurable_comp_bestIdx (hesAt Q₀ σ) (D.ZAt σ).ζ
    (G := fun j x => coneSec2Inv (hesAt Q₀ σ) (D.eAt σ) ((D.ZAt σ).ζ j) x)
    fun j => measurable_matMul measurable_const (measurable_refl_comp (measurable_id.sub_const _))

end Local

/-! #### Integrality at good places -/

section Good

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Good places** for the section: $2$ a unit, $Y$, $\zeta_j$, $e$ integral and $B(\zeta_j, e)$ units. -/
def GoodV : Prop :=
  Valued.v (2 : Fv) = 1 ∧ (D.Z.Y.map (σV v)) ∈ intMat v ∧ (∀ j, IntVec v ((D.ZAt (σV v)).ζ j)) ∧
    IntVec v (D.eAt (σV v)) ∧ ∀ j, Valued.v (bH (hesAt Q₀ (σV v)) ((D.ZAt (σV v)).ζ j) (D.eAt (σV v))) = 1

theorem eventually_goodV : ∀ᶠ v in Filter.cofinite, D.GoodV v := by
  have hb : ∀ j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (bH (hesAt Q₀ (σV v)) ((D.ZAt (σV v)).ζ j) (D.eAt (σV v))) = 1 := fun j => by
    filter_upwards [sph_eventually_valued_eq_one (D.Z.pair_ne j)] with v hv
    rw [← hv]; congr 1
    exact bH_hesAt_map Q₀ (σV v) (D.Z.ζ j) D.e
  filter_upwards [eventually_two, eventually_map_mem_intMat D.Z.Y,
    Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr fun i => eventually_valued_le_one (D.Z.ζ j i),
    Filter.eventually_all.mpr fun i => eventually_valued_le_one (D.e i),
    Filter.eventually_all.mpr hb] with v h2 hY hζ he hbv
  exact ⟨h2, hY, fun j i => hζ j i, fun i => he i, hbv⟩

variable {D v}

theorem valued_bH_le_one {x y : Fin (m + 1) → Fv} (hx : IntVec v x) (hy : IntVec v y) :
    Valued.v (bH (hesAt Q₀ (σV v)) x y) ≤ 1 :=
  valued_dotProduct_le_one v hx (hy.mulVec v (hesAt_mem_intMat v Q₀))

/-- **At a good place a primitive isotropic vector pairs to a unit with the chosen $\zeta$.** -/
theorem valued_bH_best (hv : D.GoodV v) {x : Fin (m + 1) → Fv} (hx : PrimV v x) :
    Valued.v (bH (hesAt Q₀ (σV v)) x ((D.ZAt (σV v)).ζ (bestIdx (hesAt Q₀ (σV v)) (D.ZAt (σV v)).ζ x))) = 1 := by
  have hle : ∀ j, Valued.v (bH (hesAt Q₀ (σV v)) x ((D.ZAt (σV v)).ζ j)) ≤ 1 := fun j =>
    valued_bH_le_one hx.1 (hv.2.2.1 j)
  -- some pairing is a unit
  have hex : ∃ j, Valued.v (bH (hesAt Q₀ (σV v)) x ((D.ZAt (σV v)).ζ j)) = 1 := by
    by_contra h
    push Not at h
    have hlt : ∀ j, Valued.v (bH (hesAt Q₀ (σV v)) x ((D.ZAt (σV v)).ζ j)) < 1 := fun j =>
      lt_of_le_of_ne (hle j) (h j)
    obtain ⟨i, hi⟩ := hx.2
    have h1 := lt_one_mulVec v hv.2.1 hlt i
    have h2 := (D.ZAt (σV v)).eq_Y_mulVec (hesAt_transpose Q₀ (σV v)) x
    have h3 : (D.ZAt (σV v)).Y = D.Z.Y.map (σV v) := rfl
    rw [← h3, h2, hi] at h1
    exact lt_irrefl _ h1
  obtain ⟨j, hj⟩ := hex
  refine le_antisymm (hle _) ?_
  have := bestIdx_spec (hesAt Q₀ (σV v)) (D.ZAt (σV v)).ζ x j
  rw [Valued.toNormedField.norm_le_iff, hj] at this
  exact this

theorem secM_mem_intMat (hv : D.GoodV v) {x : Fin (m + 1) → Fv} (hx : PrimV v x)
    (hq : qH (hesAt Q₀ (σV v)) x = 0) :
    D.secM (σV v) x ∈ intMat v ∧ D.secMInv (σV v) x ∈ intMat v := by
  have hH := hesAt_mem_intMat v Q₀
  have hHs := hesAt_transpose Q₀ (σV v)
  have hζi : IntVec v ((D.ZAt (σV v)).ζ (bestIdx (hesAt Q₀ (σV v)) (D.ZAt (σV v)).ζ x)) := hv.2.2.1 _
  have h1 : refl (hesAt Q₀ (σV v)) (x - (D.ZAt (σV v)).ζ (bestIdx (hesAt Q₀ (σV v)) (D.ZAt (σV v)).ζ x)) ∈
      intMat v := by
    refine refl_mem_intMat v hH (hx.1.sub v hζi) ?_
    rw [qH_sub_of_iso hHs hq ((D.ZAt (σV v)).iso _), Valuation.map_mul, Valuation.map_neg, hv.1,
      valued_bH_best hv hx, one_mul]
  have h2 : refl (hesAt Q₀ (σV v)) ((D.ZAt (σV v)).ζ (bestIdx (hesAt Q₀ (σV v)) (D.ZAt (σV v)).ζ x) -
      D.eAt (σV v)) ∈ intMat v := by
    refine refl_mem_intMat v hH (hζi.sub v hv.2.2.2.1) ?_
    rw [qH_sub_of_iso hHs ((D.ZAt (σV v)).iso _) (D.qH_eAt _), Valuation.map_mul, Valuation.map_neg, hv.1,
      hv.2.2.2.2, one_mul]
  exact ⟨mul_mem_intMat v h1 h2, mul_mem_intMat v h2 h1⟩

end Good

/-! #### The adelic section -/

/-- **The adelic section** $s : C(\mathbb A)\to SO(V)(\mathbb A)$, $s(y)\,e = y$. -/
def secA (y : adelicCone Q₀) : SOAdele Q₀ :=
  mkSOAdele Q₀ (fun w => D.secGL (adR y.1 w) (y.2.1 w).1 (y.2.1 w).2) (fun w => D.isSOAt_secGL _ _)
    (fun w => D.secGL (adC y.1 w) (y.2.2.1 w).1 (y.2.2.1 w).2) (fun w => D.isSOAt_secGL _ _)
    (fun v => D.secGL (adV y.1 v) (y.2.2.2.1 v).1 (y.2.2.2.1 v).2) (fun v => D.isSOAt_secGL _ _) (by
      filter_upwards [D.eventually_goodV, y.2.2.2.2] with v hv hp
      exact secM_mem_intMat hv hp (y.2.2.2.1 v).1)

@[simp] theorem matR_secA (y : adelicCone Q₀) (w) : matR Q₀ (D.secA y) w = D.secM (σR w) (adR y.1 w) := rfl
@[simp] theorem matC_secA (y : adelicCone Q₀) (w) : matC Q₀ (D.secA y) w = D.secM (σC w) (adC y.1 w) := rfl
@[simp] theorem matV_secA (y : adelicCone Q₀) (v) : matV Q₀ (D.secA y) v = D.secM (σV v) (adV y.1 v) := rfl

/-- **$s(y)\,e = y$.** -/
theorem secA_smul (y : adelicCone Q₀) : D.secA y • D.eAd = y.1 :=
  adeleSpace_ext (fun w => by rw [smul_apply_fst_fst, adR_eAd]; exact D.secGL_mulVec (y.2.1 w).1 (y.2.1 w).2)
    (fun w => by rw [smul_apply_fst_snd, adC_eAd]; exact D.secGL_mulVec (y.2.2.1 w).1 (y.2.2.1 w).2)
    (fun v => by rw [smul_apply_snd, adV_eAd]; exact D.secGL_mulVec (y.2.2.2.1 v).1 (y.2.2.2.1 v).2)

end ConeSecData

end SecData

/-! ### Measurability -/

section Meas

variable {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **Measurability into $SO(V)(\mathbb A)$** from measurability of the local matrices of $f(x)$ and $f(x)^{-1}$. -/
theorem measurable_SOAdele_of_mat {X : Type*} [MeasurableSpace X] {f : X → SOAdele Q₀}
    (hR1 : ∀ w, Measurable fun x => matR Q₀ (f x) w) (hR2 : ∀ w, Measurable fun x => matR Q₀ (f x)⁻¹ w)
    (hC1 : ∀ w, Measurable fun x => matC Q₀ (f x) w) (hC2 : ∀ w, Measurable fun x => matC Q₀ (f x)⁻¹ w)
    (hV1 : ∀ v, Measurable fun x => matV Q₀ (f x) v) (hV2 : ∀ v, Measurable fun x => matV Q₀ (f x)⁻¹ v) :
    Measurable f := by
  have e : f = fun x => (((f x).1.1, (f x).1.2), (f x).2) := rfl
  rw [e]
  refine Measurable.prodMk (Measurable.prodMk ((@measurable_pi_iff _ _
      (fun w : {w : InfinitePlace F // w.IsReal} => ArchSO (QRe Q₀ w)) _
      (fun w => ArchSO.instMeasurableSpace (QRe Q₀ w)) _).2 fun w => ?_)
    ((@measurable_pi_iff _ _ (fun w : {w : InfinitePlace F // w.IsComplex} => ArchSOC (QCx Q₀ w)) _
      (fun w => ArchSOC.instMeasurableSpace (QCx Q₀ w)) _).2 fun w => ?_)) ?_
  · exact measurable_archSO_of (f := fun x => (f x).1.1 w) (hR1 w) (hR2 w)
  · exact measurable_archSOC_of (f := fun x => (f x).1.2 w) (hC1 w) (hC2 w)
  · refine Measurable.subtype_mk ?_
    refine RestrictedProduct.measurable_of_forall_eval (fun v => isOpen_stdStab v QF) fun v => ?_
    exact measurable_orthGroup_of v (f := fun x => ((f x).2 : OAf QF) v) (hV1 v) (hV2 v)

/-- **Measurability of `mkSOAdele` in a parameter**, from measurability of the local matrices and their inverses. -/
theorem measurable_mkSOAdele {X : Type*} [MeasurableSpace X]
    {MR : X → ∀ w : {w : InfinitePlace F // w.IsReal}, GL (Fin n) ℝ} {hR : ∀ x w, IsSOAt Q₀ (σR w) (MR x w)}
    {MC : X → ∀ w : {w : InfinitePlace F // w.IsComplex}, GL (Fin n) ℂ} {hC : ∀ x w, IsSOAt Q₀ (σC w) (MC x w)}
    {MV : X → ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F)} {hV : ∀ x v, IsSOAt Q₀ (σV v) (MV x v)}
    {hint : ∀ x, ∀ᶠ v in Filter.cofinite, (MV x v).val ∈ intMat v ∧ (MV x v)⁻¹.val ∈ intMat v}
    (hR1 : ∀ w, Measurable fun x => (MR x w).val) (hR2 : ∀ w, Measurable fun x => (MR x w)⁻¹.val)
    (hC1 : ∀ w, Measurable fun x => (MC x w).val) (hC2 : ∀ w, Measurable fun x => (MC x w)⁻¹.val)
    (hV1 : ∀ v, Measurable fun x => (MV x v).val) (hV2 : ∀ v, Measurable fun x => (MV x v)⁻¹.val) :
    Measurable fun x => mkSOAdele Q₀ (MR x) (hR x) (MC x) (hC x) (MV x) (hV x) (hint x) := by
  refine Measurable.prodMk (Measurable.prodMk ((@measurable_pi_iff _ _
      (fun w : {w : InfinitePlace F // w.IsReal} => ArchSO (QRe Q₀ w)) _
      (fun w => ArchSO.instMeasurableSpace (QRe Q₀ w)) _).2 fun w => ?_)
    ((@measurable_pi_iff _ _ (fun w : {w : InfinitePlace F // w.IsComplex} => ArchSOC (QCx Q₀ w)) _
      (fun w => ArchSOC.instMeasurableSpace (QCx Q₀ w)) _).2 fun w => ?_)) ?_
  · exact measurable_archSO_of (f := fun x => (mkSOAdele Q₀ (MR x) (hR x) (MC x) (hC x) (MV x) (hV x) (hint x)).1.1 w)
      (hR1 w) (hR2 w)
  · exact measurable_archSOC_of (f := fun x => (mkSOAdele Q₀ (MR x) (hR x) (MC x) (hC x) (MV x) (hV x) (hint x)).1.2 w)
      (hC1 w) (hC2 w)
  · refine Measurable.subtype_mk ?_
    refine RestrictedProduct.measurable_of_forall_eval (fun v => isOpen_stdStab v QF) fun v => ?_
    exact measurable_orthGroup_of v (f := fun x =>
      ((mkSOAdele Q₀ (MR x) (hR x) (MC x) (hC x) (MV x) (hV x) (hint x)).2 : OAf QF) v) (hV1 v) (hV2 v)

/-- **The orbit map** $g\mapsto g\,y$ is measurable. -/
theorem measurable_smul_const (y : AdeleSpace F (Fin n)) : Measurable fun g : SOAdele Q₀ => g • y := by
  refine measurable_pi_iff.2 fun i => Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · refine measurable_pi_iff.2 fun w => ?_
    have : Continuous fun g : SOAdele Q₀ => matR Q₀ g w :=
      Units.continuous_val.comp ((ArchSO.continuous_incl _).comp ((continuous_apply w).comp
        (continuous_fst.comp continuous_fst)))
    exact ((continuous_apply i).comp (this.matrix_mulVec continuous_const)).measurable
  · refine measurable_pi_iff.2 fun w => ?_
    have : Continuous fun g : SOAdele Q₀ => matC Q₀ g w :=
      Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply w).comp
        (continuous_snd.comp continuous_fst)))
    exact ((continuous_apply i).comp (this.matrix_mulVec continuous_const)).measurable
  · refine RestrictedProduct.measurable_of_forall_eval (fun v => isOpen_adicCompletionIntegers v) fun v => ?_
    have : Continuous fun g : SOAdele Q₀ => matV Q₀ g v :=
      Units.continuous_val.comp (continuous_subtype_val.comp ((RestrictedProduct.continuous_eval v).comp
        (continuous_subtype_val.comp continuous_snd)))
    exact ((continuous_apply i).comp (this.matrix_mulVec continuous_const)).measurable

theorem measurableSet_stabP (y : AdeleSpace F (Fin n)) :
    MeasurableSet ((MulAction.stabilizer (SOAdele Q₀) y : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)) :=
  (measurable_smul_const Q₀ y) (measurableSet_singleton y)

instance standardBorel_stabilizer (y : AdeleSpace F (Fin n)) :
    StandardBorelSpace (MulAction.stabilizer (SOAdele Q₀) y) := by
  have := polishSpace_of_isTopologicalGroup (SOAdele Q₀)
  exact (measurableSet_stabP Q₀ y).standardBorel

end Meas

/-! ### The orbit coordinates $C(\mathbb A)\times P\simeq SO(V)(\mathbb A)$ -/

namespace ConeSecData

variable {m : ℕ} {Q₀ : QuadForm (𝓞 F) (m + 1)} (D : ConeSecData Q₀)

theorem e_ne_zero : D.e ≠ 0 := by
  intro h
  have := D.Z.pair_ne 0
  apply this
  simp only [bH, h, mulVec_zero, dotProduct_zero]

theorem eAt_ne_zero {K : Type*} [Field K] (σ : F →+* K) : D.eAt σ ≠ 0 := by
  intro h
  apply D.e_ne_zero
  funext i
  have := congrFun h i
  simpa [eAt] using this

/-- **$e\in C(\mathbb A)$.** -/
theorem eAd_mem : D.eAd ∈ adelicCone Q₀ := by
  refine ⟨fun w => ⟨D.qH_eAt _, D.eAt_ne_zero (σR w)⟩, fun w => ⟨D.qH_eAt _, D.eAt_ne_zero (σC w)⟩,
    fun v => ⟨D.qH_eAt _, D.eAt_ne_zero (σV v)⟩, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, D.e i ≠ 0 := by
    by_contra h; push Not at h; exact D.e_ne_zero (funext h)
  filter_upwards [sph_eventually_valued_eq_one hi,
    Filter.eventually_all.mpr fun j => eventually_valued_le_one (D.e j)] with v hv hle
  exact ⟨fun j => hle j, i, hv⟩

/-- The stabilizer $P$ of $e$ in $SO(V)(\mathbb A)$. -/
abbrev P : Subgroup (SOAdele Q₀) := MulAction.stabilizer (SOAdele Q₀) D.eAd

/-- **The orbit coordinates** $(y, p)\mapsto p\,s(y)^{-1}$. -/
def coordFun (p : adelicCone Q₀ × D.P) : SOAdele Q₀ := (p.2 : SOAdele Q₀) * (D.secA p.1)⁻¹

theorem coordFun_inv_smul (p : adelicCone Q₀ × D.P) : (D.coordFun p)⁻¹ • D.eAd = p.1.1 := by
  have hp : (p.2 : SOAdele Q₀) • D.eAd = D.eAd := p.2.2
  rw [coordFun, _root_.mul_inv_rev, inv_inv, mul_smul, inv_smul_eq_iff.mpr hp.symm, D.secA_smul]

theorem coordFun_mul (x : adelicCone Q₀) (p p' : D.P) :
    D.coordFun (x, p' * p) = (p' : SOAdele Q₀) * D.coordFun (x, p) := by
  simp only [coordFun, Subgroup.coe_mul, mul_assoc]

theorem coordFun_injective : Function.Injective D.coordFun := by
  rintro ⟨x, p⟩ ⟨x', p'⟩ e
  have hx : x = x' := Subtype.ext (by rw [← D.coordFun_inv_smul (x, p), ← D.coordFun_inv_smul (x', p'), e])
  subst hx
  simp only [coordFun, mul_left_inj] at e
  rw [Subtype.ext e]

theorem coordFun_surjective : Function.Surjective D.coordFun := by
  intro g
  set x : adelicCone Q₀ := ⟨g⁻¹ • D.eAd, smul_mem_adelicCone Q₀ g⁻¹ D.eAd_mem⟩
  have hfix : (g * D.secA x) • D.eAd = D.eAd := by rw [mul_smul, D.secA_smul, smul_inv_smul]
  exact ⟨(x, ⟨g * D.secA x, hfix⟩), by rw [coordFun, mul_inv_cancel_right]⟩

theorem measurable_secA : Measurable D.secA := by
  refine measurable_mkSOAdele Q₀ (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun v => ?_) (fun v => ?_)
  · exact (D.measurable_secM (σR w)).comp ((continuous_adR w).measurable.comp measurable_subtype_coe)
  · exact (D.measurable_secMInv (σR w)).comp ((continuous_adR w).measurable.comp measurable_subtype_coe)
  · exact (D.measurable_secM (σC w)).comp ((continuous_adC w).measurable.comp measurable_subtype_coe)
  · exact (D.measurable_secMInv (σC w)).comp ((continuous_adC w).measurable.comp measurable_subtype_coe)
  · exact (D.measurable_secM (σV v)).comp ((continuous_adV v).measurable.comp measurable_subtype_coe)
  · exact (D.measurable_secMInv (σV v)).comp ((continuous_adV v).measurable.comp measurable_subtype_coe)

theorem measurable_coordFun : Measurable D.coordFun :=
  (measurable_subtype_coe.comp measurable_snd).mul (D.measurable_secA.comp measurable_fst).inv

/-- **The orbit coordinates as a measurable equivalence** (Lusin–Souslin). -/
def coordEquiv : adelicCone Q₀ × D.P ≃ᵐ SOAdele Q₀ where
  toEquiv := Equiv.ofBijective D.coordFun ⟨D.coordFun_injective, D.coordFun_surjective⟩
  measurable_toFun := D.measurable_coordFun
  measurable_invFun := by
    have := polishSpace_of_isTopologicalGroup (SOAdele Q₀)
    have hemb := D.measurable_coordFun.measurableEmbedding D.coordFun_injective
    intro A hA
    have : (Equiv.ofBijective D.coordFun ⟨D.coordFun_injective, D.coordFun_surjective⟩).symm ⁻¹' A =
        D.coordFun '' A := by
      ext g
      simp only [mem_preimage, mem_image]
      constructor
      · intro hg
        exact ⟨_, hg, Equiv.ofBijective_apply_symm_apply _ _ _⟩
      · rintro ⟨p, hp, rfl⟩
        convert hp; exact Equiv.ofBijective_symm_apply_apply _ _ p
    rw [this]
    exact hemb.measurableSet_image.mpr hA

theorem coordEquiv_apply (p : adelicCone Q₀ × D.P) : D.coordEquiv p = D.coordFun p := rfl

end ConeSecData

end QuadFormsKB.Tamagawa.Measure.Weil

end
