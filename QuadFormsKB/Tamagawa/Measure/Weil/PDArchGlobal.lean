import QuadFormsKB.Tamagawa.Measure.Weil.PDArchComplex
import QuadFormsKB.Tamagawa.Measure.Weil.PDCentre
import QuadFormsKB.Tamagawa.Measure.Weil.PDTamagawa

/-!
# Weil's measure on $PD^\times(\mathbb A)$ against the Tamagawa measure of $SO(V)$, every number field

**Layer:** $F$ a number field, $a, b\in\mathcal O_F\setminus0$, $D = (a,b)_F$ (any signature), $V = (D^0,\operatorname{nrd})$.

Weil's measure `muPD` on $PD^\times(\mathbb A) = (D\otimes\mathbb A)^\times/\mathbb A^\times$ (the quotient of `tamQuat` by
`tamIdeles`) is computed on the boxes $E\times J$, $E$ the image of $T(1+V)\subseteq(D\otimes F_\infty)^\times$ and $J$ the image
of $\hat\Lambda^\times$, through Weil's fibration identity `fibMeas_muPD`:

* `muFinUnits_fibre`, `omegaInf_fibre`, `muZ_fibre`: the fibres of $(D\otimes\mathbb A)^\times \to PD^\times(\mathbb A)$ over the
  box, $\omega_\infty(T)\,\mu_{G_m}(\hat{\mathcal O}^\times)\,\mathbf 1_{E\times J}$;
* `tamQuat_sAdele`: $\mathrm{tamQuat}(T(1+V)\times\hat\Lambda^\times) = \omega_\infty(T)\,\mu_{G_m}(\hat{\mathcal O}^\times)\,
  \mu_{PD}(E\times J)$.
-/

open MeasureTheory Set Metric Filter Topology Quaternion NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta

variable {F : Type} [Field F] [NumberField F] (a b : 𝓞 F)

local notation "AF" => FiniteAdeleRing (𝓞 F) F

theorem finScalar_mem_lamHatUnits_iff (c : AFˣ) :
    finScalar (a : F) (b : F) c ∈ lamHatUnits (a : F) (b : F) ↔ c ∈ OHatUnits F := by
  have h0 : (0 : AF) ∈ OHat := fun v => zero_mem _
  have hinv : ((finScalar (a : F) (b : F) c)⁻¹ : (QuatFin (a : F) (b : F))ˣ) = finScalar (a : F) (b : F) c⁻¹ :=
    (map_inv _ c).symm
  simp only [lamHatUnits, mem_setOf_eq, lamHat, hinv]
  simp [finScalar, h0, OHatUnits]

/-- The image $J$ of $\hat\Lambda^\times$ in $PD^\times(\mathbb A_f)$. -/
def lamImgFin : Set (PDFin a b) := (QuotientGroup.mk : (QuatFin (a : F) (b : F))ˣ → PDFin a b) '' lamHatUnits (a : F) (b : F)

/-- **The finite fibre**: $\mu_{G_m}\{u : g u \in \hat\Lambda^\times\} = \mu_{G_m}(\hat{\mathcal O}^\times)\,\mathbf 1_J([g])$. -/
theorem muFinUnits_fibre (g : (QuatFin (a : F) (b : F))ˣ) :
    muFinUnits F {u | g * finScalar (a : F) (b : F) u ∈ lamHatUnits (a : F) (b : F)} =
      (lamImgFin a b).indicator (fun _ => muFinUnits F (OHatUnits F)) (QuotientGroup.mk g) := by
  by_cases h : ∃ u₀, g * finScalar (a : F) (b : F) u₀ ∈ lamHatUnits (a : F) (b : F)
  · obtain ⟨u₀, hu₀⟩ := h
    have hmem : (QuotientGroup.mk g : PDFin a b) ∈ lamImgFin a b := by
      refine ⟨_, hu₀, ?_⟩
      rw [QuotientGroup.eq]
      refine ⟨u₀⁻¹, ?_⟩
      simp [mul_assoc, map_inv]
    rw [indicator_of_mem hmem]
    have hset : {u | g * finScalar (a : F) (b : F) u ∈ lamHatUnits (a : F) (b : F)} =
        (fun u => u₀⁻¹ * u) ⁻¹' (OHatUnits F : Set AFˣ) := by
      ext u
      simp only [mem_setOf_eq, mem_preimage, SetLike.mem_coe]
      rw [← finScalar_mem_lamHatUnits_iff a b]
      have hsub := lamHatSub a b
      constructor
      · intro hu
        have : (g * finScalar (a : F) (b : F) u₀)⁻¹ * (g * finScalar (a : F) (b : F) u) ∈ lamHatSub a b :=
          (lamHatSub a b).mul_mem ((lamHatSub a b).inv_mem hu₀) hu
        show _ ∈ lamHatSub a b
        rw [map_mul, map_inv]
        simpa [mul_assoc] using this
      · intro hu
        have : (g * finScalar (a : F) (b : F) u₀) * finScalar (a : F) (b : F) (u₀⁻¹ * u) ∈ lamHatSub a b :=
          (lamHatSub a b).mul_mem hu₀ hu
        show _ ∈ lamHatSub a b
        rw [map_mul, map_inv] at this
        simpa [mul_assoc] using this
    rw [hset, measure_preimage_mul]
  · push Not at h
    have hnot : (QuotientGroup.mk g : PDFin a b) ∉ lamImgFin a b := by
      rintro ⟨x, hx, hxg⟩
      rw [QuotientGroup.eq] at hxg
      obtain ⟨u, hu⟩ := hxg
      apply h u⁻¹
      have hg : g = x * finScalar (a : F) (b : F) u := by rw [hu, mul_inv_cancel_left]
      rw [hg, map_inv, mul_inv_cancel_right]; exact hx
    rw [indicator_of_notMem hnot]
    have : {u | g * finScalar (a : F) (b : F) u ∈ lamHatUnits (a : F) (b : F)} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun u hu => h u hu
    rw [this, measure_empty]

/-! ### The archimedean fibre -/

/-- The pure quaternion $y_0i + y_1j + y_2k$ of $D\otimes F_\infty$. -/
def pureI (y : Fin 3 → mixedSpace F) : QuatInf (a : F) (b : F) := ⟨0, y 0, y 1, y 2⟩

/-- **The box** $T\cdot(1 + V) \subseteq (D\otimes F_\infty)^\times$. -/
def sInf (T : Set (mixedSpace F)ˣ) (V : Set (Fin 3 → mixedSpace F)) : Set (QuatInf (a : F) (b : F))ˣ :=
  {x | ∃ t ∈ T, ∃ y ∈ V, (x : QuatInf (a : F) (b : F)) =
    algebraMap (mixedSpace F) (QuatInf (a : F) (b : F)) (t : mixedSpace F) * (1 + pureI a b y)}

theorem smul_one_add_pureI_inj {s t : (mixedSpace F)ˣ} {y y' : Fin 3 → mixedSpace F}
    (h : algebraMap (mixedSpace F) (QuatInf (a : F) (b : F)) (s : mixedSpace F) * (1 + pureI a b y) =
      algebraMap (mixedSpace F) (QuatInf (a : F) (b : F)) (t : mixedSpace F) * (1 + pureI a b y')) :
    s = t ∧ y = y' := by
  have hre := congrArg QuaternionAlgebra.re h
  have hI := congrArg QuaternionAlgebra.imI h
  have hJ := congrArg QuaternionAlgebra.imJ h
  have hK := congrArg QuaternionAlgebra.imK h
  simp [pureI, Algebra.algebraMap_eq_smul_one] at hre hI hJ hK
  have hst : s = t := Units.ext hre
  subst hst
  refine ⟨rfl, ?_⟩
  funext i
  fin_cases i
  · exact s.isUnit.mul_left_cancel hI
  · exact s.isUnit.mul_left_cancel hJ
  · exact s.isUnit.mul_left_cancel hK

theorem val_infScalar (c : (mixedSpace F)ˣ) :
    ((infScalar (a : F) (b : F) c : (QuatInf (a : F) (b : F))ˣ) : QuatInf (a : F) (b : F)) =
      algebraMap (mixedSpace F) (QuatInf (a : F) (b : F)) (c : mixedSpace F) := rfl

/-- **The archimedean fibre**: $\omega_\infty\{u : g u \in T(1+V)\} = \omega_\infty(T)\,\mathbf 1_{[T(1+V)]}([g])$. -/
theorem omegaInf_fibre (T : Set (mixedSpace F)ˣ) (V : Set (Fin 3 → mixedSpace F))
    (g : (QuatInf (a : F) (b : F))ˣ) :
    omegaInf F {u | g * infScalar (a : F) (b : F) u ∈ sInf a b T V} =
      ((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V).indicator
        (fun _ => omegaInf F T) (QuotientGroup.mk g) := by
  by_cases h : ∃ u₀, g * infScalar (a : F) (b : F) u₀ ∈ sInf a b T V
  · obtain ⟨u₀, t₀, ht₀, y₀, hy₀, hg⟩ := h
    have hmem : (QuotientGroup.mk g : PDInf a b) ∈
        (QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V := by
      refine ⟨_, ⟨t₀, ht₀, y₀, hy₀, hg⟩, ?_⟩
      rw [QuotientGroup.eq]
      refine ⟨u₀⁻¹, ?_⟩
      simp [mul_assoc, map_inv]
    rw [indicator_of_mem hmem]
    have hgu : ∀ u, ((g * infScalar (a : F) (b : F) u : (QuatInf (a : F) (b : F))ˣ) : QuatInf (a : F) (b : F)) =
        algebraMap (mixedSpace F) (QuatInf (a : F) (b : F)) ((t₀ * u₀⁻¹ * u : (mixedSpace F)ˣ) : mixedSpace F) *
          (1 + pureI a b y₀) := by
      intro u
      have : g * infScalar (a : F) (b : F) u =
          (g * infScalar (a : F) (b : F) u₀) * infScalar (a : F) (b : F) (u₀⁻¹ * u) := by
        rw [map_mul, map_inv]; group
      rw [this, Units.val_mul, hg, val_infScalar]
      simp only [Units.val_mul, map_mul]
      rw [← map_mul, mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, ← map_mul, ← map_mul]
      congr 2
      ring
    have hset : {u | g * infScalar (a : F) (b : F) u ∈ sInf a b T V} = (fun u => (t₀ * u₀⁻¹) * u) ⁻¹' T := by
      ext u
      simp only [mem_setOf_eq, mem_preimage, sInf]
      constructor
      · rintro ⟨t, ht, y, hy, h'⟩
        rw [hgu] at h'
        have := (smul_one_add_pureI_inj a b h').1
        rw [this]; exact ht
      · intro hu
        exact ⟨_, hu, y₀, hy₀, hgu u⟩
    rw [hset, measure_preimage_mul]
  · push Not at h
    have hnot : (QuotientGroup.mk g : PDInf a b) ∉
        (QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V := by
      rintro ⟨x, hx, hxg⟩
      rw [QuotientGroup.eq] at hxg
      obtain ⟨u, hu⟩ := hxg
      apply h u⁻¹
      have hg : g = x * infScalar (a : F) (b : F) u := by rw [hu, mul_inv_cancel_left]
      rw [hg, map_inv, mul_inv_cancel_right]; exact hx
    rw [indicator_of_notMem hnot]
    have : {u | g * infScalar (a : F) (b : F) u ∈ sInf a b T V} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun u hu => h u hu
    rw [this, measure_empty]

/-! ### Measurability of the box -/

/-- The parametrization $(t, y) \mapsto t(1+y)$ of the box. -/
def boxMap (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) : QuatInf (a : F) (b : F) :=
  algebraMap (mixedSpace F) (QuatInf (a : F) (b : F)) (p.1 : mixedSpace F) * (1 + pureI a b p.2)

theorem boxMap_re (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) : (boxMap a b p).re = p.1 := by
  simp [boxMap, pureI]
theorem boxMap_imI (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) : (boxMap a b p).imI = p.1 * p.2 0 := by
  simp [boxMap, pureI]
theorem boxMap_imJ (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) : (boxMap a b p).imJ = p.1 * p.2 1 := by
  simp [boxMap, pureI]
theorem boxMap_imK (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) : (boxMap a b p).imK = p.1 * p.2 2 := by
  simp [boxMap, pureI]

theorem continuous_boxMap : Continuous (boxMap a b) := by
  have hv : Continuous fun p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F) => (p.1 : mixedSpace F) :=
    Units.continuous_val.comp continuous_fst
  have hy : ∀ i, Continuous fun p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F) => p.2 i :=
    fun i => (continuous_apply i).comp continuous_snd
  refine (continuous_quatInf_iff (a : F) (b : F)).2 ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [boxMap_re]; exact hv
  · simp_rw [boxMap_imI]; exact hv.mul (hy 0)
  · simp_rw [boxMap_imJ]; exact hv.mul (hy 1)
  · simp_rw [boxMap_imK]; exact hv.mul (hy 2)

instance : PolishSpace (mixedSpace F)ˣ := polishSpace_of_isTopologicalGroup _

instance instPolishFin3Mixed : PolishSpace (Fin 3 → mixedSpace F) where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := inferInstance

instance : PolishSpace ((mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := inferInstance

theorem measurableSet_sInf {T : Set (mixedSpace F)ˣ} {V : Set (Fin 3 → mixedSpace F)} (hT : MeasurableSet T)
    (hV : MeasurableSet V) : MeasurableSet (sInf a b T V) := by
  have himg : MeasurableSet (boxMap a b '' (T ×ˢ V)) :=
    (hT.prod hV).image_of_continuousOn_injOn (continuous_boxMap a b).continuousOn fun p _ q _ h => by
      obtain ⟨h1, h2⟩ := smul_one_add_pureI_inj a b h
      exact Prod.ext h1 h2
  have : sInf a b T V = Units.val ⁻¹' (boxMap a b '' (T ×ˢ V)) := by
    ext x
    simp only [sInf, mem_setOf_eq, mem_preimage, mem_image, boxMap, Prod.exists, mem_prod]
    constructor
    · rintro ⟨t, ht, y, hy, h⟩; exact ⟨t, y, ⟨ht, hy⟩, h.symm⟩
    · rintro ⟨t, y, ⟨ht, hy⟩, h⟩; exact ⟨t, ht, y, hy, h.symm⟩
  rw [this]
  exact himg.preimage Units.continuous_val.measurable

/-! ### The global fibre and `tamQuat` on the box -/

theorem quatUnitsEquiv_mul_quatScalar (g : (QuatAdele (a : F) (b : F))ˣ) (u : (Adeles F)ˣ) :
    quatUnitsEquiv (a : F) (b : F) (g * quatScalar (a : F) (b : F) u) =
      ((quatUnitsEquiv (a : F) (b : F) g).1 * infScalar (a : F) (b : F) (idelesEquiv F u).1,
        (quatUnitsEquiv (a : F) (b : F) g).2 * finScalar (a : F) (b : F) (idelesEquiv F u).2) := by
  rw [map_mul, quatUnitsEquiv_quatScalar]; rfl

/-- The adelic box $T(1+V)\times\hat\Lambda^\times$. -/
def sAdele (T : Set (mixedSpace F)ˣ) (V : Set (Fin 3 → mixedSpace F)) : Set (QuatAdele (a : F) (b : F))ˣ :=
  quatUnitsEquiv (a : F) (b : F) ⁻¹' (sInf a b T V ×ˢ lamHatUnits (a : F) (b : F))

variable {a b} in
theorem pdSplit_mk (ha : a ≠ 0) (hb : b ≠ 0) (g : (QuatAdele (a : F) (b : F))ˣ) :
    pdSplit a b ha hb (QuotientGroup.mk g) =
      (QuotientGroup.mk (quatUnitsEquiv (a : F) (b : F) g).1, QuotientGroup.mk (quatUnitsEquiv (a : F) (b : F) g).2) := by
  rw [pdSplit, ContinuousMulEquiv.trans_apply, pdAdeleEquiv_mk, ContinuousMulEquiv.symm_apply_eq]
  rfl

variable {a b} in
/-- **The global fibre**: $\mu_Z\{z : gz \in T(1+V)\times\hat\Lambda^\times\} =
\omega_\infty(T)\,\mu_{G_m}(\hat{\mathcal O}^\times)\,\mathbf 1_{E\times J}(\mathrm{pdSplit}[g])$. -/
theorem muZ_fibre (ha : a ≠ 0) (hb : b ≠ 0) (T : Set (mixedSpace F)ˣ) (V : Set (Fin 3 → mixedSpace F))
    (g : (QuatAdele (a : F) (b : F))ˣ) :
    muZ (a : F) (b : F) ((fun k : (pdMk (a : F) (b : F)).ker => g * (k : (QuatAdele (a : F) (b : F))ˣ)) ⁻¹'
        sAdele a b T V) =
      (pdSplit a b ha hb ⁻¹' (((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V) ×ˢ
        lamImgFin a b)).indicator (fun _ => omegaInf F T * muFinUnits F (OHatUnits F)) (QuotientGroup.mk g) := by
  set e1 := (kerEquiv (a : F) (b : F)).toHomeomorph.toMeasurableEquiv
  set e2 := (idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv
  have hmuZ : muZ (a : F) (b : F) = (tamIdeles F).map e1 := rfl
  have htam : tamIdeles F = ((omegaInf F).prod (muFinUnits F)).map e2 := rfl
  set q := quatUnitsEquiv (a : F) (b : F) g
  have hset : e2 ⁻¹' (e1 ⁻¹' ((fun k : (pdMk (a : F) (b : F)).ker => g * (k : (QuatAdele (a : F) (b : F))ˣ)) ⁻¹'
      sAdele a b T V)) = {u | q.1 * infScalar (a : F) (b : F) u ∈ sInf a b T V} ×ˢ
        {u | q.2 * finScalar (a : F) (b : F) u ∈ lamHatUnits (a : F) (b : F)} := by
    ext ⟨u, w⟩
    simp only [mem_preimage, sAdele, mem_prod, mem_setOf_eq]
    have : ((e1 (e2 (u, w)) : (pdMk (a : F) (b : F)).ker) : (QuatAdele (a : F) (b : F))ˣ) =
        quatScalar (a : F) (b : F) ((idelesEquiv F).symm (u, w)) := rfl
    rw [this, quatUnitsEquiv_mul_quatScalar]
    simp [e2, q]
  rw [hmuZ, MeasurableEquiv.map_apply, htam, MeasurableEquiv.map_apply, hset, Measure.prod_prod,
    omegaInf_fibre, muFinUnits_fibre]
  have hps := pdSplit_mk ha hb g
  by_cases h1 : (QuotientGroup.mk q.1 : PDInf a b) ∈
      (QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V <;>
  by_cases h2 : (QuotientGroup.mk q.2 : PDFin a b) ∈ lamImgFin a b <;>
  simp [indicator, h1, h2, q, mem_preimage, hps]

theorem measurableSet_sAdele {T : Set (mixedSpace F)ˣ} {V : Set (Fin 3 → mixedSpace F)} (hT : MeasurableSet T)
    (hV : MeasurableSet V) : MeasurableSet (sAdele a b T V) :=
  ((measurableSet_sInf a b hT hV).prod (isOpen_lamHatUnits (a : F) (b : F)).measurableSet).preimage
    (quatUnitsEquiv (a : F) (b : F)).continuous.measurable

variable {a b} in
/-- **`tamQuat` on the box through Weil's fibration** (`fibMeas_muPD`):
$\mathrm{tamQuat}(T(1+V)\times\hat\Lambda^\times) = \omega_\infty(T)\,\mu_{G_m}(\hat{\mathcal O}^\times)\,
\mu_{PD}(\mathrm{pdSplit}^{-1}(E\times J))$. -/
theorem tamQuat_sAdele (ha : a ≠ 0) (hb : b ≠ 0) {T : Set (mixedSpace F)ˣ} {V : Set (Fin 3 → mixedSpace F)}
    (hT : MeasurableSet T) (hV : MeasurableSet V)
    (hE : MeasurableSet ((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V)) :
    tamQuat (a : F) (b : F) (sAdele a b T V) = omegaInf F T * muFinUnits F (OHatUnits F) *
      muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)
        (pdSplit a b ha hb ⁻¹' (((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V) ×ˢ
          lamImgFin a b)) := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  have hb' : (b : F) ≠ 0 := by simpa using hb
  have hJ : MeasurableSet (lamImgFin a b) :=
    (QuotientGroup.isOpenMap_coe _ (isOpen_lamHatUnits (a : F) (b : F))).measurableSet
  have hP : MeasurableSet (pdSplit a b ha hb ⁻¹' (((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) ''
      sInf a b T V) ×ˢ lamImgFin a b)) := (hE.prod hJ).preimage (pdSplit a b ha hb).continuous.measurable
  rw [← fibMeas_muPD (valued_coe_le_one a) (valued_coe_le_one b) ha' hb',
    NormalFib.fibMeas_apply _ _ (measurable_pdMk _ _) _ _ (measurableSet_sAdele a b hT hV),
    ← lintegral_indicator_const hP]
  refine lintegral_congr fun q => ?_
  obtain ⟨g, rfl⟩ := pdMk_surjective (a : F) (b : F) q
  rw [NormalFib.kern_apply_N, NormalFib.fibK_apply _ _ _ (measurableSet_sAdele a b hT hV), muZ_fibre ha hb]
  rfl

/-! ### Haar uniqueness on $PD^\times(\mathbb A)$ and the box identity -/

local notation "Q₀" => pureFormO a b

theorem isFiniteMeasureOnCompacts_map_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (e : X ≃ₜ Y) : IsFiniteMeasureOnCompacts (μ.map e) :=
  ⟨fun K hK => by
    have : (μ.map e) K = μ (e ⁻¹' K) := e.toMeasurableEquiv.map_apply K
    rw [this]
    exact (e.isCompact_preimage.mpr hK).measure_lt_top⟩

variable {a b} in
/-- The reference product measure $\nu_\infty\times\mu_{PD,f}$ on $PD^\times(F_\infty)\times PD^\times(\mathbb A_f)$, with
$\nu_\infty$ the transport of $\mu^{\mathrm{Tam}}_\infty$ and $\mu_{PD,f}$ = `muPDFin`. -/
def nuRef (ha : a ≠ 0) (hb : b ≠ 0) : Measure (PDInf a b × PDFin a b) :=
  ((muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb)).map (pdInfEquiv a b ha hb).symm).prod (muPDFin ha hb)

variable {a b} in
theorem isMulLeftInvariant_nuRef (ha : a ≠ 0) (hb : b ≠ 0) : (nuRef ha hb).IsMulLeftInvariant := by
  have h1 : (Measure.map (⇑(pdInfEquiv a b ha hb).symm)
      (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb))).IsMulLeftInvariant :=
    isMulLeftInvariant_map (μ := muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb))
      (pdInfEquiv a b ha hb).symm.toMulEquiv.toMonoidHom.toMulHom (pdInfEquiv a b ha hb).symm.continuous.measurable
      (pdInfEquiv a b ha hb).symm.surjective
  unfold nuRef; infer_instance

open scoped Classical in
variable {a b} in
theorem isFiniteMeasureOnCompacts_muArchTamSO_pure (ha : a ≠ 0) (hb : b ≠ 0) :
    IsFiniteMeasureOnCompacts (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb)) := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have := LerayArch.isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ) (gramDetC_QCx_ne_zero Q₀ hQ)
  unfold muArchTamSO LerayArch.muArchNF
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top

variable {a b} in
theorem isFiniteMeasureOnCompacts_muPDFin (ha : a ≠ 0) (hb : b ≠ 0) :
    IsFiniteMeasureOnCompacts (muPDFin ha hb) := by
  have : IsFiniteMeasureOnCompacts (QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1)) := by
    unfold QuadFormsKB.Tamagawa.Measure.muFin; infer_instance
  have := isFiniteMeasureOnCompacts_map_homeomorph (QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1))
    (pdFinEquiv a b ha hb).symm.toHomeomorph
  unfold muPDFin
  exact IsFiniteMeasureOnCompacts.smul _ (rF_ne_top ha hb)

variable {a b} in
theorem isFiniteMeasureOnCompacts_nuRef (ha : a ≠ 0) (hb : b ≠ 0) : IsFiniteMeasureOnCompacts (nuRef ha hb) := by
  have := isFiniteMeasureOnCompacts_muArchTamSO_pure ha hb
  have := isFiniteMeasureOnCompacts_map_homeomorph (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb))
    (pdInfEquiv a b ha hb).symm.toHomeomorph
  have := isFiniteMeasureOnCompacts_muPDFin ha hb
  unfold nuRef
  infer_instance

variable {a b} in
/-- **Haar uniqueness**: the reference measure pulled back to $PD^\times(\mathbb A)$ is a constant multiple of `muPD`. -/
theorem nuRef_map_eq_smul_muPD (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c : ℝ≥0, (nuRef ha hb).map (pdSplit a b ha hb).symm =
      (c : ℝ≥0∞) • muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb) := by
  have hH := isHaarMeasure_muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha)
    (by simpa using hb)
  have := isMulLeftInvariant_nuRef ha hb
  have := isFiniteMeasureOnCompacts_nuRef ha hb
  have h1 : ((nuRef ha hb).map (pdSplit a b ha hb).symm).IsMulLeftInvariant :=
    isMulLeftInvariant_map (μ := nuRef ha hb) (pdSplit a b ha hb).symm.toMulEquiv.toMonoidHom.toMulHom
      (pdSplit a b ha hb).symm.continuous.measurable (pdSplit a b ha hb).symm.surjective
  have h2 := isFiniteMeasureOnCompacts_map_homeomorph (nuRef ha hb) (pdSplit a b ha hb).symm.toHomeomorph
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩

variable {a b} in
/-- **The box identity**: with $c$ from Haar uniqueness,
$\mu^{\mathrm{Tam}}_\infty(c_\infty(E))\cdot\omega_\infty(T) = c\cdot\omega^{D^\times}_\infty(T(1+V))$. -/
theorem box_identity (ha : a ≠ 0) (hb : b ≠ 0) (c : ℝ≥0)
    (hc : (nuRef ha hb).map (pdSplit a b ha hb).symm =
      (c : ℝ≥0∞) • muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb))
    {T : Set (mixedSpace F)ˣ} {V : Set (Fin 3 → mixedSpace F)} (hT : MeasurableSet T) (hV : MeasurableSet V)
    (hE : MeasurableSet ((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V)) :
    muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb)
        (pdInfEquiv a b ha hb '' ((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V)) *
      omegaInf F T = (c : ℝ≥0∞) * omegaQuatInf (a : F) (b : F) (sInf a b T V) := by
  set E := (QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sInf a b T V
  have hJ : MeasurableSet (lamImgFin a b) :=
    (QuotientGroup.isOpenMap_coe _ (isOpen_lamHatUnits (a : F) (b : F))).measurableSet
  have hP : MeasurableSet (pdSplit a b ha hb ⁻¹' (E ×ˢ lamImgFin a b)) :=
    (hE.prod hJ).preimage (pdSplit a b ha hb).continuous.measurable
  -- the left side through `nuRef`
  have hL : ((nuRef ha hb).map (pdSplit a b ha hb).symm) (pdSplit a b ha hb ⁻¹' (E ×ˢ lamImgFin a b)) =
      muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) (pdInfEquiv a b ha hb '' E) * cPD a b := by
    have hm : ((nuRef ha hb).map (pdSplit a b ha hb).symm) (pdSplit a b ha hb ⁻¹' (E ×ˢ lamImgFin a b)) =
        nuRef ha hb ((pdSplit a b ha hb).symm ⁻¹' (pdSplit a b ha hb ⁻¹' (E ×ˢ lamImgFin a b))) :=
      (pdSplit a b ha hb).symm.toHomeomorph.toMeasurableEquiv.map_apply _
    rw [hm]
    have : (pdSplit a b ha hb).symm ⁻¹' (pdSplit a b ha hb ⁻¹' (E ×ˢ lamImgFin a b)) = E ×ˢ lamImgFin a b := by
      ext p; simp
    have hmI : (Measure.map (⇑(pdInfEquiv a b ha hb).symm) (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb))) E =
        muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) ((pdInfEquiv a b ha hb).symm ⁻¹' E) :=
      (pdInfEquiv a b ha hb).symm.toHomeomorph.toMeasurableEquiv.map_apply E
    rw [this, nuRef, Measure.prod_prod, lamImgFin, muPDFin_image_lamHat ha hb, hmI]
    congr 2
    ext g
    constructor
    · intro hg; exact ⟨_, hg, by simp⟩
    · rintro ⟨x, hx, rfl⟩; simpa using hx
  rw [hc, Measure.smul_apply, smul_eq_mul] at hL
  have hbox := tamQuat_sAdele ha hb hT hV hE
  have hprod : tamQuat (a : F) (b : F) (sAdele a b T V) =
      omegaQuatInf (a : F) (b : F) (sInf a b T V) * muFinQuat (a : F) (b : F) (lamHatUnits (a : F) (b : F)) :=
    tamQuat_prod _ _
  set U := muFinUnits F (OHatUnits F)
  set Λ := muFinQuat (a : F) (b : F) (lamHatUnits (a : F) (b : F))
  have hU0 : U ≠ 0 := by simp only [U]; rw [muFinUnits_OHatUnits]; exact (ENNReal.ofReal_pos.mpr ohatVol_pos).ne'
  have hUt : U ≠ ⊤ := by simp only [U]; rw [muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top
  have hΛ0 : Λ ≠ 0 := by
    simp only [Λ]; rw [muFinQuat_lamHatUnits]
    exact (ENNReal.ofReal_pos.mpr (quatHatVol_pos (intA a) (intA b) (by exact_mod_cast ha)
      (by exact_mod_cast hb))).ne'
  have hΛt : Λ ≠ ⊤ := by simp only [Λ]; rw [muFinQuat_lamHatUnits]; exact ENNReal.ofReal_ne_top
  have hcU : cPD a b * U = Λ := ENNReal.div_mul_cancel hU0 hUt
  set M := muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) (pdInfEquiv a b ha hb '' E)
  set P := muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)
    (pdSplit a b ha hb ⁻¹' (E ×ˢ lamImgFin a b))
  have key : M * omegaInf F T * Λ = (c : ℝ≥0∞) * omegaQuatInf (a : F) (b : F) (sInf a b T V) * Λ := by
    calc M * omegaInf F T * Λ = (M * cPD a b) * (omegaInf F T * U) := by rw [← hcU]; ring
      _ = (c : ℝ≥0∞) * (omegaInf F T * U * P) := by rw [← hL]; ring
      _ = (c : ℝ≥0∞) * tamQuat (a : F) (b : F) (sAdele a b T V) := by rw [hbox]
      _ = _ := by rw [hprod]; ring
  exact (ENNReal.mul_left_inj hΛ0 hΛt).mp key

end QuadFormsKB.Tamagawa.Measure.Weil
