/-
# The reduced-norm fibration of `tamQuat`

**Layer:** a number field $F$, $\mathbb H = \mathbb H[F,a,b]$ with $a, b$ integral and nonzero, any signature.

* `nrdPos : (D⊗𝔸)^× →* A_+` (the reduced norm onto $A_+ = $ `posA a b`, the ideles positive at the ramified real places),
  surjective (`exists_nrdUnit_eq`); `kerPosEquiv : ker nrdPos ≃ₜ* SL1A`; `muSL1P` = `muSL1` on `ker nrdPos`;
  `muPosA` = `tamIdeles` restricted to $A_+$.
* **`fibMeas_nrdPos`**: $\int_{A_+}(g_a\cdot)_*\mu_{\mathrm{SL}_1}\,d\mu_{A_+}(a) = $ `tamQuat`, i.e. the Tamagawa measure of
  $(D\otimes\mathbb A)^\times$ is the fibred measure of `tamIdeles` and $\mu_{\mathrm{SL}_1}$ along $\operatorname{nrd}$ (Weil 1982,
  §2.4, Thm 2.4.4: the gauge form $\omega_{D^\times} = \omega_{\mathrm{SL}_1}\wedge\operatorname{nrd}^*(dx/x)$). `fibMeas_muSL1`
  is the norm-one version; the full version follows by splitting off $\|\operatorname{nrd}x\|$ on both sides, exactly as
  `fibMeas_muPDOne_full` does for the centre.

Source: Weil 1982, §2.4, Thm 2.4.4 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatQuat

open MeasureTheory Measure Set Function Topology NumberField
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] {a b : F}

variable (a b) in
/-- The reduced norm $(D\otimes\mathbb A)^\times\to A_+$. -/
def nrdPos : (QuatAdele a b)ˣ →* posA a b :=
  (nrdHom a b).codRestrict (posA a b) fun x => nrdUnit_pos_of_ramified x

@[simp] theorem coe_nrdPos (x : (QuatAdele a b)ˣ) : ((nrdPos a b x : posA a b) : (Adeles F)ˣ) = nrdUnit x := rfl

theorem continuous_nrdPos : Continuous (nrdPos a b) := continuous_nrdHom.subtype_mk _

theorem measurable_nrdPos : Measurable (nrdPos a b) := continuous_nrdPos.measurable

theorem nrdPos_surjective (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Surjective (nrdPos a b) := by
  rintro ⟨u, hu⟩
  obtain ⟨x, hx⟩ := (mem_posA_iff_exists_nrd ha0 hb0 u).1 hu
  exact ⟨x, Subtype.ext hx⟩

theorem mem_ker_nrdPos {x : (QuatAdele a b)ˣ} : x ∈ (nrdPos a b).ker ↔ nrdUnit x = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

theorem isClosed_ker_nrdPos : IsClosed ((nrdPos a b).ker : Set (QuatAdele a b)ˣ) := by
  have : ((nrdPos a b).ker : Set (QuatAdele a b)ˣ) = nrdHom a b ⁻¹' {1} := by
    ext x; simp only [SetLike.mem_coe, mem_ker_nrdPos, mem_preimage, mem_singleton_iff]; rfl
  rw [this]; exact isClosed_singleton.preimage continuous_nrdHom

instance : SecondCountableTopology (nrdPos a b).ker := TopologicalSpace.Subtype.secondCountableTopology _

instance : LocallyCompactSpace (nrdPos a b).ker :=
  (isClosed_ker_nrdPos (a := a) (b := b)).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem mem_quatOne_of_mem_ker_nrdPos (x : (nrdPos a b).ker) : (x : (QuatAdele a b)ˣ) ∈ quatOne a b := by
  rw [mem_quatOne, mem_ker_nrdPos.1 x.2, ideleNorm_one]

theorem mem_ker_nrdPos_of_SL1A (y : SL1A a b) : ((y : quatOne a b) : (QuatAdele a b)ˣ) ∈ (nrdPos a b).ker :=
  mem_ker_nrdPos.2 (mem_SL1A.1 y.2)

variable (a b) in
/-- $\ker(\operatorname{nrd} : (D\otimes\mathbb A)^\times\to A_+)\cong$ `SL1A`. -/
def kerPosEquiv : (nrdPos a b).ker ≃ₜ* SL1A a b where
  toFun x := ⟨⟨x, mem_quatOne_of_mem_ker_nrdPos x⟩, mem_SL1A.2 (mem_ker_nrdPos.1 x.2)⟩
  invFun y := ⟨(y : quatOne a b), mem_ker_nrdPos_of_SL1A y⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

@[simp] theorem coe_kerPosEquiv (x : (nrdPos a b).ker) :
    (((kerPosEquiv a b x : SL1A a b) : quatOne a b) : (QuatAdele a b)ˣ) = x := rfl

@[simp] theorem coe_kerPosEquiv_symm (y : SL1A a b) :
    (((kerPosEquiv a b).symm y : (nrdPos a b).ker) : (QuatAdele a b)ˣ) = ((y : quatOne a b) : (QuatAdele a b)ˣ) :=
  rfl

variable (a b) in
/-- $\mu_+ = $ `tamIdeles` restricted to $A_+$. -/
def muPosA : Measure (posA a b) := (tamIdeles F).comap Subtype.val

theorem measurableEmbedding_posA : MeasurableEmbedding (Subtype.val : posA a b → (Adeles F)ˣ) :=
  MeasurableEmbedding.subtype_coe (isOpen_posA a b).measurableSet

instance : (muPosA a b).IsMulLeftInvariant :=
  isMulLeftInvariant_comap_subgroup (tamIdeles F) (posA a b) (isOpen_posA a b)

instance : IsFiniteMeasureOnCompacts (muPosA a b) := by
  refine ⟨fun K hK => ?_⟩
  rw [muPosA, measurableEmbedding_posA.comap_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top

variable (ha : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

include ha hb ha0 hb0 in
/-- The Tamagawa measure `muSL1` of $\mathrm{SL}_1$ transported to $\ker(\operatorname{nrd}\to A_+)$. -/
def muSL1P : Measure (nrdPos a b).ker := (muSL1 ha hb ha0 hb0).map (kerPosEquiv a b).symm

include ha hb ha0 hb0 in
theorem isHaarMeasure_muSL1P : (muSL1P ha hb ha0 hb0).IsHaarMeasure := by
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  exact ContinuousMulEquiv.isHaarMeasure_map _ _

/-! ### The shell computation -/

theorem quatSplit_mul_SL1_snd (x : (QuatAdele a b)ˣ) (k : SL1A a b) :
    (quatSplit a b (x * ((k : quatOne a b) : (QuatAdele a b)ˣ))).2 = (quatSplit a b x).2 := by
  rw [quatSplit_apply_snd, quatSplit_apply_snd, nrdUnit_mul, mem_SL1A.1 k.2, mul_one]

theorem quatSplit_mul_SL1_fst (x : (QuatAdele a b)ˣ) (k : SL1A a b) :
    (quatSplit a b (x * ((k : quatOne a b) : (QuatAdele a b)ˣ))).1 = (quatSplit a b x).1 * (k : quatOne a b) := by
  apply Subtype.ext
  have h2 := quatSplit_mul_SL1_snd x k
  change x * ((k : quatOne a b) : (QuatAdele a b)ˣ) *
      (quatSectionHom a b (quatSplit a b (x * ((k : quatOne a b) : (QuatAdele a b)ˣ))).2)⁻¹ =
    x * (quatSectionHom a b (quatSplit a b x).2)⁻¹ * ((k : quatOne a b) : (QuatAdele a b)ˣ)
  rw [h2, mul_assoc, mul_assoc]
  congr 1
  have hc := quatScalar_comm a b (normSectionHom F (Multiplicative.ofAdd (Multiplicative.toAdd
    (quatSplit a b x).2 / 2)))⁻¹ ((k : quatOne a b) : (QuatAdele a b)ˣ)
  rw [map_inv] at hc
  exact hc.symm

/-- $\operatorname{nrd}$ of the section: $\operatorname{nrd}(s_D(t)) = s(t)$. -/
theorem nrdUnit_quatSectionHom (t : Multiplicative ℝ) : nrdUnit (quatSectionHom a b t) = normSectionHom F t := by
  change nrdUnit (quatScalar a b (normSectionHom F (Multiplicative.ofAdd (Multiplicative.toAdd t / 2)))) = _
  rw [nrdUnit_quatScalar, ← map_pow]
  congr 1
  rw [← ofAdd_toAdd t, ← ofAdd_nsmul]
  simp only [toAdd_ofAdd, ofAdd_toAdd, nsmul_eq_mul]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * (Multiplicative.toAdd t / 2) = Multiplicative.toAdd t by push_cast; ring]
  exact ofAdd_toAdd t

theorem quatSplit_apply_snd' (a b : F) (x : (QuatAdele a b)ˣ) : (quatSplit a b x).2 = quatLogNorm a b x := rfl

/-- $\operatorname{ideleSplit}(\operatorname{nrd}x) = (\operatorname{nrd}x^1, \log\|\operatorname{nrd}x\|)$. -/
theorem ideleSplit_nrdUnit (x : (QuatAdele a b)ˣ) :
    ideleSplit F (nrdUnit x) = (((nrdOne a b (quatSplit a b x).1 : posOne a b) : ideleOne F), (quatSplit a b x).2) := by
  have hlog : quatLogNorm a b x = ideleLogNorm F (nrdUnit x) := by
    rw [← quatSplit_apply_snd' a b x]
    exact (quatSplit_apply_snd a b x).trans (ideleSplit_apply_snd (nrdUnit x)).symm
  refine Prod.ext (Subtype.ext ?_) ?_
  · show nrdUnit x * (normSectionHom F (ideleLogNorm F (nrdUnit x)))⁻¹ =
      nrdUnit (x * (quatSectionHom a b (quatLogNorm a b x))⁻¹)
    rw [nrdUnit_mul, show nrdUnit (quatSectionHom a b (quatLogNorm a b x))⁻¹ =
        (nrdUnit (quatSectionHom a b (quatLogNorm a b x)))⁻¹ from MonoidHom.map_inv (nrdHom a b) _,
      nrdUnit_quatSectionHom, hlog]
  · rw [ideleSplit_apply_snd, quatSplit_apply_snd]

theorem normSectionHom_pos (t : Multiplicative ℝ) (w : {w : InfinitePlace F // w.IsReal}) :
    0 < ((normSectionHom F t : (Adeles F)ˣ) : Adeles F).1.1 w :=
  Real.rpow_pos_of_pos (Real.exp_pos _) _

/-- $u\in A_+\iff u^1\in\mathbb A^1_+$ (the norm section is positive at every real place). -/
theorem mem_posA_iff_ideleSplit (u : (Adeles F)ˣ) : u ∈ posA a b ↔ (ideleSplit F u).1 ∈ posOne a b := by
  have hu : u = ((ideleSplit F u).1 : (Adeles F)ˣ) * normSectionHom F (ideleSplit F u).2 :=
    ((ideleSplit F).symm_apply_apply u).symm
  rw [mem_posA, mem_posOne]
  constructor
  · intro h w hw hram
    have h1 := h w hw hram
    rw [hu, idele_mul_fst_fst] at h1
    exact pos_of_mul_pos_left h1 (normSectionHom_pos _ ⟨w, hw⟩).le
  · intro h w hw hram
    rw [hu, idele_mul_fst_fst]
    exact mul_pos (h w hw hram) (normSectionHom_pos _ ⟨w, hw⟩)

/-- The fibre measure of the shell $S = \{x : x^1\in E,\ 0\le\log\|\operatorname{nrd}x\|\le1\}$ over $\operatorname{nrd}x$. -/
theorem fibK_nrdPos_shell (μ : Measure (SL1A a b)) (x : (QuatAdele a b)ˣ) {E : Set (quatOne a b)}
    (hE : MeasurableSet E) :
    NormalFib.fibK (nrdPos a b) (μ.map (kerPosEquiv a b).symm) x
        (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) =
      (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1).indicator 1 (quatSplit a b x).2 *
        NormalFib.fibK (nrdOne a b) μ (quatSplit a b x).1 E := by
  classical
  have hS : MeasurableSet (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) :=
    (hE.prod (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))).preimage (quatSplit a b).continuous.measurable
  rw [NormalFib.fibK_apply _ _ _ hS, NormalFib.fibK_apply _ _ _ hE,
    Measure.map_apply (map_continuous (kerPosEquiv a b).symm).measurable
      (hS.preimage (NormalFib.measurable_mul_val _ _))]
  have hset : (kerPosEquiv a b).symm ⁻¹' ((fun k : (nrdPos a b).ker => x * (k : (QuatAdele a b)ˣ)) ⁻¹'
      (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)))) =
      if (quatSplit a b x).2 ∈ Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1 then
        (fun k : SL1A a b => (quatSplit a b x).1 * (k : quatOne a b)) ⁻¹' E else ∅ := by
    ext k
    simp only [mem_preimage, coe_kerPosEquiv_symm, mem_prod, quatSplit_mul_SL1_fst, quatSplit_mul_SL1_snd]
    split_ifs with h
    · simp [h]
    · simp [h]
  rw [hset]
  split_ifs with h
  · rw [indicator_of_mem h, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem h, measure_empty, zero_mul]

set_option maxHeartbeats 1600000 in
include ha hb ha0 hb0 in
/-- **The reduced-norm fibration of `tamQuat`**: `tamQuat` is the fibred measure of $\mu_{A_+}$ (= `tamIdeles` on $A_+$)
and $\mu_{\mathrm{SL}_1}$ along $\operatorname{nrd} : (D\otimes\mathbb A)^\times\to A_+$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 (Tamagawa measures in an exact sequence) [unverified page]"]
theorem fibMeas_nrdPos :
    NormalFib.fibMeas (nrdPos a b) (nrdPos_surjective ha0 hb0) (muPosA a b) (muSL1P ha hb ha0 hb0) =
      tamQuat a b := by
  have := isHaarMeasure_muSL1P ha hb ha0 hb0
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  obtain ⟨ν, hν⟩ : ∃ ν, ν = NormalFib.fibMeas (nrdPos a b) (nrdPos_surjective ha0 hb0) (muPosA a b)
    (muSL1P ha hb ha0 hb0) := ⟨_, rfl⟩
  rw [← hν]
  have hνl : ν.IsMulLeftInvariant := hν ▸ NormalFib.isMulLeftInvariant_fibMeas _ _ measurable_nrdPos _ _
  have hνc : IsFiniteMeasureOnCompacts ν := hν ▸
    ⟨fun _ hC => NormalFib.fibMeas_compact_lt_top _ _ continuous_nrdPos _ _ isClosed_ker_nrdPos hC⟩
  set E := quatOneRefSet a b
  have hEm : MeasurableSet E := isCompact_quatOneRefSet.isClosed.measurableSet
  set I : Set (Multiplicative ℝ) := Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1 with hI
  have hIm : MeasurableSet I := (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))
  set S := quatSplit a b ⁻¹' (E ×ˢ I) with hS
  have hSm : MeasurableSet S := (hEm.prod hIm).preimage (quatSplit a b).continuous.measurable
  have hT : tamQuat a b S = muQuatOneTam ha hb ha0 hb0 E := (muQuatOneTam_apply ha hb ha0 hb0 E).symm
  have h0 : tamQuat a b S ≠ 0 := hT ▸ muQuatOneTam_refSet_ne_zero ha hb ha0 hb0
  have htop : tamQuat a b S ≠ ∞ := hT ▸ muQuatOneTam_refSet_ne_top ha hb ha0 hb0
  -- the norm-one kernel, extended by zero to `ideleOne`
  obtain ⟨g, hg⟩ : ∃ g : posOne a b → ℝ≥0∞, g = fun q => NormalFib.kern (nrdOne a b) (nrdOne_surjective ha0 hb0)
    (muSL1 ha hb ha0 hb0) q E := ⟨_, rfl⟩
  have hgm : Measurable g := hg ▸ NormalFib.measurable_kern_apply _ _ measurable_nrdOne _ hEm
  obtain ⟨G, hG⟩ : ∃ G : ideleOne F → ℝ≥0∞, G = Function.extend Subtype.val g 0 := ⟨_, rfl⟩
  have hGm : Measurable G := hG ▸ measurableEmbedding_posOne.measurable_extend hgm measurable_const
  have hGval : ∀ q : posOne a b, G q = g q := fun q => hG ▸ Subtype.val_injective.extend_apply _ _ q
  have hGout : ∀ q : ideleOne F, q ∉ posOne a b → G q = 0 := fun q hq => by
    rw [hG, Function.extend_apply' _ _ _ (fun ⟨q', hq'⟩ => hq (hq' ▸ q'.2))]; rfl
  -- the kernel on `A_+`
  set H : (Adeles F)ˣ → ℝ≥0∞ := fun u => I.indicator 1 (ideleSplit F u).2 * G (ideleSplit F u).1 with hH
  have hHm : Measurable H :=
    ((measurable_one.indicator hIm).comp (continuous_snd.comp (ideleSplit F).continuous).measurable).mul
      (hGm.comp (continuous_fst.comp (ideleSplit F).continuous).measurable)
  have hkern : ∀ c : posA a b, NormalFib.kern (nrdPos a b) (nrdPos_surjective ha0 hb0) (muSL1P ha hb ha0 hb0) c S =
      H c := by
    intro c
    obtain ⟨x, rfl⟩ := nrdPos_surjective ha0 hb0 c
    rw [NormalFib.kern_apply_N, muSL1P, fibK_nrdPos_shell _ x hEm]
    show _ = I.indicator 1 (ideleSplit F (nrdUnit x)).2 * G (ideleSplit F (nrdUnit x)).1
    rw [ideleSplit_nrdUnit, hGval]
    congr 1
    rw [hg]
    beta_reduce
    rw [NormalFib.kern_apply_N]
  have hHout : ∀ u : (Adeles F)ˣ, u ∉ posA a b → H u = 0 := fun u hu => by
    show I.indicator 1 (ideleSplit F u).2 * G (ideleSplit F u).1 = 0
    rw [hGout _ (fun h => hu ((mem_posA_iff_ideleSplit u).2 h)), mul_zero]
  have hCS : MeasurableSpace.CountablySeparated (posA a b) := inferInstance
  have hSB : StandardBorelSpace (QuatAdele a b)ˣ := inferInstance
  have hM1 : MeasurableMul (posA a b) := inferInstance
  have hM2 : MeasurableMul₂ (QuatAdele a b)ˣ := inferInstance
  have hM3 : MeasurableInv (QuatAdele a b)ˣ := inferInstance
  have hSF : SFinite (muSL1P ha hb ha0 hb0) := inferInstance
  have hLI : (muSL1P ha hb ha0 hb0).IsMulLeftInvariant := inferInstance
  have hνS : ν S = muQuatOneTam ha hb ha0 hb0 E := by
    rw [hν, NormalFib.fibMeas_apply (nrdPos a b) (nrdPos_surjective ha0 hb0) measurable_nrdPos (muPosA a b)
      (muSL1P ha hb ha0 hb0) hSm, lintegral_congr hkern]
    -- integrate over `A_+`, then over `𝔸^×`
    rw [muPosA]
    show ∫⁻ c, H ((c : posA a b) : (Adeles F)ˣ) ∂(Measure.comap Subtype.val (tamIdeles F)) = _
    rw [← measurableEmbedding_posA.lintegral_map H, measurableEmbedding_posA.map_comap, Subtype.range_coe]
    rw [setLIntegral_eq_of_support_subset (fun u hu => by
      by_contra h; exact hu (hHout u h))]
    have hmap := lintegral_map_equiv (fun p => H ((ideleSplit F).symm p))
      (ideleSplit F).toHomeomorph.toMeasurableEquiv (μ := tamIdeles F)
    have he : ∀ u, (ideleSplit F).symm ((ideleSplit F).toHomeomorph.toMeasurableEquiv u) = u :=
      fun u => (ideleSplit F).symm_apply_apply u
    simp only [he] at hmap
    rw [← hmap]
    change ∫⁻ p, H ((ideleSplit F).symm p) ∂((tamIdeles F).map (ideleSplit F)) = _
    rw [map_ideleSplit_tamIdeles]
    have hHp : ∀ p : ideleOne F × Multiplicative ℝ, H ((ideleSplit F).symm p) = I.indicator 1 p.2 * G p.1 := by
      intro p; simp only [hH, ContinuousMulEquiv.apply_symm_apply]
    simp_rw [hHp, mul_comm (I.indicator 1 _)]
    rw [lintegral_prod_mul hGm.aemeasurable (measurable_one.indicator hIm).aemeasurable,
      lintegral_indicator_one hIm, hI, dtt_apply]
    change (∫⁻ q, G q ∂muIdeleOne F) * volume (Icc (0 : ℝ) 1) = _
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
    -- back to `A^1_+`
    rw [← setLIntegral_eq_of_support_subset (s := (posOne a b : Set (ideleOne F))) (fun q hq => by
      by_contra h; exact hq (hGout q h)), ← Subtype.range_coe (s := (posOne a b : Set (ideleOne F))),
      ← measurableEmbedding_posOne.map_comap, measurableEmbedding_posOne.lintegral_map]
    change ∫⁻ q, G q ∂muPosOne a b = _
    simp_rw [hGval]
    rw [hg, ← NormalFib.fibMeas_apply (nrdOne a b) (nrdOne_surjective ha0 hb0) measurable_nrdOne (muPosOne a b)
      (muSL1 ha hb ha0 hb0) hEm, fibMeas_muSL1]
  rw [measure_eq_div_smul ν (tamQuat a b) h0 htop, hνS, hT,
    ENNReal.div_self (muQuatOneTam_refSet_ne_zero ha hb ha0 hb0) (muQuatOneTam_refSet_ne_top ha hb ha0 hb0),
    one_smul]

end

end QuadFormsKB.Tamagawa.Measure.Weil
