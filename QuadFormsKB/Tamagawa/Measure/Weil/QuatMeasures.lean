import QuadFormsKB.Tamagawa.Measure.Weil.QuatUnits
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures

/-!
# Haar measures on $(\mathbb H\otimes\mathbb A)^\times$ and $\mathbb H_{\mathbb A}^1$

$\mathbb H = \mathbb H[F,a,b]$ over any number field $F$, `QuatAdele a b` $=\mathbb H[\mathbb A_F,a,b]$.

* **Local compactness**: $\mathbb H[\mathbb A_F,a,b]$ is locally compact (the coordinate map to $\mathbb A_F^4$ is a
  homeomorphism), hence so is its unit group (closed in $\mathbb H_{\mathbb A}\times\mathbb H_{\mathbb A}^{\mathrm{op}}$,
  Mathlib), and so is the closed subgroup $\mathbb H_{\mathbb A}^1$.
* `quatScalar`: the central embedding $\mathbb A_F^\times\to(\mathbb H\otimes\mathbb A)^\times$; **`nrdUnit_quatScalar`**:
  $\operatorname{nrd}(c) = c^2$.
* **`quatSplit`**: $(\mathbb H\otimes\mathbb A)^\times\cong\mathbb H_{\mathbb A}^1\times\mathbb R_{>0}$,
  $x\mapsto(x\,s(\|\operatorname{nrd}x\|)^{-1}, \|\operatorname{nrd}x\|)$ with the central section
  $s(t) = \operatorname{normSection}(t^{1/2})$; **`map_quatSplit`**: every Haar measure $\mu$ on
  $(\mathbb H\otimes\mathbb A)^\times$ is $\mu^1\times dt/t$ for the Haar measure `muQuatOne μ` on $\mathbb H_{\mathbb A}^1$,
  with $\mu^1(E) = \mu(\{x : x\,s(\|\operatorname{nrd}x\|)^{-1}\in E,\ 1\le\|\operatorname{nrd}x\|\le e\})$
  (**`muQuatOne_apply`**).
* **`muQuatClass μ`** on $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$: the image of $\mu^1$ on a fundamental domain,
  independent of it (**`map_restrict_eq_muQuatClass`**).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Set
open scoped ENNReal NNReal Quaternion

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

variable (a b : F)

/-! ### Local compactness -/

theorem isClosedEmbedding_quatCoord : IsClosedEmbedding (quatCoord a b) :=
  ⟨isEmbedding_quatCoord a b, by rw [(quatCoord a b).surjective.range_eq]; exact isClosed_univ⟩

instance : LocallyCompactSpace (QuatAdele a b) := (isClosedEmbedding_quatCoord a b).locallyCompactSpace

instance : LocallyCompactSpace (QuatAdele a b)ˣ := inferInstance

instance : LocallyCompactSpace (quatOne a b) :=
  (isClosed_quatOne a b).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### The central section and the splitting via $\|\operatorname{nrd}\|$ -/

/-- The central embedding $\mathbb A_F^\times\to(\mathbb H\otimes\mathbb A)^\times$, $c\mapsto c\cdot1$. -/
def quatScalar : (Adeles F)ˣ →* (QuatAdele a b)ˣ := Units.map (algebraMap (Adeles F) (QuatAdele a b)).toMonoidHom

theorem continuous_algebraMap_quat : Continuous (algebraMap (Adeles F) (QuatAdele a b)) := by
  rw [QuaternionAlgebra.coe_algebraMap]
  refine (continuous_quat_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩
  · simp only [QuaternionAlgebra.re_coe]; exact continuous_id
  · simp only [QuaternionAlgebra.imI_coe]; exact continuous_const
  · simp only [QuaternionAlgebra.imJ_coe]; exact continuous_const
  · simp only [QuaternionAlgebra.imK_coe]; exact continuous_const

theorem continuous_quatScalar : Continuous (quatScalar a b) :=
  Units.continuous_iff.mpr ⟨(continuous_algebraMap_quat a b).comp Units.continuous_val,
    (continuous_algebraMap_quat a b).comp Units.continuous_coe_inv⟩

theorem quatScalar_comm (c : (Adeles F)ˣ) (x : (QuatAdele a b)ˣ) : quatScalar a b c * x = x * quatScalar a b c :=
  Units.ext (Algebra.commutes (c : Adeles F) (x : QuatAdele a b))

theorem nrdUnit_quatScalar (c : (Adeles F)ˣ) : nrdUnit (quatScalar a b c) = c ^ 2 := by
  refine Units.ext ?_
  rw [nrdUnit_val, Units.val_pow_eq_pow_val]
  change ((algebraMap (Adeles F) (QuatAdele a b) c) * star (algebraMap (Adeles F) (QuatAdele a b) c)).re = _
  rw [QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_mul,
    QuaternionAlgebra.re_coe, sq]

theorem coe_quatNormSqHom_pos (x : (QuatAdele a b)ˣ) : 0 < (quatNormSqHom a b x : ℝ) := by
  rw [coe_quatNormSqHom]; exact pow_pos (ideleNorm_pos _) 2

/-- $x\mapsto\log\|\operatorname{nrd}x\|_{\mathbb A} = \tfrac12\log\|\det L_x\|_{\mathbb A}$ as a homomorphism to
$\mathbb R_{>0}$ = `Multiplicative ℝ`. -/
def quatLogNorm : (QuatAdele a b)ˣ →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (Real.log (quatNormSqHom a b x : ℝ) / 2)
  map_one' := by rw [map_one, NNReal.coe_one, Real.log_one, zero_div]; rfl
  map_mul' x y := by
    rw [map_mul, NNReal.coe_mul, Real.log_mul (coe_quatNormSqHom_pos a b x).ne' (coe_quatNormSqHom_pos a b y).ne',
      add_div]; rfl

theorem quatLogNorm_eq (x : (QuatAdele a b)ˣ) :
    quatLogNorm a b x = Multiplicative.ofAdd (Real.log (ideleNorm F (nrdUnit x))) := by
  change Multiplicative.ofAdd (Real.log (quatNormSqHom a b x : ℝ) / 2) = _
  rw [coe_quatNormSqHom, Real.log_pow]; congr 1; push_cast; ring

theorem continuous_quatLogNorm : Continuous (quatLogNorm a b) := by
  have hpos : ∀ x : (QuatAdele a b)ˣ, (quatNormSqHom a b x : ℝ) ≠ 0 := fun x => (coe_quatNormSqHom_pos a b x).ne'
  exact continuous_ofAdd.comp ((Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (continuous_quatNormSqHom a b)) hpos).div_const 2)

theorem mem_quatOne_iff_logNorm (x : (QuatAdele a b)ˣ) : x ∈ quatOne a b ↔ quatLogNorm a b x = 1 := by
  rw [mem_quatOne, quatLogNorm_eq]
  rw [ofAdd_eq_one]
  constructor
  · intro h; rw [h, Real.log_one]
  · intro h; rw [← Real.exp_log (ideleNorm_pos (nrdUnit x)), h, Real.exp_zero]

/-- The central section $t\mapsto\operatorname{normSection}(t^{1/2})$ of $\|\operatorname{nrd}\|$ (logarithmically,
$s\mapsto\operatorname{normSection}(e^{s/2})$). -/
def quatSectionHom : Multiplicative ℝ →* (QuatAdele a b)ˣ :=
  (quatScalar a b).comp ((normSectionHom F).comp
    { toFun := fun s => Multiplicative.ofAdd (Multiplicative.toAdd s / 2)
      map_one' := by simp
      map_mul' := fun s t => by rw [toAdd_mul, add_div]; rfl })

theorem continuous_quatSectionHom : Continuous (quatSectionHom a b) :=
  (continuous_quatScalar a b).comp (continuous_normSectionHom.comp
    (continuous_ofAdd.comp (continuous_toAdd.div_const 2)))

theorem quatLogNorm_quatSectionHom (s : Multiplicative ℝ) : quatLogNorm a b (quatSectionHom a b s) = s := by
  rw [quatLogNorm_eq]
  change Multiplicative.ofAdd (Real.log (ideleNorm F (nrdUnit (quatScalar a b
    (normSection F (Real.exp (Multiplicative.toAdd s / 2)) (Real.exp_pos _)))))) = s
  rw [nrdUnit_quatScalar, sq, ideleNorm_mul, ideleNorm_normSection, ← Real.exp_add, Real.log_exp, add_halves]
  rfl

set_option maxHeartbeats 1000000 in
/-- **$(\mathbb H\otimes\mathbb A)^\times\cong\mathbb H_{\mathbb A}^1\times\mathbb R_{>0}$** via $\|\operatorname{nrd}\|$
(`splitEquiv`; the section is central). -/
def quatSplit : (QuatAdele a b)ˣ ≃ₜ* (quatOne a b × Multiplicative ℝ) :=
  splitEquiv (quatLogNorm a b) (quatSectionHom a b) (quatOne a b) (mem_quatOne_iff_logNorm a b)
    (quatLogNorm_quatSectionHom a b) (fun _ _ => quatScalar_comm a b _ _) (continuous_quatLogNorm a b)
    (continuous_quatSectionHom a b)

theorem quatSplit_apply_snd (x : (QuatAdele a b)ˣ) :
    (quatSplit a b x).2 = Multiplicative.ofAdd (Real.log (ideleNorm F (nrdUnit x))) := quatLogNorm_eq a b x

variable {a b}

/-- **The Haar measure $\mu^1$ on $\mathbb H_{\mathbb A}^1$** attached to a Haar measure $\mu$ on $(\mathbb H\otimes\mathbb A)^\times$:
the unique measure with $(\text{`quatSplit`})_*\mu = \mu^1\times dt/t$. -/
def muQuatOne (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] : Measure (quatOne a b) :=
  splitMeasure (quatSplit a b) μ dtt

instance (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] : (muQuatOne μ).IsHaarMeasure :=
  isHaarMeasure_splitMeasure _ _ _

/-- **Measure splitting for $(\mathbb H\otimes\mathbb A)^\times$**: $(\text{`quatSplit`})_*\mu = \mu^1\times dt/t$. -/
@[kb "weil1982" "§2.3 [unverified page] (A_𝔸^× = A_𝔸^1 × ℝ_{>0} for A = ℍ, via ‖nrd‖)"]
theorem map_quatSplit (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] :
    μ.map (quatSplit a b) = (muQuatOne μ).prod dtt :=
  map_eq_prod_splitMeasure _ _ _

theorem mem_quatSplit_preimage {E : Set (quatOne a b)} {x : (QuatAdele a b)ˣ} :
    x ∈ quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)) ↔
      (quatSplit a b x).1 ∈ E ∧ 1 ≤ ideleNorm F (nrdUnit x) ∧ ideleNorm F (nrdUnit x) ≤ Real.exp 1 := by
  have hp := ideleNorm_pos (nrdUnit x)
  simp only [mem_preimage, mem_prod, quatSplit_apply_snd, toAdd_ofAdd, mem_Icc]
  rw [Real.log_nonneg_iff hp, Real.log_le_iff_le_exp hp]

/-- **$\mu^1(E) = \mu(\{x : x\,s(\|\operatorname{nrd}x\|)^{-1}\in E,\ 1\le\|\operatorname{nrd}x\|_{\mathbb A}\le e\})$**
(`mem_quatSplit_preimage`). -/
theorem muQuatOne_apply (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] (E : Set (quatOne a b)) :
    muQuatOne μ E = μ (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) := by
  rw [muQuatOne, splitMeasure_apply _ _ _ (by rw [dtt_ofAdd_Icc]; exact one_ne_zero)
    (by rw [dtt_ofAdd_Icc]; exact ENNReal.one_ne_top), dtt_ofAdd_Icc, div_one]

/-! ### The quotient $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$ -/

instance : Countable (quatUnitsOne a b) :=
  Function.Injective.countable (f := fun x : quatUnitsOne a b => (⟨(x : quatOne a b), x.2⟩ : quatUnitsSub a b))
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : quatUnitsSub a b => (z : (QuatAdele a b)ˣ)) h))

variable (a b) in
/-- $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$. -/
abbrev QuatClassOne := Quotient (MulAction.orbitRel (quatUnitsOne a b) (quatOne a b))

variable (a b) in
/-- The projection $\mathbb H_{\mathbb A}^1\to\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$. -/
abbrev quatClassMk : quatOne a b → QuatClassOne a b := Quotient.mk (MulAction.orbitRel (quatUnitsOne a b) (quatOne a b))

theorem measurable_quatClassMk : Measurable (quatClassMk a b) := fun _ hs => hs

/-- **The quotient measure on $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$** (image of $\mu^1$ restricted to a fixed
fundamental domain; independent of it by `map_restrict_eq_muQuatClass`). -/
def muQuatClass (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] : Measure (QuatClassOne a b) :=
  ((muQuatOne μ).restrict (exists_isFundamentalDomain_quatOne a b (muQuatOne μ)).choose).map (quatClassMk a b)

/-- **The quotient measure does not depend on the fundamental domain.** -/
theorem map_restrict_eq_muQuatClass (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] {D : Set (quatOne a b)}
    (hD : IsFundamentalDomain (quatUnitsOne a b) D (muQuatOne μ)) :
    ((muQuatOne μ).restrict D).map (quatClassMk a b) = muQuatClass μ := by
  ext A hA
  have hm := measurable_quatClassMk (a := a) (b := b)
  rw [muQuatClass, Measure.map_apply hm hA, Measure.map_apply hm hA, Measure.restrict_apply (hm hA),
    Measure.restrict_apply (hm hA)]
  refine hD.measure_set_eq (exists_isFundamentalDomain_quatOne a b (muQuatOne μ)).choose_spec (hm hA) fun γ => ?_
  ext x
  simp only [mem_preimage]
  have : quatClassMk a b (γ • x) = quatClassMk a b x := Quotient.sound ⟨γ, rfl⟩
  rw [this]

theorem muQuatClass_univ (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] {D : Set (quatOne a b)}
    (hD : IsFundamentalDomain (quatUnitsOne a b) D (muQuatOne μ)) : muQuatClass μ univ = muQuatOne μ D := by
  rw [← map_restrict_eq_muQuatClass μ hD, Measure.map_apply measurable_quatClassMk MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

end

end QuadFormsKB.Tamagawa.Measure.Weil
