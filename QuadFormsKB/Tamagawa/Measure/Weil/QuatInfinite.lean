import QuadFormsKB.Tamagawa.Measure.Weil.QuatLocal
import QuadFormsKB.Tamagawa.Measure.Weil.LinearScaling

/-!
# The archimedean factor $\omega_\infty$ on $(\mathbb H\otimes F_\infty)^\times$

$\mathbb H = \mathbb H[F,a,b]$, $F_\infty$ = `mixedSpace F` $=\prod_{w\text{ real}}\mathbb R\times\prod_{w\text{ complex}}\mathbb C$,
`QuatInf a b` $=\mathbb H[F_\infty,a,b]$ with the coordinate topology ($1,i,j,k$), $dx_\infty$ = the self-dual coordinate
measure `quatInfVol` ($=\mu_\infty^{\otimes4}$, `muInfVec`).

* `QuatInf a b` is a locally compact topological ring; $x$ is a unit iff $\operatorname{nrd}(x)\in F_\infty^\times$ and
  **`isOpenEmbedding_val_quatInf`** (the inverse is $\operatorname{nrd}(x)^{-1}\bar x$).
* **`distribHaarChar_quatInf`**: the modulus of left multiplication by $u$ is
  $|\det_{\mathbb R}(\operatorname{nrd}(u^{-1})^2\cdot)|^{-1} = \|\operatorname{nrd}u\|_\infty^2$ (via $\det L_u = \operatorname{nrd}(u)^2$
  and the archimedean $\mathrm{GL}_4$ scaling `map_mulVec_muInfVec`); it is continuous.
* **`omegaQuatInf a b`** $=\|\operatorname{nrd}x\|_\infty^{-2}dx_\infty$ (`unitsHaar`), a Haar measure on
  $(\mathbb H\otimes F_\infty)^\times$ (**`isHaarMeasure_omegaQuatInf`**): Weil's archimedean $\omega_\infty$ for $A = \mathbb H$
  (no convergence factor at the infinite places).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Quaternion Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

variable (a b : F)

/-- $\mathbb H[F_\infty,a,b]$. -/
abbrev QuatInf := ℍ[mixedSpace F, mixedEmbedding F a, 0, mixedEmbedding F b]

/-- The coordinates $1,i,j,k$. -/
abbrev quatInfCoord : QuatInf a b ≃ₗ[mixedSpace F] (Fin 4 → mixedSpace F) := QuaternionAlgebra.linearEquivTuple _ _ _

instance : TopologicalSpace (QuatInf a b) := TopologicalSpace.induced (quatInfCoord a b) inferInstance

theorem isInducing_quatInfCoord : IsInducing (quatInfCoord a b) := ⟨rfl⟩

theorem continuous_quatInfCoord : Continuous (quatInfCoord a b) := (isInducing_quatInfCoord a b).continuous

theorem continuous_ire : Continuous fun x : QuatInf a b => x.re :=
  (continuous_apply 0).comp (continuous_quatInfCoord a b)
theorem continuous_iimI : Continuous fun x : QuatInf a b => x.imI :=
  (continuous_apply 1).comp (continuous_quatInfCoord a b)
theorem continuous_iimJ : Continuous fun x : QuatInf a b => x.imJ :=
  (continuous_apply 2).comp (continuous_quatInfCoord a b)
theorem continuous_iimK : Continuous fun x : QuatInf a b => x.imK :=
  (continuous_apply 3).comp (continuous_quatInfCoord a b)

theorem continuous_quatInf_iff {X : Type*} [TopologicalSpace X] {f : X → QuatInf a b} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).imI) ∧
      Continuous (fun x => (f x).imJ) ∧ Continuous (fun x => (f x).imK) := by
  refine ⟨fun h => ⟨(continuous_ire a b).comp h, (continuous_iimI a b).comp h, (continuous_iimJ a b).comp h,
    (continuous_iimK a b).comp h⟩, fun ⟨h0, h1, h2, h3⟩ => ?_⟩
  rw [(isInducing_quatInfCoord a b).continuous_iff, continuous_pi_iff]
  intro i; fin_cases i
  exacts [h0, h1, h2, h3]

instance : IsTopologicalRing (QuatInf a b) where
  continuous_add := by
    have := (continuous_ire a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_ire a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimI a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimI a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimJ a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimJ a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimK a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimK a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    refine (continuous_quatInf_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
        QuaternionAlgebra.imK_add] <;> fun_prop
  continuous_mul := by
    have := (continuous_ire a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_ire a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimI a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimI a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimJ a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimJ a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimK a b).comp (continuous_fst (X := QuatInf a b) (Y := QuatInf a b))
    have := (continuous_iimK a b).comp (continuous_snd (X := QuatInf a b) (Y := QuatInf a b))
    refine (continuous_quatInf_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
        QuaternionAlgebra.imK_mul] <;> fun_prop
  continuous_neg := by
    have := continuous_ire a b
    have := continuous_iimI a b
    have := continuous_iimJ a b
    have := continuous_iimK a b
    refine (continuous_quatInf_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg,
        QuaternionAlgebra.imK_neg] <;> fun_prop

theorem continuous_star_inf : Continuous (star : QuatInf a b → QuatInf a b) := by
  have := continuous_ire a b
  have := continuous_iimI a b
  have := continuous_iimJ a b
  have := continuous_iimK a b
  refine (continuous_quatInf_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star] <;> fun_prop

/-- $\operatorname{nrd}(x) = \operatorname{re}(x\bar x)$ on $\mathbb H[F_\infty]$. -/
def nrdInf (x : QuatInf a b) : mixedSpace F := (x * star x).re

theorem continuous_nrdInf : Continuous (nrdInf a b) :=
  (continuous_ire a b).comp (continuous_id.mul (continuous_star_inf a b))

theorem nrdInf_mul (x y : QuatInf a b) : nrdInf a b (x * y) = nrdInf a b x * nrdInf a b y := by
  have hx := QuaternionAlgebra.mul_star_eq_coe x
  have hy := QuaternionAlgebra.mul_star_eq_coe y
  have h : x * y * star (x * y) = (↑(nrdInf a b y * nrdInf a b x) : QuatInf a b) := by
    rw [star_mul, mul_assoc, ← mul_assoc y, hy, ← mul_assoc, ← QuaternionAlgebra.coe_commutes, mul_assoc, hx,
      ← QuaternionAlgebra.coe_mul]
    rfl
  rw [nrdInf, h, QuaternionAlgebra.re_coe, mul_comm]

theorem nrdInf_one : nrdInf a b 1 = 1 := by simp [nrdInf]

theorem continuous_symm_quatInfCoord : Continuous (quatInfCoord a b).symm :=
  (isInducing_quatInfCoord a b).continuous_iff.mpr (by
    have : (quatInfCoord a b) ∘ (quatInfCoord a b).symm = id := funext fun p => (quatInfCoord a b).apply_symm_apply p
    rw [this]; exact continuous_id)

/-- The coordinate map as a continuous linear equivalence. -/
def quatInfCLE : QuatInf a b ≃L[mixedSpace F] (Fin 4 → mixedSpace F) where
  toLinearEquiv := quatInfCoord a b
  continuous_toFun := continuous_quatInfCoord a b
  continuous_invFun := continuous_symm_quatInfCoord a b

instance : LocallyCompactSpace (QuatInf a b) := (quatInfCLE a b).toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance : T2Space (QuatInf a b) := (quatInfCLE a b).toHomeomorph.isEmbedding.t2Space

instance : SecondCountableTopology (QuatInf a b) := (isInducing_quatInfCoord a b).secondCountableTopology

instance measurableSpace_quatInf : MeasurableSpace (QuatInf a b) := borel _

instance : BorelSpace (QuatInf a b) := ⟨rfl⟩

instance measurableSpace_quatInfUnits : MeasurableSpace (QuatInf a b)ˣ := borel _

instance : BorelSpace (QuatInf a b)ˣ := ⟨rfl⟩

instance : SecondCountableTopology (QuatInf a b)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := QuatInf a b)).symm.isEmbedding.secondCountableTopology

instance : SecondCountableTopology (QuatInf a b)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology

/-! ### Units -/

theorem isUnit_iff_isUnit_nrdInf (x : QuatInf a b) : IsUnit x ↔ IsUnit (nrdInf a b x) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : nrdInf a b u * nrdInf a b (u⁻¹ : (QuatInf a b)ˣ) = 1 := by
      rw [← nrdInf_mul, Units.mul_inv, nrdInf_one]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨⟨x, (↑n⁻¹ : mixedSpace F) • star x, ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe, show (x * star x).re = nrdInf a b x from rfl, ← hn]
      ext <;> simp
    · rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe]
      have : (star x * x).re = nrdInf a b x := by
        simp only [nrdInf, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
          QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
        ring
      rw [this, ← hn]
      ext <;> simp

/-- **Units of $\mathbb H[F_\infty]$ form an open set with continuous inverse.** -/
theorem isOpenEmbedding_val_quatInf : IsOpenEmbedding (Units.val : (QuatInf a b)ˣ → QuatInf a b) := by
  have hrange : range (Units.val : (QuatInf a b)ˣ → QuatInf a b) =
      nrdInf a b ⁻¹' range (Units.val : (mixedSpace F)ˣ → mixedSpace F) := by
    ext x
    simp only [mem_range, mem_preimage]
    exact isUnit_iff_isUnit_nrdInf a b x
  refine ⟨Units.isEmbedding_val_mk' (f := fun x => Ring.inverse (nrdInf a b x) • star x) ?_ ?_, ?_⟩
  · have hinv : ContinuousOn (fun x => Ring.inverse (nrdInf a b x)) {x : QuatInf a b | IsUnit x} := by
      intro x hx
      obtain ⟨n, hn⟩ := (isUnit_iff_isUnit_nrdInf a b x).mp hx
      refine ContinuousAt.continuousWithinAt ?_
      have h' : ContinuousAt Ring.inverse (nrdInf a b x) := hn ▸ NormedRing.inverse_continuousAt n
      exact h'.comp (continuous_nrdInf a b).continuousAt
    rw [(isInducing_quatInfCoord a b).continuousOn_iff, continuousOn_pi]
    intro i
    simp only [Function.comp_def, map_smul, Pi.smul_apply, smul_eq_mul]
    exact hinv.mul ((continuous_apply i).comp ((continuous_quatInfCoord a b).comp
      (continuous_star_inf a b))).continuousOn
  · intro u
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    obtain ⟨n, hn⟩ := (isUnit_iff_isUnit_nrdInf a b u).mp u.isUnit
    rw [← hn, Ring.inverse_unit, mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe,
      show ((u : QuatInf a b) * star (u : QuatInf a b)).re = nrdInf a b u from rfl, ← hn]
    ext <;> simp
  · rw [hrange]
    exact Units.isOpen.preimage (continuous_nrdInf a b)

instance : LocallyCompactSpace (QuatInf a b)ˣ := (isOpenEmbedding_val_quatInf a b).locallyCompactSpace

/-! ### The modulus and $\omega_\infty$ -/

theorem det_mulLeft_ne_zero_of_isUnit {x : mixedSpace F} (hx : IsUnit x) :
    LinearMap.det (LinearMap.mulLeft ℝ x) ≠ 0 := by
  have := (hx.map (Algebra.norm ℝ)).ne_zero
  rwa [Algebra.norm_apply] at this

/-- The coordinate measure $dx_\infty = \mu_\infty^{\otimes4}$ on $\mathbb H[F_\infty]$. -/
def quatInfVol : Measure (QuatInf a b) := (muInfVec F (Fin 4)).map (quatInfCLE a b).symm

instance : (quatInfVol a b).IsAddHaarMeasure :=
  (quatInfCLE a b).symm.isAddHaarMeasure_map _

theorem quatInfCoord_mul (u x : QuatInf a b) :
    quatInfCoord a b (u * x) = (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _) u) *ᵥ quatInfCoord a b x :=
  (Algebra.leftMulMatrix_mulVec_repr (QuaternionAlgebra.basisOneIJK _ 0 _) u x).symm

theorem det_leftMulMatrix_inf (u : QuatInf a b) :
    (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _) u).det = nrdInf a b u ^ 2 := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix]
  exact QuaternionAlgebra.det_mulLeft _ _ _

/-- **The modulus of $(\mathbb H\otimes F_\infty)^\times$ on $\mathbb H\otimes F_\infty$**:
$\Delta(u) = |\det_{\mathbb R}(\operatorname{nrd}(u^{-1})^2\cdot)|^{-1}$ ($=\|\operatorname{nrd}u\|_\infty^2$). -/
theorem distribHaarChar_quatInf (u : (QuatInf a b)ˣ) :
    (distribHaarChar (QuatInf a b) u : ℝ) =
      |LinearMap.det (LinearMap.mulLeft ℝ (nrdInf a b ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) ^ 2))|⁻¹ := by
  set μ := muInfVec F (Fin 4)
  set e := (quatInfCLE a b).toHomeomorph.toMeasurableEquiv
  set M := Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _) ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b)
  have hMdet : M.det = nrdInf a b ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) ^ 2 := det_leftMulMatrix_inf a b _
  have hMu : IsUnit M.det := by
    rw [hMdet]; exact ((isUnit_iff_isUnit_nrdInf a b _).mp (u⁻¹).isUnit).pow 2
  have hscale := map_mulVec_muInfVec M hMu
  rw [hMdet] at hscale
  set C : Set (Fin 4 → mixedSpace F) := Metric.ball 0 1
  have hC0 : μ C ≠ 0 := (Metric.isOpen_ball.measure_pos μ ⟨0, Metric.mem_ball_self one_pos⟩).ne'
  have hCT : μ C ≠ ⊤ := measure_ball_lt_top.ne
  have hνs : ∀ T : Set (Fin 4 → mixedSpace F), MeasurableSet T → quatInfVol a b (e ⁻¹' T) = μ T := fun T hT => by
    rw [quatInfVol, Measure.map_apply (quatInfCLE a b).symm.continuous.measurable (e.measurable hT)]
    congr 1
    ext x; simp [e]
  have hCm : MeasurableSet C := Metric.isOpen_ball.measurableSet
  have hset : u • (e ⁻¹' C) = e ⁻¹' (M.mulVec ⁻¹' C) := by
    ext x
    simp only [mem_preimage, mem_smul_set_iff_inv_smul_mem]
    change quatInfCoord a b (((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) * x) ∈ C ↔ M *ᵥ quatInfCoord a b x ∈ C
    rw [quatInfCoord_mul]
  have hMm : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hdet0 : LinearMap.det (LinearMap.mulLeft ℝ (nrdInf a b ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) ^ 2)) ≠ 0 := by
    exact det_mulLeft_ne_zero_of_isUnit (((isUnit_iff_isUnit_nrdInf a b _).mp (u⁻¹).isUnit).pow 2)
  set r : ℝ≥0 := ⟨|LinearMap.det (LinearMap.mulLeft ℝ (nrdInf a b ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) ^ 2))|⁻¹,
    by positivity⟩
  have hr : distribHaarChar (QuatInf a b) u = r :=
    distribHaarChar_eq_of_measure_smul_eq_mul (μ := quatInfVol a b) (s := e ⁻¹' C)
      (by rwa [hνs C hCm]) (by rwa [hνs C hCm]) (by
        rw [hset, hνs _ (hMm hCm), ← Measure.map_apply hMm hCm, hscale, Measure.smul_apply, smul_eq_mul,
          hνs C hCm]
        congr 1
        exact ENNReal.ofReal_coe_nnreal (p := r))
  rw [hr]
  rfl

theorem continuous_distribHaarChar_quatInf :
    Continuous (distribHaarChar (QuatInf a b) : (QuatInf a b)ˣ → ℝ≥0) := by
  have hc : Continuous fun u : (QuatInf a b)ˣ => (distribHaarChar (QuatInf a b) u : ℝ) := by
    simp_rw [distribHaarChar_quatInf]
    refine Continuous.inv₀ (continuous_abs_det_mulLeft.comp (((continuous_nrdInf a b).comp
      (Units.continuous_val.comp continuous_inv)).pow 2)) fun u => ?_
    rw [abs_ne_zero]
    exact det_mulLeft_ne_zero_of_isUnit (((isUnit_iff_isUnit_nrdInf a b _).mp (u⁻¹).isUnit).pow 2)
  exact continuous_induced_rng.mpr hc

/-- **Weil's $\omega_\infty = \|\operatorname{nrd}x\|_\infty^{-2}dx_\infty$ on $(\mathbb H\otimes F_\infty)^\times$.** -/
def omegaQuatInf : Measure (QuatInf a b)ˣ := unitsHaar (QuatInf a b) (quatInfVol a b)

/-- **$\omega_\infty$ is a Haar measure.** -/
@[kb "weil1982" "§2.3 [unverified page] (ω_∞ = ‖nrd x‖_∞^{-2}dx_∞ on (ℍ⊗F_∞)^×)"]
theorem isHaarMeasure_omegaQuatInf : (omegaQuatInf a b).IsHaarMeasure :=
  isHaarMeasure_unitsHaar (isOpenEmbedding_val_quatInf a b) (continuous_distribHaarChar_quatInf a b) _

instance : (omegaQuatInf a b).IsHaarMeasure := isHaarMeasure_omegaQuatInf a b

end

end QuadFormsKB.Tamagawa.Measure.Weil
