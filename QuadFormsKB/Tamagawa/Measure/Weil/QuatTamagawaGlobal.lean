import QuadFormsKB.Tamagawa.Measure.Weil.QuatTamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.QuatInfinite
import QuadFormsKB.Tamagawa.Measure.Weil.QuatMeasures

/-!
# The canonical Tamagawa measure on $(\mathbb H\otimes\mathbb A)^\times$, $\mathbb H_{\mathbb A}^1$ and
$\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$

$\mathbb H = \mathbb H[F,a,b]$, $a, b\in F^\times$ integral at every finite place.

* **`quatAdeleRingEquiv`**: $\mathbb H[\mathbb A_F]\cong\mathbb H[F_\infty]\times\mathbb H[\mathbb A_f]$ (rings, homeomorphic),
  hence **`quatUnitsEquiv`**: $(\mathbb H\otimes\mathbb A)^\times\cong(\mathbb H\otimes F_\infty)^\times\times(\mathbb H\otimes\mathbb A_f)^\times$
  as topological groups.
* **`tamQuat a b`** $=\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ (`omegaQuatInf` × `muFinQuat`) transported to
  $(\mathbb H\otimes\mathbb A)^\times$: Weil's Tamagawa measure attached to $\omega = \|\operatorname{nrd}\|^{-2}dx$ and
  $(\lambda_v)$, without the global factor $\rho_F^{-1}$ (kept separate, as for `tamIdeles`). **`tamQuat_prod`**:
  $\mu(\{x : x_\infty\in A,\ x_f\in B\}) = \omega_\infty(A)\,\mu_f(B)$.
* **`muQuatOneTam a b`** = `muQuatOne (tamQuat a b)` on $\mathbb H_{\mathbb A}^1$ with
  `(tamQuat a b).map (quatSplit a b) = muQuatOneTam × dt/t` (**`map_quatSplit_tamQuat`**), and
  **`muQuatClassTam a b`** = `muQuatClass (tamQuat a b)` on $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$
  (independent of the fundamental domain, **`map_restrict_eq_muQuatClassTam`**). The general versions for an arbitrary
  Haar measure (`muQuatOne μ`, `muQuatClass μ`) are kept.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

set_option synthInstance.maxHeartbeats 400000

/-- **Units of homeomorphic rings**: a ring isomorphism that is a homeomorphism induces an isomorphism of topological
unit groups. -/
def unitsContinuousMulEquiv {R S : Type*} [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S]
    (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) : Rˣ ≃ₜ* Sˣ where
  toMulEquiv := Units.mapEquiv e.toMulEquiv
  continuous_toFun := Units.continuous_iff.mpr ⟨he.comp Units.continuous_val, he.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.mpr ⟨he'.comp Units.continuous_val, he'.comp Units.continuous_coe_inv⟩

variable (a b : F)

/-- $\mathbb H[\mathbb A_F]\cong\mathbb H[F_\infty]\times\mathbb H[\mathbb A_f]$ (coordinatewise). -/
def quatAdeleRingEquiv : QuatAdele a b ≃+* (QuatInf a b × QuatFin a b) where
  toFun x := (⟨x.re.1, x.imI.1, x.imJ.1, x.imK.1⟩, ⟨x.re.2, x.imI.2, x.imJ.2, x.imK.2⟩)
  invFun p := ⟨(p.1.re, p.2.re), (p.1.imI, p.2.imI), (p.1.imJ, p.2.imJ), (p.1.imK, p.2.imK)⟩
  left_inv x := rfl
  right_inv p := rfl
  map_mul' x y := by
    refine Prod.ext (QuaternionAlgebra.ext ?_ ?_ ?_ ?_) (QuaternionAlgebra.ext ?_ ?_ ?_ ?_) <;>
      simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
        QuaternionAlgebra.imK_mul]
  map_add' x y := by
    refine Prod.ext (QuaternionAlgebra.ext ?_ ?_ ?_ ?_) (QuaternionAlgebra.ext ?_ ?_ ?_ ?_) <;> simp

theorem continuous_quatAdeleRingEquiv : Continuous (quatAdeleRingEquiv a b) := by
  refine Continuous.prodMk ?_ ?_
  · refine (continuous_quatInf_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩
    · exact continuous_fst.comp (continuous_re a b)
    · exact continuous_fst.comp (continuous_imI a b)
    · exact continuous_fst.comp (continuous_imJ a b)
    · exact continuous_fst.comp (continuous_imK a b)
  · refine (continuous_quatFin_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩
    · exact continuous_snd.comp (continuous_re a b)
    · exact continuous_snd.comp (continuous_imI a b)
    · exact continuous_snd.comp (continuous_imJ a b)
    · exact continuous_snd.comp (continuous_imK a b)

theorem continuous_quatAdeleRingEquiv_symm : Continuous (quatAdeleRingEquiv a b).symm := by
  refine (continuous_quat_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩
  · exact ((continuous_ire a b).comp continuous_fst).prodMk ((continuous_fre a b).comp continuous_snd)
  · exact ((continuous_iimI a b).comp continuous_fst).prodMk ((continuous_fimI a b).comp continuous_snd)
  · exact ((continuous_iimJ a b).comp continuous_fst).prodMk ((continuous_fimJ a b).comp continuous_snd)
  · exact ((continuous_iimK a b).comp continuous_fst).prodMk ((continuous_fimK a b).comp continuous_snd)

/-- **$(\mathbb H\otimes\mathbb A)^\times\cong(\mathbb H\otimes F_\infty)^\times\times(\mathbb H\otimes\mathbb A_f)^\times$** as
topological groups. -/
def quatUnitsEquiv : (QuatAdele a b)ˣ ≃ₜ* ((QuatInf a b)ˣ × (QuatFin a b)ˣ) :=
  (unitsContinuousMulEquiv (quatAdeleRingEquiv a b) (continuous_quatAdeleRingEquiv a b)
    (continuous_quatAdeleRingEquiv_symm a b)).trans
  { toMulEquiv := MulEquiv.prodUnits
    continuous_toFun := Homeomorph.prodUnits.continuous
    continuous_invFun := Homeomorph.prodUnits.symm.continuous }

variable {a b}
variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

variable (a b) in
/-- **Weil's Tamagawa measure on $(\mathbb H\otimes\mathbb A)^\times$**: $\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$, with
$\omega = \|\operatorname{nrd}x\|^{-2}dx$ and $\lambda_v = 1 - N(v)^{-1}$ (the global factor $\rho_F^{-1}$ of AAG §2.3 is
kept separate). -/
def tamQuat : Measure (QuatAdele a b)ˣ := ((omegaQuatInf a b).prod (muFinQuat a b)).map (quatUnitsEquiv a b).symm

include ha hb ha0 hb0 in
/-- **`tamQuat` is a Haar measure.** -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure of A_𝔸^×, A = ℍ) [unverified page for A = ℍ]"]
theorem isHaarMeasure_tamQuat : (tamQuat a b).IsHaarMeasure := by
  have := isHaarMeasure_muFinQuat ha hb ha0 hb0
  rw [tamQuat]; infer_instance

/-- **`tamQuat` on boxes**: $\mu(\{x : x_\infty\in A,\ x_f\in B\}) = \omega_\infty(A)\cdot\mu_f(B)$. -/
theorem tamQuat_prod (A : Set (QuatInf a b)ˣ) (B : Set (QuatFin a b)ˣ) :
    tamQuat a b (quatUnitsEquiv a b ⁻¹' (A ×ˢ B)) = omegaQuatInf a b A * muFinQuat a b B := by
  have : ((quatUnitsEquiv a b).symm : _ → (QuatAdele a b)ˣ) =
      (quatUnitsEquiv a b).symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [tamQuat, this, MeasurableEquiv.map_apply]
  change ((omegaQuatInf a b).prod (muFinQuat a b)) ((quatUnitsEquiv a b).symm ⁻¹'
    (quatUnitsEquiv a b ⁻¹' (A ×ˢ B))) = _
  rw [← preimage_comp]
  have h2 : (quatUnitsEquiv a b ∘ (quatUnitsEquiv a b).symm) = id :=
    funext fun p => (quatUnitsEquiv a b).apply_symm_apply p
  have : SFinite (muFinQuat a b) := by unfold muFinQuat; infer_instance
  rw [h2, preimage_id, Measure.prod_prod]

/-! ### $\mathbb H_{\mathbb A}^1$ and $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$ for the canonical measure -/

include ha hb ha0 hb0 in
/-- The canonical Haar measure $\mu^1$ on $\mathbb H_{\mathbb A}^1$: `muQuatOne` of `tamQuat`. -/
def muQuatOneTam : Measure (quatOne a b) :=
  haveI := isHaarMeasure_tamQuat ha hb ha0 hb0
  muQuatOne (tamQuat a b)

include ha hb ha0 hb0 in
/-- **Measure splitting for the canonical measure**: `(tamQuat a b).map (quatSplit a b) = μ¹ × dt/t`. -/
@[kb "weil1982" "§2.3 [unverified page] (A_𝔸^× = A_𝔸^1 × ℝ_{>0}, A = ℍ, canonical Tamagawa measure)"]
theorem map_quatSplit_tamQuat :
    (tamQuat a b).map (quatSplit a b) = (muQuatOneTam ha hb ha0 hb0).prod dtt := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  exact map_quatSplit (tamQuat a b)

include ha hb ha0 hb0 in
theorem muQuatOneTam_apply (E : Set (quatOne a b)) :
    muQuatOneTam ha hb ha0 hb0 E = tamQuat a b (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  exact muQuatOne_apply (tamQuat a b) E

include ha hb ha0 hb0 in
/-- The canonical measure on $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$: `muQuatClass` of `tamQuat`. -/
def muQuatClassTam : Measure (QuatClassOne a b) :=
  haveI := isHaarMeasure_tamQuat ha hb ha0 hb0
  muQuatClass (tamQuat a b)

include ha hb ha0 hb0 in
/-- **The canonical quotient measure does not depend on the fundamental domain.** -/
theorem map_restrict_eq_muQuatClassTam {D : Set (quatOne a b)}
    (hD : IsFundamentalDomain (quatUnitsOne a b) D (muQuatOneTam ha hb ha0 hb0)) :
    ((muQuatOneTam ha hb ha0 hb0).restrict D).map (quatClassMk a b) = muQuatClassTam ha hb ha0 hb0 := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  exact map_restrict_eq_muQuatClass (tamQuat a b) hD

include ha hb ha0 hb0 in
theorem muQuatClassTam_univ {D : Set (quatOne a b)}
    (hD : IsFundamentalDomain (quatUnitsOne a b) D (muQuatOneTam ha hb ha0 hb0)) :
    muQuatClassTam ha hb ha0 hb0 univ = muQuatOneTam ha hb ha0 hb0 D := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  exact muQuatClass_univ (tamQuat a b) hD

end

end QuadFormsKB.Tamagawa.Measure.Weil
