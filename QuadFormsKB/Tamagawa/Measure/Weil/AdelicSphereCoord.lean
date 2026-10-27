import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereFib
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereMeas
import QuadFormsKB.Tamagawa.Measure.Weil.NormalFibration

/-!
# Orbit coordinates $T(\rho)_{\mathbb A}\times SO(Q')(\mathbb A)\cong SO(V)(\mathbb A)$

For the setup of `AdelicSphere.lean`:

* `smul_mem_adelicSphere`: $SO(V)(\mathbb A)$ preserves the adelic sphere; `ξA_mem`: $\xi\in T(\rho)_{\mathbb A}$.
* **`coordFun`** $(x, h)\mapsto\iota(h)\,s(x)^{-1}$, a measurable bijection (`coordFun_bijective`, `measurable_coordFun`);
* **`coordEquiv`**: it is a measurable equivalence (Lusin–Souslin: a measurable bijection from a standard Borel space
  to a countably separated one; `adelicSphere` is closed in the Polish space $\mathbb A^N$).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

theorem qH_mulVec_of_orth {R : Type*} [Field R] {n : ℕ} {H M : Matrix (Fin n) (Fin n) R} (hM : Mᵀ * H * M = H)
    (x : Fin n → R) : qH H (M *ᵥ x) = qH H x := by
  unfold qH
  rw [dotProduct_comm (M *ᵥ x), ← dotProduct_transpose_mulVec, mulVec_mulVec, mulVec_mulVec, hM]

/-- An additive LCSC Hausdorff group is Polish. -/
theorem polishSpace_of_isTopologicalAddGroup (G : Type*) [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] : PolishSpace G := by
  let _ := IsTopologicalAddGroup.rightUniformSpace G
  have : IsRightUniformAddGroup G := { toIsTopologicalAddGroup := ‹_›, uniformity_eq := rfl }
  have : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have : (_root_.uniformity G).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  infer_instance

local notation "AF" => FiniteAdeleRing (𝓞 F) F

instance polishSpace_finiteAdeleRing : PolishSpace AF := polishSpace_of_isTopologicalAddGroup AF

instance polishSpace_adeles : PolishSpace (Adeles F) := inferInstance

instance polishSpace_adeleSpace {n : ℕ} : PolishSpace (AdeleSpace F (Fin n)) :=
  { toSecondCountableTopology := inferInstanceAs (SecondCountableTopology (Fin n → Adeles F)),
    toIsCompletelyMetrizableSpace := inferInstanceAs (TopologicalSpace.IsCompletelyMetrizableSpace (Fin n → Adeles F)) }

instance locallyCompactSpace_SOAf' {n : ℕ} (Q : QuadForm (𝓞 F) n) : LocallyCompactSpace (SOAf Q) :=
  (isClosed_soAf (Q.map (algebraMap (𝓞 F) F))).isClosedEmbedding_subtypeVal.locallyCompactSpace

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem continuous_qH {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) : Continuous (qH H) := by
  unfold qH dotProduct mulVec dotProduct
  fun_prop

theorem isClosed_adelicSphere : IsClosed (adelicSphere Q₀ ρ) := by
  simp only [adelicSphere, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun w => ?_).inter ((isClosed_iInter fun w => ?_).inter (isClosed_iInter fun v => ?_))
  · exact isClosed_eq ((continuous_qH _).comp (continuous_pi fun j =>
      (continuous_apply w).comp (continuous_fst.comp (continuous_fst.comp (continuous_apply j))))) continuous_const
  · exact isClosed_eq ((continuous_qH _).comp (continuous_pi fun j =>
      (continuous_apply w).comp (continuous_snd.comp (continuous_fst.comp (continuous_apply j))))) continuous_const
  · exact isClosed_eq ((continuous_qH _).comp (continuous_pi fun j =>
      (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply j)))) continuous_const

instance standardBorel_adelicSphere : StandardBorelSpace (adelicSphere Q₀ ρ) := by
  have : PolishSpace (adelicSphere Q₀ ρ) := isClosed_adelicSphere.polishSpace
  have : BorelSpace (AdeleSpace F (Fin (k + 1))) := inferInstance
  have : BorelSpace (adelicSphere Q₀ ρ) := inferInstance
  infer_instance

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)

/-- **$SO(V)(\mathbb A)$ preserves the adelic sphere.** -/
theorem smul_mem_adelicSphere (g : SOAdele Q₀) {y : AdeleSpace F (Fin (k + 1))} (hy : y ∈ adelicSphere Q₀ ρ) :
    g • y ∈ adelicSphere Q₀ ρ := by
  refine ⟨fun w => ?_, fun w => ?_, fun v => ?_⟩
  · rw [← hy.1 w]
    exact qH_mulVec_of_orth (hes_of_mem_soReal Q₀ (σR w) (g.1.1 w).2).1 (adR y w)
  · rw [← hy.2.1 w]
    exact qH_mulVec_of_orth (hes_of_mem_soC Q₀ (σC w) (g.1.2 w).2).1 (adC y w)
  · rw [← hy.2.2 v]
    exact qH_mulVec_of_orth ((mem_orthGroup _).mp ((g.2 : OAf QF) v).2) (adV y v)

/-- $\xi\in T(\rho)_{\mathbb A}$. -/
theorem ξA_mem : S.ξA ∈ adelicSphere Q₀ ρ := by
  refine ⟨fun w => ?_, fun w => ?_, fun v => ?_⟩
  · exact (qH_hesAt_map Q₀ (σR w) S.ξ.1).trans (congrArg _ S.qH_ξ)
  · exact (qH_hesAt_map Q₀ (σC w) S.ξ.1).trans (congrArg _ S.qH_ξ)
  · exact (qH_hesAt_map Q₀ (σV v) S.ξ.1).trans (congrArg _ S.qH_ξ)

/-- **The orbit coordinates** $(x, h)\mapsto\iota(h)\,s(x)^{-1}$. -/
def coordFun (p : adelicSphere Q₀ ρ × SOAdele S.C.Q') : SOAdele Q₀ := S.iota p.2 * (S.sphereSection hρ p.1)⁻¹

theorem coordFun_inv_smul (p : adelicSphere Q₀ ρ × SOAdele S.C.Q') : (S.coordFun hρ p)⁻¹ • S.ξA = p.1.1 := by
  rw [coordFun, _root_.mul_inv_rev, inv_inv, mul_smul, inv_smul_eq_iff.mpr (S.iota_smul_ξA hρ p.2).symm,
    S.sphereSection_smul]

theorem coordFun_mul (x : adelicSphere Q₀ ρ) (h h' : SOAdele S.C.Q') :
    S.coordFun hρ (x, h' * h) = S.iota h' * S.coordFun hρ (x, h) := by
  simp only [coordFun, map_mul, mul_assoc]

theorem coordFun_injective : Function.Injective (S.coordFun hρ) := by
  rintro ⟨x, h⟩ ⟨x', h'⟩ e
  have hx : x = x' := Subtype.ext (by
    rw [← S.coordFun_inv_smul hρ (x, h), ← S.coordFun_inv_smul hρ (x', h'), e])
  subst hx
  simp only [coordFun, mul_left_inj] at e
  rw [S.iota_injective e]

theorem coordFun_surjective : Function.Surjective (S.coordFun hρ) := by
  intro g
  set x : adelicSphere Q₀ ρ := ⟨g⁻¹ • S.ξA, smul_mem_adelicSphere g⁻¹ S.ξA_mem⟩
  have hfix : (g * S.sphereSection hρ x) • S.ξA = S.ξA := by
    rw [mul_smul, S.sphereSection_smul, smul_inv_smul]
  obtain ⟨h, hh⟩ := S.exists_iota_eq hρ hfix
  exact ⟨(x, h), by rw [coordFun, hh, mul_inv_cancel_right]⟩

theorem measurable_coordFun : Measurable (S.coordFun hρ) :=
  (S.measurable_iota.comp measurable_snd).mul ((S.measurable_sphereSection hρ).comp measurable_fst).inv

/-- **The orbit coordinates as a measurable equivalence** (Lusin–Souslin). -/
def coordEquiv : adelicSphere Q₀ ρ × SOAdele S.C.Q' ≃ᵐ SOAdele Q₀ where
  toEquiv := Equiv.ofBijective (S.coordFun hρ) ⟨S.coordFun_injective hρ, S.coordFun_surjective hρ⟩
  measurable_toFun := S.measurable_coordFun hρ
  measurable_invFun := by
    have := polishSpace_of_isTopologicalGroup (SOAdele S.C.Q')
    have hemb := (S.measurable_coordFun hρ).measurableEmbedding (S.coordFun_injective hρ)
    intro A hA
    have : (Equiv.ofBijective (S.coordFun hρ) ⟨S.coordFun_injective hρ, S.coordFun_surjective hρ⟩).symm ⁻¹' A =
        S.coordFun hρ '' A := by
      ext g
      simp only [mem_preimage, mem_image]
      constructor
      · intro hg
        exact ⟨_, hg, Equiv.ofBijective_apply_symm_apply _ _ _⟩
      · rintro ⟨p, hp, rfl⟩
        convert hp; exact Equiv.ofBijective_symm_apply_apply _ _ p
    rw [this]
    exact hemb.measurableSet_image.mpr hA

theorem coordEquiv_apply (p : adelicSphere Q₀ ρ × SOAdele S.C.Q') : S.coordEquiv hρ p = S.coordFun hρ p := rfl

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
