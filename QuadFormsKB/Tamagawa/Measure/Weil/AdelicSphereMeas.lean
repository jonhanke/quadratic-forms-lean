import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphere
import QuadFormsKB.Tamagawa.Measure.Weil.SphereMeasurable
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Adele

/-!
# Measurability of the adelic section and of the stabilizer embedding

For an `AdelicSphereSetup` $S$ (base point $\xi$, integral complement $G$, auxiliary vector $w$):

* **`measurable_sphereSection`**: the section $s : T(\rho)_{\mathbb A}\to SO(V)(\mathbb A)$ is measurable
  ($T(\rho)_{\mathbb A}$ with the subspace $\sigma$-algebra of $\mathbb A^N$). *Proof:* at each archimedean place
  $s$ is `secP` with the measurable branch $q(x + x_0)\ne0$, so `measurable_archSO_of`, `measurable_archSOC_of`
  apply; at each finite place it is `secP` with the branch $|q(x - x_0)|_v\le|q(x + x_0)|_v$, a measurable set
  (`measurableSet_valued_le`), so `measurable_orthGroup_of` applies, and `RestrictedProduct.measurable_of_forall_eval`
  assembles the finite places.
* **`measurable_iota`**: $\iota : SO(Q')(\mathbb A)\to SO(V)(\mathbb A)$ is measurable (indeed each coordinate is
  continuous: $h\mapsto G\,\mathrm{diag}(1,h)\,G^{-1}$, `continuous_conjBlockGL`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### Generic lemmas -/

section Generic

/-- **Continuous matrix-valued maps are measurable** (Borel structure on $M_n(K)$ as a product). -/
theorem measurable_of_continuous_matrix {K : Type*} [Field K] [TopologicalSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] {n : ℕ} {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] {f : T → Matrix (Fin n) (Fin n) K} (hf : Continuous f) : Measurable f := by
  have : BorelSpace (Matrix (Fin n) (Fin n) K) := inferInstanceAs (BorelSpace (Fin n → Fin n → K))
  exact hf.measurable

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {k : ℕ}

/-- $h\mapsto\mathrm{diag}(1, h)$ (`cornerMat 1 h`) is continuous. -/
theorem continuous_cornerMat_one :
    Continuous fun h : Matrix (Fin k) (Fin k) K => cornerMat (1 : K) h := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [cornerMat]; exact continuous_const
  · simp only [cornerMat]; exact continuous_const
  · simp only [cornerMat]; exact continuous_const
  · simp only [cornerMat]; exact (continuous_apply j).comp (continuous_apply i)

/-- $h\mapsto P\,\mathrm{diag}(1, h)\,P^{-1}$ is continuous on matrices. -/
theorem continuous_conjBlock (P : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    Continuous fun h : Matrix (Fin k) (Fin k) K => conjBlock P h := by
  unfold conjBlock
  exact (continuous_const.matrix_mul continuous_cornerMat_one).matrix_mul continuous_const

/-- **$h\mapsto G\,\mathrm{diag}(1,h)\,G^{-1}$ is continuous $\mathrm{GL}_k(K)\to\mathrm{GL}_{k+1}(K)$.** -/
theorem continuous_conjBlockGL (P : GL (Fin (k + 1)) K) : Continuous (conjBlockGL P) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_conjBlock P.val).comp Units.continuous_val).congr fun h =>
      (conjBlockGL_val P h).symm
  · refine ((continuous_conjBlock P.val).comp (Units.continuous_val.comp continuous_inv)).congr fun h => ?_
    simp only [Function.comp_apply]
    rw [← conjBlockGL_val, map_inv]

end Generic

/-- **$\{(a,b) : |a|_v\le|b|_v\}$ is measurable in $F_v\times F_v$.** -/
theorem measurableSet_valued_le {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet {p : v.adicCompletion F × v.adicCompletion F | Valued.v p.1 ≤ Valued.v p.2} := by
  have hU : MeasurableSet {x : v.adicCompletion F | Valued.v x ≤ 1} := by
    have := isOpen_latticeV_zero v
    rw [← coe_latticeV_zero] at *
    exact this.measurableSet
  have heq : {p : v.adicCompletion F × v.adicCompletion F | Valued.v p.1 ≤ Valued.v p.2} =
      {p | p.1 = 0} ∪ {p | p.2 ≠ 0} ∩ {p | p.1 * p.2⁻¹ ∈ {x : v.adicCompletion F | Valued.v x ≤ 1}} := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases ha : a = 0
      · exact Or.inl ha
      · have hb : b ≠ 0 := by
          rintro rfl
          rw [map_zero, le_zero_iff, map_eq_zero] at h
          exact ha h
        refine Or.inr ⟨hb, ?_⟩
        rw [← div_eq_mul_inv, map_div₀, div_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hb))]
        exact h
    · rintro (rfl | ⟨hb, h⟩)
      · simp
      · rw [← div_eq_mul_inv, map_div₀, div_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hb))] at h
        exact h
  rw [heq]
  exact (measurable_fst (measurableSet_singleton 0)).union
    ((measurable_snd (measurableSet_singleton (0 : v.adicCompletion F)).compl).inter
      ((measurable_fst.mul measurable_snd.inv) hU))

namespace AdelicSphereSetup

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}
  (S : AdelicSphereSetup Q₀ ρ)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- The finite-place branch is a measurable set. -/
theorem measurableSet_bFin (hρ : ρ ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet {x : Fin (k + 1) → v.adicCompletion F | S.bFin hρ v x} := by
  have h1 : Measurable fun x : Fin (k + 1) → v.adicCompletion F =>
      qH (hesAt Q₀ (σV v)) (x - (S.sphereDataAt hρ (σV v)).x₀) :=
    measurable_qH_comp (measurable_id.sub_const _)
  have h2 : Measurable fun x : Fin (k + 1) → v.adicCompletion F =>
      qH (hesAt Q₀ (σV v)) (x + (S.sphereDataAt hρ (σV v)).x₀) :=
    measurable_qH_comp (measurable_id.add_const _)
  exact (h1.prodMk h2) (measurableSet_valued_le v)

/-- The archimedean branch is a measurable set. -/
theorem measurableSet_bArch (hρ : ρ ≠ 0) {K : Type*} [Field K] [MeasurableSpace K] [MeasurableAdd₂ K]
    [MeasurableSub₂ K] [MeasurableMul₂ K] [MeasurableInv K] [MeasurableSingletonClass K] (σ : F →+* K) :
    MeasurableSet {x : Fin (k + 1) → K | S.bArch hρ σ x} :=
  (measurable_qH_comp (measurable_id.add_const _)) (measurableSet_singleton 0).compl

/-! #### Coordinates of the adelic sphere -/

theorem measurable_adR {n : ℕ} (Q : QuadForm (𝓞 F) n) (ρ' : F) (w : {w : InfinitePlace F // w.IsReal}) :
    Measurable fun y : adelicSphere Q ρ' => adR y.1 w :=
  measurable_pi_iff.2 fun j => Continuous.measurable
    ((continuous_apply w).comp (continuous_fst.comp (continuous_fst.comp
      ((continuous_apply j).comp continuous_subtype_val))))

theorem measurable_adC {n : ℕ} (Q : QuadForm (𝓞 F) n) (ρ' : F) (w : {w : InfinitePlace F // w.IsComplex}) :
    Measurable fun y : adelicSphere Q ρ' => adC y.1 w :=
  measurable_pi_iff.2 fun j => Continuous.measurable
    ((continuous_apply w).comp (continuous_snd.comp (continuous_fst.comp
      ((continuous_apply j).comp continuous_subtype_val))))

theorem measurable_adV {n : ℕ} (Q : QuadForm (𝓞 F) n) (ρ' : F) (v : HeightOneSpectrum (𝓞 F)) :
    Measurable fun y : adelicSphere Q ρ' => adV y.1 v :=
  measurable_pi_iff.2 fun j => Continuous.measurable
    ((RestrictedProduct.continuous_eval v).comp (continuous_snd.comp
      ((continuous_apply j).comp continuous_subtype_val)))

/-! #### The section -/

/-- **The archimedean part of the section is measurable.** -/
theorem measurable_secInf (hρ : ρ ≠ 0) : Measurable (S.secInf hρ) := by
  refine Measurable.prodMk ((@measurable_pi_iff _ _ (fun w : {w : InfinitePlace F // w.IsReal} => ArchSO (QRe Q₀ w)) _
      (fun w => ArchSO.instMeasurableSpace (QRe Q₀ w)) _).2 fun w => ?_)
    ((@measurable_pi_iff _ _ (fun w : {w : InfinitePlace F // w.IsComplex} => ArchSOC (QCx Q₀ w)) _
      (fun w => ArchSOC.instMeasurableSpace (QCx Q₀ w)) _).2 fun w => ?_)
  · refine measurable_archSO_of (f := fun y : adelicSphere Q₀ ρ => (S.secInf hρ y).1 w) ?_ ?_
    · exact (measurable_secP _ _ (S.measurableSet_bArch hρ (σR w))).comp (measurable_adR Q₀ ρ w)
    · exact (measurable_secPInv _ _ (S.measurableSet_bArch hρ (σR w))).comp (measurable_adR Q₀ ρ w)
  · refine measurable_archSOC_of (f := fun y : adelicSphere Q₀ ρ => (S.secInf hρ y).2 w) ?_ ?_
    · exact (measurable_secP _ _ (S.measurableSet_bArch hρ (σC w))).comp (measurable_adC Q₀ ρ w)
    · exact (measurable_secPInv _ _ (S.measurableSet_bArch hρ (σC w))).comp (measurable_adC Q₀ ρ w)

/-- **The finite part of the section is measurable** (into $O(V)(\mathbb A_f)$). -/
theorem measurable_secOAf (hρ : ρ ≠ 0) : Measurable (S.secOAf hρ) := by
  refine RestrictedProduct.measurable_of_forall_eval (fun v => isOpen_stdStab v QF) fun v => ?_
  refine measurable_orthGroup_of v (f := fun y : adelicSphere Q₀ ρ => S.secOAf hρ y v) ?_ ?_
  · exact (measurable_secP _ _ (S.measurableSet_bFin hρ v)).comp (measurable_adV Q₀ ρ v)
  · exact (measurable_secPInv _ _ (S.measurableSet_bFin hρ v)).comp (measurable_adV Q₀ ρ v)

/-- **The section $s : T(\rho)_{\mathbb A}\to SO(V)(\mathbb A)$ is measurable.** -/
theorem measurable_sphereSection (hρ : ρ ≠ 0) : Measurable (S.sphereSection hρ) :=
  (S.measurable_secInf hρ).prodMk (Measurable.subtype_mk (S.measurable_secOAf hρ))

/-! #### The stabilizer embedding -/

theorem measurable_iotaR (w : {w : InfinitePlace F // w.IsReal}) : Measurable (S.iotaR w) := by
  have hc : Continuous fun h : ArchSO (QRe S.C.Q' w) => conjBlockGL (S.PAt (σR w)) (ArchSO.incl _ h) :=
    (continuous_conjBlockGL _).comp (ArchSO.continuous_incl _)
  exact measurable_archSO_of (f := S.iotaR w)
    (measurable_of_continuous_matrix (Units.continuous_val.comp hc))
    (measurable_of_continuous_matrix (Units.continuous_val.comp (continuous_inv.comp hc)))

theorem measurable_iotaC (w : {w : InfinitePlace F // w.IsComplex}) : Measurable (S.iotaC w) := by
  have hc : Continuous fun h : ArchSOC (QCx S.C.Q' w) => conjBlockGL (S.PAt (σC w)) (ArchSOC.incl _ h) :=
    (continuous_conjBlockGL _).comp continuous_subtype_val
  exact measurable_archSOC_of (f := S.iotaC w)
    (measurable_of_continuous_matrix (Units.continuous_val.comp hc))
    (measurable_of_continuous_matrix (Units.continuous_val.comp (continuous_inv.comp hc)))

theorem measurable_iotaOAf : Measurable S.iotaOAf := by
  refine RestrictedProduct.measurable_of_forall_eval (fun v => isOpen_stdStab v QF) fun v => ?_
  have hc : Continuous fun h : OAf (S.C.Q'.map (algebraMap (𝓞 F) F)) =>
      conjBlockGL (S.PAt (σV v)) ((h v : orthGroup _ (v.adicCompletion F)) : GL (Fin k) (v.adicCompletion F)) :=
    (continuous_conjBlockGL _).comp (continuous_subtype_val.comp (RestrictedProduct.continuous_eval v))
  exact measurable_orthGroup_of v (f := fun h => S.iotaOAf h v)
    (measurable_of_continuous_matrix (Units.continuous_val.comp hc))
    (measurable_of_continuous_matrix (Units.continuous_val.comp (continuous_inv.comp hc)))

theorem measurable_iotaFin : Measurable S.iotaFin :=
  Measurable.subtype_mk (S.measurable_iotaOAf.comp measurable_subtype_coe)

/-- **The stabilizer embedding $\iota : SO(Q')(\mathbb A)\to SO(V)(\mathbb A)$ is measurable.** -/
theorem measurable_iota : Measurable S.iota := by
  have hR : Measurable (MonoidHom.piMap S.iotaR) :=
    (@measurable_pi_iff _ _ (fun w : {w : InfinitePlace F // w.IsReal} => ArchSO (QRe Q₀ w)) _
      (fun w => ArchSO.instMeasurableSpace (QRe Q₀ w)) _).2 fun w =>
      (S.measurable_iotaR w).comp (measurable_pi_apply w)
  have hC : Measurable (MonoidHom.piMap S.iotaC) :=
    (@measurable_pi_iff _ _ (fun w : {w : InfinitePlace F // w.IsComplex} => ArchSOC (QCx Q₀ w)) _
      (fun w => ArchSOC.instMeasurableSpace (QCx Q₀ w)) _).2 fun w =>
      (S.measurable_iotaC w).comp (measurable_pi_apply w)
  exact (hR.prodMap hC).prodMap S.measurable_iotaFin

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
