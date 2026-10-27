import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCont
import QuadFormsKB.Tamagawa.Measure.FibreConst
import QuadFormsKB.Tamagawa.Measure.LerayUnimodular
import QuadFormsKB.Tamagawa.Measure.LerayUnimodularC
import QuadFormsKB.Tamagawa.Measure.ProductSO

/-!
# Unimodularity of Weil's Tamagawa measure on $SO(V)(\mathbb A)$

**Layer:** number fields. $F$ is a number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables.

**Proves**
* `isMulRightInvariant_of_conj`: a Haar measure $\mu$ on a locally compact second countable Hausdorff group is right
  invariant as soon as $\mu(\{x : gxg^{-1}\in K\}) = \mu(K)$ for all $g$, for one compact set $K$ with nonempty interior
  (the modular character is $1$ because it is the ratio $\mu(Kg)/\mu(K)$);
* `isMulRightInvariant_muLoc`, `isMulRightInvariant_muLocSO`: the local Tamagawa measures on $O(V)(F_v)$ and
  $SO(V)(F_v)$ are right invariant (from `muLoc_conj_stdStab`, i.e. $\mu(hO(L_v)h^{-1}) = \mu(O(L_v))$);
* `isMulRightInvariant_muFin`: $\mu_f$ on $SO(V)(\mathbb A_f)$ is right invariant: $g^{-1}\,SO(\hat L)\,g$ is a box
  $\prod_{v\in S}g_v^{-1}K_vg_v\times\prod_{v\notin S}K_v$ of the same measure (`muFin_boxSO_haar`);
* `isMulRightInvariant_muArchTamSO`: the archimedean factor is right invariant (Leray measures, real and complex);
* `isMulRightInvariant_muTam`, **`map_inv_muTam`**, **`muTam_inv_preimage`**:
  $\mu_{\mathrm{Tam}}$ is right invariant and invariant under $g\mapsto g^{-1}$ (unimodularity of $SO(V)(\mathbb A)$).
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal RestrictedProduct Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.LerayArch

local instance locallyCompactSpace_SOAf_local {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm (𝓞 F) n) :
    LocallyCompactSpace (SOAf Q) :=
  (isClosed_soAf (Q.map (algebraMap (𝓞 F) F))).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### A criterion for right invariance -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- **Right invariance from conjugation invariance of one compact set.** A Haar measure $\mu$ on $G$ with
$\mu(\{x : gxg^{-1}\in K\}) = \mu(K)$ for all $g\in G$, for some compact $K$ with nonempty interior, is right invariant. -/
theorem isMulRightInvariant_of_conj (μ : Measure G) [IsHaarMeasure μ] (K : Set G) (hKc : IsCompact K)
    (hKi : (interior K).Nonempty) (h : ∀ g : G, μ {x | g * x * g⁻¹ ∈ K} = μ K) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have e := map_right_mul_eq_modularCharacterFun_smul μ g
  have hK0 : μ K ≠ 0 := (measure_pos_of_nonempty_interior μ hKi).ne'
  have hKt : μ K ≠ ∞ := hKc.measure_lt_top.ne
  have h1 : (map (· * g) μ) {y | y * g⁻¹ ∈ K} = μ K := by
    have := (Homeomorph.mulRight g).measurableEmbedding.map_apply μ {y | y * g⁻¹ ∈ K}
    refine this.trans ?_
    congr 1
    ext x; simp [Homeomorph.mulRight]
  have h2 : μ {y | y * g⁻¹ ∈ K} = μ K := by
    rw [← h g]
    exact (measure_preimage_mul μ g {y | y * g⁻¹ ∈ K}).symm
  rw [e, Measure.smul_apply, h2, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : (modularCharacterFun g : ℝ≥0) = 1 := by
    have h3 : ((modularCharacterFun g : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by rw [one_mul]; exact h1
    have h4 := (ENNReal.mul_left_inj hK0 hKt).1 h3
    exact_mod_cast h4
  rw [e, hc, one_smul]

/-- Conjugating a set by an element of a group with a bi-invariant measure preserves the measure. -/
theorem measure_conj_set_eq (μ : Measure G) [IsMulLeftInvariant μ] [IsMulRightInvariant μ] (g : G) (K : Set G) :
    μ {x | g * x * g⁻¹ ∈ K} = μ K := by
  have h1 := measure_preimage_mul μ g ((· * g⁻¹) ⁻¹' K)
  have h2 := measure_preimage_mul_right μ g⁻¹ K
  rw [← h2, ← h1]
  rfl

end Generic

/-! ### Local unimodularity -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)
local notation "Fv" => v.adicCompletion F

/-- **$\mu_v$ on $O(V)(F_v)$ is right invariant** (unimodularity of $O(V)(F_v)$ for the Haar measure `muLoc`). -/
theorem isMulRightInvariant_muLoc (hQ : Q₀.Nondegenerate) : (muLoc v Q₀ 1).IsMulRightInvariant := by
  haveI := isHaarMeasure_muLoc v Q₀ hQ one_pos
  refine isMulRightInvariant_of_conj _ (stdStab QF v : Set (orthGroup QF Fv)) (isCompact_stdStab v QF) ⟨1, ?_⟩ ?_
  · rw [(isOpen_stdStab v QF).interior_eq]; exact (stdStab QF v).one_mem
  · intro g
    have := FibreConst.muLoc_conj_stdStab v Q₀ hQ g⁻¹
    convert this using 2
    ext x
    simp only [Set.mem_ofPred_eq, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hx; exact ⟨g * x * g⁻¹, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      have : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
      rw [this]; exact hy

/-- **$\mu_v$ on $SO(V)(F_v)$ is right invariant** (the restriction of the right invariant `muLoc` to the open subgroup
$SO(V)(F_v)$, `muLocSO_eq_comap`). -/
theorem isMulRightInvariant_muLocSO (hQ : Q₀.Nondegenerate) (hn : 0 < n) :
    (muLocSO v Q₀ 1).IsMulRightInvariant := by
  haveI := isMulRightInvariant_muLoc v Q₀ hQ
  have hE := measurableEmbedding_soSub v Q₀ hQ
  rw [muLocSO_eq_comap v Q₀ hQ hn one_pos]
  refine ⟨fun g => ?_⟩
  ext S hS
  rw [map_apply (measurable_mul_const g) hS, hE.comap_apply, hE.comap_apply]
  have : Subtype.val '' ((fun x => x * g) ⁻¹' S) = (fun x => x * (g : orthGroup QF Fv)) ⁻¹' (Subtype.val '' S) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y * g, hy, rfl⟩
    · rintro ⟨z, hz, hxz⟩
      refine ⟨z * g⁻¹, by simpa using hz, ?_⟩
      have : (z : orthGroup QF Fv) = x * g := hxz
      show (z : orthGroup QF Fv) * (g : orthGroup QF Fv)⁻¹ = x
      rw [this]; group
  rw [this]
  exact measure_preimage_mul_right _ _ _

end Local

/-! ### The finite adelic factor -/

section Fin

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **$\mu_f$ on $SO(V)(\mathbb A_f)$ is right invariant** ($\lambda_v = 1$). -/
theorem isMulRightInvariant_muFin (hQ : Q₀.Nondegenerate) (hn : 0 < n) :
    (Measure.muFin Q₀ (fun _ => 1)).IsMulRightInvariant := by
  classical
  by_cases hc : Real.toNNReal (finFactor Q₀ (fun _ => 1)) = 0
  · have h0 : Measure.muFin Q₀ (fun _ => 1) = 0 := by
      unfold Measure.muFin haarNorm; rw [hc]; simp
    rw [h0]
    exact ⟨fun g => MeasureTheory.Measure.map_zero _⟩
  · have : IsHaarMeasure (Measure.muFin Q₀ (fun _ => 1)) := by
      unfold Measure.muFin haarNorm; exact IsHaarMeasure.nnreal_smul _ hc
    refine isMulRightInvariant_of_conj _ (KSO Q₀ : Set (SOAf Q₀)) (isCompact_KSO Q₀) ⟨1, ?_⟩ ?_
    · rw [(isOpen_KSO Q₀).interior_eq]; exact (KSO Q₀).one_mem
    intro g
    have hev : ∀ᶠ v in Filter.cofinite, evalSO Q₀ v g ∈ soStabSO v Q₀ := by
      have := (g : OAf QF).2
      filter_upwards [this] with v hv
      exact hv
    set S := (Filter.eventually_cofinite.mp hev).toFinset with hS
    have hgK : ∀ v, v ∉ S → evalSO Q₀ v g ∈ soStabSO v Q₀ := by
      intro v hv
      have : v ∉ {v | ¬ evalSO Q₀ v g ∈ soStabSO v Q₀} := by
        simpa [hS] using hv
      simpa using this
    set U : ∀ v, Set (SOv v Q₀) := fun v => {y | evalSO Q₀ v g * y * (evalSO Q₀ v g)⁻¹ ∈ soStabSO v Q₀} with hU
    have key : ∀ x : SOAf Q₀, (g * x * g⁻¹ ∈ KSO Q₀) ↔
        ∀ v, evalSO Q₀ v g * evalSO Q₀ v x * (evalSO Q₀ v g)⁻¹ ∈ soStabSO v Q₀ := by
      intro x
      rw [mem_KSO_iff]
      simp only [map_mul, map_inv, SetLike.mem_coe]
    have hbox : {x | g * x * g⁻¹ ∈ (KSO Q₀ : Set (SOAf Q₀))} = boxSO Q₀ S U := by
      ext x
      show g * x * g⁻¹ ∈ KSO Q₀ ↔ _
      rw [key]
      simp only [boxSO, hU, Set.mem_ofPred_eq, SetLike.mem_coe]
      constructor
      · intro hx
        refine ⟨fun v _ => hx v, fun v hv => ?_⟩
        have hg := hgK v hv
        have := (soStabSO v Q₀).mul_mem ((soStabSO v Q₀).mul_mem ((soStabSO v Q₀).inv_mem hg) (hx v)) hg
        simpa [mul_assoc] using this
      · rintro ⟨h1, h2⟩ v
        by_cases hv : v ∈ S
        · exact h1 v hv
        · have hg := hgK v hv
          exact (soStabSO v Q₀).mul_mem ((soStabSO v Q₀).mul_mem hg (h2 v hv)) ((soStabSO v Q₀).inv_mem hg)
    have hUm : ∀ v ∈ S, MeasurableSet (U v) := by
      intro v _
      refine IsOpen.measurableSet ?_
      exact (isOpen_soStabSO v Q₀).preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    have hone : ∀ v ∈ S, haarSO Q₀ v (U v) = 1 := by
      intro v _
      haveI := isMulRightInvariant_muLocSO v Q₀ hQ hn
      haveI : (muLocSO v Q₀ 1).IsMulLeftInvariant := by unfold muLocSO; infer_instance
      rw [haarSO_eq_div Q₀ hQ v one_pos]
      have hconj := measure_conj_set_eq (muLocSO v Q₀ 1) (evalSO Q₀ v g) (soStabSO v Q₀ : Set (SOv v Q₀))
      have : muLocSO v Q₀ 1 (U v) = muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) := hconj
      rw [this]
      exact ENNReal.div_self (muLocSO_soStabSO_pos Q₀ hQ v one_pos)
        (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
    rw [hbox, Measure.muFin_boxSO_haar Q₀ _ S U hUm, Finset.prod_eq_one hone, mul_one, Measure.muFin_KSO]

end Fin

/-! ### The archimedean factor -/

section Arch

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

/-- **The archimedean Tamagawa factor is right invariant** (real and complex Leray measures are, and products of right
invariant measures are). -/
theorem isMulRightInvariant_muArchTamSO (hQ : Q₀.Nondegenerate) : (muArchTamSO Q₀ hQ).IsMulRightInvariant := by
  have hR := gramDetR_QRe_ne_zero Q₀ hQ
  have hC := gramDetC_QCx_ne_zero Q₀ hQ
  have h1 : ∀ w : {w : InfinitePlace F // w.IsReal},
      (LerayReal.lerayMeasure (QuadForm.map (embedding_of_isReal w.2) (QuadForm.map (algebraMap (𝓞 F) F) Q₀))
        (hR w)).IsMulRightInvariant := fun w => LerayReal.isMulRightInvariant_lerayMeasure (hR w)
  have h2 : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (lerayMeasureC (QuadForm.map w.1.embedding (QuadForm.map (algebraMap (𝓞 F) F) Q₀))
        (hC w)).IsMulRightInvariant := fun w => isMulRightInvariant_lerayMeasureC (hC w)
  have hs1 : ∀ w : {w : InfinitePlace F // w.IsReal},
      SigmaFinite (LerayReal.lerayMeasure (QuadForm.map (embedding_of_isReal w.2) (QuadForm.map (algebraMap (𝓞 F) F) Q₀))
        (hR w)) := fun w => by
    have := LerayReal.isHaarMeasure_lerayMeasure (hR w); infer_instance
  have hs2 : ∀ w : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (lerayMeasureC (QuadForm.map w.1.embedding (QuadForm.map (algebraMap (𝓞 F) F) Q₀))
        (hC w)) := fun w => by
    have := isHaarMeasure_lerayMeasureC (hC w); infer_instance
  have hp1 : (Measure.pi fun w : {w : InfinitePlace F // w.IsReal} =>
      LerayReal.lerayMeasure (QuadForm.map (embedding_of_isReal w.2) (QuadForm.map (algebraMap (𝓞 F) F) Q₀))
        (hR w)).IsMulRightInvariant := Measure.pi.isMulRightInvariant _
  have hp2 : (Measure.pi fun w : {w : InfinitePlace F // w.IsComplex} =>
      lerayMeasureC (QuadForm.map w.1.embedding (QuadForm.map (algebraMap (𝓞 F) F) Q₀))
        (hC w)).IsMulRightInvariant := Measure.pi.isMulRightInvariant _
  unfold muArchTamSO LerayArch.muArchNF LerayArch.muArchLeray
  rw [ofReal_smul_eq]
  infer_instance

end Arch

/-! ### The Tamagawa measure -/

section Tam

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

/-- **$\mu_{\mathrm{Tam}}$ is right invariant** on $SO(V)(\mathbb A)$ (with $\lambda_v = 1$, $n > 0$). -/
theorem isMulRightInvariant_muTam (hQ : Q₀.Nondegenerate) (hn : 0 < n) :
    (muTam Q₀ hQ (fun _ => 1)).IsMulRightInvariant := by
  haveI := isMulRightInvariant_muArchTamSO Q₀ hQ
  haveI := isMulRightInvariant_muFin Q₀ hQ hn
  unfold muTam
  infer_instance

/-- A right invariant Haar measure is inversion invariant (unimodular locally compact second countable groups). -/
theorem map_inv_eq_of_isMulRightInvariant {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] [IsMulRightInvariant μ] : μ.map (fun g => g⁻¹) = μ := by
  set c := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : μ = (c * c) • μ := by
    conv_lhs => rw [← Measure.inv_inv μ, hc]
    rw [Measure.inv_def, Measure.map_smul _ measurable_inv.aemeasurable, ← Measure.inv_def, hc, smul_smul]
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h0 : μ K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    conv_rhs => rw [one_mul, h2]
    rfl
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0 ht).1 h3
  have h5 : c = 1 := by
    have h6 : (c : ℝ) * c = 1 := by exact_mod_cast h4
    have h7 : ((c : ℝ) - 1) * ((c : ℝ) + 1) = 0 := by linear_combination h6
    have h8 : (c : ℝ) + 1 ≠ 0 := by positivity
    have h9 : (c : ℝ) = 1 := by linarith [(mul_eq_zero.mp h7).resolve_right h8]
    exact_mod_cast h9
  rw [← Measure.inv_def, hc, h5, one_smul]

/-- **$\mu_{\mathrm{Tam}}$ is invariant under inversion** $g\mapsto g^{-1}$ on $SO(V)(\mathbb A)$ ($\lambda_v = 1$, $n > 0$):
$SO(V)(\mathbb A)$ is unimodular for Weil's Tamagawa measure. -/
theorem map_inv_muTam (hQ : Q₀.Nondegenerate) (hn0 : n ≠ 0) :
    (muTam Q₀ hQ (fun _ => 1)).map (fun g => g⁻¹) = muTam Q₀ hQ (fun _ => 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hc : Real.toNNReal (finFactor Q₀ (fun _ => 1)) = 0
  · have h0 : Measure.muFin Q₀ (fun _ => 1) = 0 := by
      unfold Measure.muFin haarNorm; rw [hc]; simp
    have : muTam Q₀ hQ (fun _ => 1) = 0 := by
      unfold muTam; rw [h0, Measure.prod_zero]
    rw [this, Measure.map_zero]
  · haveI : (muArchTamSO Q₀ hQ).IsHaarMeasure := by
      have := LerayArch.isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ)
        (gramDetC_QCx_ne_zero Q₀ hQ)
      unfold muArchTamSO LerayArch.muArchNF
      rw [ofReal_smul_eq]
      exact IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr (mul_pos cF_pos' cxWeil_pos)).ne'
    haveI : (Measure.muFin Q₀ (fun _ => 1)).IsHaarMeasure := by
      unfold Measure.muFin haarNorm; exact IsHaarMeasure.nnreal_smul _ hc
    haveI : (muTam Q₀ hQ (fun _ => 1)).IsHaarMeasure := by
      unfold muTam; infer_instance
    haveI := isMulRightInvariant_muTam Q₀ hQ hn
    exact map_inv_eq_of_isMulRightInvariant _

/-- **Set form of `map_inv_muTam`:** $\mu_{\mathrm{Tam}}(E^{-1}) = \mu_{\mathrm{Tam}}(E)$ for every measurable $E$. -/
theorem muTam_inv_preimage (hQ : Q₀.Nondegenerate) (hn0 : n ≠ 0) (E : Set (SOAdele Q₀)) (hE : MeasurableSet E) :
    muTam Q₀ hQ (fun _ => 1) ((fun g => g⁻¹) ⁻¹' E) = muTam Q₀ hQ (fun _ => 1) E := by
  conv_rhs => rw [← map_inv_muTam Q₀ hQ hn0]
  rw [Measure.map_apply measurable_inv hE]

end Tam

end QuadFormsKB.Tamagawa.Measure.Weil

end
