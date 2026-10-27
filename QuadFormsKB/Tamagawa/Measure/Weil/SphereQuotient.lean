import Mathlib
import QuadFormsKB.Citation

/-!
# The quotient measure on $H\backslash G$ in orbit coordinates

**Generic, Mathlib-only (upstreamable).** $H$ is a locally compact second countable group with a nonzero left-invariant
measure $\mu'$ finite on compact sets; $G$ is a group with a measure $\mu$; $\iota : H\to G$ a homomorphism; $T$ a measurable
space and $\mathrm{coord} : T\times H\simeq G$ a measurable equivalence of **orbit shape**
$$\mathrm{coord}(x, h'h) = \iota(h')\,\mathrm{coord}(x, h)$$
(for $G$ acting on $T$ with stabilizer $\iota(H)$ and a section $s$: $\mathrm{coord}(x, h) = \iota(h)s(x)^{-1}$). If $\mu$ is
invariant under left translation by $\iota(H)$ and $T$ is covered by countably many measurable sets $A_i$ with
$\mu(\mathrm{coord}(A_i\times K)) < \infty$ for every compact $K\subseteq H$, then (**`map_prod_quotMeasure`**)
$$\mu = \mathrm{coord}_*(\sigma\otimes\mu'),\qquad \sigma(A) = \frac{\mu(\mathrm{coord}(A\times U))}{\mu'(U)}
  \quad(\texttt{quotMeasure}),$$
for any measurable $U$ with $0 < \mu'(U) < \infty$; $\sigma$ is $\sigma$-finite (`sigmaFinite_quotMeasure`), and
(**`quotMeasure_mul`**) $\sigma(A)\,\mu'(B) = \mu(\mathrm{coord}(A\times B))$ for all measurable $A$, $B$.

This is Weil's quotient measure on $H\backslash G$ (Weil 1982, Lemma 2.4.1, Thm 2.4.3 [unverified page]) in the form needed
for the adelic sphere: no unimodularity, no regularity of $\mu$, only Haar uniqueness on $H$ (Mathlib's
`isMulLeftInvariant_eq_smul`) applied to $B\mapsto\mu(\mathrm{coord}(A\times B))$.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {T H G : Type*} [MeasurableSpace T] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [Group G] [MeasurableSpace G]

/-- **The quotient measure** $\sigma(A) = \mu(\mathrm{coord}(A\times U))/\mu'(U)$ on $T$ (Weil's measure on $H\backslash G$ in
orbit coordinates). Parameters: the coordinates `coord`, the measure `μ` on $G$, a set `U` of $H$ and the measure `μ'` on
$H$. -/
def quotMeasure (coord : T × H ≃ᵐ G) (μ : Measure G) (U : Set H) (μ' : Measure H) : Measure T :=
  (μ' U)⁻¹ • ((μ.map coord.symm).restrict (univ ×ˢ U)).map Prod.fst

theorem quotMeasure_apply (coord : T × H ≃ᵐ G) (μ : Measure G) {U : Set H} (hU : MeasurableSet U)
    (μ' : Measure H) {A : Set T} (hA : MeasurableSet A) :
    quotMeasure coord μ U μ' A = (μ' U)⁻¹ * μ (coord.symm ⁻¹' (A ×ˢ U)) := by
  rw [quotMeasure, Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA), Measure.map_apply coord.symm.measurable
      ((measurable_fst hA).inter (MeasurableSet.univ.prod hU))]
  congr 2
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and]

/-- The fibre measure $B\mapsto\mu(\mathrm{coord}(A\times B))$ on $H$. -/
def fibreOf (coord : T × H ≃ᵐ G) (μ : Measure G) (A : Set T) : Measure H :=
  ((μ.map coord.symm).restrict (A ×ˢ univ)).map Prod.snd

theorem fibreOf_apply (coord : T × H ≃ᵐ G) (μ : Measure G) {A : Set T} (hA : MeasurableSet A) {B : Set H}
    (hB : MeasurableSet B) : fibreOf coord μ A B = μ (coord.symm ⁻¹' (A ×ˢ B)) := by
  rw [fibreOf, Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB),
    Measure.map_apply coord.symm.measurable ((measurable_snd hB).inter (hA.prod MeasurableSet.univ))]
  congr 2
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
  exact and_comm

variable (coord : T × H ≃ᵐ G) (ι : H →* G)
  (hmul : ∀ (x : T) (h h' : H), coord (x, h' * h) = ι h' * coord (x, h))
  (μ : Measure G) (hμ : ∀ (h' : H) (E : Set G), MeasurableSet E → μ ((fun g => ι h' * g) ⁻¹' E) = μ E)

include hmul hμ in
/-- The fibre measure is left invariant. -/
theorem fibreOf_isMulLeftInvariant {A : Set T} (hA : MeasurableSet A) :
    (fibreOf coord μ A).IsMulLeftInvariant := by
  refine ⟨fun h' => ?_⟩
  ext B hB
  rw [Measure.map_apply (measurable_const_mul h') hB, fibreOf_apply coord μ hA hB,
    fibreOf_apply coord μ hA ((measurable_const_mul h') hB)]
  have hE : MeasurableSet (coord.symm ⁻¹' (A ×ˢ B)) := coord.symm.measurable (hA.prod hB)
  rw [← hμ h' _ hE]
  congr 1
  ext g
  simp only [mem_preimage, mem_prod]
  obtain ⟨⟨x, h⟩, rfl⟩ := coord.surjective g
  rw [← hmul, MeasurableEquiv.symm_apply_apply, MeasurableEquiv.symm_apply_apply]

/-- A measure on $H$ that is left invariant and finite on compacts is a multiple of a fixed Haar measure. -/
theorem eq_smul_haar (ν : Measure H) [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] :
    ν = haarScalarFactor ν Measure.haar • Measure.haar :=
  isMulLeftInvariant_eq_smul ν Measure.haar

variable (μ' : Measure H) [μ'.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ']

include hmul hμ in
/-- **The fibre measure over a set of finite type is $\sigma(A)\mu'$.** If $\mu(\mathrm{coord}(A\times K)) < \infty$ for every
compact $K$, then $\mu(\mathrm{coord}(A\times B)) = \frac{\mu(\mathrm{coord}(A\times U))}{\mu'(U)}\,\mu'(B)$. -/
theorem fibreOf_eq_of_fin (hμ'0 : μ' ≠ 0) {U : Set H} (hU : MeasurableSet U) (hU0 : μ' U ≠ 0) (hUt : μ' U ≠ ∞)
    {A : Set T} (hA : MeasurableSet A)
    (hfin : ∀ K : Set H, IsCompact K → μ (coord.symm ⁻¹' (A ×ˢ K)) ≠ ∞) {B : Set H} (hB : MeasurableSet B) :
    μ (coord.symm ⁻¹' (A ×ˢ B)) = quotMeasure coord μ U μ' A * μ' B := by
  have := fibreOf_isMulLeftInvariant coord ι hmul μ hμ hA
  have : IsFiniteMeasureOnCompacts (fibreOf coord μ A) :=
    ⟨fun K hK => by
      rw [fibreOf_apply coord μ hA hK.measurableSet, lt_top_iff_ne_top]; exact hfin K hK⟩
  have h1 := eq_smul_haar (fibreOf coord μ A)
  have h2 := eq_smul_haar μ'
  set c := haarScalarFactor (fibreOf coord μ A) Measure.haar
  set c' := haarScalarFactor μ' Measure.haar
  have hc' : (c' : ℝ≥0∞) ≠ 0 := by
    intro h0
    apply hμ'0
    rw [h2, ENNReal.coe_eq_zero.mp h0, zero_smul]
  have hUv : μ' U = c' * Measure.haar U := by
    conv_lhs => rw [h2]
    rfl
  have hH0 : Measure.haar U ≠ 0 := by
    intro h0; apply hU0; rw [hUv, h0, mul_zero]
  have hHt : Measure.haar U ≠ ∞ := by
    intro h0; apply hUt; rw [hUv, h0, ENNReal.mul_top hc']
  rw [← fibreOf_apply coord μ hA hB, quotMeasure_apply coord μ hU μ' hA, ← fibreOf_apply coord μ hA hU,
    h1, Measure.smul_apply, Measure.smul_apply, hUv]
  simp only [nnreal_smul_coe_apply]
  conv_rhs => rw [h2]
  simp only [Measure.smul_apply, nnreal_smul_coe_apply]
  rw [ENNReal.mul_inv (Or.inl hc') (Or.inl ENNReal.coe_ne_top)]
  calc (c : ℝ≥0∞) * Measure.haar B
      = (c : ℝ≥0∞) * (Measure.haar U * (Measure.haar U)⁻¹) * ((c' : ℝ≥0∞)⁻¹ * c') * Measure.haar B := by
        rw [ENNReal.mul_inv_cancel hH0 hHt, ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, mul_one, mul_one]
    _ = (c' : ℝ≥0∞)⁻¹ * (Measure.haar U)⁻¹ * (c * Measure.haar U) * (c' * Measure.haar B) := by ring

variable (hμ'0 : μ' ≠ 0) {U : Set H} (hU : MeasurableSet U) (hU0 : μ' U ≠ 0) (hUt : μ' U ≠ ∞)
  (A : ℕ → Set T) (hAm : ∀ i, MeasurableSet (A i)) (hAu : ⋃ i, A i = univ)
  (hfin : ∀ i (K : Set H), IsCompact K → μ (coord.symm ⁻¹' (A i ×ˢ K)) ≠ ∞)

include hmul hμ hμ'0 hU hU0 hUt hAm hAu hfin in
/-- **The product formula on rectangles**: $\mu(\mathrm{coord}(A	imes B)) = \sigma(A)\,\mu'(B)$ for all measurable
$A\subseteq T$, $B\subseteq H$. -/
theorem quotMeasure_mul {B : Set H} (hB : MeasurableSet B) {E : Set T} (hE : MeasurableSet E) :
    μ (coord.symm ⁻¹' (E ×ˢ B)) = quotMeasure coord μ U μ' E * μ' B := by
  set D := disjointed A
  have hDm : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hAm
  have hDu : ⋃ i, D i = univ := by rw [iUnion_disjointed, hAu]
  have hDd : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed A
  have hpiece : ∀ i, μ (coord.symm ⁻¹' ((E ∩ D i) ×ˢ B)) = quotMeasure coord μ U μ' (E ∩ D i) * μ' B := by
    intro i
    refine fibreOf_eq_of_fin coord ι hmul μ hμ μ' hμ'0 hU hU0 hUt (hE.inter (hDm i)) (fun K hK => ?_) hB
    refine ne_top_of_le_ne_top (hfin i K hK) (measure_mono ?_)
    exact preimage_mono (prod_mono ((inter_subset_right).trans (disjointed_subset A i)) le_rfl)
  have hE' : E = ⋃ i, E ∩ D i := by rw [← inter_iUnion, hDu, inter_univ]
  have hdisj : Pairwise (Function.onFun Disjoint fun i => E ∩ D i) := fun i j hij =>
    (hDd hij).mono inter_subset_right inter_subset_right
  have hdisj' : Pairwise (Function.onFun Disjoint fun i => coord.symm ⁻¹' ((E ∩ D i) ×ˢ B)) := fun i j hij =>
    ((hdisj hij).set_prod_left B B).preimage _
  conv_lhs => rw [hE', iUnion_prod_const, preimage_iUnion]
  conv_rhs => rw [hE']
  rw [measure_iUnion hdisj' fun i => coord.symm.measurable ((hE.inter (hDm i)).prod hB),
    measure_iUnion hdisj fun i => hE.inter (hDm i), ← ENNReal.tsum_mul_right]
  exact tsum_congr hpiece

include hmul hμ hμ'0 hU hU0 hUt hAm hAu hfin in
/-- **The quotient measure is $\sigma$-finite** (finite on each $A_i$). -/
theorem sigmaFinite_quotMeasure : SigmaFinite (quotMeasure coord μ U μ') := by
  refine sigmaFinite_of_countable (S := range A) (countable_range A) ?_ (by rw [sUnion_range, hAu])
  rintro _ ⟨i, rfl⟩
  have h := quotMeasure_mul coord ι hmul μ hμ μ' hμ'0 hU hU0 hUt A hAm hAu hfin hU (hAm i)
  have hc : IsCompact (∅ : Set H) := isCompact_empty
  -- σ(A_i) μ'(U) = μ(coord(A_i × U)); use a compact neighbourhood instead of U for finiteness
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have hKpos : μ' K ≠ 0 := by
    intro h0
    apply hμ'0
    have hH := eq_smul_haar μ'
    have hpos : 0 < (Measure.haar : Measure H) K :=
      (Measure.haar : Measure H).measure_pos_of_mem_nhds hK1
    have : (haarScalarFactor μ' Measure.haar : ℝ≥0∞) = 0 := by
      rw [hH, Measure.smul_apply, nnreal_smul_coe_apply] at h0
      exact (mul_eq_zero.mp h0).resolve_right hpos.ne'
    rw [hH, ENNReal.coe_eq_zero.mp this, zero_smul]
  have hK := quotMeasure_mul coord ι hmul μ hμ μ' hμ'0 hU hU0 hUt A hAm hAu hfin hKc.measurableSet (hAm i)
  have hKt : μ' K ≠ ∞ := hKc.measure_lt_top.ne
  have hfi := hfin i K hKc
  rw [hK] at hfi
  rw [lt_top_iff_ne_top]
  intro htop
  rw [htop, ENNReal.top_mul hKpos] at hfi
  exact hfi rfl

include hmul hμ hμ'0 hU hU0 hUt hAm hAu hfin in
/-- **Weil's fibration identity** $\mu = \mathrm{coord}_*(\sigma\otimes\mu')$ for the quotient measure $\sigma$ =
`quotMeasure coord μ U μ'`. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page] (quotient measure on G/H)"]
theorem map_prod_quotMeasure : μ = ((quotMeasure coord μ U μ').prod μ').map coord := by
  have := sigmaFinite_quotMeasure coord ι hmul μ hμ μ' hμ'0 hU hU0 hUt A hAm hAu hfin
  have hprod : (quotMeasure coord μ U μ').prod μ' = μ.map coord.symm := by
    refine Measure.prod_eq fun E B hE hB => ?_
    rw [Measure.map_apply coord.symm.measurable (hE.prod hB)]
    exact quotMeasure_mul coord ι hmul μ hμ μ' hμ'0 hU hU0 hUt A hAm hAu hfin hB hE
  rw [hprod, Measure.map_map coord.measurable coord.symm.measurable]
  simp

end QuadFormsKB.Tamagawa.Measure.Weil
