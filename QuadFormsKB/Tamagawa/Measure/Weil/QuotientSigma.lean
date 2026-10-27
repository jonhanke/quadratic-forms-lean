import Mathlib
import QuadFormsKB.Citation

/-!
# The quotient measure in orbit coordinates, $\sigma$-finite version

**Generic, Mathlib-only (upstreamable).** The variant of `SphereQuotient.lean` without any topology on the fibre group:
$H$ is a group with measurable multiplication and inversion and a nonzero **$\sigma$-finite** left-invariant measure $\mu'$
(e.g. a subgroup of a locally compact group with a pushed-forward product measure, as the parabolic subgroup
$P = N\rtimes SO(V')$ of the cone). With $\mathrm{coord} : T\times H\simeq G$ of orbit shape
$\mathrm{coord}(x, h'h) = \iota(h')\,\mathrm{coord}(x, h)$, $\mu$ invariant under left translation by $\iota(H)$, and countable
measurable covers $(A_i)$ of $T$ and $(K_j)$ of $H$ with $\mu(\mathrm{coord}(A_i\times K_j)) < \infty$:

* **`quotMeasureσ_mul`**: $\sigma(A)\,\mu'(B) = \mu(\mathrm{coord}(A\times B))$, $\sigma(A) = \mu(\mathrm{coord}(A\times U))/\mu'(U)$;
* **`sigmaFinite_quotMeasureσ`**: $\sigma$ is $\sigma$-finite;
* **`map_prod_quotMeasureσ`**: $\mu = \mathrm{coord}_*(\sigma\otimes\mu')$.

Uniqueness of left-invariant $\sigma$-finite measures on a measurable group (Halmos; Mathlib's `measure_eq_div_smul`)
replaces Haar uniqueness on a locally compact group.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {T H G : Type*} [MeasurableSpace T] [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  [Group G] [MeasurableSpace G]

/-- **The quotient measure** $\sigma(A) = \mu(\mathrm{coord}(A\times U))/\mu'(U)$ on $T$ (same formula as `quotMeasure`). -/
def quotMeasureσ (coord : T × H ≃ᵐ G) (μ : Measure G) (U : Set H) (μ' : Measure H) : Measure T :=
  (μ' U)⁻¹ • ((μ.map coord.symm).restrict (univ ×ˢ U)).map Prod.fst

theorem quotMeasureσ_apply (coord : T × H ≃ᵐ G) (μ : Measure G) {U : Set H} (hU : MeasurableSet U)
    (μ' : Measure H) {A : Set T} (hA : MeasurableSet A) :
    quotMeasureσ coord μ U μ' A = (μ' U)⁻¹ * μ (coord.symm ⁻¹' (A ×ˢ U)) := by
  rw [quotMeasureσ, Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA), Measure.map_apply coord.symm.measurable
      ((measurable_fst hA).inter (MeasurableSet.univ.prod hU))]
  congr 2
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and]

/-- The fibre measure $B\mapsto\mu(\mathrm{coord}(A\times B))$ on $H$. -/
def fibreOfσ (coord : T × H ≃ᵐ G) (μ : Measure G) (A : Set T) : Measure H :=
  ((μ.map coord.symm).restrict (A ×ˢ univ)).map Prod.snd

theorem fibreOfσ_apply (coord : T × H ≃ᵐ G) (μ : Measure G) {A : Set T} (hA : MeasurableSet A) {B : Set H}
    (hB : MeasurableSet B) : fibreOfσ coord μ A B = μ (coord.symm ⁻¹' (A ×ˢ B)) := by
  rw [fibreOfσ, Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB),
    Measure.map_apply coord.symm.measurable ((measurable_snd hB).inter (hA.prod MeasurableSet.univ))]
  congr 2
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
  exact and_comm

variable (coord : T × H ≃ᵐ G) (ι : H →* G)
  (hmul : ∀ (x : T) (h h' : H), coord (x, h' * h) = ι h' * coord (x, h))
  (μ : Measure G) (hμ : ∀ (h' : H) (E : Set G), MeasurableSet E → μ ((fun g => ι h' * g) ⁻¹' E) = μ E)

include hmul hμ in
theorem fibreOfσ_isMulLeftInvariant {A : Set T} (hA : MeasurableSet A) :
    (fibreOfσ coord μ A).IsMulLeftInvariant := by
  refine ⟨fun h' => ?_⟩
  ext B hB
  rw [Measure.map_apply (measurable_const_mul h') hB, fibreOfσ_apply coord μ hA hB,
    fibreOfσ_apply coord μ hA ((measurable_const_mul h') hB)]
  have hE : MeasurableSet (coord.symm ⁻¹' (A ×ˢ B)) := coord.symm.measurable (hA.prod hB)
  rw [← hμ h' _ hE]
  congr 1
  ext g
  simp only [mem_preimage, mem_prod]
  obtain ⟨⟨x, h⟩, rfl⟩ := coord.surjective g
  rw [← hmul, MeasurableEquiv.symm_apply_apply, MeasurableEquiv.symm_apply_apply]

variable (μ' : Measure H) [SigmaFinite μ'] [μ'.IsMulLeftInvariant]
  (hμ'0 : μ' ≠ 0) {U : Set H} (hU : MeasurableSet U) (hU0 : μ' U ≠ 0) (hUt : μ' U ≠ ∞)
  (A : ℕ → Set T) (hAm : ∀ i, MeasurableSet (A i)) (hAu : ⋃ i, A i = univ)
  (K : ℕ → Set H) (hKm : ∀ j, MeasurableSet (K j)) (hKu : ⋃ j, K j = univ)
  (hfin : ∀ i j, μ (coord.symm ⁻¹' (A i ×ˢ K j)) ≠ ∞)

include hmul hμ hU hU0 hUt hKm hKu in
/-- **The fibre measure over a set of finite type is $\sigma(A)\mu'$.** -/
theorem fibreOfσ_eq_of_fin {E : Set T} (hE : MeasurableSet E)
    (hfinE : ∀ j, μ (coord.symm ⁻¹' (E ×ˢ K j)) ≠ ∞) {B : Set H} (hB : MeasurableSet B) :
    μ (coord.symm ⁻¹' (E ×ˢ B)) = quotMeasureσ coord μ U μ' E * μ' B := by
  have := fibreOfσ_isMulLeftInvariant coord ι hmul μ hμ hE
  have : SigmaFinite (fibreOfσ coord μ E) := by
    refine sigmaFinite_of_countable (S := range K) (countable_range K) ?_ (by rw [sUnion_range, hKu])
    rintro _ ⟨j, rfl⟩
    rw [fibreOfσ_apply coord μ hE (hKm j), lt_top_iff_ne_top]
    exact hfinE j
  have h1 := measure_eq_div_smul (fibreOfσ coord μ E) μ' hU0 hUt
  rw [← fibreOfσ_apply coord μ hE hB, h1, Measure.smul_apply, smul_eq_mul, quotMeasureσ_apply coord μ hU μ' hE,
    fibreOfσ_apply coord μ hE hU, ENNReal.div_eq_inv_mul]

include hmul hμ hU hU0 hUt hAm hAu hKm hKu hfin in
/-- **The product formula on rectangles**: $\mu(\mathrm{coord}(E\times B)) = \sigma(E)\,\mu'(B)$. -/
theorem quotMeasureσ_mul {B : Set H} (hB : MeasurableSet B) {E : Set T} (hE : MeasurableSet E) :
    μ (coord.symm ⁻¹' (E ×ˢ B)) = quotMeasureσ coord μ U μ' E * μ' B := by
  set D := disjointed A
  have hDm : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hAm
  have hDu : ⋃ i, D i = univ := by rw [iUnion_disjointed, hAu]
  have hDd : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed A
  have hpiece : ∀ i, μ (coord.symm ⁻¹' ((E ∩ D i) ×ˢ B)) = quotMeasureσ coord μ U μ' (E ∩ D i) * μ' B := by
    intro i
    refine fibreOfσ_eq_of_fin coord ι hmul μ hμ μ' hU hU0 hUt K hKm hKu (hE.inter (hDm i)) (fun j => ?_) hB
    refine ne_top_of_le_ne_top (hfin i j) (measure_mono ?_)
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

include hmul hμ hμ'0 hU hU0 hUt hAm hAu hKm hKu hfin in
/-- **The quotient measure is $\sigma$-finite.** -/
theorem sigmaFinite_quotMeasureσ : SigmaFinite (quotMeasureσ coord μ U μ') := by
  refine sigmaFinite_of_countable (S := range A) (countable_range A) ?_ (by rw [sUnion_range, hAu])
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, μ' (K j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hμ'0
    refine Measure.measure_univ_eq_zero.mp ?_
    rw [← hKu]
    exact measure_iUnion_null h
  have h := quotMeasureσ_mul coord ι hmul μ hμ μ' hU hU0 hUt A hAm hAu K hKm hKu hfin (hKm j) (hAm i)
  have hfi := hfin i j
  rw [h] at hfi
  rw [lt_top_iff_ne_top]
  intro htop
  rw [htop, ENNReal.top_mul hj] at hfi
  exact hfi rfl

include hmul hμ hμ'0 hU hU0 hUt hAm hAu hKm hKu hfin in
/-- **Weil's fibration identity** $\mu = \mathrm{coord}_*(\sigma\otimes\mu')$ for the quotient measure. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page] (quotient measure on G/H)"]
theorem map_prod_quotMeasureσ : μ = ((quotMeasureσ coord μ U μ').prod μ').map coord := by
  have := sigmaFinite_quotMeasureσ coord ι hmul μ hμ μ' hμ'0 hU hU0 hUt A hAm hAu K hKm hKu hfin
  have hprod : (quotMeasureσ coord μ U μ').prod μ' = μ.map coord.symm := by
    refine Measure.prod_eq fun E B hE hB => ?_
    rw [Measure.map_apply coord.symm.measurable (hE.prod hB)]
    exact quotMeasureσ_mul coord ι hmul μ hμ μ' hU hU0 hUt A hAm hAu K hKm hKu hfin hB hE
  rw [hprod, Measure.map_map coord.measurable coord.symm.measurable]
  simp

end QuadFormsKB.Tamagawa.Measure.Weil
