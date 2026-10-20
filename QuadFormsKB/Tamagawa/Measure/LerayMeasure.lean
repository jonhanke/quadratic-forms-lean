import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.LerayStable

/-!
# The Leray measures $\sigma_\rho$ at a finite place

For a nondegenerate form $Q$ over $\mathcal O_v$ in $n$ variables and every $\rho \in F_v$ (including $\rho = 0$), the
**Leray measure** $\sigma_\rho$ on $V_v \smallsetminus \{0\}$, $V_v = F_v^n$, is the limit
$$\sigma_\rho(U) = \lim_{k\to\infty}\lambda_{\rho,k}(U) = \lim_{k\to\infty}\frac{\mathrm{vol}(U \cap Q^{-1}(\rho + \mathfrak p^k))}{\nu(\mathfrak p^k)}
\qquad (U \text{ compact open},\ 0 \notin U)$$
(the limit exists, `LerayStable.lean`). It is constructed from this additive content on the ring $C_0$ of compact open sets
avoiding $0$ by Carathéodory's theorem (Mathlib's `AddContent.measure`; $\sigma$-subadditivity is compactness). It is supported
on $\{Q = \rho\}$ and is the measure $dx/dQ$: for $\rho = 0$ it lives on the punctured null cone $C^\circ_v$, for $\rho \ne 0$ on the
sphere $T(\rho)_v$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal Pointwise
open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure.LerayThick QuadFormsKB.Tamagawa.Measure.LerayCone
open QuadFormsKB.Tamagawa.Measure.LerayFinite

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayFinite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The ring $C_0$ of compact open subsets of $V_v$ avoiding $0$.** -/
def Cz (n : ℕ) : Set (Set (Fin n → Fv)) := {U | IsCompact U ∧ IsOpen U ∧ (0 : Fin n → Fv) ∉ U}

theorem isSetRing_Cz : IsSetRing (Cz v n) where
  empty_mem := ⟨isCompact_empty, isOpen_empty, by simp⟩
  union_mem := fun s t hs ht => ⟨hs.1.union ht.1, hs.2.1.union ht.2.1, by simp [hs.2.2, ht.2.2]⟩
  sdiff_mem := fun s t hs ht =>
    ⟨hs.1.diff ht.2.1, hs.2.1.sdiff ht.1.isClosed, fun h => hs.2.2 h.1⟩

section Content

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure] (Q : QuadForm (v.adicCompletionIntegers F) n) (hQ : Q.Nondegenerate)

/-- **The Leray limit** $\ell_\rho(U) = \lim_k\lambda_{\rho,k}(U)$ (meaningful on $C_0$). -/
def lerayLim (ρ : Fv) (U : Set (Fin n → Fv)) : ℝ≥0∞ :=
  limUnder atTop fun k : ℕ => lerayThick ν (Qv v Q) (shell v ρ k) U

include hQ in
theorem exists_stable (ρ : Fv) {U : Set (Fin n → Fv)} (hU : U ∈ Cz v n) :
    ∀ᶠ k : ℕ in atTop, lerayThick ν (Qv v Q) (shell v ρ k) U = lerayLim v ν Q ρ U := by
  obtain ⟨k₀, hk₀⟩ := lerayThick_eventually_succ v ν Q hQ hU.1 hU.2.1 hU.2.2
  have hconst : ∀ k ≥ k₀, lerayThick ν (Qv v Q) (shell v ρ k) U = lerayThick ν (Qv v Q) (shell v ρ k₀) U := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [← hk₀ ρ k hk, ih]
  have hev : ∀ᶠ k : ℕ in atTop, lerayThick ν (Qv v Q) (shell v ρ k) U = lerayThick ν (Qv v Q) (shell v ρ k₀) U :=
    Filter.eventually_atTop.mpr ⟨k₀, hconst⟩
  have hlim : lerayLim v ν Q ρ U = lerayThick ν (Qv v Q) (shell v ρ k₀) U := by
    refine Tendsto.limUnder_eq ?_
    exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)
  exact hev.mono fun k hk => hk.trans hlim.symm

include hQ in
theorem lerayLim_empty (ρ : Fv) : lerayLim v ν Q ρ ∅ = 0 := by
  refine Tendsto.limUnder_eq ?_
  simp

include hQ in
theorem lerayLim_sUnion (ρ : Fv) (I : Finset (Set (Fin n → Fv))) (hI : ↑I ⊆ Cz v n)
    (hdis : (↑I : Set (Set (Fin n → Fv))).PairwiseDisjoint id) (hmem : ⋃₀ (↑I : Set (Set (Fin n → Fv))) ∈ Cz v n) :
    lerayLim v ν Q ρ (⋃₀ (↑I : Set (Set (Fin n → Fv)))) = ∑ u ∈ I, lerayLim v ν Q ρ u := by
  have h1 : ∀ᶠ k : ℕ in atTop, ∀ u ∈ I, lerayThick ν (Qv v Q) (shell v ρ k) u = lerayLim v ν Q ρ u :=
    (Filter.eventually_all_finset I).mpr fun u hu => exists_stable v ν Q hQ ρ (hI hu)
  have h2 := exists_stable v ν Q hQ ρ hmem
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  rw [← hk2]
  have hmeas : ∀ u ∈ I, MeasurableSet u := fun u hu => (hI hu).2.1.measurableSet
  have : ⋃₀ (↑I : Set (Set (Fin n → Fv))) = ⋃ u ∈ I, u := by simp [Set.sUnion_eq_biUnion]
  rw [this]
  have hm := measure_biUnion_finset (μ := lerayThick ν (Qv v Q) (shell v ρ k)) hdis hmeas
  simp only [id] at hm
  rw [hm]
  exact Finset.sum_congr rfl fun u hu => hk1 u hu

/-- **The Leray content** on the ring $C_0$. -/
def lerayContent (ρ : Fv) : AddContent ℝ≥0∞ (Cz v n) where
  toFun := lerayLim v ν Q ρ
  empty' := lerayLim_empty v ν Q hQ ρ
  sUnion' := fun I hI hd hm => lerayLim_sUnion v ν Q hQ ρ I hI hd hm

include hQ in
/-- **$\sigma$-subadditivity** (compactness: a compact open set covered by countably many opens needs finitely many). -/
theorem lerayContent_isSigmaSubadditive (ρ : Fv) : (lerayContent v ν Q hQ ρ).IsSigmaSubadditive := by
  intro f hf hU
  obtain ⟨t, ht⟩ := hU.1.elim_finite_subcover f (fun i => (hf i).2.1) subset_rfl
  have heq : (⋃ i, f i) = ⋃ i ∈ t, f i :=
    Set.Subset.antisymm ht (Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i)
  calc lerayContent v ν Q hQ ρ (⋃ i, f i) = lerayContent v ν Q hQ ρ (⋃ i ∈ t, f i) := by rw [← heq]
    _ ≤ ∑ i ∈ t, lerayContent v ν Q hQ ρ (f i) :=
        addContent_biUnion_le (isSetRing_Cz v) (fun i _ => hf i)
    _ ≤ ∑' i, lerayContent v ν Q hQ ρ (f i) := ENNReal.sum_le_tsum t

end Content

section Generation

lemma exists_cosetP_subset {O : Set (Fin n → Fv)} (hO : IsOpen O) {x : Fin n → Fv} (hx : x ∈ O) :
    ∃ s : ℕ, cosetP v x s ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO x hx
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one hε (norm_ϖ_lt_one v)
  refine ⟨s, fun y hy => hball ?_⟩
  rw [cosetP_eq, Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt hy hs

lemma cosetP_mem_Cz {O : Set (Fin n → Fv)} (h0 : (0 : Fin n → Fv) ∉ O) {x : Fin n → Fv} {s : ℕ}
    (h : cosetP v x s ⊆ O) : cosetP v x s ∈ Cz v n :=
  ⟨by rw [cosetP_eq]; exact isCompact_closedBall _ _, isOpen_cosetP v x s, fun h' => h0 (h h')⟩

/-- An open set avoiding $0$ is a countable union of members of $C_0$. -/
theorem exists_countable_union_Cz {O : Set (Fin n → Fv)} (hO : IsOpen O) (h0 : (0 : Fin n → Fv) ∉ O) :
    ∃ (T : Set (Fin n → Fv)) (s : (Fin n → Fv) → ℕ), T.Countable ∧ T ⊆ O ∧
      (∀ x ∈ T, cosetP v x (s x) ∈ Cz v n) ∧ O = ⋃ x ∈ T, cosetP v x (s x) := by
  choose! s hs using fun x (hx : x ∈ O) => exists_cosetP_subset v hO hx
  obtain ⟨T, hTO, hTc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := O)
    (f := fun x => cosetP v x (s x)) fun x hx =>
      mem_nhdsWithin_of_mem_nhds ((isOpen_cosetP v x _).mem_nhds (mem_cosetP_self v x _))
  refine ⟨T, s, hTc, hTO, fun x hx => cosetP_mem_Cz v h0 (hs x (hTO hx)), ?_⟩
  apply Set.Subset.antisymm hcov
  exact Set.iUnion₂_subset fun x hx => hs x (hTO hx)

/-- **The ring $C_0$ generates the Borel $\sigma$-algebra of $V_v$.** -/
theorem measurableSpace_eq_generateFrom_Cz :
    (inferInstance : MeasurableSpace (Fin n → Fv)) = MeasurableSpace.generateFrom (Cz v n) := by
  apply le_antisymm
  · have hopen : ∀ O : Set (Fin n → Fv), IsOpen O → (0 : Fin n → Fv) ∉ O →
        MeasurableSet[MeasurableSpace.generateFrom (Cz v n)] O := by
      intro O hO h0
      obtain ⟨T, s, hT, -, hmem, hOeq⟩ := exists_countable_union_Cz v hO h0
      rw [hOeq]
      exact MeasurableSet.biUnion hT fun x hx => MeasurableSpace.measurableSet_generateFrom (hmem x hx)
    have h1 : MeasurableSet[MeasurableSpace.generateFrom (Cz v n)] ({0}ᶜ : Set (Fin n → Fv)) :=
      hopen _ isClosed_singleton.isOpen_compl (by simp)
    have h2 : MeasurableSet[MeasurableSpace.generateFrom (Cz v n)] ({0} : Set (Fin n → Fv)) := by
      simpa using h1.compl
    rw [BorelSpace.measurable_eq (α := Fin n → Fv), borel]
    refine MeasurableSpace.generateFrom_le fun O hO => ?_
    have hO' : IsOpen O := hO
    have : O = (O ∩ {0}ᶜ) ∪ (O ∩ {0}) := by
      ext x; by_cases hx : x = 0 <;> simp [hx]
    rw [this]
    refine (hopen _ (hO'.inter isClosed_singleton.isOpen_compl) (by simp)).union ?_
    by_cases h0O : (0 : Fin n → Fv) ∈ O
    · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h0O)]; exact h2
    · rw [Set.inter_singleton_eq_empty.mpr h0O]; exact (MeasurableSpace.generateFrom (Cz v n)).measurableSet_empty
  · refine MeasurableSpace.generateFrom_le fun U hU => hU.2.1.measurableSet

end Generation

section Measure

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure] (Q : QuadForm (v.adicCompletionIntegers F) n)
  (hQ : Q.Nondegenerate)

/-- The Carathéodory measure of the Leray content (it gives $\infty$ to $\{0\}$, which is not covered by $C_0$). -/
def lerayMeasureRaw (ρ : Fv) : Measure (Fin n → Fv) :=
  (lerayContent v ν Q hQ ρ).measure (isSetRing_Cz v).isSetSemiring (measurableSpace_eq_generateFrom_Cz v).le
    (lerayContent_isSigmaSubadditive v ν Q hQ ρ)

/-- **The Leray measure $\sigma_\rho$ on $V_v\smallsetminus\{0\}$** (extended by $0$ at the origin): for $\rho \ne 0$ the
measure $dx/dQ$ on the sphere $T(\rho)_v$, for $\rho = 0$ on the punctured null cone $C^\circ_v$. -/
def lerayMeasure (ρ : Fv) : Measure (Fin n → Fv) := (lerayMeasureRaw v ν Q hQ ρ).restrict {(0 : Fin n → Fv)}ᶜ

/-- **Defining property**: $\sigma_\rho(U) = \lim_k\lambda_{\rho,k}(U)$ for compact open $U \not\ni 0$. -/
theorem lerayMeasure_apply (ρ : Fv) {U : Set (Fin n → Fv)} (hU : U ∈ Cz v n) :
    lerayMeasure v ν Q hQ ρ U = lerayLim v ν Q ρ U := by
  have hsub : U ⊆ {(0 : Fin n → Fv)}ᶜ := fun x hx hx0 => hU.2.2 (by rwa [Set.mem_singleton_iff.mp hx0] at hx)
  rw [lerayMeasure, Measure.restrict_apply hU.2.1.measurableSet, Set.inter_eq_left.mpr hsub]
  exact AddContent.measure_eq _ _ (measurableSpace_eq_generateFrom_Cz v) _ hU

theorem lerayMeasure_eventually (ρ : Fv) {U : Set (Fin n → Fv)} (hU : U ∈ Cz v n) :
    ∀ᶠ k : ℕ in atTop, lerayThick ν (Qv v Q) (shell v ρ k) U = lerayMeasure v ν Q hQ ρ U := by
  rw [lerayMeasure_apply v ν Q hQ ρ hU]
  exact exists_stable v ν Q hQ ρ hU

theorem lerayMeasure_singleton_zero (ρ : Fv) : lerayMeasure v ν Q hQ ρ {(0 : Fin n → Fv)} = 0 := by
  rw [lerayMeasure, Measure.restrict_apply (measurableSet_singleton _)]
  simp

theorem lerayMeasure_lt_top (ρ : Fv) {U : Set (Fin n → Fv)} (hU : U ∈ Cz v n) :
    lerayMeasure v ν Q hQ ρ U < ⊤ := by
  obtain ⟨k, hk⟩ := (lerayMeasure_eventually v ν Q hQ ρ hU).exists
  rw [← hk, lerayThick_apply ν _ _ hU.2.1.measurableSet]
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (measure_shell_pos v ν ρ k)) ?_
  refine lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_
  exact hU.1.measure_lt_top

end Measure

end QuadFormsKB.Tamagawa.Measure.LerayFinite
