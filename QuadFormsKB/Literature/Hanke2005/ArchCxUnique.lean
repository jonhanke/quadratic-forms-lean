/-
# Measures on an open set are determined by compactly supported test functions

Auxiliary measure theory for §4.3 of Hanke's thesis (`ArchVolumeComplex.lean`): Shimura's measure $\omega_Z$ on
$Z_{\mathbb C}$ is not locally finite on the ambient coordinate space (its density blows up at the boundary of $Z_{\mathbb C}$),
so the identification $(F_{\mathbb C})_*\widetilde\omega_G = c\,\omega_Z$ is made inside the open set $Z_{\mathbb C}$.

**Proves** `eq_of_lintegral_testFun_eq`: on a finite-dimensional real normed space, two measures that vanish off an open
set $O$ and give the same finite integral to every continuous, nonnegative, compactly supported $\varphi$ with
$\operatorname{tsupport}\varphi\subseteq O$ are equal. (Approximate $1_K$ for compact $K\subseteq O$ from above by such $\varphi$,
then use the $\pi$-system of compact subsets of $O$ and measurable subsets of $O^c$.)
-/
import Mathlib

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]

/-- Open sets are $\sigma$-compact. -/
theorem isSigmaCompact_of_isOpen {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have h := (isSigmaCompact_univ (X := U)).image continuous_subtype_val
  rwa [image_univ, Subtype.range_coe] at h

/-- The test function $\max(0, 1 - \operatorname{dist}(x, K)/r)$. -/
def bumpK (K : Set X) (r : ℝ) (x : X) : ℝ := max 0 (1 - infDist x K / r)

theorem continuous_bumpK (K : Set X) (r : ℝ) : Continuous (bumpK K r) :=
  continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))

theorem bumpK_nonneg (K : Set X) (r : ℝ) (x : X) : 0 ≤ bumpK K r x := le_max_left _ _

theorem bumpK_of_mem {K : Set X} {r : ℝ} {x : X} (hx : x ∈ K) : bumpK K r x = 1 := by
  simp [bumpK, infDist_zero_of_mem hx]

theorem bumpK_le_one (K : Set X) {r : ℝ} (hr : 0 < r) (x : X) : bumpK K r x ≤ 1 :=
  max_le zero_le_one (by have := infDist_nonneg (x := x) (s := K); have : 0 ≤ infDist x K / r := by positivity
                         linarith)

theorem tsupport_bumpK {K : Set X} (hK : K.Nonempty) {r : ℝ} (hr : 0 < r) :
    tsupport (bumpK K r) ⊆ cthickening r K := by
  refine closure_minimal (fun x hx => ?_) isClosed_cthickening
  refine thickening_subset_cthickening r K ((mem_thickening_iff_infDist_lt hK).mpr ?_)
  by_contra h
  rw [not_lt] at h
  apply hx
  refine max_eq_left ?_
  rw [sub_nonpos, le_div_iff₀ hr, one_mul]; exact h

theorem tendsto_bumpK {K : Set X} (hK : K.Nonempty) (hKc : IsClosed K) {δ : ℝ} (hδ : 0 < δ) (x : X) :
    Tendsto (fun m : ℕ => ENNReal.ofReal (bumpK K (δ / (m + 1)) x)) atTop (𝓝 (K.indicator 1 x)) := by
  by_cases hx : x ∈ K
  · simp [bumpK_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    have hpos : 0 < infDist x K := (hKc.notMem_iff_infDist_pos hK).mp hx
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (δ / infDist x K)
    filter_upwards [eventually_ge_atTop N] with m hm
    symm
    rw [ENNReal.ofReal_eq_zero]
    refine max_le le_rfl ?_
    have h1 : δ / infDist x K < m + 1 := by
      have : (N : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    rw [div_lt_iff₀ hpos] at h1
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    rw [sub_nonpos, div_div_eq_mul_div, le_div_iff₀ hδ, one_mul]
    linarith

theorem bumpK_mono {K : Set X} {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') (x : X) :
    bumpK K r x ≤ bumpK K r' x := by
  refine max_le_max le_rfl (sub_le_sub_left ?_ 1)
  exact div_le_div_of_nonneg_left infDist_nonneg hr hrr

/-- **Uniqueness from test functions.** Two measures vanishing off an open set $O$ that give the same finite integral
to every continuous, nonnegative, compactly supported $\varphi$ with support in $O$ are equal. -/
theorem eq_of_lintegral_testFun_eq {O : Set X} (hO : IsOpen O) {μ ν : Measure X} (hμ : μ Oᶜ = 0) (hν : ν Oᶜ = 0)
    (h : ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ x, 0 ≤ φ x) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂μ = ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ∧ ∫⁻ x, ENNReal.ofReal (φ x) ∂μ ≠ ∞) :
    μ = ν := by
  -- Step A: compact subsets of `O`
  have hA : ∀ K : Set X, IsCompact K → K ⊆ O → μ K = ν K ∧ μ K ≠ ∞ := by
    intro K hK hKO
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hO hKO
    have hcpt : IsCompact (cthickening δ K) := hK.cthickening
    have htest : ∀ r, 0 < r → r ≤ δ →
        ∫⁻ x, ENNReal.ofReal (bumpK K r x) ∂μ = ∫⁻ x, ENNReal.ofReal (bumpK K r x) ∂ν ∧
          ∫⁻ x, ENNReal.ofReal (bumpK K r x) ∂μ ≠ ∞ := by
      intro r hr hrδ
      have hts : tsupport (bumpK K r) ⊆ cthickening δ K :=
        (tsupport_bumpK hne hr).trans (cthickening_mono hrδ K)
      exact h _ (continuous_bumpK K r) (hcpt.of_isClosed_subset (isClosed_tsupport _) hts)
        (hts.trans hsub) (bumpK_nonneg K r)
    have hr : ∀ m : ℕ, 0 < δ / (m + 1) := fun m => by positivity
    have hrδ : ∀ m : ℕ, δ / (m + 1) ≤ δ := fun m => div_le_self hδ.le (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    have hlim : ∀ ρ : Measure X, ∫⁻ x, ENNReal.ofReal (bumpK K δ x) ∂ρ ≠ ∞ →
        Tendsto (fun m : ℕ => ∫⁻ x, ENNReal.ofReal (bumpK K (δ / (m + 1)) x) ∂ρ) atTop (𝓝 (ρ K)) := by
      intro ρ hfin
      rw [← lintegral_indicator_one hK.isClosed.measurableSet]
      refine tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (bumpK K δ x))
        (fun m => ENNReal.measurable_ofReal.comp (continuous_bumpK K _).measurable)
        (fun m => Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (bumpK_mono (hr m) (hrδ m) x))
        hfin (Filter.Eventually.of_forall fun x => tendsto_bumpK hne hK.isClosed hδ x)
    have hfinμ := (htest δ hδ le_rfl).2
    have hfinν : ∫⁻ x, ENNReal.ofReal (bumpK K δ x) ∂ν ≠ ∞ := by rw [← (htest δ hδ le_rfl).1]; exact hfinμ
    have e1 := hlim μ hfinμ
    have e2 := hlim ν hfinν
    have heq : (fun m : ℕ => ∫⁻ x, ENNReal.ofReal (bumpK K (δ / (m + 1)) x) ∂μ) =
        fun m : ℕ => ∫⁻ x, ENNReal.ofReal (bumpK K (δ / (m + 1)) x) ∂ν :=
      funext fun m => (htest _ (hr m) (hrδ m)).1
    rw [heq] at e1
    refine ⟨tendsto_nhds_unique e1 e2, ?_⟩
    refine ne_top_of_le_ne_top hfinμ ?_
    calc μ K = ∫⁻ x, K.indicator 1 x ∂μ := (lintegral_indicator_one hK.isClosed.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (bumpK K δ x) ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx, bumpK_of_mem hx]; simp
        · rw [indicator_of_notMem hx]; exact zero_le
  -- Step B: the π-system
  set C : Set (Set X) := {S | (IsCompact S ∧ S ⊆ O) ∨ (MeasurableSet S ∧ S ⊆ Oᶜ)} with hC
  have hpi : IsPiSystem C := by
    rintro s (⟨hs, hsO⟩ | ⟨hs, hsO⟩) t (⟨ht, htO⟩ | ⟨ht, htO⟩) hne
    · exact Or.inl ⟨hs.inter_right ht.isClosed, inter_subset_left.trans hsO⟩
    · exfalso; obtain ⟨x, hx1, hx2⟩ := hne; exact htO hx2 (hsO hx1)
    · exfalso; obtain ⟨x, hx1, hx2⟩ := hne; exact hsO hx1 (htO hx2)
    · exact Or.inr ⟨hs.inter ht, inter_subset_left.trans hsO⟩
  obtain ⟨Kseq, hKc, hKU⟩ := isSigmaCompact_of_isOpen hO
  have hKO : ∀ m, Kseq m ⊆ O := fun m => hKU ▸ subset_iUnion Kseq m
  have hgen : ‹MeasurableSpace X› = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ ?_
    · rw [BorelSpace.measurable_eq (α := X), borel]
      refine MeasurableSpace.generateFrom_le fun V hV => ?_
      have hVO : IsOpen (V ∩ O) := hV.inter hO
      obtain ⟨L, hLc, hLU⟩ := isSigmaCompact_of_isOpen hVO
      have h1 : MeasurableSet[MeasurableSpace.generateFrom C] (V ∩ O) := by
        rw [← hLU]
        refine MeasurableSet.iUnion fun m => MeasurableSpace.measurableSet_generateFrom ?_
        exact Or.inl ⟨hLc m, (hLU ▸ subset_iUnion L m).trans inter_subset_right⟩
      have h2 : MeasurableSet[MeasurableSpace.generateFrom C] (V ∩ Oᶜ) :=
        MeasurableSpace.measurableSet_generateFrom
          (Or.inr ⟨hV.measurableSet.inter hO.measurableSet.compl, inter_subset_right⟩)
      have : V = (V ∩ O) ∪ (V ∩ Oᶜ) := by rw [← inter_union_distrib_left, union_compl_self, inter_univ]
      rw [this]; exact h1.union h2
    · refine MeasurableSpace.generateFrom_le fun S hS => ?_
      rcases hS with ⟨hS, -⟩ | ⟨hS, -⟩
      · exact hS.isClosed.measurableSet
      · exact hS
  set B : ℕ → Set X := fun i => Nat.casesOn i Oᶜ Kseq with hB
  have hBU : ⋃ i, B i = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ O
    · rw [← hKU] at hx
      obtain ⟨m, hm⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨m + 1, hm⟩
    · exact mem_iUnion.mpr ⟨0, hx⟩
  have hBC : ∀ i, B i ∈ C := by
    intro i
    cases i with
    | zero => exact Or.inr ⟨hO.measurableSet.compl, subset_rfl⟩
    | succ m => exact Or.inl ⟨hKc m, hKO m⟩
  have hBfin : ∀ i, μ (B i) ≠ ∞ := by
    intro i
    cases i with
    | zero => show μ Oᶜ ≠ ∞; rw [hμ]; exact ENNReal.zero_ne_top
    | succ m => exact (hA _ (hKc m) (hKO m)).2
  refine Measure.ext_of_generateFrom_of_iUnion C B hgen hpi hBU hBC hBfin ?_
  rintro S (⟨hS, hSO⟩ | ⟨hS, hSO⟩)
  · exact (hA S hS hSO).1
  · rw [measure_mono_null hSO hμ, measure_mono_null hSO hν]

end QuadFormsKB.Hanke2005.ArchCx
