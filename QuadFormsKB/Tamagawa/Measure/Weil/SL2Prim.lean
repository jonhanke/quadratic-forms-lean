import QuadFormsKB.Tamagawa.Measure.Weil.SL2Section
import QuadFormsKB.Analysis.NFEulerProduct

/-!
# Almost every vector of $\mathbb A_F^2$ is primitive

$F$ any number field. **`muAddVec_compl_primSet`**: the set `primSet F` of primitive vectors (the image of the orbit
map $g\mapsto ge_1$ of $\mathrm{SL}_2(\mathbb A_F)$, `SL2Section.lean`) has full measure in $\mathbb A_F^2$:

* the vectors with a vanishing component at some place form a countable union of null sets (a proper real subspace at an
  infinite place; $\{x_v = 0\}$, a countable union of translates of a slice $\{x\in\hat{\mathcal O} : x_v = c\}$ of measure
  $\operatorname{vol}_v(\{c\}) = 0$, at a finite place);
* the vectors that fail to be primitive at infinitely many finite places are null by **Borel–Cantelli**: on the translate
  $\xi + \hat{\mathcal O}^2$ ($\xi\in F^2$), the event "not primitive at $v$" is a box of measure
  $\operatorname{vol}(\hat{\mathcal O})^2N(v)^{-2}$, and $\sum_v N(v)^{-2} < \infty$ (`summable_normP_rpow`, a subseries of
  $\zeta_F(2)$).

This is the measure-theoretic content of the convergence of $\prod_v(1 - N(v)^{-2})$ (Weil's $\lambda_v = 1$ for
$\mathrm{SL}_2$, AAG §2.3, p. 21) used by the fibration measure on $\mathrm{SL}_2(\mathbb A_F)$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding WithZero
open scoped ENNReal NNReal Pointwise Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Slices of $\hat{\mathcal O}$ -/

/-- The measure of a one-place slice of $\hat{\mathcal O}$: $\mu_f\{x\in\hat{\mathcal O} : x_v\in U\} =
\operatorname{vol}_v(U)\cdot\operatorname{vol}(\hat{\mathcal O})/\operatorname{vol}(\mathcal O_v)$ (stated as
`vol_v(U) * P` together with `vol(O_v) * P = vol(Ô)`). -/
theorem muFin_slice (v : HeightOneSpectrum (𝓞 F)) (U : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F))
    (hUm : MeasurableSet (U v)) (hUO : U v ⊆ v.adicCompletionIntegers F) :
    muFin F {x | x ∈ OHat ∧ x v ∈ U v} = Analysis.selfDualV v (U v) *
      ENNReal.ofReal (∏ᶠ (w) (_ : w ∉ ({v} : Finset (HeightOneSpectrum (𝓞 F)))),
        (Analysis.selfDualV w).real (Analysis.latticeV w 0)) := by
  have h := muFin_box_prod (F := F) {v} U (by simpa using hUm) (by simpa using hUO)
  rw [Finset.prod_singleton] at h
  rw [← h]
  congr 1
  ext x
  simp [and_comm]

theorem muFin_OHat_eq_volO_mul (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (ohatVol F) = volO v *
      ENNReal.ofReal (∏ᶠ (w) (_ : w ∉ ({v} : Finset (HeightOneSpectrum (𝓞 F)))),
        (Analysis.selfDualV w).real (Analysis.latticeV w 0)) := by
  have h := muFin_slice (F := F) v (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
    (measurableSet_O v) le_rfl
  have hset : {x : AF | x ∈ OHat ∧ x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} = OHat := by
    ext x; exact ⟨fun h => h.1, fun h => ⟨h, h v⟩⟩
  rw [hset, muFin_OHat] at h
  rw [h, volO]

/-- A slice with a singleton has measure zero. -/
theorem muFin_slice_singleton (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) :
    muFin F {x | x ∈ OHat ∧ x v = c} = 0 := by
  have h := muFin_slice (F := F) v (fun w => ({t | t ∈ w.adicCompletionIntegers F ∧ t = (if h : w = v then
      h ▸ c else 0)} : Set (w.adicCompletion F)))
    ((measurableSet_O v).inter (measurableSet_singleton _)) (fun t ht => ht.1)
  have h0 : Analysis.selfDualV v {t | t ∈ v.adicCompletionIntegers F ∧ t = (if h : v = v then h ▸ c else 0)} = 0 :=
    measure_mono_null (fun t ht => ht.2) (measure_singleton _)
  rw [h0, zero_mul] at h
  refine measure_mono_null ?_ h
  intro x hx
  refine ⟨hx.1, hx.1 v, ?_⟩
  simp [hx.2]

/-- **$\{x\in\mathbb A_f : x_v = 0\}$ is null.** -/
theorem muFin_eval_eq_zero (v : HeightOneSpectrum (𝓞 F)) : muFin F {x : AF | x v = 0} = 0 := by
  have hcov : {x : AF | x v = 0} ⊆ ⋃ ξ : F, (fun x => x + (-algebraMap F AF ξ)) ⁻¹'
      {z | z ∈ OHat ∧ z v = -(algebraMap F AF ξ) v} := by
    intro x hx
    obtain ⟨ξ, hξ⟩ := exists_sub_mem_OHat x
    refine Set.mem_iUnion.mpr ⟨ξ, ?_, ?_⟩
    · simpa [sub_eq_add_neg] using hξ
    · show (x + -algebraMap F AF ξ) v = -(algebraMap F AF ξ) v
      have : (x + -algebraMap F AF ξ) v = x v + -(algebraMap F AF ξ) v := rfl
      rw [this, show x v = 0 from hx, zero_add]
  refine measure_mono_null hcov (measure_iUnion_null fun ξ => ?_)
  rw [measure_preimage_add_right]
  exact muFin_slice_singleton v _

/-! ### Vanishing components -/

theorem selfDualInf_real_eq_zero (w : {w : InfinitePlace F // w.IsReal}) :
    Analysis.selfDualInf {x : mixedSpace F | x.1 w = 0} = 0 := by
  let L : mixedSpace F →ₗ[ℝ] ℝ := (LinearMap.proj w).comp (LinearMap.fst ℝ _ _)
  have hker : {x : mixedSpace F | x.1 w = 0} = (LinearMap.ker L : Set (mixedSpace F)) := by
    ext x; simp [L]
  rw [hker]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have hmem : ((Pi.single w 1, 0) : mixedSpace F) ∈ LinearMap.ker L := by rw [htop]; trivial
  simp [L] at hmem

theorem selfDualInf_complex_eq_zero (w : {w : InfinitePlace F // w.IsComplex}) :
    Analysis.selfDualInf {x : mixedSpace F | x.2 w = 0} = 0 := by
  let L : mixedSpace F →ₗ[ℝ] ℂ := (LinearMap.proj (R := ℝ) w).comp (LinearMap.snd ℝ _ _)
  have hker : {x : mixedSpace F | x.2 w = 0} = (LinearMap.ker L : Set (mixedSpace F)) := by
    ext x; simp [L]
  rw [hker]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have hmem : ((0, Pi.single w 1) : mixedSpace F) ∈ LinearMap.ker L := by rw [htop]; trivial
  simp [L] at hmem

theorem muAddVec_comp_null (i : Fin 2) {Z : Set (Adeles F)} (hZ : muAdd F Z = 0) :
    muAddVec F (Fin 2) {y | y i ∈ Z} = 0 :=
  Measure.pi_eval_preimage_null _ hZ

theorem muAdd_fst_null {Z : Set (mixedSpace F)} (hZ : Analysis.selfDualInf Z = 0) :
    muAdd F {a | a.1 ∈ Z} = 0 := by
  have : {a : Adeles F | a.1 ∈ Z} = Z ×ˢ Set.univ := by ext; simp
  rw [this, muAdd, Measure.prod_prod, hZ, zero_mul]

theorem muAdd_snd_null {Z : Set AF} (hZ : muFin F Z = 0) : muAdd F {a | a.2 ∈ Z} = 0 := by
  have : {a : Adeles F | a.2 ∈ Z} = Set.univ ×ˢ Z := by ext; simp
  rw [this, muAdd, Measure.prod_prod, hZ, mul_zero]

/-! ### Borel–Cantelli for primitivity -/

theorem lt_one_iff_mem_latticeV (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    valV v x < 1 ↔ x ∈ Analysis.latticeV v 1 := by
  rw [Analysis.mem_latticeV]
  show Valued.v x < 1 ↔ Valued.v x ≤ exp (-1 : ℤ)
  rcases eq_or_ne (Valued.v x) 0 with h | h
  · rw [h]; simp
  · obtain ⟨n, hn⟩ := WithZero.ne_zero_iff_exists.mp h
    rw [← hn]
    have h1 : ((n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = exp (Multiplicative.toAdd n) := rfl
    rw [h1, ← exp_zero, exp_lt_exp, exp_le_exp]
    omega

/-- The non-primitive event at `v` for the translate by `c = (c₀, c₁)`: a coordinate box. -/
def nonPrimBox (c : Fin 2 → AF) (v : HeightOneSpectrum (𝓞 F)) : Set (Fin 2 → AF) :=
  Set.univ.pi fun i => {x | x ∈ OHat ∧ x v ∈ ({t | c i v ∈ v.adicCompletionIntegers F ∧ valV v (t + c i v) < 1} :
    Set (v.adicCompletion F))}

theorem muFin_nonPrimSlice_le (c : AF) (v : HeightOneSpectrum (𝓞 F)) :
    muFin F {x | x ∈ OHat ∧ x v ∈ ({t | c v ∈ v.adicCompletionIntegers F ∧ valV v (t + c v) < 1} :
      Set (v.adicCompletion F))} ≤ ENNReal.ofReal (ohatVol F * (Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
  set T : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F) :=
    fun w => {t | c w ∈ w.adicCompletionIntegers F ∧ valV w (t + c w) < 1}
  have hTm : MeasurableSet (T v) := by
    by_cases hc : c v ∈ v.adicCompletionIntegers F
    · have : T v = (fun t => t + c v) ⁻¹' (Analysis.latticeV v 1 : Set (v.adicCompletion F)) := by
        ext t; simp [T, hc, lt_one_iff_mem_latticeV]
      rw [this]
      exact (Analysis.measurableSet_latticeV v 1).preimage (measurable_add_const _)
    · have : T v = ∅ := by ext t; simp [T, hc]
      rw [this]; exact MeasurableSet.empty
  have hTO : T v ⊆ v.adicCompletionIntegers F := by
    rintro t ⟨hc, ht⟩
    have h1 : valV v (t + c v) ≤ 1 := ht.le
    have : t = (t + c v) - c v := by ring
    rw [this]
    exact sub_mem (show t + c v ∈ v.adicCompletionIntegers F from h1) hc
  have h := muFin_slice (F := F) v T hTm hTO
  have hOP := muFin_OHat_eq_volO_mul (F := F) v
  set P := ENNReal.ofReal (∏ᶠ (w) (_ : w ∉ ({v} : Finset (HeightOneSpectrum (𝓞 F)))),
        (Analysis.selfDualV w).real (Analysis.latticeV w 0))
  -- `vol_v(T) ≤ vol_v(𝔭_v) = N(v)⁻¹ vol_v(O_v)`
  have hTle : Analysis.selfDualV v (T v) ≤ Analysis.selfDualV v (Analysis.latticeV v 1) := by
    by_cases hc : c v ∈ v.adicCompletionIntegers F
    · have : T v = (fun t => t + c v) ⁻¹' (Analysis.latticeV v 1 : Set (v.adicCompletion F)) := by
        ext t; simp [T, hc, lt_one_iff_mem_latticeV]
      rw [this, measure_preimage_add_right]
    · have : T v = ∅ := by ext t; simp [T, hc]
      rw [this, measure_empty]; exact bot_le
  have hp : Analysis.selfDualV v (Analysis.latticeV v 1) =
      ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) * volO v := by
    have e1 : Analysis.selfDualV v (Analysis.latticeV v 1) =
        ENNReal.ofReal ((Analysis.selfDualV v).real (Analysis.latticeV v 1)) :=
      (ENNReal.ofReal_toReal ((Analysis.isCompact_latticeV v 1).measure_lt_top.ne)).symm
    rw [e1, volO_eq_ofReal, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
      Analysis.selfDualV_real_latticeV, Analysis.selfDualV_real_latticeV, ← Analysis.modV_eq]
    congr 1
    simp only [zpow_one, zpow_zero, mul_one]
    ring
  calc muFin F {x | x ∈ OHat ∧ x v ∈ T v} = Analysis.selfDualV v (T v) * P := h
    _ ≤ Analysis.selfDualV v (Analysis.latticeV v 1) * P := by gcongr
    _ = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) * ENNReal.ofReal (ohatVol F) := by
        rw [hp, mul_assoc, ← hOP]
    _ = ENNReal.ofReal (ohatVol F * (Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
        rw [mul_comm, ← ENNReal.ofReal_mul (ohatVol_pos (F := F)).le]

theorem muFinVec_nonPrimBox_le (c : Fin 2 → AF) (v : HeightOneSpectrum (𝓞 F)) :
    muFinVec F (Fin 2) (nonPrimBox c v) ≤
      ENNReal.ofReal (ohatVol F ^ 2 * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)))) := by
  rw [nonPrimBox, muFinVec, Measure.pi_pi, Fin.prod_univ_two]
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have h2 : 2 ≤ Ideal.absNorm v.asIdeal := QuadFormsKB.NFEuler.two_le_normP v
    have h3 : 0 < Ideal.absNorm v.asIdeal := lt_of_lt_of_le two_pos h2
    exact_mod_cast h3
  calc _ ≤ ENNReal.ofReal (ohatVol F * (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
        ENNReal.ofReal (ohatVol F * (Ideal.absNorm v.asIdeal : ℝ)⁻¹) :=
        mul_le_mul' (muFin_nonPrimSlice_le _ v) (muFin_nonPrimSlice_le _ v)
    _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (ohatVol_pos (F := F)).le (inv_nonneg.mpr hN.le))]
        congr 1
        rw [Real.rpow_neg hN.le, Real.rpow_two]
        field_simp

/-- The finite parts of the vectors that are not primitive at almost all places. -/
def nonPrimFin : Set (Fin 2 → AF) := {z | ¬ ∀ᶠ v in cofinite, IsPrim (valV v) (z 0 v) (z 1 v)}

theorem not_isPrim_lt_one {v : HeightOneSpectrum (𝓞 F)} {a c : v.adicCompletion F}
    (ha : valV v a ≤ 1) (hc : valV v c ≤ 1) (h : ¬ IsPrim (valV v) a c) : valV v a < 1 ∧ valV v c < 1 := by
  have hu : ∀ x : v.adicCompletion F, valV v x ≤ 1 → ¬ (x ≠ 0 ∧ valV v x⁻¹ ≤ 1) → valV v x < 1 := by
    intro x hx hn
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have : ¬ valV v x⁻¹ ≤ 1 := fun h => hn ⟨hx0, h⟩
      rw [not_le, map_inv₀] at this
      exact lt_of_le_of_ne hx fun h1 => by rw [h1, inv_one] at this; exact lt_irrefl _ this
  unfold IsPrim at h
  push Not at h
  exact ⟨hu a ha fun h' => not_le.mpr ((h ha hc).1 h'.1) h'.2,
    hu c hc fun h' => not_le.mpr ((h ha hc).2 h'.1) h'.2⟩

theorem muFinVec_nonPrimFin : muFinVec F (Fin 2) nonPrimFin = 0 := by
  -- cover by translates `ξ + Ô²`
  have hcov : (nonPrimFin : Set (Fin 2 → AF)) ⊆ ⋃ ξ : Fin 2 → F,
      (fun z => z + (-(fun i => algebraMap F AF (ξ i)))) ⁻¹'
        ({z | (∀ i, z i ∈ OHat) ∧ ¬ ∀ᶠ v in cofinite, IsPrim (valV v)
          (z 0 v + algebraMap F AF (ξ 0) v) (z 1 v + algebraMap F AF (ξ 1) v)}) := by
    intro z hz
    choose ξ hξ using fun i => exists_sub_mem_OHat (z i)
    refine Set.mem_iUnion.mpr ⟨ξ, fun i => by simpa [sub_eq_add_neg] using hξ i, ?_⟩
    have e : ∀ i v, (z + -fun i => algebraMap F AF (ξ i)) i v + algebraMap F AF (ξ i) v = z i v := by
      intro i v
      show z i v + -(algebraMap F AF (ξ i)) v + algebraMap F AF (ξ i) v = z i v
      ring
    simp only [e]
    exact hz
  refine measure_mono_null hcov (measure_iUnion_null fun ξ => ?_)
  rw [measure_preimage_add_right]
  set c : Fin 2 → AF := fun i => algebraMap F AF (ξ i)
  -- Borel–Cantelli
  have hsub : {z : Fin 2 → AF | (∀ i, z i ∈ OHat) ∧ ¬ ∀ᶠ v in cofinite, IsPrim (valV v)
      (z 0 v + c 0 v) (z 1 v + c 1 v)} ⊆ limsup (nonPrimBox c) cofinite := by
    rintro z ⟨hzO, hz⟩
    rw [Filter.mem_limsup_iff_frequently_mem]
    have hcint : ∀ i, ∀ᶠ v in cofinite, c i v ∈ v.adicCompletionIntegers F := fun i => (c i).2
    rw [Filter.not_eventually] at hz
    refine ((hz.and_eventually ((hcint 0).and (hcint 1))).mono fun v ⟨hnp, hc0, hc1⟩ => ?_)
    have hint : ∀ i, valV v (z i v + c i v) ≤ 1 := fun i =>
      (Valuation.map_add _ _ _).trans (max_le (hzO i v) (by fin_cases i; exacts [hc0, hc1]))
    have hlt := not_isPrim_lt_one (hint 0) (hint 1) hnp
    intro i _
    refine ⟨hzO i, ?_, ?_⟩
    · fin_cases i; exacts [hc0, hc1]
    · fin_cases i; exacts [hlt.1, hlt.2]
  refine measure_mono_null hsub (measure_limsup_cofinite_eq_zero ?_)
  -- `∑_v μ(B_v) ≤ ∑_v vol(Ô)² N(v)⁻² < ∞`
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) =>
      ohatVol F ^ 2 * ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))) :=
    (QuadFormsKB.NFEuler.summable_normP_rpow (F := F) one_lt_two).mul_left _
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun v => muFinVec_nonPrimBox_le c v)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-! ### The primitive set has full measure -/

/-- **Almost every vector of $\mathbb A_F^2$ is primitive**: `primSet F` is conull for the self-dual measure. -/
@[kb "weil1982" "§2.3, p. 21 (convergence factors; λ_v = 1 for SL₂ since ∏(1 − N(v)⁻²) converges)"]
theorem muAddVec_compl_primSet : muAddVec F (Fin 2) (primSet F)ᶜ = 0 := by
  have hcov : (primSet F)ᶜ ⊆ (⋃ w, {y : AdeleSpace F (Fin 2) | y 0 ∈ {a : Adeles F | a.1 ∈
        {x : mixedSpace F | x.1 w = 0}}}) ∪
      (⋃ w, {y : AdeleSpace F (Fin 2) | y 0 ∈ {a : Adeles F | a.1 ∈ {x : mixedSpace F | x.2 w = 0}}}) ∪
      (⋃ v, {y : AdeleSpace F (Fin 2) | y 0 ∈ {a : Adeles F | a.2 ∈ {x : AF | x v = 0}}}) ∪
      boxSet Set.univ nonPrimFin := by
    intro y hy
    simp only [primSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_forall, not_or,
      not_not] at hy
    rcases hy with ⟨w, h, -⟩ | ⟨w, h, -⟩ | ⟨v, h, -⟩ | h
    · exact Or.inl (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨w, h⟩)))
    · exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨w, h⟩)))
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨v, h⟩))
    · exact Or.inr ⟨Set.mem_univ _, h⟩
  refine measure_mono_null hcov (measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_)
  · exact measure_iUnion_null fun w => muAddVec_comp_null 0 (muAdd_fst_null (selfDualInf_real_eq_zero w))
  · exact measure_iUnion_null fun w => muAddVec_comp_null 0 (muAdd_fst_null (selfDualInf_complex_eq_zero w))
  · exact measure_iUnion_null fun v => muAddVec_comp_null 0 (muAdd_snd_null (muFin_eval_eq_zero v))
  · rw [muAddVec_boxSet, muFinVec_nonPrimFin, mul_zero]

end

end QuadFormsKB.Tamagawa.Measure.Weil
