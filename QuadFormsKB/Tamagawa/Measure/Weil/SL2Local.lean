import QuadFormsKB.Tamagawa.Measure.Weil.SL2Box
import QuadFormsKB.Tamagawa.Measure.Weil.UnitsHaar

/-!
# The finite local factors of $\mu_T$ are Weil's gauge-form measures

$F$ any number field, $v$ a finite place, $K = F_v$ with the self-dual measure $dx_v$ (`Analysis.selfDualV`).
At $v$, the coordinates are $\Psi_v(y, x) = s_v(y)\,n(x)$ with the local section
$s_v(a, c) = \begin{pmatrix} a & b_v\\ c & d_v\end{pmatrix}$ (`locB`, `locD` for $B = \mathcal O_v$).

* `muTV v` $=\Psi_{v*}(dy_v|_{K^2\setminus 0}\otimes dx_v)$: the local fibration measure (the $v$-component of $\mu_T$);
* **`muTV_eq_muGaugeV`**: it equals Weil's gauge-form measure $|\omega|_v$ for $\omega = da\wedge db\wedge dc/a$, i.e.
  $|a|_v^{-1}\,da\,dc\,db$ in the chart $(a, c, b)\mapsto\begin{pmatrix} a & b\\ c & (1 + bc)/a\end{pmatrix}$, with
  $|a|_v = \Delta_K(a)$ the module (`distribHaarChar`);
* **`muTV_intMat`**: $|\omega|_v(\mathrm{SL}_2(\mathcal O_v)) = (1 - N(v)^{-2})\operatorname{vol}(\mathcal O_v)^3$ (Weil's
  Thm 2.2.5 for $\mathrm{SL}_2$, proved here: $\mathrm{SL}_2(\mathcal O_v) = \{s_v(y)n(x) : y\in\mathrm{Prim}(\mathcal O_v^2),
  x\in\mathcal O_v\}$ and `selfDualV_primV`).

Together with `muT_box_gauge` this shows that $\mu_T$ is Weil's product $|\omega|_\infty\otimes\prod_v|\omega|_v$ on
$\mathrm{SL}_2(F_\infty)\times\prod_v\mathrm{SL}_2(\mathcal O_v)$ (`finFactorSL2` $=\operatorname{vol}(\hat{\mathcal O})^3
\prod_v(1 - N(v)^{-2})$, $\operatorname{vol}(\hat{\mathcal O}) = \prod_v\operatorname{vol}(\mathcal O_v)$).
-/

open IsDedekindDomain NumberField MeasureTheory Measure
open scoped ENNReal NNReal Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F

/-- The integers $\mathcal O_v$ as a set. -/
abbrev OV : Set Kv := (v.adicCompletionIntegers F : Set Kv)

/-- **The local coordinates** $\Psi_v(y, x) = s_v(y)\,n(x)$. -/
def psiV (p : (Fin 2 → Kv) × Kv) : Matrix (Fin 2) (Fin 2) Kv :=
  !![p.1 0, p.1 0 * p.2 + locB (OV v) (p.1 0) (p.1 1); p.1 1, p.1 1 * p.2 + locD (OV v) (p.1 0) (p.1 1)]

/-- The nonzero vectors of $K^2$. -/
def primLoc : Set (Fin 2 → Kv) := {y | y 0 ≠ 0 ∨ y 1 ≠ 0}

theorem measurable_psiV : Measurable (psiV v) := by
  have hO : MeasurableSet (OV v) := measurableSet_O v
  have h0 : Measurable fun p : (Fin 2 → Kv) × Kv => p.1 0 := (measurable_pi_apply 0).comp measurable_fst
  have h1 : Measurable fun p : (Fin 2 → Kv) × Kv => p.1 1 := (measurable_pi_apply 1).comp measurable_fst
  have hB : Measurable fun p : (Fin 2 → Kv) × Kv => locB (OV v) (p.1 0) (p.1 1) :=
    (measurable_locB hO).comp (h0.prodMk h1)
  have hD : Measurable fun p : (Fin 2 → Kv) × Kv => locD (OV v) (p.1 0) (p.1 1) :=
    (measurable_locD hO).comp (h0.prodMk h1)
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · exact h0
  · exact (h0.mul measurable_snd).add hB
  · exact h1
  · exact (h1.mul measurable_snd).add hD

theorem measurableSet_primLoc : MeasurableSet (primLoc v) :=
  ((measurable_pi_apply 0) (measurableSet_singleton 0).compl).union
    ((measurable_pi_apply 1) (measurableSet_singleton 0).compl)

/-- **The local fibration measure** $\Psi_{v*}(dy_v|_{K^2\setminus0}\otimes dx_v)$ on $M_2(F_v)$. -/
def muTV : Measure (Matrix (Fin 2) (Fin 2) Kv) :=
  (((Measure.pi fun _ : Fin 2 => Analysis.selfDualV v).restrict (primLoc v)).prod (Analysis.selfDualV v)).map
    (psiV v)

/-- The module $|a|_v = \Delta_{F_v}(a)$ of $a\ne0$ (junk value $1$ at $a = 0$). -/
def modK (a : Kv) : ℝ≥0∞ :=
  if h : a ≠ 0 then (distribHaarChar Kv (unitsHomeomorphNeZero.symm ⟨a, h⟩) : ℝ≥0∞) else 1

/-- The module of $F_v$ is continuous on $F_v^\times$ (it is $1$ on the open subgroup $\mathcal O_v^\times$). -/
theorem continuous_distribHaarChar_V : Continuous (distribHaarChar Kv : Kvˣ → ℝ≥0) := by
  refine continuous_distribHaarChar_of_eventually_eq_one ?_
  have hopen : IsOpen {u : Kvˣ | (u : Kv) ∈ OV v ∧ ((u⁻¹ : Kvˣ) : Kv) ∈ OV v} :=
    ((isOpen_adicCompletionIntegers v).preimage Units.continuous_val).inter
      ((isOpen_adicCompletionIntegers v).preimage Units.continuous_coe_inv)
  have h1 : (1 : Kvˣ) ∈ {u : Kvˣ | (u : Kv) ∈ OV v ∧ ((u⁻¹ : Kvˣ) : Kv) ∈ OV v} := by
    simp only [Set.mem_ofPred_eq, inv_one, Units.val_one]
    exact ⟨(v.adicCompletionIntegers F).one_mem, (v.adicCompletionIntegers F).one_mem⟩
  filter_upwards [hopen.mem_nhds h1] with u hu using distribHaarChar_eq_one_of_mem u hu.1 hu.2

/-- Weil's chart $(a, c, b)\mapsto\begin{pmatrix} a & b\\ c & (1 + bc)/a\end{pmatrix}$ at $v$. -/
def gaugeChartV (p : (Fin 2 → Kv) × Kv) : Matrix (Fin 2) (Fin 2) Kv :=
  !![p.1 0, p.2; p.1 1, (1 + p.1 1 * p.2) * (p.1 0)⁻¹]

theorem measurable_gaugeChartV : Measurable (gaugeChartV v) := by
  have h0 : Measurable fun p : (Fin 2 → Kv) × Kv => p.1 0 := (measurable_pi_apply 0).comp measurable_fst
  have h1 : Measurable fun p : (Fin 2 → Kv) × Kv => p.1 1 := (measurable_pi_apply 1).comp measurable_fst
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · exact h0
  · exact measurable_snd
  · exact h1
  · exact (measurable_const.add (h1.mul measurable_snd)).mul h0.inv

/-- The vectors with $a\ne0$. -/
def unitFirstV : Set (Fin 2 → Kv) := {y | y 0 ≠ 0}

theorem measurable_modK : Measurable (modK v) := by
  have hf : Measurable fun x : {a : Kv // a ≠ 0} =>
      (distribHaarChar Kv (unitsHomeomorphNeZero.symm x) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp ((continuous_distribHaarChar_V v).comp
      unitsHomeomorphNeZero.symm.continuous)).measurable
  exact Measurable.dite (s := {a : Kv | a ≠ 0}) hf measurable_const (measurableSet_singleton 0).compl

/-- **Weil's local gauge-form measure** $|\omega|_v$, $\omega = da\wedge db\wedge dc/a$: $|a|_v^{-1}\,da\,dc\,db$ in the
chart `gaugeChartV`. -/
def muGaugeV : Measure (Matrix (Fin 2) (Fin 2) Kv) :=
  ((((Measure.pi fun _ : Fin 2 => Analysis.selfDualV v).restrict (unitFirstV v)).withDensity
    fun y => (modK v (y 0))⁻¹).prod (Analysis.selfDualV v)).map (gaugeChartV v)

theorem psiV_eq_gaugeChartV {y : Fin 2 → Kv} (hy : y 0 ≠ 0) (x : Kv) :
    psiV v (y, x) = gaugeChartV v (y, y 0 * x + locB (OV v) (y 0) (y 1)) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · show y 1 * x + locD (OV v) (y 0) (y 1) = (1 + y 1 * (y 0 * x + locB (OV v) (y 0) (y 1))) * (y 0)⁻¹
    have hdet := locB_det (v.adicCompletionIntegers F).zero_mem (Or.inl hy : y 0 ≠ 0 ∨ y 1 ≠ 0)
    rw [eq_mul_inv_iff_mul_eq₀ hy]
    linear_combination hdet

theorem pi_selfDualV_eval_zero :
    (Measure.pi fun _ : Fin 2 => Analysis.selfDualV v) {y | y 0 = 0} = 0 := by
  have : {y : Fin 2 → Kv | y 0 = 0} = Set.univ.pi (Function.update (fun _ => Set.univ) 0 {0}) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor
    · intro h i
      by_cases hi : i = 0
      · subst hi; simpa using h
      · simp [Function.update_of_ne hi]
    · intro h; simpa using h 0
  rw [this, Measure.pi_pi, Fin.prod_univ_two]
  simp

/-- **The local factor of $\mu_T$ is Weil's gauge-form measure:** `muTV v = muGaugeV v`. -/
@[kb "weil1982" "§2.2 (gauge forms and local measures); §2.4, Thm 2.4.3 [unverified page]"]
theorem muTV_eq_muGaugeV : muTV v = muGaugeV v := by
  ext U hU
  set μ := Measure.pi fun _ : Fin 2 => Analysis.selfDualV v
  have hg : Measurable fun y : Fin 2 → Kv => (modK v (y 0))⁻¹ :=
    ((measurable_modK v).comp (measurable_pi_apply (0 : Fin 2))).inv
  have hh : Measurable fun y : Fin 2 → Kv => Analysis.selfDualV v (Prod.mk y ⁻¹' (gaugeChartV v ⁻¹' U)) :=
    measurable_measure_prodMk_left (measurable_gaugeChartV v hU)
  rw [muTV, muGaugeV, Measure.map_apply (measurable_psiV v) hU, Measure.map_apply (measurable_gaugeChartV v) hU,
    Measure.prod_apply (measurable_psiV v hU), Measure.prod_apply (measurable_gaugeChartV v hU),
    lintegral_withDensity_eq_lintegral_mul _ hg hh]
  have hae : primLoc v =ᵐ[μ] unitFirstV v := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (pi_selfDualV_eval_zero v), ?_⟩
    · exact not_not.1 hy.2
    · refine measure_mono_null (fun y hy => ?_) (measure_empty (μ := μ))
      exact absurd (Or.inl hy.1) hy.2
  rw [Measure.restrict_congr_set hae]
  have hUm : MeasurableSet (unitFirstV v) := (measurable_pi_apply 0) (measurableSet_singleton 0).compl
  refine setLIntegral_congr_fun hUm fun y hy => ?_
  have hy0 : y 0 ≠ 0 := hy
  set u : Kvˣ := Units.mk0 (y 0) hy0
  have hset : Prod.mk y ⁻¹' (psiV v ⁻¹' U) =
      (u • ·) ⁻¹' ((· + locB (OV v) (y 0) (y 1)) ⁻¹' (Prod.mk y ⁻¹' (gaugeChartV v ⁻¹' U))) := by
    ext x
    simp only [Set.mem_preimage]
    rw [psiV_eq_gaugeChartV v hy0]
    rfl
  have hmeas : MeasurableSet ((· + locB (OV v) (y 0) (y 1)) ⁻¹' (Prod.mk y ⁻¹' (gaugeChartV v ⁻¹' U))) :=
    measurable_add_const _ (measurable_prodMk_left (measurable_gaugeChartV v hU))
  simp only [Pi.mul_apply]
  rw [hset, ← Measure.map_apply (measurable_const_smul u) hmeas, map_smul_eq_distribHaarChar_inv,
    Measure.smul_apply, measure_preimage_add_right, modK, dif_pos hy0, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv
    (distribHaarChar_ne_zero _)]
  have : unitsHomeomorphNeZero.symm ⟨y 0, hy0⟩ = u :=
    unitsHomeomorphNeZero.injective (by rw [Homeomorph.apply_symm_apply]; exact Subtype.ext rfl)
  rw [this]

/-- The integral matrices $M_2(\mathcal O_v)$. -/
def intMat : Set (Matrix (Fin 2) (Fin 2) Kv) := {X | ∀ i j, X i j ∈ OV v}

theorem measurableSet_intMat : MeasurableSet (intMat v) := by
  have : intMat v = ⋂ i, ⋂ j, (fun X : Matrix (Fin 2) (Fin 2) Kv => X i j) ⁻¹' OV v := by
    ext X; simp [intMat, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) (measurableSet_O v)

/-- The local set identity: $s_v(y)n(x)\in M_2(\mathcal O_v)$ with $y\ne0$ iff $y$ is primitive and $x\in\mathcal O_v$. -/
theorem psiV_mem_intMat_iff (y : Fin 2 → Kv) (x : Kv) :
    (y ∈ primLoc v ∧ psiV v (y, x) ∈ intMat v) ↔ (IsPrim (valV v) (y 0) (y 1) ∧ x ∈ OV v) := by
  constructor
  · rintro ⟨hy, hint⟩
    have e00 : valV v (y 0) ≤ 1 := hint 0 0
    have e01 : valV v (y 0 * x + locB (OV v) (y 0) (y 1)) ≤ 1 := hint 0 1
    have e10 : valV v (y 1) ≤ 1 := hint 1 0
    have e11 : valV v (y 1 * x + locD (OV v) (y 0) (y 1)) ≤ 1 := hint 1 1
    have hdet := locB_det (v.adicCompletionIntegers F).zero_mem hy
    have hdet' : y 0 * (y 1 * x + locD (OV v) (y 0) (y 1)) - (y 0 * x + locB (OV v) (y 0) (y 1)) * y 1 = 1 := by
      linear_combination hdet
    have hP := isPrim_of_det (valV v) e00 e01 e10 e11 hdet'
    refine ⟨hP, integral_of_prim (valV v) hP (locB_integral (valV v) hP) (locD_integral (valV v) hP) e01 e11⟩
  · rintro ⟨hP, hx⟩
    refine ⟨isPrim_ne_zero (valV v) hP, fun i j => ?_⟩
    fin_cases i <;> fin_cases j
    · exact hP.1
    · show valV v (y 0 * x + locB (OV v) (y 0) (y 1)) ≤ 1
      have hm : valV v (y 0 * x) ≤ 1 := by rw [Valuation.map_mul]; exact mul_le_one' hP.1 hx
      exact (Valuation.map_add _ _ _).trans (max_le hm (locB_integral (valV v) hP))
    · exact hP.2.1
    · show valV v (y 1 * x + locD (OV v) (y 0) (y 1)) ≤ 1
      have hm : valV v (y 1 * x) ≤ 1 := by rw [Valuation.map_mul]; exact mul_le_one' hP.2.1 hx
      exact (Valuation.map_add _ _ _).trans (max_le hm (locD_integral (valV v) hP))

/-- **$|\omega|_v(\mathrm{SL}_2(\mathcal O_v)) = (1 - N(v)^{-2})\operatorname{vol}(\mathcal O_v)^3$** (Weil's Thm 2.2.5 for
$\mathrm{SL}_2$, $q^{-3}\#\mathrm{SL}_2(\mathbb F_q) = 1 - q^{-2}$), for the local factor of $\mu_T$ and hence for Weil's
gauge-form measure (`muTV_eq_muGaugeV`). -/
@[kb "weil1982" "§2.2, Thm 2.2.5 (volume of G(O_v)) [unverified page]"]
theorem muTV_intMat :
    muTV v (intMat v) = ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2) * volO v ^ 3 := by
  set μ := Measure.pi fun _ : Fin 2 => Analysis.selfDualV v
  set P : Set (Fin 2 → Kv) := {y | IsPrim (valV v) (y 0) (y 1)}
  have hP : P = (fun z : Fin 2 → v.adicCompletionIntegers F => fun i => (z i : Kv)) '' primV v := by
    ext y
    constructor
    · intro hy
      exact ⟨fun i => ⟨y i, by fin_cases i; exacts [hy.1, hy.2.1]⟩, hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact hz
  have hPm : MeasurableSet P := by
    have : P = Set.univ.pi (fun _ => OV v) \ Set.univ.pi (fun _ => (Analysis.latticeV v 1 : Set Kv)) := by
      ext y
      simp only [P, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ_pi]
      constructor
      · intro hy
        refine ⟨fun i => by fin_cases i; exacts [hy.1, hy.2.1], fun h => ?_⟩
        have := (isPrim_iff_of_integral v hy.1 hy.2.1).1 hy
        exact this ⟨(lt_one_iff_mem_latticeV v _).2 (h 0), (lt_one_iff_mem_latticeV v _).2 (h 1)⟩
      · rintro ⟨hO, hn⟩
        rw [isPrim_iff_of_integral v (hO 0) (hO 1)]
        rintro ⟨h0, h1⟩
        apply hn
        intro i; fin_cases i
        · exact (lt_one_iff_mem_latticeV v _).1 h0
        · exact (lt_one_iff_mem_latticeV v _).1 h1
    rw [this]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_O v).diff
      (MeasurableSet.univ_pi fun _ => Analysis.measurableSet_latticeV v 1)
  have hslice : ∀ y ∈ primLoc v, Analysis.selfDualV v (Prod.mk y ⁻¹' (psiV v ⁻¹' intMat v)) =
      P.indicator (fun _ => volO v) y := by
    intro y hy
    by_cases hyP : y ∈ P
    · have : Prod.mk y ⁻¹' (psiV v ⁻¹' intMat v) = OV v := by
        ext x
        simp only [Set.mem_preimage]
        have := psiV_mem_intMat_iff v y x
        exact ⟨fun h => (this.1 ⟨hy, h⟩).2, fun h => (this.2 ⟨hyP, h⟩).2⟩
      rw [this, Set.indicator_of_mem hyP]; rfl
    · have : Prod.mk y ⁻¹' (psiV v ⁻¹' intMat v) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hyP ((psiV_mem_intMat_iff v y x).1 ⟨hy, h⟩).1
      rw [this, Set.indicator_of_notMem hyP, measure_empty]
  rw [muTV, Measure.map_apply (measurable_psiV v) (measurableSet_intMat v),
    Measure.prod_apply (measurable_psiV v (measurableSet_intMat v)),
    setLIntegral_congr_fun (measurableSet_primLoc v) hslice, lintegral_indicator_const hPm,
    Measure.restrict_apply hPm]
  have hsub : P ∩ primLoc v = P := Set.inter_eq_left.2 fun y hy => isPrim_ne_zero (valV v) hy
  rw [hsub, hP, selfDualV_primV]
  ring

/-! ### The product of the local factors -/

/-- An infinite product in $[0,\infty]$ with factors $a_i\le 1$, multiplied termwise by a family $b$ that is $1$ off a
finite set $S$: $\prod_i a_ib_i = \big(\prod_{i\in S}b_i\big)\prod_i a_i$. -/
theorem tprod_mul_of_eq_one_off {ι : Type*} {a b : ι → ℝ≥0∞} (ha : ∀ i, a i ≤ 1) (S : Finset ι)
    (hb : ∀ i ∉ S, b i = 1) (hc : ∏ i ∈ S, b i ≠ ∞) :
    ∏' i, a i * b i = (∏ i ∈ S, b i) * ∏' i, a i := by
  have hA : HasProd a (∏' i, a i) := (ENNReal.multipliable_of_le_one ha).hasProd
  have hlim : Filter.Tendsto (fun s : Finset ι => (∏ i ∈ S, b i) * ∏ i ∈ s, a i) Filter.atTop
      (nhds ((∏ i ∈ S, b i) * ∏' i, a i)) := by
    have hA' : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, a i) Filter.atTop (nhds (∏' i, a i)) := by
      have := hA; unfold HasProd at this; simpa using this
    exact ENNReal.Tendsto.const_mul hA' (Or.inr hc)
  have hP : HasProd (fun i => a i * b i) ((∏ i ∈ S, b i) * ∏' i, a i) := by
    unfold HasProd
    simp only [SummationFilter.unconditional_filter]
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop S] with s hs
    rw [Finset.prod_mul_distrib, mul_comm]
    congr 1
    exact Finset.prod_subset hs fun i _ hi => hb i hi
  exact hP.tprod_eq

/-- **The product of Weil's local gauge-form volumes** $\prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))$ is
`finFactorSL2` $=\operatorname{vol}(\hat{\mathcal O})^3\prod_v(1 - N(v)^{-2})$. -/
@[kb "weil1982" "§2.3, p. 21 (product of local volumes, λ_v = 1) [page checked in the design table]"]
theorem tprod_muGaugeV_intMat :
    ∏' v : HeightOneSpectrum (𝓞 F), muGaugeV v (intMat v) = finFactorSL2 F := by
  simp_rw [← muTV_eq_muGaugeV, muTV_intMat]
  set S := (mulSupport_volO_real_finite (F := F)).toFinset
  have hb : ∀ v ∉ S, volO v ^ 3 = 1 := by
    intro v hv
    have : (Analysis.selfDualV v).real (Analysis.latticeV v 0) = 1 := by
      by_contra h
      exact hv ((Set.Finite.mem_toFinset _).2 h)
    rw [volO_eq_ofReal, this, ENNReal.ofReal_one, one_pow]
  have hc : ∏ v ∈ S, volO v ^ 3 ≠ ∞ := ENNReal.prod_ne_top fun v _ => ENNReal.pow_ne_top (volO_ne_top v)
  have ha : ∀ v : HeightOneSpectrum (𝓞 F), ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2) ≤ 1 :=
    fun v => ENNReal.ofReal_le_one.2 (by nlinarith [sq_nonneg ((Ideal.absNorm v.asIdeal : ℝ)⁻¹)])
  rw [tprod_mul_of_eq_one_off ha S hb hc, finFactorSL2]
  congr 1
  -- `vol(Ô) = ∏_{v ∈ S} vol(O_v)`
  rw [ohatVol_eq_finprod, finprod_eq_prod_of_mulSupport_subset (s := S) _
    (fun v hv => (Set.Finite.mem_toFinset _).2 hv),
    ENNReal.ofReal_prod_of_nonneg (fun v _ => measureReal_nonneg), ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun v _ => by rw [volO_eq_ofReal]

/-- **$\tau(\mathrm{SL}_2) = 1$ for Weil's Tamagawa measure** $|\omega|_\infty\otimes\prod_v|\omega|_v$ (gauge form
$\omega = da\wedge db\wedge dc/a$, convergence factors $\lambda_v = 1$): every σ-finite left-invariant measure on
$\mathrm{SL}_2(\mathbb A_F)$ that gives the chart $U\times\prod_v\mathrm{SL}_2(\mathcal O_v)$ (for $U$ = `slNbhdInf`)
the mass $|\omega|_\infty(U)\cdot\prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))$ has covolume $1$. -/
@[kb "weil1982" "§3.7 (τ(SL₂) = 1); §2.3, p. 21 [unverified page for §3.7]"]
theorem tamagawa_SL2_gauge (μ : Measure (SL2A F)) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hbox : μ (intFin F ∩ archPart ⁻¹' slNbhdInf F) =
      muGaugeInf F (slNbhdInf F) * ∏' v : HeightOneSpectrum (𝓞 F), muGaugeV v (intMat v)) :
    covolume (SL(2, F)) (SL2A F) μ = 1 :=
  tamagawa_SL2_weil μ (by rw [hbox, tprod_muGaugeV_intMat])

end

end QuadFormsKB.Tamagawa.Measure.Weil
