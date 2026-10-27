/-
# The product characterization of $\mu_f$ on $SO(V)(\mathbb A_f)$

**Layer:** number fields; the Tamagawa measure `muFin Q₀ λ` on $SO(V)(\mathbb A_f)$ = `SOAf Q₀`, the Haar measure
normalized by $\mu_f(SO(\hat L)) = \prod'_v\mu_v(SO(L_v))$ with the local measures $\mu_v$ = `muLocSO v Q₀ λ_v`
($L = \mathcal O_F^n$, $K_v = SO(L_v)$).

**Defines**
* `evalSO v` : $SO(V)(\mathbb A_f) \to SO(V)(F_v)$ (the $v$-component, a continuous homomorphism) and `singleSO v` :
  $SO(V)(F_v) \to SO(V)(\mathbb A_f)$ ($x$ at $v$, $1$ elsewhere);
* `boxSO S U` $= \prod_{v\in S}U_v\times\prod_{v\notin S}K_v$ for a finite set $S$ of places and sets $U_v \subseteq SO(V)(F_v)$
  (the charts $G_S\times\prod_{v\notin S}K_v$ of Weil 1982, §2.3, p. 21, and their measurable boxes);
* `haarSO v Q₀`: the Haar measure on $SO(V)(F_v)$ with $\mathrm{vol}(K_v) = 1$; `piEvalSO`: $SO(V)(\mathbb A_f) \to \prod_v SO(V)(F_v)$.

**Proves** (all unconditional, standard axioms only)
* `muFin_boxSO_haar`: **the product characterization**, for every finite $S$ and measurable $U_v$ ($v \in S$):
  $$\mu_f\Big(\prod_{v\in S}U_v\times\prod_{v\notin S}K_v\Big) = \mu_f(K)\prod_{v\in S}\frac{\mu_v(U_v)}{\mu_v(K_v)}$$
  (`muFin_boxSO`, $\lambda_v > 0$), with $\mu_f(K) = \prod'_v\mu_v(K_v)$; and, when $\prod_v\mu_v(K_v)$ converges
  (`Multipliable`, e.g. rank $n \ne 0, 2$ with $\lambda = 1$, `multipliable_finFactor_one`),
  $$\mu_f\Big(\prod_{v\in S}U_v\times\prod_{v\notin S}K_v\Big) = \prod_{v\in S}\mu_v(U_v)\cdot\prod'_{v\notin S}\mu_v(K_v)$$
  (`muFin_boxSO_split`): $\mu_f$ is Weil's product measure $\prod_v\lambda_v^{-1}\omega_v$ on each chart.
* `map_restrict_muFin_KSO`: on $K = \prod_v K_v$, $\mu_f$ is $\mu_f(K)$ times the **infinite product** of the normalized
  local Haar probability measures (Mathlib's `Measure.infinitePi`).
* `resEquiv`: **$SO(V)(\mathbb A_f) \cong \prod'_v SO(V)(F_v)$ as topological groups** (Mathlib's `Πʳ` with respect to the
  $SO(L_v)$; the $SO(V)(\mathbb A_f)$ is the closed subgroup `soAf` of $O(V)(\mathbb A_f)$ with the subspace topology);
* `muFin_lam_eq_smul`: changing the convergence factors rescales $\mu_f$: $\mu_f^{\lambda} = (\prod'\mu_v^\lambda(K_v) /
  \prod'\mu_v^{\lambda'}(K_v))\,\mu_f^{\lambda'}$.

*Proof of the product characterization.* Induction on $S$. For $w \notin S$ fix the constraints at the other places and
push $\mu_f$ restricted to them forward along $g \mapsto g_w$. The result is a left-invariant measure on $SO(V)(F_w)$
(left translation by `singleSO w x` preserves $\mu_f$ and the constraints away from $w$), finite on compacts (finitely
many cosets of $K_w$ cover a compact set), hence a multiple of the Haar measure of $SO(V)(F_w)$ (`isMulLeftInvariant_eq_smul`;
$SO(V)(F_w)$ is second countable); its value on $K_w$ is the box for $S$. Infinite-measure $U_v$ by monotone exhaustion.
Template: AxiomMath's additive `finiteMeasure_chart` (not imported).

-/
import QuadFormsKB.Tamagawa.Measure.AdelicSO

open MeasureTheory Set Topology
open scoped ENNReal NNReal RestrictedProduct Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

/-! ### Two `ENNReal` facts about suprema of monotone sequences -/

theorem ennreal_iSup_mul_iSup_of_monotone {f g : ℕ → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ k, f k) * (⨆ k, g k) = ⨆ k, f k * g k := by
  rw [ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun j => le_iSup_of_le (max i j)
      (mul_le_mul' (hf (le_max_left _ _)) (hg (le_max_right _ _)))
  · exact iSup_le fun k => le_iSup_of_le k (le_iSup_of_le k le_rfl)

theorem ennreal_prod_iSup_of_monotone {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ≥0∞)
    (hf : ∀ i, Monotone (f i)) : ∏ i ∈ s, ⨆ k, f i k = ⨆ k, ∏ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, ennreal_iSup_mul_iSup_of_monotone (hf a)]
    · simp_rw [Finset.prod_insert ha]
    · exact fun k l hkl => Finset.prod_le_prod fun i _ => hf i hkl

section Product

open NumberField IsDedekindDomain QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-! ### Components and single-place elements -/

/-- **The $v$-component** $SO(V)(\mathbb A_f) \to SO(V)(F_v)$. -/
def evalSO (v : HeightOneSpectrum (𝓞 F)) : SOAf Q₀ →* SOv v Q₀ where
  toFun g := ⟨(g : OAf QF) v, g.2 v⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_evalSO (v : HeightOneSpectrum (𝓞 F)) (g : SOAf Q₀) :
    ((evalSO Q₀ v g : SOv v Q₀) : orthGroup QF (v.adicCompletion F)) = (g : OAf QF) v := rfl

theorem continuous_evalSO (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalSO Q₀ v) :=
  ((RestrictedProduct.continuous_eval v).comp continuous_subtype_val).subtype_mk _

theorem measurable_evalSO (v : HeightOneSpectrum (𝓞 F)) : Measurable (evalSO Q₀ v) :=
  (continuous_evalSO Q₀ v).measurable

open scoped Classical in
/-- **The element $x$ at the place $v$** and $1$ elsewhere, as an element of $SO(V)(\mathbb A_f)$. -/
def singleSO (v : HeightOneSpectrum (𝓞 F)) : SOv v Q₀ →* SOAf Q₀ where
  toFun x := ⟨RestrictedProduct.mulSingle (fun w => stdStab QF w) v (x : orthGroup QF (v.adicCompletion F)),
    fun w => by
      by_cases h : w = v
      · subst h
        show (RestrictedProduct.mulSingle (fun w => stdStab QF w) w
          (x : orthGroup QF (w.adicCompletion F)) w) ∈ soSub QF (w.adicCompletion F)
        rw [RestrictedProduct.mulSingle_eq_same]; exact x.2
      · show (RestrictedProduct.mulSingle (fun w => stdStab QF w) v
          (x : orthGroup QF (v.adicCompletion F)) w) ∈ soSub QF (w.adicCompletion F)
        rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h]; exact (soSub QF _).one_mem⟩
  map_one' := by
    apply Subtype.ext
    exact RestrictedProduct.mulSingle_one _ _
  map_mul' x y := by
    apply Subtype.ext
    exact RestrictedProduct.mulSingle_mul _ _ _ _

theorem evalSO_singleSO_same (v : HeightOneSpectrum (𝓞 F)) (x : SOv v Q₀) : evalSO Q₀ v (singleSO Q₀ v x) = x := by
  classical
  apply Subtype.ext
  show RestrictedProduct.mulSingle (fun w => stdStab QF w) v (x : orthGroup QF (v.adicCompletion F)) v = _
  convert RestrictedProduct.mulSingle_eq_same (fun w => stdStab QF w) v (x : orthGroup QF (v.adicCompletion F))

theorem evalSO_singleSO_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : SOv v Q₀) :
    evalSO Q₀ w (singleSO Q₀ v x) = 1 := by
  classical
  apply Subtype.ext
  show RestrictedProduct.mulSingle (fun w => stdStab QF w) v (x : orthGroup QF (v.adicCompletion F)) w = 1
  convert RestrictedProduct.mulSingle_eq_of_ne (fun w => stdStab QF w) (x : orthGroup QF (v.adicCompletion F)) h

/-! ### Boxes -/

/-- **The box** $\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)$ in $SO(V)(\mathbb A_f)$ ($S$ finite). For $U_v$ ranging over
all measurable sets these are the measurable rectangles of Weil's charts $G_S\times\prod_{v\notin S}K_v$ (Weil 1982, §2.3,
p. 21). -/
def boxSO (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (SOv v Q₀)) : Set (SOAf Q₀) :=
  {g | (∀ v ∈ S, evalSO Q₀ v g ∈ U v) ∧ ∀ v ∉ S, evalSO Q₀ v g ∈ (soStabSO v Q₀ : Set (SOv v Q₀))}

theorem mem_KSO_iff (g : SOAf Q₀) :
    g ∈ KSO Q₀ ↔ ∀ v, evalSO Q₀ v g ∈ (soStabSO v Q₀ : Set (SOv v Q₀)) := by
  rw [Subgroup.mem_subgroupOf, mem_locStab_intVec]
  rfl

theorem boxSO_empty (U : ∀ v, Set (SOv v Q₀)) : boxSO Q₀ ∅ U = (KSO Q₀ : Set (SOAf Q₀)) := by
  ext g
  simp only [boxSO, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, not_false_eq_true, forall_const,
    true_and, mem_ofPred_eq, SetLike.mem_coe]
  exact (mem_KSO_iff Q₀ g).symm

/-- The set $\{g : g_v \in K_v \text{ for } v \notin T\}$ is open (a union of cosets of the open $SO(\hat L)$). -/
theorem isOpen_awaySO (T : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen {g : SOAf Q₀ | ∀ v ∉ T, evalSO Q₀ v g ∈ (soStabSO v Q₀ : Set (SOv v Q₀))} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨g • (KSO Q₀ : Set (SOAf Q₀)), ?_, (isOpen_KSO Q₀).smul g, ⟨1, (KSO Q₀).one_mem, mul_one g⟩⟩
  rintro _ ⟨k, hk, rfl⟩ v hv
  have hk' := (mem_KSO_iff Q₀ k).mp hk v
  show evalSO Q₀ v (g * k) ∈ (soStabSO v Q₀ : Set (SOv v Q₀))
  rw [map_mul]
  exact (soStabSO v Q₀).mul_mem (hg v hv) hk'

theorem measurableSet_boxSO (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (SOv v Q₀))
    (hU : ∀ v ∈ S, MeasurableSet (U v)) : MeasurableSet (boxSO Q₀ S U) := by
  have : boxSO Q₀ S U = {g : SOAf Q₀ | ∀ v ∉ S, evalSO Q₀ v g ∈ (soStabSO v Q₀ : Set (SOv v Q₀))} ∩
      ⋂ v ∈ S, evalSO Q₀ v ⁻¹' U v := by
    ext g; simp only [boxSO, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage]; tauto
  rw [this]
  exact (isOpen_awaySO Q₀ S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v hv => measurable_evalSO Q₀ v (hU v hv))

/-! ### The normalized local Haar measures -/

/-- **The Haar measure on $SO(V)(F_v)$ with $\mathrm{vol}(SO(L_v)) = 1$.** -/
def haarSO (v : HeightOneSpectrum (𝓞 F)) : Measure (SOv v Q₀) :=
  Measure.haarMeasure (subgroupPC (soStabSO v Q₀) (isCompact_soStabSO v Q₀) (isOpen_soStabSO v Q₀))

instance (v : HeightOneSpectrum (𝓞 F)) : (haarSO Q₀ v).IsHaarMeasure := by unfold haarSO; infer_instance

theorem haarSO_soStabSO (v : HeightOneSpectrum (𝓞 F)) : haarSO Q₀ v (soStabSO v Q₀ : Set (SOv v Q₀)) = 1 :=
  Measure.haarMeasure_self

/-- $\mu_v = \mu_v(K_v)\cdot$ `haarSO`: `muLocSO` is `haarSO` scaled by $\alpha_v/\lambda_v$. -/
theorem muLocSO_apply (v : HeightOneSpectrum (𝓞 F)) (lam : ℝ) (A : Set (SOv v Q₀)) :
    muLocSO v Q₀ lam A = muLocSO v Q₀ lam (soStabSO v Q₀ : Set (SOv v Q₀)) * haarSO Q₀ v A := by
  rw [muLocSO_soStabSO, muLocSO, haarNorm, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rfl

theorem muLocSO_soStabSO_pos (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) {lam : ℝ} (hlam : 0 < lam) :
    muLocSO v Q₀ lam (soStabSO v Q₀ : Set (SOv v Q₀)) ≠ 0 := by
  rw [muLocSO_soStabSO, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact div_pos (siegelDensity_self_pos' Q₀ hQ v) hlam

/-- $\mathrm{haarSO}_v(U) = \mu_v(U)/\mu_v(K_v)$ for $\lambda_v > 0$. -/
theorem haarSO_eq_div (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) {lam : ℝ} (hlam : 0 < lam)
    (A : Set (SOv v Q₀)) :
    haarSO Q₀ v A = muLocSO v Q₀ lam A / muLocSO v Q₀ lam (soStabSO v Q₀ : Set (SOv v Q₀)) := by
  rw [muLocSO_apply Q₀ v lam A, mul_comm, ENNReal.mul_div_cancel_right (muLocSO_soStabSO_pos Q₀ hQ v hlam)]
  rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top

/-! ### The induction step -/

open scoped Classical in
/-- **One more place.** For $w \notin S$ and measurable $U_v$ ($v \in S \cup \{w\}$), if the box for $S$ has finite
measure, then $\mu_f(\mathrm{box}_{S\cup\{w\}}) = \mu_f(\mathrm{box}_S)\cdot\mathrm{haarSO}_w(U_w)$. -/
theorem muFin_boxSO_insert (lam : HeightOneSpectrum (𝓞 F) → ℝ) {w : HeightOneSpectrum (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hw : w ∉ S) (U : ∀ v, Set (SOv v Q₀))
    (hU : ∀ v ∈ S, MeasurableSet (U v)) (hUw : MeasurableSet (U w))
    (hfin : muFin Q₀ lam (boxSO Q₀ S U) ≠ ∞) :
    muFin Q₀ lam (boxSO Q₀ (insert w S) U) = muFin Q₀ lam (boxSO Q₀ S U) * haarSO Q₀ w (U w) := by
  classical
  set μ := muFin Q₀ lam
  set C : Set (SOAf Q₀) := {g | (∀ v ∈ S, evalSO Q₀ v g ∈ U v) ∧
    ∀ v ∉ insert w S, evalSO Q₀ v g ∈ (soStabSO v Q₀ : Set (SOv v Q₀))} with hCdef
  have hCm : MeasurableSet C := by
    have : C = {g : SOAf Q₀ | ∀ v ∉ insert w S, evalSO Q₀ v g ∈ (soStabSO v Q₀ : Set (SOv v Q₀))} ∩
        ⋂ v ∈ S, evalSO Q₀ v ⁻¹' U v := by
      ext g; simp only [C, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage]; tauto
    rw [this]
    exact (isOpen_awaySO Q₀ _).measurableSet.inter
      (Finset.measurableSet_biInter S fun v hv => measurable_evalSO Q₀ v (hU v hv))
  have hbox1 : boxSO Q₀ (insert w S) U = C ∩ evalSO Q₀ w ⁻¹' U w := by
    ext g
    simp only [boxSO, C, Finset.mem_insert, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun v hv => h1 v (Or.inr hv), fun v hv => h2 v (by simpa using hv)⟩, h1 w (Or.inl rfl)⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun v hv => ?_, fun v hv => h2 v (by simpa using hv)⟩
      rcases hv with rfl | hv
      · exact h3
      · exact h1 v hv
  have hbox0 : boxSO Q₀ S U = C ∩ evalSO Q₀ w ⁻¹' (soStabSO w Q₀ : Set (SOv w Q₀)) := by
    ext g
    simp only [boxSO, C, Finset.mem_insert, mem_ofPred_eq, mem_inter_iff, mem_preimage, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun v hv => h2 v hv.2⟩, h2 w hw⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun v hv => ?_⟩
      by_cases hvw : v = w
      · subst hvw; exact h3
      · exact h2 v ⟨hvw, hv⟩
  -- translation by `singleSO w x` preserves `C`
  have hCinv : ∀ x : SOv w Q₀, (fun g => singleSO Q₀ w x * g) ⁻¹' C = C := by
    intro x
    have hne : ∀ v, v ≠ w → ∀ g, evalSO Q₀ v (singleSO Q₀ w x * g) = evalSO Q₀ v g := by
      intro v hv g; rw [map_mul, evalSO_singleSO_ne Q₀ hv, one_mul]
    ext g
    simp only [C, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := h1 v hv; rwa [hne v (fun h => hw (h ▸ hv))] at this
      · have := h2 v hv; rwa [hne v (fun h => hv (h ▸ Finset.mem_insert_self _ _))] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · rw [hne v (fun h => hw (h ▸ hv))]; exact h1 v hv
      · rw [hne v (fun h => hv (h ▸ Finset.mem_insert_self _ _))]; exact h2 v hv
  have heval : ∀ (x : SOv w Q₀) g, evalSO Q₀ w (singleSO Q₀ w x * g) = x * evalSO Q₀ w g := by
    intro x g; rw [map_mul, evalSO_singleSO_same]
  -- the pushed-forward measure
  set ν : Measure (SOv w Q₀) := (μ.restrict C).map (evalSO Q₀ w) with hνdef
  have hν : ∀ A, MeasurableSet A → ν A = μ (C ∩ evalSO Q₀ w ⁻¹' A) := by
    intro A hA
    rw [hνdef, Measure.map_apply (measurable_evalSO Q₀ w) hA, Measure.restrict_apply
      (measurable_evalSO Q₀ w hA), inter_comm]
  have hKw : MeasurableSet (soStabSO w Q₀ : Set (SOv w Q₀)) := (isOpen_soStabSO w Q₀).measurableSet
  have hνK : ν (soStabSO w Q₀ : Set (SOv w Q₀)) = μ (boxSO Q₀ S U) := by rw [hν _ hKw, hbox0]
  have hinv : ν.IsMulLeftInvariant := by
    constructor
    intro x
    ext A hA
    rw [Measure.map_apply (measurable_const_mul x) hA, hν _ hA, hν _ ((measurable_const_mul x) hA)]
    have hset : C ∩ evalSO Q₀ w ⁻¹' ((fun y => x * y) ⁻¹' A) =
        (fun g => singleSO Q₀ w x * g) ⁻¹' (C ∩ evalSO Q₀ w ⁻¹' A) := by
      rw [preimage_inter, hCinv x]
      congr 1
      ext g; simp only [mem_preimage, heval]
    rw [hset, measure_preimage_mul]
  have hfoc : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro Kc hKc
    have hint : (interior (soStabSO w Q₀ : Set (SOv w Q₀))).Nonempty := by
      rw [(isOpen_soStabSO w Q₀).interior_eq]; exact ⟨1, (soStabSO w Q₀).one_mem⟩
    obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hKc hint
    calc ν Kc ≤ ν (⋃ g ∈ t, (fun h => g * h) ⁻¹' (soStabSO w Q₀ : Set (SOv w Q₀))) := measure_mono ht
      _ ≤ ∑ g ∈ t, ν ((fun h => g * h) ⁻¹' (soStabSO w Q₀ : Set (SOv w Q₀))) := measure_biUnion_finset_le _ _
      _ = ∑ _g ∈ t, μ (boxSO Q₀ S U) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [measure_preimage_mul, hνK]
      _ < ∞ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin.lt_top
  have hsmul := Measure.isMulLeftInvariant_eq_smul ν (haarSO Q₀ w)
  have hc : (Measure.haarScalarFactor ν (haarSO Q₀ w) : ℝ≥0∞) = μ (boxSO Q₀ S U) := by
    have := congrArg (fun m : Measure (SOv w Q₀) => m (soStabSO w Q₀ : Set (SOv w Q₀))) hsmul
    simp only [Measure.smul_apply, haarSO_soStabSO, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    rw [← hνK, this]
  rw [hbox1, ← hν _ hUw, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc]

/-! ### The product characterization -/

/-- **The product characterization, finite-measure boxes.** -/
theorem muFin_boxSO_haar_of_ne_top (lam : HeightOneSpectrum (𝓞 F) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v, Set (SOv v Q₀)) (hU : ∀ v ∈ S, MeasurableSet (U v)) (hUf : ∀ v ∈ S, haarSO Q₀ v (U v) ≠ ∞) :
    muFin Q₀ lam (boxSO Q₀ S U) = ENNReal.ofReal (finFactor Q₀ lam) * ∏ v ∈ S, haarSO Q₀ v (U v) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [boxSO_empty, muFin_KSO, Finset.prod_empty, mul_one]
  | insert w S hw ih =>
    have ih' := ih (fun v hv => hU v (Finset.mem_insert_of_mem hv))
      (fun v hv => hUf v (Finset.mem_insert_of_mem hv))
    have hfin : muFin Q₀ lam (boxSO Q₀ S U) ≠ ∞ := by
      rw [ih']
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.prod_ne_top fun v hv => hUf v (Finset.mem_insert_of_mem hv))
    rw [muFin_boxSO_insert Q₀ lam hw U (fun v hv => hU v (Finset.mem_insert_of_mem hv))
      (hU w (Finset.mem_insert_self w S)) hfin, ih', Finset.prod_insert hw, mul_assoc, mul_comm (haarSO Q₀ w (U w))]

/-- **The product characterization of $\mu_f$** (normalized form): for every finite set $S$ of places and measurable
$U_v \subseteq SO(V)(F_v)$ ($v \in S$),
$$\mu_f\Big(\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)\Big) = \mu_f(SO(\hat L))\cdot\prod_{v\in S}\mathrm{haarSO}_v(U_v),$$
`haarSO` normalized by $\mathrm{vol}(SO(L_v)) = 1$, and $\mu_f(SO(\hat L)) = \prod'_v\mu_v(SO(L_v))$. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure on ∏_{v∈S} V_{k_v} × ∏_{v∉S} V_{o_v})"]
theorem muFin_boxSO_haar (lam : HeightOneSpectrum (𝓞 F) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v, Set (SOv v Q₀)) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    muFin Q₀ lam (boxSO Q₀ S U) = ENNReal.ofReal (finFactor Q₀ lam) * ∏ v ∈ S, haarSO Q₀ v (U v) := by
  classical
  -- exhaust each `U v` by sets of finite Haar measure
  set E : ∀ v, ℕ → Set (SOv v Q₀) := fun v k => spanningSets (haarSO Q₀ v) k
  set U' : ℕ → ∀ v, Set (SOv v Q₀) := fun k v => U v ∩ E v k
  have hmono : Monotone fun k => boxSO Q₀ S (U' k) := by
    intro k l hkl g hg
    exact ⟨fun v hv => ⟨(hg.1 v hv).1, monotone_spanningSets _ hkl (hg.1 v hv).2⟩, hg.2⟩
  have hunion : (⋃ k, boxSO Q₀ S (U' k)) = boxSO Q₀ S U := by
    ext g
    simp only [mem_iUnion]
    constructor
    · rintro ⟨k, hg⟩; exact ⟨fun v hv => (hg.1 v hv).1, hg.2⟩
    · rintro hg
      have hex : ∀ v ∈ S, ∃ k, evalSO Q₀ v g ∈ E v k := fun v _ => by
        have := mem_iUnion.mp ((iUnion_spanningSets (haarSO Q₀ v)).symm ▸ mem_univ (evalSO Q₀ v g) :
          evalSO Q₀ v g ∈ ⋃ k, spanningSets (haarSO Q₀ v) k)
        exact this
      choose! k hk using hex
      refine ⟨S.sup k, fun v hv => ⟨hg.1 v hv, monotone_spanningSets _ (Finset.le_sup hv) (hk v hv)⟩, hg.2⟩
  have hlocal : ∀ v, haarSO Q₀ v (U v) = ⨆ k, haarSO Q₀ v (U' k v) := by
    intro v
    have hm : Monotone fun k => U' k v := fun k l hkl => inter_subset_inter_right _ (monotone_spanningSets _ hkl)
    rw [← hm.measure_iUnion]
    congr 1
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have hfinite : ∀ k, muFin Q₀ lam (boxSO Q₀ S (U' k)) =
      ENNReal.ofReal (finFactor Q₀ lam) * ∏ v ∈ S, haarSO Q₀ v (U' k v) := fun k =>
    muFin_boxSO_haar_of_ne_top Q₀ lam S (U' k)
      (fun v hv => (hU v hv).inter (measurableSet_spanningSets _ k))
      (fun v _ => ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ k)).ne)
  rw [← hunion, hmono.measure_iUnion]
  simp_rw [hfinite, hlocal]
  rw [← ENNReal.mul_iSup, ennreal_prod_iSup_of_monotone]
  intro v k l hkl
  exact measure_mono (inter_subset_inter_right _ (monotone_spanningSets _ hkl))

/-- **The product characterization of $\mu_f$** in terms of the local Tamagawa measures ($\lambda_v > 0$):
$$\mu_f\Big(\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)\Big) = \mu_f(SO(\hat L))\cdot\prod_{v\in S}\frac{\mu_v(U_v)}{\mu_v(SO(L_v))}.$$ -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure on ∏_{v∈S} V_{k_v} × ∏_{v∉S} V_{o_v})"]
theorem muFin_boxSO (hQ : Q₀.Nondegenerate) {lam : HeightOneSpectrum (𝓞 F) → ℝ} (hlam : ∀ v, 0 < lam v)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (SOv v Q₀)) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    muFin Q₀ lam (boxSO Q₀ S U) = ENNReal.ofReal (finFactor Q₀ lam) *
      ∏ v ∈ S, muLocSO v Q₀ (lam v) (U v) / muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀)) := by
  rw [muFin_boxSO_haar Q₀ lam S U hU]
  congr 1
  exact Finset.prod_congr rfl fun v _ => haarSO_eq_div Q₀ hQ v (hlam v) (U v)

/-- Splitting a convergent product of nonzero reals off a finite set. -/
theorem tprod_eq_prod_mul_tprod_ite {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (ha : Multipliable a)
    (S : Finset ι) (hS : ∀ v ∈ S, a v ≠ 0) :
    ∏' v, a v = (∏ v ∈ S, a v) * ∏' v, (if v ∈ S then 1 else a v) := by
  set c : ι → ℝ := fun v => if v ∈ S then (a v)⁻¹ else 1
  have hc : HasProd c (∏ v ∈ S, (a v)⁻¹) := by
    have h1 : HasProd c (∏ v ∈ S, c v) := hasProd_prod_of_ne_finset_one fun v hv => by simp [c, hv]
    rwa [Finset.prod_congr rfl fun v hv => (show c v = (a v)⁻¹ by simp [c, hv])] at h1
  have hb : HasProd (fun v => if v ∈ S then 1 else a v) ((∏' v, a v) * ∏ v ∈ S, (a v)⁻¹) := by
    convert ha.hasProd.mul hc using 1
    ext v
    by_cases hv : v ∈ S
    · simp [c, hv, mul_inv_cancel₀ (hS v hv)]
    · simp [c, hv]
  rw [hb.tprod_eq, mul_comm (∏' v, a v), ← mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun v hv => mul_inv_cancel₀ (hS v hv), Finset.prod_const_one, one_mul]

open scoped Classical in
/-- **The product characterization of $\mu_f$, split form** (Weil's product measure on a chart): if
$\prod_v\mu_v(SO(L_v))$ converges and $\lambda_v > 0$,
$$\mu_f\Big(\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)\Big) = \prod_{v\in S}\mu_v(U_v)\cdot\prod'_{v\notin S}\mu_v(SO(L_v)).$$ -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1} ω_v on each chart)"]
theorem muFin_boxSO_split (hQ : Q₀.Nondegenerate) {lam : HeightOneSpectrum (𝓞 F) → ℝ} (hlam : ∀ v, 0 < lam v)
    (hmult : Multipliable fun v => (muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (SOv v Q₀)) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    muFin Q₀ lam (boxSO Q₀ S U) = (∏ v ∈ S, muLocSO v Q₀ (lam v) (U v)) *
      ENNReal.ofReal (∏' v, if v ∈ S then 1 else
        (muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal) := by
  classical
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal
  have hK : ∀ v, muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (a v) := fun v => by
    simp only [a]; rw [ENNReal.ofReal_toReal]; rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top
  have ha0 : ∀ v, 0 < a v := fun v => by
    simp only [a]
    exact ENNReal.toReal_pos (muLocSO_soStabSO_pos Q₀ hQ v (hlam v)) (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  rw [muFin_boxSO Q₀ hQ hlam S U hU, finFactor,
    tprod_eq_prod_mul_tprod_ite a hmult S fun v _ => (ha0 v).ne',
    ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => (ha0 v).le),
    ENNReal.ofReal_prod_of_nonneg fun v _ => (ha0 v).le]
  rw [mul_comm (∏ v ∈ S, ENNReal.ofReal (a v)), mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hK v, ENNReal.mul_div_cancel (by rw [← hK v]; exact muLocSO_soStabSO_pos Q₀ hQ v (hlam v))
    ENNReal.ofReal_ne_top]

/-- **Convergence of $\prod_v\mu_v(SO(L_v))$ for $\lambda = 1$** in every rank $n \ne 0, 2$
(`hasProd_siegelDensity_odd/even`; for $n = 2$ convergence factors $\lambda_v = L_v(1, \chi)$ are needed). -/
theorem multipliable_muLocSO_one (hQ : Q₀.Nondegenerate) (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    Multipliable fun v => (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal := by
  have hm : Multipliable fun v => LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact (hasProd_siegelDensity_even k (by omega) Q₀ hQ).multipliable
    · exact (hasProd_siegelDensity_odd k Q₀ hQ).multipliable
  convert hm using 2 with v
  rw [muLocSO_soStabSO, div_one, ENNReal.toReal_ofReal (siegelDensity_self_pos' Q₀ hQ v).le]

/-! ### $\mu_f$ on $SO(\hat L)$ is an infinite product measure -/

/-- The components $g \mapsto (g_v)_v$, $SO(V)(\mathbb A_f) \to \prod_v SO(V)(F_v)$. -/
def piEvalSO : SOAf Q₀ → ∀ v, SOv v Q₀ := fun g v => evalSO Q₀ v g

theorem measurable_piEvalSO : Measurable (piEvalSO Q₀) :=
  measurable_pi_iff.mpr fun v => measurable_evalSO Q₀ v

instance (v : HeightOneSpectrum (𝓞 F)) :
    IsProbabilityMeasure ((haarSO Q₀ v).restrict (soStabSO v Q₀ : Set (SOv v Q₀))) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact haarSO_soStabSO Q₀ v⟩

/-- **$\mu_f$ on $SO(\hat L) = \prod_v SO(L_v)$ is the infinite product measure** of the normalized local Haar probability
measures, times $\mu_f(SO(\hat L)) = \prod'_v\mu_v(SO(L_v))$ (Mathlib's `Measure.infinitePi`). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure on ∏_v V_{o_v})"]
theorem map_restrict_muFin_KSO (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    ((muFin Q₀ lam).restrict (KSO Q₀ : Set (SOAf Q₀))).map (piEvalSO Q₀) =
      ENNReal.ofReal (finFactor Q₀ lam) •
        Measure.infinitePi (fun v => (haarSO Q₀ v).restrict (soStabSO v Q₀ : Set (SOv v Q₀))) := by
  classical
  by_cases hf : finFactor Q₀ lam ≤ 0
  · have h0 : muFin Q₀ lam = 0 := by
      rw [muFin, haarNorm, Real.toNNReal_of_nonpos hf, zero_smul]
    rw [h0, ENNReal.ofReal_of_nonpos hf, zero_smul, Measure.restrict_zero, Measure.map_zero]
  set c := ENNReal.ofReal (finFactor Q₀ lam)
  have hc0 : c ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero]; exact hf
  have hcT : c ≠ ∞ := ENNReal.ofReal_ne_top
  set L := ((muFin Q₀ lam).restrict (KSO Q₀ : Set (SOAf Q₀))).map (piEvalSO Q₀)
  have hKm : MeasurableSet (KSO Q₀ : Set (SOAf Q₀)) := (isOpen_KSO Q₀).measurableSet
  have key : c⁻¹ • L = Measure.infinitePi (fun v => (haarSO Q₀ v).restrict (soStabSO v Q₀ : Set (SOv v Q₀))) := by
    refine Measure.eq_infinitePi _ fun s t ht => ?_
    have hpi : MeasurableSet (Set.pi (s : Set (HeightOneSpectrum (𝓞 F))) t) :=
      MeasurableSet.pi s.countable_toSet fun v _ => ht v
    rw [Measure.smul_apply, Measure.map_apply (measurable_piEvalSO Q₀) hpi,
      Measure.restrict_apply (measurable_piEvalSO Q₀ hpi)]
    have hset : piEvalSO Q₀ ⁻¹' Set.pi (s : Set _) t ∩ (KSO Q₀ : Set (SOAf Q₀)) =
        boxSO Q₀ s (fun v => t v ∩ (soStabSO v Q₀ : Set (SOv v Q₀))) := by
      ext g
      simp only [mem_inter_iff, mem_preimage, Set.mem_pi, SetLike.mem_coe, boxSO,
        mem_ofPred_eq, piEvalSO]
      rw [mem_KSO_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun v hv => ⟨h1 v hv, h2 v⟩, fun v _ => h2 v⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun v hv => (h1 v hv).1, fun v => ?_⟩
        by_cases hv : v ∈ s
        · exact (h1 v hv).2
        · exact h2 v hv
    rw [hset, muFin_boxSO_haar Q₀ lam s _ (fun v _ => (ht v).inter (isOpen_soStabSO v Q₀).measurableSet),
      smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
    exact Finset.prod_congr rfl fun v _ => (Measure.restrict_apply (ht v)).symm
  rw [← key, smul_smul, ENNReal.mul_inv_cancel hc0 hcT, one_smul]

/-! ### Changing the convergence factors -/

/-- **Changing the convergence factors rescales $\mu_f$:** $\mu_f^{\lambda} = (\mu_f^{\lambda}(K)/\mu_f^{\lambda'}(K))\,
\mu_f^{\lambda'}$, i.e. by $\prod'_v\mu^\lambda_v(K_v)/\prod'_v\mu^{\lambda'}_v(K_v)$ (Weil's $(\omega, (\lambda_v))$ depends on
$(\lambda_v)$ only through this constant). -/
theorem muFin_lam_eq_smul (lam lam' : HeightOneSpectrum (𝓞 F) → ℝ) (h' : 0 < finFactor Q₀ lam') :
    muFin Q₀ lam = (Real.toNNReal (finFactor Q₀ lam / finFactor Q₀ lam')) • muFin Q₀ lam' := by
  simp only [muFin, haarNorm, smul_smul]
  congr 1
  rw [← Real.toNNReal_mul (div_nonneg (finFactor_nonneg Q₀ lam) h'.le), div_mul_cancel₀ _ h'.ne']

/-! ### $SO(V)(\mathbb A_f)$ as a restricted product -/

instance fact_isOpen_soStabSO : Fact (∀ v : HeightOneSpectrum (𝓞 F), IsOpen (soStabSO v Q₀ : Set (SOv v Q₀))) :=
  ⟨fun v => isOpen_soStabSO v Q₀⟩

/-- **The restricted product** $\prod'_v SO(V)(F_v)$ with respect to the $SO(L_v)$. -/
abbrev SOAfRes : Type := Πʳ v : HeightOneSpectrum (𝓞 F), [SOv v Q₀, soStabSO v Q₀]

example : IsTopologicalGroup (SOAfRes Q₀) := inferInstance

/-- $SO(V)(\mathbb A_f) \to \prod'_v SO(V)(F_v)$, $g \mapsto (g_v)_v$. -/
def toRes : SOAf Q₀ →* SOAfRes Q₀ where
  toFun g := ⟨fun v => evalSO Q₀ v g, by filter_upwards [(g : OAf QF).2] with v hv; exact hv⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- $\prod'_v SO(V)(F_v) \to SO(V)(\mathbb A_f)$. -/
def ofRes : SOAfRes Q₀ →* SOAf Q₀ where
  toFun x := ⟨⟨fun v => ((x v : SOv v Q₀) : orthGroup QF (v.adicCompletion F)), by
    filter_upwards [x.2] with v hv; exact hv⟩, fun v => (x v).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_toRes : Continuous (toRes Q₀) := by
  refine continuous_of_continuousAt_one (toRes Q₀) ?_
  have hK := (isOpen_KSO Q₀).isOpenEmbedding_subtypeVal
  have h1 : ((1 : SOAf Q₀)) = ((⟨1, (KSO Q₀).one_mem⟩ : KSO Q₀) : SOAf Q₀) := rfl
  rw [h1, ← hK.continuousAt_iff]
  refine Continuous.continuousAt ?_
  have hc : Continuous (RestrictedProduct.structureMap (fun v => SOv v Q₀) (fun v => (soStabSO v Q₀ : Set (SOv v Q₀)))
      Filter.cofinite ∘ (fun k : KSO Q₀ => fun v => (⟨evalSO Q₀ v k, (mem_KSO_iff Q₀ k).mp k.2 v⟩ :
        (soStabSO v Q₀ : Set (SOv v Q₀))))) :=
    RestrictedProduct.isEmbedding_structureMap.continuous.comp (continuous_pi fun v =>
      ((continuous_evalSO Q₀ v).comp continuous_subtype_val).subtype_mk _)
  exact hc

theorem continuous_ofRes : Continuous (ofRes Q₀) := by
  refine continuous_of_continuousAt_one (ofRes Q₀) ?_
  have hS := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => SOv v Q₀)
    (A := fun v => (soStabSO v Q₀ : Set (SOv v Q₀))) (fun v => isOpen_soStabSO v Q₀)
  have h1 : (1 : SOAfRes Q₀) = RestrictedProduct.structureMap _ _ Filter.cofinite
      (fun v => (⟨1, (soStabSO v Q₀).one_mem⟩ : (soStabSO v Q₀ : Set (SOv v Q₀)))) := rfl
  rw [h1, ← hS.continuousAt_iff]
  refine Continuous.continuousAt ?_
  refine continuous_induced_rng.mpr ?_
  have hc : Continuous (RestrictedProduct.structureMap _ _ Filter.cofinite ∘
        (fun (y : ∀ v, (soStabSO v Q₀ : Set (SOv v Q₀))) v =>
          (⟨(((y v : SOv v Q₀)) : orthGroup QF (v.adicCompletion F)), (y v).2⟩ :
            (stdStab QF v : Set (orthGroup QF (v.adicCompletion F)))))) :=
    RestrictedProduct.isEmbedding_structureMap.continuous.comp (continuous_pi fun v =>
      ((continuous_subtype_val.comp continuous_subtype_val).comp (continuous_apply v)).subtype_mk _)
  exact hc

/-- **$SO(V)(\mathbb A_f) \cong \prod'_v SO(V)(F_v)$ as topological groups** (restricted product with respect to the
$SO(L_v)$): the $SO(V)(\mathbb A_f)$, a closed subgroup of $O(V)(\mathbb A_f)$ with the subspace topology, is the restricted
product of the local groups. -/
def resEquiv : SOAf Q₀ ≃ₜ* SOAfRes Q₀ where
  toFun := toRes Q₀
  invFun := ofRes Q₀
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := (toRes Q₀).map_mul
  continuous_toFun := continuous_toRes Q₀
  continuous_invFun := continuous_ofRes Q₀

theorem resEquiv_apply (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) : resEquiv Q₀ g v = evalSO Q₀ v g := rfl

end Product

end QuadFormsKB.Tamagawa.Measure
