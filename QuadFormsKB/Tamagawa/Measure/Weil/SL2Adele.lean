import QuadFormsKB.Tamagawa.Measure.Weil.Ideles
import QuadFormsKB.Tamagawa.Measure.Weil.QuotientIntegral

/-!
# $\mathrm{SL}_2(\mathbb A_F)$ as a locally compact group, $\mathrm{SL}_2(F)$ discrete

$F$ is any number field (no total reality, no PID). $\mathrm{SL}_2(\mathbb A_F)$ = `SL2A F` is Mathlib's
`Matrix.SpecialLinearGroup (Fin 2) (Adeles F)` with the subspace topology of $M_2(\mathbb A_F)$; it is closed there, so
it is a locally compact, second-countable, Hausdorff topological group (its Borel σ-algebra makes it a measurable group;
Haar measures exist).

* `slEmb : SL(2, F) →* SL2A F`, the diagonal embedding, is injective (`slEmb_injective`) with **discrete** image
  (`discreteTopology_slSub`).
* **Weil's quotient $G_{\mathbb A}/G_k$.** $\mathrm{SL}_2(F)$ acts on $\mathrm{SL}_2(\mathbb A_F)$ by right translation,
  $\gamma\cdot g = g\,\gamma^{-1}$ (`slRightAction`); its covolume is Weil's $\operatorname{vol}(G_{\mathbb A}/G_k)$
  (AAG §2.4, p. 23). Exact measurable fundamental domains exist (`exists_measurableSet_forall_existsUnique_right`).
* Generic, upstreamable: **`RestrictedProduct.measurable_of_forall_eval`**: a map into a restricted product (countable
  index, second-countable factors, open subsets) is Borel measurable as soon as every coordinate is.
* `isCompact_slBox`, `isOpen_slNbhd`: a relatively compact open neighbourhood of $1$ (entries in $\hat{\mathcal O}$
  at the finite places, close to $1$ at the infinite places), used to compare measures with Haar measure.
* `measure_le_orbit_integral_of_transitive`: Siegel's finiteness criterion for a transitive action, with an
  arbitrary base point.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Pointwise Classical MatrixGroups

set_option linter.unusedSectionVars false

/-! ### Generic: measurability of maps into a restricted product -/

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- **Coordinatewise measurability into a restricted product.** For a countable index set, second-countable Borel
factors and open subsets `A i`, a map `f : X → Πʳ i, [R i, A i]` is measurable (for the Borel σ-algebra of the restricted
product topology) as soon as each coordinate `x ↦ f x i` is measurable. *Proof:* `X` is the countable union of the
measurable sets `{x | ∀ i ∉ s, f x i ∈ A i}` (`s` finite), on which `f` factors through the open embedding of
`Πʳ i, [R i, A i]_[𝓟 sᶜ]`, whose topology is induced from the product `Π i, R i`. -/
theorem measurable_of_forall_eval [Countable ι] [∀ i, SecondCountableTopology (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)] (hAopen : ∀ i, IsOpen (A i))
    {X : Type*} [MeasurableSpace X] {f : X → Πʳ i, [R i, A i]} (hf : ∀ i, Measurable fun x => f x i) :
    @Measurable X (Πʳ i, [R i, A i]) _ (borel _) f := by
  letI := borel (Πʳ i, [R i, A i])
  haveI : BorelSpace (Πʳ i, [R i, A i]) := ⟨rfl⟩
  have hS : ∀ s : Finset ι, cofinite ≤ 𝓟 ((s : Set ι)ᶜ) := fun s => by
    rw [le_principal_iff]; exact s.finite_toSet.compl_mem_cofinite
  have hcoe : Measurable fun x => ((f x : Πʳ i, [R i, A i]) : (i : ι) → R i) :=
    measurable_pi_iff.mpr hf
  refine measurable_of_isOpen fun U hU => ?_
  have hV : ∀ s : Finset ι, ∃ V : Set ((i : ι) → R i), IsOpen V ∧
      ((↑) : Πʳ i, [R i, A i]_[𝓟 ((s : Set ι)ᶜ)] → (i : ι) → R i) ⁻¹' V = inclusion R A (hS s) ⁻¹' U :=
    fun s => isEmbedding_coe_of_principal.isInducing.isOpen_iff.mp (hU.preimage (continuous_inclusion (hS s)))
  choose V hVo hVeq using hV
  have heq : f ⁻¹' U = ⋃ s : Finset ι, {x | ∀ i, i ∉ s → f x i ∈ A i} ∩
      (fun x => ((f x : Πʳ i, [R i, A i]) : (i : ι) → R i)) ⁻¹' V s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx
      have hfin : {i | f x i ∉ A i}.Finite := (f x).2
      refine ⟨hfin.toFinset, fun i hi => ?_, ?_⟩
      · by_contra h; exact hi (by simpa using h)
      · let p : Πʳ i, [R i, A i]_[𝓟 ((hfin.toFinset : Set ι)ᶜ)] :=
          ⟨f x, Filter.eventually_principal.mpr fun i hi => by
            by_contra h; exact hi (by simpa using h)⟩
        have : p ∈ inclusion R A (hS _) ⁻¹' U := hx
        rw [← hVeq] at this
        exact this
    · rintro ⟨s, hs, hxV⟩
      let p : Πʳ i, [R i, A i]_[𝓟 ((s : Set ι)ᶜ)] :=
        ⟨f x, Filter.eventually_principal.mpr fun i hi => hs i hi⟩
      have : p ∈ ((↑) : Πʳ i, [R i, A i]_[𝓟 ((s : Set ι)ᶜ)] → (i : ι) → R i) ⁻¹' V s := hxV
      rw [hVeq] at this
      exact this
  rw [heq]
  refine MeasurableSet.iUnion fun s => MeasurableSet.inter ?_ (hcoe ((hVo s).measurableSet))
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hf i ((hAopen i).measurableSet)

end RestrictedProduct

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### The group $\mathrm{SL}_2(\mathbb A_F)$ -/

variable (F) in
/-- $\mathrm{SL}_2(\mathbb A_F)$, with the subspace topology from $M_2(\mathbb A_F)$. -/
abbrev SL2A : Type := Matrix.SpecialLinearGroup (Fin 2) (Adeles F)

instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (Adeles F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Adeles F))

instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (Adeles F)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Adeles F))

instance : LocallyCompactSpace (SL2A F) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance : SecondCountableTopology (SL2A F) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

instance measurableSpace_SL2A : MeasurableSpace (SL2A F) :=
  inferInstanceAs (MeasurableSpace {A : Matrix (Fin 2) (Fin 2) (Adeles F) // A.det = 1})

instance : BorelSpace (SL2A F) :=
  inferInstanceAs (BorelSpace {A : Matrix (Fin 2) (Fin 2) (Adeles F) // A.det = 1})

example : IsTopologicalGroup (SL2A F) := inferInstance
example : T2Space (SL2A F) := inferInstance

/-- The inclusion $\mathrm{SL}_2(\mathbb A_F)\hookrightarrow M_2(\mathbb A_F)$ is a measurable embedding (it is a
closed embedding of Borel spaces). -/
theorem measurableEmbedding_SL2A_val :
    MeasurableEmbedding (Subtype.val : SL2A F → Matrix (Fin 2) (Fin 2) (Adeles F)) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.measurableEmbedding

/-- A map into $\mathrm{SL}_2(\mathbb A_F)$ is measurable iff its four entries are. -/
theorem measurable_SL2A_iff {X : Type*} [MeasurableSpace X] {f : X → SL2A F} :
    Measurable f ↔ ∀ i j, Measurable fun x => (f x : Matrix (Fin 2) (Fin 2) (Adeles F)) i j := by
  refine ⟨fun h i j => ?_, fun h => ?_⟩
  · exact (measurableEmbedding_SL2A_val.measurable.comp h).eval_matrix
  · exact measurableEmbedding_SL2A_val.measurable_comp_iff.mp (Measurable.of_eval_matrix _ h)

theorem measurable_SL2A_entry (i j : Fin 2) :
    Measurable fun g : SL2A F => (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j :=
  measurable_SL2A_iff.mp measurable_id i j

instance : MeasurableMul₂ (SL2A F) := ContinuousMul.measurableMul₂
instance : MeasurableInv (SL2A F) := ContinuousInv.measurableInv
instance : MeasurableMul (SL2A F) := inferInstance

/-! ### The discrete subgroup $\mathrm{SL}_2(F)$ -/

instance : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))

instance : Countable (SL(2, F)) :=
  Function.Injective.countable (f := fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) Subtype.val_injective

variable (F) in
/-- The diagonal embedding $\mathrm{SL}_2(F)\to\mathrm{SL}_2(\mathbb A_F)$. -/
def slEmb : SL(2, F) →* SL2A F := Matrix.SpecialLinearGroup.map (diagRing F)

@[simp] theorem slEmb_apply (γ : SL(2, F)) (i j : Fin 2) :
    (slEmb F γ : Matrix (Fin 2) (Fin 2) (Adeles F)) i j = diag F ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem slEmb_injective : Function.Injective (slEmb F) := by
  intro γ δ h
  ext i j
  have := congrArg (fun g : SL2A F => (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j) h
  simp only [slEmb_apply] at this
  exact diag_injective this

variable (F) in
/-- $\mathrm{SL}_2(F)$ as a subgroup of $\mathrm{SL}_2(\mathbb A_F)$. -/
def slSub : Subgroup (SL2A F) := (slEmb F).range

/-- **$\mathrm{SL}_2(F)$ is discrete in $\mathrm{SL}_2(\mathbb A_F)$** (from the discreteness of $F$ in $\mathbb A_F$,
entrywise). -/
@[kb "weil1982" "§2.4, p. 23 (G_k discrete in G_𝔸) [unverified locator for the discreteness statement]"]
theorem discreteTopology_slSub : DiscreteTopology (slSub F) := by
  obtain ⟨U, hU, h0U, hUdiag⟩ := exists_isOpen_diag_mem_iff (F := F)
  set V : Set (SL2A F) := {g | ∀ i j, (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j -
    (1 : Matrix (Fin 2) (Fin 2) (Adeles F)) i j ∈ U}
  have hV : IsOpen V := by
    simp only [V, Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU.preimage ?_
    exact ((continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)).sub
      continuous_const
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.mpr ⟨V, hV, ?_⟩)
  ext ⟨g, hg⟩
  obtain ⟨γ, rfl⟩ := hg
  simp only [Set.mem_preimage, Set.mem_singleton_iff, V]
  constructor
  · intro h
    have hγ : γ = 1 := by
      ext i j
      have h' := h i j
      rw [slEmb_apply] at h'
      have : diag F ((γ : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j) ∈ U := by
        rw [← diagRing_apply, map_sub, diagRing_apply]
        convert h' using 2
        rcases eq_or_ne i j with rfl | hij
        · simp [Matrix.one_apply_eq, map_one]
        · simp [Matrix.one_apply_ne hij]
      exact sub_eq_zero.mp (hUdiag _ this)
    subst hγ
    exact Subtype.ext (map_one _)
  · intro h i j
    have h1 : slEmb F γ = 1 := congrArg Subtype.val h
    rw [h1, Matrix.SpecialLinearGroup.coe_one, sub_self]
    exact h0U

instance : DiscreteTopology (slSub F) := discreteTopology_slSub

/-! ### Weil's quotient $G_{\mathbb A}/G_k$: the right action of $\mathrm{SL}_2(F)$ -/

/-- $\mathrm{SL}_2(F)$ acts on $\mathrm{SL}_2(\mathbb A_F)$ by right translation, $\gamma\cdot g = g\gamma^{-1}$; the
quotient is Weil's $G_{\mathbb A}/G_k$ (AAG §2.4). -/
instance slRightAction : MulAction (SL(2, F)) (SL2A F) where
  smul γ g := g * (slEmb F γ)⁻¹
  one_smul g := by show g * (slEmb F 1)⁻¹ = g; simp
  mul_smul γ δ g := by
    show g * (slEmb F (γ * δ))⁻¹ = g * (slEmb F δ)⁻¹ * (slEmb F γ)⁻¹
    rw [map_mul, mul_inv_rev, mul_assoc]

theorem slRight_smul_def (γ : SL(2, F)) (g : SL2A F) : γ • g = g * (slEmb F γ)⁻¹ := rfl

instance : MeasurableConstSMul (SL(2, F)) (SL2A F) :=
  ⟨fun γ => measurable_mul_const (slEmb F γ)⁻¹⟩

/-- **Exact measurable fundamental domain for $G_{\mathbb A}/G_k$** (for the discrete subgroup
$\mathrm{SL}_2(F)$, transported from left to right translation by $g\mapsto g^{-1}$). -/
theorem exists_measurableSet_forall_existsUnique_right :
    ∃ D : Set (SL2A F), MeasurableSet D ∧ ∀ g : SL2A F, ∃! γ : SL(2, F), γ • g ∈ D := by
  obtain ⟨D, hD, h⟩ := exists_measurableSet_forall_existsUnique_smul_mem (slSub F)
  refine ⟨(fun g => g⁻¹) ⁻¹' D, measurable_inv hD, fun g => ?_⟩
  obtain ⟨⟨_, γ, rfl⟩, hγ, huniq⟩ := h g⁻¹
  refine ⟨γ, ?_, fun δ hδ => ?_⟩
  · show (g * (slEmb F γ)⁻¹)⁻¹ ∈ D
    rw [mul_inv_rev, inv_inv]; exact hγ
  · have hδ' : (⟨slEmb F δ, δ, rfl⟩ : slSub F) • g⁻¹ ∈ D := by
      show slEmb F δ * g⁻¹ ∈ D
      have : (g * (slEmb F δ)⁻¹)⁻¹ ∈ D := hδ
      rwa [mul_inv_rev, inv_inv] at this
    have := huniq _ hδ'
    exact slEmb_injective (congrArg Subtype.val this)

instance (μ : Measure (SL2A F)) : HasFundamentalDomain (SL(2, F)) (SL2A F) μ := by
  obtain ⟨D, hD, h⟩ := exists_measurableSet_forall_existsUnique_right (F := F)
  exact ⟨⟨D, IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩⟩

/-! ### A relatively compact open neighbourhood of $1$ -/

variable (F) in
/-- The open set of $g\in\mathrm{SL}_2(\mathbb A_F)$ whose finite components have all entries in $\hat{\mathcal O}$ and
whose archimedean components satisfy $\|a-1\| < 1/2$, $\|b\| < 1/4$, $\|c\| < 1/4$, $\|d-1\|<1/2$ (sup norms on
$F_\infty$). -/
def slNbhd : Set (SL2A F) :=
  {g | (∀ i j, ((g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j).2 ∈ OHat) ∧
    ‖((g : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 0).1 - 1‖ < 1 / 2 ∧
    ‖((g : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1).1‖ < 1 / 4 ∧
    ‖((g : Matrix (Fin 2) (Fin 2) (Adeles F)) 1 0).1‖ < 1 / 4 ∧
    ‖((g : Matrix (Fin 2) (Fin 2) (Adeles F)) 1 1).1 - 1‖ < 1 / 2}

theorem continuous_SL2A_entry (i j : Fin 2) :
    Continuous fun g : SL2A F => (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j :=
  (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)

theorem isOpen_slNbhd : IsOpen (slNbhd F) := by
  have hc := continuous_SL2A_entry (F := F)
  simp only [slNbhd, Set.ofPred_and]
  refine IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_)))
  · simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_OHat.preimage (continuous_snd.comp (hc i j))
  · exact isOpen_lt ((continuous_fst.comp (hc 0 0)).sub continuous_const).norm continuous_const
  · exact isOpen_lt (continuous_fst.comp (hc 0 1)).norm continuous_const
  · exact isOpen_lt (continuous_fst.comp (hc 1 0)).norm continuous_const
  · exact isOpen_lt ((continuous_fst.comp (hc 1 1)).sub continuous_const).norm continuous_const

theorem one_mem_slNbhd : (1 : SL2A F) ∈ slNbhd F := by
  refine ⟨fun i j => ?_, ?_, ?_, ?_, ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
      exact fun v => (v.adicCompletionIntegers F).one_mem
    · simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij]
      exact zero_mem_OHat
  all_goals simp

/-- The compact set of $g$ with all entries in $\bar B(0, 2)\times\hat{\mathcal O}$. -/
theorem isCompact_slBox :
    IsCompact {g : SL2A F | ∀ i j, (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j ∈
      Metric.closedBall (0 : mixedSpace F) 2 ×ˢ OHat} := by
  have hK : IsCompact (Metric.closedBall (0 : mixedSpace F) 2 ×ˢ (OHat (F := F))) :=
    (isCompact_closedBall _ _).prod isCompact_OHat
  have hM : IsCompact {M : Matrix (Fin 2) (Fin 2) (Adeles F) | ∀ i j, M i j ∈
      Metric.closedBall (0 : mixedSpace F) 2 ×ˢ OHat} := by
    have : {M : Matrix (Fin 2) (Fin 2) (Adeles F) | ∀ i j, M i j ∈
        Metric.closedBall (0 : mixedSpace F) 2 ×ˢ OHat} =
        Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
          Metric.closedBall (0 : mixedSpace F) 2 ×ˢ OHat := by
      ext M
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hM

theorem norm_one_mixedSpace_le : ‖(1 : mixedSpace F)‖ ≤ 1 := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp

theorem slNbhd_subset_slBox :
    slNbhd F ⊆ {g : SL2A F | ∀ i j, (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j ∈
      Metric.closedBall (0 : mixedSpace F) 2 ×ˢ OHat} := by
  rintro g ⟨hf, h00, h01, h10, h11⟩ i j
  refine ⟨?_, hf i j⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖(1 : mixedSpace F)‖ ≤ 1 := norm_one_mixedSpace_le
  have key : ∀ a : mixedSpace F, ‖a - 1‖ < 1 / 2 → ‖a‖ ≤ 2 := fun a ha =>
    calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - 1‖ + ‖(1 : mixedSpace F)‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  fin_cases i <;> fin_cases j
  · exact key _ h00
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]; linarith
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue]; linarith
  · exact key _ h11

/-- For every Haar measure $\mu$ on $\mathrm{SL}_2(\mathbb A_F)$, $0 < \mu(\text{slNbhd}) < \infty$. -/
theorem haar_slNbhd_pos_lt_top (μ : Measure (SL2A F)) [μ.IsHaarMeasure] :
    μ (slNbhd F) ≠ 0 ∧ μ (slNbhd F) ≠ ∞ :=
  ⟨(isOpen_slNbhd.measure_pos μ ⟨1, one_mem_slNbhd⟩).ne',
    ((isCompact_slBox.measure_lt_top).trans_le' (measure_mono slNbhd_subset_slBox)).ne⟩

end

/-! ### Siegel's criterion for a transitive action -/

section Transitive

variable {Γ α : Type*} [Group Γ] [Countable Γ] [MeasurableSpace α] [MulAction Γ α]
  [MeasurableConstSMul Γ α] {μ : Measure α} [SMulInvariantMeasure Γ α μ]
  {X : Type*} [MulAction Γ X] [Countable X]

/-- **Siegel's finiteness criterion, transitive case** (`measure_le_tsum_orbit_integrals` with one orbit and an
arbitrary base point `r`): if `Γ` acts transitively on the countable set `X`, `Φ` is equivariant and
`Σ_{ξ ∈ X} Φ(ξ, x) ≥ 1` for every `x`, then `μ(D) ≤ ∫_E Φ(r, x) dμ` for every fundamental domain `D` of `Γ` and every
exact fundamental domain `E` of the stabilizer `Γ_r`. -/
theorem measure_le_orbit_integral_of_transitive (r : X) (htrans : ∀ ξ : X, ∃ γ : Γ, γ • r = ξ)
    (Φ : X → α → ℝ≥0∞) (hΦ : ∀ (γ : Γ) (ξ : X) (x : α), Φ (γ • ξ) (γ • x) = Φ ξ x)
    (hmeas : Measurable (Φ r)) (hone : ∀ x, 1 ≤ ∑' ξ : X, Φ ξ x) {D E : Set α}
    (hD : IsFundamentalDomain Γ D μ) (hE : MeasurableSet E)
    (hEx : ∀ y : α, ∃! s : MulAction.stabilizer Γ r, s • y ∈ E) :
    μ D ≤ ∫⁻ x in E, Φ r x ∂μ := by
  have horb : ∀ ξ : X, ξ ∈ MulAction.orbit Γ r := fun ξ => by
    obtain ⟨γ, rfl⟩ := htrans ξ; exact ⟨γ, rfl⟩
  let e : MulAction.orbit Γ r ≃ X := Equiv.subtypeUnivEquiv horb
  calc μ D = ∫⁻ x in D, 1 ∂μ := by simp
    _ ≤ ∫⁻ x in D, ∑' ξ : X, Φ ξ x ∂μ := lintegral_mono hone
    _ = ∫⁻ x in D, ∑' ξ : MulAction.orbit Γ r, Φ ξ x ∂μ :=
        lintegral_congr fun x => (e.tsum_eq (fun ξ => Φ ξ x)).symm
    _ = ∫⁻ x in E, Φ r x ∂μ := lintegral_orbit_unfold r Φ hΦ hmeas hD hE hEx

end Transitive

end QuadFormsKB.Tamagawa.Measure.Weil
