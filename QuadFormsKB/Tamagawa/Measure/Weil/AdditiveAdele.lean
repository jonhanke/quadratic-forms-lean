import QuadFormsKB.Analysis.AdelicPoisson

/-!
# The additive adele space of a number field and of $F^\iota$

Weil, *Adeles and Algebraic Groups* (1982), §2.1. $F$ is any number field (no total reality, no class-number
hypothesis).

* `RestrictedProduct.secondCountableTopology_of_isOpen` (generic): restricted products over a countable index with
  open subsets are second countable; hence $\mathbb A_f$ = `FiniteAdeleRing (𝓞 F) F` is locally compact, second
  countable, Borel.
* `Adeles F` $= F_\infty\times\mathbb A_f$ ($F_\infty$ = Mathlib's mixed space), `diag`, **`discreteTopology_diagSub`**
  ($F$ is discrete in $\mathbb A_F$).
* `muFin` (Haar on $\mathbb A_f$ with $\mu(\hat{\mathcal O}) = |d_F|^{-1/2} = \prod_v\operatorname{vol}_{\mathrm{sd}}(\mathcal O_v)$,
  `ohatVol_eq_finprod`), `muAdd = selfDualInf × muFin`.
* `existsUnique_vadd_mem_fundDom`: $D_\infty\times\hat{\mathcal O}$ is an exact fundamental domain for $F$;
  **`addCovolume_muAdd`**: $\operatorname{vol}(\mathbb A_F/F) = 1$.
* $A = F^\iota$: `AdeleSpace F ι`, `discreteTopology_diagVecSub`, **`addCovolume_muAddVec`**; $A = \mathbb H[F,a,b]$ through
  the coordinates $1,i,j,k$: `diagQuat`, `addCovolume_diagQuat`.

The chart lemma is in `AdditiveChart.lean`, scaling in `AdditiveScaling.lean`, Poisson in `AdditivePoisson.lean`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology RestrictedProduct NumberField.mixedEmbedding
open scoped nonZeroDivisors Classical Quaternion

/-! ### Generic: second countability of a restricted product -/

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- A restricted product (cofinite filter) of second-countable spaces over a countable index set, with
respect to open subsets, is second countable: it is the countable union of the open subspaces
`Πʳ i, [R i, A i]_[𝓟 sᶜ]` (`s` finite), each embedded in the countable product `Π i, R i`. -/
theorem secondCountableTopology_of_isOpen [Countable ι] [∀ i, SecondCountableTopology (R i)]
    (hAopen : ∀ i, IsOpen (A i)) : SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hS : ∀ s : Finset ι, cofinite ≤ 𝓟 ((s : Set ι)ᶜ) := fun s => by
    rw [le_principal_iff]; exact s.finite_toSet.compl_mem_cofinite
  have hsc : ∀ s : Finset ι, SecondCountableTopology (Set.range (inclusion R A (hS s))) := fun s => by
    have : SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((s : Set ι)ᶜ)]) :=
      isEmbedding_coe_of_principal.secondCountableTopology
    exact (isOpenEmbedding_inclusion_principal hAopen (hS s)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun s : Finset ι => Set.range (inclusion R A (hS s)))
    (fun s => (isOpenEmbedding_inclusion_principal hAopen (hS s)).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
  have hfin : {i | x i ∉ A i}.Finite := x.2
  refine ⟨hfin.toFinset, ?_⟩
  rw [range_inclusion]
  refine Filter.mem_principal.mpr fun i hi => ?_
  by_contra h
  exact hi (by simpa using h)

end RestrictedProduct

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The finite places of a number field form a countable set. -/
instance countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have : Countable (𝓞 F) := Subtype.countable
  have hsurj : Function.Surjective fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F)) := fun I =>
    (IsNoetherian.noetherian I).imp fun s hs => hs
  have : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := HeightOneSpectrum.asIdeal) fun a b h => HeightOneSpectrum.ext h

variable {F}

theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_integer _

instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  ⟨isOpen_adicCompletionIntegers⟩

theorem coe_adicCompletionIntegers_eq (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = (Analysis.latticeV v 0 : Set _) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, Analysis.mem_latticeV, HeightOneSpectrum.mem_adicCompletionIntegers]
  simp

theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [coe_adicCompletionIntegers_eq]; exact Analysis.isCompact_latticeV v 0

instance compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

/-! ### The finite adeles: topology and measurable structure -/

local notation "AF" => FiniteAdeleRing (𝓞 F) F

instance : LocallyCompactSpace AF :=
  inferInstanceAs (LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

instance : SecondCountableTopology AF :=
  RestrictedProduct.secondCountableTopology_of_isOpen isOpen_adicCompletionIntegers

instance : IsTopologicalAddGroup AF := inferInstance

instance measurableSpace_finiteAdeleRing : MeasurableSpace AF := borel AF

instance : BorelSpace AF := ⟨rfl⟩

/-- $\hat{\mathcal O} = \prod_v \mathcal O_v$, the maximal compact open subring of $\mathbb A_f$. -/
def OHat : Set AF := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}

theorem isOpen_OHat : IsOpen (OHat (F := F)) :=
  RestrictedProduct.isOpen_forall_mem isOpen_adicCompletionIntegers

theorem isCompact_OHat : IsCompact (OHat (F := F)) := by
  have : OHat (F := F) = Set.range (RestrictedProduct.structureMap _ _ cofinite) := by
    rw [RestrictedProduct.range_structureMap]; rfl
  rw [this]
  have : ∀ v : HeightOneSpectrum (𝓞 F),
      CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v =>
    isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)
  exact isCompact_range (RestrictedProduct.isEmbedding_structureMap.continuous)

theorem measurableSet_OHat : MeasurableSet (OHat (F := F)) := isOpen_OHat.measurableSet

theorem zero_mem_OHat : (0 : AF) ∈ OHat := fun v => (v.adicCompletionIntegers F).zero_mem

theorem add_mem_OHat {x y : AF} (hx : x ∈ OHat) (hy : y ∈ OHat) : x + y ∈ OHat :=
  fun v => add_mem (hx v) (hy v)

theorem neg_mem_OHat {x : AF} (hx : x ∈ OHat) : -x ∈ OHat :=
  fun v => neg_mem (hx v)

theorem sub_mem_OHat {x y : AF} (hx : x ∈ OHat) (hy : y ∈ OHat) : x - y ∈ OHat := by
  rw [sub_eq_add_neg]; exact add_mem_OHat hx (neg_mem_OHat hy)

/-- $F \cap \hat{\mathcal O} = \mathcal O_F$. -/
theorem algebraMap_mem_OHat_iff (ξ : F) :
    algebraMap F AF ξ ∈ OHat ↔ ξ ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro h
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F ξ fun v => ?_
    have := h v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    rwa [← HN.valued_algebraMap]
  · rintro ⟨a, rfl⟩ v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ≤ 1
    rw [HN.valued_algebraMap]
    exact v.valuation_le_one a

/-- Strong approximation, additive form: every finite adele is congruent to an element of $F$ modulo
$\hat{\mathcal O}$. -/
theorem exists_sub_mem_OHat (x : AF) : ∃ ξ : F, x - algebraMap F AF ξ ∈ OHat := by
  have hfin : {v | x v ∉ v.adicCompletionIntegers F}.Finite := x.2
  obtain ⟨ξ, hS, hout⟩ := Analysis.exists_strong_approx hfin.toFinset (fun v => x v) (fun _ => 0)
  refine ⟨ξ, fun v => ?_⟩
  change x v - algebraMap F (v.adicCompletion F) ξ ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  by_cases hv : v ∈ hfin.toFinset
  · have := hS v hv
    rw [neg_zero, WithZero.exp_zero] at this
    rwa [← Valuation.map_neg, neg_sub]
  · have hx : x v ∈ v.adicCompletionIntegers F := by simpa using hv
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx
    exact (Valuation.map_sub _ _ _).trans (max_le hx (hout v hv))

/-! ### The additive adele space $\mathbb A_F = F_\infty \times \mathbb A_f$ -/

variable (F) in
/-- The adele space $\mathbb A_F = F_\infty \times \mathbb A_f$ as an additive group, with $F_\infty = F\otimes\mathbb R$
Mathlib's mixed space $\mathbb R^{r_1}\times\mathbb C^{r_2}$ (the setting of the library's `adelicPoisson`). -/
abbrev Adeles : Type := mixedSpace F × FiniteAdeleRing (𝓞 F) F

example : LocallyCompactSpace (Adeles F) := inferInstance
example : SecondCountableTopology (Adeles F) := inferInstance
example : IsTopologicalAddGroup (Adeles F) := inferInstance
example : BorelSpace (Adeles F) := inferInstance

variable (F) in
/-- The diagonal embedding $F \to \mathbb A_F$. -/
def diag : F →+ Adeles F :=
  (mixedEmbedding F).toAddMonoidHom.prod (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toAddMonoidHom

@[simp] theorem diag_fst (ξ : F) : (diag F ξ).1 = mixedEmbedding F ξ := rfl
@[simp] theorem diag_snd (ξ : F) : (diag F ξ).2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ := rfl

theorem diag_injective : Function.Injective (diag F) := fun _ _ h =>
  mixedEmbedding_injective F (congrArg Prod.fst h)

variable (F) in
/-- The image $F \subset \mathbb A_F$ of the diagonal embedding, as an additive subgroup. -/
def diagSub : AddSubgroup (Adeles F) := (diag F).range

instance : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

instance countable_diagSub : Countable (diagSub F) := by
  have : Function.Surjective fun ξ : F => (⟨diag F ξ, ξ, rfl⟩ : diagSub F) := by
    rintro ⟨_, ξ, rfl⟩; exact ⟨ξ, rfl⟩
  exact this.countable

local notation "L∞" => mixedEmbedding.idealLattice F (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

omit [NumberField F] in
theorem mem_Linf_iff (y : mixedSpace F) : y ∈ L∞ ↔ ∃ a : 𝓞 F, mixedEmbedding F (a : F) = y := by
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by simpa using hz
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hz'
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    have : (a : F) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := (FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩
    simp

/-- A neighbourhood $U = W\times\hat{\mathcal O}$ of $0$ in $\mathbb A_F$ meeting $F$ only in $0$ (with $W\cap\mathcal O_F = 0$
in $F_\infty$; $F\cap\hat{\mathcal O} = \mathcal O_F$). -/
theorem exists_isOpen_diag_mem_iff :
    ∃ U : Set (Adeles F), IsOpen U ∧ (0 : Adeles F) ∈ U ∧ ∀ ξ : F, diag F ξ ∈ U → ξ = 0 := by
  have h0 : IsOpen ({0} : Set L∞) := isOpen_discrete _
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp h0
  refine ⟨W ×ˢ OHat, hW.prod isOpen_OHat, ⟨?_, zero_mem_OHat⟩, fun ξ ⟨hW', hO⟩ => ?_⟩
  · have : (0 : L∞) ∈ Subtype.val ⁻¹' W := by rw [hWeq]; rfl
    exact this
  · obtain ⟨a, ha⟩ := (algebraMap_mem_OHat_iff ξ).mp hO
    have hmem : mixedEmbedding F ξ ∈ L∞ := (mem_Linf_iff _).mpr ⟨a, by rw [← ha]⟩
    have : (⟨mixedEmbedding F ξ, hmem⟩ : L∞) ∈ Subtype.val ⁻¹' W := hW'
    rw [hWeq] at this
    have h' : mixedEmbedding F ξ = 0 := congrArg Subtype.val this
    exact mixedEmbedding_injective F (by rw [h', map_zero])

/-- **$F$ is discrete in $\mathbb A_F$.** -/
theorem discreteTopology_diagSub : DiscreteTopology (diagSub F) := by
  obtain ⟨U, hU, h0U, hUdiag⟩ := exists_isOpen_diag_mem_iff (F := F)
  refine discreteTopology_of_isOpen_singleton_zero (isOpen_induced_iff.mpr ⟨U, hU, ?_⟩)
  ext ⟨_, ξ, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain rfl := hUdiag ξ h
    exact Subtype.ext (map_zero (diag F))
  · intro h
    have : diag F ξ = 0 := congrArg Subtype.val h
    rwa [this]

/-! ### The self-dual measure on $\mathbb A_F$ -/

variable (F) in
/-- $\hat{\mathcal O}$ as a positive compact set (it is open and contains $0$). -/
def OHatCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 F) F) where
  carrier := OHat
  isCompact' := isCompact_OHat
  interior_nonempty' := ⟨0, by rw [(isOpen_OHat (F := F)).interior_eq]; exact zero_mem_OHat⟩

variable (F) in
/-- $|d_F|^{-1/2}$, the self-dual volume of $\hat{\mathcal O}$ (`muFin_OHat_eq_finprod`). -/
def ohatVol : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹

theorem sqrt_abs_discr_pos : 0 < Real.sqrt |(discr F : ℝ)| :=
  Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F)))

theorem ohatVol_pos : 0 < ohatVol F := inv_pos.mpr sqrt_abs_discr_pos

variable (F) in
/-- The self-dual Haar measure on $\mathbb A_f$: the Haar measure with $\mu(\hat{\mathcal O}) = |d_F|^{-1/2}
= \prod_v \operatorname{vol}_{\mathrm{sd}}(\mathcal O_v)$. -/
def muFin : Measure (FiniteAdeleRing (𝓞 F) F) :=
  ENNReal.ofReal (ohatVol F) • Measure.addHaarMeasure (OHatCompacts F)

instance : (muFin F).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp [ohatVol_pos]) ENNReal.ofReal_ne_top

theorem muFin_OHat : muFin F OHat = ENNReal.ofReal (ohatVol F) := by
  rw [muFin, Measure.smul_apply, smul_eq_mul]
  have := Measure.addHaarMeasure_self (K₀ := OHatCompacts F)
  change ENNReal.ofReal (ohatVol F) * Measure.addHaarMeasure (OHatCompacts F) (OHatCompacts F : Set _) = _
  rw [this, mul_one]

/-- The normalization of `muFin` is the product of the local self-dual volumes:
$|d_F|^{-1/2} = \prod_v \operatorname{vol}_{\mathrm{sd}}(\mathcal O_v)$ (`finprod_selfDualV_real` with all $k_v = 0$). -/
theorem ohatVol_eq_finprod :
    ohatVol F = ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Analysis.selfDualV v).real (Analysis.latticeV v 0) := by
  have h := Analysis.finprod_selfDualV_real (F := F) (k := fun _ => 0) (by simp)
  rw [h]
  have h1 : Analysis.idealOfExps (F := F) (fun _ => 0) = 1 := by
    simp [Analysis.idealOfExps]
  rw [h1, map_one, Rat.cast_one, one_mul, ohatVol]

variable (F) in
/-- **The self-dual measure on $\mathbb A_F$**: $\mu_\infty^{\mathrm{sd}}\times\mu_f^{\mathrm{sd}}$, with `selfDualInf`
(Lebesgue at real places, $2\,dx\,dy$ at complex places) and `muFin`. -/
def muAdd : Measure (Adeles F) := Analysis.selfDualInf.prod (muFin F)

instance : SigmaFinite (Analysis.selfDualInf (F := F)) := by
  unfold Analysis.selfDualInf; infer_instance

instance : (Analysis.selfDualInf (F := F)).IsAddHaarMeasure := by
  unfold Analysis.selfDualInf
  exact Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

instance : (muAdd F).IsAddHaarMeasure := by unfold muAdd; infer_instance

/-! ### The fundamental domain $D_\infty\times\hat{\mathcal O}$ and $\operatorname{vol}(\mathbb A_F/F) = 1$ -/

variable (F) in
/-- The basis of $F_\infty$ given by a $\mathbb Z$-basis of $\mathcal O_F$. -/
def basisInf : Module.Basis (Module.Free.ChooseBasisIndex ℤ L∞) ℝ (mixedSpace F) :=
  (Module.Free.chooseBasis ℤ L∞).ofZLatticeBasis ℝ L∞

variable (F) in
/-- $D_\infty$: the fundamental parallelotope of $\mathcal O_F$ in $F_\infty$. -/
def DInf : Set (mixedSpace F) := ZSpan.fundamentalDomain (basisInf F)

theorem span_basisInf : Submodule.span ℤ (Set.range (basisInf F)) = L∞ :=
  Module.Basis.ofZLatticeBasis_span ℝ L∞ _

/-- Every $y \in F_\infty$ has a unique $\mathcal O_F$-translate in $D_\infty$. -/
theorem existsUnique_add_mem_DInf (y : mixedSpace F) :
    ∃! a : 𝓞 F, mixedEmbedding F (a : F) + y ∈ DInf F := by
  obtain ⟨ℓ, hℓ, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (basisInf F) y
  have hℓL : (ℓ : mixedSpace F) ∈ L∞ := (span_basisInf (F := F)).le ℓ.2
  obtain ⟨a, ha⟩ := (mem_Linf_iff _).mp hℓL
  refine ⟨a, ?_, fun b hb => ?_⟩
  · show mixedEmbedding F (a : F) + y ∈ DInf F
    rw [ha]; exact hℓ
  · have hbL : mixedEmbedding F (b : F) ∈ Submodule.span ℤ (Set.range (basisInf F)) := by
      rw [span_basisInf]; exact (mem_Linf_iff _).mpr ⟨b, rfl⟩
    have := huniq ⟨_, hbL⟩ hb
    have h2 : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]; exact congrArg Subtype.val this
    exact RingOfIntegers.coe_injective (mixedEmbedding_injective F h2)

variable (F) in
/-- The fundamental domain $D_\infty\times\hat{\mathcal O}$ for $F$ acting on $\mathbb A_F$ by translation. -/
def fundDom : Set (Adeles F) := DInf F ×ˢ OHat

theorem measurableSet_fundDom : MeasurableSet (fundDom F) :=
  (ZSpan.fundamentalDomain_measurableSet (basisInf F)).prod measurableSet_OHat

/-- **Exactness of the fundamental domain.** Every adele has exactly one $F$-translate in
$D_\infty\times\hat{\mathcal O}$ (strong approximation + the fundamental parallelotope of $\mathcal O_F$). -/
theorem existsUnique_vadd_mem_fundDom (x : Adeles F) : ∃! g : diagSub F, g +ᵥ x ∈ fundDom F := by
  obtain ⟨ξ, hξ⟩ := exists_sub_mem_OHat x.2
  obtain ⟨a, ha, huniq⟩ := existsUnique_add_mem_DInf (mixedEmbedding F (-ξ) + x.1)
  have hfin : ∀ η : F, algebraMap F _ η + x.2 ∈ OHat → ∃ b : 𝓞 F, (b : F) = η + ξ := by
    intro η hη
    have : algebraMap F (FiniteAdeleRing (𝓞 F) F) (η + ξ) ∈ OHat := by
      have := sub_mem_OHat hη hξ
      rw [map_add]
      convert this using 1
      abel
    obtain ⟨b, hb⟩ := (algebraMap_mem_OHat_iff _).mp this
    exact ⟨b, hb⟩
  refine ⟨⟨diag F ((a : F) - ξ), _, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · change mixedEmbedding F ((a : F) - ξ) + x.1 ∈ DInf F
    rw [sub_eq_add_neg, map_add, add_assoc]; exact ha
  · change algebraMap F _ ((a : F) - ξ) + x.2 ∈ OHat
    have hA : algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ OHat :=
      (algebraMap_mem_OHat_iff _).mpr ⟨a, rfl⟩
    rw [map_sub, show algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) - algebraMap F _ ξ + x.2 =
      algebraMap F _ (a : F) + (x.2 - algebraMap F _ ξ) by abel]
    exact add_mem_OHat hA hξ
  · rintro ⟨_, η, rfl⟩ ⟨h1, h2⟩
    change mixedEmbedding F η + x.1 ∈ DInf F at h1
    change algebraMap F _ η + x.2 ∈ OHat at h2
    obtain ⟨b, hb⟩ := hfin η h2
    have : b = a := huniq b (by
      show mixedEmbedding F (b : F) + (mixedEmbedding F (-ξ) + x.1) ∈ DInf F
      rw [hb, map_neg, map_add, ← add_assoc, add_neg_cancel_right]; exact h1)
    subst this
    exact Subtype.ext (congrArg (diag F) (by rw [hb]; ring))

theorem isAddFundamentalDomain_fundDom (μ : Measure (Adeles F)) :
    IsAddFundamentalDomain (diagSub F) (fundDom F) μ :=
  IsAddFundamentalDomain.mk' measurableSet_fundDom.nullMeasurableSet existsUnique_vadd_mem_fundDom

theorem selfDualInf_DInf :
    Analysis.selfDualInf (DInf F) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
  have hcov := Analysis.selfDual_covolume_idealLattice (F := F) 1
  simp only [Units.val_one, map_one, Rat.cast_one, one_mul] at hcov
  have hfd : ZLattice.covolume L∞ volume = volume.real (DInf F) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L∞ volume
      (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L∞) volume)
  have hfin : volume (DInf F) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (basisInf F)).measure_lt_top.ne
  rw [Analysis.selfDualInf, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ← hcov, hfd, Measure.real,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin]
  congr 1
  simp

/-- **$\operatorname{vol}(\mathbb A_F/F) = 1$** for the self-dual measure (Weil 1982, §2.1.3, pp. 12–13: the measure of
$\mathbb A_k/k$ is $|D_k|^{1/2}$ for Weil's normalization, i.e. $1$ for the self-dual one). Here $\mathbb A_F$ is
`Adeles F`, $F$ acts by translation through the diagonal, and the measure is `muAdd F`. -/
@[kb "weil1982" "§2.1.3, pp. 12–13"]
theorem addCovolume_muAdd : addCovolume (diagSub F) (Adeles F) (muAdd F) = 1 := by
  rw [(isAddFundamentalDomain_fundDom (muAdd F)).covolume_eq_volume, fundDom, muAdd,
    Measure.prod_prod, selfDualInf_DInf, muFin_OHat, ← ENNReal.ofReal_mul (by positivity), ohatVol,
    mul_inv_cancel₀ sqrt_abs_discr_pos.ne', ENNReal.ofReal_one]

/-! ### $A = F^\iota$ with coordinatewise structure and $\Lambda = \mathcal O_F^\iota$

For the algebra $A = F^\iota$ (coordinatewise multiplication), $A\otimes\mathbb A_F = \mathbb A_F^\iota$,
$\Lambda_v = \mathcal O_v^\iota$, and the trace form $\operatorname{tr}_{A/F}(xy) = \sum_i x_iy_i$ is the standard pairing,
so its self-dual measure is the product of the self-dual measures. -/

section Vec

set_option synthInstance.maxHeartbeats 200000

variable (F) (ι : Type) [Fintype ι]

/-- $A_{\mathbb A} = \mathbb A_F^\iota$ for $A = F^\iota$. -/
abbrev AdeleSpace : Type := ι → Adeles F

/-- The diagonal embedding $F^\iota \to \mathbb A_F^\iota$. -/
def diagVec : (ι → F) →+ AdeleSpace F ι := AddMonoidHom.compLeft (diag F) ι

omit [Fintype ι] in
@[simp] theorem diagVec_apply (ξ : ι → F) (i : ι) : diagVec F ι ξ i = diag F (ξ i) := rfl

/-- $F^\iota \subset \mathbb A_F^\iota$. -/
def diagVecSub : AddSubgroup (AdeleSpace F ι) := (diagVec F ι).range

/-- The self-dual measure on $\mathbb A_F^\iota$ (trace form of $F^\iota$). -/
def muAddVec : Measure (AdeleSpace F ι) := Measure.pi fun _ : ι => muAdd F

/-- The fundamental domain $(D_\infty\times\hat{\mathcal O})^\iota$. -/
def fundDomVec : Set (AdeleSpace F ι) := Set.univ.pi fun _ : ι => fundDom F

variable {F ι}

omit [Fintype ι] in
theorem diagVec_injective : Function.Injective (diagVec F ι) := fun _ _ h =>
  funext fun i => diag_injective (congrFun h i)

instance countable_diagVecSub : Countable (diagVecSub F ι) := by
  have : Function.Surjective fun ξ : ι → F => (⟨diagVec F ι ξ, ξ, rfl⟩ : diagVecSub F ι) := by
    rintro ⟨_, ξ, rfl⟩; exact ⟨ξ, rfl⟩
  exact this.countable

/-- **$F^\iota$ is discrete in $\mathbb A_F^\iota$.** -/
theorem discreteTopology_diagVecSub : DiscreteTopology (diagVecSub F ι) := by
  obtain ⟨U, hU, h0U, hUdiag⟩ := exists_isOpen_diag_mem_iff (F := F)
  refine discreteTopology_of_isOpen_singleton_zero
    (isOpen_induced_iff.mpr ⟨Set.univ.pi fun _ => U, isOpen_set_pi Set.finite_univ fun _ _ => hU, ?_⟩)
  ext ⟨_, ξ, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi]
  constructor
  · intro h
    have : ξ = 0 := funext fun i => hUdiag (ξ i) (h i)
    subst this
    exact Subtype.ext (map_zero (diagVec F ι))
  · intro h i
    have : diagVec F ι ξ = 0 := congrArg Subtype.val h
    rw [this]; exact h0U

omit [Fintype ι] in
theorem existsUnique_vadd_mem_fundDomVec (x : AdeleSpace F ι) :
    ∃! g : diagVecSub F ι, g +ᵥ x ∈ fundDomVec F ι := by
  choose g hg huniq using fun i => existsUnique_vadd_mem_fundDom (x i)
  choose η hη using fun i => (g i).2
  refine ⟨⟨diagVec F ι η, η, rfl⟩, fun i _ => ?_, ?_⟩
  · show diag F (η i) + x i ∈ fundDom F
    rw [hη i]; exact hg i
  · rintro ⟨_, ζ, rfl⟩ hζ
    refine Subtype.ext (funext fun i => ?_)
    have h1 := huniq i ⟨diag F (ζ i), ζ i, rfl⟩ (hζ i (Set.mem_univ _))
    change diag F (ζ i) = diag F (η i)
    rw [hη i]; exact congrArg Subtype.val h1

theorem isAddFundamentalDomain_fundDomVec (μ : Measure (AdeleSpace F ι)) :
    IsAddFundamentalDomain (diagVecSub F ι) (fundDomVec F ι) μ :=
  IsAddFundamentalDomain.mk'
    (MeasurableSet.univ_pi fun _ => measurableSet_fundDom).nullMeasurableSet
    existsUnique_vadd_mem_fundDomVec

instance : SigmaFinite (muAdd F) := by unfold muAdd; infer_instance

instance measurableAdd_adeles : MeasurableAdd (Adeles F) := ContinuousAdd.measurableAdd

instance : (muAddVec F ι).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance : MeasurableAdd (AdeleSpace F ι) := Pi.measurableAdd

instance : MeasurableConstVAdd (diagVecSub F ι) (AdeleSpace F ι) :=
  AddSubgroup.instMeasurableConstVAdd _

instance : VAddInvariantMeasure (diagVecSub F ι) (AdeleSpace F ι) (muAddVec F ι) :=
  inferInstanceAs (VAddInvariantMeasure (diagVecSub F ι).toAddSubmonoid (AdeleSpace F ι) (muAddVec F ι))

/-- **$\operatorname{vol}(A_{\mathbb A}/A) = 1$ for $A = F^\iota$** (self-dual measure for the trace form). -/
@[kb "weil1982" "§2.1.3, pp. 12–13"]
theorem addCovolume_muAddVec : addCovolume (diagVecSub F ι) (AdeleSpace F ι) (muAddVec F ι) = 1 := by
  rw [(isAddFundamentalDomain_fundDomVec (muAddVec F ι)).covolume_eq_volume, fundDomVec, muAddVec,
    Measure.pi_pi]
  have h := addCovolume_muAdd (F := F)
  rw [(isAddFundamentalDomain_fundDom (muAdd F)).covolume_eq_volume] at h
  simp [h]

end Vec

/-! ### The quaternion case $A = \mathbb H[F,a,b]$, $\Lambda = \mathcal O_F\langle 1,i,j,k\rangle$

Additively $A = \mathbb H[F,a,b] \cong F^4$ through the coordinates in $1, i, j, k$ (`QuaternionAlgebra.linearEquivTuple`),
$\Lambda\otimes\mathcal O_v = \mathcal O_v^4$, and $A_{\mathbb A} = \mathbb A_F^4$. **Normalization caveat:** the self-dual measure
of $A_v$ for $\psi_v\circ\operatorname{trd}(xy)$ is $|\det G|_v^{1/2}$ times the coordinate self-dual measure, $G =
\operatorname{diag}(2, 2a, 2b, -2ab)$ the Gram matrix of $\operatorname{trd}(xy)$ on $1,i,j,k$; by the product formula
$\prod_v|\det G|_v^{1/2}\cdot|\det G|_\infty^{1/2} = 1$, so globally the trace-form self-dual measure is `muAddVec F (Fin 4)`.
That identification (local self-dual measures for a general nondegenerate pairing) is not formalized here. -/

section Quaternion

set_option synthInstance.maxHeartbeats 200000

variable (a b : F)

/-- The diagonal embedding $\mathbb H[F,a,b] \to \mathbb A_F^4$ in the coordinates $1, i, j, k$. -/
def diagQuat : ℍ[F,a,b] →+ AdeleSpace F (Fin 4) :=
  (diagVec F (Fin 4)).comp (QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).toAddMonoidHom

/-- The standard order $\Lambda = \mathcal O_F\langle 1,i,j,k\rangle$ (an order when $a, b \in \mathcal O_F$), as a set. -/
def stdOrder : Set ℍ[F,a,b] :=
  {x | ∀ m, QuaternionAlgebra.linearEquivTuple (R := F) a 0 b x m ∈ (algebraMap (𝓞 F) F).range}

theorem range_diagQuat : (diagQuat a b).range = diagVecSub F (Fin 4) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨ξ, rfl⟩
    refine ⟨(QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm ξ, ?_⟩
    change diagVec F (Fin 4) ((QuaternionAlgebra.linearEquivTuple (R := F) a 0 b)
      ((QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm ξ)) = _
    rw [LinearEquiv.apply_symm_apply]

theorem diagQuat_injective : Function.Injective (diagQuat a b) :=
  diagVec_injective.comp (QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).injective

/-- **$\mathbb H[F,a,b]$ is discrete in $A_{\mathbb A}$.** -/
theorem discreteTopology_diagQuat : DiscreteTopology (diagQuat a b).range := by
  rw [range_diagQuat]; exact discreteTopology_diagVecSub

/-- $x\in\Lambda$ iff the finite components of its diagonal image lie in $\hat\Lambda = \hat{\mathcal O}^4$. -/
theorem mem_stdOrder_iff (x : ℍ[F,a,b]) : x ∈ stdOrder a b ↔ ∀ m, (diagQuat a b x m).2 ∈ OHat :=
  forall_congr' fun _ => (algebraMap_mem_OHat_iff _).symm

/-- **$\operatorname{vol}(A_{\mathbb A}/A) = 1$ for $A = \mathbb H[F,a,b]$** (coordinate self-dual measure; see the
normalization caveat above). -/
theorem addCovolume_diagQuat :
    addCovolume (diagQuat a b).range (AdeleSpace F (Fin 4)) (muAddVec F (Fin 4)) = 1 := by
  rw [range_diagQuat]; exact addCovolume_muAddVec

end Quaternion

end

end QuadFormsKB.Tamagawa.Measure.Weil
