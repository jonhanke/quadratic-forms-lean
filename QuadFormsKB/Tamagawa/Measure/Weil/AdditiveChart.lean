import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveAdele

/-!
# The product (chart) description of the self-dual measure on $\mathbb A_f$

`muFin` (`AdditiveAdele.lean`) is defined abstractly: the Haar measure on $\mathbb A_f$ with
$\mu(\hat{\mathcal O}) = |d_F|^{-1/2} = \prod_v\operatorname{vol}_{\mathrm{sd}}(\mathcal O_v)$. Here we identify it with the
infinite product of the local self-dual measures on boxes:

* `infinitePi_map_add_left` (generic): an infinite product of translation-invariant probability measures is
  translation invariant;
* `comap_iK_muFin`: on $\hat{\mathcal O} = \prod_v\mathcal O_v$, `muFin` is $\mu(\hat{\mathcal O})$ times
  `Measure.infinitePi` of the normalized local Haar measures (uniqueness of Haar measure on the compact group
  $\prod_v\mathcal O_v$);
* **`muFin_box`** (chart lemma): for a finite set $S$ of places and measurable $U_v\subseteq\mathcal O_v$ ($v\in S$),
  $\mu\big(\prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v\big) =
  \mu(\hat{\mathcal O})\prod_{v\in S}\mu_v(U_v)/\mu_v(\mathcal O_v)$, and `muFin_box_prod`:
  $= \prod_{v\in S}\mu_v(U_v)\cdot\prod_{v\notin S}\mu_v(\mathcal O_v)$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology RestrictedProduct
open scoped Classical ENNReal NNReal

namespace MeasureTheory.Measure

/-- An infinite product of translation-invariant probability measures on additive groups is translation
invariant. -/
theorem infinitePi_map_add_left {ι : Type*} {X : ι → Type*} [∀ i, AddGroup (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableAdd (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsAddLeftInvariant] (x : ∀ i, X i) :
    map (x + ·) (infinitePi μ) = infinitePi μ := by
  refine eq_infinitePi μ fun s t ht => ?_
  rw [map_apply (measurable_const_add x) (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have : (x + ·) ⁻¹' Set.pi (s : Set ι) t = Set.pi (s : Set ι) fun i => (x i + ·) ⁻¹' t i := by
    ext y; simp [Set.mem_pi]
  rw [this, infinitePi_pi μ (fun i _ => measurable_const_add (x i) (ht i))]
  exact Finset.prod_congr rfl fun i _ => measure_preimage_add (μ i) (x i) (t i)

instance infinitePi_isAddLeftInvariant {ι : Type*} {X : ι → Type*} [∀ i, AddGroup (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableAdd (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsAddLeftInvariant] :
    (infinitePi μ).IsAddLeftInvariant :=
  ⟨infinitePi_map_add_left μ⟩

end MeasureTheory.Measure

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Normalized Haar measure on $\mathcal O_v$ -/

/-- $\operatorname{vol}_{\mathrm{sd}}(\mathcal O_v)$. -/
def volO (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0∞ :=
  Analysis.selfDualV v (v.adicCompletionIntegers F : Set (v.adicCompletion F))

theorem measurableSet_O (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  (isOpen_adicCompletionIntegers v).measurableSet

theorem volO_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < volO v :=
  (isOpen_adicCompletionIntegers v).measure_pos _ ⟨0, zero_mem _⟩

theorem volO_ne_top (v : HeightOneSpectrum (𝓞 F)) : volO v ≠ ⊤ :=
  (isCompact_adicCompletionIntegers v).measure_lt_top.ne

theorem volO_eq_ofReal (v : HeightOneSpectrum (𝓞 F)) :
    volO v = ENNReal.ofReal ((Analysis.selfDualV v).real (Analysis.latticeV v 0)) := by
  rw [volO, coe_adicCompletionIntegers_eq, Measure.real, ENNReal.ofReal_toReal]
  rw [← coe_adicCompletionIntegers_eq]; exact volO_ne_top v

/-- The normalized Haar (probability) measure on $\mathcal O_v$, as a measure on the subtype. -/
def haarO (v : HeightOneSpectrum (𝓞 F)) : Measure (v.adicCompletionIntegers F) :=
  (volO v)⁻¹ • Measure.comap Subtype.val (Analysis.selfDualV v)

theorem haarO_apply (v : HeightOneSpectrum (𝓞 F)) (s : Set (v.adicCompletionIntegers F)) :
    haarO v s = (volO v)⁻¹ * Analysis.selfDualV v (Subtype.val '' s) := by
  rw [haarO, Measure.smul_apply, smul_eq_mul]
  erw [(MeasurableEmbedding.subtype_coe (measurableSet_O v)).comap_apply]
  rfl

instance (v : HeightOneSpectrum (𝓞 F)) : IsProbabilityMeasure (haarO v) := by
  constructor
  rw [haarO_apply, Set.image_univ, Subtype.range_coe]
  exact ENNReal.inv_mul_cancel (volO_pos v).ne' (volO_ne_top v)

instance (v : HeightOneSpectrum (𝓞 F)) : (haarO v).IsAddLeftInvariant := by
  refine ⟨fun x => Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_add x) hs, haarO_apply, haarO_apply]
  congr 1
  have : Subtype.val '' ((x + ·) ⁻¹' s) = ((x : v.adicCompletion F) + ·) ⁻¹' (Subtype.val '' s) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨x + z, hz, rfl⟩
    · rintro ⟨w, hw, hwy⟩
      have hy : y ∈ v.adicCompletionIntegers F := by
        have : y = (w : v.adicCompletion F) - x := by rw [hwy]; ring
        rw [this]; exact sub_mem w.2 x.2
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have : x + ⟨y, hy⟩ = w := Subtype.ext (by rw [hwy]; rfl)
      rw [this]; exact hw
  rw [this, measure_preimage_add]

/-! ### The compact group $\prod_v\mathcal O_v$ and its embedding in $\mathbb A_f$ -/

variable (F) in
/-- $\prod_v\mathcal O_v$ as a product of subtypes. -/
abbrev OProd : Type := ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F

variable (F) in
/-- The infinite product of the normalized local Haar measures on $\prod_v\mathcal O_v$. -/
def nuO : Measure (OProd F) := Measure.infinitePi haarO

variable (F) in
/-- The embedding $\prod_v\mathcal O_v \to \mathbb A_f$ (Mathlib's `structureMap`). -/
def iK : OProd F → AF := fun x => RestrictedProduct.structureMap _ _ cofinite x

@[simp] theorem iK_apply (x : OProd F) (v : HeightOneSpectrum (𝓞 F)) : iK F x v = x v := rfl

theorem isOpenEmbedding_iK : IsOpenEmbedding (iK F) :=
  RestrictedProduct.isOpenEmbedding_structureMap isOpen_adicCompletionIntegers

theorem iK_add (x y : OProd F) : iK F (x + y) = iK F x + iK F y := rfl

theorem range_iK : Set.range (iK F) = OHat := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ v; exact (x v).2
  · intro hy; exact ⟨fun v => ⟨y v, hy v⟩, rfl⟩

theorem measurableEmbedding_iK : MeasurableEmbedding (iK F) :=
  isOpenEmbedding_iK.measurableEmbedding

/-! ### Uniqueness of Haar measure on $\prod_v\mathcal O_v$ -/

example : CompactSpace (OProd F) := inferInstance
example : BorelSpace (OProd F) := inferInstance
example : IsTopologicalAddGroup (OProd F) := inferInstance
example : SecondCountableTopology (OProd F) := inferInstance

instance : (nuO F).IsAddLeftInvariant := by unfold nuO; infer_instance

instance : IsProbabilityMeasure (nuO F) := by unfold nuO; infer_instance

instance : (Measure.comap (iK F) (muFin F)).IsAddLeftInvariant := by
  refine ⟨fun x => Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_add x) hs, measurableEmbedding_iK.comap_apply,
    measurableEmbedding_iK.comap_apply]
  have : iK F '' ((x + ·) ⁻¹' s) = (iK F x + ·) ⁻¹' (iK F '' s) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨x + z, hz, (iK_add x z)⟩
    · rintro ⟨w, hw, hwy⟩
      have hy : y ∈ Set.range (iK F) := by
        rw [range_iK]
        have : y = iK F w - iK F x := by rw [hwy]; abel
        rw [this]
        exact sub_mem_OHat (range_iK (F := F) ▸ ⟨w, rfl⟩) (range_iK (F := F) ▸ ⟨x, rfl⟩)
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_, rfl⟩
      have : x + z = w := isOpenEmbedding_iK.injective (by rw [iK_add, hwy])
      rw [this]; exact hw
  rw [this, measure_preimage_add]

theorem comap_iK_univ : Measure.comap (iK F) (muFin F) Set.univ = muFin F OHat := by
  rw [measurableEmbedding_iK.comap_apply, Set.image_univ, range_iK]

instance : IsFiniteMeasure (Measure.comap (iK F) (muFin F)) :=
  ⟨by rw [comap_iK_univ, muFin_OHat]; exact ENNReal.ofReal_lt_top⟩

/-- **`muFin` on $\hat{\mathcal O}$ is the infinite product of the local measures:** the pull-back of `muFin`
to $\prod_v\mathcal O_v$ is $\mu(\hat{\mathcal O})\cdot\bigotimes_v\big(\mu_v|_{\mathcal O_v}/\mu_v(\mathcal O_v)\big)$
(uniqueness of Haar measure on the compact group $\prod_v\mathcal O_v$). -/
theorem comap_iK_muFin : Measure.comap (iK F) (muFin F) = muFin F OHat • nuO F := by
  set lam := Measure.comap (iK F) (muFin F)
  have h1 := Measure.isAddInvariant_eq_smul_of_compactSpace lam (Measure.addHaar (G := OProd F))
  have h2 := Measure.isAddInvariant_eq_smul_of_compactSpace (nuO F) (Measure.addHaar (G := OProd F))
  set c₁ := Measure.addHaarScalarFactor lam Measure.addHaar
  set c₂ := Measure.addHaarScalarFactor (nuO F) Measure.addHaar
  have hc₂ : (c₂ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have : (nuO F) Set.univ = 0 := by
      rw [h2, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]
    simp at this
  have h3 : lam = ((c₁ : ℝ≥0∞) * (c₂ : ℝ≥0∞)⁻¹) • nuO F := by
    rw [h1]
    conv_rhs => rw [h2]
    ext s hs
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
    rw [← mul_assoc, mul_assoc (c₁ : ℝ≥0∞), ENNReal.inv_mul_cancel hc₂ ENNReal.coe_ne_top, mul_one]
  have h4 : lam Set.univ = (c₁ : ℝ≥0∞) * (c₂ : ℝ≥0∞)⁻¹ := by
    rw [h3, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← comap_iK_univ, h4]
  exact h3

/-! ### The chart lemma -/

/-- **Chart lemma (normalized form).** For a finite set $S$ of finite places and measurable
$U_v \subseteq \mathcal O_v$ ($v \in S$), `muFin` of the box $\prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v$ is
$\mu(\hat{\mathcal O})\prod_{v\in S}\mu_v(U_v)/\mu_v(\mathcal O_v)$. -/
theorem muFin_box (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (hUm : ∀ v ∈ S, MeasurableSet (U v))
    (hUO : ∀ v ∈ S, U v ⊆ v.adicCompletionIntegers F) :
    muFin F {x | (∀ v ∈ S, x v ∈ U v) ∧ x ∈ OHat} =
      muFin F OHat * ∏ v ∈ S, (volO v)⁻¹ * Analysis.selfDualV v (U v) := by
  set t : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletionIntegers F) := fun v => Subtype.val ⁻¹' U v
  have hbox : {x : AF | (∀ v ∈ S, x v ∈ U v) ∧ x ∈ OHat} = iK F '' Set.pi (S : Set _) t := by
    ext y
    constructor
    · rintro ⟨hS, hO⟩
      refine ⟨fun v => ⟨y v, hO v⟩, fun v hv => hS v hv, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fun v hv => hx v hv, fun v => (x v).2⟩
  have htm : ∀ v ∈ S, MeasurableSet (t v) := fun v hv =>
    measurable_subtype_coe (hUm v hv)
  rw [hbox, ← measurableEmbedding_iK.comap_apply, comap_iK_muFin, Measure.smul_apply, smul_eq_mul,
    nuO, Measure.infinitePi_pi _ htm]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [haarO_apply]
  congr 2
  ext z
  simp only [Set.mem_image, Set.mem_preimage, t]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact hw
  · intro hz; exact ⟨⟨z, hUO v hv hz⟩, hz, rfl⟩

/-- The real local volume $\operatorname{vol}_{\mathrm{sd}}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$; it is $1$ off the
(finitely many) places dividing the different. -/
theorem mulSupport_volO_real_finite :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (Analysis.selfDualV v).real (Analysis.latticeV v 0)).Finite := by
  refine (Analysis.finite_support_diffExp (F := F)).subset fun v hv => ?_
  rw [Function.mem_mulSupport] at hv
  rw [Function.mem_support]
  intro h0
  apply hv
  have h0' : Analysis.diffExp v = 0 := by exact_mod_cast h0
  rw [Analysis.selfDualV_real_latticeV_eq, h0']
  simp

/-- **Chart lemma (product form).** For a finite set $S$ of finite places and measurable $U_v\subseteq\mathcal O_v$
($v\in S$):
$$\mu_f\Big(\prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v\Big) =
\prod_{v\in S}\mu_v(U_v)\cdot\prod_{v\notin S}\mu_v(\mathcal O_v),$$
$\mu_v$ the local self-dual measures (`selfDualV`). -/
theorem muFin_box_prod (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (hUm : ∀ v ∈ S, MeasurableSet (U v))
    (hUO : ∀ v ∈ S, U v ⊆ v.adicCompletionIntegers F) :
    muFin F {x | (∀ v ∈ S, x v ∈ U v) ∧ x ∈ OHat} =
      (∏ v ∈ S, Analysis.selfDualV v (U v)) *
        ENNReal.ofReal (∏ᶠ (v) (_ : v ∉ S), (Analysis.selfDualV v).real (Analysis.latticeV v 0)) := by
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (Analysis.selfDualV v).real (Analysis.latticeV v 0)
  have hr0 : ∀ v, 0 ≤ r v := fun v => measureReal_nonneg
  have hsplit : ∏ᶠ v, r v = (∏ v ∈ S, r v) * ∏ᶠ (v) (_ : v ∉ S), r v := by
    rw [← finprod_mem_univ, ← Set.union_compl_self (S : Set (HeightOneSpectrum (𝓞 F))),
      finprod_mem_union' disjoint_compl_right (S.finite_toSet.inter_of_left _)
        (mulSupport_volO_real_finite.inter_of_right _), finprod_mem_coe_finset]
    rfl
  have hnn : 0 ≤ ∏ᶠ (v) (_ : v ∉ S), r v :=
    finprod_nonneg fun v => finprod_nonneg fun _ => hr0 v
  rw [muFin_box S U hUm hUO, muFin_OHat, ohatVol_eq_finprod, hsplit,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hr0 v), ENNReal.ofReal_prod_of_nonneg
      (fun v _ => hr0 v), Finset.prod_mul_distrib]
  have hv : ∀ v, ENNReal.ofReal (r v) = volO v := fun v => (volO_eq_ofReal v).symm
  simp_rw [hv]
  rw [mul_comm (∏ v ∈ S, volO v), mul_assoc, ← mul_assoc (∏ v ∈ S, volO v), ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl fun v _ => ENNReal.mul_inv_cancel (volO_pos v).ne' (volO_ne_top v),
    Finset.prod_const_one, one_mul, mul_comm]

end

end QuadFormsKB.Tamagawa.Measure.Weil
