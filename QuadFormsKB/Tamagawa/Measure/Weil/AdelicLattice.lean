import QuadFormsKB.Tamagawa.Measure.Weil.GaussLattice
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Approx

/-!
# Lattices cut out by open subgroups of $\mathbb A_f^\iota$, and their covolume

$F$ any number field, $\iota$ finite. For an open subgroup $U\subseteq\mathbb A_f^\iota$ squeezed between $d\hat{\mathcal O}^\iota$
(on $F$-points) and $d^{-1}\hat{\mathcal O}^\iota$ ($d\ne0$ an integer), the $F$-points with finite part in $U$ form a
$\mathbb Z$-lattice $L_U = \{\xi_\infty : \xi\in F^\iota,\ \xi_f\in U\}\subset F_\infty^\iota$ (`adelicLat`):

* `discreteTopology_adelicLat`, `isZLattice_adelicLat`: $L_U$ is discrete and spans $F_\infty^\iota$;
* **`covol_adelicLat_mul`** (the covolume of $F^\iota$ in $\mathbb A_F^\iota$ is $1$): for the fundamental parallelotope $P$ of
  a $\mathbb Z$-basis of $L_U$,
  $$\mu_\infty(P)\cdot\mu_f(U) = 1,$$
  because $P\times U$ is an exact fundamental domain of $F^\iota$ in $\mathbb A_F^\iota$ (density of $F$ in $\mathbb A_f$,
  `denseRange_algebraMap_finiteAdele`).

This is the adelic input of the twisted Poisson formula for $(\mathbb H\otimes\mathbb A)^\times$ (`QuatPoisson.lean`): the
twist $x$ changes $U = \hat\Lambda$ into $x^{-1}\hat\Lambda$, and $\mu_f(x^{-1}\hat\Lambda) = \|\operatorname{nrd}x_f\|_f^{-2}\mu_f(\hat\Lambda)$.

**Outside results used**: Mathlib's `IsZLattice`,
`ZSpan.fundamentalDomain`, `ZSpan.exist_unique_vadd_mem_fundamentalDomain`, `IsAddFundamentalDomain.measure_eq`,
`DenseRange.piMap`; the library's `addCovolume_muAddVec` and `denseRange_algebraMap_finiteAdele`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Pointwise Classical nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "L∞" => mixedEmbedding.idealLattice F (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

variable (F ι) in
/-- $F^\iota\to F_\infty^\iota$ coordinatewise. -/
def jInf : (ι → F) →+ (ι → V) := AddMonoidHom.compLeft (mixedEmbedding F).toAddMonoidHom ι

variable (F ι) in
/-- $F^\iota\to\mathbb A_f^\iota$ coordinatewise. -/
def jFin : (ι → F) →+ (ι → AF) := AddMonoidHom.compLeft (algebraMap F AF).toAddMonoidHom ι

@[simp] theorem jInf_apply (ξ : ι → F) (i : ι) : jInf F ι ξ i = mixedEmbedding F (ξ i) := rfl
@[simp] theorem jFin_apply (ξ : ι → F) (i : ι) : jFin F ι ξ i = algebraMap F AF (ξ i) := rfl

theorem jInf_injective : Function.Injective (jInf F ι) := fun _ _ h =>
  funext fun i => mixedEmbedding_injective F (congrFun h i)

variable (U : AddSubgroup (ι → FiniteAdeleRing (𝓞 F) F))

/-- **The lattice of $U$**: $L_U = \{\xi_\infty : \xi\in F^\iota,\ \xi_f\in U\}$. -/
def adelicLat : Submodule ℤ (ι → V) := ((U.comap (jFin F ι)).map (jInf F ι)).toIntSubmodule

theorem mem_adelicLat {z : ι → V} : z ∈ adelicLat U ↔ ∃ ξ : ι → F, jFin F ι ξ ∈ U ∧ jInf F ι ξ = z := Iff.rfl

theorem jInf_mem_adelicLat {ξ : ι → F} (h : jFin F ι ξ ∈ U) : jInf F ι ξ ∈ adelicLat U := ⟨ξ, h, rfl⟩

/-! ### Discreteness and spanning -/

/-- A neighbourhood of $0$ in $V$ meeting $\mathcal O_F$ only in $0$. -/
theorem exists_isOpen_inter_Linf : ∃ W₀ : Set V, IsOpen W₀ ∧ (0 : V) ∈ W₀ ∧
    ∀ a : 𝓞 F, mixedEmbedding F (a : F) ∈ W₀ → a = 0 := by
  have h0 : IsOpen ({0} : Set L∞) := isOpen_discrete _
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp h0
  refine ⟨W, hW, ?_, fun a ha => ?_⟩
  · have : (0 : L∞) ∈ Subtype.val ⁻¹' W := by rw [hWeq]; rfl
    exact this
  · have hmem : mixedEmbedding F (a : F) ∈ L∞ := (mem_Linf_iff _).mpr ⟨a, rfl⟩
    have : (⟨mixedEmbedding F (a : F), hmem⟩ : L∞) ∈ Subtype.val ⁻¹' W := ha
    rw [hWeq] at this
    have h' : mixedEmbedding F (a : F) = 0 := congrArg Subtype.val this
    have := mixedEmbedding_injective F (h'.trans (map_zero _).symm)
    exact RingOfIntegers.coe_injective (by simpa using this)

/-- **$L_U$ is discrete** when $d\,U\subseteq\hat{\mathcal O}^\iota$. -/
theorem discreteTopology_adelicLat {d : ℕ} (hd : d ≠ 0) (hup : ∀ c ∈ U, ∀ i, (d : AF) * c i ∈ OHat) :
    DiscreteTopology (adelicLat U) := by
  obtain ⟨W₀, hW₀, h0, hW₀int⟩ := exists_isOpen_inter_Linf (F := F)
  set B : Set (ι → V) := {z | ∀ i, (d : V) * z i ∈ W₀}
  have hB : IsOpen B := by
    have : B = ⋂ i, (fun z : ι → V => (d : V) * z i) ⁻¹' W₀ := by ext z; simp [B]
    rw [this]
    exact isOpen_iInter_of_finite fun i => hW₀.preimage (continuous_const.mul (continuous_apply i))
  refine discreteTopology_of_isOpen_singleton_zero (isOpen_induced_iff.mpr ⟨B, hB, ?_⟩)
  ext ⟨z, ξ, hξU, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, B, Set.mem_ofPred_eq]
  constructor
  · intro h
    have hξ : ξ = 0 := funext fun i => by
      have hi := hup _ hξU i
      rw [jFin_apply, show (d : AF) * algebraMap F AF (ξ i) = algebraMap F AF ((d : F) * ξ i) by simp] at hi
      obtain ⟨a, ha⟩ := (algebraMap_mem_OHat_iff _).mp hi
      have hdi := h i
      rw [jInf_apply, show (d : V) * mixedEmbedding F (ξ i) = mixedEmbedding F ((d : F) * ξ i) by simp,
        ← ha] at hdi
      have := hW₀int a hdi
      rw [this, map_zero] at ha
      exact (mul_eq_zero.mp ha.symm).resolve_left (by exact_mod_cast hd)
    subst hξ
    exact Subtype.ext (map_zero (jInf F ι))
  · intro h i
    have : jInf F ι ξ = 0 := congrArg Subtype.val h
    rw [this, Pi.zero_apply, mul_zero]; exact h0

/-- **$L_U$ spans $F_\infty^\iota$** when $d\,\mathcal O_F^\iota\subseteq U$ on $F$-points. -/
theorem isZLattice_adelicLat [DiscreteTopology (adelicLat U)] {d : ℕ} (hd : d ≠ 0)
    (hlow : ∀ ξ : ι → 𝓞 F, jFin F ι (fun i => (d : F) * (ξ i : F)) ∈ U) : IsZLattice ℝ (adelicLat U) := by
  refine ⟨?_⟩
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have h1 : ∀ i (v : V), Pi.single i v ∈ Submodule.span ℝ (adelicLat U : Set (ι → V)) := by
    intro i v
    have hv : v ∈ Submodule.span ℝ (L∞ : Set V) := by
      rw [IsZLattice.span_top (K := ℝ) (L := L∞)]; trivial
    refine Submodule.span_induction (p := fun v _ => Pi.single i v ∈ Submodule.span ℝ (adelicLat U : Set (ι → V)))
      ?_ ?_ ?_ ?_ hv
    · intro x hx
      obtain ⟨a, rfl⟩ := (mem_Linf_iff x).mp hx
      have hmem : jInf F ι (fun j => (d : F) * ((Pi.single i a : ι → 𝓞 F) j : F)) ∈ adelicLat U :=
        jInf_mem_adelicLat U (hlow (Pi.single i a))
      have heq : jInf F ι (fun j => (d : F) * ((Pi.single i a : ι → 𝓞 F) j : F)) =
          (d : ℝ) • Pi.single i (mixedEmbedding F (a : F)) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [Algebra.smul_def, map_natCast]
        · simp [hj]
      have := Submodule.smul_mem (Submodule.span ℝ (adelicLat U : Set (ι → V))) (d : ℝ)⁻¹
        (Submodule.subset_span hmem)
      rwa [heq, smul_smul, inv_mul_cancel₀ hdR, one_smul] at this
    · rw [Pi.single_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [Pi.single_add]; exact add_mem hx hy
    · intro c x _ hx; rw [Pi.single_smul]; exact Submodule.smul_mem _ c hx
  refine eq_top_iff.mpr fun z _ => ?_
  rw [← Finset.univ_sum_single z]
  exact sum_mem fun i _ => h1 i (z i)

/-! ### The covolume -/

theorem denseRange_jFin : DenseRange (jFin F ι) :=
  DenseRange.piMap fun _ => denseRange_algebraMap_finiteAdele

/-- **$P\times U$ is an exact fundamental domain of $F^\iota$ in $\mathbb A_F^\iota$**, for the fundamental parallelotope $P$
of any $\mathbb R$-basis $b$ whose $\mathbb Z$-span is $L_U$. -/
theorem existsUnique_vadd_mem_boxSet {κ : Type*} [Fintype κ] (b : Module.Basis κ ℝ (ι → V))
    (hb : Submodule.span ℤ (Set.range b) = adelicLat U) (hU : IsOpen (U : Set (ι → AF)))
    (y : AdeleSpace F ι) :
    ∃! g : diagVecSub F ι, g +ᵥ y ∈ boxSet (ZSpan.fundamentalDomain b) (U : Set (ι → AF)) := by
  set yI : ι → V := fun i => (y i).1
  set yF : ι → AF := fun i => (y i).2
  have hopen : IsOpen ((fun c => c + yF) ⁻¹' (U : Set (ι → AF))) :=
    hU.preimage (continuous_id.add continuous_const)
  have hne : ((fun c => c + yF) ⁻¹' (U : Set (ι → AF))).Nonempty := ⟨-yF, by simp [zero_mem]⟩
  obtain ⟨_, hξ₀, ξ₀, rfl⟩ := denseRange_jFin.inter_open_nonempty _ hopen hne
  simp only [Set.mem_preimage, SetLike.mem_coe] at hξ₀
  -- translate the archimedean part into P
  obtain ⟨ℓ, hℓ, hℓu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (jInf F ι ξ₀ + yI)
  have hℓL : (ℓ : ι → V) ∈ adelicLat U := hb ▸ ℓ.2
  obtain ⟨μ, hμU, hμ⟩ := (mem_adelicLat U).mp hℓL
  refine ⟨⟨diagVec F ι (ξ₀ + μ), AddMonoidHom.mem_range.mpr ⟨ξ₀ + μ, rfl⟩⟩, ?_, ?_⟩
  · show diagVec F ι (ξ₀ + μ) + y ∈ boxSet (ZSpan.fundamentalDomain b) (U : Set (ι → AF))
    rw [mem_boxSet]
    constructor
    · have : (fun i => ((diagVec F ι (ξ₀ + μ) + y) i).1) = (ℓ : ι → V) + (jInf F ι ξ₀ + yI) := by
        funext i; simp [yI, ← hμ, add_comm, add_left_comm, add_assoc]
      change (fun i => ((diagVec F ι (ξ₀ + μ) + y) i).1) ∈ _
      rw [this]; exact hℓ
    · have : (fun i => ((diagVec F ι (ξ₀ + μ) + y) i).2) = jFin F ι μ + (jFin F ι ξ₀ + yF) := by
        funext i; simp [yF, add_comm, add_left_comm, add_assoc]
      change (fun i => ((diagVec F ι (ξ₀ + μ) + y) i).2) ∈ (U : Set (ι → AF))
      rw [this]; exact U.add_mem hμU hξ₀
  · rintro ⟨_, ξ, rfl⟩ hξ
    change diagVec F ι ξ + y ∈ boxSet (ZSpan.fundamentalDomain b) (U : Set (ι → AF)) at hξ
    rw [mem_boxSet] at hξ
    obtain ⟨hξI, hξF⟩ := hξ
    have hI : ∀ η : ι → F, (fun i => ((diagVec F ι η + y) i).1) = jInf F ι η + yI := fun η => by
      funext i; simp [yI]
    have hF : ∀ η : ι → F, (fun i => ((diagVec F ι η + y) i).2) = jFin F ι η + yF := fun η => by
      funext i; simp [yF]
    change (fun i => ((diagVec F ι ξ + y) i).1) ∈ _ at hξI
    change (fun i => ((diagVec F ι ξ + y) i).2) ∈ (U : Set (ι → AF)) at hξF
    rw [hI] at hξI
    rw [hF] at hξF
    -- the difference lies in L_U and both translates lie in P
    have hdiffU : jFin F ι (ξ - (ξ₀ + μ)) ∈ U := by
      have h2 : jFin F ι (ξ₀ + μ) + yF ∈ U := by
        rw [map_add, add_assoc, add_comm (jFin F ι μ), ← add_assoc]
        exact U.add_mem (by simpa [add_comm] using hξ₀) hμU |> fun h => by simpa [add_comm, add_left_comm,
          add_assoc] using h
      have := U.sub_mem hξF h2
      simpa [map_sub] using this
    have hmem : jInf F ι (ξ - (ξ₀ + μ)) ∈ Submodule.span ℤ (Set.range b) := hb ▸ jInf_mem_adelicLat U hdiffU
    have hP1 : (⟨jInf F ι (ξ - (ξ₀ + μ)), hmem⟩ : Submodule.span ℤ (Set.range b)) +ᵥ
        (jInf F ι (ξ₀ + μ) + yI) ∈ ZSpan.fundamentalDomain b := by
      change jInf F ι (ξ - (ξ₀ + μ)) + (jInf F ι (ξ₀ + μ) + yI) ∈ _
      rw [← add_assoc, ← map_add, sub_add_cancel]; exact hξI
    have hP0 : (0 : Submodule.span ℤ (Set.range b)) +ᵥ (jInf F ι (ξ₀ + μ) + yI) ∈ ZSpan.fundamentalDomain b := by
      rw [zero_vadd, map_add, hμ, add_comm (jInf F ι ξ₀), add_assoc]; exact hℓ
    obtain ⟨_, _, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (jInf F ι (ξ₀ + μ) + yI)
    have := (huniq _ hP1).trans (huniq _ hP0).symm
    have h0 : jInf F ι (ξ - (ξ₀ + μ)) = 0 := congrArg Subtype.val this
    have hξeq : ξ = ξ₀ + μ := sub_eq_zero.mp (jInf_injective (h0.trans (map_zero _).symm))
    subst hξeq; rfl

/-- **The covolume of $L_U$**: $\mu_\infty(P_b)\cdot\mu_f(U) = 1$ for every $\mathbb R$-basis $b$ with $\mathbb Z$-span $L_U$
(the covolume of $F^\iota$ in $\mathbb A_F^\iota$ is $1$, `addCovolume_muAddVec`). -/
@[kb "weil1982" "§2.1.3, pp. 12–13 (vol(𝔸/k) = 1)"]
theorem fundamentalDomain_mul_eq_one {κ : Type*} [Fintype κ] (b : Module.Basis κ ℝ (ι → V))
    (hb : Submodule.span ℤ (Set.range b) = adelicLat U) (hU : IsOpen (U : Set (ι → AF))) :
    muInfVec F ι (ZSpan.fundamentalDomain b) * muFinVec F ι (U : Set (ι → AF)) = 1 := by
  have hmeas : MeasurableSet (boxSet (ZSpan.fundamentalDomain b) (U : Set (ι → AF))) :=
    ((ZSpan.fundamentalDomain_measurableSet b).prod hU.measurableSet).preimage
      (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι).measurable
  have hD : IsAddFundamentalDomain (diagVecSub F ι) (boxSet (ZSpan.fundamentalDomain b) (U : Set (ι → AF)))
      (muAddVec F ι) :=
    IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet (existsUnique_vadd_mem_boxSet U b hb hU)
  rw [← muAddVec_boxSet, hD.measure_eq (isAddFundamentalDomain_fundDomVec (muAddVec F ι)), muAddVec_fundDomVec]

end

end QuadFormsKB.Tamagawa.Measure.Weil

