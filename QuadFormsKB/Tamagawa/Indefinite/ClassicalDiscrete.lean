/-
# Unit groups of the lattices in the genus are discrete (Siegel's formula for indefinite forms)

**Layer:** topology of the library's adelic groups. For $b\in SO(V)(\mathbb A_f)$ the unit group
$\Gamma_b$ = `levelGroup (GammaSOAdele Q₀) (KSO Q₀) b` (the image in $G_\infty$ of the elements of $SO(V)(F)$ lying in
$bSO(\hat L)b^{-1}$, i.e. $SO(M_b)$ for the lattice $M_b = b\hat L\cap V$) is a discrete subgroup of $G_\infty$, so it
and the arithmetic stabilizers $\Gamma_{b,y}$ have exact measurable fundamental domains.

**Proves** (unconditional, standard axioms only)
* `discreteTopology_levelGroup`: $\Gamma_b$ is discrete in $G_\infty$ ($SO(V)(F)$ is discrete in $SO(V)(\mathbb A)$,
  `discreteTopology_GammaSOAdele`, and $bSO(\hat L)b^{-1}$ is compact);
* `exists_fd_levelGroup`, `exists_fd_stabArith`: exact measurable fundamental domains of $\Gamma_b$ in $G_\infty$ and of
  $\Gamma_b\cap\operatorname{Stab}(y)$ in $\operatorname{Stab}_{G_\infty}(y)$ (`exists_measurableSet_forall_existsUnique_smul_mem`).
-/
import QuadFormsKB.Tamagawa.Indefinite.ClassicalSetup

open MeasureTheory MulAction Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

/-- **The unit group $\Gamma_b$ is discrete in $G_\infty$.** -/
theorem discreteTopology_levelGroup (b : SOAf Q₀) :
    DiscreteTopology (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) := by
  haveI := discreteTopology_GammaSOAdele Q₀
  have hcl : IsClosed ((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)) :=
    Subgroup.isClosed_of_discreteTopology
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (1 : GInfSO Q₀)
  set M : Set (SOAf Q₀) := (fun x => b * x * b⁻¹) '' (KSO Q₀ : Set (SOAf Q₀)) with hM
  have hMc : IsCompact M :=
    (isCompact_KSO Q₀).image (by fun_prop)
  have hfin : (((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)) ∩ C ×ˢ M).Finite := by
    have hcpt : IsCompact (((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)) ∩ C ×ˢ M) :=
      (hCc.prod hMc).inter_left hcl
    exact hcpt.finite (IsDiscrete.mono (DiscreteTopology.isDiscrete (s :=
      ((GammaSOAdele Q₀ : Subgroup (SOAdele Q₀)) : Set (SOAdele Q₀)))) Set.inter_subset_left)
  set H := levelGroup (GammaSOAdele Q₀) (KSO Q₀) b with hH
  have hHC : ((H : Set (GInfSO Q₀)) ∩ C).Finite := by
    refine (hfin.image Prod.fst).subset ?_
    rintro a ⟨ha, haC⟩
    obtain ⟨g, ⟨hgΓ, hgK⟩, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨g, ⟨hgΓ, haC, ?_⟩, rfl⟩
    refine ⟨b⁻¹ * g.2 * b, hgK, ?_⟩
    simp [mul_assoc]
  set Fs : Set (GInfSO Q₀) := ((H : Set (GInfSO Q₀)) ∩ C) \ {1} with hFs
  have hFsc : IsClosed Fs := (hHC.subset Set.sdiff_subset).isClosed
  have hopen : IsOpen (interior C \ Fs) := isOpen_interior.sdiff hFsc
  rw [discreteTopology_iff_isOpen_singleton_one]
  refine isOpen_induced_iff.mpr ⟨interior C \ Fs, hopen, ?_⟩
  ext ⟨x, hx⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Subgroup.mk_eq_one]
  constructor
  · rintro ⟨hxi, hxF⟩
    by_contra hne
    exact hxF ⟨⟨hx, interior_subset hxi⟩, hne⟩
  · rintro rfl
    exact ⟨mem_interior_iff_mem_nhds.mpr hC, fun h => h.2 rfl⟩

/-- **Exact measurable fundamental domain of $\Gamma_b$ in $G_\infty$.** -/
theorem exists_fd_levelGroup (b : SOAf Q₀) :
    ∃ D : Set (GInfSO Q₀), MeasurableSet D ∧
      ∀ a : GInfSO Q₀, ∃! s : levelGroup (GammaSOAdele Q₀) (KSO Q₀) b, s • a ∈ D := by
  haveI := discreteTopology_levelGroup Q₀ b
  exact exists_measurableSet_forall_existsUnique_smul_mem (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b)

/-- **Exact measurable fundamental domain of the arithmetic stabilizer** $\Gamma_{b,y} = \Gamma_b\cap
\operatorname{Stab}(y)$ in $\operatorname{Stab}_{G_\infty}(y)$, for every $y\in V_\infty$. -/
theorem exists_fd_stabArith (b : SOAf Q₀) (y : VInf F n) :
    ∃ DH : Set (stabilizer (GInfSO Q₀) y), MeasurableSet DH ∧
      ∀ h : stabilizer (GInfSO Q₀) y, ∃! γ : stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y, γ • h ∈ DH := by
  haveI := discreteTopology_levelGroup Q₀ b
  haveI : DiscreteTopology (stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y) :=
    DiscreteTopology.of_continuous_injective
      (f := fun γ : stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y =>
        (⟨((γ : stabilizer (GInfSO Q₀) y) : GInfSO Q₀), γ.2⟩ : levelGroup (GammaSOAdele Q₀) (KSO Q₀) b))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      fun a c hac => Subtype.ext (Subtype.ext (congrArg
        (fun z : levelGroup (GammaSOAdele Q₀) (KSO Q₀) b => (z : GInfSO Q₀)) hac))
  haveI : SecondCountableTopology (stabilizer (GInfSO Q₀) y) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact exists_measurableSet_forall_existsUnique_smul_mem (G := stabilizer (GInfSO Q₀) y)
    (stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y)

end QuadFormsKB.Tamagawa.Indefinite
