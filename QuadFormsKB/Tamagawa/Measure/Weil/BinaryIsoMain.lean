import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoSimilar

/-!
# τ = 1 for isotropic binary forms: the transport to $\mathbb G_m$

**Layer:** a number field $F$; $Q_0$ nondegenerate binary over $\mathcal O_F$, $e$ an isotropic vector of $Q_0\otimes F$.

**Defines** `IsoComparison hQ he` (an internal *interface*, proved for every isotropic $(Q_0, e)$ in
`Weil/BinaryIsoFinal.lean`): $\chi_e : SO(V)(\mathbb A)\to\mathbb A_F^\times$ is a measurable group isomorphism (measurable
inverse) carrying $SO(V)(F)$ onto $F^\times$ and `muTam Q₀ hQ lamV` onto `tamIdeles F`.

**Proves**
* `covolume_restrict_eq_of_map`: covolumes of $\Gamma$-invariant measures are transported by measurable group
  isomorphisms (the restricted measures $\mu|_S$ used for τ are not left invariant, only $\Gamma$-invariant);
* `covolume_tamIdeles_logShell`: $\operatorname{covol}(F^\times,\mathbb A_F^\times,\mathrm{tamIdeles}|_{\{\alpha\le\log\|x\|<\beta\}})
  = \rho_F(\beta-\alpha)$;
* **`covolume_isoShellIco_of_comparison`**: given the comparison, $\operatorname{covol}(SO(V)(F),
  \mu^{\mathrm{iso}}_{\mathrm{Tam}}|_{\{\alpha\le\log|\chi_e|<\beta\}}) = \beta-\alpha$; in particular $\tau = 1$;
* invariance of the comparison under similarity $Q_0\mapsto c\,(Q_0\circ G)$, $e\mapsto G^{-1}e$
  (`isoComparison_simForm_iff`), under scaling of $e$ (`isoComparison_smul_iff`) and under equality of forms.
-/

open MeasureTheory Measure Set Matrix Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa QuadFormsKB.QuadForm

/-! ### Transport of covolumes of Γ-invariant measures -/

section Abstract

variable {G G' : Type*} [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul G]
  [MeasurableMul G']

/-- **Covolumes of $\Gamma$-invariant measures are preserved by measurable group isomorphisms** carrying $\Gamma$ onto
$\Gamma'$ and $\mu$ to $\mu'$ (as `covolume_eq_of_map`, with $\Gamma$-invariance instead of left invariance). -/
theorem covolume_restrict_eq_of_map (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ']
    (φ : G ≃* G') (hφ : Measurable φ) (hφ' : Measurable φ.symm) (hΓ : Γ.map φ.toMonoidHom = Γ')
    (μ : Measure G) (μ' : Measure G') [SMulInvariantMeasure Γ G μ] [SMulInvariantMeasure Γ' G' μ']
    (hμ : μ.map φ = μ') : covolume Γ G μ = covolume Γ' G' μ' := by
  have hμ' : μ'.map φ.symm = μ := by
    rw [← hμ, Measure.map_map hφ' hφ]; simp
  have hΓ' : Γ'.map φ.symm.toMonoidHom = Γ := by
    rw [← hΓ, Subgroup.map_map]
    convert Subgroup.map_id Γ
    ext; simp
  by_cases h : HasFundamentalDomain Γ' G' μ'
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' := isFundamentalDomain_preimage Γ Γ' φ hφ hΓ μ μ' hμ hs
    let e : G ≃ᵐ G' := ⟨φ.toEquiv, hφ, hφ'⟩
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, ← hμ, show (φ : G → G') = e from rfl, e.map_apply]
  · have h' : ¬ HasFundamentalDomain Γ G μ := by
      rintro ⟨s, hs⟩
      exact h ⟨_, isFundamentalDomain_preimage Γ' Γ φ.symm hφ' hΓ' μ' μ hμ' hs⟩
    simp only [covolume, h, h', ↓reduceDIte]

/-- The restriction of a $\Gamma$-invariant measure to a $\Gamma$-invariant measurable set is $\Gamma$-invariant. -/
theorem smulInvariantMeasure_restrict (Γ : Subgroup G) (μ : Measure G) [SMulInvariantMeasure Γ G μ] {S : Set G}
    (hS : ∀ (γ : Γ) (x : G), γ • x ∈ S ↔ x ∈ S) : SMulInvariantMeasure Γ G (μ.restrict S) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply hA, Measure.restrict_apply (measurable_const_smul γ hA)]
  have : (fun x => γ • x) ⁻¹' A ∩ S = (fun x => γ • x) ⁻¹' (A ∩ S) := by
    ext x; simp [hS γ x]
  rw [this, measure_preimage_smul]

end Abstract

/-! ### $\mathbb G_m$: the shells of $F^\times\backslash\mathbb A_F^\times$ -/

section Ideles

variable {F : Type} [Field F] [NumberField F]

variable (F) in
/-- The log-norm shell $\{x\in\mathbb A_F^\times : \alpha\le\log\|x\|_{\mathbb A}<\beta\}$. -/
def ideleLogShell (α β : ℝ) : Set (Adeles F)ˣ := (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β

theorem measurableSet_ideleLogShell (α β : ℝ) : MeasurableSet (ideleLogShell F α β) :=
  (Real.measurable_log.comp continuous_ideleNorm.measurable) measurableSet_Ico

/-- The shells are $F^\times$-invariant (product formula). -/
theorem smul_mem_ideleLogShell_iff (α β : ℝ) (γ : diagUnitsSub F) (x : (Adeles F)ˣ) :
    γ • x ∈ ideleLogShell F α β ↔ x ∈ ideleLogShell F α β := by
  obtain ⟨_, ξ, rfl⟩ := γ
  change Real.log (ideleNorm F (diagUnits F ξ * x)) ∈ Ico α β ↔ Real.log (ideleNorm F x) ∈ Ico α β
  rw [ideleNorm_mul, ideleNorm_diagUnits, one_mul]

instance smulInvariantMeasure_tamIdeles : SMulInvariantMeasure (diagUnitsSub F) (Adeles F)ˣ (tamIdeles F) :=
  ⟨fun γ A hA => by
    change tamIdeles F ((fun x => (γ : (Adeles F)ˣ) * x) ⁻¹' A) = tamIdeles F A
    exact measure_preimage_mul _ _ _⟩

instance smulInvariantMeasure_smul_tamIdeles (c : ℝ≥0∞) :
    SMulInvariantMeasure (diagUnitsSub F) (Adeles F)ˣ (c • tamIdeles F) :=
  ⟨fun γ A hA => by
    rw [Measure.smul_apply, Measure.smul_apply]
    congr 1
    change tamIdeles F ((fun x => (γ : (Adeles F)ˣ) * x) ⁻¹' A) = tamIdeles F A
    exact measure_preimage_mul _ _ _⟩

/-- **$\operatorname{covol}(F^\times, c\cdot\mathrm{tamIdeles}|_{\{\alpha\le\log\|x\|<\beta\}}) = c\,\rho_F(\beta-\alpha)$**
(`tamIdeles_exactFD_logShell_eq_residue` on an exact fundamental domain). -/
theorem covolume_tamIdeles_logShell (c : ℝ≥0∞) (α β : ℝ) :
    covolume (diagUnitsSub F) (Adeles F)ˣ ((c • tamIdeles F).restrict (ideleLogShell F α β)) =
      c * (ENNReal.ofReal (dedekindZeta_residue F) * ENNReal.ofReal (β - α)) := by
  have := discreteTopology_diagUnitsSub (F := F)
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (diagUnitsSub F)
  have := smulInvariantMeasure_restrict (diagUnitsSub F) (c • tamIdeles F) (smul_mem_ideleLogShell_iff α β)
  have hFD := IsExactFD.isFundamentalDomain (Γ := diagUnitsSub F) ⟨hDm, hD⟩
    ((c • tamIdeles F).restrict (ideleLogShell F α β))
  rw [hFD.covolume_eq_volume, Measure.restrict_apply hDm, Measure.smul_apply, smul_eq_mul]
  rw [ideleLogShell, tamIdeles_exactFD_logShell_eq_residue ⟨hDm, hD⟩ α β]

end Ideles

/-! ### The comparison $SO(V)\cong\mathbb G_m$ and its consequences -/

section Comparison

variable {F : Type} [Field F] [NumberField F] {Q₀ : QuadForm (𝓞 F) 2} (hQ : Q₀.Nondegenerate) {e : Fin 2 → F}
  (he : IsIsoVec Q₀ e)

/-- **The comparison of $SO(V)$ with $\mathbb G_m$** (an internal interface, proved for every isotropic $(Q_0,e)$ in
`Weil/BinaryIsoFinal.lean`): $\chi_e : SO(V)(\mathbb A)\to\mathbb A_F^\times$ is a bijective measurable homomorphism with
measurable inverse, carries $SO(V)(F)$ onto $F^\times$, and carries Weil's measure `muTam Q₀ hQ lamV`
($\lambda_v = 1-N(v)^{-1}$, no global factor) onto `tamIdeles F` $=\prod_v\lambda_v^{-1}\omega_v$. -/
structure IsoComparison : Prop where
  bijective : Function.Bijective (isoChar hQ he)
  measurable : Measurable (isoChar hQ he)
  measurable_symm : Measurable (MulEquiv.ofBijective (isoChar hQ he) bijective).symm
  gamma : (GammaSOAdele Q₀).map (isoChar hQ he) = diagUnitsSub F
  map_muTam : (muTam Q₀ hQ lamV).map (isoChar hQ he) = tamIdeles F

variable {hQ he}

theorem isoShellIco_eq_preimage (α β : ℝ) :
    isoShellIco Q₀ hQ he α β = isoChar hQ he ⁻¹' ideleLogShell F α β := rfl

/-- $\chi_e$ carries $SO(V)(F)$ into $F^\times$, so the shells are $SO(V)(F)$-invariant. -/
theorem smul_mem_isoShellIco_iff (h : IsoComparison hQ he) (α β : ℝ) (γ : GammaSOAdele Q₀) (g : SOAdele Q₀) :
    γ • g ∈ isoShellIco Q₀ hQ he α β ↔ g ∈ isoShellIco Q₀ hQ he α β := by
  have hγ : isoChar hQ he (γ : SOAdele Q₀) ∈ diagUnitsSub F := by
    rw [← h.gamma]; exact ⟨γ, γ.2, rfl⟩
  rw [isoShellIco_eq_preimage, mem_preimage, mem_preimage,
    show γ • g = (γ : SOAdele Q₀) * g from rfl, map_mul]
  exact smul_mem_ideleLogShell_iff α β ⟨_, hγ⟩ _

instance smulInvariantMeasure_muTamIso :
    SMulInvariantMeasure (GammaSOAdele Q₀) (SOAdele Q₀) (muTamIso Q₀ hQ) :=
  ⟨fun γ A hA => by
    change muTamIso Q₀ hQ ((fun x => (γ : SOAdele Q₀) * x) ⁻¹' A) = muTamIso Q₀ hQ A
    rw [muTamIso, Measure.smul_apply, Measure.smul_apply, measure_preimage_mul]⟩

/-- **The measure comparison**: $(\chi_e)_*\mu^{\mathrm{iso}}_{\mathrm{Tam}} = \rho_F^{-1}\,$`tamIdeles F`. -/
theorem map_muTamIso_of_comparison (h : IsoComparison hQ he) :
    (muTamIso Q₀ hQ).map (isoChar hQ he) = ENNReal.ofReal (dedekindZeta_residue F)⁻¹ • tamIdeles F := by
  rw [muTamIso, Measure.map_smul, h.map_muTam]
  exact h.measurable.aemeasurable

/-- **Every shell has the expected volume**: $\operatorname{covol}(SO(V)(F),
\mu^{\mathrm{iso}}_{\mathrm{Tam}}|_{\{\alpha\le\log|\chi_e|<\beta\}}) = \beta-\alpha$ (given the comparison). -/
theorem covolume_isoShellIco_of_comparison (h : IsoComparison hQ he) (α β : ℝ) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) ((muTamIso Q₀ hQ).restrict (isoShellIco Q₀ hQ he α β)) =
      ENNReal.ofReal (β - α) := by
  have := countable_GammaSOAdele Q₀
  set φ := MulEquiv.ofBijective (isoChar hQ he) h.bijective with hφ
  have hφc : (φ : SOAdele Q₀ → (Adeles F)ˣ) = isoChar hQ he := rfl
  have hφm : Measurable φ := by rw [hφc]; exact h.measurable
  have hΓ : (GammaSOAdele Q₀).map φ.toMonoidHom = diagUnitsSub F := by
    rw [← h.gamma]; rfl
  have := smulInvariantMeasure_restrict (GammaSOAdele Q₀) (muTamIso Q₀ hQ) (smul_mem_isoShellIco_iff h α β)
  have := smulInvariantMeasure_restrict (diagUnitsSub F)
    (ENNReal.ofReal (dedekindZeta_residue F)⁻¹ • tamIdeles F) (smul_mem_ideleLogShell_iff α β)
  have hμ : ((muTamIso Q₀ hQ).restrict (isoShellIco Q₀ hQ he α β)).map φ =
      (ENNReal.ofReal (dedekindZeta_residue F)⁻¹ • tamIdeles F).restrict (ideleLogShell F α β) := by
    rw [isoShellIco_eq_preimage, ← hφc, ← Measure.restrict_map hφm (measurableSet_ideleLogShell α β), hφc,
      map_muTamIso_of_comparison h]
  rw [covolume_restrict_eq_of_map (GammaSOAdele Q₀) (diagUnitsSub F) φ hφm h.measurable_symm hΓ _ _ hμ,
    covolume_tamIdeles_logShell, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (dedekindZeta_residue_pos F).le),
    inv_mul_cancel₀ (dedekindZeta_residue_pos F).ne', ENNReal.ofReal_one, one_mul]

/-- **τ = 1 given the comparison.** -/
theorem tauIso_of_comparison (h : IsoComparison hQ he) : tauIso Q₀ hQ he = 1 := by
  rw [tauIso, isoShell, covolume_isoShellIco_of_comparison h, sub_zero, ENNReal.ofReal_one]

end Comparison

end QuadFormsKB.Tamagawa.Measure.Weil
