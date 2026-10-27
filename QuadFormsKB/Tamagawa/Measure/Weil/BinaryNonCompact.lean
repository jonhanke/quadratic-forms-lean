import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusSplit
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.HaarCovolume

/-!
# Binary $\tau = 2$ for every anisotropic form over every number field: the quotient route

**Layer:** number fields. $F$ any number field, $D\in\mathcal O_F$ with $-D$ not a square, $Q_0 = \langle1,D\rangle$,
$E = F(\delta)$, $\delta^2 = -D$, with the basis $b = (1,\delta)$ (`hb0 : b 0 = 1`, `hb1 : b 1 * b 1 = -D`).

**Defines**
* `muTorSO hb0 hb1 hD` $= \Phi_*\mu_T$ on $SO(V)(\mathbb A)$: Weil's quotient measure `muTor` of $T(\mathbb A) =
  (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$ (the quotient of `tamIdeles E` by `tamIdeles F`), carried to
  $SO(\langle1,D\rangle)(\mathbb A)$ by $\Phi$ = `torAdeleEquiv` ($z\mapsto z/\bar z$, Hilbert 90);
* **`BinaryTorusComparison F`** (target statement, OPEN): for every such $(D, E, b)$,
  $\Phi_*\mu_T = L(1,\chi_E)\cdot\mu^{\chi_E}_{\mathrm{Tam}}$, i.e. `muTorSO … = muTam (diagForm1 D) hQ (lamL (chiE F E))`
  (Weil 1982, Thm 2.3.1: the local ratios and the product formula). It mentions no covolume or Tamagawa number.

**Proves**
* `discreteTopology_torGamma`, **`covolume_muTorSO`**: $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \Phi_*\mu_T) = 2\rho_E/\rho_F$
  for every number field and every $D$ (unconditional; from the residues for $E$ and $F$);
* **`covolume_muTamBin_of_comparison`**: the comparison for $(D,E,b)$ implies $\mathrm{covol}(\mu^{\chi_E}_{\mathrm{Tam}}) = 2$
  ($L(1,\chi_E) = \rho_E/\rho_F$, `lOne_chiE_eq`);
* **`torComparison_of_totallyDefinite`** (consistency test, unconditional): over a totally real $F$ with $\langle1,D\rangle$
  totally definite, the comparison holds (`tauTwo_binary_totallyDefinite` and Haar uniqueness by covolume,
  `eq_of_covolume_eq`);
* **`tauTwoBinaryAll_of_comparison`**: `BinaryTorusComparison F → TauTwoBinaryAll F`.
-/

open MeasureTheory Measure Set Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa
  QuadFormsKB.RegProd QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-! ### Discreteness of $T(F)$ and the covolume of the transported quotient measure -/

section Covolume

variable {D : 𝓞 F}

/-- **$T(F)$ is discrete in $T(\mathbb A)$** (transport of `discreteTopology_GammaSOAdele` along `torAdeleEquiv`). -/
theorem discreteTopology_torGamma (hD : D ≠ 0) : DiscreteTopology (torGamma D) := by
  set e := torAdeleEquiv D hD
  have hmem : ∀ x : torGamma D, e x ∈ GammaSOAdele (diagForm1 D) := fun x => by
    rw [← map_torGamma D hD]; exact ⟨x, x.2, rfl⟩
  have := discreteTopology_GammaSOAdele (diagForm1 D)
  exact DiscreteTopology.of_continuous_injective (f := fun x : torGamma D => (⟨e x, hmem x⟩ :
    GammaSOAdele (diagForm1 D))) ((e.continuous.comp continuous_subtype_val).subtype_mk _)
    fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h))

theorem countable_torGamma (D : 𝓞 F) : Countable (torGamma D) := by
  have : Countable (QuadraticAlgebra F (dD D) 0)ˣ := by
    have : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
    have : Countable (QuadraticAlgebra F (dD D) 0) :=
      Function.Injective.countable (f := fun z : QuadraticAlgebra F (dD D) 0 => (z.re, z.im))
        fun z w h => QuadraticAlgebra.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
    exact Function.Injective.countable (f := (Units.val : (QuadraticAlgebra F (dD D) 0)ˣ → _)) Units.val_injective
  refine Function.Surjective.countable (f := fun z : (QuadraticAlgebra F (dD D) 0)ˣ =>
    (⟨torMk D (quadDiagUnit (dD D) z), ⟨_, ⟨z, rfl⟩, rfl⟩⟩ : torGamma D)) ?_
  rintro ⟨_, ⟨_, ⟨z, rfl⟩, rfl⟩⟩
  exact ⟨z, rfl⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
  (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D))

/-- **Weil's quotient measure on $SO(\langle1,D\rangle)(\mathbb A)$**: $\Phi_*\mu_T$, $\Phi$ = `torAdeleEquiv`. -/
@[kb "weil1982" "§2.4, Thm 2.4.4; Thm 3.2.1, p. 43 [unverified page]; ono1963 [unverified]"]
def muTorSO (hD : D ≠ 0) : Measure (SOAdele (diagForm1 D)) := (muTor hb0 hb1).map (torAdeleEquiv D hD)

theorem isHaarMeasure_muTorSO (hD : D ≠ 0) : (muTorSO hb0 hb1 hD).IsHaarMeasure := by
  have := isHaarMeasure_muTor hb0 hb1
  exact ContinuousMulEquiv.isHaarMeasure_map _ _

/-- **$\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \Phi_*\mu_T) = 2\rho_E/\rho_F$** (every number field, every $D \ne 0$,
every signature; unconditional). -/
@[kb "weil1982" "Thm 3.2.1, p. 43 (centre argument); §2.4 [unverified page]"]
theorem covolume_muTorSO (hD : D ≠ 0) :
    covolume (GammaSOAdele (diagForm1 D)) (SOAdele (diagForm1 D)) (muTorSO hb0 hb1 hD) =
      2 * (ENNReal.ofReal (dedekindZeta_residue E) / ENNReal.ofReal (dedekindZeta_residue F)) := by
  have := discreteTopology_torGamma hD
  have := countable_torGamma D
  have := isHaarMeasure_muTor hb0 hb1
  have := isHaarMeasure_muTorSO hb0 hb1 hD
  rw [← covolume_eq_of_map (torGamma D) (GammaSOAdele (diagForm1 D)) (torAdeleEquiv D hD).toMulEquiv
    (torAdeleEquiv D hD).continuous.measurable (torAdeleEquiv D hD).symm.continuous.measurable
    (map_torGamma D hD) (muTor hb0 hb1) (muTorSO hb0 hb1 hD) rfl]
  exact covolume_muTor_torGamma hb0 hb1

end Covolume

/-! ### Weil's Tamagawa measure is a Haar measure -/

section Haar

open scoped Classical

theorem isHaarMeasure_muTam {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    {lam : HeightOneSpectrum (𝓞 F) → ℝ} (hlam : 0 < finFactor Q₀ lam) : (muTam Q₀ hQ lam).IsHaarMeasure := by
  haveI : (muArchTamSO Q₀ hQ).IsHaarMeasure := by
    have := LerayArch.isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ)
      (gramDetC_QCx_ne_zero Q₀ hQ)
    unfold muArchTamSO LerayArch.muArchNF
    rw [ofReal_smul_eq]
    exact IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))) _) cxWeil_pos)).ne'
  haveI : (Measure.muFin Q₀ lam).IsHaarMeasure := by
    unfold Measure.muFin haarNorm; exact IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr hlam).ne'
  unfold muTam; infer_instance

end Haar

/-! ### The comparison and its consequences -/

section Comparison

/-- **The measure comparison (target statement; proved for every number field: `binaryTorusComparison`,
BinaryTauTwoUncond.lean)**: for every $D\in\mathcal O_F$ with $-D$ not a square, every
quadratic extension $E = F(\delta)$ with $\delta^2 = -D$ given by the basis $b = (1,\delta)$, Weil's quotient measure
$\Phi_*\mu_T$ on $SO(\langle1,D\rangle)(\mathbb A)$ is $L(1,\chi_E)$ times Weil's Tamagawa measure with the convergence factors
of $\chi_E$, i.e. it equals `muTam (diagForm1 D) hQ (lamL (chiE F E))` (Weil 1982, Thm 2.3.1: local ratios and product
formula). An identity between two explicit Haar measures; it mentions no covolume or Tamagawa number. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, product formula); §2.3, p. 21 (convergence factors) [unverified page]"]
def BinaryTorusComparison (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (D : 𝓞 F) (hD : D ≠ 0), ¬ IsSquare (algebraMap (𝓞 F) F (-D)) →
    ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (b : Module.Basis (Fin 2) F E) (hb0 : b 0 = 1)
      (hb1 : b 1 * b 1 = algebraMap F E (dD D)),
      muTorSO hb0 hb1 hD = muTam (diagForm1 D) (nondegenerate_diagForm1 hD) (lamL (chiE F E))

variable {D : 𝓞 F} {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
  (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D))

/-- $E$ is a discriminant field of $\langle1,D\rangle$ ($s = 2\delta$, $s^2 = -4D = -\det H$). -/
theorem isDiscField_of_basis (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D)) :
    IsDiscField (diagForm1 D) E := by
  refine ⟨by rw [Module.finrank_eq_card_basis b, Fintype.card_fin], 2 * b 1, ?_, ?_⟩
  · rw [hessian_det_diagForm1, mul_pow, sq (b 1), hb1]
    simp only [map_neg, map_mul, map_ofNat, dD]
    ring
  · rintro ⟨r, hr⟩
    have h2 : b 1 = (r / 2 : F) • b 0 := by
      rw [hb0, Algebra.smul_def, mul_one, map_div₀, hr, map_ofNat]; field_simp
    have := congrArg (fun x => b.repr x 1) h2
    simp [Module.Basis.repr_self, Finsupp.single_apply] at this

/-- $L(1,\chi_E)^{-1}\cdot\mathrm{covol}(\Phi_*\mu_T) = 2$. -/
theorem lOne_inv_mul_covolume_muTorSO (hD : D ≠ 0) :
    ENNReal.ofReal (LOne (chiE F E))⁻¹ *
      covolume (GammaSOAdele (diagForm1 D)) (SOAdele (diagForm1 D)) (muTorSO hb0 hb1 hD) = 2 := by
  have hdeg : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hE := dedekindZeta_residue_pos E
  have hF := dedekindZeta_residue_pos F
  rw [covolume_muTorSO, lOne_chiE_eq hdeg, inv_div, ENNReal.ofReal_div_of_pos hE]
  have hE0 : ENNReal.ofReal (dedekindZeta_residue E) ≠ 0 := by simpa using hE
  have hF0 : ENNReal.ofReal (dedekindZeta_residue F) ≠ 0 := by simpa using hF
  have hxy : ENNReal.ofReal (dedekindZeta_residue F) / ENNReal.ofReal (dedekindZeta_residue E) *
      (ENNReal.ofReal (dedekindZeta_residue E) / ENNReal.ofReal (dedekindZeta_residue F)) = 1 := by
    simp only [div_eq_mul_inv]
    rw [show ENNReal.ofReal (dedekindZeta_residue F) * (ENNReal.ofReal (dedekindZeta_residue E))⁻¹ *
        (ENNReal.ofReal (dedekindZeta_residue E) * (ENNReal.ofReal (dedekindZeta_residue F))⁻¹) =
        (ENNReal.ofReal (dedekindZeta_residue F) * (ENNReal.ofReal (dedekindZeta_residue F))⁻¹) *
        ((ENNReal.ofReal (dedekindZeta_residue E))⁻¹ * ENNReal.ofReal (dedekindZeta_residue E)) by ring,
      ENNReal.mul_inv_cancel hF0 ENNReal.ofReal_ne_top, ENNReal.inv_mul_cancel hE0 ENNReal.ofReal_ne_top, one_mul]
  rw [mul_left_comm, hxy, mul_one]

/-- **The comparison gives $\tau = 2$**: if $\Phi_*\mu_T = L(1,\chi_E)\,\mu^{\chi_E}_{\mathrm{Tam}}$, then
$\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu^{\chi_E}_{\mathrm{Tam}}) = 2$. -/
@[kb "weil1982" "§2.4, p. 23; Thm 3.2.1, p. 43; Thm 2.3.1 [unverified page]"]
theorem covolume_muTamBin_of_comparison (hD : D ≠ 0)
    (h : muTorSO hb0 hb1 hD = muTam (diagForm1 D) (nondegenerate_diagForm1 hD) (lamL (chiE F E))) :
    covolume (GammaSOAdele (diagForm1 D)) (SOAdele (diagForm1 D))
      (muTamBin (diagForm1 D) (nondegenerate_diagForm1 hD) E) = 2 := by
  have hdeg : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have := countable_GammaSOAdele (diagForm1 D)
  obtain ⟨hL0, -⟩ := lOne_chiE (F := F) (E := E) hdeg
  rw [muTamBin, muTamChi, covolume_smul _ _ (by simpa using hL0), ← h]
  exact lOne_inv_mul_covolume_muTorSO hb0 hb1 hD

/-- **Consistency test** (unconditional): over a totally real field, for $\langle1,D\rangle$ totally definite, the
comparison $\Phi_*\mu_T = L(1,\chi_E)\,\mu^{\chi_E}_{\mathrm{Tam}}$ holds. *Proof:* both are Haar measures; their covolumes
are $2L(1,\chi_E)$ (`lOne_inv_mul_covolume_muTorSO` and `tauTwo_binary_totallyDefinite`), finite and nonzero
(`eq_of_covolume_eq`). -/
@[kb "weil1982" "Thm 2.3.1; Thm 3.7.1 (τ = 2) [unverified page]"]
theorem torComparison_of_totallyDefinite [IsTotallyReal F] (hD : D ≠ 0)
    (hdef : IsTotallyDefinite (diagForm1 D)) :
    muTorSO hb0 hb1 hD = muTam (diagForm1 D) (nondegenerate_diagForm1 hD) (lamL (chiE F E)) := by
  have hdeg : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have := countable_GammaSOAdele (diagForm1 D)
  obtain ⟨hL0, -⟩ := lOne_chiE (F := F) (E := E) hdeg
  have hτ := tauTwo_binary_totallyDefinite (diagForm1 D) (nondegenerate_diagForm1 hD) hdef E
    (isDiscField_of_basis hb0 hb1)
  have hc0 : ENNReal.ofReal (LOne (chiE F E))⁻¹ ≠ 0 := by simpa using hL0
  have hct : ENNReal.ofReal (LOne (chiE F E))⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [muTamBin, muTamChi, covolume_smul _ _ hc0] at hτ
  have heq : covolume (GammaSOAdele (diagForm1 D)) (SOAdele (diagForm1 D)) (muTorSO hb0 hb1 hD) =
      covolume (GammaSOAdele (diagForm1 D)) (SOAdele (diagForm1 D))
        (muTam (diagForm1 D) (nondegenerate_diagForm1 hD) (lamL (chiE F E))) :=
    (ENNReal.mul_right_inj hc0 hct).1 ((lOne_inv_mul_covolume_muTorSO hb0 hb1 hD).trans hτ.symm)
  have hcov0 : covolume (GammaSOAdele (diagForm1 D)) (SOAdele (diagForm1 D))
      (muTam (diagForm1 D) (nondegenerate_diagForm1 hD) (lamL (chiE F E))) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hτ; exact two_ne_zero hτ.symm
  have hcovt : covolume (GammaSOAdele (diagForm1 D)) (SOAdele (diagForm1 D))
      (muTam (diagForm1 D) (nondegenerate_diagForm1 hD) (lamL (chiE F E))) ≠ ⊤ := by
    intro ht; rw [ht, ENNReal.mul_top hc0] at hτ; exact ENNReal.top_ne_ofNat hτ
  have hpos : 0 < finFactor (diagForm1 D) (lamL (chiE F E)) := by
    rcases (finFactor_nonneg (diagForm1 D) (lamL (chiE F E))).lt_or_eq with hlt | h0
    · exact hlt
    · exfalso; apply hcov0
      have hz : Measure.muFin (diagForm1 D) (lamL (chiE F E)) = 0 := by
        unfold Measure.muFin haarNorm; rw [← h0]; simp
      rw [muTam, hz, Measure.prod_zero]
      obtain ⟨s, hs⟩ := (hasFundamentalDomain_GammaSOAdele (diagForm1 D) 0).ExistsIsFundamentalDomain
      rw [hs.covolume_eq_volume]; rfl
  have := isHaarMeasure_muTam (diagForm1 D) (nondegenerate_diagForm1 hD) hpos
  have := isHaarMeasure_muTorSO hb0 hb1 hD
  exact eq_of_covolume_eq _ _ _ heq hcov0 hcovt

end Comparison

/-! ### The headline, conditional on the comparison -/

/-- The basis $(1,\delta)$, $\delta = s/2$, of a discriminant field of $\langle1,D\rangle$. -/
theorem exists_basis_of_isDiscField {D : 𝓞 F} {E : Type} [Field E] [NumberField E] [Algebra F E]
    (h : IsDiscField (diagForm1 D) E) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 * b 1 = algebraMap F E (dD D) := by
  obtain ⟨s, hs, hsF⟩ := h.exists_sqrt
  have hδ : s / 2 ∉ Set.range (algebraMap F E) := by
    rintro ⟨r, hr⟩; exact hsF ⟨2 * r, by rw [map_mul, hr, map_ofNat]; ring⟩
  refine ⟨basisOneDelta (s / 2) hδ h.finrank_eq_two, basisOneDelta_zero _ _ _, ?_⟩
  rw [basisOneDelta_one]
  rw [hessian_det_diagForm1] at hs
  have : s / 2 * (s / 2) = s ^ 2 / 4 := by ring
  rw [this, hs]
  simp only [map_neg, map_mul, map_ofNat, dD]
  ring

/-- **$\tau = 2$ for every anisotropic binary form over $F$, given the measure comparison** (`BinaryTorusComparison F`;
everything else — Hilbert 90, the adelic isomorphism, the covolume $2\rho_E/\rho_F$ — is proved). -/
@[kb "weil1982" "§2.4, p. 23; Thm 3.2.1, p. 43; Thm 2.3.1; ono1963 [unverified]"]
theorem tauTwoBinaryAll_of_comparison (hC : BinaryTorusComparison F) : TauTwoBinaryAll F := by
  rw [tauTwoBinaryAll_iff_diagForm1]
  intro D hsq E _ _ _ hE
  have hD : D ≠ 0 := by
    rintro rfl; apply hsq; exact ⟨0, by simp⟩
  obtain ⟨b, hb0, hb1⟩ := exists_basis_of_isDiscField hE
  have := covolume_muTamBin_of_comparison hb0 hb1 hD (hC D hD hsq E b hb0 hb1)
  rw [← this]

end QuadFormsKB.Tamagawa.Measure.Weil
