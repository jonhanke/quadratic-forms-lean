/-
# The measures on a binary anisotropic stabilizer, and the character of $\delta$ over every number field

**Layer:** number fields, adeles. $Q'$ a nondegenerate **anisotropic** binary form over $\mathcal O_F$, $\chi$ a character with
$|\chi|\le1$, equal to the `chiP · Q'` off a finite set, with $L(1,\chi)$ existing.

**Proves**
* `covolume_muTam_one_binary`: Weil's $\tau(SO(Q')) = 2$ (`tauTwoBinaryAll_uncond`, measure `muTamBin`) in terms of the
  measure without convergence factors:
  $$\operatorname{covol}(\texttt{muTam Q' 1})\cdot\prod'_v\frac{\alpha_v(L')}{1-\chi(v)/Nv} = 2\,L(1,\chi)\,\prod'_v\alpha_v(L').$$
  (Both products are Mathlib `tprod`s; the left one has finite support, the right one is positive,
  `finFactor_one_pos_of_anisotropicF`; neither side involves a junk value except through the factor that cancels.)
* `lOne_chiForms_nf`, `chiP_frame_eq_chiForms_nf`: for $\delta = -\det H_{Q_0}\det H_{T_0}$ not a square, over every number
  field, $L(1,\chi)$ exists and is positive for $\chi$ = `chiForms Q₀ T₀`, and $\chi$ is the character of the binary
  complement of every adapted frame off a finite set (the proofs of the totally real versions in `FrameSiegelReg.lean`,
  without positivity).
-/
import QuadFormsKB.Tamagawa.Indefinite.Rank2Tower
import QuadFormsKB.Tamagawa.Indefinite.Rank2Weil

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Frames QuadFormsKB.RegProd NFEuler LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-! ### The character of $\delta$ over every number field -/

section Char

variable {N r : ℕ}

/-- **$F(\sqrt\delta)$** for $\delta\in\mathcal O_F$ not a square (every number field): a quadratic extension $E$ with
$s^2 = \delta$ and $\sigma s = -s$ for its nontrivial automorphism. -/
theorem exists_sqrtExt_nf {δ : 𝓞 F} (hd : ¬ IsSquare (algebraMap (𝓞 F) F δ)) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (_ : Algebra.IsQuadraticExtension F E) (s : E),
      s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F δ) ∧ Binary.Rel.conj F E s = -s := by
  obtain ⟨E, _, _, _, s, hs, hspan⟩ := Lam.exists_quadExt _ hd
  obtain ⟨hQ, -⟩ := HN.quadData _ hd s hs hspan
  refine ⟨E, inferInstance, inferInstance, inferInstance, hQ, s, hs, ?_⟩
  have hsq : (Binary.Rel.conj F E s - s) * (Binary.Rel.conj F E s + s) = 0 := by
    have : (Binary.Rel.conj F E s) ^ 2 = s ^ 2 := by
      rw [← map_pow, hs, AlgEquiv.commutes]
    linear_combination this
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso
    apply Binary.Rel.conj_ne_one F E
    ext y
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    rw [sub_eq_zero] at h
    simp [h]
  · linear_combination h

/-- **$L(1,\chi)$ exists and is positive** for $\chi$ = `chiForms Q₀ T₀`, $\delta$ not a square, every number field. -/
theorem lOne_chiForms_nf {Q₀ : QuadForm (𝓞 F) N} {T₀ : QuadForm (𝓞 F) r} (hQ : Q₀.Nondegenerate)
    (hT : T₀.Nondegenerate) (hW : ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) :
    0 < LOne (chiForms Q₀ T₀) ∧ HasLOne (chiForms Q₀ T₀) (LOne (chiForms Q₀ T₀)) := by
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_nf hW
  exact exists_hasLOne_of_almost_relChar (Algebra.IsQuadraticExtension.finrank_eq_two F E)
    (fun v => abs_chiForms_le Q₀ T₀ v) (isAlmostRelChar_chiForms hQ hT hs hsc)

/-- **$\chi$ is the character of the binary complement off a finite set** (every number field). -/
theorem chiP_frame_eq_chiForms_nf (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r) (hQ : Q₀.Nondegenerate)
    (hT : T₀.Nondegenerate) (hW : ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))) (hQ' : fr.Q'.Nondegenerate) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, chiP v fr.Q' = chiForms Q₀ T₀ v := by
  classical
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_nf hW
  have hb : algebraMap (𝓞 F) F T₀.hessian.det ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  have hS₁ : IsAlmostRelChar (fun v => chiP v fr.Q') E := by
    obtain ⟨u, hu⟩ : ∃ u : F, u = (algebraMap (𝓞 F) F T₀.hessian.det)⁻¹ := ⟨_, rfl⟩
    have hbu : algebraMap (𝓞 F) F T₀.hessian.det * u = 1 := by rw [hu]; exact mul_inv_cancel₀ hb
    refine isAlmostRelChar_of_sqrt (neg_ne_zero.2 hQ') (θ := s * algebraMap F E (fr.g.val.det * u)) ?_ ?_ ∅
      fun v _ h2 hδ => ?_
    · have hrel := det_frame_forms Q₀ T₀ fr
      rw [mul_pow, hs, ← map_pow, ← map_mul]
      congr 1
      simp only [deltaForms, map_mul, map_neg]
      linear_combination (-(algebraMap (𝓞 F) F T₀.hessian.det) * u ^ 2) * hrel
        + (-(algebraMap (𝓞 F) F fr.Q'.hessian.det) * (1 + algebraMap (𝓞 F) F T₀.hessian.det * u)) * hbu
    · rw [map_mul, hsc, AlgEquiv.commutes]; ring
    · exact chiP_binary_eq_charNF v fr.Q' h2 fun h => hδ (v.asIdeal.neg_mem_iff.2 h)
  obtain ⟨S₁, hS₁⟩ := hS₁
  obtain ⟨S₂, hS₂⟩ := isAlmostRelChar_chiForms hQ hT hs hsc
  refine ⟨S₁ ∪ S₂, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact (hS₁ v hv.1).trans (hS₂ v hv.2).symm

end Char

/-! ### A binary anisotropic stabilizer: the measure without convergence factors against Weil's -/

section Binary

variable (Q' : QuadForm (𝓞 F) 2) (hQ' : Q'.Nondegenerate) {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
  (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, chiP v Q' = χ v)

include hQ' hχ hS in
/-- With $\lambda_v = 1-\chi(v)/Nv$ the local masses $\lambda_v^{-1}\alpha_v(L')$ are $1$ off a finite set. -/
theorem muLocSO_lamL_eq_one_eventually :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S',
      (muLocSO v Q' (lamL χ v) (soStabSO v Q' : Set (SOv v Q'))).toReal = 1 := by
  classical
  have hfin := hasFiniteMulSupport_siegelDensity_binary_reg hQ' S hS
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  have h1 : NF.siegelDensity v Q' Q' * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = 1 := by
    by_contra hne
    exact hv (hfin.mem_toFinset.mpr hne)
  rw [muLocSO_soStabSO, ENNReal.toReal_ofReal (div_nonneg (siegelDensity_self_pos' Q' hQ' v).le
    (lamL_pos hχ v).le), ← h1, _root_.zpow_neg_one, div_eq_mul_inv, lamL]

include hQ' hχ hS in
theorem multipliable_muLocSO_lamL :
    Multipliable fun v => (muLocSO v Q' (lamL χ v) (soStabSO v Q' : Set (SOv v Q'))).toReal := by
  obtain ⟨S', hS'⟩ := muLocSO_lamL_eq_one_eventually Q' hQ' hχ S hS
  exact (hasProd_prod_of_ne_finset_one hS').multipliable

include hQ' hχ hS in
/-- $\prod'_v\lambda_v^{-1}\alpha_v(L') > 0$ (a finite product of positive numbers). -/
theorem finFactor_lamL_pos : 0 < finFactor Q' (lamL χ) := by
  obtain ⟨S', hS'⟩ := muLocSO_lamL_eq_one_eventually Q' hQ' hχ S hS
  rw [finFactor, (hasProd_prod_of_ne_finset_one hS').tprod_eq]
  exact Finset.prod_pos fun v _ => ENNReal.toReal_pos (muLocSO_soStabSO_pos Q' hQ' v (lamL_pos hχ v))
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)

include hχ hS in
/-- **Weil's $\tau(SO(Q')) = 2$ in terms of `muTam Q' 1`** ($Q'$ binary, anisotropic):
$\operatorname{covol}(\texttt{muTam Q' 1})\cdot\prod'_v\lambda_v^{-1}\alpha_v = 2\,L(1,\chi)\prod'_v\alpha_v$,
$\lambda_v = 1-\chi(v)/Nv$. -/
theorem covolume_muTam_one_binary (hA : AnisotropicF Q') (hL : HasLOne χ (LOne χ)) (hL0 : 0 < LOne χ) :
    covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' fun _ => 1) * ENNReal.ofReal (finFactor Q' (lamL χ)) =
      2 * ENNReal.ofReal (LOne χ) * ENNReal.ofReal (finFactor Q' fun _ => 1) := by
  have := countable_GammaSOAdele Q'
  obtain ⟨E, _, _, _, hE⟩ := exists_isDiscField_of_anisotropicF hA
  have hτ := tauTwoBinaryAll_uncond F Q' hQ' hA E hE
  set M := (muArchTamSO Q' hQ').prod (muFinOne Q') with hM
  have hf1 := finFactor_one_pos_of_anisotropicF Q' hQ' hA
  have hfl := finFactor_lamL_pos Q' hQ' hχ S hS
  -- `muTamBin = L(1,χ)⁻¹ ∏' λ⁻¹α · M`
  have hreg : regProd (fun v => chiP v Q') (-1) (fun v => NF.siegelDensity v Q' Q') =
      (LOne χ)⁻¹ * finFactor Q' (lamL χ) := by
    rw [regProd_congr_finite (abs_chiP_le Q') hχ S hS hL (-1) _
      (multipliable_of_hasFiniteMulSupport (hasFiniteMulSupport_siegelDensity_binary_reg hQ' S hS)),
      regProd, finFactor_lamL_eq Q' hQ' hχ, zpow_neg_one]
  rw [muTamBin_eq_chiP Q' hQ' hE, hreg, covolume_smul _ _ (ENNReal.ofReal_pos.2
    (mul_pos (inv_pos.2 hL0) hfl)).ne'] at hτ
  have h1 : muTam Q' hQ' (fun _ => 1) = ENNReal.ofReal (finFactor Q' fun _ => 1) • M := by
    rw [muTam, muFin_eq_smul_muFinOne, Measure.prod_smul_right]
  rw [h1, covolume_smul _ _ (ENNReal.ofReal_pos.2 hf1).ne', ← hτ, ENNReal.ofReal_mul (inv_nonneg.2 hL0.le),
    ENNReal.ofReal_inv_of_pos hL0]
  have hL1 : ENNReal.ofReal (LOne χ) ≠ 0 := (ENNReal.ofReal_pos.2 hL0).ne'
  have hL2 : ENNReal.ofReal (LOne χ) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ENNReal.ofReal (finFactor Q' fun _ => 1) * covolume (GammaSOAdele Q') (SOAdele Q') M *
        ENNReal.ofReal (finFactor Q' (lamL χ))
      = ENNReal.ofReal (finFactor Q' fun _ => 1) * (ENNReal.ofReal (finFactor Q' (lamL χ)) *
          covolume (GammaSOAdele Q') (SOAdele Q') M) := by ring
    _ = ENNReal.ofReal (finFactor Q' fun _ => 1) * ((ENNReal.ofReal (LOne χ))⁻¹ * ENNReal.ofReal (LOne χ) *
          (ENNReal.ofReal (finFactor Q' (lamL χ)) * covolume (GammaSOAdele Q') (SOAdele Q') M)) := by
        rw [ENNReal.inv_mul_cancel hL1 hL2, one_mul]
    _ = _ := by ring

end Binary

end QuadFormsKB.Tamagawa.Indefinite
