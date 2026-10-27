import QuadFormsKB.Tamagawa.Measure.Weil.BinaryMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarGlobal

/-!
# Similar binary forms have the same Tamagawa covolume
**Layer:** a number field $F$; $Q_0$ a nondegenerate binary form over $\mathcal O_F$, $G\in M_2(\mathcal O_F)$ with
$\det G\ne0$, $c\in\mathcal O_F\setminus0$, $Q_1 = c\,(Q_0\circ G)$ (`simForm`), $E$ a discriminant field of $Q_0$.

The general `covolume_muTam_simForm` needs $n\ne2$ (the product $\prod_v\alpha_v$ must converge
absolutely). For $n = 2$ the convergence factors $\lambda_v = L_v(1,\chi_E)^{-1}$ make both products
finitely supported, and the same proof goes through.

**Proves**
* `isDiscField_simForm`: $E$ is also a discriminant field of $Q_1$ ($\det H_1 = c^2\det(G)^2\det H_0$);
* `map_muFin_simConjFin_lamL`: $(g\mapsto G^{-1}gG)_*\mu^{\lambda}_{f,Q_0} = \prod_v\|\delta\|_v\cdot\mu^{\lambda}_{f,Q_1}$,
  $\delta = c^3\det(G)^3$;
* **`covolume_muTamBin_simForm`**: $\mathrm{covol}(SO(V_1)(F),\mu^{\chi_E}_{\mathrm{Tam}}) =
  \mathrm{covol}(SO(V_0)(F),\mu^{\chi_E}_{\mathrm{Tam}})$ (product formula); **`tauTwoBinaryAdelic_simForm_iff`**.

Source: Weil 1982, §2.3, Thm 2.3.1, pp. 21–22 (independence of choices, product formula).
-/

open MeasureTheory Measure Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
  QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.RegProd QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F] {Q₀ : QuadForm (𝓞 F) 2} {c : 𝓞 F}
  {G : Matrix (Fin 2) (Fin 2) (𝓞 F)} {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem hessian_det_simForm : (simForm Q₀ c G).hessian.det = c ^ 2 * G.det ^ 2 * Q₀.hessian.det := by
  rw [simForm, LatChange.hessian_smul, hessian_compMat, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Fintype.card_fin]
  ring

/-- **The discriminant field is unchanged under similarity.** -/
theorem isDiscField_simForm (h : IsDiscField Q₀ E) (hc : c ≠ 0) (hG : G.det ≠ 0) :
    IsDiscField (simForm Q₀ c G) E := by
  obtain ⟨s, hs, hsF⟩ := h.exists_sqrt
  refine ⟨h.finrank_eq_two, algebraMap F E (algebraMap (𝓞 F) F (c * G.det)) * s, ?_, ?_⟩
  · rw [mul_pow, hs, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hessian_det_simForm]
    congr 2; ring
  · rintro ⟨r, hr⟩
    have hu : (algebraMap (𝓞 F) F (c * G.det)) ≠ 0 :=
      (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (mul_ne_zero hc hG)
    apply hsF
    refine ⟨r / algebraMap (𝓞 F) F (c * G.det), ?_⟩
    rw [map_div₀, hr, mul_div_cancel_left₀ _ ((map_ne_zero _).mpr hu)]

/-- **The finite Tamagawa measures of similar binary forms** (convergence factors $\lambda_v = L_v(1,\chi_E)^{-1}$):
$(g\mapsto G^{-1}gG)_*\mu^{\lambda}_{f,Q_0} = \prod'_v\|\delta\|_v\cdot\mu^{\lambda}_{f,Q_1}$. -/
theorem map_muFin_simConjFin_lamL (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) (h : IsDiscField Q₀ E) :
    (muFin Q₀ (lamL (chiE F E))).map (simConjFin hc hG) =
      ENNReal.ofReal (∏' v : HeightOneSpectrum (𝓞 F),
          ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖) •
        muFin (simForm Q₀ c G) (lamL (chiE F E)) := by
  classical
  have hn : 0 < 2 := two_pos
  have hQ₁ := nondegenerate_simForm hQ hc hG
  have h₁ := isDiscField_simForm h hc hG
  have : LocallyCompactSpace (SOAf (simForm Q₀ c G)) :=
    (isClosed_soAf _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hχ := abs_chiE_le h.finrank_eq_two
  have hlam : ∀ v, 0 < lamL (chiE F E) v := lamL_pos hχ
  set lam := lamL (chiE F E) with hlamdef
  set S := (simBad_finite hc hG).toFinset with hS
  set e := simConjFin (Q₀ := Q₀) hc hG with he
  have hmeas : Measurable e := e.continuous.measurable
  set nδ : HeightOneSpectrum (𝓞 F) → ℝ :=
    fun v => ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ with hnδ
  set α₀ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀ with hα₀def
  set α₁ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v (simForm Q₀ c G) (simForm Q₀ c G)
    with hα₁def
  have hα₀ : ∀ v, 0 < α₀ v := fun v => siegelDensity_self_pos' Q₀ hQ v
  have hα₁ : ∀ v, 0 < α₁ v := fun v => siegelDensity_self_pos' _ hQ₁ v
  have hnδpos : ∀ v, 0 < nδ v := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr (coe_ne_zero_of_ne_zero (simJac_ne_zero hc hG)))
  have hnδ1 : ∀ v ∉ S, nδ v = 1 := fun v hv =>
    (NumberField.FinitePlace.norm_eq_one_iff_notMem F v _).mpr (by simpa [hS] using hv)
  have : IsMulLeftInvariant ((muFin Q₀ lam).map e) :=
    isMulLeftInvariant_map e.toMulEquiv.toMonoidHom.toMulHom hmeas e.surjective
  have : SigmaFinite ((muFin Q₀ lam).map e) :=
    (e.toHomeomorph.toMeasurableEquiv).sigmaFinite_map
  have hμK : ∀ v, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (α₀ v) := fun v => by
    rw [muLocSO_soStabSO, div_one]
  have hμU : ∀ v, muLocSO v Q₀ 1 (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
      (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) = ENNReal.ofReal (nδ v * α₁ v) := fun v => by
    rw [sim_muLocSO_simU hn hQ v hc hG, ENNReal.ofReal_mul (hnδpos v).le]
  have hgood : ∀ v ∉ S, α₀ v = α₁ v := fun v hv =>
    sim_alpha_eq_of_good hn hQ v hc hG (by simpa [hS] using hv)
  -- the two finitely supported products
  obtain ⟨S₀, hS₀⟩ := chiP_eq_chiE Q₀ h
  obtain ⟨S₁, hS₁⟩ := chiP_eq_chiE (simForm Q₀ c G) h₁
  set f₀ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α₀ v / lam v with hf₀
  set f₁ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α₁ v / lam v with hf₁
  have hm₀ : Multipliable f₀ := by
    refine (multipliable_siegelDensity_binary_reg hQ S₀ hS₀).congr fun v => ?_
    simp only [hf₀, hα₀def, hlamdef, lamL, _root_.zpow_neg_one, div_eq_mul_inv]
  have hm₁ : Multipliable f₁ := by
    refine (multipliable_siegelDensity_binary_reg hQ₁ S₁ hS₁).congr fun v => ?_
    simp only [hf₁, hα₁def, hlamdef, lamL, _root_.zpow_neg_one, div_eq_mul_inv]
  have hff₀ : finFactor Q₀ lam = ∏' v, f₀ v := finFactor_eq Q₀ hQ hlam
  have hff₁ : finFactor (simForm Q₀ c G) lam = ∏' v, f₁ v := finFactor_eq _ hQ₁ hlam
  have hval : ((muFin Q₀ lam).map e) (KSO (simForm Q₀ c G) : Set (SOAf (simForm Q₀ c G))) =
      ENNReal.ofReal ((∏' v, nδ v) * finFactor (simForm Q₀ c G) lam) := by
    have hU : ∀ v ∈ S, MeasurableSet (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
        (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) := fun v _ =>
      ((isOpen_soStabSO v _).preimage (simConjSOV v hc hG).continuous).measurableSet
    rw [Measure.map_apply hmeas (isOpen_KSO _).measurableSet, simConjFin_preimage_KSO,
      muFin_boxSO Q₀ hQ hlam S _ hU]
    have hr : ∀ v, muLocSO v Q₀ (lam v) (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
        (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) /
          muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (nδ v * α₁ v / α₀ v) := fun v => by
      rw [← haarSO_eq_div Q₀ hQ v (hlam v), haarSO_eq_div Q₀ hQ v one_pos, hμU, hμK,
        ENNReal.ofReal_div_of_pos (hα₀ v)]
    rw [Finset.prod_congr rfl fun v _ => hr v,
      ← ENNReal.ofReal_prod_of_nonneg (fun v _ => (div_pos (mul_pos (hnδpos v) (hα₁ v)) (hα₀ v)).le),
      ← ENNReal.ofReal_mul (finFactor_nonneg _ _)]
    congr 1
    rw [hff₀, hff₁, tprod_eq_prod_mul_tprod_ite f₀ hm₀ S (fun v _ => (div_pos (hα₀ v) (hlam v)).ne'),
      tprod_eq_prod_mul_tprod_ite f₁ hm₁ S (fun v _ => (div_pos (hα₁ v) (hlam v)).ne'), tprod_eq_prod hnδ1,
      show (∏' v, if v ∈ S then (1 : ℝ) else f₀ v) = ∏' v, if v ∈ S then (1 : ℝ) else f₁ v from
        tprod_congr fun v => by by_cases hv : v ∈ S <;> simp [hv, hf₀, hf₁, hgood]]
    have key : (∏ v ∈ S, f₀ v) * ∏ v ∈ S, nδ v * α₁ v / α₀ v = (∏ v ∈ S, nδ v) * ∏ v ∈ S, f₁ v := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [hf₀, hf₁]
      field_simp [(hα₀ v).ne', (hlam v).ne']
    linear_combination (∏' v, if v ∈ S then (1 : ℝ) else f₁ v) * key
  have hfin : ((muFin Q₀ lam).map e) (KSO (simForm Q₀ c G) : Set (SOAf (simForm Q₀ c G))) ≠ ∞ := by
    rw [hval]; exact ENNReal.ofReal_ne_top
  have hP : 0 ≤ ∏' v, nδ v := tprod_nonneg fun v => (hnδpos v).le
  rw [eq_haarNorm (isCompact_KSO _) (isOpen_KSO _) _ hfin, hval]
  unfold muFin
  rw [show (ENNReal.ofReal ((∏' v, nδ v) * finFactor (simForm Q₀ c G) lam)).toNNReal =
      (∏' v, nδ v).toNNReal * (finFactor (simForm Q₀ c G) lam).toNNReal by
    rw [← Real.toNNReal_mul hP]; exact ENNReal.toNNReal_coe _,
    sim_haarNorm_mul]
  ext A hA
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rfl

/-- **Similar binary forms have the same Tamagawa covolume** (every number field, every signature):
$\mathrm{covol}(SO(V_1)(F), \mu^{\chi_E}_{\mathrm{Tam}}) = \mathrm{covol}(SO(V_0)(F), \mu^{\chi_E}_{\mathrm{Tam}})$ for
$Q_1 = c\,(Q_0\circ G)$. *Proof:* as `covolume_muTam_simForm`, with the finitely supported products of
`map_muFin_simConjFin_lamL`; the global factor $L(1,\chi_E)^{-1}$ is the same on both sides. -/
@[kb "weil1982" "§2.3, Thm 2.3.1, pp. 21–22 (independence of choices, product formula); §2.4, p. 22"]
theorem covolume_muTamBin_simForm (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) (h : IsDiscField Q₀ E) :
    covolume (GammaSOAdele (simForm Q₀ c G)) (SOAdele (simForm Q₀ c G))
        (muTamBin (simForm Q₀ c G) (nondegenerate_simForm hQ hc hG) E) =
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamBin Q₀ hQ E) := by
  have := countable_GammaSOAdele Q₀
  have := countable_GammaSOAdele (simForm Q₀ c G)
  have hL0 := (lOne_chiE h.finrank_eq_two).1
  have hL : ENNReal.ofReal (LOne (chiE F E))⁻¹ ≠ 0 := by simpa using hL0
  rw [muTamBin, muTamChi, muTamBin, muTamChi, covolume_smul _ _ hL, covolume_smul _ _ hL]
  congr 1
  have hδ := simJac_ne_zero hc hG
  have hpf := prod_infinitePlace_mul_tprod_finitePlace hδ
  symm
  refine covolume_eq_of_localFactors (GammaSOAdele Q₀) (GammaSOAdele (simForm Q₀ c G))
    (simConjInf hc hG).toMulEquiv (simConjFin hc hG).toMulEquiv
    (simConjInf hc hG).continuous.measurable (simConjInf hc hG).symm.continuous.measurable
    (simConjFin hc hG).continuous.measurable (simConjFin hc hG).symm.continuous.measurable
    (map_GammaSOAdele_simConjAdele hc hG) _ _ _ _
    (map_muArchTamSO_simConjInf hQ hc hG) (map_muFin_simConjFin_lamL hQ hc hG h) ?_
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg _ _) _), hpf,
    ENNReal.ofReal_one]

/-- **`TauTwoBinaryAdelic` is invariant under similarity** $Q_0\mapsto c\,(Q_0\circ G)$. -/
theorem tauTwoBinaryAdelic_simForm_iff (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) :
    (∀ (E : Type) [Field E] [NumberField E] [Algebra F E], IsDiscField Q₀ E →
      covolume (GammaSOAdele (simForm Q₀ c G)) (SOAdele (simForm Q₀ c G))
        (muTamBin (simForm Q₀ c G) (nondegenerate_simForm hQ hc hG) E) = 2) ↔
    (∀ (E : Type) [Field E] [NumberField E] [Algebra F E], IsDiscField Q₀ E →
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamBin Q₀ hQ E) = 2) := by
  refine forall_congr' fun E => ?_
  refine ⟨fun h1 _ _ _ hE => ?_, fun h1 _ _ _ hE => ?_⟩
  · rw [← covolume_muTamBin_simForm hQ hc hG hE]; exact h1 hE
  · rw [covolume_muTamBin_simForm hQ hc hG hE]; exact h1 hE

end QuadFormsKB.Tamagawa.Measure.Weil
