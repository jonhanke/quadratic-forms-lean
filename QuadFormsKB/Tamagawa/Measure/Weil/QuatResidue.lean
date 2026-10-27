import QuadFormsKB.Tamagawa.Measure.Weil.QuatThetaBound
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain

/-!
# Weil's comparison of residues for $A = \mathbb H[F,a,b]$ division: $c_A = \rho_F$

$a, b\in\mathcal O_F\setminus0$ with $\mathbb H[F,a,b]$ a division algebra (`hdiv`), any number field, any signature. The zeta
integral $Z(s) = \int_{(\mathbb H\otimes\mathbb A)^\times}\Phi(x)\,\|\operatorname{nrd}x\|_{\mathbb A}^s\,d\mu(x)$ of the Gaussian test
function $\Phi = G\otimes\mathbf 1_{\hat\Lambda}$ is computed twice:

* **multiplicatively** (`tendsto_mul_quatZeta`): $(s-2)Z(s)\to\rho_F\int_{\mathbb H_{\mathbb A}}\Phi\,dx$;
* **additively**: unfolding over $\mathbb H^\times = \mathbb H\setminus0$ (hdiv), the theta sum
  $\sum_{\xi\in\mathbb H}\Phi(\xi x)$ is split at $\|\operatorname{nrd}x\| = 1$ (Tate); on $\|\operatorname{nrd}x\|\le1$ Poisson
  (`quatTheta_poisson`) gives $\|\operatorname{nrd}x\|^{-2}\int\Phi\,(1 + R)$ with the dual remainder $R$ bounded uniformly
  (`exists_quatDualRem_bound`, Fujisaki's compact set); with Lemma 3.1.2 (`setLIntegral_quatFD_logNorm`),
  $(s-2)Z(s)\to c_A'\int\Phi\,dx$.

Comparing: **`quatVolConst_eq_residue`** $c_A' = \operatorname{vol}(\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1) = \rho_F$
(Weil AAG Thm 3.1.1 (iii), §3.1 pp. 40–41, for the Tamagawa measure $\prod_v\lambda_v^{-1}\omega_v$ without the factor
$\rho_F^{-1}$).

Also here: the auxiliary integrals ($\int G = 1$, $\int G\|\operatorname{nrd}\|_\infty < \infty$,
$\mu_f(\hat\Lambda) = |d_F|^{-2}$, $Z(3) < \infty$), the unfolding (`quatZeta_eq_setLIntegral`, `quatTheta_star_eq`), the
Tate split (`orbit_rpow_eq`, `setLIntegral_leOne_rpow`), the finiteness of the dual remainder on
$\{\|\operatorname{nrd}\|\le1\}$ (`setLIntegral_leOne_dualRem_ne_top`), the additive residue
(`tendsto_mul_quatZeta_additive`) and the division criterion (`hdiv_of_not_isotropicIn`, `hdiv_iff_not_everywhere`).

**Outside results used**: Mathlib's class number formula
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`), `integral_exp_mul_Iic`,
`SchwartzMap.integrable_pow_mul`, `squeeze_zero_norm'`, `tendsto_nhds_unique`; the library's `hasseMinkowski_nf`
(Hasse–Minkowski over $F$, for the division criterion) and Fujisaki's lemma (FLT `compact_quotient` is cited there).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Quaternion Pointwise Classical Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### The Gaussian integrals -/

section Gauss

theorem integral_gaussV : ∫ y, gaussV F (Fin 4) y ∂muInfVec F (Fin 4) = 1 := by
  have h := fourierV_gaussV (F := F) (ι := Fin 4) 0
  simp only [map_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, gV_zero, Complex.ofReal_one] at h
  exact h

theorem integrable_gV : Integrable (gV (F := F) (ι := Fin 4)) (muInfVec F (Fin 4)) := by
  have h := (gaussV F (Fin 4)).integrable (μ := muInfVec F (Fin 4))
  refine (h.norm).congr (Eventually.of_forall fun y => ?_)
  simp only [gaussV_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gV_pos _)]

theorem lintegral_gaussPhi : ∫⁻ z, gaussPhi z ∂muInfVec F (Fin 4) = 1 := by
  have h1 : ∫ y, gV y ∂muInfVec F (Fin 4) = 1 := by
    have := integral_gaussV (F := F)
    simp_rw [gaussV_apply] at this
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← h1,
    ofReal_integral_eq_lintegral_ofReal integrable_gV (Eventually.of_forall fun y => (gV_pos y).le)]
  rfl

theorem absDetInf_le_norm_pow (m : mixedSpace F) : absDetInf m ≤ ‖m‖ ^ Module.finrank ℚ F := by
  rw [absDetInf, det_mulLeft_mixedSpace, abs_mul, Finset.abs_prod, abs_of_nonneg
    (Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _), ← InfinitePlace.card_add_two_mul_card_eq_rank, pow_add]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _) (by positivity)
  · calc ∏ w, |m.1 w| ≤ ∏ _w : {w : InfinitePlace F // w.IsReal}, ‖m‖ :=
          Finset.prod_le_prod₀ (fun w _ => abs_nonneg _) (fun w _ => norm_fst_apply_le m w)
      _ = ‖m‖ ^ InfinitePlace.nrRealPlaces F := by rw [Finset.prod_const, Finset.card_univ]
  · calc ∏ w, Complex.normSq (m.2 w) ≤ ∏ _w : {w : InfinitePlace F // w.IsComplex}, ‖m‖ ^ 2 :=
          Finset.prod_le_prod₀ (fun w _ => Complex.normSq_nonneg _) (fun w _ => by
            rw [Complex.normSq_eq_norm_sq]
            exact pow_le_pow_left₀ (norm_nonneg _) (norm_snd_apply_le m w) 2)
      _ = ‖m‖ ^ (2 * InfinitePlace.nrComplexPlaces F) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm]

theorem norm_nrdForm_le (α β : mixedSpace F) (z : Fin 4 → mixedSpace F) :
    ‖nrdForm α β z‖ ≤ (1 + ‖α‖ + ‖β‖ + ‖α‖ * ‖β‖) * ‖z‖ ^ 2 := by
  have hz : ∀ i, ‖z i‖ ≤ ‖z‖ := fun i => norm_le_pi_norm z i
  have hsq : ∀ i, ‖z i ^ 2‖ ≤ ‖z‖ ^ 2 := fun i =>
    (norm_pow_le _ 2).trans (pow_le_pow_left₀ (norm_nonneg _) (hz i) 2)
  unfold nrdForm
  calc ‖z 0 ^ 2 - α * z 1 ^ 2 - β * z 2 ^ 2 + α * β * z 3 ^ 2‖
      ≤ ‖z 0 ^ 2‖ + ‖α‖ * ‖z 1 ^ 2‖ + ‖β‖ * ‖z 2 ^ 2‖ + ‖α‖ * ‖β‖ * ‖z 3 ^ 2‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))) (norm_mul_le _ _)))
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))))
    _ ≤ ‖z‖ ^ 2 + ‖α‖ * ‖z‖ ^ 2 + ‖β‖ * ‖z‖ ^ 2 + ‖α‖ * ‖β‖ * ‖z‖ ^ 2 := by
        gcongr <;> exact hsq _
    _ = _ := by ring

variable (a b : F)

theorem nrdNormW_le (z : Fin 4 → mixedSpace F) :
    nrdNormW a b z ≤ (1 + ‖mixedEmbedding F a‖ + ‖mixedEmbedding F b‖ + ‖mixedEmbedding F a‖ *
      ‖mixedEmbedding F b‖) ^ Module.finrank ℚ F * ‖z‖ ^ (2 * Module.finrank ℚ F) := by
  refine (absDetInf_le_norm_pow _).trans ?_
  rw [pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_nrdForm_le _ _ z) _

/-- **$\int G\,(1 + \|\operatorname{nrd}\|_\infty) < \infty$**: the Gaussian is an admissible archimedean test function. -/
theorem lintegral_gaussPhi_nrd_ne_top :
    ∫⁻ z, gaussPhi z * ENNReal.ofReal (1 + nrdNormW a b z) ∂muInfVec F (Fin 4) ≠ ⊤ := by
  set C := (1 + ‖mixedEmbedding F a‖ + ‖mixedEmbedding F b‖ + ‖mixedEmbedding F a‖ * ‖mixedEmbedding F b‖) ^
    Module.finrank ℚ F
  set k := 2 * Module.finrank ℚ F
  have hint : Integrable (fun z => gV z + C * (‖z‖ ^ k * gV z)) (muInfVec F (Fin 4)) := by
    refine integrable_gV.add (Integrable.const_mul ?_ C)
    have h := (gaussV F (Fin 4)).integrable_pow_mul (muInfVec F (Fin 4)) k
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [gaussV_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gV_pos _)]
  refine ne_of_lt (lt_of_le_of_lt ?_ hint.lintegral_lt_top)
  · refine lintegral_mono fun z => ?_
    rw [gaussPhi, ← ENNReal.ofReal_mul (gV_pos z).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hN := nrdNormW_le a b z
    nlinarith [gV_pos z, absDetInf_nonneg (nrdForm (mixedEmbedding F a) (mixedEmbedding F b) z)]

end Gauss

/-! ### Constants -/

section Constants

theorem muFinVec_OHatVec_eq :
    muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4)) = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2)) := by
  rw [muFinVec_OHatVec, muFin_OHat, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (ohatVol_pos (F := F)).le]
  congr 1
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [ohatVol, inv_pow, show (-(4 : ℝ) / 2) = -2 by norm_num, Real.rpow_neg hd.le,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hd.le]
  norm_cast

theorem toReal_muFinVec_OHatVec :
    (muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4))).toReal = |(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2) := by
  rw [muFinVec_OHatVec_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _)]

/-- **$Z(3) < \infty$** for the Gaussian test function. -/
theorem quatZeta_three_ne_top {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    quatZeta (a : F) (b : F) gaussPhi 3 ≠ ⊤ := by
  have hΦ : Measurable (gaussPhi (F := F)) := ENNReal.measurable_ofReal.comp
    (by rw [show (gV (F := F) (ι := Fin 4)) = fun y => Real.exp (-π * qV y) from funext gV_eq_exp]
        unfold qV; fun_prop)
  rw [quatZeta_eq_mul _ _ hΦ (by norm_num)]
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top (lintegral_gaussPhi_nrd_ne_top (a : F) (b : F))
    (quatInfZeta_le _ _ hΦ (by norm_num) le_rfl)) (quatFinZeta_ne_top ha0 hb0 (by norm_num))

theorem measurable_gaussPhi : Measurable (gaussPhi (F := F)) := ENNReal.measurable_ofReal.comp
  (by rw [show (gV (F := F) (ι := Fin 4)) = fun y => Real.exp (-π * qV y) from funext gV_eq_exp]
      unfold qV; fun_prop)

end Constants

/-! ### Unfolding over $\mathbb H^\times = \mathbb H\setminus0$ -/

section Unfold

variable {a b : F}

theorem quatTestFn_zero : quatTestFn a b gaussPhi 0 = 1 := by
  rw [quatTestFn]
  simp only [map_zero, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero]
  rw [indicator_of_mem (by simp [zero_mem_OHat]), gaussPhi,
    show (fun _ : Fin 4 => (0 : mixedSpace F)) = 0 from rfl, gV_zero, ENNReal.ofReal_one, mul_one]

/-- The orbit sum over $\mathbb H^\times$. -/
def quatOrbitSum (x : (QuatAdele a b)ˣ) : ℝ≥0∞ :=
  ∑' γ : quatUnitsSub a b, quatTestFn a b gaussPhi (((γ : (QuatAdele a b)ˣ) : QuatAdele a b) * (x : QuatAdele a b))

/-- $\mathbb H^\times\cong\mathbb H\setminus0$ for a division algebra. -/
def quatUnitsSubEquiv (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) :
    quatUnitsSub a b ≃ {ξ : ℍ[F,a,b] // ξ ≠ 0} :=
  Equiv.ofBijective
    (fun γ => ⟨((γ.2.choose : (ℍ[F,a,b])ˣ) : ℍ[F,a,b]), Units.ne_zero _⟩)
    ⟨fun γ₁ γ₂ h => by
      have h1 := γ₁.2.choose_spec
      have h2 := γ₂.2.choose_spec
      have : γ₁.2.choose = γ₂.2.choose := Units.ext (congrArg Subtype.val h)
      exact Subtype.ext (h1.symm.trans (this ▸ h2)),
     fun ⟨ξ, hξ⟩ => ⟨⟨Units.map (quatDiagRing a b).toMonoidHom (hdiv ξ hξ).unit, _, rfl⟩, by
      have hmem : (⟨Units.map (quatDiagRing a b).toMonoidHom (hdiv ξ hξ).unit, _, rfl⟩ : quatUnitsSub a b).2.choose =
          (hdiv ξ hξ).unit := by
        have h := (⟨Units.map (quatDiagRing a b).toMonoidHom (hdiv ξ hξ).unit, _, rfl⟩ :
          quatUnitsSub a b).2.choose_spec
        refine Units.ext ?_
        have hinj : Function.Injective (quatDiagRing a b) := by
          intro x y hxy
          have := congrArg (quatCoord a b) hxy
          rw [quatCoord_quatDiagRing, quatCoord_quatDiagRing] at this
          exact diagQuat_injective a b this
        exact hinj (congrArg Units.val h)
      exact Subtype.ext (by simp only [hmem, IsUnit.unit_spec])⟩⟩

theorem quatUnitsSubEquiv_val (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) (γ : quatUnitsSub a b) :
    quatDiagRing a b (quatUnitsSubEquiv hdiv γ : ℍ[F,a,b]) = ((γ : (QuatAdele a b)ˣ) : QuatAdele a b) := by
  change quatDiagRing a b ((γ.2.choose : (ℍ[F,a,b])ˣ) : ℍ[F,a,b]) = _
  exact congrArg Units.val γ.2.choose_spec

/-- **$S(\bar x) = 1 + \sum_{\gamma\in\mathbb H^\times}\Phi(\gamma x)$** (hdiv: $\mathbb H\setminus0 = \mathbb H^\times$). -/
theorem quatTheta_star_eq (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) (x : (QuatAdele a b)ˣ) :
    quatTheta a b (quatStarUnit x) = 1 + quatOrbitSum x := by
  rw [← tsum_right_eq_quatTheta_star, ENNReal.tsum_eq_add_tsum_ite (0 : ℍ[F,a,b])]
  congr 1
  · rw [map_zero, zero_mul, quatTestFn_zero]
  · rw [quatOrbitSum, ← (quatUnitsSubEquiv hdiv).symm.tsum_eq]
    have h1 : ∀ ξ : ℍ[F,a,b], (if ξ = 0 then 0 else quatTestFn a b gaussPhi (quatDiagRing a b ξ * (x : QuatAdele a b))) =
        ({ξ : ℍ[F,a,b] | ξ ≠ 0} : Set ℍ[F,a,b]).indicator
          (fun ξ => quatTestFn a b gaussPhi (quatDiagRing a b ξ * (x : QuatAdele a b))) ξ := by
      intro ξ
      by_cases h : ξ = 0
      · rw [if_pos h, indicator_of_notMem (by simpa using h)]
      · rw [if_neg h, indicator_of_mem (by simpa using h)]
    simp_rw [h1]
    rw [← tsum_subtype]
    refine tsum_congr fun ξ => ?_
    congr 1
    rw [← quatUnitsSubEquiv_val hdiv, Equiv.apply_symm_apply]

end Unfold

/-! ### The additive side: unfolding, invariance, Poisson on the fundamental domain -/

section Additive

variable {a b : F}
variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

theorem ideleNorm_nrdUnit_mul {γ : (QuatAdele a b)ˣ} (hγ : γ ∈ quatUnitsSub a b) (x : (QuatAdele a b)ˣ) :
    ideleNorm F (nrdUnit (γ * x)) = ideleNorm F (nrdUnit x) := by
  have h := quatSplit_snd_mul hγ x
  rw [quatSplit_apply_snd, quatSplit_apply_snd] at h
  have h' := congrArg Multiplicative.toAdd h
  simp only [toAdd_ofAdd] at h'
  exact Real.log_injOn_pos (ideleNorm_pos _) (ideleNorm_pos _) h'

theorem measurable_quatTestFn_gauss : Measurable fun x : (QuatAdele a b)ˣ => quatTestFn a b gaussPhi (x : QuatAdele a b) :=
  measurable_quatTestFn a b measurable_gaussPhi

theorem measurable_quatOrbitSum : Measurable (quatOrbitSum (a := a) (b := b)) := by
  refine Measurable.ennreal_tsum fun γ => ?_
  have h : (fun x : (QuatAdele a b)ˣ => quatTestFn a b gaussPhi
      (((γ : (QuatAdele a b)ˣ) : QuatAdele a b) * (x : QuatAdele a b))) =
      (fun x : (QuatAdele a b)ˣ => quatTestFn a b gaussPhi (x : QuatAdele a b)) ∘
        (fun x => (γ : (QuatAdele a b)ˣ) * x) := by
    funext x; simp only [Function.comp_apply, Units.val_mul]
  rw [h]
  exact (measurable_quatTestFn_gauss (a := a) (b := b)).comp (continuous_const.mul continuous_id).measurable

theorem quatOrbitSum_mul {γ : (QuatAdele a b)ˣ} (hγ : γ ∈ quatUnitsSub a b) (x : (QuatAdele a b)ˣ) :
    quatOrbitSum (γ * x) = quatOrbitSum x := by
  rw [quatOrbitSum, quatOrbitSum]
  conv_rhs => rw [← (Equiv.mulRight (⟨γ, hγ⟩ : quatUnitsSub a b)).tsum_eq]
  refine tsum_congr fun γ' => ?_
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Units.val_mul, mul_assoc]

include ha hb ha0 hb0 in
/-- **Unfolding**: $Z(s) = \int_D\sum_{\gamma\in\mathbb H^\times}\Phi(\gamma x)\,\|\operatorname{nrd}x\|^s\,d\mu$. -/
theorem quatZeta_eq_setLIntegral {D : Set (QuatAdele a b)ˣ}
    (hD : IsFundamentalDomain (quatUnitsSub a b) D (tamQuat a b)) (s : ℝ) :
    quatZeta a b gaussPhi s = ∫⁻ x in D, quatOrbitSum x * ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ s ∂tamQuat a b := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  have hf : Measurable fun x : (QuatAdele a b)ˣ =>
      quatTestFn a b gaussPhi (x : QuatAdele a b) * ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ s :=
    measurable_quatTestFn_gauss.mul ((ENNReal.measurable_ofReal.comp (measurable_ideleNorm_nrdUnit a b)).pow_const s)
  rw [quatZeta, ← lintegral_quotient_eq hD hf]
  refine lintegral_congr fun x => ?_
  rw [quatOrbitSum, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun γ => ?_
  rw [Subgroup.smul_def, smul_eq_mul, ideleNorm_nrdUnit_mul γ.2, Units.val_mul]

theorem lintegral_exp_mul_Iic_zero {a : ℝ} (ha : 0 < a) :
    ∫⁻ u, (Iic (0 : ℝ)).indicator (fun u => ENNReal.ofReal (Real.exp (a * u))) u = ENNReal.ofReal (1 / a) := by
  rw [lintegral_indicator measurableSet_Iic, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha 0)
    (Eventually.of_forall fun u => (Real.exp_pos _).le), integral_exp_mul_Iic ha 0, mul_zero, Real.exp_zero]

/-- The set $\{\|\operatorname{nrd}x\|\le1\}$ via its indicator. -/
def leOneInd (x : (QuatAdele a b)ˣ) : ℝ≥0∞ :=
  (Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) (Real.log (ideleNorm F (nrdUnit x)))

theorem measurable_leOneInd : Measurable (leOneInd (a := a) (b := b)) :=
  (measurable_const.indicator measurableSet_Iic).comp (Real.measurable_log.comp (measurable_ideleNorm_nrdUnit a b))

include ha hb ha0 hb0 in
/-- **$\int_{D,\ \|\operatorname{nrd}x\|\le1}\|\operatorname{nrd}x\|^\alpha\,d\mu = c_A'/\alpha$** for $\alpha > 0$ (Lemma 3.1.2). -/
theorem setLIntegral_leOne_rpow {D : Set (QuatAdele a b)ˣ}
    (hD : IsFundamentalDomain (quatUnitsSub a b) D (tamQuat a b)) {α : ℝ} (hα : 0 < α) :
    ∫⁻ x in D, leOneInd x * ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ α ∂tamQuat a b =
      quatVolConst ha hb ha0 hb0 * ENNReal.ofReal (1 / α) := by
  have h := setLIntegral_quatFD_logNorm ha hb ha0 hb0 hD
    (h := (Iic (0 : ℝ)).indicator (fun u => ENNReal.ofReal (Real.exp (α * u))))
    ((ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (measurable_const_mul α))).indicator
      measurableSet_Iic)
  rw [lintegral_exp_mul_Iic_zero hα] at h
  rw [← h]
  refine lintegral_congr fun x => ?_
  simp only [leOneInd]
  by_cases hx : Real.log (ideleNorm F (nrdUnit x)) ∈ Iic (0 : ℝ)
  · rw [indicator_of_mem hx, indicator_of_mem hx, one_mul, ENNReal.ofReal_rpow_of_pos (ideleNorm_pos _),
      Real.rpow_def_of_pos (ideleNorm_pos _), mul_comm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]

include ha hb in
/-- **Poisson on the orbit sum**: $\|\operatorname{nrd}x\|^2(1 + \sum_\gamma\Phi(\gamma x)) = \mu_f(\hat\Lambda)(1 + R(\bar x))$. -/
theorem poisson_orbit (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) (x : (QuatAdele a b)ˣ) :
    ENNReal.ofReal (ideleNorm F (nrdUnit x) ^ 2) * (1 + quatOrbitSum x) =
      muFinVec F (Fin 4) OHatVec * (1 + quatDualRem (quatStarUnit x)) := by
  rw [← quatTheta_star_eq hdiv, ← quatTheta_poisson ha hb (quatStarUnit x), nrdUnit_quatStarUnit]

include ha hb in
theorem quatDualRem_star_mul (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) {γ : (QuatAdele a b)ˣ}
    (hγ : γ ∈ quatUnitsSub a b) (x : (QuatAdele a b)ˣ) :
    quatDualRem (quatStarUnit (γ * x)) = quatDualRem (quatStarUnit x) := by
  have h1 := poisson_orbit ha hb hdiv (γ * x)
  rw [ideleNorm_nrdUnit_mul hγ, quatOrbitSum_mul hγ, poisson_orbit ha hb hdiv x] at h1
  have hA0 : muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4)) ≠ 0 := muFinVec_OHatVec_ne_zero
  have hAT : muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4)) ≠ ⊤ := muFinVec_OHatVec_ne_top
  have h2 := (ENNReal.mul_right_inj hA0 hAT).mp h1
  exact ((ENNReal.add_right_inj ENNReal.one_ne_top).mp h2).symm

include ha hb in
theorem quatDualRem_star_eq (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) (x : (QuatAdele a b)ˣ) :
    quatDualRem (quatStarUnit x) = ENNReal.ofReal (ideleNorm F (nrdUnit x) ^ 2) * (1 + quatOrbitSum x) /
      muFinVec F (Fin 4) OHatVec - 1 := by
  have hA0 : muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4)) ≠ 0 := muFinVec_OHatVec_ne_zero
  have hAT : muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4)) ≠ ⊤ := muFinVec_OHatVec_ne_top
  rw [poisson_orbit ha hb hdiv x, mul_comm, ENNReal.mul_div_cancel_right hA0 hAT, ENNReal.add_sub_cancel_left
    ENNReal.one_ne_top]

include ha hb in
theorem measurable_quatDualRem_star (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) :
    Measurable fun x : (QuatAdele a b)ˣ => quatDualRem (quatStarUnit x) := by
  simp_rw [quatDualRem_star_eq ha hb hdiv]
  exact (((ENNReal.measurable_ofReal.comp ((measurable_ideleNorm_nrdUnit a b).pow_const 2)).mul
    (measurable_const.add measurable_quatOrbitSum)).div_const _).sub_const _

include ha hb in
/-- **The pointwise Tate identity** for $s > 2$:
$(1 + \sum_\gamma\Phi(\gamma x))\|\operatorname{nrd}x\|^s = \|\operatorname{nrd}x\|^{s-2}\mu_f(\hat\Lambda)(1 + R(\bar x))$. -/
theorem orbit_rpow_eq (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) (x : (QuatAdele a b)ˣ) {s : ℝ} (hs : 2 < s) :
    (1 + quatOrbitSum x) * ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ s =
      ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ (s - 2) *
        (muFinVec F (Fin 4) OHatVec * (1 + quatDualRem (quatStarUnit x))) := by
  have hpos := ideleNorm_pos (nrdUnit x)
  rw [← poisson_orbit ha hb hdiv x, ← mul_assoc, mul_comm _ (ENNReal.ofReal _), ENNReal.ofReal_rpow_of_pos hpos,
    ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul (pow_nonneg hpos.le _), mul_comm (1 + quatOrbitSum x)]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
  push_cast; ring_nf

theorem one_div_sectionScale_sq (t : Multiplicative ℝ) :
    1 / sectionScale F t ^ 2 = Real.exp (-(Multiplicative.toAdd t) / (Module.finrank ℚ F : ℝ)) := by
  have hn : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  rw [sectionScale, ← Real.rpow_natCast, ← Real.rpow_mul (Real.exp_pos _).le, ← Real.exp_mul, one_div,
    ← Real.exp_neg]
  congr 1
  push_cast
  field_simp

/-- The bound on the theta tail as a function of $u = \log t\le0$ is integrable on $(-\infty,0]$. -/
theorem lintegral_theta_tail_ne_top {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∫⁻ u in Iic (0 : ℝ), ENNReal.ofReal (δ ^ (Real.exp (-u / (Module.finrank ℚ F : ℝ)) - 1)) ≠ ⊤ := by
  have hn : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  set δ' := max δ (1 / 2)
  have hδ'0 : 0 < δ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hδ'1 : δ' < 1 := max_lt hδ1 (by norm_num)
  set κ := -Real.log δ' / (Module.finrank ℚ F : ℝ)
  have hκ : 0 < κ := div_pos (neg_pos.mpr (Real.log_neg hδ'0 hδ'1)) hn
  refine ne_top_of_le_ne_top (b := ∫⁻ u in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (κ * u))) ?_ ?_
  · rw [← lintegral_indicator measurableSet_Iic, lintegral_exp_mul_Iic_zero hκ]; exact ENNReal.ofReal_ne_top
  · refine setLIntegral_mono (by fun_prop) fun u hu => ENNReal.ofReal_le_ofReal ?_
    have hu0 : u ≤ 0 := hu
    have hX : -u / (Module.finrank ℚ F : ℝ) ≤ Real.exp (-u / (Module.finrank ℚ F : ℝ)) - 1 := by
      linarith [Real.add_one_le_exp (-u / (Module.finrank ℚ F : ℝ))]
    have hX0 : 0 ≤ -u / (Module.finrank ℚ F : ℝ) := div_nonneg (by linarith) hn.le
    calc δ ^ (Real.exp (-u / (Module.finrank ℚ F : ℝ)) - 1)
        ≤ δ' ^ (Real.exp (-u / (Module.finrank ℚ F : ℝ)) - 1) :=
          Real.rpow_le_rpow hδ0 (le_max_left _ _) (hX0.trans hX)
      _ ≤ δ' ^ (-u / (Module.finrank ℚ F : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1.le hX
      _ = Real.exp (κ * u) := by
          rw [Real.rpow_def_of_pos hδ'0]; congr 1; simp only [κ]; ring

include ha hb ha0 hb0 in
/-- **The dual remainder has finite integral over $\{\|\operatorname{nrd}x\|\le1\}$** (Fujisaki's compact set and the uniform
theta bound). -/
theorem setLIntegral_leOne_dualRem_ne_top (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) {D : Set (QuatAdele a b)ˣ}
    (hD : IsFundamentalDomain (quatUnitsSub a b) D (tamQuat a b)) :
    ∫⁻ x in D, leOneInd x * quatDualRem (quatStarUnit x) ∂tamQuat a b ≠ ⊤ := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  obtain ⟨C, hC, hCcov⟩ := exists_isCompact_quatOne_mul_mem a b hdiv
  obtain ⟨δ, hδ0, hδ1, Θ, hΘ, hbound⟩ := exists_quatDualRem_bound ha hb hC
  set T : Set (Multiplicative ℝ) := Multiplicative.toAdd ⁻¹' Iic 0
  have hTm : MeasurableSet T := measurableSet_Iic.preimage continuous_toAdd.measurable
  set C' : Set (QuatAdele a b)ˣ := quatSplit a b ⁻¹' (C ×ˢ T)
  have hC'm : MeasurableSet C' := (hC.isClosed.measurableSet.prod hTm).preimage measurable_quatSplit
  set Rf : (QuatAdele a b)ˣ → ℝ≥0∞ := fun x => quatDualRem (quatStarUnit x)
  have hRm : Measurable Rf := measurable_quatDualRem_star ha hb hdiv
  set g := C'.indicator Rf
  have hg : Measurable g := hRm.indicator hC'm
  -- step 1: the orbit of every x with ‖nrd x‖ ≤ 1 meets C'
  have h1 : ∫⁻ x in D, leOneInd x * Rf x ∂tamQuat a b ≤ ∫⁻ x, g x ∂tamQuat a b := by
    rw [← lintegral_quotient_eq hD hg]
    refine lintegral_mono fun x => ?_
    simp only [leOneInd]
    by_cases hx : Real.log (ideleNorm F (nrdUnit x)) ∈ Iic (0 : ℝ)
    · rw [indicator_of_mem hx, one_mul]
      obtain ⟨γ₀, hγ₀, hγ₀C⟩ := hCcov (quatSplit a b x).1
      have hγm : ((γ₀ : (QuatAdele a b)ˣ))⁻¹ ∈ quatUnitsSub a b :=
        (quatUnitsSub a b).inv_mem (Subgroup.mem_subgroupOf.mp hγ₀)
      have hmem : ((γ₀ : (QuatAdele a b)ˣ))⁻¹ * x ∈ C' := by
        rw [Set.mem_preimage]
        refine ⟨?_, ?_⟩
        · have : (quatSplit a b (((γ₀ : (QuatAdele a b)ˣ))⁻¹ * x)).1 = γ₀⁻¹ * (quatSplit a b x).1 := by
            apply Subtype.ext
            rw [Subgroup.coe_mul, Subgroup.coe_inv]
            exact quatSplit_fst_mul hγm x
          rw [this]; exact hγ₀C
        · rw [Set.mem_preimage, quatSplit_snd_mul hγm, quatSplit_apply_snd, toAdd_ofAdd]; exact hx
      calc Rf x = Rf (((γ₀ : (QuatAdele a b)ˣ))⁻¹ * x) := (quatDualRem_star_mul ha hb hdiv hγm x).symm
        _ = g (((γ₀ : (QuatAdele a b)ˣ))⁻¹ * x) := (indicator_of_mem hmem Rf).symm
        _ = g ((⟨((γ₀ : (QuatAdele a b)ˣ))⁻¹, hγm⟩ : quatUnitsSub a b) • x) := rfl
        _ ≤ ∑' γ' : quatUnitsSub a b, g (γ' • x) := ENNReal.le_tsum (f := fun γ' => g (γ' • x)) _
    · rw [indicator_of_notMem hx, zero_mul]; exact bot_le
  -- step 2: integrate over C' in the split coordinates
  set B : Multiplicative ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (δ ^ (1 / sectionScale F t ^ 2 - 1)) * Θ
  have hBm : Measurable B := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul_const _
    have ht : Measurable fun t : Multiplicative ℝ => Multiplicative.toAdd t := continuous_toAdd.measurable
    have hs : Measurable fun t : Multiplicative ℝ => sectionScale F t := by
      unfold sectionScale
      exact ((Real.continuous_exp.measurable.comp (ht.div_const 2)).pow_const _)
    exact measurable_const.pow ((measurable_const.div (hs.pow_const 2)).sub_const 1)
  have hgle : ∀ x, g x ≤ (C ×ˢ T).indicator (fun p => B p.2) (quatSplit a b x) := by
    intro x
    show C'.indicator Rf x ≤ _
    by_cases hx : x ∈ C'
    · rw [indicator_of_mem hx, indicator_of_mem (show quatSplit a b x ∈ C ×ˢ T from hx)]
      have hx' : x = ((quatSplit a b x).1 : (QuatAdele a b)ˣ) * quatSectionHom a b (quatSplit a b x).2 :=
        ((quatSplit a b).symm_apply_apply x).symm
      simp only [Rf]
      rw [hx', quatStarUnit_mul_section]
      rw [← hx']
      exact hbound _ hx.1 _ hx.2
    · rw [indicator_of_notMem hx]; exact bot_le
  have h2 : ∫⁻ x, g x ∂tamQuat a b ≤ muQuatOneTam ha hb ha0 hb0 C * ∫⁻ t in T, B t ∂dtt := by
    refine (lintegral_mono hgle).trans (le_of_eq ?_)
    have hm : Measurable ((C ×ˢ T).indicator fun p : quatOne a b × Multiplicative ℝ => B p.2) :=
      (hBm.comp measurable_snd).indicator (hC.isClosed.measurableSet.prod hTm)
    rw [← lintegral_map hm measurable_quatSplit, map_quatSplit_tamQuat ha hb ha0 hb0]
    have : ((C ×ˢ T).indicator fun p : quatOne a b × Multiplicative ℝ => B p.2) =
        fun p => C.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * T.indicator B p.2 := by
      funext p
      by_cases h1 : p.1 ∈ C <;> by_cases h2 : p.2 ∈ T <;>
        simp [indicator, h1, h2, Set.mem_prod]
    rw [this, lintegral_prod_mul ((measurable_const.indicator hC.isClosed.measurableSet).aemeasurable)
      ((hBm.indicator hTm).aemeasurable), lintegral_indicator_const hC.isClosed.measurableSet, one_mul,
      lintegral_indicator hTm]
  have hT : ∫⁻ t in T, B t ∂dtt ≠ ⊤ := by
    rw [dtt, setLIntegral_map hTm hBm continuous_ofAdd.measurable]
    simp only [B]
    rw [lintegral_mul_const' _ _ hΘ]
    refine ENNReal.mul_ne_top ?_ hΘ
    have hpre : (Multiplicative.ofAdd ⁻¹' T) = Iic (0 : ℝ) := by ext u; simp [T]
    rw [hpre]
    simp_rw [one_div_sectionScale_sq, toAdd_ofAdd]
    exact lintegral_theta_tail_ne_top hδ0 hδ1
  have : (muQuatOneTam ha hb ha0 hb0).IsHaarMeasure := by unfold muQuatOneTam; infer_instance
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (hC.measure_lt_top).ne hT) (h1.trans h2)

/-- The set $\{\|\operatorname{nrd}x\| > 1\}$ via its indicator. -/
def gtOneInd (x : (QuatAdele a b)ˣ) : ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) (Real.log (ideleNorm F (nrdUnit x)))

theorem measurable_gtOneInd : Measurable (gtOneInd (a := a) (b := b)) :=
  (measurable_const.indicator measurableSet_Ioi).comp (Real.measurable_log.comp (measurable_ideleNorm_nrdUnit a b))

theorem leOneInd_add_gtOneInd (x : (QuatAdele a b)ˣ) : leOneInd x + gtOneInd x = 1 := by
  simp only [leOneInd, gtOneInd]
  by_cases h : Real.log (ideleNorm F (nrdUnit x)) ≤ 0
  · rw [indicator_of_mem (show _ ∈ Iic (0 : ℝ) from h), indicator_of_notMem (show _ ∉ Ioi (0 : ℝ) from not_lt.mpr h),
      add_zero]
  · rw [indicator_of_notMem (show _ ∉ Iic (0 : ℝ) from h), indicator_of_mem (show _ ∈ Ioi (0 : ℝ) from not_le.mp h),
      zero_add]

include ha hb ha0 hb0 in
/-- **The additive residue**: $(s-2)Z(s)\to\mu_f(\hat\Lambda)\,c_A'$ as $s\to2^+$, i.e.
$\lim(s-2)Z(s) = c_A'\int_{\mathbb H_{\mathbb A}}\Phi\,dx$ ($\int\Phi = \mu_f(\hat\Lambda)\int G = \mu_f(\hat\Lambda)$). -/
theorem tendsto_mul_quatZeta_additive (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ)
    (hZ3 : quatZeta a b gaussPhi 3 ≠ ⊤) :
    Tendsto (fun s => (s - 2) * (quatZeta a b gaussPhi s).toReal) (𝓝[>] 2)
      (𝓝 ((muFinVec F (Fin 4) OHatVec).toReal * (quatVolConst ha hb ha0 hb0).toReal)) := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  obtain ⟨D₁, hD₁m, hD₁⟩ := exists_exact_quatOneFD a b
  set D := quatSplit a b ⁻¹' (D₁ ×ˢ univ)
  have hD : IsFundamentalDomain (quatUnitsSub a b) D (tamQuat a b) :=
    isFundamentalDomain_quatSplit_preimage hD₁m hD₁ _
  set μ := (tamQuat a b).restrict D
  set cA := quatVolConst ha hb ha0 hb0
  have hVT : cA ≠ ⊤ := (quatVolConst_lt_top ha hb ha0 hb0 hdiv).ne
  set A := muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4))
  have hA0 : A ≠ 0 := muFinVec_OHatVec_ne_zero
  have hAT : A ≠ ⊤ := muFinVec_OHatVec_ne_top
  set n : (QuatAdele a b)ˣ → ℝ≥0∞ := fun x => ENNReal.ofReal (ideleNorm F (nrdUnit x))
  have hn : Measurable n := ENNReal.measurable_ofReal.comp (measurable_ideleNorm_nrdUnit a b)
  set Rf : (QuatAdele a b)ˣ → ℝ≥0∞ := fun x => quatDualRem (quatStarUnit x)
  have hRm : Measurable Rf := measurable_quatDualRem_star ha hb hdiv
  set orb := quatOrbitSum (a := a) (b := b)
  have horb : Measurable orb := measurable_quatOrbitSum
  set E₀ := ∫⁻ x, leOneInd x * Rf x ∂μ
  have hE₀ : E₀ ≠ ⊤ := setLIntegral_leOne_dualRem_ne_top ha hb ha0 hb0 hdiv hD
  set Zle : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, leOneInd x * (orb x * n x ^ s) ∂μ
  set Zgt : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, gtOneInd x * (orb x * n x ^ s) ∂μ
  set E : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, leOneInd x * (n x ^ (s - 2) * Rf x) ∂μ
  -- the decomposition
  have hsplit : ∀ s, quatZeta a b gaussPhi s = Zle s + Zgt s := by
    intro s
    have hm : Measurable fun x => leOneInd x * (orb x * n x ^ s) :=
      measurable_leOneInd.mul (horb.mul (hn.pow_const s))
    calc quatZeta a b gaussPhi s = ∫⁻ x, orb x * n x ^ s ∂μ := quatZeta_eq_setLIntegral ha hb ha0 hb0 hD s
      _ = ∫⁻ x, (leOneInd x * (orb x * n x ^ s) + gtOneInd x * (orb x * n x ^ s)) ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [← add_mul, leOneInd_add_gtOneInd, one_mul]
      _ = Zle s + Zgt s := lintegral_add_left hm _
  -- the Tate identity on ‖nrd‖ ≤ 1
  have htate : ∀ s, 2 < s → Zle s + cA * ENNReal.ofReal (1 / s) = A * (cA * ENNReal.ofReal (1 / (s - 2)) + E s) := by
    intro s hs
    have h1 : ∫⁻ x, leOneInd x * n x ^ s ∂μ = cA * ENNReal.ofReal (1 / s) :=
      setLIntegral_leOne_rpow ha hb ha0 hb0 hD (by linarith)
    have h2 : ∫⁻ x, leOneInd x * n x ^ (s - 2) ∂μ = cA * ENNReal.ofReal (1 / (s - 2)) :=
      setLIntegral_leOne_rpow ha hb ha0 hb0 hD (by linarith)
    have hm1 : Measurable fun x => leOneInd x * (orb x * n x ^ s) :=
      measurable_leOneInd.mul (horb.mul (hn.pow_const s))
    have hm2 : Measurable fun x => leOneInd x * n x ^ (s - 2) := measurable_leOneInd.mul (hn.pow_const _)
    have hm3 : Measurable fun x => leOneInd x * n x ^ (s - 2) + leOneInd x * (n x ^ (s - 2) * Rf x) :=
      hm2.add (measurable_leOneInd.mul ((hn.pow_const _).mul hRm))
    rw [← h1, ← h2]
    calc Zle s + ∫⁻ x, leOneInd x * n x ^ s ∂μ
        = ∫⁻ x, (leOneInd x * (orb x * n x ^ s) + leOneInd x * n x ^ s) ∂μ := (lintegral_add_left hm1 _).symm
      _ = ∫⁻ x, A * (leOneInd x * n x ^ (s - 2) + leOneInd x * (n x ^ (s - 2) * Rf x)) ∂μ := by
          refine lintegral_congr fun x => ?_
          have h := orbit_rpow_eq ha hb hdiv x hs
          calc leOneInd x * (orb x * n x ^ s) + leOneInd x * n x ^ s
              = leOneInd x * ((1 + orb x) * n x ^ s) := by ring
            _ = leOneInd x * (n x ^ (s - 2) * (A * (1 + Rf x))) := by rw [h]
            _ = A * (leOneInd x * n x ^ (s - 2) + leOneInd x * (n x ^ (s - 2) * Rf x)) := by ring
      _ = A * (∫⁻ x, leOneInd x * n x ^ (s - 2) ∂μ + E s) := by
          rw [lintegral_const_mul _ hm3, lintegral_add_left hm2]
  -- bounds
  have hEle : ∀ s, 2 ≤ s → E s ≤ E₀ := by
    intro s hs
    refine lintegral_mono fun x => ?_
    simp only [leOneInd]
    by_cases hx : Real.log (ideleNorm F (nrdUnit x)) ∈ Iic (0 : ℝ)
    · rw [indicator_of_mem hx, one_mul, one_mul]
      have hn1 : n x ≤ 1 := by
        simp only [n]
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((Real.log_nonpos_iff (ideleNorm_pos _).le).mp hx)
      have hle1 : n x ^ (s - 2) ≤ 1 := ENNReal.rpow_le_one hn1 (by linarith)
      calc n x ^ (s - 2) * Rf x ≤ 1 * Rf x := mul_le_mul' hle1 le_rfl
        _ = Rf x := one_mul _
    · rw [indicator_of_notMem hx, zero_mul, zero_mul]
  have hZgt3 : ∀ s, s ≤ 3 → Zgt s ≤ quatZeta a b gaussPhi 3 := by
    intro s hs
    rw [hsplit 3]
    refine le_add_left (lintegral_mono fun x => ?_)
    simp only [gtOneInd]
    by_cases hx : Real.log (ideleNorm F (nrdUnit x)) ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx, one_mul, one_mul]
      have hn1 : 1 ≤ n x := by
        simp only [n]
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((Real.log_pos_iff (ideleNorm_pos _).le).mp hx).le
      exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_le hn1 hs)
    · rw [indicator_of_notMem hx, zero_mul, zero_mul]
  -- real-valued bookkeeping on 2 < s < 3
  set bracket : ℝ → ℝ := fun s => A.toReal * (E s).toReal - cA.toReal / s + (Zgt s).toReal
  set M : ℝ := A.toReal * E₀.toReal + cA.toReal + (quatZeta a b gaussPhi 3).toReal
  have hev3 : ∀ᶠ s in 𝓝[>] (2 : ℝ), 2 < s ∧ s < 3 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (2 : ℝ) < 3 by norm_num))]
      with s h1 h2 using ⟨h1, h2⟩
  have hEne : ∀ s, 2 ≤ s → E s ≠ ⊤ := fun s hs => ne_top_of_le_ne_top hE₀ (hEle s hs)
  have hZgtne : ∀ s, s ≤ 3 → Zgt s ≠ ⊤ := fun s hs => ne_top_of_le_ne_top hZ3 (hZgt3 s hs)
  have hid : ∀ s, 2 < s → s < 3 →
      (s - 2) * (quatZeta a b gaussPhi s).toReal = A.toReal * cA.toReal + (s - 2) * bracket s := by
    intro s hs2 hs3
    have ht := htate s hs2
    have hRHS : A * (cA * ENNReal.ofReal (1 / (s - 2)) + E s) ≠ ⊤ :=
      ENNReal.mul_ne_top hAT (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hVT ENNReal.ofReal_ne_top,
        hEne s hs2.le⟩)
    have hZle : Zle s ≠ ⊤ := by
      intro h; rw [h, top_add] at ht; exact hRHS ht.symm
    have ht' := congrArg ENNReal.toReal ht
    rw [ENNReal.toReal_add hZle (ENNReal.mul_ne_top hVT ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_add
        (ENNReal.mul_ne_top hVT ENNReal.ofReal_ne_top) (hEne s hs2.le), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg zero_le_one (by linarith))] at ht'
    rw [hsplit s, ENNReal.toReal_add hZle (hZgtne s hs3.le)]
    have hs2' : s - 2 ≠ 0 := by linarith
    have hs0 : s ≠ 0 := by linarith
    simp only [bracket]
    field_simp
    have : (Zle s).toReal = A.toReal * (cA.toReal * (1 / (s - 2)) + (E s).toReal) - cA.toReal * (1 / s) := by
      linarith
    rw [this]
    field_simp
    ring
  have hbd : ∀ᶠ s in 𝓝[>] (2 : ℝ), ‖(s - 2) * bracket s‖ ≤ (s - 2) * M := by
    filter_upwards [hev3] with s ⟨hs2, hs3⟩
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have h1 : (E s).toReal ≤ E₀.toReal := ENNReal.toReal_mono hE₀ (hEle s hs2.le)
    have h2 : (Zgt s).toReal ≤ (quatZeta a b gaussPhi 3).toReal := ENNReal.toReal_mono hZ3 (hZgt3 s hs3.le)
    have h3 : cA.toReal / s ≤ cA.toReal := div_le_self ENNReal.toReal_nonneg (by linarith)
    have hE0 : 0 ≤ (E s).toReal := ENNReal.toReal_nonneg
    have hZ0 : 0 ≤ (Zgt s).toReal := ENNReal.toReal_nonneg
    have hc0 : 0 ≤ cA.toReal / s := div_nonneg ENNReal.toReal_nonneg (by linarith)
    have hA0' : 0 ≤ A.toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hA0', mul_nonneg hA0' hE0]
  have h0 : Tendsto (fun s : ℝ => (s - 2) * M) (𝓝[>] 2) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => (s - 2) * M) (𝓝 2) (𝓝 ((2 - 2) * M)) :=
      ((continuous_id.sub continuous_const).mul continuous_const).tendsto 2
    rw [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun s => (s - 2) * bracket s) (𝓝[>] 2) (𝓝 0) := squeeze_zero_norm' hbd h0
  have h := (tendsto_const_nhds (x := A.toReal * cA.toReal)).add hsq
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [hev3] with s ⟨hs2, hs3⟩
  exact (hid s hs2 hs3).symm

end Additive

/-! ### The division hypothesis and ramification -/

section Division

variable {a b : F}

theorem nrdForm_evalIn_coords (ξ : ℍ[F,a,b]) :
    (Quat.nrdForm a b).evalIn F (QuaternionAlgebra.linearEquivTuple a 0 b ξ) = (ξ * star ξ).re := by
  have hc : QuaternionAlgebra.linearEquivTuple a 0 b ξ = ![ξ.re, ξ.imI, ξ.imJ, ξ.imK] := by
    funext i; fin_cases i <;> rfl
  rw [hc]
  simp [QuadForm.evalIn, Quat.nrdForm, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal,
    QuaternionAlgebra.re_mul]

/-- **Ramified somewhere $\Rightarrow$ division**: if the norm form $\langle1,-a,-b,ab\rangle$ is anisotropic over some field
$K\supseteq F$ (e.g. a completion $F_v$ at which $\mathbb H[F,a,b]$ ramifies), then every nonzero element of
$\mathbb H[F,a,b]$ is invertible. -/
theorem hdiv_of_not_isotropicIn (K : Type*) [Field K] [Algebra F K] (h : ¬ (Quat.nrdForm a b).IsotropicIn K) :
    ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ := by
  refine isUnit_of_nrd_ne_zero a b fun ξ hξ hn => h ⟨fun i => algebraMap F K
    (QuaternionAlgebra.linearEquivTuple a 0 b ξ i), ?_, ?_⟩
  · intro h0
    apply hξ
    have : QuaternionAlgebra.linearEquivTuple a 0 b ξ = 0 :=
      funext fun i => (algebraMap F K).injective (by simpa using congrFun h0 i)
    exact (QuaternionAlgebra.linearEquivTuple a 0 b).map_eq_zero_iff.mp this
  · have h1 : (Quat.nrdForm a b).evalIn K (fun i => algebraMap F K (QuaternionAlgebra.linearEquivTuple a 0 b ξ i)) =
        algebraMap F K ((Quat.nrdForm a b).evalIn F (QuaternionAlgebra.linearEquivTuple a 0 b ξ)) := by
      simp only [QuadForm.evalIn, map_sum, map_mul, apply_ite, map_zero, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h1, nrdForm_evalIn_coords, hn, map_zero]

/-- **Division $\Leftrightarrow$ ramified at some place** (Hasse–Minkowski over $F$, `hasseMinkowski_nf`): for $a, b\ne0$,
$\mathbb H[F,a,b]$ is a division algebra iff its norm form is anisotropic at some completion of $F$. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (for the norm form of a quaternion algebra; cf. 57:9, p. 146); Weil 1982 §3.1 (division algebras) [unverified page]"]
theorem hdiv_iff_not_everywhere (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) ↔
      ¬ NFPlace.Everywhere (F := F) fun K _ _ => (Quat.nrdForm a b).IsotropicIn K := by
  rw [← hasseMinkowski_nf _ (Quat.nrdForm_nondegenerate two_ne_zero ha0 hb0)]
  constructor
  · rintro hdiv ⟨c, hc0, hc⟩
    set ξ := (QuaternionAlgebra.linearEquivTuple a 0 b).symm c
    have hcξ : QuaternionAlgebra.linearEquivTuple a 0 b ξ = c := LinearEquiv.apply_symm_apply _ c
    have hξ : ξ ≠ 0 := fun h => hc0 (by rw [← hcξ, h, map_zero])
    obtain ⟨u, hu⟩ := hdiv ξ hξ
    have hn : nrdLoc a b ξ = 0 := by
      change (ξ * star ξ).re = 0
      rw [← nrdForm_evalIn_coords, hcξ, hc]
    have h1 : nrdLoc a b (u : ℍ[F,a,b]) * nrdLoc a b ((u⁻¹ : (ℍ[F,a,b])ˣ) : ℍ[F,a,b]) = 1 := by
      rw [← nrdLoc_mul, Units.mul_inv, nrdLoc_one]
    rw [hu, hn, zero_mul] at h1
    exact zero_ne_one h1
  · intro h
    exact isUnit_of_nrd_ne_zero a b fun ξ hξ hn => h ⟨QuaternionAlgebra.linearEquivTuple a 0 b ξ,
      fun h0 => hξ ((QuaternionAlgebra.linearEquivTuple a 0 b).map_eq_zero_iff.mp h0),
      by rw [nrdForm_evalIn_coords, hn]⟩

end Division

/-! ### $c_A = \rho_F$ -/

section Main

/-- **Weil's Theorem 3.1.1 (iii) for a quaternion division algebra: $c_A = \rho_F$.** For $a, b\in\mathcal O_F\setminus0$ with
$\mathbb H[F,a,b]$ a division algebra (any number field, any signature),
$$\operatorname{vol}(\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1) = \rho_F$$
for the Tamagawa measure $\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ (`tamQuat`, without the factor $\rho_F^{-1}$; with
it the volume is $1$) and the splitting $\mathrm{quatSplit}_*\mu = \mu^1\times dt/t$, $t = \|\operatorname{nrd}x\|_{\mathbb A}$.
*Proof.* Both residues of $Z(s) = \int\Phi(x)\|\operatorname{nrd}x\|^s\,d\mu$ at $s = 2$ for the Gaussian test function:
multiplicatively $\rho_F\mu_f(\hat\Lambda)$ (`tendsto_mul_quatZeta`), additively $c_A'\mu_f(\hat\Lambda)$
(`tendsto_mul_quatZeta_additive`). -/
@[kb "weil1982" "§3.1, p. 40 (comparison of the residues); Theorem 3.1.1 (iii), p. 41 (c = ρ_k)"]
theorem quatVolConst_eq_residue {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    quatVolConst (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0) =
      ENNReal.ofReal (dedekindZeta_residue F) := by
  have ha := valued_coe_le_one (F := F) a
  have hb := valued_coe_le_one (F := F) b
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have hZ3 := quatZeta_three_ne_top ha0 hb0
  have hadd := tendsto_mul_quatZeta_additive ha hb ha0' hb0' hdiv hZ3
  have hmul := tendsto_mul_quatZeta ha0 hb0 measurable_gaussPhi (lintegral_gaussPhi_nrd_ne_top (a : F) (b : F))
  rw [lintegral_gaussPhi, ENNReal.toReal_one, mul_one, ← toReal_muFinVec_OHatVec] at hmul
  have heq := tendsto_nhds_unique hadd hmul
  set A := (muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4))).toReal
  have hA : 0 < A := ENNReal.toReal_pos muFinVec_OHatVec_ne_zero muFinVec_OHatVec_ne_top
  have hV : (quatVolConst ha hb ha0' hb0').toReal = dedekindZeta_residue F := by
    have := heq
    rw [mul_comm (dedekindZeta_residue F)] at this
    exact mul_left_cancel₀ hA.ne' this
  rw [← hV, ENNReal.ofReal_toReal (quatVolConst_lt_top ha hb ha0' hb0' hdiv).ne]

end Main

end

end QuadFormsKB.Tamagawa.Measure.Weil
