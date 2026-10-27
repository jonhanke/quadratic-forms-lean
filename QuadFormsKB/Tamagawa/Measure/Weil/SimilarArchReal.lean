import QuadFormsKB.Tamagawa.Measure.LerayReal
import QuadFormsKB.Tamagawa.Measure.LerayCount
import QuadFormsKB.Tamagawa.Measure.LerayUnimodular
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarDet

/-!
# The real Leray measure under a similarity

For nondegenerate real quadratic forms with $Q' = c\cdot(Q\circ G)$ (`Q'.hessian = c • (Gᵀ * Q.hessian * G)`,
$c \ne 0$), conjugation $g \mapsto G^{-1}gG$ is an isomorphism of topological groups
$SO(Q)(\mathbb R) \to SO(Q')(\mathbb R)$ and carries the Leray measure $\mu_Q$ to $|\det L|\,\mu_{Q'}$, where
$L = c\cdot\mathrm{act}(G)$ is the induced linear map of coefficient space.

* `conjSO`, `conjSO_mat`: the isomorphism and its matrices.
* `phi_simConj`: $\Phi_{Q'}(G^{-1}XG) = (c\cdot\mathrm{act}\,G)(\Phi_Q(X))$.
* `tendsto_avg_family`, `lintegral_regionOf`, `tendsto_region_of`: the Leray limit along an arbitrary
  shrinking family of coefficient sets (generalizing `tendsto_lerayApprox`).
* `tendsto_lerayApprox_simConj`: transport of the Leray limit (conjugation is volume preserving on $M_n(\mathbb R)$).
* `map_lerayMeasure_conjSO`, `map_lerayMeasure_conjSO'`: the transformation law, with
  $|\det L| = |c|^{n(n+1)/2}|\det G|^{n+1}$.
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.ArchSOMeasure

/-! ### Conjugation `g ↦ G⁻¹ g G` between the special orthogonal groups of similar forms -/

section Conj

variable {n : ℕ} {Q Q' : QuadForm ℝ n} (G : GL (Fin n) ℝ) (c : ℝ)
  (hH : Q'.hessian = c • ((G : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℝ)))

include hH in
theorem gram_eq_of_similar :
    gramMatrixR Q' = c • ((G : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * (G : Matrix (Fin n) (Fin n) ℝ)) := by
  rw [gramMatrixR, gramMatrixR, hH, Matrix.mul_smul, Matrix.smul_mul, smul_comm]

include hH in
/-- Conjugation by $G^{-1}$ maps $SO(Q)$ into $SO(Q')$ when $H' = c\,G^{\mathsf T}HG$. -/
theorem conj_mem_soReal_similar {g : GL (Fin n) ℝ} (hg : g ∈ soReal Q) : G⁻¹ * g * G ∈ soReal Q' := by
  obtain ⟨h1, h2⟩ := (mem_soReal_iff Q g).mp hg
  rw [mem_soReal_iff]
  set pm : Matrix (Fin n) (Fin n) ℝ := (G : Matrix (Fin n) (Fin n) ℝ) with hpm
  set qm : Matrix (Fin n) (Fin n) ℝ := ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) with hqm
  set gm : Matrix (Fin n) (Fin n) ℝ := (g : Matrix (Fin n) (Fin n) ℝ) with hgm
  have e1 : pm * qm = 1 := hPPi G
  have e3 : qm * pm = 1 := hPiP G
  have e2 : qmᵀ * pmᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  simp only [Units.val_mul]
  constructor
  · rw [hH]
    calc (qm * gm * pm)ᵀ * (c • (pmᵀ * Q.hessian * pm)) * (qm * gm * pm)
        = c • (pmᵀ * (gmᵀ * ((qmᵀ * pmᵀ) * Q.hessian * (pm * qm)) * gm) * pm) := by
          simp only [transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (pmᵀ * Q.hessian * pm) := by
          rw [e1, e2]
          simp only [Matrix.one_mul, Matrix.mul_one]
          congr 1
          rw [h1]
  · rw [Matrix.det_mul, Matrix.det_mul, h2]
    have := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_one] at this
    linarith [mul_comm (pm.det) (qm.det)]

include hH in
/-- The relation $H' = c\,G^{\mathsf T}HG$ read backwards ($c \ne 0$): $H = c^{-1}(G^{-1})^{\mathsf T}H'G^{-1}$. -/
theorem hessian_eq_of_similar (hc : c ≠ 0) :
    Q.hessian = c⁻¹ • (((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q'.hessian *
      ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
  have e1 := hPPi G
  have e2 : ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * (G : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
    rw [← transpose_mul, e1, transpose_one]
  rw [hH]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  calc Q.hessian = (((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * (G : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
        Q.hessian * ((G : Matrix (Fin n) (Fin n) ℝ) * ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
        rw [e1, e2]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **Conjugation $g \mapsto G^{-1}gG$**, an isomorphism of topological groups
$SO(Q)(\mathbb R) \to SO(Q')(\mathbb R)$ when $H' = c\,G^{\mathsf T}HG$ with $c \ne 0$
(i.e. $Q' = c\cdot(Q\circ G)$). -/
def conjSO (hc : c ≠ 0) : ArchSO Q ≃ₜ* ArchSO Q' where
  toFun g := ⟨G⁻¹ * g.1 * G, conj_mem_soReal_similar G c hH g.2⟩
  invFun h := ⟨G⁻¹⁻¹ * h.1 * G⁻¹, conj_mem_soReal_similar G⁻¹ c⁻¹ (hessian_eq_of_similar G c hH hc) h.2⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    show G⁻¹ * (a.1 * b.1) * G = (G⁻¹ * a.1 * G) * (G⁻¹ * b.1 * G)
    simp [mul_assoc])
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The matrix of $G^{-1}gG$. -/
theorem conjSO_mat (hc : c ≠ 0) (g : ArchSO Q) :
    ArchSOInst.mat Q' (conjSO G c hH hc g) =
      ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * ArchSOInst.mat Q g * (G : Matrix (Fin n) (Fin n) ℝ) := by
  rfl

include hH in
/-- **$\Phi$ transforms by $c\cdot\mathrm{act}(G)$ under conjugation**:
$\Phi_{Q'}(G^{-1}XG) = (c\cdot\mathrm{act}\,G)(\Phi_Q(X))$. -/
theorem phi_simConj (X : Matrix (Fin n) (Fin n) ℝ) :
    phi Q' (((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * X * (G : Matrix (Fin n) (Fin n) ℝ)) =
      (c • act (G : Matrix (Fin n) (Fin n) ℝ)) (phi Q X) := by
  set pm : Matrix (Fin n) (Fin n) ℝ := (G : Matrix (Fin n) (Fin n) ℝ) with hpm
  set qm : Matrix (Fin n) (Fin n) ℝ := ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) with hqm
  have e1 : pm * qm = 1 := hPPi G
  have e2 : qmᵀ * pmᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  rw [LinearMap.smul_apply, phi, phi, act_apply, symOf_wtU (gram_sym_mul Q X), ← wtU_smul, gram_eq_of_similar G c hH]
  congr 1
  calc (qm * X * pm)ᵀ * (c • (pmᵀ * gramMatrixR Q * pm)) * (qm * X * pm)
      = c • (pmᵀ * (Xᵀ * ((qmᵀ * pmᵀ) * gramMatrixR Q * (pm * qm)) * X) * pm) := by
        simp only [transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = c • (pmᵀ * (Xᵀ * gramMatrixR Q * X) * pm) := by
        rw [e1, e2]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]

end Conj

/-! ### The Leray limit along an arbitrary shrinking family of measurable sets -/

section Family

/-- **Averages over a shrinking family of sets**: if $G \ge 0$ is continuous on an open $U \ni c_0$ and the
measurable sets $S_\varepsilon$ have finite positive $\mu$-mass and lie eventually in every ball $B_\delta(c_0)$,
then $\frac{1}{\mu(S_\varepsilon)}\int_{S_\varepsilon}G\,d\mu \to G(c_0)$ as $\varepsilon \to 0^+$. -/
theorem tendsto_avg_family {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) {c₀ : E} {S : ℝ → Set E} (hSm : ∀ ε, 0 < ε → MeasurableSet (S ε))
    (hpos : ∀ ε, 0 < ε → 0 < μ (S ε)) (hfin : ∀ ε, 0 < ε → μ (S ε) ≠ ∞)
    (hS : ∀ δ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball c₀ δ)
    {U : Set E} (hU : IsOpen U) (hc : c₀ ∈ U) {G : E → ℝ}
    (hGc : ContinuousOn G U) (hG0 : ∀ t ∈ U, 0 ≤ G t) :
    Tendsto (fun ε => (∫⁻ t in S ε, ENNReal.ofReal (G t) ∂μ).toReal / (μ (S ε)).toReal) (𝓝[>] 0)
      (𝓝 (G c₀)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hcont : ContinuousAt G c₀ := hGc.continuousAt (hU.mem_nhds hc)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hcont (η / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.isOpen_iff.mp hU c₀ hc
  filter_upwards [hS (min δ1 δ2) (by positivity), self_mem_nhdsWithin] with ε hSε hε
  have hε : 0 < ε := hε
  set B := S ε
  have hsub : ∀ t ∈ B, dist t c₀ < min δ1 δ2 := fun t ht => Metric.mem_ball.mp (hSε ht)
  have hU' : ∀ t ∈ B, t ∈ U := fun t ht =>
    h2 (Metric.mem_ball.mpr ((hsub t ht).trans_le (min_le_right _ _)))
  have hclose : ∀ t ∈ B, |G t - G c₀| < η / 2 := fun t ht => by
    rw [← Real.dist_eq]; exact h1 ((hsub t ht).trans_le (min_le_left _ _))
  have hmeasB : MeasurableSet B := hSm ε hε
  have hV : μ B ≠ ∞ := hfin ε hε
  have hV0 : 0 < (μ B).toReal := ENNReal.toReal_pos (hpos ε hε).ne' hV
  have hG0' := hG0 c₀ hc
  have hup : ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ ≤ ENNReal.ofReal (G c₀ + η / 2) * μ B := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).2])
  have hlo : ENNReal.ofReal (G c₀ - η / 2) * μ B ≤ ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).1])
  have hfin' : ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hup' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hlo' := ENNReal.toReal_mono hfin' hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hup'
  rw [ENNReal.toReal_mul] at hlo'
  have hlo'' : (G c₀ - η / 2) * (μ B).toReal ≤ (∫⁻ t in B, ENNReal.ofReal (G t) ∂μ).toReal :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _) hV0.le) hlo'
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hV0]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hV0]; nlinarith

variable {n : ℕ} {Q : QuadForm ℝ n}

/-- **The region over a set $E$ of coefficients**: $\{X : \det X > 0,\ \Phi_Q(X) \in E\}$ (column coordinates). -/
def regionOf (Q : QuadForm ℝ n) (E : Set (UIdx n → ℝ)) : Set (Fin n → Fin n → ℝ) :=
  {X | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ E}

theorem measurableSet_regionOf {E : Set (UIdx n → ℝ)} (hE : MeasurableSet E) :
    MeasurableSet (regionOf Q E) := by
  have hdc : Continuous fun X : Fin n → Fin n → ℝ => (Matrix.of X).det := by
    have : (fun X : Fin n → Fin n → ℝ => (Matrix.of X).det) = fun X => (ofCols X).det :=
      funext fun X => (det_ofCols X).symm
    rw [this]; exact continuous_ofCols.matrix_det
  exact (measurableSet_lt measurable_const hdc.measurable).inter
    (hE.preimage (continuous_pullCoeff Q).measurable)

variable (D : Diag Q)

/-- **The fibration identity over a general measurable set** $E \subseteq U$, for $f \ge 0$:
$\int_{\mathrm{region}(E)} f = \int_E F_f(\beta^{-1}c)\rho(c)\,dc$. -/
theorem lintegral_regionOf {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ X, 0 ≤ f X) {E : Set (UIdx n → ℝ)} (hB : MeasurableSet E) (hε : E ⊆ range (beta D)) :
    ∫⁻ X in regionOf Q E, ENNReal.ofReal (f X) =
      ∫⁻ c in E, ENNReal.ofReal (fibreInt D f (sec D c) * rho D c) := by
  have hT : MeasurableSet (beta D ⁻¹' E) := (continuous_beta D).measurable hB
  rw [regionOf, ← image_chart D hε,
    setLIntegral_image_comap (measurableEmbedding_chart D) volume (MeasurableSet.univ.prod hT), lerayFibration,
    ← Measure.prod_restrict, Measure.restrict_univ]
  rw [lintegral_prod_symm (fun x => ENNReal.ofReal (f (chart D x)))
    ((ENNReal.continuous_ofReal.comp (hf.comp (continuous_chart D))).measurable.aemeasurable)]
  have hinner : ∀ b, ∫⁻ g, ENNReal.ofReal (f (chart D (g, b))) ∂lerayD D = ENNReal.ofReal (fibreInt D f b) := by
    intro b
    rw [fibreInt, ofReal_integral_eq_lintegral_ofReal]
    · exact (hf.comp ((continuous_chart D).comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hasCompactSupport_fibre D hfc b)
    · exact Filter.Eventually.of_forall fun g => hf0 _
  simp_rw [hinner]
  rw [setLIntegral_kappa0 D hB (ψ := fun b => ENNReal.ofReal (fibreInt D f b))
      (ENNReal.continuous_ofReal.comp (continuous_fibreInt D hf hfc)).measurable,
    inter_eq_left.mpr hε]
  refine setLIntegral_congr_fun hB fun c _ => ?_
  have h0 : 0 ≤ fibreInt D f (sec D c) := integral_nonneg fun g => hf0 _
  rw [mul_comm, ← ENNReal.ofReal_mul h0]

/-- **The Leray limit along a shrinking family, $f \ge 0$.** -/
theorem tendsto_region_of_nonneg {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ X, 0 ≤ f X) {S : ℝ → Set (UIdx n → ℝ)}
    (hSm : ∀ ε, 0 < ε → MeasurableSet (S ε))
    (hpos : ∀ ε, 0 < ε → 0 < volume (S ε)) (hfin : ∀ ε, 0 < ε → volume (S ε) ≠ ∞)
    (hS : ∀ δ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball (coeffU Q) δ) :
    Tendsto (fun ε => (∫ X in regionOf Q (S ε), f X) / (volume (S ε)).toReal) (𝓝[>] 0)
      (𝓝 (∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D)) := by
  set H : (UIdx n → ℝ) → ℝ := fun c => fibreInt D f (sec D c) * rho D c
  have hHc : ContinuousOn H (range (beta D)) :=
    ((continuous_fibreInt D hf hfc).comp_continuousOn (continuousOn_sec D)).mul (continuousOn_rho D)
  have hH0 : ∀ c ∈ range (beta D), 0 ≤ H c := fun c _ =>
    mul_nonneg (integral_nonneg fun g => hf0 _) (rho_nonneg D c)
  have h := tendsto_avg_family volume hSm hpos hfin hS (isOpen_range_beta D) (coeffU_mem_range D) hHc hH0
  have hH1 : H (coeffU Q) = ∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
    simp only [H, rho_coeffU, mul_one, sec_coeffU, fibreInt, chart, SliceB.mat_one]
  rw [hH1] at h
  obtain ⟨δ0, hδ0, hsub0⟩ := Metric.isOpen_iff.mp (isOpen_range_beta D) _ (coeffU_mem_range D)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hS δ0 hδ0] with ε hε hsub
  have hε' : 0 < ε := hε
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => hf0 X)
      hf.aestronglyMeasurable, lintegral_regionOf D hf hfc hf0 (hSm ε hε') (hsub.trans hsub0)]

/-- **The Leray limit along a shrinking family of sets** (any signature, any compactly supported continuous
$f$): if the measurable sets $S_\varepsilon$ of coefficient space have finite positive volume and lie eventually
in every ball about $c_Q$, then
$\frac{1}{\mathrm{Leb}(S_\varepsilon)}\int_{\{\det X>0,\ \Phi_Q(X)\in S_\varepsilon\}} f\,dX \to \int f\,d\mu_Q$. -/
theorem tendsto_region_of {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {S : ℝ → Set (UIdx n → ℝ)} (hSm : ∀ ε, 0 < ε → MeasurableSet (S ε))
    (hpos : ∀ ε, 0 < ε → 0 < volume (S ε)) (hfin : ∀ ε, 0 < ε → volume (S ε) ≠ ∞)
    (hS : ∀ δ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball (coeffU Q) δ) :
    Tendsto (fun ε => (∫ X in regionOf Q (S ε), f X) / (volume (S ε)).toReal) (𝓝[>] 0)
      (𝓝 (∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D)) := by
  set fp : (Fin n → Fin n → ℝ) → ℝ := fun X => max (f X) 0
  set fm : (Fin n → Fin n → ℝ) → ℝ := fun X => max (-f X) 0
  have hfp : Continuous fp := hf.max continuous_const
  have hfm : Continuous fm := hf.neg.max continuous_const
  have hfpc : HasCompactSupport fp := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fp, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hfmc : HasCompactSupport fm := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fm, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hp := tendsto_region_of_nonneg D hfp hfpc (fun X => le_max_right _ _) hSm hpos hfin hS
  have hm := tendsto_region_of_nonneg D hfm hfmc (fun X => le_max_right _ _) hSm hpos hfin hS
  have hsplit : ∀ ε, (∫ X in regionOf Q (S ε), f X) / (volume (S ε)).toReal =
      (∫ X in regionOf Q (S ε), fp X) / (volume (S ε)).toReal -
        (∫ X in regionOf Q (S ε), fm X) / (volume (S ε)).toReal := by
    intro ε
    have hip : IntegrableOn fp (regionOf Q (S ε)) := (hfp.integrable_of_hasCompactSupport hfpc).integrableOn
    have him : IntegrableOn fm (regionOf Q (S ε)) := (hfm.integrable_of_hasCompactSupport hfmc).integrableOn
    rw [← sub_div, ← integral_sub hip him]
    congr 2; funext X; exact (max_zero_sub_max_neg_zero_eq_self (f X)).symm
  have hG : ∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D =
      ∫ g, fp (cols (ArchSOInst.mat Q g)) ∂lerayD D - ∫ g, fm (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
    have hc1 := hasCompactSupport_fibre D hfpc 1
    have hc2 := hasCompactSupport_fibre D hfmc 1
    simp only [chart, SliceB.mat_one, Matrix.mul_one] at hc1 hc2
    have i1 : Integrable (fun g => fp (cols (ArchSOInst.mat Q g))) (lerayD D) :=
      (hfp.comp (continuous_cols.comp (ArchSOInst.continuous_mat Q))).integrable_of_hasCompactSupport hc1
    have i2 : Integrable (fun g => fm (cols (ArchSOInst.mat Q g))) (lerayD D) :=
      (hfm.comp (continuous_cols.comp (ArchSOInst.continuous_mat Q))).integrable_of_hasCompactSupport hc2
    rw [← integral_sub i1 i2]
    congr 1; funext g; exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hG, show (fun ε => (∫ X in regionOf Q (S ε), f X) / (volume (S ε)).toReal) =
    fun ε => (∫ X in regionOf Q (S ε), fp X) / (volume (S ε)).toReal -
        (∫ X in regionOf Q (S ε), fm X) / (volume (S ε)).toReal from funext hsplit]
  exact hp.sub hm

end Family

/-! ### Transport of the Leray limit along a similarity -/

section Main

variable {n : ℕ} {Q Q' : QuadForm ℝ n} (G : GL (Fin n) ℝ) (c : ℝ)
  (hH : Q'.hessian = c • ((G : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℝ)))

/-- **The map $X \mapsto G^{-1}XG$** on $M_n(\mathbb R)$ in column coordinates. -/
def conjL : (Fin n → Fin n → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℝ) :=
  rmulL (G : Matrix (Fin n) (Fin n) ℝ) ∘ₗ lmulL ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)

theorem cols_conj (X : Matrix (Fin n) (Fin n) ℝ) :
    cols (((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * X * (G : Matrix (Fin n) (Fin n) ℝ)) =
      conjL G (cols X) := by
  rw [cols_mul_right, cols_mul_left]; rfl

/-- Conjugation has determinant $1$ on $M_n(\mathbb R)$, hence preserves Lebesgue measure. -/
theorem det_conjL : LinearMap.det (conjL G) = 1 := by
  rw [conjL, LinearMap.det_comp, det_rmulL, det_lmulL, ← mul_pow, ← Matrix.det_mul, hPPi G, det_one, one_pow]

theorem det_conjL_ne_zero : LinearMap.det (conjL G) ≠ 0 := by rw [det_conjL]; exact one_ne_zero

/-- Conjugation as a homeomorphism of $M_n(\mathbb R)$. -/
def conjE : (Fin n → Fin n → ℝ) ≃ₜ (Fin n → Fin n → ℝ) :=
  (LinearMap.equivOfDetNeZero (conjL G) (det_conjL_ne_zero G)).toContinuousLinearEquiv.toHomeomorph

theorem conjE_apply (X : Fin n → Fin n → ℝ) : conjE G X = conjL G X := rfl

theorem continuous_conjL : Continuous (conjL G) := LinearMap.continuous_of_finiteDimensional _

theorem measurePreserving_conjL : MeasurePreserving (conjL G) volume volume := by
  refine ⟨(continuous_conjL G).measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (det_conjL_ne_zero G), det_conjL]
  simp

theorem measurableEmbedding_conjL : MeasurableEmbedding (conjL G) :=
  (continuous_conjL G).measurableEmbedding fun x y h => (conjE G).injective (by simpa [conjE_apply] using h)

theorem setIntegral_conjL (f : (Fin n → Fin n → ℝ) → ℝ) (S : Set (Fin n → Fin n → ℝ)) :
    ∫ X in conjL G ⁻¹' S, f (conjL G X) = ∫ Y in S, f Y :=
  (measurePreserving_conjL G).setIntegral_preimage_emb (measurableEmbedding_conjL G) f S

/-- $c\cdot\mathrm{act}(G)$ is invertible when $c \ne 0$. -/
theorem det_smul_act_ne_zero (hc : c ≠ 0) :
    LinearMap.det (c • act (G : Matrix (Fin n) (Fin n) ℝ)) ≠ 0 := by
  have h1 : ∀ x, (c⁻¹ • act ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ))
      ((c • act (G : Matrix (Fin n) (Fin n) ℝ)) x) = x := by
    intro x
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [← act_mul, hPPi G, act_one, mul_inv_cancel₀ hc, one_smul]
  have h2 : ∀ x, (c • act (G : Matrix (Fin n) (Fin n) ℝ))
      ((c⁻¹ • act ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) x) = x := by
    intro x
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [← act_mul, hPiP G, act_one, inv_mul_cancel₀ hc, one_smul]
  have := LinearEquiv.isUnit_det' (LinearEquiv.ofLinearMap (c • act (G : Matrix (Fin n) (Fin n) ℝ))
    (c⁻¹ • act ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) (LinearMap.ext h2) (LinearMap.ext h1))
  exact this.ne_zero

include hH in
theorem coeffU_similar :
    coeffU Q' = (c • act (G : Matrix (Fin n) (Fin n) ℝ)) (coeffU Q) := by
  have := phi_simConj G c hH 1
  rw [Matrix.mul_one, hPiP G, phi_one, phi_one] at this
  exact this

include hH in
/-- **The regions correspond**: $\{X : \det(G^{-1}XG) > 0,\ \Phi_{Q'}(G^{-1}XG) \in B\} =
\{X : \det X > 0,\ \Phi_Q(X) \in L^{-1}B\}$ with $L = c\cdot\mathrm{act}(G)$. -/
theorem preimage_regionOf_conjL (B : Set (UIdx n → ℝ)) :
    conjL G ⁻¹' regionOf Q' B = regionOf Q ((c • act (G : Matrix (Fin n) (Fin n) ℝ)) ⁻¹' B) := by
  ext X
  set M : Matrix (Fin n) (Fin n) ℝ :=
    ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * ofCols X * (G : Matrix (Fin n) (Fin n) ℝ) with hM
  have hT : conjL G X = cols M := by rw [hM, cols_conj, cols_ofCols]
  have hd : (Matrix.of (cols M)).det = (Matrix.of X).det := by
    rw [← det_ofCols (cols M), ← det_ofCols X]
    show M.det = _
    rw [hM, Matrix.det_mul, Matrix.det_mul]
    have := congrArg Matrix.det (hPPi G)
    rw [Matrix.det_mul, Matrix.det_one] at this
    have h2 : (G : Matrix (Fin n) (Fin n) ℝ).det * ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ).det = 1 := this
    calc _ = ((G : Matrix (Fin n) (Fin n) ℝ).det * ((G⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ).det) *
          (ofCols X).det := by ring
      _ = _ := by rw [h2, one_mul]
  have hp : pullCoeff Q' (cols M) = (c • act (G : Matrix (Fin n) (Fin n) ℝ)) (pullCoeff Q X) := by
    rw [← phi_eq_pullCoeff, hM, phi_simConj G c hH, phi_eq_pullCoeff, cols_ofCols]
  simp only [regionOf, mem_preimage, mem_ofPred_eq, hT, hd, hp]

end Main

/-! ### The transformation law of the Leray measure -/

section Final

variable {n : ℕ} {Q Q' : QuadForm ℝ n} (G : GL (Fin n) ℝ) (c : ℝ)
  (hH : Q'.hessian = c • ((G : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℝ)))

theorem cols_conjSO (hc : c ≠ 0) (g : ArchSO Q) :
    cols (ArchSOInst.mat Q' (conjSO G c hH hc g)) = conjL G (cols (ArchSOInst.mat Q g)) := by
  rw [conjSO_mat, cols_conj]

include hH in
/-- **The Leray limit transported along a similarity.** With $L = c\cdot\mathrm{act}(G)$ on coefficient space,
$$\frac{1}{\mathrm{Leb}(B_\varepsilon(c_{Q'}))}\int_{\{\det Y>0,\ \Phi_{Q'}(Y)\in B_\varepsilon(c_{Q'})\}} f\,dY
\longrightarrow |\det L|^{-1}\int_{SO(Q)(\mathbb R)} f(\mathrm{cols}(G^{-1}gG))\,d\mu_Q(g). $$ -/
theorem tendsto_lerayApprox_simConj (hc : c ≠ 0) (hQ : gramDetR Q ≠ 0) {f : (Fin n → Fin n → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (lerayApprox Q' f) (𝓝[>] 0)
      (𝓝 (|(LinearMap.det (c • act (G : Matrix (Fin n) (Fin n) ℝ)))⁻¹| *
        ∫ g, f (cols (ArchSOInst.mat Q' (conjSO G c hH hc g))) ∂lerayMeasure Q hQ)) := by
  set L : (UIdx n → ℝ) →ₗ[ℝ] (UIdx n → ℝ) := c • act (G : Matrix (Fin n) (Fin n) ℝ) with hL
  have hd : LinearMap.det L ≠ 0 := det_smul_act_ne_zero G c hc
  set Le : (UIdx n → ℝ) ≃ₗ[ℝ] (UIdx n → ℝ) := LinearMap.equivOfDetNeZero L hd with hLe
  have hLe_apply : ∀ x, Le x = L x := fun _ => rfl
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional _
  have hLsymm : Continuous Le.symm := LinearMap.continuous_of_finiteDimensional Le.symm.toLinearMap
  have hc0 : coeffU Q' = L (coeffU Q) := coeffU_similar G c hH
  set f' : (Fin n → Fin n → ℝ) → ℝ := fun X => f (conjL G X) with hf'
  have hf'c : Continuous f' := hf.comp (continuous_conjL G)
  have hf'cs : HasCompactSupport f' := hfc.comp_homeomorph (conjE G)
  set S : ℝ → Set (UIdx n → ℝ) := fun ε => L ⁻¹' Metric.closedBall (coeffU Q') ε with hS
  have hvol : ∀ ε, volume (S ε) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| * volume (Metric.closedBall (coeffU Q') ε) :=
    fun ε => Measure.addHaar_preimage_linearMap volume hd _
  have hda : 0 < |(LinearMap.det L)⁻¹| := abs_pos.mpr (inv_ne_zero hd)
  have hSm : ∀ ε, 0 < ε → MeasurableSet (S ε) := fun ε _ =>
    Metric.isClosed_closedBall.measurableSet.preimage hLc.measurable
  have hpos : ∀ ε, 0 < ε → 0 < volume (S ε) := fun ε hε => by
    rw [hvol]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hda).ne' (Metric.measure_closedBall_pos _ _ hε).ne'
  have hfin : ∀ ε, 0 < ε → volume (S ε) ≠ ∞ := fun ε hε => by
    rw [hvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have hSball : ∀ δ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball (coeffU Q) δ := by
    intro δ hδ
    obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.mp (hLsymm.continuousAt (x := L (coeffU Q))) δ hδ
    filter_upwards [Ioo_mem_nhdsGT hη] with ε hε x hx
    have hx' : dist (L x) (L (coeffU Q)) ≤ ε := by
      have := Metric.mem_closedBall.mp hx
      rwa [hc0] at this
    have := h (x := L x) (lt_of_le_of_lt hx' hε.2)
    rw [← hLe_apply, ← hLe_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
    exact Metric.mem_ball.mpr this
  have h := tendsto_region_of (Diag.ofSpectral Q hQ) hf'c hf'cs hSm hpos hfin hSball
  have h2 := h.const_mul |(LinearMap.det L)⁻¹|
  have hlim : ∫ g, f' (cols (ArchSOInst.mat Q g)) ∂lerayD (Diag.ofSpectral Q hQ) =
      ∫ g, f (cols (ArchSOInst.mat Q' (conjSO G c hH hc g))) ∂lerayMeasure Q hQ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    rw [cols_conjSO]
  rw [hlim] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have hI : ∫ X in regionOf Q (S ε), f' X = ∫ Y in lerayRegion Q' ε, f Y := by
    have : regionOf Q (S ε) = conjL G ⁻¹' regionOf Q' (Metric.closedBall (coeffU Q') ε) :=
      (preimage_regionOf_conjL G c hH _).symm
    rw [this]
    exact setIntegral_conjL G f _
  have hv : 0 < (volume (Metric.closedBall (coeffU Q') ε)).toReal :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos _ _ hε').ne' measure_closedBall_lt_top.ne
  rw [hI, lerayApprox, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hda.le]
  field_simp

/-- **Similarities scale the Leray measure by the Jacobian.** If $Q' = c\cdot(Q\circ G)$
(`Q'.hessian = c • (Gᵀ * Q.hessian * G)`, $c \ne 0$, both forms nondegenerate), then conjugation
$g \mapsto G^{-1}gG$, $SO(Q)(\mathbb R) \to SO(Q')(\mathbb R)$, carries $\mu_Q$ to $|\det L|\,\mu_{Q'}$,
where $L = c\cdot\mathrm{act}(G)$ is the induced linear map of coefficient space $c_{ij}$, $i \le j$.
(Sanity check: $G = 1$, $Q' = cQ$ gives $\mu_Q = |c|^{n(n+1)/2}\mu_{cQ}$, consistent with
$dX = \mu_Q \otimes dc$.) -/
theorem map_lerayMeasure_conjSO (hc : c ≠ 0) (hQ : gramDetR Q ≠ 0) (hQ' : gramDetR Q' ≠ 0) :
    (lerayMeasure Q hQ).map (conjSO G c hH hc) =
      ENNReal.ofReal |LinearMap.det (c • act (G : Matrix (Fin n) (Fin n) ℝ))| • lerayMeasure Q' hQ' := by
  set d := LinearMap.det (c • act (G : Matrix (Fin n) (Fin n) ℝ)) with hdd
  have hd : d ≠ 0 := det_smul_act_ne_zero G c hc
  have hda : 0 < |d⁻¹| := abs_pos.mpr (inv_ne_zero hd)
  have hemb : MeasurableEmbedding (conjSO G c hH hc) := (conjSO G c hH hc).toHomeomorph.measurableEmbedding
  haveI : (lerayMeasure Q hQ).IsHaarMeasure := isHaarMeasure_lerayMeasure hQ
  haveI : ((lerayMeasure Q hQ).map (conjSO G c hH hc)).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map _ _
  haveI : (ENNReal.ofReal |d⁻¹| • (lerayMeasure Q hQ).map (conjSO G c hH hc)).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (ENNReal.ofReal_pos.mpr hda).ne' ENNReal.ofReal_ne_top
  have huniq := lerayMeasure_unique (Q := Q') hQ'
    (ENNReal.ofReal |d⁻¹| • (lerayMeasure Q hQ).map (conjSO G c hH hc)) (fun f hf hfc => by
      have := tendsto_lerayApprox_simConj G c hH hc hQ hf hfc
      rwa [integral_smul_measure, hemb.integral_map, ENNReal.toReal_ofReal hda.le, smul_eq_mul])
  rw [← huniq, smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hd]
  simp

/-- **The same, with the Jacobian made explicit**:
$|\det L| = |c|^{n(n+1)/2}\,|\det G|^{n+1}$. -/
theorem map_lerayMeasure_conjSO' (hc : c ≠ 0) (hQ : gramDetR Q ≠ 0) (hQ' : gramDetR Q' ≠ 0) :
    (lerayMeasure Q hQ).map (conjSO G c hH hc) =
      ENNReal.ofReal (|c| ^ (n * (n + 1) / 2) * |(G : Matrix (Fin n) (Fin n) ℝ).det| ^ (n + 1)) •
        lerayMeasure Q' hQ' := by
  rw [map_lerayMeasure_conjSO G c hH hc hQ hQ', LinearMap.det_smul, Module.finrank_fintype_fun_eq_card,
    Weil.card_UIdx, det_act, abs_mul, abs_pow, abs_pow]

end Final

end QuadFormsKB.Tamagawa.Measure.LerayReal
