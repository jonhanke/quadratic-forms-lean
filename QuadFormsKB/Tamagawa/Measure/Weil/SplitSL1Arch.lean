import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Fibre
import QuadFormsKB.Tamagawa.Measure.Weil.GL2LocalFibrationInst

/-!
# The archimedean factor of the box, for split $D$

$F$ a number field, $F_\infty$ = `mixedSpace F` with the self-dual measure $dx$ and module $|x|_\infty$ = `normInf`.

* `vecToMat` $(c_0, c_1, c_2, c_3)\mapsto\begin{pmatrix} c_0 & c_1\\ c_2 & c_3\end{pmatrix}$, and the integrand
  `glDensInf W` $(c) = \mathbf 1[c_0\in F_\infty^\times]\,\mathbf 1[\det\in F_\infty^\times]\,|\det|_\infty^{-2}\,
  \mathbf 1_W$ of $|\det X|^{-2}dX$ on $W$.
* **`lintegral_omegaInf_muGaugeInf`**: $\int_{F_\infty^\times}|\omega|_\infty\{Y : \sigma(t)Y\in W\}\,d^\times t =
  \int|\det X|_\infty^{-2}\mathbf 1_W(X)\,dX$ (the archimedean local fibration $\mathrm{GL}_2\to\mathbb G_m$,
  `GL2Fib.lintegral_gl2_fibration'` with `hyp_mixedSpace`).
-/

open MeasureTheory Measure Set NumberField NumberField.mixedEmbedding
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-- $(c_0, c_1, c_2, c_3)\mapsto\begin{pmatrix} c_0 & c_1\\ c_2 & c_3\end{pmatrix}$. -/
def vecToMat {R : Type*} (c : Fin 4 → R) : Matrix (Fin 2) (Fin 2) R := !![c 0, c 1; c 2, c 3]

theorem measurable_vecToMat {R : Type*} [MeasurableSpace R] : Measurable (vecToMat (R := R)) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [measurable_pi_apply 0, measurable_pi_apply 1, measurable_pi_apply 2, measurable_pi_apply 3]

/-- The density of $|\det X|^{-2}\,dX$ on $W$, in the coordinates $c$ (with the chart condition $c_0$ a unit). -/
def glDensInf (W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) (c : Fin 4 → mixedSpace F) : ℝ≥0∞ :=
  {x : mixedSpace F | IsUnit x}.indicator (fun _ => 1) (c 0) *
    {x : mixedSpace F | IsUnit x}.indicator (fun d => (normInf d)⁻¹ ^ 2) (c 0 * c 3 - c 1 * c 2) *
      W.indicator (fun _ => 1) (vecToMat c)

theorem range_units_val_mixedSpace : Set.range (Units.val : (mixedSpace F)ˣ → mixedSpace F) = {x | IsUnit x} := by
  ext x; exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

/-- $\int_{F_\infty^\times}g\,d^\times t = \int_{F_\infty}\mathbf 1[t\in F_\infty^\times]\,|t|_\infty^{-1}g(t)\,dt$. -/
theorem lintegral_omegaInf_units {g : mixedSpace F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g (t : mixedSpace F) ∂omegaInf F =
      ∫⁻ t, {x : mixedSpace F | IsUnit x}.indicator (fun t => (normInf t)⁻¹ * g t) t
        ∂Analysis.selfDualInf (F := F) := by
  have he : MeasurableEmbedding (Units.val : (mixedSpace F)ˣ → mixedSpace F) :=
    isOpenEmbedding_val_mixedSpace.measurableEmbedding
  have hd : Measurable fun x : mixedSpace F => (normInf x)⁻¹ := measurable_normInf.inv
  have hpt : (fun u : (mixedSpace F)ˣ => ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (u : mixedSpace F))|⁻¹) =
      fun u : (mixedSpace F)ˣ => (normInf (u : mixedSpace F))⁻¹ := by
    funext u
    rw [normInf, ENNReal.ofReal_inv_of_pos (abs_pos.2 (det_mulLeft_ne_zero_of_isUnit' u.isUnit))]
  rw [omegaInf_eq, hpt, lintegral_withDensity_eq_lintegral_mul _
    (show Measurable fun u : (mixedSpace F)ˣ => (normInf (u : mixedSpace F))⁻¹ from hd.comp Units.continuous_val.measurable)
    (show Measurable fun u : (mixedSpace F)ˣ => g (u : mixedSpace F) from hg.comp Units.continuous_val.measurable)]
  calc ∫⁻ a, ((fun u : (mixedSpace F)ˣ => (normInf (u : mixedSpace F))⁻¹) *
          fun u : (mixedSpace F)ˣ => g (u : mixedSpace F)) a ∂(Analysis.selfDualInf (F := F)).comap Units.val
      = ∫⁻ x, (fun x => (normInf x)⁻¹ * g x) x
          ∂((Analysis.selfDualInf (F := F)).comap Units.val).map Units.val := (he.lintegral_map (fun x => (normInf x)⁻¹ * g x)).symm
    _ = _ := by
      rw [he.map_comap, range_units_val_mixedSpace, lintegral_indicator measurableSet_isUnit_mixedSpace]

theorem unitFirst_eq : unitFirst F = {y | IsUnit (y 0)} := by
  ext y; simp [unitFirst, isUnit_mixedSpace_iff]

/-- **$|\omega|_\infty$ as an iterated integral** in the chart $(a, c, b)$:
$|\omega|_\infty(S) = \int\mathbf 1[a\in F_\infty^\times]\,|a|_\infty^{-1}\int\!\!\int
\mathbf 1_S\begin{pmatrix} a & b\\ c & (1 + cb)/a\end{pmatrix}db\,dc\,da$. -/
theorem muGaugeInf_apply {S : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hS : MeasurableSet S) :
    muGaugeInf F S = ∫⁻ a, {x : mixedSpace F | IsUnit x}.indicator (fun a => (normInf a)⁻¹ *
      ∫⁻ c, ∫⁻ b, S.indicator (fun _ => 1) !![a, b; c, (1 + c * b) * a⁻¹]
        ∂Analysis.selfDualInf (F := F) ∂Analysis.selfDualInf (F := F)) a ∂Analysis.selfDualInf (F := F) := by
  set μ := Analysis.selfDualInf (F := F)
  have hg : Measurable fun y : Fin 2 → mixedSpace F => (normInf (y 0))⁻¹ :=
    (measurable_normInf.comp (measurable_pi_apply (0 : Fin 2))).inv
  have hh : Measurable fun y : Fin 2 → mixedSpace F => μ (Prod.mk y ⁻¹' (gaugeChart ⁻¹' S)) :=
    measurable_measure_prodMk_left (measurable_gaugeChart hS)
  rw [muGaugeInf, Measure.map_apply measurable_gaugeChart hS, Measure.prod_apply (measurable_gaugeChart hS),
    lintegral_withDensity_eq_lintegral_mul _ hg hh, ← lintegral_indicator measurableSet_unitFirst]
  -- the inner `b`-measure as an integral
  have hb : ∀ y : Fin 2 → mixedSpace F, μ (Prod.mk y ⁻¹' (gaugeChart ⁻¹' S)) =
      ∫⁻ b, S.indicator (fun _ => 1) (gaugeChart (y, b)) ∂μ := by
    intro y
    rw [← lintegral_indicator_one ((measurable_gaugeChart hS).preimage measurable_prodMk_left)]
    rfl
  simp_rw [hb]
  -- split `y = (a, c)`
  set H : (Fin 2 → mixedSpace F) → ℝ≥0∞ := (unitFirst F).indicator
    ((fun y => (normInf (y 0))⁻¹) * fun y => ∫⁻ b, S.indicator (fun _ => 1) (gaugeChart (y, b)) ∂μ) with hH
  have hHm : Measurable H := by
    refine (hg.mul ?_).indicator measurableSet_unitFirst
    have hint : Measurable fun y => ∫⁻ b, S.indicator (fun _ => 1) (gaugeChart (y, b)) ∂μ := by
      simp_rw [← hb]; exact hh
    exact hint
  have hmp := MeasureTheory.measurePreserving_finTwoArrow μ
  rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) H,
    lintegral_prod (fun p => H (MeasurableEquiv.finTwoArrow.symm p)) (hHm.comp (MeasurableEquiv.measurable _)).aemeasurable]
  refine lintegral_congr fun a => ?_
  by_cases ha : IsUnit a
  · rw [Set.indicator_of_mem (show a ∈ {x : mixedSpace F | IsUnit x} from ha), ← lintegral_const_mul' _ _
      (ENNReal.inv_ne_top.2 (hyp_mixedSpace.md_ne_zero a ha))]
    refine lintegral_congr fun c => ?_
    have hy : MeasurableEquiv.finTwoArrow.symm (a, c) ∈ unitFirst F := by
      rw [unitFirst_eq]; exact ha
    simp only [hH, Set.indicator_of_mem hy, Pi.mul_apply]
    rfl
  · rw [Set.indicator_of_notMem (show a ∉ {x : mixedSpace F | IsUnit x} from ha)]
    refine (lintegral_congr fun c => ?_).trans lintegral_zero
    have hy : MeasurableEquiv.finTwoArrow.symm (a, c) ∉ unitFirst F := by
      rw [unitFirst_eq]; exact ha
    simp only [hH, Set.indicator_of_notMem hy]

theorem measurableSet_diagMul {W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hW : MeasurableSet W) :
    MeasurableSet {p : mixedSpace F × Matrix (Fin 2) (Fin 2) (mixedSpace F) | !![1, 0; 0, p.1] * p.2 ∈ W} := by
  refine hW.preimage (Continuous.measurable ?_)
  refine Continuous.matrix_mul ?_ continuous_snd
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first | exact continuous_const | exact continuous_fst

/-- **The archimedean local fibration $\mathrm{GL}_2\to\mathbb G_m$**:
$\int_{F_\infty^\times}|\omega|_\infty\{Y : \sigma(t)Y\in W\}\,d^\times t = \int|\det X|_\infty^{-2}\mathbf 1_W(X)\,dX$
(in the chart $X_{00}\in F_\infty^\times$). -/
theorem lintegral_omegaInf_muGaugeInf {W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hW : MeasurableSet W) :
    ∫⁻ t, muGaugeInf F {Y | !![1, 0; 0, ((t : (mixedSpace F)ˣ) : mixedSpace F)] * Y ∈ W} ∂omegaInf F =
      ∫⁻ v, glDensInf W v ∂muInfVec F (Fin 4) := by
  set μ := Analysis.selfDualInf (F := F)
  have hS : ∀ t : mixedSpace F, MeasurableSet {Y | !![1, 0; 0, t] * Y ∈ W} := fun t =>
    hW.preimage (continuous_const.matrix_mul continuous_id).measurable
  have hGm : Measurable fun t : mixedSpace F => muGaugeInf F {Y | !![1, 0; 0, t] * Y ∈ W} :=
    measurable_measure_prodMk_left (measurableSet_diagMul hW)
  rw [lintegral_omegaInf_units hGm]
  set Fv : (Fin 4 → mixedSpace F) → ℝ≥0∞ := fun v => W.indicator (fun _ => 1) (vecToMat v) with hFv
  have hFm : Measurable Fv := (measurable_const.indicator hW).comp measurable_vecToMat
  have key := GL2Fib.lintegral_gl2_fibration' (μ := μ) hyp_mixedSpace hFm
  have hR : ∀ v, GL2Fib.U.indicator (fun _ => (1 : ℝ≥0∞)) (v 0) *
      GL2Fib.U.indicator (fun d => (normInf d)⁻¹ ^ 2) (v 0 * v 3 - v 1 * v 2) * Fv v = glDensInf W v :=
    fun v => rfl
  simp_rw [hR] at key
  rw [← key]
  refine lintegral_congr fun t => ?_
  congr 1
  funext t
  congr 1
  rw [muGaugeInf_apply (hS t)]
  refine lintegral_congr fun a => ?_
  congr 1
  funext a
  congr 1
  refine lintegral_congr fun c => lintegral_congr fun b => ?_
  simp only [hFv, Set.indicator, Set.mem_ofPred_eq]
  have e : !![1, 0; 0, t] * !![a, b; c, (1 + c * b) * a⁻¹] = vecToMat ![a, b, t * c, t * (1 + c * b) * a⁻¹] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vecToMat, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]
  rw [e]

/-! ### The quaternion side at the archimedean places -/

section QuatArch

variable {a b x y : F} (h : x ^ 2 - a * y ^ 2 = b)

local notation "mE" => mixedEmbedding F

include h in
theorem split_inf : (mE x) ^ 2 - (mE a) * (mE y) ^ 2 = mE b := by
  simp only [← map_pow, ← map_mul, ← map_sub, h]

/-- $\Phi_\infty : \mathbb H[F_\infty,a,b]\to M_2(F_\infty)$, the archimedean component of $\Phi$. -/
def phiInf : QuatInf a b →ₐ[mixedSpace F] Matrix (Fin 2) (Fin 2) (mixedSpace F) :=
  quatMatHom (mE a) (mE b) (mE x) (mE y) (split_inf h)

variable (a x y) in
/-- The matrix of $\Phi_\infty$ in the coordinates $(1, i, j, k)$ resp. $(X_{00}, X_{01}, X_{10}, X_{11})$. -/
def JInf : Matrix (Fin 4) (Fin 4) (mixedSpace F) :=
  !![1, 0, mE x, mE a * mE y; 0, mE a, -(mE a * mE y), -(mE a * mE x); 0, 1, mE y, mE x;
    1, 0, -(mE x), -(mE a * mE y)]

theorem phiInf_symm_coord (c : Fin 4 → mixedSpace F) :
    phiInf h ((quatInfCLE a b).symm c) = vecToMat ((JInf a x y).mulVec c) := by
  have hq : (quatInfCLE a b).symm c = ⟨c 0, c 1, c 2, c 3⟩ := rfl
  rw [phiInf, hq, quatMatHom_apply]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [vecToMat, JInf, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

include h in
theorem det_JInf : (JInf a x y).det = 4 * mE a * mE b := by
  rw [← split_inf h, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, JInf, Fin.succAbove, Matrix.submatrix]
  ring

theorem det_phiInf (q : QuatInf a b) : (phiInf h q).det = nrdInf a b q := det_quatMatHom _ _ _ _ _ q

set_option maxHeartbeats 1000000 in
/-- **The archimedean quaternion factor of the box**: for $W$ inside the chart ($X_{00}$ and $\det X$ units),
$\omega_\infty(\Phi_\infty^{-1}W) = |4ab|_\infty^{-1}\int|\det X|_\infty^{-2}\mathbf 1_W(X)\,dX$. -/
theorem omegaQuatInf_phiInf (ha0 : a ≠ 0) (hb0 : b ≠ 0) {W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))}
    (hW : MeasurableSet W) (hWu : ∀ X ∈ W, IsUnit (X 0 0) ∧ IsUnit X.det) :
    omegaQuatInf a b {u | phiInf h (u : QuatInf a b) ∈ W} =
      (normInf (4 * mE a * mE b))⁻¹ * ∫⁻ c, glDensInf W c ∂muInfVec F (Fin 4) := by
  have hval := isOpenEmbedding_val_quatInf a b
  have he : MeasurableEmbedding (Units.val : (QuatInf a b)ˣ → QuatInf a b) := hval.measurableEmbedding
  have hφc : Continuous (phiInf h : QuatInf a b → Matrix (Fin 2) (Fin 2) (mixedSpace F)) := by
    have h0 := continuous_ire a b
    have h1 := continuous_iimI a b
    have h2 := continuous_iimJ a b
    have h3 := continuous_iimK a b
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [phiInf, quatMatHom_apply]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;> fun_prop
  set A' : Set (QuatInf a b) := phiInf h ⁻¹' W with hA'
  have hA'm : MeasurableSet A' := hφc.measurable hW
  have hAm : MeasurableSet {u : (QuatInf a b)ˣ | phiInf h (u : QuatInf a b) ∈ W} :=
    hA'm.preimage Units.continuous_val.measurable
  -- the density
  set G : QuatInf a b → ℝ≥0∞ := fun q => (normInf (phiInf h q).det)⁻¹ ^ 2 with hG
  have hGm : Measurable G := ((measurable_normInf.comp (hφc.matrix_det).measurable).inv).pow_const 2
  rw [omegaQuatInf, unitsHaar_apply hval (continuous_distribHaarChar_quatInf a b) _ hAm]
  have hdens : ∀ u : (QuatInf a b)ˣ, (distribHaarChar (QuatInf a b) u⁻¹ : ℝ≥0∞) = G u := by
    intro u
    rw [distribHaarChar_quatInf_inv]
    simp only [hG]
    rw [det_phiInf, ← ENNReal.inv_pow]
    rfl
  simp_rw [hdens]
  -- from the units to `QuatInf`
  have hsub : A' ⊆ Set.range (Units.val : (QuatInf a b)ˣ → QuatInf a b) := by
    intro q hq
    have hu : IsUnit (nrdInf a b q) := by rw [← det_phiInf h]; exact (hWu _ hq).2
    obtain ⟨u, hu⟩ := (isUnit_iff_isUnit_nrdInf a b q).2 hu
    exact ⟨u, hu⟩
  have h1 : ∫⁻ u in {u : (QuatInf a b)ˣ | phiInf h (u : QuatInf a b) ∈ W}, G u ∂(quatInfVol a b).comap Units.val =
      ∫⁻ q, A'.indicator G q ∂quatInfVol a b := by
    rw [← lintegral_indicator hAm]
    have : ({u : (QuatInf a b)ˣ | phiInf h (u : QuatInf a b) ∈ W}.indicator fun u => G u) =
        fun u : (QuatInf a b)ˣ => A'.indicator G (u : QuatInf a b) := by
      funext u; simp only [Set.indicator, hA', Set.mem_preimage, Set.mem_ofPred_eq]
    rw [this]
    calc ∫⁻ u, A'.indicator G (u : QuatInf a b) ∂(quatInfVol a b).comap Units.val
        = ∫⁻ q, A'.indicator G q ∂((quatInfVol a b).comap Units.val).map Units.val :=
          (he.lintegral_map (A'.indicator G)).symm
      _ = ∫⁻ q, A'.indicator G q ∂quatInfVol a b := by
          rw [he.map_comap, ← lintegral_indicator he.measurableSet_range]
          refine lintegral_congr fun q => ?_
          by_cases hq : q ∈ A'
          · rw [Set.indicator_of_mem (hsub hq)]
          · simp [Set.indicator_of_notMem hq]
  rw [h1]
  -- to coordinates
  have hcle : Measurable ((quatInfCLE a b).symm : (Fin 4 → mixedSpace F) → QuatInf a b) :=
    (quatInfCLE a b).symm.continuous.measurable
  rw [quatInfVol, lintegral_map ((hGm.indicator hA'm)) hcle]
  set φ : (Fin 4 → mixedSpace F) → ℝ≥0∞ := fun c => W.indicator (fun X => (normInf X.det)⁻¹ ^ 2) (vecToMat c)
    with hφ
  have hφm : Measurable φ :=
    ((((measurable_normInf.comp (continuous_id.matrix_det).measurable).inv).pow_const 2).indicator hW).comp
      measurable_vecToMat
  have hpt : ∀ c, A'.indicator G ((quatInfCLE a b).symm c) = φ ((JInf a x y).mulVec c) := by
    intro c
    simp only [hφ, Set.indicator, hA', Set.mem_preimage, hG, phiInf_symm_coord]
  simp_rw [hpt]
  have hJ : IsUnit (JInf a x y).det := by
    rw [det_JInf h]
    have h4 : IsUnit (4 : mixedSpace F) := by
      rw [show (4 : mixedSpace F) = mE 4 from (map_ofNat (mixedEmbedding F) 4).symm]
      exact (isUnit_iff_ne_zero.2 (by norm_num : (4 : F) ≠ 0)).map (mixedEmbedding F)
    exact (h4.mul ((isUnit_iff_ne_zero.2 ha0).map (mixedEmbedding F))).mul
      ((isUnit_iff_ne_zero.2 hb0).map (mixedEmbedding F))
  have hmv : Measurable (JInf a x y).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [← lintegral_map hφm hmv, map_mulVec_muInfVec _ hJ, lintegral_smul_measure, det_JInf h]
  congr 1
  · rw [normInf, ENNReal.ofReal_inv_of_pos (abs_pos.2 (det_mulLeft_ne_zero_of_isUnit'
      (by rw [← det_JInf h]; exact hJ)))]
  · refine lintegral_congr fun c => ?_
    have hdet : (vecToMat c).det = c 0 * c 3 - c 1 * c 2 := Matrix.det_fin_two_of _ _ _ _
    simp only [hφ, glDensInf]
    by_cases hc : vecToMat c ∈ W
    · obtain ⟨h0, hd⟩ := hWu _ hc
      rw [hdet] at hd
      have h0' : c 0 ∈ {x : mixedSpace F | IsUnit x} := h0
      rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc, Set.indicator_of_mem h0',
        Set.indicator_of_mem (show c 0 * c 3 - c 1 * c 2 ∈ {x : mixedSpace F | IsUnit x} from hd), hdet]
      ring
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, mul_zero]

end QuatArch

end QuadFormsKB.Tamagawa.Measure.Weil
