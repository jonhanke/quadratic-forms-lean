import QuadFormsKB.Tamagawa.Measure.LerayComplex
import QuadFormsKB.Tamagawa.Measure.LerayUnimodular

/-!
# Unimodularity of the complex Leray measure

The complex analogue of `LerayUnimodular.lean` (the two gaps left open there):

* **The Jacobian of the action on complex coefficient space** (`det_act`): $\det_{\mathbb C}(c \mapsto c\cdot M) =
  (\det M)^{n+1}$ for every $M \in M_n(\mathbb C)$, and hence the real Jacobian (the action as a real-linear map of
  $\mathbb C^{n(n+1)/2} = \mathbb R^{n(n+1)}$) is $|\det M|^{2(n+1)} = |\det M|_{\mathbb C}^{n+1}$
  (`det_restrictScalars_act`). Same proof as at the real places (multiplicativity, diagonal matrices, transvections).
* **Right invariance of $\mu_Q$ on $SO(Q)(\mathbb C)$** (`isMulRightInvariant_lerayMeasureC`): $SO(Q)(\mathbb C)$ is
  unimodular. Right translation by $h$ moves the regions $\{\operatorname{Re}\det X > 0, \Phi_Q(X) \in E\}$ to the
  regions over $E\cdot h$, which have the same volume; the fibration identity on regions (`lintegral_regionC`) and
  averaging over the shrinking sets $\bar B_\varepsilon(c_Q)\cdot h$ give $\int f(gh)\,d\mu_Q = \int f\,d\mu_Q$.
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayComplex

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ

/-! ### The Jacobian of the action on complex coefficient space -/

theorem det_act_mul (M N : 𝕄) :
    LinearMap.det (act (M * N)) = LinearMap.det (act M) * LinearMap.det (act N) := by
  rw [act_mul_eq, LinearMap.det_comp, mul_comm]

theorem det_act_one : LinearMap.det (act (1 : 𝕄)) = 1 := by
  rw [act_one_eq, LinearMap.det_id]

theorem act_diagonal (m : Fin n → ℂ) :
    act (diagonal m) = Matrix.toLin' (diagonal fun p : UIdx n => m p.1.1 * m p.1.2) := by
  refine LinearMap.ext fun c => funext fun p => ?_
  rw [act_apply, Matrix.toLin'_apply, mulVec_diagonal, diagonal_transpose]
  simp only [wtU, diagonal_mul, mul_diagonal]
  have h := congrFun (wtU_symOf c) p
  simp only [wtU] at h
  rw [← h]; ring

theorem prod_UIdx (m : Fin n → ℂ) : ∏ p : UIdx n, m p.1.1 * m p.1.2 = (∏ i, m i) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Equiv.prod_comp (eU n), Fintype.prod_sum_type, Fintype.prod_sum_type]
    have h1 : ∀ a, m (eU n (.inl a)).1.1 * m (eU n (.inl a)).1.2 = m 0 * m 0 := by intro a; simp [eU]
    have h2 : ∀ j, m (eU n (.inr (.inl j))).1.1 * m (eU n (.inr (.inl j))).1.2 = m 0 * m j.succ := by
      intro j; simp [eU]
    have h3 : ∀ p, m (eU n (.inr (.inr p))).1.1 * m (eU n (.inr (.inr p))).1.2 =
        (fun i : Fin n => m i.succ) p.1.1 * (fun i : Fin n => m i.succ) p.1.2 := by intro p; simp [eU]
    simp only [h1, h2, h3, ih (fun i => m i.succ), Finset.univ_unique, Finset.card_singleton,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fin.prod_univ_succ]
    ring

theorem det_act_diagonal (m : Fin n → ℂ) : LinearMap.det (act (diagonal m)) = (∏ i, m i) ^ (n + 1) := by
  rw [act_diagonal, LinearMap.det_toLin', det_diagonal, prod_UIdx]

theorem det_act_transvection {i j : Fin n} (hij : i ≠ j) (c : ℂ) :
    LinearMap.det (act (transvection i j c)) = 1 := by
  set d : Fin n → ℂ := Function.update 1 i 2
  have hconj : diagonal d * transvection i j c = transvection i j (2 * c) * diagonal d := by
    ext a b
    rw [diagonal_mul, mul_diagonal]
    simp only [transvection, Matrix.add_apply, single_apply, Matrix.one_apply, d]
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = j
      · subst hb; simp [hij, Function.update_of_ne hij.symm]
      · by_cases hab : a = b
        · subst hab; simp [Ne.symm hb]
        · simp [hab, Ne.symm hab, Ne.symm hb]
    · by_cases hab : a = b
      · subst hab; simp [ha, Ne.symm ha]
      · simp [ha, hab, Ne.symm ha]
  have hd : LinearMap.det (act (diagonal d)) ≠ 0 := by
    rw [det_act_diagonal]
    refine pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
    by_cases hk : k = i
    · subst hk; simp [d]
    · simp [d, Function.update_of_ne hk]
  have h1 := congrArg (fun M => LinearMap.det (act M)) hconj
  simp only [det_act_mul] at h1
  have h2 : LinearMap.det (act (transvection i j c)) = LinearMap.det (act (transvection i j (2 * c))) := by
    have := h1
    rw [mul_comm (LinearMap.det (act (transvection i j (2 * c))))] at this
    exact mul_left_cancel₀ hd this
  have h3 : LinearMap.det (act (transvection i j (2 * c))) = LinearMap.det (act (transvection i j c)) ^ 2 := by
    rw [two_mul, ← transvection_mul_transvection_same i j hij, det_act_mul, sq]
  have h4 : LinearMap.det (act (transvection i j c)) ≠ 0 := by
    have := congrArg (fun M => LinearMap.det (act M)) (transvection_mul_transvection_same i j hij c (-c))
    simp only [det_act_mul, add_neg_cancel, transvection_zero, det_act_one] at this
    exact left_ne_zero_of_mul_eq_one this
  rw [h2] at h3 h4
  have h5 := h3
  rw [sq] at h5
  have : LinearMap.det (act (transvection i j (2 * c))) = 1 :=
    mul_left_cancel₀ h4 (h5.symm.trans (mul_one _).symm)
  rw [h2, this]

theorem det_act_list_transvec (L : List (TransvectionStruct (Fin n) ℂ)) :
    LinearMap.det (act (L.map TransvectionStruct.toMatrix).prod) = 1 := by
  induction L with
  | nil => simp [det_act_one]
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, det_act_mul, ih, mul_one]
    exact det_act_transvection t.hij t.c

/-- **The Jacobian of the action on complex coefficient space**: $\det_{\mathbb C}(c \mapsto c \cdot M) =
(\det M)^{n+1}$. -/
@[kb "weil1982" "§2.4 (Jacobian of S ↦ MᵀSM on symmetric matrices) [unverified]"]
theorem det_act (M : 𝕄) : LinearMap.det (act M) = M.det ^ (n + 1) := by
  obtain ⟨L, L', D, rfl⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  rw [det_act_mul, det_act_mul, det_act_list_transvec, det_act_list_transvec, det_act_diagonal, det_mul, det_mul,
    det_diagonal]
  have hL : ∀ L : List (TransvectionStruct (Fin n) ℂ), (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
    intro L
    induction L with
    | nil => simp
    | cons t L ih => rw [List.map_cons, List.prod_cons, det_mul, ih, mul_one, TransvectionStruct.det]
  rw [hL, hL]; ring

/-- **The real Jacobian of the action**: as a real-linear map of $\mathbb C^{n(n+1)/2} = \mathbb R^{n(n+1)}$,
$\det_{\mathbb R}(c \mapsto c\cdot M) = |\det M|^{2(n+1)} = |\det M|_{\mathbb C}^{n+1}$. -/
@[kb "weil1982" "§2.4 (Jacobian of S ↦ MᵀSM, complex places) [unverified]"]
theorem det_restrictScalars_act (M : 𝕄) :
    LinearMap.det ((act M).restrictScalars ℝ) = Complex.normSq M.det ^ (n + 1) := by
  rw [det_restrictScalars_complex, det_act, map_pow]

/-- On $SO(Q)(\mathbb C)$ the action on coefficient space has real Jacobian $1$. -/
theorem det_restrictScalars_act_mat {Q : QuadForm ℂ n} (h : ArchSOC Q) :
    LinearMap.det ((act (ArchSOC.mat Q h)).restrictScalars ℝ) = 1 := by
  rw [det_restrictScalars_act, ArchSOC.det_mat, map_one, one_pow]

/-! ### Right translation by $h \in SO(Q)(\mathbb C)$ -/

variable {Q : QuadForm ℂ n} (D : DiagC Q)

/-- Right multiplication by $h$ in column coordinates, as a measurable equivalence. -/
def rmulME (h : ArchSOC Q) : (Fin n → Fin n → ℂ) ≃ᵐ (Fin n → Fin n → ℂ) :=
  linMEquiv (rmulL (ArchSOC.mat Q h)) (rmulL (ArchSOC.mat Q h⁻¹))
    (rmulL_rmulL (ArchSOC.mat_inv_mul h)) (rmulL_rmulL (ArchSOC.mat_mul_inv h))

theorem coe_rmulME (h : ArchSOC Q) : ⇑(rmulME h) = ⇑(rmulL (ArchSOC.mat Q h)) := rfl

/-- The homeomorphism underlying `rmulME`. -/
def rmulHomeo (h : ArchSOC Q) : (Fin n → Fin n → ℂ) ≃ₜ (Fin n → Fin n → ℂ) :=
  (LinearEquiv.ofLinearMap (rmulL (ArchSOC.mat Q h)) (rmulL (ArchSOC.mat Q h⁻¹))
    (LinearMap.ext (rmulL_rmulL (ArchSOC.mat_inv_mul h)))
    (LinearMap.ext (rmulL_rmulL (ArchSOC.mat_mul_inv h)))).toContinuousLinearEquiv.toHomeomorph

theorem coe_rmulHomeo (h : ArchSOC Q) : ⇑(rmulHomeo h) = ⇑(rmulL (ArchSOC.mat Q h)) := rfl

theorem measurePreserving_rmulME (h : ArchSOC Q) : MeasurePreserving (rmulME h) volume volume := by
  refine ⟨(rmulME h).measurable, ?_⟩
  have hdet : LinearMap.det (rmulL (ArchSOC.mat Q h)) = 1 := by
    rw [det_rmulL, ArchSOC.det_mat, one_pow]
  rw [coe_rmulME, map_clm_addHaar volume _ (by rw [hdet]; exact one_ne_zero), hdet]
  simp

theorem act_mat_mat_inv' (h : ArchSOC Q) (c : UIdx n → ℂ) :
    act (ArchSOC.mat Q h) (act (ArchSOC.mat Q h⁻¹) c) = c := by
  rw [← act_mul, ArchSOC.mat_inv_mul, act_one]

theorem act_mat_inv_mat' (h : ArchSOC Q) (c : UIdx n → ℂ) :
    act (ArchSOC.mat Q h⁻¹) (act (ArchSOC.mat Q h) c) = c := by
  rw [← act_mul, ArchSOC.mat_mul_inv, act_one]

/-- The action of $h \in SO(Q)(\mathbb C)$ on coefficient space, as a measurable equivalence. -/
def actSO (h : ArchSOC Q) : (UIdx n → ℂ) ≃ᵐ (UIdx n → ℂ) :=
  linMEquiv (act (ArchSOC.mat Q h)) (act (ArchSOC.mat Q h⁻¹)) (act_mat_mat_inv' h) (act_mat_inv_mat' h)

theorem coe_actSO (h : ArchSOC Q) : ⇑(actSO h) = ⇑(act (ArchSOC.mat Q h)) := rfl

/-- **Right translation moves regions along the action**. -/
theorem image_rmulME_regionC (h : ArchSOC Q) (E : Set (UIdx n → ℂ)) :
    rmulME h '' regionC Q E = regionC Q (actSO h '' E) := by
  set M := ArchSOC.mat Q h
  have hcol : ∀ X, rmulME h X = cols (ofCols X * M) := fun X => by
    rw [coe_rmulME, cols_mul_right, cols_ofCols]
  ext Y
  constructor
  · rintro ⟨X, ⟨hX1, hX2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hcol, ofCols_cols, det_mul, ArchSOC.det_mat, mul_one]; exact hX1
    · rw [hcol, ofCols_cols, phi_mul, coe_actSO]
      exact ⟨_, hX2, rfl⟩
  · rintro ⟨hY1, c, hc, hcY⟩
    refine ⟨cols (ofCols Y * ArchSOC.mat Q h⁻¹), ⟨?_, ?_⟩, ?_⟩
    · rw [ofCols_cols, det_mul, ArchSOC.det_mat, mul_one]; exact hY1
    · rw [ofCols_cols, phi_mul, ← hcY, coe_actSO, ← act_mul, ArchSOC.mat_mul_inv, act_one]
      exact hc
    · rw [hcol, ofCols_cols, Matrix.mul_assoc, ArchSOC.mat_inv_mul, Matrix.mul_one, cols_ofCols]

theorem actSO_coeffUC (h : ArchSOC Q) : actSO h (coeffUC Q) = coeffUC Q := by
  rw [coe_actSO, ← phi_one, ← phi_mul, Matrix.one_mul,
    show ArchSOC.mat Q h = ArchSOC.mat Q h * 1 from (Matrix.mul_one _).symm,
    phi_of_isometry Q (ArchSOC.isometry Q h)]

theorem volume_image_actSO (h : ArchSOC Q) (s : Set (UIdx n → ℂ)) : volume (actSO h '' s) = volume s := by
  rw [coe_actSO, show ⇑(act (ArchSOC.mat Q h)) = ⇑((act (ArchSOC.mat Q h)).restrictScalars ℝ) from rfl,
    addHaar_image_linearMap, det_restrictScalars_act_mat, abs_one, ENNReal.ofReal_one, one_mul]

/-- **The transported balls shrink to $c_Q$**. -/
theorem exists_image_actSO_subset (h : ArchSOC Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > 0, actSO h '' Metric.closedBall (coeffUC Q) ε ⊆ Metric.closedBall (coeffUC Q) (C * ε) := by
  set L := LinearMap.toContinuousLinearMap (act (ArchSOC.mat Q h))
  refine ⟨‖L‖ + 1, by positivity, fun ε hε => ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  rw [Metric.mem_closedBall] at hc ⊢
  have hL : ∀ x, L x = act (ArchSOC.mat Q h) x := fun x => rfl
  calc dist (actSO h c) (coeffUC Q) = ‖L (c - coeffUC Q)‖ := by
        rw [dist_eq_norm, map_sub, hL, hL, ← coe_actSO, actSO_coeffUC]
    _ ≤ ‖L‖ * ‖c - coeffUC Q‖ := L.le_opNorm _
    _ ≤ (‖L‖ + 1) * ε := by
        rw [← dist_eq_norm]
        exact mul_le_mul (by linarith) hc dist_nonneg (by positivity)

/-- The fibration identity on regions over any measurable $E \subseteq U_0$, for continuous compactly supported
$f \ge 0$. -/
theorem lintegral_regionC_ofReal {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ X, 0 ≤ f X) {E : Set (UIdx n → ℂ)} (hE : MeasurableSet E) (hEU : E ⊆ U0 D) :
    ∫⁻ X in regionC Q E, ENNReal.ofReal (f X) =
      ∫⁻ c in E, ENNReal.ofReal (fibreInt D f (sec D c) * rho D c) := by
  rw [lintegral_regionC D (φ := fun X => ENNReal.ofReal (f X))
    (ENNReal.measurable_ofReal.comp hf.measurable) hE hEU]
  refine setLIntegral_congr_fun hE fun c _ => ?_
  have hinner : ∫⁻ g, ENNReal.ofReal (f (chart D (g, sec D c))) ∂lerayDC D =
      ENNReal.ofReal (fibreInt D f (sec D c)) := by
    rw [fibreInt, ofReal_integral_eq_lintegral_ofReal]
    · exact (hf.comp ((continuous_chart D).comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hasCompactSupport_fibre D hfc _)
    · exact Filter.Eventually.of_forall fun g => hf0 _
  have h0 : 0 ≤ fibreInt D f (sec D c) := integral_nonneg fun g => hf0 _
  rw [hinner, mul_comm, ← ENNReal.ofReal_mul h0]

/-- **Right translation does not change integrals against the complex Leray measure**, for compactly supported
continuous $f \ge 0$. -/
theorem integral_mul_right_lerayDC {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ X, 0 ≤ f X) (h : ArchSOC Q) :
    ∫ g, f (cols (ArchSOC.mat Q (g * h))) ∂lerayDC D = ∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
  set fh : (Fin n → Fin n → ℂ) → ℝ := f ∘ rmulHomeo h
  have hfh : Continuous fh := hf.comp (rmulHomeo h).continuous
  have hfhc : HasCompactSupport fh := hfc.comp_isClosedEmbedding (rmulHomeo h).isClosedEmbedding
  have hfh0 : ∀ X, 0 ≤ fh X := fun X => hf0 _
  have hL : ∀ g : ArchSOC Q, f (cols (ArchSOC.mat Q (g * h))) = fh (cols (ArchSOC.mat Q g)) := fun g => by
    simp only [fh, Function.comp_apply, ArchSOC.mat_mul, cols_mul_right, coe_rmulHomeo]
  simp_rw [hL]
  have hA := tendsto_lerayApproxC D hfh hfhc
  obtain ⟨C, hC, hSsub⟩ := exists_image_actSO_subset h
  set S : ℝ → Set (UIdx n → ℂ) := fun ε => actSO h '' Metric.closedBall (coeffUC Q) ε
  set H : (UIdx n → ℂ) → ℝ := fun c => fibreInt D f (sec D c) * rho D c
  have hHc : ContinuousOn H (U0 D) :=
    ((continuous_fibreInt D hf hfc).comp_continuousOn (continuousOn_sec D)).mul (continuousOn_rho D)
  have hH0 : ∀ c ∈ U0 D, 0 ≤ H c := fun c _ =>
    mul_nonneg (integral_nonneg fun g => hf0 _) (rho_nonneg D c)
  have hSm : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (actSO h).measurableSet_image.mpr Metric.isClosed_closedBall.measurableSet
  have hvol : ∀ ε, volume (S ε) = volume (Metric.closedBall (coeffUC Q) ε) := fun ε => volume_image_actSO h _
  have hB := LerayReal.tendsto_avg_of_subset volume hC hSsub hSm
    (fun ε hε => by rw [hvol]; exact Metric.measure_closedBall_pos volume _ hε)
    (fun ε hε => by rw [hvol]; exact measure_closedBall_lt_top.ne)
    (isOpen_U0 D) (coeffUC_mem_U0 D) hHc hH0
  have hH1 : H (coeffUC Q) = ∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
    simp only [H, rho_coeffUC, mul_one, sec_coeffUC, fibreInt, chart, SliceB.mat_one]
  rw [hH1] at hB
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ U0 D := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (isOpen_U0 D) _ (coeffUC_mem_U0 D)
    filter_upwards [Ioo_mem_nhdsGT (show 0 < δ / (2 * C) by positivity)] with ε hε
    refine (hSsub ε hε.1).trans ((Metric.closedBall_subset_ball ?_).trans hsub)
    have := hε.2
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  refine tendsto_nhds_unique (hA.congr' ?_) hB
  filter_upwards [hev] with ε hε
  rw [lerayApproxC, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => hfh0 X)
      hfh.aestronglyMeasurable, lerayRegionC, ← hvol ε]
  congr 2
  have h1 : ∫⁻ X in regionC Q (Metric.closedBall (coeffUC Q) ε), ENNReal.ofReal (fh X) =
      ∫⁻ Y in rmulME h '' regionC Q (Metric.closedBall (coeffUC Q) ε), ENNReal.ofReal (f Y) :=
    (measurePreserving_rmulME h).setLIntegral_comp_emb (rmulME h).measurableEmbedding
      (fun Y => ENNReal.ofReal (f Y)) _
  rw [h1, image_rmulME_regionC, lintegral_regionC_ofReal D hf hfc hf0 (hSm ε) hε]

instance isMulRightInvariant_lerayDC : (lerayDC D).IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  have hμ := isMulLeftInvariant_eq_smul ((lerayDC D).map (· * h)) (lerayDC D)
  set k := haarScalarFactor ((lerayDC D).map (· * h)) (lerayDC D)
  have hmeas : Measurable fun g : ArchSOC Q => g * h := measurable_mul_const h
  have h1 : ∫ g, bump n (cols (ArchSOC.mat Q g)) ∂((lerayDC D).map (· * h)) =
      ∫ g, bump n (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
    rw [integral_map (f := fun g => bump n (cols (ArchSOC.mat Q g))) hmeas.aemeasurable
      (continuous_bump.comp (continuous_cols.comp (ArchSOC.continuous_mat Q))).aestronglyMeasurable]
    exact integral_mul_right_lerayDC D continuous_bump hasCompactSupport_bump bump_nonneg h
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h1
  have hpos := integral_bump_pos D
  have hk : (k : ℝ) = 1 := mul_right_cancel₀ hpos.ne' (h1.trans (one_mul _).symm)
  rw [hμ, show k = 1 from NNReal.coe_eq_one.mp hk, one_smul]

/-- **Unimodularity at the complex places**: the Leray measure $\mu_Q$ on $SO(Q)(\mathbb C)$ is right invariant,
hence bi-invariant. -/
@[kb "weil1982" "§2.2 (gauge forms on unimodular groups) [unverified]"]
theorem isMulRightInvariant_lerayMeasureC (hQ : gramDetC Q ≠ 0) : (lerayMeasureC Q hQ).IsMulRightInvariant :=
  isMulRightInvariant_lerayDC _

/-- **Right translation by $h$ preserves $\mu_Q$** at a complex place. -/
@[kb "weil1982" "§2.2 (gauge forms on unimodular groups) [unverified]"]
theorem map_mul_right_lerayMeasureC (hQ : gramDetC Q ≠ 0) (h : ArchSOC Q) :
    (lerayMeasureC Q hQ).map (· * h) = lerayMeasureC Q hQ := by
  have := isMulRightInvariant_lerayMeasureC hQ
  exact map_mul_right_eq_self _ h

end QuadFormsKB.Tamagawa.Measure.LerayComplex
