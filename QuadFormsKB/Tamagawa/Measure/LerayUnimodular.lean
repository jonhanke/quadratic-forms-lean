import QuadFormsKB.Tamagawa.Measure.LerayReal

/-!
# Unimodularity of the real Leray measure

$SO(Q)(\mathbb R)$ is unimodular for every nondegenerate real form $Q$ (any signature). We prove that the Leray
measure $\mu_Q$ (`LerayReal.lerayMeasure`) is also **right** invariant (`isMulRightInvariant_lerayMeasure`), with no Lie
theory, from two facts:

* **The Jacobian of the action on coefficient space**: $\det(c \mapsto c\cdot M) = (\det M)^{n+1}$ for every
  $M \in M_n(\mathbb R)$ (`det_act`; the action $S \mapsto M^{\mathsf T}SM$ on symmetric matrices). Proof: the map
  $M \mapsto \det(\text{act}\,M)$ is multiplicative; on diagonal matrices it is $\prod_{i \le j}m_im_j =
  (\prod_i m_i)^{n+1}$; on a transvection $T$ it is $1$, because $T$ is conjugate (by a diagonal matrix) to $T^2$; and
  every matrix is a product of transvections and a diagonal matrix (Mathlib's
  `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`). In particular $|\det(\text{act}\,h)| = 1$ on
  $SO(Q)$: the fibre map $c \mapsto g^{\mathsf T}cg$ has determinant one for $g \in O(Q)$.
* **The Leray limit along transported balls**: right translation by $h \in SO(Q)(\mathbb R)$ is $X \mapsto Xh$ on
  $M_n(\mathbb R)$ (Lebesgue-measure preserving, $\det$-preserving), and it moves the Leray regions over balls
  $B_\varepsilon(c_Q)$ to the regions over $h \cdot B_\varepsilon(c_Q)$, which have the same volume and shrink to $c_Q$.
  The fibration identity (`lerayFibration`) and averaging over these sets give
  $\int f(gh)\,d\mu_Q(g) = \int f\,d\mu_Q$ for compactly supported continuous $f \ge 0$.
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.ArchSOMeasure

variable {n : ℕ}

/-! ### The Jacobian of the action on coefficient space -/

theorem det_act_mul (M N : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (act (M * N)) = LinearMap.det (act M) * LinearMap.det (act N) := by
  rw [act_mul_eq, LinearMap.det_comp, mul_comm]

theorem det_act_one : LinearMap.det (act (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
  rw [act_one_eq, LinearMap.det_id]

theorem act_diagonal (m : Fin n → ℝ) :
    act (diagonal m) = Matrix.toLin' (diagonal fun p : UIdx n => m p.1.1 * m p.1.2) := by
  refine LinearMap.ext fun c => funext fun p => ?_
  rw [act_apply, Matrix.toLin'_apply, mulVec_diagonal, diagonal_transpose]
  simp only [wtU, diagonal_mul, mul_diagonal]
  have h := congrFun (wtU_symOf c) p
  simp only [wtU] at h
  rw [← h]; ring

theorem prod_UIdx (m : Fin n → ℝ) : ∏ p : UIdx n, m p.1.1 * m p.1.2 = (∏ i, m i) ^ (n + 1) := by
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

theorem det_act_diagonal (m : Fin n → ℝ) : LinearMap.det (act (diagonal m)) = (∏ i, m i) ^ (n + 1) := by
  rw [act_diagonal, LinearMap.det_toLin', det_diagonal, prod_UIdx]

theorem det_act_transvection {i j : Fin n} (hij : i ≠ j) (c : ℝ) :
    LinearMap.det (act (transvection i j c)) = 1 := by
  set d : Fin n → ℝ := Function.update 1 i 2
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
  have : LinearMap.det (act (transvection i j (2 * c))) = 1 := by
    have := mul_left_cancel₀ h4 (h5.symm.trans (mul_one _).symm)
    exact this
  rw [h2, this]

theorem det_act_list_transvec (L : List (TransvectionStruct (Fin n) ℝ)) :
    LinearMap.det (act (L.map TransvectionStruct.toMatrix).prod) = 1 := by
  induction L with
  | nil => simp [det_act_one]
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, det_act_mul, ih, mul_one]
    exact det_act_transvection t.hij t.c

/-- **The Jacobian of the action on coefficient space**: $\det(c \mapsto c \cdot M) = (\det M)^{n+1}$. -/
@[kb "weil1982" "§2.4 (Jacobian of S ↦ MᵀSM on symmetric matrices) [unverified]"]
theorem det_act (M : Matrix (Fin n) (Fin n) ℝ) : LinearMap.det (act M) = M.det ^ (n + 1) := by
  obtain ⟨L, L', D, rfl⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  rw [det_act_mul, det_act_mul, det_act_list_transvec, det_act_list_transvec, det_act_diagonal, det_mul, det_mul,
    det_diagonal]
  have hL : ∀ L : List (TransvectionStruct (Fin n) ℝ), (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
    intro L
    induction L with
    | nil => simp
    | cons t L ih => rw [List.map_cons, List.prod_cons, det_mul, ih, mul_one, TransvectionStruct.det]
  rw [hL, hL]; ring


/-! ### Averages over shrinking sets -/

/-- **Averages over shrinking sets**: if $S_\varepsilon \subseteq \bar B_{C\varepsilon}(c_0)$ has finite positive mass,
and $G \ge 0$ is continuous on an open $U \ni c_0$, then $\frac{1}{\mu(S_\varepsilon)}\int_{S_\varepsilon}G\,d\mu
\to G(c_0)$. -/
theorem tendsto_avg_of_subset {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) {c₀ : E} {S : ℝ → Set E} {C : ℝ} (hC : 0 < C)
    (hS : ∀ ε > 0, S ε ⊆ Metric.closedBall c₀ (C * ε)) (hSm : ∀ ε, MeasurableSet (S ε))
    (hpos : ∀ ε > 0, 0 < μ (S ε)) (hfin : ∀ ε > 0, μ (S ε) ≠ ∞) {U : Set E} (hU : IsOpen U) (hc : c₀ ∈ U)
    {G : E → ℝ} (hGc : ContinuousOn G U) (hG0 : ∀ t ∈ U, 0 ≤ G t) :
    Tendsto (fun ε => (∫⁻ t in S ε, ENNReal.ofReal (G t) ∂μ).toReal / (μ (S ε)).toReal) (𝓝[>] 0)
      (𝓝 (G c₀)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  have hcont : ContinuousAt G c₀ := hGc.continuousAt (hU.mem_nhds hc)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hcont (η / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.isOpen_iff.mp hU c₀ hc
  refine ⟨min δ1 δ2 / C, by positivity, fun {ε} hε hεd => ?_⟩
  have hε : 0 < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hε, lt_div_iff₀ hC] at hεd
  set B := S ε
  have hsub : ∀ t ∈ B, dist t c₀ < min δ1 δ2 := fun t ht =>
    lt_of_le_of_lt (Metric.mem_closedBall.mp (hS ε hε ht)) (by linarith)
  have hU' : ∀ t ∈ B, t ∈ U := fun t ht =>
    h2 (Metric.mem_ball.mpr ((hsub t ht).trans_le (min_le_right _ _)))
  have hclose : ∀ t ∈ B, |G t - G c₀| < η / 2 := fun t ht => by
    rw [← Real.dist_eq]; exact h1 ((hsub t ht).trans_le (min_le_left _ _))
  have hmeasB : MeasurableSet B := hSm ε
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

/-! ### The fibration identity over general sets near $c_Q$ -/

variable {Q : QuadForm ℝ n} (D : Diag Q)

/-- **The region over $E$**: $\{X : \det X > 0,\ \Phi_Q(X) \in E\}$ (column coordinates). -/
def regionR (Q : QuadForm ℝ n) (E : Set (UIdx n → ℝ)) : Set (Fin n → Fin n → ℝ) :=
  {X | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ E}

/-- The fibration identity on the region over any measurable $E \subseteq U = \beta(B)$, for $f \ge 0$. -/
theorem lintegral_regionR {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ X, 0 ≤ f X) {E : Set (UIdx n → ℝ)} (hE : MeasurableSet E) (hEU : E ⊆ range (beta D)) :
    ∫⁻ X in regionR Q E, ENNReal.ofReal (f X) =
      ∫⁻ c in E, ENNReal.ofReal (fibreInt D f (sec D c) * rho D c) := by
  have hT : MeasurableSet (beta D ⁻¹' E) := (continuous_beta D).measurable hE
  rw [regionR, ← image_chart D hEU,
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
  rw [setLIntegral_kappa0 D hE (ψ := fun b => ENNReal.ofReal (fibreInt D f b))
      (ENNReal.continuous_ofReal.comp (continuous_fibreInt D hf hfc)).measurable,
    inter_eq_left.mpr hEU]
  refine setLIntegral_congr_fun hE fun c _ => ?_
  have h0 : 0 ≤ fibreInt D f (sec D c) := integral_nonneg fun g => hf0 _
  rw [mul_comm, ← ENNReal.ofReal_mul h0]

/-! ### Right translation by $h \in SO(Q)(\mathbb R)$ -/

theorem rmulL_rmulL {M M' : Matrix (Fin n) (Fin n) ℝ} (h : M' * M = 1) (X : Fin n → Fin n → ℝ) :
    rmulL M (rmulL M' X) = X := by
  rw [← cols_ofCols X, ← cols_mul_right, ← cols_mul_right, Matrix.mul_assoc, h, Matrix.mul_one]

theorem ArchSOInst.mat_one (Q : QuadForm ℝ n) : ArchSOInst.mat Q 1 = 1 := by simp [ArchSOInst.mat]

theorem ArchSOInst.mat_inv_mul (Q : QuadForm ℝ n) (g : ArchSO Q) : ArchSOInst.mat Q g⁻¹ * ArchSOInst.mat Q g = 1 := by
  rw [← ArchSOInst.mat_mul, inv_mul_cancel, ArchSOInst.mat_one]

theorem ArchSOInst.mat_mul_inv (Q : QuadForm ℝ n) (g : ArchSO Q) : ArchSOInst.mat Q g * ArchSOInst.mat Q g⁻¹ = 1 := by
  rw [← ArchSOInst.mat_mul, mul_inv_cancel, ArchSOInst.mat_one]

/-- Right multiplication by $h$ in column coordinates, as a continuous linear equivalence. -/
def rmulCLE (h : ArchSO Q) : (Fin n → Fin n → ℝ) ≃L[ℝ] (Fin n → Fin n → ℝ) :=
  (LinearEquiv.ofLinear (rmulL (ArchSOInst.mat Q h)) (rmulL (ArchSOInst.mat Q h⁻¹))
    (LinearMap.ext (rmulL_rmulL (ArchSOInst.mat_inv_mul Q h)))
    (LinearMap.ext (rmulL_rmulL (ArchSOInst.mat_mul_inv Q h)))).toContinuousLinearEquiv

/-- Right multiplication by $h$ in column coordinates, as a measurable equivalence. -/
def rmulME (h : ArchSO Q) : (Fin n → Fin n → ℝ) ≃ᵐ (Fin n → Fin n → ℝ) := (rmulCLE h).toHomeomorph.toMeasurableEquiv

theorem coe_rmulME (h : ArchSO Q) : ⇑(rmulME h) = ⇑(rmulL (ArchSOInst.mat Q h)) := rfl

theorem measurePreserving_rmulME (h : ArchSO Q) : MeasurePreserving (rmulME h) volume volume := by
  refine ⟨(rmulME h).measurable, ?_⟩
  have hdet : LinearMap.det (rmulL (ArchSOInst.mat Q h)) = 1 := by
    rw [det_rmulL, ArchSOInst.det_mat, one_pow]
  rw [coe_rmulME, map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact one_ne_zero), hdet]
  simp

theorem act_mat_mat_inv (h : ArchSO Q) (c : UIdx n → ℝ) :
    act (ArchSOInst.mat Q h) (act (ArchSOInst.mat Q h⁻¹) c) = c := by
  rw [← act_mul, ArchSOInst.mat_inv_mul, act_one]

theorem act_mat_inv_mat (h : ArchSO Q) (c : UIdx n → ℝ) :
    act (ArchSOInst.mat Q h⁻¹) (act (ArchSOInst.mat Q h) c) = c := by
  rw [← act_mul, ArchSOInst.mat_mul_inv, act_one]

/-- The action of $h$ on coefficient space, as a measurable equivalence. -/
def actME (h : ArchSO Q) : (UIdx n → ℝ) ≃ᵐ (UIdx n → ℝ) :=
  (LinearEquiv.ofLinear (act (ArchSOInst.mat Q h)) (act (ArchSOInst.mat Q h⁻¹))
    (LinearMap.ext (act_mat_mat_inv h)) (LinearMap.ext (act_mat_inv_mat h))).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem coe_actME (h : ArchSO Q) : ⇑(actME h) = ⇑(act (ArchSOInst.mat Q h)) := rfl

/-- **Right translation moves regions along the action**: $\{X : \det X > 0, \Phi_Q(X) \in E\}\cdot h =
\{Y : \det Y > 0, \Phi_Q(Y) \in E\cdot h\}$. -/
theorem image_rmulME_regionR (h : ArchSO Q) (E : Set (UIdx n → ℝ)) :
    rmulME h '' regionR Q E = regionR Q (actME h '' E) := by
  set M := ArchSOInst.mat Q h
  have hcol : ∀ X, rmulME h X = cols (ofCols X * M) := fun X => by
    rw [coe_rmulME, cols_mul_right, cols_ofCols]
  have hdet : ∀ N : Matrix (Fin n) (Fin n) ℝ, (Matrix.of (cols N)).det = N.det := fun N => by
    rw [← det_ofCols]; rfl
  ext Y
  constructor
  · rintro ⟨X, ⟨hX1, hX2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hcol, hdet, det_mul, ArchSOInst.det_mat, mul_one, det_ofCols]; exact hX1
    · rw [hcol, ← phi_eq_pullCoeff, phi_mul, coe_actME]
      refine ⟨_, hX2, ?_⟩
      rw [phi_eq_pullCoeff, cols_ofCols]
  · rintro ⟨hY1, c, hc, hcY⟩
    refine ⟨cols (ofCols Y * ArchSOInst.mat Q h⁻¹), ⟨?_, ?_⟩, ?_⟩
    · rw [hdet, det_mul, ArchSOInst.det_mat, mul_one, det_ofCols]; exact hY1
    · rw [← phi_eq_pullCoeff, phi_mul, phi_eq_pullCoeff, cols_ofCols, ← hcY, coe_actME, ← act_mul,
        ArchSOInst.mat_mul_inv, act_one]
      exact hc
    · rw [hcol, show ofCols (cols (ofCols Y * ArchSOInst.mat Q h⁻¹)) = ofCols Y * ArchSOInst.mat Q h⁻¹ from rfl,
        Matrix.mul_assoc, ArchSOInst.mat_inv_mul, Matrix.mul_one, cols_ofCols]


theorem actME_coeffU (h : ArchSO Q) : actME h (coeffU Q) = coeffU Q := by
  rw [coe_actME, ← phi_one, ← phi_mul, Matrix.one_mul,
    show ArchSOInst.mat Q h = ArchSOInst.mat Q h * 1 from (Matrix.mul_one _).symm,
    phi_of_isometry Q (ArchSOInst.isometry Q h)]

theorem volume_image_actME (h : ArchSO Q) (s : Set (UIdx n → ℝ)) : volume (actME h '' s) = volume s := by
  rw [coe_actME, addHaar_image_linearMap, det_act, ArchSOInst.det_mat, one_pow, abs_one, ENNReal.ofReal_one,
    one_mul]

/-- **The transported balls shrink to $c_Q$**: $\bar B_\varepsilon(c_Q)\cdot h \subseteq \bar B_{C\varepsilon}(c_Q)$. -/
theorem exists_image_actME_subset (h : ArchSO Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > 0, actME h '' Metric.closedBall (coeffU Q) ε ⊆ Metric.closedBall (coeffU Q) (C * ε) := by
  set L := LinearMap.toContinuousLinearMap (act (ArchSOInst.mat Q h))
  refine ⟨‖L‖ + 1, by positivity, fun ε hε => ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  rw [Metric.mem_closedBall] at hc ⊢
  have hL : ∀ x, L x = act (ArchSOInst.mat Q h) x := fun x => rfl
  calc dist (actME h c) (coeffU Q) = ‖L (c - coeffU Q)‖ := by
        rw [dist_eq_norm, map_sub, hL, hL, ← coe_actME, actME_coeffU]
    _ ≤ ‖L‖ * ‖c - coeffU Q‖ := L.le_opNorm _
    _ ≤ (‖L‖ + 1) * ε := by
        rw [← dist_eq_norm]
        exact mul_le_mul (by linarith) hc dist_nonneg (by positivity)

/-- **Right translation does not change integrals against the Leray measure**, for compactly supported continuous
$f \ge 0$: $\int f(gh)\,d\mu_Q(g) = \int f(g)\,d\mu_Q(g)$. -/
theorem integral_mul_right_lerayD {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ X, 0 ≤ f X) (h : ArchSO Q) :
    ∫ g, f (cols (ArchSOInst.mat Q (g * h))) ∂lerayD D = ∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
  set fh : (Fin n → Fin n → ℝ) → ℝ := f ∘ (rmulCLE h).toHomeomorph
  have hfh : Continuous fh := hf.comp (rmulCLE h).toHomeomorph.continuous
  have hfhc : HasCompactSupport fh := hfc.comp_isClosedEmbedding (rmulCLE h).toHomeomorph.isClosedEmbedding
  have hfh0 : ∀ X, 0 ≤ fh X := fun X => hf0 _
  have hL : ∀ g : ArchSO Q, f (cols (ArchSOInst.mat Q (g * h))) = fh (cols (ArchSOInst.mat Q g)) := fun g => by
    simp only [fh, Function.comp_apply, ArchSOInst.mat_mul, cols_mul_right]; rfl
  simp_rw [hL]
  have hA := tendsto_lerayApprox D hfh hfhc
  -- the averages over the transported balls
  obtain ⟨C, hC, hSsub⟩ := exists_image_actME_subset h
  set S : ℝ → Set (UIdx n → ℝ) := fun ε => actME h '' Metric.closedBall (coeffU Q) ε
  set H : (UIdx n → ℝ) → ℝ := fun c => fibreInt D f (sec D c) * rho D c
  have hHc : ContinuousOn H (range (beta D)) :=
    ((continuous_fibreInt D hf hfc).comp_continuousOn (continuousOn_sec D)).mul (continuousOn_rho D)
  have hH0 : ∀ c ∈ range (beta D), 0 ≤ H c := fun c _ =>
    mul_nonneg (integral_nonneg fun g => hf0 _) (rho_nonneg D c)
  have hSm : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (actME h).measurableSet_image.mpr Metric.isClosed_closedBall.measurableSet
  have hvol : ∀ ε, volume (S ε) = volume (Metric.closedBall (coeffU Q) ε) := fun ε => volume_image_actME h _
  have hB := tendsto_avg_of_subset volume hC hSsub hSm
    (fun ε hε => by rw [hvol]; exact Metric.measure_closedBall_pos volume _ hε)
    (fun ε hε => by rw [hvol]; exact measure_closedBall_lt_top.ne)
    (isOpen_range_beta D) (coeffU_mem_range D) hHc hH0
  have hH1 : H (coeffU Q) = ∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
    simp only [H, rho_coeffU, mul_one, sec_coeffU, fibreInt, chart, SliceB.mat_one]
  rw [hH1] at hB
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ range (beta D) := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (isOpen_range_beta D) _ (coeffU_mem_range D)
    filter_upwards [Ioo_mem_nhdsGT (show 0 < δ / (2 * C) by positivity)] with ε hε
    refine (hSsub ε hε.1).trans ((Metric.closedBall_subset_ball ?_).trans hsub)
    have := hε.2
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  refine tendsto_nhds_unique (hA.congr' ?_) hB
  filter_upwards [hev] with ε hε
  have hreg : lerayRegion Q ε = regionR Q (Metric.closedBall (coeffU Q) ε) := rfl
  rw [lerayApprox, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => hfh0 X)
      hfh.aestronglyMeasurable, hreg, ← hvol ε]
  congr 2
  have h1 : ∫⁻ X in regionR Q (Metric.closedBall (coeffU Q) ε), ENNReal.ofReal (fh X) =
      ∫⁻ Y in rmulME h '' regionR Q (Metric.closedBall (coeffU Q) ε), ENNReal.ofReal (f Y) :=
    (measurePreserving_rmulME h).setLIntegral_comp_emb (rmulME h).measurableEmbedding
      (fun Y => ENNReal.ofReal (f Y)) _
  rw [h1, image_rmulME_regionR, lintegral_regionR D hf hfc hf0 (hSm ε) hε]

/-- **The Leray measure is right invariant** (any signature): $SO(Q)(\mathbb R)$ is unimodular and $\mu_Q$ is a
bi-invariant Haar measure. -/
instance isMulRightInvariant_lerayD : (lerayD D).IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  have hμ := isMulLeftInvariant_eq_smul ((lerayD D).map (· * h)) (lerayD D)
  set k := haarScalarFactor ((lerayD D).map (· * h)) (lerayD D)
  have hmeas : Measurable fun g : ArchSO Q => g * h := measurable_mul_const h
  have h1 : ∫ g, bump n (cols (ArchSOInst.mat Q g)) ∂((lerayD D).map (· * h)) =
      ∫ g, bump n (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
    rw [integral_map (f := fun g => bump n (cols (ArchSOInst.mat Q g))) hmeas.aemeasurable
      (continuous_bump.comp (continuous_cols.comp (ArchSOInst.continuous_mat Q))).aestronglyMeasurable]
    exact integral_mul_right_lerayD D continuous_bump hasCompactSupport_bump bump_nonneg h
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h1
  have hpos := integral_bump_pos D
  have hk : (k : ℝ) = 1 := mul_right_cancel₀ hpos.ne' (h1.trans (one_mul _).symm)
  rw [hμ, show k = 1 from NNReal.coe_eq_one.mp hk, one_smul]

/-- **Unimodularity**: the Leray measure $\mu_Q$ on $SO(Q)(\mathbb R)$ is right invariant for every nondegenerate real
form $Q$ (any signature), hence bi-invariant. -/
@[kb "weil1982" "§2.2 (gauge forms on unimodular groups) [unverified]"]
theorem isMulRightInvariant_lerayMeasure (hQ : gramDetR Q ≠ 0) : (lerayMeasure Q hQ).IsMulRightInvariant :=
  isMulRightInvariant_lerayD _

/-- **Right translation by $h$ preserves $\mu_Q$** (explicit form of `isMulRightInvariant_lerayMeasure`). -/
@[kb "weil1982" "§2.2 (gauge forms on unimodular groups) [unverified]"]
theorem map_mul_right_lerayMeasure (hQ : gramDetR Q ≠ 0) (h : ArchSO Q) :
    (lerayMeasure Q hQ).map (· * h) = lerayMeasure Q hQ := by
  have := isMulRightInvariant_lerayMeasure hQ
  exact map_mul_right_eq_self _ h

end QuadFormsKB.Tamagawa.Measure.LerayReal
