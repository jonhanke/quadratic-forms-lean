/-
# Hanke 2005, §4.3: test functions adapted to $F_{\mathbb C}$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Fix the chart $W\ni c_0$ of the Gram map $h$ (`exists_chart`, with continuous inverse $g$ on $h(W)$) and a bump $\chi$ at
$c_Q$ supported in $h(W)$. For $X$ with $\Phi(X)\in h(W)$ the reconstruction (`ArchCxRecon.lean`) gives
$X = \Psi(u(X), Y, \sigma)$; the **test function** attached to $\varphi$ on $Z_{\mathbb C}$ is
$$f_\varphi(X) = \varphi(u(X))\,\chi(\Phi(X)).$$

**Proves**
* `continuous_fTest`, `hasCompactSupport_fTest`: $f_\varphi$ is continuous with compact support when $\varphi$ is continuous
  with compact support in $Z_{\mathbb C}$;
* `fTest_mat`: on $SO_n(\mathbb C)$, $f_\varphi(\alpha) = \varphi(F_{\mathbb C}(\alpha))$.
-/
import QuadFormsKB.Literature.Hanke2005.ArchCxRecon
import QuadFormsKB.Literature.Hanke2005.ArchActionComplex

open Matrix Complex Set Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

/-! ### The chart data -/

/-- The chart domain $W$ (`exists_chart`). -/
def Wc (n : ℕ) : Set (UIdx n → ℂ) := (exists_chart (n := n)).choose

/-- The continuous inverse $g$ of $h$ on $h(W)$. -/
def gc (n : ℕ) : (UIdx n → ℂ) → UIdx n → ℂ := (exists_chart (n := n)).choose_spec.choose

theorem chart_spec : IsOpen (Wc n) ∧ c0 ∈ Wc n ∧ IsOpen (hmap '' Wc n) ∧ ContinuousOn (gc n) (hmap '' Wc n) ∧
    (∀ c ∈ Wc n, gc n (hmap c) = c) ∧
    ∀ c ∈ Wc n, PDU (fun q => (c q).re) ∧ 0 < (1 - I • cplx (cS c)).det.re ∧
      LinearMap.det (fderiv ℝ hmap c : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) ≠ 0 :=
  (exists_chart (n := n)).choose_spec.choose_spec

theorem isOpen_Wc : IsOpen (Wc n) := chart_spec.1
theorem c0_mem_Wc : (c0 : UIdx n → ℂ) ∈ Wc n := chart_spec.2.1
theorem isOpen_hmap_Wc : IsOpen (hmap '' Wc n) := chart_spec.2.2.1
theorem continuousOn_gc : ContinuousOn (gc n) (hmap '' Wc n) := chart_spec.2.2.2.1
theorem gc_hmap {c : UIdx n → ℂ} (hc : c ∈ Wc n) : gc n (hmap c) = c := chart_spec.2.2.2.2.1 c hc
theorem PDU_of_Wc {c : UIdx n → ℂ} (hc : c ∈ Wc n) : PDU (fun q => (c q).re) := (chart_spec.2.2.2.2.2 c hc).1
theorem det_re_pos_of_Wc {c : UIdx n → ℂ} (hc : c ∈ Wc n) : 0 < (1 - I • cplx (cS c)).det.re :=
  (chart_spec.2.2.2.2.2 c hc).2.1
theorem det_ne_zero_of_Wc {c : UIdx n → ℂ} (hc : c ∈ Wc n) : (1 - I • cplx (cS c)).det ≠ 0 := fun h => by
  have := det_re_pos_of_Wc hc; rw [h, zero_re] at this; exact lt_irrefl _ this
theorem det_fderiv_ne_zero_of_Wc {c : UIdx n → ℂ} (hc : c ∈ Wc n) :
    LinearMap.det (fderiv ℝ hmap c : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) ≠ 0 :=
  (chart_spec.2.2.2.2.2 c hc).2.2

theorem cQ_mem : coeffUC (sumSqC n) ∈ hmap '' Wc n := ⟨c0, c0_mem_Wc, hmap_c0⟩

theorem gc_mem {w : UIdx n → ℂ} (hw : w ∈ hmap '' Wc n) : gc n w ∈ Wc n := by
  obtain ⟨c, hc, rfl⟩ := hw; rw [gc_hmap hc]; exact hc

theorem hmap_gc {w : UIdx n → ℂ} (hw : w ∈ hmap '' Wc n) : hmap (gc n w) = w := by
  obtain ⟨c, hc, rfl⟩ := hw; rw [gc_hmap hc]

theorem gc_cQ : gc n (coeffUC (sumSqC n)) = c0 := by rw [← hmap_c0, gc_hmap c0_mem_Wc]

/-! ### The bump $\chi$ at $c_Q$ -/

theorem exists_radius : ∃ δ > 0, Metric.closedBall (coeffUC (sumSqC n)) (2 * δ) ⊆ hmap '' Wc n := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp isOpen_hmap_Wc _ cQ_mem
  refine ⟨ε / 4, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩

/-- The bump radius $\delta$. -/
def rad (n : ℕ) : ℝ := (exists_radius (n := n)).choose

theorem rad_pos : 0 < rad n := (exists_radius (n := n)).choose_spec.1

theorem closedBall_rad_subset : Metric.closedBall (coeffUC (sumSqC n)) (2 * rad n) ⊆ hmap '' Wc n :=
  (exists_radius (n := n)).choose_spec.2

/-- **The bump** $\chi(w) = \max(0, 1 - |w - c_Q|/\delta)$. -/
def chiB (n : ℕ) (w : UIdx n → ℂ) : ℝ := max 0 (1 - dist w (coeffUC (sumSqC n)) / rad n)

theorem continuous_chiB : Continuous (chiB n) :=
  continuous_const.max (continuous_const.sub ((continuous_id.dist continuous_const).div_const _))

theorem chiB_nonneg (w : UIdx n → ℂ) : 0 ≤ chiB n w := le_max_left _ _

theorem chiB_cQ : chiB n (coeffUC (sumSqC n)) = 1 := by simp [chiB]

theorem chiB_eq_zero {w : UIdx n → ℂ} (hw : rad n ≤ dist w (coeffUC (sumSqC n))) : chiB n w = 0 := by
  refine max_eq_left ?_
  have := rad_pos (n := n)
  rw [sub_nonpos, le_div_iff₀ this, one_mul]; exact hw

theorem tsupport_chiB : tsupport (chiB n) ⊆ Metric.closedBall (coeffUC (sumSqC n)) (rad n) := by
  refine closure_minimal (fun w hw => ?_) Metric.isClosed_closedBall
  by_contra h
  rw [Metric.mem_closedBall, not_le] at h
  exact hw (chiB_eq_zero h.le)

theorem tsupport_chiB_subset : tsupport (chiB n) ⊆ hmap '' Wc n := by
  refine tsupport_chiB.trans ((Metric.closedBall_subset_closedBall ?_).trans closedBall_rad_subset)
  have := rad_pos (n := n); linarith

/-! ### The coordinate $u(X)$ and the test functions -/

/-- $u(X)$: the skew coordinate of the reconstruction, with $c = g(\Phi(X))$. -/
def uOf (X : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℝ := uOfc (ofCols X) (gc n (phi (sumSqC n) (ofCols X)))

/-- **The test function** $f_\varphi(X) = \varphi(u(X))\,\chi(\Phi(X))$. -/
def fTest (φ : (LIdx n → ℝ) → ℝ) (X : Fin n → Fin n → ℂ) : ℝ :=
  φ (lowerOf (uOf X)) * chiB n (phi (sumSqC n) (ofCols X))

theorem continuous_reM : Continuous (reM : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_imM : Continuous (imM : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_lowerOf : Continuous (lowerOf : Matrix (Fin n) (Fin n) ℝ → LIdx n → ℝ) :=
  continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)

theorem continuousOn_matrix_inv_real :
    ContinuousOn (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) {M | M.det ≠ 0} := by
  have : (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (continuous_id.matrix_det.continuousOn.inv₀ fun M hM => hM).smul
    continuous_id.matrix_adjugate.continuousOn

theorem continuousAt_uOf {X₀ : Fin n → Fin n → ℂ} (h : phi (sumSqC n) (ofCols X₀) ∈ hmap '' Wc n) :
    ContinuousAt uOf X₀ := by
  have hphi : Continuous fun X : Fin n → Fin n → ℂ => phi (sumSqC n) (ofCols X) :=
    (continuous_phi _).comp continuous_ofCols
  have hc : ContinuousAt (fun X : Fin n → Fin n → ℂ => gc n (phi (sumSqC n) (ofCols X))) X₀ :=
    (continuousOn_gc.continuousAt (isOpen_hmap_Wc.mem_nhds h)).comp
      (f := fun X : Fin n → Fin n → ℂ => phi (sumSqC n) (ofCols X)) hphi.continuousAt
  have hc0 := gc_mem h
  have hS : ContinuousAt (fun X : Fin n → Fin n → ℂ => 1 - I • cplx (cS (gc n (phi (sumSqC n) (ofCols X))))) X₀ :=
    continuousAt_const.sub (((continuous_cplx.comp continuous_cS).continuousAt.comp
      (f := fun X : Fin n → Fin n → ℂ => gc n (phi (sumSqC n) (ofCols X))) hc).const_smul I)
  have hSi : ContinuousAt (fun X : Fin n → Fin n → ℂ =>
      (1 - I • cplx (cS (gc n (phi (sumSqC n) (ofCols X)))))⁻¹) X₀ :=
    (continuousOn_matrix_inv.continuousAt (IsOpen.mem_nhds
      (isOpen_ne_fun continuous_id.matrix_det continuous_const) (det_ne_zero_of_Wc hc0))).comp
      (f := fun X : Fin n → Fin n → ℂ => 1 - I • cplx (cS (gc n (phi (sumSqC n) (ofCols X))))) hS
  have hA : ContinuousAt (fun X : Fin n → Fin n → ℂ => aOf (ofCols X) (gc n (phi (sumSqC n) (ofCols X)))) X₀ :=
    ContinuousAt.mul (continuous_ofCols.continuousAt (x := X₀)) hSi
  have hdet := det_reM_aOf_ne_zero (hmap_gc h) (PDU_of_Wc hc0) (det_ne_zero_of_Wc hc0)
  have hYi : ContinuousAt (fun X : Fin n → Fin n → ℂ =>
      (reM (aOf (ofCols X) (gc n (phi (sumSqC n) (ofCols X)))))⁻¹) X₀ :=
    (continuousOn_matrix_inv_real.continuousAt (IsOpen.mem_nhds
      (isOpen_ne_fun continuous_id.matrix_det continuous_const) hdet)).comp
      (f := fun X : Fin n → Fin n → ℂ => reM (aOf (ofCols X) (gc n (phi (sumSqC n) (ofCols X)))))
      (continuous_reM.continuousAt.comp
        (f := fun X : Fin n → Fin n → ℂ => aOf (ofCols X) (gc n (phi (sumSqC n) (ofCols X)))) hA)
  exact ContinuousAt.mul ((continuous_imM.continuousAt.comp
    (f := fun X : Fin n → Fin n → ℂ => aOf (ofCols X) (gc n (phi (sumSqC n) (ofCols X)))) hA).neg) hYi

theorem continuous_fTest {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) : Continuous (fTest φ) := by
  have hphi : Continuous fun X : Fin n → Fin n → ℂ => phi (sumSqC n) (ofCols X) :=
    (continuous_phi _).comp continuous_ofCols
  refine continuous_iff_continuousAt.2 fun X₀ => ?_
  by_cases h : phi (sumSqC n) (ofCols X₀) ∈ hmap '' Wc n
  · exact (hφ.continuousAt.comp (f := fun X => lowerOf (uOf X))
      (continuous_lowerOf.continuousAt.comp (f := uOf) (continuousAt_uOf h))).mul
      (continuous_chiB.comp hphi).continuousAt
  · have hnot : phi (sumSqC n) (ofCols X₀) ∉ tsupport (chiB n) := fun h' => h (tsupport_chiB_subset h')
    have hev : ∀ᶠ X in 𝓝 X₀, phi (sumSqC n) (ofCols X) ∉ tsupport (chiB n) :=
      hphi.continuousAt.eventually_mem ((isClosed_tsupport _).isOpen_compl.mem_nhds hnot)
    have heq : (fun _ : Fin n → Fin n → ℂ => (0 : ℝ)) =ᶠ[𝓝 X₀] fTest φ := by
      filter_upwards [hev] with X hX
      rw [fTest, image_eq_zero_of_notMem_tsupport hX, mul_zero]
    exact continuousAt_const.congr heq

/-- On $SO_n(\mathbb C)$: $f_\varphi(\alpha) = \varphi(F_{\mathbb C}(\alpha))$. -/
theorem fTest_mat (φ : (LIdx n → ℝ) → ℝ) (g : ArchSOC (sumSqC n)) :
    fTest φ (cols (ArchSOC.mat _ g)) = φ (FCG g) := by
  have hg := mat_mem_SOC g
  have hphi : phi (sumSqC n) (ArchSOC.mat _ g) = coeffUC (sumSqC n) := by
    rw [phi_sumSqC, hg.1, coeffUC_eq, gramC_sumSqC]
  rw [fTest, uOf, ofCols_cols, hphi, gc_cQ, chiB_cQ, mul_one, FCG, uOfc, aOf, cS_c0, cplx_zero, smul_zero,
    sub_zero, inv_one, Matrix.mul_one, actC_zero]

/-! ### Compact support -/

theorem diag_gram_eq (Y M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (Yᵀ * M * Y) j j = (fun i => Y i j) ⬝ᵥ (M *ᵥ fun i => Y i j) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- A uniform lower bound $m\,\|v\|^2\le v\cdot(1 - {}^tuu)v$ for $u$ in a compact subset of $Z_{\mathbb C}$. -/
theorem exists_lower_bound {K : Set (Matrix (Fin n) (Fin n) ℝ)} (hK : IsCompact K) (hKZ : K ⊆ ZC n) :
    ∃ m > 0, ∀ u ∈ K, ∀ v : Fin n → ℝ, m * ‖v‖ ^ 2 ≤ v ⬝ᵥ (mZ u *ᵥ v) := by
  set S := K ×ˢ Metric.sphere (0 : Fin n → ℝ) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hcont : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) => q.2 ⬝ᵥ (mZ q.1 *ᵥ q.2) :=
    continuous_snd.dotProduct ((continuous_const.sub (continuous_fst.matrix_transpose.matrix_mul
      continuous_fst)).matrix_mulVec continuous_snd)
  have hpos : ∀ q ∈ S, 0 < q.2 ⬝ᵥ (mZ q.1 *ᵥ q.2) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have hPD := (posDef_iff_dotProduct_mulVec.mp (hKZ hu).2).2 hv0
    rw [star_trivial] at hPD
    exact hPD
  obtain ⟨m, hm, hmS⟩ : ∃ m > 0, ∀ q ∈ S, m ≤ q.2 ⬝ᵥ (mZ q.1 *ᵥ q.2) := by
    rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun q hq => by rw [he] at hq; exact absurd hq (Set.notMem_empty q)⟩
    · obtain ⟨q₀, hq₀, hmin⟩ := hS.exists_isMinOn hne hcont.continuousOn
      exact ⟨_, hpos q₀ hq₀, fun q hq => hmin hq⟩
  refine ⟨m, hm, fun u hu v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have h1 := hmS (u, ‖v‖⁻¹ • v) ⟨hu, hw⟩
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1
  have h2 : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * v ⬝ᵥ (mZ u *ᵥ v))) = v ⬝ᵥ (mZ u *ᵥ v) := by
    field_simp
  calc m * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ * (‖v‖⁻¹ * v ⬝ᵥ (mZ u *ᵥ v))) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = v ⬝ᵥ (mZ u *ᵥ v) := by rw [mul_comm]; exact h2

theorem hasCompactSupport_fTest {φ : (LIdx n → ℝ) → ℝ} (hφc : HasCompactSupport φ)
    (hφZ : tsupport φ ⊆ skewOf ⁻¹' ZC n) : HasCompactSupport (fTest φ) := by
  set B := Metric.closedBall (coeffUC (sumSqC n)) (rad n)
  have hBN : B ⊆ hmap '' Wc n := (Metric.closedBall_subset_closedBall (by linarith [rad_pos (n := n)])).trans
    closedBall_rad_subset
  have hB : IsCompact B := isCompact_closedBall _ _
  set Kc := gc n '' B
  have hKc : IsCompact Kc := hB.image_of_continuousOn (continuousOn_gc.mono hBN)
  set Ku := skewOf '' tsupport φ
  have hKu : IsCompact Ku := hφc.isCompact.image continuous_skewOf
  have hKuZ : Ku ⊆ ZC n := by rintro _ ⟨v, hv, rfl⟩; exact hφZ hv
  obtain ⟨m, hm, hmK⟩ := exists_lower_bound hKu hKuZ
  have hcTpi : Continuous fun c : UIdx n → ℂ => (fun i j => cT c i j : Fin n → Fin n → ℝ) :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp continuous_cT)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcTpi.continuousOn
  set R := max C 0
  set r := Real.sqrt (R / m)
  set Kσ := cS '' Kc
  have hKσ : IsCompact Kσ := hKc.image continuous_cS
  set Kp := Ku ×ˢ (Metric.closedBall (0 : Fin n → Fin n → ℝ) r ×ˢ Kσ)
  have hKp : IsCompact Kp := hKu.prod ((isCompact_closedBall _ _).prod hKσ)
  have hcpsi : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      cols (psiM q.1 q.2.1 q.2.2) := by
    have h1 : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
        psiM q.1 q.2.1 q.2.2 := by
      unfold psiM
      exact ((continuous_const.sub ((continuous_cplx.comp continuous_fst).const_smul I)).mul
        (continuous_cplx.comp (continuous_fst.comp continuous_snd))).mul
        (continuous_const.sub ((continuous_cplx.comp (continuous_snd.comp continuous_snd)).const_smul I))
    exact (continuous_pi fun j => continuous_pi fun i => (continuous_apply j).comp ((continuous_apply i).comp h1))
  refine HasCompactSupport.intro (hKp.image hcpsi) fun X hX => ?_
  by_contra hne
  apply hX
  have hchi : chiB n (phi (sumSqC n) (ofCols X)) ≠ 0 := fun h => hne (by rw [fTest, h, mul_zero])
  have hφne : φ (lowerOf (uOf X)) ≠ 0 := fun h => hne (by rw [fTest, h, zero_mul])
  have hXB : phi (sumSqC n) (ofCols X) ∈ B := by
    by_contra h'
    rw [Metric.mem_closedBall, not_le] at h'
    exact hchi (chiB_eq_zero h'.le)
  set c := gc n (phi (sumSqC n) (ofCols X))
  have hcW : c ∈ Wc n := gc_mem (hBN hXB)
  have hc : hmap c = phi (sumSqC n) (ofCols X) := hmap_gc (hBN hXB)
  have hT := PDU_of_Wc hcW
  have hd := det_ne_zero_of_Wc hcW
  set u := uOfc (ofCols X) c
  set Y := reM (aOf (ofCols X) c)
  have hu : u = uOf X := rfl
  have huK : u ∈ Ku := by
    refine ⟨lowerOf u, subset_tsupport _ hφne, ?_⟩
    exact skewOf_lowerOf (uOfc_skew hc hT hd)
  have hcK : c ∈ Kc := ⟨_, hXB, rfl⟩
  have hY : (fun i j => Y i j : Fin n → Fin n → ℝ) ∈ Metric.closedBall (0 : Fin n → Fin n → ℝ) r := by
    refine Metric.mem_closedBall.mpr ?_
    rw [dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    set v : Fin n → ℝ := fun i => Y i j
    have h1 : m * ‖v‖ ^ 2 ≤ v ⬝ᵥ (mZ u *ᵥ v) := hmK u huK v
    have h2 : v ⬝ᵥ (mZ u *ᵥ v) = cT c j j := by
      rw [← diag_gram_eq, ← tT, tT_uOfc hc hT hd]
    have h3 : cT c j j ≤ R := by
      refine (le_abs_self _).trans ((le_trans ?_ (hC c hcK)).trans (le_max_left _ _))
      exact (norm_le_pi_norm (fun j' => cT c j j') j).trans
        (norm_le_pi_norm (fun i j => cT c i j : Fin n → Fin n → ℝ) j)
    have h4 : ‖v‖ ^ 2 ≤ R / m := by
      rw [le_div_iff₀ hm]; nlinarith
    calc ‖Y i j‖ = ‖v i‖ := rfl
      _ ≤ ‖v‖ := norm_le_pi_norm v i
      _ ≤ r := Real.le_sqrt_of_sq_le h4
  refine ⟨(u, fun i j => Y i j, cS c), ⟨huK, hY, ⟨c, hcK, rfl⟩⟩, ?_⟩
  show cols (psiM u Y (cS c)) = X
  rw [← X_eq_psiM hc hT hd, cols_ofCols]

end QuadFormsKB.Hanke2005.ArchCx
