/-
# Hanke 2005, §4.2: the box averages of the fibre densities

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Auxiliary limits for the volume computation of §4.2 (`ArchVolumeReal.lean`). Coordinates: upper coordinates
$t = (t_{ij})_{i\le j}$ of symmetric matrices (Gram coordinates), boxes
$\mathrm{boxD}_k(\varepsilon) = \{t : |w_{ij}(t_{ij} - \delta_{ij})|\le\varepsilon\}$ around the identity ($w_{ii} = 1$,
$w_{ij} = 2$, the coefficient weights), $\mathrm{box}_{12}(\varepsilon) = \{A\in\mathbb R^{q\times r} : |2A_{ij}|\le\varepsilon\}$.

**Defines** `Jint ε T` $=\int_{A\in\mathrm{box}_{12}}\int\rho_q(s)\,[s + G_{T^{-1}}(A)\in\mathrm{boxD}_q]\,ds\,dA$ and
`Iint ε` $=\int\rho_r(s)[s\in\mathrm{boxD}_r]\,J_\varepsilon(-s)\,ds$, where $\rho_k$ = `densR k` is the density of
$X\mapsto{}^tXX$ and $G_H(A)_{ij} = A_i\cdot HA_j$.

**Proves** `tendsto_Iint`: $I_\varepsilon/(|\mathrm{boxD}_q||\mathrm{box}_{12}||\mathrm{boxD}_r|)\to c_qc_r$ as
$\varepsilon\to0^+$, $c_k = \rho_k(1)$ = `cprod k` (Siegel's $\mathrm{vol}(O_k(\mathbb R))$ in Gram coordinates).
-/
import QuadFormsKB.Literature.Hanke2005.ArchGramAux
import QuadFormsKB.Tamagawa.Measure.LerayReal

open MeasureTheory Matrix Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Tamagawa.ArchVol

/-! ### Boxes -/

/-- Upper coordinates of the identity matrix. -/
def idU (k : ℕ) : UIdx k → ℝ := fun p => if p.1.1 = p.1.2 then 1 else 0

/-- The box $\{t : |w_{ij}(t_{ij} - \delta_{ij})|\le\varepsilon\}$ around the identity, in upper (Gram) coordinates. -/
def boxD (k : ℕ) (ε : ℝ) : Set (UIdx k → ℝ) := box (idU k) wt ε

/-- The box $\{A : |2A_{ij}|\le\varepsilon\}$ in $\mathbb R^{q\times r}$. -/
def box12 (q r : ℕ) (ε : ℝ) : Set (Fin q → Fin r → ℝ) := {A | ∀ a c, |A a c| ≤ ε / 2}

theorem measurableSet_boxD (k : ℕ) (ε : ℝ) : MeasurableSet (boxD k ε) :=
  MeasurableSet.univ_pi fun _ => measurableSet_closedBall

theorem measurableSet_box12 (q r : ℕ) (ε : ℝ) : MeasurableSet (box12 q r ε) := by
  have : box12 q r ε = univ.pi fun _ => univ.pi fun _ => Metric.closedBall 0 (ε / 2) := by
    ext A; simp [box12, Real.dist_eq]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_closedBall

theorem mem_boxD {k : ℕ} {ε : ℝ} {t : UIdx k → ℝ} :
    t ∈ boxD k ε ↔ ∀ p, |t p - idU k p| ≤ ε / wt p := by
  simp [boxD, box, Real.dist_eq]

theorem symU_idU (k : ℕ) : symU (idU k) = 1 := by
  ext i j
  simp only [symU, idU, Matrix.of_apply, one_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | skip
  all_goals simp_all [eq_comm]

theorem piv_idU (k : ℕ) : piv k (idU k) :=
  piv_of_PDU k _ fun x hx => by
    rw [symU_idU, one_mulVec]
    simpa using (dotProduct_star_self_pos_iff (v := x)).mpr hx

theorem densR_idU (k : ℕ) : densR k (idU k) = ENNReal.ofReal (cprod k) := by
  rw [(densR_of_piv k _ (piv_idU k)).2, symU_idU, det_one, Real.one_rpow, mul_one]

/-! ### The density near the identity -/

/-- $\rho_k$ is within $\eta$ of $c_k$ near the identity. -/
theorem densR_near (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ t : UIdx k → ℝ, (∀ p, |t p - idU k p| < δ) →
      ENNReal.ofReal (cprod k - η) ≤ densR k t ∧ densR k t ≤ ENNReal.ofReal (cprod k + η) := by
  set G : (UIdx k → ℝ) → ℝ := fun t => cprod k * (symU t).det ^ (-(1 / 2 : ℝ))
  have hG : ContinuousAt G (idU k) := by
    refine continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl ?_) |>.comp
      continuous_det_symU.continuousAt)
    rw [symU_idU, det_one]; exact one_ne_zero
  have hG0 : G (idU k) = cprod k := by simp [G, symU_idU]
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp hG η hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.isOpen_iff.mp (isOpen_piv k) _ (piv_idU k)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  have hd : dist t (idU k) < min δ₁ δ₂ := by
    rw [dist_pi_lt_iff (lt_min hδ₁ hδ₂)]
    intro p; rw [Real.dist_eq]; exact ht p
  have hpiv : piv k t := h₂ (lt_of_lt_of_le hd (min_le_right _ _))
  have hGt : |G t - cprod k| < η := by
    rw [← hG0, ← Real.dist_eq]; exact h₁ (lt_of_lt_of_le hd (min_le_left _ _))
  rw [(densR_of_piv k t hpiv).2]
  rw [abs_lt] at hGt
  exact ⟨ENNReal.ofReal_le_ofReal (by simp only [G] at hGt; linarith),
    ENNReal.ofReal_le_ofReal (by simp only [G] at hGt; linarith)⟩

theorem wt_ge_one {k : ℕ} (p : UIdx k) : 1 ≤ wt p := by unfold wt; split_ifs <;> norm_num

/-- **The shifted box average**: for $\varepsilon$ small and $|h|\le\varepsilon$,
$\int\rho_k(s)[s + h\in\mathrm{boxD}_k(\varepsilon)]\,ds$ is within $\eta|\mathrm{boxD}_k(\varepsilon)|$ of $c_k|\mathrm{boxD}_k(\varepsilon)|$. -/
theorem lintegral_shift_bounds (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ∀ h : UIdx k → ℝ, (∀ p, |h p| ≤ ε) →
      ENNReal.ofReal (cprod k - η) * volume (boxD k ε) ≤
          ∫⁻ s, densR k s * (boxD k ε).indicator 1 (s + h) ∧
        ∫⁻ s, densR k s * (boxD k ε).indicator 1 (s + h) ≤
          ENNReal.ofReal (cprod k + η) * volume (boxD k ε) := by
  obtain ⟨δ, hδ, hnear⟩ := densR_near k hη
  refine ⟨δ / 2, by positivity, fun ε hε hεδ h hh => ?_⟩
  set S := (fun s => s + h) ⁻¹' boxD k ε
  have hS : MeasurableSet S := (measurableSet_boxD k ε).preimage (measurable_id.add_const h)
  have hrw : ∫⁻ s, densR k s * (boxD k ε).indicator 1 (s + h) = ∫⁻ s in S, densR k s := by
    rw [← lintegral_indicator hS]
    congr 1; funext s
    by_cases hs : s + h ∈ boxD k ε
    · simp [S, hs, indicator]
    · simp [S, hs, indicator]
  have hvol : volume S = volume (boxD k ε) := measure_preimage_add_right _ _ _
  have hclose : ∀ s ∈ S, ∀ p, |s p - idU k p| < δ := by
    intro s hs p
    have h1 := mem_boxD.mp hs p
    have h2 : ε / wt p ≤ ε := div_le_self hε.le (wt_ge_one p)
    simp only [Pi.add_apply] at h1
    calc |s p - idU k p| = |(s p + h p - idU k p) - h p| := by ring_nf
      _ ≤ |s p + h p - idU k p| + |h p| := abs_sub _ _
      _ ≤ ε + ε := add_le_add (h1.trans h2) (hh p)
      _ < δ := by linarith
  rw [hrw]
  constructor
  · calc ENNReal.ofReal (cprod k - η) * volume (boxD k ε) = ∫⁻ _ in S, ENNReal.ofReal (cprod k - η) := by
          rw [setLIntegral_const, hvol, mul_comm]
      _ ≤ ∫⁻ s in S, densR k s := setLIntegral_mono' hS fun s hs => (hnear s (hclose s hs)).1
  · calc ∫⁻ s in S, densR k s ≤ ∫⁻ _ in S, ENNReal.ofReal (cprod k + η) :=
          setLIntegral_mono' hS fun s hs => (hnear s (hclose s hs)).2
      _ = ENNReal.ofReal (cprod k + η) * volume (boxD k ε) := by rw [setLIntegral_const, hvol, mul_comm]

/-! ### The integrals $J_\varepsilon$ and $I_\varepsilon$ -/

theorem matInv_neg {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, nonsing_inv_mul _ h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [det_neg, isUnit_iff_ne_zero, mul_ne_zero_iff, not_and_or]
      right; intro h0; exact h (isUnit_iff_ne_zero.mpr h0)
    rw [nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit _ h', neg_zero]

/-- $J_\varepsilon(T) = \int_{A\in\mathrm{box}_{12}}\int\rho_q(s)\,[s + G_{T^{-1}}(A)\in\mathrm{boxD}_q(\varepsilon)]\,ds\,dA$. -/
def Jint (q r : ℕ) (ε : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ≥0∞ :=
  ∫⁻ A : Fin q → Fin r → ℝ, (box12 q r ε).indicator
    (fun A => ∫⁻ s, densR q s * (boxD q ε).indicator 1 (s + gramH T⁻¹ A)) A

/-- $I_\varepsilon = \int\rho_r(s)\,[s\in\mathrm{boxD}_r(\varepsilon)]\,J_\varepsilon(-s)\,ds$. -/
def Iint (q r : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : UIdx r → ℝ, densR r s * (boxD r ε).indicator (fun s => Jint q r ε (-(symU s))) s

theorem continuous_symU {k : ℕ} : Continuous (symU : (UIdx k → ℝ) → Matrix (Fin k) (Fin k) ℝ) := by
  refine continuous_matrix fun i j => ?_
  simp only [symU, Matrix.of_apply]
  split_ifs <;> exact continuous_apply _

/-- Near the identity the entries of $(\mathrm{symU}\,s)^{-1}$ are bounded by $2$. -/
theorem inv_symU_bound (k : ℕ) : ∃ δ > 0, ∀ s : UIdx k → ℝ, (∀ p, |s p - idU k p| < δ) →
    ∀ i j, |(symU s)⁻¹ i j| ≤ 2 := by
  have hc : ContinuousAt (fun s : UIdx k → ℝ => (symU s)⁻¹) (idU k) := by
    refine (QuadFormsKB.Tamagawa.Measure.LerayReal.continuousOn_matrix_inv.continuousAt ?_).comp
      continuous_symU.continuousAt
    refine (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds ?_
    simp [symU_idU]
  have hev : ∀ᶠ s in 𝓝 (idU k), ∀ i j, |(symU s)⁻¹ i j| ≤ 2 := by
    rw [Filter.eventually_all]; intro i; rw [Filter.eventually_all]; intro j
    have h1 : Tendsto (fun s : UIdx k → ℝ => (symU s)⁻¹ i j) (𝓝 (idU k)) (𝓝 ((symU (idU k))⁻¹ i j)) :=
      (continuous_id.matrix_elem i j).continuousAt.tendsto.comp hc
    rw [symU_idU, inv_one] at h1
    have h2 : |(1 : Matrix (Fin k) (Fin k) ℝ) i j| < 2 := by
      rw [one_apply]; split_ifs <;> norm_num
    have h3 : ∀ᶠ y in 𝓝 ((1 : Matrix (Fin k) (Fin k) ℝ) i j), |y| < 2 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds h2
    exact (h1.eventually h3).mono fun x hx => hx.le
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun s hs => h ?_⟩
  rw [dist_pi_lt_iff hδ]; intro p; rw [Real.dist_eq]; exact hs p

/-- For $\varepsilon$ small, $|G_{T^{-1}}(A)|\le\varepsilon$ on $\mathrm{box}_{12}(\varepsilon)$ when $-T\in\mathrm{boxD}_r(\varepsilon)$. -/
theorem gramH_small (q r : ℕ) : ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ∀ s ∈ boxD r ε, ∀ A ∈ box12 q r ε,
    ∀ p, |gramH (-(symU s))⁻¹ A p| ≤ ε := by
  obtain ⟨δ₀, hδ₀, hb⟩ := inv_symU_bound r
  refine ⟨min (δ₀ / 2) (1 / ((r : ℝ) ^ 2 + 1)), lt_min (by positivity) (by positivity), fun ε hε hεδ s hs A hA p => ?_⟩
  have hε1 : ε < δ₀ / 2 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hε2 : ε < 1 / ((r : ℝ) ^ 2 + 1) := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hsc : ∀ p', |s p' - idU r p'| < δ₀ := fun p' =>
    lt_of_le_of_lt ((mem_boxD.mp hs p').trans (div_le_self hε.le (wt_ge_one p'))) (by linarith)
  have hM : ∀ i j, |(-(symU s))⁻¹ i j| ≤ 2 := by
    intro i j; rw [matInv_neg, Matrix.neg_apply, abs_neg]; exact hb s hsc i j
  simp only [gramH, dotProduct, mulVec]
  have hA' : ∀ a c, |A a c| ≤ ε / 2 := hA
  calc |∑ c, A p.1.1 c * ∑ d, (-(symU s))⁻¹ c d * A p.1.2 d|
      ≤ ∑ c, |A p.1.1 c| * ∑ d, |(-(symU s))⁻¹ c d| * |A p.1.2 d| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (abs_nonneg _)
        exact Finset.sum_le_sum fun d _ => by rw [abs_mul]
    _ ≤ ∑ _c : Fin r, (ε / 2) * ∑ _d : Fin r, 2 * (ε / 2) := by
        refine Finset.sum_le_sum fun c _ => mul_le_mul (hA' _ _) (Finset.sum_le_sum fun d _ =>
          mul_le_mul (hM c d) (hA' _ _) (abs_nonneg _) (by norm_num)) (Finset.sum_nonneg fun _ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
    _ = (r : ℝ) ^ 2 * ε ^ 2 / 2 := by simp [Finset.sum_const, Finset.card_univ]; ring
    _ ≤ ε := by
        have h3 : ε * ((r : ℝ) ^ 2 + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hε2
        nlinarith [sq_nonneg (r : ℝ), hε.le]

theorem setLIntegral_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α} (hS : MeasurableSet S)
    {F : α → ℝ≥0∞} {L U : ℝ≥0∞} (hF : ∀ x ∈ S, L ≤ F x ∧ F x ≤ U) :
    L * μ S ≤ ∫⁻ x, S.indicator F x ∂μ ∧ ∫⁻ x, S.indicator F x ∂μ ≤ U * μ S := by
  rw [lintegral_indicator hS]
  refine ⟨?_, ?_⟩
  · calc L * μ S = ∫⁻ _ in S, L ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x in S, F x ∂μ := setLIntegral_mono' hS fun x hx => (hF x hx).1
  · calc ∫⁻ x in S, F x ∂μ ≤ ∫⁻ _ in S, U ∂μ := setLIntegral_mono' hS fun x hx => (hF x hx).2
      _ = U * μ S := by rw [setLIntegral_const, mul_comm]

/-- **Bounds for $I_\varepsilon$.** -/
theorem Iint_bounds (q r : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ →
      ENNReal.ofReal (cprod r - η) * (ENNReal.ofReal (cprod q - η) * volume (boxD q ε) * volume (box12 q r ε)) *
          volume (boxD r ε) ≤ Iint q r ε ∧
        Iint q r ε ≤ ENNReal.ofReal (cprod r + η) *
          (ENNReal.ofReal (cprod q + η) * volume (boxD q ε) * volume (box12 q r ε)) * volume (boxD r ε) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := lintegral_shift_bounds q hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := lintegral_shift_bounds r hη
  obtain ⟨δ₃, hδ₃, h₃⟩ := gramH_small q r
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun ε hε hεδ => ?_⟩
  have e1 : ε < δ₁ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have e2 : ε < δ₂ := lt_of_lt_of_le hεδ ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : ε < δ₃ := lt_of_lt_of_le hεδ ((min_le_right _ _).trans (min_le_right _ _))
  have hJ : ∀ s ∈ boxD r ε,
      ENNReal.ofReal (cprod q - η) * volume (boxD q ε) * volume (box12 q r ε) ≤ Jint q r ε (-(symU s)) ∧
        Jint q r ε (-(symU s)) ≤ ENNReal.ofReal (cprod q + η) * volume (boxD q ε) * volume (box12 q r ε) := by
    intro s hs
    exact setLIntegral_bounds (measurableSet_box12 q r ε) fun A hA =>
      h₁ ε hε e1 _ (h₃ ε hε e3 s hs A hA)
  have hI : Iint q r ε = ∫⁻ s, (boxD r ε).indicator (fun s => densR r s * Jint q r ε (-(symU s))) s := by
    rw [Iint]; congr 1; funext s
    by_cases hs : s ∈ boxD r ε <;> simp [hs]
  have h0 := h₂ ε hε e2 0 (fun _ => by simp [hε.le])
  simp only [add_zero] at h0
  have hD : ∫⁻ s, densR r s * (boxD r ε).indicator 1 s = ∫⁻ s in boxD r ε, densR r s := by
    rw [← lintegral_indicator (measurableSet_boxD r ε)]; congr 1; funext s
    by_cases hs : s ∈ boxD r ε <;> simp [hs]
  rw [hD] at h0
  rw [hI, lintegral_indicator (measurableSet_boxD r ε)]
  set Lq := ENNReal.ofReal (cprod q - η) * volume (boxD q ε) * volume (box12 q r ε)
  set Uq := ENNReal.ofReal (cprod q + η) * volume (boxD q ε) * volume (box12 q r ε)
  have hc : ∀ c : ℝ≥0∞, ∫⁻ s in boxD r ε, c * densR r s = c * ∫⁻ s in boxD r ε, densR r s :=
    fun c => lintegral_const_mul c (measurable_densR r)
  constructor
  · calc ENNReal.ofReal (cprod r - η) * Lq * volume (boxD r ε)
        = Lq * (ENNReal.ofReal (cprod r - η) * volume (boxD r ε)) := by ring
      _ ≤ Lq * ∫⁻ s in boxD r ε, densR r s := mul_le_mul_right h0.1 _
      _ = ∫⁻ s in boxD r ε, Lq * densR r s := (hc Lq).symm
      _ ≤ ∫⁻ s in boxD r ε, densR r s * Jint q r ε (-(symU s)) :=
          setLIntegral_mono' (measurableSet_boxD r ε) fun s hs => by
            rw [mul_comm]; exact mul_le_mul_right (hJ s hs).1 _
  · calc ∫⁻ s in boxD r ε, densR r s * Jint q r ε (-(symU s))
        ≤ ∫⁻ s in boxD r ε, Uq * densR r s :=
          setLIntegral_mono' (measurableSet_boxD r ε) fun s hs => by
            rw [mul_comm Uq]; exact mul_le_mul_right (hJ s hs).2 _
      _ = Uq * ∫⁻ s in boxD r ε, densR r s := hc Uq
      _ ≤ Uq * (ENNReal.ofReal (cprod r + η) * volume (boxD r ε)) := mul_le_mul_right h0.2 _
      _ = ENNReal.ofReal (cprod r + η) * Uq * volume (boxD r ε) := by ring

theorem volume_boxD (k : ℕ) (ε : ℝ) : volume (boxD k ε) = ∏ p : UIdx k, ENNReal.ofReal (2 * (ε / wt p)) :=
  volume_box _ _ _

theorem volume_boxD_ne_top (k : ℕ) (ε : ℝ) : volume (boxD k ε) ≠ ⊤ := by
  rw [volume_boxD]; exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

theorem volume_boxD_pos (k : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < volume (boxD k ε) := by
  rw [volume_boxD]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p _ => (ENNReal.ofReal_pos.mpr (by have := wt_pos p; positivity)).ne')

theorem volume_box12 (q r : ℕ) (ε : ℝ) : volume (box12 q r ε) = ENNReal.ofReal ε ^ (q * r) := by
  have : box12 q r ε = univ.pi fun _ => univ.pi fun _ => Metric.closedBall (0 : ℝ) (ε / 2) := by
    ext A; simp [box12, Real.dist_eq]
  rw [this, volume_pi_pi]
  simp only [volume_pi_pi, Real.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, show 2 * (ε / 2) = ε by ring, mul_comm r q]

theorem volume_box12_ne_top (q r : ℕ) (ε : ℝ) : volume (box12 q r ε) ≠ ⊤ := by
  rw [volume_box12]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem volume_box12_pos (q r : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < volume (box12 q r ε) := by
  rw [volume_box12]; exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr hε) _

/-- The product $V_\varepsilon = |\mathrm{boxD}_q(\varepsilon)|\,|\mathrm{box}_{12}(\varepsilon)|\,|\mathrm{boxD}_r(\varepsilon)|$. -/
def Vbox (q r : ℕ) (ε : ℝ) : ℝ≥0∞ := volume (boxD q ε) * volume (box12 q r ε) * volume (boxD r ε)

theorem Vbox_ne_top (q r : ℕ) (ε : ℝ) : Vbox q r ε ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (volume_boxD_ne_top q ε) (volume_box12_ne_top q r ε))
    (volume_boxD_ne_top r ε)

theorem Vbox_pos (q r : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < Vbox q r ε :=
  ENNReal.mul_pos (ENNReal.mul_pos (volume_boxD_pos q hε).ne' (volume_box12_pos q r hε).ne').ne'
    (volume_boxD_pos r hε).ne'

/-- **The box average of $I_\varepsilon$**: $I_\varepsilon/V_\varepsilon\to c_qc_r$. -/
theorem tendsto_Iint (q r : ℕ) :
    Tendsto (fun ε => (Iint q r ε).toReal / (Vbox q r ε).toReal) (𝓝[>] 0) (𝓝 (cprod q * cprod r)) := by
  have hq := cprod_pos q
  have hr := cprod_pos r
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  set η := min (min (cprod q / 2) (cprod r / 2)) (min 1 (e / (2 * (cprod q + cprod r + 1))))
  have hη : 0 < η := lt_min (lt_min (by positivity) (by positivity)) (lt_min one_pos (by positivity))
  have hηq : η ≤ cprod q / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hηr : η ≤ cprod r / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηe : η ≤ e / (2 * (cprod q + cprod r + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ, hδ, hb⟩ := Iint_bounds q r hη
  refine ⟨δ, hδ, fun ε hε hdist => ?_⟩
  have hε0 : 0 < ε := hε
  have hεδ : ε < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hdist; exact hdist
  obtain ⟨hlo, hhi⟩ := hb ε hε0 hεδ
  set V := Vbox q r ε
  have hV : 0 < V.toReal := ENNReal.toReal_pos (Vbox_pos q r hε0).ne' (Vbox_ne_top q r ε)
  have hlo' : ENNReal.ofReal ((cprod r - η) * (cprod q - η)) * V ≤ Iint q r ε := by
    convert hlo using 1
    rw [ENNReal.ofReal_mul (by linarith)]; simp only [V, Vbox]; ring
  have hhi' : Iint q r ε ≤ ENNReal.ofReal ((cprod r + η) * (cprod q + η)) * V := by
    convert hhi using 1
    rw [ENNReal.ofReal_mul (by linarith)]; simp only [V, Vbox]; ring
  have hfin : ENNReal.ofReal ((cprod r + η) * (cprod q + η)) * V ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Vbox_ne_top q r ε)
  have hlo2 : (cprod r - η) * (cprod q - η) * V.toReal ≤ (Iint q r ε).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfin hhi') hlo'
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by nlinarith)] at this
  have hhi2 : (Iint q r ε).toReal ≤ (cprod r + η) * (cprod q + η) * V.toReal := by
    have := ENNReal.toReal_mono hfin hhi'
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by nlinarith)] at this
  have h1 : (cprod r - η) * (cprod q - η) ≤ (Iint q r ε).toReal / V.toReal := by
    rw [le_div_iff₀ hV]; exact hlo2
  have h2 : (Iint q r ε).toReal / V.toReal ≤ (cprod r + η) * (cprod q + η) := by
    rw [div_le_iff₀ hV]; exact hhi2
  have hk : η * (cprod q + cprod r + 1) ≤ e / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (cprod q + cprod r + 1))).mp hηe
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end QuadFormsKB.Hanke2005.ArchReal
