import QuadFormsKB.Tamagawa.Measure.Weil.PDArchChart

/-!
# The slice side of the archimedean comparison; adapted coordinates; ratio limits

**Layer:** $\Bbbk = \mathbb R$ or $\mathbb C$ (`RCLike`), $Q = \alpha_0x_0^2 + \alpha_1x_1^2 + \alpha_2x_2^2$ diagonal.

* `betaJ α`: the orbit map $b \mapsto \Phi_Q(b)$ of the slice group in the coordinates $b = 1 + U(w)$
  ($U(w)$ upper triangular); `hasStrictFDerivAt_betaJ`: strict derivative $w_{ij}\mapsto 2\alpha_iw_{ij}$ at $0$,
  `det_betaDL`: determinant $64\alpha_0^3\alpha_1^2\alpha_2$.
* `eMatE`: the coordinates $M \mapsto ((M_{21}, M_{20}, M_{10}), (M_{ij})_{i\le j})$ on $M_3(\Bbbk)$, an isometry for the
  sup norms; `volume_image_eMatE`: measure preserving.
* `volume_shear`: $\mathrm{vol}\{(y,u) : y\in S,\ u - Py\in W\} = \mathrm{vol}(S)\mathrm{vol}(W)$.
* `tendsto_ratio_of_bounds`: the elementary limit used to read off a ratio of Haar measures from first-order data.
-/

open Matrix MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.ArchVol

section Beta

variable {𝕜 : Type*} [RCLike 𝕜] (α : Fin 3 → 𝕜)

/-- The coefficient vector of $y \mapsto Q(My)$ for $Q = \sum_i \alpha_i x_i^2$ (`phi` for a diagonal Gram matrix). -/
def phiK (M : Matrix (Fin 3) (Fin 3) 𝕜) : UIdx 3 → 𝕜 :=
  fun p => (wt p : 𝕜) * (Mᵀ * Matrix.diagonal α * M) p.1.1 p.1.2

/-- **The orbit map of the slice** in upper triangular coordinates: $w \mapsto \Phi_Q(1 + U(w))$. -/
def betaJ (w : UIdx 3 → 𝕜) : UIdx 3 → 𝕜 := phiK α (1 + utK w)

/-- Its derivative at $0$: $w_{ij} \mapsto 2\alpha_i w_{ij}$. -/
def betaDL : (UIdx 3 → 𝕜) →ₗ[𝕜] (UIdx 3 → 𝕜) := Matrix.toLin' (Matrix.diagonal fun p => 2 * α p.1.1)

theorem betaJ_smul (t : 𝕜) (w : UIdx 3 → 𝕜) :
    betaJ α (t • w) = betaJ α 0 + t • betaDL α w + t ^ 2 • phiK α (utK w) := by
  funext p
  obtain ⟨⟨i, j⟩, h⟩ := p
  simp only [betaJ, phiK, betaDL, utK_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.toLin'_apply,
    Matrix.mulVec_diagonal]
  fin_cases i <;> fin_cases j <;> first | (simp at h; done) |
  (simp [utK, wt, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, Matrix.one_apply]; push_cast; ring)

theorem contDiff_betaJ : ContDiff 𝕜 ⊤ (betaJ α) := by
  rw [contDiff_pi]; intro p
  obtain ⟨⟨i, j⟩, h⟩ := p
  simp only [betaJ, phiK]
  fin_cases i <;> fin_cases j <;> first | (simp at h; done) |
  (simp [utK, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, Matrix.one_apply]; fun_prop)

theorem hasDerivAt_betaJ_line (w : UIdx 3 → 𝕜) :
    HasDerivAt (fun t : 𝕜 => betaJ α (t • w)) (betaDL α w) 0 := by
  simp_rw [betaJ_smul]
  have h1 : HasDerivAt (fun r : 𝕜 => r • betaDL α w) ((1 : 𝕜) • betaDL α w) 0 := (hasDerivAt_id 0).smul_const _
  have h2 : HasDerivAt (fun r : 𝕜 => r ^ 2 • phiK α (utK w)) (((2 : ℕ) * (0 : 𝕜) ^ (2 - 1)) • phiK α (utK w)) 0 :=
    (hasDerivAt_pow 2 (0 : 𝕜)).smul_const _
  convert (h1.const_add (betaJ α 0)).add h2 using 1
  simp

theorem hasStrictFDerivAt_betaJ :
    HasStrictFDerivAt (betaJ α) (LinearMap.toContinuousLinearMap (betaDL α)) 0 := by
  have h := (contDiff_betaJ α).contDiffAt.hasStrictFDerivAt (x := 0) (by simp)
  convert h using 1
  refine ContinuousLinearMap.ext fun w => ?_
  have hd : HasFDerivAt (betaJ α) (fderiv 𝕜 (betaJ α) 0) ((0 : 𝕜) • w) := by
    rw [zero_smul]; exact ((contDiff_betaJ α).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun r : 𝕜 => r • w) w 0 := by simpa using (hasDerivAt_id (0 : 𝕜)).smul_const w
  have h1 : HasDerivAt (fun r : 𝕜 => betaJ α (r • w)) (fderiv 𝕜 (betaJ α) 0 w) 0 := by
    simpa [Function.comp_def] using hd.comp_hasDerivAt (0 : 𝕜) hline
  exact ((hasDerivAt_betaJ_line α w).unique h1)

theorem det_betaDL : LinearMap.det (betaDL α) = 64 * α 0 ^ 3 * α 1 ^ 2 * α 2 := by
  rw [betaDL, LinearMap.det_toLin', Matrix.det_diagonal]
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 ≤ p.2) (by simp)
    (fun p : Fin 3 × Fin 3 => 2 * α p.1), Finset.prod_filter, Fintype.prod_prod_type]
  simp [Fin.prod_univ_three]
  ring

end Beta

section Coord

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The index of a strictly lower entry $(i,j)$, $i > j$: $(2,1) \mapsto 0$, $(2,0) \mapsto 1$, $(1,0) \mapsto 2$. -/
def lowIdx (i j : Fin 3) : Fin 3 := if i = 2 ∧ j = 1 then 0 else if i = 2 then 1 else 2

/-- The inverse of `eMatL`. -/
def eMatInvL : ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) →ₗ[𝕜] (Fin 3 → Fin 3 → 𝕜) where
  toFun q := fun j i => if h : i ≤ j then q.2 ⟨(i, j), h⟩ else q.1 (lowIdx i j)
  map_add' q q' := by funext j i; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> rfl
  map_smul' t q := by
    funext j i; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl

theorem eMatInvL_eMatL (X : Fin 3 → Fin 3 → 𝕜) : eMatInvL (eMatL X) = X := by
  funext j i
  fin_cases i <;> fin_cases j <;> simp [eMatInvL, eMatL, lowIdx]

theorem eMatL_eMatInvL (q : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) : eMatL (eMatInvL q) = q := by
  ext i
  · fin_cases i <;> simp [eMatInvL, eMatL, lowIdx]
  · obtain ⟨⟨i, j⟩, h⟩ := i
    simp [eMatInvL, eMatL, h]

/-- **Adapted coordinates on $M_3$** as a continuous linear equivalence. -/
def eMatE : (Fin 3 → Fin 3 → 𝕜) ≃L[𝕜] (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) :=
  (LinearEquiv.ofLinear eMatL eMatInvL (LinearMap.ext eMatL_eMatInvL) (LinearMap.ext eMatInvL_eMatL)).toContinuousLinearEquiv

@[simp] theorem eMatE_apply (X : Fin 3 → Fin 3 → 𝕜) : eMatE X = eMatL X := rfl

theorem norm_eMatL_le (X : Fin 3 → Fin 3 → 𝕜) : ‖eMatL X‖ ≤ ‖X‖ := by
  have hX : ∀ j i, ‖X j i‖ ≤ ‖X‖ := fun j i => (norm_le_pi_norm (X j) i).trans (norm_le_pi_norm X j)
  rw [Prod.norm_def, max_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    fin_cases k <;> simp [eMatL, hX]
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => by simp [eMatL, hX]

theorem norm_eMatInvL_le (q : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) : ‖eMatInvL q‖ ≤ ‖q‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simp only [eMatInvL, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · exact (norm_le_pi_norm q.2 _).trans (norm_snd_le q)
  · exact (norm_le_pi_norm q.1 _).trans (norm_fst_le q)

theorem norm_eMatE (X : Fin 3 → Fin 3 → 𝕜) : ‖eMatE X‖ = ‖X‖ := by
  refine le_antisymm (norm_eMatL_le X) ?_
  calc ‖X‖ = ‖eMatInvL (eMatL X)‖ := by rw [eMatInvL_eMatL]
    _ ≤ ‖eMatL X‖ := norm_eMatInvL_le _

theorem preimage_eMatE_ball (r : ℝ) : (eMatE : (Fin 3 → Fin 3 → 𝕜) ≃L[𝕜] _) ⁻¹' ball 0 r = ball 0 r := by
  ext X; simp only [mem_preimage, mem_ball_zero_iff, norm_eMatE]

section Vol

variable [MeasureSpace 𝕜] [BorelSpace 𝕜] [(volume : Measure 𝕜).IsAddHaarMeasure] [SigmaFinite (volume : Measure 𝕜)]

theorem card_uIdx_three : Fintype.card (UIdx 3) = 6 := by decide

instance instAddHaarPiK (ι : Type*) [Fintype ι] : (volume : Measure (ι → 𝕜)).IsAddHaarMeasure := inferInstance

instance instAddHaarE3 : (volume : Measure ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜))).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure volume volume

theorem volume_ball_M : volume (ball (0 : Fin 3 → Fin 3 → 𝕜) 1) = volume (ball (0 : 𝕜) 1) ^ 9 := by
  rw [volume_pi_ball _ one_pos]
  simp only [Pi.zero_apply]
  rw [volume_pi_ball _ one_pos]
  simp [Finset.prod_const, ← pow_mul]

theorem volume_ball_E : volume (ball (0 : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) 1) = volume (ball (0 : 𝕜) 1) ^ 9 := by
  rw [show (0 : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) = (0, 0) from rfl, ← ball_prod_same, Measure.volume_eq_prod,
    Measure.prod_prod, volume_pi_ball _ one_pos, volume_pi_ball _ one_pos]
  simp [Finset.prod_const, card_uIdx_three, ← pow_add]

theorem map_eMatE_volume : (volume : Measure (Fin 3 → Fin 3 → 𝕜)).map eMatE = volume := by
  have hH : ((volume : Measure (Fin 3 → Fin 3 → 𝕜)).map eMatE).IsAddHaarMeasure :=
    (eMatE (𝕜 := 𝕜)).isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (Fin 3 → Fin 3 → 𝕜)).map eMatE)
    (volume : Measure ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)))
  have hball := congrArg (fun μ : Measure ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) => μ (ball 0 1)) h
  simp only [Measure.smul_apply] at hball
  rw [Measure.map_apply eMatE.continuous.measurable measurableSet_ball, preimage_eMatE_ball, volume_ball_M,
    volume_ball_E] at hball
  have hv0 : volume (ball (0 : 𝕜) 1) ^ 9 ≠ 0 := pow_ne_zero _ (measure_ball_pos volume _ one_pos).ne'
  have hvt : volume (ball (0 : 𝕜) 1) ^ 9 ≠ ∞ := ENNReal.pow_ne_top measure_ball_lt_top.ne
  have hc : ((Measure.addHaarScalarFactor ((volume : Measure (Fin 3 → Fin 3 → 𝕜)).map eMatE)
      (volume : Measure ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜))) : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul] at hball
    exact (ENNReal.mul_left_inj hv0 hvt).mp (hball.symm.trans (one_mul _).symm)
  have hc' : Measure.addHaarScalarFactor ((volume : Measure (Fin 3 → Fin 3 → 𝕜)).map eMatE)
      (volume : Measure ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜))) = 1 := by exact_mod_cast hc
  conv_lhs => rw [h]
  rw [hc', one_smul]

theorem volume_image_eMatE (T : Set (Fin 3 → Fin 3 → 𝕜)) :
    volume ((eMatE : (Fin 3 → Fin 3 → 𝕜) ≃L[𝕜] _) '' T) = volume T := by
  set e := (eMatE (𝕜 := 𝕜)).toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin 3 → Fin 3 → 𝕜) → _) = eMatE := rfl
  rw [← map_eMatE_volume, ← he, MeasurableEquiv.map_apply, he,
    preimage_image_eq _ (eMatE (𝕜 := 𝕜)).injective]

/-- **Shear invariance**: $\{(y, u) : y \in S,\ u - P y \in W\}$ has measure $\mathrm{vol}(S)\,\mathrm{vol}(W)$. -/
theorem volume_shear (P : (Fin 3 → 𝕜) →L[𝕜] (UIdx 3 → 𝕜)) {S : Set (Fin 3 → 𝕜)} {W : Set (UIdx 3 → 𝕜)}
    (hS : MeasurableSet S) (hW : MeasurableSet W) :
    volume {p : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) | p.1 ∈ S ∧ p.2 - P p.1 ∈ W} = volume S * volume W := by
  have hm : MeasurableSet {p : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) | p.1 ∈ S ∧ p.2 - P p.1 ∈ W} :=
    (hS.preimage measurable_fst).inter (hW.preimage (measurable_snd.sub (P.continuous.measurable.comp measurable_fst)))
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  have hsl : ∀ y, volume (Prod.mk y ⁻¹' {p : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) | p.1 ∈ S ∧ p.2 - P p.1 ∈ W}) =
      S.indicator (fun _ => volume W) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      have : Prod.mk y ⁻¹' {p : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) | p.1 ∈ S ∧ p.2 - P p.1 ∈ W} =
          (fun u => u + (-P y)) ⁻¹' W := by
        ext u; simp [hy, sub_eq_add_neg]
      rw [this, measure_preimage_add_right]
    · rw [indicator_of_notMem hy]
      have : Prod.mk y ⁻¹' {p : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) | p.1 ∈ S ∧ p.2 - P p.1 ∈ W} = ∅ := by
        ext u; simp [hy]
      rw [this, measure_empty]
  simp_rw [hsl]
  rw [lintegral_indicator_const hS, mul_comm]

end Vol

end Coord

/-! ### The shear sets and their images -/

section Shear

variable {𝕜 : Type*} [RCLike 𝕜] [MeasureSpace 𝕜] [BorelSpace 𝕜] [(volume : Measure 𝕜).IsAddHaarMeasure]
  [SigmaFinite (volume : Measure 𝕜)]

/-- The shear set $\{(y, u) : \|y\| < \delta,\ \|u - Py\| < \delta\}$. -/
def shearSet (P : (Fin 3 → 𝕜) →L[𝕜] (UIdx 3 → 𝕜)) (δ : ℝ) : Set ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) :=
  {p | p.1 ∈ ball 0 δ ∧ p.2 - P p.1 ∈ ball 0 δ}

theorem shearSet_subset_ball (P : (Fin 3 → 𝕜) →L[𝕜] (UIdx 3 → 𝕜)) {δ : ℝ} (hδ : 0 < δ) :
    shearSet P δ ⊆ ball 0 ((1 + ‖P‖) * δ) := by
  rintro ⟨y, u⟩ ⟨hy, hu⟩
  rw [mem_ball_zero_iff] at hy hu ⊢
  rw [Prod.norm_def, max_lt_iff]
  have hP : ‖P y‖ ≤ ‖P‖ * δ := (P.le_opNorm y).trans (mul_le_mul_of_nonneg_left hy.le (norm_nonneg _))
  constructor
  · nlinarith [norm_nonneg P]
  · calc ‖u‖ = ‖(u - P y) + P y‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - P y‖ + ‖P y‖ := norm_add_le _ _
      _ < (1 + ‖P‖) * δ := by nlinarith

theorem volume_shearSet (P : (Fin 3 → 𝕜) →L[𝕜] (UIdx 3 → 𝕜)) (δ : ℝ) :
    volume (shearSet P δ) = volume (ball (0 : Fin 3 → 𝕜) δ) * volume (ball (0 : UIdx 3 → 𝕜) δ) :=
  volume_shear P measurableSet_ball measurableSet_ball

/-- **First-order expansion on the shear sets**: for $g$ with strict derivative $L$ at $0$, the volume of $g(S_\delta)$
is $|\det L|\,\mathrm{vol}(B_\delta)\mathrm{vol}(B'_\delta)$ up to $o(\mathrm{vol})$. -/
theorem eventually_shear_image (P : (Fin 3 → 𝕜) →L[𝕜] (UIdx 3 → 𝕜))
    {g : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) → (Fin 3 → 𝕜) × (UIdx 3 → 𝕜)}
    {L : ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) →L[ℝ] ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜))} (hg : HasStrictFDerivAt g L 0) :
    ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), |(volume (g '' shearSet P δ)).toReal -
      |L.det| * ((volume (ball (0 : Fin 3 → 𝕜) δ)).toReal * (volume (ball (0 : UIdx 3 → 𝕜) δ)).toReal)| ≤
      ε * ((volume (ball (0 : Fin 3 → 𝕜) δ)).toReal * (volume (ball (0 : UIdx 3 → 𝕜) δ)).toReal) := by
  intro ε hε
  obtain ⟨r, hr, hnear⟩ := eventually_image_near volume hg hε
  have hC : 0 < 1 + ‖P‖ := by positivity
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < r / (1 + ‖P‖) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos hr hC))
  filter_upwards [self_mem_nhdsWithin, hev] with δ hδ hδr
  have hsub : shearSet P δ ⊆ ball 0 r := (shearSet_subset_ball P hδ).trans
    (ball_subset_ball (by rw [lt_div_iff₀ hC] at hδr; linarith))
  have hfin : volume (shearSet P δ) ≠ ∞ := by
    rw [volume_shearSet]; exact ENNReal.mul_ne_top measure_ball_lt_top.ne measure_ball_lt_top.ne
  obtain ⟨h1, h2⟩ := hnear _ hsub hfin
  rw [volume_shearSet, ENNReal.toReal_mul] at h1 h2
  rw [abs_le]; constructor <;> nlinarith

end Shear

/-! ### Ratio limits -/

/-- A limit read off from relative bounds. -/
theorem tendsto_div_of_bounds {G v : ℝ → ℝ} {d : ℝ} (hv : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < v δ)
    (h : ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0:ℝ), |G δ - d * v δ| ≤ ε * v δ) :
    Tendsto (fun δ => G δ / v δ) (𝓝[>] 0) (𝓝 d) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hv, h (ε / 2) (by positivity)] with δ hvδ hδ
  rw [Real.dist_eq, show G δ / v δ - d = (G δ - d * v δ) / v δ by field_simp, abs_div, abs_of_pos hvδ,
    div_lt_iff₀ hvδ]
  linarith [mul_pos hε hvδ]

/-- **The ratio limit**: from $L\kappa = G$, $G \approx d_G v_bv_w$ and $\kappa \approx d_Bv_w$, $L/v_b \to d_G/d_B$. -/
theorem tendsto_ratio_of_bounds {L κ G vb vw : ℝ → ℝ} {dG dB : ℝ} (hdB : 0 < dB)
    (hvb : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < vb δ) (hvw : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < vw δ)
    (h1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), L δ * κ δ = G δ)
    (h2 : ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0:ℝ), |G δ - dG * (vb δ * vw δ)| ≤ ε * (vb δ * vw δ))
    (h3 : ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0:ℝ), |κ δ - dB * vw δ| ≤ ε * vw δ) :
    Tendsto (fun δ => L δ / vb δ) (𝓝[>] 0) (𝓝 (dG / dB)) := by
  have tG := tendsto_div_of_bounds (hvb.and hvw |>.mono fun δ h => mul_pos h.1 h.2) h2
  have tK := tendsto_div_of_bounds hvw h3
  refine (tG.div tK hdB.ne').congr' ?_
  filter_upwards [hvb, hvw, h1, h3 (dB / 2) (by positivity)] with δ hb hw hL hK
  have hκ : 0 < κ δ := by
    have := (abs_le.mp hK).1
    nlinarith
  simp only [Pi.div_apply]
  rw [← hL]
  field_simp

/-- **The ratio limit, limit form**: from $L\kappa = G$, $G/(v_bv_w) \to d_G$, $\kappa/v_w \to d_B \ne 0$:
$L/v_b \to d_G/d_B$. -/
theorem tendsto_ratio_of_tendsto {L κ G vb vw : ℝ → ℝ} {dG dB : ℝ} (hdB : dB ≠ 0)
    (hvb : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < vb δ) (hvw : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < vw δ)
    (h1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), L δ * κ δ = G δ)
    (tG : Tendsto (fun δ => G δ / (vb δ * vw δ)) (𝓝[>] 0) (𝓝 dG))
    (tK : Tendsto (fun δ => κ δ / vw δ) (𝓝[>] 0) (𝓝 dB)) :
    Tendsto (fun δ => L δ / vb δ) (𝓝[>] 0) (𝓝 (dG / dB)) := by
  refine (tG.div tK hdB).congr' ?_
  have hK : ∀ᶠ δ in 𝓝[>] (0:ℝ), κ δ / vw δ ≠ 0 := tK.eventually_ne hdB
  filter_upwards [hvb, hvw, h1, hK] with δ hb hw hL hk
  have hκ : κ δ ≠ 0 := fun h => hk (by rw [h, zero_div])
  simp only [Pi.div_apply]
  rw [← hL]
  field_simp

/-- $\mathrm{vol}(B_\delta)/\mathrm{vol}(B_\delta) \to 1$-type positivity: balls have positive finite volume. -/
theorem toReal_volume_ball_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {δ : ℝ} (hδ : 0 < δ) :
    0 < (μ (ball (0 : E) δ)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos μ _ hδ).ne' measure_ball_lt_top.ne

end QuadFormsKB.Tamagawa.Measure.Weil
