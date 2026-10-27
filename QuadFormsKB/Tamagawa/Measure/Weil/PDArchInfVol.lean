import QuadFormsKB.Tamagawa.Measure.Weil.PDArchGlobal

/-!
# The archimedean quotient mass of a small box

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus0$, $D\otimes F_\infty$ with Weil's measure
$\omega^{D^\times}_\infty = \|\operatorname{nrd}x\|_\infty^{-2}dx$ (`omegaQuatInf`) and $\omega_\infty = \|t\|^{-1}dt$ on
$F_\infty^\times$ (`omegaInf`), self-dual Haar measures.

**Proves** `tendsto_box_ratio`: for $T_\delta = \{\|t - 1\| < \delta\}$ and $S_\delta = T_\delta(1 + B_\delta)$,
$$\frac{\omega^{D^\times}_\infty(S_\delta)}{\omega_\infty(T_\delta)\,\mathrm{vol}(B_\delta)} \longrightarrow 1\qquad(\delta\to0^+),$$
i.e. Weil's quotient measure $\omega^{D^\times}_\infty/\omega_\infty$ on $PD^\times(F_\infty)$ has density $1$ at the identity in
the chart $y \mapsto [1+y]$. Ingredients: the densities $\Delta(u)^{-1}$ of both measures are continuous and equal to $1$
at $1$ (`unitsHaar_near_one`), and $(t, y) \mapsto (t, ty)$ has derivative the identity at $(1, 0)$ (`hasStrictFDerivAt_phiTY`,
the first-order lemma `ArchFirstOrder`).
-/

open MeasureTheory Set Metric Filter Topology Quaternion NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta

section UnitsHaarNear

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [MeasurableSpace R] [BorelSpace R] [MeasurableSpace Rˣ] [BorelSpace Rˣ] [T2Space R]

/-- **$\omega = \Delta(u)^{-1}d\nu$ is $\nu$ to first order at $1$**: for every $\varepsilon > 0$ there is a
neighbourhood $U$ of $1$ on which $(1-\varepsilon)\nu \le \omega \le (1+\varepsilon)\nu$. -/
theorem unitsHaar_near_one (hval : Topology.IsOpenEmbedding (Units.val : Rˣ → R))
    (hΔ : Continuous (distribHaarChar R : Rˣ → ℝ≥0)) (ν : Measure R) [ν.IsAddHaarMeasure] [ν.Regular]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : Rˣ), ∀ A ⊆ U, MeasurableSet A →
      ENNReal.ofReal (1 - ε) * ν (Units.val '' A) ≤ unitsHaar R ν A ∧
        unitsHaar R ν A ≤ ENNReal.ofReal (1 + ε) * ν (Units.val '' A) := by
  have hc : Continuous fun u : Rˣ => ((distribHaarChar R u⁻¹ : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (hΔ.comp continuous_inv)
  have h1 : ((distribHaarChar R (1 : Rˣ)⁻¹ : ℝ≥0) : ℝ) = 1 := by simp
  have hU : (fun u : Rˣ => ((distribHaarChar R u⁻¹ : ℝ≥0) : ℝ)) ⁻¹' Ioo (1 - ε) (1 + ε) ∈ 𝓝 (1 : Rˣ) :=
    hc.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by rw [h1]; linarith) (by rw [h1]; linarith))
  refine ⟨_, hU, fun A hA hAm => ?_⟩
  have he := measurableEmbedding_val hval
  rw [unitsHaar_apply hval hΔ ν hAm, ← he.comap_apply ν A]
  constructor
  · rw [← setLIntegral_const]
    refine setLIntegral_mono' hAm fun u hu => ?_
    have := (hA hu).1
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal this.le
  · rw [← setLIntegral_const]
    refine setLIntegral_mono' hAm fun u hu => ?_
    have := (hA hu).2
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal this.le

end UnitsHaarNear

open scoped Classical

section Box

variable {F : Type} [Field F] [NumberField F]

/-- $(t, y) \mapsto (t, ty)$. -/
def phiTY (p : mixedSpace F × (Fin 3 → mixedSpace F)) : mixedSpace F × (Fin 3 → mixedSpace F) :=
  (p.1, fun i => p.1 * p.2 i)

theorem hasStrictFDerivAt_phiTY : ∃ L : (mixedSpace F × (Fin 3 → mixedSpace F)) →L[ℝ]
    (mixedSpace F × (Fin 3 → mixedSpace F)),
    HasStrictFDerivAt (phiTY (F := F)) L ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) ∧ ∀ v, L v = v := by
  set x₀ : mixedSpace F × (Fin 3 → mixedSpace F) := ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F))
  have h1 := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := x₀))
  have h2 : ∀ i : Fin 3, HasStrictFDerivAt (fun p : mixedSpace F × (Fin 3 → mixedSpace F) => p.1 * p.2 i)
      (x₀.1 • ((ContinuousLinearMap.proj (R := ℝ) i).comp (ContinuousLinearMap.snd ℝ (mixedSpace F) _)) +
        x₀.2 i • ContinuousLinearMap.fst ℝ (mixedSpace F) (Fin 3 → mixedSpace F)) x₀ := by
    intro i
    exact h1.mul ((hasStrictFDerivAt_apply i _).comp x₀ (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := x₀)))
  refine ⟨_, h1.prodMk (hasStrictFDerivAt_pi.2 h2), fun v => ?_⟩
  refine Prod.ext rfl (funext fun i => ?_)
  simp [x₀]


/-- **First-order expansion on balls at a point.** -/
theorem tendsto_image_ball_div_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) :
    Tendsto (fun δ => (μ (f '' ball x δ)).toReal / (μ (ball x δ)).toReal) (𝓝[>] 0) (𝓝 |L.det|) := by
  refine tendsto_div_of_bounds (eventually_mem_nhdsWithin.mono fun δ hδ =>
    ENNReal.toReal_pos (measure_ball_pos μ _ hδ).ne' measure_ball_lt_top.ne) ?_
  intro ε hε
  obtain ⟨r, hr, hnear⟩ := eventually_image_near μ hf hε
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hr)] with δ hδ
  obtain ⟨h1, h2⟩ := hnear _ (ball_subset_ball (le_of_lt hδ)) measure_ball_lt_top.ne
  rw [abs_le]; constructor <;> nlinarith

theorem isUnit_of_mem_ball_one {x : mixedSpace F} (hx : x ∈ ball (1 : mixedSpace F) 1) : IsUnit x := by
  have h : ‖1 - x‖ < 1 := by rw [norm_sub_rev, ← dist_eq_norm]; exact hx
  simpa using (Units.oneSub (1 - x) h).isUnit

variable (F) in
/-- $T_\delta = \{t \in F_\infty^\times : \|t - 1\| < \delta\}$. -/
def tBall (δ : ℝ) : Set (mixedSpace F)ˣ := Units.val ⁻¹' ball (1 : mixedSpace F) δ

theorem measurableSet_tBall (δ : ℝ) : MeasurableSet (tBall F δ) :=
  isOpen_ball.measurableSet.preimage Units.continuous_val.measurable

theorem image_val_tBall {δ : ℝ} (hδ : δ ≤ 1) : Units.val '' tBall F δ = ball (1 : mixedSpace F) δ := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    exact ⟨(isUnit_of_mem_ball_one (ball_subset_ball hδ hx)).unit, hx, rfl⟩

/-- From two-sided multiplicative bounds to a real-number estimate. -/
theorem abs_toReal_sub_le_of_bounds {m v : ℝ≥0∞} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hv : v ≠ ∞)
    (h1 : ENNReal.ofReal (1 - ε) * v ≤ m) (h2 : m ≤ ENNReal.ofReal (1 + ε) * v) :
    |m.toReal - 1 * v.toReal| ≤ ε * v.toReal := by
  have hm : m ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv) h2
  have a1 := ENNReal.toReal_mono hm h1
  have a2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at a1 a2
  rw [abs_le]; constructor <;> nlinarith

/-- $\omega_\infty(T_\delta)/\mathrm{vol}(B_\delta(1)) \to 1$. -/
theorem tendsto_omegaInf_tBall :
    Tendsto (fun δ => (omegaInf F (tBall F δ)).toReal / (Analysis.selfDualInf (F := F) (ball 1 δ)).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  refine tendsto_div_of_bounds (eventually_mem_nhdsWithin.mono fun δ hδ =>
    ENNReal.toReal_pos (measure_ball_pos _ _ hδ).ne' measure_ball_lt_top.ne) ?_
  intro ε hε
  set ε' := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  obtain ⟨U, hU, hbd⟩ := unitsHaar_near_one isOpenEmbedding_val_mixedSpace continuous_distribHaarChar_mixedSpace
    (Analysis.selfDualInf (F := F)) hε'
  rw [isOpenEmbedding_val_mixedSpace.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp hW
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hr one_pos))] with δ hδ
  have hδr : δ < r := hδ.trans_le (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (le_of_lt hδ).trans (min_le_right _ _)
  have hsub : tBall F δ ⊆ U := fun u hu => hWU (hrW (ball_subset_ball hδr.le hu))
  obtain ⟨h1, h2⟩ := hbd _ hsub (measurableSet_tBall δ)
  rw [image_val_tBall hδ1] at h1 h2
  have := abs_toReal_sub_le_of_bounds hε' (by
    have : ε' ≤ 1 / 2 := min_le_right _ _; linarith) measure_ball_lt_top.ne h1 h2
  exact this.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ENNReal.toReal_nonneg)

end Box

/-! ### The box $T_\delta(1 + B_\delta)$ in $(D\otimes F_\infty)^\times$ -/

section QuatBox

variable {F : Type} [Field F] [NumberField F] (a b : 𝓞 F)

/-- $S_\delta = T_\delta(1 + B_\delta) \subseteq (D\otimes F_\infty)^\times$. -/
def sBall (δ : ℝ) : Set (QuatInf (a : F) (b : F))ˣ := sInf a b (tBall F δ) (ball 0 δ)

theorem measurableSet_sBall (δ : ℝ) : MeasurableSet (sBall a b δ) :=
  measurableSet_sInf a b (measurableSet_tBall δ) measurableSet_ball

theorem nrdInf_one_add_pureI (y : Fin 3 → mixedSpace F) :
    nrdInf (a : F) (b : F) (1 + pureI a b y) = 1 + (-(mixedEmbedding F (a : F)) * y 0 ^ 2 -
      mixedEmbedding F (b : F) * y 1 ^ 2 + mixedEmbedding F (a : F) * mixedEmbedding F (b : F) * y 2 ^ 2) := by
  simp [nrdInf, pureI]; ring

variable (F) in
/-- A radius below which $1 + y$ is a unit of $D\otimes F_\infty$. -/
def rQ : ℝ := min 1 (1 / (1 + ‖mixedEmbedding F (a : F)‖ + ‖mixedEmbedding F (b : F)‖ +
  ‖mixedEmbedding F (a : F) * mixedEmbedding F (b : F)‖))

theorem rQ_pos : 0 < rQ F a b := lt_min one_pos (by positivity)

theorem isUnit_one_add_pureI {y : Fin 3 → mixedSpace F} (hy : ‖y‖ < rQ F a b) :
    IsUnit (1 + pureI a b y) := by
  rw [isUnit_iff_isUnit_nrdInf, nrdInf_one_add_pureI]
  set A := mixedEmbedding F (a : F)
  set B := mixedEmbedding F (b : F)
  set q := -A * y 0 ^ 2 - B * y 1 ^ 2 + A * B * y 2 ^ 2
  have hy1 : ‖y‖ < 1 := hy.trans_le (min_le_left _ _)
  have hy2 : ‖y‖ < 1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖) := hy.trans_le (min_le_right _ _)
  have h0 : ‖y 0‖ ≤ ‖y‖ := norm_le_pi_norm y 0
  have h1 : ‖y 1‖ ≤ ‖y‖ := norm_le_pi_norm y 1
  have h2 : ‖y 2‖ ≤ ‖y‖ := norm_le_pi_norm y 2
  have hq : ‖q‖ ≤ (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ ^ 2 := by
    have e0 : ‖y 0 ^ 2‖ ≤ ‖y‖ ^ 2 := (norm_pow_le' _ two_pos).trans (pow_le_pow_left₀ (norm_nonneg _) h0 2)
    have e1 : ‖y 1 ^ 2‖ ≤ ‖y‖ ^ 2 := (norm_pow_le' _ two_pos).trans (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    have e2 : ‖y 2 ^ 2‖ ≤ ‖y‖ ^ 2 := (norm_pow_le' _ two_pos).trans (pow_le_pow_left₀ (norm_nonneg _) h2 2)
    calc ‖q‖ ≤ ‖A‖ * ‖y 0 ^ 2‖ + ‖B‖ * ‖y 1 ^ 2‖ + ‖A * B‖ * ‖y 2 ^ 2‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [neg_mul, norm_neg]; exact norm_mul_le _ _
          · exact norm_mul_le _ _
          · exact norm_mul_le _ _
      _ ≤ (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ ^ 2 := by
          nlinarith [norm_nonneg A, norm_nonneg B, norm_nonneg (A * B)]
  have hc : 0 < 1 + ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
  have hlt : ‖q‖ < 1 := by
    have hyy : ‖y‖ ^ 2 ≤ ‖y‖ := by nlinarith [norm_nonneg y]
    have : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖y‖ < 1 := by
      rw [lt_div_iff₀ hc] at hy2; nlinarith [norm_nonneg y]
    nlinarith [norm_nonneg A, norm_nonneg B, norm_nonneg (A * B), norm_nonneg y]
  refine isUnit_of_mem_ball_one ?_
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hlt

theorem image_val_sBall {δ : ℝ} (hδ : δ ≤ rQ F a b) :
    Units.val '' sBall a b δ = boxMap a b '' (tBall F δ ×ˢ ball 0 δ) := by
  ext x
  constructor
  · rintro ⟨u, ⟨t, ht, y, hy, h⟩, rfl⟩
    exact ⟨(t, y), ⟨ht, hy⟩, h.symm⟩
  · rintro ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
    have hu : IsUnit (boxMap a b (t, y)) :=
      (t.isUnit.map (algebraMap (mixedSpace F) (QuatInf (a : F) (b : F)))).mul
        (isUnit_one_add_pureI a b ((mem_ball_zero_iff.mp hy).trans_le hδ))
    exact ⟨hu.unit, ⟨t, ht, y, hy, rfl⟩, rfl⟩

/-- The coordinates of $t(1+y)$: $(t, ty_0, ty_1, ty_2)$. -/
def psiTY (p : mixedSpace F × (Fin 3 → mixedSpace F)) : Fin 4 → mixedSpace F :=
  ![p.1, p.1 * p.2 0, p.1 * p.2 1, p.1 * p.2 2]

theorem quatInfCLE_boxMap (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) :
    quatInfCLE (a : F) (b : F) (boxMap a b p) = psiTY ((p.1 : mixedSpace F), p.2) := by
  funext i
  fin_cases i <;> simp [quatInfCLE, psiTY, boxMap_re, boxMap_imI, boxMap_imJ, boxMap_imK]

theorem piFinSuccAbove_psiTY (p : mixedSpace F × (Fin 3 → mixedSpace F)) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => mixedSpace F) 0 (psiTY p) = phiTY p := by
  refine Prod.ext rfl (funext fun j => ?_)
  fin_cases j <;> rfl

/-- **The coordinate volume of the box** $S_\delta$ is the volume of the image of a ball under $(t,y)\mapsto(t,ty)$. -/
theorem quatInfVol_sBall {δ : ℝ} (hδ1 : δ ≤ 1) (hδ : δ ≤ rQ F a b) :
    quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ) =
      ((Analysis.selfDualInf (F := F)).prod (Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F)))
        (phiTY '' ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ) := by
  set e := (quatInfCLE (a : F) (b : F)).toHomeomorph.toMeasurableEquiv
  set e4 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => mixedSpace F) 0
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin 4 => Analysis.selfDualInf (F := F)) 0
  have h1 : quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ) =
      muInfVec F (Fin 4) (e '' (Units.val '' sBall a b δ)) := by
    have : quatInfVol (a : F) (b : F) = (muInfVec F (Fin 4)).map e.symm := rfl
    rw [this, MeasurableEquiv.map_apply, MeasurableEquiv.preimage_symm]
  have h2 : e '' (Units.val '' sBall a b δ) = psiTY '' (ball (1 : mixedSpace F) δ ×ˢ ball 0 δ) := by
    rw [image_val_sBall a b hδ, image_image, ← image_val_tBall hδ1]
    ext z
    constructor
    · rintro ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
      exact ⟨((t : mixedSpace F), y), ⟨⟨t, ht, rfl⟩, hy⟩, (quatInfCLE_boxMap a b (t, y)).symm⟩
    · rintro ⟨⟨s, y⟩, ⟨⟨t, ht, rfl⟩, hy⟩, rfl⟩
      exact ⟨(t, y), ⟨ht, hy⟩, quatInfCLE_boxMap a b (t, y)⟩
  rw [h1, h2]
  have h3 : muInfVec F (Fin 4) (psiTY '' (ball (1 : mixedSpace F) δ ×ˢ ball 0 δ)) =
      ((Measure.pi fun _ : Fin 4 => Analysis.selfDualInf (F := F)).map e4)
        (e4 '' (psiTY '' (ball (1 : mixedSpace F) δ ×ˢ ball 0 δ))) := by
    rw [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image]
  rw [h3, hmp.map_eq, image_image, ← ball_prod_same (1 : mixedSpace F) (0 : Fin 3 → mixedSpace F) δ]
  congr 1
  exact image_congr fun p _ => piFinSuccAbove_psiTY p

theorem quatInfCLE_one : quatInfCLE (a : F) (b : F) 1 = ![1, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [quatInfCLE]

/-- **The box shrinks to $1$**: every neighbourhood of $1$ in $(D\otimes F_\infty)^\times$ contains $S_\delta$ for small
$\delta$. -/
theorem sBall_subset_of_mem_nhds {U : Set (QuatInf (a : F) (b : F))ˣ} (hU : U ∈ 𝓝 (1 : (QuatInf (a : F) (b : F))ˣ)) :
    ∃ r > (0 : ℝ), ∀ δ, δ < r → sBall a b δ ⊆ U := by
  rw [(isOpenEmbedding_val_quatInf (a : F) (b : F)).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  rw [Units.val_one, (isInducing_quatInfCoord (a : F) (b : F)).nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨W', hW', hW'W⟩ := hW
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hW'
  refine ⟨min 1 (ρ / 2), lt_min one_pos (by positivity), fun δ hδ u hu => ?_⟩
  have hδ1 : δ < 1 := hδ.trans_le (min_le_left _ _)
  have hδρ : δ < ρ / 2 := hδ.trans_le (min_le_right _ _)
  obtain ⟨t, ht, y, hy, hxu⟩ := hu
  apply hWU
  apply hW'W
  apply hball
  have hc : quatInfCoord (a : F) (b : F) (u : QuatInf (a : F) (b : F)) = psiTY ((t : mixedSpace F), y) := by
    rw [hxu]; exact quatInfCLE_boxMap a b (t, y)
  rw [hc, show quatInfCoord (a : F) (b : F) 1 = ![1, 0, 0, 0] from quatInfCLE_one a b]
  have ht' : dist (t : mixedSpace F) 1 < δ := ht
  have hy' : ‖y‖ < δ := mem_ball_zero_iff.mp hy
  have htn : ‖(t : mixedSpace F)‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' (t : mixedSpace F) 1
    rw [← dist_eq_norm] at this
    have h1 : ‖(1 : mixedSpace F)‖ ≤ 1 := by
      rw [Prod.norm_def]
      exact max_le ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp)
        ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp)
    linarith
  have hty : ∀ j, ‖(t : mixedSpace F) * y j‖ < ρ := fun j => by
    calc ‖(t : mixedSpace F) * y j‖ ≤ ‖(t : mixedSpace F)‖ * ‖y j‖ := norm_mul_le _ _
      _ ≤ 2 * ‖y‖ := mul_le_mul htn (norm_le_pi_norm y j) (norm_nonneg _) (by norm_num)
      _ < ρ := by linarith
  rw [Metric.mem_ball, dist_pi_lt_iff hρ]
  intro i
  fin_cases i
  · simp [psiTY]; linarith
  · simpa [psiTY, dist_eq_norm] using hty 0
  · simpa [psiTY, dist_eq_norm] using hty 1
  · simpa [psiTY, dist_eq_norm] using hty 2

variable (F) in
/-- The coordinate measure on $F_\infty\times F_\infty^3$. -/
abbrev muE : Measure (mixedSpace F × (Fin 3 → mixedSpace F)) :=
  (Analysis.selfDualInf (F := F)).prod (Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F))

instance : (muE F).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem tendsto_phiTY_ball :
    Tendsto (fun δ => (muE F (phiTY '' ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ)).toReal /
      (muE F (ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨L, hL, hLid⟩ := hasStrictFDerivAt_phiTY (F := F)
  have hL1 : L = ContinuousLinearMap.id ℝ _ := ContinuousLinearMap.ext hLid
  have h := tendsto_image_ball_div_at (muE F) hL
  rwa [hL1, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one] at h

theorem muE_phiTY_ne_top (δ : ℝ) :
    muE F (phiTY '' ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ) ≠ ∞ := by
  have hc : Continuous (phiTY (F := F)) :=
    continuous_fst.prodMk (continuous_pi fun i => continuous_fst.mul ((continuous_apply i).comp continuous_snd))
  exact ((measure_mono (image_mono ball_subset_closedBall)).trans_lt
    ((isCompact_closedBall _ δ).image hc).measure_lt_top).ne

/-- $\omega^{D^\times}_\infty(S_\delta)/\mathrm{vol}(S_\delta) \to 1$. -/
theorem tendsto_omegaQuatInf_sBall :
    Tendsto (fun δ => (omegaQuatInf (a : F) (b : F) (sBall a b δ)).toReal /
      (quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < min 1 (rQ F a b) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min one_pos (rQ_pos a b)))
  have hvol : ∀ᶠ δ in 𝓝[>] (0 : ℝ), quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ) =
      muE F (phiTY '' ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ) :=
    hsmall.mono fun δ hδ => quatInfVol_sBall a b ((le_of_lt hδ).trans (min_le_left _ _))
      ((le_of_lt hδ).trans (min_le_right _ _))
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < (quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ)).toReal := by
    have h1 := (tendsto_phiTY_ball (F := F)).eventually (lt_mem_nhds (zero_lt_one))
    filter_upwards [h1, hvol, eventually_mem_nhdsWithin] with δ hδ hv hδ0
    rw [hv]
    have hb : 0 < (muE F (ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos _ _ hδ0).ne' measure_ball_lt_top.ne
    by_contra hneg
    push Not at hneg
    have : (muE F (phiTY '' ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ)).toReal /
        (muE F (ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ)).toReal ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hneg hb.le
    linarith
  refine tendsto_div_of_bounds hpos ?_
  intro ε hε
  set ε' := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  obtain ⟨U, hU, hbd⟩ := unitsHaar_near_one (isOpenEmbedding_val_quatInf (a : F) (b : F))
    (continuous_distribHaarChar_quatInf (a : F) (b : F)) (quatInfVol (a : F) (b : F)) hε'
  obtain ⟨r, hr, hsub⟩ := sBall_subset_of_mem_nhds a b hU
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hr), hvol] with δ hδ hv
  obtain ⟨h1, h2⟩ := hbd _ (hsub δ hδ) (measurableSet_sBall a b δ)
  have hfin : quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ) ≠ ∞ := by rw [hv]; exact muE_phiTY_ne_top δ
  have := abs_toReal_sub_le_of_bounds hε' (by
    have : ε' ≤ 1 / 2 := min_le_right _ _; linarith) hfin h1 h2
  exact this.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ENNReal.toReal_nonneg)

/-- **The archimedean quotient mass of the box, to first order**:
$\dfrac{\omega^{D^\times}_\infty(S_\delta)}{\omega_\infty(T_\delta)\,\mathrm{vol}(B_\delta)} \to 1$, where
$\mathrm{vol}$ is the self-dual measure on $F_\infty^3$. -/
theorem tendsto_box_ratio :
    Tendsto (fun δ => ((omegaQuatInf (a : F) (b : F) (sBall a b δ)).toReal / (omegaInf F (tBall F δ)).toReal) /
      ((Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F)) (ball 0 δ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  have t1 := tendsto_omegaQuatInf_sBall a b
  have t2 := tendsto_phiTY_ball (F := F)
  have t3 := tendsto_omegaInf_tBall (F := F)
  have h := (t1.mul t2).div t3 one_ne_zero
  rw [mul_one, div_one] at h
  refine h.congr' ?_
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < min 1 (rQ F a b) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min one_pos (rQ_pos a b)))
  have hT0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (omegaInf F (tBall F δ)).toReal ≠ 0 :=
    t3.eventually_ne one_ne_zero |>.mp (Eventually.of_forall fun δ h h0 => h (by rw [h0, zero_div]))
  have hq0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ)).toReal ≠ 0 :=
    t1.eventually_ne one_ne_zero |>.mp (Eventually.of_forall fun δ h h0 => h (by rw [h0, div_zero]))
  filter_upwards [hsmall, hT0, hq0, eventually_mem_nhdsWithin] with δ hδ hT hq hδ0
  have hδ1 : δ ≤ 1 := (le_of_lt hδ).trans (min_le_left _ _)
  have hδr : δ ≤ rQ F a b := (le_of_lt hδ).trans (min_le_right _ _)
  have hδ0' : (0 : ℝ) < δ := hδ0
  have hq' : muE F (phiTY '' ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ) =
      quatInfVol (a : F) (b : F) (Units.val '' sBall a b δ) := (quatInfVol_sBall a b hδ1 hδr).symm
  simp only [Pi.div_apply]
  rw [hq']
  have hball : muE F (ball ((1 : mixedSpace F), (0 : Fin 3 → mixedSpace F)) δ) =
      Analysis.selfDualInf (F := F) (ball 1 δ) *
        (Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F)) (ball 0 δ) := by
    rw [← ball_prod_same (1 : mixedSpace F) (0 : Fin 3 → mixedSpace F) δ, muE, Measure.prod_prod]
  rw [hball, ENNReal.toReal_mul]
  have h1 : (Analysis.selfDualInf (F := F) (ball 1 δ)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (measure_ball_pos _ _ hδ0').ne' measure_ball_lt_top.ne).ne'
  have h3 : ((Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F)) (ball 0 δ)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (measure_ball_pos _ _ hδ0').ne' measure_ball_lt_top.ne).ne'
  field_simp

end QuatBox

end QuadFormsKB.Tamagawa.Measure.Weil
