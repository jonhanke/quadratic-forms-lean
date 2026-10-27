import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.TauSOOne

/-!
# The adelic covolume of $SO_1$ for Weil's Tamagawa measure

**Layer:** number fields. $F$ is a number field and $Q_0 = \langle c\rangle = c\,x_0^2$ a nondegenerate form in one
variable over $\mathcal O_F$ ($c\ne0$), any signature at the real places, complex places allowed.

In dimension $1$ the group $SO(V)$ is trivial over every field ($g^{\mathsf T}(2c)g = 2c$ and $\det g = 1$ force $g = 1$),
so $SO(V)(\mathbb A)$ and $SO(V)(F)$ are trivial and the covolume is the total mass of Weil's Tamagawa measure
`muTam Q₀ hQ 1` (MuTamSO.lean, convergence factors $\lambda_v = 1$):
$$\mathrm{covol} = c_F\,2^{0}\cdot\prod_{w\ \mathrm{real}}\frac1{|2c|_w}\cdot\prod_{w\ \mathrm{complex}}\frac1{|2c|_w^{2}}
\cdot\prod_{\mathfrak p}N\mathfrak p^{v_\mathfrak p(2c)} = 1$$
($c_F = |d_F|^{0} = 1$; the archimedean Leray masses of the one-point groups; the local densities
$\alpha_\mathfrak p(\langle c\rangle,\langle c\rangle) = N\mathfrak p^{v_\mathfrak p(2c)}$, `siegelDensity_rankOne`); the
product formula for $2c$ gives $1$.

**Proves**
* `subsingleton_SOAdele`: $SO(V)(\mathbb A)$ is trivial; `covolume_eq_univ`: the covolume is the total mass;
* `lerayMeasure_univ_rankOne`, `lerayMeasureC_univ_rankOne`: the Leray masses $1/|2a|$ of $SO_1(\mathbb R)$ (either sign
  of $a$) and $1/|2a|^2$ of $SO_1(\mathbb C)$;
* `muTam_univ_rankOne`: the total mass of `muTam` is the combinatorial `tamagawaK Q₀`, which is $1$
  (`tamagawaK_rankOne_eq_one`);
* **`covolume_muTam_rankOne`**: $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) = 1$ for every
  nondegenerate $Q_0$ in one variable over every number field: **unconditional**.
-/

open MeasureTheory

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F]

open Matrix QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.LerayArch QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.ArchVol

theorem gl_one_eq_one {R : Type*} [CommRing R]
    (g : GL (Fin 1) R) (h2 : (g : Matrix (Fin 1) (Fin 1) R).det = 1) : g = 1 := by
  rw [Matrix.det_fin_one] at h2
  ext i j
  fin_cases i; fin_cases j
  simpa using h2

theorem subsingleton_archSO (Q : QuadForm ℝ 1) : Subsingleton (ArchSO Q) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : ArchSO Q, x = 1 := fun x =>
    Subtype.ext (gl_one_eq_one _ ((mem_soReal_iff Q _).mp x.2).2)
  rw [key a, key b]

theorem subsingleton_archSOC (Q : QuadForm ℂ 1) : Subsingleton (ArchSOC Q) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : ArchSOC Q, x = 1 := fun x =>
    Subtype.ext (gl_one_eq_one _ ((mem_soC_iff Q _).mp x.2).2)
  rw [key a, key b]

theorem subsingleton_SOAf (Q₀ : QuadForm (𝓞 F) 1) : Subsingleton (SOAf Q₀) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : SOAf Q₀, x = 1 := fun x => by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    apply Subtype.ext
    exact gl_one_eq_one _ (x.2 v)
  rw [key a, key b]

theorem subsingleton_SOAdele (Q₀ : QuadForm (𝓞 F) 1) : Subsingleton (SOAdele Q₀) := by
  have := subsingleton_SOAf Q₀
  have h1 : ∀ w : {w : InfinitePlace F // w.IsReal}, Subsingleton (ArchSO (QRe Q₀ w)) :=
    fun w => subsingleton_archSO _
  have h2 : ∀ w : {w : InfinitePlace F // w.IsComplex}, Subsingleton (ArchSOC (QCx Q₀ w)) :=
    fun w => subsingleton_archSOC _
  have : Subsingleton (GInfSO Q₀) := by unfold GInfSO ArchGroup; infer_instance
  infer_instance

theorem covolume_eq_univ (Q₀ : QuadForm (𝓞 F) 1) (μ : Measure (SOAdele Q₀)) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) μ = μ Set.univ := by
  have h0 := subsingleton_SOAdele Q₀
  have hG : Subsingleton (GammaSOAdele Q₀) := ⟨fun a b => Subtype.ext (h0.elim _ _)⟩
  have hc := countable_GammaSOAdele Q₀
  have hs : ∀ (c : GammaSOAdele Q₀) (x : SOAdele Q₀), c • x = x := fun c x => h0.elim _ _
  have hm : MeasurableConstSMul (GammaSOAdele Q₀) (SOAdele Q₀) :=
    ⟨fun c => by
      have : (fun x : SOAdele Q₀ => c • x) = id := funext (hs c)
      rw [this]; exact measurable_id⟩
  have hi : SMulInvariantMeasure (GammaSOAdele Q₀) (SOAdele Q₀) μ :=
    ⟨fun c s _ => by
      have : (fun x : SOAdele Q₀ => c • x) = id := funext (hs c)
      rw [this]; rfl⟩
  have hfd : IsFundamentalDomain (GammaSOAdele Q₀) (Set.univ : Set (SOAdele Q₀)) μ :=
    ⟨nullMeasurableSet_univ, Filter.Eventually.of_forall fun x => ⟨⟨1, one_mem _⟩, Set.mem_univ _⟩,
      fun g h hgh => absurd (hG.elim g h) hgh⟩
  exact hfd.covolume_eq_volume μ


open scoped Classical in
theorem prod_embeddings_eq (g : ℝ → ℝ) (x : F) :
    ∏ σ : F →ₐ[ℚ] ℂ, g ‖σ x‖ =
      (∏ w : {w : InfinitePlace F // w.IsReal}, g (w.1 x)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (g (w.1 x)) ^ 2 := by
  set G : InfinitePlace F → ℝ := fun w => g (w x)
  have h1 : ∏ σ : F →ₐ[ℚ] ℂ, g ‖σ x‖ = ∏ φ : F →+* ℂ, G (InfinitePlace.mk φ) := by
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => G (InfinitePlace.mk φ))
      (fun σ => g ‖σ x‖)]
    intro φ
    simp only [G, InfinitePlace.apply, RingHom.equivRatAlgHom_apply]
    rfl
  have h2 : ∏ φ : F →+* ℂ, G (InfinitePlace.mk φ) = ∏ w : InfinitePlace F, G w ^ w.mult := by
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => G (InfinitePlace.mk φ))]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Finset.prod_congr rfl fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2], Finset.prod_const,
      InfinitePlace.card_filter_mk_eq]
  rw [h1, h2, ← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    have : (w : InfinitePlace F).mult = 1 := by simp [InfinitePlace.mult, w.2]
    simp [this, G]
  · refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have : (w : InfinitePlace F).mult = 2 := by simp [InfinitePlace.mult, w.2]
    simp [this, G]


section RealMass
open Filter Topology Set
open scoped Classical

/-- Averages of a function continuous at `x₀` (value `1`) over shrinking regions. -/
theorem tendsto_avg_squeeze {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] (μ : Measure α)
    {x₀ : α} {f : α → ℝ} (hf : ContinuousAt f x₀) (hf1 : f x₀ = 1)
    {R : ℝ → Set α} {B V : ℝ → ℝ} {L : ℝ}
    (hshrink : ∀ η > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), R ε ⊆ Metric.ball x₀ η)
    (hfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ (R ε) < ⊤)
    (hV : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ.real (R ε) = V ε)
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntegrableOn f (R ε) μ)
    (hB : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < B ε)
    (hlim : Tendsto (fun ε => V ε / B ε) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε => (∫ X in R ε, f X ∂μ) / B ε) (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhds] at hlim ⊢
  intro e he
  have hLb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), V ε / B ε < |L| + 1 := by
    have := hlim 1 one_pos
    filter_upwards [this] with ε hε
    have h2 : V ε / B ε - L < 1 := by
      have := (abs_lt.mp (show |V ε / B ε - L| < 1 from hε)).2
      exact this
    have := le_abs_self L
    linarith
  set η : ℝ := e / (2 * (|L| + 1)) with hη
  have hLpos : 0 < |L| + 1 := by positivity
  have hηpos : 0 < η := by positivity
  have hcont : ∀ᶠ y in 𝓝 x₀, |f y - 1| < η := by
    have := hf.eventually (Metric.ball_mem_nhds (f x₀) hηpos)
    filter_upwards [this] with y hy
    rw [hf1] at hy
    simpa [Real.dist_eq] using hy
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff_ball.mp hcont
  filter_upwards [hshrink δ hδ, hfin, hV, hint, hB, hlim (e / 2) (by positivity), hLb] with
    ε hsub hfin' hV' hint' hB' hlim' hLb'
  have hint1 : IntegrableOn (fun _ : α => (1 : ℝ)) (R ε) μ := integrableOn_const hfin'.ne
  have h1 : (∫ X in R ε, f X ∂μ) - V ε = ∫ X in R ε, (f X - 1) ∂μ := by
    rw [integral_sub hint' hint1, setIntegral_const, smul_eq_mul, mul_one, hV']
  have h2 : ‖∫ X in R ε, (f X - 1) ∂μ‖ ≤ η * μ.real (R ε) := by
    refine norm_setIntegral_le_of_norm_le_const hfin' (fun X hX => ?_)
    have := hδb X (hsub hX)
    rw [Real.norm_eq_abs]; exact this.le
  have h3 : |(∫ X in R ε, f X ∂μ) / B ε - V ε / B ε| ≤ η * (V ε / B ε) := by
    rw [← sub_div, abs_div, abs_of_pos hB', div_le_iff₀ hB', mul_assoc, div_mul_cancel₀ _ hB'.ne', h1, ← hV']
    simpa [Real.norm_eq_abs] using h2
  have h4 : η * (V ε / B ε) ≤ η * (|L| + 1) := mul_le_mul_of_nonneg_left hLb'.le hηpos.le
  have h5 : η * (|L| + 1) = e / 2 := by rw [hη]; field_simp
  rw [Real.dist_eq]
  have h6 : |(∫ X in R ε, f X ∂μ) / B ε - L| ≤
      |(∫ X in R ε, f X ∂μ) / B ε - V ε / B ε| + |V ε / B ε - L| := by
    have := abs_add_le ((∫ X in R ε, f X ∂μ) / B ε - V ε / B ε) (V ε / B ε - L)
    simpa using this
  rw [Real.dist_eq] at hlim'
  linarith


theorem eval_rank1 (Q : QuadForm ℝ 1) (x : Fin 1 → ℝ) : Q.eval x = Q.coeff 0 0 * x 0 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn]; ring

theorem pullCoeff_rank1 (Q : QuadForm ℝ 1) (X : Fin 1 → Fin 1 → ℝ) (p : UIdx 1) :
    pullCoeff Q X p = Q.coeff 0 0 * (X 0 0) ^ 2 := by
  have h1 : p.1.1 = 0 := Subsingleton.elim _ _
  have h2 : p.1.2 = 0 := Subsingleton.elim _ _
  simp [pullCoeff, h1, h2, eval_rank1]

theorem coeffU_rank1 (Q : QuadForm ℝ 1) (p : UIdx 1) : coeffU Q p = Q.coeff 0 0 := by
  have h : p = ⟨(0, 0), le_refl _⟩ := Subsingleton.elim _ _
  simp [coeffU, h]

theorem lerayRegion_rank1 (Q : QuadForm ℝ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    lerayRegion Q ε = (fun X : Fin 1 → Fin 1 → ℝ => X 0 0) ⁻¹'
      {x : ℝ | 0 < x ∧ |Q.coeff 0 0 * x ^ 2 - Q.coeff 0 0| ≤ ε} := by
  ext X
  simp only [lerayRegion, mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_pi_le_iff hε,
    pullCoeff_rank1, coeffU_rank1, Real.dist_eq]
  rw [Matrix.det_fin_one]
  simp


theorem set_rank1 (a ε : ℝ) (ha : a ≠ 0) (hε : 0 < ε) (hεa : ε < |a|) :
    {x : ℝ | 0 < x ∧ |a * x ^ 2 - a| ≤ ε} = Icc (√(1 - ε / |a|)) (√(1 + ε / |a|)) := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hδ : ε / |a| < 1 := (div_lt_one hapos).mpr hεa
  have hδ0 : 0 < ε / |a| := div_pos hε hapos
  have key : ∀ x : ℝ, |a * x ^ 2 - a| ≤ ε ↔ 1 - ε / |a| ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + ε / |a| := by
    intro x
    have : a * x ^ 2 - a = a * (x ^ 2 - 1) := by ring
    rw [this, abs_mul, ← le_div_iff₀' hapos, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  ext x
  simp only [mem_ofPred_eq, mem_Icc, key]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨Real.sqrt_le_iff.mpr ⟨hx.le, h1⟩, (Real.le_sqrt' hx).mpr h2⟩
  · rintro ⟨h1, h2⟩
    have hpos : 0 < √(1 - ε / |a|) := Real.sqrt_pos.mpr (by linarith)
    have hx : 0 < x := lt_of_lt_of_le hpos h1
    exact ⟨hx, (Real.sqrt_le_iff.mp h1).2, (Real.le_sqrt' hx).mp h2⟩

theorem volume_lerayRegion_rank1 (Q : QuadForm ℝ 1) (ha : Q.coeff 0 0 ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hεa : ε < |Q.coeff 0 0|) :
    volume (lerayRegion Q ε) =
      ENNReal.ofReal (√(1 + ε / |Q.coeff 0 0|) - √(1 - ε / |Q.coeff 0 0|)) := by
  rw [lerayRegion_rank1 Q hε.le, set_rank1 _ _ ha hε hεa]
  have hmp := (volume_preserving_funUnique (Fin 1) ℝ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℝ))
  have := hmp.measure_preimage (s := Icc (√(1 - ε / |Q.coeff 0 0|)) (√(1 + ε / |Q.coeff 0 0|)))
    measurableSet_Icc.nullMeasurableSet
  rw [Real.volume_Icc] at this
  rw [← this]
  rfl


theorem tendsto_ratio_rank1 (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun ε : ℝ => (√(1 + ε / |a|) - √(1 - ε / |a|)) / (2 * ε)) (𝓝[>] 0) (𝓝 (1 / (2 * |a|))) := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  set g : ℝ → ℝ := fun t => √(1 + t) - √(1 - t) with hg
  have hd : HasDerivAt g 1 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
    have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have h1' := h1.sqrt (by norm_num)
    have h2' := h2.sqrt (by norm_num)
    have := h1'.sub h2'
    convert this using 1
    simp; norm_num
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hd
  have hmap : Tendsto (fun ε : ℝ => ε / |a|) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => ε / |a|) (𝓝 0) (𝓝 (0 / |a|)) := (continuous_id.div_const _).tendsto 0
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (div_pos hε hapos).ne'
  have h := (hslope.comp hmap).mul_const (1 / (2 * |a|))
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have h0 : g 0 = 0 := by simp [hg]
  show (ε / |a|)⁻¹ * (g (0 + ε / |a|) - g 0) * (1 / (2 * |a|)) = _
  rw [h0, zero_add, sub_zero]
  simp only [hg]
  field_simp

theorem volume_ball_rank1 (Q : QuadForm ℝ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (Metric.closedBall (coeffU Q) ε) = ENNReal.ofReal (2 * ε) := by
  rw [Real.volume_pi_closedBall _ hε]
  have : Fintype.card (UIdx 1) = 1 := by decide
  rw [this, pow_one]


theorem coeff_ne_zero_of_gramDetR (Q : QuadForm ℝ 1) (hQ : gramDetR Q ≠ 0) : Q.coeff 0 0 ≠ 0 := by
  intro h0
  apply hQ
  rw [gramDetR, Matrix.det_fin_one]
  simp [QuadForm.hessian, h0]

/-- **The Leray mass of $SO_1(\mathbb R)$:** for $Q = a\,x_0^2$ over $\mathbb R$, $a\ne0$ (either sign), the Leray measure
of the one-point group $SO(Q)(\mathbb R)$ is $1/(2|a|)$ (the Leray limit over the interval $[\sqrt{1-\delta},\sqrt{1+\delta}]$). -/
theorem lerayMeasure_univ_rankOne (Q : QuadForm ℝ 1) (hQ : gramDetR Q ≠ 0) :
    lerayMeasure Q hQ Set.univ = ENNReal.ofReal (1 / (2 * |Q.coeff 0 0|)) := by
  have ha := coeff_ne_zero_of_gramDetR Q hQ
  have hapos : 0 < |Q.coeff 0 0| := abs_pos.mpr ha
  have hsub := subsingleton_archSO Q
  have := isHaarMeasure_lerayMeasure hQ
  set μ := lerayMeasure Q hQ with hμ
  have hfin : μ Set.univ < ⊤ := by
    have : (Set.univ : Set (ArchSO Q)) = {1} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨Set.mem_univ _, fun x _ => Subsingleton.elim _ _⟩
    rw [this]; exact isCompact_singleton.measure_lt_top
  -- the Leray limit for the LerayReal.bump function
  have h1 := tendsto_lerayMeasure (Q := Q) hQ (continuous_bump (n := 1)) hasCompactSupport_bump
  have hint : ∫ g, LerayReal.bump 1 (cols (ArchSOInst.mat Q g)) ∂μ = μ.real Set.univ := by
    have : (fun g : ArchSO Q => LerayReal.bump 1 (cols (ArchSOInst.mat Q g))) = fun _ => 1 := by
      funext g
      rw [Subsingleton.elim g 1]
      have : ArchSOInst.mat Q 1 = 1 := by simp [ArchSOInst.mat]
      simp [this, LerayReal.bump]
    rw [this, integral_const, smul_eq_mul, mul_one]
  rw [hint] at h1
  have h2 : Tendsto (lerayApprox Q (LerayReal.bump 1)) (𝓝[>] 0) (𝓝 (1 / (2 * |Q.coeff 0 0|))) := by
    have hball : ∀ ε : ℝ, 0 < ε → (volume (Metric.closedBall (coeffU Q) ε)).toReal = 2 * ε := fun ε hε => by
      rw [volume_ball_rank1 Q hε.le, ENNReal.toReal_ofReal (by linarith)]
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < |Q.coeff 0 0| :=
      by filter_upwards [Ioo_mem_nhdsGT hapos] with ε hε using ⟨hε.1, hε.2⟩
    have hr : Tendsto (fun ε : ℝ => (√(1 + ε / |Q.coeff 0 0|) - √(1 - ε / |Q.coeff 0 0|)) / (2 * ε))
        (𝓝[>] 0) (𝓝 (1 / (2 * |Q.coeff 0 0|))) := tendsto_ratio_rank1 _ ha
    have hvol : ∀ ε : ℝ, 0 < ε → ε < |Q.coeff 0 0| → volume (lerayRegion Q ε) =
        ENNReal.ofReal (√(1 + ε / |Q.coeff 0 0|) - √(1 - ε / |Q.coeff 0 0|)) :=
      fun ε h1 h2 => volume_lerayRegion_rank1 Q ha h1 h2
    refine tendsto_avg_squeeze volume (x₀ := cols (1 : Matrix (Fin 1) (Fin 1) ℝ)) (f := LerayReal.bump 1)
      (R := lerayRegion Q) (B := fun ε => (volume (Metric.closedBall (coeffU Q) ε)).toReal)
      (V := fun ε => √(1 + ε / |Q.coeff 0 0|) - √(1 - ε / |Q.coeff 0 0|)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (LerayReal.continuous_bump (n := 1)).continuousAt
    · simp [LerayReal.bump]
    · intro η hη
      have c1 : Tendsto (fun ε : ℝ => √(1 - ε / |Q.coeff 0 0|)) (𝓝 0) (𝓝 1) := by
        have hc : Continuous fun ε : ℝ => √(1 - ε / |Q.coeff 0 0|) :=
          (continuous_const.sub (continuous_id.div_const _)).sqrt
        simpa using hc.tendsto 0
      have c2 : Tendsto (fun ε : ℝ => √(1 + ε / |Q.coeff 0 0|)) (𝓝 0) (𝓝 1) := by
        have hc : Continuous fun ε : ℝ => √(1 + ε / |Q.coeff 0 0|) :=
          (continuous_const.add (continuous_id.div_const _)).sqrt
        simpa using hc.tendsto 0
      have e1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 1 - η < √(1 - ε / |Q.coeff 0 0|) :=
        (c1.eventually (lt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds
      have e2 : ∀ᶠ ε : ℝ in 𝓝[>] 0, √(1 + ε / |Q.coeff 0 0|) < 1 + η :=
        (c2.eventually (gt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds
      filter_upwards [hev, e1, e2] with ε h h1 h2 X hX
      rw [lerayRegion_rank1 Q h.1.le, set_rank1 _ _ ha h.1 h.2] at hX
      have hX' : X 0 0 ∈ Icc (√(1 - ε / |Q.coeff 0 0|)) (√(1 + ε / |Q.coeff 0 0|)) := hX
      rw [Metric.mem_ball, dist_pi_lt_iff hη]
      intro i
      rw [dist_pi_lt_iff hη]
      intro j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      rw [Real.dist_eq, abs_lt]
      have : LerayReal.cols (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 1 := by simp [LerayReal.cols]
      rw [this]
      constructor <;> linarith [hX'.1, hX'.2]
    · filter_upwards [hev] with ε h
      rw [hvol ε h.1 h.2]; exact ENNReal.ofReal_lt_top
    · filter_upwards [hev] with ε h
      rw [Measure.real, hvol ε h.1 h.2, ENNReal.toReal_ofReal]
      have : 1 - ε / |Q.coeff 0 0| ≤ 1 + ε / |Q.coeff 0 0| := by
        have : 0 ≤ ε / |Q.coeff 0 0| := div_nonneg h.1.le hapos.le
        linarith
      have := Real.sqrt_le_sqrt this
      linarith
    · exact Eventually.of_forall fun ε =>
        ((LerayReal.continuous_bump (n := 1)).integrable_of_hasCompactSupport
          LerayReal.hasCompactSupport_bump).integrableOn
    · filter_upwards [hev] with ε h
      rw [hball ε h.1]; linarith [h.1]
    · refine hr.congr' ?_
      filter_upwards [hev] with ε h
      rw [hball ε h.1]
  have h3 := tendsto_nhds_unique h1 h2
  rw [← ENNReal.ofReal_toReal hfin.ne]
  congr 1


end RealMass


section ComplexMass
open Filter Topology Set
open scoped Classical

theorem gramC_rank1 (Q : QuadForm ℂ 1) : gramC Q 0 0 = Q.coeff 0 0 := by
  simp [gramC, QuadForm.hessian]; ring

theorem phi_rank1 (Q : QuadForm ℂ 1) (M : Matrix (Fin 1) (Fin 1) ℂ) (p : UIdx 1) :
    LerayComplex.phi Q M p = Q.coeff 0 0 * (M 0 0) ^ 2 := by
  have h1 : p.1.1 = 0 := Subsingleton.elim _ _
  have h2 : p.1.2 = 0 := Subsingleton.elim _ _
  simp [LerayComplex.phi, LerayComplex.wtU, h1, h2, Matrix.mul_apply, gramC_rank1, ArchVol.wt]
  ring

theorem coeffUC_rank1 (Q : QuadForm ℂ 1) (p : UIdx 1) : coeffUC Q p = Q.coeff 0 0 := by
  have h : p = ⟨(0, 0), le_refl _⟩ := Subsingleton.elim _ _
  simp [coeffUC, h]

theorem lerayRegionC_rank1 (Q : QuadForm ℂ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    lerayRegionC Q ε = (fun X : Fin 1 → Fin 1 → ℂ => X 0 0) ⁻¹'
      {x : ℂ | 0 < x.re ∧ ‖Q.coeff 0 0 * x ^ 2 - Q.coeff 0 0‖ ≤ ε} := by
  ext X
  simp only [lerayRegionC, regionC, mem_ofPred_eq, mem_preimage, Metric.mem_closedBall]
  rw [dist_pi_le_iff hε]
  simp only [phi_rank1, coeffUC_rank1, dist_eq_norm]
  rw [Matrix.det_fin_one]
  simp [LerayComplex.ofCols]


def SC (δ : ℝ) : Set ℂ := {x : ℂ | 0 < x.re ∧ ‖x ^ 2 - 1‖ ≤ δ}

theorem injOn_sq_SC (δ : ℝ) : InjOn (fun x : ℂ => x ^ 2) (SC δ) := by
  intro x hx y hy h
  have h' : (x - y) * (x + y) = 0 := by simp only at h; ring_nf; rw [h]; ring
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have := congrArg Complex.re h1
    simp at this
    linarith [hx.1, hy.1]

theorem image_sq_SC {δ : ℝ} (hδ : δ < 1) : (fun x : ℂ => x ^ 2) '' SC δ = Metric.closedBall 1 δ := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.2
  · intro hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre : 0 < w.re := by
      have := Complex.abs_re_le_norm (w - 1)
      have h2 : (w - 1).re = w.re - 1 := by simp
      rw [h2] at this
      have := (abs_le.mp this).1
      linarith
    have hw0 : w ≠ 0 := fun h => by simp [h] at hre
    refine ⟨w ^ (2⁻¹ : ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
      refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
      · have := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
        have h3 : ((Complex.log w) * 2⁻¹).im = w.arg / 2 := by
          simp [Complex.log_im]; ring
        rw [h3]; have := (abs_lt.mp this).1; linarith [Real.pi_pos]
      · have := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
        have h3 : ((Complex.log w) * 2⁻¹).im = w.arg / 2 := by
          simp [Complex.log_im]; ring
        rw [h3]; have := (abs_lt.mp this).2; linarith [Real.pi_pos]
    · have : (w ^ (2⁻¹ : ℂ)) ^ 2 = w := by
        have := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
        simpa using this
      rw [this]; exact hw
    · have := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
      simpa using this


theorem measurableSet_SC (δ : ℝ) : MeasurableSet (SC δ) :=
  (measurableSet_lt measurable_const Complex.measurable_re).inter
    (measurableSet_le ((measurable_id.pow_const 2).sub_const 1).norm measurable_const)

noncomputable def dsq (x : ℂ) : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * x)).restrictScalars ℝ

theorem det_dsq (x : ℂ) : (dsq x).det = ‖2 * x‖ ^ 2 := by
  show LinearMap.det (dsq x : ℂ →ₗ[ℝ] ℂ) = _
  have h1 : (dsq x : ℂ →ₗ[ℝ] ℂ) = (LinearMap.mul ℂ ℂ (2 * x)).restrictScalars ℝ := by
    ext z; simp [dsq, mul_comm]
  rw [h1, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  have : (LinearMap.mul ℂ ℂ (2 * x)).det = 2 * x := by
    have : LinearMap.mul ℂ ℂ (2 * x) = LinearMap.mulLeft ℂ (2 * x) := rfl
    rw [this, LinearMap.det_mulLeft]
  rw [this]
  simp [Complex.normSq_eq_norm_sq]

theorem lintegral_SC {δ : ℝ} :
    ∫⁻ x in SC δ, ENNReal.ofReal (‖2 * x‖ ^ 2) = volume ((fun x : ℂ => x ^ 2) '' SC δ) := by
  have := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure ℂ) (f := fun x : ℂ => x ^ 2)
    (f' := dsq) (measurableSet_SC δ) (fun x _ => ?_) (injOn_sq_SC δ)
  · rw [← this]
    refine lintegral_congr fun x => ?_
    rw [det_dsq, abs_of_nonneg (by positivity)]
  · have h := ((hasDerivAt_pow 2 x).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt (s := SC δ)
    convert h using 2
    ext z
    simp [dsq, mul_comm]


theorem SC_norm_sq {δ : ℝ} {x : ℂ} (hx : x ∈ SC δ) : 1 - δ ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ 1 + δ := by
  have h1 : ‖x ^ 2‖ = ‖x‖ ^ 2 := norm_pow _ _
  have h2 := hx.2
  have h3 : |‖x ^ 2‖ - ‖(1 : ℂ)‖| ≤ ‖x ^ 2 - 1‖ := abs_norm_sub_norm_le _ _
  rw [norm_one, h1] at h3
  have := abs_le.mp (h3.trans h2)
  constructor <;> linarith [this.1, this.2]

theorem volume_SC_lt_top {δ : ℝ} (hδ : δ < 1) : volume (SC δ) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 2) fun x hx => ?_) (measure_closedBall_lt_top)
  rw [Metric.mem_closedBall, dist_zero_right]
  have := (SC_norm_sq hx).2
  nlinarith [norm_nonneg x]

theorem SC_bounds {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    4 * (1 - δ) * (volume (SC δ)).toReal ≤ Real.pi * δ ^ 2 ∧
      Real.pi * δ ^ 2 ≤ 4 * (1 + δ) * (volume (SC δ)).toReal := by
  have hfin := volume_SC_lt_top h1
  have key := lintegral_SC (δ := δ)
  rw [image_sq_SC h1, Complex.volume_closedBall] at key
  have hT : (ENNReal.ofReal δ ^ 2 * (NNReal.pi : ENNReal)).toReal = Real.pi * δ ^ 2 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal h0.le]
    simp [mul_comm]
  have hint : ∀ c : ℝ, 0 ≤ c → (∀ x ∈ SC δ, ENNReal.ofReal (‖2 * x‖ ^ 2) ≤ ENNReal.ofReal c) →
      (∫⁻ x in SC δ, ENNReal.ofReal (‖2 * x‖ ^ 2)).toReal ≤ c * (volume (SC δ)).toReal := by
    intro c hc hle
    have := setLIntegral_mono' (μ := volume) (measurableSet_SC δ) hle
    rw [setLIntegral_const] at this
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) this
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h2
  have hint' : ∀ c : ℝ, 0 ≤ c → (∀ x ∈ SC δ, ENNReal.ofReal c ≤ ENNReal.ofReal (‖2 * x‖ ^ 2)) →
      c * (volume (SC δ)).toReal ≤ (∫⁻ x in SC δ, ENNReal.ofReal (‖2 * x‖ ^ 2)).toReal := by
    intro c hc hle
    have := setLIntegral_mono' (μ := volume) (measurableSet_SC δ) hle
    rw [setLIntegral_const] at this
    have hne : ∫⁻ x in SC δ, ENNReal.ofReal (‖2 * x‖ ^ 2) ≠ ⊤ := by
      rw [key]; exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
    have h2 := ENNReal.toReal_mono hne this
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h2
  have hnorm : ∀ x : ℂ, ‖2 * x‖ ^ 2 = 4 * ‖x‖ ^ 2 := fun x => by
    rw [norm_mul]; simp; ring
  constructor
  · have := hint' (4 * (1 - δ)) (by linarith) fun x hx => by
      apply ENNReal.ofReal_le_ofReal
      rw [hnorm]; linarith [(SC_norm_sq hx).1]
    rw [key] at this
    rwa [hT] at this
  · have := hint (4 * (1 + δ)) (by linarith) fun x hx => by
      apply ENNReal.ofReal_le_ofReal
      rw [hnorm]; linarith [(SC_norm_sq hx).2]
    rw [key] at this
    rwa [hT] at this


theorem coeff_ne_zero_of_gramDetC (Q : QuadForm ℂ 1) (hQ : gramDetC Q ≠ 0) : Q.coeff 0 0 ≠ 0 := by
  intro h0
  apply hQ
  rw [gramDetC, Matrix.det_fin_one, gramC_rank1, h0]

theorem set_rank1C (a : ℂ) (ε : ℝ) (ha : a ≠ 0) :
    {x : ℂ | 0 < x.re ∧ ‖a * x ^ 2 - a‖ ≤ ε} = SC (ε / ‖a‖) := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  ext x
  simp only [mem_ofPred_eq, SC]
  have : a * x ^ 2 - a = a * (x ^ 2 - 1) := by ring
  rw [this, norm_mul, le_div_iff₀' hapos]

theorem volume_lerayRegionC_rank1 (Q : QuadForm ℂ 1) (ha : Q.coeff 0 0 ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (lerayRegionC Q ε) = volume (SC (ε / ‖Q.coeff 0 0‖)) := by
  rw [lerayRegionC_rank1 Q hε, set_rank1C _ _ ha]
  have hmp := (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))
  have := hmp.measure_preimage (s := SC (ε / ‖Q.coeff 0 0‖)) (measurableSet_SC _).nullMeasurableSet
  rw [← this]
  rfl

theorem volume_ballC_rank1 (Q : QuadForm ℂ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (Metric.closedBall (coeffUC Q) ε) = ENNReal.ofReal ε ^ 2 * NNReal.pi := by
  rw [volume_pi_closedBall _ hε]
  have : Finset.univ = ({⟨(0, 0), le_refl _⟩} : Finset (UIdx 1)) := by
    ext p; simp [Subsingleton.elim p ⟨(0, 0), le_refl _⟩]
  rw [this, Finset.prod_singleton, Complex.volume_closedBall]

theorem tendsto_ratioC (a : ℝ) (ha : 0 < a) (V : ℝ → ℝ)
    (hV : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 4 * (1 - ε / a) * V ε ≤ Real.pi * (ε / a) ^ 2 ∧
      Real.pi * (ε / a) ^ 2 ≤ 4 * (1 + ε / a) * V ε)
    (hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < a) :
    Tendsto (fun ε => V ε / (Real.pi * ε ^ 2)) (𝓝[>] 0) (𝓝 ((1 / (2 * a)) ^ 2)) := by
  have hval : (1 / (2 * a)) ^ 2 = 1 / (4 * a ^ 2 * (1 + 0 / a)) := by field_simp; ring
  have hval' : (1 / (2 * a)) ^ 2 = 1 / (4 * a ^ 2 * (1 - 0 / a)) := by field_simp; ring
  have c1 : Tendsto (fun ε : ℝ => 1 / (4 * a ^ 2 * (1 + ε / a))) (𝓝[>] 0) (𝓝 ((1 / (2 * a)) ^ 2)) := by
    rw [hval]
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
    simp; positivity
  have c2 : Tendsto (fun ε : ℝ => 1 / (4 * a ^ 2 * (1 - ε / a))) (𝓝[>] 0) (𝓝 ((1 / (2 * a)) ^ 2)) := by
    rw [hval']
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
    simp; positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' c1 c2 ?_ ?_
  · filter_upwards [hV, hev] with ε h h2
    obtain ⟨h0, h1⟩ := h2
    have hd : 0 < ε / a := div_pos h0 ha
    have hd1 : ε / a < 1 := (div_lt_one ha).mpr h1
    have : Real.pi * ε ^ 2 = Real.pi * (ε / a) ^ 2 * a ^ 2 := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h.2, Real.pi_pos, sq_nonneg a, mul_pos Real.pi_pos (pow_pos hd 2)]
  · filter_upwards [hV, hev] with ε h h2
    obtain ⟨h0, h1⟩ := h2
    have hd : 0 < ε / a := div_pos h0 ha
    have hd1 : ε / a < 1 := (div_lt_one ha).mpr h1
    have : Real.pi * ε ^ 2 = Real.pi * (ε / a) ^ 2 * a ^ 2 := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (mul_pos (by positivity) (by linarith))]
    nlinarith [h.1, Real.pi_pos, sq_nonneg a, mul_pos Real.pi_pos (pow_pos hd 2)]


/-- **The Leray mass of $SO_1(\mathbb C)$:** for $Q = a\,x_0^2$ over $\mathbb C$, $a\ne0$, the Leray measure of the
one-point group $SO(Q)(\mathbb C)$ is $(1/(2|a|))^2 = |2a|_{\mathbb C}^{-1}$ (change of variables $x\mapsto x^2$). -/
theorem lerayMeasureC_univ_rankOne (Q : QuadForm ℂ 1) (hQ : gramDetC Q ≠ 0) :
    lerayMeasureC Q hQ Set.univ = ENNReal.ofReal ((1 / (2 * ‖Q.coeff 0 0‖)) ^ 2) := by
  have ha := coeff_ne_zero_of_gramDetC Q hQ
  have hapos : 0 < ‖Q.coeff 0 0‖ := norm_pos_iff.mpr ha
  have hsub := subsingleton_archSOC Q
  have := isHaarMeasure_lerayMeasureC hQ
  set μ := lerayMeasureC Q hQ with hμ
  have hfin : μ Set.univ < ⊤ := by
    have : (Set.univ : Set (ArchSOC Q)) = {1} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨Set.mem_univ _, fun x _ => Subsingleton.elim _ _⟩
    rw [this]; exact isCompact_singleton.measure_lt_top
  have h1 := tendsto_lerayMeasureC (Q := Q) hQ (LerayComplex.continuous_bump (n := 1)) LerayComplex.hasCompactSupport_bump
  have hint : ∫ g, LerayComplex.bump 1 (LerayComplex.cols (ArchSOC.mat Q g)) ∂μ = μ.real Set.univ := by
    have : (fun g : ArchSOC Q => LerayComplex.bump 1 (LerayComplex.cols (ArchSOC.mat Q g))) = fun _ => 1 := by
      funext g
      rw [Subsingleton.elim g 1]
      simp [ArchSOC.mat_one, LerayComplex.bump]
    rw [this, integral_const, smul_eq_mul, mul_one]
  rw [hint] at h1
  have h2 : Tendsto (lerayApproxC Q (LerayComplex.bump 1)) (𝓝[>] 0) (𝓝 ((1 / (2 * ‖Q.coeff 0 0‖)) ^ 2)) := by
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < ‖Q.coeff 0 0‖ := by
      filter_upwards [Ioo_mem_nhdsGT hapos] with ε hε using ⟨hε.1, hε.2⟩
    have hδ : ∀ ε : ℝ, 0 < ε → ε < ‖Q.coeff 0 0‖ → 0 < ε / ‖Q.coeff 0 0‖ ∧ ε / ‖Q.coeff 0 0‖ < 1 :=
      fun ε h1 h2 => ⟨div_pos h1 hapos, (div_lt_one hapos).mpr h2⟩
    have hball : ∀ ε : ℝ, 0 < ε → (volume (Metric.closedBall (coeffUC Q) ε)).toReal = Real.pi * ε ^ 2 := by
      intro ε hε
      rw [volume_ballC_rank1 Q hε.le, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le]
      simp [mul_comm]
    refine tendsto_avg_squeeze volume (x₀ := LerayComplex.cols (1 : Matrix (Fin 1) (Fin 1) ℂ)) (f := LerayComplex.bump 1)
      (R := lerayRegionC Q) (B := fun ε => (volume (Metric.closedBall (coeffUC Q) ε)).toReal)
      (V := fun ε => (volume (SC (ε / ‖Q.coeff 0 0‖))).toReal) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (LerayComplex.continuous_bump (n := 1)).continuousAt
    · simp [LerayComplex.bump]
    · intro η hη
      have c1 : Tendsto (fun ε : ℝ => ε / ‖Q.coeff 0 0‖) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_id.div_const ‖Q.coeff 0 0‖).tendsto 0
      have e1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε / ‖Q.coeff 0 0‖ < η :=
        (c1.eventually (gt_mem_nhds hη)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hev, e1] with ε h h1 X hX
      rw [lerayRegionC_rank1 Q h.1.le, set_rank1C _ _ ha] at hX
      have hX' : X 0 0 ∈ SC (ε / ‖Q.coeff 0 0‖) := hX
      have hxd : ‖X 0 0 - 1‖ ≤ ε / ‖Q.coeff 0 0‖ := by
        have hfac : (X 0 0 - 1) * (X 0 0 + 1) = X 0 0 ^ 2 - 1 := by ring
        have hge : 1 ≤ ‖X 0 0 + 1‖ := by
          have := Complex.re_le_norm (X 0 0 + 1)
          simp at this
          linarith [hX'.1]
        have h3 : ‖X 0 0 - 1‖ * ‖X 0 0 + 1‖ ≤ ε / ‖Q.coeff 0 0‖ := by
          rw [← norm_mul, hfac]; exact hX'.2
        nlinarith [norm_nonneg (X 0 0 - 1)]
      rw [Metric.mem_ball, dist_pi_lt_iff hη]
      intro i
      rw [dist_pi_lt_iff hη]
      intro j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      have : LerayComplex.cols (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1 := by simp [LerayComplex.cols]
      rw [this, dist_eq_norm]
      linarith
    · filter_upwards [hev] with ε h
      rw [volume_lerayRegionC_rank1 Q ha h.1.le]
      exact volume_SC_lt_top (hδ ε h.1 h.2).2
    · filter_upwards [hev] with ε h
      rw [Measure.real, volume_lerayRegionC_rank1 Q ha h.1.le]
    · exact Eventually.of_forall fun ε =>
        ((LerayComplex.continuous_bump (n := 1)).integrable_of_hasCompactSupport LerayComplex.hasCompactSupport_bump).integrableOn
    · filter_upwards [hev] with ε h
      rw [hball ε h.1]; exact mul_pos Real.pi_pos (pow_pos h.1 2)
    · have := tendsto_ratioC ‖Q.coeff 0 0‖ hapos (fun ε => (volume (SC (ε / ‖Q.coeff 0 0‖))).toReal)
        (by
          filter_upwards [hev] with ε h
          have hd := hδ ε h.1 h.2
          have := SC_bounds hd.1 hd.2
          exact ⟨this.1, this.2⟩) hev
      refine this.congr' ?_
      filter_upwards [hev] with ε h
      rw [hball ε h.1]
  have h3 := tendsto_nhds_unique h1 h2
  rw [← ENNReal.ofReal_toReal hfin.ne]
  congr 1


end ComplexMass

open scoped Classical in
/-- **The total mass of Weil's measure in dimension $1$** is the combinatorial `tamagawaK Q₀`
(archimedean Leray masses times the local densities; $c_F = 1$, `cxWeil F 1` $= 1$). -/
theorem muTam_univ_rankOne (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    muTam Q₀ hQ (fun _ => 1) Set.univ = ENNReal.ofReal (tamagawaK Q₀) := by
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have := subsingleton_SOAf Q₀
  have hK : (KSO Q₀ : Set (SOAf Q₀)) = Set.univ := Set.eq_univ_of_forall fun x => by
    rw [Subsingleton.elim x 1]; exact one_mem _
  have hF : muFin Q₀ (fun _ => 1) Set.univ = ENNReal.ofReal (∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀) := by
    rw [← hK, muFin_KSO, finFactor_one Q₀ hQ]
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero Q₀ hQ w); infer_instance
  have hsfC : ∀ w, SigmaFinite (lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero Q₀ hQ w); infer_instance
  rw [muTam_eq_smul, Measure.smul_apply, smul_eq_mul, ← Set.univ_prod_univ, Measure.prod_prod, hF,
    muArchNF, muArchLeray, ← Set.univ_prod_univ, Measure.prod_prod, Measure.pi_univ, Measure.pi_univ]
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal}, |(QRe Q₀ w).coeff 0 0| = w.1 ((Q₀.coeff 0 0 : 𝓞 F) : F) := by
    intro w
    rw [← InfinitePlace.norm_embedding_of_isReal w.2, Real.norm_eq_abs]
    simp [QuadForm.map]
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, ‖(QCx Q₀ w).coeff 0 0‖ = w.1 ((Q₀.coeff 0 0 : 𝓞 F) : F) := by
    intro w
    rw [← InfinitePlace.norm_embedding_eq]
    simp [QuadForm.map]
  simp only [lerayMeasure_univ_rankOne, lerayMeasureC_univ_rankOne, hR, hC]
  have hpos : ∀ w : InfinitePlace F, 0 ≤ 1 / (2 * w ((Q₀.coeff 0 0 : 𝓞 F) : F)) := fun w => by positivity
  have hcF : cF F 1 * cxWeil F 1 = 1 := by simp [cF, cxWeil]
  rw [hcF, ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_prod_of_nonneg (fun w _ => hpos w.1),
    ← ENNReal.ofReal_prod_of_nonneg (fun w _ => pow_nonneg (hpos w.1) 2),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => hpos w.1),
    ← ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun w _ => hpos w.1)
      (Finset.prod_nonneg fun w _ => pow_nonneg (hpos w.1) 2))]
  congr 1
  rw [tamagawaK]
  simp only [RankOne.archVolSO_one, TauSOOne.detGram_rankOne]
  rw [prod_embeddings_eq (fun d => 1 / (2 * d)) ((Q₀.coeff 0 0 : 𝓞 F) : F)]
  simp [cF]

/-- **$\tau(SO_1) = 1$ in Weil's adelic normalization:** for every number field $F$ and every nondegenerate form
$Q_0 = \langle c\rangle$ in one variable over $\mathcal O_F$, the covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for Weil's
Tamagawa measure `muTam Q₀ hQ 1` is $1$ (both groups are trivial; the value is the product formula for $2c$).
**Unconditional.** -/
@[kb "weil1982" "§3.7, p. 62 (rank one: SO_1 trivial, τ = 1) [unverified page]"]
theorem covolume_muTam_rankOne (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 1 := by
  rw [covolume_eq_univ, muTam_univ_rankOne Q₀ hQ, TauSOOne.tamagawaK_rankOne_eq_one Q₀ hQ, ENNReal.ofReal_one]

end QuadFormsKB.Tamagawa.Measure.Weil
