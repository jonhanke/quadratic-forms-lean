/-
# The shell ratio $\omega_\infty(\mathrm{BinfPos}) = 2^{r_2}\,\omega_\infty(\mathrm{Vone})$

**Layer:** $F$ an arbitrary number field; the archimedean Haar measure $\omega_\infty$ on $F_\infty^\times$.

* `omegaInf_box`: for measurable $P_w\subseteq\mathbb R\setminus0$ ($w$ real) and $P_w\subseteq\mathbb C\setminus0$ ($w$ complex),
  $\omega_\infty(\{t : t_w\in P_w\ \forall w\}) = 2^{r_2}\prod_{w\ \mathrm{real}}\int_{P_w}\frac{dx}{|x|}\cdot
  \prod_{w\ \mathrm{complex}}\int_{P_w}\frac{d^2z}{\|z\|^2}$.
* local comparisons: $\int_{(1,4)}dx/|x| = \int_{1<|x|<2}dx/|x|$ ($=\log 4$) and
  $\int_{1<\|z\|<4}d^2z/\|z\|^2 = 2\int_{1<\|z\|<2}d^2z/\|z\|^2$ (scaling $z\mapsto 2z$).
* **`omegaInf_BinfPos`**: $\omega_\infty(\mathrm{BinfPos}) = 2^{r_2}\,\omega_\infty(\mathrm{Vone})$, with
  `omegaInf_BinfPos_ne_zero`, `omegaInf_BinfPos_ne_top`.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSFibAny
import QuadFormsKB.Tamagawa.Measure.Weil.ArchPolarGlobal

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal NNReal Classical

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

section ShellRatio

variable {F : Type} [Field F] [NumberField F]

/-- The box $\{t : t_w\in P_w\ (w\text{ real}),\ t_w\in P_w\ (w\text{ complex})\}\subseteq F_\infty$. -/
def infBoxSet (PR : {w : InfinitePlace F // w.IsReal} → Set ℝ) (PC : {w : InfinitePlace F // w.IsComplex} → Set ℂ) :
    Set (mixedSpace F) :=
  {t | (∀ w, t.1 w ∈ PR w) ∧ ∀ w, t.2 w ∈ PC w}

theorem measurableSet_infBoxSet {PR : {w : InfinitePlace F // w.IsReal} → Set ℝ}
    {PC : {w : InfinitePlace F // w.IsComplex} → Set ℂ} (hR : ∀ w, MeasurableSet (PR w))
    (hC : ∀ w, MeasurableSet (PC w)) : MeasurableSet (infBoxSet PR PC) := by
  have e : infBoxSet PR PC = (⋂ w, (fun t : mixedSpace F => t.1 w) ⁻¹' PR w) ∩
      ⋂ w, (fun t : mixedSpace F => t.2 w) ⁻¹' PC w := by ext t; simp [infBoxSet]
  rw [e]
  exact (MeasurableSet.iInter fun w => (hR w).preimage ((measurable_pi_apply w).comp measurable_fst)).inter
    (MeasurableSet.iInter fun w => (hC w).preimage ((measurable_pi_apply w).comp measurable_snd))

omit [NumberField F] in
theorem isUnit_of_mem_infBoxSet {PR : {w : InfinitePlace F // w.IsReal} → Set ℝ}
    {PC : {w : InfinitePlace F // w.IsComplex} → Set ℂ} (h0R : ∀ w, (0 : ℝ) ∉ PR w) (h0C : ∀ w, (0 : ℂ) ∉ PC w)
    {t : mixedSpace F} (ht : t ∈ infBoxSet PR PC) : IsUnit t := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  refine ⟨fun w => isUnit_iff_ne_zero.2 ?_, fun w => isUnit_iff_ne_zero.2 ?_⟩
  · intro h; exact h0R w (h ▸ ht.1 w)
  · intro h; exact h0C w (h ▸ ht.2 w)

/-- **$\omega_\infty$ of a box**: $\omega_\infty(\mathrm{box}) = 2^{r_2}\prod_{\mathrm{real}}\int_{P_w}|x|^{-1}dx
\prod_{\mathrm{complex}}\int_{P_w}\|z\|^{-2}d^2z$. -/
theorem omegaInf_box {PR : {w : InfinitePlace F // w.IsReal} → Set ℝ}
    {PC : {w : InfinitePlace F // w.IsComplex} → Set ℂ} (hR : ∀ w, MeasurableSet (PR w))
    (hC : ∀ w, MeasurableSet (PC w)) (h0R : ∀ w, (0 : ℝ) ∉ PR w) (h0C : ∀ w, (0 : ℂ) ∉ PC w) :
    omegaInf F (Units.val ⁻¹' infBoxSet PR PC) = (2 : ℝ≥0∞) ^ nrComplexPlaces F *
      ((∏ w, ∫⁻ x in PR w, ENNReal.ofReal |x|⁻¹) * ∏ w, ∫⁻ z in PC w, ENNReal.ofReal (‖z‖ ^ 2)⁻¹) := by
  have he := isOpenEmbedding_val_mixedSpace (F := F) |>.measurableEmbedding
  have hNm := measurableSet_infBoxSet hR hC
  have hSm : MeasurableSet (Units.val ⁻¹' infBoxSet PR PC : Set (mixedSpace F)ˣ) :=
    hNm.preimage Units.continuous_val.measurable
  have himg : Units.val '' (Units.val ⁻¹' infBoxSet PR PC : Set (mixedSpace F)ˣ) = infBoxSet PR PC :=
    image_preimage_eq_of_subset fun t ht => ⟨(isUnit_of_mem_infBoxSet h0R h0C ht).unit, rfl⟩
  set dR : (w : {w : InfinitePlace F // w.IsReal}) → ℝ → ℝ≥0∞ :=
    fun w => (PR w).indicator fun t => ENNReal.ofReal |t|⁻¹ with hdR
  set dC : (w : {w : InfinitePlace F // w.IsComplex}) → ℂ → ℝ≥0∞ :=
    fun w => (PC w).indicator fun t => ENNReal.ofReal (‖t‖ ^ 2)⁻¹ with hdC
  have hmR : ∀ w, Measurable (dR w) := fun w =>
    (Measurable.ennreal_ofReal (measurable_id.abs.inv)).indicator (hR w)
  have hmC : ∀ w, Measurable (dC w) := fun w =>
    (Measurable.ennreal_ofReal ((continuous_norm.measurable.pow_const 2).inv)).indicator (hC w)
  rw [omegaInf_eq, withDensity_apply _ hSm]
  set g : mixedSpace F → ℝ≥0∞ := fun t => ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ t)|⁻¹
  calc ∫⁻ u in (Units.val ⁻¹' infBoxSet PR PC : Set (mixedSpace F)ˣ),
          ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (u : mixedSpace F))|⁻¹
        ∂(Analysis.selfDualInf (F := F)).comap Units.val
      = ∫⁻ u, g u ∂(((Analysis.selfDualInf (F := F)).restrict
          (Units.val '' (Units.val ⁻¹' infBoxSet PR PC : Set (mixedSpace F)ˣ))).comap Units.val) := by
        rw [he.restrict_comap]
    _ = ∫⁻ t, g t ∂((((Analysis.selfDualInf (F := F)).restrict
          (Units.val '' (Units.val ⁻¹' infBoxSet PR PC : Set (mixedSpace F)ˣ))).comap Units.val).map Units.val) :=
        (he.lintegral_map _).symm
    _ = ∫⁻ t in infBoxSet PR PC, g t ∂Analysis.selfDualInf (F := F) := by
        rw [he.map_comap, Measure.restrict_restrict he.measurableSet_range,
          inter_eq_right.2 (image_subset_range _ _), himg]
    _ = ∫⁻ t, (∏ w, dR w (t.1 w)) * ∏ w, dC w (t.2 w) ∂Analysis.selfDualInf (F := F) := by
        rw [← lintegral_indicator hNm]
        refine lintegral_congr fun t => ?_
        by_cases ht : t ∈ infBoxSet PR PC
        · simp only [hdR, hdC, g]
          rw [indicator_of_mem ht, Finset.prod_congr rfl fun w _ => indicator_of_mem (ht.1 w) _,
            Finset.prod_congr rfl fun w _ => indicator_of_mem (ht.2 w) _, det_mulLeft_abs, mul_inv,
            ENNReal.ofReal_mul (inv_nonneg.2 (Finset.prod_nonneg fun _ _ => abs_nonneg _)),
            ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
            ENNReal.ofReal_prod_of_nonneg fun _ _ => inv_nonneg.2 (abs_nonneg _),
            ENNReal.ofReal_prod_of_nonneg fun _ _ => inv_nonneg.2 (by positivity)]
        · rw [indicator_of_notMem ht]
          have ht' : ¬ ((∀ w, t.1 w ∈ PR w) ∧ ∀ w, t.2 w ∈ PC w) := ht
          simp only [not_and_or, not_forall] at ht'
          rcases ht' with ⟨w, hw⟩ | ⟨w, hw⟩
          · rw [Finset.prod_eq_zero (Finset.mem_univ w) (indicator_of_notMem hw _), zero_mul]
          · rw [Finset.prod_eq_zero (Finset.mem_univ w) (indicator_of_notMem hw _), mul_zero]
    _ = _ := by
        rw [Analysis.selfDualInf, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
        push_cast
        congr 1
        have hfR : Measurable fun y : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ w, dR w (y w) :=
          Finset.measurable_prod _ fun w _ => (hmR w).comp (measurable_pi_apply w)
        have hfC : Measurable fun y : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w, dC w (y w) :=
          Finset.measurable_prod _ fun w _ => (hmC w).comp (measurable_pi_apply w)
        rw [show (volume : Measure (mixedSpace F)) = (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)).prod
              volume from rfl,
          lintegral_prod_mul hfR.aemeasurable hfC.aemeasurable,
          show (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)) = Measure.pi fun _ => volume from rfl,
          show (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)) = Measure.pi fun _ => volume from rfl,
          lintegral_pi_prod _ hmR, lintegral_pi_prod _ hmC]
        congr 1
        · exact Finset.prod_congr rfl fun w _ => lintegral_indicator (hR w) _
        · exact Finset.prod_congr rfl fun w _ => lintegral_indicator (hC w) _

end ShellRatio

/-! ### Local comparisons -/

/-- $\int_{(a,b)}dx/|x| = \log(b/a)$ for $0<a<b$. -/
theorem lintegral_Ioo_inv {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal |x|⁻¹ = ENNReal.ofReal (Real.log (b / a)) := by
  have hb : 0 < b := ha.trans hab
  have hint : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b :=
    intervalIntegral.intervalIntegrable_inv (fun x hx => by
      rw [uIcc_of_le hab.le] at hx; exact (ha.trans_le hx.1).ne') continuousOn_id
  have hI : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo a b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo a b)] fun x : ℝ => x⁻¹ :=
    (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => inv_nonneg.2 (ha.trans hx.1).le)
  rw [← integral_inv_of_pos ha hb, intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hI hnn]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [abs_of_pos (ha.trans hx.1)]

/-- **Real places**: $\int_{(1,4)}dx/|x| = \int_{1<|x|<2}dx/|x|$ (both are $\log 4$). -/
theorem lintegral_real_shell_ratio :
    ∫⁻ x in Ioo (1 : ℝ) 4, ENNReal.ofReal |x|⁻¹ = ∫⁻ x in {x : ℝ | |x| ∈ Ioo (1 : ℝ) 2}, ENNReal.ofReal |x|⁻¹ := by
  have hset : {x : ℝ | |x| ∈ Ioo (1 : ℝ) 2} = Ioo (-2) (-1) ∪ Ioo 1 2 := by
    ext x
    simp only [mem_ofPred_eq, mem_Ioo, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h] at h1 h2; exact Or.inr ⟨h1, h2⟩
      · rw [abs_of_nonpos h] at h1 h2; exact Or.inl ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [abs_of_neg (by linarith)]; constructor <;> linarith
      · rw [abs_of_pos (by linarith)]; exact ⟨h1, h2⟩
  have hneg : ∫⁻ x in Ioo (-2 : ℝ) (-1), ENNReal.ofReal |x|⁻¹ = ∫⁻ x in Ioo (1 : ℝ) 2, ENNReal.ofReal |x|⁻¹ := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding (fun x : ℝ => ENNReal.ofReal |x|⁻¹) (Ioo (1 : ℝ) 2)
    rw [← this]
    have e : (fun x : ℝ => -x) ⁻¹' Ioo (1 : ℝ) 2 = Ioo (-2) (-1) := by
      ext x; simp only [mem_preimage, mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [abs_neg]
    rw [e]
  rw [hset, lintegral_union measurableSet_Ioo (Ioo_disjoint_Ioo.2 (by norm_num)), hneg,
    lintegral_Ioo_inv one_pos (by norm_num), lintegral_Ioo_inv one_pos (by norm_num), ← ENNReal.ofReal_add
      (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))]
  congr 1
  rw [div_one, div_one, ← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem measurableSet_normIoo (a b : ℝ) : MeasurableSet {z : ℂ | ‖z‖ ∈ Ioo a b} :=
  measurableSet_Ioo.preimage continuous_norm.measurable

/-- **Complex places**: $\int_{1<\|z\|<4}d^2z/\|z\|^2 = 2\int_{1<\|z\|<2}d^2z/\|z\|^2$ (scaling $z\mapsto2z$ and the
null circle $\|z\| = 2$). -/
theorem lintegral_complex_shell_ratio :
    ∫⁻ z in {z : ℂ | ‖z‖ ∈ Ioo (1 : ℝ) 4}, ENNReal.ofReal (‖z‖ ^ 2)⁻¹ =
      2 * ∫⁻ z in {z : ℂ | ‖z‖ ∈ Ioo (1 : ℝ) 2}, ENNReal.ofReal (‖z‖ ^ 2)⁻¹ := by
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ 2)⁻¹ with hf
  have hfm : Measurable f := Measurable.ennreal_ofReal ((continuous_norm.measurable.pow_const 2).inv)
  set A12 : Set ℂ := {z : ℂ | ‖z‖ ∈ Ioo (1 : ℝ) 2} with hA12
  set A24 : Set ℂ := {z : ℂ | ‖z‖ ∈ Ioo (2 : ℝ) 4} with hA24
  have hA12m : MeasurableSet A12 := measurableSet_normIoo 1 2
  have hA24m : MeasurableSet A24 := measurableSet_normIoo 2 4
  have hsplit : {z : ℂ | ‖z‖ ∈ Ioo (1 : ℝ) 4} = (A12 ∪ Metric.sphere (0 : ℂ) 2) ∪ A24 := by
    ext z
    simp only [hA12, hA24, mem_ofPred_eq, mem_Ioo, mem_union, mem_sphere_iff_norm, sub_zero]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy ‖z‖ 2 with h | h | h
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨h, h2⟩
    · rintro ((⟨h1, h2⟩ | h) | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · rw [h]; constructor <;> norm_num
      · exact ⟨by linarith, h2⟩
  have hsph : ∫⁻ z in Metric.sphere (0 : ℂ) 2, f z = 0 :=
    setLIntegral_measure_zero _ _ (Measure.addHaar_sphere volume (0 : ℂ) 2)
  have hd1 : Disjoint A12 (Metric.sphere (0 : ℂ) 2) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [mem_sphere_iff_norm, sub_zero] at hz'
    have := hz.2; rw [hz'] at this; exact lt_irrefl _ this
  have hd2 : Disjoint (A12 ∪ Metric.sphere (0 : ℂ) 2) A24 := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases hz with hz | hz
    · have := hz.2; have := hz'.1; linarith [hz.2, hz'.1]
    · rw [mem_sphere_iff_norm, sub_zero] at hz
      have := hz'.1; rw [hz] at this; exact lt_irrefl _ this
  have hscale : ∫⁻ z in A24, f z = ∫⁻ z in A12, f z := by
    set G : ℂ → ℝ≥0∞ := A24.indicator f with hG
    have hGm : Measurable G := hfm.indicator hA24m
    have hpt : ∀ z : ℂ, G ((2 : ℝ) • z) = ENNReal.ofReal (1 / 4) * A12.indicator f z := by
      intro z
      have hn : ‖(2 : ℝ) • z‖ = 2 * ‖z‖ := by rw [_root_.norm_smul, Real.norm_two]
      by_cases hz : z ∈ A12
      · have hz' : (2 : ℝ) • z ∈ A24 := by
          simp only [hA24, hA12, mem_ofPred_eq, mem_Ioo, hn] at hz ⊢
          constructor <;> linarith [hz.1, hz.2]
        rw [hG, indicator_of_mem hz', indicator_of_mem hz, hf]
        simp only [hn]
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        have : ‖z‖ ≠ 0 := by
          have := hz.1; intro h; rw [h] at this; norm_num at this
        field_simp
        ring
      · have hz' : (2 : ℝ) • z ∉ A24 := by
          intro h
          apply hz
          simp only [hA24, hA12, mem_ofPred_eq, mem_Ioo, hn] at h ⊢
          constructor <;> linarith [h.1, h.2]
        rw [hG, indicator_of_notMem hz', indicator_of_notMem hz, mul_zero]
    have hmap := lintegral_map hGm (measurable_const_smul (2 : ℝ) : Measurable fun z : ℂ => (2 : ℝ) • z)
      (μ := (volume : Measure ℂ))
    rw [Measure.map_addHaar_smul (volume : Measure ℂ) (by norm_num : (2 : ℝ) ≠ 0), lintegral_smul_measure,
      Complex.finrank_real_complex] at hmap
    simp only [hpt] at hmap
    have hG' : ∫⁻ a, G a = ∫⁻ a in A24, f a := lintegral_indicator hA24m _
    rw [lintegral_const_mul _ (hfm.indicator hA12m), lintegral_indicator hA12m, hG'] at hmap
    have h4 : ENNReal.ofReal |((2 : ℝ) ^ 2)⁻¹| = ENNReal.ofReal (1 / 4) := by
      congr 1; norm_num
    rw [h4, smul_eq_mul] at hmap
    have h0 : ENNReal.ofReal (1 / 4) ≠ 0 := by simp
    exact (ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top).1 hmap
  rw [hsplit, lintegral_union hA24m hd2, lintegral_union (Metric.isClosed_sphere.measurableSet) hd1, hsph, add_zero, hscale, two_mul]

section Final

variable {F : Type} [Field F] [NumberField F]

/-- **The shell ratio**: $\omega_\infty(\mathrm{BinfPos}) = 2^{r_2}\,\omega_\infty(\mathrm{Vone})$. -/
theorem omegaInf_BinfPos : omegaInf F (BinfPos (F := F)) = (2 : ℝ≥0∞) ^ nrComplexPlaces F * omegaInf F (Vone (F := F)) := by
  have h1 : (BinfPos (F := F)) = Units.val ⁻¹' infBoxSet (F := F) (fun _ => Ioo (1 : ℝ) 4)
      (fun _ => {z : ℂ | ‖z‖ ∈ Ioo (1 : ℝ) 4}) := by
    ext t
    simp only [BinfPos, Binf, mem_ofPred_eq, infBoxSet, mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun w => ?_, h2⟩
      have := h3 w
      have h1w := h1 w
      rw [abs_of_pos this] at h1w
      exact h1w
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun w => ?_, h2⟩, fun w => ?_⟩
      · rw [abs_of_pos (one_pos.trans (h1 w).1)]; exact h1 w
      · exact one_pos.trans (h1 w).1
  have h2 : (Vone (F := F)) = Units.val ⁻¹' infBoxSet (F := F) (fun _ => {x : ℝ | |x| ∈ Ioo (1 : ℝ) 2})
      (fun _ => {z : ℂ | ‖z‖ ∈ Ioo (1 : ℝ) 2}) := by
    ext t; rfl
  have hmR : MeasurableSet {x : ℝ | |x| ∈ Ioo (1 : ℝ) 2} := measurableSet_Ioo.preimage continuous_abs.measurable
  rw [h1, h2, omegaInf_box (fun _ => measurableSet_Ioo) (fun _ => measurableSet_normIoo 1 4)
      (fun _ h => by norm_num [mem_Ioo] at h) (fun _ h => by norm_num [mem_Ioo] at h),
    omegaInf_box (fun _ => hmR) (fun _ => measurableSet_normIoo 1 2)
      (fun _ h => by norm_num [mem_Ioo] at h) (fun _ h => by norm_num [mem_Ioo] at h)]
  simp only [lintegral_real_shell_ratio, lintegral_complex_shell_ratio, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  have hc : Fintype.card {w : InfinitePlace F // w.IsComplex} = nrComplexPlaces F := by
    rw [nrComplexPlaces]
  rw [hc]
  ring

theorem omegaInf_BinfPos_ne_zero : omegaInf F (BinfPos (F := F)) ≠ 0 := by
  rw [omegaInf_BinfPos]
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) omegaInf_Vone_ne_zero

theorem omegaInf_BinfPos_ne_top : omegaInf F (BinfPos (F := F)) ≠ ∞ := by
  rw [omegaInf_BinfPos]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) omegaInf_Vone_ne_top

end Final

end QuadFormsKB.Tamagawa.Measure.Weil
