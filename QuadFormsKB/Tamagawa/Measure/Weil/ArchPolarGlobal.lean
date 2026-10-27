import QuadFormsKB.Tamagawa.Measure.ArchPolar
import QuadFormsKB.Tamagawa.Measure.PiProdLintegral
import QuadFormsKB.Tamagawa.Measure.Weil.QuatInfinite
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures

/-!
# Polar coordinates for $(D\otimes F_\infty)^\times$ over all archimedean places

**Layer:** $F$ a number field with $r_1$ real and $r_2$ complex places, $D\otimes F_\infty = \mathbb H[F_\infty,a,b]$ (`QuatInf`)
with Weil's measure $\Omega = \|\operatorname{nrd}x\|_\infty^{-2}dx_\infty$ (`omegaQuatInf`, $dx_\infty$ the self-dual measure in the
coordinates $1, i, j, k$), and $\omega = |t|_\infty^{-1}dt$ on $F_\infty^\times$ (`omegaInf`). At each place $w$ let $Q_w$ be a
quaternary form with $Q_w(x_w) = \operatorname{nrd}(x)_w$ in the coordinates of $x$ at $w$ (`quatCoordR`, `quatCoordC`).

For sets $A_w\subseteq\{Q_w = 1\}$ and radial sets $T_w$ ($\log$-radii at a real place, $T_w\subseteq\{\operatorname{Re}\beta>0\}$ at a
complex place), the **cone** $Y = \{x : x_w\in\mathrm{cone}(T_w,A_w)\ \forall w\}$ (`archCone`) and its reduced-norm shell
$N = \{t : t_w\in e^{2T_w}\ (w\text{ real}),\ t_w\in T_w^2\ (w\text{ complex})\}$ (`nrdShell`) satisfy

* **`omegaQuatInf_archCone`**: $\Omega(Y) = 2^{4r_2}\prod_{w\text{ real}}\nu_w(A_w)\,\mathrm{Leb}(T_w)\prod_{w\text{ complex}}\nu_w(A_w)
  \int_{T_w}|\beta|^{-2}d^2\beta$;
* **`omegaInf_nrdShell`**: $\omega(N) = 2^{r_2}\prod_{w\text{ real}}2\,\mathrm{Leb}(T_w)\prod_{w\text{ complex}}4\int_{T_w}|\beta|^{-2}d^2\beta$;
* **`omegaQuatInf_archCone_eq`**: $\Omega(Y) = 8^{r_2}\,\sigma(A)\,\omega(N)$, $\sigma(A) = \prod_w\sigma_w(A_w)$ the product of the sphere Leray
  measures (`SphereLeray.sig`, `SphereLerayC.sigC`).

The proof reorders the coordinates $(\mathbb R^{r_1}\times\mathbb C^{r_2})^4\cong\prod_w F_w^4$ (`coordSplit`, measure preserving) and uses
the local polar identities of `ArchPolar.lean` place by place.
-/

open MeasureTheory Measure Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Tamagawa.Measure.ArchPolar
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

local notation "ιR" => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "ιC" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-! ### Reordering the coordinates -/

/-- $(F_\infty)^4\to\prod_{w\text{ real}}\mathbb R^4\times\prod_{w\text{ complex}}\mathbb C^4$. -/
def coordSplit (c : Fin 4 → mixedSpace F) : (ιR → Fin 4 → ℝ) × (ιC → Fin 4 → ℂ) :=
  (fun w i => (c i).1 w, fun w i => (c i).2 w)

theorem measurable_coordSplit : Measurable (coordSplit (F := F)) := by
  refine Measurable.prodMk ?_ ?_ <;> refine measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun i => ?_
  · exact (measurable_pi_apply w).comp (measurable_fst.comp (measurable_pi_apply i))
  · exact (measurable_pi_apply w).comp (measurable_snd.comp (measurable_pi_apply i))

theorem measurePreserving_coordSplit :
    MeasurePreserving (coordSplit (F := F)) (Measure.pi fun _ : Fin 4 => (volume : Measure (mixedSpace F)))
      ((Measure.pi fun _ : ιR => Measure.pi fun _ : Fin 4 => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : ιC => Measure.pi fun _ : Fin 4 => (volume : Measure ℂ))) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow (ιR → ℝ) (ιC → ℂ) (Fin 4)
    (fun _ => (volume : Measure (ιR → ℝ))) (fun _ => (volume : Measure (ιC → ℂ)))
  have h2 := (measurePreserving_piComm (ι := Fin 4) (κ := ιR) (volume : Measure ℝ)).prod
    (measurePreserving_piComm (ι := Fin 4) (κ := ιC) (volume : Measure ℂ))
  have e : (Measure.pi fun _ : Fin 4 => (volume : Measure (mixedSpace F))) =
      Measure.pi fun _ : Fin 4 => (volume : Measure (ιR → ℝ)).prod (volume : Measure (ιC → ℂ)) := rfl
  rw [e]
  have e2 : (volume : Measure (ιR → ℝ)) = Measure.pi fun _ => volume := rfl
  have e3 : (volume : Measure (ιC → ℂ)) = Measure.pi fun _ => volume := rfl
  rw [e2, e3] at h1
  exact h2.comp h1

theorem pi_const_smul {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : ℝ≥0) : Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq (μ := fun _ : ι => c • μ) fun s _ => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, nnreal_smul_coe_apply, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]

/-- `muInfVec F (Fin 4)` in the reordered coordinates: $2^{4r_2}$ times Lebesgue measure. -/
theorem map_coordSplit_muInfVec :
    (muInfVec F (Fin 4)).map coordSplit = ((2 : ℝ≥0∞) ^ (4 * nrComplexPlaces F)) •
      ((Measure.pi fun _ : ιR => Measure.pi fun _ : Fin 4 => (volume : Measure ℝ)).prod
        (Measure.pi fun _ : ιC => Measure.pi fun _ : Fin 4 => (volume : Measure ℂ))) := by
  rw [muInfVec, Analysis.selfDualInf, pi_const_smul, Measure.map_smul, measurePreserving_coordSplit.map_eq,
    Fintype.card_fin, ← pow_mul, mul_comm, ENNReal.smul_def]
  · push_cast; rfl
  · exact measurable_coordSplit.aemeasurable

/-! ### The coordinates of a quaternion at a place -/

variable (a b : F)

/-- The coordinates $(x_0, x_1, x_2, x_3)$ of $x$ at a real place. -/
def quatCoordR (w : ιR) (x : QuatInf a b) : Fin 4 → ℝ := fun i => (quatInfCLE a b x i).1 w

/-- The coordinates of $x$ at a complex place. -/
def quatCoordC (w : ιC) (x : QuatInf a b) : Fin 4 → ℂ := fun i => (quatInfCLE a b x i).2 w

theorem coordSplit_quatInfCLE (x : QuatInf a b) :
    coordSplit (quatInfCLE a b x) = (fun w => quatCoordR a b w x, fun w => quatCoordC a b w x) := rfl

/-! ### $\Omega$ as an integral over $D\otimes F_\infty$ -/

/-- The density of $\Omega$: $\|\operatorname{nrd}x\|_\infty^{-2} = |\det_{\mathbb R}(\operatorname{nrd}(x)^2\cdot)|^{-1}$. -/
def omegaDens (x : QuatInf a b) : ℝ≥0∞ :=
  ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (nrdInf a b x ^ 2))|⁻¹

theorem measurable_omegaDens : Measurable (omegaDens a b) :=
  Measurable.ennreal_ofReal ((continuous_abs_det_mulLeft.comp ((continuous_nrdInf a b).pow 2)).measurable.inv)

theorem omegaQuatInf_apply {S : Set (QuatInf a b)ˣ} (hS : MeasurableSet S) :
    omegaQuatInf a b S = ∫⁻ x in Units.val '' S, omegaDens a b x ∂quatInfVol a b := by
  have he := (isOpenEmbedding_val_quatInf a b).measurableEmbedding
  have hd : ∀ u : (QuatInf a b)ˣ, (distribHaarChar (QuatInf a b) u⁻¹ : ℝ≥0∞) = omegaDens a b u := fun u => by
    rw [← ENNReal.ofReal_coe_nnreal, distribHaarChar_quatInf, inv_inv, omegaDens]
  rw [omegaQuatInf, unitsHaar, withDensity_apply _ hS]
  simp_rw [hd]
  calc ∫⁻ u in S, omegaDens a b u ∂(quatInfVol a b).comap Units.val
      = ∫⁻ u, omegaDens a b u ∂(((quatInfVol a b).restrict (Units.val '' S)).comap Units.val) := by
        rw [he.restrict_comap]
    _ = ∫⁻ x, omegaDens a b x ∂((((quatInfVol a b).restrict (Units.val '' S)).comap Units.val).map Units.val) :=
        (he.lintegral_map _).symm
    _ = _ := by
        rw [he.map_comap, Measure.restrict_restrict he.measurableSet_range,
          inter_eq_right.2 (image_subset_range _ _)]

theorem setLIntegral_quatInfVol {C : Set (QuatInf a b)} (shellDensC : MeasurableSet C) {g : QuatInf a b → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x in C, g x ∂quatInfVol a b =
      ∫⁻ c, (quatInfCLE a b '' C).indicator (fun c => g ((quatInfCLE a b).symm c)) c ∂muInfVec F (Fin 4) := by
  have hm : Measurable (quatInfCLE a b).symm := (quatInfCLE a b).symm.continuous.measurable
  rw [← lintegral_indicator shellDensC, quatInfVol, lintegral_map (hg.indicator shellDensC) hm]
  refine lintegral_congr fun c => ?_
  by_cases hc : c ∈ quatInfCLE a b '' C
  · obtain ⟨x, hx, rfl⟩ := hc
    rw [indicator_of_mem (mem_image_of_mem _ hx), ContinuousLinearEquiv.symm_apply_apply, indicator_of_mem hx]
  · rw [indicator_of_notMem hc, indicator_of_notMem]
    intro h; exact hc ⟨_, h, ContinuousLinearEquiv.apply_symm_apply _ _⟩

/-! ### The cone and the shell -/

-- (`local notation` must not occur in `variable` types: it silently breaks the later declarations.)
variable {a b}
variable (QR : {w : InfinitePlace F // w.IsReal} → QuadForm ℝ 4)
  (QC : {w : InfinitePlace F // w.IsComplex} → QuadForm ℂ 4)
  (hQR : ∀ (w : {w : InfinitePlace F // w.IsReal}) (x : QuatInf a b),
    (QR w).eval (quatCoordR a b w x) = (nrdInf a b x).1 w)
  (hQC : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (x : QuatInf a b),
    (QC w).eval (quatCoordC a b w x) = (nrdInf a b x).2 w)
  (TR : {w : InfinitePlace F // w.IsReal} → Set ℝ)
  (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (SphereLeray.Sph (QR w) 1))
  (TC : {w : InfinitePlace F // w.IsComplex} → Set ℂˣ)
  (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphereLerayC.SphC (QC w) 1))

/-- **The archimedean cone** $Y$ in $D\otimes F_\infty$: the $x$ with $x_w\in\mathrm{cone}(T_w, A_w)$ at every place $w$. -/
def archConeSet : Set (QuatInf a b) :=
  {x | (∀ w : ιR, quatCoordR a b w x ∈ coneR (QR w) (TR w) (AR w)) ∧ ∀ w : ιC, quatCoordC a b w x ∈ coneC (QC w) (TC w) (AC w)}


include hQR hQC in
theorem nrdInf_ne_zero_of_mem_archConeSet {x : QuatInf a b} (hx : x ∈ archConeSet QR QC TR AR TC AC)
    (_hTC : ∀ w, TC w ⊆ SphereLerayC.halfU) : IsUnit (nrdInf a b x) := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  refine ⟨fun w => ?_, fun w => ?_⟩
  · obtain ⟨⟨t, y⟩, -, hy⟩ := hx.1 w
    rw [← hQR, ← hy, SphereLeray.eval_pol, mul_one]
    exact (Real.exp_pos _).ne'.isUnit
  · obtain ⟨⟨β, y⟩, -, hy⟩ := hx.2 w
    rw [← hQC, ← hy, SphereLerayC.eval_polC, mul_one]
    exact (pow_ne_zero 2 β.ne_zero).isUnit

/-- The local densities: $|Q_w|^{-2}$ on the real cone, $|Q_w|^{-4}$ on the complex cone. -/
def coneDensR (w : ιR) : (Fin 4 → ℝ) → ℝ≥0∞ :=
  (coneR (QR w) (TR w) (AR w)).indicator fun v => ENNReal.ofReal (((QR w).eval v) ^ 2)⁻¹

def coneDensC (w : ιC) : (Fin 4 → ℂ) → ℝ≥0∞ :=
  (coneC (QC w) (TC w) (AC w)).indicator fun v => ENNReal.ofReal (‖(QC w).eval v‖ ^ 4)⁻¹

theorem det_mulLeft_sq (s : mixedSpace F) :
    |LinearMap.det (LinearMap.mulLeft ℝ (s ^ 2))| = (∏ w, (s.1 w) ^ 2) * ∏ w, ‖s.2 w‖ ^ 4 := by
  rw [det_mulLeft_mixedSpace]
  have h1 : ∀ w, (s ^ 2).1 w = (s.1 w) ^ 2 := fun w => rfl
  have h2 : ∀ w, (s ^ 2).2 w = (s.2 w) ^ 2 := fun w => rfl
  simp_rw [h1, h2, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul]
  exact abs_of_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _)
    (Finset.prod_nonneg fun _ _ => by positivity))

include hQR hQC in
theorem omegaDens_eq_prod (x : QuatInf a b) (hx : x ∈ archConeSet QR QC TR AR TC AC) :
    omegaDens a b x = (∏ w, coneDensR QR TR AR w (quatCoordR a b w x)) * ∏ w, coneDensC QC TC AC w (quatCoordC a b w x) := by
  rw [omegaDens, det_mulLeft_sq]
  simp only [coneDensR, coneDensC]
  rw [Finset.prod_congr rfl fun w _ => indicator_of_mem (hx.1 w) _,
    Finset.prod_congr rfl fun w _ => indicator_of_mem (hx.2 w) _]
  simp_rw [hQR, hQC]
  rw [mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 (Finset.prod_nonneg fun _ _ => sq_nonneg _)),
    ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ENNReal.ofReal_prod_of_nonneg fun _ _ => inv_nonneg.2 (sq_nonneg _),
    ENNReal.ofReal_prod_of_nonneg fun _ _ => inv_nonneg.2 (by positivity)]

theorem prod_coneDens_eq_zero (x : QuatInf a b) (hx : x ∉ archConeSet QR QC TR AR TC AC) :
    (∏ w, coneDensR QR TR AR w (quatCoordR a b w x)) * ∏ w, coneDensC QC TC AC w (quatCoordC a b w x) = 0 := by
  simp only [archConeSet, mem_ofPred_eq, not_and_or, not_forall] at hx
  rcases hx with ⟨w, hw⟩ | ⟨w, hw⟩
  · rw [Finset.prod_eq_zero (Finset.mem_univ w) (indicator_of_notMem hw _), zero_mul]
  · rw [Finset.prod_eq_zero (Finset.mem_univ w) (indicator_of_notMem hw _), mul_zero]

theorem measurable_coneDensR (hT : ∀ w, MeasurableSet (TR w)) (hA : ∀ w, MeasurableSet (AR w)) (w : ιR) :
    Measurable (coneDensR QR TR AR w) :=
  (Measurable.ennreal_ofReal ((((QuadFormsKB.Siegel.continuous_eval_real (QR w))).measurable.pow_const 2).inv)).indicator
    (measurableSet_coneR _ (hT w) (hA w))

theorem measurable_coneDensC (hT : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU)
    (hA : ∀ w, MeasurableSet (AC w)) (w : ιC) : Measurable (coneDensC QC TC AC w) :=
  (Measurable.ennreal_ofReal ((((SphereLerayC.continuous_evalC (QC w)).norm).measurable.pow_const 4).inv)).indicator
    (measurableSet_coneC _ (hT w) (hTh w) (hA w))

theorem lintegral_coneDensR (hT : ∀ w, MeasurableSet (TR w)) (hA : ∀ w, MeasurableSet (AR w)) (w : ιR) :
    ∫⁻ v, coneDensR QR TR AR w v ∂(Measure.pi fun _ : Fin 4 => (volume : Measure ℝ)) =
      SphereLeray.nu (QR w) 1 (AR w) * volume (TR w) := by
  rw [← volume_pi, coneDensR, lintegral_indicator (measurableSet_coneR _ (hT w) (hA w)), lintegral_coneR _ (hT w) (hA w)]

theorem lintegral_coneDensC (hT : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU)
    (hA : ∀ w, MeasurableSet (AC w)) (w : ιC) :
    ∫⁻ v, coneDensC QC TC AC w v ∂(Measure.pi fun _ : Fin 4 => (volume : Measure ℂ)) =
      SphereLerayC.nuC (QC w) 1 (AC w) * ∫⁻ β in TC w, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ ∂SphereLerayC.volU := by
  rw [← volume_pi, coneDensC, lintegral_indicator (measurableSet_coneC _ (hT w) (hTh w) (hA w)),
    lintegral_coneC _ (hT w) (hTh w) (hA w)]

/-- The cone as a set of units. -/
def archCone : Set (QuatInf a b)ˣ := Units.val ⁻¹' archConeSet QR QC TR AR TC AC

theorem measurableSet_archConeSet (hTR : ∀ w, MeasurableSet (TR w)) (hAR : ∀ w, MeasurableSet (AR w))
    (hTC : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hAC : ∀ w, MeasurableSet (AC w)) :
    MeasurableSet (archConeSet (a := a) (b := b) QR QC TR AR TC AC) := by
  have shellDensR : ∀ w, Measurable (quatCoordR a b w) := fun w => measurable_pi_iff.2 fun i =>
    (measurable_pi_apply w).comp (measurable_fst.comp ((measurable_pi_apply i).comp
      (quatInfCLE a b).continuous.measurable))
  have shellDensC : ∀ w, Measurable (quatCoordC a b w) := fun w => measurable_pi_iff.2 fun i =>
    (measurable_pi_apply w).comp (measurable_snd.comp ((measurable_pi_apply i).comp
      (quatInfCLE a b).continuous.measurable))
  have e : archConeSet (a := a) (b := b) QR QC TR AR TC AC =
      (⋂ w, quatCoordR a b w ⁻¹' coneR (QR w) (TR w) (AR w)) ∩ ⋂ w, quatCoordC a b w ⁻¹' coneC (QC w) (TC w) (AC w) := by
    ext x; simp [archConeSet]
  rw [e]
  refine (MeasurableSet.iInter fun w => ?_).inter (MeasurableSet.iInter fun w => ?_)
  · exact (measurableSet_coneR _ (hTR w) (hAR w)).preimage (shellDensR w)
  · exact (measurableSet_coneC _ (hTC w) (hTh w) (hAC w)).preimage (shellDensC w)

include hQR hQC in
theorem image_val_archCone (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) :
    Units.val '' archCone (a := a) (b := b) QR QC TR AR TC AC = archConeSet QR QC TR AR TC AC := by
  refine (image_preimage_eq_of_subset fun x hx => ?_)
  have hu := nrdInf_ne_zero_of_mem_archConeSet QR QC hQR hQC TR AR TC AC hx hTh
  exact ⟨((isUnit_iff_isUnit_nrdInf a b x).2 hu).unit, rfl⟩

include hQR hQC in
/-- **$\Omega$ of the archimedean cone**:
$\Omega(Y) = 2^{4r_2}\prod_{w\text{ real}}\nu_w(A_w)\,\mathrm{Leb}(T_w)\prod_{w\text{ complex}}\nu_w(A_w)\int_{T_w}|\beta|^{-2}d^2\beta$. -/
theorem omegaQuatInf_archCone (hTR : ∀ w, MeasurableSet (TR w)) (hAR : ∀ w, MeasurableSet (AR w))
    (hTC : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hAC : ∀ w, MeasurableSet (AC w)) :
    omegaQuatInf a b (archCone QR QC TR AR TC AC) =
      (2 : ℝ≥0∞) ^ (4 * nrComplexPlaces F) * ((∏ w, SphereLeray.nu (QR w) 1 (AR w) * volume (TR w)) *
        ∏ w, SphereLerayC.nuC (QC w) 1 (AC w) *
          ∫⁻ β in TC w, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ ∂SphereLerayC.volU) := by
  have hCm := measurableSet_archConeSet (a := a) (b := b) QR QC TR AR TC AC hTR hAR hTC hTh hAC
  have hSm : MeasurableSet (archCone (a := a) (b := b) QR QC TR AR TC AC) :=
    hCm.preimage Units.continuous_val.measurable
  rw [omegaQuatInf_apply a b hSm, image_val_archCone QR QC hQR hQC TR AR TC AC hTh,
    setLIntegral_quatInfVol a b hCm (measurable_omegaDens a b)]
  set Φ : (ιR → Fin 4 → ℝ) × (ιC → Fin 4 → ℂ) → ℝ≥0∞ := fun p =>
    (∏ w, coneDensR QR TR AR w (p.1 w)) * ∏ w, coneDensC QC TC AC w (p.2 w)
  have hΦ : ∀ c, (quatInfCLE a b '' archConeSet QR QC TR AR TC AC).indicator
      (fun c => omegaDens a b ((quatInfCLE a b).symm c)) c = Φ (coordSplit c) := fun c => by
    set x := (quatInfCLE a b).symm c
    have hc : c = quatInfCLE a b x := ((quatInfCLE a b).apply_symm_apply c).symm
    rw [hc, coordSplit_quatInfCLE]
    simp only [Φ]
    by_cases hx : x ∈ archConeSet QR QC TR AR TC AC
    · rw [indicator_of_mem (mem_image_of_mem _ hx), ContinuousLinearEquiv.symm_apply_apply,
        omegaDens_eq_prod QR QC hQR hQC TR AR TC AC x hx]
    · rw [indicator_of_notMem (by
        rintro ⟨y, hy, hxy⟩
        rw [(quatInfCLE a b).injective hxy] at hy; exact hx hy), prod_coneDens_eq_zero QR QC TR AR TC AC x hx]
  have hmR := measurable_coneDensR QR TR AR hTR hAR
  have hmC := measurable_coneDensC QC TC AC hTC hTh hAC
  have hΦm : Measurable Φ :=
    (Finset.measurable_prod _ fun w _ => (hmR w).comp ((measurable_pi_apply w).comp measurable_fst)).mul
      (Finset.measurable_prod _ fun w _ => (hmC w).comp ((measurable_pi_apply w).comp measurable_snd))
  simp_rw [hΦ]
  rw [← lintegral_map hΦm measurable_coordSplit, map_coordSplit_muInfVec, lintegral_smul_measure]
  congr 1
  have hfR : Measurable fun y : {w : InfinitePlace F // w.IsReal} → Fin 4 → ℝ => ∏ w, coneDensR QR TR AR w (y w) :=
    Finset.measurable_prod _ fun w _ => (hmR w).comp (measurable_pi_apply w)
  have hfC : Measurable fun y : {w : InfinitePlace F // w.IsComplex} → Fin 4 → ℂ => ∏ w, coneDensC QC TC AC w (y w) :=
    Finset.measurable_prod _ fun w _ => (hmC w).comp (measurable_pi_apply w)
  rw [show Φ = fun p => (∏ w, coneDensR QR TR AR w (p.1 w)) * ∏ w, coneDensC QC TC AC w (p.2 w) from rfl,
    lintegral_prod_mul hfR.aemeasurable hfC.aemeasurable, lintegral_pi_prod _ hmR, lintegral_pi_prod _ hmC]
  simp_rw [lintegral_coneDensR QR TR AR hTR hAR, lintegral_coneDensC QC TC AC hTC hTh hAC]

/-! ### The reduced-norm shell -/

variable (F) in
/-- **The shell** $N = \{t : t_w\in e^{2T_w}\ (w\text{ real}),\ t_w\in T_w^2\ (w\text{ complex})\}\subseteq F_\infty$. -/
def nrdShellSet (TR : ιR → Set ℝ) (TC : ιC → Set ℂˣ) : Set (mixedSpace F) :=
  {t | (∀ w, t.1 w ∈ (fun s : ℝ => Real.exp (2 * s)) '' TR w) ∧
    ∀ w, t.2 w ∈ (fun z : ℂ => z ^ 2) '' (Units.val '' TC w)}

variable (F) in
/-- The shell as a set of units of $F_\infty$. -/
def nrdShell (TR : ιR → Set ℝ) (TC : ιC → Set ℂˣ) : Set (mixedSpace F)ˣ := Units.val ⁻¹' nrdShellSet F TR TC

theorem isUnit_of_mem_shellSet {TR : ιR → Set ℝ} {TC : ιC → Set ℂˣ} {t : mixedSpace F}
    (ht : t ∈ nrdShellSet F TR TC) : IsUnit t := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  refine ⟨fun w => ?_, fun w => ?_⟩
  · obtain ⟨s, -, hs⟩ := ht.1 w
    rw [← hs]; exact (Real.exp_pos _).ne'.isUnit
  · obtain ⟨_, ⟨β, -, rfl⟩, hs⟩ := ht.2 w
    rw [← hs]; exact (pow_ne_zero 2 β.ne_zero).isUnit

/-- The local densities of $\omega$ on the shell. -/
def shellDensR (TR : ιR → Set ℝ) (w : ιR) : ℝ → ℝ≥0∞ :=
  ((fun s : ℝ => Real.exp (2 * s)) '' TR w).indicator fun t => ENNReal.ofReal |t|⁻¹

def shellDensC (TC : ιC → Set ℂˣ) (w : ιC) : ℂ → ℝ≥0∞ :=
  ((fun z : ℂ => z ^ 2) '' (Units.val '' TC w)).indicator fun t => ENNReal.ofReal (‖t‖ ^ 2)⁻¹

theorem measurableSet_expImage {T : Set ℝ} (hT : MeasurableSet T) :
    MeasurableSet ((fun s : ℝ => Real.exp (2 * s)) '' T) :=
  hT.image_of_continuousOn_injOn (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    fun x _ y _ h => by have := Real.exp_injective h; simpa using this

theorem measurableSet_sqImage {T : Set ℂˣ} (hT : MeasurableSet T) (hTh : T ⊆ SphereLerayC.halfU) :
    MeasurableSet ((fun z : ℂ => z ^ 2) '' (Units.val '' T)) := by
  have hTm : MeasurableSet (Units.val '' T) := SphereLerayC.measurableEmbedding_val.measurableSet_image.2 hT
  refine hTm.image_of_continuousOn_injOn (continuous_pow 2).continuousOn ?_
  rintro _ ⟨β, hβ, rfl⟩ _ ⟨γ, hγ, rfl⟩ h
  have hβ' : 0 < (β : ℂ).re := hTh hβ
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact h
  · exfalso
    have hγ' : 0 < (γ : ℂ).re := hTh hγ
    have := congrArg Complex.re h
    rw [Complex.neg_re] at this; linarith

theorem measurableSet_shellSet {TR : ιR → Set ℝ} {TC : ιC → Set ℂˣ} (hTR : ∀ w, MeasurableSet (TR w))
    (hTC : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) :
    MeasurableSet (nrdShellSet F TR TC) := by
  have e : nrdShellSet F TR TC = (⋂ w : ιR, (fun t : mixedSpace F => t.1 w) ⁻¹'
      ((fun s : ℝ => Real.exp (2 * s)) '' TR w)) ∩
      ⋂ w : ιC, (fun t : mixedSpace F => t.2 w) ⁻¹' ((fun z : ℂ => z ^ 2) '' (Units.val '' TC w)) := by
    ext t; simp [nrdShellSet]
  rw [e]
  refine (MeasurableSet.iInter fun w => ?_).inter (MeasurableSet.iInter fun w => ?_)
  · exact (measurableSet_expImage (hTR w)).preimage ((measurable_pi_apply w).comp measurable_fst)
  · exact (measurableSet_sqImage (hTC w) (hTh w)).preimage ((measurable_pi_apply w).comp measurable_snd)

theorem det_mulLeft_abs (t : mixedSpace F) :
    |LinearMap.det (LinearMap.mulLeft ℝ t)| = (∏ w, |t.1 w|) * ∏ w, ‖t.2 w‖ ^ 2 := by
  rw [det_mulLeft_mixedSpace, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  exact Finset.prod_congr rfl fun w _ => by rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

/-- **$\omega$ of the shell**: $\omega(N) = 2^{r_2}\prod_{w\text{ real}}2\,\mathrm{Leb}(T_w)
\prod_{w\text{ complex}}4\int_{T_w}|\beta|^{-2}d^2\beta$. -/
theorem omegaInf_nrdShell {TR : ιR → Set ℝ} {TC : ιC → Set ℂˣ} (hTR : ∀ w, MeasurableSet (TR w))
    (hTC : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) :
    omegaInf F (nrdShell F TR TC) = (2 : ℝ≥0∞) ^ nrComplexPlaces F * ((∏ w, 2 * volume (TR w)) *
      ∏ w, 4 * ∫⁻ β in TC w, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ ∂SphereLerayC.volU) := by
  have he := isOpenEmbedding_val_mixedSpace (F := F) |>.measurableEmbedding
  have hNm := measurableSet_shellSet (F := F) hTR hTC hTh
  have hSm : MeasurableSet (nrdShell F TR TC) := hNm.preimage Units.continuous_val.measurable
  have himg : Units.val '' nrdShell F TR TC = nrdShellSet F TR TC :=
    image_preimage_eq_of_subset fun t ht => ⟨(isUnit_of_mem_shellSet ht).unit, rfl⟩
  have hmR : ∀ w, Measurable (shellDensR TR w) := fun w =>
    (Measurable.ennreal_ofReal (measurable_id.abs.inv)).indicator (measurableSet_expImage (hTR w))
  have hmC : ∀ w, Measurable (shellDensC TC w) := fun w =>
    (Measurable.ennreal_ofReal ((continuous_norm.measurable.pow_const 2).inv)).indicator
      (measurableSet_sqImage (hTC w) (hTh w))
  rw [omegaInf_eq, withDensity_apply _ hSm]
  have hd : Measurable fun t : mixedSpace F => ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ t)|⁻¹ :=
    Measurable.ennreal_ofReal (continuous_abs_det_mulLeft.measurable.inv)
  set g : mixedSpace F → ℝ≥0∞ := fun t => ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ t)|⁻¹
  calc ∫⁻ u in nrdShell F TR TC, ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (u : mixedSpace F))|⁻¹
        ∂(Analysis.selfDualInf (F := F)).comap Units.val
      = ∫⁻ u, g u ∂(((Analysis.selfDualInf (F := F)).restrict (Units.val '' nrdShell F TR TC)).comap Units.val) := by
        rw [he.restrict_comap]
    _ = ∫⁻ t, g t ∂((((Analysis.selfDualInf (F := F)).restrict (Units.val '' nrdShell F TR TC)).comap
          Units.val).map Units.val) := (he.lintegral_map _).symm
    _ = ∫⁻ t in nrdShellSet F TR TC, g t ∂Analysis.selfDualInf (F := F) := by
        rw [he.map_comap, Measure.restrict_restrict he.measurableSet_range,
          inter_eq_right.2 (image_subset_range _ _), himg]
    _ = ∫⁻ t, (∏ w, shellDensR TR w (t.1 w)) * ∏ w, shellDensC TC w (t.2 w) ∂Analysis.selfDualInf (F := F) := by
        rw [← lintegral_indicator hNm]
        refine lintegral_congr fun t => ?_
        by_cases ht : t ∈ nrdShellSet F TR TC
        · simp only [shellDensR, shellDensC, g]
          rw [indicator_of_mem ht, Finset.prod_congr rfl fun w _ => indicator_of_mem (ht.1 w) _,
            Finset.prod_congr rfl fun w _ => indicator_of_mem (ht.2 w) _, det_mulLeft_abs, mul_inv,
            ENNReal.ofReal_mul (inv_nonneg.2 (Finset.prod_nonneg fun _ _ => abs_nonneg _)),
            ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
            ENNReal.ofReal_prod_of_nonneg fun _ _ => inv_nonneg.2 (abs_nonneg _),
            ENNReal.ofReal_prod_of_nonneg fun _ _ => inv_nonneg.2 (by positivity)]
        · rw [indicator_of_notMem ht]
          have ht' : ¬ ((∀ w, t.1 w ∈ (fun s : ℝ => Real.exp (2 * s)) '' TR w) ∧
              ∀ w, t.2 w ∈ (fun z : ℂ => z ^ 2) '' (Units.val '' TC w)) := ht
          simp only [not_and_or, not_forall] at ht'
          rcases ht' with ⟨w, hw⟩ | ⟨w, hw⟩
          · rw [Finset.prod_eq_zero (Finset.mem_univ w) (indicator_of_notMem hw _), zero_mul]
          · rw [Finset.prod_eq_zero (Finset.mem_univ w) (indicator_of_notMem hw _), mul_zero]
    _ = _ := by
        rw [Analysis.selfDualInf, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
        push_cast
        congr 1
        have hfR : Measurable fun y : ιR → ℝ => ∏ w, shellDensR TR w (y w) :=
          Finset.measurable_prod _ fun w _ => (hmR w).comp (measurable_pi_apply w)
        have hfC : Measurable fun y : ιC → ℂ => ∏ w, shellDensC TC w (y w) :=
          Finset.measurable_prod _ fun w _ => (hmC w).comp (measurable_pi_apply w)
        rw [show (volume : Measure (mixedSpace F)) = (volume : Measure (ιR → ℝ)).prod volume from rfl,
          lintegral_prod_mul hfR.aemeasurable hfC.aemeasurable,
          show (volume : Measure (ιR → ℝ)) = Measure.pi fun _ => volume from rfl,
          show (volume : Measure (ιC → ℂ)) = Measure.pi fun _ => volume from rfl,
          lintegral_pi_prod _ hmR, lintegral_pi_prod _ hmC]
        congr 1
        · refine Finset.prod_congr rfl fun w _ => ?_
          rw [shellDensR, lintegral_indicator (measurableSet_expImage (hTR w)), ← lintegral_expImage (hTR w)]
          refine setLIntegral_congr_fun (measurableSet_expImage (hTR w)) fun t ht => ?_
          obtain ⟨s, -, rfl⟩ := ht
          rw [abs_of_pos (Real.exp_pos _)]
        · refine Finset.prod_congr rfl fun w _ => ?_
          rw [shellDensC, lintegral_indicator (measurableSet_sqImage (hTC w) (hTh w)), lintegral_sqImage (hTC w) (hTh w)]

include hQR hQC in
/-- **Polar coordinates on $(D\otimes F_\infty)^\times$**: $\Omega(Y) = 8^{r_2}\,\sigma(A)\,\omega(N)$, with
$\sigma(A) = \prod_{w\text{ real}}\sigma_w(A_w)\prod_{w\text{ complex}}\sigma_w(A_w)$ the product of the sphere Leray measures of the
forms $Q_w$ at $Q_w = 1$. -/
theorem omegaQuatInf_archCone_eq (hTR : ∀ w, MeasurableSet (TR w)) (hAR : ∀ w, MeasurableSet (AR w))
    (hTC : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hAC : ∀ w, MeasurableSet (AC w)) :
    omegaQuatInf a b (archCone QR QC TR AR TC AC) =
      (8 : ℝ≥0∞) ^ nrComplexPlaces F * ((∏ w, SphereLeray.sig (QR w) 1 (AR w)) *
        ∏ w, SphereLerayC.sigC (QC w) 1 (AC w)) * omegaInf F (nrdShell F TR TC) := by
  rw [omegaQuatInf_archCone QR QC hQR hQC TR AR TC AC hTR hAR hTC hTh hAC, omegaInf_nrdShell hTR hTC hTh]
  have hnu : ∀ w, SphereLeray.nu (QR w) 1 (AR w) = 2 * SphereLeray.sig (QR w) 1 (AR w) := fun w => by
    rw [SphereLeray.sig, Measure.smul_apply, smul_eq_mul, ← mul_assoc, abs_one, mul_one,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hnuC : ∀ w, SphereLerayC.nuC (QC w) 1 (AC w) = 4 * SphereLerayC.sigC (QC w) 1 (AC w) := fun w => by
    rw [SphereLerayC.nuC_eq_smul_sigC one_ne_zero, Measure.smul_apply, smul_eq_mul, mul_one]
    congr 1
    rw [show ‖(2 : ℂ)‖₊ = 2 by ext; simp]
    norm_num
  simp_rw [hnu, hnuC]
  rw [show (8 : ℝ≥0∞) = 2 ^ 3 by norm_num, ← pow_mul,
    show 4 * nrComplexPlaces F = 3 * nrComplexPlaces F + nrComplexPlaces F by ring, pow_add]
  simp only [Finset.prod_mul_distrib]
  ring

end QuadFormsKB.Tamagawa.Measure.Weil

end
