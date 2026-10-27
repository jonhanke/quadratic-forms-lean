import QuadFormsKB.Tamagawa.Measure.SphereLeray
import QuadFormsKB.Tamagawa.Measure.SphereLerayC

/-!
# Polar coordinates for the quaternion units at one archimedean place

**Layer:** one archimedean place, a quaternary form $Q$ over $\mathbb R$ or $\mathbb C$ (any signature; for the norm form
$\langle1,-a,-b,ab\rangle$ of a quaternion algebra, $Q = \operatorname{nrd}$), the sphere $S_1 = \{Q = 1\}$ with its Leray
measure $\sigma = \sigma_1$ (`SphereLeray.sig`, `SphereLerayC.sigC`) and cone measure $\nu = \nu_1$.

For $A\subseteq S_1$ and a set $T$ of radial parameters, the **cone** over $A$ is $\{rx : r\in T,\ x\in A\}$
(`coneR`, real: $r = e^t$, $t\in T$; `coneC`, complex: $r = \beta\in T\subseteq\{\operatorname{Re}\beta>0\}$).

* **`lintegral_coneR`**: $\int_{\mathrm{cone}}|Q(y)|^{-2}\,dy = \nu(A)\cdot\mathrm{Leb}(T)$ (real, $n = 4$);
* **`lintegral_expImage`**: $\int_{\{e^{2t} : t\in T\}}dt'/t' = 2\,\mathrm{Leb}(T)$, so $\nu = 2\sigma$ gives
  $\int_{\mathrm{cone}}|Q|^{-2} = \sigma(A)\int_{Q(\mathrm{cone})}|t|^{-1}dt$;
* **`lintegral_coneC`**: $\int_{\mathrm{cone}}|Q(y)|^{-4}\,d^8y = \nu(A)\int_T|\beta|^{-2}d^2\beta$ (complex, $n = 4$);
* **`lintegral_sqImage`**: $\int_{\{\beta^2 : \beta\in T\}}|t|^{-2}d^2t = 4\int_T|\beta|^{-2}d^2\beta$ (change of variables
  $t = \beta^2$, real Jacobian $|2\beta|^2$), so $\nu = 4\sigma$ gives the same identity
  $\int_{\mathrm{cone}}|Q|_{\mathbb C}^{-2} = \sigma(A)\int_{Q(\mathrm{cone})}|t|_{\mathbb C}^{-1}d^2t$ with $|z|_{\mathbb C} = |z|^2$.

These are the local factors of $\omega^{D^\times}_\infty(\mathrm{cone}) = 8^{r_2}\,\sigma(A)\,\omega_\infty(\operatorname{nrd}\mathrm{cone})$.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ArchPolar

/-! ### Real places -/

section Real

open SphereLeray QuadFormsKB.Siegel

variable (Q : QuadForm ℝ 4)

/-- **The real cone** $\{e^tx : t\in T,\ x\in A\}$ over $A\subseteq S_1$. -/
def coneR (T : Set ℝ) (A : Set (Sph Q 1)) : Set (Fin 4 → ℝ) := pol Q 1 '' (T ×ˢ A)

theorem measurableSet_coneR {T : Set ℝ} (hT : MeasurableSet T) {A : Set (Sph Q 1)} (hA : MeasurableSet A) :
    MeasurableSet (coneR Q T A) :=
  (measurableEmbedding_pol one_ne_zero).measurableSet_image.2 (hT.prod hA)

theorem restrict_image_pol {S : Set (ℝ × Sph Q 1)} (hS : MeasurableSet S) :
    (volume : Measure (Fin 4 → ℝ)).restrict (pol Q 1 '' S) =
      ((Measure.comap (pol Q 1) volume).restrict S).map (pol Q 1) := by
  have he := measurableEmbedding_pol (Q := Q) one_ne_zero
  calc (volume : Measure (Fin 4 → ℝ)).restrict (pol Q 1 '' S)
      = ((volume : Measure (Fin 4 → ℝ)).restrict (range (pol Q 1))).restrict (pol Q 1 '' S) := by
        rw [Measure.restrict_restrict (he.measurableSet_image.2 hS), inter_eq_left.2 (image_subset_range _ _)]
    _ = ((Measure.comap (pol Q 1) volume).map (pol Q 1)).restrict (pol Q 1 '' S) := by rw [he.map_comap]
    _ = ((Measure.comap (pol Q 1) volume).restrict (pol Q 1 ⁻¹' (pol Q 1 '' S))).map (pol Q 1) :=
        he.restrict_map _ _
    _ = _ := by rw [he.injective.preimage_image]

/-- **Polar coordinates on a real cone**: $\int_{\mathrm{cone}}|Q(y)|^{-2}\,dy = \nu(A)\cdot\mathrm{Leb}(T)$. -/
theorem lintegral_coneR {T : Set ℝ} (hT : MeasurableSet T) {A : Set (Sph Q 1)} (hA : MeasurableSet A) :
    ∫⁻ y in coneR Q T A, ENNReal.ofReal ((Q.eval y) ^ 2)⁻¹ = nu Q 1 A * volume T := by
  have he := measurableEmbedding_pol (Q := Q) one_ne_zero
  have hTA := hT.prod hA
  have hsf := sigmaFinite_nu (Q := Q) (c := 1) one_ne_zero
  have hmf : Measurable fun p : ℝ × Sph Q 1 => ENNReal.ofReal ((Q.eval (pol Q 1 p)) ^ 2)⁻¹ :=
    Measurable.ennreal_ofReal ((((continuous_eval_real Q).comp (continuous_pol Q 1)).measurable.pow_const 2).inv)
  rw [coneR, restrict_image_pol Q hTA, he.lintegral_map, comap_pol one_ne_zero (by norm_num),
    ← Measure.prod_restrict, lintegral_prod _ hmf.aemeasurable]
  have hin : ∀ t : ℝ, ∫⁻ x, ENNReal.ofReal ((Q.eval (pol Q 1 (t, x))) ^ 2)⁻¹ ∂(nu Q 1).restrict A =
      ENNReal.ofReal (Real.exp (4 * t))⁻¹ * nu Q 1 A := fun t => by
    have e : ∀ x : Sph Q 1, (Q.eval (pol Q 1 (t, x))) ^ 2 = Real.exp (4 * t) := fun x => by
      rw [eval_pol, mul_one, ← Real.exp_nat_mul]; push_cast; ring_nf
    simp_rw [e]
    rw [lintegral_const, Measure.restrict_apply_univ]
  simp_rw [hin]
  have hm4 : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (4 * x))⁻¹ :=
    Measurable.ennreal_ofReal ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.inv)
  rw [lintegral_mul_const _ hm4, mul_comm]
  congr 1
  rw [rad, restrict_withDensity hT, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (by fun_prop)]
  have h1 : ∀ t : ℝ, (fun t : ℝ => ENNReal.ofReal (Real.exp ((4 : ℕ) * t))) t *
      ENNReal.ofReal (Real.exp (4 * t))⁻¹ = 1 := fun t => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    push_cast
    rw [mul_inv_cancel₀ (Real.exp_pos _).ne', ENNReal.ofReal_one]
  simp_rw [Pi.mul_apply, h1, lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- **The cone over a relatively open $A$ with open radii is open** (polar coordinates are a homeomorphism onto
$\{Q > 0\}$). -/
theorem isOpen_coneR {T : Set ℝ} (hT : IsOpen T) {A : Set (Sph Q 1)} (hA : IsOpen A) : IsOpen (coneR Q T A) := by
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hA
  set g : (Fin 4 → ℝ) → ℝ × (Fin 4 → ℝ) := fun y => (Real.log (Q.eval y) / 2, (Real.sqrt (Q.eval y))⁻¹ • y)
  have hQc := continuous_eval_real Q
  have hg : ContinuousOn g (posSet Q 1) := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine (ContinuousOn.log hQc.continuousOn fun y hy => ?_).div_const 2
      have : 0 < 1 * Q.eval y := hy; linarith
    · refine ContinuousOn.smul (ContinuousOn.inv₀ (Real.continuous_sqrt.comp hQc).continuousOn fun y hy => ?_)
        continuousOn_id
      have : 0 < 1 * Q.eval y := hy
      exact (Real.sqrt_pos.2 (by linarith)).ne'
  have e : coneR Q T (Subtype.val ⁻¹' O) = posSet Q 1 ∩ g ⁻¹' (T ×ˢ O) := by
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      have hQ : Q.eval (pol Q 1 (t, x)) = Real.exp (2 * t) := by rw [eval_pol, mul_one]
      refine ⟨by rw [posSet, mem_ofPred_eq, hQ, one_mul]; exact Real.exp_pos _, ?_, ?_⟩
      · change Real.log (Q.eval (pol Q 1 (t, x))) / 2 ∈ T
        rw [hQ, Real.log_exp, mul_div_cancel_left₀ _ two_ne_zero]; exact ht
      · change (Real.sqrt (Q.eval (pol Q 1 (t, x))))⁻¹ • pol Q 1 (t, x) ∈ O
        rw [hQ, show Real.exp (2 * t) = Real.exp t ^ 2 by rw [← Real.exp_nat_mul]; push_cast; ring_nf,
          Real.sqrt_sq (Real.exp_pos _).le, pol, smul_smul, inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]
        exact hx
    · rintro ⟨hy, ht, hx⟩
      have hy' : 0 < Q.eval y := by have : 0 < 1 * Q.eval y := hy; linarith
      have hs : 0 < Real.sqrt (Q.eval y) := Real.sqrt_pos.2 hy'
      have hxs : Q.eval ((Real.sqrt (Q.eval y))⁻¹ • y) = 1 := by
        rw [eval_smul_real, inv_pow, Real.sq_sqrt hy'.le, inv_mul_cancel₀ hy'.ne']
      refine ⟨(Real.log (Q.eval y) / 2, ⟨_, hxs⟩), ⟨ht, hx⟩, ?_⟩
      rw [pol, smul_smul]
      have : Real.exp (Real.log (Q.eval y) / 2) = Real.sqrt (Q.eval y) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy']; congr 1; ring
      rw [this, mul_inv_cancel₀ hs.ne', one_smul]
  rw [e]
  exact hg.isOpen_inter_preimage (isOpen_posSet Q 1) (hT.prod hO)

/-- **The norm image of a real cone**: $\int_{\{e^{2t} : t\in T\}}dt'/t' = 2\,\mathrm{Leb}(T)$. -/
theorem lintegral_expImage {T : Set ℝ} (hT : MeasurableSet T) :
    ∫⁻ t in (fun s : ℝ => Real.exp (2 * s)) '' T, ENNReal.ofReal t⁻¹ = 2 * volume T := by
  have hd : ∀ x ∈ T, HasDerivWithinAt (fun s : ℝ => Real.exp (2 * s)) (2 * Real.exp (2 * x)) T x := fun x _ => by
    have := ((hasDerivAt_id x).const_mul 2).exp
    simp only [mul_one, id] at this
    rw [mul_comm]; exact this.hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => Real.exp (2 * s)) T := fun x _ y _ h => by
    have := Real.exp_injective h; linarith
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hT hd hinj]
  have h1 : ∀ x : ℝ, ENNReal.ofReal |2 * Real.exp (2 * x)| * ENNReal.ofReal (Real.exp (2 * x))⁻¹ = 2 := fun x => by
    rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_assoc,
      mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one, ENNReal.ofReal_ofNat]
  simp_rw [h1, lintegral_const, Measure.restrict_apply_univ]

end Real

/-! ### Complex places -/

section Complex

open SphereLerayC

variable (Q : QuadForm ℂ 4)

/-- **The complex cone** $\{\beta x : \beta\in T,\ x\in A\}$ over $A\subseteq S_1$ ($T\subseteq\{\operatorname{Re}\beta>0\}$). -/
def coneC (T : Set ℂˣ) (A : Set (SphC Q 1)) : Set (Fin 4 → ℂ) := polC Q 1 '' (T ×ˢ A)

theorem measurableSet_coneC {T : Set ℂˣ} (hT : MeasurableSet T) (hTh : T ⊆ halfU) {A : Set (SphC Q 1)}
    (hA : MeasurableSet A) : MeasurableSet (coneC Q T A) :=
  (hT.prod hA).image_of_continuousOn_injOn (continuous_polC Q 1).continuousOn
    ((injOn_polC_halfU one_ne_zero).mono (prod_mono hTh (subset_univ _)))

theorem mem_coneC_iff {T : Set ℂˣ} (hTh : T ⊆ halfU) {A : Set (SphC Q 1)} {β : ℂˣ} (hβ : β ∈ halfU)
    (x : SphC Q 1) : (β : ℂ) • (x : Fin 4 → ℂ) ∈ coneC Q T A ↔ β ∈ T ∧ x ∈ A := by
  constructor
  · rintro ⟨⟨β', x'⟩, ⟨hβ', hx'⟩, h⟩
    have := injOn_polC_halfU (Q := Q) one_ne_zero (x₁ := (β', x')) (x₂ := (β, x)) ⟨hTh hβ', mem_univ _⟩
      ⟨hβ, mem_univ x⟩ h
    rw [Prod.mk.injEq] at this
    rw [← this.1, ← this.2]; exact ⟨hβ', hx'⟩
  · rintro ⟨hβT, hxA⟩; exact ⟨(β, x), ⟨hβT, hxA⟩, rfl⟩

/-- **The complex cone over a relatively open $A$ with open radii in the half plane is open.** -/
theorem isOpen_coneC {T : Set ℂˣ} (hT : IsOpen T) (hTh : T ⊆ halfU) {A : Set (SphC Q 1)} (hA : IsOpen A) :
    IsOpen (coneC Q T A) := by
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hA
  set r : (Fin 4 → ℂ) → ℂ := fun y => (Q.eval y) ^ (2⁻¹ : ℂ)
  set g : (Fin 4 → ℂ) → ℂ × (Fin 4 → ℂ) := fun y => (r y, (r y)⁻¹ • y)
  set D : Set (Fin 4 → ℂ) := (fun y => Q.eval y) ⁻¹' Complex.slitPlane
  have hQc := continuous_evalC Q
  have hD : IsOpen D := Complex.isOpen_slitPlane.preimage hQc
  have hr : ContinuousOn r D := fun y hy =>
    ((continuousAt_cpow_const hy).comp hQc.continuousAt).continuousWithinAt
  have hTo : IsOpen (Units.val '' T) := (Units.isOpenEmbedding_val (R := ℂ)).isOpenMap _ hT
  have hTne : ∀ z ∈ Units.val '' T, z ≠ 0 := by rintro _ ⟨β, -, rfl⟩; exact β.ne_zero
  set D' : Set (Fin 4 → ℂ) := D ∩ r ⁻¹' (Units.val '' T)
  have hD' : IsOpen D' := hr.isOpen_inter_preimage hD hTo
  have hg : ContinuousOn (fun y => (r y)⁻¹ • y) D' := by
    refine ContinuousOn.smul (ContinuousOn.inv₀ (hr.mono inter_subset_left) fun y hy => hTne _ hy.2) continuousOn_id
  have e : coneC Q T (Subtype.val ⁻¹' O) = D' ∩ (fun y => (r y)⁻¹ • y) ⁻¹' O := by
    ext y
    constructor
    · rintro ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩
      have hβh := hTh hβ
      have hQ : Q.eval (polC Q 1 (β, x)) = (β : ℂ) ^ 2 := by rw [eval_polC, mul_one]
      have hsq : r (polC Q 1 (β, x)) = β := by
        simp only [r]; rw [hQ]; exact Complex.sq_cpow_two_inv hβh
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show Q.eval (polC Q 1 (β, x)) ∈ Complex.slitPlane
        rw [hQ, Complex.mem_slitPlane_iff]
        have hx : 0 < (β : ℂ).re := hβh
        by_cases hy : (β : ℂ).im = 0
        · left; rw [sq, Complex.mul_re, hy]; nlinarith
        · right; rw [sq, Complex.mul_im]
          intro h; apply hy; nlinarith [mul_pos hx hx]
      · rw [mem_preimage, hsq]; exact ⟨β, hβ, rfl⟩
      · rw [mem_preimage, hsq, polC, smul_smul, inv_mul_cancel₀ β.ne_zero, one_smul]; exact hx
    · rintro ⟨⟨hyD, hyT⟩, hx⟩
      obtain ⟨β, hβ, hβr⟩ := hyT
      have hβ0 : (β : ℂ) ≠ 0 := β.ne_zero
      have hQ : Q.eval y = (β : ℂ) ^ 2 := by
        rw [hβr]; simp only [r]
        exact (Complex.cpow_ofNat_inv_pow _ 2).symm
      have hxs : Q.eval ((r y)⁻¹ • y) = 1 := by
        rw [eval_smulC, ← hβr, hQ, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hβ0)]
      refine ⟨(β, ⟨_, hxs⟩), ⟨hβ, hx⟩, ?_⟩
      change (β : ℂ) • ((r y)⁻¹ • y) = y
      rw [← hβr, smul_smul, mul_inv_cancel₀ hβ0, one_smul]
  rw [e]
  exact hg.isOpen_inter_preimage hD' hO

theorem coneC_subset {T : Set ℂˣ} (hTh : T ⊆ halfU) (A : Set (SphC Q 1)) :
    coneC Q T A ⊆ polC Q 1 '' (halfU ×ˢ univ) :=
  image_mono (prod_mono hTh (subset_univ _))

/-- **Polar coordinates on a complex cone**: $\int_{\mathrm{cone}}|Q(y)|^{-4}\,d^8y = \nu(A)\int_T|\beta|^{-2}d^2\beta$. -/
theorem lintegral_coneC {T : Set ℂˣ} (hT : MeasurableSet T) (hTh : T ⊆ halfU) {A : Set (SphC Q 1)}
    (hA : MeasurableSet A) :
    ∫⁻ y in coneC Q T A, ENNReal.ofReal (‖Q.eval y‖ ^ 4)⁻¹ =
      nuC Q 1 A * ∫⁻ β in T, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ ∂volU := by
  set g : (Fin 4 → ℂ) → ℝ≥0∞ := fun y => ENNReal.ofReal (‖Q.eval y‖ ^ 4)⁻¹
  have hg : Measurable g := (Measurable.ennreal_ofReal (((continuous_evalC Q).norm.pow 4).measurable.inv))
  have hcm := measurableSet_coneC Q hT hTh hA
  have hP : MeasurableSet (polC Q 1 '' (halfU ×ˢ univ)) :=
    (isOpen_halfU.measurableSet.prod MeasurableSet.univ).image_of_continuousOn_injOn
      (continuous_polC Q 1).continuousOn (injOn_polC_halfU one_ne_zero)
  have h1 : ∫⁻ y in coneC Q T A, g y = ∫⁻ y in polC Q 1 '' (halfU ×ˢ univ), (coneC Q T A).indicator g y := by
    rw [setLIntegral_indicator hcm, inter_eq_left.2 (coneC_subset Q hTh A)]
  rw [h1, lintegral_polC_half one_ne_zero (by norm_num) (hg.indicator hcm)]
  have hin : ∀ β ∈ halfU, ∫⁻ x, (coneC Q T A).indicator g ((β : ℂ) • (x : Fin 4 → ℂ)) ∂nuC Q 1 =
      T.indicator (fun β : ℂˣ => ENNReal.ofReal (‖(β : ℂ)‖ ^ 8)⁻¹ * nuC Q 1 A) β := fun β hβ => by
    have e : ∀ x : SphC Q 1, (coneC Q T A).indicator g ((β : ℂ) • (x : Fin 4 → ℂ)) =
        T.indicator (fun β : ℂˣ => ENNReal.ofReal (‖(β : ℂ)‖ ^ 8)⁻¹) β * A.indicator 1 x := fun x => by
      by_cases hβT : β ∈ T
      · by_cases hxA : x ∈ A
        · rw [indicator_of_mem ((mem_coneC_iff Q hTh hβ x).2 ⟨hβT, hxA⟩), indicator_of_mem hβT,
            indicator_of_mem hxA, Pi.one_apply, mul_one]
          simp only [g]
          rw [eval_smulC, show Q.eval (x : Fin 4 → ℂ) = 1 from x.2, mul_one, norm_pow, ← pow_mul]
        · rw [indicator_of_notMem (fun h => hxA ((mem_coneC_iff Q hTh hβ x).1 h).2),
            indicator_of_notMem hxA, mul_zero]
      · rw [indicator_of_notMem (fun h => hβT ((mem_coneC_iff Q hTh hβ x).1 h).1),
          indicator_of_notMem hβT, zero_mul]
    simp_rw [e]
    rw [lintegral_const_mul _ (measurable_one.indicator hA), lintegral_indicator hA, Pi.one_def,
      setLIntegral_const, one_mul]
    by_cases hβT : β ∈ T
    · rw [indicator_of_mem hβT, indicator_of_mem hβT]
    · rw [indicator_of_notMem hβT, indicator_of_notMem hβT, zero_mul]
  rw [setLIntegral_congr_fun isOpen_halfU.measurableSet hin, setLIntegral_indicator hT, inter_eq_left.2 hTh,
    lamU, setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_wt _) _ hT]
  · have hmeas : Measurable fun β : ℂˣ => ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ :=
      Measurable.ennreal_ofReal (((continuous_norm.comp Units.continuous_val).measurable.pow_const 2).inv)
    rw [← lintegral_const_mul _ hmeas]
    refine setLIntegral_congr_fun hT fun β _ => ?_
    simp only [Pi.mul_apply]
    have hb : 0 < ‖(β : ℂ)‖ := norm_pos_iff.2 β.ne_zero
    have key : wt (2 * ((4 : ℕ) : ℤ) - 2) β * ENNReal.ofReal (‖(β : ℂ)‖ ^ 8)⁻¹ =
        ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ := by
      rw [wt, show (2 * ((4 : ℕ) : ℤ) - 2) = 6 by norm_num,
        show (((‖(β : ℂ)‖₊ ^ (6 : ℤ) : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal (‖(β : ℂ)‖ ^ 6) by
          rw [← ENNReal.ofReal_coe_nnreal]; congr 1,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [← mul_assoc, key, mul_comm]
  · exact (Measurable.ennreal_ofReal ((continuous_norm.comp Units.continuous_val).measurable.pow_const 8).inv).mul_const _

/-- `volU`-integrals over $T$ are Lebesgue integrals over the image of $T$ in $\mathbb C$. -/
theorem setLIntegral_volU {T : Set ℂˣ} (hT : MeasurableSet T) (g : ℂ → ℝ≥0∞) :
    ∫⁻ β in T, g (β : ℂ) ∂volU = ∫⁻ z in Units.val '' T, g z := by
  have he := measurableEmbedding_val
  have hTm : MeasurableSet (Units.val '' T) := he.measurableSet_image.2 hT
  calc ∫⁻ β in T, g (β : ℂ) ∂volU
      = ∫⁻ β, g (β : ℂ) ∂((volume.restrict (Units.val '' T)).comap Units.val) := by
        rw [volU, he.restrict_comap]
    _ = ∫⁻ z, g z ∂(((volume.restrict (Units.val '' T)).comap Units.val).map Units.val) :=
        (he.lintegral_map _).symm
    _ = _ := by
        rw [he.map_comap, Measure.restrict_restrict he.measurableSet_range, inter_eq_right.2 (image_subset_range _ _)]

theorem det_mulLeft_complex (c : ℂ) :
    LinearMap.det (LinearMap.mulLeft ℝ c) = Complex.normSq c := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
  rfl

/-- **The norm image of a complex cone**: $\int_{\{\beta^2 : \beta\in T\}}|t|^{-2}d^2t = 4\int_T|\beta|^{-2}d^2\beta$. -/
theorem lintegral_sqImage {T : Set ℂˣ} (hT : MeasurableSet T) (hTh : T ⊆ halfU) :
    ∫⁻ t in (fun z : ℂ => z ^ 2) '' (Units.val '' T), ENNReal.ofReal (‖t‖ ^ 2)⁻¹ =
      4 * ∫⁻ β in T, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ ∂volU := by
  have hTm : MeasurableSet (Units.val '' T) := measurableEmbedding_val.measurableSet_image.2 hT
  set f' : ℂ → ℂ →L[ℝ] ℂ := fun z => (ContinuousLinearMap.mul ℝ ℂ) (2 * z)
  have hd : ∀ z ∈ Units.val '' T, HasFDerivWithinAt (fun z : ℂ => z ^ 2) (f' z) (Units.val '' T) z := by
    intro z _
    have h := (hasDerivAt_pow 2 z).hasFDerivAt.restrictScalars ℝ
    refine (h.congr_fderiv ?_).hasFDerivWithinAt
    ext1 w
    simp [f', mul_comm]
  have hinj : InjOn (fun z : ℂ => z ^ 2) (Units.val '' T) := by
    rintro _ ⟨β, hβ, rfl⟩ _ ⟨γ, hγ, rfl⟩ h
    have hβ' := hTh hβ; have hγ' := hTh hγ
    simp only [halfU, mem_ofPred_eq] at hβ' hγ'
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
    · exact h
    · exfalso; rw [h, Complex.neg_re] at hβ'; linarith
  have hmeas : Measurable fun β : ℂˣ => ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ :=
    Measurable.ennreal_ofReal (((continuous_norm.comp Units.continuous_val).measurable.pow_const 2).inv)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hTm hd hinj,
    ← setLIntegral_volU hT (fun z => ENNReal.ofReal |(f' z).det| * ENNReal.ofReal (‖z ^ 2‖ ^ 2)⁻¹),
    ← lintegral_const_mul _ hmeas]
  refine setLIntegral_congr_fun hT fun β _ => ?_
  have hdet : (f' (β : ℂ)).det = Complex.normSq (2 * β) := by
    rw [ContinuousLinearMap.det, ← det_mulLeft_complex]
    rfl
  have hb : 0 < ‖(β : ℂ)‖ := norm_pos_iff.2 β.ne_zero
  rw [hdet, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, norm_pow, norm_mul,
    show ‖(2 : ℂ)‖ = 2 by norm_num, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  field_simp
  ring

end Complex

end QuadFormsKB.Tamagawa.Measure.ArchPolar
