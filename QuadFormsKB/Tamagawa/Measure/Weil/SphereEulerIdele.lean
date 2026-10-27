import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerLocalReal
import QuadFormsKB.Tamagawa.Measure.Weil.LintegralPiProd

/-!
# The multiplicative transform of the Gaussian test function

$F$ totally real, $\Phi = G\otimes\mathbf 1_{\hat{\mathcal O}^n}$ = `gaussTest`, $a = n + 2s$. The idele integral
$M_s\Phi(y) = \int_{\mathbb A^\times}\|z\|^{a}\Phi(zy)\,d^\times z$ (`mellinPhi`) splits into an archimedean and a finite part
(**`mellinPhi_gaussTest`**):
$$M_s\Phi(y) = |d_F|^{-1/2}\prod_w M_a(y_w)\cdot\sum_{e}\prod_vq_v^{-e_va}\,\mathbf 1\big[|y_{v,i}|_v\le q_v^{e_v}\ \forall v,i\big],$$
the sum over the finitely supported $e : \{\text{finite places}\}\to\mathbb Z$ (the ideals $\mathfrak b = \prod_v\mathfrak p_v^{e_v}$ of
$z_f$), $M_a$ = `archMellin`. *Proof.* `lintegral_tamIdeles_ideal` (the fibres of $z\mapsto\mathfrak a(z_f)$ are cosets of
$\hat{\mathcal O}^\times$ of mass $|d_F|^{-1/2}$), with $\|z\| = N(z_\infty)/N\mathfrak a(z_f)$ and
$z_fy_f\in\hat{\mathcal O}^n\iff|y_{v,i}|_v\le q_v^{\operatorname{ord}_vz_v}$; the archimedean integral factors over the real places.
-/

open MeasureTheory Set Filter WithZero
open scoped ENNReal nonZeroDivisors Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "FI" => IdeleClass.FracIdeal F

/-! ### Exponent vectors -/

/-- The exponent vector $(\operatorname{ord}_vz_v)_v$ of a finite idele. -/
def ordFin (z : AFˣ) : HeightOneSpectrum (𝓞 F) →₀ ℤ := Finsupp.ofSupportFinite (ordAt z) (finite_ordAt z)

theorem ordFin_apply (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : ordFin z v = ordAt z v := rfl

theorem finite_count (𝔟 : FI) :
    {v : HeightOneSpectrum (𝓞 F) | FractionalIdeal.count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0}.Finite :=
  FractionalIdeal.finite_factors (K := F) (𝔟 : FractionalIdeal (𝓞 F)⁰ F)

/-- The exponent vector $(\operatorname{ord}_v\mathfrak b)_v$ of a fractional ideal. -/
def countFin (𝔟 : FI) : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (finite_count 𝔟)

theorem countFin_apply (𝔟 : FI) (v : HeightOneSpectrum (𝓞 F)) :
    countFin 𝔟 v = FractionalIdeal.count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := rfl

theorem countFin_ideleIdeal (z : AFˣ) : countFin (ideleIdeal F z) = ordFin z :=
  Finsupp.ext fun v => by rw [countFin_apply, ordFin_apply]; exact count_ideleIdeal z v

theorem countFin_bijective : Function.Bijective (countFin (F := F)) := by
  refine ⟨fun I J h => fracIdeal_ext_count fun v => by
    have := DFunLike.congr_fun h v
    rwa [countFin_apply, countFin_apply] at this, fun e => ⟨primeProd e, ?_⟩⟩
  have he : {v | e v ≠ 0}.Finite := by
    exact e.support.finite_toSet.subset fun v hv => by simpa using hv
  exact Finsupp.ext fun v => by rw [countFin_apply]; exact count_primeProd e he v

/-- **The pushforward of `tamIdeles` to (archimedean part, exponent vector)**: for $h\ge0$ on $F_\infty$ and any
$H\ge0$ on exponent vectors,
$\int h(z_\infty)H(\operatorname{ord}z_f)\,d^\times z = |d_F|^{-1/2}2^{r_2}\int h(x)\,dx/N(x)\cdot\sum_eH(e)$. -/
theorem lintegral_tamIdeles_ordFin (h : mixedSpace F → ℝ≥0∞) (hh : Measurable h)
    (H : (HeightOneSpectrum (𝓞 F) →₀ ℤ) → ℝ≥0∞) :
    ∫⁻ g, h (infPart g) * H (ordFin (finPart g)) ∂tamIdeles F =
      ENNReal.ofReal (IdeleClass.ideleConst F) * (∫⁻ x, h x * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹) *
        ∑' e, H e := by
  have h1 := lintegral_tamIdeles_ideal (fun x 𝔟 => h x * H (countFin 𝔟)) (fun 𝔟 => hh.mul_const _)
  simp only [countFin_ideleIdeal] at h1
  rw [h1, IdeleClass.ideleLIntegral, mul_assoc]
  congr 1
  rw [← (Equiv.ofBijective _ countFin_bijective).tsum_eq, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun 𝔟 => ?_
  rw [Equiv.ofBijective_apply]
  rw [show (∫⁻ x, h x * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹) * H (countFin 𝔟) =
      ∫⁻ x, h x * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ * H (countFin 𝔟) from
    (lintegral_mul_const _ (hh.mul (IdeleClass.measurable_invNorm F))).symm]
  refine lintegral_congr fun x => ?_
  ring

/-! ### The finite weight -/

variable {n : ℕ}

/-- **The finite weight of an exponent vector** $e$ at $y$: $\prod_vq_v^{-e_va}$ if $|y_{v,i}|_v\le q_v^{e_v}$ for all $v, i$
(i.e. $z_fy_f\in\hat{\mathcal O}^n$ for $\operatorname{ord}z_f = e$), else $0$. -/
def finWeight (a : ℝ) (y : AdeleSpace F (Fin n)) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ v ∈ e.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(e v : ℝ) * a)) *
    {y : AdeleSpace F (Fin n) | ∀ v i, Valued.v (adV y v i) ≤ exp (e v)}.indicator 1 y

theorem idealNorm_ideleIdeal_rpow (z : AFˣ) (a : ℝ) :
    (IdeleClass.idealNorm F (ideleIdeal F z)) ^ (-a) =
      ∏ v ∈ (ordFin z).support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ordFin z v : ℝ) * a) := by
  have h1 : IdeleClass.idealNorm F (ideleIdeal F z) =
      ∏ v ∈ (ordFin z).support, (Ideal.absNorm v.asIdeal : ℝ) ^ ordFin z v := by
    show IdeleClass.idealNorm F (primeProd (ordAt z)) = _
    rw [idealNorm_primeProd _ (finite_ordAt z)]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    simp only [Function.mem_mulSupport] at hv
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, ordFin_apply]
    intro h0; exact hv (by rw [h0, zpow_zero])
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) < Ideal.absNorm v.asIdeal := fun v =>
    zero_lt_one.trans (one_lt_absNorm v)
  rw [h1, ← Real.finsetProd_rpow _ _ fun v _ => (zpow_pos (hq v) _).le]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Real.rpow_intCast, ← Real.rpow_mul (hq v).le]
  ring_nf

/-- **The integrand of $M_s\Phi$ in (archimedean part, exponent vector) form.** -/
theorem zetaWeight_mul_gaussTest (s : ℝ) (y : AdeleSpace F (Fin n)) (z : (Adeles F)ˣ) :
    zetaWeight s n z * gaussTest F n (z • y) =
      (ENNReal.ofReal (mixedEmbedding.norm (infPart z : mixedSpace F) ^ ((n : ℝ) + 2 * s)) *
        ENNReal.ofReal (gV fun i => (infPart z : mixedSpace F) * (y i).1)) *
      finWeight ((n : ℝ) + 2 * s) y (ordFin (finPart z)) := by
  set a : ℝ := (n : ℝ) + 2 * s
  set x : mixedSpace F := (infPart z : mixedSpace F)
  have hI := IdeleClass.idealNorm_pos F (ideleIdeal F (finPart z))
  have hN := mixedEmbedding.norm_nonneg x
  have hw : zetaWeight s n z = ENNReal.ofReal (mixedEmbedding.norm x ^ a) *
      ENNReal.ofReal (∏ v ∈ (ordFin (finPart z)).support,
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ordFin (finPart z) v : ℝ) * a)) := by
    rw [zetaWeight, ideleNorm_eq_ideleClass, IdeleClass.ideleNorm, ← idealNorm_ideleIdeal_rpow,
      Real.div_rpow hN hI.le, Real.rpow_neg hI.le, div_eq_mul_inv,
      ENNReal.ofReal_mul (Real.rpow_nonneg hN _)]
  have hmem : (fun i => ((z • y) i).2) ∈ (OHatVec : Set (Fin n → AF)) ↔
      y ∈ {y : AdeleSpace F (Fin n) | ∀ v i, Valued.v (adV y v i) ≤ exp (ordFin (finPart z) v)} := by
    rw [show (fun i => ((z • y) i).2) = fun i => ((z • y) i).2 from rfl, mem_OHatVec_iff]
    simp only [mem_ofPred_eq, LocalZeta.latL]
    refine forall_congr' fun v => forall_congr' fun i => ?_
    have e : adV (z • y) v i = ((finPart z : AF) v) * adV y v i := rfl
    rw [e, map_mul, valued_eq_exp_ordAt, ordFin_apply]
    constructor
    · intro h
      have h2 := mul_le_mul_right h (exp (ordAt (finPart z) v))
      rwa [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul, mul_one] at h2
    · intro h
      have h2 := mul_le_mul_right h (exp (-ordAt (finPart z) v))
      rwa [← exp_add, neg_add_cancel, exp_zero] at h2
  have hg : (gV fun i => ((z • y) i).1) = gV fun i => x * (y i).1 := rfl
  rw [hw, gaussTest, finWeight, hg]
  by_cases h : y ∈ {y : AdeleSpace F (Fin n) | ∀ v i, Valued.v (adV y v i) ≤ exp (ordFin (finPart z) v)}
  · rw [indicator_of_mem (hmem.mpr h), indicator_of_mem h]
    simp only [Pi.one_apply, one_mul, mul_one]
    ring
  · rw [indicator_of_notMem (fun h' => h (hmem.mp h')), indicator_of_notMem h]
    simp

/-! ### The archimedean integral -/

/-- $x\mapsto G(xy)$ is measurable. -/
theorem measurable_gV_mul (y : AdeleSpace F (Fin n)) :
    Measurable fun x : mixedSpace F => gV fun i => x * (y i).1 := by
  unfold gV gR
  exact (continuous_finsetProd _ fun i _ => Real.continuous_exp.comp (continuous_const.mul
    (Continuous.add (continuous_finsetSum _ fun w _ => ((continuous_apply w).comp
      (continuous_fst.mul continuous_const)).pow 2)
      (continuous_const.mul (continuous_finsetSum _ fun w _ =>
        (continuous_norm.comp ((continuous_apply w).comp (continuous_snd.mul continuous_const))).pow 2))))).measurable

/-- For totally real $F$, $N(x) = \prod_w|x_w|$. -/
theorem norm_eq_prod_abs [IsEmpty {w : InfinitePlace F // w.IsComplex}] (x : mixedSpace F) :
    mixedEmbedding.norm x = ∏ w : {w : InfinitePlace F // w.IsReal}, |x.1 w| := by
  rw [mixedEmbedding.norm_apply]
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w =>
    w.isReal_or_isComplex.resolve_right fun h => IsEmpty.false (⟨w, h⟩ : {w : InfinitePlace F // w.IsComplex})
  rw [Finset.prod_subtype Finset.univ (p := fun w : InfinitePlace F => w.IsReal) (by simp [hr])
    (fun w => normAtPlace w x ^ w.mult)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs, InfinitePlace.mult]
  simp [w.2]

/-- **The archimedean integral factors over the real places** (totally real $F$):
$\int_{F_\infty}N(x)^a\,G(xy)\,dx/N(x) = \prod_wM_a(y_w)$. -/
theorem lintegral_mixedSpace_gauss [IsEmpty {w : InfinitePlace F // w.IsComplex}] (a : ℝ)
    (y : AdeleSpace F (Fin n)) :
    ∫⁻ x : mixedSpace F, ENNReal.ofReal (mixedEmbedding.norm x ^ a) *
        ENNReal.ofReal (gV fun i => x * (y i).1) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      ∏ w, archMellin a (adR y w) := by
  have hg : ∀ x : mixedSpace F, ENNReal.ofReal (gV fun i => x * (y i).1) =
      ∏ w : {w : InfinitePlace F // w.IsReal}, gaussRe (x.1 w • adR y w) := by
    intro x
    simp only [gaussRe, gV, gR]
    simp only [Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.sum_empty, mul_zero,
      add_zero]
    rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_sum]
    congr 2
    simp only [adR, Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Pi.mul_apply, mul_pow, ← Finset.mul_sum, neg_mul,
      Finset.sum_neg_distrib]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have hf : ∀ x : mixedSpace F, ENNReal.ofReal (mixedEmbedding.norm x ^ a) *
        ENNReal.ofReal (gV fun i => x * (y i).1) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      ∏ w : {w : InfinitePlace F // w.IsReal},
        (ENNReal.ofReal (|x.1 w| ^ a * |x.1 w|⁻¹) * gaussRe (x.1 w • adR y w)) := by
    intro x
    rw [hg, Finset.prod_mul_distrib (f := fun w : {w : InfinitePlace F // w.IsReal} =>
        ENNReal.ofReal (|x.1 w| ^ a * |x.1 w|⁻¹)),
      ← ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity), Finset.prod_mul_distrib,
      norm_eq_prod_abs, ← Real.finsetProd_rpow _ _ fun w _ => abs_nonneg _,
      Finset.prod_inv_distrib, ENNReal.ofReal_mul (by positivity)]
    ring
  simp_rw [hf]
  rw [show (volume : Measure (mixedSpace F)) = (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)).prod
    (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)) from Measure.volume_eq_prod _ _]
  rw [lintegral_prod _ (by
      refine Measurable.aemeasurable ?_
      exact Finset.measurable_prod _ fun w _ => (ENNReal.measurable_ofReal.comp
        ((((measurable_pi_apply w).comp measurable_fst).abs.pow_const a).mul
          (((measurable_pi_apply w).comp measurable_fst).abs.inv))).mul
        (measurable_gaussRe.comp ((((measurable_pi_apply w).comp measurable_fst)).smul_const _)))]
  have h1 : (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)) univ = 1 := by
    rw [volume_pi, Measure.pi_univ]; simp
  simp only [lintegral_const, h1, mul_one]
  have := lintegral_pi_prod (fun _ => (volume : Measure ℝ)) (fun w t => ENNReal.ofReal (|t| ^ a * |t|⁻¹) *
    gaussRe (t • adR y w)) fun w => by
    exact (ENNReal.measurable_ofReal.comp ((measurable_id.abs.pow_const a).mul measurable_id.abs.inv)).mul
      (measurable_gaussRe.comp (measurable_id.smul_const _))
  exact this

/-- **The multiplicative transform of the Gaussian test function** (totally real $F$):
$M_s\Phi(y) = |d_F|^{-1/2}\prod_wM_a(y_w)\sum_e\mathrm{finWeight}_a(y, e)$, $a = n+2s$. -/
theorem mellinPhi_gaussTest [IsEmpty {w : InfinitePlace F // w.IsComplex}] (s : ℝ) (y : AdeleSpace F (Fin n)) :
    mellinPhi (gaussTest F n) s y =
      ENNReal.ofReal (IdeleClass.ideleConst F) * (∏ w, archMellin ((n : ℝ) + 2 * s) (adR y w)) *
        ∑' e, finWeight ((n : ℝ) + 2 * s) y e := by
  have hh : Measurable fun x : mixedSpace F => ENNReal.ofReal (mixedEmbedding.norm x ^ ((n : ℝ) + 2 * s)) *
      ENNReal.ofReal (gV fun i => x * (y i).1) := by
    exact (ENNReal.measurable_ofReal.comp ((mixedEmbedding.continuous_norm F).measurable.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_gV_mul y))
  rw [mellinPhi]
  simp_rw [zetaWeight_mul_gaussTest]
  rw [lintegral_tamIdeles_ordFin _ hh, lintegral_mixedSpace_gauss]

end QuadFormsKB.Tamagawa.Measure.Weil

end
