import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerIdele
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerLocalComplex

/-!
# The multiplicative transform of the Gaussian test function over every number field

$F$ any number field, $\Phi = G\otimes\mathbf 1_{\hat{\mathcal O}^n}$ = `gaussTest`, $a = n + 2s$. the
`mellinPhi_gaussTest` is stated for totally real $F$. With the complex places (**`mellinPhi_gaussTestNF`**):
$$M_s\Phi(y) = |d_F|^{-1/2}2^{r_2}\prod_{w\ \mathrm{real}}M_a(y_w)\prod_{w\ \mathrm{complex}}M^{\mathbb C}_a(y_w)\cdot
  \sum_e\mathrm{finWeight}_a(y, e),$$
$M_a$ = `archMellin`, $M^{\mathbb C}_a$ = `archMellinC`. *Proof.* As `mellinPhi_gaussTest`: `lintegral_tamIdeles_ordFin`,
then the archimedean integral over $F_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$ factors over all infinite places
(**`lintegral_mixedSpace_gaussNF`**), the Gaussian being $\prod_{w\ \mathrm{real}}e^{-\pi|y_w|^2}
\prod_{w\ \mathrm{complex}}e^{-2\pi|y_w|^2}$ (**`ofReal_gV_fstNF`**) and $N(x) = \prod_{w\ \mathrm{real}}|x_w|
\prod_{w\ \mathrm{complex}}|x_w|^2$.
-/

open MeasureTheory Set Filter WithZero
open scoped ENNReal nonZeroDivisors Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **The Gaussian `gV` factors over the infinite places**, for any family `z` of vectors of `F_∞`. -/
theorem ofReal_gV_eq_prod (z : Fin n → mixedSpace F) :
    ENNReal.ofReal (gV z) =
      (∏ w : {w : InfinitePlace F // w.IsReal}, gaussRe (fun i => (z i).1 w)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, ENNReal.ofReal (gaussFnC (fun i => (z i).2 w)) := by
  have hR : ∏ w : {w : InfinitePlace F // w.IsReal}, gaussRe (fun i => (z i).1 w) =
      ENNReal.ofReal (Real.exp (-Real.pi * ∑ w : {w : InfinitePlace F // w.IsReal}, ∑ i, ((z i).1 w) ^ 2)) := by
    simp only [gaussRe]
    rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum]
  have hC : ∏ w : {w : InfinitePlace F // w.IsComplex}, ENNReal.ofReal (gaussFnC (fun i => (z i).2 w)) =
      ENNReal.ofReal (Real.exp (-(2 * Real.pi) *
        ∑ w : {w : InfinitePlace F // w.IsComplex}, ∑ i, ‖(z i).2 w‖ ^ 2)) := by
    simp only [gaussFnC]
    rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum]
  rw [hR, hC, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, gV_eq_exp, qV]
  congr 2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm (f := fun i w => ((z i).1 w) ^ 2),
    Finset.sum_comm (f := fun i w => ‖(z i).2 w‖ ^ 2)]
  ring

/-- $N(x) = \prod_{w\ \mathrm{real}}|x_w|\prod_{w\ \mathrm{complex}}|x_w|^2$ on $F_\infty$. -/
theorem norm_eq_prod_placesNF (x : mixedSpace F) :
    mixedEmbedding.norm x = (∏ w : {w : InfinitePlace F // w.IsReal}, |x.1 w|) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ ^ 2 := by
  rw [mixedEmbedding.norm_apply,
    ← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs, InfinitePlace.mult]
    simp [w.2]
  · refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex) _ _ (fun w => ?_)
    have hw : w.1.IsComplex := not_isReal_iff_isComplex.mp w.2
    rw [normAtPlace_apply_of_isComplex hw, InfinitePlace.mult]
    simp [w.2]
    rfl

/-- **The archimedean Gaussian factors over all infinite places**:
$G(y_\infty) = \prod_{w\ \mathrm{real}}e^{-\pi|y_w|^2}\prod_{w\ \mathrm{complex}}e^{-2\pi|y_w|^2}$. -/
theorem ofReal_gV_fstNF (y : AdeleSpace F (Fin n)) :
    ENNReal.ofReal (gV fun i => (y i).1) =
      (∏ w, gaussRe (adR y w)) * ∏ w, ENNReal.ofReal (gaussFnC (adC y w)) :=
  ofReal_gV_eq_prod _

/-- **The archimedean integral factors over all infinite places** (every number field):
$\int_{F_\infty}N(x)^a\,G(xy)\,dx/N(x) = \prod_{w\ \mathrm{real}}M_a(y_w)\prod_{w\ \mathrm{complex}}M^{\mathbb C}_a(y_w)$. -/
theorem lintegral_mixedSpace_gaussNF (a : ℝ) (y : AdeleSpace F (Fin n)) :
    ∫⁻ x : mixedSpace F, ENNReal.ofReal (mixedEmbedding.norm x ^ a) *
        ENNReal.ofReal (gV fun i => x * (y i).1) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      (∏ w, archMellin a (adR y w)) * ∏ w, archMellinC a (adC y w) := by
  set fR : {w : InfinitePlace F // w.IsReal} → ℝ → ℝ≥0∞ := fun w t =>
    ENNReal.ofReal (|t| ^ a * |t|⁻¹) * gaussRe (t • adR y w) with hfR
  set fC : {w : InfinitePlace F // w.IsComplex} → ℂ → ℝ≥0∞ := fun w t =>
    ENNReal.ofReal ((‖t‖ ^ 2) ^ a * (‖t‖ ^ 2)⁻¹) * ENNReal.ofReal (gaussFnC (t • adC y w)) with hfC
  have hmR : ∀ w, Measurable (fR w) := fun w =>
    Measurable.mul (ENNReal.measurable_ofReal.comp
      ((measurable_id.abs.pow_const a).mul measurable_id.abs.inv))
      (measurable_gaussRe.comp (measurable_id.smul_const _))
  have hmC : ∀ w, Measurable (fC w) := fun w =>
    Measurable.mul (ENNReal.measurable_ofReal.comp
      (((measurable_id.norm.pow_const 2).pow_const a).mul (measurable_id.norm.pow_const 2).inv))
      (ENNReal.measurable_ofReal.comp (measurable_gaussFnC.comp (measurable_id.smul_const _)))
  have hf : ∀ x : mixedSpace F, ENNReal.ofReal (mixedEmbedding.norm x ^ a) *
        ENNReal.ofReal (gV fun i => x * (y i).1) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      (∏ w, fR w (x.1 w)) * ∏ w, fC w (x.2 w) := by
    intro x
    have hr : mixedEmbedding.norm x ^ a * (mixedEmbedding.norm x)⁻¹ =
        (∏ w : {w : InfinitePlace F // w.IsReal}, (|x.1 w| ^ a * |x.1 w|⁻¹)) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, ((‖x.2 w‖ ^ 2) ^ a * (‖x.2 w‖ ^ 2)⁻¹) := by
      rw [norm_eq_prod_placesNF, Real.mul_rpow (by positivity) (by positivity), mul_inv,
        Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Real.finsetProd_rpow _ _ (fun w _ => abs_nonneg _), Real.finsetProd_rpow _ _ (fun w _ => by positivity),
        Finset.prod_inv_distrib, Finset.prod_inv_distrib]
      ring
    have hN : ENNReal.ofReal (mixedEmbedding.norm x ^ a) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
        (∏ w : {w : InfinitePlace F // w.IsReal}, ENNReal.ofReal (|x.1 w| ^ a * |x.1 w|⁻¹)) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, ENNReal.ofReal ((‖x.2 w‖ ^ 2) ^ a * (‖x.2 w‖ ^ 2)⁻¹) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _), hr,
        ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => by positivity),
        ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity),
        ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
    have h1 : ∀ w : {w : InfinitePlace F // w.IsReal}, (fun i => (x * (y i).1).1 w) = x.1 w • adR y w := by
      intro w; funext i; simp [adR]
    have h2 : ∀ w : {w : InfinitePlace F // w.IsComplex}, (fun i => (x * (y i).1).2 w) = x.2 w • adC y w := by
      intro w; funext i; simp [adC]
    rw [ofReal_gV_eq_prod]
    simp only [h1, h2, hfR, hfC, Finset.prod_mul_distrib]
    calc _ = (ENNReal.ofReal (mixedEmbedding.norm x ^ a) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹) *
          ((∏ w : {w : InfinitePlace F // w.IsReal}, gaussRe (x.1 w • adR y w)) *
            ∏ w : {w : InfinitePlace F // w.IsComplex}, ENNReal.ofReal (gaussFnC (x.2 w • adC y w))) := by ring
      _ = _ := by rw [hN]; ring
  simp_rw [hf]
  rw [show (volume : Measure (mixedSpace F)) = (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)).prod
    (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)) from Measure.volume_eq_prod _ _]
  rw [lintegral_prod_mul (f := fun u : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ w, fR w (u w))
    (g := fun u : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w, fC w (u w))
    (Finset.measurable_prod _ fun w _ => (hmR w).comp (measurable_pi_apply w)).aemeasurable
    (Finset.measurable_prod _ fun w _ => (hmC w).comp (measurable_pi_apply w)).aemeasurable,
    volume_pi, volume_pi, lintegral_pi_prod _ _ hmR, lintegral_pi_prod _ _ hmC]
  rfl

/-- **The multiplicative transform of the Gaussian test function** (every number field):
$M_s\Phi(y) = |d_F|^{-1/2}2^{r_2}\prod_{w\ \mathrm{real}}M_a(y_w)\prod_{w\ \mathrm{complex}}M^{\mathbb C}_a(y_w)
\sum_e\mathrm{finWeight}_a(y, e)$, $a = n+2s$. -/
theorem mellinPhi_gaussTestNF (s : ℝ) (y : AdeleSpace F (Fin n)) :
    mellinPhi (gaussTest F n) s y =
      ENNReal.ofReal (IdeleClass.ideleConst F) * ((∏ w, archMellin ((n : ℝ) + 2 * s) (adR y w)) *
        ∏ w, archMellinC ((n : ℝ) + 2 * s) (adC y w)) * ∑' e, finWeight ((n : ℝ) + 2 * s) y e := by
  have hh : Measurable fun x : mixedSpace F => ENNReal.ofReal (mixedEmbedding.norm x ^ ((n : ℝ) + 2 * s)) *
      ENNReal.ofReal (gV fun i => x * (y i).1) := by
    exact (ENNReal.measurable_ofReal.comp ((mixedEmbedding.continuous_norm F).measurable.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_gV_mul y))
  rw [mellinPhi]
  simp_rw [zetaWeight_mul_gaussTest]
  rw [lintegral_tamIdeles_ordFin _ hh, lintegral_mixedSpace_gaussNF]

end QuadFormsKB.Tamagawa.Measure.Weil

end
