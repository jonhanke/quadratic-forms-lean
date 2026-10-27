import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerLocalReal
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropicGauss

/-!
# The standard Gaussian as archimedean data

$G(x) = e^{-\pi\sum_ix_i^2}$ on $\mathbb R^n$ (`gaussFn`), $F$ totally real:
* **`isArchTestFn_gaussFn`**: $G$ and $|Q_w|G$ are integrable at every real place;
* **`integral_gaussFn`**: $\int_{\mathbb R^n}G = 1$;
* **`phiIntegralNF_gaussFn`**: `phiIntegralNF` of $G$ (no complex places) is $|d_F|^{-n/2}$;
* **`toReal_muFinVec_OHatVec`**: $\mu_f(\hat{\mathcal O}^n) = |d_F|^{-n/2}$.
Hence $\hat\Phi(0) = \mu_f(\hat{\mathcal O}^n) = 1\cdot$ `phiIntegralNF` $G$ (**`muFinVec_eq_phiIntegralNF_gaussFn`**), the
normalization `b_eq` of Weil's induction step with $\kappa = 1$.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace QuadFormsKB.SphericalZeta QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta
  QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- $G$ is a product of one-dimensional Gaussians. -/
theorem gaussFn_eq_prod {n : ℕ} (x : Fin n → ℝ) : gaussFn x = ∏ i, Real.exp (-Real.pi * x i ^ 2) := by
  rw [gaussFn, ← Real.exp_sum, Finset.mul_sum]

/-- $G$ is integrable. -/
theorem integrable_gaussFn {n : ℕ} : Integrable (gaussFn : (Fin n → ℝ) → ℝ) := by
  have hg : Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (-Real.pi * x i ^ 2))
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
    Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq Real.pi_pos
  rw [← volume_pi] at hg
  exact hg.congr (Filter.Eventually.of_forall fun x => (gaussFn_eq_prod x).symm)

theorem isArchTestFn_gaussFn (Q₀ : QuadForm (𝓞 F) n) : IsArchTestFn Q₀ (fun _ => gaussFn) := by
  refine ⟨fun _ => integrable_gaussFn, fun w => ?_⟩
  obtain ⟨B, hB0, hB⟩ := abs_eval_le_sum_sq (Siegel.realForm Q₀ w)
  obtain ⟨C, hC⟩ := exists_bound_rpow_mul_exp (s := 1) zero_le_one (half_pos Real.pi_pos)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 1 zero_le_one)
  have hi : Integrable (fun x : Fin n → ℝ => B * C * ∏ i, Real.exp (-(Real.pi / 2) * x i ^ 2))
      (volume : Measure (Fin n → ℝ)) := by
    have hg : Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (-(Real.pi / 2) * x i ^ 2))
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
      Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq (half_pos Real.pi_pos)
    rw [← volume_pi] at hg
    exact hg.const_mul _
  refine hi.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_realVal Q₀ w).abs.mul (by unfold gaussFn; fun_prop)).aestronglyMeasurable
  · set u := ∑ i, x i ^ 2 with hu
    have hu0 : 0 ≤ u := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hprod : ∏ i, Real.exp (-(Real.pi / 2) * x i ^ 2) = Real.exp (-(Real.pi / 2) * u) := by
      rw [← Real.exp_sum, hu, Finset.mul_sum]
    rw [hprod, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (by unfold gaussFn; positivity))]
    have h1 : |realVal Q₀ w x| ≤ B * u := hB x
    have h2 := hC u hu0
    rw [Real.rpow_one] at h2
    have h3 : Real.exp (-Real.pi * u) = Real.exp (-(Real.pi / 2) * u) * Real.exp (-(Real.pi / 2) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    show |realVal Q₀ w x| * Real.exp (-Real.pi * u) ≤ _
    rw [h3]
    have he := (Real.exp_pos (-(Real.pi / 2) * u)).le
    calc |realVal Q₀ w x| * (Real.exp (-(Real.pi / 2) * u) * Real.exp (-(Real.pi / 2) * u))
        ≤ (B * u) * (Real.exp (-(Real.pi / 2) * u) * Real.exp (-(Real.pi / 2) * u)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = B * (u * Real.exp (-(Real.pi / 2) * u)) * Real.exp (-(Real.pi / 2) * u) := by ring
      _ ≤ B * C * Real.exp (-(Real.pi / 2) * u) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hB0) he

theorem integral_gaussFn : ∫ x : Fin n → ℝ, gaussFn x = 1 := by
  have h := integral_fintype_prod_volume_eq_prod (ι := Fin n) (𝕜 := ℝ) (E := fun _ => ℝ)
    (fun (_ : Fin n) (x : ℝ) => Real.exp (-Real.pi * x ^ 2))
  simp_rw [gaussFn_eq_prod]
  rw [h]
  have h1 : ∀ _i : Fin n, ∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) = 1 := by
    intro _
    rw [integral_gaussian]
    simp
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_const_one]

theorem phiIntegralNF_gaussFn [IsEmpty {w : InfinitePlace F // w.IsComplex}] :
    phiIntegralNF (n := n) (fun _ : RealPlace F => gaussFn) (fun _ _ => 0) =
      |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) := by
  rw [phiIntegralNF, phiIntegral_eq]
  simp [integral_gaussFn]

theorem toReal_muFinVec_OHatVec' :
    (muFinVec F (Fin n) OHatVec).toReal = |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) := by
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [muFinVec_OHatVec, muFin_OHat, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (ohatVol_pos (F := F)).le, ENNReal.toReal_ofReal (by have := ohatVol_pos (F := F); positivity)]
  rw [ohatVol, inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hd.le,
    ← Real.rpow_neg hd.le]
  congr 1
  ring

theorem muFinVec_eq_phiIntegralNF_gaussFn [IsEmpty {w : InfinitePlace F // w.IsComplex}] :
    (muFinVec F (Fin n) OHatVec).toReal = 1 * phiIntegralNF (n := n) (fun _ : RealPlace F => gaussFn) (fun _ _ => 0) := by
  rw [one_mul, phiIntegralNF_gaussFn, toReal_muFinVec_OHatVec']

end QuadFormsKB.Tamagawa.Measure.Weil

end
