/-
# Hua's integral, analytic part: the one-dimensional and radial integrals

**Layer:** local, one real place; elementary Lebesgue integrals (no global input).
$c_1(\sigma) = \int_{\mathbb R}(1 + t^2)^{-\sigma/2}dt$ (`hc1`, finite for $\sigma > 1$), $c_2(r,\sigma) = \int_{\mathbb R^r}(1 + w^{\mathsf T}w)^{1-\sigma}dw$
(`hc2`, finite for $2(\sigma - 1) > r$), $\int|(a - q) + iy|^{-\sigma}da = y^{1-\sigma}c_1(\sigma)$, and the linear change of variables
$\int f = |\det A|\int f(A\,\cdot)$; used by `ArchHua.lean`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.ArchVolume

open MeasureTheory Matrix Complex
open scoped Real ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open QuadFormsKB.Tamagawa.ArchVol

/-! ### The one-dimensional and radial integrals -/

/-- $c_1(\sigma) = \int_{\mathbb R}(1 + t^2)^{-\sigma/2}\,dt$. -/
def hc1 (σ : ℝ) : ℝ≥0∞ := ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ (-σ / 2))

/-- $c_2(r, \sigma) = \int_{\mathbb R^r}(1 + w^{\mathsf T}w)^{1-\sigma}\,dw$. -/
def hc2 (r : ℕ) (σ : ℝ) : ℝ≥0∞ := ∫⁻ w : Fin r → ℝ, ENNReal.ofReal ((1 + w ⬝ᵥ w) ^ (1 - σ))

/-- Pointwise: $|x + iy|^{-\sigma} = (x^2 + y^2)^{-\sigma/2}$. -/
theorem norm_add_I_rpow_eq (σ x y : ℝ) :
    ‖((x : ℝ) : ℂ) + I * y‖ ^ (-σ) = (x ^ 2 + y ^ 2) ^ (-σ / 2) := by
  rw [mul_comm I, Complex.norm_add_mul_I, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1; ring

/-- $\int_{\mathbb R}|(a - q) + iy|^{-\sigma}\,da = y^{1-\sigma}c_1(\sigma)$ for $y > 0$. -/
theorem lintegral_norm_add_I_rpow {σ q y : ℝ} (hy : 0 < y) :
    ∫⁻ a : ℝ, ENNReal.ofReal (‖((a - q : ℝ) : ℂ) + I * y‖ ^ (-σ)) = ENNReal.ofReal (y ^ (1 - σ)) * hc1 σ := by
  simp only [norm_add_I_rpow_eq]
  rw [lintegral_sub_right_eq_self (fun a : ℝ => ENNReal.ofReal ((a ^ 2 + y ^ 2) ^ (-σ / 2))) q]
  have hy0 : y ≠ 0 := hy.ne'
  have hmap := Real.map_volume_mul_left hy0
  set F : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal ((a ^ 2 + y ^ 2) ^ (-σ / 2)) with hF
  have hFm : Measurable F := by
    simp only [hF]; fun_prop
  have h1 : ∫⁻ t, F (y * t) = ∫⁻ a, F a ∂(Measure.map (y * ·) volume) :=
    (lintegral_map hFm (measurable_const_mul y)).symm
  rw [hmap, lintegral_smul_measure, abs_inv, abs_of_pos hy] at h1
  have h2 : ∫⁻ a, F a = ENNReal.ofReal y * ∫⁻ t, F (y * t) := by
    rw [h1, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hy.le, mul_inv_cancel₀ hy0,
      ENNReal.ofReal_one, one_mul]
  rw [h2]
  have h3 : ∀ t : ℝ, F (y * t) = ENNReal.ofReal (y ^ (-σ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-σ / 2)) := by
    intro t
    simp only [hF]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (y * t) ^ 2 + y ^ 2 = y ^ 2 * (1 + t ^ 2) := by ring
    rw [this, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    congr 2; push_cast; ring
  simp only [h3]
  rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc, ← ENNReal.ofReal_mul hy.le,
    sub_eq_add_neg 1 σ, Real.rpow_add hy, Real.rpow_one]
  rfl

theorem hc1_lt_top {σ : ℝ} (hσ : 1 < σ) : hc1 σ < ∞ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := σ)
    (by simpa using hσ)
  simp only [Real.norm_eq_abs, sq_abs] at h
  have := h.lintegral_lt_top
  unfold hc1
  exact this

theorem hc2_lt_top {r : ℕ} {σ : ℝ} (hσ : (r : ℝ) < 2 * (σ - 1)) : hc2 r σ < ∞ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Fin r → ℝ) (μ := volume) (r := 2 * (σ - 1))
    (by simpa using hσ)
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) h.lintegral_lt_top
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : ‖w‖ ^ 2 ≤ w ⬝ᵥ w := by
    have hnn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have : ‖w‖ ≤ √(w ⬝ᵥ w) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      refine Real.le_sqrt_of_sq_le ?_
      rw [Real.norm_eq_abs, sq_abs, sq]
      exact Finset.single_le_sum (f := fun j => w j * w j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    calc ‖w‖ ^ 2 ≤ √(w ⬝ᵥ w) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt hnn
  have e : -(2 * (σ - 1)) / 2 = 1 - σ := by ring
  rw [e]
  have hσ' : 1 - σ ≤ 0 := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hσ'

/-- Change of variables $u = Aw$: $\int f(u)\,du = |\det A|\int f(Aw)\,dw$. -/
theorem lintegral_eq_det_mul_comp {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ} (hA : A.det ≠ 0)
    {f : (Fin r → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f u = ENNReal.ofReal |A.det| * ∫⁻ w, f (A *ᵥ w) := by
  have hmeas : Measurable fun y : Fin r → ℝ => A *ᵥ y :=
    (Matrix.toLin' A).continuous_of_finiteDimensional.measurable
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  have h1 : ∫⁻ w, f (A *ᵥ w) = ∫⁻ u, f u ∂(Measure.map (fun y : Fin r → ℝ => A *ᵥ y) volume) :=
    (lintegral_map hf hmeas).symm
  have h' : Measure.map (fun y : Fin r → ℝ => A *ᵥ y) volume = ENNReal.ofReal |A.det|⁻¹ • volume := by
    rw [← abs_inv]; exact h
  rw [h1, h', lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    mul_inv_cancel₀ (abs_ne_zero.mpr hA), ENNReal.ofReal_one, one_mul]

end QuadFormsKB.SiegelWeil.Forms.ArchR
