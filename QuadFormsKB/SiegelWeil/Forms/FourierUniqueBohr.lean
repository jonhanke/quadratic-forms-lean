/-
# Uniqueness of the coefficients of an absolutely convergent exponential sum on $\mathbb R$

**Layer:** elementary analysis on $\mathbb R$ (no arithmetic input).

**Result.** `coeff_eq_zero_of_tsum_exp_eq_zero`: let $(c_i)_{i\in\iota}$ be absolutely summable complex numbers ($\iota$ countable) and
$(\lambda_i)$ pairwise distinct real frequencies. If $\sum_ic_ie^{2\pi i\lambda_it} = 0$ for every real $t$, then every $c_i = 0$.

*Proof (Bohr's mean value):* for fixed $j$ and $R > 0$,
$$0 = \frac1R\int_0^R\sum_ic_ie^{2\pi i(\lambda_i-\lambda_j)t}\,dt = \sum_ic_iA_R(\lambda_i - \lambda_j),\qquad
  A_R(\mu) = \frac1R\int_0^Re^{2\pi i\mu t}dt,$$
with $|A_R| \le 1$, $A_R(0) = 1$ and $A_R(\mu) = (e^{2\pi i\mu R} - 1)/(2\pi i\mu R) \to 0$ for $\mu \ne 0$; dominated convergence for
sums (Tannery) gives $c_j = 0$.

Source: Bohr, *Fastperiodische Funktionen* (1932) (the mean value of an almost periodic function) [unverified]; used here for
the uniqueness of Fourier expansions on $\mathbb H_r^d$ (`FourierUnique.lean`).
-/
import Mathlib

open MeasureTheory Complex
open scoped Real

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-- The unit-modulus exponential $e^{2\pi i\mu t}$ for real $\mu, t$. -/
lemma norm_cexp_two_pi_I_mul (μ t : ℝ) : ‖cexp (2 * π * I * ((μ : ℂ) * t))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The mean value $A_R(\mu) = \frac1R\int_0^R e^{2\pi i\mu t}\,dt$. -/
def meanExp (R μ : ℝ) : ℂ := (R : ℂ)⁻¹ * ∫ t in (0 : ℝ)..R, cexp (2 * π * I * ((μ : ℂ) * t))

/-- $|A_R(\mu)| \le 1$ for $R > 0$. -/
lemma norm_meanExp_le (R μ : ℝ) (hR : 0 < R) : ‖meanExp R μ‖ ≤ 1 := by
  unfold meanExp
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := R)
    (f := fun t : ℝ => cexp (2 * π * I * ((μ : ℂ) * t))) (C := 1)
    (fun x _ => (norm_cexp_two_pi_I_mul μ x).le)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [sub_zero, abs_of_pos hR] at h
  calc R⁻¹ * ‖∫ t in (0 : ℝ)..R, cexp (2 * π * I * ((μ : ℂ) * t))‖ ≤ R⁻¹ * (1 * R) :=
        by gcongr
    _ = 1 := by field_simp

/-- $A_R(0) = 1$ for $R > 0$. -/
lemma meanExp_zero (R : ℝ) (hR : 0 < R) : meanExp R 0 = 1 := by
  unfold meanExp
  simp [hR.ne']

/-- For $\mu \ne 0$, $|A_R(\mu)| \le 2/(2\pi|\mu|R)$. -/
lemma norm_meanExp_le_of_ne (R μ : ℝ) (hR : 0 < R) (hμ : μ ≠ 0) :
    ‖meanExp R μ‖ ≤ (2 / (2 * π * |μ|)) * R⁻¹ := by
  unfold meanExp
  have hc : (2 * π * I * (μ : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, hμ]
  have hint : (∫ t in (0 : ℝ)..R, cexp (2 * π * I * ((μ : ℂ) * t)))
      = (cexp ((2 * π * I * (μ : ℂ)) * R) - cexp ((2 * π * I * (μ : ℂ)) * (0 : ℝ)))
        / (2 * π * I * (μ : ℂ)) := by
    rw [← integral_exp_mul_complex hc]
    congr 1; funext t; congr 1; ring
  rw [hint, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_div]
  have hn : ‖(2 * π * I * (μ : ℂ))‖ = 2 * π * |μ| := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  have hnum : ‖cexp ((2 * π * I * (μ : ℂ)) * R) - cexp ((2 * π * I * (μ : ℂ)) * (0 : ℝ))‖ ≤ 2 := by
    have h1 : ‖cexp ((2 * π * I * (μ : ℂ)) * R)‖ = 1 := by
      have := norm_cexp_two_pi_I_mul μ R
      rw [← this]; congr 2; ring
    have h2 : ‖cexp ((2 * π * I * (μ : ℂ)) * (0 : ℝ))‖ = 1 := by simp
    calc _ ≤ ‖cexp ((2 * π * I * (μ : ℂ)) * R)‖ + ‖cexp ((2 * π * I * (μ : ℂ)) * (0 : ℝ))‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  rw [hn]
  have hpos : 0 < 2 * π * |μ| := by positivity
  calc R⁻¹ * (‖_‖ / (2 * π * |μ|)) ≤ R⁻¹ * (2 / (2 * π * |μ|)) := by gcongr
    _ = _ := by ring

/-- For $\mu \ne 0$, $A_{n+1}(\mu) \to 0$ as $n \to \infty$. -/
lemma tendsto_meanExp (μ : ℝ) (hμ : μ ≠ 0) :
    Filter.Tendsto (fun n : ℕ => meanExp ((n : ℝ) + 1) μ) Filter.atTop (nhds 0) := by
  have hK : Filter.Tendsto (fun n : ℕ => (2 / (2 * π * |μ|)) * ((n : ℝ) + 1)⁻¹) Filter.atTop
      (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop)).const_mul
        (2 / (2 * π * |μ|))
  refine squeeze_zero_norm (fun n => ?_) hK
  exact norm_meanExp_le_of_ne _ _ (by positivity) hμ

/-- **Uniqueness of the coefficients of an absolutely convergent exponential sum** with distinct real frequencies. -/
theorem coeff_eq_zero_of_tsum_exp_eq_zero {ι : Type*} [Countable ι] (c : ι → ℂ) (hc : Summable fun i => ‖c i‖)
    (lam : ι → ℝ) (hlam : Function.Injective lam)
    (h : ∀ t : ℝ, ∑' i, c i * cexp (2 * π * I * (lam i * t)) = 0) (j : ι) : c j = 0 := by
  -- Step 1: shift frequencies by `lam j`.
  have h1 : ∀ t : ℝ, ∑' i, c i * cexp (2 * π * I * (((lam i - lam j : ℝ) : ℂ) * t)) = 0 := by
    intro t
    have e : ∀ i, c i * cexp (2 * π * I * (((lam i - lam j : ℝ) : ℂ) * t))
        = c i * cexp (2 * π * I * (lam i * t)) * cexp (-(2 * π * I * (lam j * t))) := by
      intro i
      rw [mul_assoc (c i) (cexp _) (cexp _), ← Complex.exp_add]
      congr 2; push_cast; ring
    simp_rw [e]
    rw [tsum_mul_right, h t, zero_mul]
  -- Step 2: the mean over `[0, R]` vanishes.
  have h2 : ∀ R : ℝ, 0 < R → ∑' i, c i * meanExp R (lam i - lam j) = 0 := by
    intro R hR
    set F : ι → ℝ → ℂ := fun i t => c i * cexp (2 * π * I * (((lam i - lam j : ℝ) : ℂ) * t)) with hF
    have hFc : ∀ i, Continuous (F i) := fun i => by
      simp only [hF]; fun_prop
    have hint : ∀ i, Integrable (F i) (volume.restrict (Set.Ioc 0 R)) := fun i =>
      ((hFc i).continuousOn.integrableOn_Icc (a := 0) (b := R)).mono_set Set.Ioc_subset_Icc_self
    have hnorm : ∀ i, ∫ a in Set.Ioc 0 R, ‖F i a‖ = ‖c i‖ * R := by
      intro i
      have : ∀ a, ‖F i a‖ = ‖c i‖ := fun a => by
        simp only [hF]; rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
      simp_rw [this]
      simp [Measure.real, hR.le, mul_comm]
    have hsum : Summable fun i => ∫ a in Set.Ioc 0 R, ‖F i a‖ := by
      simp_rw [hnorm]; exact hc.mul_right _
    have hHS := hasSum_integral_of_summable_integral_norm hint hsum
    have hz : (∫ a in Set.Ioc 0 R, ∑' i, F i a) = 0 := by
      simp only [hF, h1]; simp
    rw [hz] at hHS
    have hterm : ∀ i, (∫ a in Set.Ioc 0 R, F i a) = (R : ℂ) * (c i * meanExp R (lam i - lam j)) := by
      intro i
      rw [← intervalIntegral.integral_of_le hR.le]
      simp only [hF]
      rw [intervalIntegral.integral_const_mul]
      unfold meanExp
      field_simp [hR.ne']
    simp_rw [hterm] at hHS
    have := hHS.tsum_eq
    rw [tsum_mul_left] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by exact_mod_cast hR.ne')
    · exact h0
  -- Step 3: Tannery.
  classical
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (n : ℕ) i => c i * meanExp ((n : ℝ) + 1) (lam i - lam j))
    (g := fun i => if i = j then c j else 0) (bound := fun i => ‖c i‖) hc
    (fun i => by
      by_cases hij : i = j
      · subst hij
        simp only [ite_true, sub_self]
        have : ∀ n : ℕ, meanExp ((n : ℝ) + 1) 0 = 1 := fun n => meanExp_zero _ (by positivity)
        simp [this]
      · have hne : lam i - lam j ≠ 0 := sub_ne_zero.mpr (fun e => hij (hlam e))
        simp only [hij, ite_false]
        simpa using (tendsto_meanExp _ hne).const_mul (c i))
    (Filter.Eventually.of_forall fun n i => by
      rw [norm_mul]
      calc ‖c i‖ * ‖meanExp ((n : ℝ) + 1) (lam i - lam j)‖ ≤ ‖c i‖ * 1 := by
            gcongr; exact norm_meanExp_le _ _ (by positivity)
        _ = ‖c i‖ := mul_one _)
  have hconst : (fun n : ℕ => ∑' i, c i * meanExp ((n : ℝ) + 1) (lam i - lam j)) = fun _ => 0 :=
    funext fun n => h2 _ (by positivity)
  rw [hconst, tsum_ite_eq] at hT
  exact (tendsto_nhds_unique tendsto_const_nhds hT).symm

end QuadFormsKB.SiegelWeil.Forms
