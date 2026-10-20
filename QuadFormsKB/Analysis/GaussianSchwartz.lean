/-
Partly adapted from Physlib (HEPLean/PhysLean, Apache-2.0), file
`Physlib/Mathematics/InnerProductSpace/Gaussian.lean` (author Gregory J. Loges): the derivative bound
`norm_iteratedFDeriv_innerSL_le_pow` is copied, and the proof pattern of `realStdGaussian` is
generalized from the real rate `1/2` to a complex rate `b` with `0 < Re b`. The bound
`exists_bound_pow_mul_exp_neg_mul_of_nonneg` and the iterated-derivative computation are adapted from
Sphere-Packing-Lean (Apache-2.0), math-inc/Sphere-Packing-Lean commit 1e98fb4,
`SpherePacking/Dim24/Uniqueness/Rigidity/Classify/EvenUnimodular/ThetaTransform.lean`.
Ported to Mathlib for Lean v4.35.0 for QuadFormsKB.
-/
import Mathlib
import QuadFormsKB.Citation

/-!
# Complex Gaussians as Schwartz functions

For a real inner product space $V$ and $b \in \mathbb{C}$ with $\operatorname{Re} b > 0$, the function
$$g_b(\vec{v}) = e^{-b\,\|\vec{v}\|^2}$$
is a Schwartz function $V \to \mathbb{C}$ (`QuadFormsKB.Analysis.gaussianSchwartz`). Mathlib (v4.35.0) has the
Fourier transform of $g_b$ (`fourier_gaussian_innerProductSpace`) but not $g_b$ as a `SchwartzMap`; this file
supplies it so that Poisson summation for Schwartz functions applies to Gaussians.
-/

open Real Complex Filter ContinuousLinearMap
open scoped SchwartzMap

namespace QuadFormsKB.Analysis

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- (Physlib.) Crude bounds on the iterated derivatives of $\vec{x} \mapsto \langle \vec{x}, \vec{x}\rangle$. -/
private lemma norm_iteratedFDeriv_innerSL_le_pow (x : E) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun x : E ↦ innerSL ℝ x x) x‖ ≤ (2 + ‖x‖ ^ 2) ^ n := by
  have h_id₁ : ‖iteratedFDeriv ℝ 1 id x‖ ≤ 1 := by simp [norm_id_le]
  have h_id : ∀ k ≥ 2, ‖iteratedFDeriv ℝ k id x‖ = 0 := by
    intro k hk
    rw [show k = k - 2 + 2 by omega, norm_eq_zero]
    ext
    simp [iteratedFDeriv_succ_apply_right]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        n.choose k * ‖iteratedFDeriv ℝ k id x‖ * ‖iteratedFDeriv ℝ (n - k) id x‖ :=
      (innerSL ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
        contDiff_id contDiff_id x (Nat.cast_le.mpr n.le_succ) (norm_innerSL_le ℝ)
    _ = n.choose 0 * ‖iteratedFDeriv ℝ 0 id x‖ * ‖iteratedFDeriv ℝ (n - 0) id x‖ +
        n.choose 1 * ‖iteratedFDeriv ℝ 1 id x‖ * ‖iteratedFDeriv ℝ (n - 1) id x‖ := by
      refine Finset.sum_eq_add_of_mem 0 1 ?_ ?_ zero_ne_one fun k hk hk₀₁ ↦ ?_
      · simp
      · simp [Nat.zero_lt_of_lt hn]
      · simp [h_id, hk₀₁, Nat.two_le_iff]
    _ ≤ ‖x‖ * ‖iteratedFDeriv ℝ n id x‖ + n.choose 1 * ‖iteratedFDeriv ℝ (n - 1) id x‖ := by bound
  rcases (show n = 1 ∨ n = 2 ∨ 2 < n by omega) with rfl | rfl | hn'
  · refine le_trans (b := 2 * ‖x‖) ?_ (by nlinarith)
    simp [← le_sub_iff_add_le, two_mul, mul_le_of_le_one_right, norm_id_le]
  · refine le_trans ?_ (le_trans (le_self_pow₀ one_le_two two_ne_zero) (by bound))
    simp [h_id, norm_id_le]
  · rw [h_id n (by omega), h_id (n - 1) (by omega), mul_zero, mul_zero, add_zero]
    positivity

/-- (Sphere-Packing-Lean.) $x^k e^{-a x}$ is bounded on $[0, \infty)$ for $a > 0$. -/
lemma exists_bound_pow_mul_exp_neg_mul_of_nonneg (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-a * x) ≤ C := by
  have hlim :
      Tendsto (fun x : ℝ => x ^ k * Real.exp (-a * x)) atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (k : ℝ)) (b := a) ha)
  have hevent : ∀ᶠ x : ℝ in atTop, x ^ k * Real.exp (-a * x) ≤ 1 :=
    (hlim.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)))
  rcases (Filter.eventually_atTop.1 hevent) with ⟨R, hR⟩
  let R0 : ℝ := max R 0
  have hcont : Continuous fun x : ℝ => x ^ k * Real.exp (-a * x) := by
    fun_prop
  have hne : (Set.Icc (0 : ℝ) R0).Nonempty := ⟨0, le_rfl, le_max_right R 0⟩
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) R0)).exists_isMaxOn hne hcont.continuousOn with
    ⟨x0, hx0, hxmax⟩
  refine ⟨max (x0 ^ k * Real.exp (-a * x0)) 1, ?_⟩
  intro x hx
  by_cases hxR : x ≤ R0
  · exact (hxmax ⟨hx, hxR⟩).trans (le_max_left _ _)
  · exact (hR x (le_trans (le_max_left R 0) (le_of_not_ge hxR))).trans (le_max_right _ _)

/-- The profile $t \mapsto e^{c t}$ on $\mathbb{R}$, $c \in \mathbb{C}$. -/
private def expProfile (c : ℂ) : ℝ → ℂ := fun t => cexp (c * (t : ℂ))

private lemma expProfile_contDiff (c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (expProfile c) := by
  have : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => c * (t : ℂ)) := contDiff_const.mul ofRealCLM.contDiff
  exact this.cexp

/-- (Sphere-Packing-Lean, `thetaProfile_iteratedDeriv`, with a general constant.)
$\frac{d^n}{dt^n} e^{ct} = c^n e^{ct}$. -/
private lemma expProfile_iteratedDeriv (c : ℂ) (n : ℕ) :
    iteratedDeriv n (expProfile c) = fun t => c ^ n * expProfile c t := by
  induction n with
  | zero => funext t; simp
  | succ n hn =>
    funext t
    rw [iteratedDeriv_succ, hn]
    have hlin : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c t := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal
    have h := (hlin.cexp).const_mul (c ^ n)
    rw [show (fun x => c ^ n * expProfile c x) = fun x : ℝ => c ^ n * cexp (c * (x : ℂ)) from rfl,
      h.deriv]
    simp only [expProfile]
    ring

private lemma norm_expProfile (c : ℂ) (t : ℝ) : ‖expProfile c t‖ = Real.exp (c.re * t) := by
  simp [expProfile, Complex.norm_exp]

/-- **The complex Gaussian $\vec{v} \mapsto e^{-b\|\vec{v}\|^2}$ as a Schwartz function**, for
$\operatorname{Re} b > 0$. -/
def gaussianSchwartz (b : ℂ) (hb : 0 < b.re) : 𝓢(E, ℂ) where
  toFun x := cexp (-b * ((‖x‖ ^ 2 : ℝ) : ℂ))
  smooth' := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => ((‖x‖ ^ 2 : ℝ) : ℂ)) :=
      ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)
    exact (contDiff_const.mul h1).cexp
  decay' k n := by
    set a := b.re
    -- the derivative bound for the profile, uniform in the order `m ≤ n`
    set M : ℝ := (max 1 ‖-b‖) ^ n
    obtain ⟨C, hC⟩ := exists_bound_pow_mul_exp_neg_mul_of_nonneg (k + n) hb
    refine ⟨n.factorial * M * Real.exp (2 * a) * C, fun x => ?_⟩
    have hcomp : (fun x : E => cexp (-b * ((‖x‖ ^ 2 : ℝ) : ℂ))) =
        expProfile (-b) ∘ fun x : E => innerSL ℝ x x := by
      funext x; simp [expProfile]
    have hD : ‖iteratedFDeriv ℝ n (fun x : E => cexp (-b * ((‖x‖ ^ 2 : ℝ) : ℂ))) x‖ ≤
        n.factorial * (M * Real.exp (-a * ‖x‖ ^ 2)) * (2 + ‖x‖ ^ 2) ^ n := by
      rw [hcomp]
      refine norm_iteratedFDeriv_comp_le (expProfile_contDiff (-b)) ?_ (by exact_mod_cast le_top)
        x ?_ ?_
      · exact ContDiff.inner ℝ contDiff_id contDiff_id
      · intro m hm
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, expProfile_iteratedDeriv, norm_mul,
          norm_pow, norm_expProfile]
        have hinner : innerSL ℝ x x = ‖x‖ ^ 2 := by simp
        rw [hinner, Complex.neg_re]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        calc ‖-b‖ ^ m ≤ (max 1 ‖-b‖) ^ m := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) m
          _ ≤ M := pow_le_pow_right₀ (le_max_left _ _) hm
      · exact fun m hm _ => norm_iteratedFDeriv_innerSL_le_pow x hm
    have hM : 0 ≤ M := by positivity
    set u : ℝ := 2 + ‖x‖ ^ 2
    have hu : 0 ≤ u := by positivity
    have hxu : ‖x‖ ≤ u := by nlinarith [norm_nonneg x]
    have hpow : ‖x‖ ^ k ≤ u ^ k := pow_le_pow_left₀ (norm_nonneg _) hxu k
    have hexp : Real.exp (-a * ‖x‖ ^ 2) = Real.exp (2 * a) * Real.exp (-a * u) := by
      rw [← Real.exp_add]; congr 1; simp only [u]; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E => cexp (-b * ((‖x‖ ^ 2 : ℝ) : ℂ))) x‖
        ≤ u ^ k * (n.factorial * (M * Real.exp (-a * ‖x‖ ^ 2)) * u ^ n) :=
          mul_le_mul hpow hD (norm_nonneg _) (by positivity)
      _ = n.factorial * M * Real.exp (2 * a) * (u ^ (k + n) * Real.exp (-a * u)) := by
          rw [hexp, pow_add]; ring
      _ ≤ n.factorial * M * Real.exp (2 * a) * C :=
          mul_le_mul_of_nonneg_left (hC u hu) (by positivity)

@[simp] theorem gaussianSchwartz_apply (b : ℂ) (hb : 0 < b.re) (x : E) :
    gaussianSchwartz b hb x = cexp (-b * ((‖x‖ ^ 2 : ℝ) : ℂ)) := rfl

end

end QuadFormsKB.Analysis
