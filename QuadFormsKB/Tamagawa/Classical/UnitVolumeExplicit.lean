/-
# The unit volumes $\pi/16$ and $\log(1+\sqrt2)/(8\sqrt2)$, and Siegel's formula with explicit constants

**Layer:** $\mathbb Q$.

The unit volumes `unitVolume_sum_sumTwoSq` ($\sum_iv(M_i) = L(1,\chi_{-4})/4$) and `unitVolume_sum_pell2`
($L(1,\chi_8)/8$) with
$L(1,\chi_{-4}) = \pi/4$ and $L(1,\chi_8) = \log(1+\sqrt2)/\sqrt2$ (`LValues.lean`):
$$\sum_iv(M_i) = \frac{\pi}{16}\ \ (x_0^2+x_1^2),\qquad \sum_iv(M_i) = \frac{\log(1+\sqrt2)}{8\sqrt2}\ \ (x_0^2-2x_1^2)$$
(**`unitVolume_sum_sumTwoSq_pi`**, **`unitVolume_sum_pell2_log`**). With $c^{(1)}_\infty = |\det H|^{-1}$ ($= 1/4$, resp.
$1/8$), the binary headline $c^{(1)}_\infty\sum_in(M_i,T_0) = \frac12B(T_0)\sum_iv(M_i)$ becomes Siegel's formula with
every
constant explicit (**`siegel_sumTwoSq_explicit`**, **`siegel_pell2_explicit`**):
$$\sum_in(M_i,T_0) = \frac{\pi}{8}\,B(T_0),\qquad \sum_in(M_i,T_0) = \frac{\log(1+\sqrt2)}{2\sqrt2}\,B(T_0),$$
and at $T_0 = \langle1\rangle$: $B(1) = 8/\pi$, resp. $2\sqrt2/\log(1+\sqrt2)$. Unconditional.
-/
import QuadFormsKB.Tamagawa.Classical.LValues

open NumberField
open scoped ENNReal Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB.Binary QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure.Weil
  RatBridge LocalDensity

/-! ### The unit volumes -/

/-- **The unit volume of $x_0^2+x_1^2$** (the genus of $\mathbb Z^2$, one class; $v(M_i)$ = `unitVolume`, the volume of
$SO(M_i)\backslash SO(2)(\mathbb R)$ for Weil's measure):
$$\sum_iv(M_i) = \frac{\pi}{16}.$$
From `unitVolume_sum_sumTwoSq` and $L(1,\chi_{-4}) = \pi/4$ (`LOne_neg_four`). Unconditional. -/
@[kb "siegel1935" "Hauptsatz, n = 2, m = 1, at the number 1 (unit volume) [unverified]"]
theorem unitVolume_sum_sumTwoSq_pi :
    ∑' i, unitVolume (up sumTwoSqZ) nondegenerate_up_sumTwoSq i = ENNReal.ofReal (π / 16) := by
  rw [unitVolume_sum_sumTwoSq, LOne_neg_four]
  congr 1
  ring

/-- **The unit volume of $x_0^2-2x_1^2$** (the genus of $\mathbb Z^2$, one class; $v(M_i)$ = `unitVolume`, the volume of
$SO(M_i)\backslash SO(1,1)(\mathbb R)$ for Weil's measure, $SO(\mathbb Z^2) = \pm(3+2\sqrt2)^{\mathbb Z}$):
$$\sum_iv(M_i) = \frac{\log(1+\sqrt2)}{8\sqrt2}.$$
From `unitVolume_sum_pell2` and $L(1,\chi_8) = \log(1+\sqrt2)/\sqrt2$ (`LOne_eight`). Unconditional. -/
@[kb "siegel1935" "Hauptsatz, n = 2, m = 1, at the number 1 (unit volume) [unverified]"]
theorem unitVolume_sum_pell2_log :
    ∑' i, unitVolume (up pell2Z) nondegenerate_up_pell2 i =
      ENNReal.ofReal (Real.log (1 + Real.sqrt 2) / (8 * Real.sqrt 2)) := by
  rw [unitVolume_sum_pell2, LOne_eight]
  congr 1
  ring

/-! ### The density product at $1$ -/

/-- $B(1) = 8/\pi$ for $x_0^2+x_1^2$ (`binDensityProduct_one_sumTwoSq`: $B(1) = 2/L(1,\chi_{-4})$). -/
theorem binDensityProduct_one_sumTwoSq_pi :
    binDensityProduct (up sumTwoSqZ) (DVR.unary 1) (QField (-4)) = 8 / π := by
  rw [binDensityProduct_one_sumTwoSq, LOne_neg_four]
  field_simp
  ring

/-- $B(1) = 2\sqrt2/\log(1+\sqrt2)$ for $x_0^2-2x_1^2$ (`binDensityProduct_one_pell2`: $B(1) = 2/L(1,\chi_8)$). -/
theorem binDensityProduct_one_pell2_log :
    binDensityProduct (up pell2Z) (DVR.unary 1) (QField 8) = 2 * Real.sqrt 2 / Real.log (1 + Real.sqrt 2) := by
  rw [binDensityProduct_one_pell2, LOne_eight]
  rw [div_div_eq_mul_div]

/-! ### Siegel's formula with explicit constants -/

/-- From the binary headline: $\sum_in(M_i,T_0) = (2/(|k|\,V))^{-1}\cdots$, i.e. $|k|^{-1}N = \frac12BV$ solved for
$N$. -/
theorem tsum_repCount_of_unitVolume (Q₀ : QuadForm (𝓞 ℚ) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra ℚ E] (hE : IsDiscField Q₀ E)
    (T₀ : QuadForm (𝓞 ℚ) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀)
    {k : ℤ} (hk0 : k ≠ 0) (hk : Q₀.hessian.det = (k : 𝓞 ℚ)) {V : ℝ} (hV0 : 0 ≤ V)
    (hV : ∑' i, unitVolume Q₀ hQ i = ENNReal.ofReal V) :
    ∑' i, Indefinite.repCount Q₀ T₀ i = ENNReal.ofReal (|(k : ℝ)| * V / 2 * binDensityProduct Q₀ T₀ E) := by
  have e := siegelIndefinite_binary_uncond Q₀ hQ hA E hE T₀ hT Ξ
  rw [cInfCorankOne_rat Q₀ hk, hV] at e
  have hk' : 0 < |(k : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hk0)
  have hc0 : ENNReal.ofReal (|(k : ℝ)|⁻¹) ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hk')).ne'
  have hN : ∑' i, Indefinite.repCount Q₀ T₀ i = (ENNReal.ofReal (|(k : ℝ)|⁻¹))⁻¹ *
      (2⁻¹ * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) * ENNReal.ofReal V) := by
    rw [← e, ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
  rw [hN, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hk', inv_inv,
    ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_ofNat, div_eq_mul_inv]
  ring

/-- **Siegel's formula for $x_0^2+x_1^2$ with explicit constants** (Siegel 1935, Hauptsatz for $n = 2$, $m = 1$, with
$c^{(1)}_\infty = 1/4$, $\varepsilon = \frac12$ and $\sum_iv(M_i) = \pi/16$): for every nondegenerate unary form $T_0$ over
$\mathcal O_\mathbb Q = \mathbb Z$ represented by $x_0^2+x_1^2$ over $\mathbb Q$ (a rational frame $\Xi$),
$$\sum_in(M_i,T_0) = \frac{\pi}{8}\,B(T_0),$$
$n(M_i,T_0)$ = `Indefinite.repCount` the number of representations by the class $M_i$ modulo its units, $B(T_0)$ =
`binDensityProduct` $= L(1,\chi_E)^{-1}\prod_p\beta_p(T_0)\,(1-\chi_E(p)/p)^{-1}$ the regularized product of the local
densities, $E = \mathbb Q(i)$. Unconditional. -/
@[kb "siegel1935" "Hauptsatz, n = 2, m = 1 (explicit constants) [unverified]"]
theorem siegel_sumTwoSq_explicit (T₀ : QuadForm (𝓞 ℚ) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame (up sumTwoSqZ) T₀) :
    ∑' i, Indefinite.repCount (up sumTwoSqZ) T₀ i =
      ENNReal.ofReal (π / 8 * binDensityProduct (up sumTwoSqZ) T₀ (QField (-4))) := by
  rw [tsum_repCount_of_unitVolume (up sumTwoSqZ) nondegenerate_up_sumTwoSq anisotropicF_up_sumTwoSq (QField (-4))
    isDiscField_sumTwoSq T₀ hT Ξ (k := 4) (by norm_num) (by rw [sumTwoSqZ, hessian_det_up_diag]; norm_num)
    (by positivity) unitVolume_sum_sumTwoSq_pi]
  rw [show |((4 : ℤ) : ℝ)| = 4 by norm_num]
  congr 1
  ring

/-- **Siegel's formula for $x_0^2-2x_1^2$ with explicit constants** (Siegel 1935, Hauptsatz for $n = 2$, $m = 1$, with
$c^{(1)}_\infty = 1/8$, $\varepsilon = \frac12$ and $\sum_iv(M_i) = \log(1+\sqrt2)/(8\sqrt2)$): for every nondegenerate unary
form $T_0$ over $\mathbb Z$ represented by $x_0^2-2x_1^2$ over $\mathbb Q$ (a rational frame $\Xi$),
$$\sum_in(M_i,T_0) = \frac{\log(1+\sqrt2)}{2\sqrt2}\,B(T_0),$$
$n(M_i,T_0)$ = `Indefinite.repCount` the number of representations by the class $M_i$ modulo its (infinite) unit group,
$B(T_0)$ = `binDensityProduct` the regularized product of the local densities, $E = \mathbb Q(\sqrt2)$. Unconditional. -/
@[kb "siegel1935" "Hauptsatz, n = 2, m = 1 (explicit constants) [unverified]"]
theorem siegel_pell2_explicit (T₀ : QuadForm (𝓞 ℚ) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame (up pell2Z) T₀) :
    ∑' i, Indefinite.repCount (up pell2Z) T₀ i =
      ENNReal.ofReal (Real.log (1 + Real.sqrt 2) / (2 * Real.sqrt 2) * binDensityProduct (up pell2Z) T₀ (QField 8)) := by
  have hV0 : 0 ≤ Real.log (1 + Real.sqrt 2) / (8 * Real.sqrt 2) :=
    div_nonneg (Real.log_nonneg (by linarith [Real.sqrt_nonneg 2])) (by positivity)
  rw [tsum_repCount_of_unitVolume (up pell2Z) nondegenerate_up_pell2 anisotropicF_up_pell2 (QField 8)
    isDiscField_pell2 T₀ hT Ξ (k := -8) (by norm_num) (by rw [pell2Z, hessian_det_up_diag]; norm_num)
    hV0 unitVolume_sum_pell2_log]
  rw [show |((-8 : ℤ) : ℝ)| = 8 by norm_num]
  congr 1
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

end QuadFormsKB.Tamagawa.Classical
