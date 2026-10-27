/-
# Classical special cases: the binary headline at $m$ and at $1$

**Layer:** number fields.

`siegelIndefinite_binary_uncond` at $T_0 = \langle m\rangle$ and at $\langle1\rangle$ share $c^{(1)}_\infty(Q_0)$ and
$\sum_iv(M_i)$. If the genus has exactly one class of representations of $1$ modulo units ($\sum_in(M_i,1) = 1$), then
$$\sum_in(M_i,m) = \frac{B(m)}{B(1)},\qquad B(m) = \texttt{binDensityProduct}(Q_0,\langle m\rangle,E)$$
(`tsum_repCount_eq_ratio`): the units and the regulator, which enter only $v(M_i)$, cancel, and so do $|d_F|^{-1/2}$ and
$L(1,\chi_E)^{-1}$.
-/
import QuadFormsKB.Tamagawa.Classical.BinaryProduct

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil LocalDensity RegProd QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F]

theorem cInfCorankOne_ne_zero_of_nondegenerate {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) : cInfCorankOne Q₀ ≠ 0 := by
  have hd : algebraMap (𝓞 F) F Q₀.hessian.det ≠ 0 := algebraMap_det_ne_zero Q₀ hQ
  unfold cInfCorankOne
  refine mul_ne_zero (ENNReal.ofReal_pos.2 (cF_pos' (F := F) N)).ne' (mul_ne_zero ?_ ?_)
  · refine Finset.prod_ne_zero_iff.2 fun w _ => (ENNReal.ofReal_pos.2 (inv_pos.2 (abs_pos.2 ?_))).ne'
    exact (map_ne_zero _).2 hd
  · refine Finset.prod_ne_zero_iff.2 fun w _ => (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (norm_pos_iff.2 ?_) 2))).ne'
    exact (map_ne_zero _).2 hd

theorem cInfCorankOne_ne_top_of {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) : cInfCorankOne Q₀ ≠ ⊤ := by
  unfold cInfCorankOne
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ?_)
  · exact ENNReal.prod_ne_top fun w _ => ENNReal.ofReal_ne_top
  · exact ENNReal.prod_ne_top fun w _ => ENNReal.ofReal_ne_top

/-- **The binary headline at $m$ against $m = 1$.** If $\sum_in(M_i,1) = 1$, then for every $m$ with a rational point
$\sum_in(M_i,m) = B(m)/B(1)$, $B$ = `binDensityProduct`, and $B(1) > 0$. -/
theorem tsum_repCount_eq_ratio (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (Ξ₁ : RatFrame Q₀ (DVR.unary 1)) (h1 : ∑' i, repCount Q₀ (DVR.unary (1 : 𝓞 F)) i = 1)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (Ξ : RatFrame Q₀ (DVR.unary m)) :
    0 < binDensityProduct Q₀ (DVR.unary 1) E ∧
      ∑' i, repCount Q₀ (DVR.unary m) i =
        ENNReal.ofReal (binDensityProduct Q₀ (DVR.unary m) E / binDensityProduct Q₀ (DVR.unary 1) E) := by
  have hT1 : (DVR.unary (1 : 𝓞 F)).Nondegenerate := unary_nondegenerate (by simp)
  have e1 := siegelIndefinite_binary_uncond Q₀ hQ hA E hE (DVR.unary 1) hT1 Ξ₁
  have em := siegelIndefinite_binary_uncond Q₀ hQ hA E hE (DVR.unary m) (unary_nondegenerate hm) Ξ
  rw [h1, mul_one] at e1
  set c := cInfCorankOne Q₀
  set V := ∑' i, unitVolume Q₀ hQ i
  set B1 := binDensityProduct Q₀ (DVR.unary 1) E
  set Bm := binDensityProduct Q₀ (DVR.unary m) E
  have hc0 : c ≠ 0 := cInfCorankOne_ne_zero_of_nondegenerate Q₀ hQ
  have hct : c ≠ ⊤ := cInfCorankOne_ne_top_of Q₀
  -- from `e1`: `B(1) > 0`, `V ≠ 0`, `V ≠ ⊤`
  have hB1 : ENNReal.ofReal B1 ≠ 0 := by
    intro h; rw [h, mul_zero, zero_mul] at e1; exact hc0 e1
  have hB1pos : 0 < B1 := ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hB1)
  have hV0 : V ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hc0 e1
  have hVt : V ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) hB1)] at e1
    exact hct e1
  refine ⟨hB1pos, ?_⟩
  -- `c * N = 2⁻¹ Bm V` and `c = 2⁻¹ B1 V`, so `N * B1 = Bm`
  have key : (∑' i, repCount Q₀ (DVR.unary m) i) * ENNReal.ofReal B1 = ENNReal.ofReal Bm := by
    have h2 : (2 : ℝ≥0∞)⁻¹ * V ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) hV0
    have h2t : (2 : ℝ≥0∞)⁻¹ * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 two_ne_zero) hVt
    refine (ENNReal.mul_left_inj h2 h2t).1 ?_
    calc (∑' i, repCount Q₀ (DVR.unary m) i) * ENNReal.ofReal B1 * (2⁻¹ * V)
        = (∑' i, repCount Q₀ (DVR.unary m) i) * (2⁻¹ * ENNReal.ofReal B1 * V) := by ring
      _ = (∑' i, repCount Q₀ (DVR.unary m) i) * c := by rw [e1]
      _ = 2⁻¹ * ENNReal.ofReal Bm * V := by rw [mul_comm, em]
      _ = ENNReal.ofReal Bm * (2⁻¹ * V) := by ring
  rw [ENNReal.ofReal_div_of_pos hB1pos, ← key, ENNReal.mul_div_cancel_right hB1 ENNReal.ofReal_ne_top]

/-- **The ratio of the local products.** If $\beta_v(m) = \beta_v(1)\,r_v$ with $(r_v)$ of finite support and the $\beta_v(1)$
nonzero, then $B(m)/B(1) = \prod_vr_v$. -/
theorem binDensityProduct_div (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (Ξ₁ : RatFrame Q₀ (DVR.unary 1)) {m : 𝓞 F} (r : HeightOneSpectrum (𝓞 F) → ℝ)
    (hr : (Function.mulSupport r).Finite)
    (hβ : ∀ v, NF.localDensity v Q₀ m = NF.localDensity v Q₀ 1 * r v)
    (hB1 : 0 < binDensityProduct Q₀ (DVR.unary 1) E) :
    binDensityProduct Q₀ (DVR.unary m) E / binDensityProduct Q₀ (DVR.unary 1) E = ∏' v, r v := by
  have hT1 : (DVR.unary (1 : 𝓞 F)).Nondegenerate := unary_nondegenerate (by simp)
  have hmul := multipliable_binDensity Q₀ hQ E hE (DVR.unary 1) hT1 Ξ₁
  simp only [NF.localDensityForm_unary] at hmul
  have hprod : ∏' v, NF.localDensity v Q₀ m / lamL (chiE F E) v =
      (∏' v, NF.localDensity v Q₀ 1 / lamL (chiE F E) v) * ∏' v, r v := by
    rw [← hmul.tprod_mul (multipliable_of_hasFiniteMulSupport hr)]
    exact tprod_congr fun v => by rw [hβ]; ring
  have hB1' := hB1
  unfold binDensityProduct at hB1' ⊢
  simp only [NF.localDensityForm_unary] at hB1' ⊢
  rw [hprod]
  have hne : (|(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) * (LOne (chiE F E))⁻¹ *
      ∏' v, NF.localDensity v Q₀ 1 / lamL (chiE F E) v) ≠ 0 := hB1'.ne'
  rw [← mul_assoc]
  exact mul_div_cancel_left₀ _ hne

end QuadFormsKB.Tamagawa.Indefinite
