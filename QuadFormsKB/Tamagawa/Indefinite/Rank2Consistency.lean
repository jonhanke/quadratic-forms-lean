/-
# Consistency checks for Siegel's formula with a rank-2 complement

**Layer:** number fields; $\mathbb Q$.

* `ternaryDensityProductReg_eq_chiTern`, `siegelProduct3_eq_ternaryDensityProductReg`: the local side of the ternary
  headline `siegelIndefinite_ternary_uncond` is the regularized ternary product (the character `chiTern Q₀ m`),
  i.e. the finite part of `siegelProduct3` (the local side of the definite statement `SiegelFormulaAt3`):
  $S_3(L,m) = \texttt{ternaryDensityProductReg}\cdot\prod_\sigma\beta_\sigma(m)$.
* Over $\mathbb Q$ (any signature), the natural-order reading holds **unconditionally**: the partial products
  $\prod_{p\le X}\beta_p(L,T_0)$ converge to the regularized product of `siegelIndefiniteForms_rank2_uncond`
  (`hasProd_normOrder_localDensityForm_rank2_rat`), and for ternary forms $\prod_{p\le X}\beta_p(L,m)$ converges to the local
  side of `siegelIndefinite_ternary_uncond` (`hasProd_normOrder_ternary_rat`).
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernary
import QuadFormsKB.Tamagawa.Indefinite.Rank2RatChecks

open Filter
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Frames LocalDensity QuadFormsKB.RegProd NFEuler

/-- **The ternary local side is the regularized product** with the character `chiTern Q₀ m`. -/
theorem ternaryDensityProductReg_eq_chiTern {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) 3)
    (m : 𝓞 F) :
    ternaryDensityProductReg Q₀ m =
      |(discr F : ℝ)| ^ (-1 : ℝ) * regProd (chiTern Q₀ m) 1 (fun v => NF.localDensity v Q₀ m) := by
  rw [ternaryDensityProductReg, chiForms_unary_eq_chiTern]

/-- **The rank-3 Siegel product is the ternary local side times the archimedean densities**:
$S_3(L,m) = \texttt{ternaryDensityProductReg}(Q_0,m)\cdot\prod_{\sigma}\beta_\sigma(m)$. -/
theorem siegelProduct3_eq_ternaryDensityProductReg {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) 3)
    (m : 𝓞 F) :
    siegelProduct3 Q₀ m = ternaryDensityProductReg Q₀ m *
      ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ) := by
  rw [ternaryDensityProductReg_eq_chiTern, siegelProduct3, siegelProductWith]
  norm_num
  ring

/-- **The natural order over $\mathbb Q$, forms by forms, unconditional**: for $Q_0$, $T_0$ over $\mathbb Z$ nondegenerate
($N = r + 2$, any signature) with $\delta$ not a square and a rational frame, the partial products
$\prod_{p\le X}\beta_p(L,T_0)$ converge to the regularized product of the headline. -/
@[kb "hanke2004" "(5.3), p. 368 (natural order over ℚ, N − r = 2) [unverified]"]
theorem hasProd_normOrder_localDensityForm_rank2_rat {r : ℕ} (Q₀ : QuadForm (𝓞 ℚ) (r + 2)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 ℚ) r) (hT : T₀.Nondegenerate) (hW : ¬ IsSquare (algebraMap (𝓞 ℚ) ℚ (deltaForms Q₀ T₀)))
    (Ξ : RatFrame Q₀ T₀) (hr : 1 ≤ r) :
    HasProd (fun v => NF.localDensityForm v Q₀ T₀)
      (regProd (chiForms Q₀ T₀) 1 fun v => NF.localDensityForm v Q₀ T₀) (normOrder ℚ) :=
  hasProd_normOrder_localDensityForm_rank2 Q₀ hQ T₀ hT hW Ξ hr
    (naturalOrderEulerOne_chiForms_rat_nondeg Q₀ T₀ hQ hT hW)

/-- **The natural order over $\mathbb Q$ for ternary forms, unconditional**: $\prod_{p\le X}\beta_p(L,m)$ converges to
$L(1,\chi)\prod_p\beta_p(L,m)(1-\chi(p)/p)$, the local side (up to $|d_F|^{-1} = 1$) of `siegelIndefinite_ternary_uncond`. -/
@[kb "hanke2004" "(5.3), p. 368 (natural order over ℚ, n = 3) [unverified]"]
theorem hasProd_normOrder_ternary_rat (Q₀ : QuadForm (𝓞 ℚ) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 ℚ}
    (hm : (m : ℚ) ≠ 0) (hW : ¬ IsSquare (-(2 * (m : ℚ) * algebraMap (𝓞 ℚ) ℚ Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : ℚ)) :
    HasProd (fun v => NF.localDensity v Q₀ m)
      (regProd (chiForms Q₀ (DVR.unary m)) 1 fun v => NF.localDensity v Q₀ m) (normOrder ℚ) := by
  have h := hasProd_normOrder_localDensityForm_rank2_rat Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
    (not_isSquare_deltaForms_unary hW) ((ratFrameEquivRatSphere Q₀ m).symm ξ) le_rfl
  simp only [NF.localDensityForm_unary] at h
  exact h

end QuadFormsKB.Tamagawa.Indefinite
