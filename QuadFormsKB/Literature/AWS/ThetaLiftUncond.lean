/-
# Hanke, AWS 2009 notes, §4.6: the unfolding and the theta lift without `QuotientIntegralInputs`

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §4.5–§4.6 (pp. 61–66).
The results of `AWS/Unfolding.lean` (D18, D19, D24) and `AWS/ThetaLift.lean` (D23, D24) are stated there
relative to the input `QuotientIntegralInputs` (an integral over $\Gamma\backslash G$ satisfying Weil's
formula). This file restates them (`_uncond`) for the **constructed** integral
$$I(F) = \sum_{i\in I}\frac{1}{|\Gamma\cap\alpha_iK\alpha_i^{-1}|}\int_K F(\alpha_ih)\,d\mu(h)$$
(`dosetIntegral`, `AWS/QuotientIntegral.lean`), which satisfies Weil's formula (`weil_dosetIntegral`),
and, for $G = O(V_\mathbb{A})$, for the Haar measure $\mu$ = `haarOA` with $\mathrm{vol}(K_\mathbb{A}) = 1$
(`AWS/HaarAdelic.lean`).

Moreover (`quotientIntegral_eq_dosetIntegral`), **every** integral $I$ satisfying Weil's formula agrees with
`dosetIntegral` on left-$\Gamma$-invariant functions integrable on each $\alpha_iK$, so these statements
hold for the integral over $\Gamma\backslash G$, independently of the choice of the $\alpha_i$.

The only remaining input of the theta-lift statements is `AWSInputs Q` (Lemma 4.5.1 and finiteness of
$\mathrm{Aut}(L_i)$); the finiteness of the class number enters through the given finite family of
representatives $\alpha_i$.
-/
import QuadFormsKB.Literature.AWS.HaarAdelic
import QuadFormsKB.Literature.AWS.ThetaLift

open Matrix MeasureTheory Complex Real
open scoped Pointwise UpperHalfPlane

namespace QuadFormsKB.AWS

variable {n : ℕ}

/-! ### Abstract groups -/

section Abstract

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ K : Subgroup G}

/-- **Uniqueness of the integral over $\Gamma\backslash G$** on invariant functions: any integral
satisfying Weil's formula (a term of `QuotientIntegralInputs`) agrees with `dosetIntegral` on every
left-$\Gamma$-invariant $F$ integrable on each $\alpha_iK$, where $G = \bigsqcup_i\Gamma\alpha_iK$ with
finite $\Gamma\cap\alpha_iK\alpha_i^{-1}$. In particular `dosetIntegral` does not depend on the choice of
representatives on such $F$. -/
@[kb "hanke2011aws" "§4.6, (4.5)-(4.13), pp. 63-64"]
theorem quotientIntegral_eq_dosetIntegral {μ : Measure G} (inp : QuotientIntegralInputs Γ K μ)
    {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G))
    (F : G → ℂ) (hF : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hint : ∀ i, IntegrableOn F (α i • (K : Set G)) μ) :
    inp.I F = dosetIntegral Γ K μ α F :=
  integral_eq_sum_doset inp α hcov hdisj hfin F hF hint

variable [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]

/-- **D19, (4.14)–(4.17) (p. 64), unconditional version** of `integral_indicator_mul`, for the
constructed integral `dosetIntegral` (which satisfies Weil's formula, `weil_dosetIntegral`): with
$G = \bigsqcup_i\Gamma\alpha_iK$, finite $\Gamma_i = \Gamma\cap\alpha_iK\alpha_i^{-1}$, $\Gamma$ countable,
$K$ measurable with $\mu(K) = 1$ and $\mu$ left-invariant, for left-$\Gamma$-invariant $\theta$,
$$\int_{\Gamma\backslash G}\Phi_{L_j}(h)\,\theta(h)\,dh = \frac{1}{|\Gamma_j|}\int_K\theta(\alpha_jh)\,d\mu(h).$$ -/
@[kb "hanke2011aws" "§4.6, (4.14)-(4.17), p. 64"]
theorem integral_indicator_mul_uncond (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1)
    {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G)) (j : ι)
    (θ : G → ℂ) (hθ : ∀ γ ∈ Γ, ∀ g, θ (γ * g) = θ g)
    (hint : ∀ i, IntegrableOn (fun h => dosetIndicator Γ K (α j) h * θ h) (α i • (K : Set G)) μ) :
    dosetIntegral Γ K μ α (fun h => dosetIndicator Γ K (α j) h * θ h) =
      ((Nat.card (Γ ⊓ conjSub (α j) K : Subgroup G) : ℂ))⁻¹ *
        ∫ h in (K : Set G), θ (α j * h) ∂μ :=
  integral_indicator_mul (QuotientIntegralInputs.ofDoubleCosets inferInstance hK hK1 α hcov hdisj hfin)
    α hcov hdisj hfin j θ hθ hint

/-- **D24, unconditional version** of `integral_one_eq_mass`: with the hypotheses of
`integral_indicator_mul_uncond`, the volume of $\Gamma\backslash G$ is
$\int_{\Gamma\backslash G}1\,dh = \sum_i 1/|\Gamma_i|$ (the mass). -/
@[kb "hanke2011aws" "§4.6 with §2.6, p. 34"]
theorem integral_one_eq_mass_uncond (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1)
    {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G)) :
    dosetIntegral Γ K μ α (fun _ => 1) = ∑ i, ((Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ))⁻¹ :=
  integral_one_eq_mass (QuotientIntegralInputs.ofDoubleCosets inferInstance hK hK1 α hcov hdisj hfin)
    α hcov hdisj hfin

/-- **D24, unconditional version** of `integral_eq_sum_integral_indicator_mul`: for left-$\Gamma$-invariant
$\theta$, $\int_{\Gamma\backslash G}\theta = \sum_j\int_{\Gamma\backslash G}\Phi_{L_j}\theta$. -/
@[kb "hanke2011aws" "§4.5-§4.6, pp. 62-66"]
theorem integral_eq_sum_integral_indicator_mul_uncond (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1)
    {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G))
    (θ : G → ℂ) (hθ : ∀ γ ∈ Γ, ∀ g, θ (γ * g) = θ g)
    (hint : ∀ i, IntegrableOn θ (α i • (K : Set G)) μ)
    (hint' : ∀ i j, IntegrableOn (fun h => dosetIndicator Γ K (α j) h * θ h) (α i • (K : Set G)) μ) :
    dosetIntegral Γ K μ α θ =
      ∑ j, dosetIntegral Γ K μ α (fun h => dosetIndicator Γ K (α j) h * θ h) :=
  integral_eq_sum_integral_indicator_mul
    (QuotientIntegralInputs.ofDoubleCosets inferInstance hK hK1 α hcov hdisj hfin)
    α hcov hdisj hfin θ hθ hint hint'

end Abstract

/-! ### The adelic orthogonal group -/

/-- **D24 for $O(V)\backslash O(V_\mathbb{A})$, unconditional**: for $H$ positive definite over
$\mathbb{R}$, representatives $\alpha_i$ of the double cosets $O(V)\alpha_iK_\mathbb{A}$ with finite
$\mathrm{Aut}(L_i) = O(V)\cap\alpha_iK_\mathbb{A}\alpha_i^{-1}$, and the Haar measure $dh_\mathbb{A}$ with
$\mathrm{vol}(K_\mathbb{A}) = 1$,
$$\mathrm{vol}\bigl(O(V)\backslash O(V_\mathbb{A})\bigr) = \sum_i\frac{1}{|\mathrm{Aut}(L_i)|}.$$ -/
@[kb "hanke2011aws" "§4.6 with §2.6, p. 34"]
theorem integral_one_eq_mass_OA (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : (H.map (algebraMap ℚ ℝ)).PosDef) {ι : Type*} [Fintype ι] (α : ι → OA H)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints H) (KA H))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints H) (KA H) (α i) =
      DoubleCoset.mk (ratPoints H) (KA H) (α j) → i = j)
    (hfin : ∀ i, Finite (ratPoints H ⊓ conjSub (α i) (KA H) : Subgroup (OA H))) :
    dosetIntegral (ratPoints H) (KA H) (haarOA H hH) α (fun _ => 1) =
      ∑ i, ((Nat.card (ratPoints H ⊓ conjSub (α i) (KA H) : Subgroup (OA H)) : ℂ))⁻¹ :=
  integral_one_eq_mass_uncond (isOpen_KA H).measurableSet (haarOA_KA H hH) α hcov hdisj hfin

variable (Q : QuadForm ℚ n)

/-- **D23: (4.4)–(4.34), pp. 63–66, unconditional in the quotient integral.** Version of
`thetaLift_indicator_eq` for the integral over $O(V)\backslash O(V_\mathbb{A})$ constructed from the Haar
measure `haarOA` ($\mathrm{vol}(K_\mathbb{A}) = 1$; Weil's formula is `weil_OA`), for $Q$ positive definite:
$$\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,y^{n/4}\,\Theta_{L_j}(z).$$
Conditional on `AWSInputs Q` only. -/
@[kb "hanke2011aws" "§4.6, (4.4)-(4.34), pp. 63-66"]
theorem thetaLift_indicator_eq_uncond (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef) (I : AWSInputs Q)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    dosetIntegral (ratPoints Q.hessian) (KA Q.hessian) (haarOA Q.hessian hH) α
        (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian I.gluing (α j) stdLat)) : ℂ)⁻¹ *
        (((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) *
          thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z) :=
  thetaLift_indicator_eq Q
    (quotientIntegralInputsOA Q.hessian hH α hcov hdisj fun i => I.finite_aut (α i)) I α hα hcov hdisj j z

/-- **D23, (4.35)–(4.37), p. 66, unconditional in the quotient integral**: version of
`thetaLift_classical` for the constructed integral (Haar measure `haarOA`), for $Q$ positive definite:
$$y^{-n/4}\,\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,\Theta_{L_j}(z).$$
Conditional on `AWSInputs Q` only. -/
@[kb "hanke2011aws" "§4.6, (4.35)-(4.37), p. 66"]
theorem thetaLift_classical_uncond (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef) (I : AWSInputs Q)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
      dosetIntegral (ratPoints Q.hessian) (KA Q.hessian) (haarOA Q.hessian hH) α
        (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian I.gluing (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z :=
  thetaLift_classical Q
    (quotientIntegralInputsOA Q.hessian hH α hcov hdisj fun i => I.finite_aut (α i)) I α hα hcov hdisj j z

/-- **D24 (with D23), unconditional in the quotient integral**: version of `thetaLift_one` for the
constructed integral (Haar measure `haarOA`), for $Q$ positive definite:
$$y^{-n/4}\int_{O(V)\backslash O(V_\mathbb{A})}\theta(g_{\infty,z},h)\,dh
= \sum_{j}\frac{\Theta_{L_j}(z)}{|\mathrm{Aut}(L_j)|}.$$
Conditional on `AWSInputs Q` only. -/
@[kb "hanke2011aws" "§4.5-§4.6, pp. 62-66"]
theorem thetaLift_one_uncond (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef) (I : AWSInputs Q)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
      dosetIntegral (ratPoints Q.hessian) (KA Q.hessian) (haarOA Q.hessian hH) α (thetaKernel Q z) =
      ∑ j, (Nat.card (autLat Q.hessian (latSMul Q.hessian I.gluing (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z :=
  thetaLift_one Q
    (quotientIntegralInputsOA Q.hessian hH α hcov hdisj fun i => I.finite_aut (α i)) I α hα hcov hdisj z

end QuadFormsKB.AWS
