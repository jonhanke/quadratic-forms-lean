/-
# Hanke, AWS 2009 notes, §4.6: the theta lift for positive definite $Q$, with no inputs

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §4.5–§4.6 (pp. 61–66).
The theta-lift results D23–D24 (`AWS/ThetaLift.lean`) are stated relative to two inputs:
* `QuotientIntegralInputs` (the integral over $O(V)\backslash O(V_\mathbb{A})$ with Weil's formula),
  constructed in `AWS/HaarAdelic.lean` for $H$ positive definite over $\mathbb{R}$ (`quotientIntegralInputsOA`,
  for the Haar measure `haarOA` with $\mathrm{vol}(K_\mathbb{A}) = 1$), given finite stabilizers
  $O(V)\cap\alpha_iK_\mathbb{A}\alpha_i^{-1}$;
* `AWSInputs Q` (Lemma 4.5.1, finiteness of the class set and of every $\mathrm{Aut}(L_i)$), proved for positive
  definite $Q$ in `AWS/Finiteness.lean` (`awsInputs_of_posDef`, `finite_aut_of_posDef`).

This file combines the two: for $Q$ positive definite (the Hessian $H$ of $Q$ positive definite over
$\mathbb{R}$, hypothesis `hH`) the four statements below take **neither** input as a hypothesis. They are
stated for the constructed integral `dosetIntegral` with the Haar measure `haarOA`; by
`quotientIntegral_eq_dosetIntegral` (`AWS/ThetaLiftUncond.lean`) every integral satisfying Weil's formula agrees
with it on left-$O(V)$-invariant functions. The remaining hypotheses `hα`, `hcov`, `hdisj` (a finite family of
representatives of $O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A}$ with trivial archimedean components) describe the
setting and can always be met (`exists_doset_reps`).

* `thetaLift_indicator_eq_posDef_uncond` (D23, (4.4)–(4.34));
* `thetaLift_classical_posDef_uncond` (D23, (4.35)–(4.37));
* `thetaLift_one_posDef_uncond` (D24 with D23);
* `integral_one_eq_mass_posDef_uncond` (D24: $\mathrm{vol}(O(V)\backslash O(V_\mathbb{A})) = \sum_i 1/|\mathrm{Aut}(L_i)|$).

`evalIn_pos_of_posDef` converts `hH` to the hypothesis of `AWS/Finiteness.lean`
($Q(\vec x) > 0$ for $\vec x \in \mathbb{Q}^n \setminus \{0\}$).
-/
import QuadFormsKB.Literature.AWS.Finiteness
import QuadFormsKB.Literature.AWS.ThetaLiftUncond

open Matrix MeasureTheory Complex Real
open scoped Pointwise UpperHalfPlane

namespace QuadFormsKB.AWS

variable {n : ℕ} (Q : QuadForm ℚ n)

variable {Q} in
/-- **Positive definite over $\mathbb{R}$ implies positive on $\mathbb{Q}^n$:** if the Hessian $H$ of $Q$ is positive
definite over $\mathbb{R}$, then $Q(\vec x) > 0$ for every $\vec x \in \mathbb{Q}^n \setminus \{0\}$ (since
$\vec x^{\mathsf T}H\vec x = 2Q(\vec x)$). -/
theorem evalIn_pos_of_posDef (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef) :
    ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x := by
  intro x hx
  have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
    intro h
    apply hx
    funext i
    simpa using congrFun h i
  have h := hH.dotProduct_mulVec_pos hx'
  have key : star (fun i => (x i : ℝ)) ⬝ᵥ (Q.hessian.map (algebraMap ℚ ℝ) *ᵥ fun i => (x i : ℝ)) =
      ((x ⬝ᵥ (Q.hessian *ᵥ x) : ℚ) : ℝ) := by
    simp [dotProduct, mulVec, Matrix.map_apply]
  rw [key, dot_hessian_self_rat] at h
  have h2 : (0 : ℚ) < 2 * Q.evalIn ℚ x := by exact_mod_cast h
  linarith

/-- **D23: (4.4)–(4.34), pp. 63–66, for positive definite $Q$, with no inputs:** `thetaLift_indicator_eq_uncond`
with `AWSInputs Q` discharged (`awsInputs_of_posDef`). For the integral over $O(V)\backslash O(V_\mathbb{A})$
constructed from the Haar measure `haarOA` ($\mathrm{vol}(K_\mathbb{A}) = 1$), representatives $\alpha_i$ of the
double cosets with $\alpha_{i,\infty} = 1$, $L_j = \alpha_j\mathbb{Z}^n$ and $z = x + iy \in \mathbb{H}$:
$$\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,y^{n/4}\,\Theta_{L_j}(z).$$ -/
@[kb "hanke2011aws" "§4.6, (4.4)-(4.34), pp. 63-66"]
theorem thetaLift_indicator_eq_posDef_uncond (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    dosetIntegral (ratPoints Q.hessian) (KA Q.hessian) (haarOA Q.hessian hH) α
        (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α j) stdLat)) : ℂ)⁻¹ *
        (((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) *
          thetaSeries Q (latSMul Q.hessian (latticeGluing n) (α j) stdLat) z) :=
  thetaLift_indicator_eq_uncond Q hH (awsInputs_of_posDef (evalIn_pos_of_posDef hH)) α hα hcov hdisj j z

/-- **D23, (4.35)–(4.37), p. 66, for positive definite $Q$, with no inputs:** `thetaLift_classical_uncond` with
`AWSInputs Q` discharged (`awsInputs_of_posDef`), for the constructed integral (Haar measure `haarOA`):
$$y^{-n/4}\,\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,\Theta_{L_j}(z).$$ -/
@[kb "hanke2011aws" "§4.6, (4.35)-(4.37), p. 66"]
theorem thetaLift_classical_posDef_uncond (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
      dosetIntegral (ratPoints Q.hessian) (KA Q.hessian) (haarOA Q.hessian hH) α
        (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian (latticeGluing n) (α j) stdLat) z :=
  thetaLift_classical_uncond Q hH (awsInputs_of_posDef (evalIn_pos_of_posDef hH)) α hα hcov hdisj j z

/-- **D24 (with D23), for positive definite $Q$, with no inputs:** `thetaLift_one_uncond` with `AWSInputs Q`
discharged (`awsInputs_of_posDef`), for the constructed integral (Haar measure `haarOA`): the theta lift of the
constant function $1$ is the mass-weighted genus theta series,
$$y^{-n/4}\int_{O(V)\backslash O(V_\mathbb{A})}\theta(g_{\infty,z},h)\,dh
= \sum_{j \in I}\frac{\Theta_{L_j}(z)}{|\mathrm{Aut}(L_j)|}.$$ -/
@[kb "hanke2011aws" "§4.5-§4.6, pp. 62-66"]
theorem thetaLift_one_posDef_uncond (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
      dosetIntegral (ratPoints Q.hessian) (KA Q.hessian) (haarOA Q.hessian hH) α (thetaKernel Q z) =
      ∑ j, (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian (latticeGluing n) (α j) stdLat) z :=
  thetaLift_one_uncond Q hH (awsInputs_of_posDef (evalIn_pos_of_posDef hH)) α hα hcov hdisj z

/-- **D24 (p. 62 with §2.6), for positive definite $Q$, with no inputs: the volume of
$O(V)\backslash O(V_\mathbb{A})$ is the mass.** For the constructed integral (Haar measure `haarOA`,
$\mathrm{vol}(K_\mathbb{A}) = 1$) and representatives $\alpha_i$ of the double cosets $O(V)\alpha_iK_\mathbb{A}$,
with $L_i = \alpha_i\mathbb{Z}^n$:
$$\int_{O(V)\backslash O(V_\mathbb{A})} 1\,dh = \sum_{i \in I}\frac{1}{|\mathrm{Aut}(L_i)|}.$$
The finiteness of the stabilizers is `finite_aut_of_posDef`; `integral_one_eq_mass_posDef` gives the formula. -/
@[kb "hanke2011aws" "§4.6 with §2.6, p. 34"]
theorem integral_one_eq_mass_posDef_uncond (hH : (Q.hessian.map (algebraMap ℚ ℝ)).PosDef)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j) :
    dosetIntegral (ratPoints Q.hessian) (KA Q.hessian) (haarOA Q.hessian hH) α (fun _ => 1) =
      ∑ i, (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α i) stdLat)) : ℂ)⁻¹ :=
  integral_one_eq_mass_posDef Q (evalIn_pos_of_posDef hH)
    (quotientIntegralInputsOA Q.hessian hH α hcov hdisj fun i =>
      finite_aut_of_posDef (evalIn_pos_of_posDef hH) (α i)) α hcov hdisj

end QuadFormsKB.AWS
