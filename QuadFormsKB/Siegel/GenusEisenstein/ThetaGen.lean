/-
# The genus theta series as a modular form, and its constant terms

For $Q$ positive definite quaternary with Hessian $H$ and $N = |\det H|$ (a level of every form in the genus,
`isThetaLevel_natAbs_det_genus`):

* `thetaGenMF hQ`: $\Theta_{\mathrm{Gen}(Q)} = \mathrm{Mass}(Q)^{-1}\sum_{[Q']}|\mathrm{Aut}(Q')|^{-1}\Theta_{Q'}$ as a Mathlib
  `ModularForm (Gamma1 N) 2` (`thetaGenMF_apply`);
* `qExpansion_thetaGenMF_coeff`: its $q$-coefficients are the genus averages $r_{\mathrm{Gen}}(m)$ = `genusRepAvg Q m`;
* `cuspVal_thetaGenMF`: its constant term at $\gamma\infty$, $\gamma_{10} = c \ge 1$, is $M_A(\gamma_{00}, c)$ (`thetaMult`; the
  constant terms of the $\Theta_{Q'}$ agree, `SameGenus.thetaMult_eq`, and the weights sum to $1$);
* `thetaMult_two_eq`: $M_S(a, c) = -\frac{1}{4c^2\sqrt{\det S}}\,G_S(a, c)$ for $k = 2$.
-/
import QuadFormsKB.Siegel.GenusEisenstein.Construction
import QuadFormsKB.Siegel.Thm63Inputs
import QuadFormsKB.Siegel.ThetaCuspidal
import QuadFormsKB.Siegel.GenusFinite

open Complex Filter Topology ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

local notation "Γ₁" => CongruenceSubgroup.Gamma1

variable {Q : IntQF 4} (hQ : Q.PosDef)

/-- **$\Theta_{\mathrm{Gen}(Q)}$ as a modular form of weight 2 for $\Gamma_1(|\det H|)$.** -/
@[kb "hanke2004" "(4.5), p. 366 (genus theta series) [unverified]"]
noncomputable def thetaGenMF : ModularForm (Γ₁ Q.hessian.det.natAbs) 2 :=
  (mass Q)⁻¹ • ∑ c ∈ (genusFinite hQ).finite_classes.toFinset.attach, ((c.1.autCard : ℝ))⁻¹ •
    thetaMFGamma1 ((sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp c.2)).posDef hQ) (k := 2) rfl
      (natAbs_det_pos hQ)
      (isThetaLevel_natAbs_det_genus hQ (by decide) _ (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp c.2)))

lemma modularForm_sum_apply' {N : ℕ} {ι : Type*} (s : Finset ι) (F : ι → ModularForm (Γ₁ N) 2) (τ : ℍ) :
    (∑ i ∈ s, F i) τ = ∑ i ∈ s, F i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem thetaGenMF_apply (τ : ℍ) : thetaGenMF hQ τ = thetaGen Q τ := by
  rw [thetaGenMF, thetaGen_eq_sum (genusFinite hQ)]
  simp only [IsSMulApply.smul_apply, real_smul]
  rw [modularForm_sum_apply']
  simp only [IsSMulApply.smul_apply, real_smul]
  push_cast
  congr 1
  rw [← Finset.sum_attach (genusFinite hQ).finite_classes.toFinset
    (fun c => ((c.autCard : ℂ))⁻¹ * theta c.out τ)]
  rfl

/-- **The $q$-coefficients of $\Theta_{\mathrm{Gen}(Q)}$ are the genus averages $r_{\mathrm{Gen}}(m)$.** -/
theorem qExpansion_thetaGenMF_coeff (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 (thetaGenMF hQ)).coeff m = (genusRepAvg Q m : ℂ) := by
  refine (ModularFormClass.qExpansion_coeff_unique (k := 2) (c := fun j => (genusRepAvg Q j : ℂ)) one_pos
    (one_mem_strictPeriods_Gamma1 _) (f := thetaGenMF hQ) (fun τ => ?_) m).symm
  rw [thetaGenMF_apply]
  convert hasSum_thetaGen hQ (genusFinite hQ) (z := (τ : ℂ)) τ.im_pos using 2 with j
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- **The constant term of $\Theta_{\mathrm{Gen}(Q)}$ at $\gamma\infty$** ($\gamma_{10} = c \ge 1$): $M_A(\gamma_{00}, c)$. -/
theorem cuspVal_thetaGenMF {γ : SL(2, ℤ)} {c : ℕ} [NeZero c] (hc : γ 1 0 = c) :
    haveI : NeZero Q.hessian.det.natAbs := ⟨(natAbs_det_pos hQ).ne'⟩
    cuspVal (thetaGenMF hQ) γ = thetaMult (gramMatrix Q) 2 (γ 0 0) c := by
  have : NeZero Q.hessian.det.natAbs := ⟨(natAbs_det_pos hQ).ne'⟩
  have hF := genusFinite hQ
  apply cuspVal_eq_of_tendsto
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * (c : ℤ) = 1 := by rw [← hc]; exact det_SL' γ
  set T := hF.finite_classes.toFinset
  have hlim : Tendsto (fun τ : ℍ => (((mass Q)⁻¹ : ℝ) : ℂ) * ∑ q ∈ T, (((q.autCard : ℝ))⁻¹ : ℂ) *
      (theta q.out ((γ 0 0 * τ + γ 0 1) / (c * τ + γ 1 1)) * (((c * τ + γ 1 1 : ℂ)) ^ 2)⁻¹))
      UpperHalfPlane.atImInfty (𝓝 ((((mass Q)⁻¹ : ℝ) : ℂ) * ∑ q ∈ T, (((q.autCard : ℝ))⁻¹ : ℂ) *
        thetaMult (gramMatrix Q) 2 (γ 0 0) c)) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun q hq => tendsto_const_nhds.mul ?_)
    have hg := sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hq)
    rw [hg.thetaMult_eq hQ 2 (γ 0 0) c]
    exact tendsto_theta_cusp (hg.posDef hQ) (k := 2) rfl hdet
  have hval : (((mass Q)⁻¹ : ℝ) : ℂ) * ∑ q ∈ T, (((q.autCard : ℝ))⁻¹ : ℂ) *
      thetaMult (gramMatrix Q) 2 (γ 0 0) c = thetaMult (gramMatrix Q) 2 (γ 0 0) c := by
    rw [← Finset.sum_mul, sum_autCard_inv hF, ← mul_assoc]
    have hm : ((mass Q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mass_pos hQ hF).ne'
    push_cast
    rw [inv_mul_cancel₀ hm, one_mul]
  rw [hval] at hlim
  refine hlim.congr fun τ => ?_
  rw [ModularForm.SL_slash_apply, thetaGenMF_apply, thetaGen_eq_sum hF, ModularGroup.denom_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, hc]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  rw [zpow_neg, zpow_two, sq]
  ring

/-- $M_S(a, c) = -\dfrac{1}{4c^2\sqrt{\det S}}\,G_S(a, c)$ in weight $k = 2$. -/
theorem thetaMult_two_eq (S : Matrix (Fin 4) (Fin 4) ℝ) (a : ℤ) (c : ℕ) [NeZero c] :
    thetaMult S 2 a c = -(1 / (4 * (c : ℂ) ^ 2 * Real.sqrt S.det)) * gaussSum S a c 0 := by
  unfold thetaMult
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  rw [div_pow, neg_pow_two, Complex.I_sq, mul_pow]
  push_cast
  by_cases hs : Real.sqrt S.det = 0
  · simp [hs]
  · field_simp
    ring

end QuadFormsKB.Siegel.GenusEis
