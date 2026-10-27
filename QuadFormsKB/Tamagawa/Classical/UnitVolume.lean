/-
# The unit volumes of an anisotropic binary form: $\sum_iv(M_i)$ via $L(1,\chi_E)$

**Layer:** number fields.

$F$ a number field, $Q_0$ a nondegenerate binary form over $\mathcal O_F$, anisotropic over $F$, $E$ its discriminant field
(`IsDiscField`), $\chi_E$ = `chiE F E`, $\lambda_v = 1-\chi_E(v)/Nv$ = `lamL (chiE F E) v`, $\alpha_v(L,L)$ =
`NF.siegelDensity v Q₀ Q₀`, $v(M_i)$ = `unitVolume` (the covolume of the unit group of the class $M_i$ in
$SO(V)(F_\infty)$; for indefinite $Q_0$ over $\mathbb Q$ the unit group is infinite cyclic up to sign and $v(M_i)$ carries its
regulator). Weil's $\tau(SO(V)) = 2$ (`tauTwoBinaryAll_uncond`) reads
$$\sum_iv(M_i) = \frac{2\,L(1,\chi_E)}{\prod_v\alpha_v(L,L)/\lambda_v}\qquad(\texttt{tsum\_unitVolume\_binary}),$$
the product having almost all factors equal to $1$, and with $L(1,\chi_E) = \rho_E/\rho_F$ (`lOne_chiE_eq`) and Mathlib's
residue $\rho_K = 2^{r_1}(2\pi)^{r_2}h_KR_K/(w_K\sqrt{|d_K|})$ (`dedekindZeta_residue_def`) every constant is explicit
(**`unitVolume_sum_binary`**: class numbers, regulators, numbers of roots of unity, discriminants of $E$ and $F$).
Unconditional.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne

open MeasureTheory
open scoped ENNReal Real

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil LocalDensity QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F]

/-- **The unit volumes of an anisotropic binary form** (every number field $F$, any signature):
$$\sum_iv(M_i) = \frac{2\,L(1,\chi_E)}{\prod_v\alpha_v(L,L)\,(1-\chi_E(v)/Nv)^{-1}},$$
$\alpha_v(L,L)$ = `NF.siegelDensity v Q₀ Q₀`, $1-\chi_E(v)/Nv$ = `lamL (chiE F E) v` (the factors are $1$ for almost all $v$,
`eventually_muLocSO_lamL_chiE`), and the product is positive. This is Weil's $\tau(SO(V)) = 2$
(`tauTwoBinaryAll_uncond`). -/
theorem tsum_unitVolume_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E) :
    0 < ∏' v, NF.siegelDensity v Q₀ Q₀ / lamL (chiE F E) v ∧
      ∑' i, unitVolume Q₀ hQ i =
        ENNReal.ofReal (2 * LOne (chiE F E) / ∏' v, NF.siegelDensity v Q₀ Q₀ / lamL (chiE F E) v) := by
  set lam := lamL (chiE F E) with hlamdef
  have hlam : ∀ v, 0 < lam v := lamL_pos (abs_chiE_le hE.finrank_eq_two)
  obtain ⟨hL, -⟩ := lOne_chiE (F := F) (E := E) hE.finrank_eq_two
  obtain ⟨S, hS⟩ := eventually_muLocSO_lamL_chiE Q₀ hQ hE
  have haS : ∀ v ∉ S, aSO Q₀ v / lam v = 1 := by
    intro v hv
    have h := hS v hv
    have h0 : 0 ≤ NF.siegelDensity v Q₀ Q₀ / lam v :=
      div_nonneg (siegelDensity_self_pos' Q₀ hQ v).le (hlam v).le
    rw [muLocSO_soStabSO, ← ENNReal.ofReal_one] at h
    rw [aSO_eq_siegelDensity Q₀ hQ v]
    exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).mp h
  have hafin : (Function.mulSupport fun v => aSO Q₀ v / lam v).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (haS v h)
  have hApos : 0 < ∏' v, aSO Q₀ v / lam v := by
    rw [tprod_eq_prod (s := hafin.toFinset) (fun v hv => by
      by_contra hne; exact hv (hafin.mem_toFinset.2 hne))]
    exact Finset.prod_pos fun v _ => div_pos (aSO_pos Q₀ hQ v) (hlam v)
  have hsd : ∀ v, aSO Q₀ v / lam v = NF.siegelDensity v Q₀ Q₀ / lam v := fun v => by
    rw [aSO_eq_siegelDensity Q₀ hQ v]
  simp_rw [hsd] at hApos
  refine ⟨hApos, ?_⟩
  set a := ∏' v, NF.siegelDensity v Q₀ Q₀ / lam v with ha
  set A := ENNReal.ofReal a with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := ∑' i, unitVolume Q₀ hQ i with hV
  have hτ : ENNReal.ofReal (LOne (chiE F E))⁻¹ * (A * V) = 2 := by
    have h := tauTwoBinaryAll_uncond F Q₀ hQ hA E hE
    rw [muTamBin, muTamChi, covolume_smul_muTam, covolume_muTam_eq_muFin_mul, muFin_KSO,
      finFactor_eq_tprod_aSO Q₀ hQ hlam] at h
    simp_rw [hsd] at h
    exact h
  have hAV : A * V = ENNReal.ofReal (2 * LOne (chiE F E)) := by
    rw [ENNReal.ofReal_inv_of_pos hL] at hτ
    have hL0 : ENNReal.ofReal (LOne (chiE F E)) ≠ 0 := (ENNReal.ofReal_pos.2 hL).ne'
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    calc A * V = (ENNReal.ofReal (LOne (chiE F E)))⁻¹ * (A * V) * ENNReal.ofReal (LOne (chiE F E)) := by
          rw [mul_comm _ (A * V), mul_assoc, ENNReal.inv_mul_cancel hL0 ENNReal.ofReal_ne_top, mul_one]
      _ = 2 * ENNReal.ofReal (LOne (chiE F E)) := by rw [hτ]
  rw [ENNReal.ofReal_div_of_pos hApos, ← hAV, mul_comm, ENNReal.mul_div_cancel_right hA0 hAt]

/-- **The unit volumes of an anisotropic binary form, every constant explicit** (Weil's $\tau(SO(V)) = 2$ with
Dirichlet's and Dedekind's class number formula; every number field $F$, any signature): for $Q_0$ a nondegenerate binary
form over $\mathcal O_F$, anisotropic over $F$, with discriminant field $E = F(\sqrt{-\det H_{Q_0}})$,
$$\sum_iv(M_i) = \frac{2\,\rho_E/\rho_F}{\prod_v\alpha_v(L,L)\,(1-\chi_E(v)/Nv)^{-1}},\qquad
  \rho_K = \frac{2^{r_1(K)}(2\pi)^{r_2(K)}\,R_K\,h_K}{w_K\sqrt{|d_K|}},$$
$h_K$ = `classNumber K`, $R_K$ = `regulator K` (the units), $w_K$ = `torsionOrder K` (the roots of unity), $d_K$ = `discr K`,
$r_1, r_2$ the numbers of real and complex places; $v(M_i)$ = `unitVolume` (the covolume of the unit group $SO(M_i)$ in
$SO(V)(F_\infty)$), $\alpha_v(L,L)$ = `NF.siegelDensity v Q₀ Q₀`, $\chi_E$ = `chiE F E`. Unconditional. -/
@[kb "weil1982" "§2.4 and Ch. IV (τ(SO_2) = 2 for anisotropic binary forms; convergence factors L_v(1, χ_E)) [unverified]"]
theorem unitVolume_sum_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E) :
    ∑' i, unitVolume Q₀ hQ i =
      ENNReal.ofReal (2 * (2 ^ nrRealPlaces E * (2 * π) ^ nrComplexPlaces E * Units.regulator E * classNumber E /
          (Units.torsionOrder E * Real.sqrt |(discr E : ℝ)|)) /
        (2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F * classNumber F /
          (Units.torsionOrder F * Real.sqrt |(discr F : ℝ)|)) /
        ∏' v, NF.siegelDensity v Q₀ Q₀ / lamL (chiE F E) v) := by
  rw [(tsum_unitVolume_binary Q₀ hQ hA E hE).2, lOne_chiE_eq hE.finrank_eq_two, dedekindZeta_residue_def,
    dedekindZeta_residue_def]
  congr 1
  ring

end QuadFormsKB.Tamagawa.Classical
