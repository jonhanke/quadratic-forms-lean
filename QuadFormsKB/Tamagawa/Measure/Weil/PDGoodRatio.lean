import QuadFormsKB.Tamagawa.Measure.LerayPadic
import QuadFormsKB.Tamagawa.Measure.Weil.PDMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.QuatTamagawa

/-!
# The good-place local ratios $r_v = 1$ for $PD^\times \cong SO(D^0)$

$F$ a number field, $a, b \in \mathcal O_F\setminus0$, $D = \mathbb H[F,a,b]$, $Q_0$ = `QuatZeta.pureFormO a b`
$= \langle -a,-b,ab\rangle$ (the norm form on $D^0$). `covolume_pd_eq_covolume_muTam` needs local ratios $r_v$
between Weil's quotient measure on $PD^\times(F_v) = D_v^\times/F_v^\times$ and `muLocSO v Q₀ 1` with
$\prod_v r_v = 1$. At a good place ($v \nmid 2ab$, $\mathrm{vol}(\mathfrak o_v) = 1$) the image of $\Lambda_v^\times$ is
$SO(L_v)$ (`exists_smul_mem_lamLocUnits`, `conjOrth_mem_stdStab`), the quotient measure gives it
$\lambda_v^{-1}\omega_v(\Lambda_v^\times)/\lambda_v^{-1}\omega_v(\mathfrak o_v^\times) = $ `quatLocalFactor a b v`
$/ 1$, and the gauge-form volume is $\mu_v(SO(L_v)) = 1 - q^{-2}$ (`muLocSO_soStabSO_ternary`). So:

* **`eventually_muLocSO_soStabSO_eq_quatLocalFactor`**: for all but finitely many $v$,
  $\mu_v(SO(L_v)) = \lambda_v^{-1}\omega_v(\Lambda_v^\times)$, i.e. $r_v = 1$.

The bad places and $\infty$ (where $r_v = |c|_v$ by Weil's Thm 2.3.1) are not done.
-/

open IsDedekindDomain NumberField MeasureTheory Filter
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.QuatZeta QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-- Only finitely many primes contain a nonzero $x \in \mathcal O_F$. -/
theorem finite_setOf_mem_asIdeal {x : 𝓞 F} (hx : x ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {x}) (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx)).subset
    fun _ hv => Ideal.dvd_span_singleton.2 hv

/-- Elements of $\mathcal O_F$ are integral at every finite place. -/
theorem valued_algebraMap_le_one (x : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap F (v.adicCompletion F) (x : F)) ≤ 1 := by
  have hval : Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = v.valuation F (x : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [hval, show (x : F) = algebraMap (𝓞 F) F x from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_le_one x

/-- **The good-place local ratios are $1$** (the gap, item 2, at almost every place): for all but finitely many
finite places $v$,
$$\mu_v(SO(L_v)) = \lambda_v^{-1}\omega_v(\Lambda_v^\times) = 1 - N(v)^{-2},$$
where $\mu_v$ = `muLocSO v Q₀ 1` is the gauge-form measure on $SO(D^0)(F_v)$ (`LerayPadic.lerayApprox_eventually_eq`),
$L = \mathcal O_F^3$ with the form $\langle -a,-b,ab\rangle$, and $\lambda_v^{-1}\omega_v(\Lambda_v^\times)$ = `quatLocalFactor`
($\Lambda = \mathcal O_F\langle1,i,j,k\rangle$). Proof: `muLocSO_soStabSO_ternary` ($v \nmid 2\det H_{Q_0}$) and
`quatLocalFactor_good`. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratios of gauge-form measures) [unverified]"]
theorem eventually_muLocSO_soStabSO_eq_quatLocalFactor (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Measure.muLocSO v (pureFormO a b) 1 (Measure.soStabSO v (pureFormO a b) : Set (Measure.SOv v (pureFormO a b))) =
        ENNReal.ofReal (quatLocalFactor (a : F) (b : F) v) := by
  have ha0 : (a : F) ≠ 0 := by exact_mod_cast ha
  have hb0 : (b : F) ≠ 0 := by exact_mod_cast hb
  have hdet0 : (pureFormO a b).hessian.det ≠ 0 := nondegenerate_pureFormO a b ha hb
  have h2fin := (finite_setOf_mem_asIdeal (two_ne_zero : (2 : 𝓞 F) ≠ 0)).compl_mem_cofinite
  have hdfin := (finite_setOf_mem_asIdeal hdet0).compl_mem_cofinite
  filter_upwards [quatLocalFactor_good (fun v => valued_algebraMap_le_one a v) (fun v => valued_algebraMap_le_one b v)
    ha0 hb0, h2fin, hdfin] with v h1 h2 h3
  have hπ2 : ¬ NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    rw [show (2 : v.adicCompletionIntegers F) = NF.ι v 2 from (map_ofNat _ 2).symm, NF.π_dvd_ι_iff]; exact h2
  have hπd : ¬ NF.π v ∣ (NF.Qp v (pureFormO a b)).hessian.det := by
    rw [NF.det_hessian_Qp, NF.π_dvd_ι_iff]; exact h3
  rw [LerayPadic.muLocSO_soStabSO_ternary v _ hπ2 hπd, h1, NF.q_completion]

end QuadFormsKB.Tamagawa.Measure.Weil
