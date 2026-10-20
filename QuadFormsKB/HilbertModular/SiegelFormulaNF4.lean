/-
# Siegel's formula over a totally real field for quaternary forms ($n = 4$, weight 2)

**Setting.** $F$ totally real of degree $d = [F:\mathbb Q] \ge 2$ with $\mathcal O_F$ a PID (`[IsPrincipalIdealRing (𝓞 F)]`), $Q_0$ a totally
positive definite quadratic form over $\mathcal O_F$ in $n = 4$ variables, $L = \mathcal O_F^4$, its genus classes $\mathrm{cls}(M)$,
$|O(M)|$ = `LatClass.autCard`, $r_M(\nu)$ = `latRepF`, $\mathrm{Mass}(L)$ = `mass`, $\beta_\infty = \prod_w\beta_w$ (Lebesgue measure at each real place),
$\beta_\mathfrak p$ = `LocalDensity.NF.localDensity` ($\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$), $\mathrm{aENF} = \beta_\infty\prod_\mathfrak p\beta_\mathfrak p$.

**Main theorem** (`siegelFormula_nf_four`): for $\nu \in \mathcal O_F$ totally positive,
$$\frac1{\mathrm{Mass}(L)}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(\nu)}{|O(M)|} = |d_F|^{-3/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu).$$
Together with `siegelFormula_nf` ($n \ge 6$) this is `siegelFormula_nf_of_two_le`: Siegel's formula over $F$ for every even
$n = 2k \ge 4$ ($d \ge 2$ when $k = 2$). Also `siegelFormulaAt_of_pid_four` (the input `SiegelFormulaAt` for $n = 4$).

**Convention for the conditionally convergent objects.** $\prod_\mathfrak p\beta_\mathfrak p(\nu)$ converges absolutely for $n = 4$
(`Siegel.multipliable_eulerFactorNF`) and is the unconditional product (`tprod`). The singular series is **not** absolutely convergent over
$u \in F/\mathcal O$ for $n = 4$; it is summed grouped by denominators (the rows $(C, t)$ of `SingularNF.ssPart`), where it converges
absolutely (`qCoeff_eisQ2_eq`), and its value is identified through the truncations $S_{(X!)^E}$ (`SingularNF.tsum_ssPart_eq`).

**Proof.** `Cuspidal2.lean` and `SiegelHecke.lean` give $\theta_{\mathrm{Gen}} = E_Q$ once `EisHeckeRel Q₀ (eisQ2 …)` holds (`qCoeff_eisQ2_eq_genus_avg`). Its coefficients:
* `eisQ2_coeff_eq_discr_mul_aENF`: $a_\nu(E_Q) = |d_F|^{-3/2}\mathrm{aENF}(\nu)$ for $\nu \gg 0$ in $\mathcal O_F$ (`qCoeff_eisQ2_eq`, `tsum_ssPart_eq`,
  The archimedean constant `eisArch_eq`, which covers $k = 2$);
* `eisQ2_coeff_eq_zero_of_not_int`, `eisQ2_coeff_eq_zero_of_not_pos`: $a_\mu(E_Q) = 0$ for $\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$ or $\mu \not\gg 0$;
* **`eisHeckeRel_eisQ2`**: the $T(\pi^2)$ relations, prime by prime from these and `aENF_mul_pi_sq` (valid for $k = 2$).

**Cross-check with $\mathbb Q$.** Over $\mathbb Q$ the quaternary case is `Siegel.GenusEis.siegelFormula_quaternary`: `genusRepAvg Q m = aE Q m`
for $m \ge 1$, i.e. the same genus average equals $\beta_\infty(m)\prod_p\beta_p(m)$. `siegelFormula_nf_four` has the same shape with the factor
$|d_F|^{-(n-1)/2} = |d_F|^{-3/2}$, which is $1$ over $\mathbb Q$ (`discrFactor_rat`). The proofs are parallel: Möbius-inverted Eisenstein
series of the cusp constants (`GenusEis.hasSum_eisQCoeff` ↔ `qCoeff_eisGen2`), the singular series identified prime by prime
(`hasSum_ssTerm` ↔ `tsum_ssPart_eq`), and the Hecke/Kneser vanishing argument. The scope differs: over $\mathbb Q$ ($d = 1$) the weight-2
series needs Hecke's non-holomorphic correction, which vanishes for $d \ge 2$; hence $d \ge 2$ here.

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), Hauptsatz [unverified]; Siegel, Ann.
Math. 38 (1937) [unverified]; Hecke (1927) [unverified]; Shimura, Duke Math. J. 45 (1978), §3 [unverified]; Hanke 2004, (5.3), p. 368
(with the corrected constant).
-/
import QuadFormsKB.HilbertModular.EisensteinQ2Coeff
import QuadFormsKB.HilbertModular.SteinitzGenus

open Complex NumberField
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### The coefficients of $E_Q$ in weight 2 -/

section Coeff

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hfree : GenusFree (formF Q₀) stdLat)
  (hd : 2 ≤ Fintype.card (InfinitePlace F))

lemma lipCoeff_two_ne_zero {μ : F} (hμ : ∀ v, 0 < realEmb F v μ) : lipCoeff 2 (realVec μ) ≠ 0 := by
  rw [lipCoeff, if_pos (show ∀ v, 0 < realVec μ v from hμ)]
  refine mul_ne_zero (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ ?_) (by simp)))
    (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hμ v).ne'))
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

include hQ hn hlev h𝔑 hfree hd in
/-- **Siegel's formula for the coefficients of $E_Q$ in weight 2** ($n = 4$, $d \ge 2$, free genus): for $\nu \in \mathcal O_F$ totally positive,
$$a_\nu(E_Q) = |d_F|^{-3/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu) = |d_F|^{-3/2}\,\texttt{aENF}\ Q_0\ \nu.$$
The $n = 4$ case of `eisQ_coeff_eq_discr_mul_aENF`: the coefficient is $C_Qc_{\mathcal O}\Lambda_2(\nu)$ times the singular series
grouped by denominators (`qCoeff_eisQ2_eq`), which is $|d_F|\prod_\mathfrak p\beta_\mathfrak p(\nu)$ (`SingularNF.tsum_ssPart_eq`). -/
@[kb "hanke2004" "(5.3), p. 368, over F, n = 4: a_E(ν) = |d_F|^{-3/2} ∏_v β_v(ν) (weight 2, corrected constant) [unverified]"]
theorem eisQ2_coeff_eq_discr_mul_aENF {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (ιO ν)) =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν : ℝ) : ℂ) := by
  have hQ' := isTotPosGram_Q₀ hQ
  have hQnd : Q₀.Nondegenerate := det_hessian_ne_zero hQ'
  have hν0 : ν ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    simpa using hν v
  obtain ⟨m, hm⟩ := exists_oDual_eq (algebraMap_mem_invDifferent ν)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [oDual_zero] at hm
    exact hν0 (by simpa using hm.symm)
  obtain ⟨hsum, hq⟩ := qCoeff_eisQ2_eq hQ hn hlev h𝔑 hfree hd hm0
  rw [hm] at hsum hq
  have hss := SiegelWeil.SingularNF.tsum_ssPart_eq Q₀ hQnd (by omega) hν0 (hsum (lipCoeff_two_ne_zero hν))
    (QuadFormsKB.Siegel.multipliable_eulerFactorNF hQnd (by omega) (QuadFormsKB.Siegel.hshape_NF Q₀) hν0)
  rw [hq, eisArch_eq hQ' (by norm_num) hn hν, hss]
  have hd' := discr_pos (F := F)
  have hs : Real.sqrt (discr F : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hd').ne'
  have hN : (((discr F).natAbs : ℕ) : ℝ) = Real.sqrt (discr F : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Real.sq_sqrt hd'.le, abs_of_pos hd']
  rw [abs_of_pos hd', QuadFormsKB.Siegel.aENF, QuadFormsKB.Siegel.aEWithNF, QuadFormsKB.Siegel.eulerProductNF, hN]
  push_cast
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hs' : (Real.sqrt (discr F : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  simp only [QuadFormsKB.Siegel.eulerFactorNF]
  have key : (Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ (j + 1 + 1) =
      ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ j := by
    have h1 : (Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hs', one_pow]
    calc (Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ (j + 1 + 1)
        = ((Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ 2) *
            ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ j := by ring
      _ = ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ j := by rw [h1, one_mul]
  linear_combination ((QuadFormsKB.Siegel.betaInfNF Q₀ (ιO ν) : ℂ) *
    ((∏' v, LocalDensity.NF.localDensity v Q₀ ν : ℝ) : ℂ)) * key

include hQ hn hlev h𝔑 hfree hd in
/-- **$a_\mu(E_Q) = 0$ for $\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$** (weight 2): the grouped singular series vanishes
(`SingularNF.tsum_ssPart_eq_zero_of_not_int`). -/
theorem eisQ2_coeff_eq_zero_of_not_int {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0)
    (hint : ¬ ∃ b : 𝓞 F, ιO b = oDual m) :
    qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (oDual m)) = 0 := by
  obtain ⟨hsum, hq⟩ := qCoeff_eisQ2_eq hQ hn hlev h𝔑 hfree hd hm
  rw [hq]
  by_cases hL : lipCoeff 2 (realVec (oDual m)) = 0
  · rw [hL, mul_zero, zero_mul]
  · rw [SiegelWeil.SingularNF.tsum_ssPart_eq_zero_of_not_int Q₀ (oDual_mem m) hint (hsum hL), mul_zero]

include hQ hn hlev h𝔑 hfree hd in
/-- **$a_\mu(E_Q) = 0$ for $\mu \not\gg 0$** (weight 2): $\Lambda_2(\mu) = 0$. -/
theorem eisQ2_coeff_eq_zero_of_not_pos {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0)
    (hpos : ¬ ∀ v, 0 < realEmb F v (oDual m)) :
    qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (oDual m)) = 0 := by
  rw [(qCoeff_eisQ2_eq hQ hn hlev h𝔑 hfree hd hm).2, lipCoeff_of_not_pos hpos, mul_zero, zero_mul]

include hQ hn hlev h𝔑 hfree hd in
/-- **The $T(\pi^2)$ relations for the weight-2 Eisenstein series of the genus** ($n = 4$, $d \ge 2$, free genus):
`EisHeckeRel Q₀ (eisQ2 Q₀ 𝔑 h𝔑)` with $m_E = 1$: for every prime $\pi \nmid 2\det H$ and every $\pi$-unit $\mu \in \mathfrak d^{-1}$,
$$a_{\pi^2\mu}(E_Q) = (q^2 + \chi_\pi q + 1)\,a_\mu(E_Q).$$
This was the last named input of the $n = 4$ case (`qCoeff_eisQ2_eq_genus_avg`). -/
@[kb "siegel1935" "T(𝔭²) relations for the weight-2 Eisenstein coefficients over F (n = 4) [unverified]"]
theorem eisHeckeRel_eisQ2 : EisHeckeRel Q₀ (eisQ2 Q₀ 𝔑 h𝔑) := by
  classical
  refine ⟨1, one_pos, fun π hπ _ h2 hdet m hu => ?_⟩
  have hπ0 := hπ.ne_zero
  have hQ' := isTotPosGram_Q₀ hQ
  have hQnd : Q₀.Nondegenerate := det_hessian_ne_zero hQ'
  obtain ⟨m', hm'⟩ := exists_dualElt_mul (π ^ 2) m
  have hm'' : (π : F) ^ 2 * oDual m = oDual m' := by rw [oDual, oDual, hm']; push_cast; rfl
  have hμ0 := ne_zero_of_isUnitAt hu
  have hm0 : m ≠ 0 := by rintro rfl; exact hμ0 oDual_zero
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    rw [oDual_zero] at hm''
    exact mul_ne_zero (pow_ne_zero 2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hπ0))
      hμ0 hm''
  change qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec ((π : F) ^ 2 * oDual m)) =
    heckeEigen Q₀ hπ * qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (oDual m))
  by_cases hint : ∃ ν : 𝓞 F, ιO ν = oDual m
  · obtain ⟨ν, hν⟩ := hint
    have hνπ : ¬ π ∣ ν := not_dvd_of_isUnitAt (by rw [hν]; exact hu)
    have hν0 : ν ≠ 0 := by rintro rfl; exact hμ0 (by rw [← oDual, ← hν, map_zero])
    have he : (π : F) ^ 2 * oDual m = ιO (ν * π ^ 2) := by rw [← hν, map_mul, map_pow]; ring
    by_cases hpos : ∀ v, 0 < realEmb F v (ιO ν)
    · have hpos' : ∀ v, 0 < realEmb F v (ιO (ν * π ^ 2)) := fun v => by
        rw [← he, realEmb_sq_mul_pos_iff hπ0, ← hν]; exact hpos v
      rw [he, ← hν, eisQ2_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 hfree hd hpos',
        eisQ2_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 hfree hd hpos,
        aENF_mul_pi_sq hQnd hn (le_refl 2) hπ h2 hdet hν0 hνπ
          (fun w => by obtain ⟨v, h⟩ := w; rw [siegel_realEmb_eq]; exact (hpos v).le), heckeEigen]
      push_cast
      ring
    · have hpos' : ¬ ∀ v, 0 < realEmb F v (oDual m') := by
        rw [← hm'']; intro h; exact hpos fun v => by rw [hν]; exact (realEmb_sq_mul_pos_iff hπ0 _ v).mp (h v)
      rw [hm'', eisQ2_coeff_eq_zero_of_not_pos hQ hn hlev h𝔑 hfree hd hm'0 hpos',
        eisQ2_coeff_eq_zero_of_not_pos hQ hn hlev h𝔑 hfree hd hm0 (by rw [← hν]; exact hpos), mul_zero]
  · have hint' : ¬ ∃ ν : 𝓞 F, ιO ν = oDual m' := by
      rintro ⟨ν', hν'⟩
      exact hint (mem_int_of_sq_mul' hπ hu (hν'.trans hm''.symm))
    rw [hm'', eisQ2_coeff_eq_zero_of_not_int hQ hn hlev h𝔑 hfree hd hm'0 hint',
      eisQ2_coeff_eq_zero_of_not_int hQ hn hlev h𝔑 hfree hd hm0 hint, mul_zero]

end Coeff

/-! ### The weight-2 inputs for every totally real $F$ (any class number)

The genus of $\mathcal O_F^4$ is free for every $F$ (`genusFree_formF`, Steinitz), so both inputs for $E = E_Q$ in weight 2 are theorems
without $h_F = 1$. (The vanishing step for $n = 4$ and $h_F > 1$ is not covered: `eq_zero_of_heckeRel'` needs $k \ge 3$.) -/

/-- **The $T(\pi^2)$ relations for the weight-2 Eisenstein series, every totally real $F$** ($n = 4$, $d \ge 2$, any class number):
`eisHeckeRel_eisQ2` with the genus free by `genusFree_formF`. -/
@[kb "siegel1935" "T(𝔭²) relations for the weight-2 Eisenstein coefficients over F, any class number (n = 4) [unverified]"]
theorem eisHeckeRel_eisQ2' {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    EisHeckeRel Q₀ (eisQ2 Q₀ 𝔑 h𝔑) :=
  eisHeckeRel_eisQ2 hQ hn hlev h𝔑 (genusFree_formF hQ) hd

/-- **The weight-2 input `ThetaGenSubCusp2` for $E = E_Q$, every totally real $F$** ($n = 4$, $d \ge 2$, any class number; via
`thetaGen_sub_eisQ2_mem_cuspFormChar'`). -/
@[kb "siegel1935" "θ_Gen − E_Q ∈ S₂ discharges ThetaGenSubCusp2, any class number [unverified]"]
theorem thetaGenSubCusp2_eisQ2' {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    ThetaGenSubCusp2 Q₀ (eisQ2 Q₀ 𝔑 h𝔑) 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) :=
  thetaGen_sub_eisQ2_mem_cuspFormChar' hQ hlev h𝔑 hn hd

/-! ### Siegel's formula for $n = 4$ -/

variable [IsPrincipalIdealRing (𝓞 F)]

/-- **Class number one: $a_\nu(E_Q) = |d_F|^{-3/2}\,\mathrm{aENF}(\nu)$ in weight 2 with no freeness hypothesis** ($\mathcal O_F$ a PID, $n = 4$,
$d \ge 2$, $\nu \in \mathcal O_F$ totally positive). -/
@[kb "hanke2004" "(5.3), p. 368, over F, n = 4, h_F = 1: a_E(ν) = |d_F|^{-3/2} ∏_v β_v(ν) (weight 2) [unverified]"]
theorem eisQ2_coeff_eq_discr_mul_aENF_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀))
    (hn : n = 2 * 2) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)
    (hd : 2 ≤ Fintype.card (InfinitePlace F)) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (ιO ν)) =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν : ℝ) : ℂ) :=
  eisQ2_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 (genusFree_of_isPrincipalIdealRing _ _) hd hν

/-- **The $T(\pi^2)$ relations for the weight-2 series, class number one** (`eisHeckeRel_eisQ2` with the genus free by
`genusFree_of_isPrincipalIdealRing`; $n = 4$, $d \ge 2$). -/
@[kb "siegel1935" "T(𝔭²) relations for the weight-2 Eisenstein coefficients over F, h_F = 1 (n = 4) [unverified]"]
theorem eisHeckeRel_eisQ2_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    EisHeckeRel Q₀ (eisQ2 Q₀ 𝔑 h𝔑) :=
  eisHeckeRel_eisQ2 hQ hn hlev h𝔑 (genusFree_of_isPrincipalIdealRing _ _) hd

/-- **$\theta_{\mathrm{Gen}} = E_Q$ for $n = 4$, unconditionally** ($h_F = 1$, $d \ge 2$): `qCoeff_eisQ2_eq_genus_avg` with its input
`EisHeckeRel` discharged (`eisHeckeRel_eisQ2`). -/
@[kb "siegel1935" "θ_Gen = E_Q in weight 2 over F, h_F = 1, d ≥ 2 [unverified]"]
theorem thetaGen_eq_eisQ2_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    thetaGen (formF Q₀) stdLat = eisQ2 Q₀ 𝔑 h𝔑 :=
  (qCoeff_eisQ2_eq_genus_avg hQ hn hlev h𝔑 hd (eisHeckeRel_eisQ2_of_pid hQ hn hlev h𝔑 hd) 0).1

/-- **The coefficients of the weight-2 $E_Q$ are the genus averages, unconditionally** ($n = 4$, $d \ge 2$, $h_F = 1$): $\theta_{\mathrm{Gen}} = E_Q$
and, for $\nu \in \mathcal O_F$, $a_\nu(E_Q) = \mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)}r_M(\nu)/|O(M)|$. `qCoeff_eisQ2_eq_genus_avg` with
`EisHeckeRel` discharged (`eisHeckeRel_eisQ2_of_pid`). -/
@[kb "siegel1935" "θ_Gen = E_Q and r_Gen(ν) = a_ν(E_Q) in weight 2 over F, h_F = 1, d ≥ 2, unconditional [unverified]"]
theorem qCoeff_eisQ2_eq_genus_avg_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F)) (ν : 𝓞 F) :
    thetaGen (formF Q₀) stdLat = eisQ2 Q₀ 𝔑 h𝔑 ∧
      qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (ιO ν)) =
        ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
          ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
            ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) :=
  qCoeff_eisQ2_eq_genus_avg hQ hn hlev h𝔑 hd (eisHeckeRel_eisQ2_of_pid hQ hn hlev h𝔑 hd) ν

/-- **Siegel's formula over a totally real field for quaternary forms** ($F$ totally real of degree $d \ge 2$, $h_F = 1$; unconditional).
For $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 4$ variables and $\nu \in \mathcal O_F$ totally positive,
$$\mathrm{Mass}(\mathcal O_F^4)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^4)}\frac{r_M(\nu)}{|O(M)|}
  = |d_F|^{-3/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu)\quad(= |d_F|^{-3/2}\,\texttt{aENF}\ Q_0\ \nu).$$
The weight-2 case of `siegelFormula_nf`. Over $\mathbb Q$ ($d = 1$) the same statement is `Siegel.GenusEis.siegelFormula_quaternary`
(there $|d_F| = 1$). -/
@[kb "siegel1935" "Hauptsatz over a totally real F, h_F = 1, n = 4 (d ≥ 2): genus average = |d_F|^{-3/2} β_∞ ∏ β_𝔭 [unverified]"]
theorem siegelFormula_nf_four {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 4)
    (hd : 2 ≤ Fintype.card (InfinitePlace F)) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    (mass (formF Q₀) stdLat)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          (latRepF (formF Q₀) c.out.1 ν : ℝ) / (LatClass.autCard (formF Q₀) c : ℝ) =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν := by
  have hn' : n = 2 * 2 := hn
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  have h1 := (qCoeff_eisQ2_eq_genus_avg hQ hn' hlev h𝔑 hd (eisHeckeRel_eisQ2_of_pid hQ hn' hlev h𝔑 hd) ν).2
  have h2 := eisQ2_coeff_eq_discr_mul_aENF_of_pid hQ hn' hlev h𝔑 hd hν
  have h3 := h1.symm.trans h2
  apply Complex.ofReal_injective
  rw [← h3]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [div_eq_inv_mul]

/-- **Siegel's formula over $F$ for every even $n = 2k \ge 4$** ($h_F = 1$; $d \ge 2$ when $k = 2$): `siegelFormula_nf` ($k \ge 3$)
and `siegelFormula_nf_four` ($k = 2$). -/
@[kb "siegel1935" "Hauptsatz over a totally real F, h_F = 1, every even n ≥ 4 (d ≥ 2 if n = 4) [unverified]"]
theorem siegelFormula_nf_of_two_le {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 2 ≤ k) (hd : k = 2 → 2 ≤ Fintype.card (InfinitePlace F)) {ν : 𝓞 F}
    (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    (mass (formF Q₀) stdLat)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          (latRepF (formF Q₀) c.out.1 ν : ℝ) / (LatClass.autCard (formF Q₀) c : ℝ) =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν := by
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2 : k = 2 := by omega
    exact siegelFormula_nf_four hQ (by omega) (hd hk2) hν
  · exact siegelFormula_nf hQ hn hk3 hν

/-- **Siegel's formula over $F$ for $n = 4$ with `repMass`**: $\mathrm{repMass}(\mathcal O_F^4, \nu) = \mathrm{Mass}(\mathcal O_F^4)\cdot
|d_F|^{-3/2}\,\mathrm{aENF}(\nu)$ ($h_F = 1$, $d \ge 2$, $\nu \gg 0$). -/
@[kb "siegel1935" "Hauptsatz over F (repMass form), h_F = 1, n = 4, d ≥ 2 [unverified]"]
theorem siegelFormula_nf_four_repMass {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 4)
    (hd : 2 ≤ Fintype.card (InfinitePlace F)) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    QuadFormsKB.Tamagawa.repMass (formF Q₀) stdLat (ιO ν) =
      mass (formF Q₀) stdLat * ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν) := by
  have hm : 0 < mass (formF Q₀) stdLat := mass_pos hQ stdLat (isIntegral_stdLat Q₀)
  rw [← siegelFormula_nf_four hQ hn hd hν, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul,
    QuadFormsKB.Tamagawa.repMass, finsum_mem_eq_finite_toFinset_sum _
      (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀))]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **The input `SiegelFormulaAt` is a theorem for $n = 4$** ($F$ totally real of degree $d \ge 2$, $h_F = 1$, $Q_0$ totally positive
definite quaternary, $m \gg 0$): $\mathrm{repMass}(\mathcal O_F^4, m) = \mathrm{Mass}(\mathcal O_F^4)\cdot S(L, m)$ with `siegelProduct`. -/
@[kb "siegel1935" "Hauptsatz over F: SiegelFormulaAt, h_F = 1, n = 4, d ≥ 2 [unverified]"]
theorem siegelFormulaAt_of_pid_four {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 4)
    (hd : 2 ≤ Fintype.card (InfinitePlace F)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (ιO m)) :
    QuadFormsKB.Tamagawa.SiegelFormulaAt Q₀ m := by
  refine ⟨?_⟩
  rw [siegelProduct_eq_discr_mul_aENF (isTotPosGram_Q₀ hQ) (by omega) hm]
  exact siegelFormula_nf_four_repMass hQ hn hd hm

end QuadFormsKB.HilbertModular
