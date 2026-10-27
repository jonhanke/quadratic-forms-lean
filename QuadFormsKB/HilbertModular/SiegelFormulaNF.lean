/-
# Siegel's formula over a totally real field, unconditionally

**Setting.** $F$ a totally real number field with $\mathcal O_F$ a PID (class number one; `[IsPrincipalIdealRing (𝓞 F)]`), $Q_0$ a totally
positive definite quadratic form over $\mathcal O_F$ in $n = 2k \ge 6$ variables (`IsTotallyPosDef (formF Q₀)`), $L = \mathcal O_F^n$
(`stdLat`), its genus classes $\mathrm{cls}(M)$ (`genusClasses`), $|O(M)|$ the number of isometries of $M$ (proper and improper,
`LatClass.autCard`), $r_M(\nu) = \#\{x \in M : Q_0(x) = \nu\}$ (`latRepF`), $\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)}|O(M)|^{-1}$ (`mass`).

**Main theorem** (`siegelFormula_nf`, Siegel's Hauptsatz over $F$ in degree one): for every totally positive $\nu \in \mathcal O_F$,
$$\frac{1}{\mathrm{Mass}(L)}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(\nu)}{|O(M)|}
  = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu) = |d_F|^{-(n-1)/2}\,\texttt{aENF}\ Q_0\ \nu,$$
with $\beta_\infty = \prod_w\beta_w$ (Lebesgue measure at each real place, Hanke (5.5)) and $\beta_\mathfrak p$ = `LocalDensity.NF.localDensity`
($\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$, Hanke (5.1)–(5.2); every prime, dyadic included). The constant $|d_F|^{-(n-1)/2}$ is the
correction of Hanke 2004, (5.3) over $F \ne \mathbb Q$; over $\mathbb Q$ it is $1$ (`discrFactor_rat`).

**No inputs.** It is proved from `thetaGen_eq_eisQ` ($\theta_{\mathrm{Gen}} = E_Q$ by the Hecke/Kneser vanishing argument), whose input
`EisHeckeRel` is now a theorem (`eisHeckeRel_eisQ_of_pid`), the coefficients of $E_Q$ (`eisQ_coeff_eq_discr_mul_aENF_of_pid`), and
the existence of a theta level (`exists_isThetaLevelF`). The only scope hypotheses are $F$ totally real, $h_F = 1$, $n = 2k \ge 6$,
$Q_0$ totally positive definite.

**Corollaries.**
* `siegelFormula_nf_repMass`: The same with the `repMass` (a `finsum` over the genus classes).
* `siegelFormulaAt_of_pid`: **The input `Tamagawa.SiegelFormulaAt Q₀ m` holds** for every totally positive $m$ (with
  `siegelProduct_eq_discr_mul_aENF`), so it is no longer an input of the mass-formula induction in this scope.

**Cross-check with $\mathbb Q$.** Over $\mathbb Q$ (`Siegel.SiegelFormula`, proved for $n = 4$ as `Siegel.GenusEis.siegelFormula_quaternary`) the statement is `genusRepAvg Q m = aE Q m` for $m \ge 1$: The genus average (the same $\sum r_M(m)/|O(M)|$ over $\mathrm{Mass}$)
equals Hanke's (5.3) with no constant. `siegelFormula_nf` has the same shape, with `aENF` the transcription of (5.3) to $F$ and the factor
$|d_F|^{-(n-1)/2}$, which is $1$ for $F = \mathbb Q$ (`discrFactor_rat`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), Hauptsatz [unverified]; Siegel, Ann.
Math. 38 (1937) (over number fields) [unverified]; Hanke 2004, (5.3), p. 368 (with the corrected constant);
Shimura, Duke Math. J. 45 (1978), §3 [unverified]; Eichler 1952 and Kneser 1957 (the Hecke/neighbour argument) [unverified].
-/
import QuadFormsKB.HilbertModular.EisHecke
import QuadFormsKB.HilbertModular.Cuspidal2

open Complex NumberField
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **Siegel's formula over a totally real field, $n \ge 6$, class number one** (unconditional). For $Q_0$ totally positive definite
over $\mathcal O_F$ in $n = 2k \ge 6$ variables and $\nu \in \mathcal O_F$ totally positive,
$$\mathrm{Mass}(\mathcal O_F^n)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^n)}\frac{r_M(\nu)}{|O(M)|}
  = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu)\quad(= |d_F|^{-(n-1)/2}\,\texttt{aENF}\ Q_0\ \nu).$$
Proof: $\theta_{\mathrm{Gen}} = E_Q$ (with `EisHeckeRel` proved here), so the genus average is the $\nu$-th coefficient of $E_Q$
(`qCoeff_eisQ_eq_genus_avg`), which is the $|d_F|^{-(n-1)/2}\mathrm{aENF}(\nu)$. -/
@[kb "siegel1935" "Hauptsatz over a totally real F, h_F = 1, n ≥ 6: genus average = |d_F|^{-(n-1)/2} β_∞ ∏ β_𝔭 [unverified]"]
theorem siegelFormula_nf {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
    (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    (mass (formF Q₀) stdLat)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          (latRepF (formF Q₀) c.out.1 ν : ℝ) / (LatClass.autCard (formF Q₀) c : ℝ) =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  have h1 := qCoeff_eisQ_eq_genus_avg hQ hn hlev h𝔑 hk (eisHeckeRel_eisQ_of_pid hQ hn hlev h𝔑 hk) ν
  have h2 := eisQ_coeff_eq_discr_mul_aENF_of_pid hQ hn hlev h𝔑 hk hν
  have h3 := h1.symm.trans h2
  apply Complex.ofReal_injective
  rw [← h3]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [div_eq_inv_mul]

/-- **Siegel's formula over $F$ with the `repMass`**: $\mathrm{repMass}(\mathcal O_F^n, \nu) = \mathrm{Mass}(\mathcal O_F^n)\cdot
|d_F|^{-(n-1)/2}\,\mathrm{aENF}(\nu)$ ($F$ totally real, $h_F = 1$, $n = 2k \ge 6$, $\nu \gg 0$). -/
@[kb "siegel1935" "Hauptsatz over F (repMass form), h_F = 1, n ≥ 6 [unverified]"]
theorem siegelFormula_nf_repMass {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    QuadFormsKB.Tamagawa.repMass (formF Q₀) stdLat (ιO ν) =
      mass (formF Q₀) stdLat * ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν) := by
  have hm : 0 < mass (formF Q₀) stdLat := mass_pos hQ stdLat (isIntegral_stdLat Q₀)
  rw [← siegelFormula_nf hQ hn hk hν, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul,
    QuadFormsKB.Tamagawa.repMass, finsum_mem_eq_finite_toFinset_sum _
      (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀))]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **The input `SiegelFormulaAt` is a theorem** ($F$ totally real, $h_F = 1$, $Q_0$ totally positive definite in
$n = 2k \ge 6$ variables, $m \gg 0$):
$\mathrm{repMass}(\mathcal O_F^n, m) = \mathrm{Mass}(\mathcal O_F^n)\cdot S(L, m)$ with the `siegelProduct`
$S(L, m) = |d_F|^{-(n-1)/2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(m)$ (=
$|d_F|^{-(n-1)/2}\,$`aENF`, by `siegelProduct_eq_discr_mul_aENF`). -/
@[kb "siegel1935" "Hauptsatz over F: The SiegelFormulaAt, h_F = 1, n ≥ 6 [unverified]"]
theorem siegelFormulaAt_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (ιO m)) :
    QuadFormsKB.Tamagawa.SiegelFormulaAt Q₀ m := by
  refine ⟨?_⟩
  rw [siegelProduct_eq_discr_mul_aENF (isTotPosGram_Q₀ hQ) (by omega) hm]
  exact siegelFormula_nf_repMass hQ hn hk hm

/-! ### The $E_Q$ forms with `EisHeckeRel` discharged ($n \ge 6$, $h_F = 1$)

`thetaGen_eq_eisQ` and `qCoeff_eisQ_eq_genus_avg` (`SiegelHecke.lean`) take `EisHeckeRel Q₀ (eisQ Q₀ k)` as a hypothesis; it is
the theorem `eisHeckeRel_eisQ_of_pid` (from the explicit coefficients
$a_\nu(E_Q) = |d_F|^{-(n-1)/2}\,\mathrm{aENF}(\nu)$ and the local identity `aENF_mul_pi_sq`:
$\beta_\mathfrak q(\pi^2\nu) = \beta_\mathfrak q(\nu)$ for $\mathfrak q \ne (\pi)$ and the good-prime Euler factor at
$\pi$). The following are their unconditional forms. -/

/-- **$\theta_{\mathrm{Gen}} = E_Q$, unconditionally** ($F$ totally real, $h_F = 1$, $Q_0$ totally positive definite in $n = 2k \ge 6$ variables,
$\mathfrak N \ne 0$ a theta level): `thetaGen_eq_eisQ` with `EisHeckeRel` discharged by `eisHeckeRel_eisQ_of_pid`. -/
@[kb "siegel1935" "Hauptsatz, θ_Gen = E_Q over F, h_F = 1, n ≥ 6, unconditional [unverified]"]
theorem thetaGen_eq_eisQ_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hk : 3 ≤ k) :
    thetaGen (formF Q₀) stdLat = eisQ Q₀ k :=
  thetaGen_eq_eisQ hQ hn hlev h𝔑 hk (eisHeckeRel_eisQ_of_pid hQ hn hlev h𝔑 hk)

/-- **The coefficients of $E_Q$ are the genus averages, unconditionally** ($h_F = 1$, $n = 2k \ge 6$): for $\nu \in \mathcal O_F$,
$a_\nu(E_Q) = \mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)}r_M(\nu)/|O(M)|$. `qCoeff_eisQ_eq_genus_avg` with `EisHeckeRel` discharged
(`eisHeckeRel_eisQ_of_pid`). -/
@[kb "siegel1935" "r_Gen(ν) = ν-th coefficient of E_Q, over F, h_F = 1, n ≥ 6, unconditional [unverified]"]
theorem qCoeff_eisQ_eq_genus_avg_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hk : 3 ≤ k) (ν : 𝓞 F) :
    qCoeff (eisQ Q₀ k) (koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) (realVec (ν : F)) =
      ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) :=
  qCoeff_eisQ_eq_genus_avg hQ hn hlev h𝔑 hk (eisHeckeRel_eisQ_of_pid hQ hn hlev h𝔑 hk) ν

/-! ### $n = 4$ (weight 2): reduction to one named input

We have $\theta_{\mathrm{Gen}} - E_Q \in S_2$ for the weight-2 Eisenstein series of the genus (`eisQ2`,
$d = [F:\mathbb Q] \ge 2$), so the input `ThetaGenSubCusp2` is a theorem. The remaining input
`EisHeckeRel Q₀ (eisQ2 Q₀ 𝔑 h𝔑)` is proved in `SiegelFormulaNF4.lean` (`eisHeckeRel_eisQ2`, from the Fourier
coefficients of $E_Q$ in weight 2, `qCoeff_eisQ2_eq`), which gives `siegelFormula_nf_four`. Over $\mathbb Q$ the case
$n = 4$ is `Siegel.GenusEis.siegelFormula_quaternary`. -/

/-- **The weight-2 input `ThetaGenSubCusp2` is a theorem** for $E = E_Q$ = `eisQ2` ($n = 4$, $d \ge 2$, $h_F = 1$). -/
@[kb "siegel1935" "θ_Gen − E_Q ∈ S₂ discharges ThetaGenSubCusp2 [unverified]"]
theorem thetaGenSubCusp2_eisQ2 {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    ThetaGenSubCusp2 Q₀ (eisQ2 Q₀ 𝔑 h𝔑) 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) :=
  thetaGen_sub_eisQ2_mem_cuspFormChar_of_pid hQ hn hlev h𝔑 hd

/-- **Siegel's formula over $F$ for $n = 4$, conditional on one named input**: for $Q_0$ totally positive definite quaternary over
$\mathcal O_F$ ($F$ totally real of degree $d \ge 2$, $h_F = 1$), a theta level $\mathfrak N \ne 0$, and the $T(\pi^2)$ relations for the
weight-2 Eisenstein series of the genus (`EisHeckeRel Q₀ (eisQ2 Q₀ 𝔑 h𝔑)`, an input), $\theta_{\mathrm{Gen}} = E_Q$, hence for $\nu \in \mathcal O_F$
$$a_\nu(E_Q) = \mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)}\frac{r_M(\nu)}{|O(M)|}.$$
The input is discharged by `eisHeckeRel_eisQ2` and $a_\nu(E_Q) = |d_F|^{-3/2}\,\mathrm{aENF}(\nu)$ is `eisQ2_coeff_eq_discr_mul_aENF`
(`SiegelFormulaNF4.lean`); the unconditional statement is `siegelFormula_nf_four`. -/
@[kb "siegel1935" "Hauptsatz over F, n = 4: θ_Gen = E_Q given EisHeckeRel for eisQ2 [unverified]"]
theorem qCoeff_eisQ2_eq_genus_avg {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (hE : EisHeckeRel Q₀ (eisQ2 Q₀ 𝔑 h𝔑)) (ν : 𝓞 F) :
    thetaGen (formF Q₀) stdLat = eisQ2 Q₀ 𝔑 h𝔑 ∧
      qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (ιO ν)) =
        ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
          ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
            ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) := by
  classical
  have hθ := thetaGen_eq_of_wt2 hQ hlev h𝔑 hn (thetaGenSubCusp2_eisQ2 hQ hn hlev h𝔑 hd) hE
  refine ⟨hθ, ?_⟩
  have h1 := qCoeff_thetaGen hQ hn hlev h𝔑 (mOf ν)
  rw [dualElt_mOf, hθ] at h1
  rw [show oBasis F = koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) from rfl, h1]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 : ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (mOf ν) :=
    ⟨ν, (dualElt_mOf ν).symm⟩
  rw [latCoeff, dite_eq_left_of_eq_true (eq_true h2)]
  congr 3
  exact IsFractionRing.injective (𝓞 F) F (h2.choose_spec.trans (dualElt_mOf ν))

end QuadFormsKB.HilbertModular
