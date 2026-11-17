/-
# The Siegel–Weil formula in degree one over every totally real field, every class number

**Setting.** $F$ a totally real number field of **any class number**, $Q_0$ a totally positive definite quadratic form over
$\mathcal O_F$ in $n = 2k$ variables, $k \ge 3$, $L = \mathcal O_F^n$, $\theta_{\mathrm{Gen}} = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)
\subseteq\mathrm{gen}(L)}\theta_M/|O(M)|$ (`thetaGen`), $E_Q$ the Eisenstein series of the genus (`eisQ`, built from the constant terms
of $\theta_{\mathrm{Gen}}$ at the cusps), $q$-coefficients $a_\mu$ for $\mu \in \mathfrak d^{-1}$ (`qCoeff` for the lattice
$\sigma(\mathcal O_F)$).

**Main results.**
* `eisQ_coeff_eq_siegelProduct`: for every totally positive $\nu \in \mathcal O_F$, $a_\nu(E_Q)$ is Siegel's product of local
  densities `Tamagawa.siegelProduct Q₀ ν` (the right-hand side of `Tamagawa.SiegelFormulaAt`), every class number.
* `siegelFormula_nf_uncond`: Siegel's formula in the genus-average form of `HilbertModular.siegelFormula_nf'`, every class number,
  $n \ge 4$, without `PrincipalPrimeSupply` (from `Tamagawa.Measure.Weil.siegelFormulaAt_totallyReal`).
* **`thetaGen_eq_eisQ_uncond`** (classical form): $\theta_{\mathrm{Gen}} = E_Q$, every class number, unconditional.
* **`siegelWeil_formula_lattice_uncond`**, **`siegelWeil_formula_uncond`** (adelic form):
  $E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\,\theta_{\mathrm{Gen}}(z)$, every class number, unconditional.

**Proof (coefficient comparison).** $g = \theta_{\mathrm{Gen}} - E_Q$ is a cusp form for every class number
(`thetaGen_sub_eisQ_mem_cuspFormChar'`). Its coefficient $a_\mu(g)$ vanishes for every $\mu \in \mathfrak d^{-1}$:
* $\mu = 0$ or $\mu$ not totally positive: $g$ vanishes at $i\infty$ (`qCoeff_support_of_isZeroAtImInftyPi`);
* $\mu \notin \mathcal O_F$: $a_\mu(\theta_{\mathrm{Gen}}) = 0$ (`latCoeff`) and $a_\mu(E_Q) = 0$ (the singular series vanishes,
  `SingularNF.singSeries_eq_zero_of_not_int`);
* $\mu = \nu \in \mathcal O_F$ totally positive: $a_\nu(\theta_{\mathrm{Gen}})$ is the genus average of $r_M(\nu)$, which is
  $|d_F|^{-(n-1)/2}\mathrm{aENF}(\nu)$ by Siegel's formula (unconditional), and $a_\nu(E_Q)$ is the same (`eisQ_coeff_eq_discr_mul_aENF'`).
Fourier inversion (`hasSum_qExpansion`) gives $g = 0$. This replaces the Hecke-operator vanishing argument of
`SiegelFormulaNP.lean`, which needed principal primes (`PrincipalPrimeSupply F`).

Sources: Siegel, Ann. Math. 36 (1935), Hauptsatz [unverified]; Weil, Acta Math. 113 (1965), Ch. IV [unverified];
Weil, *Adeles and algebraic groups* (1982), Thm 4.5.1 [unverified page].
-/
import QuadFormsKB.HilbertModular.SiegelFormulaNP
import QuadFormsKB.HilbertModular.SiegelFormulaNF4
import QuadFormsKB.SiegelWeil.SiegelWeilLattice
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal

open NumberField Complex Filter
open scoped MatrixGroups nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **The Fourier coefficients of $E_Q$ are Siegel's products of local densities**, every class number: for $F$ totally real,
$Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2k \ge 6$ variables and $\nu \in \mathcal O_F$ totally positive,
$$a_\nu(E_Q) = \texttt{Tamagawa.siegelProduct}\ Q_0\ \nu = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu).$$
(The coefficient comparison for every class number, `eisQ_coeff_eq_discr_mul_aENF'`, and `siegelProduct_eq_discr_mul_aENF`.) -/
@[kb "siegel1935" "the ν-th coefficient of the genus Eisenstein series is Siegel's density product, over F, every class number [unverified]"]
theorem eisQ_coeff_eq_siegelProduct {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO ν)) = (QuadFormsKB.Tamagawa.siegelProduct Q₀ ν : ℂ) := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  rw [eisQ_coeff_eq_discr_mul_aENF' hQ hn hlev h𝔑 hk hν,
    siegelProduct_eq_discr_mul_aENF (isTotPosGram_Q₀ hQ) (by omega) hν]

/-- **Siegel's formula over a totally real field of any class number, $n \ge 4$, unconditional** (the statement of
`siegelFormula_nf'` without `PrincipalPrimeSupply`): for $Q_0$ totally positive definite over $\mathcal O_F$ in $n \ge 4$ variables and
$\nu \in \mathcal O_F$ totally positive,
$$\mathrm{Mass}(\mathcal O_F^n)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^n)}\frac{r_M(\nu)}{|O(M)|}
  = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu).$$
(`Tamagawa.Measure.Weil.siegelFormulaAt_totallyReal` and `siegelProduct_eq_discr_mul_aENF`.) -/
@[kb "siegel1935" "Hauptsatz over a totally real F, every class number, n ≥ 4, unconditional [unverified]"]
theorem siegelFormula_nf_uncond {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n)
    {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    (mass (formF Q₀) stdLat)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          (latRepF (formF Q₀) c.out.1 ν : ℝ) / (LatClass.autCard (formF Q₀) c : ℝ) =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν := by
  have hS : QuadFormsKB.Tamagawa.repMass (formF Q₀) stdLat (ιO ν) =
      mass (formF Q₀) stdLat * QuadFormsKB.Tamagawa.siegelProduct Q₀ ν :=
    (QuadFormsKB.Tamagawa.Measure.Weil.siegelFormulaAt_totallyReal hn Q₀ hQ hν).repMass_eq
  rw [siegelProduct_eq_discr_mul_aENF (isTotPosGram_Q₀ hQ) (by omega) hν] at hS
  have hm : 0 < mass (formF Q₀) stdLat := mass_pos hQ stdLat (isIntegral_stdLat Q₀)
  have hsum : QuadFormsKB.Tamagawa.repMass (formF Q₀) stdLat (ιO ν) =
      ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
        (latRepF (formF Q₀) c.out.1 ν : ℝ) / (LatClass.autCard (formF Q₀) c : ℝ) := by
    rw [QuadFormsKB.Tamagawa.repMass, finsum_mem_eq_finite_toFinset_sum _
      (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀))]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 2
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [← hsum, hS, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

section Main

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
  (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)

include hQ hn hlev h𝔑 in
/-- The $\nu$-th coefficient of $\theta_{\mathrm{Gen}}$ at $\nu \in \mathcal O_F$ is the genus average of $r_M(\nu)$ (any class number). -/
lemma qCoeff_thetaGen_int (ν : 𝓞 F) :
    qCoeff (thetaGen (formF Q₀) stdLat) (oBasis F) (realVec (ιO ν)) =
      ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) := by
  classical
  rw [show ιO ν = QuadFormsKB.Analysis.dualElt 1 (mOf ν) from (dualElt_mOf ν).symm, qCoeff_thetaGen' hQ hn hlev h𝔑]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt 1 (mOf ν) := ⟨ν, (dualElt_mOf ν).symm⟩
  rw [latCoeff, dif_pos h1]
  congr 3
  exact IsFractionRing.injective (𝓞 F) F (h1.choose_spec.trans (dualElt_mOf ν))

include hQ hn hlev h𝔑 in
/-- The coefficient of $\theta_{\mathrm{Gen}}$ at $\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$ is $0$. -/
lemma qCoeff_thetaGen_not_int (m : Fin (Module.finrank ℚ F) → ℤ) (hint : ¬ ∃ ν : 𝓞 F, ιO ν = oDual m) :
    qCoeff (thetaGen (formF Q₀) stdLat) (oBasis F) (dualVec (oBasis F) m) = 0 := by
  classical
  rw [dualVec_oBasis, qCoeff_thetaGen' hQ hn hlev h𝔑]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun c _ => ?_)
  rw [latCoeff, dif_neg hint, mul_zero]

include hQ hn hlev h𝔑 in
/-- The coefficient of $E_Q$ at $\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$ is $0$ ($k \ge 3$, any class number). -/
lemma qCoeff_eisQ_not_int (hk : 3 ≤ k) (m : Fin (Module.finrank ℚ F) → ℤ) (hm : m ≠ 0)
    (hint : ¬ ∃ ν : 𝓞 F, ιO ν = oDual m) :
    qCoeff (eisQ Q₀ k) (oBasis F) (dualVec (oBasis F) m) = 0 := by
  have hfree := genusFree_formF hQ
  have hsum := fun μ => (eisQ_qexp hQ hn hlev h𝔑 hfree hk (fun _ => UpperHalfPlane.I)).2.1 μ
  rw [qCoeff_eisQ hQ hn hlev h𝔑 hfree hk hm, eisQCoeff,
    SiegelWeil.SingularNF.singSeries_eq_zero_of_not_int Q₀ (oDual_mem m) hint (hsum _)]
  simp

end Main

/-- **Classical form: $\theta_{\mathrm{Gen}} = E_Q$ over every totally real field, every class number, $n = 2k \ge 6$,
unconditional** (the statement of `thetaGen_eq_eisQ'` without `PrincipalPrimeSupply`). For $F$ totally real and $Q_0$ totally
positive definite over $\mathcal O_F$ in $n = 2k$ variables, $k \ge 3$, the genus theta series
$\theta_{\mathrm{Gen}} = \mathrm{Mass}(\mathcal O_F^n)^{-1}\sum_{\mathrm{cls}(M)}\theta_M/|O(M)|$ equals the Eisenstein series $E_Q$ of the genus.
Proof by comparing all Fourier coefficients (module docstring). -/
@[kb "siegel1935" "Hauptsatz, θ_Gen = E_Q over every totally real F, every class number, n ≥ 6, unconditional [unverified]"]
theorem thetaGen_eq_eisQ_uncond {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) :
    thetaGen (formF Q₀) stdLat = eisQ Q₀ k := by
  classical
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  have hfree := genusFree_formF hQ
  have hcusp := thetaGen_sub_eisQ_mem_cuspFormChar' hQ hn hlev h𝔑 hk
  set θ := thetaGen (formF Q₀) stdLat with hθdef
  set E := eisQ Q₀ k with hEdef
  set b := oBasis F with hbdef
  have hθ := thetaGen_mem_modularFormChar' hQ hn hlev h𝔑
  have hθhol : IsHolomorphic θ := hθ.1.2.1
  have hθper : IsLatticePeriodic θ b := isLatticePeriodic_of_mem_modularFormChar hθ
  have hEm := eisQ_mem_modularFormChar hQ hn hlev h𝔑 hk hfree
  have hEhol : IsHolomorphic E := hEm.1.2.1
  have hEper : IsLatticePeriodic E b := isLatticePeriodic_of_mem_modularFormChar hEm
  have hghol : IsHolomorphic (θ - E) := hcusp.1.2.1
  have hgper : IsLatticePeriodic (θ - E) b := isLatticePeriodic_of_mem_cuspFormChar hcusp
  have hgz : IsZeroAtImInftyPi (θ - E) := by
    have h := hcusp.1.2.2 1
    rwa [map_one, SlashAction.slash_one] at h
  -- every coefficient of `θ - E` vanishes
  have hzero : ∀ m, qCoeff (θ - E) b (dualVec b m) = 0 := by
    intro m
    by_contra hne
    obtain ⟨hnn, h0⟩ := qCoeff_support_of_isZeroAtImInftyPi hghol hgper hgz m hne
    rw [hbdef, dualVec_oBasis] at hnn h0
    have hμ0 : oDual m ≠ 0 := by
      intro h; apply h0; funext v; simp [realVec, h]
    have hpos : ∀ v, 0 < realEmb F v (oDual m) := by
      intro v
      refine lt_of_le_of_ne (hnn v) (Ne.symm fun hv => hμ0 ?_)
      exact (realEmb F v).injective (by rw [hv, map_zero])
    have hm0 : m ≠ 0 := by rintro rfl; exact hμ0 oDual_zero
    apply hne
    rw [qCoeff_sub hθhol hEhol hθper hEper, sub_eq_zero]
    by_cases hint : ∃ ν : 𝓞 F, ιO ν = oDual m
    · obtain ⟨ν, hν⟩ := hint
      have hνpos : ∀ v, 0 < realEmb F v (ιO ν) := fun v => hν ▸ hpos v
      rw [hbdef, dualVec_oBasis, ← hν, qCoeff_thetaGen_int hQ hn hlev h𝔑 ν,
        eisQ_coeff_eq_discr_mul_aENF' hQ hn hlev h𝔑 hk hνpos,
        ← siegelFormula_nf_uncond hQ (by omega) hνpos]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [div_eq_inv_mul]
    · rw [hbdef, qCoeff_thetaGen_not_int hQ hn hlev h𝔑 m hint,
        qCoeff_eisQ_not_int hQ hn hlev h𝔑 hk m hm0 hint]
  -- Fourier inversion
  funext z
  have h := hasSum_qExpansion hghol hgper z
  have h0 : ∀ m, qCoeff (θ - E) b (dualVec b m) * qTerm (dualVec b m) z = 0 := fun m => by
    rw [hzero m, zero_mul]
  rw [show (fun m => qCoeff (θ - E) b (dualVec b m) * qTerm (dualVec b m) z) = fun _ => 0 from
    funext h0] at h
  have h1 : (θ - E) z = 0 := h.unique hasSum_zero
  simpa [sub_eq_zero] using h1

/-- **The coefficients of $E_Q$ are the genus averages**, every totally real $F$, every class number, $n = 2k \ge 6$, unconditional
(`qCoeff_eisQ_eq_genus_avg'` without `PrincipalPrimeSupply`). -/
@[kb "siegel1935" "r_Gen(ν) = ν-th coefficient of E_Q, over F, every class number, unconditional [unverified]"]
theorem qCoeff_eisQ_eq_genus_avg_uncond {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) (ν : 𝓞 F) :
    qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO ν)) =
      ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  rw [← thetaGen_eq_eisQ_uncond hQ hn hk, qCoeff_thetaGen_int hQ hn hlev h𝔑 ν]

/-- **$\theta_{\mathrm{Gen}} = E_Q$ for quaternary forms ($n = 4$, weight 2) over every totally real field of degree $d \ge 2$, every class
number, unconditional** (`thetaGen_eq_eisQ2_of_pid` without the principal ideal domain hypothesis). Same coefficient comparison as
`thetaGen_eq_eisQ_uncond`, with the weight-2 Eisenstein series `eisQ2` of the theta level $\mathfrak N$ ($d \ge 2$: Hecke's correction
term vanishes). -/
@[kb "siegel1935" "Hauptsatz, θ_Gen = E_Q over every totally real F of degree ≥ 2, n = 4, every class number, unconditional [unverified]"]
theorem thetaGen_eq_eisQ2_uncond {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    thetaGen (formF Q₀) stdLat = eisQ2 Q₀ 𝔑 h𝔑 := by
  classical
  have hfree := genusFree_formF hQ
  have hcusp := thetaGen_sub_eisQ2_mem_cuspFormChar' hQ hlev h𝔑 hn hd
  set θ := thetaGen (formF Q₀) stdLat with hθdef
  set E := eisQ2 Q₀ 𝔑 h𝔑 with hEdef
  set b := oBasis F with hbdef
  have hθ := thetaGen_mem_modularFormChar' hQ hn hlev h𝔑
  have hθhol : IsHolomorphic θ := hθ.1.2.1
  have hθper : IsLatticePeriodic θ b := isLatticePeriodic_of_mem_modularFormChar hθ
  have hEm := eisQ2_mem_modularFormChar hQ hn hlev h𝔑 hd hfree
  have hEhol : IsHolomorphic E := hEm.1.2.1
  have hEper : IsLatticePeriodic E b := isLatticePeriodic_of_mem_modularFormChar hEm
  have hghol : IsHolomorphic (θ - E) := hcusp.1.2.1
  have hgper : IsLatticePeriodic (θ - E) b := isLatticePeriodic_of_mem_cuspFormChar hcusp
  have hgz : IsZeroAtImInftyPi (θ - E) := by
    have h := hcusp.1.2.2 1
    rwa [map_one, SlashAction.slash_one] at h
  have hzero : ∀ m, qCoeff (θ - E) b (dualVec b m) = 0 := by
    intro m
    by_contra hne
    obtain ⟨hnn, h0⟩ := qCoeff_support_of_isZeroAtImInftyPi hghol hgper hgz m hne
    rw [hbdef, dualVec_oBasis] at hnn h0
    have hμ0 : oDual m ≠ 0 := by
      intro h; apply h0; funext v; simp [realVec, h]
    have hpos : ∀ v, 0 < realEmb F v (oDual m) := by
      intro v
      refine lt_of_le_of_ne (hnn v) (Ne.symm fun hv => hμ0 ?_)
      exact (realEmb F v).injective (by rw [hv, map_zero])
    have hm0 : m ≠ 0 := by rintro rfl; exact hμ0 oDual_zero
    apply hne
    rw [qCoeff_sub hθhol hEhol hθper hEper, sub_eq_zero]
    by_cases hint : ∃ ν : 𝓞 F, ιO ν = oDual m
    · obtain ⟨ν, hν⟩ := hint
      have hνpos : ∀ v, 0 < realEmb F v (ιO ν) := fun v => hν ▸ hpos v
      rw [hbdef, dualVec_oBasis, ← hν, qCoeff_thetaGen_int hQ hn hlev h𝔑 ν,
        eisQ2_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 hfree hd hνpos,
        ← siegelFormula_nf_uncond hQ (by omega) hνpos]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [div_eq_inv_mul]
    · rw [hbdef, qCoeff_thetaGen_not_int hQ hn hlev h𝔑 m hint, dualVec_oBasis,
        eisQ2_coeff_eq_zero_of_not_int hQ hn hlev h𝔑 hfree hd hm0 hint]
  funext z
  have h := hasSum_qExpansion hghol hgper z
  have h0 : ∀ m, qCoeff (θ - E) b (dualVec b m) * qTerm (dualVec b m) z = 0 := fun m => by
    rw [hzero m, zero_mul]
  rw [show (fun m => qCoeff (θ - E) b (dualVec b m) * qTerm (dualVec b m) z) = fun _ => 0 from
    funext h0] at h
  have h1 : (θ - E) z = 0 := h.unique hasSum_zero
  simpa [sub_eq_zero] using h1

end QuadFormsKB.HilbertModular

namespace QuadFormsKB.SiegelWeil

open QuadFormsKB.HilbertModular QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m : ℕ}

/-- **Adelic form, any lattice basis: the Siegel–Weil formula in degree one for every totally positive form over
$\mathcal O_F$, every class number, unconditional** (`siegelWeil_formula_lattice` without `PrincipalPrimeSupply`): for $F$ totally
real, $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2m \ge 6$ variables (not necessarily diagonal, dyadic places
included), a diagonalization $Q_0\circ P = \langle d\rangle$ ($\det P \ne 0$, all $d_i \ne 0$), $L' = P^{-1}\mathcal O_F^n$ and
$z \in \mathbb H^d$,
$$E(g_z, s_0, \varphi_\infty\otimes\textstyle\bigotimes_v\mathbf 1_{L'_v}) = \prod_wy_w^{m/2}\cdot\theta_{\mathrm{Gen}}(z),\qquad
  \theta_{\mathrm{Gen}} = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M}{|O(M)|},\quad L = \mathcal O_F^n.$$ -/
@[kb "weil1965" "Ch. IV (the Siegel–Weil formula), degree one, n ≥ 6, every totally real F, every class number, unconditional [unverified]; Siegel (1935), Hauptsatz [unverified]"]
theorem siegelWeil_formula_lattice_uncond (hm : 3 ≤ m) {Q₀ : QuadForm (𝓞 F) (2 * m)} (hQ : IsTotallyPosDef (formF Q₀))
    {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0) {d : Fin (2 * m) → 𝓞 F} (hd : ∀ i, d i ≠ 0)
    (hQP : Q₀.compMat P = QuadForm.diag d) (z : InfinitePlace F → UpperHalfPlane) :
    eisensteinL (unitsOfInt d hd) P hP (isArchSection_archSec d hd (pos_of_compMat hQ hP hQP) z) =
      (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) * thetaGen (formF Q₀) stdLat z := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  rw [(eisensteinL_archSec_eq_eisQ hm hQ hP hd hQP z).2, thetaGen_eq_eisQ_uncond hQ rfl hm]

/-- **Adelic form, explicit genus sum**: `siegelWeil_formula_lattice_of_pid` for every class number, unconditional:
$$E(g_z, s_0, \varphi_\infty\otimes\textstyle\bigotimes_v\mathbf 1_{L'_v}) = \prod_wy_w^{m/2}\cdot\mathrm{Mass}(L)^{-1}
  \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M(z)}{|O(M)|}.$$ -/
@[kb "weil1965" "Ch. IV (the Siegel–Weil formula), degree one, n ≥ 6, every class number, genus sum, unconditional [unverified]"]
theorem siegelWeil_formula_lattice_sum_uncond (hm : 3 ≤ m) {Q₀ : QuadForm (𝓞 F) (2 * m)}
    (hQ : IsTotallyPosDef (formF Q₀)) {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0)
    {d : Fin (2 * m) → 𝓞 F} (hd : ∀ i, d i ≠ 0) (hQP : Q₀.compMat P = QuadForm.diag d)
    (z : InfinitePlace F → UpperHalfPlane) :
    eisensteinL (unitsOfInt d hd) P hP (isArchSection_archSec d hd (pos_of_compMat hQ hP hQP) z) =
      (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) *
        (((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
          ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
            ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * thetaLatt (formF Q₀) c.out.1 z) := by
  rw [siegelWeil_formula_lattice_uncond hm hQ hP hd hQP z,
    thetaGen_eq_sum (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀))]
  simp [Finset.sum_apply, smul_eq_mul]

/-- **Adelic form, diagonal $Q_0$**: `siegelWeil_formula` without `PrincipalPrimeSupply` and without the scope condition
`GenusFree` (which holds for every $F$, `genusFree_formF`): for $Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite over $\mathcal O_F$,
$n = 2m \ge 6$, every totally real $F$, every class number,
$E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\cdot\theta_{\mathrm{Gen}}(z)$. -/
@[kb "weil1965" "Ch. IV (the Siegel–Weil formula), degree one, n ≥ 6, diagonal, every class number, unconditional [unverified]"]
theorem siegelWeil_formula_uncond {b : Fin (2 * m) → 𝓞 F} (hb : ∀ i, b i ≠ 0)
    (hQ : IsTotallyPosDef (formF (QuadForm.diag b))) (hm : 3 ≤ m) (z : InfinitePlace F → UpperHalfPlane) :
    eisenstein (unitsOfInt b hb) (isArchSection_archSec b hb (pos_of_isTotallyPosDef hQ) z) =
      (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) * thetaGen (formF (QuadForm.diag b)) stdLat z := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  rw [(eisenstein_archSec_eq_eisQ hb hQ hm hlev h𝔑 (genusFree_formF hQ) z).2,
    thetaGen_eq_eisQ_uncond hQ rfl hm]

end QuadFormsKB.SiegelWeil

end
