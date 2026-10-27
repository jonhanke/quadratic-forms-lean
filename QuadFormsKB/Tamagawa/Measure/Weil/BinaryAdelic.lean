import QuadFormsKB.Tamagawa.Measure.Weil.BinaryMeasure
import QuadFormsKB.Tamagawa.BinaryTauNF
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropic

/-!
# Weil's $\tau(SO(V)) = 2$ for binary $V$, adelic form
**Layer:** number fields. $F$ a number field, $Q_0$ a nondegenerate binary form over $\mathcal O_F$, $E$ its discriminant
field (`IsDiscField`), $\mu^{\chi_E}_{\mathrm{Tam}}$ = `muTamBin Q₀ hQ E` (Weil's Tamagawa measure with the convergence
factors $L_v(1,\chi_E)$ and the global factor $L(1,\chi_E)^{-1}$; `BinaryMeasure.lean`).

**Defines**
* **`TauTwoBinaryAdelic Q₀ hQ`** (target statement): $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu^{\chi_E}_{\mathrm{Tam}}) = 2$ for
  every discriminant field $E$ (Ono's $\tau(R^1_{E/F}\mathbb G_m) = 2$);
* `TauTwoBinaryAll F` (target statement): `TauTwoBinaryAdelic` for every anisotropic nondegenerate binary form over $F$.

**Proves**
* **the bridge** `covolume_muTamBin_eq_tauSOReg`: for $F$ totally real and $Q_0$ totally positive definite,
  $\mathrm{covol}(\mu^{\chi_E}_{\mathrm{Tam}}) = \tau^{\mathrm{reg}}(SO(Q_0))$ (`tauSOReg`, the regularized mass-formula
  normalization), from `covolume_muTam_eq_covolume_muAdele` and `covolume_muAdele` (both for any $\lambda$);
* **`tauTwo_binary_totallyPosDef`** (unconditional): $\tau = 2$ for every totally positive definite binary form over every
  totally real field, from `binaryTamagawaTwoReg_nf`;
* non-vacuity: `anisotropicF_of_isTotallyPosDef`, `exists_isDiscField_of_isTotallyPosDef`, `isTotallyPosDef_sumSq`
  ($x_0^2+x_1^2$).
-/

open MeasureTheory Measure Set Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.RegProd
  QuadFormsKB.NFEuler QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-! ### The statements -/

/-- **Weil's theorem $\tau(SO(V)) = 2$ for binary $V$, adelic form** (target statement; Ono's
$\tau(R^1_{E/F}\mathbb G_m) = 2$; Weil 1982, §2.4, p. 23 for $\tau(G) = \mathrm{vol}(G_{\mathbb A}/G_k)$ with convergence
factors): for every discriminant field $E$ of $Q_0$ (`IsDiscField`), the covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for
Weil's Tamagawa measure with the convergence factors of $\chi_E$ (`muTamBin`) is $2$. By `muTamBin_congr` the measure,
hence the statement, does not depend on the choice of $E$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k), convergence factors); ono1963 (τ(R^1_{E/F} G_m) = 2) [unverified]"]
def TauTwoBinaryAdelic (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [Algebra F E], IsDiscField Q₀ E →
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamBin Q₀ hQ E) = 2

variable (F) in
/-- **$\tau = 2$ for every anisotropic binary form over $F$** (target statement): every nondegenerate binary $Q_0$ over
$\mathcal O_F$ with $Q_0\otimes F$ anisotropic (any signature at the real places, complex places allowed) satisfies
`TauTwoBinaryAdelic`. Isotropic binary forms are excluded: there $SO(V)\cong\mathbb G_m$ and $\tau$ needs a different
definition. -/
@[kb "weil1982" "§2.4, p. 23; ono1963 (τ of the norm-one torus) [unverified]"]
def TauTwoBinaryAll : Prop :=
  ∀ (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate), AnisotropicF Q₀ → TauTwoBinaryAdelic Q₀ hQ

/-! ### The bridge to the regularized mass-formula normalization -/

section Bridge

variable [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 2)

/-- **The bridge:** for $F$ totally real and $Q_0$ totally positive definite,
$$\mathrm{covol}\bigl(SO(V)(F), SO(V)(\mathbb A), \mu^{\chi_E}_{\mathrm{Tam}}\bigr) = \tau^{\mathrm{reg}}(SO(Q_0))
  = |d_F|^{-1/2}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\cdot L(1,\chi)^{-1}\prod_v\frac{\alpha_v(L,L)}{1-\chi(v)/Nv}\cdot
  \mathrm{mass}_{SO},$$
`tauSOReg` (with the combinatorial character `chiP · Q₀`, equal to $\chi_E$ off a finite set). -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); Lemma 2.4.2, p. 26 (unfolding) [unverified]"]
theorem covolume_muTamBin_eq_tauSOReg (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (formF Q₀)) {E : Type} [Field E]
    [NumberField E] [Algebra F E] (h : IsDiscField Q₀ E) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamBin Q₀ hQ E) = ENNReal.ofReal (tauSOReg Q₀) := by
  have := countable_GammaSOAdele Q₀
  obtain ⟨S, hS⟩ := chiP_eq_chiE Q₀ h
  obtain ⟨hL0, hL⟩ := lOne_chiE h.finrank_eq_two
  have hχ := abs_chiE_le h.finrank_eq_two
  have hLi : IsIntegral (formF Q₀) (stdLat F 2).1 := isIntegral_stdLat Q₀
  have hreg : regProd (fun v => chiP v Q₀) (-1) (fun v => NF.siegelDensity v Q₀ Q₀) =
      (LOne (chiE F E))⁻¹ * finFactor Q₀ (lamL (chiE F E)) := by
    rw [regProd_congr_finite (abs_chiP_le Q₀) hχ S hS hL (-1) _
      (multipliable_siegelDensity_binary_reg hQ S hS), regProd, _root_.zpow_neg_one, finFactor_lamL_eq Q₀ hQ hχ]
  have hprod : 0 ≤ ∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram Q₀ σ) :=
    Finset.prod_nonneg fun σ _ => (archVolSO_detGram_pos Q₀ hQ σ).le
  have hff : 0 ≤ finFactor Q₀ (lamL (chiE F E)) := finFactor_nonneg Q₀ _
  have hcF : cF F 2 = |(discr F : ℝ)| ^ (-((2 : ℝ) * (2 - 1) / 4)) := by rw [cF]; norm_num
  rw [muTamBin, muTamChi, covolume_smul _ _ (by simpa using hL0),
    covolume_muTam_eq_covolume_muAdele Q₀ hQ two_pos hpd, covolume_muAdele Q₀ hQ two_pos hpd hLi,
    tauSOReg, tamagawaKReg, hreg, ← hcF]
  rw [← ENNReal.ofReal_prod_of_nonneg fun σ _ => (archVolSO_detGram_pos Q₀ hQ σ).le,
    ← ENNReal.ofReal_mul cF_nonneg, ← ENNReal.ofReal_mul (mul_nonneg cF_nonneg hprod),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg cF_nonneg hprod) hff), ← ENNReal.ofReal_mul (inv_nonneg.mpr hL0.le)]
  congr 1
  ring

/-- **$\tau(SO(V)) = 2$ for every totally positive definite binary form over every totally real field, adelic form**
(unconditional): the covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for Weil's Tamagawa measure with the convergence
factors $L_v(1,\chi_E)$ is $2$. From the bridge and `binaryTamagawaTwoReg_nf` (the mass formula of
$\mathcal O_F[\sqrt{-D}]$). -/
@[kb "weil1982" "§2.4, p. 23; Thm. 3.7.1 (τ = 2), rank 2 with convergence factors; ono1963 [unverified]"]
theorem tauTwo_binary_totallyPosDef (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (formF Q₀)) :
    TauTwoBinaryAdelic Q₀ hQ := by
  intro E _ _ _ h
  rw [covolume_muTamBin_eq_tauSOReg Q₀ hQ hpd h, binaryTamagawaTwoReg_nf.tau_eq_two Q₀ hpd]
  simp

end Bridge

end QuadFormsKB.Tamagawa.Measure.Weil
