import QuadFormsKB.Tamagawa.Unitary.Unfold
import QuadFormsKB.Tamagawa.Unitary.TauInput

/-!
# The hermitian mass formula from $\tau(U(V)) = 2$

**Layer:** Gan–Hanke–Yu's setting (Gan–Hanke–Yu 2001, §4) as in `Global.lean` and `TauInput.lean`: $F$ totally real, $E = F(\theta)$,
$\theta^2 = -D$, $\chi = \chi_{E/F}$, $H_0$ a nondegenerate totally definite integral hermitian $m\times m$ matrix over
$\mathcal O_F[\omega]$, $\Lambda = \mathcal O_F[\omega]^m$.

**The mass.** $\mathrm{mass}(\Lambda) = \sum_{\alpha}1/\#\big(U(V)(F)\cap\alpha\,U(\hat\Lambda)\alpha^{-1}\big)$ over the finitely many
double cosets $U(V)(F)\,\alpha\,U(\hat\Lambda)$ in $U(V)(\mathbb A_f)$ (`dcMass (GammaUf D H₀) (KU D H₀)`; Gan–Hanke–Yu (4.1): the sum of
$1/\#\Gamma_i$ over the classes in the genus of $\Lambda$; finiteness is `finite_orbits_U`).

**Proves**
* `tauU_eq_two_iff`: $\tau(U(V)) = 2$ iff $L(1,\chi)^{-1}|d_F|^{-m^2/2}\prod_\rho\mu_\rho\cdot\prod_v\mu_v(U(\Lambda_v))\cdot\mathrm{mass} = 2$
  (from the unfolding `tauU_eq`, unconditional);
* **`massFormulaU`** (conditional on the named input `TauUnitaryTwo`): the identity above, and its real form
  **`massFormulaU_real`**
  $$\mathrm{mass}(\Lambda) = \frac{2}{L(1,\chi)^{-1}\,|d_F|^{-m^2/2}\prod_\rho\mu_\rho(U(V)(F_\rho))\prod_v\mu_v(U(\Lambda_v))},$$
  with every factor of the denominator positive (`massFormulaU_factors_pos`). Here $\mu_\rho(U(V)(F_\rho))$ = `archDensityU`
  and $\prod_v\mu_v(U(\Lambda_v))$ = `finFactorU` $=\prod_v\beta^h_v/\lambda_v$ (where the $\beta^h_v/\lambda_v\ge0$, `finFactorU_eq`;
  at the places $v\nmid2D\,N(\det H_0)$, $\beta^h_v = \prod_{i=1}^m(1-(\chi(v)/q_v)^i)$, `hermDensity_eq_good`).

This is the unitary analogue of the Smith–Minkowski–Siegel mass formula in Weil's form (Weil 1982, §2.4; Gan–Hanke–Yu (2.6)–(2.7)
before the Bruhat–Tits evaluation of the local volumes). Gan–Hanke–Yu's Props 4.4/4.5 additionally evaluate the local factors at
the bad places through Bruhat–Tits theory (`UnitaryProp213`, parked).
-/

open MeasureTheory Measure MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Lattices QuadFormsKB.Siegel NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (H₀ : Matrix (Fin m) (Fin m) (QuadO D))

/-- **$\tau(U(V)) = 2$ is the mass formula** (definite case, $F$ totally real; unconditional equivalence, from the unfolding
`tauU_eq`). -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)) [unverified]; ganhankeyu2001 (4.1), (4.3), pp. 109–110"]
theorem tauU_eq_two_iff [IsTotallyReal F] [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (hD : D ≠ 0)
    (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    tauU D H₀ hD hH hdet E = 2 ↔
      ENNReal.ofReal (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ *
        ENNReal.ofReal (|(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2))) *
        (∏ ρ : F →+* ℝ, ENNReal.ofReal (archDensityU D H₀ ρ)) *
        ENNReal.ofReal (finFactorU D H₀ (lamL (chiE F E))) *
        ENNReal.ofReal (dcMass (GammaUf D H₀) (KU D H₀)) = 2 := by
  rw [tauU_eq D H₀ hD hH hdet (isTotallyPosDef_traceQFF D H₀) E]

/-- **The hermitian mass formula** (Gan–Hanke–Yu 2001, (4.1) with (4.3); Weil's form), **conditional on the named input
`TauUnitaryTwo`** ($\tau(U(V)) = 2$, Kottwitz/Ono):
$$L(1,\chi)^{-1}\,|d_F|^{-m^2/2}\prod_\rho\mu_\rho(U(V)(F_\rho))\cdot\prod_v\mu_v(U(\Lambda_v))\cdot\mathrm{mass}(\Lambda) = 2.$$ -/
@[kb "ganhankeyu2001" "(4.1), (4.3), p. 109–110 (Mass(K) with τ(G) = 2)"]
theorem massFormulaU [IsTotallyReal F] [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (hm : 1 ≤ m)
    (hD : D ≠ 0) (hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-D))) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] {θ : 𝓞 E}
    (hθ : Binary.Rel.conjO F E θ = -θ) (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2)
    (I : TauUnitaryTwo D H₀ hm hD hsq hH hdet E hθ hθD) :
    ENNReal.ofReal (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ *
        ENNReal.ofReal (|(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2))) *
        (∏ ρ : F →+* ℝ, ENNReal.ofReal (archDensityU D H₀ ρ)) *
        ENNReal.ofReal (finFactorU D H₀ (lamL (chiE F E))) *
        ENNReal.ofReal (dcMass (GammaUf D H₀) (KU D H₀)) = 2 :=
  (tauU_eq_two_iff D H₀ hD hH hdet E).mp I.tau_eq

/-- **The local factors are positive** under `TauUnitaryTwo` ($L(1,\chi) > 0$, every $\mu_\rho(U(V)(F_\rho)) > 0$,
$\prod_v\mu_v(U(\Lambda_v)) > 0$, $\mathrm{mass} > 0$): a product of `ENNReal.ofReal`s equal to $2$ has no factor $0$. -/
theorem massFormulaU_factors_pos [IsTotallyReal F] [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (hm : 1 ≤ m)
    (hD : D ≠ 0) (hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-D))) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] {θ : 𝓞 E}
    (hθ : Binary.Rel.conjO F E θ = -θ) (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2)
    (I : TauUnitaryTwo D H₀ hm hD hsq hH hdet E hθ hθD) :
    0 < (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ ∧ (∀ ρ : F →+* ℝ, 0 < archDensityU D H₀ ρ) ∧
      0 < finFactorU D H₀ (lamL (chiE F E)) ∧ 0 < dcMass (GammaUf D H₀) (KU D H₀) := by
  have h := massFormulaU D H₀ hm hD hsq hH hdet E hθ hθD I
  have hne : ENNReal.ofReal (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ *
        ENNReal.ofReal (|(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2))) *
        (∏ ρ : F →+* ℝ, ENNReal.ofReal (archDensityU D H₀ ρ)) *
        ENNReal.ofReal (finFactorU D H₀ (lamL (chiE F E))) *
        ENNReal.ofReal (dcMass (GammaUf D H₀) (KU D H₀)) ≠ 0 := by rw [h]; norm_num
  simp only [ne_eq, mul_eq_zero, not_or, ENNReal.ofReal_eq_zero, not_le, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, not_exists] at hne
  obtain ⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩ := hne
  exact ⟨h1, h3, h4, h5⟩

/-- **The hermitian mass formula, real form** (conditional on `TauUnitaryTwo`):
$$\mathrm{mass}(\Lambda) = \frac{2}{L(1,\chi)^{-1}\,|d_F|^{-m^2/2}\prod_\rho\mu_\rho(U(V)(F_\rho))\prod_v\mu_v(U(\Lambda_v))}.$$ -/
@[kb "ganhankeyu2001" "(4.1), (4.3), p. 109–110 (Mass(K) with τ(G) = 2)"]
theorem massFormulaU_real [IsTotallyReal F] [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (hm : 1 ≤ m)
    (hD : D ≠ 0) (hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-D))) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] {θ : 𝓞 E}
    (hθ : Binary.Rel.conjO F E θ = -θ) (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2)
    (I : TauUnitaryTwo D H₀ hm hD hsq hH hdet E hθ hθD) :
    dcMass (GammaUf D H₀) (KU D H₀) =
      2 / ((QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ * |(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2)) *
        (∏ ρ : F →+* ℝ, archDensityU D H₀ ρ) * finFactorU D H₀ (lamL (chiE F E))) := by
  obtain ⟨h1, h3, h4, h5⟩ := massFormulaU_factors_pos D H₀ hm hD hsq hH hdet E hθ hθD I
  have h := massFormulaU D H₀ hm hD hsq hH hdet E hθ hθD I
  have h2 : 0 ≤ |(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2)) := Real.rpow_nonneg (abs_nonneg _) _
  rw [← ENNReal.ofReal_prod_of_nonneg (fun ρ _ => (h3 ρ).le), ← ENNReal.ofReal_mul h1.le,
    ← ENNReal.ofReal_mul (mul_nonneg h1.le h2),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h1.le h2) (Finset.prod_nonneg fun ρ _ => (h3 ρ).le)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg h1.le h2)
      (Finset.prod_nonneg fun ρ _ => (h3 ρ).le)) h4.le)] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1.le h2)
    (Finset.prod_nonneg fun ρ _ => (h3 ρ).le)) h4.le) h5.le), ENNReal.toReal_ofNat] at h'
  have hden : (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ * |(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2)) *
      (∏ ρ : F →+* ℝ, archDensityU D H₀ ρ) * finFactorU D H₀ (lamL (chiE F E)) ≠ 0 := by
    have : 0 < |(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2)) := by
      refine Real.rpow_pos_of_pos (abs_pos.mpr ?_) _
      exact_mod_cast discr_ne_zero F
    exact (mul_pos (mul_pos (mul_pos h1 this) (Finset.prod_pos fun ρ _ => h3 ρ)) h4).ne'
  rw [eq_div_iff hden]
  linear_combination h'

end QuadFormsKB.Tamagawa.Unitary
