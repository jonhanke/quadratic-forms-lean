/-
# Siegel's formula for forms by forms as an Euler product of degree-$r$ Whittaker integrals (Siegel–Weil for forms by forms)

**Layer:** $F$ a totally real number field; forms over $\mathcal O_F$.

**Setting.** $Q_0 = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, totally positive definite, $n = 2m$ (0-based indices);
$T_0$ a totally positive definite quadratic form in $r$ variables over $\mathcal O_F$, $1 \le r$, $n - r \ge 3$; $L = \mathcal O_F^n$.
$W_{T,v}$ = `whittakerR` is the local Whittaker integral of degree $r$ of the lattice section $f_v = f_{\mathbf 1_{L_v^r}}$ of the Weil
representation of $\mathrm{Sp}_{2r}(F_v)$ (`SiegelWeil/Forms/LocalWhittaker.lean`), at every finite place, dyadic included.

**Result** (`siegelForms_eq_whittaker`, **unconditional**):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\cdot\prod_\sigma\beta_\sigma(Q_0, T_0)\cdot
  (\gamma_{V,\infty}c_{B,\infty})^r\prod_{v<\infty}W_{T_0,v}(\mathbf 1_{L_v^r}).$$
Dividing by $\mathrm{Mass}(L)$, the left side is the $T_0$-th Fourier coefficient of the genus average of the degree-$r$ theta series
$\theta_M(Z) = \sum_{X\in M^r}e(\operatorname{tr}(Q_0[X]Z))$ (the coefficient of $e(\operatorname{tr}(T_GZ))$ in $\theta_M$ is $r_M(T_0)$). The right side
is the Euler product of the local Whittaker factors: Weil's factorization of the $T_0$-th Fourier coefficient of the Siegel Eisenstein series
$E(g, s_0, \Phi)$ at $s_0 = n/2 - (r+1)/2$, with the archimedean factor written as Siegel's density $\beta_\sigma(Q_0, T_0)$ (`archDensityForm`)
times the archimedean Weil constants. So the $T_0$-th coefficient of the Siegel–Weil identity in degree $r$ holds for every $T_0 \gg 0$.

*Proof:* Siegel's formula for forms by forms (`Tamagawa.Frames.siegelFormsAt_totallyReal_general`, unconditional) gives the left side as
$\mathrm{Mass}(L)\,|d_F|^{-r(2n-r-1)/4}\prod_\sigma\beta_\sigma\prod_\mathfrak p\beta_\mathfrak p(Q_0, T_0)$; the product of the densities converges
(`multipliable_localDensityForm`), so $\prod_vW_{T_0,v} = C_f^{(r)}\prod_\mathfrak p\beta_\mathfrak p$ (`hasProd_whittakerR`), and
$(\gamma_{V,\infty}c_{B,\infty})^rC_f^{(r)} = |d_F|^{-r(2n-r-1)/4}$ (`globalConstR_eq_rpow`).

**Not proved here.** The global Siegel Eisenstein series on $P(F)\backslash\mathrm{Sp}_{2r}(F)$ in degree $r \ge 2$, its convergence, and its
unfolding into $\prod_vW_{T,v}$; the archimedean Whittaker integral (Siegel's gamma integral in degree $r$); so the identity is stated at the
level of Fourier coefficients, not as an identity of functions on $\mathrm{Sp}_{2r}(\mathbb A)$.

Sources: Siegel, Ann. Math. 36 (1935), Hauptsatz [unverified]; Weil, Acta Math. 113 (1965), Ch. II–IV [unverified]; Kudla, *Some
extensions of the Siegel–Weil formula* (2008), §1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.GlobalWhittaker
import QuadFormsKB.SiegelWeil.Forms.DensityProduct

open IsDedekindDomain NumberField
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Frames Lattices

variable {F : Type} [Field F] [NumberField F] {m r : ℕ}

/-- **Siegel's formula for forms by forms as an Euler product of Whittaker integrals** (degree $r$, every finite place, dyadic
included; unconditional). For $F$ totally real, $Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m$, and $T_0$
totally positive definite in $r$ variables over $\mathcal O_F$ with $1 \le r$, $r + 3 \le n$, and $L = \mathcal O_F^n$:
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\cdot\prod_\sigma\beta_\sigma(Q_0, T_0)\cdot
  (\gamma_{V,\infty}c_{B,\infty})^r\prod_{v<\infty}W_{T_0,v}(\mathbf 1_{L_v^r}),$$
$W_{T_0,v}$ = `whittakerR` (the local Whittaker integral of degree $r$), $\beta_\sigma$ = `archDensityForm`, $\gamma_{V,\infty}$, $c_{B,\infty}$ the Weil
index and the self-dual constant of the archimedean model (`localDataInf`). -/
@[kb "weil1965" "Ch. II–IV (Siegel's formula as the Fourier coefficients of the Siegel–Weil identity, forms by forms) [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem siegelForms_eq_whittaker [IsTotallyReal F] (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (T₀ : QuadForm (𝓞 F) r) (hr : 1 ≤ r) (hrN : r + 3 ≤ 2 * m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    ((repMassT ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (stdLat F (2 * m)) (T₀.map (algebraMap (𝓞 F) F)) : ℝ) : ℂ) =
      (mass ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (stdLat F (2 * m)) : ℂ) *
        ((∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (2 * m) r (detGram (QuadForm.diag b) σ) (detGram T₀ σ) : ℝ) : ℂ) *
        (((localDataInf (F := F)).gammaV (aInf (unitsOfInt b hb)) *
            (localDataInf (F := F)).cB (aInf (unitsOfInt b hb))) ^ r *
          ∏' v : HeightOneSpectrum (𝓞 F), whittakerR v (aOfInt v b hb)
            ((LocalDensity.NF.Qp v T₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)))) := by
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hS := (siegelFormsAt_totallyReal_general (QuadForm.diag b) T₀ hr hrN hpd hpdT).repMass_eq
  have hmult := multipliable_localDensityForm (QuadForm.diag b) T₀ hr hrN hpd hpdT
  have hW := (hasProd_whittakerR r (by omega) b hb T₀ hT hmult.hasProd).tprod_eq
  have hC := globalConstR_eq_rpow (unitsOfInt b hb) r (m := m) (by omega)
  have hdens : (∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v (QuadForm.diag b) T₀) =
      ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.localDensityForm v (QuadForm.diag b) T₀ :=
    tprod_congr fun v => by
      unfold LocalDensity.NF.siegelDensity
      rw [if_neg (by omega), one_mul]
  have heps1 : epsCodimOne (2 * m) r = 1 := by unfold epsCodimOne; rw [if_neg (by omega)]
  have heps2 : epsNR (2 * m) r = 1 := by unfold epsNR; rw [if_neg (by omega)]
  rw [hS, hW, ← mul_assoc _ (constFinR _ _), hC]
  unfold siegelProductT
  rw [hdens, heps1]
  simp only [heps2, one_mul]
  push_cast
  ring

end QuadFormsKB.SiegelWeil.Forms
