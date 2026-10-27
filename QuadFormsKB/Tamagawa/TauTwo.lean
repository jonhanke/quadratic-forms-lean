import QuadFormsKB.Tamagawa.AdditiveGenus
import QuadFormsKB.Tamagawa.SphericalResidue
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal

/-!
# Weil's Theorem 4.5.1: $\tau(SO(V)) = 2$ by comparing the two residues

**Setting.** $F$ totally real, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n \ge 5$ variables with $Q = Q_0\otimes F$
totally positive definite, $L = \mathcal O_F^n$ (genus free: `GenusFree`, automatic for $\mathcal O_F$ a PID), $G = SO(V)$,
$\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ with the Gaussian $\Phi_w = e^{-\pi Q_w}$ (`GlobalZeta.gaussian Q₀ π`).

**Weil's argument** (A. Weil, *Adeles and Algebraic Groups*, 1982, §4.5, pp. 108–109, Theorem 4.5.1, p. 109). The spherical
sum $Z(s) = \sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho)$ ((2), p. 102; `SphericalZeta.sphericalZeta`) has two residues at $s = 0$:
1. *multiplicatively* ((8), p. 108; `SphericalZeta.tendsto_mul_sphericalZeta_zero_gaussian`):
   $\lim_{s\to0^+}sZ(s) = \rho_F\int_{V(\mathbb A)}\Phi\,dx$;
2. *additively* (p. 109; `AdditiveZeta.tendsto_mul_sphericalSum`): if Weil's unfolding over the spheres holds
   (`SphericalFibration`: $Z^+(s) = \sum_\rho\frac{\tau'_\rho}2Z(s,\rho)$) and the stabilizers have $\tau'_\rho = 2$
   (`ComplementTauTwo`, the induction hypothesis), then $\lim_{s\to0^+}sZ(s) = \frac{\rho_F}2\,\tau(G)\int_{V(\mathbb A)}\Phi\,dx$.

Since $\rho_F > 0$ and $\int\Phi > 0$, $\tau(G) = 2$ (`tamagawaNumberTwo_of_sphericalFibration`).

**Corollaries.** The mass formula in rank $n$ (`massFormula`: $\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$,
`massFormula_of_sphericalFibration`), and Siegel's formula for numbers (`siegelFormulaAt_of_sphericalFibration`, via the
`siegelFormulaAt_of_tamagawa`, for $Q_0 = \langle m\rangle\perp Q_0'$ split, with $\tau = 2$ in rank $n - 1$ for $Q_0'$).

**Hypothesis hygiene.** The two inputs are the named structures. Neither mentions $\tau(SO(V))$: `SphericalFibration`
is an identity between the additive zeta function $Z^+$ (a sum over the classes of the genus with the weights) and the
spherical zeta functions with the constants $\tau'_\rho$; `ComplementTauTwo` says $\tau'_\rho = 2$. The value of $\tau(SO(V))$ is
**computed** from the comparison of residues. The status of `SphericalFibration` (what is proved of it, and what remains) is
in `SphericalFibration.lean`.
-/

open NumberField Filter Topology
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.TauTwo

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalZeta
open QuadFormsKB.GlobalZeta

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- The spherical zeta functions as a family indexed by the square classes $c \in F^\times/F^{\times2}$:
$Z_c(s) = Z(s,\rho_c)$ at the representative $\rho_c$ = `Quotient.out c` (the terms of `sphericalZeta`), for the Gaussian
$\Phi_w = e^{-\pi Q_w}$. -/
def sphFamily (Q₀ : QuadForm (𝓞 F) n) : SqClasses F → ℝ → ℝ :=
  fun c s => sphericalZetaAt Q₀ (gaussian Q₀ π) ((Quotient.out c : Fˣ) : F) s

lemma tsum_sphFamily (Q₀ : QuadForm (𝓞 F) n) (s : ℝ) :
    ∑' c, sphFamily Q₀ c s = sphericalZeta Q₀ (gaussian Q₀ π) s := rfl

/-- **Totally positive definite, real form**: if $Q_0\otimes F$ is totally positive definite on $F^n$, then each real form
$Q_w$ is positive definite on $\mathbb R^n$ (`GlobalZeta.IsTotallyPosDef`). Via the Gram matrix: $Q_w(x) = x^{\mathsf T}\varphi_w(A)x$
with $\varphi_w(A)$ positive definite (`isTotPosGram_of_isTotallyPosDef`). -/
theorem globalZeta_isTotallyPosDef (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀)) :
    GlobalZeta.IsTotallyPosDef Q₀ := by
  intro w x hx
  rw [realVal_eq_dotProduct]
  exact (isTotPosGram_of_isTotallyPosDef hpd w.1).dotProduct_mulVec_pos hx

/-- $\int_{V(\mathbb A)}\Phi\,dx > 0$ for the Gaussian ($= c_L > 0$). -/
theorem phiIntegral_gaussian_pi_pos (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀)) :
    0 < phiIntegral (gaussian Q₀ π) := by
  rw [phiIntegral_gaussian_pi Q₀ (isTotPosGram_of_isTotallyPosDef hpd)]
  exact latConst_pos (isTotPosGram_of_isTotallyPosDef hpd) _

/-- **Weil's Theorem 4.5.1 (the induction step): $\tau(SO(V)) = 2$** (Weil 1982, §4.5, Thm 4.5.1, p. 109; the comparison of
the residues of the spherical sum $Z(s) = \sum_\rho Z(s,\rho)$, (2) and (8), p. 108, with the additive residue $\rho_k\tau(G)/2$,
p. 109). For $F$ totally real, $Q_0$ nondegenerate over $\mathcal O_F$ in $n \ge 5$ variables with $Q_0\otimes F$ totally
positive definite and the genus of $\mathcal O_F^n$ free: **if** Weil's unfolding over the spheres holds for the spherical
zeta functions $Z(s,\rho)$ of the Gaussian $\Phi_w = e^{-\pi Q_w}$ (`SphericalFibration Q₀ (sphFamily Q₀) τ'`, indexed by
$F^\times/F^{\times2}$) **and** the stabilizers have Tamagawa number $2$ (`ComplementTauTwo τ'`, the induction hypothesis in rank
$n - 1$), **then** $\tau(SO(V)) = 2$ (`TamagawaNumberTwo Q₀`, with `tauSO`).

*Proof.* $\lim_{s\to0^+}sZ(s) = \rho_F\int\Phi$ and $= \frac{\rho_F}2\tau(G)\int\Phi$; limits in $\mathcal N_{>}(0)$ are
unique, and $\rho_F\int\Phi \ne 0$. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109 (comparison of residues, (8) p. 108 and p. 109)"]
theorem tamagawaNumberTwo_of_sphericalFibration (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 5 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) (hfree : GenusFree (formF Q₀) stdLat) {τ' : SqClasses F → ℝ}
    (hfib : SphericalFibration Q₀ (sphFamily Q₀) τ') (htwo : ComplementTauTwo τ') :
    Tamagawa.TamagawaNumberTwo Q₀ := by
  have hA := tendsto_mul_sphericalSum Q₀ hQ (by omega) hpd hfree hfib htwo
  have hM := tendsto_mul_sphericalZeta_zero_gaussian Q₀ hQ (globalZeta_isTotallyPosDef Q₀ hpd) hn Real.pi_pos
  simp_rw [tsum_sphFamily] at hA
  have heq := tendsto_nhds_unique hA hM
  have hρ := dedekindZeta_residue_pos F
  have hI := phiIntegral_gaussian_pi_pos Q₀ hpd
  unfold Tamagawa.TamagawaNumberTwo
  have h' : dedekindZeta_residue F * phiIntegral (gaussian Q₀ π) * (Tamagawa.tauSO Q₀ - 2) = 0 := by
    linear_combination 2 * heq
  rcases mul_eq_zero.mp h' with h | h
  · exact absurd h (mul_pos hρ hI).ne'
  · linarith

/-- **Weil's Theorem 4.5.1 for $h_F = 1$**: as `tamagawaNumberTwo_of_sphericalFibration`, with `GenusFree` discharged
(`genusFree_of_isPrincipalIdealRing`). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem tamagawaNumberTwo_of_sphericalFibration_of_pid [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hn : 5 ≤ n) (hpd : IsTotallyPosDef (formF Q₀)) {τ' : SqClasses F → ℝ}
    (hfib : SphericalFibration Q₀ (sphFamily Q₀) τ') (htwo : ComplementTauTwo τ') :
    Tamagawa.TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_sphericalFibration Q₀ hQ hn hpd (genusFree_of_isPrincipalIdealRing _ _) hfib htwo

/-- **The mass formula in rank $n \ge 5$ from the induction step** (`massFormula` with Weil's $\tau = 2$):
$\mathrm{Mass}(\mathcal O_F^n) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$, given `SphericalFibration` and `ComplementTauTwo`. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_of_sphericalFibration (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 5 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) (hfree : GenusFree (formF Q₀) stdLat) {τ' : SqClasses F → ℝ}
    (hfib : SphericalFibration Q₀ (sphFamily Q₀) τ') (htwo : ComplementTauTwo τ') :
    mass (formF Q₀) (Tamagawa.stdLat F n) = (Tamagawa.tamagawaK Q₀)⁻¹ :=
  Tamagawa.massFormula Q₀ hQ (by omega) hpd (isIntegral_stdLat Q₀)
    (tamagawaNumberTwo_of_sphericalFibration Q₀ hQ hn hpd hfree hfib htwo)

/-- **Siegel's formula for the number $m$ in rank $n + 1 \ge 5$** from Weil's induction step: for the split
form $Q_0 = \langle m\rangle\perp Q_0'$, $\tau = 2$ in rank $n+1$ comes from `tamagawaNumberTwo_of_sphericalFibration`, and $\tau = 2$
for $Q_0'$ (rank $n$) is the hypothesis `hτ'`; `siegelFormulaAt_of_tamagawa` (with the local orbital identity at
$\mathfrak p \mid 2m$, `hbad`) gives $\sum_{\mathrm{cls}(M)}r_M(m)/|O(M)| = \mathrm{Mass}(L)\,S(L,m)$. -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem as a formal consequence of τ = 2), Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_of_sphericalFibration (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hn : 4 ≤ n)
    (hpd : IsTotallyPosDef (formF (Tamagawa.splitForm m Q₀')))
    (hfree : GenusFree (formF (Tamagawa.splitForm m Q₀')) stdLat) {τ' : SqClasses F → ℝ}
    (hfib : SphericalFibration (Tamagawa.splitForm m Q₀') (sphFamily (Tamagawa.splitForm m Q₀')) τ')
    (htwo : ComplementTauTwo τ')
    (hbad : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal →
      Tamagawa.LocalOrbitalIdentityAt v Q₀' m)
    (hτ' : Tamagawa.TamagawaNumberTwo Q₀') : Tamagawa.SiegelFormulaAt (Tamagawa.splitForm m Q₀') m := by
  have hQ : (Tamagawa.splitForm m Q₀').Nondegenerate := Tamagawa.nondegenerate_of_map hpd.nondegenerate
  exact Tamagawa.siegelFormulaAt_of_tamagawa m hm Q₀' (by omega) hpd (isIntegral_stdLat _) hbad
    (tamagawaNumberTwo_of_sphericalFibration _ hQ (by omega) hpd hfree hfib htwo) hτ'

end QuadFormsKB.TauTwo
