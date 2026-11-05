/-
# The Siegel–Weil formula of degree $\le R$ from the Fourier expansion of the Eisenstein series alone

**Layer:** global over a totally real number field $F$ whose ring of integers $\mathcal O_F$ is a principal ideal domain.

**Setting.** $Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite with $b_i \in \mathcal O_F$, $n = 2m$, $L = \mathcal O_F^n$, $\Phi_v = \mathbf 1_{L_v^r}$;
a degree bound $R$ with $m > 4R^2$; $\mathcal E^{(r)}(Z) = \det(\operatorname{Im}Z)^{-m/2}E^{(r)}(g_Z, s_0, \Phi)$ (`eisHolR`) and the genus theta series
$\theta^{(r)}_{\mathrm{gen}(L)}$ (`thetaGenR`).

**Result.** **`eisHolR_eq_thetaGenR_of_expansion_only`**: suppose that for every $r \le R$ the function $\mathcal E^{(r)}$ has *some* absolutely
convergent Fourier expansion $\sum_Ta_r(T)e_T$ on $\mathbb H_r^d$ with $a_r(T) \ne 0$ only for totally positive semidefinite $T$. Then $\mathcal E^{(r)} = \theta^{(r)}_{\mathrm{gen}(L)}$ on $\mathbb H_r^d$ for every $r \le R$, i.e.
$$E^{(r)}(g_Z, s_0, \Phi) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\frac1{\mathrm{Mass}(L)}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M(Z)}{|O(M)|}.$$
*Proof.* The assembly `eisHolR_eq_thetaGenR_of_expansion` with its nonsingular-coefficient hypothesis supplied by
`eisHolR_coeff_full` (lower cells, big cell, orthogonality, periodicity under $\mathrm{Sym}_r(\mathfrak d^{-1})$).

Sources: Weil, Acta Math. 113 (1965) [unverified]; Kudla–Rallis, J. reine angew. Math. 387 (1988) [unverified]; Siegel, Ann. of Math. 36
(1935) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinCoeffFull
import QuadFormsKB.SiegelWeil.Forms.SiegelWeilAssembly

open Matrix NumberField
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

/-- **Siegel–Weil of degree $\le R$, given only the Fourier expansion of the Eisenstein series** (see the module docstring). -/
@[kb "weil1965" "Ch. IV (Siegel–Weil formula) [unverified]; kudlaRallis1988 [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem eisHolR_eq_thetaGenR_of_expansion_only [IsPrincipalIdealRing (𝓞 F)] {m : ℕ} (b : Fin (2 * m) → 𝓞 F)
    (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map ιO)) (R : ℕ) (hm : 4 * (R : ℝ) ^ 2 < m)
    (a : ∀ r : ℕ, QuadForm F r → ℂ)
    (hsum : ∀ r ≤ R, ∀ Z ∈ siegelHF F r, Summable fun T => ‖a r T * eT T Z‖)
    (hexp : ∀ r ≤ R, ∀ Z ∈ siegelHF F r, HasSum (fun T => a r T * eT T Z) (eisHolR (r := r) b hb hbpos Z))
    (hpsd : ∀ r ≤ R, ∀ T, a r T ≠ 0 → IsTotPSD T) :
    ∀ r ≤ R, ∀ Z ∈ siegelHF F r,
      eisHolR b hb hbpos Z = thetaGenR ((QuadForm.diag b).map ιO) (Tamagawa.stdLat F (2 * m)) Z := by
  refine eisHolR_eq_thetaGenR_of_expansion b hb hbpos hpd (Tamagawa.stdLat F (2 * m))
    (Tamagawa.Frames.isIntegral_stdLat_map (QuadForm.diag b)) R hm a hsum hexp hpsd ?_
  intro r hr1 hrR T hT
  have hmr : 4 * (r : ℝ) ^ 2 < m := by
    have h1 : (r : ℝ) ≤ R := by exact_mod_cast hrR
    have h0 : (0 : ℝ) ≤ r := by positivity
    nlinarith
  exact eisHolR_coeff_full b hb hbpos hr1 hmr hpd (hsum r hrR) (hexp r hrR) (hpsd r hrR) T hT

end QuadFormsKB.SiegelWeil.Forms
