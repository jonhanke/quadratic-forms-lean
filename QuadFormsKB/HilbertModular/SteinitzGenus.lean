/-
# The genus of $\mathcal O_F^n$ is free, for every totally real $F$

**Setting.** $F$ a totally real number field (any class number), $Q_0$ a totally positive definite form over $\mathcal O_F$ in
$n = 2k$ variables, $L = \mathcal O_F^n$ (`stdLat`).

**Main results.**
* **`genusFree_of_nondegenerate`**, **`genusFree_formF`**: The hypothesis `GenusFree` holds for every nondegenerate $Q$ over every
  number field (Steinitz, `Lattices.Steinitz.exists_latOf_of_sameGenus`): every lattice in the genus of $\mathcal O_F^n$ is
  $\gamma\mathcal O_F^n$. Before, it was proved only for $\mathcal O_F$ a PID (`genusFree_of_isPrincipalIdealRing`).
* Consequently, without $[\texttt{IsPrincipalIdealRing}\ \mathcal O_F]$:
  - `thetaGen_mem_modularFormChar'`: $\theta_{\mathrm{Gen}} \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$;
  - **`thetaGen_sub_eisQ_mem_cuspFormChar'`** ($k \ge 3$) and `thetaGen_sub_eisQ2_mem_cuspFormChar'` ($k = 2$, $d \ge 2$):
    $\theta_{\mathrm{Gen}} - E_Q$ is a cusp form;
  - **`eisQ_coeff_eq_discr_mul_aENF'`**: $a_\nu(E_Q) = |d_F|^{-(n-1)/2}\,\mathrm{aENF}(\nu)$ for $\nu \gg 0$, $k \ge 3$;
  - **`eisHeckeRel_eisQ'`**: `EisHeckeRel Q₀ (eisQ Q₀ k)` (the $T(\pi^2)$ relations of $E_Q$ at prime elements $\pi$).

The theta series treated earlier are those of free lattices; this file shows that no non-free lattice occurs in the
genus of $\mathcal O_F^n$, so the modularity suffices for $\theta_{\mathrm{Gen}}$ (lattices with nontrivial Steinitz
class only enter the Hecke argument at non-principal primes).

Sources: Steinitz (1911); O'Meara (1963), 81:5, p. 212, §82, pp. 220–238.
-/
import QuadFormsKB.Lattices.Steinitz
import QuadFormsKB.HilbertModular.EisHecke
import QuadFormsKB.HilbertModular.Cuspidal2

open NumberField Complex
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **The genus of $\mathcal O_F^n$ is free** for every nondegenerate $Q$ on $F^n$ and every number field $F$ (`GenusFree`, no class-number
hypothesis): every lattice $M$ in the genus of $\mathcal O_F^n$ is $\gamma\mathcal O_F^n$. -/
@[kb "omeara1963" "§82, §102A, p. 297 (genus); §81A, 81:5, p. 212 (Steinitz form)"]
theorem genusFree_of_nondegenerate (Q : QuadForm F n) (hQ : Q.Nondegenerate) : GenusFree Q stdLat :=
  fun M hM => Steinitz.exists_latOf_of_sameGenus Q hQ M.2 hM

/-- **`GenusFree` for a totally positive definite form over $\mathcal O_F$** (every totally real $F$). -/
@[kb "omeara1963" "§102A, p. 297 (genus); §81A, 81:5, p. 212"]
theorem genusFree_formF [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) :
    GenusFree (formF Q₀) stdLat :=
  genusFree_of_nondegenerate _ hQ.nondegenerate

variable [IsTotallyReal F]

section C5a

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)

include hQ hn hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} \in M_k(\Gamma_0(\mathfrak N), \chi_{Q_0})$ for every totally real $F$** (without $h_F = 1$). -/
@[kb "siegel1935" "θ_Gen is modular with the theta character, over F, any class number [unverified]"]
theorem thetaGen_mem_modularFormChar' :
    thetaGen (formF Q₀) stdLat ∈ modularFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k :=
  thetaGen_mem_modularFormChar hQ hn hlev h𝔑 (genusFree_formF hQ)

include hQ hn hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} - E_Q \in S_k(\Gamma_0(\mathfrak N), \chi_Q)$, $k \ge 3$, for every totally real $F$** (without $h_F = 1$). -/
@[kb "siegel1935" "θ_Gen − E_Q is a cusp form, over F, any class number [unverified]"]
theorem thetaGen_sub_eisQ_mem_cuspFormChar' (hk : 3 ≤ k) :
    thetaGen (formF Q₀) stdLat - eisQ Q₀ k ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k :=
  thetaGen_sub_eisQ_mem_cuspFormChar hQ hn hlev h𝔑 hk (genusFree_formF hQ)

include hQ hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} - E_Q \in S_2(\Gamma_0(\mathfrak N), \chi_Q)$ for quaternary forms, every totally real $F$ of degree $d \ge 2$**
(without $h_F = 1$). -/
@[kb "siegel1935" "θ_Gen − E_Q ∈ S₂, over F, any class number [unverified]"]
theorem thetaGen_sub_eisQ2_mem_cuspFormChar' (hn : n = 2 * 2) (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    thetaGen (formF Q₀) stdLat - eisQ2 Q₀ 𝔑 h𝔑 ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) 2 :=
  thetaGen_sub_eisQ2_mem_cuspFormChar hQ hn hlev h𝔑 hd (genusFree_formF hQ)

end C5a

/-- **The coefficients of $E_Q$ for every totally real $F$**: $a_\nu(E_Q) = |d_F|^{-(n-1)/2}\,\mathrm{aENF}(\nu)$ for
$\nu \in \mathcal O_F$ totally positive, $n = 2k \ge 6$ (no class-number hypothesis). -/
@[kb "hanke2004" "(5.3) with the corrected constant, Fourier coefficients of E_Q over F, any class number"]
theorem eisQ_coeff_eq_discr_mul_aENF' {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑)
    (h𝔑 : 𝔑 ≠ ⊥) (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO ν)) =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν : ℝ) : ℂ) :=
  eisQ_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 (genusFree_formF hQ) hk hν

/-- **The $T(\pi^2)$ relations for every totally real $F$**: `EisHeckeRel Q₀ (eisQ Q₀ k)` for $k \ge 3$ (no
class-number hypothesis). The relations are stated at prime elements $\pi$, i.e. at the principal primes
$\mathfrak p = (\pi)$. -/
@[kb "shimura1978" "T(π²) relations for E_Q over F, any class number [unverified]"]
theorem eisHeckeRel_eisQ' {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑)
    (h𝔑 : 𝔑 ≠ ⊥) (hk : 3 ≤ k) : EisHeckeRel Q₀ (eisQ Q₀ k) :=
  eisHeckeRel_eisQ hQ hn hlev h𝔑 (genusFree_formF hQ) hk

end QuadFormsKB.HilbertModular

end
