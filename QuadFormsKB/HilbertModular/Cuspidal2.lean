/-
# Weight 2: $\theta_{\mathrm{Gen}} - E_Q$ is a cusp form for quaternary forms over a totally real field

**Setting** (as in `Cuspidal.lean`, with $k = 2$): $F$ totally real of degree $d \ge 2$, $Q_0$ a totally positive definite form over
$\mathcal{O}_F$ in $n = 4$ variables, $\mathfrak N \ne 0$ a theta level of $Q_0$ (`IsThetaLevelF`), $\chi_Q$ its character (`thetaCharF`), and the
genus of $\mathcal{O}_F^4$ free (`GenusFree`; proved for $\mathcal{O}_F$ a PID).

**The Eisenstein series of the genus in weight 2** (`eisQ2`): $E_Q = E^{(2)}_{\theta_{\mathrm{Gen}}}$ of `EisensteinGenus2.lean`, a finite
combination $\sum_C\sum_ra_r\,E_2(\cdot; \Phi_{C,\mathfrak d_r})$ of the weight-2 series (Hecke's trick) of periodic weights. Its weights
are determined by the cusp values of $\theta_{\mathrm{Gen}}$, which equal those of $\theta_{Q_0}$ (`thetaCuspVal`): on the vectors $x$ with
ideal $\mathfrak b_C$, $\Phi_C(x) = \varphi_{\theta}(x) = $ `thetaCuspVal Q₀ 2 (cuspMat x₁ (-x₀))` (`perExt_eq_phiF`).

**Main results** ($d \ge 2$, $n = 4$):
* `eisQ2_mem_modularFormChar`: $E_Q \in M_2(\Gamma_0(\mathfrak N), \chi_Q)$;
* `tendsto_eisQ2_slash`: $E_Q\,|_2\,A \to$ `thetaCuspVal Q₀ 2 A` at every cusp;
* **`thetaGen_sub_eisQ2_mem_cuspFormChar`**: $\theta_{\mathrm{Gen}} - E_Q \in S_2(\Gamma_0(\mathfrak N), \chi_Q)$ (and `_of_pid`);
* `thetaLatt_sub_eisQ2_mem_cuspFormChar`: $\theta_M - E_Q \in S_2(\Gamma_0(\mathfrak N), \chi_Q)$ for $M$ in the genus.

Sources: Siegel (1935) [unverified]; Hecke (1927) [unverified]; Shimura (Duke 1978), §3 [unverified].
-/
import QuadFormsKB.HilbertModular.Cuspidal
import QuadFormsKB.HilbertModular.EisensteinGenus2

open Matrix NumberField Complex Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **The weight-2 Eisenstein series of the genus of $Q_0$** at level $\mathfrak N$: $E_Q = E^{(2)}_{\theta_{\mathrm{Gen}}}$ (`eisGen2`).
Parameters: `Q₀` (the form), `𝔑` (the level), `h𝔑 : 𝔑 ≠ ⊥`. -/
@[kb "siegel1935" "the Eisenstein series of the genus in weight 2, over F [unverified]"]
noncomputable def eisQ2 (Q₀ : QuadForm (𝓞 F) n) (𝔑 : Ideal (𝓞 F)) (h𝔑 : 𝔑 ≠ ⊥) :
    (InfinitePlace F → UpperHalfPlane) → ℂ :=
  eisGen2 (thetaGen (formF Q₀) stdLat) 𝔑 h𝔑

section Main

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hd : 2 ≤ Fintype.card (InfinitePlace F))

include hQ hn hlev h𝔑 hd in
/-- **$E_Q \in M_2(\Gamma_0(\mathfrak N), \chi_Q)$** ($n = 4$, $d \ge 2$, free genus). -/
@[kb "siegel1935" "E_Q ∈ M₂(Γ₀(𝔑), χ_Q), over F [unverified]"]
theorem eisQ2_mem_modularFormChar (hfree : GenusFree (formF Q₀) stdLat) :
    eisQ2 Q₀ 𝔑 h𝔑 ∈ modularFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) 2 :=
  eisGen2_mem_modularFormChar hd h𝔑 (hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree)
    (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2

include hQ hn hlev h𝔑 hd in
/-- **$E_Q$ has the constant term of $\theta_{\mathrm{Gen}}$ (and of $\theta_{Q_0}$) at every cusp** ($n = 4$, $d \ge 2$). -/
@[kb "siegel1935" "constant terms of E_Q at the cusps, weight 2, over F [unverified]"]
theorem tendsto_eisQ2_slash (hfree : GenusFree (formF Q₀) stdLat) (A : SL(2, F)) :
    Tendsto (eisQ2 Q₀ 𝔑 h𝔑 ∣[(2 : ℤ)] slHom (realEmb F) A) atImInftyPi (𝓝 (thetaCuspVal Q₀ 2 A)) := by
  have h := tendsto_eisGen2_slash hd h𝔑 (hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree)
    (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2 A
  have hc : cuspVal (thetaGen (formF Q₀) stdLat) 2 A = thetaCuspVal Q₀ 2 A :=
    cuspVal_eq_of_tendsto (tendsto_thetaGen_slash hQ hn hlev h𝔑 hfree A)
  rw [hc] at h
  exact h

include hQ hn hlev h𝔑 hd in
/-- **$\theta_{\mathrm{Gen}} - E_Q$ is a cusp form in weight 2** over a totally real field of degree $d \ge 2$: for a totally positive
definite quaternary $Q_0$ over $\mathcal{O}_F$, a theta level $\mathfrak N \ne 0$ and a free genus,
$$\theta_{\mathrm{Gen}} - E_Q \in S_2(\Gamma_0(\mathfrak N), \chi_Q).$$ -/
@[kb "siegel1935" "θ_Gen − E_Q is a cusp form, weight 2, over a totally real field [unverified]"]
theorem thetaGen_sub_eisQ2_mem_cuspFormChar (hfree : GenusFree (formF Q₀) stdLat) :
    thetaGen (formF Q₀) stdLat - eisQ2 Q₀ 𝔑 h𝔑 ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) 2 :=
  sub_eisGen2_mem_cuspFormChar hd h𝔑 (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree)
    (hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree)

include hQ hn hlev h𝔑 hd in
/-- **$\theta_M - E_Q$ is a cusp form in weight 2** for every lattice $M$ in the genus of $\mathcal{O}_F^4$ (free genus). -/
@[kb "siegel1935" "θ_M − E_Q is a cusp form, weight 2, over F [unverified]"]
theorem thetaLatt_sub_eisQ2_mem_cuspFormChar (hfree : GenusFree (formF Q₀) stdLat)
    (M : Lat F n) (hM : SameGenus (formF Q₀) intVec M.1) :
    thetaLatt (formF Q₀) M.1 - eisQ2 Q₀ 𝔑 h𝔑 ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) 2 := by
  have h1 := thetaLatt_sub_thetaGen_mem_cuspFormChar hQ hn hlev h𝔑 hfree M hM
  have h2 := thetaGen_sub_eisQ2_mem_cuspFormChar hQ hn hlev h𝔑 hd hfree
  have := (cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) 2).add_mem h1 h2
  rwa [sub_add_sub_cancel] at this

include hQ hn hlev h𝔑 hd in
/-- **Class number one: $\theta_{\mathrm{Gen}} - E_Q \in S_2$ with no freeness hypothesis** ($\mathcal{O}_F$ a PID, $n = 4$, $d \ge 2$). -/
@[kb "siegel1935" "θ_Gen − E_Q is a cusp form, weight 2, h_F = 1 [unverified]"]
theorem thetaGen_sub_eisQ2_mem_cuspFormChar_of_pid [IsPrincipalIdealRing (𝓞 F)] :
    thetaGen (formF Q₀) stdLat - eisQ2 Q₀ 𝔑 h𝔑 ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) 2 :=
  thetaGen_sub_eisQ2_mem_cuspFormChar hQ hn hlev h𝔑 hd (genusFree_of_isPrincipalIdealRing _ _)

end Main

end QuadFormsKB.HilbertModular
