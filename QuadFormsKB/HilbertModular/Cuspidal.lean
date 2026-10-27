/-
# $\theta_{\mathrm{Gen}} - E_Q$ is a cusp form over a totally real field

**Setting** (`GenusTheta.lean`): $F$ totally real, $Q_0$ a totally positive definite form over $\mathcal{O}_F$ in $n = 2k$ variables,
$\mathfrak N \ne 0$ a theta level of $Q_0$ (`IsThetaLevelF`), $\chi_Q$ its character (`thetaCharF`), and the genus of $\mathcal{O}_F^n$ in
$(F^n, Q_0)$ free (`GenusFree`; proved for $\mathcal{O}_F$ a PID).

**The Eisenstein series of the genus** (`eisQ`): $E_Q = E_{\theta_{\mathrm{Gen}}}$ of `EisensteinGenus.lean`, the Eisenstein series
$E_k(\cdot; W)$ whose weight $W$ is supported on one reduced vector per cusp line, with value the constant term of $\theta_{\mathrm{Gen}}$
there.

**Main results** ($k \ge 3$):
* `eisQ_mem_modularFormChar`: $E_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$;
* `tendsto_eisQ_slash`: at every cusp $A\infty$, $E_Q\,|_k\,A \to$ `thetaCuspVal Q₀ k A`, the constant term of $\theta_{Q_0}$ (and of
  every $\theta_M$, $M$ in the genus, and of $\theta_{\mathrm{Gen}}$): the local (Gauss-sum) constant of `tendsto_thetaQ_slash`;
* **`thetaGen_sub_eisQ_mem_cuspFormChar`**: $\theta_{\mathrm{Gen}} - E_Q \in S_k(\Gamma_0(\mathfrak N), \chi_Q)$;
* `thetaLatt_sub_eisQ_mem_cuspFormChar`: $\theta_M - E_Q \in S_k(\Gamma_0(\mathfrak N), \chi_Q)$ for every $M$ in the genus.

A cusp form here is `cuspFormChar`: $f\,|_k\,A \to 0$ at $\infty$ for every $A \in \mathrm{SL}_2(F)$, i.e. the constant term
(the $\nu = 0$ coefficient of the $q$-expansion at the cusp $A\infty$) vanishes at every cusp; it is checked directly from the
limits, with no $q$-expansion needed.

**Weight 2** ($n = 4$, $d \ge 2$) is in `Cuspidal2.lean` (periodic weights via Möbius over ideals and ray classes).

Over $\mathbb{Q}$: `Siegel.GenusEis.cuspPart` (weight 2, $\Gamma_1(N)$).

Sources: Siegel (1935) [unverified]; Shimura (1973), §2, and (Duke 1978), §3 [unverified]; Hecke (1927) [unverified].
-/
import QuadFormsKB.HilbertModular.GenusTheta
import QuadFormsKB.HilbertModular.EisensteinGenus

open Matrix NumberField Complex Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **The Eisenstein series of the genus of $Q_0$**: $E_Q = E_{\theta_{\mathrm{Gen}}}$, weight $k$ (`eisGen`). -/
@[kb "siegel1935" "the Eisenstein series of the genus, over F [unverified]"]
noncomputable def eisQ (Q₀ : QuadForm (𝓞 F) n) (k : ℕ) : (InfinitePlace F → UpperHalfPlane) → ℂ :=
  eisGen (thetaGen (formF Q₀) stdLat) k

section Main

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)

include hQ hn hlev h𝔑 in
lemma hasCuspLimits_thetaGen (hfree : GenusFree (formF Q₀) stdLat) :
    HasCuspLimits (thetaGen (formF Q₀) stdLat) k :=
  fun A => ⟨_, tendsto_thetaGen_slash hQ hn hlev h𝔑 hfree A⟩

include hQ hn hlev h𝔑 in
/-- **$E_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$** ($k \ge 3$). -/
@[kb "siegel1935" "E_Q ∈ M_k(Γ₀(𝔑), χ_Q), over F [unverified]"]
theorem eisQ_mem_modularFormChar (hk : 3 ≤ k) (hfree : GenusFree (formF Q₀) stdLat) :
    eisQ Q₀ k ∈ modularFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k :=
  eisGen_mem_modularFormChar (by exact_mod_cast hk) h𝔑 (hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree)
    (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2

include hQ hn hlev h𝔑 in
/-- **$E_Q$ has the constant term of $\theta_{\mathrm{Gen}}$ (and of $\theta_{Q_0}$) at every cusp** ($k \ge 3$): for every
$A \in \mathrm{SL}_2(F)$, $E_Q\,|_k\,A \to$ `thetaCuspVal Q₀ k A`. -/
@[kb "siegel1935" "constant terms of E_Q at the cusps, over F [unverified]"]
theorem tendsto_eisQ_slash (hk : 3 ≤ k) (hfree : GenusFree (formF Q₀) stdLat) (A : SL(2, F)) :
    Tendsto (eisQ Q₀ k ∣[(k : ℤ)] slHom (realEmb F) A) atImInftyPi (𝓝 (thetaCuspVal Q₀ k A)) := by
  have h := tendsto_eisGen_slash (by exact_mod_cast hk) h𝔑 (hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree)
    (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2 A
  rwa [cuspVal_eq_of_tendsto (tendsto_thetaGen_slash hQ hn hlev h𝔑 hfree A)] at h

include hQ hn hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} - E_Q$ is a cusp form** over a totally real field: for a totally positive definite $Q_0$ over $\mathcal{O}_F$
in $n = 2k \ge 6$ variables, a theta level $\mathfrak N \ne 0$ and a free genus,
$$\theta_{\mathrm{Gen}} - E_Q \in S_k(\Gamma_0(\mathfrak N), \chi_Q).$$ -/
@[kb "siegel1935" "θ_Gen − E_Q is a cusp form, over a totally real field [unverified]"]
theorem thetaGen_sub_eisQ_mem_cuspFormChar (hk : 3 ≤ k) (hfree : GenusFree (formF Q₀) stdLat) :
    thetaGen (formF Q₀) stdLat - eisQ Q₀ k ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k :=
  sub_eisGen_mem_cuspFormChar (by exact_mod_cast hk) h𝔑 (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree)
    (hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree)

include hQ hn hlev h𝔑 in
/-- **$\theta_M - E_Q$ is a cusp form** for every lattice $M$ in the genus of $\mathcal{O}_F^n$ ($k \ge 3$, free genus). -/
@[kb "siegel1935" "θ_M − E_Q is a cusp form, over F [unverified]"]
theorem thetaLatt_sub_eisQ_mem_cuspFormChar (hk : 3 ≤ k) (hfree : GenusFree (formF Q₀) stdLat)
    (M : Lat F n) (hM : SameGenus (formF Q₀) intVec M.1) :
    thetaLatt (formF Q₀) M.1 - eisQ Q₀ k ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k := by
  have h1 := thetaLatt_sub_thetaGen_mem_cuspFormChar hQ hn hlev h𝔑 hfree M hM
  have h2 := thetaGen_sub_eisQ_mem_cuspFormChar hQ hn hlev h𝔑 hk hfree
  have := (cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k).add_mem h1 h2
  rwa [sub_add_sub_cancel] at this

include hQ hn hlev h𝔑 in
/-- **Class number one: $\theta_{\mathrm{Gen}} - E_Q$ is a cusp form with no freeness hypothesis** ($\mathcal{O}_F$ a PID, $k \ge 3$). -/
@[kb "siegel1935" "θ_Gen − E_Q is a cusp form, h_F = 1 [unverified]"]
theorem thetaGen_sub_eisQ_mem_cuspFormChar_of_pid [IsPrincipalIdealRing (𝓞 F)] (hk : 3 ≤ k) :
    thetaGen (formF Q₀) stdLat - eisQ Q₀ k ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k :=
  thetaGen_sub_eisQ_mem_cuspFormChar hQ hn hlev h𝔑 hk (genusFree_of_isPrincipalIdealRing _ _)

end Main

end QuadFormsKB.HilbertModular
