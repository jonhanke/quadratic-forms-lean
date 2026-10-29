import QuadFormsKB.Tamagawa.TauTwo
import QuadFormsKB.Tamagawa.SphericalFibration
import QuadFormsKB.Tamagawa.NonPIDEuler
import QuadFormsKB.Tamagawa.TernaryTamagawaNF
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal
import QuadFormsKB.Tamagawa.Measure.Weil.ReleaseHeadlines
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereFibProof
import QuadFormsKB.Tamagawa.Indefinite.OneClass

/-!
# Weil's induction inputs, discharged

Several named inputs of Weil's induction (Weil 1982, §4.5) are hypotheses of theorems written before τ = 2 was proved.
Now that $\tau(SO) = 2$ holds in every rank $N \ge 3$ over every totally real field (lattice form:
`tamagawaNumberTwo_ternary_nf`, `Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal`) and in every dimension $\ge 3$
over every number field (adelic form: `Measure.Weil.tauTwoAll_release_uncond`), they are theorems in the instances that
are used. This file states them and the consumers without them.

* `AdditiveZeta.ComplementTauTwo (tauComp Q₀)` (`complementTauTwo_tauComp`) and
  `AdditiveZeta.SphericalFibration Q₀ (sphFamily Q₀) (tauComp Q₀)` (`sphericalFibration_tauComp`): for $Q_0$ totally
  positive definite in $n + 1 \ge 5$ variables over a totally real $F$, any class number. Both structures are schematic
  in the family $\tau'$; they are true for $\tau' = $ `tauComp Q₀` (the Tamagawa numbers of the orthogonal complements
  of the chosen frames), not for an arbitrary family.
* Consequences without inputs: the additive residue (`tendsto_mul_sphericalSum_uncond`), Weil's Theorem 4.5.1 by the
  comparison of residues (`tamagawaNumberTwo_of_sphericalFibration_uncond`) and the mass formula
  (`massFormula_of_sphericalFibration_uncond`).
* `MassFormulaHolds` in rank 3 (`massFormulaHolds_ternary_nf`) and rank $\ge 3$ (`massFormulaHolds_totallyReal`).
* `Measure.Weil.AdelicComplementTauTwo S` for every sphere family whose complements have $k \ge 3$ variables
  (`Measure.Weil.adelicComplementTauTwo_of_three_le`), and the adelic unfolding $Z^+(s) = \sum_c Z(s,c)$ for the
  constructed family without inputs (`Measure.Weil.adelicZetaPlus_eq_tsum_uncond`).
* Siegel's formula for an indefinite form with one class in its genus (`Indefinite.siegelIndefinite_oneClass_uncond`,
  `Indefinite.siegelIndefinite_oneClass_div_uncond`): `Indefinite.siegelIndefinite_oneClass` without its inputs
  `AdelicSphereFibration`, `AdelicSphereDensities` and `TamagawaNumberTwoAdelic`, for $N \ge 4$.
-/

open NumberField Filter Topology
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.AdditiveZeta

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **$\tau(SO(Q_0)) = 2$ for every totally positive definite form in $N \ge 3$ variables over every totally real field**
(any class number): rank 3 is `tamagawaNumberTwo_ternary_nf`, rank $\ge 4$ is
`Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal`. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109 [unverified page]; rank ≥ 3, every class number"]
theorem tamagawaNumberTwo_totallyReal {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ := by
  rcases Nat.lt_or_ge N 4 with h | h
  · obtain rfl : N = 3 := by omega
    exact tamagawaNumberTwo_ternary_nf Q₀ hpd
  · exact Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal h Q₀ hpd

/-- **The mass formula $\mathrm{Mass}(\mathcal O_F^N) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$ (`MassFormulaHolds Q₀`) in every
rank $N \ge 3$ over every totally real field** (any class number), for $Q_0$ totally positive definite. -/
@[kb "weil1982" "Thm 4.5.1, p. 109, mass formula [unverified page]; rank ≥ 3, every class number"]
theorem massFormulaHolds_totallyReal {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)
    (tamagawaNumberTwo_totallyReal hN Q₀ hpd)

/-- **The mass formula in rank 3 over every totally real field** (`MassFormulaHolds Q₀` for $Q_0$ ternary and totally
positive definite, any class number), the base case of `MassFormulaHolds` left open in `MassInduction.lean`. -/
@[kb "weil1982" "Thm 3.7.1 (m = 3), p. 65 [unverified page]; mass formula, rank 3"]
theorem massFormulaHolds_ternary_nf (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) :
    MassFormulaHolds Q₀ :=
  massFormulaHolds_totallyReal le_rfl Q₀ hpd

/-- **The induction hypothesis of Weil's §4.5 holds for the complements of the frames** (`ComplementTauTwo (tauComp Q₀)`):
for $Q_0$ totally positive definite in $n + 1$ variables, $n \ge 3$, over a totally real $F$ (any class number),
$\tau'_k = \tau(SO(Q'_k)) = 2$ for every square class $k$. -/
@[kb "weil1982" "§4.5, p. 108 (τ(G') = 2 by the induction assumption), discharged"]
theorem complementTauTwo_tauComp {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) : ComplementTauTwo (tauComp Q₀) :=
  complementTauTwo_of_IH Q₀ hpd fun Q' h => tamagawaNumberTwo_totallyReal hn Q' h

/-- **Weil's fibration over the spheres holds** (`SphericalFibration Q₀ (sphFamily Q₀) (tauComp Q₀)`): for $Q_0$ totally
positive definite in $n + 1 \ge 5$ variables over a totally real $F$ (any class number), for $s > 0$
$$Z^+(s) = \sum_{\rho\in F^\times/F^{\times2}}\frac{\tau'_\rho}2Z(s,\rho),$$
with $Z^+$ the additive zeta function of the genus, $Z(s,\rho)$ the spherical zeta functions of the Gaussian and
$\tau'_\rho = $ `tauComp Q₀`. From the orbital Euler product (`orbitalEulerProduct_nf'`) and Steinitz
(`genusFree_formF`). -/
@[kb "weil1982" "§4.5, p. 109 (Lemma 2.4.2 on T(ρ)), discharged"]
theorem sphericalFibration_tauComp {n : ℕ} (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) :
    SphericalFibration Q₀ (TauTwo.sphFamily Q₀) (tauComp Q₀) :=
  QuadFormsKB.SphericalFibration.sphericalFibration_of_orbitalEulerProduct Q₀ (by omega) hpd (genusFree_formF hpd)
    (orbitalEulerProduct_nf' Q₀ hpd hn)

/-- **Weil's additive residue, without inputs** (Weil 1982, §4.5, p. 109): for $Q_0$ totally positive definite in
$n + 1 \ge 5$ variables over a totally real $F$ (any class number), the spherical sum of the Gaussian satisfies
$$\lim_{s\to0^+}s\sum_\rho Z(s,\rho) = \frac{\rho_F}2\,\tau(SO)\int_{V(\mathbb A)}\Phi\,dx.$$
`AdditiveZeta.tendsto_mul_sphericalSum` with its two inputs discharged. -/
@[kb "weil1982" "§4.5, p. 109 (additive calculation; residue ρ_kτ(G)/2)"]
theorem tendsto_mul_sphericalSum_uncond {n : ℕ} (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) :
    Tendsto (fun s => s * ∑' k, TauTwo.sphFamily Q₀ k s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F / 2 * tauSO Q₀ * GlobalZeta.phiIntegral (GlobalZeta.gaussian Q₀ π))) :=
  tendsto_mul_sphericalSum Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd (genusFree_formF hpd)
    (sphericalFibration_tauComp hn Q₀ hpd) (complementTauTwo_tauComp (by omega) Q₀ hpd)

/-- **Weil's Theorem 4.5.1 by the comparison of residues, without inputs**: for $Q_0$ totally positive definite in
$n + 1 \ge 5$ variables over a totally real $F$ (any class number), $\tau(SO(V)) = 2$.
`TauTwo.tamagawaNumberTwo_of_sphericalFibration'` with `SphericalFibration` and `ComplementTauTwo` discharged. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109 (comparison of residues)"]
theorem tamagawaNumberTwo_of_sphericalFibration_uncond {n : ℕ} (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  QuadFormsKB.SphericalFibration.tamagawaNumberTwo_of_sphericalFibration' Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd
    (sphericalFibration_tauComp hn Q₀ hpd) (complementTauTwo_tauComp (by omega) Q₀ hpd)

/-- **The mass formula in rank $n + 1 \ge 5$ by Weil's comparison of residues, without inputs**:
$\mathrm{Mass}(\mathcal O_F^{n+1}) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$ for $Q_0$ totally positive definite over a totally real
$F$ (any class number). `TauTwo.massFormula_of_sphericalFibration` with its inputs discharged. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_of_sphericalFibration_uncond {n : ℕ} (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) : mass (formF Q₀) (stdLat F (n + 1)) = (tamagawaK Q₀)⁻¹ :=
  TauTwo.massFormula_of_sphericalFibration Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd
    (genusFree_formF hpd) (sphericalFibration_tauComp hn Q₀ hpd) (complementTauTwo_tauComp (by omega) Q₀ hpd)

end QuadFormsKB.Tamagawa

namespace QuadFormsKB.Tamagawa.Measure.Weil

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Set Matrix MulAction
open IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **The adelic induction hypothesis holds** (`AdelicComplementTauTwo S`): for every sphere family $S$ of a form in
$k + 1$ variables over a number field $F$ whose complements $Q'_c$ have $k \ge 3$ variables,
$\tau(SO(Q'_c)) = 2$ for every class $c$ (`tauTwoAll_release_uncond`, every signature, every number field). -/
@[kb "weil1982" "§4.5, p. 109 (induction on dim: τ(G'_ρ) = 2), discharged"]
theorem adelicComplementTauTwo_of_three_le (hk : 3 ≤ k) {Q₀ : QuadForm (𝓞 F) (k + 1)} (S : AdelicSphereFamily Q₀) :
    AdelicComplementTauTwo S :=
  ⟨fun c => tauTwoAll_release_uncond k hk (S.Q' c) (S.hQ' c)⟩

/-- **The adelic spherical unfolding $Z^+(s) = \sum_cZ(s,c)$ without inputs** (Weil 1982, §4.5, p. 109: "$Z^+(s) = Z(s)$"):
for $Q_0$ nondegenerate in $k + 1 \ge 4$ variables over a number field $F$, the constructed sphere family, measurable
$\Phi \ge 0$ and every real $s$. `adelicZetaPlus_eq_tsum_of_complementTauTwo` with the fibration and the induction
hypothesis discharged. -/
@[kb "weil1982" "§4.5, p. 109 (Z⁺(s) = Σ_ρ Z(s,ρ) under τ(G'_ρ) = 2)"]
theorem adelicZetaPlus_eq_tsum_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    {Φ : AdeleSpace F (Fin (k + 1)) → ENNReal} (hΦ : Measurable Φ)
    {D : Set (SOAdele Q₀)} (hD : MeasureTheory.IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : MeasureTheory.IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) (s : ℝ) :
    adelicZetaPlus Q₀ hQ Φ D DM s = ∑' c, adelicSphZeta ((sphereFamily hQ hk).data c) Φ s :=
  adelicZetaPlus_eq_tsum_of_complementTauTwo (by omega) _ (sphereFamily_fibration hQ hk)
    (adelicComplementTauTwo_of_three_le hk _) hΦ hD hDM s

end QuadFormsKB.Tamagawa.Measure.Weil

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {k : ℕ}

/-- **Siegel's formula for an indefinite form with one class in its genus, without inputs** (Siegel 1936, Hauptsatz for
indefinite forms; Eichler 1952): let $F$ be a totally real number field with $\mathcal O_F$ a principal ideal domain,
$Q_0$ nondegenerate over $\mathcal O_F$ in $N = k + 1 \ge 4$ variables, $Q$ isotropic at every real place (`hinf`), with
`LocalSpinorUnits` at the primes $\mathfrak p \mid 2\det H$ (`hbad`), and $m \in \mathcal O_F\setminus0$ with a rational
point $\xi$ on $Q_0 = m$. Then
$$c_\infty(m)\,\rho(L, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot v(L),$$
$L = \mathcal O_F^N$, $v(L)$ = `unitVolume` and $\rho(L, m)$ = `repMeasure` at the proper class `dcL` of $L$, the only one in
its genus. `siegelIndefinite_oneClass` with the inputs `AdelicSphereFibration`, `AdelicSphereDensities` and
$\tau = 2$ discharged (for the constructed sphere data; this needs $N \ge 4$, where the original allows $N \ge 3$). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus) [unverified]"]
theorem siegelIndefinite_oneClass_uncond [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (k + 1))
    (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (k + 1)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInf (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) (dcL Q₀) =
      ENNReal.ofReal (finDensityProduct Q₀ m) * unitVolume Q₀ hQ (dcL Q₀) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  have h := siegelIndefinite_release_totallyReal_uncond hQ hk hm ξ
  rwa [tsum_eq_single (dcL Q₀) (fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj),
    tsum_eq_single (dcL Q₀) (fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj)] at h

/-- **The ratio form, without inputs**: under the hypotheses of `siegelIndefinite_oneClass_uncond`, $0 < v(L) < \infty$
and $$\frac{c_\infty(m)\,\rho(L, m)}{v(L)} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus) [unverified]"]
theorem siegelIndefinite_oneClass_div_uncond [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (k + 1))
    (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (k + 1)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    (cInf (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) (dcL Q₀)) /
        unitVolume Q₀ hQ (dcL Q₀) =
      ENNReal.ofReal (finDensityProduct Q₀ m) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  have hτ := tauTwoAll_release_uncond (k + 1) (by omega) Q₀ hQ
  have hsum : ∑' i, unitVolume Q₀ hQ i = unitVolume Q₀ hQ (dcL Q₀) :=
    tsum_eq_single (dcL Q₀) fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj
  rw [siegelIndefinite_oneClass_uncond Q₀ hQ hk hinf hbad hm ξ,
    ENNReal.mul_div_cancel_right (hsum ▸ tsum_unitVolume_ne_zero Q₀ hQ hτ)
      (hsum ▸ tsum_unitVolume_ne_top Q₀ hQ hτ)]

end QuadFormsKB.Tamagawa.Indefinite
