import QuadFormsKB.Tamagawa.InputsFollowup
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume

/-!
# Mass and Siegel formulas over every totally real field without the discharged inputs

Several theorems were written before their named inputs were proved, and still carry them as hypotheses:

* `LatChange.massFormula_lat_nf` assumes `TamagawaNumberTwo Q₀` ($\tau(SO(Q_0)) = 2$), proved in every rank $N \ge 3$
  over every totally real number field by `tamagawaNumberTwo_totallyReal`;
* `massFormula_all_ranks_nf`, `siegelFormulaAt_all_ranks_nf` and `massFormula_lat_all_ranks_nf` assume
  `RankFourUnitSiegel F` (Siegel's formula in rank $4$ for the number $1$), proved for every totally real number field
  by `Measure.Weil.rankFourUnitSiegel_nf`.

This file states each of them without the input (one-line wrappers). Throughout, $F$ is a totally real number field
(any degree, any class number), $Q_0$ is a totally positive definite quadratic form in $N$ variables over the ring of
integers $\mathcal O_F$, and `formF Q₀` is $Q_0$ read over $F$.

* `massFormula_lat_totallyReal`: for every lattice $L$ on $(F^N, Q_0)$ that is integral for $Q_0$ ($N \ge 3$; any
  Steinitz class, $L$ need not be free), $\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}$.
* `massFormula_all_ranks_nf_uncond`: `MassFormulaHolds Q₀` for $N \ge 4$ (the same statement as
  `Measure.Weil.massFormula_all_ranks_totallyReal`, obtained here through the rank-four Siegel route).
* `siegelFormulaAt_all_ranks_nf_uncond`: `SiegelFormulaAt Q₀ m` for $Q_0$ in $n + 1 \ge 5$ variables and every totally
  positive $m \in \mathcal O_F$.
* `massFormula_lat_all_ranks_nf_uncond`: the lattice mass formula for $N \ge 4$ through the rank-four route.

It also records, with a `@[kb]` tag (so that the input audit sees the discharge), that the named input
`Measure.Weil.IdeleClassVolumeResidue F` (the volume of the norm-one idele class group is the residue $\rho_F$) holds
for every number field $F$: `ideleClassVolumeResidue_nf`, the untagged `Measure.Weil.idelesClassVolumeResidue`.

Source: Weil 1982, Theorem 3.7.1 and Theorem 4.5.1 (p. 109) [unverified page]; Siegel 1935, Hauptsatz [unverified].
-/

open NumberField

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **The mass formula for the genus of an arbitrary lattice over every totally real number field, unconditionally**:
for $Q_0$ a totally positive definite quadratic form in $N \ge 3$ variables over $\mathcal O_F$ and every lattice $L$ on
$V = (F^N, Q_0)$ that is integral for $Q_0$ (any Steinitz class; $L$ need not be free),
$$\mathrm{Mass}(L) = \sum_{\mathrm{cls}\,M \subseteq \mathrm{gen}\,L} \frac1{|O(M)|} = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}.$$
This is `LatChange.massFormula_lat_nf` with its input $\tau(SO(Q_0)) = 2$ supplied by `tamagawaNumberTwo_totallyReal`. -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice, rank ≥ 3, every class number [unverified]"]
theorem massFormula_lat_totallyReal {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F N) (hLi : IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L = (LatChange.tamagawaKLat Q₀ L)⁻¹ :=
  LatChange.massFormula_lat_nf Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd
    (tamagawaNumberTwo_totallyReal hN Q₀ hpd) L hLi

/-- **The mass formula `MassFormulaHolds Q₀` in every rank $N \ge 4$ over every totally real number field,
unconditionally**: `massFormula_all_ranks_nf` with `RankFourUnitSiegel F` supplied by
`Measure.Weil.rankFourUnitSiegel_nf`. -/
@[kb "weil1982" "Thm. 4.5.1, p. 109; mass formula; every class number [unverified page]"]
theorem massFormula_all_ranks_nf_uncond {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_nf (Measure.Weil.rankFourUnitSiegel_nf F) hN Q₀ hpd

/-- **Siegel's formula `SiegelFormulaAt Q₀ m` in every rank $n + 1 \ge 5$ over every totally real number field,
unconditionally**, for every totally positive $m \in \mathcal O_F$: `siegelFormulaAt_all_ranks_nf` with
`RankFourUnitSiegel F` supplied by `Measure.Weil.rankFourUnitSiegel_nf`. -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; every class number [unverified page]"]
theorem siegelFormulaAt_all_ranks_nf_uncond {n : ℕ} (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks_nf (Measure.Weil.rankFourUnitSiegel_nf F) hn Q₀ hpd hm

/-- **The mass formula for the genus of an arbitrary lattice in every rank $N \ge 4$ over every totally real number
field, unconditionally** (any Steinitz class): `massFormula_lat_all_ranks_nf` with `RankFourUnitSiegel F` supplied by
`Measure.Weil.rankFourUnitSiegel_nf`. `massFormula_lat_totallyReal` gives the same conclusion for $N \ge 3$. -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice, every class number [unverified]"]
theorem massFormula_lat_all_ranks_nf_uncond {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F N) (hLi : IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L = (LatChange.tamagawaKLat Q₀ L)⁻¹ :=
  massFormula_lat_all_ranks_nf (Measure.Weil.rankFourUnitSiegel_nf F) hN Q₀ hpd L hLi

/-- **The named input `IdeleClassVolumeResidue F` holds for every number field $F$**:
$\operatorname{vol}(F^\times\backslash\mathbb A_F^1, \mu^1) = \rho_F$, the residue at $s = 1$ of the Dedekind zeta function
(Weil 1982, Theorem 3.1.1 (iii) for $\mathbb G_m$). This is `Measure.Weil.idelesClassVolumeResidue`, restated with a
`@[kb]` tag. -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41 [unverified page]"]
theorem ideleClassVolumeResidue_nf (F : Type) [Field F] [NumberField F] :
    Measure.Weil.IdeleClassVolumeResidue F :=
  Measure.Weil.idelesClassVolumeResidue

end QuadFormsKB.Tamagawa
