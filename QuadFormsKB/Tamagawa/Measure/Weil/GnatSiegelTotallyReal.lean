/-
# Siegel's formula for every totally real field, unconditionally

**Layer:** $F$ a totally real number field (any degree, any class number).

With `nsBadDeepRatio : NSBadDeepRatio F` (the window argument, `GnatNSWinFinal`), every input of the
non-square comparison is discharged:

* **`nsBadPlaceRatio`**: `NSBadPlaceRatio F` (via `nsBadPlaceRatio_of_deep`);
* **`gnatMeasureComparisonNS`**, **`gnatMeasureComparisonDef`**, **`gnatTamagawaComparisonDef`**: Weil's Thm 2.3.1 for
  $G^\natural\to SO_4$ (non-square and square discriminants);
* **`quaternaryTamagawaTwo_nf'`**: $\tau(SO_4) = 2$; **`rankFourUnitSiegel_nf`**: `RankFourUnitSiegel F`;
* **`siegelFormulaAt_totallyReal`**: Siegel's formula $r_Q(m) = $ (Siegel main term) for every totally positive definite
  form $Q$ over $\mathcal O_F$ in every rank $N\ge4$ and every totally positive $m$;
* **`tamagawaNumberTwo_all_ranks_totallyReal`**, **`massFormula_all_ranks_totallyReal`**: $\tau(SO(Q)) = 2$ and the mass
  formula in every rank $N\ge4$.

All unconditional: `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`. (Ranks $1$-$3$ were already
unconditional.)

Source: Siegel 1935, Hauptsatz [unverified]; Weil 1982, Thm 2.3.1, §3.7 (Thm 3.7.1), §4.5 (Thm 4.5.1) [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinFinal

open NumberField

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

variable (F : Type) [Field F] [NumberField F]

/-- **`NSBadPlaceRatio F` holds for every number field $F$.** -/
@[kb "weil1982" "Thm 2.3.1 (local ratios at the bad places) [unverified page]"]
theorem nsBadPlaceRatio : NSBadPlaceRatio F := nsBadPlaceRatio_of_deep (nsBadDeepRatio F)

variable [IsTotallyReal F]

/-- **`GnatMeasureComparisonNSDef F`** (Weil's Thm 2.3.1 for the non-square model), unconditionally. -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
theorem gnatMeasureComparisonNS : GnatMeasureComparisonNSDef F :=
  gnatMeasureComparisonNS_of_ratio (nsBadPlaceRatio F)

/-- **`GnatMeasureComparisonDef F`**, unconditionally. -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
theorem gnatMeasureComparisonDef : GnatMeasureComparisonDef F :=
  gnatMeasureComparisonDef_of_ratio (nsBadPlaceRatio F)

/-- **`GnatTamagawaComparisonDef F`**, unconditionally. -/
@[kb "weil1982" "Thm 2.3.1, §3.7 [unverified page]"]
theorem gnatTamagawaComparisonDef : GnatTamagawaComparisonDef F :=
  gnatTamagawaComparisonDef_of_ratio (nsBadPlaceRatio F)

/-- **$\tau(SO_4) = 2$ for every totally real $F$**, unconditionally. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65 [unverified page]"]
theorem quaternaryTamagawaTwo_nf' : QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_ratio (nsBadPlaceRatio F)

/-- **`RankFourUnitSiegel F`** for every totally real $F$, unconditionally. -/
@[kb "weil1982" "§4.5, p. 100; §3.7 [unverified page]"]
theorem rankFourUnitSiegel_nf : RankFourUnitSiegel F :=
  rankFourUnitSiegel_of_ratio (nsBadPlaceRatio F)

variable {F}

/-- **Siegel's formula over every totally real field, unconditionally**: for every totally positive definite form
$Q_0$ over $\mathcal O_F$ in rank $N\ge4$ and every totally positive $m\in\mathcal O_F$, `SiegelFormulaAt Q₀ m` (the
representation number $r_{Q_0}(m)$ averaged over the genus equals Siegel's product of local densities). -/
@[kb "siegel1935" "Hauptsatz [unverified]; weil1982 §4.5, Thm 4.5.1 [unverified page]"]
theorem siegelFormulaAt_totallyReal {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 F} (hm : ∀ v, 0 < QuadFormsKB.HilbertModular.realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_totallyReal_of_ratio (nsBadPlaceRatio F) hN Q₀ hpd hm

/-- **$\tau(SO(Q_0)) = 2$ in every rank $N\ge4$, every totally real $F$**, unconditionally. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109 [unverified page]"]
theorem tamagawaNumberTwo_all_ranks_totallyReal {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_of_ratio (nsBadPlaceRatio F) hN Q₀ hpd

/-- **The mass formula in every rank $N\ge4$, every totally real $F$**, unconditionally. -/
@[kb "weil1982" "Thm 4.5.1, p. 109 [unverified page]"]
theorem massFormula_all_ranks_totallyReal {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_of_ratio (nsBadPlaceRatio F) hN Q₀ hpd

end QuadFormsKB.Tamagawa.Measure.Weil
