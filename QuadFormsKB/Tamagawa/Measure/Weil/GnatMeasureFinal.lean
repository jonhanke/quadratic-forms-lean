/-
# Status of `GnatMeasureComparisonDef` — the square half is a theorem

**Layer:** a totally real number field $F$ (any class number).

* **`gnatMeasureComparisonDef_square`** (unconditional): the `square` field of the input `GnatMeasureComparisonDef F`,
  i.e. $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for $\Phi$ = `sqPEquiv` and every totally definite $D = (a,b)_F$
  (`map_muP_sqPEquiv_eq_muTam`).
* **`tamagawaNumberTwoAdelic_qSq_totallyDefinite`** (unconditional): Weil's $\tau(SO(\langle1,-a,-b,ab\rangle)) = 2$ (adelic,
  `muTam`) for every totally definite quaternion algebra $(a,b)_F$ over every totally real $F$.
* **`GnatMeasureComparisonNSDef F`** (input, named): the remaining `nonsquare` field (the non-square-discriminant model
  $\langle1,-ad,-bd,abd\rangle$, $\Phi$ = `nsPEquiv`). **`gnatMeasureComparisonDef_of_ns`**: it implies
  `GnatMeasureComparisonDef F`; hence the consumers `rankFourUnitSiegel_of_ns`, `quaternaryTamagawaTwo_of_ns`,
  **`siegelFormulaAt_totallyReal_of_ns`** (Siegel's formula for every totally positive definite form over $\mathcal O_F$ in
  every rank $N\ge4$, every totally positive $m$), `tamagawaNumberTwo_all_ranks_of_ns`, `massFormula_all_ranks_of_ns`.

*Hypothesis hygiene.* `GnatMeasureComparisonNSDef` compares two explicit Haar measures on $SO(V)(\mathbb A)$ along an
explicit isomorphism (non-square case only); it mentions no lattice, covolume, Tamagawa number or representation count,
and is strictly weaker than `GnatMeasureComparisonDef` (whose square half is proved here).

Source: Weil 1982, Thm 2.3.1; §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqMeasure
import QuadFormsKB.Tamagawa.SiegelRankFourNF

open MeasureTheory NumberField
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **The square half of `GnatMeasureComparisonDef F` is a theorem** (every totally real $F$, any class number). -/
@[kb "weil1982" "Thm 2.3.1; §3.7, p. 65 [unverified page]"]
theorem gnatMeasureComparisonDef_square (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hna : IsTotallyPos (-(a : F)))
    (hnb : IsTotallyPos (-(b : F))) (hQ : (qSq a b).Nondegenerate) :
    ((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map (sqPEquiv ha0 hb0) = muTam (qSq a b) hQ (fun _ => 1) :=
  map_muP_sqPEquiv_eq_muTam ha0 hb0 hna hnb hQ

/-- **Weil's adelic $\tau(SO(\langle1,-a,-b,ab\rangle)) = 2$ for every totally definite $(a,b)_F$** over every totally real $F$
— unconditional. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_qSq_totallyDefinite {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) (hQ : (qSq a b).Nondegenerate) :
    TamagawaNumberTwoAdelic (qSq a b) hQ := by
  have hdiv := hdiv_of_totallyNeg (F := F) (a := (a : F)) (b := (b : F))
    (fun w hw => emb_neg_of_isTotallyPos_neg hna w hw) (fun w hw => emb_neg_of_isTotallyPos_neg hnb w hw)
  have := (gnatSqO ha0 hb0).isHaarMeasure_muP (muSq ha0 hb0)
  unfold TamagawaNumberTwoAdelic
  rw [covolume_eq_of_continuousMulEquiv _ _ (sqPEquiv ha0 hb0) (map_gamP_sqPEquiv ha0 hb0) _ _
    (map_muP_sqPEquiv_eq_muTam ha0 hb0 hna hnb hQ), covolume_gnatSq ha0 hb0 hdiv]

variable (F) in
/-- **Input (named): the non-square half of `GnatMeasureComparisonDef`** — Weil's local-ratio identity
$\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the explicit $\Phi$ = `nsPEquiv` on the totally definite non-square models
$\langle1,-ad,-bd,abd\rangle$ ($-a, -b, d\gg0$). Fields: `nonsquare` (exactly the `nonsquare` field of
`GnatMeasureComparisonDef F`). -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
structure GnatMeasureComparisonNSDef : Prop where
  nonsquare : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (_hna : IsTotallyPos (-(a : F))) (_hnb : IsTotallyPos (-(b : F)))
    (_hdpos : IsTotallyPos (d : F)) (hQ : (qNS a b d).Nondegenerate),
    ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map
      (nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
        (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁)) = muTam (qNS a b d) hQ (fun _ => 1)

/-- **`GnatMeasureComparisonDef F` from its non-square half** (the square half is `gnatMeasureComparisonDef_square`). -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
theorem gnatMeasureComparisonDef_of_ns (hNS : GnatMeasureComparisonNSDef F) : GnatMeasureComparisonDef F :=
  ⟨gnatMeasureComparisonDef_square, hNS.nonsquare⟩

/-- **$\tau(SO_4) = 2$ for every totally real $F$**, given only the non-square half. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem quaternaryTamagawaTwo_of_ns (hNS : GnatMeasureComparisonNSDef F) : QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_measureDef (gnatMeasureComparisonDef_of_ns hNS)

/-- **`RankFourUnitSiegel F`**, given only the non-square half. -/
@[kb "weil1982" "§4.5, p. 100; §3.7; Thm 2.3.1"]
theorem rankFourUnitSiegel_of_ns (hNS : GnatMeasureComparisonNSDef F) : RankFourUnitSiegel F :=
  rankFourUnitSiegel_of_measureDef (gnatMeasureComparisonDef_of_ns hNS)

/-- **Siegel's formula for every totally positive definite form over $\mathcal O_F$ in every rank $N\ge4$, every totally
positive $m$, every totally real $F$** (any class number), given only the non-square half. -/
@[kb "siegel1935" "Hauptsatz [unverified]; weil1982 §4.5, Thm 4.5.1"]
theorem siegelFormulaAt_totallyReal_of_ns (hNS : GnatMeasureComparisonNSDef F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < QuadFormsKB.HilbertModular.realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_ge_four_of_measureDef (gnatMeasureComparisonDef_of_ns hNS) hN Q₀ hpd hm

/-- **$\tau = 2$ in every rank $N\ge4$**, given only the non-square half. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109; Thm 2.3.1"]
theorem tamagawaNumberTwo_all_ranks_of_ns (hNS : GnatMeasureComparisonNSDef F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_of_measureDef (gnatMeasureComparisonDef_of_ns hNS) hN Q₀ hpd

/-- **The mass formula in every rank $N\ge4$**, given only the non-square half. -/
@[kb "weil1982" "Thm 4.5.1, p. 109; Thm 2.3.1"]
theorem massFormula_all_ranks_of_ns (hNS : GnatMeasureComparisonNSDef F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_of_measureDef (gnatMeasureComparisonDef_of_ns hNS) hN Q₀ hpd

end QuadFormsKB.Tamagawa.Measure.Weil
