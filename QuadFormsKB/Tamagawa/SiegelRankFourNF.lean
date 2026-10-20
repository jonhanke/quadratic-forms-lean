import QuadFormsKB.Tamagawa.Measure.Weil.GnatTamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.GnatComparison

/-!
# Siegel's formula in rank 4 for every form, every totally real field

`siegelFormulaAt_four_of_quaternary_nf` (`RankFourFromTau.lean`) covers only the split lattices $\mathcal O_F\perp\mathcal O_F^3$ at
$m = m_0$, and the rank-$\ge 5$ headlines (`siegelFormulaAt_of_quaternary_nf`) start at rank $5$ because they take the complement's
$\tau$ from the quaternary induction. In rank $4$ the complement is ternary, and $\tau = 2$ for every ternary form over $\mathcal O_F$
is proved for every totally real $F$ (`tamagawaNumberTwo_ternary_nf`). So `siegelFormulaAt_of_local` (rank $N = n + 1 \ge 4$,
no split shape, no condition on the lattice) gives Siegel's formula for **every** totally positive definite quaternary form and
every totally positive $m$, any class number, from $\tau(SO_4) = 2$ alone.

* `siegelFormulaAt_rankFour_of_quaternary_nf`: from `QuaternaryTamagawaTwo F`.
* `siegelFormulaAt_rankFour_of_gnatComparison`: from `GnatTamagawaComparison F`.
* `siegelFormulaAt_ge_four_of_gnatComparison`: every rank $N \ge 4$ in one statement (rank $4$ here, rank $\ge 5$ from
  `siegelFormulaAt_all_ranks_of_gnatComparison`).
* `siegelFormulaAt_ge_four_of_measureDef`: the same from the smaller input `GnatMeasureComparisonDef F` (only the
  measure identity Φ_*μ_P = muTam for the definite models; the adelic isomorphisms Φ are proved).

Sources: Weil 1982, §4.5, p. 100 (Siegel's theorem from $\tau = 2$) and Thm. 3.7.1 ($m = 4$), p. 65.
-/

open NumberField

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices QuadForm HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Siegel's formula for numbers in rank $4$, for every totally positive definite quaternary form over $\mathcal O_F$** and every
totally positive $m$, every totally real $F$ (any class number), given $\tau(SO_4) = 2$ (`QuaternaryTamagawaTwo F`). The complement's
$\tau$ is the proved ternary case (`tamagawaNumberTwo_ternary_nf`); the local orbital identities are proved (`orbitalLocalIdentities`). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel from τ = 2), rank 4, every form; any class number, given τ(SO_4) = 2"]
theorem siegelFormulaAt_rankFour_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) (Q₀ : QuadForm (𝓞 F) 4)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_of_local (n := 3) Q₀ hpd le_rfl
    (orbitalLocalIdentities Q₀ (nondegenerate_of_totallyPosDef' hpd)) (h4.tau_eq_two Q₀ hpd)
    (fun Q' hQ' => tamagawaNumberTwo_ternary_nf Q' hQ') hm

/-- **Siegel's formula in rank $4$ for every form, every totally real field**, given `GnatTamagawaComparison F`. -/
@[kb "weil1982" "§4.5, p. 100; Thm 3.7.1 (m = 4), p. 65; rank 4, every form, any class number, given the measure comparison"]
theorem siegelFormulaAt_rankFour_of_gnatComparison (hC : Measure.Weil.GnatTamagawaComparison F)
    (Q₀ : QuadForm (𝓞 F) 4) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_rankFour_of_quaternary_nf (Measure.Weil.quaternaryTamagawaTwo_of_gnatComparison hC) Q₀ hpd hm

/-- **Siegel's formula for numbers in every rank $N \ge 4$, every totally positive definite form over $\mathcal O_F$, every totally
real field** (any class number), given `GnatTamagawaComparison F`. -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; every rank ≥ 4, any class number, given the measure comparison"]
theorem siegelFormulaAt_ge_four_of_gnatComparison (hC : Measure.Weil.GnatTamagawaComparison F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m := by
  obtain rfl | h5 := eq_or_lt_of_le hN
  · exact siegelFormulaAt_rankFour_of_gnatComparison hC Q₀ hpd hm
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    exact Measure.Weil.siegelFormulaAt_all_ranks_of_gnatComparison hC (by omega) Q₀ hpd hm

/-- **Siegel's formula for numbers in every rank $N \ge 4$, every totally positive definite form over $\mathcal O_F$, every totally
real field** (any class number), given only the measure identity `GnatMeasureComparisonDef F` (Weil's Thm 2.3.1, ∏ r_v = 1, for
the definite models; the adelic isomorphisms `sqPEquiv`, `nsPEquiv` are proved). -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; Thm 2.3.1; every rank ≥ 4, any class number, given the measure identity"]
theorem siegelFormulaAt_ge_four_of_measureDef (hM : Measure.Weil.GnatMeasureComparisonDef F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m := by
  obtain rfl | h5 := eq_or_lt_of_le hN
  · exact siegelFormulaAt_rankFour_of_quaternary_nf (Measure.Weil.quaternaryTamagawaTwo_of_measureDef hM) Q₀ hpd hm
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    exact Measure.Weil.siegelFormulaAt_all_ranks_of_measureDef hM (by omega) Q₀ hpd hm

end QuadFormsKB.Tamagawa
