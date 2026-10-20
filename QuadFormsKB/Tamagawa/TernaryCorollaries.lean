/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.TernaryAssembly
import QuadFormsKB.Tamagawa.LocalSmith
import QuadFormsKB.Tamagawa.RatBridge

/-!
# $\tau(SO) = 2$, the mass formula and Siegel's formula in every rank from the trace-zero local factors

**Layer:** $F$ totally real, $\mathcal O_F$ a PID; for the $F = \mathbb Q$ statements, $\mathbb Q$ and $\mathbb Z$.

`ternaryTamagawaTwo_of_badLocalFactors` gives `TernaryTamagawaTwo F` from the single named input
`TraceZeroBadLocalFactors F` (the local densities of the trace-zero lattices $\mathcal O_v^0$ of maximal orders at the dyadic and
ramified places). Combined with the all-rank theorems (`tamagawaNumberTwo_all_ranks_of_ternary` etc., whose odd-rank local input is
proved in `LocalSmith`) and the bridge to $\mathbb Q$ (`RatBridge`), every statement below depends on that one input only.

**Proves** `tamagawaNumberTwo_all_ranks_of_traceZero`, `massFormula_all_ranks_of_traceZero`,
`siegelFormulaAt_all_ranks_of_traceZero`, `tamagawaNumberTwo_rat_all_ranks_of_traceZero`,
`siegelFormulaAt_rat_all_ranks_of_traceZero`, `siegelFormula_int_all_ranks_of_traceZero`.

Source: Weil 1982, §3.7 and §4.5 (Thm. 3.7.1, Thm. 4.5.1).
-/

open NumberField

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.QuatOrder

section NF

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]

/-- **$\tau(SO(Q_0)) = 2$ in every rank $N \ge 3$ from the trace-zero local factors** ($F$ totally real of degree $\ge 2$,
$\mathcal O_F$ a PID, $Q_0$ totally positive definite). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; §3.7, Thm 3.7.1, p. 65"]
theorem tamagawaNumberTwo_all_ranks_of_traceZero (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (I : TraceZeroBadLocalFactors F) {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_of_ternary hd (ternaryTamagawaTwo_of_badLocalFactors I) hN Q₀ hpd

/-- **The mass formula in every rank $N \ge 3$ from the trace-zero local factors.** -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem massFormula_all_ranks_of_traceZero (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (I : TraceZeroBadLocalFactors F) {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_of_ternary hd (ternaryTamagawaTwo_of_badLocalFactors I) hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N \ge 4$ from the trace-zero local factors** (even $N$ needs no input). -/
@[kb "weil1982" "§4.5, p. 100, Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_all_ranks_of_traceZero (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (I : TraceZeroBadLocalFactors F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks_of_ternary hd (ternaryTamagawaTwo_of_badLocalFactors I) hN Q₀ hpd hm

end NF

section Rat

/-- **$\tau(SO) = 2$ over $\mathbb Q$ in every rank $N \ge 3$ from the trace-zero local factors over $\mathbb Q$.** -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 and Thm. 3.7.1, p. 65, over ℚ"]
theorem tamagawaNumberTwo_rat_all_ranks_of_traceZero (I : TraceZeroBadLocalFactors ℚ) {N : ℕ} (hN : 3 ≤ N)
    (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  RatBridge.tamagawaNumberTwo_rat_all_ranks (ternaryTamagawaTwo_of_badLocalFactors I)
    (oddRankOrbitalLocalIdentities ℚ) hN Q₀ hpd

/-- **Siegel's formula over $\mathbb Q$ in every rank $N \ge 4$ from the trace-zero local factors over $\mathbb Q$.** -/
@[kb "siegel1935" "Hauptsatz (numbers) over ℚ, every rank ≥ 4 [unverified]"]
theorem siegelFormulaAt_rat_all_ranks_of_traceZero (I : TraceZeroBadLocalFactors ℚ) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ}
    (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m :=
  RatBridge.siegelFormulaAt_rat_all_ranks (ternaryTamagawaTwo_of_badLocalFactors I)
    (oddRankOrbitalLocalIdentities ℚ) hN Q₀ hpd hm

/-- **Hanke's Siegel formula over $\mathbb Z$ in every rank $N \ge 4$ from the trace-zero local factors over $\mathbb Q$.** -/
@[kb "siegel1935" "Hauptsatz, every rank ≥ 4, Hanke's (5.3) form over ℤ [unverified]"]
theorem siegelFormula_int_all_ranks_of_traceZero (I : TraceZeroBadLocalFactors ℚ) {N : ℕ} (hN : 4 ≤ N)
    (Q : QuadForm ℤ N) (hQ : IntQF.PosDef Q) : Siegel.SiegelFormula Q :=
  RatBridge.siegelFormula_int_all_ranks (ternaryTamagawaTwo_of_badLocalFactors I)
    (oddRankOrbitalLocalIdentities ℚ) hN Q hQ

end Rat

end QuadFormsKB.Tamagawa
