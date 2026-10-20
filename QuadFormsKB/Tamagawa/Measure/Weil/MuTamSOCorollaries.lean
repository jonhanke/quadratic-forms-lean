import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.TernaryTamagawaNF
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal

/-!
# `TamagawaNumberTwoAdelic` in the definite case

Corollaries of `tamagawaNumberTwoAdelic_iff` (`MuTamSO.lean`): the library's proved instances of $\tau(SO(Q_0)) = 2$ for totally
positive definite forms over totally real fields give Weil's adelic statement for the Tamagawa measure `muTam`.

* `tamagawaNumberTwoAdelic_ternary`: every totally positive definite ternary form over every totally real field (any class
  number; from `tamagawaNumberTwo_ternary_nf`). Unconditional.
* `tamagawaNumberTwoAdelic_all_ranks`: every rank $N\ge3$, $F$ totally real of degree $\ge2$ with $\mathcal O_F$ a PID (from
  `tamagawaNumberTwo_all_ranks_uncond`). Unconditional.
* `tamagawaNumberTwoAdelic_rat`: every rank $N\ge3$ over $\mathbb Q$ (from `tamagawaNumberTwo_rat_all_ranks_uncond`).
  Unconditional.
* `tamagawaNumberTwoAdelic_all_ranks_of_rankFour`: every rank $N\ge4$, every totally real $F$ (any class number), given the
  named input `RankFourUnitSiegel F` (from `tamagawaNumberTwo_all_ranks_nf`).
-/

open NumberField

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Weil's adelic $\tau(SO(V)) = 2$ for every totally positive definite ternary form over every totally real field**
(any class number). -/
@[kb "weil1982" "Thm 3.7.1 (m = 3), p. 65; §2.4, p. 23"]
theorem tamagawaNumberTwoAdelic_ternary (Q₀ : QuadForm (𝓞 F) 3) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwoAdelic Q₀ hQ :=
  (tamagawaNumberTwoAdelic_iff Q₀ hQ (by norm_num) hpd (LatChange.isIntegral_std Q₀)).mpr
    (tamagawaNumberTwo_ternary_nf Q₀ hpd)

/-- **Weil's adelic $\tau(SO(V)) = 2$ in every rank $N\ge3$** for totally positive definite forms over a totally real
field of degree $\ge 2$ whose ring of integers is a PID. -/
@[kb "weil1982" "Thm 4.5.1, p. 109; Thm 3.7.1, p. 65; §2.4, p. 23"]
theorem tamagawaNumberTwoAdelic_all_ranks [IsPrincipalIdealRing (𝓞 F)] (hd : 2 ≤ Fintype.card (InfinitePlace F))
    {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (formF Q₀)) :
    TamagawaNumberTwoAdelic Q₀ hQ :=
  (tamagawaNumberTwoAdelic_iff Q₀ hQ (by omega) hpd (LatChange.isIntegral_std Q₀)).mpr
    (tamagawaNumberTwo_all_ranks_uncond hd hN Q₀ hpd)

/-- **Weil's adelic $\tau(SO(V)) = 2$ in every rank $N\ge4$ over every totally real field** (any class number), given the
named input `RankFourUnitSiegel F`. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109; §2.4, p. 23; given rank-4 Siegel for m = 1"]
theorem tamagawaNumberTwoAdelic_all_ranks_of_rankFour (hS : RankFourUnitSiegel F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (formF Q₀)) :
    TamagawaNumberTwoAdelic Q₀ hQ :=
  (tamagawaNumberTwoAdelic_iff Q₀ hQ (by omega) hpd (LatChange.isIntegral_std Q₀)).mpr
    (tamagawaNumberTwo_all_ranks_nf hS hN Q₀ hpd)

/-- **Weil's adelic $\tau(SO(V)) = 2$ over $\mathbb Q$ in every rank $N\ge3$** (positive definite forms). -/
@[kb "weil1982" "Thm 4.5.1, p. 109 and Thm 3.7.1, p. 65, over ℚ; §2.4, p. 23"]
theorem tamagawaNumberTwoAdelic_rat {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwoAdelic Q₀ hQ :=
  (tamagawaNumberTwoAdelic_iff Q₀ hQ (by omega) hpd (LatChange.isIntegral_std Q₀)).mpr
    (tamagawaNumberTwo_rat_all_ranks_uncond hN Q₀ hpd)

end QuadFormsKB.Tamagawa.Measure.Weil
