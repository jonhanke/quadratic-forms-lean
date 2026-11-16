/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Cauchy
import QuadFormsKB.Literature.MorenoWagstaff.Ch8Sprague
import QuadFormsKB.Literature.MorenoWagstaff.Remark65Even060

/-!
# Headline statements, proved: C. J. Moreno and S. S. Wagstaff, Jr., Sums of Squares of Integers

The declarations of `Challenge_MorenoWagstaff.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/MorenoWagstaff.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_MorenoWagstaff.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## Sums of squares and polygonal numbers

Theorems of C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers* (2005): Jacobi's four-squares
formula, Cauchy's polygonal number theorem and Sprague's theorem on sums of distinct squares. -/

section SumsOfSquares

/-- **Jacobi's four-squares formula** (C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers*, Chapman & Hall/CRC, 2005, Theorem 2.6, p. 29). For n ≥ 1, the number
r₄(n) = #{x ∈ ℤ⁴ : x₀² + x₁² + x₂² + x₃² = n} (`Siegel.repNum (Siegel.sumSq 4) n`) is 8σ(n) for n odd and 24σ(m)
for n even, where σ is the sum of divisors (`ArithmeticFunction.sigma 1`) and m = n / 2^{v₂(n)} is the largest odd
divisor of n (`ordCompl[2] n`). Moreover the set of such x is finite. -/
theorem jacobi_fourSquares (n : ℕ) (hn : 0 < n) :
    Siegel.repNum (Siegel.sumSq 4) n =
        (if Odd n then 8 * ArithmeticFunction.sigma 1 n else 24 * ArithmeticFunction.sigma 1 (ordCompl[2] n)) ∧
      (Siegel.repSet (Siegel.sumSq 4) n).Finite :=
  ⟨QuadFormsKB.MorenoWagstaff.theorem26 n hn, IntQF.PosDef.repSet_finite Siegel.posDef_sumSq _⟩

/-- **Cauchy's polygonal number theorem** (C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers*, Chapman & Hall/CRC, 2005, Theorem 2.9, p. 54). For m ≥ 3, every positive
integer n is the sum of four polygonal numbers of order m + 2 and a number r ≤ m − 2 (that is, r further
polygonal numbers equal to 1): n = p(t) + p(u) + p(v) + p(w) + r with p(k) = k + m·k(k − 1)/2
(`MorenoWagstaff.polygonal (m + 2) k`). So n is a sum of m + 2 polygonal numbers of order m + 2, at most four of
them different from 0 and 1. -/
theorem cauchy_polygonalNumbers (m n : ℕ) (hm : 3 ≤ m) (hn : 0 < n) :
    ∃ t u v w r : ℕ, r ≤ m - 2 ∧
      n = MorenoWagstaff.polygonal (m + 2) t + MorenoWagstaff.polygonal (m + 2) u +
        MorenoWagstaff.polygonal (m + 2) v + MorenoWagstaff.polygonal (m + 2) w + r :=
  QuadFormsKB.MorenoWagstaff.theorem29 m n hm hn

/-- **Sprague's theorem: sums of distinct squares** (R. Sprague, 1948; C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers*, Chapman & Hall/CRC, 2005, §8.4, p. 328). A positive
integer is a sum of distinct positive squares if and only if it is not one of the 31 numbers 2, 3, 6, 7, 8, 11,
12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32, 33, 43, 44, 47, 48, 60, 67, 72, 76, 92, 96, 108, 112, 128; in
particular every integer greater than 128 is. (*Erratum:* the book says 32 exceptions; its list has 31.) -/
theorem sprague_distinctSquares (n : ℕ) (hn : 0 < n) :
    (∃ S : Finset ℕ, (∀ k ∈ S, 0 < k) ∧ ∑ k ∈ S, k ^ 2 = n) ↔
      n ∉ ({2, 3, 6, 7, 8, 11, 12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32, 33, 43, 44, 47, 48, 60, 67, 72, 76, 92,
      96, 108, 112, 128} : Finset ℕ) :=
  QuadFormsKB.MorenoWagstaff.spragueTheorem n hn

end SumsOfSquares

/-! ## Hardy's theorem on sums of squares

C. J. Moreno and S. S. Wagstaff, Jr. (2005), Theorem 6.1: the number of representations of n as a sum of s squares
equals the singular series for 5 ≤ s ≤ 8, and differs from it by O(n^{s/4}) for s > 8. -/

section HardySquares

/-- **Hardy's theorem on sums of squares** (C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers*, Chapman & Hall/CRC, 2005, Theorem 6.1, p. 189). For s ≥ 1 let
r_s(n) = #{x ∈ ℤˢ : x₀² + ⋯ + x_{s−1}² = n} (`Siegel.repNum (Siegel.sumSq s) n`) and let
ρ_s(n) = n^{s/2−1} π^{s/2} / Γ(s/2) · ∑_{m ≥ 1} A_m(n) be the singular series (`MorenoWagstaff.singularSeriesSq s n`,
the book's (6.17)), with A_m(n) = ∑_{h mod m, (h, m) = 1} (S_{h,m}/m)^s e^{−2πinh/m} and S_{h,m} the quadratic Gauss
sum (`Siegel.SingularSeries.ssTerm (Siegel.sumSq s) n m`). Then r_s(n) = ρ_s(n) for 5 ≤ s ≤ 8 and n ≥ 1, and for
every s > 8 there is a constant C with |r_s(n) − ρ_s(n)| ≤ C n^{s/4} for all n ≥ 1. Moreover (so that every term
is meaningful) the series ∑_m A_m(n) converges for s ≥ 5 and the set of representations is finite. -/
theorem hardy_sumsOfSquares :
    (∀ s n : ℕ, 5 ≤ s → s ≤ 8 → 0 < n →
      (Siegel.repNum (Siegel.sumSq s) n : ℂ) = MorenoWagstaff.singularSeriesSq s n) ∧
    (∀ s : ℕ, 8 < s → ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      ‖(Siegel.repNum (Siegel.sumSq s) n : ℂ) - MorenoWagstaff.singularSeriesSq s n‖ ≤ C * (n : ℝ) ^ ((s : ℝ) / 4)) ∧
    (∀ s n : ℕ, 5 ≤ s → Summable (Siegel.SingularSeries.ssTerm (Siegel.sumSq s) (n : ℤ))) ∧
    (∀ s n : ℕ, (Siegel.repSet (Siegel.sumSq s) n).Finite) :=
  ⟨QuadFormsKB.MorenoWagstaff.theorem61.1, QuadFormsKB.MorenoWagstaff.theorem61.2,
    fun _ n hs => QuadFormsKB.MorenoWagstaff.summable_ssTerm_sumSq hs n,
    fun _ _ => IntQF.PosDef.repSet_finite Siegel.posDef_sumSq _⟩

end HardySquares

/-! ## The singular series of 2k squares (new in 0.6.0)

C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers* (2005), Remark 6.5, for every even k ≥ 4. -/

section SingularSeries

theorem singularSeries_twoK_squares {k n : ℕ} (hk : Even k) (hk4 : 4 ≤ k) (hn : 0 < n) :
    MorenoWagstaff.singularSeriesSq (2 * k) n =
      (2 * k : ℂ) / ((2 ^ k - 1) * |(bernoulli k : ℝ)|) *
        ∑ d ∈ n.divisors, (d : ℂ) ^ (k - 1) * (-1 : ℂ) ^ ((d + k / 2) * (n / d - 1)) :=
  QuadFormsKB.MorenoWagstaff.remark65Even k n hk hk4 hn

end SingularSeries

end QuadFormsKB.Headlines
