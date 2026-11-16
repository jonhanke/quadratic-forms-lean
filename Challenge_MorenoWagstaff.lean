/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Cauchy
import QuadFormsKB.Literature.MorenoWagstaff.Ch8Sprague
import QuadFormsKB.Literature.MorenoWagstaff.Remark65Even060

/-!
# Headline statements: C. J. Moreno and S. S. Wagstaff, Jr., Sums of Squares of Integers

Jacobi's four-squares formula, Cauchy's polygonal number theorem, Sprague's theorem, Hardy's theorem on sums of squares and the singular series of 2k squares.

Every proof here is a deliberate `sorry`. `Solution_MorenoWagstaff.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/MorenoWagstaff.json`) checks that each theorem of
`Solution_MorenoWagstaff.lean` has exactly the statement given here and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The headlines are split into one file per book or topic (`comparator.json`
lists them), so that each check loads only what its statements need.

**Conventions.** Q denotes a quadratic form (`QuadForm R n`: the polynomial ∑_{i ≤ j} c_ij x_i x_j) or a quadratic
form on an abstract vector space (Mathlib's `QuadraticForm F V`). Classes of lattices are isometry classes under the
full orthogonal group O(Q) (improper isometries included), and every lattice L' in a genus is weighted by 1/|O(L')|.
F is a number field with ring of integers 𝓞 F; "totally positive" means positive under every real embedding.

**No hidden default values.** Some notions in the formulas take a default value outside their intended range:
`∏'` (Mathlib's unconditional infinite product) is `1` when the product does not converge unconditionally, `∑ᶠ` is
`0` over an infinite set, `Nat.card` is `0` for an infinite type, and `L_F(1, χ)` (`LOne`, a limit) is a junk value
when the limit does not exist. Each headline therefore states, as extra conjuncts, the facts that make every such
term meaningful: the genus has finitely many classes, the automorphism groups and representation sets are finite,
the infinite products converge unconditionally, and L_F(1, χ) exists (and is positive).
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
      (Siegel.repSet (Siegel.sumSq 4) n).Finite := by
  sorry

/-- **Cauchy's polygonal number theorem** (C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers*, Chapman & Hall/CRC, 2005, Theorem 2.9, p. 54). For m ≥ 3, every positive
integer n is the sum of four polygonal numbers of order m + 2 and a number r ≤ m − 2 (that is, r further
polygonal numbers equal to 1): n = p(t) + p(u) + p(v) + p(w) + r with p(k) = k + m·k(k − 1)/2
(`MorenoWagstaff.polygonal (m + 2) k`). So n is a sum of m + 2 polygonal numbers of order m + 2, at most four of
them different from 0 and 1. -/
theorem cauchy_polygonalNumbers (m n : ℕ) (hm : 3 ≤ m) (hn : 0 < n) :
    ∃ t u v w r : ℕ, r ≤ m - 2 ∧
      n = MorenoWagstaff.polygonal (m + 2) t + MorenoWagstaff.polygonal (m + 2) u +
        MorenoWagstaff.polygonal (m + 2) v + MorenoWagstaff.polygonal (m + 2) w + r := by
  sorry

/-- **Sprague's theorem: sums of distinct squares** (R. Sprague, 1948; C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers*, Chapman & Hall/CRC, 2005, §8.4, p. 328). A positive
integer is a sum of distinct positive squares if and only if it is not one of the 31 numbers 2, 3, 6, 7, 8, 11,
12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32, 33, 43, 44, 47, 48, 60, 67, 72, 76, 92, 96, 108, 112, 128; in
particular every integer greater than 128 is. (*Erratum:* the book says 32 exceptions; its list has 31.) -/
theorem sprague_distinctSquares (n : ℕ) (hn : 0 < n) :
    (∃ S : Finset ℕ, (∀ k ∈ S, 0 < k) ∧ ∑ k ∈ S, k ^ 2 = n) ↔
      n ∉ ({2, 3, 6, 7, 8, 11, 12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32, 33, 43, 44, 47, 48, 60, 67, 72, 76, 92,
      96, 108, 112, 128} : Finset ℕ) := by
  sorry

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
    (∀ s n : ℕ, (Siegel.repSet (Siegel.sumSq s) n).Finite) := by
  sorry

end HardySquares

/-! ## The singular series of 2k squares (new in 0.6.0)

C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers* (2005), Remark 6.5, for every even k ≥ 4. -/

section SingularSeries

/-- **The singular series of 2k squares as a divisor sum** (Moreno–Wagstaff, *Sums of Squares of Integers*, Chapman
& Hall/CRC, 2005, Remark 6.5, the case of k even). For every even k ≥ 4 and every n ≥ 1, the singular series
ρ_{2k}(n) of the sum of 2k squares (`MorenoWagstaff.singularSeriesSq (2k) n`, the product over all primes of the
local factors of Hardy's singular series) equals
2k / ((2^k − 1) |B_k|) · ∑_{d | n} d^{k−1} (−1)^{(d + k/2)(n/d − 1)},
with B_k the k-th Bernoulli number (Mathlib's `bernoulli`). -/
theorem singularSeries_twoK_squares {k n : ℕ} (hk : Even k) (hk4 : 4 ≤ k) (hn : 0 < n) :
    MorenoWagstaff.singularSeriesSq (2 * k) n =
      (2 * k : ℂ) / ((2 ^ k - 1) * |(bernoulli k : ℝ)|) *
        ∑ d ∈ n.divisors, (d : ℂ) ^ (k - 1) * (-1 : ℂ) ^ ((d + k / 2) * (n / d - 1)) := by
  sorry

end SingularSeries

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Classical cases over ℚ
* `Siegel.sumSq k`, `Siegel.repNum`, `Siegel.repSet` (Siegel/FourSquares.lean, Siegel/Genus.lean): x₀² + … + x_{k-1}²;
  #{x ∈ ℤ^n : Q(x) = m} (`Nat.card`) and the set itself.
* `Siegel.genusClasses Q`, `Siegel.QClass.repNum`, `Siegel.QClass.autCard` (Siegel/Genus.lean): the
  GL_n(ℤ)-classes of forms in the genus of Q; r_{Q'}(m) and |Aut(Q')| for a form Q' in the class.

Lattices and sums of squares (new in 0.5.0)
* `Siegel.repNum Q m` and `Siegel.repSet Q m`: the number (`Nat.card`) and the set of x ∈ ℤⁿ with Q(x) = m;
  `Siegel.sumSq n` = x₀² + ⋯ + x_{n−1}²; `MorenoWagstaff.polygonal r k` = k + (r − 2)·k(k − 1)/2.

New in 0.5.1
* `MorenoWagstaff.singularSeriesSq s n` (Literature/MorenoWagstaff/Ch6to8Statements.lean): the singular series ρ_s(n);
  `Siegel.SingularSeries.ssTerm Q n m` (Siegel/SingularSeries.lean): its m-th term A_m(n) (0 for m = 0).
-/

end QuadFormsKB.Headlines
