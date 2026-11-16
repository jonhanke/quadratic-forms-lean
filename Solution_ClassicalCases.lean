/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Classical.BinaryUncond
import QuadFormsKB.Tamagawa.Classical.HyperbolicRat
import QuadFormsKB.Tamagawa.Classical.Ternary
import QuadFormsKB.Tamagawa.Classical.UnitVolumeExplicit
import QuadFormsKB.Tamagawa.HeadlineFactsWeil

/-!
# Headline statements, proved: Classical cases over ℚ

The declarations of `Challenge_ClassicalCases.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/ClassicalCases.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_ClassicalCases.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## Classical special cases over ℚ

Forms over ℤ: `Siegel.sumSq k` = x₀² + … + x_{k-1}², `Classical.sumTwoSqZ` = x₀² + x₁², `Classical.pell2Z` = x₀² - 2x₁².
`Siegel.repNum Q m` = #{x ∈ ℤ^n : Q(x) = m} (a `Nat.card`); each statement with a `repNum` also states that the set of
solutions is finite. `RatBridge.up Q` is Q viewed over 𝓞_ℚ, and `Indefinite.repCount` is as in the section on
indefinite forms (representations modulo the unit group, summed over the proper classes of the genus). -/

section Classical

set_option synthInstance.maxHeartbeats 400000

open QuadFormsKB.Tamagawa.Classical QuadFormsKB.Tamagawa.RatBridge QuadFormsKB.Binary QuadFormsKB.LocalDensity
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure.Weil

/-- **Gauss's theorem on sums of three squares.** For squarefree m ≥ 1, with D the discriminant of ℚ(√-m)
(`gaussDisc m`: -m if m ≡ 3 mod 4, else -4m),
r₃(m) = c(m) · h(D)/w(D), c(m) = 24 if m ≡ 1, 2 mod 4, 48 if m ≡ 3 mod 8, 0 if m ≡ 7 mod 8,
h(D) the class number and w(D) the number of roots of unity of ℚ(√-m) (`QField D`, Mathlib's `classNumber` and
`Units.torsionOrder`). Moreover the set of x ∈ ℤ³ with x₀² + x₁² + x₂² = m is finite. -/
theorem gauss_threeSquares {m : ℤ} (hm : 1 ≤ m) (hsf : Squarefree m) {D : ℤ} [IsQuadDisc D]
    (hD : D = gaussDisc m) :
    (Siegel.repNum (Siegel.sumSq 3) m : ℝ) =
      (if m % 4 = 1 ∨ m % 4 = 2 then 24 else if m % 8 = 3 then 48 else 0) *
        (classNumber (QField D) : ℝ) / (Units.torsionOrder (QField D) : ℝ) ∧
      (Siegel.repSet (Siegel.sumSq 3) m).Finite :=
  ⟨QuadFormsKB.Tamagawa.Classical.gauss_three_squares hm hsf hD, IntQF.PosDef.repSet_finite Siegel.posDef_sumSq m⟩

/-- **Jacobi's two-squares theorem**, from Siegel's formula: for m ≥ 1,
r₂(m) = #{(x, y) ∈ ℤ² : x² + y² = m} = 4 ∑_{d | m} χ₋₄(d),
χ₋₄ the nontrivial character mod 4 (Mathlib's `ZMod.χ₄`). Moreover the set of solutions is finite. -/
theorem jacobi_twoSquares (m : ℕ) (hm : 1 ≤ m) :
    (Siegel.repNum sumTwoSqZ m : ℝ) = 4 * ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) ∧
      (Siegel.repSet sumTwoSqZ m).Finite :=
  ⟨dirichlet_sumTwoSq_r2 m hm, finite_repSet_sumTwoSqZ m⟩

/-- **Siegel's formula for x₀² + x₁² with explicit constants** (Siegel 1935, Hauptsatz for n = 2, m = 1:
c⁽¹⁾_∞ = 1/4, ε = 1/2, ∑_i v(M_i) = π/16). For every nondegenerate unary form T₀ over 𝓞_ℚ = ℤ represented by
x₀² + x₁² over ℚ (a rational frame Ξ),
∑_i n(M_i, T₀) = (π/8) · B(T₀),
B(T₀) = `binDensityProduct` = L(1, χ_E)^{-1} ∏_p L_p(1, χ_E) β_p(T₀), E = ℚ(i) = `QField (-4)`. Moreover L(1, χ_E)
exists and is positive, and the product ∏_p L_p(1, χ_E) β_p(T₀) converges unconditionally. -/
theorem siegel_twoSquares (T₀ : QuadForm (𝓞 ℚ) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame (up sumTwoSqZ) T₀) :
    ∑' i, Indefinite.repCount (up sumTwoSqZ) T₀ i =
      ENNReal.ofReal (Real.pi / 8 * binDensityProduct (up sumTwoSqZ) T₀ (QField (-4))) ∧
      HasLOne (chiE ℚ (QField (-4))) (LOne (chiE ℚ (QField (-4)))) ∧ 0 < LOne (chiE ℚ (QField (-4))) ∧
      Multipliable fun v => NF.localDensityForm v (up sumTwoSqZ) T₀ / lamL (chiE ℚ (QField (-4))) v :=
  ⟨siegel_sumTwoSq_explicit T₀ hT Ξ, (hasLOne_chiE isDiscField_sumTwoSq.finrank_eq_two).1,
    (hasLOne_chiE isDiscField_sumTwoSq.finrank_eq_two).2,
    multipliable_binDensity (up sumTwoSqZ) nondegenerate_up_sumTwoSq (QField (-4)) isDiscField_sumTwoSq T₀ hT Ξ⟩

/-- **Dirichlet's theorem for x₀² - 2x₁²**, from Siegel's formula for an indefinite binary form: for m ≥ 1,
the number of representations of m by the genus of x₀² - 2x₁² (one class) modulo its infinite unit group is
∑_{d | m} χ₈(d), χ₈ the character of ℚ(√2) (Mathlib's `ZMod.χ₈`). -/
theorem dirichlet_xSqMinusTwoYSq (m : ℕ) (hm : 1 ≤ m) :
    ∑' i, Indefinite.repCount (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) i =
      ENNReal.ofReal (∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ)) :=
  dirichlet_pell2_uncond m hm

/-- **The number of representations by x₀x₁**, from Siegel's formula for an isotropic binary form (Siegel's
excluded case): for m ∈ ℤ, m ≠ 0, the genus of ℤ² for x₀x₁ (`DVR.hyperbolic (𝓞 ℚ)`) has only one proper class, and
the number of representations of m by it modulo its unit group {±1} is d(|m|), the number of positive divisors of
|m| (Mathlib's `Nat.divisors`). -/
theorem divisorCount_xy {m : ℤ} (hm : m ≠ 0) :
    ∑' i, Indefinite.repCount (DVR.hyperbolic (𝓞 ℚ)) (DVR.unary (m : 𝓞 ℚ)) i = (m.natAbs.divisors.card : ENNReal) ∧
      Subsingleton (DC (DVR.hyperbolic (𝓞 ℚ))) :=
  ⟨tsum_repCount_hypForm_rat hm, subsingleton_DC_hypForm (F := ℚ)⟩

/-- **Siegel's formula for positive definite ternary forms over ℤ, Euler product in the natural order of the
primes** (Siegel 1935, Hauptsatz for n = 3). Let Q be a positive definite form over ℤ in 3 variables and m ≥ 1.
Then the partial products ∏_{p ≤ X} β_p(m) of the local densities converge, as X → ∞, to a limit P
(`Siegel.IsEulerProductValue Q m P`; the primes are taken in their natural order, since for n = 3 the product
need not converge unconditionally), and
a_E(m) = β_∞(m) · P.
Here a_E(m) = (∑_{[Q'] ∈ Gen(Q)} r_{Q'}(m)/|Aut(Q')|) / (∑_{[Q'] ∈ Gen(Q)} 1/|Aut(Q')|) is the average over the
GL_3(ℤ)-classes [Q'] of forms in the genus of Q (`Siegel.genusRepAvg`), r_{Q'}(m) = #{x ∈ ℤ³ : Q'(x) = m}, and
β_∞(m) = (3 ω_3 D^{-1/2}/2) m^{1/2} with ω_3 the volume of the unit ball and D = det(H/2), H the Hessian of Q
(`Siegel.aEWith Q m P` = β_∞(m) · P). Moreover the genus of Q has finitely many classes and its mass
∑_{[Q'] ∈ Gen(Q)} 1/|Aut(Q')| is positive. (The library also proves the same formula with P the regularized value
L(1, χ) · ∏_p β_p(m)(1 - χ(p)/p), `Tamagawa.RatHeadline3.siegelFormula3_rat_uncond`, on which this one rests; the
two values agree.) -/
theorem siegel_ternary_rat_natural (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) {m : ℤ} (hm : 1 ≤ m) :
    (∃ P : ℝ, Siegel.IsEulerProductValue Q m P ∧ Siegel.genusRepAvg Q m = Siegel.aEWith Q m P) ∧
      (Siegel.genusClasses Q).Finite ∧ 0 < Siegel.mass Q :=
  ⟨RatHeadline3.siegelFormula3_natural_rat_uncond Q hQ hm, (Siegel.genusFinite hQ).finite_classes,
    Siegel.mass_pos hQ (Siegel.genusFinite hQ)⟩

end Classical

end QuadFormsKB.Headlines
