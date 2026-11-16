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
# Headline statements: Classical cases over ℚ

Gauss's three-squares theorem, Jacobi's two-squares theorem, Dirichlet's theorem for x² − 2y², the divisor count for xy, and Siegel's ternary formula in the natural order.

Every proof here is a deliberate `sorry`. `Solution_ClassicalCases.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/ClassicalCases.json`) checks that each theorem of
`Solution_ClassicalCases.lean` has exactly the statement given here and depends only on the axioms `propext`,
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
      (Siegel.repSet (Siegel.sumSq 3) m).Finite := by
  sorry

/-- **Jacobi's two-squares theorem**, from Siegel's formula: for m ≥ 1,
r₂(m) = #{(x, y) ∈ ℤ² : x² + y² = m} = 4 ∑_{d | m} χ₋₄(d),
χ₋₄ the nontrivial character mod 4 (Mathlib's `ZMod.χ₄`). Moreover the set of solutions is finite. -/
theorem jacobi_twoSquares (m : ℕ) (hm : 1 ≤ m) :
    (Siegel.repNum sumTwoSqZ m : ℝ) = 4 * ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) ∧
      (Siegel.repSet sumTwoSqZ m).Finite := by
  sorry

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
      Multipliable fun v => NF.localDensityForm v (up sumTwoSqZ) T₀ / lamL (chiE ℚ (QField (-4))) v := by
  sorry

/-- **Dirichlet's theorem for x₀² - 2x₁²**, from Siegel's formula for an indefinite binary form: for m ≥ 1,
the number of representations of m by the genus of x₀² - 2x₁² (one class) modulo its infinite unit group is
∑_{d | m} χ₈(d), χ₈ the character of ℚ(√2) (Mathlib's `ZMod.χ₈`). -/
theorem dirichlet_xSqMinusTwoYSq (m : ℕ) (hm : 1 ≤ m) :
    ∑' i, Indefinite.repCount (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) i =
      ENNReal.ofReal (∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ)) := by
  sorry

/-- **The number of representations by x₀x₁**, from Siegel's formula for an isotropic binary form (Siegel's
excluded case): for m ∈ ℤ, m ≠ 0, the genus of ℤ² for x₀x₁ (`DVR.hyperbolic (𝓞 ℚ)`) has only one proper class, and
the number of representations of m by it modulo its unit group {±1} is d(|m|), the number of positive divisors of
|m| (Mathlib's `Nat.divisors`). -/
theorem divisorCount_xy {m : ℤ} (hm : m ≠ 0) :
    ∑' i, Indefinite.repCount (DVR.hyperbolic (𝓞 ℚ)) (DVR.unary (m : 𝓞 ℚ)) i = (m.natAbs.divisors.card : ENNReal) ∧
      Subsingleton (DC (DVR.hyperbolic (𝓞 ℚ))) := by
  sorry

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
      (Siegel.genusClasses Q).Finite ∧ 0 < Siegel.mass Q := by
  sorry

end Classical

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.
* `QuadForm.Nondegenerate` (Defs/QuadForm.lean): det H ≠ 0.

Siegel's theorem
* `SiegelSpace.LatClassV.repCount Q c t` (Tamagawa/SiegelGenusV.lean): r_M(t) = #{x ∈ M : Q(x) = t} for any lattice
  M in the class c (a `Nat.card`; independent of the representative).

Tamagawa number and mass formula
* `Lattices.genusClasses Q L` (Lattices/Finite.lean): the classes L' in the genus of L (lattices in F^n up to isometry
  by the full O(Q), improper isometries included); `Lattices.LatClass.autCard Q c` (same file): |O(M)| =
  `Nat.card (autLat Q M)` for any lattice M in the class c. The mass ∑ 1/|O(L')| is written out in the statement
  (it is `Lattices.mass Q L`, same file).

`Tamagawa/Measure/`)
* `IsDiscField Q₀ E`, `chiE F E`, `lamL χ`, `muTamChi`, `muTamBin Q₀ hQ E` (Weil/BinaryMeasure.lean): [E : F] = 2 and E
  contains a square root of -det H outside F; χ_E(v) = 1, -1, 0 as v splits, is inert, ramifies in E; λ_v = 1 - χ(v)/Nv;
  L_F(1, χ)^{-1} · `muTam Q₀ hQ (lamL χ)`; the case χ = χ_E.
* `RegProd.LOne`, `RegProd.HasLOne` (Siegel/RegProd.lean, as above).

Siegel's formula for indefinite forms (namespace `Tamagawa.Indefinite` unless stated; paths in `Tamagawa/Indefinite/`)
* `DC Q₀` (ClassicalSetup.lean): SO(V)(F)\SO(V)(𝔸_f)/SO(L̂), the proper classes in the genus of L = 𝓞_F^N.
* `repMeasureT`, `RatFrame Q₀ T₀` (FrameClassical.lean): the same for representations of forms (frames X with
  Q₀ ∘ X = T₀); rational frames. `Measure.Weil.RatSphere Q₀ ρ` (Measure/Weil/SphereOrbitsNF.lean): {η ∈ F^N : Q₀(η) = ρ}.
* `Indefinite.repCount Q₀ T₀ i` (CorankOneCount.lean): #(Γ_i\R(M_i, T₀)) in [0, ∞], R(M_i, T₀) = `repsT`.

Classical cases over ℚ
* `Siegel.sumSq k`, `Siegel.repNum`, `Siegel.repSet` (Siegel/FourSquares.lean, Siegel/Genus.lean): x₀² + … + x_{k-1}²;
  #{x ∈ ℤ^n : Q(x) = m} (`Nat.card`) and the set itself.
* `Tamagawa.Classical.sumTwoSqZ`, `pell2Z`, `gaussDisc` (Tamagawa/Classical/Basic.lean): x₀² + x₁², x₀² - 2x₁², the
  discriminant of ℚ(√-m). `Binary.QField D`, `Binary.IsQuadDisc D` (Binary/QuadraticField.lean): the quadratic field
  of discriminant D. `Tamagawa.RatBridge.up Q` (Tamagawa/RatBridge.lean): Q over 𝓞_ℚ.
* `LocalDensity.DVR.hyperbolic A` (LocalDensity/FormDensityHyperbolic.lean): the form x₀x₁ over A.
* `IntQF.PosDef Q` (Literature/Universal/Basic.lean): Q(x) > 0 for every nonzero x ∈ ℤ^n.
* `Siegel.genusClasses Q`, `Siegel.QClass.repNum`, `Siegel.QClass.autCard` (Siegel/Genus.lean): the
  GL_n(ℤ)-classes of forms in the genus of Q; r_{Q'}(m) and |Aut(Q')| for a form Q' in the class.
* `Siegel.mass Q`, `Siegel.genusRepSum Q m`, `Siegel.genusRepAvg Q m` (Siegel/Mass.lean): ∑ 1/|Aut(Q')|,
  ∑ r_{Q'}(m)/|Aut(Q')| over the classes in the genus, and their quotient a_E(m).
* `Siegel.eulerFactor Q m p`, `Siegel.eulerPartialProd Q m X`, `Siegel.IsEulerProductValue Q m P`,
  `Siegel.betaInf Q m`, `Siegel.aEWith Q m P` (Siegel/LocalProduct.lean): β_p(m); ∏_{p ≤ X} β_p(m); these
  partial products tend to P as X → ∞; β_∞(m); β_∞(m) · P.

Exact mass formulas (paths in `Literature/`)
* `Tamagawa.Indefinite.DC Q₀`, `Tamagawa.Indefinite.unitGroup Q₀ i` (Tamagawa/Indefinite/ClassicalSetup.lean and
  ClassicalMeasures.lean, outside `Literature/`): the proper classes in the genus of 𝓞_F^n, and Γ_i = SO(L_i).

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).

Lattices and sums of squares (new in 0.5.0)
* `Siegel.repNum Q m` and `Siegel.repSet Q m`: the number (`Nat.card`) and the set of x ∈ ℤⁿ with Q(x) = m;
  `Siegel.sumSq n` = x₀² + ⋯ + x_{n−1}²; `MorenoWagstaff.polygonal r k` = k + (r − 2)·k(k − 1)/2.
-/

end QuadFormsKB.Headlines
