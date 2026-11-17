/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Literature.Hanke2005.GHYConductorDyadic
import QuadFormsKB.Tamagawa.Indefinite.DCFinite

/-!
# Headline statements: Exact mass formulas

The Conway–Sloane mass formula, Shimura's exact mass formula (Gan, Hanke and Yu) and Hanke's exact mass formula.

Every proof here is a deliberate `sorry`. `Solution_ExactMass.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/ExactMass.json`) checks that each theorem of
`Solution_ExactMass.lean` has exactly the statement given here and depends only on the axioms `propext`,
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

/-! ## Exact mass formulas

The mass of a genus is the sum of 1/|Aut| over its classes. Siegel's theorem in its general form (the first section)
expresses it through local densities; the statements below evaluate it exactly. Over ℤ: the Conway–Sloane formula from
the genus symbols. Over totally real number fields: Shimura's exact formula for the special orthogonal group, as
computed by Gan, Hanke and Yu, for odd and for even n. Over every number field: Hanke's formula, in a corrected
general form. In the last three, F is a number field, Q₀ a form in n variables with coefficients in 𝓞 F, and
L = 𝓞_F^n is a maximal lattice for Q₀ (`Hanke2005.StdIsMaximal Q₀`: Q₀(L) ⊆ 𝓞 F, and no strictly larger lattice
has this property). The classes counted are the proper classes in the genus of L (`Tamagawa.Indefinite.DC Q₀`, the
double cosets SO(V)(F)\SO(V)(𝔸_f)/SO(L̂)), with Γ_i = SO(L_i) the unit group of the class i
(`Tamagawa.Indefinite.unitGroup Q₀ i`). -/

section ExactMass

open scoped ENNReal

open QuadFormsKB.Hanke2005 QuadFormsKB.Tamagawa.Indefinite

/-- **The Conway–Sloane mass formula over ℤ from the genus symbols** (J. H. Conway and N. J. A. Sloane,
"Low-dimensional lattices IV: the mass formula", 1988, (2), (3), §7 and §9). Let A be a symmetric n × n integer
matrix, n ≥ 3, such that the form Q(x) = xᵀAx (`LocalDensity.ofMatrixZ A`) is positive definite. Let τ be a 2-adic
symbol of A (`ConwaySloane.IsTwoSymbolOf`) whose constituents τ_k are trivial for k ≥ N₂, and for every odd prime
p dividing det A let σ_p be a p-adic symbol of A (`ConwaySloane.IsOddSymbolOf`) whose constituents are trivial
from N_p on. Then the mass of the genus of Q, ∑_{[Q'] ∈ Gen(Q)} 1/|Aut(Q')| (`Siegel.mass`), is
  m(Q) = std(n, det A) · ∏_{p | 2 det A} m_p / std_p(n, det A),
where std is the standard mass (7) (`ConwaySloane.Mass.stdMass`), std_p the standard p-mass (6)
(`ConwaySloane.Mass.stdP`), and m_p the p-mass of the symbol, formula (3) with Tables 1 and 2: the product of the
diagonal factors of the constituents (by species), the cross terms, and at p = 2 the type factor
(`ConwaySloane.Mass.pMassTwo τ N₂`, `ConwaySloane.Mass.pMassOdd p σ_p N_p`). The paper states (3) at p = 2 without
proof; it is proved here. Moreover the genus of Q has finitely many classes and its mass is positive. -/
theorem massFormula_genusSymbols {n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (τ : ConwaySloane.TwoSymbol) (N₂ : ℕ) (hτ : ConwaySloane.IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ)
    (hτN : τ.SupportedBelow N₂) (σ : ℕ → ConwaySloane.OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      ConwaySloane.IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧
        ∀ k, N p ≤ k → σ p k = ConwaySloane.OddFactor.trivial) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = ConwaySloane.Mass.stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors,
        ((if p = 2 then ConwaySloane.Mass.pMassTwo τ N₂ else ConwaySloane.Mass.pMassOdd p (σ p) (N p)) /
          (ConwaySloane.Mass.stdP p n A.det : ℝ)) ∧
      (Siegel.genusClasses (LocalDensity.ofMatrixZ A)).Finite ∧ 0 < Siegel.mass (LocalDensity.ofMatrixZ A) := by
  sorry

/-- **Shimura's exact mass formula for SO, odd n** (W. T. Gan, J. Hanke and J.-K. Yu, "On an exact mass formula of
Shimura", 2001, Proposition 7.4, with (7.1)–(7.3)). Let F be a totally real number field of degree d, and Q₀ a
nondegenerate form in n = 2k + 1 ≥ 3 variables over 𝓞 F, totally positive definite over F, with L = 𝓞_F^n maximal.
Then
  ∑_i 1/|Γ_i| = 2^{-kd} · |L(M)| · τ(SO) · ∏_𝔭 λ_𝔭,  τ(SO) = 2,
the sum over the proper classes i in the genus of L, with |L(M)| = ∏_{r=1}^{k} |ζ_F(1 - 2r)|
(`Hanke2005.lMotiveOdd F k`; each factor is written through the functional equation as
|d_F|^{2r-1/2} (2 (2r-1)!/(2π)^{2r})^d ζ_F(2r), `Hanke2005.absZetaNeg`) and λ_𝔭 the local factor of Gan, Hanke and
Yu at the prime 𝔭 (`Hanke2005.lambdaGHYAt`). The paper's L(M) is read in absolute value: ζ_F(1 - 2r) has sign
(-1)^{rd}. Moreover there are finitely many classes, every Γ_i is finite, and λ_𝔭 = 1 for all but finitely many
primes 𝔭. -/
theorem shimuraMass_odd {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (((2 : ℝ) ^ ((n / 2) * Module.finrank ℚ F))⁻¹ * lMotiveOdd F (n / 2) * 2 *
        ∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYAt v Q₀) ∧
      Finite (DC Q₀) ∧ (∀ i : DC Q₀, Finite (unitGroup Q₀ i)) ∧
      Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaGHYAt v Q₀ := by
  sorry

/-- **Shimura's exact mass formula for SO, even n** (W. T. Gan, J. Hanke and J.-K. Yu, "On an exact mass formula
of Shimura", 2001, Proposition 7.5, with (7.1)–(7.3)). Let F be a totally real number field of degree d, and Q₀ a
nondegenerate form in n = 2k ≥ 4 variables over 𝓞 F, totally positive definite over F, with L = 𝓞_F^n maximal.
Then
  ∑_i 1/|Γ_i| = 2^{-kd} · |L(M)| · τ(SO) · ∏_𝔭 λ_𝔭,  τ(SO) = 2,
the sum over the proper classes i in the genus of L, with |L(M)| = ∏_{r=1}^{k-1} |ζ_F(1 - 2r)| · |L_F(1 - k, χ)|
(`Hanke2005.lMotiveEven Q₀ k`; χ = `Hanke2005.chiK` is the quadratic character of F(√δ), δ = (-1)^k det(H)/2^n
(`Hanke2005.discK`), H the Hessian of Q₀, and the values at negative integers are written through the functional
equations, `Hanke2005.absZetaNeg`, `Hanke2005.absLNeg`) and λ_𝔭 the local factor of Gan, Hanke and Yu at the prime
𝔭 (`Hanke2005.lambdaGHYEvenAt`). The paper's L(M) is read in absolute value. Moreover there are finitely many
classes, every Γ_i is finite, and λ_𝔭 = 1 for all but finitely many primes 𝔭. -/
theorem shimuraMass_even {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (hn : 4 ≤ n)
    (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (((2 : ℝ) ^ ((n / 2) * Module.finrank ℚ F))⁻¹ * lMotiveEven Q₀ (n / 2) * 2 *
        ∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYEvenAt v Q₀) ∧
      Finite (DC Q₀) ∧ (∀ i : DC Q₀, Finite (unitGroup Q₀ i)) ∧
      Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaGHYEvenAt v Q₀ := by
  sorry

/-- **Hanke's exact mass formula over number fields, in corrected general form** (J. Hanke, "An exact mass formula
for quadratic forms over number fields", 2005, Theorem 5.1). Let F be a number field of degree d, D = |d_F|, and Q₀
a nondegenerate form in n ≥ 3 variables over 𝓞 F, of any signature, with L = 𝓞_F^n maximal. Then Hanke's mass
(`Hanke2005.hankeMass Q₀ hQ`, (5.4)–(5.6): the sum over the proper classes i in the genus of L of the covolume of
Γ_i in the archimedean group, divided by the volume vol_C of its maximal compact subgroup) is
  2 D^{⌊(n-1)²/4⌋} ∏_{j=1}^{⌊(n-1)/2⌋} (D^{1/2} ((2j-1)!/(2π)^{2j})^d ζ_F(2j)) · [L̃ : L]^{(n-1)/2} ∏_𝔭 λ'_𝔭
    · ∏_{v real} b_v · ∏_{v complex} (2^{-(n-1)(n-2)/2} π^{n(n+1)/4} ∏_{j=1}^{n} Γ(j/2)^{-1})
    · (2^{-(n-1)d/2} if n is odd; D^{1/2} ((n/2 - 1)! (2π)^{-n/2})^d L_F(n/2, χ) if n is even)
(`Hanke2005.theorem51RHSGen Q₀`), with [L̃ : L] = ∏_𝔭 [L̃_𝔭 : L_𝔭] the index of L in its dual
(`Hanke2005.dualIndexAt`), b_v Hanke's factor at a real place (`Hanke2005.bPhi`, from the Witt index
`Hanke2005.rAt`), and χ the quadratic character of F(√δ) (`Hanke2005.chiK`).
*Correction to the printed theorem.* Theorem 5.1 as printed omits Shimura's hypothesis "for odd n, the determinant
of Q₀ is at every prime a unit times a square", and is false without it. This statement has no such hypothesis: at
the primes where that condition fails (n odd), Hanke's local factor λ_𝔭 is replaced by
λ'_𝔭 = (1 + q^{-m})/2 if t_𝔭 = 1 and λ'_𝔭 = (1 - q^{-m})/2 if t_𝔭 = 3, where m = ⌊n/2⌋, q = N𝔭 and t_𝔭 is the
dimension of the anisotropic kernel of Q₀ at 𝔭 (these factors come from Gan, Hanke and Yu, Table 4); at every other
prime λ'_𝔭 = λ_𝔭 (`Hanke2005.lambdaGen`). Under Shimura's hypothesis the right side is the printed one. Moreover the
genus of L has finitely many proper classes, and [L̃_𝔭 : L_𝔭] = λ'_𝔭 = 1 for all but finitely many primes 𝔭. -/
theorem hankeMass_numberField {F : Type} [Field F] [NumberField F] {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHSGen Q₀) ∧ Finite (DC Q₀) ∧
      (Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => dualIndexAt v Q₀) ∧
      Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaGen v Q₀ := by
  sorry

end ExactMass

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.
* `QuadForm.Nondegenerate` (Defs/QuadForm.lean): det H ≠ 0.

Tamagawa number and mass formula
* `Lattices.IsTotallyPosDef`, `Lattices.IsTotallyPos` (Lattices/Finite.lean): Q(x) totally positive for x ≠ 0.
* `Lattices.genusClasses Q L` (Lattices/Finite.lean): the classes L' in the genus of L (lattices in F^n up to isometry
  by the full O(Q), improper isometries included); `Lattices.LatClass.autCard Q c` (same file): |O(M)| =
  `Nat.card (autLat Q M)` for any lattice M in the class c. The mass ∑ 1/|O(L')| is written out in the statement
  (it is `Lattices.mass Q L`, same file).

Siegel's formula for indefinite forms (namespace `Tamagawa.Indefinite` unless stated; paths in `Tamagawa/Indefinite/`)
* `DC Q₀` (ClassicalSetup.lean): SO(V)(F)\SO(V)(𝔸_f)/SO(L̂), the proper classes in the genus of L = 𝓞_F^N.
* `unitGroup Q₀ i`, `unitVolume Q₀ hQ i`, `reps`, `repMeasure Q₀ hQ m 𝔉 i` (ClassicalMeasures.lean) and
  `repMeasureOf` (ThetaUnfold.lean): Γ_i = SO(M_i) in G_∞; v(M_i) = covolume of Γ_i in G_∞ for `muArchTamSO`; the
  representations of m by M_i; ρ(M_i, m) = ∑ over Γ_i-orbits of x of the covolume of the stabilizer Γ_{i,x} in H_x for
  the stabilizer measure of the archimedean fibration 𝔉 (`ArchFibration`, ThetaUnfold.lean).

Classical cases over ℚ
* `IntQF.PosDef Q` (Literature/Universal/Basic.lean): Q(x) > 0 for every nonzero x ∈ ℤ^n.
* `Siegel.genusClasses Q`, `Siegel.QClass.repNum`, `Siegel.QClass.autCard` (Siegel/Genus.lean): the
  GL_n(ℤ)-classes of forms in the genus of Q; r_{Q'}(m) and |Aut(Q')| for a form Q' in the class.
* `Siegel.mass Q`, `Siegel.genusRepSum Q m`, `Siegel.genusRepAvg Q m` (Siegel/Mass.lean): ∑ 1/|Aut(Q')|,
  ∑ r_{Q'}(m)/|Aut(Q')| over the classes in the genus, and their quotient a_E(m).

Exact mass formulas (paths in `Literature/`)
* `LocalDensity.ofMatrixZ A` (LocalDensity/JordanForm.lean, outside `Literature/`): the form xᵀAx of an integer
  matrix A. `Siegel.mass Q`, `Siegel.genusClasses Q` and `IntQF.PosDef Q` as in the classical cases over ℚ.
* `ConwaySloane.OddFactor`, `ConwaySloane.OddSymbol`, `ConwaySloane.TwoSymbol` (ConwaySloane/Symbol.lean): the
  p-adic and 2-adic genus symbols, one constituent (dimension, sign, and at p = 2 type and oddity) for each scale p^k;
  `OddFactor.trivial` is the zero-dimensional constituent; `TwoSymbol.SupportedBelow` (ConwaySloane/Existence.lean):
  the constituents vanish from the given index on.
* `ConwaySloane.IsTwoSymbolOf`, `ConwaySloane.IsOddSymbolOf` (ConwaySloane/TwoAdicForm.lean,
  ConwaySloane/OddClassification.lean): the symbol of the p-adic Jordan decomposition of the matrix over ℚ_p.
* `ConwaySloane.Mass.stdMass n d` (ConwaySloane/Mass/StandardMass.lean): the standard mass (7),
  2 π^{-n(n+1)/4} ∏_{j=1}^{n} Γ(j/2) · ζ(2)ζ(4)⋯ζ(2s-2) · (ζ_D(s) if n is even), s = ⌈n/2⌉, D = (-1)^s d.
* `ConwaySloane.Mass.pMassOdd p σ N`, `ConwaySloane.Mass.pMassTwo τ N`, `ConwaySloane.Mass.stdP p n d`
  (ConwaySloane/Mass/PMass.lean): the p-mass (3) of a symbol (diagonal factors by Table 1 and 2, cross terms, type
  factor at p = 2) and the standard p-mass (6).
* `Hanke2005.StdIsMaximal Q₀` (Hanke2005/MassFormula.lean): 𝓞_F^n is a maximal lattice for Q₀ (O'Meara's maximal
  lattices, `OMeara.IsMaximal`, Literature/OMeara/).
* `Tamagawa.Indefinite.DC Q₀`, `Tamagawa.Indefinite.unitGroup Q₀ i` (Tamagawa/Indefinite/ClassicalSetup.lean and
  ClassicalMeasures.lean, outside `Literature/`): the proper classes in the genus of 𝓞_F^n, and Γ_i = SO(L_i).
* `Lattices.IsTotallyPosDef` as in the Tamagawa section.
* `Hanke2005.lMotiveOdd F k`, `Hanke2005.absZetaNeg F r`, `Hanke2005.lambdaGHYAt v Q₀`
  (Hanke2005/GHYMassFormula.lean): ∏_{r=1}^{k} |ζ_F(1 - 2r)|; |ζ_F(1 - 2r)| through the functional equation; the local
  factor of Gan, Hanke and Yu for odd n (1 when L_𝔭 is self-dual).
* `Hanke2005.lMotiveEven Q₀ k`, `Hanke2005.absLNeg Q₀ k`, `Hanke2005.lambdaGHYEvenAt v Q₀`
  (Hanke2005/GHYMassFormulaEven.lean): ∏_{r=1}^{k-1} |ζ_F(1 - 2r)| · |L_F(1 - k, χ)|; |L_F(1 - k, χ)| through the
  functional equation (with the norm of the conductor of χ); the local factor of Gan, Hanke and Yu for even n.
* `Hanke2005.dualIndexAt v Q₀`, `Hanke2005.anisoDim v Q₀`, `Hanke2005.discK Q₀`, `Hanke2005.chiK v Q₀`,
  `Hanke2005.lambdaAt v Q₀`, `Hanke2005.rAt Q₀ w`, `Hanke2005.hankeMass Q₀ hQ` (Hanke2005/MassFormula.lean):
  [L̃_𝔭 : L_𝔭] = |det H|_𝔭^{-1}; the dimension t_𝔭 of the anisotropic kernel at 𝔭; δ = (-1)^{n/2} det(H)/2^n; the
  character of F(√δ) at 𝔭; Hanke's λ_𝔭; the Witt index at a real place; Hanke's mass (5.4)–(5.6).
* `Hanke2005.lambdaGen v Q₀`, `Hanke2005.lambdaOddNonUnit`, `Hanke2005.theorem51RHSGen Q₀`
  (Hanke2005/TheoremFiveOneGeneral.lean): the corrected local factor λ'_𝔭 and the right side of the corrected
  Theorem 5.1; `Hanke2005.DetUnitSqAt v Q₀` (Hanke2005/GHYOddLocal.lean): det(H)/2^n is a unit times a square at 𝔭;
  `Hanke2005.bPhi` (Hanke2005/Archimedean.lean): Hanke's factor b_v at a real place; `NFEuler.dedekindZetaR`,
  `NFEuler.LFunctionNF` (Analysis/NFEulerProduct.lean, Analysis/NFLFunctions.lean, outside `Literature/`): ζ_F(s) and L_F(s, χ) as Dirichlet series (s > 1).

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).
-/

end QuadFormsKB.Headlines
