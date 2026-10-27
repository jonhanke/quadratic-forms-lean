/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Defs.QuadForm
import QuadFormsKB.Defs.Rational
import QuadFormsKB.Defs.NumberField
import QuadFormsKB.HilbertModular.Congruence
import QuadFormsKB.HilbertModular.GenusTheta
import QuadFormsKB.Lattices.Basic
import QuadFormsKB.Lattices.Finite
import QuadFormsKB.Siegel.RegProd
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Tamagawa.MassInduction
import QuadFormsKB.Tamagawa.SiegelClassical
import QuadFormsKB.Tamagawa.SiegelGenusV
import QuadFormsKB.Tamagawa.SiegelQuadSpace
import QuadFormsKB.Tamagawa.SiegelSpace
import QuadFormsKB.Tamagawa.SiegelSpaceChars
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.Measure.Weil.SpaceHeadlines
import QuadFormsKB.Tamagawa.Measure.Weil.SpaceBinary
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsotropic
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropic
import QuadFormsKB.Tamagawa.Measure.Weil.SphereOrbitsNF
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphere
import QuadFormsKB.Tamagawa.Indefinite.ClassicalMeasures
import QuadFormsKB.Tamagawa.Indefinite.SiegelIndefinite
import QuadFormsKB.Tamagawa.Indefinite.SiegelComplex
import QuadFormsKB.Tamagawa.Indefinite.FrameClassical
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefinite
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteNF
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteRank2
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteIso
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteChecks
import QuadFormsKB.Tamagawa.Indefinite.IsoMeasures
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernary
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernaryIso
import QuadFormsKB.Tamagawa.Indefinite.CorankOneCount
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne
import QuadFormsKB.Tamagawa.FrameRepMass
import QuadFormsKB.Tamagawa.FrameSiegel
import QuadFormsKB.Tamagawa.FrameSiegelReg
import QuadFormsKB.Tamagawa.Classical.Basic
import QuadFormsKB.Binary.SiegelBinaryChecks
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Binary.QuadraticField
import QuadFormsKB.Siegel.FourSquares
import QuadFormsKB.Siegel.Genus
-- Imported last: QuadFormsKB.LocalDensity.NF.det_hessian_Qp is declared in both NFLocalGeneral and NFFormDensity
-- (same statement), and the later import wins; this order matches the library root file, so Challenge and
-- Solution see the same constant (checked by lake comparator).
import QuadFormsKB.LocalDensity.NFFormDensity

/-!
# Headline statements

This file is the one place to read to check **what the library claims**. It states the headline results; every
proof here is a deliberate `sorry`, one per advertised theorem. The proofs are in `Solution.lean`, which declares the
same theorems and proves each by citing library theorems (the main theorem, and lemmas for the finiteness and
convergence conjuncts). `lake comparator` (configured by `comparator.json`) checks that each theorem of
`Solution.lean` has exactly the statement given here and depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`. To trust a headline one needs to read only

* this file,
* the definitions it names, listed with file pointers in the section "Definitions used" at the end, and
* Mathlib.

This file imports only the library modules that define the notions in the statements (they also contain proofs,
which the statements do not depend on).

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

/-! ## Siegel's theorem over totally real number fields

Setting: F a totally real number field, (V, Q) a totally positive definite quadratic space over F of dimension n,
L an 𝓞 F-lattice in V (of any Steinitz class, so not necessarily free) on which Q is integral, and m ∈ 𝓞 F totally
positive. In the statements, n is local notation for `finrank F V`. In each formula the left side is

  ∑ over classes L' in Gen(L) of r_{L'}(m)/|O(L')|

(in Lean: `∑ᶠ c ∈ genusClassesV Q L` of `LatClassV.repCount Q c m / LatClassV.autCard Q c`), and the right side
starts with the mass ∑ over classes L' in Gen(L) of 1/|O(L')| (the `∑ᶠ` of `(LatClassV.autCard Q c)⁻¹`). On the right,
d_F is the discriminant of F, N𝔡(L) the norm of the discriminant ideal of L, β_σ(m) = π^{n/2}/Γ(n/2) · σ(m)^{(n-2)/2}
the real density at the embedding σ, and β_𝔭(L, m) the classical local density of L at the prime 𝔭 (all named in
"Definitions used"). -/

section Siegel

-- `IsScalarTower (𝓞 F) F V` says the two scalar actions on V agree: (a • c) • v = a • (c • v) for a ∈ 𝓞 F, c ∈ F.
-- So the 𝓞 F-module structure (needed for lattices L ⊆ V) is the restriction of the F-vector-space structure.
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {V : Type*} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
  {L : Submodule (𝓞 F) V} [L.IsLattice F]

-- In this section `n` is notation for the dimension `finrank F V` of V over F (pure syntax: it unfolds to
-- `finrank F V` when the statement is elaborated). Its scope ends with the section, so the later `{n : ℕ}` variables
-- are unaffected.
set_option hygiene false in
local notation "n" => finrank F V

/-- **Siegel's theorem, rank n ≥ 4.** With the setting above,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-(n-1)/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · ∏_𝔭 β_𝔭(L, m).
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
and the product ∏_𝔭 β_𝔭(L, m) converges unconditionally. -/
theorem siegel_totallyReal (hn : 4 ≤ n) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((n : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity n ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        ∏' v, intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      Multipliable fun v => intrinsicBetaV v Q L m := by
  sorry

/-- **Siegel's theorem, rank 3** (Euler product regularized by L(1, χ_m)). With the setting above and n = 3,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1} · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)
  · L_F(1, χ_m) · ∏_𝔭 β_𝔭(L, m) (1 - χ_m(𝔭)/N𝔭),
where χ_m is the quadratic character of F(√(-2m·det H))/F, H the Hessian of Q in a basis of V (this version
uses the basis `finBasisOfFinrankEq`; see the next theorem for a basis-free character).
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
the limit L_F(1, χ_m) = lim_{s→1⁺} L_F(s, χ_m) exists and is positive, and the corrected product
∏_𝔭 β_𝔭(L, m) (1 - χ_m(𝔭)/N𝔭) converges unconditionally. -/
theorem siegel_totallyReal_rank3 (h : n = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m) 1 fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m)
        (LOne (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m)) ∧
      0 < LOne (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m) ∧
      Multipliable fun v => intrinsicBetaV v Q L m *
        (1 - spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 3, basis-free character.** As `siegel_totallyReal_rank3`, with χ_m the character of
F(√(-2m·disc Q))/F defined without choosing a basis, and the same extra conjuncts. -/
theorem siegel_totallyReal_rank3' (h : n = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3V Q m) 1 fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar3V Q m) (LOne (spaceChar3V Q m)) ∧ 0 < LOne (spaceChar3V Q m) ∧
      Multipliable fun v => intrinsicBetaV v Q L m * (1 - spaceChar3V Q m v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 2** (factor 1/2; Euler product regularized by L(1, χ_Q)^{-1}). With the setting above
and n = 2,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (1/2) · (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · L_F(1, χ_Q)^{-1} · ∏_𝔭 β_𝔭(L, m) (1 - χ_Q(𝔭)/N𝔭)^{-1},
where χ_Q is the quadratic character of F(√(-det H))/F, H the Hessian of Q in the basis `finBasisOfFinrankEq`.
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
the limit L_F(1, χ_Q) = lim_{s→1⁺} L_F(s, χ_Q) exists and is positive, and the corrected product
∏_𝔭 β_𝔭(L, m) (1 - χ_Q(𝔭)/N𝔭)^{-1} converges unconditionally. -/
theorem siegel_totallyReal_rank2 (h : n = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (1 / 2 : ℝ) * (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h))) (-1) fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h)))
        (LOne (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h)))) ∧
      0 < LOne (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h))) ∧
      Multipliable fun v => intrinsicBetaV v Q L m *
        (1 - spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h)) v / (NFEuler.normP v : ℝ)) ^ (-1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 2, basis-free character.** As `siegel_totallyReal_rank2`, with χ_Q the character of
F(√(-disc Q))/F defined without choosing a basis, and the same extra conjuncts. -/
theorem siegel_totallyReal_rank2' (h : n = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (1 / 2 : ℝ) * (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2V Q) (-1) fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar2V Q) (LOne (spaceChar2V Q)) ∧ 0 < LOne (spaceChar2V Q) ∧
      Multipliable fun v => intrinsicBetaV v Q L m * (1 - spaceChar2V Q v / (NFEuler.normP v : ℝ)) ^ (-1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 1** (factor 1/2 at every place). With the setting above and n = 1,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · 2 · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)/2
  · ∏_𝔭 β_𝔭(L, m)/2.
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
and the product ∏_𝔭 β_𝔭(L, m)/2 converges unconditionally. -/
theorem siegel_totallyReal_rank1 (h : n = 1) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (2 * (discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ 1 / 2) *
        ∏' v, intrinsicBetaV v Q L m / 2)) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      Multipliable fun v => intrinsicBetaV v Q L m / 2 := by
  sorry

end Siegel

/-! ## The Tamagawa number and the mass formula over totally real number fields

Setting: F a totally real number field, Q₀ a quadratic form in n ≥ 4 variables with coefficients in 𝓞 F that is
totally positive definite over F. (Ranks 1–3 are also proved in the library; see `docs/results/`.) -/

section Tamagawa

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **τ(SO(Q)) = 2.** For Q₀ as above, the Tamagawa number of SO(Q₀) is 2. Here `tauSO Q₀` is
μ_Tam(K) · ∑_α 1/|Γ_α| (a Tamagawa volume times a double-coset mass); the library proves it equals the covolume of
SO(Q₀)(F) in SO(Q₀)(𝔸) for a Haar measure normalized as Weil's Tamagawa measure (`Measure.tauSO_eq_covolume`).
Moreover the product ∏_𝔭 α_𝔭(Q₀, Q₀) in μ_Tam(K) converges unconditionally, and the double-coset space
SO(Q₀)(F)\SO(Q₀)(𝔸_f)/SO(𝓞̂_F^n) in the mass is finite, with finite stabilizers Γ_α. -/
theorem tamagawa_two_totallyReal (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef (formF Q₀)) :
    tauSO Q₀ = 2 ∧
      (Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀) ∧
      Finite (MulAction.orbitRel.Quotient ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀)))
        (soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F n)).subgroupOf (soAf (formF Q₀)))) ∧
      ∀ x : soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F n)).subgroupOf (soAf (formF Q₀)),
        Finite (MulAction.stabilizer ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀))) x) := by
  sorry

/-- **The Smith–Minkowski–Siegel mass formula.** For Q₀ as above and L = 𝓞_F^n,
∑_{L' ∈ Gen(L)} 1/|O(L')| = ( |d_F|^{-n(n-1)/4} · ∏_σ vol(SO(Q₀^σ)) · ∏_𝔭 α_𝔭(Q₀, Q₀) )^{-1},
with σ running over the embeddings F → ℂ (all real), vol(SO(Q₀^σ)) the closed-form archimedean volume
(`archVolSO` at the Gram determinant `detGram Q₀ σ`), and α_𝔭(Q₀, Q₀) = (1/2) β_𝔭(Q₀, Q₀) Siegel's local density.
Moreover the genus of L has finitely many classes, every lattice in the genus has a finite automorphism group,
and the product ∏_𝔭 α_𝔭(Q₀, Q₀) converges unconditionally. -/
theorem massFormula_totallyReal (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef (formF Q₀)) :
    (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F n), ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) =
      (|(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) *
        ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹ ∧
      (genusClasses (formF Q₀) (stdLat F n)).Finite ∧
      (∀ M : Lat F n, SameGenus (formF Q₀) (stdLat F n).1 M.1 → Finite (autLat (formF Q₀) M.1)) ∧
      Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
  sorry

end Tamagawa

/-! ## Local–global principles over number fields

Setting: F any number field. `NFPlace F` is the set of places of F (infinite places and nonzero primes of 𝓞 F);
`NFPlace.Everywhere P` means P holds over the completion F_v for every place v. Forms are `QuadForm F n`. -/

section LocalGlobal

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Hilbert reciprocity.** For a, b ∈ F^×, the local Hilbert symbol (a, b)_v is -1 at only finitely many places
v, and at an even number of them; equivalently ∏_v (a, b)_v = 1. -/
theorem hilbertReciprocity_numberField (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard := by
  sorry

/-- **Hasse–Minkowski (isotropy).** A nondegenerate quadratic form Q over F is isotropic over F if and only if it is
isotropic over every completion F_v. -/
theorem hasseMinkowski_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  sorry

/-- **Representation is local–global.** A nondegenerate quadratic form Q over F represents c ∈ F^× over F if and only
if it represents c over every completion F_v. -/
theorem represents_iff_everywhere_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) (c : F) (hc : c ≠ 0) :
    Q.RepresentsIn F c ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.RepresentsIn K c := by
  sorry

/-- **Isometry is local–global.** Two nondegenerate quadratic forms Q, R over F in the same number of variables are
isometric over F if and only if they are isometric over every completion F_v. -/
theorem isometric_iff_everywhere_numberField (Q R : QuadForm F n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn F R ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsometricIn K R := by
  sorry

/-- **Hasse–Minkowski over ℚ.** A nondegenerate quadratic form Q over ℚ, in any number of variables, is isotropic over
ℚ if and only if it is isotropic over ℝ and over ℚ_p for every prime p. -/
theorem hasseMinkowski_rat (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ RatPlace.Everywhere fun K _ _ => Q.IsotropicIn K := by
  sorry

end LocalGlobal

/-! ## The Tamagawa number of SO(V) over every number field

Setting: F any number field (real and complex places allowed). For a nondegenerate quadratic form Q₀ in n variables
with coefficients in 𝓞 F, `SOAdele Q₀` is SO(V)(𝔸) = G_∞ × SO(V)(𝔸_f) (V = F^n with Q₀), `GammaSOAdele Q₀` is SO(V)(F)
embedded diagonally, and `muTam Q₀ hQ λ` is Weil's Tamagawa measure with convergence factors λ_v:
|d_F|^{-n(n-1)/4} · 2^{n(n-1)r₂/2} · μ_∞ × μ_f, where μ_∞ is the product of the gauge-form (Leray) measures at the
archimedean places, r₂ the number of complex places, and μ_f the Haar measure on SO(V)(𝔸_f) giving the stabilizer
SO(L̂) of L = 𝓞_F^n the mass ∏'_v μ_v(SO(L_v)), μ_v = `muLocSO v Q₀ λ_v` (so μ_v(SO(L_v)) = α_v(L, L)/λ_v, Siegel's
local density divided by λ_v). `covolume Γ G μ` is Mathlib's: the μ-measure of a fundamental domain of Γ in G, and 0 if
there is none; so a nonzero value also says that a fundamental domain exists.

**No hidden default values.** μ_f is defined through the real product ∏'_v μ_v(SO(L_v)) (a `tprod`, which is 1 when the
product does not converge), and some measures carry the factor L_F(1, χ)^{-1} (`LOne`, a limit): each statement
below also states that this product converges unconditionally and, where it occurs, that L_F(1, χ) exists and is
positive. -/

section TamagawaNumberField

set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

open MeasureTheory QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

/-- **τ(SO(V)) = 2 over every number field** (Weil). For every nondegenerate quadratic form Q₀ in n ≥ 3 variables
with coefficients in 𝓞 F (any signature at the real places, isotropic or not, F with complex places allowed), the
covolume of SO(V)(F) in SO(V)(𝔸) for Weil's Tamagawa measure with convergence factors λ_v = 1 is 2.
Moreover the product ∏'_v μ_v(SO(L_v)) in the measure converges unconditionally. -/
theorem tamagawa_two_numberField (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 ∧
      Multipliable fun v => (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal := by
  sorry

/-- **τ(SO(V)) = 2 for quadratic spaces over every number field** (Weil). Let V be a vector space over F of
dimension n ≥ 3 and Q a nondegenerate quadratic form on V (Mathlib's `QuadraticForm F V`, nondegenerate polar form).
Then (V, Q) has an integral model (`IntegralModel Q`: a basis b of V, a nonzero d ∈ 𝓞 F and a form Q₀ over 𝓞 F with
Q₀ = d · Q in the coordinates of b), and for every integral model the form Q₀ is nondegenerate, the covolume of SO(V)(F)
in SO(V)(𝔸) for Weil's Tamagawa measure of Q₀ (λ_v = 1) is 2, and the product ∏'_v μ_v(SO(L_v)) converges
unconditionally. -/
theorem tamagawa_two_space {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : 3 ≤ finrank F V) (Q : QuadraticForm F V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : M.form.Nondegenerate,
      covolume (GammaSOAdele M.form) (SOAdele M.form) (muTam M.form hM fun _ => 1) = 2 ∧
      Multipliable fun v => (muLocSO v M.form 1 (soStabSO v M.form : Set (SOv v M.form))).toReal := by
  sorry

/-- **τ(SO_1) = 1.** For every nondegenerate form Q₀ = ⟨c⟩ in one variable over 𝓞 F, the covolume of
SO(V)(F) in SO(V)(𝔸) for Weil's Tamagawa measure (λ_v = 1) is 1 (both groups are trivial; the value is the product
formula for 2c). Moreover the product ∏'_v μ_v(SO(L_v)) converges unconditionally. -/
theorem tamagawa_one_rankOne (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 1 ∧
      Multipliable fun v => (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal := by
  sorry

/-- **τ(SO(V)) = 2 for anisotropic binary forms over every number field** (Weil; Ono's τ(R¹_{E/F} 𝔾_m) = 2).
Let Q₀ be a nondegenerate binary form over 𝓞 F that is anisotropic over F (any signature, complex places allowed),
and E a discriminant field of Q₀ (`IsDiscField Q₀ E`: [E : F] = 2 and E contains a square root of -det H, H the
Hessian of Q₀; such an E exists, `exists_isDiscField_of_anisotropicF`). For Weil's Tamagawa measure with the
convergence factors λ_v = L_v(1, χ_E)^{-1} = 1 - χ_E(v)/Nv and the global factor L_F(1, χ_E)^{-1} (`muTamBin`), the
covolume of SO(V)(F) in SO(V)(𝔸) is 2. Moreover L_F(1, χ_E) = lim_{s→1⁺} L_F(s, χ_E) exists and is positive, and the
product ∏'_v λ_v^{-1} μ_v(SO(L_v)) converges unconditionally (its factors are 1 for almost all v). -/
theorem tamagawa_two_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamBin Q₀ hQ E) = 2 ∧
      HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) ∧
      Multipliable fun v => (muLocSO v Q₀ (lamL (chiE F E) v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal := by
  sorry

/-- **τ(SO(V)) = 2 for anisotropic binary quadratic spaces over every number field.** Let V be a vector space
over F of dimension 2 and Q a nondegenerate anisotropic quadratic form on V. Then (V, Q) has an integral model, and
for every integral model the form Q₀ (read in 2 variables, `IntegralModel.form₂`) is nondegenerate and anisotropic
over F, and for every discriminant field E of Q₀ the conclusions of `tamagawa_two_binary` hold: the covolume for
`muTamBin` is 2, L_F(1, χ_E) exists and is positive, and the product of the local masses converges. -/
theorem tamagawa_two_space_binary {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V = 2) (Q : QuadraticForm F V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hA : Q.Anisotropic) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : (M.form₂ hV).Nondegenerate,
      AnisotropicF (M.form₂ hV) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E], IsDiscField (M.form₂ hV) E →
        covolume (GammaSOAdele (M.form₂ hV)) (SOAdele (M.form₂ hV)) (muTamBin (M.form₂ hV) hM E) = 2 ∧
        HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) ∧
        Multipliable fun v => (muLocSO v (M.form₂ hV) (lamL (chiE F E) v)
          (soStabSO v (M.form₂ hV) : Set (SOv v (M.form₂ hV)))).toReal := by
  sorry

/-- **τ(SO(V)) = 1 for isotropic binary forms over every number field** (Weil; Ono's τ(𝔾_m) = 1). Let Q₀ be a
nondegenerate binary form over 𝓞 F with an isotropic vector e ∈ F² (`IsIsoVec Q₀ e`: e ≠ 0, Q₀(e) = 0). Then
SO(V) ≅ 𝔾_m, and τ = vol(SO(V)(F)\SO(V)(𝔸)¹) = 1 for Weil's measure with the convergence factors
λ_v = 1 - N(v)^{-1} and the global factor ρ_F^{-1}, ρ_F the residue of ζ_F at 1 (`tauIso`: the covolume of SO(V)(F)
for this measure restricted to the shell 0 ≤ log |χ_e| < 1, which is the norm-one quotient measure; `muTamIso`).
Moreover the product ∏'_v λ_v^{-1} μ_v(SO(L_v)) in the measure converges unconditionally. -/
theorem tamagawa_one_binary_isotropic (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (e : Fin 2 → F)
    (he : IsIsoVec Q₀ e) :
    tauIso Q₀ hQ he = 1 ∧
      Multipliable fun v => (muLocSO v Q₀ (lamV v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal := by
  sorry

/-- **τ(SO(V)) = 1 for isotropic binary quadratic spaces over every number field.** Let V be a vector space
over F of dimension 2 and Q a nondegenerate quadratic form on V that is isotropic (not `QuadraticMap.Anisotropic`).
Then (V, Q) has an integral model, and for every integral model the form Q₀ (in 2 variables, `IntegralModel.form₂`)
is nondegenerate and isotropic over F, `tauIso` = 1 for every isotropic vector of Q₀, and the product of the local
masses converges unconditionally. -/
theorem tamagawa_one_space_binary_isotropic {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V = 2) (Q : QuadraticForm F V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hI : ¬ Q.Anisotropic) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : (M.form₂ hV).Nondegenerate,
      IsotropicF (M.form₂ hV) ∧
      (∀ (e : Fin 2 → F) (he : IsIsoVec (M.form₂ hV) e), tauIso (M.form₂ hV) hM he = 1) ∧
      Multipliable fun v => (muLocSO v (M.form₂ hV) (lamV v) (soStabSO v (M.form₂ hV) : Set (SOv v (M.form₂ hV)))).toReal := by
  sorry

end TamagawaNumberField

/-! ## Siegel's formula for indefinite forms over every number field

Setting: F any number field; Q₀ a nondegenerate quadratic form over 𝓞 F in N variables, of any signature (at a complex
place every form is indefinite); L = 𝓞_F^N; G = SO(V), G_∞ = ∏_{w | ∞} SO(V)(F_w). The sums ∑' i run over the proper
classes M_i in the genus of L (`DC Q₀`: the double cosets SO(V)(F)\SO(V)(𝔸_f)/SO(L̂)), as sums in [0, ∞] (`ENNReal`).
`unitVolume Q₀ hQ i` = v(M_i) is the covolume of the unit group SO(M_i) in G_∞ for Weil's archimedean Tamagawa measure
μ_∞ (`muArchTamSO`). For a rational point (a vector ξ ∈ F^N with Q₀(ξ) = m, `RatSphere`; or a frame Ξ ∈ F^{N×r} with
Q₀ ∘ Ξ = T₀, `RatFrame`), Siegel's measure of representations ρ(M_i, ·) (`repMeasure`, `repMeasureT`) is
∑_{x ∈ Γ_i\R(M_i, ·)} vol(Γ_{i,x}\H_x), the sum over the unit-group orbits of the representations by M_i of the
covolumes of their stabilizers, for the quotient measures on the stabilizers H_x ⊆ G_∞ given by an archimedean
fibration of μ_∞ (`archFibrationNF`, `frameArchFibrationNF`, `frameArchFibrationRank2`). The constants c_∞
(`cInfNF`, `cInfTNF`, `cInfCorankOne`) are products of |d_F|^{-N(N-1)/4} and normalized archimedean absolute values;
the local sides (`finDensityProduct`, `frameDensityProduct`, ...) are |d_F|^{-…} times products over the primes 𝔭 of
𝓞 F of the local densities β_𝔭 (`LocalDensity.NF.localDensity`, `LocalDensity.NF.localDensityForm`), regularized by
L_F(1, χ) or by ρ_F = Res_{s=1} ζ_F(s) when the stabilizer has rank 2.

**Side conditions.** Each statement also states, where the library proves it, that the real products ∏'_𝔭 on the
local side converge unconditionally (a `tprod` is 1 otherwise), that L_F(1, χ) exists and is positive, and that
0 < ∑_i v(M_i) < ∞. Facts that are not available as library lemmas are named in the docstring and not stated. In
particular the finiteness of the set of classes `DC Q₀` for indefinite Q₀ is not stated (the library proves the
finiteness of the full-orthogonal classes in a genus, `Lattices.genusClasses_finite_of_nondegenerate`, but not of
`DC Q₀`); the sums over classes are sums in [0, ∞] and need no finiteness to be meaningful. -/

section SiegelIndefinite

set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F]

open MeasureTheory QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Indefinite
  QuadFormsKB.Tamagawa.Frames QuadFormsKB.LocalDensity

/-- **Siegel's formula for indefinite forms, numbers, every number field** (Siegel 1936, measure of
representations; Weil 1965). For Q₀ nondegenerate over 𝓞 F in N = k + 1 ≥ 4 variables (any signature) and
m ∈ 𝓞 F, m ≠ 0, represented by Q₀ over F (a rational point ξ),
c_∞(m) · ∑_i ρ(M_i, m) = |d_F|^{-(N-1)/2} ∏_𝔭 β_𝔭(L, m) · ∑_i v(M_i),
with c_∞(m) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |2m|_w^{-(N-1)} (`cInfNF`) and ρ for the archimedean sphere fibration
`archFibrationNF`. Moreover ∏_𝔭 β_𝔭(L, m) converges unconditionally and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_numberField {k : ℕ} (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensity v Q₀ m) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

/-- **Siegel's formula for indefinite forms, forms by forms, every number field** (Siegel 1936; Weil 1965).
For Q₀ nondegenerate over 𝓞 F in N = r + n' variables (any signature), n' ≥ 3, and T₀ nondegenerate over 𝓞 F of rank
r ≥ 1 represented by Q₀ over F (a rational frame Ξ, Q₀ ∘ Ξ = T₀),
c_∞(T₀) · ∑_i ρ(M_i, T₀) = |d_F|^{-(N(N-1) - n'(n'-1))/4} ∏_𝔭 β_𝔭(L, T₀) · ∑_i v(M_i),
with c_∞(T₀) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |det H_{T₀}|_w^{-n'} (`cInfTNF`) and ρ for the frame fibration
`frameArchFibrationNF`. Moreover the product ∏_𝔭 β_𝔭(L, T₀) converges unconditionally and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_forms_numberField {r n' : ℕ} (hr : 1 ≤ r) (hn' : 3 ≤ n') (Q₀ : QuadForm (𝓞 F) (r + n'))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationNF Q₀ hQ T₀ hT hn' Ξ) i =
      ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

/-- **Siegel's formula, forms by forms with an anisotropic stabilizer of rank 2, every number field.** For Q₀
nondegenerate over 𝓞 F in N = r + 2 variables (any signature), T₀ nondegenerate of rank r ≥ 1 with a rational frame Ξ,
and δ = -det H_{Q₀} det H_{T₀} not a square in F (`deltaForms`; the orthogonal complement of Ξ is anisotropic),
c_∞(T₀) · ∑_i ρ(M_i, T₀) = |d_F|^{-(N(N-1)-2)/4} L_F(1, χ) ∏_𝔭 β_𝔭(L, T₀)(1 - χ(𝔭)/N𝔭) · ∑_i v(M_i),
χ = `chiForms Q₀ T₀` (χ(𝔭) = (δ/𝔭) at 𝔭 ∤ 2δ, 0 otherwise), ρ for `frameArchFibrationRank2`. Moreover
L_F(1, χ) = lim_{s→1⁺} L_F(s, χ) exists and is positive, the corrected product ∏_𝔭 β_𝔭(L, T₀)(1 - χ(𝔭)/N𝔭)
converges unconditionally, and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_forms_rank2 {r : ℕ} (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (hW : ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
    (Ξ : RatFrame Q₀ T₀) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationRank2 Q₀ hQ T₀ hT hW Ξ) i =
      ENNReal.ofReal (frameDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiForms Q₀ T₀) (LOne (chiForms Q₀ T₀)) ∧ 0 < LOne (chiForms Q₀ T₀) ∧
    (Multipliable fun v =>
      NF.localDensityForm v Q₀ T₀ * (1 - chiForms Q₀ T₀ v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ)) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

/-- **Siegel's formula for numbers by ternary forms, every number field** (the case r = 1 of
`siegel_indefinite_forms_rank2`). For Q₀ nondegenerate ternary over 𝓞 F (any signature), m ∈ 𝓞 F, m ≠ 0,
represented by Q₀ over F (a rational point ξ), and -2m det H_{Q₀} not a square in F (m^⊥ anisotropic),
c_∞(m) · ∑_i ρ(M_i, m) = |d_F|^{-1} L_F(1, χ) ∏_𝔭 β_𝔭(L, m)(1 - χ(𝔭)/N𝔭) · ∑_i v(M_i),
with χ = `chiForms Q₀ ⟨m⟩` (χ(𝔭) = (-2m det H_{Q₀}/𝔭) at the good primes), ρ the measures of the representations
of m (vectors read as 1-frames, `ratFrameEquivRatSphere`) for `frameArchFibrationRank2`. Moreover L_F(1, χ) exists
and is positive, the corrected product converges unconditionally, and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_ternary (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hW : ¬ IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := 2) (m : F) * ∑' i, repMeasureT Q₀ (DVR.unary m) hQ
        (frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
          ((ratFrameEquivRatSphere Q₀ m).symm ξ)) i =
      ENNReal.ofReal (ternaryDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiForms Q₀ (DVR.unary m)) (LOne (chiForms Q₀ (DVR.unary m))) ∧
    0 < LOne (chiForms Q₀ (DVR.unary m)) ∧
    (Multipliable fun v =>
      NF.localDensity v Q₀ m * (1 - chiForms Q₀ (DVR.unary m) v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ)) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

/-- **Siegel's formula, forms by forms with an isotropic stabilizer of rank 2 (Siegel's excluded case),
regularized, every number field.** For Q₀ nondegenerate over 𝓞 F in N = r + 2 variables (any signature), T₀
nondegenerate of rank r ≥ 1 with a rational frame Ξ, and δ = -det H_{Q₀} det H_{T₀} a square in F (the stabilizers
are split tori),
2 c_∞(T₀) · ∑_i ρ¹(M_i, T₀) = |d_F|^{-(N(N-1)-2)/4} ρ_F ∏_𝔭 β_𝔭(L, T₀)(1 - N𝔭^{-1}) · ∑_i v(M_i),
ρ_F = Res_{s=1} ζ_F(s), with ρ¹ the measures of representations for the norm-one stabilizers (`repMeasureIso`).
Moreover the corrected product converges unconditionally and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_forms_rank2_isotropic {r : ℕ} (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 2))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀) :
    2 * (cInfTNF Q₀ T₀ * ∑' i, repMeasureIso Q₀ hQ T₀ hT hiso Ξ i) =
      ENNReal.ofReal (isoDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ * lamV v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

/-- **Siegel's formula for numbers by ternary forms with m^⊥ isotropic (Siegel's excluded case), regularized,
every number field** (the case r = 1 of `siegel_indefinite_forms_rank2_isotropic`). For Q₀ nondegenerate ternary over
𝓞 F (any signature), m ∈ 𝓞 F, m ≠ 0, represented by Q₀ over F (a rational point ξ), and -2m det H_{Q₀} a square in F,
2 c_∞(m) · ∑_i ρ¹(M_i, m) = |d_F|^{-1} ρ_F ∏_𝔭 β_𝔭(L, m)(1 - N𝔭^{-1}) · ∑_i v(M_i).
Moreover the corrected product converges unconditionally and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_ternary_isotropic (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    2 * (cInfNF (k := 2) (m : F) * ∑' i, repMeasureIso Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
        (isSquare_deltaForms_unary hiso) ((ratFrameEquivRatSphere Q₀ m).symm ξ) i) =
      ENNReal.ofReal (ternaryIsoDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensity v Q₀ m * lamV v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

/-- **Siegel's formula, forms of corank one, every number field** (Siegel 1935, Hauptsatz for n = m + 1,
ε = 1/2). For Q₀ nondegenerate over 𝓞 F in N = r + 1 variables (any signature), r ≥ 2, and T₀ nondegenerate of rank r
with a rational frame Ξ,
c⁽¹⁾_∞(Q₀) · ∑_i n(M_i, T₀) = (1/2) |d_F|^{-(N(N-1))/4} ∏_𝔭 β_𝔭(L, T₀) · ∑_i v(M_i),
n(M_i, T₀) = `repCount` the number of representations of T₀ by M_i modulo the unit group (a cardinal in [0, ∞]),
c⁽¹⁾_∞(Q₀) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |det H_{Q₀}|_w^{-1} (`cInfCorankOne`). Moreover the product
∏_𝔭 β_𝔭(L, T₀) converges unconditionally and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_forms_corank1 {r : ℕ} (hr : 2 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, Indefinite.repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

/-- **Siegel's formula for the numbers represented by an anisotropic binary form, every number field**
(Siegel 1935, Hauptsatz for n = 2, m = 1, ε = 1/2; Dirichlet over ℚ). For Q₀ a nondegenerate binary form over 𝓞 F (any
signature) that is anisotropic over F, E a discriminant field of Q₀ (`IsDiscField`; one exists,
`exists_isDiscField_of_anisotropicF`), and T₀ = ⟨m⟩ nondegenerate of rank one with a rational frame Ξ (Q₀(Ξ) = m),
c⁽¹⁾_∞(Q₀) · ∑_i n(M_i, m) = (1/2) |d_F|^{-1/2} L_F(1, χ_E)^{-1} ∏_𝔭 L_𝔭(1, χ_E) β_𝔭(L, m) · ∑_i v(M_i),
n(M_i, m) = `repCount` (the representations modulo the unit group SO(M_i); finite for definite Q₀, infinite unit group
for indefinite Q₀). Moreover L_F(1, χ_E) exists and is positive, and the product ∏_𝔭 L_𝔭(1, χ_E) β_𝔭(L, m)
converges unconditionally, and 0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, Indefinite.repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ / lamL (chiE F E) v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

open Classical in
/-- **Siegel's formula for forms of the same rank (corank zero), every number field** (Siegel 1935, Hauptsatz
for n = m, ε = 1/2 at every place). For Q₀ nondegenerate over 𝓞 F in N ≥ 3 variables (any signature) and T₀
nondegenerate in N variables with a rational frame Ξ (Q₀ ∘ Ξ = T₀, Ξ ∈ GL_N(F)),
∑_i n(M_i, T₀) = ∏_{w | ∞} |det Ξ|_w^{-1} ∏_𝔭 β_𝔭(L, T₀)/2 · ∑_i v(M_i)
(normalized absolute values; n = `repCount`). Moreover the product ∏_𝔭 β_𝔭(L, T₀)/2 converges unconditionally and
0 < ∑_i v(M_i) < ∞. -/
theorem siegel_indefinite_forms_corank0 {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    ∑' i, Indefinite.repCount Q₀ T₀ i =
      ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) *
        ∏' v, NF.localDensityForm v Q₀ T₀ / 2) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ / 2) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  sorry

end SiegelIndefinite

/-! ## Representations of forms by forms over totally real number fields

Setting: F a totally real number field, Q₀ a quadratic form over 𝓞 F in N variables and T₀ one in r variables,
1 ≤ r ≤ N, both totally positive definite over F, L = 𝓞_F^N. r_M(T) is the number of frames X ∈ M^r (columns in M) with
Q ∘ X = T (`LatClass.repCountT`, a `Nat.card`). The case stated here is N ≥ 3 and N - r ≠ 2 (the product of the local
densities converges absolutely); the library also proves the other cases (`Frames.siegelForms_all_ranks`: N - r = 2
regularized by L_F(1, χ), N = 2, N = 1). -/

section SiegelForms

set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open QuadFormsKB.Tamagawa.Frames QuadFormsKB.LocalDensity

/-- **Siegel's formula for representations of forms by forms** (Siegel 1935, Hauptsatz; over F: Siegel
1937). With the setting above,
∑_{L' ∈ Gen(L)} r_{L'}(T₀)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · S(Q₀, T₀),
S(Q₀, T₀) = ε' |d_F|^{-r(2N-r-1)/4} ∏_σ ε β_σ(Q₀, T₀) ∏_𝔭 α_𝔭(Q₀, T₀) (`siegelProductT`; ε = 1/2 at every place if
r = N, ε' = 1/2 if r = N - 1). Moreover the product ∏_𝔭 α_𝔭(Q₀, T₀) converges unconditionally, the genus of L has
finitely many classes, and every lattice M in the genus has a finite automorphism group O(M) and finitely many frames
X ∈ M^r with Q₀ ∘ X = T₀. -/
theorem siegelForms_totallyReal {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) (hN : 3 ≤ N) (h2 : N ≠ r + 2)
    (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hpd : IsTotallyPosDef (formF Q₀))
    (hpdT : IsTotallyPosDef (formF T₀)) :
    (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F N),
        (LatClass.repCountT (formF Q₀) c (formF T₀) : ℝ) / LatClass.autCard (formF Q₀) c) =
      (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F N), ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) *
        siegelProductT Q₀ T₀ ∧
      (Multipliable fun v => NF.siegelDensity v Q₀ T₀) ∧
      (genusClasses (formF Q₀) (stdLat F N)).Finite ∧
      ∀ M : Lat F N, SameGenus (formF Q₀) (stdLat F N).1 M.1 →
        Finite (autLat (formF Q₀) M.1) ∧
        Finite {X : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => X i j) ∈ M.1) ∧ (formF Q₀).compMat X = formF T₀} := by
  sorry

end SiegelForms

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

end Classical


/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`). Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.
* `QuadForm.evalIn`, `QuadForm.eval` (Defs/QuadForm.lean): the value Q(x) for x ∈ K^n, K an R-algebra (resp. K = R).
* `QuadForm.hessian` (Defs/QuadForm.lean): the Hessian matrix H = C + Cᵀ, so Q(x) = (1/2) xᵀ H x.
* `QuadForm.Nondegenerate` (Defs/QuadForm.lean): det H ≠ 0.
* `QuadForm.IsotropicIn K` (Defs/QuadForm.lean): Q(x) = 0 for some nonzero x ∈ K^n.
* `QuadForm.RepresentsIn K c` (Defs/QuadForm.lean): Q(x) = c for some x ∈ K^n.
* `QuadForm.IsometricIn K Q R` (Defs/QuadForm.lean): Q(P x) = R(x) for all x, for some P ∈ GL_n(K).
* `RatPlace.Everywhere`, `RatPlace.atPlace` (Defs/Rational.lean): the property holds over ℝ and every ℚ_p.
* `NFPlace`, `NFPlace.atPlace`, `NFPlace.Everywhere` (Defs/NumberField.lean): places of F (infinite places,
  nonzero primes of 𝓞 F); the property holds over every completion (`w.Completion`, `v.adicCompletion F`).
* `NFPlace.hilbert` (Defs/NumberField.lean): (a, b)_v, the Hilbert symbol over the completion F_v.
* `hilbertSymbol K a b` (Defs/Hilbert.lean): 1 if z² = a x² + b y² has a nonzero solution in K, else -1.

Siegel's theorem
* `HilbertModular.realEmb F v` (HilbertModular/Congruence.lean): the real embedding F → ℝ of the place v.
* `Lattices.IsIntegralLattice Q L` (Lattices/Basic.lean): Q(x) ∈ 𝓞 F for all x ∈ L, where F is the number field of Q
  (an implicit argument, read off the type of Q) and 𝓞 F is Mathlib's ring of integers of F
  (`NumberField.RingOfIntegers F`).
* `SiegelSpace.IsTotallyPosDefV Q` (Tamagawa/SiegelQuadSpace.lean): Q(x) is totally positive (positive under every
  real embedding of F, the number field of Q, read off its type) for every x ≠ 0.
* `SiegelSpace.LatClassV Q` (Tamagawa/SiegelGenusV.lean): the classes of lattices of (V, Q), i.e. 𝓞 F-lattices in V
  up to isometry by the full O(V, Q) (improper isometries included).
* `SiegelSpace.genusClassesV Q L` (Tamagawa/SiegelGenusV.lean): the set of classes of the lattices M with
  `SameGenusV Q L M`, i.e. the classes L' in Gen(L); `SiegelSpace.SameGenusV Q L M` (same file): M is in the genus
  of L (locally isometric to L at every prime of 𝓞 F).
* `SiegelSpace.LatClassV.repCount Q c t` (Tamagawa/SiegelGenusV.lean): r_M(t) = #{x ∈ M : Q(x) = t} for any lattice
  M in the class c (a `Nat.card`; independent of the representative).
* `SiegelSpace.LatClassV.autCard Q c` (Tamagawa/SiegelGenusV.lean): |O(M)| = `Nat.card (autLatV Q M)` for any
  lattice M in the class c, improper isometries included (independent of the representative).
* `Lattices.autLatV Q M` (Lattices/Basic.lean): O(M), the isometries of (V, Q) mapping M onto M.
* `SiegelSpace.discNormV Q L` (Tamagawa/SiegelClassical.lean): N𝔡(L), the absolute norm of the discriminant ideal of
  L (an ideal of 𝓞 F).
* `SiegelSpace.intrinsicBetaV v Q L m` (Tamagawa/SiegelClassical.lean): for v = 𝔭 a nonzero prime of 𝓞 F
  (`HeightOneSpectrum (𝓞 F)`; the product ∏' v runs over these), β_𝔭(L, m) =
  lim_k #{x ∈ L_𝔭/𝔭^k L_𝔭 : Q(x) ≡ m mod 𝔭^k} / N𝔭^{k(n-1)}, via `SiegelSpace.intrinsicBeta` (same file)
  in the coordinates of `Module.finBasis`.
* `Tamagawa.archRepDensity n a d` (Tamagawa/MassInduction.lean): π^{n/2}/Γ(n/2) · a^{(n-2)/2} · d^{-1/2}.
* `RegProd.regProd χ e f` (Siegel/RegProd.lean): L_F(1, χ)^e · ∏'_𝔭 f(𝔭)(1 - χ(𝔭)/N𝔭)^e, with `RegProd.LOne`
  = lim_{s→1+} L_F(s, χ) and `RegProd.HasLOne χ c` (same file): L_F(s, χ) → c as s → 1⁺;
  `NFEuler.normP 𝔭` (Analysis/NFEulerProduct.lean): N𝔭, the absolute norm of 𝔭.
* `SiegelSpace.spaceChar3`, `SiegelSpace.spaceChar2` (Tamagawa/SiegelSpace.lean): χ(𝔭) = `sqChar` of
  -2m·det H, resp. -det H; `SiegelSpace.sqChar` (same file): the quadratic symbol at 𝔭 (0 at 𝔭 | 2 and at non-units).
* `SiegelSpace.spaceChar3V`, `SiegelSpace.spaceChar2V` (Tamagawa/SiegelSpaceChars.lean): the same with the
  basis-free `sqClassChar` and `hessDetV`.
* `Lattices.coordForm Q e` (Lattices/Basic.lean): the form Q in the basis e (a `Basis (Fin k) F V`), as a `QuadForm F k`
  (F the field of Q; k = 3 or 2 in the statements, from `finBasisOfFinrankEq F V h`).

Tamagawa number and mass formula
* `HilbertModular.formF Q₀` (HilbertModular/GenusTheta.lean): Q₀ with coefficients mapped into F.
* `Lattices.IsTotallyPosDef`, `Lattices.IsTotallyPos` (Lattices/Finite.lean): Q(x) totally positive for x ≠ 0.
* `Tamagawa.tauSO` (Tamagawa/MassFormula.lean): `tamagawaK Q₀ · dcMass (…)`; equal to the Tamagawa covolume by
  `Tamagawa.Measure.tauSO_eq_covolume` (Tamagawa/Measure/AdelicSO.lean).
* `Tamagawa.tamagawaK`, `Tamagawa.archVolSO`, `Tamagawa.detGram` (Tamagawa/MassFormula.lean): the Tamagawa volume of
  the stabilizer, the archimedean volume of SO(Q₀^σ), and |σ(det(H/2))|.
* `Lattices.genusClasses Q L` (Lattices/Finite.lean): the classes L' in the genus of L (lattices in F^n up to isometry
  by the full O(Q), improper isometries included); `Lattices.LatClass.autCard Q c` (same file): |O(M)| =
  `Nat.card (autLat Q M)` for any lattice M in the class c. The mass ∑ 1/|O(L')| is written out in the statement
  (it is `Lattices.mass Q L`, same file).
* `Lattices.SameGenus Q L M`, `Lattices.autLat Q M` (Lattices/Genus.lean): M is in the genus of L; O(M).
* `Lattices.OAf`, `Lattices.ratPoints`, `Lattices.locStab` (Lattices/ClassSet.lean): O(V)(𝔸_f), the diagonal
  O(V)(F) inside it, and the stabilizer O(L̂) of L; `Tamagawa.soAf` (Tamagawa/MassFormula.lean): SO(V)(𝔸_f).
* `Tamagawa.stdLat F n` (Tamagawa/MassFormula.lean): the lattice 𝓞_F^n in F^n.
* `LocalDensity.NF.siegelDensity v Q T` (LocalDensity/NFFormDensity.lean): α_𝔭(Q, T) = ε β_𝔭(Q, T), ε = 1/2 if
  T has the same rank as Q, with β_𝔭 = `localDensityForm` (same file).

Tamagawa numbers over every number field (namespace `Tamagawa.Measure.Weil` unless stated; paths in
`Tamagawa/Measure/`)
* `SOAdele Q₀`, `GInfSO Q₀`, `GammaSOAdele Q₀`, `muTam Q₀ hQ λ`, `muArchTamSO`, `cxWeil`, `TamagawaNumberTwoAdelic`
  (Weil/MuTamSO.lean): SO(V)(𝔸) = G_∞ × SO(V)(𝔸_f), the diagonal SO(V)(F), Weil's Tamagawa measure with convergence
  factors λ, its archimedean factor |d_F|^{-n(n-1)/4} 2^{n(n-1)r₂/2} μ_∞ (μ_∞ the product of the gauge-form (Leray)
  measures at the real and complex places, `muArchNF`, LerayArch.lean, LerayComplex.lean).
* `Tamagawa.Measure.muFin Q₀ λ`, `finFactor`, `KSO`, `SOAf` (AdelicSO.lean): the Haar measure on SO(V)(𝔸_f) with
  μ_f(SO(L̂)) = ∏'_v μ_v(SO(L_v)) (`finFactor`), SO(L̂), SO(V)(𝔸_f); `Tamagawa.Measure.muLocSO v Q₀ λ`, `soStabSO`,
  `SOv` (LocalSO.lean): the Haar measure on SO(V)(F_v) with μ_v(SO(L_v)) = α_v(L, L)/λ_v (`muLocSO_soStabSO`).
* `IntegralModel Q` (Weil/SpaceHeadlines.lean): a basis b of V, d ∈ 𝓞 F nonzero and Q₀ over 𝓞 F with Q₀ = d·Q in the
  coordinates of b (fields `basis`, `scale`, `scale_ne_zero`, `form`, `eq`); `IntegralModel.form₂` (Weil/SpaceBinary.lean):
  Q₀ read in 2 variables when dim V = 2.
* `AnisotropicF Q₀` (Weil/TauTwoAnisotropic.lean): Q₀(ξ) = 0 only for ξ = 0 in F^n; `IsotropicF Q₀`, `IsIsoVec Q₀ e`
  (Weil/BinaryIsotropic.lean): Q₀ has an isotropic vector; e ≠ 0 with Q₀(e) = 0.
* `IsDiscField Q₀ E`, `chiE F E`, `lamL χ`, `muTamChi`, `muTamBin Q₀ hQ E` (Weil/BinaryMeasure.lean): [E : F] = 2 and E
  contains a square root of -det H outside F; χ_E(v) = 1, -1, 0 as v splits, is inert, ramifies in E; λ_v = 1 - χ(v)/Nv;
  L_F(1, χ)^{-1} · `muTam Q₀ hQ (lamL χ)`; the case χ = χ_E.
* `tauIso Q₀ hQ he`, `muTamIso`, `isoShell`, `isoChar`, `lamV` (Weil/BinaryIsotropic.lean, Weil/Ideles.lean): the
  covolume of SO(V)(F) for ρ_F^{-1} `muTam Q₀ hQ lamV` restricted to {0 ≤ log ‖χ_e(g)‖ < 1}, χ_e : SO(V) ≅ 𝔾_m the
  character of the isotropic line of e, λ_v = 1 - N(v)^{-1}; ρ_F = Mathlib's `dedekindZeta_residue F`.
* `RegProd.LOne`, `RegProd.HasLOne` (Siegel/RegProd.lean, as above).

Siegel's formula for indefinite forms (namespace `Tamagawa.Indefinite` unless stated; paths in `Tamagawa/Indefinite/`)
* `DC Q₀` (ClassicalSetup.lean): SO(V)(F)\SO(V)(𝔸_f)/SO(L̂), the proper classes in the genus of L = 𝓞_F^N.
* `unitGroup Q₀ i`, `unitVolume Q₀ hQ i`, `reps`, `repMeasure Q₀ hQ m 𝔉 i` (ClassicalMeasures.lean) and
  `repMeasureOf` (ThetaUnfold.lean): Γ_i = SO(M_i) in G_∞; v(M_i) = covolume of Γ_i in G_∞ for `muArchTamSO`; the
  representations of m by M_i; ρ(M_i, m) = ∑ over Γ_i-orbits of x of the covolume of the stabilizer Γ_{i,x} in H_x for
  the stabilizer measure of the archimedean fibration 𝔉 (`ArchFibration`, ThetaUnfold.lean).
* `repMeasureT`, `RatFrame Q₀ T₀` (FrameClassical.lean): the same for representations of forms (frames X with
  Q₀ ∘ X = T₀); rational frames. `Measure.Weil.RatSphere Q₀ ρ` (Measure/Weil/SphereOrbitsNF.lean): {η ∈ F^N : Q₀(η) = ρ}.
* `repMeasureIso`, `isoStabMeasure` (IsoMeasures.lean): ρ¹, the same with the stabilizer measures restricted to the
  shells {0 ≤ log |χ_X|_∞ < 1} (the norm-one volumes).
* `Indefinite.repCount Q₀ T₀ i` (CorankOneCount.lean): #(Γ_i\R(M_i, T₀)) in [0, ∞], R(M_i, T₀) = `repsT`.
* `archFibrationNF`, `cInfNF` (SiegelComplex.lean): the archimedean sphere fibration (constructed from
  `realArchFibration`, `complexArchFibrationW`) and c_∞(m) = |d_F|^{-N(N-1)/4} ∏_w |2m|_w^{-(N-1)}.
* `frameArchFibrationNF`, `cInfTNF` (FormsIndefiniteNF.lean); `frameArchFibrationRank2`, `frameDensityProductReg`
  (FormsIndefiniteRank2.lean); `isoDensityProductReg` (FormsIndefiniteIso.lean); `cInfCorankOne`, `binDensityProduct`
  (SiegelCorankOne.lean): the frame fibrations, c_∞(T₀) = |d_F|^{-N(N-1)/4} ∏_w |det H_{T₀}|_w^{-n'},
  c⁽¹⁾_∞(Q₀) = |d_F|^{-N(N-1)/4} ∏_w |det H_{Q₀}|_w^{-1}, and the regularized local sides displayed in the docstrings.
* `finDensityProduct` (SiegelIndefinite.lean), `frameDensityProduct` (FormsIndefinite.lean),
  `ternaryDensityProductReg`, `not_isSquare_deltaForms_unary` (SiegelTernary.lean), `ternaryIsoDensityProductReg`,
  `isSquare_deltaForms_unary` (SiegelTernaryIso.lean), `ratFrameEquivRatSphere`, `unary_nondegenerate`
  (FormsIndefiniteChecks.lean): the local sides; vectors as 1-frames.
* `Frames.deltaForms`, `Frames.chiForms` (Tamagawa/FrameSiegelReg.lean): δ = -det H_{Q₀} det H_{T₀} and its quadratic
  character (0 at 𝔭 | 2δ). `LocalDensity.NF.localDensity v Q m`, `LocalDensity.NF.localDensityForm v Q T`
  (LocalDensity/NFFormDensity.lean): β_𝔭(L, m), β_𝔭(L, T). `LocalDensity.DVR.unary m` (LocalDensity/FormDensity.lean):
  the form ⟨m⟩ in one variable. `Measure.Weil.σR`, `Measure.Weil.σC` (Measure/Weil/AdelicSphere.lean): the real and
  complex embeddings of F indexed by the infinite places.

Forms by forms (namespace `Tamagawa.Frames`; paths in `Tamagawa/`)
* `LatClass.repCountT Q c T`, `repCountT` (FrameRepMass.lean): r_M(T) = #{X ∈ M^r : Q ∘ X = T} for M in the class c.
* `siegelProductT Q₀ T₀`, `epsNR`, `epsCodimOne`, `archDensityForm` (FrameSiegel.lean): Siegel's product S(Q₀, T₀).

Classical cases over ℚ
* `Siegel.sumSq k`, `Siegel.repNum`, `Siegel.repSet` (Siegel/FourSquares.lean, Siegel/Genus.lean): x₀² + … + x_{k-1}²;
  #{x ∈ ℤ^n : Q(x) = m} (`Nat.card`) and the set itself.
* `Tamagawa.Classical.sumTwoSqZ`, `pell2Z`, `gaussDisc` (Tamagawa/Classical/Basic.lean): x₀² + x₁², x₀² - 2x₁², the
  discriminant of ℚ(√-m). `Binary.QField D`, `Binary.IsQuadDisc D` (Binary/QuadraticField.lean): the quadratic field
  of discriminant D. `Tamagawa.RatBridge.up Q` (Tamagawa/RatBridge.lean): Q over 𝓞_ℚ.
-/

end QuadFormsKB.Headlines
