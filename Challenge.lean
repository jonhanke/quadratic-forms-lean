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
import QuadFormsKB.LocalDensity.NFFormDensity
import QuadFormsKB.Siegel.RegProd
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Tamagawa.MassInduction
import QuadFormsKB.Tamagawa.SiegelClassical
import QuadFormsKB.Tamagawa.SiegelGenusV
import QuadFormsKB.Tamagawa.SiegelQuadSpace
import QuadFormsKB.Tamagawa.SiegelSpace
import QuadFormsKB.Tamagawa.SiegelSpaceChars

/-!
# Headline statements

This file is the one place to read to check **what the library claims**. It states the headline results; every
proof here is a deliberate `sorry`, one per advertised theorem. The proofs are in `Solution.lean`, which declares the
same theorems and proves each by a one-line appeal to the library theorem. `lake comparator` (configured by
`comparator.json`) checks that each theorem of `Solution.lean` has exactly the statement given here and depends only
on the axioms `propext`, `Classical.choice` and `Quot.sound`. To trust a headline one needs to read only

* this file,
* the definitions it names, listed with file pointers in the section "Definitions used" at the end, and
* Mathlib.

This file imports only the library modules that define the notions in the statements (they also contain proofs,
which the statements do not depend on).

**Conventions.** Q denotes a quadratic form (`QuadForm R n`: the polynomial ∑_{i ≤ j} c_ij x_i x_j) or a quadratic
form on an abstract vector space (Mathlib's `QuadraticForm F V`). Classes of lattices are isometry classes under the
full orthogonal group O(Q) (improper isometries included), and every lattice L' in a genus is weighted by 1/|O(L')|.
F is a number field with ring of integers 𝓞 F; "totally positive" means positive under every real embedding.

**Caution on products.** `∏'` is Mathlib's unconditional infinite product, which returns `1` when the product does
not converge unconditionally; `regProd` (ranks 2 and 3) uses a limit `L_F(1, χ)` that takes a junk value if the
limit does not exist. The library proves separately that the products and limits occurring here converge.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## Siegel's theorem over totally real number fields

Setting: F a totally real number field, (V, Q) a totally positive definite quadratic space over F of dimension n,
L an 𝓞 F-lattice in V (of any Steinitz class, so not necessarily free) on which Q is integral, and m ∈ 𝓞 F totally
positive. In each formula the left side is

  ∑ over classes L' in Gen(L) of r_{L'}(m)/|O(L')|   (`repMassGenV Q L m`),

and `massGenV Q L` = ∑ over classes L' in Gen(L) of 1/|O(L')|. On the right, d_F is the discriminant of F,
N𝔡(L) the norm of the discriminant ideal of L, β_σ(m) = π^{n/2}/Γ(n/2) · σ(m)^{(n-2)/2} the real density at the
embedding σ, and β_𝔭(L, m) the classical local density of L at the prime 𝔭 (all named in "Definitions used"). -/

section Siegel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {V : Type*} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
  {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **Siegel's theorem, rank n ≥ 4.** With the setting above,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-(n-1)/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · ∏_𝔭 β_𝔭(L, m). -/
theorem siegel_totallyReal (hn : 4 ≤ finrank F V) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (|(discr F : ℝ)| ^ (-((finrank F V : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (finrank F V) ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        ∏' v, intrinsicBetaV v Q L m) := by
  sorry

/-- **Siegel's theorem, rank 3** (Euler product regularized by L(1, χ_m)). With the setting above and n = 3,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1} · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)
  · L_F(1, χ_m) · ∏_𝔭 β_𝔭(L, m) (1 - χ_m(𝔭)/N𝔭),
where χ_m is the quadratic character of F(√(-2m·det H))/F, H the Hessian of Q in a basis of V (this version
uses the basis `finBasisOfFinrankEq`; see the next theorem for a basis-free character). -/
theorem siegel_totallyReal_rank3 (h : finrank F V = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m) 1 fun v => intrinsicBetaV v Q L m) := by
  sorry

/-- **Siegel's theorem, rank 3, basis-free character.** As `siegel_totallyReal_rank3`, with χ_m the character of
F(√(-2m·disc Q))/F defined without choosing a basis. -/
theorem siegel_totallyReal_rank3' (h : finrank F V = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3V Q m) 1 fun v => intrinsicBetaV v Q L m) := by
  sorry

/-- **Siegel's theorem, rank 2** (factor 1/2; Euler product regularized by L(1, χ_Q)^{-1}). With the setting above
and n = 2,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (1/2) · (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · L_F(1, χ_Q)^{-1} · ∏_𝔭 β_𝔭(L, m) (1 - χ_Q(𝔭)/N𝔭)^{-1},
where χ_Q is the quadratic character of F(√(-det H))/F, H the Hessian of Q in the basis `finBasisOfFinrankEq`. -/
theorem siegel_totallyReal_rank2 (h : finrank F V = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV Q L *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h))) (-1) fun v => intrinsicBetaV v Q L m) := by
  sorry

/-- **Siegel's theorem, rank 2, basis-free character.** As `siegel_totallyReal_rank2`, with χ_Q the character of
F(√(-disc Q))/F defined without choosing a basis. -/
theorem siegel_totallyReal_rank2' (h : finrank F V = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV Q L *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2V Q) (-1) fun v => intrinsicBetaV v Q L m) := by
  sorry

/-- **Siegel's theorem, rank 1** (factor 1/2 at every place). With the setting above and n = 1,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · 2 · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)/2
  · ∏_𝔭 β_𝔭(L, m)/2. -/
theorem siegel_totallyReal_rank1 (h : finrank F V = 1) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (2 * (discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ 1 / 2) *
        ∏' v, intrinsicBetaV v Q L m / 2)) := by
  sorry

end Siegel

/-! ## The Tamagawa number and the mass formula over totally real number fields

Setting: F a totally real number field, Q₀ a quadratic form in n ≥ 4 variables with coefficients in 𝓞 F that is
totally positive definite over F. (Ranks 1–3 are also proved in the library; see `docs/results/`.) -/

section Tamagawa

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **τ(SO(Q)) = 2.** For Q₀ as above, the Tamagawa number of SO(Q₀) is 2. Here `tauSO Q₀` is
μ_Tam(K) · ∑_α 1/|Γ_α| (a Tamagawa volume times a double-coset mass); the library proves it equals the covolume of
SO(Q₀)(F) in SO(Q₀)(𝔸) for a Haar measure normalized as Weil's Tamagawa measure (`Measure.tauSO_eq_covolume`). -/
theorem tamagawa_two_totallyReal (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef (formF Q₀)) :
    tauSO Q₀ = 2 := by
  sorry

/-- **The Smith–Minkowski–Siegel mass formula.** For Q₀ as above and L = 𝓞_F^n,
∑_{L' ∈ Gen(L)} 1/|O(L')| = ( |d_F|^{-n(n-1)/4} · ∏_σ vol(SO(Q₀^σ)) · ∏_𝔭 α_𝔭(Q₀, Q₀) )^{-1},
with σ running over the embeddings F → ℂ (all real), vol(SO(Q₀^σ)) the closed-form archimedean volume
(`archVolSO` at the Gram determinant `detGram Q₀ σ`), and α_𝔭(Q₀, Q₀) = (1/2) β_𝔭(Q₀, Q₀) Siegel's local density. -/
theorem massFormula_totallyReal (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef (formF Q₀)) :
    mass (formF Q₀) (stdLat F n) =
      (|(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) *
        ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹ := by
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
* `Lattices.IsIntegralLattice Q L` (Lattices/Basic.lean): Q(x) ∈ 𝓞 F for all x ∈ L.
* `SiegelSpace.IsTotallyPosDefV Q` (Tamagawa/SiegelQuadSpace.lean): Q(x) totally positive for every x ≠ 0.
* `SiegelSpace.massGenV`, `SiegelSpace.repMassGenV` (Tamagawa/SiegelGenusV.lean): ∑ 1/|O(L')| and
  ∑ r_{L'}(t)/|O(L')| over the classes L' in Gen(L); built from `genusClassesV`, `LatClassV.autCard`,
  `LatClassV.repCount` (same file).
* `SiegelSpace.discNormV Q L` (Tamagawa/SiegelClassical.lean): N𝔡(L), the norm of the discriminant ideal of L.
* `SiegelSpace.intrinsicBetaV v Q L m` (Tamagawa/SiegelClassical.lean): β_𝔭(L, m) =
  lim_k #{x ∈ L_𝔭/𝔭^k L_𝔭 : Q(x) ≡ m mod 𝔭^k} / N𝔭^{k(n-1)}, via `SiegelSpace.intrinsicBeta` (same file)
  in the coordinates of `Module.finBasis`.
* `Tamagawa.archRepDensity n a d` (Tamagawa/MassInduction.lean): π^{n/2}/Γ(n/2) · a^{(n-2)/2} · d^{-1/2}.
* `RegProd.regProd χ e f` (Siegel/RegProd.lean): L_F(1, χ)^e · ∏'_𝔭 f(𝔭)(1 - χ(𝔭)/N𝔭)^e, with `RegProd.LOne`
  = lim_{s→1+} L_F(s, χ).
* `SiegelSpace.spaceChar3`, `SiegelSpace.spaceChar2` (Tamagawa/SiegelSpace.lean): χ(𝔭) = `sqChar` of
  -2m·det H, resp. -det H; `SiegelSpace.sqChar` (same file): the quadratic symbol at 𝔭 (0 at 𝔭 | 2 and at non-units).
* `SiegelSpace.spaceChar3V`, `SiegelSpace.spaceChar2V` (Tamagawa/SiegelSpaceChars.lean): the same with the
  basis-free `sqClassChar` and `hessDetV`.
* `Lattices.coordForm Q e` (Lattices/Basic.lean): the form Q in the basis e, as a `QuadForm F n`.

Tamagawa number and mass formula
* `HilbertModular.formF Q₀` (HilbertModular/GenusTheta.lean): Q₀ with coefficients mapped into F.
* `Lattices.IsTotallyPosDef`, `Lattices.IsTotallyPos` (Lattices/Finite.lean): Q(x) totally positive for x ≠ 0.
* `Tamagawa.tauSO` (Tamagawa/MassFormula.lean): `tamagawaK Q₀ · dcMass (…)`; equal to the Tamagawa covolume by
  `Tamagawa.Measure.tauSO_eq_covolume` (Tamagawa/Measure/AdelicSO.lean).
* `Tamagawa.tamagawaK`, `Tamagawa.archVolSO`, `Tamagawa.detGram` (Tamagawa/MassFormula.lean): the Tamagawa volume of
  the stabilizer, the archimedean volume of SO(Q₀^σ), and |σ(det(H/2))|.
* `Lattices.mass Q L` (Lattices/Finite.lean): ∑ over `genusClasses Q L` of 1/`LatClass.autCard`.
* `Tamagawa.stdLat F n` (Tamagawa/MassFormula.lean): the lattice 𝓞_F^n in F^n.
* `LocalDensity.NF.siegelDensity v Q T` (LocalDensity/NFFormDensity.lean): α_𝔭(Q, T) = ε β_𝔭(Q, T), ε = 1/2 if
  T has the same rank as Q, with β_𝔭 = `localDensityForm` (same file).
-/

end QuadFormsKB.Headlines
