/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB

/-!
# Headline statements, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by a one-line appeal to the
library theorem. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly
the statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## Siegel's theorem over totally real number fields

Setting: F a totally real number field, (V, Q) a totally positive definite quadratic space over F of dimension N,
L an 𝓞 F-lattice in V (of any Steinitz class, so not necessarily free) on which Q is integral, and m ∈ 𝓞 F totally
positive. In each formula the left side is

  ∑ over classes L' in Gen(L) of r_{L'}(m)/|O(L')|   (`repMassGenV Q L m`),

and `massGenV Q L` = ∑ over classes L' in Gen(L) of 1/|O(L')|. On the right, d_F is the discriminant of F,
N𝔡(L) the norm of the discriminant ideal of L, β_σ(m) = π^{N/2}/Γ(N/2) · σ(m)^{(N-2)/2} the real density at the
embedding σ, and β_𝔭(L, m) the classical local density of L at the prime 𝔭 (all named in "Definitions used"). -/

section Siegel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {V : Type*} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
  {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **Siegel's theorem, rank N ≥ 4.** With the setting above,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-(N-1)/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · ∏_𝔭 β_𝔭(L, m). -/
theorem siegel_totallyReal (hN : 4 ≤ finrank F V) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (|(discr F : ℝ)| ^ (-((finrank F V : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (finrank F V) ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        ∏' v, intrinsicBetaV v Q L m) :=
  siegelFormula_quadraticSpace_classical hN hQ hL hm

/-- **Siegel's theorem, rank 3** (Euler product regularized by L(1, χ_m)). With the setting above and N = 3,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1} · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)
  · L_F(1, χ_m) · ∏_𝔭 β_𝔭(L, m) (1 - χ_m(𝔭)/N𝔭),
where χ_m is the quadratic character of F(√(-2m·det H))/F, H the Hessian of Q in a basis of V (this version
uses the basis `finBasisOfFinrankEq`; see the next theorem for a basis-free character). -/
theorem siegel_totallyReal_rank3 (h : finrank F V = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m) 1 fun v => intrinsicBetaV v Q L m) :=
  siegelFormula3_quadraticSpace_classical h hQ hL hm

/-- **Siegel's theorem, rank 3, basis-free character.** As `siegel_totallyReal_rank3`, with χ_m the character of
F(√(-2m·disc Q))/F defined without choosing a basis. -/
theorem siegel_totallyReal_rank3' (h : finrank F V = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3V Q m) 1 fun v => intrinsicBetaV v Q L m) :=
  siegelFormula3_quadraticSpace_classical' h hQ hL hm

/-- **Siegel's theorem, rank 2** (factor 1/2; Euler product regularized by L(1, χ_Q)^{-1}). With the setting above
and N = 2,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (1/2) · (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · L_F(1, χ_Q)^{-1} · ∏_𝔭 β_𝔭(L, m) (1 - χ_Q(𝔭)/N𝔭)^{-1},
where χ_Q is the quadratic character of F(√(-det H))/F, H the Hessian of Q in the basis `finBasisOfFinrankEq`. -/
theorem siegel_totallyReal_rank2 (h : finrank F V = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV Q L *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h))) (-1) fun v => intrinsicBetaV v Q L m) :=
  siegelFormula2_quadraticSpace_classical h hQ hL hm

/-- **Siegel's theorem, rank 2, basis-free character.** As `siegel_totallyReal_rank2`, with χ_Q the character of
F(√(-disc Q))/F defined without choosing a basis. -/
theorem siegel_totallyReal_rank2' (h : finrank F V = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV Q L *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2V Q) (-1) fun v => intrinsicBetaV v Q L m) :=
  siegelFormula2_quadraticSpace_classical' h hQ hL hm

/-- **Siegel's theorem, rank 1** (factor 1/2 at every place). With the setting above and N = 1,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · 2 · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)/2
  · ∏_𝔭 β_𝔭(L, m)/2. -/
theorem siegel_totallyReal_rank1 (h : finrank F V = 1) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV Q L (algebraMap (𝓞 F) F m) = massGenV Q L *
      (2 * (discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ 1 / 2) *
        ∏' v, intrinsicBetaV v Q L m / 2)) :=
  siegelFormula1_quadraticSpace_classical h hQ hL hm

end Siegel

/-! ## The Tamagawa number and the mass formula over totally real number fields

Setting: F a totally real number field, Q₀ a quadratic form in N ≥ 4 variables with coefficients in 𝓞 F that is
totally positive definite over F. (Ranks 1–3 are also proved in the library; see `docs/results/`.) -/

section Tamagawa

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {N : ℕ}

/-- **τ(SO(Q)) = 2.** For Q₀ as above, the Tamagawa number of SO(Q₀) is 2. Here `tauSO Q₀` is
μ_Tam(K) · ∑_α 1/|Γ_α| (a Tamagawa volume times a double-coset mass); the library proves it equals the covolume of
SO(Q₀)(F) in SO(Q₀)(𝔸) for a Haar measure normalized as Weil's Tamagawa measure (`Measure.tauSO_eq_covolume`). -/
theorem tamagawa_two_totallyReal (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hQ : IsTotallyPosDef (formF Q₀)) :
    tauSO Q₀ = 2 :=
  Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal hN Q₀ hQ

/-- **The Smith–Minkowski–Siegel mass formula.** For Q₀ as above and L = 𝓞_F^N,
∑_{L' ∈ Gen(L)} 1/|O(L')| = ( |d_F|^{-N(N-1)/4} · ∏_σ vol(SO(Q₀^σ)) · ∏_𝔭 α_𝔭(Q₀, Q₀) )^{-1},
with σ running over the embeddings F → ℂ (all real), vol(SO(Q₀^σ)) the closed-form archimedean volume
(`archVolSO` at the Gram determinant `detGram Q₀ σ`), and α_𝔭(Q₀, Q₀) = (1/2) β_𝔭(Q₀, Q₀) Siegel's local density. -/
theorem massFormula_totallyReal (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hQ : IsTotallyPosDef (formF Q₀)) :
    mass (formF Q₀) (stdLat F N) =
      (|(discr F : ℝ)| ^ (-((N : ℝ) * (N - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO N (detGram Q₀ σ)) *
        ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹ :=
  Measure.Weil.massFormula_all_ranks_totallyReal hN Q₀ hQ

end Tamagawa

/-! ## Local–global principles over number fields

Setting: F any number field. `NFPlace F` is the set of places of F (infinite places and nonzero primes of 𝓞 F);
`NFPlace.Everywhere P` means P holds over the completion F_v for every place v. Forms are `QuadForm F n`. -/

section LocalGlobal

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Hilbert reciprocity.** For a, b ∈ F^×, the local Hilbert symbol (a, b)_v is -1 at only finitely many places
v, and at an even number of them; equivalently ∏_v (a, b)_v = 1. -/
theorem hilbertReciprocity_numberField (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard :=
  hilbert_reciprocity_nf a b ha hb

/-- **Hasse–Minkowski (isotropy).** A nondegenerate quadratic form Q over F is isotropic over F if and only if it is
isotropic over every completion F_v. -/
theorem hasseMinkowski_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_nf Q hQ

/-- **Representation is local–global.** A nondegenerate quadratic form Q over F represents c ∈ F^× over F if and only
if it represents c over every completion F_v. -/
theorem represents_iff_everywhere_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) (c : F) (hc : c ≠ 0) :
    Q.RepresentsIn F c ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.RepresentsIn K c :=
  represents_iff_everywhere_nf Q hQ c hc

/-- **Isometry is local–global.** Two nondegenerate quadratic forms Q, R over F in the same number of variables are
isometric over F if and only if they are isometric over every completion F_v. -/
theorem isometric_iff_everywhere_numberField (Q R : QuadForm F n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn F R ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsometricIn K R :=
  isometricIn_iff_everywhere_nf Q R hQ hR

/-- **Hasse–Minkowski over ℚ.** A nondegenerate quadratic form Q over ℚ, in any number of variables, is isotropic over
ℚ if and only if it is isotropic over ℝ and over ℚ_p for every prime p. -/
theorem hasseMinkowski_rat (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ RatPlace.Everywhere fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski Q hQ

end LocalGlobal

end QuadFormsKB.Headlines
