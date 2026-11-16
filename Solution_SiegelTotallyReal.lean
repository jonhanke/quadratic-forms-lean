/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.FrameSiegelAll
import QuadFormsKB.Tamagawa.HeadlineFacts
import QuadFormsKB.Tamagawa.HeadlineFactsWeil

/-!
# Headline statements, proved: Siegel's theorem over totally real number fields

The declarations of `Challenge_SiegelTotallyReal.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/SiegelTotallyReal.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_SiegelTotallyReal.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
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
      Multipliable fun v => intrinsicBetaV v Q L m :=
  ⟨siegelFormula_quadraticSpace_classical hn hQ hL hm,
    genusClassesV_finite hQ hL, fun M _ hM => finite_autLatV_and_repSet hQ hL _ M hM,
    multipliable_intrinsicBetaV hn hQ hL hm⟩

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
        (1 - spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ) :=
  ⟨siegelFormula3_quadraticSpace_classical h hQ hL hm,
    genusClassesV_finite hQ hL, fun M _ hM => finite_autLatV_and_repSet hQ hL _ M hM,
    regFacts_spaceChar3 hQ hL hm _⟩

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
      Multipliable fun v => intrinsicBetaV v Q L m * (1 - spaceChar3V Q m v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ) :=
  ⟨siegelFormula3_quadraticSpace_classical' h hQ hL hm,
    genusClassesV_finite hQ hL, fun M _ hM => finite_autLatV_and_repSet hQ hL _ M hM,
    regFacts_spaceChar3V h hQ hL hm⟩

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
        (1 - spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h)) v / (NFEuler.normP v : ℝ)) ^ (-1 : ℤ) :=
  ⟨siegelFormula2_quadraticSpace_classical h hQ hL hm,
    genusClassesV_finite hQ hL, fun M _ hM => finite_autLatV_and_repSet hQ hL _ M hM,
    regFacts_spaceChar2 hQ hL hm _⟩

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
      Multipliable fun v => intrinsicBetaV v Q L m * (1 - spaceChar2V Q v / (NFEuler.normP v : ℝ)) ^ (-1 : ℤ) :=
  ⟨siegelFormula2_quadraticSpace_classical' h hQ hL hm,
    genusClassesV_finite hQ hL, fun M _ hM => finite_autLatV_and_repSet hQ hL _ M hM,
    regFacts_spaceChar2V h hQ hL hm⟩

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
      Multipliable fun v => intrinsicBetaV v Q L m / 2 :=
  ⟨siegelFormula1_quadraticSpace_classical h hQ hL hm,
    genusClassesV_finite hQ hL, fun M _ hM => finite_autLatV_and_repSet hQ hL _ M hM,
    multipliable_intrinsicBetaV_rankOne h hQ hL hm⟩

end Siegel

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
        Finite {X : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => X i j) ∈ M.1) ∧ (formF Q₀).compMat X = formF T₀} :=
  ⟨by
      have h := (siegelForms_all_ranks Q₀ T₀ hr hrN hpd hpdT).repMass_eq
      rwa [siegelProductAll_of_ge Q₀ T₀ hN h2] at h,
    multipliable_siegelDensity_forms hr hrN hN h2 Q₀ T₀ hpd hpdT,
    genusClasses_finite hpd _ (LatChange.isIntegral_std Q₀),
    fun M hM => ⟨finite_autLat hpd M.2 (SameGenus.isIntegral _ (LatChange.isIntegral_std Q₀) hM),
      finite_repSetT hpd (SameGenus.isIntegral _ (LatChange.isIntegral_std Q₀) hM) _⟩⟩

end SiegelForms

end QuadFormsKB.Headlines
