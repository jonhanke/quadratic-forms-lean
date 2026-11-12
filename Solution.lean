/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB

/-!
# Headline statements, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing library theorems: the
main theorem, plus the finiteness and convergence lemmas for the side conditions (`Tamagawa/HeadlineFacts.lean`,
`genusClassesV_finite`, `genusClasses_finite`, `finite_autLat`, `multipliable_siegelDensity`). `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly
the statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
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

/-! ## The Tamagawa number and the mass formula over totally real number fields

Setting: F a totally real number field, Q₀ a quadratic form in n ≥ 4 variables with coefficients in 𝓞 F that is
totally positive definite over F; the last two statements are the case n = 3. (Ranks 1 and 2 are also
proved in the library; see `docs/results/`.) -/

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
        Finite (MulAction.stabilizer ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀))) x) :=
  ⟨Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal hn Q₀ hQ,
    multipliable_siegelDensity (by omega) (by omega) Q₀ (nondegenerate_of_isTotallyPosDef hQ),
    finite_orbits_SO Q₀ (nondegenerate_of_isTotallyPosDef hQ) (by omega) hQ,
    finite_stabilizer_SO hQ _ (LatChange.isIntegral_std Q₀)⟩

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
      Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
  ⟨Measure.Weil.massFormula_all_ranks_totallyReal hn Q₀ hQ,
    genusClasses_finite hQ _ (LatChange.isIntegral_std Q₀),
    fun M hM => finite_autLat hQ M.2 (SameGenus.isIntegral _ (LatChange.isIntegral_std Q₀) hM),
    multipliable_siegelDensity (by omega) (by omega) Q₀ (nondegenerate_of_isTotallyPosDef hQ)⟩

/-- **τ(SO(Q)) = 2, ternary forms.** As `tamagawa_two_totallyReal`, for a form Q₀ in 3 variables with coefficients
in 𝓞 F that is totally positive definite over F: the Tamagawa number `tauSO Q₀` of SO(Q₀) is 2. Moreover the
product ∏_𝔭 α_𝔭(Q₀, Q₀) in μ_Tam(K) converges unconditionally, and the double-coset space
SO(Q₀)(F)\SO(Q₀)(𝔸_f)/SO(𝓞̂_F^3) in the mass is finite, with finite stabilizers Γ_α. -/
theorem tamagawa_two_totallyReal_ternary (Q₀ : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef (formF Q₀)) :
    tauSO Q₀ = 2 ∧
      (Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀) ∧
      Finite (MulAction.orbitRel.Quotient ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀)))
        (soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F 3)).subgroupOf (soAf (formF Q₀)))) ∧
      ∀ x : soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F 3)).subgroupOf (soAf (formF Q₀)),
        Finite (MulAction.stabilizer ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀))) x) :=
  ⟨QuatOrder.ternaryTamagawaTwo_nf.tau_eq_two Q₀ (nondegenerate_of_isTotallyPosDef hQ) hQ
      (LatChange.isIntegral_std Q₀),
    multipliable_siegelDensity (by norm_num) (by norm_num) Q₀ (nondegenerate_of_isTotallyPosDef hQ),
    finite_orbits_SO Q₀ (nondegenerate_of_isTotallyPosDef hQ) (by norm_num) hQ,
    finite_stabilizer_SO hQ _ (LatChange.isIntegral_std Q₀)⟩

/-- **The Smith–Minkowski–Siegel mass formula, ternary forms.** As `massFormula_totallyReal`, for a form Q₀ in
3 variables with coefficients in 𝓞 F that is totally positive definite over F, and L = 𝓞_F^3:
∑_{L' ∈ Gen(L)} 1/|O(L')| = ( |d_F|^{-3/2} · ∏_σ vol(SO(Q₀^σ)) · ∏_𝔭 α_𝔭(Q₀, Q₀) )^{-1}
(the exponent is -n(n-1)/4 at n = 3). Moreover the genus of L has finitely many classes, every lattice in the genus
has a finite automorphism group, and the product ∏_𝔭 α_𝔭(Q₀, Q₀) converges unconditionally. -/
theorem massFormula_totallyReal_ternary (Q₀ : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef (formF Q₀)) :
    (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F 3), ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) =
      (|(discr F : ℝ)| ^ (-((3 : ℝ) * (3 - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 3 (detGram Q₀ σ)) *
        ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹ ∧
      (genusClasses (formF Q₀) (stdLat F 3)).Finite ∧
      (∀ M : Lat F 3, SameGenus (formF Q₀) (stdLat F 3).1 M.1 → Finite (autLat (formF Q₀) M.1)) ∧
      Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
  ⟨massFormulaHolds_ternary_nf Q₀ hQ,
    genusClasses_finite hQ _ (LatChange.isIntegral_std Q₀),
    fun M hM => finite_autLat hQ M.2 (SameGenus.isIntegral _ (LatChange.isIntegral_std Q₀) hM),
    multipliable_siegelDensity (by norm_num) (by norm_num) Q₀ (nondegenerate_of_isTotallyPosDef hQ)⟩

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
      Multipliable fun v => (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨tauTwoAll_release_uncond n hn Q₀ hQ, multipliable_muLocSO_one Q₀ hQ (by omega) (by omega)⟩

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
      Multipliable fun v => (muLocSO v M.form 1 (soStabSO v M.form : Set (SOv v M.form))).toReal :=
  ⟨(tauTwo_space_uncond hV Q hQ).1, fun M =>
    let ⟨hM, h⟩ := (tauTwo_space_uncond hV Q hQ).2 M
    ⟨hM, h, multipliable_muLocSO_one M.form hM (by omega) (by omega)⟩⟩

/-- **τ(SO_1) = 1.** For every nondegenerate form Q₀ = ⟨c⟩ in one variable over 𝓞 F, the covolume of
SO(V)(F) in SO(V)(𝔸) for Weil's Tamagawa measure (λ_v = 1) is 1 (both groups are trivial; the value is the product
formula for 2c). Moreover the product ∏'_v μ_v(SO(L_v)) converges unconditionally. -/
theorem tamagawa_one_rankOne (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 1 ∧
      Multipliable fun v => (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨covolume_muTam_rankOne Q₀ hQ, multipliable_muLocSO_one Q₀ hQ one_ne_zero (by norm_num)⟩

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
      Multipliable fun v => (muLocSO v Q₀ (lamL (chiE F E) v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨tauTwoBinaryAll_uncond F Q₀ hQ hA E hE, (hasLOne_chiE hE.finrank_eq_two).1, (hasLOne_chiE hE.finrank_eq_two).2,
    multipliable_muLocSO_lamL_chiE hQ hE⟩

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
          (soStabSO v (M.form₂ hV) : Set (SOv v (M.form₂ hV)))).toReal :=
  ⟨(tauTwo_space_binary hV Q hQ hA).1, fun M =>
    let ⟨hM, hA', h⟩ := (tauTwo_space_binary hV Q hQ hA).2 M
    ⟨hM, hA', fun E _ _ _ hE => ⟨h E hE, (hasLOne_chiE hE.finrank_eq_two).1, (hasLOne_chiE hE.finrank_eq_two).2,
      multipliable_muLocSO_lamL_chiE hM hE⟩⟩⟩

/-- **τ(SO(V)) = 1 for isotropic binary forms over every number field** (Weil; Ono's τ(𝔾_m) = 1). Let Q₀ be a
nondegenerate binary form over 𝓞 F with an isotropic vector e ∈ F² (`IsIsoVec Q₀ e`: e ≠ 0, Q₀(e) = 0). Then
SO(V) ≅ 𝔾_m, and τ = vol(SO(V)(F)\SO(V)(𝔸)¹) = 1 for Weil's measure with the convergence factors
λ_v = 1 - N(v)^{-1} and the global factor ρ_F^{-1}, ρ_F the residue of ζ_F at 1 (`tauIso`: the covolume of SO(V)(F)
for this measure restricted to the shell 0 ≤ log |χ_e| < 1, which is the norm-one quotient measure; `muTamIso`).
Moreover the product ∏'_v λ_v^{-1} μ_v(SO(L_v)) in the measure converges unconditionally. -/
theorem tamagawa_one_binary_isotropic (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (e : Fin 2 → F)
    (he : IsIsoVec Q₀ e) :
    tauIso Q₀ hQ he = 1 ∧
      Multipliable fun v => (muLocSO v Q₀ (lamV v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨tauOne_binary_isotropic_uncond F Q₀ hQ ⟨e, he⟩ e he, multipliable_muLocSO_lamV_of_isotropicF hQ ⟨e, he⟩⟩

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
      Multipliable fun v => (muLocSO v (M.form₂ hV) (lamV v) (soStabSO v (M.form₂ hV) : Set (SOv v (M.form₂ hV)))).toReal :=
  ⟨(tauOne_space_binary_isotropic hV Q hQ hI).1, fun M =>
    let ⟨hM, hI', h⟩ := (tauOne_space_binary_isotropic hV Q hQ hI).2 M
    ⟨hM, hI', h, multipliable_muLocSO_lamV_of_isotropicF hM hI'⟩⟩

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

**Side conditions.** Each statement also states that the real products ∏'_𝔭 on the local side converge
unconditionally (a `tprod` is 1 otherwise), that L_F(1, χ) exists and is positive where it occurs, that
0 < ∑_i v(M_i) < ∞, and that there are finitely many proper classes M_i in the genus of L (`Finite (DC Q₀)`, from
`finite_DC`: O'Meara 103:4, for every nondegenerate Q₀ of any signature). The sums over classes are sums in [0, ∞];
with finitely many classes they are finite sums. -/

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
`archFibrationNF`. Moreover ∏_𝔭 β_𝔭(L, m) converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_numberField {k : ℕ} (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)
    {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensity v Q₀ m) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefinite_uncond hQ hk hm ξ,
    Siegel.multipliable_eulerFactorNF_uncond hQ (by omega) fun h => hm (by simp [h]),
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula for indefinite forms, forms by forms, every number field** (Siegel 1936; Weil 1965).
For Q₀ nondegenerate over 𝓞 F in N = r + n' variables (any signature), n' ≥ 3, and T₀ nondegenerate over 𝓞 F of rank
r ≥ 1 represented by Q₀ over F (a rational frame Ξ, Q₀ ∘ Ξ = T₀),
c_∞(T₀) · ∑_i ρ(M_i, T₀) = |d_F|^{-(N(N-1) - n'(n'-1))/4} ∏_𝔭 β_𝔭(L, T₀) · ∑_i v(M_i),
with c_∞(T₀) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |det H_{T₀}|_w^{-n'} (`cInfTNF`) and ρ for the frame fibration
`frameArchFibrationNF`. Moreover the product ∏_𝔭 β_𝔭(L, T₀) converges unconditionally and
0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_numberField {r n' : ℕ} (hr : 1 ≤ r) (hn' : 3 ≤ n') (Q₀ : QuadForm (𝓞 F) (r + n'))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationNF Q₀ hQ T₀ hT hn' Ξ) i =
      ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_uncond Q₀ hQ T₀ hT hn' Ξ hr,
    multipliable_localDensityForm_of_frame Q₀ hQ T₀ hT hn' Ξ,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula, forms by forms with an anisotropic stabilizer of rank 2, every number field.** For Q₀
nondegenerate over 𝓞 F in N = r + 2 variables (any signature), T₀ nondegenerate of rank r ≥ 1 with a rational frame Ξ,
and δ = -det H_{Q₀} det H_{T₀} not a square in F (`deltaForms`; the orthogonal complement of Ξ is anisotropic),
c_∞(T₀) · ∑_i ρ(M_i, T₀) = |d_F|^{-(N(N-1)-2)/4} L_F(1, χ) ∏_𝔭 β_𝔭(L, T₀)(1 - χ(𝔭)/N𝔭) · ∑_i v(M_i),
χ = `chiForms Q₀ T₀` (χ(𝔭) = (δ/𝔭) at 𝔭 ∤ 2δ, 0 otherwise), ρ for `frameArchFibrationRank2`. Moreover
L_F(1, χ) = lim_{s→1⁺} L_F(s, χ) exists and is positive, the corrected product ∏_𝔭 β_𝔭(L, T₀)(1 - χ(𝔭)/N𝔭)
converges unconditionally, and 0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_rank2 {r : ℕ} (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (hW : ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
    (Ξ : RatFrame Q₀ T₀) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationRank2 Q₀ hQ T₀ hT hW Ξ) i =
      ENNReal.ofReal (frameDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiForms Q₀ T₀) (LOne (chiForms Q₀ T₀)) ∧ 0 < LOne (chiForms Q₀ T₀) ∧
    (Multipliable fun v =>
      NF.localDensityForm v Q₀ T₀ * (1 - chiForms Q₀ T₀ v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ)) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  by
    refine ⟨siegelIndefiniteForms_rank2_uncond Q₀ hQ T₀ hT hW Ξ hr, (lOne_chiForms_nf hQ hT hW).2,
      (lOne_chiForms_nf hQ hT hW).1, ?_,
      tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      finite_DC Q₀ hQ⟩
    simpa only [zpow_one] using multipliable_localDensityForm_rank2 Q₀ hQ T₀ hT hW Ξ hr

/-- **Siegel's formula for numbers by ternary forms, every number field** (the case r = 1 of
`siegel_indefinite_forms_rank2`). For Q₀ nondegenerate ternary over 𝓞 F (any signature), m ∈ 𝓞 F, m ≠ 0,
represented by Q₀ over F (a rational point ξ), and -2m det H_{Q₀} not a square in F (m^⊥ anisotropic),
c_∞(m) · ∑_i ρ(M_i, m) = |d_F|^{-1} L_F(1, χ) ∏_𝔭 β_𝔭(L, m)(1 - χ(𝔭)/N𝔭) · ∑_i v(M_i),
with χ = `chiForms Q₀ ⟨m⟩` (χ(𝔭) = (-2m det H_{Q₀}/𝔭) at the good primes), ρ the measures of the representations
of m (vectors read as 1-frames, `ratFrameEquivRatSphere`) for `frameArchFibrationRank2`. Moreover L_F(1, χ) exists
and is positive, the corrected product converges unconditionally, and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
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
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  by
    refine ⟨siegelIndefinite_ternary_uncond Q₀ hQ hm hW ξ,
      (lOne_chiForms_nf hQ (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)).2,
      (lOne_chiForms_nf hQ (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)).1, ?_,
      tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
      finite_DC Q₀ hQ⟩
    have h := multipliable_localDensityForm_rank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
      (not_isSquare_deltaForms_unary hW) ((ratFrameEquivRatSphere Q₀ m).symm ξ) le_rfl
    simpa only [zpow_one, NF.localDensityForm_unary] using h

/-- **Siegel's formula, forms by forms with an isotropic stabilizer of rank 2 (Siegel's excluded case),
regularized, every number field.** For Q₀ nondegenerate over 𝓞 F in N = r + 2 variables (any signature), T₀
nondegenerate of rank r ≥ 1 with a rational frame Ξ, and δ = -det H_{Q₀} det H_{T₀} a square in F (the stabilizers
are split tori),
2 c_∞(T₀) · ∑_i ρ¹(M_i, T₀) = |d_F|^{-(N(N-1)-2)/4} ρ_F ∏_𝔭 β_𝔭(L, T₀)(1 - N𝔭^{-1}) · ∑_i v(M_i),
ρ_F = Res_{s=1} ζ_F(s), with ρ¹ the measures of representations for the norm-one stabilizers (`repMeasureIso`).
Moreover the corrected product converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_rank2_isotropic {r : ℕ} (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 2))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀) :
    2 * (cInfTNF Q₀ T₀ * ∑' i, repMeasureIso Q₀ hQ T₀ hT hiso Ξ i) =
      ENNReal.ofReal (isoDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ * lamV v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_rank2_isotropic_uncond Q₀ hQ T₀ hT hiso Ξ hr,
    multipliable_localDensityForm_iso Q₀ hQ T₀ hT hiso Ξ hr,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula for numbers by ternary forms with m^⊥ isotropic (Siegel's excluded case), regularized,
every number field** (the case r = 1 of `siegel_indefinite_forms_rank2_isotropic`). For Q₀ nondegenerate ternary over
𝓞 F (any signature), m ∈ 𝓞 F, m ≠ 0, represented by Q₀ over F (a rational point ξ), and -2m det H_{Q₀} a square in F,
2 c_∞(m) · ∑_i ρ¹(M_i, m) = |d_F|^{-1} ρ_F ∏_𝔭 β_𝔭(L, m)(1 - N𝔭^{-1}) · ∑_i v(M_i).
Moreover the corrected product converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_ternary_isotropic (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    2 * (cInfNF (k := 2) (m : F) * ∑' i, repMeasureIso Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
        (isSquare_deltaForms_unary hiso) ((ratFrameEquivRatSphere Q₀ m).symm ξ) i) =
      ENNReal.ofReal (ternaryIsoDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensity v Q₀ m * lamV v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefinite_ternary_isotropic_uncond Q₀ hQ hm hiso ξ,
    multipliable_localDensity_ternary_iso Q₀ hQ hm hiso ξ,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula, forms of corank one, every number field** (Siegel 1935, Hauptsatz for n = m + 1,
ε = 1/2). For Q₀ nondegenerate over 𝓞 F in N = r + 1 variables (any signature), r ≥ 2, and T₀ nondegenerate of rank r
with a rational frame Ξ,
c⁽¹⁾_∞(Q₀) · ∑_i n(M_i, T₀) = (1/2) |d_F|^{-(N(N-1))/4} ∏_𝔭 β_𝔭(L, T₀) · ∑_i v(M_i),
n(M_i, T₀) = `repCount` the number of representations of T₀ by M_i modulo the unit group (a cardinal in [0, ∞]),
c⁽¹⁾_∞(Q₀) = |d_F|^{-N(N-1)/4} ∏_{w | ∞} |det H_{Q₀}|_w^{-1} (`cInfCorankOne`). Moreover the product
∏_𝔭 β_𝔭(L, T₀) converges unconditionally and 0 < ∑_i v(M_i) < ∞; there are
finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_corank1 {r : ℕ} (hr : 2 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, Indefinite.repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_corank1_uncond Q₀ hQ T₀ hT Ξ hr,
    multipliable_localDensityForm_corank1 Q₀ hQ T₀ hT Ξ hr,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

/-- **Siegel's formula for the numbers represented by an anisotropic binary form, every number field**
(Siegel 1935, Hauptsatz for n = 2, m = 1, ε = 1/2; Dirichlet over ℚ). For Q₀ a nondegenerate binary form over 𝓞 F (any
signature) that is anisotropic over F, E a discriminant field of Q₀ (`IsDiscField`; one exists,
`exists_isDiscField_of_anisotropicF`), and T₀ = ⟨m⟩ nondegenerate of rank one with a rational frame Ξ (Q₀(Ξ) = m),
c⁽¹⁾_∞(Q₀) · ∑_i n(M_i, m) = (1/2) |d_F|^{-1/2} L_F(1, χ_E)^{-1} ∏_𝔭 L_𝔭(1, χ_E) β_𝔭(L, m) · ∑_i v(M_i),
n(M_i, m) = `repCount` (the representations modulo the unit group SO(M_i); finite for definite Q₀, infinite unit group
for indefinite Q₀). Moreover L_F(1, χ_E) exists and is positive, and the product ∏_𝔭 L_𝔭(1, χ_E) β_𝔭(L, m)
converges unconditionally, and 0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, Indefinite.repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) * ∑' i, unitVolume Q₀ hQ i ∧
    HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ / lamL (chiE F E) v) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefinite_binary_uncond Q₀ hQ hA E hE T₀ hT Ξ, (hasLOne_chiE hE.finrank_eq_two).1,
    (hasLOne_chiE hE.finrank_eq_two).2, multipliable_binDensity Q₀ hQ E hE T₀ hT Ξ,
    (tsum_unitVolume_ne_zero_top_binary Q₀ hQ hA E hE).1, (tsum_unitVolume_ne_zero_top_binary Q₀ hQ hA E hE).2,
    finite_DC Q₀ hQ⟩

open Classical in
/-- **Siegel's formula for forms of the same rank (corank zero), every number field** (Siegel 1935, Hauptsatz
for n = m, ε = 1/2 at every place). For Q₀ nondegenerate over 𝓞 F in N ≥ 3 variables (any signature) and T₀
nondegenerate in N variables with a rational frame Ξ (Q₀ ∘ Ξ = T₀, Ξ ∈ GL_N(F)),
∑_i n(M_i, T₀) = ∏_{w | ∞} |det Ξ|_w^{-1} ∏_𝔭 β_𝔭(L, T₀)/2 · ∑_i v(M_i)
(normalized absolute values; n = `repCount`). Moreover the product ∏_𝔭 β_𝔭(L, T₀)/2 converges unconditionally and
0 < ∑_i v(M_i) < ∞; there are finitely many proper classes M_i (`DC Q₀` is finite). -/
theorem siegel_indefinite_forms_corank0 {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    ∑' i, Indefinite.repCount Q₀ T₀ i =
      ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) *
        ∏' v, NF.localDensityForm v Q₀ T₀ / 2) * ∑' i, unitVolume Q₀ hQ i ∧
    (Multipliable fun v => NF.localDensityForm v Q₀ T₀ / 2) ∧
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ ∧
    Finite (DC Q₀) :=
  ⟨siegelIndefiniteForms_corank0_uncond Q₀ hQ T₀ hT Ξ hN,
    multipliable_localDensityForm_half_corank0 Q₀ hQ T₀ hT Ξ hN,
    tsum_unitVolume_ne_zero Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    tsum_unitVolume_ne_top Q₀ hQ (tauTwoAll_release_uncond _ (by omega) Q₀ hQ),
    finite_DC Q₀ hQ⟩

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
        Finite {X : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => X i j) ∈ M.1) ∧ (formF Q₀).compMat X = formF T₀} :=
  ⟨by
      have h := (siegelForms_all_ranks Q₀ T₀ hr hrN hpd hpdT).repMass_eq
      rwa [siegelProductAll_of_ge Q₀ T₀ hN h2] at h,
    multipliable_siegelDensity_forms hr hrN hN h2 Q₀ T₀ hpd hpdT,
    genusClasses_finite hpd _ (LatChange.isIntegral_std Q₀),
    fun M hM => ⟨finite_autLat hpd M.2 (SameGenus.isIntegral _ (LatChange.isIntegral_std Q₀) hM),
      finite_repSetT hpd (SameGenus.isIntegral _ (LatChange.isIntegral_std Q₀) hM) _⟩⟩

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
      (Siegel.genusClasses (LocalDensity.ofMatrixZ A)).Finite ∧ 0 < Siegel.mass (LocalDensity.ofMatrixZ A) :=
  ⟨ConwaySloane.Mass.mass_eq_stdMass_mul_symbols_unconditional hn hA hQ τ N₂ hτ hτN σ N hodd,
    (Siegel.genusFinite hQ).finite_classes, Siegel.mass_pos hQ (Siegel.genusFinite hQ)⟩

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
      Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaGHYAt v Q₀ :=
  ⟨ghy_prop74 hn hodd Q₀ hQ hpd hmax, finite_DC Q₀ hQ,
    (tsum_inv_card_unitGroup Q₀ hQ (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)).1, by
      have e : (fun v : HeightOneSpectrum (𝓞 F) => lambdaGHYAt v Q₀) = fun v =>
          ‖(2 : v.adicCompletion F)‖ ^ (n / 2) * dualIndexAt v Q₀ ^ (n / 2) * lambdaGen v Q₀ :=
        funext fun v => lambdaGHYAt_eq v hn hodd Q₀ hQ hmax
      rw [e]
      exact (((hasFiniteMulSupport_norm_two (F := F)).pow (n / 2)).mul
        ((hasFiniteMulSupport_dualIndexAt Q₀ hQ).pow (n / 2))).mul (hasFiniteMulSupport_lambdaGen Q₀ hQ)⟩

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
      Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaGHYEvenAt v Q₀ :=
  ⟨ghy_prop75_proved hn heven Q₀ hQ hpd hmax, finite_DC Q₀ hQ,
    (tsum_inv_card_unitGroup Q₀ hQ (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)).1,
    (hasFiniteMulSupport_dualIndexAt Q₀ hQ).subset fun v hv => by
      simp only [Function.mem_mulSupport] at hv ⊢
      intro h1
      apply hv
      have h := lambdaGHYEvenAt_mul ramifiedDualIndexConductor_proved v hn heven Q₀ hQ hmax
      have hc : condFactor v Q₀ = 1 := by
        unfold condFactor
        rw [if_neg (not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven h1)]
      rw [hc, h1, lambdaAt_eq_one_of Q₀ v h1] at h
      simpa using h⟩

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
      Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaGen v Q₀ :=
  ⟨theorem51_general hn Q₀ hQ hmax, finite_DC Q₀ hQ, hasFiniteMulSupport_dualIndexAt Q₀ hQ,
    hasFiniteMulSupport_lambdaGen Q₀ hQ⟩

end ExactMass

/-! ## Classification of lattices and genera

O'Meara's classification of lattices over the completion of a number field at a dyadic prime (93:28) and at a prime
where 2 is prime (93:29); Conway–Sloane's description of the p-adically automorphous numbers (Sphere Packings,
Lattices and Groups, Chapter 15, Theorem 18) at every prime; and the description of the genus of a positive definite
integral lattice by its discriminant form (Conway–Sloane 1988, §11, Lemmas 2 and 4). The two O'Meara statements and
Theorem 18 are named propositions of the library (`OMeara.DyadicClassification`, `OMeara.TwoAdicClassification`,
`ConwaySloane.Theorem18Statement`), each a single field stating the theorem; the docstrings spell them out. -/

section Classification

/-- **Conway–Sloane, Theorem 18, at every prime** (J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and
Groups, Chapter 15, §9.5; "based on Theorem 81" of Watson). `ConwaySloane.Theorem18Statement` says: for every
nondegenerate form Q over ℚ in n variables, every lattice L in ℚ^n and every prime p (`v`, a nonzero prime of
𝓞_ℚ = ℤ), a p-adic unit A ∈ ℚ_p^× is p-adically automorphous, i.e. lies in θ(O⁺(L_p)), the group of spinor norms
of the proper automorphisms of L_p (`Lattices.localSpinorNormGroup Q hQ v L`), if and only if, up to squares, A is
the product Q(x_1) ⋯ Q(x_{2k}) of the norms of an even number of p-adic root vectors x_i: vectors with Q(x_i) ≠ 0
whose reflection maps L_p onto itself (`ConwaySloane.IsRootVector`). The book quotes the theorem without proof;
both directions are proved here, at p = 2 included. -/
theorem automorphous_iff_rootVectors : ConwaySloane.Theorem18Statement :=
  ConwaySloane.theorem18Statement_holds

/-- **O'Meara 93:28: classification of lattices at a dyadic prime** (O. T. O'Meara, Introduction to Quadratic
Forms, §93F, 93:28). Let F be a number field, 𝔭 = `w` a nonzero prime of 𝓞 F, F_𝔭 the completion with ring of
integers 𝔬, and V a finite-dimensional quadratic space over F_𝔭 with form Q. `OMeara.DyadicClassification 𝔬 Q`
says: if 2 is not a unit of 𝔬 (𝔭 is dyadic) and Q is regular, let L and K be lattices on V with Jordan splittings
L = L_1 ⊥ ⋯ ⊥ L_t and K = K_1 ⊥ ⋯ ⊥ K_t (`OMeara.IsJordanSplitting`) having the same fundamental invariants
t, dim L_i, 𝔰_i, 𝔴_i, a_i (`OMeara.SameFundamentalInvariants`), and let L_(i) = L_1 ⊥ ⋯ ⊥ L_i and K_(i) be the
Jordan chains (`OMeara.jordanChain`). Then L and K are isometric (`OMeara.cls Q L = OMeara.cls Q K`) if and only if
for 1 ≤ i ≤ t - 1:
1. dL_(i)/dK_(i) ≅ 1 mod 𝔣_i (`OMeara.DiscQuotSqEquivMod`), with 𝔣_i the ideal of §93E (`OMeara.fIdeal`);
2. FL_(i) → FK_(i) ⊥ ⟨a_{i+1}⟩ (`OMeara.SpanRepresents`) when 𝔣_i ⊊ 4 a_{i+1} 𝔴_{i+1}^{-1};
3. FL_(i) → FK_(i) ⊥ ⟨a_i⟩ when 𝔣_i ⊊ 4 a_i 𝔴_i^{-1}.
Indices are 0-based in Lean: the condition for O'Meara's i is stated for the pair i, j = i + 1. -/
theorem dyadicClassification {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {V : Type*}
    [AddCommGroup V] [Module (w.adicCompletion F) V] [FiniteDimensional (w.adicCompletion F) V]
    [Module (w.adicCompletionIntegers F) V] [IsScalarTower (w.adicCompletionIntegers F) (w.adicCompletion F) V]
    (Q : QuadraticForm (w.adicCompletion F) V) :
    OMeara.DyadicClassification (w.adicCompletionIntegers F) Q :=
  OMeara.Step8.dyadicClassification_nf w Q

/-- **O'Meara 93:29: classification of lattices at a 2-adic prime** (O. T. O'Meara, Introduction to Quadratic
Forms, §93G, 93:29). Let F be a number field, 𝔭 = `v` a nonzero prime of 𝓞 F, F_𝔭 the completion with ring of
integers 𝔬, and V a finite-dimensional quadratic space over F_𝔭 with form Q. `OMeara.TwoAdicClassification 𝔬 Q`
says: if 2 is a prime element of 𝔬 (`OMeara.IsTwoAdic`; for example F_𝔭 = ℚ_2) and Q is regular, let L and K be
lattices on V with Jordan splittings L = L_1 ⊥ ⋯ ⊥ L_t and K = K_1 ⊥ ⋯ ⊥ K_t having the same Jordan invariants
t, dim L_i, 𝔰_i, 𝔫_i (`OMeara.SameJordanInvariants`), and let L_(i), K_(i) be the Jordan chains. Then L and K are
isometric if and only if for 1 ≤ i ≤ t - 1:
1. dL_(i)/dK_(i) ≅ 1 mod 𝔫_i 𝔫_{i+1}/𝔰_i²;
2. FL_(i) → FK_(i) ⊥ ⟨2^{u_i}⟩ when 𝔫_{i+1} ⊆ 4 𝔫_i, where 2^{u_i} 𝔬 = 𝔫_i.
Here 𝔰_i is the scale and 𝔫_i the norm ideal of L_i (`OMeara.scale`, `OMeara.normIdeal`). Indices are 0-based in
Lean, as in `dyadicClassification`. -/
theorem twoAdicClassification {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {V : Type*}
    [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
    [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]
    (Q : QuadraticForm (v.adicCompletion F) V) :
    OMeara.TwoAdicClassification (v.adicCompletionIntegers F) Q :=
  OMeara.G29.twoAdicClassification_twoAdic_nf v Q

/-- **The genus from the discriminant form, modulo the type** (J. H. Conway and N. J. A. Sloane, "Low-dimensional
lattices IV: the mass formula", 1988, §11, Lemma 2). Two positive definite integral lattices L and M of dimension n,
given by their Gram matrices A and B (`ConwaySloane.Mass.PosDefGram`), are in the same genus (the forms xᵀAx and
xᵀBx are in the same genus, `Siegel.SameGenus`) if and only if they have the same type T (T = 1 if the lattice is
odd, T = 2 if it is even, `ConwaySloane.Mass.gramType`) and there is an isomorphism L*/L ≅ M*/M of the discriminant
groups preserving norms modulo T (`ConwaySloane.Mass.DiscIso T A B`). -/
theorem sameGenus_iff_discIso {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} (hA : ConwaySloane.Mass.PosDefGram A)
    (hB : ConwaySloane.Mass.PosDefGram B) :
    Siegel.SameGenus (LocalDensity.ofMatrixZ A) (LocalDensity.ofMatrixZ B) ↔
      (ConwaySloane.Mass.gramType A = ConwaySloane.Mass.gramType B ∧
        ConwaySloane.Mass.DiscIso (ConwaySloane.Mass.gramType A) A B) :=
  ConwaySloane.Mass.lemma2 hA hB

/-- **The genus from the discriminant form, modulo 1** (J. H. Conway and N. J. A. Sloane, "Low-dimensional
lattices IV: the mass formula", 1988, §11, Lemma 4). Two positive definite integral lattices L and M of dimension n
(Gram matrices A and B) are in the same genus if and only if they have the same type and there is an isomorphism
L*/L ≅ M*/M of the discriminant groups preserving norms modulo 1 (`ConwaySloane.Mass.DiscIso 1 A B`). -/
theorem sameGenus_iff_discIso_one {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} (hA : ConwaySloane.Mass.PosDefGram A)
    (hB : ConwaySloane.Mass.PosDefGram B) :
    Siegel.SameGenus (LocalDensity.ofMatrixZ A) (LocalDensity.ofMatrixZ B) ↔
      (ConwaySloane.Mass.gramType A = ConwaySloane.Mass.gramType B ∧ ConwaySloane.Mass.DiscIso 1 A B) :=
  ConwaySloane.Mass.lemma4 hA hB

end Classification

/-! ## Class numbers

Watson's theorem (1963): a genus of positive definite integer-valued forms in more than 11 variables is never a single
class. -/

section ClassNumbers

/-- **Watson's theorem: every genus in n > 11 variables has at least two classes** (G. L. Watson, "The
class-number of a positive quadratic form", Proc. London Math. Soc. (3) 13 (1963), 549–576, Theorem 1, the case
n ≥ 12 of (1.1); quoted without proof in J. W. S. Cassels, Rational Quadratic Forms, Appendix A, §3, p. 364). Let Q
be a positive definite integer-valued form in n > 11 variables (`QuadForm ℤ n`, the polynomial ∑_{i ≤ j} c_ij x_i x_j
with integer coefficients, and `IntQF.PosDef Q`). Then the genus of Q contains at least two GL_n(ℤ)-classes of forms
(`Siegel.genusClasses Q`, counted with Mathlib's `Set.encard`), and finitely many. Watson's other case of (1.1),
n = 11, is not part of this statement. -/
theorem watson_twoClasses {n : ℕ} (hn : 11 < n) (Q : QuadForm ℤ n) (hQ : IntQF.PosDef Q) :
    (2 : ℕ∞) ≤ (Siegel.genusClasses Q).encard ∧ (Siegel.genusClasses Q).Finite :=
  ⟨QuadFormsKB.Watson1963.two_le_encard_genusClasses hn hQ, (Siegel.genusFinite hQ).finite_classes⟩

end ClassNumbers

/-! ## Quaternion orders

Theorems of J. Voight, *Quaternion Algebras* (2021): maximal orders and their discriminant, the correspondence between
ternary quadratic forms and quaternion orders, and the Eichler mass formula for maximal orders. -/

section QuaternionOrders

/-- **Maximal orders are the orders of discriminant equal to the discriminant of the algebra** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
Theorem 15.5.5, p. 249), over every number field F. Let a, b be nonzero elements of the ring of integers 𝓞_F,
B = (a, b)_F the quaternion algebra with i² = a, j² = b, ij = −ji (`QuatOrder.QuatF F a b`), and O an 𝓞_F-order
of B (`QuatOrder.IsOrder`: a finitely generated 𝓞_F-submodule and subring spanning B over F) that is free of
rank 4 as an 𝓞_F-module (automatic when 𝓞_F is a principal ideal domain). Then O is a maximal order
(`QuatOrder.IsMaximalOrder`: not properly contained in another order) if and only if its reduced discriminant
is the product of the finite primes at which B ramifies (`QuatOrder.ramFin`): `Voight.HasDiscrd O 𝔇` says that
for every 𝓞_F-basis e₀, …, e₃ of O the determinant det(trd(e_i e_j)) of the reduced trace form generates the
ideal 𝔇². -/
theorem voight_maximal_iff_discriminant {F : Type} [Field F] [NumberField F] (a b : 𝓞 F) (ha : a ≠ 0)
    (hb : b ≠ 0) (O : Subalgebra (𝓞 F) (QuatOrder.QuatF F a b)) (hO : QuatOrder.IsOrder (𝓞 F) F O)
    (hfree : Nonempty (Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O))) :
    QuatOrder.IsMaximalOrder (𝓞 F) F O ↔
      Voight.HasDiscrd O (∏ v ∈ QuatOrder.ramFin ha hb, v.asIdeal) :=
  QuadFormsKB.Voight.Disc.maximalIffDiscriminant F a b ha hb O hO hfree

/-- **Ternary quadratic forms and quaternion orders** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021, Main Theorem 22.4.1, p. 364, due to
Gross and Lucianovic), for a principal ideal domain R whose fraction field F has 2 ≠ 0. For a ternary form
Q = ∑_{i ≤ j} c_ij x_i x_j over R (`QuadForm R 3`), `Voight.Clf0 Q` is its even Clifford algebra and
`Voight.ternaryDisc Q` its half-discriminant 4c₀₀c₁₁c₂₂ + c₁₂c₀₂c₀₁ − c₀₀c₁₂² − c₁₁c₀₂² − c₂₂c₀₁²; Q is
nondegenerate when this is nonzero. A quaternion R-order (`Voight.IsQuaternionOrder R F O`) is an R-algebra that
is finitely generated and torsion-free as an R-module and whose extension F ⊗_R O is a quaternion algebra over F.
Forms Q, Q' are similar (`Voight.Similar`) if Q' is isometric over R to u·Q for a unit u of R. The three
conjuncts: the even Clifford algebra of a nondegenerate form is a quaternion order; every quaternion order is
isomorphic to one of them; and two of them are isomorphic exactly when the forms are similar. Together:
Q ↦ Clf⁰(Q) is a bijection from similarity classes of nondegenerate ternary forms onto isomorphism classes of
quaternion R-orders. -/
theorem voight_evenClifford_correspondence (R F : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] (h2 : (2 : F) ≠ 0) :
    (∀ Q : QuadForm R 3, Voight.ternaryDisc Q ≠ 0 → Voight.IsQuaternionOrder R F (Voight.Clf0 Q)) ∧
    (∀ (O : Type) [Ring O] [Algebra R O], Voight.IsQuaternionOrder R F O →
      ∃ Q : QuadForm R 3, Voight.ternaryDisc Q ≠ 0 ∧ Nonempty (O ≃ₐ[R] Voight.Clf0 Q)) ∧
    (∀ Q Q' : QuadForm R 3, Voight.ternaryDisc Q ≠ 0 → Voight.ternaryDisc Q' ≠ 0 →
      (Nonempty (Voight.Clf0 Q ≃ₐ[R] Voight.Clf0 Q') ↔ Voight.Similar Q Q')) :=
  have h := QuadFormsKB.Voight.evenCliffordCorrespondence_of_two_ne_zero (R := R) h2
  ⟨h.isQuaternionOrder, fun O _ _ => h.exists_clf0 O, h.nonempty_equiv_iff_similar⟩

/-- **The Eichler mass formula for maximal orders over a totally real number field** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
Main Theorem 26.1.5 and Theorem 26.1.12 for level one, p. 432–433). Let F be a totally real number field of
degree n = [F : ℚ] whose ring of integers 𝓞_F is a principal ideal domain, a, b nonzero in 𝓞_F with
B = (a, b)_F totally definite (`QuatOrder.IsTotDefinite a b`: σ(a) < 0 and σ(b) < 0 for every real embedding σ),
and O a maximal order of B containing 𝓞_F⟨i, j⟩ (`QuatOrder.stdOrder F a b ≤ O`). Then
mass(O) = ∑_{[J]} 1/[O_R(J)^× : 𝓞_F^×] (`Voight.classMass O`: the sum over the classes of nonzero left
ideals J of O under J ~ Jβ, β ∈ B^×, of the inverse index of 𝓞_F^× in the unit group of the right order of J)
equals 2 ζ_F(2) (2π)^{−2n} |d_F|^{3/2} h_F ∏_{𝔭 | 𝔇} (N𝔭 − 1), with ζ_F the Dedekind zeta function
(`NFEuler.dedekindZetaR`), d_F the discriminant, h_F the class number and 𝔇 the product of the finite ramified
primes of B. Moreover (so that every term is meaningful) there are finitely many classes and every index is
finite. The containment O ⊇ 𝓞_F⟨i, j⟩ and the principal ideal domain hypothesis are restrictions of this
formalization; Voight's theorem holds for every maximal order and every class number. -/
theorem eichlerMass_totallyReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : QuatOrder.IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatOrder.QuatF F a b)} (hO : QuatOrder.IsMaximalOrder (𝓞 F) F O)
    (hstd : QuatOrder.stdOrder F a b ≤ O) :
    Voight.classMass O = 2 * NFEuler.dedekindZetaR F 2 / (2 * Real.pi) ^ (2 * Module.finrank ℚ F) *
        |(NumberField.discr F : ℝ)| ^ (3 / 2 : ℝ) * (NumberField.classNumber F : ℝ) *
        ∏ v ∈ QuatOrder.ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1) ∧
      Finite (Quotient (QuatOrder.idealSetoid O)) ∧
      ∀ J : Ideal O, J ≠ ⊥ → (QuatOrder.centralUnitsIn (R := 𝓞 F) J).FiniteIndex :=
  ⟨QuadFormsKB.Voight.Wave3.classMass_eq_maximal ha hb hdef hO hstd,
    QuadFormsKB.QuatOrder.Gen.finite_classes ha hb hO
      (fun _ hx => QuadFormsKB.QuatOrder.eq_zero_of_nrd_eq_zero hdef hx),
    fun _ hJ => QuadFormsKB.QuatOrder.finiteIndex_centralUnitsIn hdef hO.1 hstd hJ⟩

/-- **The Eichler mass formula over ℚ** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021, Theorem 25.1.1 = Theorem 25.3.15, p. 415 and 422).
Let a, b be nonzero integers (in 𝓞_ℚ) with B = (a, b)_ℚ definite (a < 0 and b < 0) and O a maximal order of B
containing ℤ⟨i, j⟩. Then mass(O) = ∑_{[J]} 1/[O_R(J)^× : {±1}] (`Voight.classMass O`, as in
`eichlerMass_totallyReal`) equals φ(D)/12 = (1/12) ∏_{p | D} (p − 1), the product over the primes at which B
ramifies; there are finitely many classes and every index is finite. The containment O ⊇ ℤ⟨i, j⟩ is a
restriction of this formalization. -/
theorem eichlerMass_rat {a b : 𝓞 ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : QuatOrder.IsTotDefinite a b)
    {O : Subalgebra (𝓞 ℚ) (QuatOrder.QuatF ℚ a b)} (hO : QuatOrder.IsMaximalOrder (𝓞 ℚ) ℚ O)
    (hstd : QuatOrder.stdOrder ℚ a b ≤ O) :
    Voight.classMass O = (∏ v ∈ QuatOrder.ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)) / 12 ∧
      Finite (Quotient (QuatOrder.idealSetoid O)) ∧
      ∀ J : Ideal O, J ≠ ⊥ → (QuatOrder.centralUnitsIn (R := 𝓞 ℚ) J).FiniteIndex :=
  ⟨QuadFormsKB.Voight.Wave3.classMass_eq_rat_maximal ha hb hdef hO hstd,
    QuadFormsKB.QuatOrder.Gen.finite_classes ha hb hO
      (fun _ hx => QuadFormsKB.QuatOrder.eq_zero_of_nrd_eq_zero hdef hx),
    fun _ hJ => QuadFormsKB.QuatOrder.finiteIndex_centralUnitsIn hdef hO.1 hstd hJ⟩

end QuaternionOrders

/-! ## Even unimodular lattices

G. Chenevier and J. Lannes (2019), §1.1: positive definite even unimodular lattices exist exactly in the dimensions
divisible by 8, and there are finitely many classes in each dimension. -/

section EvenUnimodular

/-- **Even unimodular lattices: dimensions divisible by 8, finitely many classes** (G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices*, Ergebnisse der Mathematik und ihrer Grenzgebiete (3. Folge) 69, Springer, 2019, §1.1, p. 1,
Scholium 2.2.2). An even unimodular lattice of dimension n is here a positive definite integer-valued form Q in
n variables whose Gram matrix (the Hessian of Q, with even diagonal) has determinant 1
(`ChenevierLannes.IsEvenUnimodular Q`). Such a form exists if and only if 8 divides n, and the set X_n of their
GL_n(ℤ)-classes (`Siegel.classOf Q`) is finite. -/
theorem evenUnimodular_classes (n : ℕ) :
    ((∃ Q : QuadForm ℤ n, ChenevierLannes.IsEvenUnimodular Q) ↔ 8 ∣ n) ∧
      {c | ∃ Q : QuadForm ℤ n, ChenevierLannes.IsEvenUnimodular Q ∧ Siegel.classOf Q = c}.Finite :=
  ⟨⟨fun ⟨Q, hQ⟩ => QuadFormsKB.ChenevierLannes.classSet_nonempty_iff.1 ⟨_, Q, hQ, rfl⟩,
    fun h => (QuadFormsKB.ChenevierLannes.classSet_nonempty_iff.2 h).elim fun _ ⟨Q, hQ, _⟩ => ⟨Q, hQ⟩⟩,
    QuadFormsKB.ChenevierLannes.classSet_finite n⟩

end EvenUnimodular

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


end QuadFormsKB.Headlines
