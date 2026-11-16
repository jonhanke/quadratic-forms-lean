/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.HeadlineFacts
import QuadFormsKB.Tamagawa.InputsFollowup

/-!
# Headline statements, proved: The Tamagawa number and the mass formula over totally real number fields

The declarations of `Challenge_TamagawaTotallyReal.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/TamagawaTotallyReal.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_TamagawaTotallyReal.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

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

end QuadFormsKB.Headlines
