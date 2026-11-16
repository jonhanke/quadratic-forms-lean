/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Literature.Hanke2005.GHYConductorDyadic
import QuadFormsKB.Tamagawa.Indefinite.DCFinite

/-!
# Headline statements, proved: Exact mass formulas

The declarations of `Challenge_ExactMass.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/ExactMass.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_ExactMass.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
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

end QuadFormsKB.Headlines
