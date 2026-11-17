/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.SiegelWeil.RatModular

/-!
# Headline statements, proved: The Siegel–Weil formula over ℚ

The declarations of `Challenge_SiegelWeil.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/SiegelWeil.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_SiegelWeil.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

/-! ## The Siegel–Weil formula over ℚ (new in 0.6.0)

C. L. Siegel (1935), in the language of Mathlib's modular forms: the genus theta series of a positive definite
integral quadratic form in an even number n ≥ 4 of variables is a modular form of weight n/2 for Γ₁(N) with the
theta character on Γ₀(N), and it equals the Eisenstein series of the genus, whose Fourier coefficients are Siegel's
products of local densities. -/

section SiegelWeilRat

open scoped ModularForm in
theorem siegelWeil_rat {n k : ℕ} (Q : IntQF n) (hQ : Q.PosDef) (hn : n = 2 * k) (hk : 2 ≤ k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma1 Q.hessian.det.natAbs) k,
      (∀ τ : UpperHalfPlane, g τ = Siegel.thetaGen Q τ) ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma0 Q.hessian.det.natAbs,
        (⇑g) ∣[(k : ℤ)] γ = (Siegel.thetaChi Q k Q.hessian.det.natAbs (γ 1 1) : ℂ) • ⇑g) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ m : ℕ, 1 ≤ m → (UpperHalfPlane.qExpansion 1 g).coeff m = (Siegel.aE Q m : ℂ) :=
  QuadFormsKB.Siegel.GenusEis.siegelWeil_rat hQ hn hk

end SiegelWeilRat

end QuadFormsKB.Headlines
