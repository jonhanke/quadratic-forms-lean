/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.SiegelWeil.RatModular

/-!
# Headline statements: The Siegel–Weil formula over ℚ

The genus theta series of a positive definite form over ℤ in an even number of variables is the Eisenstein series of the genus, in Mathlib's modular forms.

Every proof here is a deliberate `sorry`. `Solution_SiegelWeil.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/SiegelWeil.json`) checks that each theorem of
`Solution_SiegelWeil.lean` has exactly the statement given here and depends only on the axioms `propext`,
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

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

/-! ## The Siegel–Weil formula over ℚ (new in 0.6.0)

C. L. Siegel (1935), in the language of Mathlib's modular forms: the genus theta series of a positive definite
integral quadratic form in an even number n ≥ 4 of variables is a modular form of weight n/2 for Γ₁(N) with the
theta character on Γ₀(N), and it equals the Eisenstein series of the genus, whose Fourier coefficients are Siegel's
products of local densities. -/

section SiegelWeilRat

open scoped ModularForm in
/-- **The Siegel–Weil formula over ℚ** (C. L. Siegel, "Über die analytische Theorie der quadratischen Formen", Ann.
of Math. 36 (1935), Hauptsatz, as an identity of modular forms; J. Hanke, "Some recent results about (ternary)
quadratic forms", CRM Proceedings 36 (2004), (5.3), p. 368). Let Q be a positive definite quadratic form over ℤ
(`IntQF.PosDef`) in n = 2k variables, k ≥ 2, with Hessian matrix H and N = |det H|. Then there is a modular form g
of weight k for Γ₁(N) (Mathlib's `ModularForm (CongruenceSubgroup.Gamma1 N) k`) such that
1. g(τ) = Θ_Gen(Q)(τ) for every τ in the upper half plane, where Θ_Gen(Q) (`Siegel.thetaGen Q`) is the genus theta
   series Mass(Q)⁻¹ ∑_{Q'} θ_{Q'}/|O(Q')|, the sum over the classes Q' in the genus of Q;
2. g transforms under Γ₀(N) with the theta character: g |_k γ = χ_Q(d) g for γ ∈ Γ₀(N) with lower right entry d
   (`Siegel.thetaChi Q k N d`, the Jacobi symbol of the discriminant of Q at d);
3. g is the Eisenstein series of the genus: its q-expansion (Mathlib's `qExpansion` with period 1) has constant
   term 1 and m-th coefficient a_E(m) (`Siegel.aE Q m`) = β_∞(m) ∏_p β_p(m), Siegel's product of the real density
   and the local densities of Q at m, for every m ≥ 1. -/
theorem siegelWeil_rat {n k : ℕ} (Q : IntQF n) (hQ : Q.PosDef) (hn : n = 2 * k) (hk : 2 ≤ k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma1 Q.hessian.det.natAbs) k,
      (∀ τ : UpperHalfPlane, g τ = Siegel.thetaGen Q τ) ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma0 Q.hessian.det.natAbs,
        (⇑g) ∣[(k : ℤ)] γ = (Siegel.thetaChi Q k Q.hessian.det.natAbs (γ 1 1) : ℂ) • ⇑g) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ m : ℕ, 1 ≤ m → (UpperHalfPlane.qExpansion 1 g).coeff m = (Siegel.aE Q m : ℂ) := by
  sorry

end SiegelWeilRat

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm.hessian` (Defs/QuadForm.lean): the Hessian matrix H = C + Cᵀ, so Q(x) = (1/2) xᵀ H x.

Classical cases over ℚ
* `IntQF.PosDef Q` (Literature/Universal/Basic.lean): Q(x) > 0 for every nonzero x ∈ ℤ^n.

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).
-/

end QuadFormsKB.Headlines
