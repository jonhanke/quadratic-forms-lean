/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ChenevierLannes.HeckeCommute060
import QuadFormsKB.Literature.ChenevierLannes.Venkov060.HarmonicTheta
import QuadFormsKB.Literature.ChenevierLannes.WittIgusa060

/-!
# Headline statements: G. Chenevier and J. Lannes, Automorphic Forms and Even Unimodular Lattices

Even unimodular lattices, their Siegel theta series, Venkov's root sums and the Kneser–Hecke operators (and, conditionally, the identity of Witt and Igusa).

Every proof here is a deliberate `sorry`. `Solution_ChenevierLannes.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/ChenevierLannes.json`) checks that each theorem of
`Solution_ChenevierLannes.lean` has exactly the statement given here and depends only on the axioms `propext`,
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
      {c | ∃ Q : QuadForm ℤ n, ChenevierLannes.IsEvenUnimodular Q ∧ Siegel.classOf Q = c}.Finite := by
  sorry

end EvenUnimodular

/-! ## Even unimodular lattices of dimension 16

G. Chenevier and J. Lannes (2019), Corollary 2.3.6 (Witt): E₈ ⊕ E₈ and E₁₆ are, up to isomorphism, the only
positive definite even unimodular lattices of dimension 16. -/

section EvenUnimodularSixteen

/-- **Witt's classification of even unimodular lattices of dimension 16** (G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices*, Ergebnisse der Mathematik und ihrer Grenzgebiete (3. Folge) 69, Springer, 2019, Corollary 2.3.6,
p. 36, and §3.3.1, pp. 57–58; E. Witt, 1941). With `ChenevierLannes.IsEvenUnimodular` and `Siegel.classOf` as in
`evenUnimodular_classes`, the set X₁₆ of classes of even unimodular forms in 16 variables is
{[E₈ ⊕ E₈], [E₁₆]}: `Lattices.twoE8` is the orthogonal sum of two copies of the E₈ form `Lattices.e8`, and
`Lattices.gamma16` is E₁₆ = D₁₆⁺ (Cassels' Γ₁₆). The two classes are different, and the automorphism groups
(`Siegel.Aut`, in GL₁₆(ℤ)) have orders |O(E₈ ⊕ E₈)| = 2 · 696729600² and |O(E₁₆)| = 2¹⁵ · 16!. -/
theorem witt_evenUnimodular_sixteen :
    {c | ∃ Q : QuadForm ℤ 16, ChenevierLannes.IsEvenUnimodular Q ∧ Siegel.classOf Q = c} =
        {Siegel.classOf Lattices.twoE8, Siegel.classOf Lattices.gamma16} ∧
      Siegel.classOf Lattices.twoE8 ≠ Siegel.classOf Lattices.gamma16 ∧
      Nat.card (Siegel.Aut Lattices.twoE8) = 2 * 696729600 ^ 2 ∧
      Nat.card (Siegel.Aut Lattices.gamma16) = 2 ^ 15 * Nat.factorial 16 := by
  sorry

end EvenUnimodularSixteen

/-! ## Siegel theta series, Venkov's root sums and Hecke operators (new in 0.6.0)

G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices* (2019): the Siegel theta series of an
even unimodular lattice is a Siegel modular form (§5.1), Venkov's root sums in dimensions 8, 16 and 24
(Proposition 2.3.2), and the Kneser–Hecke operators T_p commute (§1.3). -/

section ThetaHecke

/-- **Siegel theta series of even unimodular lattices are Siegel modular forms** (Chenevier–Lannes, §5.1, p. 123,
citing Freitag). Let Q be an even unimodular positive definite quadratic form over ℤ in n variables
(`ChenevierLannes.IsEvenUnimodular`) and g ≥ 0. The Siegel theta series of genus g,
ϑ_g(Q)(Z) = ∑_{X ∈ M_{n×g}(ℤ)} exp(π i tr(Xᵀ H X Z)) (`ChenevierLannes.siegelTheta g Q`, H the Hessian matrix of
Q), is a Siegel modular form of weight n/2 for Sp_2g(ℤ) (`ChenevierLannes.IsSiegelModularForm`: holomorphic on the
Siegel upper half space, the transformation law f(γZ) = det(CZ + D)^{n/2} f(Z) for every γ ∈ Sp_2g(ℤ), and bounded
on Im Z ≥ 1). -/
theorem siegelTheta_modular {n : ℕ} (Q : QuadForm ℤ n) (hQ : ChenevierLannes.IsEvenUnimodular Q) (g : ℕ) :
    ChenevierLannes.IsSiegelModularForm ((n / 2 : ℕ) : ℤ) g (ChenevierLannes.siegelTheta g Q) := by
  sorry

/-- **Venkov's root sums in dimensions 8, 16 and 24** (Chenevier–Lannes, Proposition 2.3.2, after B. Venkov). Let
Q be an even unimodular positive definite quadratic form over ℤ in n ∈ {8, 16, 24} variables and R(Q) its set of
roots, the α ∈ ℤⁿ with Q(α) = 1 (`ChenevierLannes.rootSet`; norm 2 for the bilinear form). Then R(Q) is finite and
for every x ∈ ℝⁿ, ∑_{α ∈ R(Q)} (α · x)² = (2 |R(Q)| / n) · 2Q(x), where α · x is the bilinear form of Q
(`ChenevierLannes.latDot`). The proof shows that the theta series with the harmonic polynomial (α · x)² − (|α|²/n)|x|²
is a cusp form of weight n/2 + 2 ∈ {6, 10, 14} for SL_2(ℤ), hence 0. -/
theorem venkov_rootSum {n : ℕ} (hn : n = 8 ∨ n = 16 ∨ n = 24) (Q : QuadForm ℤ n)
    (hQ : ChenevierLannes.IsEvenUnimodular Q) (x : Fin n → ℝ) :
    (ChenevierLannes.rootSet Q).Finite ∧
      ∑ᶠ α ∈ ChenevierLannes.rootSet Q, ChenevierLannes.latDot Q α x ^ 2 =
        2 * ((ChenevierLannes.rootSet Q).ncard : ℝ) / n * (2 * Q.evalIn ℝ x) := by
  sorry

/-- **The Kneser–Hecke operators commute** (Chenevier–Lannes, §1.3, p. 6, and §3.2, p. 55; every rank n and all
primes p, q, including 2). On the functions f : X_n → ℂ on the classes of even unimodular lattices of rank n
(`Siegel.QClass n`, the classes in `ChenevierLannes.classSet n`), T_p f(x) = ∑_{y} N_p(x, y) f(y), with N_p(x, y)
the number of p-neighbours of a lattice of class x that have class y (`ChenevierLannes.heckeT p`). Then
T_p(T_q f)(x) = T_q(T_p f)(x) for every class x ∈ X_n. -/
theorem heckeT_comm (n p q : ℕ) [Fact p.Prime] [Fact q.Prime] (f : Siegel.QClass n → ℂ)
    {x : Siegel.QClass n} (hx : x ∈ ChenevierLannes.classSet n) :
    ChenevierLannes.heckeT p (ChenevierLannes.heckeT q f) x =
      ChenevierLannes.heckeT q (ChenevierLannes.heckeT p f) x := by
  sorry

end ThetaHecke

/-! ## Conditional: the identity of Witt and Igusa in genus g ≤ 3 (new in 0.6.0)

Conditional on one named input: there are no nonzero Siegel cusp forms of weight 8 in genus 2 and 3
(`ChenevierLannes.CuspFormsWeightEightVanish`; Igusa 1962, Tsuyumine 1986), not yet proved here. -/

section WittIgusaConditional

/-- **Witt and Igusa: ϑ_g(E_8 ⊕ E_8) = ϑ_g(E_16) for g ≤ 3, conditional on the vanishing of the Siegel cusp forms of
weight 8 in genus 2 and 3** (Chenevier–Lannes, (1.3.2) and §5.2). The hypothesis
`ChenevierLannes.CuspFormsWeightEightVanish` (a named input, not proved here; J. Igusa 1962 for genus 2,
S. Tsuyumine 1986 for genus 3) states that every Siegel cusp form of weight 8 and genus 2 or 3
(`ChenevierLannes.IsSiegelCuspForm`) vanishes on the Siegel upper half space. The conclusion
`ChenevierLannes.WittIgusa` states: for g ≤ 3 and every Z in the Siegel upper half space of genus g,
ϑ_g(E_8 ⊕ E_8)(Z) = ϑ_g(E_16)(Z) (`ChenevierLannes.siegelTheta`, with `twoE8` and `gamma16` the forms of
E_8 ⊕ E_8 and E_16 = D_16^+). -/
theorem wittIgusa_of_cuspVanish (h : ChenevierLannes.CuspFormsWeightEightVanish) : ChenevierLannes.WittIgusa := by
  sorry

end WittIgusaConditional

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.
* `QuadForm.evalIn`, `QuadForm.eval` (Defs/QuadForm.lean): the value Q(x) for x ∈ K^n, K an R-algebra (resp. K = R).

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).

Lattices and sums of squares (new in 0.5.0)
* `ChenevierLannes.IsEvenUnimodular Q`: Q positive definite with Gram matrix (the Hessian) of determinant 1;
  `Siegel.classOf Q`: the GL_n(ℤ)-class of Q.

New in 0.5.1
* `Lattices.e8`, `Lattices.twoE8`, `Lattices.gamma16` (Literature/Cassels/AppA/): the forms of E₈, E₈ ⊕ E₈ and
  E₁₆ = Γ₁₆ (Cassels, Appendix A); `Siegel.Aut Q` (Siegel/Genus.lean): the matrices of GL_n(ℤ) preserving Q.
-/

end QuadFormsKB.Headlines
