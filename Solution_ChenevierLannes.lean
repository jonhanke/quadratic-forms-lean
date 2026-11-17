/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ChenevierLannes.HeckeCommute060
import QuadFormsKB.Literature.ChenevierLannes.Venkov060.HarmonicTheta
import QuadFormsKB.Literature.ChenevierLannes.WittIgusa060

/-!
# Headline statements, proved: G. Chenevier and J. Lannes, Automorphic Forms and Even Unimodular Lattices

The declarations of `Challenge_ChenevierLannes.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/ChenevierLannes.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_ChenevierLannes.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
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
      {c | ∃ Q : QuadForm ℤ n, ChenevierLannes.IsEvenUnimodular Q ∧ Siegel.classOf Q = c}.Finite :=
  ⟨⟨fun ⟨Q, hQ⟩ => QuadFormsKB.ChenevierLannes.classSet_nonempty_iff.1 ⟨_, Q, hQ, rfl⟩,
    fun h => (QuadFormsKB.ChenevierLannes.classSet_nonempty_iff.2 h).elim fun _ ⟨Q, hQ, _⟩ => ⟨Q, hQ⟩⟩,
    QuadFormsKB.ChenevierLannes.classSet_finite n⟩

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
      Nat.card (Siegel.Aut Lattices.gamma16) = 2 ^ 15 * Nat.factorial 16 :=
  ⟨QuadFormsKB.ChenevierLannes.wittRankSixteen,
    fun h => QuadFormsKB.Lattices.gamma16_not_isometric
      (Siegel.IsometricGL.symm (Siegel.classOf_eq_classOf_iff.mp h)),
    by rw [QuadFormsKB.ChenevierLannes.card_aut_twoE8, QuadFormsKB.ChenevierLannes.card_aut_e8_eq],
    QuadFormsKB.ChenevierLannes.card_aut_gamma16⟩

end EvenUnimodularSixteen

/-! ## Siegel theta series, Venkov's root sums and Hecke operators (new in 0.6.0)

G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices* (2019): the Siegel theta series of an
even unimodular lattice is a Siegel modular form (§5.1), Venkov's root sums in dimensions 8, 16 and 24
(Proposition 2.3.2), and the Kneser–Hecke operators T_p commute (§1.3). -/

section ThetaHecke

theorem siegelTheta_modular {n : ℕ} (Q : QuadForm ℤ n) (hQ : ChenevierLannes.IsEvenUnimodular Q) (g : ℕ) :
    ChenevierLannes.IsSiegelModularForm ((n / 2 : ℕ) : ℤ) g (ChenevierLannes.siegelTheta g Q) :=
  QuadFormsKB.ChenevierLannes.siegelThetaModular_of_evenUnimodular Q hQ g

theorem venkov_rootSum {n : ℕ} (hn : n = 8 ∨ n = 16 ∨ n = 24) (Q : QuadForm ℤ n)
    (hQ : ChenevierLannes.IsEvenUnimodular Q) (x : Fin n → ℝ) :
    (ChenevierLannes.rootSet Q).Finite ∧
      ∑ᶠ α ∈ ChenevierLannes.rootSet Q, ChenevierLannes.latDot Q α x ^ 2 =
        2 * ((ChenevierLannes.rootSet Q).ncard : ℝ) / n * (2 * Q.evalIn ℝ x) := by
  refine ⟨QuadFormsKB.ChenevierLannes.rootSet_finite hQ.posDef, ?_⟩
  rcases hn with rfl | rfl | rfl
  · exact QuadFormsKB.ChenevierLannes.venkovRootSum_eight.root_sum Q hQ x
  · exact QuadFormsKB.ChenevierLannes.venkovRootSum_sixteen.root_sum Q hQ x
  · exact QuadFormsKB.ChenevierLannes.venkovRootSum_twentyFour.root_sum Q hQ x

theorem heckeT_comm (n p q : ℕ) [Fact p.Prime] [Fact q.Prime] (f : Siegel.QClass n → ℂ)
    {x : Siegel.QClass n} (hx : x ∈ ChenevierLannes.classSet n) :
    ChenevierLannes.heckeT p (ChenevierLannes.heckeT q f) x =
      ChenevierLannes.heckeT q (ChenevierLannes.heckeT p f) x :=
  QuadFormsKB.ChenevierLannes.heckeCommute n p q f x hx

end ThetaHecke

/-! ## Conditional: the identity of Witt and Igusa in genus g ≤ 3 (new in 0.6.0)

Conditional on one named input: there are no nonzero Siegel cusp forms of weight 8 in genus 2 and 3
(`ChenevierLannes.CuspFormsWeightEightVanish`; Igusa 1962, Tsuyumine 1986), not yet proved here. -/

section WittIgusaConditional

theorem wittIgusa_of_cuspVanish (h : ChenevierLannes.CuspFormsWeightEightVanish) : ChenevierLannes.WittIgusa :=
  QuadFormsKB.ChenevierLannes.wittIgusa_of_cuspVanish h

end WittIgusaConditional

end QuadFormsKB.Headlines
