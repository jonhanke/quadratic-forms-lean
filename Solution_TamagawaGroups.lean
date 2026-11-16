/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GLnTamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.Sp2Tamagawa

/-!
# Headline statements, proved: Tamagawa numbers of SL_n, GL_n and Sp_2

The declarations of `Challenge_TamagawaGroups.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/TamagawaGroups.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_TamagawaGroups.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

/-! ## The Tamagawa number of the special linear group

A. Weil (1982): τ(SL_n) = 1 over every number field, with Weil's Tamagawa measure on SL_n(𝔸_F) built by induction
on n from the self-dual additive measures. -/

section TamagawaSLn

/-- **τ(SL_n) = 1 over every number field** (A. Weil, *Adeles and Algebraic Groups*, Progress in Mathematics 23, Birkhäuser, 1982, Chapter III, with §2.4, Theorem 2.4.3 for the
measure; proved here by induction on n with Siegel's mean value theorem and the adelic Poisson summation formula).
Let F be a number field, n = k + 1 ≥ 1 and 𝔸_F the adele ring of F. SL_n(F) acts on SL_n(𝔸_F)
(`Tamagawa.Measure.Weil.SLn.SLnA F (Fin n)`) by right multiplication through the diagonal embedding. For the
Tamagawa measure `Tamagawa.Measure.Weil.SLn.muSL F k` of SL_n(𝔸_F) (Weil's fibration measure
ω_{SL_n} = dy ∧ ω_{SL_{n−1}} ∧ dc for the fibration of SL_n over the nonzero vectors of 𝔸_F^n, with the
self-dual additive Haar measures; the point mass on SL_1(𝔸_F) = {1}), the quotient SL_n(F)\SL_n(𝔸_F) has a
measurable fundamental domain, the measure is left invariant, and the covolume is 1. -/
theorem tamagawa_SLn {F : Type} [Field F] [NumberField F] (k : ℕ) :
    MeasureTheory.covolume (Matrix.SpecialLinearGroup (Fin (k + 1)) F)
        (Tamagawa.Measure.Weil.SLn.SLnA F (Fin (k + 1))) (Tamagawa.Measure.Weil.SLn.muSL F k) = 1 ∧
      MeasureTheory.HasFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 1)) F)
        (Tamagawa.Measure.Weil.SLn.SLnA F (Fin (k + 1))) (Tamagawa.Measure.Weil.SLn.muSL F k) ∧
      (Tamagawa.Measure.Weil.SLn.muSL F k).IsMulLeftInvariant :=
  ⟨QuadFormsKB.Tamagawa.Measure.Weil.SLn.tamagawa_SLn k, inferInstance, inferInstance⟩

end TamagawaSLn

/-! ## The Tamagawa numbers of GL_n and Sp_2 (new in 0.6.0)

A. Weil (1982): τ(GL_n) = 1 with Weil's convergence factors, and τ(Sp_2) = 1, over every number field. -/

section TamagawaGLnSp2

theorem tamagawa_GLn {F : Type} [Field F] [NumberField F] (k : ℕ) :
    MeasureTheory.covolume (Tamagawa.Measure.Weil.GLn.GammaGL F k) (Tamagawa.Measure.Weil.GLn.GLOne F k)
      (Tamagawa.Measure.Weil.GLn.muGL F k) = 1 :=
  QuadFormsKB.Tamagawa.Measure.Weil.GLn.tamagawa_GLn k

theorem tamagawa_Sp2 {F : Type} [Field F] [NumberField F] :
    MeasureTheory.covolume (Matrix.symplecticGroup (Fin 1) F) (Tamagawa.Measure.Weil.Sp2A F)
      (Tamagawa.Measure.Weil.muSp2 F) = 1 :=
  QuadFormsKB.Tamagawa.Measure.Weil.tamagawa_Sp2

end TamagawaGLnSp2

end QuadFormsKB.Headlines
