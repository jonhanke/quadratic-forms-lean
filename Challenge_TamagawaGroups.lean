/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GLnTamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.Sp2Tamagawa

/-!
# Headline statements: Tamagawa numbers of SL_n, GL_n and Sp_2

τ(SL_n) = 1, τ(GL_n) = 1 and τ(Sp_2) = 1 over every number field (Weil).

Every proof here is a deliberate `sorry`. `Solution_TamagawaGroups.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/TamagawaGroups.json`) checks that each theorem of
`Solution_TamagawaGroups.lean` has exactly the statement given here and depends only on the axioms `propext`,
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
      (Tamagawa.Measure.Weil.SLn.muSL F k).IsMulLeftInvariant := by
  sorry

end TamagawaSLn

/-! ## The Tamagawa numbers of GL_n and Sp_2 (new in 0.6.0)

A. Weil (1982): τ(GL_n) = 1 with Weil's convergence factors, and τ(Sp_2) = 1, over every number field. -/

section TamagawaGLnSp2

/-- **τ(GL_n) = 1 over every number field** (A. Weil, *Adeles and Algebraic Groups*, Progress in Mathematics 23,
Birkhäuser, 1982, §2.4, Theorem 2.4.4 and Chapter III: τ(GL_n) = τ(SL_n) τ(G_m) = 1). Let F be a number field,
n = k + 1 ≥ 1 and 𝔸_F the adele ring of F. GL_n(𝔸_F)^1 = {g : ‖det g‖_𝔸 = 1}
(`Tamagawa.Measure.Weil.GLn.GLOne F k`) contains GL_n(F) diagonally (`GLn.GammaGL F k`, by the product formula),
which acts on it by multiplication. The Tamagawa measure `GLn.muGL F k` of GL_n(𝔸_F)^1 is Weil's measure with the
convergence factors λ_v = 1 − q_v^{−1} and the global factor ρ_F^{−1}, ρ_F the residue of the Dedekind zeta
function ζ_F at s = 1: ρ_F^{−1} times the fibre measure of det : GL_n(𝔸_F)^1 → 𝔸_F^{×,1} over the measure of the
norm-one ideles, with the Tamagawa measure of SL_n(𝔸_F) (as in `tamagawa_SLn`) on the fibres. The covolume of
GL_n(F) in GL_n(𝔸_F)^1 is 1 (in particular the quotient has a measurable fundamental domain: Mathlib's `covolume`
is 0 otherwise). -/
theorem tamagawa_GLn {F : Type} [Field F] [NumberField F] (k : ℕ) :
    MeasureTheory.covolume (Tamagawa.Measure.Weil.GLn.GammaGL F k) (Tamagawa.Measure.Weil.GLn.GLOne F k)
      (Tamagawa.Measure.Weil.GLn.muGL F k) = 1 := by
  sorry

/-- **τ(Sp_2) = 1 over every number field** (A. Weil, *Adeles and Algebraic Groups*, 1982, the case n = 1 of
τ(Sp_2n) = 1). Sp_2(𝔸_F) (`Tamagawa.Measure.Weil.Sp2A F`, Mathlib's `Matrix.symplecticGroup (Fin 1)` over the adele
ring) contains Sp_2(F), acting by right multiplication; its Tamagawa measure `Tamagawa.Measure.Weil.muSp2 F` is the
Tamagawa measure of SL_2(𝔸_F) transported along the identification Sp_2 = SL_2 (defined over ℤ, so it matches the
gauge forms and the local measures at every place). The covolume is 1. This is τ(SL_2) = 1 for the group Sp_2. -/
theorem tamagawa_Sp2 {F : Type} [Field F] [NumberField F] :
    MeasureTheory.covolume (Matrix.symplecticGroup (Fin 1) F) (Tamagawa.Measure.Weil.Sp2A F)
      (Tamagawa.Measure.Weil.muSp2 F) = 1 := by
  sorry

end TamagawaGLnSp2

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

New in 0.5.1
* `Tamagawa.Measure.Weil.SLn.SLnA F ι` (Tamagawa/Measure/Weil/SLnAdele.lean): SL_ι(𝔸_F) with 𝔸_F = `Adeles F`
  (Tamagawa/Measure/Weil/AdditiveAdele.lean: the product of `mixedSpace F` and the finite adeles); SL_ι(F) acts by
  right multiplication through the diagonal embedding (`slnRightAction`, same file).
* `Tamagawa.Measure.Weil.SLn.muSL F k` (Tamagawa/Measure/Weil/SLnInduct.lean): Weil's Tamagawa measure on
  SL_{k+1}(𝔸_F), by induction on k (point mass for k = 0; the fibration measure over the nonzero vectors otherwise).
-/

end QuadFormsKB.Headlines
