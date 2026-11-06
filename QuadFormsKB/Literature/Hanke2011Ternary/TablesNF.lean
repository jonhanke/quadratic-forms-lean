/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Ternary.OddNF
import QuadFormsKB.Literature.Hanke2011Ternary.DyadicNF
import QuadFormsKB.Literature.Hanke2011Structure.TernaryNF

/-!
# Paper 7's local tables over a number field in which $2$ splits completely; Theorem 8.1 unconditional

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), §2 (Theorem 2.4, Table 2), §5 (Table 5.3), §8 (Theorem 8.1, p. 27).

The named input `Hanke2011Structure.TernaryLocalTablesNF F` (paper 7's Tables 2 and 5.3 for the true ternary local
genera over the completions $F_{\mathfrak p}$) is **proved** for every number field $F$ in which $2$ splits completely
(`ternaryLocalTablesNF_of_twoSplits`):

* at $\mathfrak p \nmid 2$, from the classification of the local genera over the nondyadic local field $F_{\mathfrak p}$
  and their densities (`OddNF.oddNF_finite`, `oddNF_A`, `oddNF_B`, `oddNF_unimod`);
* at $\mathfrak p \mid 2$, where $F_{\mathfrak p} \cong \mathbb Q_2$, by transport of the proved $\mathbb Q_2$ tables
  (`dyNF_finite`, `dyNF_zero`, `dyNF_A`, `dyNF_B`).

Consequently Theorem 8.1 (primitive formula, coefficientwise) holds unconditionally for every totally real $F$ in which
$2$ splits completely (`theorem_8_1_primitive`).
-/

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Hanke2011Ternary QuadFormsKB.Hanke2011Ternary.NF QuadFormsKB.NFEuler

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-- **Paper 7's local tables hold over every number field in which $2$ splits completely**: the named input
`TernaryLocalTablesNF F` (Table 2 at $\mathfrak p \nmid 2$ with $q = N\mathfrak p$, Table 5.3 at $\mathfrak p \mid 2$ with
$F_{\mathfrak p} = \mathbb Q_2$, for the true ternary local genera) is a theorem.  Unconditional. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7; §5, Table 5.3, pp. 20-21 (over F_p, 2 split completely in F)"]
theorem ternaryLocalTablesNF_of_twoSplits (hs : TwoSplitsCompletely F) : TernaryLocalTablesNF F where
  fin v S c := by
    by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
    · exact dyNF_finite (hs.isQ2Prime v h2) S c
    · exact OddNF.oddNF_finite h2 S c
  odd_A v h2 S hS := OddNF.oddNF_A h2 S hS
  odd_B v h2 S hS := OddNF.oddNF_B h2 S hS
  odd_unimod v h2 S hS := OddNF.oddNF_unimod h2 S hS
  dy_zero _ v h2 S hS c := dyNF_zero (hs.isQ2Prime v h2) S hS c
  dy_A _ v h2 S hS := dyNF_A (hs.isQ2Prime v h2) S hS
  dy_B _ v h2 S hS x hx := dyNF_B (hs.isQ2Prime v h2) S hS x hx

/-- **Theorem 8.1, primitive formula, coefficientwise, unconditional** (Hanke 2011, ternary paper, p. 27): for a totally
real number field $F$ in which $2$ splits completely, the totally positive definite signature, and $\lambda(\mathfrak a)$
globally rational with a totally positive representative $\alpha$, the total mass of the primitive $\mathcal O_F$-valued
ternary lattices of Hessian determinant squareclass $\lambda(\mathfrak a)$ is
$$\frac{|\Delta_F|^{3/2}}{(64\pi^2)^{[F:\mathbb Q]}}\,N(\mathfrak a)^2\cdot\frac{4^{[F:\mathbb Q]}\zeta_F(2)}{2}
\Bigl([\mathfrak a^{-s}]\frac{\zeta_F(s+1)\zeta_F(2s+3)}{N(2\mathcal O_F)^s\zeta_F(3s+6)} +
(-1)^{[F:\mathbb Q]}[\mathfrak a^{-s}]\frac{\zeta_F(2s+2)\zeta_F(s+2)}{N(2\mathcal O_F)^s\zeta_F(3s+6)}\Bigr),$$
the coefficient of $N(\mathfrak a)^{-s}$ in the paper's formula (see `theorem_8_1_coeff`, of which this is the case with
the named input discharged by `ternaryLocalTablesNF_of_twoSplits`). -/
@[kb "hanke2011ternary" "§8, Thm. 8.1, p. 27 (primitive formula, coefficientwise, unconditional; F totally real, 2 split)"]
theorem theorem_8_1_primitive [IsTotallyReal F] (hs : TwoSplitsCompletely F)
    (lam : DistinguishedFamily F) (a : (Ideal (𝓞 F))⁰) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v (lam.toHom a)) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal}, IsSquare (algebraMap F w.1.Completion (α : F))) :
    ∑ᶠ t ∈ GenStar (lam.toHom a) (totPosSig F 3) ∅ (fun _ => 1),
        massOfTuple (lam.toHom a) (totPosSig F 3) ∅ (fun _ => 1) t =
      |(discr F : ℝ)| ^ ((3 : ℝ) / 2) / (64 * Real.pi ^ 2) ^ Module.finrank ℚ F *
        (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ 2 *
        (4 ^ Module.finrank ℚ F * dedekindZetaR F 2 / 2) *
        ((eulerCoeff EA a + (-1) ^ Module.finrank ℚ F * eulerCoeff EB a : ℚ) : ℝ) :=
  theorem_8_1_coeff (ternaryLocalTablesNF_of_twoSplits hs) hs lam a α hα hsign

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.ternaryLocalTablesNF_of_twoSplits
#print axioms QuadFormsKB.Hanke2011Structure.theorem_8_1_primitive
