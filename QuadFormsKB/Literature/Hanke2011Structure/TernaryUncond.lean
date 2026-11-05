/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.TernaryFinal
import QuadFormsKB.Literature.Hanke2011Structure.TernaryRational
import QuadFormsKB.Tamagawa.Dyadic7CountMain

/-!
# Paper 7 over $\mathbb Q$, unconditional

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), and *The structure of masses of rank n quadratic lattices of varying determinant
over number fields*, arXiv:1108.3580 (`hanke2011structure`).

With the 2-adic count proved (`Dyadic7.ternaryDyadicMassCount_holds`), paper 7's three inputs and its main results over
$\mathbb Q$ hold without hypotheses:

* `ternaryLocalMassFormula_holds`: $M^*_{1;3}(N) = 2\zeta(2)(A^*_3(N) + B^*_3(N))$ for the true local genera
  (paper 6, Thm. 4.8 over $\mathbb Q$, $n = 3$);
* `ternaryGenusDensityFormula_holds`: the same, summed over the primitive positive definite ternary genera;
* `primitiveMassLocalFormula_holds`: paper 7's input for Cor. 8.2;
* `cor82_holds` (Cor. 8.2, both identities), `theorem_1_1_holds` (Thm. 1.1, the divisor sum);
* `theorem_5_4_two_A_holds`, `theorem_5_4_two_B_holds`: paper 6, Thm. 5.4 at $p = 2$ for $n = 3$ over $\mathbb Q$
  (paper 7, Lemmas 6.1–6.2) for the true local genera.
-/

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Dyadic7 IsDedekindDomain NumberField PowerSeries QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane Cassels

/-- **Paper 6's local input over $\mathbb Q$ for $n = 3$**, unconditional:
$M^*_{1;3}(N) = 2\zeta(2)(A^*_3(N) + B^*_3(N))$ for every $N \ge 1$. -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, Rem. 4.14, p. 20; hanke2011ternary §§2–5, Thm. 4.12 (F = Q, n = 3)"]
theorem ternaryLocalMassFormula_holds : TernaryLocalMassFormula :=
  ternaryLocalMassFormula_of_dyadic dyadicTernaryLocalMassTable_holds

/-- **The named input `TernaryGenusDensityFormula` holds** (unconditional). -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17; Lemma 3.7, p. 13 (F = Q, n = 3)"]
theorem ternaryGenusDensityFormula_holds : TernaryGenusDensityFormula :=
  ternaryGenusDensityFormula_of_local ternaryLocalMassFormula_holds

/-- **Paper 7's named input `PrimitiveMassLocalFormula` holds** (unconditional). -/
@[kb "hanke2011ternary" "§8, proof of Cor. 8.2 (input), via paper 6 Thm. 4.8, Lemma 3.7, Cor. 6.3–6.4"]
theorem primitiveMassLocalFormula_holds : Hanke2011Ternary.PrimitiveMassLocalFormula :=
  primitiveMassLocalFormula_of_local ternaryLocalMassFormula_holds

/-- **Paper 7, Corollary 8.2** (both identities), unconditional:
$D_{\mathrm{Mass}^*;3}(s) = \frac{1}{48\cdot2^s}\frac{\zeta(s-1)\zeta(2s-1)-\zeta(2s-2)\zeta(s)}{\zeta(3s)}$ and
$D_{\mathrm{Mass};3}(s) = \frac{1}{48\cdot2^s}[\zeta(s-1)\zeta(2s-1)-\zeta(2s-2)\zeta(s)]$. -/
@[kb "hanke2011ternary" "§8, Cor. 8.2, pp. 27–28"]
theorem cor82_holds : Hanke2011Ternary.Cor82 :=
  Hanke2011Ternary.cor82_of_input primitiveMassLocalFormula_holds

/-- **Paper 7, Theorem 1.1**, unconditional: for every $m \ge 1$,
$\mathrm{TMass}_3(2m) = \frac1{48}\sum_{m = ab^2}(ab - b^2)$, and $\mathrm{TMass}_3(N) = 0$ for odd $N$. -/
@[kb "hanke2011ternary" "§1, Thm. 1.1, p. 2"]
theorem theorem_1_1_holds :
    (∀ m : ℕ, m ≠ 0 → Hanke2011Ternary.TMass3 (2 * m) = (1 / 48) *
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m),
        ((ab.1 : ℚ) * ab.2 - (ab.2 : ℚ) ^ 2)) ∧
    (∀ N : ℕ, ¬ 2 ∣ N → Hanke2011Ternary.TMass3 N = 0) :=
  Hanke2011Ternary.theorem_1_1 primitiveMassLocalFormula_holds

/-- **Paper 6, Theorem 5.4 at $p = 2$ ($n = 3$, $F = \mathbb Q$), the $A^*$ series, unconditional** (paper 7,
Lemma 6.1): $\sum_h A^*_2(2^hu)X^h = X(1 - X^3/64)/((1 - X/2)(1 - X^2/8))$ for the true local genera. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (n = 3, F_p = Q_2); hanke2011ternary Lemma 6.1, p. 22"]
theorem theorem_5_4_two_A_holds {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ}
    (hu : u ∈ sqUnits) :
    PowerSeries.mk (fun h => trueA2 v u (zSqCl v (2 ^ h * u))) *
        ((1 - C (1 / 2 : ℝ) * X) * (1 - C (1 / 8 : ℝ) * X ^ 2)) = X * (1 - C (1 / 64 : ℝ) * X ^ 3) :=
  theorem_5_4_two_A dyadicTernaryLocalMassTable_holds h2 hu

/-- **Paper 6, Theorem 5.4 at $p = 2$ ($n = 3$, $F = \mathbb Q$), the $B^*$ series, unconditional** (paper 7,
Lemma 6.2): $\bigl(\sum_h B^*_2(2^hu)X^h\bigr)(1 - X^2/4) = -\varepsilon_uX(1 + X/4 + X^2/16)$ for the true local
genera. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (n = 3, F_p = Q_2); hanke2011ternary Lemma 6.2, p. 23"]
theorem theorem_5_4_two_B_holds {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ}
    (hu : u ∈ sqUnits) :
    PowerSeries.mk (fun h => trueB2 v u (zSqCl v (2 ^ h * u))) * (1 - C (1 / 4 : ℝ) * X ^ 2) =
      -(C (((negOneChar u.toNat : ℤˣ) : ℤ) : ℝ) * X * (1 + C (1 / 4 : ℝ) * X + C (1 / 16 : ℝ) * X ^ 2)) :=
  theorem_5_4_two_B dyadicTernaryLocalMassTable_holds h2 hu

end QuadFormsKB.Hanke2011Structure
