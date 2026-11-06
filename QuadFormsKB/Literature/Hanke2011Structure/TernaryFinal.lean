/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.TernaryAssembly
import QuadFormsKB.Tamagawa.Odd7Main

/-!
# Paper 7's inputs from paper 6 and the true local genera

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), and *The structure of masses of rank n quadratic lattices of varying determinant
over number fields*, arXiv:1108.3580 (`hanke2011structure`).

* `oddTernaryLocalData_holds`: the odd-prime local data used by the assembly (`OddTernaryLocalData`) hold, from the
  identification of paper 7's Lemma 2.1 tuples with the true $\mathbb Z_p$-genera (`Odd7.odd_finite`, `Odd7.odd_A`,
  `Odd7.odd_B`, `Odd7.odd_unimodular`). Unconditional.
* `ternaryLocalMassFormula_of_dyadic`: paper 6's local input `TernaryLocalMassFormula`
  ($M^*_{1;3}(N) = 2\zeta(2)(A^*_3(N)+B^*_3(N))$) from Table 5.3 at $p = 2$ alone
  (`Dyadic7.DyadicTernaryLocalMassTable`), hence from the combinatorial `Dyadic7.TernaryDyadicMassCount`.
* `theorem_1_1_of_count`: paper 7's Theorem 1.1 conditional only on `Dyadic7.TernaryDyadicMassCount`.
-/

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Dyadic7 IsDedekindDomain NumberField

/-- **The odd-prime local data hold** (paper 7, Lemma 2.1–2.3 and Theorem 2.4 for the true local genera at every odd
prime of $\mathbb Q$). Unconditional. -/
@[kb "hanke2011ternary" "§2, Lemmas 2.1–2.3, Thm. 2.4, pp. 4–7 (true local genera at p odd)"]
theorem oddTernaryLocalData_holds : OddTernaryLocalData where
  fin := fun _ hv S c => Odd7.odd_finite hv S c
  A_eq := fun _ hv S hS => Odd7.odd_A hv S hS
  B_eq := fun _ hv S hS => Odd7.odd_B hv S hS
  unimod := fun _ hv S hS => Odd7.odd_unimodular hv S hS

/-- **`TernaryLocalMassFormula` from Table 5.3 at $p = 2$ alone.** -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, Rem. 4.14, p. 20; hanke2011ternary §§2–5 (F = Q, n = 3)"]
theorem ternaryLocalMassFormula_of_dyadic (H2 : DyadicTernaryLocalMassTable) : TernaryLocalMassFormula :=
  ternaryLocalMassFormula_of_tables oddTernaryLocalData_holds H2

/-- **`TernaryLocalMassFormula` from the combinatorial 2-adic count.** -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, Rem. 4.14, p. 20; hanke2011ternary §§2–5, Thm. 4.12 (F = Q, n = 3)"]
theorem ternaryLocalMassFormula_of_count (hC : TernaryDyadicMassCount) : TernaryLocalMassFormula :=
  ternaryLocalMassFormula_of_dyadic (dyadicTernaryLocalMassTable_of_count hC)

/-- **Paper 7's named input `PrimitiveMassLocalFormula`, conditional only on the 2-adic count.** -/
@[kb "hanke2011ternary" "§8, proof of Cor. 8.2 (input), via paper 6 Thm. 4.8, Lemma 3.7, Cor. 6.3–6.4"]
theorem primitiveMassLocalFormula_of_count (hC : TernaryDyadicMassCount) :
    Hanke2011Ternary.PrimitiveMassLocalFormula :=
  primitiveMassLocalFormula_of_local (ternaryLocalMassFormula_of_count hC)

/-- **Paper 7, Theorem 1.1, conditional only on the 2-adic count `TernaryDyadicMassCount`:**
$\mathrm{TMass}_3(2m) = \frac1{48}\sum_{m = ab^2}(ab - b^2)$ and $\mathrm{TMass}_3(N) = 0$ for odd $N$. -/
@[kb "hanke2011ternary" "§1, Thm. 1.1, p. 2"]
theorem theorem_1_1_of_count (hC : TernaryDyadicMassCount) :
    (∀ m : ℕ, m ≠ 0 → Hanke2011Ternary.TMass3 (2 * m) = (1 / 48) *
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m),
        ((ab.1 : ℚ) * ab.2 - (ab.2 : ℚ) ^ 2)) ∧
    (∀ N : ℕ, ¬ 2 ∣ N → Hanke2011Ternary.TMass3 N = 0) :=
  theorem_1_1_of_local (ternaryLocalMassFormula_of_count hC)

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.oddTernaryLocalData_holds
#print axioms QuadFormsKB.Hanke2011Structure.ternaryLocalMassFormula_of_dyadic
#print axioms QuadFormsKB.Hanke2011Structure.theorem_1_1_of_count
