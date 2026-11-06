import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.RefinementDefs

/-!
# Saha–Hanke §6.3: the case tree for $a + b = 3$ (generated, checked by `omega`)

Source: R. Saha and J. Hanke, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §5.3 (the Extended Refinement
Algorithm) and §6.3.

This file is **generated** by scripts (outside Lean: a case-tree search over linear cones, and a generator of the
Lean output). It replaces the source's computer run of the
Extended Refinement Algorithm by a case tree whose every step is checked by Lean (`by_cases` on a linear inequality
in the nine coefficients; each leaf is closed by `omega`, using the relation at one probe value $T$, which is the
value of one of the twelve vectors of $V$ for one of the three forms).

`core_ab12` is the purely arithmetic statement: for reduced coefficient triples $[a_i, b_i, c_i]$ and functions
$N_i$ with $N_i(t) \ge$ `cntV`$(a_i, b_i, c_i, t)$, equality for $t < \min(16a_i - 4b_i + c_i, 6c_i)$, and the
relation $N_1(t) + 2N_2(t) = 3N_3(t)$ for all $t \ge 0$, the three triples are equal or $([k,k,k], [4k,4k,4k], [k,0,3k])$ with $k = a_3$.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm.Refinement

set_option maxHeartbeats 0 in
set_option maxRecDepth 4000 in
/-- **The case tree for $a + b = 3$** (see the module docstring). -/
theorem core_ab12 {a1 b1 c1 a2 b2 c2 a3 b3 c3 : ℤ}
    {N1 N2 N3 : ℤ → ℤ}
    (r1 : 0 ≤ b1 ∧ b1 ≤ a1 ∧ a1 ≤ c1 ∧ 0 < a1) (r2 : 0 ≤ b2 ∧ b2 ≤ a2 ∧ a2 ≤ c2 ∧ 0 < a2)
    (r3 : 0 ≤ b3 ∧ b3 ≤ a3 ∧ a3 ≤ c3 ∧ 0 < a3)
    (lo1 : ∀ t, 0 ≤ t → cntV a1 b1 c1 t ≤ N1 t)
    (lo2 : ∀ t, 0 ≤ t → cntV a2 b2 c2 t ≤ N2 t)
    (lo3 : ∀ t, 0 ≤ t → cntV a3 b3 c3 t ≤ N3 t)
    (ex1 : ∀ t, 0 ≤ t → t < 16 * a1 - 4 * b1 + c1 → t < 6 * c1 → N1 t = cntV a1 b1 c1 t)
    (ex2 : ∀ t, 0 ≤ t → t < 16 * a2 - 4 * b2 + c2 → t < 6 * c2 → N2 t = cntV a2 b2 c2 t)
    (ex3 : ∀ t, 0 ≤ t → t < 16 * a3 - 4 * b3 + c3 → t < 6 * c3 → N3 t = cntV a3 b3 c3 t)
    (rel : ∀ t, 0 ≤ t → N1 t + 2 * N2 t = 3 * N3 t) :
    (a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧ a2 = a3 ∧ b2 = b3 ∧ c2 = c3) ∨
      (a1 = a3 ∧ b1 = a3 ∧ c1 = a3 ∧ a2 = 4 * a3 ∧ b2 = 4 * a3 ∧ c2 = 4 * a3 ∧ b3 = 0 ∧ c3 = 3 * a3) := by
  obtain ⟨r1a, r1b, r1c, r1d⟩ := r1
  obtain ⟨r2a, r2b, r2c, r2d⟩ := r2
  obtain ⟨r3a, r3b, r3c, r3d⟩ := r3
  by_cases h1 : 1 ≤ a1 - a2
  swap
  · -- branch
    by_cases h2 : 1 ≤ a1 - b1 + c1 - a3
    swap
    · -- branch
      by_cases h3 : 1 ≤ -a1 + a3
      swap
      · -- branch
        by_cases h4 : 1 ≤ -a1 + b1 - c1 + a2
        swap
        · -- branch
          by_cases h5 : 1 ≤ -a1 + b1 - c1 + a2 - b2 + c2
          swap
          · -- branch
            by_cases h6 : 1 ≤ -a1 + b1 - c1 + a3 - b3 + c3
            swap
            · -- branch
              exact Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
            exfalso
            have hT : 0 ≤ (a1 - b1 + c1) := by omega
            have e := rel (a1 - b1 + c1) hT
            have l1 := lo1 (a1 - b1 + c1) hT
            have l2 := lo2 (a1 - b1 + c1) hT
            have l3 := lo3 (a1 - b1 + c1) hT
            have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x3
            have := ind_bounds (a1) (a1 - b1 + c1)
            have := ind_bounds (c1) (a1 - b1 + c1)
            have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
            have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_one (a2) (a1 - b1 + c1) (by omega)
            have := ind_one (c2) (a1 - b1 + c1) (by omega)
            have := ind_one (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
            have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (a3) (a1 - b1 + c1)
            have := ind_bounds (c3) (a1 - b1 + c1)
            have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            omega
          by_cases h7 : 0 ≤ a1 - b1 + c1 - c3
          swap
          · -- branch
            by_cases h8 : 0 ≤ a1 - b1 + c1 - c2
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (a1 - b1 + c1) := by omega
              have e := rel (a1 - b1 + c1) hT
              have l1 := lo1 (a1 - b1 + c1) hT
              have l2 := lo2 (a1 - b1 + c1) hT
              have l3 := lo3 (a1 - b1 + c1) hT
              have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_bounds (a1) (a1 - b1 + c1)
              have := ind_one (c1) (a1 - b1 + c1) (by omega)
              have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_one (a2) (a1 - b1 + c1) (by omega)
              have := ind_bounds (c2) (a1 - b1 + c1)
              have := ind_bounds (a2 - b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (a3) (a1 - b1 + c1)
              have := ind_zero (c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              omega
            exfalso
            have hT : 0 ≤ (a1 - b1 + c1) := by omega
            have e := rel (a1 - b1 + c1) hT
            have l1 := lo1 (a1 - b1 + c1) hT
            have l2 := lo2 (a1 - b1 + c1) hT
            have l3 := lo3 (a1 - b1 + c1) hT
            have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x3
            have := ind_bounds (a1) (a1 - b1 + c1)
            have := ind_bounds (c1) (a1 - b1 + c1)
            have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_one (a2) (a1 - b1 + c1) (by omega)
            have := ind_one (c2) (a1 - b1 + c1) (by omega)
            have := ind_bounds (a2 - b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (a3) (a1 - b1 + c1)
            have := ind_zero (c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            omega
          by_cases h9 : 0 ≤ a1 - b1 + c1 - a3 + b3 - c3
          swap
          · -- branch
            by_cases h10 : 0 ≤ a1 - b1 + c1 - c2
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (a1 - b1 + c1) := by omega
              have e := rel (a1 - b1 + c1) hT
              have l1 := lo1 (a1 - b1 + c1) hT
              have l2 := lo2 (a1 - b1 + c1) hT
              have l3 := lo3 (a1 - b1 + c1) hT
              have x1 := ex1 (a1 - b1 + c1) hT (by omega) (by omega)
              have x2 := ex2 (a1 - b1 + c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a1 - b1 + c1)
              have := ind_bounds (c1) (a1 - b1 + c1)
              have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
              have := ind_zero (a1 + b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_bounds (a2) (a1 - b1 + c1)
              have := ind_zero (c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (a2 + b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_one (a3) (a1 - b1 + c1) (by omega)
              have := ind_one (c3) (a1 - b1 + c1) (by omega)
              have := ind_bounds (a3 - b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (a3 + b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1)
              omega
            exfalso
            have hT : 0 ≤ (a1 - b1 + c1) := by omega
            have e := rel (a1 - b1 + c1) hT
            have l1 := lo1 (a1 - b1 + c1) hT
            have l2 := lo2 (a1 - b1 + c1) hT
            have l3 := lo3 (a1 - b1 + c1) hT
            have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x3
            have := ind_one (a1) (a1 - b1 + c1) (by omega)
            have := ind_one (c1) (a1 - b1 + c1) (by omega)
            have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
            have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
            have := ind_one (a2) (a1 - b1 + c1) (by omega)
            have := ind_one (c2) (a1 - b1 + c1) (by omega)
            have := ind_bounds (a2 - b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
            have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
            have := ind_bounds (a3) (a1 - b1 + c1)
            have := ind_bounds (c3) (a1 - b1 + c1)
            have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
            omega
          exfalso
          have hT : 0 ≤ (a1 - b1 + c1) := by omega
          have e := rel (a1 - b1 + c1) hT
          have l1 := lo1 (a1 - b1 + c1) hT
          have l2 := lo2 (a1 - b1 + c1) hT
          have l3 := lo3 (a1 - b1 + c1) hT
          have x1 := ex1 (a1 - b1 + c1) hT (by omega) (by omega)
          have x2 := ex2 (a1 - b1 + c1) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (a1 - b1 + c1)
          have := ind_bounds (c1) (a1 - b1 + c1)
          have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
          have := ind_zero (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_bounds (a2) (a1 - b1 + c1)
          have := ind_bounds (c2) (a1 - b1 + c1)
          have := ind_zero (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2 + b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_one (a3) (a1 - b1 + c1) (by omega)
          have := ind_one (c3) (a1 - b1 + c1) (by omega)
          have := ind_one (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
          have := ind_bounds (a3 + b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1)
          omega
        by_cases h11 : 0 ≤ a1 - b1 + c1 - c3
        swap
        · -- branch
          by_cases h12 : 1 ≤ a1 - 2 * b1 + 4 * c1 - a3 + b3 - c3
          swap
          · -- branch
            by_cases h13 : 1 ≤ 4 * a1 + 2 * b1 + c1 - c3
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
              have e := rel (4 * a1 - 2 * b1 + c1) hT
              have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
              have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
              have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
              have x3 := ex3 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (c1) (4 * a1 - 2 * b1 + c1)
              have := ind_one (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_one (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_one (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_one (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a3) (4 * a1 - 2 * b1 + c1)
              have := ind_zero (c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
              omega
            by_cases h14 : 1 ≤ a1 - 2 * b1 + 4 * c1 - c3
            swap
            · -- branch
              by_cases h15 : 1 ≤ -4 * a1 + 2 * b1 - c1 + a2
              swap
              · -- branch
                by_cases h16 : 0 ≤ 4 * a1 - 2 * b1 + c1 - c2
                swap
                · -- branch
                  by_cases h17 : 0 ≤ 4 * a1 - 2 * b1 + c1 - c3
                  swap
                  · -- branch
                    exfalso
                    have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
                    have e := rel (4 * a1 - 2 * b1 + c1) hT
                    have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
                    have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
                    have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
                    have x3 := ex3 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_one (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_one (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_one (a2) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_bounds (c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a3) (4 * a1 - 2 * b1 + c1)
                    have := ind_zero (c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    omega
                  by_cases h18 : 0 ≤ 4 * a1 - 2 * b1 + c1 - a3 + b3 - c3
                  swap
                  · -- branch
                    exfalso
                    have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
                    have e := rel (4 * a1 - 2 * b1 + c1) hT
                    have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
                    have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
                    have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
                    have x3 := ex3 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
                    have := ind_one (c1) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_one (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_one (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_one (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_one (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                    have := ind_one (a2) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_bounds (c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (a3) (4 * a1 - 2 * b1 + c1)
                    have := ind_bounds (c3) (4 * a1 - 2 * b1 + c1)
                    have := ind_zero (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                    omega
                  exfalso
                  have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
                  have e := rel (4 * a1 - 2 * b1 + c1) hT
                  have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
                  have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
                  have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
                  have x1 := ex1 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
                  have x2 := ex2 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x1 x2
                  have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_zero (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_zero (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_bounds (a2) (4 * a1 - 2 * b1 + c1)
                  have := ind_zero (c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (a3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_bounds (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
                  omega
                by_cases h19 : 0 ≤ 4 * a1 - 2 * b1 + c1 - a2 + b2 - c2
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
                  have e := rel (4 * a1 - 2 * b1 + c1) hT
                  have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
                  have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
                  have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
                  have x3 := ex3 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_one (a1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_one (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                  have := ind_one (a2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_one (c2) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_bounds (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_bounds (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1)
                  have := ind_zero (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                  omega
                exfalso
                have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
                have e := rel (4 * a1 - 2 * b1 + c1) hT
                have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
                have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
                have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
                have x3 := ex3 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (c1) (4 * a1 - 2 * b1 + c1)
                have := ind_one (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_one (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_one (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                have := ind_one (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                have := ind_one (a2) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_one (c2) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_one (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_bounds (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a3) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (c3) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1)
                have := ind_zero (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                omega
              by_cases h20 : 0 ≤ 4 * a1 - 2 * b1 + c1 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
                have e := rel (4 * a1 - 2 * b1 + c1) hT
                have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
                have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
                have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
                have x3 := ex3 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (c1) (4 * a1 - 2 * b1 + c1)
                have := ind_one (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_one (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_one (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
                have := ind_one (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
                have := ind_bounds (a3) (4 * a1 - 2 * b1 + c1)
                have := ind_zero (c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
                omega
              by_cases h21 : 0 ≤ 4 * a1 - 2 * b1 + c1 - a3 + b3 - c3
              swap
              · -- branch
                by_cases h22 : 1 ≤ a2 - a3 + b3 - c3
                swap
                · -- branch
                  by_cases h23 : 1 ≤ -a2 + b2 - c2 + a3 + b3 + c3
                  swap
                  · -- branch
                    by_cases h24 : 1 ≤ -c2 + a3 + b3 + c3
                    swap
                    · -- branch
                      by_cases h25 : 1 ≤ -a2 + c2
                      swap
                      · -- branch
                        by_cases h26 : 1 ≤ a2 - b2
                        swap
                        · -- branch
                          exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        exfalso
                        have hT : 0 ≤ (c2) := by omega
                        have e := rel (c2) hT
                        have l1 := lo1 (c2) hT
                        have l2 := lo2 (c2) hT
                        have l3 := lo3 (c2) hT
                        have x1 := ex1 (c2) hT (by omega) (by omega)
                        have x2 := ex2 (c2) hT (by omega) (by omega)
                        simp only [cntV] at l1 l2 l3 x1 x2
                        have := ind_bounds (a1) (c2)
                        have := ind_bounds (c1) (c2)
                        have := ind_bounds (a1 - b1 + c1) (c2)
                        have := ind_bounds (a1 + b1 + c1) (c2)
                        have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
                        have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
                        have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
                        have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
                        have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
                        have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
                        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
                        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
                        have := ind_bounds (a2) (c2)
                        have := ind_bounds (c2) (c2)
                        have := ind_zero (a2 - b2 + c2) (c2) (by omega)
                        have := ind_zero (a2 + b2 + c2) (c2) (by omega)
                        have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
                        have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
                        have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
                        have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
                        have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
                        have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
                        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
                        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
                        have := ind_one (a3) (c2) (by omega)
                        have := ind_one (c3) (c2) (by omega)
                        have := ind_one (a3 - b3 + c3) (c2) (by omega)
                        have := ind_one (a3 + b3 + c3) (c2) (by omega)
                        have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
                        have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
                        have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
                        have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
                        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
                        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
                        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
                        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
                        omega
                      by_cases h27 : 0 ≤ a2 - a3 + b3 - c3
                      swap
                      · -- branch
                        exfalso
                        have hT : 0 ≤ (a2) := by omega
                        have e := rel (a2) hT
                        have l1 := lo1 (a2) hT
                        have l2 := lo2 (a2) hT
                        have l3 := lo3 (a2) hT
                        have x3 := ex3 (a2) hT (by omega) (by omega)
                        simp only [cntV] at l1 l2 l3 x3
                        have := ind_bounds (a1) (a2)
                        have := ind_one (c1) (a2) (by omega)
                        have := ind_one (a1 - b1 + c1) (a2) (by omega)
                        have := ind_one (a1 + b1 + c1) (a2) (by omega)
                        have := ind_one (4 * a1 - 2 * b1 + c1) (a2) (by omega)
                        have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
                        have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2)
                        have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2)
                        have := ind_one (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
                        have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2)
                        have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2)
                        have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2)
                        have := ind_one (a2) (a2) (by omega)
                        have := ind_bounds (c2) (a2)
                        have := ind_bounds (a2 - b2 + c2) (a2)
                        have := ind_bounds (a2 + b2 + c2) (a2)
                        have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2)
                        have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2)
                        have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2)
                        have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2)
                        have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2)
                        have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2)
                        have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2)
                        have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2)
                        have := ind_bounds (a3) (a2)
                        have := ind_bounds (c3) (a2)
                        have := ind_zero (a3 - b3 + c3) (a2) (by omega)
                        have := ind_zero (a3 + b3 + c3) (a2) (by omega)
                        have := ind_zero (4 * a3 - 2 * b3 + c3) (a2) (by omega)
                        have := ind_zero (4 * a3 + 2 * b3 + c3) (a2) (by omega)
                        have := ind_zero (9 * a3 - 3 * b3 + c3) (a2) (by omega)
                        have := ind_zero (9 * a3 + 3 * b3 + c3) (a2) (by omega)
                        have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2) (by omega)
                        have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2) (by omega)
                        have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2) (by omega)
                        have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2) (by omega)
                        omega
                      exfalso
                      have hT : 0 ≤ (a2) := by omega
                      have e := rel (a2) hT
                      have l1 := lo1 (a2) hT
                      have l2 := lo2 (a2) hT
                      have l3 := lo3 (a2) hT
                      have x1 := ex1 (a2) hT (by omega) (by omega)
                      have x2 := ex2 (a2) hT (by omega) (by omega)
                      simp only [cntV] at l1 l2 l3 x1 x2
                      have := ind_bounds (a1) (a2)
                      have := ind_bounds (c1) (a2)
                      have := ind_bounds (a1 - b1 + c1) (a2)
                      have := ind_bounds (a1 + b1 + c1) (a2)
                      have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
                      have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
                      have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
                      have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
                      have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2)
                      have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
                      have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
                      have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
                      have := ind_bounds (a2) (a2)
                      have := ind_zero (c2) (a2) (by omega)
                      have := ind_zero (a2 - b2 + c2) (a2) (by omega)
                      have := ind_zero (a2 + b2 + c2) (a2) (by omega)
                      have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
                      have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
                      have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
                      have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
                      have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
                      have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
                      have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
                      have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
                      have := ind_one (a3) (a2) (by omega)
                      have := ind_one (c3) (a2) (by omega)
                      have := ind_one (a3 - b3 + c3) (a2) (by omega)
                      have := ind_bounds (a3 + b3 + c3) (a2)
                      have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
                      have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
                      have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
                      have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
                      have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
                      have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
                      have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
                      have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
                      omega
                    exfalso
                    have hT : 0 ≤ (c2) := by omega
                    have e := rel (c2) hT
                    have l1 := lo1 (c2) hT
                    have l2 := lo2 (c2) hT
                    have l3 := lo3 (c2) hT
                    have x3 := ex3 (c2) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_one (a1) (c2) (by omega)
                    have := ind_one (c1) (c2) (by omega)
                    have := ind_one (a1 - b1 + c1) (c2) (by omega)
                    have := ind_one (a1 + b1 + c1) (c2) (by omega)
                    have := ind_one (4 * a1 - 2 * b1 + c1) (c2) (by omega)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
                    have := ind_one (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
                    have := ind_one (a2) (c2) (by omega)
                    have := ind_one (c2) (c2) (by omega)
                    have := ind_bounds (a2 - b2 + c2) (c2)
                    have := ind_bounds (a2 + b2 + c2) (c2)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
                    have := ind_bounds (a3) (c2)
                    have := ind_bounds (c3) (c2)
                    have := ind_bounds (a3 - b3 + c3) (c2)
                    have := ind_zero (a3 + b3 + c3) (c2) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
                    omega
                  exfalso
                  have hT : 0 ≤ (a2 - b2 + c2) := by omega
                  have e := rel (a2 - b2 + c2) hT
                  have l1 := lo1 (a2 - b2 + c2) hT
                  have l2 := lo2 (a2 - b2 + c2) hT
                  have l3 := lo3 (a2 - b2 + c2) hT
                  have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (a2 - b2 + c2)
                  have := ind_bounds (c1) (a2 - b2 + c2)
                  have := ind_one (a1 - b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_one (a1 + b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_one (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_one (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_one (a2) (a2 - b2 + c2) (by omega)
                  have := ind_one (c2) (a2 - b2 + c2) (by omega)
                  have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a3) (a2 - b2 + c2)
                  have := ind_bounds (c3) (a2 - b2 + c2)
                  have := ind_bounds (a3 - b3 + c3) (a2 - b2 + c2)
                  have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  omega
                by_cases h28 : 0 ≤ -2 * b3
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (a3 - b3 + c3) := by omega
                  have e := rel (a3 - b3 + c3) hT
                  have l1 := lo1 (a3 - b3 + c3) hT
                  have l2 := lo2 (a3 - b3 + c3) hT
                  have l3 := lo3 (a3 - b3 + c3) hT
                  have x1 := ex1 (a3 - b3 + c3) hT (by omega) (by omega)
                  have x2 := ex2 (a3 - b3 + c3) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x1 x2
                  have := ind_bounds (a1) (a3 - b3 + c3)
                  have := ind_bounds (c1) (a3 - b3 + c3)
                  have := ind_bounds (a1 - b1 + c1) (a3 - b3 + c3)
                  have := ind_bounds (a1 + b1 + c1) (a3 - b3 + c3)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a3 - b3 + c3)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a3 - b3 + c3)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a3 - b3 + c3)
                  have := ind_zero (9 * a1 + 3 * b1 + c1) (a3 - b3 + c3) (by omega)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a3 - b3 + c3)
                  have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                  have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                  have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                  have := ind_zero (a2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (a2 - b2 + c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (a2 + b2 + c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                  have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                  have := ind_one (a3) (a3 - b3 + c3) (by omega)
                  have := ind_one (c3) (a3 - b3 + c3) (by omega)
                  have := ind_one (a3 - b3 + c3) (a3 - b3 + c3) (by omega)
                  have := ind_bounds (a3 + b3 + c3) (a3 - b3 + c3)
                  have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 - b3 + c3)
                  have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 - b3 + c3)
                  have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 - b3 + c3)
                  have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 - b3 + c3)
                  have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 - b3 + c3)
                  have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 - b3 + c3)
                  have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 - b3 + c3)
                  have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 - b3 + c3)
                  omega
                exfalso
                have hT : 0 ≤ (a3 - b3 + c3) := by omega
                have e := rel (a3 - b3 + c3) hT
                have l1 := lo1 (a3 - b3 + c3) hT
                have l2 := lo2 (a3 - b3 + c3) hT
                have l3 := lo3 (a3 - b3 + c3) hT
                have x1 := ex1 (a3 - b3 + c3) hT (by omega) (by omega)
                have x2 := ex2 (a3 - b3 + c3) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a3 - b3 + c3)
                have := ind_bounds (c1) (a3 - b3 + c3)
                have := ind_bounds (a1 - b1 + c1) (a3 - b3 + c3)
                have := ind_bounds (a1 + b1 + c1) (a3 - b3 + c3)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (a3 - b3 + c3)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (a3 - b3 + c3)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (a3 - b3 + c3)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (a3 - b3 + c3)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a3 - b3 + c3)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a3 - b3 + c3)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a3 - b3 + c3)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (a2) (a3 - b3 + c3) (by omega)
                have := ind_zero (c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (a2 - b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (a2 + b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_one (a3) (a3 - b3 + c3) (by omega)
                have := ind_one (c3) (a3 - b3 + c3) (by omega)
                have := ind_one (a3 - b3 + c3) (a3 - b3 + c3) (by omega)
                have := ind_one (a3 + b3 + c3) (a3 - b3 + c3) (by omega)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 - b3 + c3)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 - b3 + c3)
                omega
              exfalso
              have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
              have e := rel (4 * a1 - 2 * b1 + c1) hT
              have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
              have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
              have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
              have x1 := ex1 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
              have x2 := ex2 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_one (a3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_one (c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_one (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
              have := ind_bounds (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1)
              omega
            by_cases h29 : 1 ≤ a2 - c3
            swap
            · -- branch
              by_cases h30 : 1 ≤ -a2 + b2 - c2 + a3 - b3 + c3
              swap
              · -- branch
                by_cases h31 : 1 ≤ -c2 + a3 - b3 + c3
                swap
                · -- branch
                  by_cases h32 : 0 ≤ a2 - c3
                  swap
                  · -- branch
                    exfalso
                    have hT : 0 ≤ (a2) := by omega
                    have e := rel (a2) hT
                    have l1 := lo1 (a2) hT
                    have l2 := lo2 (a2) hT
                    have l3 := lo3 (a2) hT
                    have x3 := ex3 (a2) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_bounds (a1) (a2)
                    have := ind_one (c1) (a2) (by omega)
                    have := ind_one (a1 - b1 + c1) (a2) (by omega)
                    have := ind_bounds (a1 + b1 + c1) (a2)
                    have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2)
                    have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2)
                    have := ind_one (a2) (a2) (by omega)
                    have := ind_bounds (c2) (a2)
                    have := ind_bounds (a2 - b2 + c2) (a2)
                    have := ind_bounds (a2 + b2 + c2) (a2)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2)
                    have := ind_bounds (a3) (a2)
                    have := ind_zero (c3) (a2) (by omega)
                    have := ind_zero (a3 - b3 + c3) (a2) (by omega)
                    have := ind_zero (a3 + b3 + c3) (a2) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (a2) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (a2) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (a2) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (a2) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2) (by omega)
                    omega
                  exfalso
                  have hT : 0 ≤ (a2) := by omega
                  have e := rel (a2) hT
                  have l1 := lo1 (a2) hT
                  have l2 := lo2 (a2) hT
                  have l3 := lo3 (a2) hT
                  have x1 := ex1 (a2) hT (by omega) (by omega)
                  have x2 := ex2 (a2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x1 x2
                  have := ind_bounds (a1) (a2)
                  have := ind_bounds (c1) (a2)
                  have := ind_bounds (a1 - b1 + c1) (a2)
                  have := ind_zero (a1 + b1 + c1) (a2) (by omega)
                  have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
                  have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
                  have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
                  have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
                  have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
                  have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
                  have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
                  have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
                  have := ind_bounds (a2) (a2)
                  have := ind_zero (c2) (a2) (by omega)
                  have := ind_zero (a2 - b2 + c2) (a2) (by omega)
                  have := ind_zero (a2 + b2 + c2) (a2) (by omega)
                  have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
                  have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
                  have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
                  have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
                  have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
                  have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
                  have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
                  have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
                  have := ind_one (a3) (a2) (by omega)
                  have := ind_one (c3) (a2) (by omega)
                  have := ind_bounds (a3 - b3 + c3) (a2)
                  have := ind_bounds (a3 + b3 + c3) (a2)
                  have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
                  have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
                  have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
                  have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
                  have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
                  have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
                  have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
                  have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
                  omega
                exfalso
                have hT : 0 ≤ (c2) := by omega
                have e := rel (c2) hT
                have l1 := lo1 (c2) hT
                have l2 := lo2 (c2) hT
                have l3 := lo3 (c2) hT
                have x3 := ex3 (c2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_one (a1) (c2) (by omega)
                have := ind_one (c1) (c2) (by omega)
                have := ind_one (a1 - b1 + c1) (c2) (by omega)
                have := ind_bounds (a1 + b1 + c1) (c2)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
                have := ind_one (a2) (c2) (by omega)
                have := ind_one (c2) (c2) (by omega)
                have := ind_bounds (a2 - b2 + c2) (c2)
                have := ind_bounds (a2 + b2 + c2) (c2)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
                have := ind_bounds (a3) (c2)
                have := ind_bounds (c3) (c2)
                have := ind_zero (a3 - b3 + c3) (c2) (by omega)
                have := ind_zero (a3 + b3 + c3) (c2) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
                omega
              exfalso
              have hT : 0 ≤ (a2 - b2 + c2) := by omega
              have e := rel (a2 - b2 + c2) hT
              have l1 := lo1 (a2 - b2 + c2) hT
              have l2 := lo2 (a2 - b2 + c2) hT
              have l3 := lo3 (a2 - b2 + c2) hT
              have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_bounds (a1) (a2 - b2 + c2)
              have := ind_bounds (c1) (a2 - b2 + c2)
              have := ind_one (a1 - b1 + c1) (a2 - b2 + c2) (by omega)
              have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
              have := ind_one (a2) (a2 - b2 + c2) (by omega)
              have := ind_one (c2) (a2 - b2 + c2) (by omega)
              have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
              have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
              have := ind_bounds (a3) (a2 - b2 + c2)
              have := ind_bounds (c3) (a2 - b2 + c2)
              have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
              omega
            exfalso
            have hT : 0 ≤ (c3) := by omega
            have e := rel (c3) hT
            have l1 := lo1 (c3) hT
            have l2 := lo2 (c3) hT
            have l3 := lo3 (c3) hT
            have x1 := ex1 (c3) hT (by omega) (by omega)
            have x2 := ex2 (c3) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (c3)
            have := ind_bounds (c1) (c3)
            have := ind_bounds (a1 - b1 + c1) (c3)
            have := ind_bounds (a1 + b1 + c1) (c3)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (c3)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (c3) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (c3) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (c3) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (c3) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (c3) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c3) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c3) (by omega)
            have := ind_zero (a2) (c3) (by omega)
            have := ind_zero (c2) (c3) (by omega)
            have := ind_zero (a2 - b2 + c2) (c3) (by omega)
            have := ind_zero (a2 + b2 + c2) (c3) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (c3) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (c3) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (c3) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (c3) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (c3) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (c3) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c3) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c3) (by omega)
            have := ind_one (a3) (c3) (by omega)
            have := ind_one (c3) (c3) (by omega)
            have := ind_bounds (a3 - b3 + c3) (c3)
            have := ind_bounds (a3 + b3 + c3) (c3)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (c3)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (c3)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (c3)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (c3)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c3)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c3)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c3)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c3)
            omega
          by_cases h33 : 1 ≤ a2 - a3 + b3 - c3
          swap
          · -- branch
            by_cases h34 : 0 ≤ 4 * a1 - 2 * b1 + c1 - c2
            swap
            · -- branch
              by_cases h35 : 0 ≤ a2 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a2) := by omega
                have e := rel (a2) hT
                have l1 := lo1 (a2) hT
                have l2 := lo2 (a2) hT
                have l3 := lo3 (a2) hT
                have x3 := ex3 (a2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_bounds (a1) (a2)
                have := ind_one (c1) (a2) (by omega)
                have := ind_one (a1 - b1 + c1) (a2) (by omega)
                have := ind_bounds (a1 + b1 + c1) (a2)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2)
                have := ind_one (a2) (a2) (by omega)
                have := ind_bounds (c2) (a2)
                have := ind_bounds (a2 - b2 + c2) (a2)
                have := ind_bounds (a2 + b2 + c2) (a2)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2)
                have := ind_bounds (a3) (a2)
                have := ind_zero (c3) (a2) (by omega)
                have := ind_zero (a3 - b3 + c3) (a2) (by omega)
                have := ind_zero (a3 + b3 + c3) (a2) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (a2) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (a2) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (a2) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (a2) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2) (by omega)
                omega
              by_cases h36 : 0 ≤ a2 - a3 + b3 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a2) := by omega
                have e := rel (a2) hT
                have l1 := lo1 (a2) hT
                have l2 := lo2 (a2) hT
                have l3 := lo3 (a2) hT
                have x1 := ex1 (a2) hT (by omega) (by omega)
                have x2 := ex2 (a2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a2)
                have := ind_bounds (c1) (a2)
                have := ind_bounds (a1 - b1 + c1) (a2)
                have := ind_zero (a1 + b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_bounds (a2) (a2)
                have := ind_zero (c2) (a2) (by omega)
                have := ind_zero (a2 - b2 + c2) (a2) (by omega)
                have := ind_zero (a2 + b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_one (a3) (a2) (by omega)
                have := ind_one (c3) (a2) (by omega)
                have := ind_bounds (a3 - b3 + c3) (a2)
                have := ind_bounds (a3 + b3 + c3) (a2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
                omega
              exfalso
              have hT : 0 ≤ (a2) := by omega
              have e := rel (a2) hT
              have l1 := lo1 (a2) hT
              have l2 := lo2 (a2) hT
              have l3 := lo3 (a2) hT
              have x1 := ex1 (a2) hT (by omega) (by omega)
              have x2 := ex2 (a2) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a2)
              have := ind_bounds (c1) (a2)
              have := ind_bounds (a1 - b1 + c1) (a2)
              have := ind_bounds (a1 + b1 + c1) (a2)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
              have := ind_bounds (a2) (a2)
              have := ind_zero (c2) (a2) (by omega)
              have := ind_zero (a2 - b2 + c2) (a2) (by omega)
              have := ind_zero (a2 + b2 + c2) (a2) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
              have := ind_one (a3) (a2) (by omega)
              have := ind_one (c3) (a2) (by omega)
              have := ind_one (a3 - b3 + c3) (a2) (by omega)
              have := ind_bounds (a3 + b3 + c3) (a2)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
              omega
            by_cases h37 : 0 ≤ 4 * a1 - 2 * b1 + c1 - a2 + b2 - c2
            swap
            · -- branch
              by_cases h38 : 1 ≤ -a2 + c2
              swap
              · -- branch
                by_cases h39 : 0 ≤ c2 - c3
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (c2) := by omega
                  have e := rel (c2) hT
                  have l1 := lo1 (c2) hT
                  have l2 := lo2 (c2) hT
                  have l3 := lo3 (c2) hT
                  have x3 := ex3 (c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (c2)
                  have := ind_bounds (c1) (c2)
                  have := ind_bounds (a1 - b1 + c1) (c2)
                  have := ind_bounds (a1 + b1 + c1) (c2)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
                  have := ind_one (a2) (c2) (by omega)
                  have := ind_one (c2) (c2) (by omega)
                  have := ind_bounds (a2 - b2 + c2) (c2)
                  have := ind_bounds (a2 + b2 + c2) (c2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
                  have := ind_bounds (a3) (c2)
                  have := ind_zero (c3) (c2) (by omega)
                  have := ind_zero (a3 - b3 + c3) (c2) (by omega)
                  have := ind_zero (a3 + b3 + c3) (c2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
                  omega
                by_cases h40 : 0 ≤ c2 - a3 + b3 - c3
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (c2) := by omega
                  have e := rel (c2) hT
                  have l1 := lo1 (c2) hT
                  have l2 := lo2 (c2) hT
                  have l3 := lo3 (c2) hT
                  have x3 := ex3 (c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_one (a1) (c2) (by omega)
                  have := ind_one (c1) (c2) (by omega)
                  have := ind_one (a1 - b1 + c1) (c2) (by omega)
                  have := ind_bounds (a1 + b1 + c1) (c2)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
                  have := ind_one (a2) (c2) (by omega)
                  have := ind_one (c2) (c2) (by omega)
                  have := ind_bounds (a2 - b2 + c2) (c2)
                  have := ind_bounds (a2 + b2 + c2) (c2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
                  have := ind_bounds (a3) (c2)
                  have := ind_bounds (c3) (c2)
                  have := ind_zero (a3 - b3 + c3) (c2) (by omega)
                  have := ind_zero (a3 + b3 + c3) (c2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
                  omega
                exfalso
                have hT : 0 ≤ (c2) := by omega
                have e := rel (c2) hT
                have l1 := lo1 (c2) hT
                have l2 := lo2 (c2) hT
                have l3 := lo3 (c2) hT
                have x1 := ex1 (c2) hT (by omega) (by omega)
                have x2 := ex2 (c2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (c2)
                have := ind_bounds (c1) (c2)
                have := ind_bounds (a1 - b1 + c1) (c2)
                have := ind_bounds (a1 + b1 + c1) (c2)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
                have := ind_bounds (a2) (c2)
                have := ind_bounds (c2) (c2)
                have := ind_zero (a2 - b2 + c2) (c2) (by omega)
                have := ind_zero (a2 + b2 + c2) (c2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
                have := ind_one (a3) (c2) (by omega)
                have := ind_one (c3) (c2) (by omega)
                have := ind_one (a3 - b3 + c3) (c2) (by omega)
                have := ind_bounds (a3 + b3 + c3) (c2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
                omega
              by_cases h41 : 0 ≤ a2 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a2) := by omega
                have e := rel (a2) hT
                have l1 := lo1 (a2) hT
                have l2 := lo2 (a2) hT
                have l3 := lo3 (a2) hT
                have x3 := ex3 (a2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_bounds (a1) (a2)
                have := ind_one (c1) (a2) (by omega)
                have := ind_one (a1 - b1 + c1) (a2) (by omega)
                have := ind_bounds (a1 + b1 + c1) (a2)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2)
                have := ind_one (a2) (a2) (by omega)
                have := ind_bounds (c2) (a2)
                have := ind_bounds (a2 - b2 + c2) (a2)
                have := ind_bounds (a2 + b2 + c2) (a2)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2)
                have := ind_bounds (a3) (a2)
                have := ind_zero (c3) (a2) (by omega)
                have := ind_zero (a3 - b3 + c3) (a2) (by omega)
                have := ind_zero (a3 + b3 + c3) (a2) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (a2) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (a2) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (a2) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (a2) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2) (by omega)
                omega
              by_cases h42 : 0 ≤ a2 - a3 + b3 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a2) := by omega
                have e := rel (a2) hT
                have l1 := lo1 (a2) hT
                have l2 := lo2 (a2) hT
                have l3 := lo3 (a2) hT
                have x1 := ex1 (a2) hT (by omega) (by omega)
                have x2 := ex2 (a2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a2)
                have := ind_bounds (c1) (a2)
                have := ind_bounds (a1 - b1 + c1) (a2)
                have := ind_zero (a1 + b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_bounds (a2) (a2)
                have := ind_zero (c2) (a2) (by omega)
                have := ind_zero (a2 - b2 + c2) (a2) (by omega)
                have := ind_zero (a2 + b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_one (a3) (a2) (by omega)
                have := ind_one (c3) (a2) (by omega)
                have := ind_bounds (a3 - b3 + c3) (a2)
                have := ind_bounds (a3 + b3 + c3) (a2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
                omega
              exfalso
              have hT : 0 ≤ (a2) := by omega
              have e := rel (a2) hT
              have l1 := lo1 (a2) hT
              have l2 := lo2 (a2) hT
              have l3 := lo3 (a2) hT
              have x1 := ex1 (a2) hT (by omega) (by omega)
              have x2 := ex2 (a2) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a2)
              have := ind_bounds (c1) (a2)
              have := ind_bounds (a1 - b1 + c1) (a2)
              have := ind_bounds (a1 + b1 + c1) (a2)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
              have := ind_bounds (a2) (a2)
              have := ind_zero (c2) (a2) (by omega)
              have := ind_zero (a2 - b2 + c2) (a2) (by omega)
              have := ind_zero (a2 + b2 + c2) (a2) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
              have := ind_one (a3) (a2) (by omega)
              have := ind_one (c3) (a2) (by omega)
              have := ind_one (a3 - b3 + c3) (a2) (by omega)
              have := ind_bounds (a3 + b3 + c3) (a2)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
              omega
            by_cases h43 : 1 ≤ -4 * a1 + 2 * b1 - c1 + a3 + b3 + c3
            swap
            · -- branch
              by_cases h44 : 1 ≤ a2 - c3
              swap
              · -- branch
                by_cases h45 : 1 ≤ -a2 + c2
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (c2) := by omega
                  have e := rel (c2) hT
                  have l1 := lo1 (c2) hT
                  have l2 := lo2 (c2) hT
                  have l3 := lo3 (c2) hT
                  have x3 := ex3 (c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_one (a1) (c2) (by omega)
                  have := ind_one (c1) (c2) (by omega)
                  have := ind_one (a1 - b1 + c1) (c2) (by omega)
                  have := ind_bounds (a1 + b1 + c1) (c2)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
                  have := ind_one (a2) (c2) (by omega)
                  have := ind_one (c2) (c2) (by omega)
                  have := ind_bounds (a2 - b2 + c2) (c2)
                  have := ind_bounds (a2 + b2 + c2) (c2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
                  have := ind_bounds (a3) (c2)
                  have := ind_bounds (c3) (c2)
                  have := ind_zero (a3 - b3 + c3) (c2) (by omega)
                  have := ind_zero (a3 + b3 + c3) (c2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
                  omega
                by_cases h46 : 0 ≤ a2 - c3
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (a2) := by omega
                  have e := rel (a2) hT
                  have l1 := lo1 (a2) hT
                  have l2 := lo2 (a2) hT
                  have l3 := lo3 (a2) hT
                  have x3 := ex3 (a2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (a2)
                  have := ind_one (c1) (a2) (by omega)
                  have := ind_one (a1 - b1 + c1) (a2) (by omega)
                  have := ind_bounds (a1 + b1 + c1) (a2)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2)
                  have := ind_one (a2) (a2) (by omega)
                  have := ind_bounds (c2) (a2)
                  have := ind_bounds (a2 - b2 + c2) (a2)
                  have := ind_bounds (a2 + b2 + c2) (a2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2)
                  have := ind_bounds (a3) (a2)
                  have := ind_zero (c3) (a2) (by omega)
                  have := ind_zero (a3 - b3 + c3) (a2) (by omega)
                  have := ind_zero (a3 + b3 + c3) (a2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2) (by omega)
                  omega
                exfalso
                have hT : 0 ≤ (a2) := by omega
                have e := rel (a2) hT
                have l1 := lo1 (a2) hT
                have l2 := lo2 (a2) hT
                have l3 := lo3 (a2) hT
                have x1 := ex1 (a2) hT (by omega) (by omega)
                have x2 := ex2 (a2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a2)
                have := ind_bounds (c1) (a2)
                have := ind_bounds (a1 - b1 + c1) (a2)
                have := ind_zero (a1 + b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_bounds (a2) (a2)
                have := ind_zero (c2) (a2) (by omega)
                have := ind_zero (a2 - b2 + c2) (a2) (by omega)
                have := ind_zero (a2 + b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_one (a3) (a2) (by omega)
                have := ind_one (c3) (a2) (by omega)
                have := ind_bounds (a3 - b3 + c3) (a2)
                have := ind_bounds (a3 + b3 + c3) (a2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
                omega
              exfalso
              have hT : 0 ≤ (c3) := by omega
              have e := rel (c3) hT
              have l1 := lo1 (c3) hT
              have l2 := lo2 (c3) hT
              have l3 := lo3 (c3) hT
              have x1 := ex1 (c3) hT (by omega) (by omega)
              have x2 := ex2 (c3) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (c3)
              have := ind_bounds (c1) (c3)
              have := ind_bounds (a1 - b1 + c1) (c3)
              have := ind_bounds (a1 + b1 + c1) (c3)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (c3)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (c3) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (c3) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (c3) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (c3) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (c3) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c3) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c3) (by omega)
              have := ind_zero (a2) (c3) (by omega)
              have := ind_zero (c2) (c3) (by omega)
              have := ind_zero (a2 - b2 + c2) (c3) (by omega)
              have := ind_zero (a2 + b2 + c2) (c3) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (c3) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (c3) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (c3) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (c3) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (c3) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (c3) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c3) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c3) (by omega)
              have := ind_one (a3) (c3) (by omega)
              have := ind_one (c3) (c3) (by omega)
              have := ind_bounds (a3 - b3 + c3) (c3)
              have := ind_bounds (a3 + b3 + c3) (c3)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (c3)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (c3)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (c3)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (c3)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c3)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c3)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c3)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c3)
              omega
            exfalso
            have hT : 0 ≤ (4 * a1 - 2 * b1 + c1) := by omega
            have e := rel (4 * a1 - 2 * b1 + c1) hT
            have l1 := lo1 (4 * a1 - 2 * b1 + c1) hT
            have l2 := lo2 (4 * a1 - 2 * b1 + c1) hT
            have l3 := lo3 (4 * a1 - 2 * b1 + c1) hT
            have x3 := ex3 (4 * a1 - 2 * b1 + c1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x3
            have := ind_bounds (a1) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (c1) (4 * a1 - 2 * b1 + c1)
            have := ind_one (a1 - b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_one (a1 + b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_one (4 * a1 - 2 * b1 + c1) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_bounds (4 * a1 + 2 * b1 + c1) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a1 - 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a1 + 3 * b1 + c1) (4 * a1 - 2 * b1 + c1)
            have := ind_one (a1 - 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_bounds (a1 + 2 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (4 * a1 - 2 * b1 + c1)
            have := ind_one (a2) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_one (c2) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_one (a2 - b2 + c2) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_bounds (a2 + b2 + c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (4 * a2 - 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (4 * a2 + 2 * b2 + c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a2 - 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a2 + 3 * b2 + c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (a2 - 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (a2 + 2 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (a3) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (c3) (4 * a1 - 2 * b1 + c1)
            have := ind_bounds (a3 - b3 + c3) (4 * a1 - 2 * b1 + c1)
            have := ind_zero (a3 + b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (4 * a3 - 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (4 * a3 + 2 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 3 * b3 + c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (a3 - 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (a3 + 2 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
            have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (4 * a1 - 2 * b1 + c1) (by omega)
            omega
          exfalso
          have hT : 0 ≤ (a3 - b3 + c3) := by omega
          have e := rel (a3 - b3 + c3) hT
          have l1 := lo1 (a3 - b3 + c3) hT
          have l2 := lo2 (a3 - b3 + c3) hT
          have l3 := lo3 (a3 - b3 + c3) hT
          have x1 := ex1 (a3 - b3 + c3) hT (by omega) (by omega)
          have x2 := ex2 (a3 - b3 + c3) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (a3 - b3 + c3)
          have := ind_bounds (c1) (a3 - b3 + c3)
          have := ind_bounds (a1 - b1 + c1) (a3 - b3 + c3)
          have := ind_bounds (a1 + b1 + c1) (a3 - b3 + c3)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a3 - b3 + c3)
          have := ind_bounds (4 * a1 + 2 * b1 + c1) (a3 - b3 + c3)
          have := ind_bounds (9 * a1 - 3 * b1 + c1) (a3 - b3 + c3)
          have := ind_bounds (9 * a1 + 3 * b1 + c1) (a3 - b3 + c3)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
          have := ind_zero (a2) (a3 - b3 + c3) (by omega)
          have := ind_zero (c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (a2 - b2 + c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (a2 + b2 + c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
          have := ind_one (a3) (a3 - b3 + c3) (by omega)
          have := ind_one (c3) (a3 - b3 + c3) (by omega)
          have := ind_one (a3 - b3 + c3) (a3 - b3 + c3) (by omega)
          have := ind_bounds (a3 + b3 + c3) (a3 - b3 + c3)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 - b3 + c3)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 - b3 + c3)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 - b3 + c3)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 - b3 + c3)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 - b3 + c3)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 - b3 + c3)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 - b3 + c3)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 - b3 + c3)
          omega
        by_cases h47 : 0 ≤ a1 - b1 + c1 - a3 + b3 - c3
        swap
        · -- branch
          exfalso
          have hT : 0 ≤ (a1 - b1 + c1) := by omega
          have e := rel (a1 - b1 + c1) hT
          have l1 := lo1 (a1 - b1 + c1) hT
          have l2 := lo2 (a1 - b1 + c1) hT
          have l3 := lo3 (a1 - b1 + c1) hT
          have x1 := ex1 (a1 - b1 + c1) hT (by omega) (by omega)
          have x2 := ex2 (a1 - b1 + c1) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (a1 - b1 + c1)
          have := ind_bounds (c1) (a1 - b1 + c1)
          have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
          have := ind_zero (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2) (a1 - b1 + c1) (by omega)
          have := ind_zero (c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2 + b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
          have := ind_one (a3) (a1 - b1 + c1) (by omega)
          have := ind_one (c3) (a1 - b1 + c1) (by omega)
          have := ind_bounds (a3 - b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (a3 + b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1)
          omega
        exfalso
        have hT : 0 ≤ (a1 - b1 + c1) := by omega
        have e := rel (a1 - b1 + c1) hT
        have l1 := lo1 (a1 - b1 + c1) hT
        have l2 := lo2 (a1 - b1 + c1) hT
        have l3 := lo3 (a1 - b1 + c1) hT
        have x1 := ex1 (a1 - b1 + c1) hT (by omega) (by omega)
        have x2 := ex2 (a1 - b1 + c1) hT (by omega) (by omega)
        simp only [cntV] at l1 l2 l3 x1 x2
        have := ind_bounds (a1) (a1 - b1 + c1)
        have := ind_bounds (c1) (a1 - b1 + c1)
        have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
        have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
        have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
        have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
        have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
        have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
        have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (a2) (a1 - b1 + c1) (by omega)
        have := ind_zero (c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (a2 + b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_one (a3) (a1 - b1 + c1) (by omega)
        have := ind_one (c3) (a1 - b1 + c1) (by omega)
        have := ind_one (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
        have := ind_bounds (a3 + b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1)
        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1)
        omega
      exfalso
      have hT : 0 ≤ (a1) := by omega
      have e := rel (a1) hT
      have l1 := lo1 (a1) hT
      have l2 := lo2 (a1) hT
      have l3 := lo3 (a1) hT
      have x3 := ex3 (a1) hT (by omega) (by omega)
      simp only [cntV] at l1 l2 l3 x3
      have := ind_one (a1) (a1) (by omega)
      have := ind_bounds (c1) (a1)
      have := ind_bounds (a1 - b1 + c1) (a1)
      have := ind_bounds (a1 + b1 + c1) (a1)
      have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
      have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
      have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
      have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
      have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
      have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
      have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
      have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
      have := ind_bounds (a2) (a1)
      have := ind_bounds (c2) (a1)
      have := ind_bounds (a2 - b2 + c2) (a1)
      have := ind_bounds (a2 + b2 + c2) (a1)
      have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
      have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
      have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
      have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
      have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
      have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
      have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
      have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
      have := ind_zero (a3) (a1) (by omega)
      have := ind_zero (c3) (a1) (by omega)
      have := ind_zero (a3 - b3 + c3) (a1) (by omega)
      have := ind_zero (a3 + b3 + c3) (a1) (by omega)
      have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
      have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
      have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
      have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
      have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
      have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
      have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
      have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
      omega
    by_cases h48 : 1 ≤ a2 - a3
    swap
    · -- branch
      by_cases h49 : 1 ≤ -a1 + a3
      swap
      · -- branch
        by_cases h50 : 1 ≤ -c1 + a2 - b2 + c2
        swap
        · -- branch
          by_cases h51 : 1 ≤ -a1 + a2 - b2 + c2
          swap
          · -- branch
            by_cases h52 : 1 ≤ a1 - b1
            swap
            · -- branch
              by_cases h53 : 1 ≤ -a1 + a3 - b3 + c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a1) := by omega
                have e := rel (a1) hT
                have l1 := lo1 (a1) hT
                have l2 := lo2 (a1) hT
                have l3 := lo3 (a1) hT
                have x1 := ex1 (a1) hT (by omega) (by omega)
                have x2 := ex2 (a1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a1)
                have := ind_bounds (c1) (a1)
                have := ind_zero (a1 - b1 + c1) (a1) (by omega)
                have := ind_zero (a1 + b1 + c1) (a1) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (a1) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
                have := ind_bounds (a2) (a1)
                have := ind_bounds (c2) (a1)
                have := ind_bounds (a2 - b2 + c2) (a1)
                have := ind_zero (a2 + b2 + c2) (a1) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
                have := ind_one (a3) (a1) (by omega)
                have := ind_one (c3) (a1) (by omega)
                have := ind_one (a3 - b3 + c3) (a1) (by omega)
                have := ind_bounds (a3 + b3 + c3) (a1)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
                omega
              exfalso
              have hT : 0 ≤ (a1) := by omega
              have e := rel (a1) hT
              have l1 := lo1 (a1) hT
              have l2 := lo2 (a1) hT
              have l3 := lo3 (a1) hT
              have x3 := ex3 (a1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_one (a1) (a1) (by omega)
              have := ind_bounds (c1) (a1)
              have := ind_bounds (a1 - b1 + c1) (a1)
              have := ind_bounds (a1 + b1 + c1) (a1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
              have := ind_one (a2) (a1) (by omega)
              have := ind_one (c2) (a1) (by omega)
              have := ind_one (a2 - b2 + c2) (a1) (by omega)
              have := ind_bounds (a2 + b2 + c2) (a1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
              have := ind_bounds (a3) (a1)
              have := ind_bounds (c3) (a1)
              have := ind_zero (a3 - b3 + c3) (a1) (by omega)
              have := ind_zero (a3 + b3 + c3) (a1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
              omega
            by_cases h54 : 1 ≤ -c1 + a2 + b2 + c2
            swap
            · -- branch
              by_cases h55 : 0 ≤ a1 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a1) := by omega
                have e := rel (a1) hT
                have l1 := lo1 (a1) hT
                have l2 := lo2 (a1) hT
                have l3 := lo3 (a1) hT
                have x3 := ex3 (a1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_bounds (a1) (a1)
                have := ind_bounds (c1) (a1)
                have := ind_bounds (a1 - b1 + c1) (a1)
                have := ind_bounds (a1 + b1 + c1) (a1)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
                have := ind_bounds (a2) (a1)
                have := ind_one (c2) (a1) (by omega)
                have := ind_one (a2 - b2 + c2) (a1) (by omega)
                have := ind_bounds (a2 + b2 + c2) (a1)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
                have := ind_bounds (a3) (a1)
                have := ind_zero (c3) (a1) (by omega)
                have := ind_zero (a3 - b3 + c3) (a1) (by omega)
                have := ind_zero (a3 + b3 + c3) (a1) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
                omega
              by_cases h56 : 0 ≤ a1 - a3 + b3 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a1) := by omega
                have e := rel (a1) hT
                have l1 := lo1 (a1) hT
                have l2 := lo2 (a1) hT
                have l3 := lo3 (a1) hT
                have x3 := ex3 (a1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_one (a1) (a1) (by omega)
                have := ind_bounds (c1) (a1)
                have := ind_bounds (a1 - b1 + c1) (a1)
                have := ind_bounds (a1 + b1 + c1) (a1)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
                have := ind_one (a2) (a1) (by omega)
                have := ind_one (c2) (a1) (by omega)
                have := ind_one (a2 - b2 + c2) (a1) (by omega)
                have := ind_bounds (a2 + b2 + c2) (a1)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
                have := ind_bounds (a3) (a1)
                have := ind_bounds (c3) (a1)
                have := ind_zero (a3 - b3 + c3) (a1) (by omega)
                have := ind_zero (a3 + b3 + c3) (a1) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
                omega
              exfalso
              have hT : 0 ≤ (a1) := by omega
              have e := rel (a1) hT
              have l1 := lo1 (a1) hT
              have l2 := lo2 (a1) hT
              have l3 := lo3 (a1) hT
              have x1 := ex1 (a1) hT (by omega) (by omega)
              have x2 := ex2 (a1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a1)
              have := ind_bounds (c1) (a1)
              have := ind_zero (a1 - b1 + c1) (a1) (by omega)
              have := ind_zero (a1 + b1 + c1) (a1) (by omega)
              have := ind_zero (4 * a1 - 2 * b1 + c1) (a1) (by omega)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
              have := ind_bounds (a2) (a1)
              have := ind_bounds (c2) (a1)
              have := ind_bounds (a2 - b2 + c2) (a1)
              have := ind_zero (a2 + b2 + c2) (a1) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
              have := ind_one (a3) (a1) (by omega)
              have := ind_one (c3) (a1) (by omega)
              have := ind_one (a3 - b3 + c3) (a1) (by omega)
              have := ind_bounds (a3 + b3 + c3) (a1)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
              omega
            by_cases h57 : 0 ≤ c1 - c3
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (a1) := by omega
              have e := rel (a1) hT
              have l1 := lo1 (a1) hT
              have l2 := lo2 (a1) hT
              have l3 := lo3 (a1) hT
              have x3 := ex3 (a1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_bounds (a1) (a1)
              have := ind_bounds (c1) (a1)
              have := ind_bounds (a1 - b1 + c1) (a1)
              have := ind_bounds (a1 + b1 + c1) (a1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
              have := ind_bounds (a2) (a1)
              have := ind_one (c2) (a1) (by omega)
              have := ind_one (a2 - b2 + c2) (a1) (by omega)
              have := ind_bounds (a2 + b2 + c2) (a1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
              have := ind_bounds (a3) (a1)
              have := ind_zero (c3) (a1) (by omega)
              have := ind_zero (a3 - b3 + c3) (a1) (by omega)
              have := ind_zero (a3 + b3 + c3) (a1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
              omega
            by_cases h58 : 0 ≤ c1 - a3 + b3 - c3
            swap
            · -- branch
              by_cases h59 : 1 ≤ -a1 + c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (c1) := by omega
                have e := rel (c1) hT
                have l1 := lo1 (c1) hT
                have l2 := lo2 (c1) hT
                have l3 := lo3 (c1) hT
                have x3 := ex3 (c1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_bounds (a1) (c1)
                have := ind_one (c1) (c1) (by omega)
                have := ind_bounds (a1 - b1 + c1) (c1)
                have := ind_bounds (a1 + b1 + c1) (c1)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (c1)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (c1)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (c1)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (c1)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c1)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c1)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c1)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c1)
                have := ind_one (a2) (c1) (by omega)
                have := ind_one (c2) (c1) (by omega)
                have := ind_one (a2 - b2 + c2) (c1) (by omega)
                have := ind_bounds (a2 + b2 + c2) (c1)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (c1)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (c1)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (c1)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (c1)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c1)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c1)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c1)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c1)
                have := ind_bounds (a3) (c1)
                have := ind_bounds (c3) (c1)
                have := ind_zero (a3 - b3 + c3) (c1) (by omega)
                have := ind_zero (a3 + b3 + c3) (c1) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (c1) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (c1) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (c1) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (c1) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (c1) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (c1) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c1) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c1) (by omega)
                omega
              exfalso
              have hT : 0 ≤ (a1) := by omega
              have e := rel (a1) hT
              have l1 := lo1 (a1) hT
              have l2 := lo2 (a1) hT
              have l3 := lo3 (a1) hT
              have x3 := ex3 (a1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_bounds (a1) (a1)
              have := ind_bounds (c1) (a1)
              have := ind_bounds (a1 - b1 + c1) (a1)
              have := ind_bounds (a1 + b1 + c1) (a1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
              have := ind_bounds (a2) (a1)
              have := ind_one (c2) (a1) (by omega)
              have := ind_one (a2 - b2 + c2) (a1) (by omega)
              have := ind_bounds (a2 + b2 + c2) (a1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
              have := ind_bounds (a3) (a1)
              have := ind_zero (c3) (a1) (by omega)
              have := ind_zero (a3 - b3 + c3) (a1) (by omega)
              have := ind_zero (a3 + b3 + c3) (a1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
              omega
            exfalso
            have hT : 0 ≤ (c1) := by omega
            have e := rel (c1) hT
            have l1 := lo1 (c1) hT
            have l2 := lo2 (c1) hT
            have l3 := lo3 (c1) hT
            have x1 := ex1 (c1) hT (by omega) (by omega)
            have x2 := ex2 (c1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (c1)
            have := ind_bounds (c1) (c1)
            have := ind_zero (a1 - b1 + c1) (c1) (by omega)
            have := ind_zero (a1 + b1 + c1) (c1) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (c1) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (c1) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (c1) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (c1) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (c1) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (c1) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c1) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c1) (by omega)
            have := ind_bounds (a2) (c1)
            have := ind_bounds (c2) (c1)
            have := ind_bounds (a2 - b2 + c2) (c1)
            have := ind_zero (a2 + b2 + c2) (c1) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (c1) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (c1) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (c1) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (c1) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (c1) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (c1) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c1) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c1) (by omega)
            have := ind_one (a3) (c1) (by omega)
            have := ind_one (c3) (c1) (by omega)
            have := ind_one (a3 - b3 + c3) (c1) (by omega)
            have := ind_bounds (a3 + b3 + c3) (c1)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (c1)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (c1)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (c1)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (c1)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c1)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c1)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c1)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c1)
            omega
          by_cases h60 : 0 ≤ a1 - c3
          swap
          · -- branch
            by_cases h61 : 0 ≤ a1 - c2
            swap
            · -- branch
              by_cases h62 : 1 ≤ a2 - b2
              swap
              · -- branch
                by_cases h63 : 1 ≤ a1 - b1
                swap
                · -- branch
                  by_cases h64 : 1 ≤ -a1 + b1 - c1 + a3 - b3 + c3
                  swap
                  · -- branch
                    by_cases h65 : 1 ≤ -a2 + b2 - c2 + a3 - b3 + c3
                    swap
                    · -- branch
                      by_cases h66 : 1 ≤ c2 - c3
                      swap
                      · -- branch
                        by_cases h67 : 1 ≤ a1 - b1 + c1 - a2 + b2 - c2
                        swap
                        · -- branch
                          exact Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                        exfalso
                        have hT : 0 ≤ (a2 - b2 + c2) := by omega
                        have e := rel (a2 - b2 + c2) hT
                        have l1 := lo1 (a2 - b2 + c2) hT
                        have l2 := lo2 (a2 - b2 + c2) hT
                        have l3 := lo3 (a2 - b2 + c2) hT
                        have x1 := ex1 (a2 - b2 + c2) hT (by omega) (by omega)
                        have x2 := ex2 (a2 - b2 + c2) hT (by omega) (by omega)
                        simp only [cntV] at l1 l2 l3 x1 x2
                        have := ind_bounds (a1) (a2 - b2 + c2)
                        have := ind_bounds (c1) (a2 - b2 + c2)
                        have := ind_zero (a1 - b1 + c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (a1 + b1 + c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                        have := ind_bounds (a2) (a2 - b2 + c2)
                        have := ind_bounds (c2) (a2 - b2 + c2)
                        have := ind_bounds (a2 - b2 + c2) (a2 - b2 + c2)
                        have := ind_zero (a2 + b2 + c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                        have := ind_one (a3) (a2 - b2 + c2) (by omega)
                        have := ind_one (c3) (a2 - b2 + c2) (by omega)
                        have := ind_one (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                        have := ind_bounds (a3 + b3 + c3) (a2 - b2 + c2)
                        have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2)
                        have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2)
                        have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2)
                        have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2)
                        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2)
                        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2)
                        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2)
                        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2)
                        omega
                      exfalso
                      have hT : 0 ≤ (c3) := by omega
                      have e := rel (c3) hT
                      have l1 := lo1 (c3) hT
                      have l2 := lo2 (c3) hT
                      have l3 := lo3 (c3) hT
                      have x1 := ex1 (c3) hT (by omega) (by omega)
                      have x2 := ex2 (c3) hT (by omega) (by omega)
                      simp only [cntV] at l1 l2 l3 x1 x2
                      have := ind_bounds (a1) (c3)
                      have := ind_bounds (c1) (c3)
                      have := ind_bounds (a1 - b1 + c1) (c3)
                      have := ind_zero (a1 + b1 + c1) (c3) (by omega)
                      have := ind_zero (4 * a1 - 2 * b1 + c1) (c3) (by omega)
                      have := ind_zero (4 * a1 + 2 * b1 + c1) (c3) (by omega)
                      have := ind_zero (9 * a1 - 3 * b1 + c1) (c3) (by omega)
                      have := ind_zero (9 * a1 + 3 * b1 + c1) (c3) (by omega)
                      have := ind_zero (a1 - 2 * b1 + 4 * c1) (c3) (by omega)
                      have := ind_zero (a1 + 2 * b1 + 4 * c1) (c3) (by omega)
                      have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c3) (by omega)
                      have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c3) (by omega)
                      have := ind_bounds (a2) (c3)
                      have := ind_zero (c2) (c3) (by omega)
                      have := ind_zero (a2 - b2 + c2) (c3) (by omega)
                      have := ind_zero (a2 + b2 + c2) (c3) (by omega)
                      have := ind_zero (4 * a2 - 2 * b2 + c2) (c3) (by omega)
                      have := ind_zero (4 * a2 + 2 * b2 + c2) (c3) (by omega)
                      have := ind_zero (9 * a2 - 3 * b2 + c2) (c3) (by omega)
                      have := ind_zero (9 * a2 + 3 * b2 + c2) (c3) (by omega)
                      have := ind_zero (a2 - 2 * b2 + 4 * c2) (c3) (by omega)
                      have := ind_zero (a2 + 2 * b2 + 4 * c2) (c3) (by omega)
                      have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c3) (by omega)
                      have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c3) (by omega)
                      have := ind_one (a3) (c3) (by omega)
                      have := ind_one (c3) (c3) (by omega)
                      have := ind_bounds (a3 - b3 + c3) (c3)
                      have := ind_bounds (a3 + b3 + c3) (c3)
                      have := ind_bounds (4 * a3 - 2 * b3 + c3) (c3)
                      have := ind_bounds (4 * a3 + 2 * b3 + c3) (c3)
                      have := ind_bounds (9 * a3 - 3 * b3 + c3) (c3)
                      have := ind_bounds (9 * a3 + 3 * b3 + c3) (c3)
                      have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c3)
                      have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c3)
                      have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c3)
                      have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c3)
                      omega
                    exfalso
                    have hT : 0 ≤ (a2 - b2 + c2) := by omega
                    have e := rel (a2 - b2 + c2) hT
                    have l1 := lo1 (a2 - b2 + c2) hT
                    have l2 := lo2 (a2 - b2 + c2) hT
                    have l3 := lo3 (a2 - b2 + c2) hT
                    have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_one (a1) (a2 - b2 + c2) (by omega)
                    have := ind_bounds (c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 - b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_one (a2) (a2 - b2 + c2) (by omega)
                    have := ind_one (c2) (a2 - b2 + c2) (by omega)
                    have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (a3) (a2 - b2 + c2)
                    have := ind_bounds (c3) (a2 - b2 + c2)
                    have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    omega
                  exfalso
                  have hT : 0 ≤ (a1 - b1 + c1) := by omega
                  have e := rel (a1 - b1 + c1) hT
                  have l1 := lo1 (a1 - b1 + c1) hT
                  have l2 := lo2 (a1 - b1 + c1) hT
                  have l3 := lo3 (a1 - b1 + c1) hT
                  have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (a1 - b1 + c1)
                  have := ind_bounds (c1) (a1 - b1 + c1)
                  have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
                  have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_one (a2) (a1 - b1 + c1) (by omega)
                  have := ind_one (c2) (a1 - b1 + c1) (by omega)
                  have := ind_one (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
                  have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (a3) (a1 - b1 + c1)
                  have := ind_bounds (c3) (a1 - b1 + c1)
                  have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  omega
                by_cases h68 : 1 ≤ -c1 + a2 + b2 + c2
                swap
                · -- branch
                  by_cases h69 : 0 ≤ a2 - b2 + c2 - c3
                  swap
                  · -- branch
                    exfalso
                    have hT : 0 ≤ (a2 - b2 + c2) := by omega
                    have e := rel (a2 - b2 + c2) hT
                    have l1 := lo1 (a2 - b2 + c2) hT
                    have l2 := lo2 (a2 - b2 + c2) hT
                    have l3 := lo3 (a2 - b2 + c2) hT
                    have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_bounds (a1) (a2 - b2 + c2)
                    have := ind_bounds (c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 - b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (a2) (a2 - b2 + c2)
                    have := ind_one (c2) (a2 - b2 + c2) (by omega)
                    have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (a3) (a2 - b2 + c2)
                    have := ind_zero (c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    omega
                  by_cases h70 : 0 ≤ a2 - b2 + c2 - a3 + b3 - c3
                  swap
                  · -- branch
                    exfalso
                    have hT : 0 ≤ (a2 - b2 + c2) := by omega
                    have e := rel (a2 - b2 + c2) hT
                    have l1 := lo1 (a2 - b2 + c2) hT
                    have l2 := lo2 (a2 - b2 + c2) hT
                    have l3 := lo3 (a2 - b2 + c2) hT
                    have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_one (a1) (a2 - b2 + c2) (by omega)
                    have := ind_bounds (c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 - b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                    have := ind_one (a2) (a2 - b2 + c2) (by omega)
                    have := ind_one (c2) (a2 - b2 + c2) (by omega)
                    have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                    have := ind_bounds (a3) (a2 - b2 + c2)
                    have := ind_bounds (c3) (a2 - b2 + c2)
                    have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                    omega
                  exfalso
                  have hT : 0 ≤ (a2 - b2 + c2) := by omega
                  have e := rel (a2 - b2 + c2) hT
                  have l1 := lo1 (a2 - b2 + c2) hT
                  have l2 := lo2 (a2 - b2 + c2) hT
                  have l3 := lo3 (a2 - b2 + c2) hT
                  have x1 := ex1 (a2 - b2 + c2) hT (by omega) (by omega)
                  have x2 := ex2 (a2 - b2 + c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x1 x2
                  have := ind_bounds (a1) (a2 - b2 + c2)
                  have := ind_bounds (c1) (a2 - b2 + c2)
                  have := ind_zero (a1 - b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a1 + b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a2) (a2 - b2 + c2)
                  have := ind_bounds (c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 - b2 + c2) (a2 - b2 + c2)
                  have := ind_zero (a2 + b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                  have := ind_one (a3) (a2 - b2 + c2) (by omega)
                  have := ind_one (c3) (a2 - b2 + c2) (by omega)
                  have := ind_one (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a3 + b3 + c3) (a2 - b2 + c2)
                  have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2)
                  have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2)
                  have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2)
                  have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2)
                  have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2)
                  have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2)
                  have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2)
                  have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2)
                  omega
                by_cases h71 : 0 ≤ c1 - c3
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (a2 - b2 + c2) := by omega
                  have e := rel (a2 - b2 + c2) hT
                  have l1 := lo1 (a2 - b2 + c2) hT
                  have l2 := lo2 (a2 - b2 + c2) hT
                  have l3 := lo3 (a2 - b2 + c2) hT
                  have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (a2 - b2 + c2)
                  have := ind_bounds (c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 - b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (a2) (a2 - b2 + c2)
                  have := ind_one (c2) (a2 - b2 + c2) (by omega)
                  have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a3) (a2 - b2 + c2)
                  have := ind_zero (c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  omega
                by_cases h72 : 0 ≤ c1 - a3 + b3 - c3
                swap
                · -- branch
                  by_cases h73 : 1 ≤ -a2 + b2 - c2 + c3
                  swap
                  · -- branch
                    exfalso
                    have hT : 0 ≤ (c1) := by omega
                    have e := rel (c1) hT
                    have l1 := lo1 (c1) hT
                    have l2 := lo2 (c1) hT
                    have l3 := lo3 (c1) hT
                    have x3 := ex3 (c1) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x3
                    have := ind_bounds (a1) (c1)
                    have := ind_one (c1) (c1) (by omega)
                    have := ind_bounds (a1 - b1 + c1) (c1)
                    have := ind_bounds (a1 + b1 + c1) (c1)
                    have := ind_bounds (4 * a1 - 2 * b1 + c1) (c1)
                    have := ind_bounds (4 * a1 + 2 * b1 + c1) (c1)
                    have := ind_bounds (9 * a1 - 3 * b1 + c1) (c1)
                    have := ind_bounds (9 * a1 + 3 * b1 + c1) (c1)
                    have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c1)
                    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c1)
                    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c1)
                    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c1)
                    have := ind_one (a2) (c1) (by omega)
                    have := ind_one (c2) (c1) (by omega)
                    have := ind_one (a2 - b2 + c2) (c1) (by omega)
                    have := ind_bounds (a2 + b2 + c2) (c1)
                    have := ind_bounds (4 * a2 - 2 * b2 + c2) (c1)
                    have := ind_bounds (4 * a2 + 2 * b2 + c2) (c1)
                    have := ind_bounds (9 * a2 - 3 * b2 + c2) (c1)
                    have := ind_bounds (9 * a2 + 3 * b2 + c2) (c1)
                    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c1)
                    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c1)
                    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c1)
                    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c1)
                    have := ind_bounds (a3) (c1)
                    have := ind_bounds (c3) (c1)
                    have := ind_zero (a3 - b3 + c3) (c1) (by omega)
                    have := ind_zero (a3 + b3 + c3) (c1) (by omega)
                    have := ind_zero (4 * a3 - 2 * b3 + c3) (c1) (by omega)
                    have := ind_zero (4 * a3 + 2 * b3 + c3) (c1) (by omega)
                    have := ind_zero (9 * a3 - 3 * b3 + c3) (c1) (by omega)
                    have := ind_zero (9 * a3 + 3 * b3 + c3) (c1) (by omega)
                    have := ind_zero (a3 - 2 * b3 + 4 * c3) (c1) (by omega)
                    have := ind_zero (a3 + 2 * b3 + 4 * c3) (c1) (by omega)
                    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c1) (by omega)
                    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c1) (by omega)
                    omega
                  exfalso
                  have hT : 0 ≤ (a2 - b2 + c2) := by omega
                  have e := rel (a2 - b2 + c2) hT
                  have l1 := lo1 (a2 - b2 + c2) hT
                  have l2 := lo2 (a2 - b2 + c2) hT
                  have l3 := lo3 (a2 - b2 + c2) hT
                  have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (a2 - b2 + c2)
                  have := ind_bounds (c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 - b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (a2) (a2 - b2 + c2)
                  have := ind_one (c2) (a2 - b2 + c2) (by omega)
                  have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a3) (a2 - b2 + c2)
                  have := ind_zero (c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  omega
                exfalso
                have hT : 0 ≤ (c1) := by omega
                have e := rel (c1) hT
                have l1 := lo1 (c1) hT
                have l2 := lo2 (c1) hT
                have l3 := lo3 (c1) hT
                have x1 := ex1 (c1) hT (by omega) (by omega)
                have x2 := ex2 (c1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (c1)
                have := ind_bounds (c1) (c1)
                have := ind_zero (a1 - b1 + c1) (c1) (by omega)
                have := ind_zero (a1 + b1 + c1) (c1) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (c1) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (c1) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (c1) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (c1) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (c1) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (c1) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c1) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c1) (by omega)
                have := ind_bounds (a2) (c1)
                have := ind_bounds (c2) (c1)
                have := ind_bounds (a2 - b2 + c2) (c1)
                have := ind_zero (a2 + b2 + c2) (c1) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (c1) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (c1) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (c1) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (c1) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (c1) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (c1) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c1) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c1) (by omega)
                have := ind_one (a3) (c1) (by omega)
                have := ind_one (c3) (c1) (by omega)
                have := ind_one (a3 - b3 + c3) (c1) (by omega)
                have := ind_bounds (a3 + b3 + c3) (c1)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (c1)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (c1)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (c1)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (c1)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c1)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c1)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c1)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c1)
                omega
              by_cases h74 : 0 ≤ c2 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (c2) := by omega
                have e := rel (c2) hT
                have l1 := lo1 (c2) hT
                have l2 := lo2 (c2) hT
                have l3 := lo3 (c2) hT
                have x3 := ex3 (c2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_bounds (a1) (c2)
                have := ind_bounds (c1) (c2)
                have := ind_bounds (a1 - b1 + c1) (c2)
                have := ind_bounds (a1 + b1 + c1) (c2)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
                have := ind_one (a2) (c2) (by omega)
                have := ind_one (c2) (c2) (by omega)
                have := ind_bounds (a2 - b2 + c2) (c2)
                have := ind_bounds (a2 + b2 + c2) (c2)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
                have := ind_bounds (a3) (c2)
                have := ind_zero (c3) (c2) (by omega)
                have := ind_zero (a3 - b3 + c3) (c2) (by omega)
                have := ind_zero (a3 + b3 + c3) (c2) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
                omega
              by_cases h75 : 0 ≤ c2 - a3 + b3 - c3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (c2) := by omega
                have e := rel (c2) hT
                have l1 := lo1 (c2) hT
                have l2 := lo2 (c2) hT
                have l3 := lo3 (c2) hT
                have x1 := ex1 (c2) hT (by omega) (by omega)
                have x2 := ex2 (c2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (c2)
                have := ind_zero (c1) (c2) (by omega)
                have := ind_zero (a1 - b1 + c1) (c2) (by omega)
                have := ind_zero (a1 + b1 + c1) (c2) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
                have := ind_bounds (a2) (c2)
                have := ind_bounds (c2) (c2)
                have := ind_zero (a2 - b2 + c2) (c2) (by omega)
                have := ind_zero (a2 + b2 + c2) (c2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
                have := ind_one (a3) (c2) (by omega)
                have := ind_one (c3) (c2) (by omega)
                have := ind_bounds (a3 - b3 + c3) (c2)
                have := ind_bounds (a3 + b3 + c3) (c2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
                omega
              exfalso
              have hT : 0 ≤ (c2) := by omega
              have e := rel (c2) hT
              have l1 := lo1 (c2) hT
              have l2 := lo2 (c2) hT
              have l3 := lo3 (c2) hT
              have x1 := ex1 (c2) hT (by omega) (by omega)
              have x2 := ex2 (c2) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (c2)
              have := ind_bounds (c1) (c2)
              have := ind_bounds (a1 - b1 + c1) (c2)
              have := ind_bounds (a1 + b1 + c1) (c2)
              have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
              have := ind_bounds (a2) (c2)
              have := ind_bounds (c2) (c2)
              have := ind_zero (a2 - b2 + c2) (c2) (by omega)
              have := ind_zero (a2 + b2 + c2) (c2) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
              have := ind_one (a3) (c2) (by omega)
              have := ind_one (c3) (c2) (by omega)
              have := ind_one (a3 - b3 + c3) (c2) (by omega)
              have := ind_bounds (a3 + b3 + c3) (c2)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
              omega
            exfalso
            have hT : 0 ≤ (a1) := by omega
            have e := rel (a1) hT
            have l1 := lo1 (a1) hT
            have l2 := lo2 (a1) hT
            have l3 := lo3 (a1) hT
            have x3 := ex3 (a1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x3
            have := ind_bounds (a1) (a1)
            have := ind_bounds (c1) (a1)
            have := ind_bounds (a1 - b1 + c1) (a1)
            have := ind_bounds (a1 + b1 + c1) (a1)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
            have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
            have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
            have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
            have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
            have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
            have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
            have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
            have := ind_one (a2) (a1) (by omega)
            have := ind_one (c2) (a1) (by omega)
            have := ind_bounds (a2 - b2 + c2) (a1)
            have := ind_bounds (a2 + b2 + c2) (a1)
            have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
            have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
            have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
            have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
            have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
            have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
            have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
            have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
            have := ind_bounds (a3) (a1)
            have := ind_zero (c3) (a1) (by omega)
            have := ind_zero (a3 - b3 + c3) (a1) (by omega)
            have := ind_zero (a3 + b3 + c3) (a1) (by omega)
            have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
            have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
            have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
            have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
            have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
            have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
            have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
            have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
            omega
          by_cases h76 : 0 ≤ a1 - a3 + b3 - c3
          swap
          · -- branch
            exfalso
            have hT : 0 ≤ (a1) := by omega
            have e := rel (a1) hT
            have l1 := lo1 (a1) hT
            have l2 := lo2 (a1) hT
            have l3 := lo3 (a1) hT
            have x1 := ex1 (a1) hT (by omega) (by omega)
            have x2 := ex2 (a1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (a1)
            have := ind_zero (c1) (a1) (by omega)
            have := ind_zero (a1 - b1 + c1) (a1) (by omega)
            have := ind_zero (a1 + b1 + c1) (a1) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (a1) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
            have := ind_bounds (a2) (a1)
            have := ind_bounds (c2) (a1)
            have := ind_zero (a2 - b2 + c2) (a1) (by omega)
            have := ind_zero (a2 + b2 + c2) (a1) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
            have := ind_one (a3) (a1) (by omega)
            have := ind_one (c3) (a1) (by omega)
            have := ind_bounds (a3 - b3 + c3) (a1)
            have := ind_bounds (a3 + b3 + c3) (a1)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
            omega
          exfalso
          have hT : 0 ≤ (a1) := by omega
          have e := rel (a1) hT
          have l1 := lo1 (a1) hT
          have l2 := lo2 (a1) hT
          have l3 := lo3 (a1) hT
          have x1 := ex1 (a1) hT (by omega) (by omega)
          have x2 := ex2 (a1) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (a1)
          have := ind_bounds (c1) (a1)
          have := ind_bounds (a1 - b1 + c1) (a1)
          have := ind_bounds (a1 + b1 + c1) (a1)
          have := ind_zero (4 * a1 - 2 * b1 + c1) (a1) (by omega)
          have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
          have := ind_bounds (a2) (a1)
          have := ind_bounds (c2) (a1)
          have := ind_zero (a2 - b2 + c2) (a1) (by omega)
          have := ind_zero (a2 + b2 + c2) (a1) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
          have := ind_one (a3) (a1) (by omega)
          have := ind_one (c3) (a1) (by omega)
          have := ind_one (a3 - b3 + c3) (a1) (by omega)
          have := ind_bounds (a3 + b3 + c3) (a1)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
          omega
        by_cases h77 : 0 ≤ c1 - c3
        swap
        · -- branch
          by_cases h78 : 0 ≤ a1 - c2
          swap
          · -- branch
            by_cases h79 : 1 ≤ -c2 + c3
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (c1) := by omega
              have e := rel (c1) hT
              have l1 := lo1 (c1) hT
              have l2 := lo2 (c1) hT
              have l3 := lo3 (c1) hT
              have x3 := ex3 (c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_one (a1) (c1) (by omega)
              have := ind_one (c1) (c1) (by omega)
              have := ind_bounds (a1 - b1 + c1) (c1)
              have := ind_bounds (a1 + b1 + c1) (c1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (c1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (c1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (c1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (c1)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c1)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c1)
              have := ind_one (a2) (c1) (by omega)
              have := ind_bounds (c2) (c1)
              have := ind_bounds (a2 - b2 + c2) (c1)
              have := ind_bounds (a2 + b2 + c2) (c1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (c1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (c1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (c1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (c1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c1)
              have := ind_bounds (a3) (c1)
              have := ind_zero (c3) (c1) (by omega)
              have := ind_zero (a3 - b3 + c3) (c1) (by omega)
              have := ind_zero (a3 + b3 + c3) (c1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (c1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (c1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (c1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (c1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (c1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (c1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c1) (by omega)
              omega
            exfalso
            have hT : 0 ≤ (c2) := by omega
            have e := rel (c2) hT
            have l1 := lo1 (c2) hT
            have l2 := lo2 (c2) hT
            have l3 := lo3 (c2) hT
            have x3 := ex3 (c2) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x3
            have := ind_bounds (a1) (c2)
            have := ind_bounds (c1) (c2)
            have := ind_bounds (a1 - b1 + c1) (c2)
            have := ind_bounds (a1 + b1 + c1) (c2)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
            have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
            have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
            have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
            have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
            have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
            have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
            have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
            have := ind_one (a2) (c2) (by omega)
            have := ind_one (c2) (c2) (by omega)
            have := ind_bounds (a2 - b2 + c2) (c2)
            have := ind_bounds (a2 + b2 + c2) (c2)
            have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
            have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
            have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
            have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
            have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
            have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
            have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
            have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
            have := ind_bounds (a3) (c2)
            have := ind_zero (c3) (c2) (by omega)
            have := ind_zero (a3 - b3 + c3) (c2) (by omega)
            have := ind_zero (a3 + b3 + c3) (c2) (by omega)
            have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
            have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
            have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
            have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
            have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
            have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
            have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
            have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
            omega
          exfalso
          have hT : 0 ≤ (a1) := by omega
          have e := rel (a1) hT
          have l1 := lo1 (a1) hT
          have l2 := lo2 (a1) hT
          have l3 := lo3 (a1) hT
          have x3 := ex3 (a1) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x3
          have := ind_bounds (a1) (a1)
          have := ind_bounds (c1) (a1)
          have := ind_bounds (a1 - b1 + c1) (a1)
          have := ind_bounds (a1 + b1 + c1) (a1)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
          have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
          have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
          have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
          have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
          have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
          have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
          have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
          have := ind_one (a2) (a1) (by omega)
          have := ind_one (c2) (a1) (by omega)
          have := ind_bounds (a2 - b2 + c2) (a1)
          have := ind_bounds (a2 + b2 + c2) (a1)
          have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
          have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
          have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
          have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
          have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
          have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
          have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
          have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
          have := ind_bounds (a3) (a1)
          have := ind_zero (c3) (a1) (by omega)
          have := ind_zero (a3 - b3 + c3) (a1) (by omega)
          have := ind_zero (a3 + b3 + c3) (a1) (by omega)
          have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
          have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
          have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
          have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
          have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
          have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
          have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
          have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
          omega
        by_cases h80 : 0 ≤ c1 - a3 + b3 - c3
        swap
        · -- branch
          by_cases h81 : 0 ≤ a1 - c2
          swap
          · -- branch
            by_cases h82 : 1 ≤ -c2 + c3
            swap
            · -- branch
              by_cases h83 : 1 ≤ -a1 + b1 - c1 + a2 - b2 + c2
              swap
              · -- branch
                by_cases h84 : 1 ≤ c1 - c2
                swap
                · -- branch
                  by_cases h85 : 1 ≤ -c1 + c2
                  swap
                  · -- branch
                    by_cases h86 : 1 ≤ a1 - b1 + c1 - a2 + b2 - c2
                    swap
                    · -- branch
                      by_cases h87 : 1 ≤ -a1 + b1 - c1 + a3 - b3 + c3
                      swap
                      · -- branch
                        by_cases h88 : 0 ≤ a1 - c3
                        swap
                        · -- branch
                          by_cases h89 : 1 ≤ c2 - c3
                          swap
                          · -- branch
                            by_cases h90 : 1 ≤ a2 - b2 + c2 - a3 + b3 - c3
                            swap
                            · -- branch
                              exact Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                            exfalso
                            have hT : 0 ≤ (a3 - b3 + c3) := by omega
                            have e := rel (a3 - b3 + c3) hT
                            have l1 := lo1 (a3 - b3 + c3) hT
                            have l2 := lo2 (a3 - b3 + c3) hT
                            have l3 := lo3 (a3 - b3 + c3) hT
                            have x1 := ex1 (a3 - b3 + c3) hT (by omega) (by omega)
                            have x2 := ex2 (a3 - b3 + c3) hT (by omega) (by omega)
                            simp only [cntV] at l1 l2 l3 x1 x2
                            have := ind_bounds (a1) (a3 - b3 + c3)
                            have := ind_bounds (c1) (a3 - b3 + c3)
                            have := ind_bounds (a1 - b1 + c1) (a3 - b3 + c3)
                            have := ind_bounds (a1 + b1 + c1) (a3 - b3 + c3)
                            have := ind_zero (4 * a1 - 2 * b1 + c1) (a3 - b3 + c3) (by omega)
                            have := ind_zero (4 * a1 + 2 * b1 + c1) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a1 - 3 * b1 + c1) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a1 + 3 * b1 + c1) (a3 - b3 + c3) (by omega)
                            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                            have := ind_bounds (a2) (a3 - b3 + c3)
                            have := ind_bounds (c2) (a3 - b3 + c3)
                            have := ind_zero (a2 - b2 + c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (a2 + b2 + c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                            have := ind_one (a3) (a3 - b3 + c3) (by omega)
                            have := ind_one (c3) (a3 - b3 + c3) (by omega)
                            have := ind_one (a3 - b3 + c3) (a3 - b3 + c3) (by omega)
                            have := ind_bounds (a3 + b3 + c3) (a3 - b3 + c3)
                            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 - b3 + c3)
                            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 - b3 + c3)
                            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 - b3 + c3)
                            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 - b3 + c3)
                            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 - b3 + c3)
                            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 - b3 + c3)
                            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 - b3 + c3)
                            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 - b3 + c3)
                            omega
                          exfalso
                          have hT : 0 ≤ (c3) := by omega
                          have e := rel (c3) hT
                          have l1 := lo1 (c3) hT
                          have l2 := lo2 (c3) hT
                          have l3 := lo3 (c3) hT
                          have x1 := ex1 (c3) hT (by omega) (by omega)
                          have x2 := ex2 (c3) hT (by omega) (by omega)
                          simp only [cntV] at l1 l2 l3 x1 x2
                          have := ind_bounds (a1) (c3)
                          have := ind_bounds (c1) (c3)
                          have := ind_bounds (a1 - b1 + c1) (c3)
                          have := ind_zero (a1 + b1 + c1) (c3) (by omega)
                          have := ind_zero (4 * a1 - 2 * b1 + c1) (c3) (by omega)
                          have := ind_zero (4 * a1 + 2 * b1 + c1) (c3) (by omega)
                          have := ind_zero (9 * a1 - 3 * b1 + c1) (c3) (by omega)
                          have := ind_zero (9 * a1 + 3 * b1 + c1) (c3) (by omega)
                          have := ind_zero (a1 - 2 * b1 + 4 * c1) (c3) (by omega)
                          have := ind_zero (a1 + 2 * b1 + 4 * c1) (c3) (by omega)
                          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c3) (by omega)
                          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c3) (by omega)
                          have := ind_bounds (a2) (c3)
                          have := ind_zero (c2) (c3) (by omega)
                          have := ind_zero (a2 - b2 + c2) (c3) (by omega)
                          have := ind_zero (a2 + b2 + c2) (c3) (by omega)
                          have := ind_zero (4 * a2 - 2 * b2 + c2) (c3) (by omega)
                          have := ind_zero (4 * a2 + 2 * b2 + c2) (c3) (by omega)
                          have := ind_zero (9 * a2 - 3 * b2 + c2) (c3) (by omega)
                          have := ind_zero (9 * a2 + 3 * b2 + c2) (c3) (by omega)
                          have := ind_zero (a2 - 2 * b2 + 4 * c2) (c3) (by omega)
                          have := ind_zero (a2 + 2 * b2 + 4 * c2) (c3) (by omega)
                          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c3) (by omega)
                          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c3) (by omega)
                          have := ind_one (a3) (c3) (by omega)
                          have := ind_one (c3) (c3) (by omega)
                          have := ind_bounds (a3 - b3 + c3) (c3)
                          have := ind_bounds (a3 + b3 + c3) (c3)
                          have := ind_bounds (4 * a3 - 2 * b3 + c3) (c3)
                          have := ind_bounds (4 * a3 + 2 * b3 + c3) (c3)
                          have := ind_bounds (9 * a3 - 3 * b3 + c3) (c3)
                          have := ind_bounds (9 * a3 + 3 * b3 + c3) (c3)
                          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c3)
                          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c3)
                          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c3)
                          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c3)
                          omega
                        exfalso
                        have hT : 0 ≤ (a1) := by omega
                        have e := rel (a1) hT
                        have l1 := lo1 (a1) hT
                        have l2 := lo2 (a1) hT
                        have l3 := lo3 (a1) hT
                        have x1 := ex1 (a1) hT (by omega) (by omega)
                        have x2 := ex2 (a1) hT (by omega) (by omega)
                        simp only [cntV] at l1 l2 l3 x1 x2
                        have := ind_bounds (a1) (a1)
                        have := ind_bounds (c1) (a1)
                        have := ind_bounds (a1 - b1 + c1) (a1)
                        have := ind_zero (a1 + b1 + c1) (a1) (by omega)
                        have := ind_zero (4 * a1 - 2 * b1 + c1) (a1) (by omega)
                        have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
                        have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
                        have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
                        have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
                        have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
                        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
                        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
                        have := ind_bounds (a2) (a1)
                        have := ind_zero (c2) (a1) (by omega)
                        have := ind_zero (a2 - b2 + c2) (a1) (by omega)
                        have := ind_zero (a2 + b2 + c2) (a1) (by omega)
                        have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
                        have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
                        have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
                        have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
                        have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
                        have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
                        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
                        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
                        have := ind_one (a3) (a1) (by omega)
                        have := ind_one (c3) (a1) (by omega)
                        have := ind_bounds (a3 - b3 + c3) (a1)
                        have := ind_bounds (a3 + b3 + c3) (a1)
                        have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
                        have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
                        have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
                        have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
                        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
                        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
                        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
                        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
                        omega
                      exfalso
                      have hT : 0 ≤ (a1 - b1 + c1) := by omega
                      have e := rel (a1 - b1 + c1) hT
                      have l1 := lo1 (a1 - b1 + c1) hT
                      have l2 := lo2 (a1 - b1 + c1) hT
                      have l3 := lo3 (a1 - b1 + c1) hT
                      have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
                      simp only [cntV] at l1 l2 l3 x3
                      have := ind_bounds (a1) (a1 - b1 + c1)
                      have := ind_bounds (c1) (a1 - b1 + c1)
                      have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
                      have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
                      have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
                      have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
                      have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
                      have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
                      have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
                      have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
                      have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
                      have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
                      have := ind_one (a2) (a1 - b1 + c1) (by omega)
                      have := ind_one (c2) (a1 - b1 + c1) (by omega)
                      have := ind_one (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
                      have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
                      have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
                      have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
                      have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
                      have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
                      have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
                      have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
                      have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
                      have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
                      have := ind_bounds (a3) (a1 - b1 + c1)
                      have := ind_bounds (c3) (a1 - b1 + c1)
                      have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                      have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                      omega
                    by_cases h91 : 0 ≤ a2 - b2 + c2 - a3 + b3 - c3
                    swap
                    · -- branch
                      exfalso
                      have hT : 0 ≤ (a2 - b2 + c2) := by omega
                      have e := rel (a2 - b2 + c2) hT
                      have l1 := lo1 (a2 - b2 + c2) hT
                      have l2 := lo2 (a2 - b2 + c2) hT
                      have l3 := lo3 (a2 - b2 + c2) hT
                      have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                      simp only [cntV] at l1 l2 l3 x3
                      have := ind_bounds (a1) (a2 - b2 + c2)
                      have := ind_one (c1) (a2 - b2 + c2) (by omega)
                      have := ind_bounds (a1 - b1 + c1) (a2 - b2 + c2)
                      have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
                      have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
                      have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                      have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                      have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                      have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
                      have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                      have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                      have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                      have := ind_one (a2) (a2 - b2 + c2) (by omega)
                      have := ind_one (c2) (a2 - b2 + c2) (by omega)
                      have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                      have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                      have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                      have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                      have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                      have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                      have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                      have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                      have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                      have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                      have := ind_bounds (a3) (a2 - b2 + c2)
                      have := ind_bounds (c3) (a2 - b2 + c2)
                      have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                      have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                      omega
                    exfalso
                    have hT : 0 ≤ (a2 - b2 + c2) := by omega
                    have e := rel (a2 - b2 + c2) hT
                    have l1 := lo1 (a2 - b2 + c2) hT
                    have l2 := lo2 (a2 - b2 + c2) hT
                    have l3 := lo3 (a2 - b2 + c2) hT
                    have x1 := ex1 (a2 - b2 + c2) hT (by omega) (by omega)
                    have x2 := ex2 (a2 - b2 + c2) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x1 x2
                    have := ind_bounds (a1) (a2 - b2 + c2)
                    have := ind_bounds (c1) (a2 - b2 + c2)
                    have := ind_zero (a1 - b1 + c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a1 + b1 + c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                    have := ind_bounds (a2) (a2 - b2 + c2)
                    have := ind_bounds (c2) (a2 - b2 + c2)
                    have := ind_bounds (a2 - b2 + c2) (a2 - b2 + c2)
                    have := ind_zero (a2 + b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                    have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                    have := ind_one (a3) (a2 - b2 + c2) (by omega)
                    have := ind_one (c3) (a2 - b2 + c2) (by omega)
                    have := ind_one (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                    have := ind_bounds (a3 + b3 + c3) (a2 - b2 + c2)
                    have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2)
                    have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2)
                    have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2)
                    have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2)
                    have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2)
                    have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2)
                    have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2)
                    have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2)
                    omega
                  exfalso
                  have hT : 0 ≤ (c1) := by omega
                  have e := rel (c1) hT
                  have l1 := lo1 (c1) hT
                  have l2 := lo2 (c1) hT
                  have l3 := lo3 (c1) hT
                  have x1 := ex1 (c1) hT (by omega) (by omega)
                  have x2 := ex2 (c1) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x1 x2
                  have := ind_bounds (a1) (c1)
                  have := ind_bounds (c1) (c1)
                  have := ind_bounds (a1 - b1 + c1) (c1)
                  have := ind_zero (a1 + b1 + c1) (c1) (by omega)
                  have := ind_zero (4 * a1 - 2 * b1 + c1) (c1) (by omega)
                  have := ind_zero (4 * a1 + 2 * b1 + c1) (c1) (by omega)
                  have := ind_zero (9 * a1 - 3 * b1 + c1) (c1) (by omega)
                  have := ind_zero (9 * a1 + 3 * b1 + c1) (c1) (by omega)
                  have := ind_zero (a1 - 2 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_zero (a1 + 2 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_bounds (a2) (c1)
                  have := ind_zero (c2) (c1) (by omega)
                  have := ind_zero (a2 - b2 + c2) (c1) (by omega)
                  have := ind_zero (a2 + b2 + c2) (c1) (by omega)
                  have := ind_zero (4 * a2 - 2 * b2 + c2) (c1) (by omega)
                  have := ind_zero (4 * a2 + 2 * b2 + c2) (c1) (by omega)
                  have := ind_zero (9 * a2 - 3 * b2 + c2) (c1) (by omega)
                  have := ind_zero (9 * a2 + 3 * b2 + c2) (c1) (by omega)
                  have := ind_zero (a2 - 2 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_zero (a2 + 2 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_one (a3) (c1) (by omega)
                  have := ind_one (c3) (c1) (by omega)
                  have := ind_bounds (a3 - b3 + c3) (c1)
                  have := ind_bounds (a3 + b3 + c3) (c1)
                  have := ind_bounds (4 * a3 - 2 * b3 + c3) (c1)
                  have := ind_bounds (4 * a3 + 2 * b3 + c3) (c1)
                  have := ind_bounds (9 * a3 - 3 * b3 + c3) (c1)
                  have := ind_bounds (9 * a3 + 3 * b3 + c3) (c1)
                  have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c1)
                  have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c1)
                  have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c1)
                  have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c1)
                  omega
                exfalso
                have hT : 0 ≤ (c2) := by omega
                have e := rel (c2) hT
                have l1 := lo1 (c2) hT
                have l2 := lo2 (c2) hT
                have l3 := lo3 (c2) hT
                have x1 := ex1 (c2) hT (by omega) (by omega)
                have x2 := ex2 (c2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (c2)
                have := ind_zero (c1) (c2) (by omega)
                have := ind_zero (a1 - b1 + c1) (c2) (by omega)
                have := ind_zero (a1 + b1 + c1) (c2) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
                have := ind_bounds (a2) (c2)
                have := ind_bounds (c2) (c2)
                have := ind_zero (a2 - b2 + c2) (c2) (by omega)
                have := ind_zero (a2 + b2 + c2) (c2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
                have := ind_one (a3) (c2) (by omega)
                have := ind_one (c3) (c2) (by omega)
                have := ind_bounds (a3 - b3 + c3) (c2)
                have := ind_bounds (a3 + b3 + c3) (c2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
                omega
              by_cases h92 : 0 ≤ a1 - b1 + c1 - a3 + b3 - c3
              swap
              · -- branch
                by_cases h93 : 0 ≤ a1 - b1 + c1 - c2
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (c1) := by omega
                  have e := rel (c1) hT
                  have l1 := lo1 (c1) hT
                  have l2 := lo2 (c1) hT
                  have l3 := lo3 (c1) hT
                  have x1 := ex1 (c1) hT (by omega) (by omega)
                  have x2 := ex2 (c1) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x1 x2
                  have := ind_bounds (a1) (c1)
                  have := ind_bounds (c1) (c1)
                  have := ind_bounds (a1 - b1 + c1) (c1)
                  have := ind_zero (a1 + b1 + c1) (c1) (by omega)
                  have := ind_zero (4 * a1 - 2 * b1 + c1) (c1) (by omega)
                  have := ind_zero (4 * a1 + 2 * b1 + c1) (c1) (by omega)
                  have := ind_zero (9 * a1 - 3 * b1 + c1) (c1) (by omega)
                  have := ind_zero (9 * a1 + 3 * b1 + c1) (c1) (by omega)
                  have := ind_zero (a1 - 2 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_zero (a1 + 2 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c1) (by omega)
                  have := ind_bounds (a2) (c1)
                  have := ind_zero (c2) (c1) (by omega)
                  have := ind_zero (a2 - b2 + c2) (c1) (by omega)
                  have := ind_zero (a2 + b2 + c2) (c1) (by omega)
                  have := ind_zero (4 * a2 - 2 * b2 + c2) (c1) (by omega)
                  have := ind_zero (4 * a2 + 2 * b2 + c2) (c1) (by omega)
                  have := ind_zero (9 * a2 - 3 * b2 + c2) (c1) (by omega)
                  have := ind_zero (9 * a2 + 3 * b2 + c2) (c1) (by omega)
                  have := ind_zero (a2 - 2 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_zero (a2 + 2 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c1) (by omega)
                  have := ind_one (a3) (c1) (by omega)
                  have := ind_one (c3) (c1) (by omega)
                  have := ind_bounds (a3 - b3 + c3) (c1)
                  have := ind_bounds (a3 + b3 + c3) (c1)
                  have := ind_bounds (4 * a3 - 2 * b3 + c3) (c1)
                  have := ind_bounds (4 * a3 + 2 * b3 + c3) (c1)
                  have := ind_bounds (9 * a3 - 3 * b3 + c3) (c1)
                  have := ind_bounds (9 * a3 + 3 * b3 + c3) (c1)
                  have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c1)
                  have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c1)
                  have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c1)
                  have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c1)
                  omega
                exfalso
                have hT : 0 ≤ (a1 - b1 + c1) := by omega
                have e := rel (a1 - b1 + c1) hT
                have l1 := lo1 (a1 - b1 + c1) hT
                have l2 := lo2 (a1 - b1 + c1) hT
                have l3 := lo3 (a1 - b1 + c1) hT
                have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x3
                have := ind_one (a1) (a1 - b1 + c1) (by omega)
                have := ind_one (c1) (a1 - b1 + c1) (by omega)
                have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
                have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
                have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
                have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
                have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
                have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
                have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
                have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
                have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
                have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
                have := ind_one (a2) (a1 - b1 + c1) (by omega)
                have := ind_one (c2) (a1 - b1 + c1) (by omega)
                have := ind_bounds (a2 - b2 + c2) (a1 - b1 + c1)
                have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
                have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
                have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
                have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
                have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
                have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
                have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
                have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
                have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
                have := ind_bounds (a3) (a1 - b1 + c1)
                have := ind_bounds (c3) (a1 - b1 + c1)
                have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                omega
              exfalso
              have hT : 0 ≤ (a1 - b1 + c1) := by omega
              have e := rel (a1 - b1 + c1) hT
              have l1 := lo1 (a1 - b1 + c1) hT
              have l2 := lo2 (a1 - b1 + c1) hT
              have l3 := lo3 (a1 - b1 + c1) hT
              have x1 := ex1 (a1 - b1 + c1) hT (by omega) (by omega)
              have x2 := ex2 (a1 - b1 + c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a1 - b1 + c1)
              have := ind_bounds (c1) (a1 - b1 + c1)
              have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
              have := ind_zero (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
              have := ind_bounds (a2) (a1 - b1 + c1)
              have := ind_bounds (c2) (a1 - b1 + c1)
              have := ind_zero (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (a2 + b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
              have := ind_one (a3) (a1 - b1 + c1) (by omega)
              have := ind_one (c3) (a1 - b1 + c1) (by omega)
              have := ind_one (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_bounds (a3 + b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1)
              omega
            exfalso
            have hT : 0 ≤ (c2) := by omega
            have e := rel (c2) hT
            have l1 := lo1 (c2) hT
            have l2 := lo2 (c2) hT
            have l3 := lo3 (c2) hT
            have x3 := ex3 (c2) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x3
            have := ind_bounds (a1) (c2)
            have := ind_bounds (c1) (c2)
            have := ind_bounds (a1 - b1 + c1) (c2)
            have := ind_bounds (a1 + b1 + c1) (c2)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (c2)
            have := ind_bounds (4 * a1 + 2 * b1 + c1) (c2)
            have := ind_bounds (9 * a1 - 3 * b1 + c1) (c2)
            have := ind_bounds (9 * a1 + 3 * b1 + c1) (c2)
            have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c2)
            have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c2)
            have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c2)
            have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c2)
            have := ind_one (a2) (c2) (by omega)
            have := ind_one (c2) (c2) (by omega)
            have := ind_bounds (a2 - b2 + c2) (c2)
            have := ind_bounds (a2 + b2 + c2) (c2)
            have := ind_bounds (4 * a2 - 2 * b2 + c2) (c2)
            have := ind_bounds (4 * a2 + 2 * b2 + c2) (c2)
            have := ind_bounds (9 * a2 - 3 * b2 + c2) (c2)
            have := ind_bounds (9 * a2 + 3 * b2 + c2) (c2)
            have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c2)
            have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c2)
            have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c2)
            have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c2)
            have := ind_bounds (a3) (c2)
            have := ind_zero (c3) (c2) (by omega)
            have := ind_zero (a3 - b3 + c3) (c2) (by omega)
            have := ind_zero (a3 + b3 + c3) (c2) (by omega)
            have := ind_zero (4 * a3 - 2 * b3 + c3) (c2) (by omega)
            have := ind_zero (4 * a3 + 2 * b3 + c3) (c2) (by omega)
            have := ind_zero (9 * a3 - 3 * b3 + c3) (c2) (by omega)
            have := ind_zero (9 * a3 + 3 * b3 + c3) (c2) (by omega)
            have := ind_zero (a3 - 2 * b3 + 4 * c3) (c2) (by omega)
            have := ind_zero (a3 + 2 * b3 + 4 * c3) (c2) (by omega)
            have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c2) (by omega)
            have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c2) (by omega)
            omega
          by_cases h94 : 1 ≤ -a1 + c3
          swap
          · -- branch
            by_cases h95 : 1 ≤ -a1 + b1 - c1 + a2 - b2 + c2
            swap
            · -- branch
              by_cases h96 : 1 ≤ -a1 + c1
              swap
              · -- branch
                by_cases h97 : 1 ≤ a1 - b1 + c1 - a2 + b2 - c2
                swap
                · -- branch
                  by_cases h98 : 1 ≤ -a1 + b1 - c1 + a3 - b3 + c3
                  swap
                  · -- branch
                    by_cases h99 : 1 ≤ a2 - b2 + c2 - a3 + b3 - c3
                    swap
                    · -- branch
                      exact Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                    exfalso
                    have hT : 0 ≤ (a3 - b3 + c3) := by omega
                    have e := rel (a3 - b3 + c3) hT
                    have l1 := lo1 (a3 - b3 + c3) hT
                    have l2 := lo2 (a3 - b3 + c3) hT
                    have l3 := lo3 (a3 - b3 + c3) hT
                    have x1 := ex1 (a3 - b3 + c3) hT (by omega) (by omega)
                    have x2 := ex2 (a3 - b3 + c3) hT (by omega) (by omega)
                    simp only [cntV] at l1 l2 l3 x1 x2
                    have := ind_bounds (a1) (a3 - b3 + c3)
                    have := ind_bounds (c1) (a3 - b3 + c3)
                    have := ind_bounds (a1 - b1 + c1) (a3 - b3 + c3)
                    have := ind_bounds (a1 + b1 + c1) (a3 - b3 + c3)
                    have := ind_zero (4 * a1 - 2 * b1 + c1) (a3 - b3 + c3) (by omega)
                    have := ind_zero (4 * a1 + 2 * b1 + c1) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a1 - 3 * b1 + c1) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a1 + 3 * b1 + c1) (a3 - b3 + c3) (by omega)
                    have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                    have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                    have := ind_bounds (a2) (a3 - b3 + c3)
                    have := ind_bounds (c2) (a3 - b3 + c3)
                    have := ind_zero (a2 - b2 + c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (a2 + b2 + c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                    have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                    have := ind_one (a3) (a3 - b3 + c3) (by omega)
                    have := ind_one (c3) (a3 - b3 + c3) (by omega)
                    have := ind_one (a3 - b3 + c3) (a3 - b3 + c3) (by omega)
                    have := ind_bounds (a3 + b3 + c3) (a3 - b3 + c3)
                    have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 - b3 + c3)
                    have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 - b3 + c3)
                    have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 - b3 + c3)
                    have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 - b3 + c3)
                    have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 - b3 + c3)
                    have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 - b3 + c3)
                    have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 - b3 + c3)
                    have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 - b3 + c3)
                    omega
                  exfalso
                  have hT : 0 ≤ (a1 - b1 + c1) := by omega
                  have e := rel (a1 - b1 + c1) hT
                  have l1 := lo1 (a1 - b1 + c1) hT
                  have l2 := lo2 (a1 - b1 + c1) hT
                  have l3 := lo3 (a1 - b1 + c1) hT
                  have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (a1 - b1 + c1)
                  have := ind_bounds (c1) (a1 - b1 + c1)
                  have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
                  have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
                  have := ind_one (a2) (a1 - b1 + c1) (by omega)
                  have := ind_one (c2) (a1 - b1 + c1) (by omega)
                  have := ind_one (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
                  have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
                  have := ind_bounds (a3) (a1 - b1 + c1)
                  have := ind_bounds (c3) (a1 - b1 + c1)
                  have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
                  omega
                by_cases h100 : 0 ≤ a2 - b2 + c2 - a3 + b3 - c3
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (a2 - b2 + c2) := by omega
                  have e := rel (a2 - b2 + c2) hT
                  have l1 := lo1 (a2 - b2 + c2) hT
                  have l2 := lo2 (a2 - b2 + c2) hT
                  have l3 := lo3 (a2 - b2 + c2) hT
                  have x3 := ex3 (a2 - b2 + c2) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_bounds (a1) (a2 - b2 + c2)
                  have := ind_one (c1) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a1 - b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 + b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2)
                  have := ind_one (a2) (a2 - b2 + c2) (by omega)
                  have := ind_one (c2) (a2 - b2 + c2) (by omega)
                  have := ind_one (a2 - b2 + c2) (a2 - b2 + c2) (by omega)
                  have := ind_bounds (a2 + b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2)
                  have := ind_bounds (a3) (a2 - b2 + c2)
                  have := ind_bounds (c3) (a2 - b2 + c2)
                  have := ind_zero (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 + b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2) (by omega)
                  omega
                exfalso
                have hT : 0 ≤ (a2 - b2 + c2) := by omega
                have e := rel (a2 - b2 + c2) hT
                have l1 := lo1 (a2 - b2 + c2) hT
                have l2 := lo2 (a2 - b2 + c2) hT
                have l3 := lo3 (a2 - b2 + c2) hT
                have x1 := ex1 (a2 - b2 + c2) hT (by omega) (by omega)
                have x2 := ex2 (a2 - b2 + c2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a2 - b2 + c2)
                have := ind_bounds (c1) (a2 - b2 + c2)
                have := ind_zero (a1 - b1 + c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (a1 + b1 + c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
                have := ind_bounds (a2) (a2 - b2 + c2)
                have := ind_bounds (c2) (a2 - b2 + c2)
                have := ind_bounds (a2 - b2 + c2) (a2 - b2 + c2)
                have := ind_zero (a2 + b2 + c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
                have := ind_one (a3) (a2 - b2 + c2) (by omega)
                have := ind_one (c3) (a2 - b2 + c2) (by omega)
                have := ind_one (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
                have := ind_bounds (a3 + b3 + c3) (a2 - b2 + c2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2)
                omega
              exfalso
              have hT : 0 ≤ (a1) := by omega
              have e := rel (a1) hT
              have l1 := lo1 (a1) hT
              have l2 := lo2 (a1) hT
              have l3 := lo3 (a1) hT
              have x1 := ex1 (a1) hT (by omega) (by omega)
              have x2 := ex2 (a1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a1)
              have := ind_zero (c1) (a1) (by omega)
              have := ind_zero (a1 - b1 + c1) (a1) (by omega)
              have := ind_zero (a1 + b1 + c1) (a1) (by omega)
              have := ind_zero (4 * a1 - 2 * b1 + c1) (a1) (by omega)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
              have := ind_bounds (a2) (a1)
              have := ind_bounds (c2) (a1)
              have := ind_zero (a2 - b2 + c2) (a1) (by omega)
              have := ind_zero (a2 + b2 + c2) (a1) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
              have := ind_one (a3) (a1) (by omega)
              have := ind_one (c3) (a1) (by omega)
              have := ind_bounds (a3 - b3 + c3) (a1)
              have := ind_bounds (a3 + b3 + c3) (a1)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
              omega
            by_cases h101 : 0 ≤ a1 - b1 + c1 - a3 + b3 - c3
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (a1 - b1 + c1) := by omega
              have e := rel (a1 - b1 + c1) hT
              have l1 := lo1 (a1 - b1 + c1) hT
              have l2 := lo2 (a1 - b1 + c1) hT
              have l3 := lo3 (a1 - b1 + c1) hT
              have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_one (a1) (a1 - b1 + c1) (by omega)
              have := ind_one (c1) (a1 - b1 + c1) (by omega)
              have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
              have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
              have := ind_one (a2) (a1 - b1 + c1) (by omega)
              have := ind_one (c2) (a1 - b1 + c1) (by omega)
              have := ind_bounds (a2 - b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
              have := ind_bounds (a3) (a1 - b1 + c1)
              have := ind_bounds (c3) (a1 - b1 + c1)
              have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
              omega
            exfalso
            have hT : 0 ≤ (a1 - b1 + c1) := by omega
            have e := rel (a1 - b1 + c1) hT
            have l1 := lo1 (a1 - b1 + c1) hT
            have l2 := lo2 (a1 - b1 + c1) hT
            have l3 := lo3 (a1 - b1 + c1) hT
            have x1 := ex1 (a1 - b1 + c1) hT (by omega) (by omega)
            have x2 := ex2 (a1 - b1 + c1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (a1 - b1 + c1)
            have := ind_bounds (c1) (a1 - b1 + c1)
            have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
            have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
            have := ind_bounds (a2) (a1 - b1 + c1)
            have := ind_bounds (c2) (a1 - b1 + c1)
            have := ind_zero (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (a2 + b2 + c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
            have := ind_one (a3) (a1 - b1 + c1) (by omega)
            have := ind_one (c3) (a1 - b1 + c1) (by omega)
            have := ind_one (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
            have := ind_bounds (a3 + b3 + c3) (a1 - b1 + c1)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1)
            omega
          exfalso
          have hT : 0 ≤ (a1) := by omega
          have e := rel (a1) hT
          have l1 := lo1 (a1) hT
          have l2 := lo2 (a1) hT
          have l3 := lo3 (a1) hT
          have x3 := ex3 (a1) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x3
          have := ind_bounds (a1) (a1)
          have := ind_bounds (c1) (a1)
          have := ind_bounds (a1 - b1 + c1) (a1)
          have := ind_bounds (a1 + b1 + c1) (a1)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
          have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
          have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
          have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
          have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
          have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
          have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
          have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
          have := ind_one (a2) (a1) (by omega)
          have := ind_one (c2) (a1) (by omega)
          have := ind_bounds (a2 - b2 + c2) (a1)
          have := ind_bounds (a2 + b2 + c2) (a1)
          have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
          have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
          have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
          have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
          have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
          have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
          have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
          have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
          have := ind_bounds (a3) (a1)
          have := ind_zero (c3) (a1) (by omega)
          have := ind_zero (a3 - b3 + c3) (a1) (by omega)
          have := ind_zero (a3 + b3 + c3) (a1) (by omega)
          have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
          have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
          have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
          have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
          have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
          have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
          have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
          have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
          omega
        exfalso
        have hT : 0 ≤ (c1) := by omega
        have e := rel (c1) hT
        have l1 := lo1 (c1) hT
        have l2 := lo2 (c1) hT
        have l3 := lo3 (c1) hT
        have x1 := ex1 (c1) hT (by omega) (by omega)
        have x2 := ex2 (c1) hT (by omega) (by omega)
        simp only [cntV] at l1 l2 l3 x1 x2
        have := ind_bounds (a1) (c1)
        have := ind_bounds (c1) (c1)
        have := ind_bounds (a1 - b1 + c1) (c1)
        have := ind_bounds (a1 + b1 + c1) (c1)
        have := ind_zero (4 * a1 - 2 * b1 + c1) (c1) (by omega)
        have := ind_zero (4 * a1 + 2 * b1 + c1) (c1) (by omega)
        have := ind_zero (9 * a1 - 3 * b1 + c1) (c1) (by omega)
        have := ind_zero (9 * a1 + 3 * b1 + c1) (c1) (by omega)
        have := ind_zero (a1 - 2 * b1 + 4 * c1) (c1) (by omega)
        have := ind_zero (a1 + 2 * b1 + 4 * c1) (c1) (by omega)
        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c1) (by omega)
        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c1) (by omega)
        have := ind_bounds (a2) (c1)
        have := ind_bounds (c2) (c1)
        have := ind_zero (a2 - b2 + c2) (c1) (by omega)
        have := ind_zero (a2 + b2 + c2) (c1) (by omega)
        have := ind_zero (4 * a2 - 2 * b2 + c2) (c1) (by omega)
        have := ind_zero (4 * a2 + 2 * b2 + c2) (c1) (by omega)
        have := ind_zero (9 * a2 - 3 * b2 + c2) (c1) (by omega)
        have := ind_zero (9 * a2 + 3 * b2 + c2) (c1) (by omega)
        have := ind_zero (a2 - 2 * b2 + 4 * c2) (c1) (by omega)
        have := ind_zero (a2 + 2 * b2 + 4 * c2) (c1) (by omega)
        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c1) (by omega)
        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c1) (by omega)
        have := ind_one (a3) (c1) (by omega)
        have := ind_one (c3) (c1) (by omega)
        have := ind_one (a3 - b3 + c3) (c1) (by omega)
        have := ind_bounds (a3 + b3 + c3) (c1)
        have := ind_bounds (4 * a3 - 2 * b3 + c3) (c1)
        have := ind_bounds (4 * a3 + 2 * b3 + c3) (c1)
        have := ind_bounds (9 * a3 - 3 * b3 + c3) (c1)
        have := ind_bounds (9 * a3 + 3 * b3 + c3) (c1)
        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c1)
        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c1)
        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c1)
        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c1)
        omega
      exfalso
      have hT : 0 ≤ (a1) := by omega
      have e := rel (a1) hT
      have l1 := lo1 (a1) hT
      have l2 := lo2 (a1) hT
      have l3 := lo3 (a1) hT
      have x3 := ex3 (a1) hT (by omega) (by omega)
      simp only [cntV] at l1 l2 l3 x3
      have := ind_one (a1) (a1) (by omega)
      have := ind_bounds (c1) (a1)
      have := ind_bounds (a1 - b1 + c1) (a1)
      have := ind_bounds (a1 + b1 + c1) (a1)
      have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
      have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
      have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
      have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
      have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
      have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
      have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
      have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
      have := ind_bounds (a2) (a1)
      have := ind_bounds (c2) (a1)
      have := ind_bounds (a2 - b2 + c2) (a1)
      have := ind_bounds (a2 + b2 + c2) (a1)
      have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
      have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
      have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
      have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
      have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
      have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
      have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
      have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
      have := ind_zero (a3) (a1) (by omega)
      have := ind_zero (c3) (a1) (by omega)
      have := ind_zero (a3 - b3 + c3) (a1) (by omega)
      have := ind_zero (a3 + b3 + c3) (a1) (by omega)
      have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
      have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
      have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
      have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
      have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
      have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
      have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
      have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
      omega
    exfalso
    have hT : 0 ≤ (a3) := by omega
    have e := rel (a3) hT
    have l1 := lo1 (a3) hT
    have l2 := lo2 (a3) hT
    have l3 := lo3 (a3) hT
    have x1 := ex1 (a3) hT (by omega) (by omega)
    have x2 := ex2 (a3) hT (by omega) (by omega)
    simp only [cntV] at l1 l2 l3 x1 x2
    have := ind_bounds (a1) (a3)
    have := ind_bounds (c1) (a3)
    have := ind_zero (a1 - b1 + c1) (a3) (by omega)
    have := ind_zero (a1 + b1 + c1) (a3) (by omega)
    have := ind_zero (4 * a1 - 2 * b1 + c1) (a3) (by omega)
    have := ind_zero (4 * a1 + 2 * b1 + c1) (a3) (by omega)
    have := ind_zero (9 * a1 - 3 * b1 + c1) (a3) (by omega)
    have := ind_zero (9 * a1 + 3 * b1 + c1) (a3) (by omega)
    have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (a2) (a3) (by omega)
    have := ind_zero (c2) (a3) (by omega)
    have := ind_zero (a2 - b2 + c2) (a3) (by omega)
    have := ind_zero (a2 + b2 + c2) (a3) (by omega)
    have := ind_zero (4 * a2 - 2 * b2 + c2) (a3) (by omega)
    have := ind_zero (4 * a2 + 2 * b2 + c2) (a3) (by omega)
    have := ind_zero (9 * a2 - 3 * b2 + c2) (a3) (by omega)
    have := ind_zero (9 * a2 + 3 * b2 + c2) (a3) (by omega)
    have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3) (by omega)
    have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3) (by omega)
    have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3) (by omega)
    have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3) (by omega)
    have := ind_one (a3) (a3) (by omega)
    have := ind_bounds (c3) (a3)
    have := ind_bounds (a3 - b3 + c3) (a3)
    have := ind_bounds (a3 + b3 + c3) (a3)
    have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3)
    have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3)
    have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3)
    have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3)
    have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3)
    have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3)
    have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3)
    have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3)
    omega
  by_cases h102 : 0 ≤ a2 - a3
  swap
  · -- branch
    exfalso
    have hT : 0 ≤ (a2) := by omega
    have e := rel (a2) hT
    have l1 := lo1 (a2) hT
    have l2 := lo2 (a2) hT
    have l3 := lo3 (a2) hT
    have x3 := ex3 (a2) hT (by omega) (by omega)
    simp only [cntV] at l1 l2 l3 x3
    have := ind_bounds (a1) (a2)
    have := ind_bounds (c1) (a2)
    have := ind_bounds (a1 - b1 + c1) (a2)
    have := ind_bounds (a1 + b1 + c1) (a2)
    have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
    have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
    have := ind_bounds (9 * a1 - 3 * b1 + c1) (a2)
    have := ind_bounds (9 * a1 + 3 * b1 + c1) (a2)
    have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a2)
    have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a2)
    have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a2)
    have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a2)
    have := ind_one (a2) (a2) (by omega)
    have := ind_bounds (c2) (a2)
    have := ind_bounds (a2 - b2 + c2) (a2)
    have := ind_bounds (a2 + b2 + c2) (a2)
    have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2)
    have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2)
    have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2)
    have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2)
    have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2)
    have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2)
    have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2)
    have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2)
    have := ind_zero (a3) (a2) (by omega)
    have := ind_zero (c3) (a2) (by omega)
    have := ind_zero (a3 - b3 + c3) (a2) (by omega)
    have := ind_zero (a3 + b3 + c3) (a2) (by omega)
    have := ind_zero (4 * a3 - 2 * b3 + c3) (a2) (by omega)
    have := ind_zero (4 * a3 + 2 * b3 + c3) (a2) (by omega)
    have := ind_zero (9 * a3 - 3 * b3 + c3) (a2) (by omega)
    have := ind_zero (9 * a3 + 3 * b3 + c3) (a2) (by omega)
    have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2) (by omega)
    have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2) (by omega)
    have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2) (by omega)
    have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2) (by omega)
    omega
  by_cases h103 : 1 ≤ -a2 + c3
  swap
  · -- branch
    by_cases h104 : 1 ≤ a2 - a3
    swap
    · -- branch
      by_cases h105 : 1 ≤ a1 - b1 + c1 - a2 + b2 - c2
      swap
      · -- branch
        by_cases h106 : 1 ≤ 4 * a1 - 2 * b1 + c1 - c2
        swap
        · -- branch
          by_cases h107 : 0 ≤ a2 - a3 + b3 - c3
          swap
          · -- branch
            exfalso
            have hT : 0 ≤ (a2) := by omega
            have e := rel (a2) hT
            have l1 := lo1 (a2) hT
            have l2 := lo2 (a2) hT
            have l3 := lo3 (a2) hT
            have x1 := ex1 (a2) hT (by omega) (by omega)
            have x2 := ex2 (a2) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (a2)
            have := ind_bounds (c1) (a2)
            have := ind_bounds (a1 - b1 + c1) (a2)
            have := ind_zero (a1 + b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_bounds (a2) (a2)
            have := ind_zero (c2) (a2) (by omega)
            have := ind_zero (a2 - b2 + c2) (a2) (by omega)
            have := ind_zero (a2 + b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_one (a3) (a2) (by omega)
            have := ind_one (c3) (a2) (by omega)
            have := ind_bounds (a3 - b3 + c3) (a2)
            have := ind_bounds (a3 + b3 + c3) (a2)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
            omega
          exfalso
          have hT : 0 ≤ (a2) := by omega
          have e := rel (a2) hT
          have l1 := lo1 (a2) hT
          have l2 := lo2 (a2) hT
          have l3 := lo3 (a2) hT
          have x1 := ex1 (a2) hT (by omega) (by omega)
          have x2 := ex2 (a2) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (a2)
          have := ind_bounds (c1) (a2)
          have := ind_bounds (a1 - b1 + c1) (a2)
          have := ind_bounds (a1 + b1 + c1) (a2)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
          have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
          have := ind_bounds (a2) (a2)
          have := ind_zero (c2) (a2) (by omega)
          have := ind_zero (a2 - b2 + c2) (a2) (by omega)
          have := ind_zero (a2 + b2 + c2) (a2) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
          have := ind_one (a3) (a2) (by omega)
          have := ind_one (c3) (a2) (by omega)
          have := ind_one (a3 - b3 + c3) (a2) (by omega)
          have := ind_bounds (a3 + b3 + c3) (a2)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
          omega
        by_cases h108 : 1 ≤ a2 - b2
        swap
        · -- branch
          by_cases h109 : 0 ≤ a2 - a3 + b3 - c3
          swap
          · -- branch
            exfalso
            have hT : 0 ≤ (a2) := by omega
            have e := rel (a2) hT
            have l1 := lo1 (a2) hT
            have l2 := lo2 (a2) hT
            have l3 := lo3 (a2) hT
            have x1 := ex1 (a2) hT (by omega) (by omega)
            have x2 := ex2 (a2) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (a2)
            have := ind_bounds (c1) (a2)
            have := ind_bounds (a1 - b1 + c1) (a2)
            have := ind_zero (a1 + b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_bounds (a2) (a2)
            have := ind_zero (c2) (a2) (by omega)
            have := ind_zero (a2 - b2 + c2) (a2) (by omega)
            have := ind_zero (a2 + b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_one (a3) (a2) (by omega)
            have := ind_one (c3) (a2) (by omega)
            have := ind_bounds (a3 - b3 + c3) (a2)
            have := ind_bounds (a3 + b3 + c3) (a2)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
            omega
          exfalso
          have hT : 0 ≤ (a2) := by omega
          have e := rel (a2) hT
          have l1 := lo1 (a2) hT
          have l2 := lo2 (a2) hT
          have l3 := lo3 (a2) hT
          have x1 := ex1 (a2) hT (by omega) (by omega)
          have x2 := ex2 (a2) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (a2)
          have := ind_bounds (c1) (a2)
          have := ind_bounds (a1 - b1 + c1) (a2)
          have := ind_bounds (a1 + b1 + c1) (a2)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a2)
          have := ind_bounds (4 * a1 + 2 * b1 + c1) (a2)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
          have := ind_bounds (a2) (a2)
          have := ind_zero (c2) (a2) (by omega)
          have := ind_zero (a2 - b2 + c2) (a2) (by omega)
          have := ind_zero (a2 + b2 + c2) (a2) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
          have := ind_one (a3) (a2) (by omega)
          have := ind_one (c3) (a2) (by omega)
          have := ind_one (a3 - b3 + c3) (a2) (by omega)
          have := ind_bounds (a3 + b3 + c3) (a2)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
          omega
        by_cases h110 : 0 ≤ c2 - a3 + b3 - c3
        swap
        · -- branch
          by_cases h111 : 1 ≤ c1 - c2
          swap
          · -- branch
            exfalso
            have hT : 0 ≤ (a2) := by omega
            have e := rel (a2) hT
            have l1 := lo1 (a2) hT
            have l2 := lo2 (a2) hT
            have l3 := lo3 (a2) hT
            have x1 := ex1 (a2) hT (by omega) (by omega)
            have x2 := ex2 (a2) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (a2)
            have := ind_bounds (c1) (a2)
            have := ind_bounds (a1 - b1 + c1) (a2)
            have := ind_zero (a1 + b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_bounds (a2) (a2)
            have := ind_zero (c2) (a2) (by omega)
            have := ind_zero (a2 - b2 + c2) (a2) (by omega)
            have := ind_zero (a2 + b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_one (a3) (a2) (by omega)
            have := ind_one (c3) (a2) (by omega)
            have := ind_bounds (a3 - b3 + c3) (a2)
            have := ind_bounds (a3 + b3 + c3) (a2)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
            omega
          exfalso
          have hT : 0 ≤ (c2) := by omega
          have e := rel (c2) hT
          have l1 := lo1 (c2) hT
          have l2 := lo2 (c2) hT
          have l3 := lo3 (c2) hT
          have x1 := ex1 (c2) hT (by omega) (by omega)
          have x2 := ex2 (c2) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (c2)
          have := ind_zero (c1) (c2) (by omega)
          have := ind_zero (a1 - b1 + c1) (c2) (by omega)
          have := ind_zero (a1 + b1 + c1) (c2) (by omega)
          have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
          have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
          have := ind_bounds (a2) (c2)
          have := ind_bounds (c2) (c2)
          have := ind_zero (a2 - b2 + c2) (c2) (by omega)
          have := ind_zero (a2 + b2 + c2) (c2) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
          have := ind_one (a3) (c2) (by omega)
          have := ind_one (c3) (c2) (by omega)
          have := ind_bounds (a3 - b3 + c3) (c2)
          have := ind_bounds (a3 + b3 + c3) (c2)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
          omega
        exfalso
        have hT : 0 ≤ (c2) := by omega
        have e := rel (c2) hT
        have l1 := lo1 (c2) hT
        have l2 := lo2 (c2) hT
        have l3 := lo3 (c2) hT
        have x1 := ex1 (c2) hT (by omega) (by omega)
        have x2 := ex2 (c2) hT (by omega) (by omega)
        simp only [cntV] at l1 l2 l3 x1 x2
        have := ind_bounds (a1) (c2)
        have := ind_bounds (c1) (c2)
        have := ind_bounds (a1 - b1 + c1) (c2)
        have := ind_bounds (a1 + b1 + c1) (c2)
        have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
        have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
        have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
        have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
        have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
        have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
        have := ind_bounds (a2) (c2)
        have := ind_bounds (c2) (c2)
        have := ind_zero (a2 - b2 + c2) (c2) (by omega)
        have := ind_zero (a2 + b2 + c2) (c2) (by omega)
        have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
        have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
        have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
        have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
        have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
        have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
        have := ind_one (a3) (c2) (by omega)
        have := ind_one (c3) (c2) (by omega)
        have := ind_one (a3 - b3 + c3) (c2) (by omega)
        have := ind_bounds (a3 + b3 + c3) (c2)
        have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
        have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
        have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
        have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
        omega
      by_cases h112 : 1 ≤ 2 * b2
      swap
      · -- branch
        by_cases h113 : 0 ≤ c2 - a3 + b3 - c3
        swap
        · -- branch
          by_cases h114 : 1 ≤ c1 - c2
          swap
          · -- branch
            exfalso
            have hT : 0 ≤ (a2) := by omega
            have e := rel (a2) hT
            have l1 := lo1 (a2) hT
            have l2 := lo2 (a2) hT
            have l3 := lo3 (a2) hT
            have x1 := ex1 (a2) hT (by omega) (by omega)
            have x2 := ex2 (a2) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (a2)
            have := ind_bounds (c1) (a2)
            have := ind_bounds (a1 - b1 + c1) (a2)
            have := ind_zero (a1 + b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
            have := ind_bounds (a2) (a2)
            have := ind_zero (c2) (a2) (by omega)
            have := ind_zero (a2 - b2 + c2) (a2) (by omega)
            have := ind_zero (a2 + b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
            have := ind_one (a3) (a2) (by omega)
            have := ind_one (c3) (a2) (by omega)
            have := ind_bounds (a3 - b3 + c3) (a2)
            have := ind_bounds (a3 + b3 + c3) (a2)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
            omega
          exfalso
          have hT : 0 ≤ (c2) := by omega
          have e := rel (c2) hT
          have l1 := lo1 (c2) hT
          have l2 := lo2 (c2) hT
          have l3 := lo3 (c2) hT
          have x1 := ex1 (c2) hT (by omega) (by omega)
          have x2 := ex2 (c2) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (c2)
          have := ind_zero (c1) (c2) (by omega)
          have := ind_zero (a1 - b1 + c1) (c2) (by omega)
          have := ind_zero (a1 + b1 + c1) (c2) (by omega)
          have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
          have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
          have := ind_bounds (a2) (c2)
          have := ind_bounds (c2) (c2)
          have := ind_zero (a2 - b2 + c2) (c2) (by omega)
          have := ind_zero (a2 + b2 + c2) (c2) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
          have := ind_one (a3) (c2) (by omega)
          have := ind_one (c3) (c2) (by omega)
          have := ind_bounds (a3 - b3 + c3) (c2)
          have := ind_bounds (a3 + b3 + c3) (c2)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
          omega
        exfalso
        have hT : 0 ≤ (c2) := by omega
        have e := rel (c2) hT
        have l1 := lo1 (c2) hT
        have l2 := lo2 (c2) hT
        have l3 := lo3 (c2) hT
        have x1 := ex1 (c2) hT (by omega) (by omega)
        have x2 := ex2 (c2) hT (by omega) (by omega)
        simp only [cntV] at l1 l2 l3 x1 x2
        have := ind_bounds (a1) (c2)
        have := ind_bounds (c1) (c2)
        have := ind_bounds (a1 - b1 + c1) (c2)
        have := ind_bounds (a1 + b1 + c1) (c2)
        have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
        have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
        have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
        have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
        have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
        have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
        have := ind_bounds (a2) (c2)
        have := ind_bounds (c2) (c2)
        have := ind_zero (a2 - b2 + c2) (c2) (by omega)
        have := ind_zero (a2 + b2 + c2) (c2) (by omega)
        have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
        have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
        have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
        have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
        have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
        have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
        have := ind_one (a3) (c2) (by omega)
        have := ind_one (c3) (c2) (by omega)
        have := ind_one (a3 - b3 + c3) (c2) (by omega)
        have := ind_bounds (a3 + b3 + c3) (c2)
        have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
        have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
        have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
        have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
        omega
      by_cases h115 : 0 ≤ a2 - b2 + c2 - a3 + b3 - c3
      swap
      · -- branch
        by_cases h116 : 1 ≤ -a1 + b1 - c1 + a2 + b2 + c2
        swap
        · -- branch
          by_cases h117 : 1 ≤ -c1 + a2 + b2 + c2
          swap
          · -- branch
            by_cases h118 : 1 ≤ -a1 + a2 + b2 + c2
            swap
            · -- branch
              by_cases h119 : 0 ≤ -2 * b3
              swap
              · -- branch
                exfalso
                have hT : 0 ≤ (a3 - b3 + c3) := by omega
                have e := rel (a3 - b3 + c3) hT
                have l1 := lo1 (a3 - b3 + c3) hT
                have l2 := lo2 (a3 - b3 + c3) hT
                have l3 := lo3 (a3 - b3 + c3) hT
                have x1 := ex1 (a3 - b3 + c3) hT (by omega) (by omega)
                have x2 := ex2 (a3 - b3 + c3) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a3 - b3 + c3)
                have := ind_bounds (c1) (a3 - b3 + c3)
                have := ind_zero (a1 - b1 + c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (a1 + b1 + c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
                have := ind_bounds (a2) (a3 - b3 + c3)
                have := ind_bounds (c2) (a3 - b3 + c3)
                have := ind_bounds (a2 - b2 + c2) (a3 - b3 + c3)
                have := ind_zero (a2 + b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
                have := ind_one (a3) (a3 - b3 + c3) (by omega)
                have := ind_one (c3) (a3 - b3 + c3) (by omega)
                have := ind_one (a3 - b3 + c3) (a3 - b3 + c3) (by omega)
                have := ind_bounds (a3 + b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 - b3 + c3)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 - b3 + c3)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 - b3 + c3)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 - b3 + c3)
                omega
              exfalso
              have hT : 0 ≤ (a3 - b3 + c3) := by omega
              have e := rel (a3 - b3 + c3) hT
              have l1 := lo1 (a3 - b3 + c3) hT
              have l2 := lo2 (a3 - b3 + c3) hT
              have l3 := lo3 (a3 - b3 + c3) hT
              have x1 := ex1 (a3 - b3 + c3) hT (by omega) (by omega)
              have x2 := ex2 (a3 - b3 + c3) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a3 - b3 + c3)
              have := ind_bounds (c1) (a3 - b3 + c3)
              have := ind_bounds (a1 - b1 + c1) (a3 - b3 + c3)
              have := ind_bounds (a1 + b1 + c1) (a3 - b3 + c3)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (a3 - b3 + c3)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a3 - b3 + c3) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 - b3 + c3) (by omega)
              have := ind_bounds (a2) (a3 - b3 + c3)
              have := ind_bounds (c2) (a3 - b3 + c3)
              have := ind_bounds (a2 - b2 + c2) (a3 - b3 + c3)
              have := ind_zero (a2 + b2 + c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 - b3 + c3) (by omega)
              have := ind_one (a3) (a3 - b3 + c3) (by omega)
              have := ind_one (c3) (a3 - b3 + c3) (by omega)
              have := ind_one (a3 - b3 + c3) (a3 - b3 + c3) (by omega)
              have := ind_one (a3 + b3 + c3) (a3 - b3 + c3) (by omega)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 - b3 + c3)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 - b3 + c3)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 - b3 + c3)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 - b3 + c3)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 - b3 + c3)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 - b3 + c3)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 - b3 + c3)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 - b3 + c3)
              omega
            by_cases h120 : 0 ≤ a1 - a3 + b3 - c3
            swap
            · -- branch
              by_cases h121 : 1 ≤ a2 - b2
              swap
              · -- branch
                by_cases h122 : 1 ≤ -a2 + c2
                swap
                · -- branch
                  exfalso
                  have hT : 0 ≤ (a1) := by omega
                  have e := rel (a1) hT
                  have l1 := lo1 (a1) hT
                  have l2 := lo2 (a1) hT
                  have l3 := lo3 (a1) hT
                  have x3 := ex3 (a1) hT (by omega) (by omega)
                  simp only [cntV] at l1 l2 l3 x3
                  have := ind_one (a1) (a1) (by omega)
                  have := ind_bounds (c1) (a1)
                  have := ind_bounds (a1 - b1 + c1) (a1)
                  have := ind_bounds (a1 + b1 + c1) (a1)
                  have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
                  have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1)
                  have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1)
                  have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1)
                  have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1)
                  have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1)
                  have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1)
                  have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1)
                  have := ind_one (a2) (a1) (by omega)
                  have := ind_one (c2) (a1) (by omega)
                  have := ind_one (a2 - b2 + c2) (a1) (by omega)
                  have := ind_bounds (a2 + b2 + c2) (a1)
                  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1)
                  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1)
                  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1)
                  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1)
                  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1)
                  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1)
                  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1)
                  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1)
                  have := ind_bounds (a3) (a1)
                  have := ind_bounds (c3) (a1)
                  have := ind_zero (a3 - b3 + c3) (a1) (by omega)
                  have := ind_zero (a3 + b3 + c3) (a1) (by omega)
                  have := ind_zero (4 * a3 - 2 * b3 + c3) (a1) (by omega)
                  have := ind_zero (4 * a3 + 2 * b3 + c3) (a1) (by omega)
                  have := ind_zero (9 * a3 - 3 * b3 + c3) (a1) (by omega)
                  have := ind_zero (9 * a3 + 3 * b3 + c3) (a1) (by omega)
                  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1) (by omega)
                  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1) (by omega)
                  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1) (by omega)
                  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1) (by omega)
                  omega
                exfalso
                have hT : 0 ≤ (a2) := by omega
                have e := rel (a2) hT
                have l1 := lo1 (a2) hT
                have l2 := lo2 (a2) hT
                have l3 := lo3 (a2) hT
                have x1 := ex1 (a2) hT (by omega) (by omega)
                have x2 := ex2 (a2) hT (by omega) (by omega)
                simp only [cntV] at l1 l2 l3 x1 x2
                have := ind_bounds (a1) (a2)
                have := ind_bounds (c1) (a2)
                have := ind_bounds (a1 - b1 + c1) (a2)
                have := ind_zero (a1 + b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
                have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
                have := ind_bounds (a2) (a2)
                have := ind_zero (c2) (a2) (by omega)
                have := ind_zero (a2 - b2 + c2) (a2) (by omega)
                have := ind_zero (a2 + b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 - 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (4 * a2 + 2 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 3 * b2 + c2) (a2) (by omega)
                have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2) (by omega)
                have := ind_one (a3) (a2) (by omega)
                have := ind_one (c3) (a2) (by omega)
                have := ind_bounds (a3 - b3 + c3) (a2)
                have := ind_bounds (a3 + b3 + c3) (a2)
                have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2)
                have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2)
                have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2)
                have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2)
                have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2)
                omega
              exfalso
              have hT : 0 ≤ (c2) := by omega
              have e := rel (c2) hT
              have l1 := lo1 (c2) hT
              have l2 := lo2 (c2) hT
              have l3 := lo3 (c2) hT
              have x1 := ex1 (c2) hT (by omega) (by omega)
              have x2 := ex2 (c2) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (c2)
              have := ind_zero (c1) (c2) (by omega)
              have := ind_zero (a1 - b1 + c1) (c2) (by omega)
              have := ind_zero (a1 + b1 + c1) (c2) (by omega)
              have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
              have := ind_bounds (a2) (c2)
              have := ind_bounds (c2) (c2)
              have := ind_zero (a2 - b2 + c2) (c2) (by omega)
              have := ind_zero (a2 + b2 + c2) (c2) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
              have := ind_one (a3) (c2) (by omega)
              have := ind_one (c3) (c2) (by omega)
              have := ind_bounds (a3 - b3 + c3) (c2)
              have := ind_bounds (a3 + b3 + c3) (c2)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
              omega
            by_cases h123 : 0 ≤ a1 - a3 - b3 - c3
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (a1) := by omega
              have e := rel (a1) hT
              have l1 := lo1 (a1) hT
              have l2 := lo2 (a1) hT
              have l3 := lo3 (a1) hT
              have x1 := ex1 (a1) hT (by omega) (by omega)
              have x2 := ex2 (a1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x1 x2
              have := ind_bounds (a1) (a1)
              have := ind_bounds (c1) (a1)
              have := ind_zero (a1 - b1 + c1) (a1) (by omega)
              have := ind_zero (a1 + b1 + c1) (a1) (by omega)
              have := ind_zero (4 * a1 - 2 * b1 + c1) (a1) (by omega)
              have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
              have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
              have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
              have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
              have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
              have := ind_bounds (a2) (a1)
              have := ind_bounds (c2) (a1)
              have := ind_bounds (a2 - b2 + c2) (a1)
              have := ind_zero (a2 + b2 + c2) (a1) (by omega)
              have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
              have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
              have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
              have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
              have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
              have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
              have := ind_one (a3) (a1) (by omega)
              have := ind_one (c3) (a1) (by omega)
              have := ind_one (a3 - b3 + c3) (a1) (by omega)
              have := ind_bounds (a3 + b3 + c3) (a1)
              have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
              have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
              have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
              have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
              have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
              have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
              have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
              have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
              omega
            exfalso
            have hT : 0 ≤ (a1) := by omega
            have e := rel (a1) hT
            have l1 := lo1 (a1) hT
            have l2 := lo2 (a1) hT
            have l3 := lo3 (a1) hT
            have x1 := ex1 (a1) hT (by omega) (by omega)
            have x2 := ex2 (a1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (a1)
            have := ind_bounds (c1) (a1)
            have := ind_bounds (a1 - b1 + c1) (a1)
            have := ind_bounds (a1 + b1 + c1) (a1)
            have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (a1) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (a1) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (a1) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1) (by omega)
            have := ind_bounds (a2) (a1)
            have := ind_bounds (c2) (a1)
            have := ind_bounds (a2 - b2 + c2) (a1)
            have := ind_zero (a2 + b2 + c2) (a1) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (a1) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (a1) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (a1) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (a1) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1) (by omega)
            have := ind_one (a3) (a1) (by omega)
            have := ind_one (c3) (a1) (by omega)
            have := ind_one (a3 - b3 + c3) (a1) (by omega)
            have := ind_one (a3 + b3 + c3) (a1) (by omega)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1)
            omega
          by_cases h124 : 0 ≤ c1 - a3 + b3 - c3
          swap
          · -- branch
            by_cases h125 : 1 ≤ a2 - b2
            swap
            · -- branch
              exfalso
              have hT : 0 ≤ (c1) := by omega
              have e := rel (c1) hT
              have l1 := lo1 (c1) hT
              have l2 := lo2 (c1) hT
              have l3 := lo3 (c1) hT
              have x3 := ex3 (c1) hT (by omega) (by omega)
              simp only [cntV] at l1 l2 l3 x3
              have := ind_bounds (a1) (c1)
              have := ind_one (c1) (c1) (by omega)
              have := ind_bounds (a1 - b1 + c1) (c1)
              have := ind_bounds (a1 + b1 + c1) (c1)
              have := ind_bounds (4 * a1 - 2 * b1 + c1) (c1)
              have := ind_bounds (4 * a1 + 2 * b1 + c1) (c1)
              have := ind_bounds (9 * a1 - 3 * b1 + c1) (c1)
              have := ind_bounds (9 * a1 + 3 * b1 + c1) (c1)
              have := ind_bounds (a1 - 2 * b1 + 4 * c1) (c1)
              have := ind_bounds (a1 + 2 * b1 + 4 * c1) (c1)
              have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (c1)
              have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (c1)
              have := ind_one (a2) (c1) (by omega)
              have := ind_one (c2) (c1) (by omega)
              have := ind_one (a2 - b2 + c2) (c1) (by omega)
              have := ind_bounds (a2 + b2 + c2) (c1)
              have := ind_bounds (4 * a2 - 2 * b2 + c2) (c1)
              have := ind_bounds (4 * a2 + 2 * b2 + c2) (c1)
              have := ind_bounds (9 * a2 - 3 * b2 + c2) (c1)
              have := ind_bounds (9 * a2 + 3 * b2 + c2) (c1)
              have := ind_bounds (a2 - 2 * b2 + 4 * c2) (c1)
              have := ind_bounds (a2 + 2 * b2 + 4 * c2) (c1)
              have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (c1)
              have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (c1)
              have := ind_bounds (a3) (c1)
              have := ind_bounds (c3) (c1)
              have := ind_zero (a3 - b3 + c3) (c1) (by omega)
              have := ind_zero (a3 + b3 + c3) (c1) (by omega)
              have := ind_zero (4 * a3 - 2 * b3 + c3) (c1) (by omega)
              have := ind_zero (4 * a3 + 2 * b3 + c3) (c1) (by omega)
              have := ind_zero (9 * a3 - 3 * b3 + c3) (c1) (by omega)
              have := ind_zero (9 * a3 + 3 * b3 + c3) (c1) (by omega)
              have := ind_zero (a3 - 2 * b3 + 4 * c3) (c1) (by omega)
              have := ind_zero (a3 + 2 * b3 + 4 * c3) (c1) (by omega)
              have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (c1) (by omega)
              have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (c1) (by omega)
              omega
            exfalso
            have hT : 0 ≤ (c2) := by omega
            have e := rel (c2) hT
            have l1 := lo1 (c2) hT
            have l2 := lo2 (c2) hT
            have l3 := lo3 (c2) hT
            have x1 := ex1 (c2) hT (by omega) (by omega)
            have x2 := ex2 (c2) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (c2)
            have := ind_zero (c1) (c2) (by omega)
            have := ind_zero (a1 - b1 + c1) (c2) (by omega)
            have := ind_zero (a1 + b1 + c1) (c2) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (c2) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (c2) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (c2) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (c2) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (c2) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (c2) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c2) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c2) (by omega)
            have := ind_bounds (a2) (c2)
            have := ind_bounds (c2) (c2)
            have := ind_zero (a2 - b2 + c2) (c2) (by omega)
            have := ind_zero (a2 + b2 + c2) (c2) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (c2) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (c2) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (c2) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (c2) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (c2) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (c2) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c2) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c2) (by omega)
            have := ind_one (a3) (c2) (by omega)
            have := ind_one (c3) (c2) (by omega)
            have := ind_bounds (a3 - b3 + c3) (c2)
            have := ind_bounds (a3 + b3 + c3) (c2)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (c2)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (c2)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (c2)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (c2)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c2)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c2)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c2)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c2)
            omega
          by_cases h126 : 0 ≤ c1 - a3 - b3 - c3
          swap
          · -- branch
            exfalso
            have hT : 0 ≤ (c1) := by omega
            have e := rel (c1) hT
            have l1 := lo1 (c1) hT
            have l2 := lo2 (c1) hT
            have l3 := lo3 (c1) hT
            have x1 := ex1 (c1) hT (by omega) (by omega)
            have x2 := ex2 (c1) hT (by omega) (by omega)
            simp only [cntV] at l1 l2 l3 x1 x2
            have := ind_bounds (a1) (c1)
            have := ind_bounds (c1) (c1)
            have := ind_zero (a1 - b1 + c1) (c1) (by omega)
            have := ind_zero (a1 + b1 + c1) (c1) (by omega)
            have := ind_zero (4 * a1 - 2 * b1 + c1) (c1) (by omega)
            have := ind_zero (4 * a1 + 2 * b1 + c1) (c1) (by omega)
            have := ind_zero (9 * a1 - 3 * b1 + c1) (c1) (by omega)
            have := ind_zero (9 * a1 + 3 * b1 + c1) (c1) (by omega)
            have := ind_zero (a1 - 2 * b1 + 4 * c1) (c1) (by omega)
            have := ind_zero (a1 + 2 * b1 + 4 * c1) (c1) (by omega)
            have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c1) (by omega)
            have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c1) (by omega)
            have := ind_bounds (a2) (c1)
            have := ind_bounds (c2) (c1)
            have := ind_bounds (a2 - b2 + c2) (c1)
            have := ind_zero (a2 + b2 + c2) (c1) (by omega)
            have := ind_zero (4 * a2 - 2 * b2 + c2) (c1) (by omega)
            have := ind_zero (4 * a2 + 2 * b2 + c2) (c1) (by omega)
            have := ind_zero (9 * a2 - 3 * b2 + c2) (c1) (by omega)
            have := ind_zero (9 * a2 + 3 * b2 + c2) (c1) (by omega)
            have := ind_zero (a2 - 2 * b2 + 4 * c2) (c1) (by omega)
            have := ind_zero (a2 + 2 * b2 + 4 * c2) (c1) (by omega)
            have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c1) (by omega)
            have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c1) (by omega)
            have := ind_one (a3) (c1) (by omega)
            have := ind_one (c3) (c1) (by omega)
            have := ind_one (a3 - b3 + c3) (c1) (by omega)
            have := ind_bounds (a3 + b3 + c3) (c1)
            have := ind_bounds (4 * a3 - 2 * b3 + c3) (c1)
            have := ind_bounds (4 * a3 + 2 * b3 + c3) (c1)
            have := ind_bounds (9 * a3 - 3 * b3 + c3) (c1)
            have := ind_bounds (9 * a3 + 3 * b3 + c3) (c1)
            have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c1)
            have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c1)
            have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c1)
            have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c1)
            omega
          exfalso
          have hT : 0 ≤ (c1) := by omega
          have e := rel (c1) hT
          have l1 := lo1 (c1) hT
          have l2 := lo2 (c1) hT
          have l3 := lo3 (c1) hT
          have x1 := ex1 (c1) hT (by omega) (by omega)
          have x2 := ex2 (c1) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (c1)
          have := ind_bounds (c1) (c1)
          have := ind_bounds (a1 - b1 + c1) (c1)
          have := ind_bounds (a1 + b1 + c1) (c1)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (c1)
          have := ind_zero (4 * a1 + 2 * b1 + c1) (c1) (by omega)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (c1) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (c1) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (c1) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (c1) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (c1) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (c1) (by omega)
          have := ind_bounds (a2) (c1)
          have := ind_bounds (c2) (c1)
          have := ind_bounds (a2 - b2 + c2) (c1)
          have := ind_zero (a2 + b2 + c2) (c1) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (c1) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (c1) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (c1) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (c1) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (c1) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (c1) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (c1) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (c1) (by omega)
          have := ind_one (a3) (c1) (by omega)
          have := ind_one (c3) (c1) (by omega)
          have := ind_one (a3 - b3 + c3) (c1) (by omega)
          have := ind_one (a3 + b3 + c3) (c1) (by omega)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (c1)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (c1)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (c1)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (c1)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (c1)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (c1)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (c1)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (c1)
          omega
        by_cases h127 : 0 ≤ a1 - b1 + c1 - a3 + b3 - c3
        swap
        · -- branch
          exfalso
          have hT : 0 ≤ (a1 - b1 + c1) := by omega
          have e := rel (a1 - b1 + c1) hT
          have l1 := lo1 (a1 - b1 + c1) hT
          have l2 := lo2 (a1 - b1 + c1) hT
          have l3 := lo3 (a1 - b1 + c1) hT
          have x3 := ex3 (a1 - b1 + c1) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x3
          have := ind_bounds (a1) (a1 - b1 + c1)
          have := ind_bounds (c1) (a1 - b1 + c1)
          have := ind_one (a1 - b1 + c1) (a1 - b1 + c1) (by omega)
          have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1)
          have := ind_bounds (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1)
          have := ind_bounds (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1)
          have := ind_bounds (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1)
          have := ind_bounds (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1)
          have := ind_one (a2) (a1 - b1 + c1) (by omega)
          have := ind_one (c2) (a1 - b1 + c1) (by omega)
          have := ind_one (a2 - b2 + c2) (a1 - b1 + c1) (by omega)
          have := ind_bounds (a2 + b2 + c2) (a1 - b1 + c1)
          have := ind_bounds (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1)
          have := ind_bounds (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1)
          have := ind_bounds (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1)
          have := ind_bounds (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1)
          have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1)
          have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1)
          have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1)
          have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1)
          have := ind_bounds (a3) (a1 - b1 + c1)
          have := ind_bounds (c3) (a1 - b1 + c1)
          have := ind_zero (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
          have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1) (by omega)
          omega
        by_cases h128 : 0 ≤ a1 - b1 + c1 - a3 - b3 - c3
        swap
        · -- branch
          exfalso
          have hT : 0 ≤ (a3 + b3 + c3) := by omega
          have e := rel (a3 + b3 + c3) hT
          have l1 := lo1 (a3 + b3 + c3) hT
          have l2 := lo2 (a3 + b3 + c3) hT
          have l3 := lo3 (a3 + b3 + c3) hT
          have x1 := ex1 (a3 + b3 + c3) hT (by omega) (by omega)
          have x2 := ex2 (a3 + b3 + c3) hT (by omega) (by omega)
          simp only [cntV] at l1 l2 l3 x1 x2
          have := ind_bounds (a1) (a3 + b3 + c3)
          have := ind_bounds (c1) (a3 + b3 + c3)
          have := ind_bounds (a1 - b1 + c1) (a3 + b3 + c3)
          have := ind_bounds (a1 + b1 + c1) (a3 + b3 + c3)
          have := ind_bounds (4 * a1 - 2 * b1 + c1) (a3 + b3 + c3)
          have := ind_zero (4 * a1 + 2 * b1 + c1) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a1 - 3 * b1 + c1) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a1 + 3 * b1 + c1) (a3 + b3 + c3) (by omega)
          have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3 + b3 + c3) (by omega)
          have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3 + b3 + c3) (by omega)
          have := ind_bounds (a2) (a3 + b3 + c3)
          have := ind_bounds (c2) (a3 + b3 + c3)
          have := ind_bounds (a2 - b2 + c2) (a3 + b3 + c3)
          have := ind_zero (a2 + b2 + c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (4 * a2 - 2 * b2 + c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (4 * a2 + 2 * b2 + c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a2 - 3 * b2 + c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a2 + 3 * b2 + c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3 + b3 + c3) (by omega)
          have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3 + b3 + c3) (by omega)
          have := ind_one (a3) (a3 + b3 + c3) (by omega)
          have := ind_one (c3) (a3 + b3 + c3) (by omega)
          have := ind_one (a3 - b3 + c3) (a3 + b3 + c3) (by omega)
          have := ind_one (a3 + b3 + c3) (a3 + b3 + c3) (by omega)
          have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3 + b3 + c3)
          have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3 + b3 + c3)
          have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3 + b3 + c3)
          have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3 + b3 + c3)
          have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3 + b3 + c3)
          have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3 + b3 + c3)
          have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3 + b3 + c3)
          have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3 + b3 + c3)
          omega
        exfalso
        have hT : 0 ≤ (a1 - b1 + c1) := by omega
        have e := rel (a1 - b1 + c1) hT
        have l1 := lo1 (a1 - b1 + c1) hT
        have l2 := lo2 (a1 - b1 + c1) hT
        have l3 := lo3 (a1 - b1 + c1) hT
        have x1 := ex1 (a1 - b1 + c1) hT (by omega) (by omega)
        have x2 := ex2 (a1 - b1 + c1) hT (by omega) (by omega)
        simp only [cntV] at l1 l2 l3 x1 x2
        have := ind_bounds (a1) (a1 - b1 + c1)
        have := ind_bounds (c1) (a1 - b1 + c1)
        have := ind_bounds (a1 - b1 + c1) (a1 - b1 + c1)
        have := ind_bounds (a1 + b1 + c1) (a1 - b1 + c1)
        have := ind_bounds (4 * a1 - 2 * b1 + c1) (a1 - b1 + c1)
        have := ind_zero (4 * a1 + 2 * b1 + c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a1 - 3 * b1 + c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a1 + 3 * b1 + c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (a1 - 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (a1 + 2 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a1 - b1 + c1) (by omega)
        have := ind_bounds (a2) (a1 - b1 + c1)
        have := ind_bounds (c2) (a1 - b1 + c1)
        have := ind_bounds (a2 - b2 + c2) (a1 - b1 + c1)
        have := ind_zero (a2 + b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (4 * a2 - 2 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (4 * a2 + 2 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 - 3 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 + 3 * b2 + c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (a2 - 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (a2 + 2 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a1 - b1 + c1) (by omega)
        have := ind_one (a3) (a1 - b1 + c1) (by omega)
        have := ind_one (c3) (a1 - b1 + c1) (by omega)
        have := ind_one (a3 - b3 + c3) (a1 - b1 + c1) (by omega)
        have := ind_one (a3 + b3 + c3) (a1 - b1 + c1) (by omega)
        have := ind_bounds (4 * a3 - 2 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (4 * a3 + 2 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 - 3 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 + 3 * b3 + c3) (a1 - b1 + c1)
        have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a1 - b1 + c1)
        have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a1 - b1 + c1)
        have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a1 - b1 + c1)
        omega
      exfalso
      have hT : 0 ≤ (a2 - b2 + c2) := by omega
      have e := rel (a2 - b2 + c2) hT
      have l1 := lo1 (a2 - b2 + c2) hT
      have l2 := lo2 (a2 - b2 + c2) hT
      have l3 := lo3 (a2 - b2 + c2) hT
      have x1 := ex1 (a2 - b2 + c2) hT (by omega) (by omega)
      have x2 := ex2 (a2 - b2 + c2) hT (by omega) (by omega)
      simp only [cntV] at l1 l2 l3 x1 x2
      have := ind_bounds (a1) (a2 - b2 + c2)
      have := ind_bounds (c1) (a2 - b2 + c2)
      have := ind_zero (a1 - b1 + c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (a1 + b1 + c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (4 * a1 - 2 * b1 + c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (4 * a1 + 2 * b1 + c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a1 - 3 * b1 + c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a1 + 3 * b1 + c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2 - b2 + c2) (by omega)
      have := ind_bounds (a2) (a2 - b2 + c2)
      have := ind_bounds (c2) (a2 - b2 + c2)
      have := ind_bounds (a2 - b2 + c2) (a2 - b2 + c2)
      have := ind_zero (a2 + b2 + c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (4 * a2 - 2 * b2 + c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (4 * a2 + 2 * b2 + c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a2 - 3 * b2 + c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a2 + 3 * b2 + c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (a2 - 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (a2 + 2 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
      have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a2 - b2 + c2) (by omega)
      have := ind_one (a3) (a2 - b2 + c2) (by omega)
      have := ind_one (c3) (a2 - b2 + c2) (by omega)
      have := ind_one (a3 - b3 + c3) (a2 - b2 + c2) (by omega)
      have := ind_bounds (a3 + b3 + c3) (a2 - b2 + c2)
      have := ind_bounds (4 * a3 - 2 * b3 + c3) (a2 - b2 + c2)
      have := ind_bounds (4 * a3 + 2 * b3 + c3) (a2 - b2 + c2)
      have := ind_bounds (9 * a3 - 3 * b3 + c3) (a2 - b2 + c2)
      have := ind_bounds (9 * a3 + 3 * b3 + c3) (a2 - b2 + c2)
      have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a2 - b2 + c2)
      have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a2 - b2 + c2)
      have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a2 - b2 + c2)
      have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a2 - b2 + c2)
      omega
    exfalso
    have hT : 0 ≤ (a3) := by omega
    have e := rel (a3) hT
    have l1 := lo1 (a3) hT
    have l2 := lo2 (a3) hT
    have l3 := lo3 (a3) hT
    have x1 := ex1 (a3) hT (by omega) (by omega)
    have x2 := ex2 (a3) hT (by omega) (by omega)
    simp only [cntV] at l1 l2 l3 x1 x2
    have := ind_bounds (a1) (a3)
    have := ind_bounds (c1) (a3)
    have := ind_zero (a1 - b1 + c1) (a3) (by omega)
    have := ind_zero (a1 + b1 + c1) (a3) (by omega)
    have := ind_zero (4 * a1 - 2 * b1 + c1) (a3) (by omega)
    have := ind_zero (4 * a1 + 2 * b1 + c1) (a3) (by omega)
    have := ind_zero (9 * a1 - 3 * b1 + c1) (a3) (by omega)
    have := ind_zero (9 * a1 + 3 * b1 + c1) (a3) (by omega)
    have := ind_zero (a1 - 2 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (a1 + 2 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a3) (by omega)
    have := ind_zero (a2) (a3) (by omega)
    have := ind_zero (c2) (a3) (by omega)
    have := ind_zero (a2 - b2 + c2) (a3) (by omega)
    have := ind_zero (a2 + b2 + c2) (a3) (by omega)
    have := ind_zero (4 * a2 - 2 * b2 + c2) (a3) (by omega)
    have := ind_zero (4 * a2 + 2 * b2 + c2) (a3) (by omega)
    have := ind_zero (9 * a2 - 3 * b2 + c2) (a3) (by omega)
    have := ind_zero (9 * a2 + 3 * b2 + c2) (a3) (by omega)
    have := ind_zero (a2 - 2 * b2 + 4 * c2) (a3) (by omega)
    have := ind_zero (a2 + 2 * b2 + 4 * c2) (a3) (by omega)
    have := ind_zero (9 * a2 - 6 * b2 + 4 * c2) (a3) (by omega)
    have := ind_zero (9 * a2 + 6 * b2 + 4 * c2) (a3) (by omega)
    have := ind_one (a3) (a3) (by omega)
    have := ind_bounds (c3) (a3)
    have := ind_bounds (a3 - b3 + c3) (a3)
    have := ind_bounds (a3 + b3 + c3) (a3)
    have := ind_bounds (4 * a3 - 2 * b3 + c3) (a3)
    have := ind_bounds (4 * a3 + 2 * b3 + c3) (a3)
    have := ind_bounds (9 * a3 - 3 * b3 + c3) (a3)
    have := ind_bounds (9 * a3 + 3 * b3 + c3) (a3)
    have := ind_bounds (a3 - 2 * b3 + 4 * c3) (a3)
    have := ind_bounds (a3 + 2 * b3 + 4 * c3) (a3)
    have := ind_bounds (9 * a3 - 6 * b3 + 4 * c3) (a3)
    have := ind_bounds (9 * a3 + 6 * b3 + 4 * c3) (a3)
    omega
  exfalso
  have hT : 0 ≤ (a2) := by omega
  have e := rel (a2) hT
  have l1 := lo1 (a2) hT
  have l2 := lo2 (a2) hT
  have l3 := lo3 (a2) hT
  have x1 := ex1 (a2) hT (by omega) (by omega)
  have x3 := ex3 (a2) hT (by omega) (by omega)
  simp only [cntV] at l1 l2 l3 x1 x3
  have := ind_zero (a1) (a2) (by omega)
  have := ind_zero (c1) (a2) (by omega)
  have := ind_zero (a1 - b1 + c1) (a2) (by omega)
  have := ind_zero (a1 + b1 + c1) (a2) (by omega)
  have := ind_zero (4 * a1 - 2 * b1 + c1) (a2) (by omega)
  have := ind_zero (4 * a1 + 2 * b1 + c1) (a2) (by omega)
  have := ind_zero (9 * a1 - 3 * b1 + c1) (a2) (by omega)
  have := ind_zero (9 * a1 + 3 * b1 + c1) (a2) (by omega)
  have := ind_zero (a1 - 2 * b1 + 4 * c1) (a2) (by omega)
  have := ind_zero (a1 + 2 * b1 + 4 * c1) (a2) (by omega)
  have := ind_zero (9 * a1 - 6 * b1 + 4 * c1) (a2) (by omega)
  have := ind_zero (9 * a1 + 6 * b1 + 4 * c1) (a2) (by omega)
  have := ind_bounds (a2) (a2)
  have := ind_bounds (c2) (a2)
  have := ind_bounds (a2 - b2 + c2) (a2)
  have := ind_bounds (a2 + b2 + c2) (a2)
  have := ind_bounds (4 * a2 - 2 * b2 + c2) (a2)
  have := ind_bounds (4 * a2 + 2 * b2 + c2) (a2)
  have := ind_bounds (9 * a2 - 3 * b2 + c2) (a2)
  have := ind_bounds (9 * a2 + 3 * b2 + c2) (a2)
  have := ind_bounds (a2 - 2 * b2 + 4 * c2) (a2)
  have := ind_bounds (a2 + 2 * b2 + 4 * c2) (a2)
  have := ind_bounds (9 * a2 - 6 * b2 + 4 * c2) (a2)
  have := ind_bounds (9 * a2 + 6 * b2 + 4 * c2) (a2)
  have := ind_one (a3) (a2) (by omega)
  have := ind_zero (c3) (a2) (by omega)
  have := ind_zero (a3 - b3 + c3) (a2) (by omega)
  have := ind_zero (a3 + b3 + c3) (a2) (by omega)
  have := ind_zero (4 * a3 - 2 * b3 + c3) (a2) (by omega)
  have := ind_zero (4 * a3 + 2 * b3 + c3) (a2) (by omega)
  have := ind_zero (9 * a3 - 3 * b3 + c3) (a2) (by omega)
  have := ind_zero (9 * a3 + 3 * b3 + c3) (a2) (by omega)
  have := ind_zero (a3 - 2 * b3 + 4 * c3) (a2) (by omega)
  have := ind_zero (a3 + 2 * b3 + 4 * c3) (a2) (by omega)
  have := ind_zero (9 * a3 - 6 * b3 + 4 * c3) (a2) (by omega)
  have := ind_zero (9 * a3 + 6 * b3 + 4 * c3) (a2) (by omega)
  omega

end QuadFormsKB.Hanke2023ThreeTerm.Refinement
