/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7CountTest
import QuadFormsKB.Tamagawa.Dyadic7CountRowsA
import QuadFormsKB.Tamagawa.Dyadic7CountRowsB
import QuadFormsKB.Tamagawa.Dyadic7CountRowsC
import QuadFormsKB.Tamagawa.Dyadic7CountTable
import QuadFormsKB.Tamagawa.Dyadic7Table

/-!
# Paper 7 at $p = 2$: the 2-adic count of Table 5.3 for every $h$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), Thm. 4.12 and Tables 5.1–5.3, pp. 15–22.

**Proves** the named statement `Dyadic7.TernaryDyadicMassCount` (`ternaryDyadicMassCount_holds`): for every Hessian
valuation $h \ge 1$ and unit class $u \in \{1,3,5,7\}$, the class-weighted sums of the mass weights (and of the
Hasse-weighted mass weights) over the admissible ternary 2-adic block decompositions are the entries of Table 5.3.

Route:
1. `classSum_eq`: a class-weighted sum over `admSet h u` is the sum over the class representatives `reps h u`
   (`reps_subset`, `reps_cover`, `reps_uniq`); the binary lists with exponents $1, 1$ are equivalent to diagonal ones
   (`binary11_equiv`, decided over the finitely many unit pairs).
2. `sum_reps`: the representatives are the diagonal lists with exponents $1, e, h-1-e$ and the binary lists with
   exponents $m, h-2m$; their first-in-class units are summed row by row of Table 5.3 (`famR…_A`, `famR…_B`,
   files `Dyadic7CountRows*.lean`).
3. `dyadicA4_eq`, `dyadicBmag_eq`: the table regrouped by these exponents.

Then `dyadicTernaryLocalMassTable_holds` (the true normalized local mass sums at $p = 2$ are Table 5.3) is
unconditional. Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.Hanke2011Ternary

/-! ### Binary lists with exponents $1, 1$ -/

/-- The window decomposition of the binary lists with exponents $1, 1$. -/
def famBin11 : BinFam 1 1 where
  ws := [(0, 3)]
  L x := [[binBlock x.1 1, .sq 1 x.2]]
  hnd := by nd_tac
  hloc x := by hloc_tac
  hdec x := winDecomp_of (L := [[binBlock x.1 1, .sq 1 x.2]]) (L₀ := [[.hyp 1, .sq 1 1]]) (by hloc_tac)
    (by (simp only [List.map_cons, List.map_nil, forgetUnit_binBlock] <;> simp [forgetUnit])) (by simp only [winLens, List.map_cons, List.map_nil, Nat.sub_zero]; decide)
    (by lt_tac) (by disj_tac) (by cover_tac)
  hforget x y := by (simp only [List.map_cons, List.map_nil, forgetUnit_binBlock] <;> simp [forgetUnit])

theorem symEquiv_bin11 (x : ℤ × ℤ) (y : ℤ × ℤ × ℤ)
    (hdt : ∀ i < 3, (blockSymbol [.sq 1 y.1, .sq 1 y.2.1, .sq 1 y.2.2] i).dim =
        (blockSymbol [binBlock x.1 1, .sq 1 x.2] i).dim ∧
      (blockSymbol [.sq 1 y.1, .sq 1 y.2.1, .sq 1 y.2.2] i).type = (blockSymbol [binBlock x.1 1, .sq 1 x.2] i).type)
    (hr : WinEq (blockSymbol [binBlock x.1 1, .sq 1 x.2]) (blockSymbol [.sq 1 y.1, .sq 1 y.2.1, .sq 1 y.2.2]) 3) :
    SymEquiv (binL 1 1 x) (sqL 1 1 y) := by
  have h1 : localize (binL 1 1 x) 0 3 = [binBlock x.1 1, .sq 1 x.2] := by
    have := famBin11.hloc x
    simpa [famBin11] using this
  have h2 : localize (sqL 1 1 y) 0 3 = [.sq 1 y.1, .sq 1 y.2.1, .sq 1 y.2.2] := by
    have := famR1.hloc y
    simpa [famR1] using this
  unfold SymEquiv
  rw [moveEquiv_iff_local (famBin11.hdec x) (famR1.hdec y)]
  · intro w hw
    simp only [famBin11, List.mem_singleton] at hw
    subst hw
    simpa [h1, h2] using hr
  · intro w hw i hi
    simp only [famBin11, List.mem_singleton] at hw
    subst hw
    simp only [Nat.sub_zero] at hi ⊢
    rw [h1, h2]
    exact hdt i hi

/-- **The binary lists with exponents $1, 1$ are equivalent to diagonal ones** (decided over the unit pairs). -/
theorem binary11_equiv {u : ℤ} (hu : u ∈ sqUnits) :
    ∀ x ∈ binUnits u, ∃ y ∈ sqUnits3 u, SymEquiv (binL 1 1 x) (sqL 1 1 y) := by
  have key : ∀ x ∈ binUnits u, ∃ y ∈ sqUnits3 u,
      (∀ i < 3, (blockSymbol [.sq 1 y.1, .sq 1 y.2.1, .sq 1 y.2.2] i).dim =
          (blockSymbol [binBlock x.1 1, .sq 1 x.2] i).dim ∧
        (blockSymbol [.sq 1 y.1, .sq 1 y.2.1, .sq 1 y.2.2] i).type =
          (blockSymbol [binBlock x.1 1, .sq 1 x.2] i).type) ∧
      WinEq (blockSymbol [binBlock x.1 1, .sq 1 x.2]) (blockSymbol [.sq 1 y.1, .sq 1 y.2.1, .sq 1 y.2.2]) 3 := by
    simp only [sqUnits, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  intro x hx
  obtain ⟨y, hy, hdt, hr⟩ := key x hx
  exact ⟨y, hy, symEquiv_bin11 x y hdt hr⟩

/-! ### The rows, by exponents -/

/-- Evaluate a regrouped table entry at explicit exponents. -/
macro "val_tac" : tactic => `(tactic| (
  simp (disch := omega) only [sqValA, binValA, sqValB, binValB, if_pos, if_neg, add_zero, zero_add,
    Nat.add_sub_cancel, true_and, and_true, eq_self_iff_true]
  try first | rfl | (congr 2 <;> omega) | (congr 1 <;> omega)))

theorem sq_rows_A {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (e : ℕ) (he : e ∈ (range h).filter (SqExpOK h)) :
    ∑ x ∈ minSq u e (h - 1 - e), massWt h u (sqL e (h - 1 - e) x) = ((sqValA h e : ℚ) : ℝ) / 4 := by
  rw [mem_sqF] at he
  obtain ⟨h1, h2, h3⟩ := he
  rcases (by omega : e = 1 ∨ e = 2 ∨ e = 3 ∨ 4 ≤ e) with rfl | rfl | rfl | he4
  · rcases (by omega : h = 3 ∨ h = 4 ∨ h = 5 ∨ 6 ≤ h) with rfl | rfl | rfl | hh
    · rw [famR1_A hu]; congr 2; val_tac
    · rw [famR2_A hu]; congr 2; val_tac
    · rw [famR3_A hu]; congr 2; val_tac
    · obtain ⟨b, rfl⟩ : ∃ b, h = b + 3 := ⟨h - 3, by omega⟩
      rw [show b + 3 - 1 - 1 = b + 1 by omega, famR4_A b (by omega) hu]; congr 2; val_tac
  · rcases (by omega : h = 5 ∨ h = 6 ∨ h = 7 ∨ 8 ≤ h) with rfl | rfl | rfl | hh
    · rw [famR7_A hu]; congr 2; val_tac
    · rw [famR12_A hu]; congr 2; val_tac
    · rw [famR13_A hu]; congr 2; val_tac
    · obtain ⟨c, rfl⟩ : ∃ c, h = c + 4 := ⟨h - 4, by omega⟩
      rw [show c + 4 - 1 - 2 = c + 1 by omega, famR16_A c (by omega) hu]; congr 2; val_tac
  · rcases (by omega : h = 7 ∨ h = 8 ∨ h = 9 ∨ 10 ≤ h) with rfl | rfl | rfl | hh
    · rw [famR8_A hu]; congr 2; val_tac
    · rw [famR14_A hu]; congr 2; val_tac
    · rw [famR15_A hu]; congr 2; val_tac
    · obtain ⟨c, rfl⟩ : ∃ c, h = c + 5 := ⟨h - 5, by omega⟩
      rw [show c + 5 - 1 - 3 = c + 1 by omega, famR19_A c (by omega) hu]; congr 2; val_tac
  · obtain ⟨b, rfl⟩ : ∃ b, e = b + 1 := ⟨e - 1, by omega⟩
    rcases (by omega : h = 2 * b + 3 ∨ h = 2 * b + 4 ∨ h = 2 * b + 5 ∨ 2 * b + 6 ≤ h) with rfl | rfl | rfl | hh
    · rw [show 2 * b + 3 - 1 - (b + 1) = b + 1 by omega, famR9_A b (by omega) hu]; congr 2; val_tac
    · rw [show 2 * b + 4 - 1 - (b + 1) = b + 2 by omega, famR17_A b (by omega) hu]; congr 2; val_tac
    · rw [show 2 * b + 5 - 1 - (b + 1) = b + 3 by omega, famR18_A b (by omega) hu]; congr 2; val_tac
    · obtain ⟨c, rfl⟩ : ∃ c, h = b + c + 3 := ⟨h - b - 3, by omega⟩
      rw [show b + c + 3 - 1 - (b + 1) = c + 1 by omega, famR20_A b c (by omega) (by omega) hu]; congr 2
      simp (disch := omega) only [sqValA, if_pos, if_neg, add_zero, zero_add, Nat.add_sub_cancel, true_and, and_true]
      congr 2; omega

theorem sq_rows_B {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (e : ℕ) (he : e ∈ (range h).filter (SqExpOK h)) :
    ∑ x ∈ minSq u e (h - 1 - e), (hasseQ (sqL e (h - 1 - e) x) : ℝ) * massWt h u (sqL e (h - 1 - e) x) =
      (hasseQ (baseList u) : ℝ) * ((sqValB h e : ℚ) : ℝ) / 4 := by
  rw [mem_sqF] at he
  obtain ⟨h1, h2, h3⟩ := he
  rcases (by omega : e = 1 ∨ e = 2 ∨ e = 3 ∨ 4 ≤ e) with rfl | rfl | rfl | he4
  · rcases (by omega : h = 3 ∨ h = 4 ∨ h = 5 ∨ 6 ≤ h) with rfl | rfl | rfl | hh
    · rw [famR1_B hu]; congr 3; val_tac
    · rw [famR2_B hu]; congr 3; val_tac
    · rw [famR3_B hu]; congr 3; val_tac
    · obtain ⟨b, rfl⟩ : ∃ b, h = b + 3 := ⟨h - 3, by omega⟩
      rw [show b + 3 - 1 - 1 = b + 1 by omega, famR4_B b (by omega) hu]; congr 3; val_tac
  · rcases (by omega : h = 5 ∨ h = 6 ∨ h = 7 ∨ 8 ≤ h) with rfl | rfl | rfl | hh
    · rw [famR7_B hu]; congr 3; val_tac
    · rw [famR12_B hu]; congr 3; val_tac
    · rw [famR13_B hu]; congr 3; val_tac
    · obtain ⟨c, rfl⟩ : ∃ c, h = c + 4 := ⟨h - 4, by omega⟩
      rw [show c + 4 - 1 - 2 = c + 1 by omega, famR16_B c (by omega) hu]; congr 3; val_tac
  · rcases (by omega : h = 7 ∨ h = 8 ∨ h = 9 ∨ 10 ≤ h) with rfl | rfl | rfl | hh
    · rw [famR8_B hu]; congr 3; val_tac
    · rw [famR14_B hu]; congr 3; val_tac
    · rw [famR15_B hu]; congr 3; val_tac
    · obtain ⟨c, rfl⟩ : ∃ c, h = c + 5 := ⟨h - 5, by omega⟩
      rw [show c + 5 - 1 - 3 = c + 1 by omega, famR19_B c (by omega) hu]; congr 3; val_tac
  · obtain ⟨b, rfl⟩ : ∃ b, e = b + 1 := ⟨e - 1, by omega⟩
    rcases (by omega : h = 2 * b + 3 ∨ h = 2 * b + 4 ∨ h = 2 * b + 5 ∨ 2 * b + 6 ≤ h) with rfl | rfl | rfl | hh
    · rw [show 2 * b + 3 - 1 - (b + 1) = b + 1 by omega, famR9_B b (by omega) hu]; congr 3; val_tac
    · rw [show 2 * b + 4 - 1 - (b + 1) = b + 2 by omega, famR17_B b (by omega) hu]; congr 3; val_tac
    · rw [show 2 * b + 5 - 1 - (b + 1) = b + 3 by omega, famR18_B b (by omega) hu]; congr 3; val_tac
    · obtain ⟨c, rfl⟩ : ∃ c, h = b + c + 3 := ⟨h - b - 3, by omega⟩
      rw [show b + c + 3 - 1 - (b + 1) = c + 1 by omega, famR20_B b c (by omega) (by omega) hu]; congr 3
      simp (disch := omega) only [sqValB, if_pos, if_neg, add_zero, zero_add, Nat.add_sub_cancel, true_and, and_true]
      rw [show b + c + 3 - 2 - (b + 1) = c by omega]

theorem bin_rows_A {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (m : ℕ) (hm : m ∈ (range h).filter (BinExpOK h)) :
    ∑ x ∈ minBin u m (h - 2 * m), massWt h u (binL m (h - 2 * m) x) = ((binValA h m : ℚ) : ℝ) / 4 := by
  rw [mem_binF] at hm
  rcases hm with ⟨h1, rfl | ⟨rfl, h2⟩⟩
  · rcases (by omega : h = 1 ∨ 2 ≤ h) with rfl | hh
    · rw [famR5_A hu]; congr 2; val_tac
    · obtain ⟨b, rfl⟩ : ∃ b, h = b + 1 := ⟨h - 1, by omega⟩
      rw [show b + 1 - 2 * 0 = b + 1 by omega, famR6_A b (by omega) hu]; congr 2; val_tac
  · rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · rw [famR10_A hu]; congr 2; val_tac
    · obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (b + 1) + 1 - 2 * (b + 1) = 1 by omega, show 2 * (b + 1) + 1 = 2 * b + 3 by omega,
        famR11_A b (by omega) hu]; congr 2; val_tac

theorem bin_rows_B {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (m : ℕ) (hm : m ∈ (range h).filter (BinExpOK h)) :
    ∑ x ∈ minBin u m (h - 2 * m), (hasseQ (binL m (h - 2 * m) x) : ℝ) * massWt h u (binL m (h - 2 * m) x) =
      (hasseQ (baseList u) : ℝ) * ((binValB h m : ℚ) : ℝ) / 4 := by
  rw [mem_binF] at hm
  rcases hm with ⟨h1, rfl | ⟨rfl, h2⟩⟩
  · rcases (by omega : h = 1 ∨ 2 ≤ h) with rfl | hh
    · rw [famR5_B hu]; congr 3; val_tac
    · obtain ⟨b, rfl⟩ : ∃ b, h = b + 1 := ⟨h - 1, by omega⟩
      rw [show b + 1 - 2 * 0 = b + 1 by omega, famR6_B b (by omega) hu]; congr 3; val_tac
  · rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · rw [famR10_B hu]; congr 3; val_tac
    · obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (b + 1) + 1 - 2 * (b + 1) = 1 by omega, show 2 * (b + 1) + 1 = 2 * b + 3 by omega,
        famR11_B b (by omega) hu]; congr 3; val_tac

/-! ### The count -/

/-- **Paper 7, Theorem 4.12 and Tables 5.1–5.3 (the 2-adic case analysis), proved:** the named statement
`TernaryDyadicMassCount` holds for every Hessian valuation $h \ge 1$ and every unit class $u$. -/
@[kb "hanke2011ternary" "Thm. 4.12 and Tables 5.1–5.3, pp. 15–22 (the 2-adic case analysis)"]
theorem ternaryDyadicMassCount_holds : TernaryDyadicMassCount where
  A_eq h _ u hu := by
    rw [classSum_eq (reps h u) (fun D => massWt h u D) (fun D _ D' _ hm => massWt_eq_of_moveEquiv hm)
      (reps_subset h u) (reps_cover h u (binary11_equiv hu)) (reps_uniq h u), sum_reps,
      Finset.sum_congr rfl (sq_rows_A hu), Finset.sum_congr rfl (bin_rows_A hu), ← Finset.sum_div,
      ← Finset.sum_div, ← add_div, dyadicA, dyadicA4_eq]
    push_cast
    ring
  B_eq h _ u hu := by
    rw [classSum_eq (reps h u) (fun D => (hasseQ D : ℝ) * massWt h u D)
      (fun D hD D' hD' hm => by rw [hasseQ_eq_of_moveEquiv hD hD' hm, massWt_eq_of_moveEquiv hm])
      (reps_subset h u) (reps_cover h u (binary11_equiv hu)) (reps_uniq h u), sum_reps,
      Finset.sum_congr rfl (sq_rows_B hu), Finset.sum_congr rfl (bin_rows_B hu), dyadicBmag_eq]
    simp only [mul_div_assoc, ← Finset.mul_sum, ← Finset.sum_div]
    push_cast
    ring

/-- **The true normalized local mass sums at $p = 2$ are Table 5.3** (paper 7, Thm. 4.12; the sign convention
$\varepsilon_u = -c_2(G_0)$), unconditional. -/
@[kb "hanke2011ternary" "Thm. 4.12, Table 5.3, pp. 15–22"]
theorem dyadicTernaryLocalMassTable_holds : DyadicTernaryLocalMassTable :=
  dyadicTernaryLocalMassTable_of_count ternaryDyadicMassCount_holds

end QuadFormsKB.Dyadic7
