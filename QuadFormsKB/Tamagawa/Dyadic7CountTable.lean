/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7CountTrans
import QuadFormsKB.Literature.Hanke2011Ternary.DyadicEuler

/-!
# Paper 7 at $p = 2$: Table 5.3 regrouped by exponents

The entries `dyadicA4 h`, `dyadicBmag h` of Hanke's Table 5.3 (sums over the 20 partial local genus symbols of
Lemma 4.2) regrouped as sums over the exponent data of the class representatives `Dyadic7.reps`:

* `sqValA h e`, `sqValB h e`: the contribution of the diagonal lists with exponents $1, e, h - 1 - e$ (rows 1–4, 7–9,
  12–20 of the table, written with the table's parameters $b$, $c$ expressed through $h$ and $e$);
* `binValA h m`, `binValB h m`: the contribution of the binary lists with exponents $m$, $h - 2m$ (rows 5, 6, 10, 11).

**Proves** `dyadicA4_eq` and `dyadicBmag_eq`: `dyadicA4 h` (resp. `dyadicBmag h`) is the sum of `sqValA h e`
(resp. `sqValB`) over the admissible $e$ (`SqExpOK`) plus the sum of `binValA h m` (resp. `binValB`) over the admissible
$m$ (`BinExpOK`). Pure arithmetic of the table.

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Ternary

/-- Table 5.3, column $4A^*$, rows with diagonal representatives $[2ax^2, 2^e by^2, 2^{h-1-e}cz^2]$. -/
noncomputable def sqValA (h e : ℕ) : ℚ :=
  (if e = 1 ∧ h = 3 then 1 / 2 else 0) +
  (if e = 1 ∧ h = 4 then 3 * (1 / 2) ^ 4 else 0) +
  (if e = 1 ∧ h = 5 then 3 * (1 / 2) ^ 5 else 0) +
  (if e = 1 ∧ 6 ≤ h then 3 * (1 / 2) ^ ((h - 3) + 3) else 0) +
  (if e = 2 ∧ h = 5 then 3 * (1 / 2) ^ 6 else 0) +
  (if e = 3 ∧ h = 7 then 3 * (1 / 2) ^ 9 else 0) +
  (if 4 ≤ e ∧ h = 2 * e + 1 then 3 * (1 / 2) ^ (3 * (e - 1) + 3) else 0) +
  (if e = 2 ∧ h = 6 then 3 * (1 / 2) ^ 7 else 0) +
  (if e = 2 ∧ h = 7 then 3 * (1 / 2) ^ 8 else 0) +
  (if e = 3 ∧ h = 8 then 3 * (1 / 2) ^ 10 else 0) +
  (if e = 3 ∧ h = 9 then 3 * (1 / 2) ^ 11 else 0) +
  (if e = 2 ∧ 8 ≤ h then 3 * (1 / 2) ^ ((h - 4) + 5) else 0) +
  (if 4 ≤ e ∧ h = 2 * e + 2 then 3 * (1 / 2) ^ (3 * (e - 1) + 4) else 0) +
  (if 4 ≤ e ∧ h = 2 * e + 3 then 3 * (1 / 2) ^ (3 * (e - 1) + 5) else 0) +
  (if e = 3 ∧ 10 ≤ h then 3 * (1 / 2) ^ ((h - 5) + 7) else 0) +
  (if 4 ≤ e ∧ 2 * e + 4 ≤ h then 3 * (1 / 2) ^ (2 * (e - 1) + (h - 2 - e) + 3) else 0)

/-- Table 5.3, column $4A^*$, rows with binary representatives $[2^m\beta, 2^{h-2m}wx^2]$. -/
noncomputable def binValA (h m : ℕ) : ℚ :=
  (if m = 0 ∧ h = 1 then 4 else 0) +
  (if m = 0 ∧ 2 ≤ h then 4 * (1 / 2) ^ (h - 1) else 0) +
  (if m = 2 ∧ h = 5 then (1 / 2) ^ 6 else 0) +
  (if 3 ≤ m ∧ h = 2 * m + 1 then (1 / 2) ^ (3 * (m - 1) + 3) else 0)

/-- Table 5.3, column $|4B^*|$, diagonal rows. -/
noncomputable def sqValB (h e : ℕ) : ℚ :=
  (if e = 1 ∧ h = 3 then (1 / 2) ^ 2 else 0) +
  (if e = 1 ∧ h = 5 then 3 * (1 / 2) ^ 6 else 0) +
  (if e = 1 ∧ 6 ≤ h then (if Even (h - 3) then 3 * (1 / 2) ^ ((h - 3) + 4) else 0) else 0) +
  (if e = 3 ∧ h = 7 then 3 * (1 / 2) ^ 10 else 0) +
  (if 4 ≤ e ∧ h = 2 * e + 1 then (if Even (e - 1) then 3 * (1 / 2) ^ (3 * (e - 1) + 4) else 0) else 0) +
  (if e = 3 ∧ h = 9 then 3 * (1 / 2) ^ 12 else 0) +
  (if 4 ≤ e ∧ h = 2 * e + 3 then (if Even (e - 1) then 3 * (1 / 2) ^ (3 * (e - 1) + 6) else 0) else 0) +
  (if e = 3 ∧ 10 ≤ h then (if Even (h - 5) then 3 * (1 / 2) ^ ((h - 5) + 8) else 0) else 0) +
  (if 4 ≤ e ∧ 2 * e + 4 ≤ h then (if Even (e - 1) ∧ Even (h - 2 - e) then
    3 * (1 / 2) ^ (2 * (e - 1) + (h - 2 - e) + 4) else 0) else 0)

/-- Table 5.3, column $|4B^*|$, binary rows. -/
noncomputable def binValB (h m : ℕ) : ℚ :=
  (if m = 0 ∧ h = 1 then 4 else 0) +
  (if m = 0 ∧ 2 ≤ h then (if Even (h - 1) then 4 * (1 / 2) ^ (h - 1) else 2 * (1 / 2) ^ (h - 1)) else 0) +
  (if m = 2 ∧ h = 5 then (1 / 2) ^ 6 else 0) +
  (if 3 ≤ m ∧ h = 2 * m + 1 then
    (if Even (m - 1) then (1 / 2) ^ (3 * (m - 1) + 4) else (1 / 2) ^ (3 * (m - 1) + 3)) else 0)

/-- A sum of a function supported on at most one point $B$. -/
theorem sum_ite_unique (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℚ) (B : ℕ)
    (hu : ∀ e ∈ s, P e → e = B) : ∑ e ∈ s, (if P e then f e else 0) = if B ∈ s ∧ P B then f B else 0 := by
  by_cases hB : B ∈ s ∧ P B
  · rw [if_pos hB, Finset.sum_eq_single B]
    · rw [if_pos hB.2]
    · intro e he hne; rw [if_neg]; exact fun hp => hne (hu e he hp)
    · intro h; exact absurd hB.1 h
  · rw [if_neg hB]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [if_neg]
    intro hp
    obtain rfl := hu e he hp
    exact hB ⟨he, hp⟩

theorem mem_sqF {h e : ℕ} : e ∈ (range h).filter (SqExpOK h) ↔ 1 ≤ e ∧ e + 1 ≤ h ∧ e ≤ h - 1 - e := by
  simp only [Finset.mem_filter, Finset.mem_range, SqExpOK]; omega

theorem mem_binF {h m : ℕ} : m ∈ (range h).filter (BinExpOK h) ↔ 2 * m + 1 ≤ h ∧ (m = 0 ∨ (h = 2 * m + 1 ∧ 2 ≤ m)) := by
  simp only [Finset.mem_filter, Finset.mem_range, BinExpOK]; omega

/-- Close a goal `if … then x else 0 = if … then y else 0` of natural-number conditions. -/
macro "ite_close" : tactic => `(tactic| (
  split_ifs <;> (try simp only [Nat.even_iff, ← Nat.not_even_iff_odd] at *) <;>
    first | rfl | (exfalso; omega) | (congr 2 <;> omega) | (congr 1 <;> omega)))

/-- A diagonal row of the regrouped table, supported at `e = B`: reduce the sum over `e` to one `if`. -/
macro "sq_row" B:term : tactic => `(tactic| (
  rw [sum_ite_unique _ _ _ $B (fun e he hp => by rw [mem_sqF] at he; omega)]
  simp only [mem_sqF, mem_binF, true_and, and_true, true_or, or_true, eq_self_iff_true, mul_zero, zero_add]))

/-- A binary row of the regrouped table, supported at `m = B`. -/
macro "bin_row" B:term : tactic => `(tactic| (
  rw [sum_ite_unique _ _ _ $B (fun e he hp => by rw [mem_binF] at he; omega)]
  simp only [mem_sqF, mem_binF, true_and, and_true, true_or, or_true, eq_self_iff_true, mul_zero, zero_add]))

theorem family20_eq (val : ℕ → ℕ → ℚ) (h : ℕ) :
    family20 val h = ∑ e ∈ (range h).filter (SqExpOK h),
      if 4 ≤ e ∧ 2 * e + 4 ≤ h then val (e - 1) (h - 2 - e) else 0 := by
  unfold family20
  have inner : ∀ b ∈ range (h + 1), (∑ c ∈ range (h + 1), if 3 ≤ b ∧ b + 3 ≤ c ∧ b + c + 3 = h then val b c else 0)
      = if 3 ≤ b ∧ b + 3 ≤ h - b - 3 ∧ b + 3 < h then val b (h - b - 3) else 0 := by
    intro b _
    rw [sum_ite_unique _ _ _ (h - b - 3) (fun c _ hc => by omega)]
    simp only [Finset.mem_range]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_congr rfl inner, Finset.sum_filter]
  rw [Finset.sum_range_succ, if_neg (by omega), add_zero]
  rcases h with _ | k
  · simp
  conv_rhs => rw [Finset.sum_range_succ']
  conv_lhs => rw [Finset.sum_range_succ]
  rw [if_neg (show ¬ SqExpOK (k + 1) 0 by unfold SqExpOK; omega), add_zero, if_neg (by omega), add_zero]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [Finset.mem_range] at hb
  by_cases hc : 3 ≤ b ∧ b + 3 ≤ k + 1 - b - 3 ∧ b + 3 < k + 1
  · rw [if_pos hc, if_pos (show SqExpOK (k + 1) (b + 1) by unfold SqExpOK; omega), if_pos (by omega)]
    congr 1 <;> omega
  · rw [if_neg hc]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **Table 5.3, column $4A^*$, regrouped by the exponents of the class representatives.** -/
theorem dyadicA4_eq (h : ℕ) :
    dyadicA4 h = ∑ e ∈ (range h).filter (SqExpOK h), sqValA h e +
      ∑ m ∈ (range h).filter (BinExpOK h), binValA h m := by
  have r1 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 1 ∧ h = 3 then (1 / 2 : ℚ) else 0) =
      single 3 (1 / 2) h := by sq_row 1; unfold single; ite_close
  have r2 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 1 ∧ h = 4 then 3 * (1 / 2 : ℚ) ^ 4 else 0) =
      single 4 (3 * (1 / 2) ^ 4) h := by sq_row 1; unfold single; ite_close
  have r3 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 1 ∧ h = 5 then 3 * (1 / 2 : ℚ) ^ 5 else 0) =
      single 5 (3 * (1 / 2) ^ 5) h := by sq_row 1; unfold single; ite_close
  have r4 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 1 ∧ 6 ≤ h then 3 * (1 / 2 : ℚ) ^ ((h - 3) + 3) else 0) =
      family 3 (fun b => b + 3) (fun b => 3 * (1 / 2) ^ (b + 3)) h := by
    sq_row 1; rw [family_coeff 1 3 3 (by norm_num) (fun b => b + 3) (fun b => by ring)]; ite_close
  have r5 : ∑ m ∈ (range h).filter (BinExpOK h), (if m = 0 ∧ h = 1 then (4 : ℚ) else 0) = single 1 4 h := by
    bin_row 0; unfold single; ite_close
  have r6 : ∑ m ∈ (range h).filter (BinExpOK h), (if m = 0 ∧ 2 ≤ h then 4 * (1 / 2 : ℚ) ^ (h - 1) else 0) =
      family 1 (fun b => b + 1) (fun b => 4 * (1 / 2) ^ b) h := by
    bin_row 0; rw [family_coeff 1 1 1 (by norm_num) (fun b => b + 1) (fun b => by ring)]; ite_close
  have r7 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 2 ∧ h = 5 then 3 * (1 / 2 : ℚ) ^ 6 else 0) =
      single 5 (3 * (1 / 2) ^ 6) h := by sq_row 2; unfold single; ite_close
  have r8 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 3 ∧ h = 7 then 3 * (1 / 2 : ℚ) ^ 9 else 0) =
      single 7 (3 * (1 / 2) ^ 9) h := by sq_row 3; unfold single; ite_close
  have r9 : ∑ e ∈ (range h).filter (SqExpOK h),
      (if 4 ≤ e ∧ h = 2 * e + 1 then 3 * (1 / 2 : ℚ) ^ (3 * (e - 1) + 3) else 0) =
      family 3 (fun b => 2 * b + 3) (fun b => 3 * (1 / 2) ^ (3 * b + 3)) h := by
    sq_row ((h - 1) / 2); rw [family_coeff 2 3 3 (by norm_num) (fun b => 2 * b + 3) (fun b => by ring)]; ite_close
  have r10 : ∑ m ∈ (range h).filter (BinExpOK h), (if m = 2 ∧ h = 5 then (1 / 2 : ℚ) ^ 6 else 0) =
      single 5 ((1 / 2) ^ 6) h := by bin_row 2; unfold single; ite_close
  have r11 : ∑ m ∈ (range h).filter (BinExpOK h),
      (if 3 ≤ m ∧ h = 2 * m + 1 then (1 / 2 : ℚ) ^ (3 * (m - 1) + 3) else 0) =
      family 2 (fun b => 2 * b + 3) (fun b => (1 / 2) ^ (3 * b + 3)) h := by
    bin_row ((h - 1) / 2); rw [family_coeff 2 3 2 (by norm_num) (fun b => 2 * b + 3) (fun b => by ring)]; ite_close
  have r12 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 2 ∧ h = 6 then 3 * (1 / 2 : ℚ) ^ 7 else 0) =
      single 6 (3 * (1 / 2) ^ 7) h := by sq_row 2; unfold single; ite_close
  have r13 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 2 ∧ h = 7 then 3 * (1 / 2 : ℚ) ^ 8 else 0) =
      single 7 (3 * (1 / 2) ^ 8) h := by sq_row 2; unfold single; ite_close
  have r14 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 3 ∧ h = 8 then 3 * (1 / 2 : ℚ) ^ 10 else 0) =
      single 8 (3 * (1 / 2) ^ 10) h := by sq_row 3; unfold single; ite_close
  have r15 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 3 ∧ h = 9 then 3 * (1 / 2 : ℚ) ^ 11 else 0) =
      single 9 (3 * (1 / 2) ^ 11) h := by sq_row 3; unfold single; ite_close
  have r16 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 2 ∧ 8 ≤ h then 3 * (1 / 2 : ℚ) ^ ((h - 4) + 5) else 0) =
      family 4 (fun c => c + 4) (fun c => 3 * (1 / 2) ^ (c + 5)) h := by
    sq_row 2; rw [family_coeff 1 4 4 (by norm_num) (fun c => c + 4) (fun b => by ring)]; ite_close
  have r17 : ∑ e ∈ (range h).filter (SqExpOK h),
      (if 4 ≤ e ∧ h = 2 * e + 2 then 3 * (1 / 2 : ℚ) ^ (3 * (e - 1) + 4) else 0) =
      family 3 (fun b => 2 * b + 4) (fun b => 3 * (1 / 2) ^ (3 * b + 4)) h := by
    sq_row ((h - 2) / 2); rw [family_coeff 2 4 3 (by norm_num) (fun b => 2 * b + 4) (fun b => by ring)]; ite_close
  have r18 : ∑ e ∈ (range h).filter (SqExpOK h),
      (if 4 ≤ e ∧ h = 2 * e + 3 then 3 * (1 / 2 : ℚ) ^ (3 * (e - 1) + 5) else 0) =
      family 3 (fun b => 2 * b + 5) (fun b => 3 * (1 / 2) ^ (3 * b + 5)) h := by
    sq_row ((h - 3) / 2); rw [family_coeff 2 5 3 (by norm_num) (fun b => 2 * b + 5) (fun b => by ring)]; ite_close
  have r19 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 3 ∧ 10 ≤ h then 3 * (1 / 2 : ℚ) ^ ((h - 5) + 7) else 0) =
      family 5 (fun c => c + 5) (fun c => 3 * (1 / 2) ^ (c + 7)) h := by
    sq_row 3; rw [family_coeff 1 5 5 (by norm_num) (fun c => c + 5) (fun b => by ring)]; ite_close
  have r20 : ∑ e ∈ (range h).filter (SqExpOK h),
      (if 4 ≤ e ∧ 2 * e + 4 ≤ h then 3 * (1 / 2 : ℚ) ^ (2 * (e - 1) + (h - 2 - e) + 3) else 0) =
      family20 (fun b c => 3 * (1 / 2) ^ (2 * b + c + 3)) h := by
    rw [family20_eq]
  simp only [sqValA, binValA, Finset.sum_add_distrib]
  rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20]
  unfold dyadicA4
  ring

/-- **Table 5.3, column $|4B^*|$, regrouped by the exponents of the class representatives.** -/
theorem dyadicBmag_eq (h : ℕ) :
    dyadicBmag h = ∑ e ∈ (range h).filter (SqExpOK h), sqValB h e +
      ∑ m ∈ (range h).filter (BinExpOK h), binValB h m := by
  have r1 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 1 ∧ h = 3 then (1 / 2 : ℚ) ^ 2 else 0) =
      single 3 ((1 / 2) ^ 2) h := by sq_row 1; unfold single; ite_close
  have r3 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 1 ∧ h = 5 then 3 * (1 / 2 : ℚ) ^ 6 else 0) =
      single 5 (3 * (1 / 2) ^ 6) h := by sq_row 1; unfold single; ite_close
  have r4 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 1 ∧ 6 ≤ h then
      (if Even (h - 3) then 3 * (1 / 2 : ℚ) ^ ((h - 3) + 4) else 0) else 0) =
      family 3 (fun b => b + 3) (fun b => if Even b then 3 * (1 / 2) ^ (b + 4) else 0) h := by
    sq_row 1; rw [family_coeff 1 3 3 (by norm_num) (fun b => b + 3) (fun b => by ring)]; ite_close
  have r5 : ∑ m ∈ (range h).filter (BinExpOK h), (if m = 0 ∧ h = 1 then (4 : ℚ) else 0) = single 1 4 h := by
    bin_row 0; unfold single; ite_close
  have r6 : ∑ m ∈ (range h).filter (BinExpOK h), (if m = 0 ∧ 2 ≤ h then
      (if Even (h - 1) then 4 * (1 / 2 : ℚ) ^ (h - 1) else 2 * (1 / 2) ^ (h - 1)) else 0) =
      family 1 (fun b => b + 1) (fun b => if Even b then 4 * (1 / 2) ^ b else 2 * (1 / 2) ^ b) h := by
    bin_row 0; rw [family_coeff 1 1 1 (by norm_num) (fun b => b + 1) (fun b => by ring)]; ite_close
  have r8 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 3 ∧ h = 7 then 3 * (1 / 2 : ℚ) ^ 10 else 0) =
      single 7 (3 * (1 / 2) ^ 10) h := by sq_row 3; unfold single; ite_close
  have r9 : ∑ e ∈ (range h).filter (SqExpOK h), (if 4 ≤ e ∧ h = 2 * e + 1 then
      (if Even (e - 1) then 3 * (1 / 2 : ℚ) ^ (3 * (e - 1) + 4) else 0) else 0) =
      family 3 (fun b => 2 * b + 3) (fun b => if Even b then 3 * (1 / 2) ^ (3 * b + 4) else 0) h := by
    sq_row ((h - 1) / 2); rw [family_coeff 2 3 3 (by norm_num) (fun b => 2 * b + 3) (fun b => by ring)]; ite_close
  have r10 : ∑ m ∈ (range h).filter (BinExpOK h), (if m = 2 ∧ h = 5 then (1 / 2 : ℚ) ^ 6 else 0) =
      single 5 ((1 / 2) ^ 6) h := by bin_row 2; unfold single; ite_close
  have r11 : ∑ m ∈ (range h).filter (BinExpOK h), (if 3 ≤ m ∧ h = 2 * m + 1 then
      (if Even (m - 1) then (1 / 2 : ℚ) ^ (3 * (m - 1) + 4) else (1 / 2) ^ (3 * (m - 1) + 3)) else 0) =
      family 2 (fun b => 2 * b + 3)
        (fun b => if Even b then (1 / 2) ^ (3 * b + 4) else (1 / 2) ^ (3 * b + 3)) h := by
    bin_row ((h - 1) / 2); rw [family_coeff 2 3 2 (by norm_num) (fun b => 2 * b + 3) (fun b => by ring)]; ite_close
  have r15 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 3 ∧ h = 9 then 3 * (1 / 2 : ℚ) ^ 12 else 0) =
      single 9 (3 * (1 / 2) ^ 12) h := by sq_row 3; unfold single; ite_close
  have r18 : ∑ e ∈ (range h).filter (SqExpOK h), (if 4 ≤ e ∧ h = 2 * e + 3 then
      (if Even (e - 1) then 3 * (1 / 2 : ℚ) ^ (3 * (e - 1) + 6) else 0) else 0) =
      family 3 (fun b => 2 * b + 5) (fun b => if Even b then 3 * (1 / 2) ^ (3 * b + 6) else 0) h := by
    sq_row ((h - 3) / 2); rw [family_coeff 2 5 3 (by norm_num) (fun b => 2 * b + 5) (fun b => by ring)]; ite_close
  have r19 : ∑ e ∈ (range h).filter (SqExpOK h), (if e = 3 ∧ 10 ≤ h then
      (if Even (h - 5) then 3 * (1 / 2 : ℚ) ^ ((h - 5) + 8) else 0) else 0) =
      family 5 (fun c => c + 5) (fun c => if Even c then 3 * (1 / 2) ^ (c + 8) else 0) h := by
    sq_row 3; rw [family_coeff 1 5 5 (by norm_num) (fun c => c + 5) (fun b => by ring)]; ite_close
  have r20 : ∑ e ∈ (range h).filter (SqExpOK h), (if 4 ≤ e ∧ 2 * e + 4 ≤ h then
      (if Even (e - 1) ∧ Even (h - 2 - e) then 3 * (1 / 2 : ℚ) ^ (2 * (e - 1) + (h - 2 - e) + 4) else 0) else 0) =
      family20 (fun b c => if Even b ∧ Even c then 3 * (1 / 2) ^ (2 * b + c + 4) else 0) h := by
    rw [family20_eq]
  simp only [sqValB, binValB, Finset.sum_add_distrib]
  rw [r1, r3, r4, r5, r6, r8, r9, r10, r11, r15, r18, r19, r20]
  unfold dyadicBmag
  ring

end QuadFormsKB.Dyadic7
