/-
# Moreno–Wagstaff 2005, §8.4: Sprague's theorem

**Source.** R. Sprague, *Über Zerlegungen in ungleiche Quadratzahlen* (1948); cited in C. J. Moreno and
S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), §8.4, p. 328.

**Proves**
* `spragueTheorem` (**proved**, unconditional): a positive integer is a sum of distinct positive squares iff it is
  not one of the 31 exceptions $2, 3, 6, \dots, 128$.

**Method.** Let $A_k$ be the set of sums of distinct squares from $\{1^2,\dots,k^2\}$ and $T_k = \sum_{i \le k} i^2$.
The set $A_k$ is encoded as the bitmask `mask k` (`mask (k+1) = mask k ||| mask k <<< (k+1)^2`), and a finite
check by `decide` (kernel Nat arithmetic) shows: the 31 exceptions are not in $A_{11}$ (any representation of
$n \le 128$ uses only $i \le 11$), and every other $n \le 521$ lies in $A_{12}$ ($T_{12} = 650$). By induction on
$k \ge 12$, $[129, T_k - 129] \subseteq A_k$ (the intervals $[129, T_k-129]$ and $[129 + (k+1)^2, T_{k+1}-129]$
overlap), and $T_k \to \infty$.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Statements

namespace QuadFormsKB.MorenoWagstaff

namespace Sprague

/-- Bitmask whose set bits are the sums of distinct squares from $\{1^2, \dots, k^2\}$. -/
def mask : ℕ → ℕ
  | 0 => 1
  | k + 1 => mask k ||| (mask k <<< (k + 1) ^ 2)

/-- $T_k = 1^2 + \dots + k^2$. -/
def T : ℕ → ℕ
  | 0 => 0
  | k + 1 => T k + (k + 1) ^ 2

/-- $n$ is a sum of distinct squares from $\{1^2,\dots,k^2\}$. -/
def A (k n : ℕ) : Prop := ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 k ∧ ∑ i ∈ S, i ^ 2 = n

theorem testBit_mask (k n : ℕ) : (mask k).testBit n = true ↔ A k n := by
  induction k generalizing n with
  | zero =>
    constructor
    · intro h
      have : n = 0 := by simpa [mask, Nat.testBit_one_eq_true_iff_self_eq_zero] using h
      exact ⟨∅, by simp, by simp [this]⟩
    · rintro ⟨S, hS, rfl⟩
      have : S = ∅ := by simpa using hS
      simp [this, mask]
  | succ k ih =>
    have key : (mask (k + 1)).testBit n = true ↔
        (mask k).testBit n = true ∨ ((k + 1) ^ 2 ≤ n ∧ (mask k).testBit (n - (k + 1) ^ 2) = true) := by
      simp [mask, Nat.testBit_shiftLeft]
    rw [key, ih, ih]
    constructor
    · rintro (⟨S, hS, h⟩ | ⟨hle, S, hS, h⟩)
      · exact ⟨S, hS.trans (Finset.Icc_subset_Icc le_rfl (by omega)), h⟩
      · have hn : k + 1 ∉ S := fun hm => by have := Finset.mem_Icc.1 (hS hm); omega
        refine ⟨insert (k + 1) S, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simp
          · have := Finset.mem_Icc.1 (hS hx); simp only [Finset.mem_Icc]; omega
        · rw [Finset.sum_insert hn, h]; omega
    · rintro ⟨S, hS, h⟩
      by_cases hm : k + 1 ∈ S
      · right
        have hsum := Finset.add_sum_erase S (fun i => i ^ 2) hm
        refine ⟨by omega, S.erase (k + 1), ?_, by omega⟩
        intro x hx
        have h1 := Finset.mem_Icc.1 (hS (Finset.mem_of_mem_erase hx))
        have h2 := Finset.ne_of_mem_erase hx
        simp only [Finset.mem_Icc]; omega
      · left
        refine ⟨S, ?_, h⟩
        intro x hx
        have h1 := Finset.mem_Icc.1 (hS hx)
        have h2 : x ≠ k + 1 := fun e => hm (e ▸ hx)
        simp only [Finset.mem_Icc]; omega

theorem T_ge_sq (k : ℕ) : k ^ 2 ≤ T k := by
  cases k with
  | zero => simp [T]
  | succ k => simp only [T]; omega

theorem T_big (k : ℕ) (hk : 12 ≤ k) : 257 + (k + 1) ^ 2 ≤ T k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => simp only [T]; nlinarith

theorem base_check : ∀ n, n < 522 → 0 < n →
    n ∉ ({2, 3, 6, 7, 8, 11, 12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32,
      33, 43, 44, 47, 48, 60, 67, 72, 76, 92, 96, 108, 112, 128} : Finset ℕ) →
    (mask 12).testBit n = true := by
  decide +kernel

theorem exc_check : ∀ n ∈ ({2, 3, 6, 7, 8, 11, 12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32,
      33, 43, 44, 47, 48, 60, 67, 72, 76, 92, 96, 108, 112, 128} : Finset ℕ),
    (mask 11).testBit n = false := by
  decide +kernel

theorem interval (k : ℕ) (hk : 12 ≤ k) : ∀ n, 129 ≤ n → n + 129 ≤ T k → A k n := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro n h1 h2
    rw [← testBit_mask]
    apply base_check n (by simp [T] at h2; omega) (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  | succ k hk ih =>
    intro n h1 h2
    have hT := T_big k hk
    simp only [T] at h2
    by_cases hc : n + 129 ≤ T k
    · obtain ⟨S, hS, h⟩ := ih n h1 hc
      exact ⟨S, hS.trans (Finset.Icc_subset_Icc le_rfl (by omega)), h⟩
    · obtain ⟨S, hS, h⟩ := ih (n - (k + 1) ^ 2) (by omega) (by omega)
      have hn : k + 1 ∉ S := fun hm => by have := Finset.mem_Icc.1 (hS hm); omega
      refine ⟨insert (k + 1) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · simp
        · have := Finset.mem_Icc.1 (hS hx); simp only [Finset.mem_Icc]; omega
      · rw [Finset.sum_insert hn, h]; omega

end Sprague

open Sprague in
/-- **Sprague's theorem** (Moreno–Wagstaff §8.4, p. 328; Sprague 1948), proved unconditionally. A positive integer
is a sum of distinct positive squares iff it is not one of the 31 listed exceptions. Proof: bitmask computation
(`decide`) for $n \le 521$ with squares up to $12^2$ and for the exceptions with squares up to $11^2$, then the
interval induction $[129, T_k - 129] \subseteq A_k$ for $k \ge 12$. -/
theorem spragueTheorem : SpragueTheorem := by
  intro n hn
  constructor
  · rintro ⟨S, hpos, hsum⟩ hex
    have hsub : S ⊆ Finset.Icc 1 11 := by
      intro x hx
      have h1 : x ^ 2 ≤ ∑ k ∈ S, k ^ 2 :=
        Finset.single_le_sum (f := fun k => k ^ 2) (fun _ _ => Nat.zero_le _) hx
      have hn128 : n ≤ 128 := by
        revert hex; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have : x ≤ 11 := by nlinarith
      exact Finset.mem_Icc.2 ⟨hpos x hx, this⟩
    have := (testBit_mask 11 n).2 ⟨S, hsub, hsum⟩
    rw [exc_check n hex] at this
    exact absurd this (by simp)
  · intro hex
    by_cases h : n ≤ 128
    · have hb := base_check n (by omega) hn hex
      obtain ⟨S, hS, hs⟩ := (testBit_mask 12 n).1 hb
      exact ⟨S, fun k hk => (Finset.mem_Icc.1 (hS hk)).1, hs⟩
    · obtain ⟨S, hS, hs⟩ := interval (n + 129) (by omega) n (by omega)
        (by have := T_ge_sq (n + 129); nlinarith)
      exact ⟨S, fun k hk => (Finset.mem_Icc.1 (hS hk)).1, hs⟩

end QuadFormsKB.MorenoWagstaff
