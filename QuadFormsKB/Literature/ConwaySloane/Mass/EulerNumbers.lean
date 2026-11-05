/-
# Conway–Sloane 1988, §8, (16): $\zeta_{-1}(s)$ and the Euler numbers

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, formula (16), p. 268: for odd $s$,
$$\zeta_{-1}(s) = 1 - 3^{-s} + 5^{-s} - 7^{-s} + \cdots = \frac{(\frac12\pi)^s}{2\,(s-1)!}\,\lvert E_{s-1}\rvert,$$
with $E_n$ the Euler numbers (Abramowitz–Stegun, chap. 23).

**Definition.** Mathlib has no Euler numbers. `eulerNum n` is the integer $E_n$ defined by the standard recurrence
$$E_0 = 1,\qquad \sum_{k=0}^{n}\binom nk E_k = 0\quad(n \ge 2\text{ even}),\qquad E_n = 0\quad(n\text{ odd}),$$
so $E_0, E_2, E_4, \dots = 1, -1, 5, -61, 1385, -50521, \dots$ ($\operatorname{sech} t = \sum_n E_n t^n/n!$). It is computed by
`eulerList n` $= [E_0, \dots, E_{n-1}]$; `eulerNum_rec` proves the recurrence.

**Proves**
* `eulerNum_zero`, `eulerNum_odd`, `eulerNum_rec`: the defining properties; `eulerNum_values`: $E_0, \dots, E_{10}$.
* `zetaD_neg_one_euler` ((16)): the formula for $s = 1, 3, 5, 7, 9, 11$ (every odd $s$ of Table 6, $s \le 12$), from
  `zetaD_neg_one_one` ($s = 1$) and the closed form (13) for $D = -1$ (`zetaD_neg_one_odd`, $s \ge 3$).

**All odd $s$:** (16) for every odd $s$ is `zetaD_neg_one_euler_all` (`Mass/EulerBernoulli.lean`), through the identity
between the Euler numbers and the Bernoulli polynomials at $\frac14, \frac34$ (`eulerNum_eq_bernoulli`).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6

namespace QuadFormsKB.ConwaySloane.Mass

open Finset
open scoped Real

/-- The next Euler number from the list $[E_0, \dots, E_{n-1}]$: $E_0 = 1$, $E_n = 0$ for odd $n$, and
$E_n = -\sum_{k<n}\binom nk E_k$ for even $n \ge 2$. -/
def eulerNext (n : ℕ) (L : List ℤ) : ℤ :=
  if n = 0 then 1 else if n % 2 = 1 then 0
  else -((List.range n).map (fun k => (n.choose k : ℤ) * L.getD k 0)).sum

/-- The list $[E_0, \dots, E_{n-1}]$ of the first $n$ Euler numbers. -/
def eulerList : ℕ → List ℤ
  | 0 => []
  | n + 1 => eulerList n ++ [eulerNext n (eulerList n)]

/-- **The Euler numbers** $E_n$ (Conway–Sloane (16), p. 268; Abramowitz–Stegun, chap. 23), defined by the recurrence
$E_0 = 1$, $E_n = 0$ for odd $n$, and $\sum_{k=0}^{n}\binom nk E_k = 0$ for even $n \ge 2$ (`eulerNum_rec`); the
coefficients of $\operatorname{sech} t = \sum_n E_n t^n/n!$. -/
@[kb "conwaysloane1988" "§8 (16), p. 268 (Euler numbers)"]
def eulerNum (n : ℕ) : ℤ := (eulerList (n + 1)).getD n 0

theorem eulerList_length (n : ℕ) : (eulerList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [eulerList, ih]

theorem eulerList_getD {n k : ℕ} (hk : k < n) : (eulerList n).getD k 0 = eulerNum k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · rw [eulerList, List.getD_append _ _ _ _ (by rw [eulerList_length]; exact h), ih h]
    · rfl

theorem eulerNum_eq_next (n : ℕ) : eulerNum n = eulerNext n (eulerList n) := by
  rw [eulerNum, eulerList, List.getD_append_right _ _ _ _ (by rw [eulerList_length]),
    eulerList_length, Nat.sub_self]
  rfl

theorem eulerNum_zero : eulerNum 0 = 1 := rfl

theorem eulerNum_odd {n : ℕ} (hn : n % 2 = 1) : eulerNum n = 0 := by
  rw [eulerNum_eq_next, eulerNext]
  simp only [show n ≠ 0 by omega, hn, ↓reduceIte]

/-- **The recurrence of the Euler numbers**: $\sum_{k=0}^{n}\binom nk E_k = 0$ for even $n \ge 2$. -/
@[kb "conwaysloane1988" "§8 (16), p. 268 (Euler numbers)"]
theorem eulerNum_rec {n : ℕ} (hn : n % 2 = 0) (h2 : n ≠ 0) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * eulerNum k = 0 := by
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, eulerNum_eq_next n, eulerNext]
  simp only [h2, show n % 2 ≠ 1 by omega, ↓reduceIte]
  have : ((List.range n).map (fun k => (n.choose k : ℤ) * (eulerList n).getD k 0)).sum
      = ∑ k ∈ range n, (n.choose k : ℤ) * eulerNum k := by
    rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
    · exact Finset.sum_congr rfl (fun k hk => by rw [eulerList_getD (mem_range.mp hk)])
  rw [this]
  ring

/-- $E_0, \dots, E_{10} = 1, 0, -1, 0, 5, 0, -61, 0, 1385, 0, -50521$. -/
theorem eulerNum_values :
    (List.range 11).map eulerNum = [1, 0, -1, 0, 5, 0, -61, 0, 1385, 0, -50521] := by
  decide

/-- **(16), p. 268**: for odd $s \le 11$,
$$\zeta_{-1}(s) = 1 - 3^{-s} + 5^{-s} - \cdots = \frac{(\frac12\pi)^s}{2\,(s-1)!}\,\lvert E_{s-1}\rvert,$$
$E_n$ the Euler numbers (`eulerNum`). This covers every odd $s$ of Table 6 ($s \le 12$). -/
@[kb "conwaysloane1988" "§8 (16), p. 268"]
theorem zetaD_neg_one_euler {s : ℕ} (hs : s ∈ ({1, 3, 5, 7, 9, 11} : Finset ℕ)) :
    zetaD (-1) s = (π / 2) ^ s / (2 * (s - 1).factorial) * |(eulerNum (s - 1) : ℝ)| := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · have hz : zetaD (-1) 1 = π / 4 := zetaD_neg_one_one
    rw [show eulerNum (1 - 1) = 1 by decide]
    norm_num [hz, Nat.factorial]
    ring
  · have hz : zetaD (-1) 3 = 1 / 32 * π ^ 3 := by
      have := table6_1_3; field_simp at this ⊢; linarith
    rw [show eulerNum (3 - 1) = -1 by decide]
    norm_num [hz, Nat.factorial]
    ring
  · have hz : zetaD (-1) 5 = 5 / 1536 * π ^ 5 := by
      have := table6_1_5; field_simp at this ⊢; linarith
    rw [show eulerNum (5 - 1) = 5 by decide]
    norm_num [hz, Nat.factorial]
    ring
  · have hz : zetaD (-1) 7 = 61 / 184320 * π ^ 7 := by
      have := table6_1_7; field_simp at this ⊢; linarith
    rw [show eulerNum (7 - 1) = -61 by decide]
    norm_num [hz, Nat.factorial]
    ring
  · have hz : zetaD (-1) 9 = 277 / 8257536 * π ^ 9 := by
      have := table6_1_9; field_simp at this ⊢; linarith
    rw [show eulerNum (9 - 1) = 1385 by decide]
    norm_num [hz, Nat.factorial]
    ring
  · have hz : zetaD (-1) 11 = 50521 / 14863564800 * π ^ 11 := by
      have := table6_1_11; field_simp at this ⊢; linarith
    rw [show eulerNum (11 - 1) = -50521 by decide]
    norm_num [hz, Nat.factorial]
    ring

end QuadFormsKB.ConwaySloane.Mass
