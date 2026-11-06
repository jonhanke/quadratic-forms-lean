import Mathlib
import QuadFormsKB.Citation

/-!
# Saha–Hanke §6.2–6.3: the counting function used by the verified case trees

Source: R. Saha and J. Hanke, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §5.3 and §6.2–6.3.

For a reduced form $f = [a, b, c]$ ($0 \le b \le a \le c$, $a > 0$) let
$$V = \{(1,0), (0,1), (-1,1), (1,1), (-2,1), (2,1), (-3,1), (3,1), (-1,2), (1,2), (-3,2), (3,2)\},$$
twelve strongly primitive vectors. `cntV a b c t` is the number of $v \in V$ with $f(v) \le t$, written out as a sum
of indicators `ind x t` $= [x \le t]$ of the twelve values $f(v)$ (linear in $a, b, c$):
$a$, $c$, $a - b + c$, $a + b + c$, $4a \mp 2b + c$, $9a \mp 3b + c$, $a \mp 2b + 4c$, $9a \mp 6b + 4c$.

`RefinementCount.lean` proves that the cumulative strongly primitive count $N_f(t)$ satisfies
$N_f(t) \ge$ `cntV a b c t` always, with equality when $t < 16a - 4b + c$ and $t < 6c$ (every other strongly
primitive vector has a value $\ge \min(16a - 4b + c, 6c)$). The files `RefinementAB11.lean`, `RefinementAB12.lean`
are the case trees over these linear data.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm.Refinement

/-- The indicator $[x \le t] \in \{0, 1\}$. -/
def ind (x t : ℤ) : ℤ := if x ≤ t then 1 else 0

lemma ind_one (x t : ℤ) (h : x ≤ t) : ind x t = 1 := if_pos h

lemma ind_zero (x t : ℤ) (h : t < x) : ind x t = 0 := if_neg (not_le.mpr h)

lemma ind_bounds (x t : ℤ) : 0 ≤ ind x t ∧ ind x t ≤ 1 := by
  unfold ind; split_ifs <;> omega

/-- **The number of the twelve vectors of $V$ with value $\le t$** for the form $[a, b, c]$. -/
def cntV (a b c t : ℤ) : ℤ :=
  ind a t + ind c t + ind (a - b + c) t + ind (a + b + c) t + ind (4 * a - 2 * b + c) t +
    ind (4 * a + 2 * b + c) t + ind (9 * a - 3 * b + c) t + ind (9 * a + 3 * b + c) t +
    ind (a - 2 * b + 4 * c) t + ind (a + 2 * b + 4 * c) t + ind (9 * a - 6 * b + 4 * c) t +
    ind (9 * a + 6 * b + 4 * c) t

end QuadFormsKB.Hanke2023ThreeTerm.Refinement
