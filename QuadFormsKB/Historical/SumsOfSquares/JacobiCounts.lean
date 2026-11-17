/-
# Jacobi's counts for four and eight squares, in Eisenstein's and Smith's wording (wrappers)

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`).  Targets
, all **wrappers** of theorems already proved in this library:

* (Eisenstein, *Mathematische Abhandlungen* (1847), 6. *Neue Theoreme der höhern Arithmetik*, p. 193,
  `eisenstein1847-abhandlungen:p193.5`): $r_4(m) = 8\sigma(m)$ for odd $m$ (`four_squares_odd`), wrapper of
  `Siegel.repNum_sumSq_four` (Jacobi's four-squares theorem, proved here through $E_2$).
* (same work, p. 195, `eisenstein1847-abhandlungen:p195.4`): $r_8(m) = 16\sum_{d \mid m}d^3$ for odd $m$
  (`eight_squares_odd`), wrapper of `MorenoWagstaff.repNum_sumSq_eight_odd`.
* (Smith, *Collected Mathematical Papers* I, p. 307, `smith1894-papers1:p307.4`):
  $r_8(N) = 16\sum_{d \mid N}(-1)^{N+d}d^3$ for every $N \ge 1$ (`eight_squares`), wrapper of
  `MorenoWagstaff.repNum_sumSq_eight` (proved here through $E_4$ on $\Gamma_0(4)$). The row's second sentence (the
  number of representations of $8N$ by eight positive odd squares) is not formalized (loose end).

Here $r_s(m)$ = `sqRep s m` $= \#\{\vec x \in \mathbb Z^s : x_0^2 + \dots + x_{s-1}^2 = m\}$ (ordered, signed).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Wave2.EightSquares
import QuadFormsKB.Historical.SumsOfSquares.Eisenstein

namespace QuadFormsKB.Historical.SumsOfSquares

open QuadFormsKB.Siegel
open scoped ArithmeticFunction.sigma

/-- `sqRep s m` is the library's representation number `repNum (sumSq s) m`. -/
theorem sqRep_eq_repNum (s m : ℕ) : sqRep s m = repNum (sumSq s) m := by
  unfold sqRep repNum
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [repSet, eval_sumSq])

/-- **Four squares, odd $m$** (Eisenstein, *Math. Abh.* (1847), p. 193, after Jacobi):
for odd $m$, the number of representations of $m$ as an ordered sum of four integer squares is
$8\sigma(m) = 8\sum_{d \mid m} d$. **Wrapper** of `Siegel.repNum_sumSq_four`. -/
@[kb "eisenstein1847" "6. Neue Theoreme der höhern Arithmetik, p. 193 (occurrence eisenstein1847-abhandlungen:p193.5)"]
theorem four_squares_odd (m : ℕ) (hm : Odd m) : sqRep 4 m = 8 * ∑ d ∈ m.divisors, d := by
  rw [sqRep_eq_repNum, repNum_sumSq_four hm.pos]
  congr 1
  refine Finset.sum_congr (Finset.filter_true_of_mem fun d hd h4 => ?_) fun _ _ => rfl
  have : 2 ∣ m := (dvd_trans (by norm_num) h4).trans (Nat.dvd_of_mem_divisors hd)
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)

/-- **Eight squares, odd $m$** (Eisenstein, *Math. Abh.* (1847), p. 195, after Jacobi):
for odd $m$, $r_8(m) = 16\sum_{d \mid m} d^3$. **Wrapper** of `MorenoWagstaff.repNum_sumSq_eight_odd`. -/
@[kb "eisenstein1847" "6. Neue Theoreme der höhern Arithmetik, p. 195 (occurrence eisenstein1847-abhandlungen:p195.4)"]
theorem eight_squares_odd (m : ℕ) (hm : Odd m) : sqRep 8 m = 16 * ∑ d ∈ m.divisors, d ^ 3 := by
  rw [sqRep_eq_repNum, MorenoWagstaff.repNum_sumSq_eight_odd hm, ArithmeticFunction.sigma_apply]

/-- **Jacobi's eight-squares theorem** (Smith, *Collected Mathematical Papers* I, p. 307):
for every $N \ge 1$, $r_8(N) = 16\sum_{d \mid N}(-1)^{N+d}d^3$ (so $16\sigma_3(N)$ for odd $N$). **Wrapper** of
`MorenoWagstaff.repNum_sumSq_eight`. -/
@[kb "smith1894a" "p. 307 (occurrence smith1894-papers1:p307.4)"]
theorem eight_squares (N : ℕ) (hN : 1 ≤ N) :
    (sqRep 8 N : ℤ) = 16 * ∑ d ∈ N.divisors, (-1 : ℤ) ^ (N + d) * (d : ℤ) ^ 3 := by
  rw [sqRep_eq_repNum, MorenoWagstaff.repNum_sumSq_eight hN]

end QuadFormsKB.Historical.SumsOfSquares
