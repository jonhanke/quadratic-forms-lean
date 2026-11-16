/-
# Ramanujan: $r_2$, $r_4$, $r_6$, $r_8$ are pure divisor sums

**Library** `QuadFormsKB.Historical.Ramanujan` (historical library, not imported by `QuadFormsKB`).  Target
(Ramanujan, *On certain trigonometrical
sums and their applications in the theory of numbers*, Trans. Cambridge Philos. Soc. 22 (1918), *Collected Papers*
(1927), No. 21): writing $r_{2s}(n) = \delta_{2s}(n) + \epsilon_{2s}(n)$ with $\delta_{2s}$ the divisor-function
(Eisenstein) part, $\epsilon_{2s} = 0$ for $s = 1, 2, 3, 4$, i.e. $r_2, r_4, r_6, r_8$ are pure divisor sums; and
$\epsilon_{2s} = o(\delta_{2s})$ for every $s$.

*Partial:* the first clause is `ramanujan_divisor_sums` (**proved**, unconditional): for every $n \ge 1$,
* $r_2(n) = 4\bigl(d_1(n) - d_3(n)\bigr)$ ($d_i$ = number of divisors $\equiv i \bmod 4$);
* $r_4(n) = 8\sum_{d \mid n,\ 4 \nmid d} d$;
* $r_6(n) = 4\sum_{\delta \mid n,\ \delta\ \mathrm{odd}}(-1)^{(\delta-1)/2}\bigl(4(n/\delta)^2 - \delta^2\bigr)$;
* $r_8(n) = 16\sum_{d \mid n}(-1)^{n+d}d^3$.

These are Ramanujan's $\delta_2, \delta_4, \delta_6, \delta_8$ written as divisor sums (his general $\delta_{2s}$ is
given by Bernoulli and Euler numbers; for $2s \le 8$ it reduces to these classical sums). It is a **wrapper** of
`two_squares_count`, `Siegel.repNum_sumSq_four`, `six_squares` (Smith's form, proved in this round) and `eight_squares`.
The second clause ($\epsilon_{2s} = o(\delta_{2s})$ for all $s$, a cusp-form bound) is not formalized (loose end):
$\delta_{2s}$ for general $s$ is not defined here and the bound needs modular forms of weight $s$ on $\Gamma_0(4)$.

Here $r_s(n)$ = `sqRep s n` $= \#\{\vec x \in \mathbb Z^s : x_0^2 + \dots + x_{s-1}^2 = n\}$ (ordered, signed).
-/
import QuadFormsKB.Historical.SumsOfSquares
import QuadFormsKB.Historical.SumsOfSquares.SixSquaresAll

namespace QuadFormsKB.Historical.Ramanujan

open QuadFormsKB.Siegel QuadFormsKB.Historical.SumsOfSquares

/-- **$r_2, r_4, r_6, r_8$ are divisor sums** (first clause: $\epsilon_{2s} = 0$ for
$s \le 4$). **Proved** (wrapper of the four classical formulas). -/
@[kb "ramanujan1927" "No. 21, §§ 11–12 [unverified locator]"]
theorem ramanujan_divisor_sums (n : ℕ) (hn : 1 ≤ n) :
    (sqRep 2 n : ℤ) = 4 * (((n.divisors.filter (· % 4 = 1)).card : ℤ) - (n.divisors.filter (· % 4 = 3)).card) ∧
      sqRep 4 n = 8 * ∑ d ∈ n.divisors.filter (¬ 4 ∣ ·), d ∧
      (sqRep 6 n : ℤ) = 4 * ∑ δ ∈ n.divisors.filter Odd,
        (-1 : ℤ) ^ ((δ - 1) / 2) * (4 * ((n / δ : ℕ) : ℤ) ^ 2 - (δ : ℤ) ^ 2) ∧
      (sqRep 8 n : ℤ) = 16 * ∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 := by
  refine ⟨?_, ?_, six_squares n hn, eight_squares n hn⟩
  · rw [← two_squares_count n hn, sqRep_eq_repNum, ← card_pairs_eq_repNum]
  · rw [sqRep_eq_repNum, repNum_sumSq_four hn]

end QuadFormsKB.Historical.Ramanujan
