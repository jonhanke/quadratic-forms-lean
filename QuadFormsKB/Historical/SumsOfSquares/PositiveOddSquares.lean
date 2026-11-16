/-
# Sums of six and of eight positive odd squares (Smith, after Jacobi): statements

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`). 
Targets, the second sentences of two rows whose first
sentences are proved in `SixSquaresAll.lean` and `JacobiCounts.lean`:

* (Smith, *Collected Mathematical Papers* I, p. 307): for odd $N$ the number of ordered
  representations of $2N$ as a sum of six positive odd squares is
  $\frac1{16}\sum_{\delta \mid N}\bigl[(-1)^{(\delta'-1)/2} - (-1)^{(\delta-1)/2}\bigr]\delta^2$, $\delta' = N/\delta$
  (`SmithSixOddSquares`, **stated**).
* (Smith, *ibid.*, p. 307): the number of ordered representations of $8N$ as a sum of eight positive
  odd squares is $\sum_{d \mid N,\ N/d\ \mathrm{odd}} d^3$ (`SmithEightOddSquares`, **stated**).

Both were checked by brute force (six squares for odd $N \le 21$, eight squares for $N \le 11$). They are stated, not
proved: the source derives them from the theta identities for $\theta_2^6$, $\theta_2^8$ (Jacobi's
$\theta_3^4 = \theta_2^4 + \theta_4^4$), which are not available here.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import QuadFormsKB.Citation

namespace QuadFormsKB.Historical.SumsOfSquares

/-- The number of ordered representations of $M$ as a sum of $k$ positive odd squares. -/
noncomputable def oddSqRep (k M : ℕ) : ℕ :=
  Nat.card {x : Fin k → ℕ // (∀ i, Odd (x i)) ∧ ∑ i, x i ^ 2 = M}

/-- **Stated** (second sentence; Smith, *Collected Mathematical Papers* I, p. 307):
for odd $N$, $16 \cdot \#\{\text{six positive odd squares summing to } 2N\} =
\sum_{\delta \mid N}\bigl[(-1)^{(\delta'-1)/2} - (-1)^{(\delta-1)/2}\bigr]\delta^2$ with $\delta' = N/\delta$. -/
@[kb "smith1894a" "p. 307 (occurrence smith1894-papers1:p307.2) [unverified locator]"]
def SmithSixOddSquares : Prop :=
  ∀ N : ℕ, Odd N →
    16 * (oddSqRep 6 (2 * N) : ℤ) =
      ∑ δ ∈ N.divisors, ((-1) ^ ((N / δ - 1) / 2) - (-1) ^ ((δ - 1) / 2)) * (δ : ℤ) ^ 2

/-- **Stated** (second sentence; Smith, *Collected Mathematical Papers* I, p. 307):
for $N \ge 1$, $\#\{\text{eight positive odd squares summing to } 8N\} = \sum_{d \mid N,\ N/d\ \mathrm{odd}} d^3$. -/
@[kb "smith1894a" "p. 307 (occurrence smith1894-papers1:p307.4) [unverified locator]"]
def SmithEightOddSquares : Prop :=
  ∀ N : ℕ, 1 ≤ N → oddSqRep 8 (8 * N) = ∑ d ∈ N.divisors.filter (fun d => Odd (N / d)), d ^ 3

end QuadFormsKB.Historical.SumsOfSquares
