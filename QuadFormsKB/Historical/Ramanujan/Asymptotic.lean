/-
# Ramanujan's singular series for $r_{2s}(n)$ and the asymptotic $r_{2s} \sim \delta_{2s}$: statement for even $s$

**Library** `QuadFormsKB.Historical.Ramanujan` (historical library, not imported by `QuadFormsKB`).  Targets
: second clause, and 
(Ramanujan, *On certain trigonometrical sums and their applications in the theory of numbers* (1918), §§ 11-12,
*Collected Papers* (1927) No. 21): $r_{2s}(n) = \delta_{2s}(n) + e_{2s}(n)$ with
$$\delta_{2s}(n) = \frac{\pi^s n^{s-1}}{\Gamma(s)}\sum_{q \ge 1} q^{-s}\,\tilde c_{\rho(q)}(n),\qquad
  \rho(q) = q\ (q\ \text{odd}),\ 2q\ (q\ \text{even}),$$
and $e_{2s}(n)$ of lower order than $\delta_{2s}(n)$, so $r_{2s}(n) \sim \delta_{2s}(n)$.

For even $s$ the twisted sums are $\tilde c_r(n) = c_r(n)\cos\frac{\pi s(r-1)}2$, so (11.11), (11.21)
$$\delta_{2s}(n) = \frac{\pi^s n^{s-1}}{(s-1)!}\sum_{q \ge 1}\varepsilon_s(q)\,q^{-s}c_{\rho(q)}(n),\qquad
  \varepsilon_s(q) = -1 \text{ if } q \text{ is even and } s \equiv 2 \pmod 4,\ \text{else } 1,$$
with Ramanujan's sum $c_r(n) = \sum_{1 \le h \le r,\ (h, r) = 1}\cos(2\pi h n / r)$ (`ramanujanSum`,
`ramanujanDelta`). `RamanujanAsymptoticEven` **states** $r_{2s}(n)/\delta_{2s}(n) \to 1$ for every even $s \ge 2$
(sums of $4k$ squares). The odd $s$ (sums of $4k + 2$ squares, (11.31), (11.41)) involve Ramanujan's second sums
$s_r(n)$, whose definition is not recorded in the historical sources; they are not stated.
For $s = 2, 4$ the series reproduces $r_4$, $r_8$ exactly (checked numerically in the historical sources for $n \le 30$; the
divisor-sum formulas are `ramanujan_divisor_sums`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.SetTheory.Cardinal.Finite
import QuadFormsKB.Citation

namespace QuadFormsKB.Historical.Ramanujan

open Filter Topology

/-- Ramanujan's sum $c_r(n) = \sum_{1 \le h \le r,\ (h, r) = 1}\cos(2\pi h n / r)$. -/
noncomputable def ramanujanSum (r n : ℕ) : ℝ :=
  ∑ h ∈ (Finset.Icc 1 r).filter (fun h => Nat.Coprime h r), Real.cos (2 * Real.pi * h * n / r)

/-- Ramanujan's $\delta_{2s}(n)$ for even $s$ ((11.11) for $s \equiv 0 \pmod 4$, (11.21) for $s \equiv 2 \pmod 4$):
$\frac{\pi^s n^{s-1}}{(s-1)!}\sum_{q \ge 1}\varepsilon_s(q)q^{-s}c_{\rho(q)}(n)$. -/
noncomputable def ramanujanDelta (s n : ℕ) : ℝ :=
  Real.pi ^ s * (n : ℝ) ^ (s - 1) / ((s - 1).factorial : ℝ) *
    ∑' q : ℕ, if q = 0 then 0 else
      (if q % 2 = 0 ∧ s % 4 = 2 then -1 else 1) / (q : ℝ) ^ s *
        ramanujanSum (if q % 2 = 1 then q else 2 * q) n

/-- **Stated** (second clause, and ; Ramanujan 1918, *Collected
Papers* No. 21, §§ 11-12): for every even $s \ge 2$, the number $r_{2s}(n)$ of representations of $n$ as a sum of
$2s$ squares satisfies $r_{2s}(n)/\delta_{2s}(n) \to 1$ as $n \to \infty$. -/
@[kb "ramanujan1927" "No. 21, §§ 11-12 [unverified locator]"]
def RamanujanAsymptoticEven : Prop :=
  ∀ s : ℕ, 2 ≤ s → Even s →
    Tendsto (fun n : ℕ => (Nat.card {x : Fin (2 * s) → ℤ // ∑ i, x i ^ 2 = (n : ℤ)} : ℝ) / ramanujanDelta s n)
      atTop (𝓝 1)

end QuadFormsKB.Historical.Ramanujan
