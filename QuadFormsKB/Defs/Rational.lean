/-
# Rational quadratic forms and the places of $\mathbb{Q}$

A rational quadratic form is a quadratic polynomial with rational coefficients
(`RatQF n` $=$ `QuadForm ℚ n`). Because its coefficients are rational, it can be evaluated
over **any field $K \supseteq \mathbb{Q}$** (`QuadForm.evalIn`), in particular over each
completion $\mathbb{Q}_v$: $\mathbb{R}$ and the $p$-adic fields $\mathbb{Q}_p$. That is all the
base change the local-global statements need. `Equiv/BaseChange.lean` relates it to Mathlib's
`QuadraticForm.baseChange`.

The places of $\mathbb{Q}$ are `RatPlace` ($\infty$ and the primes $p$). A local condition is
written `atPlace P v`, for a predicate `P` on fields of characteristic $0$. The number-field
version generalizes this shape, with $K_v$ in place of $\mathbb{Q}_v$.
-/
import Mathlib
import QuadFormsKB.Defs.QuadForm

open Matrix

namespace QuadFormsKB

/-- **A rational quadratic form in $n$ variables:** `QuadForm ℚ n`, the polynomial
$Q(\vec{x}) = \sum_{0 \le i \le j < n} c_{ij}\, x_i x_j$ with $c_{ij} \in \mathbb{Q}$ (upper-triangular
coefficient matrix). It is evaluated over any field $K \supseteq \mathbb{Q}$ with `evalIn K`.

See also: `RatQF.IsIntegral` (integer coefficients), `RatQF.gram` (the Gram matrix over
$\mathbb{Q}$). -/
abbrev RatQF (n : ℕ) := QuadForm ℚ n

/-- The places of ℚ: the archimedean place and one place for each prime. -/
inductive RatPlace
  | infinite
  | finite (p : Nat.Primes)

namespace RatPlace

/-- **A property at the place $v$:** `atPlace P v` means $P$ holds over the completion
$\mathbb{Q}_v$, namely $P(\mathbb{R})$ for $v = \infty$ and $P(\mathbb{Q}_p)$ for $v = p$.

$P$ is a predicate on fields of characteristic $0$, so it can mention any form with rational
coefficients evaluated over the field (e.g. `fun K _ _ => Q.IsotropicIn K`). -/
def atPlace (P : (K : Type) → [Field K] → [CharZero K] → Prop) : RatPlace → Prop
  | infinite => P ℝ
  | finite p => haveI : Fact p.1.Prime := ⟨p.2⟩; P ℚ_[p.1]

/-- **A property everywhere locally:** $P$ holds over **every** completion of $\mathbb{Q}$:
over $\mathbb{R}$ and over $\mathbb{Q}_p$ for every prime $p$. This is the right-hand side of
local-global statements such as `hasseMinkowski`. -/
def Everywhere (P : (K : Type) → [Field K] → [CharZero K] → Prop) : Prop :=
  ∀ v, atPlace P v

end RatPlace

end QuadFormsKB
