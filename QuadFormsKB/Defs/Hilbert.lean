/-
# The Hilbert symbol $(a,b)_K$

**The field is always explicit.** Every Hilbert symbol here is taken over a field $K$
that is passed as an argument, and **all solutions are sought in $K$**. For the
local-global theory over $\mathbb{Q}$, $K$ is a completion of $\mathbb{Q}$, namely
$\mathbb{R}$ or $\mathbb{Q}_p$, and $a, b$ are rationals viewed in $K$ (`RatPlace.hilbert`).
$K = \mathbb{Q}$ itself is allowed, but the local statements never use it.

**One definition** (Serre, *A Course in Arithmetic*, III.1.1), `hilbertSymbol`: for
$a, b \in K^\times$, $(a,b)_K = 1$ iff $z^2 = a x^2 + b y^2$ has a solution
$(x,y,z) \in K^3 \setminus \{0\}$, else $-1$. Other descriptions in the literature are
theorems in `Equiv/Hilbert.lean`, not separate definitions:

* conic: $(a,b)_K = 1 \iff a x^2 + b y^2 = 1$ is solvable in $K$ (for $a, b \ne 0$,
  $2 \ne 0$ in $K$), `hilbertSymbol_eq_one_iff_conic`;
* isotropy: $(a,b)_K = 1 \iff \langle a, b, -1 \rangle$ is isotropic over $K$,
  `hilbertSymbol_eq_one_iff_isotropic`.

Mathlib v4.35.0 has no Hilbert symbol.
-/
import QuadFormsKB.Defs.Rational

namespace QuadFormsKB

open Classical in
/-- **The Hilbert symbol $(a,b)_K \in \{1,-1\}$ over the field $K$** (Serre's definition).

The field $K$ is the explicit first argument; $a, b \in K$; solutions are sought **in $K$**:
$$(a,b)_K = \begin{cases} 1 & \text{if } z^2 = a x^2 + b y^2 \text{ has a solution }
(x,y,z) \in K^3 \setminus \{0\}, \\ -1 & \text{otherwise.} \end{cases}$$

The value depends on $K$: $(-1,-1)_{\mathbb{R}} = -1$ (no nonzero real solution of
$z^2 = -x^2 - y^2$), while $(-1,-1)_{\mathbb{Q}_3} = 1$.

*Domain.* Serre defines it for $a, b \in K^\times$. If $a = 0$ or $b = 0$ this definition
returns $1$ (e.g. $a = 0$: take $(x,y,z) = (1,0,0)$). That value is a convention with no
mathematical content, and the theorems about the symbol assume $a, b \ne 0$. Its standard
properties also need $\operatorname{char} K \ne 2$.

See also: `RatPlace.hilbert` ($(a,b)_v$ for $a, b \in \mathbb{Q}$),
`hilbertSymbol_eq_one_iff_conic`, `hilbertSymbol_eq_one_iff_isotropic`,
`hilbertSymbol_real`. -/
@[kb "serre1973" "Ch. III, §1.1; omeara1963 §63B, p. 164 (Hilbert symbol); cassels1978 Ch. 3, §2, p. 41 (Hilbert norm residue symbol)"]
noncomputable def hilbertSymbol (K : Type*) [Field K] (a b : K) : ℤ :=
  if ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 then 1 else -1

/-- **The local Hilbert symbol $(a,b)_v$ of rationals $a, b \in \mathbb{Q}$ at a place $v$
of $\mathbb{Q}$.** It is the Hilbert symbol over the completion $\mathbb{Q}_v$:
$$(a,b)_v = (a,b)_{\mathbb{Q}_v}, \qquad \mathbb{Q}_\infty = \mathbb{R}, \quad
\mathbb{Q}_p = \text{the } p\text{-adic numbers},$$
with $a, b$ viewed in $\mathbb{Q}_v$. Solutions are sought **in $\mathbb{Q}_v$, not in
$\mathbb{Q}$**. This is the symbol in Hilbert's product formula $\prod_v (a,b)_v = 1$
(`hilbert_product_formula`). -/
noncomputable def RatPlace.hilbert : RatPlace → ℚ → ℚ → ℤ
  | .infinite, a, b => hilbertSymbol ℝ a b
  | .finite p, a, b => haveI : Fact p.1.Prime := ⟨p.2⟩; hilbertSymbol ℚ_[p.1] a b

/-- **The Hasse invariant over the field $K$** of the diagonal form
$\langle a_0, \dots, a_{n-1} \rangle$ with $a_i \in \mathbb{Q}$ viewed in $K$
(Serre's convention, $i < j$; 0-based indices):
$$\varepsilon_K(\langle a_0, \dots, a_{n-1} \rangle) = \prod_{0 \le i < j < n} (a_i, a_j)_K.$$
O'Meara's convention uses $i \le j$ instead. The two differ by a factor
$\prod_i (a_i, a_i)_K$. -/
@[kb "serre1973" "Ch. IV, §2.1"]
noncomputable def hasseInvariant (K : Type*) [Field K] [CharZero K] {n : ℕ} (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i < j then hilbertSymbol K (algebraMap ℚ K (a i)) (algebraMap ℚ K (a j)) else 1

/-- **Same square class over the field $K$:** the rationals $d_1, d_2$, viewed in $K$, satisfy
$d_1 = t^2 d_2$ for some $t \in K^\times$, i.e. they agree in $K^\times / (K^\times)^2$. Used to
compare discriminants over $K = \mathbb{Q}_p$ or $\mathbb{R}$. -/
def SameSquareClass (K : Type*) [Field K] [CharZero K] (d₁ d₂ : ℚ) : Prop :=
  ∃ t : K, t ≠ 0 ∧ algebraMap ℚ K d₁ = t ^ 2 * algebraMap ℚ K d₂

end QuadFormsKB
