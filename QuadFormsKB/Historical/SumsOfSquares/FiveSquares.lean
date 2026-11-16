/-
# Eisenstein's five-squares formulas (1847) as finite character sums

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`).  Targets
(Eisenstein, *Note sur la représentation d'un nombre par la
somme de cinq carrés*, J. reine angew. Math. 35 (1847), 368, work `eisenstein1847-cinq-carres`). For odd squarefree
$m$, with $\bigl(\frac\mu m\bigr)$ the Jacobi symbol and $r_s(m) = \#\{\vec x \in \mathbb Z^s : \sum x_i^2 = m\}$:

* ($m \equiv 1 \bmod 8$, $m \ne 1$): $r_5(m) = -80\sum_{\mu=1}^{(m-1)/2}\bigl(\frac\mu m\bigr)\mu$;
* ($m \equiv 3 \bmod 8$): $r_5(m) = -80\sum_{\mu=1}^{(m-1)/2}(-1)^\mu\bigl(\frac\mu m\bigr)\mu
  = 320\sum_{\mu=1}^{(m-3)/4}\bigl(\frac\mu m\bigr)\mu + \tfrac{10}3\,m\,r_3(m)$;
* ($m \equiv 5 \bmod 8$): $r_5(m) = -112\sum_{\mu=1}^{(m-1)/2}\bigl(\frac\mu m\bigr)\mu$;
* ($m \equiv 7 \bmod 8$): $r_5(m) = 80\sum_{\mu=1}^{(m-1)/2}(-1)^\mu\bigl(\frac\mu m\bigr)\mu
  = 320\sum_{\mu=1}^{(m-3)/4}\bigl(\frac\mu m\bigr)\mu$.

`EisensteinFiveSquares1`, `…3`, `…5`, `…7` (one `Prop` per row; the $m \equiv 3$ case multiplied by $3$ to stay in
$\mathbb Z$), all **stated**. Each was checked numerically for every odd squarefree $m < 300$
(no discrepancy, so no erratum).

*Why out of reach here:* the Euler-product form $r_5(m) = c_5(m)\pi^{-2}m^{3/2}\sum_{\mu\ \mathrm{odd}}
\bigl(\frac m\mu\bigr)\mu^{-2}$ is **proved** for squarefree $m$ (`five_squares_squarefree`, `OddSquares.lean`); the
missing step is Dirichlet's evaluation of $L(2, \chi)$ for an even quadratic character $\chi$ as a finite sum
$\sum\chi(\mu)\mu$ over a half or quarter interval (Gauss sums and the functional equation, or generalized Bernoulli
numbers $B_{2,\chi}$), which is in neither Mathlib nor this library (loose end, as for the seven-squares formulas
`EisensteinSevenSquares`).
-/
import QuadFormsKB.Historical.SumsOfSquares.Eisenstein

namespace QuadFormsKB.Historical.SumsOfSquares

/-- $\sum_{\mu = 1}^{b}(-1)^\mu\bigl(\frac\mu m\bigr)\mu$ (Jacobi symbol), an integer. -/
def altJacobiSum (m b : ℕ) : ℤ := ∑ μ ∈ Finset.Icc 1 b, (-1) ^ μ * jacobiSym μ m * (μ : ℤ)

/-- **Eisenstein's five squares, $m \equiv 1 \pmod 8$**: for odd squarefree
$m \equiv 1 \pmod 8$, $m \ne 1$, $r_5(m) = -80\sum_{\mu=1}^{(m-1)/2}\bigl(\frac\mu m\bigr)\mu$. **Stated.** -/
@[kb "eisenstein1847cinq" "p. 368 (occurrence eisenstein1847-cinq-carres:p368.4) [unverified locator]"]
def EisensteinFiveSquares1 : Prop :=
  ∀ m : ℕ, 1 < m → Squarefree m → m % 8 = 1 →
    (sqRep 5 m : ℤ) = -80 * jacobiPowerSum m 1 ((m - 1) / 2) 1

/-- **Eisenstein's five squares, $m \equiv 3 \pmod 8$**: for squarefree
$m \equiv 3 \pmod 8$, $r_5(m) = -80\sum_{\mu=1}^{(m-1)/2}(-1)^\mu\bigl(\frac\mu m\bigr)\mu$ and
$3r_5(m) = 960\sum_{\mu=1}^{(m-3)/4}\bigl(\frac\mu m\bigr)\mu + 10\,m\,r_3(m)$. **Stated.** -/
@[kb "eisenstein1847cinq" "p. 368 (occurrence eisenstein1847-cinq-carres:p368.5) [unverified locator]"]
def EisensteinFiveSquares3 : Prop :=
  ∀ m : ℕ, Squarefree m → m % 8 = 3 →
    (sqRep 5 m : ℤ) = -80 * altJacobiSum m ((m - 1) / 2) ∧
      3 * (sqRep 5 m : ℤ) = 960 * jacobiPowerSum m 1 ((m - 3) / 4) 1 + 10 * m * sqRep 3 m

/-- **Eisenstein's five squares, $m \equiv 5 \pmod 8$**: for squarefree
$m \equiv 5 \pmod 8$, $r_5(m) = -112\sum_{\mu=1}^{(m-1)/2}\bigl(\frac\mu m\bigr)\mu$. **Stated.** -/
@[kb "eisenstein1847cinq" "p. 368 (occurrence eisenstein1847-cinq-carres:p368.6) [unverified locator]"]
def EisensteinFiveSquares5 : Prop :=
  ∀ m : ℕ, Squarefree m → m % 8 = 5 →
    (sqRep 5 m : ℤ) = -112 * jacobiPowerSum m 1 ((m - 1) / 2) 1

/-- **Eisenstein's five squares, $m \equiv 7 \pmod 8$**: for squarefree
$m \equiv 7 \pmod 8$, $r_5(m) = 80\sum_{\mu=1}^{(m-1)/2}(-1)^\mu\bigl(\frac\mu m\bigr)\mu
= 320\sum_{\mu=1}^{(m-3)/4}\bigl(\frac\mu m\bigr)\mu$. **Stated.** -/
@[kb "eisenstein1847cinq" "p. 368 (occurrence eisenstein1847-cinq-carres:p368.7) [unverified locator]"]
def EisensteinFiveSquares7 : Prop :=
  ∀ m : ℕ, Squarefree m → m % 8 = 7 →
    (sqRep 5 m : ℤ) = 80 * altJacobiSum m ((m - 1) / 2) ∧
      (sqRep 5 m : ℤ) = 320 * jacobiPowerSum m 1 ((m - 3) / 4) 1

end QuadFormsKB.Historical.SumsOfSquares
