/-
# Sums of two and five squares: the classical formulas (historical library)

**Library** `QuadFormsKB.Historical.SumsOfSquares` (a separate `lean_lib`, not imported by `QuadFormsKB`). 
Targets:

* (Dickson, *History of the Theory of Numbers* II (1920), ch. VI, p. 242,
  occurrence `dickson1920-history2:p242.1b`, and the reports of Jacobi, Dirichlet, Glaisher and others on pp. 235–252):
  for every integer $n \ge 1$,
  $$\#\{(x, y) \in \mathbb Z^2 : x^2 + y^2 = n\} = 4\bigl(d_1(n) - d_3(n)\bigr) = 4\sum_{d\mid n}\chi_{-4}(d),$$
  $d_i(n)$ the number of positive divisors of $n$ congruent to $i$ modulo $4$. `two_squares_count`: **wrapper** of
  `MorenoWagstaff.theorem25` (Moreno–Wagstaff, Theorem 2.5); `two_squares_count_chi4`: **wrapper** of
  `Tamagawa.Classical.jacobi_two_squares`.
* (H. J. S. Smith, *Mémoire sur la représentation des nombres par des sommes
  de cinq carrés* (Grand Prix 1882), *Collected Mathematical Papers* II (1894), Paper XLIV, Art. 16, pp. 672–675,
  occurrences `smith1894-papers2:p672.2`, `p673.2`, `p673.3`, `p674.1`, `p675.1`, `p675.2`, `p675.3`): the number of
  primitive representations of $M \ge 1$ as $x_1^2 + \dots + x_5^2$ is
  $$N(M) = 2^4 \cdot 5! \cdot \tfrac1{12}\,\zeta'(M)\,M^{3/2}\,\frac1{\pi^2}\sum_{m\ \mathrm{odd}\ \ge1}\Bigl(\frac Mm\Bigr)\frac1{m^2}
    = \frac{160\,\zeta'(M)\,M^{3/2}}{\pi^2}\sum_{m\ \mathrm{odd}}\Bigl(\frac Mm\Bigr)\frac1{m^2},$$
  with $\zeta'(M) = 1, \tfrac7{10}, \tfrac12, 1, \tfrac12, \tfrac12$ for $M \equiv 3 \bmod 4$, $5 \bmod 8$, $1 \bmod 8$,
  $2 \bmod 4$, $4 \bmod 8$, $0 \bmod 8$. `SmithFiveSquares`: **stated** (a named `Prop`, not proved, not assumed anywhere).

**Index convention.** Smith's variables $x_1, \dots, x_5$ are `x 0, …, x 4` here (0-based, `Fin 5`).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2ProofsB
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace QuadFormsKB.Historical.SumsOfSquares

open QuadFormsKB.Siegel

/-! ### Two squares -/

/-- $r_2(n)$ (the library's `repNum (sumSq 2) n`, over `Fin 2 → ℤ`) counts the pairs $(x, y) \in \mathbb Z^2$ with
$x^2 + y^2 = n$. -/
lemma card_pairs_eq_repNum (n : ℤ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} = repNum (sumSq 2) n := by
  unfold repNum
  refine (Nat.card_congr (Equiv.subtypeEquiv (finTwoArrowEquiv ℤ) fun x => ?_)).symm
  simp [repSet, eval_sumSq, Fin.sum_univ_two]

/-- **The number of representations by $x^2 + y^2$** (Dickson II, ch. VI, p. 242,
`dickson1920-history2:p242.1b`, "four times the excess of the number of divisors of $m$ of the form $4h+1$ over the number
of divisors of the form $4h+3$"): for every integer $n \ge 1$,
$$\#\{(x, y) \in \mathbb Z^2 : x^2 + y^2 = n\} = 4\bigl(d_1(n) - d_3(n)\bigr),\qquad
  d_i(n) = \#\{d \mid n : d > 0,\ d \equiv i \bmod 4\}.$$
**Wrapper** of `MorenoWagstaff.theorem25` (Moreno–Wagstaff, Theorem 2.5, proved in this library). -/
@[kb "dickson1920" "ch. VI, p. 242 (occurrence dickson1920-history2:p242.1b)"]
theorem two_squares_count (n : ℕ) (hn : 1 ≤ n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} : ℤ) =
      4 * (((n.divisors.filter (· % 4 = 1)).card : ℤ) - (n.divisors.filter (· % 4 = 3)).card) := by
  rw [card_pairs_eq_repNum]
  exact (MorenoWagstaff.theorem25.1 n hn).2

/-- **The same count with the character $\chi_{-4}$** ("equivalently
$4\sum_{d\mid n}\chi_{-4}(d)$"): for $n \ge 1$, $\#\{(x, y) \in \mathbb Z^2 : x^2 + y^2 = n\} = 4\sum_{d \mid n}\chi_{-4}(d)$,
$\chi_{-4}$ = Mathlib's `ZMod.χ₄`. **Wrapper** of `Tamagawa.Classical.jacobi_two_squares` (proved in this library from
Siegel's formula for binary forms). -/
@[kb "dickson1920" "ch. VI, p. 236 (Dirichlet, Werke 1, 463; occurrence dickson1920-history2:p236.2) and p. 242 (p242.1b)"]
theorem two_squares_count_chi4 (n : ℕ) (hn : 1 ≤ n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} : ℝ) =
      4 * ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) :=
  Tamagawa.Classical.jacobi_two_squares n hn

/-! ### Five squares: Smith's formula, stated -/

/-- **Primitive representations by five squares** (Smith, Paper XLIV, Art. 16, p. 672): $N(M)$ is the number of
$\vec x = (x_0, \dots, x_4) \in \mathbb Z^5$ with $x_0^2 + \dots + x_4^2 = M$ and $\gcd(x_0, \dots, x_4) = 1$ (every
common divisor is a unit). Ordered and signed, as in Smith (e.g. $N(1) = 10$, $N(3) = 80$). -/
@[kb "smith1894" "Paper XLIV, Art. 16, p. 672 (occurrence smith1894-papers2:p672.2)"]
noncomputable def primRepFive (M : ℕ) : ℕ :=
  Nat.card {x : Fin 5 → ℤ // ∑ i, x i ^ 2 = M ∧ ∀ d : ℤ, (∀ i, d ∣ x i) → IsUnit d}

/-- **Smith's factor $\zeta'(M)$** (Paper XLIV, Art. 16, cases I–VI, pp. 673–675): $\zeta' = 1$ for $M \equiv 3 \pmod 4$
(case I), $\tfrac7{10} = \tfrac15 + \tfrac12$ for $M \equiv 5 \pmod 8$ (II), $\tfrac12$ for $M \equiv 1 \pmod 8$ (III),
$1$ for $M \equiv 2 \pmod 4$ (IV), $\tfrac12$ for $M \equiv 4 \pmod 8$ (V, $\zeta' = 2\zeta$, $\zeta = \tfrac14$) and
$\tfrac12$ for $M \equiv 0 \pmod 8$ (VI, $\zeta' = 4\zeta$, $\zeta = \tfrac18$). -/
@[kb "smith1894" "Paper XLIV, Art. 16, cases I–VI, pp. 673–675 (occurrences smith1894-papers2:p673.2–p675.3)"]
noncomputable def smithZeta' (M : ℕ) : ℝ :=
  if M % 4 = 3 then 1
  else if M % 8 = 5 then 7 / 10
  else if M % 8 = 1 then 1 / 2
  else if M % 4 = 2 then 1
  else 1 / 2

/-- **Smith's series** $\sum_{m\ \mathrm{odd}\ \ge 1} \bigl(\frac Mm\bigr) m^{-2}$, $\bigl(\frac Mm\bigr)$ the Jacobi symbol
(Mathlib's `jacobiSym`), written as a sum over all $m \ge 0$ with the even terms $0$. It converges absolutely
($|(\frac Mm)| \le 1$). -/
@[kb "smith1894" "Paper XLIV, Art. 16, p. 672 (occurrence smith1894-papers2:p672.2)"]
noncomputable def smithSeries (M : ℕ) : ℝ :=
  ∑' m : ℕ, if Odd m then (jacobiSym M m : ℝ) / (m : ℝ) ^ 2 else 0

/-- **Smith's five-squares formula** (H. J. S. Smith, *Mémoire sur la représentation des
nombres par des sommes de cinq carrés*, *Collected Mathematical Papers* II (1894), Paper XLIV, Art. 16, pp. 672–675):
for every integer $M \ge 1$, the number of primitive representations of $M$ as a sum of five squares is
$$N(M) = 2^4 \cdot 5! \cdot \frac1{12}\,\zeta'(M)\,M^{3/2}\,\frac{1}{\pi^2}\sum_{m\ \mathrm{odd}}\Bigl(\frac Mm\Bigr)\frac1{m^2}
  = \frac{160\,\zeta'(M)\,M^{3/2}}{\pi^2}\sum_{m\ \mathrm{odd}}\Bigl(\frac Mm\Bigr)\frac1{m^2}.$$
(Smith prints the prefactor as $2^4 \cdot 5\,\Pi$, $\Pi\,5 = 5! = 120$.)

**Stated, not proved** (a named `Prop`; no theorem of this library assumes it). Route: Siegel's formula for the genus
of $x_0^2 + \dots + x_4^2$ (one class, `Siegel.genusClasses_sumSq`), Möbius inversion from all to primitive
representations, and the evaluation of the local densities at $2$ and at the odd primes dividing $M$ (Smith's
$\zeta$ table). Checked numerically (primitive counts against the formula, every $M \le 50$). -/
@[kb "smith1894" "Paper XLIV, Art. 16, pp. 672–675 (occurrences smith1894-papers2:p672.2, p673.2, p673.3, p674.1, p675.1–p675.3)"]
def SmithFiveSquares : Prop :=
  ∀ M : ℕ, 1 ≤ M →
    (primRepFive M : ℝ) =
      160 * smithZeta' M * (M : ℝ) ^ ((3 : ℝ) / 2) / Real.pi ^ 2 * smithSeries M

end QuadFormsKB.Historical.SumsOfSquares
