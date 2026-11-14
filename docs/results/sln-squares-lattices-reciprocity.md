# The special linear group, sums of squares, lattices and reciprocity (new in 0.5.1)

Five headline results added in release 0.5.1. Each is stated in [`Challenge.lean`](../../Challenge.lean) (section
names below) and proved in [`Solution.lean`](../../Solution.lean) from the library theorem named here, with only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no unproved input.

| Headline (section) | Statement | Library theorem | Restrictions of the Lean statement |
|---|---|---|---|
| `tamagawa_SLn` (`TamagawaSLn`) | A. Weil, *Adeles and Algebraic Groups* (1982), Chapter III: $`\tau(\mathrm{SL}_n) = \operatorname{vol}(\mathrm{SL}_n(F)\backslash\mathrm{SL}_n(\mathbb A_F)) = 1`$ for every number field $`F`$ and $`n \ge 1`$ | `Tamagawa.Measure.Weil.SLn.tamagawa_SLn` | none; the measure is Weil's fibration measure $`\omega_{\mathrm{SL}_n} = dy \wedge \omega_{\mathrm{SL}_{n-1}} \wedge dc`$ with self-dual additive measures |
| `hardy_sumsOfSquares` (`HardySquares`) | C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers* (2005), Theorem 6.1 (Hardy): $`r_s(n) = \rho_s(n)`$ (the singular series) for $`5 \le s \le 8`$, and $`r_s(n) = \rho_s(n) + O(n^{s/4})`$ for $`s > 8`$ | `MorenoWagstaff.theorem61` | none |
| `witt_evenUnimodular_sixteen` (`EvenUnimodularSixteen`) | G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices* (2019), Corollary 2.3.6 (Witt): the even unimodular lattices of dimension 16 are $`E_8 \oplus E_8`$ and $`E_{16}`$, with $`\lvert O(E_8 \oplus E_8)\rvert = 2 \cdot 696729600^2`$ and $`\lvert O(E_{16})\rvert = 2^{15} \cdot 16!`$ | `ChenevierLannes.wittRankSixteen`, `ChenevierLannes.card_aut_twoE8`, `ChenevierLannes.card_aut_gamma16` | none (positive definite lattices, as in the book) |
| `quadraticReciprocity_polynomial` (`RationalFunctionField`) | M. Rosen, *Number Theory in Function Fields* (2002), Theorem 3.3: $`(P'/P)(P/P') = (-1)^{\frac{q-1}{2}\deg P \deg P'}`$ for distinct monic irreducible $`P, P' \in \mathbb F_q[t]`$ | `RatFuncQR.legendreSym_mul_legendreSym'` | $`q`$ odd, as in the book |
| `hilbertReciprocity_ratFunc` (`RationalFunctionField`) | O. T. O'Meara, *Introduction to Quadratic Forms* (1963), 71:18, for $`\mathbb F_q(t)`$: $`\prod_v (a, b)_v = 1`$ over the places of $`\mathbb F_q(t)`$ | `RatFuncPlace.hilbertReciprocity` | the rational function field with $`q`$ odd; O'Meara states the law for number fields |

The proof of $`\tau(\mathrm{SL}_n) = 1`$ is by induction on $`n`$: the adelic Poisson summation formula for a
Gaussian test function, integrated over a fundamental domain, together with Siegel's mean value theorem, gives
$`(\rho - c)(\tau_n - \tau_{n-1}) = 0`$ with $`\rho > c`$. Witt's classification is proved by the mass formula:
the masses of $`E_8 \oplus E_8`$ and $`E_{16}`$ already exhaust the mass of the genus, a proof different from the
book's.
