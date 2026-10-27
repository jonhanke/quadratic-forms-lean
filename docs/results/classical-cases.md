# Classical cases of Siegel's formula over ℚ

Classical theorems on representation numbers recovered from Siegel's formula and the Tamagawa numbers of release 0.2.0, with explicit constants.

## Statements

- **Gauss's three-squares theorem.** For squarefree $`m \ge 1`$, with $`D`$ the discriminant of $`\mathbb{Q}(\sqrt{-m})`$ ($`D = -m`$ if $`m \equiv 3 \bmod 4`$, else $`-4m`$),

  ```math
  r_3(m) = c(m)\,\frac{h(D)}{w(D)},\qquad c(m) = \begin{cases} 24 & m \equiv 1, 2 \bmod 4,\\ 48 & m \equiv 3 \bmod 8,\\ 0 & m \equiv 7 \bmod 8,\end{cases}
  ```

  $`h(D)`$ the class number and $`w(D)`$ the number of roots of unity of $`\mathbb{Q}(\sqrt{-m})`$.
- **Jacobi's two-squares theorem.** For $`m \ge 1`$, $`r_2(m) = \#\{(x, y) \in \mathbb{Z}^2 : x^2 + y^2 = m\} = 4\sum_{d \mid m}\chi_{-4}(d)`$.
- **Siegel's formula for $`x^2 + y^2`$ with explicit constants.** For a nondegenerate unary form $`T_0`$ over $`\mathbb{Z}`$ represented by $`x^2 + y^2`$ over $`\mathbb{Q}`$,
  $`\sum_i n(M_i, T_0) = \tfrac{\pi}{8}\, L(1,\chi_{-4})^{-1}\prod_p L_p(1,\chi_{-4})\,\beta_p(T_0)`$ (Siegel's Hauptsatz for $`n = 2`$, $`m = 1`$: $`c^{(1)}_\infty = 1/4`$, $`\varepsilon = \tfrac12`$, $`\sum_i v(M_i) = \pi/16`$).
- **Dirichlet's theorem for $`x^2 - 2y^2`$.** For $`m \ge 1`$, the number of representations of $`m`$ by the genus of $`x^2 - 2y^2`$ (one class), counted modulo its infinite unit group, is $`\sum_{d \mid m}\chi_8(d)`$.

## In Lean

The headline statements are in [`Challenge.lean`](../../Challenge.lean), section "Classical special cases over ℚ". Each statement with a representation number $`r_k(m)`$ also states that the set of solutions is finite; the statement for $`x^2 + y^2`$ with constants also states that $`L(1,\chi_{-4})`$ exists and is positive and that the product converges.

- `QuadFormsKB.Headlines.gauss_threeSquares` (from `QuadFormsKB.Tamagawa.Classical.gauss_three_squares`).
- `QuadFormsKB.Headlines.jacobi_twoSquares` (from `QuadFormsKB.Tamagawa.Classical.dirichlet_sumTwoSq_r2`).
- `QuadFormsKB.Headlines.siegel_twoSquares` (from `QuadFormsKB.Tamagawa.Classical.siegel_sumTwoSq_explicit`).
- `QuadFormsKB.Headlines.dirichlet_xSqMinusTwoYSq` (from `QuadFormsKB.Tamagawa.Classical.dirichlet_pell2_uncond`).

## Proof outline

Each is a specialization of Siegel's formula with the local densities computed in closed form. Three squares: the definite ternary formula over $`\mathbb{Q}`$ (regularized by $`L(1,\chi)`$), whose genus has one class; at every odd prime $`\beta_p(m)(1 - \chi(p)/p) = 1 - p^{-2}`$, and Dirichlet's class number formula $`L(1,\chi_D) = 2\pi h(D)/(w(D)\sqrt{|D|})`$ gives $`h(D)/w(D)`$. Binary forms: the [corank-one formula](siegel-indefinite.md) with a one-class genus, the unit volume computed explicitly ($`\pi/16`$ for $`x^2 + y^2`$, a multiple of $`\log(1 + \sqrt2)`$ for $`x^2 - 2y^2`$), and the regularized product of the local densities evaluated as a divisor sum; the count modulo units is the number of elements of norm $`m`$ of $`\mathbb{Z}[i]`$, resp. $`\mathbb{Z}[\sqrt2]`$, modulo the norm-one units.

## References

- C. F. Gauss, *Disquisitiones Arithmeticae*, art. 291–292 [unverified locator].
- C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) [unverified locator].

Bibliographic entries are in [references.bib](../../references.bib).
