# Quaternion orders, even unimodular lattices and sums of squares (new in 0.5.0)

Eight headline results from the five books added in release 0.5.0. Each is stated in
[`Challenge.lean`](../../Challenge.lean) (section names below) and proved in [`Solution.lean`](../../Solution.lean)
from the library theorem named here, with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and
no unproved input. The other central results of these books that are stated in Lean, and their status, are listed in
the [statement maps](books/README.md).

## Quaternion orders (J. Voight, *Quaternion Algebras*, 2021)

| Headline | Statement | Library theorem | Restrictions of the Lean statement |
|---|---|---|---|
| `voight_maximal_iff_discriminant` | Theorem 15.5.5: an order $`\mathcal O`$ of $`B = (a,b)_F`$ over a number field $`F`$ is maximal if and only if its reduced discriminant is the product $`\mathfrak D`$ of the finite primes at which $`B`$ ramifies | `Voight.Disc.maximalIffDiscriminant` | $`a, b`$ in the ring of integers; $`\mathcal O`$ free of rank 4 (automatic when the ring of integers is a principal ideal domain); every number field, every class number, dyadic primes included |
| `voight_evenClifford_correspondence` | Main Theorem 22.4.1 (Gross and Lucianovic): the even Clifford algebra is a bijection from similarity classes of nondegenerate ternary quadratic forms over $`R`$ onto isomorphism classes of quaternion $`R`$-orders | `Voight.evenCliffordCorrespondence_of_two_ne_zero` | $`R`$ a principal ideal domain whose fraction field has $`2 \ne 0`$ |
| `eichlerMass_totallyReal` | Main Theorem 26.1.5 and Theorem 26.1.12 (level one): $`\operatorname{mass}(\mathcal O) = 2\,\zeta_F(2)\,(2\pi)^{-2n}\,\lvert d_F\rvert^{3/2}\,h_F \prod_{\mathfrak p \mid \mathfrak D}(N\mathfrak p - 1)`$ for a maximal order of a totally definite quaternion algebra over a totally real field of degree $`n`$ | `Voight.Wave3.classMass_eq_maximal` | ring of integers a principal ideal domain; $`\mathcal O \supseteq \mathbb Z_F\langle i, j\rangle`$ with $`a, b`$ integral |
| `eichlerMass_rat` | Theorem 25.1.1: over ℚ, $`\operatorname{mass}(\mathcal O) = \varphi(D)/12`$ for a maximal order of a definite quaternion algebra of discriminant $`D`$ | `Voight.Wave3.classMass_eq_rat_maximal` | $`\mathcal O \supseteq \mathbb Z\langle i, j\rangle`$ with $`a, b`$ integers |

The two mass formulas also state that there are finitely many classes of left ideals and that every unit index is
finite, so that the mass (a sum of inverses of indices) is meaningful. Voight's theorems hold for every maximal order
and every class number; the containment of $`\mathbb Z_F\langle i, j\rangle`$ and the principal ideal domain
hypothesis come from the analytic proof formalized here (a Dirichlet series of the order and its residue).

## Even unimodular lattices (G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices*, 2019)

| Headline | Statement | Library theorems |
|---|---|---|
| `evenUnimodular_classes` | §1.1: a positive definite even unimodular lattice of dimension $`n`$ exists if and only if $`8 \mid n`$, and there are finitely many classes in each dimension | `ChenevierLannes.classSet_nonempty_iff`, `ChenevierLannes.classSet_finite` |

## Sums of squares and polygonal numbers (C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers*, 2005)

| Headline | Statement | Library theorem |
|---|---|---|
| `jacobi_fourSquares` | Theorem 2.6 (Jacobi): $`r_4(n) = 8\sigma(n)`$ for odd $`n`$ and $`24\sigma(m)`$ for even $`n`$, $`m`$ the largest odd divisor of $`n`$ | `MorenoWagstaff.theorem26` |
| `cauchy_polygonalNumbers` | Theorem 2.9 (Cauchy): for $`m \ge 3`$ every positive integer is the sum of four polygonal numbers of order $`m+2`$ and at most $`m-2`$ ones | `MorenoWagstaff.theorem29` |
| `sprague_distinctSquares` | §8.4 (Sprague, 1948): a positive integer is a sum of distinct positive squares unless it is one of 31 exceptions, the largest 128 | `MorenoWagstaff.spragueTheorem` |

*Erratum* (Moreno and Wagstaff, §8.4, p. 328): the book says there are 32 exceptions; its list, and the true list, has 31.
