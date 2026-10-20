# Hasse–Minkowski over ℚ

A nondegenerate quadratic form over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}">, in any number of variables, is isotropic over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> if and only if it is isotropic over <img src="../images/inline/0ed839b111fe.svg" align="absmiddle" alt="\mathbb{R}"> and over every p-adic field <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">. The page also covers the companion results: the local–global principle for isometry, and the classification of quadratic forms over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p"> by dimension, discriminant and Hasse invariant.

## Statement

Let $`Q`$ and $`R`$ be nondegenerate quadratic forms over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> in $`n`$ variables.

1. **Isotropy.** $`Q`$ is isotropic over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> if and only if it is isotropic over <img src="../images/inline/0ed839b111fe.svg" align="absmiddle" alt="\mathbb{R}"> and over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p"> for every prime $`p`$.
2. **Representation.** For $`c \ne 0`$ in <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}">, $`Q`$ represents $`c`$ over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> if and only if it represents $`c`$ over <img src="../images/inline/0ed839b111fe.svg" align="absmiddle" alt="\mathbb{R}"> and over every <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">.
3. **Isometry.** $`Q`$ and $`R`$ are isometric over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> if and only if they are isometric over <img src="../images/inline/0ed839b111fe.svg" align="absmiddle" alt="\mathbb{R}"> and over every <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">.
4. **Classification over ℚ<sub>p</sub>.** For nonzero rationals $`a_0, \dots, a_{n-1}`$ and $`b_0, \dots, b_{n-1}`$, the diagonal forms $`\langle a_0, \dots, a_{n-1}\rangle`$ and $`\langle b_0, \dots, b_{n-1}\rangle`$ are isometric over the p-adic field <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p"> if and only if $`\prod_i a_i`$ and $`\prod_i b_i`$ lie in the same square class of <img src="../images/inline/a61497dfe5b5.svg" align="absmiddle" alt="\mathbb{Q}_p^\times"> and their Hasse invariants agree.

Here the Hasse invariant is Serre's $`\varepsilon = \prod_{i<j} (a_i, a_j)_p`$, with $`(\cdot,\cdot)_p`$ the Hilbert symbol of <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">.

## Scope and hypotheses

- Every number of variables $`n`$. Nondegenerate means that the Hessian matrix (twice the Gram matrix) has nonzero determinant.
- Every prime $`p`$, including $`p = 2`$.
- The classification is stated for diagonal forms with rational coefficients, compared over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">; every nondegenerate form over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> is isometric over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> to such a form.
- The other conventions for the Hasse invariant in the literature (O'Meara's $`\prod_{i \le j}`$, Cassels, Lam, Shimura) are defined separately, converted into each other exactly, and each is shown to be an isometry invariant satisfying the product formula over all places of <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}">.

## In Lean

All unconditional:

- `QuadFormsKB.hasseMinkowski`: isotropy.
- `QuadFormsKB.represents_iff_everywhere`: representation.
- `QuadFormsKB.isometric_iff_everywhere`: isometry.
- `QuadFormsKB.isometric_padic_iff`: classification over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p"> (proved as `QuadFormsKB.isometric_padic_iff_invariants`); `QuadFormsKB.hasseInvariant_isometric`: invariance of the Hasse invariant.
- `QuadFormsKB.isSquare_iff_everywhere`, `QuadFormsKB.hilbert_product_formula`, `QuadFormsKB.isotropic_padic_of_five_le`: the local–global principle for squares, Hilbert reciprocity over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}">, and isotropy of forms in at least $`5`$ variables over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">.
- `QuadFormsKB.hasseOMeara_eq`, `QuadFormsKB.RatPlace.hasseOMeara_isometric`, `QuadFormsKB.hasseSerre_product_formula`, `QuadFormsKB.hasseOMeara_product_formula` (and the analogues for Cassels, Lam and Shimura): the Hasse invariant conventions.
- `QuadFormsKB.hasseMinkowski_nf_rat`: the case $`F`$ = <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> of [Hasse–Minkowski over number fields](hasse-minkowski-number-fields.md), through the identification of the places of <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}">.

## Proof outline

The proof follows Serre's *A Course in Arithmetic*, Ch. IV. The local theory gives the squares of <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">, explicit formulas for the Hilbert symbol at odd $`p`$ and at $`p = 2`$, bimultiplicativity, and the product formula. Rank $`2`$ is the local–global principle for squares, and rank $`3`$ is Legendre's theorem. Rank $`4`$ uses a common value of two binary forms chosen with prescribed Hilbert symbols, which needs Dirichlet's theorem on primes in progressions. Rank $`n \ge 5`$ uses isotropy over every <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p"> and induction. Representation follows from isotropy of $`Q \perp \langle -c\rangle`$, and isometry from representation and Witt cancellation over <img src="../images/inline/0ed839b111fe.svg" align="absmiddle" alt="\mathbb{R}"> and <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">. In the classification over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">, invariance of $`\varepsilon`$ is proved by induction with Witt cancellation instead of Witt's chain-equivalence theorem. The converse uses the local representation criterion (Serre IV, §2.2, Thm 6).

## References

- J.-P. Serre, *A Course in Arithmetic*, Springer GTM 7, 1973: Ch. IV, §3.2, Thm 8 (Hasse–Minkowski) and Cor. 1; §3.3, Thm 9 (isometry); §2.3, Thm 7 (classification over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">); §2.2, Thm 6; Ch. III, §2.1, Thm 3 (product formula).
- J. W. S. Cassels, *Rational Quadratic Forms*, Academic Press, 1978 [unverified locator].
- O. T. O'Meara, *Introduction to Quadratic Forms*, Springer, 1963 [unverified locator].
- G. Shimura, *Arithmetic of Quadratic Forms*, Springer, 2010, §28.13 [unverified locator].

Bibliographic entries are in [references.bib](../../references.bib). See also [Witt's theorems](witt.md).
