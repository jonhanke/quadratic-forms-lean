# Hasse–Minkowski over number fields

A nondegenerate quadratic form over a number field $`F`$ is isotropic over $`F`$ if and only if it is isotropic over every completion $`F_v`$. The same local–global principle holds for representing a nonzero number and for isometry of two forms. All three are proved for every number field and every number of variables.

## Statement

Let $`F`$ be a number field and let $`Q`$, $`R`$ be nondegenerate quadratic forms over $`F`$ in $`n`$ variables. Let $`v`$ run over all places of $`F`$, finite and infinite, and let $`F_v`$ be the completion.

1. **Isotropy.** $`Q`$ is isotropic over $`F`$ if and only if $`Q`$ is isotropic over $`F_v`$ for every $`v`$.
2. **Representation.** For $`c \in F^\times`$, $`Q`$ represents $`c`$ over $`F`$ if and only if $`Q`$ represents $`c`$ over $`F_v`$ for every $`v`$.
3. **Isometry.** $`Q`$ and $`R`$ are isometric over $`F`$ if and only if they are isometric over $`F_v`$ for every $`v`$.

## Scope and hypotheses

- Every number field $`F`$, with no hypothesis on degree, signature or class number.
- Every number of variables $`n`$. Nondegenerate means that the Hessian matrix of $`Q`$ (twice the Gram matrix) has nonzero determinant.
- The forms are the repository's quadratic forms $`\sum_{i \le j} c_{ij} x_i x_j`$ with coefficients in $`F`$, and $`F_v`$ is the real or complex completion at an infinite place or the completion at a nonzero prime of <img src="../images/inline/42d5ddede335.svg" align="absmiddle" alt="\mathcal{O}_F">.

## In Lean

All unconditional:

- `QuadFormsKB.hasseMinkowski_nf`: isotropy (Lam's route).
- `QuadFormsKB.hasseMinkowski_nf_serre`: isotropy again, by Serre's route over $`F`$; an independent second proof.
- `QuadFormsKB.represents_iff_everywhere_nf`: representation of $`c \ne 0`$.
- `QuadFormsKB.isometricIn_iff_everywhere_nf`: isometry, both directions; the local-to-global direction is `QuadFormsKB.Tamagawa.FormClassNF.isometricIn_of_everywhere_nf`, the converse is base change of an isometry (`QuadFormsKB.QuadForm.isometricIn_baseChange`, over any field with $`2 \ne 0`$).
- Ingredients: `QuadFormsKB.SqLG.isSquare_iff_everywhere` (an element of $`F`$ that is a square in every completion is a square), `QuadFormsKB.HasseNorm.hilbert_eq_one_of_everywhere` (the Hasse norm theorem for quadratic extensions), `QuadFormsKB.hilbert_reciprocity_nf` and `QuadFormsKB.PresNF.exists_prescribed_hilbert` (elements with prescribed local Hilbert symbols).

## Proof outline

Diagonalize $`Q`$. In rank $`2`$, $`\langle a, b\rangle`$ is isotropic if and only if $`-ab`$ is a square, so the local–global principle for squares applies. In rank $`3`$, when $`-ab`$ is not a square, $`\langle a, b, c\rangle`$ is isotropic if and only if $`-c/a`$ is a norm from $`F(\sqrt{-ab})`$, and the Hasse norm theorem for quadratic extensions applies; it is proved with Chevalley's algebraic second inequality and no imported class field theory. Lam's route then handles rank $`4`$ by passing to the discriminant extension and rank $`n \ge 5`$ by induction, splitting off a binary form whose global value is chosen by weak approximation. Serre's route over $`F`$ replaces Dirichlet's theorem on primes in progressions by the existence of elements with prescribed local Hilbert symbols, which is proved from Hilbert reciprocity and a duality argument on $`S`$-units. Representation follows from isotropy of $`Q \perp \langle -c\rangle`$. Isometry follows by induction on $`n`$: a value of $`R`$ is represented by $`Q`$ everywhere, hence over $`F`$, and Witt cancellation at every place removes it.

## Related work

Tau Ceti has the induction steps of Hasse–Minkowski over number fields in rank 4 and in rank at least 5 ([`NumberTheory/QuadraticForm/Global/`](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/NumberTheory/QuadraticForm/Global)), conditional on the lower-rank cases. Here the theorem is proved completely, in every rank, for isotropy, representation and isometry.

## References

- O. T. O'Meara, *Introduction to Quadratic Forms*, Springer, 1963, 66:1, 66:3, 66:4 (Hasse–Minkowski), §65 (Hasse norm theorem), 71:19 (prescribed symbols) [unverified locator].
- T. Y. Lam, *Introduction to Quadratic Forms over Fields*, AMS GSM 67, 2005, Ch. VI, Thm 3.1 [unverified locator].
- J.-P. Serre, *A Course in Arithmetic*, Springer GTM 7, 1973, Ch. IV, §3 (the proof over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> that Serre's route follows).
- J. S. Milne, *Class Field Theory*, lecture notes, Ch. VII [unverified locator].

Bibliographic entries are in [references.bib](../../references.bib). See also [Hasse–Minkowski over ℚ](hasse-minkowski-rationals.md), [Hilbert reciprocity](hilbert-reciprocity.md) and [Witt's theorems](witt.md).
