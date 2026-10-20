# Witt's theorems over every field, including characteristic 2

Witt's extension, cancellation and decomposition theorems, and the transitivity of the orthogonal group on vectors of a given value, are proved for Mathlib's `QuadraticForm K V` over an arbitrary field $`K`$, including fields of characteristic $`2`$. In characteristic $`2`$ the hypotheses are the sharp ones from Elman–Karpenko–Merkurjev.

## Statement

Let $`K`$ be a field, $`V`$ a finite-dimensional vector space over $`K`$, and $`Q`$ a quadratic form on $`V`$ with polar form $`b(x,y) = Q(x+y) - Q(x) - Q(y)`$. Let $`\mathrm{rad}\, b`$ be the radical of $`b`$, and let the quadratic radical be $`\mathrm{rad}\, Q = \{ v \in \mathrm{rad}\, b : Q(v) = 0 \}`$. Call $`Q`$ nonsingular if $`b`$ is nondegenerate.

1. **Extension.** Assume $`\mathrm{rad}\, Q = 0`$. Let $`W \subseteq V`$ be a subspace and $`\sigma \colon W \to V`$ a linear map with $`Q(\sigma w) = Q(w)`$ and $`\sigma(w) \in \mathrm{rad}\, b \iff w \in \mathrm{rad}\, b`$ for all $`w \in W`$. Then $`\sigma`$ extends to an isometry of $`V`$.
2. **Cancellation.** If $`Q`$ is nonsingular and $`\mathrm{rad}\, Q_1 = 0`$, then $`Q \perp Q_1 \cong Q \perp Q_2`$ implies $`Q_1 \cong Q_2`$.
3. **Decomposition.** If $`\mathrm{rad}\, Q = 0`$, then $`Q \cong H^m \perp Q_{\mathrm{an}}`$ with $`H`$ the hyperbolic plane (the form $`xy`$ on $`K^2`$) and $`Q_{\mathrm{an}}`$ anisotropic. The integer $`m`$ (the Witt index) and the isometry class of $`Q_{\mathrm{an}}`$ are unique.
4. **Transitivity.** If $`Q`$ is nonsingular, the orthogonal group of $`Q`$ acts transitively on $`\{ v : Q(v) = a \}`$ for every $`a \ne 0`$. If $`\mathrm{rad}\, Q = 0`$, it acts transitively on the nonzero isotropic vectors.

## Scope and hypotheses

- Every field $`K`$; no assumption on the characteristic.
- In characteristic other than $`2`$, $`\mathrm{rad}\, Q = 0`$ and nonsingularity both mean that $`b`$ is nondegenerate, and the usual statements are recovered; corollaries are stated with Mathlib's `associated` form.
- In characteristic $`2`$, $`\mathrm{rad}\, Q = 0`$ is weaker than nonsingularity and weaker than Mathlib's `QuadraticMap.Nondegenerate`, which is covered as a special case.
- The hypotheses cannot be dropped in characteristic $`2`$. Extension fails without the radical condition on $`\sigma`$: for $`V = \langle 1\rangle \perp H`$ the map sending a generator of $`\langle 1 \rangle`$ to a vector of value $`1`$ in $`H`$ is isometric but does not extend. Cancellation fails for singular $`Q`$: over the field with two elements, $`\langle 1\rangle \perp [1,1] \cong \langle 1\rangle \perp H`$, while $`x^2 + xy + y^2`$ is anisotropic.
- Not covered: cancellation without the hypothesis on $`Q_1`$, and the Witt group.

## In Lean

All unconditional, in the namespace `QuadraticForm` (files under [QuadFormsKB/Witt/](../../QuadFormsKB/Witt/)):

- `QuadraticForm.exists_isometryEquiv_extend`: extension; variants `QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate` (nonsingular $`Q`$, injective $`\sigma`$), `QuadraticForm.exists_isometryEquiv_extend_of_associated` (characteristic not $`2`$) and `QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate'` (Mathlib's `QuadraticMap.Nondegenerate`).
- `QuadraticForm.equivalent_of_prod_equivalent_prod`: cancellation; variants `QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate` and `QuadraticForm.equivalent_of_prod_equivalent_prod_of_associated`.
- `QuadraticForm.exists_wittDecomposition`, `QuadraticForm.wittDecomposition_unique`, `QuadraticForm.eq_wittIndex`: decomposition, uniqueness, and the Witt index.
- `QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`, `QuadraticForm.exists_isometryEquiv_apply_eq_of_isotropic`, `QuadraticForm.exists_isometryEquiv_apply_eq`: transitivity.
- `QuadFormsKB.QuadForm.isometricIn_of_orthSum`, `QuadFormsKB.RatQF.isometric_of_orthSum`, `QuadFormsKB.RatQF.isometricIn_padic_of_orthSum`: cancellation for the repository's coefficient-based forms, over any field extension, over <img src="../images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> and over <img src="../images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">.

## Proof outline

The proof uses three kinds of elementary isometries, given by explicit formulas valid in every characteristic: the reflection along a vector $`z`$ with $`Q(z) \ne 0`$, the Eichler transformation attached to an isotropic vector $`z`$ and a vector orthogonal to it, and the rescaling of a hyperbolic pair. One extension step moves $`x`$ to $`y`$ while fixing a subspace: with $`z = x - y`$, reflect along $`z`$ if $`Q(z) \ne 0`$, use an Eichler transformation if $`x`$ lies outside the span of the fixed subspace, $`z`$ and $`\mathrm{rad}\, b`$, and otherwise rescale a hyperbolic pair through $`z`$. Induction on a basis of $`W`$ gives extension. Cancellation follows from extension. The decomposition splits off hyperbolic planes explicitly, and its uniqueness follows from cancellation.

## References

- R. Elman, N. Karpenko and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*, AMS Colloquium Publications 56, 2008, Thms 8.3, 8.4, 8.5 [unverified locator].
- T. Y. Lam, *Introduction to Quadratic Forms over Fields*, AMS GSM 67, 2005, Ch. I, Thm 4.2 and §4 [unverified locator].
- W. Scharlau, *Quadratic and Hermitian Forms*, Springer, 1985, Ch. 1, Thm 5.3 [unverified locator].
- O. T. O'Meara, *Introduction to Quadratic Forms*, Springer, 1963, 42:16–42:17 [unverified locator].

Bibliographic entries are in [references.bib](../../references.bib).
