# Quadratic forms over number fields in Lean 4

[![Lean build](https://github.com/jonhanke/quadratic-forms-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/quadratic-forms-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23509792.svg)](https://doi.org/10.5281/zenodo.23509792)

A Lean 4 library (built on Mathlib v4.35.0) for the arithmetic theory of quadratic forms over number fields. The Lean library is called `QuadFormsKB`.

- **Literature statements**: each result from a paper or book is a Lean declaration tagged
  `@[kb "<source key>" "<locator>"]`.
- **Definition equivalences**: competing definitions live side by side in `Defs/`, with
  their comparison (equal, strictly contained, counterexample) proved in `Equiv/`.
- **What is proved**: every theorem is checked by the Lean kernel; the only `sorry`s in the
  repository are the deliberate ones in the headline files `Challenge_<book>.lean` (one per book or topic,
  listed in [`comparator.json`](comparator.json)), which state the headline results without proofs. The CI workflow builds the library and checks that the headline theorems depend only
  on the standard axioms `propext`, `Classical.choice` and `Quot.sound`
  ([scripts/check_axioms.lean](scripts/check_axioms.lean)), and runs `lake comparator` once per book to check
  the proved statements of `Solution_<book>.lean` against `Challenge_<book>.lean`.

## Highlights

Every result listed here is checked by the Lean kernel with only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) and depends on no unproved input.

- **[Siegel's theorem for totally positive definite quadratic lattices representing numbers over totally real number fields](docs/results/siegel-totally-real.md):** for every totally positive definite quadratic lattice $`L`$ over <img src="docs/images/inline/42d5ddede335.svg" align="absmiddle" alt="\mathcal{O}_F"> of every rank $`n`$, in every genus (including genera of non-free lattices), and every totally positive $`m \in`$ <img src="docs/images/inline/42d5ddede335.svg" align="absmiddle" alt="\mathcal{O}_F">, the genus average $`\sum_{L'} r_{L'}(m)/|\mathrm{O}(L')| \big/ \sum_{L'} 1/|\mathrm{O}(L')|`$ equals the product of the local densities of $`L`$ (regularized by $`L(1,\chi)`$ when $`n = 2, 3`$; over ℚ in rank $`3`$ also in the natural order of the primes).
- **[Tamagawa number and mass formula over totally real number fields](docs/results/tamagawa-mass-formula.md):** $`\tau(\mathrm{SO}(Q)) = 2`$ and the Smith–Minkowski–Siegel mass formula (Siegel's general form, as an Euler product of local densities) for totally positive definite quadratic lattices of every rank over every totally real number field.
- **[Hilbert reciprocity over number fields](docs/results/hilbert-reciprocity.md):** $`\prod_v (a,b)_v = 1`$ for all $`a, b \in F^\times`$ and every number field $`F`$, by a purely local proof via the Weil index, independent of class field theory. (Tau Ceti proves it through class field theory and the Brauer group.)
- **[Hasse–Minkowski over number fields](docs/results/hasse-minkowski-number-fields.md):** a quadratic form over a number field is isotropic, represents $`c`$, or is isometric to another form if and only if this holds over every completion $`F_v`$. (Tau Ceti has the rank-4 and rank-≥5 induction steps, conditional on the lower ranks.)
- **[Hasse–Minkowski over ℚ](docs/results/hasse-minkowski-rationals.md)**, for forms in any number of variables.
- **[Tamagawa numbers of SO(V) over every number field](docs/results/tamagawa-table.md)** (new in 0.2.0): $`\tau(\mathrm{SO}(V)) = 2`$ for every nondegenerate quadratic space of dimension $`n \ge 3`$ over every number field (any signature, isotropic or not, complex places allowed); $`\tau = 2`$ for anisotropic and $`\tau = 1`$ for isotropic binary spaces, with Weil's convergence factors; $`\tau = 1`$ in dimension $`1`$.
- **[Siegel's formula for indefinite forms over every number field](docs/results/siegel-indefinite.md)** (new in 0.2.0): the measure form of Siegel's formula for numbers and for forms represented by forms of any signature, for every rank of the stabilizer, including Siegel's excluded case of an isotropic binary stabilizer (regularized by the residue of $`\zeta_F`$); and Siegel's formula for definite forms representing forms over totally real fields.
- **[Exact mass formulas](docs/results/mass-formulas.md)** (new in 0.4.0): the Conway–Sloane mass formula over ℤ from the genus symbols; Shimura's exact mass formula for $`\mathrm{SO}`$ over totally real number fields (Gan, Hanke and Yu), odd and even $`n`$; Hanke's exact mass formula over every number field, in a corrected general form.
- **[Classification of lattices and genera](docs/results/classification.md)** (new in 0.4.0): O'Meara 93:28 and 93:29 at the dyadic primes of number fields; Conway–Sloane's Theorem 18 on automorphous numbers at every prime; the genus of a positive definite integral lattice from its discriminant form (Conway–Sloane 1988, Lemmas 2 and 4); and (new in 0.4.1) Watson's theorem: every genus of positive definite integer-valued forms in $`n > 11`$ variables has at least two classes.
- **[Quaternion orders, even unimodular lattices and sums of squares](docs/results/quaternions-lattices-squares.md)** (new in 0.5.0): Voight's Theorem 15.5.5 (an order of a quaternion algebra over a number field is maximal exactly when its discriminant is the product of the finite ramified primes), Voight's Main Theorem 22.4.1 (the bijection between similarity classes of nondegenerate ternary quadratic forms and quaternion orders over a principal ideal domain, 2 ≠ 0), the Eichler mass formula for maximal orders over ℚ and over totally real number fields, the existence of even unimodular lattices exactly in dimensions divisible by 8 (with finitely many classes), Jacobi's four-squares formula, Cauchy's polygonal number theorem and Sprague's theorem on sums of distinct squares.
- **[The special linear group, sums of squares, lattices and reciprocity](docs/results/sln-squares-lattices-reciprocity.md)** (new in 0.5.1): $`\tau(\mathrm{SL}_n) = 1`$ over every number field (Weil), Hardy's theorem on sums of $`s`$ squares (equal to the singular series for $`5 \le s \le 8`$, with error $`O(n^{s/4})`$ for $`s > 8`$), Witt's classification of the even unimodular lattices of dimension 16 ($`E_8 \oplus E_8`$ and $`E_{16}`$), quadratic reciprocity in $`\mathbb F_q[t]`$ and the Hilbert reciprocity law over $`\mathbb F_q(t)`$ ($`q`$ odd).
- **[Classical cases over ℚ](docs/results/classical-cases.md)** (new in 0.2.0): Gauss's three-squares theorem, Jacobi's two-squares theorem and Dirichlet's theorem for $`x^2 - 2y^2`$, from Siegel's formula with explicit constants; and (new in 0.2.1) the number of representations of $`m \ne 0`$ by $`xy`$ modulo $`\pm1`$ is the number of divisors of $`|m|`$, from Siegel's formula in its excluded isotropic binary case.
- **[Siegel–Weil, theta series, Shimura's fundamental theorem and Tamagawa numbers of GL_n and Sp_2](docs/results/siegel-weil-theta-tamagawa.md)** (new in 0.6.0): the Siegel–Weil formula over ℚ in Mathlib's modular forms (the genus theta series of a positive definite form in $`n = 2k \ge 4`$ variables is the Eisenstein series of the genus, with Siegel's local densities as its Fourier coefficients); Shimura's fundamental theorem on representations (Theorem 11.6 (i) and (v)) and his mass formula (13.18), over every number field; the Siegel theta series of an even unimodular lattice is a Siegel modular form of every genus; Venkov's root sums in dimensions 8, 16 and 24; the Kneser–Hecke operators commute; the singular series of $`2k`$ squares as a divisor sum ($`k \ge 4`$ even); $`\tau(\mathrm{GL}_n) = 1`$ and $`\tau(\mathrm{Sp}_2) = 1`$ over every number field; Eichler's mass formula $`\mathrm{mass}(\mathrm{Cls}\,\mathcal O) = \varphi(D)\psi(M)/12`$ for Eichler orders of every level $`M`$ in definite quaternion algebras over ℚ (Voight, Theorem 25.3.18).


## Conditional theorems

This theorem is proved from a named input that is not yet proved here. The input is a hypothesis of the Lean statement (a named proposition, never assumed globally), so the theorem says exactly what it depends on; it is in the headline files and checked by `lake comparator` like the others.

- **Witt and Igusa: $`\vartheta_g(E_8 \oplus E_8) = \vartheta_g(E_{16})`$ for $`g \le 3`$** (Chenevier–Lannes, (1.3.2); `wittIgusa_of_cuspVanish` in [`Challenge_ChenevierLannes.lean`](Challenge_ChenevierLannes.lean)), **conditional on** the vanishing of the Siegel cusp forms of weight 8 in genus 2 and 3 (`ChenevierLannes.CuspFormsWeightEightVanish`; Igusa 1962, Tsuyumine 1986).

No conjecture is assumed anywhere in the library; conjectures appear only as stated propositions.

**Main statements.** To check what is claimed, read the headline files: each `Challenge_<book>.lean` (listed in [`comparator.json`](comparator.json)) states the results of one book or topic, with a docstring for each and a list of the library definitions the statements use; every proof there is a deliberate `sorry`. Each headline also states the finiteness and convergence facts (finite genus, finite automorphism groups, convergent products, existence of $`L_F(1,\chi)`$) that make its sums and infinite products meaningful, so that no term relies on a Lean default value (since 0.2.1 this includes the finiteness of the number of proper classes in the genus for the indefinite Siegel formulas). The matching `Solution_<book>.lean` proves the same statements by appeal to the library theorems, and `lake comparator` (configured by `comparator/<book>.json`) checks that each proved statement is exactly the one in `Challenge_<book>.lean` and uses only the standard axioms. [`formalization.yaml`](formalization.yaml) records the scope, sources, divergences from the literature, provenance and review status in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

## What's new in 0.6.1

A maintenance release: no new headlines, and the 73 headline statements of 0.6.0 are unchanged (the headline files
`Challenge_<book>.lean` are identical to those of 0.6.0, and `lake comparator` accepts every book again).

- **Duplicate instances removed**: 107 of the 118 global instances that duplicated an instance already provided by Mathlib were removed or made local, including all 12 that were not definitionally equal to Mathlib's. On the 0.6.1 tree the check finds 16 global instances that instance search also finds without them through an instance outside the library (mostly a general Mathlib instance applied to other instances of the library, such as measurability of multiplication from continuity); all 16 are definitionally equal to the instance found and none of them occurs in a headline statement. In particular the unit groups, subgroups and quotient groups of the Tamagawa measure theory (the ideles, the units of the finite adeles and of the archimedean component, $`\mathrm{GL}_n(\mathbb A)^1`$, the orthogonal group at a finite place, among others) now carry Mathlib's σ-algebras, which are proved to be their Borel σ-algebras (new file `QuadFormsKB/Tamagawa/Measure/UnitsBorel.lean`); before, the library put the Borel σ-algebra on them directly. The statement $`\tau(\mathrm{Sp}_2) = 1`$ therefore now refers to Mathlib's subspace σ-algebra; its text is unchanged.
- **Historical library, Gauss**: fifteen new files in `QuadFormsKBHistoricalGauss` on the *Disquisitiones Arithmeticae*, mostly Section V (see the list in `QuadFormsKB/Historical/Gauss.lean`): improper transformations and the opposite form (Arts. 172, 177, 213–214, 224), forms of square determinant and of determinant 0 (Arts. 212, 215), the orders of forms and their number (Arts. 226, 256 I), composition of forms (the matrix lemma of Art. 234, Arts. 235 and 238–240, the orders of a composite in Art. 245, representations under composition in Art. 244, in part), roots of representations and the forms $`(M, N, (N^2 - D)/M)`$ (Arts. 168–170, 224), ambiguous classes (Art. 165), chains of neighbouring forms (Arts. 177, 208), the number of proper transformations (Art. 214), and, in Section VII, Gauss's leading terms of the period equations (Art. 357). Statements not yet proved are named propositions, never assumed.
- **Corrected summary of Cassels, Chapter 2, (1.2)**: the [Cassels statement map](docs/results/books/cassels.md) gave the polarization formula as $`\phi(u_1,u_2) = \tfrac12\{\phi(u_1+u_2) - \phi(u_1-u_2)\}`$; Cassels has $`\tfrac14`$. Only the summary in the map was wrong; the Lean statement is unaffected.
- **Docstring of the cited input $`\tau(\mathrm{SO}(V)) = 2`$** (`QuadFormsKB/Tamagawa/MassFormula.lean`): it now says when the value is 2 (dimension $`n \ge 3`$, and $`n = 2`$ for anisotropic spaces) and when it is 1 (dimension 1 and isotropic binary spaces, where a result assuming the input is vacuous).
- The headline statements added in releases 0.2.0 to 0.6.0 are still **not yet reviewed** by a human (see Provenance).
- **Known restrictions** of the headlines, stated in their docstrings and hypotheses:
  - Voight's Theorem 15.5.5 is proved for orders that are free of rank 4 over the ring of integers (automatic when it is a principal ideal domain); the general case, with a pseudo-basis, is not yet formalized.
  - Voight's Main Theorem 22.4.1 is proved over a principal ideal domain whose fraction field has 2 ≠ 0; the book states it over a Dedekind domain.
  - The Eichler mass formulas of 0.5.0 are stated for maximal orders containing the order generated by i and j, over ℚ and over totally real number fields whose ring of integers is a principal ideal domain. The new headline for Eichler orders over ℚ (0.6.0) has no such hypothesis.
  - Sprague's theorem: the book states 32 exceptions, but its list has 31; the formalization uses the list.
  - Watson's theorem is stated for n > 11; Watson's case n = 11 is not yet formalized.
  - The two reciprocity laws over function fields are proved for the rational function field 𝔽_q(t) with q odd; Hilbert reciprocity over other global function fields and in characteristic 2 is not yet formalized.
  - The Siegel–Weil formula over ℚ is stated for an even number n ≥ 4 of variables; odd n (half-integral weight) is not yet formalized.
  - The Tamagawa measure of GL_n(𝔸_F)^1 is defined through Weil's fibration over the determinant (as for SL_n), not as a restricted product of local measures; their comparison is not yet formalized.

## What's new in 0.6.0

- **Twelve new headlines** (73 in total, the 61 headlines of 0.5.2 unchanged; see [Siegel–Weil, theta series, Shimura's fundamental theorem and Tamagawa numbers](docs/results/siegel-weil-theta-tamagawa.md)): the Siegel–Weil formula over ℚ in Mathlib's modular forms; Shimura's Theorem 11.6 (i) and (v) and the mass formula (13.18); Siegel theta series of even unimodular lattices are Siegel modular forms; Venkov's root sums in dimensions 8, 16 and 24; the Kneser–Hecke operators commute; the singular series of $`2k`$ squares; $`\tau(\mathrm{GL}_n) = 1`$ and $`\tau(\mathrm{Sp}_2) = 1`$; Eichler's mass formula for Eichler orders of every level over ℚ (Voight, Theorem 25.3.18). Eleven are unconditional; one, the identity of Witt and Igusa, is a [conditional theorem](#conditional-theorems) with its named input.
- **One headline file per book or topic**: `Challenge.lean` and `Solution.lean` are replaced by 14 pairs `Challenge_<book>.lean` and `Solution_<book>.lean` (`SiegelTotallyReal`, `TamagawaTotallyReal`, `TamagawaSO`, `TamagawaGroups`, `LocalGlobal`, `SiegelIndefinite`, `SiegelWeil`, `ClassicalCases`, `ExactMass`, `Classification`, `Voight`, `Shimura`, `ChenevierLannes`, `MorenoWagstaff`), indexed by [`comparator.json`](comparator.json), each with its own `lake comparator` configuration in `comparator/`; CI runs the comparator once per book, as a matrix of jobs. Each headline file imports only the modules its statements need, and no file imports all of Mathlib, so that every check loads far less. The theorem names are unchanged.
- **Statement maps updated**: the [statement maps](docs/results/books/README.md) of the five books added in 0.5.0 now count Voight 40 results (29 proved, 3 in part), Shimura 45 results (31 proved, 11 in part), Kitaoka 68 results (36 proved, 9 in part), Chenevier–Lannes 32 results (11 proved, 11 in part), Moreno–Wagstaff 31 results (30 proved, 0 in part).
- **New results in the library** (not headlines), each proved with only the standard axioms:
  - G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*: Theorem 10.5 (the local transitivity theorem for maximal lattices) at every finite place, the dyadic ones included, Theorem 10.3, Theorem 11.6 (ii), the one-class property of the genus of maximal lattices for the sum of $`n = 5, 7, 9`$ squares (§12.12) and with it Theorem 12.14 (iv);
  - J. Voight, *Quaternion Algebras*: Definition 23.4.1 and Propositions 23.4.2 and 23.4.19 (Eichler orders as intersections of two maximal orders, local–global); Proposition 26.6.4 (the mass of a suborder at one prime) over every totally real number field, and with it the mass formula for every maximal order over ℚ (Theorem 25.1.1) and Theorem 26.1.12 over totally real number fields whose ring of integers is a principal ideal domain;
  - G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices*: theta series with a harmonic polynomial of degree 2 are modular forms of weight $`n/2 + 2`$, Scholium 2.3.4 (rank part), the neighbour counts at $`p = 2`$;
  - Y. Kitaoka, *Arithmetic of Quadratic Forms*: Theorem 5.6.3 (I) for odd $`p`$;
  - the Siegel–Weil formula in degree one over every totally real number field for every class number (the genus theta series equals the Eisenstein series of the genus, classical and adelic forms), and the mass of every lattice over totally real fields without inputs.
- **Historical libraries**: the formalizations of historical works, each a separate Lean library not imported by `QuadFormsKB` and built by `lake build`: Gauss, *Disquisitiones Arithmeticae*, Sections IV–VII, with Arndt, Kronecker and Eisenstein (`QuadFormsKBHistoricalGauss`); Jacobi's *Fundamenta nova* (`QuadFormsKB.Historical.Jacobi`); sums of squares from Jacobi to Eisenstein and Smith (`QuadFormsKB.Historical.SumsOfSquares`); binary forms after Fermat, Gauss, Dirichlet and Smith (`QuadFormsKB.Historical.BinaryForms`); Ramanujan's papers on quadratic forms (`QuadFormsKB.Historical.Ramanujan`); Smith's papers (`QuadFormsKB.Historical.SmithPapers`); Dickson, *History of the Theory of Numbers* III and *Studies in the Theory of Numbers* (`QuadFormsKB.Historical.Dickson`, `QuadFormsKB.Historical.DicksonStudies`). Their results have no headlines; statements not yet proved are named propositions, never assumed.
- The headline statements added in releases 0.2.0 to 0.5.2 were **not yet reviewed** by a human at the time of this release (see Provenance).
- **Known restrictions** of the headlines, stated in their docstrings and hypotheses:
  - Voight's Theorem 15.5.5 is proved for orders that are free of rank 4 over the ring of integers (automatic when it is a principal ideal domain); the general case, with a pseudo-basis, is not yet formalized.
  - Voight's Main Theorem 22.4.1 is proved over a principal ideal domain whose fraction field has 2 ≠ 0; the book states it over a Dedekind domain.
  - The Eichler mass formulas of 0.5.0 are stated for maximal orders containing the order generated by i and j, over ℚ and over totally real number fields whose ring of integers is a principal ideal domain. The new headline for Eichler orders over ℚ (0.6.0) has no such hypothesis.
  - Sprague's theorem: the book states 32 exceptions, but its list has 31; the formalization uses the list.
  - Watson's theorem is stated for n > 11; Watson's case n = 11 is not yet formalized.
  - The two reciprocity laws over function fields are proved for the rational function field 𝔽_q(t) with q odd; Hilbert reciprocity over other global function fields and in characteristic 2 is not yet formalized.
  - The Siegel–Weil formula over ℚ is stated for an even number n ≥ 4 of variables; odd n (half-integral weight) is not yet formalized.
  - The Tamagawa measure of GL_n(𝔸_F)^1 is defined through Weil's fibration over the determinant (as for SL_n), not as a restricted product of local measures; their comparison is not yet formalized.

## What's new in 0.5.2

- **No new headlines**: the 61 headlines of 0.5.1 are unchanged.
- **Statement maps updated**: the [statement maps](docs/results/books/README.md) of the five books added in 0.5.0 now count Voight 40 results (24 proved, 3 in part), Shimura 44 results (25 proved, 10 in part), Kitaoka 68 results (36 proved, 8 in part), Chenevier–Lannes 32 results (6 proved, 12 in part), Moreno–Wagstaff 31 results (29 proved, 1 in part) (Kitaoka: 30 proved in 0.5.1; the new results of the other books are not yet in their maps).
- **New results in the library** (not headlines), each proved with only the standard axioms:
  - Y. Kitaoka, *Arithmetic of Quadratic Forms*: Kneser's extension theorem (Theorem 1.2.2), Theorems 5.3.4 and 5.4.1 (Eichler's extension theorem) with Corollary 5.4.1, Theorems 7.1.1, 7.1.2 and 7.5.1 (positive lattices of rank less than 43 are of E-type, from Blichfeldt's estimate of Hermite's constant), Theorem 3.3.1 (2) and (4), Theorems 3.4.2, 3.5.1 and 3.5.2, and quadratic spaces over finite fields of characteristic 2 (Chapter 1);
  - J. Voight, *Quaternion Algebras*: the Bruhat–Tits tree and Eichler orders (Section 23.5); Gorenstein, Bass and basic orders and the radical idealizer;
  - G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*: Propositions 4.3 and 4.6, Lemma 4.4, Sections 7.3 and 7.4 and Theorem 7.13;
  - G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices*: $`d`$-neighbours (Propositions 3.1.3 to 3.1.5) and the holy constructions of the Niemeier lattices;
  - the mass formula $`\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}`$ for every lattice $`L`$ (not necessarily free) on a totally positive definite quadratic space of dimension $`n \ge 3`$ over every totally real number field, without inputs.
- The headline statements added in releases 0.2.0 to 0.5.1 were **not yet reviewed** by a human at the time of this release (see Provenance).
- **Known restrictions** of the headlines, stated in their docstrings and hypotheses:
  - Voight's Theorem 15.5.5 is proved for orders that are free of rank 4 over the ring of integers (automatic when it is a principal ideal domain); the general case, with a pseudo-basis, is not yet formalized.
  - Voight's Main Theorem 22.4.1 is proved over a principal ideal domain whose fraction field has 2 ≠ 0; the book states it over a Dedekind domain.
  - The Eichler mass formulas are proved for maximal orders containing the order generated by i and j, over ℚ and over totally real number fields whose ring of integers is a principal ideal domain.
  - Sprague's theorem: the book states 32 exceptions, but its list has 31; the formalization uses the list.
  - Watson's theorem is stated for n > 11; Watson's case n = 11 is not yet formalized.
  - The two reciprocity laws over function fields are proved for the rational function field 𝔽_q(t) with q odd; Hilbert reciprocity over other global function fields and in characteristic 2 is not yet formalized.

## What's new in 0.5.1

- **Five new headlines** (61 in total, the 56 headlines of 0.5.0 unchanged; see [the special linear group, sums of squares, lattices and reciprocity](docs/results/sln-squares-lattices-reciprocity.md)): $`\tau(\mathrm{SL}_n) = 1`$ over every number field (Weil), Hardy's theorem on sums of $`s`$ squares (equal to the singular series for $`5 \le s \le 8`$, with error $`O(n^{s/4})`$ for $`s > 8`$), Witt's classification of the even unimodular lattices of dimension 16 ($`E_8 \oplus E_8`$ and $`E_{16}`$), quadratic reciprocity in $`\mathbb F_q[t]`$ and the Hilbert reciprocity law over $`\mathbb F_q(t)`$ ($`q`$ odd).
- **Statement maps extended**: the [statement maps](docs/results/books/README.md) of the five books added in 0.5.0 list the results formalized since then: Voight 40 results (24 proved, 3 in part), Shimura 44 results (25 proved, 10 in part), Kitaoka 68 results (30 proved, 9 in part), Chenevier–Lannes 32 results (6 proved, 12 in part), Moreno–Wagstaff 31 results (29 proved, 1 in part).
- The headline statements added in releases 0.2.0 to 0.5.1 were **not yet reviewed** by a human at the time of this release (see Provenance).
- **Known restrictions** of the headlines, stated in their docstrings and hypotheses:
  - Voight's Theorem 15.5.5 is proved for orders that are free of rank 4 over the ring of integers (automatic when it is a principal ideal domain); the general case, with a pseudo-basis, is not yet formalized.
  - Voight's Main Theorem 22.4.1 is proved over a principal ideal domain whose fraction field has 2 ≠ 0; the book states it over a Dedekind domain.
  - The Eichler mass formulas are proved for maximal orders containing the order generated by i and j, over ℚ and over totally real number fields whose ring of integers is a principal ideal domain.
  - Sprague's theorem: the book states 32 exceptions, but its list has 31; the formalization uses the list.
  - Watson's theorem is stated for n > 11; Watson's case n = 11 is not yet formalized.
  - The two reciprocity laws over function fields are proved for the rational function field 𝔽_q(t) with q odd; Hilbert reciprocity over other global function fields and in characteristic 2 is not yet formalized.

## What's new in 0.5.0

- **Five new books**: J. Voight, *Quaternion Algebras* (2021); G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups* (2004); Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993); G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices* (2019); and C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers* (2005). For each, a [statement map](docs/results/books/README.md) lists the central results of the book that are stated in Lean, with the Lean declarations and their status (proved, proved in part, conditional on a named input, or stated as a named proposition): Voight 31 results (18 proved, 3 in part), Shimura 34 (20 proved, 5 in part), Kitaoka 47 (23 proved, 8 in part), Chenevier–Lannes 23 (4 proved, 5 in part), Moreno–Wagstaff 28 (26 proved).
- **Eight new headlines** (56 in total, the 48 headlines of 0.4.1 unchanged; see [quaternion orders, lattices and sums of squares](docs/results/quaternions-lattices-squares.md)): Voight's Theorem 15.5.5 (an order of a quaternion algebra over a number field is maximal exactly when its discriminant is the product of the finite ramified primes), Voight's Main Theorem 22.4.1 (the bijection between similarity classes of nondegenerate ternary quadratic forms and quaternion orders over a principal ideal domain, 2 ≠ 0), the Eichler mass formula for maximal orders over ℚ and over totally real number fields, the existence of even unimodular lattices exactly in dimensions divisible by 8 (with finitely many classes), Jacobi's four-squares formula, Cauchy's polygonal number theorem and Sprague's theorem on sums of distinct squares.
- The headline statements added in releases 0.2.0 to 0.5.0 were **not yet reviewed** by a human at the time of this release (see Provenance).
- **Known restrictions** of the new headlines, stated in their docstrings and hypotheses:
  - Theorem 15.5.5 is proved for orders that are free of rank 4 over the ring of integers (automatic when it is a principal ideal domain); the general case, with a pseudo-basis, is not yet formalized.
  - Main Theorem 22.4.1 is proved over a principal ideal domain whose fraction field has 2 ≠ 0; the book states it over a Dedekind domain.
  - The Eichler mass formulas are proved for maximal orders containing the order generated by i and j, over ℚ and over totally real number fields whose ring of integers is a principal ideal domain.
  - Sprague's theorem: the book states 32 exceptions, but its list has 31; the formalization uses the list.

## What's new in 0.4.1

- **Watson's theorem** (G. L. Watson, "The class-number of a positive quadratic form", Proc. London Math. Soc. (3) 13 (1963), 549–576, Theorem 1): every genus of positive definite integer-valued forms in $`n > 11`$ variables has at least two classes. A new headline (`watson_twoClasses`; 48 in total, the 47 headlines of 0.4.0 unchanged); Cassels quotes the theorem without proof in Appendix A, and its book map now has 501 results proved and none conditional.
- The headline statements added in releases 0.2.0 to 0.4.1 were **not yet reviewed** by a human at the time of this release (see Provenance).

## What's new in 0.4.0

- **Nine new headlines** (47 in total); the 38 headlines of 0.3.0 are unchanged.
- **The Conway–Sloane mass formula over ℤ from the genus symbols** ([mass formulas](docs/results/mass-formulas.md)): the mass of a positive definite integral form in $`n \ge 3`$ variables is the standard mass times the ratios of the $`p`$-masses of its genus symbols to the standard $`p`$-masses, including $`p = 2`$, where the paper states the formula without proof (`massFormula_genusSymbols`).
- **Shimura's exact mass formula for SO**, as computed by Gan, Hanke and Yu, over every totally real number field, for odd and for even $`n`$ (`shimuraMass_odd`, `shimuraMass_even`).
- **Hanke's exact mass formula over every number field, in corrected general form** (`hankeMass_numberField`): Theorem 5.1 of the 2005 paper as printed omits Shimura's hypothesis on the determinant for odd $`n`$ and is false without it; the headline holds for every maximal lattice, with the local factors of Gan, Hanke and Yu at the primes where that hypothesis fails.
- **Conway–Sloane, Chapter 15, Theorem 18 at every prime** ([classification](docs/results/classification.md)): the $`p`$-adically automorphous numbers are the products of an even number of norms of $`p`$-adic root vectors, at $`p = 2`$ included (`automorphous_iff_rootVectors`).
- **O'Meara 93:28 and 93:29**, the classification of lattices at the dyadic primes and at the 2-adic primes of number fields, are now headlines (`dyadicClassification`, `twoAdicClassification`).
- **Conway–Sloane 1988, Lemmas 2 and 4**: two positive definite integral lattices are in the same genus if and only if they have the same type and isomorphic discriminant forms (`sameGenus_iff_discIso`, `sameGenus_iff_discIso_one`).
- **Four books complete**: Cassels, *Rational Quadratic Forms*; O'Meara, *Introduction to Quadratic Forms*; Conway–Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15; and Conway–Sloane, *Low-dimensional lattices IV: the mass formula* (1988). Item-by-item maps from each book to the Lean declarations give the status of every item ([book maps](docs/results/books/README.md)): Cassels, 500 results proved and 1 conditional on a named input (Watson's theorem, quoted without proof in Appendix A, that every genus of positive definite forms in $`n > 11`$ variables has at least two classes); O'Meara, 571 proved and none open; Conway–Sloane, Chapter 15, 115 proved; Conway–Sloane 1988, 57 proved. The remaining items are definitions, out of scope, or (two in Chapter 15) not formalized.
- **Tartakowsky's theorem for quaternary forms** (Cassels, Chapter 11, Lemma 9.2 and Theorem 1.6 for $`n = 4`$): a positive definite classically integral form in 4 variables primitively represents over ℤ every sufficiently large integer that it primitively represents over every $`\mathbb Z_p`$ (`QuadFormsKB.Cassels.Ch11L92.tartakowskyClassicalAt_four_holds`).
- **Unimodular lattices up to dimension 13** (O'Meara 106, text 7, after Kneser, stated in the book without proof): for $`1 \le n \le 13`$ the unimodular lattices on the positive definite space $`I_n`$ over ℚ are, up to isometry, $`\mathbb Z^n`$, $`E_8 \perp \mathbb Z^{n-8}`$ and $`E_{12} \perp \mathbb Z^{n-12}`$ (O'Meara's notation), proved by the mass formula (`QuadFormsKB.Lattices.omeara106_r38`).
- **O'Meara 101:8a**: over a global function field of characteristic not 2, the spinor norms of the rotations of a regular quadratic space of dimension $`n \ge 3`$ are all of $`F^\times`$ (`QuadFormsKB.OMeara.omeara101_8a`).
- The headline statements added in releases 0.2.0 to 0.4.0 were **not yet reviewed** by a human at the time of this release (see Provenance).

## What's new in 0.3.0

- **Three new headlines** (38 in total): $`\tau(\mathrm{SO}(Q)) = 2`$ and the Smith–Minkowski–Siegel mass formula for ternary totally positive definite forms over every totally real number field (`tamagawa_two_totallyReal_ternary`, `massFormula_totallyReal_ternary`; earlier releases stated them for $`n \ge 4`$), and Siegel's formula for positive definite ternary forms over ℤ with the Euler product in the natural order of the primes (`siegel_ternary_rat_natural`).
- **Ternary Siegel formula, natural order:** over ℚ in rank $`3`$ the headline reads the product in the natural order of the primes; over a totally real field $`F`$ it is the regularized form, since the natural-order reading over $`F`$ needs the prime ideal theorem for Hecke characters, which is proved in a separate library.
- **Local classification at the dyadic primes:** O'Meara's Theorem 93:28 (classification of lattices over a dyadic local field) over the completion of every number field at every dyadic prime, and Theorem 93:29 over every 2-adic completion, unconditionally.
- **The Siegel–Weil formula in degree one** over totally real number fields, for diagonal totally positive definite forms in $`n = 2m \ge 6`$ variables: the Siegel Eisenstein series at $`s_0 = m - 1`$ equals the weighted average of the theta series over the classes of the genus (unconditional when $`\mathcal{O}_F`$ has class number one, under named inputs in general), with the Eisenstein series, its Fourier expansion and the local Whittaker functions.
- **Hanke's papers:** results of *An exact mass formula for quadratic forms over number fields* (2005), of the two papers on the structure of masses of lattices of varying determinant over number fields (2011), of Gan–Hanke–Yu, *On an exact mass formula of Shimura* (2001), of Berkovich–Hanke–Jagy on the S-genus identities (2012) and of Saha–Hanke on three-term relations for theta series (2023).
- **Conway and Sloane:** results of *Sphere Packings, Lattices and Groups*, Chapters 15 and 16 (genus symbols over ℤ and the mass formula) and of *Low-dimensional lattices IV: the mass formula* (1988).
- **More of Cassels and O'Meara:** further numbered results of Cassels, *Rational Quadratic Forms*, and of O'Meara, *Introduction to Quadratic Forms*.
- The headline statements added in releases 0.2.0, 0.2.1 and 0.3.0 were **not yet reviewed** by a human at the time of this release (see Provenance).

## What's new in 0.2.1

- **Finitely many classes in the genus, every signature:** for every number field $`F`$ and every nondegenerate quadratic form over $`\mathcal{O}_F`$, of any signature, the genus contains only finitely many proper classes (`QuadFormsKB.Tamagawa.Indefinite.finite_DC`). The nine indefinite Siegel headlines now state this finiteness (`Finite (DC Q₀)`); release 0.2.0 named it in their docstrings as not stated.
- **The form $`xy`$ over ℚ:** a new headline, `divisorCount_xy`: for $`m \ne 0`$ the genus of $`\mathbb{Z}^2`$ has one proper class, and the number of representations of $`m`$ modulo $`\pm1`$ is the number of positive divisors of $`|m|`$. On the way: the unit volume $`v^1(\mathbb{Z}^2) = 1`$ and $`\prod_p (v_p(m) + 1) = d(|m|)`$.
- **One declaration for one theorem:** `QuadFormsKB.LocalDensity.NF.det_hessian_Qp` was declared in two files; it is now declared once.
- **Further library material** (no new headlines): more numbered results from Cassels, *Rational Quadratic Forms* (from Chapters 2–8, 10, 13, 14 and Appendix B) and from O'Meara, *Introduction to Quadratic Forms* (from Chapters I–X); the Weil representation of $`\mathrm{Sp}_{2g}`$ and the theta series of genus $`g`$ with its transformation law under $`\mathrm{Sp}_{2g}(\mathbb{Z})`$, and the classical consequence that the rank of an even unimodular positive definite lattice is divisible by $`8`$; for positive definite forms, the finiteness facts assumed in Hanke's Arizona Winter School notes are proved, and their four-squares formulas hold without inputs.
- The 21 headline statements added in 0.2.0, the nine of them extended here, and `divisorCount_xy` were **not yet reviewed** by a human at the time of this release (see Provenance).

## Further results

These are grouped by how they relate to existing formalizations. Each line names the topic in bold; where Mathlib or [Tau Ceti](https://github.com/TauCetiProject/TauCeti) already has a version, the line says what is added here.

**New in this library**

- **Local densities:** at every prime of every number field, dyadic primes included.
- **Class numbers:** finiteness of the class number of a genus of lattices over every number field.
- **Strong approximation:** for the spin group of an indefinite form in $`n \ge 3`$ variables over a number field.
- **Free genera:** over every number field, every lattice in the genus of <img src="docs/images/inline/203e27023b18.svg" align="absmiddle" alt="\mathcal{O}_F^n"> is free.
- **Binary quadratic forms over ℚ, in classical form:** Siegel's formula for positive definite binary quadratic forms of every discriminant, stated with Dirichlet's $`L(1,\chi_D)`$ and classes of forms. (Over every totally real number field, rank 2 is part of Siegel's theorem above, and is also stated for binary quadratic forms over the ring of integers, with the product regularized by $`L_F(1,\chi)`$.)
- **Hasse invariants over ℚ:** the conventions of Serre, Cassels, O'Meara, Lam and Shimura (Hasse's original invariant) compared, with their product formulas. O'Meara and Shimura define theirs over number fields and their completions; here they are formalized and compared only for forms over ℚ and the places of ℚ.
- **Sums of squares over ℤ:** Legendre's three-squares theorem and the Davenport–Cassels lemma.
- **Theta series:** theta inversion for totally positive definite forms over totally real number fields.

**Extending results in Mathlib or Tau Ceti**

- **Witt's theorems** (extension, cancellation, decomposition, transitivity)
  - *Here:* over every field, including characteristic $`2`$.
  - *Tau Ceti:* fields of characteristic $`\ne 2`$.
- **Jordan decompositions**
  - *Here:* over discrete valuation rings, dyadic ones included.
  - *Tau Ceti:* the Jordan splitting over the p-adic integers.
- **Kneser neighbours**
  - *Here:* Kneser's theorem over every number field: for $`n \ge 3`$ and a prime element $`\pi`$ of the ring of integers (not dividing $`2`$) at which $`V`$ is isotropic and $`L`$ is unimodular, chains of $`\pi`$-neighbours of $`L`$ reach every class in the spinor genus of $`L`$, so the whole genus when it is a single spinor genus.
  - *Tau Ceti:* over ℤ only (lattices in rational quadratic spaces): the definition of neighbours and the easier fact that they lie in the genus of $`L`$.
- **Hasse norm theorem**
  - *Here:* for quadratic extensions of number fields, without class field theory.
  - *Tau Ceti:* a reduction through class field theory.
- **Class number formula**
  - *Here:* Dirichlet's formula in the form with $`L(1,\chi_D)`$.
  - *Mathlib:* the residue of the Dedekind zeta function.

**Also proved here, available elsewhere**

- **Isotropy in dimension $`\ge 5`$**
  - *Here:* over every non-archimedean completion of a number field, dyadic completions included.
  - *Tau Ceti:* over every non-archimedean local field of characteristic $`\ne 2`$, dyadic fields included.
- **Local classification**
  - *Here:* quadratic forms over the p-adic field <img src="docs/images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p">, for every rational prime p including p = 2, are classified by dimension, discriminant and Hasse invariant (for forms with rational coefficients).
  - *Tau Ceti:* the same over every non-archimedean local field of characteristic $`\ne 2`$, dyadic fields included.
- **Class numbers over ℤ**
  - *Here:* finiteness via Hermite reduction.
  - *Tau Ceti:* reduction theory of positive definite lattices.

**Related work.** Mathlib (the foundation of this library) and [Tau Ceti](https://github.com/TauCetiProject/TauCeti/tree/main/TauCeti) overlap with parts of this library: Witt's theorems (`LinearAlgebra/QuadraticForm/Witt/`), quadratic forms over local fields (`NumberTheory/LocalField/QuadraticForm/`), global quadratic forms and Hilbert reciprocity (`NumberTheory/QuadraticForm/Global/`, `NumberTheory/ClassFieldTheory/Global/Hilbert/`) and integral lattices (`NumberTheory/IntegralLattice/`). The pages in [docs/results/](docs/results/README.md) say what each result here adds.

Precise statements and Lean names: [docs/results/further-results.md](docs/results/further-results.md).

Detailed statements, with the Lean names, proof outlines and references, are in [docs/results/](docs/results/README.md).

## Layout

```
Challenge_<book>.lean   the headline statements of one book or topic (proofs: deliberate sorry);
                        0.1.0's reviewed, later not yet
Solution_<book>.lean    the same statements, proved from the library
comparator.json         the index of the books: one `lake comparator` check per book
comparator/<book>.json  the `lake comparator` configuration of one book (Solution against Challenge)
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
QuadFormsKB/
  Citation.lean         @[kb "<key>" "<locator>"] citation attribute (keys from references.bib)
  Defs/QuadForm.lean    the primary definition: QuadForm R n = ∑_{i≤j} c_ij x_i x_j
                        (upper-triangular coefficients, any commutative ring)
  Defs/                 IntQF := QuadForm ℤ n, RatQF := QuadForm ℚ n, places of ℚ,
                        Hilbert symbol, BinQF, …
  Equiv/                theorems comparing models: QuadForm ≃ Mathlib QuadraticForm (any R),
                        polynomial ≃ Gram matrix over ℚ, integrality notions, BinQF bridge
  Literature/<Source>/  statements from a source, with their proofs
  Witt/                 Witt's theorems over any field (char 2 included): extension, cancellation,
                        decomposition, transitivity; bridge to QuadForm
  Binary/               binary forms: quadratic fields K_D, Kronecker character,
                        ζ_K = ζ·L(χ_D), Dirichlet's class number formula
  LocalDensity/         Hanke 2004 local densities: ℚ layer + DVR layer (number fields, every
                        prime)
  Lattices/             lattices over number fields: genera, class numbers, spinor norms,
                        strong approximation, Kneser neighbours
  Siegel/, Tamagawa/    Siegel's formula, the Tamagawa number τ(SO) = 2 and the mass formula
  SiegelWeil/           the Siegel–Weil formula in degree one
  Historical/           historical works (Gauss, Jacobi, Eisenstein, Smith, Ramanujan, Dickson), one
                        Lean library per work, not imported by QuadFormsKB
references.bib          bibliography; the keys used by @[kb]
docs/results/           statements, Lean names and proof outlines of the main results
scripts/check_axioms.lean  prints the axioms of the headline theorems (run in CI)
scripts/verify-comparator.sh  runs `lake comparator` for one book with the toolchain's kernels (run in CI)
```

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean   # axioms of the headline theorems
./scripts/verify-comparator.sh Voight     # Solution_Voight against Challenge_Voight (Linux; needs bubblewrap);
                                         # the books are listed in comparator.json
```

## Adding a result from the literature

1. Add a BibTeX entry to `references.bib`.
2. State the result in Lean and tag it with `@[kb "<key>" "<locator>"]` (for example
   `@[kb "omeara1963" "§82"]`). Reuse the `Defs/` vocabulary; if the source uses a new
   convention, add it as a *new* definition and prove its relation to the existing ones in
   `Equiv/`.
3. If Mathlib already has the result, the proof is just the Mathlib lemma, which makes the link
   explicit.

## Provenance

QuadFormsKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5,
with a small share by Claude Sonnet 5.5, in October and November 2026. Release 0.1.0 took about a week of development; at list
prices its model usage would have cost roughly $1,200–1,800 (it ran on a flat-rate subscription).
Up to release 0.2.0 the source repository (created on 2026-10-14) has about 3,260 commits on its main branch; at list
prices its model usage, about 35,720 requests, mostly to Claude Opus 5.5 with Claude Sonnet 5.5 subagents, would have
cost roughly $3,090 (it ran on a flat-rate subscription, the $200/month Max plan). These figures cover the whole
source repository up to 2026-10-27, including release 0.1.0 and overhead, not only the proofs.
Jonathan Hanke designed and directed it: he chose the results, the conventions and the proof routes.
The proofs are checked by the Lean kernel, and CI checks that the headline theorems use only the
standard axioms. The 13 headline statements of release 0.1.0 (now in the headline files), and the definitions they use, were
reviewed by Jonathan Hanke. The 21 headline statements added in release 0.2.0 (nine of them
extended in release 0.2.1 by the finiteness of the proper classes in the genus), the one added in release 0.2.1, the three added in release 0.3.0, the nine added in release 0.4.0, the one added in release
0.4.1, the eight added in release 0.5.0, the five added in release 0.5.1, the twelve added in release 0.6.0, and the definitions they use, have **not yet been reviewed** by a human; that review is planned for a later release. `lake comparator` checks that each `Solution_<book>.lean` proves exactly the statements of its `Challenge_<book>.lean`. The rest of the library (its other definitions and intermediate results) has not been
reviewed by a human; as with any AI-written formalization, treat it as untrustworthy until checked
against the literature. Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.23509792](https://doi.org/10.5281/zenodo.23509792) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.6.1](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.6.1)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24348425](https://doi.org/10.5281/zenodo.24348425). No new headline statements (73 in total, unchanged): global instances that duplicated Mathlib's removed (the Tamagawa measure theory now uses Mathlib's σ-algebras on unit groups and subgroups, proved to be Borel), fifteen new files of the historical Gauss library (*Disquisitiones Arithmeticae*, mostly Section V), and a corrected summary of Cassels, Chapter 2, (1.2).
- **[v0.6.0](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.6.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24296166](https://doi.org/10.5281/zenodo.24296166). Twelve new headline statements (73 in total; one of them conditional on a named input): the Siegel–Weil formula over ℚ, Shimura's fundamental theorem and mass formula (13.18), Siegel theta series of even unimodular lattices, Venkov's root sums, the commuting Kneser–Hecke operators, the singular series of 2k squares, τ(GL_n) = 1 and τ(Sp_2) = 1, Eichler's mass formula for Eichler orders over ℚ, and the identity of Witt and Igusa (conditional); one headline file and one comparator check per book or topic; the historical libraries.
- **[v0.5.2](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.5.2)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24258447](https://doi.org/10.5281/zenodo.24258447). No new headline statements (61 in total); the Kitaoka statement map updated, and new library results from Kitaoka, Voight, Shimura and Chenevier–Lannes.
- **[v0.5.1](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.5.1)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24215699](https://doi.org/10.5281/zenodo.24215699). Five new headline statements (61 in total): $`\tau(\mathrm{SL}_n) = 1`$ over every number field (Weil), Hardy's theorem on sums of $`s`$ squares (equal to the singular series for $`5 \le s \le 8`$, with error $`O(n^{s/4})`$ for $`s > 8`$), Witt's classification of the even unimodular lattices of dimension 16 ($`E_8 \oplus E_8`$ and $`E_{16}`$), quadratic reciprocity in $`\mathbb F_q[t]`$ and the Hilbert reciprocity law over $`\mathbb F_q(t)`$ ($`q`$ odd); the statement maps of the five books of 0.5.0 extended.
- **[v0.5.0](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.5.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24173254](https://doi.org/10.5281/zenodo.24173254). Five new books with statement maps (J. Voight, *Quaternion Algebras* (2021); G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups* (2004); Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993); G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices* (2019); and C. J. Moreno and S. S. Wagstaff, Jr., *Sums of Squares of Integers* (2005)) and eight new headline statements (56 in total): Voight's Theorem 15.5.5 (an order of a quaternion algebra over a number field is maximal exactly when its discriminant is the product of the finite ramified primes), Voight's Main Theorem 22.4.1 (the bijection between similarity classes of nondegenerate ternary quadratic forms and quaternion orders over a principal ideal domain, 2 ≠ 0), the Eichler mass formula for maximal orders over ℚ and over totally real number fields, the existence of even unimodular lattices exactly in dimensions divisible by 8 (with finitely many classes), Jacobi's four-squares formula, Cauchy's polygonal number theorem and Sprague's theorem on sums of distinct squares.
- **[v0.4.1](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.4.1)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24064127](https://doi.org/10.5281/zenodo.24064127). One new headline statement (48 in total): Watson's theorem (1963), every genus of positive definite integer-valued forms in $`n > 11`$ variables has at least two classes.
- **[v0.4.0](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.4.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24051456](https://doi.org/10.5281/zenodo.24051456). Nine new headline statements (47 in total): the Conway–Sloane mass formula over ℤ from the genus symbols, Shimura's exact mass formula for SO over totally real number fields (odd and even $`n`$), Hanke's exact mass formula over every number field in corrected general form, Conway–Sloane's Theorem 18 at every prime, O'Meara 93:28 and 93:29, and Lemmas 2 and 4 of Conway–Sloane 1988. The four books (Cassels; O'Meara; Conway–Sloane, Chapter 15; Conway–Sloane 1988) are complete, with item-by-item maps.
- **[v0.3.0](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.3.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.23993531](https://doi.org/10.5281/zenodo.23993531). Three new headline statements (38 in total): $`\tau(\mathrm{SO}(Q)) = 2`$ and the mass formula for ternary totally positive definite forms over totally real number fields, and Siegel's formula for positive definite ternary forms over ℤ in the natural order of the primes. The library adds O'Meara's classification of lattices at the dyadic primes of number fields, the Siegel–Weil formula in degree one over totally real fields, results of Hanke's papers on mass formulas, of Conway and Sloane on genus symbols and masses, and further results of Cassels and O'Meara.
- **[v0.2.1](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.2.1)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.23761129](https://doi.org/10.5281/zenodo.23761129). The proper classes in the genus of a nondegenerate form over the ring of integers of a number field, of any signature, are finite in number (`QuadFormsKB.Tamagawa.Indefinite.finite_DC`); the nine indefinite Siegel headlines now state this finiteness (`Finite (DC Q₀)`), which 0.2.0 named in their docstrings as not stated. For $`xy`$ over ℚ: one proper class in the genus of $`\mathbb{Z}^2`$, the unit volume $`v^1(\mathbb{Z}^2) = 1`$, $`\prod_p (v_p(m) + 1) = d(|m|)`$, and the new headline `divisorCount_xy` (the number of representations of $`m \ne 0`$ modulo $`\pm1`$ is the number of divisors of $`|m|`$; 35 headline statements in total). A theorem that was declared twice in the library (`QuadFormsKB.LocalDensity.NF.det_hessian_Qp`) is now declared once.
- **[v0.2.0](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.2.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.23693826](https://doi.org/10.5281/zenodo.23693826). Adds the Tamagawa numbers of $`\mathrm{SO}(V)`$ over every number field, Siegel's formula for indefinite forms and for forms by forms, and classical cases over ℚ (21 new headline statements in `Challenge.lean`, 34 in total). It also records an [erratum](docs/results/errata.md): an input assumed by three earlier theorems is false; those theorems are vacuous, are not headlines, and are replaced by unconditional ones.
- **[v0.1.0](https://github.com/jonhanke/quadratic-forms-lean/releases/tag/v0.1.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.23509793](https://doi.org/10.5281/zenodo.23509793).

**Not in this release** (planned for a later release; none changes a headline):

- for $`xy`$ over ℚ: the number of representations modulo the units rewritten as an explicit count of the integer pairs $`(x, y)`$ with $`xy = m`$ modulo $`\pm1`$ (the headline counts them through the library's `repCount`);
- Tamagawa numbers of the other groups of type $`D_n`$ (for example spin groups and similitude groups); only $`\mathrm{SO}(V)`$ is treated.

## License

Apache License 2.0; see [LICENSE](LICENSE).
