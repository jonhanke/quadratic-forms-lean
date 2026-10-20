# QuadFormsKB

[![Lean build](https://github.com/jonhanke/quadratic-forms-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/quadratic-forms-lean/actions/workflows/build.yml)

A Lean 4 + Mathlib (v4.35.0) knowledge base for number theory / quadratic forms:

- **Literature statements**: each result from a paper or book is a Lean declaration tagged
  `@[kb "<source key>" "<locator>"]`.
- **Definition equivalences**: competing definitions live side by side in `Defs/`, with
  their comparison (equal, strictly contained, counterexample) proved in `Equiv/`.
- **What is proved**: every theorem is checked by the Lean kernel; the repository contains no
  `sorry`. The CI workflow builds the library and checks that the headline theorems depend only
  on the standard axioms `propext`, `Classical.choice` and `Quot.sound`
  ([scripts/check_axioms.lean](scripts/check_axioms.lean)), and runs `lake comparator` to check
  the proved statements against [`Challenge.lean`](Challenge.lean).

## Highlights

Every result listed here is checked by the Lean kernel with only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) and depends on no unproved input.

- **[Siegel's theorem for totally positive definite quadratic lattices representing numbers over totally real number fields](docs/results/siegel-totally-real.md):** for every totally positive definite quadratic lattice $`L`$ over <img src="docs/images/inline/42d5ddede335.svg" align="absmiddle" alt="\mathcal{O}_F"> of every rank $`n`$, in every genus (including genera of non-free lattices), and every totally positive $`m \in`$ <img src="docs/images/inline/42d5ddede335.svg" align="absmiddle" alt="\mathcal{O}_F">, the genus average $`\sum_{L'} r_{L'}(m)/|\mathrm{O}(L')| \big/ \sum_{L'} 1/|\mathrm{O}(L')|`$ equals the product of the local densities of $`L`$ (regularized by $`L(1,\chi)`$ when $`n = 2, 3`$).
- **[Tamagawa number and mass formula over totally real number fields](docs/results/tamagawa-mass-formula.md):** $`\tau(\mathrm{SO}(Q)) = 2`$ and the Smith–Minkowski–Siegel mass formula for totally positive definite quadratic lattices of every rank over every totally real number field.
- **[Hilbert reciprocity over number fields](docs/results/hilbert-reciprocity.md):** $`\prod_v (a,b)_v = 1`$ for all $`a, b \in F^\times`$ and every number field $`F`$, by a purely local proof via the Weil index, independent of class field theory. (Tau Ceti proves it through class field theory and the Brauer group.)
- **[Hasse–Minkowski over number fields](docs/results/hasse-minkowski-number-fields.md):** a quadratic form over a number field is isotropic, represents $`c`$, or is isometric to another form if and only if this holds over every completion $`F_v`$. (Tau Ceti has the rank-4 and rank-≥5 induction steps, conditional on the lower ranks.)
- **[Hasse–Minkowski over ℚ](docs/results/hasse-minkowski-rationals.md)**, for forms in any number of variables.


**Main statements.** To check what is claimed, read one file: [`Challenge.lean`](Challenge.lean) states the results above, with a docstring for each and a list of the library definitions the statements use; every proof there is a deliberate `sorry`. [`Solution.lean`](Solution.lean) proves the same statements by appeal to the library theorems, and `lake comparator` (configured by [`comparator.json`](comparator.json)) checks that each proved statement is exactly the one in `Challenge.lean` and uses only the standard axioms. [`formalization.yaml`](formalization.yaml) records the scope, sources, divergences from the literature, provenance and review status in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

## Further results

- Witt's theorems (extension, cancellation, decomposition, transitivity) over every field, including characteristic $`2`$; Tau Ceti has versions for fields in which $`2`$ is invertible. See [docs/results/witt.md](docs/results/witt.md).
- The standard Hasse invariant conventions (Serre, O'Meara, Lam, Cassels) compared, with their product formulas; local–global isometry over <img src="docs/images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}">. Also proved here: the classification over each p-adic field <img src="docs/images/inline/903326f5e2d2.svg" align="absmiddle" alt="\mathbb{Q}_p"> by dimension, discriminant and Hasse invariant (cf. Tau Ceti, over local fields in which 2 is invertible).
- Every quadratic form of dimension $`\ge 5`$ over a non-archimedean completion of a number field is isotropic, dyadic completions included (cf. Tau Ceti, over local fields in which 2 is invertible).
- Jordan decompositions of lattices over discrete valuation rings, including dyadic ones (Tau Ceti has the splitting over the p-adic integers), and local densities at every prime of every number field.
- Finiteness of class numbers of lattices over every number field (over <img src="docs/images/inline/b719c7ce5a74.svg" align="absmiddle" alt="\mathbb{Z}">, cf. the reduction theory in Tau Ceti).
- Strong approximation for the spin group of an indefinite form in $`n \ge 3`$ variables over a number field, and Kneser's neighbour method, which reaches every class of a genus that is a single spinor genus (Tau Ceti has neighbours and the same-genus lemma).
- Every lattice in the genus of <img src="docs/images/inline/203e27023b18.svg" align="absmiddle" alt="\mathcal{O}_F^n"> is free.
- The Hasse norm theorem for quadratic extensions of number fields, without class field theory.
- Dirichlet's class number formula in the form with the value $`L(1,\chi_D)`$ (Mathlib has the residue of the Dedekind zeta function), and Siegel's formula for positive definite binary forms over <img src="docs/images/inline/242caa40867f.svg" align="absmiddle" alt="\mathbb{Q}"> of every discriminant.
- Legendre's three-squares theorem and the Davenport–Cassels lemma.
- Theta inversion for totally positive definite forms over totally real number fields.


**Related work.** Mathlib (the foundation of this library) and [Tau Ceti](https://github.com/TauCetiProject/TauCeti/tree/main/TauCeti) overlap with parts of this library: Witt's theorems (`LinearAlgebra/QuadraticForm/Witt/`), quadratic forms over local fields (`NumberTheory/LocalField/QuadraticForm/`), global quadratic forms and Hilbert reciprocity (`NumberTheory/QuadraticForm/Global/`, `NumberTheory/ClassFieldTheory/Global/Hilbert/`) and integral lattices (`NumberTheory/IntegralLattice/`). The pages in [docs/results/](docs/results/README.md) say what each result here adds.

Precise statements and Lean names: [docs/results/further-results.md](docs/results/further-results.md).

Detailed statements, with the Lean names, proof outlines and references, are in [docs/results/](docs/results/README.md).

## Layout

```
Challenge.lean          the headline statements, for human review (proofs: deliberate sorry)
Solution.lean           the same statements, proved from the library
comparator.json         configuration for `lake comparator` (Solution against Challenge)
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
references.bib          bibliography; the keys used by @[kb]
docs/results/           statements, Lean names and proof outlines of the main results
scripts/check_axioms.lean  prints the axioms of the headline theorems (run in CI)
scripts/verify-comparator.sh  runs `lake comparator` with the toolchain's kernels (run in CI)
```

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean   # axioms of the headline theorems
./scripts/verify-comparator.sh            # Solution against Challenge (Linux; needs bubblewrap)
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
with a small share by Claude Sonnet 5.5, in October 2026. Development took about a week; at list
prices the model usage would have cost roughly $1,200–1,800 (it ran on a flat-rate subscription).
Jonathan Hanke designed and directed it: he chose the results, the conventions and the proof routes.
The proofs are checked by the Lean kernel, and CI checks that the headline theorems use only the
standard axioms. The headline statements are collected in `Challenge.lean` for human review; that
review is in progress. As with any AI-written formalization, the definitions and statements should
be treated as untrustworthy until checked against the literature. Human review of them has only
begun, so corrections and reports of mis-formalizations are very welcome.

## License

Apache License 2.0; see [LICENSE](LICENSE).
