# Classification of lattices and genera

Headlines added in 0.4.0 (in [`Challenge.lean`](../../Challenge.lean), section "Classification of lattices and genera"; proved in [`Solution.lean`](../../Solution.lean) with only the standard axioms and no unproved input; not yet reviewed by a human).

| Result | Setting | Lean |
|---|---|---|
| O'Meara 93:28: lattices with Jordan splittings of the same fundamental invariants are isometric if and only if conditions (i)–(iii) on the Jordan chains hold | the completion of a number field at a dyadic prime | `QuadFormsKB.Headlines.dyadicClassification` (from `QuadFormsKB.OMeara.Step8.dyadicClassification_nf`) |
| O'Meara 93:29: the same with the Jordan invariants and conditions (i)–(ii) | the completion of a number field at a prime where $`2`$ is a prime element (for example $`\mathbb{Q}_2`$) | `QuadFormsKB.Headlines.twoAdicClassification` (from `QuadFormsKB.OMeara.G29.twoAdicClassification_twoAdic_nf`) |
| Conway–Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, Theorem 18: a $`p`$-adic unit is $`p`$-adically automorphous if and only if, up to squares, it is the product of the norms of an even number of $`p`$-adic root vectors (quoted in the book without proof) | every nondegenerate form over ℚ, every lattice, every prime $`p`$, including $`p = 2`$ | `QuadFormsKB.Headlines.automorphous_iff_rootVectors` (from `QuadFormsKB.ConwaySloane.theorem18Statement_holds`) |
| Conway–Sloane 1988, §11, Lemma 2: two positive definite integral lattices are in the same genus if and only if they have the same type $`T`$ and an isomorphism of discriminant groups preserving norms modulo $`T`$ | positive definite integral Gram matrices of the same dimension | `QuadFormsKB.Headlines.sameGenus_iff_discIso` (from `QuadFormsKB.ConwaySloane.Mass.lemma2`) |
| Conway–Sloane 1988, §11, Lemma 4: the same with norms modulo $`1`$ | the same | `QuadFormsKB.Headlines.sameGenus_iff_discIso_one` (from `QuadFormsKB.ConwaySloane.Mass.lemma4`) |

Headline added in 0.4.1 (section "Class numbers" of [`Challenge.lean`](../../Challenge.lean); proved in [`Solution.lean`](../../Solution.lean) with only the standard axioms and no unproved input; not yet reviewed by a human):

| Result | Setting | Lean |
|---|---|---|
| Watson's theorem (G. L. Watson, "The class-number of a positive quadratic form", Proc. London Math. Soc. (3) 13 (1963), 549–576, Theorem 1, the case $`n \ge 12`$ of (1.1); quoted without proof in Cassels, *Rational Quadratic Forms*, Appendix A, §3): the genus contains at least two classes, and finitely many | positive definite integer-valued forms over ℤ in $`n > 11`$ variables | `QuadFormsKB.Headlines.watson_twoClasses` (from `QuadFormsKB.Watson1963.two_le_encard_genusClasses`) |

The full statements, with every condition written out, are the docstrings of the headlines. Item-by-item maps of the books: [book maps](books/README.md).
