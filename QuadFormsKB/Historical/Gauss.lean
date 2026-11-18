import QuadFormsKB.Historical.Gauss.Forms
import QuadFormsKB.Historical.Gauss.Transformations
import QuadFormsKB.Historical.Gauss.Reduction
import QuadFormsKB.Historical.Gauss.Composition
import QuadFormsKB.Historical.Gauss.Duplication
import QuadFormsKB.Historical.Gauss.Genera
import QuadFormsKB.Historical.Gauss.EisensteinTernary
import QuadFormsKB.Historical.Gauss.CompositionInvariance
import QuadFormsKB.Historical.Gauss.Products
import QuadFormsKB.Historical.Gauss.Determinants
import QuadFormsKB.Historical.Gauss.ResidueForms
import QuadFormsKB.Historical.Gauss.ReductionNegative
import QuadFormsKB.Historical.Gauss.GeneraCount
import QuadFormsKB.Historical.Gauss.EisensteinExamples
import QuadFormsKB.Historical.Gauss.GenusGroup
import QuadFormsKB.Historical.Gauss.DuplicationSubstitution
import QuadFormsKB.Historical.Gauss.TernaryRepresentations
import QuadFormsKB.Historical.Gauss.Example161
import QuadFormsKB.Historical.Gauss.ReductionIndefinite
import QuadFormsKB.Historical.Gauss.AmbiguousForms
import QuadFormsKB.Historical.Gauss.CharacteristicNumbers
import QuadFormsKB.Historical.Gauss.CompositionTransitivity
import QuadFormsKB.Historical.Gauss.Art256
import QuadFormsKB.Historical.Gauss.Periods
import QuadFormsKB.Historical.Gauss.SectionSix
import QuadFormsKB.Historical.Gauss.Art331Example
import QuadFormsKB.Historical.Gauss.Example161Genus
import QuadFormsKB.Historical.Gauss.IdonealPositive
import QuadFormsKB.Historical.Gauss.Art307Presentation
import QuadFormsKB.Historical.Gauss.SquareDeterminant
import QuadFormsKB.Historical.Gauss.PeriodsDistinct
import QuadFormsKB.Historical.Gauss.Representations
import QuadFormsKB.Historical.Gauss.CompleteCharacter
import QuadFormsKB.Historical.Gauss.CompositionDeterminants
import QuadFormsKB.Historical.Gauss.Nonresidues
import QuadFormsKB.Historical.Gauss.PeriodsQuadratic
import QuadFormsKB.Historical.Gauss.Opposite
import QuadFormsKB.Historical.Gauss.SquareDegenerate
import QuadFormsKB.Historical.Gauss.Orders
import QuadFormsKB.Historical.Gauss.CompositionOrders
import QuadFormsKB.Historical.Gauss.PeriodsQuadraticLeading
import QuadFormsKB.Historical.Gauss.TransformationsFinite
import QuadFormsKB.Historical.Gauss.CompositionEquations
import QuadFormsKB.Historical.Gauss.MatrixLemma
import QuadFormsKB.Historical.Gauss.CompositionGcd
import QuadFormsKB.Historical.Gauss.RootForms
import QuadFormsKB.Historical.Gauss.NeighbourChains
import QuadFormsKB.Historical.Gauss.TransformationsInfinite
import QuadFormsKB.Historical.Gauss.OrdersComplements
import QuadFormsKB.Historical.Gauss.AmbiguousClasses
import QuadFormsKB.Historical.Gauss.CompositionRepresentations

/-!
# Historical library: Gauss, *Disquisitiones Arithmeticae*, Section V, and its successors

A separate `lean_lib` (`QuadFormsKBHistoricalGauss`) of statements in the sources' own terms, each tagged with its result id in the historical sources (R-...):

* `Forms`: Gauss's $(a, b, c) = a x^2 + 2bxy + cy^2$, determinant $b^2 - ac$, and the dictionary to the library's
  `BinQF`.
* `Transformations`: Art. 214, all proper transformations of a form into a contained one.
* `Reduction`: Arts. 171, 172, 223 (Rule I), reduced forms of negative determinant.
* `Composition`: Arts. 235-236, 249, Gauss's composition and the class group.
* `Duplication`: Arndt's principal genus theorem and Gauss's Art. 287.
* `Genera`: Kronecker's genus character identity and Gauss's count of genera.
* `EisensteinTernary`: Eisenstein's tables for the automorphisms of reduced ternary forms.
* `CompositionInvariance`: Art. 238, composition is invariant under proper equivalence, and Art. 236
  for the given primitive forms themselves.
* `Products`: Art. 244, a composite represents the products, with signs.
* `Determinants`: Arts. 171, 215, 226.
* `ResidueForms`: Art. 233 I, VI, VIII, forms that are quadratic residues (,
  ).
* `ReductionNegative`: Art. 223 for negative forms; the positive nonsquare case stated.
* `EisensteinExamples`: Eisenstein's table rows proved on his eight worked examples.
* `GeneraCount`: Arts. 261-262, half of the assignable characters.
* `GenusGroup`: genera as cosets of the principal genus; Art. 303, idoneal numbers; Art. 307 III-IV; Art. 287 end, in local form; Art. 307 VII stated.
* `DuplicationSubstitution`: Arts. 286-287 I, the duplication substitution; Art. 236
  for non-primitive forms; Art. 259, ambiguous classes of derived orders.
* `TernaryRepresentations`: Art. 290, equivalent binary forms are represented equally often;
  Art. 297, the ternary proof of reciprocity case V.
* `Example161`: Art. 260, the principal genus and duplicates for determinant $-161$.
* `ReductionIndefinite`: Arts. 183, 223, every form of positive nonsquare determinant is equivalent to a reduced
  form.
* `AmbiguousForms`: Art. 257 I-II, the number of properly primitive forms $(A, 0, C)$ and $(2B, B, C)$ of a given
  determinant.
* `CharacteristicNumbers`: Art. 233 II-III, the particular characters of a form and its characteristic numbers.
* `CompositionTransitivity`: Art. 235, $d = D n^2$ and $d' = D n'^2$ (hence Art. 287 I without assuming $n = n'$);
  Arts. 237-238, transport of a transformation into a product.
* `Art256`: Arts. 256 VI, 259 II, for $D \equiv 5 \pmod 8$ the classes of $(4, 1, (1-D)/4)$ and
  $(4, 3, (9-D)/4)$ are mutually inverse of order dividing $3$.
* `Periods`: Section VII, Arts. 342-351, Gaussian periods: dependence on the coset, partition, products, the tower
  of period equations.
* `SectionSix`: Section VI, Art. 155/327 (the value $v$ of a representation), Arts. 331-333
  (residues and factoring, the number of square roots of $-D$ modulo $M$,
  ).
* `Art331Example`: Art. 331, Gauss's exclusion example for $M = 997331$: $127$ is the only prime below $998$ left by
  the residues $-6, 13, -14, 17, 37, -53$.
* `Example161Genus`: Art. 260, the principal genus of determinant $-161$ consists of exactly four classes.
* `IdonealPositive`: Art. 303 for positive forms, as Gauss states it.
* `Art307Presentation`: Art. 307 VII, the class group of a regular determinant is $E^k \prod_{i \in I} A_i$
  (proves `Art307RegularPresentation`).
* `SquareDeterminant`: Arts. 206-207, 223 for square determinant $h^2$, the representatives $(A, h, 0)$,
  $0 \le A < 2h$, and their uniqueness; Art. 215 III, representations by $m(gx + hy)^2$.
* `PeriodsDistinct`: Art. 346, the periods of distinct cosets are distinct (first claim).
* `Representations`: Arts. 154-155, the value of a proper representation is one class modulo $M$;
  Art. 154, reduction to primitive representations; Art. 166, substitutions of determinant $\pm 1$
  preserve the greatest common divisor; Art. 179, $4D/m^2 \equiv 0, 3 \pmod 4$ and $\ge 3$.
* `CompleteCharacter`: Art. 233 IV, V, VII, the complete character of a residue form and the number of values of
  $\sqrt{M(a, b, c)}$.
* `CompositionDeterminants`: Art. 235, $\Delta = D n n'$, $\Delta^2 = d d'$, the sign of $\Delta$, and the greatest
  common divisor of the six numbers.
* `Nonresidues`: Art. 125, every integer that is not a square is a nonresidue of some odd prime.
* `PeriodsQuadratic`: Art. 357, $4\Phi_p = Y^2 - p^* Z^2$ with $Y, Z$ integer polynomials.
* `Opposite`: Arts. 213-214, improper transformations as proper ones into the opposite form; Art. 177; Art. 172 for improper equivalence of reduced forms; Art. 224, equivalent forms
  have the same primitive representations and the same values (partial).
* `SquareDegenerate`: Art. 212, representations by a form of square determinant via its factorization; Art. 215 I-II, forms of determinant $0$.
* `Orders`: Art. 226, the orders and their number $(\mu+1)(\alpha+1)\cdots$ resp. $(\mu+2)(\alpha+1)\cdots$; Art. 256 I, admissibility of the simplest form.
* `CompositionOrders`: Art. 245, the determinant of a composite and properly primitive composites; the full order
  statement stated.
* `PeriodsQuadraticLeading`: Art. 357 with Gauss's leading terms $Y = 2X^m + X^{m-1} + \dots$,
  $Z = X^{m-1} + \dots$.
* `TransformationsFinite`: Art. 214, finitely many proper transformations for $D < 0$ and for $D$ a nonzero square;
  infinitely many in examples with $D = 0$ and $D = 2$.
* `CompositionEquations`: Art. 235, the nine coefficient equations, the identities $\Omega$ and their converse.
* `MatrixLemma`: Art. 234, the matrix lemma; Art. 238 (combined substitution); Art. 239, a composite contains every
  other composite of the same forms.
* `CompositionGcd`: Art. 235 divisibilities; Art. 245, $\gcd(A, 2B, C) = m m'$ and the order statements; Art. 240
  step I.
* `RootForms`: Arts. 168-169, roots of representations and the forms $(M, N, (N^2 - D)/M)$; Art. 170 (ambiguous
  forms); Art. 224 and its converse.
* `AmbiguousClasses`: Art. 165, the ambiguous clause used in Art. 170.
* `NeighbourChains`: Art. 177, chains of neighbouring forms; Art. 208.
* `TransformationsInfinite`: Art. 214, infinitely many proper transformations for positive nonsquare $D$.
* `OrdersComplements`: Art. 226 count with the decomposition derived from $D$; Art. 256 I in general.
* `CompositionRepresentations`: Art. 244, representations multiply under composition and, for
  $\gcd(a, a', b + b') = 1$, primitive representations with roots $b$, $b'$ give one with root $B$; general $\mu$ stated (`Art244GeneralModulus`).
-/
