# J. Voight, *Quaternion Algebras*: statement map

Graduate Texts in Mathematics 288, Springer, 2021 (open access). Items are numbered as in the book: `Theorem 15.5.5` is Theorem 5.5 of Chapter 15.

This is a statement map: it lists the central results of the book that are stated in the Lean library, with the Lean declarations and their status. It is not a complete map of the book; results that are not listed are not formalized here. *Proved* means proved in Lean with only the standard axioms and no unproved input (the declaration's whole dependency closure); *conditional* names the unproved inputs it still assumes; *stated* means that the result is stated as a named proposition (a Lean `def` or `structure` of type `Prop`) and not proved. When several declarations are listed, the status is that of the best one, and the last column says how the Lean statements differ from the book (restrictions or generalizations); *proved in part* means that the proved declarations cover only part of the result (a special case or some of its clauses), as the last column says. The statements are short descriptions in our own words, not quotations; read the book for the exact wording.

Rows: 31. proved: 18; proved in part: 3; conditional: 1; stated: 9.

## 5. Quaternion algebras and quadratic forms

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 5.1.1 and Corollary 5.2.6 | Two quaternion algebras with nonzero parameters over a field are isomorphic as algebras if and only if their trace-zero (pure) quadratic forms are similar. | `Voight.PureForm.nonempty_algEquiv_iff_similar`, `Voight.PureForm.nonempty_algEquiv_iff_isometricIn` | proved | fields in which $2 \neq 0$; algebras presented as $(a, b)$ with $a, b \neq 0$ |
| Main Theorem 5.4.4 | A quaternion algebra $(a,b)$ is a division algebra exactly when the Hilbert symbol $(a,b)$ equals $-1$, and it is isomorphic to the algebra of $2 \times 2$ matrices exactly when the symbol equals $1$. | `Quat.hilbertSymbol_eq_neg_one_iff_division`, `Quat.nonempty_algEquiv_matrix_iff`, `Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero` | proved in part (see the last column) | only the equivalences between being a division algebra, being split, the Hilbert symbol and the existence of a norm-zero element are covered; fields in which $2 \neq 0$ |

## 9. Lattices and integral quadratic forms

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Lemma 9.4.6 and Corollary 9.4.7 | Membership in a lattice, inclusion of lattices, and equality of lattices can be tested after completing at every finite place. | `Voight.Wave3.eq_iff_forall_localOrder_eq`, `Voight.Wave3.le_iff_forall_localOrder_le`, `Voight.Wave3.mem_of_forall_localOrder` | proved | stated for orders in algebras $(a,b)$ over a number field, which are lattices of the algebra |

## 10. Orders

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Lemma 10.4.3 | An order in a quaternion algebra over a number field is maximal if and only if its completion at every finite place is a maximal order. | `Voight.Wave3.isMaximalOrder_iff_forall_localOrder` | proved | orders in algebras $(a,b)$ with $a, b$ in the ring of integers of a number field |
| Corollary 10.5.5 | Over a principal ideal domain, the ring of $2 \times 2$ matrices over the ring is a maximal order in the matrix algebra over its fraction field, and every maximal order there is conjugate to it. | `QuatOrder.exists_eq_conj_matOrder`, `QuatOrder.isMaximalOrder_matOrder` | proved in part (see the last column) | matrices of size $2 \times 2$ only (the book treats size $n$) |

## 13. Quaternion algebras over local fields

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Proposition 13.3.4 | In a quaternion division algebra over a complete discrete valuation ring, the valuation ring of the extended valuation is the unique maximal order. | `QuatOrder.eq_valOrder_of_isMaximalOrder`, `QuatOrder.isMaximalOrder_valOrder` | proved | a Henselian valuation ring that is noetherian, algebra $(a,b)$ with $2ab \neq 0$ and no zero divisors |

## 14. Quaternion algebras over global fields

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Main Theorem 14.6.1 (finiteness and parity of the ramification set) | A quaternion algebra over a number field is ramified at only finitely many places, and the number of such places is even. | `Quat.ramified_finite_even` | proved | every number field, algebras $(a,b)$ with $a, b \neq 0$ |
| Main Theorem 14.6.1 (local-global principle for isomorphism) | Two quaternion algebras over a number field are isomorphic if and only if they have the same ramification at every place, and an algebra is split if and only if it is unramified everywhere. | `Voight.LocalGlobal.nonempty_algEquiv_iff_ram_eq`, `Voight.LocalGlobal.nonempty_algEquiv_iff_hilbert_eq`, `Voight.LocalGlobal.nonempty_algEquiv_one_iff` | proved | every number field, algebras $(a,b)$ with $a, b \neq 0$ |
| Main Theorem 14.6.1 (existence part) | For every finite set of real and finite places of even size, there is a quaternion algebra over the number field that is ramified exactly at those places. | `Voight.LocalGlobal.RamificationSurjective` | stated (a named proposition, not proved) | stated as a named proposition about a number field, not proved |
| Main Theorem 14.7.4 | The reduced norms of units of a quaternion algebra over a number field are exactly the nonzero elements that are positive at every real place where the algebra is ramified. | `Quat.eichler_norm_theorem_general`, `Quat.eichler_norm_theorem'` | proved | every number field for the first declaration; the second treats totally definite algebras over a totally real field |

## 15. Discriminants

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 15.5.5 | An order in a quaternion algebra over a number field is maximal if and only if its reduced discriminant equals the discriminant of the algebra. | `Voight.Disc.maximalIffDiscriminant`, `Voight.MaximalIffDiscriminant` | proved | every number field, orders in algebras $(a,b)$ with $a, b$ in the ring of integers |
| Theorem 15.5.5 (maximal orders have the algebra's discriminant) | The reduced discriminant of a maximal order in a quaternion algebra over a number field equals the product of the finite ramified primes. | `Voight.Disc.maximalOrderDiscriminant`, `Voight.MassWave2.MaximalOrderDiscriminant` | proved | every number field; this is one direction of the equivalence above |

## 17. Classes of quaternion ideals

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 17.8.3 (finiteness of the class set) | A maximal order in a quaternion division algebra over a number field has only finitely many classes of left ideals. | `QuatOrder.Gen.finite_classes`, `QuatOrder.finite_classes` | proved | maximal orders of division algebras $(a,b)$ over every number field (first declaration); the second requires the ring of integers to be a principal ideal domain |
| Theorem 17.8.3 and Corollary 17.8.5 (Eichler, indefinite case) | For an indefinite quaternion algebra over the rationals and a maximal order, the class number is one. | `Voight.ClassNumberOneIndefiniteRat` | stated (a named proposition, not proved) | base field the rational numbers; stated as a named proposition, not proved |

## 22. Quaternion orders and ternary quadratic forms

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Main Theorem 22.4.1 (Gross and Lucianovic) | Over a principal ideal domain, the even Clifford algebra gives a bijection between similarity classes of nondegenerate ternary quadratic forms and isomorphism classes of quaternion orders. | `Voight.mainTheorem_22_4_1_of_two_ne_zero`, `Voight.evenCliffordCorrespondence_of_two_ne_zero`, `Voight.EvenCliffordCorrespondence`, `Voight.MainTheorem22_4_1` | proved in part (see the last column) | proved when $2 \neq 0$ in the fraction field; the case of characteristic 2 is only stated (the last two declarations are the named propositions) |
| Main Theorem 22.4.1 (existence and uniqueness for orders in $(a,b)$) | Every order in a quaternion algebra $(a,b)$ over the fraction field of a principal ideal domain is isomorphic to the even Clifford algebra of a nondegenerate ternary quadratic form, which is unique up to similarity. | `Voight.OrderClf0.exists_unique_clf0`, `Voight.exists_clf0_of_isQuaternionOrder` | proved | principal ideal domains whose fraction field has $2 \neq 0$ |
| Corollary 22.3.22 | The even Clifford algebra of a nondegenerate ternary quadratic form over a domain is a quaternion order. | `Voight.isQuaternionOrder_clf0`, `Voight.isQuaternionAlgebra_clf0_field` | proved | domains whose fraction field has $2 \neq 0$ |
| Proposition 22.4.12 and Theorem 22.2.11 | Two nondegenerate ternary quadratic forms over a domain have isomorphic even Clifford algebras if and only if they are similar. | `Voight.nonempty_clf0_equiv_iff_similar` | proved | ternary forms of nonzero half-discriminant over an integral domain |

## 23. Quaternion orders

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Definition 23.4.1 | An Eichler order is the intersection of two maximal orders, in the formulation over a number field and in a general local form. | `Voight.IsEichlerOrder`, `Voight.Wave3.IsEichler` | stated (a named proposition, not proved) | the first declaration is for orders in algebras $(a,b)$ over a number field; the second is for a general algebra over the fraction field of a commutative ring |
| Proposition 23.4.3 (c) implies (a) | Over a local ring, the standard upper triangular order of level a power of a uniformizer is an Eichler order. | `Voight.Wave3.isEichler_stdEichlerOrder`, `Voight.Wave3.stdEichlerOrder_eq_inf` | proved | orders in the algebra of $2 \times 2$ matrices over the fraction field of a domain |
| Proposition 23.4.3 (a) implies (c) | Over a local ring, every Eichler order is conjugate to a standard upper triangular order of some level. | `Voight.Wave3.LocalEichlerStructure` | stated (a named proposition, not proved) | stated as a named proposition, not proved |

## 25. The Eichler mass formula

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 25.1.1 and Theorem 25.3.15 | For a definite quaternion algebra over the rationals, the mass of the left classes of a maximal order is the product of $p - 1$ over the ramified primes $p$, divided by $12$. | `Voight.Wave3.classMass_eq_rat_maximal`, `Voight.EichlerMassFormulaRat` | proved | maximal orders containing $\mathbb{Z}\langle i, j \rangle$ in algebras $(a,b)$ with $a, b$ integers; the second declaration is the named proposition without that containment |
| Theorem 25.3.18 | The mass formula over the rationals for Eichler orders of level $M$ multiplies the maximal-order mass by the Dedekind function $\psi(M)$. | `Voight.EichlerMassFormulaEichlerOrdersRat` | stated (a named proposition, not proved) | stated as a named proposition, not proved |
| Theorem 25.4.1 | A maximal order in a definite quaternion algebra over the rationals has class number one if and only if the discriminant is $2$, $3$, $5$, $7$ or $13$. | `Voight.Wave3.ClassNumberOneMaximalRat` | stated (a named proposition, not proved) | stated as a named proposition, not proved |

## 26. Classical zeta functions

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Main Theorem 26.1.5 and Theorem 26.1.12 (maximal orders) | The mass of the left classes of a maximal order in a totally definite quaternion algebra over a totally real field is $2\zeta_F(2)(2\pi)^{-2n}\|d_F\|^{3/2} h_F$ times the product of $N\mathfrak{p} - 1$ over the ramified finite primes, where $n$ is the degree of the field. | `Voight.Wave3.classMass_eq_maximal`, `Voight.EichlerMassFormulaMaximal` | proved | totally real field whose ring of integers is a principal ideal domain, algebras $(a,b)$ with $a,b$ in the ring of integers, orders containing $\mathbb{Z}_F\langle i,j \rangle$; the second declaration is the named proposition for every totally real field |
| Theorem 26.1.12 (Eichler orders) | The mass formula for Eichler orders of level $\mathfrak{M}$ in a totally definite quaternion algebra multiplies the maximal-order mass by the Dedekind function $\psi(\mathfrak{M})$. | `Voight.EichlerMassFormulaEichlerOrders` | stated (a named proposition, not proved) | stated as a named proposition, not proved |
| Corollary 26.4.7 | The Dirichlet series counting left ideals of a maximal order by reduced norm equals $\zeta_F(s)\zeta_F(s-1)$ times the product of $1 - N\mathfrak{p}^{1-s}$ over the ramified finite primes. | `QuatOrder.hasSum_zetaO`, `QuatOrder.Gen.hasSum_zetaO` | proved | real $s > 2$; the first declaration needs the ring of integers to be a principal ideal domain |
| Theorem 26.5.4 | Eichler's mass formula: the sum over the left ideal classes of the reciprocal indices of the unit groups, in a maximal order of a totally definite quaternion algebra, equals an explicit product of $\zeta_F(2)$, the discriminant, powers of $\pi$ and local factors at ramified primes. | `QuatOrder.Gen.eichler_mass_formula_nf'`, `QuatOrder.Gen.eichler_mass_formula_nf`, `QuatOrder.eichler_mass_formula'` | proved | totally real field, algebras $(a,b)$ with $a,b$ in the ring of integers, maximal orders containing $\mathbb{Z}_F\langle i,j \rangle$; the last declaration also needs the ring of integers to be a principal ideal domain; the formulas use the lattice constant of the order rather than the discriminant |

## 30. Optimal embeddings

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 30.1.5 | The class number of a maximal order in a definite quaternion algebra over the rationals of discriminant $D$ is $\varphi(D)/12$ plus two correction terms involving Kronecker symbols for $-4$ and $-3$ at primes dividing $D$. | `Voight.EichlerClassNumberFormulaRat`, `Voight.eichlerClassNumberFormulaRat_of_brandtTraceFormulaRat` | proved, conditional on `Voight.BrandtTraceFormulaRat` | level one and the rational numbers only; stated as a named proposition, and derived (second declaration) from the Brandt matrix trace formula of Theorem 41.1.13, which is itself stated and not proved |
| Main Theorem 30.8.6 | The Eichler class number formula over the rationals expressed through the mass and the numbers of optimal embeddings of the Gaussian and Eisenstein integers. | `Voight.EichlerClassNumberFormulaMassRat` | stated (a named proposition, not proved) | the rational numbers and maximal orders; stated as a named proposition, not proved |

## 41. Brandt matrices

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 41.1.13 and Main Theorem 41.5.2 | The trace of the Brandt matrix of index $n$ for a maximal order in a definite quaternion algebra over the rationals is a sum of class numbers of orders attached to integers $t$ with $t^2 < 4n$, plus a term for square $n$. | `Voight.BrandtTraceFormulaRat` | stated (a named proposition, not proved) | the rational numbers and maximal orders; stated as a named proposition, not proved (the class number formula of Theorem 30.1.5 is derived from it) |
