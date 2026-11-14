# G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*: statement map

Mathematical Surveys and Monographs 109, American Mathematical Society, 2004. Items are numbered as in the book: theorems and lemmas by number, displayed formulas as `(n.m)`.

This is a statement map: it lists the central results of the book that are stated in the Lean library, with the Lean declarations and their status. It is not a complete map of the book; results that are not listed are not formalized here. *Proved* means proved in Lean with only the standard axioms and no unproved input (the declaration's whole dependency closure); *conditional* names the unproved inputs it still assumes; *stated* means that the result is stated as a named proposition (a Lean `def` or `structure` of type `Prop`) and not proved. When several declarations are listed, the status is that of the best one, and the last column says how the Lean statements differ from the book (restrictions or generalizations); *proved in part* means that the proved declarations cover only part of the result (a special case or some of its clauses), as the last column says. The statements are short descriptions in our own words, not quotations; read the book for the exact wording.

Rows: 44. proved: 25; proved in part: 10; conditional: 2; stated: 7.

## 1. Quadratic forms and associative algebras

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Lemma 1.5 (ii) | For a nondegenerate quadratic space and a nonzero value $q$, the vectors $h$ with $Q(h)=q$ form a single orbit under the special orthogonal group when $n>1$, and the nonzero isotropic vectors form a single orbit when $n>2$; the orthogonal group is transitive on vectors of equal value by the Witt extension theorem. | `Shimura2004.lemma_1_5_ii_anisotropic`, `Shimura2004.lemma_1_5_ii_isotropic`, `Shimura2004.lemma_1_5_ii_orth`, `Shimura2004.intro_single_orbit` | proved in part (see the last column) | Only part (ii) of the lemma is stated; part (i), on extending isometric embeddings of subspaces, is not. |

## 2. Clifford algebras

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 2.6 | If the space contains a hyperbolic pair with orthogonal complement $U$, the Clifford algebra of the whole space is isomorphic to the algebra of $2\times 2$ matrices over the Clifford algebra of $U$, and its even part is isomorphic to the matrix algebra over the Clifford algebra of $U$ of the corresponding smaller size. | `Shimura2004.MatrixModel.theorem_2_6_one`, `Shimura2004.MatrixModel.theorem_2_6_one_even` | proved in part (see the last column) | Proved only for a single hyperbolic pair (the book allows any number of them, giving matrices of size $2^s$), and the statement on the even part is proved for $U\ne 0$ only; the case $U=0$ is not stated. |
| Lemma 2.7 (i), (ii), (iv) | For the product $z$ of an orthogonal basis, conjugation of a vector by $z$ gives $(-1)^{n-1}$ times that vector, the square and the reversal of $z$ are given by explicit signs and squares of the basis vectors, and $z$ is central when $n$ is odd. | `Shimura2004.vec_mul_orthProd`, `Shimura2004.orthProd_sq`, `Shimura2004.reverse_orthProd`, `Shimura2004.orthProd_mem_center_of_odd` | proved in part (see the last column) | Only the clauses on conjugation, the square, the reversal and centrality for odd $n$ are stated. |
| Theorem 2.8 (centres) | The centre of the Clifford algebra is spanned by $1$ and $z$ when $n$ is odd, and the centre of its even part is spanned by $1$ and $z$ when $n$ is even and positive. | `Shimura2004.theorem_2_8_ii_center`, `Shimura2004.theorem_2_8_i_center` | proved in part (see the last column) | Only the descriptions of the centres are stated; the central simplicity assertions and the tensor decomposition of the algebra are not. |

## 3. Clifford groups and spin groups

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| (3.1a), (3.1b) | An invertible element of the Clifford algebra lies in the Clifford group exactly when conjugation by it maps the space of vectors onto itself, and the even Clifford group is the intersection of the Clifford group with the even subalgebra. | `Shimura2004.mem_cliffordGroup_iff`, `Shimura2004.mem_M0_iff`, `Shimura2004.cliffordGroupOdd` | proved | — |
| (3.1c) and the discussion following it | Twisting by conjugation defines a homomorphism from the Clifford group to the orthogonal group of Q. | `Shimura2004.tau_mem_orth`, `Shimura2004.tau_mul`, `Shimura2004.tau` | proved | — |
| Lemma 3.3 | A nonisotropic vector is an element of the odd part of the Clifford group. | `Shimura2004.vecUnit_mem_cliffordGroupOdd` | proved | — |
| Theorem 3.6 (i) | For $n$ odd, the image of the Clifford group under the twisted conjugation map is the special orthogonal group, the element $-1$ is not in the image, and the Clifford group is the product of the units of the centre with the even Clifford group. | `Shimura2004.tau_mem_range_iff_of_odd`, `Shimura2004.det_tau_eq_one_of_odd`, `Shimura2004.tau_ne_neg_one_of_odd`, `Shimura2004.exists_central_mul_of_odd` | proved | — |
| Theorem 3.6 (ii) | For $n$ even and positive, the Clifford group equals the homogeneous Clifford group, its image is the full orthogonal group, its odd part maps exactly onto the orthogonal transformations of determinant $-1$, and the intersection of the centre of the even subalgebra with the even Clifford group is the nonzero scalars together with the nonzero multiples of $z$ (for $n>2$), or the units of that centre (for $n=2$). | `Shimura2004.exists_tau_eq_of_mem_orth_of_even`, `Shimura2004.cliffordGroup_le_homogeneous_of_even`, `Shimura2004.det_tau_of_mem_cliffordGroupOdd_of_even`, `Shimura2004.exists_tau_eq_of_det_eq_neg_one_of_even`, `Shimura2004.index_M0_homogeneous`, `Shimura2004.theorem_3_6_ii_center_inter_G_plus`, `Shimura2004.theorem_3_6_ii_center_inter_G_plus_two` | proved | The clause on the centre is proved for even $n\ge 2$, in separate statements for $n>2$ and for $n=2$. |
| Theorem 3.6 (iii) | Twisted conjugation induces an isomorphism from the even Clifford group modulo the nonzero scalars onto the special orthogonal group. | `Shimura2004.theorem_3_6_iii` | proved in part (see the last column) | The companion isomorphism of the full Clifford group modulo scalars with the orthogonal group, for $n$ even, is not stated as a single isomorphism, although its ingredients appear in the row for Theorem 3.6 (ii). |
| Theorem 3.7 (i) | The even Clifford group consists of the products of an even number of nonisotropic vectors, and the odd part of the Clifford group consists of the products of an odd number of them. | `Shimura2004.mem_M0_iff_exists_vecProd`, `Shimura2004.mem_cliffordGroupOdd_iff_exists_vecProd` | proved | — |
| Theorem 3.7 (ii) and (3.4) | The homogeneous Clifford group contains the even Clifford group with index $2$, and the multiplier, defined as an element times its reversal, is a homomorphism to the nonzero scalars that agrees with the value of Q on vectors. | `Shimura2004.index_M0_homogeneous`, `Shimura2004.homogeneousCliffordGroup`, `Shimura2004.multiplier`, `Shimura2004.multiplier_vecUnit`, `Shimura2004.reverse_mul_self_eq_multiplier`, `Shimura2004.involute_mul_reverse_involute_eq_multiplier` | proved | — |
| (3.5) | An element whose product with its reversal is a nonzero scalar and which conjugates the space of vectors into itself lies in the even Clifford group. | `Shimura2004.mem_M0_of_mul_reverse` | proved | — |
| (3.6) and the spin group | The spin group is the kernel of the multiplier on the even Clifford group, it meets the scalars in $\{\pm 1\}$, and twisted conjugation embeds its quotient by $\{\pm 1\}$ into the special orthogonal group. | `Shimura2004.mem_spinGroupG1_iff_mem_spinGroup`, `Shimura2004.spinGroupG1`, `Shimura2004.algebraMap_mem_spinGroupG1_iff`, `Shimura2004.tau_eq_one_iff_of_mem_spinGroupG1` | proved | — |
| (3.7), (3.7a) | The spinor norm of the image of an element of the even Clifford group is its multiplier modulo squares, and the image of the spin group is the set of rotations of spinor norm $1$. | `Shimura2004.spinorNormHom_tau`, `Shimura2004.tau_image_spinGroupG1` | proved | — |
| Lemma 3.8 | The even Clifford group, with its twisted conjugation action and multiplier, is unchanged when Q is scaled by a nonzero constant, and the Clifford group, the twisted action, the multiplier and the spinor norm are transported compatibly along an isometry. | `Shimura2004.mem_M0_iff_exists_evenScale`, `Shimura2004.tau_evenScaleM0Equiv`, `Shimura2004.multiplier_evenScaleM0Equiv`, `Shimura2004.cliffordUnitMap_mem_cliffordGroup_iff`, `Shimura2004.tau_cliffordGroupMap`, `Shimura2004.multiplier_cliffordUnitMap`, `Shimura2004.spinorNormHom_conjIsometry` | proved | — |
| Lemma 3.10, (3.11), (3.12) | In the presence of a hyperbolic pair, the elements $e(a,b)$ form a homomorphic image of pairs of nonzero scalars in the even Clifford group, with multiplier $ab$, acting by an explicit diagonal rescaling. | `Shimura2004.eabHom_mem_M0`, `Shimura2004.multiplier_eab`, `Shimura2004.tau_eab`, `Shimura2004.tau_qe_add_f` | proved | — |
| Lemma 3.13 | For a nonisotropic vector $\kappa$ with orthogonal complement $W$, the elements of the even Clifford group of the whole space are exactly the elements $p+\kappa q$ of one of two explicit types, with $p$ in the even Clifford group of $W$ and $q\in Wp$, or $q$ in the odd Clifford group of $W$ and $p\in Wq$, and the multiplier of such an element is $pp^{*}+\kappa^{2}qq^{*}$. | `Shimura2004.lemma_3_13`, `Shimura2004.lemma_3_13_type1_mem`, `Shimura2004.lemma_3_13_type2_mem`, `Shimura2004.lemma_3_13_type1_norm`, `Shimura2004.lemma_3_13_type2_norm` | proved | — |
| Lemma 3.15 | For an element of the homogeneous Clifford group written as a $2\times 2$ matrix over the Clifford algebra of $U$ via the matrix model, the entries satisfy explicit symmetry relations on products of pairs of entries, each entry has a scalar product with its reversal and conjugates $U$ into itself, and each invertible entry lies in the Clifford group of $U$. | `Shimura2004.MatrixModel.lemma_3_15_i`, `Shimura2004.MatrixModel.lemma_3_15_ii`, `Shimura2004.MatrixModel.lemma_3_15_iii` | proved | — |
| Lemma 3.16 | For a nonisotropic vector $h$ with orthogonal complement $W$, elements $a$ of the even (respectively odd) part of the Clifford group of $W$ satisfy $a^{*}ha=\pm\nu(a)h$, with the sign given by the parity; moreover the elements of the even Clifford group with $a^{*}ha$ a multiple of $h$ form the union of the even Clifford group of $W$ and $h$ times its odd part, and those with $a^{*}ha=\nu(a)h$ form the even Clifford group of $W$. | `Shimura2004.lemma_3_16_even`, `Shimura2004.lemma_3_16_odd`, `Shimura2004.lemma_3_16_h_even`, `Shimura2004.lemma_3_16_h_odd`, `Shimura2004.formula_3_20a`, `Shimura2004.formula_3_20b` | proved | — |

## 4. Parabolic subgroups

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Proposition 4.3 | The even Clifford group is the product of the stabilizer of a fixed isotropic line with the spin group. | `Shimura2004.prop_4_3_M0_eq_mul` | proved | — |
| (4.8) and the discussion following it | Twisted conjugation maps the parabolic subgroup of the even Clifford group onto the corresponding parabolic subgroup of the special orthogonal group. | `Shimura2004.tau_mem_parabolicSO`, `Shimura2004.exists_tau_eq_of_mem_parabolicSO` | proved | — |

## 8. Clifford groups over a local field

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Proposition 8.7 | The image of the multiplier on the even Clifford group is all nonzero scalars when the space contains an isotropic vector or, locally, when $n\ge 3$; it is the squares when $n=1$, and the norms from the discriminant extension when $n=2$. | `Shimura2004.prop_8_7_isotropic`, `Shimura2004.prop_8_7_local`, `Shimura2004.prop_8_7_dim_one`, `Shimura2004.prop_8_7_binary` | proved | The local case is proved for completions of a number field at finite primes, not for every local field. |

## 8. Formal Hecke algebras and formal Euler factors

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| (8.23a) | For a maximal lattice over a finite-prime completion whose anisotropic part has dimension at most $1$, the dilation series over the double cosets of the stabilizer in the special orthogonal group equals an explicit product of local Euler factors. | `Shimura2004.Formula8_23a` | stated (a named proposition, not proved) | Stated only, not proved. |

## 9. Orthogonal, Clifford, and spin groups over a global field

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 9.18 | When Q is indefinite at some real place and $n\ge 3$, every adelic rotation of spinor norm one lies in a rational rotation times the stabilizer of the lattice. | `Shimura2004.theorem_9_18_weak` | proved | Weak form: the book places the rational part in a smaller subgroup (the global spinor kernel) and allows every open subgroup in place of the stabilizer of the standard lattice. |
| Lemma 9.19 (iii) | For indefinite Q and $n\ge 3$, the spinor norm identifies the set of classes in the genus of the standard lattice with the quotient of the ideles by the rational ideles times the image of the stabilizer, which gives the number of classes. | `Shimura2004.lemma_9_19_iii` | proved | Stated for the stabilizer of the standard lattice over the ring of integers of a number field. |

## 10. Quadratic Diophantine equations over a local field

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 10.3 | Over a finite-prime completion of a number field, the lattice vectors of a fixed nonzero value of Q form finitely many orbits under the stabilizer of the lattice in the special orthogonal group. | `Shimura2004.Theorem10_3` | stated (a named proposition, not proved) | Stated only, not proved. |
| Theorem 10.5 | For a maximal lattice satisfying the unit-discriminant condition, two vectors with the same value of Q and the same ideal generated by their pairings with the lattice lie in one orbit of the stabilizer. | `Shimura2004.Theorem10_5` | stated (a named proposition, not proved) | Stated only, not proved. |

## 11. Quadratic Diophantine equations over a global field

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 11.1 (i) | Over a number field, the lattice vectors of a fixed nonzero value of Q form finitely many orbits under the stabilizer of the lattice in the special orthogonal group. | `Shimura2004.theorem_11_1_i_definite`, `Shimura2004.Theorem11_1_i` | proved in part (see the last column) | Proved only when Q is totally positive definite, and then without requiring the value to be nonzero; the general statement is stated but not proved. |
| Theorem 11.6 (i) | The number of orbits of representations of a value by the lattices of a minimal system of classes in a genus equals the class number of the special orthogonal group of the orthogonal complement of a representing vector. | `Shimura2004.Theorem11_6_i`, `Shimura2004.FundamentalTheorem11_6` | stated (a named proposition, not proved) | Stated only, not proved; the named structure is used as an input to the results that depend on it. |
| Theorem 11.6 (v) | The set of representations of a value by a lattice is nonempty exactly when the lattice is equivalent to a member of the minimal system. | `Shimura2004.Theorem11_6_v` | stated (a named proposition, not proved) | Stated only, not proved. |

## 12. The class number of an orthogonal group and sums of squares

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 12.14 (iv) | For sums of $5$, $7$ or $9$ squares, the number of orbits of representations of a positive integer by a maximal lattice equals the class number of the special orthogonal group of the orthogonal complement. | `Shimura2004.theorem_12_14_iv`, `Shimura2004.Theorem12_14_iv` | proved, conditional on `Shimura2004.FundamentalTheorem11_6`, `Shimura2004.SumSquaresOneClass` | Conditional on two named inputs: the fundamental theorem on representations (Theorem 11.6 (i)) and the statement that the genus of maximal lattices is a single class. |

## 13. Nonscalar quadratic Diophantine equations; connection with the mass formula

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| (13.12) and (13.13b) | For totally positive definite Q the mass of the special orthogonal group is twice the mass of the orthogonal group, and the mass of the genus of maximal lattices is given by an explicit product of Euler factors and zeta values. | `Shimura2004.exact_mass_maximal_definite`, `Shimura2004.exact_mass_maximal`, `Shimura2004.mass_SO_eq_two_mul_mass_O`, `Shimura2004.mass_SO_eq_two_mul_mass_O_lat` | proved | The comparison of masses is proved for the standard lattice and, for $n$ odd, for every integral lattice; the explicit mass formula is proved for $n\ge 3$ and maximal standard lattices over the ring of integers of a number field, and the book credits it to another paper of the author. |
| (13.14) and (13.16) | For totally positive definite Q, the set of lattice vectors of a given value and given pairing ideal is finite, and its mass (the weighted count by the automorphism group of the lattice) equals its number of elements. | `Shimura2004.formula_13_16`, `Shimura2004.massSolSet` | proved | Proved for totally positive definite Q over a number field only. |
| (13.18) | For totally positive definite Q, the weighted count of representations of a value by the lattices of the minimal system equals the mass of the special orthogonal group of the orthogonal complement. | `Shimura2004.formula_13_18`, `Shimura2004.Formula13_18` | proved, conditional on `Shimura2004.FundamentalTheorem11_6_ii` | Proved from the named input stating the correspondence of orbits of Theorem 11.6 (i) and (ii), which is itself stated but not proved; the correspondence is stated with equal orders of stabilizers, which is weaker than the isomorphism in the book. |
| Theorem 13.14 | The number of representations of a squarefree positive integer as a sum of $5$, $7$ or $9$ squares of integers or half-integers is an explicit constant times a special value of the Dirichlet $L$-function of a quadratic field. | `Shimura2004.Theorem13_14` | stated (a named proposition, not proved) | Stated only, not proved. |

## 14. Clifford and spin groups over the real numbers: the case of signature (1, m)

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 14.2 (i) | For a nondegenerate real quadratic form on a nonzero space, the subgroup of the even Clifford group with positive multiplier has index $1$ if the form is definite and index $2$ otherwise. | `Shimura2004.theorem_14_2_i`, `Shimura2004.G0` | proved | — |
| Theorem 14.2 (ii) | For a nondegenerate real quadratic form, the positive-multiplier group modulo the real scalars, the spin group modulo $\{\pm1\}$ and the image of the spin group under twisted conjugation are isomorphic, and the image of the positive-multiplier group equals the image of the spin group; this image is the identity component of the special orthogonal group. | `Shimura2004.theorem_14_2_ii_algebraic`, `Shimura2004.Theorem14_2_ii_identityComponent` | proved in part (see the last column) | The algebraic isomorphisms are proved; the identification of the image with the identity component of the special orthogonal group is stated but not proved. |
| Theorem 14.2 (iii) | The positive-multiplier subgroup and the spin group are connected when the dimension exceeds $2$, and in dimension $2$ the spin group is connected exactly when the form is definite. | `Shimura2004.Theorem14_2_iii` | stated (a named proposition, not proved) | Stated only, not proved. |
| Theorem 14.2 (iv) | For an orthogonal decomposition of a real quadratic space into a positive definite part $X$ and a negative definite part $Y$, the product of the spin groups of $X$ and $Y$ is a maximal compact subgroup of the spin group of the space, and the two factors meet in $\{\pm1\}$. | `Shimura2004.spin_inter_eq_one_or_neg_one`, `Shimura2004.Theorem14_2_iv` | proved in part (see the last column) | Only the intersection statement is proved, over any field of characteristic different from $2$; the maximal compactness is stated but not proved. |
| Theorem 14.3 | For a Witt decomposition of a real quadratic space with the anisotropic part negative definite, the form is positive definite on $X$ and negative definite on $Y$, and the spin group, the even Clifford group and the positive-multiplier group are each a product of a parabolic subgroup with the compact group built from $X$ and $Y$. | `Shimura2004.isWittDecomposition_definite`, `Shimura2004.Theorem14_3` | proved in part (see the last column) | Only the definiteness of the form on $X$ and $Y$ is proved; the product decompositions are stated but not proved, and the statement for even dimension is not included. |
| Theorem 14.7 | For the action of the even Clifford group on the tube domain of signature $(1,m)$ by generalized fractional linear transformations, the action satisfies a group law (1) and a cocycle law (2), the automorphy factor being invertible and the action preserving the domain. | `Shimura2004.MatrixModel.theorem_14_7_1`, `Shimura2004.MatrixModel.theorem_14_7_2`, `Shimura2004.MatrixModel.Theorem14_7` | proved in part (see the last column) | The group law and the cocycle law are proved under the hypothesis that the automorphy factors are invertible, which the main assertion of the theorem asserts and which is stated but not proved; the remaining parts (3) to (7) are not stated. |

## 15. The case of signature (2, m)

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Lemma 15.4 | For a space of signature $(1,m-1)$, if $z=x+iy$ with $y$ in the open light cone, then $z$ is invertible in the complexified Clifford algebra and $-z^{-1}$ again lies in the tube domain. | `Shimura2004.lemma_15_4`, `Shimura2004.Lemma15_4` | proved | Proved in a vector form: the complexified Clifford algebra is not constructed, and invertibility is expressed as nonvanishing of the complexified value of Q. |

## 16. Orthogonal groups over the real numbers and symmetric spaces

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Lemma 16.5 | Every invertible real matrix factors uniquely as a positive definite symmetric matrix times an orthogonal one, and positive definite matrices are exactly the products of a triangular matrix with its transpose, uniquely. | `Shimura2004.lemma_16_5_polar`, `Shimura2004.lemma_16_5_cholesky` | proved | — |
