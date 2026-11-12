# G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices*: statement map

Ergebnisse der Mathematik und ihrer Grenzgebiete (3. Folge) 69, Springer, 2019. Items are numbered as in the book.

This is a statement map: it lists the central results of the book that are stated in the Lean library, with the Lean declarations and their status. It is not a complete map of the book; results that are not listed are not formalized here. *Proved* means proved in Lean with only the standard axioms and no unproved input (the declaration's whole dependency closure); *conditional* names the unproved inputs it still assumes; *stated* means that the result is stated as a named proposition (a Lean `def` or `structure` of type `Prop`) and not proved. When several declarations are listed, the status is that of the best one, and the last column says how the Lean statements differ from the book (restrictions or generalizations); *proved in part* means that the proved declarations cover only part of the result (a special case or some of its clauses), as the last column says. The statements are short descriptions in our own words, not quotations; read the book for the exact wording.

Rows: 23. proved: 4; proved in part: 5; conditional: 4; stated: 10.

## 1. Introduction

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Section 1.1, nonemptiness of X_n | The set $X_n$ of isomorphism classes of even unimodular lattices of rank $n$ is nonempty exactly when $8$ divides $n$. | `ChenevierLannes.classSet_nonempty_iff`, `ChenevierLannes.classSet` | proved | Positive definite lattices; proved without conditions. |
| Section 1.1, finiteness of X_n | For every rank $n$, the set $X_n$ of classes of even unimodular lattices is finite. | `ChenevierLannes.classSet_finite` | proved | Positive definite lattices; proved without conditions. |
| Section 1.1, the Leech lattice | There exists an even unimodular lattice of rank $24$ with no vectors of norm $2$ (the Leech lattice). | `ChenevierLannes.LeechExists`, `ChenevierLannes.IsLeechType` | stated (a named proposition, not proved) | Stated as a named proposition only; existence is not proved. Uniqueness is the row for Theorem 2.3.16. |
| Section 1.1, Niemeier lattices and the size of X_24 | The set $X_{24}$ has exactly $24$ elements, given the table of Coxeter numbers (root counts) of the Niemeier lattices. | `ChenevierLannes.niemeierCount_of_coxeterNumbers`, `ChenevierLannes.NiemeierCoxeterNumbers` | proved in part (see the last column), conditional on `ChenevierLannes.NiemeierCoxeterNumbers` | Conditional on the named proposition recording the table of Coxeter numbers. Weaker than the book: root systems are not formalized, so the bijection with root systems is not stated, only the count of classes and the Coxeter numbers. |
| Theorem A | For every prime $p$, the matrix of the Hecke operator $T_p$ on $\mathbb{Z}[X_{16}]$ is $c_{16}(p)$ times the identity plus an explicit rational multiple involving $\tau(p)$ of a fixed rank one integer matrix. | `ChenevierLannes.TheoremA` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. The odd-prime neighbour counting identities for rank $16$ are proved separately. |
| Theorem B (i) | A Niemeier lattice with roots is a $p$-neighbor of the Leech lattice if and only if $p$ is at least the Coxeter number of its root system. | `ChenevierLannes.TheoremB_i` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. The Coxeter number is defined as the number of roots divided by $24$. |
| Theorem B (ii) | The $p$-neighbor graph on $X_{24}$ is complete if and only if $p \ge 47$. | `ChenevierLannes.TheoremB_ii` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. |
| Equation (1.3.2), Witt and Igusa | The Siegel theta series of $E_8 \oplus E_8$ and of $E_{16}$ agree in every genus $g \le 3$. | `ChenevierLannes.wittIgusa_genus_one`, `ChenevierLannes.WittIgusa` | proved in part (see the last column) | The general statement is a named proposition only; the case of genus one is proved. |
| Theorem D | For genus $1 \le g \le 12$, the theta map from $\mathbb{C}[X_{24}]$ onto Siegel modular forms of weight $12$ is surjective and carries the kernel of the previous genus onto the cusp forms. | `ChenevierLannes.TheoremD` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. |

## 2. Bilinear and Quadratic Algebra

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Scholium 2.2.2 (b) | If an even unimodular lattice of rank $n$ exists, then $8$ divides $n$. | `ChenevierLannes.eight_dvd_of_isEvenUnimodular`, `ChenevierLannes.IsEvenUnimodular` | proved | Positive definite case only; proved without conditions. |
| Scholium 2.2.5 (b) and Proposition 2.2.6 | Any two even unimodular lattices of the same rank lie in the same genus. | `ChenevierLannes.sameGenus_of_isEvenUnimodular` | proved | Positive definite case only; proved without conditions. |
| Corollary 2.3.5 (Mordell) | Every even unimodular lattice of rank $8$ is isomorphic to $E_8$. | `ChenevierLannes.MordellRankEight` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. |
| Corollary 2.3.6 (Witt) | Every even unimodular lattice of rank $16$ is isomorphic to $E_8 \oplus E_8$ or to $E_{16}$, so $X_{16}$ has exactly two elements. | `ChenevierLannes.classSet_sixteen_ncard`, `ChenevierLannes.WittRankSixteen` | proved, conditional on `ChenevierLannes.WittRankSixteen` | Conditional on the named proposition asserting the classification in rank $16$. That the two lattices are not isomorphic is proved separately. |
| Theorem 2.3.16 (Conway) | Any two Niemeier lattices without roots are isomorphic, so the Leech lattice is unique. | `ChenevierLannes.ConwayLeechUnique` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. |
| Theorem 2.3.17 (Niemeier) | The $24$ classes of Niemeier lattices are determined by their root systems, whose Coxeter numbers are given by the table of the book. | `ChenevierLannes.NiemeierCoxeterNumbers`, `ChenevierLannes.niemeierCount_of_coxeterNumbers` | proved in part (see the last column), conditional on `ChenevierLannes.NiemeierCoxeterNumbers` | Numerical form only, stated as a named proposition: the multiset of Coxeter numbers of $X_{24}$. The bijection with root systems is not stated because root systems are not formalized. |

## 3. Kneser Neighbors

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Theorem 3.1.12 (Kneser) | For every prime $p$, the graph of $p$-neighbors on $X_n$ is connected. | `ChenevierLannes.kneser_connected_of_input`, `ChenevierLannes.KneserConnectivity` | proved in part (see the last column), conditional on `ChenevierLannes.EvenUnimodularOneSpinorGenus` | Proved for odd $p$ and $n \ge 3$, conditional on the named proposition that genus equals spinor genus for even unimodular lattices. The case $p = 2$ is only stated. |
| Proposition-Definition 3.2.1, odd primes | An even unimodular lattice of rank $n > 0$ has exactly $c_n(p) = 1 + p + \cdots + p^{n-2} + p^{n/2-1}$ neighbors at an odd prime $p$. | `ChenevierLannes.card_neighbors_eq_cn` | proved in part (see the last column) | Odd primes only; proved without conditions. |
| Proposition-Definition 3.2.1, the prime 2 | An even unimodular lattice of rank $n > 0$ has exactly $2^{n-1} - 1 + 2^{n/2-1}$ neighbors at the prime $2$. | `ChenevierLannes.NeighborCountTwo` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. |
| Proposition 3.2.2 | For each class $x$ in $X_n$, the neighbor counts $N_p(x, y)$ summed over all classes $y$ equal $c_n(p)$. | `ChenevierLannes.sum_nbNum`, `ChenevierLannes.nbCount_sixteen_add` | proved in part (see the last column) | Odd primes only; proved without conditions. The second declaration is the instance for rank $16$. |
| Proposition 3.2.3 | The neighbor counts satisfy the symmetry $N_p(x, y)/\|\mathrm{O}(y)\| = N_p(y, x)/\|\mathrm{O}(x)\|$ between two classes $x$ and $y$ in $X_n$. | `ChenevierLannes.nbNum_mul_autCard` | proved in part (see the last column) | Odd primes only; proved without conditions. |
| Proposition 3.2.4 | For each class $y$ in $X_n$, summing $N_p(x, y)$ divided by the order of the automorphism group of $x$ over all classes $x$ gives $c_n(p)$ divided by the order of the automorphism group of $y$. | `ChenevierLannes.sum_nbNum_div_autCard` | proved in part (see the last column) | Odd primes only; proved without conditions. |
| Section 3.3.1, the operator T_2 in rank 16 | In the basis $(E_{16}, E_8 \oplus E_8)$ of $\mathbb{Z}[X_{16}]$, the Hecke operator $T_2$ has the explicit matrix with entries $20025$, $18225$, $12870$, $14670$. | `ChenevierLannes.HeckeTwoSixteen` | stated (a named proposition, not proved) | Stated as a named proposition only; not proved. |

## 5. Theta Series and Even Unimodular Lattices

| Item | Statement | Lean declarations | Status | Lean statement: scope |
|---|---|---|---|---|
| Section 5.1, Siegel theta series are modular | For an even unimodular lattice of rank $n$ and every genus $g \ge 1$, the Siegel theta series is a Siegel modular form of weight $n/2$ for $\mathrm{Sp}_{2g}(\mathbb{Z})$. | `ChenevierLannes.SiegelThetaModular` | stated (a named proposition, not proved) | Stated as a named proposition only (a cited theorem of Freitag, not proved); only the values on the Siegel upper half space are used. |
