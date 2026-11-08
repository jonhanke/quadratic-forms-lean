# J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices IV: the mass formula": map to the Lean library

Proceedings of the Royal Society of London A 419 (1988), 259–286. Items: displayed formulas as `(n)`, lemmas by number, sections as `§n`.

Each row is a result of the book (numbered, or stated in the text: `41, text 17` is the 17th result stated in the running text of §41 or Chapter 41, `41, proof step 2` a step inside a proof), the Lean declaration that formalizes it, and its status. *Proved* means proved in Lean with only the standard axioms and no unproved input (the declaration's whole dependency closure); *conditional* names the unproved inputs it still assumes; *not formalized* means the library does not state it. Rows that are not results (summaries, history, plans) are omitted. The statements in the middle column are short descriptions, not quotations; read the book for the exact wording. Items of the book that the library states in a generalized form (for example over every number field) are mapped to the general statement.

Rows: 72. proved: 57; formalized as a definition, in Mathlib, or inside proofs: 12; out of scope: 3.

## §1. Introduction (pp. 259–260)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (1) | 259 | $m(f) = \sum_{i=1}^h 1/\lvert\mathrm{Aut}(f^{(i)})\rvert$ over the inequivalent forms of the genus of a positive definite integral $f$ | `Siegel.mass` | formalized (a definition, or used in proofs) |
| §1, text 2 | 259 | $h$ is the class number of the genus | `Siegel.genusFinite` | proved |
| §1, text 3 | 259–260 | The $p$-mass is the product of diagonal factors, cross terms and the type factor; mass is a rational multiple of the standard mass | `ConwaySloane.Mass.example_ii_ratio_irrational` | proved |
| §1, text 4 | 260 | $\zeta_D(s) = \sum_{m = 1,3,5,\ldots}(D/m)m^{-s}$, $D = (-1)^sd$, for $n = 2s$ | `ConwaySloane.Mass.hasSum_zetaD` | proved |
| §1, text 5 | 260 | $1 - \frac15 + \frac17 - \frac1{11} + \frac1{13} - \cdots = \pi/(2\sqrt3)$ ($d = 3$, $s = 1$, $D = -3$) | `ConwaySloane.Mass.zetaD_neg_three_one` | proved |
| §1, text 6 | 260 | $1 + 3^{-4} + 5^{-4} + 7^{-4} + \cdots = \pi^4/96$ ($d = D = 1$, $s = 4$) | `ConwaySloane.Mass.zetaD_one_four` | proved |
| §1, text 7 | 260 | $d = D = 2$, $s = 6$: $1 - 3^{-6} - 5^{-6} + 7^{-6} + 9^{-6} - \cdots = 361\pi^6/(245760\sqrt2)$ | `ConwaySloane.Mass.zetaD_two_six` | proved |

## §4. The mass formula (p. 263)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (2) | 263 | $m(f) = 2\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\prod_p(2m_p(f))$, $n \ge 2$ | `ConwaySloane.Mass.mass_formula_two` | proved |
| §4, text 1 | 263 | The $p$-mass is the reciprocal of the number of automorphisms of $f$ modulo $p^r$, times a normalizing power of $p$ (§12) | `ConwaySloane.Mass.countN`, `ConwaySloane.Mass.pMassDensity` | formalized (a definition, or used in proofs) |
| (3) | 263 | $m_p(f) = \prod_q M_p(f_q)\cdot\prod_{q<q'}(q'/q)^{\frac12n(q)n(q')}\cdot 2^{n(\mathrm{I,I}) - n(\mathrm{II})}$ | `ConwaySloane.Mass.pMassFormulaOdd` | proved |
| §4, text 2 | 263 | Definitions: diagonal factor, diagonal product, cross term, cross-product, type factor; $n(\mathrm{II})$ = sum of dimensions of type II constituents, $n(\mathrm{I,I})$ = number of adjacent pairs $f_q, f_{2q}$ both of type I | `ConwaySloane.Mass.crossExp`, `ConwaySloane.Mass.nII`, `ConwaySloane.Mass.nII'`, `ConwaySloane.Mass.diagProdTwo` | formalized (a definition, or used in proofs) |

## §5. Computing the diagonal factors $M_p(f_q)$ (pp. 263–265)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (4) | 263 | $p$-adic Jordan decomposition $f = \sum_q qf_q$ over all powers $q$ of $p$ (negative exponents included), $f_q$ unit forms, almost all of dimension 0 | `ConwaySloane.IsOddSymbolOf`, `ConwaySloane.IsTwoSymbolOf` | formalized (a definition, or used in proofs) |
| §5, text 1 | 263–264 | Orthogonal groups over $\mathbb F_p$: one group $O_N(p)$ for $N$ odd, two $O_{N\pm}(p)$ for $N$ even; the *species* $N$, $N+$, $N-$ | `ConwaySloane.Mass.Species` | formalized (a definition, or used in proofs) |
| Table 1 | 264 | The species of $f_q$: for $p = 2$ from type, dimension, octane value and free/bound status; for odd $p$ from the dimension and whether $d_q$ is a residue, $p \equiv \pm1 \pmod 4$ | `ConwaySloane.Mass.species_f_g` | proved |
| §5, text 2 | 265 | Odd $p$: only the dimension and the quadratic character of $d_q$ matter | `ConwaySloane.Mass.oddSpecies` | formalized (a definition, or used in proofs) |
| §5, text 3 | 265 | Octane value: type II: $0$ or $4$ as $\det \equiv \pm1$ or $\pm3 \pmod 8$; type I: $\#\{a_i \equiv 1\} - \#\{a_i \equiv -1\} \pmod 4$ in a diagonalization; equals the oddity, $+4$ if the sign is $-$ | `ConwaySloane.Mass.octane_diag` | proved |
| §5, text 4 | 265 | $f_q$ is *bound* if $f_{q/2}$ or $f_{2q}$ has type I, otherwise *free* | `ConwaySloane.Mass.pMassTwo_moveEquiv` | proved |
| (5) | 265 | $M_p(2s-1) = \frac1{2(1-p^{-2})\cdots(1-p^{2-2s})}$, $M_p(2s\pm) = \frac1{2(1-p^{-2})\cdots(1-p^{2-2s})(1\mp p^{-s})}$ | `ConwaySloane.Mass.Species.diagFactor` | formalized (a definition, or used in proofs) |
| Table 2 | 264 | The diagonal factors for species $0+, 1, 2\pm, 3, 4\pm, 5$ and $p = 2, 3, 5, 7$, general $p$; also $\mathrm{std}_p$ for dimensions $1,2$; $3,4$; $5,6$ | `ConwaySloane.Mass.table2_general` | proved |
| §5, text 5 | 265 | For odd $p$, or $p = 2$ and $f_q$ free, $M_p(f_q)$ is the $p$-mass of $f_q$ as a form in its own right | `ConwaySloane.Mass.pMassDensity_unitEntries` | proved |

## §6. Love forms: the mass formula in dimensions 0 and 1 (pp. 265–266)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §6, text 1 | 265–266 | Love forms (dimension 0): factor 1 for odd $p$; for $p = 2$ free love forms contribute 1, bound love forms $\frac12$ | `ConwaySloane.Mass.diagProdTwo_abbrev` | proved |
| §6, text 2 | 266 | The initial 2 of (2) is the Tamagawa number of $SO_n$; it should be 1 in dimensions 0 and 1 (local and global forms of given determinant are unique) | `ConwaySloane.Mass.mass_dim_zero` | proved |
| §6, text 3 | 266 | $2m_p(f)$ is the proper $p$-mass ($[O_n : SO_n] = 2$); replace by 1 in dimension 0 | `Tamagawa.mass_SO_eq_two_mul_mass` | proved |

## §7. The standard $p$-masses and the standard mass (pp. 266–267)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (6) | 266 | $\mathrm{std}_p(f) = 1/(2(1-p^{-2})\cdots(1-p^{2-2s})(1-\epsilon p^{-s}))$, $\epsilon = 0$ ($n$ odd) or $(D/p)$, $D = (-1)^sd$, $0$ if $p \mid 2d$ | `ConwaySloane.Mass.stdP` | formalized (a definition, or used in proofs) |
| §7, text 1 | 266 | For all but finitely many $p$, $m_p(f) = \mathrm{std}_p(f)$ | `ConwaySloane.Mass.pMassDensity_eq_stdP` | proved |
| (7) | 266 | $\mathrm{std}(f) = 2\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\cdot\zeta(2)\zeta(4)\cdots\zeta(2s-2)\cdot\zeta_D(s)$ ($\zeta_D$ omitted for $n$ odd) | `ConwaySloane.Mass.stdMass_odd` | proved |
| (8) | 266 | $\zeta_D(s) = \prod_p(1 - (D/p)p^{-s})^{-1}$ | `ConwaySloane.Mass.eulerProduct_zetaD` | proved |
| (9) | 266 | $= \sum_{m = 1,3,5,\ldots}(D/m)m^{-s}$, Jacobi symbol | `ConwaySloane.Mass.hasSum_zetaD` | proved |
| §7, text 2 | 266 | The actual mass is a simple rational multiple of the standard mass | `ConwaySloane.Mass.example_ii_ratio_irrational` | proved |
| Table 3 | 267 | $\mathrm{std}(f)$ for $n \le 25$ (as a multiple of $\zeta_D(s)$ for $n$ even) | `ConwaySloane.Mass.stdMass_table_1` | proved |

## §8. Calculation of $\zeta_D(s)$ (pp. 267–271)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §8, text 1 | 267–268 | $\chi(m) = (D/m)$ ($m$ odd), $0$ ($m$ even) is a Dirichlet character; modulus $k$, conductor $k_1$, $\chi = \chi_1\psi$ with $\chi_1$ principal mod $k$ and $\psi$ primitive mod $k_1$ | `ConwaySloane.Mass.chiD`, `ConwaySloane.Mass.IsModulus`, `ConwaySloane.Mass.IsConductor` | formalized (a definition, or used in proofs) |
| (10) | 268 | $\zeta_D(s) = L(s,\chi) = L(s,\psi)\prod_{p \mid k}(1 - \psi(p)/p^s)$ | `ConwaySloane.Mass.zetaD_eq_L_mul` | proved |
| (11) | 268 | Functional equation $L(1-s,\psi) = \frac{k_1^{s-1}\Gamma(s)}{(2\pi)^s}(i^{-s} + \psi(-1)i^s)G(\psi)L(s,\bar\psi)$, Gauss sum $G(\psi)$ | `ConwaySloane.Mass.LFunction_one_sub_primitive` | proved |
| (12) | 268 | $L(1-s,\psi) = -\frac{k_1^{s-1}}{s}\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)$ | `ConwaySloane.Mass.LFunction_one_sub_bernoulli` | proved |
| (13) | 268 | $\zeta_D(s) = \prod_{p\mid k}(1 - \psi(p)/p^s)\cdot\frac{-(2\pi)^s}{s!(i^{-s}+\psi(-1)i^s)}\cdot\frac{\sum\psi(r)B_s(r/k_1)}{\sum\psi(r)e^{2\pi ir/k_1}}$ | `ConwaySloane.Mass.zetaD_formula` | proved |
| (14) | 268 | $\zeta_{4D}(s) = \zeta_D(s)$, $\zeta_{p^3D}(s) = \zeta_{pD}(s)$ ($p$ odd) | `ConwaySloane.Mass.zetaD_four_mul` | proved |
| (15) | 268 | $\zeta_1(s) = (1-2^{-s})\zeta(s) = (1-2^{-s})\frac{(2\pi)^s}{2\cdot s!}\lvert B_s\rvert$ ($s$ even) | `ConwaySloane.Mass.zetaD_one_eq` | proved |
| (16) | 268 | $\zeta_{-1}(s) = \frac{(\frac12\pi)^s}{2(s-1)!}\lvert E_{s-1}\rvert$ ($s$ odd) | `ConwaySloane.Mass.zetaD_neg_one_euler_all` | proved |
| Table 4 | 269 | Modulus $k$ and conductor $k_1$ of $\chi$ for $\lvert D\rvert \le 11$ | — | formalized (a definition, or used in proofs) |
| Table 5 | 269 | Values of $\psi(m)$, $1 \le m \le k_1$, $\lvert D\rvert \le 9$ | — | formalized (a definition, or used in proofs) |
| Table 6 | 270–271 | $\zeta_D(s)d^{s-1}\sqrt d/\pi^s$ for $d \le 25$, $s \le 12$ | `ConwaySloane.Mass.zetaD_eq_abs` | proved |

## §9. Examples of mass calculations (pp. 269–274)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §9 (i) | 269–272 | $f = \mathrm{diag}(7,1,1)$: tableau, $m_2 = \frac14 = \frac38\mathrm{std}_2$, $m_7 = \frac{49}{32} = 3\,\mathrm{std}_7$, $\mathrm{std}(f) = \frac16$, $m(f) = \frac3{16}$ | `ConwaySloane.Mass.example_i_two` | proved |
| (17) | 272 | For $p \mid 2d$: $\mathrm{std}_p(f) = M_p(n)$ ($n$ odd), $M_p(n-1)$ ($n$ even) | `ConwaySloane.Mass.stdP_of_dvd` | proved |
| §9 (i).r2 | 272 | The genus of $\mathrm{diag}(7,1,1)$ has two classes, $7 \oplus I_2$ and $7_2 \oplus I_1$, with $\lvert\mathrm{Aut}\rvert = 16$, $8$; $\frac1{16}+\frac18 = \frac3{16}$ | `ConwaySloane.Mass.example_i_two_classes` | proved |
| §9 (ii) | 272–273 | $f = a_3 \oplus I_1$, $\det 24$: diagonalizations, tableau, $m_2 = \sqrt2$, $m_3 = 27\sqrt3/32$, $m(f) = \frac3{32}$ | `ConwaySloane.Mass.example_ii_two` | proved |
| §9 (ii).r2 | 273 | The genus of $a_3 \oplus I_1$ has two classes ($f$ and $c_4$), masses $\frac1{2^2\cdot2\cdot2\cdot2} + \frac1{2\cdot8\cdot1} = \frac3{32}$ | `ConwaySloane.Mass.example_ii_two_classes` | proved |
| §9 (iii) | 273 | Abbreviated tableau: omit love forms, type factor $2^{j-k-l}$ ($l$ = number of bound love forms) | `ConwaySloane.Mass.diagProdTwo_abbrev` | proved |
| §9 (iv) | 274 | For $d = 1$, (2) gives the masses of the unimodular genera (Sphere Packings, Lattices and Groups Ch. 16, Thms. 1, 2) | `ConwaySloane.Mass.unimodular_II8` | proved |

## §10. Verification of the results of part I (pp. 274–280)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §10, text 1 | 274 | Vines: the graph on genera with $L$ and $L \oplus I_1$ joined; each component is a stem of odd genera with at most one even twig per node (by Lemma 3) | `ConwaySloane.Mass.vineGraph_structure` | proved |
| §10, text 2 | 274 | The $n$-dimensional lattices of a vine are the $L_r \oplus I_{n-r}$ | `ConwaySloane.Mass.vine_lattices` | proved |
| Table 7 | 275 | Masses of $I_n(11^+)$, $n \le 7$, as sums of the contributions $L_k \oplus I_{n-k}$ | `ConwaySloane.Mass.table7_total_one` | proved |
| §10, text 3 | 275 | The mass of $L_k \oplus I_r$ is that of $L_k \oplus I_{r-1}$ divided by $2r$ ($L_k$ without norm-1 vectors) | `ConwaySloane.Mass.card_aut_sumI` | proved |
| Table 8 | 276–277 | The vines of the lattices of Part I | — | out of scope (not formalized) |
| Table 9 | 278–279 | Witt components and $g_1, g_2$ for the lattices of Table 8 not in Part I | — | out of scope (not formalized) |

## §11. Properties of the genus (pp. 280–281)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Lemma 1 | 280 | $f$, $g$ in the same genus iff $f \oplus \begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $g \oplus \begin{pmatrix}0&1\\1&0\end{pmatrix}$ are integrally equivalent | `ConwaySloane.lemma1Statement_proof` | proved |
| §11, text 1 | 280 | The discriminant quadratic form on $L^*/L$, values in $\mathbb Q/\mathbb Z$ ($\mathbb Q/2\mathbb Z$ if $L$ even) | `ConwaySloane.Mass.dualNorm_congr_one` | proved |
| Lemma 2 | 280 | $L$, $M$ in the same genus iff same dimension, same type $T$, and $L^*/L \cong M^*/M$ preserving norms mod $T$ | `ConwaySloane.Mass.lemma2_if_odd` | proved |
| Lemma 3 | 280 | $L \oplus I_1$, $M \oplus I_1$ in the same genus and same type $\Rightarrow$ $L$, $M$ in the same genus | `ConwaySloane.Mass.lemma3Statement_proof` | proved |
| Lemma 4 | 280 | Same genus iff same dimension and type and $L^*/L \cong M^*/M$ preserving norms mod 1 | `ConwaySloane.Mass.Gauss2.lemma4Statement_holds` | proved |
| §11, text 2 | 280–281 | Lemma 4 is not categorical: the isomorphism of discriminant groups need not come from a 2-adic equivalence | `ConwaySloane.Mass.lemma4_not_categorical` | proved |
| §11, text 3 | 281 | $d = 2$: $v_2\cdot v_2 \equiv \frac12 \pmod 1$; two genera $I_n(2)$, $II_n(2)$ | `ConwaySloane.Mass.norm_generator_det_two` | proved |
| §11, text 4 | 281 | $d = p$ odd prime: four genera $I_n(p^\pm)$, $II_n(p^\pm)$ | `ConwaySloane.Mass.genera_det_prime` | proved |
| §11, text 5 | 281 | $d = 2p$: four genera $I_n(d^\pm)$, $II_n(d^\pm)$ | `ConwaySloane.Mass.genera_det_two_prime` | proved |

## §12. The $p$-adic density and the $p$-mass (pp. 281–282)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (18) | 281 | $N(p^r) = \#\{X \bmod p^r : X^{\mathrm{tr}}AX \equiv A \pmod{p^r}\}$ | `ConwaySloane.Mass.countN_eq_shimuraCount` | proved |
| §12, text 1 | 281 | $\alpha_p(f) = N(p^r)/p^{\frac12rn(n-1)}$ is independent of $r$ for large $r$; $m_p(f) = p^{\frac12s(n+1)}/\alpha_p(f)$, $p^s \parallel \det f$ | `ConwaySloane.Mass.alphaP_stabilizes` | proved |
| §12, text 2 | 282 | The $p$-mass is invariant under scaling the form; the $p$-adic density is not | `ConwaySloane.Mass.pMassDensity_smul_prime` | proved |
| §12, text 3 | 282 | The $p$-mass is the reciprocal of the order of the automorphism group of $f$ modulo $p^r$ times a normalizing power | `ConwaySloane.Mass.countN` | formalized (a definition, or used in proofs) |

## §13. The structure of the mass formula (pp. 282–284)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §13, text 2 | 283 | $f = \begin{pmatrix}2&1\\1&2\end{pmatrix}$, $g = f \oplus 2$: same $q = 1$ constituent $2(x^2+xy+y^2)$, type II, octane value 4; free for $f$, bound for $g$ | `ConwaySloane.Mass.species_f_g` | proved |
| §13, text 3 | 283 | $g$ is 2-adically equivalent to $h = \begin{pmatrix}2&1&0\\1&4&0\\0&0&6/7\end{pmatrix}$, $h_1 = 2(x^2+xy+2y^2)$ of octane value 0 | `ConwaySloane.Mass.corrected20_spec` | proved |
| (20) | 283 | The transformation between $g$ and $h$ has identity $2\times2$ block | `ConwaySloane.Mass.corrected20_spec` | proved |
| §13, text 4 | 283–284 | $X_1 \bmod 2$ preserves the symplectic form; $Sp_{2m}(\mathbb F_2) \cong O_{2m+1}(\mathbb F_2)$ | — | out of scope (not formalized) |
| §13, text 5 | 284 | Invariants of a type I summand: $\epsilon_q = (2/\det f_q)$ and the octane value; for type II the octane value is determined by $\epsilon_q$ | `ConwaySloane.Mass.octane_typeII` | proved |
