# J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15: map to the Lean library

3rd edition, Springer, 1999 (Grundlehren der mathematischen Wissenschaften 290), Chapter 15, "On the classification of integral quadratic forms". Items: theorems and lemmas by number, displayed formulas as `(n)`, sections as `§n`.

Each row is a result of the book (numbered, or stated in the text: `41, text 17` is the 17th result stated in the running text of §41 or Chapter 41, `41, proof step 2` a step inside a proof), the Lean declaration that formalizes it, and its status. *Proved* means proved in Lean with only the standard axioms and no unproved input (the declaration's whole dependency closure); *conditional* names the unproved inputs it still assumes; *not formalized* means the library does not state it. Rows that are not results (summaries, history, plans) are omitted. The statements in the middle column are short descriptions, not quotations; read the book for the exact wording. Items of the book that the library states in a generalized form (for example over every number field) are mapped to the general statement.

Rows: 172. proved: 115; formalized as a definition, in Mathlib, or inside proofs: 50; out of scope: 7.

## §0–1. Introduction (pp. 352–354)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §1, text 3 | 353 | By Eichler's theorem (Thm. 14), genera of indefinite forms of dimension $\ge 3$ in the tables are classes when there is one spinor genus | `ConwaySloane.oneClass_of_natAbs_lt` | proved |
| (1) | 354 | If $f$ is indefinite of dimension $n$ and determinant $d$ with more than one class in its genus, then $k^{\binom n2} \mid 4^{[n/2]}d$ for some nonsquare $k \equiv 0, 1 \pmod 4$ | `ConwaySloane.theorem21` | proved |

## §2. Definitions (pp. 354–356)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (2) | 354 | Binary form with matrix $A = \begin{pmatrix}a&b\\b&c\end{pmatrix}$: $f(x) = xAx^{\mathrm t} = ax_1^2 + 2bx_1x_2 + cx_2^2$; associated bilinear form; $n$-ary forms | `gramForm`, `Cassels.Ch8Ex2.gramForm` | formalized (a definition, or used in proofs) |
| §2.1, text 1 | 355 | Two notions of integrality (as a quadratic form: $a, 2b, c \in \mathbb Z$; as a bilinear form: $a, b, c \in \mathbb Z$, "classically integral") | `isClassicallyIntegral_iff` | proved |
| §2.1, text 2 | 355 | If $f$ is integral in either sense then $2f$ is integral in the other; $f \sim g \iff 2f \sim 2g$ | `two_smul_isClassicallyIntegral` | proved |
| §2.2, text 1 | 355 | Lattice in a rational inner product space, integral basis; norm $(x,x)$ | `Lattices.Lat` | formalized (a definition, or used in proofs) |
| (3) | 355 | Binary forms with matrices $A, B$ are integrally equivalent ($f \sim g$) if $B = MAM^{\mathrm t}$ with $M$ integral, $\det M = \pm1$; proper if $\det M = 1$, improper if $-1$ | `ConwaySloane.Binary.ProperEquiv`, `ConwaySloane.Binary.ImproperEquiv`, `Siegel.IntEquiv` | formalized (a definition, or used in proofs) |
| §2.2, text 2 | 355 | A change of basis $e_i' = \sum m_{ij}e_j$ generates the same lattice iff $M^{-1}$ is integral iff $\det M = \pm1$ | `Matrix.isUnit_iff_isUnit_det` | proved |
| (4) | 356 | $n$-ary forms: (properly or improperly) integrally equivalent if $B = MAM^{\mathrm t}$ with $\det M = \pm1$ | `Siegel.IntEquiv`, `Cassels.ZpEquiv` | formalized (a definition, or used in proofs) |
| §2.2, text 3 | 356 | $d = \det A$ is an invariant of integral equivalence; the *determinant* of $f$; warning about "discriminant" | `Siegel.IntEquiv`, `hessian.det` | formalized (a definition, or used in proofs) |
| §2.2, text 4 | 356 | Equivalence over an arbitrary ring $R$ (det a unit of $R$); $x^2+y^2$ and $2z^2+2t^2$ are rationally but not integrally equivalent (explicit substitution) | `ConwaySloane.Rational.diag_one_one_equiv_two_two` | proved |
| §2.2, text 5 | 356 | Rationally equivalent forms have determinants whose ratio is a nonzero rational square | `Hanke2005.SqDet.of_isometryEquiv` | proved |

## §3. The classification of binary quadratic forms (pp. 356–366)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Thm. 1 | 356–357 | (Edwards) For $d = a_0a_1 - b_0^2$ with $-d$ not a square, the sequence (5) defined by (6)–(7) ($a_{i+1} = (b_i^2+d)/a_i$, $b_{i+1}$ the largest solution of $b_i + b_{i+1} \equiv 0 \pmod{a_{i+1}}$ with $b_{i+1}^2 + d < 0$, else the absolutely smallest) is ultimately periodic; two forms are properly equivalent iff they lead to the same cycle | `ConwaySloane.Binary.theorem1` | proved |
| (5)–(7) | 357 | The sequence of forms $a_i{}^{b_i}a_{i+1}$ and the rules (6), (7) | `ConwaySloane.Binary.isStepB_stepB` | proved |
| §3.1, text 1 | 357 | $-d$ not a square implies the $a_i$ are nonzero, so the rules are well defined | `ConwaySloane.Binary.StepInv.step` | proved |
| (8) | 357 | The cycle of $x^2 - 67y^2$ (ten reduced forms); $-x^2 + 67y^2$ gives a disjoint cycle | `ConwaySloane.Binary.example8_cycle` | proved |
| (9), (10) | 357 | A positive definite cycle is a single form ($b = 0$ or $2b = \lvert a\rvert$) or a pair $\{[a,b,c],[c,-b,a]\}$ | `ConwaySloane.Binary.definite_cycle` | proved |
| (11) | 358 | A positive definite $[a,b,c]$ is reduced iff $-a < 2b \le a \le c$, with $b \ge 0$ if $a = c$; every positive definite form is properly equivalent to a unique reduced form | `ConwaySloane.Binary.exists_reduced_pos` | proved |
| §3.2, text 1 | 358 | (11) implies $b^2 \le d/3$, so reduced forms are enumerated by factoring $d + b^2 = ac$ | `ConwaySloane.Binary.IsReducedPos.three_sq_le` | proved |
| §3.2, text 2 | 358 | Interpretation: $a$ the minimum of $f$, $c$ the least value independent of $e_1$; generalization to Minkowski reduction (§10.1) | `Reduction.IsMinkowskiReduced` | formalized (a definition, or used in proofs) |
| §3.2, text 3 | 358–359 | (11) is equivalent to the root $z = x/y$ lying in the fundamental region of $SL_2(\mathbb Z)$ (Fig. 15.2); finitely many walls in higher dimensions | `Reduction.thm_1_3` | proved |
| (12) | 359 | (Gauss §183) For $-d$ not a square, the indefinite reduced forms are those with $0 < b < \sqrt{-d} < \min(b + \lvert a\rvert, b + \lvert c\rvert)$ | `ConwaySloane.Binary.indef_d13` | proved |
| §3.3, text 1 | 359 | When $-d$ is a square the process terminates at $[a,b,0]$ with $b = \sqrt{-d}$; (Gauss §§206–210) $[a,b,0]$ and $[a',b,0]$ are properly equivalent iff $a \equiv a' \pmod{2b}$, improperly iff $aa' \equiv \gcd(a,b)^2 \pmod{2b\gcd(a,b)}$ | `ConwaySloane.Binary.gauss_square_criterion` | proved |
| §3.3, text 2 | 359 | Extended reduced forms $0^ba$, $a^b0$ ($-b < a \le b$); the cycle becomes a finite chain | `Binary.IsExtReduced`, `Binary.sqChain`, `Binary.table152sq_a_correct`, `Binary.table152sq_b_correct`, `Binary.SqTableOK.complete` | formalized (a definition, or used in proofs) |
| Table 15.1 | 360 | Reduced positive definite binary forms, $1 \le d \le 50$ | `ConwaySloane.Binary.table151_correct` | proved |
| Table 15.2 | 362–363 | Cycles of reduced indefinite binary forms, $-100 \le d \le -1$, with the notation of pp. 359–364 | `Binary.table152_correct`, `Binary.table152b_correct` | formalized (a definition, or used in proofs) |
| §3.3, text 3 | 361–364 | Reading the table: signs alternate; parentheses and braces; examples $d = -99, -37, -13, -14, -16$ | `ConwaySloane.Binary.indef_d13` | proved |
| §3.4, text 1 | 364 | Composition gives proper classes of primitive forms a group (Gauss); none for dimension $\ge 3$ | `Composition.FormClass.instCommGroup` | formalized (a definition, or used in proofs) |
| §3.4, text 2 | 364–365 | For $-d$ squarefree, $\not\equiv 1 \pmod 4$: ideals of $\mathbb Z[\sqrt{-d}]$, norm $\lvert ru - st\rvert$, principal ideals, normed ideals | `ConwaySloane.absNorm_eq_natAbs_odet` | proved |
| (13) | 365 | Multiplication of normed ideals $\mathcal I_N\mathcal J_M = (\mathcal I\mathcal J)_{NM}$; normed ideal class group | `ConwaySloane.NormedIdeal.mul_ideal`, `ConwaySloane.NormedIdeal.mul_norm`, `ConwaySloane.NormedClassGroup`, `ConwaySloane.NormedClassGroup.instCommGroup` | formalized (a definition, or used in proofs) |
| §3.4, text 3 | 365 | Proper classes of properly primitive forms of determinant $d$ correspond to normed ideal classes via $f \mapsto \langle a, -b + \sqrt{-d}\rangle_a$ | `ConwaySloane.formClass_eq_iff` | proved |
| §3.4, text 4 | 365–366 | Example: determinant $-7$, the class of $[3,2,-1]$ squares to the class of $[2,1,-3]$; the group is cyclic of order 2 | `Binary.det7_cycles`, `Binary.det7_square_cycle`, `Binary.det7_principal`, `Binary.det7_not_equiv`, `Binary.det7_ideal_square`, `Binary.det7_classes`, `Binary.Det7ClassesStatement` | formalized (a definition, or used in proofs) |
| §3.4, text 5 | 366 | Improperly equivalent forms lie in the inverse class (Cassels Ch. 14 Thm. 2.1); ambiguous forms | `Composition.isAmbiguous_iff_improper` | proved |
| §3.5, text 1 | 366 | Two binary forms are in the same genus iff their quotient is a square in the class group | `Composition.sameGenus_iff_exists_sq` | proved |
| §3.5, text 2 | 366 | (Estes–Pall) Two binary forms are in the same spinor genus iff their quotient is a fourth power | `ConwaySloane.EstesPall.estesPallStatement` | proved |
| §3.5, text 3 | 366 | §9 assumes dimension $\ge 3$; for binary forms there are no spinor operators for all sequences of unit square classes | `ConwaySloane.theorem15b_fails_dim_two` | proved |

## §4. The $p$-adic numbers (pp. 366–370)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §4, text 1 | 366–367 | Conway–Sloane's primes $-1, 2, 3, 5, \dots$; $\mathbb Q_{-1} = \mathbb Z_{-1} = \mathbb R$; $\mathbb Q^\times$ is a product of the cyclic groups generated by $-1$ and the primes | `RatPlace` | formalized (a definition, or used in proofs) |
| §4.1, text 1 | 367 | The $p$-adic metric $d_p(x,y) = p^{-k}$; examples $d_5(2,52) = 1/25$, $d_3(1/27,0) = 27$ | `ConwaySloane.padicMetric`, `ConwaySloane.padicMetric_five_two_fiftytwo`, `ConwaySloane.padicMetric_three_inv27_zero` | formalized (a definition, or used in proofs) |
| §4.1, text 2 | 367 | Product formula: $\prod_p d_p(x,y) = 1$ over all $p$ including $-1$ ($x \ne y$) | `Cassels.product_formula` | proved |
| §4.1, text 3 | 367 | $\mathbb Q_p$, $\mathbb Z_p$ as completions; $2/3$ as a 5-adic limit of $4, 34, 334, \dots$; a rational with denominator prime to $p$ is a $p$-adic integer | `Padic.norm_rat_le_one` | proved |
| §4.2, text 1 | 367 | $6$ is a 5-adic square ($1, -9, 16, -109, \dots$); for odd $p$ a unit that is a quadratic residue mod $p$ is a $p$-adic square | `Cassels.Ch4Scan.isSquare_odd_of_residue` | proved |
| §4.2, text 2 | 368 | The square classes: $\pm u$ ($p = -1$); $u_1, u_3, u_5, u_7, 2u_1, \dots, 2u_7$ ($p = 2$); $u_+, u_-, pu_+, pu_-$ ($p \ge 3$) | `HilbertLocal`, `Cassels.Ch3` | formalized (a definition, or used in proofs) |
| (14) | 368 | Extended gcd: for $n = (-1)^a2^b3^c\cdots$, $\nu = (-1)^\alpha2^\beta3^\gamma\cdots$, $(n,\nu) = (-1)^{\min(a,\alpha)}2^{\min(b,\beta)}\cdots$ | `ConwaySloane.extGcd`, `ConwaySloane.extGcd_eq`, `ConwaySloane.ExtCoprime`, `ConwaySloane.extCoprime_iff` | formalized (a definition, or used in proofs) |
| §4.3, text 1 | 368 | Two negative numbers are never coprime | `ConwaySloane.not_extCoprime_of_neg` | formalized (a definition, or used in proofs) |
| §4.3, text 2 | 368 | Extended Jacobi–Legendre symbol $\left(\frac{\nu}{n}\right)$: Legendre for odd $p$; $\left(\frac{\nu}{-1}\right) = 1$; $\left(\frac{\nu}{2}\right) = \pm1$ as $\nu \equiv \pm1, \pm3 \pmod 8$; multiplicative in $n$ | `ConwaySloane.extJacobi`, `ConwaySloane.extJacobi_eq`, `ConwaySloane.extJacobi_two`, `ConwaySloane.extJacobi_of_odd`, `ConwaySloane.jacobiTwo` | formalized (a definition, or used in proofs) |
| §4.3, text 3 | 369 | Quadratic reciprocity for the extended symbol: $\left(\frac{\nu}{n}\right) = \left(\frac{n}{\nu}\right)$ unless $n \equiv \nu \equiv -1 \pmod 4$ | `ConwaySloane.extJacobi_reciprocity`, `ConwaySloane.PrintedReciprocity`, `ConwaySloane.not_printedReciprocity` | formalized (a definition, or used in proofs) |
| §4.4, text 1 | 369 | Over a field of characteristic $\ne 2$ every form diagonalizes, starting from any vector of nonzero norm | `QuadraticForm.equivalent_weightedSumSquares` | proved |
| Thm. 2 | 369–370 | For $p \ne 2$ every $p$-adically integral form diagonalizes over $\mathbb Z_p$; for $p = 2$ it is a direct sum of $(qx)$ and $\begin{pmatrix}qa&qb\\qb&qc\end{pmatrix}$ ($q$ a power of $2$, $a, c$ even, $x, b, ac - b^2$ odd) | `Cassels.exists_canonical` | proved |
| §4.4, proof step 1 | 369 | Proof: pivot on an entry divisible by the least power of $p$; the $2\times2$ case for $p = 2$ | — | formalized (a definition, or used in proofs) |

## §5. Rational invariants of quadratic forms (pp. 370–373)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §5.1, text 1 | 370 | $p$-part and $p'$-part of $A = p^\alpha a$; $p$-adic antisquares ($p^{\mathrm{odd}}u_-$, $2^{\mathrm{odd}}u_{\pm3}$) | `ConwaySloane.unitPart`, `ConwaySloane.pExcessEntry` | formalized (a definition, or used in proofs) |
| §5.1, text 2 | 370–371 | $p$-signature of $\mathrm{diag}(p^\alpha a, \dots)$: $\sum p^\alpha + 4m$ ($p \ne 2$), $\sum a + 4m$ ($p = 2$), $m$ the number of antisquares; $(-1)$-signature = signature; the 2-signature is the oddity | `ConwaySloane.pSignature`, `ConwaySloane.pSignatureEntry`, `ConwaySloane.oddity`, `ConwaySloane.signature` | formalized (a definition, or used in proofs) |
| §5.1, text 3 | 371 | The $p$-signature mod 8 is a rational invariant | `ConwaySloane.pExcess_eq_hasse` | proved |
| (15) | 371 | Sum formula: $\sum_p p$-excess$(f) \equiv 0 \pmod 8$ | `ConwaySloane.sum_excess_eq_zero` | proved |
| §5.1, text 4 | 371 | $p$-excess $= p$-signature $- n$ ($p \ne 2$), $n - $ oddity ($p = 2$) | `ConwaySloane.pExcess_eq_pSignature_sub` | proved |
| (16) | 371 | Oddity formula: signature $+ \sum_{p \ge 3}$ $p$-excess $\equiv$ oddity $\pmod 8$ | `ConwaySloane.oddity_formula` | proved |
| §5.1, text 5 | 371 | Example $\mathrm{diag}(1,3,-3)$ | `ConwaySloane.example_diag_one_three_neg_three` | proved |
| Thm. 3 | 372 | Nonsingular forms of the same dimension are rationally equivalent iff the determinant ratio is a square and all $p$-excesses agree; (ii)' signature, oddity and $p$-excesses ($p \ge 3$) | `ConwaySloane.Rational.theorem3` | proved |
| Thm. 4 | 372 | (Weak Hasse principle) Rational forms equivalent over all $\mathbb Q_p$ are rationally equivalent | `isometric_iff_everywhere` | proved |
| Thm. 5 | 372 | (Strong Hasse principle, existence) $p$-adic forms of determinant $d$ satisfying the oddity formula come from a rational form | `Cassels.Ch6.exists_form_of_local` | proved |
| §5.2, text 2 | 373 | Remark (2): $p$-excesses are even, and divisible by 4 if $p \equiv 1 \pmod 4$ | `ConwaySloane.pExcess_even` | proved |
| (17) | 373 | Hasse–Minkowski invariant $(f)_p = \prod_{i<j}(A_i,A_j)_p$ | `RatPlace.hasseConwaySloane` | formalized (a definition, or used in proofs) |
| §5.3, text 1 | 373 | $(f)_p = \pm1$ as $p$-excess$(f) - p$-excess$(f_0) \equiv 0, 4 \pmod 8$, $f_0 = \mathrm{diag}(A_1\cdots A_n, 1, \dots, 1)$ | `ConwaySloane.hasseConwaySloane_eq_one_iff` | proved |

## §6. The invariance and completeness of the rational invariants (pp. 373–378)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §6.1, text 1 | 373 | A binary form over a field is determined by its determinant (mod squares) and any nonzero number $a$ it represents: $f \cong \mathrm{diag}(a, d/a)$ | `QuadForm` | formalized (a definition, or used in proofs) |
| Table 15.3 | 374 | $p$-adic invariants (signature, oddity, $p$-excess) vs the square classes represented by binary forms, for $p = -1, 2, \ge 3$ | `ConwaySloane.Rational.represents_two_adic_iff_oddity` | proved |
| §6.1, text 2 | 373–375 | Example: 2-adic binary forms of determinant $2u_3$: two classes, oddities $0$ and $4$; $x^2 + 6y^2$ does not represent $4^m(8k+3)$ | `ConwaySloane.not_represents_one_six` | proved |
| §6.1, text 3 | 375 | Oddity and determinant are complete invariants of 2-adic binary rational forms (likewise for other $p$): Thm. 3 for binary forms | `ConwaySloane.isometric_two_adic_iff_oddity` | proved |
| §6.1, text 4 | 375 | The isotropic form $\mathrm{diag}(A,-A)$ represents every nonzero number | `OMeara.hyperbolic_universal` | proved |
| §6.2, text 1 | 375 | Every equivalence of diagonal forms is a chain of binary equivalences | `Cassels.exists_reflTransGen_normalBasis` | proved |
| Thm. 6 | 376 | Witt cancellation over a field of characteristic $\ne 2$ | `QuadraticForm.equivalent_of_prod_equivalent_prod` | proved |
| (18) | 376 | The reflection $x \mapsto x - 2\frac{f(x,r)}{f(r,r)}r$ | `Lattices.symm` | formalized (a definition, or used in proofs) |
| §6.2, text 2 | 376 | Remark: Sylvester's law of inertia follows from Witt cancellation | `QuadraticForm.equivalent_signType_weighted_sum_squared` | proved |
| §6.2, text 3 | 376 | Definition: trivial invariants (all $p$-excesses $\equiv 0$, determinant a square) | `ConwaySloane.Rational.TrivialInvariants` | formalized (a definition, or used in proofs) |
| Thm. 7 | 376 | A form with trivial invariants is rationally equivalent to $\mathrm{diag}(\pm1, \dots, \pm1)$ | `ConwaySloane.Rational.theorem7` | proved |
| (19) | 376–377 | Thm. 7 implies Thm. 3: $f \oplus f \oplus f \oplus f$ and $g \oplus f \oplus f \oplus f$ have trivial invariants | `ConwaySloane.trivialInvariants_four` | proved |
| §6.3, text 1 | 377 | Reduction: square-free diagonal $F$ with trivial invariants, show $F \oplus \mathrm{diag}((+1)^N,(-1)^N) \sim \mathrm{diag}(\pm1,\dots)$; $p$-terms | `ConwaySloane.Rational.theorem7` | proved |
| Thm. 8 | 377 | (Replacement lemma) For $p \ge 3$, $-1 \le a, b < p$, $ab$ a square mod $p$: a $p$-term $pat$ may be replaced by $pbt$ without new primes larger than $p$ (adjoining $\pm1$ summands) | `ConwaySloane.Rational.replacement_lemma` | proved |
| (20) | 377 | $p, p \to p, pr \to pu, pur \to pu, pu$ (first of several $p$-terms arbitrary) | `ConwaySloane.Rational.diag_p_pr_equiv` | proved |
| (21) | 378 | $\mathrm{diag}(-p, p) \sim \mathrm{diag}(-1, 1)$ | `ConwaySloane.Rational.diag_neg_p_p_equiv` | proved |
| §6.3, text 2 | 378 | $p = 2$: $\mathrm{diag}(2,2) \sim \mathrm{diag}(1,1)$, $\mathrm{diag}(2,-2) \sim \mathrm{diag}(1,-1)$, $\mathrm{diag}(-2,-2) \sim \mathrm{diag}(-1,-1)$; end of the proofs of Thms. 7 and 3 | `ConwaySloane.Rational.diag_two_two_equiv` | proved |

## §7. The genus and its invariants (pp. 378–384)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §7, text 1 | 378 | Definition: same genus = equivalent over $\mathbb Z_p$ for all $p$ including $-1$ | `Siegel.SameGenus`, `Lattices.SameGenus` | formalized (a definition, or used in proofs) |
| §7, text 2 | 378 | For indefinite forms of dimension $\ge 3$ there is one class in the genus whenever $\lvert\det f\rvert < 128$; otherwise $k^{\binom n2} \mid 4^{[n/2]}\det f$ | `ConwaySloane.oneClass_of_natAbs_lt` | proved |
| §7, text 4 | 378 | $f$, $g$ are in the same genus iff $f \oplus \begin{pmatrix}0&1\\1&0\end{pmatrix} \cong g \oplus \begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $\mathbb Z$ | `ConwaySloane.sameGenus_iff_intEquiv_add_hyperbolic` | proved |
| (22) | 378 | Jordan decomposition $f = f_1 \oplus pf_p \oplus p^2f_{p^2} \oplus \cdots$ with unit forms $f_q$; Jordan constituents, scale | `Cassels.exists_canonical` | proved |
| §7.1, text 1 | 379 | $p = -1$: $f = f_1 \oplus (-1)f_{-1}$ with $f_{\pm1}$ positive definite | `QuadraticForm.equivalent_signType_weighted_sum_squared` | proved |
| §7.1, text 2 | 379 | For $p \ne 2$: the scales $q$, dimensions $n_q$ and signs $\varepsilon_q = \left(\frac{\det f_q}{p}\right)$ are a complete set of invariants (Thm. 9); for $p = -1$ only $n_\pm$ | `ConwaySloane.theorem9` | proved |
| §7.2, text 1 | 379 | $(-1)$-adic symbol $+^a-^b$; $p$-adic symbol: formal product of factors $q^{\varepsilon_qn_q}$; example (23); abbreviations | `ConwaySloane.RealSymbol`, `ConwaySloane.OddFactor`, `ConwaySloane.OddSymbol`, `ConwaySloane.Sign` | formalized (a definition, or used in proofs) |
| (23) | 379 | Example: $1^{-2}3^{+5}9^{+1}27^{-3}$ | `ConwaySloane.example23` | formalized (a definition, or used in proofs) |
| Thm. 9 | 379 | For $p \ne 2$, $f$ and $g$ are $\mathbb Z_p$-equivalent iff they have the same $n_q, \varepsilon_q$ for each $q$ (the same $p$-adic symbol) | `ConwaySloane.theorem9` | proved |
| §7.2, text 2 | 379–380 | Thm. 9 makes two assertions (complete invariants of constituents; invariants of the constituents are invariants of $f$) | `ConwaySloane.oddSymbol_eq_of_zpEquiv` | proved |
| (24) | 380 | 2-adic Jordan decomposition $f = f_1 \oplus 2f_2 \oplus 4f_4 \oplus \cdots$ | `Cassels.exists_dyadic_decomp` | proved |
| §7.3, text 1 | 380 | Invariants of $qf_q$: scale, type $S_q \in \{\mathrm I, \mathrm{II}\}$, $n_q$, $\varepsilon_q = \left(\frac{\det f_q}{2}\right)$, oddity $t_q$ | `ConwaySloane.ScaledType`, `ConwaySloane.TwoFactor` | formalized (a definition, or used in proofs) |
| §7.3, text 2 | 380 | Type I iff $qf_q$ represents an odd multiple of $q$ iff an odd diagonal entry; $t_q$ = trace mod 8 of a diagonalization (type I), $0$ (type II) | `ConwaySloane.blockSymbol`, `ConwaySloane.IsTwoSymbolOf` | formalized (a definition, or used in proofs) |
| §7.4, text 1 | 380 | 2-adic symbol: factors $q_{t_q}^{\varepsilon_qn_q}$ (type I) or $q^{\varepsilon_qn_q}$ (type II); notation $q_{\mathrm I}$, $q_{\mathrm{II}}$ | `ConwaySloane.TwoFactor`, `ConwaySloane.TwoSymbol` | formalized (a definition, or used in proofs) |
| §7.4, text 2 | 380 | Example $1^{-2}2_5^{+3}4_3^{-1}8^{+4}$ | `ConwaySloane.example74` | formalized (a definition, or used in proofs) |
| §7.5, text 1 | 381 | A form may have several Jordan decompositions with different 2-adic symbols | `ConwaySloane.twoSymbols_differ` | proved |
| Thm. 10 | 381 | $f, f'$ are 2-adically equivalent iff (i) $n_q = n'_q$, $S_q = S'_q$, and (ii) for each $m$ with $f_{2^m}$ of type II, $\sum_{q<2^m}(t_q - t'_q) \equiv 4(\min(a,m) + \min(b,m) + \cdots) \pmod 8$, where $2^a, 2^b, \dots$ are the $q$ with $\varepsilon_q \ne \varepsilon'_q$ | `ConwaySloane.TwoAdic.zpEquiv_iff_theorem10Cond` | proved |
| §7.5, text 2 | 381 | Definitions: interval, compartment (maximal run of type I), train (maximal run with no two adjacent type II) | `ConwaySloane.IsCompartment`, `ConwaySloane.IsTrain`, `ConwaySloane.IsBoundary` | formalized (a definition, or used in proofs) |
| (25) | 381 | Example symbol with compartments and trains | `ConwaySloane.not_exists_example25` | proved |
| §7.5, text 3 | 381 | (i) Oddity fusion: only the total oddity of each compartment matters | `ConwaySloane.Step`, `fuse`, `ConwaySloane.fuseStep`, `ConwaySloane.MoveEquiv` | formalized (a definition, or used in proofs) |
| §7.5, text 4 | 381–382 | (ii) Sign walking: change the signs of two terms of a train, changing the oddity of each compartment by 4 for each step in it (odd number of steps) | `ConwaySloane.moveEquiv_iff_sameInvariants` | proved |
| (26)–(28) | 382 | Example of a 3-step and a 1-step walk | `ConwaySloane.moveEquiv_26_27` | proved |
| §7.5, text 5 | 382 | Intermediate symbols with impossible constituents (e.g. $8^{-0}$) are allowed | `ConwaySloane.Step`, `ConwaySloane.MoveEquiv` | formalized (a definition, or used in proofs) |
| §7.6, text 1 | 382 | Canonical 2-adic symbol: at most one minus sign per train, on its first nonzero-dimensional form, with compartment totals; it is unique; two forms are 2-adically equivalent iff their canonical symbols agree | `ConwaySloane.moveEquiv_iff_canonical_eq` | proved |
| §7.6, text 2 | 382 | Example: canonical symbol of (25) | `ConwaySloane.moveEquiv_example25c_canonical25` | proved |
| (29) | 382–383 | Determinant condition: the product of the $\varepsilon_q$ is $\left(\frac{a}{p}\right)$, $\det f = p^\alpha a$ | `ConwaySloane.OddSymbol.DetCond`, `ConwaySloane.TwoSymbol.DetCond`, `ConwaySloane.jacobiTwo` | formalized (a definition, or used in proofs) |
| §7.7, text 1 | 383 | Signature $= r - s$; $p$-excess $\equiv \sum n_q(q-1) + 4k_p$; oddity $\equiv \sum t_q + 4k_2$ ($k_p$ = number of antisquare terms) | `ConwaySloane.pExcess_eq_pExcessJordan` | proved |
| (30) | 383 | Oddity formula in terms of the symbols | `ConwaySloane.oddity_formula` | proved |
| (31) | 383 | Existence, $p \ne 2$: if $n = 0$ or $p = -1$ then $\varepsilon = +$ | `ConwaySloane.OddFactor.Exists` | formalized (a definition, or used in proofs) |
| (32)–(35) | 383 | Existence, $p = 2$: $n = 0 \Rightarrow$ type II, $\varepsilon = +$; $n = 1$: $\varepsilon = + \Rightarrow t \equiv \pm1$, $\varepsilon = - \Rightarrow t \equiv \pm3$; $n = 2$, type I: $\varepsilon = + \Rightarrow t \equiv 0, \pm2$, $\varepsilon = - \Rightarrow t \equiv 4, \pm2$; $t \equiv n \pmod 2$; type II $\Rightarrow t \equiv 0$, $n$ odd $\Rightarrow$ type I | `ConwaySloane.TwoFactor.exists_iff_of_dim_one` | proved |
| Thm. 11 | 383 | Putative symbols satisfying (29)–(35) come from an integral form | `ConwaySloane.theorem11` | proved |
| §7.7, text 2 | 384 | In abbreviated symbols the only condition on a compartment of $\ge 2$ constituents is total oddity $\equiv$ total dimension mod 2 | `ConwaySloane.compartment_remark_counterexample` | proved |
| §7.8, text 1 | 384 | Genus symbol $\mathrm I_{r,s}(\cdots)$, $\mathrm{II}_{r,s}(\cdots)$; the omitted $1$-constituents are recovered from $\det f$, $\dim f$, type and (30) | `ConwaySloane.GenusSymbolData.scaleOne_determined` | proved |
| §7.8, made explicit | 379–384 | **Genus ↔ genus symbol** (main theorem): two nondegenerate integral forms are in the same genus iff they have the same genus symbol (dimension, determinant, $(-1)$-adic symbol, $p$-adic symbols, canonical 2-adic symbol); with Thm. 11, genera of dimension $n$ $\simeq$ symbol systems satisfying (29)–(35) up to the same symbol. The book leaves the combined statement implicit (it gives Thms. 9–11 and §7.6, then uses the symbol as a name of the genus) | `ConwaySloane.sameGenus_iff_sameSymbol` | proved |
| §7.8, text 2 | 384 | Examples $\mathrm I_{r,s}(2)$, $\mathrm{II}_{r,s}(3)$, $\mathrm I_{r,s}(3)$ | `ConwaySloane.table154_two_typeI` | proved |

## §8. Forms of small determinant and $p$-elementary forms (pp. 385–388)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §8.1, text 2 | 385 | Determinant $\pm1$: $\mathrm I_{r,s}$ exists unless $r = s = 0$; $\mathrm{II}_{r,s}$ iff $r - s \equiv 0 \pmod 8$ | `ConwaySloane.smallDet_one_typeI` | proved |
| §8.1, text 3 | 385–386 | Determinant $\pm3$: the four genera $\mathrm I_{r,s}(3^{\pm1})$, $\mathrm{II}_{r,s}(3^{\pm1})$, their oddity conditions; the failures $0$, $1_-$, $2_-$ for small $n$ | `ConwaySloane.smallDet_three_typeI` | proved |
| Thm. 12 | 386 | All genera of forms with $\lvert\det\rvert \le 11$ are as in Table 15.4 | `ConwaySloane.table154_two_typeI` | proved |
| Table 15.4 | 387 | The genera with $\lvert\det\rvert \le 11$, signatures mod 8, exceptions | `ConwaySloane.smallDet_one_typeI` | proved |
| §8.1, text 4 | 386 | For indefinite forms of dimension $\ge 3$ these genera are classes (Cor. 21) | `ConwaySloane.oneClass_of_natAbs_le_eleven` | proved |
| §8.2, text 1 | 386 | Definition: $p$-elementary ($L^*/L$ a nontrivial elementary abelian $p$-group) | `ConwaySloane.IsPElementary` | formalized (a definition, or used in proofs) |
| Thm. 13 | 386–388 | (a) $p \ge 3$: genera $\mathrm I_{r,s}(p^{\pm k})$ (all signatures) and $\mathrm{II}_{r,s}(p^{\pm k})$ ($r - s \equiv \pm2 - 2 - (p-1)k$), sign $\left(\frac{-1}{p}\right)^s$ when $k = n$; one class when indefinite, $n \ge 3$; (b) $p = 2$: Table 15.5, one class in the indefinite cases | `ConwaySloane.thm13a_typeI` | proved |
| Table 15.5 | 388 | The 2-elementary genera | `ConwaySloane.table155_I_I` | proved |

## §9. The spinor genus (pp. 388–396)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Thm. 14 | 388 | (Eichler) For indefinite forms of dimension $\ge 3$ a spinor genus is one class | `Lattices.eichler_spinorGenus_eq_class_uncond` | proved |
| §9.1, text 2 | 389 | Each genus is partitioned into spinor genera, a power of 2 in number; spinor operators act transitively | `Lattices.spinorGeneraQuot_mul_self` | proved |
| §9.2, text 1 | 389 | Forms in the same genus are rationally equivalent by a transformation with denominator prime to $2d$ | `Lattices.exists_chain_of_sameGenus` | proved |
| (36) | 389 | $[L : L \cap M] = [M : L \cap M] = r$, $r$ prime to $2d$ | `Lattices.sameProperSpinorGenus_latSMul_of_casselsI` | proved |
| Thm. 15 | 389 | (Watson Thm. 70) (a) the spinor genus of $g$ is determined by that of $f$ and $r$: $SG(g) = SG(f)\cdot\Delta(r)$; (b) for $n \ge 3$, $SG(f)\cdot\Delta(r)$ is defined for every natural $r$ prime to $2d$ | `Lattices.sameProperSpinorGenus_latSMul_of_casselsI` | proved |
| §9.2, text 2 | 389 | Remarks: (b) fails in dimension 2; for indefinite $n \ge 3$ spinor genus = class | `ConwaySloane.theorem15b_fails_dim_two` | proved |
| §9.3, text 1 | 390 | Products of reflections; spinor norm $f(v_1)\cdots f(v_k)$ mod squares; proper/improper; special orthogonal group; integral automorphisms | `Lattices.spinorNorm_symmProd` | proved |
| §9.3, text 2 | 390 | Definitions: automorphous numbers (spinor norms of proper integral automorphisms), $p$-adically automorphous | `Lattices.latSpinorNormGroup`, `Lattices.localSpinorNormGroup` | formalized (a definition, or used in proofs) |
| Thm. 16 | 390 | The spinor kernel consists of the $\Delta(r)$ with $r$ automorphous and prime to $2d$ | `ConwaySloane.not_theorem16Printed` | proved |
| Thm. 17 | 390 | The spinor kernel is generated by the $\Delta_p(A)$, $p \in \Pi$, $A$ $p$-adically automorphous | `ConwaySloane.theorem17` | proved |
| §9.4, text 1 | 390 | $\Pi$: finite set of primes containing $-1$, $2$ and the primes dividing $d$; spinor operators as sequences $(r_p)_{p\in\Pi}$ of unit square classes | `ConwaySloane.casselsCond_std` | proved |
| (37) | 390 | $\Delta(r) = (r, r, \dots)$ for $r$ prime to $\Pi$ | `ConwaySloane.deltaR` | formalized (a definition, or used in proofs) |
| (38) | 391 | $\Delta_p(A) = (p^\alpha, \dots, p^\alpha, a, p^\alpha, \dots)$ for $A = p^\alpha a$ | `ConwaySloane.deltaP`, `ConwaySloane.mk_deltaP` | formalized (a definition, or used in proofs) |
| §9.5, text 1 | 391 | Definition: $p$-adic root vector (the reflection is a $p$-adically integral automorphism) | `ConwaySloane.IsRootVector` | formalized (a definition, or used in proofs) |
| Thm. 18 | 391 | (Watson Thm. 81) A $p$-adic number is $p$-adically automorphous iff it is a product of an even number of norms of $p$-adic root vectors | `ConwaySloane.theorem18Statement_holds` | proved |
| §9.5, text 2 | 391 | Remark: for odd $p$ every $p$-adically integral automorphism is a product of integral reflections (Cassels p. 115); for $p = 2$ usually but not always (O'Meara) | `ConwaySloane.exists_rootVectors_of_mem_locStabV` | proved |
| §9.5, text 3 | 391–392 | Algorithm: list (I) diagonal entries ($p \ne 2$) or $qx$ ($p = 2$), list (II) $2qu_1, 2qu_3, 2qu_5, 2qu_7$ per type II block; automorphous numbers generated by ratios of pairs, plus (i) all units if some $f_q$ ($p \ge 3$) or $f_q \oplus f_{2q} \oplus f_{4q}$ ($p = 2$) has dimension $\ge 2$ resp. $\ge 3$, (ii) $2u_1, 2u_3, u_5, u_3, u_7$ for ratios $u_1, u_5, (1,4,16)u_{\mathrm{odd}}, (2,8)u_{1,5}, (2,8)u_{3,7}$ | `ConwaySloane.algorithm_odd` | proved |
| §9.5, text 4 | 392 | Example $\mathrm{diag}(3,16)$, $p = 2$: automorphous numbers $u_1, u_3, u_5, u_7$; $e_1 + e_2$ is a root vector of $I_2$ | `ConwaySloane.example_diag_3_16` | proved |
| §9.6, text 1 | 392 | Definition: tractable prime ($\Delta_p(u)$ in the kernel for every unit $u$); $-1$ always tractable | `ConwaySloane.IsTractable` | formalized (a definition, or used in proofs) |
| (39) | 392 | $\Delta_p(u) = (1, \dots, 1, u, 1, \dots)$ | `ConwaySloane.IsTractable` | formalized (a definition, or used in proofs) |
| §9.6, text 2 | 392 | If $f$ is indefinite then $-1$ is $(-1)$-adically automorphous and $\Delta_{-1}(-1)$ is in the kernel | `ConwaySloane.mulSingle_neg_one_mem_of_isTractable` | proved |
| §9.6, text 3 | 392 | Irrelevant primes ($p \nmid 2\det f$, odd): the automorphous numbers are exactly the unit classes | `ConwaySloane.mem_localSpinorNormGroup_std_iff_of_not_dvd` | proved |
| §9.6, text 4 | 392–393 | Example $\begin{pmatrix}2&1&0\\1&2&0\\0&0&18\end{pmatrix}$: two spinor genera, second represented by $\begin{pmatrix}6&3&0\\3&6&0\\0&0&2\end{pmatrix}$ | `ConwaySloane.example96_two_spinorGenera` | proved |
| Thm. 19 | 393 | If $f$ is indefinite with more than one class in its genus, then for some $p$ (possibly $-1$) $f$ is $p$-adically diagonalizable with diagonal entries involving distinct powers of $p$ | `ConwaySloane.theorem19` | proved |
| Thm. 20 | 393–394 | For indefinite $f$: (a) $p \ge 3$ intractable $\Rightarrow p^{\binom n2} \mid d$ (40); (b) $p \equiv 3 \pmod 4$ is not the only intractable prime; (c) 2 intractable $\Rightarrow 4^{\binom n2} \mid 4^{[n/2]}d$ (41); (d) 2 the only intractable prime $\Rightarrow 8^{\binom n2} \mid 4^{[n/2]}d$ (42) | `ConwaySloane.theorem20a` | proved |
| (40)–(42) | 393–394 | The divisibilities of Thm. 20 | `ConwaySloane.theorem20a` | proved |
| Thm. 21 | 395 | Indefinite, more than one class in the genus $\Rightarrow k^{\binom n2} \mid 4^{[n/2]}d$ for some nonsquare $k \equiv 0, 1 \pmod 4$ (43) | `ConwaySloane.theorem21` | proved |
| Cor. 22 | 395 | Indefinite with more than one class $\Rightarrow \lvert d\rvert \ge d_0(n)$: $17$ ($n = 2$), $128$ ($n = 3$), $5^{\binom n2}$ ($n$ even $\ge 4$), $2\cdot5^{\binom n2}$ ($n$ odd $\ge 5$) | `ConwaySloane.corollary22_uncond` | proved |
| (44) | 396 | The forms $\begin{pmatrix}2&3\\3&2\end{pmatrix} \oplus 5^2(\cdots) \oplus \cdots$ attaining $d_0$ | `ConwaySloane.natAbs_det_A44` | proved |
| §9.7, text 3 | 396 | $\begin{pmatrix}2&3\\3&-4\end{pmatrix}$, $\begin{pmatrix}-2&3\\3&4\end{pmatrix}$ are in distinct classes of the genus $\mathrm{II}_{1,1}(17)$ | `ConwaySloane.example17_intEquiv` | proved |

## §10. The classification of positive definite forms (pp. 396–402)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (45) | 396 | Minkowski reduced: $f(e_t) \le f(v)$ for all $v$ such that $e_1, \dots, e_{t-1}, v$ extends to an integral basis | `Reduction.IsMinkowskiReduced`, `Reduction.ExtendsBasis` | formalized (a definition, or used in proofs) |
| §10.1, text 1 | 396 | Only finitely many of the inequalities are needed (Cassels p. 256, Thm. 1.3) | `Reduction.thm_1_3` | proved |
| (46) | 396 | $0 < a_{11} \le a_{22} \le \cdots \le a_{nn}$ | `Reduction.IsMinkowskiReduced.diag_mono` | proved |
| §10.1, text 2 | 396 | With $v = e_t - \sum_{s\in S}\epsilon_se_s$: $2\lvert\sum\epsilon_sa_{st} - \sum_{r<s}\epsilon_r\epsilon_sa_{rs}\rvert \le \sum a_{ss}$ | `Binary.minkowski_ineq`, `Binary.minkowski_ineq_neg`, `Binary.minkowski_ineq_abs_of_card_le_one` | formalized (a definition, or used in proofs) |
| (47)–(49) | 397 | The cases $S = \{s\}, \{r,s\}, \{q,r,s\}$ | `ConwaySloane.Tern.IsReducedPrinted`, `ConwaySloane.Tern.IsMinkowski`, `ConwaySloane.Tern.isMinkowskiReduced_iff`, `ConwaySloane.counterexample_printed48` | formalized (a definition, or used in proofs) |
| §10.1, text 3 | 397 | (Minkowski; Cassels Lemma 1.2) for $n \le 4$ coefficients $0, \pm1$ suffice: (46), (46)–(47), (46)–(48), (46)–(49) define reduction for $n = 1, 2, 3, 4$ | `Reduction.lemma_1_2` | proved |
| §10.1, text 5 | 397 | Finitely many classes of given determinant (Cassels p. 256, Thm. 1.1) | `Reduction.finite_intEquiv_isMinkowskiReduced` | proved |
| Table 15.6 | 398 | Indecomposable reduced positive definite ternary forms, $d \le 50$ | `ConwaySloane.table156`, `ConwaySloane.table156_correct` | formalized (a definition, or used in proofs) |
| Table 15.7 | 399 | Indecomposable indefinite ternary forms, $\lvert d\rvert \le 100$ | `Examples.table157`, `Examples.table157_correct` | formalized (a definition, or used in proofs) |
| §10.2, text 1 | 399 | Lattices generated by norm 1 and 2 vectors are sums of $I_n, A_n, D_n, E_6, E_7, E_8$ | — | out of scope (not formalized) |
| Thm. 23 | 399 | Positive definite forms of determinant 2 (dimension $\le 18$) and 3 (dimension $\le 17$) are as in Tables 15.8, 15.9 | — | out of scope (not formalized) |
| §10.3, proof step 1 | 399–400 | Determinant 2: $L_n = w^\perp$ for a norm-2 vector $w$ in a unimodular $L_{n+1}$; cases (a), (b) | — | out of scope (not formalized) |
| §10.3, proof step 2 | 401 | Determinant 3: $v\cdot v \equiv \pm1/3$; $A_2^\perp$ or $\langle3\rangle^\perp$; cases (a)–(e) | — | out of scope (not formalized) |
| Table 15.8 | 400 | Lattices of determinant 2, minimal norm $\ge 2$, dimension $\le 18$ | — | out of scope (not formalized) |
| Table 15.9 | 402 | Lattices of determinant 3, minimal norm $\ge 2$, dimension $\le 17$ | — | out of scope (not formalized) |

## §11. Computational complexity (pp. 402–405)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| §11, text 3 | 403 | For positive definite forms of fixed dimension, (C1)–(C4), (G1)–(G4) are solvable in time polynomial in $d$ (Minkowski reduction) | — | out of scope (not formalized) |
| §11, text 5 | 403–404 | Dickson–Ross example: $x^2 - 3y^2 - 2yz - 23z^2$ and $x^2 - 7y^2 - 6yz - 11z^2$ are equivalent | `Siegel.ex2_properIntEquiv` | proved |
| (50) | 404 | The unimodular matrix $M$ transforming one Dickson–Ross form into the other | `ConwaySloane.dicksonRossM_det`, `ConwaySloane.dicksonRoss_equiv`, `ConwaySloane.dicksonRoss_poly` | formalized (a definition, or used in proofs) |
| §11, text 7 | 404–405 | $\mathrm{diag}(-1,64,2)$ has a genus $\mathrm I_{2,1}(2\times64)$ of two classes; (51) gives a representative of the second | `ConwaySloane.example11_exactly_two_classes` | proved |
| (51) | 404 | The ternary forms $\begin{pmatrix}-1&1&0\\1&63&0\\0&0&2\end{pmatrix}$ and $\begin{pmatrix}-9&1&0\\1&7&0\\0&0&2\end{pmatrix}$ | `ConwaySloane.example11_exactly_two_classes` | proved |
