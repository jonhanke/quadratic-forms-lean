# O. T. O'Meara, *Introduction to Quadratic Forms*: map to the Lean library

Springer, 1963 (Grundlehren der mathematischen Wissenschaften 117). Items are numbered as in the book: `93:28` is the statement 28 of §93.

Each row is a result of the book (numbered, or stated in the text: `41, text 17` is the 17th result stated in the running text of §41 or Chapter 41, `41, proof step 2` a step inside a proof), the Lean declaration that formalizes it, and its status. *Proved* means proved in Lean with only the standard axioms and no unproved input (the declaration's whole dependency closure); *conditional* names the unproved inputs it still assumes; *not formalized* means the library does not state it. Rows that are not results (summaries, history, plans) are omitted. The statements in the middle column are short descriptions, not quotations; read the book for the exact wording. Items of the book that the library states in a generalized form (for example over every number field) are mapped to the general statement.

Rows: 672. proved: 571; formalized as a definition, in Mathlib, or inside proofs: 100; out of scope: 1.

## Chapter I. Valuated Fields

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 11, text 1 | 2 | A finite field has only the trivial valuation | `OMeara.eq_one_of_finite` | proved |
| 11:1 | 4 | A valuation is non-archimedean if and only if it is bounded on the natural integers of $F$ | `OMeara.isNonarchimedean_iff_natCast_bounded` | proved |
| 11:2 | 4 | Principle of Domination: $\lvert\alpha_1 + \dots + \alpha_n\rvert = \lvert\alpha_1\rvert$ if $\lvert\alpha_\lambda\rvert < \lvert\alpha_1\rvert$ for $\lambda > 1$ | `OMeara.domination_sum` | proved |
| 11:2a | 5 | The same for a convergent series | `OMeara.domination_tsum` | proved |
| 11:3 | 5 | A valuation on an algebraic extension that is trivial on $F$ is trivial | `OMeara.eq_one_of_trivial_on_algebraic` | proved |
| 11:4 | 5 | Equivalent valuations: same topology $\iff$ ($\lvert\alpha\rvert_1 < 1 \iff \lvert\alpha\rvert_2 < 1$) $\iff \lvert\ \rvert_1^{\varrho} = \lvert\ \rvert_2$ | `OMeara.equivalent_valuations_tfae` | proved |
| 11:4a | 6 | If $\lvert\ \rvert_1$ is non-trivial and $\lvert\alpha\rvert_1 < 1 \Rightarrow \lvert\alpha\rvert_2 < 1$, the valuations are equivalent | `OMeara.sameTopology_of_lt_one_imp` | proved |
| 11:4b | 6 | The trivial valuation is equivalent to itself alone | `OMeara.isEquiv_trivial_iff` | proved |
| 11:5 | 6 | Equivalent valuations of $E$ inducing the same non-trivial valuation on a subfield are equal | `OMeara.eq_of_isEquiv_of_eq_on_subfield` | proved |
| 11, text 2 | 6–7 | $\lvert\ \rvert^{\varrho}$ is a valuation for $0 < \varrho \le 1$ (for every $\varrho > 0$ if non-archimedean) | `OMeara.rpowAbsLeOne`, `OMeara.rpowAbs` | formalized (a definition, or used in proofs) |
| 11:6 | 7 | A topological isomorphism $F \to G$ carries the spot $\mathfrak p$ to $\mathfrak q$ ($\mathfrak q = \mathfrak p^{\sigma}$), and each valuation in $\mathfrak p$ has one in $\mathfrak q$ making $\sigma$ analytic | `OMeara.topologicalIso_spot` | proved |
| 11:7 | 8 | For finitely many inequivalent non-trivial valuations there is $\alpha$ with $\lvert\alpha\rvert_1 > 1$, $\lvert\alpha\rvert_\lambda < 1$ ($\lambda \ge 2$) | `OMeara.exists_one_lt_lt_one` | proved |
| 11:8 | 8 | Weak Approximation Theorem | `OMeara.weak_approximation` | proved |
| 11:9 | 9 | Over a complete non-archimedean field every series whose terms tend to $0$ converges | `OMeara.summable_of_tendsto_zero` | proved |
| 11:10 | 9 | A complete field is its own completion, and has no other | `OMeara.isCompletion_self` | proved |
| 11:11 | 9 | A field is complete at its trivial spot | `OMeara.completeSpace_trivial` | proved |
| 11:12 | 10 | Completeness is invariant under topological isomorphism | `OMeara.completeSpace_iff_of_isTopologicalIso` | proved |
| 11:13 | 10 | Every field has a completion at each spot | `OMeara.exists_isCompletion` | proved |
| 11:14 | 10 | A topological isomorphism into a complete field prolongs uniquely to the completion | `OMeara.exists_prolongation` | proved |
| 11:15 | 11 | Two completions at the same spot are uniquely topologically isomorphic over $F$ | `OMeara.exists_unique_equiv_of_isCompletion` | proved |
| 11:16 | 11–12 | Notation $F_{\mathfrak p}$, $E_{\mathfrak P}$, $F_{\mathfrak P}$ (closure of $F$ in $E_{\mathfrak P}$) | `AbsoluteValue.Completion`, `AbsoluteValue.Completion.algebraOfLiesOver` | in Mathlib |
| 11:17 | 12 | All norms on a finite-dimensional space over a complete field define the same topology, which is complete | `OMeara.norms_equivalent` | proved |
| 11:18 | 13 | For $E/F$ finite and $F$ complete at $\mathfrak p$: $E$ is complete at $\mathfrak P$, and $\mathfrak P$ is the only spot dividing $\mathfrak p$ | `OMeara.extension_unique` | proved |
| 11:18a | 13 | An isomorphism topological on $F$ is topological on $E$ | `OMeara.isEquiv_spectralAbs_of_isEquiv_on_base` | proved |
| 11:19 | 14 | $E_{\mathfrak P} = EF_{\mathfrak P}$ and $[E_{\mathfrak P} : F_{\mathfrak P}] \le [E:F]$ | `OMeara.compositum_completion` | proved |
| 12:1 | 14 | $\mathbb Q$ has exactly one archimedean spot; its valuations are $\lvert\ \rvert_\infty^{\varrho}$, $0 < \varrho \le 1$ | `OMeara.rat_archimedean_exists_rpow` | proved |
| 12:2 | 15 | Over a complete archimedean field, $1 + \alpha$ is a square when $4\lvert\alpha\rvert < \lvert 4\rvert$ | `OMeara.isSquare_one_add` | proved |
| 12:3 | 16 | A complete archimedean valuation prolongs to $F(i)$, $i^2 = -1$ | `OMeara.exists_prolongation_adjoin_sqrt_neg_one` | proved |
| 12:4 | 17 | A complete archimedean field is topologically isomorphic to $\mathbb R$ or $\mathbb C$ | `OMeara.complete_archimedean_isTopologicalIso` | proved |
| 12:5 | 19 | The ordinary absolute value at an archimedean spot ($\lvert m\rvert = m$) exists and is unique | `OMeara.exists_ordinary_rpow` | proved |
| 12:6 | 19 | Every valuation of an archimedean spot is $\lvert\ \rvert^{\varrho}$, $0 < \varrho \le 1$, with $\lvert\ \rvert$ ordinary | `OMeara.ordinary_rpow` | proved |
| 12:7 | 19 | For $\mathfrak P \mid \mathfrak p$ with $\mathfrak p$ non-trivial, restriction is a bijection of the valuations in $\mathfrak P$ onto those in $\mathfrak p$ | `OMeara.under_bijective` | proved |
| 12:8 | 19 | Real and complex spots | `OMeara.IsRealSpot`, `OMeara.IsComplexSpot` | formalized (a definition, or used in proofs) |
| 12:9 | 19 | The normalized valuation at an archimedean spot | `OMeara.normalizedSpotAbs` | formalized (a definition, or used in proofs) |
| 12:10 | 19 | Triangle law for the normalized valuation (factor $2^{r-1}$ at complex spots) | `OMeara.normalizedSpotAbs_add_le_of_real` | proved |
| 12:11 | 20 | Positive and negative elements at a real spot | `OMeara.IsPositiveElt`, `OMeara.IsNegativeElt` | formalized (a definition, or used in proofs) |
| 12:12 | 20 | At a real spot $F_{\mathfrak p} = -\dot F_{\mathfrak p}^2 \cup 0 \cup \dot F_{\mathfrak p}^2$; positive elements form a subgroup | `OMeara.isPositiveElt_iff_pos` | proved |
| 12:13 | 20 | The prime field of characteristic $0$ has exactly one archimedean spot; it is real; the positive elements are the $m/n$ | `OMeara.rat_archimedean_real_spot` | proved |
| 13, text 1 | 21 | $\mathfrak m(\mathfrak p)$ is the largest proper ideal of $\mathfrak o(\mathfrak p)$; residue class fields exist | `OMeara.maximalIdealOf_isMaximal` | proved |
| 13:1 | 21 | Example of the notation $F_{\mathfrak p}(\mathfrak p)$ | `OMeara.residue_completion` | proved |
| 13:2 | 21 | $\chi(\bar F(\mathfrak p)) = \chi(F)$ when $\chi(F) \ne 0$ | `OMeara.residue_char` | proved |
| 13:3 | 21 | Congruences modulo an additive subgroup | `AddSubgroup.quotient`, `Submodule.Quotient` | in Mathlib |
| 13:4 | 22 | (1) $\lvert F\rvert = \lvert F_{\mathfrak p}\rvert$; (2) $(\lvert E_{\mathfrak P}\rvert : \lvert F_{\mathfrak P}\rvert) = (\lvert E\rvert : \lvert F\rvert)$; (3) the index does not depend on the valuation | `OMeara.valueGroup_completion` | proved |
| 13:5 | 23 | (1) $\bar F(\mathfrak p) = \bar F_{\mathfrak p}(\mathfrak p)$; (2) $[E_{\mathfrak P}(\mathfrak P) : F_{\mathfrak P}(\mathfrak P)] = [E(\mathfrak P) : F(\mathfrak P)]$ | `OMeara.residue_completion` | proved |
| 13:6 | 24 | $e(\mathfrak P|\mathfrak p)f(\mathfrak P|\mathfrak p) \le n$ | `OMeara.ramificationIndexAbs_mul_inertiaDegAbs_le` | proved |
| 13:7 | 26 | Monic irreducible factors of an integral monic polynomial are integral | `OMeara.monic_factor_integral` | proved |
| 13:8 | 26 | Hensel's lemma (lifting a coprime factorization) | `LocalDensity.DVR.exists_eval_eq_of_dvd` | proved |
| 13:9 | 28 | Reducibility Criterion: $f$ is reducible if $0 < \lvert a_0\rvert < \lvert f\rvert = \lvert a_i\rvert$ for some $i < n$ | `OMeara.not_irreducible_of_norm_coeff_lt` | proved |
| 14:1 | 28 | A complete valuation has a unique prolongation to a finite extension, $\lvert\alpha\rvert = \lvert N_{E/F}\alpha\rvert^{1/n}$, complete | `OMeara.exists_unique_prolongation` | proved |
| 15, text 1 | 30–31 | Every spot of $F$ is divisible by at least one and at most $n$ spots of $E$ | `OMeara.exists_under_eq` | proved |
| 15:1 | 31 | $(\sigma E)_{\mathfrak P} = F_{\mathfrak p}(\sigma\theta)$ | `OMeara.closure_range_eq_adjoin` | proved |
| 15:2 | 31 | $\mathfrak P_\sigma = \mathfrak P_\tau$ if and only if $\sigma\theta$, $\tau\theta$ are conjugate over $F_{\mathfrak p}$ | `OMeara.isEquiv_comp_iff_minpoly_eq` | proved |
| 15:3 | 32 | $\sum_{\mathfrak P|\mathfrak p} n(\mathfrak P|\mathfrak p) = n$ and $\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}\alpha = N_{E/F}\alpha$ | `OMeara.sum_localDegree_eq_finrank` | proved |
| 15:4 | 33 | The norm is continuous for any topology finer than all $\mathfrak P$-adic ones | `OMeara.continuous_norm_of_le` | proved |
| 15:4a | 33 | $\varepsilon$–$\delta$ continuity of the norm at the spots $\mathfrak P \mid \mathfrak p$ | `OMeara.exists_norm_sub_lt` | proved |
| 15:5 | 33 | At a real spot, $(-1)^r N_{E/F}\alpha$ is positive when $\alpha$ is negative at exactly $r$ real $\mathfrak P$ | `OMeara.isPositiveElt_norm` | proved |
| 15:6 | 34 | $\lvert\alpha\rvert_{\mathfrak P} \le 1$ for all $\mathfrak P \mid \mathfrak p$ implies $\lvert N\alpha\rvert_{\mathfrak p} \le 1$, with equality iff all are $1$ | `OMeara.norm_le_one_of_forall_le_one` | proved |
| 15:7 | 34 | The spots $\mathfrak P \mid \mathfrak p$ correspond to the irreducible factors of $\operatorname{irr}(x,\theta,F)$ over $F_{\mathfrak p}$; local degree = degree of the factor | `OMeara.spots_equiv_factors` | proved |
| 15:8 | 35 | $\mathbb Q(\sqrt a)$ at $\infty$: two spots of local degree 1 ($a > 0$) or one of local degree 2 ($a < 0$) | `OMeara.spots_sqrt` | proved |
| 15:9 | 35 | $\mathbb Q(\sqrt[3]2)$ at $\infty$: one real spot of local degree 1 and one complex spot of local degree 2 | `OMeara.spots_cbrt_two` | proved |
| 15:10 | 36 | Abelian $E/F$: $n(\mathfrak P|\mathfrak p) = [E:Z]$ for all $\mathfrak P$; $Z_{\mathfrak P} = F_{\mathfrak P}$, $Z = F_{\mathfrak P} \cap E$; $e$, $f$ independent of $\mathfrak P$ | `OMeara.localDegree_eq_card_decompositionGroupAbs` | proved |
| 15:10a | 37 | For $d \mid n_{\mathfrak p}$ there is $Z \subseteq H \subseteq E$ with local degree $d$ | `OMeara.exists_intermediateField_localDegree_eq` | proved |
| 16, text 1 | 37–38 | A discrete valuation is non-trivial and non-archimedean; discreteness depends only on the spot | `OMeara.IsDiscreteAbs.isNonarchimedean` | proved |
| 16:1 | 38 | For $E/F$ finite, $\mathfrak P$ is discrete if and only if $\mathfrak p$ is | `OMeara.isDiscreteAbs_iff_under` | proved |
| 16, text 2 | 38 | Prime elements: they exist, are the elements whose value generates $\lvert F\rvert$, differ by units; $\mathfrak m(\mathfrak p) = \pi\mathfrak o(\mathfrak p)$; $\alpha = \varepsilon\pi^{\nu}$ and the rules for $\operatorname{ord}$ | `OMeara.isPrimeElt_iff` | proved |
| 16:2 | 38 | $\operatorname{ord}_{\mathfrak P}\alpha = e(\mathfrak P|\mathfrak p)\operatorname{ord}_{\mathfrak p}\alpha$ for $\alpha \in F$ | `OMeara.ordAbs_algebraMap` | proved |
| 16:3 | 39 | Unique expansion $\alpha = \sum_{\nu \ge m} c_\nu\pi_\nu$ with $c_\nu$ in a representative set | `OMeara.exists_unique_expansion` | proved |
| 16:4 | 40 | $e f = n$ for complete discrete spots | `OMeara.ramificationIndexAbs_mul_inertiaDegAbs_eq` | proved |
| 11.d1 | 1 | Triangle law ($\lvert a+b\rvert \le \lvert a\rvert + \lvert b\rvert$) and strong triangle law ($\lvert a+b\rvert \le \max(\lvert a\rvert,\lvert b\rvert)$); a valuation satisfying the strong triangle law is non-archimedean, otherwise archimedean | `AbsoluteValue`, `IsNonarchimedean` | in Mathlib |
| 11.d2 | 3, 7 | Carrying a valuation (respectively a spot) from a field $F$ to a field $F'$ along an isomorphism | `OMeara.isTopologicalIso_iff_isEquiv_carryAbs` | proved |
| 11.d3 | 7 | A spot is an equivalence class of valuations; the spot containing the trivial valuation (and then no other) is the trivial spot | `AbsoluteValue.IsEquiv`, `AbsoluteValue.trivial`, `OMeara.SameTopology` | in Mathlib |
| 11.d4 | 7 | A spot $\mathfrak P$ on an extension $E$ induces a unique spot $\mathfrak p$ on $F$; one says $\mathfrak P$ divides $\mathfrak p$ and writes $\mathfrak P \mid \mathfrak p$ | `OMeara.under_isEquiv` | proved |
| 11.d5 | 8 | A set of spots $T$ divides a set $S$ ($T \mid S$) when each spot of $T$ induces a spot of $S$; $T$ fully divides $S$ ($T \parallel S$) when $T$ is the largest set of spots on $E$ dividing $S$ | `OMeara.SetDivides`, `OMeara.FullyDivides`, `OMeara.FullyDivides.setDivides` | formalized (a definition, or used in proofs) |
| 11.d6 | 9 | $F$ is complete at a spot $\mathfrak p$ when some (equivalently each) valuation in $\mathfrak p$ is complete | `OMeara.completeSpace_of_isEquiv` | proved |
| 11.d7 | 9 | A completion of $F$ at $\mathfrak p$: a field complete at a spot dividing $\mathfrak p$ in which $F$ is dense | `OMeara.IsCompletion` | formalized (a definition, or used in proofs) |
| 13.d1 | 20–21 | For a non-archimedean spot $\mathfrak p$: the integers $\mathfrak o(\mathfrak p) = \{a : \lvert a\rvert_{\mathfrak p} \le 1\}$ (ring of integers, valuation ring), the group of units $\mathfrak u(\mathfrak p) = \{a : \lvert a\rvert_{\mathfrak p} = 1\}$, the maximal ideal $\mathfrak m(\mathfrak p) = \{a : \lvert a\rvert_{\mathfrak p} < 1\}$; a residue class field $(\varphi, H)$ | `OMeara.integers`, `OMeara.maximalIdealOf`, `OMeara.IsResidueClassField` | formalized (a definition, or used in proofs) |
| 13.d2 | 22–24 | The ramification index $e(\mathfrak P|\mathfrak p) = (\lvert E\rvert : \lvert F\rvert)$; the residue class field of $F$ obtained by natural restriction; the degree of inertia $f(\mathfrak P|\mathfrak p) = [E(\mathfrak P) : F(\mathfrak P)]$ | `OMeara.inertiaDegAbs_congr` | proved |
| 13.d3 | 25 | A function on a subring $Z$ of $F$ satisfying the valuation axioms prolongs uniquely to a valuation on the quotient field $F$ of $Z$ by $\lvert a/b\rvert = \lvert a\rvert/\lvert b\rvert$ | `OMeara.exists_unique_extend_of_isFractionRing` | proved |
| 13.d4 | 25 | A polynomial over a non-archimedean field $F$ is integral when all its coefficients are integers of $F$; the Gauss valuation on $F(x)$ | `Polynomial.gaussNorm`, `Polynomial.gaussNorm_mul` | in Mathlib |
| 15.d1 | 31–32 | Local degree $n(\mathfrak P|\mathfrak p) = [E_{\mathfrak P} : F_{\mathfrak P}]$; local norm $N_{\mathfrak P|\mathfrak p}\colon E_{\mathfrak P} \to F_{\mathfrak p}$ and local trace $S_{\mathfrak P\mid\mathfrak p}$ | `OMeara.localDegree`, `OMeara.localNorm` | formalized (a definition, or used in proofs) |
| 15.d2 | 35 | A finite extension is abelian when it is Galois (normal and separable) with abelian Galois group | `IsGalois` | in Mathlib |
| 15.d3 | 35 | The decomposition group of $E/F$ at $\mathfrak P \mid \mathfrak p$ is the subgroup of the Galois group fixing the spot $\mathfrak P$; the decomposition field is its fixed field | `OMeara.decompositionGroupAbs` | formalized (a definition, or used in proofs) |
| 16.d1 | 37 | A valuation is discrete when it is non-trivial and its value group is a discrete infinite cyclic subgroup of the positive reals; a prime spot is discrete when it contains a discrete valuation | `OMeara.IsDiscreteAbs` | formalized (a definition, or used in proofs) |
| 16.d2 | 38 | A prime element of the integral domain $\mathfrak o(\mathfrak p)$ is a non-unit $x$ such that in every factorization $x = \alpha\beta$ one of $\alpha,\beta$ is a unit; the order $\operatorname{ord}_{\mathfrak p}\alpha$; a representative set of the residue class field | `OMeara.IsPrimeElt`, `OMeara.ordAbs`, `OMeara.IsRepresentativeSet` | formalized (a definition, or used in proofs) |

## Chapter II. Dedekind Theory of Ideals

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 21:1 | 42 | The set of all non-archimedean spots of the field of rational numbers is a Dedekind set | `OMeara.rat_dedekindAxioms` | proved |
| 21, text 1 | 42 | The axioms hold for the primes of a Dedekind domain; a single discrete spot, and a finite set satisfying (D1), is Dedekind | `OMeara.dedekindAxioms` | proved |
| 21:2 | 42 | Strong Approximation Theorem | `OMeara.strong_approximation` | proved |
| 21:2a | 43 | Prescribed values $\lvert A\rvert_{\mathfrak p} = \xi_{\mathfrak p}$ on $T$ and $\le \xi_{\mathfrak p}$ elsewhere | `OMeara.exists_valuation_eq_le` | proved |
| 21:3 | 43 | $\mathfrak o(S) \ne F$ and $F$ is the quotient field of $\mathfrak o(S)$ | `OMeara.ringOfIntegers_eq_and_isFractionRing` | proved |
| 21:4 | 44 | $\mathfrak o(\mathfrak p)$ is the closure of $\mathfrak o(S)$; $\mathfrak o(S)$ contains a representative set of the residue class field | `OMeara.valuation_le_one_iff_mem_closure` | proved |
| 22, text 1 | 45–46 | $\lvert\mathfrak a\rvert_{\mathfrak p} = \max_{\alpha \in \mathfrak a}\lvert\alpha\rvert_{\mathfrak p}$ is attained; rules for $\lvert\ \rvert_{\mathfrak p}$ on ideals ($\lvert\mathfrak a\cap\mathfrak b\rvert_{\mathfrak p} = \min$) | `OMeara.isGreatest_valuation_image` | proved |
| 22:1 | 46 | $\mathfrak a = \{\alpha : \lvert\alpha\rvert_{\mathfrak p} \le \lvert\mathfrak a\rvert_{\mathfrak p}\ \forall\mathfrak p\}$ and $\mathfrak a \subseteq \mathfrak b \iff \lvert\mathfrak a\rvert_{\mathfrak p} \le \lvert\mathfrak b\rvert_{\mathfrak p}$ | `OMeara.mem_iff_forall_valuation_le_idealAbs` | proved |
| 22:2 | 47 | Local ideals with almost all values $1$ glue to a fractional ideal | `OMeara.exists_fractionalIdeal_of_local` | proved |
| 22:3 | 47 | Identities $\mathfrak a(\mathfrak b + \mathfrak c) = \mathfrak a\mathfrak b + \mathfrak a\mathfrak c$, … , $\mathfrak a^n = \mathfrak b^n \Rightarrow \mathfrak a = \mathfrak b$ | `OMeara.mul_sup_eq` | proved |
| 22, text 2 | 47 | The fractional ideals form a group | `FractionalIdeal`, `Units`, `FractionalIdeal.mul_inv_cancel` | in Mathlib |
| 22:4 | 48 | $(\mathfrak a + \mathfrak b)^{-1} = \mathfrak a^{-1} \cap \mathfrak b^{-1}$ and $(\mathfrak a \cap \mathfrak b)^{-1} = \mathfrak a^{-1} + \mathfrak b^{-1}$ | `OMeara.inv_sup_eq` | proved |
| 22:5 | 48 | For fractional ideals $\mathfrak a,\mathfrak b,\mathfrak c$ there are non-zero $\alpha,\beta \in F$ with $\mathfrak c = \alpha\mathfrak a + \beta\mathfrak b$ (and $\beta$ can be any element with $\beta\mathfrak b \subseteq \mathfrak c$) | `OMeara.exists_eq_smul_add_smul` | proved |
| 22:5a | 48 | Every fractional ideal has the form $\alpha\mathfrak o + \beta\mathfrak o$ with $\alpha,\beta \in F$ | `OMeara.exists_eq_span_pair` | proved |
| 22:5b | 48 | Every fractional ideal is a finitely generated $\mathfrak o$-module | `OMeara.fractionalIdeal_fg` | proved |
| 22:5c | 48 | If $\mathfrak b$ is integral, some integral ideal $\mathfrak a'$ in the ideal class of $\mathfrak a$ is relatively prime to $\mathfrak b$ | `OMeara.exists_coprime_in_class` | proved |
| 22:6 | 49 | For $0 \ne \mathfrak a \subsetneq \mathfrak o$: $\mathfrak a = \mathfrak o \cap \mathfrak m(\mathfrak p)$ for some $\mathfrak p$ $\iff$ prime $\iff$ indecomposable $\iff$ maximal | `OMeara.tfae_prime_indecomposable_maximal` | proved |
| 22:7 | 49 | Unique Factorization Theorem: the fractional ideals form a free abelian group with the prime ideals as a base | `OMeara.existsUnique_prime_factorization` | proved |
| 22:8 | 50 | The order $\operatorname{ord}_{\mathfrak p}\mathfrak a$; $\operatorname{ord}_{\mathfrak p}\mathfrak a\mathfrak b = \operatorname{ord}_{\mathfrak p}\mathfrak a + \operatorname{ord}_{\mathfrak p}\mathfrak b$, $\lvert\mathfrak a\rvert_{\mathfrak p} = \lvert\pi\rvert_{\mathfrak p}^{\operatorname{ord}_{\mathfrak p}\mathfrak a}$ | `OMeara.ord_mul` | proved |
| 22:9 | 50 | For fractional ideals $\mathfrak a,\mathfrak b,\mathfrak r_1,\mathfrak r_2$ there are non-zero $\alpha,\beta$ with $\alpha\mathfrak a\mathfrak r_1 + \beta\mathfrak b\mathfrak r_2 = \mathfrak r_1 + \mathfrak r_2$ | `OMeara.exists_smul_mul_add_smul_mul_eq` | proved |
| 22, text 3 | 51 | §22D: $\mathfrak o/\mathfrak p \cong F(\mathfrak p)$; $\mathfrak a/\mathfrak b \cong \mathfrak o/\mathfrak a^{-1}\mathfrak b$; $\mathfrak o/\mathfrak a\mathfrak b \cong \mathfrak o/\mathfrak a \oplus \mathfrak o/\mathfrak b$ for coprime $\mathfrak a, \mathfrak b$ | `Ideal.quotientMulEquivQuotientProd`, `IsDedekindDomain.HeightOneSpectrum`, `OMeara.quotientOneEquiv` | in Mathlib |
| 22, text 4 | 51 | §22E: for a single discrete spot every fractional ideal is $\pi^{\nu}\mathfrak o$ | `IsDiscreteValuationRing`, `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible` | in Mathlib |
| 22:10 | 52 | Dedekind sets $S$, $T$ with $\mathfrak o(S) = \mathfrak o(T)$ are equal (the underlying set of spots of a Dedekind domain is unique) | `OMeara.existsUnique_heightOneSpectrum_isEquiv` | proved |
| 23:1 | 52 | For a finite separable extension, $T \mid S$ and $S$ Dedekind imply $T$ Dedekind | `OMeara.integralClosure_dedekindAxioms` | proved |
| 23:2 | 53 | For $T \parallel S$: $\alpha \in \mathfrak o(T) \iff \operatorname{irr}(x,\alpha,F)$ has coefficients in $\mathfrak o(S)$ $\iff$ $\alpha$ is integral over $\mathfrak o(S)$ | `OMeara.tfae_integral_over` | proved |
| 21.d1 | 41–42 | A non-empty set $S$ of spots on $F$ is a Dedekind set of spots when (D1) every spot in $S$ is discrete, (D2) for each $a \in F$ one has $\lvert a\rvert_{\mathfrak p} \le 1$ for almost all $\mathfrak p \in S$, (D3) the approximation condition for two distinct spots of $S$ and every $\varepsilon > 0$; $\mathfrak o(S) = \bigcap_{\mathfrak p\in S}\mathfrak o(\mathfrak p)$ is the ring of integers at $S$ | `OMeara.DedekindAxioms`, `OMeara.DedekindAxiomsOn` | formalized (a definition, or used in proofs) |
| 22.d1 | 44 | A fractional ideal of $F$ at $S$ is a non-zero $\mathfrak o$-submodule $\mathfrak a \subseteq F$ with $\lambda\mathfrak a \subseteq \mathfrak o$ for some non-zero $\lambda$; the group $J(S)$ of fractional ideals; the principal ideals $P(S)$; an ideal is integral when it lies in $\mathfrak o$ | `FractionalIdeal`, `FractionalIdeal.coeIdeal`, `FractionalIdeal.spanSingleton` | in Mathlib |
| 22.d2 | 44–45 | Greatest common divisor and least common multiple of ideals ($\mathfrak a+\mathfrak b$ and $\mathfrak a\cap\mathfrak b$); $\mathfrak a,\mathfrak b$ are relatively prime when $\mathfrak a+\mathfrak b = \mathfrak o$ | `IsCoprime`, `Ideal.sup`, `Ideal.inf` | in Mathlib |
| 22.d3 | 45 | The valuation of an ideal at $\mathfrak p$: $\lvert\mathfrak a\rvert_{\mathfrak p} = \max_{\alpha \in \mathfrak a}\lvert\alpha\rvert_{\mathfrak p}$ | `OMeara.isGreatest_valuation_image` | proved |
| 22.d4 | 48 | The ideal class group of $F$ at $S$ is $J/P$ (fractional ideals modulo principal ideals); its order is the class number $h_F(S)$ | `OMeara.ClassGroupAt` | formalized (a definition, or used in proofs) |
| 22.d5 | 48 | A non-zero integral ideal $\mathfrak a \ne \mathfrak o$ is decomposable when $\mathfrak a = \mathfrak b\mathfrak c$ with integral ideals $\mathfrak b,\mathfrak c \ne \mathfrak o$, indecomposable otherwise | `OMeara.tfae_prime_indecomposable_maximal` | proved |
| 22.d6 | 48 | An ideal $\mathfrak a$ of $\mathfrak o$ is prime when $\mathfrak o/\mathfrak a$ is an integral domain (recalled from algebra) | `Ideal.IsPrime` | in Mathlib |
| 22.d7 | 52 | A subring $R$ of a field $F$ is a Dedekind domain when $R = \mathfrak o(S)$ for a Dedekind set of spots $S$ on $F$ ($S$ is then unique, 22:10: the underlying set of spots of $R$) | `IsDedekindDomain` | in Mathlib |

## Chapter III. Fields of Number Theory

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 31:1 | 56 | The finite $p$-adic spots and the spot $\infty$ are all the non-trivial spots of $\mathbb Q$ | `everywhere_isotropic_rat_iff` | proved |
| 31:2 | 57 | The finite spots of a rational global field form a Dedekind set, and $Z = \mathfrak o(S)$ | `OMeara.rat_dedekindAxioms` | proved |
| 31:3 | 57 | In $k(x)$ only the constants are integral at $\infty$; $k = \bigcap_{\mathfrak p}\mathfrak o(\mathfrak p)$ | `OMeara.inftyValuation_le_one_iff` | proved |
| 31:4 | 57 | Representative sets and $N\mathfrak p = p$, respectively $q^{\deg p}$; $k$ is a representative set at $\infty$ | `OMeara.residue_card_int` | proved |
| 31:5 | 57 | Every $p$-adic number is $\sum c_\nu p^{\nu}$ with $0 \le c_\nu < p$, uniquely | `OMeara.padic_expansion` | proved |
| 31:6 | 58 | Definition: number field | `OMeara.numberField_iff` | proved |
| 31:7 | 58 | Definition: function field | `OMeara.IsFunctionFieldOM`, `OMeara.isFunctionFieldOM_of_functionField` | formalized (a definition, or used in proofs) |
| 31:8 | 58 | Definition: global field | `OMeara.IsGlobalFieldOM`, `OMeara.isGlobalFieldOM_iff`, `OMeara.isGlobalFieldOM_of_numberField` | formalized (a definition, or used in proofs) |
| 31:9 | 58 | Every global field is a finite separable extension of a rational global field | `OMeara.numberField_finite_separable` | proved |
| 32, text 1 | 59 | The normalized valuation of a discrete spot with finite residue class field exists and is unique | `OMeara.exists_unique_isNormalizedAbs` | proved |
| 32:1 | 59 | Definition of a local field (complete, discrete, finite residue class field) | `OMeara.IsLocalFieldSpot` | formalized (a definition, or used in proofs) |
| 32:2 | 59 | $\mathbb Q_p$ is a local field | `OMeara.isLocalFieldSpot_padic` | proved |
| 32:3 | 60 | A finite extension of a local field is local, $N\mathfrak P = (N\mathfrak p)^f$, $\lvert\alpha\rvert_{\mathfrak P} = \lvert N\alpha\rvert_{\mathfrak p}$ (normalized) | `OMeara.isLocal_of_finite` | proved |
| 32:4 | 60 | The completion of a global field at a non-trivial non-archimedean spot is a local field | `OMeara.isLocalFieldSpot_adicCompletion` | proved |
| 32:5 | 60 | $(\mathfrak o : \mathfrak p^{\nu}) = (N\mathfrak p)^{\nu}$ | `HN.card_quot_ϖ_pow` | proved |
| 32, text 2 | 61 | Unramified and fully ramified extensions in towers | `OMeara.isUnramifiedAbs_tower_iff` | proved |
| 32:6 | 61 | $E = F(\alpha)$ with $f(\alpha) = 0$, $f'(\alpha)$ a unit: $\alpha$ integral, $E/F$ unramified, $\bar E = \bar F(\bar\alpha)$ | `OMeara.isUnramifiedAbs_of_derivative` | proved |
| 32:6a | 61 | $F(\zeta)/F$ is unramified for an $m$-th root of unity $\zeta$, $m$ a unit | `OMeara.isUnramifiedAbs_adjoin_root_of_unity` | proved |
| 32:7 | 61 | Distinct elements of a cyclic group of order prime to $N\mathfrak p$ lie in distinct residue classes | `OMeara.residue_injOn_rootsOfUnity` | proved |
| 32:8 | 62 | The $(N\mathfrak p - 1)$-th roots of unity form a cyclic group of order $N\mathfrak p - 1$; no other roots of unity of order prime to $N\mathfrak p$ | `OMeara.rootsOfUnity_residueCard_sub_one` | proved |
| 32:8a | 62 | The $(N\mathfrak p - 1)$-th roots of unity and $0$ form a representative set | `OMeara.bijOn_residue_teichmuller` | proved |
| 32:9 | 62 | A splitting field of $x^{(N\mathfrak p)^n} - x$ is unramified of degree $n$ | `OMeara.isUnramifiedAbs_of_isSplittingField` | proved |
| 32:10 | 63 | An unramified extension of degree $n$ is a splitting field of $x^{(N\mathfrak p)^n} - x$ | `OMeara.isSplittingField_of_isUnramifiedAbs` | proved |
| 32:11 | 63 | Unramified subfields of a given degree are unique; $K_r \subseteq K_m$ for $r \mid m$ | `OMeara.unramified_subfield_unique` | proved |
| 32:12 | 63 | An unramified extension is Galois with cyclic group generated by the unique $\sigma$ with $\sigma x \equiv x^{N\mathfrak p}$ | `OMeara.isGalois_isCyclic_frobenius` | proved |
| 32:12a | 64 | $\sigma\zeta = \zeta^{N\mathfrak p}$ for the $(N\mathfrak P - 1)$-th roots of unity | `OMeara.frobeniusAbs_rootOfUnity` | proved |
| 32:13 | 64 | Definition of the Frobenius automorphism | `OMeara.frobeniusAbs` | formalized (a definition, or used in proofs) |
| 32:14 | 64 | $E/F$ unramified implies $EH/H$ unramified | `OMeara.isUnramifiedAbs_sup` | proved |
| 32:15 | 64 | An Eisenstein polynomial gives a fully ramified extension, with $\alpha$ a prime element | `OMeara.isFullyRamifiedAbs_of_eisenstein` | proved |
| 33:1 | 66 | A non-zero $a$ has $\lvert a\rvert_{\mathfrak p} = 1$ for almost all $\mathfrak p$, and $\prod_{\mathfrak p}\lvert a\rvert_{\mathfrak p} = 1$ (Product Formula) | `NFLocal.finite_bad_places_nf` | proved |
| 33:2 | 67 | $(\mathfrak b : \mathfrak a) = N\mathfrak a/N\mathfrak b$ for $\mathfrak a \subseteq \mathfrak b$ | `OMeara.card_quotient_eq_absNorm_div` | proved |
| 33:3 | 68 | $N\mathfrak a = \prod_{\mathfrak p} \lvert\mathfrak a\rvert_{\mathfrak p}^{-1}$ | `OMeara.idealNorm_eq_prod_inv_normalizedAbs` | proved |
| 33, text 1 | 69 | $\lVert\alpha i\rVert = \lVert i\rVert$ and $M(\alpha i) = M(i)$ | `OMeara.norm_principal_mul` | proved |
| 33:4 | 69 | $M(i) \le \max(1, D\lVert i\rVert)$ | `OMeara.exists_boundedCount_le` | proved |
| 33:5 | 70 | $C\lVert i\rVert < M(i)$ | `OMeara.exists_lt_boundedCount` | proved |
| 33:6 | 73 | The absolute units form a finite cyclic group, the roots of unity | `OMeara.absoluteUnits_finite_cyclic_rootsOfUnity` | proved |
| 33:7 | 74 | Only finitely many discrete spots have $N\mathfrak p \le K$ | `OMeara.finite_primes_norm_le` | proved |
| 33:8 | 74 | For $s \ge 2$ and each $\mathfrak q \in \Omega - S$ there is an $S$-unit large at $\mathfrak q$ and small at the other spots of $\Omega - S$ | `OMeara.exists_sUnit_one_lt` | proved |
| 33:9 | 75 | $s - 1$ such units are independent and generate a subgroup of finite index | `OMeara.sUnits_independent_finiteIndex` | proved |
| 33:10 | 77 | Dirichlet Unit Theorem: $\mathfrak u(S)$ is the absolute units times $s - 1$ infinite cyclic groups | `OMeara.sUnit_theorem` | proved |
| 33:11 | 77 | Very strong approximation | `Lattices.exists_very_strong_approx` | proved |
| 33:11a | 78 | The $A$ of 33:11 can be chosen with $\lvert A\rvert_{\mathfrak q} > 1/\varepsilon$ | `Lattices.exists_very_strong_approx` | proved |
| 33:12 | 78 | A set $S$ of discrete spots is Dedekind if and only if $S \ne \Omega$ | `OMeara.dedekindAxiomsOn_numberField` | proved |
| 33:13 | 79 | The class number $h_F(S)$ is finite | `OMeara.finite_classGroupAt` | proved |
| 33:13a | 80 | There is a Dedekind set $S_0$ of almost all spots with $h_F(S) = 1$ for $S \subseteq S_0$ | `OMeara.exists_finite_set_classGroupAt_subsingleton` | proved |
| 33:14 | 80 | $(J_F : P_FJ_F^S) = h_F(S) < \infty$ | `OMeara.index_sup_sIdeles_eq_card_classGroupAt` | proved |
| 33:14a | 81 | There is $S_0$ with $(J_F : P_FJ_F^S) = 1$ for $S \subseteq S_0$ | `OMeara.exists_index_sup_sIdeles_eq_one` | proved |
| 33, text 2 | 81 | §33J: the classical ring of integers of a number field is $\mathfrak o(T)$ for $T$ the discrete spots | `OMeara.tfae_integral_over` | proved |
| 31.d1 | 55 | A rational function field is a field $k(x)$ with $k$ finite and $x$ transcendental over $k$ ($k$ is its constant field); a rational global field is a rational number field or a rational function field | `OMeara.IsRationalFunctionField`, `OMeara.isRationalFunctionField_ratFunc` | formalized (a definition, or used in proofs) |
| 31.d2 | 55 | The $\mathfrak p$-adic spot of a rational global field at a prime $\mathfrak p$: write $\alpha = \mathfrak p^{k}u/v$ with $\mathfrak p\nmid uv$ and put $\lvert\alpha\rvert_{\mathfrak p} = \rho^{k}$ with $0<\rho<1$; the spot $\infty$ is the unique archimedean spot for $\mathbb Q$ and for a function field the spot of $\lvert f/g\rvert_\infty = \rho^{\deg g - \deg f}$; the $\mathfrak p$-adic spots are the finite spots and $\infty$ is the infinite spot | `padicNorm`, `IsDedekindDomain.HeightOneSpectrum.valuation`, `RatFunc.inftyValuation` | in Mathlib |
| 31.d3 | 57 | The ring of $\mathfrak p$-adic integers $\mathbb Z_{\mathfrak p}$ is the ring of integers of $\mathbb Q_{\mathfrak p}$ | `PadicInt` | in Mathlib |
| 32.d1 | 59 | $N\mathfrak p$ is the number of elements of the residue class field of $F$ at $\mathfrak p$; the normalized valuation at $\mathfrak p$ is the valuation in $\mathfrak p$ for which $N\mathfrak p$ generates the value group | `OMeara.IsNormalizedAbs`, `OMeara.normPrime` | formalized (a definition, or used in proofs) |
| 32.d2 | 60 | An extension $E/F$ of local fields at $\mathfrak P \mid \mathfrak p$ is unramified when $e = 1$ and $f = n$, ramified otherwise, and fully ramified when $e = n$ and $f = 1$ | `OMeara.IsUnramifiedAbs`, `OMeara.IsFullyRamifiedAbs` | formalized (a definition, or used in proofs) |
| 33.d1 | 68 | An idèle of $F$ is an element $i = (i_{\mathfrak p})$ of the direct product $\prod_{\mathfrak p} F_{\mathfrak p}^{\times}$ with $\lvert i_{\mathfrak p}\rvert_{\mathfrak p} = 1$ for almost all $\mathfrak p$; the idèles form the group $J_F$ (coordinatewise multiplication) | `NumberField.IdeleGroup`, `OMeara.ideleAt`, `OMeara.ideleAtInf` | in Mathlib |
| 33.d2 | 68 | The volume of an idèle $i$ is $\lVert i\rVert = \prod_{\mathfrak p}\lvert i_{\mathfrak p}\rvert_{\mathfrak p}$ | `OMeara.norm_idele_eq` | proved |
| 33.d3 | 69 | A subset $X$ of $F$ is bounded by the idèle $i$ when $\lvert x\rvert_{\mathfrak p} \le \lvert i_{\mathfrak p}\rvert_{\mathfrak p}$ for all $x \in X$ and all $\mathfrak p$; $M(i)$ is the number of elements bounded by $i$ | `OMeara.IsBoundedByIdele`, `OMeara.boundedCount` | formalized (a definition, or used in proofs) |
| 33.d4 | 73 | The $S$-units of $F$ are the elements $a$ with $\lvert a\rvert_{\mathfrak p} = 1$ for all $\mathfrak p \in S$ (a subgroup of $F^{\times}$); the group $\mathfrak u(\Omega)$ of absolute units | `OMeara.absoluteUnits`, `Set.unit` | in Mathlib |
| 33.d5 | 80 | A principal idèle is the image of an element of $F^{\times}$ (diagonal embedding); the principal idèles form the subgroup $P_F$ of $J_F$; an $S$-idèle $i$ has $\lvert i_{\mathfrak p}\rvert_{\mathfrak p} = 1$ for all $\mathfrak p \in S$ (the subgroup $J_F^S$), and $P_F^S = J_F^S \cap P_F$ | `OMeara.sIdeles`, `OMeara.principalSIdeles` | formalized (a definition, or used in proofs) |

## Chapter IV. Quadratic Forms and the Orthogonal Group

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 41, text 1 | 82–84 | Definitions: quadratic space, $B$ and $Q$, representation and isometry, orthogonal group $O(V)$ | `OMeara.bil`, `OMeara.IsRepresentedBy`, `OMeara.orth`, `Lattices.orthGroup`, `Lattices.orthGroupV`, `Quat.SOMulEquivOfIsometric` | formalized (a definition, or used in proofs) |
| 41:1 | 84 | A linear map $\sigma\colon V \to W$ with $B(\sigma x_i,\sigma x_j) = B(x_i,x_j)$ on a base is a representation | `OMeara.rep_of_bil_basis` | proved |
| 41:2 | 86 | If spaces $U$, $V$ have matrices $M$, $N$ in bases then $U \to V$ iff $M \to N$ and $U \cong V$ iff $M \cong N$ ($N = T^{\mathsf t}MT$, $T$ invertible) | `OMeara.exists_rep_iff_gram` | proved |
| 41:3 | 87 | Scaling: (i) if $V \cong N$ then $V^{a} \cong aN$; (ii) $d(V^a) = a^n\,dV$ | `OMeara.gram_smul` | proved |
| 41:4 | 87 | $m$ vectors with $d(x_1,\dots,x_m) \ne 0$ are linearly independent | `OMeara.linearIndependent_of_det_gram_ne_zero` | proved |
| 41, text 17–41, text 29 | 85–88 | Matrix equivalence, $\langle N\rangle$, discriminant $d(x_1,\dots,x_m)$ and $dV$, $dV = 1$ for the zero space; a quadratic form as a polynomial $\sum a_{ij}X_iX_j$ and its symmetric matrix | `OMeara.matRep_refl` | proved |
| 42, text 1–42, text 8 | 88–90 | Orthogonal splitting $V = V_1 \perp\cdots\perp V_r$, components, discriminant of a splitting, orthogonal sums, orthogonal base, combined representations $\sigma_1 \perp\cdots\perp\sigma_r$ | `Tamagawa.Frames.det_hessian_blockForm` | proved |
| 42:1 | 90 | Every non-zero quadratic space has an orthogonal base | `OMeara.exists_orthogonal_basis'` | proved |
| 42, text 9–42, text 13 | 90–92 | Orthogonal complement $U^{\perp}$; $\operatorname{rad}V = V^{\perp}$; regular space; $x \mapsto B(x,\cdot)$ is an isomorphism onto the dual; dual base and its uniqueness | `OMeara.mem_orthogonal_iff_bil` | proved |
| 42:2, 42:2a, 42:2b | 91 | A sum of pairwise orthogonal subspaces has $\operatorname{rad}V = \sum\operatorname{rad}V_i$ (42:2); it is regular if and only if every summand is (42:2a); if regular, the sum is direct (42:2b) | `OMeara.rad_eq_iSup` | proved |
| 42:3 | 91 | A space is regular if and only if $dV \ne 0$ | `QuadForm.Nondegenerate` | formalized (a definition, or used in proofs) |
| 42:4 | 91 | (a) A regular subspace $U$ of $V$ splits $V$: $V = U \perp U^{\perp}$; (b) if $V = U \perp W$ then $W = U^{\perp}$ | `Tamagawa.exists_adaptedFrame` | proved |
| 42:5, 42:6 | 92 | Regular $V$ with matrix $N$ has matrix $N^{-1}$ in the dual base (42:5); $\dim U + \dim U^{\perp} = \dim V$ and $U^{\perp\perp} = U$ (42:6) | `OMeara.gram_dualBasis` | proved |
| 42:7 | 93 | A representation of a regular space into another space is an isometry (injective) | `OMeara.injective_of_rep` | proved |
| 42, text 14, 42:8, 42, text 15 | 93–94 | Radical splitting $V = U \perp \operatorname{rad}V$; for radical splittings: $V \to V_1$ iff $U \to U_1$ (42:8 (1)), $V \cong V_1$ iff $U \cong U_1$ and $\operatorname{rad}V \cong \operatorname{rad}V_1$ (42:8 (2)) | `OMeara.exists_isCompl_rad` | proved |
| 42, text 16–42, text 20, 42:9 | 94 | Isotropic and totally isotropic vectors and spaces; hyperbolic plane and its properties (isometric, regular, $d = -1$, universal); a binary space is a hyperbolic plane iff it is isotropic and regular iff $dV = -1$ | `OMeara.totallyIsotropic_iff` | proved |
| 42:10 | 95 | (a) A regular isotropic space is split by a hyperbolic plane; (b) hence it is universal | `Lattices.exists_hyperbolic_pair` | proved |
| 42:11, 42:12, 42:13, 42, proof step 1 | 95 | A regular space represents $\alpha$ iff $\langle -\alpha\rangle \perp V$ is isotropic (42:11); a regular ternary subspace $U$ of a regular quaternary $V$ with $dV = 1$ (42:12); totally isotropic subspaces and hyperbolic planes (42:13) | `OMeara.mem_range_iff_isotropic_prod` | proved |
| 42, text 21, 42:14, 42:14a | 96 | An isometry $\sigma$ is an involution if and only if $V = U \perp W$ with $\sigma = -1_U \perp 1_W$ (42:14); $W$ is the fixed space and $U$ the reversed space (42:14a) | `OMeara.neg_mem_orth` | proved |
| 42, text 22–42, text 27 | 96–97 | The symmetry $\tau_y\colon x \mapsto x - \dfrac{2B(x,y)}{Q(y)}y$ is an isometry of determinant $-1$, an involution, $\tau_y = \tau_{y'}$ iff $Fy = Fy'$, and $\sigma\tau_y\sigma^{-1} = \tau_{\sigma y}$ | `QuadForm.eval_reflMat` | proved |
| 42:15 | 97 | The hyperbolic plane and its symmetries: (i) $\tau_{x-\alpha y}$ acts by $x \mapsto \alpha y$, $y \mapsto \alpha^{-1}x$; (ii) every symmetry of $H$ has this action and interchanges the isotropic lines; (iii) conversely an isometry interchanging the lines is a symmetry; (iv) any other isometry acts by $x \mapsto \alpha x$, $y \mapsto \alpha^{-1}y$ and equals $\tau_{x-y}\tau_{x-\alpha y}$ | `OMeara.hyperbolic_symmetry` | proved |
| 42:16 | 97–98 | Witt cancellation: isometric regular subspaces $U \cong W$ of $V$ have $U^{\perp} \cong W^{\perp}$ | `QuadraticForm.equivalent_of_prod_equivalent_prod_of_associated` | proved |
| 42:17 | 98 | Witt's theorem: an isometry between subspaces of regular isometric spaces extends | `QuadraticForm.exists_isometryEquiv_extend_of_associated` | proved |
| 42, text 28–42, text 33 | 99–100 | Index $\operatorname{ind}V$, splitting off hyperbolic planes, hyperbolic space, elementary transformations | `OMeara.finrank_eq_wittIndex_of_maximal` | proved |
| 43, text 1–43, text 7 | 100–101 | $\det\sigma = \pm 1$; rotations $O^{+}(V)$ (determinant $1$) and reflexions $O^{-}(V)$ (determinant $-1$); every symmetry has determinant $-1$; $\det\colon O_n \to \{\pm 1\}$ has kernel $O_n^{+}$ of index $2$; automorphs of a matrix | `OMeara.det_orth_eq` | proved |
| 43:1, 43:2 | 101–102 | A hyperbolic $V$ and $\sigma$ the identity on a maximal totally isotropic subspace is a rotation (43:1); prolongations of an isometry of a hyperplane: at most two for a regular hyperplane, one is a symmetry times the other (43:2 (a)); exactly one for a non-regular hyperplane (43:2 (b)) | `OMeara.det_eq_one_of_fix_totallyIsotropic` | proved |
| 43:3 | 102–103 | Cartan–Dieudonné: every isometry of a regular $n$-ary space is a product of at most $n$ symmetries | `OMeara.exists_symmetry_prod_eq_length_le` | proved |
| 43:3a, 43:3b | 103–104 | If $\sigma$ is a product of $r$ symmetries then its fixed space has dimension $\ge n - r$ (43:3a); if $\sigma$ is a product of $n$ symmetries the first symmetry can be chosen arbitrarily (43:3b) | `OMeara.finrank_le_finrank_fixed_add_length` | proved |
| 43:4 | 105 | $1 \le n \le 3$, $d$ the dimension of the fixed space of $\sigma$: $\sigma$ is a product of $n - d$, not fewer, symmetries | `OMeara.exists_cd_prod_length_eq_sub_fixRank` | proved |
| 43:5, 43:5a | 105–106 | Ternary regular $V$, isotropic axis: the rotations with this axis form a group isomorphic to $(F,+)$ (43:5); every such rotation is the square of a rotation on the same axis, and there is one that is not the identity (43:5a) | `OMeara.exists_mulEquiv_rotationsFixing` | proved |
| 43, text 15, 43, text 2 | 106 | Definition of the subgroup $\Omega_n$ of $O_n$ (the commutator subgroup of $O_n$; §43D); $\Omega_n \subseteq O_n^{+}$ | `OMeara.omega` | formalized (a definition, or used in proofs) |
| 43:6, 43:7 | 107 | $\Omega_n$ contains the square of every element of $O_n$ (43:6 (a)), is generated by the commutators $\tau_x\tau_y\tau_x\tau_y$ (43:6 (b)) and by the squares of elements of $O_n^{+}$ (43:6 (c)); for $n \ge 3$ it is also the commutator subgroup of $O_n^{+}$ (43:7) | `OMeara.sq_mem_omega` | proved |
| 43:8 | 108 | $\Omega_n$ for small $n$: $n = 1$, $O_1$ has two elements and $\Omega_1$ is trivial (i); $n = 2$, $\Omega_2 = 1$ iff $V$ is the hyperbolic plane over a field of three elements (ii); $\Omega_2 = (O_2^{+})^2$ (iii) | `OMeara.orth_eq_pair_of_finrank_one` | proved |
| 43:9–43:12b | 108–110 | A $\sigma$ fixing every line is $\pm 1_V$ (43:9); the same for isotropic lines, $n \ge 3$ (43:10) and anisotropic lines (43:11); $Z_n = \{\pm 1_V\}$ except for the hyperbolic plane over a field of three elements (43:12); $O_n$ is commutative only for $n = 1$ and that plane (43:12a); $O_n^{+}$ is commutative for $n = 1, 2$ and not for $n \ge 3$ (43:12b) | `OMeara.eq_one_or_neg_of_forall_mem_line` | proved |
| 43:13, 43:13a | 110–111 | For $n \ge 3$: the centralizer of $\Omega_n$ in $O_n$ is $Z_n$ (43:13); the center of $O_n^{+}$ is $O_n^{+} \cap Z_n$ (43:13a (i)) and the center of $\Omega_n$ is $\Omega_n \cap Z_n$ (43:13a (ii)) | `OMeara.mem_centralizer_omega_iff` | proved |
| 43:14, 43:14a, 43:15 | 111–112 | For $n \ge 3$ and $0 \subset U \subset V$ some $\sigma \in \Omega_n$ has $\sigma U \ne U$ (43:14); $\Omega_n \cap Z_n \subset \Omega_n$ (proper) if $n \ge 3$ (43:14a, read from the page image); $V$ regular $n$-ary, not the hyperbolic plane over a field of three elements, $0 \ne \alpha \in Q(V)$: a base with $Q(x_i) = \alpha$ for all $i$ (43:15) | `OMeara.exists_mem_omega_map_ne` | proved |
| 41.d1 | 82 | A geometry whose bilinear form is alternating is symplectic; one whose form is hermitian is unitary | — | out of scope (not formalized) |
| 41.d3 | 83 | A quadratic space $V$ is universal when $Q(V) = F$ | `OMeara.IsUniversal` | formalized (a definition, or used in proofs) |
| 41.d4 | 83 | Subsets $X, Y$ of $V$ are orthogonal when $B(X,Y) = 0$ | `OMeara.mem_orthogonal_iff_bil` | proved |
| 41.d5 | 85 | A symmetric matrix $M$ is represented by $N$ when $M = T^{\mathsf t}NT$ for a matrix $T$ over $F$, and equivalent to $N$ when $T$ is invertible | `QuadForm.IsometricIn` | formalized (a definition, or used in proofs) |
| 42.d1 | 90 | For orthogonal splittings $V = V_1 \perp\cdots\perp V_r$ and subspaces $W_i$ of $W$ that are pairwise orthogonal, representations $\sigma_i\colon V_i \to W_i$ combine to a unique representation $\sigma = \sigma_1 \perp\cdots\perp \sigma_r\colon V \to W$ | `OMeara.exists_unique_rep_of_splitting` | proved |
| 42.d2 | 94 | A non-zero vector is isotropic when $Q(x) = 0$ and anisotropic otherwise; a non-zero space is isotropic when it contains an isotropic vector, anisotropic when it does not, and totally isotropic when each non-zero vector is isotropic | `RatQF.isotropicIn_iff_baseChange` | proved |
| 42.d3 | 94 | A hyperbolic plane is a space with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ in some base | `Lattices.exists_hyperbolic_pair` | proved |
| 42.d4 | 99 | The index $\operatorname{ind}V$ of a regular space is the common dimension of its maximal totally isotropic subspaces ($Q(M) = 0$); $V$ is a hyperbolic space when $V = H_1 \perp\cdots\perp H_r$ with hyperbolic planes $H_i$ (so $0 < 2r = \dim V$) | `OMeara.finrank_eq_wittIndex_of_maximal` | proved |
| 43.d1 | 101 | The automorphs of a symmetric matrix $M$ are the matrices $T$ with $M = T^{\mathsf t}MT$; the proper automorphs have determinant $+1$ | `Quat.mem_SO_iff_hessian` | proved |
| 43.d2 | 103 | The fixed space of an isometry $\sigma$ of $V$ is $\{x \in V : \sigma x = x\}$ | `OMeara.fixSp`, `OMeara.fixRank` | formalized (a definition, or used in proofs) |
| 43.d3 | 105 | The axis of a rotation of a ternary space is the line of vectors it fixes | `OMeara.fixRank_eq_one_of_ternary` | proved |

## Chapter V. The Algebras of Quadratic Forms

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 51, text 1 | 114–118 | Algebras over a field; commutative and division algebras; algebra homomorphisms; defining an algebra by a multiplication table on a basis (associativity among basis vectors, existence of an identity); multiplicative bilinear maps and the tensor product $A_1\otimes\cdots\otimes A_r$; the algebra $L_F(V)$ of linear transformations; opposite algebra; simple, central, division algebras | `Algebra`, `Module.End`, `IsSimpleRing`, `Algebra.IsCentral` | in Mathlib |
| 52:1 | 119–120 | If $A$ and $B$ are central simple algebras over $F$ then so is $A\otimes_F B$ | `OMeara.isCentralSimple_tensorProduct` | proved |
| 52:2 | 120 | Two central simple subalgebras $B, C$ of $A$ containing $1$ and commuting element-wise: the elements $bc$ span the subalgebra they generate, which is isomorphic to $B\otimes_F C$ | `OMeara.tensorProduct_equiv_sup` | proved |
| 52:3 | 121 | For a minimal left ideal $\mathfrak a$ of an algebra $A$, $R_A(\mathfrak a)$ is a division algebra | `OMeara.isUnit_or_eq_zero_of_isAtom` | proved |
| 52:4 | 121 | Minimal left ideals $\mathfrak a, \mathfrak b$ of a simple algebra are $A$-isomorphic, and $R_A(\mathfrak a) \cong R_A(\mathfrak b)$ | `OMeara.nonempty_linearEquiv_of_isAtom` | proved |
| 52:5, 52:6 | 122 | $M_n(F)$ is central simple over $F$; $M_m(F) \otimes M_n(F) \cong M_{mn}(F)$ | `Matrix.isCentral`, `Matrix.kroneckerAlgEquiv` | in Mathlib |
| 52:7 | 122–123 | $M_n(F) \otimes_F D \cong M_n(D)$ for a central division algebra $D$ | `OMeara.nonempty_matrix_tensor_algEquiv_matrix` | proved |
| 52:8 | 123–124 | If $A$ is central simple and $A \cong M_n(D)$ for a division algebra $D$, then $D$ is central, $n$ is unique and $D$ is unique up to isomorphism | `OMeara.omeara_52_8` | proved |
| 52:9 | 125–127 | Wedderburn's theorem: a central simple algebra over $F$ is $M_n(F)\otimes_F D$ for a central division algebra $D$; $n$ is unique and $D$ is unique up to isomorphism | `OMeara.exists_algEquiv_matrix_tensor_division` | proved |
| 52, text 1 | 127–128 | Similarity of central simple algebras: isomorphic algebras are similar; $A \sim A'$ iff $A\otimes M_r(F) \cong A'\otimes M_s(F)$; similar factors give similar tensor products; $A \otimes B \cong B \otimes A$, associativity, $A \otimes F \cong A$; $A$ splits iff $A \sim 1$ iff its division component is $F$; $A \sim 1$ implies $A \otimes B \sim B$ | `OMeara.isBrauerEquivalent_iff_nonempty_algEquiv` | proved |
| 52:10 | 128–129 | $A \otimes_F A^{*}$ splits ($A \otimes A^{*} \cong M_{n^2}(F)$) | `OMeara.tensorProduct_mulOpposite_equiv_end` | proved |
| 52, text 2 | 129 | Cancellation law: $A \otimes B \sim A' \otimes B$ implies $A \sim A'$; the Brauer group (footnote) | `OMeara.CSA52.isBrauerEquivalent_of_tensor` | proved |
| 53, text 1 | 129–131 | Existence and uniqueness of the $E$-ification $EV$ of an $F$-space $V$, of $E$-ifications of quadratic spaces, $EV$ regular if $V$ is, extension of isometries and of algebras | `TensorProduct.RightActions`, `LinearMap.baseChange`, `QuadraticMap.baseChange` | in Mathlib |
| 54:1 | 132 | Any two Clifford algebras of a regular quadratic space are isomorphic (by a unique isomorphism, the identity on $V$) | `CliffordAlgebra` | in Mathlib |
| 54:2 | 132–133 | If $V$ has an orthogonal base $x_1,\dots,x_n$ and $A$ is an algebra compatible with $V$, the subalgebra generated by $V$ in $A$ contains $1_A$ and is spanned by the $2^n$ products $x_1^{e_1}\cdots x_n^{e_n}$ ($e_i = 0, 1$) | `OMeara.CliffordDim.adjoin_range_toSubmodule_eq_span_word` | proved |
| 54:2a | 133 | The dimension of that subalgebra is at most $2^n$ | `OMeara.CliffordDim.finrank_adjoin_range_le` | proved |
| 54:2b | 133 | If the dimension is $2^n$ then the subalgebra generated by $V$ is a Clifford algebra of $V$ | `OMeara.CliffordDim.isCliffordAlgebra_adjoin_of_finrank_eq` | proved |
| 54:3 | 133–135 | Every regular quadratic space has a Clifford algebra | `OMeara.CliffordDim.isCliffordAlgebra_cliffordAlgebra` | proved |
| 54:3a | 135 | The Clifford algebra of an $n$-ary space is generated by $V$ and has dimension $2^n$ | `OMeara.CliffordDim.finrank_cliffordAlgebra` | proved |
| 54, text 1 | 135 | The $2^n$ products $x_1^{e_1}\cdots x_n^{e_n}$ form a base of $C$ (the base derived from $x_1,\dots,x_n$) | `OMeara.CliffordDim.linearIndependent_word_cliffordAlgebra` | proved |
| 54, text 2 | 135 | The even elements form a subalgebra $C^{+}$ containing $1$, spanned by the even derived base vectors; $\dim C^{+} = 2^{n-1}$ | `OMeara.finrank_even` | proved |
| 54:4 | 135–136 | An even element of $C$ that commutes with every element of $V$ is in $F1$ | `OMeara.mem_range_algebraMap_of_mem_even_of_commute` | proved |
| 54:5 | 136 | There is exactly one algebra anti-isomorphism $C \to C$ that is the identity on $V$ | `OMeara.existsUnique_algEquiv_op` | proved |
| 54:6 | 136–137 | If $\tau_{y_1}\cdots\tau_{y_r} = 1_V$ then $Q(y_1)\cdots Q(y_r) \in F^{\times 2}$ | `OMeara.isSquare_prod_of_prod_symmetry_eq_one` | proved |
| 55, text 1 | 137–138 | Definition of the spinor norm $\theta\colon O(V) \to F^{\times}/F^{\times 2}$, $\theta(\tau_{y_1}\cdots\tau_{y_r}) = \prod Q(y_i)$, well defined by 54:6; $\theta(\sigma\tau) = \theta(\sigma)\theta(\tau)$; $\theta(\sigma^{-1}) = \theta(\sigma)$; $\theta(\tau_u) = Q(u)$; $O'(V) = \ker\theta$ on $O^{+}(V)$; a commutator has spinor norm $1$, so $\Omega \le O'$ | `Lattices.spinorNorm_symm` | proved |
| 55, text 2 | 138 | Each of $\Omega_n \le O_n' \le O_n^{+} \le O_n$ is a normal subgroup of $O_n$; scaling $V$ by $a \ne 0$ does not change $O$, $O^{+}$, $O'$ (rotations change spinor norm by an even power of $a$) | `OMeara.omega_subgroupOf_normal` | proved |
| 55:1 | 138–139 | Example: the symmetry of the hyperbolic plane $H = Fx + Fy$ with $\tau x = ay$, $\tau y = a^{-1}x$ is $\tau_{x - ay}$ and has spinor norm $-2a$; the rotation $x\mapsto ax$, $y\mapsto a^{-1}y$ has spinor norm $a$ | `OMeara.hyperbolic_Q_sub_smul` | proved |
| 55:2 | 139 | For $n \ge 2$ the spinor norm $\theta(O_n^{+})$ is the set of scalars $\kappa_1\cdots\kappa_{2r}$ with $2r \le n$ and all $\kappa_i \in Q(V)$ | `OMeara.exists_hasSpinorNorm_iff` | proved |
| 55:2a | 139 | If $V$ is isotropic then $\theta(O_n^{+}) = F^{\times}$ | `OMeara.exists_hasSpinorNorm_of_isotropic` | proved |
| 55:3 | 139 | If the values $Q(u_i)$ are a permutation of the values $Q(v_i)$ then $\tau_{u_1}\cdots\tau_{u_r}\Omega_n = \tau_{v_1}\cdots\tau_{v_r}\Omega_n$ | `OMeara.symProd_mul_inv_mem_omega` | proved |
| 55:4 | 139 | If $V = U \perp W$ and $\sigma = \tau \perp \rho$ then $\theta(\sigma) = \theta(\tau)\theta(\rho)$ | `OMeara.hasSpinorNorm_of_splitting` | proved |
| 55:5 | 140 | For $1 \le n \le 3$: $(O_n^{+})^{2} = \Omega_n = O_n'$ | `OMeara.omega_eq_orthPrime_of_finrank_le_three` | proved |
| 55:6 | 140 | If $U$ is a regular subspace with $Q(U) = Q(V)$ and $\Omega(U) = O'(U)$ then $\Omega(V) = O'(V)$ | `OMeara.omega_eq_orthPrime_of_subspace` | proved |
| 55:6a | 140–141 | For isotropic $V$: $\Omega(V) = O'(V)$ and $O^{+}/O' \cong F^{\times}/F^{\times 2}$ | `OMeara.omega_eq_orthPrime_of_isotropic` | proved |
| 55:7 | 141 | $\theta(-1_V) = dV$, and $-1_V \in O_n'$ if and only if $n$ is even and $dV = 1$ | `OMeara.hasSpinorNorm_neg_one` | proved |
| 56, text 1 | 141–142 | The normal series $1 \le \Omega_n\cap\mathbb Z_n \le \Omega_n \le O_n' \le O_n^{+} \le O_n$; the structure of $\mathbb Z_n\Omega_n/\Omega_n$, $O_n'/\Omega_n$ and $O_n^{+}/O_n'$ for $n \le 3$ or isotropic $V$ (the quotient $\Omega_n/\Omega_n\cap\mathbb Z_n$ is simple for isotropic $V$, $n\ge5$) | `OMeara.neg_mem_omega_iff` | proved |
| 57:1 | 143 | An element $x$ of a quaternion algebra is invertible if and only if its norm $Nx$ is non-zero, and then $x^{-1} = (Nx)^{-1}\bar x$ | `Quat.isUnit_iff_nrd_ne_zero` | proved |
| 57:2 | 143–144 | $\left(\frac{\alpha,\beta}{F}\right)$ is central simple | `OMeara.Quaternions57.isCentral` | proved |
| 57:3 | 144 | If $y, z$ in an algebra $A$ satisfy $y^2 = \alpha 1$, $z^2 = \beta 1$, $yz = -zy$, then $F1 + Fy + Fz + Fyz$ is isomorphic to $\left(\frac{\alpha,\beta}{F}\right)$ | `OMeara.Quaternions57.nonempty_algEquiv_range_liftHom` | proved |
| 57:4 | 144–145 | Example: $(1,-1) \cong M_2(F)$, via $y = e_{12} + e_{21}$, $z = e_{12} - e_{21}$ | `OMeara.Quaternions57.nonempty_algEquiv_matrix_one_neg_one` | proved |
| 57:5 | 145 | Example: the Clifford algebra of $\langle\alpha\rangle \perp \langle\beta\rangle$ is isomorphic to $\left(\frac{\alpha,\beta}{F}\right)$ | `OMeara.Quaternions57.exists_cliffordAlgebra_algEquiv` | proved |
| 57:6 | 145 | An algebra isomorphism of quaternion algebras sends pure quaternions to pure quaternions and preserves conjugates, norm and trace | `OMeara.Quaternions57.algEquiv_re_eq_zero` | proved |
| 57, text 1 | 145–146 | §57B: the quaternion algebra is a quadratic space with $B(x,y)\,1 = \tfrac12T(x\bar y)$, $Q(x)1 = Nx$; scalars are orthogonal to pure quaternions; for pure $x, y$, $B(x,y) = 0$ iff $xy = -yx$; $(\alpha,\beta) \cong \langle1\rangle\perp\langle-\alpha\rangle\perp\langle-\beta\rangle\perp\langle\alpha\beta\rangle$, discriminant $d(\alpha,\beta) = 1$ | `OMeara.QuatIso57.bil_nrdQuadraticForm_apply` | proved |
| 57:7 | 146 | Example: if $V = \langle-\alpha\rangle\perp\langle-\beta\rangle$ is a binary subspace of the pure quaternions of $C$, then $C \cong \left(\frac{\alpha,\beta}{F}\right)$ | `OMeara.QuatIso57.nonempty_algEquiv_of_pure` | proved |
| 57:8 | 146 | $C \cong D$ as algebras $\iff$ $C \cong D$ as quadratic spaces $\iff$ $C^{\circ} \cong D^{\circ}$ | `OMeara.QuatIso57.tfae_iso` | proved |
| 57:9 | 146–147 | For $\alpha, \beta \ne 0$ the following are equivalent: $(\alpha,\beta) \cong (1,-1)$; not a division algebra; isotropic; $(\alpha,\beta)^{\circ}$ isotropic; $\langle\alpha\rangle\perp\langle\beta\rangle$ represents $1$; $\alpha \in N_{E/F}E$ for $E = F(\sqrt\beta)$ | `OMeara.QuatIso57.tfae_division` | proved |
| 57:10 | 147–148 | (1) $(1,\alpha) \cong (1,-1) \cong (\alpha,-\alpha) \cong (\alpha,1-\alpha)$; (2) $(\beta,\alpha) \cong (\alpha,\beta) \cong (\alpha\lambda^2,\beta\mu^2)$; (3) $(\alpha,\alpha\beta) \cong (\alpha,-\beta)$; (4) $(\alpha,\beta)\otimes(\alpha,\gamma) \cong (\alpha,\beta\gamma)\otimes(1,-1)$ | `OMeara.QuatIso57.algEquiv_one_chain` | proved |
| 57:11, first assertion | 148 | $(\alpha,\beta)\otimes(\alpha,\gamma) \sim (\alpha,\beta\gamma)$ (and the similarity versions of 57:10) | `OMeara.Hasse58.isBrauerEquivalent_quaternion_tensor_quaternion` | proved |
| 57:11, second assertion | 148 | $(\alpha,\beta)\otimes(\alpha,\beta) \sim 1$, so $(\alpha,\beta)$ is isomorphic to its own reciprocal | `OMeara.CSA52.isBrauerEquivalent_quaternion_tensor_self` | proved |
| 57:12 | 148 | For an anisotropic pure quaternion $u$, $u$ is invertible and $\tau_u x = -uxu^{-1}$ for pure $x$ | `OMeara.Quaternions57.symmetry_pure_apply` | proved |
| 57:13 | 148–149 | For an invertible quaternion $y$, the conjugation $\sigma_y$ is a rotation of the pure quaternions, and every rotation of the ternary space is $\sigma_y$ for some $y$ | `Lattices.exists_conj_of_mem_spinorKernel` | proved |
| 58:1 | 150 | Two orthogonal bases of a regular space are joined by a chain of orthogonal bases, each obtained from the previous by altering at most two adjacent basis vectors | `OMeara.exists_adjacent_chain_of_orthogonal_bases` | proved |
| 58:2 | 151 | The Hasse algebra $SV$ (the Brauer class of $\bigotimes_{i<j}\left(\frac{a_i,a_j}{F}\right)$) is well defined | `OMeara.Hasse58.nonempty_algEquiv_hasseAlg_values` | proved |
| 58.d1 | 150 | The Hasse algebra $S V = \bigotimes_i (a_i, d_i)$, $d_i = a_1\cdots a_i$, of a regular space with an orthogonal base of values $a_i$ | `OMeara.Hasse58.hasseAlg` | formalized (a definition, or used in proofs) |
| 58:3 | 151–152 | Rules for $SV$: $S V \sim \bigotimes_{i\le j}(a_i,a_j)$; $S(U\perp W) \sim S U\otimes(dU,dW)\otimes S W$; scaling $S(V^{\alpha})$; ternary and quaternary formulas | `OMeara.Hasse58.isBrauerEquivalent_hasseAlg_hasseAlgPairs` | proved |
| 58:4 | 152 | For regular $V, W$ of dimension $n \le 3$: $V \cong W$ iff $\dim V = \dim W$, $dV = dW$, $SV \sim SW$ | `OMeara.Class58.isometric_iff_invariants_of_dim_le_three` | proved |
| 58:5 | 152 | Example: over $\mathbb R$, $\perp^4\langle 1\rangle$ and $\perp^4\langle -1\rangle$ have the same invariants but are not isometric | `OMeara.Class58.example_58_5` | proved |
| 58:6 | 153 | A regular ternary space is isotropic if and only if $SV \sim \left(\frac{-1,-1}{F}\right)$ | `OMeara.Class58.isotropic_iff_hasseAlg_eq_of_dim_three` | proved |
| 58:7 | 153 | A regular quaternary space $V$ with discriminant $d$ is isotropic if and only if $EV$ is isotropic, $E = F(\sqrt d)$ | `OMeara.isotropic_iff_baseChange_isotropic` | proved |
| 58:7a | 153 | $V$ is isotropic if and only if $E(SV) \sim \left(\frac{-1,-1}{E}\right)$ | `OMeara.Class58.isotropic_iff_hasseAlg_baseChange_of_dim_four` | proved |
| 58:8 | 153–154 | Over fields where every regular quinary space is isotropic, regular spaces are classified by $\dim$, $dV$, $SV$ | `OMeara.Class58.isometric_iff_invariants_of_quinaryIsotropic` | proved |
| 52.d1 | 122 | The matrix algebra $M_n(D)$ over a division algebra $D$: all $n\times n$ matrices with entries in $D$, usual addition and multiplication, scalar multiple $a(d_{ij}) = (ad_{ij})$ for $a \in F$; the $n^2$ matrices with a single entry $1$ are its defining matrices | `Matrix`, `Matrix.instAlgebra` | in Mathlib |
| 52.d2 | 128 | Central simple algebras $A, A'$ are similar ($A \sim A'$) when their division algebra components are isomorphic; $A$ splits ($A \sim 1$) when $A \cong M_n(F)$ for some $n \ge 1$, equivalently when its division algebra component is $F$ | `OMeara.isBrauerEquivalent_iff_nonempty_algEquiv` | proved |
| 52.d3 | 128 | The reciprocal algebra $A^{*}$ of a central simple algebra $A$: the same vector space with the twisted product $a * b = ba$ | `MulOpposite`, `Aᵐᵒᵖ` | in Mathlib |
| 54.d1 | 131–132 | An algebra $A$ is compatible with a quadratic space $V$ when $V$ is a subspace of $A$ with $x^2 = Q(x)1_A$ for all $x \in V$; a Clifford algebra $C$ of $V$ is an algebra compatible with $V$ with the universal property that for every compatible $A$ there is exactly one algebra homomorphism $C \to A$ restricting to the identity on $V$ | `OMeara.CliffordDim.IsCliffordAlgebra`, `CliffordAlgebra`, `CliffordAlgebra.lift`, `CliffordAlgebra.ι` | in Mathlib |
| 57.d1 | 142 | The quaternion algebra $\left(\frac{\alpha,\beta}{F}\right)$ with defining base $1, x_1, x_2, x_3$ ($x_1^2 = \alpha$, $x_2^2 = \beta$, $x_3 = x_1x_2 = -x_2x_1$) [formula partly lost]; its elements are quaternions, the elements of $F1$ scalar quaternions, those of $Fx_1 + Fx_2 + Fx_3$ pure quaternions; $(\alpha,\beta)$ is written for the algebra when there is no danger of confusion | `QuaternionAlgebra` | in Mathlib |
| 57.d2 | 143 | The conjugate of a quaternion $x = \xi_0 1 + \xi_1x_1 + \xi_2x_2 + \xi_3x_3$ is $\bar x = \xi_0 1 - \xi_1x_1 - \xi_2x_2 - \xi_3x_3$; its norm is $Nx = x\bar x$ and its trace $Tx = x + \bar x$ | `QuaternionAlgebra.star`, `QuaternionAlgebra.normSq`, `Quat.nrdPolar` | in Mathlib |

## Chapter VI. The Equivalence of Quadratic Forms

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 61, text 1 | 154 | Over a real complete field, $V$ is *positive definite* if $Q(x)$ is a square for every $x$ | `OMeara.posDef_iff_isSquare` | proved |
| 61, text 2 | 154 | Definitions of *negative definite*, *definite*, *indefinite* (not definite) | `OMeara.IsNegDef`, `OMeara.IsDefinite`, `OMeara.IsIndefinite` | formalized (a definition, or used in proofs) |
| 61, text 3 | 154–155 | A real space has an orthogonal base with $Q = 1$ on the first $p$ vectors and $-1$ on the other $q$ (so $V \cong \langle 1\rangle^p \perp \langle -1\rangle^q$) | `OMeara.exists_equivalent_one_neg_one` | proved |
| 61, text 4 | 155 | $V$ is positive definite if and only if $p = n$, negative definite if and only if $q = n$, and indefinite if and only if it is isotropic | `OMeara.posDef_iff_sigPos_eq` | proved |
| 61, text 5 | 155 | The set of values $Q(V)$ is $F^{2}$, $F$, or $-F^{2}$ for positive definite, indefinite, negative definite $V$ | `OMeara.range_eq_of_posDef` | proved |
| 61, text 6 | 155 | Subspaces of a positive definite space are regular and positive definite | `OMeara.posDef_restrict` | proved |
| 61, text 7 | 155 | All maximal positive definite subspaces have the same dimension $\operatorname{ind}^{+}V$; likewise $\operatorname{ind}^{-}V$ (uses Witt's theorem) | `OMeara.finrank_eq_sigPos_of_maximal` | proved |
| 61, text 8 | 155 | $\operatorname{ind}^{+}V + \operatorname{ind}^{-}V = \dim V$ and $\operatorname{ind}V = \min(\operatorname{ind}^{+}V, \operatorname{ind}^{-}V)$ | `OMeara.sigPos_add_sigNeg` | proved |
| 61:1 | 156 | Theorem: $U$ is represented by $V$ if and only if $\operatorname{ind}^{\pm}U \le \operatorname{ind}^{\pm}V$; isometric if and only if equal indices | `OMeara.isRepresentedBy_iff_sigPos_le` | proved |
| 61:2 | 156 | Remark: $\langle -1\rangle \perp \langle -1\rangle$ does not represent $1$, so $(-1,-1)$ is a division algebra (by 57:9); there are two quaternion algebras over a real field, $(1,-1)$ and $(-1,-1)$ | `OMeara.not_neg_sq_add_neg_sq_eq_one` | proved |
| 61, text 9 | 156 | Complex case: every regular space is $\langle 1\rangle^n$; isotropic if $n \ge 2$; represented by $V$ if and only if $\dim U \le \dim V$; isometric if and only if equal dimensions | `OMeara.equivalent_sum_squares_complex` | proved |
| 61, text 10 | 156 | Over $\mathbb C$ there is one quaternion algebra, $(1,-1)$ | `OMeara.quat_complex_equiv` | proved |
| 61, text 11 | 156–157 | Structure of $\Omega_n\cap Z_n$, $O_n'/\Omega_n$, $O_n^{+}/O_n'$ over complete archimedean fields (read in the page image): complex, $\Omega_n = O_n' = O_n^+$ and $\Omega_n\cap Z_n = \{\pm1_V\}$ for $n$ even, $1_V$ for $n$ odd; real, $(O_n^+ : O_n') = 2$ if $V$ is indefinite, $1$ if definite, $O_n' = \Omega_n$, and $\Omega_n\cap Z_n = \{\pm1_V\}$ if $dV = 1$ with $n$ even, $1_V$ otherwise | `OMeara.complex_omega_eq_orthPrime_eq_orthPlus` | proved |
| 62, text 1 | 157 | Squaring on $F_q^{\times}$ has kernel $\{\pm1\}$, so exactly half of the nonzero elements are squares | `OMeara.isSquare_or_isSquare_mul` | proved |
| 62:1 | 157 | A regular space over a finite field is universal if $n \ge 2$ (binary case: some $1 + \epsilon^2$ is a non-square) | `OMeara.isUniversal_of_two_le` | proved |
| 62:1a | 157 | Corollary: a regular space over a finite field has the splitting $\langle 1\rangle \perp \cdots \perp \langle 1\rangle \perp \langle dV\rangle$; two spaces of each dimension | `OMeara.equivalent_one_disc` | proved |
| 62:1b | 158 | Corollary: $V$ is isotropic if $n \ge 3$ | `OMeara.not_anisotropic_of_three_le` | proved |
| 62:2 | 158 | Theorem: $U \cong V$ if and only if equal dimension and discriminant | `OMeara.equivalent_iff_finrank_disc` | proved |
| 62:3 | 158 | Remark: $\langle\alpha\rangle \perp \langle\beta\rangle$ represents $1$, so there is one quaternion algebra over a finite field | `OMeara.exists_sq_add_sq_eq_one` | proved |
| 62:4 | 158 | Remark (read in the page image): for regular $V$ with $n \ge 2$ over a finite field, $(O_n^{+} : O_n') = 2$, $O_n' = \Omega_n$, and $\Omega_n\cap Z_n = \{\pm1_V\}$ if $dV = 1$ with $n$ even, $1_V$ otherwise | `OMeara.relIndex_orthPrime_orthPlus_finite` | proved |
| 63, text 1 | 158 | Fractional ideals of $F$ are the powers $\mathfrak p^\nu = \pi^\nu\mathfrak o$ (recalled from §22E) | `HN.exists_exp_eq` | proved |
| 63, text 2 | 158 | Definition: $F$ is *dyadic* if its residue field has characteristic $2$, *non-dyadic* otherwise | `OMeara.isDyadic_adicCompletionIntegers_iff` | proved |
| 63, text 3 | 159 | $F$ dyadic if and only if $0 < \lvert 2\rvert < 1$ ($\operatorname{ord} 2 > 0$); non-dyadic if and only if $\lvert 2\rvert = 1$ | `HN.valued_two` | proved |
| 63, text 4 | 159 | Non-dyadic: exactly half of the nonzero residues are squares (from §62) | `OMeara.index_sq_residue_nondyadic` | proved |
| 63, text 5 | 159 | Dyadic: every residue is a square (finite fields are perfect); for units $\varepsilon, \varepsilon'$ there is a unit $\delta$ with $\varepsilon \equiv \varepsilon'\delta^2 \bmod \pi$ | `OMeara.isSquare_residue_of_dyadic` | proved |
| 63:1 | 159 | Local Square Theorem: $1 + 4\pi\alpha = (1 + 2\pi\beta)^2$ for some integer $\beta$ | `HN.isSquare_of_valued_sub_one_lt` | proved |
| 63:1a | 159 | Units $\varepsilon \equiv \delta \bmod 4\pi$ lie in the same square class | `HN.isSquare_of_valued_sub_one_lt` | proved |
| 63:1b | 159 | $F^{\times 2}$ is open in $F$ | `Tamagawa.Measure.Weil.isOpen_sqSub` | proved |
| 63, text 6 | 159–160 | Definition: quadratic defect $\mathfrak d(\xi) = \bigcap \alpha\mathfrak o$ over all $\xi = \eta^2 + \alpha$ | `OMeara.quadDefect` | formalized (a definition, or used in proofs) |
| 63, text 7 | 160 | $\mathfrak d(\xi) \subseteq \xi\mathfrak o$ | `OMeara.quadDefect_le_span` | proved |
| 63, text 8 | 160 | $\xi \in F^2$ if and only if $\mathfrak d(\xi) = 0$ | `OMeara.isSquare_iff_quadDefect_eq_bot` | proved |
| 63, text 9 | 160 | The defect is attained: $\xi = \eta^2 + \alpha$ with $\alpha\mathfrak o = \mathfrak d(\xi)$ | `OMeara.exists_quadDefect_eq` | proved |
| 63, text 10 | 160 | $\mathfrak d(\alpha^2\xi) = \alpha^2\mathfrak d(\xi)$ | `OMeara.quadDefect_sq_mul` | proved |
| 63, text 11 | 160 | $\mathfrak d(\xi) = \xi\mathfrak o$ if $\operatorname{ord}\xi$ is odd | `OMeara.quadDefect_of_odd` | proved |
| 63, text 12 | 160 | Even order reduces to units: $\mathfrak d(\pi^{2r}\varepsilon) = \pi^{2r}\mathfrak d(\varepsilon)$ | `OMeara.quadDefect_zpow_mul` | proved |
| 63, text 13 | 160 | $\mathfrak d(\varepsilon) = \mathfrak p^d$ if and only if $\varepsilon$ is a square mod $\mathfrak p^d$ but not mod $\mathfrak p^{d+1}$ | `OMeara.quadDefect_eq_pow_iff` | proved |
| 63:2 | 160 | Non-dyadic: $\mathfrak d(\varepsilon) \in \{0, \mathfrak o\}$; dyadic: $0, 4\mathfrak o$, or $\mathfrak p^d$ with $d$ odd, $4\mathfrak o \subset \mathfrak p^d \subseteq \mathfrak p$ | `OMeara.quadDefect_unit_nondyadic` | proved |
| 63:3 | 161 | $\mathfrak d(\varepsilon) = 4\mathfrak o$ if and only if $F(\sqrt\varepsilon)/F$ is quadratic unramified | `Binary.Rel.relChar_eq_quadSymbol` | proved |
| 63:4 | 161 | A unit of defect $4\mathfrak o$ exists and is unique up to squares | `Binary.Rel.genusSym_inert_iff` | proved |
| 63:5 | 162 | Dyadic: $\varepsilon = 1 + \alpha$ with $\lvert 4\rvert < \lvert\alpha\rvert < 1$, $\operatorname{ord}\alpha$ odd, has $\mathfrak d(\varepsilon) = \alpha\mathfrak o$ | `OMeara.quadDefect_one_add` | proved |
| 63:6 | 162 | Remark: each ideal of 63:2 occurs as a defect | `OMeara.exists_quadDefect_nondyadic` | proved |
| 63, text 14 | 162 | $1 + \mathfrak p^r$ is a neighbourhood of $1$ and a subgroup of $\mathfrak u$; $1 + \mathfrak p^{r+1} \subseteq 1 + \mathfrak p^r \subseteq \mathfrak u$ | `HN.Ufil_anti` | proved |
| 63:7 | 162 | Lemma: $(G : H) = (\theta G : \theta H)(G_\theta : H_\theta)$ for a homomorphism $\theta$ | `HN.relIndex_range_eq_index_comap_mul` | proved |
| 63:8 | 163 | (1) $(\mathfrak u : 1 + \mathfrak p^r) = (N\mathfrak p - 1)(N\mathfrak p)^{r-1}$; (2) $(1 + \mathfrak p^r)^2 = 1 + 2\mathfrak p^r$ if $\mathfrak p^r \subseteq 2\mathfrak p$ | `HN.relIndex_Ufil` | proved |
| 63:9 | 163 | $(F^\times : F^{\times 2}) = 2(\mathfrak u : \mathfrak u^2) = 4(N\mathfrak p)^{\operatorname{ord} 2}$ | `HN.index_sq_U0` | proved |
| 63, text 15 | 164 | Definition: $(\alpha, \beta)_\mathfrak p = 1$ if $\alpha\xi^2 + \beta\eta^2 = 1$ is solvable in $F$, else $-1$ (also for complete archimedean $F$) | `hilbertSymbol`, `NFPlace.hilbert` | formalized (a definition, or used in proofs) |
| 63:10 | 164 | Example: $\alpha \in N_{E/F}E^\times$ if and only if $(\alpha, \beta)_\mathfrak p = 1$, $E = F(\sqrt\beta)$ | `Binary.Rel.genusSym_eq_one_iff` | proved |
| 63:11 | 164 | Binary $V$ with $dV$ prime: $V$ represents exactly one of $\gamma$, $\gamma\Delta$ | `OMeara.represents_xor_of_disc_prime` | proved |
| 63:11a | 165 | $(\varepsilon, \Delta)_\mathfrak p = 1$ and $(\pi, \Delta)_\mathfrak p = -1$ | `OMeara.hilbertSymbol_unit_delta` | proved |
| 63:11b | 165 | $(\pi, \Delta)$ is a division algebra; every quaternion division algebra over $F$ is isomorphic to it | `OMeara.quat_prime_delta_division` | proved |
| 63:12 | 166 | Example: non-dyadic, units $\varepsilon, \delta$: $(\varepsilon, \delta) = 1$; $(\pi, \delta) = 1$ if and only if $\delta$ is a square | `SqDual.hilbert_units_nondyadic` | proved |
| 63, text 17 | 166 | $(\alpha, \beta)$ is a division algebra if and only if $(\alpha, \beta)_\mathfrak p = -1$ | `Quat.hilbertSymbol_eq_neg_one_iff_division` | proved |
| 63, text 18 | 166 | The first two formulas of 57:10 for the symbol: $(1,\alpha) = (\alpha,-\alpha) = (\alpha,1-\alpha) = 1$; symmetry; invariance under squares | `hilbertSymbol_comm` | proved |
| 63, text 19 | 166 | $(\alpha, \alpha\beta)_\mathfrak p = (\alpha, -\beta)_\mathfrak p$ | `NFPlace.hilbert_self` | proved |
| 63, text 20 | 166 | Bimultiplicativity $(\alpha,\beta)(\alpha,\gamma) = (\alpha,\beta\gamma)$ ("the fourth") | `NFPlace.hilbert_mul_right` | proved |
| 63:13 | 166 | Nondegeneracy: for a non-square $\beta$ there is $\alpha$ with $(\alpha, \beta)_\mathfrak p = -1$ | `HasseIsoNF.localHilbertField_adicCompletion` | proved |
| 63:13a | 167 | $(F^\times : N_{E/F}E^\times) = 2$ for $E/F$ quadratic | `HN.hilbertSymbol_mul_right_of_global` | proved |
| 63, text 21 | 167 | Definition: Hasse symbol $S_\mathfrak pV = \prod_i (\alpha_i, d_i)_\mathfrak p$, $d_i = \alpha_1\cdots\alpha_i$ | `OMeara.hasseS_eq_prod_partial` | proved |
| 63, text 22 | 167 | $S_\mathfrak pV$ is independent of the orthogonal splitting | `OMeara.hasseS_eq_of_isometric` | proved |
| 63, text 24 | 167 | $S_\mathfrak pV = \prod_{i \le j}(\alpha_i, \alpha_j)_\mathfrak p$ (from Remark 58:3) | `NFPlace.hasseOMeara_eq` | proved |
| 63, text 25 | 167 | $S_\mathfrak p(U \perp W) = S_\mathfrak pU \cdot (dU, dW)_\mathfrak p \cdot S_\mathfrak pW$ | `OMeara.hasseS_append` | proved |
| 63, text 26 | 167 | $S_\mathfrak p(V^\alpha) = (\alpha, (-1)^{n(n+1)/2}(dV)^{n+1})_\mathfrak p\,S_\mathfrak pV$ | `OMeara.hasseS_smul` | proved |
| 63:14 | 167 | Example: non-dyadic, $\langle\varepsilon_1, \dots, \varepsilon_n\rangle$ with units and $n \ge 3$ is isotropic | `NFLocal.isotropic_diag_units_nf` | proved |
| 63:15 | 168–169 | Example, binary $V$: (i) $dV = -\Delta \Rightarrow Q(V) = \mathfrak uF^{\times2}$ or $\pi\mathfrak uF^{\times2}$; (ii) anisotropic with $1 \in Q(V)$: $Q(V)$ has index $2$ in $F^\times$; (iii) $V \cong W$ if and only if $Q(V) = Q(W)$; (iv) anisotropic, $Q(V) \subseteq Q(W) \Rightarrow V \cong W$ | `NFPlace.hilbert_eq_one_iff` | proved |
| 63:16 | 169 | Example: $E/F$ unramified quadratic $\Rightarrow N_{E/F}E^\times = \mathfrak uF^{\times 2}$ | `Binary.Rel.genusSym_inert_iff` | proved |
| 63, text 27 | 169 | (inside 63:16) $N_{E/F}\alpha$ is a unit if and only if $\alpha$ is; $N_{E/F}\mathfrak U = \mathfrak u$ | `OMeara.isUnit_iff_norm_isUnit` | proved |
| 63:17 | 169 | Anisotropic quaternary $V \cong \langle 1, -\Delta, \pi, -\pi\Delta\rangle$ | `LocalRankFive.isotropic_four_of_not_isSquare` | proved |
| 63:18 | 170 | Remark: one anisotropic quaternary space, discriminant $1$, universal; **every regular quaternary space is universal**; two quaternary spaces of discriminant $1$ | `represents_padic_of_four_le` | proved |
| 63:19 | 170 | Every quadratic space of dimension $\ge 5$ over a local field is isotropic | `Lattices.isotropicIn_adicCompletion_of_five_le` | proved |
| 63:20 | 170 | Theorem: regular spaces are isometric if and only if same dimension, discriminant and Hasse symbol | `LocalClassNF.isometric_finite_iff_general` | proved |
| 63:21 | 170 | Theorem: $U$ is represented by $V$ ($\nu = \dim V - \dim U$) if and only if $U \cong V$ ($\nu = 0$), $U \perp \langle dU\,dV\rangle \cong V$ ($\nu = 1$), $U \perp H \cong V$ when $\nu = 2$ and $dU = -dV$; always when $\nu \ge 3$ | `PadicClass.represents_two_iff` | proved |
| 63:22 | 171 | Theorem: some $V'$ has the dimension and discriminant of $V$ and $S_\mathfrak pV' = -S_\mathfrak pV$ if and only if $V$ is neither a line nor a hyperbolic plane | `OMeara.exists_hasseS_neg_iff` | proved |
| 63:23 | 171 | Theorem: $(n_0, d_0, s_0)$ are the invariants of some space if and only if $s_0 = (-1, d_0)_\mathfrak p$ when $n_0 = 1$, or $n_0 = 2$ with $d_0 \in -F^{\times 2}$ | `OMeara.exists_invariants_iff` | proved |
| 63:24 | 172 | Example: non-dyadic quaternary $V$ with unit discriminant and $S_\mathfrak pV = 1$: every ternary subspace $U$ has $Q(U) \supseteq \mathfrak u$ | `OMeara.represents_units_of_ternary` | proved |
| 64, text 1 | 172 | $K^{S}$ is the group of idèles with $\lvert i_{\mathfrak p}\rvert_{\mathfrak p} = 1$ at $\mathfrak p \in S$ and $i_{\mathfrak p} = 1$ at $\mathfrak p \notin S$; it is a subgroup of $J^{S}$ | `OMeara.kIdeles_le_sIdeles` | proved |
| 64, text 2 | 172 | For a spot $\mathfrak p$, the idèles $I_{\mathfrak p}$ supported at $\mathfrak p$ form a group isomorphic to $F_{\mathfrak p}$; it lies in $J^{S}$ if and only if $\mathfrak p \notin S$ | `OMeara.mem_ideleSupportedAt_iff` | proved |
| 64, text 3 | 173 | For a finite separable extension $E/F$ the norm of an idèle, $N_{E/F}\colon J_E \to J_F$, is defined spot by spot | `OMeara.ideleNorm` | formalized (a definition, or used in proofs) |
| 64, text 4 | 173 | $N_{E/F}$ is compatible with the field norm ($N_{E/F}P_E \subseteq P_F$) and with towers $F \subseteq E \subseteq H$ | `OMeara.map_principalSubgroup_le` | proved |
| 65, text 1 | 174 | Conventions on $S$: (i) non-dyadic discrete, (ii) almost all spots, (iii) not all spots, (iv) $J_F = P_FJ^{S}$ (exists by 33:14a) | `OMeara.SConventions` | formalized (a definition, or used in proofs) |
| 65, text 2 | 174 | $\mathfrak u = \{\alpha \in F : \lvert\alpha\rvert_{\mathfrak p} = 1\ \forall \mathfrak p \in S\}$, the group of $S$-units | `HN.SUnit` | formalized (a definition, or used in proofs) |
| 65, text 3 | 174 | $J^{S,2}$, the $S$-idèles that are squares outside $S$; $J^{S,2} = K^{S}\mathfrak U^{2}$ | `OMeara.sqSIdeles_eq_sup` | proved |
| 65, text 4 | 175 | For $E = F(\sqrt\theta)$ and a spot $\mathfrak p$: the local degree $n_{\mathfrak p}$ is $1$ ($\theta$ a square at $\mathfrak p$, two spots over $\mathfrak p$) or $2$ (one spot); $e_{\mathfrak p}, f_{\mathfrak p}$ depend only on $\mathfrak p$ | `HN.two_primes_of_isSquare` | proved |
| 65, text 5 | 176 | $E/F$ is *unramified* at $\mathfrak p$ if $e = 1$, $f = n_{\mathfrak p}$ | `HN.ramificationIdx_eq_one` | proved |
| 65, text 6 | 176 | The spots outside $S$ split into $A = \{n_{\mathfrak p} = 1\}$ and $B = \{n_{\mathfrak p} = 2\}$; $a + b = s$ | `OMeara.ncard_splitA_add_ncard_splitB` | proved |
| 65, text 7 | 176 | $\alpha$ is a *local norm* at $\mathfrak p$ if it is a norm from every $E_{\mathfrak P}$ over $\mathfrak p$; the local norm index is $1$ if $n_{\mathfrak p} = 1$ and $2$ if $n_{\mathfrak p} = 2$ (by 63:13a); $\alpha$ is a local norm if and only if $(\alpha,\theta)_{\mathfrak p} = 1$ | `HN.mem_range_norm_iff` | proved |
| 65, text 8 | 176 | An idèle is a local norm at $\mathfrak p$ if its component is; $(J_{\mathfrak p} : \cdots)$ index formula | `OMeara.isLocalNormIdeleAt_iff` | proved |
| 65:1 | 177 | Example: $\theta$ a unit at a non-dyadic discrete $\mathfrak p$ implies $E/F$ unramified at $\mathfrak p$ and $N_{\mathfrak P/\mathfrak p}\mathfrak U_{\mathfrak P} = \mathfrak u_{\mathfrak p}$ (by 32:6 and 63:16) | `HN.ramificationIdx_eq_one` | proved |
| 65:2 | 177 | Example: an idèle is a norm of an idèle of $E$ if and only if it is a local norm at all $\mathfrak p$ with $n_{\mathfrak p} = 2$ | `OMeara.mem_range_ideleNorm_iff` | proved |
| 65:3 | 177 | Example: $N_{E/F}J_E^{S}$ is the set of idèles in $J^{S}$ that are local norms wherever $n_{\mathfrak p} = 2$ | `OMeara.mem_map_sIdeles_iff` | proved |
| 65:4 | 177 | Example: if $\theta$ is a unit at all $\mathfrak p \in S$, the same holds with the local norm condition at $\Omega - S$ | `OMeara.mem_map_sIdeles_iff_of_unit` | proved |
| 65:5 | 177 | A finitely generated subgroup $G \subseteq F^{\times}$ of rank $r$ has $(G : G^{2}) = 2^{r+1}$ if $-1 \in G$, else $2^{r}$ | `HN.index_range_two` | proved |
| 65:6 | 178 | $(P^{S} : (P^{S})^{2}) = (\mathfrak u : \mathfrak u^{2}) = 2^{s}$ (Dirichlet unit theorem and 65:5) | `HN.index_sq_sUnit` | proved |
| 65:7 | 178 | $(J^{S} : J^{S,2}) = 4^{s}$ | `OMeara.relIndex_sqSIdeles` | proved |
| 65:8 | 178 | If $\theta$ is a unit at all spots of $S$: $(J^{S} : N_{E/F}J_E^{S}) = 2^{b}$ | `OMeara.relIndex_map_sIdeles` | proved |
| 65:9 | 179 | Herbrand's lemma: for a finite index subgroup $\Phi$ of $G$ and endomorphisms $N, T$ with $NT = TN = 1$: $\frac{(G_T : NG)}{(G_N : TG)} = \frac{(\Phi_T : N\Phi)}{(\Phi_N : T\Phi)}$ | `HN.herbrand_formula` | proved |
| 65:10 | 179 | If $\theta$ is a unit at all spots of $S$: $b \ge 1$ and $(P^{S} : N P_E^{S}) = (\mathfrak u : N\mathfrak U) = 2^{b-1}$ (via Herbrand and Dirichlet) | `HN.index_normsF_mul` | proved |
| 65:11 | 181 | If $\alpha$ is a square at all spots outside $S$ and a unit at all spots in $S$, then $\alpha$ is a square in $F$ | `OMeara.isSquare_of_unit_of_isSquare_outside` | proved |
| 65:11a | 181 | $P^{S} \cap J^{S,2} = (P^{S})^{2}$ | `OMeara.principalSIdeles_inf_sqSIdeles` | proved |
| 65:12 | 181 | $(J_F : P_FJ^{S,2}) = (J^{S} : P^{S}J^{S,2}) = 2^{s}$ | `OMeara.index_principal_sup_sqSIdeles` | proved |
| 65:13 | 181 | If $\theta$ is a unit on $S$ and $J_F = P_FJ^{S}$: $(J_F : P_FN J_E) = 2\,(P_FNJ_E : NP_E) \le \cdots$ | `OMeara.index_principal_sup_range_ideleNorm` | proved |
| 65:14 | 182 | Corollary of 65:13: the global norm index $(J_F : P_FN J_E)$ is at least $2$ | `OMeara.two_le_index_principal_sup_range_ideleNorm` | proved |
| 65:15 | 182 | Global Square Theorem: an element of a global field that is a square at almost all spots is a square | `SqLG.isSquare_iff_everywhere` | proved |
| 65, text 9 | 182–183 | Generators of $\mathfrak u$ modulo $\mathfrak u^{2}$: there is a set of exactly $s$ of them, the representation is unique, and every non-square in $\mathfrak u$ extends to such a set | `OMeara.card_le_of_isGenModSq` | proved |
| 65, text 10 | 183 | $F(\sqrt{\mathfrak u})$ is the field obtained by adjoining all square roots of $S$-units | `OMeara.sqrtSUnitField_eq_adjoin` | proved |
| 65:16 | 183 | $[F(\sqrt{\mathfrak u}) : F] = 2^{s}$, from the abstract fact: non-squares $\beta_i$ with all products of distinct $\beta_i$ non-squares give a field extension of degree $2^{t}$ | `OMeara.finrank_sqrtSUnitField` | proved |
| 65:17 | 183 | For generators $\varepsilon_1,\dots,\varepsilon_s$ there are infinitely many $\mathfrak p \in S$ with $\varepsilon_1$ a non-square and $\varepsilon_2,\dots,\varepsilon_s$ squares at $\mathfrak p$ | `OMeara.infinite_nonsquare_one` | proved |
| 65:18 | 183 | There are spots $\mathfrak p_1,\dots,\mathfrak p_s \in S$ such that $\varepsilon_i$ is a non-square at $\mathfrak p_i$ and a square at the others | `OMeara.exists_dual_spots` | proved |
| 65:18a | 184 | If $\alpha$ is a square outside $S$ and a unit on $S - \{\mathfrak p_1,\dots,\mathfrak p_s\}$, then $\alpha$ is a square in $F$ | `OMeara.isSquare_of_dual_spots` | proved |
| 65:19 | 184 | Every element of a global field is a square at infinitely many spots | `OMeara.infinite_isSquare_at` | proved |
| 65:20 | 184 | For an $S$-unit $\varepsilon$ there are distinct spots $\mathfrak q, \mathfrak q'$ in $S$ at which $\varepsilon$ is a square and which have the same square $S$-units | `OMeara.exists_twin_spots` | proved |
| 65:21 | 185 | $(J_F : P_FN J_E) \le 2$ (second inequality: a strictly ascending tower of subgroups) | `OMeara.index_principal_sup_range_ideleNorm_eq_two` | proved |
| 65:22 | 186 | If $\theta$ is a unit on $S$ and $J_F = P_FJ^{S}$: $P_F \cap NJ_E = NP_E$, equivalently the index is $2$ | `OMeara.principalSIdeles_inf_map_sIdeles` | proved |
| 65:23 | 186 | Hasse Norm Theorem: for a quadratic extension $E/F$ of global fields, $\alpha \in F$ is a norm if and only if it is a local norm everywhere | `HasseNorm.hilbert_eq_one_of_everywhere` | proved |
| 66, text 1 | 186 | Notation: $V_{\mathfrak p} = F_{\mathfrak p}V$ is the localization; $V$ is *isotropic at* $\mathfrak p$ if $V_{\mathfrak p}$ is; $U, V$ are *isometric at* $\mathfrak p$ if their localizations are | `Tamagawa.SiegelSpace.locFormV` | formalized (a definition, or used in proofs) |
| 66, text 2 | 186 | $S_{\mathfrak p}V = \prod_{i \le j}(a_i, a_j)_{\mathfrak p}$ for $V \cong \langle a_1\rangle \perp \cdots \perp \langle a_n\rangle$ | `NFPlace.hasseOMeara`, `RatPlace.hasseOMeara` | formalized (a definition, or used in proofs) |
| 66:1 | 187 | Hasse–Minkowski, isotropy form: a regular space over a global field is isotropic if and only if it is isotropic at all spots | `hasseMinkowski_nf` | proved |
| 66:3 | 189 | Representation form: $U$ is represented by $V$ if and only if $U_{\mathfrak p}$ is represented by $V_{\mathfrak p}$ at all spots | `represents_iff_everywhere_nf` | proved |
| 66:4 | 189 | Hasse–Minkowski, isometry form: $U \cong V$ if and only if $U_{\mathfrak p} \cong V_{\mathfrak p}$ at all spots | `Tamagawa.FormClassNF.isometricIn_of_everywhere_nf` | proved |
| 66:5 | 189 | Remark: complete invariants of a space over a global field: dimension, discriminant, Hasse symbols at discrete spots, positive indices at real spots (the last not needed for function fields) | `OMeara.isometricIn_iff_invariants` | proved |
| 66:6 | 189 | Example: $S_{\mathfrak p}V = 1$ at almost all spots (so only finitely many Hasse symbols need checking) | `NFPlace.hasseOMeara_product_formula` | proved |
| 66, text 3 | 189 | Corollary of 66:6: $V_{\mathfrak p}$ is isotropic at almost all $\mathfrak p$ when $n \ge 3$ | `OMeara.finite_not_isotropicIn` | proved |
| 65.d1 | 174 | For a discrete spot $\mathfrak p$ let $\mathfrak o_{\mathfrak p}$ be the ring of integers and $\mathfrak u_{\mathfrak p}$ the group of units of $F_{\mathfrak p}$; an element of $F$ (or $F_{\mathfrak p}$) is said to be a square, an integer, a unit, ... at $\mathfrak p$ if it is one in $F_{\mathfrak p}$, and an idèle $i$ if its component $i_{\mathfrak p}$ is | `HilbertLocal.isSquare_unit_iff` | proved |

## Chapter VII. Hilbert's Reciprocity Law

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 70, text 1 | 190 | Hilbert's reciprocity law $\prod_{\mathfrak p}(\alpha,\beta)_{\mathfrak p} = 1$; hence $\prod_{\mathfrak p}S_{\mathfrak p}V = 1$, a dependence relation among the invariants of $V$ (investigated in §72) | `HN.hilbert_product_formula_nf` | proved |
| 71, text 1 | 190–191 | A primitive $m$-th root of unity generates all $m$-th roots of unity in a field; $F$ contains a primitive $m$-th root if it contains $m$ distinct $m$-th roots | `IsPrimitiveRoot`, `IsPrimitiveRoot.eq_pow_of_pow_eq_one` | in Mathlib |
| 71:1, 71:2 | 191 | Definitions: $K/F$ is an *absolute $m$-cyclotomic extension* if $K = F(\zeta)$ for a primitive $m$-th root of unity; *$m$-cyclotomic* if a subextension of one | `OMeara.isAbsCyclotomic_iff_isCyclotomicExtension` | proved |
| 71:3–71:6 | 191 | Examples: absolute $m$-cyclotomic extensions are splitting fields of $x^{m}-1$; compositum of $m$- and $n$-cyclotomic extensions for coprime $m,n$; uniqueness inside an algebraic closure | `OMeara.isAbsCyclotomic_iff_isSplittingField` | proved |
| 71, text 2 | 191 | A cyclotomic extension is Galois with abelian Galois group (via $\sigma\zeta = \zeta^{r}$) | `IsCyclotomicExtension.isGalois`, `IsCyclotomicExtension.autEquivPowers` | in Mathlib |
| 71, text 3 | 191–192 | *Unramified* at a discrete spot: $e = 1$, $f = n$; for an abelian extension the notion depends only on $\mathfrak p$; $m$-cyclotomic extensions are unramified at spots where $m$ is a unit (by 32:6a) | `HN.ramificationIdx_eq_one` | proved |
| 71:7 | 192 | A finite extension $H/F$ of a number field is unramified at almost all discrete spots of $H$ | `OMeara.finite_setOf_ramificationIdx_ne_one` | proved |
| 71:8 | 192 | The absolute $p$-cyclotomic extension of $F$ has degree $p-1$ for almost all primes $p$ (Eisenstein polynomial argument) | `OMeara.finrank_isAbsCyclotomic_prime` | proved |
| 71:9 | 192–193 | For a finite extension $H/F$ and almost all $p$, every $p$-cyclotomic subextension $K/F$ has $[KH:H] = [K:F]$ | `OMeara.finrank_sup_of_le_adjoin_primitiveRoot` | proved |
| 71, text 4 | 193 | The Frobenius automorphism $\sigma_{\mathfrak p} \in \mathrm{Gal}(K/F)$ at spots where $m$ is a unit; the product $\sigma_{\alpha} = \prod_{\mathfrak p}\sigma_{\mathfrak p}^{\operatorname{ord}_{\mathfrak p}\alpha}$ | `OMeara.existsUnique_frobCyc` | proved |
| 71:10 | 193–194 | Formula: for $\sqrt\beta \in K$, $\sigma_{\alpha}(\sqrt\beta) = \sqrt\beta\prod_{\mathfrak p \in S}\big(\tfrac{\alpha,\beta}{\mathfrak p}\big)$ | `OMeara.frobProd_sqrt` | proved |
| 71:11 | 194–195 | Formula: for $\alpha$ integral at $S$ and close to $1$ outside $S$, $\sigma_{\alpha}\zeta = \zeta^{(-1)^{r}}$ ($r$ the number of real spots where $\alpha < 0$) | `OMeara.exists_frobProd_zeta` | proved |
| 71:12 | 195–196 | If $E/F$ is $m$-cyclotomic and $m$ a unit at $\mathfrak q$, then $I_{\mathfrak q} \subseteq P_FNJ_E$ if and only if $E/F$ has local degree $1$ at $\mathfrak q$ | `OMeara.ideleSupportedAt_le_principalNormIdeles_of_cyclotomic` | proved |
| 71:13 | 196 | If $\big(\tfrac{\alpha,\theta}{\mathfrak p}\big)$-type symbols $(\alpha, -1)_{\mathfrak p} = 1$ for all discrete $\mathfrak p$ then $(\alpha,-1)_{\mathfrak p} = 1$ at the real spots | `OMeara.even_card_infinite_hilbert_neg_one` | proved |
| 71:14 | 197 | For $a \ge 2$ there are infinitely many primes $p$ such that $a$ has even period modulo $p$ | `OMeara.infinite_setOf_even_orderOf` | proved |
| 71:15 | 197–198 | For a discrete spot $\mathfrak p$ there are infinitely many primes $p$ and $p$-cyclotomic extensions $K/F$ unramified of local degree $2$ at $\mathfrak p$ | `OMeara.infinite_setOf_cyclotomic_localDegree_two` | proved |
| 71:16 | 198–200 | For two spots at which $E/F$ is unramified of local degree $2$ and idèles $i_1 \in I_{\mathfrak p_1} - NJ_E$, $i_2 \in I_{\mathfrak p_2} - NJ_E$: $i_1i_2 \in P_FNJ_E$ | `OMeara.mul_mem_principalNormIdeles` | proved |
| 71:17 | 201 | If $E/F$ is unramified at $\mathfrak q$ then $I_{\mathfrak q} \subseteq P_FNJ_E$ if and only if the local degree at $\mathfrak q$ is $1$ | `OMeara.ideleSupportedAt_le_principalNormIdeles_iff` | proved |
| 71:18 | 201–203 | Hilbert's reciprocity law: for $\alpha,\beta \in F^{\times}$ the symbols $(\alpha,\beta)_{\mathfrak p}$ are $1$ almost everywhere and $\prod_{\mathfrak p}(\alpha,\beta)_{\mathfrak p} = 1$ | `HN.hilbert_product_formula_nf` | proved |
| 71, proof step 1 | 201–202 | (step 1 of the proof) for three spots at which $\beta$ is not a square there is $\gamma$ with symbol $-1$ at two of them and $+1$ elsewhere | `OMeara.exists_hilbert_neg_one_at_two_of_three` | proved |
| 71:19, 71:19a | 203 | For an even set $T$ of discrete or real spots there are $\alpha,\beta \in F$ with $(\alpha,\beta)_{\mathfrak p} = -1$ exactly for $\mathfrak p \in T$; $\beta$ may be any element that is a non-square at all spots of $T$ | `NFInputs.exists_prescribed_hilbert_nf` | proved |
| 72:1 | 203–205 | A regular $n$-ary space $U_{\mathfrak p}$ over each completion of a number field comes from a global $V$ if and only if (1) a common $d \in F$ with $dU_{\mathfrak p} = d$, (2) $S_{\mathfrak p}U_{\mathfrak p} = 1$ almost everywhere, (3) $\prod_{\mathfrak p}S_{\mathfrak p}U_{\mathfrak p} = 1$ | `OMeara.exists_global_iff` | proved |
| 73, text 1 | 205–206 | Legendre symbol $(a/p)$ for odd prime $p \nmid a$; $(a/p) = 1$ if and only if $a$ is a square in $\mathbb Q_p$ (Local Square Theorem) | `HilbertLocal.isSquare_unit_iff` | proved |
| 73:1 | 206 | For $p$ odd and $a, b$ prime to $p$: $\big(\tfrac{a,b}{p}\big) = 1$ and $\big(\tfrac{a,p}{p}\big) = \big(\tfrac ap\big)$ | `OMeara.hilbertSymbol_int_of_coprime` | proved |
| 73:2 | 206–207 | For $a, b$ odd: $\big(\tfrac{a,b}{2}\big) = (-1)^{\frac{a-1}{2}\frac{b-1}{2}}$ and $\big(\tfrac{2,b}{2}\big) = (-1)^{(b^{2}-1)/8}$ | `OMeara.hilbertSymbol_two_adic_of_odd` | proved |
| 73:3 | 207 | Quadratic reciprocity with its first and second supplements, from Hilbert reciprocity and 73:1–73:2 | `OMeara.quadratic_reciprocity_of_hilbert` | proved |

## Chapter VIII. Quadratic Forms over Dedekind Domains

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 81, text 1 | 208–209 | For an $\mathfrak o$-module $M \subseteq V$: $FM$ is the spanned subspace; $\alpha M$, $\mathfrak aM$; laws $\mathfrak a(M \cap N) = \mathfrak aM \cap \mathfrak aN$, $(\mathfrak a + \mathfrak b)M = \mathfrak aM + \mathfrak bM$, $F(M+N) = FM + FN$ | `Submodule`, `Submodule.span`, `Submodule.instSMul` | in Mathlib |
| 81, text 2 | 209 | Definition: $M$ is a *lattice in* $V$ if $M = \mathfrak ox_1 + \cdots + \mathfrak ox_m$ for independent $x_i$; a lattice *on* $V$ if in addition $FM = V$; the point $0$ is a lattice | `OMeara.fg_iff_le_span_basis` | proved |
| 81:1 | 209 | A module $M \subseteq V$ is a lattice if and only if $\alpha M \subseteq L$ for some non-zero $\alpha \in \mathfrak o$ and some lattice $L$ on $V$ | `OMeara.fg_iff_exists_smul_le` | proved |
| 81:1a | 209–210 | For $M \subseteq U \subseteq V$: $M$ is a lattice in $V$ if and only if it is a lattice in $U$ | `OMeara.le_span_basis_iff_of_le` | proved |
| 81, text 3 | 210 | Submodules of lattices are lattices; $L \cap K$, $\alpha L$, $\mathfrak aL$, $L+K$ are lattices; every finitely generated $\mathfrak o$-module in $V$ is a lattice | `Submodule.FG` | in Mathlib |
| 81, text 4 | 210 | The *coefficient* $\mathfrak a_x = \{\alpha \in F : \alpha x \in L\}$ of a vector $x \in FL$ in $L$ is a fractional ideal; $x$ is a *maximal vector* if $\mathfrak a_x = \mathfrak o$; maximal vectors exist on every line if the class number is $1$ | `OMeara.coeff_fg` | proved |
| 81:2 | 210–211 | For a hyperplane $U$ and $x_0 \notin U$, the coefficient is maximal for some vector $x_0 + u_0$, and then $L = \mathfrak a(x_0+u_0) + (L \cap U)$ | `OMeara.exists_coeff_max` | proved |
| 81:3 | 211–212 | For a lattice $L$ on $V$ and a base $x_1,\dots,x_n$ there is a base $y_i \in Fx_1+\cdots+Fx_i$ and fractional ideals $\mathfrak a_i$ with $L = \mathfrak a_1y_1 + \cdots + \mathfrak a_ny_n$ | `OMeara.exists_adapted_basis_flag` | proved |
| 81:4 | 212 | Example: the coefficient of $\sum \alpha_ix_i$ in $\sum \mathfrak a_ix_i$ is $(\mathfrak a_1\alpha_1^{-1}) \cap \cdots \cap (\mathfrak a_n\alpha_n^{-1})$; in particular of $x_i$ it is $\mathfrak a_i$ | `OMeara.coeff_sum_basis` | proved |
| 81:5 | 212 | (Steinitz) Every lattice $L$ on $V$ is $\mathfrak a z_1 + \mathfrak oz_2 + \cdots + \mathfrak oz_n$ for a fractional ideal $\mathfrak a$ and a base $z_i$ | `Lattices.Steinitz.exists_eq_glImage_steinitzLat` | proved |
| 81:6 | 212 | Example: an $\mathfrak o$-module in $V$ is a lattice if and only if it is finitely generated | `OMeara.fg_iff_le_span_basis` | proved |
| 81, text 5 | 212–213 | *Adapted* bases; *rank* $L = \dim FL$; a *base* of $L$ and *free* lattices; every lattice is almost free ($\mathfrak ax_1 + \mathfrak ox_2 + \cdots$); free when the class number is $1$ | `OMeara.exists_adapted` | proved |
| 81:7 | 213 | For bases with $L = \sum\mathfrak a_ix_i$, $K = \sum\mathfrak b_iy_i$ and $y_i = \sum_j a_{ij}x_j$: $K \subseteq L$ if and only if $a_{ij}\mathfrak b_i \subseteq \mathfrak a_j$ | `OMeara.le_iff_of_adapted` | proved |
| 81:8 | 213–214 | If $K \subseteq L$ then $K = L$ if and only if $\mathfrak a_1\cdots\mathfrak a_n = \mathfrak b_1\cdots\mathfrak b_n\det(a_{ij})$ | `OMeara.eq_iff_prod_of_adapted` | proved |
| 81, text 6 | 214 | An integral matrix is *unimodular* if its determinant is a unit; a matrix is unimodular if and only if it is invertible with an integral inverse | `Matrix.isUnit_iff_isUnit_det` | proved |
| 81:9 | 214 | For a free lattice with base $x_i$, vectors $y_i = \sum a_{ij}x_j$ form a base if and only if $(a_{ij})$ is unimodular | `OMeara.span_eq_iff_unimodular` | proved |
| 81:10 | 214 | Example: $\mathfrak ov_1 + \cdots + \mathfrak ov_r$ is unchanged by $v_1 \mapsto \epsilon v_1 + \sum\alpha_iv_i$ for a unit $\epsilon$ | `OMeara.span_update_eq` | proved |
| 81:11 | 214–216 | (Invariant factors) Lattices $K, L$ on $V$ have a base with $L = \sum\mathfrak a_ix_i$, $K = \sum\mathfrak a_i\mathfrak t_ix_i$, $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$, the $\mathfrak t_i$ unique | `OMeara.exists_invariant_factors` | proved |
| 81:12 | 216 | Definition of the invariant factors $\mathfrak t_i$ of $K$ in $L$; $(L:K) = \prod(\mathfrak o : \mathfrak t_i)$; finitely many lattices between $K$ and $L$ in the local and global cases | `OMeara.invFactors_eq` | proved |
| 81, text 7 | 216–217 | The localization $\mathfrak a_{\mathfrak p}$ of a fractional ideal; $(\mathfrak{ab})_{\mathfrak p} = \mathfrak a_{\mathfrak p}\mathfrak b_{\mathfrak p}$, $(\mathfrak a \cap \mathfrak b)_{\mathfrak p} = \cdots$, $\mathfrak a = \bigcap_{\mathfrak p}(F \cap \mathfrak a_{\mathfrak p})$ | `Lattices.mem_iff_forall_loc` | proved |
| 81:13 | 217 | $\mathfrak a_{\mathfrak p}$ is the closure of $\mathfrak a$ in $F_{\mathfrak p}$ | `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers` | in Mathlib |
| 81, text 8 | 217–218 | The localization $L_{\mathfrak p}$ of a lattice is the $\mathfrak o_{\mathfrak p}$-module generated by $L$ in $V_{\mathfrak p}$; it is a lattice; $(L+K)_{\mathfrak p} = L_{\mathfrak p} + K_{\mathfrak p}$; $L = \bigcap_{\mathfrak p}(V \cap L_{\mathfrak p})$; $L_{\mathfrak p} = K_{\mathfrak p}$ for almost all $\mathfrak p$ if $FL = FK$ | `Lattices.loc_isLattice` | proved |
| 81:14 | 218–219 | Given $\mathfrak o_{\mathfrak p}$-lattices $J^{(\mathfrak p)}$ on $V_{\mathfrak p}$ with $J^{(\mathfrak p)} = L_{\mathfrak p}$ for almost all $\mathfrak p$ there is a unique $\mathfrak o$-lattice $K$ with $K_{\mathfrak p} = J^{(\mathfrak p)}$ for all $\mathfrak p$ | `Lattices.LocFamily.existsUnique_loc_eq` | proved |
| 82, text 1 | 220 | Definitions: $K$ is *represented by* $L$ ($K \to L$) if there is a representation $\sigma\colon FK \to FL$ with $\sigma K \subseteq L$; an *isometry* of lattices; $K$, $L$ *isometric* ($K \cong L$) if $\sigma K = L$ | `OMeara.LatticeIsRepresentedBy`, `OMeara.IsometricLat`, `Lattices.IsometricLattices`, `Lattices.IsIsometric`, `Tamagawa.SiegelSpace.repCountV`, `Binary.Rel.repNumLat`, `Tamagawa.repCount` | formalized (a definition, or used in proofs) |
| 82, text 2 | 220 | Fundamental question: determine the class of $L$ (isometry class) by invariants; known over local fields, partially over global | `OMeara.cls` | formalized (a definition, or used in proofs) |
| 82, text 3 | 220–221 | Integral representation and equivalence of symmetric matrices $M \to N$, $M \cong N$ (over $\mathfrak o$), $\operatorname{cls}N$; the matrix $N$ of a free lattice in a base | `Binary.Rel.normFormBasis_eval` | proved |
| 82:1 | 222 | For free lattices with matrices $M, N$: (1) $K \to L$ if and only if $M \to N$ over $\mathfrak o$; (2) $K \cong L$ if and only if $M \cong N$ | `OMeara.isRepresentedBy_iff_gram` | proved |
| 82, text 4 | 222 | The discriminant $d_{\mathfrak o}L$ of a free lattice (square class modulo $\mathfrak u^{2}$ of the determinant of a base); $dL$; $d\,0 = 1$ | `OMeara.exists_unit_det_gram` | proved |
| 82, text 5 | 222–223 | The *class* $\operatorname{cls}L$ ($K = \sigma L$, $\sigma \in O(V)$), the *proper class* $\operatorname{cls}^{+}L$; each class contains one or two proper classes; $O(L)$, $O^{+}(L)$, $O^{-}(L)$ | `Binary.Rel.isometricLattices_iff` | proved |
| 82:2 | 223 | Example: $\sigma O(L)\sigma^{-1} = O(\sigma L)$ for $\sigma \in O(V)$ | `OMeara.orthLat_latMap` | proved |
| 82:3 | 223 | Example: $\operatorname{cls}L = \operatorname{cls}^{+}L$ if and only if $(O(L):O^{+}(L)) = 2$ | `OMeara.clsPlus_eq_cls_iff_relIndex` | proved |
| 82:4 | 223 | Example: $\operatorname{cls}^{+}L = \operatorname{cls}L$ if $\dim V$ is odd ($-1_V \in O(L) - O^{+}(L)$) | `OMeara.clsPlus_eq_cls_of_odd` | proved |
| 82:5 | 223 | Example: for a free lattice with matrix $M$, $O(L)$ corresponds to the integral automorphs of $M$; the index is $2$ if and only if $M$ has an improper integral automorph | `OMeara.mem_orthLat_iff_integral` | proved |
| 82:6 | 223 | Example: free lattices $K, L$ on one space with matrices $M, N$: $\operatorname{cls}K = \operatorname{cls}L$ if and only if $\operatorname{cls}M = \operatorname{cls}N$ | `OMeara.mem_cls_iff_gram` | proved |
| 82, text 6 | 223–225 | Direct and orthogonal sums of lattices $L = L_1 \perp \cdots \perp L_r$, components, splitting; adjunction of lattices; the notation $L \cong \langle\alpha_1\rangle \perp \cdots$ and an orthogonal base | `OMeara.IsOrthSplit`, `OMeara.IsOrthSum`, `Tamagawa.splitForm`, `QuadForm.orthSum` | formalized (a definition, or used in proofs) |
| 82, text 7 | 225–226 | The radical $\operatorname{rad}L = \{x \in L : B(x,L) = 0\}$; $L$ is *regular* if $\operatorname{rad}L = 0$; $\operatorname{rad}(L \perp K) = \operatorname{rad}L \perp \operatorname{rad}K$; every lattice has a radical splitting $L = K \perp \operatorname{rad}L$ with $K$ regular; its uniqueness up to isometry | `OMeara.span_splitComp_self` | proved |
| 82:7 | 226–227 | A regular sublattice $K = K_1 \perp \cdots \perp K_r$ of $L$ is a component of $L$ if and only if each $K_i$ is | `OMeara.splits_iff_forall_of_isOrthSplit` | proved |
| 82, text 8 | 227 | The *scale* $\mathfrak sL$ (generated by $B(L,L)$) and the *norm* $\mathfrak nL$ (generated by $Q(L)$); $2\mathfrak sL \subseteq \mathfrak nL \subseteq \mathfrak sL$; for $L = J \perp K$, $\mathfrak s$ and $\mathfrak n$ are sums | `OMeara.normIdeal_le_scale` | proved |
| 82:8, 82:8a | 227–228 | For $L = \mathfrak a_1z_1 + \cdots + \mathfrak a_rz_r$: $\mathfrak sL = \sum\mathfrak a_i\mathfrak a_jB(z_i,z_j)$, $\mathfrak nL = \sum\mathfrak a_i^{2}Q(z_i) + 2\mathfrak sL$; $\mathfrak s(\mathfrak aL) = \mathfrak a^{2}\mathfrak sL$, $\mathfrak n(\mathfrak aL) = \mathfrak a^{2}\mathfrak nL$ | `OMeara.scale_iSup_smul` | proved |
| 82:9 | 229 | A regular lattice $K$ is a component of a lattice on $V$ with the same scale and norm | `OMeara.Dedekind.exists_lattice_split_scale_norm` | proved |
| 82, text 9 | 229 | The *volume* $\mathfrak vL = \mathfrak a_1^{2}\cdots\mathfrak a_r^{2}\,d(z_1,\dots,z_r)$ of a lattice (well defined by 81:8); $\mathfrak v0 = \mathfrak o$; $\mathfrak v(J \perp K) = \mathfrak vJ\,\mathfrak vK$ | `OMeara.volume_eq_of_adapted` | proved |
| 82:10 | 229–230 | $\mathfrak vL \subseteq (\mathfrak sL)^{r}$ ($r$ the rank) | `OMeara.volume_le_scale_pow` | proved |
| 82:11, 82:11a | 230 | For regular lattices $K \subseteq L$ with $\mathfrak a$ the product of the invariant factors: $\mathfrak vK = \mathfrak a^{2}\mathfrak vL$ and $\mathfrak aL \subseteq K$; $\mathfrak vK \subseteq \mathfrak vL$ | `OMeara.volume_eq_prod_invFactors_sq` | proved |
| 82:12 | 230 | Example: if $\sigma L \subseteq L$ for $\sigma \in O(V)$ then $\sigma L = L$ (volume is preserved) | `OMeara.latMap_eq_of_le` | proved |
| 82, text 10 | 230–231 | The dual $L^{\#} = \{x \in FL : B(x,L) \subseteq \mathfrak o\}$ of a regular lattice: $L = \sum\mathfrak a_ix_i$ gives $L^{\#} = \sum\mathfrak a_i^{-1}y_i$ ($y_i$ the dual base); $L^{\#\#} = L$, $(\mathfrak aL)^{\#} = \mathfrak a^{-1}L^{\#}$, $\mathfrak vL^{\#} = (\mathfrak vL)^{-1}$, $(J \perp K)^{\#} = J^{\#} \perp K^{\#}$, $L \supseteq K \Rightarrow L^{\#} \subseteq K^{\#}$ | `OMeara.dual_eq_of_adapted` | proved |
| 82, text 11 | 231 | A lattice is *$\mathfrak a$-modular* if $\mathfrak sL = \mathfrak a$ and $\mathfrak vL = \mathfrak a^{r}$; *unimodular* if $\mathfrak a = \mathfrak o$; $\alpha L$ is $\alpha^{2}\mathfrak a$-modular; a splitting is modular if and only if both parts are; $\mathfrak ox$ is $Q(x)$-modular | `OMeara.IsModular.isRegular` | proved |
| 82:13 | 231–232 | A free lattice with matrix $M$ is unimodular if and only if $M$ is unimodular | `OMeara.isUnimodular_iff_gram` | proved |
| 82:14, 82:14a | 232 | $L$ is $\mathfrak a$-modular if and only if $\mathfrak aL^{\#} = L$; then $L = \{x \in FL : B(x,L) \subseteq \mathfrak a\}$ | `OMeara.isModular_iff_smul_dual` | proved |
| 82:14b | 232 | $L$ is unimodular if and only if $L^{\#} = L$ | `OMeara.isUnimodular_iff_dual_eq` | proved |
| 82:15, 82:15a | 232–233 | An $\mathfrak a$-modular sublattice $J$ of $L$ splits $L$ if and only if $B(J,L) \subseteq \mathfrak a$; if $\mathfrak sL = \mathfrak a$ it always splits | `OMeara.Dedekind.splits_iff_of_isModular` | proved |
| 82:16 | 233 | An isotropic vector in an $\mathfrak a$-modular lattice lies in a binary lattice that splits $L$ | `OMeara.exists_binary_split_of_isModular` | proved |
| 82:17 | 233 | ($\mathfrak o$ a principal ideal domain) $L$ is $\mathfrak a$-modular if and only if $B(x,L) = \mathfrak a$ for every maximal vector $x$ | `OMeara.isModular_iff_forall_isMaxVec` | proved |
| 82, text 12 | 234 | A lattice $L$ on $V$ is *$\mathfrak a$-maximal* if $\mathfrak nL \subseteq \mathfrak a$ and every lattice $K \supseteq L$ with $\mathfrak nK \subseteq \mathfrak a$ equals $L$; scaling and splittings of maximal lattices | `OMeara.IsMaximal.ideal_smul` | proved |
| 82:18, 82:18a | 234 | Every lattice $L$ with $\mathfrak nL \subseteq \mathfrak a$ is contained in an $\mathfrak a$-maximal lattice; every regular space contains $\mathfrak a$-maximal lattices | `OMeara.Dedekind.exists_isMaximal_ge` | proved |
| 82:19 | 234–235 | If $2^{r}(\mathfrak vL)\mathfrak a^{-r}$ has no integral square factors then $L$ is $\mathfrak a$-maximal | `OMeara.two_pow_mul_volume_le_one` | proved |
| 82:20 | 235 | An isotropic vector of an $\mathfrak a$-maximal lattice lies in a binary lattice that splits it | `OMeara.Dedekind.exists_binary_split_of_isMaximal` | proved |
| 82:21, 82:21a | 235–236 | On the hyperbolic plane, $L$ is $2\mathfrak a$-maximal if and only if $L$ is $\mathfrak a$-modular with $\mathfrak nL \subseteq 2\mathfrak a$; then $L = \mathfrak bx + \mathfrak a\mathfrak b^{-1}y$ for the isotropic lines | `OMeara.isMaximal_iff_isModular_of_hyperbolic` | proved |
| 82:22 | 236 | Example: ($\mathfrak o$ principal ideal domain) $L$ is $2\alpha\mathfrak o$-maximal on the hyperbolic plane if and only if $L \cong \begin{pmatrix}0&\alpha\\\alpha&0\end{pmatrix}$ | `OMeara.isMaximal_iff_gram_of_principal` | proved |
| 82:23 | 236–237 | Any two maximal lattices on an isotropic space split simultaneously along a hyperbolic plane | `OMeara.exists_hyperbolic_split_of_isMaximal` | proved |
| 82, text 13 | 237 | For regular $L$ and a fractional ideal $\mathfrak a$: $L^{\mathfrak a} = \{x \in L : B(x,L) \subseteq \mathfrak a\} = \mathfrak aL^{\#} \cap L$; $\mathfrak sL^{\mathfrak a} \subseteq \mathfrak a$; for $\mathfrak b$-modular $L$, $L^{\mathfrak a} = L$ if $\mathfrak b \subseteq \mathfrak a$ and $\mathfrak a\mathfrak b^{-1}L$ if $\mathfrak b \supseteq \mathfrak a$ | `OMeara.subA_eq_smul_dual_inf` | proved |
| 82, text 14 | 238 | *Scaling*: $V^{\alpha}$ is $V$ with the form $\alpha B$; $\mathfrak s(L^{\alpha}) = \alpha\mathfrak sL$, $\mathfrak n$, $\mathfrak v(L^{\alpha}) = \alpha^{r}\mathfrak vL$; $L$ $\mathfrak a$-modular gives $L^{\alpha}$ $\alpha\mathfrak a$-modular; $O(L) = O(L^{\alpha})$ and $\operatorname{cls}L = \operatorname{cls}L^{\alpha}$ | `Binary.Rel.isSimilarLat_ideal_iff` | proved |
| 82, text 15 | 238–239 | Localization of scale, norm and volume: $\mathfrak sL_{\mathfrak p} = (\mathfrak sL)_{\mathfrak p}$ etc.; $L$ is $\mathfrak a$-modular if and only if every $L_{\mathfrak p}$ is $\mathfrak a_{\mathfrak p}$-modular; $L$ is $\mathfrak a$-maximal if and only if every $L_{\mathfrak p}$ is $\mathfrak a_{\mathfrak p}$-maximal | `OMeara.scale_locLat` | proved |
| 82.d1 | 220 | A lattice $L$ in $V$ is called binary, ternary, quaternary, quinary, $\dots$ according as its rank (the dimension of $FL$) is $2, 3, 4, 5, \dots$ | `OMeara.exists_binary_split_of_isModular` | proved |

## Chapter IX. Integral Theory of Quadratic Forms over Local Fields

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 91, text 0 | 239–240 | Every lattice over a local field is free; $\mathfrak sL = B(x, y)\mathfrak o$ and $\mathfrak nL = Q(x)\mathfrak o$ for $x, y$ of largest value | `OMeara.exists_basis` | proved |
| 91, text 1 | 234 | Definition of an $\mathfrak a$-maximal lattice (§82H) | `OMeara.IsMaximal` | formalized (a definition, or used in proofs) |
| 91:1 | 239 | On an anisotropic space an $\mathfrak a$-maximal lattice is $\{x : Q(x) \in \mathfrak a\}$; all $\mathfrak a$-maximal lattices are equal | `OMeara.mem_iff_of_isMaximal` | proved |
| 91:2 | 240 | All $\mathfrak a$-maximal lattices on a regular space are in one class | `OMeara.cls_eq_of_isMaximal` | proved |
| 91:3 | 240–241 | $Q(L) = Q(V) \cap \mathfrak a$ for an $\mathfrak a$-maximal lattice $L$; consequences for $\dim V \ge 3$ | `OMeara.Q_image_eq_of_isMaximal` | proved |
| 91, text 2 | 241 | Criterion of §91B: for a maximal anisotropic vector $u$ of $L$, $\tau_u \in O(L) \iff 2B(u, L) \subseteq Q(u)\mathfrak o$ | `OMeara.symmetry_mem_orthLat_iff` | proved |
| 91:4 | 241 | $O(L)$ contains a symmetry of $V$ | `OMeara.exists_symmetry_mem_orthLat` | proved |
| 91:4a | 241 | $(O(L) : O^{+}(L)) = 2$, hence $\operatorname{cls} L = \operatorname{cls}^{+} L$ | `OMeara.relIndex_orthLatPlus` | proved |
| 91:5 | 242 | $O(L) = O(V)$ for a maximal lattice $L$ on an anisotropic space | `OMeara.orthLat_eq_orth_of_isMaximal` | proved |
| 91:6 | 242 | $\theta(O^{+}(V)) = F^{\times}$ for $\dim V \ge 3$ | `OMeara.spinorNormHom_surjective_of_three_le` | proved |
| 91:7 | 242–243 | There is a lattice $L$ on $V$ ($\dim V \ge 3$) with $\theta(O^{+}(L)) = F^{\times}$ | `OMeara.exists_lattice_spinorNorm_eq_top` | proved |
| 91:8 | 243 | $\theta(O^{+}(L)) \supseteq \mathfrak u$ for a maximal lattice $L$, $\dim V \ge 3$ | `OMeara.exists_hasSpinorNorm_of_isMaximal` | proved |
| 91, text 3 | 244 | $L^{\mathfrak a}$ of a Jordan splitting: $\mathfrak sL^{\mathfrak a} = \mathfrak a$ iff some component is $\mathfrak a$-modular, and that component is the first one of a Jordan splitting of $L^{\mathfrak a}$ | `OMeara.subA_eq_iSup` | proved |
| 91:9 | 244 | Any two Jordan splittings of $L$ have the same number of components, scales, ranks, and $\mathfrak nL_i = \mathfrak sL_i \iff \mathfrak nK_i = \mathfrak sK_i$ | `OMeara.IsJordanSplitting.sameJordanType` | proved |
| 91:10 | 245–246 | Jordan chains $L_{(1)} \subseteq \cdots \subseteq L_{(t)} = L$, inverse chains, $L = L_{(i)} \perp L^{(i+1)}$ | `OMeara.jordanChain_mono` | proved |
| 91:11 | 246 | For Jordan chains of lattices of the same Jordan type, $\mathfrak vL_{(i)} = \mathfrak vK_{(i)}$ and $dL_{(i)}/dK_{(i)}$ is a unit | `OMeara.exists_unit_det_jordanChain` | proved |
| 92, text 1 | 246 | Over a non-dyadic field $\mathfrak nL = \mathfrak sL$, and every non-zero regular lattice has an orthogonal base | `OMeara.normIdeal_eq_scale` | proved |
| 92:1 | 246 | A unimodular lattice is $\langle 1\rangle \perp \cdots \perp \langle 1 \rangle \perp \langle \varepsilon\rangle$ with $\varepsilon$ a unit | `OMeara.exists_basis_diag_of_isUnimodular` | proved |
| 92:1a | 247 | There are essentially two unimodular lattices of given dimension (classified by $dL \in \mathfrak u/\mathfrak u^{2}$) | `OMeara.isometricLat_iff_sameDisc_of_isUnimodular` | proved |
| 92:1b | 247 | $Q(L) \supseteq \mathfrak u$ if $\dim L \ge 2$, and $Q(L) = \mathfrak o$ if $\dim L \ge 3$, for unimodular $L$ | `OMeara.exists_mem_Q_eq_unit` | proved |
| 92:2 | 247 | Lattices of the same Jordan type on $V$ are in the same class iff $dL_i = dK_i$ for all $i$ | `OMeara.cls_eq_iff_sameDisc` | proved |
| 92:2a | 248 | $\operatorname{cls} L = \operatorname{cls} K$ iff $FL_i \cong FK_i$ for all $i$ | `OMeara.cls_eq_iff_isometric_span` | proved |
| 92:2b | 248 | $\operatorname{cls} L = \operatorname{cls} K$ iff $FL_{(i)} \cong FK_{(i)}$ for the Jordan chains | `OMeara.cls_eq_iff_isometric_chain` | proved |
| 92:3 | 248 | Cancellation: $L \cong K$, $L = L' \perp L''$, $K = K' \perp K''$, $L' \cong K'$ imply $L'' \cong K''$ | `OMeara.isometricLat_cancel` | proved |
| 92:4 | 248 | Every element of $O(L)$ is a product of at most $2n - 1$ symmetries in $O(L)$ | `OMeara.exists_symmetry_list` | proved |
| 92:5 | 249 | $\theta(O^{+}(L)) = \mathfrak uF^{\times 2}$ for a modular lattice with $\dim L \ge 2$ | `OMeara.exists_hasSpinorNorm_of_isModular` | proved |
| 92:6 | 249 | For a maximal anisotropic $y$, $\tau_y \in O(L)$ iff $\mathfrak oy$ splits $L$ | `OMeara.symmetry_mem_orthLat_iff_splits` | proved |
| 92:7, 92:8 | 249–250 | For $dV = 1$, $S_pV = 1$ there is a lattice with $\theta(O(L)) = F^{\times 2}$ (and $\theta(O^{+}(L)) = \varepsilon F^{\times 2}$ for $\dim V$ even) | `OMeara.exists_lattice_spinorNorm_square` | proved |
| 92:9 | 250 | $\mathfrak sL \subseteq \mathfrak o$ and $\mathfrak vL \supsetneq \mathfrak p^{n(n-1)/2}$ imply $\theta(O^{+}(L)) \supseteq \mathfrak u$ | `OMeara.exists_hasSpinorNorm_of_volume` | proved |
| 93, text 1 | 250–251 | Notation $\alpha \cong \beta$ ($\alpha/\beta \in \mathfrak u^{2}$) and $\alpha \cong \beta \bmod \mathfrak a$ | `OMeara.SqEquiv`, `OMeara.SqEquivMod` | formalized (a definition, or used in proofs) |
| 93:1 | 251 | Notation: $\mathfrak o^{2}$ denotes the set of squares of elements of $\mathfrak o$ | `IsSquare`, `Set.range` | in Mathlib |
| 93:2 | 251 | Notation $dL \cong \alpha \bmod \mathfrak a$ and $dL\,dK \cong \alpha \bmod \mathfrak a$ | `OMeara.DiscSqEquivMod`, `OMeara.DiscProdSqEquivMod` | formalized (a definition, or used in proofs) |
| 93, text 2 | 251–252 | The norm group $\mathfrak gL = Q(L) + 2(\mathfrak sL)$: $2\mathfrak sL \subseteq \mathfrak gL \subseteq \mathfrak nL$, $K \subseteq L \Rightarrow \mathfrak gK \subseteq \mathfrak gL$, $\mathfrak g(K \perp L) = \mathfrak gK + \mathfrak gL$, $\mathfrak gL = Q(L)$ when $\mathfrak sL = \mathfrak o$ and $L$ contains a hyperbolic plane | `OMeara.two_mul_mem_normGroup` | proved |
| 93:3 | 252–253 | A lattice of scale $\mathfrak o$ on a hyperbolic space lies in a unimodular lattice with the same norm group | `OMeara.exists_isUnimodular_of_isHyperbolicSpace` | proved |
| 93, text 3 | 253 | $\mathfrak mL$, the weight $\mathfrak wL = \mathfrak p(\mathfrak mL) + 2(\mathfrak sL)$ and its bounds, norm and weight generators; parity of $\operatorname{ord}\mathfrak nL + \operatorname{ord}\mathfrak mL$ | `OMeara.weight_bounds` | proved |
| 93:4 | 254 | $\mathfrak gL = a\mathfrak o^{2} + \mathfrak wL$ for norm and weight generators $a$, $b$ | `OMeara.normGroup_eq_sq_add` | proved |
| 93:5–93:8 | 254 | Examples: finding generators; behaviour under scaling of the lattice and of the space | `OMeara.exists_isNormGenerator_Q` | proved |
| 93, text 4 | 255 | The unimodular matrix $A(\alpha, \beta)$ ($\alpha, \beta \in \mathfrak o$, $-1 + 4\alpha\beta \in \mathfrak u$) | `OMeara.matA`, `OMeara.HasMatrixA`, `LocalDensity.DVR.pairSumForm` | formalized (a definition, or used in proofs) |
| 93:9 | 255 | $A(\alpha, 0) \cong A(\alpha + 2\beta, 0)$ | `OMeara.HasMatrixA.add_two_mul` | proved |
| 93:10 | 255 | A binary unimodular lattice with a norm generator in $Q(L)$ is $A(a, \beta)$ with $\beta \in \mathfrak wL$ | `OMeara.exists_hasMatrixA` | proved |
| 93:11 | 255–256 | A binary unimodular lattice with $\mathfrak nL \subseteq 2\mathfrak p$ is $A(0,0)$ or $A(2, 2\rho)$ | `OMeara.hasMatrixA_of_normIdeal_le_two` | proved |
| 93:12 | 256 | Changing $A(\alpha, 0)$ in $L = J \perp K$ by $z \in K^{\mathfrak o}$ gives an isometric complement | `OMeara.exists_isOrthSum_shift` | proved |
| 93:13 | 256 | $\langle \xi A(\alpha, 0)\rangle \perp K \cong \langle \xi A(\alpha + \xi^{-1}\beta, 0)\rangle \perp K$ for $\beta \in \mathfrak g K^{\xi\mathfrak o}$ | `OMeara.exists_isOrthSum_matA` | proved |
| 93:14 | 256–257 | Cancellation of a hyperbolic plane $A(0,0)$ | `OMeara.isometricLat_of_cancel_hyperbolic` | proved |
| 93:14a | 257–258 | Cancellation of a modular lattice $J$ with $\mathfrak g J \subseteq \mathfrak g K^{\mathfrak a}$ | `OMeara.isometricLat_of_cancel_modular` | proved |
| 93, text 5 | 258 | The general cancellation law fails over a dyadic field: $\langle A(0,0)\rangle \perp \langle 1 \rangle \cong \langle A(1,0)\rangle \perp \langle 1\rangle$ but $A(0,0) \not\cong A(1,0)$ | `OMeara.isometricLat_hyp_one` | proved |
| 93:15 | 258 | A unimodular lattice has an orthogonal base iff $\mathfrak n L = \mathfrak s L$; otherwise it is an orthogonal sum of binary lattices | `OMeara.exists_orthogonal_basis_iff_of_isUnimodular` | proved |
| 93:16 | 259 | Two unimodular lattices on the same space are isometric iff their norm groups agree | `OMeara.cls_eq_iff_normGroup_eq` | proved |
| 93:17 | 259 | A binary unimodular lattice with norm generator $a \in Q(L)$, weight generator $b$ and $dL = -(1+\alpha)$, $\mathfrak d(1+\alpha) = \alpha\mathfrak o$, has $\alpha a^{-1} \in b\mathfrak o$ and $L \cong A(a, -\alpha a^{-1})$ | `OMeara.D17.omeara93_17` | proved |
| 93:18 | 260–262 | Classification of unimodular lattices of dimension $\ge 3$: (i) $b\mathfrak o = 2\mathfrak o$ in the even case; (ii) $\operatorname{ord} a + \operatorname{ord} b$ even: $L \cong A(0,0) \perp \cdots$; (iii) $\dim 4$, odd: $L \cong J$ or $K$, not both; (iv) $\dim 3$, odd: $A(b,0) \perp \langle -d\rangle$ or $A(b, 4\rho b^{-1}) \perp \langle -d(1-4\rho)\rangle$, not both; (v) $\dim \ge 5$: $L \cong A(0,0) \perp \cdots$ and $\mathfrak gL = Q(L)$; (vi) $\dim 4$, $dL = 1$ | `OMeara.D18.omeara93_18_i` | proved |
| 93:19 | 262 | For a modular lattice $L$ with $\mathfrak sL \subseteq \mathfrak p$, $\dim L \ge 3$ and $\lambda \in \mathfrak g L$: $\langle A(\alpha, \beta)\rangle \perp L \cong \langle A(\alpha + \lambda, \beta)\rangle \perp K$ with $\mathfrak gL \subseteq \mathfrak gK$ | `OMeara.D18.omeara93_19` | proved |
| 93:20 | 262 | $\theta(O^{+}(L)) \supseteq \mathfrak u$ for a modular lattice of dimension $\ge 3$ over a dyadic local field | `OMeara.D18.omeara93_20_nf` | proved |
| 93, text 6 | 262–264 | Definitions: the fundamental invariants $t$, $\dim L_i$, $\mathfrak s_i$, $\mathfrak w_i$, $a_i$, the ideals $\mathfrak f_i$, fundamental type, saturated splittings | `OMeara.fundNormGroup`, `OMeara.fundWeight`, `OMeara.IsFundNormGenerators`, `OMeara.fIdeal`, `OMeara.SameFundamentalType`, `OMeara.IsSaturated` | formalized (a definition, or used in proofs) |
| 93:21 | 265 | A Jordan splitting with all components of dimension at least $3$ can be replaced by a saturated one | `OMeara.Sat93.saturatedSplittingExistence_nf` | proved |
| 93:22–93:25 | 266–267 | Examples: characterization of saturated splittings; behaviour of the invariants under scaling and under $L \mapsto L^{\#}$ | `OMeara.fIdeal_smul_form` | proved |
| 93:26, 93:27 | 267 | Formulas for $\mathfrak s_i^{2}\mathfrak f_i$ in terms of the fundamental invariants; special cases | `OMeara.mul_fIdeal_of_odd` | proved |
| 93, text 7 | 276–277 | The 2-adic case: Jordan invariants $\mathfrak n_i$; $\mathfrak g L = \mathfrak n L$, $\mathfrak w L = 2\mathfrak s L$ | `OMeara.normGroup_eq_normIdeal_twoAdic` | proved |
| 94, text 1 | 279 | Scale and norm from the matrix of a base: $\mathfrak sL = \sum \mathfrak o\,B(x_i, x_j)$, $\mathfrak nL = \sum \mathfrak o\,Q(x_i) + 2(\mathfrak sL)$ | `OMeara.scale_normIdeal_of_basis` | proved |
| 94, text 2 | 279–280 | An algorithm that produces a Jordan splitting from a base | `LocalDensity.DVR.dvr_stepGen` | proved |
| 94, text 3 | 280 | Formulas for a norm generator and the weight, and the fundamental invariants from $L^{\mathfrak s_1}, \dots, L^{\mathfrak s_t}$ | `OMeara.isNormGenerator_of_eq_two_scale` | proved |
| 95:1 | 280–283 | Over a local field $O_n'(V) = \Omega_n(V)$ except for an anisotropic quaternary space over a non-dyadic field, where the index is $2$ | `OMeara.omega_orthPrime_local` | proved |
| 95:1a | 283 | In the exceptional case $\tau_{\langle 1\rangle}\tau_{\langle\Delta\rangle}\tau_{\langle\pi\rangle}\tau_{\langle\pi\Delta\rangle}\Omega_4$ and $\Omega_4$ are the two cosets of $\Omega_4$ in $O'_4$ | `OMeara.omega_cosets_local` | proved |
| 95:2 | 283 | If $\sigma = \tau_{(\alpha_1)}\cdots\tau_{(\alpha_r)} \in \Omega_n$ with $n \ge 3$ and $r \le n$, some regular ternary subspace represents $\alpha_1, \dots, \alpha_r$ | `OMeara.exists_ternary_of_mem_omega` | proved |
| 95, text 1 | 283–284 | $\Omega_n \cap Z_n = \{\pm 1_V\}$ exactly when $dV = 1$ and $n$ is even, except in the exceptional case, where it holds exactly when $-1$ is a non-square | `OMeara.neg_mem_omega_iff_local` | proved |
| 95, text 2 | 284 | $O_n^+/O_n' \cong F^{\times}/F^{\times 2}$ for $n \ge 3$ (and for $n = 2$ isotropic); a subgroup of index $2$ for $n = 2$ anisotropic | `OMeara.spinorNormHom_surjective_local` | proved |
| 91.d1 | 243 | A Jordan splitting of a non-zero regular lattice $L$ over a local field is an orthogonal splitting $L = L_1 \perp \cdots \perp L_t$ into modular lattices with strictly decreasing scales $\mathfrak sL_1 \supsetneq \cdots \supsetneq \mathfrak sL_t$ [inclusion signs partly lost in the scan]; every such $L$ has one | `OMeara.exists_isJordanSplitting` | proved |
| 91.d2 | 245 | Two Jordan splittings $L = L_1 \perp \cdots \perp L_t$ and $K = K_1 \perp \cdots \perp K_{t'}$ are of the same type when $t = t'$ and for all $i$: $\mathfrak sL_i = \mathfrak sK_i$, $\dim L_i = \dim K_i$, and $\mathfrak nL_i = \mathfrak sL_i$ if and only if $\mathfrak nK_i = \mathfrak sK_i$; lattices are of the same Jordan type when their Jordan splittings are | `OMeara.SameJordanType`, `OMeara.isJordanSplitting_latMap` | formalized (a definition, or used in proofs) |
| 93.d1 | 257 | A hyperbolic adjunction to a lattice $L$ is the adjunction of a lattice $J = \xi_1A(0,0) \perp \cdots \perp \xi_rA(0,0)$ with $\xi_i \in F$; if $\xi_i\mathfrak o = \mathfrak a$ for each $i$ then $J$ is $\mathfrak a$-modular and the adjunction is an $\mathfrak a$-modular hyperbolic adjunction | `OMeara.IsHyperbolicLattice`, `OMeara.IsModularHyperbolic` | formalized (a definition, or used in proofs) |

## Chapter X. Integral Theory of Quadratic Forms over Global Fields

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| 101, text 1 | 285 | The norm $\lVert x\rVert_{\mathfrak p} = \max_i \lvert\alpha_i\rvert_{\mathfrak p}$ on $V$ (with respect to a base) is a norm and, in the non-archimedean case, ultrametric and locally constant away from $0$ | `Lattices.vecNorm_eq_zero_iff` | proved |
| 101, text 2 | 286–287 | $V$ and $L_F(V)$ are topological vector spaces, $L_F(V)$ is a topological ring, $\det$ is continuous, $GL(V)$ is open and inversion is continuous; the matrix norm | `Lattices.omeara101_r2` | proved |
| 101:1 | 287–288 | Example: change of base changes $\lVert\cdot\rVert$ by bounded factors (and by units at almost all spots) | `Lattices.vecNorm_le_matNorm_mul_vecNorm_inv` | proved |
| 101, text 3 | 288 | $\lvert B(x,y)\rvert \le A\lVert x\rVert\lVert y\rVert$; $B$ and $Q$ are continuous | `Lattices.valued_evalIn_le` | proved |
| 101:2 | 288 | Example: the set of anisotropic vectors is open and $u \mapsto \tau_u$ is continuous on it | `Lattices.omeara101_2` | proved |
| 101:3 | 288 | Example: $O^{+}(V)$ is open and closed in $O(V)$ | `Lattices.isClopen_soSub` | proved |
| 101:4 (i) | 288 | Example: over a local field the isometries $\sigma$ with $\lVert\sigma\rVert = 1$ are exactly $O(M)$ for the lattice $M$ spanned by the base; they form a group | `Lattices.mem_stdStab_iff_matNorm_le_one` | proved |
| 101:4 (ii) | 289 | Example: for a lattice $L$, $\sigma L = L$ for all $\sigma \in O(V)$ close enough to $1_V$ (the stabilizer of a lattice is open) | `Lattices.exists_mem_nhds_locAct_eq` | proved |
| 101:4 (iii) | 289 | Example: if $K = \lambda L$ with $\lambda \in O(V)$, then $\sigma L = K$ for all $\sigma \in O(V)$ close enough to $\lambda$ | `Lattices.exists_mem_nhds_locAct_eq` | proved |
| 101, text 4 | 289 | Localization $\sigma \mapsto \sigma_{\mathfrak p}$ of a linear map is an injective ring homomorphism $L_F(V) \to L_{F_{\mathfrak p}}(V_{\mathfrak p})$ preserving determinants, isometries and rotations | `Lattices.orthMap`, `Lattices.diagF` | formalized (a definition, or used in proofs) |
| 101, text 5 | 289 | $(\tau_u)_{\mathfrak p} = \tau_{u_{\mathfrak p}}$, and the inclusions $O_n(V)_{\mathfrak p} \subseteq O_n(V_{\mathfrak p})$, $\Omega_n(V)_{\mathfrak p} \subseteq \Omega_n(V_{\mathfrak p})$ | `Lattices.orthMap_symm` | proved |
| 101:5 | 290 | Conventions on the notation $\sigma_{\mathfrak p}$ | `Lattices.orthMap` | formalized (a definition, or used in proofs) |
| 101:6 | 290 | Example: $\sigma_{\mathfrak p}L_{\mathfrak p} = (\sigma L)_{\mathfrak p}$ for all $\mathfrak p \in S$; hence $O(L)_{\mathfrak p} \subseteq O(L_{\mathfrak p})$ | `Lattices.diagF_smul` | proved |
| 101:7 | 290 | Weak Approximation Theorem for Rotations: given $\varphi_{\mathfrak p} \in O^{+}(V_{\mathfrak p})$ at finitely many spots, some $\sigma \in O^{+}(V)$ is $\varepsilon$-close at each | `Lattices.exists_symmProd_approx` | proved |
| 101:8 | 291 | $\theta(O^{+}(V))$ is the set of elements positive at the real spots where $V_{\mathfrak p}$ is anisotropic ($n \ge 3$) | `Lattices.spinorNormGroup_eq_posAtAnisoReal` | proved |
| 101:8a | 292 | Over a function field, $\theta(O^{+}(V)) = F^{\times}$ | `OMeara.omeara101_8a` | proved |
| 101:9 | 292 | Quaternary $V$: for a set $T$ of spots with $\Omega_4(V_{\mathfrak p}) \subsetneq O_4^{+}(V_{\mathfrak p})$, some $\sigma \in O_4^{+}(V)$ has $\sigma_{\mathfrak p} \notin \Omega_4(V_{\mathfrak p})$ on $T$ and $\sigma_{\mathfrak p} \in \Omega_4(V_{\mathfrak p})$ elsewhere | `Lattices.omeara101_9` | proved |
| 101:10 | 292–293 | Example: for $n$ even there is a lattice $K$ with $\operatorname{cls}^{+}K \neq \operatorname{cls}K$, by a construction using 65:20, 81:14 and 92:8 | `Lattices.exists_lat_det_ne_neg_one`, `Lattices.OMeara101_10` | formalized (a definition, or used in proofs) |
| 101, text 7 | 295 | The group $J_V$ of split rotations: families $\Sigma_{\mathfrak p} \in O^{+}(V_{\mathfrak p})$ over all spots with $\lVert\Sigma_{\mathfrak p}\rVert_{\mathfrak p} = 1$ for almost all $\mathfrak p$ (independent of the base) | `Lattices.OAf`, `AWS.OAf` | formalized (a definition, or used in proofs) |
| 101, text 8 | 296 | $J_V'$ = split rotations with $\Sigma_{\mathfrak p} \in O'(V_{\mathfrak p})$ at all spots; it is normal in $J_V$ with abelian quotient (it contains the commutators) | `Lattices.commutator_mem_spinorKernelAf` | proved |
| 101, text 9 | 296 | $\sigma \mapsto (\sigma)$ embeds $O^{+}(V)$ into $J_V$ as the group $P_V$ of principal split rotations | `Lattices.diagF`, `Lattices.ratPoints` | formalized (a definition, or used in proofs) |
| 101, text 10 | 296 | $D = \theta(O^{+}(V))$, and $P_D$ is the group of principal idèles $(\alpha)$ with $\alpha \in D$ | `Lattices.spinorNormGroup`, `Lattices.mem_spinorNormGroup`, `Lattices.sq_mem_spinorNormGroup` | formalized (a definition, or used in proofs) |
| 101:13 | 296 | Example: for $n \ge 3$, $(F^{\times} : D)$ is finite, and $J_F = P_DJ_F^{S}$ for all small enough $S$ | `Lattices.index_spinorNormGroup_ne_zero` | proved |
| 101, text 11 | 296–297 | $J_L = \{\Sigma \in J_V : \Sigma_{\mathfrak p} \in O^{+}(L_{\mathfrak p})\ \forall \mathfrak p \in S\}$, $J_L'$-variants; $O^{+}(L) \cong P_V \cap J_L$ | `Lattices.stabilizer_eq_locStab` | proved |
| 101, text 12 | 297 | For $\Sigma \in J_V$ the lattice $\Sigma L$ is defined by $(\Sigma L)_{\mathfrak p} = \Sigma_{\mathfrak p}L_{\mathfrak p}$ (it exists and is unique by 81:14, since $\Sigma_{\mathfrak p}L_{\mathfrak p} = L_{\mathfrak p}$ almost everywhere); $(\Sigma\Lambda)L = \Sigma(\Lambda L)$, $\sigma L = (\sigma)L$ | `Lattices.LocFamily.loc_glue` | proved |
| 101, text 13 | 297 | $\{\Sigma \in J_V : \Sigma L = L\}$ is the group $J_L$ | `Lattices.stabilizer_eq_locStab` | proved |
| 102, text 1 | 297 | Definition: $\operatorname{gen}L$ = lattices $K$ with $K_\mathfrak p = \Sigma_\mathfrak pL_\mathfrak p$, $\Sigma_\mathfrak p \in O(V_\mathfrak p)$, at every $\mathfrak p$ | `Lattices.SameGenus`, `Lattices.FormSameGenus`, `Tamagawa.SiegelSpace.SameGenusV`, `Lattices.genusClasses` | formalized (a definition, or used in proofs) |
| 102, text 2 | 297 | The lattices on $V$ are partitioned into genera | `Lattices.SameGenus.refl` | proved |
| 102, text 3 | 297 | $\operatorname{gen}K = \operatorname{gen}L$ if and only if $\operatorname{cls}K_\mathfrak p = \operatorname{cls}L_\mathfrak p$ for all $\mathfrak p$ | `Lattices.SameGenus` | formalized (a definition, or used in proofs) |
| 102, text 4 | 297 | Definition: proper genus $\operatorname{gen}^+L$ (local rotations) | `Lattices.SameProperGenus` | formalized (a definition, or used in proofs) |
| 102, text 5 | 297 | Partition into proper genera | `Lattices.SameProperGenus.refl` | proved |
| 102, text 6 | 297 | $\operatorname{gen}^+K = \operatorname{gen}^+L$ if and only if $\operatorname{cls}^+K_\mathfrak p = \operatorname{cls}^+L_\mathfrak p$ for all $\mathfrak p$ | `Lattices.SameProperGenus` | formalized (a definition, or used in proofs) |
| 102, text 7 | 298 | $\operatorname{gen}L = \operatorname{gen}^+L$ (class and proper class agree over local fields) | `Lattices.sameProperGenus_iff_sameGenus` | proved |
| 102, text 8 | 298 | $K \in \operatorname{gen}L$ if and only if $K = \Sigma L$ for some $\Sigma \in J_V$ | `Lattices.orbit_eq_genus` | proved |
| 102, text 9 | 298 | Definition: spinor genus $\operatorname{spn}L$: $K_\mathfrak p = \sigma\Sigma_\mathfrak pL_\mathfrak p$, $\sigma \in O(V)$, $\Sigma_\mathfrak p \in O'(V_\mathfrak p)$ | `Lattices.latSpinorGenus`, `Lattices.SameSpinorGenus` | formalized (a definition, or used in proofs) |
| 102, text 10 | 298 | Equivalently $K = \sigma\Sigma L$ with $\Sigma \in J_V'$ | `Lattices.mem_latSpinorGenus` | proved |
| 102, text 11 | 298 | The lattices on $V$ are partitioned into spinor genera | `Lattices.SameSpinorGenus.refl` | proved |
| 102, text 12 | 298 | $\operatorname{cls}L \subseteq \operatorname{spn}L \subseteq \operatorname{gen}L$ | `Lattices.IsIsometric.sameSpinorGenus` | proved |
| 102, text 13 | 298 | Definition: $h(L)$ classes and $g(L)$ spinor genera in $\operatorname{gen}L$ (finite, shown later) | `Lattices.genusClasses`, `Lattices.mass`, `Lattices.dosetEquivSpinorGenera`, `Lattices.classNumber`, `Lattices.spinorGenusNumber` | formalized (a definition, or used in proofs) |
| 102, text 14 | 298 | Definition: proper spinor genus $\operatorname{spn}^+L$ (three equivalent forms) | `Lattices.sameProperSpinorGenus_iff` | proved |
| 102, text 15 | 298–299 | Partition into proper spinor genera; $\operatorname{cls}^+L \subseteq \operatorname{spn}^+L \subseteq \operatorname{gen}^+L$ | `Lattices.SameProperSpinorGenus.refl` | proved |
| 102, text 16 | 299 | Definition: $h^+(L)$, $g^+(L)$ | `Lattices.properClassNumber`, `Lattices.properSpinorGenusNumber` | formalized (a definition, or used in proofs) |
| 102, text 17 | 299 | All lattices in a genus have the same volume $\mathfrak vL$ | `Lattices.omeara102_r18_holds` | proved |
| 102, text 18 | 299 | Definition: volume of a genus, class, spinor genus | `Lattices.omeara102_r18_holds` | proved |
| 102, text 19 | 299 | Scale and norm of a genus | `Lattices.SameGenus.isIntegral` | proved |
| 102, text 20 | 299 | A genus containing an $\mathfrak a$-modular (resp. $\mathfrak a$-maximal) lattice consists of such lattices | `Lattices.isModular_of_sameGenus` | proved |
| 102:1 | 299 | Example: $\Sigma\operatorname{spn}L = \operatorname{spn}\Sigma L$ (and for $\operatorname{spn}^+$), $\Sigma \in J_V$ | `Lattices.latSpinorGenus_smul` | proved |
| 102:2 | 299 | Example: $h \le h^+ \le 2h$; $g \le g^+ \le 2g$; $g^+ \in \{g, 2g\}$ | `Lattices.classNumber_le_properClassNumber` | proved |
| 102:3 | 299 | Example: the genus of an $\mathfrak a$-maximal lattice is the set of all $\mathfrak a$-maximal lattices on $V$; they share scale, norm and volume | `Lattices.omeara102_3_holds` | proved |
| 102:4 | 299–300 | Example: for $K \in \operatorname{gen}L$ and finite $T$ there is $K' \in \operatorname{cls}^+K$ with $K'_\mathfrak p = L_\mathfrak p$ on $T$ | `Lattices.exists_isometric_agree` | proved |
| 102:6 | 300 | Example: $x^2 + 11y^2$ represents $3$ everywhere locally but not globally | `Lattices.omeara102_6` | proved |
| 102, proof step 1 | 300–301 | (proof of 102:7, step 1) $H \supseteq$ commutators $\Rightarrow$ $HXY$ is independent of order, a normal subgroup | `Lattices.commutator_mem_spinorKernelAf` | proved |
| 102:9 | 304 | Theorem: $J_F = P_DJ_F^S$ and $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$ everywhere $\Rightarrow \operatorname{spn}^+L = \operatorname{gen}L$ | `Lattices.omeara102_9` | proved |
| 102:10 | 304 | Example: (i) $J_F = P_DJ_F^S$ when the class number is $1$ and for $\mathbb Q$; (ii) $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$ for modular or maximal $L$, or with a large modular Jordan component | `Lattices.spinorNormsContainUnits_of_isModularLat` | proved |
| 103, text 1 | 305 | The counting number $N\alpha = N(\alpha\mathfrak o)$ of a scalar; $N(\alpha\beta) = N\alpha\,N\beta$ and $N\alpha = \prod_{\mathfrak p \in S}\lvert\alpha\rvert_{\mathfrak p}^{-1}$ | `Lattices.omeara103_r1` | proved |
| 103:1 | 305 | For a lattice $L$ and a non-singular $\varphi$ with $\varphi L \subseteq L$: $(L : \varphi L) = N(\det\varphi)$ | `Lattices.ClassFin.exists_pigeon` | proved |
| 103:2 | 305–306 | There is a constant $\gamma$ depending on $F$ and $S$ such that for every matrix $(a_{ij})$ with $\det \in \mathfrak u$ there are $\xi_j \in \mathfrak o$, not all $0$, with $\lvert a_{i1}\xi_1 + \cdots + a_{in}\xi_n\rvert_{\mathfrak p} \le \gamma$ for all $\mathfrak p \notin S$ | `Lattices.ClassFin.exists_short` | proved |
| 103:3 | 307 | Lemma: for a fractional ideal $\mathfrak c$ there is a finite set $\mathfrak D \subseteq F$ such that $Q(L) \cap \mathfrak D \ne \emptyset$ for every lattice $L$ with $\mathfrak sL \subseteq \mathfrak o$, $\mathfrak vL \supseteq \mathfrak c$ | `Lattices.ClassFin.exists_value_set` | proved |
| 103:4 | 309 | Theorem: the number of proper classes of lattices on $V$ with integral scale and volume containing $\mathfrak c$ is finite; in particular the number of proper classes in a genus is finite | `Lattices.ClassFin.classes_finite` | proved |
| 103, proof step 1 | 309–310 | (proof of 103:4, step 2) the inductive step: lattices representing a fixed $\alpha$ lie in a finite number of classes, by splitting off $y$ with $Q(y) = \alpha$ | `Lattices.ClassFin.gram_step` | proved |
| 103:5 | 310–311 | Remark: for fixed $F$, $S$, $\mathfrak c$ and $n$, only finitely many quadratic spaces $V$ of dimension $n$ (up to isometry) carry a lattice of integral scale and volume $\mathfrak c$ | `Lattices.omeara103_5_holds` | proved |
| 104:1 | 311 | Lemma: for a lattice $L$ on $V$ ($\dim V \ge 3$) and a finite set $T \subseteq S$ there is a scalar $\mu$, a unit at $T$, such that every element of $\mu\mathfrak o$ that is represented by $V$ and locally by $L$ at every spot is represented by $L$ | `Lattices.exists_scale_represents` | proved |
| 104:2 | 311 | Definition: $S$ is *indefinite* for $V$ if $V_{\mathfrak p}$ is isotropic at some spot outside $S$; otherwise *definite* | `Lattices.IsIndefinite` | formalized (a definition, or used in proofs) |
| 104:3 | 311–315 | Strong approximation for vectors of a given norm ($\dim V \ge 4$, $S$ indefinite) | `Lattices.vecApprox_of_indefinite` | proved |
| 104, proof step 1 | 312 | (proof of 104:3, step 2) a vector $y$ of norm $1$ close to the local vectors, via weak approximation for rotations | `Lattices.exists_quadric_approx` | proved |
| 104, proof step 2 | 313 | (proof of 104:3, step 3) the sublattice $K = L \cap U$ of the orthogonal complement and its represented values at good primes | `Lattices.exists_rep_perp_lattice` | proved |
| 104, proof step 3 | 314 | (proof of 104:3, step 4) the choice of $\beta$ by very strong approximation | `Lattices.exists_beta_local` | proved |
| 104:4 | 315 | Strong Approximation Theorem for Rotations ($\dim V \ge 3$, $S$ indefinite) | `Lattices.strongApproximationSpin` | proved |
| 104, proof step 4 | 315 | (proof of 104:4, step 1a) approximation of short commutators $\tau_u\tau_v\tau_u\tau_v$ | `Lattices.pair_approx` | proved |
| 104, proof step 5 | 316 | (step 1b) products of short commutators | `Lattices.list_approx` | proved |
| 104, proof step 6 | 316–317 | (step 1c) the correction by an element of $O^{4}$ | `Lattices.exists_correction` | proved |
| 104, proof step 7 | 317–319 | (step 2) the ternary case via the quaternion algebra of $V$ and Proposition 57:13 | `Lattices.rotApprox_ternary_isotropic` | proved |
| 104:5 | 319 | Theorem: $\operatorname{cls}^{+}L = \operatorname{spn}^{+}L$ and $\operatorname{cls}L = \operatorname{spn}L$ for $\dim V \ge 3$, $S$ indefinite | `Lattices.eichler_spinorGenus_eq_class` | proved |
| 104:6 | 319–320 | Example: over $\mathbb Q$ with $V$ a hyperbolic plane, $K \in \operatorname{spn}^{+}L$ but $K \notin \operatorname{cls}^{+}L$; so $\dim V \ge 3$ is needed in 104:5 | `Lattices.omeara104_6` | proved |
| 104:7 | 320 | Remark: indefiniteness is needed in 104:5 (by 106:13) | `Lattices.omeara104_7` | proved |
| 104:8 | 320 | Remark: 104:5 with 102:9 and 102:10 give conditions under which $\operatorname{cls}^{+}L = \operatorname{gen}L$ | `Lattices.isIsometric_of_sameGenus'` | proved |
| 104:9 | 320 | Theorem: $S$ indefinite for $V$, $\dim V \ge 3$, $J_F = P_DJ_F^{S}$, $L$ modular or maximal: $\operatorname{cls}^{+}L = \operatorname{gen}L$ | `Lattices.omeara104_9` | proved |
| 104:10 | 320–321 | Theorem: over $\mathbb Q$, indefinite, $\dim V \ge 3$: two lattices of the same norm and scale, both modular or both maximal, are in the same proper class | `Lattices.omeara104_10` | proved |
| 104:11 | 321 | Example: an indefinite binary unimodular lattice over $\mathbb Z$ is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ or $\begin{pmatrix}1&0\\0&-1\end{pmatrix}$ [formula lost: partly], so $\operatorname{cls}^{+}L = \operatorname{gen}L$ | `Lattices.omeara104_11` | proved |
| 104:12 | 321 | Example: an indefinite unimodular $\mathbb Z$-lattice of norm $\mathbb Z$ [formula lost] is isometric to $\langle 1\rangle^{p} \perp \langle -1\rangle^{q}$ | `Lattices.omeara104_12_space` | proved |
| 105, text 1 | 321 | Definition: a lattice $L$ is *decomposable* if $L = K_1 \perp K_2$ with $K_1, K_2 \ne 0$, otherwise *indecomposable*; every lattice is an orthogonal sum of at most $n$ indecomposable lattices (an *indecomposable splitting*) | `Lattices.exists_indecomposable_splitting` | proved |
| 105:1 | 321 | Theorem: if $S$ is definite for $V$ and contains all dyadic spots, the components of an indecomposable splitting of $L$ are unique up to order | `Lattices.indecomposable_splitting_unique` | proved |
| 106, text 1 | 323–324 | If $V$ is positive definite with a unimodular lattice then $dV = 1$, $S_{p}V = 1$ for all $p$, hence $V \cong I_n$ (the sum of $n$ squares) | `Lattices.omeara106_r1` | proved |
| 106, text 2 | 324 | A lattice is *completely decomposable* if it is an orthogonal sum of lattices of dimension $1$ (matrix $I_n$) | `Lattices.IsCompletelyDecomposable` | formalized (a definition, or used in proofs) |
| 106, text 3 | 324 | A unimodular $\mathbb Z$-lattice has $\mathfrak nL = \mathbb Z$ (*odd*) or $2\mathbb Z$ (*even*); $L$ is even if and only if $Q(L) \subseteq 2\mathbb Z$ | `Lattices.IsEvenLat`, `Lattices.IsUnimodularZ`, `Lattices.omearaDual` | formalized (a definition, or used in proofs) |
| 106:1 | 324–325 | An even unimodular lattice on $V \cong I_n$ exists if and only if $n \equiv 0 \bmod 8$ | `Lattices.omeara106_1` | proved |
| 106, text 4 | 325 | The set $\mathcal G(L)$ of unimodular lattices $K$ with $K_p = L_p$ at all odd $p$ | `Lattices.omearaG` | formalized (a definition, or used in proofs) |
| 106:2 | 325 | For $n \ge 5$ and unimodular $K, L$ there is $J \in \operatorname{cls}^{+}K$ with $J \in \mathcal G(L)$ | `Lattices.omeara106_2_holds` | proved |
| 106, text 5 | 325–326 | *Adjacent lattices*: $K$ is adjacent to $L$ if the invariant factors of $K$ in $L$ are $\tfrac12\mathbb Z, \mathbb Z, \dots, \mathbb Z, 2\mathbb Z$; adjacency is symmetric, finite in number, preserved by isometries | `Lattices.Nbr.IsNbrL`, `Lattices.Nbr.nbLat`, `Siegel.Kneser.IsNeighbor` | formalized (a definition, or used in proofs) |
| 106:3 | 326 | For $n \equiv 0 \bmod 8$ and a unimodular $L$ there are even and odd unimodular lattices adjacent to $L$ | `Lattices.exists_adjacent_of_sameParity`, `Lattices.OMeara106_3` | formalized (a definition, or used in proofs) |
| 106:4 | 326–327 | For $n \ge 2$, unimodular $K, L$ with $K \in \mathcal G(L)$ are joined by a chain of adjacent unimodular lattices | `Lattices.kneser_reach_uncond` | proved |
| 106:5 | 328 | Equivalent conditions for adjacency: (1) adjacent, (2) $\mathfrak v(K + L) = \tfrac14\mathbb Z$, (3) $\mathfrak v(K \cap L) = 4\mathbb Z$ | `Lattices.omeara106_5` | proved |
| 106:6 | 328 | If $K$ is adjacent to $L$ and $y \in L - K$: $L + K = \mathbb Zy + K$, $L = \mathbb Zy + (L \cap K)$, $L \cap K = (\mathbb Zy + K)^{\#}$ | `Lattices.omeara106_6` | proved |
| 106:7 | 328–329 | For $y \in \tfrac12K - K$ with $Q(y) \in \mathbb Z$ there is exactly one unimodular lattice adjacent to $K$ containing $y$, namely $\mathbb Zy + (\mathbb Zy + K)^{\#}$ | `Lattices.omeara106_7` | proved |
| 106:8, 106:8a | 329 | $y + z \in L - K$ if and only if $z \in L \cap K$; two adjacent lattices coincide if and only if $y - y' \in K$ with $B(y,y') \in \mathbb Z$; this gives a procedure to list all adjacent lattices | `Lattices.omeara106_8` | proved |
| 106:9 | 330 | If $y = w + z$ with $Q(w) = 1$, $z \in K$, $B(y,w) \in \tfrac12\mathbb Z - \mathbb Z$ then $\operatorname{cls}L = \operatorname{cls}K$ | `Lattices.omeara106_9` | proved |
| 106:10 | 330 | A unimodular lattice on $I_n$ with $1 \le n \le 7$ is $\cong I_n$ | `Lattices.omeara106_10_uncond` | proved |
| 106, text 6 | 331 | The matrix $\Phi_n$ ($n = 8, 12, 16, \dots$) built from the Cartan-type matrix $\Gamma_{n-3}$; the lattice $E$ spanned by $\tfrac12(x_1 + \cdots + x_n)$ and the lattice $D$ is unimodular, indecomposable, and all indecomposable unimodular lattices adjacent to $D$ are in one proper class | `Lattices.omearaE_indecomposable` | proved |
| 106:11 | 332 | $\sum A_ix_i \in E$ if and only if $A_i \in \tfrac12\mathbb Z$, $A_i - A_j \in \mathbb Z$, $\sum A_i \in 2\mathbb Z$; hence $E$ does not represent $1$ and is indecomposable | `Lattices.omeara106_11` | proved |
| 106:12 | 333–334 | For $n = 8$: every unimodular lattice adjacent to $E$ is in the class of $D$ or of $E$ | `Lattices.omeara106_12` | proved |
| 106:13 | 334–335 | Theorem: a unimodular lattice on a positive definite $V$ with $1 \le n \le 9$ is isometric to exactly one of $I_n$, $\Phi_8 \perp I_{n-8}$ | `Lattices.omeara106_13` | proved |
| 106, text 7 | 335 | Beyond $n = 9$: for $n \le 13$ the classes are $I_{n}$ and $\Phi_8 \perp I_{n-8}$ (via a result of Kneser); new indecomposable lattices appear in dimensions $14$, $15$, $16$ | `Lattices.omeara106_r38` | proved |
| 101.d1 | 297 | The subgroup $J_F^{L}$ of the idèle group $J_F$ of idèles $i$ with $i_{\mathfrak p} \in \theta(O^{+}(L_{\mathfrak p}))$ for all $\mathfrak p \in S$ (the notation is read from the scan, where it is garbled) | `Lattices.spinorIdeleGroup`, `Lattices.localSpinorNormGroup` | formalized (a definition, or used in proofs) |
| 105.d1 | 322 | A vector $x$ of a lattice $L$ is reducible when $x = y + z$ with non-zero $y, z \in L$ and $B(y,z) = 0$, and irreducible otherwise | `Lattices.IsReducibleVec` | formalized (a definition, or used in proofs) |
