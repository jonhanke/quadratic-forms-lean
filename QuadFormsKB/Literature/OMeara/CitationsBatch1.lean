import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF
import QuadFormsKB.Literature.HasseNorm.LocalIndexTwo
import QuadFormsKB.Literature.OMeara.Sec43C
import QuadFormsKB.Literature.OMeara.Sec43CD
import QuadFormsKB.Literature.OMeara.Sec43Center
import QuadFormsKB.Literature.OMeara.Sec43E
import QuadFormsKB.Literature.OMeara.Sec43Low
import QuadFormsKB.Literature.OMeara.Sec52B
import QuadFormsKB.Literature.OMeara.Sec52F
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec55Omega
import QuadFormsKB.Literature.OMeara.Sec57Iso
import QuadFormsKB.Literature.OMeara.Sec91
import QuadFormsKB.Literature.OMeara.Sec91Units
import QuadFormsKB.Binary.RelDensities
import QuadFormsKB.Binary.RelativeQuadratic
import QuadFormsKB.Defs.Hilbert
import QuadFormsKB.Defs.Integral
import QuadFormsKB.Defs.NumberField
import QuadFormsKB.Defs.QuadForm
import QuadFormsKB.Defs.Rational
import QuadFormsKB.Equiv.NumberFieldRat
import QuadFormsKB.Lattices.CartanDieudonne
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Lattices.FreeBridge
import QuadFormsKB.Lattices.Genus
import QuadFormsKB.Lattices.Local
import QuadFormsKB.Lattices.NeighborGenus
import QuadFormsKB.Lattices.SAEqualPairs
import QuadFormsKB.Lattices.SARotations
import QuadFormsKB.Lattices.SATernary
import QuadFormsKB.Lattices.SAWeak
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Lattices.SpinorNorm
import QuadFormsKB.Lattices.Steinitz
import QuadFormsKB.Lattices.StrongApproximationProof
import QuadFormsKB.Literature.Cassels.Ch11Sec1Criterion
import QuadFormsKB.Literature.Cassels.Ch11Sec1Indef
import QuadFormsKB.Literature.Cassels.Ch3.Basic
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.HasseNorm.FirstInequality
import QuadFormsKB.Literature.HasseNorm.KummerSquares
import QuadFormsKB.Literature.HasseNorm.LocalNorm
import QuadFormsKB.Literature.HasseNorm.Places
import QuadFormsKB.Literature.HasseNorm.Reciprocity
import QuadFormsKB.Literature.HasseNorm.SUnits
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNF
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.SquaresLocalGlobal
import QuadFormsKB.Literature.OMeara.Sec101A
import QuadFormsKB.Literature.OMeara.Sec101B
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.OMeara.Sec106E
import QuadFormsKB.Literature.OMeara.Sec11A
import QuadFormsKB.Literature.OMeara.Sec11B
import QuadFormsKB.Literature.OMeara.Sec12A
import QuadFormsKB.Literature.OMeara.Sec12B
import QuadFormsKB.Literature.OMeara.Sec14A
import QuadFormsKB.Literature.OMeara.Sec21
import QuadFormsKB.Literature.OMeara.Sec22
import QuadFormsKB.Literature.OMeara.Sec31
import QuadFormsKB.Literature.OMeara.Sec32A
import QuadFormsKB.Literature.OMeara.Sec33A
import QuadFormsKB.Literature.OMeara.Sec33B
import QuadFormsKB.Literature.OMeara.Sec41
import QuadFormsKB.Literature.OMeara.Sec42
import QuadFormsKB.Literature.OMeara.Sec42Iso
import QuadFormsKB.Literature.OMeara.Sec43CD
import QuadFormsKB.Literature.OMeara.Sec43Low
import QuadFormsKB.Literature.OMeara.Sec52A
import QuadFormsKB.Literature.OMeara.Sec52B
import QuadFormsKB.Literature.OMeara.Sec52F
import QuadFormsKB.Literature.OMeara.Sec54
import QuadFormsKB.Literature.OMeara.Sec54Dim
import QuadFormsKB.Literature.OMeara.Sec54Even
import QuadFormsKB.Literature.OMeara.Sec54Gap
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec57
import QuadFormsKB.Literature.OMeara.Sec57Iso
import QuadFormsKB.Literature.OMeara.Sec58Bases
import QuadFormsKB.Literature.OMeara.Sec58Hasse
import QuadFormsKB.Literature.OMeara.Sec61B
import QuadFormsKB.Literature.OMeara.Sec62
import QuadFormsKB.Literature.OMeara.Sec62Gap
import QuadFormsKB.Literature.OMeara.Sec63C
import QuadFormsKB.Literature.OMeara.Sec63D
import QuadFormsKB.Literature.OMeara.Sec65A
import QuadFormsKB.Literature.OMeara.Sec65B
import QuadFormsKB.Literature.OMeara.Sec65D
import QuadFormsKB.Literature.OMeara.Sec81
import QuadFormsKB.Literature.OMeara.Sec81Adapted
import QuadFormsKB.Literature.OMeara.Sec81Change
import QuadFormsKB.Literature.OMeara.Sec81Invariant
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Literature.OMeara.Sec82Free
import QuadFormsKB.Literature.OMeara.Sec82Isom
import QuadFormsKB.Literature.OMeara.Sec82Local
import QuadFormsKB.Literature.OMeara.Sec82Modular
import QuadFormsKB.Literature.OMeara.Sec82Sub
import QuadFormsKB.Literature.OMeara.Sec82Volume
import QuadFormsKB.Literature.OMeara.Sec91
import QuadFormsKB.Literature.OMeara.Sec91Chain
import QuadFormsKB.Literature.OMeara.Sec91Jordan
import QuadFormsKB.Literature.OMeara.Sec91Max
import QuadFormsKB.Literature.OMeara.Sec91Max3
import QuadFormsKB.Literature.OMeara.Sec91MaxA
import QuadFormsKB.Literature.OMeara.Sec91Type
import QuadFormsKB.Literature.OMeara.Sec92
import QuadFormsKB.Literature.OMeara.Sec92Cancel
import QuadFormsKB.Literature.OMeara.Sec92Class
import QuadFormsKB.Literature.OMeara.Sec93
import QuadFormsKB.Literature.OMeara.Sec93Gap
import QuadFormsKB.LocalDensity.DVR
import QuadFormsKB.LocalDensity.DVRExplicit
import QuadFormsKB.LocalDensity.DVRLevel
import QuadFormsKB.LocalDensity.DyadicArf
import QuadFormsKB.LocalDensity.DyadicJordan
import QuadFormsKB.LocalDensity.Explicit
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.EvenUnimodularRank
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Siegel.NFDyadicGood
import QuadFormsKB.Tamagawa.BinaryCMLocalType
import QuadFormsKB.Tamagawa.BlockForm
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Tamagawa.Indefinite.OneClass
import QuadFormsKB.Tamagawa.LatticeChange
import QuadFormsKB.Tamagawa.LocalVolume
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveScaling
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicMinkowski
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinUnits
import QuadFormsKB.Tamagawa.Measure.Weil.SpaceHeadlines
import QuadFormsKB.Tamagawa.OrbitHensel
import QuadFormsKB.Tamagawa.QuatOrderGlobal
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Tamagawa.QuaternionSO3
import QuadFormsKB.Tamagawa.Reflection
import QuadFormsKB.Tamagawa.SiegelClassical
import QuadFormsKB.Tamagawa.SiegelGenusV
import QuadFormsKB.Tamagawa.SiegelSpaceChars
import QuadFormsKB.Weil.Genus.EightDvd
import QuadFormsKB.Weil.ProductFormulas
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Witt.Cancellation
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Witt.Extension

/-!
# O'Meara: citations for declarations elsewhere in the library (first part)

Locators of the 1973 printing, added with `attribute [kb …]` so that the files where the
declarations live are unchanged (tags only: no statement or proof changes).
-/

attribute [kb "omeara1963" "§11B, 11:1 (sufficiency), p. 4 (statement: special case (one direction))"] QuadFormsKB.OMeara.isNonarchimedean_of_natCast_le
attribute [kb "omeara1963" "§11B, 11:2, p. 4 (proof route)"] QuadFormsKB.OMeara.domination_sum_aux
attribute [kb "omeara1963" "§11A, p. 2 (valuated field containing $\\mathbb Q$ is archimedean) (statement: special case ($\\mathbb Q$))"] QuadFormsKB.OMeara.real_not_nonarchimedean
attribute [kb "omeara1963" "§11C, p. 7 ($\\lvert \\ \\rvert ^{\\varrho}$ non-archimedean) (definition)"] QuadFormsKB.OMeara.rpowAbs
attribute [kb "omeara1963" "§11D, p. 7 (spots equal iff topologies agree) (statement: special case)"] QuadFormsKB.OMeara.equivalent_valuations_tfae
attribute [kb "omeara1963" "§11D, 11:6, p. 7 (topological isomorphism) (definition)"] QuadFormsKB.OMeara.IsTopologicalIso
attribute [kb "omeara1963" "§11G, 11:18, p. 13 (proof route)"] QuadFormsKB.OMeara.prolongation_formula
attribute [kb "omeara1963" "§11F, 11:9, p. 9 (series over a complete non-archimedean field) (statement: special case ($\\mathbb Q_p$))"] QuadFormsKB.Cassels.padic_summable_iff
attribute [kb "omeara1963" "§12, 12:1, p. 14 (proof route)"] QuadFormsKB.OMeara.rat_archimedean_equiv_real
attribute [kb "omeara1963" "§12, 12:1 (existence), p. 14 (statement: special case)"] QuadFormsKB.OMeara.real_not_nonarchimedean
attribute [kb "omeara1963" "§12, 12:5, p. 19 (proof route)"] QuadFormsKB.OMeara.two_rpow_eq_two
attribute [kb "omeara1963" "§12, 12:9, p. 19 (definition)"] QuadFormsKB.OMeara.normalizedSpotAbs_of_real
attribute [kb "omeara1963" "§12, 12:9, p. 19 (definition)"] QuadFormsKB.OMeara.normalizedSpotAbs_of_complex
attribute [kb "omeara1963" "§12, 12:10, p. 19 (proof route)"] QuadFormsKB.OMeara.sq_sum_le
attribute [kb "omeara1963" "§12, 12:4 (case $\\lvert m\\rvert = m$), p. 17 (proof route)"] QuadFormsKB.OMeara.ordinary_ratCast
attribute [kb "omeara1963" "§12, 12:4, p. 17 (proof route)"] QuadFormsKB.OMeara.isCompletion_rat_real
attribute [kb "omeara1963" "§12, 12:13, p. 20 (the prime field $\\mathbb Q$) (statement: special case)"] QuadFormsKB.OMeara.rat_archimedean_spot_unique
attribute [kb "omeara1963" "§12, 12:4 (steps 4–5), pp. 17–18 (proof route)"] QuadFormsKB.OMeara.norm_eq_of_algEquiv_complex
attribute [kb "omeara1963" "§13A, p. 20 (the group of units $\\mathfrak u(\\mathfrak p)$ of a completion) (statement: special case)"] QuadFormsKB.HN.U0
attribute [kb "omeara1963" "§13A, p. 20 (the group of units $\\mathfrak u(\\mathfrak p)$ of a completion) (statement: special case)"] QuadFormsKB.HN.mem_U0
attribute [kb "omeara1963" "§13A, p. 21 (the maximal ideal $\\mathfrak m(\\mathfrak p)$, completion of a number field) (statement: special case)"] QuadFormsKB.HN.mem_maximalIdeal_iff
attribute [kb "omeara1963" "§13B, 13:5 (1), p. 23 (statement: special case)"] QuadFormsKB.HN.card_residueField
attribute [kb "omeara1963" "§13B, 13:5 (1), p. 23 ($k=1$) (statement: special case)"] QuadFormsKB.LocalDensity.NF.quotEquiv
attribute [kb "omeara1963" "§13B, p. 22 (ramification index); §16, 16:2 (statement: special case)"] QuadFormsKB.HN.ordTwo_liesOver
attribute [kb "omeara1963" "§13B, 13:6, p. 24 ($n=2$, global primes) (statement: special case)"] QuadFormsKB.HN.sum_ef
attribute [kb "omeara1963" "§13A, 13:3, p. 21 (congruences) (statement: special case)"] QuadFormsKB.LocalDensity.NF.sModEq_iff_valued
attribute [kb "omeara1963" "§13D, 13:8, p. 26 (case $i=1$) (statement: special case)"] QuadFormsKB.QuatOrder.henselianLocalRing_adicCompletionIntegers
attribute [kb "omeara1963" "§13D, 13:8, p. 26 (case $i=1$) (statement: special case)"] QuadFormsKB.Tamagawa.BinaryCM.henselian_adicCompletionIntegers'
attribute [kb "omeara1963" "§13D, p. 26 (completeness hypothesis of Hensel's lemma) (background)"] QuadFormsKB.LocalDensity.NF.isAdicComplete
attribute [kb "omeara1963" "§13D, 13:8, step 2, p. 27 (variant) (proof route)"] QuadFormsKB.LocalDensity.DVR.newton_step
attribute [kb "omeara1963" "§14, 14:1, pp. 28–29 (components of the theorem: extends / unique / complete / norm formula) (statement: special case (complete non-trivial non-archimedean $F$))"] QuadFormsKB.OMeara.spectralAbs_extends
attribute [kb "omeara1963" "§14, 14:1, pp. 28–29 (components of the theorem: extends / unique / complete / norm formula) (statement: special case (complete non-trivial non-archimedean $F$))"] QuadFormsKB.OMeara.eq_spectralAbs_of_extends
attribute [kb "omeara1963" "§14, 14:1, pp. 28–29 (components of the theorem: extends / unique / complete / norm formula) (statement: special case (complete non-trivial non-archimedean $F$))"] QuadFormsKB.OMeara.completeSpace_spectralAbs
attribute [kb "omeara1963" "§14, 14:1, pp. 28–29 (components of the theorem: extends / unique / complete / norm formula) (statement: special case (complete non-trivial non-archimedean $F$))"] QuadFormsKB.OMeara.spectralNorm_eq_norm_rpow
attribute [kb "omeara1963" "§15A, p. 30 (every spot of $F$ is divisible by a spot of $E$) (statement: special case (finite primes of number fields))"] QuadFormsKB.HN.exists_over
attribute [kb "omeara1963" "§15A, p. 30 ($F_\\mathfrak P\\to E_\\mathfrak P$, $E_\\mathfrak P=F_\\mathfrak P E$) (statement: variant (quadratic extension))"] QuadFormsKB.HN.compMap
attribute [kb "omeara1963" "§15A, p. 30 ($F_\\mathfrak P\\to E_\\mathfrak P$, $E_\\mathfrak P=F_\\mathfrak P E$) (statement: variant (quadratic extension))"] QuadFormsKB.HN.tensorToCompletion_surjective
attribute [kb "omeara1963" "§15A, p. 31 (at most $n$ spots) and §15C, 15:10 (3) (quadratic case) (statement: special case)"] QuadFormsKB.HN.sum_ef
attribute [kb "omeara1963" "§15A, p. 31 (at most $n$ spots) and §15C, 15:10 (3) (quadratic case) (statement: special case)"] QuadFormsKB.HN.ef_of_two
attribute [kb "omeara1963" "§15B, pp. 32–33 (the local norm, as the norm of $F_\\mathfrak p\\otimes_FE$) (definition / background)"] QuadFormsKB.HN.tensor_structure
attribute [kb "omeara1963" "§15B, pp. 32–33 (the local norm, as the norm of $F_\\mathfrak p\\otimes_FE$) (definition / background)"] QuadFormsKB.HN.index_norm_eq_two
attribute [kb "omeara1963" "§15B, 15:8, p. 35 (quadratic extensions at infinite places) (statement: special case)"] QuadFormsKB.HN.SplitsInf
attribute [kb "omeara1963" "§15B, 15:8, p. 35 (quadratic extensions at infinite places) (statement: special case)"] QuadFormsKB.HN.card_infinitePlace_add
attribute [kb "omeara1963" "§16, p. 37 (discrete valuation: value group $\\exp\\mathbb Z$) (definition / statement: special case)"] QuadFormsKB.HN.exists_exp_eq
attribute [kb "omeara1963" "§16, p. 37 (discrete valuation: value group $\\exp\\mathbb Z$) (definition / statement: special case)"] QuadFormsKB.HN.valued_le_exp_neg_one
attribute [kb "omeara1963" "§16, p. 38 (prime elements and valuations) (statement: special case)"] QuadFormsKB.LocalDensity.NF.irreducible_of_valued
attribute [kb "omeara1963" "§16, p. 38 (prime elements and valuations) (statement: special case)"] QuadFormsKB.LocalDensity.NF.irreducible_π
attribute [kb "omeara1963" "§16, p. 38 (prime elements and valuations) (statement: special case)"] QuadFormsKB.HN.irreducible_ϖO
attribute [kb "omeara1963" "§16, p. 38 ($\\mathfrak m=\\pi\\mathfrak o$) (statement: special case)"] QuadFormsKB.LocalDensity.NF.span_π_pow
attribute [kb "omeara1963" "§16, p. 38 ($\\mathfrak m=\\pi\\mathfrak o$) (statement: special case)"] QuadFormsKB.LocalDensity.NF.mem_span_π_pow
attribute [kb "omeara1963" "§16, p. 38 (the order function $\\operatorname{ord}_\\mathfrak p$ and its rules) (statement: variant (elements of the ring, exponent in $\\mathbb N$))"] QuadFormsKB.LocalDensity.DVR.dvr_eq_pow_mul_unit
attribute [kb "omeara1963" "§16, p. 38 (the order function $\\operatorname{ord}_\\mathfrak p$ and its rules) (statement: variant (elements of the ring, exponent in $\\mathbb N$))"] QuadFormsKB.LocalDensity.DVR.dvr_exact
attribute [kb "omeara1963" "§16, p. 38 (the order function $\\operatorname{ord}_\\mathfrak p$ and its rules) (statement: variant (elements of the ring, exponent in $\\mathbb N$))"] QuadFormsKB.Tamagawa.LatChange.ord
attribute [kb "omeara1963" "§16, p. 38 (the order function $\\operatorname{ord}_\\mathfrak p$ and its rules) (statement: variant (elements of the ring, exponent in $\\mathbb N$))"] QuadFormsKB.Tamagawa.LatChange.exists_eq_ord
attribute [kb "omeara1963" "§16, p. 38 (the order function $\\operatorname{ord}_\\mathfrak p$ and its rules) (statement: variant (elements of the ring, exponent in $\\mathbb N$))"] QuadFormsKB.Tamagawa.LatChange.eq_of_pow_mul_unit
attribute [kb "omeara1963" "§16, p. 38 (the order function $\\operatorname{ord}_\\mathfrak p$ and its rules) (statement: variant (elements of the ring, exponent in $\\mathbb N$))"] QuadFormsKB.Tamagawa.LatChange.ord_mul
attribute [kb "omeara1963" "§16, 16:2, p. 38 (statement: special case)"] QuadFormsKB.HN.ordTwo_liesOver
attribute [kb "omeara1963" "§16, 16:4, p. 40 ($n=2$) (statement: special case)"] QuadFormsKB.HN.ef_of_unique
attribute [kb "omeara1963" "§16, 16:4, p. 40 ($n=2$) (statement: special case)"] QuadFormsKB.HN.sum_ef
attribute [kb "omeara1963" "§16, p. 39 (representative set of the residue class field) (background)"] QuadFormsKB.HN.exists_int_approx
attribute [kb "omeara1963" "§21, p. 42 (definition of $\\mathfrak o(S)$) (statement: special case (first conjunct))"] QuadFormsKB.OMeara.ringOfIntegers_eq_and_isFractionRing
attribute [kb "omeara1963" "§21, p. 42 (a single discrete spot, or a finite set satisfying (D1), is Dedekind) (statement: special case)"] QuadFormsKB.OMeara.dedekindAxiomsOn_of_nonempty
attribute [kb "omeara1963" "§21, p. 42, (D2) (definition (axiom (D2) for primes of a Dedekind domain))"] QuadFormsKB.OMeara.valuation_le_one_cofinite
attribute [kb "omeara1963" "§21, p. 42, (D3) (definition (axiom (D3) for primes of a Dedekind domain))"] QuadFormsKB.OMeara.exists_approx_pair
attribute [kb "omeara1963" "§22B, p. 45 (definition of $\\lvert\\mathfrak a\\rvert_{\\mathfrak p}$)"] QuadFormsKB.OMeara.idealAbs
attribute [kb "omeara1963" "§22A, p. 45 (the sum, intersection and product of fractional ideals are non-zero)"] QuadFormsKB.OMeara.sup_ne_zero'
attribute [kb "omeara1963" "§22A, p. 45 (the sum, intersection and product of fractional ideals are non-zero)"] QuadFormsKB.OMeara.inf_ne_zero'
attribute [kb "omeara1963" "§22A, p. 45 (the sum, intersection and product of fractional ideals are non-zero)"] QuadFormsKB.OMeara.spanSingleton_ne_zero'
attribute [kb "omeara1963" "§22B, p. 45 ($\\lvert\\mathfrak a\\mathfrak b\\rvert_{\\mathfrak p}=\\lvert\\mathfrak a\\rvert_{\\mathfrak p}\\lvert\\mathfrak b\\rvert_{\\mathfrak p}$, additive form)"] QuadFormsKB.OMeara.ord_mul
attribute [kb "omeara1963" "§22B, p. 45 ($\\lvert\\mathfrak a+\\mathfrak b\\rvert_{\\mathfrak p}=\\max$) and §22C, p. 50 ($\\mathfrak a+\\mathfrak b=\\prod\\mathfrak p^{\\min}$)"] QuadFormsKB.OMeara.count_sup
attribute [kb "omeara1963" "§22B, pp. 45–46 ($\\lvert\\mathfrak a\\cap\\mathfrak b\\rvert_{\\mathfrak p}=\\min$) and §22C, p. 50 ($\\mathfrak a\\cap\\mathfrak b=\\prod\\mathfrak p^{\\max}$)"] QuadFormsKB.OMeara.count_inf
attribute [kb "omeara1963" "§22C, p. 50 (a ⊆ b iff ν_p ≤ μ_p); also §22B, 22:1 (2)"] QuadFormsKB.OMeara.le_iff_forall_count
attribute [kb "omeara1963" "§22B, p. 45 (maximum attained) / 22:1 (1) (proof route)"] QuadFormsKB.OMeara.mem_iff_valuation_le
attribute [kb "omeara1963" "§22B, p. 45 (maximum attained) / 22:1 (1) (proof route)"] QuadFormsKB.OMeara.valuation_le_idealAbs
attribute [kb "omeara1963" "§22B, p. 45 (maximum attained) / 22:1 (1) (proof route)"] QuadFormsKB.OMeara.exists_mem_valuation_eq
attribute [kb "omeara1963" "§22D, p. 51 ($\\mathfrak o/\\mathfrak p\\cong$ residue class field; $k=1$) (statement: generalization (all $k$, completion))"] QuadFormsKB.LocalDensity.NF.quotEquiv
attribute [kb "omeara1963" "§22D, p. 51 (surjectivity onto the residue field) (statement: special case)"] QuadFormsKB.Binary.Rel.residue_ι_surjective
attribute [kb "omeara1963" "§31, p. 55 (rational function field k(x); k arbitrary) (definition)"] QuadFormsKB.OMeara.ratFunc_dedekindAxioms
attribute [kb "omeara1963" "§31, 31:1 (ii), p. 56 (the spots of $\\mathbb Q$ are all different, and are $\\infty$ and the primes) (statement: special case (over $\\mathbb Q$ only))"] QuadFormsKB.NFPlace.toRatPlace_bijective
attribute [kb "omeara1963" "§31, 31:5, p. 57 (discrete spot of $\\mathbb Q_p$) (statement: special case)"] QuadFormsKB.OMeara.isLocalFieldSpot_padic
attribute [kb "omeara1963" "§31, 31:1, p. 56 (archimedean half, for $\\mathbb Q$) (statement: special case)"] QuadFormsKB.OMeara.rat_archimedean_spot_unique
attribute [kb "omeara1963" "§31, p. 55 (finite spots and $\\infty$ of $\\mathbb Q$) (definition)"] QuadFormsKB.RatPlace
attribute [kb "omeara1963" "§31, p. 55 and §12 (spots of a number field) (definition)"] QuadFormsKB.NFPlace
attribute [kb "omeara1963" "§32A, p. 59 (definition of $N\\mathfrak p$)"] QuadFormsKB.OMeara.normPrime
attribute [kb "omeara1963" "§32A, p. 59 ($N\\mathfrak p$ is the same on the completion)"] QuadFormsKB.HN.card_residueField
attribute [kb "omeara1963" "§32A, 32:5, p. 60 ($(\\mathfrak o:\\mathfrak p^\\nu)=(N\\mathfrak p)^\\nu$; global form) (statement: special case)"] QuadFormsKB.LocalDensity.NF.card_quot_π_pow
attribute [kb "omeara1963" "§32A, 32:3 (2), p. 60 (global quadratic case) (statement: special case)"] QuadFormsKB.Binary.Rel.absNorm_eq_pow_inertiaDeg
attribute [kb "omeara1963" "§32B, p. 60 ($ef=n$, global quadratic case) (statement: special case)"] QuadFormsKB.Binary.Rel.sum_ramificationIdx_mul_inertiaDeg
attribute [kb "omeara1963" "§33B, 33:1, p. 66 (product formula) (statement: special case)"] QuadFormsKB.WeilRep.prod_modulus_eq_one
attribute [kb "omeara1963" "§33A, p. 65 (normalized valuations) (definition)"] QuadFormsKB.OMeara.normalizedAbs
attribute [kb "omeara1963" "§33B, 33:1, p. 66 (product formula, $F = \\mathbb Q$) (statement: special case)"] QuadFormsKB.Cassels.product_formula
attribute [kb "omeara1963" "§33A, p. 65 (normalized valuation) (background)"] QuadFormsKB.WeilRep.modK_eq_norm
attribute [kb "omeara1963" "§33D, p. 68 (volume of an idèle) (definition)"] QuadFormsKB.Tamagawa.Measure.Weil.ideleNorm
attribute [kb "omeara1963" "§33E, 33:5, p. 70 (statement: special case)"] QuadFormsKB.Tamagawa.Measure.Weil.adelicMinkowski_idele
attribute [kb "omeara1963" "§33E, 33:5, p. 70 (statement: special case)"] QuadFormsKB.Tamagawa.Measure.Weil.exists_isCompact_forall_idele_smul_mem
attribute [kb "omeara1963" "§33F, p. 73 (the group of S-units) (definition)"] QuadFormsKB.HN.SUnit
attribute [kb "omeara1963" "§33F, 33:10, p. 77 (rank of the S-units) (statement: special case)"] QuadFormsKB.HN.finrank_sUnit
attribute [kb "omeara1963" "§33H, 33:13a, p. 80 (proof route)"] QuadFormsKB.HN.exists_classGroup_generators
attribute [kb "omeara1963" "§33G, proof of 33:11, p. 77 (background)"] QuadFormsKB.OMeara.weak_approximation
attribute [kb "omeara1963" "§33I, p. 80 (F^× ≅ P_F) (statement: special case)"] QuadFormsKB.OMeara.unitEmbedding_injective
attribute [kb "omeara1963" "§41A, p. 83 ($Q(ax)=a^2Q(x)$)"] QuadFormsKB.OMeara.Q_smul
attribute [kb "omeara1963" "§41A, p. 83 ($Q(x+y)=Q(x)+Q(y)+2B(x,y)$)"] QuadFormsKB.OMeara.Q_add
attribute [kb "omeara1963" "§41A, p. 83 ($Q(ax)=a^2Q(x)$)"] QuadFormsKB.QuadForm.evalIn_smul
attribute [kb "omeara1963" "§41A, p. 83 (scaling $B^a=aB$)"] QuadFormsKB.OMeara.iv_bil_smul_form
attribute [kb "omeara1963" "§41A, p. 84 ($B(\\sigma x,\\sigma y)=B(x,y)$)"] QuadFormsKB.OMeara.rep_iff_compl₁₂
attribute [kb "omeara1963" "§41A, p. 82 ($B$ symmetric, $Q(x)=B(x,x)$)"] QuadFormsKB.OMeara.bil_self
attribute [kb "omeara1963" "§41A, p. 82 ($B$ symmetric, $Q(x)=B(x,x)$)"] QuadFormsKB.OMeara.bil_comm
attribute [kb "omeara1963" "§41B, p. 85 (matrix of a space)"] QuadFormsKB.OMeara.gram_eq_toMatrix₂
attribute [kb "omeara1963" "§41B, 41:3, p. 87 ($V^a\\cong aN$)"] QuadFormsKB.OMeara.iv_gram_smul
attribute [kb "omeara1963" "§41B, p. 87 (discriminant independent of the base) (statement: special case)"] QuadFormsKB.Tamagawa.SiegelSpace.hessDetV_eq_basis
attribute [kb "omeara1963" "§41B, p. 86 (notation $\\langle N\\rangle$) and §41C, p. 88 (definition)"] QuadFormsKB.QuadForm.diag
attribute [kb "omeara1963" "§41B, p. 86 (notation $\\langle N\\rangle$) and §41C, p. 88 (definition)"] QuadFormsKB.QuadForm.hessian
attribute [kb "omeara1963" "§41C, p. 88 (equivalence of forms by substitution) (definition)"] QuadFormsKB.QuadForm.IsometricIn
attribute [kb "omeara1963" "§41C, pp. 87–88 (a quadratic form) (definition)"] QuadFormsKB.QuadForm
attribute [kb "omeara1963" "§42A, p. 88 (orthogonal splitting) (definition)"] QuadFormsKB.OMeara.PairwiseOrth
attribute [kb "omeara1963" "§42A, p. 89 ($d(V_1 \\perp V_2) = dV_1\\,dV_2$) (statement: special case (two blocks))"] QuadFormsKB.Tamagawa.Frames.det_hessian_blockForm
attribute [kb "omeara1963" "§42A, p. 89 (discriminant of an orthogonal base) (statement: special case)"] QuadFormsKB.OMeara.Sp55.det_gram_orthogonal
attribute [kb "omeara1963" "§42A, p. 90 (orthogonal base) (definition)"] QuadFormsKB.OMeara.IsOrthogonalBasis
attribute [kb "omeara1963" "§42A, 42:1, p. 90 (statement: generalization (nondegenerate, anisotropic vectors))"] QuadFormsKB.Lattices.exists_orthogonal_basis
attribute [kb "omeara1963" "§42B, p. 91 (radical) (definition)"] QuadFormsKB.OMeara.splitComp
attribute [kb "omeara1963" "§42B, 42:4, p. 91 (a regular subspace splits)"] QuadFormsKB.OMeara.Sp55.isCompl_perp
attribute [kb "omeara1963" "§42D, p. 94 (hyperbolic planes: isometric, regular, $d = -1$) (statement: special case)"] QuadFormsKB.OMeara.isHyperbolicPlane_tfae
attribute [kb "omeara1963" "§42D, 42:10, p. 95 (a regular isotropic space is universal)"] QuadFormsKB.OMeara.exists_eq_of_isotropic'
attribute [kb "omeara1963" "§42D, proof of 42:10 and 42:13, p. 95"] QuadFormsKB.OMeara.exists_hyp_partner
attribute [kb "omeara1963" "§42D, 42:10, p. 95 (statement: generalization (all characteristic))"] QuadraticForm.Witt.exists_split_hyperbolicPlane
attribute [kb "omeara1963" "§42E, p. 97 (a symmetry is an involution, reverses $Fy$, fixes $(Fy)^\\perp$)"] QuadFormsKB.OMeara.symmetry_symmetry
attribute [kb "omeara1963" "§42E, p. 97 (a symmetry is an involution, reverses $Fy$, fixes $(Fy)^\\perp$)"] QuadFormsKB.OMeara.symmetry_apply
attribute [kb "omeara1963" "§42E, p. 97 (a symmetry is an involution, reverses $Fy$, fixes $(Fy)^\\perp$)"] QuadFormsKB.OMeara.iv_symmetry_self_apply
attribute [kb "omeara1963" "§42E, p. 97 ($\\tau_y = \\tau_{y'}$ iff the lines agree) (statement: special case ($\\Leftarrow$))"] QuadFormsKB.OMeara.Sp55.symmetry_smul_vec
attribute [kb "omeara1963" "§42E, p. 97 ($\\sigma\\tau_y\\sigma^{-1} = \\tau_{\\sigma y}$; $\\tau_y \\in O(V)$)"] QuadFormsKB.OMeara.Sp55.conj_symmetry
attribute [kb "omeara1963" "§42E, p. 97 ($\\sigma\\tau_y\\sigma^{-1} = \\tau_{\\sigma y}$; $\\tau_y \\in O(V)$)"] QuadFormsKB.OMeara.symmetry_mem_orth
attribute [kb "omeara1963" "§42F, 42:16, p. 97 (Witt cancellation) (statement: generalization)"] QuadraticForm.equivalent_of_prod_equivalent_prod
attribute [kb "omeara1963" "§42F, 42:16, p. 97 (Witt cancellation) (statement: generalization)"] QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate
attribute [kb "omeara1963" "§42F, 42:17, p. 98 (statement: generalization (arbitrary radical))"] QuadraticForm.exists_isometryEquiv_extend
attribute [kb "omeara1963" "§42F, p. 99 (index, splitting off hyperbolic planes) (statement: variant)"] QuadraticForm.wittIndex
attribute [kb "omeara1963" "§42F, p. 99 (index, splitting off hyperbolic planes) (statement: variant)"] QuadraticForm.exists_wittDecomposition
attribute [kb "omeara1963" "§42F, p. 99 (index, splitting off hyperbolic planes) (statement: variant)"] QuadraticForm.wittDecomposition_unique
attribute [kb "omeara1963" "§42F, p. 99 (index, splitting off hyperbolic planes) (statement: variant)"] QuadraticForm.eq_wittIndex
attribute [kb "omeara1963" "§42F, p. 99 (hyperbolic space) (definition)"] QuadraticForm.hyperbolicSpace
attribute [kb "omeara1963" "§43A, p. 100 ($\\det\\sigma = \\pm1$)"] QuadFormsKB.OMeara.det_orth_eq
attribute [kb "omeara1963" "§43A, p. 100 ($\\det\\sigma = \\pm1$)"] QuadFormsKB.Tamagawa.det_eq_one_or_neg_one
attribute [kb "omeara1963" "§43A, p. 100 (rotations) (definition)"] QuadFormsKB.Tamagawa.mem_soSub
attribute [kb "omeara1963" "§43, p. 101 ($(O_n : O^+_n) = 2$) (statement: special case)"] QuadFormsKB.Tamagawa.exists_orthGroup_det_neg_one
attribute [kb "omeara1963" "§43B, proof of 43:3, step 1, pp. 102–103"] QuadFormsKB.OMeara.cd_star_even_det
attribute [kb "omeara1963" "§43B, p. 103 (fixed space) (definition)"] QuadFormsKB.OMeara.fixSp
attribute [kb "omeara1963" "§43B, p. 103 (fixed space) (definition)"] QuadFormsKB.OMeara.fixRank
attribute [kb "omeara1963" "§43B, footnote p. 102 (bound $2n$) (statement: special case)"] QuadFormsKB.OMeara.exists_symmetry_prod_eq
attribute [kb "omeara1963" "§43C, 43:4, p. 105 ($n \\le 3$ rotations) (statement: special case)"] QuadFormsKB.OMeara.exists_symmetry_prod_eq_length_le_two
attribute [kb "omeara1963" "§43C, 43:4, p. 105 ($d = n - 1$) (proof route)"] QuadFormsKB.OMeara.exists_cd_prod_eq_of_fix_hyperplane
attribute [kb "omeara1963" "§43C, p. 104 ($O^+_2$ commutative)"] QuadFormsKB.OMeara.orthPlus_comm_of_finrank_le_two
attribute [kb "omeara1963" "§43C, p. 105 (announced)"] QuadFormsKB.OMeara.orthPlus_not_comm_of_three_le
attribute [kb "omeara1963" "§43D, p. 106 ($\\Omega_n \\subseteq O^+_n$)"] QuadFormsKB.OMeara.omega_le_orthPrime
attribute [kb "omeara1963" "§43D, p. 106 ($\\Omega_n \\subseteq O^+_n$)"] QuadFormsKB.OMeara.orthPrime_le_orthPlus
attribute [kb "omeara1963" "§43D, 43:6 (c), p. 107 ($\\supseteq$) (statement: special case)"] QuadFormsKB.OMeara.sq_mem_omega_of_mem_orthPlus
attribute [kb "omeara1963" "§43D, 43:8 (iii), p. 108 (statement: generalization ($n \\le 3$))"] QuadFormsKB.OMeara.omega_eq_sq_orthPlus
attribute [kb "omeara1963" "§42D/§43, background"] QuadFormsKB.OMeara.hyperbolic_Q_sub_smul
attribute [kb "omeara1963" "§51A, p. 114 (every vector of $U \\otimes V$ is $\\sum u_\\mu \\otimes y_\\mu$) (statement: special case)"] QuadFormsKB.OMeara.sum_tensorCoeff_tmul
attribute [kb "omeara1963" "§51B, p. 117 ($F \\otimes A \\cong A$) (statement: special case (other side))"] QuadFormsKB.OMeara.CSA52.nonempty_algEquiv_tensor_one
attribute [kb "omeara1963" "§51B, pp. 117–118 ($A \\otimes B \\cong B \\otimes A$) (statement: special case)"] QuadFormsKB.OMeara.CSA52.nonempty_algEquiv_tensor_comm
attribute [kb "omeara1963" "§51B, p. 118 (associativity of $\\otimes$) (statement: special case)"] QuadFormsKB.OMeara.CSA52.nonempty_algEquiv_tensor_assoc
attribute [kb "omeara1963" "§52A, proof of 52:1, pp. 119–120 (unique expansion; minimal-length argument)"] QuadFormsKB.OMeara.tensorCoeff
attribute [kb "omeara1963" "§52A, proof of 52:1, pp. 119–120 (unique expansion; minimal-length argument)"] QuadFormsKB.OMeara.sum_tensorCoeff_tmul
attribute [kb "omeara1963" "§52A, proof of 52:1, pp. 119–120 (unique expansion; minimal-length argument)"] QuadFormsKB.OMeara.exists_eq_one_tmul_of_commute
attribute [kb "omeara1963" "§52A, proof of 52:1, pp. 119–120 (unique expansion; minimal-length argument)"] QuadFormsKB.OMeara.exists_one_tmul_mem_of_ne_zero
attribute [kb "omeara1963" "§52A, proof of 52:2, p. 120"] QuadFormsKB.OMeara.subalgebraTensorMap
attribute [kb "omeara1963" "§52A, proof of 52:2, p. 120"] QuadFormsKB.OMeara.range_subalgebraTensorMap
attribute [kb "omeara1963" "§52A, proof of 52:2, p. 120"] QuadFormsKB.OMeara.subalgebraTensorMap_injective
attribute [kb "omeara1963" "§52C, proof of 52:8, step 3, p. 124"] QuadFormsKB.OMeara.isSimpleModule_matrix_vec
attribute [kb "omeara1963" "§52C, proof of 52:8, step 3, p. 124"] QuadFormsKB.OMeara.vecEndAlgEquiv
attribute [kb "omeara1963" "§52C, proof of 52:8, step 3, p. 124"] QuadFormsKB.OMeara.vecRightMulAlgHom_bijective
attribute [kb "omeara1963" "§52C, proof of 52:8, step 3, p. 124"] QuadFormsKB.OMeara.exists_isAtom_end_algEquiv
attribute [kb "omeara1963" "§52B, 52:4, p. 121 (proof route)"] QuadFormsKB.OMeara.nonempty_linearEquiv_of_isSimpleModule
attribute [kb "omeara1963" "§52F, pp. 127–128 (definition of similarity $A \\sim A'$)"] QuadFormsKB.OMeara.isBrauerEquivalent_iff_nonempty_algEquiv
attribute [kb "omeara1963" "§52F, p. 128 ($A \\sim A'$ iff $A \\otimes M_r(F) \\cong A' \\otimes M_s(F)$)"] QuadFormsKB.OMeara.isBrauerEquivalent_iff_tensor
attribute [kb "omeara1963" "§52F, p. 128 ($A \\sim A'$ iff $A \\otimes M_r(F) \\cong A' \\otimes M_s(F)$)"] QuadFormsKB.OMeara.CSA52.isBrauerEquivalent_iff_tensor_matrix
attribute [kb "omeara1963" "§52F, p. 128 (splitting iff division component is $F$)"] QuadFormsKB.OMeara.splits_iff_nonempty_algEquiv_base
attribute [kb "omeara1963" "§52F, p. 128 ($A \\otimes B \\sim B \\otimes A$ etc.)"] QuadFormsKB.OMeara.CSA52.isBrauerEquivalent_tensor_comm
attribute [kb "omeara1963" "§52F, p. 128 ($A \\otimes B \\sim B \\otimes A$ etc.)"] QuadFormsKB.OMeara.CSA52.isBrauerEquivalent_tensor_one
attribute [kb "omeara1963" "§52F, p. 128 ($A \\otimes B \\sim B \\otimes A$ etc.)"] QuadFormsKB.OMeara.CSA52.isBrauerEquivalent_tensor_assoc
attribute [kb "omeara1963" "§52F, p. 128 (reciprocal algebra $A^*$) (definition)"] QuadFormsKB.OMeara.CSA52.op
attribute [kb "omeara1963" "§52C, 52:6, pp. 122–123"] QuadFormsKB.OMeara.CSA52.matrixTensorEquiv
attribute [kb "omeara1963" "§52F, footnote, p. 128 (the Brauer group) (statement: special case (monoid only))"] QuadFormsKB.OMeara.Hasse58.Br
attribute [kb "omeara1963" "§52F, proof of 52:10, pp. 128–129"] QuadFormsKB.OMeara.mulLeftRight_bijective
attribute [kb "omeara1963" "§53A, p. 129 ($V \\subseteq EV$) (statement: special case)"] QuadFormsKB.OMeara.Sp58.one_tmul_injective
attribute [kb "omeara1963" "§53C, p. 131 (the $E$-ification of a quadratic space, $E = F_\\mathfrak p$) in addition to the existing §66 tag (definition)"] QuadFormsKB.Tamagawa.SiegelSpace.locFormV
attribute [kb "omeara1963" "§53C, p. 131 ($V$ and $EV$ have the same matrix) (statement: special case)"] QuadFormsKB.Tamagawa.SiegelSpace.locFormV_eq_coord
attribute [kb "omeara1963" "§53C, p. 131 (the extended form is the unique one agreeing with $Q$) (background)"] QuadFormsKB.OMeara.Sp58.baseChange_tmul_add
attribute [kb "omeara1963" "§54, p. 132 (orthogonal vectors anticommute in a compatible algebra)"] QuadFormsKB.OMeara.CliffordDim.mul_eq_neg_mul_of_orth
attribute [kb "omeara1963" "§54, 54:2, p. 132 (the products $x_1^{e_1}\\cdots x_n^{e_n}$) (definition)"] QuadFormsKB.OMeara.CliffordDim.word
attribute [kb "omeara1963" "§54, 54:2, p. 132 (the products $x_1^{e_1}\\cdots x_n^{e_n}$) (definition)"] QuadFormsKB.OMeara.CliffordDim.wordSpan
attribute [kb "omeara1963" "§54, derived base, p. 135"] QuadFormsKB.OMeara.CliffordDim.derivedBasis
attribute [kb "omeara1963" "§54, derived base, p. 135"] QuadFormsKB.OMeara.CliffordDim.span_word_cliffordAlgebra
attribute [kb "omeara1963" "§54, 54:3"] QuadFormsKB.OMeara.isCliffordAlgebraOf_cliffordAlgebra
attribute [kb "omeara1963" "§54, p. 135 ($C^+$ spanned by even derived words)"] QuadFormsKB.OMeara.CliffordEven.even_toSubmodule_eq_span_word
attribute [kb "omeara1963" "§54, p. 135 ($C^+$ spanned by even derived words)"] QuadFormsKB.OMeara.CliffordEven.word_mem_evenOdd
attribute [kb "omeara1963" "§54, p. 135 ($\\dim C^+ = 2^{n-1}$, basis form)"] QuadFormsKB.OMeara.CliffordEven.finrank_even_of_basis
attribute [kb "omeara1963" "§54, proof of 54:6, p. 136"] QuadFormsKB.OMeara.Cl54.neg_ι_mul_ι
attribute [kb "omeara1963" "§54, proof of 54:6, p. 136"] QuadFormsKB.OMeara.Cl54.involute_cw_mul_ι
attribute [kb "omeara1963" "§54, proof of 54:6, p. 136"] QuadFormsKB.OMeara.Cl54.reverse_cw_mul_cw
attribute [kb "omeara1963" "§54, 54:4, p. 135 (twisted-centre route) (proof route)"] QuadFormsKB.OMeara.Cl54.mem_range_algebraMap_of_twisted
attribute [kb "omeara1963" "§55, 55:5, p. 140 ((O⁺_n)² ⊆ Ω_n)"] QuadFormsKB.OMeara.sq_mem_omega
attribute [kb "omeara1963" "§55, p. 138 (the symmetries $\\tau_u$ of $V$ and $V^a$ coincide)"] QuadFormsKB.OMeara.Sp55.symmetry_smul
attribute [kb "omeara1963" "§55, p. 138 (scaling changes $\\theta(\\tau_u)$ by $a$; rotations unchanged) (proof route)"] QuadFormsKB.OMeara.orthPrime_smul_le
attribute [kb "omeara1963" "§55, p. 137 (spinor norms are nonzero classes) (background)"] QuadFormsKB.OMeara.HasSpinorNorm.ne_zero
attribute [kb "omeara1963" "§55, p. 137 (spinor norms are nonzero classes) (background)"] QuadFormsKB.OMeara.HasSpinorNorm.one
attribute [kb "omeara1963" "§56, p. 141 ($O_n/O^+_n$ cyclic of order 2), replacing the 62:4 locator"] QuadFormsKB.OMeara.relIndex_orthPlus
attribute [kb "omeara1963" "§56, p. 141 (normal series) (background)"] QuadFormsKB.OMeara.orthPlus_subgroupOf_normal
attribute [kb "omeara1963" "§57A, p. 142 (pure quaternions) (definition)"] QuadFormsKB.OMeara.Quaternions57.pureSubmodule
attribute [kb "omeara1963" "§57A, p. 142 ($x_ix_j = -x_jx_i$) (statement: special case)"] QuadFormsKB.OMeara.QuatIso57.qJ_mul_qI
attribute [kb "omeara1963" "§57A, p. 142 ($x_ix_j = -x_jx_i$) (statement: special case)"] QuadFormsKB.OMeara.QuatIso57.qK_mul_qI
attribute [kb "omeara1963" "§57A, p. 143 (norm $Nx$) (definition)"] QuadFormsKB.Quat.nrd
attribute [kb "omeara1963" "§57A, p. 143 ($x\\bar x = Nx$)"] QuadFormsKB.Quat.mul_star_eq_nrd
attribute [kb "omeara1963" "§57A, p. 143 ($x\\bar x = Nx$)"] QuadFormsKB.Quat.star_mul_eq_nrd
attribute [kb "omeara1963" "§57A, p. 143 ($N\\bar x = Nx$)"] QuadFormsKB.Quat.nrd_star
attribute [kb "omeara1963" "§57A, p. 143 ($N(xy) = Nx\\,Ny$)"] QuadFormsKB.Quat.nrd_mul
attribute [kb "omeara1963" "§57A, p. 143 ($x^2 = -Nx$ for pure $x$) (statement: special case)"] QuadFormsKB.OMeara.QuatIso57.pure_mul_self
attribute [kb "omeara1963" "§57A, p. 143 ($x^2$ scalar iff $x$ scalar or pure) (statement: special case)"] QuadFormsKB.OMeara.Quaternions57.re_eq_zero_of_mul_self_scalar
attribute [kb "omeara1963" "§57B, p. 146 (scalars orthogonal to pure quaternions)"] QuadFormsKB.OMeara.QuatIso57.bil_scalar_pure
attribute [kb "omeara1963" "§57B, p. 146 (scalars orthogonal to pure quaternions)"] QuadFormsKB.OMeara.QuatIso57.nrdQuadraticForm_equivalent_prod
attribute [kb "omeara1963" "§57B, p. 146 ($B(x,y)=0 \\iff xy=-yx$ for pure $x,y$)"] QuadFormsKB.OMeara.QuatIso57.bil_pure_eq_zero_iff
attribute [kb "omeara1963" "§57B, p. 146 ($(\\alpha,\\beta)\\cong\\langle1,-\\alpha,-\\beta,\\alpha\\beta\\rangle$)"] QuadFormsKB.OMeara.QuatIso57.nrdQuadraticForm_equivalent_diag
attribute [kb "omeara1963" "§57B, p. 146 ($d(\\alpha,\\beta)=1$)"] QuadFormsKB.OMeara.QuatIso57.gram_det
attribute [kb "omeara1963" "§57, 57:7, p. 146 (proof route)"] QuadFormsKB.OMeara.QuatIso57.nonempty_algEquiv_of_sq
attribute [kb "omeara1963" "§57, 57:10 (4), proof, p. 148"] QuadFormsKB.OMeara.QuatIso57.equiv_tensor_of_subalgebras
attribute [kb "omeara1963" "§57, 57:13, p. 148 (first assertion: $\\sigma_y$ is a rotation)"] QuadFormsKB.Quat.conjGL_mem
attribute [kb "omeara1963" "§57, 57:13, p. 148 (first assertion: $\\sigma_y$ is a rotation)"] QuadFormsKB.Quat.conjSO
attribute [kb "omeara1963" "§57, 57:13, p. 149 (every rotation is some $\\sigma_y$)"] QuadFormsKB.Quat.conjSO_surjective
attribute [kb "omeara1963" "§57, 57:13, p. 149 (conjugation by a norm-1 quaternion has spinor norm 1) (statement: special case)"] QuadFormsKB.Lattices.mem_spinorKernel_of_conj
attribute [kb "omeara1963" "§57, 57:13, proof step 4, p. 149"] QuadFormsKB.Quat.ker_conjSO
attribute [kb "omeara1963" "§57, 57:4 and 57:9 ((3) $\\Rightarrow$ (1)), pp. 145–147 (statement: generalization)"] QuadFormsKB.Quat.nonempty_algEquiv_matrix_of_hilbertSymbol
attribute [kb "omeara1963" "§57, 57:10 (2), p. 147"] QuadFormsKB.OMeara.quatScaleEquiv
attribute [kb "omeara1963" "§57, 57:11, p. 148 (reciprocal) (proof route)"] QuadFormsKB.OMeara.CSA52.quaternionOpEquiv
attribute [kb "omeara1963" "§58, 58:1, proof steps 1 and 2, p. 150"] QuadFormsKB.OMeara.Sp58.exists_chain_first
attribute [kb "omeara1963" "§58, 58:1, proof steps 1 and 2, p. 150"] QuadFormsKB.OMeara.Sp58.chain_of_isOrthAniso
attribute [kb "omeara1963" "§58, 58:2, p. 151 (similarity version)"] QuadFormsKB.OMeara.Hasse58.isBrauerEquivalent_hasseAlg_values
attribute [kb "omeara1963" "§58, p. 150 (prefix versus suffix products) (proof route)"] QuadFormsKB.OMeara.Hasse58.cls_hasseAlg_eq
attribute [kb "omeara1963" "§61C, p. 156 (complex case, $\\Omega_n\\cap Z_n$) (statement: generalization)"] QuadFormsKB.OMeara.neg_mem_omega_iff
attribute [kb "omeara1963" "§61C, p. 157 (real case, $\\Omega_n\\cap Z_n$) (statement: generalization)"] QuadFormsKB.OMeara.neg_mem_orthPrime_iff
attribute [kb "omeara1963" "§61C, p. 157 (real case, $O_n'=\\Omega_n$) (statement: generalization)"] QuadFormsKB.OMeara.omega_eq_orthPrime
attribute [kb "omeara1963" "§61C, p. 157 (real case, $O_n'=\\Omega_n$) (statement: generalization)"] QuadFormsKB.OMeara.omega_eq_orthPrime_of_subspace
attribute [kb "omeara1963" "§61C, p. 157 (indefinite real $V$) (statement: generalization)"] QuadFormsKB.OMeara.orthPlus_quotient_equiv_of_isotropic
attribute [kb "omeara1963" "§61C, p. 157 (indefinite real $V$) (statement: generalization)"] QuadFormsKB.OMeara.exists_hasSpinorNorm_of_isotropic
attribute [kb "omeara1963" "§62, 62:4, p. 158 ($\\Omega_n\\cap Z_n$) (statement: generalization)"] QuadFormsKB.OMeara.neg_mem_omega_iff
attribute [kb "omeara1963" "§62, 62:4, p. 158 ($\\Omega_n\\cap Z_n$) (statement: generalization)"] QuadFormsKB.OMeara.neg_mem_orthPrime_iff
attribute [kb "omeara1963" "§62, 62:1, proof, p. 157"] QuadFormsKB.OMeara.exists_sq_add_sq_eq_one'
attribute [kb "omeara1963" "§63, p. 159 (dyadic iff $0 < \\lvert 2\\rvert < 1$) (definition)"] QuadFormsKB.HN.ordTwo
attribute [kb "omeara1963" "§63A, p. 162 ($1 + \\mathfrak p^{r+1} \\subseteq 1 + \\mathfrak p^r \\subseteq \\mathfrak u$)"] QuadFormsKB.HN.Ufil_anti
attribute [kb "omeara1963" "§63A, p. 162 ($1 + \\mathfrak p^{r+1} \\subseteq 1 + \\mathfrak p^r \\subseteq \\mathfrak u$)"] QuadFormsKB.HN.Ufil_le_U0
attribute [kb "omeara1963" "§63A, p. 162 ($1 + \\mathfrak p^r$ is a neighbourhood of $1$)"] QuadFormsKB.Tamagawa.Measure.Weil.isOpen_oneSub
attribute [kb "omeara1963" "§63A, 63:8 (2), p. 163 (statement: variant)"] QuadFormsKB.HN.sq_mem_Ufil_iff
attribute [kb "omeara1963" "§63A, 63:8 (1), p. 163 (the index $(N\\mathfrak p - 1)(N\\mathfrak p)^{r-1}$ through the residue field) (proof route)"] QuadFormsKB.HN.χ0_ker
attribute [kb "omeara1963" "§63A, 63:8 (1), p. 163 (the index $(N\\mathfrak p - 1)(N\\mathfrak p)^{r-1}$ through the residue field) (proof route)"] QuadFormsKB.HN.card_residueField
attribute [kb "omeara1963" "§63B, 63:12, p. 166 (over $\\mathbb Q_p$) (statement: special case)"] QuadFormsKB.HilbertLocal.hilbertSymbol_units
attribute [kb "omeara1963" "§63B, p. 166 (formulas of 57:10: invariance under squares)"] QuadFormsKB.PadicClass.hs_sq_left
attribute [kb "omeara1963" "§63B, p. 166 (formulas of 57:10: invariance under squares)"] QuadFormsKB.PadicClass.hs_sq_right
attribute [kb "omeara1963" "§63B, p. 166 (formulas of 57:10) (statement: special case)"] QuadFormsKB.RatPlace.hilbert_self
attribute [kb "omeara1963" "§63B, p. 166 (formulas of 57:10)"] QuadFormsKB.hilbertSymbol_comm
attribute [kb "omeara1963" "§63B, p. 166 (formulas of 57:10)"] QuadFormsKB.hilbertSymbol_self_neg
attribute [kb "omeara1963" "§63B, p. 166 (bimultiplicativity) (statement: special case)"] QuadFormsKB.HilbertLocal.hilbertSymbol_padic_mul_left
attribute [kb "omeara1963" "§63B, p. 166 (bimultiplicativity) (statement: special case)"] QuadFormsKB.NFLocal.hilbertSymbol_mul_left_infinite_nf
attribute [kb "omeara1963" "§63B, p. 167 (the two formulas for $S_\\mathfrak p V$ agree)"] QuadFormsKB.OMeara.hasseOMeara_finite_eq_hasseS
attribute [kb "omeara1963" "§63B, p. 167 ($S(U \\perp W)$, $U$ a line) (statement: special case)"] QuadFormsKB.PadicClass.hasseVec_cons_prod
attribute [kb "omeara1963" "§63C, 63:17 and 63:18, pp. 169–170 (statement: special case)"] QuadFormsKB.PadicClass.isotropic_four_iff_common
attribute [kb "omeara1963" "§63B, 63:11b, p. 165 (proof route)"] QuadFormsKB.OMeara.quatNormEquiv
attribute [kb "omeara1963" "§65A, p. 174 ($s = \\lvert\\Omega - S\\rvert$) (definition)"] QuadFormsKB.OMeara.outsideS
attribute [kb "omeara1963" "§65A, p. 174 (square at $\\mathfrak p$) (definition)"] QuadFormsKB.OMeara.SqAt
attribute [kb "omeara1963" "§65A, p. 175 ($S'$ and $N_{E/F}\\mathfrak U \\subseteq \\mathfrak u$) (definition)"] QuadFormsKB.HN.overS
attribute [kb "omeara1963" "§65A, p. 175 ($S'$ and $N_{E/F}\\mathfrak U \\subseteq \\mathfrak u$) (definition)"] QuadFormsKB.HN.normsF
attribute [kb "omeara1963" "§65A, p. 175 ($e_\\mathfrak p, f_\\mathfrak p$ in terms of $n_\\mathfrak p$) (statement: special case)"] QuadFormsKB.HN.ef_of_two
attribute [kb "omeara1963" "§65A, p. 175 ($e_\\mathfrak p, f_\\mathfrak p$ in terms of $n_\\mathfrak p$) (statement: special case)"] QuadFormsKB.HN.ef_of_unique
attribute [kb "omeara1963" "§65B, proof of 65:10, step 4, p. 181"] QuadFormsKB.HN.herbrandM1_eq_one
attribute [kb "omeara1963" "§65B, proof of 65:7, step 2–3, p. 178 (background)"] QuadFormsKB.HN.index_sq_completion
attribute [kb "omeara1963" "§65B, 65:11, p. 181 (proof route)"] QuadFormsKB.HN.isSquare_of_isSquare_local
attribute [kb "omeara1963" "§66, p. 186 ($S_\\mathfrak p V$ of a form) (definition)"] QuadFormsKB.NFPlace.hasseOMearaForm
attribute [kb "omeara1963" "§66, p. 186 (isotropic / isometric at $\\mathfrak p$ via the completion) (definition)"] QuadFormsKB.QuadForm.IsotropicIn
attribute [kb "omeara1963" "§66, p. 186 (isotropic / isometric at $\\mathfrak p$ via the completion) (definition)"] QuadFormsKB.QuadForm.IsometricIn
attribute [kb "omeara1963" "§66, proof of 66:1 step 5, p. 188 (finiteness of $T$)"] QuadFormsKB.NFLocal.isotropic_diag_units_nf
attribute [kb "omeara1963" "§66, 66:1, proof step 5 ($n \\ge 5$), p. 188"] QuadFormsKB.hasseMinkowski_nf_of_inputs
attribute [kb "omeara1963" "§71, p. 190 (Hilbert reciprocity law, statement in the chapter introduction)"] QuadFormsKB.hilbert_reciprocity_nf
attribute [kb "omeara1963" "§71, p. 190 (Hilbert reciprocity law, statement in the chapter introduction)"] QuadFormsKB.HN.hilbert_product_formula_nf
attribute [kb "omeara1963" "§71, p. 190 (reciprocity law for Hasse symbols, product of S_p V equals 1)"] QuadFormsKB.NFPlace.hasseOMeara_product_formula
attribute [kb "omeara1963" "§71, p. 190 (reciprocity law for Hasse symbols, variant over the rationals)"] QuadFormsKB.hasseOMeara_product_formula
attribute [kb "omeara1963" "§71D, 71:18, p. 201 (special case F = ℚ)"] QuadFormsKB.hilbert_product_formula
attribute [kb "omeara1963" "§71D, 71:18, p. 201 (special case F = ℚ)"] QuadFormsKB.hilbert_reciprocity_nf_rat
attribute [kb "omeara1963" "§73, 73:2, p. 206 (special case: odd a, b and (2, b); general 2-adic formula)"] QuadFormsKB.HilbertLocal.hilbertSymbol_two_formula
attribute [kb "omeara1963" "§73, 73:2, p. 206 (special case: odd integers a, b and (2, b))"] QuadFormsKB.ConwaySloane.hilbert_two_int
attribute [kb "omeara1963" "§73, 73:1, p. 206 ((a,b/p) = 1 for p-adic units, variant)"] QuadFormsKB.HilbertLocal.hilbertSymbol_units
attribute [kb "omeara1963" "§73, 73:1, p. 206 (variant: general exponents); §73, p. 206 (symbol determined by units and (a, p))"] QuadFormsKB.HilbertLocal.hilbertSymbol_odd_formula
attribute [kb "omeara1963" "§73, 73:1, p. 206 (variant: integers prime to p, general exponents)"] QuadFormsKB.ConwaySloane.hilbert_odd_int
attribute [kb "omeara1963" "§73, p. 206 (unit is a square in ℚ_p iff its residue is a square mod p)"] QuadFormsKB.HilbertLocal.isSquare_unit_iff
attribute [kb "omeara1963" "§81A, p. 209 (lattice on V = F^n: finitely generated and spanning)"] QuadFormsKB.Lattices.Lat
attribute [kb "omeara1963" "§81A, p. 209 (𝔬x₁+…+𝔬xₙ is a lattice on V)"] QuadFormsKB.Lattices.latOf_isLattice
attribute [kb "omeara1963" "§81A, p. 209 (𝔬x₁+…+𝔬xₙ is a lattice on V; standard base)"] QuadFormsKB.Lattices.intVec_isLattice
attribute [kb "omeara1963" "§81A, p. 210 (every finitely generated 𝔬-module in V is a lattice)"] QuadFormsKB.OMeara.fg_iff_le_span_basis
attribute [kb "omeara1963" "§81B, p. 213 (a free lattice: a lattice with a base)"] QuadFormsKB.Lattices.latOf
attribute [kb "omeara1963" "§81B, p. 213 (dim L = dim FL = rank L, free lattice)"] QuadFormsKB.OMeara.finrank_eq_finrank_span
attribute [kb "omeara1963" "§81C, proof of 81:8, p. 214 (cofactor bound)"] QuadFormsKB.OMeara.span_det_mul_prod_le
attribute [kb "omeara1963" "§81D, proof of 81:11, step 3, p. 215"] QuadFormsKB.OMeara.exists_smul_mul_sup_eq_one
attribute [kb "omeara1963" "§81E, p. 217 (laws of the localization of ideals)"] QuadFormsKB.OMeara.locIdeal_mul
attribute [kb "omeara1963" "§81E, p. 217 (laws of the localization of ideals)"] QuadFormsKB.OMeara.locIdeal_one
attribute [kb "omeara1963" "§81E, p. 217 (laws of the localization of ideals)"] QuadFormsKB.OMeara.locIdeal_span_singleton
attribute [kb "omeara1963" "§81E, p. 217 (laws of the localization of ideals)"] QuadFormsKB.OMeara.locIdealHom
attribute [kb "omeara1963" "§81E, p. 217 (a ⊆ b iff a_𝔭 ⊆ b_𝔭 for all 𝔭)"] QuadFormsKB.OMeara.le_of_forall_locIdeal_le
attribute [kb "omeara1963" "§81E, p. 217 (a = b iff a_𝔭 = b_𝔭 for all 𝔭)"] QuadFormsKB.OMeara.eq_of_forall_locIdeal_eq
attribute [kb "omeara1963" "§81E, p. 218 ((Σ 𝔞ᵢ zᵢ)_𝔭 = Σ 𝔞ᵢ,𝔭 zᵢ)"] QuadFormsKB.OMeara.locLat_iSup_smul
attribute [kb "omeara1963" "§81E, p. 218 (L ⊆ K iff L_𝔭 ⊆ K_𝔭 for all 𝔭)"] QuadFormsKB.Lattices.le_iff_forall_loc
attribute [kb "omeara1963" "§81E, p. 218 (L = K iff L_𝔭 = K_𝔭 for all 𝔭)"] QuadFormsKB.Lattices.loc_injective
attribute [kb "omeara1963" "§81B, p. 210 (𝔞_x is non-zero)"] QuadFormsKB.OMeara.coeff_ne_bot
attribute [kb "omeara1963" "§82C, p. 222 (isometry of lattices is an equivalence relation; variant: full O(V), number field)"] QuadFormsKB.Lattices.IsIsometric.refl
attribute [kb "omeara1963" "§82C, p. 222 (isometry of lattices is an equivalence relation)"] QuadFormsKB.Lattices.IsIsometric.symm
attribute [kb "omeara1963" "§82C, p. 222 (isometry of lattices is an equivalence relation)"] QuadFormsKB.Lattices.IsIsometric.trans
attribute [kb "omeara1963" "§82J, p. 238 (the form of V^α is αB)"] QuadFormsKB.OMeara.bil_smul
attribute [kb "omeara1963" "§82J, p. 238 (L α-modular in V gives L unimodular for α⁻¹Q; variant)"] QuadFormsKB.OMeara.isUnimodular_smul_of_isModular
attribute [kb "omeara1963" "§82A, p. 220 (K ≅ L on one space, as K = σL) (variant)"] QuadFormsKB.Lattices.IsIsometric
attribute [kb "omeara1963" "§82A, p. 220 (question reduced to σK = L with σ ∈ O(V); DVR case)"] QuadFormsKB.OMeara.mem_cls_of_isometricLat
attribute [kb "omeara1963" "§82B, p. 221 (class of a matrix, as classes of forms) (variant)"] QuadFormsKB.Tamagawa.FormClassNF.FormClass
attribute [kb "omeara1963" "§82B, p. 221 (class of a matrix over Z) (variant)"] QuadFormsKB.Siegel.QClass
attribute [kb "omeara1963" "§82C, p. 223 (index of O⁺(L) in O(L) is 1 or 2) (variant)"] QuadFormsKB.OMeara.clsPlus_eq_cls_iff_relIndex
attribute [kb "omeara1963" "§82D, p. 224 (orthogonal sum of quadratic spaces) (variant)"] QuadFormsKB.QuadForm.orthSum
attribute [kb "omeara1963" "§82D, p. 225 (orthogonal base of a lattice)"] QuadFormsKB.OMeara.exists_orthogonal_basis
attribute [kb "omeara1963" "§82D, p. 225 (orthogonal base, for spaces) (variant)"] QuadFormsKB.OMeara.IsOrthogonalBasis
attribute [kb "omeara1963" "§82E, p. 227 (sL = sum B(x_i,x_j)o for a generating family)"] QuadFormsKB.OMeara.scale_span
attribute [kb "omeara1963" "§82E, p. 229 (vL independent of the adapted base)"] QuadFormsKB.OMeara.volume_eq_of_adapted
attribute [kb "omeara1963" "§82E, 82:11, p. 230 (index of K in L as covolume ratio) (variant)"] QuadFormsKB.Tamagawa.SiegelSpace.latIndex_eq_inv_covol
attribute [kb "omeara1963" "§82E, 82:11, p. 230 (index of K in L as covolume ratio) (variant)"] QuadFormsKB.Tamagawa.SiegelSpace.latIndex_mul_relIndex
attribute [kb "omeara1963" "§82H, p. 234 (a-maximal lattice, relative to a subspace) (variant)"] QuadFormsKB.OMeara.IsMaxIn
attribute [kb "omeara1963" "§82J, p. 238 (matrix of L^α is αM)"] QuadFormsKB.OMeara.gram_smul
attribute [kb "omeara1963" "§82J, p. 238 (d(L^α) = α^r dL) (special case: spaces)"] QuadFormsKB.OMeara.det_gram_smul
attribute [kb "omeara1963" "§82J, p. 238 (O(V^α) = O(V); lattice statement not formalized) (variant)"] QuadFormsKB.OMeara.orth_smul
attribute [kb "omeara1963" "§82J, p. 238 (O⁺(V^α) = O⁺(V); lattice statement not formalized) (variant)"] QuadFormsKB.OMeara.orthPlus_smul
attribute [kb "omeara1963" "§91A, proof of 91:1, p. 240 (Local Square Theorem used)"] QuadFormsKB.OMeara.isSquare_one_add_four_mul
attribute [kb "omeara1963" "§91B, 91:6, p. 242 (special case: V isotropic)"] QuadFormsKB.OMeara.spinorNormHom_surjective_of_isotropic
attribute [kb "omeara1963" "§91C, p. 243 (L = J ⊥ K for an sL-modular sublattice J)"] QuadFormsKB.OMeara.splits_of_isModular_of_scale_eq
attribute [kb "omeara1963" "§91C, p. 245 (any two Jordan splittings of L are of the same type)"] QuadFormsKB.OMeara.IsJordanSplitting.sameJordanType
attribute [kb "omeara1963" "§91C, p. 244 (L^a for a b-modular lattice L, b ⊆ a)"] QuadFormsKB.OMeara.subA_of_isModular_of_le
attribute [kb "omeara1963" "§91C, p. 244 (L^a for a b-modular lattice L, b ⊇ a)"] QuadFormsKB.OMeara.subA_of_isModular_of_ge
attribute [kb "omeara1963" "§91C, p. 244 (sL^a ⊆ a)"] QuadFormsKB.OMeara.Dedekind.scale_subA_le
attribute [kb "omeara1963" "§91C, p. 244 (L^a for a Jordan splitting, variant)"] QuadFormsKB.OMeara.IsOrthSum.subA
attribute [kb "omeara1963" "§92, p. 246 (2sL ⊆ nL ⊆ sL, recalled from §82E)"] QuadFormsKB.OMeara.normIdeal_le_scale
attribute [kb "omeara1963" "§92, p. 246 (2sL ⊆ nL, recalled from §82E)"] QuadFormsKB.OMeara.two_mul_mem_normIdeal
attribute [kb "omeara1963" "§92, p. 246 (ox with Q(x)o = sL is sL-modular)"] QuadFormsKB.OMeara.isModular_span_singleton
attribute [kb "omeara1963" "§91A, proof of 91:2, p. 241 (components of a-maximal lattices are a-maximal)"] QuadFormsKB.OMeara.IsMaxIn.complement
attribute [kb "omeara1963" "§91A, proof of 91:2, p. 240 (proof route)"] QuadFormsKB.OMeara.exists_hyperbolic_split_of_isMaxIn
attribute [kb "omeara1963" "§91A, proof of 91:1, p. 240 (closed under addition)"] QuadFormsKB.OMeara.Q_add_mem_of_anisotropic
attribute [kb "omeara1963" "§91A, proof of 91:1, p. 240 (the o-module X)"] QuadFormsKB.OMeara.anisoSub
attribute [kb "omeara1963" "§91A, proof of 91:2, pp. 240–241 (proof route)"] QuadFormsKB.OMeara.exists_orth_of_isMaxIn
attribute [kb "omeara1963" "§91C, p. 243 (L = J ⊥ K with J sL-modular)"] QuadFormsKB.OMeara.exists_isOrthSum_modular
attribute [kb "omeara1963" "§91C, p. 244 (scale of L^a for a b-modular L)"] QuadFormsKB.OMeara.notMem_scale_subA
attribute [kb "omeara1963" "§91C, p. 244 (sL^a ⊆ a)"] QuadFormsKB.OMeara.scale_subA_le
attribute [kb "omeara1963" "§91C, p. 244 (a-modular component splits L^a)"] QuadFormsKB.OMeara.isOrthSum_subA
attribute [kb "omeara1963" "§91C, 91:10, p. 246 (chain increasing, last term L)"] QuadFormsKB.OMeara.jordanChain_mono
attribute [kb "omeara1963" "§91C, 91:10, p. 246 (chain increasing, last term L)"] QuadFormsKB.OMeara.jordanChain_last
attribute [kb "omeara1963" "§91C, 91:11, p. 246 (vL_(i) = vK_(i))"] QuadFormsKB.OMeara.volume_jordanChain_eq
attribute [kb "omeara1963" "§92, p. 246 (orthogonal family of anisotropic vectors)"] QuadFormsKB.OMeara.exists_orth_family
attribute [kb "omeara1963" "§92, 92:3, p. 248 (variant: splittings of one lattice)"] QuadFormsKB.OMeara.isometricLat_cancel_of_isOrthSum
attribute [kb "omeara1963" "§93, p. 251 (2(sL) ⊆ nL ⊆ sL, recalled from §82)"] QuadFormsKB.OMeara.two_mul_mem_normIdeal
attribute [kb "omeara1963" "§93, p. 251 (2(sL) ⊆ nL ⊆ sL, recalled from §82)"] QuadFormsKB.OMeara.normIdeal_le_scale
attribute [kb "omeara1963" "§93A, p. 252 (nL = aο for a of largest value in gL; existence of a norm generator)"] QuadFormsKB.OMeara.exists_isNormGenerator_Q
attribute [kb "omeara1963" "§93A, p. 253 ( (2(sL))"] QuadFormsKB.OMeara.weight_bounds
attribute [kb "omeara1963" "§93D, 93:15, p. 258 (variant: even unimodular over a DVR is a sum of binary forms)"] QuadFormsKB.LocalDensity.DVR.exists_pairSum_of_isLocalLevel_zero
attribute [kb "omeara1963" "§93E, p. 262 (scales $\\mathfrak s_i$ of the components)"] QuadFormsKB.OMeara.IsJordanSplitting
attribute [kb "omeara1963" "§93E, p. 263 (t, dim L_i, s_i are unique) (special case)"] QuadFormsKB.OMeara.IsJordanSplitting.sameJordanType
attribute [kb "omeara1963" "§93G, p. 276 (2o ⊆ p in a dyadic local field)"] QuadFormsKB.HN.valued_two
attribute [kb "omeara1963" "§94, pp. 279–280 (one step of the Jordan splitting procedure, Gram matrix form) (variant)"] QuadFormsKB.LocalDensity.DVR.dvr_stepGen
attribute [kb "omeara1963" "§94, p. 280 (repeating the step gives a Jordan splitting) (variant)"] QuadFormsKB.LocalDensity.DVR.exists_jordanFormGen
attribute [kb "omeara1963" "§94, p. 280 (norm generator from a largest value of Q) (variant)"] QuadFormsKB.OMeara.exists_isNormGenerator_Q
attribute [kb "omeara1963" "§95, 95:1, p. 280 (Ω = O' when isotropic or n ≤ 3; step 1) (special case)"] QuadFormsKB.OMeara.omega_eq_orthPrime
attribute [kb "omeara1963" "§95, 95:1, p. 281 (isotropic case, step 1) (special case)"] QuadFormsKB.OMeara.omega_eq_orthPrime_of_isotropic
attribute [kb "omeara1963" "§95, 95:1, p. 281 (1 ≤ n ≤ 3, step 1) (special case)"] QuadFormsKB.OMeara.omega_eq_orthPrime_of_finrank_le_three
attribute [kb "omeara1963" "§95, proof of 95:1, p. 281 (coset of a product of symmetries independent of order)"] QuadFormsKB.OMeara.symProd_mul_inv_mem_omega
attribute [kb "omeara1963" "§95, p. 283 (−1_V ∈ Ω iff n even and dV = 1) (special case)"] QuadFormsKB.OMeara.neg_mem_omega_iff
attribute [kb "omeara1963" "§95, p. 284 (O⁺/O' ≅ F/F², isotropic case) (special case)"] QuadFormsKB.OMeara.orthPlus_quotient_equiv_of_isotropic
attribute [kb "omeara1963" "§101A, p. 285 (norm property (3), the triangle inequality, as a consequence of the ultrametric inequality)"] QuadFormsKB.Lattices.vecNorm_add_le
attribute [kb "omeara1963" "§101A, 101:4 (i), p. 288 (the isometries with ‖σ‖ = 1 form a group)"] QuadFormsKB.Lattices.stdStab
attribute [kb "omeara1963" "§101D, p. 297 (σL = (σ)L for a rotation σ)"] QuadFormsKB.Lattices.diagF_smul
attribute [kb "omeara1963" "§101D, p. 296 (the definition of a split rotation is independent of the base)"] QuadFormsKB.Lattices.eventually_matNorm_conj_eq
attribute [kb "omeara1963" "§101D, pp. 295–296 (J_V: split rotations, finite spots; variant)"] QuadFormsKB.Tamagawa.soAf
attribute [kb "omeara1963" "§101D, p. 297 (proof step: ‖Σ_𝔭‖ = 1 iff Σ_𝔭 M_𝔭 = M_𝔭)"] QuadFormsKB.Lattices.mem_stdStab_iff_matNorm_le_one
attribute [kb "omeara1963" "§101D, p. 297 (proof step: L_𝔭 = M_𝔭 for almost all 𝔭)"] QuadFormsKB.Lattices.loc_eventually_std
attribute [kb "omeara1963" "§101C, proof of 101:12, p. 294 (Global Square Theorem step)"] QuadFormsKB.SqLG.isSquare_iff_everywhere
attribute [kb "omeara1963" "§101C, proof of 101:12, p. 294"] QuadFormsKB.Lattices.isSquare_of_eventually_isSquare
attribute [kb "omeara1963" "§101D, p. 296 (σ ↦ (σ) is injective)"] QuadFormsKB.Lattices.diagF_injective
attribute [kb "omeara1963" "§101B, p. 289 (rotations localize to rotations)"] QuadFormsKB.Lattices.orthMap_mem_soSub
attribute [kb "omeara1963" "§101B, p. 289 (spinor-kernel elements localize to spinor-kernel elements)"] QuadFormsKB.Lattices.orthMap_mem_spinorKernel
attribute [kb "omeara1963" "§103, 103:4, p. 309 (special case: forms over Z, classes in a genus)"] QuadFormsKB.Siegel.genusClasses_finite
attribute [kb "omeara1963" "§103, proof of 103:4, step 1, p. 309 (a class is one or two proper classes)"] QuadFormsKB.Lattices.properClassNumber_le_two_mul
attribute [kb "omeara1963" "§103, proof of 103:4, step 1, p. 309 (a class is one or two proper classes; special case: forms over Z)"] QuadFormsKB.Siegel.ncard_properClassesIn
attribute [kb "omeara1963" "§103, proof of 103:4, step 3, p. 310 (Witt's theorem, special case)"] QuadFormsKB.Lattices.ClassFin.exists_orth_mulVec_eq
attribute [kb "omeara1963" "§104, 104:3, p. 311 (the statement, with neighbourhoods)"] QuadFormsKB.Lattices.VecApprox
attribute [kb "omeara1963" "§104, 104:4, p. 315 (the statement, with neighbourhoods)"] QuadFormsKB.Lattices.RotApprox
attribute [kb "omeara1963" "§104, proof of 104:4, step 1b, p. 316 (proof route: short commutators generate the spinor kernel, isotropic case; Proposition 43:6)"] QuadFormsKB.Lattices.spinorKernel_le_eqPairGroup
attribute [kb "omeara1963" "§104, 104:5, p. 319 (cls⁺ L = spn⁺ L)"] QuadFormsKB.Lattices.isProperIsometric_of_sameProperSpinorGenus
attribute [kb "omeara1963" "§104, 104:5, p. 319 (cls⁺ L = spn⁺ L)"] QuadFormsKB.Lattices.properSpinorGenus_eq_properClass
attribute [kb "omeara1963" "§104, 104:8, p. 320 (variant: one proper class in the genus, adelic form)"] QuadFormsKB.Tamagawa.Indefinite.subsingleton_DC
attribute [kb "omeara1963" "§104, proof of 104:3, step 2, p. 312 (weak approximation for products of symmetries)"] QuadFormsKB.Lattices.exists_symmProd_approx
attribute [kb "omeara1963" "§106, p. 324 (the form I_n = x₀² + ⋯ + x_{n-1}²)"] QuadFormsKB.Lattices.sumSqForm
attribute [kb "omeara1963" "§106E, p. 331 (the vector y = ½(x₁ + ⋯ + x_n); indices shifted)"] QuadFormsKB.Lattices.omearaEHalf
attribute [kb "omeara1963" "§106E, p. 331 (generators of E)"] QuadFormsKB.Lattices.omearaEGens
attribute [kb "omeara1963" "§106A, 106:1, p. 324 (only if: 8 ∣ n; proof route via theta series)"] QuadFormsKB.Siegel.eight_dvd_of_posDef_det_one
attribute [kb "omeara1963" "§106A, 106:1, p. 324 (only if: 8 ∣ n; variant)"] QuadFormsKB.WeilRep.Genus.four_dvd_of_evenUnimodular
attribute [kb "omeara1963" "§106A, 106:1, p. 324 (proof route: the if direction by E₈ ⊥ ⋯ ⊥ E₈)"] QuadFormsKB.Siegel.e8
attribute [kb "omeara1963" "§106E, p. 331 (Φ₈ unimodular; special case n = 8, up to change of base)"] QuadFormsKB.Siegel.e8_det
attribute [kb "omeara1963" "§106, p. 323 (indefinite: class = genus; variant)"] QuadFormsKB.Lattices.isIsometric_of_sameGenus'
attribute [kb "omeara1963" "§106B, p. 326 (adjacency is symmetric; neighbours at any prime, variant)"] QuadFormsKB.Lattices.Nbr.IsNbrL.symm
attribute [kb "omeara1963" "§106B, p. 326 (adjacency is invariant under O(V); variant: full orthogonal group, any prime)"] QuadFormsKB.Lattices.Nbr.IsNbrL.glImage
attribute [kb "omeara1963" "§101D, p. 297 (O⁺(L) ≅ P_V ∩ J_L, via σL = (σ)L) (variant: full O)"] QuadFormsKB.Lattices.stabilizer_eq_locStab
attribute [kb "omeara1963" "§63B, 63:11b, p. 165 (proof route)"] QuadFormsKB.OMeara.quatSwapEquiv
attribute [kb "omeara1963" "§13B, 13:6, p. 24 (n = 2, global primes) (statement: special case)"] QuadFormsKB.Binary.Rel.sum_ramificationIdx_mul_inertiaDeg
attribute [kb "omeara1963" "§16, 16:4, p. 40 (n = 2) (statement: special case)"] QuadFormsKB.Binary.Rel.sum_ramificationIdx_mul_inertiaDeg
