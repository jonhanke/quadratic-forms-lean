import QuadFormsKB.Binary.ClassBijection
import QuadFormsKB.Binary.ClassNumberFormula
import QuadFormsKB.Binary.EulerProductAtOne
import QuadFormsKB.Binary.FormAut
import QuadFormsKB.Binary.FormsIdeals
import QuadFormsKB.Binary.GenusCharacters
import QuadFormsKB.Binary.GenusClassGroup
import QuadFormsKB.Binary.GenusComposition
import QuadFormsKB.Binary.GenusCount
import QuadFormsKB.Binary.GenusDuplication
import QuadFormsKB.Binary.GenusLocal
import QuadFormsKB.Binary.GenusMass
import QuadFormsKB.Binary.KroneckerChar
import QuadFormsKB.Binary.QuadraticField
import QuadFormsKB.Binary.RelForms
import QuadFormsKB.Binary.RelGenusHilbert
import QuadFormsKB.Binary.SiegelBinary
import QuadFormsKB.Defs.Binary
import QuadFormsKB.Defs.Hilbert
import QuadFormsKB.Defs.Integral
import QuadFormsKB.Defs.QuadForm
import QuadFormsKB.Equiv.Binary
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Equiv.Integral
import QuadFormsKB.Equiv.NumberFieldRat
import QuadFormsKB.HilbertModular.EisHecke
import QuadFormsKB.HilbertModular.TartakowskyUncond
import QuadFormsKB.Lattices.Basic
import QuadFormsKB.Lattices.CartanDieudonne
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Lattices.Finite
import QuadFormsKB.Lattices.FreeBridge
import QuadFormsKB.Lattices.Genus
import QuadFormsKB.Lattices.Local
import QuadFormsKB.Lattices.NeighborRep
import QuadFormsKB.Lattices.SAApprox
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Lattices.SAEqualPairs
import QuadFormsKB.Lattices.SALemma1041
import QuadFormsKB.Lattices.SARotations
import QuadFormsKB.Lattices.SATernary
import QuadFormsKB.Lattices.SATernaryAway
import QuadFormsKB.Lattices.SAVSA
import QuadFormsKB.Lattices.SAVectorsAnisotropic
import QuadFormsKB.Lattices.SAVectorsAway
import QuadFormsKB.Lattices.SAVectorsIsotropic
import QuadFormsKB.Lattices.SAWeak
import QuadFormsKB.Lattices.SpinorGenus
import QuadFormsKB.Lattices.SpinorGenusCount
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Lattices.SpinorLocal
import QuadFormsKB.Lattices.SpinorNorm
import QuadFormsKB.Lattices.Steinitz
import QuadFormsKB.Lattices.StrongApproximation
import QuadFormsKB.Lattices.StrongApproximationProof
import QuadFormsKB.Lattices.UnimodularDVR
import QuadFormsKB.Literature.Cassels.Ch10.Clifford
import QuadFormsKB.Literature.Cassels.Ch11Sec1Example
import QuadFormsKB.Literature.Cassels.Ch11Sec1Forms
import QuadFormsKB.Literature.Cassels.Ch11Sec1Indef
import QuadFormsKB.Literature.Cassels.Ch11Sec3Group
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm
import QuadFormsKB.Literature.Cassels.Ch11Sec6Genus
import QuadFormsKB.Literature.Cassels.Ch11Sec7Lemma
import QuadFormsKB.Literature.Cassels.Ch12.Basic
import QuadFormsKB.Literature.Cassels.Ch12.Sec4
import QuadFormsKB.Literature.Cassels.Ch12.Sec5
import QuadFormsKB.Literature.Cassels.Ch12.Sec7
import QuadFormsKB.Literature.Cassels.Ch12.SquareDecomp
import QuadFormsKB.Literature.Cassels.Ch13.Sec3Matrix
import QuadFormsKB.Literature.Cassels.Ch14.CompositionSL
import QuadFormsKB.Literature.Cassels.Ch2.WittChain
import QuadFormsKB.Literature.Cassels.Ch2.WittGroup
import QuadFormsKB.Literature.Cassels.Ch5.Minkowski
import QuadFormsKB.Literature.Cassels.Ch8.Bases
import QuadFormsKB.Literature.Cassels.Ch9Examples
import QuadFormsKB.Literature.Cassels.Ch9Examples3
import QuadFormsKB.Literature.Cassels.Ch9Examples6
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Literature.Cassels.Ch9Sec4LocalPadic
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Literature.Cassels.Ch9Sec5Exist
import QuadFormsKB.Literature.Cassels.Ch9Sec5Lat
import QuadFormsKB.Literature.Cassels.Ch9Sec6Four
import QuadFormsKB.Literature.Cassels.Ch9Sec6Three
import QuadFormsKB.Literature.Classical.DavenportCassels
import QuadFormsKB.Literature.Classical.SumsOfSquares
import QuadFormsKB.Literature.HasseNorm.LocalIndexTwo
import QuadFormsKB.Literature.HasseNorm.SecondInequality
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.PrescribedSymbols
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.OMeara.Sec105
import QuadFormsKB.Literature.OMeara.Sec106E
import QuadFormsKB.Literature.OMeara.Sec42Iso
import QuadFormsKB.Literature.OMeara.Sec43C
import QuadFormsKB.Literature.OMeara.Sec43CD
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec63C
import QuadFormsKB.Literature.OMeara.Sec73
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Literature.OMeara.Sec82Max
import QuadFormsKB.Literature.OMeara.Sec82Radical
import QuadFormsKB.LocalDensity.DyadicJordan
import QuadFormsKB.LocalDensity.FormDensityHyperbolic
import QuadFormsKB.LocalDensity.JordanForm
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.Formula
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.FourSquaresJacobi
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Siegel.GenusEisenstein.ThetaGen
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.Siegel.HeckeBound
import QuadFormsKB.Siegel.Mass
import QuadFormsKB.Siegel.Tartakowsky
import QuadFormsKB.Siegel.Theta
import QuadFormsKB.Siegel.ThetaCuspidal
import QuadFormsKB.Siegel.ThetaGamma0
import QuadFormsKB.Siegel.ThetaModular
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Tamagawa.Classical.BinaryJacobi
import QuadFormsKB.Tamagawa.Classical.LValues
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Tamagawa.LocalVolume
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.Weil.ReleaseHeadlines
import QuadFormsKB.Tamagawa.Measure.Weil.SpaceHeadlines
import QuadFormsKB.Tamagawa.OrthFq
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Tamagawa.QuaternionSO3
import QuadFormsKB.Tamagawa.Reflection
import QuadFormsKB.Tamagawa.SiegelClassical
import QuadFormsKB.Tamagawa.SiegelFormulaConsumers
import QuadFormsKB.Tamagawa.SquareClassDuality
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal
import QuadFormsKB.Weil.LocalK0
import QuadFormsKB.Witt.Basic
import QuadFormsKB.Witt.Cancellation
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Witt.Represents

/-!
# Cassels: citations for declarations elsewhere in the library (first part)

Locators of the 1978 printing, added with `attribute [kb …]` so that the files where the
declarations live are unchanged (tags only: no statement or proof changes). Generated by
a script (outside Lean); the rows that correct an existing locator were edited by hand in the source files.
-/

attribute [kb "cassels1978" "Ch. 1, §2, (2.3), p. 5 (definition)"] QuadFormsKB.QuadForm.RepresentsIn
attribute [kb "cassels1978" "Ch. 1, §2, p. 5 (I-equivalence of forms) (definition)"] QuadFormsKB.QuadForm.IsometricIn
attribute [kb "cassels1978" "Ch. 1, §2, p. 5 (equivalence is an equivalence relation) (statement: variant)"] QuadFormsKB.QuadForm.isometricIn_refl
attribute [kb "cassels1978" "Ch. 1, §2, p. 5 (equivalence is an equivalence relation) (statement: variant)"] QuadFormsKB.QuadForm.isometricIn_symm
attribute [kb "cassels1978" "Ch. 1, §2, p. 5 (equivalence is an equivalence relation) (statement: variant)"] QuadFormsKB.QuadForm.isometricIn_trans
attribute [kb "cassels1978" "Ch. 1, §2, p. 6 (equivalent forms represent the same elements) (statement: special case)"] QuadFormsKB.QuadForm.representsIn_of_isometricIn
attribute [kb "cassels1978" "Ch. 1, §2, (2.9)–(2.10), p. 6 (G = B'FB, Hessian form, B invertible) (statement: special case)"] QuadFormsKB.Siegel.IsometricGL.hessian_eq
attribute [kb "cassels1978" "Ch. 1, §2, (2.17), p. 7 (integer-valued iff coefficients integral) (statement: variant)"] QuadFormsKB.RatQF.isIntegral_iff_integerValued
attribute [kb "cassels1978" "Ch. 1, §2, p. 7 (integer-valued forms) (definition)"] QuadFormsKB.RatQF.IsIntegral
attribute [kb "cassels1978" "Ch. 1, §2, p. 7 (classically integral) (definition)"] QuadFormsKB.IsClassicallyIntegral
attribute [kb "cassels1978" "Ch. 1, §1, p. 4 (the solubility theorem in terms of $\\mathbb Q_p$) (statement: variant)"] QuadFormsKB.hasseMinkowski
attribute [kb "cassels1978" "Ch. 1, §3, p. 8 (represents globally iff everywhere locally) (statement: variant)"] QuadFormsKB.represents_iff_everywhere
attribute [kb "cassels1978" "Ch. 1, §3, p. 8 (equivalent globally iff everywhere locally) (statement: variant)"] QuadFormsKB.isometric_iff_everywhere
attribute [kb "cassels1978" "Ch. 1, §3, p. 9 (the genus) (definition)"] QuadFormsKB.Siegel.SameGenus
attribute [kb "cassels1978" "Ch. 1, §3, p. 9 (a genus has finitely many classes) (statement: special case)"] QuadFormsKB.Siegel.genusFinite
attribute [kb "cassels1978" "Ch. 1, §3, p. 9 (genera of sums of two, three, four squares) (statement: generalization)"] QuadFormsKB.Siegel.sameGenus_sumSq_intEquiv
attribute [kb "cassels1978" "Ch. 1, §1, (1.5), p. 2 (necessity of $n \\ne 4^a(8b+7)$) (proof route)"] QuadFormsKB.Grosswald.not_three_squares_four_pow_mul
attribute [kb "cassels1978" "Ch. 2, §4, p. 20 (n symmetries suffice) and Ex. 8, p. 30"] QuadFormsKB.OMeara.exists_symmetry_prod_eq_length_le
attribute [kb "cassels1978" "Ch. 2, Ex. 10, p. 30"] QuadFormsKB.OMeara.exists_cd_prod_cons_eq
attribute [kb "cassels1978" "Ch. 2, Ex. 6 and Ex. 7 (ii), p. 29"] QuadFormsKB.OMeara.exists_hyperbolic_partners
attribute [kb "cassels1978" "Ch. 2, §1, (1.2), p. 11 (statement: variant)"] QuadFormsKB.QuadForm.polar_eq_hessian
attribute [kb "cassels1978" "Ch. 2, §1, (1.4), p. 12 (change of basis gives an equivalent form) (statement: variant)"] QuadFormsKB.Lattices.coordIsometry
attribute [kb "cassels1978" "Ch. 2, §1, (1.5), p. 12 (regular) (definition)"] QuadFormsKB.QuadForm.Nondegenerate
attribute [kb "cassels1978" "Ch. 2, §1, (1.5), p. 12 (regular space) and p. 11 (the 0-dimensional space) (definition)"] QuadFormsKB.Cassels.QSpace
attribute [kb "cassels1978" "Ch. 2, §1, (1.7), p. 12 (statement: special case)"] QuadFormsKB.Cassels.detU_eq_of_equivalent
attribute [kb "cassels1978" "Ch. 2, §1, p. 13 (the determinant $d(\\phi)$) (definition)"] QuadFormsKB.Cassels.detU
attribute [kb "cassels1978" "Ch. 2, §1, (1.8), p. 13 (definition)"] QuadFormsKB.Cassels.IsNormalBasis
attribute [kb "cassels1978" "Ch. 2, §2, p. 15 (represents) (definition)"] QuadFormsKB.QuadForm.RepresentsIn
attribute [kb "cassels1978" "Ch. 2, §2, p. 15 (isotropic, anisotropic) (definition)"] QuadFormsKB.QuadForm.IsotropicIn
attribute [kb "cassels1978" "Ch. 2, §2, (2.1), p. 15 (definition)"] QuadraticForm.hyperbolicPlane
attribute [kb "cassels1978" "Ch. 2, §2, (2.1), p. 15 (definition)"] QuadFormsKB.Lattices.hypForm
attribute [kb "cassels1978" "Ch. 2, §2, (2.1), p. 15 (definition)"] QuadFormsKB.Cassels.hypSpace
attribute [kb "cassels1978" "Ch. 2, §2, Lemma 2.1, Cor. 1, p. 15 (statement: variant)"] QuadraticForm.Witt.exists_split_hyperbolicPlane
attribute [kb "cassels1978" "Ch. 2, §2, p. 15 (the Remark after Lemma 2.1: the algorithm for $u_2$) (proof route)"] QuadraticForm.Witt.hyperbolic_partner
attribute [kb "cassels1978" "Ch. 2, §4, p. 18 (isometric spaces) (definition)"] QuadFormsKB.QuadForm.IsometricIn
attribute [kb "cassels1978" "Ch. 2, §4, p. 19 (autometries, $O(U)$) (definition)"] QuadFormsKB.Lattices.orthGroup
attribute [kb "cassels1978" "Ch. 2, §4, p. 19 (autometries, $O(U)$) (definition)"] QuadFormsKB.Lattices.orthGroupV
attribute [kb "cassels1978" "Ch. 2, §4, p. 19 (proper autometries $O^+(U)$) (definition)"] QuadFormsKB.Tamagawa.soSub
attribute [kb "cassels1978" "Ch. 2, §4, p. 19 (improper autometries exist)"] QuadFormsKB.Tamagawa.exists_orthGroup_det_neg_one
attribute [kb "cassels1978" "Ch. 2, §4, (4.1), p. 19 (definition)"] QuadFormsKB.Lattices.symm
attribute [kb "cassels1978" "Ch. 2, §4, (4.1), p. 19 (definition)"] QuadraticForm.Witt.reflection
attribute [kb "cassels1978" "Ch. 2, §4, (4.2), p. 19 (statement: variant)"] QuadFormsKB.QuadForm.det_reflMat
attribute [kb "cassels1978" "Ch. 2, §4, (4.3), p. 19"] QuadFormsKB.Lattices.symm_mulVec_bil
attribute [kb "cassels1978" "Ch. 2, §4, (4.3), p. 19"] QuadraticForm.Witt.reflection_apply
attribute [kb "cassels1978" "Ch. 2, §4, Lemma 4.2, p. 19"] QuadFormsKB.Lattices.symm_sub_apply
attribute [kb "cassels1978" "Ch. 2, §4, Lemma 4.2, Cor. 1, p. 20 (proof: $\\tau_{u+v}u=-v$) (proof route)"] QuadFormsKB.Lattices.symm_add_apply
attribute [kb "cassels1978" "Ch. 2, §4, Lemma 4.2, Cor. 1, p. 20 (replaces the tag \"Lemma 4.2, p. 19\") (statement: variant)"] QuadFormsKB.Lattices.exists_symm_apply_eq
attribute [kb "cassels1978" "Ch. 2, §4, Lemma 4.2, Cor. 1, p. 20 (statement: generalization)"] QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate
attribute [kb "cassels1978" "Ch. 2, §4, Thm. 4.1, p. 21"] QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate
attribute [kb "cassels1978" "Ch. 2, §4, Thm. 4.1, Cor. 1–2, pp. 21–22"] QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate
attribute [kb "cassels1978" "Ch. 2, §4, Thm. 4.1, Cor. 1–2, pp. 21–22 (statement: variant)"] QuadraticForm.equivalent_of_prod_equivalent_prod_of_associated
attribute [kb "cassels1978" "Ch. 2, §5, p. 23 (the zero of $S$) (definition)"] QuadFormsKB.Cassels.S.zero_def
attribute [kb "cassels1978" "Ch. 2, §5, p. 23 (the dimension of $s\\in S$) (definition)"] QuadFormsKB.Cassels.S.dim
attribute [kb "cassels1978" "Ch. 2, §5, p. 23 (the determinant of $s\\in S$) (definition)"] QuadFormsKB.Cassels.S.det
attribute [kb "cassels1978" "Ch. 2, §5, (5.3), p. 25 (definition)"] QuadFormsKB.Cassels.dimG
attribute [kb "cassels1978" "Ch. 2, §5, (5.1), p. 23 (case $n=1$); Ex. 18, p. 33 (statement: special case)"] QuadFormsKB.Cassels.unary_add_star
attribute [kb "cassels1978" "Ch. 2, Ex. 18, p. 33 (statement: special case)"] QuadFormsKB.Cassels.star_unary
attribute [kb "cassels1978" "Ch. 2, §5, (5.5), p. 25 (statement: variant)"] QuadraticForm.exists_wittDecomposition
attribute [kb "cassels1978" "Ch. 2, §5, (5.5), p. 25 (uniqueness; not in Cassels) (statement: generalization)"] QuadraticForm.wittDecomposition_unique
attribute [kb "cassels1978" "Ch. 2, §5, Lemma 5.8, p. 27 (proof step) (proof route)"] QuadFormsKB.Cassels.exists_sq_add_sq_eq
attribute [kb "cassels1978" "Ch. 2, Ex. 13(vi), p. 32 (hyperbolic plane) (statement: special case)"] QuadFormsKB.LocalDensity.DVR.card_orth_hyperbolic_field
attribute [kb "cassels1978" "Ch. 2, Ex. 13(vi), p. 32 (statement: variant)"] QuadFormsKB.LocalDensity.DVR.card_orthMod_one_unimodular
attribute [kb "cassels1978" "Ch. 2, Ex. 17, p. 33 (statement: special case)"] QuadFormsKB.FieldGen.isotropic_four_of_quadExt
attribute [kb "cassels1978" "Ch. 3, §2, p. 41 (the symbol at $p\\le\\infty$, $\\mathbb Q_\\infty=\\mathbb R$) (definition)"] QuadFormsKB.RatPlace.hilbert
attribute [kb "cassels1978" "Ch. 3, §2, p. 41 (definition via isotropy of $ax^2+by^2-z^2$)"] QuadFormsKB.hilbertSymbol_eq_one_iff_isotropic
attribute [kb "cassels1978" "Ch. 3, §2, p. 41 ($(a,b)$ depends only on $a,b$ modulo squares)"] QuadFormsKB.PadicClass.hs_sq_left
attribute [kb "cassels1978" "Ch. 3, §2, p. 41 ($(a,b)$ depends only on $a,b$ modulo squares)"] QuadFormsKB.PadicClass.hs_sq_right
attribute [kb "cassels1978" "Ch. 3, §2, p. 41 ($(a,b)$ depends only on $a,b$ modulo squares)"] QuadFormsKB.HN.hilbertSymbol_mul_sq_left
attribute [kb "cassels1978" "Ch. 3, §2, (2.1), p. 41"] QuadFormsKB.HN.hilbertSymbol_eq_one_iff_norm
attribute [kb "cassels1978" "Ch. 3, §2, (2.1), p. 41 (statement: generalization (number field places))"] QuadFormsKB.NFPlace.hilbert_eq_one_iff
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (i), p. 42 (statement: special case (places of $\\mathbb Q$))"] QuadFormsKB.RatPlace.hilbert_comm
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (i), p. 42 (statement: generalization)"] QuadFormsKB.NFPlace.hilbert_comm
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (ii)$'$, p. 42 (statement: special case (places of $\\mathbb Q$))"] QuadFormsKB.RatPlace.hilbert_mul_right
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (ii)$'$, p. 42 (statement: generalization)"] QuadFormsKB.NFPlace.hilbert_mul_right
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (iii)$'$, p. 42 (statement: generalization)"] QuadFormsKB.SqDual.hilbCl_nondeg_fin
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (iii)$'$, p. 42 (statement: generalization)"] QuadFormsKB.SqDual.hilbCl_nondeg_inf
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (v), p. 42 (statement: generalization)"] QuadFormsKB.SqDual.hilbert_units_nondyadic
attribute [kb "cassels1978" "Ch. 3, §2, Lemma 2.1 (v), p. 42 (statement: generalization)"] QuadFormsKB.WeilRep.hilbertSymbol_units_of_good
attribute [kb "cassels1978" "Ch. 3, §2, table ($\\alpha$), p. 43 (statement: variant)"] QuadFormsKB.ConwaySloane.hilbert_odd_int
attribute [kb "cassels1978" "Ch. 3, §2, table ($\\beta$), pp. 43–44 (statement: variant)"] QuadFormsKB.ConwaySloane.hilbert_two_int
attribute [kb "cassels1978" "Ch. 3, §3, p. 46 ($(a,b)_p=1$ for almost all $p$)"] QuadFormsKB.HilbertLocal.hilbert_support_finite
attribute [kb "cassels1978" "Ch. 3, §3, Lemma 3.4, p. 46 (statement: variant (via `NFPlace ℚ`))"] QuadFormsKB.hilbert_reciprocity_nf_rat
attribute [kb "cassels1978" "Ch. 3, §3, Lemma 3.4, p. 46 (statement: generalization (number field))"] QuadFormsKB.hilbert_reciprocity_nf
attribute [kb "cassels1978" "Ch. 3, §3, p. 46 (Lemma 3.4 gives quadratic reciprocity) (proof route)"] QuadFormsKB.OMeara.quadratic_reciprocity_of_hilbert
attribute [kb "cassels1978" "Ch. 3, §1, Lemma 1.7, Cor., p. 41"] QuadFormsKB.isotropic_padic_of_five_le
attribute [kb "cassels1978" "Ch. 3, §1, Lemma 1.7, Cor., p. 41 (statement: generalization)"] QuadFormsKB.LocalRankFive.isotropic_five
attribute [kb "cassels1978" "Ch. 3, §1, Lemma 1.6, Cor. (i) and (ii), p. 40 (order of $\\mathbb Q_p^{\\times}/(\\mathbb Q_p^{\\times})^2$) (statement: generalization)"] QuadFormsKB.HN.index_sq_completion
attribute [kb "cassels1978" "Ch. 3, §1, Lemma 1.6, p. 40 (statement: generalization (non-dyadic))"] QuadFormsKB.NFLocal.isSquare_of_valuation_sub_one_lt_nf
attribute [kb "cassels1978" "Ch. 4, §1, p. 55 (the determinant $d(f)$ is an invariant)"] QuadFormsKB.PadicClass.disc_of_isometric
attribute [kb "cassels1978" "Ch. 4, §1, p. 55 (footnote: other definitions of the invariant) (background)"] QuadFormsKB.RatPlace.hasseOMeara
attribute [kb "cassels1978" "Ch. 4, §1, p. 55 (footnote: other definitions of the invariant) (statement: variant)"] QuadFormsKB.hasseOMeara_eq
attribute [kb "cassels1978" "Ch. 4, §1, Thm. 1.2, p. 56 (the value of $c$ over $\\mathbb R$) (statement: variant)"] QuadFormsKB.hasseSerre_infinite_eq
attribute [kb "cassels1978" "Ch. 4, §1, Thm. 1.2, p. 56"] QuadFormsKB.LocalClassNF.isometric_real_vec_iff
attribute [kb "cassels1978" "Ch. 4, §1, Thm. 1.3, p. 56 (statement: variant (for $S$))"] QuadFormsKB.OMeara.exists_invariants_iff
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.2, p. 57 (and its Cor. 1, Lemma 2.1 Cor.)"] QuadFormsKB.PadicClass.hasseVec_eq_of_isometric
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.2, Cor. 1, p. 58 (statement: generalization)"] QuadFormsKB.NFPlace.hasseCasselsForm_eq_of_isometric
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.3 (ii), p. 58"] QuadFormsKB.Cassels.detU_add
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.3 (iii), p. 58 (for $S$) (statement: variant)"] QuadFormsKB.OMeara.hasseS_append
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.3 (iii), p. 58 (one summand a line) (statement: special case)"] QuadFormsKB.PadicClass.hasseVec_cons_prod
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.4, p. 58"] QuadFormsKB.FieldGen.isotropic_diag_two_iff
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.6 (i), p. 59 (statement: special case)"] QuadFormsKB.LocalRankFive.isotropic_four_of_not_isSquare
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.6, Cor., p. 60 (statement: variant)"] QuadFormsKB.PadicClass.represents_three_iff
attribute [kb "cassels1978" "Ch. 4, §2, Lemma 2.6, Cor., p. 60 (statement: variant)"] QuadFormsKB.represents_padic_three_iff
attribute [kb "cassels1978" "Ch. 4, §2, p. 60 (Note: Lemma 2.7 over finite extensions) (statement: generalization)"] QuadFormsKB.LocalRankFive.isotropicIn_completion_of_five_le
attribute [kb "cassels1978" "Ch. 4, §2, p. 61–62 (proof of Thm. 1.3) (proof route)"] QuadFormsKB.OMeara.exists_invariants_iff
attribute [kb "cassels1978" "Ch. 4, Notes, p. 66 (Sections 1, 2 over finite extensions) (statement: generalization)"] QuadFormsKB.NFPlace.isometric_iff
attribute [kb "cassels1978" "Ch. 5, §2, p. 68 (the set $\\mathbb Z^n$ in $\\mathbb R^n$) (definition)"] QuadFormsKB.Cassels.stdLattice
attribute [kb "cassels1978" "Ch. 5, §2, p. 68 (the set $\\mathbb Z^n$ in $\\mathbb R^n$) (definition)"] QuadFormsKB.Cassels.mem_stdLattice
attribute [kb "cassels1978" "Ch. 5, §3, (3.1), p. 72 ($d(\\mathbb Z^n)=1$) (background)"] QuadFormsKB.Cassels.covolume_stdLattice
attribute [kb "cassels1978" "Ch. 5, §2, Thm. 2.4, p. 71 (strict inequalities at all indices but one) (statement: generalization)"] QuadFormsKB.Cassels.minkowski_linear_forms_at
attribute [kb "cassels1978" "Ch. 5, §2, proof of Thm. 2.3, p. 70 ($\\Lambda$ has index $\\le m$) (proof route)"] QuadFormsKB.Cassels.congrHom
attribute [kb "cassels1978" "Ch. 5, §2, proof of Thm. 2.3, p. 70 ($\\Lambda$ has index $\\le m$) (proof route)"] QuadFormsKB.Cassels.mem_ker_congrHom
attribute [kb "cassels1978" "Ch. 5, §3, p. 72 (definition of a lattice)"] QuadFormsKB.Cassels.minkowski_basis
attribute [kb "cassels1978" "Ch. 5, §3, p. 72 (definition of a lattice)"] QuadFormsKB.Cassels.minkowski_lattice
attribute [kb "cassels1978" "Ch. 5, §2, p. 68 (Blichfeldt's original theorem is the case $k=1$) (statement: special case)"] QuadFormsKB.Cassels.blichfeldt_one
attribute [kb "cassels1978" "Ch. 5, Ex. 1 (ii), p. 74 (statement: variant)"] QuadFormsKB.Grosswald.fermat_two_squares
attribute [kb "cassels1978" "Ch. 5, Ex. 2 (ii), p. 74 (statement: variant)"] QuadFormsKB.Grosswald.lagrange_four_squares
attribute [kb "cassels1978" "Ch. 6, §1, p. 75 (the analogue of Thm. 1.1 over a number field) (statement: generalization)"] QuadFormsKB.hasseMinkowski_nf
attribute [kb "cassels1978" "Ch. 6, Notes, p. 96 (the strong principle holds over a number field) (statement: generalization)"] QuadFormsKB.hasseMinkowski_nf
attribute [kb "cassels1978" "Ch. 6, Notes, p. 96 (the weak principle holds over a number field) (statement: generalization)"] QuadFormsKB.Tamagawa.FormClassNF.isometricIn_of_everywhere_nf
attribute [kb "cassels1978" "Ch. 6, §11, Cor. 2 to Thm. 11.1, p. 94"] QuadFormsKB.isometric_iff_everywhere
attribute [kb "cassels1978" "Ch. 6, §1, Thm. 1.1, Cor. 1, p. 75 (Meyer: an indefinite form in n ≥ 5 variables is isotropic) (statement: generalization (number field))"] QuadFormsKB.Lattices.isotropicIn_of_five_le
attribute [kb "cassels1978" "Ch. 6, §2, p. 77 (proof that Thm. 1.1 implies Thm. 1.2) (proof route)"] QuadFormsKB.isometric_of_everywhere
attribute [kb "cassels1978" "Ch. 6, §5, Cor. to Thm. 5.1, p. 83 (statement: variant)"] QuadFormsKB.Prescribed.exists_rat_approx_sq_classes
attribute [kb "cassels1978" "Ch. 6, Ex. 6, p. 100 (statement: variant)"] QuadFormsKB.DavenportCassels.sum_sq_int_of_rat
attribute [kb "cassels1978" "Ch. 6, §1, p. 76 (the invariant $c_p(f)$ of a rational form) (definition)"] QuadFormsKB.RatPlace.hasseCassels
attribute [kb "cassels1978" "Ch. 7, §2, p. 102 (the lattice with basis $b_1,\\dots,b_n$) (definition)"] QuadFormsKB.Lattices.latOf
attribute [kb "cassels1978" "Ch. 7, §2, Lemma 2.1, p. 103 (statement: variant)"] QuadFormsKB.Lattices.exists_gl_int_of_glImage_eq
attribute [kb "cassels1978" "Ch. 7, §2, p. 103 (forms and lattices) (definition)"] QuadFormsKB.Lattices.gramForm
attribute [kb "cassels1978" "Ch. 7, §3, p. 104 (relative determinant) (definition)"] QuadFormsKB.Tamagawa.SiegelSpace.latIndex
attribute [kb "cassels1978" "Ch. 7, §3, p. 104 (the lattice $l\\Lambda$) (definition)"] QuadFormsKB.Binary.Rel.smulLat
attribute [kb "cassels1978" "Ch. 7, §3, Thm. 3.1 and Cor., pp. 106–108 (for $\\mathbb Z$) (statement: special case)"] QuadFormsKB.Siegel.tfae_extends_basis
attribute [kb "cassels1978" "Ch. 7, §3, Thm. 3.1 and Cor., pp. 106–108 (for $\\mathbb Z_p$) (statement: special case)"] QuadFormsKB.Cassels.tfae_extends_basis_padic
attribute [kb "cassels1978" "Ch. 7, §3, Thm. 3.1, Cor., p. 108 (primitive vectors, for $\\mathbb Z$) (statement: special case)"] QuadFormsKB.Siegel.exists_basis_first_iff_gcd
attribute [kb "cassels1978" "Ch. 7, §4, p. 109 (the radical of a lattice) (definition)"] QuadFormsKB.OMeara.splitComp
attribute [kb "cassels1978" "Ch. 7, §4, Lemma 4.1, p. 109 (statement: variant)"] QuadFormsKB.OMeara.exists_radical_splitting
attribute [kb "cassels1978" "Ch. 7, §4, p. 109 ($\\Lambda_1$ carries a regular form) (statement: variant)"] QuadFormsKB.OMeara.IsOrthSum.isRegular_of_radical
attribute [kb "cassels1978" "Ch. 7, Notes, p. 110 (Dedekind domain: lattices as $\\bigoplus I\\oplus J$)"] QuadFormsKB.Lattices.Steinitz.exists_eq_glImage_steinitzLat
attribute [kb "cassels1978" "Ch. 8, §1, p. 111 (variant: classical integrality over ℤ)"] QuadFormsKB.IsClassicallyIntegral
attribute [kb "cassels1978" "Ch. 8, §1, p. 111 (variant: primitive form over ℤ)"] QuadFormsKB.Siegel.IsPrimitiveCI
attribute [kb "cassels1978" "Ch. 8, §1, p. 111 (variant: properly primitive over ℤ)"] QuadFormsKB.Siegel.IsProperlyPrimitive
attribute [kb "cassels1978" "Ch. 8, §1, p. 111 (variant: improperly primitive over ℤ)"] QuadFormsKB.Siegel.IsImproperlyPrimitive
attribute [kb "cassels1978" "Ch. 8, §3, p. 113 ((3.7), the symmetry τ_b)"] QuadFormsKB.Cassels.tauFun
attribute [kb "cassels1978" "Ch. 8, §3, p. 113 ((3.7), τ_b is an involution)"] QuadFormsKB.Cassels.tauFun_involutive
attribute [kb "cassels1978" "Ch. 8, Cor. to Lemma 3.2, p. 114 (variant: reflection in a vector of minimal order)"] QuadFormsKB.QuadForm.exists_refl_data_dvr
attribute [kb "cassels1978" "Ch. 8, Cor. 2 to Lemma 3.3, p. 115 (variant: orthogonal unit-norm basis hypothesis)"] QuadFormsKB.Lattices.mem_closure_unitSymmSet
attribute [kb "cassels1978" "Ch. 8, Lemma 3.4, p. 115"] QuadFormsKB.Siegel.Kneser.isometricGL_diag_normal
attribute [kb "cassels1978" "Ch. 8, Lemma 3.4, p. 115 (proof route: n = 2 step)"] QuadFormsKB.Siegel.Kneser.exists_binary_one
attribute [kb "cassels1978" "Ch. 8, Lemma 3.4, p. 115 (proof route: n = 2 step)"] QuadFormsKB.Siegel.Kneser.isometricGL_diag_rot
attribute [kb "cassels1978" "Ch. 8, Lemma 4.1, p. 117 (variant: Jordan splitting, p = 2)"] QuadFormsKB.LocalDensity.DVR.exists_jordanFormGen
attribute [kb "cassels1978" "Ch. 8, Lemma 4.1, p. 117 (variant: p = 2 case)"] QuadFormsKB.LocalDensity.exists_jordanForm
attribute [kb "cassels1978" "Ch. 8, Lemma 5.2, p. 123 (variant: congruence modulo 4c)"] QuadFormsKB.Siegel.CongrLocal.meq_of_congr
attribute [kb "cassels1978" "Ch. 8, Notes, p. 124 (generalization to finite extensions of Q_p, unimodular case)"] QuadFormsKB.Lattices.Nbr.isometricGL_of_unimodular_dvr
attribute [kb "cassels1978" "Ch. 8, Examples, Ex. 7 (i), p. 126 (generalization: Dedekind domain)"] QuadFormsKB.OMeara.Dedekind.exists_isMaximal_ge
attribute [kb "cassels1978" "Ch. 9, §1, p. 127 (the group O(f) of integral automorphs)"] QuadFormsKB.Siegel.Aut
attribute [kb "cassels1978" "Ch. 9, §1, p. 128 (globally equivalent forms are in the same genus)"] QuadFormsKB.Siegel.IntEquiv.sameGenus
attribute [kb "cassels1978" "Ch. 9, §1, p. 130 (primitive version of Thm. 1.3)"] QuadFormsKB.Siegel.exists_sameGenus_primRep
attribute [kb "cassels1978" "Ch. 9, §1, p. 130 (genus of one class: necessary and sufficient conditions)"] QuadFormsKB.Siegel.exists_primRep_of_one_class
attribute [kb "cassels1978" "Ch. 9, Thm. 1.1, p. 128 (generalization to number fields)"] QuadFormsKB.Lattices.ClassFin.classes_finite
attribute [kb "cassels1978" "Ch. 9, Thm. 1.5, p. 131 (generalization to number fields)"] QuadFormsKB.Lattices.vecApprox_of_indefinite
attribute [kb "cassels1978" "Ch. 9, Thm. 1.5, p. 131 (generalization to number fields, approximation part)"] QuadFormsKB.Lattices.vecStrongApproximation
attribute [kb "cassels1978" "Ch. 9, Lemma 3.2, Cor. 2, p. 138"] QuadFormsKB.Siegel.Hermite.unimodular_posDef_equiv_one
attribute [kb "cassels1978" "Ch. 9, Lemma 3.2, Cor. 2, p. 138 (genus of one class)"] QuadFormsKB.Siegel.genusClasses_sumSq
attribute [kb "cassels1978" "Ch. 9, §5, p. 144 (sums of at most five squares: genus of one class)"] QuadFormsKB.Siegel.genusClasses_sumSq
attribute [kb "cassels1978" "Ch. 9, Lemma 3.2, Cor. 2, p. 138 (proof route)"] QuadFormsKB.Siegel.sameGenus_sumSq_intEquiv
attribute [kb "cassels1978" "Ch. 9, Lemma 4.2, p. 140 (variant: lattice version over a number field, isometry not necessarily proper)"] QuadFormsKB.Lattices.exists_isometric_agree
attribute [kb "cassels1978" "Ch. 9, §6, p. 144 ((6.1)–(6.2): proper integral automorphs)"] QuadFormsKB.Siegel.AutPlus
attribute [kb "cassels1978" "Ch. 9, §6, (6.9), p. 146 (variant: half the weight)"] QuadFormsKB.Siegel.mass
attribute [kb "cassels1978" "Ch. 9, §6, (6.9), p. 146 (variant: half the weight)"] QuadFormsKB.Lattices.mass
attribute [kb "cassels1978" "Ch. 9, §6, p. 149 (formulas for the weight of a genus need the analytic theory; variant)"] QuadFormsKB.Tamagawa.massFormula
attribute [kb "cassels1978" "Ch. 9, Lemma 6.4, p. 150 (proof step (6.34): o+(f) = 24)"] QuadFormsKB.Siegel.card_autPlus_sumSq_three
attribute [kb "cassels1978" "Ch. 9, Lemma 6.4, p. 150 (proof step: genus of one class)"] QuadFormsKB.Siegel.pgenusClasses_sumSq_three
attribute [kb "cassels1978" "Ch. 9, Lemma 6.5, p. 152 (proof step (6.45))"] QuadFormsKB.Siegel.card_autPlus_sumSq_four
attribute [kb "cassels1978" "Ch. 9, Lemma 6.6, p. 152 (the forms of (6.46) lie in one genus)"] QuadFormsKB.Siegel.sameGenus_lemma66
attribute [kb "cassels1978" "Ch. 9, Thm. 7.2, p. 155 (variant: approximation of products of symmetries over a number field)"] QuadFormsKB.Lattices.exists_symmProd_approx
attribute [kb "cassels1978" "Ch. 9, Notes, p. 161 (generalization of the chapter to number fields)"] QuadFormsKB.Lattices.exists_sameGenus_primitive
attribute [kb "cassels1978" "Ch. 9, Notes, p. 161 (Thm. 1.5 generalized: isotropy at one place, O'Meara 104:3)"] QuadFormsKB.Lattices.vecApprox_of_indefinite
attribute [kb "cassels1978" "Ch. 9, Notes, p. 161 (Thm. 1.5 fails for n = 3)"] QuadFormsKB.Siegel.ex23_not_primRep
attribute [kb "cassels1978" "Ch. 9, Examples, Ex. 23, p. 168 (over ℝ)"] QuadFormsKB.Siegel.ex23_real
attribute [kb "cassels1978" "Ch. 9, §3, p. 139 (forms of one genus are rationally equivalent)"] QuadFormsKB.Lattices.isometricGL_rat_of_sameGenus
attribute [kb "cassels1978" "Ch. 10, §1, p. 169 (aim: a strong approximation theorem)"] QuadFormsKB.Lattices.strongApproximationSpin
attribute [kb "cassels1978" "Ch. 10, §1, p. 170 (the norm $N(uv) = N(u)N(v)$ of Hamilton's quaternions; general quaternion algebra)"] QuadFormsKB.Quat.nrd_mul
attribute [kb "cassels1978" "Ch. 10, §1, p. 170 (conjugation of the pure quaternions, $y = uxu^{-1}$; variant)"] QuadFormsKB.Quat.conjLin
attribute [kb "cassels1978" "Ch. 10, §1, p. 170 (homomorphism from the quaternion units to the rotations; variant)"] QuadFormsKB.Quat.conjSO
attribute [kb "cassels1978" "Ch. 10, §1, p. 170 (conjugation is proper; variant)"] QuadFormsKB.Quat.det_conjLin
attribute [kb "cassels1978" "Ch. 10, §1, p. 170 (onto the rotations; variant)"] QuadFormsKB.Quat.conjSO_surjective
attribute [kb "cassels1978" "Ch. 10, §1, p. 170 (kernel; variant: $K^\\times$ on all units)"] QuadFormsKB.Quat.ker_conjSO
attribute [kb "cassels1978" "Ch. 10, Cor. 3 to Thm. 3.1, p. 178 (the spinor norm homomorphism; defined via symmetries)"] QuadFormsKB.OMeara.spinorNormHom
attribute [kb "cassels1978" "Ch. 10, Cor. 3 to Thm. 3.1, p. 178 (the spinor norm homomorphism; defined via symmetries)"] QuadFormsKB.Lattices.spinorNormHom
attribute [kb "cassels1978" "Ch. 10, Cor. 3 to Thm. 3.1, p. 178 ($\\Theta = \\ker\\theta$)"] QuadFormsKB.OMeara.ker_spinorNormHom
attribute [kb "cassels1978" "Ch. 10, Cor. 3 to Thm. 3.1, p. 178 ($\\Theta = \\ker\\theta \\cap O^+$)"] QuadFormsKB.Lattices.spinorKernel_eq_ker
attribute [kb "cassels1978" "Ch. 10, §3, p. 176 (definition of $M_0(V)$)"] QuadFormsKB.Cassels.M0
attribute [kb "cassels1978" "Ch. 10, Cor. 1 to Lemma 3.3, p. 179"] QuadFormsKB.Lattices.eqPairGroup_eq_commutator
attribute [kb "cassels1978" "Ch. 10, Thm. 3.2, p. 179 ($\\Omega \\subseteq \\Theta$)"] QuadFormsKB.OMeara.omega_le_orthPrime
attribute [kb "cassels1978" "Ch. 10, Thm. 3.2, p. 179 ($\\Omega = \\Theta$ for isotropic $V$)"] QuadFormsKB.OMeara.omega_eq_orthPrime_of_isotropic
attribute [kb "cassels1978" "Ch. 10, Thm. 3.2, p. 179 (isotropic case; with Cor. 1 to Lemma 3.3, $\\Omega = \\Theta$)"] QuadFormsKB.Lattices.spinorKernel_eq_eqPairGroup
attribute [kb "cassels1978" "Ch. 10, Thm. 3.2, Note, p. 179 (other cases of $\\Omega = \\Theta$)"] QuadFormsKB.OMeara.omega_eq_orthPrime_of_finrank_le_three
attribute [kb "cassels1978" "Ch. 10, Thm. 3.2, p. 180 (proof route: reduction to a hyperbolic plane; variant)"] QuadFormsKB.OMeara.omega_eq_orthPrime_of_subspace
attribute [kb "cassels1978" "Ch. 10, §4, p. 182 (definition of $O(\\Lambda)$)"] QuadFormsKB.Lattices.autLat
attribute [kb "cassels1978" "Ch. 10, Lemma 4.1, p. 183 (equality (4.11), over a number field; variant)"] QuadFormsKB.Lattices.mem_localSpinorNormGroup_iff_of_unimodular
attribute [kb "cassels1978" "Ch. 10, §6, p. 185 ($O(V) \\to O(V_K)$)"] QuadFormsKB.Lattices.orthMap
attribute [kb "cassels1978" "Ch. 10, §7, p. 186 ($O(\\Lambda_p)$ is open; special case)"] QuadFormsKB.Tamagawa.Measure.isOpen_stdStab
attribute [kb "cassels1978" "Ch. 10, §7, p. 186 ($O(\\Lambda_p)$ is open; generalization)"] QuadFormsKB.Lattices.exists_mem_nhds_locAct_eq
attribute [kb "cassels1978" "Ch. 10, §7, p. 186 ($\\Lambda_p = \\Gamma_p$ for almost all $p$)"] QuadFormsKB.Lattices.loc_eventually_std
attribute [kb "cassels1978" "Ch. 10, Thm. 7.1, p. 188 (proof route, $n = 3$: through the quaternary norm form; variant)"] QuadFormsKB.Lattices.rotApprox_ternary
attribute [kb "cassels1978" "Ch. 10, Thm. 7.1, p. 189 (proof route, $n \\ge 4$; variant)"] QuadFormsKB.Lattices.list_approx
attribute [kb "cassels1978" "Ch. 10, Thm. 7.1, p. 190 (proof route, $n \\ge 4$: correction at the remaining primes; variant)"] QuadFormsKB.Lattices.exists_correction
attribute [kb "cassels1978" "Ch. 10, Notes, p. 191 (generalization to number fields)"] QuadFormsKB.Lattices.strongApproximationSpin
attribute [kb "cassels1978" "Ch. 11, §7, proof of Lemma 7.1, (7.5)–(7.12), pp. 229–230 (proof route)"] QuadFormsKB.Lattices.spnRepresentsPrim_shift
attribute [kb "cassels1978" "Ch. 11, §7, proof of Lemma 7.1, p. 229 (proof route: hyperbolic plane)"] QuadFormsKB.Lattices.exists_isotropic_qbil_eq_one
attribute [kb "cassels1978" "Ch. 11, §1, p. 196 (equivalence of lattices in the wide sense: definition)"] QuadFormsKB.Lattices.IsIsometric
attribute [kb "cassels1978" "Ch. 11, §1, p. 196 (the form of a lattice with a basis)"] QuadFormsKB.Lattices.basisForm
attribute [kb "cassels1978" "Ch. 11, §1, p. 196 (the lattice of a form: inverse of the correspondence of Lemma 1.1)"] QuadFormsKB.Lattices.latOf
attribute [kb "cassels1978" "Ch. 11, §1, p. 198 (forms of one genus are lattices in one space; generalization: number field)"] QuadFormsKB.Lattices.Steinitz.exists_latOf_of_sameGenus
attribute [kb "cassels1978" "Ch. 11, §1, p. 199 (genus of lattices, (1.5)–(1.6); generalization: full orthogonal group, number field)"] QuadFormsKB.Lattices.SameGenus
attribute [kb "cassels1978" "Ch. 11, Thm. 1.2, p. 202 (finiteness part: finitely many classes, so finitely many spinor genera; generalization)"] QuadFormsKB.Lattices.genusClasses_finite
attribute [kb "cassels1978" "Ch. 11, Thm. 1.4, p. 202 (variant: full orthogonal group, isotropic case)"] QuadFormsKB.Lattices.classesEquivSpinorGenera'
attribute [kb "cassels1978" "Ch. 11, Thm. 1.2, p. 202 (the spinor genera as double cosets; variant)"] QuadFormsKB.Lattices.dosetEquivSpinorGenera
attribute [kb "cassels1978" "Ch. 11, §1, p. 200 ((1.16), (1.17): the spinor norm on O⁺(V), O⁺(V_p))"] QuadFormsKB.Lattices.spinorNorm
attribute [kb "cassels1978" "Ch. 11, Lemma 1.5, p. 203 (the form φ(b_j) = q_j)"] QuadFormsKB.Lattices.casselsOddPrimeForm
attribute [kb "cassels1978" "Ch. 11, §3, (3.8)–(3.14), pp. 208–209 (the groups R, S, T and the diagonal map)"] QuadFormsKB.Lattices.CasselsR
attribute [kb "cassels1978" "Ch. 11, §3, (3.8)–(3.14), pp. 208–209 (the groups R, S, T and the diagonal map)"] QuadFormsKB.Lattices.casselsS
attribute [kb "cassels1978" "Ch. 11, §3, (3.8)–(3.14), pp. 208–209 (the groups R, S, T and the diagonal map)"] QuadFormsKB.Lattices.casselsT
attribute [kb "cassels1978" "Ch. 11, §3, (3.8)–(3.14), pp. 208–209 (the groups R, S, T and the diagonal map)"] QuadFormsKB.Lattices.casselsDiag
attribute [kb "cassels1978" "Ch. 11, §3, (3.15), p. 209 (G = R/ST)"] QuadFormsKB.Lattices.CasselsG
attribute [kb "cassels1978" "Ch. 11, §3, (3.15), p. 209 (G = R/ST)"] QuadFormsKB.Lattices.casselsST
attribute [kb "cassels1978" "Ch. 11, §3, (3.11), p. 209 (R² ⊆ S; reading uncertain)"] QuadFormsKB.Lattices.sq_mem_casselsS
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4 (ii)/(iii), p. 201 (variant: full orthogonal group)"] QuadFormsKB.Lattices.IsIsometric.sameSpinorGenus
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4 (ii)/(iii), p. 201 (variant: full orthogonal group)"] QuadFormsKB.Lattices.SameSpinorGenus.sameGenus
attribute [kb "cassels1978" "Ch. 11, Notes, p. 249 (Theorem 1.1 over the ring of integers of a number field; generalization)"] QuadFormsKB.Lattices.LocFamily.existsUnique_loc_eq
attribute [kb "cassels1978" "Ch. 11, Thm. 1.6, p. 204 (variant: n even ≥ 6, ordinary representation, non-explicit constant)"] QuadFormsKB.Siegel.tartakowsky_even
attribute [kb "cassels1978" "Ch. 11, Thm. 1.6, p. 204 (variant: n even ≥ 6, number field, class number one)"] QuadFormsKB.HilbertModular.tartakowsky_nf'
attribute [kb "cassels1978" "Ch. 11, Examples, Ex. 2, p. 251 (the same pair of forms up to renaming the variables)"] QuadFormsKB.Siegel.ex3_ternary
attribute [kb "cassels1978" "Ch. 11, Notes, p. 251 (Liouville-type formula: special case, four squares)"] QuadFormsKB.Siegel.repNum_sumSq_four
attribute [kb "cassels1978" "add `Ch. 11, Notes, p. 249 (the equivalence of O'Meara's and Watson's definitions of the spinor genus)"] QuadFormsKB.Lattices.sameProperSpinorGenus_latSMul_of_casselsI
attribute [kb "cassels1978" "add `Ch. 11, Notes, p. 249 (generalization to number fields)"] QuadFormsKB.Lattices.spinorGeneraEquivQuot
attribute [kb "cassels1978" "Ch. 12, §1, Thm. 1.1, p. 256 (proof: finitely many integral m with f(m) < M)"] QuadFormsKB.Reduction.finite_val_le
attribute [kb "cassels1978" "Ch. 12, §1, p. 260 (triangle inequality for the square root of f)"] QuadFormsKB.Reduction.sqrt_val_add_le
attribute [kb "cassels1978" "Ch. 12, §1, (1.9), p. 260"] QuadFormsKB.Reduction.sqrt_val_sum_le
attribute [kb "cassels1978" "Ch. 12, §3, (3.1), p. 263 (existence of the decomposition by completing the square)"] QuadFormsKB.Reduction.exists_isSqDecomp
attribute [kb "cassels1978" "Ch. 12, §3, proof of Thm. 3.1 (iii), p. 265 (h_1 ⋯ h_n = d(f))"] QuadFormsKB.Reduction.IsSqDecomp.det_eq
attribute [kb "cassels1978" "Ch. 12, §3, proof of Lemma 1.3, (3.4), p. 265"] QuadFormsKB.Reduction.IsSqDecomp.offdiag_eq
attribute [kb "cassels1978" "Ch. 12, §1, p. 257 (the union of the TR is the set of all positive definite forms); §6, p. 275, fact (i) (special case n = 2)"] QuadFormsKB.Reduction.thm_7_1
attribute [kb "cassels1978" "Ch. 12, §6, p. 275, fact (ii) (special case n = 2)"] QuadFormsKB.Reduction.thm_7_4
attribute [kb "cassels1978" "Ch. 12, §1, p. 257 (the reduced forms form a cone bounded by finitely many hyperplanes)"] QuadFormsKB.Reduction.thm_5_2_cor
attribute [kb "cassels1978" "Ch. 12, §6, p. 275 (T maps strictly definite forms to strictly definite forms)"] QuadFormsKB.Reduction.PosDef.act
attribute [kb "cassels1978" "Ch. 12, §1, Thm. 1.2, p. 256 (finiteness form: finitely many T)"] QuadFormsKB.Reduction.finite_gl_reduced_pair
attribute [kb "cassels1978" "Ch. 13, §4, (4.1), p. 298 (rational automorphs generated by symmetries; recalled from Ch. 2, Lemma 4.3)"] QuadFormsKB.Lattices.exists_symmProd_eq
attribute [kb "cassels1978" "Ch. 13, §3, (3.8), p. 290 (classically integral; variant for n-ary forms over ℤ)"] QuadFormsKB.IsClassicallyIntegral
attribute [kb "cassels1978" "Ch. 13, §3, (3.21)–(3.22), p. 292 (the linear forms L and M)"] QuadFormsKB.Cassels.Ch13.linLM
attribute [kb "cassels1978" "Ch. 13, §3, (3.24), p. 292 (η = t + u√D)"] QuadFormsKB.Cassels.Ch13.etaHom
attribute [kb "cassels1978" "Ch. 13, §12, p. 327 (iii) (variant: indefinite, same proper spinor genus implies properly equivalent; over a number field)"] QuadFormsKB.Lattices.properSpinorGenus_eq_properClass
attribute [kb "cassels1978" "Ch. 13, §1, p. 284 (variant: O(L) finite for lattices in a totally positive definite space over a number field)"] QuadFormsKB.Lattices.finite_autLat
attribute [kb "cassels1978" "Ch. 13, Examples, Ex. 1, p. 328 (special case: fundamental discriminant)"] QuadFormsKB.Binary.card_autSL
attribute [kb "cassels1978" "Ch. 14, §1, p. 331 (primitive form: gcd(a,b,c) = 1)"] QuadFormsKB.Binary.Primitive
attribute [kb "cassels1978" "Ch. 14, §1, (1.4), p. 331 (discriminant D = b² − 4ac)"] QuadFormsKB.BinQF.disc
attribute [kb "cassels1978" "Ch. 14, §1, (1.5), p. 331 (D = −4d(f), via the Hessian)"] QuadFormsKB.BinQF.disc_eq_neg_det_hessian
attribute [kb "cassels1978" "Ch. 14, §1, (1.6), p. 331 (D ≡ 0, 1 mod 4)"] QuadFormsKB.BinQF.disc_mod_four
attribute [kb "cassels1978" "Ch. 14, §1, p. 331 (class means proper equivalence)"] QuadFormsKB.Binary.SLEquiv
attribute [kb "cassels1978" "Ch. 14, §1, p. 331 (variant: D < 0 fundamental, group of classes via ideal classes)"] QuadFormsKB.Binary.slClassEquiv
attribute [kb "cassels1978" "Ch. 14, §1, (1.8)–(1.10), pp. 331–332 (composition is independent of the choices)"] QuadFormsKB.Cassels.sLEquiv_compose
attribute [kb "cassels1978" "Ch. 14, Thm. 2.1, p. 338 (inverse class = class of improperly equivalent forms; D < 0 fundamental)"] QuadFormsKB.Binary.idealClass_conj
attribute [kb "cassels1978" "Ch. 14, Thm. 2.1, p. 337 (proof: finiteness of the group; D < 0 fundamental)"] QuadFormsKB.Binary.card_slClasses
attribute [kb "cassels1978" "Ch. 14, §1, p. 332 (preview of Gauss's theorem: squares = principal genus)"] QuadFormsKB.Binary.principalGenus_eq_sq
attribute [kb "cassels1978" "Ch. 14, §1, p. 332 (number of genera = order of G/G²; variant: D < 0 fundamental)"] QuadFormsKB.Binary.card_genera
attribute [kb "cassels1978" "Ch. 14, §1, (1.13), p. 332 and §4, (4.1), p. 341 (ambiguous class: improperly equivalent to itself)"] QuadFormsKB.Binary.sLEquiv_conj_iff
attribute [kb "cassels1978" "Ch. 14, §4, (4.1), p. 341 (an improper automorph exists iff the form is equivalent to its opposite)"] QuadFormsKB.Binary.exists_improper_iff
attribute [kb "cassels1978" "Ch. 14, §3, p. 339 (genus of a proper class; principal genus)"] QuadFormsKB.Binary.slGenus
attribute [kb "cassels1978" "Ch. 14, Thm. 3.1, p. 339 (proof step: a square lies in the principal genus; different proof)"] QuadFormsKB.Binary.IsFormClassGroup.genusHom_sq
attribute [kb "cassels1978" "Ch. 14, Cor. to Thm. 3.1, p. 339 (variant: every genus has h/2^(t−1) classes)"] QuadFormsKB.Binary.IsFormClassGroup.card_classes_in_genus
attribute [kb "cassels1978" "Ch. 14, Cor. to Thm. 3.1, p. 339 (variant: every genus has the same number of proper classes)"] QuadFormsKB.Binary.card_slClasses_in_genus
attribute [kb "cassels1978" "Ch. 14, Lemma 3.1 (i), p. 339 (special case: p odd, p ∤ D)"] QuadFormsKB.Binary.isometricGL_padic_of_not_dvd
attribute [kb "cassels1978" "Ch. 14, §4, p. 343 (order of the proper automorphs for D < 0 fundamental; variant)"] QuadFormsKB.Binary.card_autSL
attribute [kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343 (variant: the image has index 2 iff the product of the characters is 1; D < 0 fundamental)"] QuadFormsKB.Binary.prod_formChar_eq_one
attribute [kb "cassels1978" "Ch. 14, Cor. to Thm. 5.1, p. 344 (special case n = 2, hypothesis: a rational form exists instead of (5.4))"] QuadFormsKB.Siegel.exists_form_of_local_forms
attribute [kb "cassels1978" "Ch. 14, §6, pp. 345–346 (the ambiguous classes are the elements of order at most 2)"] QuadFormsKB.Binary.card_twoTorsion
attribute [kb "cassels1978" "Ch. 14, §7, p. 354 (variant: weak Hasse principle, isometry formulation)"] QuadFormsKB.isometric_iff_everywhere
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (the form N(xα + yβ)/N(J) of an ideal basis)"] QuadFormsKB.Binary.IsFormOf
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (an ideal has a basis of the shape l, m + nω; variant: Hermite normal form)"] QuadFormsKB.Binary.exists_eq_span_mul_formIdeal
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (proper classes of forms correspond to ideal classes; D < 0 fundamental)"] QuadFormsKB.Binary.idealClass_eq_of_sLEquiv
attribute [kb "cassels1978" "Ch. 14, Examples, Ex. 1, p. 358 (variant: fundamental discriminant, excluding D = 1)` and `Ch. 14, Notes, p. 354 (fundamental discriminant)"] QuadFormsKB.Binary.IsQuadDisc
attribute [kb "cassels1978" "Ch. 14, Examples, Ex. 2, p. 358 (Kronecker symbol (D/b) for b > 0; fundamental D)"] QuadFormsKB.Binary.kronZ
attribute [kb "cassels1978" "Ch. 14, Examples, Ex. 2 (i), p. 358 (only if: variant for fundamental D)"] QuadFormsKB.Binary.kronZ_eq_one_of_primRep
attribute [kb "cassels1978" "extend existing tag: `Ch. 14, Lemma 4.1, p. 341 (variant: normal form a ∣ b instead of b ∈ {0, a})"] QuadFormsKB.Binary.exists_sLEquiv_a_dvd_b
attribute [kb "cassels1978" "extend existing tag: `Ch. 14, Thm. 2.1, p. 337 (variant: D < 0 fundamental, group law transported from ideal classes)"] QuadFormsKB.Binary.isFormClassGroup
attribute [kb "cassels1978" "App. A, §2, p. 362 (orthogonal sum of sublattices, (i)–(ii); several summands, p. 363)"] QuadFormsKB.Lattices.IsOrthSplitting
attribute [kb "cassels1978" "App. A, §2, p. 362 (condition (ii): the summands are mutually orthogonal)"] QuadFormsKB.Lattices.LatOrth
attribute [kb "cassels1978" "App. A, §2, p. 362 (indecomposable lattice; here non-zero)"] QuadFormsKB.Lattices.IsIndecomposable
attribute [kb "cassels1978" "App. A, §2, (2.1)–(2.2), p. 363 (decomposable vector)"] QuadFormsKB.Lattices.IsReducibleVec
attribute [kb "cassels1978" "App. A, §3, p. 365 (the lattice Γ₈: 8-dimensional, integer-valued, determinant 1)"] QuadFormsKB.Siegel.e8
attribute [kb "cassels1978" "App. A, §3, p. 365 (Γ₈ has determinant 1)"] QuadFormsKB.Siegel.e8_det
attribute [kb "cassels1978" "App. A, §3, p. 365 (Γ₈ is positive definite)"] QuadFormsKB.Siegel.e8_posDef
attribute [kb "cassels1978" "App. A, §3, p. 365 (special case: existence of a determinant-1 form in 16 variables; cf. Ch. 9, Ex. 10)"] QuadFormsKB.Siegel.ex10
attribute [kb "cassels1978" "App. A, Examples, Ex. 1 (iii), p. 367 (variant: O'Meara's lattice E, 4 ∣ n, n ≥ 8)"] QuadFormsKB.Lattices.omearaE_indecomposable
attribute [kb "cassels1978" "App. B, §1, (1.1 bis), p. 369 (generalization: the inversion law for any positive definite integral form)"] QuadFormsKB.Siegel.theta_S'
attribute [kb "cassels1978" "App. B, §1, (1.1 bis), p. 369 (analogue for an even unimodular form: Θ(−1/z) = z^k Θ(z))"] QuadFormsKB.Siegel.theta_S_unimodular
attribute [kb "cassels1978" "App. B, §1, (1.2), p. 369 (Jacobi: sums of two squares)"] QuadFormsKB.Tamagawa.Classical.jacobi_two_squares
attribute [kb "cassels1978" "App. B, §1, (1.3), p. 369 (Jacobi: sums of four squares)"] QuadFormsKB.Siegel.repNum_sumSq_four
attribute [kb "cassels1978" "App. B, §2, (2.1)–(2.3), p. 370 (the discriminant, ≡ 0, 1 mod 4)"] QuadFormsKB.BinQF.disc
attribute [kb "cassels1978" "App. B, §2, (2.3), p. 370 (h(D) for D < 0 is the number of proper classes)"] QuadFormsKB.Binary.card_slClasses
attribute [kb "cassels1978" "App. B, §2, (2.4), p. 371 (fundamental discriminant)"] QuadFormsKB.Binary.IsQuadDisc
attribute [kb "cassels1978" "App. B, §2, (2.5), p. 371 (the Kronecker symbol)"] QuadFormsKB.Binary.kronZ
attribute [kb "cassels1978" "App. B, §2, proof of Lemma 2.1, p. 371 (w is the number of proper automorphs, D < 0)"] QuadFormsKB.Binary.card_autSL
attribute [kb "cassels1978" "App. B, Lemma 2.2, p. 372 (variant: (D/m) = +1 for m primitively represented, m prime to D)"] QuadFormsKB.Binary.kronZ_eq_one_of_primRep
attribute [kb "cassels1978" "App. B, §3, (3.1), p. 375 (Euler product of L(1, χ_D))"] QuadFormsKB.Binary.eulerProductAtOne
attribute [kb "cassels1978" "App. B, §3, p. 375 (the weight over proper classes is twice Siegel's weight)"] QuadFormsKB.Tamagawa.mass_SO_eq_two_mul_mass
attribute [kb "cassels1978" "App. B, §3, (3.2), p. 375 (unconditional form, rank ≥ 3)"] QuadFormsKB.Tamagawa.massFormula_all_ranks_uncond
attribute [kb "cassels1978" "App. B, §3, (3.4)–(3.5), p. 376 (the local factors at good primes, n odd)"] QuadFormsKB.Tamagawa.hasProd_siegelDensity_odd
attribute [kb "cassels1978" "App. B, §3, (3.4)–(3.5), p. 376 (the local factors at good primes, n even)"] QuadFormsKB.Tamagawa.hasProd_siegelDensity_even
attribute [kb "cassels1978" "App. B, §3, (3.6)–(3.7), p. 376 (the archimedean factor)"] QuadFormsKB.Tamagawa.archVolSO
attribute [kb "cassels1978" "App. B, §3, p. 377 (special case: the genus of x_1² + … + x_n² has one class for n ≤ 5)"] QuadFormsKB.Siegel.genusClasses_sumSq
attribute [kb "cassels1978" "App. B, §3, (3.12), p. 378 (special case l = 1: the weighted average)"] QuadFormsKB.Siegel.genusRepAvg
attribute [kb "cassels1978" "App. B, §3, (3.13), p. 378 (special case l = 1, rank ≥ 4, unconditional)"] QuadFormsKB.Tamagawa.siegelFormula_int_all_ranks_uncond
attribute [kb "cassels1978" "App. B, §3, p. 378 (a one-class genus: four squares)"] QuadFormsKB.Siegel.siegelFormula_Q4'
attribute [kb "cassels1978" "App. B, Thm. 4.1, p. 380 (proved for dim V ≥ 3)"] QuadFormsKB.Tamagawa.Measure.Weil.tauTwo_space_uncond
attribute [kb "cassels1978" "App. B, Thm. 4.1, p. 380 (proved for n ≥ 3, every number field)"] QuadFormsKB.Tamagawa.Measure.Weil.tauTwoAll_release_uncond
attribute [kb "cassels1978" "App. B, §4, p. 379 (the adelic orthogonal group: finite adeles, full O, over a number field)"] QuadFormsKB.Lattices.OAf
attribute [kb "cassels1978" "App. B, §4, (4.7)–(4.10), pp. 380–381 (classes of the genus as double cosets)"] QuadFormsKB.Lattices.dosetEquivClassesInGenus
attribute [kb "cassels1978" "App. B, §4, (4.2)–(4.3), pp. 379–380 (the Tamagawa measure of the stabilizer)"] QuadFormsKB.Tamagawa.tamagawaK
attribute [kb "cassels1978" "App. B, §5, (5.1), p. 382 (the theta series)"] QuadFormsKB.Siegel.theta
attribute [kb "cassels1978" "App. B, §5, (5.18), p. 385 (the Stufe; here any level)"] QuadFormsKB.Siegel.IsThetaLevel
attribute [kb "cassels1978" "App. B, §5, (5.19), p. 386 (the character ε of the theta series)"] QuadFormsKB.Siegel.thetaChi
attribute [kb "cassels1978" "App. B, §5, (5.20), p. 386 (Θ(f,t) ∈ M(k, N, ε): the transformation law on Γ₀(N))"] QuadFormsKB.Siegel.theta_gamma0_chi
attribute [kb "cassels1978" "App. B, §5, (5.22), p. 386 (the Stufe and character depend only on the genus)"] QuadFormsKB.Siegel.SameGenus.thetaMult_eq
attribute [kb "cassels1978" "App. B, §5, p. 386 (cusp form coefficients are of smaller order than Eisenstein ones)"] QuadFormsKB.Siegel.cuspBound_hecke
attribute [kb "cassels1978" "App. B, §5, (5.23), p. 386 (variant: representation numbers = genus average + cusp coefficient)"] QuadFormsKB.Siegel.repNum_eq_aE_add_genusCuspCoeff_uncond
attribute [kb "cassels1978" "App. B, §5, (5.24), p. 386 (the genus theta series as a modular form)"] QuadFormsKB.Siegel.GenusEis.thetaGenMF
attribute [kb "cassels1978" "Ch. 14, Lemma 4.3, Cor., p. 343"] QuadFormsKB.Binary.card_twoTorsion
attribute [kb "cassels1978" "App. B, Thm. 2.1 (i), p. 371 (variant: L(1, χ_D) = 2πh/(w√|D|))"] QuadFormsKB.Binary.classNumberFormula_neg
attribute [kb "cassels1978" "App. B, Thm. 2.1 (ii), p. 371 (variant: L(1, χ_D) = 2hR/√D)"] QuadFormsKB.Binary.classNumberFormula_pos
attribute [kb "cassels1978" "Ch. 14, Lemma 2.1, p. 334"] QuadFormsKB.Binary.exists_coprime_value
attribute [kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343"] QuadFormsKB.Binary.exists_form_of_signs
attribute [kb "cassels1978" "Ch. 14, Lemma 4.1, p. 341"] QuadFormsKB.Binary.exists_sLEquiv_a_dvd_b
attribute [kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343"] QuadFormsKB.Binary.generaVec_bijective
attribute [kb "cassels1978" "Ch. 14, Thm. 2.1, p. 337"] QuadFormsKB.Binary.isFormClassGroup
attribute [kb "cassels1978" "Ch. 14, Thm. 3.1, p. 339"] QuadFormsKB.Binary.principalGenus_eq_sq
attribute [kb "cassels1978" "App. B, (3.13), p. 378"] QuadFormsKB.Binary.siegelFormula_binary
attribute [kb "cassels1978" "App. B, §5, p. 388 (Eichler's description of Hecke operators)"] QuadFormsKB.HilbertModular.eisHeckeRel_eisQ
attribute [kb "cassels1978" "Ch. 9, Thm. 1.1, p. 128"] QuadFormsKB.Lattices.ClassFin.classes_finite
attribute [kb "cassels1978" "Ch. 11, Thm. 1.1, p. 198"] QuadFormsKB.Lattices.LocFamily.existsUnique_loc_eq
attribute [kb "cassels1978" "Ch. 8, Lemma 3.4 and Cor. to Thm. 3.1, pp. 115–116"] QuadFormsKB.Lattices.Nbr.isometricGL_of_unimodular_dvr
attribute [kb "cassels1978" "App. B, §5, p. 388 (Eichler's description of Hecke operators)"] QuadFormsKB.Lattices.Nbr.sum_latRep_neighbors_of_not_dvd
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4, p. 200"] QuadFormsKB.Lattices.SameSpinorGenus.refl
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4, p. 200"] QuadFormsKB.Lattices.SameSpinorGenus.symm
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4, p. 200"] QuadFormsKB.Lattices.SameSpinorGenus.trans
attribute [kb "cassels1978" "Ch. 11, Thm. 1.4, p. 202"] QuadFormsKB.Lattices.eichler_spinorGenus_eq_class_uncond
attribute [kb "cassels1978" "Ch. 10, Lemma 7.2, p. 190"] QuadFormsKB.Lattices.eqPair_approx
attribute [kb "cassels1978" "Ch. 9, Lemma 4.2, p. 140"] QuadFormsKB.Lattices.exists_isometric_agree
attribute [kb "cassels1978" "Ch. 9, Thm. 7.2, p. 155"] QuadFormsKB.Lattices.exists_symmProd_approx
attribute [kb "cassels1978" "Ch. 11, Lemma 8.1, p. 231"] QuadFormsKB.Lattices.exists_very_strong_approx
attribute [kb "cassels1978" "Ch. 11, Lemma 8.1, p. 231"] QuadFormsKB.Lattices.exists_very_strong_approx_at
attribute [kb "cassels1978" "Ch. 11, Thm. 1.5, p. 203; Ch. 11, Lemma 3.6, Cor., p. 213"] QuadFormsKB.Lattices.isIsometric_of_sameGenus
attribute [kb "cassels1978" "Ch. 11, Thm. 1.4, p. 202"] QuadFormsKB.Lattices.latSpinorGenus_eq_class'
attribute [kb "cassels1978" "Ch. 10, Lemma 4.1, p. 183; Ch. 11, Lemma 3.3, p. 208"] QuadFormsKB.Lattices.localSpinorUnits_of_unimodular
attribute [kb "cassels1978" "Ch. 9, §6, (6.9), p. 146 (weight of a genus; differs by the factor 2)"] QuadFormsKB.Lattices.mass
attribute [kb "cassels1978" "Ch. 10, Lemma 7.2, p. 190"] QuadFormsKB.Lattices.pair_approx
attribute [kb "cassels1978" "Ch. 11, Thm. 8.2, p. 232"] QuadFormsKB.Lattices.rotApproxAt_of_isotropicAt
attribute [kb "cassels1978" "Ch. 11, Thm. 1.5, p. 203; Ch. 11, Lemma 3.6, Cor., p. 213"] QuadFormsKB.Lattices.sameSpinorGenus_of_sameGenus
attribute [kb "cassels1978" "Ch. 11, Thm. 3.1, p. 211"] QuadFormsKB.Lattices.spinorGeneraEquivQuot
attribute [kb "cassels1978" "Ch. 11, Thm. 1.2, p. 202"] QuadFormsKB.Lattices.spinorGeneraQuot_comm
attribute [kb "cassels1978" "Ch. 11, Thm. 1.2, p. 202"] QuadFormsKB.Lattices.spinorGeneraQuot_mul_self
attribute [kb "cassels1978" "Ch. 10, Lemma 4.1, p. 183; Ch. 11, Lemma 3.3, p. 208"] QuadFormsKB.Lattices.spinorNorm_stdStab_unit
attribute [kb "cassels1978" "Ch. 10, Thm. 7.1, Cor., p. 187"] QuadFormsKB.Lattices.strongApproximationSpin
attribute [kb "cassels1978" "Ch. 11, Thm. 8.2, p. 232"] QuadFormsKB.Lattices.strongApproximationSpinAt
attribute [kb "cassels1978" "Ch. 8, Lemma 3.2, p. 114"] QuadFormsKB.Lattices.symm_mem_stdStab'
attribute [kb "cassels1978" "Ch. 11, Thm. 8.1, p. 231"] QuadFormsKB.Lattices.vecApproxAt_of_isotropicAt
attribute [kb "cassels1978" "Ch. 9, Thm. 1.5, p. 131; Ch. 10, Lemma 7.1, p. 187"] QuadFormsKB.Lattices.vecApprox_of_indefinite
attribute [kb "cassels1978" "Ch. 9, Thm. 1.5, p. 131; Ch. 10, Lemma 7.1, p. 187"] QuadFormsKB.Lattices.vecStrongApproximation
attribute [kb "cassels1978" "Ch. 8, Thm. 3.1, pp. 115–116 (existence)"] QuadFormsKB.LocalDensity.DVR.exists_jordanFormGen
attribute [kb "cassels1978" "Ch. 8, Thm. 3.1, pp. 115–116 (existence)"] QuadFormsKB.LocalDensity.exists_jordanForm
attribute [kb "cassels1978" "Ch. 8, Lemma 3.4 and Cor. to Thm. 3.1, pp. 115–116"] QuadFormsKB.Siegel.Kneser.isometricGL_of_unimodular
attribute [kb "cassels1978" "App. B, (3.13), p. 378"] QuadFormsKB.Siegel.SiegelFormula
attribute [kb "cassels1978" "Ch. 9, Lemma 3.2, Cor. 2, p. 138"] QuadFormsKB.Siegel.genusClasses_sumSq
attribute [kb "cassels1978" "App. B, (5.23)–(5.24), pp. 386–387"] QuadFormsKB.Siegel.hasSum_thetaGen
attribute [kb "cassels1978" "Ch. 9, §6, (6.9), p. 146 (weight of a genus; differs by the factor 2)"] QuadFormsKB.Siegel.mass
attribute [kb "cassels1978" "App. B, §5, p. 386 (no cusp forms: E_8)"] QuadFormsKB.Siegel.repNum_e8
attribute [kb "cassels1978" "App. B, §5, p. 386 (no cusp forms: E_8)"] QuadFormsKB.Siegel.thetaE8_eq_E₄
attribute [kb "cassels1978" "App. B, (5.23)–(5.24), pp. 386–387"] QuadFormsKB.Siegel.thetaGenCusp
attribute [kb "cassels1978" "App. B, (5.20), p. 386"] QuadFormsKB.Siegel.thetaSIF
attribute [kb "cassels1978" "App. B, (5.20), p. 386"] QuadFormsKB.Siegel.theta_U
attribute [kb "cassels1978" "App. B, (5.20), p. 386"] QuadFormsKB.Siegel.theta_fricke
attribute [kb "cassels1978" "Ch. 10, Thm. 7.1, Cor., p. 187"] QuadFormsKB.StrongApproximationSpin
attribute [kb "cassels1978" "App. B, Thm. 2.1, p. 371"] QuadFormsKB.Tamagawa.Classical.lFunction_kronecker_eight_one
attribute [kb "cassels1978" "App. B, Thm. 2.1, p. 371"] QuadFormsKB.Tamagawa.Classical.lFunction_kronecker_neg_four_one
attribute [kb "cassels1978" "App. B, Thm. 4.1, p. 380"] QuadFormsKB.Tamagawa.TamagawaNumberTwo
attribute [kb "cassels1978" "Ch. 8, Cor. to Lemma 3.2, p. 114"] QuadFormsKB.Tamagawa.exists_stdStab_det_neg_one
attribute [kb "cassels1978" "App. B, (3.2), p. 375"] QuadFormsKB.Tamagawa.massFormula
attribute [kb "cassels1978" "App. B, (3.2), p. 375"] QuadFormsKB.Tamagawa.massFormula_even
attribute [kb "cassels1978" "App. B, (3.2), p. 375"] QuadFormsKB.Tamagawa.massFormula_odd
attribute [kb "cassels1978" "App. B, §4, (4.11)–(4.19), pp. 380–382"] QuadFormsKB.Tamagawa.mass_eq_dcMass
attribute [kb "cassels1978" "App. B, §4, (4.11)–(4.19), pp. 380–382"] QuadFormsKB.Tamagawa.mass_mul_vol_eq
attribute [kb "cassels1978" "App. B, §4, (4.11)–(4.19), pp. 380–382"] QuadFormsKB.Tamagawa.tauSO
