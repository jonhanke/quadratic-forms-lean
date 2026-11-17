import Solution_SiegelTotallyReal
import Solution_TamagawaTotallyReal
import Solution_TamagawaSO
import Solution_TamagawaGroups
import Solution_LocalGlobal
import Solution_SiegelIndefinite
import Solution_SiegelWeil
import Solution_ClassicalCases
import Solution_ExactMass
import Solution_Classification
import Solution_Voight
import Solution_Shimura
import Solution_ChenevierLannes
import Solution_MorenoWagstaff

/-!
# Axiom check for the headline theorems

`lake env lean scripts/check_axioms.lean` prints the axioms each headline theorem depends on.
Every line should list only `propext`, `Classical.choice` and `Quot.sound`; the CI workflow
fails if any other axiom (in particular `sorryAx`) appears.
-/

-- Siegel's theorem over totally real number fields
#print axioms QuadFormsKB.Headlines.siegel_totallyReal
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank3
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank3'
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank2
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank2'
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank1
#print axioms QuadFormsKB.Headlines.siegelForms_totallyReal
-- The Tamagawa number and the mass formula over totally real number fields
#print axioms QuadFormsKB.Headlines.tamagawa_two_totallyReal
#print axioms QuadFormsKB.Headlines.massFormula_totallyReal
#print axioms QuadFormsKB.Headlines.tamagawa_two_totallyReal_ternary
#print axioms QuadFormsKB.Headlines.massFormula_totallyReal_ternary
-- The Tamagawa number of SO(V) over every number field
#print axioms QuadFormsKB.Headlines.tamagawa_two_numberField
#print axioms QuadFormsKB.Headlines.tamagawa_two_space
#print axioms QuadFormsKB.Headlines.tamagawa_one_rankOne
#print axioms QuadFormsKB.Headlines.tamagawa_two_binary
#print axioms QuadFormsKB.Headlines.tamagawa_two_space_binary
#print axioms QuadFormsKB.Headlines.tamagawa_one_binary_isotropic
#print axioms QuadFormsKB.Headlines.tamagawa_one_space_binary_isotropic
-- Tamagawa numbers of SL_n, GL_n and Sp_2
#print axioms QuadFormsKB.Headlines.tamagawa_SLn
#print axioms QuadFormsKB.Headlines.tamagawa_GLn
#print axioms QuadFormsKB.Headlines.tamagawa_Sp2
-- Local–global principles and reciprocity
#print axioms QuadFormsKB.Headlines.hilbertReciprocity_numberField
#print axioms QuadFormsKB.Headlines.hasseMinkowski_numberField
#print axioms QuadFormsKB.Headlines.represents_iff_everywhere_numberField
#print axioms QuadFormsKB.Headlines.isometric_iff_everywhere_numberField
#print axioms QuadFormsKB.Headlines.hasseMinkowski_rat
#print axioms QuadFormsKB.Headlines.quadraticReciprocity_polynomial
#print axioms QuadFormsKB.Headlines.hilbertReciprocity_ratFunc
-- Siegel's formula for indefinite forms over every number field
#print axioms QuadFormsKB.Headlines.siegel_indefinite_numberField
#print axioms QuadFormsKB.Headlines.siegel_indefinite_forms_numberField
#print axioms QuadFormsKB.Headlines.siegel_indefinite_forms_rank2
#print axioms QuadFormsKB.Headlines.siegel_indefinite_ternary
#print axioms QuadFormsKB.Headlines.siegel_indefinite_forms_rank2_isotropic
#print axioms QuadFormsKB.Headlines.siegel_indefinite_ternary_isotropic
#print axioms QuadFormsKB.Headlines.siegel_indefinite_forms_corank1
#print axioms QuadFormsKB.Headlines.siegel_indefinite_binary
#print axioms QuadFormsKB.Headlines.siegel_indefinite_forms_corank0
-- The Siegel–Weil formula over ℚ
#print axioms QuadFormsKB.Headlines.siegelWeil_rat
-- Classical cases over ℚ
#print axioms QuadFormsKB.Headlines.gauss_threeSquares
#print axioms QuadFormsKB.Headlines.jacobi_twoSquares
#print axioms QuadFormsKB.Headlines.siegel_twoSquares
#print axioms QuadFormsKB.Headlines.dirichlet_xSqMinusTwoYSq
#print axioms QuadFormsKB.Headlines.divisorCount_xy
#print axioms QuadFormsKB.Headlines.siegel_ternary_rat_natural
-- Exact mass formulas
#print axioms QuadFormsKB.Headlines.massFormula_genusSymbols
#print axioms QuadFormsKB.Headlines.shimuraMass_odd
#print axioms QuadFormsKB.Headlines.shimuraMass_even
#print axioms QuadFormsKB.Headlines.hankeMass_numberField
-- Classification of lattices and genera, and class numbers
#print axioms QuadFormsKB.Headlines.automorphous_iff_rootVectors
#print axioms QuadFormsKB.Headlines.dyadicClassification
#print axioms QuadFormsKB.Headlines.twoAdicClassification
#print axioms QuadFormsKB.Headlines.sameGenus_iff_discIso
#print axioms QuadFormsKB.Headlines.sameGenus_iff_discIso_one
#print axioms QuadFormsKB.Headlines.watson_twoClasses
-- J. Voight, Quaternion Algebras
#print axioms QuadFormsKB.Headlines.voight_maximal_iff_discriminant
#print axioms QuadFormsKB.Headlines.voight_evenClifford_correspondence
#print axioms QuadFormsKB.Headlines.eichlerMass_totallyReal
#print axioms QuadFormsKB.Headlines.eichlerMass_rat
#print axioms QuadFormsKB.Headlines.eichlerMass_eichlerOrders_rat
-- G. Shimura, Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups
#print axioms QuadFormsKB.Headlines.shimura_theorem11_6_i
#print axioms QuadFormsKB.Headlines.shimura_theorem11_6_v
#print axioms QuadFormsKB.Headlines.shimura_formula13_18
-- G. Chenevier and J. Lannes, Automorphic Forms and Even Unimodular Lattices
#print axioms QuadFormsKB.Headlines.evenUnimodular_classes
#print axioms QuadFormsKB.Headlines.witt_evenUnimodular_sixteen
#print axioms QuadFormsKB.Headlines.siegelTheta_modular
#print axioms QuadFormsKB.Headlines.venkov_rootSum
#print axioms QuadFormsKB.Headlines.heckeT_comm
#print axioms QuadFormsKB.Headlines.wittIgusa_of_cuspVanish
-- C. J. Moreno and S. S. Wagstaff, Jr., Sums of Squares of Integers
#print axioms QuadFormsKB.Headlines.jacobi_fourSquares
#print axioms QuadFormsKB.Headlines.cauchy_polygonalNumbers
#print axioms QuadFormsKB.Headlines.sprague_distinctSquares
#print axioms QuadFormsKB.Headlines.hardy_sumsOfSquares
#print axioms QuadFormsKB.Headlines.singularSeries_twoK_squares
