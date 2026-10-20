import Solution

/-!
# Axiom check for the headline theorems

`lake env lean scripts/check_axioms.lean` prints the axioms each headline theorem depends on.
Every line should list only `propext`, `Classical.choice` and `Quot.sound`; the CI workflow
fails if any other axiom (in particular `sorryAx`) appears.
-/

-- The statements are in Challenge.lean; Solution.lean proves each by citing the library theorems named in
-- its proof. (`lake comparator` checks the same, against Challenge.lean; see comparator.json.)
-- Siegel's theorem over totally real number fields
#print axioms QuadFormsKB.Headlines.siegel_totallyReal
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank3
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank3'
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank2
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank2'
#print axioms QuadFormsKB.Headlines.siegel_totallyReal_rank1
-- Tamagawa number and mass formula over totally real number fields
#print axioms QuadFormsKB.Headlines.tamagawa_two_totallyReal
#print axioms QuadFormsKB.Headlines.massFormula_totallyReal
-- Hilbert reciprocity and Hasse–Minkowski over number fields
#print axioms QuadFormsKB.Headlines.hilbertReciprocity_numberField
#print axioms QuadFormsKB.Headlines.hasseMinkowski_numberField
#print axioms QuadFormsKB.Headlines.represents_iff_everywhere_numberField
#print axioms QuadFormsKB.Headlines.isometric_iff_everywhere_numberField
-- Hasse–Minkowski over ℚ
#print axioms QuadFormsKB.Headlines.hasseMinkowski_rat
