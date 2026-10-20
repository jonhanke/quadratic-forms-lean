import QuadFormsKB

/-!
# Axiom check for the headline theorems

`lake env lean scripts/check_axioms.lean` prints the axioms each headline theorem depends on.
Every line should list only `propext`, `Classical.choice` and `Quot.sound`; the CI workflow
fails if any other axiom (in particular `sorryAx`) appears.
-/

-- Siegel's theorem over totally real number fields
#print axioms QuadFormsKB.Tamagawa.SiegelSpace.siegelFormula_quadraticSpace_classical
#print axioms QuadFormsKB.Tamagawa.SiegelSpace.siegelFormula3_quadraticSpace_classical
#print axioms QuadFormsKB.Tamagawa.SiegelSpace.siegelFormula3_quadraticSpace_classical'
#print axioms QuadFormsKB.Tamagawa.SiegelSpace.siegelFormula2_quadraticSpace_classical
#print axioms QuadFormsKB.Tamagawa.SiegelSpace.siegelFormula2_quadraticSpace_classical'
#print axioms QuadFormsKB.Tamagawa.SiegelSpace.siegelFormula1_quadraticSpace_classical
-- Tamagawa number and mass formula over totally real number fields
#print axioms QuadFormsKB.Tamagawa.Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal
#print axioms QuadFormsKB.Tamagawa.Measure.Weil.massFormula_all_ranks_totallyReal
-- Hilbert reciprocity and Hasse–Minkowski over number fields
#print axioms QuadFormsKB.hilbert_reciprocity_nf
#print axioms QuadFormsKB.hasseMinkowski_nf
#print axioms QuadFormsKB.represents_iff_everywhere_nf
#print axioms QuadFormsKB.Tamagawa.FormClassNF.isometricIn_of_everywhere_nf
-- Hasse–Minkowski over ℚ
#print axioms QuadFormsKB.hasseMinkowski
