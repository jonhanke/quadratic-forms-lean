/-
# O'Meara Chapter X: citations for declarations elsewhere in the library

Declarations outside `Literature/OMeara/` that state (special cases of) items of O'Meara's Chapter X (1973 printing)
but carried no O'Meara tag. The tags are added here with `attribute [kb …]`, so the files where the
declarations live are unchanged. O'Meara's split rotations $J_V$ have components at all spots and lie in $O^+$; the
library's `Lattices.OAf` uses the finite spots and the full orthogonal groups (noted in each docstring).
-/
import QuadFormsKB.Lattices.SAApprox
import QuadFormsKB.Lattices.SAWeak
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Lattices.SARotations
import QuadFormsKB.Lattices.SATernary
import QuadFormsKB.Lattices.SATernaryAway
import QuadFormsKB.Lattices.SAVecAux
import QuadFormsKB.Lattices.SAVectorsAnisotropic
import QuadFormsKB.Lattices.SAVectorsAway
import QuadFormsKB.Lattices.SALocalRep
import QuadFormsKB.Lattices.SALemma1041
import QuadFormsKB.Lattices.SpinorGenusCount
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Lattices.StrongApproximationProof
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Lattices.NeighborGenus
import QuadFormsKB.Literature.AWS.Adelic
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.AdelicSO
import QuadFormsKB.Tamagawa.LatIndexCard
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.ThetaCuspidal
import QuadFormsKB.Siegel.KneserBridge
import QuadFormsKB.Lattices.KneserLocal
import QuadFormsKB.Lattices.Neighbors

namespace QuadFormsKB

/-! ### §101 -/

-- 101:4 (ii), (iii): lattice stabilizers are open; σL = K for σ close to λ when K = λL
attribute [kb "omeara1963" "§101A, 101:4 (ii) and (iii), p. 289 (generalization: σ ∈ GL_n(F_𝔭))"]
  Lattices.exists_mem_nhds_locAct_eq
attribute [kb "omeara1963" "§101A, 101:4 (ii), p. 289 (special case)"]
  Tamagawa.Measure.isOpen_stabLat Tamagawa.Measure.isOpen_locStab Tamagawa.Measure.isOpen_stdStab

-- 101:2 and §101A, p. 288: continuity of Q and of u ↦ τ_u on the anisotropic vectors
attribute [kb "omeara1963" "§101A, 101:2, p. 288 (u ↦ τ_u is continuous at an anisotropic u)"] Lattices.continuousAt_symm
attribute [kb "omeara1963" "§101A, p. 288 (Q is continuous on V_𝔭)"] Lattices.continuous_evalIn

-- §101B, p. 289: localization of isometries; (τ_u)_𝔭 = τ_{u_𝔭}; 101:5 (the notation σ_𝔭)
attribute [kb "omeara1963" "§101B, p. 289 (localization σ ↦ σ_𝔭); 101:5, p. 290 (notation)"] Lattices.orthMap
attribute [kb "omeara1963" "§101B, p. 289 ((τ_u)_𝔭 = τ_{u_𝔭})"]
  Lattices.orthMap_symm Lattices.orthMap_symm_locVec Lattices.orthMap_symmProd

-- 101:6: σ_𝔭 L_𝔭 = (σL)_𝔭
attribute [kb "omeara1963" "§101B, 101:6, p. 290 ((σL)_𝔭 = σ_𝔭 L_𝔭)"] Lattices.diagF_smul

-- 101:7: weak approximation for rotations (finite spots, products of symmetries)
attribute [kb "omeara1963" "§101B, 101:7, p. 290 (special case: finite spots)"] Lattices.exists_symmProd_approx

-- §101D: split rotations J_V, J'_V, P_V, J_L, the lattice ΣL
attribute [kb "omeara1963" "§101D, p. 295 (J_V; finite spots, full orthogonal groups)"] Lattices.OAf
attribute [kb "omeara1963" "§101D, p. 296 (J'_V is normal and contains the commutators)"]
  Lattices.commutator_mem_spinorKernelAf Lattices.normal_of_spinorKernelAf_le
attribute [kb "omeara1963" "§101D, p. 296 (σ ↦ (σ), principal split rotations P_V)"]
  Lattices.diagF Lattices.ratPoints
attribute [kb "omeara1963" "§101D, pp. 296–297 (J_L = {Σ ∈ J_V : ΣL = L}; full orthogonal group)"]
  Lattices.locStab Lattices.stabilizer_eq_locStab
attribute [kb "omeara1963" "§101D, p. 297 (the lattice ΣL, (ΣΛ)L = Σ(ΛL))"] Lattices.latSMul Lattices.latAction

/-! ### §102 -/

attribute [kb "omeara1963" "§102A, p. 298 (K ∈ gen L iff K = ΣL, Σ ∈ J_V)"]
  Lattices.orbit_eq_genus AWS.orbit_eq_genus
attribute [kb "omeara1963" "§102A, p. 297 (the lattices are partitioned into genera)"]
  Lattices.SameGenus.refl Lattices.SameGenus.symm Lattices.SameGenus.trans
attribute [kb "omeara1963" "§102A, p. 298 (partition into spinor genera)"]
  Lattices.SameSpinorGenus.refl Lattices.SameSpinorGenus.symm Lattices.SameSpinorGenus.trans
attribute [kb "omeara1963" "§102A, p. 298 (cls L ⊆ spn L ⊆ gen L)"]
  Lattices.class_subset_latSpinorGenus Lattices.latSpinorGenus_subset_genus
attribute [kb "omeara1963" "§102A, p. 298 (spn L: K = σΣL, σ ∈ O(V), Σ ∈ J'_V)"]
  Lattices.mem_latSpinorGenus Lattices.sameSpinorGenus_iff
attribute [kb "omeara1963" "§102A, 102:4, pp. 299–300 (special case)"] Lattices.exists_isometric_agree
attribute [kb "omeara1963" "§102B, proof of 102:7, step 1, pp. 300–301"]
  Lattices.commutator_mem_spinorKernelAf Lattices.normal_of_spinorKernelAf_le Lattices.doset_rel_iff_of_normal
attribute [kb "omeara1963" "§102B, 102:8 and 102:8a, pp. 302–304 (the spinor genera form an elementary abelian 2-group)"]
  Lattices.spinorGeneraQuot_comm
attribute [kb "omeara1963" "§102B, 102:8a, p. 304"] Lattices.spinorGeneraQuot_mul_self
attribute [kb "omeara1963" "§102B, 102:10 (ii), p. 304 (special case: non-dyadic unimodular)"]
  Lattices.localSpinorUnits_of_unimodular

attribute [kb "omeara1963" "§102A, p. 299 (all lattices in a genus have the same volume; special case over ℤ)"]
  Siegel.SameGenus.det_hessian_eq

/-! ### §103 -/

attribute [kb "omeara1963" "§103, 103:1, p. 305 (background: (L : φL) = N(det φ))"]
  Tamagawa.SiegelSpace.latIndex_eq_inv_covol
attribute [kb "omeara1963" "§103, 103:3, p. 307 (bounded form)"] Lattices.ClassFin.exists_value_bound
attribute [kb "omeara1963" "§103, proof of 103:4, step 2, pp. 309–310"] Lattices.ClassFin.gram_step

/-! ### §104 -/

attribute [kb "omeara1963" "§104, proof of 104:3, step 2, p. 312"] Lattices.exists_quadric_approx
attribute [kb "omeara1963" "§104, proof of 104:3, step 3, p. 313"]
  Lattices.exists_rep_perp_lattice Lattices.LocRep.exists_perp_std Lattices.LocRep.exists_eval_eq_dvr
attribute [kb "omeara1963" "§104, proof of 104:3, step 4, pp. 314–315"]
  Lattices.exists_beta_local Lattices.representsIn_of_isotropic_perp Lattices.vecApprox_core
  Lattices.vecApprox_core_at
attribute [kb "omeara1963" "§104, proof of 104:4, step 1a, p. 315"] Lattices.pair_approx Lattices.eqPair_approx
attribute [kb "omeara1963" "§104, proof of 104:4, step 1b, p. 316"] Lattices.list_approx
attribute [kb "omeara1963" "§104, proof of 104:4, step 1c, pp. 316–317"]
  Lattices.exists_correction Lattices.rotApprox_of_vecApprox_of_correction
  Lattices.rotApprox_of_vecApprox_of_four_le
attribute [kb "omeara1963" "§104, proof of 104:4, step 2, pp. 317–319"]
  Lattices.rotApprox_ternary Lattices.rotApprox_ternary_isotropic Lattices.exists_conj_of_mem_spinorKernel
  Lattices.rotApproxAt_ternary_of
attribute [kb "omeara1963" "§104, 104:8, p. 320 (special case)"]
  Lattices.isIsometric_of_sameGenus Lattices.isIsometric_of_sameGenus'

/-! ### §106 -/

attribute [kb "omeara1963" "§106B, pp. 325–326 (adjacent lattices; here π-neighbours for any prime π)"]
  Lattices.Nbr.IsNbrL
attribute [kb "omeara1963" "§106B, 106:4, pp. 326–327 (analogue: neighbours at an odd prime π ∤ det)"]
  Lattices.kneser_reach_uncond Lattices.kneser_reach_genus_uncond Siegel.Kneser.Bridge.exists_nbrReach_intEquiv
attribute [kb "omeara1963" "§106C, 106:7, pp. 328–329 (analogue: the explicit neighbour at an odd prime π ∤ det)"]
  Lattices.Nbr.nbLat Lattices.Nbr.exists_eq_nbLat
attribute [kb "omeara1963" "§106D, 106:10, p. 330 (special case: n ≤ 5)"] Siegel.Hermite.unimodular_posDef_equiv_one
attribute [kb "omeara1963" "§106E, p. 331 (background: the lattice E_8)"] Siegel.e8

end QuadFormsKB
