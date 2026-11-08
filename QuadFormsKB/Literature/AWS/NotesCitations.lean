/-
# Hanke, Arizona Winter School 2009 notes: citations of results the library already proves

J. Hanke, *Quadratic Forms and Automorphic Forms*, arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed
page). Most of Chs. 1–3 quote standard results (Cassels, O'Meara, Lam, Shimura, Miyake, Jacobson). This file
attaches the notes' locators to the library declarations that prove them. "(variant: …)" records where the
library statement differs from the notes' (another generality, another normalization, or a special case).
-/
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Lattices.CartanDieudonne
import QuadFormsKB.Lattices.SpinorNorm
import QuadFormsKB.Lattices.SpinorGenus
import QuadFormsKB.Lattices.Eichler
import QuadFormsKB.Lattices.Kneser
import QuadFormsKB.Literature.Cassels.Ch2.Basic
import QuadFormsKB.Literature.Cassels.Ch4.Invariants
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.Cassels.Ch10.Clifford
import QuadFormsKB.Literature.Cassels.Ch10.Spin
import QuadFormsKB.Literature.Cassels.Ch10.SpinGroup
import QuadFormsKB.Literature.Cassels.AppB.ModularBasics
import QuadFormsKB.Literature.OMeara.Sec42Iso
import QuadFormsKB.Literature.OMeara.Sec52A
import QuadFormsKB.Literature.OMeara.Sec52B
import QuadFormsKB.Literature.OMeara.Sec54
import QuadFormsKB.Literature.OMeara.Sec54Dim
import QuadFormsKB.Literature.OMeara.Sec54Even
import QuadFormsKB.Literature.OMeara.Sec54Inv
import QuadFormsKB.Literature.OMeara.Sec57Iso
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Literature.OMeara.Sec82Dual
import QuadFormsKB.Literature.OMeara.Sec91
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.LocalDensity.JordanForm
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Analysis.LatticePoisson
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.Siegel.Theta
import QuadFormsKB.Siegel.ThetaGamma0
import QuadFormsKB.Siegel.ThetaModular
import QuadFormsKB.Siegel.Formula
import QuadFormsKB.Siegel.SiegelQuaternary
import QuadFormsKB.Siegel.FourSquaresJacobi
import QuadFormsKB.Siegel.HeckeBound
import QuadFormsKB.Siegel.Tartakowsky
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Siegel.LevelCharacter
import QuadFormsKB.Siegel.Neighbors
import QuadFormsKB.Siegel.KneserConnectedProof
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal

/-! ## Chapter 1 -/

attribute [kb "hanke2011aws" "§1.2, (1.1)–(1.2), pp. 11–12 (Hessian bilinear form and the polarization identity)"]
  QuadFormsKB.QuadForm.polar_eq_hessian
attribute [kb "hanke2011aws" "§1.2, p. 12 (Hessian matrix H = 2B)"] QuadFormsKB.QuadForm.hessian
attribute [kb "hanke2011aws" "§1.3, (1.3), p. 13 (equivalence over R)"] QuadFormsKB.Siegel.IsometricGL
attribute [kb "hanke2011aws" "§1.4, p. 13 (scaled quadratic form a·Q)"] QuadFormsKB.QuadForm.smul_coeff
attribute [kb "hanke2011aws" "§1.4, p. 14 (orthogonal direct sum Q₁ ⊕ Q₂)"] QuadFormsKB.QuadForm.orthSum
attribute [kb "hanke2011aws" "§1.4, p. 14 ((Q₁ ⊕ Q₂)(x) = Q₁(x₁) + Q₂(x₂))"] QuadFormsKB.QuadForm.evalIn_orthSum
attribute [kb "hanke2011aws" "§1.5, Thm. 1.5.1, p. 14 (orthogonal basis; as a diagonal form)"]
  QuadFormsKB.FieldGen.exists_isometric_diag
attribute [kb "hanke2011aws" "§1.5, Lemma 1.5.3, p. 15 (radical splitting)"]
  QuadFormsKB.Cassels.exists_regular_compl_radical
attribute [kb "hanke2011aws" "§1.5, Thm. 1.5.4, p. 15 (variant: O'Meara 42:13, hyperbolic partners y_i of a base x_i of U; U' = span y)"]
  QuadFormsKB.OMeara.exists_hyperbolic_partners
attribute [kb "hanke2011aws" "§1.5, Thm. 1.5.5, p. 16 (Witt's theorem; variant: V nondegenerate)"]
  QuadraticForm.exists_isometryEquiv_extend_of_associated
attribute [kb "hanke2011aws" "§1.6, Thm. 1.6.2, p. 16 (classification over ℝ by the number of negative entries)"]
  QuadFormsKB.LocalClassNF.isometric_real_vec_iff
attribute [kb "hanke2011aws" "§1.6, Thm. 1.6.3, p. 17 (classification over ℚ_p by (n, d, c))"]
  QuadFormsKB.isometric_padic_iff_invariants
attribute [kb "hanke2011aws" "§1.6, Thm. 1.6.3, p. 17 (restriction 1: c = 1 if n = 1)"]
  QuadFormsKB.Cassels.hasseVec_eq_one_of_dim_one
attribute [kb "hanke2011aws" "§1.6, Thm. 1.6.3, p. 17 (restriction 1: c = 1 if (n, d) = (2, −1))"]
  QuadFormsKB.Cassels.hasseVec_eq_one_of_dim_two
attribute [kb "hanke2011aws" "§1.6, Thm. 1.6.3, p. 17 (every other triple (n, d, c), n ≥ 1, occurs)"]
  QuadFormsKB.Cassels.exists_of_invariants
attribute [kb "hanke2011aws" "§1.7, Remark 1.7.1, p. 18 (Gram dual lattice, O'Meara §82F)"] QuadFormsKB.OMeara.dual
attribute [kb "hanke2011aws" "§1.7, p. 18 (level N of a ℤ-form: N H⁻¹ even)"] QuadFormsKB.Siegel.IsLevel
attribute [kb "hanke2011aws" "§1.7, p. 18 (the level N)"] QuadFormsKB.Siegel.level
attribute [kb "hanke2011aws" "§1.8, Lemma 1.8.1, p. 19 (variant: over a discrete valuation ring, for a modular sublattice)"]
  QuadFormsKB.OMeara.splits_of_isModular_of_scale_eq
attribute [kb "hanke2011aws" "§1.8, Thm. 1.8.2, p. 19 (Jordan decomposition; as a Jordan form with the same local counts)"]
  QuadFormsKB.LocalDensity.exists_jordanForm
attribute [kb "hanke2011aws" "§1.8, Thm. 1.8.2, p. 19 (p > 2: unimodular part diagonal with unit entries)"]
  QuadFormsKB.Siegel.Kneser.isometricGL_diag_normal
attribute [kb "hanke2011aws" "§1.9, Thm. 1.9.1, p. 20 (Hasse–Minkowski, equivalence)"]
  QuadFormsKB.isometric_iff_everywhere
attribute [kb "hanke2011aws" "§1.9, Remark 1.9.2, p. 20 (over a number field)"]
  QuadFormsKB.Tamagawa.FormClassNF.isometricIn_of_everywhere_nf
attribute [kb "hanke2011aws" "§1.9, p. 20 (the class Cls(Q))"] QuadFormsKB.Siegel.classOf
attribute [kb "hanke2011aws" "§1.9, p. 20 (the genus Gen(Q))"] QuadFormsKB.Siegel.SameGenus
attribute [kb "hanke2011aws" "§1.9, p. 20 (the classes in the genus; h_Q = |Gen(Q)|)"] QuadFormsKB.Siegel.genusClasses
attribute [kb "hanke2011aws" "§1.9, Thm. 1.9.3, p. 21 (h_Q < ∞; nondegenerate integral forms)"]
  QuadFormsKB.Siegel.genusClasses_finite
attribute [kb "hanke2011aws" "§1.9, Thm. 1.9.3, p. 21 (h_Q < ∞; positive definite)"] QuadFormsKB.Siegel.genusFinite
attribute [kb "hanke2011aws" "§1.9, Remark 1.9.4, p. 21 (number of proper classes in a class)"]
  QuadFormsKB.Siegel.ncard_properClassesIn
attribute [kb "hanke2011aws" "§1.10, Thm. 1.10.3(2), p. 23 (variant: positive definite, p odd, genus = one spinor genus)"]
  QuadFormsKB.Siegel.Kneser.kneserConnected_of_spinorGenus

/-! ## Chapter 2 -/

attribute [kb "hanke2011aws" "§2.1, p. 25 (r_Q(m) < ∞ for positive definite Q)"] QuadFormsKB.IntQF.PosDef.repSet_finite
attribute [kb "hanke2011aws" "§2.1, p. 25 (#Aut(Q) < ∞)"] QuadFormsKB.IntQF.PosDef.finite_aut
attribute [kb "hanke2011aws" "§2.1, p. 25 (theta series Θ_Q)"] QuadFormsKB.Siegel.theta
attribute [kb "hanke2011aws" "§2.1, Thm. 2.1.2, p. 26 (Θ_Q is holomorphic on ℋ)"]
  QuadFormsKB.Siegel.differentiableOn_theta
attribute [kb "hanke2011aws" "§2.1, Thm. 2.1.2, p. 26 (Θ_Q = Σ r_Q(m) e^{2πimz}, absolutely convergent)"]
  QuadFormsKB.Siegel.hasSum_theta
attribute [kb "hanke2011aws" "§2.2, Thm. 2.2.1, p. 27 (Poisson summation; for Schwartz functions)"]
  QuadFormsKB.Analysis.intPoisson
attribute [kb "hanke2011aws" "§2.2, (2.1), p. 27 (Θ_{x²}(z) = θ(2z), Jacobi's theta)"] QuadFormsKB.Siegel.theta_sumSq_one
attribute [kb "hanke2011aws" "§2.2, (2.1), p. 27 (Θ_{x²}(−1/4z) = √(−2iz) Θ_{x²}(z), as the inversion of θ)"]
  QuadFormsKB.Siegel.jacobiTheta_S_of_theta_S
attribute [kb "hanke2011aws" "§2.2, Thm. 2.2.3, p. 28 (variant: n even, with the theta multiplier)"]
  QuadFormsKB.Siegel.theta_gamma0
attribute [kb "hanke2011aws" "§2.3, Cor. 2.3.2, p. 29 (variant: n = 2k even, trivial character)"]
  QuadFormsKB.Siegel.thetaMFGamma0
attribute [kb "hanke2011aws" "§2.3, (2.4), p. 30 (Fourier expansion of the Eisenstein series G_k)"]
  QuadFormsKB.Cassels.eisenstein_fourier_series
attribute [kb "hanke2011aws" "§2.3, Facts 1, p. 30 (variant: level one)"] QuadFormsKB.Cassels.modularForm_finiteDimensional
attribute [kb "hanke2011aws" "§2.3, Facts 2, p. 30 (variant: level one, even k ≥ 4)"]
  QuadFormsKB.Cassels.modularForm_eq_eisenstein_add_cusp
attribute [kb "hanke2011aws" "§2.3, Facts 4, p. 31 (variant: cusp part of Θ_Q, n = 2k, exponent k/2)"]
  QuadFormsKB.Siegel.cuspBound_hecke
attribute [kb "hanke2011aws" "§2.4, Thm. 2.4.1, p. 31 (variant: n even ≥ 6, given the local density gaps at the bad primes)"]
  QuadFormsKB.Siegel.tartakowsky_even
attribute [kb "hanke2011aws" "§2.5, Thm. 2.5.1, p. 33 (Siegel's formula, named statement)"] QuadFormsKB.Siegel.SiegelFormula
attribute [kb "hanke2011aws" "§2.5, Thm. 2.5.1, p. 33 (proved for positive definite quaternary forms)"]
  QuadFormsKB.Siegel.GenusEis.siegelFormula_quaternary
attribute [kb "hanke2011aws" "§2.5, Thm. 2.5.1, p. 33 (Siegel's formula (2.5)–(2.6), every positive definite Q in n ≥ 4 variables)"]
  QuadFormsKB.Tamagawa.siegelFormula_int_all_ranks_uncond
attribute [kb "hanke2011aws" "§2.7, Thm. 2.7.1, p. 36 (Jacobi's four squares theorem)"] QuadFormsKB.Siegel.repNum_sumSq_four

/-! ## Chapter 3 -/

attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.1, p. 41"] QuadFormsKB.OMeara.isCentralSimple_tensorProduct
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.7, p. 43 (Wedderburn; as A ≅ M_n(F) ⊗ D)"]
  QuadFormsKB.OMeara.exists_algEquiv_matrix_tensor_division
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.7, p. 43 (uniqueness of D)"]
  QuadFormsKB.OMeara.unique_algEquiv_matrix_tensor_division
attribute [kb "hanke2011aws" "§3.1, p. 42 (N(αβ) = N(α)N(β) for quaternions)"] QuadFormsKB.Quat.nrd_mul
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.6 and proof, p. 43 (quaternions: α invertible iff N(α) ≠ 0)"]
  QuadFormsKB.Quat.isUnit_iff_nrd_ne_zero
attribute [kb "hanke2011aws" "§3.1, Lemma 3.1.8, p. 43"] QuadFormsKB.OMeara.QuatIso57.tfae_iso
attribute [kb "hanke2011aws" "§3.1, Cor. 3.1.9, p. 44"] QuadFormsKB.OMeara.QuatIso57.tfae_division
attribute [kb "hanke2011aws" "§3.1, Cor. 3.1.9 and (3.1), p. 44 ((a, b) = −1 iff division)"]
  QuadFormsKB.Quat.hilbertSymbol_eq_neg_one_iff_division
attribute [kb "hanke2011aws" "§3.1, p. 44 (split iff (a, b) = 1)"] QuadFormsKB.Quat.nonempty_algEquiv_matrix_iff
attribute [kb "hanke2011aws" "§3.1, (3.1), p. 44 (Hilbert symbol)"] QuadFormsKB.hilbertSymbol
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.12(1), p. 44"] QuadFormsKB.hilbertSymbol_comm
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.12(2), p. 44 (ℚ_p)"] QuadFormsKB.HilbertLocal.hilbertSymbol_padic_mul_left
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.12(2), p. 44 (ℝ)"] QuadFormsKB.HilbertLocal.hilbertSymbol_real_mul_left
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.12(4), p. 45 ((a, −a) = 1)"] QuadFormsKB.hilbertSymbol_self_neg
attribute [kb "hanke2011aws" "§3.1, Thm. 3.1.13, p. 45"] QuadFormsKB.hilbert_product_formula
attribute [kb "hanke2011aws" "§3.1, Cor. 3.1.14, p. 45 (over any number field)"] QuadFormsKB.Quat.ramified_finite_even
attribute [kb "hanke2011aws" "§3.2, Thm. 3.2.1, p. 46 (dim C(V) = 2ⁿ)"]
  QuadFormsKB.OMeara.CliffordDim.finrank_cliffordAlgebra
attribute [kb "hanke2011aws" "§3.2, Thm. 3.2.2, p. 47"] QuadFormsKB.OMeara.finrank_even
attribute [kb "hanke2011aws" "§3.2, p. 47 (canonical involution)"] QuadFormsKB.Cassels.reverse_properties
attribute [kb "hanke2011aws" "§3.2, p. 47 (α⁻¹ = α̃/N(α))"] QuadFormsKB.Cassels.inverse_of_mul_reverse
attribute [kb "hanke2011aws" "§3.2, Lemma 3.2.3, p. 47"] QuadFormsKB.OMeara.Inv54.isUnit_iff_anisotropic
attribute [kb "hanke2011aws" "§3.3, (3.7), p. 48 (reflection τ_v)"] QuadFormsKB.OMeara.symmetry
attribute [kb "hanke2011aws" "§3.3, Lemma 3.3.1(b), p. 48"] QuadFormsKB.Lattices.symm_sub_apply
attribute [kb "hanke2011aws" "§3.3, Thm. 3.3.2, p. 48"] QuadFormsKB.Lattices.exists_symmProd_eq
attribute [kb "hanke2011aws" "§3.3, Lemma 3.3.3, p. 49"] QuadFormsKB.OMeara.mem_range_algebraMap_of_mem_even_of_commute
attribute [kb "hanke2011aws" "§3.3, Thm. 3.3.4, p. 49 (well defined)"] QuadFormsKB.Lattices.isSquare_valProd_of_symmProd_eq_one
attribute [kb "hanke2011aws" "§3.3, Thm. 3.3.4 and (3.8), p. 49 (the spinor norm homomorphism)"]
  QuadFormsKB.Lattices.spinorNormHom
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.1, p. 50"] QuadFormsKB.Cassels.conjHom_vecUnit
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.3, p. 51 (onto SO(V))"] QuadFormsKB.Cassels.range_conjM0
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.3, p. 51 (kernel K^×)"] QuadFormsKB.Cassels.conjM0_eq_one_iff
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.4, p. 51"] QuadFormsKB.Cassels.spinorNormHom_conjM0
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.5, p. 52 (image κ(V))"] QuadFormsKB.Cassels.range_spinConj
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.5, p. 52 (kernel {±1})"] QuadFormsKB.Cassels.spinConj_eq_one_iff
attribute [kb "hanke2011aws" "§3.5, p. 53 (the spinor genus)"] QuadFormsKB.Lattices.SameSpinorGenus
attribute [kb "hanke2011aws" "§3.5, Thm. 3.5.1, p. 53 (Eichler; relative to strong approximation for Spin)"]
  QuadFormsKB.Lattices.eichler_spinorGenus_eq_class
attribute [kb "hanke2011aws" "§1.2, pp. 12–13 (R-valued quadratic form on a free R-module: coefficients in R)"]
  QuadFormsKB.QuadForm
attribute [kb "hanke2011aws" "§1.7, p. 18 (unimodular: the Hessian lattice is self-dual; O'Meara 82:14b)"]
  QuadFormsKB.IsUnimodularAt
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.2, p. 50 (φ : U₀ → SO(V))"] QuadFormsKB.Cassels.conjM0
attribute [kb "hanke2011aws" "§3.4, Lemma 3.4.2, p. 50 (φ(U₀) ⊆ SO(V))"] QuadFormsKB.Cassels.conjM0_mem_orthPlus
