/-
# Cassels, Appendices A and B: further citations of library declarations

Declarations elsewhere in the library that formalize (variants of) items of Cassels' Appendix A (*Definite forms*,
pp. 362–367) and Appendix B (*Analytic methods*, pp. 368–390) that had no citation tag yet after `AppBCitations.lean` and `CitationsBatch1.lean`. The tags are added with
`attribute [kb …]`, so the files where the declarations live are unchanged. Differences of setting are in the locators:
the library's local densities are over the ring of integers of a number field and count $X$ with $Q \circ X = T$ as
quadratic forms (Cassels: $X'FX \equiv G$ for his integral matrices, the same away from $2$); the library's adelic groups
are over the finite adeles with the full orthogonal group (Cassels: $O^{+}$, including the place $\infty$).
-/
import QuadFormsKB.Literature.Cassels.AppA.Watson
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.LocalDensity.NFFormDensity
import QuadFormsKB.Tamagawa.FrameSiegelAll
import QuadFormsKB.Tamagawa.InputsFollowup
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal
import QuadFormsKB.Siegel.EisensteinWt2.Forms
import QuadFormsKB.Literature.Cassels.AppB.Sec2Lemmas

namespace QuadFormsKB

/-! ### Appendix A, §3: conventions -/

attribute [kb "cassels1978" "App. A, §3, p. 364 (isomorphic lattices with forms: integrally equivalent forms)"]
  Siegel.IntEquiv
attribute [kb "cassels1978" "App. A, §3, p. 364 (Λ = Γ + Λ′: the orthogonal sum)"] QuadForm.orthSum
attribute [kb "cassels1978" "App. A, §3, p. 364 (rΓ: the orthogonal sum of r copies; here Γ = Γ₈)"] DefiniteForms.repE8

/-! ### Appendix B, §2: binary forms -/

attribute [kb "cassels1978" "App. B, §2, p. 371 (a*(m): the number of orbits of representations of m under proper automorphs)"]
  Cassels.repOrbitCount
attribute [kb "cassels1978" "App. B, §2, (2.9), p. 371 (A*(M) for one form)"] Cassels.orbitCountSum
attribute [kb "cassels1978" "App. B, §2, (2.7), p. 371 (w = 6, 4, 2)"] Cassels.properAutomorphCount
attribute [kb "cassels1978" "App. B, §2, (2.1)–(2.3), p. 370 (D ≡ 0 or 1 mod 4)"] BinQF.disc_mod_four

/-! ### Appendix B, §3: Siegel's formulae -/

attribute [kb "cassels1978" "App. B, §3, p. 375 (Cassels' weight W over proper classes is twice the mass)"]
  Siegel.pweight_eq_two_mul_mass
attribute [kb "cassels1978" "App. B, §3, (3.3), p. 376, and (3.14)–(3.15), p. 378 (variant: the local density α_p(𝓕, 𝒢) over a number field; T = Q gives Cassels' 2β_p⁻¹)"]
  LocalDensity.NF.localDensityForm
attribute [kb "cassels1978" "App. B, §3, (3.14)–(3.15), p. 378 (the number of solutions of X′FX ≡ G mod pᵗ; as quadratic forms)"]
  LocalDensity.NF.repCountForm
attribute [kb "cassels1978" "App. B, §3, (3.13), p. 378 (Siegel's factor ε applied to the local densities)"]
  LocalDensity.NF.siegelDensity
attribute [kb "cassels1978" "App. B, §3, (3.16)–(3.17), p. 378 (the archimedean factor α_∞(𝓕, 𝒢), coefficient coordinates)"]
  Tamagawa.Frames.archDensityForm
attribute [kb "cassels1978" "App. B, §3, (3.13), p. 378 (ε = 1/2 for l = n − 1)"] Tamagawa.Frames.epsCodimOne
attribute [kb "cassels1978" "App. B, §3, (3.10)–(3.13), pp. 377–378 (Siegel's formula for representations of forms by forms, every l ≤ n; over a totally real field, proved)"]
  Tamagawa.Frames.siegelForms_all_ranks

/-! ### Appendix B, §4: Tamagawa numbers -/

attribute [kb "cassels1978" "App. B, §4, (4.5)–(4.6), p. 380 (the lattice αΛ with (αΛ)_p = α_pΛ_p)"] Lattices.latSMul
attribute [kb "cassels1978" "App. B, §4, p. 380 (αΛ and Λ lie in one genus, and every lattice of the genus is some αΛ)"]
  Lattices.orbit_eq_genus
attribute [kb "cassels1978" "App. B, §4, p. 380 (for α ∈ O(V), αΛ is equivalent to Λ)"] Lattices.diagF_smul
attribute [kb "cassels1978" "App. B, §4, p. 380 (the Tamagawa number does not depend on the choices; variant: the lattice and a rescaling)"]
  Tamagawa.LatChange.tauSO_smul_compMat
attribute [kb "cassels1978" "App. B, §4, p. 382 ((4.17) for indefinite forms; the case of a genus of one class)"]
  Tamagawa.Indefinite.siegelIndefinite_oneClass_uncond
attribute [kb "cassels1978" "App. B, §4, p. 382 ((3.13) from the Tamagawa measure of the stabilizer; l = 1)"]
  Tamagawa.siegelFormulaAt_of_tamagawa

/-! ### Appendix B, §5: modular forms -/

attribute [kb "cassels1978" "App. B, §5, (5.13 bis)–(5.15), p. 385 (M(k, N, ε) for Γ₀(N) with a character; character evaluated at d)"]
  Siegel.EisensteinWt2.IsModularFormWithChar

end QuadFormsKB
