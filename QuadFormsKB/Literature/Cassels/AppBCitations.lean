/-
# Cassels, Appendices A and B: citations for declarations elsewhere in the library

Declarations outside `Literature/Cassels/` that state (variants of) items of Cassels' Appendix A (*Definite forms*,
pp. 362–367) and Appendix B (*Analytic methods*, pp. 368–389) but carried no Cassels tag yet. The tags are added here
with `attribute [kb …]`, so the files where the declarations live are unchanged.

Differences of setting, noted in the locators: Cassels' $\theta(z) = \sum z^{m^2}$ and $\Theta(f, t)$ are for one form
or for integer-valued forms with his matrix $F$; the library's theta series $\Theta_Q(z) = \sum_{\vec x} e(zQ(\vec x))$ is
in the Hessian normalization. The library's genus averages are over $\mathrm{GL}_n(\mathbb Z)$-classes (Cassels: proper
classes; the weights differ by the factor $2$ of his p. 375). The adelic groups are over the finite adeles (Cassels
includes the place $\infty$) and are built from the full orthogonal groups or $SO$.
-/
import QuadFormsKB.Binary.GenusCount
import QuadFormsKB.Binary.ClassBijection
import QuadFormsKB.Binary.KroneckerChar
import QuadFormsKB.Binary.GenusAverage
import QuadFormsKB.Binary.SiegelBinary
import QuadFormsKB.Siegel.Formula
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.FourSquaresJacobi
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.ThetaCuspidal
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Literature.AWS.Adelic
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Tamagawa.Measure.AdelicSO

namespace QuadFormsKB

/-! ### Appendix A, §3: the lattice $\Gamma_8$ -/

attribute [kb "cassels1978" "App. A, §3, p. 365 (the lattice Γ₈: 8-dimensional, integer-valued, determinant 1)"]
  Siegel.e8
attribute [kb "cassels1978" "App. A, §3, p. 365 (Γ₈ has determinant 1)"] Siegel.e8_det
attribute [kb "cassels1978" "App. A, §3, p. 365 (Γ₈ is positive definite)"] Siegel.e8_posDef

/-! ### Appendix B, §1: theta functions -/

attribute [kb "cassels1978" "App. B, §1, (1.1 bis), p. 369 (the inversion law θ(−1/s) = √(s/i) θ(s), generalized to any positive definite form)"]
  Siegel.theta_S'
attribute [kb "cassels1978" "App. B, §1, (1.1 bis), p. 369 (analogue for an even unimodular form: Θ(−1/z) = z^k Θ(z))"]
  Siegel.theta_S_unimodular
attribute [kb "cassels1978" "App. B, §1, (1.3), p. 369 (Jacobi: the number of representations as a sum of four squares)"]
  Siegel.repNum_sumSq_four

/-! ### Appendix B, §2: binary forms -/

attribute [kb "cassels1978" "App. B, §2, p. 370 (the primitive positive definite forms of discriminant D < 0)"]
  Binary.PosForms
attribute [kb "cassels1978" "App. B, §2, p. 370 (h(D) for D < 0: the number of proper classes = the class number of ℚ(√D))"]
  Binary.card_slClasses
attribute [kb "cassels1978" "App. B, §2, (2.5), p. 371 (the Kronecker symbol (D/·) as a Dirichlet character)"]
  Binary.kroneckerChar
attribute [kb "cassels1978" "App. B, §2, (2.5), p. 371 (the Kronecker symbol at odd primes)"] Binary.kronZ_odd_prime
attribute [kb "cassels1978" "App. B, §2, Lemma 2.2, p. 372 (variant: m is represented by the genus iff an ideal of norm m lies in its class)"]
  Binary.genusOf_eq_iff_represents
attribute [kb "cassels1978" "App. B, §2, proof of Lemma 2.2, p. 372 (variant: the weighted number of representations counts ideals of norm m)"]
  Binary.genusRepSum_eq_half_sum
attribute [kb "cassels1978" "App. B, §2, Lemma 2.2 and Cor., pp. 372–373 (variant: the genus average for m prime to D)"]
  Binary.genusRepAvg_binary_coprime

/-! ### Appendix B, §3: Siegel's formulae -/

attribute [kb "cassels1978" "App. B, §3, (3.12)–(3.13), pp. 377–378 (l = 1, the Euler product given as a value; a named input)"]
  Siegel.SiegelFormula3
attribute [kb "cassels1978" "App. B, §3, (3.13), p. 378 (n = 2, l = 1, m prime to D: proved for binary forms of fundamental discriminant D < 0)"]
  Binary.siegelFormula_binary_coprime
attribute [kb "cassels1978" "App. B, §3, (3.13), p. 378 (l = 1, f = x₀² + ⋯ + x₃², proved)"] Siegel.siegelFormula_Q4'
attribute [kb "cassels1978" "App. B, §3, p. 378 (a one-class genus: the average is the number of representations; four squares)"]
  Siegel.genusRepAvg_Q4'

/-! ### Appendix B, §4: adeles on the orthogonal group -/

attribute [kb "cassels1978" "App. B, §4, p. 379 (the adelic orthogonal group: finite adeles, full O, over a number field)"]
  Lattices.OAf
attribute [kb "cassels1978" "App. B, §4, p. 379 (the adelic orthogonal group: finite adeles, full O, over ℚ)"] AWS.OAf
attribute [kb "cassels1978" "App. B, §4, p. 379 (O⁺ over the finite adeles: SO)"] Tamagawa.soAf
attribute [kb "cassels1978" "App. B, §4, p. 379 (the topological group O⁺ over the finite adeles: SO)"]
  Tamagawa.Measure.SOAf
attribute [kb "cassels1978" "App. B, §4, (4.1)–(4.3), pp. 379–380, and (4.14)–(4.15), p. 381 (product of the local measures of the stabilizer)"]
  Tamagawa.tamagawaK

/-! ### Appendix B, §5: modular forms -/

attribute [kb "cassels1978" "App. B, §5, (5.20), p. 386 (Θ(f, t) ∈ M(k, N, ε): the case N = 1, even unimodular f)"]
  Siegel.thetaMF
attribute [kb "cassels1978" "App. B, §5, (5.1), p. 382, and (5.22), p. 386 (the coefficients of Θ are the numbers a_f(m))"]
  Siegel.qExpansion_thetaMF_coeff
attribute [kb "cassels1978" "App. B, §5, (5.18), p. 385 (the Stufe N: N F⁻¹ even integral; here any level, not only the least)"]
  Siegel.IsThetaLevel
attribute [kb "cassels1978" "App. B, §5, (5.23), p. 386 (Θ_f − Θ_{f'} is a cusp form, f' in the genus of f; for Γ₁(N))"]
  Siegel.thetaCuspDiff
attribute [kb "cassels1978" "App. B, §5, (5.4)–(5.7), p. 383 (background: binary forms through composition; the genus average)"]
  Binary.genusRepAvg_binary

end QuadFormsKB
