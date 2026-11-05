/-
# The Conway–Sloane mass formula, unconditional

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (2), (3), p. 263, Tables 1–2, p. 264, §6–7, p. 266, §9, pp. 269–272 (bibliography key `conwaysloane1988`).

The two inputs about a single odd unimodular constituent at $p = 2$ are proved (`pMassUnimodularTwoTypeI_holds`,
`rhoValueTwoTypeI_holds`), so the one-step identity next to a type I constituent (`PMassStepTwoTypeI`) holds, formula (3)
holds at $p = 2$ (`pMassFormulaTwo_holds`), and with formula (3) at the odd primes (`pMassFormulaOdd`) the mass formula
from the genus symbols holds for every positive definite integral form of dimension $n \ge 3$
(`mass_eq_stdMass_mul_symbols_unconditional`). The paper states (3) at $p = 2$ without proof.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRhoTypeI
import QuadFormsKB.Literature.ConwaySloane.Mass.MainTwo

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

/-- **The one-step identity of (3) at $p = 2$ next to a type I constituent** (formerly a named input). -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §6, p. 266 (one step at p = 2 next to type I)"]
theorem pMassStepTwoTypeI_holds : PMassStepTwoTypeI :=
  pMassStepTwoTypeI_of_inputs pMassUnimodularTwoTypeI_holds (rhoValueTwo_of_typeI rhoValueTwoTypeI_holds)

/-- **Formula (3) at $p = 2$** (Conway–Sloane 1988, (3), p. 263, Tables 1–2, p. 264, §6, p. 266; stated in the paper
without proof): for every symmetric integral $A$ with $\det A \ne 0$ and every 2-adic symbol $\sigma$ of $A$,
$m_2(A) = $ `pMassTwo σ N`. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2); Tables 1–2, p. 264; §6, p. 266"]
theorem pMassFormulaTwo_holds : PMassFormulaTwo := pMassFormulaTwo_of_stepTypeI pMassStepTwoTypeI_holds

end QuadFormsKB.ConwaySloane.Mass.Two

namespace QuadFormsKB.ConwaySloane.Mass

open Two

/-- **Formula (3) at $p = 2$**, as an equation: $m_2(A) = $ `pMassTwo σ N` for a symmetric integral $A$ with
$\det A \ne 0$, a 2-adic symbol $\sigma$ of $A$ and $N$ with $\sigma_k$ trivial for $k \ge N$. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2)"]
theorem pMassDensity_eq_pMassTwo {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (σ : TwoSymbol) (N : ℕ) (hσ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) σ) (hN : σ.SupportedBelow N) :
    pMassDensity 2 A = pMassTwo σ N :=
  pMassFormulaTwo_holds.pMass_eq A hA hdet σ N hσ hN

/-- **The Conway–Sloane mass formula, unconditional** (Conway–Sloane 1988, (2), (3), p. 263, §7, p. 266, §9, p. 272):
for a positive definite symmetric integral Gram matrix $A$ of dimension $n \ge 3$, with 2-adic symbol $\tau$ and
$p$-adic symbols $\sigma_p$ ($p \mid d$ odd), the mass of the genus is
$m(f) = \mathrm{std}(f)\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$, $m_p$ from Tables 1–2, the cross terms and
the type factor. -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266; §9, p. 272"]
theorem mass_eq_stdMass_mul_symbols_unconditional {n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (τ : TwoSymbol) (N₂ : ℕ) (hτ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ) (hτN : τ.SupportedBelow N₂)
    (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧ ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors,
        ((if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p)) / (stdP p n A.det : ℝ)) :=
  mass_eq_stdMass_mul_symbols_two hn hA hQ pMassFormulaTwo_holds τ N₂ hτ hτN σ N hodd

/-- **§9 (i), unconditional** (Conway–Sloane 1988, pp. 269–272): the mass of the genus of $\mathrm{diag}(7, 1, 1)$ is
$\frac3{16}$. -/
@[kb "conwaysloane1988" "§9 (i), pp. 269–272"]
theorem example_i_mass_unconditional : Siegel.mass (LocalDensity.ofMatrixZ ex1Gram) = 3 / 16 :=
  example_i_mass_two pMassFormulaTwo_holds

end QuadFormsKB.ConwaySloane.Mass
