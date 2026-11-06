/-
# Conway–Sloane 1988: the mass formula from the symbols, with (3) proved at the odd primes

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (2), (3), §7 and §9 (bibliography key `conwaysloane1988`).

`Main.lean` states the paper's working form of the mass formula conditional on (3) at every prime dividing $2d$
(the named inputs `PMassFormulaOdd p` and `PMassFormulaTwo`). Formula (3) at the odd primes is now a theorem
(`pMassFormulaOdd`, `OddProof.lean`), so this file restates the consequences with the odd-prime inputs discharged:

* `mass_eq_stdMass_mul_symbols_two` — for a positive definite symmetric integral Gram matrix $A$, $n \ge 3$, with a
  2-adic symbol $\tau$ and $p$-adic symbols $\sigma_p$ of $A$,
  $$m(f) = \mathrm{std}(f)\prod_{p \mid 2d}\frac{m_p(\sigma_p)}{\mathrm{std}_p(f)},$$
  conditional only on (3) at $p = 2$ (`PMassFormulaTwo`);
* `example_i_mass_two` — §9 (i): $m(\mathrm{diag}(7,1,1)) = \frac3{16}$, conditional only on (3) at $p = 2$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Main
import QuadFormsKB.Literature.ConwaySloane.Mass.OddProof

namespace QuadFormsKB.ConwaySloane.Mass

/-- **The mass formula in the paper's working form, from the genus symbols, with (3) proved at the odd primes**
(Conway–Sloane 1988, (2), (3), §7, §9): for $n \ge 3$ the mass is the standard mass times
$\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$, $m_p(\sigma_p)$ computed from the symbols by Tables 1–2, the
cross terms and (at $p = 2$) the type factor. Conditional only on (3) at $p = 2$ (`PMassFormulaTwo`). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266; §9, p. 272"]
theorem mass_eq_stdMass_mul_symbols_two {n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (h2 : PMassFormulaTwo) (τ : TwoSymbol) (N₂ : ℕ) (hτ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ)
    (hτN : τ.SupportedBelow N₂)
    (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧ ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors,
        ((if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p)) / (stdP p n A.det : ℝ)) :=
  mass_eq_stdMass_mul_symbols hn hA hQ h2 τ N₂ hτ hτN σ N fun p hp hp2 hdvd =>
    haveI : Fact p.Prime := ⟨hp⟩
    ⟨pMassFormulaOdd hp2, hodd p hp hp2 hdvd⟩

/-- **§9 (i), end to end, with (3) proved at $p = 7$** (Conway–Sloane 1988, pp. 269–272): the mass of the genus of
$\mathrm{diag}(7,1,1)$ is $\frac3{16}$, conditional only on (3) at $p = 2$ (`PMassFormulaTwo`). -/
@[kb "conwaysloane1988" "§9 (i), pp. 269–272"]
theorem example_i_mass_two (h2 : PMassFormulaTwo) : Siegel.mass (LocalDensity.ofMatrixZ ex1Gram) = 3 / 16 :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  example_i_mass h2 (pMassFormulaOdd (by norm_num))

end QuadFormsKB.ConwaySloane.Mass
