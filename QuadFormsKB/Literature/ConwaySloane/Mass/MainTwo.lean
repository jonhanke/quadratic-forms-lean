/-
# Conway–Sloane 1988: the mass formula from the symbols, with (3) proved except next to type I constituents at 2

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (2), (3), §6, §7 and §9 (bibliography key `conwaysloane1988`).

Formula (3) is proved at every odd prime (`pMassFormulaOdd`, `OddProof.lean`) and at $p = 2$ for every form whose
2-adic Jordan constituents all have type II (`pMassDensity_eq_pMassTwo_typeII`). At $p = 2$ in general it follows from the
named input `PMassStepTwoTypeI` (one splitting step next to a type I constituent, `TwoAdicMain.lean`):

* `pMassFormulaTwo_of_stepTypeI` — `PMassStepTwoTypeI` implies the former input `PMassFormulaTwo`;
* `mass_eq_stdMass_mul_symbols_stepTypeI` — for a positive definite symmetric integral Gram matrix $A$, $n \ge 3$,
  $m(f) = \mathrm{std}(f)\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$, conditional only on `PMassStepTwoTypeI`;
* `mass_eq_stdMass_mul_symbols_typeII` — the same, **unconditional**, when the 2-adic symbol of $A$ has only type II
  constituents;
* `example_i_mass_stepTypeI` — §9 (i): $m(\mathrm{diag}(7,1,1)) = \frac3{16}$, conditional only on `PMassStepTwoTypeI`.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicMain
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicBase
import QuadFormsKB.Literature.ConwaySloane.Mass.MainOdd

namespace QuadFormsKB.ConwaySloane.Mass

open Two

/-- The even unimodular value of $m_2$ (`pMassDensity_intMat_typeII_unimodular`), in the form used by the assembly. -/
theorem typeIIBase : TypeIIBase := fun D hv h0 hII => pMassDensity_intMat_typeII_unimodular D hv h0 hII

/-- **Formula (3) at $p = 2$ from the one-step input next to type I constituents** (Conway–Sloane 1988, (3), p. 263,
Tables 1–2, §6). -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2); Tables 1–2, p. 264; §6, p. 266"]
theorem pMassFormulaTwo_of_stepTypeI (I : PMassStepTwoTypeI) : PMassFormulaTwo :=
  pMassFormulaTwo_of_step I typeIIBase

/-- **Formula (3) at $p = 2$, unconditional, when every 2-adic Jordan constituent has type II** (Conway–Sloane 1988,
(3), p. 263): $m_2(A) = $ `pMassTwo σ N`. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2, all constituents of type II)"]
theorem pMassDensity_eq_pMassTwo_typeII {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det ≠ 0) (σ : TwoSymbol)
    (N : ℕ) (hσ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) σ) (hN : σ.SupportedBelow N)
    (hII : ∀ k, (σ k).type = .II) : pMassDensity 2 A = pMassTwo σ N :=
  pMassDensity_eq_pMassTwo_of_typeII typeIIBase A hdet σ N hσ hN hII

/-- **The mass formula in the paper's working form, from the genus symbols** (Conway–Sloane 1988, (2), (3), §7, §9),
with (3) proved at the odd primes and reduced at $p = 2$ to one splitting step next to a type I constituent: for $n \ge 3$
the mass is the standard mass times $\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$. Conditional only on
`PMassStepTwoTypeI`. -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266; §9, p. 272"]
theorem mass_eq_stdMass_mul_symbols_stepTypeI (I : PMassStepTwoTypeI) {n : ℕ} (hn : 3 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (τ : TwoSymbol) (N₂ : ℕ) (hτ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ) (hτN : τ.SupportedBelow N₂)
    (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧ ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors,
        ((if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p)) / (stdP p n A.det : ℝ)) :=
  mass_eq_stdMass_mul_symbols_two hn hA hQ (pMassFormulaTwo_of_stepTypeI I) τ N₂ hτ hτN σ N hodd

/-- **The mass formula from the genus symbols, unconditional when the 2-adic Jordan constituents all have type II**
(Conway–Sloane 1988, (2), (3), §7, §9): for a positive definite symmetric integral Gram matrix $A$ of dimension
$n \ge 3$ whose 2-adic symbol $\tau$ has only type II constituents (for instance every even form of odd determinant),
$m(f) = \mathrm{std}(f)\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$. -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266; §9, p. 272 (2-adic constituents of type II)"]
theorem mass_eq_stdMass_mul_symbols_typeII {n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (τ : TwoSymbol) (N₂ : ℕ) (hτ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ) (hτN : τ.SupportedBelow N₂)
    (hII : ∀ k, (τ k).type = .II)
    (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧ ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors,
        ((if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p)) / (stdP p n A.det : ℝ)) := by
  have hd : A.det ≠ 0 := (det_pos_of_posDef hA hQ).ne'
  rw [mass_eq_stdMass_mul hn hA hQ]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  congr 1
  split_ifs with h
  · subst h
    exact pMassDensity_eq_pMassTwo_typeII A hd τ N₂ hτ hτN hII
  · have : Fact p.Prime := ⟨hpp⟩
    have hdvd : (p : ℤ) ∣ A.det := by
      have h1 : p ∣ (2 * A.det).natAbs := Nat.dvd_of_mem_primeFactors hp
      have h2' : (p : ℤ) ∣ 2 * A.det := Int.natCast_dvd.mpr h1
      rcases Int.Prime.dvd_mul' hpp h2' with h3 | h3
      · exfalso
        have : p ∣ 2 := by exact_mod_cast h3
        exact h ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this)
      · exact h3
    obtain ⟨hσ, hN⟩ := hodd p hpp h hdvd
    exact (pMassFormulaOdd h).pMass_eq A hA hd (σ p) (N p) hσ hN

/-- **§9 (i), end to end** (Conway–Sloane 1988, pp. 269–272): the mass of the genus of $\mathrm{diag}(7,1,1)$ is
$\frac3{16}$, conditional only on `PMassStepTwoTypeI` ($\mathrm{diag}(7,1,1)$ is odd, so its 2-adic constituent $f_1$ has
type I). -/
@[kb "conwaysloane1988" "§9 (i), pp. 269–272"]
theorem example_i_mass_stepTypeI (I : PMassStepTwoTypeI) : Siegel.mass (LocalDensity.ofMatrixZ ex1Gram) = 3 / 16 :=
  example_i_mass_two (pMassFormulaTwo_of_stepTypeI I)

end QuadFormsKB.ConwaySloane.Mass
