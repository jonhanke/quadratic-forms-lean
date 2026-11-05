/-
# Conway–Sloane 1988: the mass formula from the symbols, and example (i) end to end

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (2), (3), §7 and §9 (bibliography key `conwaysloane1988`).

* `mass_eq_stdMass_mul_symbols` — **the paper's working form of the mass formula** (§9): for a positive definite
  symmetric integral Gram matrix $A$ of dimension $n \ge 3$ and determinant $d$, with a 2-adic symbol $\tau$ and $p$-adic
  symbols $\sigma_p$ ($p \mid d$ odd) of $A$,
  $$m(f) = \mathrm{std}(f)\prod_{p \mid 2d}\frac{m_p(\sigma_p)}{\mathrm{std}_p(f)},$$
  $m_p(\sigma_p)$ the right-hand side of (3). **Conditional** on the named inputs `PMassFormulaTwo` and
  `PMassFormulaOdd p` at the odd $p \mid d$ (formula (3), which the paper does not prove); everything else ((2), the
  standard values at $p \nmid 2d$, the Euler product of the standard mass) is proved (`mass_eq_stdMass_mul`).
* `example_i_mass` — §9 (i): $m(\mathrm{diag}(7,1,1)) = \frac3{16}$, conditional on (3) at $p = 2$ and $p = 7$, with
  the symbols certified (`isTwoSymbolOf_ex1`, `isOddSymbolOf_ex1`).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm
import QuadFormsKB.Literature.ConwaySloane.Mass.ExampleForms
import QuadFormsKB.Literature.ConwaySloane.Mass.Table7

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-- **The mass formula in the paper's working form, from the genus symbols** (Conway–Sloane 1988, (2), (3), §7, §9):
for $n \ge 3$, under (3) at the primes dividing $2d$ (named inputs), the mass is the standard mass times
$\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$ with $m_p(\sigma_p)$ computed from the symbols by Tables 1–2,
the cross terms and the type factor. -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266; §9, p. 272"]
theorem mass_eq_stdMass_mul_symbols {n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (h2 : PMassFormulaTwo) (τ : TwoSymbol) (N₂ : ℕ) (hτ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ)
    (hτN : τ.SupportedBelow N₂)
    (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      PMassFormulaOdd p ∧ IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧
        ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
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
    exact h2.pMass_eq A hA hd τ N₂ hτ hτN
  · haveI : Fact p.Prime := ⟨hpp⟩
    have hdvd : (p : ℤ) ∣ A.det := by
      have h1 : p ∣ (2 * A.det).natAbs := Nat.dvd_of_mem_primeFactors hp
      have h2' : (p : ℤ) ∣ 2 * A.det := Int.natCast_dvd.mpr h1
      rcases Int.Prime.dvd_mul' hpp h2' with h3 | h3
      · exfalso
        have : p ∣ 2 := by exact_mod_cast h3
        exact h ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this)
      · exact h3
    obtain ⟨hin, hσ, hN⟩ := hodd p hpp h hdvd
    exact hin.pMass_eq A hA hd (σ p) (N p) hσ hN

theorem ex1Gram_symm : ex1Gram.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem ex1Gram_det : ex1Gram.det = 7 := by
  simp [ex1Gram, Matrix.det_diagonal, Fin.prod_univ_three]

theorem ex1Gram_posDef : IntQF.PosDef (LocalDensity.ofMatrixZ ex1Gram) := by
  intro x hx
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2])
  simp [QuadForm.eval, QuadForm.evalIn, LocalDensity.ofMatrixZ, ex1Gram, Fin.sum_univ_three, Matrix.diagonal]
  have h0 := mul_self_nonneg (x 0)
  have h1 := mul_self_nonneg (x 1)
  have h2 := mul_self_nonneg (x 2)
  rcases hx' with h | h | h <;> have := mul_self_pos.mpr h <;> nlinarith

/-- **§9 (i), end to end** (Conway–Sloane 1988, pp. 269–272): the mass of the genus of $\mathrm{diag}(7,1,1)$ is
$\frac3{16} = \frac38 \cdot 3 \cdot \frac16$, conditional on (3) at $p = 2$ and $p = 7$ (named inputs). The paper checks
this against the two classes $7 \oplus I_2$ and $7_2 \oplus I_1$ ($\frac1{16} + \frac18$); that enumeration is not
formalized. -/
@[kb "conwaysloane1988" "§9 (i), pp. 269–272"]
theorem example_i_mass (h2 : PMassFormulaTwo)
    (h7 : haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩; PMassFormulaOdd 7) :
    Siegel.mass (LocalDensity.ofMatrixZ ex1Gram) = 3 / 16 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsupp2 : ex1Two.SupportedBelow 1 := fun k hk => by simp [ex1Two, show k ≠ 0 by omega]
  have hsupp7 : ∀ k, 2 ≤ k → ex1Seven k = OddFactor.trivial := fun k hk => by
    simp [ex1Seven, show k ≠ 0 by omega, show k ≠ 1 by omega]
  rw [mass_eq_stdMass_mul_symbols le_rfl ex1Gram_symm ex1Gram_posDef h2 ex1Two 1
    (by simpa using isTwoSymbolOf_ex1) hsupp2 (fun _ => ex1Seven) (fun _ => 2) ?_]
  · have hpf : (2 * (7 : ℤ)).natAbs.primeFactors = {2, 7} := by
      rw [show (2 * (7 : ℤ)).natAbs = 2 * 7 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors (by norm_num)]
      rfl
    rw [ex1Gram_det, hpf]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton, if_pos rfl, if_neg (by norm_num)]
    obtain ⟨hm2, hs2, -⟩ := example_i_two
    obtain ⟨hm7, hs7, -⟩ := example_i_seven
    rw [hm2, hs2, hm7, hs7, stdMass_table_3]
    norm_num
  · intro p hp hp2 hdvd
    rw [ex1Gram_det] at hdvd
    have hp7 : p = 7 := by
      have : p ∣ 7 := by exact_mod_cast hdvd
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 this
    subst hp7
    exact ⟨h7, isOddSymbolOf_ex1, hsupp7⟩

end QuadFormsKB.ConwaySloane.Mass
