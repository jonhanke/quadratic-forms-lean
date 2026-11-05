/-
# Conway–Sloane 1988, (3): the $p$-mass from the Jordan decomposition, as a named input

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §4, (3), p. 263; §5; §13, p. 282 (bibliography key `conwaysloane1988`).

The paper does not prove (3): "We shall neither prove the mass formula ((2) and (3)) nor justify our evaluation of the
$p$-masses (§5)" (§13, p. 282); its 2-adic part is "ultimately derived by translation and simplification of Watson's
formula" (§3, p. 262). Formula (2) is proved in `Density.lean` (`mass_formula_two`, $n \ge 3$); (3), the evaluation of
the $p$-mass $m_p(f) = p^{s(n+1)/2}/\alpha_p(f)$ (§12, `pMassDensity`) from a Jordan decomposition, is stated here as a
**named input**, one structure for the odd primes and one for $p = 2$:

* `PMassFormulaOdd p`: for every nondegenerate symmetric integral Gram matrix $A$ and every $p$-adic symbol $\sigma$ of
  $A$ (`IsOddSymbolOf`, *Sphere Packings, Lattices and Groups* Ch. 15), `pMassDensity p A = pMassOdd p σ N`;
* `PMassFormulaTwo`: the same at $p = 2$ with the 2-adic symbols (`IsTwoSymbolOf`) and `pMassTwo`.

Neither is definitionally the conclusion of a theorem that uses it: they relate the counting $p$-mass of §12 to the
combinatorial right-hand side of (3), while the conclusions are statements about `Siegel.mass`.

**Status.** `PMassFormulaOdd p` is a theorem for every odd prime $p$: `pMassFormulaOdd` in `OddProof.lean`
(block count identity, Theorem 9, induction over the constituents). The consequences without the odd-prime inputs are
in `MainOdd.lean`.

**Consistency.** `pMassOdd_unimodular`: for a unimodular constituent at an odd prime (the symbol $1^{\pm n}$, all primes
$p \nmid 2d$), the right-hand side of (3) is the standard $p$-mass $\mathrm{std}_p$ of (6). The library proves the
left-hand side equals $\mathrm{std}_p$ for $p \nmid 2d$ (`StdForm.lean`), so the input is a theorem at those primes.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Density
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass
import QuadFormsKB.Literature.ConwaySloane.OddClassification
import QuadFormsKB.Literature.ConwaySloane.TwoAdicForm

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-- **Input: formula (3) at an odd prime $p$** (Conway–Sloane 1988, (3), p. 263, Tables 1–2; cited, not proved, in the
paper: Smith 1867, Minkowski 1885, Siegel 1935, Watson 1976). For every dimension $n$, every symmetric integral Gram
matrix $A$ with $\det A \ne 0$, and every $p$-adic symbol $\sigma$ of $A$ supported below $N$, the $p$-mass of §12
equals the product of the diagonal factors and the cross terms:
$$\frac{p^{s(n+1)/2}}{\alpha_p(A)} = \prod_q M_p(f_q)\cdot\prod_{q<q'}(q'/q)^{\frac12n(q)n(q')}.$$
Field:
- `pMass_eq`: `pMassDensity p A = pMassOdd p σ N` under these hypotheses. -/
@[kb "conwaysloane1988" "(3), p. 263 (p odd); §13, p. 282 (not proved in the paper)"]
structure PMassFormulaOdd (p : ℕ) [Fact p.Prime] : Prop where
  pMass_eq : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → A.det ≠ 0 →
    ∀ (σ : OddSymbol) (N : ℕ), IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) σ →
      (∀ k, N ≤ k → σ k = OddFactor.trivial) → pMassDensity p A = pMassOdd p σ N

/-- **Input: formula (3) at $p = 2$** (Conway–Sloane 1988, (3), p. 263, Tables 1–2, §6; cited, not proved, in the paper,
"derived by translation and simplification of Watson's formula", §3, p. 262). For every symmetric integral Gram matrix
$A$ with $\det A \ne 0$ and every 2-adic symbol $\sigma$ of $A$ supported below $N$, the 2-mass of §12 equals the
diagonal product (species from Table 1 with the free/bound status, bound love forms included), the cross-product and the
type factor $2^{n(\mathrm{I,I}) - n(\mathrm{II})}$.
Field:
- `pMass_eq`: `pMassDensity 2 A = pMassTwo σ N` under these hypotheses. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2); §3, p. 262; §13, p. 282 (not proved in the paper)"]
structure PMassFormulaTwo : Prop where
  pMass_eq : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → A.det ≠ 0 →
    ∀ (σ : TwoSymbol) (N : ℕ), IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) σ →
      σ.SupportedBelow N → pMassDensity 2 A = pMassTwo σ N

/-- The $p$-adic symbol $1^{\varepsilon n}$ of a unimodular form at an odd prime. -/
def unimodularSymbol (n : ℕ) (ε : Sign) : OddSymbol := fun k => if k = 0 then ⟨n, ε⟩ else OddFactor.trivial

/-- **Consistency of (3) with (6) at the unimodular primes** (Conway–Sloane 1988, §7, p. 266: "for all but finitely
many primes $p$ the $p$-mass $m_p(f)$ takes [its] standard value"): for an odd prime $p \nmid d$ and the symbol
$1^{\varepsilon n}$ with $\varepsilon = \left(\frac dp\right)$, the right-hand side of (3) is $\mathrm{std}_p(f)$. The
species rule of Table 1 ($n \equiv 2 \pmod 4$, $p \equiv 3 \pmod 4$ reverses the sign) is exactly the factor
$\left(\frac{(-1)^s}{p}\right)$ in $(D/p)$, $D = (-1)^sd$. -/
@[kb "conwaysloane1988" "§7, p. 266; Table 1, p. 264 (consistency of (3) and (6))"]
theorem pMassOdd_unimodular {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d) :
    pMassOdd p (unimodularSymbol n (Sign.ofInt (jacobiSym d p))) 1 = (stdP p n d : ℝ) := by
  have hc : crossExp (fun k => (unimodularSymbol n (Sign.ofInt (jacobiSym d p)) k).dim) 1 = 0 := by
    simp [crossExp]
  rw [pMassOdd, hc, pow_zero, mul_one, Finset.prod_range_one]
  congr 1
  simp only [unimodularSymbol, if_true, oddSpecies, Species.diagFactor, stdP]
  have hcop : Nat.Coprime p d.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hd (Int.natCast_dvd.mpr h)
  have hJ : jacobiSym d p = 1 ∨ jacobiSym d p = -1 :=
    jacobiSym.eq_one_or_neg_one (by simpa [Int.gcd] using hcop.symm)
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases Nat.Prime.eq_two_or_odd hp.out with h | h
    · exact absurd h hp2
    · omega
  rcases Nat.even_or_odd n with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · -- n = 2s even
    have hno : ¬ Odd (s + s) := by rw [Nat.not_odd_iff_even]; exact ⟨s, rfl⟩
    have e1 : (s + s + 1) / 2 = s := by omega
    have e2 : (s + s) / 2 = s := by omega
    have key : ((if (s + s) % 4 = 2 ∧ p % 4 = 3 then (Sign.ofInt (jacobiSym d p)).flip
        else Sign.ofInt (jacobiSym d p)).toInt : ℤ) = jacobiSym ((-1) ^ s * d) p := by
      rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_neg_one (hp.out.odd_of_ne_two hp2)]
      rcases hp4 with h4 | h4
      · rw [ZMod.χ₄_nat_one_mod_four h4]
        have : ¬ ((s + s) % 4 = 2 ∧ p % 4 = 3) := by omega
        rw [if_neg this]
        rcases hJ with hJ | hJ <;> simp [hJ, Sign.ofInt, Sign.toInt]
      · rw [ZMod.χ₄_nat_three_mod_four h4]
        rcases Nat.even_or_odd s with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · have : ¬ ((t + t + (t + t)) % 4 = 2 ∧ p % 4 = 3) := by omega
          rw [if_neg this, Even.neg_one_pow ⟨t, rfl⟩]
          rcases hJ with hJ | hJ <;> simp [hJ, Sign.ofInt, Sign.toInt]
        · have : ((2 * t + 1 + (2 * t + 1)) % 4 = 2 ∧ p % 4 = 3) := ⟨by omega, h4⟩
          rw [if_pos this, Odd.neg_one_pow ⟨t, rfl⟩]
          rcases hJ with hJ | hJ <;> simp [hJ, Sign.ofInt, Sign.toInt, Sign.flip]
    simp only [hno, hp2, or_false, if_false, e1, e2, show ¬ (s + s = 0) by omega]
    rw [← key]
  · -- n = 2s + 1 odd
    have ho : Odd (2 * s + 1) := ⟨s, rfl⟩
    have e1 : (2 * s + 1 + 1) / 2 - 1 = (2 * s + 1) / 2 := by omega
    simp [ho, e1]

end QuadFormsKB.ConwaySloane.Mass
