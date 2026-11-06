/-
# Conway–Sloane 1988, §6: the mass formula in dimension 1

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §6, p. 266 (bibliography key `conwaysloane1988`): "This 2 should therefore be replaced by 1 in dimensions 0 and
1, because then both the local and global forms of determinant $d$ are unique".

For a one-dimensional form $\langle d\rangle$ every 2-adic symbol has one constituent $\mathrm I_1$ (octane value $\pm1$,
free, species $0+$) and two bound love forms, so $m_2 = \frac14 = \frac12\mathrm{std}_2$; at an odd $p \mid d$ the symbol
has one constituent of dimension 1 and $m_p = \frac12 = \mathrm{std}_p$. With $\mathrm{std}(f) = 2$ (Table 3) the
working form of (2) gives $1$, while the mass is $\frac12$ (`Siegel.RankOne.mass_unary`): the initial factor $2$ of
(2) must be replaced by $1$ (`dim_one_working_form`).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass
import QuadFormsKB.Literature.ConwaySloane.Mass.StandardMass

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-- The 2-adic symbol with the single constituent $f$ at the scale $2^a$. -/
def singleTwo (a : ℕ) (f : TwoFactor) : TwoSymbol := fun k => if k = a then f else TwoFactor.trivial

/-- The $p$-adic symbol with the single constituent $f$ at the scale $p^a$. -/
def singleOdd (a : ℕ) (f : OddFactor) : OddSymbol := fun k => if k = a then f else OddFactor.trivial

theorem crossExp_single (a N : ℕ) (m : ℕ) :
    crossExp (fun k => if k = a then m else 0) N = 0 := by
  unfold crossExp
  refine Finset.sum_eq_zero fun k' hk' => Finset.sum_eq_zero fun k hk => ?_
  have : k < k' := Finset.mem_range.mp hk
  by_cases h1 : k = a <;> by_cases h2 : k' = a <;> simp [h1, h2] <;> omega

/-- In dimension 1 the 2-mass of the symbol is $\frac14$: the constituent $\mathrm I_1$ is free with octane value
$\pm1$ (species $0+$) and its two neighbours are bound love forms. -/
theorem pMassTwo_single (a : ℕ) (f : TwoFactor) (hdim : f.dim = 1) (htype : f.type = .I)
    (hoct : octane f = 1 ∨ octane f = 7) : pMassTwo (singleTwo a f) (a + 1) = 1 / 4 := by
  have hsp : (twoSpecies f False).diagFactor 2 = 1 := by
    rcases hoct with h | h <;> simp (config := { decide := true }) [twoSpecies, h, htype, hdim, Species.diagFactor]
  have hfree : ¬ IsBound (singleTwo a f) a := by
    rintro (⟨ha, h⟩ | h)
    · have : a - 1 ≠ a := by omega
      simp [singleTwo, this, TwoFactor.trivial] at h
    · have : a + 1 ≠ a := by omega
      simp [singleTwo, this, TwoFactor.trivial] at h
  have hfa : (twoSpecies (singleTwo a f a) (IsBound (singleTwo a f) a)).diagFactor 2 = 1 := by
    rw [← hsp]; simp only [singleTwo, if_true]
    exact congrArg _ (twoSpecies_congr (by simpa using hfree) rfl rfl rfl)
  have hb1 : (twoSpecies (singleTwo a f (a + 1)) (IsBound (singleTwo a f) (a + 1))).diagFactor 2 = 1 / 2 := by
    have hb : IsBound (singleTwo a f) (a + 1) := Or.inl ⟨by omega, by simp [singleTwo, htype]⟩
    have : singleTwo a f (a + 1) = TwoFactor.trivial := by simp [singleTwo]
    rw [this, twoSpecies_trivial_bound hb]; simp [Species.diagFactor, Species.odd, lowerProd]
  have hother : ∀ k, k + 1 < a → (twoSpecies (singleTwo a f k) (IsBound (singleTwo a f) k)).diagFactor 2 = 1 := by
    intro k hk
    have hb : ¬ IsBound (singleTwo a f) k := by
      rintro (⟨-, h⟩ | h)
      · have : k - 1 ≠ a := by omega
        simp [singleTwo, this, TwoFactor.trivial] at h
      · have : k + 1 ≠ a := by omega
        simp [singleTwo, this, TwoFactor.trivial] at h
    have : singleTwo a f k = TwoFactor.trivial := by simp [singleTwo]; omega
    rw [this, twoSpecies_trivial_free hb]; rfl
  have hd : diagProdTwo (singleTwo a f) (a + 1) = 1 / 4 := by
    unfold diagProdTwo
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [Finset.prod_range_succ, Finset.prod_range_one, hfa, hb1]
      simp [halfFactor, singleTwo, htype]; norm_num
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hbm : (twoSpecies (singleTwo (b + 1) f b) (IsBound (singleTwo (b + 1) f) b)).diagFactor 2 = 1 / 2 := by
        have hb : IsBound (singleTwo (b + 1) f) b := Or.inr (by simp [singleTwo, htype])
        have : singleTwo (b + 1) f b = TwoFactor.trivial := by simp [singleTwo]
        rw [this, twoSpecies_trivial_bound hb]; simp [Species.diagFactor, Species.odd, lowerProd]
      rw [show b + 1 + 1 + 1 = b + 3 by omega, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_eq_one (fun k hk => hother k (by simp at hk; omega)), hbm,
        show b + 2 = b + 1 + 1 by omega, hb1, hfa]
      simp [halfFactor, singleTwo, TwoFactor.trivial]; norm_num
  have hc : crossExp (fun k => (singleTwo a f k).dim) (a + 1) = 0 := by
    have : (fun k => (singleTwo a f k).dim) = fun k => if k = a then 1 else 0 := by
      funext k; by_cases h : k = a <;> simp [singleTwo, h, hdim, TwoFactor.trivial]
    rw [this]; exact crossExp_single a (a + 1) 1
  have hII : nII (singleTwo a f) (a + 1) = 0 := by
    unfold nII
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : k = a <;> simp [singleTwo, h, htype, TwoFactor.trivial]
  have hII' : nII' (singleTwo a f) (a + 1) = 0 := by
    unfold nII'
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : k = a <;> simp [singleTwo, h, TwoFactor.trivial]
  rw [pMassTwo, hd, hc, hII, hII']; norm_num

/-- In dimension 1 the $p$-mass of the symbol ($p$ odd) is $\frac12$. -/
theorem pMassOdd_single (p a : ℕ) (ε : Sign) : pMassOdd p (singleOdd a ⟨1, ε⟩) (a + 1) = 1 / 2 := by
  have hc : crossExp (fun k => (singleOdd a ⟨1, ε⟩ k).dim) (a + 1) = 0 := by
    have : (fun k => (singleOdd a ⟨1, ε⟩ k).dim) = fun k => if k = a then 1 else 0 := by
      funext k; by_cases h : k = a <;> simp [singleOdd, h, OddFactor.trivial]
    rw [this]; exact crossExp_single a (a + 1) 1
  rw [pMassOdd, hc, pow_zero, mul_one, Finset.prod_range_succ,
    Finset.prod_eq_one (fun k hk => by
      have : k ≠ a := by simp at hk; omega
      simp [singleOdd, this, oddSpecies, OddFactor.trivial, Species.diagFactor])]
  simp [singleOdd, oddSpecies, Species.diagFactor, lowerProd]

/-- **§6, dimension 1** (Conway–Sloane 1988, p. 266): for a form of dimension 1 and determinant $d$, with a 2-adic
symbol of one constituent $\mathrm I_1$ at $2^a$ (existence condition (33): octane value $\pm1$) and $p$-adic symbols of one
constituent at $p^{a_p}$, the working form of (2), $\mathrm{std}(f)\prod_{p \mid 2d}m_p/\mathrm{std}_p$, equals $1$, twice
the mass $\frac12$ (`Siegel.RankOne.mass_unary`): in dimension 1 the initial factor 2 of (2) must be replaced by 1. -/
@[kb "conwaysloane1988" "§6, p. 266 (dimension 1)"]
theorem dim_one_working_form (d : ℤ) (hd : d ≠ 0) (a : ℕ) (f : TwoFactor) (hdim : f.dim = 1) (htype : f.type = .I)
    (hoct : octane f = 1 ∨ octane f = 7) (ap : ℕ → ℕ) (ε : ℕ → Sign) :
    stdMass 1 d * ∏ p ∈ (2 * d).natAbs.primeFactors,
      ((if p = 2 then pMassTwo (singleTwo a f) (a + 1) else pMassOdd p (singleOdd (ap p) ⟨1, ε p⟩) (ap p + 1)) /
        (stdP p 1 d : ℝ)) = 1 := by
  have hs : ∀ p, (stdP p 1 d : ℝ) = 1 / 2 := fun p => by
    simp [stdP, lowerProd]
  have h2 : 2 ∈ (2 * d).natAbs.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, by simpa using hd⟩
    rw [Int.natAbs_mul]; exact dvd_mul_right _ _
  rw [← Finset.mul_prod_erase _ _ h2, if_pos rfl, pMassTwo_single a f hdim htype hoct, hs,
      Finset.prod_eq_one (fun p hp => by
        rw [if_neg (Finset.ne_of_mem_erase hp), pMassOdd_single, hs]; norm_num),
      stdMass_table_1]
  norm_num

end QuadFormsKB.ConwaySloane.Mass
