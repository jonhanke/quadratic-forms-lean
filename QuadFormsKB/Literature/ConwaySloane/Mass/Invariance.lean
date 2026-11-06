/-
# Conway–Sloane 1988: the $p$-mass of a symbol is invariant under scaling

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988) (bibliography key `conwaysloane1988`), abstract, p. 259: "Our version, unlike earlier ones, is visibly invariant
under scale changes and dualizing"; §12, p. 282: "the $p$-mass, unlike the $p$-adic density, is invariant under changing
the scale of the form".

Multiplying a form by $p$ multiplies every scale $q$ by $p$: the symbol of $pf$ has the constituent $f_q$ at the scale
$pq$, and a zero-dimensional constituent at the scale $1$ (`shiftOdd`, `shiftTwo`). This file proves that the right-hand
side of (3) does not change (`pMassOdd_shift`, `pMassTwo_shift`). For $p = 2$ the new love form $f_1$ of $2f$ is bound
exactly when $f_1$ of $f$ has type I, and takes over the factor of the old $f_{1/2}$ (§6).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-- The $p$-adic symbol ($p$ odd) of $pf$: the constituent of scale $p^{k+1}$ is that of scale $p^k$ of $f$. -/
def shiftOdd (σ : OddSymbol) : OddSymbol := fun k => if k = 0 then OddFactor.trivial else σ (k - 1)

/-- The 2-adic symbol of $2f$: the constituent of scale $2^{k+1}$ is that of scale $2^k$ of $f$. -/
def shiftTwo (σ : TwoSymbol) : TwoSymbol := fun k => if k = 0 then TwoFactor.trivial else σ (k - 1)

theorem crossExp_shift (dim : ℕ → ℕ) (N : ℕ) :
    crossExp (fun k => if k = 0 then 0 else dim (k - 1)) (N + 1) = crossExp dim N := by
  unfold crossExp
  rw [Finset.sum_range_succ']
  simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.sum_range_succ']
  simp only [if_true, mul_zero, zero_mul, add_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  omega

/-- **Scaling invariance at an odd prime** (Conway–Sloane 1988, p. 259 and §12, p. 282): the $p$-mass (3) of the
symbol of $pf$ equals that of $f$. -/
@[kb "conwaysloane1988" "abstract, p. 259; §12, p. 282 (invariance under scale changes)"]
theorem pMassOdd_shift (p : ℕ) (σ : OddSymbol) (N : ℕ) : pMassOdd p (shiftOdd σ) (N + 1) = pMassOdd p σ N := by
  unfold pMassOdd
  have hc : crossExp (fun k => (shiftOdd σ k).dim) (N + 1) = crossExp (fun k => (σ k).dim) N := by
    have : (fun k => (shiftOdd σ k).dim) = (fun k => if k = 0 then 0 else (σ (k - 1)).dim) := by
      funext k
      by_cases hk : k = 0 <;> simp [shiftOdd, hk, OddFactor.trivial]
    rw [this]; exact crossExp_shift (fun k => (σ k).dim) N
  rw [hc, Finset.prod_range_succ']
  simp [shiftOdd, oddSpecies, OddFactor.trivial, Species.diagFactor]

theorem isBound_shift (σ : TwoSymbol) (k : ℕ) : IsBound (shiftTwo σ) (k + 1) ↔ IsBound σ k := by
  unfold IsBound shiftTwo
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [TwoFactor.trivial]
  · have h1 : k ≠ 0 := by omega
    simp [h1]

/-- **Scaling invariance at $p = 2$** (Conway–Sloane 1988, p. 259 and §12, p. 282): the 2-mass (3) of the symbol of
$2f$ equals that of $f$. -/
@[kb "conwaysloane1988" "abstract, p. 259; §12, p. 282 (invariance under scale changes)"]
theorem pMassTwo_shift (σ : TwoSymbol) (N : ℕ) : pMassTwo (shiftTwo σ) (N + 1) = pMassTwo σ N := by
  have hc : crossExp (fun k => (shiftTwo σ k).dim) (N + 1) = crossExp (fun k => (σ k).dim) N := by
    have : (fun k => (shiftTwo σ k).dim) = (fun k => if k = 0 then 0 else (σ (k - 1)).dim) := by
      funext k
      by_cases hk : k = 0 <;> simp [shiftTwo, hk, TwoFactor.trivial]
    rw [this]; exact crossExp_shift (fun k => (σ k).dim) N
  have hII : nII (shiftTwo σ) (N + 1) = nII σ N := by
    unfold nII
    rw [Finset.sum_range_succ']
    simp [shiftTwo, TwoFactor.trivial]
  have hII' : nII' (shiftTwo σ) (N + 1) = nII' σ N := by
    unfold nII'
    rw [Finset.sum_range_succ']
    simp [shiftTwo, TwoFactor.trivial]
  have hdiag : diagProdTwo (shiftTwo σ) (N + 1) = diagProdTwo σ N := by
    unfold diagProdTwo
    rw [Finset.prod_range_succ']
    have h0 : (twoSpecies (shiftTwo σ 0) (IsBound (shiftTwo σ) 0)).diagFactor 2 = halfFactor σ := by
      unfold halfFactor
      by_cases hI : (σ 0).type = .I
      · have hb : IsBound (shiftTwo σ) 0 := Or.inr (by simpa [shiftTwo] using hI)
        simp only [hI, if_true]
        simp (config := { decide := true }) [shiftTwo, twoSpecies, hb, TwoFactor.trivial, Species.diagFactor,
          lowerProd]
      · have hb : ¬ IsBound (shiftTwo σ) 0 := by
          rintro (⟨h, -⟩ | h)
          · exact h rfl
          · exact hI (by simpa [shiftTwo] using h)
        simp only [hI, if_false]
        have : shiftTwo σ 0 = TwoFactor.trivial := rfl
        rw [this, twoSpecies_trivial_free hb]; rfl
    have hhalf : halfFactor (shiftTwo σ) = 1 := by simp [halfFactor, shiftTwo, TwoFactor.trivial]
    rw [h0, hhalf]
    have : ∀ k ∈ range (N + 1), (twoSpecies (shiftTwo σ (k + 1)) (IsBound (shiftTwo σ) (k + 1))).diagFactor 2 =
        (twoSpecies (σ k) (IsBound σ k)).diagFactor 2 := fun k _ => by
      have : shiftTwo σ (k + 1) = σ k := by simp [shiftTwo]
      rw [this, twoSpecies_congr (isBound_shift σ k) rfl rfl rfl]
    rw [Finset.prod_congr rfl this]
    ring
  unfold pMassTwo
  rw [hdiag, hc, hII, hII']

end QuadFormsKB.ConwaySloane.Mass
