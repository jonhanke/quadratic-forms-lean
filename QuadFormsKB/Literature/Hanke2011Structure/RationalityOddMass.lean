/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddSeries
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass

/-!
# Paper 6, Theorem 5.4 at odd primes: the weight of a symbol is the normalized Conway–Sloane $p$-mass

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23, Lemma 7.3, p. 29.

For an odd prime $p$ let $M_p(d, \varepsilon)$ (`Mw`) be the diagonal factor $M_p$ of the species of a Jordan
constituent of dimension $d$ and sign $\varepsilon$ (Conway–Sloane 1988, Table 1 and (5)), and
$a_\rho = p^{-\rho(\rho+1)/2}$ (`aw`).  The weight $\mathrm{wt}(\sigma)$ of a symbol (`RatOdd.wtN`, defined in
`RationalityOddSeries` by peeling the scale-$0$ factor) is then, for a symbol $\sigma$ of total dimension $r$ and
weighted scale $\nu = \sum_kk\,n_k$,
$$\mathrm{wt}(\sigma) = m_p(\sigma)\,p^{-(r+1)\nu/2},$$
$m_p(\sigma)$ the $p$-mass of Conway–Sloane's formula (3) (`pMassOdd`): the exponent of $\sqrt p$ in the cross product
is $\sum_{k<k'}(k'-k)n_kn_{k'} = (r+1)\nu - \sum_j\rho_j(\rho_j+1)$, $\rho_j = \sum_{k>j}n_k$ (`wtN_mul_pow`).
By Lemma 7.3 (`invBeta_eq_pMass`) the inverse local density of a genus is $2\,m_p\,p^{-(n+1)\nu/2}$, so $\mathrm{wt}$ is
the inverse local density divided by $2$.

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Hanke2011Structure.RatOdd

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass

/-- **The factor weight at the prime $p$**: the diagonal factor $M_p$ of the species of a constituent of dimension
$d$ and sign $\varepsilon$ (Conway–Sloane 1988, Table 1, $p$ odd). -/
noncomputable def Mw (p : ℕ) (d : ℕ) (s : Sign) : ℝ := (((oddSpecies p ⟨d, s⟩).diagFactor p : ℚ) : ℝ)

/-- **The gap weight** $a_\rho = p^{-\rho(\rho+1)/2}$. -/
noncomputable def aw (p : ℕ) (ρ : ℕ) : ℝ := ((p : ℝ) ^ (ρ * (ρ + 1) / 2))⁻¹

theorem Mw_zero (p : ℕ) : Mw p 0 Sign.plus = 1 := by
  simp [Mw, oddSpecies, Species.diagFactor]

theorem aw_zero (p : ℕ) : aw p 0 = 1 := by simp [aw]

theorem crossExp_succ (dim : ℕ → ℕ) (N : ℕ) :
    crossExp dim (N + 1) = crossExp (fun k => dim (k + 1)) N + dim 0 * ∑ k ∈ range N, (k + 1) * dim (k + 1) := by
  unfold crossExp
  rw [Finset.sum_range_succ']
  simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  ring

theorem sum_succ_dim (σ : OddSymbol) (N : ℕ) :
    ∑ k ∈ range N, (k + 1) * (σ (k + 1)).dim = zs (shiftS σ) N + rk (shiftS σ) N := by
  unfold zs rk shiftS
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem aw_eq (p : ℕ) (hp : 0 < p) (ρ : ℕ) : aw p ρ = ((Real.sqrt p) ^ (ρ * (ρ + 1)))⁻¹ := by
  unfold aw
  have h2 : (Real.sqrt p) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have : (p : ℝ) ^ (ρ * (ρ + 1) / 2) = (Real.sqrt p) ^ (ρ * (ρ + 1)) := by
    calc (p : ℝ) ^ (ρ * (ρ + 1) / 2) = ((Real.sqrt p) ^ 2) ^ (ρ * (ρ + 1) / 2) := by rw [h2]
      _ = (Real.sqrt p) ^ (2 * (ρ * (ρ + 1) / 2)) := by rw [← pow_mul]
      _ = (Real.sqrt p) ^ (ρ * (ρ + 1)) := by rw [Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self ρ)]
  rw [this]

/-- **The weight is the normalized $p$-mass** (an identity for every symbol and every cutoff):
$\mathrm{wt}_N(\sigma)\,\sqrt p^{(r+1)\nu} = \prod_{k<N}M_p(n_k, \varepsilon_k)\cdot\sqrt p^{\sum_{k<k'<N}(k'-k)n_kn_{k'}}$,
$r = \sum_{k<N}n_k$, $\nu = \sum_{k<N}kn_k$. -/
theorem wtN_mul_pow (p : ℕ) (hp : 0 < p) :
    ∀ (N : ℕ) (σ : OddSymbol),
      wtN (Mw p) (aw p) N σ * Real.sqrt p ^ ((rk σ N + 1) * zs σ N) =
        (∏ k ∈ range N, Mw p (σ k).dim (σ k).sign) * Real.sqrt p ^ crossExp (fun k => (σ k).dim) N := by
  intro N
  induction N with
  | zero => intro σ; simp [wtN_zero, rk, zs, crossExp]
  | succ N ih =>
    intro σ
    have hih := ih (shiftS σ)
    have hs0 : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hp)).ne'
    rw [wtN_succ, rk_succ, zs_succ, Finset.prod_range_succ', crossExp_succ, sum_succ_dim, aw_eq p hp]
    have e1 : crossExp (fun k => (σ (k + 1)).dim) N = crossExp (fun k => (shiftS σ k).dim) N := rfl
    have e2 : ∏ k ∈ range N, Mw p (σ (k + 1)).dim (σ (k + 1)).sign =
        ∏ k ∈ range N, Mw p (shiftS σ k).dim (shiftS σ k).sign := rfl
    simp only [e1, e2]
    set s := Real.sqrt p
    set R := rk (shiftS σ) N
    set Z := zs (shiftS σ) N
    set d := (σ 0).dim
    set W := wtN (Mw p) (aw p) N (shiftS σ)
    set Pr := ∏ k ∈ range N, Mw p (shiftS σ k).dim (shiftS σ k).sign
    set c := crossExp (fun k => (shiftS σ k).dim) N
    have key : s ^ ((d + R + 1) * (Z + R)) = s ^ (R * (R + 1)) * s ^ ((R + 1) * Z) * s ^ (d * (Z + R)) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    have hA : s ^ (R * (R + 1)) ≠ 0 := pow_ne_zero _ hs0
    rw [key, pow_add s c (d * (Z + R))]
    generalize s ^ (R * (R + 1)) = A at hA ⊢
    generalize s ^ ((R + 1) * Z) = B at hih ⊢
    generalize s ^ (d * (Z + R)) = C
    generalize s ^ c = D at hih ⊢
    calc Mw p d (σ 0).sign * A⁻¹ * W * (A * B * C) = Mw p d (σ 0).sign * (W * B) * C := by
          field_simp
      _ = _ := by rw [hih]; ring

/-- **The weight of a symbol of finite support is its $p$-mass divided by $\sqrt p^{(r+1)\nu}$**: if $\sigma$ is
trivial from scale $N$ on, $\mathrm{wt}(\sigma)\,\sqrt p^{(r+1)\nu} = m_p(\sigma)$ with $r = \sum n_k$,
$\nu = \sum kn_k$ (`pMassOdd`, Conway–Sloane's formula (3)). -/
theorem wtC_mul_pow (p : ℕ) (hp : 0 < p) {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) :
    wtC (Mw p) (aw p) σ * Real.sqrt p ^ ((rkC σ + 1) * zsC σ) = pMassOdd p σ N := by
  have h1 := wtN_mul_pow p hp N σ
  unfold wtC rkC zsC
  rw [(stable_wtN (Mw p) (aw p) (Mw_zero p) (aw_zero p)).cut_eq h, stable_rk.cut_eq h, stable_zs.cut_eq h, h1]
  unfold pMassOdd
  rw [Rat.cast_prod]
  rfl

end QuadFormsKB.Hanke2011Structure.RatOdd
