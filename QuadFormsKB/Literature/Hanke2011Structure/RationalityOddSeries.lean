/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.ConwaySloane.Symbol

/-!
# Paper 6, Theorem 5.4 at odd primes, every rank: the generating series of Conway–Sloane symbols

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23.

This file is purely combinatorial (no genera, no densities).  It proves the rationality of the weighted generating
series of $p$-adic symbols (Conway–Sloane, odd $p$): a symbol is a function $k \mapsto (n_k, \varepsilon_k)$
(`OddSymbol`) of total dimension $r = \sum_k n_k$ and weighted scale $Z = \sum_k k\,n_k$.  For
* a factor weight $M$ (later: the diagonal factor $M_p$ of the species) and a gap weight $a_\rho$
  (later: $p^{-\rho(\rho+1)/2}$),
* a function $\varphi$ of the *state* $(E, O, d_e, d_o)$ of the symbol: $E$, $O$ the products of the signs
  $\varepsilon_k$ over the even / odd scales, $d_e$, $d_o$ the total dimensions at the even / odd scales,

the *weight* of a symbol is $\prod_k M(n_k, \varepsilon_k)\prod_k a_{\rho_k}$, $\rho_k = \sum_{k' > k}n_{k'}$ (`wt`,
defined by peeling the scale-$0$ factor), and the series is $\sum_\nu\bigl(\sum_{Z(\sigma)=\nu}\varphi(\text{state})\,
\mathrm{wt}(\sigma)\bigr)X^\nu$.  Peeling the scale-$0$ factor $\sigma = (f, \sigma')$ gives
$$S_r[\varphi] = a_rX^r\,S_r[\varphi^{\mathrm{swap}}] + \sum_{d \ge 1,\ \varepsilon}M(d,\varepsilon)\,a_{r-d}X^{r-d}\,
S_{r-d}[\varphi_{(d,\varepsilon)}],$$
where the swap of even and odd scales is an involution, so the system closes: `ratS` ($S_r[\varphi]$ is rational for
every $r$ and every $\varphi$, by strong induction on $r$, solving the $2\times2$ system $S_r[\varphi]$,
$S_r[\varphi\circ\mathrm{swap}]$) and `rat_Pn` (the same for the primitive part, $n_0 \ge 1$, which is the sum over
$d \ge 1$ in the recursion).  Fully proved (no hypothesis beyond $M(0,+) = 1$, $a_0 = 1$).

Formalization: a symbol is a function `OddSymbol` $=\mathbb N \to$ `OddFactor`; the statistics and the weight are
first defined with a cutoff $N$ (`rk`, `zs`, `ev`, `od`, `de`, `dd`, `wtN`), shown stable once the symbol is trivial
(`stable_rk`, …, `stable_wtN`), and then used without cutoff (`rkC`, `zsC`, `statC`, `wtC`).  The finite sets
`symSet r ν` of valid symbols of finite support with $\sum n_k = r$, $\sum kn_k = \nu$ are decomposed by their first
factor (`symSetQ_eq`, `finsum_symSetQ`), which gives the coefficient recursion `coef_peel`, the series recursion
`ser_peel` and the split `ser_split`.

Indices are 0-based.
-/

open PowerSeries Finset

namespace QuadFormsKB.Hanke2011Structure.RatOdd

open QuadFormsKB.ConwaySloane

/-! ### Rational power series -/

/-- **A rational power series over $\mathbb R$**: $S\,Q = P$ for polynomials $P$, $Q$ with $Q(0) \ne 0$ (so
$S = P/Q$ in $\mathbb R[[X]]$). -/
def RatSeries (S : PowerSeries ℝ) : Prop :=
  ∃ P Q : Polynomial ℝ, Q.coeff 0 ≠ 0 ∧ S * (Q : PowerSeries ℝ) = (P : PowerSeries ℝ)

theorem RatSeries.zero : RatSeries 0 := ⟨0, 1, by simp, by simp⟩

theorem RatSeries.const (c : ℝ) : RatSeries (PowerSeries.C c) :=
  ⟨Polynomial.C c, 1, by simp, by simp⟩

theorem RatSeries.add {S T : PowerSeries ℝ} (hS : RatSeries S) (hT : RatSeries T) : RatSeries (S + T) := by
  obtain ⟨P, Q, hQ, h⟩ := hS
  obtain ⟨P', Q', hQ', h'⟩ := hT
  refine ⟨P * Q' + P' * Q, Q * Q', ?_, ?_⟩
  · rw [Polynomial.mul_coeff_zero]; exact mul_ne_zero hQ hQ'
  · push_cast
    linear_combination (↑Q' : PowerSeries ℝ) * h + (↑Q : PowerSeries ℝ) * h'

theorem RatSeries.polyMul (R : Polynomial ℝ) {S : PowerSeries ℝ} (hS : RatSeries S) :
    RatSeries ((R : PowerSeries ℝ) * S) := by
  obtain ⟨P, Q, hQ, h⟩ := hS
  refine ⟨R * P, Q, hQ, ?_⟩
  push_cast
  rw [mul_assoc, h]

theorem RatSeries.CXpowMul (c : ℝ) (m : ℕ) {S : PowerSeries ℝ} (hS : RatSeries S) :
    RatSeries (PowerSeries.C c * PowerSeries.X ^ m * S) := by
  have := RatSeries.polyMul (Polynomial.C c * Polynomial.X ^ m) hS
  simpa using this

theorem RatSeries.sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) (h : ∀ i ∈ s, RatSeries (f i)) :
    RatSeries (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RatSeries.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (mem_insert_self _ _)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- Dividing by a polynomial with nonzero constant term preserves rationality. -/
theorem RatSeries.of_mul (W : Polynomial ℝ) (hW : W.coeff 0 ≠ 0) {S T : PowerSeries ℝ}
    (h : S * (W : PowerSeries ℝ) = T) (hT : RatSeries T) : RatSeries S := by
  obtain ⟨P, Q, hQ, hh⟩ := hT
  refine ⟨P, W * Q, ?_, ?_⟩
  · rw [Polynomial.mul_coeff_zero]; exact mul_ne_zero hW hQ
  · push_cast
    rw [← mul_assoc, h, hh]

/-! ### Symbols and their statistics (cutoff $N$) -/

/-- The sign $\pm$ as a unit of $\mathbb Z$. -/
def signU : Sign → ℤˣ
  | .plus => 1
  | .minus => -1

/-- The symbol with the scale-$0$ factor removed: $k \mapsto \sigma(k+1)$. -/
def shiftS (σ : OddSymbol) : OddSymbol := fun k => σ (k + 1)

/-- The symbol with the factor $f$ at scale $0$ followed by $\sigma$ at the scales $1, 2, \dots$. -/
def consS (f : OddFactor) (σ : OddSymbol) : OddSymbol := fun k => match k with
  | 0 => f
  | k + 1 => σ k

@[simp] theorem consS_zero (f : OddFactor) (σ : OddSymbol) : consS f σ 0 = f := rfl
@[simp] theorem consS_succ (f : OddFactor) (σ : OddSymbol) (k : ℕ) : consS f σ (k + 1) = σ k := rfl
@[simp] theorem shiftS_consS (f : OddFactor) (σ : OddSymbol) : shiftS (consS f σ) = σ := rfl

theorem consS_shiftS (σ : OddSymbol) : consS (σ 0) (shiftS σ) = σ := by
  funext k; cases k <;> rfl

theorem consS_inj {f g : OddFactor} {σ τ : OddSymbol} (h : consS f σ = consS g τ) : f = g ∧ σ = τ := by
  refine ⟨congrFun h 0, ?_⟩
  funext k
  exact congrFun h (k + 1)

/-- The total dimension $\sum_{k<N}n_k$. -/
def rk (σ : OddSymbol) (N : ℕ) : ℕ := ∑ k ∈ range N, (σ k).dim

/-- The weighted scale $\sum_{k<N}k\,n_k$ (for a symbol of a diagonal form $\operatorname{diag}(p^{z_i}u_i)$, $\sum_iz_i$). -/
def zs (σ : OddSymbol) (N : ℕ) : ℕ := ∑ k ∈ range N, k * (σ k).dim

/-- The product of the signs at the even scales. -/
def ev (σ : OddSymbol) (N : ℕ) : ℤˣ := ∏ k ∈ range N, if k % 2 = 0 then signU (σ k).sign else 1

/-- The product of the signs at the odd scales. -/
def od (σ : OddSymbol) (N : ℕ) : ℤˣ := ∏ k ∈ range N, if k % 2 = 1 then signU (σ k).sign else 1

/-- The total dimension at the even scales. -/
def de (σ : OddSymbol) (N : ℕ) : ℕ := ∑ k ∈ range N, if k % 2 = 0 then (σ k).dim else 0

/-- The total dimension at the odd scales. -/
def dd (σ : OddSymbol) (N : ℕ) : ℕ := ∑ k ∈ range N, if k % 2 = 1 then (σ k).dim else 0

theorem rk_succ (σ : OddSymbol) (N : ℕ) : rk σ (N + 1) = (σ 0).dim + rk (shiftS σ) N := by
  unfold rk shiftS
  rw [Finset.sum_range_succ']; ring

theorem rk_succ_end (σ : OddSymbol) (N : ℕ) : rk σ (N + 1) = rk σ N + (σ N).dim := by
  unfold rk; rw [Finset.sum_range_succ]

theorem zs_succ (σ : OddSymbol) (N : ℕ) : zs σ (N + 1) = zs (shiftS σ) N + rk (shiftS σ) N := by
  unfold zs rk shiftS
  rw [Finset.sum_range_succ', ← Finset.sum_add_distrib]
  simp only [zero_mul, add_zero]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ev_succ (σ : OddSymbol) (N : ℕ) : ev σ (N + 1) = od (shiftS σ) N * signU (σ 0).sign := by
  unfold ev od shiftS
  rw [Finset.prod_range_succ']
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have : (k + 1) % 2 = 0 ↔ k % 2 = 1 := by omega
  simp only [this]

theorem od_succ (σ : OddSymbol) (N : ℕ) : od σ (N + 1) = ev (shiftS σ) N := by
  unfold ev od shiftS
  rw [Finset.prod_range_succ']
  simp only [Nat.zero_mod, show ¬ (0 = 1) by omega, ite_false, mul_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : (k + 1) % 2 = 1 ↔ k % 2 = 0 := by omega
  simp only [this]

theorem de_succ (σ : OddSymbol) (N : ℕ) : de σ (N + 1) = dd (shiftS σ) N + (σ 0).dim := by
  unfold de dd shiftS
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_mod, ite_true]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (k + 1) % 2 = 0 ↔ k % 2 = 1 := by omega
  simp only [this]

theorem dd_succ (σ : OddSymbol) (N : ℕ) : dd σ (N + 1) = de (shiftS σ) N := by
  unfold de dd shiftS
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_mod, show ¬ (0 = 1) by omega, ite_false, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (k + 1) % 2 = 1 ↔ k % 2 = 0 := by omega
  simp only [this]

/-- The trivial symbol. -/
def triv : OddSymbol := fun _ => OddFactor.trivial

/-- **Valid symbols**: a zero-dimensional factor has sign $+$ (the factor is the omitted one). -/
def Valid (σ : OddSymbol) : Prop := ∀ k, (σ k).dim = 0 → (σ k).sign = Sign.plus

/-- The symbol is trivial from scale $N$ on. -/
def TrivFrom (σ : OddSymbol) (N : ℕ) : Prop := ∀ k, N ≤ k → σ k = OddFactor.trivial

theorem triv_of_dim_zero {σ : OddSymbol} (hV : Valid σ) {k : ℕ} (h : (σ k).dim = 0) : σ k = OddFactor.trivial := by
  have hs := hV k h
  cases hk : σ k with
  | mk d s =>
    rw [hk] at h hs
    simp only at h hs
    subst h
    subst hs
    rfl

/-- The symbol has finite support: it is trivial from some scale on. -/
def FinSupp (σ : OddSymbol) : Prop := ∃ N, TrivFrom σ N

theorem TrivFrom.dim {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {k : ℕ} (hk : N ≤ k) : (σ k).dim = 0 := by
  rw [h k hk]; rfl

theorem TrivFrom.sign {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {k : ℕ} (hk : N ≤ k) :
    (σ k).sign = Sign.plus := by
  rw [h k hk]; rfl

theorem trivFrom_cons {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) (f : OddFactor) : TrivFrom (consS f σ) (N + 1) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact h j (by omega)

theorem trivFrom_shift {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) : TrivFrom (shiftS σ) N := by
  intro k hk
  exact h (k + 1) (by omega)

theorem trivFrom_shift' {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ (N + 1)) : TrivFrom (shiftS σ) N := by
  intro k hk
  exact h (k + 1) (by omega)

theorem finSupp_cons {σ : OddSymbol} (f : OddFactor) : FinSupp (consS f σ) ↔ FinSupp σ := by
  constructor
  · rintro ⟨N, h⟩
    exact ⟨N, trivFrom_shift h⟩
  · rintro ⟨N, h⟩
    exact ⟨N + 1, trivFrom_cons h f⟩

theorem valid_cons {σ : OddSymbol} (f : OddFactor) :
    Valid (consS f σ) ↔ (f.dim = 0 → f.sign = Sign.plus) ∧ Valid σ := by
  constructor
  · intro h
    exact ⟨h 0, fun k => h (k + 1)⟩
  · rintro ⟨h0, h⟩ k
    cases k with
    | zero => exact h0
    | succ k => exact h k

theorem triv_trivFrom : TrivFrom triv 0 := fun _ _ => rfl

/-! ### Stability of the statistics under the cutoff -/

theorem rk_stable {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {N' : ℕ} (hN : N ≤ N') : rk σ N' = rk σ N := by
  unfold rk
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun k _ hk => ?_
  exact h.dim (by simpa using hk)

theorem zs_stable {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {N' : ℕ} (hN : N ≤ N') : zs σ N' = zs σ N := by
  unfold zs
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun k _ hk => ?_
  rw [h.dim (by simpa using hk)]; simp

theorem ev_stable {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {N' : ℕ} (hN : N ≤ N') : ev σ N' = ev σ N := by
  unfold ev
  symm
  refine Finset.prod_subset (Finset.range_subset_range.2 hN) fun k _ hk => ?_
  rw [h.sign (by simpa using hk)]; simp [signU]

theorem od_stable {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {N' : ℕ} (hN : N ≤ N') : od σ N' = od σ N := by
  unfold od
  symm
  refine Finset.prod_subset (Finset.range_subset_range.2 hN) fun k _ hk => ?_
  rw [h.sign (by simpa using hk)]; simp [signU]

theorem de_stable {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {N' : ℕ} (hN : N ≤ N') : de σ N' = de σ N := by
  unfold de
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun k _ hk => ?_
  rw [h.dim (by simpa using hk)]; simp

theorem dd_stable {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) {N' : ℕ} (hN : N ≤ N') : dd σ N' = dd σ N := by
  unfold dd
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun k _ hk => ?_
  rw [h.dim (by simpa using hk)]; simp

/-! ### Weights -/

/-- **The weight of a symbol, cut off at $N$.**  With a factor weight `M` (dimension, sign) and a gap weight `a`
(indexed by the total dimension $\rho$ of the scales above the gap), defined by peeling the scale-$0$ factor:
$$\mathrm{wt}_0(\sigma) = 1,\qquad \mathrm{wt}_{N+1}(\sigma) = M(n_0,\varepsilon_0)\,a_{\rho_0}\,\mathrm{wt}_N(\sigma'),$$
$\sigma' = $ `shiftS σ`, $\rho_0 = \sum_{k<N}n'_k$.  Unfolded, $\mathrm{wt}_N(\sigma) = \prod_{k<N}M(n_k,\varepsilon_k)
\prod_{k<N}a_{\rho_k}$, $\rho_k = \sum_{k<j<N}n_j$. -/
def wtN (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) : ℕ → OddSymbol → ℝ
  | 0, _ => 1
  | N + 1, σ => M (σ 0).dim (σ 0).sign * a (rk (shiftS σ) N) * wtN M a N (shiftS σ)

theorem wtN_zero (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) (σ : OddSymbol) : wtN M a 0 σ = 1 := rfl

theorem wtN_succ (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) (N : ℕ) (σ : OddSymbol) :
    wtN M a (N + 1) σ = M (σ 0).dim (σ 0).sign * a (rk (shiftS σ) N) * wtN M a N (shiftS σ) := rfl

theorem wtN_stable_succ (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) :
    ∀ (N : ℕ) (σ : OddSymbol), TrivFrom σ N → wtN M a (N + 1) σ = wtN M a N σ := by
  intro N
  induction N with
  | zero =>
    intro σ h
    rw [wtN_succ, wtN_zero, wtN_zero, h.dim (le_refl 0), h.sign (le_refl 0)]
    simp [hM, ha, rk]
  | succ N ih =>
    intro σ h
    rw [wtN_succ M a (N + 1) σ, wtN_succ M a N σ, ih (shiftS σ) (trivFrom_shift' h), rk_succ_end (shiftS σ) N]
    have : (shiftS σ N).dim = 0 := h.dim (by omega)
    rw [this, add_zero]

theorem wtN_stable (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) (hM : M 0 Sign.plus = 1) (ha : a 0 = 1)
    {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) : ∀ m, wtN M a (N + m) σ = wtN M a N σ := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, wtN_stable_succ M a hM ha (N + m) σ (fun k hk => h k (by omega)), ih]

/-! ### Cutoff-free statistics -/

open Classical in
/-- A cutoff from which the symbol is trivial (`0` if there is none). -/
noncomputable def cut (σ : OddSymbol) : ℕ := if h : FinSupp σ then h.choose else 0

theorem trivFrom_cut {σ : OddSymbol} (h : FinSupp σ) : TrivFrom σ (cut σ) := by
  unfold cut
  rw [dif_pos h]  
  exact h.choose_spec

/-- A statistic is stable if it does not change when the cutoff is increased past the support. -/
def Stable {α : Type*} (g : OddSymbol → ℕ → α) : Prop :=
  ∀ σ N, TrivFrom σ N → ∀ N', N ≤ N' → g σ N' = g σ N

theorem Stable.eq {α : Type*} {g : OddSymbol → ℕ → α} (hg : Stable g) {σ : OddSymbol} {N N' : ℕ}
    (h : TrivFrom σ N) (h' : TrivFrom σ N') : g σ N = g σ N' := by
  rw [← hg σ N h (max N N') (le_max_left _ _), ← hg σ N' h' (max N N') (le_max_right _ _)]

theorem Stable.cut_eq {α : Type*} {g : OddSymbol → ℕ → α} (hg : Stable g) {σ : OddSymbol} {N : ℕ}
    (h : TrivFrom σ N) : g σ (cut σ) = g σ N :=
  hg.eq (trivFrom_cut ⟨N, h⟩) h

theorem stable_rk : Stable rk := fun _ _ h _ hN => rk_stable h hN
theorem stable_zs : Stable zs := fun _ _ h _ hN => zs_stable h hN
theorem stable_ev : Stable ev := fun _ _ h _ hN => ev_stable h hN
theorem stable_od : Stable od := fun _ _ h _ hN => od_stable h hN
theorem stable_de : Stable de := fun _ _ h _ hN => de_stable h hN
theorem stable_dd : Stable dd := fun _ _ h _ hN => dd_stable h hN

theorem stable_wtN (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) :
    Stable (fun σ N => wtN M a N σ) := by
  intro σ N h N' hN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact wtN_stable M a hM ha h m

/-- The total dimension $\sum_kn_k$ of a symbol of finite support. -/
noncomputable def rkC (σ : OddSymbol) : ℕ := rk σ (cut σ)
/-- The weighted scale $\sum_kk\,n_k$. -/
noncomputable def zsC (σ : OddSymbol) : ℕ := zs σ (cut σ)
/-- The product of the signs at the even scales. -/
noncomputable def evC (σ : OddSymbol) : ℤˣ := ev σ (cut σ)
/-- The product of the signs at the odd scales. -/
noncomputable def odC (σ : OddSymbol) : ℤˣ := od σ (cut σ)
/-- The total dimension at the even scales. -/
noncomputable def deC (σ : OddSymbol) : ℕ := de σ (cut σ)
/-- The total dimension at the odd scales. -/
noncomputable def ddC (σ : OddSymbol) : ℕ := dd σ (cut σ)
/-- The weight of a symbol of finite support. -/
noncomputable def wtC (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) (σ : OddSymbol) : ℝ := wtN M a (cut σ) σ

/-- The **state** $(E, O, d_e, d_o)$ of a symbol: the products of the signs at the even / odd scales and the total
dimensions at the even / odd scales. -/
abbrev State : Type := ℤˣ × ℤˣ × ℕ × ℕ

/-- The state of a symbol of finite support. -/
noncomputable def statC (σ : OddSymbol) : State := (evC σ, odC σ, deC σ, ddC σ)

/-- Adding the factor $f$ at scale $0$ (and shifting all other scales up by one) changes the state by `step f`. -/
def step (f : OddFactor) (s : State) : State := (s.2.1 * signU f.sign, s.1, s.2.2.2 + f.dim, s.2.2.1)

/-- Swapping the even and the odd scales. -/
def swapS (s : State) : State := (s.2.1, s.1, s.2.2.2, s.2.2.1)

theorem swapS_swapS (s : State) : swapS (swapS s) = s := rfl

theorem step_trivial : step OddFactor.trivial = swapS := by
  funext s
  simp [step, swapS, OddFactor.trivial, signU]

section Peel

variable (M : ℕ → Sign → ℝ) (a : ℕ → ℝ)

theorem rkC_cons {σ : OddSymbol} (h : FinSupp σ) (f : OddFactor) : rkC (consS f σ) = f.dim + rkC σ := by
  obtain ⟨N, hN⟩ := h
  unfold rkC
  rw [stable_rk.cut_eq (trivFrom_cons hN f), stable_rk.cut_eq hN, rk_succ]
  rfl

theorem zsC_cons {σ : OddSymbol} (h : FinSupp σ) (f : OddFactor) : zsC (consS f σ) = zsC σ + rkC σ := by
  obtain ⟨N, hN⟩ := h
  unfold zsC rkC
  rw [stable_zs.cut_eq (trivFrom_cons hN f), stable_zs.cut_eq hN, stable_rk.cut_eq hN, zs_succ]
  rfl

theorem statC_cons {σ : OddSymbol} (h : FinSupp σ) (f : OddFactor) : statC (consS f σ) = step f (statC σ) := by
  obtain ⟨N, hN⟩ := h
  have h1 := trivFrom_cons hN f
  unfold statC evC odC deC ddC step
  rw [stable_ev.cut_eq h1, stable_od.cut_eq h1, stable_de.cut_eq h1, stable_dd.cut_eq h1,
    stable_ev.cut_eq hN, stable_od.cut_eq hN, stable_de.cut_eq hN, stable_dd.cut_eq hN,
    ev_succ, od_succ, de_succ, dd_succ]
  rfl

theorem wtC_cons (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) {σ : OddSymbol} (h : FinSupp σ) (f : OddFactor) :
    wtC M a (consS f σ) = M f.dim f.sign * a (rkC σ) * wtC M a σ := by
  obtain ⟨N, hN⟩ := h
  have h1 := trivFrom_cons hN f
  unfold wtC rkC
  rw [(stable_wtN M a hM ha).cut_eq h1, (stable_wtN M a hM ha).cut_eq hN, stable_rk.cut_eq hN, wtN_succ]
  rfl

end Peel

/-! ### The finite sets of symbols of given rank and weighted scale -/

/-- The valid symbols of finite support with total dimension $r$ and weighted scale $\nu$ ("valid" = a
zero-dimensional factor has sign $+$). -/
def symSet (r ν : ℕ) : Set OddSymbol := {σ | Valid σ ∧ FinSupp σ ∧ rkC σ = r ∧ zsC σ = ν}

theorem valid_triv : Valid triv := fun _ _ => rfl

theorem finSupp_triv : FinSupp triv := ⟨0, triv_trivFrom⟩

theorem rkC_triv : rkC triv = 0 := by
  unfold rkC; rw [stable_rk.cut_eq triv_trivFrom]; simp [rk]

theorem zsC_triv : zsC triv = 0 := by
  unfold zsC; rw [stable_zs.cut_eq triv_trivFrom]; simp [zs]

theorem eq_triv_of_rkC_zero {σ : OddSymbol} (hV : Valid σ) (hF : FinSupp σ) (h : rkC σ = 0) : σ = triv := by
  funext k
  apply triv_of_dim_zero hV
  by_cases hk : k < cut σ
  · exact (Finset.sum_eq_zero_iff.1 (show rk σ (cut σ) = 0 from h)) k (Finset.mem_range.2 hk)
  · exact (trivFrom_cut hF).dim (not_lt.1 hk)

theorem symSet_zero_subset (ν : ℕ) : symSet 0 ν ⊆ {triv} := fun _ hσ => eq_triv_of_rkC_zero hσ.1 hσ.2.1 hσ.2.2.1

theorem symSet_cons_iff (f : OddFactor) (σ : OddSymbol) (r ν : ℕ) :
    consS f σ ∈ symSet r ν ↔ (f.dim = 0 → f.sign = Sign.plus) ∧ Valid σ ∧ FinSupp σ ∧
      f.dim + rkC σ = r ∧ zsC σ + rkC σ = ν := by
  constructor
  · rintro ⟨hV, hF, hr, hz⟩
    have hF' := (finSupp_cons f).1 hF
    rw [rkC_cons hF'] at hr
    rw [zsC_cons hF'] at hz
    obtain ⟨h0, hV'⟩ := (valid_cons f).1 hV
    exact ⟨h0, hV', hF', hr, hz⟩
  · rintro ⟨h0, hV', hF', hr, hz⟩
    refine ⟨(valid_cons f).2 ⟨h0, hV'⟩, (finSupp_cons f).2 hF', ?_, ?_⟩
    · rw [rkC_cons hF']; exact hr
    · rw [zsC_cons hF']; exact hz

/-- The index set of the first factors: $(d, \varepsilon)$ with $d \le r$, $r - d \le \nu$, a zero-dimensional
factor having sign $+$, and satisfying the predicate $Q$. -/
noncomputable def Jq (Q : OddFactor → Prop) (r ν : ℕ) : Finset (ℕ × Sign) :=
  open Classical in
  ((Finset.range (r + 1) ×ˢ ({Sign.plus, Sign.minus} : Finset Sign)).filter
    fun x => (x.1 = 0 → x.2 = Sign.plus) ∧ r - x.1 ≤ ν ∧ Q ⟨x.1, x.2⟩)

theorem mem_Jq {Q : OddFactor → Prop} {r ν : ℕ} {x : ℕ × Sign} :
    x ∈ Jq Q r ν ↔ x.1 ≤ r ∧ (x.1 = 0 → x.2 = Sign.plus) ∧ r - x.1 ≤ ν ∧ Q ⟨x.1, x.2⟩ := by
  classical
  unfold Jq
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  have h2 : x.2 ∈ ({Sign.plus, Sign.minus} : Finset Sign) := by cases x.2 <;> simp
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4, h5⟩
    exact ⟨by omega, h3, h4, h5⟩
  · rintro ⟨h1, h3, h4, h5⟩
    exact ⟨⟨by omega, h2⟩, h3, h4, h5⟩

/-- **Peeling the scale-$0$ factor off the symbols with a prescribed first factor.** -/
theorem symSetQ_eq (Q : OddFactor → Prop) (r ν : ℕ) :
    {σ | σ ∈ symSet r ν ∧ Q (σ 0)} =
      ⋃ x ∈ (Jq Q r ν : Set (ℕ × Sign)), consS ⟨x.1, x.2⟩ '' symSet (r - x.1) (ν - (r - x.1)) := by
  ext σ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Finset.mem_coe, exists_prop]
  have key : σ ∈ symSet r ν ↔ consS (σ 0) (shiftS σ) ∈ symSet r ν := by rw [consS_shiftS]
  constructor
  · rintro ⟨hσ, hQ⟩
    obtain ⟨h0, hVs, hFs, hr, hz⟩ := (symSet_cons_iff _ _ _ _).1 (key.1 hσ)
    refine ⟨((σ 0).dim, (σ 0).sign), mem_Jq.2 ⟨by omega, h0, by omega, hQ⟩, shiftS σ,
      ⟨hVs, hFs, by (try simp only); omega, by (try simp only); omega⟩, consS_shiftS σ⟩
  · rintro ⟨x, hx, σ', ⟨hV, hF, hr, hz⟩, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_Jq.1 hx
    refine ⟨(symSet_cons_iff _ _ _ _).2 ⟨h2, hV, hF, by (try simp only); omega, by (try simp only); omega⟩, h4⟩

theorem symSet_finite (r ν : ℕ) : (symSet r ν).Finite := by
  have key : ∀ n r ν, r + ν = n → (symSet r ν).Finite := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro r ν hn
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · exact (Set.finite_singleton triv).subset (symSet_zero_subset ν)
      · have h := symSetQ_eq (fun _ => True) r ν
        rw [show {σ | σ ∈ symSet r ν ∧ True} = symSet r ν from by ext; simp] at h
        rw [h]
        refine (Finset.finite_toSet _).biUnion fun x hx => (ih _ ?_ _ _ rfl).image _
        obtain ⟨h1, h2, h3, h4⟩ := mem_Jq.1 hx
        omega
  exact key _ r ν rfl

theorem consS_injective (f : OddFactor) : Function.Injective (consS f) := fun _ _ h => (consS_inj h).2

/-- The sum over the symbols with first factor satisfying `Q`, as a sum over the first factors. -/
theorem finsum_symSetQ (Q : OddFactor → Prop) (F : OddSymbol → ℝ) (r ν : ℕ) :
    ∑ᶠ σ ∈ {σ | σ ∈ symSet r ν ∧ Q (σ 0)}, F σ =
      ∑ x ∈ Jq Q r ν, ∑ᶠ σ' ∈ symSet (r - x.1) (ν - (r - x.1)), F (consS ⟨x.1, x.2⟩ σ') := by
  rw [symSetQ_eq, finsum_mem_biUnion, finsum_mem_coe_finset (fun x => ∑ᶠ j ∈ consS ⟨x.1, x.2⟩ ''
    symSet (r - x.1) (ν - (r - x.1)), F j) (Jq Q r ν)]
  · refine Finset.sum_congr rfl fun x _ => ?_
    exact finsum_mem_image (fun _ _ _ _ h => consS_injective _ h)
  · intro x _ y _ hxy
    refine Set.disjoint_left.2 ?_
    rintro σ ⟨σ₁, _, rfl⟩ ⟨σ₂, _, h⟩
    obtain ⟨hf, -⟩ := consS_inj h
    exact hxy (Prod.ext (by simpa using (congrArg OddFactor.dim hf).symm) (by simpa using (congrArg OddFactor.sign hf).symm))
  · exact Finset.finite_toSet _
  · intro x _
    exact (symSet_finite _ _).image _


/-! ### The generating series and the rationality theorem -/

section Series

variable (M : ℕ → Sign → ℝ) (a : ℕ → ℝ)

/-- **The coefficient of $X^\nu$** of the generating series of rank $r$ and observable $\varphi$ (a function of the
state): $\sum\varphi(\mathrm{state}(\sigma))\,\mathrm{wt}(\sigma)$ over the valid symbols $\sigma$ of finite support with
$\sum n_k = r$, $\sum kn_k = \nu$, whose first factor satisfies $Q$. -/
noncomputable def coef (Q : OddFactor → Prop) (φ : State → ℝ) (r ν : ℕ) : ℝ :=
  ∑ᶠ σ ∈ {σ | σ ∈ symSet r ν ∧ Q (σ 0)}, φ (statC σ) * wtC M a σ

/-- **The generating series** $\sum_\nu\mathrm{coef}\,X^\nu$. -/
noncomputable def ser (Q : OddFactor → Prop) (φ : State → ℝ) (r : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (coef M a Q φ r)

variable {M a}

theorem coef_peel (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) (Q : OddFactor → Prop) (φ : State → ℝ) (r ν : ℕ) :
    coef M a Q φ r ν = ∑ x ∈ Jq Q r ν, M x.1 x.2 * a (r - x.1) *
      coef M a (fun _ => True) (fun s => φ (step ⟨x.1, x.2⟩ s)) (r - x.1) (ν - (r - x.1)) := by
  unfold coef
  rw [finsum_symSetQ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show {σ | σ ∈ symSet (r - x.1) (ν - (r - x.1)) ∧ True} = symSet (r - x.1) (ν - (r - x.1)) from by
    ext; simp, mul_finsum_mem]
  refine finsum_mem_congr rfl fun σ' hσ' => ?_
  obtain ⟨hV, hF, hr, hz⟩ := hσ'
  rw [statC_cons hF, wtC_cons M a hM ha hF, hr]
  ring

theorem Jq_true_eq (Q : OddFactor → Prop) (r ν : ℕ) : Jq Q r ν = (Jq Q r r).filter fun x => r - x.1 ≤ ν := by
  classical
  ext x
  rw [Finset.mem_filter, mem_Jq, mem_Jq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, by omega, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2, _, h4⟩, h3⟩
    exact ⟨h1, h2, h3, h4⟩

theorem ser_peel (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) (Q : OddFactor → Prop) (φ : State → ℝ) (r : ℕ) :
    ser M a Q φ r = ∑ x ∈ Jq Q r r, PowerSeries.C (M x.1 x.2 * a (r - x.1)) * PowerSeries.X ^ (r - x.1) *
      ser M a (fun _ => True) (fun s => φ (step ⟨x.1, x.2⟩ s)) (r - x.1) := by
  classical
  ext ν
  rw [ser, PowerSeries.coeff_mk, coef_peel hM ha, map_sum, Jq_true_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc (PowerSeries.C _), PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs with h1
  · rw [ser, PowerSeries.coeff_mk]
  · simp

theorem Jq_true_split (r : ℕ) :
    Jq (fun _ => True) r r = insert (0, Sign.plus) (Jq (fun f => 1 ≤ f.dim) r r) := by
  ext x
  rw [Finset.mem_insert, mem_Jq, mem_Jq]
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    by_cases h0 : x.1 = 0
    · left; exact Prod.ext h0 (h2 h0)
    · right; exact ⟨h1, h2, h3, by simp only; omega⟩
  · rintro (rfl | ⟨h1, h2, h3, -⟩)
    · exact ⟨by simp, by simp, by simp, trivial⟩
    · exact ⟨h1, h2, h3, trivial⟩

theorem zero_notMem_Jq_pos (r : ℕ) : (0, Sign.plus) ∉ Jq (fun f => 1 ≤ f.dim) r r := by
  intro h
  have := (mem_Jq.1 h).2.2.2
  simp at this

/-- **The recursion** (peeling the scale-$0$ factor): $S_r[\varphi] = a_rX^r\,S_r[\varphi\circ\mathrm{swap}] +
P_r[\varphi]$, $P_r$ the series of the symbols with $n_0 \ge 1$. -/
theorem ser_split (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) (φ : State → ℝ) (r : ℕ) :
    ser M a (fun _ => True) φ r = PowerSeries.C (a r) * PowerSeries.X ^ r *
        ser M a (fun _ => True) (fun s => φ (swapS s)) r +
      ser M a (fun f => 1 ≤ f.dim) φ r := by
  rw [ser_peel hM ha (fun _ => True), Jq_true_split, Finset.sum_insert (zero_notMem_Jq_pos r),
    ser_peel hM ha (fun f => 1 ≤ f.dim)]
  congr 1
  simp only [Nat.sub_zero, hM, one_mul]
  have : (fun s => φ (step ⟨(0, Sign.plus).1, (0, Sign.plus).2⟩ s)) = fun s => φ (swapS s) := by
    funext s
    have := congrFun step_trivial s
    simp only [OddFactor.trivial] at this
    simp only [this]
  rw [this]

theorem coef_zero (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) (φ : State → ℝ) (ν : ℕ) :
    coef M a (fun _ => True) φ 0 ν = if ν = 0 then φ (statC triv) else 0 := by
  unfold coef
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · rw [if_pos rfl, show {σ | σ ∈ symSet 0 0 ∧ True} = {triv} from ?_, finsum_mem_singleton]
    · have : wtC M a triv = 1 := by
        unfold wtC
        rw [(stable_wtN M a hM ha).cut_eq triv_trivFrom]
        rfl
      rw [this, mul_one]
    · ext σ
      simp only [Set.mem_setOf_eq, and_true, Set.mem_singleton_iff]
      exact ⟨fun h => symSet_zero_subset 0 h, fun h => h ▸ ⟨valid_triv, finSupp_triv, rkC_triv, zsC_triv⟩⟩
  · rw [if_neg hν.ne', show {σ | σ ∈ symSet 0 ν ∧ True} = ∅ from ?_, finsum_mem_empty]
    ext σ
    simp only [Set.mem_setOf_eq, and_true, Set.mem_empty_iff_false, iff_false]
    intro h
    have := symSet_zero_subset ν h
    rw [Set.mem_singleton_iff.1 this] at h
    exact hν.ne' (h.2.2.2.symm.trans zsC_triv)

theorem ser_zero (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) (φ : State → ℝ) :
    ser M a (fun _ => True) φ 0 = PowerSeries.C (φ (statC triv)) := by
  ext ν
  rw [ser, PowerSeries.coeff_mk, coef_zero hM ha, PowerSeries.coeff_C]

/-- **Rationality of the primitive part**, given the rationality in smaller rank. -/
theorem ratP_of_lt (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) (r : ℕ)
    (ih : ∀ r' < r, ∀ φ : State → ℝ, RatSeries (ser M a (fun _ => True) φ r')) (φ : State → ℝ) :
    RatSeries (ser M a (fun f => 1 ≤ f.dim) φ r) := by
  rw [ser_peel hM ha]
  refine RatSeries.sum _ _ fun x hx => ?_
  obtain ⟨h1, h2, h3, h4⟩ := mem_Jq.1 hx
  have h4' : 1 ≤ x.1 := h4
  exact RatSeries.CXpowMul _ _ (ih (r - x.1) (by omega) _)

/-- **Theorem (rationality of the generating series of symbols).**  For every factor weight $M$ with
$M(0,+) = 1$, every gap weight $a$ with $a_0 = 1$, every rank $r$ and every function $\varphi$ of the state
$(E, O, d_e, d_o)$, the series $\sum_\nu\bigl(\sum_{\sigma}\varphi(\mathrm{state}\,\sigma)\,\mathrm{wt}(\sigma)\bigr)X^\nu$ over
the valid symbols of rank $r$ and weighted scale $\nu$ is a rational function of $X$. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (combinatorial core: rationality of the symbol series, odd p)"]
theorem ratS (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) :
    ∀ (r : ℕ) (φ : State → ℝ), RatSeries (ser M a (fun _ => True) φ r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro φ
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [ser_zero hM ha]; exact RatSeries.const _
    · have hP := ratP_of_lt hM ha r ih
      have h1 := ser_split hM ha φ r
      have h2 := ser_split hM ha (fun s => φ (swapS s)) r
      simp only [swapS_swapS] at h2
      set S := ser M a (fun _ => True) φ r
      set S' := ser M a (fun _ => True) (fun s => φ (swapS s)) r
      set W : Polynomial ℝ := 1 - Polynomial.C (a r ^ 2) * Polynomial.X ^ (2 * r)
      have hW : W.coeff 0 ≠ 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        simp [W, show 2 * r ≠ 0 from by omega]
      refine RatSeries.of_mul W hW ?_ ((hP φ).add (RatSeries.CXpowMul (a r) r (hP (fun s => φ (swapS s)))))
      simp only [W, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X, map_pow]
      linear_combination h1 + (PowerSeries.C (a r) * PowerSeries.X ^ r) * h2

/-- **Rationality of the primitive part** ($n_0 \ge 1$), every rank, every observable of the state. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (combinatorial core: primitive part, odd p)"]
theorem rat_Pn (hM : M 0 Sign.plus = 1) (ha : a 0 = 1) (r : ℕ) (φ : State → ℝ) :
    RatSeries (ser M a (fun f => 1 ≤ f.dim) φ r) :=
  ratP_of_lt hM ha r (fun r' _ => ratS hM ha r') φ

end Series


end QuadFormsKB.Hanke2011Structure.RatOdd
