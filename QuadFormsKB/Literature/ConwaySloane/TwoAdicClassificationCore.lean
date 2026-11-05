/-
# Conway–Sloane, Ch. 15, Theorem 10: the printed conditions are O'Meara's conditions 93:29 (on symbols)

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.5, Thm. 10, p. 381
(`conwaysloane1999`); O. T. O'Meara, *Introduction to Quadratic Forms*, §93G, 93:29, p. 277 (`omeara1963`).

This file is the combinatorial core of the proof of Theorem 10 for forms (`TwoAdicClassification.lean`). For a block
decomposition with 2-adic symbol $\sigma$ the lattice computations of `TwoAdicClassificationLattice.lean` express
O'Meara's conditions (i), (ii) of 93:29, for consecutive Jordan components $2^k$, $2^{k'}$ (the nonzero-dimensional
scales), through two prefix quantities of the symbol:
* `unitPre σ (k + 1)`: the unit part modulo 8 of the determinant of $f_1 \perp f_2 \perp \cdots \perp f_{2^k}$; the unit
  part of $\det f_q$ is the unit $\equiv 1 + t_q - n_q \pmod 4$ with $\left(\frac{\cdot}{2}\right) = \varepsilon_q$
  (`unitOf`);
* `oddPre σ (k + 1)`: the oddity of a diagonalization over $\mathbb Q_2$ of the same form, $\sum_{q \le 2^k}
  (t_q + 4[\,q = 2^{\mathrm{odd}},\ \varepsilon_q = -1\,])$.
With $\delta_q = 0$ (type I) or $1$ (type II), $m = k' - k + \delta_{2^k} + \delta_{2^{k'}}$ and $u = k + \delta_{2^k}$,
condition (i) says that the two determinant units agree modulo $2^{\min(m, 3)}$, and condition (ii) (required when
$k' + \delta_{2^{k'}} \ge k + \delta_{2^k} + 2$) says $\mathrm{oddity}(f_{\le 2^k}) + \mathrm{oddity}\langle 2^uW\rangle =
\mathrm{oddity}(f'_{\le 2^k}) + 1$, $W$ the product of the two units (`OMPair`). Together with the equality of the
$\mathbb Q_2$-classes of the whole forms (the same determinant unit and oddity), these are `OMCond`.

**Proves** `theorem10Cond_iff_omCond`: for symbols with the same dimensions and types whose constituents satisfy the
existence conditions (32)–(35), the printed conditions (i), (ii) of Theorem 10 are equivalent to `OMCond`.

*Proof.* With $X(m)$ the difference of the prefix oddities and $Y(m)$ the number of sign differences below $2^m$,
Theorem 10 (ii) at a type II scale $2^m$ says $X(m) + 4mY(m) \equiv 0 \pmod 8$ (`prefix_sub_eq`). Between consecutive
nonzero-dimensional scales $2^k < 2^{k'}$ the quantities $X$, $Y$ are constant, the type II scales in $(2^k, 2^{k'}]$ are
the zero-dimensional ones and possibly $2^{k'}$, and if $2^k$ has type II the condition at $2^k$ gives
$X(k+1) = 4kY(k+1)$; the comparison with `OMPair` is then a finite check (`local_pair`).
-/
import QuadFormsKB.Literature.ConwaySloane.Existence
import QuadFormsKB.Literature.ConwaySloane.Theorem10

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### The prefix quantities -/

/-- The unit modulo 8 which is $\equiv 1 + a \pmod 4$ (for even $a$) and has $\left(\frac{\cdot}{2}\right) = (-1)^b$. -/
def unitOf (a b : ZMod 8) : ZMod 8 := (if 2 * a = 0 then 1 else 7) * (if 4 * b = 0 then 1 else 5)

/-- The indicator of a minus sign. -/
def signInd (s : Sign) : ZMod 8 := if s = .minus then 1 else 0

/-- The unit part modulo 8 of the determinant of a 2-adic constituent with invariants $n, \varepsilon, t$. -/
def cu (f : TwoFactor) : ZMod 8 := unitOf (f.oddity - f.dim) (signInd f.sign)

/-- **The determinant unit of a prefix**: the product of `cu` over the constituents of scales $2^j$, $j < m$. -/
def unitPre (σ : TwoSymbol) : ℕ → ZMod 8
  | 0 => 1
  | m + 1 => unitPre σ m * cu (σ m)

/-- The oddity of a diagonalization over $\mathbb Q_2$ of the constituent of scale $2^k$:
$t + 4[\,k \text{ odd},\ \varepsilon = -1\,]$. -/
def oddW (k : ℕ) (f : TwoFactor) : ZMod 8 := f.oddity + 4 * (k : ZMod 8) * signInd f.sign

/-- **The oddity of a prefix**: the sum of `oddW` over the constituents of scales $2^j$, $j < m$. -/
def oddPre (σ : TwoSymbol) : ℕ → ZMod 8
  | 0 => 0
  | m + 1 => oddPre σ m + oddW m (σ m)

/-- The oddity of the rank one form $\langle 2^u w\rangle$, $w$ a unit modulo 8:
$w + 4[\,u \text{ odd},\ w \equiv \pm 3\,]$. -/
def oddE (u w : ZMod 8) : ZMod 8 := w + 4 * u * (if w = 3 ∨ w = 5 then 1 else 0)

/-- $\delta = 0$ for type I, $1$ for type II: the norm of the constituent of scale $2^k$ is $2^{k + \delta}$. -/
def dlt (σ : TwoSymbol) (k : ℕ) : ℕ := if IsTypeI σ k then 0 else 1

/-- $2^k < 2^{k'}$ are consecutive nonzero-dimensional scales of $\sigma$. -/
def NextNZ (σ : TwoSymbol) (k k' : ℕ) : Prop :=
  k < k' ∧ (σ k).dim ≠ 0 ∧ (σ k').dim ≠ 0 ∧ ∀ j, k < j → j < k' → (σ j).dim = 0

/-- **O'Meara's conditions (i), (ii) of 93:29 for consecutive components $2^k$, $2^{k'}$**, in terms of the symbols:
(i) the determinant units of the prefixes agree modulo 4 if $m \ge 2$ and modulo 8 if $m \ge 3$; (ii) the oddity
equation when $\mathfrak n_{2^{k'}} \subseteq 4\mathfrak n_{2^k}$. -/
def OMPair (σ τ : TwoSymbol) (k k' : ℕ) : Prop :=
  (2 ≤ k' - k + dlt σ k + dlt σ k' → 2 * (unitPre σ (k + 1) - unitPre τ (k + 1)) = 0) ∧
  (3 ≤ k' - k + dlt σ k + dlt σ k' → unitPre σ (k + 1) = unitPre τ (k + 1)) ∧
  (k + dlt σ k + 2 ≤ k' + dlt σ k' →
    oddPre σ (k + 1) + oddE ((k + dlt σ k : ℕ) : ZMod 8) (unitPre σ (k + 1) * unitPre τ (k + 1)) =
      oddPre τ (k + 1) + 1)

/-- **O'Meara's conditions on symbols**: `OMPair` for all consecutive nonzero-dimensional scales, and the same
determinant unit and oddity of the whole forms (the forms are equivalent over $\mathbb Q_2$). -/
def OMCond (σ τ : TwoSymbol) (N : ℕ) : Prop :=
  (∀ k k', NextNZ σ k k' → OMPair σ τ k k') ∧ unitPre σ N = unitPre τ N ∧ oddPre σ N = oddPre τ N

/-! ### Finite checks -/

theorem unitOf_sq (a b : ZMod 8) : unitOf a b * unitOf a b = 1 := by
  revert a b; decide

theorem unitOf_mul (a a' b b' : ZMod 8) :
    unitOf (2 * a) b * unitOf (2 * a') b' = unitOf (2 * a + 2 * a') (b + b') := by
  revert a a' b b'; decide

theorem unitOf_add_four (a c b : ZMod 8) : unitOf (a + 4 * c) b = unitOf a b := by
  revert a c b; decide

theorem unitOf_zero_eq_one_iff (b : ZMod 8) : unitOf 0 b = 1 ↔ 4 * b = 0 := by
  revert b; decide

theorem exists_two_mul_sub (t : ZMod 8) : ∃ c : ZMod 8, t - ((t.val % 2 : ℕ) : ZMod 8) = 2 * c := by
  revert t; decide

theorem natCast_eq_mod_two_add (n : ℕ) : (n : ZMod 8) = ((n % 2 : ℕ) : ZMod 8) + 2 * ((n / 2 : ℕ) : ZMod 8) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  push_cast; ring

/-- An oddity $t \equiv n \pmod 2$ differs from $n$ by an even residue. -/
theorem exists_sub_eq_two_mul {t : ZMod 8} {n : ℕ} (h : t.val % 2 = n % 2) : ∃ c : ZMod 8, t - n = 2 * c := by
  obtain ⟨c, hc⟩ := exists_two_mul_sub t
  refine ⟨c - ((n / 2 : ℕ) : ZMod 8), ?_⟩
  rw [natCast_eq_mod_two_add n, ← h]
  linear_combination hc

/-- The local comparison for a pair of consecutive nonzero-dimensional scales $2^k < 2^{k'}$: `gk` $= k' - k$,
`δ`, `δ'` their types (`dlt`), `kz` the residue of $k$, $2c = X(k+1)$, $Y = Y(k+1)$. The left side is `OMPair`, the
right side Theorem 10 (ii) at the type II scales $2^{k+1}$, $2^{k+2}$ when they lie in $(2^k, 2^{k'}]$. -/
def LocalStmt (c Y kz : ZMod 8) (gk δ δ' : ℕ) : Prop :=
  ((2 ≤ gk + δ + δ' → 2 * (unitOf (2 * c) Y - 1) = 0) ∧ (3 ≤ gk + δ + δ' → unitOf (2 * c) Y = 1) ∧
    (δ + 2 ≤ gk + δ' → 2 * c = 1 - oddE (kz + δ) (unitOf (2 * c) Y))) ↔
  (((2 ≤ gk ∨ δ' = 1) → 2 * c + 4 * (kz + 1) * Y = 0) ∧
    ((3 ≤ gk ∨ (gk = 2 ∧ δ' = 1)) → 2 * c + 4 * (kz + 2) * Y = 0))

instance (c Y kz : ZMod 8) (gk δ δ' : ℕ) : Decidable (LocalStmt c Y kz gk δ δ') := by
  unfold LocalStmt; infer_instance

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
theorem localStmt_check : ∀ c Y : ZMod 8, ∀ kb : Bool, ∀ gk < 4, ∀ δ < 2, ∀ δ' < 2, 1 ≤ gk →
    (δ = 1 → 2 * c = 4 * (if kb then 1 else 0) * Y) → LocalStmt c Y (if kb then 1 else 0) gk δ δ' := by
  decide

theorem localStmt_congr {c Y kz kz' : ZMod 8} {gk δ δ' : ℕ} (h : 4 * kz = 4 * kz') :
    LocalStmt c Y kz gk δ δ' ↔ LocalStmt c Y kz' gk δ δ' := by
  have e1 : 4 * (kz + 1) * Y = 4 * (kz' + 1) * Y := by linear_combination Y * h
  have e2 : 4 * (kz + 2) * Y = 4 * (kz' + 2) * Y := by linear_combination Y * h
  have e3 : ∀ w, oddE (kz + δ) w = oddE (kz' + δ) w := fun w => by
    unfold oddE; linear_combination (if w = 3 ∨ w = 5 then 1 else 0 : ZMod 8) * h
  unfold LocalStmt; rw [e1, e2, e3]

theorem localStmt_min {c Y kz : ZMod 8} {gk δ δ' : ℕ} (h3 : 3 ≤ gk) (hδ : δ ≤ 1) :
    LocalStmt c Y kz gk δ δ' ↔ LocalStmt c Y kz 3 δ δ' := by
  unfold LocalStmt
  simp only [show 2 ≤ gk + δ + δ' by omega, show 3 ≤ gk + δ + δ' by omega, show 2 ≤ gk ∨ δ' = 1 by omega,
    show 3 ≤ gk ∨ (gk = 2 ∧ δ' = 1) by omega, show δ + 2 ≤ gk + δ' by omega, show 2 ≤ 3 + δ + δ' by omega,
    show 3 ≤ 3 + δ + δ' by omega, show 2 ≤ 3 ∨ δ' = 1 by omega, show 3 ≤ 3 ∨ (3 = 2 ∧ δ' = 1) by omega,
    show δ + 2 ≤ 3 + δ' by omega, true_implies]

theorem four_mul_natCast_mod_two (k : ℕ) :
    4 * (k : ZMod 8) = 4 * (if k % 2 = 1 then 1 else 0) := by
  rw [natCast_eq_mod_two_add k]
  have h8 : (8 : ZMod 8) = 0 := by decide
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp only [h] <;>
    · push_cast; linear_combination ((k / 2 : ℕ) : ZMod 8) * h8

/-- **The local comparison**, for natural parameters. -/
theorem localStmt_of {c Y : ZMod 8} {k gk δ δ' : ℕ} (hg : 1 ≤ gk) (hδ : δ ≤ 1) (hδ' : δ' ≤ 1)
    (hcar : δ = 1 → 2 * c = 4 * (k : ZMod 8) * Y) : LocalStmt c Y (k : ZMod 8) gk δ δ' := by
  have hk := four_mul_natCast_mod_two k
  rw [localStmt_congr hk]
  have hcar' : δ = 1 → 2 * c = 4 * (if k % 2 = 1 then 1 else 0) * Y := fun h => by rw [hcar h, hk]
  have key : ∀ g, 1 ≤ g → g < 4 → LocalStmt c Y (if k % 2 = 1 then 1 else 0) g δ δ' := by
    intro g hg1 hg4
    have := localStmt_check c Y (decide (k % 2 = 1)) g hg4 δ (by omega) δ' (by omega) hg1
    simp only [decide_eq_true_eq] at this
    exact this hcar'
  rcases Nat.lt_or_ge gk 4 with h | h
  · exact key gk hg h
  · rw [localStmt_min (by omega) hδ]; exact key 3 (by omega) (by omega)

/-! ### The prefix differences -/

/-- The difference $X(m)$ of the prefix oddities. -/
def oddDiff (σ τ : TwoSymbol) (m : ℕ) : ZMod 8 := oddPre σ m - oddPre τ m

/-- The number $Y(m)$ (modulo 8; only its parity matters) of minus signs of $\sigma$ and of $\tau$ below $2^m$. -/
def signCnt (σ τ : TwoSymbol) (m : ℕ) : ZMod 8 := (minusBelow σ m : ZMod 8) + minusBelow τ m

theorem minusBelow_succ_cast (ρ : TwoSymbol) (m : ℕ) :
    ((minusBelow ρ (m + 1) : ℕ) : ZMod 8) = minusBelow ρ m + signInd (ρ m).sign := by
  simp only [minusBelow, signInd, Nat.cast_add]
  split_ifs <;> simp

theorem signCnt_succ (σ τ : TwoSymbol) (m : ℕ) :
    signCnt σ τ (m + 1) = signCnt σ τ m + signInd (σ m).sign + signInd (τ m).sign := by
  unfold signCnt; rw [minusBelow_succ_cast, minusBelow_succ_cast]; ring

theorem oddDiff_succ (σ τ : TwoSymbol) (m : ℕ) :
    oddDiff σ τ (m + 1) = oddDiff σ τ m + oddW m (σ m) - oddW m (τ m) := by
  unfold oddDiff; simp only [oddPre]; ring

/-- **Theorem 10 (ii) in terms of $X$, $Y$**: the difference of the prefix invariants is $X(m) + 4mY(m)$. -/
theorem prefix_sub_eq (σ τ : TwoSymbol) : ∀ m : ℕ,
    prefixInvariant σ m - prefixInvariant τ m = oddDiff σ τ m + 4 * (m : ZMod 8) * signCnt σ τ m
  | 0 => by simp [prefixInvariant, oddDiff, oddPre, signCnt, minusBelow]
  | m + 1 => by
    have ih := prefix_sub_eq σ τ m
    rw [prefixInvariant_succ, prefixInvariant_succ, oddDiff_succ, signCnt_succ, minusBelow_succ_cast,
      minusBelow_succ_cast]
    unfold oddW signCnt at *
    have h8 : (8 : ZMod 8) = 0 := by decide
    push_cast
    linear_combination ih - ((minusBelow τ m : ZMod 8) + signInd (τ m).sign + m * signInd (σ m).sign) * h8

theorem unitPre_sq (σ : TwoSymbol) : ∀ m, unitPre σ m * unitPre σ m = 1
  | 0 => by simp [unitPre]
  | m + 1 => by
    have ih := unitPre_sq σ m
    have h := unitOf_sq ((σ m).oddity - (σ m).dim) (signInd (σ m).sign)
    simp only [unitPre, cu] at *
    linear_combination (unitOf ((σ m).oddity - (σ m).dim) (signInd (σ m).sign)) ^ 2 * ih + h

theorem type_eq_II_of_not {ρ : TwoSymbol} {k : ℕ} (h : ¬ IsTypeI ρ k) : (ρ k).type = .II := by
  unfold IsTypeI at h
  cases h' : (ρ k).type
  · exact absurd h' h
  · rfl

theorem typeII_of_dim_zero {ρ : TwoSymbol} (hρ : ∀ k, (ρ k).Exists) {k : ℕ} (h : (ρ k).dim = 0) : ¬ IsTypeI ρ k := by
  have := ((hρ k).1 h).1
  unfold IsTypeI; rw [this]; simp

theorem four_mul_natCast_of_parity {m k : ℕ} (h : m % 2 = k % 2) : 4 * (m : ZMod 8) = 4 * (k : ZMod 8) := by
  rw [four_mul_natCast_mod_two m, four_mul_natCast_mod_two k, h]

section Core

variable {σ τ : TwoSymbol} {N : ℕ} (hT : Theorem10Setting σ τ N) (hσ : ∀ k, (σ k).Exists)
  (hτ : ∀ k, (τ k).Exists)
include hT hσ hτ

theorem oddity_sub_dim (k : ℕ) :
    ∃ c c' : ZMod 8, (σ k).oddity - (σ k).dim = 2 * c ∧ (τ k).oddity - (σ k).dim = 2 * c' := by
  obtain ⟨c, hc⟩ := exists_sub_eq_two_mul (hσ k).2.2.2.1
  obtain ⟨c', hc'⟩ := exists_sub_eq_two_mul (hτ k).2.2.2.1
  rw [hT.dim_eq] at hc'
  exact ⟨c, c', hc, hc'⟩

theorem oddDiff_even : ∀ m, ∃ x : ZMod 8, oddDiff σ τ m = 2 * x
  | 0 => ⟨0, by simp [oddDiff, oddPre]⟩
  | m + 1 => by
    obtain ⟨x, hx⟩ := oddDiff_even m
    obtain ⟨c, c', hc, hc'⟩ := oddity_sub_dim hT hσ hτ m
    refine ⟨x + c - c' + 2 * m * (signInd (σ m).sign - signInd (τ m).sign), ?_⟩
    rw [oddDiff_succ, hx]; unfold oddW
    linear_combination hc - hc'

/-- **The product of the two determinant units** is the unit determined by $X$ and $Y$. -/
theorem unitPre_mul_eq : ∀ m, unitPre σ m * unitPre τ m = unitOf (oddDiff σ τ m) (signCnt σ τ m)
  | 0 => by
    simp only [unitPre, oddDiff, oddPre, signCnt, minusBelow]
    decide
  | m + 1 => by
    have ih := unitPre_mul_eq m
    obtain ⟨x, hx⟩ := oddDiff_even hT hσ hτ m
    obtain ⟨c, c', hc, hc'⟩ := oddity_sub_dim hT hσ hτ m
    have hcσ : cu (σ m) = unitOf (2 * c) (signInd (σ m).sign) := by unfold cu; rw [hc]
    have hcτ : cu (τ m) = unitOf (2 * c') (signInd (τ m).sign) := by unfold cu; rw [hT.dim_eq m, hc']
    have hXs : oddDiff σ τ (m + 1) =
        2 * x + 2 * c + 2 * c' + 4 * (-c' + m * (signInd (σ m).sign - signInd (τ m).sign)) := by
      rw [oddDiff_succ, hx]; unfold oddW; linear_combination hc - hc'
    calc unitPre σ (m + 1) * unitPre τ (m + 1)
        = (unitPre σ m * unitPre τ m) * cu (σ m) * cu (τ m) := by simp only [unitPre]; ring
      _ = unitOf (2 * x) (signCnt σ τ m) * unitOf (2 * c) (signInd (σ m).sign) *
            unitOf (2 * c') (signInd (τ m).sign) := by rw [unitPre_mul_eq m, hx, hcσ, hcτ]
      _ = unitOf (2 * (x + c) + 2 * c') (signCnt σ τ m + signInd (σ m).sign + signInd (τ m).sign) := by
        rw [unitOf_mul, show 2 * x + 2 * c = 2 * (x + c) by ring, unitOf_mul]
      _ = unitOf (oddDiff σ τ (m + 1)) (signCnt σ τ (m + 1)) := by
        rw [hXs, signCnt_succ, unitOf_add_four]; ring_nf

/-- Across a zero-dimensional scale $X$ and $Y$ do not change. -/
theorem step_dim_zero {j : ℕ} (h : (σ j).dim = 0) :
    oddDiff σ τ (j + 1) = oddDiff σ τ j ∧ signCnt σ τ (j + 1) = signCnt σ τ j := by
  have hτ0 : (τ j).dim = 0 := by rw [hT.dim_eq]; exact h
  obtain ⟨hIIσ, hsσ⟩ := (hσ j).1 h
  obtain ⟨hIIτ, hsτ⟩ := (hτ j).1 hτ0
  have hoσ := (hσ j).2.2.2.2 hIIσ
  have hoτ := (hτ j).2.2.2.2 hIIτ
  rw [oddDiff_succ, signCnt_succ]
  unfold oddW signInd
  simp [hoσ, hoτ, hsσ, hsτ]

theorem const_of_dim_zero {a b : ℕ} (hab : a ≤ b) (h : ∀ j, a ≤ j → j < b → (σ j).dim = 0) :
    oddDiff σ τ b = oddDiff σ τ a ∧ signCnt σ τ b = signCnt σ τ a := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ b hab ih =>
    obtain ⟨e1, e2⟩ := ih (fun j h1 h2 => h j h1 (by omega))
    obtain ⟨f1, f2⟩ := step_dim_zero hT hσ hτ (h b hab (by omega))
    exact ⟨f1.trans e1, f2.trans e2⟩

/-- **The carry**: if $2^k$ has type II and Theorem 10 (ii) holds at $2^k$, then $X(k+1) = 4kY(k+1)$. -/
theorem carry {k : ℕ} (hk : ¬ IsTypeI σ k)
    (h : oddDiff σ τ k + 4 * (k : ZMod 8) * signCnt σ τ k = 0) :
    oddDiff σ τ (k + 1) = 4 * (k : ZMod 8) * signCnt σ τ (k + 1) := by
  have hkτ : ¬ IsTypeI τ k := (hT.isTypeI_iff k).not.mpr hk
  have hoσ : (σ k).oddity = 0 := (hσ k).2.2.2.2 (type_eq_II_of_not hk)
  have hoτ : (τ k).oddity = 0 := (hτ k).2.2.2.2 (type_eq_II_of_not hkτ)
  rw [oddDiff_succ, signCnt_succ]
  unfold oddW
  rw [hoσ, hoτ]
  have h8 : (8 : ZMod 8) = 0 := by decide
  linear_combination h - (k * signCnt σ τ k + k * signInd (τ k).sign) * h8

/-- **The pair comparison**: for consecutive nonzero-dimensional scales $2^k < 2^{k'}$ (with the carry when $2^k$ has
type II), `OMPair` holds iff Theorem 10 (ii) holds at the type II scales $2^{k+1}$, $2^{k+2}$ lying in $(2^k, 2^{k'}]$. -/
theorem omPair_iff {k k' : ℕ} (hk : NextNZ σ k k')
    (hcar : ¬ IsTypeI σ k → oddDiff σ τ (k + 1) = 4 * (k : ZMod 8) * signCnt σ τ (k + 1)) :
    OMPair σ τ k k' ↔
      ((2 ≤ k' - k ∨ dlt σ k' = 1) →
          oddDiff σ τ (k + 1) + 4 * ((k : ZMod 8) + 1) * signCnt σ τ (k + 1) = 0) ∧
        ((3 ≤ k' - k ∨ (k' - k = 2 ∧ dlt σ k' = 1)) →
          oddDiff σ τ (k + 1) + 4 * ((k : ZMod 8) + 2) * signCnt σ τ (k + 1) = 0) := by
  obtain ⟨x, hx⟩ := oddDiff_even hT hσ hτ (k + 1)
  have hW := unitPre_mul_eq hT hσ hτ (k + 1)
  rw [hx] at hW
  have hsq := unitPre_sq τ (k + 1)
  have hX : oddPre σ (k + 1) - oddPre τ (k + 1) = 2 * x := hx
  set U := unitPre σ (k + 1)
  set U' := unitPre τ (k + 1)
  set Y := signCnt σ τ (k + 1)
  set W := unitOf (2 * x) Y
  have hUU : U = W * U' := by linear_combination U' * hW - U * hsq
  have e1 : 2 * (U - U') = 0 ↔ 2 * (W - 1) = 0 := by
    rw [hUU]
    constructor
    · intro h; linear_combination U' * h - 2 * (W - 1) * hsq
    · intro h; linear_combination U' * h
  have e2 : U = U' ↔ W = 1 := by
    rw [hUU]
    constructor
    · intro h; linear_combination U' * h - (W - 1) * hsq
    · intro h; rw [h, one_mul]
  have e3 : ∀ u w : ZMod 8, oddPre σ (k + 1) + oddE u w = oddPre τ (k + 1) + 1 ↔ 2 * x = 1 - oddE u w := by
    intro u w
    constructor
    · intro h; linear_combination h - hX
    · intro h; linear_combination hX + h
  have hd : dlt σ k ≤ 1 := by unfold dlt; split_ifs <;> omega
  have hd' : dlt σ k' ≤ 1 := by unfold dlt; split_ifs <;> omega
  have hcar' : dlt σ k = 1 → 2 * x = 4 * (k : ZMod 8) * Y := fun h => by
    have hII : ¬ IsTypeI σ k := fun hI => by simp [dlt, hI] at h
    rw [← hx]; exact hcar hII
  have L := localStmt_of (k := k) (gk := k' - k) (by have := hk.1; omega) hd hd' hcar'
  unfold LocalStmt at L
  unfold OMPair
  have r3 : (k + dlt σ k + 2 ≤ k' + dlt σ k') ↔ dlt σ k + 2 ≤ k' - k + dlt σ k' := by
    have := hk.1; omega
  rw [e1, e2, e3, hW, r3, hx, Nat.cast_add]
  exact L

/-- **Theorem 10's conditions are O'Meara's conditions** (on symbols): for 2-adic symbols with the same dimensions
and types, whose constituents satisfy the existence conditions (32)–(35) and vanish from the scale $2^N$ on, the
printed conditions (i), (ii) of Theorem 10 hold iff `OMCond` holds. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, Thm. 10, p. 381 (conditions (i), (ii) = O'Meara 93:29 (i), (ii))"]
theorem theorem10Cond_iff_omCond (hN : ∀ k, N ≤ k → (σ k).dim = 0) :
    Theorem10Cond σ τ N ↔ OMCond σ τ N := by
  rw [theorem10Cond_iff_prefix hT, four_mul_signDiffBelow]
  have hCS : (∀ m, ¬ IsTypeI σ m → prefixInvariant τ m = prefixInvariant σ m) ↔
      ∀ m, ¬ IsTypeI σ m → oddDiff σ τ m + 4 * (m : ZMod 8) * signCnt σ τ m = 0 := by
    refine forall_congr' fun m => imp_congr_right fun _ => ?_
    rw [← prefix_sub_eq, sub_eq_zero, eq_comm]
  have h4 : (4 * (minusBelow σ N : ZMod 8) + 4 * (minusBelow τ N : ZMod 8) = 0) ↔ 4 * signCnt σ τ N = 0 := by
    unfold signCnt; rw [mul_add]
  have hsq := unitPre_sq τ N
  have hglob : unitPre σ N = unitPre τ N ↔ unitPre σ N * unitPre τ N = 1 := by
    constructor
    · intro h; rw [h, hsq]
    · intro h; linear_combination unitPre τ N * h - unitPre σ N * hsq
  rw [hCS, h4]
  constructor
  · rintro ⟨hY, hP⟩
    have hXN : oddDiff σ τ N = 0 := by
      have := hP N (hT.typeII_of_le N le_rfl)
      linear_combination this - (N : ZMod 8) * hY
    refine ⟨fun k k' hk => ?_, ?_, ?_⟩
    · have hcar : ¬ IsTypeI σ k → oddDiff σ τ (k + 1) = 4 * (k : ZMod 8) * signCnt σ τ (k + 1) :=
        fun hII => carry hT hσ hτ hII (hP k hII)
      rw [omPair_iff hT hσ hτ hk hcar]
      have hkk := hk.1
      constructor
      · intro hc1
        have hII : ¬ IsTypeI σ (k + 1) := by
          by_cases h2 : 2 ≤ k' - k
          · exact typeII_of_dim_zero hσ (hk.2.2.2 (k + 1) (by omega) (by omega))
          · have hk' : k' = k + 1 := by omega
            have hd : dlt σ k' = 1 := hc1.resolve_left h2
            subst hk'
            intro hI; simp [dlt, hI] at hd
        have := hP (k + 1) hII
        push_cast at this
        exact this
      · intro hc2
        have hII : ¬ IsTypeI σ (k + 2) := by
          rcases Nat.lt_or_ge (k + 2) k' with h | h
          · exact typeII_of_dim_zero hσ (hk.2.2.2 (k + 2) (by omega) h)
          · rcases hc2 with h3 | ⟨h3, hd⟩
            · omega
            · have hk' : k' = k + 2 := by omega
              subst hk'
              intro hI; simp [dlt, hI] at hd
        have e := step_dim_zero hT hσ hτ (hk.2.2.2 (k + 1) (by omega) (by omega))
        have := hP (k + 2) hII
        rw [show k + 2 = (k + 1) + 1 from rfl, e.1, e.2] at this
        push_cast at this
        linear_combination this
    · rw [hglob, unitPre_mul_eq hT hσ hτ N, hXN, unitOf_zero_eq_one_iff]; exact hY
    · unfold oddDiff at hXN; exact sub_eq_zero.1 hXN
  · rintro ⟨hpairs, hU, hO⟩
    have hXN : oddDiff σ τ N = 0 := by unfold oddDiff; rw [hO, sub_self]
    have hY : 4 * signCnt σ τ N = 0 := by
      have := hglob.1 hU
      rwa [unitPre_mul_eq hT hσ hτ N, hXN, unitOf_zero_eq_one_iff] at this
    refine ⟨hY, ?_⟩
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm
    classical
    by_cases hex : ∃ j, j < m ∧ (σ j).dim ≠ 0
    · obtain ⟨j₀, hj₀, hj₀d⟩ := hex
      set k := Nat.findGreatest (fun j => (σ j).dim ≠ 0) (m - 1) with hk_def
      have hk_spec : (σ k).dim ≠ 0 := Nat.findGreatest_spec (P := fun j => (σ j).dim ≠ 0) (by omega) hj₀d
      have hk_lt : k < m := by have := Nat.findGreatest_le (P := fun j => (σ j).dim ≠ 0) (m - 1); omega
      have hk_max : ∀ j, k < j → j < m → (σ j).dim = 0 := fun j h1 h2 => by
        by_contra hne
        exact Nat.findGreatest_is_greatest (P := fun j => (σ j).dim ≠ 0) h1 (by omega) hne
      have hcar : ¬ IsTypeI σ k → oddDiff σ τ (k + 1) = 4 * (k : ZMod 8) * signCnt σ τ (k + 1) :=
        fun hII => carry hT hσ hτ hII (ih k hk_lt hII)
      have hconst := const_of_dim_zero hT hσ hτ (a := k + 1) (b := m) (by omega)
        (fun j h1 h2 => hk_max j (by omega) h2)
      by_cases hex' : ∃ j, m ≤ j ∧ (σ j).dim ≠ 0
      · rw [hconst.1, hconst.2]
        set k' := Nat.find hex' with hk'_def
        have hk'1 : m ≤ k' ∧ (σ k').dim ≠ 0 := Nat.find_spec hex'
        have hk'min : ∀ j, m ≤ j → j < k' → (σ j).dim = 0 := fun j h1 h2 => by
          by_contra hne
          exact Nat.find_min hex' h2 ⟨h1, hne⟩
        have hNZ : NextNZ σ k k' := ⟨by omega, hk_spec, hk'1.2, fun j h1 h2 =>
          if h : j < m then hk_max j h1 h else hk'min j (by omega) h2⟩
        have hpair := (omPair_iff hT hσ hτ hNZ hcar).1 (hpairs k k' hNZ)
        have hdm : m = k' → dlt σ k' = 1 := fun h => by
          rw [← h]; simp [dlt, hm]
        rcases Nat.even_or_odd (m - k) with ⟨j, hj⟩ | ⟨j, hj⟩
        · -- `m ≡ k + 2`
          have hc2 : 3 ≤ k' - k ∨ (k' - k = 2 ∧ dlt σ k' = 1) := by
            by_cases hkk : k' = k + 2
            · right; exact ⟨by omega, hdm (by omega)⟩
            · left; omega
          have h4m : 4 * (m : ZMod 8) = 4 * ((k : ZMod 8) + 2) := by
            have := four_mul_natCast_of_parity (m := m) (k := k + 2) (by omega)
            push_cast at this; exact this
          rw [h4m]; exact hpair.2 hc2
        · -- `m ≡ k + 1`
          have hc1 : 2 ≤ k' - k ∨ dlt σ k' = 1 := by
            by_cases hkk : k' = k + 1
            · right; exact hdm (by omega)
            · left; omega
          have h4m : 4 * (m : ZMod 8) = 4 * ((k : ZMod 8) + 1) := by
            have := four_mul_natCast_of_parity (m := m) (k := k + 1) (by omega)
            push_cast at this; exact this
          rw [h4m]; exact hpair.1 hc1
      · push Not at hex'
        have e1 := const_of_dim_zero hT hσ hτ (a := m) (b := max m N) (le_max_left _ _)
          (fun j h1 _ => hex' j h1)
        have e2 := const_of_dim_zero hT hσ hτ (a := N) (b := max m N) (le_max_right _ _)
          (fun j h1 _ => hN j h1)
        rw [← e1.1, ← e1.2, e2.1, e2.2, hXN]
        linear_combination (m : ZMod 8) * hY
    · push Not at hex
      have e := const_of_dim_zero hT hσ hτ (a := 0) (b := m) (Nat.zero_le m) (fun j _ h2 => hex j h2)
      rw [e.1, e.2]
      simp [oddDiff, oddPre, signCnt, minusBelow]

end Core

end QuadFormsKB.ConwaySloane
