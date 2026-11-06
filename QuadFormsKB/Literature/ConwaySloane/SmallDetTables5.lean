/-
# Conway–Sloane, Ch. 15, §8.1: Table 15.4, the rows $\lvert\det\rvert = 4$

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.1,
Theorem 12, Table 15.4 (p. 387) (`conwaysloane1999`).

For $\lvert\det\rvert = 4$ the 2-adic symbol lives on the scales $1, 2, 4$ with $\dim_1 + 2\dim_2 = 2$, i.e. either one
constituent of dimension $1$ at the scale $4$ (the rows $4_{\pm1}$, $4^{\pm1}$) or one of dimension $2$ at the scale $2$
(the rows $2^2_{\mathrm I}$, $2^{\pm2}_{\mathrm{II}}$). The odd-prime symbols are the unit symbols of `odd_unit`.

This file proves the *shape lemma* `two_shape4` (the data forced by the conditions) and the general existence theorem
`det4_exists_iff`: a system of symbols satisfying the conditions with $\lvert\det\rvert = 4$, signature $(r,s)$ and a
property `P` of the three constituents exists iff there are three constituents with these dimensions, existence
conditions, sign product and oddity formula and the property `P`.

**Covered rows (existence, with the book's signatures and exceptions, by `decide` on the first cases and a tail
argument `exists_stable`/`rhsA_tail`/`rhsB_tail` for large $n$):** all eight rows $\lvert\det\rvert = 4$:
$\mathrm I(4_{\pm1})$, $\mathrm{II}(4^{\pm1})$, $\mathrm I(2_{\mathrm I}^2)$, $\mathrm{II}(2_{\mathrm I}^2)$,
$\mathrm I(2_{\mathrm{II}}^2)$, $\mathrm{II}(2_{\mathrm{II}}^{\pm2})$ (`table154_four_*`). The rows with the sign $\pm$ of
the book ($4_{\pm1}$) are the two genera distinguished by the invariant $t + 4[\varepsilon = -] \in \{1, 7\}$ of the
compartment of the scale-4 constituent.

**Discrepancy with the printed table (found by computation).** For $\mathrm I_{r,s}(4_{\pm1})$ the book lists the
exceptions "$0, 1, 2_{\mp2}$". The conditions (29)–(35) also exclude $n = 3$ with signature $\mp3$: for the genus with
scale-4 invariant $1$ the signature $-3$ (mod 8) is impossible (a two-dimensional type I constituent with sign $+$ needs
$t \in \{0, \pm2\}$, with sign $-$ needs $t \in \{4, \pm2\}$, neither gives the required $t = \sigma - 1$ or
$\sigma - 5$), see `table154_four_I_plus`. This looks like an omitted exception $3_{\mp3}$ in the book.

**Not done here.** Uniqueness of each genus up to `MoveEquiv` for the $\pm4$ rows (the invariants of the moves are
determined by the data used here, but the proof was not carried out), the rows $\lvert\det\rvert = 8$ and Table 15.5.
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables3

namespace QuadFormsKB.ConwaySloane

open Finset

theorem signProd_eq_three (s : ℕ → Sign) (N : ℕ) (h3 : ∀ k, 3 ≤ k → s k = .plus)
    (hN : ∀ k, N ≤ k → s k = .plus) : signProd s N = signProd s 3 := by
  rcases le_total N 3 with h | h
  · exact (signProd_stable s h hN).symm
  · exact signProd_stable s h h3

/-- **The 2-adic symbol when $v_2(\det) = 2$**: only the scales $1, 2, 4$ occur, with $\dim_1 + 2\dim_2 = 2$; the
signs have product $\left(\frac{\det/4}{2}\right)$ and the oddity is $t_0 + t_1 + t_2 + 4[\varepsilon_1 = -]$ (the scale
$2$ is an odd power of $2$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (2-adic shape for |det| = 4)"]
theorem GenusSymbolData.two_shape4 (G : GenusSymbolData) (hc : G.Conditions) (hv2 : padicValInt 2 G.det = 2) :
    (∀ k, 3 ≤ k → G.two k = TwoFactor.trivial) ∧
      (G.two 1).dim + 2 * (G.two 2).dim = 2 ∧
      (G.two 0).dim + (G.two 1).dim + (G.two 2).dim = G.n ∧
      ((G.two 0).sign.mul (G.two 1).sign).mul (G.two 2).sign = jacobiTwo (G.det / 4) ∧
      G.two.oddity G.N = (G.two 0).oddity + (G.two 1).oddity + (G.two 2).oddity +
        4 * ind8 ((G.two 1).sign = .minus) ∧
      (G.two 0).Exists ∧ (G.two 1).Exists ∧ (G.two 2).Exists := by
  obtain ⟨hs, hsg⟩ := hc.two_det
  rw [hv2] at hs
  have hsupp := hc.two_supp
  have hex := hc.two_exists
  have d3 : ∀ k, 3 ≤ k → (G.two k).dim = 0 := by
    intro k hk
    by_cases hkN : k < G.N
    · have hle : k * (G.two k).dim ≤ ∑ k ∈ range G.N, k * (G.two k).dim :=
        Finset.single_le_sum (f := fun k => k * (G.two k).dim) (fun i _ => Nat.zero_le _) (mem_range.2 hkN)
      rw [hs] at hle
      by_contra hne
      have h1 : 1 ≤ (G.two k).dim := Nat.pos_of_ne_zero hne
      have := Nat.mul_le_mul hk h1
      omega
    · rw [hsupp k (not_lt.1 hkN)]; rfl
  have t3 : ∀ k, 3 ≤ k → G.two k = TwoFactor.trivial := by
    intro k hk
    obtain ⟨h32, -, -, -, hII⟩ := hex k
    have h1 : (G.two k).dim = 0 := d3 k hk
    obtain ⟨h2, h3⟩ := h32 h1
    have h4 : (G.two k).oddity = 0 := hII h2
    generalize G.two k = f at h1 h2 h3 h4
    obtain ⟨d, s, t, o⟩ := f
    dsimp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  have hsupN : ∀ k, G.N ≤ k → (G.two k).dim = 0 := fun k hk => by rw [hsupp k hk]; rfl
  refine ⟨t3, ?_, ?_, ?_, ?_, hex 0, hex 1, hex 2⟩
  · rw [sum_range_stable_nat (f := fun k => k * (G.two k).dim) (m := 3) (fun k hk => by simp [d3 k hk])
      (fun k hk => by simp [hsupN k hk])] at hs
    simpa [Finset.sum_range_succ] using hs
  · have h := hc.two_dim
    rw [sum_range_stable_nat (f := fun k => (G.two k).dim) (m := 3) (fun k hk => d3 k hk) hsupN] at h
    simpa [Finset.sum_range_succ] using h
  · rw [signProd_eq_three (fun k => (G.two k).sign) G.N
      (fun k hk => by simp [t3 k hk, TwoFactor.trivial])
      (fun k hk => by simp [hsupp k hk, TwoFactor.trivial]), hv2] at hsg
    simpa [signProd, Sign.plus_mul] using hsg
  · have hodd : G.two.oddity G.N = G.two.oddity 3 := by
      rcases le_total 3 G.N with h | h
      · exact TwoSymbol.oddity_congr (fun k hk => t3 k hk) h
      · exact (TwoSymbol.oddity_congr hsupp h).symm
    rw [hodd]
    unfold TwoSymbol.oddity
    have h2odd : ¬ Odd 2 := by decide
    simp [Finset.sum_range_succ, ind8, h2odd]
    ring

/-! ### Existence for $\lvert\det\rvert = 4$ -/

theorem natAbs_four (s : ℕ) : (4 * (-1 : ℤ) ^ s).natAbs = 4 := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem padicValInt_four_two (s : ℕ) : padicValInt 2 (4 * (-1 : ℤ) ^ s) = 2 := by
  simp only [padicValInt, natAbs_four]
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact padicValNat.prime_pow 2

theorem padicValInt_four_odd (q s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : padicValInt q (4 * (-1 : ℤ) ^ s) = 0 := by
  have : ¬ q ∣ 4 := by
    intro h
    have : q ∣ 2 ^ 2 := by simpa using h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow this))
  simp [padicValInt, natAbs_four, padicValNat.eq_zero_of_not_dvd this]

/-- **The system of symbols for $\lvert\det\rvert = 4$** with the three 2-adic constituents `c0 c1 c2` (scales
$1, 2, 4$) and unit symbols at the odd primes. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±4)"]
def dataTwo4 (r s : ℕ) (c0 c1 c2 : TwoFactor) : GenusSymbolData where
  n := r + s
  det := 4 * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q k => if k = 0 then ⟨r + s, Sign.ofInt (jacobiSym (4 * (-1) ^ s) q)⟩ else OddFactor.trivial
  two := fun k => if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else TwoFactor.trivial
  N := 3

theorem dataTwo4_conditions (r s : ℕ) (c0 c1 c2 : TwoFactor)
    (hn : c0.dim + c1.dim + c2.dim = r + s) (hdim : c1.dim + 2 * c2.dim = 2)
    (h0 : c0.Exists) (h1 : c1.Exists) (h2 : c2.Exists)
    (hsg : (c0.sign.mul c1.sign).mul c2.sign = .plus)
    (hsig : (r : ZMod 8) - s = c0.oddity + c1.oddity + c2.oddity + 4 * ind8 (c1.sign = .minus)) :
    (dataTwo4 r s c0 c1 c2).Conditions where
  ne_zero := mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp [dataTwo4, h.neg_one_pow, this]
    · simp [dataTwo4, h.neg_one_pow, h]
  odd_supp q k hk := by
    have hk' : 3 ≤ k := hk
    simp [dataTwo4, show k ≠ 0 by omega]
  two_supp k hk := by
    have hk' : 3 ≤ k := hk
    simp [dataTwo4, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
  odd_dim q _ _ := by simp [dataTwo4, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by
    simp [dataTwo4, Finset.sum_range_succ, TwoFactor.trivial]
    omega
  odd_det q hq hq2 := by
    refine ⟨?_, ?_⟩
    · simp [dataTwo4, padicValInt_four_odd q s hq hq2, Finset.sum_range_succ, OddFactor.trivial]
    · simp [dataTwo4, padicValInt_four_odd q s hq hq2, signProd, Sign.plus_mul, Sign.mul_plus,
        OddFactor.trivial]
  two_det := by
    refine ⟨?_, ?_⟩
    · simp [dataTwo4, padicValInt_four_two, Finset.sum_range_succ, TwoFactor.trivial]
      omega
    · have hd : (4 * (-1 : ℤ) ^ s) / 2 ^ 2 = (-1) ^ s := by simp
      simp [dataTwo4, padicValInt_four_two, signProd, hd, jacobiTwo_pm_one, Sign.plus_mul, Sign.mul_plus,
        TwoFactor.trivial]
      simpa [signProd, Sign.plus_mul] using hsg
  odd_exists q hq hq2 k := by
    by_cases hk : k = 0
    · subst hk
      simp only [dataTwo4, if_true]
      intro h0'
      have : r + s = 0 := h0'
      omega
    · simp [dataTwo4, hk, OddFactor.Exists, OddFactor.trivial]
  two_exists k := by
    by_cases hk : k = 0
    · subst hk; simpa [dataTwo4] using h0
    · by_cases hk1 : k = 1
      · subst hk1; simpa [dataTwo4] using h1
      · by_cases hk2 : k = 2
        · subst hk2; simpa [dataTwo4] using h2
        · simp only [dataTwo4, if_neg hk, if_neg hk1, if_neg hk2]
          decide
  oddity_formula := by
    have hna : (dataTwo4 r s c0 c1 c2).det.natAbs = 2 ^ 2 := by
      simp [dataTwo4, natAbs_four]
    rw [hna, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Finset.filter_singleton,
      if_neg (by norm_num), Finset.sum_empty, add_zero]
    simp [dataTwo4, GenusSymbolData.signature, TwoSymbol.oddity, Finset.sum_range_succ, TwoFactor.trivial,
      ind8] at hsig ⊢
    have h2odd : ¬ Odd 2 := by decide
    simp [h2odd]
    linear_combination hsig

/-- The constraints on the three 2-adic constituents of a system with $\lvert\det\rvert = 4$ and signature
$(r,s)$ (Conway–Sloane, §7.7 and §8.1). -/
def Constr4 (r s : ℕ) (c0 c1 c2 : TwoFactor) : Prop :=
  c0.dim + c1.dim + c2.dim = r + s ∧ c1.dim + 2 * c2.dim = 2 ∧ c0.Exists ∧ c1.Exists ∧ c2.Exists ∧
    (c0.sign.mul c1.sign).mul c2.sign = .plus ∧
    (r : ZMod 8) - s = c0.oddity + c1.oddity + c2.oddity + 4 * ind8 (c1.sign = .minus)

/-- **Existence for $\lvert\det\rvert = 4$, general form** (Conway–Sloane, §8.1, Table 15.4, rows $\pm4$): a system of
symbols satisfying the conditions with $\lvert\det\rvert = 4$, $(-1)$-adic symbol $+^r-^s$ and a property `P` of its
three 2-adic constituents (scales $1,2,4$) exists iff there are constituents satisfying `Constr4` and `P`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±4)"]
theorem det4_exists_iff (r s : ℕ) (P : TwoFactor → TwoFactor → TwoFactor → Prop) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧
        P (G.two 0) (G.two 1) (G.two 2)) ↔ ∃ c0 c1 c2, Constr4 r s c0 c1 c2 ∧ P c0 c1 c2 := by
  constructor
  · rintro ⟨G, hc, hr, hd, hP⟩
    have hn : G.n = r + s := by rw [← hc.real_dim, hr]
    have hv2 : padicValInt 2 G.det = 2 := by
      simp only [padicValInt, hd]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact padicValNat.prime_pow 2
    obtain ⟨-, h1, h2, h3, h4, e0, e1, e2⟩ := G.two_shape4 hc hv2
    have hj : jacobiTwo (G.det / 4) = .plus := by
      apply jacobiTwo_pm_one_int
      have : G.det = 4 ∨ G.det = -4 := by omega
      rcases this with h | h <;> rw [h] <;> norm_num
    rw [hj] at h3
    refine ⟨G.two 0, G.two 1, G.two 2, ⟨by omega, h1, e0, e1, e2, h3, ?_⟩, hP⟩
    have h := hc.oddity_formula
    rw [hd, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Finset.filter_singleton, if_neg (by norm_num), Finset.sum_empty, add_zero, h4] at h
    have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
    rw [hsig] at h
    exact h
  · rintro ⟨c0, c1, c2, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hP⟩
    exact ⟨dataTwo4 r s c0 c1 c2, dataTwo4_conditions r s c0 c1 c2 a1 a2 a3 a4 a5 a6 a7, rfl,
      by simp [dataTwo4, natAbs_four], by simpa [dataTwo4] using hP⟩

/-! ### The rows -/

/-- Right-hand side, constituent of dimension $1$ at the scale $4$ ($\dim_1 = 0$): scale-1 type `T0`, with a
side condition `Q` on the signs and oddities of the scale-1 and scale-4 constituents. -/
def RhsA (T0 : ScaledType) (Q : Sign → ZMod 8 → Sign → ZMod 8 → Prop) (n : ℕ) (σ : ZMod 8) : Prop :=
  1 ≤ n ∧ ∃ ε0 ∈ signList, ∃ ε2 ∈ signList, ∃ t0 t2 : ZMod 8, ε0.mul ε2 = .plus ∧
    (⟨n - 1, ε0, T0, t0⟩ : TwoFactor).Exists ∧ (⟨1, ε2, .I, t2⟩ : TwoFactor).Exists ∧ σ = t0 + t2 ∧
    Q ε0 t0 ε2 t2

/-- Right-hand side, constituent of dimension $2$ at the scale $2$ ($\dim_2 = 0$): scale-1 type `T0`, scale-2
type `T1`, with a side condition `Q` on the sign of the scale-2 constituent. -/
def RhsB (T0 T1 : ScaledType) (Q : Sign → Prop) (n : ℕ) (σ : ZMod 8) : Prop :=
  2 ≤ n ∧ ∃ ε0 ∈ signList, ∃ ε1 ∈ signList, ∃ t0 t1 : ZMod 8, ε0.mul ε1 = .plus ∧
    (⟨n - 2, ε0, T0, t0⟩ : TwoFactor).Exists ∧ (⟨2, ε1, T1, t1⟩ : TwoFactor).Exists ∧
    σ = t0 + t1 + 4 * ind8 (ε1 = .minus) ∧ Q ε1

set_option synthInstance.maxSize 1024 in
instance (T0 : ScaledType) (Q : Sign → ZMod 8 → Sign → ZMod 8 → Prop) [∀ a b c d, Decidable (Q a b c d)]
    (n : ℕ) (σ : ZMod 8) : Decidable (RhsA T0 Q n σ) := by
  unfold RhsA; infer_instance

set_option synthInstance.maxSize 1024 in
instance (T0 T1 : ScaledType) (Q : Sign → Prop) [∀ a, Decidable (Q a)] (n : ℕ) (σ : ZMod 8) :
    Decidable (RhsB T0 T1 Q n σ) := by
  unfold RhsB; infer_instance

theorem TwoFactor.eta (c : TwoFactor) : c = ⟨c.dim, c.sign, c.type, c.oddity⟩ := by cases c; rfl

theorem exists_stable (m : ℕ) (hm : 3 ≤ m) (ε : Sign) (T : ScaledType) (t : ZMod 8) :
    (⟨m + 2, ε, T, t⟩ : TwoFactor).Exists ↔ (⟨m, ε, T, t⟩ : TwoFactor).Exists := by
  constructor
  · rintro ⟨-, -, -, h4, h5⟩
    exact ⟨fun h => by have : m = 0 := h; omega, fun h => by have : m = 1 := h; omega,
      fun h => by have : m = 2 := h; omega, by simp only at h4 ⊢; omega, h5⟩
  · rintro ⟨-, -, -, h4, h5⟩
    exact ⟨fun h => by have : m + 2 = 0 := h; omega, fun h => by have : m + 2 = 1 := h; omega,
      fun h => by have : m + 2 = 2 := h; omega, by simp only at h4 ⊢; omega, h5⟩

theorem rhsA_tail (T0 : ScaledType) (Q : Sign → ZMod 8 → Sign → ZMod 8 → Prop) (n : ℕ) (hn : 4 ≤ n)
    (σ : ZMod 8) : RhsA T0 Q (n + 2) σ ↔ RhsA T0 Q n σ := by
  unfold RhsA
  have e : n + 2 - 1 = (n - 1) + 2 := by omega
  rw [e]
  simp only [exists_stable (n - 1) (by omega)]
  constructor
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩

theorem rhsB_tail (T0 T1 : ScaledType) (Q : Sign → Prop) (n : ℕ) (hn : 5 ≤ n) (σ : ZMod 8) :
    RhsB T0 T1 Q (n + 2) σ ↔ RhsB T0 T1 Q n σ := by
  unfold RhsB
  have e : n + 2 - 2 = (n - 2) + 2 := by omega
  rw [e]
  simp only [exists_stable (n - 2) (by omega)]
  constructor
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩

theorem explicit_of (R P : ℕ → ZMod 8 → Prop) (N0 : ℕ) (tailR : ∀ n, N0 ≤ n → ∀ σ, R (n + 2) σ ↔ R n σ)
    (tailP : ∀ n, N0 ≤ n → ∀ σ, P (n + 2) σ ↔ P n σ) (base : ∀ n, n < N0 + 2 → ∀ σ, R n σ ↔ P n σ) :
    ∀ n σ, R n σ ↔ P n σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ
    by_cases h : n < N0 + 2
    · exact base n h σ
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [tailR m (by omega) σ, tailP m (by omega) σ]
      exact ih m (by omega) σ

theorem det4_rowA (T0 : ScaledType) (Q : Sign → ZMod 8 → Sign → ZMod 8 → Prop) (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = T0 ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 1 ∧
        Q (G.two 0).sign (G.two 0).oddity (G.two 2).sign (G.two 2).oddity) ↔
      RhsA T0 Q (r + s) ((r : ZMod 8) - s) := by
  refine (det4_exists_iff r s (fun c0 c1 c2 => c0.type = T0 ∧ c1.dim = 0 ∧ c2.dim = 1 ∧
    Q c0.sign c0.oddity c2.sign c2.oddity)).trans ?_
  constructor
  · rintro ⟨⟨d0, s0, ty0, o0⟩, ⟨d1, s1, ty1, o1⟩, ⟨d2, s2, ty2, o2⟩, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hT, h1, h2, hQ⟩
    dsimp only at *
    subst hT h1 h2
    have hd0 : d0 = r + s - 1 := by omega
    subst hd0
    obtain ⟨h32, -, -, -, hII⟩ := a4
    obtain ⟨hty, hsg⟩ := h32 rfl
    have ho : o1 = 0 := hII hty
    subst hty hsg ho
    have hty2 : ty2 = .I := (a5 : (⟨1, s2, ty2, o2⟩ : TwoFactor).Exists).typeI_of_odd (by simp)
    subst hty2
    refine ⟨by omega, s0, mem_signList _, s2, mem_signList _, o0, o2, ?_, a3, a5, ?_, hQ⟩
    · simpa [Sign.mul_plus] using a6
    · simpa [ind8] using a7
  · rintro ⟨hn, ε0, -, ε2, -, t0, t2, hp, e0, e2, hσ, hQ⟩
    refine ⟨⟨r + s - 1, ε0, T0, t0⟩, TwoFactor.trivial, ⟨1, ε2, .I, t2⟩,
      ⟨by simp [TwoFactor.trivial]; omega, by simp [TwoFactor.trivial], e0, by decide, e2, ?_, ?_⟩,
      rfl, rfl, rfl, hQ⟩
    · simpa [TwoFactor.trivial, Sign.mul_plus] using hp
    · simp [TwoFactor.trivial, ind8, hσ]

theorem det4_rowB (T0 T1 : ScaledType) (Q : Sign → Prop) (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = T0 ∧
        (G.two 1).dim = 2 ∧ (G.two 1).type = T1 ∧ (G.two 2).dim = 0 ∧ Q (G.two 1).sign) ↔
      RhsB T0 T1 Q (r + s) ((r : ZMod 8) - s) := by
  refine (det4_exists_iff r s (fun c0 c1 c2 => c0.type = T0 ∧ c1.dim = 2 ∧ c1.type = T1 ∧ c2.dim = 0 ∧
    Q c1.sign)).trans ?_
  constructor
  · rintro ⟨⟨d0, s0, ty0, o0⟩, ⟨d1, s1, ty1, o1⟩, ⟨d2, s2, ty2, o2⟩, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hT, h1, hT1, h2, hQ⟩
    dsimp only at *
    subst hT h1 hT1 h2
    have hd0 : d0 = r + s - 2 := by omega
    subst hd0
    obtain ⟨h32, -, -, -, hII⟩ := a5
    obtain ⟨hty, hsg⟩ := h32 rfl
    have ho : o2 = 0 := hII hty
    subst hty hsg ho
    refine ⟨by omega, s0, mem_signList _, s1, mem_signList _, o0, o1, ?_, a3, a4, ?_, hQ⟩
    · simpa [Sign.mul_plus] using a6
    · simpa using a7
  · rintro ⟨hn, ε0, -, ε1, -, t0, t1, hp, e0, e1, hσ, hQ⟩
    refine ⟨⟨r + s - 2, ε0, T0, t0⟩, ⟨2, ε1, T1, t1⟩, TwoFactor.trivial,
      ⟨by simp [TwoFactor.trivial]; omega, by simp [TwoFactor.trivial], e0, e1, by decide, ?_, ?_⟩,
      rfl, rfl, rfl, rfl, hQ⟩
    · simpa [TwoFactor.trivial, Sign.mul_plus] using hp
    · simp [TwoFactor.trivial, hσ]

/-! ### Table 15.4, rows $\lvert\det\rvert = 4$

In all statements $\sigma = (r - s) \bmod 8 \in \mathbb Z/8$ and $n = r + s$; `σ.val` is its representative in
$\{0, \dots, 7\}$. -/

/-- **Table 15.4, $\pm4$, $\mathrm I_{r,s}(4_{+1})$** (scale-1 type I, scale-4 constituent of dimension $1$ with
invariant $t + 4[\varepsilon = -] = 1$): exceptions $0$, $1$, $2_{-2}$ and (not listed in the book) $3_{-3}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, I(4_{+1}))"]
theorem table154_four_I_plus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 1 ∧
        (G.two 2).oddity + 4 * ind8 ((G.two 2).sign = .minus) = 1) ↔
      (((r + s = 2 ∧ (((r : ZMod 8) - s).val = 0 ∨ ((r : ZMod 8) - s).val = 2)) ∨
        (r + s = 3 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 3 ∨ ((r : ZMod 8) - s).val = 7)) ∨
        (4 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2))) :=
  (det4_rowA .I (fun _ _ ε2 t2 => t2 + 4 * ind8 (ε2 = .minus) = 1) r s).trans
    (explicit_of (RhsA .I (fun _ _ ε2 t2 => t2 + 4 * ind8 (ε2 = .minus) = 1))
      (fun n σ => (n = 2 ∧ (σ.val = 0 ∨ σ.val = 2)) ∨ (n = 3 ∧ (σ.val = 1 ∨ σ.val = 3 ∨ σ.val = 7)) ∨
        (4 ≤ n ∧ σ.val % 2 = n % 2)) 4
      (fun n hn σ => rhsA_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm I_{r,s}(4_{-1})$**: the negative of the previous row: exceptions $0$, $1$, $2_{+2}$
and (not listed in the book) $3_{+3}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, I(4_{-1}))"]
theorem table154_four_I_minus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 1 ∧
        (G.two 2).oddity + 4 * ind8 ((G.two 2).sign = .minus) = 7) ↔
      (((r + s = 2 ∧ (((r : ZMod 8) - s).val = 0 ∨ ((r : ZMod 8) - s).val = 6)) ∨
        (r + s = 3 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 5 ∨ ((r : ZMod 8) - s).val = 7)) ∨
        (4 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2))) :=
  (det4_rowA .I (fun _ _ ε2 t2 => t2 + 4 * ind8 (ε2 = .minus) = 7) r s).trans
    (explicit_of (RhsA .I (fun _ _ ε2 t2 => t2 + 4 * ind8 (ε2 = .minus) = 7))
      (fun n σ => (n = 2 ∧ (σ.val = 0 ∨ σ.val = 6)) ∨ (n = 3 ∧ (σ.val = 1 ∨ σ.val = 5 ∨ σ.val = 7)) ∨
        (4 ≤ n ∧ σ.val % 2 = n % 2)) 4
      (fun n hn σ => rhsA_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm{II}_{r,s}(4^{1})$**: signature $\pm1$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, II(4^1))"]
theorem table154_four_II_plus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 1 ∧ (G.two 2).sign = .plus) ↔
      ((r + s) % 2 = 1 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 7)) :=
  (det4_rowA .II (fun _ _ ε2 _ => ε2 = .plus) r s).trans
    (explicit_of (RhsA .II (fun _ _ ε2 _ => ε2 = .plus))
      (fun n σ => n % 2 = 1 ∧ (σ.val = 1 ∨ σ.val = 7)) 4
      (fun n hn σ => rhsA_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm{II}_{r,s}(4^{-1})$**: signature $\pm3$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, II(4^{-1}))"]
theorem table154_four_II_minus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 1 ∧ (G.two 2).sign = .minus) ↔
      ((r + s) % 2 = 1 ∧ 3 ≤ r + s ∧ (((r : ZMod 8) - s).val = 3 ∨ ((r : ZMod 8) - s).val = 5)) :=
  (det4_rowA .II (fun _ _ ε2 _ => ε2 = .minus) r s).trans
    (explicit_of (RhsA .II (fun _ _ ε2 _ => ε2 = .minus))
      (fun n σ => n % 2 = 1 ∧ 3 ≤ n ∧ (σ.val = 3 ∨ σ.val = 5)) 4
      (fun n hn σ => rhsA_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm I_{r,s}(2_{\mathrm I}^2)$**: all signatures, exceptions $0$, $1$, $2$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, I(2_I^2))"]
theorem table154_four_I_2I (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 2 ∧ (G.two 1).type = .I ∧ (G.two 2).dim = 0 ∧ True) ↔
      (3 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2) :=
  (det4_rowB .I .I (fun _ => True) r s).trans
    (explicit_of (RhsB .I .I (fun _ => True)) (fun n σ => 3 ≤ n ∧ σ.val % 2 = n % 2) 5
      (fun n hn σ => rhsB_tail _ _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm{II}_{r,s}(2_{\mathrm I}^2)$**: signature $0, \pm2$, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, II(2_I^2))"]
theorem table154_four_II_2I (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 2 ∧ (G.two 1).type = .I ∧ (G.two 2).dim = 0 ∧ True) ↔
      ((r + s) % 2 = 0 ∧ 2 ≤ r + s ∧
        (((r : ZMod 8) - s).val = 0 ∨ ((r : ZMod 8) - s).val = 2 ∨ ((r : ZMod 8) - s).val = 6)) :=
  (det4_rowB .II .I (fun _ => True) r s).trans
    (explicit_of (RhsB .II .I (fun _ => True))
      (fun n σ => n % 2 = 0 ∧ 2 ≤ n ∧ (σ.val = 0 ∨ σ.val = 2 ∨ σ.val = 6)) 5
      (fun n hn σ => rhsB_tail _ _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm I_{r,s}(2_{\mathrm{II}}^2)$**: all signatures, exceptions $0, 1, 2, 3_{\pm3},
4_{\pm4}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, I(2_II^2))"]
theorem table154_four_I_2II (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 2 ∧ (G.two 1).type = .II ∧ (G.two 2).dim = 0 ∧ True) ↔
      ((r + s = 3 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 7)) ∨
        (r + s = 4 ∧ (((r : ZMod 8) - s).val = 0 ∨ ((r : ZMod 8) - s).val = 2 ∨ ((r : ZMod 8) - s).val = 6)) ∨
        (5 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2)) :=
  (det4_rowB .I .II (fun _ => True) r s).trans
    (explicit_of (RhsB .I .II (fun _ => True))
      (fun n σ => (n = 3 ∧ (σ.val = 1 ∨ σ.val = 7)) ∨ (n = 4 ∧ (σ.val = 0 ∨ σ.val = 2 ∨ σ.val = 6)) ∨
        (5 ≤ n ∧ σ.val % 2 = n % 2)) 5
      (fun n hn σ => rhsB_tail _ _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm{II}_{r,s}(2_{\mathrm{II}}^2)$**: signature $0$, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, II(2_II^2))"]
theorem table154_four_II_2II_plus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 2 ∧ (G.two 1).type = .II ∧ (G.two 2).dim = 0 ∧ (G.two 1).sign = .plus) ↔
      ((r + s) % 2 = 0 ∧ 2 ≤ r + s ∧ ((r : ZMod 8) - s).val = 0) :=
  (det4_rowB .II .II (fun ε1 => ε1 = .plus) r s).trans
    (explicit_of (RhsB .II .II (fun ε1 => ε1 = .plus))
      (fun n σ => n % 2 = 0 ∧ 2 ≤ n ∧ σ.val = 0) 5
      (fun n hn σ => rhsB_tail _ _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm4$, $\mathrm{II}_{r,s}(2_{\mathrm{II}}^{-2})$**: signature $4$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±4, II(2_II^{-2}))"]
theorem table154_four_II_2II_minus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 4 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 2 ∧ (G.two 1).type = .II ∧ (G.two 2).dim = 0 ∧ (G.two 1).sign = .minus) ↔
      ((r + s) % 2 = 0 ∧ 4 ≤ r + s ∧ ((r : ZMod 8) - s).val = 4) :=
  (det4_rowB .II .II (fun ε1 => ε1 = .minus) r s).trans
    (explicit_of (RhsB .II .II (fun ε1 => ε1 = .minus))
      (fun n σ => n % 2 = 0 ∧ 4 ≤ n ∧ σ.val = 4) 5
      (fun n hn σ => rhsB_tail _ _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

end QuadFormsKB.ConwaySloane
