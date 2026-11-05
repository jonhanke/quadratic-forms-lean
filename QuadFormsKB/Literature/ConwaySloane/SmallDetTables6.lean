/-
# Conway–Sloane, Ch. 15, §8.1: Table 15.4, the rows $\lvert\det\rvert = 8$

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.1,
Theorem 12, Table 15.4 (p. 387) (`conwaysloane1999`).

Continuation of `SmallDetTables5.lean` ($\lvert\det\rvert = 4$): for $\lvert\det\rvert = 8$ the 2-adic symbol lives on
the scales $1, 2, 4, 8$ with $\dim_1 + 2\dim_2 + 3\dim_3 = 3$.

This file proves the shape lemma `two_shape8` and the general existence theorem `det8_exists_iff`, and then the existence
statements for all twelve rows $\lvert\det\rvert = 8$ of Table 15.4 (`table154_eight_*`), by `decide` on the first cases
and the tail arguments `rhsC_tail`, `rhsD_tail`, `rhsE_tail` for large $n$:
$\mathrm I(8_{\pm1})$, $\mathrm I(8_{\pm3})$ (four genera: sign $\varepsilon_3$ and oddity $t_3$ of the scale-8
constituent), $\mathrm{II}(8^{\pm1})$, $\mathrm I/\mathrm{II}(2\times4)$, $\mathrm I/\mathrm{II}(2^3)$. Every printed
signature set and exception list agrees with the computed one (including $3_{\mp3}$ for $8_{\pm1}$ and $3_{\mp1}$ for
$8_{\pm3}$); in particular the exception $3_{\mp3}$ that is printed for $8_{\pm1}$ supports the reading that the book
also omitted it for $4_{\pm1}$ (see `SmallDetTables5.lean`).

Uniqueness of the genera up to `MoveEquiv` is not proved for these rows.
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables5

namespace QuadFormsKB.ConwaySloane

open Finset

/-- **The 2-adic symbol when $v_2(\det) = 3$**: only the scales $1, 2, 4, 8$ occur, with
$\dim_1 + 2\dim_2 + 3\dim_3 = 3$; the signs have product $\left(\frac{\det/8}{2}\right)$ and the oddity is
$t_0 + t_1 + t_2 + t_3 + 4([\varepsilon_1 = -] + [\varepsilon_3 = -])$ (the scales $2$ and $8$ are odd powers of $2$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (2-adic shape for |det| = 8)"]
theorem GenusSymbolData.two_shape8 (G : GenusSymbolData) (hc : G.Conditions) (hv2 : padicValInt 2 G.det = 3) :
    (∀ k, 4 ≤ k → G.two k = TwoFactor.trivial) ∧
      (G.two 1).dim + 2 * (G.two 2).dim + 3 * (G.two 3).dim = 3 ∧
      (G.two 0).dim + (G.two 1).dim + (G.two 2).dim + (G.two 3).dim = G.n ∧
      (((G.two 0).sign.mul (G.two 1).sign).mul (G.two 2).sign).mul (G.two 3).sign = jacobiTwo (G.det / 8) ∧
      G.two.oddity G.N = (G.two 0).oddity + (G.two 1).oddity + (G.two 2).oddity + (G.two 3).oddity +
        4 * (ind8 ((G.two 1).sign = .minus) + ind8 ((G.two 3).sign = .minus)) ∧
      (G.two 0).Exists ∧ (G.two 1).Exists ∧ (G.two 2).Exists ∧ (G.two 3).Exists := by
  obtain ⟨hs, hsg⟩ := hc.two_det
  rw [hv2] at hs
  have hsupp := hc.two_supp
  have hex := hc.two_exists
  have d4 : ∀ k, 4 ≤ k → (G.two k).dim = 0 := by
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
  have t4 : ∀ k, 4 ≤ k → G.two k = TwoFactor.trivial := by
    intro k hk
    obtain ⟨h32, -, -, -, hII⟩ := hex k
    have h1 : (G.two k).dim = 0 := d4 k hk
    obtain ⟨h2, h3⟩ := h32 h1
    have h4 : (G.two k).oddity = 0 := hII h2
    generalize G.two k = f at h1 h2 h3 h4
    obtain ⟨d, s, t, o⟩ := f
    dsimp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  have hsupN : ∀ k, G.N ≤ k → (G.two k).dim = 0 := fun k hk => by rw [hsupp k hk]; rfl
  refine ⟨t4, ?_, ?_, ?_, ?_, hex 0, hex 1, hex 2, hex 3⟩
  · rw [sum_range_stable_nat (f := fun k => k * (G.two k).dim) (m := 4) (fun k hk => by simp [d4 k hk])
      (fun k hk => by simp [hsupN k hk])] at hs
    simpa [Finset.sum_range_succ] using hs
  · have h := hc.two_dim
    rw [sum_range_stable_nat (f := fun k => (G.two k).dim) (m := 4) (fun k hk => d4 k hk) hsupN] at h
    simpa [Finset.sum_range_succ] using h
  · have h4 : signProd (fun k => (G.two k).sign) G.N = signProd (fun k => (G.two k).sign) 4 := by
      rcases le_total G.N 4 with h | h
      · exact (signProd_stable _ h (fun k hk => by simp [hsupp k hk, TwoFactor.trivial])).symm
      · exact signProd_stable _ h (fun k hk => by simp [t4 k hk, TwoFactor.trivial])
    rw [h4, hv2] at hsg
    simpa [signProd, Sign.plus_mul] using hsg
  · have hodd : G.two.oddity G.N = G.two.oddity 4 := by
      rcases le_total 4 G.N with h | h
      · exact TwoSymbol.oddity_congr (fun k hk => t4 k hk) h
      · exact (TwoSymbol.oddity_congr hsupp h).symm
    rw [hodd]
    unfold TwoSymbol.oddity
    have h2odd : ¬ Odd 2 := by decide
    have h3odd : Odd 3 := by decide
    simp [Finset.sum_range_succ, ind8, h2odd, h3odd]
    split_ifs <;> ring

theorem natAbs_eight (s : ℕ) : (8 * (-1 : ℤ) ^ s).natAbs = 2 ^ 3 := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem padicValInt_eight_two (s : ℕ) : padicValInt 2 (8 * (-1 : ℤ) ^ s) = 3 := by
  simp only [padicValInt, natAbs_eight]
  exact padicValNat.prime_pow 3

theorem padicValInt_eight_odd (q s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q (8 * (-1 : ℤ) ^ s) = 0 := by
  have : ¬ q ∣ 2 ^ 3 := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  have h8 : ¬ q ∣ 8 := fun h => this (by simpa using h)
  simp [padicValInt, natAbs_eight, padicValNat.eq_zero_of_not_dvd h8]

/-- **The system of symbols for $\lvert\det\rvert = 8$** with the four 2-adic constituents (scales $1,2,4,8$) and unit
symbols at the odd primes. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±8)"]
def dataTwo8 (r s : ℕ) (c0 c1 c2 c3 : TwoFactor) : GenusSymbolData where
  n := r + s
  det := 8 * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q k => if k = 0 then ⟨r + s, Sign.ofInt (jacobiSym (8 * (-1) ^ s) q)⟩ else OddFactor.trivial
  two := fun k =>
    if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else if k = 3 then c3 else TwoFactor.trivial
  N := 4

theorem dataTwo8_conditions (r s : ℕ) (c0 c1 c2 c3 : TwoFactor)
    (hn : c0.dim + c1.dim + c2.dim + c3.dim = r + s) (hdim : c1.dim + 2 * c2.dim + 3 * c3.dim = 3)
    (h0 : c0.Exists) (h1 : c1.Exists) (h2 : c2.Exists) (h3 : c3.Exists)
    (hsg : (((c0.sign.mul c1.sign).mul c2.sign).mul c3.sign) = .plus)
    (hsig : (r : ZMod 8) - s = c0.oddity + c1.oddity + c2.oddity + c3.oddity +
      4 * (ind8 (c1.sign = .minus) + ind8 (c3.sign = .minus))) :
    (dataTwo8 r s c0 c1 c2 c3).Conditions where
  ne_zero := mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp [dataTwo8, h.neg_one_pow, this]
    · simp [dataTwo8, h.neg_one_pow, h]
  odd_supp q k hk := by
    have hk' : 4 ≤ k := hk
    simp [dataTwo8, show k ≠ 0 by omega]
  two_supp k hk := by
    have hk' : 4 ≤ k := hk
    simp [dataTwo8, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega]
  odd_dim q _ _ := by simp [dataTwo8, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by
    simp [dataTwo8, Finset.sum_range_succ, TwoFactor.trivial]
    omega
  odd_det q hq hq2 := by
    refine ⟨?_, ?_⟩
    · simp [dataTwo8, padicValInt_eight_odd q s hq hq2, Finset.sum_range_succ, OddFactor.trivial]
    · simp [dataTwo8, padicValInt_eight_odd q s hq hq2, signProd, Sign.plus_mul, Sign.mul_plus,
        OddFactor.trivial]
  two_det := by
    refine ⟨?_, ?_⟩
    · simp [dataTwo8, padicValInt_eight_two, Finset.sum_range_succ, TwoFactor.trivial]
      omega
    · have hd : (8 * (-1 : ℤ) ^ s) / 2 ^ 3 = (-1) ^ s := by simp
      simp [dataTwo8, padicValInt_eight_two, signProd, hd, jacobiTwo_pm_one, Sign.plus_mul, Sign.mul_plus,
        TwoFactor.trivial]
      simpa [signProd, Sign.plus_mul] using hsg
  odd_exists q hq hq2 k := by
    by_cases hk : k = 0
    · subst hk
      simp only [dataTwo8, if_true]
      intro h0'
      have : r + s = 0 := h0'
      omega
    · simp [dataTwo8, hk, OddFactor.Exists, OddFactor.trivial]
  two_exists k := by
    by_cases hk : k = 0
    · subst hk; simpa [dataTwo8] using h0
    · by_cases hk1 : k = 1
      · subst hk1; simpa [dataTwo8] using h1
      · by_cases hk2 : k = 2
        · subst hk2; simpa [dataTwo8] using h2
        · by_cases hk3 : k = 3
          · subst hk3; simpa [dataTwo8] using h3
          · simp only [dataTwo8, if_neg hk, if_neg hk1, if_neg hk2, if_neg hk3]
            decide
  oddity_formula := by
    have hna : (dataTwo8 r s c0 c1 c2 c3).det.natAbs = 2 ^ 3 := by
      simp [dataTwo8, natAbs_eight]
    rw [hna, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Finset.filter_singleton,
      if_neg (by norm_num), Finset.sum_empty, add_zero]
    have h2odd : ¬ Odd 2 := by decide
    have h3odd : Odd 3 := by decide
    simp [dataTwo8, GenusSymbolData.signature, TwoSymbol.oddity, Finset.sum_range_succ, TwoFactor.trivial,
      ind8, h2odd, h3odd] at hsig ⊢
    split_ifs at hsig ⊢ <;> linear_combination hsig

/-- The constraints on the four 2-adic constituents of a system with $\lvert\det\rvert = 8$ and signature $(r,s)$. -/
def Constr8 (r s : ℕ) (c0 c1 c2 c3 : TwoFactor) : Prop :=
  c0.dim + c1.dim + c2.dim + c3.dim = r + s ∧ c1.dim + 2 * c2.dim + 3 * c3.dim = 3 ∧
    c0.Exists ∧ c1.Exists ∧ c2.Exists ∧ c3.Exists ∧
    (((c0.sign.mul c1.sign).mul c2.sign).mul c3.sign) = .plus ∧
    (r : ZMod 8) - s = c0.oddity + c1.oddity + c2.oddity + c3.oddity +
      4 * (ind8 (c1.sign = .minus) + ind8 (c3.sign = .minus))

/-- **Existence for $\lvert\det\rvert = 8$, general form** (Conway–Sloane, §8.1, Table 15.4, rows $\pm8$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±8)"]
theorem det8_exists_iff (r s : ℕ) (P : TwoFactor → TwoFactor → TwoFactor → TwoFactor → Prop) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧
        P (G.two 0) (G.two 1) (G.two 2) (G.two 3)) ↔
      ∃ c0 c1 c2 c3, Constr8 r s c0 c1 c2 c3 ∧ P c0 c1 c2 c3 := by
  constructor
  · rintro ⟨G, hc, hr, hd, hP⟩
    have hn : G.n = r + s := by rw [← hc.real_dim, hr]
    have hv2 : padicValInt 2 G.det = 3 := by
      simp only [padicValInt, hd]
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact padicValNat.prime_pow 3
    obtain ⟨-, h1, h2, h3, h4, e0, e1, e2, e3⟩ := G.two_shape8 hc hv2
    have hj : jacobiTwo (G.det / 8) = .plus := by
      apply jacobiTwo_pm_one_int
      have : G.det = 8 ∨ G.det = -8 := by omega
      rcases this with h | h <;> rw [h] <;> norm_num
    rw [hj] at h3
    refine ⟨G.two 0, G.two 1, G.two 2, G.two 3, ⟨by omega, h1, e0, e1, e2, e3, h3, ?_⟩, hP⟩
    have h := hc.oddity_formula
    have e8 : (8 : ℕ).primeFactors = {2} := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two
    rw [hd, e8, Finset.filter_singleton, if_neg (by norm_num), Finset.sum_empty, add_zero, h4] at h
    have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
    rw [hsig] at h
    exact h
  · rintro ⟨c0, c1, c2, c3, ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, hP⟩
    exact ⟨dataTwo8 r s c0 c1 c2 c3, dataTwo8_conditions r s c0 c1 c2 c3 a1 a2 a3 a4 a5 a6 a7 a8, rfl,
      by simp [dataTwo8, natAbs_eight], by simpa [dataTwo8] using hP⟩

/-! ### The shapes -/

/-- One constituent of dimension $1$ at the scale $8$ (shape $\dim_3 = 1$): scale-1 type `T0`, the scale-8
constituent $\langle 1, \varepsilon_3, \mathrm I, t_3\rangle$ constrained by `Q`; $t_0$ is eliminated using the oddity formula. -/
def RhsC (T0 : ScaledType) (Q : Sign → ZMod 8 → Prop) (n : ℕ) (σ : ZMod 8) : Prop :=
  1 ≤ n ∧ ∃ ε0 ∈ signList, ∃ ε3 ∈ signList, ∃ t3 : ZMod 8, ε0.mul ε3 = .plus ∧
    (⟨n - 1, ε0, T0, σ - t3 - 4 * ind8 (ε3 = .minus)⟩ : TwoFactor).Exists ∧
    (⟨1, ε3, .I, t3⟩ : TwoFactor).Exists ∧ Q ε3 t3

/-- One constituent of dimension $1$ at each of the scales $2$ and $4$ (shape $\dim_1 = \dim_2 = 1$, "$2\times4$"). -/
def RhsD (T0 : ScaledType) (n : ℕ) (σ : ZMod 8) : Prop :=
  2 ≤ n ∧ ∃ ε0 ∈ signList, ∃ ε1 ∈ signList, ∃ ε2 ∈ signList, ∃ t0 t1 : ZMod 8,
    (ε0.mul ε1).mul ε2 = .plus ∧ (⟨n - 2, ε0, T0, t0⟩ : TwoFactor).Exists ∧
    (⟨1, ε1, .I, t1⟩ : TwoFactor).Exists ∧
    (⟨1, ε2, .I, σ - t0 - t1 - 4 * ind8 (ε1 = .minus)⟩ : TwoFactor).Exists

/-- One constituent of dimension $3$ at the scale $2$ (shape $\dim_1 = 3$, "$2^3$"). -/
def RhsE (T0 : ScaledType) (n : ℕ) (σ : ZMod 8) : Prop :=
  3 ≤ n ∧ ∃ ε0 ∈ signList, ∃ ε1 ∈ signList, ∃ t1 : ZMod 8, ε0.mul ε1 = .plus ∧
    (⟨n - 3, ε0, T0, σ - t1 - 4 * ind8 (ε1 = .minus)⟩ : TwoFactor).Exists ∧
    (⟨3, ε1, .I, t1⟩ : TwoFactor).Exists

set_option synthInstance.maxSize 1024 in
instance (T0 : ScaledType) (Q : Sign → ZMod 8 → Prop) [∀ a b, Decidable (Q a b)] (n : ℕ) (σ : ZMod 8) :
    Decidable (RhsC T0 Q n σ) := by
  unfold RhsC; infer_instance

set_option synthInstance.maxSize 1024 in
instance (T0 : ScaledType) (n : ℕ) (σ : ZMod 8) : Decidable (RhsD T0 n σ) := by
  unfold RhsD; infer_instance

set_option synthInstance.maxSize 1024 in
instance (T0 : ScaledType) (n : ℕ) (σ : ZMod 8) : Decidable (RhsE T0 n σ) := by
  unfold RhsE; infer_instance

theorem det8_rowC (T0 : ScaledType) (Q : Sign → ZMod 8 → Prop) (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = T0 ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 1 ∧ Q (G.two 3).sign (G.two 3).oddity) ↔
      RhsC T0 Q (r + s) ((r : ZMod 8) - s) := by
  refine (det8_exists_iff r s (fun c0 c1 c2 c3 => c0.type = T0 ∧ c1.dim = 0 ∧ c2.dim = 0 ∧ c3.dim = 1 ∧
    Q c3.sign c3.oddity)).trans ?_
  constructor
  · rintro ⟨⟨d0, s0, ty0, o0⟩, ⟨d1, s1, ty1, o1⟩, ⟨d2, s2, ty2, o2⟩, ⟨d3, s3, ty3, o3⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, hT, h1, h2, h3, hQ⟩
    dsimp only at *
    subst hT h1 h2 h3
    have hd0 : d0 = r + s - 1 := by omega
    subst hd0
    obtain ⟨h32, -, -, -, hII⟩ := a4
    obtain ⟨hty, hsg⟩ := h32 rfl
    have ho : o1 = 0 := hII hty
    subst hty hsg ho
    obtain ⟨h32', -, -, -, hII'⟩ := a5
    obtain ⟨hty', hsg'⟩ := h32' rfl
    have ho' : o2 = 0 := hII' hty'
    subst hty' hsg' ho'
    have hty3 : ty3 = .I := (a6 : (⟨1, s3, ty3, o3⟩ : TwoFactor).Exists).typeI_of_odd (by simp)
    subst hty3
    have ho0 : o0 = ((r : ZMod 8) - s) - o3 - 4 * ind8 (s3 = .minus) := by
      simp [ind8] at a8 ⊢
      linear_combination -a8
    refine ⟨by omega, s0, mem_signList _, s3, mem_signList _, o3, ?_, ?_, a6, hQ⟩
    · simpa [Sign.mul_plus] using a7
    · rw [← ho0]; exact a3
  · rintro ⟨hn, ε0, -, ε3, -, t3, hp, e0, e3, hQ⟩
    refine ⟨⟨r + s - 1, ε0, T0, (r : ZMod 8) - s - t3 - 4 * ind8 (ε3 = .minus)⟩, TwoFactor.trivial,
      TwoFactor.trivial, ⟨1, ε3, .I, t3⟩,
      ⟨by simp [TwoFactor.trivial]; omega, by simp [TwoFactor.trivial], e0, by decide, by decide, e3, ?_, ?_⟩,
      rfl, rfl, rfl, rfl, hQ⟩
    · simpa [TwoFactor.trivial, Sign.mul_plus] using hp
    · simp [TwoFactor.trivial, ind8]; ring

theorem det8_rowD (T0 : ScaledType) (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = T0 ∧
        (G.two 1).dim = 1 ∧ (G.two 2).dim = 1 ∧ (G.two 3).dim = 0 ∧ True) ↔
      RhsD T0 (r + s) ((r : ZMod 8) - s) := by
  refine (det8_exists_iff r s (fun c0 c1 c2 c3 => c0.type = T0 ∧ c1.dim = 1 ∧ c2.dim = 1 ∧ c3.dim = 0 ∧
    True)).trans ?_
  constructor
  · rintro ⟨⟨d0, s0, ty0, o0⟩, ⟨d1, s1, ty1, o1⟩, ⟨d2, s2, ty2, o2⟩, ⟨d3, s3, ty3, o3⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, hT, h1, h2, h3, -⟩
    dsimp only at *
    subst hT h1 h2 h3
    have hd0 : d0 = r + s - 2 := by omega
    subst hd0
    obtain ⟨h32, -, -, -, hII⟩ := a6
    obtain ⟨hty, hsg⟩ := h32 rfl
    have ho : o3 = 0 := hII hty
    subst hty hsg ho
    have hty1 : ty1 = .I := (a4 : (⟨1, s1, ty1, o1⟩ : TwoFactor).Exists).typeI_of_odd (by simp)
    have hty2 : ty2 = .I := (a5 : (⟨1, s2, ty2, o2⟩ : TwoFactor).Exists).typeI_of_odd (by simp)
    subst hty1 hty2
    have ho2 : o2 = ((r : ZMod 8) - s) - o0 - o1 - 4 * ind8 (s1 = .minus) := by
      simp [ind8] at a8 ⊢
      linear_combination -a8
    refine ⟨by omega, s0, mem_signList _, s1, mem_signList _, s2, mem_signList _, o0, o1, ?_, a3, a4, ?_⟩
    · simpa [Sign.mul_plus] using a7
    · rw [← ho2]; exact a5
  · rintro ⟨hn, ε0, -, ε1, -, ε2, -, t0, t1, hp, e0, e1, e2⟩
    refine ⟨⟨r + s - 2, ε0, T0, t0⟩, ⟨1, ε1, .I, t1⟩,
      ⟨1, ε2, .I, (r : ZMod 8) - s - t0 - t1 - 4 * ind8 (ε1 = .minus)⟩, TwoFactor.trivial,
      ⟨by simp [TwoFactor.trivial]; omega, by simp [TwoFactor.trivial], e0, e1, e2, by decide, ?_, ?_⟩,
      rfl, rfl, rfl, rfl, trivial⟩
    · simpa [TwoFactor.trivial, Sign.mul_plus] using hp
    · simp [TwoFactor.trivial, ind8]; ring

theorem det8_rowE (T0 : ScaledType) (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = T0 ∧
        (G.two 1).dim = 3 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 0 ∧ True) ↔
      RhsE T0 (r + s) ((r : ZMod 8) - s) := by
  refine (det8_exists_iff r s (fun c0 c1 c2 c3 => c0.type = T0 ∧ c1.dim = 3 ∧ c2.dim = 0 ∧ c3.dim = 0 ∧
    True)).trans ?_
  constructor
  · rintro ⟨⟨d0, s0, ty0, o0⟩, ⟨d1, s1, ty1, o1⟩, ⟨d2, s2, ty2, o2⟩, ⟨d3, s3, ty3, o3⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, hT, h1, h2, h3, -⟩
    dsimp only at *
    subst hT h1 h2 h3
    have hd0 : d0 = r + s - 3 := by omega
    subst hd0
    obtain ⟨h32, -, -, -, hII⟩ := a5
    obtain ⟨hty, hsg⟩ := h32 rfl
    have ho : o2 = 0 := hII hty
    subst hty hsg ho
    obtain ⟨h32', -, -, -, hII'⟩ := a6
    obtain ⟨hty', hsg'⟩ := h32' rfl
    have ho' : o3 = 0 := hII' hty'
    subst hty' hsg' ho'
    have hty1 : ty1 = .I := (a4 : (⟨3, s1, ty1, o1⟩ : TwoFactor).Exists).typeI_of_odd (by simp)
    subst hty1
    have ho0 : o0 = ((r : ZMod 8) - s) - o1 - 4 * ind8 (s1 = .minus) := by
      simp [ind8] at a8 ⊢
      linear_combination -a8
    refine ⟨by omega, s0, mem_signList _, s1, mem_signList _, o1, ?_, ?_, a4⟩
    · simpa [Sign.mul_plus] using a7
    · rw [← ho0]; exact a3
  · rintro ⟨hn, ε0, -, ε1, -, t1, hp, e0, e1⟩
    refine ⟨⟨r + s - 3, ε0, T0, (r : ZMod 8) - s - t1 - 4 * ind8 (ε1 = .minus)⟩, ⟨3, ε1, .I, t1⟩,
      TwoFactor.trivial, TwoFactor.trivial,
      ⟨by simp [TwoFactor.trivial]; omega, by simp [TwoFactor.trivial], e0, e1, by decide, by decide, ?_, ?_⟩,
      rfl, rfl, rfl, rfl, trivial⟩
    · simpa [TwoFactor.trivial, Sign.mul_plus] using hp
    · simp [TwoFactor.trivial, ind8]; ring

theorem rhsC_tail (T0 : ScaledType) (Q : Sign → ZMod 8 → Prop) (n : ℕ) (hn : 4 ≤ n) (σ : ZMod 8) :
    RhsC T0 Q (n + 2) σ ↔ RhsC T0 Q n σ := by
  unfold RhsC
  have e : n + 2 - 1 = (n - 1) + 2 := by omega
  rw [e]
  simp only [exists_stable (n - 1) (by omega)]
  constructor
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩

theorem rhsD_tail (T0 : ScaledType) (n : ℕ) (hn : 5 ≤ n) (σ : ZMod 8) :
    RhsD T0 (n + 2) σ ↔ RhsD T0 n σ := by
  unfold RhsD
  have e : n + 2 - 2 = (n - 2) + 2 := by omega
  rw [e]
  simp only [exists_stable (n - 2) (by omega)]
  constructor
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩

theorem rhsE_tail (T0 : ScaledType) (n : ℕ) (hn : 6 ≤ n) (σ : ZMod 8) :
    RhsE T0 (n + 2) σ ↔ RhsE T0 n σ := by
  unfold RhsE
  have e : n + 2 - 3 = (n - 3) + 2 := by omega
  rw [e]
  simp only [exists_stable (n - 3) (by omega)]
  constructor
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩

/-! ### Table 15.4, rows $\lvert\det\rvert = 8$

$\sigma = (r - s) \bmod 8$, $n = r + s$. The four genera $\mathrm I_{r,s}(8_{\pm1})$, $\mathrm I_{r,s}(8_{\pm3})$ of the
book are distinguished by the sign $\varepsilon_3$ and the oddity $t_3$ of the constituent at the scale $8$ (the sign is
an invariant of its train, $t_3 + 4[\varepsilon_3 = -]$ of its compartment). -/

/-- **Table 15.4, $\pm8$, $\mathrm I_{r,s}(8_{+1})$** ($\varepsilon_3 = +$, $t_3 = 1$): exceptions $0$, $1$, $2_{-2}$,
$3_{-3}$ (the book: "$0, 1, 2_{\mp2}, 3_{\mp3}$"). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, I(8_{+1}))"]
theorem table154_eight_I_p1 (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 1 ∧
        ((G.two 3).sign = .plus ∧ (G.two 3).oddity = 1)) ↔
      (((r + s = 2 ∧ (((r : ZMod 8) - s).val = 0 ∨ ((r : ZMod 8) - s).val = 2)) ∨
        (r + s = 3 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 3 ∨ ((r : ZMod 8) - s).val = 7)) ∨
        (4 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2))) :=
  (det8_rowC .I (fun ε3 t3 => ε3 = .plus ∧ t3 = 1) r s).trans
    (explicit_of (RhsC .I (fun ε3 t3 => ε3 = .plus ∧ t3 = 1))
      (fun n σ => (n = 2 ∧ (σ.val = 0 ∨ σ.val = 2)) ∨ (n = 3 ∧ (σ.val = 1 ∨ σ.val = 3 ∨ σ.val = 7)) ∨
        (4 ≤ n ∧ σ.val % 2 = n % 2)) 4
      (fun n hn σ => rhsC_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm I_{r,s}(8_{-1})$** ($\varepsilon_3 = +$, $t_3 = 7$): exceptions $0$, $1$, $2_{+2}$,
$3_{+3}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, I(8_{-1}))"]
theorem table154_eight_I_m1 (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 1 ∧
        ((G.two 3).sign = .plus ∧ (G.two 3).oddity = 7)) ↔
      (((r + s = 2 ∧ (((r : ZMod 8) - s).val = 0 ∨ ((r : ZMod 8) - s).val = 6)) ∨
        (r + s = 3 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 5 ∨ ((r : ZMod 8) - s).val = 7)) ∨
        (4 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2))) :=
  (det8_rowC .I (fun ε3 t3 => ε3 = .plus ∧ t3 = 7) r s).trans
    (explicit_of (RhsC .I (fun ε3 t3 => ε3 = .plus ∧ t3 = 7))
      (fun n σ => (n = 2 ∧ (σ.val = 0 ∨ σ.val = 6)) ∨ (n = 3 ∧ (σ.val = 1 ∨ σ.val = 5 ∨ σ.val = 7)) ∨
        (4 ≤ n ∧ σ.val % 2 = n % 2)) 4
      (fun n hn σ => rhsC_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm I_{r,s}(8_{+3})$** ($\varepsilon_3 = -$, $t_3 = 3$): exceptions $0$, $1$, $2_0$,
$2_{-2}$, $3_{-1}$ (the book: "$0, 1, 2_0, 2_{\mp2}, 3_{\mp1}$"). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, I(8_{+3}))"]
theorem table154_eight_I_p3 (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 1 ∧
        ((G.two 3).sign = .minus ∧ (G.two 3).oddity = 3)) ↔
      (((r + s = 2 ∧ (((r : ZMod 8) - s).val = 2 ∨ ((r : ZMod 8) - s).val = 4)) ∨
        (r + s = 3 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 3 ∨ ((r : ZMod 8) - s).val = 5)) ∨
        (4 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2))) :=
  (det8_rowC .I (fun ε3 t3 => ε3 = .minus ∧ t3 = 3) r s).trans
    (explicit_of (RhsC .I (fun ε3 t3 => ε3 = .minus ∧ t3 = 3))
      (fun n σ => (n = 2 ∧ (σ.val = 2 ∨ σ.val = 4)) ∨ (n = 3 ∧ (σ.val = 1 ∨ σ.val = 3 ∨ σ.val = 5)) ∨
        (4 ≤ n ∧ σ.val % 2 = n % 2)) 4
      (fun n hn σ => rhsC_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm I_{r,s}(8_{-3})$** ($\varepsilon_3 = -$, $t_3 = 5$): exceptions $0$, $1$, $2_0$,
$2_{+2}$, $3_{+1}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, I(8_{-3}))"]
theorem table154_eight_I_m3 (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 1 ∧
        ((G.two 3).sign = .minus ∧ (G.two 3).oddity = 5)) ↔
      (((r + s = 2 ∧ (((r : ZMod 8) - s).val = 4 ∨ ((r : ZMod 8) - s).val = 6)) ∨
        (r + s = 3 ∧ (((r : ZMod 8) - s).val = 3 ∨ ((r : ZMod 8) - s).val = 5 ∨ ((r : ZMod 8) - s).val = 7)) ∨
        (4 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2))) :=
  (det8_rowC .I (fun ε3 t3 => ε3 = .minus ∧ t3 = 5) r s).trans
    (explicit_of (RhsC .I (fun ε3 t3 => ε3 = .minus ∧ t3 = 5))
      (fun n σ => (n = 2 ∧ (σ.val = 4 ∨ σ.val = 6)) ∨ (n = 3 ∧ (σ.val = 3 ∨ σ.val = 5 ∨ σ.val = 7)) ∨
        (4 ≤ n ∧ σ.val % 2 = n % 2)) 4
      (fun n hn σ => rhsC_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm{II}_{r,s}(8)$:** signature $\pm1$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, II(8))"]
theorem table154_eight_II_plus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 1 ∧ ((G.two 3).sign = .plus ∧ True)) ↔
      ((r + s) % 2 = 1 ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 7)) :=
  (det8_rowC .II (fun ε3 _ => ε3 = .plus ∧ True) r s).trans
    (explicit_of (RhsC .II (fun ε3 _ => ε3 = .plus ∧ True))
      (fun n σ => n % 2 = 1 ∧ (σ.val = 1 ∨ σ.val = 7)) 4
      (fun n hn σ => rhsC_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm{II}_{r,s}(8^{-1})$:** signature $\pm1$, exception $1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, II(8^{-1}))"]
theorem table154_eight_II_minus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 0 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 1 ∧ ((G.two 3).sign = .minus ∧ True)) ↔
      ((r + s) % 2 = 1 ∧ 3 ≤ r + s ∧ (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 7)) :=
  (det8_rowC .II (fun ε3 _ => ε3 = .minus ∧ True) r s).trans
    (explicit_of (RhsC .II (fun ε3 _ => ε3 = .minus ∧ True))
      (fun n σ => n % 2 = 1 ∧ 3 ≤ n ∧ (σ.val = 1 ∨ σ.val = 7)) 4
      (fun n hn σ => rhsC_tail _ _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by beta_reduce; decide) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm I_{r,s}(2\times4)$:** all signatures, exceptions $0$, $1$, $2$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, I(2×4))"]
theorem table154_eight_I_2x4 (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 1 ∧ (G.two 2).dim = 1 ∧ (G.two 3).dim = 0 ∧ True) ↔
      (3 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2) :=
  (det8_rowD .I r s).trans
    (explicit_of (RhsD .I) (fun n σ => 3 ≤ n ∧ σ.val % 2 = n % 2) 5
      (fun n hn σ => rhsD_tail _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by decide +kernel) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm{II}_{r,s}(2\times4)$:** even signatures, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, II(2×4))"]
theorem table154_eight_II_2x4 (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 1 ∧ (G.two 2).dim = 1 ∧ (G.two 3).dim = 0 ∧ True) ↔
      ((r + s) % 2 = 0 ∧ 2 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = 0) :=
  (det8_rowD .II r s).trans
    (explicit_of (RhsD .II) (fun n σ => n % 2 = 0 ∧ 2 ≤ n ∧ σ.val % 2 = 0) 5
      (fun n hn σ => rhsD_tail _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by decide +kernel) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm I_{r,s}(2^3)$:** all signatures, exceptions $0$, $1$, $2$, $3$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, I(2^3))"]
theorem table154_eight_I_2cube (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .I ∧
        (G.two 1).dim = 3 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 0 ∧ True) ↔
      (4 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2) :=
  (det8_rowE .I r s).trans
    (explicit_of (RhsE .I) (fun n σ => 4 ≤ n ∧ σ.val % 2 = n % 2) 6
      (fun n hn σ => rhsE_tail _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by decide +kernel) _ _)

/-- **Table 15.4, $\pm8$, $\mathrm{II}_{r,s}(2^3)$:** odd signatures, exception $1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±8, II(2^3))"]
theorem table154_eight_II_2cube (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 8 ∧ (G.two 0).type = .II ∧
        (G.two 1).dim = 3 ∧ (G.two 2).dim = 0 ∧ (G.two 3).dim = 0 ∧ True) ↔
      ((r + s) % 2 = 1 ∧ 3 ≤ r + s ∧ ((r : ZMod 8) - s).val % 2 = 1) :=
  (det8_rowE .II r s).trans
    (explicit_of (RhsE .II) (fun n σ => n % 2 = 1 ∧ 3 ≤ n ∧ σ.val % 2 = 1) 6
      (fun n hn σ => rhsE_tail _ n hn σ) (fun n hn σ => by constructor <;> intro h <;> omega)
      (by decide +kernel) _ _)

end QuadFormsKB.ConwaySloane
