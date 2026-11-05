/-
# Conway–Sloane, Ch. 15, §8.1: Table 15.4, the rows $\lvert\det\rvert = 2p$, $p = 3, 5$

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.1,
Theorem 12, Table 15.4 (p. 387) (`conwaysloane1999`).

Continuation of `SmallDetTables2.lean` (rows $\pm2$) to the determinants $\pm2p$ for an odd prime $p$: the 2-adic symbol
is $1_{t_0}^{\varepsilon_0(n-1)}2_{t_1}^{\varepsilon_11}$ as for $\pm2$ but now $\varepsilon_0\varepsilon_1 =
\left(\frac{\det/2}{2}\right)$ is not forced to be $+$, and the $p$-adic symbol is $1^{\pm(n-1)}p^{e1}$.

**Covered rows** (see the end of the file for the statements): the rows $\mathrm I_{r,s}(2\times p^{e})$ and
$\mathrm{II}_{r,s}(2\times p^{e})$ for $p = 3$ ($\lvert\det\rvert = 6$) and $p = 5$ ($\lvert\det\rvert = 10$), $e = \pm$, as
existence statements with explicit signatures/exceptions; uniqueness of the genus up to `MoveEquiv`
(`table154_twoP_unique`) for every odd prime $p$.
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables2
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### The 2-adic shape when $v_2(\det) = 1$ -/

/-- **The 2-adic symbol when $v_2(\det) = 1$**: scale $1$ of dimension $n-1$, scale $2$ of dimension $1$ (type I), all
other scales empty; $\varepsilon_0\varepsilon_1 = \left(\frac{\det/2}{2}\right)$ and the 2-adic oddity is
$t_0 + t_1 + 4[\varepsilon_1 = -]$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (2-adic shape for even determinant)"]
theorem GenusSymbolData.two_shape (G : GenusSymbolData) (hc : G.Conditions) (hv2 : padicValInt 2 G.det = 1) :
    (G.two 0).dim + 1 = G.n ∧ (G.two 1).dim = 1 ∧ (∀ k, 2 ≤ k → G.two k = TwoFactor.trivial) ∧
      (G.two 1).type = .I ∧ (G.two 0).sign.mul (G.two 1).sign = jacobiTwo (G.det / 2) ∧
      G.two.oddity G.N = (G.two 0).oddity + (G.two 1).oddity + 4 * ind8 ((G.two 1).sign = .minus) ∧
      (G.two 0).Exists ∧ (G.two 1).Exists := by
  obtain ⟨hs, hsg⟩ := hc.two_det
  rw [hv2] at hs
  have hsupp := hc.two_supp
  have hex := hc.two_exists
  have d2 : ∀ k, 2 ≤ k → (G.two k).dim = 0 := by
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
  have t2 : ∀ k, 2 ≤ k → G.two k = TwoFactor.trivial := by
    intro k hk
    obtain ⟨h32, -, -, -, hII⟩ := hex k
    have h1 : (G.two k).dim = 0 := d2 k hk
    obtain ⟨h2, h3⟩ := h32 h1
    have h4 : (G.two k).oddity = 0 := hII h2
    generalize G.two k = f at h1 h2 h3 h4
    obtain ⟨d, s, t, o⟩ := f
    dsimp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  have d1 : (G.two 1).dim = 1 := by
    have h : ∑ k ∈ range G.N, k * (G.two k).dim = 1 * (G.two 1).dim := by
      refine Finset.sum_eq_single 1 (fun k _ hk => ?_) (fun h1 => ?_)
      · rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have : k = 0 := by omega
          simp [this]
        · simp [d2 k hk2]
      · have : G.N ≤ 1 := by simpa using h1
        rw [hsupp 1 this]; simp [TwoFactor.trivial]
    rw [h] at hs
    omega
  have hN2 : 2 ≤ G.N := by
    by_contra h
    have h' : G.N ≤ 1 := by omega
    have := hsupp 1 h'
    rw [this] at d1
    simp [TwoFactor.trivial] at d1
  have hdimsum : (G.two 0).dim + 1 = G.n := by
    have h := hc.two_dim
    rw [sum_range_stable_nat (f := fun k => (G.two k).dim) (m := 2) (fun k hk => d2 k hk)
      (fun k hk => by rw [hsupp k hk]; rfl)] at h
    simpa [Finset.sum_range_succ, d1] using h
  have hsign : (G.two 0).sign.mul (G.two 1).sign = jacobiTwo (G.det / 2) := by
    rw [signProd_stable (fun k => (G.two k).sign) hN2
      (fun k hk => by simp [t2 k hk, TwoFactor.trivial]), hv2] at hsg
    simpa [signProd, Sign.plus_mul] using hsg
  refine ⟨hdimsum, d1, t2, (hex 1).typeI_of_odd (by omega), hsign, ?_, hex 0, hex 1⟩
  have hsupp2 : G.two.SupportedBelow 2 := fun k hk => t2 k hk
  rw [TwoSymbol.oddity_congr hsupp2 hN2]
  unfold TwoSymbol.oddity
  simp [Finset.sum_range_succ, ind8]
  ring

/-- **The $p$-adic symbol when $v_p(\det) = 1$** ($p$ odd): $1^{\pm(n-1)}p^{e1}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (p-adic shape, one factor p)"]
theorem GenusSymbolData.p_shape (G : GenusSymbolData) (hc : G.Conditions) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hvp : padicValInt p G.det = 1) :
    (G.odd p 0).dim + 1 = G.n ∧ (G.odd p 1).dim = 1 ∧ (∀ k, 2 ≤ k → G.odd p k = OddFactor.trivial) ∧
      (G.odd p 0).sign.mul (G.odd p 1).sign = Sign.ofInt (jacobiSym (G.det / p) p) ∧
      (G.odd p).pExcess p G.N = ((p : ZMod 8) - 1) + 4 * ind8 ((G.odd p 1).sign = .minus) ∧
      (G.odd p 0).Exists := by
  obtain ⟨hs, hsg⟩ := hc.odd_det p hp hp2
  rw [hvp] at hs
  have hsupp := hc.odd_supp p
  have hex := hc.odd_exists p hp hp2
  have d2 : ∀ k, 2 ≤ k → (G.odd p k).dim = 0 := by
    intro k hk
    by_cases hkN : k < G.N
    · have hle : k * (G.odd p k).dim ≤ ∑ k ∈ range G.N, k * (G.odd p k).dim :=
        Finset.single_le_sum (f := fun k => k * (G.odd p k).dim) (fun i _ => Nat.zero_le _) (mem_range.2 hkN)
      rw [hs] at hle
      by_contra hne
      have h1 : 1 ≤ (G.odd p k).dim := Nat.pos_of_ne_zero hne
      have := Nat.mul_le_mul hk h1
      omega
    · rw [hsupp k (not_lt.1 hkN)]; rfl
  have t2 : ∀ k, 2 ≤ k → G.odd p k = OddFactor.trivial := by
    intro k hk
    have h1 : (G.odd p k).dim = 0 := d2 k hk
    have h2 : (G.odd p k).sign = .plus := hex k h1
    generalize G.odd p k = f at h1 h2
    obtain ⟨d, s⟩ := f
    dsimp only at h1 h2
    subst h1 h2
    rfl
  have d1 : (G.odd p 1).dim = 1 := by
    have h : ∑ k ∈ range G.N, k * (G.odd p k).dim = 1 * (G.odd p 1).dim := by
      refine Finset.sum_eq_single 1 (fun k _ hk => ?_) (fun h1 => ?_)
      · rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have : k = 0 := by omega
          simp [this]
        · simp [d2 k hk2]
      · have : G.N ≤ 1 := by simpa using h1
        rw [hsupp 1 this]; simp [OddFactor.trivial]
    rw [h] at hs
    omega
  have hN2 : 2 ≤ G.N := by
    by_contra h
    have h' : G.N ≤ 1 := by omega
    have := hsupp 1 h'
    rw [this] at d1
    simp [OddFactor.trivial] at d1
  have hdimsum : (G.odd p 0).dim + 1 = G.n := by
    have h := hc.odd_dim p hp hp2
    rw [sum_range_stable_nat (f := fun k => (G.odd p k).dim) (m := 2) (fun k hk => d2 k hk)
      (fun k hk => by rw [hsupp k hk]; rfl)] at h
    simpa [Finset.sum_range_succ, d1] using h
  refine ⟨hdimsum, d1, t2, ?_, ?_, hex 0⟩
  · rw [signProd_stable (fun k => (G.odd p k).sign) hN2
      (fun k hk => by simp [t2 k hk, OddFactor.trivial]), hvp] at hsg
    simpa [signProd, Sign.plus_mul] using hsg
  · rw [OddSymbol.pExcess_congr p (σ := G.odd p) (N := 2) t2 hN2]
    unfold OddSymbol.pExcess
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d1]
    cases (G.odd p 1).sign <;> simp [ind8]

/-! ### The determinant $2p(-1)^s$ -/

theorem pf_two_mul (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 * p).primeFactors.filter (· ≠ 2) = {p} := by
  ext q
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hq, hdv, -⟩, hq2⟩
    rcases (Nat.Prime.dvd_mul hq).1 hdv with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h) hq2
    · exact (Nat.prime_dvd_prime_iff_eq hq hp).1 h
  · rintro rfl
    exact ⟨⟨hp, dvd_mul_left _ _, by have := hp.pos; omega⟩, hp2⟩

theorem natAbs_two_mul (p s : ℕ) : ((2 * (p : ℤ)) * (-1) ^ s).natAbs = 2 * p := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem padicValInt_2p_two (p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValInt 2 ((2 * (p : ℤ)) * (-1) ^ s) = 1 := by
  have hn : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  have hp0 : p ≠ 0 := hp.ne_zero
  simp only [padicValInt, natAbs_two_mul]
  rw [padicValNat.mul (by norm_num) hp0, padicValNat.eq_zero_of_not_dvd hn]
  simp

theorem padicValInt_2p_p (p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValInt p ((2 * (p : ℤ)) * (-1) ^ s) = 1 := by
  haveI := Fact.mk hp
  have hn : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hp0 : p ≠ 0 := hp.ne_zero
  simp only [padicValInt, natAbs_two_mul]
  rw [padicValNat.mul (by norm_num) hp0, padicValNat.eq_zero_of_not_dvd hn]
  simp

theorem padicValInt_2p_ne (q p s : ℕ) (hq : q.Prime) (hp : p.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    padicValInt q ((2 * (p : ℤ)) * (-1) ^ s) = 0 := by
  have h1 : ¬ q ∣ 2 := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
  have h2 : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h)
  have : ¬ q ∣ 2 * p := fun h => ((Nat.Prime.dvd_mul hq).1 h).elim h1 h2
  simp only [padicValInt, natAbs_two_mul]
  exact padicValNat.eq_zero_of_not_dvd this

/-- **The data forced by the conditions when $\lvert\det\rvert = 2p$** (Conway–Sloane, §8.1, Table 15.4, rows
$\pm6$, $\pm10$): the 2-adic symbol $1_{t_0}^{\varepsilon_0(n-1)}2_{t_1}^{\varepsilon_11}$ with
$\varepsilon_0\varepsilon_1 = \left(\frac{p(-1)^s}{2}\right)$, the $p$-adic symbol $1^{\pm(n-1)}p^{e1}$ with sign product
$\left(\frac{2(-1)^s}{p}\right)$, and the oddity formula. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±6, ±10)"]
theorem GenusSymbolData.det2p_part (G : GenusSymbolData) (hc : G.Conditions) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) {r s : ℕ} (hd : G.det.natAbs = 2 * p) (hr : G.real = ⟨r, s⟩) :
    (G.two 0).dim + 1 = r + s ∧ (G.two 1).dim = 1 ∧ (∀ k, 2 ≤ k → G.two k = TwoFactor.trivial) ∧
      (G.two 1).type = .I ∧ (G.two 0).sign.mul (G.two 1).sign = jacobiTwo ((p : ℤ) * (-1) ^ s) ∧
      (G.two 0).Exists ∧ (G.two 1).Exists ∧
      (G.odd p 0).dim + 1 = r + s ∧
      (G.odd p 0).sign.mul (G.odd p 1).sign = Sign.ofInt (jacobiSym (2 * (-1) ^ s) p) ∧ (G.odd p 0).Exists ∧
      (r : ZMod 8) - s + (((p : ZMod 8) - 1) + 4 * ind8 ((G.odd p 1).sign = .minus)) =
        (G.two 0).oddity + (G.two 1).oddity + 4 * ind8 ((G.two 1).sign = .minus) := by
  have hn : G.n = r + s := by rw [← hc.real_dim, hr]
  have hdet : G.det = 2 * ((p : ℤ) * (-1) ^ s) := by
    have := G.det_eq_of hc (m := 2 * p) (by have := hp.pos; omega) hd hr
    rw [this]; push_cast; ring
  have hv2 : padicValInt 2 G.det = 1 := by
    have := padicValInt_2p_two p s hp hp2
    rw [hdet]; rw [show (2 * ((p : ℤ) * (-1) ^ s)) = ((2 * (p : ℤ)) * (-1) ^ s) by push_cast; ring]
    exact this
  have hvp : padicValInt p G.det = 1 := by
    have := padicValInt_2p_p p s hp hp2
    rw [hdet]; rw [show (2 * ((p : ℤ) * (-1) ^ s)) = ((2 * (p : ℤ)) * (-1) ^ s) by push_cast; ring]
    exact this
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := G.two_shape hc hv2
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := G.p_shape hc p hp hp2 hvp
  have hd2 : G.det / 2 = (p : ℤ) * (-1) ^ s := by rw [hdet]; exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hdp : G.det / p = 2 * (-1) ^ s := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [hdet, show 2 * ((p : ℤ) * (-1) ^ s) = (p : ℤ) * (2 * (-1) ^ s) by ring]
    exact Int.mul_ediv_cancel_left _ hp0
  rw [hd2] at a5
  rw [hdp] at b4
  refine ⟨by omega, a2, a3, a4, a5, a7, a8, by omega, b4, b6, ?_⟩
  have h := hc.oddity_formula
  rw [hd, pf_two_mul p hp hp2, Finset.sum_singleton, b5, a6] at h
  have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
  rw [hsig] at h
  exact h

/-- $\left(\frac{2(-1)^s}{p}\right)$ as a sign, in closed form: $\left(\frac{2}{p}\right)\left(\frac{-1}{p}\right)^s$. -/
theorem ofInt_J2 (p s : ℕ) (hp : p % 2 = 1) :
    Sign.ofInt (jacobiSym (2 * (-1 : ℤ) ^ s) p) = (jacobiTwo (p : ℤ)).mul (negSignAt p s) := by
  have h2 : jacobiSym 2 p = ZMod.χ₈ (p : ZMod 8) := jacobiSym.at_two (Nat.odd_iff.2 hp)
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  have hj2 : jacobiTwo (p : ℤ) = if p % 8 = 1 ∨ p % 8 = 7 then .plus else .minus := by
    unfold jacobiTwo
    split_ifs <;> first | rfl | omega
  rw [jacobiSym.mul_left, h2, ZMod.χ₈_nat_eq_if_mod_eight, hj2]
  rcases Nat.even_or_odd s with he | ho
  · have : ¬ Odd s := Nat.not_odd_iff_even.2 he
    rcases h8 with h | h | h | h <;>
      simp [he.neg_one_pow, negSignAt, this, Sign.ofInt, Sign.mul, Sign.flip, hp, h]
  · have hj : jacobiSym (-1) p = ZMod.χ₄ (p : ZMod 4) := jacobiSym.at_neg_one (Nat.odd_iff.2 hp)
    rcases h8 with h | h | h | h
    · rw [ho.neg_one_pow, hj, ZMod.χ₄_nat_one_mod_four (by omega)]
      simp [negSignAt, Sign.ofInt, Sign.mul, Sign.flip, hp, h, show p % 4 = 1 by omega]
    · rw [ho.neg_one_pow, hj, ZMod.χ₄_nat_three_mod_four (by omega)]
      simp [negSignAt, Sign.ofInt, Sign.mul, Sign.flip, hp, h, ho, show p % 4 = 3 by omega]
    · rw [ho.neg_one_pow, hj, ZMod.χ₄_nat_one_mod_four (by omega)]
      simp [negSignAt, Sign.ofInt, Sign.mul, Sign.flip, hp, h, show p % 4 = 1 by omega]
    · rw [ho.neg_one_pow, hj, ZMod.χ₄_nat_three_mod_four (by omega)]
      simp [negSignAt, Sign.ofInt, Sign.mul, Sign.flip, hp, h, ho, show p % 4 = 3 by omega]

/-! ### The system of symbols for $\lvert\det\rvert = 2p$ -/

/-- **The system of symbols for $\lvert\det\rvert = 2p$**: determinant $2p(-1)^s$, $(-1)$-adic symbol $+^r-^s$,
$p$-adic symbol $1^{\varepsilon(n-1)}p^{e1}$ with $\varepsilon$ forced by (29), symbols $1^{\varepsilon n}$ at the other
odd primes, and 2-adic symbol $1_{t_0}^{\varepsilon_0(n-1)}2_{t_1}^{\varepsilon_11}$ with the scale-1 constituent of
type `T`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±6, ±10)"]
def det2pData (p r s : ℕ) (e ε0 ε1 : Sign) (T : ScaledType) (t0 t1 : ZMod 8) : GenusSymbolData where
  n := r + s
  det := (2 * (p : ℤ)) * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q k =>
    if q = p then
      (if k = 0 then ⟨r + s - 1, (Sign.ofInt (jacobiSym (2 * (-1) ^ s) p)).mul e⟩
       else if k = 1 then ⟨1, e⟩ else OddFactor.trivial)
    else (if k = 0 then ⟨r + s, Sign.ofInt (jacobiSym ((2 * (p : ℤ)) * (-1) ^ s) q)⟩
      else OddFactor.trivial)
  two := fun k =>
    if k = 0 then ⟨r + s - 1, ε0, T, t0⟩ else if k = 1 then ⟨1, ε1, .I, t1⟩ else TwoFactor.trivial
  N := 2

theorem det2pData_conditions (p r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (e ε0 ε1 : Sign) (T : ScaledType)
    (t0 t1 : ZMod 8) (hn : 1 ≤ r + s)
    (hcompat : r + s = 1 → e = Sign.ofInt (jacobiSym (2 * (-1) ^ s) p))
    (hsg : ε0.mul ε1 = jacobiTwo ((p : ℤ) * (-1) ^ s))
    (h0 : (⟨r + s - 1, ε0, T, t0⟩ : TwoFactor).Exists) (h1 : (⟨1, ε1, .I, t1⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s + (((p : ZMod 8) - 1) + 4 * ind8 (e = .minus)) =
      t0 + t1 + 4 * ind8 (ε1 = .minus)) :
    (det2pData p r s e ε0 ε1 T t0 t1).Conditions where
  ne_zero := mul_ne_zero (by have := hp.pos; positivity) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    have hpos : (0 : ℤ) < (2 * (p : ℤ)) := by have := hp.pos; positivity
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp only [det2pData, h.neg_one_pow, this, mul_one, iff_false, not_lt]
      exact hpos.le
    · simp only [det2pData, h.neg_one_pow, h, mul_neg, mul_one, iff_true]
      linarith
  odd_supp q k hk := by
    have hk' : 2 ≤ k := hk
    by_cases hq : q = p
    · simp [det2pData, hq, show k ≠ 0 by omega, show k ≠ 1 by omega]
    · simp [det2pData, hq, show k ≠ 0 by omega]
  two_supp k hk := by
    have hk' : 2 ≤ k := hk
    simp [det2pData, show k ≠ 0 by omega, show k ≠ 1 by omega]
  odd_dim q _ _ := by
    by_cases hq : q = p
    · simp [det2pData, hq, Finset.sum_range_succ]
      omega
    · simp [det2pData, hq, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by
    simp [det2pData, Finset.sum_range_succ]
    omega
  odd_det q hq hq2 := by
    by_cases h3 : q = p
    · subst h3
      refine ⟨?_, ?_⟩
      · simp [det2pData, padicValInt_2p_p q s hq hp2, Finset.sum_range_succ]
      · have hd : ((2 * (q : ℤ)) * (-1) ^ s) / (q : ℤ) = 2 * (-1) ^ s := by
          have hp0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
          rw [show ((2 * (q : ℤ)) * (-1) ^ s) = (q : ℤ) * (2 * (-1) ^ s) by push_cast; ring]
          exact Int.mul_ediv_cancel_left _ hp0
        simp [det2pData, padicValInt_2p_p q s hq hp2, signProd, hd, Sign.plus_mul, Sign.mul_mul_self]
    · refine ⟨?_, ?_⟩
      · simp [det2pData, h3, padicValInt_2p_ne q p s hq hp hq2 h3, Finset.sum_range_succ, OddFactor.trivial]
      · simp [det2pData, h3, padicValInt_2p_ne q p s hq hp hq2 h3, signProd, Sign.plus_mul, Sign.mul_plus,
          OddFactor.trivial]
  two_det := by
    have hv := padicValInt_2p_two p s hp hp2
    refine ⟨by simp [det2pData, hv, Finset.sum_range_succ, TwoFactor.trivial], ?_⟩
    have hd : ((2 * (p : ℤ)) * (-1) ^ s) / 2 = (p : ℤ) * (-1) ^ s := by
      rw [show ((2 * (p : ℤ)) * (-1) ^ s) = 2 * ((p : ℤ) * (-1) ^ s) by push_cast; ring]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    simp [det2pData, hv, signProd, hd, Sign.plus_mul, Sign.mul_plus, TwoFactor.trivial, hsg]
  odd_exists q hq hq2 k := by
    by_cases h3 : q = p
    · subst h3
      by_cases hk0 : k = 0
      · subst hk0
        simp only [det2pData, if_true]
        intro h0'
        have h0'' : r + s - 1 = 0 := h0'
        rw [hcompat (by omega)]
        exact Sign.mul_self_eq _
      · by_cases hk1 : k = 1
        · subst hk1
          intro h0'
          have : (1 : ℕ) = 0 := by simpa [det2pData] using h0'
          omega
        · simp [det2pData, hk0, hk1, OddFactor.Exists, OddFactor.trivial]
    · by_cases hk0 : k = 0
      · subst hk0
        simp only [det2pData, h3, if_true, if_false]
        intro h0'
        have h0'' : r + s = 0 := h0'
        omega
      · simp [det2pData, h3, hk0, OddFactor.Exists, OddFactor.trivial]
  two_exists k := by
    by_cases hk : k = 0
    · subst hk; simpa [det2pData] using h0
    · by_cases hk1 : k = 1
      · subst hk1; simpa [det2pData] using h1
      · simp only [det2pData, if_neg hk, if_neg hk1]
        decide
  oddity_formula := by
    have hna : (det2pData p r s e ε0 ε1 T t0 t1).det.natAbs = 2 * p := by
      simp [det2pData, natAbs_two_mul]
    rw [hna, pf_two_mul p hp hp2, Finset.sum_singleton]
    simp only [det2pData, if_true]
    unfold OddSymbol.pExcess TwoSymbol.oddity GenusSymbolData.signature
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [ind8, TwoFactor.trivial]
    cases e <;> cases ε1 <;> simp [ind8] at ht ⊢ <;> linear_combination ht

theorem det2p_exists_of (p r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (e ε0 ε1 : Sign) (T : ScaledType)
    (t0 t1 : ZMod 8) (hn : 1 ≤ r + s)
    (hcompat : r + s = 1 → e = Sign.ofInt (jacobiSym (2 * (-1) ^ s) p))
    (hsg : ε0.mul ε1 = jacobiTwo ((p : ℤ) * (-1) ^ s))
    (h0 : (⟨r + s - 1, ε0, T, t0⟩ : TwoFactor).Exists) (h1 : (⟨1, ε1, .I, t1⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s + (((p : ZMod 8) - 1) + 4 * ind8 (e = .minus)) =
      t0 + t1 + 4 * ind8 (ε1 = .minus)) :
    ∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 * p ∧ (G.two 0).type = T ∧
      (G.odd p 1).sign = e :=
  ⟨det2pData p r s e ε0 ε1 T t0 t1, det2pData_conditions p r s hp hp2 e ε0 ε1 T t0 t1 hn hcompat hsg h0 h1 ht,
    rfl, by simp [det2pData, natAbs_two_mul], by simp [det2pData], by simp [det2pData]⟩

/-- The list of the two signs, for decidable existential statements. -/
def signList : List Sign := [.plus, .minus]

/-- **The right-hand side for the rows $\mathrm I/\mathrm{II}_{r,s}(2\times p^{e})$**: $n \ge 1$; for $n = 1$ the
$p$-adic $1^{\pm0}$ constituent has sign $+$; and the 2-adic constituents $1_{t_0}^{\varepsilon_0(n-1)}$ (type `T`) and
$2_{t_1}^{\varepsilon_11}$ exist with $\varepsilon_0\varepsilon_1 = \left(\frac{p(-1)^s}{2}\right)$ and the oddity
formula (signature $+$ $p$-excess $=$ oddity). -/
def Rhs2p (p r s : ℕ) (e : Sign) (T : ScaledType) : Prop :=
  1 ≤ r + s ∧ (r + s = 1 → e = (jacobiTwo (p : ℤ)).mul (negSignAt p s)) ∧
    ∃ ε0 ∈ signList, ∃ ε1 ∈ signList, ∃ t0 t1 : ZMod 8,
      ε0.mul ε1 = jacobiTwo ((p : ℤ) * (-1) ^ s) ∧ (⟨r + s - 1, ε0, T, t0⟩ : TwoFactor).Exists ∧
      (⟨1, ε1, .I, t1⟩ : TwoFactor).Exists ∧
      (r : ZMod 8) - s + (((p : ZMod 8) - 1) + 4 * ind8 (e = .minus)) = t0 + t1 + 4 * ind8 (ε1 = .minus)

set_option synthInstance.maxSize 1024 in
instance (p r s : ℕ) (e : Sign) (T : ScaledType) : Decidable (Rhs2p p r s e T) := by
  unfold Rhs2p; infer_instance

theorem mem_signList (x : Sign) : x ∈ signList := by cases x <;> simp [signList]

/-- **Existence for $\lvert\det\rvert = 2p$** (Conway–Sloane, §8.1, Table 15.4, rows $\pm6$, $\pm10$): a system of
symbols satisfying the conditions with $\lvert\det\rvert = 2p$, $(-1)$-adic symbol $+^r-^s$, scale-1 2-adic type `T`
and $p$-adic constituent $p^{e1}$ exists iff `Rhs2p p r s e T`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±6, ±10)"]
theorem table154_twoP (p r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (e : Sign) (T : ScaledType) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 * p ∧ (G.two 0).type = T ∧
        (G.odd p 1).sign = e) ↔ Rhs2p p r s e T := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  constructor
  · rintro ⟨G, hc, hr, hd, hT, he⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, b1, b4, b6, hodd⟩ := G.det2p_part hc p hp hp2 hd hr
    refine ⟨by omega, fun hn => ?_, ?_⟩
    · have h0 : (G.odd p 0).dim = 0 := by omega
      have hs0 : (G.odd p 0).sign = .plus := b6 h0
      rw [hs0, Sign.plus_mul, he, ofInt_J2 p s hpodd] at b4
      exact b4
    · refine ⟨(G.two 0).sign, mem_signList _, (G.two 1).sign, mem_signList _, (G.two 0).oddity,
        (G.two 1).oddity, a5, ?_, ?_, ?_⟩
      · have : (G.two 0) = ⟨r + s - 1, (G.two 0).sign, T, (G.two 0).oddity⟩ := by
          generalize G.two 0 = f at a1 hT
          obtain ⟨d, sg, ty, o⟩ := f
          dsimp only at a1 hT ⊢
          subst hT
          congr 1
          omega
        rw [← this]; exact a6
      · have : (G.two 1) = ⟨1, (G.two 1).sign, .I, (G.two 1).oddity⟩ := by
          generalize G.two 1 = f at a2 a4
          obtain ⟨d, sg, ty, o⟩ := f
          dsimp only at a2 a4 ⊢
          subst a2 a4
          rfl
        rw [← this]; exact a7
      · rw [he] at hodd; exact hodd
  · rintro ⟨hn, hcompat, ε0, -, ε1, -, t0, t1, hsg, h0, h1, ht⟩
    exact det2p_exists_of p r s hp hp2 e ε0 ε1 T t0 t1 hn
      (fun h => by rw [ofInt_J2 p s hpodd]; exact hcompat h) hsg h0 h1 ht

/-- The oddity target $r - s + (p-1) + 4[e = -]$ for the rows $2\times p^{e}$. -/
def target2p (p r s : ℕ) (e : Sign) : ℤ := (r : ℤ) - s + ((p : ℤ) - 1) + (if e = .minus then 4 else 0)

theorem rhs2p_II_necessary (p r s : ℕ) (e : Sign) (h : Rhs2p p r s e .II) :
    target2p p r s e % 8 = 1 ∨ target2p p r s e % 8 = 7 := by
  obtain ⟨-, -, ε0, -, ε1, -, t0, t1, -, h0, h1, ht⟩ := h
  have h0' : t0 = 0 := h0.2.2.2.2 rfl
  have hv := exists1_values ε1 t1 h1
  have hc : ∀ c : ℤ, (r : ZMod 8) - s + (((p : ZMod 8) - 1) + 4 * ind8 (e = .minus)) = (c : ZMod 8) →
      (target2p p r s e - c) % 8 = 0 := by
    intro c hc
    have : (((target2p p r s e - c : ℤ)) : ZMod 8) = 0 := by
      unfold target2p
      cases e <;> simp [ind8] at hc ⊢ <;> linear_combination hc
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    omega
  rcases hv with hv | hv
  · left
    have := hc 1 (by rw [ht, h0', zero_add]; simpa using hv)
    omega
  · right
    have := hc 7 (by rw [ht, h0', zero_add]; simpa using hv)
    omega

theorem rhs2p_typeI_big (p r s : ℕ) (hp1 : p % 2 = 1) (e : Sign) (h : 4 ≤ r + s) : Rhs2p p r s e .I := by
  refine ⟨by omega, fun hn => by omega, jacobiTwo ((p : ℤ) * (-1) ^ s), mem_signList _, .plus, mem_signList _,
    (((target2p p r s e - 1 : ℤ)) : ZMod 8), 1, ?_, ?_, by decide, ?_⟩
  · cases jacobiTwo ((p : ℤ) * (-1) ^ s) <;> rfl
  · apply typeI_big _ _ _ (by omega)
    have := ZMod.val_intCast (n := 8) (target2p p r s e - 1)
    have hT : target2p p r s e = (r : ℤ) - s + ((p : ℤ) - 1) + (if e = .minus then 4 else 0) := rfl
    split_ifs at hT <;> omega
  · unfold target2p
    cases e <;> simp [ind8] <;> push_cast <;> ring

theorem rhs2p_typeII_big (p r s : ℕ) (e : Sign) (h : 3 ≤ r + s)
    (hpar : (r + s) % 2 = 1) (ht : target2p p r s e % 8 = 1 ∨ target2p p r s e % 8 = 7) :
    Rhs2p p r s e .II := by
  have hE0 : ∀ ε : Sign, (⟨r + s - 1, ε, .II, 0⟩ : TwoFactor).Exists := by
    intro ε
    refine ⟨fun h0 => ?_, fun h1 => ?_, (fun _ hI => by cases hI), ?_, fun _ => rfl⟩
    · have h0' : r + s - 1 = 0 := h0
      omega
    · have h1' : r + s - 1 = 1 := h1
      omega
    · show (0 : ZMod 8).val % 2 = (r + s - 1) % 2
      simp
      omega
  have hv : (((target2p p r s e : ℤ)) : ZMod 8) = 1 ∨ (((target2p p r s e : ℤ)) : ZMod 8) = 7 := by
    rcases ht with ht | ht
    · left
      have : (((target2p p r s e - 1 : ℤ)) : ZMod 8) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
      push_cast at this ⊢
      linear_combination this
    · right
      have : (((target2p p r s e - 7 : ℤ)) : ZMod 8) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
      push_cast at this ⊢
      linear_combination this
  refine ⟨by omega, fun hn => by omega, jacobiTwo ((p : ℤ) * (-1) ^ s), mem_signList _, .plus, mem_signList _,
    0, (((target2p p r s e : ℤ)) : ZMod 8), ?_, hE0 _, ?_, ?_⟩
  · cases jacobiTwo ((p : ℤ) * (-1) ^ s) <;> rfl
  · rcases hv with hv | hv <;> rw [hv] <;> decide
  · unfold target2p
    cases e <;> simp [ind8] <;> push_cast <;> ring

theorem rhs2p_I_iff_of (p : ℕ) (e : Sign) (hp1 : p % 2 = 1)
    (hsmall : ∀ r, r ≤ 3 → ∀ s, s ≤ 3 → r + s < 4 → (Rhs2p p r s e .I ↔ 2 ≤ r + s)) (r s : ℕ) :
    Rhs2p p r s e .I ↔ 2 ≤ r + s := by
  by_cases h : 4 ≤ r + s
  · exact ⟨fun _ => by omega, fun _ => rhs2p_typeI_big p r s hp1 e h⟩
  · exact hsmall r (by omega) s (by omega) (by omega)

theorem rhs2p_II_iff_of (p : ℕ) (e : Sign) (hp1 : p % 2 = 1) (P : ℕ → ℕ → Prop)
    (hsmall : ∀ r, r ≤ 2 → ∀ s, s ≤ 2 → r + s ≤ 2 → (Rhs2p p r s e .II ↔ P r s))
    (hbig : ∀ r s, 3 ≤ r + s → (P r s ↔ ((r + s) % 2 = 1 ∧
      (target2p p r s e % 8 = 1 ∨ target2p p r s e % 8 = 7)))) (r s : ℕ) :
    Rhs2p p r s e .II ↔ P r s := by
  by_cases h : 3 ≤ r + s
  · rw [hbig r s h]
    constructor
    · intro hR
      have := rhs2p_II_necessary p r s e hR
      refine ⟨?_, this⟩
      have hT : target2p p r s e = (r : ℤ) - s + ((p : ℤ) - 1) + (if e = .minus then 4 else 0) := rfl
      split_ifs at hT <;> omega
    · rintro ⟨hpar, ht⟩
      exact rhs2p_typeII_big p r s e h hpar ht
  · exact hsmall r (by omega) s (by omega) (by omega)

/-! ### Table 15.4, rows $\pm6$ and $\pm10$ -/

/-- **Table 15.4, $\pm6$, $\mathrm I_{r,s}(2\times3)$:** all signatures, exceptions $0$, $1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±6, I(2×3))"]
theorem table154_six_typeI_plus (r s : ℕ) : Rhs2p 3 r s .plus .I ↔ 2 ≤ r + s :=
  rhs2p_I_iff_of 3 .plus (by norm_num) (by decide) r s

/-- **Table 15.4, $\pm6$, $\mathrm I_{r,s}(2\times3^{-1})$:** all signatures, exceptions $0$, $1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±6, I(2×3^{-1}))"]
theorem table154_six_typeI_minus (r s : ℕ) : Rhs2p 3 r s .minus .I ↔ 2 ≤ r + s :=
  rhs2p_I_iff_of 3 .minus (by norm_num) (by decide) r s

/-- **Table 15.4, $\pm10$, $\mathrm I_{r,s}(2\times5)$:** all signatures, exceptions $0$, $1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±10, I(2×5))"]
theorem table154_ten_typeI_plus (r s : ℕ) : Rhs2p 5 r s .plus .I ↔ 2 ≤ r + s :=
  rhs2p_I_iff_of 5 .plus (by norm_num) (by decide) r s

/-- **Table 15.4, $\pm10$, $\mathrm I_{r,s}(2\times5^{-1})$:** all signatures, exceptions $0$, $1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±10, I(2×5^{-1}))"]
theorem table154_ten_typeI_minus (r s : ℕ) : Rhs2p 5 r s .minus .I ↔ 2 ≤ r + s :=
  rhs2p_I_iff_of 5 .minus (by norm_num) (by decide) r s

/-- **Table 15.4, $\pm6$, $\mathrm{II}_{r,s}(2\times3)$:** signatures $\equiv 5, 7 \pmod 8$ (the book lists the pair
$\mathrm{II}_{r,s}(2\times3^{\pm1})$ as "odd", the two signs $e$ together covering all odd signatures).

*Note on the book's exceptions "$1_{\pm1}$" for this row.* The $\pm$ of the exception is paired with the $\pm$ of
$3^{\pm1}$: for $3^{+1}$ the case $n = 1$, $r - s = +1$ is excluded, and for $3^{-1}$ the case $n = 1$, $r - s = -1$.
With the signature sets derived here ($\{5,7\}$ for $3^{+1}$, $\{1,3\}$ for $3^{-1}$ modulo $8$) these two cases already
lie outside the allowed classes, so there is no conflict with the book. The $n = 1$ genera that do exist are
$\langle 6\rangle \in \mathrm{II}_{1,0}(2\times3^{-1})$ (signature $+1$) and
$\langle -6\rangle \in \mathrm{II}_{0,1}(2\times3^{+1})$ (signature $-1$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±6, II(2×3))"]
theorem table154_six_typeII_plus (r s : ℕ) :
    Rhs2p 3 r s .plus .II ↔ (((r : ℤ) - s) % 8 = 5 ∨ ((r : ℤ) - s) % 8 = 7) :=
  rhs2p_II_iff_of 3 .plus (by norm_num) (fun r s => ((r : ℤ) - s) % 8 = 5 ∨ ((r : ℤ) - s) % 8 = 7)
    (by beta_reduce; decide) (fun r s _ => by simp [target2p]; omega) r s

/-- **Table 15.4, $\pm6$, $\mathrm{II}_{r,s}(2\times3^{-1})$:** signatures $\equiv 1, 3 \pmod 8$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±6, II(2×3^{-1}))"]
theorem table154_six_typeII_minus (r s : ℕ) :
    Rhs2p 3 r s .minus .II ↔ (((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 3) :=
  rhs2p_II_iff_of 3 .minus (by norm_num) (fun r s => ((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 3)
    (by beta_reduce; decide) (fun r s _ => by simp [target2p]; omega) r s

/-- **Table 15.4, $\pm10$, $\mathrm{II}_{r,s}(2\times5)$:** signature $\pm3$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±10, II(2×5))"]
theorem table154_ten_typeII_plus (r s : ℕ) :
    Rhs2p 5 r s .plus .II ↔ (((r : ℤ) - s) % 8 = 3 ∨ ((r : ℤ) - s) % 8 = 5) :=
  rhs2p_II_iff_of 5 .plus (by norm_num) (fun r s => ((r : ℤ) - s) % 8 = 3 ∨ ((r : ℤ) - s) % 8 = 5)
    (by beta_reduce; decide) (fun r s _ => by simp [target2p]; omega) r s

/-- **Table 15.4, $\pm10$, $\mathrm{II}_{r,s}(2\times5^{-1})$:** signature $\pm1$, no exceptions (for $n = 1$ the book
reads this genus as $\mathrm{II}_{r,s}(2^{-1}\times5^{-1})$, the asterisk of the table). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±10, II(2×5^{-1}))"]
theorem table154_ten_typeII_minus (r s : ℕ) :
    Rhs2p 5 r s .minus .II ↔ (((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 7) :=
  rhs2p_II_iff_of 5 .minus (by norm_num) (fun r s => ((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 7)
    (by beta_reduce; decide) (fun r s _ => by simp [target2p]; omega) r s

/-! ### Uniqueness of the genus for $\lvert\det\rvert = 2p$ -/

theorem two1_isTypeI_iff (G : GenusSymbolData) (hc : G.Conditions) (hv2 : padicValInt 2 G.det = 1) (k : ℕ) :
    IsTypeI G.two k ↔ k = 1 ∨ (k = 0 ∧ (G.two 0).type = .I) := by
  obtain ⟨-, -, t2, ht1, -⟩ := G.two_shape hc hv2
  by_cases hk0 : k = 0
  · subst hk0; simp [IsTypeI]
  by_cases hk1 : k = 1
  · subst hk1; simpa [IsTypeI] using ht1
  · have hk : 2 ≤ k := by omega
    simp [IsTypeI, t2 k hk, TwoFactor.trivial, hk0, hk1]

theorem two1_compartments (G : GenusSymbolData) (hc : G.Conditions) (hv2 : padicValInt 2 G.det = 1) {c₁ c₂ : ℕ}
    (h : IsCompartment G.two c₁ c₂) :
    (c₁ = 0 ∧ c₂ = 1 ∧ (G.two 0).type = .I) ∨ (c₁ = 1 ∧ c₂ = 1 ∧ (G.two 0).type = .II) := by
  obtain ⟨hle, hall, hstart, hend⟩ := h
  have hI := two1_isTypeI_iff G hc hv2
  by_cases hT : (G.two 0).type = .I
  · have h1 : ¬ IsTypeI G.two (c₂ + 1) := hend
    rw [hI] at h1
    have h2 := hall c₂ (by omega) le_rfl
    rw [hI] at h2
    have hc2 : c₂ = 1 := by
      rcases h2 with h2 | h2
      · exact h2
      · exfalso; apply h1; right; exact ⟨by omega, hT⟩
    have hc1 : c₁ = 0 := by
      rcases hstart with h | h
      · exact h
      · exfalso; apply h; rw [hI]; right; exact ⟨by omega, hT⟩
    left; exact ⟨hc1, hc2, hT⟩
  · have hT' : (G.two 0).type = .II := by
      cases h : (G.two 0).type
      · exact absurd h hT
      · rfl
    have h1 : ¬ IsTypeI G.two (c₂ + 1) := hend
    rw [hI] at h1
    have h2 := hall c₂ (by omega) le_rfl
    rw [hI] at h2
    have hc2 : c₂ = 1 := by
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd h2.2 hT
    have hc1 : c₁ = 1 := by
      have h3 := hall c₁ le_rfl hle
      rw [hI] at h3
      rcases h3 with h3 | h3
      · exact h3
      · exact absurd h3.2 hT
    right; exact ⟨hc1, hc2, hT'⟩

theorem two1_compInv (G : GenusSymbolData) (hc : G.Conditions) (hv2 : padicValInt 2 G.det = 1) {c₁ c₂ : ℕ}
    (h : IsCompartment G.two c₁ c₂) :
    compartmentInvariant G.two c₁ c₂ =
      (G.two 0).oddity + (G.two 1).oddity + 4 * ind8 ((G.two 1).sign = .minus) := by
  obtain ⟨-, -, -, -, -, -, hE0, -⟩ := G.two_shape hc hv2
  have e12 : Finset.Icc 1 2 = {1, 2} := by decide
  have e02 : Finset.Icc 0 2 = {0, 1, 2} := by decide
  have e01 : Finset.Icc 0 1 = {0, 1} := by decide
  have e11 : Finset.Icc 1 1 = {1} := by decide
  rcases two1_compartments G hc hv2 h with ⟨rfl, rfl, hT⟩ | ⟨rfl, rfl, hT⟩
  · simp only [compartmentInvariant, e01, e02]
    simp [minusBelow, ind8]
    cases (G.two 0).sign <;> cases (G.two 1).sign <;> simp <;> ring_nf <;> decide
  · have h0 : (G.two 0).oddity = 0 := hE0.2.2.2.2 hT
    simp only [compartmentInvariant, e11, e12]
    simp [minusBelow, ind8, h0]
    cases (G.two 0).sign <;> cases (G.two 1).sign <;> simp <;> ring_nf <;> decide

theorem two1_minusBelow (G : GenusSymbolData) (hc : G.Conditions) (hv2 : padicValInt 2 G.det = 1) :
    ∀ m, 2 ≤ m → minusBelow G.two m =
      (if (G.two 0).sign = .minus then 1 else 0) + (if (G.two 1).sign = .minus then 1 else 0) := by
  obtain ⟨-, -, t2, -, -, -, -, -⟩ := G.two_shape hc hv2
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp [minusBelow]
  | succ m hm ih =>
    rw [minusBelow, ih, t2 m hm]
    simp [TwoFactor.trivial]

theorem det2p_vals (G : GenusSymbolData) (hc : G.Conditions) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {r s : ℕ}
    (hd : G.det.natAbs = 2 * p) (hr : G.real = ⟨r, s⟩) :
    G.det = 2 * (p : ℤ) * (-1) ^ s ∧ padicValInt 2 G.det = 1 ∧ padicValInt p G.det = 1 := by
  have hdet : G.det = 2 * (p : ℤ) * (-1) ^ s := by
    have := G.det_eq_of hc (m := 2 * p) (by have := hp.pos; omega) hd hr
    rw [this]; push_cast; ring
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet]; exact padicValInt_2p_two p s hp hp2
  · rw [hdet]; exact padicValInt_2p_p p s hp hp2

theorem odd_p_form (G : GenusSymbolData) (hc : G.Conditions) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {r s : ℕ}
    (hd : G.det.natAbs = 2 * p) (hr : G.real = ⟨r, s⟩) (k : ℕ) :
    G.odd p k = if k = 0 then ⟨r + s - 1, (Sign.ofInt (jacobiSym (2 * (-1) ^ s) p)).mul (G.odd p 1).sign⟩
      else if k = 1 then ⟨1, (G.odd p 1).sign⟩ else OddFactor.trivial := by
  obtain ⟨-, -, hvp⟩ := det2p_vals G hc p hp hp2 hd hr
  obtain ⟨b1, b2, b3, b4, -, -⟩ := G.p_shape hc p hp hp2 hvp
  have hdet := (det2p_vals G hc p hp hp2 hd hr).1
  have hn : G.n = r + s := by rw [← hc.real_dim, hr]
  have hdp : G.det / p = 2 * (-1) ^ s := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [hdet, show 2 * (p : ℤ) * (-1) ^ s = (p : ℤ) * (2 * (-1) ^ s) by ring]
    exact Int.mul_ediv_cancel_left _ hp0
  rw [hdp] at b4
  by_cases hk0 : k = 0
  · subst hk0
    simp only [if_true]
    have hs0 : (G.odd p 0).sign = (Sign.ofInt (jacobiSym (2 * (-1) ^ s) p)).mul (G.odd p 1).sign := by
      rw [← b4]
      cases (G.odd p 0).sign <;> cases (G.odd p 1).sign <;> rfl
    generalize G.odd p 0 = f at b1 hs0
    obtain ⟨d, sg⟩ := f
    dsimp only at b1 hs0
    rw [hs0]
    congr 1
    omega
  · by_cases hk1 : k = 1
    · subst hk1
      simp only [if_neg hk0, if_true]
      generalize G.odd p 1 = f at b2
      obtain ⟨d, sg⟩ := f
      dsimp only at b2
      rw [b2]
    · simp only [if_neg hk0, if_neg hk1]
      exact b3 k (by omega)

/-- **Uniqueness of the genus for $\lvert\det\rvert = 2p$** (Conway–Sloane, §8.1, Table 15.4, rows $\pm6$, $\pm10$):
two systems satisfying the conditions with equal $(-1)$-adic symbols, equal types of the scale-1 2-adic constituent
and equal sign of $p^{e1}$ have equal $p$-adic symbols at all odd primes and $\texttt{MoveEquiv}$-related 2-adic
symbols: one genus for each $(r, s, T, e)$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±6, ±10: one genus for each (r,s), type and sign)"]
theorem table154_twoP_unique (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (G G' : GenusSymbolData)
    (hc : G.Conditions) (hc' : G'.Conditions) (hr : G.real = G'.real) (hd : G.det.natAbs = 2 * p)
    (hd' : G'.det.natAbs = 2 * p) (hT : (G.two 0).type = (G'.two 0).type)
    (he : (G.odd p 1).sign = (G'.odd p 1).sign) :
    (∀ q, q.Prime → q ≠ 2 → G.odd q = G'.odd q) ∧ MoveEquiv G.two G'.two := by
  have hr1 : G.real = ⟨G.real.pos, G.real.neg⟩ := rfl
  have hr2 : G'.real = ⟨G.real.pos, G.real.neg⟩ := hr.symm.trans hr1
  generalize G.real.pos = r at hr1 hr2
  generalize G.real.neg = s at hr1 hr2
  have hn : G.n = r + s := by rw [← hc.real_dim, hr1]
  have hn' : G'.n = r + s := by rw [← hc'.real_dim, hr2]
  obtain ⟨hdet, hv2, hvp⟩ := det2p_vals G hc p hp hp2 hd hr1
  obtain ⟨hdet', hv2', hvp'⟩ := det2p_vals G' hc' p hp hp2 hd' hr2
  refine ⟨fun q hq hq2 => ?_, ?_⟩
  · by_cases hqp : q = p
    · subst hqp
      funext k
      rw [odd_p_form G hc q hp hp2 hd hr1, odd_p_form G' hc' q hp hp2 hd' hr2, he]
    · funext k
      rw [G.odd_unit hc q hq hq2 (by rw [hdet]; exact padicValInt_2p_ne q p s hq hp hq2 hqp),
        G'.odd_unit hc' q hq hq2 (by rw [hdet']; exact padicValInt_2p_ne q p s hq hp hq2 hqp), hn, hn', hdet, hdet']
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, b1, b4, b6, hoe⟩ := G.det2p_part hc p hp hp2 hd hr1
    obtain ⟨a1', a2', a3', a4', a5', a6', a7', b1', b4', b6', hoe'⟩ := G'.det2p_part hc' p hp hp2 hd' hr2
    have hI := two1_isTypeI_iff G hc hv2
    have hty : ∀ k, (G'.two k).type = (G.two k).type := by
      intro k
      by_cases hk0 : k = 0
      · subst hk0; exact hT.symm
      by_cases hk1 : k = 1
      · subst hk1; rw [a4, a4']
      · have hk : 2 ≤ k := by omega
        rw [a3 k hk, a3' k hk]
    refine (moveEquiv_iff_sameInvariants (B := 2) (fun k hk => ?_)).2 ?_
    · rw [hI]; omega
    · refine ⟨fun k => ?_, hty, fun k hk => ?_, fun y hy => ?_, fun c₁ c₂ hC => ?_⟩
      · by_cases hk0 : k = 0
        · subst hk0; omega
        by_cases hk1 : k = 1
        · subst hk1; rw [a2, a2']
        · have hk : 2 ≤ k := by omega
          rw [a3 k hk, a3' k hk]
      · have hk' : ¬ (k = 1 ∨ (k = 0 ∧ (G.two 0).type = .I)) := by rw [← hI]; exact hk
        by_cases h2 : 2 ≤ k
        · rw [a3 k h2, a3' k h2]
        · have hk0 : k = 0 := by
            by_contra h
            exact hk' (Or.inl (by omega))
          subst hk0
          have hT2 : (G.two 0).type = .II := by
            cases h : (G.two 0).type
            · exfalso; apply hk'; right; exact ⟨rfl, h⟩
            · rfl
          have hT2' : (G'.two 0).type = .II := by rw [hty, hT2]
          rw [a6'.2.2.2.2 hT2', a6.2.2.2.2 hT2]
      · have hy2 : 2 ≤ y := by
          obtain ⟨h1, h2⟩ := hy
          by_contra h
          by_cases hy0 : y = 0
          · apply h2
            rw [hI]
            left
            omega
          · apply h1
            rw [hI]
            left
            omega
        have hmb := two1_minusBelow G hc hv2 (y + 1) (by omega)
        have hmb' := two1_minusBelow G' hc' hv2' (y + 1) (by omega)
        rw [hmb, hmb']
        have hsame : (G.two 0).sign.mul (G.two 1).sign = (G'.two 0).sign.mul (G'.two 1).sign := by
          rw [a5, a5']
        revert hsame
        cases (G.two 0).sign <;> cases (G.two 1).sign <;> cases (G'.two 0).sign <;> cases (G'.two 1).sign <;>
          simp [Sign.mul, Sign.flip] <;> decide
      · have hC' : IsCompartment G'.two c₁ c₂ := by
          simpa only [IsCompartment, IsTypeI, hty] using hC
        rw [two1_compInv G' hc' hv2' hC', two1_compInv G hc hv2 hC, ← hoe, ← hoe']
        rw [he]

end QuadFormsKB.ConwaySloane
