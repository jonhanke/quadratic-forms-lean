/-
# Conway–Sloane, Ch. 15, §8.1: Table 15.4, the rows with a factor $2$ in the determinant

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.1,
Theorem 12, Table 15.4 (p. 387) (`conwaysloane1999`; printed page = PDF page of the chapter file + 351).

For the rows whose 2-adic symbol has several scales the book's "genus" is a class of symbols modulo sign walking and
oddity fusion (`MoveEquiv`). Here a row is classified in two statements:
* **existence**: a system of symbols satisfying `GenusSymbolData.Conditions` with the stated invariants exists iff the
  signature condition/exceptions of the book hold;
* **uniqueness**: two such systems have equal odd-prime symbols and `MoveEquiv` 2-adic symbols, i.e. there is exactly
  one genus with the given invariants (this is why the table lists a single genus $\mathrm I_{r,s}(2)$ for each
  $(r,s)$).

**Covered rows.** $\lvert\det\rvert = 2$: $\mathrm I_{r,s}(2)$ (all signatures, exceptions $0, 1$) and
$\mathrm{II}_{r,s}(2)$ (signature $\pm1$, no exceptions): `table154_two_typeI`, `table154_two_typeII`,
`table154_two_unique`.

**Not covered.** $\lvert\det\rvert = 4, 6, 8, 10$, the rows $\mathrm I_{r,s}(9^{\pm1})$, $\mathrm{II}_{r,s}(9^{\pm1})$, and
Table 15.5 (2-elementary forms): each needs the same analysis with more scales (see the module docstring of
`SmallDetTables.lean`).
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDet

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### The data forced by the conditions when $\lvert\det\rvert = 2$ -/

theorem natAbs_two_cases {d : ℤ} (hd : d.natAbs = 2) : d = 2 ∨ d = -2 := by omega

theorem jacobiTwo_pm_one_int {d : ℤ} (hd : d = 1 ∨ d = -1) : jacobiTwo d = .plus := by
  rcases hd with h | h <;> subst h <;> decide

/-- **The data forced by the conditions when $\lvert\det\rvert = 2$** (Conway–Sloane, §8.1, Table 15.4, rows $\pm2$):
the 2-adic symbol is $1_{t_0}^{\varepsilon(n-1)}2_{t_1}^{\varepsilon1}$ (the scale $2$ constituent has dimension $1$,
hence type I; the two signs agree), the other scales are empty, and the signature is
$t_0 + t_1 + 4[\varepsilon = -]$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±2)"]
theorem GenusSymbolData.det2_part (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 2) :
    (G.two 0).dim + 1 = G.n ∧ (G.two 1).dim = 1 ∧ (∀ k, 2 ≤ k → G.two k = TwoFactor.trivial) ∧
      (G.two 1).type = .I ∧ (G.two 0).sign = (G.two 1).sign ∧
      (G.signature : ZMod 8) = (G.two 0).oddity + (G.two 1).oddity + 4 * ind8 ((G.two 1).sign = .minus) ∧
      (G.two 0).Exists ∧ (G.two 1).Exists := by
  have hv2 : padicValInt 2 G.det = 1 := by simp [padicValInt, hd]
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
  have hsign : (G.two 0).sign = (G.two 1).sign := by
    rw [signProd_stable (fun k => (G.two k).sign) hN2
      (fun k hk => by simp [t2 k hk, TwoFactor.trivial]), hv2] at hsg
    have hj : jacobiTwo (G.det / 2 ^ 1) = .plus := by
      apply jacobiTwo_pm_one_int
      rcases natAbs_two_cases hd with h | h <;> rw [h] <;> norm_num
    rw [hj] at hsg
    simp only [signProd, Sign.plus_mul] at hsg
    revert hsg
    cases (G.two 0).sign <;> cases (G.two 1).sign <;> intro h <;> first | rfl | exact absurd h (by decide)
  refine ⟨hdimsum, d1, t2, (hex 1).typeI_of_odd (by omega), hsign, ?_, hex 0, hex 1⟩
  have h := hc.oddity_formula
  rw [hd, Nat.Prime.primeFactors Nat.prime_two, Finset.filter_singleton, if_neg (by norm_num),
    Finset.sum_empty, add_zero] at h
  rw [h]
  have hsupp2 : G.two.SupportedBelow 2 := fun k hk => t2 k hk
  rw [TwoSymbol.oddity_congr hsupp2 hN2]
  unfold TwoSymbol.oddity
  simp [Finset.sum_range_succ, ind8]
  ring

theorem GenusSymbolData.det_eq_of (G : GenusSymbolData) (hc : G.Conditions) {m r s : ℕ} (hm : 0 < m)
    (hd : G.det.natAbs = m) (hr : G.real = ⟨r, s⟩) : G.det = (m : ℤ) * (-1) ^ s := by
  have h := hc.real_sign
  rw [hr] at h
  have h' : G.det < 0 ↔ Odd s := h
  have hcase : G.det = m ∨ G.det = -(m : ℤ) := by omega
  rcases Nat.even_or_odd s with he | ho
  · have hnl : ¬ G.det < 0 := fun hl => (Nat.not_odd_iff_even.2 he) (h'.1 hl)
    rw [he.neg_one_pow, mul_one]
    omega
  · have hl : G.det < 0 := h'.2 ho
    rw [ho.neg_one_pow, mul_neg, mul_one]
    omega

/-- **The symbol at an odd prime not dividing the determinant** is $1^{\varepsilon n}$,
$\varepsilon = \left(\frac{\det}{q}\right)$ (Conway–Sloane, §7.7, (29)). -/
theorem GenusSymbolData.odd_unit (G : GenusSymbolData) (hc : G.Conditions) (q : ℕ) (hq : q.Prime)
    (hq2 : q ≠ 2) (hv : padicValInt q G.det = 0) (k : ℕ) :
    G.odd q k = if k = 0 then ⟨G.n, Sign.ofInt (jacobiSym G.det q)⟩ else OddFactor.trivial := by
  obtain ⟨hs, hsg⟩ := hc.odd_det q hq hq2
  rw [hv] at hs
  have hsupp := hc.odd_supp q
  have hex := hc.odd_exists q hq hq2
  have hdim : ∀ k, 0 < k → (G.odd q k).dim = 0 := by
    intro k hk
    by_cases hkN : k < G.N
    · have := (Finset.sum_eq_zero_iff.1 hs) k (mem_range.2 hkN)
      simpa [hk.ne'] using this
    · rw [hsupp k (not_lt.1 hkN)]; rfl
  have htriv : ∀ k, 0 < k → G.odd q k = OddFactor.trivial := by
    intro k hk
    have h1 : (G.odd q k).dim = 0 := hdim k hk
    have h2 : (G.odd q k).sign = .plus := hex k h1
    generalize G.odd q k = f at h1 h2
    obtain ⟨d, s⟩ := f
    dsimp only at h1 h2
    subst h1 h2
    rfl
  have hzero : G.N ≤ 0 → G.odd q 0 = OddFactor.trivial := fun h => hsupp 0 h
  have hn : (G.odd q 0).dim = G.n := by
    rw [← hc.odd_dim q hq hq2]
    symm
    refine Finset.sum_eq_single 0 (fun k _ hk => hdim k (Nat.pos_of_ne_zero hk)) fun h0 => ?_
    have : G.N ≤ 0 := by simpa using h0
    rw [hzero this]; rfl
  have hsign : (G.odd q 0).sign = Sign.ofInt (jacobiSym G.det q) := by
    rw [hv, pow_zero, Int.ediv_one] at hsg
    rw [← hsg]
    have hs' : ∀ k, 1 ≤ k → (fun k => (G.odd q k).sign) k = .plus := fun k hk => by
      simp [htriv k hk, OddFactor.trivial]
    rcases Nat.eq_zero_or_pos G.N with hN | hN
    · rw [hN]
      have := hc.odd_supp q 0 (by omega)
      simp [signProd, this, OddFactor.trivial]
    · rw [signProd_stable (fun k => (G.odd q k).sign) hN hs']
      simp only [signProd]
      cases (G.odd q 0).sign <;> rfl
  by_cases hk : k = 0
  · subst hk
    simp only [if_true]
    generalize G.odd q 0 = f at hn hsign
    obtain ⟨d, s⟩ := f
    dsimp only at hn hsign
    rw [hn, hsign]
  · simp only [if_neg hk]
    exact htriv k (Nat.pos_of_ne_zero hk)

theorem padicValInt_two_negOnePow (q s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q (2 * (-1 : ℤ) ^ s) = 0 := by
  have : ¬ q ∣ 2 := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
  simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow, padicValNat.eq_zero_of_not_dvd this]

/-- **The system of symbols for $\lvert\det\rvert = 2$**: determinant $2(-1)^s$, $(-1)$-adic symbol $+^r-^s$,
2-adic symbol $1_{t_0}^{\varepsilon(n-1)}2_{t_1}^{\varepsilon1}$ with the scale-1 constituent of type `T`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±2)"]
def det2Data (r s : ℕ) (ε : Sign) (T : ScaledType) (t0 t1 : ZMod 8) : GenusSymbolData where
  n := r + s
  det := 2 * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q k => if k = 0 then ⟨r + s, Sign.ofInt (jacobiSym (2 * (-1) ^ s) q)⟩ else OddFactor.trivial
  two := fun k => if k = 0 then ⟨r + s - 1, ε, T, t0⟩ else if k = 1 then ⟨1, ε, .I, t1⟩ else TwoFactor.trivial
  N := 2

theorem det2Data_conditions (r s : ℕ) (ε : Sign) (T : ScaledType) (t0 t1 : ZMod 8) (hn : 1 ≤ r + s)
    (h0 : (⟨r + s - 1, ε, T, t0⟩ : TwoFactor).Exists) (h1 : (⟨1, ε, .I, t1⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s = t0 + t1 + 4 * ind8 (ε = .minus)) :
    (det2Data r s ε T t0 t1).Conditions where
  ne_zero := mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp [det2Data, h.neg_one_pow, this]
    · simp [det2Data, h.neg_one_pow, h]
  odd_supp q k hk := by
    have hk' : 2 ≤ k := hk
    simp [det2Data, show k ≠ 0 by omega]
  two_supp k hk := by
    have hk' : 2 ≤ k := hk
    simp [det2Data, show k ≠ 0 by omega, show k ≠ 1 by omega]
  odd_dim q _ _ := by simp [det2Data, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by
    simp [det2Data, Finset.sum_range_succ]
    omega
  odd_det q hq hq2 := by
    refine ⟨?_, ?_⟩
    · simp [det2Data, padicValInt_two_negOnePow q s hq hq2, Finset.sum_range_succ, OddFactor.trivial]
    · simp [det2Data, padicValInt_two_negOnePow q s hq hq2, signProd, Sign.plus_mul, Sign.mul_plus,
        OddFactor.trivial]
  two_det := by
    have hv : padicValInt 2 (2 * (-1 : ℤ) ^ s) = 1 := by
      simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow]
    refine ⟨by simp [det2Data, hv, Finset.sum_range_succ], ?_⟩
    have hd : (2 * (-1 : ℤ) ^ s) / 2 ^ 1 = (-1) ^ s := by simp
    simp [det2Data, hv, signProd, hd, jacobiTwo_pm_one, Sign.plus_mul, TwoFactor.trivial]
    cases ε <;> rfl
  odd_exists q hq hq2 k := by
    by_cases hk : k = 0
    · subst hk
      simp only [det2Data, if_true]
      intro h0'
      have : r + s = 0 := h0'
      omega
    · simp [det2Data, hk, OddFactor.Exists, OddFactor.trivial]
  two_exists k := by
    by_cases hk : k = 0
    · subst hk; simpa [det2Data] using h0
    · by_cases hk1 : k = 1
      · subst hk1; simpa [det2Data] using h1
      · simp only [det2Data, if_neg hk, if_neg hk1]
        decide
  oddity_formula := by
    have hna : (det2Data r s ε T t0 t1).det.natAbs = 2 := by
      simp [det2Data, Int.natAbs_mul, Int.natAbs_pow]
    rw [hna, Nat.Prime.primeFactors Nat.prime_two, Finset.filter_singleton, if_neg (by norm_num),
      Finset.sum_empty, add_zero]
    simp [det2Data, GenusSymbolData.signature, TwoSymbol.oddity, ind8, Finset.sum_range_succ, TwoFactor.trivial]
    rw [ht]
    unfold ind8
    split_ifs <;> ring

theorem det2_exists_of (r s : ℕ) (ε : Sign) (T : ScaledType) (t0 t1 : ZMod 8) (hn : 1 ≤ r + s)
    (h0 : (⟨r + s - 1, ε, T, t0⟩ : TwoFactor).Exists) (h1 : (⟨1, ε, .I, t1⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s = t0 + t1 + 4 * ind8 (ε = .minus)) :
    ∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ∧ (G.two 0).type = T :=
  ⟨det2Data r s ε T t0 t1, det2Data_conditions r s ε T t0 t1 hn h0 h1 ht, rfl,
    by simp [det2Data, Int.natAbs_mul, Int.natAbs_pow], by simp [det2Data]⟩

set_option synthInstance.maxSize 1024 in
theorem exists1_values : ∀ (ε : Sign) (t : ZMod 8), (⟨1, ε, .I, t⟩ : TwoFactor).Exists →
    t + 4 * ind8 (ε = .minus) = 1 ∨ t + 4 * ind8 (ε = .minus) = 7 := by
  intro ε
  cases ε <;> decide

theorem typeI_big (σ : Sign) (m : ℕ) (t : ZMod 8) (hm : 3 ≤ m) (ht : t.val % 2 = m % 2) :
    (⟨m, σ, .I, t⟩ : TwoFactor).Exists := by
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 _ => ?_, ht, fun h => nomatch h⟩
  · have h0' : m = 0 := h0
    omega
  · have h1' : m = 1 := h1
    omega
  · have h2' : m = 2 := h2
    omega

set_option synthInstance.maxSize 1024 in
theorem det2_small : ∀ r, r ≤ 3 → ∀ s, s ≤ 3 → 2 ≤ r + s → r + s ≤ 3 →
    ((⟨r + s - 1, .plus, .I, (r : ZMod 8) - s - 1⟩ : TwoFactor).Exists ∨
      (⟨r + s - 1, .plus, .I, (r : ZMod 8) - s - 7⟩ : TwoFactor).Exists) := by
  decide

/-- **Table 15.4, $\pm2$, $\mathrm I_{r,s}(2)$:** all signatures, exceptions $0$ and $1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±2, I(2))"]
theorem table154_two_typeI (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ∧ (G.two 0).type = .I) ↔
      2 ≤ r + s := by
  constructor
  · rintro ⟨G, hc, hr, hd, hT⟩
    obtain ⟨h1, -, -, -, -, -, hE0, -⟩ := G.det2_part hc hd
    have hn : G.n = r + s := by rw [← hc.real_dim, hr]
    by_contra hlt
    have h0 : (G.two 0).dim = 0 := by omega
    have := (hE0.1 h0).1
    rw [hT] at this
    exact absurd this (by decide)
  · intro h
    have hn : 1 ≤ r + s := by omega
    by_cases h4 : 4 ≤ r + s
    · refine det2_exists_of r s .plus .I (((r : ℤ) - s - 1 : ℤ) : ZMod 8) 1 hn ?_ ?_ ?_
      · apply typeI_big _ _ _ (by omega)
        have := ZMod.val_intCast (n := 8) ((r : ℤ) - s - 1)
        omega
      · decide
      · simp [ind8]
    · have := det2_small r (by omega) s (by omega) h (by omega)
      rcases this with h0 | h0
      · exact det2_exists_of r s .plus .I _ 1 hn h0 (by decide) (by simp [ind8])
      · exact det2_exists_of r s .plus .I _ 7 hn h0 (by decide) (by simp [ind8])

/-- **Table 15.4, $\pm2$, $\mathrm{II}_{r,s}(2)$:** signature $\pm1$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±2, II(2))"]
theorem table154_two_typeII (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ∧ (G.two 0).type = .II) ↔
      (((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 7) := by
  constructor
  · rintro ⟨G, hc, hr, hd, hT⟩
    obtain ⟨-, d1, -, ht1, -, hsig, hE0, hE1⟩ := G.det2_part hc hd
    have h0 : (G.two 0).oddity = 0 := hE0.2.2.2.2 hT
    have hE1' : (⟨1, (G.two 1).sign, .I, (G.two 1).oddity⟩ : TwoFactor).Exists := by
      generalize G.two 1 = f at d1 ht1 hE1
      obtain ⟨d, sg, ty, o⟩ := f
      dsimp only at d1 ht1 hE1 ⊢
      subst d1 ht1
      exact hE1
    have hv := exists1_values _ _ hE1'
    have hsr : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
    rw [hsr, h0, zero_add] at hsig
    rcases hv with hv | hv
    · left
      have := (zmod_cast_iff r s (-1)).1 (by push_cast; rw [hsig, hv]; ring)
      omega
    · right
      have := (zmod_cast_iff r s (-7)).1 (by push_cast; rw [hsig, hv]; ring)
      omega
  · intro h
    have hn : 1 ≤ r + s := by
      by_contra hn
      have : r = 0 := by omega
      have : s = 0 := by omega
      subst r s
      omega
    have hpar : (r + s) % 2 = 1 := by omega
    have hE0 : (⟨r + s - 1, .plus, .II, 0⟩ : TwoFactor).Exists := by
      refine ⟨fun _ => ⟨rfl, rfl⟩, fun h1 => ?_, (fun _ hI => by cases hI), ?_, fun _ => rfl⟩
      · have h1' : r + s - 1 = 1 := h1
        exfalso
        omega
      · show (0 : ZMod 8).val % 2 = (r + s - 1) % 2
        simp
        omega
    rcases h with h | h
    · exact det2_exists_of r s .plus .II 0 1 hn hE0 (by decide) (by
        have := (zmod_cast_iff r s (-1)).2 (by omega)
        push_cast at this
        simp [ind8]
        linear_combination this)
    · exact det2_exists_of r s .plus .II 0 7 hn hE0 (by decide) (by
        have := (zmod_cast_iff r s (-7)).2 (by omega)
        push_cast at this
        simp [ind8]
        linear_combination this)

/-! ### Uniqueness of the genus for $\lvert\det\rvert = 2$ -/

theorem det2_isTypeI_iff (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 2) (k : ℕ) :
    IsTypeI G.two k ↔ k = 1 ∨ (k = 0 ∧ (G.two 0).type = .I) := by
  obtain ⟨-, -, t2, ht1, -⟩ := G.det2_part hc hd
  by_cases hk0 : k = 0
  · subst hk0; simp [IsTypeI]
  by_cases hk1 : k = 1
  · subst hk1; simpa [IsTypeI] using ht1
  · have hk : 2 ≤ k := by omega
    simp [IsTypeI, t2 k hk, TwoFactor.trivial, hk0, hk1]

theorem det2_compartments (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 2) {c₁ c₂ : ℕ}
    (h : IsCompartment G.two c₁ c₂) :
    (c₁ = 0 ∧ c₂ = 1 ∧ (G.two 0).type = .I) ∨ (c₁ = 1 ∧ c₂ = 1 ∧ (G.two 0).type = .II) := by
  obtain ⟨hle, hall, hstart, hend⟩ := h
  have hI := det2_isTypeI_iff G hc hd
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

theorem det2_compInv (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 2) {c₁ c₂ : ℕ}
    (h : IsCompartment G.two c₁ c₂) : compartmentInvariant G.two c₁ c₂ = (G.signature : ZMod 8) := by
  obtain ⟨-, -, -, -, hsign, hsig, hE0, -⟩ := G.det2_part hc hd
  rw [hsig]
  have e12 : Finset.Icc 1 2 = {1, 2} := by decide
  have e02 : Finset.Icc 0 2 = {0, 1, 2} := by decide
  have e01 : Finset.Icc 0 1 = {0, 1} := by decide
  have e11 : Finset.Icc 1 1 = {1} := by decide
  rcases det2_compartments G hc hd h with ⟨rfl, rfl, hT⟩ | ⟨rfl, rfl, hT⟩
  · simp only [compartmentInvariant, e01, e02]
    simp [minusBelow, hsign, ind8]
    cases (G.two 1).sign <;> simp <;> decide
  · have h0 : (G.two 0).oddity = 0 := hE0.2.2.2.2 hT
    simp only [compartmentInvariant, e11, e12]
    simp [minusBelow, hsign, ind8, h0]
    cases (G.two 1).sign <;> simp <;> decide

theorem det2_minusBelow (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 2) :
    ∀ m, 2 ≤ m → minusBelow G.two m =
      (if (G.two 0).sign = .minus then 1 else 0) + (if (G.two 1).sign = .minus then 1 else 0) := by
  obtain ⟨-, -, t2, -, -, -, -, -⟩ := G.det2_part hc hd
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp [minusBelow]
  | succ m hm ih =>
    rw [minusBelow, ih, t2 m hm]
    simp [TwoFactor.trivial]

/-- **Uniqueness of the genus for $\lvert\det\rvert = 2$** (Conway–Sloane, §8.1, Table 15.4, rows $\pm2$): two
systems of symbols satisfying the conditions, with equal $(-1)$-adic symbols and equal types of the scale-1
constituent, have the same $p$-adic symbols at the odd primes and $2$-adic symbols related by sign walking and oddity
fusion: for each $(r,s)$ and type there is at most one genus ($\mathrm I_{r,s}(2)$, $\mathrm{II}_{r,s}(2)$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±2: one genus for each (r,s) and type)"]
theorem table154_two_unique (G G' : GenusSymbolData) (hc : G.Conditions) (hc' : G'.Conditions)
    (hr : G.real = G'.real) (hd : G.det.natAbs = 2) (hd' : G'.det.natAbs = 2)
    (hT : (G.two 0).type = (G'.two 0).type) :
    (∀ q, q.Prime → q ≠ 2 → G.odd q = G'.odd q) ∧ MoveEquiv G.two G'.two := by
  have hr1 : G.real = ⟨G.real.pos, G.real.neg⟩ := rfl
  have hr2 : G'.real = ⟨G.real.pos, G.real.neg⟩ := hr.symm.trans hr1
  generalize G.real.pos = r at hr1 hr2
  generalize G.real.neg = s at hr1 hr2
  have hn : G.n = r + s := by rw [← hc.real_dim, hr1]
  have hn' : G'.n = r + s := by rw [← hc'.real_dim, hr2]
  have hdet : G.det = 2 * (-1) ^ s := by
    simpa using G.det_eq_of hc (m := 2) (by norm_num) hd hr1
  have hdet' : G'.det = 2 * (-1) ^ s := by
    simpa using G'.det_eq_of hc' (m := 2) (by norm_num) hd' hr2
  refine ⟨fun q hq hq2 => ?_, ?_⟩
  · funext k
    rw [G.odd_unit hc q hq hq2 (by rw [hdet]; exact padicValInt_two_negOnePow q s hq hq2),
      G'.odd_unit hc' q hq hq2 (by rw [hdet']; exact padicValInt_two_negOnePow q s hq hq2), hn, hn', hdet, hdet']
  · obtain ⟨hds, d1, t2, ht1, hsg, hsig, hE0, hE1⟩ := G.det2_part hc hd
    obtain ⟨hds', d1', t2', ht1', hsg', hsig', hE0', hE1'⟩ := G'.det2_part hc' hd'
    have hI := det2_isTypeI_iff G hc hd
    have hty : ∀ k, (G'.two k).type = (G.two k).type := by
      intro k
      by_cases hk0 : k = 0
      · subst hk0; exact hT.symm
      by_cases hk1 : k = 1
      · subst hk1; rw [ht1, ht1']
      · have hk : 2 ≤ k := by omega
        rw [t2 k hk, t2' k hk]
    refine (moveEquiv_iff_sameInvariants (B := 2) (fun k hk => ?_)).2 ?_
    · rw [hI]; omega
    · refine ⟨fun k => ?_, hty, fun k hk => ?_, fun y hy => ?_, fun c₁ c₂ hC => ?_⟩
      · by_cases hk0 : k = 0
        · subst hk0; omega
        by_cases hk1 : k = 1
        · subst hk1; rw [d1, d1']
        · have hk : 2 ≤ k := by omega
          rw [t2 k hk, t2' k hk]
      · have hk' : ¬ (k = 1 ∨ (k = 0 ∧ (G.two 0).type = .I)) := by rw [← hI]; exact hk
        by_cases h2 : 2 ≤ k
        · rw [t2 k h2, t2' k h2]
        · have hk0 : k = 0 := by
            by_contra h
            exact hk' (Or.inl (by omega))
          subst hk0
          have hT2 : (G.two 0).type = .II := by
            cases h : (G.two 0).type
            · exfalso; apply hk'; right; exact ⟨rfl, h⟩
            · rfl
          have hT2' : (G'.two 0).type = .II := by rw [hty, hT2]
          rw [hE0'.2.2.2.2 hT2', hE0.2.2.2.2 hT2]
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
        have hmb := det2_minusBelow G hc hd (y + 1) (by omega)
        have hmb' := det2_minusBelow G' hc' hd' (y + 1) (by omega)
        have hs1 : (G.two 0).sign = (G.two 1).sign := hsg
        have hs1' : (G'.two 0).sign = (G'.two 1).sign := hsg'
        rw [hmb, hmb', hs1, hs1']
        cases (G.two 1).sign <;> cases (G'.two 1).sign <;> simp <;> decide
      · have hC' : IsCompartment G'.two c₁ c₂ := by
          simpa only [IsCompartment, IsTypeI, hty] using hC
        rw [det2_compInv G' hc' hd' hC', det2_compInv G hc hd hC]
        simp [GenusSymbolData.signature, hr1, hr2]

end QuadFormsKB.ConwaySloane
