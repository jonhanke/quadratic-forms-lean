/-
# Conway–Sloane, Ch. 15, §8.2: Theorem 13 (b) and Table 15.5, the 2-elementary genera

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.2,
Theorem 13 (b), Table 15.5 (p. 388) (`conwaysloane1999`).

A 2-elementary genus has the 2-adic symbol $1^{\varepsilon_0(n-k)}2^{\varepsilon_1k}$ (scales $1$ and $2$ only) and
determinant $\pm2^k$, $0 < k \le n$. This file proves the shape lemma `two_shapeK`, the general existence theorem
`detK_exists_iff` and the existence statements for the rows of Table 15.5 (`table155_*`).

**Covered rows.** All five rows of Table 15.5 (existence, for all $n$ and all $k \ge 1$): $\mathrm I(2_{\mathrm I}^k)$,
$\mathrm I(2_{\mathrm{II}}^k)$, $\mathrm{II}(2_{\mathrm I}^k)$, $\mathrm{II}(2_{\mathrm{II}}^{k})$ and
$\mathrm{II}(2_{\mathrm{II}}^{-k})$ (the last two being the signs $\pm$ of the scale-2 constituent). The conditions are
those of the book (the dimensions $n-k$ and $k$ are reduced to $\le 4$ by `exists_capf`, then checked by `decide`).
No discrepancy with the printed table. Uniqueness of the genera up to `MoveEquiv` is not proved.
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables6

namespace QuadFormsKB.ConwaySloane

open Finset

/-- **The 2-adic symbol of a 2-elementary system** ($v_2(\det) = k$, nothing at the scales $\ge 2^2$): the constituents at
the scales $1$ and $2$ have dimensions $n - k$ and $k$, the sign product is $\left(\frac{\det/2^k}{2}\right)$ and the
oddity is $t_0 + t_1 + 4[\varepsilon_1 = -]$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13(b), Table 15.5, p. 388 (2-adic shape)"]
theorem GenusSymbolData.two_shapeK (G : GenusSymbolData) (hc : G.Conditions) (k : ℕ)
    (hv2 : padicValInt 2 G.det = k) (hel : ∀ j, 2 ≤ j → (G.two j).dim = 0) :
    (∀ j, 2 ≤ j → G.two j = TwoFactor.trivial) ∧ (G.two 1).dim = k ∧
      (G.two 0).dim + (G.two 1).dim = G.n ∧
      (G.two 0).sign.mul (G.two 1).sign = jacobiTwo (G.det / 2 ^ k) ∧
      G.two.oddity G.N = (G.two 0).oddity + (G.two 1).oddity + 4 * ind8 ((G.two 1).sign = .minus) ∧
      (G.two 0).Exists ∧ (G.two 1).Exists := by
  obtain ⟨hs, hsg⟩ := hc.two_det
  rw [hv2] at hs
  have hsupp := hc.two_supp
  have hex := hc.two_exists
  have t2 : ∀ j, 2 ≤ j → G.two j = TwoFactor.trivial := by
    intro j hj
    obtain ⟨h32, -, -, -, hII⟩ := hex j
    have h1 : (G.two j).dim = 0 := hel j hj
    obtain ⟨h2, h3⟩ := h32 h1
    have h4 : (G.two j).oddity = 0 := hII h2
    generalize G.two j = f at h1 h2 h3 h4
    obtain ⟨d, s, t, o⟩ := f
    dsimp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  have hsupN : ∀ j, G.N ≤ j → (G.two j).dim = 0 := fun j hj => by rw [hsupp j hj]; rfl
  refine ⟨t2, ?_, ?_, ?_, ?_, hex 0, hex 1⟩
  · rw [sum_range_stable_nat (f := fun j => j * (G.two j).dim) (m := 2) (fun j hj => by simp [hel j hj])
      (fun j hj => by simp [hsupN j hj])] at hs
    simpa [Finset.sum_range_succ] using hs
  · have h := hc.two_dim
    rw [sum_range_stable_nat (f := fun j => (G.two j).dim) (m := 2) (fun j hj => hel j hj) hsupN] at h
    simpa [Finset.sum_range_succ] using h
  · have h2 : signProd (fun j => (G.two j).sign) G.N = signProd (fun j => (G.two j).sign) 2 := by
      rcases le_total G.N 2 with h | h
      · exact (signProd_stable _ h (fun j hj => by simp [hsupp j hj, TwoFactor.trivial])).symm
      · exact signProd_stable _ h (fun j hj => by simp [t2 j hj, TwoFactor.trivial])
    rw [h2, hv2] at hsg
    simpa [signProd, Sign.plus_mul] using hsg
  · have hodd : G.two.oddity G.N = G.two.oddity 2 := by
      rcases le_total 2 G.N with h | h
      · exact TwoSymbol.oddity_congr (fun j hj => t2 j hj) h
      · exact (TwoSymbol.oddity_congr hsupp h).symm
    rw [hodd]
    unfold TwoSymbol.oddity
    simp [Finset.sum_range_succ, ind8]
    ring

theorem natAbs_pow_two (k s : ℕ) : ((2 : ℤ) ^ k * (-1) ^ s).natAbs = 2 ^ k := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem padicValInt_pow_two (k s : ℕ) : padicValInt 2 ((2 : ℤ) ^ k * (-1) ^ s) = k := by
  simp only [padicValInt, natAbs_pow_two]
  exact padicValNat.prime_pow k

theorem padicValInt_pow_two_odd (q k s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q ((2 : ℤ) ^ k * (-1) ^ s) = 0 := by
  have : ¬ q ∣ 2 ^ k := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  simp only [padicValInt, natAbs_pow_two]
  exact padicValNat.eq_zero_of_not_dvd this

/-- **The system of symbols for a 2-elementary genus**, determinant $2^k(-1)^s$, 2-adic constituents `c0`, `c1`
(scales $1$ and $2$), unit symbols at the odd primes. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13(b), Table 15.5, p. 388"]
def dataTwoK (r s k : ℕ) (c0 c1 : TwoFactor) : GenusSymbolData where
  n := r + s
  det := 2 ^ k * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q j => if j = 0 then ⟨r + s, Sign.ofInt (jacobiSym (2 ^ k * (-1) ^ s) q)⟩ else OddFactor.trivial
  two := fun j => if j = 0 then c0 else if j = 1 then c1 else TwoFactor.trivial
  N := 2

theorem dataTwoK_conditions (r s k : ℕ) (hk : 1 ≤ k) (c0 c1 : TwoFactor)
    (hn : c0.dim + c1.dim = r + s) (hdim : c1.dim = k) (h0 : c0.Exists) (h1 : c1.Exists)
    (hsg : c0.sign.mul c1.sign = .plus)
    (hsig : (r : ZMod 8) - s = c0.oddity + c1.oddity + 4 * ind8 (c1.sign = .minus)) :
    (dataTwoK r s k c0 c1).Conditions where
  ne_zero := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp [dataTwoK, h.neg_one_pow, this]
    · simp [dataTwoK, h.neg_one_pow, h]
  odd_supp q j hj := by
    have hj' : 2 ≤ j := hj
    simp [dataTwoK, show j ≠ 0 by omega]
  two_supp j hj := by
    have hj' : 2 ≤ j := hj
    simp [dataTwoK, show j ≠ 0 by omega, show j ≠ 1 by omega]
  odd_dim q _ _ := by simp [dataTwoK, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by
    simp [dataTwoK, Finset.sum_range_succ]
    omega
  odd_det q hq hq2 := by
    refine ⟨?_, ?_⟩
    · simp [dataTwoK, padicValInt_pow_two_odd q k s hq hq2, Finset.sum_range_succ, OddFactor.trivial]
    · simp [dataTwoK, padicValInt_pow_two_odd q k s hq hq2, signProd, Sign.plus_mul, Sign.mul_plus,
        OddFactor.trivial]
  two_det := by
    refine ⟨?_, ?_⟩
    · simp [dataTwoK, padicValInt_pow_two, Finset.sum_range_succ]
      omega
    · have hd : (2 ^ k * (-1 : ℤ) ^ s) / 2 ^ k = (-1) ^ s :=
        Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num))
      simp [dataTwoK, padicValInt_pow_two, signProd, hd, jacobiTwo_pm_one, Sign.plus_mul]
      simpa [signProd, Sign.plus_mul] using hsg
  odd_exists q hq hq2 j := by
    by_cases hj : j = 0
    · subst hj
      simp only [dataTwoK, if_true]
      intro h0'
      have : r + s = 0 := h0'
      omega
    · simp [dataTwoK, hj, OddFactor.Exists, OddFactor.trivial]
  two_exists j := by
    by_cases hj : j = 0
    · subst hj; simpa [dataTwoK] using h0
    · by_cases hj1 : j = 1
      · subst hj1; simpa [dataTwoK] using h1
      · simp only [dataTwoK, if_neg hj, if_neg hj1]
        decide
  oddity_formula := by
    have hna : (dataTwoK r s k c0 c1).det.natAbs = 2 ^ k := by
      simp [dataTwoK, natAbs_pow_two]
    rw [hna, Nat.primeFactors_prime_pow (by omega) Nat.prime_two, Finset.filter_singleton,
      if_neg (by norm_num), Finset.sum_empty, add_zero]
    have h2odd : ¬ Odd 2 := by decide
    simp [dataTwoK, GenusSymbolData.signature, TwoSymbol.oddity, Finset.sum_range_succ, TwoFactor.trivial,
      ind8] at hsig ⊢
    split_ifs at hsig ⊢ <;> linear_combination hsig

/-- The constraints on the two 2-adic constituents of a 2-elementary system. -/
def ConstrK (r s k : ℕ) (c0 c1 : TwoFactor) : Prop :=
  c0.dim + c1.dim = r + s ∧ c1.dim = k ∧ c0.Exists ∧ c1.Exists ∧ c0.sign.mul c1.sign = .plus ∧
    (r : ZMod 8) - s = c0.oddity + c1.oddity + 4 * ind8 (c1.sign = .minus)

/-- **Existence for 2-elementary genera, general form** (Conway–Sloane, §8.2, Thm. 13(b), Table 15.5). -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13(b), Table 15.5, p. 388"]
theorem detK_exists_iff (r s k : ℕ) (hk : 1 ≤ k) (P : TwoFactor → TwoFactor → Prop) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧ P (G.two 0) (G.two 1)) ↔
      ∃ c0 c1, ConstrK r s k c0 c1 ∧ P c0 c1 := by
  constructor
  · rintro ⟨G, hc, hr, hd, hel, hP⟩
    have hn : G.n = r + s := by rw [← hc.real_dim, hr]
    have hv2 : padicValInt 2 G.det = k := by
      simp only [padicValInt, hd]
      exact padicValNat.prime_pow k
    obtain ⟨-, h1, h2, h3, h4, e0, e1⟩ := G.two_shapeK hc k hv2 hel
    have hne : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hj : jacobiTwo (G.det / 2 ^ k) = .plus := by
      apply jacobiTwo_pm_one_int
      have hcase : G.det = 2 ^ k ∨ G.det = -(2 ^ k) := by
        have := Int.natAbs_eq G.det
        rw [hd] at this
        push_cast at this
        exact this
      rcases hcase with h | h
      · left; rw [h]; exact Int.ediv_self hne
      · right; rw [h, Int.neg_ediv_of_dvd (dvd_refl _), Int.ediv_self hne]
    rw [hj] at h3
    refine ⟨G.two 0, G.two 1, ⟨by omega, h1, e0, e1, h3, ?_⟩, hP⟩
    have h := hc.oddity_formula
    have e2 : (2 ^ k : ℕ).primeFactors = {2} := Nat.primeFactors_prime_pow (by omega) Nat.prime_two
    rw [hd, e2, Finset.filter_singleton, if_neg (by norm_num), Finset.sum_empty, add_zero, h4] at h
    have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
    rw [hsig] at h
    exact h
  · rintro ⟨c0, c1, ⟨a1, a2, a3, a4, a5, a6⟩, hP⟩
    refine ⟨dataTwoK r s k c0 c1, dataTwoK_conditions r s k hk c0 c1 a1 a2 a3 a4 a5 a6, rfl,
      by simp [dataTwoK, natAbs_pow_two], fun j hj => ?_, by simpa [dataTwoK] using hP⟩
    simp [dataTwoK, show j ≠ 0 by omega, show j ≠ 1 by omega, TwoFactor.trivial]

/-- Right-hand side for the 2-elementary rows: scale-1 type `T0` (dimension $n-k$), scale-2 type `T1` (dimension $k$)
with a condition `Q` on the sign of the scale-2 constituent; $t_1$ is eliminated using the oddity formula. -/
def RhsK (T0 T1 : ScaledType) (Q : Sign → Prop) (n k : ℕ) (σ : ZMod 8) : Prop :=
  1 ≤ k ∧ k ≤ n ∧ ∃ ε0 ∈ signList, ∃ ε1 ∈ signList, ∃ t0 : ZMod 8, ε0.mul ε1 = .plus ∧
    (⟨n - k, ε0, T0, t0⟩ : TwoFactor).Exists ∧
    (⟨k, ε1, T1, σ - t0 - 4 * ind8 (ε1 = .minus)⟩ : TwoFactor).Exists ∧ Q ε1

set_option synthInstance.maxSize 1024 in
instance (T0 T1 : ScaledType) (Q : Sign → Prop) [∀ a, Decidable (Q a)] (n k : ℕ) (σ : ZMod 8) :
    Decidable (RhsK T0 T1 Q n k σ) := by
  unfold RhsK; infer_instance

theorem detK_rowK (T0 T1 : ScaledType) (Q : Sign → Prop) (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = T0 ∧ (G.two 1).dim = k ∧ (G.two 1).type = T1 ∧ Q (G.two 1).sign)) ↔
      RhsK T0 T1 Q (r + s) k ((r : ZMod 8) - s) := by
  refine (detK_exists_iff r s k hk (fun c0 c1 => c0.type = T0 ∧ c1.dim = k ∧ c1.type = T1 ∧
    Q c1.sign)).trans ?_
  constructor
  · rintro ⟨⟨d0, s0, ty0, o0⟩, ⟨d1, s1, ty1, o1⟩, ⟨a1, a2, a3, a4, a5, a6⟩, hT, h1, hT1, hQ⟩
    dsimp only at *
    subst hT h1 hT1
    have hd0 : d0 = r + s - d1 := by omega
    subst hd0
    have ho1 : o1 = ((r : ZMod 8) - s) - o0 - 4 * ind8 (s1 = .minus) := by
      linear_combination -a6
    refine ⟨hk, by omega, s0, mem_signList _, s1, mem_signList _, o0, a5, a3, ?_, hQ⟩
    rw [← ho1]; exact a4
  · rintro ⟨-, hkn, ε0, -, ε1, -, t0, hp, e0, e1, hQ⟩
    exact ⟨⟨r + s - k, ε0, T0, t0⟩, ⟨k, ε1, T1, (r : ZMod 8) - s - t0 - 4 * ind8 (ε1 = .minus)⟩,
      ⟨by simp; omega, rfl, e0, e1, hp, by simp; ring⟩, rfl, rfl, rfl, hQ⟩

/-! ### Reduction of the dimensions -/

/-- Cap a dimension: $m \le 4$ is kept, larger $m$ is replaced by $3$ or $4$ of the same parity. -/
def capf (m : ℕ) : ℕ := if m ≤ 4 then m else 4 - m % 2

theorem capf_le (m : ℕ) : capf m ≤ 4 := by unfold capf; split_ifs <;> omega

theorem capf_pos {m : ℕ} (h : 1 ≤ m) : 1 ≤ capf m := by unfold capf; split_ifs <;> omega

theorem exists_capf (m : ℕ) (ε : Sign) (T : ScaledType) (t : ZMod 8) :
    (⟨m, ε, T, t⟩ : TwoFactor).Exists ↔ (⟨capf m, ε, T, t⟩ : TwoFactor).Exists := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : m ≤ 4
    · have : capf m = m := by unfold capf; rw [if_pos h]
      rw [this]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      rw [exists_stable m' (by omega), ih m' (by omega)]
      have : capf (m' + 2) = capf m' := by
        unfold capf
        by_cases h1 : m' ≤ 4 <;> simp only [h1, if_true, if_false] <;> split_ifs <;> omega
      rw [this]

/-- The existence condition for two constituents of dimensions `a`, `b` (types `T0`, `T1`) with the sign condition
`Q` on the second. -/
def GK (T0 T1 : ScaledType) (Q : Sign → Prop) (a b : ℕ) (σ : ZMod 8) : Prop :=
  ∃ ε0 ∈ signList, ∃ ε1 ∈ signList, ∃ t0 : ZMod 8, ε0.mul ε1 = .plus ∧
    (⟨a, ε0, T0, t0⟩ : TwoFactor).Exists ∧
    (⟨b, ε1, T1, σ - t0 - 4 * ind8 (ε1 = .minus)⟩ : TwoFactor).Exists ∧ Q ε1

set_option synthInstance.maxSize 1024 in
instance (T0 T1 : ScaledType) (Q : Sign → Prop) [∀ a, Decidable (Q a)] (a b : ℕ) (σ : ZMod 8) :
    Decidable (GK T0 T1 Q a b σ) := by
  unfold GK; infer_instance

theorem GK_cap (T0 T1 : ScaledType) (Q : Sign → Prop) (a b : ℕ) (σ : ZMod 8) :
    GK T0 T1 Q a b σ ↔ GK T0 T1 Q (capf a) (capf b) σ := by
  unfold GK
  simp only [exists_capf a, exists_capf b]

theorem rhsK_iff_GK (T0 T1 : ScaledType) (Q : Sign → Prop) (n k : ℕ) (σ : ZMod 8) :
    RhsK T0 T1 Q n k σ ↔ (1 ≤ k ∧ k ≤ n ∧ GK T0 T1 Q (n - k) k σ) := Iff.rfl

theorem GK_iff_of (T0 T1 : ScaledType) (Q : Sign → Prop) (P : ℕ → ℕ → ZMod 8 → Prop)
    (hbase : ∀ a, a ≤ 4 → ∀ b, b ≤ 4 → ∀ σ, 1 ≤ b → (GK T0 T1 Q a b σ ↔ P a b σ))
    (hcap : ∀ a b σ, P a b σ ↔ P (capf a) (capf b) σ) (a b : ℕ) (σ : ZMod 8) (hb : 1 ≤ b) :
    GK T0 T1 Q a b σ ↔ P a b σ := by
  rw [GK_cap, hbase _ (capf_le a) _ (capf_le b) σ (capf_pos hb), ← hcap]

/-! ### The rows of Table 15.5

Notation: $n = r + s$, $\sigma = (r - s) \bmod 8$, $k$ the dimension of the constituent at the scale $2$ (so the
determinant is $\pm2^k$ and $a = n - k$ is the dimension at the scale $1$). -/

/-- Row 1: $\mathrm I_{r,s}(2_{\mathrm I}^k)$, $0 < k < n$. -/
def Pt1 (a b : ℕ) (σ : ZMod 8) : Prop := 0 < b ∧ 0 < a ∧ σ.val % 2 = (a + b) % 2
/-- Row 2: $\mathrm I_{r,s}(2_{\mathrm{II}}^k)$, $k$ even $< n$; $k = n-1 \Rightarrow \sigma \equiv \pm1$;
$k = n-2 \Rightarrow \sigma \not\equiv 4$. -/
def Pt2 (a b : ℕ) (σ : ZMod 8) : Prop :=
  0 < b ∧ b % 2 = 0 ∧ 0 < a ∧ σ.val % 2 = (a + b) % 2 ∧ (a = 1 → σ.val = 1 ∨ σ.val = 7) ∧
    (a = 2 → σ.val ≠ 4)
/-- Row 3: $\mathrm{II}_{r,s}(2_{\mathrm I}^k)$, $0 < k \equiv n \pmod 2$; $k = 1 \Rightarrow \sigma \equiv \pm1$;
$k = 2 \Rightarrow \sigma \not\equiv 4$. -/
def Pt3 (a b : ℕ) (σ : ZMod 8) : Prop :=
  0 < b ∧ a % 2 = 0 ∧ σ.val % 2 = (a + b) % 2 ∧ (b = 1 → σ.val = 1 ∨ σ.val = 7) ∧ (b = 2 → σ.val ≠ 4)
/-- Row 4: $\mathrm{II}_{r,s}(2_{\mathrm{II}}^k)$, $n$ and $k$ even, $\sigma \equiv 0$. -/
def Pt4 (a b : ℕ) (σ : ZMod 8) : Prop := 0 < b ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ σ.val = 0
/-- Row 5: $\mathrm{II}_{r,s}(2_{\mathrm{II}}^{-k})$, $n$ and $k$ even, $0 < k < n$, $\sigma \equiv 4$. -/
def Pt5 (a b : ℕ) (σ : ZMod 8) : Prop := 0 < b ∧ 0 < a ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ σ.val = 4

instance (a b : ℕ) (σ : ZMod 8) : Decidable (Pt1 a b σ) := by unfold Pt1; infer_instance
instance (a b : ℕ) (σ : ZMod 8) : Decidable (Pt2 a b σ) := by unfold Pt2; infer_instance
instance (a b : ℕ) (σ : ZMod 8) : Decidable (Pt3 a b σ) := by unfold Pt3; infer_instance
instance (a b : ℕ) (σ : ZMod 8) : Decidable (Pt4 a b σ) := by unfold Pt4; infer_instance
instance (a b : ℕ) (σ : ZMod 8) : Decidable (Pt5 a b σ) := by unfold Pt5; infer_instance

theorem Pt1_cap (a b σ) : Pt1 a b σ ↔ Pt1 (capf a) (capf b) σ := by
  unfold Pt1 capf; split_ifs <;> omega
theorem Pt2_cap (a b σ) : Pt2 a b σ ↔ Pt2 (capf a) (capf b) σ := by
  unfold Pt2 capf; split_ifs <;> omega
theorem Pt3_cap (a b σ) : Pt3 a b σ ↔ Pt3 (capf a) (capf b) σ := by
  unfold Pt3 capf; split_ifs <;> omega
theorem Pt4_cap (a b σ) : Pt4 a b σ ↔ Pt4 (capf a) (capf b) σ := by
  unfold Pt4 capf; split_ifs <;> omega
theorem Pt5_cap (a b σ) : Pt5 a b σ ↔ Pt5 (capf a) (capf b) σ := by
  unfold Pt5 capf; split_ifs <;> omega

/-- **Table 15.5, row 1: $\mathrm I_{r,s}(2_{\mathrm I}^k)$**, $0 < k < n$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Table 15.5, p. 388 (I(2_I^k))"]
theorem table155_I_2I (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .I ∧ (G.two 1).dim = k ∧ (G.two 1).type = .I ∧ True)) ↔
      (k < r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2) := by
  rw [detK_rowK .I .I (fun _ => True) r s k hk, rhsK_iff_GK]
  have key := GK_iff_of .I .I (fun _ => True) Pt1 (by beta_reduce; decide) Pt1_cap (r + s - k) k
    ((r : ZMod 8) - s) hk
  constructor
  · rintro ⟨-, hkn, hg⟩
    have := key.1 hg
    unfold Pt1 at this
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨hk, by omega, key.2 (by unfold Pt1; omega)⟩

/-- **Table 15.5, row 2: $\mathrm I_{r,s}(2_{\mathrm{II}}^k)$**, $k$ even $< n$; if $k = n-1$ then
$r - s \equiv \pm1 \pmod 8$, if $k = n-2$ then $r - s \not\equiv 4 \pmod 8$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Table 15.5, p. 388 (I(2_II^k))"]
theorem table155_I_2II (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .I ∧ (G.two 1).dim = k ∧ (G.two 1).type = .II ∧ True)) ↔
      (k % 2 = 0 ∧ k < r + s ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2 ∧
        (k + 1 = r + s → (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 7)) ∧
        (k + 2 = r + s → ((r : ZMod 8) - s).val ≠ 4)) := by
  rw [detK_rowK .I .II (fun _ => True) r s k hk, rhsK_iff_GK]
  have key := GK_iff_of .I .II (fun _ => True) Pt2 (by beta_reduce; decide) Pt2_cap (r + s - k) k
    ((r : ZMod 8) - s) hk
  constructor
  · rintro ⟨-, hkn, hg⟩
    have := key.1 hg
    unfold Pt2 at this
    omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨hk, by omega, key.2 (by unfold Pt2; omega)⟩

/-- **Table 15.5, row 3: $\mathrm{II}_{r,s}(2_{\mathrm I}^k)$**, $0 < k \equiv n \pmod 2$; if $k = 1$ then
$r - s \equiv \pm1$, if $k = 2$ then $r - s \not\equiv 4 \pmod 8$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Table 15.5, p. 388 (II(2_I^k))"]
theorem table155_II_2I (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .II ∧ (G.two 1).dim = k ∧ (G.two 1).type = .I ∧ True)) ↔
      (k ≤ r + s ∧ k % 2 = (r + s) % 2 ∧ ((r : ZMod 8) - s).val % 2 = (r + s) % 2 ∧
        (k = 1 → (((r : ZMod 8) - s).val = 1 ∨ ((r : ZMod 8) - s).val = 7)) ∧
        (k = 2 → ((r : ZMod 8) - s).val ≠ 4)) := by
  rw [detK_rowK .II .I (fun _ => True) r s k hk, rhsK_iff_GK]
  have key := GK_iff_of .II .I (fun _ => True) Pt3 (by beta_reduce; decide) Pt3_cap (r + s - k) k
    ((r : ZMod 8) - s) hk
  constructor
  · rintro ⟨-, hkn, hg⟩
    have := key.1 hg
    unfold Pt3 at this
    omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨hk, h1, key.2 (by unfold Pt3; omega)⟩

/-- **Table 15.5, row 4: $\mathrm{II}_{r,s}(2_{\mathrm{II}}^k)$**, $n$ and $k$ even, $r - s \equiv 0 \pmod 8$
(sign $+$ at the scale $2$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Table 15.5, p. 388 (II(2_II^k))"]
theorem table155_II_2II_plus (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .II ∧ (G.two 1).dim = k ∧ (G.two 1).type = .II ∧ (G.two 1).sign = .plus)) ↔
      (k ≤ r + s ∧ (r + s) % 2 = 0 ∧ k % 2 = 0 ∧ ((r : ZMod 8) - s).val = 0) := by
  rw [detK_rowK .II .II (fun ε1 => ε1 = .plus) r s k hk, rhsK_iff_GK]
  have key := GK_iff_of .II .II (fun ε1 => ε1 = .plus) Pt4 (by beta_reduce; decide) Pt4_cap (r + s - k) k
    ((r : ZMod 8) - s) hk
  constructor
  · rintro ⟨-, hkn, hg⟩
    have := key.1 hg
    unfold Pt4 at this
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hk, h1, key.2 (by unfold Pt4; omega)⟩

/-- **Table 15.5, row 5: $\mathrm{II}_{r,s}(2_{\mathrm{II}}^{-k})$**, $n$ and $k$ even, $0 < k < n$,
$r - s \equiv 4 \pmod 8$ (sign $-$ at the scale $2$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Table 15.5, p. 388 (II(2_II^{-k}))"]
theorem table155_II_2II_minus (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .II ∧ (G.two 1).dim = k ∧ (G.two 1).type = .II ∧ (G.two 1).sign = .minus)) ↔
      (k < r + s ∧ (r + s) % 2 = 0 ∧ k % 2 = 0 ∧ ((r : ZMod 8) - s).val = 4) := by
  rw [detK_rowK .II .II (fun ε1 => ε1 = .minus) r s k hk, rhsK_iff_GK]
  have key := GK_iff_of .II .II (fun ε1 => ε1 = .minus) Pt5 (by beta_reduce; decide) Pt5_cap (r + s - k) k
    ((r : ZMod 8) - s) hk
  constructor
  · rintro ⟨-, hkn, hg⟩
    have := key.1 hg
    unfold Pt5 at this
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hk, by omega, key.2 (by unfold Pt5; omega)⟩

end QuadFormsKB.ConwaySloane
