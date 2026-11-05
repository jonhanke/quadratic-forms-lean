/-
# Conway–Sloane, Ch. 15, §8.2: Theorem 13 (b), Table 15.5, the 2-elementary genera

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.2,
Theorem 13 (b) and Table 15.5 (p. 388) (`conwaysloane1999`; printed page = PDF page of the chapter file + 351).

As in `SmallDet.lean`, "the genus exists" means "there is a system of symbols (`GenusSymbolData`) satisfying
`GenusSymbolData.Conditions` ((29)–(35) of §7.7) with the stated invariants"; passing from symbols to forms is
Thm. 11 (`Theorem11.lean`). A *2-elementary* genus has $\lvert\det\rvert = 2^k$ with $k \ge 1$ and 2-adic symbol
$1^{\pm(n-k)}2^{\pm k}$ (only the scales $1$ and $2$), all odd-prime symbols trivial; $n = r + s$.

**What is proved.** Write $\mathrm I$/$\mathrm{II}$ before the brackets for the type of the scale-$1$ constituent (the
lattice is even iff it is $\mathrm{II}$; a zero-dimensional constituent counts as type $\mathrm{II}$) and the subscript
for the type of the scale-$2$ constituent. With $0 < k$ (a hypothesis `1 ≤ k` of every statement):
* `table155_I_I`: $\mathrm I_{r,s}(2^k_{\mathrm I})$ exists iff $k < n$ (printed: $0 < k < n$);
* `table155_I_II`: $\mathrm I_{r,s}(2^k_{\mathrm{II}})$ exists iff $k$ is even, $k < n$, and
  $k = n-1 \Rightarrow r - s \equiv \pm1$, $k = n-2 \Rightarrow r - s \not\equiv 4 \pmod 8$;
* `table155_II_I`: $\mathrm{II}_{r,s}(2^k_{\mathrm I})$ exists iff $k \equiv n \pmod 2$, $k \le n$, and
  $k = 1 \Rightarrow r - s \equiv \pm1$, $k = 2 \Rightarrow r - s \not\equiv 4 \pmod 8$;
* `table155_II_II_plus`: $\mathrm{II}_{r,s}(2^k_{\mathrm{II}})$ (sign $+$) exists iff $n$, $k$ even, $k \le n$,
  $r - s \equiv 0 \pmod 8$;
* `table155_II_II_minus`: $\mathrm{II}_{r,s}(2^{-k}_{\mathrm{II}})$ (sign $-$) exists iff $n$, $k$ even, $k < n$,
  $r - s \equiv 4 \pmod 8$;
* `table155_unique`: *uniqueness*: two systems with the same row data have equal odd-prime symbols and 2-adic symbols
  related by sign walking and oddity fusion (`MoveEquiv`), i.e. there is exactly one genus per row.

**Discrepancies with the printed table.** None of substance: every row is proved exactly as printed, under the
reading that the table's standing hypothesis is $0 < k \le n$ (the book says only "$2^k$" for 2-elementary, so
$k \ge 1$). Two points of reading are made explicit: (i) for $\mathrm{II}_{r,s}(2^k_{\mathrm{II}})$ the case $k = n$
(a zero-dimensional scale-$1$ constituent) *is* allowed, e.g. $\sqrt2E_8$ ($r - s = 8$, $k = n = 8$), so the
condition is $k \le n$, and $k > 0$ has to be added to the printed "$n$ and $k$ even" (for $k = 0$ the genus is not
2-elementary: it is unimodular); (ii) the conditions "$k = n - 1 \Rightarrow r-s \equiv \pm1$" and
"$k = n-2 \Rightarrow r - s \not\equiv 4$" are the existence conditions (33), (34) for the one- and two-dimensional
scale-$1$ (resp. scale-$2$) constituent, exactly as printed; the signs of the constituents are not part of the name of
the rows $\mathrm I(2^k_{\mathrm I})$, $\mathrm I(2^k_{\mathrm{II}})$, $\mathrm{II}(2^k_{\mathrm I})$ because they are
absorbed by sign walking (and the sign $-$ is never needed for existence there).
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables2

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### Definitions -/

/-- **A 2-elementary system of symbols** (Conway–Sloane, §8.2, Thm. 13 (b), Table 15.5): a system `G` of local symbols
satisfying the conditions (29)–(35) of §7.7, with $(-1)$-adic symbol $+^r-^s$, $\lvert\det\rvert = 2^k$, 2-adic
constituents only at the scales $2^0 = 1$ (dimension $n - k$, type `T₀`) and $2^1 = 2$ (dimension $k$, type `T₁`), and
trivial symbols (no constituent of positive scale) at every odd prime. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388"]
def TwoElemGenus (G : GenusSymbolData) (r s k : ℕ) (T₀ T₁ : ScaledType) : Prop :=
  G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
    (G.two 0).dim + k = r + s ∧ (G.two 1).dim = k ∧ (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
    (G.two 0).type = T₀ ∧ (G.two 1).type = T₁ ∧
    (∀ q, q.Prime → q ≠ 2 → ∀ j, 1 ≤ j → G.odd q j = OddFactor.trivial)

/-! ### Helper lemmas -/

theorem twoElem_natAbs (k s : ℕ) : ((2 : ℤ) ^ k * (-1) ^ s).natAbs = 2 ^ k := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem twoElem_padicValInt (k s : ℕ) : padicValInt 2 ((2 : ℤ) ^ k * (-1) ^ s) = k := by
  simp [padicValInt, twoElem_natAbs]

theorem twoElem_padicValInt_ne (q k s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q ((2 : ℤ) ^ k * (-1) ^ s) = 0 := by
  have : ¬ q ∣ 2 ^ k := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  simp [padicValInt, twoElem_natAbs, padicValNat.eq_zero_of_not_dvd this]

theorem twoElem_div (k s : ℕ) : ((2 : ℤ) ^ k * (-1) ^ s) / 2 ^ k = (-1) ^ s :=
  Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num))

theorem twoElem_dmod (r s : ℕ) : (((r : ZMod 8) - s).val : ℤ) = ((r : ℤ) - s) % 8 := by
  have e : ((r : ZMod 8) - s) = (((r : ℤ) - s : ℤ) : ZMod 8) := by push_cast; rfl
  rw [e]
  have h := ZMod.val_intCast (n := 8) ((r : ℤ) - s)
  omega

theorem zmod8_c17 : ∀ x : ZMod 8, (x = 1 ∨ x = 7) ↔ ((x.val : ℤ) = 1 ∨ (x.val : ℤ) = 7) := by decide

theorem zmod8_c026 : ∀ x : ZMod 8, x.val % 2 = 0 → ((x = 0 ∨ x = 2 ∨ x = 6) ↔ (x.val : ℤ) ≠ 4) := by decide

theorem zmod8_c4 : ∀ x : ZMod 8, x = 4 ↔ (x.val : ℤ) = 4 := by decide

theorem twoElem_c17 (r s : ℕ) :
    (((r : ZMod 8) - s = 1 ∨ (r : ZMod 8) - s = 7) ↔ (((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 7)) := by
  rw [zmod8_c17, twoElem_dmod]

theorem twoElem_c026 (r s : ℕ) (h : (r + s) % 2 = 0) :
    (((r : ZMod 8) - s = 0 ∨ (r : ZMod 8) - s = 2 ∨ (r : ZMod 8) - s = 6) ↔ ((r : ℤ) - s) % 8 ≠ 4) := by
  rw [zmod8_c026 _ (by rw [val_sub_mod_two]; exact h), twoElem_dmod]

theorem twoElem_c4 (r s : ℕ) : ((r : ZMod 8) - s = 4) ↔ ((r : ℤ) - s) % 8 = 4 := by
  rw [zmod8_c4, twoElem_dmod]

theorem val_sub_par : ∀ a b : ZMod 8, (a - b).val % 2 = (a.val + b.val) % 2 := by decide

/-! ### Existence conditions for the constituents -/

theorem twoElem_exists_II (m : ℕ) (ε : Sign) (hm : m % 2 = 0) (h0 : m = 0 → ε = .plus) :
    (⟨m, ε, .II, 0⟩ : TwoFactor).Exists := by
  refine ⟨fun h => ⟨rfl, h0 h⟩, fun h1 => ?_, (fun _ hI => by cases hI), ?_, fun _ => rfl⟩
  · exfalso
    have h1' : m = 1 := h1
    omega
  · show (0 : ZMod 8).val % 2 = m % 2
    simp
    omega

theorem twoElem_exists_I_plus (m : ℕ) (t : ZMod 8) (hm : 1 ≤ m) (hp : t.val % 2 = m % 2)
    (h1 : m = 1 → t = 1 ∨ t = 7) (h2 : m = 2 → t = 0 ∨ t = 2 ∨ t = 6) :
    (⟨m, .plus, .I, t⟩ : TwoFactor).Exists := by
  refine ⟨fun h => ?_, fun h => ?_, fun h _ => ?_, hp, fun h => nomatch h⟩
  · exfalso
    have : m = 0 := h
    omega
  · exact ⟨fun _ => h1 h, fun hh => nomatch hh⟩
  · exact ⟨fun _ => h2 h, fun hh => nomatch hh⟩

theorem TwoFactor.Exists.pos_of_typeI {f : TwoFactor} (h : f.Exists) (hT : f.type = .I) : 1 ≤ f.dim := by
  by_contra hh
  have := (h.1 (by omega)).1
  rw [hT] at this
  exact absurd this (by decide)

theorem TwoFactor.Exists.eff1 {f : TwoFactor} (h : f.Exists) (hT : f.type = .I) (h1 : f.dim = 1) :
    f.oddity + 4 * ind8 (f.sign = .minus) = 1 ∨ f.oddity + 4 * ind8 (f.sign = .minus) = 7 := by
  obtain ⟨m, ε, T, t⟩ := f
  dsimp only at hT h1
  subst hT h1
  exact exists1_values ε t h

set_option synthInstance.maxSize 1024 in
theorem twoElem_exists2_values : ∀ (ε : Sign) (t : ZMod 8), (⟨2, ε, .I, t⟩ : TwoFactor).Exists →
    (t + 4 * ind8 (ε = .minus) = 0 ∨ t + 4 * ind8 (ε = .minus) = 2 ∨ t + 4 * ind8 (ε = .minus) = 6) := by
  intro ε
  cases ε <;> decide

theorem TwoFactor.Exists.eff2 {f : TwoFactor} (h : f.Exists) (hT : f.type = .I) (h2 : f.dim = 2) :
    f.oddity + 4 * ind8 (f.sign = .minus) = 0 ∨ f.oddity + 4 * ind8 (f.sign = .minus) = 2 ∨
      f.oddity + 4 * ind8 (f.sign = .minus) = 6 := by
  obtain ⟨m, ε, T, t⟩ := f
  dsimp only at hT h2
  subst hT h2
  exact twoElem_exists2_values ε t h

theorem TwoFactor.Exists.oddity_of_typeII {f : TwoFactor} (h : f.Exists) (hT : f.type = .II) : f.oddity = 0 :=
  h.2.2.2.2 hT

theorem TwoFactor.Exists.even_of_typeII {f : TwoFactor} (h : f.Exists) (hT : f.type = .II) : f.dim % 2 = 0 := by
  have hp : f.oddity.val % 2 = f.dim % 2 := h.2.2.2.1
  rw [h.oddity_of_typeII hT, ZMod.val_zero] at hp
  omega

theorem twoElem_exists_base (m : ℕ) (hm : 1 ≤ m) : ∃ t : ZMod 8, (⟨m, .plus, .I, t⟩ : TwoFactor).Exists := by
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  · exact ⟨((m % 2 : ℕ) : ZMod 8), typeI_big .plus m _ h (by rw [ZMod.val_natCast]; omega)⟩

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
theorem twoElem_exists_pair_small : ∀ m₀ : ℕ, m₀ ≤ 2 → ∀ m₁ : ℕ, m₁ ≤ 2 → 1 ≤ m₀ → 1 ≤ m₁ → ∀ d : ZMod 8,
    d.val % 2 = (m₀ + m₁) % 2 → (m₀ = 1 → m₁ = 1 → d ≠ 4) →
      ∃ t₀ t₁ : ZMod 8, (⟨m₀, .plus, .I, t₀⟩ : TwoFactor).Exists ∧
      (⟨m₁, .plus, .I, t₁⟩ : TwoFactor).Exists ∧ d = t₀ + t₁ := by
  decide

theorem twoElem_exists_pair (m₀ m₁ : ℕ) (h₀ : 1 ≤ m₀) (h₁ : 1 ≤ m₁) (d : ZMod 8)
    (hd : d.val % 2 = (m₀ + m₁) % 2) (hne : m₀ = 1 → m₁ = 1 → d ≠ 4) :
    ∃ t₀ t₁ : ZMod 8, (⟨m₀, .plus, .I, t₀⟩ : TwoFactor).Exists ∧ (⟨m₁, .plus, .I, t₁⟩ : TwoFactor).Exists ∧
      d = t₀ + t₁ := by
  by_cases h3 : 3 ≤ m₀
  · obtain ⟨t₁, e₁⟩ := twoElem_exists_base m₁ h₁
    have e : t₁.val % 2 = m₁ % 2 := e₁.2.2.2.1
    refine ⟨d - t₁, t₁, typeI_big _ _ _ h3 ?_, e₁, by ring⟩
    have := val_sub_par d t₁
    omega
  · by_cases h3' : 3 ≤ m₁
    · obtain ⟨t₀, e₀⟩ := twoElem_exists_base m₀ h₀
      have e : t₀.val % 2 = m₀ % 2 := e₀.2.2.2.1
      refine ⟨t₀, d - t₀, e₀, typeI_big _ _ _ h3' ?_, by ring⟩
      have := val_sub_par d t₀
      omega
    · exact twoElem_exists_pair_small m₀ (by omega) m₁ (by omega) h₀ h₁ d hd hne

/-! ### The system of symbols -/

/-- **The system of symbols of a 2-elementary genus**: determinant $2^k(-1)^s$, $(-1)$-adic symbol $+^r-^s$, the
$p$-adic symbol $1^{\varepsilon_p(r+s)}$ at every odd $p$, and the 2-adic symbol
$1_{t_0}^{\varepsilon(n-k)}2_{t_1}^{\varepsilon k}$ with the constituents of types `T₀`, `T₁`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388"]
def twoElemData (r s k : ℕ) (ε : Sign) (T₀ : ScaledType) (t₀ : ZMod 8) (T₁ : ScaledType) (t₁ : ZMod 8) :
    GenusSymbolData where
  n := r + s
  det := 2 ^ k * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q j => if j = 0 then ⟨r + s, Sign.ofInt (jacobiSym (2 ^ k * (-1) ^ s) q)⟩ else OddFactor.trivial
  two := fun j =>
    if j = 0 then ⟨r + s - k, ε, T₀, t₀⟩ else if j = 1 then ⟨k, ε, T₁, t₁⟩ else TwoFactor.trivial
  N := 2

theorem twoElemData_conditions (r s k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ r + s) (ε : Sign) (T₀ : ScaledType)
    (t₀ : ZMod 8) (T₁ : ScaledType) (t₁ : ZMod 8)
    (h0 : (⟨r + s - k, ε, T₀, t₀⟩ : TwoFactor).Exists) (h1 : (⟨k, ε, T₁, t₁⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s = t₀ + t₁ + 4 * ind8 (ε = .minus)) :
    (twoElemData r s k ε T₀ t₀ T₁ t₁).Conditions where
  ne_zero := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    have hpos : (0 : ℤ) < 2 ^ k := by positivity
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp only [twoElemData, h.neg_one_pow, this, mul_one, iff_false, not_lt]
      exact hpos.le
    · simp only [twoElemData, h.neg_one_pow, h, mul_neg, mul_one, iff_true]
      linarith
  odd_supp q j hj := by
    have hj' : 2 ≤ j := hj
    simp [twoElemData, show j ≠ 0 by omega]
  two_supp j hj := by
    have hj' : 2 ≤ j := hj
    simp [twoElemData, show j ≠ 0 by omega, show j ≠ 1 by omega]
  odd_dim q _ _ := by simp [twoElemData, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by
    simp [twoElemData, Finset.sum_range_succ]
    omega
  odd_det q hq hq2 := by
    have hv := twoElem_padicValInt_ne q k s hq hq2
    refine ⟨?_, ?_⟩
    · simp [twoElemData, hv, Finset.sum_range_succ, OddFactor.trivial]
    · simp [twoElemData, hv, signProd, Sign.plus_mul, Sign.mul_plus, OddFactor.trivial]
  two_det := by
    have hv := twoElem_padicValInt k s
    refine ⟨by simp [twoElemData, hv, Finset.sum_range_succ], ?_⟩
    simp [twoElemData, hv, signProd, jacobiTwo_pm_one, Sign.plus_mul, TwoFactor.trivial]
    cases ε <;> rfl
  odd_exists q hq hq2 j := by
    by_cases hj : j = 0
    · subst hj
      simp only [twoElemData, ↓reduceIte]
      intro h0'
      have : r + s = 0 := h0'
      omega
    · simp [twoElemData, hj, OddFactor.Exists, OddFactor.trivial]
  two_exists j := by
    by_cases hj : j = 0
    · subst hj; simpa [twoElemData] using h0
    · by_cases hj1 : j = 1
      · subst hj1; simpa [twoElemData] using h1
      · simp only [twoElemData, hj, hj1, ↓reduceIte]
        decide
  oddity_formula := by
    have hna : (twoElemData r s k ε T₀ t₀ T₁ t₁).det.natAbs = 2 ^ k := by
      simp [twoElemData, twoElem_natAbs]
    rw [hna, Nat.primeFactors_prime_pow (by omega) Nat.prime_two, Finset.filter_singleton]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_empty, add_zero]
    simp [twoElemData, GenusSymbolData.signature, TwoSymbol.oddity, ind8, Finset.sum_range_succ, TwoFactor.trivial]
    rw [ht]
    unfold ind8
    split_ifs <;> ring

theorem twoElem_exists (r s k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ r + s) (ε : Sign) (T₀ : ScaledType) (t₀ : ZMod 8)
    (T₁ : ScaledType) (t₁ : ZMod 8)
    (h0 : (⟨r + s - k, ε, T₀, t₀⟩ : TwoFactor).Exists) (h1 : (⟨k, ε, T₁, t₁⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s = t₀ + t₁ + 4 * ind8 (ε = .minus)) :
    TwoElemGenus (twoElemData r s k ε T₀ t₀ T₁ t₁) r s k T₀ T₁ ∧
      ((twoElemData r s k ε T₀ t₀ T₁ t₁).two 1).sign = ε := by
  refine ⟨⟨twoElemData_conditions r s k hk hkn ε T₀ t₀ T₁ t₁ h0 h1 ht, rfl, by simp [twoElemData, twoElem_natAbs],
    by simp [twoElemData]; omega, by simp [twoElemData], ?_, by simp [twoElemData], by simp [twoElemData], ?_⟩,
    by simp [twoElemData]⟩
  · intro j hj
    have : j ≠ 0 := by omega
    have : j ≠ 1 := by omega
    simp [twoElemData, *, TwoFactor.trivial]
  · intro q _ _ j hj
    have : j ≠ 0 := by omega
    simp [twoElemData, *]

/-! ### The data forced by the conditions -/

theorem TwoElemGenus.det_eq {G : GenusSymbolData} {r s k : ℕ} {T₀ T₁ : ScaledType}
    (h : TwoElemGenus G r s k T₀ T₁) : G.det = 2 ^ k * (-1) ^ s := by
  obtain ⟨hc, hr, hd, -⟩ := h
  have := G.det_eq_of hc (m := 2 ^ k) (by positivity) hd hr
  simpa using this

/-- **The data forced by the conditions for a 2-elementary genus**: $(\dim f_1) + k = n$, no constituent of scale
$\ge 4$, the signs of the two constituents agree, the oddity formula
$r - s \equiv t_0 + t_1 + 4[\varepsilon = -]$, and the two constituents exist ((32)–(35)). -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388"]
theorem TwoElemGenus.part {G : GenusSymbolData} {r s k : ℕ} {T₀ T₁ : ScaledType}
    (h : TwoElemGenus G r s k T₀ T₁) (hk : 1 ≤ k) :
    (G.two 0).dim + k = r + s ∧ (∀ j, 2 ≤ j → G.two j = TwoFactor.trivial) ∧
      (G.two 0).sign = (G.two 1).sign ∧
      (r : ZMod 8) - s = (G.two 0).oddity + (G.two 1).oddity + 4 * ind8 ((G.two 1).sign = .minus) ∧
      (G.two 0).Exists ∧ (G.two 1).Exists := by
  have hdet := h.det_eq
  obtain ⟨hc, hr, hd, hdim0, d1, hel, -, -, -⟩ := h
  have hv2 : padicValInt 2 G.det = k := by rw [hdet]; exact twoElem_padicValInt k s
  obtain ⟨-, hsg⟩ := hc.two_det
  rw [hv2] at hsg
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
  have hN2 : 2 ≤ G.N := by
    by_contra hN
    have := hsupp 1 (by omega)
    rw [this] at d1
    simp [TwoFactor.trivial] at d1
    omega
  have hsign : (G.two 0).sign = (G.two 1).sign := by
    rw [signProd_stable (fun j => (G.two j).sign) hN2
      (fun j hj => by simp [t2 j hj, TwoFactor.trivial]), hdet, twoElem_div, jacobiTwo_pm_one] at hsg
    simp only [signProd, Sign.plus_mul] at hsg
    revert hsg
    cases (G.two 0).sign <;> cases (G.two 1).sign <;> intro hh <;> first | rfl | exact absurd hh (by decide)
  refine ⟨hdim0, t2, hsign, ?_, hex 0, hex 1⟩
  have hf := hc.oddity_formula
  rw [hd, Nat.primeFactors_prime_pow (by omega) Nat.prime_two, Finset.filter_singleton] at hf
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_empty, add_zero] at hf
  have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
  rw [← hsig, hf]
  have hsupp2 : G.two.SupportedBelow 2 := fun j hj => t2 j hj
  rw [TwoSymbol.oddity_congr hsupp2 hN2]
  unfold TwoSymbol.oddity
  simp [Finset.sum_range_succ, ind8]
  ring

theorem TwoElemGenus.odd_unit {G : GenusSymbolData} {r s k : ℕ} {T₀ T₁ : ScaledType}
    (h : TwoElemGenus G r s k T₀ T₁) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (j : ℕ) :
    G.odd q j = if j = 0 then ⟨r + s, Sign.ofInt (jacobiSym (2 ^ k * (-1) ^ s) q)⟩ else OddFactor.trivial := by
  have hdet := h.det_eq
  have hn : G.n = r + s := by rw [← h.1.real_dim, h.2.1]
  rw [G.odd_unit h.1 q hq hq2 (by rw [hdet]; exact twoElem_padicValInt_ne q k s hq hq2), hn, hdet]

/-! ### Table 15.5: existence -/

/-- **Table 15.5, $\mathrm I_{r,s}(2^k_{\mathrm I})$** (Conway–Sloane, §8.2, Thm. 13 (b), p. 388): a 2-elementary genus
with both the scale-$1$ and the scale-$2$ constituent of type I exists iff $k < n$ ($n = r + s$, $k \ge 1$), as
printed. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388 (I_{r,s}(2^k_I))"]
theorem table155_I_I (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, TwoElemGenus G r s k .I .I) ↔ k < r + s := by
  constructor
  · rintro ⟨G, h⟩
    obtain ⟨hn, -, -, -, hE0, -⟩ := h.part hk
    have := hE0.pos_of_typeI h.2.2.2.2.2.2.1
    omega
  · intro hlt
    obtain ⟨t₀, t₁, e₀, e₁, hsum⟩ := twoElem_exists_pair (r + s - k) k (by omega) hk ((r : ZMod 8) - s)
      (by rw [val_sub_mod_two]; omega)
      (fun h1 h2 hd4 => by have := (twoElem_c4 r s).1 hd4; omega)
    exact ⟨_, (twoElem_exists r s k hk hlt.le .plus .I t₀ .I t₁ e₀ e₁ (by simp [ind8, hsum])).1⟩

/-- **Table 15.5, $\mathrm I_{r,s}(2^k_{\mathrm{II}})$** (Conway–Sloane, §8.2, Thm. 13 (b), p. 388): scale-$1$ type
I, scale-$2$ type II: exists iff $k$ is even, $k < n$, and $r - s \equiv \pm1 \pmod 8$ if $k = n - 1$, $r - s \not\equiv
4 \pmod 8$ if $k = n - 2$; as printed. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388 (I_{r,s}(2^k_II))"]
theorem table155_I_II (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, TwoElemGenus G r s k .I .II) ↔
      (Even k ∧ k < r + s ∧ (k + 1 = r + s → ((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 7) ∧
        (k + 2 = r + s → ((r : ℤ) - s) % 8 ≠ 4)) := by
  constructor
  · rintro ⟨G, h⟩
    obtain ⟨hn, -, hsg, hsig, hE0, hE1⟩ := h.part hk
    have hT0 : (G.two 0).type = .I := h.2.2.2.2.2.2.1
    have hT1 : (G.two 1).type = .II := h.2.2.2.2.2.2.2.1
    have d1 : (G.two 1).dim = k := h.2.2.2.2.1
    have hev := hE1.even_of_typeII hT1
    have hpos := hE0.pos_of_typeI hT0
    have hdeff : (r : ZMod 8) - s = (G.two 0).oddity + 4 * ind8 ((G.two 0).sign = .minus) := by
      rw [hsig, hE1.oddity_of_typeII hT1, hsg]; ring
    refine ⟨Nat.even_iff.2 (by omega), by omega, fun h1 => ?_, fun h2 => ?_⟩
    · have := hE0.eff1 hT0 (by omega)
      exact (twoElem_c17 r s).1 (by rw [hdeff]; exact this)
    · have := hE0.eff2 hT0 (by omega)
      exact (twoElem_c026 r s (by omega)).1 (by rw [hdeff]; exact this)
  · rintro ⟨hev, hlt, h1, h2⟩
    have hev' : k % 2 = 0 := Nat.even_iff.1 hev
    have hpar : ((r : ZMod 8) - s).val % 2 = (r + s - k) % 2 := by rw [val_sub_mod_two]; omega
    have e₀ : (⟨r + s - k, .plus, .I, (r : ZMod 8) - s⟩ : TwoFactor).Exists :=
      twoElem_exists_I_plus _ _ (by omega) hpar (fun h => (twoElem_c17 r s).2 (h1 (by omega)))
        (fun h => (twoElem_c026 r s (by omega)).2 (h2 (by omega)))
    have e₁ : (⟨k, .plus, .II, 0⟩ : TwoFactor).Exists := twoElem_exists_II k .plus hev' (fun _ => rfl)
    exact ⟨_, (twoElem_exists r s k hk hlt.le .plus .I _ .II 0 e₀ e₁ (by simp [ind8])).1⟩

/-- **Table 15.5, $\mathrm{II}_{r,s}(2^k_{\mathrm I})$** (Conway–Sloane, §8.2, Thm. 13 (b), p. 388): scale-$1$ type
II, scale-$2$ type I: exists iff $k \equiv n \pmod 2$, $k \le n$, and $r - s \equiv \pm1$ if $k = 1$, $r - s \not\equiv
4 \pmod 8$ if $k = 2$; as printed ($k = n$ is allowed: the scale-$1$ constituent is then zero-dimensional). -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388 (II_{r,s}(2^k_I))"]
theorem table155_II_I (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, TwoElemGenus G r s k .II .I) ↔
      (k % 2 = (r + s) % 2 ∧ k ≤ r + s ∧ (k = 1 → ((r : ℤ) - s) % 8 = 1 ∨ ((r : ℤ) - s) % 8 = 7) ∧
        (k = 2 → ((r : ℤ) - s) % 8 ≠ 4)) := by
  constructor
  · rintro ⟨G, h⟩
    obtain ⟨hn, -, hsg, hsig, hE0, hE1⟩ := h.part hk
    have hT0 : (G.two 0).type = .II := h.2.2.2.2.2.2.1
    have hT1 : (G.two 1).type = .I := h.2.2.2.2.2.2.2.1
    have d1 : (G.two 1).dim = k := h.2.2.2.2.1
    have hev := hE0.even_of_typeII hT0
    have hdeff : (r : ZMod 8) - s = (G.two 1).oddity + 4 * ind8 ((G.two 1).sign = .minus) := by
      rw [hsig, hE0.oddity_of_typeII hT0]; ring
    refine ⟨by omega, by omega, fun h1 => ?_, fun h2 => ?_⟩
    · have := hE1.eff1 hT1 (by omega)
      exact (twoElem_c17 r s).1 (by rw [hdeff]; exact this)
    · have := hE1.eff2 hT1 (by omega)
      exact (twoElem_c026 r s (by omega)).1 (by rw [hdeff]; exact this)
  · rintro ⟨hpar, hkn, h1, h2⟩
    have hpar' : ((r : ZMod 8) - s).val % 2 = k % 2 := by rw [val_sub_mod_two]; omega
    have e₀ : (⟨r + s - k, .plus, .II, 0⟩ : TwoFactor).Exists :=
      twoElem_exists_II _ .plus (by omega) (fun _ => rfl)
    have e₁ : (⟨k, .plus, .I, (r : ZMod 8) - s⟩ : TwoFactor).Exists :=
      twoElem_exists_I_plus _ _ hk hpar' (fun h => (twoElem_c17 r s).2 (h1 h))
        (fun h => (twoElem_c026 r s (by omega)).2 (h2 h))
    exact ⟨_, (twoElem_exists r s k hk hkn .plus .II 0 .I _ e₀ e₁ (by simp [ind8])).1⟩

/-- **Table 15.5, $\mathrm{II}_{r,s}(2^k_{\mathrm{II}})$** (Conway–Sloane, §8.2, Thm. 13 (b), p. 388): both
constituents of type II, sign $+$: exists iff $n$ and $k$ are even, $k \le n$ and $r - s \equiv 0 \pmod 8$. The printed
table omits $k \le n$ (standing hypothesis) and $k > 0$ (2-elementary); $k = n$ is allowed. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388 (II_{r,s}(2^k_II))"]
theorem table155_II_II_plus (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, TwoElemGenus G r s k .II .II ∧ (G.two 1).sign = .plus) ↔
      (k ≤ r + s ∧ Even (r + s) ∧ Even k ∧ ((r : ℤ) - s) % 8 = 0) := by
  constructor
  · rintro ⟨G, h, hs1⟩
    obtain ⟨hn, -, hsg, hsig, hE0, hE1⟩ := h.part hk
    have hT0 : (G.two 0).type = .II := h.2.2.2.2.2.2.1
    have hT1 : (G.two 1).type = .II := h.2.2.2.2.2.2.2.1
    have d1 : (G.two 1).dim = k := h.2.2.2.2.1
    have hev0 := hE0.even_of_typeII hT0
    have hev1 := hE1.even_of_typeII hT1
    rw [hE0.oddity_of_typeII hT0, hE1.oddity_of_typeII hT1, hs1] at hsig
    have hz : (r : ZMod 8) - s = 0 := by rw [hsig]; simp [ind8]
    exact ⟨by omega, Nat.even_iff.2 (by omega), Nat.even_iff.2 (by omega), (sub_eq_zero_iff_mod r s).1 hz⟩
  · rintro ⟨hkn, hn, hev, hm⟩
    have hn' := Nat.even_iff.1 hn
    have hev' := Nat.even_iff.1 hev
    have e₀ : (⟨r + s - k, .plus, .II, 0⟩ : TwoFactor).Exists :=
      twoElem_exists_II _ .plus (by omega) (fun _ => rfl)
    have e₁ : (⟨k, .plus, .II, 0⟩ : TwoFactor).Exists := twoElem_exists_II k .plus hev' (fun _ => rfl)
    exact ⟨_, twoElem_exists r s k hk hkn .plus .II 0 .II 0 e₀ e₁
      (by rw [(sub_eq_zero_iff_mod r s).2 hm]; simp [ind8])⟩

/-- **Table 15.5, $\mathrm{II}_{r,s}(2^{-k}_{\mathrm{II}})$** (Conway–Sloane, §8.2, Thm. 13 (b), p. 388): both
constituents of type II, sign $-$: exists iff $n$ and $k$ are even, $k < n$ and $r - s \equiv 4 \pmod 8$; as printed. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388 (II_{r,s}(2^{-k}_II))"]
theorem table155_II_II_minus (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, TwoElemGenus G r s k .II .II ∧ (G.two 1).sign = .minus) ↔
      (k < r + s ∧ Even (r + s) ∧ Even k ∧ ((r : ℤ) - s) % 8 = 4) := by
  constructor
  · rintro ⟨G, h, hs1⟩
    obtain ⟨hn, -, hsg, hsig, hE0, hE1⟩ := h.part hk
    have hT0 : (G.two 0).type = .II := h.2.2.2.2.2.2.1
    have hT1 : (G.two 1).type = .II := h.2.2.2.2.2.2.2.1
    have d1 : (G.two 1).dim = k := h.2.2.2.2.1
    have hev0 := hE0.even_of_typeII hT0
    have hev1 := hE1.even_of_typeII hT1
    have hpos : 1 ≤ (G.two 0).dim := by
      by_contra hh
      have := (hE0.1 (by omega)).2
      rw [hsg, hs1] at this
      exact absurd this (by decide)
    rw [hE0.oddity_of_typeII hT0, hE1.oddity_of_typeII hT1, hs1] at hsig
    have hz : (r : ZMod 8) - s = 4 := by rw [hsig]; simp [ind8]
    exact ⟨by omega, Nat.even_iff.2 (by omega), Nat.even_iff.2 (by omega), (twoElem_c4 r s).1 hz⟩
  · rintro ⟨hkn, hn, hev, hm⟩
    have hn' := Nat.even_iff.1 hn
    have hev' := Nat.even_iff.1 hev
    have e₀ : (⟨r + s - k, .minus, .II, 0⟩ : TwoFactor).Exists :=
      twoElem_exists_II _ .minus (by omega) (fun h => absurd h (by omega))
    have e₁ : (⟨k, .minus, .II, 0⟩ : TwoFactor).Exists :=
      twoElem_exists_II k .minus hev' (fun h => absurd h (by omega))
    exact ⟨_, twoElem_exists r s k hk hkn.le .minus .II 0 .II 0 e₀ e₁
      (by rw [(twoElem_c4 r s).2 hm]; simp [ind8])⟩

/-! ### Table 15.5: uniqueness -/

theorem twoElem_toII {t : ScaledType} (h : ¬ t = .I) : t = .II := by cases t <;> simp_all

theorem twoElem_minusBelow (σ : TwoSymbol) (ht : ∀ j, 2 ≤ j → σ j = TwoFactor.trivial) :
    ∀ m, 2 ≤ m → minusBelow σ m =
      (if (σ 0).sign = .minus then 1 else 0) + (if (σ 1).sign = .minus then 1 else 0) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp [minusBelow]
  | succ m hm ih =>
    rw [minusBelow, ih, ht m hm]
    simp [TwoFactor.trivial]

theorem twoElem_compartments (σ : TwoSymbol) (ht : ∀ j, 2 ≤ j → σ j = TwoFactor.trivial) {c₁ c₂ : ℕ}
    (h : IsCompartment σ c₁ c₂) :
    (c₁ = 0 ∧ c₂ = 0 ∧ (σ 0).type = .I ∧ (σ 1).type = .II) ∨
      (c₁ = 0 ∧ c₂ = 1 ∧ (σ 0).type = .I ∧ (σ 1).type = .I) ∨
      (c₁ = 1 ∧ c₂ = 1 ∧ (σ 0).type = .II ∧ (σ 1).type = .I) := by
  have hnI : ∀ j, 2 ≤ j → ¬ IsTypeI σ j := fun j hj => by simp [IsTypeI, ht j hj, TwoFactor.trivial]
  have toII : ∀ t : ScaledType, t ≠ .I → t = .II := fun t ht => by cases t <;> simp_all
  obtain ⟨hle, hall, hstart, hend⟩ := h
  have h2 : (σ c₂).type = .I := hall c₂ hle le_rfl
  have hc2 : c₂ < 2 := by
    by_contra hh
    exact hnI c₂ (by omega) h2
  have hc2' : c₂ = 0 ∨ c₂ = 1 := by omega
  rcases hc2' with rfl | rfl
  · have hc1 : c₁ = 0 := by omega
    subst hc1
    have : ¬ IsTypeI σ 1 := hend
    exact Or.inl ⟨rfl, rfl, h2, toII _ this⟩
  · rcases (by omega : c₁ = 0 ∨ c₁ = 1) with rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl, hall 0 le_rfl hle, h2⟩)
    · rcases hstart with hh | hh
      · omega
      · exact Or.inr (Or.inr ⟨rfl, rfl, toII _ hh, h2⟩)

theorem twoElem_compInv (σ : TwoSymbol) (ht : ∀ j, 2 ≤ j → σ j = TwoFactor.trivial)
    (hsg : (σ 0).sign = (σ 1).sign) (hE0 : (σ 0).Exists) (hE1 : (σ 1).Exists) (d : ZMod 8)
    (hsig : d = (σ 0).oddity + (σ 1).oddity + 4 * ind8 ((σ 1).sign = .minus)) {c₁ c₂ : ℕ}
    (h : IsCompartment σ c₁ c₂) : compartmentInvariant σ c₁ c₂ = d := by
  have e01 : Finset.Icc 0 1 = {0, 1} := by decide
  have e02 : Finset.Icc 0 2 = {0, 1, 2} := by decide
  have e00 : Finset.Icc 0 0 = {0} := by decide
  have e11 : Finset.Icc 1 1 = {1} := by decide
  have e12 : Finset.Icc 1 2 = {1, 2} := by decide
  rcases twoElem_compartments σ ht h with ⟨rfl, rfl, hT0, hT1⟩ | ⟨rfl, rfl, hT0, hT1⟩ | ⟨rfl, rfl, hT0, hT1⟩
  · have h1 := hE1.oddity_of_typeII hT1
    simp only [compartmentInvariant, e00, e01]
    rw [hsig, h1]
    simp [minusBelow, hsg, ind8]
  · simp only [compartmentInvariant, e01, e02]
    rw [hsig]
    simp [minusBelow, hsg, ind8]
    cases (σ 1).sign
    · simp
    · simp; decide
  · have h0 := hE0.oddity_of_typeII hT0
    simp only [compartmentInvariant, e11, e12]
    rw [hsig, h0]
    simp [minusBelow, hsg, ind8]
    cases (σ 1).sign
    · simp
    · simp; decide

theorem twoElem_four_ind (a b : Sign) (d : ZMod 8) (ha : d = 4 * ind8 (a = .minus)) (hb : d = 4 * ind8 (b = .minus)) :
    (4 * (((if a = .minus then 1 else 0 : ℕ)) : ZMod 8)) = 4 * (((if b = .minus then 1 else 0 : ℕ)) : ZMod 8) := by
  revert ha hb
  revert d
  cases a <;> cases b <;> decide

theorem twoElem_four_ind2 (a b : Sign) (h : a = b) :
    4 * ((((if a = .minus then 1 else 0 : ℕ) + (if b = .minus then 1 else 0 : ℕ) : ℕ)) : ZMod 8) = 0 := by
  subst h
  cases a <;> decide

/-- **Uniqueness of the genus in Table 15.5** (Conway–Sloane, §8.2, Thm. 13 (b), p. 388): two 2-elementary systems of
symbols with the same $(r, s)$, $k$ and types of the two constituents have the same $p$-adic symbols at the odd primes
and $2$-adic symbols related by sign walking and oddity fusion: for each row of the table (each $(r,s,k)$ and types)
there is at most one genus. (For the rows $\mathrm{II}(2^{\pm k}_{\mathrm{II}})$ the common sign of the two
constituents is determined by $r - s \bmod 8$, so it need not be assumed.) -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (b), Table 15.5, p. 388 (one genus for each row)"]
theorem table155_unique {G G' : GenusSymbolData} {r s k : ℕ} {T₀ T₁ : ScaledType} (hk : 1 ≤ k)
    (h : TwoElemGenus G r s k T₀ T₁) (h' : TwoElemGenus G' r s k T₀ T₁) :
    (∀ q, q.Prime → q ≠ 2 → G.odd q = G'.odd q) ∧ MoveEquiv G.two G'.two := by
  refine ⟨fun q hq hq2 => ?_, ?_⟩
  · funext j
    rw [h.odd_unit q hq hq2, h'.odd_unit q hq hq2]
  · obtain ⟨hn, t2, hsg, hsig, hE0, hE1⟩ := h.part hk
    obtain ⟨hn', t2', hsg', hsig', hE0', hE1'⟩ := h'.part hk
    have hT0 : (G.two 0).type = T₀ := h.2.2.2.2.2.2.1
    have hT1 : (G.two 1).type = T₁ := h.2.2.2.2.2.2.2.1
    have hT0' : (G'.two 0).type = T₀ := h'.2.2.2.2.2.2.1
    have hT1' : (G'.two 1).type = T₁ := h'.2.2.2.2.2.2.2.1
    have d1 : (G.two 1).dim = k := h.2.2.2.2.1
    have d1' : (G'.two 1).dim = k := h'.2.2.2.2.1
    have hty : ∀ j, (G'.two j).type = (G.two j).type := by
      intro j
      by_cases hj0 : j = 0
      · subst hj0; rw [hT0, hT0']
      by_cases hj1 : j = 1
      · subst hj1; rw [hT1, hT1']
      · have hj : 2 ≤ j := by omega
        rw [t2 j hj, t2' j hj]
    refine (moveEquiv_iff_sameInvariants (B := 2) (fun j hj => ?_)).2 ?_
    · simp [IsTypeI, t2 j hj, TwoFactor.trivial]
    · refine ⟨fun j => ?_, hty, fun j hj => ?_, fun y hy => ?_, fun c₁ c₂ hC => ?_⟩
      · by_cases hj0 : j = 0
        · subst hj0; omega
        by_cases hj1 : j = 1
        · subst hj1; rw [d1, d1']
        · have hj : 2 ≤ j := by omega
          rw [t2 j hj, t2' j hj]
      · have hII : (G.two j).type = .II := twoElem_toII hj
        have hII' : (G'.two j).type = .II := by rw [hty, hII]
        rw [(h'.1.two_exists j).oddity_of_typeII hII', (h.1.two_exists j).oddity_of_typeII hII]
      · have hy1 : (G.two y).type = .II := twoElem_toII hy.1
        have hy2 : (G.two (y + 1)).type = .II := twoElem_toII hy.2
        by_cases hy0 : y = 0
        · subst hy0
          have o0 := hE0.oddity_of_typeII hy1
          have o1 := hE1.oddity_of_typeII hy2
          have o0' := hE0'.oddity_of_typeII (by rw [hty]; exact hy1)
          have o1' := hE1'.oddity_of_typeII (by rw [hty]; exact hy2)
          rw [o0, o1, zero_add, zero_add] at hsig
          rw [o0', o1', zero_add, zero_add] at hsig'
          have e : ∀ σ : TwoSymbol, minusBelow σ (0 + 1) = if (σ 0).sign = .minus then 1 else 0 := fun σ => by
            simp [minusBelow]
          rw [e, e, hsg, hsg']
          exact twoElem_four_ind _ _ _ hsig' hsig
        · rw [twoElem_minusBelow G.two t2 (y + 1) (by omega), twoElem_minusBelow G'.two t2' (y + 1) (by omega),
            hsg, hsg', twoElem_four_ind2 _ _ rfl, twoElem_four_ind2 _ _ rfl]
      · have hC' : IsCompartment G'.two c₁ c₂ := by
          simpa only [IsCompartment, IsTypeI, hty] using hC
        rw [twoElem_compInv G'.two t2' hsg' hE0' hE1' _ hsig' hC', twoElem_compInv G.two t2 hsg hE0 hE1 _ hsig hC]

end QuadFormsKB.ConwaySloane
