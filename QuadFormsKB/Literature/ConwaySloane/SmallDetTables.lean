/-
# Conway–Sloane, Ch. 15, §8: Theorem 12 / Table 15.4 and Theorem 13 (a), at the level of symbols

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.1–8.2,
pp. 385–388 (`conwaysloane1999`; printed page = PDF page of the chapter file + 351).

As in `SmallDet.lean`, "the genus exists" means "there is a `GenusSymbolData` satisfying `Conditions`
((29)–(35) of §7.7) with the stated invariants"; the genera are told apart by the invariants that the book puts in
the genus symbol: the type of the 2-adic constituent of scale $1$ (I or II, the subscript of $\mathrm I_{r,s}$,
$\mathrm{II}_{r,s}$), the signs $e = \pm$ of the constituent $p^{ek}$, and the signature $r - s$.

**Theorem 13 (a), general odd prime $p$ and $k \ge 1$ (p-elementary: only the scales $1$ and $p$).**
* `thm13a_typeI`, `thm13a_typeII`: a system of symbols satisfying the conditions, with $\lvert\det\rvert = p^k$,
  $(-1)$-adic symbol $+^r-^s$, $p$-adic symbol $1^{\pm(n-k)}p^{ek}$, and 2-adic scale-1 type I (resp. II), exists iff
  `TypeIRhs` (resp. `TypeIIRhs`): $k \le n$; if $k = n$ then $e = \left(\frac{-1}{p}\right)^s$ (the book's "except that
  ... when $k = n$ the sign must be $\left(\frac{-1}{p}\right)^s$"); the 2-adic constituent $1_t^{\sigma n}$,
  $\sigma = \left(\frac{\det}{2}\right)$, $t \equiv r - s + k(p-1) + 4[e = -]$ satisfies (32)–(35) (type I); and for type
  II $r - s + k(p-1) + 4[e=-] \equiv 0 \pmod 8$, which is the book's $r - s \equiv \pm2 - 2 - (p-1)k$ (with $e = \pm$:
  $4[e=-] \equiv -(\pm2 - 2)$).
  The book's "$\mathrm I_{r,s}(p^{\pm k})$ for all signatures" lists the symbols; the small-$n$ exceptions of
  Table 15.4 are the failures of the 2-adic existence conditions, see below.

**Theorem 12 / Table 15.4 (rows $\lvert\det\rvert = 3, 5, 7, 11$, and the rows $3^{\pm2}$ of $\lvert\det\rvert = 9$)**:
the instances `table154_*` of the above, each with the signatures and the exceptions of the book, checked by `decide`
(type I) and `omega` (type II). A discrepancy with the printed table, if any, is stated in the docstring of the
instance. Covered: $\mathrm I_{r,s}(p^{\pm1})$, $\mathrm{II}_{r,s}(p^{\pm1})$ for $p = 3,5,7,11$ and
$\mathrm I_{r,s}(3^{\pm2})$, $\mathrm{II}_{r,s}(3^{\pm2})$.

**Not covered** (skipped): the rows whose symbols involve the prime $2$ in the determinant ($\lvert\det\rvert = 2, 4, 6,
8, 10$) or a scale $p^2$ ($\mathrm I_{r,s}(9^{\pm1})$, $\mathrm{II}_{r,s}(9^{\pm1})$), and $\lvert\det\rvert = 1$ (done in
`SmallDet.lean`): these need the equivalences of 2-adic symbols (sign walking, oddity fusion, `OddClassification`) or scale-$p^2$
bookkeeping, and the table lists *genera* (classes of symbols) there. Table 15.5 (2-elementary forms) is not done.
Passing from symbols to forms is Thm. 11 (not part of this file).
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDet

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### Definitions -/

/-- The integer $k(p-1) + 4[e = -]$: the $p$-excess of the $p$-adic symbol $1^{\pm(n-k)}p^{ek}$ (Conway–Sloane, §7.7,
p. 383: $\sum_q n_q(q-1) + 4k_p$ with the single antisquare term $p^{-k}$ when $e = -$). -/
def excI (p k : ℕ) (e : Sign) : ℤ := (k : ℤ) * ((p : ℤ) - 1) + (if e = .minus then 4 else 0)

/-- The sign $\left(\frac{-1}{p}\right)^s$ as a `Sign`. -/
def negSignAt (p s : ℕ) : Sign := if p % 4 = 3 ∧ Odd s then .minus else .plus

theorem ofInt_jacobi_negOne (p s : ℕ) (hp : p % 2 = 1) :
    Sign.ofInt (jacobiSym ((-1 : ℤ) ^ s) p) = negSignAt p s := by
  rcases Nat.even_or_odd s with h | h
  · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
    simp [h.neg_one_pow, negSignAt, this, Sign.ofInt]
  · have hj : jacobiSym (-1) p = ZMod.χ₄ (p : ZMod 4) := jacobiSym.at_neg_one (Nat.odd_iff.2 hp)
    rcases Nat.odd_mod_four_iff.1 hp with h1 | h1
    · rw [ZMod.χ₄_nat_one_mod_four h1] at hj
      simp [h.neg_one_pow, negSignAt, h1, hj, Sign.ofInt]
    · rw [ZMod.χ₄_nat_three_mod_four h1] at hj
      simp [h.neg_one_pow, negSignAt, h1, h, hj, Sign.ofInt]

/-- **The right-hand side for type I** (see the module docstring). -/
def TypeIRhs (p k r s : ℕ) (e : Sign) : Prop :=
  k ≤ r + s ∧ (r + s = k → e = negSignAt p s) ∧
    (⟨r + s, jacobiTwo ((p : ℤ) ^ k * (-1) ^ s), .I, (r : ZMod 8) - s + ((excI p k e : ℤ) : ZMod 8)⟩ :
      TwoFactor).Exists

/-- **The right-hand side for type II** (see the module docstring). -/
def TypeIIRhs (p k r s : ℕ) (e : Sign) : Prop :=
  k ≤ r + s ∧ (r + s = k → e = negSignAt p s) ∧ ((r : ℤ) - s + excI p k e) % 8 = 0

/-! ### Number-theoretic helpers -/

theorem natAbs_pk (p k s : ℕ) : ((p : ℤ) ^ k * (-1) ^ s).natAbs = p ^ k := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem padicValInt_pk (p k s : ℕ) (hp : p.Prime) : padicValInt p ((p : ℤ) ^ k * (-1) ^ s) = k := by
  haveI := Fact.mk hp
  simp [padicValInt, natAbs_pk]

theorem padicValInt_pk_ne (q p k s : ℕ) (hq : q.Prime) (hp : p.Prime) (hne : q ≠ p) :
    padicValInt q ((p : ℤ) ^ k * (-1) ^ s) = 0 := by
  have : ¬ q ∣ p ^ k := fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))
  simp [padicValInt, natAbs_pk, padicValNat.eq_zero_of_not_dvd this]

theorem pk_div (p k s : ℕ) (hp : p.Prime) : ((p : ℤ) ^ k * (-1) ^ s) / (p : ℤ) ^ k = (-1) ^ s := by
  have : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  exact Int.mul_ediv_cancel_left _ this

/-! ### The system of symbols -/

/-- **The system of symbols for the $p$-elementary genus** $p^{ek}$ (Conway–Sloane, §8.2, Thm. 13): determinant
$p^k(-1)^s$, $(-1)$-adic symbol $+^r-^s$, $p$-adic symbol $1^{\varepsilon(r+s-k)}p^{ek}$ ($\varepsilon$ forced by (29)),
$1^{\varepsilon(r+s)}$ at the other odd primes, and the 2-adic symbol $1^{\sigma(r+s)}$ of type `T`, oddity `t`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13, pp. 386–388"]
def dataPK (p k r s : ℕ) (e : Sign) (T : ScaledType) (t : ZMod 8) : GenusSymbolData where
  n := r + s
  det := (p : ℤ) ^ k * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q j =>
    if q = p then
      (if j = 0 then ⟨r + s - k, (Sign.ofInt (jacobiSym ((-1) ^ s) p)).mul e⟩
       else if j = 1 then ⟨k, e⟩ else OddFactor.trivial)
    else (if j = 0 then ⟨r + s, Sign.ofInt (jacobiSym ((p : ℤ) ^ k * (-1) ^ s) q)⟩ else OddFactor.trivial)
  two := fun j => if j = 0 then ⟨r + s, jacobiTwo ((p : ℤ) ^ k * (-1) ^ s), T, t⟩ else TwoFactor.trivial
  N := 2

theorem dataPK_conditions (p k r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (e : Sign) (T : ScaledType)
    (t : ZMod 8) (hn : k ≤ r + s)
    (hcompat : r + s = k → e = Sign.ofInt (jacobiSym ((-1) ^ s) p))
    (hE : (⟨r + s, jacobiTwo ((p : ℤ) ^ k * (-1) ^ s), T, t⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s + ((excI p k e : ℤ) : ZMod 8) = t) :
    (dataPK p k r s e T t).Conditions where
  ne_zero := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    have hpos : (0 : ℤ) < (p : ℤ) ^ k := by positivity [hp.pos]
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp only [dataPK, h.neg_one_pow, this, mul_one, iff_false, not_lt]
      exact hpos.le
    · simp only [dataPK, h.neg_one_pow, h, mul_neg, mul_one, iff_true]
      linarith
  odd_supp q j hj := by
    have hj' : 2 ≤ j := hj
    by_cases hq : q = p
    · simp [dataPK, hq, show j ≠ 0 by omega, show j ≠ 1 by omega]
    · simp [dataPK, hq, show j ≠ 0 by omega]
  two_supp j hj := by
    have hj' : 2 ≤ j := hj
    simp [dataPK, show j ≠ 0 by omega]
  odd_dim q _ _ := by
    by_cases hq : q = p
    · simp [dataPK, hq, Finset.sum_range_succ]
      omega
    · simp [dataPK, hq, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by simp [dataPK, Finset.sum_range_succ, TwoFactor.trivial]
  odd_det q hq hq2 := by
    by_cases h3 : q = p
    · subst h3
      refine ⟨?_, ?_⟩
      · simp [dataPK, padicValInt_pk q k s hq, Finset.sum_range_succ]
      · simp [dataPK, padicValInt_pk q k s hq, signProd, pk_div q k s hq, Sign.plus_mul, Sign.mul_mul_self]
    · refine ⟨?_, ?_⟩
      · simp [dataPK, h3, padicValInt_pk_ne q p k s hq hp h3, Finset.sum_range_succ, OddFactor.trivial]
      · simp [dataPK, h3, padicValInt_pk_ne q p k s hq hp h3, signProd, Sign.plus_mul, Sign.mul_plus,
          OddFactor.trivial]
  two_det := by
    have hv : padicValInt 2 ((p : ℤ) ^ k * (-1) ^ s) = 0 :=
      padicValInt_pk_ne 2 p k s Nat.prime_two hp (Ne.symm hp2)
    refine ⟨by simp [dataPK, hv, Finset.sum_range_succ, TwoFactor.trivial], ?_⟩
    simp [dataPK, hv, signProd, TwoFactor.trivial, Sign.plus_mul, Sign.mul_plus]
  odd_exists q hq hq2 j := by
    by_cases h3 : q = p
    · subst h3
      by_cases hj0 : j = 0
      · subst hj0
        simp only [dataPK, if_true]
        intro h0
        have h0' : r + s - k = 0 := h0
        rw [hcompat (by omega)]
        exact Sign.mul_self_eq _
      · by_cases hj1 : j = 1
        · subst hj1
          intro h0
          have h0' : k = 0 := by simpa [dataPK] using h0
          omega
        · simp [dataPK, hj0, hj1, OddFactor.Exists, OddFactor.trivial]
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [dataPK, h3, if_true, if_false]
        intro h0
        have h0' : r + s = 0 := h0
        omega
      · simp [dataPK, h3, hj0, OddFactor.Exists, OddFactor.trivial]
  two_exists j := by
    by_cases hj : j = 0
    · subst hj; simpa [dataPK] using hE
    · simp only [dataPK, if_neg hj]
      decide
  oddity_formula := by
    have hna : (dataPK p k r s e T t).det.natAbs = p ^ k := by
      simp [dataPK, natAbs_pk]
    rw [hna, Nat.primeFactors_prime_pow (by omega) hp, Finset.filter_singleton, if_pos hp2,
      Finset.sum_singleton]
    simp only [dataPK, if_true]
    unfold OddSymbol.pExcess TwoSymbol.oddity GenusSymbolData.signature
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [ind8, TwoFactor.trivial]
    rw [← ht]
    unfold excI
    cases e <;> simp <;> ring

/-- **The data forced by the conditions for a $p$-elementary genus** (Conway–Sloane, §8.2, Thm. 13): $k \le n$; the
$p$-adic symbol is $1^{\pm(n-k)}p^{ek}$; the 2-adic constituent of scale $1$ is $1_t^{\sigma n}$ with
$\sigma = \left(\frac{\det}{2}\right)$ and $t \equiv r - s + k(p-1) + 4[e = -]$; and for $k = n$ the sign is
$e = \left(\frac{-1}{p}\right)^s$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13(a), pp. 386–388"]
theorem GenusSymbolData.pk_part (G : GenusSymbolData) (hc : G.Conditions) (p k : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 1 ≤ k) (hd : G.det.natAbs = p ^ k) (hel : ∀ j, 2 ≤ j → (G.odd p j).dim = 0)
    {r s : ℕ} (hr : G.real = ⟨r, s⟩) :
    k ≤ r + s ∧
      G.two 0 = ⟨r + s, jacobiTwo ((p : ℤ) ^ k * (-1) ^ s), (G.two 0).type,
        (r : ZMod 8) - s + ((excI p k (G.odd p 1).sign : ℤ) : ZMod 8)⟩ ∧
      (G.two 0).Exists ∧ (r + s = k → (G.odd p 1).sign = negSignAt p s) := by
  have hn : G.n = r + s := by rw [← hc.real_dim, hr]
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  -- the determinant
  have hdet : G.det = (p : ℤ) ^ k * (-1) ^ s := by
    have h := hc.real_sign
    rw [hr] at h
    have h' : G.det < 0 ↔ Odd s := h
    have hP : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; rfl
    have hpos : (0 : ℤ) < (p : ℤ) ^ k := by positivity [hp.pos]
    have hcase : G.det = (p : ℤ) ^ k ∨ G.det = -((p : ℤ) ^ k) := by
      have := Int.natAbs_eq G.det
      rw [hd, hP] at this
      exact this
    rcases Nat.even_or_odd s with he | ho
    · have hnl : ¬ G.det < 0 := fun hl => (Nat.not_odd_iff_even.2 he) (h'.1 hl)
      rw [he.neg_one_pow, mul_one]
      rcases hcase with h1 | h1
      · exact h1
      · exfalso; apply hnl; rw [h1]; linarith
    · have hl : G.det < 0 := h'.2 ho
      rw [ho.neg_one_pow, mul_neg, mul_one]
      rcases hcase with h1 | h1
      · exfalso; rw [h1] at hl; linarith
      · exact h1
  have hv2 : padicValInt 2 G.det = 0 := by
    rw [hdet]; exact padicValInt_pk_ne 2 p k s Nat.prime_two hp (Ne.symm hp2)
  have hvp : padicValInt p G.det = k := by rw [hdet]; exact padicValInt_pk p k s hp
  obtain ⟨-, hdim2, hsign2, hoddeq, hE2⟩ := G.two_part hc hv2
  obtain ⟨hs3, hsg3⟩ := hc.odd_det p hp hp2
  rw [hvp] at hs3
  have hsupp := hc.odd_supp p
  have hex := hc.odd_exists p hp hp2
  have t3 : ∀ j, 2 ≤ j → G.odd p j = OddFactor.trivial := by
    intro j hj
    have h1 : (G.odd p j).dim = 0 := hel j hj
    have h2 : (G.odd p j).sign = .plus := hex j h1
    generalize G.odd p j = f at h1 h2
    obtain ⟨d, s'⟩ := f
    dsimp only at h1 h2
    subst h1 h2
    rfl
  have d1 : (G.odd p 1).dim = k := by
    have h : ∑ j ∈ range G.N, j * (G.odd p j).dim = 1 * (G.odd p 1).dim := by
      refine Finset.sum_eq_single 1 (fun j _ hj => ?_) (fun h1 => ?_)
      · rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · have : j = 0 := by omega
          simp [this]
        · simp [hel j hj2]
      · have : G.N ≤ 1 := by simpa using h1
        rw [hsupp 1 this]; simp [OddFactor.trivial]
    rw [h] at hs3
    omega
  have hN2 : 2 ≤ G.N := by
    by_contra h
    have h' : G.N ≤ 1 := by omega
    have := hsupp 1 h'
    rw [this] at d1
    simp [OddFactor.trivial] at d1
    omega
  have hdimsum : (G.odd p 0).dim + k = G.n := by
    have h := hc.odd_dim p hp hp2
    rw [sum_range_stable_nat (f := fun j => (G.odd p j).dim) (m := 2) (fun j hj => hel j hj)
      (fun j hj => by rw [hsupp j hj]; rfl)] at h
    simpa [Finset.sum_range_succ, d1] using h
  have hexc : (G.odd p).pExcess p G.N = ((excI p k (G.odd p 1).sign : ℤ) : ZMod 8) := by
    rw [OddSymbol.pExcess_congr p (σ := G.odd p) (N := 2) t3 hN2]
    unfold OddSymbol.pExcess
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d1]
    unfold excI
    cases (G.odd p 1).sign <;> simp [ind8]
  refine ⟨by omega, ?_, hE2, ?_⟩
  · have h := hc.oddity_formula
    rw [hd, Nat.primeFactors_prime_pow (by omega) hp, Finset.filter_singleton, if_pos hp2,
      Finset.sum_singleton, hexc] at h
    have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by
      simp [GenusSymbolData.signature, hr]
    rw [hsig] at h
    have hodd : (G.two 0).oddity = (r : ZMod 8) - s + ((excI p k (G.odd p 1).sign : ℤ) : ZMod 8) := by
      rw [← hoddeq, ← h]
    generalize G.two 0 = f at hdim2 hsign2 hodd hE2 ⊢
    obtain ⟨d, sg, ty, o⟩ := f
    dsimp only at hdim2 hsign2 hodd ⊢
    rw [hdet] at hsign2
    subst hodd
    rw [hdim2, hn, hsign2]
  · intro hnk
    have h0 : (G.odd p 0).dim = 0 := by omega
    have hs0 : (G.odd p 0).sign = .plus := hex 0 h0
    rw [signProd_stable (fun j => (G.odd p j).sign) hN2
      (fun j hj => by simp [t3 j hj, OddFactor.trivial]), hvp, hdet, pk_div p k s hp,
      ofInt_jacobi_negOne p s hpodd] at hsg3
    simpa [signProd, hs0, Sign.plus_mul] using hsg3

theorem excI_even (p k : ℕ) (e : Sign) (hp : p % 2 = 1) : excI p k e % 2 = 0 := by
  have h : Even ((p : ℤ) - 1) := by rw [Int.even_iff]; omega
  have h2 : Even ((k : ℤ) * ((p : ℤ) - 1)) := h.mul_left _
  unfold excI
  rcases h2 with ⟨m, hm⟩
  cases e <;> simp <;> omega

theorem typeI_ge3 (σ : Sign) (c : ℤ) (hc : c % 2 = 0) (r s : ℕ) (h : 3 ≤ r + s) :
    (⟨r + s, σ, .I, (r : ZMod 8) - s + (c : ZMod 8)⟩ : TwoFactor).Exists := by
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 _ => ?_, ?_, fun h => nomatch h⟩
  · have h0' : r + s = 0 := h0
    omega
  · have h1' : r + s = 1 := h1
    omega
  · have h2' : r + s = 2 := h2
    omega
  · exact val_sub_add_mod_two r s c hc

/-- **Theorem 13 (a), type I** (Conway–Sloane, §8.2, pp. 386–388): the genus $\mathrm I_{r,s}(p^{ek})$ of
$p$-elementary forms ($p$ odd, $k \ge 1$, only the scales $1$ and $p$) exists iff `TypeIRhs p k r s e`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13(a), pp. 386–388 (I_{r,s}(p^{±k}))"]
theorem thm13a_typeI (p k r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (e : Sign) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = p ^ k ∧ (G.two 0).type = .I ∧
        (G.odd p 1).sign = e ∧ ∀ j, 2 ≤ j → (G.odd p j).dim = 0) ↔ TypeIRhs p k r s e := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  constructor
  · rintro ⟨G, hc, hr, hd, hT, he, hel⟩
    obtain ⟨h1, h2, h3, h4⟩ := G.pk_part hc p k hp hp2 hk hd hel hr
    rw [he, hT] at h2
    rw [he] at h4
    refine ⟨h1, h4, ?_⟩
    rw [h2] at h3
    simpa [hT] using h3
  · rintro ⟨h1, hcompat, hE⟩
    refine ⟨dataPK p k r s e .I _, dataPK_conditions p k r s hp hp2 hk e .I _ h1 ?_ hE rfl, rfl, ?_,
      by simp [dataPK], by simp [dataPK], ?_⟩
    · intro h; rw [ofInt_jacobi_negOne p s hpodd]; exact hcompat h
    · simp [dataPK, natAbs_pk]
    · intro j hj
      have : j ≠ 0 := by omega
      have : j ≠ 1 := by omega
      simp [dataPK, *, OddFactor.trivial]

/-- **Theorem 13 (a), type II** (Conway–Sloane, §8.2, pp. 386–388): the genus $\mathrm{II}_{r,s}(p^{ek})$ exists iff
`TypeIIRhs p k r s e`, i.e. $r - s + k(p-1) + 4[e=-] \equiv 0 \pmod 8$ (the book's
$r - s \equiv \pm2 - 2 - (p-1)k$) and the conditions $k \le n$, $k = n \Rightarrow e = \left(\frac{-1}{p}\right)^s$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13(a), pp. 386–388 (II_{r,s}(p^{±k}))"]
theorem thm13a_typeII (p k r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (e : Sign) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = p ^ k ∧ (G.two 0).type = .II ∧
        (G.odd p 1).sign = e ∧ ∀ j, 2 ≤ j → (G.odd p j).dim = 0) ↔ TypeIIRhs p k r s e := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have hev := excI_even p k e hpodd
  constructor
  · rintro ⟨G, hc, hr, hd, hT, he, hel⟩
    obtain ⟨h1, h2, h3, h4⟩ := G.pk_part hc p k hp hp2 hk hd hel hr
    rw [he] at h4 h2
    refine ⟨h1, h4, ?_⟩
    have := h3.2.2.2.2 hT
    rw [h2] at this
    have h5 : (r : ZMod 8) - s + ((excI p k e : ℤ) : ZMod 8) = 0 := this
    have h6 : (((r : ℤ) - s + excI p k e : ℤ) : ZMod 8) = 0 := by push_cast; exact h5
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h6
    omega
  · rintro ⟨h1, hcompat, hsig⟩
    have hpar : (r + s) % 2 = 0 := by omega
    refine ⟨dataPK p k r s e .II 0, dataPK_conditions p k r s hp hp2 hk e .II 0 h1 ?_ ?_ ?_, rfl, ?_,
      by simp [dataPK], by simp [dataPK], ?_⟩
    · intro h; rw [ofInt_jacobi_negOne p s hpodd]; exact hcompat h
    · refine ⟨fun h0 => ?_, fun h1' => ?_, (fun _ hI => by cases hI), ?_, fun _ => rfl⟩
      · have h0' : r + s = 0 := h0
        omega
      · have h1'' : r + s = 1 := h1'
        exfalso
        omega
      · show (0 : ZMod 8).val % 2 = (r + s) % 2
        simp
        omega
    · have h6 : (((r : ℤ) - s + excI p k e : ℤ) : ZMod 8) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
      push_cast at h6
      exact h6
    · simp [dataPK, natAbs_pk]
    · intro j hj
      have : j ≠ 0 := by omega
      have : j ≠ 1 := by omega
      simp [dataPK, *, OddFactor.trivial]

set_option synthInstance.maxSize 1024 in
instance (p k r s : ℕ) (e : Sign) : Decidable (TypeIRhs p k r s e) := by
  unfold TypeIRhs; infer_instance

instance (p k r s : ℕ) (e : Sign) : Decidable (TypeIIRhs p k r s e) := by
  unfold TypeIIRhs; infer_instance

theorem typeIRhs_iff_of (p k : ℕ) (e : Sign) (hp1 : p % 2 = 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (F : ℕ → ℕ → Prop)
    (hsmall : ∀ r, r ≤ 2 → ∀ s, s ≤ 2 → r + s < 3 → (TypeIRhs p k r s e ↔ ¬ F r s))
    (hbig : ∀ r s, 3 ≤ r + s → ¬ F r s) (r s : ℕ) : TypeIRhs p k r s e ↔ ¬ F r s := by
  by_cases h : 3 ≤ r + s
  · simp only [hbig r s h, not_false_eq_true, iff_true]
    exact ⟨by omega, fun hn => by omega, typeI_ge3 _ _ (excI_even p k e hp1) r s h⟩
  · exact hsmall r (by omega) s (by omega) (by omega)

/-! ### Table 15.4: the rows $\lvert\det\rvert = 3, 5, 7, 11$ and $3^{\pm2}$ -/

/-- **Table 15.4, $\pm3$, $\mathrm I_{r,s}(3)$:** all signatures, exceptions $0$, $1_{-1}$, $2_{-2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±3, I(3))"]
theorem table154_three_typeI_plus (r s : ℕ) :
    TypeIRhs 3 1 r s .plus ↔ ¬ (r = 0 ∧ s ≤ 2) :=
  typeIRhs_iff_of 3 1 .plus (by norm_num) le_rfl (by norm_num) (fun r s => r = 0 ∧ s ≤ 2)
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm3$, $\mathrm I_{r,s}(3^{-1})$:** exceptions $0$, $1_{+1}$, $2_{+2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±3, I(3^{-1}))"]
theorem table154_three_typeI_minus (r s : ℕ) :
    TypeIRhs 3 1 r s .minus ↔ ¬ (s = 0 ∧ r ≤ 2) :=
  typeIRhs_iff_of 3 1 .minus (by norm_num) le_rfl (by norm_num) (fun r s => s = 0 ∧ r ≤ 2)
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm5$, $\mathrm I_{r,s}(5)$:** all signatures, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±5, I(5))"]
theorem table154_five_typeI_plus (r s : ℕ) :
    TypeIRhs 5 1 r s .plus ↔ ¬ (r = 0 ∧ s = 0) :=
  typeIRhs_iff_of 5 1 .plus (by norm_num) le_rfl (by norm_num) (fun r s => r = 0 ∧ s = 0)
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm5$, $\mathrm I_{r,s}(5^{-1})$:** exceptions $0$, $1$, $2_0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±5, I(5^{-1}))"]
theorem table154_five_typeI_minus (r s : ℕ) :
    TypeIRhs 5 1 r s .minus ↔ ¬ (r + s ≤ 1 ∨ (r = 1 ∧ s = 1)) :=
  typeIRhs_iff_of 5 1 .minus (by norm_num) le_rfl (by norm_num) (fun r s => r + s ≤ 1 ∨ (r = 1 ∧ s = 1))
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm7$, $\mathrm I_{r,s}(7)$:** exceptions $0$, $1_{-1}$, $2_{-2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±7, I(7))"]
theorem table154_seven_typeI_plus (r s : ℕ) :
    TypeIRhs 7 1 r s .plus ↔ ¬ (r = 0 ∧ s ≤ 2) :=
  typeIRhs_iff_of 7 1 .plus (by norm_num) le_rfl (by norm_num) (fun r s => r = 0 ∧ s ≤ 2)
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm7$, $\mathrm I_{r,s}(7^{-1})$:** exceptions $0$, $1_{+1}$, $2_{+2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±7, I(7^{-1}))"]
theorem table154_seven_typeI_minus (r s : ℕ) :
    TypeIRhs 7 1 r s .minus ↔ ¬ (s = 0 ∧ r ≤ 2) :=
  typeIRhs_iff_of 7 1 .minus (by norm_num) le_rfl (by norm_num) (fun r s => s = 0 ∧ r ≤ 2)
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm11$, $\mathrm I_{r,s}(11)$:** exceptions $0$, $1_{-1}$, $2_{-2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±11, I(11))"]
theorem table154_eleven_typeI_plus (r s : ℕ) :
    TypeIRhs 11 1 r s .plus ↔ ¬ (r = 0 ∧ s ≤ 2) :=
  typeIRhs_iff_of 11 1 .plus (by norm_num) le_rfl (by norm_num) (fun r s => r = 0 ∧ s ≤ 2)
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm11$, $\mathrm I_{r,s}(11^{-1})$:** exceptions $0$, $1_{+1}$, $2_{+2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±11, I(11^{-1}))"]
theorem table154_eleven_typeI_minus (r s : ℕ) :
    TypeIRhs 11 1 r s .minus ↔ ¬ (s = 0 ∧ r ≤ 2) :=
  typeIRhs_iff_of 11 1 .minus (by norm_num) le_rfl (by norm_num) (fun r s => s = 0 ∧ r ≤ 2)
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm9$, $\mathrm I_{r,s}(3^2)$:** exceptions $0$, $1$, $2_0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, I(3^2))"]
theorem table154_threeSq_typeI_plus (r s : ℕ) :
    TypeIRhs 3 2 r s .plus ↔ ¬ (r + s ≤ 1 ∨ (r = 1 ∧ s = 1)) :=
  typeIRhs_iff_of 3 2 .plus (by norm_num) (by norm_num) le_rfl (fun r s => r + s ≤ 1 ∨ (r = 1 ∧ s = 1))
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm9$, $\mathrm I_{r,s}(3^{-2})$:** exceptions $0$, $1$, $2_{\pm2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, I(3^{-2}))"]
theorem table154_threeSq_typeI_minus (r s : ℕ) :
    TypeIRhs 3 2 r s .minus ↔ ¬ (r + s ≤ 1 ∨ (r = 2 ∧ s = 0) ∨ (r = 0 ∧ s = 2)) :=
  typeIRhs_iff_of 3 2 .minus (by norm_num) (by norm_num) le_rfl
    (fun r s => r + s ≤ 1 ∨ (r = 2 ∧ s = 0) ∨ (r = 0 ∧ s = 2))
    (by beta_reduce; decide) (fun r s h => by omega) r s

/-- **Table 15.4, $\pm3$, $\mathrm{II}_{r,s}(3)$:** signature $-2$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±3, II(3))"]
theorem table154_three_typeII_plus (r s : ℕ) : TypeIIRhs 3 1 r s .plus ↔ ((r : ℤ) - s) % 8 = 6 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm3$, $\mathrm{II}_{r,s}(3^{-1})$:** signature $+2$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±3, II(3^{-1}))"]
theorem table154_three_typeII_minus (r s : ℕ) : TypeIIRhs 3 1 r s .minus ↔ ((r : ℤ) - s) % 8 = 2 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm5$, $\mathrm{II}_{r,s}(5)$:** signature $4$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±5, II(5))"]
theorem table154_five_typeII_plus (r s : ℕ) : TypeIIRhs 5 1 r s .plus ↔ ((r : ℤ) - s) % 8 = 4 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm5$, $\mathrm{II}_{r,s}(5^{-1})$:** signature $0$, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±5, II(5^{-1}))"]
theorem table154_five_typeII_minus (r s : ℕ) :
    TypeIIRhs 5 1 r s .minus ↔ ((r : ℤ) - s) % 8 = 0 ∧ r + s ≠ 0 := by
  constructor
  · rintro ⟨h1, -, h⟩
    simp [excI] at h
    omega
  · rintro ⟨h, hn⟩
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm7$, $\mathrm{II}_{r,s}(7)$:** signature $+2$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±7, II(7))"]
theorem table154_seven_typeII_plus (r s : ℕ) : TypeIIRhs 7 1 r s .plus ↔ ((r : ℤ) - s) % 8 = 2 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm7$, $\mathrm{II}_{r,s}(7^{-1})$:** signature $-2$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±7, II(7^{-1}))"]
theorem table154_seven_typeII_minus (r s : ℕ) : TypeIIRhs 7 1 r s .minus ↔ ((r : ℤ) - s) % 8 = 6 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm11$, $\mathrm{II}_{r,s}(11)$:** signature $-2$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±11, II(11))"]
theorem table154_eleven_typeII_plus (r s : ℕ) : TypeIIRhs 11 1 r s .plus ↔ ((r : ℤ) - s) % 8 = 6 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm11$, $\mathrm{II}_{r,s}(11^{-1})$:** signature $+2$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±11, II(11^{-1}))"]
theorem table154_eleven_typeII_minus (r s : ℕ) : TypeIIRhs 11 1 r s .minus ↔ ((r : ℤ) - s) % 8 = 2 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm9$, $\mathrm{II}_{r,s}(3^2)$:** signature $4$, no exceptions. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, II(3^2))"]
theorem table154_threeSq_typeII_plus (r s : ℕ) : TypeIIRhs 3 2 r s .plus ↔ ((r : ℤ) - s) % 8 = 4 := by
  constructor
  · rintro ⟨-, -, h⟩
    simp [excI] at h
    omega
  · intro h
    refine ⟨by omega, fun hn => by exfalso; omega, ?_⟩
    simp [excI]
    omega

/-- **Table 15.4, $\pm9$, $\mathrm{II}_{r,s}(3^{-2})$:** signature $0$, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, II(3^{-2}))"]
theorem table154_threeSq_typeII_minus (r s : ℕ) :
    TypeIIRhs 3 2 r s .minus ↔ ((r : ℤ) - s) % 8 = 0 ∧ r + s ≠ 0 := by
  constructor
  · rintro ⟨h1, -, h⟩
    simp [excI] at h
    omega
  · rintro ⟨h, hn⟩
    refine ⟨by omega, fun hn2 => ?_, ?_⟩
    · have hs : s = 1 := by omega
      have hr : r = 1 := by omega
      subst hs hr
      decide
    · simp [excI]
      omega

end QuadFormsKB.ConwaySloane
