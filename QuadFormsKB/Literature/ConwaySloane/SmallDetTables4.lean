/-
# Conway–Sloane, Ch. 15, §8.1: Table 15.4, the rows $\mathrm I_{r,s}(9^{\pm1})$, $\mathrm{II}_{r,s}(9^{\pm1})$

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.1,
Theorem 12, Table 15.4 (p. 387) (`conwaysloane1999`).

For an odd prime $p$: determinant $\pm p^2$ with the $p$-adic symbol $1^{\varepsilon(n-1)}(p^2)^{e1}$ (a single
constituent of dimension $1$ at the scale $p^2$ and nothing at the scale $p$). The scale $p^2$ is a square, so there is
no antisquare term and the $p$-excess is $p^2 - 1 \equiv 0 \pmod 8$; the 2-adic symbol is $1_t^{+n}$ (type I) or
$1^{+n}$ (type II) with $t \equiv r - s$.

**Covered rows.** $\mathrm I_{r,s}(9^{\pm1})$ and $\mathrm{II}_{r,s}(9^{\pm1})$ ($p = 3$): existence
(`table154_nine_*`: `rhs9`, `thm_p2_exists`) and uniqueness of the genus (`thm_p2_unique`, equality of all symbols,
no moves needed since only the scale $1$ occurs at $2$).
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables3

namespace QuadFormsKB.ConwaySloane

open Finset

theorem sq_odd_zmod8 (p : ℕ) (hp : p % 2 = 1) : (p : ZMod 8) ^ 2 = 1 := by
  have h : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by simp [ZMod.natCast_mod]
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rw [h]
  rcases h8 with h | h | h | h <;> rw [h] <;> decide

theorem sq_odd_int8 (p : ℕ) (hp : p % 2 = 1) : ((p : ℤ) ^ 2) % 8 = 1 := by
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h | h | h | h <;> simp [pow_two, Int.mul_emod, show (p : ℤ) % 8 = (p % 8 : ℕ) by omega, h]

theorem jacobiTwo_sq (p s : ℕ) (hp : p % 2 = 1) : jacobiTwo ((p : ℤ) ^ 2 * (-1) ^ s) = .plus := by
  have h := sq_odd_int8 p hp
  rcases Nat.even_or_odd s with he | ho
  · simp only [he.neg_one_pow, mul_one, jacobiTwo]; rw [if_pos (Or.inl h)]
  · simp only [ho.neg_one_pow, mul_neg, mul_one, jacobiTwo]
    rw [if_pos (Or.inr (by omega))]

theorem natAbs_sq (p s : ℕ) : ((p : ℤ) ^ 2 * (-1) ^ s).natAbs = p ^ 2 := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem padicValInt_sq (p s : ℕ) (hp : p.Prime) : padicValInt p ((p : ℤ) ^ 2 * (-1) ^ s) = 2 := by
  haveI := Fact.mk hp
  simp [padicValInt, natAbs_sq]

theorem padicValInt_sq_ne (q p s : ℕ) (hq : q.Prime) (hp : p.Prime) (hne : q ≠ p) :
    padicValInt q ((p : ℤ) ^ 2 * (-1) ^ s) = 0 := by
  have : ¬ q ∣ p ^ 2 := fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))
  simp [padicValInt, natAbs_sq, padicValNat.eq_zero_of_not_dvd this]

theorem sq_div (p s : ℕ) (hp : p.Prime) : ((p : ℤ) ^ 2 * (-1) ^ s) / (p : ℤ) ^ 2 = (-1) ^ s := by
  have : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  exact Int.mul_ediv_cancel_left _ this

/-- **The data forced by the conditions for the scale $p^2$** (Conway–Sloane, §8.1, Table 15.4, rows $\pm9$):
if $v_p(\det) = 2$ and there is nothing at the scale $p$, then the $p$-adic symbol is $1^{\pm(n-1)}(p^2)^{e1}$,
the sign product is $\left(\frac{\det/p^2}{p}\right)$ and the $p$-excess is $p^2 - 1$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±9, scale 9)"]
theorem GenusSymbolData.p2_shape (G : GenusSymbolData) (hc : G.Conditions) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hvp : padicValInt p G.det = 2) (h1 : (G.odd p 1).dim = 0) :
    (G.odd p 0).dim + 1 = G.n ∧ (G.odd p 2).dim = 1 ∧ (∀ k, 3 ≤ k → G.odd p k = OddFactor.trivial) ∧
      G.odd p 1 = OddFactor.trivial ∧
      (G.odd p 0).sign.mul (G.odd p 2).sign = Sign.ofInt (jacobiSym (G.det / (p : ℤ) ^ 2) p) ∧
      (G.odd p).pExcess p G.N = (p : ZMod 8) ^ 2 - 1 ∧ (G.odd p 0).Exists := by
  obtain ⟨hs, hsg⟩ := hc.odd_det p hp hp2
  rw [hvp] at hs
  have hsupp := hc.odd_supp p
  have hex := hc.odd_exists p hp hp2
  have d3 : ∀ k, 3 ≤ k → (G.odd p k).dim = 0 := by
    intro k hk
    by_cases hkN : k < G.N
    · have hle : k * (G.odd p k).dim ≤ ∑ k ∈ range G.N, k * (G.odd p k).dim :=
        Finset.single_le_sum (f := fun k => k * (G.odd p k).dim) (fun i _ => Nat.zero_le _) (mem_range.2 hkN)
      rw [hs] at hle
      by_contra hne
      have h1' : 1 ≤ (G.odd p k).dim := Nat.pos_of_ne_zero hne
      have := Nat.mul_le_mul hk h1'
      omega
    · rw [hsupp k (not_lt.1 hkN)]; rfl
  have triv : ∀ k, (G.odd p k).dim = 0 → G.odd p k = OddFactor.trivial := by
    intro k hk
    have h2 : (G.odd p k).sign = .plus := hex k hk
    generalize G.odd p k = f at hk h2
    obtain ⟨d, s⟩ := f
    dsimp only at hk h2
    subst hk h2
    rfl
  have t3 : ∀ k, 3 ≤ k → G.odd p k = OddFactor.trivial := fun k hk => triv k (d3 k hk)
  have t1 : G.odd p 1 = OddFactor.trivial := triv 1 h1
  have d2 : (G.odd p 2).dim = 1 := by
    have h : ∑ k ∈ range G.N, k * (G.odd p k).dim = 2 * (G.odd p 2).dim := by
      refine Finset.sum_eq_single 2 (fun k _ hk => ?_) (fun h2 => ?_)
      · rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · have : k = 0 ∨ k = 1 := by omega
          rcases this with rfl | rfl
          · simp
          · simp [h1]
        · simp [d3 k hk3]
      · have : G.N ≤ 2 := by simpa using h2
        rw [hsupp 2 this]; simp [OddFactor.trivial]
    rw [h] at hs
    omega
  have hN3 : 3 ≤ G.N := by
    by_contra h
    have h' : G.N ≤ 2 := by omega
    have := hsupp 2 h'
    rw [this] at d2
    simp [OddFactor.trivial] at d2
  have hdimsum : (G.odd p 0).dim + 1 = G.n := by
    have h := hc.odd_dim p hp hp2
    rw [sum_range_stable_nat (f := fun k => (G.odd p k).dim) (m := 3) (fun k hk => d3 k hk)
      (fun k hk => by rw [hsupp k hk]; rfl)] at h
    simpa [Finset.sum_range_succ, d2, h1] using h
  refine ⟨hdimsum, d2, t3, t1, ?_, ?_, hex 0⟩
  · rw [signProd_stable (fun k => (G.odd p k).sign) hN3
      (fun k hk => by simp [t3 k hk, OddFactor.trivial]), hvp] at hsg
    simpa [signProd, Sign.plus_mul, t1, OddFactor.trivial, Sign.mul_plus] using hsg
  · rw [OddSymbol.pExcess_congr p (σ := G.odd p) (N := 3) t3 hN3]
    unfold OddSymbol.pExcess
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d2, h1]
    have h2odd : ¬ Odd 2 := by decide
    simp [ind8, t1, OddFactor.trivial, h2odd]

/-- **The system of symbols for $\mathrm I/\mathrm{II}_{r,s}((p^2)^{e})$**: determinant $p^2(-1)^s$, $p$-adic symbol
$1^{\varepsilon(n-1)}(p^2)^{e1}$, 2-adic symbol $1_t^{+n}$ of type `T`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±9, scale 9)"]
def dataP2 (p r s : ℕ) (e : Sign) (T : ScaledType) (t : ZMod 8) : GenusSymbolData where
  n := r + s
  det := (p : ℤ) ^ 2 * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun q j =>
    if q = p then
      (if j = 0 then ⟨r + s - 1, (Sign.ofInt (jacobiSym ((-1) ^ s) p)).mul e⟩
       else if j = 2 then ⟨1, e⟩ else OddFactor.trivial)
    else (if j = 0 then ⟨r + s, Sign.ofInt (jacobiSym ((p : ℤ) ^ 2 * (-1) ^ s) q)⟩ else OddFactor.trivial)
  two := fun j => if j = 0 then ⟨r + s, .plus, T, t⟩ else TwoFactor.trivial
  N := 3

theorem dataP2_conditions (p r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (e : Sign) (T : ScaledType) (t : ZMod 8)
    (hn : 1 ≤ r + s) (hcompat : r + s = 1 → e = Sign.ofInt (jacobiSym ((-1) ^ s) p))
    (hE : (⟨r + s, .plus, T, t⟩ : TwoFactor).Exists) (ht : (r : ZMod 8) - s = t) :
    (dataP2 p r s e T t).Conditions where
  ne_zero := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    have hpos : (0 : ℤ) < (p : ℤ) ^ 2 := by have := hp.pos; positivity
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp only [dataP2, h.neg_one_pow, this, mul_one, iff_false, not_lt]
      exact hpos.le
    · simp only [dataP2, h.neg_one_pow, h, mul_neg, mul_one, iff_true]
      linarith
  odd_supp q j hj := by
    have hj' : 3 ≤ j := hj
    by_cases hq : q = p
    · simp [dataP2, hq, show j ≠ 0 by omega, show j ≠ 2 by omega]
    · simp [dataP2, hq, show j ≠ 0 by omega]
  two_supp j hj := by
    have hj' : 3 ≤ j := hj
    simp [dataP2, show j ≠ 0 by omega]
  odd_dim q _ _ := by
    by_cases hq : q = p
    · simp [dataP2, hq, Finset.sum_range_succ, OddFactor.trivial]
      omega
    · simp [dataP2, hq, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by simp [dataP2, Finset.sum_range_succ, TwoFactor.trivial]
  odd_det q hq hq2 := by
    by_cases h3 : q = p
    · subst h3
      refine ⟨?_, ?_⟩
      · simp [dataP2, padicValInt_sq q s hq, Finset.sum_range_succ, OddFactor.trivial]
      · simp [dataP2, padicValInt_sq q s hq, signProd, sq_div q s hq, Sign.plus_mul, Sign.mul_plus,
          Sign.mul_mul_self, OddFactor.trivial]
    · refine ⟨?_, ?_⟩
      · simp [dataP2, h3, padicValInt_sq_ne q p s hq hp h3, Finset.sum_range_succ, OddFactor.trivial]
      · simp [dataP2, h3, padicValInt_sq_ne q p s hq hp h3, signProd, Sign.plus_mul, Sign.mul_plus,
          OddFactor.trivial]
  two_det := by
    have hv := padicValInt_sq_ne 2 p s Nat.prime_two hp (Ne.symm hp2)
    refine ⟨by simp [dataP2, hv, Finset.sum_range_succ, TwoFactor.trivial], ?_⟩
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
    simp [dataP2, hv, signProd, jacobiTwo_sq p s hpodd, Sign.plus_mul, Sign.mul_plus, TwoFactor.trivial]
  odd_exists q hq hq2 j := by
    by_cases h3 : q = p
    · subst h3
      by_cases hj0 : j = 0
      · subst hj0
        simp only [dataP2, if_true]
        intro h0
        have h0' : r + s - 1 = 0 := h0
        rw [hcompat (by omega)]
        exact Sign.mul_self_eq _
      · by_cases hj2 : j = 2
        · subst hj2
          intro h0
          have : (1 : ℕ) = 0 := by simpa [dataP2] using h0
          omega
        · simp [dataP2, hj0, hj2, OddFactor.Exists, OddFactor.trivial]
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [dataP2, h3, if_true, if_false]
        intro h0
        have h0' : r + s = 0 := h0
        omega
      · simp [dataP2, h3, hj0, OddFactor.Exists, OddFactor.trivial]
  two_exists j := by
    by_cases hj : j = 0
    · subst hj; simpa [dataP2] using hE
    · simp only [dataP2, if_neg hj]
      decide
  oddity_formula := by
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
    have hna : (dataP2 p r s e T t).det.natAbs = p ^ 2 := by simp [dataP2, natAbs_sq]
    rw [hna, Nat.primeFactors_prime_pow (by norm_num) hp, Finset.filter_singleton, if_pos hp2,
      Finset.sum_singleton]
    simp only [dataP2, if_true]
    unfold OddSymbol.pExcess TwoSymbol.oddity GenusSymbolData.signature
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have h2odd : ¬ Odd 2 := by decide
    simp [ind8, TwoFactor.trivial, OddFactor.trivial, h2odd, sq_odd_zmod8 p hpodd]
    exact ht

/-- **Existence for the scale $p^2$** (Conway–Sloane, §8.1, Table 15.4, rows $\pm9$, $p = 3$): the genus
$\mathrm I_{r,s}((p^2)^{e})$ / $\mathrm{II}_{r,s}((p^2)^{e})$ (nothing at the scale $p$) exists iff $n \ge 1$, for $n = 1$
the sign is $e = \left(\frac{-1}{p}\right)^s$, and the 2-adic constituent $1_t^{+n}$ with $t \equiv r - s$ (and $t = 0$ for
type II) satisfies (32)–(35). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±9, scale 9)"]
theorem thm_p2_exists (p r s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (e : Sign) (T : ScaledType) (t : ZMod 8) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = p ^ 2 ∧ (G.two 0).type = T ∧
        (G.two 0).oddity = t ∧ (G.odd p 2).sign = e ∧ (G.odd p 1).dim = 0) ↔
      (1 ≤ r + s ∧ (r + s = 1 → e = negSignAt p s) ∧ (⟨r + s, .plus, T, t⟩ : TwoFactor).Exists ∧
        (r : ZMod 8) - s = t) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  constructor
  · rintro ⟨G, hc, hr, hd, hT, ho, he, h1⟩
    have hn : G.n = r + s := by rw [← hc.real_dim, hr]
    have hdet : G.det = (p : ℤ) ^ 2 * (-1) ^ s := by
      have := G.det_eq_of hc (m := p ^ 2) (by have := hp.pos; positivity) hd hr
      rw [this]; push_cast; ring
    have hvp : padicValInt p G.det = 2 := by rw [hdet]; exact padicValInt_sq p s hp
    have hv2 : padicValInt 2 G.det = 0 := by
      rw [hdet]; exact padicValInt_sq_ne 2 p s Nat.prime_two hp (Ne.symm hp2)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := G.p2_shape hc p hp hp2 hvp h1
    obtain ⟨-, hdim, hsg, hoddeq, hE⟩ := G.two_part hc hv2
    have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
    refine ⟨by omega, fun hn1 => ?_, ?_, ?_⟩
    · have h0 : (G.odd p 0).dim = 0 := by omega
      have hs0 : (G.odd p 0).sign = .plus := b7 h0
      rw [hs0, Sign.plus_mul, he, hdet, sq_div p s hp, ofInt_jacobi_negOne p s hpodd] at b5
      exact b5
    · have : (G.two 0) = ⟨r + s, .plus, T, t⟩ := by
        have hs : (G.two 0).sign = jacobiTwo G.det := hsg
        rw [hdet, jacobiTwo_sq p s hpodd] at hs
        generalize G.two 0 = f at hdim hs hT ho
        obtain ⟨d, sg, ty, o⟩ := f
        dsimp only at hdim hs hT ho
        subst hs hT ho
        rw [hdim, hn]
      rw [← this]; exact hE
    · have h := hc.oddity_formula
      rw [hd, Nat.primeFactors_prime_pow (by norm_num) hp, Finset.filter_singleton, if_pos hp2,
        Finset.sum_singleton, b6, sq_odd_zmod8 p hpodd, sub_self, add_zero, hoddeq, ho, hsig] at h
      exact h
  · rintro ⟨hn, hcompat, hE, ht⟩
    refine ⟨dataP2 p r s e T t, dataP2_conditions p r s hp hp2 e T t hn ?_ hE ht, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; rw [ofInt_jacobi_negOne p s hpodd]; exact hcompat h
    · simp [dataP2, natAbs_sq]
    · simp [dataP2]
    · simp [dataP2]
    · simp [dataP2]
    · simp [dataP2, OddFactor.trivial]

/-- **The symbols are determined by the invariants** (scale $p^2$): the 2-adic symbol is
$1_{r-s}^{+n}$ (of the given type) and the $p$-adic symbol is $1^{\pm(n-1)}(p^2)^{e1}$. -/
theorem GenusSymbolData.p2_data (G : GenusSymbolData) (hc : G.Conditions) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {r s : ℕ} (hd : G.det.natAbs = p ^ 2) (hr : G.real = ⟨r, s⟩) (h1 : (G.odd p 1).dim = 0) :
    (∀ k, G.two k = if k = 0 then ⟨r + s, .plus, (G.two 0).type, (r : ZMod 8) - s⟩ else TwoFactor.trivial) ∧
    (∀ k, G.odd p k = if k = 0 then ⟨r + s - 1, (Sign.ofInt (jacobiSym ((-1) ^ s) p)).mul (G.odd p 2).sign⟩
      else if k = 2 then ⟨1, (G.odd p 2).sign⟩ else OddFactor.trivial) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have hn : G.n = r + s := by rw [← hc.real_dim, hr]
  have hdet : G.det = (p : ℤ) ^ 2 * (-1) ^ s := by
    have := G.det_eq_of hc (m := p ^ 2) (by have := hp.pos; positivity) hd hr
    rw [this]; push_cast; ring
  have hvp : padicValInt p G.det = 2 := by rw [hdet]; exact padicValInt_sq p s hp
  have hv2 : padicValInt 2 G.det = 0 := by
    rw [hdet]; exact padicValInt_sq_ne 2 p s Nat.prime_two hp (Ne.symm hp2)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := G.p2_shape hc p hp hp2 hvp h1
  obtain ⟨htriv, hdim, hsg, hoddeq, hE⟩ := G.two_part hc hv2
  have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by simp [GenusSymbolData.signature, hr]
  have hodd : (G.two 0).oddity = (r : ZMod 8) - s := by
    have h := hc.oddity_formula
    rw [hd, Nat.primeFactors_prime_pow (by norm_num) hp, Finset.filter_singleton, if_pos hp2,
      Finset.sum_singleton, b6, sq_odd_zmod8 p hpodd, sub_self, add_zero, hoddeq, hsig] at h
    exact h.symm
  refine ⟨fun k => ?_, fun k => ?_⟩
  · by_cases hk : k = 0
    · subst hk
      simp only [if_true]
      have hs : (G.two 0).sign = jacobiTwo G.det := hsg
      rw [hdet, jacobiTwo_sq p s hpodd] at hs
      generalize G.two 0 = f at hdim hs hodd
      obtain ⟨d, sg, ty, o⟩ := f
      dsimp only at hdim hs hodd
      subst hs hodd
      rw [hdim, hn]
    · simp only [if_neg hk]; exact htriv k (Nat.pos_of_ne_zero hk)
  · by_cases hk0 : k = 0
    · subst hk0
      simp only [if_true]
      rw [hdet, sq_div p s hp, ofInt_jacobi_negOne p s hpodd] at b5
      have hs0 : (G.odd p 0).sign = (Sign.ofInt (jacobiSym ((-1) ^ s) p)).mul (G.odd p 2).sign := by
        rw [ofInt_jacobi_negOne p s hpodd, ← b5]
        cases (G.odd p 0).sign <;> cases (G.odd p 2).sign <;> rfl
      generalize G.odd p 0 = f at b1 hs0
      obtain ⟨d, sg⟩ := f
      dsimp only at b1 hs0
      rw [hs0]
      congr 1
      omega
    · by_cases hk2 : k = 2
      · subst hk2
        simp only [if_neg hk0, if_true]
        generalize G.odd p 2 = f at b2
        obtain ⟨d, sg⟩ := f
        dsimp only at b2
        rw [b2]
      · simp only [if_neg hk0, if_neg hk2]
        by_cases hk1 : k = 1
        · subst hk1; exact b4
        · exact b3 k (by omega)

/-- **Uniqueness of the genus for the scale $p^2$** (Conway–Sloane, §8.1, Table 15.4, rows $\pm9$): two systems
satisfying the conditions with equal $(-1)$-adic symbols, equal types of the 2-adic constituent and equal sign of
$(p^2)^{e1}$ (nothing at the scale $p$) have identical $2$-adic and $p$-adic symbols and equal symbols at all other odd
primes. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (rows ±9: one genus for each (r,s), type and sign)"]
theorem thm_p2_unique (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (G G' : GenusSymbolData) (hc : G.Conditions)
    (hc' : G'.Conditions) (hr : G.real = G'.real) (hd : G.det.natAbs = p ^ 2) (hd' : G'.det.natAbs = p ^ 2)
    (h1 : (G.odd p 1).dim = 0) (h1' : (G'.odd p 1).dim = 0) (hT : (G.two 0).type = (G'.two 0).type)
    (he : (G.odd p 2).sign = (G'.odd p 2).sign) :
    (∀ k, G.two k = G'.two k) ∧ (∀ q, q.Prime → q ≠ 2 → G.odd q = G'.odd q) := by
  have hr1 : G.real = ⟨G.real.pos, G.real.neg⟩ := rfl
  have hr2 : G'.real = ⟨G.real.pos, G.real.neg⟩ := hr.symm.trans hr1
  generalize G.real.pos = r at hr1 hr2
  generalize G.real.neg = s at hr1 hr2
  obtain ⟨t1, o1⟩ := G.p2_data hc p hp hp2 hd hr1 h1
  obtain ⟨t2, o2⟩ := G'.p2_data hc' p hp hp2 hd' hr2 h1'
  have hn : G.n = r + s := by rw [← hc.real_dim, hr1]
  have hn' : G'.n = r + s := by rw [← hc'.real_dim, hr2]
  have hdet : G.det = (p : ℤ) ^ 2 * (-1) ^ s := by
    have := G.det_eq_of hc (m := p ^ 2) (by have := hp.pos; positivity) hd hr1
    rw [this]; push_cast; ring
  have hdet' : G'.det = (p : ℤ) ^ 2 * (-1) ^ s := by
    have := G'.det_eq_of hc' (m := p ^ 2) (by have := hp.pos; positivity) hd' hr2
    rw [this]; push_cast; ring
  refine ⟨fun k => ?_, fun q hq hq2 => ?_⟩
  · rw [t1 k, t2 k, hT]
  · by_cases hqp : q = p
    · subst hqp
      funext k
      rw [o1 k, o2 k, he]
    · funext k
      rw [G.odd_unit hc q hq hq2 (by rw [hdet]; exact padicValInt_sq_ne q p s hq hp hqp),
        G'.odd_unit hc' q hq hq2 (by rw [hdet']; exact padicValInt_sq_ne q p s hq hp hqp), hn, hn', hdet, hdet']

/-! ### Table 15.4, rows $\pm9$, $\mathrm I_{r,s}(9^{\pm1})$ and $\mathrm{II}_{r,s}(9^{\pm1})$ -/

set_option synthInstance.maxSize 1024 in
theorem typeI_plus_exists (r s : ℕ) (h : 1 ≤ r + s) :
    (⟨r + s, .plus, .I, (r : ZMod 8) - s⟩ : TwoFactor).Exists := by
  by_cases h3 : 3 ≤ r + s
  · exact typeI_big _ _ _ h3 (val_sub_mod_two r s)
  · have hr : r ≤ 2 := by omega
    have hs : s ≤ 2 := by omega
    interval_cases r <;> interval_cases s <;> first | omega | decide

theorem typeII_zero_exists (r s : ℕ) (h : ((r : ℤ) - s) % 8 = 0) (hn : r + s ≠ 0) :
    (⟨r + s, .plus, .II, 0⟩ : TwoFactor).Exists := by
  refine ⟨fun h0 => absurd (show r + s = 0 from h0) hn, fun h1 => ?_, (fun _ hI => by cases hI), ?_,
    fun _ => rfl⟩
  · have h1' : r + s = 1 := h1
    exfalso
    omega
  · show (0 : ZMod 8).val % 2 = (r + s) % 2
    simp
    omega

/-- **Table 15.4, $\pm9$, $\mathrm I_{r,s}(9^{e})$ in general** ($p = 3$, scale $9$, nothing at the scale $3$):
exists iff $n \ge 1$ and, for $n = 1$, $e = \left(\frac{-1}{3}\right)^s$. -/
theorem table154_nine_typeI (e : Sign) (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ^ 2 ∧ (G.two 0).type = .I ∧
        (G.odd 3 2).sign = e ∧ (G.odd 3 1).dim = 0) ↔ (1 ≤ r + s ∧ (r + s = 1 → e = negSignAt 3 s)) := by
  constructor
  · rintro ⟨G, hc, hr, hd, hT, he, h1⟩
    obtain ⟨hn, hcompat, -, -⟩ := (thm_p2_exists 3 r s Nat.prime_three (by norm_num) e .I
      (G.two 0).oddity).1 ⟨G, hc, hr, hd, hT, rfl, he, h1⟩
    exact ⟨hn, hcompat⟩
  · rintro ⟨hn, hcompat⟩
    obtain ⟨G, hG⟩ := (thm_p2_exists 3 r s Nat.prime_three (by norm_num) e .I ((r : ZMod 8) - s)).2
      ⟨hn, hcompat, typeI_plus_exists r s hn, rfl⟩
    obtain ⟨hc, hr, hd, hT, -, he, h1⟩ := hG
    exact ⟨G, hc, hr, hd, hT, he, h1⟩

/-- **Table 15.4, $\pm9$, $\mathrm I_{r,s}(9)$:** all signatures, exceptions $0$ and $1_{-1}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, I(9))"]
theorem table154_nine_typeI_plus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ^ 2 ∧ (G.two 0).type = .I ∧
        (G.odd 3 2).sign = .plus ∧ (G.odd 3 1).dim = 0) ↔ (1 ≤ r + s ∧ ¬ (r = 0 ∧ s = 1)) := by
  rw [table154_nine_typeI]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun ⟨h0, h1⟩ => ?_⟩
    subst h0 h1
    exact absurd (hc rfl) (by decide)
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun h1 => ?_⟩
    have : r = 1 ∧ s = 0 := by omega
    obtain ⟨rfl, rfl⟩ := this
    decide

/-- **Table 15.4, $\pm9$, $\mathrm I_{r,s}(9^{-1})$:** all signatures, exceptions $0$ and $1_{+1}$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, I(9^{-1}))"]
theorem table154_nine_typeI_minus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ^ 2 ∧ (G.two 0).type = .I ∧
        (G.odd 3 2).sign = .minus ∧ (G.odd 3 1).dim = 0) ↔ (1 ≤ r + s ∧ ¬ (r = 1 ∧ s = 0)) := by
  rw [table154_nine_typeI]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun ⟨h0, h1⟩ => ?_⟩
    subst h0 h1
    exact absurd (hc rfl) (by decide)
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun h1 => ?_⟩
    have : r = 0 ∧ s = 1 := by omega
    obtain ⟨rfl, rfl⟩ := this
    decide

/-- **Table 15.4, $\pm9$, $\mathrm{II}_{r,s}(9^{e})$ in general:** signature $0$, exception $0$ (both signs $e$). -/
theorem table154_nine_typeII (e : Sign) (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ^ 2 ∧ (G.two 0).type = .II ∧
        (G.odd 3 2).sign = e ∧ (G.odd 3 1).dim = 0) ↔ (((r : ℤ) - s) % 8 = 0 ∧ r + s ≠ 0) := by
  constructor
  · rintro ⟨G, hc, hr, hd, hT, he, h1⟩
    obtain ⟨hn, -, hE, ht⟩ := (thm_p2_exists 3 r s Nat.prime_three (by norm_num) e .II
      (G.two 0).oddity).1 ⟨G, hc, hr, hd, hT, rfl, he, h1⟩
    have h0 : (G.two 0).oddity = 0 := by
      exact hE.2.2.2.2 rfl
    rw [h0] at ht
    refine ⟨?_, by omega⟩
    have h6 : (((r : ℤ) - s : ℤ) : ZMod 8) = 0 := by push_cast; exact ht
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h6
    omega
  · rintro ⟨h, hn⟩
    have hz : (r : ZMod 8) - s = 0 := (sub_eq_zero_iff_mod r s).2 h
    obtain ⟨G, hG⟩ := (thm_p2_exists 3 r s Nat.prime_three (by norm_num) e .II 0).2
      ⟨by omega, fun h1 => by exfalso; omega, typeII_zero_exists r s h hn, hz⟩
    obtain ⟨hc, hr, hd, hT, -, he, h1⟩ := hG
    exact ⟨G, hc, hr, hd, hT, he, h1⟩

/-- **Table 15.4, $\pm9$, $\mathrm{II}_{r,s}(9)$:** signature $0$, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, II(9))"]
theorem table154_nine_typeII_plus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ^ 2 ∧ (G.two 0).type = .II ∧
        (G.odd 3 2).sign = .plus ∧ (G.odd 3 1).dim = 0) ↔ (((r : ℤ) - s) % 8 = 0 ∧ r + s ≠ 0) :=
  table154_nine_typeII .plus r s

/-- **Table 15.4, $\pm9$, $\mathrm{II}_{r,s}(9^{-1})$:** signature $0$, exception $0$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, Table 15.4, p. 387 (±9, II(9^{-1}))"]
theorem table154_nine_typeII_minus (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ^ 2 ∧ (G.two 0).type = .II ∧
        (G.odd 3 2).sign = .minus ∧ (G.odd 3 1).dim = 0) ↔ (((r : ℤ) - s) % 8 = 0 ∧ r + s ≠ 0) :=
  table154_nine_typeII .minus r s

end QuadFormsKB.ConwaySloane
