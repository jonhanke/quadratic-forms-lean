/-
# Conway–Sloane, Ch. 15, §6.1, Table 15.3 at odd primes

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §6.1, Table 15.3, p. 374
(`conwaysloane1999`). For an odd prime $p$ the square classes of $\mathbb Q_p^\times$ are $u_+, u_-, pu_+, pu_-$
($u_\pm$ a unit with $\left(\frac{u}{p}\right) = \pm1$). For a binary form of determinant class $D$, the table lists, for
each value of its $p$-excess (depending on $p \bmod 8$), the square classes it represents. The $p = 2$ part is in
`Rational.lean` (`represents_two_adic_iff_oddity`, `table_check`).

**Formalization.** A square class is a pair `(v, ε)` (`SqCl`: $v \in \{0, 1\}$ the parity of the valuation, `ε = true` for
a residue unit part); `pEc P c` is the $p$-excess of $\langle c\rangle$ for $p \equiv P \pmod 8$; `oddTable P D` is the
book's table for the determinant class $D$ (a list of rows: $p$-excess, represented classes; rows marked "–" in the book
are absent).

**Proves**
* `represents_padic_iff_pExcess` (the mechanism, as for $p = 2$): $\langle a, b\rangle$ represents $r$ over
  $\mathbb Q_p$ iff $p\text{-excess}\langle a,b\rangle = p\text{-excess}\langle ab\rangle + p\text{-excess}\langle r\rangle
  + p\text{-excess}\langle -ab\rangle - p\text{-excess}\langle -rab\rangle$;
* `table153_odd_check`: the table entries agree with this criterion, for all $p \bmod 8$, all classes $a, b, r$
  (finite check by `decide`), and the rows listed are exactly the attained $p$-excesses;
* `table153_odd`: **Table 15.3 for odd $p$**: $\langle a,b\rangle$ represents $r$ over $\mathbb Q_p$ iff the class of $r$
  is in the row of the table for the class of $ab$ and the $p$-excess of $\langle a,b\rangle$.
-/
import QuadFormsKB.Literature.ConwaySloane.Rational
import QuadFormsKB.Literature.ConwaySloane.Theorem11
import QuadFormsKB.Witt.Represents

namespace QuadFormsKB.ConwaySloane

open QuadForm Rational

/-- A square class of $\mathbb Q_p^\times$, $p$ odd: (parity of the valuation, unit part a residue). -/
abbrev SqCl := Bool × Bool

/-- The $p$-excess of $\langle c\rangle$ for $p \equiv P \pmod 8$: $P - 1 + 4[\varepsilon = -]$ if the valuation is
odd, $0$ otherwise. -/
def pEc (P : ZMod 8) (c : SqCl) : ZMod 8 := if c.1 then (P - 1) + (if c.2 then 0 else 4) else 0

/-- Product of square classes. -/
def mulc (c d : SqCl) : SqCl := (xor c.1 d.1, c.2 == d.2)

/-- Negation of a square class: $-1$ is a residue iff $p \equiv 1 \pmod 4$. -/
def negc (P : ZMod 8) (c : SqCl) : SqCl := (c.1, if P = 1 ∨ P = 5 then c.2 else !c.2)

/-- The classes $u_+, u_-, pu_+, pu_-$. -/
def uP : SqCl := (false, true)
def uM : SqCl := (false, false)
def pP : SqCl := (true, true)
def pM : SqCl := (true, false)

/-- **Table 15.3, odd $p$** (p. 374), as printed: for $p \equiv P \pmod 8$ and determinant class $D$, the rows
($p$-excess, square classes represented). -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, Table 15.3, p. 374 (p ≥ 3)"]
def oddTable (P : ZMod 8) (D : SqCl) : List (ZMod 8 × List SqCl) :=
  if D = uP then
    (if P = 1 ∨ P = 5 then [(0, [uP, uM, pP, pM])] else [(0, [uP, uM]), (4, [pP, pM])])
  else if D = uM then
    (if P = 3 ∨ P = 7 then [(0, [uP, uM, pP, pM])] else [(0, [uP, uM]), (4, [pP, pM])])
  else if D = pP then
    [(P - 1, [uP, pP]), (P + 3, [uM, pM])]
  else
    [(P + 3, [uP, pM]), (P - 1, [uM, pP])]

/-- The classes represented by the row of the table for $D$ with $p$-excess $e$ (empty if there is no such row). -/
def rowFor (P : ZMod 8) (D : SqCl) (e : ZMod 8) : List SqCl :=
  ((oddTable P D).filter fun row => row.1 = e).flatMap Prod.snd

/-- **The table agrees with the criterion** (finite check): for every $p \bmod 8$ and classes $a$, $b$, $r$, the class
$r$ is in the row of $\mathrm{class}(ab)$ with excess $p\text{-excess}\langle a\rangle + p\text{-excess}\langle b\rangle$ iff
the criterion of `represents_padic_iff_pExcess` holds; and the excesses of the rows are exactly the attained ones. -/
theorem table153_odd_check : ∀ P ∈ ({1, 3, 5, 7} : Finset (ZMod 8)), ∀ a b r : SqCl,
    (r ∈ rowFor P (mulc a b) (pEc P a + pEc P b) ↔
      pEc P a + pEc P b = pEc P (mulc a b) + pEc P r + pEc P (negc P (mulc a b)) -
        pEc P (negc P (mulc r (mulc a b)))) ∧
    ((oddTable P (mulc a b)).map Prod.fst).Nodup := by
  decide

theorem table153_rows_attained : ∀ P ∈ ({1, 3, 5, 7} : Finset (ZMod 8)), ∀ D : SqCl, ∀ row ∈ oddTable P D,
    ∃ a b : SqCl, mulc a b = D ∧ pEc P a + pEc P b = row.1 := by
  decide

section Odd

variable {p : ℕ} [hp : Fact p.Prime]

/-- The square class of a nonzero integer at the odd prime $p$. -/
noncomputable def clsOf (p : ℕ) (x : ℤ) : SqCl := (decide (Odd (padicValInt p x)), decide (jacobiSym (unitPart p x) p = 1))

theorem pExcessEntry_eq_pEc (hp2 : p ≠ 2) {x : ℤ} (hx : x ≠ 0) : pExcessEntry p x = pEc (p : ZMod 8) (clsOf p x) := by
  have hr := natCast_zmod8_odd (hp.out.odd_of_ne_two hp2)
  have hJ := jacobiSym_pm_of_not_dvd (p := p) (not_dvd_unitPart hx)
  unfold pExcessEntry pEc clsOf
  rcases Nat.even_or_odd (padicValInt p x) with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hno : ¬ Odd (padicValInt p x) := Nat.not_odd_iff_even.mpr ⟨k, hk⟩
    rw [hk, ← two_mul, pow_mul]
    have h1 : ((p : ZMod 8) ^ 2) = 1 := by rcases hr with h | h | h | h <;> rw [h] <;> decide
    rw [h1, one_pow]
    have h2k : ¬ Odd (2 * k) := Nat.not_odd_iff_even.mpr (even_two_mul k)
    simp [h2k]
  · have ho : Odd (padicValInt p x) := ⟨k, hk⟩
    rw [hk, pow_succ, pow_mul]
    have h1 : ((p : ZMod 8) ^ 2) = 1 := by rcases hr with h | h | h | h <;> rw [h] <;> decide
    rw [h1, one_pow, one_mul]
    rcases hJ with h | h <;> simp [ho, ← hk, h]

theorem clsOf_mul (hp2 : p ≠ 2) {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) : clsOf p (x * y) = mulc (clsOf p x) (clsOf p y) := by
  have hJx := jacobiSym_pm_of_not_dvd (p := p) (not_dvd_unitPart hx)
  have hJy := jacobiSym_pm_of_not_dvd (p := p) (not_dvd_unitPart hy)
  unfold clsOf mulc
  rw [padicValInt.mul hx hy, unitPart_mul hx hy, jacobiSym.mul_left]
  simp only [Prod.mk.injEq]
  constructor
  · rcases Nat.even_or_odd (padicValInt p x) with h1 | h1 <;> rcases Nat.even_or_odd (padicValInt p y) with h2 | h2 <;>
      simp [h1, h2, Nat.odd_add, Nat.not_odd_iff_even.mpr, Nat.not_even_iff_odd.mpr]
  · rcases hJx with h1 | h1 <;> rcases hJy with h2 | h2 <;> simp [h1, h2]

theorem clsOf_neg (hp2 : p ≠ 2) {x : ℤ} (hx : x ≠ 0) : clsOf p (-x) = negc (p : ZMod 8) (clsOf p x) := by
  have h := clsOf_mul hp2 (x := -1) (y := x) (by norm_num) hx
  rw [neg_one_mul] at h
  rw [h]
  have hr := natCast_zmod8_odd (hp.out.odd_of_ne_two hp2)
  have hJx := jacobiSym_pm_of_not_dvd (p := p) (not_dvd_unitPart hx)
  have hm1 : clsOf p (-1) = (false, decide (p % 4 = 1)) := by
    unfold clsOf
    have hv : padicValInt p (-1) = 0 := padicValInt.eq_zero_of_not_dvd (by
      intro h; exact (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one (by simpa using h))
    have hu : unitPart p (-1) = -1 := by simp [unitPart, hv]
    rw [hv, hu, jacobiSym.at_neg_one (hp.out.odd_of_ne_two hp2)]
    simp only [Nat.not_odd_zero, decide_false, Prod.mk.injEq, true_and]
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    have : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h4 with h | h <;> simp [h, this]
  rw [hm1]
  unfold mulc negc
  have hp8 : (p : ZMod 8) = 1 ∨ (p : ZMod 8) = 5 ↔ p % 4 = 1 := by
    have : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by simp
    have h8 : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have : p % 4 = p % 8 % 4 := by omega
    interval_cases hq : p % 8 <;> simp_all <;> decide
  by_cases h : p % 4 = 1
  · simp [h, hp8.mpr h]
  · have : ¬ ((p : ZMod 8) = 1 ∨ (p : ZMod 8) = 5) := fun h' => h (hp8.mp h')
    simp [h, this]

end Odd

/-- **The mechanism of Table 15.3 at an odd prime** (§6.1, pp. 373–375): for nonzero integers $a, b, r$ the binary form
$\langle a,b\rangle$ represents $r$ over $\mathbb Q_p$ iff
$p\text{-excess}\langle a,b\rangle = p\text{-excess}\langle ab\rangle + p\text{-excess}\langle r\rangle +
p\text{-excess}\langle -ab\rangle - p\text{-excess}\langle -rab\rangle$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, Table 15.3, p. 374 (p ≥ 3)"]
theorem represents_padic_iff_pExcess (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {a b r : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hr : r ≠ 0) :
    (diag ![(a : ℚ), b]).RepresentsIn ℚ_[p] (r : ℚ) ↔
      pExcess p ![a, b] = pExcessEntry p (a * b) + pExcessEntry p r + pExcessEntry p (-(a * b)) -
        pExcessEntry p (-(r * (a * b))) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hcast : ∀ i, (![(a : ℚ), b] : Fin 2 → ℚ) i ≠ 0 := fun i => by
    fin_cases i <;> simp [ha, hb]
  have hrep := represents_padic_two_iff p ![(a : ℚ), b] hcast (r : ℚ) (by exact_mod_cast hr)
  rw [hrep]
  have e1 : hilbertSymbol ℚ_[p] (algebraMap ℚ ℚ_[p] (r : ℚ)) (algebraMap ℚ ℚ_[p] (-∏ i, (![(a : ℚ), b] : Fin 2 → ℚ) i)) =
      (RatPlace.finite ⟨p, hp.out⟩).hilbert (r : ℚ) ((-(a * b) : ℤ) : ℚ) := by
    simp [RatPlace.hilbert, Fin.prod_univ_two]
  have e2 : hasseInvariant ℚ_[p] ![(a : ℚ), b] = (RatPlace.finite ⟨p, hp.out⟩).hilbert (a : ℚ) (b : ℚ) := by
    simp [hasseInvariant, Fin.prod_univ_two, RatPlace.hilbert]
  rw [e1, e2]
  have m1 := pExcessEntry_mul p hp2 ha hb
  have m2 := pExcessEntry_mul p hp2 hr (neg_ne_zero.mpr hab)
  have hpx : pExcess p ![a, b] = pExcessEntry p a + pExcessEntry p b := by
    simp [pExcess, Fin.sum_univ_two]
  have hY := RatPlace.hilbert_pm (RatPlace.finite ⟨p, hp.out⟩) (r : ℚ) ((-(a * b) : ℤ) : ℚ)
  have hX := RatPlace.hilbert_pm (RatPlace.finite ⟨p, hp.out⟩) (a : ℚ) (b : ℚ)
  have e3 : r * -(a * b) = -(r * (a * b)) := by ring
  rw [e3] at m2
  rw [← sgn4_inj hY hX, hpx]
  constructor
  · intro h
    linear_combination m1 - m2 - h
  · intro h
    linear_combination m1 - m2 - h

/-- **Table 15.3 for an odd prime $p$** (Conway–Sloane, §6.1, p. 374): the binary form $\langle a, b\rangle$ ($a, b$
nonzero integers) represents the nonzero integer $r$ over $\mathbb Q_p$ iff the square class of $r$ is listed in the row
of the table for the determinant class of $ab$ and the $p$-excess of $\langle a,b\rangle$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, Table 15.3, p. 374 (p ≥ 3)"]
theorem table153_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {a b r : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0) :
    (diag ![(a : ℚ), b]).RepresentsIn ℚ_[p] (r : ℚ) ↔
      clsOf p r ∈ rowFor (p : ZMod 8) (clsOf p (a * b)) (pExcess p ![a, b]) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hP : (p : ZMod 8) ∈ ({1, 3, 5, 7} : Finset (ZMod 8)) := by
    rcases natCast_zmod8_odd (hp.out.odd_of_ne_two hp2) with h | h | h | h <;> simp [h]
  have hpx : pExcess p ![a, b] = pEc (p : ZMod 8) (clsOf p a) + pEc (p : ZMod 8) (clsOf p b) := by
    simp [pExcess, Fin.sum_univ_two, pExcessEntry_eq_pEc hp2 ha, pExcessEntry_eq_pEc hp2 hb]
  rw [represents_padic_iff_pExcess p hp2 ha hb hr, hpx, clsOf_mul hp2 ha hb,
    (table153_odd_check _ hP (clsOf p a) (clsOf p b) (clsOf p r)).1,
    pExcessEntry_eq_pEc hp2 hab, pExcessEntry_eq_pEc hp2 hr, pExcessEntry_eq_pEc hp2 (neg_ne_zero.mpr hab),
    pExcessEntry_eq_pEc hp2 (neg_ne_zero.mpr (mul_ne_zero hr hab)), clsOf_mul hp2 ha hb, clsOf_neg hp2 hab,
    clsOf_neg hp2 (mul_ne_zero hr hab), clsOf_mul hp2 hr hab, clsOf_mul hp2 ha hb]

/-! ### $p = -1$ -/

/-- **Table 15.3 at $p = -1$** (Conway–Sloane, §6.1, p. 374): a real binary form $\langle a, b\rangle$ of determinant
class $+u$ ($ab > 0$) represents only the numbers of the sign of $a$ (signature $\pm2$); one of class $-u$ ($ab < 0$)
represents both signs (signature $0$). -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, Table 15.3, p. 374 (p = -1)"]
theorem table153_real {a b r : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0) :
    (diag ![a, b]).RepresentsIn ℝ r ↔ (0 < a * b → 0 < a * r) := by
  have hev : ∀ x : Fin 2 → ℝ, (diag ![a, b]).evalIn ℝ x = (a : ℝ) * x 0 ^ 2 + (b : ℝ) * x 1 ^ 2 := fun x => by
    rw [evalIn_diag, Fin.sum_univ_two]; simp
  constructor
  · rintro ⟨x, hx⟩ hab
    rw [hev] at hx
    simp only [eq_ratCast] at hx
    have hx' : ((a : ℝ) * x 0 ^ 2 + (b : ℝ) * x 1 ^ 2) = r := hx
    have hab' : (0 : ℝ) < a * b := by exact_mod_cast hab
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    have : (0 : ℝ) < a * r := by
      rw [← hx']
      rcases lt_or_gt_of_ne (show (a : ℝ) ≠ 0 by exact_mod_cast ha) with h | h
      · have hb0 : (b : ℝ) < 0 := by nlinarith
        have : (a : ℝ) * x 0 ^ 2 + (b : ℝ) * x 1 ^ 2 < 0 := by
          rcases lt_or_eq_of_le (add_nonpos (mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg (x 0)))
            (mul_nonpos_of_nonpos_of_nonneg hb0.le (sq_nonneg (x 1)))) with h' | h'
          · exact h'
          · exact absurd (hx'.symm.trans h') hr'
        nlinarith
      · have hb0 : (0 : ℝ) < b := by nlinarith
        have : 0 < (a : ℝ) * x 0 ^ 2 + (b : ℝ) * x 1 ^ 2 := by
          rcases lt_or_eq_of_le (add_nonneg (mul_nonneg h.le (sq_nonneg (x 0))) (mul_nonneg hb0.le (sq_nonneg (x 1))))
            with h' | h'
          · exact h'
          · exact absurd (hx'.symm.trans h'.symm) hr'
        nlinarith
    exact_mod_cast this
  · intro h
    by_cases har : 0 < a * r
    · -- represent by the first variable
      refine ⟨![Real.sqrt ((r : ℝ) / a), 0], ?_⟩
      rw [hev]
      have hq : (0 : ℝ) ≤ (r : ℝ) / a := by
        have : (0 : ℝ) < a * r := by exact_mod_cast har
        rcases lt_or_gt_of_ne (show (a : ℝ) ≠ 0 by exact_mod_cast ha) with h' | h'
        · exact (div_pos_of_neg_of_neg (by nlinarith) h').le
        · exact (div_pos (by nlinarith) h').le
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.sq_sqrt hq, eq_ratCast]
      field_simp
      ring
    · -- then `ab < 0`, and `b r > 0`: represent by the second variable
      have hab : a * b < 0 := by
        rcases lt_or_gt_of_ne (mul_ne_zero ha hb) with h' | h'
        · exact h'
        · exact absurd (h h') har
      have hbr : 0 < b * r := by
        have har' : a * r < 0 := lt_of_le_of_ne (not_lt.mp har) (mul_ne_zero ha hr)
        nlinarith [mul_pos_iff.mp (show 0 < (a * b) * (a * r) by nlinarith), sq_nonneg a, mul_self_pos.mpr ha]
      refine ⟨![0, Real.sqrt ((r : ℝ) / b)], ?_⟩
      rw [hev]
      have hq : (0 : ℝ) ≤ (r : ℝ) / b := by
        have : (0 : ℝ) < b * r := by exact_mod_cast hbr
        rcases lt_or_gt_of_ne (show (b : ℝ) ≠ 0 by exact_mod_cast hb) with h' | h'
        · exact (div_pos_of_neg_of_neg (by nlinarith) h').le
        · exact (div_pos (by nlinarith) h').le
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.sq_sqrt hq, eq_ratCast]
      field_simp
      ring

end QuadFormsKB.ConwaySloane
