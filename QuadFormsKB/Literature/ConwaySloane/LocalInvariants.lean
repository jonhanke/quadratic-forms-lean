/-
# Conway–Sloane, Ch. 15, §6.1: the $p$-adic invariants are complete over $\mathbb Q_p$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §6.1, p. 375
(`conwaysloane1999`): "the oddity and the determinant are a complete set of invariants for 2-adic binary rational forms
… and similarly for other $p$". Formalized for integer diagonal forms in any number $n$ of variables (0-based): two such
forms are equivalent over $\mathbb Q_p$ iff their determinants lie in the same square class of $\mathbb Q_p$ and their
$p$-excesses (oddities, $p = 2$) agree.

**Proves**
* `pExcessEntry_eq_of_sameSquareClass`, `oddityEntry_eq_of_sameSquareClass`: the rank-one $p$-excess (oddity) depends
  only on the square class in $\mathbb Q_p$;
* `isometric_padic_iff_pExcess` ($p$ odd), `isometric_two_adic_iff_oddity` ($p = 2$).
-/
import QuadFormsKB.Literature.ConwaySloane.Table153

namespace QuadFormsKB.ConwaySloane

open QuadForm Rational

section

variable {p : ℕ} [hp : Fact p.Prime]

theorem isSquare_mul_of_sameSquareClass {x y : ℤ} (hy : y ≠ 0) (h : SameSquareClass ℚ_[p] (x : ℚ) (y : ℚ)) :
    IsSquare (((x * y : ℤ) : ℚ_[p])) := by
  obtain ⟨t, -, ht⟩ := h
  refine ⟨t * y, ?_⟩
  have : ((x : ℚ_[p])) = t ^ 2 * y := by simpa using ht
  push_cast; rw [this]; ring

/-- An integer $p^v u$, $p \nmid u$, as $p^v$ times a unit of $\mathbb Z_p$. -/
theorem exists_unit_eq {x : ℤ} (hx : x ≠ 0) :
    ∃ u : ℤ_[p]ˣ, ((x : ℤ) : ℚ_[p]) = (p : ℚ_[p]) ^ (padicValInt p x : ℤ) * ((u : ℤ_[p]) : ℚ_[p]) ∧
      (u : ℤ_[p]) = (unitPart p x : ℤ_[p]) := by
  obtain ⟨u, hu⟩ := exists_unit_of_not_dvd (p := p) (unitPart p x) (not_dvd_unitPart hx)
  refine ⟨u, ?_, hu⟩
  rw [hu]
  conv_lhs => rw [eq_pow_mul_unitPart (p := p) x]
  push_cast
  rw [zpow_natCast]

/-- **The rank-one $p$-excess depends only on the square class in $\mathbb Q_p$** ($p$ odd). -/
theorem pExcessEntry_eq_of_sameSquareClass (hp2 : p ≠ 2) {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : SameSquareClass ℚ_[p] (x : ℚ) (y : ℚ)) : pExcessEntry p x = pExcessEntry p y := by
  have hsq := isSquare_mul_of_sameSquareClass hy h
  obtain ⟨u, hu, hu'⟩ := exists_unit_eq (p := p) hx
  obtain ⟨w, hw, hw'⟩ := exists_unit_eq (p := p) hy
  have e : (((x * y : ℤ)) : ℚ_[p]) = (p : ℚ_[p]) ^ ((padicValInt p x + padicValInt p y : ℕ) : ℤ) *
      (((u * w : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
    push_cast; rw [hu, hw, zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; ring
  rw [e, HilbertLocal.isSquare_zpow_mul_unit_iff hp2] at hsq
  obtain ⟨hev, hsqu⟩ := hsq
  rw [pExcessEntry_eq_pEc hp2 hx, pExcessEntry_eq_pEc hp2 hy]
  congr 1
  unfold clsOf
  refine Prod.ext ?_ ?_
  · simp only
    have h2 : Even (padicValInt p x + padicValInt p y) := by exact_mod_cast hev
    rcases Nat.even_add.mp h2 with h3
    by_cases hxo : Odd (padicValInt p x)
    · have : Odd (padicValInt p y) := by
        by_contra hno
        exact (Nat.not_even_iff_odd.mpr hxo) (h3.mpr (Nat.not_odd_iff_even.mp hno))
      simp [hxo, this]
    · have : ¬ Odd (padicValInt p y) := fun hyo =>
        hxo (Nat.not_even_iff_odd.mp fun he => (Nat.not_even_iff_odd.mpr hyo) (h3.mp he))
      simp [hxo, this]
  · simp only
    have hm : PadicInt.toZMod ((u * w : ℤ_[p]ˣ) : ℤ_[p]) = ((unitPart p x * unitPart p y : ℤ) : ZMod p) := by
      push_cast
      rw [map_mul, hu', hw', map_intCast, map_intCast]
    rw [hm] at hsqu
    have hnd : ¬ (p : ℤ) ∣ unitPart p x * unitPart p y := fun h =>
      ((Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h).elim (not_dvd_unitPart hx) (not_dvd_unitPart hy)
    have hL : jacobiSym (unitPart p x * unitPart p y) p = 1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p
        (fun h => hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h))]
      exact hsqu
    rw [jacobiSym.mul_left] at hL
    rcases jacobiSym_pm_of_not_dvd (p := p) (not_dvd_unitPart hx) with h1 | h1 <;>
      rcases jacobiSym_pm_of_not_dvd (p := p) (not_dvd_unitPart hy) with h2 | h2 <;>
      simp_all

/-- **$\mathbb Q_p$-classification by the determinant and the $p$-excess** (Conway–Sloane, §6.1, p. 375: "similarly
for other $p$"), $p$ odd, for integer diagonal forms. -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, p. 375 (p odd)"]
theorem isometric_padic_iff_pExcess (hp2 : p ≠ 2) {n : ℕ} (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) :
    (diag fun i => (a i : ℚ)).IsometricIn ℚ_[p] (diag fun i => (b i : ℚ)) ↔
      SameSquareClass ℚ_[p] ((∏ i, a i : ℤ) : ℚ) ((∏ i, b i : ℤ) : ℚ) ∧ pExcess p a = pExcess p b := by
  have ha' : ∀ i, (fun i => (a i : ℚ)) i ≠ 0 := fun i => by simpa using ha i
  have hb' : ∀ i, (fun i => (b i : ℚ)) i ≠ 0 := fun i => by simpa using hb i
  have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hB : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  rw [isometric_padic_iff_invariants p _ _ ha' hb']
  push_cast
  refine and_congr_right fun hss => ?_
  have hS : SameSquareClass ℚ_[p] ((∏ i, a i : ℤ) : ℚ) ((∏ i, b i : ℤ) : ℚ) := by push_cast; exact hss
  rw [pExcess_eq_hasse p hp2 a ha, pExcess_eq_hasse p hp2 b hb,
    pExcessEntry_eq_of_sameSquareClass hp2 hA hB hS, add_right_inj,
    sgn4_inj (hasseSerre_pm _ _) (hasseSerre_pm _ _)]
  have h1 := RatPlace.hasseSerre_finite ⟨p, hp.out⟩ (fun i => (a i : ℚ))
  have h2 := RatPlace.hasseSerre_finite ⟨p, hp.out⟩ (fun i => (b i : ℚ))
  rw [h1, h2]

end

section Two

/-- **The rank-one oddity depends only on the square class in $\mathbb Q_2$.** -/
theorem oddityEntry_eq_of_sameSquareClass {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : SameSquareClass ℚ_[2] (x : ℚ) (y : ℚ)) : oddityEntry x = oddityEntry y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := isSquare_mul_of_sameSquareClass hy h
  obtain ⟨u, hu, hu'⟩ := exists_unit_eq (p := 2) hx
  obtain ⟨w, hw, hw'⟩ := exists_unit_eq (p := 2) hy
  have e : (((x * y : ℤ)) : ℚ_[2]) = (2 : ℚ_[2]) ^ ((padicValInt 2 x + padicValInt 2 y : ℕ) : ℤ) *
      (((u * w : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) := by
    push_cast; rw [hu, hw, zpow_add₀ (by norm_num)]; push_cast; ring
  rw [e, HilbertLocal.isSquare_two_zpow_mul_unit_iff] at hsq
  obtain ⟨hev, h8⟩ := hsq
  refine oddityEntry_eq_of ?_ ?_
  · have h2 : Even (padicValInt 2 x + padicValInt 2 y) := by exact_mod_cast hev
    have h3 := Nat.even_add.mp h2
    constructor
    · intro hxo
      by_contra hno
      exact (Nat.not_even_iff_odd.mpr hxo) (h3.mpr (Nat.not_odd_iff_even.mp hno))
    · intro hyo
      by_contra hno
      exact (Nat.not_even_iff_odd.mpr hyo) (h3.mp (Nat.not_odd_iff_even.mp hno))
  · have hm : PadicInt.toZModPow 3 ((u * w : ℤ_[2]ˣ) : ℤ_[2]) = ((unitPart 2 x * unitPart 2 y : ℤ) : ZMod (2 ^ 3)) := by
      push_cast
      rw [map_mul, hu', hw', map_intCast, map_intCast]
    rw [hm] at h8
    have h8' : ((unitPart 2 x : ℤ) : ZMod 8) * (unitPart 2 y : ZMod 8) = 1 := by exact_mod_cast h8
    have hy2 : ((unitPart 2 y : ℤ) : ZMod 8) ^ 2 = 1 := Binary.sq_odd_zmod8 (by exact_mod_cast not_dvd_unitPart (p := 2) hy)
    linear_combination ((unitPart 2 y : ℤ) : ZMod 8) * h8' - ((unitPart 2 x : ℤ) : ZMod 8) * hy2

/-- **$\mathbb Q_2$-classification by the determinant and the oddity** (Conway–Sloane, §6.1, p. 375: "the oddity and
the determinant are a complete set of invariants"), for integer diagonal forms in any dimension. -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, p. 375 (p = 2)"]
theorem isometric_two_adic_iff_oddity {n : ℕ} (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (diag fun i => (a i : ℚ)).IsometricIn ℚ_[2] (diag fun i => (b i : ℚ)) ↔
      SameSquareClass ℚ_[2] ((∏ i, a i : ℤ) : ℚ) ((∏ i, b i : ℤ) : ℚ) ∧ oddity a = oddity b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha' : ∀ i, (fun i => (a i : ℚ)) i ≠ 0 := fun i => by simpa using ha i
  have hb' : ∀ i, (fun i => (b i : ℚ)) i ≠ 0 := fun i => by simpa using hb i
  have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hB : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  rw [isometric_padic_iff_invariants 2 _ _ ha' hb']
  push_cast
  refine and_congr_right fun hss => ?_
  have hS : SameSquareClass ℚ_[2] ((∏ i, a i : ℤ) : ℚ) ((∏ i, b i : ℤ) : ℚ) := by push_cast; exact hss
  rw [oddity_eq_hasse a ha, oddity_eq_hasse b hb, oddityEntry_eq_of_sameSquareClass hA hB hS, add_right_inj,
    sgn4_inj (hasseSerre_pm _ _) (hasseSerre_pm _ _)]
  have h1 := RatPlace.hasseSerre_finite ⟨2, Nat.prime_two⟩ (fun i => (a i : ℚ))
  have h2 := RatPlace.hasseSerre_finite ⟨2, Nat.prime_two⟩ (fun i => (b i : ℚ))
  rw [h1, h2]

/-- **The example of §6.1** (Conway–Sloane, p. 375): $x^2 + 6y^2$ does not represent $4^m(8k+3)$ over $\mathbb Q_2$
(the oddity criterion of Table 15.3 gives $0 \ne 4$). -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, p. 375 (x² + 6y² does not represent 4^m(8k+3))"]
theorem not_represents_one_six (m : ℕ) (k : ℤ) :
    ¬ (diag ![(1 : ℚ), 6]).RepresentsIn ℚ_[2] (((4 ^ m * (8 * k + 3) : ℤ)) : ℚ) := by
  have hr : (4 ^ m * (8 * k + 3) : ℤ) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega)
  have h := represents_two_adic_iff_oddity (a := 1) (b := 6) (r := 4 ^ m * (8 * k + 3)) one_ne_zero (by norm_num) hr
  push_cast at h ⊢
  rw [h]
  have e1 : oddityEntry 1 = 1 := by simpa using oddityEntry_two_pow_mul 0 1 (by decide)
  have h80 : (8 : ZMod 8) = 0 := rfl
  have e6 : oddityEntry 6 = 7 := by
    have := oddityEntry_two_pow_mul 1 3 (by decide); norm_num at this; rw [this]; try decide
  have em6 : oddityEntry (-6) = 1 := by
    have := oddityEntry_two_pow_mul 1 (-3) (by decide); norm_num at this; rw [this]; try decide
  have er : oddityEntry (4 ^ m * (8 * k + 3)) = 3 := by
    have hu : ¬ (2 : ℤ) ∣ 8 * k + 3 := by omega
    have := oddityEntry_two_pow_mul (2 * m) (8 * k + 3) hu
    rw [pow_mul] at this; norm_num at this; rw [this]
    have hne : ¬ Odd (2 * m) := Nat.not_odd_iff_even.mpr (even_two_mul m)
    rw [h80, zero_mul, zero_add]; simp [hne]
  have erm : oddityEntry (-(4 ^ m * (8 * k + 3) * 6)) = 7 := by
    have hu : ¬ (2 : ℤ) ∣ -3 * (8 * k + 3) := by omega
    have := oddityEntry_two_pow_mul (2 * m + 1) (-3 * (8 * k + 3)) hu
    have ee : (2 : ℤ) ^ (2 * m + 1) * (-3 * (8 * k + 3)) = -(4 ^ m * (8 * k + 3) * 6) := by
      rw [pow_succ, pow_mul]; ring
    rw [ee] at this; rw [this]
    have h7 : ((-3 * (8 * k + 3) : ℤ) : ZMod 8) = 7 := by
      rw [show (-3 * (8 * k + 3) : ℤ) = 7 + 8 * (-3 * k - 2) by ring]
      push_cast; rw [h80, zero_mul, add_zero]
    rw [h7]
    split_ifs with hh
    · rcases hh with ⟨-, h'⟩; revert h'; decide
    · rfl
  simp only [oddity, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, e1, e6, em6, er]
  rw [show -(4 ^ m * (8 * k + 3) * 6) = -(4 ^ m * (8 * k + 3) * 6) from rfl, erm]
  decide

end Two

end QuadFormsKB.ConwaySloane
