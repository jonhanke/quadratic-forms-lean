/-
# Conway–Sloane, Ch. 15, §6.2, (19): reduction of Theorem 3 to Theorem 7

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §6.2, (19), pp. 376–377
(`conwaysloane1999`). If $f$ and $g$ have the same invariants (the determinant ratio is a square and all the
$p$-excesses agree), then $f \oplus f \oplus f \oplus f$ and $g \oplus f \oplus f \oplus f$ have trivial invariants (all
$p$-excesses $\equiv 0$, square determinant), so Theorem 7 applies to both; Witt cancellation then gives Theorem 3.

**Proves** for integer diagonal forms (0-based, as in `Rational.lean`):
* `excess_append`: the excesses are additive under $\oplus$;
* `four_mul_excess`: every excess is even ($4 \cdot \text{excess} \equiv 0 \pmod 8$, §5.2, Remark (2), p. 373);
* `trivialInvariants_four`, `trivialInvariants_mixed`: the two claims of (19).
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem11

namespace QuadFormsKB.ConwaySloane

open Finset Rational

variable {m k : ℕ}

theorem signature_append (a : Fin m → ℤ) (b : Fin k → ℤ) :
    signature (Fin.append a b) = signature a + signature b := by
  unfold signature; rw [Fin.sum_univ_add]; simp

theorem pExcess_append (p : ℕ) (a : Fin m → ℤ) (b : Fin k → ℤ) :
    pExcess p (Fin.append a b) = pExcess p a + pExcess p b := by
  unfold pExcess; rw [Fin.sum_univ_add]; simp

/-- **The excesses are additive under orthogonal sum.** -/
theorem excess_append (v : RatPlace) (a : Fin m → ℤ) (b : Fin k → ℤ) :
    excess v (Fin.append a b) = excess v a + excess v b := by
  cases v with
  | infinite =>
    simp only [excess, negOneExcess, signature_append]; push_cast; ring
  | finite p =>
    simp only [excess]
    split_ifs
    · simp only [twoExcess, oddity_append]; push_cast; ring
    · exact pExcess_append _ a b

theorem four_mul_oddityEntry {x : ℤ} (hx : x ≠ 0) : 4 * oddityEntry x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu := intCast_zmod8_odd (by exact_mod_cast not_dvd_unitPart (p := 2) hx)
  unfold oddityEntry
  generalize ((unitPart 2 x : ℤ) : ZMod 8) = r at hu ⊢
  split_ifs <;> rcases hu with rfl | rfl | rfl | rfl <;> decide

theorem four_mul_sign {x : ℤ} (hx : x ≠ 0) : (4 : ZMod 8) * (Int.sign x : ZMod 8) = 4 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; decide
  · rw [Int.sign_eq_one_of_pos h]; decide

/-- **Every excess is even** (Conway–Sloane, §5.2, Remark (2), p. 373): $4 \cdot \text{excess} \equiv 0 \pmod 8$, at
every place, for a nonsingular diagonal form. -/
@[kb "conwaysloane1999" "Ch. 15, §5.2, Remark (2), p. 373 (all places)"]
theorem four_mul_excess (v : RatPlace) {n : ℕ} (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) : 4 * excess v a = 0 := by
  cases v with
  | infinite =>
    simp only [excess, negOneExcess, signature]
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl fun i _ => four_mul_sign (ha i)]
    simp; ring
  | finite p =>
    simp only [excess]
    split_ifs with hp2
    · simp only [twoExcess, oddity]
      rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl fun i _ => four_mul_oddityEntry (ha i)]
      simp; ring
    · have : Fact p.1.Prime := ⟨p.2⟩
      exact (pExcess_even p.1 hp2 a).1

/-- **(19), first claim** (Conway–Sloane, §6.2, p. 376): $f \oplus f \oplus f \oplus f$ has trivial invariants. -/
@[kb "conwaysloane1999" "Ch. 15, §6.2, (19), pp. 376–377"]
theorem trivialInvariants_four {n : ℕ} (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    TrivialInvariants (Fin.append (Fin.append (Fin.append a a) a) a) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [excess_append, excess_append, excess_append]
    have := four_mul_excess v a ha
    linear_combination this
  · refine ⟨((∏ i, a i : ℤ) : ℚ) ^ 2, ?_⟩
    rw [prod_append, prod_append, prod_append]
    push_cast; ring

/-- **(19), second claim** (Conway–Sloane, §6.2, pp. 376–377): if $f$, $g$ have the same invariants (the quotient of
the determinants is a square and all the excesses agree), then $g \oplus f \oplus f \oplus f$ has trivial invariants. -/
@[kb "conwaysloane1999" "Ch. 15, §6.2, (19), pp. 376–377"]
theorem trivialInvariants_mixed {n : ℕ} (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hsq : IsSquare (((∏ i, a i : ℤ) : ℚ) / ((∏ i, b i : ℤ) : ℚ))) (hex : ∀ v, excess v a = excess v b) :
    TrivialInvariants (Fin.append (Fin.append (Fin.append b a) a) a) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [excess_append, excess_append, excess_append, ← hex v]
    have := four_mul_excess v a ha
    linear_combination this
  · obtain ⟨r, hr⟩ := hsq
    have hA : ((∏ i, a i : ℤ) : ℚ) ≠ 0 := by exact_mod_cast prod_ne_zero_iff.mpr fun i _ => ha i
    have hB : ((∏ i, b i : ℤ) : ℚ) ≠ 0 := by exact_mod_cast prod_ne_zero_iff.mpr fun i _ => hb i
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hr
      exact (div_ne_zero hA hB) hr
    refine ⟨((∏ i, a i : ℤ) : ℚ) ^ 2 / r, ?_⟩
    rw [prod_append, prod_append, prod_append]
    push_cast
    have e : ((∏ i, b i : ℤ) : ℚ) = ((∏ i, a i : ℤ) : ℚ) / (r * r) := by
      rw [← hr]; field_simp
    push_cast at e
    rw [e]
    field_simp

end QuadFormsKB.ConwaySloane
