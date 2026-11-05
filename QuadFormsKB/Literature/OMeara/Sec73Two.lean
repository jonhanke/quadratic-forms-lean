/-
# O'Meara §73: Proposition 73:2, the 2-adic Hilbert symbol of odd integers

**Setting.** The Hilbert symbol over $\mathbb Q_p$ is `hilbertSymbol ℚ_[p]` with rational integers viewed in
$\mathbb Q_p$. O'Meara writes the exponents $\frac{a-1}{2}\cdot\frac{b-1}{2}$ and $\frac{b^2-1}{8}$; only their parity
matters, and the statement below is phrased with `Even`.

**Proves** Proposition 73:2 (p. 206): `hilbertSymbol_two_adic_of_odd`, from the library's 2-adic formula
`HilbertLocal.hilbertSymbol_two_formula`. Proposition 73:1 and Theorem 73:3 are in `Sec73.lean`.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity

set_option linter.unusedSectionVars false

namespace QuadFormsKB.OMeara

open QuadFormsKB.HilbertLocal in
private lemma exists_unit_of_int (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    ∃ u : ℤ_[p]ˣ, (u : ℤ_[p]) = (a : ℤ_[p]) := by
  have h1 : ‖(a : ℤ_[p])‖ = 1 := by
    have h2 : ¬ ‖(a : ℤ_[p])‖ < 1 := fun h => ha ((PadicInt.norm_int_lt_one_iff_dvd a).1 h)
    exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h2)
  exact ⟨(PadicInt.isUnit_iff.2 h1).unit, IsUnit.unit_spec _⟩

private lemma intCast_mod8 (a : ℤ) : (a : ZMod (2 ^ 3)) = ((a % 8 : ℤ) : ZMod (2 ^ 3)) := by
  have := (ZMod.intCast_mod a 8).symm
  simpa using this

private lemma twoEps_int (a : ℤ) (ha : Odd a) :
    HilbertLocal.twoEps (a : ZMod (2 ^ 3)) = if Even ((a - 1) / 2) then 0 else 1 := by
  rw [intCast_mod8]
  obtain ⟨m, hm⟩ := ha
  have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  rcases this with h | h | h | h <;> rw [h]
  · have e : HilbertLocal.twoEps (((1 : ℤ)) : ZMod (2 ^ 3)) = 0 := by decide
    rw [e]; split_ifs with hh
    · rfl
    · exfalso; apply hh; rw [Int.even_iff]; omega
  · have e : HilbertLocal.twoEps (((3 : ℤ)) : ZMod (2 ^ 3)) = 1 := by decide
    rw [e]; split_ifs with hh
    · exfalso; rw [Int.even_iff] at hh; omega
    · rfl
  · have e : HilbertLocal.twoEps (((5 : ℤ)) : ZMod (2 ^ 3)) = 0 := by decide
    rw [e]; split_ifs with hh
    · rfl
    · exfalso; apply hh; rw [Int.even_iff]; omega
  · have e : HilbertLocal.twoEps (((7 : ℤ)) : ZMod (2 ^ 3)) = 1 := by decide
    rw [e]; split_ifs with hh
    · exfalso; rw [Int.even_iff] at hh; omega
    · rfl

private lemma twoOmega_int (b : ℤ) (hb : Odd b) :
    HilbertLocal.twoOmega (b : ZMod (2 ^ 3)) = if Even ((b ^ 2 - 1) / 8) then 0 else 1 := by
  rw [intCast_mod8]
  obtain ⟨m, hm⟩ := hb
  have key : ∀ r : ℤ, b % 8 = r → ∀ c : ℤ, r ^ 2 - 1 = 8 * c →
      (b ^ 2 - 1) / 8 = 8 * (b / 8) ^ 2 + 2 * (b / 8) * r + c := by
    intro r hr c hc
    have hb8 : b = 8 * (b / 8) + r := by omega
    have : b ^ 2 - 1 = 8 * (8 * (b / 8) ^ 2 + 2 * (b / 8) * r + c) := by
      calc b ^ 2 - 1 = (8 * (b / 8) + r) ^ 2 - 1 := by rw [← hb8]
        _ = _ := by linear_combination hc
    rw [this]; omega
  have : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by omega
  rcases this with h | h | h | h
  · rw [key 1 h 0 (by norm_num), h]
    have e : HilbertLocal.twoOmega (((1 : ℤ)) : ZMod (2 ^ 3)) = 0 := by decide
    rw [e]; generalize (b / 8) ^ 2 = t; split_ifs with hh
    · rfl
    · exfalso; apply hh; rw [Int.even_iff]; omega
  · rw [key 3 h 1 (by norm_num), h]
    have e : HilbertLocal.twoOmega (((3 : ℤ)) : ZMod (2 ^ 3)) = 1 := by decide
    rw [e]; generalize (b / 8) ^ 2 = t; split_ifs with hh
    · exfalso; rw [Int.even_iff] at hh; omega
    · rfl
  · rw [key 5 h 3 (by norm_num), h]
    have e : HilbertLocal.twoOmega (((5 : ℤ)) : ZMod (2 ^ 3)) = 1 := by decide
    rw [e]; generalize (b / 8) ^ 2 = t; split_ifs with hh
    · exfalso; rw [Int.even_iff] at hh; omega
    · rfl
  · rw [key 7 h 6 (by norm_num), h]
    have e : HilbertLocal.twoOmega (((7 : ℤ)) : ZMod (2 ^ 3)) = 0 := by decide
    rw [e]; generalize (b / 8) ^ 2 = t; split_ifs with hh
    · rfl
    · exfalso; apply hh; rw [Int.even_iff]; omega

/-- **Proposition 73:2** (O'Meara 1963, p. 206): for odd rational integers $a$, $b$,
$\left(\frac{a, b}{2}\right) = (-1)^{\frac{a-1}{2}\cdot\frac{b-1}{2}}$ and
$\left(\frac{2, b}{2}\right) = (-1)^{\frac{b^2-1}{8}}$. -/
@[kb "omeara1963" "§73, 73:2, p. 206"]
theorem hilbertSymbol_two_adic_of_odd (a b : ℤ) (ha : Odd a) (hb : Odd b) :
    hilbertSymbol ℚ_[2] (a : ℚ_[2]) (b : ℚ_[2]) = (if Even ((a - 1) / 2 * ((b - 1) / 2)) then 1 else -1) ∧
      hilbertSymbol ℚ_[2] (2 : ℚ_[2]) (b : ℚ_[2]) = (if Even ((b ^ 2 - 1) / 8) then 1 else -1) := by
  obtain ⟨u, hu⟩ := exists_unit_of_int 2 a (by rintro ⟨k, hk⟩; obtain ⟨m, hm⟩ := ha; push_cast at hk; omega)
  obtain ⟨v, hv⟩ := exists_unit_of_int 2 b (by rintro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hb; push_cast at hk; omega)
  have hu' : ((u : ℤ_[2]) : ℚ_[2]) = (a : ℚ_[2]) := by rw [hu]; simp
  have hv' : ((v : ℤ_[2]) : ℚ_[2]) = (b : ℚ_[2]) := by rw [hv]; simp
  have hua : PadicInt.toZModPow 3 (u : ℤ_[2]) = (a : ZMod (2 ^ 3)) := by rw [hu]; simp
  have hvb : PadicInt.toZModPow 3 (v : ℤ_[2]) = (b : ZMod (2 ^ 3)) := by rw [hv]; simp
  refine ⟨?_, ?_⟩
  · have := HilbertLocal.hilbertSymbol_two_formula 0 0 u v
    simp only [pow_zero, one_mul, zero_mul, mul_zero, add_zero] at this
    rw [← hu', ← hv', this, hua, hvb, twoEps_int a ha, twoEps_int b hb]
    by_cases hA : Even ((a - 1) / 2) <;> by_cases hB : Even ((b - 1) / 2) <;> simp [Int.even_mul, hA, hB]
  · have := HilbertLocal.hilbertSymbol_two_formula 1 0 1 v
    have h2 : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_num
    simp only [pow_zero, one_mul, zero_mul, mul_zero, add_zero, pow_one, Units.val_one,
      PadicInt.coe_one, Nat.cast_one, mul_one, map_one] at this
    rw [← hv', this, hvb, twoOmega_int b hb]
    have e : HilbertLocal.twoEps (1 : ZMod (2 ^ 3)) = 0 := by decide
    rw [e]
    split_ifs <;> simp

end QuadFormsKB.OMeara
