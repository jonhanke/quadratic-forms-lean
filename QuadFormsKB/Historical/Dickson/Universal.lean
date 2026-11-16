/-
# Universal diagonal ternary forms (Dickson, *Studies*, 1930)

**Library** `QuadFormsKB.Historical.Dickson` (historical library, not imported by `QuadFormsKB`).  Target
:

* (Dickson, *Studies in the Theory of Numbers* (1930), ch. II): the form $ax^2 + by^2 + cz^2$ (nonzero integers $a, b, c$) is universal, i.e.
  represents every integer (positive, negative and $0$), iff
  (I) $a, b, c$ are not all of one sign;
  (II) no two of $a, b, c$ have a common odd prime factor;
  (III) $abc$ is odd or twice an odd number;
  (IV) $-bc$, $-ca$, $-ab$ are quadratic residues modulo $a$, $b$, $c$ respectively.
  **Stated** as `DicksonUniversalDiagonalTernary` (a named proposition, not used as a hypothesis anywhere). The
  necessity of (I) and (II) is **proved** (`not_all_pos_of_universal`, `not_all_neg_of_universal`,
  `no_common_odd_prime_of_universal`); the necessity of (III) and (IV) and the sufficiency are not (loose end: they
  need the $2$-adic analysis and Dickson's construction via Legendre's theorem).

A numerical check (all $a, b, c$ with $\lvert a\rvert, \lvert b\rvert, \lvert c\rvert \le 10$, all $n$ with
$\lvert n\rvert \le 120$) agrees with the statement.
-/
import Mathlib.FieldTheory.Finite.Basic
import QuadFormsKB.Citation

namespace QuadFormsKB.Historical.Dickson

/-- The form $ax^2 + by^2 + cz^2$ is **universal** over $\mathbb Z$: it represents every integer. -/
def IsUniversalDiag3 (a b c : ℤ) : Prop :=
  ∀ n : ℤ, ∃ x y z : ℤ, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = n

/-- Dickson's conditions (I)–(IV) on $(a, b, c)$. -/
def DicksonUniversalConditions (a b c : ℤ) : Prop :=
  -- (I) not all of one sign
  ¬ (0 < a ∧ 0 < b ∧ 0 < c) ∧ ¬ (a < 0 ∧ b < 0 ∧ c < 0) ∧
  -- (II) no two coefficients share an odd prime factor
  (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b) ∧ ¬ ((p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) ∧
      ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ c)) ∧
  -- (III) abc odd or twice an odd number
  (Odd (a * b * c) ∨ a * b * c % 4 = 2) ∧
  -- (IV) -bc, -ca, -ab quadratic residues modulo a, b, c
  IsSquare ((-(b * c) : ℤ) : ZMod a.natAbs) ∧ IsSquare ((-(c * a) : ℤ) : ZMod b.natAbs) ∧
    IsSquare ((-(a * b) : ℤ) : ZMod c.natAbs)

/-- (Dickson, *Studies* (1930)), **Dickson's
classification of universal diagonal ternary forms**: for nonzero integers $a, b, c$, $ax^2 + by^2 + cz^2$ represents
every integer iff conditions (I)–(IV) hold. **Stated**, not proved. -/
@[kb "dickson1930" "[unverified locator]"]
def DicksonUniversalDiagonalTernary : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → (IsUniversalDiag3 a b c ↔ DicksonUniversalConditions a b c)

private theorem core_no_common {a b c : ℤ} (h : IsUniversalDiag3 a b c) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : (p : ℤ) ∣ a) (hb : (p : ℤ) ∣ b) : False := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hc : (p : ℤ) ∣ c
  · obtain ⟨x, y, z, hxyz⟩ := h 1
    have : (p : ℤ) ∣ 1 := by
      rw [← hxyz]
      exact dvd_add (dvd_add (ha.mul_right _) (hb.mul_right _)) (hc.mul_right _)
    have := Int.eq_one_of_dvd_one (by positivity) this
    exact hp.ne_one (by exact_mod_cast this)
  · have hc' : (c : ZMod p) ≠ 0 := fun hh => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hh)
    have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hchar
    obtain ⟨x, y, z, hxyz⟩ := h ((c : ℤ) * (g.val : ℤ))
    have h1 := congrArg (Int.cast : ℤ → ZMod p) hxyz
    push_cast at h1
    rw [ZMod.natCast_zmod_val] at h1
    have ha' : ((a : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 ha
    have hb' : ((b : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hb
    rw [ha', hb'] at h1
    apply hg
    refine ⟨z, ?_⟩
    apply mul_left_cancel₀ hc'
    linear_combination -h1

private theorem universal_perm_cab {a b c : ℤ} (h : IsUniversalDiag3 a b c) : IsUniversalDiag3 b c a := by
  intro n
  obtain ⟨x, y, z, hh⟩ := h n
  exact ⟨y, z, x, by linarith⟩

private theorem universal_perm_acb {a b c : ℤ} (h : IsUniversalDiag3 a b c) : IsUniversalDiag3 a c b := by
  intro n
  obtain ⟨x, y, z, hh⟩ := h n
  exact ⟨x, z, y, by linarith⟩

/-- necessity of (I), positive half: a universal diagonal ternary form is not positive definite. -/
@[kb "dickson1930" "[unverified locator]"]
theorem not_all_pos_of_universal (a b c : ℤ) (h : IsUniversalDiag3 a b c) : ¬ (0 < a ∧ 0 < b ∧ 0 < c) := by
  rintro ⟨ha, hb, hc⟩
  obtain ⟨x, y, z, hxyz⟩ := h (-1)
  nlinarith [mul_nonneg ha.le (sq_nonneg x), mul_nonneg hb.le (sq_nonneg y), mul_nonneg hc.le (sq_nonneg z)]

/-- necessity of (I), negative half: a universal diagonal ternary form is not negative definite. -/
@[kb "dickson1930" "[unverified locator]"]
theorem not_all_neg_of_universal (a b c : ℤ) (h : IsUniversalDiag3 a b c) : ¬ (a < 0 ∧ b < 0 ∧ c < 0) := by
  rintro ⟨ha, hb, hc⟩
  obtain ⟨x, y, z, hxyz⟩ := h 1
  nlinarith [mul_nonneg (neg_nonneg.2 ha.le) (sq_nonneg x), mul_nonneg (neg_nonneg.2 hb.le) (sq_nonneg y),
    mul_nonneg (neg_nonneg.2 hc.le) (sq_nonneg z)]

/-- necessity of (II): if $ax^2 + by^2 + cz^2$ is universal, no odd prime divides two of $a, b, c$
(if $p \mid a, b$, every value is $\equiv cz^2 \pmod p$, so $c$ times a nonresidue is missed). -/
@[kb "dickson1930" "[unverified locator]"]
theorem no_common_odd_prime_of_universal (a b c : ℤ) (h : IsUniversalDiag3 a b c) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b) ∧ ¬ ((p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) ∧ ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ c) := by
  refine ⟨fun ⟨h1, h2⟩ => core_no_common h hp hp2 h1 h2,
    fun ⟨h1, h2⟩ => core_no_common (universal_perm_cab h) hp hp2 h1 h2,
    fun ⟨h1, h2⟩ => core_no_common (universal_perm_acb h) hp hp2 h1 h2⟩

end QuadFormsKB.Historical.Dickson
