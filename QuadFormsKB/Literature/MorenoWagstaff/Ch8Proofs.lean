/-
# Moreno–Wagstaff 2005, Chapter 8: proofs

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Chapter 8.

**Proves**
* `theorem85` (Theorem 8.5, **proved**): $w^2 + \delta = 2n - (x^2 + \delta) \equiv -(x^2+\delta)$ and likewise for
  $y, z$, so the two products agree mod $n$ (the book's one-line computation).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Statements

namespace QuadFormsKB.MorenoWagstaff

/-- **Moreno–Wagstaff, Theorem 8.5** (p. 339), proved: since $w^2 + \delta = 2n - (x^2 + \delta)$ and
$y^2 + \delta = 2n - (z^2 + \delta)$, the product $(w^2+\delta)(y^2+\delta)$ differs from $(x^2+\delta)(z^2+\delta)$ by a
multiple of $n$. -/
@[kb "morenowagstaff2005" "Theorem 8.5, p. 339"]
theorem theorem85 : Theorem85 := by
  intro n δ w x y z h1 h2
  have hw : w ^ 2 + δ = 2 * n - (x ^ 2 + δ) := by linarith
  have hy : y ^ 2 + δ = 2 * n - (z ^ 2 + δ) := by linarith
  have key : ∀ a : ℤ, a % n ≡ a [ZMOD n] := fun a => Int.mod_modEq a n
  calc (w ^ 2 + δ) % n * ((y ^ 2 + δ) % n) ≡ (w ^ 2 + δ) * (y ^ 2 + δ) [ZMOD n] := (key _).mul (key _)
    _ = (x ^ 2 + δ) * (z ^ 2 + δ) + n * (4 * n - 2 * (x ^ 2 + δ) - 2 * (z ^ 2 + δ)) := by
        rw [hw, hy]; ring
    _ ≡ (x ^ 2 + δ) * (z ^ 2 + δ) + 0 [ZMOD n] :=
        Int.ModEq.add_left _ ((Int.modEq_zero_iff_dvd).2 (dvd_mul_right _ _))
    _ = (x ^ 2 + δ) * (z ^ 2 + δ) := by ring
    _ ≡ (x ^ 2 + δ) % n * ((z ^ 2 + δ) % n) [ZMOD n] := ((key _).mul (key _)).symm

end QuadFormsKB.MorenoWagstaff
