/-
# Sums of squares (Grosswald, *Representations of Integers as Sums of Squares*, 1985)

Statements in the form the literature gives them, over $\mathbb{N}$. Where Mathlib already has
the result, the proof cites the Mathlib lemma, so the registry records it as `proved` with a
pointer to where the real proof lives.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Classical.ThreeSquares

namespace QuadFormsKB.Grosswald

/-- **Fermat's two-squares theorem:** a prime $p \equiv 1 \pmod 4$ is a sum of two squares,
$p = a^2 + b^2$ with $a, b \in \mathbb{N}$. Proved by citing Mathlib's `Nat.Prime.sq_add_sq`. -/
@[kb "grosswald1985" "Ch. 2, Thm. 1"]
theorem fermat_two_squares (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq (by omega)

/-- **Sums of two squares (Euler, Gauss):** $n \in \mathbb{N}$ is a sum of two squares iff every
prime $q \equiv 3 \pmod 4$ divides $n$ to an even power, i.e. $v_q(n)$ is even. Proved by citing
Mathlib's `Nat.eq_sq_add_sq_iff`. -/
@[kb "grosswald1985" "Ch. 2, Thm. 3; cassels1978 Ch. 1, §1, p. 2 (Euler's criterion for two squares)"]
theorem two_squares_iff (n : ℕ) :
    (∃ x y, n = x ^ 2 + y ^ 2) ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) :=
  Nat.eq_sq_add_sq_iff

/-- **Lagrange's four-squares theorem:** every $n \in \mathbb{N}$ is $a^2 + b^2 + c^2 + d^2$ with
$a, b, c, d \in \mathbb{N}$. Proved by citing Mathlib's `Nat.sum_four_squares`. -/
@[kb "grosswald1985" "Ch. 3, Thm. 1; cassels1978 Ch. 1, §1, p. 2 (Lagrange's four squares)"]
theorem lagrange_four_squares (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

/-- **No $8k + 7$ is a sum of three squares:** $a^2 + b^2 + c^2 \ne 8k + 7$ for all
$a, b, c, k \in \mathbb{N}$, since squares are $0, 1, 4 \pmod 8$. -/
@[kb "grosswald1985" "Ch. 4, §1"]
theorem not_three_squares_eight_mul_add_seven (a b c k : ℕ) :
    a ^ 2 + b ^ 2 + c ^ 2 ≠ 8 * k + 7 := by
  intro h
  have hsq : ∀ x : ℕ, x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by
    intro x
    have : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
    rw [Nat.pow_mod]
    interval_cases x % 8 <;> simp
  rcases hsq a with ha|ha|ha <;> rcases hsq b with hb|hb|hb <;> rcases hsq c with hc|hc|hc <;> omega

/-- **No $4^a(8b + 7)$ is a sum of three squares:** $x_0^2 + x_1^2 + x_2^2 \ne 4^a (8b + 7)$ for all
$x_0, x_1, x_2, a, b \in \mathbb{N}$.

*Proof.* Induction on $a$. For $a = 0$ this is `not_three_squares_eight_mul_add_seven`. If
$x_0^2 + x_1^2 + x_2^2 \equiv 0 \pmod 4$, then every $x_i$ is even (squares are $0, 1 \bmod 4$), and
dividing by $4$ gives a representation of $4^{a-1}(8b + 7)$. -/
@[kb "grosswald1985" "Ch. 4, §1"]
theorem not_three_squares_four_pow_mul (a : ℕ) :
    ∀ x y z b : ℕ, x ^ 2 + y ^ 2 + z ^ 2 ≠ 4 ^ a * (8 * b + 7) := by
  induction a with
  | zero => intro x y z b; simpa using not_three_squares_eight_mul_add_seven x y z b
  | succ k ih =>
    intro x y z b h
    have hsq : ∀ t : ℕ, (t ^ 2 % 4 = 0 ∧ 2 ∣ t) ∨ t ^ 2 % 4 = 1 := by
      intro t
      rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
      · left; refine ⟨?_, dvd_mul_right 2 u⟩
        rw [show (2 * u) ^ 2 = 4 * u ^ 2 by ring]; exact Nat.mul_mod_right _ _
      · right
        rw [show (2 * u + 1) ^ 2 = 4 * (u ^ 2 + u) + 1 by ring, Nat.mul_add_mod]
    have h4 : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 := by
      rw [h, pow_succ, mul_comm (4 ^ k) 4, mul_assoc]; exact Nat.mul_mod_right _ _
    rcases hsq x with ⟨hx, ⟨x', rfl⟩⟩ | hx
    · rcases hsq y with ⟨hy, ⟨y', rfl⟩⟩ | hy
      · rcases hsq z with ⟨hz, ⟨z', rfl⟩⟩ | hz
        · apply ih x' y' z' b
          have h' : 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * (4 ^ k * (8 * b + 7)) := by
            rw [show 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = (2 * x') ^ 2 + (2 * y') ^ 2 + (2 * z') ^ 2 by ring,
              h]; ring
          exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
        · generalize (2 * x') ^ 2 = X at *; generalize (2 * y') ^ 2 = Y at *
          generalize z ^ 2 = Z at *; omega
      · generalize (2 * x') ^ 2 = X at *; generalize y ^ 2 = Y at *
        rcases hsq z with ⟨hz, -⟩ | hz <;> (generalize z ^ 2 = Z at *; omega)
    · generalize x ^ 2 = X at *
      rcases hsq y with ⟨hy, -⟩ | hy <;> rcases hsq z with ⟨hz, -⟩ | hz <;>
        (generalize y ^ 2 = Y at *; generalize z ^ 2 = Z at *; omega)

/-- **Legendre's three-squares theorem (Legendre, Gauss):** $n \in \mathbb{N}$ is a sum of three
squares iff $n$ is **not** of the form $4^a (8b + 7)$ with $a, b \in \mathbb{N}$. Not in Mathlib
v4.35.0.

*Proof.* The easy direction is `not_three_squares_four_pow_mul` (descent by $4$ from
`not_three_squares_eight_mul_add_seven`). The hard direction is
`QuadFormsKB.ThreeSquares.three_squares_of_not_form` (Serre, *A Course in Arithmetic*, Ch. IV,
Appendix): local representability at every place, Hasse–Minkowski over $\mathbb{Q}$
(`QuadFormsKB.represents_iff_everywhere`), then the Davenport–Cassels lemma
(`QuadFormsKB.DavenportCassels.davenport_cassels`). -/
@[kb "grosswald1985" "Ch. 4, Thm. 1; cassels1978 Ch. 1, §1, p. 2 (Legendre's three squares)"]
theorem legendre_three_squares (n : ℕ) :
    (∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n) ↔ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  refine ⟨?_, ThreeSquares.three_squares_of_not_form n⟩
  rintro ⟨x, y, z, h⟩ ⟨a, b, rfl⟩
  exact not_three_squares_four_pow_mul a x y z b h

end QuadFormsKB.Grosswald
