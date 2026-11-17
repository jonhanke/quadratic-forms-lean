/-
# Ramanujan, *Collected Papers* (1927): further ternary laws, $x^2 + y^2 + z^2 + nu^2$, and Liouville's forms

**Library** `QuadFormsKB.Historical.Ramanujan` (historical library, not imported by `QuadFormsKB`).  Targets
, all from Ramanujan, *On the
expression of a number in the form $ax^2 + by^2 + cz^2 + du^2$*, Proc. Cambridge Philos. Soc. 19 (1917), 11–21,
*Collected Papers* (1927), No. 20:

* (§ 3, p. 172): six further ternary laws. A number $N \ge 0$ is **not** of the form
  * $x^2 + y^2 + 4z^2$ exactly when $N = 4^\lambda(8\mu + 7)$ or $N = 8\mu + 3$: `ternary_114`, **proved**;
  * $x^2 + y^2 + 8z^2$ exactly when $N = 4^\lambda(16\mu + 14)$, $16\mu + 6$ or $4\mu + 3$: `ternary_118`, **proved**;
  * $x^2 + 2y^2 + 8z^2$ exactly when $N = 4^\lambda(8\mu + 7)$ or $8\mu + 5$: `ternary_128`, **proved**;
  * $x^2 + y^2 + 5z^2$ exactly when $N = 4^\lambda(8\mu + 3)$: `Ternary115`, **stated**; the "not represented" half
    `not_rep_115_of_exc` **proved**;
  * $x^2 + y^2 + 6z^2$ exactly when $N = 9^\lambda(9\mu + 3)$: `Ternary116`, **stated**; `not_rep_116_of_exc`
    **proved**;
  * $x^2 + 2y^2 + 6z^2$ exactly when $N = 4^\lambda(8\mu + 5)$: `Ternary126`, **stated**; `not_rep_126_of_exc`
    **proved**.

  The first three follow from Legendre's three-squares theorem (through `ternary_111`, `ternary_112` of
  `Ternary.lean`); the last three, like `Ternary113`, `Ternary123`, `Ternary125`, need the one-class-in-the-genus
  property of the form and are out of reach here (see `Ternary.lean`).
* (§ 3, footnote, p. 172): the even numbers not of the form $x^2 + y^2 + 10z^2$ are exactly
  $4^\lambda(16\mu + 6)$. *Partial:* `rep_1_1_10_two_mul_iff` (**proved**: $2M$ is represented by $x^2 + y^2 + 10z^2$ iff
  $M$ is represented by $x^2 + y^2 + 5z^2$), `not_rep_1_1_10_of_exc` (the exceptions are not represented,
  **proved**) and `even_rep_1_1_10_of_ternary115` (the law for even numbers, **proved conditional on** the stated
  `Ternary115`). The odd exceptions $3, 7, 21, 31, 33, 43, 67, 79, 87, 133, 217, 219, 223, 253, 307, 391$ that Ramanujan
  lists (and for which he saw no law) are not formalized.
* (§§ 6.1, 6.5 (i), 6.6 (i)): $x^2 + y^2 + z^2 + nu^2$ has infinitely many exceptions when
  $n \equiv 0 \pmod 8$ (every $N \equiv 7 \bmod 8$ is missed: `quaternary_exc_zero_mod_eight`), when $n \equiv 1 \pmod 8$,
  $n \ge 33$, and when $n \equiv 4 \pmod{32}$, $n \ge 132$ (every $7 \cdot 4^\lambda$ is missed, for **all** $\lambda \ge 0$,
  not only for $\lambda$ large: `quaternary_exc_one_mod_eight`, `quaternary_exc_four_mod_32`). **Proved.**
* (§ 5): $x^2 + y^2 + z^2 + nu^2$ ($n \ge 1$) represents all integers from $4n$ on, and all but
  finitely many integers, exactly when $n \in \{1, 4, 9, 17, 25, 36, 68, 100\}$ or $n \equiv 2, 3 \pmod 4$,
  $n \equiv 5 \pmod 8$, $n \equiv 12 \pmod{16}$ or $n \equiv 20 \pmod{32}$ (`RamanujanGoodN`); and
  $m(x^2 + y^2 + z^2) + nu^2$ with $m \ge 3$ misses a whole residue class modulo $m$.
  *Partial:* the necessity `good_of_eventually_rep` (finitely many exceptions $\Rightarrow$ `RamanujanGoodN`) and the
  statement about $m \ge 3$ (`exists_residue_not_rep_of_three_le`) are **proved**; the sufficiency
  (`RamanujanSection5Sufficiency`) is **stated** (Ramanujan's proof uses the ternary laws of § 3 and a case analysis
  on $n$ modulo $32$; the cases $n \equiv 3 \bmod 4$ etc. need laws stated, not proved, here).
* (No. 20, § 2, footnote; *Collected Papers* p. 170): twelve of the universal forms had been treated
  by Liouville and Pepin: $(1,1,1,2)$, $(1,1,1,4)$, $(1,1,2,2)$, $(1,2,2,2)$, $(1,1,2,4)$, $(1,2,2,4)$, $(1,2,4,4)$,
  $(1,1,2,8)$, $(1,2,4,8)$, $(1,1,3,3)$, $(1,2,3,6)$, $(1,2,5,10)$. `liouville_pepin_universal`: **proved** for the ten
  forms other than $(1,1,3,3)$ and $(1,2,5,10)$ (**wrapper** of `universal_of_ramanujanList` and `universal_1236`);
  those two are among the 15 forms of `RamanujanRemaining` (`liouville_pepin_universal_of_remaining`, **proved
  conditional on** the stated `RamanujanRemaining`). Liouville's and Pepin's representation-number formulas themselves
  are not part of the row.

**Conventions.** $\lambda, \mu \ge 0$; all variables range over $\mathbb Z$; `Rep3 a b c N` and `Rep4 a b c d N` are the
representation predicates of `Ternary.lean` and `Quaternary.lean`; `IsExc q r s N` means $N = q^\lambda(r\mu + s)$.
-/
import QuadFormsKB.Historical.Ramanujan.Quaternary

namespace QuadFormsKB.Historical.Ramanujan

/-! ### Private helper lemmas -/

private theorem sq8b (x : ℤ) (h : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

private theorem sq8c (x : ℤ) (h : x % 2 = 0) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4 := by
  have : x % 8 = 0 ∨ x % 8 = 2 ∨ x % 8 = 4 ∨ x % 8 = 6 := by omega
  rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- Squares modulo 8, with the parity of the base. -/
private theorem sq8 (x : ℤ) :
    (x % 2 = 0 ∧ (x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4)) ∨ (x % 2 = 1 ∧ x ^ 2 % 8 = 1) := by
  by_cases hx : x % 2 = 0
  · exact Or.inl ⟨hx, sq8c x hx⟩
  · exact Or.inr ⟨by omega, sq8b x (by omega)⟩

/-- Squares modulo 9, with divisibility of the base by 3. -/
private theorem sq9 (x : ℤ) :
    (x % 3 = 0 ∧ x ^ 2 % 9 = 0) ∨ (x % 3 ≠ 0 ∧ (x ^ 2 % 9 = 1 ∨ x ^ 2 % 9 = 4 ∨ x ^ 2 % 9 = 7)) := by
  have : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨
      x % 9 = 8 := by omega
  rcases this with h | h | h | h | h | h | h | h | h <;>
    first
    | (left; exact ⟨by omega, by simp [pow_two, Int.mul_emod, h]⟩)
    | (right; exact ⟨by omega, by simp [pow_two, Int.mul_emod, h]⟩)

private theorem no115 (l m : ℕ) : ∀ x y z : ℤ, x ^ 2 + y ^ 2 + 5 * z ^ 2 = 4 ^ l * (8 * m + 3) → False := by
  induction l with
  | zero =>
    intro x y z h
    rw [pow_zero, one_mul] at h
    have := sq8 x
    have := sq8 y
    have := sq8 z
    omega
  | succ l ih =>
    intro x y z h
    have h' : x ^ 2 + y ^ 2 + 5 * z ^ 2 = 4 * (4 ^ l * (8 * m + 3)) := by rw [h]; ring
    have := sq8 x
    have := sq8 y
    have := sq8 z
    obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, z = 2 * c := ⟨z / 2, by omega⟩
    exact ih a b c (by linarith)

private theorem no116 (l m : ℕ) : ∀ x y z : ℤ, x ^ 2 + y ^ 2 + 6 * z ^ 2 = 9 ^ l * (9 * m + 3) → False := by
  induction l with
  | zero =>
    intro x y z h
    rw [pow_zero, one_mul] at h
    have := sq9 x
    have := sq9 y
    have := sq9 z
    omega
  | succ l ih =>
    intro x y z h
    have h' : x ^ 2 + y ^ 2 + 6 * z ^ 2 = 9 * (9 ^ l * (9 * m + 3)) := by rw [h]; ring
    have := sq9 x
    have := sq9 y
    have := sq9 z
    obtain ⟨a, rfl⟩ : ∃ a, x = 3 * a := ⟨x / 3, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = 3 * b := ⟨y / 3, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, z = 3 * c := ⟨z / 3, by omega⟩
    exact ih a b c (by linarith)

private theorem no126 (l m : ℕ) : ∀ x y z : ℤ, x ^ 2 + 2 * y ^ 2 + 6 * z ^ 2 = 4 ^ l * (8 * m + 5) → False := by
  induction l with
  | zero =>
    intro x y z h
    rw [pow_zero, one_mul] at h
    have := sq8 x
    have := sq8 y
    have := sq8 z
    omega
  | succ l ih =>
    intro x y z h
    have h' : x ^ 2 + 2 * y ^ 2 + 6 * z ^ 2 = 4 * (4 ^ l * (8 * m + 5)) := by rw [h]; ring
    have hK : (4 : ℤ) ^ l * (8 * m + 5) % 4 = 0 ∨ (4 : ℤ) ^ l * (8 * m + 5) % 4 = 1 := by
      rcases l with _ | l
      · rw [pow_zero, one_mul]; omega
      · have : (4 : ℤ) ^ (l + 1) * (8 * m + 5) = 4 * (4 ^ l * (8 * m + 5)) := by ring
        rw [this]; omega
    have sx := sq8 x
    have sy := sq8 y
    have sz := sq8 z
    obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
    have hx2 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
    have sa := sq8 a
    have hyz : y % 2 = 0 ∧ z % 2 = 0 := by omega
    obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, z = 2 * c := ⟨z / 2, by omega⟩
    exact ih a b c (by linarith)

private theorem exc_half_1_16_6 (k : ℕ) : IsExc 4 16 6 (2 * k) ↔ IsExc 4 8 3 k := by
  constructor
  · rintro ⟨l, m, h⟩
    exact ⟨l, m, by linarith⟩
  · rintro ⟨l, m, h⟩
    exact ⟨l, m, by linarith⟩

private theorem rep4_int {n N : ℕ} (h : Rep4 1 1 1 n N) :
    ∃ x y z u : ℤ, x ^ 2 + y ^ 2 + z ^ 2 + (n : ℤ) * u ^ 2 = N := by
  obtain ⟨x, y, z, u, h⟩ := h
  exact ⟨x, y, z, u, by push_cast at h; linarith⟩

private theorem u_zero {n : ℕ} {B : ℤ} (hB : B < n) (x y z u : ℤ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 + (n : ℤ) * u ^ 2 = B) : u = 0 ∧ x ^ 2 + y ^ 2 + z ^ 2 = B := by
  have hu : u = 0 := by
    by_contra hu
    have h1 : 1 ≤ u ^ 2 := by
      have := sq_pos_of_ne_zero hu
      omega
    have h2 : (n : ℤ) * 1 ≤ n * u ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  subst hu
  exact ⟨rfl, by linarith⟩

private theorem exc1_aux {n : ℕ} (hn : n % 8 = 1) (h33 : 33 ≤ n) :
    ∀ l : ℕ, ∀ x y z u : ℤ, x ^ 2 + y ^ 2 + z ^ 2 + (n : ℤ) * u ^ 2 = 7 * 4 ^ l → False := by
  have hn33 : (33 : ℤ) ≤ n := by exact_mod_cast h33
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro x y z u h
    rcases l with _ | _ | l
    · norm_num at h
      obtain ⟨-, h3⟩ := u_zero (B := 7) (by linarith) x y z u h
      exact (ternary_111 7).1 ⟨x, y, z, by push_cast; linarith⟩ ⟨0, 0, by norm_num⟩
    · norm_num at h
      obtain ⟨-, h3⟩ := u_zero (B := 28) (by linarith) x y z u h
      exact (ternary_111 28).1 ⟨x, y, z, by push_cast; linarith⟩ ⟨1, 0, by norm_num⟩
    · have e : (7 : ℤ) * 4 ^ (l + 2) = 16 * (7 * 4 ^ l) := by ring
      rw [e] at h
      obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 8 * k + 1 := ⟨n / 8, by omega⟩
      have hnk : (n : ℤ) * u ^ 2 = u ^ 2 + 8 * ((k : ℤ) * u ^ 2) := by rw [hk]; push_cast; ring
      have sx := sq8 x
      have sy := sq8 y
      have sz := sq8 z
      have su := sq8 u
      have hall : x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 ∧ u % 2 = 0 := by omega
      obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
      obtain ⟨c, rfl⟩ : ∃ c, z = 2 * c := ⟨z / 2, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, u = 2 * d := ⟨u / 2, by omega⟩
      have e2 : (7 : ℤ) * 4 ^ (l + 1) = 4 * (7 * 4 ^ l) := by ring
      exact ih (l + 1) (by omega) a b c d (by rw [e2]; linarith)

/-! ### Six further ternary laws -/

/-- **$x^2 + y^2 + 4z^2$**: $N$ is represented iff $N$ is neither
$4^\lambda(8\mu + 7)$ nor $\equiv 3 \pmod 8$. **Proved** (from the three-squares theorem). -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
theorem ternary_114 (N : ℕ) : Rep3 1 1 4 N ↔ ¬ (IsExc 4 8 7 N ∨ N % 8 = 3) := by
  constructor
  · rintro ⟨x, y, z, h⟩ hc
    push_cast at h
    rcases hc with hc | hc
    · exact (ternary_111 N).1 ⟨x, y, 2 * z, by push_cast; linarith⟩ hc
    · have := sq8 x
      have := sq8 y
      have := sq8 z
      omega
  · intro hN
    have h1 : Rep3 1 1 1 N := (ternary_111 N).2 (fun h => hN (Or.inl h))
    have h3 : N % 8 ≠ 3 := fun h => hN (Or.inr h)
    obtain ⟨a, b, c, h⟩ := h1
    push_cast at h
    have := sq8 a
    have := sq8 b
    have := sq8 c
    have hev : a % 2 = 0 ∨ b % 2 = 0 ∨ c % 2 = 0 := by omega
    rcases hev with he | he | he
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
      exact ⟨b, c, k, by push_cast; linarith⟩
    · obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
      exact ⟨a, c, k, by push_cast; linarith⟩
    · obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k := ⟨c / 2, by omega⟩
      exact ⟨a, b, k, by push_cast; linarith⟩

/-- **$x^2 + y^2 + 8z^2$**: $N$ is represented iff $N$ is neither
$4^\lambda(16\mu + 14)$ nor $\equiv 6 \pmod{16}$ nor $\equiv 3 \pmod 4$. **Proved** (from the three-squares theorem). -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
theorem ternary_118 (N : ℕ) : Rep3 1 1 8 N ↔ ¬ (IsExc 4 16 14 N ∨ N % 16 = 6 ∨ N % 4 = 3) := by
  constructor
  · rintro ⟨x, y, z, h⟩ hc
    push_cast at h
    have sx := sq8 x
    have sy := sq8 y
    rcases hc with ⟨l, m, hc⟩ | hc | hc
    · rcases l with _ | l
      · rw [pow_zero, one_mul] at hc
        omega
      · have hK : N = 4 * (4 ^ l * (16 * m + 14)) := by rw [hc]; ring
        have hN : (N : ℤ) = 4 * (4 ^ l * (16 * m + 14)) := by rw [hK]; push_cast; ring
        obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
        exact (ternary_112 (4 ^ l * (16 * m + 14))).1 ⟨a, b, z, by push_cast; linarith⟩ ⟨l, m, rfl⟩
    · omega
    · omega
  · intro hN
    have hA : ¬ IsExc 4 16 14 N := fun h => hN (Or.inl h)
    have hB : N % 16 ≠ 6 := fun h => hN (Or.inr (Or.inl h))
    have hC : N % 4 ≠ 3 := fun h => hN (Or.inr (Or.inr h))
    have hmod : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · obtain ⟨K, hK⟩ : ∃ K, N = 4 * K := ⟨N / 4, by omega⟩
      have hKe : ¬ IsExc 4 16 14 K := by
        rintro ⟨l, m, h⟩
        exact hA ⟨l + 1, m, by rw [hK, h]; ring⟩
      obtain ⟨x, y, z, h⟩ := (ternary_112 K).2 hKe
      push_cast at h
      exact ⟨2 * x, 2 * y, z, by rw [hK]; push_cast; linarith⟩
    · obtain ⟨x, y, w, h⟩ := (ternary_112 N).2 hA
      push_cast at h
      have sx := sq8 x
      have sy := sq8 y
      have sw := sq8 w
      obtain ⟨k, rfl⟩ : ∃ k, w = 2 * k := ⟨w / 2, by omega⟩
      exact ⟨x, y, k, by push_cast; linarith⟩
    · have h8 : N % 8 = 2 := by
        by_contra h8
        have : N % 16 = 14 := by omega
        exact hA ⟨0, N / 16, by rw [pow_zero, one_mul]; omega⟩
      obtain ⟨M, hM⟩ : ∃ M, N = 2 * M := ⟨N / 2, by omega⟩
      have hM4 : M % 4 = 1 := by omega
      have hMe : ¬ IsExc 4 8 7 M := by
        rintro ⟨l, m, h⟩
        rcases l with _ | l
        · rw [pow_zero, one_mul] at h
          omega
        · have : M = 4 * (4 ^ l * (8 * m + 7)) := by rw [h]; ring
          omega
      obtain ⟨a, b, c, h⟩ := (ternary_111 M).2 hMe
      push_cast at h
      have sa := sq8 a
      have sb := sq8 b
      have sc := sq8 c
      have hev : a % 2 = 0 ∨ b % 2 = 0 ∨ c % 2 = 0 := by omega
      rcases hev with he | he | he
      · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
        exact ⟨b + c, b - c, k, by rw [hM]; push_cast; linarith⟩
      · obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
        exact ⟨a + c, a - c, k, by rw [hM]; push_cast; linarith⟩
      · obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k := ⟨c / 2, by omega⟩
        exact ⟨a + b, a - b, k, by rw [hM]; push_cast; linarith⟩

/-- **$x^2 + 2y^2 + 8z^2$**: $N$ is represented iff $N$ is neither
$4^\lambda(8\mu + 7)$ nor $\equiv 5 \pmod 8$. **Proved** (from the three-squares theorem). -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
theorem ternary_128 (N : ℕ) : Rep3 1 2 8 N ↔ ¬ (IsExc 4 8 7 N ∨ N % 8 = 5) := by
  constructor
  · rintro ⟨x, y, z, h⟩ hc
    push_cast at h
    rcases hc with hc | hc
    · exact (ternary_122 N).1 ⟨x, y, 2 * z, by push_cast; linarith⟩ hc
    · have := sq8 x
      have := sq8 y
      omega
  · intro hN
    have hA : ¬ IsExc 4 8 7 N := fun h => hN (Or.inl h)
    have hB : N % 8 ≠ 5 := fun h => hN (Or.inr h)
    by_cases h4 : N % 4 = 0
    · obtain ⟨K, hK⟩ : ∃ K, N = 4 * K := ⟨N / 4, by omega⟩
      have hKe : ¬ IsExc 4 8 7 K := by
        rintro ⟨l, m, h⟩
        exact hA ⟨l + 1, m, by rw [hK, h]; ring⟩
      obtain ⟨x, y, z, h⟩ := (ternary_122 K).2 hKe
      push_cast at h
      exact ⟨2 * x, 2 * y, z, by rw [hK]; push_cast; linarith⟩
    · obtain ⟨x, y, w, h⟩ := (ternary_122 N).2 hA
      push_cast at h
      have sx := sq8 x
      have sy := sq8 y
      have sw := sq8 w
      have hev : y % 2 = 0 ∨ w % 2 = 0 := by omega
      rcases hev with he | he
      · obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
        exact ⟨x, w, k, by push_cast; linarith⟩
      · obtain ⟨k, rfl⟩ : ∃ k, w = 2 * k := ⟨w / 2, by omega⟩
        exact ⟨x, y, k, by push_cast; linarith⟩

/-- **$x^2 + y^2 + 5z^2$**: $N$ is represented iff $N \ne 4^\lambda(8\mu + 3)$.
**Stated** (the form is alone in its genus; the sufficiency needs that, as for `Ternary113`). The necessity is
`not_rep_115_of_exc`. -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
def Ternary115 : Prop := ∀ N : ℕ, Rep3 1 1 5 N ↔ ¬ IsExc 4 8 3 N

/-- **$x^2 + y^2 + 6z^2$**: $N$ is represented iff $N \ne 9^\lambda(9\mu + 3)$.
**Stated**; the necessity is `not_rep_116_of_exc`. -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
def Ternary116 : Prop := ∀ N : ℕ, Rep3 1 1 6 N ↔ ¬ IsExc 9 9 3 N

/-- **$x^2 + 2y^2 + 6z^2$**: $N$ is represented iff $N \ne 4^\lambda(8\mu + 5)$.
**Stated**; the necessity is `not_rep_126_of_exc`. -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
def Ternary126 : Prop := ∀ N : ℕ, Rep3 1 2 6 N ↔ ¬ IsExc 4 8 5 N

/-- The numbers $4^\lambda(8\mu + 3)$ are not of the form $x^2 + y^2 + 5z^2$ (half of `Ternary115`). **Proved.** -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
theorem not_rep_115_of_exc {N : ℕ} (h : IsExc 4 8 3 N) : ¬ Rep3 1 1 5 N := by
  obtain ⟨l, m, rfl⟩ := h
  rintro ⟨x, y, z, h⟩
  push_cast at h
  exact no115 l m x y z (by linarith)

/-- The numbers $9^\lambda(9\mu + 3)$ are not of the form $x^2 + y^2 + 6z^2$ (half of `Ternary116`). **Proved.** -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
theorem not_rep_116_of_exc {N : ℕ} (h : IsExc 9 9 3 N) : ¬ Rep3 1 1 6 N := by
  obtain ⟨l, m, rfl⟩ := h
  rintro ⟨x, y, z, h⟩
  push_cast at h
  exact no116 l m x y z (by linarith)

/-- The numbers $4^\lambda(8\mu + 5)$ are not of the form $x^2 + 2y^2 + 6z^2$ (half of `Ternary126`). **Proved.** -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.further)"]
theorem not_rep_126_of_exc {N : ℕ} (h : IsExc 4 8 5 N) : ¬ Rep3 1 2 6 N := by
  obtain ⟨l, m, rfl⟩ := h
  rintro ⟨x, y, z, h⟩
  push_cast at h
  exact no126 l m x y z (by linarith)

/-! ### $x^2 + y^2 + 10z^2$ -/

/-- $2M = x^2 + y^2 + 10z^2$ is solvable iff $M = x^2 + y^2 + 5z^2$ is ($x \equiv y \bmod 2$ and
$(x+y)^2 + (x-y)^2 = 2(x^2+y^2)$). **Proved.** -/
theorem rep_1_1_10_two_mul_iff (M : ℕ) : Rep3 1 1 10 (2 * M) ↔ Rep3 1 1 5 M := by
  constructor
  · rintro ⟨x, y, z, h⟩
    push_cast at h
    have sx := sq8 x
    have sy := sq8 y
    have hxy : (x + y) % 2 = 0 := by omega
    obtain ⟨p, hp⟩ : ∃ p, x + y = 2 * p := ⟨(x + y) / 2, by omega⟩
    have hy : y = 2 * p - x := by omega
    subst hy
    exact ⟨p, x - p, z, by push_cast; linarith⟩
  · rintro ⟨a, b, c, h⟩
    push_cast at h
    exact ⟨a + b, a - b, c, by push_cast; linarith⟩

/-- The even numbers $4^\lambda(16\mu + 6)$ are not of the form $x^2 + y^2 + 10z^2$ (the historical sources,
the "not represented" half). **Proved.** -/
@[kb "ramanujan1917" "§ 3, footnote, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.fn)"]
theorem not_rep_1_1_10_of_exc {N : ℕ} (h : IsExc 4 16 6 N) : ¬ Rep3 1 1 10 N := by
  obtain ⟨l, m, rfl⟩ := h
  have e : 4 ^ l * (16 * m + 6) = 2 * (4 ^ l * (8 * m + 3)) := by ring
  rw [e, rep_1_1_10_two_mul_iff]
  exact not_rep_115_of_exc ⟨l, m, rfl⟩

/-- **The even numbers not of the form $x^2 + y^2 + 10z^2$ are exactly $4^\lambda(16\mu + 6)$** (the historical sources
). **Proved conditional on** the stated law `Ternary115` for $x^2 + y^2 + 5z^2$. -/
@[kb "ramanujan1917" "§ 3, footnote, Collected Papers p. 172 (occurrence ramanujan1927-papers:p20.s3.fn)"]
theorem even_rep_1_1_10_of_ternary115 (h : Ternary115) (N : ℕ) (hN : Even N) :
    Rep3 1 1 10 N ↔ ¬ IsExc 4 16 6 N := by
  obtain ⟨k, rfl⟩ := hN
  rw [← two_mul, rep_1_1_10_two_mul_iff, exc_half_1_16_6]
  exact h k

/-! ### $x^2 + y^2 + z^2 + nu^2$ -/

/-- **Infinitely many exceptions for $n \equiv 0 \pmod 8$** (§ 6.1): every
$N \equiv 7 \pmod 8$ is missed by $x^2 + y^2 + z^2 + nu^2$. **Proved.** -/
@[kb "ramanujan1917" "§ 6.1, Collected Papers p. 175 (occurrence ramanujan1927-papers:p20.s6) [unverified locator]"]
theorem quaternary_exc_zero_mod_eight {n N : ℕ} (hn : n % 8 = 0) (hN : N % 8 = 7) : ¬ Rep4 1 1 1 n N := by
  intro h
  obtain ⟨x, y, z, u, h⟩ := rep4_int h
  have hd : (8 : ℤ) ∣ (n : ℤ) * u ^ 2 :=
    Dvd.dvd.mul_right (by exact_mod_cast Nat.dvd_of_mod_eq_zero hn) _
  have := sq8 x
  have := sq8 y
  have := sq8 z
  omega

/-- **Infinitely many exceptions for $n \equiv 1 \pmod 8$, $n \ge 33$** (§ 6.5 (i)):
$x^2 + y^2 + z^2 + nu^2$ misses $7 \cdot 4^\lambda$ for every $\lambda \ge 0$. **Proved.** *Update:* Ramanujan says
"for $\lambda$ large"; every $\lambda \ge 0$ works. -/
@[kb "ramanujan1917" "§ 6.5 (i), Collected Papers p. 176 (occurrence ramanujan1927-papers:p20.s6) [unverified locator]"]
theorem quaternary_exc_one_mod_eight {n : ℕ} (hn : n % 8 = 1) (h33 : 33 ≤ n) (l : ℕ) :
    ¬ Rep4 1 1 1 n (7 * 4 ^ l) := by
  intro h
  obtain ⟨x, y, z, u, h⟩ := rep4_int h
  push_cast at h
  exact exc1_aux hn h33 l x y z u h

/-- **Infinitely many exceptions for $n \equiv 4 \pmod{32}$, $n \ge 132$** (§ 6.6 (i)):
$x^2 + y^2 + z^2 + nu^2$ misses $7 \cdot 4^\lambda$ for every $\lambda \ge 0$. **Proved.** *Update:* Ramanujan says
"for $\lambda$ large"; every $\lambda \ge 0$ works. -/
@[kb "ramanujan1917" "§ 6.6 (i), Collected Papers p. 176 (occurrence ramanujan1927-papers:p20.s6) [unverified locator]"]
theorem quaternary_exc_four_mod_32 {n : ℕ} (hn : n % 32 = 4) (h132 : 132 ≤ n) (l : ℕ) :
    ¬ Rep4 1 1 1 n (7 * 4 ^ l) := by
  intro h
  obtain ⟨x, y, z, u, h⟩ := rep4_int h
  push_cast at h
  have hn132 : (132 : ℤ) ≤ n := by exact_mod_cast h132
  rcases l with _ | l
  · norm_num at h
    obtain ⟨-, h3⟩ := u_zero (B := 7) (by linarith) x y z u h
    exact (ternary_111 7).1 ⟨x, y, z, by push_cast; linarith⟩ ⟨0, 0, by norm_num⟩
  · obtain ⟨n', hn'⟩ : ∃ n', n = 4 * n' := ⟨n / 4, by omega⟩
    have hnu : (n : ℤ) * u ^ 2 = 4 * ((n' : ℤ) * u ^ 2) := by rw [hn']; push_cast; ring
    have e : (7 : ℤ) * 4 ^ (l + 1) = 4 * (7 * 4 ^ l) := by ring
    rw [e] at h
    have sx := sq8 x
    have sy := sq8 y
    have sz := sq8 z
    obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, z = 2 * c := ⟨z / 2, by omega⟩
    exact quaternary_exc_one_mod_eight (n := n') (by omega) (by omega) l
      ⟨a, b, c, u, by push_cast; linarith⟩

/-- **Ramanujan's admissible coefficients** (§ 5): $n \in \{1, 4, 9, 17, 25, 36, 68, 100\}$, or $n \equiv 2, 3 \pmod 4$,
or $n \equiv 5 \pmod 8$, or $n \equiv 12 \pmod{16}$, or $n \equiv 20 \pmod{32}$. -/
def RamanujanGoodN (n : ℕ) : Prop :=
  n = 1 ∨ n = 4 ∨ n = 9 ∨ n = 17 ∨ n = 25 ∨ n = 36 ∨ n = 68 ∨ n = 100 ∨ n % 4 = 2 ∨ n % 4 = 3 ∨ n % 8 = 5 ∨
    n % 16 = 12 ∨ n % 32 = 20

/-- **Necessity in Ramanujan's § 5 theorem** (with ): if
$x^2 + y^2 + z^2 + nu^2$ represents every integer from some point on, then $n$ is one of Ramanujan's admissible
coefficients. **Proved.** -/
@[kb "ramanujan1917" "§ 5, Collected Papers p. 174 (occurrence ramanujan1927-papers:p20.s5) [unverified locator]"]
theorem good_of_eventually_rep {n : ℕ} (h : ∃ B : ℕ, ∀ N ≥ B, Rep4 1 1 1 n N) : RamanujanGoodN n := by
  by_contra hng
  obtain ⟨B, hB⟩ := h
  unfold RamanujanGoodN at hng
  have key : n % 8 = 0 ∨ (n % 8 = 1 ∧ 33 ≤ n) ∨ (n % 32 = 4 ∧ 132 ≤ n) := by omega
  have hlt : B < 4 ^ B := Nat.lt_pow_self (by norm_num)
  rcases key with h0 | ⟨h1, h33⟩ | ⟨h2, h132⟩
  · exact quaternary_exc_zero_mod_eight h0 (N := 8 * B + 7) (by omega) (hB _ (by omega))
  · exact quaternary_exc_one_mod_eight h1 h33 B (hB _ (by omega))
  · exact quaternary_exc_four_mod_32 h2 h132 B (hB _ (by omega))

/-- **Sufficiency in Ramanujan's § 5 theorem**: for every admissible $n \ge 1$, the form
$x^2 + y^2 + z^2 + nu^2$ represents every integer $N \ge 4n$. **Stated** (Ramanujan's proof splits by $n$ modulo $32$
and uses the ternary laws of § 3, several of which are only stated here). -/
@[kb "ramanujan1917" "§ 5, Collected Papers p. 174 (occurrence ramanujan1927-papers:p20.s5) [unverified locator]"]
def RamanujanSection5Sufficiency : Prop :=
  ∀ n : ℕ, 1 ≤ n → RamanujanGoodN n → ∀ N : ℕ, 4 * n ≤ N → Rep4 1 1 1 n N

/-- **$m(x^2 + y^2 + z^2) + nu^2$ with $m \ge 3$ misses a residue class modulo $m$** (last
sentence): there is $r < m$ such that no $N \equiv r \pmod m$ is of the form $m(x^2 + y^2 + z^2) + nu^2$. **Proved**
(the values $nu^2 \bmod m$ are at most $\lfloor m/2\rfloor + 1 < m$ residues, as $u$ and $-u$ give the same). -/
@[kb "ramanujan1917" "§ 5, Collected Papers p. 174 (occurrence ramanujan1927-papers:p20.s5) [unverified locator]"]
theorem exists_residue_not_rep_of_three_le {m : ℕ} (hm : 3 ≤ m) (n : ℕ) :
    ∃ r < m, ∀ N : ℕ, N % m = r → ¬ ∃ x y z u : ℤ, (m : ℤ) * (x ^ 2 + y ^ 2 + z ^ 2) + n * u ^ 2 = N := by
  have hmpos : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmod : ∀ u w : ℤ, (w ≡ u [ZMOD m] ∨ w ≡ -u [ZMOD m]) → (n : ℤ) * u ^ 2 % m = (n : ℤ) * w ^ 2 % m := by
    rintro u w (h | h)
    · exact ((h.pow 2).symm).mul_left (n : ℤ)
    · have := h.pow 2
      rw [neg_sq] at this
      exact (this.symm).mul_left (n : ℤ)
  have key : ∀ u : ℤ, ∃ w : ℕ, w < m / 2 + 1 ∧ (n : ℤ) * u ^ 2 % m = (((n * w ^ 2) % m : ℕ) : ℤ) := by
    intro u
    have hv0 : 0 ≤ u % m := Int.emod_nonneg _ hmpos.ne'
    have hv1 : u % m < m := Int.emod_lt_of_pos _ hmpos
    have hvu : u % (m : ℤ) ≡ u [ZMOD m] := Int.mod_modEq u m
    by_cases hc : 2 * (u % (m : ℤ)) ≤ m
    · refine ⟨(u % (m : ℤ)).toNat, by omega, ?_⟩
      have h1 := hmod u (u % m) (Or.inl hvu)
      rw [h1]
      push_cast
      rw [Int.toNat_of_nonneg hv0]
    · refine ⟨((m : ℤ) - u % (m : ℤ)).toNat, by omega, ?_⟩
      have hw : ((m : ℤ) - u % (m : ℤ)) ≡ -u [ZMOD m] := by
        have h0 : (m : ℤ) - u % (m : ℤ) ≡ 0 - u % (m : ℤ) [ZMOD m] :=
          (Int.modEq_zero_iff_dvd.2 dvd_rfl).sub_right _
        rw [zero_sub] at h0
        exact h0.trans hvu.neg
      have h1 := hmod u _ (Or.inr hw)
      rw [h1]
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]
  have hcard : (Finset.image (fun w : ℕ => (n * w ^ 2) % m) (Finset.range (m / 2 + 1))).card <
      (Finset.range m).card := by
    calc _ ≤ (Finset.range (m / 2 + 1)).card := Finset.card_image_le
      _ = m / 2 + 1 := Finset.card_range _
      _ < (Finset.range m).card := by rw [Finset.card_range]; omega
  obtain ⟨r, hr, hrn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨r, Finset.mem_range.1 hr, ?_⟩
  rintro N hN ⟨x, y, z, u, h⟩
  obtain ⟨w, hw, hw2⟩ := key u
  apply hrn
  rw [Finset.mem_image]
  refine ⟨w, Finset.mem_range.2 hw, ?_⟩
  have h1 : (N : ℤ) % m = (n : ℤ) * u ^ 2 % m := by
    rw [← h, add_comm, Int.add_mul_emod_self_left]
  have h2 : ((N % m : ℕ) : ℤ) = (((n * w ^ 2) % m : ℕ) : ℤ) := by
    rw [← hw2, ← h1]
    push_cast
    rfl
  rw [hN] at h2
  exact_mod_cast h2.symm

/-! ### Liouville's and Pepin's twelve forms -/

/-- **Ten of the twelve forms treated by Liouville and Pepin are universal**:
$(1,1,1,2)$, $(1,1,1,4)$, $(1,1,2,2)$, $(1,2,2,2)$, $(1,1,2,4)$, $(1,2,2,4)$, $(1,2,4,4)$, $(1,1,2,8)$, $(1,2,4,8)$,
$(1,2,3,6)$. **Wrapper** of `universal_of_ramanujanList` and `universal_1236`. -/
@[kb "ramanujan1927" "No. 20, § 2, footnote, Collected Papers p. 170 (occurrence ramanujan1927-papers:p20.s2.fn)"]
theorem liouville_pepin_universal :
    Universal4 1 1 1 2 ∧ Universal4 1 1 1 4 ∧ Universal4 1 1 2 2 ∧ Universal4 1 2 2 2 ∧ Universal4 1 1 2 4 ∧
      Universal4 1 2 2 4 ∧ Universal4 1 2 4 4 ∧ Universal4 1 1 2 8 ∧ Universal4 1 2 4 8 ∧ Universal4 1 2 3 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, universal_1236⟩ <;>
    exact universal_of_ramanujanList (by unfold RamanujanList; omega) (by unfold RemainingForm; omega)

/-- **The other two of Liouville's and Pepin's forms**, $(1,1,3,3)$ and $(1,2,5,10)$,
are universal, **conditional on** the stated `RamanujanRemaining` (they are among its 15 forms). -/
@[kb "ramanujan1927" "No. 20, § 2, footnote, Collected Papers p. 170 (occurrence ramanujan1927-papers:p20.s2.fn)"]
theorem liouville_pepin_universal_of_remaining (h : RamanujanRemaining) :
    Universal4 1 1 3 3 ∧ Universal4 1 2 5 10 :=
  ⟨h 1 1 3 3 (by unfold RemainingForm; omega), h 1 2 5 10 (by unfold RemainingForm; omega)⟩

end QuadFormsKB.Historical.Ramanujan
