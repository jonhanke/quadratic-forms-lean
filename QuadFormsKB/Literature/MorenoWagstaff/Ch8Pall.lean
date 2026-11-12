/-
# Moreno–Wagstaff 2005, §8.4: Pall's theorem on sums of $s$ positive squares

**Source.** G. Pall, *On sums of squares*, Amer. Math. Monthly 40 (1933), 10–18; cited in C. J. Moreno and
S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), §8.4, Theorem 8.4, p. 328.

**Proves**
* `theorem84` (**proved**, unconditional, using only Legendre's three-squares theorem
  `Grosswald.legendre_three_squares`): the full statement `Theorem84` (cases $s \ge 6$, $s = 5$, $s = 4$).

**Method.** The book cites the result without proof; the argument here is ours.
* *Finite checks.* The set of sums of $s$ positive squares (squares $\le 12^2$) is encoded as a bitmask
  `pm s`, and all checks for $n \le 168$ are done by `decide +kernel`.
* *$s = 4$.* If $N \equiv 3, 6 \pmod 8$ then $N$ is a sum of three squares (Legendre) but not of two (squares are
  $0,1,4 \bmod 8$), so every three-square representation of $N$ has all three entries positive. For $n \not\equiv 0
  \pmod 8$ and $n > 168$ one subtracts a suitable $a^2$ (or, for $n \equiv 1 \pmod 4$, an odd $a^2$ chosen by $n \bmod
  32$, and scales by $2$) to land in that case. If $8 \mid n$, every representation of $n$ by four squares has all
  entries even, so $n$ is represented iff $n/4$ is (strong induction); this also gives the nonrepresentability of
  $4^e n_1$, $n_1 \in \{2,6,14\}$.
* *$s \ge 5$.* Nonrepresentability of $s + b$, $b \in B$, by induction on $s$ (the defects $k^2 - 1$ cannot sum to
  $b$); for $s = 5$, $n = 33$ by the finite check. Representability: for $s = 5$ and $n > 168$ add $k^2$, $k \in \{1,2\}$,
  to an odd (hence non-exceptional) number represented by four positive squares; $s \ge 6$ by induction adding $1^2$.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Statements
import QuadFormsKB.Literature.Classical.SumsOfSquares

namespace QuadFormsKB.MorenoWagstaff

namespace Pall

/-- Bitmask: bit $n$ of `orK m K` is set iff $n = k^2 + j$ with $1 \le k \le K$ and bit $j$ of `m` set. -/
def orK (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => orK m k ||| (m <<< (k + 1) ^ 2)

/-- Bitmask of the sums of $s$ positive squares (with roots $\le 12$). -/
def pm : ℕ → ℕ
  | 0 => 1
  | s + 1 => orK (pm s) 12

theorem testBit_orK (m K n : ℕ) : (orK m K).testBit n = true ↔
    ∃ k, 1 ≤ k ∧ k ≤ K ∧ k ^ 2 ≤ n ∧ m.testBit (n - k ^ 2) = true := by
  induction K with
  | zero => simp [orK]
  | succ K ih =>
    have key : (orK m (K + 1)).testBit n = true ↔
        (orK m K).testBit n = true ∨ ((K + 1) ^ 2 ≤ n ∧ m.testBit (n - (K + 1) ^ 2) = true) := by
      simp [orK, Nat.testBit_shiftLeft]
    rw [key, ih]
    constructor
    · rintro (⟨k, h1, h2, h3, h4⟩ | ⟨h1, h2⟩)
      · exact ⟨k, h1, by omega, h3, h4⟩
      · exact ⟨K + 1, by omega, le_rfl, h1, h2⟩
    · rintro ⟨k, h1, h2, h3, h4⟩
      by_cases hk : k = K + 1
      · subst hk; exact Or.inr ⟨h3, h4⟩
      · exact Or.inl ⟨k, h1, by omega, h3, h4⟩

/-- Decomposition of a sum of $s+1$ positive squares. -/
theorem succ_iff (s n : ℕ) : IsSumPosSq (s + 1) n ↔
    ∃ k m, 0 < k ∧ IsSumPosSq s m ∧ k ^ 2 + m = n := by
  constructor
  · rintro ⟨x, hx, hs⟩
    refine ⟨x 0, ∑ i : Fin s, x i.succ ^ 2, hx 0, ⟨fun i => x i.succ, fun i => hx _, rfl⟩, ?_⟩
    rw [← hs, Fin.sum_univ_succ]
  · rintro ⟨k, m, hk, ⟨x, hx, hs⟩, rfl⟩
    refine ⟨Fin.cons k x, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hk
      · simpa using hx j
    · rw [Fin.sum_univ_succ]; simp [hs]

theorem zero_iff (n : ℕ) : IsSumPosSq 0 n ↔ n = 0 := by
  constructor
  · rintro ⟨x, _, h⟩; simpa using h.symm
  · rintro rfl; exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩

theorem testBit_pm (s : ℕ) : ∀ n, n < 169 → ((pm s).testBit n = true ↔ IsSumPosSq s n) := by
  induction s with
  | zero =>
    intro n _
    rw [zero_iff]
    simp [pm, Nat.testBit_one_eq_true_iff_self_eq_zero]
  | succ s ih =>
    intro n hn
    simp only [pm]
    rw [testBit_orK, succ_iff]
    constructor
    · rintro ⟨k, h1, h2, h3, h4⟩
      exact ⟨k, n - k ^ 2, by omega, (ih _ (by omega)).1 h4, by omega⟩
    · rintro ⟨k, m, hk, hm, rfl⟩
      have hk12 : k ≤ 12 := by nlinarith
      exact ⟨k, hk, hk12, by omega, by rw [Nat.add_sub_cancel_left]; exact (ih _ (by omega)).2 hm⟩

theorem four_iff (n : ℕ) : IsSumPosSq 4 n ↔
    ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  constructor
  · intro h
    obtain ⟨a, m1, ha, h3, rfl⟩ := (succ_iff 3 n).1 h
    obtain ⟨b, m2, hb, h2, rfl⟩ := (succ_iff 2 m1).1 h3
    obtain ⟨c, m3, hc, h1, rfl⟩ := (succ_iff 1 m2).1 h2
    obtain ⟨d, m4, hd, h0, rfl⟩ := (succ_iff 0 m3).1 h1
    have := (zero_iff m4).1 h0
    subst this
    exact ⟨a, b, c, d, ha, hb, hc, hd, by ring⟩
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
    refine (succ_iff 3 _).2 ⟨a, b ^ 2 + c ^ 2 + d ^ 2, ha, ?_, by ring⟩
    refine (succ_iff 2 _).2 ⟨b, c ^ 2 + d ^ 2, hb, ?_, by ring⟩
    refine (succ_iff 1 _).2 ⟨c, d ^ 2, hc, ?_, by ring⟩
    exact (succ_iff 0 _).2 ⟨d, 0, hd, (zero_iff 0).2 rfl, rfl⟩

theorem sq_mod8 (a : ℕ) :
    (a % 2 = 1 ∧ a ^ 2 % 8 = 1) ∨ (a % 2 = 0 ∧ (a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 4)) := by
  have e : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod _ _ _
  rcases (by omega : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨
    a % 8 = 6 ∨ a % 8 = 7) with h | h | h | h | h | h | h | h <;> rw [e, h] <;> omega

theorem sq_mod8' (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  rcases sq_mod8 a with h | h <;> omega

/-- Doubling: $s$ positive squares for $m$ gives $s$ positive squares for $4m$. -/
theorem quad (s m : ℕ) (h : IsSumPosSq s m) : IsSumPosSq s (4 * m) := by
  obtain ⟨x, hx, hs⟩ := h
  refine ⟨fun i => 2 * x i, fun i => by have := hx i; show 0 < 2 * x i; omega, ?_⟩
  simp only [mul_pow]
  rw [← Finset.mul_sum, hs]; norm_num

/-- If $8 \mid n$, every representation of $n$ as a sum of four squares has even entries. -/
theorem four_quarter (n : ℕ) (h8 : 8 ∣ n) (h : IsSumPosSq 4 n) : IsSumPosSq 4 (n / 4) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hs⟩ := (four_iff n).1 h
  have ha' := sq_mod8 a
  have hb' := sq_mod8 b
  have hc' := sq_mod8 c
  have hd' := sq_mod8 d
  have hea : a % 2 = 0 := by omega
  have heb : b % 2 = 0 := by omega
  have hec : c % 2 = 0 := by omega
  have hed : d % 2 = 0 := by omega
  refine (four_iff _).2 ⟨a / 2, b / 2, c / 2, d / 2, by omega, by omega, by omega, by omega, ?_⟩
  have e1 : a ^ 2 = 4 * (a / 2) ^ 2 := by
    obtain ⟨t, rfl⟩ : 2 ∣ a := by omega
    simp; ring
  have e2 : b ^ 2 = 4 * (b / 2) ^ 2 := by
    obtain ⟨t, rfl⟩ : 2 ∣ b := by omega
    simp; ring
  have e3 : c ^ 2 = 4 * (c / 2) ^ 2 := by
    obtain ⟨t, rfl⟩ : 2 ∣ c := by omega
    simp; ring
  have e4 : d ^ 2 = 4 * (d / 2) ^ 2 := by
    obtain ⟨t, rfl⟩ : 2 ∣ d := by omega
    simp; ring
  omega

theorem three_pos (N : ℕ) (h : N % 8 = 3 ∨ N % 8 = 6) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 + z ^ 2 = N := by
  have hL := (Grosswald.legendre_three_squares N).2 (by
    rintro ⟨a, b, hab⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · omega
    · obtain ⟨t, rfl⟩ : ∃ t, a = t + 1 := ⟨a - 1, by omega⟩
      have h4 : 4 ∣ N := ⟨4 ^ t * (8 * b + 7), by rw [hab]; ring⟩
      omega)
  obtain ⟨x, y, z, hxyz⟩ := hL
  have hx := sq_mod8' x
  have hy := sq_mod8' y
  have hz := sq_mod8' z
  refine ⟨x, y, z, ?_, ?_, ?_, hxyz⟩
  · rcases Nat.eq_zero_or_pos x with rfl | hp
    · simp at hx; omega
    · exact hp
  · rcases Nat.eq_zero_or_pos y with rfl | hp
    · simp at hy; omega
    · exact hp
  · rcases Nat.eq_zero_or_pos z with rfl | hp
    · simp at hz; omega
    · exact hp

/-- The four exceptional-family and small exceptions, as in `Theorem84` (iii). -/
def Exc4 (n : ℕ) : Prop :=
  n < 4 ∨ (∃ b ∈ insert 25 (insert 37 ({1, 2, 4, 5, 7, 10, 13} : Finset ℕ)), n = 4 + b) ∨
    ∃ e : ℕ, ∃ n₁ ∈ ({2, 6, 14} : Finset ℕ), n = 4 ^ e * n₁

theorem small4 : ∀ n < 169, 0 < n →
    ¬ (n < 4 ∨ (∃ b ∈ insert 25 (insert 37 ({1, 2, 4, 5, 7, 10, 13} : Finset ℕ)), n = 4 + b) ∨
      ∃ e ∈ Finset.range 4, ∃ n₁ ∈ ({2, 6, 14} : Finset ℕ), n = 4 ^ e * n₁) →
    (pm 4).testBit n = true := by
  decide +kernel

theorem ge_of (s m : ℕ) (h : IsSumPosSq s m) : s ≤ m := by
  obtain ⟨x, hx, rfl⟩ := h
  calc s = ∑ _i : Fin s, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => by have := hx i; nlinarith

/-- $s + b$ is not a sum of $s$ positive squares for $b \in B = \{1,2,4,5,7,10,13\}$. -/
theorem negB (s : ℕ) : ∀ d : ℕ, (d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 5 ∨ d = 7 ∨ d = 10 ∨ d = 13) →
    ¬ IsSumPosSq s (s + d) := by
  induction s with
  | zero =>
    intro d hd h
    have := (zero_iff _).1 h
    omega
  | succ s ih =>
    intro d hd h
    obtain ⟨k, m, hk, hm, hkm⟩ := (succ_iff s _).1 h
    have hge := ge_of s m hm
    have hk3 : k ≤ 3 := by
      by_contra hc
      have h16 : 16 ≤ k ^ 2 := by nlinarith
      omega
    interval_cases k
    · exact ih (m - s) (by omega) (by rwa [show s + (m - s) = m by omega])
    · exact ih (m - s) (by omega) (by rwa [show s + (m - s) = m by omega])
    · exact ih (m - s) (by omega) (by rwa [show s + (m - s) = m by omega])

theorem aux1 (n a N : ℕ) (ha : 0 < a) (hN : N % 8 = 3 ∨ N % 8 = 6) (hn : a ^ 2 + N = n) :
    IsSumPosSq 4 n := by
  obtain ⟨x, y, z, hx, hy, hz, hs⟩ := three_pos N hN
  exact (four_iff n).2 ⟨a, x, y, z, ha, hx, hy, hz, by omega⟩

theorem aux2 (n a M : ℕ) (ha : 0 < a) (hM : M % 8 = 3 ∨ M % 8 = 6) (hn : a ^ 2 + 4 * M = n) :
    IsSumPosSq 4 n := by
  obtain ⟨x, y, z, hx, hy, hz, hs⟩ := three_pos M hM
  refine (four_iff n).2 ⟨a, 2 * x, 2 * y, 2 * z, ha, by omega, by omega, by omega, ?_⟩
  have : (2 * x) ^ 2 + (2 * y) ^ 2 + (2 * z) ^ 2 = 4 * (x ^ 2 + y ^ 2 + z ^ 2) := by ring
  omega

theorem four_pos (n : ℕ) (hn : 169 ≤ n) (h8 : n % 8 ≠ 0) : IsSumPosSq 4 n := by
  have hm : n % 32 = 1 ∨ n % 32 = 5 ∨ n % 32 = 9 ∨ n % 32 = 13 ∨ n % 32 = 17 ∨ n % 32 = 21 ∨
      n % 32 = 25 ∨ n % 32 = 29 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
    omega
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | (exact aux1 n 1 (n - 1) (by norm_num) (by omega) (by omega))
    | (exact aux1 n 2 (n - 4) (by norm_num) (by omega) (by omega))
    | (exact aux1 n 4 (n - 16) (by norm_num) (by omega) (by omega))
    | (exact aux2 n 1 ((n - 1) / 4) (by norm_num) (by omega) (by omega))
    | (exact aux2 n 3 ((n - 9) / 4) (by norm_num) (by omega) (by omega))
    | (exact aux2 n 5 ((n - 25) / 4) (by norm_num) (by omega) (by omega))
    | (exact aux2 n 7 ((n - 49) / 4) (by norm_num) (by omega) (by omega))

theorem not4_2 : ¬ IsSumPosSq 4 2 := fun h => by
  have := (testBit_pm 4 2 (by norm_num)).2 h; revert this; decide +kernel
theorem not4_6 : ¬ IsSumPosSq 4 6 := fun h => by
  have := (testBit_pm 4 6 (by norm_num)).2 h; revert this; decide +kernel
theorem not4_14 : ¬ IsSumPosSq 4 14 := fun h => by
  have := (testBit_pm 4 14 (by norm_num)).2 h; revert this; decide +kernel
theorem not4_29 : ¬ IsSumPosSq 4 29 := fun h => by
  have := (testBit_pm 4 29 (by norm_num)).2 h; revert this; decide +kernel
theorem not4_41 : ¬ IsSumPosSq 4 41 := fun h => by
  have := (testBit_pm 4 41 (by norm_num)).2 h; revert this; decide +kernel
theorem not5_33 : ¬ IsSumPosSq 5 33 := fun h => by
  have := (testBit_pm 5 33 (by norm_num)).2 h; revert this; decide +kernel

theorem fam (e n₁ : ℕ) (hn₁ : n₁ = 2 ∨ n₁ = 6 ∨ n₁ = 14) : ¬ IsSumPosSq 4 (4 ^ e * n₁) := by
  induction e with
  | zero =>
    rcases hn₁ with rfl | rfl | rfl
    · simpa using not4_2
    · simpa using not4_6
    · simpa using not4_14
  | succ e ih =>
    intro h
    have e1 : 4 ^ (e + 1) * n₁ = 4 * (4 ^ e * n₁) := by ring
    have h2 : 2 ∣ n₁ := by omega
    have h3 : 2 ∣ 4 ^ e * n₁ := dvd_mul_of_dvd_right h2 _
    rw [e1] at h
    have h8 : 8 ∣ 4 * (4 ^ e * n₁) := by omega
    have := four_quarter _ h8 h
    rw [show 4 * (4 ^ e * n₁) / 4 = 4 ^ e * n₁ by omega] at this
    exact ih this

theorem neg4 (n : ℕ) (h : IsSumPosSq 4 n) : ¬ Exc4 n := by
  rintro (hlt | ⟨b, hb, hnb⟩ | ⟨e, n₁, hn₁, hne⟩)
  · have := ge_of 4 n h; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    subst hnb
    rcases hb with rfl | rfl | hb
    · exact not4_29 h
    · exact not4_41 h
    · exact negB 4 b (by omega) h
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn₁
    subst hne
    exact fam e n₁ hn₁ h

theorem exc_mono (n : ℕ) (hn : 168 ≤ n) (h4 : 4 ∣ n) (h : Exc4 (n / 4)) : Exc4 n := by
  rcases h with h | ⟨b, hb, hnb⟩ | ⟨e, n₁, hn₁, hne⟩
  · omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    omega
  · exact Or.inr (Or.inr ⟨e + 1, n₁, hn₁, by
    have : 4 ^ (e + 1) * n₁ = 4 * (4 ^ e * n₁) := by ring
    omega⟩)

theorem pos4 (n : ℕ) (hn : 0 < n) (hE : ¬ Exc4 n) : IsSumPosSq 4 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hlt : n < 169
    · refine (testBit_pm 4 n hlt).1 (small4 n hlt hn ?_)
      rintro (h | h | ⟨e, -, n₁, hn₁, hne⟩)
      · exact hE (Or.inl h)
      · exact hE (Or.inr (Or.inl h))
      · exact hE (Or.inr (Or.inr ⟨e, n₁, hn₁, hne⟩))
    · by_cases h8 : n % 8 = 0
      · have h1 : IsSumPosSq 4 (n / 4) :=
          ih (n / 4) (by omega) (by omega) (fun hc => hE (exc_mono n (by omega) (by omega) hc))
        have := quad 4 _ h1
        rwa [show 4 * (n / 4) = n by omega] at this
      · exact four_pos n (by omega) h8

theorem small5 : ∀ n < 169,
    ¬ (n < 5 ∨ ∃ b ∈ insert 28 ({1, 2, 4, 5, 7, 10, 13} : Finset ℕ), n = 5 + b) →
    (pm 5).testBit n = true := by
  decide +kernel

theorem not_exc_odd (m : ℕ) (hm : 42 ≤ m) (hodd : m % 2 = 1) : ¬ Exc4 m := by
  rintro (h | ⟨b, hb, hnb⟩ | ⟨e, n₁, hn₁, hne⟩)
  · omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn₁
    have h2 : 2 ∣ n₁ := by omega
    have h3 : 2 ∣ 4 ^ e * n₁ := dvd_mul_of_dvd_right h2 _
    omega

theorem pos5 (n : ℕ)
    (h : ¬ (n < 5 ∨ ∃ b ∈ insert 28 ({1, 2, 4, 5, 7, 10, 13} : Finset ℕ), n = 5 + b)) :
    IsSumPosSq 5 n := by
  by_cases hlt : n < 169
  · exact (testBit_pm 5 n hlt).1 (small5 n hlt h)
  · rcases Nat.even_or_odd' n with ⟨t, ht | ht⟩
    · exact (succ_iff 4 n).2 ⟨1, n - 1, by norm_num, pos4 _ (by omega)
        (not_exc_odd _ (by omega) (by omega)), by omega⟩
    · exact (succ_iff 4 n).2 ⟨2, n - 4, by norm_num, pos4 _ (by omega)
        (not_exc_odd _ (by omega) (by omega)), by omega⟩

theorem pos6 (s : ℕ) (hs : 6 ≤ s) : ∀ n : ℕ, s ≤ n →
    ¬ (n = s + 1 ∨ n = s + 2 ∨ n = s + 4 ∨ n = s + 5 ∨ n = s + 7 ∨ n = s + 10 ∨ n = s + 13) →
    IsSumPosSq s n := by
  induction s, hs using Nat.le_induction with
  | base =>
    intro n hn hB
    by_cases h34 : n = 34
    · subst h34
      exact (testBit_pm 6 34 (by norm_num)).1 (by decide +kernel)
    · refine (succ_iff 5 n).2 ⟨1, n - 1, by norm_num, pos5 _ ?_, by omega⟩
      rintro (h | ⟨b, hb, h⟩)
      · omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        omega
  | succ s hs ih =>
    intro n hn hB
    exact (succ_iff s n).2 ⟨1, n - 1, by norm_num, ih _ (by omega) (by omega), by omega⟩

end Pall

/-- **Moreno–Wagstaff, Theorem 8.4** (Pall; §8.4, p. 328): the statement `Theorem84` on sums of $s$ positive
squares (exceptions for $s \ge 6$, $s = 5$, $s = 4$). Proved unconditionally; see the module header for the
method (the case $s = 4$ uses Legendre's three-squares theorem and a mod $8$ positivity argument, not the
book's, which cites Pall). -/
theorem theorem84 : Theorem84 := by
  show (∀ s n : ℕ, 6 ≤ s → 0 < n → (IsSumPosSq s n ↔
      ¬ (n < s ∨ ∃ b ∈ ({1, 2, 4, 5, 7, 10, 13} : Finset ℕ), n = s + b))) ∧
    (∀ n : ℕ, 0 < n → (IsSumPosSq 5 n ↔
      ¬ (n < 5 ∨ ∃ b ∈ insert 28 ({1, 2, 4, 5, 7, 10, 13} : Finset ℕ), n = 5 + b))) ∧
    (∀ n : ℕ, 0 < n → (IsSumPosSq 4 n ↔ ¬ Pall.Exc4 n))
  refine ⟨?_, ?_, ?_⟩
  · intro s n hs hn
    constructor
    · rintro h (h1 | ⟨b, hb, rfl⟩)
      · have := Pall.ge_of s n h; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        exact Pall.negB s b (by omega) h
    · intro h
      refine Pall.pos6 s hs n (by omega) ?_
      intro hc
      exact h (Or.inr ⟨n - s, by simp only [Finset.mem_insert, Finset.mem_singleton]; omega, by omega⟩)
  · intro n hn
    constructor
    · rintro h (h1 | ⟨b, hb, rfl⟩)
      · have := Pall.ge_of 5 n h; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | hb
        · exact Pall.not5_33 h
        · exact Pall.negB 5 b (by omega) h
    · exact Pall.pos5 n
  · intro n hn
    exact ⟨fun h => Pall.neg4 n h, fun h => Pall.pos4 n hn h⟩

end QuadFormsKB.MorenoWagstaff
