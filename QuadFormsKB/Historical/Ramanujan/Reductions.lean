/-
# Ramanujan's 15 remaining quaternary forms from his three stated ternary laws

**Library** `QuadFormsKB.Historical.Ramanujan` (historical library, not imported by `QuadFormsKB`).  Targets
(Ramanujan 1917, § 2, table; *Collected Papers* p. 170) and 
($x^2 + y^2 + 3z^2 + 3t^2$; Smith, *Collected Mathematical Papers* II; Dickson, *History* III).

The 15 forms of `RemainingForm` are not proved universal unconditionally here; this file proves that they are universal
**conditional on** the three stated ternary laws of `Ternary.lean` (Dirichlet's `Ternary113` for $x^2 + y^2 + 3z^2$,
`Ternary123`, `Ternary125`), exactly as the 38 other forms follow from the proved ternary laws: for each $n$ choose the
fourth variable $t$ so that $n - dt^2$ avoids the exceptions of the ternary sub-form. These are reductions, not
inputs: the three laws are stated `Prop`s, never assumed by an unconditional result.

* `universal1133_of_ternary113`: `Ternary113 → Universal1133`.
* `ramanujanRemaining_of_ternary`: `Ternary113 → Ternary123 → Ternary125 → RamanujanRemaining`.
* `ramanujanClassification_of_ternary`: the corrected classification (54 forms) from the same three laws.
-/
import QuadFormsKB.Historical.Ramanujan.Quaternary

namespace QuadFormsKB.Historical.Ramanujan

/-- Scaling all four variables by $q$: $\mathrm{Rep4}(m) \Rightarrow \mathrm{Rep4}(q^2 m)$. -/
private theorem rep4_scale {a b c d m : ℕ} (q : ℕ) (h : Rep4 a b c d m) : Rep4 a b c d (q ^ 2 * m) := by
  obtain ⟨x, y, z, t, h⟩ := h
  exact ⟨q * x, q * y, q * z, q * t, by push_cast; linear_combination (q : ℤ) ^ 2 * h⟩

/-- Universality follows from representing every $n$ with $q^2 \nmid n$ (descent $n = q^2 m$). -/
private theorem univ_nonmult_aux (a b c d q : ℕ) (hq : 2 ≤ q) (h : ∀ n, n % (q ^ 2) ≠ 0 → Rep4 a b c d n) :
    Universal4 a b c d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : n % (q ^ 2) = 0
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact ⟨0, 0, 0, 0, by simp⟩
      · obtain ⟨m, rfl⟩ : ∃ m, n = q ^ 2 * m := ⟨n / q ^ 2, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)).symm⟩
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | h0
          · simp at hpos
          · exact h0
        have hq2 : 4 ≤ q ^ 2 := by nlinarith
        have hm : m < q ^ 2 * m := by nlinarith
        exact rep4_scale q (ih m hm)
    · exact h n h4

private theorem univ_nonmult4 (a b c d : ℕ) (h : ∀ n, n % 4 ≠ 0 → Rep4 a b c d n) : Universal4 a b c d :=
  univ_nonmult_aux a b c d 2 (by norm_num) (by simpa using h)

private theorem univ_nonmult9 (a b c d : ℕ) (h : ∀ n, n % 9 ≠ 0 → Rep4 a b c d n) : Universal4 a b c d :=
  univ_nonmult_aux a b c d 3 (by norm_num) (by simpa using h)

private theorem univ_nonmult25 (a b c d : ℕ) (h : ∀ n, n % 25 ≠ 0 → Rep4 a b c d n) : Universal4 a b c d :=
  univ_nonmult_aux a b c d 5 (by norm_num) (by simpa using h)

private theorem nexcA (N : ℕ) (h : N % 9 ≠ 6 ∧ (N % 9 ≠ 0 ∨ (N % 81 ≠ 0 ∧ N % 81 ≠ 54))) : ¬ IsExc 9 9 6 N := by
  rintro ⟨l, m, hN⟩
  rcases l with _ | _ | l
  · simp at hN; omega
  · simp at hN; omega
  · have : N = 81 * (9 ^ l * (9 * m + 6)) := by rw [hN]; ring
    omega

private theorem nexcB (N : ℕ) (h : N % 4 ≠ 0 ∧ N % 16 ≠ 10) : ¬ IsExc 4 16 10 N := by
  rintro ⟨l, m, hN⟩
  rcases l with _ | l
  · simp at hN; omega
  · have : N = 4 * (4 ^ l * (16 * m + 10)) := by rw [hN]; ring
    omega

private theorem nexcC (N : ℕ) (h : N % 25 ≠ 0 ∧ N % 25 ≠ 10 ∧ N % 25 ≠ 15) :
    ¬ (IsExc 25 25 10 N ∨ IsExc 25 25 15 N) := by
  rintro (⟨l, m, hN⟩ | ⟨l, m, hN⟩)
  · rcases l with _ | l
    · simp at hN; omega
    · have : N = 25 * (25 ^ l * (25 * m + 10)) := by rw [hN]; ring
      omega
  · rcases l with _ | l
    · simp at hN; omega
    · have : N = 25 * (25 ^ l * (25 * m + 15)) := by rw [hN]; ring
      omega

/-- Adding $e t^2$ to a ternary representation of $n - et^2$. -/
private theorem drop4' (a b c e n t : ℕ) (h : e * t ^ 2 ≤ n) (hr : Rep3 a b c (n - e * t ^ 2)) :
    Rep4 a b c e n := by
  obtain ⟨x, y, z, hxyz⟩ := hr
  have hc : ((n - e * t ^ 2 : ℕ) : ℤ) = n - e * t ^ 2 := by rw [Nat.cast_sub h]; push_cast; ring
  rw [hc] at hxyz
  exact ⟨x, y, z, t, by linarith⟩

private theorem stepA (h : Ternary113) (d n t s : ℕ) (hs : d * t ^ 2 = s) (hle : s ≤ n)
    (hg : (n - s) % 9 ≠ 6 ∧ ((n - s) % 9 ≠ 0 ∨ ((n - s) % 81 ≠ 0 ∧ (n - s) % 81 ≠ 54))) : Rep4 1 1 3 d n := by
  subst hs
  exact drop4' 1 1 3 d n t hle ((h _).2 (nexcA _ hg))

private theorem stepB (h : Ternary123) (d n t s : ℕ) (hs : d * t ^ 2 = s) (hle : s ≤ n)
    (hg : (n - s) % 4 ≠ 0 ∧ (n - s) % 16 ≠ 10) : Rep4 1 2 3 d n := by
  subst hs
  exact drop4' 1 2 3 d n t hle ((h _).2 (nexcB _ hg))

private theorem stepC (h : Ternary125) (d n t s : ℕ) (hs : d * t ^ 2 = s) (hle : s ≤ n)
    (hg : (n - s) % 25 ≠ 0 ∧ (n - s) % 25 ≠ 10 ∧ (n - s) % 25 ≠ 15) : Rep4 1 2 5 d n := by
  subst hs
  exact drop4' 1 2 5 d n t hle ((h _).2 (nexcC _ hg))

private theorem arithA_3 (n : ℕ) (hn : n % 9 ≠ 0) :
    (n) % 9 ≠ 6 ∧ ((n) % 9 ≠ 0 ∨ ((n) % 81 ≠ 0 ∧ (n) % 81 ≠ 54)) ∨
    (3 ≤ n ∧ ((n - 3) % 9 ≠ 6 ∧ ((n - 3) % 9 ≠ 0 ∨ ((n - 3) % 81 ≠ 0 ∧ (n - 3) % 81 ≠ 54)))) := by omega

private theorem remA_3 (h : Ternary113) : Universal4 1 1 3 3 :=
  univ_nonmult9 _ _ _ _ fun n hn => by
    rcases arithA_3 n hn with h0 | ⟨h1, h2⟩
    · exact stepA h 3 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepA h 3 n 1 3 (by norm_num) (by omega) (by omega)

private theorem arithA_4 (n : ℕ) (hn : n % 9 ≠ 0) :
    (n) % 9 ≠ 6 ∧ ((n) % 9 ≠ 0 ∨ ((n) % 81 ≠ 0 ∧ (n) % 81 ≠ 54)) ∨
    (4 ≤ n ∧ ((n - 4) % 9 ≠ 6 ∧ ((n - 4) % 9 ≠ 0 ∨ ((n - 4) % 81 ≠ 0 ∧ (n - 4) % 81 ≠ 54)))) := by omega

private theorem remA_4 (h : Ternary113) : Universal4 1 1 3 4 :=
  univ_nonmult9 _ _ _ _ fun n hn => by
    rcases arithA_4 n hn with h0 | ⟨h1, h2⟩
    · exact stepA h 4 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepA h 4 n 1 4 (by norm_num) (by omega) (by omega)

private theorem arithA_5 (n : ℕ) (hn : n % 9 ≠ 0) :
    (n) % 9 ≠ 6 ∧ ((n) % 9 ≠ 0 ∨ ((n) % 81 ≠ 0 ∧ (n) % 81 ≠ 54)) ∨
    (5 ≤ n ∧ ((n - 5) % 9 ≠ 6 ∧ ((n - 5) % 9 ≠ 0 ∨ ((n - 5) % 81 ≠ 0 ∧ (n - 5) % 81 ≠ 54)))) := by omega

private theorem remA_5 (h : Ternary113) : Universal4 1 1 3 5 :=
  univ_nonmult9 _ _ _ _ fun n hn => by
    rcases arithA_5 n hn with h0 | ⟨h1, h2⟩
    · exact stepA h 5 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepA h 5 n 1 5 (by norm_num) (by omega) (by omega)

private theorem arithA_6 (n : ℕ) (hn : n % 9 ≠ 0) :
    (n) % 9 ≠ 6 ∧ ((n) % 9 ≠ 0 ∨ ((n) % 81 ≠ 0 ∧ (n) % 81 ≠ 54)) ∨
    (6 ≤ n ∧ ((n - 6) % 9 ≠ 6 ∧ ((n - 6) % 9 ≠ 0 ∨ ((n - 6) % 81 ≠ 0 ∧ (n - 6) % 81 ≠ 54)))) ∨
    (24 ≤ n ∧ ((n - 24) % 9 ≠ 6 ∧ ((n - 24) % 9 ≠ 0 ∨ ((n - 24) % 81 ≠ 0 ∧ (n - 24) % 81 ≠ 54)))) ∨
    n = 6 := by omega

private theorem remA_6 (h : Ternary113) : Universal4 1 1 3 6 :=
  univ_nonmult9 _ _ _ _ fun n hn => by
    rcases arithA_6 n hn with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl
    · exact stepA h 6 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepA h 6 n 1 6 (by norm_num) (by omega) (by omega)
    · exact stepA h 6 n 2 24 (by norm_num) (by omega) (by omega)
    · exact ⟨0, 0, 0, 1, by norm_num⟩

private theorem arithB_3 (n : ℕ) (hn : n % 4 ≠ 0) :
    (n) % 4 ≠ 0 ∧ (n) % 16 ≠ 10 ∨
    (3 ≤ n ∧ ((n - 3) % 4 ≠ 0 ∧ (n - 3) % 16 ≠ 10)) := by omega

private theorem remB_3 (h : Ternary123) : Universal4 1 2 3 3 :=
  univ_nonmult4 _ _ _ _ fun n hn => by
    rcases arithB_3 n hn with h0 | ⟨h1, h2⟩
    · exact stepB h 3 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepB h 3 n 1 3 (by norm_num) (by omega) (by omega)

private theorem arithB_5 (n : ℕ) (hn : n % 4 ≠ 0) :
    (n) % 4 ≠ 0 ∧ (n) % 16 ≠ 10 ∨
    (5 ≤ n ∧ ((n - 5) % 4 ≠ 0 ∧ (n - 5) % 16 ≠ 10)) := by omega

private theorem remB_5 (h : Ternary123) : Universal4 1 2 3 5 :=
  univ_nonmult4 _ _ _ _ fun n hn => by
    rcases arithB_5 n hn with h0 | ⟨h1, h2⟩
    · exact stepB h 5 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepB h 5 n 1 5 (by norm_num) (by omega) (by omega)

private theorem arithB_7 (n : ℕ) (hn : n % 4 ≠ 0) :
    (n) % 4 ≠ 0 ∧ (n) % 16 ≠ 10 ∨
    (7 ≤ n ∧ ((n - 7) % 4 ≠ 0 ∧ (n - 7) % 16 ≠ 10)) := by omega

private theorem remB_7 (h : Ternary123) : Universal4 1 2 3 7 :=
  univ_nonmult4 _ _ _ _ fun n hn => by
    rcases arithB_7 n hn with h0 | ⟨h1, h2⟩
    · exact stepB h 7 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepB h 7 n 1 7 (by norm_num) (by omega) (by omega)

private theorem arithB_8 (n : ℕ) (hn : n % 4 ≠ 0) :
    (n) % 4 ≠ 0 ∧ (n) % 16 ≠ 10 ∨
    (8 ≤ n ∧ ((n - 8) % 4 ≠ 0 ∧ (n - 8) % 16 ≠ 10)) := by omega

private theorem remB_8 (h : Ternary123) : Universal4 1 2 3 8 :=
  univ_nonmult4 _ _ _ _ fun n hn => by
    rcases arithB_8 n hn with h0 | ⟨h1, h2⟩
    · exact stepB h 8 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepB h 8 n 1 8 (by norm_num) (by omega) (by omega)

private theorem arithB_9 (n : ℕ) (hn : n % 4 ≠ 0) :
    (n) % 4 ≠ 0 ∧ (n) % 16 ≠ 10 ∨
    (9 ≤ n ∧ ((n - 9) % 4 ≠ 0 ∧ (n - 9) % 16 ≠ 10)) := by omega

private theorem remB_9 (h : Ternary123) : Universal4 1 2 3 9 :=
  univ_nonmult4 _ _ _ _ fun n hn => by
    rcases arithB_9 n hn with h0 | ⟨h1, h2⟩
    · exact stepB h 9 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepB h 9 n 1 9 (by norm_num) (by omega) (by omega)

private theorem arithB_10 (n : ℕ) (hn : n % 4 ≠ 0) :
    (n) % 4 ≠ 0 ∧ (n) % 16 ≠ 10 ∨
    (40 ≤ n ∧ ((n - 40) % 4 ≠ 0 ∧ (n - 40) % 16 ≠ 10)) ∨
    n = 10 ∨
    n = 26 := by omega

private theorem remB_10 (h : Ternary123) : Universal4 1 2 3 10 :=
  univ_nonmult4 _ _ _ _ fun n hn => by
    rcases arithB_10 n hn with h0 | ⟨h1, h2⟩ | rfl | rfl
    · exact stepB h 10 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepB h 10 n 2 40 (by norm_num) (by omega) (by omega)
    · exact ⟨0, 0, 0, 1, by norm_num⟩
    · exact ⟨4, 0, 0, 1, by norm_num⟩

private theorem arithC_6 (n : ℕ) (hn : n % 25 ≠ 0) :
    (n) % 25 ≠ 0 ∧ (n) % 25 ≠ 10 ∧ (n) % 25 ≠ 15 ∨
    (6 ≤ n ∧ ((n - 6) % 25 ≠ 0 ∧ (n - 6) % 25 ≠ 10 ∧ (n - 6) % 25 ≠ 15)) := by omega

private theorem remC_6 (h : Ternary125) : Universal4 1 2 5 6 :=
  univ_nonmult25 _ _ _ _ fun n hn => by
    rcases arithC_6 n hn with h0 | ⟨h1, h2⟩
    · exact stepC h 6 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepC h 6 n 1 6 (by norm_num) (by omega) (by omega)

private theorem arithC_7 (n : ℕ) (hn : n % 25 ≠ 0) :
    (n) % 25 ≠ 0 ∧ (n) % 25 ≠ 10 ∧ (n) % 25 ≠ 15 ∨
    (7 ≤ n ∧ ((n - 7) % 25 ≠ 0 ∧ (n - 7) % 25 ≠ 10 ∧ (n - 7) % 25 ≠ 15)) := by omega

private theorem remC_7 (h : Ternary125) : Universal4 1 2 5 7 :=
  univ_nonmult25 _ _ _ _ fun n hn => by
    rcases arithC_7 n hn with h0 | ⟨h1, h2⟩
    · exact stepC h 7 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepC h 7 n 1 7 (by norm_num) (by omega) (by omega)

private theorem arithC_8 (n : ℕ) (hn : n % 25 ≠ 0) :
    (n) % 25 ≠ 0 ∧ (n) % 25 ≠ 10 ∧ (n) % 25 ≠ 15 ∨
    (8 ≤ n ∧ ((n - 8) % 25 ≠ 0 ∧ (n - 8) % 25 ≠ 10 ∧ (n - 8) % 25 ≠ 15)) := by omega

private theorem remC_8 (h : Ternary125) : Universal4 1 2 5 8 :=
  univ_nonmult25 _ _ _ _ fun n hn => by
    rcases arithC_8 n hn with h0 | ⟨h1, h2⟩
    · exact stepC h 8 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepC h 8 n 1 8 (by norm_num) (by omega) (by omega)

private theorem arithC_9 (n : ℕ) (hn : n % 25 ≠ 0) :
    (n) % 25 ≠ 0 ∧ (n) % 25 ≠ 10 ∧ (n) % 25 ≠ 15 ∨
    (9 ≤ n ∧ ((n - 9) % 25 ≠ 0 ∧ (n - 9) % 25 ≠ 10 ∧ (n - 9) % 25 ≠ 15)) := by omega

private theorem remC_9 (h : Ternary125) : Universal4 1 2 5 9 :=
  univ_nonmult25 _ _ _ _ fun n hn => by
    rcases arithC_9 n hn with h0 | ⟨h1, h2⟩
    · exact stepC h 9 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepC h 9 n 1 9 (by norm_num) (by omega) (by omega)

private theorem arithC_10 (n : ℕ) (hn : n % 25 ≠ 0) :
    (n) % 25 ≠ 0 ∧ (n) % 25 ≠ 10 ∧ (n) % 25 ≠ 15 ∨
    (10 ≤ n ∧ ((n - 10) % 25 ≠ 0 ∧ (n - 10) % 25 ≠ 10 ∧ (n - 10) % 25 ≠ 15)) ∨
    (40 ≤ n ∧ ((n - 40) % 25 ≠ 0 ∧ (n - 40) % 25 ≠ 10 ∧ (n - 40) % 25 ≠ 15)) ∨
    n = 10 ∨
    n = 35 := by omega

private theorem remC_10 (h : Ternary125) : Universal4 1 2 5 10 :=
  univ_nonmult25 _ _ _ _ fun n hn => by
    rcases arithC_10 n hn with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl | rfl
    · exact stepC h 10 n 0 0 (by norm_num) (by omega) (by omega)
    · exact stepC h 10 n 1 10 (by norm_num) (by omega) (by omega)
    · exact stepC h 10 n 2 40 (by norm_num) (by omega) (by omega)
    · exact ⟨0, 0, 0, 1, by norm_num⟩
    · exact ⟨5, 0, 0, 1, by norm_num⟩


/-- **$x^2 + y^2 + 3z^2 + 3t^2$ is universal, conditional on Dirichlet's law for $x^2 + y^2 + 3z^2$** (the historical sources
): `Ternary113 → Universal1133` (for $n = 9^\lambda(9\mu + 6)$ take
$t = 3^\lambda$). -/
@[kb "smith1894b" "[unverified locator]"]
theorem universal1133_of_ternary113 (h : Ternary113) : Universal1133 :=
  remA_3 h

/-- **The 15 remaining forms are universal, conditional on the three stated ternary laws** (the historical sources
). -/
@[kb "ramanujan1917" "§ 2, table, Collected Papers p. 170"]
theorem ramanujanRemaining_of_ternary (h3 : Ternary113) (h23 : Ternary123) (h25 : Ternary125) :
    RamanujanRemaining := by
  rintro a b c d ⟨rfl, ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, hd⟩ | ⟨rfl, rfl, h1, h2⟩⟩
  · obtain rfl | rfl | rfl | rfl : d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
    exacts [remA_3 h3, remA_4 h3, remA_5 h3, remA_6 h3]
  · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [remB_3 h23, remB_5 h23, remB_7 h23, remB_8 h23, remB_9 h23, remB_10 h23]
  · obtain rfl | rfl | rfl | rfl | rfl : d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 := by omega
    exacts [remC_6 h25, remC_7 h25, remC_8 h25, remC_9 h25, remC_10 h25]

/-- **Ramanujan's classification (54 forms), conditional on the three stated ternary laws** (the historical sources
). -/
@[kb "ramanujan1917" "§ 2, Collected Papers pp. 169–170"]
theorem ramanujanClassification_of_ternary (h3 : Ternary113) (h23 : Ternary123) (h25 : Ternary125) :
    RamanujanClassification :=
  ramanujanClassification_iff.2 (ramanujanRemaining_of_ternary h3 h23 h25)

end QuadFormsKB.Historical.Ramanujan
