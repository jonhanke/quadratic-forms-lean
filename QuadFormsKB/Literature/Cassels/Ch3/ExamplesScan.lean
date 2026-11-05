/-
# Cassels, Chapter 3: Examples 1, 2, 3, 4, 7, 9 (pp. 49-50), transcribed from the page images

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *Examples*, pp. 49-50. The statements below
were transcribed from the page images; the machine-read text of these examples is garbled.

**Setting.** $p$ is a prime (`[Fact p.Prime]`), $\mathbb Q_p$ = `ℚ_[p]`, $\mathbb Z_p$ = `ℤ_[p]`, and
$|\cdot|_p$ is the norm `‖·‖`. The Hilbert symbol is the library's `hilbertSymbol K a b` (solvability of
$z^2 = a x^2 + b y^2$ over the field `K`), the one used by `Cassels.Ch3Ex.ex10`. The labels $a_1, a_2$ of Example 1
are labels of two $3$-adic numbers, not vector indices.

**Proves.**
* Ex. 1 (p. 49): the $3$-adic integers $a_1$ ($5a_1 + 1 = 0$) and $a_2$ ($a_2^2 = 7$, $|a_2 - 1|_3 < 1$) exist and are
  unique, and $|16 - a_1|_3 \le 3^{-3}$, $|13 - a_2|_3 \le 3^{-3}$ (`ex1`).
* Ex. 2 (p. 49): for $a \in \mathbb Z$, $5x^2 = a$ is soluble in $\mathbb Z_7$, respectively in $\mathbb Q_7$, if and only if
  $a = 0$ or ($v_7(a)$ is even and $a/7^{v_7(a)}$ is a quadratic non-residue modulo $7$) (`ex2_padicInt`, `ex2_padic`).
* Ex. 3 (p. 49): $a = 1$, $b = 172$ give $|a^2 + 6b^2 - 5|_5 \le 5^{-4}$ (`ex3`).
* Ex. 4 (p. 49): for $c \in \mathbb Z_p$ with $|c|_p < 1$, $(1 + c)^{-1} = \sum_{n \ge 0} (-c)^n$ (`ex4_geometric`),
  and $a = 7324219$ satisfies $|1/4 - a|_5 \le 5^{-10}$ (`ex4_approx`).
* Ex. 7 (p. 50): $u = 181$ satisfies $|u^2 + 7|_2 \le 2^{-10}$ (`ex7`).
* Ex. 9 (p. 50): $(a+1, -a)_p = 1$ and $(a, a)_p = (a, -1)_p$ over $\mathbb Q_p$ (`ex9_padic`) and over $\mathbb R$
  (`ex9_real`).

**Reconstructed / errata.** The explicit integers in Ex. 1, 3, 4, 7 are our own computations (the book asks to "find"
them); they were found numerically and are checked by the proofs. Ex. 9: see the *Erratum* on `ex9_padic`.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree
import QuadFormsKB.Literature.Cassels.Ch3.ExerciseTen

open Filter Topology

noncomputable section

namespace QuadFormsKB.Cassels.Ch3Scan

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-- Helper: an integer not divisible by the prime $p$ has $p$-adic norm $1$ in $\mathbb Z_p$. -/
theorem norm_intCast_eq_one {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : ‖(n : ℤ_[p])‖ = 1 := by
  have h := (PadicInt.norm_int_lt_one_iff_dvd (p := p) n).not.mpr hn
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp h)

/-- **Cassels, Ch. 3, Ex. 1 (p. 49).** In $\mathbb Z_3$ there are unique elements $a_1$, $a_2$ with
$5a_1 + 1 = 0$, respectively $a_2^2 = 7$ and $|a_2 - 1|_3 < 1$; for them $|16 - a_1|_3 \le 3^{-3}$ and
$|13 - a_2|_3 \le 3^{-3}$, so $b_1 = 16$, $b_2 = 13$ are integers with $|b_j - a_j|_3 \le 3^{-3}$.
(The book asks to find such $b_1, b_2$; the values are our computation.) -/
@[kb "cassels1978" "Ch. 3, Ex. 1, p. 49"]
theorem ex1 :
    (∃! a₁ : ℤ_[3], 5 * a₁ + 1 = 0) ∧
    (∃! a₂ : ℤ_[3], a₂ ^ 2 = 7 ∧ ‖a₂ - 1‖ < 1) ∧
    (∀ a₁ : ℤ_[3], 5 * a₁ + 1 = 0 → ‖(16 : ℤ_[3]) - a₁‖ ≤ (3 : ℝ) ^ (-3 : ℤ)) ∧
    (∀ a₂ : ℤ_[3], a₂ ^ 2 = 7 → ‖a₂ - 1‖ < 1 → ‖(13 : ℤ_[3]) - a₂‖ ≤ (3 : ℝ) ^ (-3 : ℤ)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have n5 : ‖(5 : ℤ_[3])‖ = 1 := by
    have := norm_intCast_eq_one (p := 3) (n := 5) (by norm_num)
    simpa using this
  have n14 : ‖(14 : ℤ_[3])‖ = 1 := by
    have := norm_intCast_eq_one (p := 3) (n := 14) (by norm_num)
    simpa using this
  have n81 : ‖(81 : ℤ_[3])‖ ≤ (3 : ℝ) ^ (-3 : ℤ) := by
    have := (PadicInt.norm_int_le_pow_iff_dvd (p := 3) (k := 81) (n := 3)).2 (by norm_num)
    simpa using this
  have n162 : ‖(162 : ℤ_[3])‖ ≤ (3 : ℝ) ^ (-3 : ℤ) := by
    have := (PadicInt.norm_int_le_pow_iff_dvd (p := 3) (k := 162) (n := 3)).2 (by norm_num)
    simpa using this
  have u5 : IsUnit (5 : ℤ_[3]) := PadicInt.isUnit_iff.mpr n5
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (5 : ℤ_[3]) * ((u5.unit⁻¹ : ℤ_[3]ˣ) : ℤ_[3]) = 1 := by
      have := u5.unit.mul_inv
      simp
    have h5 : (5 : ℤ_[3]) ≠ 0 := fun h => by simp [h] at n5
    refine ⟨-((u5.unit⁻¹ : ℤ_[3]ˣ) : ℤ_[3]), by linear_combination -h1, ?_⟩
    intro y hy
    have : (5 : ℤ_[3]) * (y - -((u5.unit⁻¹ : ℤ_[3]ˣ) : ℤ_[3])) = 0 := by linear_combination hy + h1
    have := (mul_eq_zero.mp this).resolve_left h5
    linear_combination this
  · have h2 : (2 : ℤ_[3]) ≠ 0 := fun h => by
      have := norm_intCast_eq_one (p := 3) (n := 2) (by norm_num)
      simp [h] at this
    have n2 : ‖(2 : ℤ_[3])‖ = 1 := by
      have := norm_intCast_eq_one (p := 3) (n := 2) (by norm_num)
      simpa using this
    have n6 : ‖(6 : ℤ_[3])‖ < 1 := by
      have := (PadicInt.norm_int_lt_one_iff_dvd (p := 3) 6).2 (by norm_num)
      simpa using this
    have hd : (Polynomial.X ^ 2 - Polynomial.C 7 : Polynomial ℤ_[3]).derivative.aeval (1 : ℤ_[3]) = 2 := by
      simp; norm_num
    have hv : (Polynomial.X ^ 2 - Polynomial.C 7 : Polynomial ℤ_[3]).aeval (1 : ℤ_[3]) = -6 := by
      simp; norm_num
    have hn : ‖(Polynomial.X ^ 2 - Polynomial.C 7 : Polynomial ℤ_[3]).aeval (1 : ℤ_[3])‖ <
        ‖(Polynomial.X ^ 2 - Polynomial.C 7 : Polynomial ℤ_[3]).derivative.aeval (1 : ℤ_[3])‖ ^ 2 := by
      rw [hd, hv, norm_neg, n2]; simpa using n6
    obtain ⟨z, hz, hz1, -, huniq⟩ := hensels_lemma hn
    have hz' : z ^ 2 = 7 := by simp at hz; linear_combination hz
    rw [hd, n2] at hz1
    refine ⟨z, ⟨hz', hz1⟩, ?_⟩
    rintro y ⟨hy, hy1⟩
    exact huniq y (by simp; linear_combination hy) (by rw [hd, n2]; exact hy1)
  · intro a₁ h
    have e : (5 : ℤ_[3]) * (16 - a₁) = 81 := by linear_combination -h
    have := congrArg norm e
    rw [norm_mul, n5, one_mul] at this
    rw [this]; exact n81
  · intro a₂ h hn
    have e : (13 - a₂) * (13 + a₂) = 162 := by linear_combination -h
    have n13 : ‖(13 : ℤ_[3]) + a₂‖ = 1 := by
      have e2 : (13 : ℤ_[3]) + a₂ = 14 + (a₂ - 1) := by ring
      rw [e2]
      by_contra hne
      have hlt : ‖(14 : ℤ_[3]) + (a₂ - 1)‖ < 1 :=
        lt_of_le_of_ne (PadicInt.norm_le_one _) hne
      have : ‖(14 : ℤ_[3])‖ ≤ max ‖(14 : ℤ_[3]) + (a₂ - 1)‖ ‖a₂ - 1‖ := by
        have h := PadicInt.nonarchimedean ((14 : ℤ_[3]) + (a₂ - 1)) (-(a₂ - 1))
        rw [show (14 : ℤ_[3]) + (a₂ - 1) + -(a₂ - 1) = 14 by ring, norm_neg] at h
        exact h
      rw [n14] at this
      exact absurd (lt_of_le_of_lt this (max_lt hlt hn)) (lt_irrefl _)
    have := congrArg norm e
    rw [norm_mul, n13, mul_one] at this
    rw [this]; exact n162

/-- Helper: in $\mathbb Z/7$ an element $s$ is $5t^2$ for some $t$ if and only if $s$ is a nonzero non-square
(so $5$ is a quadratic non-residue modulo $7$). -/
theorem five_mul_sq_iff (s : ZMod 7) (hs : s ≠ 0) : (∃ t : ZMod 7, 5 * t ^ 2 = s) ↔ ¬ IsSquare s := by
  revert s; decide

/-- Helper: for an integer $u$ not divisible by $7$, $5y^2 = u$ is soluble in $\mathbb Z_7$ if and only if
$u$ is a quadratic non-residue modulo $7$ (Hensel's lemma for the "if" direction). -/
theorem unit_case (u : ℤ) (hu : ¬ (7 : ℤ) ∣ u) :
    (∃ y : ℤ_[7], 5 * y ^ 2 = (u : ℤ_[7])) ↔ ¬ IsSquare (u : ZMod 7) := by
  have hu0 : (u : ZMod 7) ≠ 0 := fun h =>
    hu (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd u 7).mp h)
  rw [← five_mul_sq_iff _ hu0]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨PadicInt.toZMod y, ?_⟩
    have := congrArg (PadicInt.toZMod (p := 7)) hy
    have h5 : PadicInt.toZMod (p := 7) 5 = 5 := map_ofNat _ 5
    simpa [h5] using this
  · rintro ⟨t, ht⟩
    set t0 : ℤ := (t.val : ℤ) with ht0
    have hc : ((t0 : ℤ) : ZMod 7) = t := by simp [ht0]
    have hd : (7 : ℤ) ∣ 5 * t0 ^ 2 - u := by
      have : ((5 * t0 ^ 2 - u : ℤ) : ZMod 7) = 0 := by push_cast; rw [hc, ht]; ring
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp this
    have hd2 : ¬ (7 : ℤ) ∣ 10 * t0 := by
      intro h
      have h1 : ((10 * t0 : ℤ) : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr (by exact_mod_cast h)
      have h2 : (10 : ZMod 7) * t = 0 := by push_cast at h1; rwa [hc] at h1
      have key : ∀ t : ZMod 7, 10 * t = 0 → t = 0 := by decide
      have h3 : t = 0 := key t h2
      apply hu0; rw [← ht, h3]; ring
    have hn : ‖(Polynomial.C (5 : ℤ_[7]) * Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[7])).aeval (t0 : ℤ_[7])‖ <
        ‖(Polynomial.C (5 : ℤ_[7]) * Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[7])).derivative.aeval
          (t0 : ℤ_[7])‖ ^ 2 := by
      have e1 : (Polynomial.C (5 : ℤ_[7]) * Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[7])).aeval (t0 : ℤ_[7])
          = ((5 * t0 ^ 2 - u : ℤ) : ℤ_[7]) := by simp
      have e2 : (Polynomial.C (5 : ℤ_[7]) * Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[7])).derivative.aeval
          (t0 : ℤ_[7]) = ((10 * t0 : ℤ) : ℤ_[7]) := by
        simp; ring
      rw [e1, e2, norm_intCast_eq_one hd2]
      simpa using (PadicInt.norm_int_lt_one_iff_dvd (p := 7) _).2 hd
    obtain ⟨z, hz, -⟩ := hensels_lemma hn
    refine ⟨z, ?_⟩
    simp at hz
    linear_combination hz

/-- Helper: the decomposition $a = 7^{v} u$ with $v = v_7(a)$ and $7 \nmid u$, for a nonzero integer $a$. -/
theorem decomp (a : ℤ) (ha : a ≠ 0) :
    (7 : ℤ) ^ padicValInt 7 a * (a / 7 ^ padicValInt 7 a) = a ∧
      ¬ (7 : ℤ) ∣ a / 7 ^ padicValInt 7 a := by
  have hd : (7 : ℤ) ^ padicValInt 7 a ∣ a := padicValInt_dvd a
  refine ⟨Int.mul_ediv_cancel' hd, fun h => ?_⟩
  obtain ⟨w, hw⟩ := h
  have : ((7 : ℕ) : ℤ) ^ (padicValInt 7 a + 1) ∣ a := by
    refine ⟨w, ?_⟩
    have := (Int.mul_ediv_cancel' hd).symm
    rw [hw] at this
    push_cast
    linear_combination this
  rcases (padicValInt_dvd_iff (p := 7) _ a).mp this with h | h
  · exact ha h
  · omega

/-- Helper: if $a \ne 0$ is an integer with $v_7(a)$ even and $a / 7^{v_7(a)}$ a non-residue mod $7$, then
$5x^2 = a$ has a solution in $\mathbb Z_7$. -/
theorem solvable_of_cond (a : ℤ) (ha : a ≠ 0) (hev : Even (padicValInt 7 a))
    (hnr : ¬ IsSquare ((a / 7 ^ padicValInt 7 a : ℤ) : ZMod 7)) :
    ∃ x : ℤ_[7], 5 * x ^ 2 = (a : ℤ_[7]) := by
  obtain ⟨h1, h2⟩ := decomp a ha
  obtain ⟨y, hy⟩ := (unit_case _ h2).mpr hnr
  obtain ⟨k, hk⟩ := hev
  refine ⟨(7 : ℤ_[7]) ^ k * y, ?_⟩
  have : (a : ℤ_[7]) = (7 : ℤ_[7]) ^ (k + k) * ((a / 7 ^ padicValInt 7 a : ℤ) : ℤ_[7]) := by
    conv_lhs => rw [← h1]
    rw [hk]; push_cast; ring
  rw [this, ← hy]; ring

/-- Helper: if $5x^2 = a$ has a solution in $\mathbb Q_7$ with $a \ne 0$ an integer, then $v_7(a)$ is even and
$a / 7^{v_7(a)}$ is a non-residue mod $7$. -/
theorem cond_of_solvable (a : ℤ) (ha : a ≠ 0) (x : ℚ_[7]) (hx : 5 * x ^ 2 = (a : ℚ_[7])) :
    Even (padicValInt 7 a) ∧ ¬ IsSquare ((a / 7 ^ padicValInt 7 a : ℤ) : ZMod 7) := by
  obtain ⟨h1, h2⟩ := decomp a ha
  set v := padicValInt 7 a with hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply ha; exact_mod_cast (by simpa using hx.symm : (a : ℚ_[7]) = 0)
  have hn5 : ‖(5 : ℚ_[7])‖ = 1 := by
    have := Padic.norm_natCast_eq_one_iff (p := 7) (n := 5)
    simpa using this.2 (by norm_num)
  -- the norm of `a`
  have hna : ‖(a : ℚ_[7])‖ = (7 : ℝ) ^ (-(v : ℤ)) := by
    have h : ‖((a : ℚ) : ℚ_[7])‖ = padicNorm 7 (a : ℚ) := Padic.eq_padicNorm _
    have hq : ((a : ℚ) : ℚ_[7]) = (a : ℚ_[7]) := by norm_cast
    rw [hq] at h
    rw [h, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast ha), padicValRat.of_int]
    rw [hv]; push_cast; rfl
  have hnx : ‖(a : ℚ_[7])‖ = (7 : ℝ) ^ (-(2 * x.valuation)) := by
    rw [← hx, norm_mul, hn5, one_mul, norm_pow, Padic.norm_eq_zpow_neg_valuation hx0, ← zpow_natCast,
      ← zpow_mul]
    norm_num
    ring_nf
  have hvm : (v : ℤ) = 2 * x.valuation := by
    have := hna.symm.trans hnx
    have h7 : (1 : ℝ) < 7 := by norm_num
    have := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 7) (by norm_num : (7 : ℝ) ≠ 1) this
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x.valuation = k := ⟨x.valuation.toNat, by omega⟩
  have hvk : v = k + k := by omega
  refine ⟨⟨k, hvk⟩, ?_⟩
  rw [← unit_case _ h2]
  have hy : ‖x / (7 : ℚ_[7]) ^ k‖ ≤ 1 := by
    rw [norm_div, norm_pow, Padic.norm_eq_zpow_neg_valuation hx0, hk]
    have : ‖(7 : ℚ_[7])‖ = (7 : ℝ)⁻¹ := by simpa using Padic.norm_p (p := 7)
    rw [this]
    simp
  refine ⟨⟨x / (7 : ℚ_[7]) ^ k, hy⟩, ?_⟩
  apply PadicInt.ext
  have h7 : (7 : ℚ_[7]) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha' : (a : ℚ_[7]) = (7 : ℚ_[7]) ^ (k + k) * ((a / 7 ^ v : ℤ) : ℚ_[7]) := by
    conv_lhs => rw [← h1]
    rw [hvk]; push_cast; ring
  have : (7 : ℚ_[7]) ^ (k + k) * ((a / 7 ^ v : ℤ) : ℚ_[7]) = 5 * x ^ 2 := by rw [← ha', hx]
  have hz : ((⟨x / (7 : ℚ_[7]) ^ k, hy⟩ : ℤ_[7]) : ℚ_[7]) = x / 7 ^ k := rfl
  change (5 : ℚ_[7]) * ((⟨x / (7 : ℚ_[7]) ^ k, hy⟩ : ℤ_[7]) : ℚ_[7]) ^ 2 = ((a / 7 ^ v : ℤ) : ℚ_[7])
  rw [hz, div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero 2 h7)]
  linear_combination (-1) * this

/-- **Cassels, Ch. 3, Ex. 2 (p. 49), $\mathbb Z_7$ part.** For an integer $a$, the equation $5x^2 = a$ has a solution
$x \in \mathbb Z_7$ if and only if $a = 0$, or $v_7(a)$ is even and $a / 7^{v_7(a)}$ is a quadratic non-residue
modulo $7$. -/
@[kb "cassels1978" "Ch. 3, Ex. 2, p. 49"]
theorem ex2_padicInt (a : ℤ) :
    (∃ x : ℤ_[7], 5 * x ^ 2 = (a : ℤ_[7])) ↔
      a = 0 ∨ (Even (padicValInt 7 a) ∧ ¬ IsSquare ((a / 7 ^ padicValInt 7 a : ℤ) : ZMod 7)) := by
  by_cases ha : a = 0
  · subst ha; simp only [true_or, iff_true]; exact ⟨0, by simp⟩
  · simp only [ha, false_or]
    constructor
    · rintro ⟨x, hx⟩
      exact cond_of_solvable a ha (x : ℚ_[7]) (by exact_mod_cast congrArg (fun z : ℤ_[7] => (z : ℚ_[7])) hx)
    · rintro ⟨h1, h2⟩; exact solvable_of_cond a ha h1 h2

/-- **Cassels, Ch. 3, Ex. 2 (p. 49), $\mathbb Q_7$ part.** For an integer $a$, the equation $5x^2 = a$ has a solution
$x \in \mathbb Q_7$ if and only if $a = 0$, or $v_7(a)$ is even and $a / 7^{v_7(a)}$ is a quadratic non-residue
modulo $7$ (the same condition as in $\mathbb Z_7$). -/
@[kb "cassels1978" "Ch. 3, Ex. 2, p. 49"]
theorem ex2_padic (a : ℤ) :
    (∃ x : ℚ_[7], 5 * x ^ 2 = (a : ℚ_[7])) ↔
      a = 0 ∨ (Even (padicValInt 7 a) ∧ ¬ IsSquare ((a / 7 ^ padicValInt 7 a : ℤ) : ZMod 7)) := by
  by_cases ha : a = 0
  · subst ha; simp only [true_or, iff_true]; exact ⟨0, by simp⟩
  · simp only [ha, false_or]
    constructor
    · rintro ⟨x, hx⟩; exact cond_of_solvable a ha x hx
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx⟩ := solvable_of_cond a ha h1 h2
      exact ⟨x, by exact_mod_cast congrArg (fun z : ℤ_[7] => (z : ℚ_[7])) hx⟩

/-- **Cassels, Ch. 3, Ex. 3 (p. 49).** There are integers $a, b$ with $|a^2 + 6b^2 - 5|_5 \le 5^{-4}$; for
example $a = 1$, $b = 172$ (here $a^2 + 6b^2 - 5 = 625 \cdot 284$). -/
@[kb "cassels1978" "Ch. 3, Ex. 3, p. 49"]
theorem ex3 :
    ∃ a b : ℤ, ‖(a : ℚ_[5]) ^ 2 + 6 * (b : ℚ_[5]) ^ 2 - 5‖ ≤ (5 : ℝ) ^ (-4 : ℤ) := by
  refine ⟨1, 172, ?_⟩
  have h := (Padic.norm_int_le_pow_iff_dvd (p := 5) (1 ^ 2 + 6 * 172 ^ 2 - 5) 4).2 (by norm_num)
  have e : ((1 : ℤ) : ℚ_[5]) ^ 2 + 6 * ((172 : ℤ) : ℚ_[5]) ^ 2 - 5 = ((1 ^ 2 + 6 * 172 ^ 2 - 5 : ℤ) : ℚ_[5]) := by
    push_cast; ring
  rw [e]
  exact_mod_cast h

/-- **Cassels, Ch. 3, Ex. 4 (p. 49), first part.** For every prime $p$ and $c \in \mathbb Z_p$ with $|c|_p < 1$,
$$\frac{1}{1 + c} = 1 - c + c^2 - c^3 + \cdots,$$
the series converging in $\mathbb Q_p$ (`HasSum` of the terms $(-c)^n$, $n \ge 0$). -/
@[kb "cassels1978" "Ch. 3, Ex. 4, p. 49"]
theorem ex4_geometric (c : ℤ_[p]) (hc : ‖c‖ < 1) :
    HasSum (fun n : ℕ => (-(c : ℚ_[p])) ^ n) ((1 + (c : ℚ_[p]))⁻¹) := by
  have h : ‖-(c : ℚ_[p])‖ < 1 := by rw [norm_neg, ← PadicInt.norm_def]; exact hc
  simpa using hasSum_geometric_of_norm_lt_one h

/-- **Cassels, Ch. 3, Ex. 4 (p. 49), second part.** There is an integer $a$ with $|1/4 - a|_5 \le 5^{-10}$; for
example $a = 7324219$ ($4a \equiv 1 \pmod{5^{10}}$). -/
@[kb "cassels1978" "Ch. 3, Ex. 4, p. 49"]
theorem ex4_approx : ∃ a : ℤ, ‖(1 / 4 : ℚ_[5]) - (a : ℚ_[5])‖ ≤ (5 : ℝ) ^ (-10 : ℤ) := by
  refine ⟨7324219, ?_⟩
  have h := (Padic.norm_int_le_pow_iff_dvd (p := 5) (1 - 4 * 7324219) 10).2 (by norm_num)
  have n4 : ‖(4 : ℚ_[5])‖ = 1 := by
    have := Padic.norm_natCast_eq_one_iff (p := 5) (n := 4)
    simpa using this.2 (by norm_num)
  have e : (1 / 4 : ℚ_[5]) - ((7324219 : ℤ) : ℚ_[5]) = (4 : ℚ_[5])⁻¹ * ((1 - 4 * 7324219 : ℤ) : ℚ_[5]) := by
    push_cast; field_simp; norm_num
  rw [e, norm_mul, norm_inv, n4]
  simpa using h

/-- **Cassels, Ch. 3, Ex. 7 (p. 50).** There is an integer $u$ with $|u^2 + 7|_2 \le 2^{-10}$; for example
$u = 181$ ($181^2 + 7 = 2^{10} \cdot 32$). -/
@[kb "cassels1978" "Ch. 3, Ex. 7, p. 50"]
theorem ex7 : ∃ u : ℤ, ‖(u : ℚ_[2]) ^ 2 + 7‖ ≤ (2 : ℝ) ^ (-10 : ℤ) := by
  refine ⟨181, ?_⟩
  have h := (Padic.norm_int_le_pow_iff_dvd (p := 2) (181 ^ 2 + 7) 10).2 (by norm_num)
  have e : ((181 : ℤ) : ℚ_[2]) ^ 2 + 7 = ((181 ^ 2 + 7 : ℤ) : ℚ_[2]) := by push_cast; ring
  rw [e]
  exact_mod_cast h

/-- Helper: from $(-1, a)_K\,(a, a)_K = 1$ and $(\cdot,\cdot)_K^2 = 1$ get $(a,a)_K = (a,-1)_K$. -/
theorem aa_eq_of_mul_eq_one (K : Type*) [Field K] (a : K)
    (h : hilbertSymbol K (-1) a * hilbertSymbol K a a = 1) :
    hilbertSymbol K a a = hilbertSymbol K a (-1) := by
  rw [hilbertSymbol_comm K a (-1)]
  have hs := Cassels.Ch3Ex.hilbertSymbol_sq K (-1) a
  linear_combination (-(hilbertSymbol K a a)) * hs + (hilbertSymbol K (-1) a) * h

/-- **Cassels, Ch. 3, Ex. 9 (p. 50), over $\mathbb Q_p$.** For every prime $p$: for $a \in \mathbb Q_p$ with
$a \ne 0$ and $a \ne -1$ (so that both entries are nonzero), $(a + 1, -a)_p = 1$; and for $a \ne 0$,
$(a, a)_p = (a, -1)_p$.

*Erratum:* the printed hypothesis is "$a \ne 0, 1$". The first identity needs $a + 1 \ne 0$, i.e. $a \ne -1$ (for
$a = -1$ the symbol $(0, 1)_p$ is undefined), while $a = 1$ is harmless ($(2, -1)_p = 1$). Confirmed by the proof: it
uses $z^2 = (a+1)x^2 + (-a)y^2$ with $x = y = z = 1$. -/
@[kb "cassels1978" "Ch. 3, Ex. 9, p. 50"]
theorem ex9_padic :
    (∀ a : ℚ_[p], a ≠ 0 → a ≠ -1 → hilbertSymbol ℚ_[p] (a + 1) (-a) = 1) ∧
    (∀ a : ℚ_[p], a ≠ 0 → hilbertSymbol ℚ_[p] a a = hilbertSymbol ℚ_[p] a (-1)) := by
  refine ⟨fun a _ _ => ?_, fun a ha => ?_⟩
  · have hex : ∃ x y z : _, (x, y, z) ≠ 0 ∧ z ^ 2 = (a + 1) * x ^ 2 + (-a) * y ^ 2 :=
      ⟨1, 1, 1, by simp, by ring⟩
    simp only [hilbertSymbol, hex, ite_true]
  · apply aa_eq_of_mul_eq_one
    have hm1 : (-1 : ℚ_[p]) ≠ 0 := by norm_num
    have h1 := hilbertSymbol_self_neg ℚ_[p] a
    rw [hilbertSymbol_comm, show -a = (-1) * a by ring,
      HilbertLocal.hilbertSymbol_padic_mul_left _ _ _ hm1 ha ha] at h1
    exact h1

/-- **Cassels, Ch. 3, Ex. 9 (p. 50), over $\mathbb R$** (the place $p = \infty$). For $a \in \mathbb R$,
$a \ne 0, -1$: $(a+1, -a)_{\mathbb R} = 1$; for $a \ne 0$: $(a, a)_{\mathbb R} = (a, -1)_{\mathbb R}$. See the
*Erratum* on `ex9_padic` for the hypothesis. -/
@[kb "cassels1978" "Ch. 3, Ex. 9, p. 50"]
theorem ex9_real :
    (∀ a : ℝ, a ≠ 0 → a ≠ -1 → hilbertSymbol ℝ (a + 1) (-a) = 1) ∧
    (∀ a : ℝ, a ≠ 0 → hilbertSymbol ℝ a a = hilbertSymbol ℝ a (-1)) := by
  refine ⟨fun a _ _ => ?_, fun a ha => ?_⟩
  · have hex : ∃ x y z : _, (x, y, z) ≠ 0 ∧ z ^ 2 = (a + 1) * x ^ 2 + (-a) * y ^ 2 :=
      ⟨1, 1, 1, by simp, by ring⟩
    simp only [hilbertSymbol, hex, ite_true]
  · apply aa_eq_of_mul_eq_one
    have hm1 : (-1 : ℝ) ≠ 0 := by norm_num
    have h1 := hilbertSymbol_self_neg ℝ a
    rw [hilbertSymbol_comm, show -a = (-1) * a by ring,
      HilbertLocal.hilbertSymbol_real_mul_left _ _ _ hm1 ha ha] at h1
    exact h1

end QuadFormsKB.Cassels.Ch3Scan
