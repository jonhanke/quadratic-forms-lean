/-
# Cassels, Chapter 14, §6: the negative Pell equation for $D = 4rs$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §6, pp. 350–352 (the worked example $D = 4rs$, 14.r12).

Let $r \ne s$ be primes with $r \equiv s \equiv 1 \pmod 4$. Cassels studies the forms of discriminant $4rs$ and the
ambiguous forms $f(1) = [1, 0, -rs]$, $f(-1) = [-1, 0, rs]$, $f(r) = [r, 0, -s]$, $f(s) = [s, 0, -r]$; exactly one
of $f(-1), f(r), f(s)$ is equivalent to $f(1)$, i.e. represents $1$. He concludes:

* if $(r/s) = -1$, then $x^2 - rsy^2 = -1$ is soluble (p. 351, `exists_negPell_of_legendreSym`);
* if $(r/s) = 1$ and neither $s$ is a fourth power modulo $r$ nor $r$ modulo $s$ (the conditional biquadratic
  symbols $[s/r]_4 = [r/s]_4 = -1$, p. 351), then $x^2 - rsy^2 = -1$ is soluble (case (i), p. 352,
  `exists_negPell_of_not_biquadratic`).

*Proof route.* Cassels argues with the class group and the kernel of $\mathcal B \to \mathcal A$ (Lemma 6.1, Lemma 4.3),
which are not formalized here. The proofs below are the elementary form of the same argument (Legendre's): for the
least solution $x^2 - rsy^2 = 1$ with $y > 0$, $x$ is odd and $\frac{x+1}2 \cdot \frac{x-1}2 = rs\,(\frac y2)^2$ with
coprime factors, so $\alpha u^2 - \beta v^2 = 1$ with $\alpha\beta = rs$; $\alpha = 1$ contradicts minimality,
$\alpha = rs$ solves the negative equation, and $\alpha \in \{r, s\}$ is the representation of $1$ by $f(r)$ or
$-f(s)$, excluded by the hypotheses (Cassels' evaluation of $(w/r)$, p. 352, with $w = 1$).
-/
import QuadFormsKB.Defs.QuadForm

namespace QuadFormsKB.Composition

/-- Coprime positive integers whose product is a square are both squares of positive integers. -/
lemma sq_of_coprime_pos {a b z : ℤ} (h : IsCoprime a b) (hab : a * b = z ^ 2) (ha : 0 < a)
    (hb : 0 < b) : ∃ u v : ℤ, 0 < u ∧ 0 < v ∧ a = u ^ 2 ∧ b = v ^ 2 := by
  have key : ∀ {a b : ℤ}, IsCoprime a b → a * b = z ^ 2 → 0 < a → ∃ u : ℤ, 0 < u ∧ a = u ^ 2 := by
    intro a b h hab ha
    obtain ⟨a0, h0 | h0⟩ := Int.sq_of_isCoprime h hab
    · refine ⟨|a0|, ?_, by rw [sq_abs]; exact h0⟩
      rcases eq_or_ne a0 0 with rfl | hne
      · simp at h0; omega
      · exact abs_pos.mpr hne
    · nlinarith [sq_nonneg a0]
  obtain ⟨u, hu, hu'⟩ := key h hab ha
  obtain ⟨v, hv, hv'⟩ := key h.symm (by rw [mul_comm]; exact hab) hb
  exact ⟨u, v, hu, hv, hu', hv'⟩

/-- Splitting lemma: coprime `A, B > 0` with `A B = α β z²`, `α ∣ A`, `β ∣ B`, are `α u²`, `β v²`
with `z = u v`. -/
lemma split_case {A B z α β : ℤ} (hα : 0 < α) (hβ : 0 < β) (hcop : IsCoprime A B) (hA : α ∣ A)
    (hB : β ∣ B) (hAB : A * B = α * β * z ^ 2) (hA0 : 0 < A) (hB0 : 0 < B) (hz : 0 < z) :
    ∃ u v : ℤ, 0 < u ∧ 0 < v ∧ A = α * u ^ 2 ∧ B = β * v ^ 2 ∧ z = u * v := by
  obtain ⟨A', rfl⟩ := hA
  obtain ⟨B', rfl⟩ := hB
  have h1 : A' * B' = z ^ 2 := by
    have : α * β * (A' * B') = α * β * z ^ 2 := by rw [← hAB]; ring
    exact mul_left_cancel₀ (mul_pos hα hβ).ne' this
  have hc : IsCoprime A' B' := (hcop.of_mul_left_right).of_mul_right_right
  have hA' : 0 < A' := (mul_pos_iff_of_pos_left hα).mp hA0
  have hB' : 0 < B' := (mul_pos_iff_of_pos_left hβ).mp hB0
  obtain ⟨u, v, hu, hv, rfl, rfl⟩ := sq_of_coprime_pos hc h1 hA' hB'
  refine ⟨u, v, hu, hv, rfl, rfl, ?_⟩
  have : (z - u * v) * (z + u * v) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · nlinarith [mul_pos hu hv]

/-- `N y² mod 4` for `N ≡ 1 (mod 4)` is `0` or `1`. -/
lemma mul_sq_mod4 (N y : ℤ) (hN : N % 4 = 1) : (N * y ^ 2) % 4 = 0 ∨ (N * y ^ 2) % 4 = 1 := by
  have h2 : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
    have h4 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
    rcases h4 with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
  rw [Int.mul_emod, hN]
  rcases h2 with h | h <;> simp [h]

/-- Descent step for `x² - r s y² = 1`, `y > 0`: either the negative equation is soluble, or there is
a smaller solution, or `r u² - s v² = 1`, or `s u² - r v² = 1` is soluble. -/
lemma pell_step {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hr4 : r % 4 = 1) (hs4 : s % 4 = 1)
    (hrs : r ≠ s) (x y : ℤ) (hx : x ^ 2 - (r * s : ℤ) * y ^ 2 = 1) (hy : 0 < y) :
    (∃ u v : ℤ, u ^ 2 - (r * s : ℤ) * v ^ 2 = -1) ∨
    (∃ u v : ℤ, 0 < v ∧ v < y ∧ u ^ 2 - (r * s : ℤ) * v ^ 2 = 1) ∨
    (∃ u v : ℤ, (r : ℤ) * u ^ 2 - s * v ^ 2 = 1) ∨ (∃ u v : ℤ, (s : ℤ) * u ^ 2 - r * v ^ 2 = 1) := by
  have hrpos : (0 : ℤ) < r := by exact_mod_cast hr.pos
  have hspos : (0 : ℤ) < s := by exact_mod_cast hs.pos
  have hNpos : (0 : ℤ) < r * s := mul_pos hrpos hspos
  have hN4 : ((r * s : ℤ)) % 4 = 1 := by
    have h1 : (r : ℤ) % 4 = 1 := by omega
    have h2 : (s : ℤ) % 4 = 1 := by omega
    rw [Int.mul_emod, h1, h2]; norm_num
  -- x > 0
  obtain ⟨x, hxpos, hx⟩ : ∃ x : ℤ, 0 < x ∧ x ^ 2 - (r * s : ℤ) * y ^ 2 = 1 := by
    refine ⟨|x|, ?_, by rwa [sq_abs]⟩
    rcases eq_or_ne x 0 with rfl | hne
    · nlinarith [mul_pos hNpos (mul_pos hy hy)]
    · exact abs_pos.mpr hne
  -- x odd
  have hxodd : x % 2 = 1 := by
    by_contra hne
    have : x % 2 = 0 := by omega
    obtain ⟨k, hk⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
    subst hk
    have := mul_sq_mod4 _ y hN4
    have h3 : (r * s : ℤ) * y ^ 2 = 4 * k ^ 2 - 1 := by linarith
    omega
  obtain ⟨B, hB⟩ : ∃ B, x = 2 * B + 1 := ⟨x / 2, by omega⟩
  subst hB
  have hB1 : 1 ≤ B := by
    by_contra hlt
    have : B = 0 := by omega
    subst this
    nlinarith [mul_pos hNpos (mul_pos hy hy)]
  have h4 : 4 * (B * (B + 1)) = (r * s : ℤ) * y ^ 2 := by linarith
  have hyeven : y % 2 = 0 := by
    by_contra hne
    have hyo : y % 2 = 1 := by omega
    obtain ⟨t, ht⟩ : ∃ t, y = 2 * t + 1 := ⟨y / 2, by omega⟩
    have hNo : ((r * s : ℤ)) % 2 = 1 := by omega
    have : ((r * s : ℤ) * y ^ 2) % 2 = 1 := by
      rw [Int.mul_emod, hNo]
      have : y ^ 2 % 2 = 1 := by rw [pow_two, Int.mul_emod, hyo]; norm_num
      rw [this]; norm_num
    omega
  obtain ⟨z, hz⟩ : ∃ z, y = 2 * z := ⟨y / 2, by omega⟩
  subst hz
  have hz0 : 0 < z := by omega
  have hBz : B * (B + 1) = (r * s : ℤ) * z ^ 2 := by linarith
  have hcop : IsCoprime (B + 1) B := ⟨1, -1, by ring⟩
  have hrP : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  have hsP : Prime (s : ℤ) := Nat.prime_iff_prime_int.mp hs
  have hrsc : IsCoprime (r : ℤ) (s : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hr hs).mpr hrs)
  have hrd : (r : ℤ) ∣ B * (B + 1) := ⟨s * z ^ 2, by rw [hBz]; ring⟩
  have hsd : (s : ℤ) ∣ B * (B + 1) := ⟨r * z ^ 2, by rw [hBz]; ring⟩
  have hAB : (B + 1) * B = (r * s : ℤ) * z ^ 2 := by rw [mul_comm]; exact hBz
  have hB0 : 0 < B := by omega
  have hA0 : 0 < B + 1 := by omega
  have hdiff : (B + 1) - B = 1 := by ring
  rcases hrP.dvd_or_dvd hrd with hr1 | hr1 <;> rcases hsP.dvd_or_dvd hsd with hs1 | hs1
  · -- r ∣ B, s ∣ B
    obtain ⟨u, v, hu, hv, h1, h2, h3⟩ := split_case (α := 1) (β := (r * s : ℤ)) one_pos hNpos hcop
      (one_dvd _) (hrsc.mul_dvd hr1 hs1) (by rw [hAB]; ring) hA0 hB0 hz0
    right; left
    refine ⟨u, v, hv, ?_, by nlinarith⟩
    nlinarith
  · -- r ∣ B, s ∣ B + 1
    obtain ⟨u, v, hu, hv, h1, h2, h3⟩ := split_case (α := (s : ℤ)) (β := (r : ℤ)) hspos hrpos hcop
      hs1 hr1 (by rw [hAB]; ring) hA0 hB0 hz0
    right; right; right
    exact ⟨u, v, by nlinarith⟩
  · -- r ∣ B + 1, s ∣ B
    obtain ⟨u, v, hu, hv, h1, h2, h3⟩ := split_case (α := (r : ℤ)) (β := (s : ℤ)) hrpos hspos hcop
      hr1 hs1 (by linarith [hAB]) hA0 hB0 hz0
    right; right; left
    exact ⟨u, v, by nlinarith⟩
  · -- r ∣ B + 1, s ∣ B + 1
    obtain ⟨u, v, hu, hv, h1, h2, h3⟩ := split_case (α := (r * s : ℤ)) (β := 1) hNpos one_pos hcop
      (hrsc.mul_dvd hr1 hs1) (one_dvd _) (by rw [hAB]; ring) hA0 hB0 hz0
    left
    exact ⟨v, u, by nlinarith⟩

/-- Trichotomy: for primes `r ≠ s` congruent to `1` mod `4`, either `x² - r s y² = -1` is soluble, or
`r u² - s v² = 1` is, or `s u² - r v² = 1` is (Legendre's descent on the least Pell solution). -/
lemma negPell_trichotomy {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hr4 : r % 4 = 1)
    (hs4 : s % 4 = 1) (hrs : r ≠ s) :
    (∃ x y : ℤ, x ^ 2 - (r * s : ℤ) * y ^ 2 = -1) ∨
    (∃ u v : ℤ, (r : ℤ) * u ^ 2 - s * v ^ 2 = 1) ∨ (∃ u v : ℤ, (s : ℤ) * u ^ 2 - r * v ^ 2 = 1) := by
  have hrpos : (0 : ℤ) < r := by exact_mod_cast hr.pos
  have hspos : (0 : ℤ) < s := by exact_mod_cast hs.pos
  have hNpos : (0 : ℤ) < r * s := mul_pos hrpos hspos
  have hnsq : ¬ IsSquare ((r * s : ℤ)) := by
    rintro ⟨m, hm⟩
    have hrP : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
    have hrm : (r : ℤ) ∣ m := hrP.dvd_of_dvd_pow (n := 2) ⟨s, by rw [pow_two, ← hm]⟩
    obtain ⟨a, rfl⟩ := hrm
    have : (s : ℤ) = r * a ^ 2 := by
      have : (r : ℤ) * s = r * (r * a ^ 2) := by rw [hm]; ring
      exact mul_left_cancel₀ hrpos.ne' this
    have hd : (r : ℤ) ∣ s := ⟨a ^ 2, this⟩
    exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp (Int.natCast_dvd_natCast.mp hd))
  have main : ∀ n : ℕ, ∀ x y : ℤ, y = n → 0 < y → x ^ 2 - (r * s : ℤ) * y ^ 2 = 1 →
      (∃ x y : ℤ, x ^ 2 - (r * s : ℤ) * y ^ 2 = -1) ∨
      (∃ u v : ℤ, (r : ℤ) * u ^ 2 - s * v ^ 2 = 1) ∨
      (∃ u v : ℤ, (s : ℤ) * u ^ 2 - r * v ^ 2 = 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hyn hy hx
      rcases pell_step hr hs hr4 hs4 hrs x y hx hy with h | ⟨u, v, hv, hvy, huv⟩ | h | h
      · exact Or.inl h
      · lift v to ℕ using hv.le
        exact ih v (by omega) u v rfl hv huv
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  obtain ⟨x, y, hxy, hy0⟩ := Pell.exists_of_not_isSquare hNpos hnsq
  refine main (|y|).toNat x |y| (by simp) (abs_pos.mpr hy0) (by rwa [sq_abs])

/-- `a u² - p v² = 1` makes `a` a square modulo `p`, so `(a/p) = 1`. -/
lemma legendreSym_eq_one_of_rep {p : ℕ} [Fact p.Prime] (a u v : ℤ)
    (h : a * u ^ 2 - p * v ^ 2 = 1) : legendreSym p a = 1 := by
  have h1 : (a : ZMod p) * (u : ZMod p) ^ 2 = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) h
    simpa using this
  have hu : (u : ZMod p) ≠ 0 := by
    intro h0; rw [h0] at h1; simp at h1
  have ha : (a : ZMod p) ≠ 0 := by
    intro h0; rw [h0] at h1; simp at h1
  rw [legendreSym.eq_one_iff p ha]
  refine ⟨((u : ZMod p))⁻¹, ?_⟩
  have := eq_inv_of_mul_eq_one_left h1
  rw [this, sq, mul_inv]

/-- Mod 8 information on `r u² - s v² = 1` with `r ≡ s ≡ 1 (mod 4)`: `v` is even, and `v ≡ 2 (mod 4)`
if `r ≡ 5 (mod 8)`. -/
lemma mod8_facts (r s u v : ℤ) (hr : r % 4 = 1) (hs : s % 4 = 1) (h : r * u ^ 2 - s * v ^ 2 = 1) :
    v % 2 = 0 ∧ (r % 8 = 5 → v % 4 = 2) := by
  have sqm : ∀ t : ℤ, (t % 4 = 0 ∧ t ^ 2 % 8 = 0) ∨ (t % 4 = 1 ∧ t ^ 2 % 8 = 1) ∨
      (t % 4 = 2 ∧ t ^ 2 % 8 = 4) ∨ (t % 4 = 3 ∧ t ^ 2 % 8 = 1) := by
    intro t
    have h2 : t ^ 2 % 8 = ((t % 8) * (t % 8)) % 8 := by rw [pow_two, Int.mul_emod]
    have h8 : t % 8 = 0 ∨ t % 8 = 1 ∨ t % 8 = 2 ∨ t % 8 = 3 ∨ t % 8 = 4 ∨ t % 8 = 5 ∨
        t % 8 = 6 ∨ t % 8 = 7 := by omega
    rcases h8 with h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 <;> rw [h8] at h2 <;> omega
  have hra : (r * u ^ 2) % 8 = ((r % 8) * (u ^ 2 % 8)) % 8 := Int.mul_emod _ _ _
  have hsb : (s * v ^ 2) % 8 = ((s % 8) * (v ^ 2 % 8)) % 8 := Int.mul_emod _ _ _
  have hr8 : r % 8 = 1 ∨ r % 8 = 5 := by omega
  have hs8 : s % 8 = 1 ∨ s % 8 = 5 := by omega
  rcases sqm u with ⟨_, hu⟩ | ⟨_, hu⟩ | ⟨_, hu⟩ | ⟨_, hu⟩ <;>
  rcases sqm v with ⟨hv4, hv⟩ | ⟨hv4, hv⟩ | ⟨hv4, hv⟩ | ⟨hv4, hv⟩ <;>
  rcases hr8 with h8 | h8 <;> rcases hs8 with h8' | h8' <;>
  (rw [h8, hu] at hra; rw [h8', hv] at hsb; omega)

/-- If `r u² - s v² = 1` (`v : ℕ`) for primes `r ≡ s ≡ 1 (mod 4)`, then `s` is a fourth power mod `r`
(Cassels, p. 352, via `[-1/r]_4 = (2/r)` and the evaluation of `(v/r)`). -/
lemma fourth_power_nat {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hr : r % 4 = 1) (hs : s % 4 = 1)
    (u : ℤ) (v : ℕ) (h : (r : ℤ) * u ^ 2 - s * (v : ℤ) ^ 2 = 1) :
    ∃ b : ℤ, b ^ 4 ≡ s [ZMOD r] := by
  have hrp : r.Prime := Fact.out
  have hr2 : r ≠ 2 := by omega
  have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
  have hr4' : (r : ℤ) % 4 = 1 := by omega
  have hs4' : (s : ℤ) % 4 = 1 := by omega
  obtain ⟨hv2, hv4⟩ := mod8_facts r s u v hr4' hs4' h
  have hv0 : v ≠ 0 := by
    rintro rfl
    have h' : (r : ℤ) * u ^ 2 = 1 := by
      have := h; rw [Nat.cast_zero] at this; linarith
    have hd : (r : ℤ) ∣ 1 := ⟨u ^ 2, h'.symm⟩
    have hd' : r ∣ 1 := by exact_mod_cast hd
    exact hrp.ne_one (Nat.eq_one_of_dvd_one hd')
  obtain ⟨k, m, hm, hvkm⟩ := Nat.exists_eq_two_pow_mul_odd hv0
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : v = m := by rw [hvkm]; ring
    have := Nat.odd_iff.mp hm
    omega
  have hk5 : r % 8 = 5 → k = 1 := by
    intro h5
    by_contra hk1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h4 : v = 4 * (2 ^ j * m) := by rw [hvkm]; ring
    have := hv4 (by omega)
    omega
  have hv' : (v : ℤ) = 2 ^ k * m := by rw [hvkm]; push_cast; ring
  -- J(m | r) = 1
  have hJm : jacobiSym (m : ℤ) r = 1 := by
    have h1 : jacobiSym (r : ℤ) m = jacobiSym (m : ℤ) r :=
      jacobiSym.quadratic_reciprocity_one_mod_four hr hm
    rw [← h1]
    have hmod : ((r : ℤ) * u ^ 2) % (m : ℤ) = 1 % (m : ℤ) := by
      have : (1 : ℤ) ≡ r * u ^ 2 [ZMOD m] := by
        refine Int.modEq_iff_dvd.mpr ⟨s * 2 ^ (2 * k) * m, ?_⟩
        rw [hv'] at h
        linear_combination h
      exact this.symm
    have hcop : Int.gcd u m = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp ⟨r * u, -(s * 2 ^ (2 * k) * m), by
        rw [hv'] at h
        linear_combination h⟩
    calc jacobiSym (r : ℤ) m = jacobiSym (r : ℤ) m * jacobiSym (u ^ 2) m := by
          rw [jacobiSym.sq_one' hcop, mul_one]
      _ = jacobiSym ((r : ℤ) * u ^ 2) m := (jacobiSym.mul_left _ _ _).symm
      _ = jacobiSym 1 m := jacobiSym.mod_left' hmod
      _ = 1 := jacobiSym.one_left m
  have hJv : jacobiSym (v : ℤ) r = jacobiSym 2 r ^ k := by
    rw [hv', jacobiSym.mul_left, jacobiSym.pow_left, hJm, mul_one]
  have hc2 : jacobiSym 2 r = ZMod.χ₈ r := jacobiSym.at_two hrodd
  obtain ⟨i, hi⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : r % 4 ≠ 3)
  obtain ⟨I, hI⟩ : ∃ I : ℤ, (I : ZMod r) = i := ⟨i.val, by simp⟩
  have h2ne : (2 : ZMod r) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    have := Nat.le_of_dvd (by norm_num) h0'
    have := hrp.two_le
    omega
  have hine : i ≠ 0 := by
    rintro rfl; simp at hi
  have hJ2I : jacobiSym 2 r * jacobiSym I r = 1 := by
    rw [← jacobiSym.mul_left, ← jacobiSym.legendreSym.to_jacobiSym]
    have hne : (((2 * I : ℤ)) : ZMod r) ≠ 0 := by
      push_cast; rw [hI]; exact mul_ne_zero h2ne hine
    rw [legendreSym.eq_one_iff r hne]
    refine ⟨1 + i, ?_⟩
    push_cast; rw [hI]; linear_combination hi
  have hcast : -((s : ZMod r)) * (v : ZMod r) ^ 2 = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod r) h
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  have hvr : (v : ZMod r) ≠ 0 := by
    intro h0; rw [h0] at hcast; simp at hcast
  have hJ : jacobiSym (I * (v : ℤ)) r = 1 := by
    rw [jacobiSym.mul_left, hJv]
    have hr2' : r % 2 = 1 := by omega
    have h8 : r % 8 = 1 ∨ r % 8 = 5 := by omega
    rcases h8 with h8 | h8
    · have : jacobiSym 2 r = 1 := by
        rw [hc2, ZMod.χ₈_nat_eq_if_mod_eight]; simp [h8, hr2']
      rw [this] at hJ2I ⊢
      simpa using hJ2I
    · have : jacobiSym 2 r = -1 := by
        rw [hc2, ZMod.χ₈_nat_eq_if_mod_eight]; simp [h8, hr2']
      rw [this] at hJ2I
      rw [this, hk5 h8]
      linarith
  have hsq : IsSquare (((I * (v : ℤ) : ℤ)) : ZMod r) := by
    have hne : ((I * (v : ℤ) : ℤ) : ZMod r) ≠ 0 := by
      push_cast; rw [hI]; exact mul_ne_zero hine hvr
    exact (legendreSym.eq_one_iff r hne).mp (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hJ)
  obtain ⟨c, hc⟩ := hsq
  push_cast at hc
  rw [hI] at hc
  have hvinv : (v : ZMod r) * (v : ZMod r)⁻¹ = 1 := mul_inv_cancel₀ hvr
  have key : (c * (v : ZMod r)⁻¹) ^ 4 = (s : ZMod r) := by
    calc (c * (v : ZMod r)⁻¹) ^ 4 = (c * c) ^ 2 * ((v : ZMod r)⁻¹) ^ 4 := by ring
      _ = (i * v) ^ 2 * ((v : ZMod r)⁻¹) ^ 4 := by rw [← hc]
      _ = (i * i) * ((v : ZMod r) * (v : ZMod r)⁻¹) ^ 2 * ((v : ZMod r)⁻¹) ^ 2 := by ring
      _ = -(((v : ZMod r)⁻¹) ^ 2) := by rw [hvinv, ← hi]; ring
      _ = (s : ZMod r) := by
        linear_combination (((v : ZMod r)⁻¹) ^ 2) * hcast +
          (s : ZMod r) * ((v : ZMod r) * (v : ZMod r)⁻¹ + 1) * hvinv
  refine ⟨((c * (v : ZMod r)⁻¹).val : ℤ), (ZMod.intCast_eq_intCast_iff _ _ r).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact key

/-- If `r u² - s v² = 1` for primes `r ≡ s ≡ 1 (mod 4)`, then `s` is a fourth power mod `r`. -/
lemma fourth_power {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hr : r % 4 = 1) (hs : s % 4 = 1)
    (u v : ℤ) (h : (r : ℤ) * u ^ 2 - s * v ^ 2 = 1) : ∃ b : ℤ, b ^ 4 ≡ s [ZMOD r] :=
  fourth_power_nat hr hs u v.natAbs (by rw [Int.natAbs_sq]; exact h)

/-- **Cassels, Ch. 14, §6** (p. 351): *let $r, s$ be distinct primes with $r \equiv s \equiv 1 \pmod 4$ and
$(r/s) = -1$. Then there is an integral solution of $x^2 - rsy^2 = -1$.* Here $(r/s)$ is the Legendre symbol
`legendreSym s r`. -/
@[kb "cassels1978" "Ch. 14, §6, p. 351 (D = 4rs, (r/s) = −1: x² − rsy² = −1 is soluble)"]
theorem exists_negPell_of_legendreSym {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hr : r % 4 = 1) (hs : s % 4 = 1)
    (hrs : r ≠ s) (h : legendreSym s r = -1) : ∃ x y : ℤ, x ^ 2 - (r * s : ℤ) * y ^ 2 = -1 := by
  rcases negPell_trichotomy (Fact.out : r.Prime) (Fact.out : s.Prime) hr hs hrs with h1 | ⟨u, v, h1⟩ | ⟨u, v, h1⟩
  · exact h1
  · have := legendreSym_eq_one_of_rep (p := s) (r : ℤ) u v h1
    omega
  · have h2 := legendreSym_eq_one_of_rep (p := r) (s : ℤ) u v h1
    have h3 : legendreSym s (r : ℤ) = legendreSym r (s : ℤ) :=
      legendreSym.quadratic_reciprocity_one_mod_four hr (by omega)
    omega

/-- **Cassels, Ch. 14, §6, case (i)** (p. 352): *let $r, s$ be distinct primes with $r \equiv s \equiv 1 \pmod 4$ and
$(r/s) = 1$, and suppose that $[s/r]_4 = [r/s]_4 = -1$, i.e. $s$ is not a fourth power modulo $r$ and $r$ is not a
fourth power modulo $s$. Then $x^2 - rsy^2 = -1$ is soluble.* (Cassels' "conditional biquadratic symbol" $[a/p]_4$,
p. 351, is $1$ if $a \equiv b^4 \pmod p$ is soluble and $-1$ otherwise, for a quadratic residue $a$ of a prime
$p \equiv 1 \pmod 4$.) *Note:* the proof does not use $(r/s) = 1$ (if $(r/s) = -1$ the conclusion holds by
`exists_negPell_of_legendreSym`); the hypothesis is kept to match Cassels' case division, where it makes the symbols
$[s/r]_4, [r/s]_4$ defined. -/
@[kb "cassels1978" "Ch. 14, §6, p. 352, case (i) (x² − rsy² = −1 is soluble)"]
theorem exists_negPell_of_not_biquadratic {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hr : r % 4 = 1)
    (hs : s % 4 = 1) (hrs : r ≠ s) (_h : legendreSym s r = 1)
    (hsr4 : ¬ ∃ b : ℤ, b ^ 4 ≡ s [ZMOD r]) (hrs4 : ¬ ∃ b : ℤ, b ^ 4 ≡ r [ZMOD s]) :
    ∃ x y : ℤ, x ^ 2 - (r * s : ℤ) * y ^ 2 = -1 := by
  rcases negPell_trichotomy (Fact.out : r.Prime) (Fact.out : s.Prime) hr hs hrs with h1 | ⟨u, v, h1⟩ | ⟨u, v, h1⟩
  · exact h1
  · exact absurd (fourth_power hr hs u v h1) hsr4
  · exact absurd (fourth_power hs hr u v h1) hrs4

end QuadFormsKB.Composition
