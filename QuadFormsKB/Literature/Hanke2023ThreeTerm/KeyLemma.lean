import Mathlib
import QuadFormsKB.Citation

/-!
# Saha–Hanke, three-term theta relations: the Key Lemma (Lemma 5.7)

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1, §5.2, Definition 5.6 and Lemma 5.7, p. 10
(bib key `hanke2023threeterm`).

For $a, b \in \mathbb{Z}_{\ge 0}$ with $(a, b) \ne (0, 0)$, the non-negative integer solutions
$(x, y, z)$ of
$$\frac{a}{a+b}\, x + \frac{b}{a+b}\, y = z$$
are exactly the $\mathbb{Z}_{\ge 0}$-linear combinations of the *linset*
$L_{a,b} = \{L_1, L_2, L_3\}$, where $L_1 = (1,1,1)$, $L_2 = (a+b, 0, a)/\gcd(a,b)$ and
$L_3 = (0, a+b, b)/\gcd(a,b)$.

*Update (proof gap):* the printed proof of the forward direction uses "since $a, b > 0$" to rule out
$\min\{x_0, y_0, z_0\} = z_0 < \min\{x_0, y_0\}$, although the lemma allows $a = 0$ or $b = 0$.
The proof here avoids this: $z$ is a weighted average of $x$ and $y$, so it lies between them,
and the divisibility step only uses $\gcd(a + b, b) = \gcd(a, b) = 1$.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

/-- **Definition 5.6 (the linset $L_{a,b}$)**, as the list $[L_1, L_2, L_3]$ of vectors in
$\mathbb{N}^3$ (written as triples): $L_1 = (1,1,1)$, $L_2 = ((a+b)/g, 0, a/g)$ and
$L_3 = (0, (a+b)/g, b/g)$ with $g = \gcd(a, b)$. -/
@[kb "hanke2023threeterm" "§5.2, Definition 5.6, p. 10"]
def linset (a b : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 1), ((a + b) / Nat.gcd a b, 0, a / Nat.gcd a b),
    (0, (a + b) / Nat.gcd a b, b / Nat.gcd a b)]

/-- Integral form of equation (7): over $\mathbb{N}$, $a x + b y = (a+b) z$. -/
lemma eq7_iff_nat (a b x y z : ℕ) (hab : a + b ≠ 0) :
    ((a : ℚ) / (a + b) * x + (b : ℚ) / (a + b) * y = z) ↔ a * x + b * y = (a + b) * z := by
  have h : ((a : ℚ) + b) ≠ 0 := by exact_mod_cast hab
  constructor
  · intro e
    have : (a : ℚ) * x + b * y = (a + b) * z := by
      rw [← e]; field_simp
    exact_mod_cast this
  · intro e
    have e' : (a : ℚ) * x + b * y = (a + b) * z := by exact_mod_cast e
    field_simp
    linarith

/-- Coprime core of the Key Lemma: if $\gcd(a, b) = 1$ and $a x + b y = (a+b) z$ over
$\mathbb{N}$, then $(x, y, z) = c_1 (1,1,1) + c_2 (a+b, 0, a) + c_3 (0, a+b, b)$. -/
lemma key_coprime (a b x y z : ℕ) (hcop : Nat.Coprime a b) (e : a * x + b * y = (a + b) * z) :
    ∃ c₁ c₂ c₃ : ℕ, x = c₁ + c₂ * (a + b) ∧ y = c₁ + c₃ * (a + b) ∧
      z = c₁ + c₂ * a + c₃ * b := by
  rcases le_total x y with hxy | hyx
  · -- `x ≤ z ≤ y`, and `b (y - x) = (a + b) (z - x)`.
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    have hz : x ≤ z := by
      by_contra h
      push Not at h
      have : (a + b) * z < (a + b) * x ∨ a + b = 0 := by
        rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
        · exact Or.inr h0
        · exact Or.inl (Nat.mul_lt_mul_of_pos_left h h0)
      rcases this with h1 | h0
      · nlinarith
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha hb
        simp at hcop
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hz
    have e2 : b * d = (a + b) * w := by nlinarith
    have hc : Nat.Coprime (a + b) b := by
      simpa [Nat.coprime_add_self_left] using hcop
    have hdvd : (a + b) ∣ d := (Nat.Coprime.dvd_of_dvd_mul_right hc ⟨w, e2.symm ▸ by ring⟩)
    obtain ⟨k, rfl⟩ := hdvd
    refine ⟨x, 0, k, by ring, by ring, ?_⟩
    rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb; simp at hcop
    · have : w = b * k := by
        have : (a + b) * w = (a + b) * (b * k) := by rw [← e2]; ring
        exact Nat.eq_of_mul_eq_mul_left h0 this
      subst this; ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hyx
    have hz : y ≤ z := by
      by_contra h
      push Not at h
      rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha hb; simp at hcop
      · have := Nat.mul_lt_mul_of_pos_left h h0
        nlinarith
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hz
    have e2 : a * d = (a + b) * w := by nlinarith
    have hc : Nat.Coprime (a + b) a := by
      simpa [Nat.coprime_add_self_left, Nat.coprime_comm] using hcop.symm
    have hdvd : (a + b) ∣ d := (Nat.Coprime.dvd_of_dvd_mul_left hc ⟨w, e2.symm ▸ by ring⟩)
    obtain ⟨k, rfl⟩ := hdvd
    refine ⟨y, k, 0, by ring, by ring, ?_⟩
    rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb; simp at hcop
    · have : w = a * k := by
        have : (a + b) * w = (a + b) * (a * k) := by rw [← e2]; ring
        exact Nat.eq_of_mul_eq_mul_left h0 this
      subst this; ring

/-- **Lemma 5.7 (The Key Lemma).** Let $a, b \in \mathbb{Z}_{\ge 0}$ with $(a, b) \ne (0, 0)$ and
$g = \gcd(a, b)$. A non-negative integer triple $(x, y, z)$ solves
$\frac{a}{a+b} x + \frac{b}{a+b} y = z$ (equation (7)) if and only if
$(x, y, z) = c_1 L_1 + c_2 L_2 + c_3 L_3$ for some $c_1, c_2, c_3 \in \mathbb{Z}_{\ge 0}$, where
$L_1 = (1,1,1)$, $L_2 = ((a+b)/g, 0, a/g)$, $L_3 = (0, (a+b)/g, b/g)$ are the elements of
`linset a b` (Definition 5.6). -/
@[kb "hanke2023threeterm" "§5.2, Lemma 5.7, p. 10"]
theorem key_lemma (a b : ℕ) (hab : (a, b) ≠ (0, 0)) (x y z : ℕ) :
    ((a : ℚ) / (a + b) * x + (b : ℚ) / (a + b) * y = z) ↔
      ∃ c₁ c₂ c₃ : ℕ,
        x = c₁ * 1 + c₂ * ((a + b) / Nat.gcd a b) + c₃ * 0 ∧
        y = c₁ * 1 + c₂ * 0 + c₃ * ((a + b) / Nat.gcd a b) ∧
        z = c₁ * 1 + c₂ * (a / Nat.gcd a b) + c₃ * (b / Nat.gcd a b) := by
  have hab' : a + b ≠ 0 := by
    intro h; apply hab; simp only [Prod.mk.injEq]; omega
  have hg : 0 < Nat.gcd a b := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp; omega
    · exact Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
  set g := Nat.gcd a b with hgdef
  have hcop : Nat.Coprime a' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg
    rw [← hgdef] at this
    have h1 : a / g = a' := by rw [ha']; exact Nat.mul_div_cancel_left _ hg
    have h2 : b / g = b' := by rw [hb']; exact Nat.mul_div_cancel_left _ hg
    rwa [h1, h2] at this
  have hdiv1 : (a + b) / g = a' + b' := by
    rw [ha', hb', ← mul_add]; exact Nat.mul_div_cancel_left _ hg
  have hdiv2 : a / g = a' := by rw [ha']; exact Nat.mul_div_cancel_left _ hg
  have hdiv3 : b / g = b' := by rw [hb']; exact Nat.mul_div_cancel_left _ hg
  rw [hdiv1, hdiv2, hdiv3, eq7_iff_nat a b x y z hab']
  have hred : a * x + b * y = (a + b) * z ↔ a' * x + b' * y = (a' + b') * z := by
    rw [ha', hb']
    constructor
    · intro e
      apply Nat.eq_of_mul_eq_mul_left hg
      linarith [e]
    · intro e
      calc g * a' * x + g * b' * y = g * (a' * x + b' * y) := by ring
        _ = g * ((a' + b') * z) := by rw [e]
        _ = (g * a' + g * b') * z := by ring
  rw [hred]
  constructor
  · intro e
    obtain ⟨c₁, c₂, c₃, h1, h2, h3⟩ := key_coprime a' b' x y z hcop e
    exact ⟨c₁, c₂, c₃, by rw [h1]; ring, by rw [h2]; ring, by rw [h3]; ring⟩
  · rintro ⟨c₁, c₂, c₃, rfl, rfl, rfl⟩
    ring

end QuadFormsKB.Hanke2023ThreeTerm
