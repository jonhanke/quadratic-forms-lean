/-
# Cassels, Chapter 4, §2: isotropy of binary forms

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 4, *Quadratic forms over local fields*,
Lemma 2.4, p. 58.

**Setting.** A regular binary form over a field $k$ is, after a change of basis (Ch. 2, Lemma 1.4), a diagonal form
$f(x, y) = a x^{2} + b y^{2}$ with $a, b \in k^{\times}$; its determinant is $d(f) = ab$ (modulo squares). The form is
*isotropic* if it has a zero $(x, y) \neq (0, 0)$.

**Proves** Lemma 2.4 (`binary_isotropic_iff`): $a x^{2} + b y^{2}$ is isotropic iff $-d(f) = -ab$ is a square in
$k$. Cassels states it for any field (the proof needs no restriction on the characteristic for diagonal forms).

**Proof.** If $a x^{2} + b y^{2} = 0$ with $(x, y) \neq 0$ then $y \neq 0$ and $-ab = (ax/y)^{2}$; conversely if
$-ab = t^{2}$ then $(x, y) = (t, a)$ is a zero.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

/-- **Cassels, Ch. 4, Lemma 2.4.** Let $k$ be a field and $a, b \in k^{\times}$. The regular binary diagonal form
$a x^{2} + b y^{2}$ (determinant $d = ab$) is isotropic, i.e. $a x^{2} + b y^{2} = 0$ for some
$(x, y) \neq (0, 0)$, if and only if $-d = -ab$ is a square in $k$. -/
@[kb "cassels1978" "Ch. 4, Lemma 2.4, p. 58"]
theorem binary_isotropic_iff {k : Type*} [Field k] {a b : k} (ha : a ≠ 0) (_hb : b ≠ 0) :
    (∃ x y : k, (x, y) ≠ (0, 0) ∧ a * x ^ 2 + b * y ^ 2 = 0) ↔ IsSquare (-(a * b)) := by
  constructor
  · rintro ⟨x, y, hxy, h⟩
    have hy : y ≠ 0 := by
      rintro rfl
      have : x = 0 := by simpa [ha] using h
      exact hxy (by simp [this])
    refine ⟨a * x / y, ?_⟩
    field_simp
    linear_combination -h
  · rintro ⟨t, ht⟩
    refine ⟨t, a, by simp [ha], ?_⟩
    linear_combination (-a) * ht

end QuadFormsKB.Cassels
