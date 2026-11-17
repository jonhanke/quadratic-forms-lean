import QuadFormsKB.Historical.Gauss.ReductionIndefinite

/-!
# Forms of square determinant and representations by $m(gx+hy)^2$ (Disquisitiones Arithmeticae, Arts. 206-207, 215)

ids: (Art. 223: for $D = h^2$ the representative $(A, h, 0)$ of a class; loose end
a recorded loose end, square case) and (Art. 215 III).

* `art206_square_reduced` (proved): every form $(a, b, c)$ with $b^2 - ac = h^2$, $h > 0$, is properly equivalent to
  $(A, h, 0)$ for some $0 \le A < 2h$. Proof: the form represents $0$ primitively; completing the primitive zero to a
  matrix of determinant $1$ gives a form $(a', b', 0)$ with $b'^2 = h^2$; the sign of $b'$ is fixed by a further
  substitution of determinant $1$ (`square_flip_sign`), and $A$ is reduced modulo $2h$ by $x \mapsto x + k y$.
* `art206_square_reduced_unique` (proved): for $0 \le A, A' < 2h$, $(A, h, 0)$ and $(A', h, 0)$ are properly
  equivalent only if $A = A'$ (from Conway-Sloane's `gauss_square_only_if`, via `sLEquiv_to_properEquiv`).
* `art215_III_represented_iff`, `art215_III_solutions`, `art215_III_representations` (proved): Art. 215 III with plain
  integers.

Not covered by a recorded loose end: Gauss's choice of the representative inside the period of reduced forms for positive
nonsquare determinants.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary
open QuadFormsKB.ConwaySloane.Binary (BinForm ProperEquiv)

/-- Converse of `properEquiv_to_sLEquiv`: Gauss's proper equivalence of `gaussForm`s gives Conway-Sloane's
`ProperEquiv` of the `BinForm`s $\langle a, b, c\rangle$. -/
theorem sLEquiv_to_properEquiv {a b c A B C : ℤ}
    (h : SLEquiv (gaussForm a b c) (gaussForm A B C)) :
    ProperEquiv (⟨a, b, c⟩ : BinForm) ⟨A, B, C⟩ := by
  obtain ⟨p, q, r, s, hd, hs⟩ := (sLEquiv_iff _ _).1 h
  rw [subst_gaussForm] at hs
  have h1 := congrArg BinQF.a hs
  have h2 := congrArg BinQF.b hs
  have h3 := congrArg BinQF.c hs
  simp only [a_gaussForm, b_gaussForm, c_gaussForm] at h1 h2 h3
  refine ⟨!![p, r; q, s], by rw [Matrix.det_fin_two_of]; linarith, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuadFormsKB.ConwaySloane.Binary.BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [h1, h2, h3]

/-- Flip of sign: $(A, -h, 0)$ is properly equivalent to some $(A', h, 0)$ ($h > 0$). -/
theorem square_flip_sign (A h : ℤ) (hh : 0 < h) :
    ∃ A', SLEquiv (gaussForm A (-h) 0) (gaussForm A' h 0) := by
  have hpos : 0 < Int.gcd A (2 * h) := Int.gcd_pos_of_ne_zero_right _ (by omega)
  obtain ⟨g, A1, H, hg0, hcop, hA, hH⟩ := Int.exists_gcd_one' hpos
  have hcop' : IsCoprime H A1 := Int.isCoprime_iff_gcd_eq_one.2 (by rw [Int.gcd_comm]; exact hcop)
  obtain ⟨u, v, huv⟩ := hcop'
  have key : A * H = 2 * h * A1 := by linear_combination H * hA - A1 * hH
  refine ⟨A * v ^ 2 + 2 * (-h) * v * (-u) + 0 * (-u) ^ 2, ?_⟩
  rw [sLEquiv_iff]
  refine ⟨v, H, -u, A1, by linarith, ?_⟩
  rw [subst_gaussForm]
  have e1 : (A * H ^ 2 + 2 * (-h) * H * A1 + 0 * A1 ^ 2) = 0 := by linear_combination H * key
  have e2 : (A * v * H + (-h) * (v * A1 + H * (-u)) + 0 * (-u) * A1) = h := by
    linear_combination v * key + h * huv
  rw [e1, e2]

/-- Moving the first coefficient by multiples of $2h$: $(A, h, 0) \sim (A + 2hk, h, 0)$. -/
theorem square_shift (A h k : ℤ) : SLEquiv (gaussForm A h 0) (gaussForm (A + 2 * h * k) h 0) := by
  rw [sLEquiv_iff]
  refine ⟨1, 0, k, 1, by ring, ?_⟩
  rw [subst_gaussForm]
  congr 1 <;> ring

/-- A primitive zero of a form of square determinant gives an equivalent $(A, h, 0)$. -/
theorem square_of_zero {a b c h x y : ℤ} (hh : 0 < h) (hd : gaussDet a b c = h ^ 2)
    (hz : a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = 0) (hc : IsCoprime x y) :
    ∃ A, SLEquiv (gaussForm a b c) (gaussForm A h 0) := by
  obtain ⟨u, v, huv⟩ := hc
  have hdet1 : (v * y - x * (-u)) = 1 := by linarith
  have hsub := subst_gaussForm a b c v x (-u) y
  have hdet := gaussDet_subst a b c v x (-u) y
  rw [hz] at hsub hdet
  rw [hdet1, hd] at hdet
  obtain ⟨a', b', hsub', hdet'⟩ : ∃ a' b' : ℤ,
      subst v x (-u) y (gaussForm a b c) = gaussForm a' b' 0 ∧ gaussDet a' b' 0 = h ^ 2 :=
    ⟨_, _, hsub, by rw [hdet]; ring⟩
  have hb : b' ^ 2 = h ^ 2 := by simpa [gaussDet] using hdet'
  have hs : SLEquiv (gaussForm a b c) (gaussForm a' b' 0) := by
    rw [sLEquiv_iff]; exact ⟨v, x, -u, y, by linarith, hsub'⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hb with h1 | h1
  · rw [h1] at hs; exact ⟨a', hs⟩
  · rw [h1] at hs
    obtain ⟨A', hA'⟩ := square_flip_sign a' h hh
    exact ⟨A', hs.trans hA'⟩

/-- Every form of square determinant represents $0$ primitively. -/
theorem square_primitive_zero {a b c h : ℤ} (hh : 0 < h) (hd : gaussDet a b c = h ^ 2) :
    ∃ x y : ℤ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = 0 ∧ IsCoprime x y := by
  simp only [gaussDet] at hd
  by_cases ha : a = 0
  · exact ⟨1, 0, by simp [ha], isCoprime_one_left⟩
  · have hpos : 0 < Int.gcd (h - b) a := Int.gcd_pos_of_ne_zero_right _ ha
    obtain ⟨g, x, y, hg0, hcop, hx, hy⟩ := Int.exists_gcd_one' hpos
    refine ⟨x, y, ?_, Int.isCoprime_iff_gcd_eq_one.2 hcop⟩
    have h0 : a * (h - b) ^ 2 + 2 * b * (h - b) * a + c * a ^ 2 = 0 := by
      have h1 : (h - b) ^ 2 + 2 * b * (h - b) + c * a = 0 := by nlinarith
      linear_combination a * h1
    have h3 : (g : ℤ) ^ 2 * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = 0 := by
      have e : (g : ℤ) ^ 2 * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) =
          a * (h - b) ^ 2 + 2 * b * (h - b) * a + c * a ^ 2 := by
        rw [hx]
        linear_combination (-(2 * b * x * g + c * (a + y * g))) * hy
      rw [e]; exact h0
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (pow_ne_zero 2 (by exact_mod_cast hg0.ne'))
    · exact h4

/-- **Forms of square determinant (Gauss, *Disq. Arith.* Arts. 206-207, the Art. 223
row, square case $D = h^2$): every form $(a, b, c)$ with $b^2 - ac = h^2$, $h > 0$, is
properly equivalent to $(A, h, 0)$ for some $0 \le A < 2h$.** Unconditional. Gauss's rule in Art. 223 is "the form
$(A, k, 0)$ with $A \le k$ or $(A - 2k, k, 0)$"; here the least nonnegative residue modulo $2h$ is used, which is
the same normal form up to the choice of the half-open interval ($[0, 2h)$ rather than $(-h, h]$). -/
@[kb "gauss1801" "Arts. 206-207, 223"]
theorem art206_square_reduced {a b c h : ℤ} (hh : 0 < h) (hd : gaussDet a b c = h ^ 2) :
    ∃ A : ℤ, 0 ≤ A ∧ A < 2 * h ∧ SLEquiv (gaussForm a b c) (gaussForm A h 0) := by
  obtain ⟨x, y, hz, hc⟩ := square_primitive_zero hh hd
  obtain ⟨A0, hA0⟩ := square_of_zero hh hd hz hc
  have h2 : 0 < 2 * h := by omega
  refine ⟨A0 % (2 * h), Int.emod_nonneg _ h2.ne', Int.emod_lt_of_pos _ h2, ?_⟩
  have hk : A0 % (2 * h) = A0 + 2 * h * (-(A0 / (2 * h))) := by
    have := Int.emod_add_mul_ediv A0 (2 * h)
    linarith
  rw [hk]
  exact hA0.trans (square_shift A0 h _)

/-- **Uniqueness of the representative (Gauss, *Disq. Arith.* Arts. 206-207, square
case): for $h > 0$ and $0 \le A, A' < 2h$, the forms $(A, h, 0)$ and $(A', h, 0)$ are properly
equivalent only if $A = A'$.** A wrapper of Conway-Sloane's `gauss_square_only_if` (Ch. 15, §3.3) through
`sLEquiv_to_properEquiv`. -/
@[kb "gauss1801" "Arts. 206-207, 223"]
theorem art206_square_reduced_unique {A A' h : ℤ} (hh : 0 < h) (hA : 0 ≤ A) (hA2 : A < 2 * h)
    (hA' : 0 ≤ A') (hA2' : A' < 2 * h) (hpe : SLEquiv (gaussForm A h 0) (gaussForm A' h 0)) : A = A' := by
  have hm := QuadFormsKB.ConwaySloane.Binary.gauss_square_only_if hh (sLEquiv_to_properEquiv hpe)
  have h' : A % (2 * h) = A' % (2 * h) := hm
  rwa [Int.emod_eq_of_lt hA hA2, Int.emod_eq_of_lt hA' hA2'] at h'

/-- **Representation by $m(gx+hy)^2$ (Gauss, *Disq. Arith.* Art. 215 III), existence:
for coprime integers $g, h$, an integer $N$ is represented by $m (g x + h y)^2$ iff $N = m e^2$ for an integer
$e$.** (Gauss's $m \ne 0$ is not needed for this part.) -/
@[kb "gauss1801" "Art. 215 III"]
theorem art215_III_represented_iff {g h m N : ℤ} (hgh : IsCoprime g h) :
    (∃ x y : ℤ, m * (g * x + h * y) ^ 2 = N) ↔ ∃ e : ℤ, N = m * e ^ 2 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨g * x + h * y, hxy.symm⟩
  · rintro ⟨e, rfl⟩
    obtain ⟨u, v, huv⟩ := hgh
    have h1 : g * (e * u) + h * (e * v) = e := by linear_combination e * huv
    exact ⟨e * u, e * v, by rw [h1]⟩

/-- **Art. 215 III, the solutions of $g x + h y = e$ ($g, h$ coprime):** if $g x_0 + h y_0 = e$ then the integral
solutions of $g x + h y = e$ are exactly $x = x_0 + z h$, $y = y_0 - z g$, $z \in \mathbb{Z}$ (the historical sources
). -/
@[kb "gauss1801" "Art. 215 III"]
theorem art215_III_solutions {g h e x₀ y₀ : ℤ} (hgh : IsCoprime g h) (h₀ : g * x₀ + h * y₀ = e) (x y : ℤ) :
    g * x + h * y = e ↔ ∃ z : ℤ, x = x₀ + z * h ∧ y = y₀ - z * g := by
  constructor
  · intro hxy
    have hd : g * (x - x₀) = h * (y₀ - y) := by linear_combination hxy - h₀
    by_cases hh : h = 0
    · subst hh
      have hu : IsUnit g := isCoprime_zero_right.1 hgh
      have hg2 : g * g = 1 := by
        rcases Int.isUnit_iff.1 hu with rfl | rfl <;> norm_num
      refine ⟨(y₀ - y) * g, ?_, ?_⟩
      · have : g * (x - x₀) = 0 := by simpa using hd
        rcases mul_eq_zero.1 this with h1 | h1
        · exact absurd h1 hu.ne_zero
        · linarith
      · linear_combination (y₀ - y) * hg2
    · have hdvd : h ∣ x - x₀ := by
        have : h ∣ g * (x - x₀) := ⟨y₀ - y, hd⟩
        exact hgh.symm.dvd_of_dvd_mul_left this
      obtain ⟨z, hz⟩ := hdvd
      refine ⟨z, by linarith, ?_⟩
      have : h * (g * z) = h * (y₀ - y) := by rw [← hd, hz]; ring
      have := mul_left_cancel₀ hh this
      linarith
  · rintro ⟨z, rfl, rfl⟩
    linear_combination h₀

/-- **Art. 215 III, the representations of $N = m e^2$ by $m(gx+hy)^2$ ($g, h$ coprime, $m \ne 0$):** the
representations are exactly the solutions of $g x + h y = e$ or $g x + h y = -e$ (the
solutions of each are described by `art215_III_solutions`). -/
@[kb "gauss1801" "Art. 215 III"]
theorem art215_III_representations {g h m e : ℤ} (hm : m ≠ 0) (x y : ℤ) :
    m * (g * x + h * y) ^ 2 = m * e ^ 2 ↔ g * x + h * y = e ∨ g * x + h * y = -e := by
  rw [mul_right_inj' hm]
  exact sq_eq_sq_iff_eq_or_eq_neg

end QuadFormsKB.Historical.Gauss
