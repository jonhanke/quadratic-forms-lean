/-
# Cassels, Chapter 12, Example 3: the cases of equality

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, Examples, Ex. 3, pp. 282–283. Example 3 asks to show that a
Minkowski-reduced ternary form $Q(\vec{x}) = \sum_{i,j} f_{ij}x_ix_j$ of determinant $d$ satisfies
$f_{00}f_{11}f_{22} \le 2d$ (formalized as `QuadFormsKB.Reduction.example_3`; Cassels' indices $1, 2, 3$ are
$0, 1, 2$ here) and then to "determine all the cases of equality", remarking that this is much more tedious.

**Result (`example_3_eq`).** For a Minkowski-reduced real ternary form with matrix $F$, write $a = f_{00}$,
$p = f_{01}$, $q = f_{02}$, $r = f_{12}$. Then $f_{00}f_{11}f_{22} = 2d$ holds if and only if $f_{00} = f_{11} = f_{22} = a$
and one of the following holds (`TernaryEqualityShape`):

* (A) $|2p| = |2q| = |2r| = a$ and $pqr > 0$ (the face-centred cubic lattice $A_3$ scaled: four sign patterns);
* (B) exactly one of $p, q, r$ is $0$ and the other two have absolute value $a/2$ (the lattice $A_3$ again, in a
  different basis: twelve sign patterns).

With $a = 2$ these are the integral forms $2(x_0^2 + x_1^2 + x_2^2) + 2(\pm x_0x_1 \pm x_0x_2 \pm x_1x_2)$ with an even number of
minus signs (case (A)) and $2(x_0^2 + x_1^2 + x_2^2) \pm 2x_ix_j \pm 2x_ix_k$ (case (B)); in all of them $d = a^3/2$.
So the equality forms are exactly the positive multiples of the sixteen forms in the list, up to the sign
conventions of reduction (the sign changes $x_i \mapsto -x_i$ act on $(p, q, r)$ by sign changes preserving the sign of
$pqr$ and the number of zeros).

**Proof.** (i) The equality forces $f_{22} = f_{11}$ (since $(f_{22} - f_{11})(f_{00}f_{11} - 2p^2) \ge 0$ with the second
factor positive) and the vanishing of the polynomial $E = a b^2 + 4pqr - 2ar^2 - 2bq^2 - 2bp^2$ ($b = f_{11}$)
which is $\ge 0$ (Gauss' cyclic-sum argument is replaced by the two sign cases of `lemPos0`/`lemNeg0` in
`Ch12/Examples.lean`). (ii) In each sign case, strictness: `eqPos0`/`eqNeg0` show $b = a$ and reduce to the cubic
inequalities `coreP`/`coreN` on $x = 2|p|/a$, $y = 2|q|/a$, $z = 2|r|/a \in [0,1]$, whose equality cases are
$(1,1,1)$ and the permutations of $(1,1,0)$ (the first only with an even number of negative entries among
$p, q, r$). (iii) The converse is a direct computation of $d$.

**Reconstructed.** The book gives only a hint (Gauss' decomposition into the cases all $f_{ij} \ge 0$ and all
$f_{ij} \le 0$, with cyclic-sum identities garbled in the machine-read text). The characterization above was
determined independently, numerically (random search over the reduction polytope) and then proved.
The statement `example_3_eq` assumes only reducedness; it does not assert that the sixteen shapes are themselves
Minkowski-reduced (only that among reduced forms the equality cases are among them).
-/
import QuadFormsKB.Literature.Cassels.Ch12.Examples

open Matrix

namespace QuadFormsKB.Reduction

namespace Ex3Equality

/-- Helper: the cubic inequality behind the case $pqr \ge 0$ with its cases of equality. For $x, y, z \in [0,1]$ with
$2 + xyz \le x^2 + y^2 + z^2$ (the reverse inequality always holds), $(x, y, z)$ is $(1,1,1)$ or a permutation of
$(1,1,0)$. -/
theorem coreP (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz1 : z ≤ 1)
    (h : 2 + x*y*z ≤ x^2 + y^2 + z^2) :
    (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 1 ∧ z = 1) := by
  have u := sub_nonneg.2 hx1
  have v := sub_nonneg.2 hy1
  have w := sub_nonneg.2 hz1
  have t1 := mul_nonneg u hx
  have t2 := mul_nonneg v hy
  have t3 := mul_nonneg w hz
  have t4 := mul_nonneg (mul_nonneg u v) hz
  have t5 := mul_nonneg u w
  have t6 := mul_nonneg v w
  have hsum : (1-x)*x + (1-y)*y + (1-z)*z + (1-x)*(1-y)*z + (1-x)*(1-z) + (1-y)*(1-z) ≤ 0 := by nlinarith [h]
  have e1 : (1-x)*x = 0 := by linarith
  have e2 : (1-y)*y = 0 := by linarith
  have e3 : (1-z)*z = 0 := by linarith
  have bin : ∀ s : ℝ, (1-s)*s = 0 → s = 1 ∨ s = 0 := by
    intro s hs
    rcases mul_eq_zero.1 hs with h | h
    · left; linarith
    · right; exact h
  have e5 : (1-x)*(1-z) = 0 := by linarith
  have e6 : (1-y)*(1-z) = 0 := by linarith
  rcases bin x e1 with rfl | rfl <;> rcases bin y e2 with rfl | rfl <;> rcases bin z e3 with rfl | rfl <;>
    simp_all

/-- Helper: the cubic inequality behind the case $pqr \le 0$ with its cases of equality. For $x, y, z \in [0,1]$ with
$x + y + z \le 2$ and $2 \le xyz + x^2 + y^2 + z^2$ (the reverse inequality always holds), $(x, y, z)$ is a
permutation of $(1,1,0)$. -/
theorem coreN (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz1 : z ≤ 1)
    (hs : x + y + z ≤ 2) (h : 2 ≤ x*y*z + x^2 + y^2 + z^2) :
    (x = 1 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 1 ∧ z = 1) := by
  have u := sub_nonneg.2 hx1
  have v := sub_nonneg.2 hy1
  have w := sub_nonneg.2 hz1
  have S := sub_nonneg.2 hs
  have t1 := mul_nonneg u hx
  have t2 := mul_nonneg v hy
  have t3 := mul_nonneg w hz
  have t4 := mul_nonneg (mul_nonneg hx hy) hz
  have key : (x*y*z + (1-x)*x + (1-y)*y + (1-z)*z + (2 - (x+y+z))) / 4 ≤ 2 - (x*y*z + x^2 + y^2 + z^2) := by
    nlinarith [mul_nonneg S hx, mul_nonneg S hy, mul_nonneg S hz, mul_nonneg S u, mul_nonneg S v, mul_nonneg S w,
    mul_nonneg (mul_nonneg S hx) hy, mul_nonneg (mul_nonneg S hx) hz, mul_nonneg (mul_nonneg S hy) hz,
    mul_nonneg (mul_nonneg u v) w, mul_nonneg (mul_nonneg u v) hz, mul_nonneg (mul_nonneg u w) hy,
    mul_nonneg (mul_nonneg v w) hx, mul_nonneg u hx, mul_nonneg v hy, mul_nonneg w hz,
    mul_nonneg u w, mul_nonneg u v, mul_nonneg v w, mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  have e1 : (1-x)*x = 0 := by linarith
  have e2 : (1-y)*y = 0 := by linarith
  have e3 : (1-z)*z = 0 := by linarith
  have e4 : x*y*z = 0 := by linarith
  have e5 : x + y + z = 2 := by linarith
  have bin : ∀ s : ℝ, (1-s)*s = 0 → s = 1 ∨ s = 0 := by
    intro s hs
    rcases mul_eq_zero.1 hs with h | h
    · left; linarith
    · right; exact h
  rcases bin x e1 with rfl | rfl <;> rcases bin y e2 with rfl | rfl <;> rcases bin z e3 with rfl | rfl <;>
    simp_all

/-- Helper: the cases of equality for the nonnegative-variables inequality `lemPos0` (case $pqr \ge 0$ of
Example 3, after replacing $p, q, r$ by their absolute values). If $a \le b$, $0 \le p, q, r$, $2p \le a$, $2q \le a$,
$2r \le b$ and $E = ab^2 + 4pqr - 2ar^2 - 2bq^2 - 2bp^2 \le 0$ (it is always $\ge 0$), then $b = a$ and
$(2p, 2q, 2r)$ is $(a,a,a)$ or a permutation of $(a, a, 0)$. -/
theorem eqPos0 (a b p q r : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hp2 : 2*p ≤ a) (hq2 : 2*q ≤ a) (hr2 : 2*r ≤ b)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h0 : a*b*b + 4*p*q*r - 2*a*r^2 - 2*b*q^2 - 2*b*p^2 ≤ 0) :
    b = a ∧ ((2*p = a ∧ 2*q = a ∧ 2*r = a) ∨ (2*p = a ∧ 2*q = a ∧ r = 0) ∨ (2*p = a ∧ q = 0 ∧ 2*r = a) ∨
      (p = 0 ∧ 2*q = a ∧ 2*r = a)) := by
  have X := sub_nonneg.2 hp2
  have Y := sub_nonneg.2 hq2
  have Z := sub_nonneg.2 hr2
  have W := sub_nonneg.2 hab
  have hb : 0 ≤ b := by linarith
  have h1 : b = a := by
    by_contra hne
    have hW : 0 < b - a := lt_of_le_of_ne W (Ne.symm (sub_ne_zero.2 hne))
    nlinarith [mul_nonneg (mul_nonneg X Y) Z, mul_nonneg (mul_nonneg X Y) hr, mul_nonneg (mul_nonneg X hq) Z,
    mul_nonneg (mul_nonneg hp Y) Z, mul_nonneg (mul_nonneg X hq) hr, mul_nonneg (mul_nonneg hp Y) hr,
    mul_nonneg (mul_nonneg hp hq) Z, mul_nonneg (mul_nonneg hp hq) hr,
    mul_pos (mul_pos hW ha) ha, mul_nonneg (mul_nonneg W hp) hb, mul_nonneg (mul_nonneg W hq) hb,
    mul_nonneg (mul_nonneg W hr) ha.le, mul_nonneg (mul_nonneg W hr) hb,
    mul_nonneg (mul_nonneg hb hp) X, mul_nonneg (mul_nonneg hb hq) Y, mul_nonneg (mul_nonneg ha.le hr) Z,
    mul_nonneg (mul_nonneg W hp) ha.le, mul_nonneg (mul_nonneg W hq) ha.le, mul_nonneg (mul_nonneg W ha.le) ha.le]
  refine ⟨h1, ?_⟩
  rw [h1] at hr2 h0
  have hx : 0 ≤ 2*p/a := by positivity
  have hy : 0 ≤ 2*q/a := by positivity
  have hz : 0 ≤ 2*r/a := by positivity
  have hx1 : 2*p/a ≤ 1 := (div_le_one ha).2 hp2
  have hy1 : 2*q/a ≤ 1 := (div_le_one ha).2 hq2
  have hz1 : 2*r/a ≤ 1 := (div_le_one ha).2 hr2
  have hg : 2 + (2*p/a)*(2*q/a)*(2*r/a) ≤ (2*p/a)^2 + (2*q/a)^2 + (2*r/a)^2 := by
    have e : (2*p/a)^2 + (2*q/a)^2 + (2*r/a)^2 - (2 + (2*p/a)*(2*q/a)*(2*r/a)) =
        -(2 * (a*a*a + 4*p*q*r - 2*a*r^2 - 2*a*q^2 - 2*a*p^2)) / a^3 := by
      field_simp
      ring
    have : -(2 * (a*a*a + 4*p*q*r - 2*a*r^2 - 2*a*q^2 - 2*a*p^2)) / a^3 ≥ 0 := by
      apply div_nonneg _ (by positivity)
      linarith
    linarith
  have key := coreP _ _ _ hx hy hz hx1 hy1 hz1 hg
  have ha' : a ≠ 0 := ha.ne'
  have cv : ∀ t : ℝ, (2*t/a = 1 ↔ 2*t = a) ∧ (2*t/a = 0 ↔ t = 0) := by
    intro t
    constructor
    · rw [div_eq_one_iff_eq ha']
    · rw [div_eq_zero_iff]; constructor
      · rintro (h | h)
        · linarith
        · exact absurd h ha'
      · intro h; left; rw [h]; ring
  simp only [(cv p).1, (cv q).1, (cv r).1, (cv p).2, (cv q).2, (cv r).2] at key
  exact key

/-- Helper: the cases of equality for `lemNeg0` (case $pqr \le 0$ of Example 3, after replacing $p, q, r$ by their
absolute values). Under the hypotheses of `eqPos0` and in addition $2(p + q + r) \le a + b$, if
$E' = ab^2 - 4pqr - 2ar^2 - 2bq^2 - 2bp^2 \le 0$ (it is always $\ge 0$) then $b = a$ and $(2p, 2q, 2r)$ is a
permutation of $(a, a, 0)$. -/
theorem eqNeg0 (a b p q r : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hp2 : 2*p ≤ a) (hq2 : 2*q ≤ a) (hr2 : 2*r ≤ b) (hs : 2*(p+q+r) ≤ a + b)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h0 : a*b*b - 4*p*q*r - 2*a*r^2 - 2*b*q^2 - 2*b*p^2 ≤ 0) :
    b = a ∧ ((2*p = a ∧ 2*q = a ∧ r = 0) ∨ (2*p = a ∧ q = 0 ∧ 2*r = a) ∨
      (p = 0 ∧ 2*q = a ∧ 2*r = a)) := by
  have X := sub_nonneg.2 hp2
  have Y := sub_nonneg.2 hq2
  have Z := sub_nonneg.2 hr2
  have S := sub_nonneg.2 hs
  have W := sub_nonneg.2 hab
  have hb : 0 ≤ b := by linarith
  have h1 : b = a := by
    by_contra hne
    have hW : 0 < b - a := lt_of_le_of_ne W (Ne.symm (sub_ne_zero.2 hne))
    nlinarith [mul_nonneg (mul_nonneg X Y) Z, mul_nonneg (mul_nonneg X Y) hr, mul_nonneg (mul_nonneg X hq) Z,
    mul_nonneg (mul_nonneg hp Y) Z, mul_nonneg (mul_nonneg X hq) hr, mul_nonneg (mul_nonneg hp Y) hr,
    mul_nonneg (mul_nonneg hp hq) Z, mul_nonneg (mul_nonneg hp hq) hr,
    mul_nonneg (mul_nonneg S hp) X, mul_nonneg (mul_nonneg S hq) Y, mul_nonneg (mul_nonneg S hr) Z,
    mul_nonneg (mul_nonneg S hp) hq, mul_nonneg (mul_nonneg S hp) hr, mul_nonneg (mul_nonneg S hq) hr,
    mul_nonneg (mul_nonneg S X) Y, mul_nonneg (mul_nonneg S X) Z, mul_nonneg (mul_nonneg S Y) Z,
    mul_nonneg (mul_nonneg S hp) hb, mul_nonneg (mul_nonneg S hq) hb, mul_nonneg (mul_nonneg S hr) ha.le,
    mul_nonneg (mul_nonneg S hr) hb,
    mul_pos (mul_pos hW ha) ha, mul_nonneg (mul_nonneg W hp) hb, mul_nonneg (mul_nonneg W hq) hb,
    mul_nonneg (mul_nonneg W hr) ha.le, mul_nonneg (mul_nonneg W hr) hb,
    mul_nonneg (mul_nonneg hb hp) X, mul_nonneg (mul_nonneg hb hq) Y, mul_nonneg (mul_nonneg ha.le hr) Z,
    mul_nonneg (mul_nonneg W hp) ha.le, mul_nonneg (mul_nonneg W hq) ha.le, mul_nonneg (mul_nonneg W ha.le) ha.le]
  refine ⟨h1, ?_⟩
  rw [h1] at hr2 h0 hs
  have hx : 0 ≤ 2*p/a := by positivity
  have hy : 0 ≤ 2*q/a := by positivity
  have hz : 0 ≤ 2*r/a := by positivity
  have hx1 : 2*p/a ≤ 1 := (div_le_one ha).2 hp2
  have hy1 : 2*q/a ≤ 1 := (div_le_one ha).2 hq2
  have hz1 : 2*r/a ≤ 1 := (div_le_one ha).2 hr2
  have hs' : 2*p/a + 2*q/a + 2*r/a ≤ 2 := by
    rw [← add_div, ← add_div, div_le_iff₀ ha]; linarith
  have hg : 2 ≤ (2*p/a)*(2*q/a)*(2*r/a) + (2*p/a)^2 + (2*q/a)^2 + (2*r/a)^2 := by
    have e : (2*p/a)*(2*q/a)*(2*r/a) + (2*p/a)^2 + (2*q/a)^2 + (2*r/a)^2 - 2 =
        -(2 * (a*a*a - 4*p*q*r - 2*a*r^2 - 2*a*q^2 - 2*a*p^2)) / a^3 := by
      field_simp
      ring
    have : -(2 * (a*a*a - 4*p*q*r - 2*a*r^2 - 2*a*q^2 - 2*a*p^2)) / a^3 ≥ 0 := by
      apply div_nonneg _ (by positivity)
      linarith
    linarith
  have key := coreN _ _ _ hx hy hz hx1 hy1 hz1 hs' hg
  have ha' : a ≠ 0 := ha.ne'
  have cv : ∀ t : ℝ, (2*t/a = 1 ↔ 2*t = a) ∧ (2*t/a = 0 ↔ t = 0) := by
    intro t
    constructor
    · rw [div_eq_one_iff_eq ha']
    · rw [div_eq_zero_iff]; constructor
      · rintro (h | h)
        · linarith
        · exact absurd h ha'
      · intro h; left; rw [h]; ring
  simp only [(cv p).1, (cv q).1, (cv r).1, (cv p).2, (cv q).2, (cv r).2] at key
  exact key

/-- **The shape of the equality cases** in terms of the diagonal entry $a$ and the off-diagonal entries
$p = f_{01}$, $q = f_{02}$, $r = f_{12}$ (with $f_{00} = f_{11} = f_{22} = a$): either (A) $|2p| = |2q| = |2r| = a$ and
$pqr > 0$, or (B) one of $p, q, r$ vanishes and the other two satisfy $|2\cdot| = a$. -/
def ShapeEq (a p q r : ℝ) : Prop :=
  (|2*p| = a ∧ |2*q| = a ∧ |2*r| = a ∧ 0 < p*q*r) ∨ (p = 0 ∧ |2*q| = a ∧ |2*r| = a) ∨
    (q = 0 ∧ |2*p| = a ∧ |2*r| = a) ∨ (r = 0 ∧ |2*p| = a ∧ |2*q| = a)

/-- Helper: $|2t| = 2|t|$. -/
theorem abs_two_mul' (t : ℝ) : |2*t| = 2*|t| := by
  rw [abs_mul, abs_two]

/-- Helper: from the equality cases for the absolute values $P = |p|$, $Q = |q|$, $R = |r|$ and $0 \le pqr$ to
`ShapeEq`. -/
theorem shape_of_pos {a p q r P Q R : ℝ} (ha : 0 < a) (hP : |p| = P) (hQ : |q| = Q) (hR : |r| = R)
    (hs : 0 ≤ p*q*r)
    (h : (2*P = a ∧ 2*Q = a ∧ 2*R = a) ∨ (2*P = a ∧ 2*Q = a ∧ R = 0) ∨ (2*P = a ∧ Q = 0 ∧ 2*R = a) ∨
      (P = 0 ∧ 2*Q = a ∧ 2*R = a)) : ShapeEq a p q r := by
  unfold ShapeEq
  rw [abs_two_mul', abs_two_mul', abs_two_mul', hP, hQ, hR]
  have z : ∀ t T : ℝ, |t| = T → T = 0 → t = 0 := fun t T h1 h2 => abs_eq_zero.1 (h1.trans h2)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    refine ⟨h1, h2, h3, lt_of_le_of_ne hs (Ne.symm ?_)⟩
    have hp : p ≠ 0 := fun h0 => by
      rw [h0] at hP; simp at hP; linarith
    have hq : q ≠ 0 := fun h0 => by
      rw [h0] at hQ; simp at hQ; linarith
    have hr : r ≠ 0 := fun h0 => by
      rw [h0] at hR; simp at hR; linarith
    exact mul_ne_zero (mul_ne_zero hp hq) hr
  · right; right; right; exact ⟨z _ _ hR h3, h1, h2⟩
  · right; right; left; exact ⟨z _ _ hQ h2, h1, h3⟩
  · right; left; exact ⟨z _ _ hP h1, h2, h3⟩

/-- Helper: as `shape_of_pos`, for the case of an odd number of negative entries, where only type (B) occurs. -/
theorem shape_of_neg {a p q r P Q R : ℝ} (hP : |p| = P) (hQ : |q| = Q) (hR : |r| = R)
    (h : (2*P = a ∧ 2*Q = a ∧ R = 0) ∨ (2*P = a ∧ Q = 0 ∧ 2*R = a) ∨ (P = 0 ∧ 2*Q = a ∧ 2*R = a)) :
    ShapeEq a p q r := by
  unfold ShapeEq
  rw [abs_two_mul', abs_two_mul', abs_two_mul', hP, hQ, hR]
  have z : ∀ t T : ℝ, |t| = T → T = 0 → t = 0 := fun t T h1 h2 => abs_eq_zero.1 (h1.trans h2)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · right; right; right; exact ⟨z _ _ hR h3, h1, h2⟩
  · right; right; left; exact ⟨z _ _ hQ h2, h1, h3⟩
  · right; left; exact ⟨z _ _ hP h1, h2, h3⟩

/-- Helper: the algebraic core of the cases of equality. Under the hypotheses of `QuadFormsKB.Reduction.alg3`, if
$abc = 2(abc + 2pqr - ar^2 - bq^2 - cp^2)$ then $c = b$, $b = a$ and `ShapeEq a p q r` holds. -/
theorem alg3_eq (a b c p q r : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hp1 : -a ≤ 2*p) (hp2 : 2*p ≤ a) (hq1 : -a ≤ 2*q) (hq2 : 2*q ≤ a)
    (hr1 : -b ≤ 2*r) (hr2 : 2*r ≤ b)
    (s1 : 0 ≤ a + b + 2*p + 2*q + 2*r) (s2 : 0 ≤ a + b - 2*p + 2*q - 2*r)
    (s3 : 0 ≤ a + b - 2*p - 2*q + 2*r) (s4 : 0 ≤ a + b + 2*p - 2*q - 2*r)
    (heq : a*b*c = 2 * (a*b*c + 2*p*q*r - a*r^2 - b*q^2 - c*p^2)) :
    c = b ∧ b = a ∧ ShapeEq a p q r := by
  have hc : 0 ≤ (c - b) * (a*b - 2*p^2) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hpos : 0 < a*b - 2*p^2 := by nlinarith
  have hE : 0 ≤ a*b*b + 4*p*q*r - 2*a*r^2 - 2*b*q^2 - 2*b*p^2 := by
    rcases le_total 0 p with hp | hp <;> rcases le_total 0 q with hq | hq <;> rcases le_total 0 r with hr | hr
    · exact lemPos0 a b p q r ha hab hp2 hq2 hr2 hp hq hr
    · have := lemNeg0 a b p q (-r) ha hab hp2 hq2 (by linarith) (by linarith) hp hq (by linarith)
      nlinarith
    · have := lemNeg0 a b p (-q) r ha hab hp2 (by linarith) hr2 (by linarith) hp (by linarith) hr
      nlinarith
    · have := lemPos0 a b p (-q) (-r) ha hab hp2 (by linarith) (by linarith) hp (by linarith) (by linarith)
      nlinarith
    · have := lemNeg0 a b (-p) q r ha hab (by linarith) hq2 hr2 (by linarith) (by linarith) hq hr
      nlinarith
    · have := lemPos0 a b (-p) q (-r) ha hab (by linarith) hq2 (by linarith) (by linarith) hq (by linarith)
      nlinarith
    · have := lemPos0 a b (-p) (-q) r ha hab (by linarith) (by linarith) hr2 (by linarith) (by linarith) hr
      nlinarith
    · have := lemNeg0 a b (-p) (-q) (-r) ha hab (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
      nlinarith
  have hct : (c - b) * (a*b - 2*p^2) = 0 := by nlinarith
  have hcb : c = b := by
    rcases mul_eq_zero.1 hct with h | h
    · linarith
    · linarith
  subst hcb
  have hE0 : a*c*c + 4*p*q*r - 2*a*r^2 - 2*c*q^2 - 2*c*p^2 ≤ 0 := by nlinarith
  refine ⟨rfl, ?_⟩
  rcases le_total 0 p with hp | hp <;> rcases le_total 0 q with hq | hq <;> rcases le_total 0 r with hr | hr
  · obtain ⟨h1, h2⟩ := eqPos0 a c p q r ha hab hp2 hq2 hr2 hp hq hr hE0
    exact ⟨h1, shape_of_pos ha (abs_of_nonneg hp) (abs_of_nonneg hq) (abs_of_nonneg hr)
      (mul_nonneg (mul_nonneg hp hq) hr) h2⟩
  · obtain ⟨h1, h2⟩ := eqNeg0 a c p q (-r) ha hab hp2 hq2 (by linarith) (by linarith) hp hq (by linarith)
      (by nlinarith)
    exact ⟨h1, shape_of_neg (abs_of_nonneg hp) (abs_of_nonneg hq) (abs_of_nonpos hr) h2⟩
  · obtain ⟨h1, h2⟩ := eqNeg0 a c p (-q) r ha hab hp2 (by linarith) hr2 (by linarith) hp (by linarith) hr
      (by nlinarith)
    exact ⟨h1, shape_of_neg (abs_of_nonneg hp) (abs_of_nonpos hq) (abs_of_nonneg hr) h2⟩
  · obtain ⟨h1, h2⟩ := eqPos0 a c p (-q) (-r) ha hab hp2 (by linarith) (by linarith) hp (by linarith)
      (by linarith) (by nlinarith)
    exact ⟨h1, shape_of_pos ha (abs_of_nonneg hp) (abs_of_nonpos hq) (abs_of_nonpos hr)
      (by nlinarith [mul_nonneg (mul_nonneg hp (neg_nonneg.2 hq)) (neg_nonneg.2 hr)]) h2⟩
  · obtain ⟨h1, h2⟩ := eqNeg0 a c (-p) q r ha hab (by linarith) hq2 hr2 (by linarith) (by linarith) hq hr
      (by nlinarith)
    exact ⟨h1, shape_of_neg (abs_of_nonpos hp) (abs_of_nonneg hq) (abs_of_nonneg hr) h2⟩
  · obtain ⟨h1, h2⟩ := eqPos0 a c (-p) q (-r) ha hab (by linarith) hq2 (by linarith) (by linarith) hq
      (by linarith) (by nlinarith)
    exact ⟨h1, shape_of_pos ha (abs_of_nonpos hp) (abs_of_nonneg hq) (abs_of_nonpos hr)
      (by nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.2 hp) hq) (neg_nonneg.2 hr)]) h2⟩
  · obtain ⟨h1, h2⟩ := eqPos0 a c (-p) (-q) r ha hab (by linarith) (by linarith) hr2 (by linarith)
      (by linarith) hr (by nlinarith)
    exact ⟨h1, shape_of_pos ha (abs_of_nonpos hp) (abs_of_nonpos hq) (abs_of_nonneg hr)
      (by nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.2 hp) (neg_nonneg.2 hq)) hr]) h2⟩
  · obtain ⟨h1, h2⟩ := eqNeg0 a c (-p) (-q) (-r) ha hab (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by nlinarith)
    exact ⟨h1, shape_of_neg (abs_of_nonpos hp) (abs_of_nonpos hq) (abs_of_nonpos hr) h2⟩

end Ex3Equality

/-- **The equality shapes of Example 3.** A real symmetric $3 \times 3$ matrix $F = (f_{ij})$ (indices $0, 1, 2$) has
`TernaryEqualityShape` if $f_{11} = f_{00}$, $f_{22} = f_{00}$ and, with $a = f_{00}$, $p = f_{01}$, $q = f_{02}$,
$r = f_{12}$, either (A) $|2p| = |2q| = |2r| = a$ and $pqr > 0$, or (B) one of $p, q, r$ is $0$ and the other two
satisfy $|2p| = a$ (resp. $|2q|$, $|2r|$) $= a$. These are the positive multiples of sixteen forms (all of them
Minkowski-reduced, checked numerically), each a rescaled copy of the face-centred cubic (root lattice $A_3$)
form with $d = a^3/2$. -/
def TernaryEqualityShape (F : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  F 1 1 = F 0 0 ∧ F 2 2 = F 0 0 ∧ Ex3Equality.ShapeEq (F 0 0) (F 0 1) (F 0 2) (F 1 2)

/-- **Example 3, the cases of equality** (Cassels, Ch. 12, p. 283): for a Minkowski-reduced real ternary form with matrix
$F = (f_{ij})$ and determinant $d = \det F$, $f_{00}f_{11}f_{22} = 2d$ if and only if $F$ has `TernaryEqualityShape`:
$f_{00} = f_{11} = f_{22} = a$ and the off-diagonal entries $(p, q, r) = (f_{01}, f_{02}, f_{12})$ are $\pm a/2$ with
$pqr > 0$, or two of them are $\pm a/2$ and the third is $0$. (Cassels' $f_{11}f_{22}f_{33}$ is $f_{00}f_{11}f_{22}$ here.)
Unconditional: no input beyond reducedness. -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 3 (cases of equality), pp. 282–283"]
theorem example_3_eq {F : Matrix (Fin 3) (Fin 3) ℝ} (hF : IsMinkowskiReduced F) :
    F 0 0 * F 1 1 * F 2 2 = 2 * F.det ↔ TernaryEqualityShape F := by
  have hs : F.IsSymm := ((posDef_iff F).1 hF.1).1
  have hsym : ∀ i j, F j i = F i j := fun i j => by
    have : Fᵀ = F := hs
    simpa using congrFun (congrFun this i) j
  have hdet : F.det = F 0 0 * F 1 1 * F 2 2 + 2 * F 0 1 * F 0 2 * F 1 2 - F 0 0 * F 1 2 ^ 2
      - F 1 1 * F 0 2 ^ 2 - F 2 2 * F 0 1 ^ 2 := by
    rw [Matrix.det_fin_three, hsym 0 1, hsym 0 2, hsym 1 2]; ring
  rw [hdet]
  constructor
  · intro heq
    have hs2 : ∀ e0 e1 : ℤ, (e0 = 1 ∨ e0 = -1) → (e1 = 1 ∨ e1 = -1) →
        0 ≤ F 0 0 + F 1 1 + 2 * e0 * e1 * F 0 1 + 2 * e0 * F 0 2 + 2 * e1 * F 1 2 := by
      intro e0 e1 h0 h1
      set b : Fin 3 → ℤ := ![e0, e1, 1] with hb
      have hg : tailGcd (2 : Fin 3) b = 1 := by
        unfold tailGcd
        have : (Finset.univ.filter fun k : Fin 3 => (2 : Fin 3) ≤ k) = {2} := by
          ext k; fin_cases k <;> simp
        rw [this, Finset.gcd_singleton]
        simp [hb]
      have h := (isMinkowskiReduced_iff_gcd F).1 hF |>.2 2 b hg
      have hv : val F (cast b) = F 0 0 * e0 ^ 2 + F 1 1 * e1 ^ 2 + F 2 2 + 2 * F 0 1 * e0 * e1
          + 2 * F 0 2 * e0 + 2 * F 1 2 * e1 := by
        simp [val, dotProduct, Matrix.mulVec, Fin.sum_univ_three, cast, hb, hsym 1 0, hsym 2 0, hsym 2 1]
        ring
      rw [hv] at h
      have e0sq : (e0 : ℝ) ^ 2 = 1 := by rcases h0 with rfl | rfl <;> norm_num
      have e1sq : (e1 : ℝ) ^ 2 = 1 := by rcases h1 with rfl | rfl <;> norm_num
      rw [e0sq, e1sq] at h
      nlinarith
    have h01 := hF.abs_two_mul_le (i := 0) (j := 1) (by decide)
    have h02 := hF.abs_two_mul_le (i := 0) (j := 2) (by decide)
    have h12 := hF.abs_two_mul_le (i := 1) (j := 2) (by decide)
    have hab := hF.diag_mono (i := 0) (j := 1) (by decide)
    have hbc := hF.diag_mono (i := 1) (j := 2) (by decide)
    have ha := hF.1.diag_pos (i := 0)
    have s1 := hs2 1 1 (Or.inl rfl) (Or.inl rfl)
    have s2 := hs2 1 (-1) (Or.inl rfl) (Or.inr rfl)
    have s3 := hs2 (-1) 1 (Or.inr rfl) (Or.inl rfl)
    have s4 := hs2 (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    push_cast at s1 s2 s3 s4
    rw [abs_le] at h01 h02 h12
    obtain ⟨h1, h2, h3⟩ := Ex3Equality.alg3_eq (F 0 0) (F 1 1) (F 2 2) (F 0 1) (F 0 2) (F 1 2) ha hab hbc
      h01.1 h01.2 h02.1 h02.2 h12.1 h12.2 (by linarith) (by linarith) (by linarith) (by linarith) heq
    exact ⟨h2, by rw [h1, h2], h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2]
    rcases h3 with ⟨hp, hq, hr, hpos⟩ | ⟨hp, hq, hr⟩ | ⟨hq, hp, hr⟩ | ⟨hr, hp, hq⟩
    · have key : ∀ t : ℝ, |2*t| = F 0 0 → t ^ 2 = F 0 0 ^ 2 / 4 := fun t ht => by
        have := sq_abs (2*t); rw [ht] at this; nlinarith
      have hp' := key _ hp
      have hq' := key _ hq
      have hr' := key _ hr
      have hprod : F 0 1 * F 0 2 * F 1 2 = F 0 0 ^ 3 / 8 := by
        have hsq : (F 0 1 * F 0 2 * F 1 2) ^ 2 = (F 0 0 ^ 3 / 8) ^ 2 := by
          have : (F 0 1 * F 0 2 * F 1 2) ^ 2 = F 0 1 ^ 2 * F 0 2 ^ 2 * F 1 2 ^ 2 := by ring
          rw [this, hp', hq', hr']; ring
        have h8 : 0 ≤ F 0 0 ^ 3 / 8 := by have := hF.1.diag_pos (i := 0); positivity
        exact (sq_eq_sq₀ hpos.le h8).1 hsq
      have e : 2 * F 0 1 * F 0 2 * F 1 2 = 2 * (F 0 1 * F 0 2 * F 1 2) := by ring
      rw [e, hprod, hp', hq', hr']
      ring
    · have key : ∀ t : ℝ, |2*t| = F 0 0 → t ^ 2 = F 0 0 ^ 2 / 4 := fun t ht => by
        have := sq_abs (2*t); rw [ht] at this; nlinarith
      have hq' := key _ hq
      have hr' := key _ hr
      rw [hp, hq', hr']
      ring
    · have key : ∀ t : ℝ, |2*t| = F 0 0 → t ^ 2 = F 0 0 ^ 2 / 4 := fun t ht => by
        have := sq_abs (2*t); rw [ht] at this; nlinarith
      have hp' := key _ hp
      have hr' := key _ hr
      rw [hq, hp', hr']
      ring
    · have key : ∀ t : ℝ, |2*t| = F 0 0 → t ^ 2 = F 0 0 ^ 2 / 4 := fun t ht => by
        have := sq_abs (2*t); rw [ht] at this; nlinarith
      have hp' := key _ hp
      have hq' := key _ hq
      rw [hr, hp', hq']
      ring

end QuadFormsKB.Reduction
