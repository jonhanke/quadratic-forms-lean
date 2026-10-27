/-
# Cassels, Chapter 12: Examples

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, Examples 1–5, pp. 282–283.

* Example 1 (i) (`example_1_i`): $6x^2 - 14xy + 9y^2$ is positive definite and $x^2 + 5y^2$ is a reduced form equivalent
  to it. Parts (ii) and (iii) are lost in the machine-read text and are not formalized.
* Example 2 (`example_2`, `example_2_eq`): $ac \le \tfrac43 d$ for a reduced binary form, with the cases of equality.
* Example 3 (`example_3`): $f_{00}f_{11}f_{22} \le 2d$ for a reduced ternary form (the cases of equality are not
  formalized).
* Example 4 (`example_4`): Hadamard's inequality $\det(\phi(\vec{b}_i, \vec{b}_j)) \le \prod_i \phi(\vec{b}_i)$.
* Example 5 (`example_5_i`, `example_5_ii`, `example_5_iii`): $\prod_j M_j \ge I^2 d(f)$, with $I = |\det(\vec{m}_0, \dots,
  \vec{m}_{n-1})|$ bounded in terms of $n$, and $I = 1$ for $n = 2, 3$.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec5

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **Example 1 (i)** (Cassels, Ch. 12, p. 282): $f = 6x^2 - 14xy + 9y^2$ (matrix
$\begin{pmatrix}6 & -7\\ -7 & 9\end{pmatrix}$) is positive definite, and the unimodular substitution
$T = \begin{pmatrix}1 & 2\\ 1 & 1\end{pmatrix}$, $(x, y) = (X + 2Y, X + Y)$, takes it to the reduced form $X^2 + 5Y^2$. -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 1 (i), p. 282"]
theorem example_1_i :
    (!![6, -7; -7, 9] : Matrix (Fin 2) (Fin 2) ℝ).PosDef ∧
      ∃ T : GL (Fin 2) ℤ, T.val = !![1, 2; 1, 1] ∧ act T.val !![6, -7; -7, 9] = !![1, 0; 0, 5] ∧
        IsMinkowskiReduced (!![1, 0; 0, 5] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hval : ∀ (a b : ℤ), val (!![1, 0; 0, 5] : Matrix (Fin 2) (Fin 2) ℝ) ![(a : ℝ), (b : ℝ)] =
      (a : ℝ) ^ 2 + 5 * (b : ℝ) ^ 2 := by
    intro a b
    simp [val, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  refine ⟨?_, ⟨!![1, 2; 1, 1], !![-1, 2; 1, -1], ?_, ?_⟩, rfl, ?_, ?_⟩
  · rw [posDef_iff]
    refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp, fun x hx => ?_⟩
    have : val (!![6, -7; -7, 9] : Matrix (Fin 2) (Fin 2) ℝ) x =
        6 * (x 0 - 7 / 6 * x 1) ^ 2 + 5 / 6 * x 1 ^ 2 := by
      simp [val, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [this]
    by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := fun h0 => hx (by ext i; fin_cases i <;> simp [h0, h1])
      rw [h1]; have := sq_pos_of_ne_zero h0; nlinarith
    · have := sq_pos_of_ne_zero h1
      nlinarith [sq_nonneg (x 0 - 7 / 6 * x 1)]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [act, castM, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · rw [isMinkowskiReduced_iff_gcd]
    have hval' : ∀ x : Fin 2 → ℝ, val (!![1, 0; 0, 5] : Matrix (Fin 2) (Fin 2) ℝ) x = x 0 ^ 2 + 5 * x 1 ^ 2 := by
      intro x
      simp [val, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    refine ⟨?_, ?_⟩
    · rw [posDef_iff]
      refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp, fun x hx => ?_⟩
      rw [hval']
      by_cases h1 : x 1 = 0
      · have h0 : x 0 ≠ 0 := fun h0 => hx (by ext i; fin_cases i <;> simp [h0, h1])
        rw [h1]; have := sq_pos_of_ne_zero h0; nlinarith
      · have := sq_pos_of_ne_zero h1
        nlinarith [sq_nonneg (x 0)]
    · intro j b hb
      have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      rcases hj with rfl | rfl
      · have hne : b 0 ≠ 0 ∨ b 1 ≠ 0 := by
          by_contra hc
          push Not at hc
          have : tailGcd (0 : Fin 2) b = 0 := by
            unfold tailGcd
            apply Finset.gcd_eq_zero_iff.2
            intro k _
            fin_cases k <;> simp [hc.1, hc.2]
          rw [this] at hb
          exact zero_ne_one hb
        have h1 : (1 : ℤ) ≤ b 0 ^ 2 + 5 * b 1 ^ 2 := by
          rcases hne with h | h
          · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (b 1)]
          · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (b 0)]
        have h2 : (1 : ℝ) ≤ (b 0 : ℝ) ^ 2 + 5 * (b 1 : ℝ) ^ 2 := by exact_mod_cast h1
        rw [show cast b = ![(b 0 : ℝ), (b 1 : ℝ)] by ext i; fin_cases i <;> simp [cast], hval']
        simpa using h2
      · have hb1 : tailGcd (1 : Fin 2) b = normalize (b 1) := by
          unfold tailGcd
          have : (Finset.univ.filter fun k : Fin 2 => (1 : Fin 2) ≤ k) = {1} := by
            ext k; fin_cases k <;> simp
          rw [this, Finset.gcd_singleton]
        rw [hb1] at hb
        have h1 : (1 : ℤ) ≤ b 1 ^ 2 := by
          have : b 1 ≠ 0 := by
            intro h0; rw [h0] at hb; simp at hb
          nlinarith [sq_pos_of_ne_zero this]
        have h2 : (1 : ℝ) ≤ (b 1 : ℝ) ^ 2 := by exact_mod_cast h1
        rw [show cast b = ![(b 0 : ℝ), (b 1 : ℝ)] by ext i; fin_cases i <;> simp [cast], hval']
        simp
        nlinarith [sq_nonneg (b 0 : ℝ)]

/-- Helper: facts about a reduced binary form. -/
theorem binary_facts {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : IsMinkowskiReduced F) :
    F.det = F 0 0 * F 1 1 - F 0 1 ^ 2 ∧ |2 * F 0 1| ≤ F 0 0 ∧ F 0 0 ≤ F 1 1 ∧ 0 < F 0 0 := by
  have hs : F.IsSymm := ((posDef_iff F).1 hF.1).1
  have hsym : F 1 0 = F 0 1 := by
    have : Fᵀ = F := hs
    simpa using congrFun (congrFun this 0) 1
  refine ⟨?_, hF.abs_two_mul_le (by decide), hF.diag_mono (by decide), hF.1.diag_pos⟩
  rw [Matrix.det_fin_two, hsym]; ring

/-- **Example 2** (Cassels, Ch. 12, p. 282): if $f = ax^2 + 2bxy + cy^2$ is Minkowski-reduced with determinant
$d = ac - b^2$, then $ac \le \tfrac43 d$. -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 2, p. 282"]
theorem example_2 {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : IsMinkowskiReduced F) :
    F 0 0 * F 1 1 ≤ 4 / 3 * F.det := by
  obtain ⟨hdet, h1, h2, h3⟩ := binary_facts hF
  rw [hdet]
  nlinarith [sq_abs (2 * F 0 1), abs_nonneg (2 * F 0 1), mul_le_mul_of_nonneg_left h2 h3.le]

/-- **Example 2, the cases of equality** (Cassels, Ch. 12, p. 282): for reduced $f$, $ac = \tfrac43 d$ iff $a = c$ and
$|2b| = a$, i.e. $f$ is a positive multiple of $x^2 \pm xy + y^2$. -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 2, p. 282 (cases of equality)"]
theorem example_2_eq {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : IsMinkowskiReduced F) :
    F 0 0 * F 1 1 = 4 / 3 * F.det ↔ F 0 0 = F 1 1 ∧ |2 * F 0 1| = F 0 0 := by
  obtain ⟨hdet, h1, h2, h3⟩ := binary_facts hF
  rw [hdet]
  have hsq := sq_abs (2 * F 0 1)
  have hab := abs_nonneg (2 * F 0 1)
  constructor
  · intro h
    have e1 : F 0 0 * F 0 0 = F 0 0 * F 1 1 := by
      nlinarith [mul_le_mul_of_nonneg_left h2 h3.le, mul_self_le_mul_self hab h1]
    have e2 : F 0 0 = F 1 1 := mul_left_cancel₀ h3.ne' e1
    refine ⟨e2, ?_⟩
    have : |2 * F 0 1| * |2 * F 0 1| = F 0 0 * F 0 0 := by nlinarith
    exact (mul_self_inj hab h3.le).1 this
  · rintro ⟨e1, e2⟩
    rw [← e1] at *
    nlinarith

/-- Helper (Example 3, case $p, q, r \ge 0$ at $c = b$): an inequality for the entries of a reduced ternary form. -/
theorem lemPos0 (a b p q r : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hp2 : 2*p ≤ a) (hq2 : 2*q ≤ a) (hr2 : 2*r ≤ b)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ a*b*b + 4*p*q*r - 2*a*r^2 - 2*b*q^2 - 2*b*p^2 := by
  have X := sub_nonneg.2 hp2
  have Y := sub_nonneg.2 hq2
  have Z := sub_nonneg.2 hr2
  have W := sub_nonneg.2 hab
  have hb : 0 ≤ b := by linarith
  nlinarith [mul_nonneg (mul_nonneg X Y) Z, mul_nonneg (mul_nonneg X Y) hr, mul_nonneg (mul_nonneg X hq) Z,
    mul_nonneg (mul_nonneg hp Y) Z, mul_nonneg (mul_nonneg X hq) hr, mul_nonneg (mul_nonneg hp Y) hr,
    mul_nonneg (mul_nonneg hp hq) Z, mul_nonneg (mul_nonneg hp hq) hr,
    mul_nonneg (mul_nonneg W ha.le) hb, mul_nonneg (mul_nonneg W hp) hb, mul_nonneg (mul_nonneg W hq) hb,
    mul_nonneg (mul_nonneg W hr) ha.le, mul_nonneg (mul_nonneg W hr) hb,
    mul_nonneg (mul_nonneg hb hp) X, mul_nonneg (mul_nonneg hb hq) Y, mul_nonneg (mul_nonneg ha.le hr) Z,
    mul_nonneg (mul_nonneg W hp) ha.le, mul_nonneg (mul_nonneg W hq) ha.le, mul_nonneg (mul_nonneg W ha.le) ha.le]

/-- Helper (Example 3, case $p, q, r \le 0$ at $c = b$, after negation). -/
theorem lemNeg0 (a b p q r : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hp2 : 2*p ≤ a) (hq2 : 2*q ≤ a) (hr2 : 2*r ≤ b) (hs : 2*(p+q+r) ≤ a + b)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ a*b*b - 4*p*q*r - 2*a*r^2 - 2*b*q^2 - 2*b*p^2 := by
  have X := sub_nonneg.2 hp2
  have Y := sub_nonneg.2 hq2
  have Z := sub_nonneg.2 hr2
  have S := sub_nonneg.2 hs
  have W := sub_nonneg.2 hab
  have hb : 0 ≤ b := by linarith
  nlinarith [mul_nonneg (mul_nonneg X Y) Z, mul_nonneg (mul_nonneg X Y) hr, mul_nonneg (mul_nonneg X hq) Z,
    mul_nonneg (mul_nonneg hp Y) Z, mul_nonneg (mul_nonneg X hq) hr, mul_nonneg (mul_nonneg hp Y) hr,
    mul_nonneg (mul_nonneg hp hq) Z, mul_nonneg (mul_nonneg hp hq) hr,
    mul_nonneg (mul_nonneg S hp) X, mul_nonneg (mul_nonneg S hq) Y, mul_nonneg (mul_nonneg S hr) Z,
    mul_nonneg (mul_nonneg S hp) hq, mul_nonneg (mul_nonneg S hp) hr, mul_nonneg (mul_nonneg S hq) hr,
    mul_nonneg (mul_nonneg S X) Y, mul_nonneg (mul_nonneg S X) Z, mul_nonneg (mul_nonneg S Y) Z,
    mul_nonneg (mul_nonneg S hp) hb, mul_nonneg (mul_nonneg S hq) hb, mul_nonneg (mul_nonneg S hr) ha.le,
    mul_nonneg (mul_nonneg S hr) hb,
    mul_nonneg (mul_nonneg W ha.le) hb, mul_nonneg (mul_nonneg W hp) hb, mul_nonneg (mul_nonneg W hq) hb,
    mul_nonneg (mul_nonneg W hr) ha.le, mul_nonneg (mul_nonneg W hr) hb,
    mul_nonneg (mul_nonneg hb hp) X, mul_nonneg (mul_nonneg hb hq) Y, mul_nonneg (mul_nonneg ha.le hr) Z,
    mul_nonneg (mul_nonneg W hp) ha.le, mul_nonneg (mul_nonneg W hq) ha.le, mul_nonneg (mul_nonneg W ha.le) ha.le]

/-- Helper (Example 3): the algebraic core. With $a = f_{00}$, $b = f_{11}$, $c = f_{22}$, $p = f_{01}$,
$q = f_{02}$, $r = f_{12}$, the inequalities of a reduced ternary form give $abc \le 2d$. -/
theorem alg3 (a b c p q r : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hp1 : -a ≤ 2*p) (hp2 : 2*p ≤ a) (hq1 : -a ≤ 2*q) (hq2 : 2*q ≤ a)
    (hr1 : -b ≤ 2*r) (hr2 : 2*r ≤ b)
    (s1 : 0 ≤ a + b + 2*p + 2*q + 2*r) (s2 : 0 ≤ a + b - 2*p + 2*q - 2*r)
    (s3 : 0 ≤ a + b - 2*p - 2*q + 2*r) (s4 : 0 ≤ a + b + 2*p - 2*q - 2*r) :
    a*b*c ≤ 2 * (a*b*c + 2*p*q*r - a*r^2 - b*q^2 - c*p^2) := by
  -- reduce to c = b
  have hc : 0 ≤ (c - b) * (a*b - 2*p^2) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have key : 0 ≤ a*b*b + 4*p*q*r - 2*a*r^2 - 2*b*q^2 - 2*b*p^2 →
      a*b*c ≤ 2 * (a*b*c + 2*p*q*r - a*r^2 - b*q^2 - c*p^2) := by
    intro h; nlinarith
  apply key
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

/-- **Example 3** (Cassels, Ch. 12, pp. 282–283): a Minkowski-reduced ternary form has $f_{00}f_{11}f_{22} \le 2d$,
$d = \det F$ (Gauss). The cases of equality are not formalized. -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 3, pp. 282–283"]
theorem example_3 {F : Matrix (Fin 3) (Fin 3) ℝ} (hF : IsMinkowskiReduced F) :
    F 0 0 * F 1 1 * F 2 2 ≤ 2 * F.det := by
  have hs : F.IsSymm := ((posDef_iff F).1 hF.1).1
  have hsym : ∀ i j, F j i = F i j := fun i j => by
    have : Fᵀ = F := hs
    simpa using congrFun (congrFun this i) j
  have hdet : F.det = F 0 0 * F 1 1 * F 2 2 + 2 * F 0 1 * F 0 2 * F 1 2 - F 0 0 * F 1 2 ^ 2
      - F 1 1 * F 0 2 ^ 2 - F 2 2 * F 0 1 ^ 2 := by
    rw [Matrix.det_fin_three, hsym 0 1, hsym 0 2, hsym 1 2]; ring
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
  rw [hdet]
  rw [abs_le] at h01 h02 h12
  have := alg3 (F 0 0) (F 1 1) (F 2 2) (F 0 1) (F 0 2) (F 1 2) ha hab hbc h01.1 h01.2 h02.1 h02.2 h12.1 h12.2
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- Helper: the Gram matrix $(\vec{b}_i^{\mathsf T}F\vec{b}_j)$ is $B^{\mathsf T}FB$, $B$ having columns $\vec{b}_j$. -/
theorem gram_eq {k : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (b : Fin k → Fin n → ℝ) :
    (Matrix.of fun i j => b i ⬝ᵥ (F *ᵥ b j)) =
      (Matrix.of fun (r : Fin n) (j : Fin k) => b j r)ᵀ * F * (Matrix.of fun (r : Fin n) (j : Fin k) => b j r) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Helper: the Gram matrix of a positive semi-definite form is positive semi-definite. -/
theorem gram_posSemidef {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) {k : ℕ} (b : Fin k → Fin n → ℝ) :
    (Matrix.of fun i j => b i ⬝ᵥ (F *ᵥ b j)).PosSemidef := by
  rw [gram_eq]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hF.conjTranspose_mul_mul_same (Matrix.of fun (r : Fin n) (j : Fin k) => b j r)

/-- **Hadamard's inequality for positive semi-definite matrices:** $\det G \le \prod_i g_{ii}$. -/
theorem det_le_prod_diag {k : ℕ} {G : Matrix (Fin k) (Fin k) ℝ} (hG : G.PosSemidef) : G.det ≤ ∏ i, G i i := by
  by_cases hd : G.det = 0
  · rw [hd]
    exact Finset.prod_nonneg fun i _ => hG.diag_nonneg
  · have hPD : G.PosDef := hG.posDef_iff_det_ne_zero.2 hd
    obtain ⟨h, C, hdec, hpos⟩ := exists_isSqDecomp hPD
    rw [hdec.det_eq]
    refine Finset.prod_le_prod₀ (fun i _ => (hpos i).le) (fun i _ => ?_)
    rw [hdec.diag_eq i]
    have hmem : i ∈ Finset.Iic i := Finset.mem_Iic.2 le_rfl
    calc h i = h i * C i i ^ 2 := by rw [hdec.2.1]; ring
      _ ≤ _ := Finset.single_le_sum (f := fun l => h l * C l i ^ 2)
          (fun l _ => mul_nonneg (hpos l).le (sq_nonneg _)) hmem

/-- **Example 4 (Hadamard's inequality)** (Cassels, Ch. 12, p. 283): for vectors $\vec{b}_0, \dots, \vec{b}_{k-1}$ in the real
positive definite quadratic space $(\mathbb{R}^n, f)$, with bilinear form $\phi(\vec{x}, \vec{y}) = \vec{x}^{\mathsf T}F\vec{y}$,
$$\det\bigl(\phi(\vec{b}_i, \vec{b}_j)\bigr)_{i,j} \le \prod_i \phi(\vec{b}_i, \vec{b}_i).$$ -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 4, p. 283"]
theorem example_4 {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {k : ℕ} (b : Fin k → Fin n → ℝ) :
    (Matrix.of fun i j => b i ⬝ᵥ (F *ᵥ b j)).det ≤ ∏ i, val F (b i) := by
  have hsd := gram_posSemidef hF.posSemidef b
  have hdiag : ∀ i, (Matrix.of fun i j => b i ⬝ᵥ (F *ᵥ b j)) i i = val F (b i) := fun i => rfl
  simp only [← hdiag]
  exact det_le_prod_diag hsd

/-- **Example 5 (i)** (Cassels, Ch. 12, p. 283): if $\vec{m}_0, \dots, \vec{m}_{n-1}$ are linearly independent integral
vectors with $f(\vec{m}_j) = M_j$ and $I = |\det(\vec{m}_0, \dots, \vec{m}_{n-1})|$, then $\prod_j M_j \ge I^2 d(f)$. (The
displayed inequality is garbled in the machine-read text; $I^2$ is forced by Example 4 applied to the $\vec{m}_j$.) -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 5 (i), p. 283"]
theorem example_5_i {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {m : Fin n → Fin n → ℤ}
    (hm : ∀ j, val F (cast (m j)) = succMin F j) :
    (Matrix.of fun i j => (m j i : ℝ)).det ^ 2 * F.det ≤ ∏ j, succMin F j := by
  have hsd := gram_posSemidef hF.posSemidef (fun j => cast (m j))
  have h1 := det_le_prod_diag hsd
  rw [gram_eq] at h1
  have hdet : ((Matrix.of fun (r : Fin n) (j : Fin n) => cast (m j) r)ᵀ * F *
      (Matrix.of fun (r : Fin n) (j : Fin n) => cast (m j) r)).det =
      (Matrix.of fun i j => (m j i : ℝ)).det ^ 2 * F.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    simp only [cast]
    ring
  rw [hdet] at h1
  refine h1.trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_))
  rw [← hm j]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, val, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [cast]
  ring

/-- **Example 5 (ii)** (Cassels, Ch. 12, p. 283): $I$ is bounded by a constant depending only on $n$
(here $I^2 \le n^n$, from (i) and Theorem 2.2 with $\gamma_n = n$). -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 5 (ii), p. 283"]
theorem example_5_ii {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {m : Fin n → Fin n → ℤ}
    (hm : ∀ j, val F (cast (m j)) = succMin F j) :
    (Matrix.of fun i j => (m j i : ℝ)).det ^ 2 ≤ (n : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 := example_5_i hF hm
  have h2 := prod_succMin_le hF (hermiteConstantBound_n hn)
  have hd := hF.det_pos
  have : (Matrix.of fun i j => (m j i : ℝ)).det ^ 2 * F.det ≤ (n : ℝ) ^ n * F.det := h1.trans h2
  exact le_of_mul_le_mul_right this hd

/-- Helper (Example 5 (iii)): Babai rounding. For an upper unitriangular real matrix $C$ and any real vector
$\ell$ there is an integral vector $z$ with $|(C(\ell - z))_k| \le 1/2$ for all $k$ (rounding from the last
coordinate down). -/
theorem babai_round {C : Matrix (Fin n) (Fin n) ℝ} (hC : ∀ i j, j < i → C i j = 0) (hCd : ∀ i, C i i = 1)
    (l : Fin n → ℝ) : ∃ z : Fin n → ℤ, ∀ k, |(C *ᵥ (l - cast z)) k| ≤ 1 / 2 := by
  have key : ∀ t : ℕ, t ≤ n → ∃ z : Fin n → ℤ, ∀ k : Fin n, n - t ≤ k.val →
      |(C *ᵥ (l - cast z)) k| ≤ 1 / 2 := by
    intro t
    induction t with
    | zero => intro _; exact ⟨0, fun k hk => by have := k.2; omega⟩
    | succ t ih =>
      intro ht
      obtain ⟨z, hz⟩ := ih (by omega)
      set k0 : Fin n := ⟨n - (t + 1), by omega⟩ with hk0
      set δ : ℤ := round ((C *ᵥ (l - cast z)) k0) with hδ
      refine ⟨z + Pi.single k0 δ, fun k hk => ?_⟩
      have hexp : (C *ᵥ (l - cast (z + Pi.single k0 δ))) k =
          (C *ᵥ (l - cast z)) k - δ * C k k0 := by
        have : l - cast (z + Pi.single k0 δ) =
            (l - cast z) - (δ : ℝ) • (Pi.single k0 1 : Fin n → ℝ) := by
          ext i
          by_cases h : i = k0
          · subst h; simp [cast]; ring
          · simp [cast, h]
        rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul]
        simp
      rcases eq_or_lt_of_le (show k0 ≤ k from by
        show k0.val ≤ k.val
        simp only [hk0]; omega) with h | h
      · rw [hexp, ← h, hCd]
        have := abs_sub_round ((C *ᵥ (l - cast z)) k0)
        rw [mul_one]
        exact this
      · rw [hexp, hC k k0 h, mul_zero, sub_zero]
        apply hz
        have : k0.val < k.val := h
        simp only [hk0] at this
        omega
  obtain ⟨z, hz⟩ := key n le_rfl
  exact ⟨z, fun k => hz k (by omega)⟩

/-- Helper (Example 5 (iii)): for $n \le 3$, every integral vector is an integral combination of the
$\vec{m}_j$, i.e. $P^{-1}\vec{v}$ is integral. *Proof* (Gram-Schmidt/Babai): otherwise a coset representative
$\vec{u} = \sum_j y_j\vec{m}_j$ with Gram-Schmidt coordinates of absolute value $\le 1/2$ has
$f(\vec{u}) \le \tfrac{n}{4}M_J < M_J$, $J$ the last index with $y_J \ne 0$, contradicting Lemma 2.1. -/
theorem lattice_mem_of_le_three (hn : n ≤ 3) {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef)
    {m : Fin n → Fin n → ℤ} (hli : LinearIndependent ℝ fun j => cast (m j))
    (hm : ∀ j, val F (cast (m j)) = succMin F j) (v : Fin n → ℤ) :
    ∃ z : Fin n → ℤ, (Matrix.of fun i j => (m j i : ℝ))⁻¹ *ᵥ cast v = cast z := by
  classical
  by_contra hnot
  push Not at hnot
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (m j i : ℝ) with hP
  have hPm : ∀ j, P *ᵥ Pi.single j 1 = cast (m j) := by
    intro j; rw [Matrix.mulVec_single_one]; ext i; simp [hP, cast]
  have hPu : IsUnit P := Matrix.linearIndependent_col_iff_isUnit.1 hli
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hPinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hGpos : (Pᵀ * F * P).PosDef := by
    have := hF.conjTranspose_mul_mul_same (B := P) (Matrix.mulVec_injective_of_isUnit hPu)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  obtain ⟨h, C, hdec, hpos⟩ := exists_isSqDecomp hGpos
  have hGdiag : ∀ k, (Pᵀ * F * P) k k = succMin F k := by
    intro k
    rw [← hm k, ← val_single (Pᵀ * F * P) k, val_conj, hPm]
  obtain ⟨z, hz⟩ := babai_round hdec.1 hdec.2.1 (P⁻¹ *ᵥ cast v)
  set l := P⁻¹ *ᵥ cast v with hl
  set y := l - cast z with hy
  have hy0 : y ≠ 0 := fun h0 => hnot z (sub_eq_zero.1 h0)
  obtain ⟨J, hJmem, hJmax⟩ := Finset.exists_max_image (Finset.univ.filter fun j => y j ≠ 0) id (by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
    exact ⟨i, by simpa using hi⟩)
  have hyJ : y J ≠ 0 := (Finset.mem_filter.1 hJmem).2
  have hyz : ∀ j, J < j → y j = 0 := by
    intro j hj
    by_contra hne
    exact absurd (hJmax j (by simpa using hne)) (not_le.2 hj)
  set u : Fin n → ℤ := v - (Matrix.of fun i j => m j i) *ᵥ z with hu
  have hcu : cast u = P *ᵥ y := by
    have h1 : P *ᵥ y = cast v - P *ᵥ cast z := by
      rw [hy, Matrix.mulVec_sub, hl, Matrix.mulVec_mulVec, hPinv', Matrix.one_mulVec]
    have h2 : P *ᵥ cast z = cast ((Matrix.of fun i j => m j i) *ᵥ z) := by
      rw [← castM_mulVec_cast]
      congr 1
    rw [h1, h2]
    funext i
    simp [hu, cast]
  have hge : succMin F J ≤ val F (cast u) := by
    by_contra hlt
    push Not at hlt
    have hmem := mem_span_of_val_lt_succMin hF hli hm hlt
    have hle : Submodule.span ℝ ((fun i => cast (m i)) '' {i | i < J}) ≤
        LinearMap.ker ((LinearMap.proj J : (Fin n → ℝ) →ₗ[ℝ] ℝ) ∘ₗ (P⁻¹).mulVecLin) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply,
        LinearMap.proj_apply]
      rw [← hPm i, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
      have : J ≠ i := ne_of_gt hi
      simp [this]
    have := hle hmem
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply] at this
    rw [hcu, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec] at this
    exact hyJ this
  have hval : val F (cast u) = ∑ k, h k * (C *ᵥ y) k ^ 2 := by
    rw [hcu, ← val_conj]
    exact val_eq_of_isSqDecomp hdec y
  have hMpos : 0 < succMin F J := succMin_pos hF J
  have hterm : ∀ k, h k * (C *ᵥ y) k ^ 2 ≤ if k ≤ J then succMin F J / 4 else 0 := by
    intro k
    split_ifs with hk
    · have h1 : h k ≤ succMin F k := by
        have := hdec.diag_eq k
        rw [hGdiag k] at this
        rw [this]
        calc h k = h k * C k k ^ 2 := by rw [hdec.2.1]; ring
          _ ≤ _ := Finset.single_le_sum (f := fun i => h i * C i k ^ 2)
              (fun i _ => mul_nonneg (hpos i).le (sq_nonneg _)) (Finset.mem_Iic.2 le_rfl)
      have h2 : succMin F k ≤ succMin F J := succMin_mono hF hk
      have h3 : (C *ᵥ y) k ^ 2 ≤ 1 / 4 := by
        have := abs_le.1 (hz k)
        nlinarith [this.1, this.2]
      have h4 := hpos k
      calc h k * (C *ᵥ y) k ^ 2 ≤ h k * (1 / 4) := by gcongr
        _ ≤ succMin F J / 4 := by linarith
    · have : (C *ᵥ y) k = 0 := by
        rw [Matrix.mulVec, dotProduct]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hjk : j < k
        · rw [hdec.1 k j hjk, zero_mul]
        · rw [hyz j (lt_of_lt_of_le (not_le.1 hk) (not_lt.1 hjk)), mul_zero]
      rw [this]; simp
  have hsum : ∑ k, h k * (C *ᵥ y) k ^ 2 ≤
      ((Finset.univ.filter fun k : Fin n => k ≤ J).card : ℝ) * (succMin F J / 4) := by
    calc ∑ k, h k * (C *ᵥ y) k ^ 2 ≤ ∑ k : Fin n, (if k ≤ J then succMin F J / 4 else 0) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter fun k : Fin n => k ≤ J).card : ℝ) ≤ 3 := by
    have : (Finset.univ.filter fun k : Fin n => k ≤ J).card ≤ 3 :=
      (Finset.card_filter_le _ _).trans (by simpa using hn)
    exact_mod_cast this
  nlinarith [mul_le_mul_of_nonneg_right hcard (show 0 ≤ succMin F J / 4 by linarith)]

/-- **Example 5 (iii)** (Cassels, Ch. 12, p. 283): for $n = 2$ and $n = 3$, $I = 1$: linearly independent integral vectors
realizing the successive minima form a basis of $\mathbb{Z}^n$. -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 5 (iii), p. 283"]
theorem example_5_iii (hn : n = 2 ∨ n = 3) {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef)
    {m : Fin n → Fin n → ℤ} (hli : LinearIndependent ℝ fun j => cast (m j))
    (hm : ∀ j, val F (cast (m j)) = succMin F j) :
    |(Matrix.of fun i j => (m j i : ℝ)).det| = 1 := by
  have hn3 : n ≤ 3 := by rcases hn with rfl | rfl <;> norm_num
  choose z hz using lattice_mem_of_le_three hn3 hF hli hm
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (m j i : ℝ) with hP
  set Pz : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => m j i with hPz
  set Z : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => z (Pi.single j 1) i with hZ
  have hPu : IsUnit P := Matrix.linearIndependent_col_iff_isUnit.1 hli
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPmap : P = Pz.map (fun x : ℤ => (x : ℝ)) := by ext i j; simp [hP, hPz]
  have hinv : P⁻¹ = Z.map (fun x : ℤ => (x : ℝ)) := by
    ext i j
    have h1 := hz (Pi.single j 1)
    have h2 : (cast (Pi.single j 1 : Fin n → ℤ) : Fin n → ℝ) = Pi.single j 1 := by
      funext k; by_cases hk : k = j <;> simp [cast, hk]
    rw [h2] at h1
    have := congrFun h1 i
    rw [Matrix.mulVec_single_one] at this
    simpa [hZ, cast] using this
  have hmul : P.det * P⁻¹.det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv P hPdet, Matrix.det_one]
  rw [hinv, hPmap, ← Int.cast_det, ← Int.cast_det] at hmul
  have hint : Pz.det * Z.det = 1 := by exact_mod_cast hmul
  rcases Int.isUnit_iff.1 (IsUnit.of_mul_eq_one _ hint) with h | h
  · rw [hPmap, ← Int.cast_det, h]; simp
  · rw [hPmap, ← Int.cast_det, h]; simp

end QuadFormsKB.Reduction
