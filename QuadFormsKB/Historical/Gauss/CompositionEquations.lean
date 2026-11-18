import QuadFormsKB.Historical.Gauss.CompositionDeterminants

/-!
# The coefficient equations of Gauss's composition (Disquisitiones Arithmeticae, Art. 235)

(the nine coefficient equations $[1]$-$[9]$; proved),
(the identities $\Omega$ determining $F = (A, B, C)$; the three equations for $A, B, C$ are
proved, the divisibility consequences are not part of this file) and (the converse: $\Omega$
implies the nine equations, and the determinant relations; proved).

Indices are $0$-based: Gauss's $p, p', p'', p'''$ (and $q, \dots, q'''$) are `p 0, …, p 3` (`q 0, …, q 3`), and
$P, Q, R, S, T, U$ are `minors p q 0, …, 5`. Forms are Gauss's: $F = (A, B, C)$, $f = (a, b, c)$,
$f' = (a', b', c')$ (`gaussForm`, with middle library coefficient $2B$, $2b$, $2b'$), determinants
$D = B^2 - AC$, $d = b^2 - ac$, $d' = b'^2 - a'c'$.

## What is proved

* `transformsInto_iff_coefficientEquations`: `TransformsInto F f f' p q` holds iff the nine
  equations `CoefficientEquations` hold (comparison of the coefficients of the nine monomials in $x, y, x', y'$);
  `gaussPolar` is the polar form $\langle (u, v), (u', v') \rangle_F = A u u' + B (u v' + v u') + C v v'$.
* `art235_omega` (the identities $\Omega$ for the form $F$): if $F$ is transformed into $f f'$ with the
  six relations of Art. 235 (`GaussRelations`) and $d, d' \ne 0$, then $A n n' = q_1 q_2 - q_0 q_3$,
  $2 B n n' = p_0 q_3 + q_0 p_3 - p_1 q_2 - q_1 p_2$, $C n n' = p_1 p_2 - p_0 p_3$ (`OmegaFormEquations`).
  The proof is not Gauss's but a direct one: for a pair of the six numbers that is nonzero the vectors $(p_i, q_i)$
  are expressed through the other two (Cramer), giving $P_{ij}^2 (A n n' - (q_1 q_2 - q_0 q_3)) = 0$; $B$ then
  follows from $\Delta = D n n'$ (`art235_delta_eq`).
* `art235_omega_converse`: for nonzero rational $n, n'$ the six relations and the three equations
  of $\Omega$ imply `TransformsInto`, $d = n^2 D$ and $d' = n'^2 D$.

## What is not proved here

* The divisibility consequences listed in ($mm'$ divides $aa', 2ab', \dots$; $M$ divides $am'$, ...) are
  done in `CompositionGcd.lean` (another file), not here.
* In the hypothesis "forms nondegenerate" is used as $d \ne 0$ and $d' \ne 0$; this makes $n, n' \ne 0$
  and $D \ne 0$ automatic (via $d = n^2 D$, $d' = n'^2 D$). Without it the proof does not go through.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-- **The polar form of Gauss's form $F = (A, B, C)$** (Art. 235):
$\langle (u, v), (u', v') \rangle_F = A\,u u' + B\,(u v' + v u') + C\,v v'$, the symmetric bilinear form with
$\langle (u, v), (u, v) \rangle_F = F(u, v) = A u^2 + 2 B u v + C v^2$. -/
def gaussPolar (A B C u v u' v' : ℤ) : ℤ := A * u * u' + B * (u * v' + v * u') + C * v * v'

/-- **The nine coefficient equations $[1]$-$[9]$ of Art. 235**: with $v_i = (p_i, q_i)$,
$$F(v_0) = aa',\ F(v_1) = ac',\ F(v_2) = ca',\ F(v_3) = cc',$$
$$\langle v_0, v_1 \rangle_F = ab',\ \langle v_0, v_2 \rangle_F = ba',\ \langle v_1, v_3 \rangle_F = bc',\
\langle v_2, v_3 \rangle_F = cb',\ \langle v_0, v_3 \rangle_F + \langle v_1, v_2 \rangle_F = 2bb'$$
(Gauss's $p, p', p'', p'''$ are $p_0, \dots, p_3$; $F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$ in Gauss's
notation $ax^2 + 2bxy + cy^2$). -/
@[kb "gauss1801" "Art. 235"]
def CoefficientEquations (A B C a b c a' b' c' : ℤ) (p q : Fin 4 → ℤ) : Prop :=
  (gaussForm A B C).eval (p 0) (q 0) = a * a' ∧ (gaussForm A B C).eval (p 1) (q 1) = a * c' ∧
  (gaussForm A B C).eval (p 2) (q 2) = c * a' ∧ (gaussForm A B C).eval (p 3) (q 3) = c * c' ∧
  gaussPolar A B C (p 0) (q 0) (p 1) (q 1) = a * b' ∧ gaussPolar A B C (p 0) (q 0) (p 2) (q 2) = b * a' ∧
  gaussPolar A B C (p 1) (q 1) (p 3) (q 3) = b * c' ∧ gaussPolar A B C (p 2) (q 2) (p 3) (q 3) = c * b' ∧
  gaussPolar A B C (p 0) (q 0) (p 3) (q 3) + gaussPolar A B C (p 1) (q 1) (p 2) (q 2) = 2 * (b * b')

/-- **The six relations of Art. 235** between the six numbers and $f, f'$ (without the transformation):
$P = a n'$, $R - S = 2 b n'$, $U = c n'$, $Q = a' n$, $R + S = 2 b' n$, $T = c' n$ (`minors p q 0, …, 5`). -/
def OmegaRelations (a b c a' b' c' : ℤ) (p q : Fin 4 → ℤ) (n n' : ℚ) : Prop :=
  (minors p q 0 : ℚ) = a * n' ∧ (minors p q 2 : ℚ) - minors p q 3 = 2 * b * n' ∧
    (minors p q 5 : ℚ) = c * n' ∧ (minors p q 1 : ℚ) = a' * n ∧
    (minors p q 2 : ℚ) + minors p q 3 = 2 * b' * n ∧ (minors p q 4 : ℚ) = c' * n

/-- **The three equations of $\Omega$ for $F = (A, B, C)$** (Art. 235/00334):
$A n n' = q_1 q_2 - q_0 q_3$, $2 B n n' = p_0 q_3 + q_0 p_3 - p_1 q_2 - q_1 p_2$, $C n n' = p_1 p_2 - p_0 p_3$
(Gauss's $Ann' = q'q'' - qq'''$, $2Bnn' = pq''' + qp''' - p'q'' - q'p''$, $Cnn' = p'p'' - pp'''$). -/
def OmegaFormEquations (A B C : ℤ) (p q : Fin 4 → ℤ) (n n' : ℚ) : Prop :=
  (A : ℚ) * n * n' = q 1 * q 2 - q 0 * q 3 ∧
    2 * (B : ℚ) * n * n' = p 0 * q 3 + q 0 * p 3 - p 1 * q 2 - q 1 * p 2 ∧
    (C : ℚ) * n * n' = p 1 * p 2 - p 0 * p 3

/-! ### The nine coefficient equations -/

private theorem coefficientEquations_of_transformsInto {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q) :
    CoefficientEquations A B C a b c a' b' c' p q := by
  have ev : ∀ x y x' y' : ℤ,
      A * (bilin p x y x' y') ^ 2 + 2 * B * bilin p x y x' y' * bilin q x y x' y' + C * (bilin q x y x' y') ^ 2 =
        (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * (a' * x' ^ 2 + 2 * b' * x' * y' + c' * y' ^ 2) := by
    intro x y x' y'
    have := hT x y x' y'
    rw [eval_gaussForm, eval_gaussForm, eval_gaussForm] at this
    exact this
  have e00 : A * p 0 ^ 2 + 2 * B * p 0 * q 0 + C * q 0 ^ 2 = a * a' := by
    have h := ev 1 0 1 0
    simp only [bilin] at h; linear_combination h
  have e11 : A * p 1 ^ 2 + 2 * B * p 1 * q 1 + C * q 1 ^ 2 = a * c' := by
    have h := ev 1 0 0 1
    simp only [bilin] at h; linear_combination h
  have e22 : A * p 2 ^ 2 + 2 * B * p 2 * q 2 + C * q 2 ^ 2 = c * a' := by
    have h := ev 0 1 1 0
    simp only [bilin] at h; linear_combination h
  have e33 : A * p 3 ^ 2 + 2 * B * p 3 * q 3 + C * q 3 ^ 2 = c * c' := by
    have h := ev 0 1 0 1
    simp only [bilin] at h; linear_combination h
  have e01 : gaussPolar A B C (p 0) (q 0) (p 1) (q 1) = a * b' := by
    have h := ev 1 0 1 1
    have : 2 * gaussPolar A B C (p 0) (q 0) (p 1) (q 1) = 2 * (a * b') := by
      simp only [bilin, gaussPolar] at h e00 e11 ⊢; linear_combination h - e00 - e11
    exact mul_left_cancel₀ two_ne_zero this
  have e02 : gaussPolar A B C (p 0) (q 0) (p 2) (q 2) = b * a' := by
    have h := ev 1 1 1 0
    have : 2 * gaussPolar A B C (p 0) (q 0) (p 2) (q 2) = 2 * (b * a') := by
      simp only [bilin, gaussPolar] at h e00 e22 ⊢; linear_combination h - e00 - e22
    exact mul_left_cancel₀ two_ne_zero this
  have e13 : gaussPolar A B C (p 1) (q 1) (p 3) (q 3) = b * c' := by
    have h := ev 1 1 0 1
    have : 2 * gaussPolar A B C (p 1) (q 1) (p 3) (q 3) = 2 * (b * c') := by
      simp only [bilin, gaussPolar] at h e11 e33 ⊢; linear_combination h - e11 - e33
    exact mul_left_cancel₀ two_ne_zero this
  have e23 : gaussPolar A B C (p 2) (q 2) (p 3) (q 3) = c * b' := by
    have h := ev 0 1 1 1
    have : 2 * gaussPolar A B C (p 2) (q 2) (p 3) (q 3) = 2 * (c * b') := by
      simp only [bilin, gaussPolar] at h e22 e33 ⊢; linear_combination h - e22 - e33
    exact mul_left_cancel₀ two_ne_zero this
  have e9 : gaussPolar A B C (p 0) (q 0) (p 3) (q 3) + gaussPolar A B C (p 1) (q 1) (p 2) (q 2) =
      2 * (b * b') := by
    have h := ev 1 1 1 1
    have : 2 * (gaussPolar A B C (p 0) (q 0) (p 3) (q 3) + gaussPolar A B C (p 1) (q 1) (p 2) (q 2)) =
        2 * (2 * (b * b')) := by
      simp only [bilin, gaussPolar] at h e00 e11 e22 e33 e01 e02 e13 e23 ⊢
      linear_combination h - e00 - e11 - e22 - e33 - 2 * e01 - 2 * e02 - 2 * e13 - 2 * e23
    exact mul_left_cancel₀ two_ne_zero this
  unfold CoefficientEquations
  refine ⟨?_, ?_, ?_, ?_, e01, e02, e13, e23, e9⟩
  · rw [eval_gaussForm]; linear_combination e00
  · rw [eval_gaussForm]; linear_combination e11
  · rw [eval_gaussForm]; linear_combination e22
  · rw [eval_gaussForm]; linear_combination e33

private theorem transformsInto_of_coefficientEquations {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ}
    (h : CoefficientEquations A B C a b c a' b' c' p q) :
    TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := h
  simp only [eval_gaussForm, gaussPolar] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  intro x y x' y'
  simp only [eval_gaussForm, bilin]
  linear_combination (x * x') ^ 2 * e1 + (x * y') ^ 2 * e2 + (y * x') ^ 2 * e3 + (y * y') ^ 2 * e4 +
    2 * (x * x') * (x * y') * e5 + 2 * (x * x') * (y * x') * e6 + 2 * (x * y') * (y * y') * e7 +
    2 * (y * x') * (y * y') * e8 + 2 * (x * x') * (y * y') * e9

/-- **Gauss, *Disq. Arith.* Art. 235, the nine coefficient equations:** for forms
$F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$ in Gauss's notation $ax^2 + 2bxy + cy^2$ and a bilinear
substitution $X = p_0 xx' + p_1 xy' + p_2 yx' + p_3 yy'$, $Y = q_0 xx' + \dots + q_3 yy'$, the identity
$F(X, Y) = f(x, y) f'(x', y')$ holds for all integers $x, y, x', y'$ (`TransformsInto`) if and only if the nine
equations $[1]$-$[9]$ hold (`CoefficientEquations`: $F(p_0, q_0) = aa'$, $F(p_1, q_1) = ac'$, $F(p_2, q_2) = ca'$,
$F(p_3, q_3) = cc'$, polar equations $ab'$, $ba'$, $bc'$, $cb'$, and
$\langle v_0, v_3 \rangle_F + \langle v_1, v_2 \rangle_F = 2bb'$). Proved in both directions with no extra hypotheses:
forward by evaluating the identity at points with entries in $\{0, 1\}$, backward by expanding (Gauss's "comparison of
the coefficients of the nine monomials"). Indices $0$-based. -/
@[kb "gauss1801" "Art. 235"]
theorem transformsInto_iff_coefficientEquations {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ} :
    TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q ↔
      CoefficientEquations A B C a b c a' b' c' p q :=
  ⟨coefficientEquations_of_transformsInto, transformsInto_of_coefficientEquations⟩

/-! ### Pure algebra over the rationals -/

/-- The polar form over the rationals (private copy of `gaussPolar`). -/
private def gq (A B C u v u' v' : ℚ) : ℚ := A * u * u' + B * (u * v' + v * u') + C * v * v'

private theorem gq_swap (A B C u v u' v' : ℚ) : gq C B A v u v' u' = gq A B C u v u' v' := by
  simp only [gq]; ring

private theorem cast_eval (A B C u v : ℤ) :
    (((gaussForm A B C).eval u v : ℤ) : ℚ) = gq A B C u v u v := by
  rw [eval_gaussForm]; simp only [gq]; push_cast; ring

private theorem cast_polar (A B C u v u' v' : ℤ) :
    ((gaussPolar A B C u v u' v' : ℤ) : ℚ) = gq A B C u v u' v' := by
  simp [gaussPolar, gq]

private theorem pair01 {p0 p1 p2 p3 q0 q1 q2 q3 A B C a a' b' c' n n' P Q R S T : ℚ}
    (hPd : P = p0 * q1 - q0 * p1) (hQd : Q = p0 * q2 - q0 * p2) (hRd : R = p0 * q3 - q0 * p3)
    (hSd : S = p1 * q2 - q1 * p2) (hTd : T = p1 * q3 - q1 * p3)
    (hP : P = a * n') (hQ : Q = a' * n) (hT : T = c' * n) (hRS : R + S = 2 * b' * n)
    (e00 : gq A B C p0 q0 p0 q0 = a * a') (e01 : gq A B C p0 q0 p1 q1 = a * b')
    (e11 : gq A B C p1 q1 p1 q1 = a * c') :
    P ^ 2 * (A * n * n' - (q1 * q2 - q0 * q3)) = 0 := by
  simp only [gq] at e00 e01 e11
  have hA : P ^ 2 * A = a * (a' * q1 ^ 2 - 2 * b' * q0 * q1 + c' * q0 ^ 2) := by
    rw [hPd]; linear_combination q1 ^ 2 * e00 - 2 * q0 * q1 * e01 + q0 ^ 2 * e11
  have hW : P * (q1 * q2 - q0 * q3) = Q * q1 ^ 2 - (R + S) * q0 * q1 + T * q0 ^ 2 := by
    rw [hPd, hQd, hRd, hSd, hTd]; ring
  have hPW : P * (q1 * q2 - q0 * q3) = n * (a' * q1 ^ 2 - 2 * b' * q0 * q1 + c' * q0 ^ 2) := by
    rw [hW, hRS, hQ, hT]; ring
  linear_combination (n * n') * hA - P * hPW - n * (a' * q1 ^ 2 - 2 * b' * q0 * q1 + c' * q0 ^ 2) * hP

private theorem pair02 {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' n n' P Q R S U : ℚ}
    (hPd : P = p0 * q1 - q0 * p1) (hQd : Q = p0 * q2 - q0 * p2) (hRd : R = p0 * q3 - q0 * p3)
    (hSd : S = p1 * q2 - q1 * p2) (hUd : U = p2 * q3 - q2 * p3)
    (hP : P = a * n') (hQ : Q = a' * n) (hU : U = c * n') (hRmS : R - S = 2 * b * n')
    (e00 : gq A B C p0 q0 p0 q0 = a * a') (e02 : gq A B C p0 q0 p2 q2 = b * a')
    (e22 : gq A B C p2 q2 p2 q2 = c * a') :
    Q ^ 2 * (A * n * n' - (q1 * q2 - q0 * q3)) = 0 := by
  simp only [gq] at e00 e02 e22
  have hA : Q ^ 2 * A = a' * (a * q2 ^ 2 - 2 * b * q0 * q2 + c * q0 ^ 2) := by
    rw [hQd]; linear_combination q2 ^ 2 * e00 - 2 * q0 * q2 * e02 + q0 ^ 2 * e22
  have hW : Q * (q1 * q2 - q0 * q3) = P * q2 ^ 2 - (R - S) * q0 * q2 + U * q0 ^ 2 := by
    rw [hPd, hQd, hRd, hSd, hUd]; ring
  have hQW : Q * (q1 * q2 - q0 * q3) = n' * (a * q2 ^ 2 - 2 * b * q0 * q2 + c * q0 ^ 2) := by
    rw [hW, hRmS, hP, hU]; ring
  linear_combination (n * n') * hA - Q * hQW - n' * (a * q2 ^ 2 - 2 * b * q0 * q2 + c * q0 ^ 2) * hQ

private theorem pair13 {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c c' n n' P R S T U : ℚ}
    (hPd : P = p0 * q1 - q0 * p1) (hRd : R = p0 * q3 - q0 * p3)
    (hSd : S = p1 * q2 - q1 * p2) (hTd : T = p1 * q3 - q1 * p3) (hUd : U = p2 * q3 - q2 * p3)
    (hP : P = a * n') (hT : T = c' * n) (hU : U = c * n') (hRmS : R - S = 2 * b * n')
    (e11 : gq A B C p1 q1 p1 q1 = a * c') (e13 : gq A B C p1 q1 p3 q3 = b * c')
    (e33 : gq A B C p3 q3 p3 q3 = c * c') :
    T ^ 2 * (A * n * n' - (q1 * q2 - q0 * q3)) = 0 := by
  simp only [gq] at e11 e13 e33
  have hA : T ^ 2 * A = c' * (a * q3 ^ 2 - 2 * b * q1 * q3 + c * q1 ^ 2) := by
    rw [hTd]; linear_combination q3 ^ 2 * e11 - 2 * q1 * q3 * e13 + q1 ^ 2 * e33
  have hW : T * (q1 * q2 - q0 * q3) = U * q1 ^ 2 - (R - S) * q1 * q3 + P * q3 ^ 2 := by
    rw [hPd, hRd, hSd, hTd, hUd]; ring
  have hTW : T * (q1 * q2 - q0 * q3) = n' * (a * q3 ^ 2 - 2 * b * q1 * q3 + c * q1 ^ 2) := by
    rw [hW, hRmS, hP, hU]; ring
  linear_combination (n * n') * hA - T * hTW - n' * (a * q3 ^ 2 - 2 * b * q1 * q3 + c * q1 ^ 2) * hT

private theorem pair23 {p0 p1 p2 p3 q0 q1 q2 q3 A B C c a' b' c' n n' Q R S T U : ℚ}
    (hQd : Q = p0 * q2 - q0 * p2) (hRd : R = p0 * q3 - q0 * p3)
    (hSd : S = p1 * q2 - q1 * p2) (hTd : T = p1 * q3 - q1 * p3) (hUd : U = p2 * q3 - q2 * p3)
    (hQ : Q = a' * n) (hT : T = c' * n) (hU : U = c * n') (hRS : R + S = 2 * b' * n)
    (e22 : gq A B C p2 q2 p2 q2 = c * a') (e23 : gq A B C p2 q2 p3 q3 = c * b')
    (e33 : gq A B C p3 q3 p3 q3 = c * c') :
    U ^ 2 * (A * n * n' - (q1 * q2 - q0 * q3)) = 0 := by
  simp only [gq] at e22 e23 e33
  have hA : U ^ 2 * A = c * (a' * q3 ^ 2 - 2 * b' * q2 * q3 + c' * q2 ^ 2) := by
    rw [hUd]; linear_combination q3 ^ 2 * e22 - 2 * q2 * q3 * e23 + q2 ^ 2 * e33
  have hW : U * (q1 * q2 - q0 * q3) = T * q2 ^ 2 - (R + S) * q2 * q3 + Q * q3 ^ 2 := by
    rw [hQd, hRd, hSd, hTd, hUd]; ring
  have hUW : U * (q1 * q2 - q0 * q3) = n * (a' * q3 ^ 2 - 2 * b' * q2 * q3 + c' * q2 ^ 2) := by
    rw [hW, hRS, hT, hQ]; ring
  linear_combination (n * n') * hA - U * hUW - n * (a' * q3 ^ 2 - 2 * b' * q2 * q3 + c' * q2 ^ 2) * hU

private theorem pair03 {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R T U : ℚ}
    (hPd : P = p0 * q1 - q0 * p1) (hQd : Q = p0 * q2 - q0 * p2) (hRd : R = p0 * q3 - q0 * p3)
    (hTd : T = p1 * q3 - q1 * p3) (hUd : U = p2 * q3 - q2 * p3)
    (hP : P = a * n') (hQ : Q = a' * n) (hT : T = c' * n) (hU : U = c * n')
    (hR : R = b * n' + b' * n)
    (hd : b ^ 2 - a * c = D * n ^ 2) (hd' : b' ^ 2 - a' * c' = D * n' ^ 2)
    (e00 : gq A B C p0 q0 p0 q0 = a * a') (e03 : gq A B C p0 q0 p3 q3 = b * b' + D * n * n')
    (e33 : gq A B C p3 q3 p3 q3 = c * c') :
    R ^ 2 * (A * n * n' - (q1 * q2 - q0 * q3)) = 0 := by
  simp only [gq] at e00 e03 e33
  have hA : R ^ 2 * A = a * a' * q3 ^ 2 - 2 * (b * b' + D * n * n') * q0 * q3 + c * c' * q0 ^ 2 := by
    rw [hRd]; linear_combination q3 ^ 2 * e00 - 2 * q0 * q3 * e03 + q0 ^ 2 * e33
  have hW : R ^ 2 * (q1 * q2 - q0 * q3) = (T * q0 + P * q3) * (U * q0 + Q * q3) - R ^ 2 * q0 * q3 := by
    rw [hPd, hQd, hRd, hTd, hUd]; ring
  have hW2 : R ^ 2 * (q1 * q2 - q0 * q3) =
      n * n' * (a * a' * q3 ^ 2 - 2 * (b * b' + D * n * n') * q0 * q3 + c * c' * q0 ^ 2) := by
    rw [hW, hT, hP, hU, hQ, hR]
    linear_combination (-n' ^ 2 * q0 * q3) * hd + (-n ^ 2 * q0 * q3) * hd'
  linear_combination (n * n') * hA - hW2

private theorem pair12 {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q S T U : ℚ}
    (hPd : P = p0 * q1 - q0 * p1) (hQd : Q = p0 * q2 - q0 * p2)
    (hSd : S = p1 * q2 - q1 * p2) (hTd : T = p1 * q3 - q1 * p3) (hUd : U = p2 * q3 - q2 * p3)
    (hP : P = a * n') (hQ : Q = a' * n) (hT : T = c' * n) (hU : U = c * n')
    (hS : S = b' * n - b * n')
    (hd : b ^ 2 - a * c = D * n ^ 2) (hd' : b' ^ 2 - a' * c' = D * n' ^ 2)
    (e11 : gq A B C p1 q1 p1 q1 = a * c') (e12 : gq A B C p1 q1 p2 q2 = b * b' - D * n * n')
    (e22 : gq A B C p2 q2 p2 q2 = c * a') :
    S ^ 2 * (A * n * n' - (q1 * q2 - q0 * q3)) = 0 := by
  simp only [gq] at e11 e12 e22
  have hA : S ^ 2 * A = a * c' * q2 ^ 2 - 2 * (b * b' - D * n * n') * q1 * q2 + c * a' * q1 ^ 2 := by
    rw [hSd]; linear_combination q2 ^ 2 * e11 - 2 * q1 * q2 * e12 + q1 ^ 2 * e22
  have hW : S ^ 2 * (q1 * q2 - q0 * q3) = S ^ 2 * q1 * q2 - (Q * q1 - P * q2) * (T * q2 - U * q1) := by
    rw [hPd, hQd, hSd, hTd, hUd]; ring
  have hW2 : S ^ 2 * (q1 * q2 - q0 * q3) =
      n * n' * (a * c' * q2 ^ 2 - 2 * (b * b' - D * n * n') * q1 * q2 + c * a' * q1 ^ 2) := by
    rw [hW, hT, hP, hU, hQ, hS]
    linear_combination (n ^ 2 * q1 * q2) * hd' + (n' ^ 2 * q1 * q2) * hd
  linear_combination (n * n') * hA - hW2

/-- All hypotheses of the identities $\Omega$ for $A$, as one bundle over the rationals (private). -/
private structure OmegaData (p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R S T U : ℚ) : Prop where
  hPd : P = p0 * q1 - q0 * p1
  hQd : Q = p0 * q2 - q0 * p2
  hRd : R = p0 * q3 - q0 * p3
  hSd : S = p1 * q2 - q1 * p2
  hTd : T = p1 * q3 - q1 * p3
  hUd : U = p2 * q3 - q2 * p3
  hP : P = a * n'
  hRmS : R - S = 2 * b * n'
  hU : U = c * n'
  hQ : Q = a' * n
  hRS : R + S = 2 * b' * n
  hT : T = c' * n
  hn : n ≠ 0
  hn' : n' ≠ 0
  hd0 : b ^ 2 - a * c ≠ 0
  hd : b ^ 2 - a * c = D * n ^ 2
  hd' : b' ^ 2 - a' * c' = D * n' ^ 2
  e00 : gq A B C p0 q0 p0 q0 = a * a'
  e01 : gq A B C p0 q0 p1 q1 = a * b'
  e02 : gq A B C p0 q0 p2 q2 = b * a'
  e03 : gq A B C p0 q0 p3 q3 = b * b' + D * n * n'
  e11 : gq A B C p1 q1 p1 q1 = a * c'
  e12 : gq A B C p1 q1 p2 q2 = b * b' - D * n * n'
  e13 : gq A B C p1 q1 p3 q3 = b * c'
  e22 : gq A B C p2 q2 p2 q2 = c * a'
  e23 : gq A B C p2 q2 p3 q3 = c * b'
  e33 : gq A B C p3 q3 p3 q3 = c * c'

private theorem omegaA_aux {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R S T U : ℚ}
    (h : OmegaData p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R S T U) :
    A * n * n' = q1 * q2 - q0 * q3 := by
  obtain ⟨hPd, hQd, hRd, hSd, hTd, hUd, hP, hRmS, hU, hQ, hRS, hT, hn, hn', hd0, hd, hd', e00, e01, e02, e03,
    e11, e12, e13, e22, e23, e33⟩ := h
  have hR' : R = b * n' + b' * n := by linarith
  have hS' : S = b' * n - b * n' := by linarith
  have z0 := pair01 hPd hQd hRd hSd hTd hP hQ hT hRS e00 e01 e11
  have z1 := pair02 hPd hQd hRd hSd hUd hP hQ hU hRmS e00 e02 e22
  have z2 := pair03 hPd hQd hRd hTd hUd hP hQ hT hU hR' hd hd' e00 e03 e33
  have z3 := pair12 hPd hQd hSd hTd hUd hP hQ hT hU hS' hd hd' e11 e12 e22
  have z4 := pair13 hPd hRd hSd hTd hUd hP hT hU hRmS e11 e13 e33
  have z5 := pair23 hQd hRd hSd hTd hUd hQ hT hU hRS e22 e23 e33
  by_contra hZ
  have hZ' : A * n * n' - (q1 * q2 - q0 * q3) ≠ 0 := sub_ne_zero.mpr hZ
  have sq0 : ∀ x : ℚ, x ^ 2 * (A * n * n' - (q1 * q2 - q0 * q3)) = 0 → x = 0 := fun x hx =>
    pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp hx).resolve_right hZ')
  have hP0 := sq0 _ z0
  have hU0 := sq0 _ z5
  have hR0 := sq0 _ z2
  have hS0 := sq0 _ z3
  have ha : a = 0 := by
    have : a * n' = 0 := by rw [← hP]; exact hP0
    exact (mul_eq_zero.mp this).resolve_right hn'
  have hc : c = 0 := by
    have : c * n' = 0 := by rw [← hU]; exact hU0
    exact (mul_eq_zero.mp this).resolve_right hn'
  have hb : b = 0 := by
    have : 2 * b * n' = 0 := by linear_combination -hRmS + hR0 - hS0
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact h2
    · exact absurd h1 hn'
  apply hd0
  rw [ha, hb, hc]; ring

private theorem omegaC_aux {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R S T U : ℚ}
    (h : OmegaData p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R S T U) :
    C * n * n' = p1 * p2 - p0 * p3 := by
  have := omegaA_aux (p0 := q0) (p1 := q1) (p2 := q2) (p3 := q3) (q0 := p0) (q1 := p1) (q2 := p2) (q3 := p3)
    (A := C) (B := B) (C := A) (a := a) (b := b) (c := c) (a' := a') (b' := b') (c' := c') (n := -n) (n' := -n') (D := D) (P := -P) (Q := -Q) (R := -R) (S := -S)
    (T := -T) (U := -U)
    { hPd := by linear_combination -h.hPd
      hQd := by linear_combination -h.hQd
      hRd := by linear_combination -h.hRd
      hSd := by linear_combination -h.hSd
      hTd := by linear_combination -h.hTd
      hUd := by linear_combination -h.hUd
      hP := by linear_combination -h.hP
      hRmS := by linear_combination -h.hRmS
      hU := by linear_combination -h.hU
      hQ := by linear_combination -h.hQ
      hRS := by linear_combination -h.hRS
      hT := by linear_combination -h.hT
      hn := neg_ne_zero.mpr h.hn
      hn' := neg_ne_zero.mpr h.hn'
      hd0 := h.hd0
      hd := by rw [h.hd]; ring
      hd' := by rw [h.hd']; ring
      e00 := by rw [gq_swap]; exact h.e00
      e01 := by rw [gq_swap]; exact h.e01
      e02 := by rw [gq_swap]; exact h.e02
      e03 := by rw [gq_swap, h.e03]; ring
      e11 := by rw [gq_swap]; exact h.e11
      e12 := by rw [gq_swap, h.e12]; ring
      e13 := by rw [gq_swap]; exact h.e13
      e22 := by rw [gq_swap]; exact h.e22
      e23 := by rw [gq_swap]; exact h.e23
      e33 := by rw [gq_swap]; exact h.e33 }
  linear_combination this

private theorem omegaB_aux {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R S T U : ℚ}
    (h : OmegaData p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' D P Q R S T U)
    (hD : D = B ^ 2 - A * C) (hA : A * n * n' = q1 * q2 - q0 * q3) (hC : C * n * n' = p1 * p2 - p0 * p3) :
    2 * B * n * n' = p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2 := by
  have e03 := h.e03
  have e12 := h.e12
  simp only [gq] at e03 e12
  have hM2 : (p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2) ^ 2 - 4 * (q1 * q2 - q0 * q3) * (p1 * p2 - p0 * p3) =
      (R - S) ^ 2 - 4 * P * U := by
    rw [h.hPd, h.hRd, h.hSd, h.hUd]; ring
  have hDn : D * n ^ 2 * n' ^ 2 = ((R - S) ^ 2 - 4 * P * U) / 4 := by
    linear_combination (-n' ^ 2) * h.hd - (R - S + 2 * b * n') / 4 * h.hRmS + U * h.hP + a * n' * h.hU
  have hβ : (2 * B * n * n') ^ 2 = (p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2) ^ 2 := by
    linear_combination (-4 * n ^ 2 * n' ^ 2) * hD + 4 * hDn + 4 * C * n * n' * hA +
      4 * (q1 * q2 - q0 * q3) * hC - hM2
  have hBM : n * n' * B * (p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2) =
      (p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2) ^ 2 / 2 := by
    linear_combination (n * n') * e03 - (n * n') * e12 + (p1 * p2 - p0 * p3) * hA +
      (q1 * q2 - q0 * q3) * hC + 2 * hDn - (1 / 2) * hM2
  have hz : (2 * B * n * n' - (p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2)) ^ 2 = 0 := by
    linear_combination hβ - 4 * hBM
  have := pow_eq_zero_iff two_ne_zero |>.mp hz
  linarith

private theorem converse_aux {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c a' b' c' n n' P Q R S T U : ℚ}
    (hPd : P = p0 * q1 - q0 * p1) (hQd : Q = p0 * q2 - q0 * p2) (hRd : R = p0 * q3 - q0 * p3)
    (hSd : S = p1 * q2 - q1 * p2) (hTd : T = p1 * q3 - q1 * p3) (hUd : U = p2 * q3 - q2 * p3)
    (hP : P = a * n') (hRmS : R - S = 2 * b * n') (hU : U = c * n') (hQ : Q = a' * n)
    (hRS : R + S = 2 * b' * n) (hT : T = c' * n)
    (hA : A * n * n' = q1 * q2 - q0 * q3) (hB : 2 * B * n * n' = p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2)
    (hC : C * n * n' = p1 * p2 - p0 * p3) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    gq A B C p0 q0 p0 q0 = a * a' ∧ gq A B C p1 q1 p1 q1 = a * c' ∧ gq A B C p2 q2 p2 q2 = c * a' ∧
      gq A B C p3 q3 p3 q3 = c * c' ∧ gq A B C p0 q0 p1 q1 = a * b' ∧ gq A B C p0 q0 p2 q2 = b * a' ∧
      gq A B C p1 q1 p3 q3 = b * c' ∧ gq A B C p2 q2 p3 q3 = c * b' ∧
      gq A B C p0 q0 p3 q3 + gq A B C p1 q1 p2 q2 = 2 * (b * b') := by
  have key : ∀ X Y : ℚ, n * n' * X = n * n' * Y → X = Y := fun X Y h =>
    mul_left_cancel₀ (mul_ne_zero hn hn') h
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_,
    key _ _ ?_⟩
  · have k : n * n' * gq A B C p0 q0 p0 q0 = P * Q := by
      rw [hPd, hQd]; simp only [gq]
      linear_combination p0 * p0 * hA + (p0 * q0 + q0 * p0) / 2 * hB + q0 * q0 * hC
    rw [k, hP, hQ]; ring
  · have k : n * n' * gq A B C p1 q1 p1 q1 = P * T := by
      rw [hPd, hTd]; simp only [gq]
      linear_combination p1 * p1 * hA + (p1 * q1 + q1 * p1) / 2 * hB + q1 * q1 * hC
    rw [k, hP, hT]; ring
  · have k : n * n' * gq A B C p2 q2 p2 q2 = Q * U := by
      rw [hQd, hUd]; simp only [gq]
      linear_combination p2 * p2 * hA + (p2 * q2 + q2 * p2) / 2 * hB + q2 * q2 * hC
    rw [k, hQ, hU]; ring
  · have k : n * n' * gq A B C p3 q3 p3 q3 = T * U := by
      rw [hTd, hUd]; simp only [gq]
      linear_combination p3 * p3 * hA + (p3 * q3 + q3 * p3) / 2 * hB + q3 * q3 * hC
    rw [k, hT, hU]; ring
  · have k : n * n' * gq A B C p0 q0 p1 q1 = P * (R + S) / 2 := by
      rw [hPd, hRd, hSd]; simp only [gq]
      linear_combination p0 * p1 * hA + (p0 * q1 + q0 * p1) / 2 * hB + q0 * q1 * hC
    rw [k, hP, hRS]; ring
  · have k : n * n' * gq A B C p0 q0 p2 q2 = Q * (R - S) / 2 := by
      rw [hQd, hRd, hSd]; simp only [gq]
      linear_combination p0 * p2 * hA + (p0 * q2 + q0 * p2) / 2 * hB + q0 * q2 * hC
    rw [k, hQ, hRmS]; ring
  · have k : n * n' * gq A B C p1 q1 p3 q3 = T * (R - S) / 2 := by
      rw [hTd, hRd, hSd]; simp only [gq]
      linear_combination p1 * p3 * hA + (p1 * q3 + q1 * p3) / 2 * hB + q1 * q3 * hC
    rw [k, hT, hRmS]; ring
  · have k : n * n' * gq A B C p2 q2 p3 q3 = U * (R + S) / 2 := by
      rw [hUd, hRd, hSd]; simp only [gq]
      linear_combination p2 * p3 * hA + (p2 * q3 + q2 * p3) / 2 * hB + q2 * q3 * hC
    rw [k, hU, hRS]; ring
  · have k : n * n' * (gq A B C p0 q0 p3 q3 + gq A B C p1 q1 p2 q2) = (R - S) * (R + S) / 2 := by
      rw [hRd, hSd]; simp only [gq]
      linear_combination (p0 * p3 + p1 * p2) * hA + (p0 * q3 + q0 * p3 + p1 * q2 + q1 * p2) / 2 * hB +
        (q0 * q3 + q1 * q2) * hC
    rw [k, hRmS, hRS]; ring

private theorem converse_disc_aux {p0 p1 p2 p3 q0 q1 q2 q3 A B C a b c n n' P R S U : ℚ}
    (hPd : P = p0 * q1 - q0 * p1) (hRd : R = p0 * q3 - q0 * p3)
    (hSd : S = p1 * q2 - q1 * p2) (hUd : U = p2 * q3 - q2 * p3)
    (hP : P = a * n') (hRmS : R - S = 2 * b * n') (hU : U = c * n')
    (hA : A * n * n' = q1 * q2 - q0 * q3) (hB : 2 * B * n * n' = p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2)
    (hC : C * n * n' = p1 * p2 - p0 * p3) (hn' : n' ≠ 0) :
    b ^ 2 - a * c = n ^ 2 * (B ^ 2 - A * C) := by
  have hM2 : (p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2) ^ 2 - 4 * (q1 * q2 - q0 * q3) * (p1 * p2 - p0 * p3) =
      (R - S) ^ 2 - 4 * P * U := by
    rw [hPd, hRd, hSd, hUd]; ring
  apply mul_left_cancel₀ (pow_ne_zero 2 hn')
  linear_combination -(R - S + 2 * b * n') / 4 * hRmS + U * hP + a * n' * hU -
    (2 * B * n * n' + (p0 * q3 + q0 * p3 - p1 * q2 - q1 * p2)) / 4 * hB + C * n * n' * hA +
    (q1 * q2 - q0 * q3) * hC - (1 / 4) * hM2

/-! ### The identities $\Omega$ and their converse -/

/-- **Gauss, *Disq. Arith.* Art. 235, the identities $\Omega$ for $F$:** let
$F = (A, B, C)$ be transformed into $f f'$, $f = (a, b, c)$, $f' = (a', b', c')$, by the bilinear substitution
$(p, q)$ (`TransformsInto`), let the six relations $P = an'$, $R - S = 2bn'$, $U = cn'$, $Q = a'n$, $R + S = 2b'n$,
$T = c'n$ hold with rational $n, n'$ (`GaussRelations`), and let $f$, $f'$ be nondegenerate ($d = b^2 - ac \ne 0$,
$d' = b'^2 - a'c' \ne 0$). Then
$$A n n' = q_1 q_2 - q_0 q_3,\quad 2 B n n' = p_0 q_3 + q_0 p_3 - p_1 q_2 - q_1 p_2,\quad
C n n' = p_1 p_2 - p_0 p_3$$
(`OmegaFormEquations`; Gauss's $Ann' = q'q'' - qq'''$, $2Bnn' = pq''' + qp''' - p'q'' - q'p''$,
$Cnn' = p'p'' - pp'''$ with $0$-based indices). The first six equations of $\Omega$ are the hypotheses
(`GaussRelations`).

Differences from the source: Gauss leaves the derivation to the reader; the nondegeneracy $d, d' \ne 0$ is an extra
hypothesis here (it forces $n, n' \ne 0$ and $D \ne 0$ by `disc_mul_sq_of_rel_first`). The divisibility consequences
listed in the historical sources ($mm'$ divides $aa', \dots$) are proved in `CompositionGcd.lean`, not here. -/
@[kb "gauss1801" "Art. 235"]
theorem art235_omega {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n')
    (hd : gaussDet a b c ≠ 0) (hd' : gaussDet a' b' c' ≠ 0) :
    OmegaFormEquations A B C p q n n' := by
  obtain ⟨hT, h0, h1, h2, h3, h4, h5⟩ := hR
  have hdq : ((b : ℚ) ^ 2 - a * c) ≠ 0 := by
    intro h; apply hd; unfold gaussDet; exact_mod_cast h
  have hdq' : ((b' : ℚ) ^ 2 - a' * c') ≠ 0 := by
    intro h; apply hd'; unfold gaussDet; exact_mod_cast h
  have hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0 :=
    exists_eval_ne_zero_of_disc_ne_zero (by rw [disc_gaussForm]; intro h; apply hd; omega)
  have hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0 :=
    exists_eval_ne_zero_of_disc_ne_zero (by rw [disc_gaussForm]; intro h; apply hd'; omega)
  have e1 := disc_mul_sq_of_rel_first hT (by simpa using h3) (by simpa using h4) (by simpa using h5) hf'
  have e2 := disc_mul_sq_of_rel_second hT (by simpa using h0) (by simpa using h1) (by simpa using h2) hf
  simp only [disc_gaussForm, gaussDet] at e1 e2
  push_cast at e1 e2
  have hd1 : (b : ℚ) ^ 2 - a * c = ((B : ℚ) ^ 2 - A * C) * n ^ 2 := by linear_combination e1 / 4
  have hd2 : (b' : ℚ) ^ 2 - a' * c' = ((B : ℚ) ^ 2 - A * C) * n' ^ 2 := by linear_combination e2 / 4
  have hn : n ≠ 0 := by
    intro h; apply hdq; rw [hd1, h]; ring
  have hn' : n' ≠ 0 := by
    intro h; apply hdq'; rw [hd2, h]; ring
  have hΔ := art235_delta_eq (Δ := A * p 0 * p 3 + B * (p 0 * q 3 + q 0 * p 3) + C * q 0 * q 3 - b * b')
    hT h0 h1 h2 h3 h4 h5 (by ring) hf hf'
  simp only [gaussDet] at hΔ
  push_cast at hΔ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := transformsInto_iff_coefficientEquations.1 hT
  have g00 : gq A B C (p 0) (q 0) (p 0) (q 0) = a * a' := by
    have := congrArg (Int.cast : ℤ → ℚ) c1; rw [cast_eval] at this; simpa using this
  have g11 : gq A B C (p 1) (q 1) (p 1) (q 1) = a * c' := by
    have := congrArg (Int.cast : ℤ → ℚ) c2; rw [cast_eval] at this; simpa using this
  have g22 : gq A B C (p 2) (q 2) (p 2) (q 2) = c * a' := by
    have := congrArg (Int.cast : ℤ → ℚ) c3; rw [cast_eval] at this; simpa using this
  have g33 : gq A B C (p 3) (q 3) (p 3) (q 3) = c * c' := by
    have := congrArg (Int.cast : ℤ → ℚ) c4; rw [cast_eval] at this; simpa using this
  have g01 : gq A B C (p 0) (q 0) (p 1) (q 1) = a * b' := by
    have := congrArg (Int.cast : ℤ → ℚ) c5; rw [cast_polar] at this; simpa using this
  have g02 : gq A B C (p 0) (q 0) (p 2) (q 2) = b * a' := by
    have := congrArg (Int.cast : ℤ → ℚ) c6; rw [cast_polar] at this; simpa using this
  have g13 : gq A B C (p 1) (q 1) (p 3) (q 3) = b * c' := by
    have := congrArg (Int.cast : ℤ → ℚ) c7; rw [cast_polar] at this; simpa using this
  have g23 : gq A B C (p 2) (q 2) (p 3) (q 3) = c * b' := by
    have := congrArg (Int.cast : ℤ → ℚ) c8; rw [cast_polar] at this; simpa using this
  have g9 : gq A B C (p 0) (q 0) (p 3) (q 3) + gq A B C (p 1) (q 1) (p 2) (q 2) = 2 * (b * b') := by
    have := congrArg (Int.cast : ℤ → ℚ) c9
    rw [Int.cast_add, cast_polar, cast_polar] at this; simpa using this
  have g03 : gq A B C (p 0) (q 0) (p 3) (q 3) = b * b' + ((B : ℚ) ^ 2 - A * C) * n * n' := by
    simp only [gq]
    linear_combination hΔ
  have g12 : gq A B C (p 1) (q 1) (p 2) (q 2) = b * b' - ((B : ℚ) ^ 2 - A * C) * n * n' := by
    linear_combination g9 - g03
  have hPd : (minors p q 0 : ℚ) = p 0 * q 1 - q 0 * p 1 := by simp [minors]
  have hQd : (minors p q 1 : ℚ) = p 0 * q 2 - q 0 * p 2 := by simp [minors]
  have hRd : (minors p q 2 : ℚ) = p 0 * q 3 - q 0 * p 3 := by simp [minors]
  have hSd : (minors p q 3 : ℚ) = p 1 * q 2 - q 1 * p 2 := by simp [minors]
  have hTd : (minors p q 4 : ℚ) = p 1 * q 3 - q 1 * p 3 := by simp [minors]
  have hUd : (minors p q 5 : ℚ) = p 2 * q 3 - q 2 * p 3 := by simp [minors]
  have hO : OmegaData (p 0) (p 1) (p 2) (p 3) (q 0) (q 1) (q 2) (q 3) (A : ℚ) B C a b c a' b' c' n n'
      ((B : ℚ) ^ 2 - A * C) (minors p q 0 : ℚ) (minors p q 1 : ℚ) (minors p q 2 : ℚ) (minors p q 3 : ℚ)
      (minors p q 4 : ℚ) (minors p q 5 : ℚ) :=
    { hPd := hPd, hQd := hQd, hRd := hRd, hSd := hSd, hTd := hTd, hUd := hUd
      hP := h0, hRmS := h1, hU := h2, hQ := h3, hRS := h4, hT := h5
      hn := hn, hn' := hn', hd0 := hdq, hd := by linear_combination hd1, hd' := by linear_combination hd2
      e00 := g00, e01 := g01, e02 := g02, e03 := g03, e11 := g11, e12 := g12, e13 := g13, e22 := g22
      e23 := g23, e33 := g33 }
  have hA := omegaA_aux hO
  have hC := omegaC_aux hO
  unfold OmegaFormEquations
  exact ⟨hA, omegaB_aux hO rfl hA hC, hC⟩

/-- **Gauss, *Disq. Arith.* Art. 235, end, the converse:** let $p_i, q_i$ be integers,
$n, n'$ **nonzero** rationals, $F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$ integral forms, and let the nine
equations $\Omega$ hold: the six relations $P = an'$, $R - S = 2bn'$, $U = cn'$, $Q = a'n$, $R + S = 2b'n$,
$T = c'n$ (`OmegaRelations`) and $Ann' = q_1q_2 - q_0q_3$, $2Bnn' = p_0q_3 + q_0p_3 - p_1q_2 - q_1p_2$,
$Cnn' = p_1p_2 - p_0p_3$ (`OmegaFormEquations`). Then $F$ is transformed into $f f'$ by the substitution
(`TransformsInto`, i.e. the nine coefficient equations $[1]$-$[9]$ hold, `CoefficientEquations`), and
$b^2 - ac = n^2 (B^2 - AC)$, $b'^2 - a'c' = n'^2 (B^2 - AC)$ (in $\mathbb Q$; the historical sources write $n^2$ and $n'^2$
the same way).

Differences from the source: none in substance. The historical sources' "nonzero $n, n'$" is a hypothesis and is needed (each
coefficient equation is obtained by cancelling $nn'$, the determinant relations by cancelling $n'^2$, resp. $n^2$);
$A, B, C, a, \dots$ are integers, as the library's forms are (the historical sources allow rationals). Gauss leaves the computation
to the reader; here $nn' \cdot [\,i\,]$ equals a product of two of the six numbers, which equals $nn'$ times the
right-hand side of $[\,i\,]$. -/
@[kb "gauss1801" "Art. 235"]
theorem art235_omega_converse {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hn : n ≠ 0) (hn' : n' ≠ 0) (hrel : OmegaRelations a b c a' b' c' p q n n')
    (hom : OmegaFormEquations A B C p q n n') :
    TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q ∧
      (gaussDet a b c : ℚ) = n ^ 2 * gaussDet A B C ∧ (gaussDet a' b' c' : ℚ) = n' ^ 2 * gaussDet A B C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hrel
  obtain ⟨hA, hB, hC⟩ := hom
  have hPd : (minors p q 0 : ℚ) = p 0 * q 1 - q 0 * p 1 := by simp [minors]
  have hQd : (minors p q 1 : ℚ) = p 0 * q 2 - q 0 * p 2 := by simp [minors]
  have hRd : (minors p q 2 : ℚ) = p 0 * q 3 - q 0 * p 3 := by simp [minors]
  have hSd : (minors p q 3 : ℚ) = p 1 * q 2 - q 1 * p 2 := by simp [minors]
  have hTd : (minors p q 4 : ℚ) = p 1 * q 3 - q 1 * p 3 := by simp [minors]
  have hUd : (minors p q 5 : ℚ) = p 2 * q 3 - q 2 * p 3 := by simp [minors]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    converse_aux hPd hQd hRd hSd hTd hUd h0 h1 h2 h3 h4 h5 hA hB hC hn hn'
  refine ⟨transformsInto_of_coefficientEquations ?_, ?_, ?_⟩
  · unfold CoefficientEquations
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : (((gaussForm A B C).eval (p 0) (q 0) : ℤ) : ℚ) = ((a * a' : ℤ) : ℚ) := by
        rw [cast_eval]; push_cast; exact g1
      exact_mod_cast this
    · have : (((gaussForm A B C).eval (p 1) (q 1) : ℤ) : ℚ) = ((a * c' : ℤ) : ℚ) := by
        rw [cast_eval]; push_cast; exact g2
      exact_mod_cast this
    · have : (((gaussForm A B C).eval (p 2) (q 2) : ℤ) : ℚ) = ((c * a' : ℤ) : ℚ) := by
        rw [cast_eval]; push_cast; exact g3
      exact_mod_cast this
    · have : (((gaussForm A B C).eval (p 3) (q 3) : ℤ) : ℚ) = ((c * c' : ℤ) : ℚ) := by
        rw [cast_eval]; push_cast; exact g4
      exact_mod_cast this
    · have : ((gaussPolar A B C (p 0) (q 0) (p 1) (q 1) : ℤ) : ℚ) = ((a * b' : ℤ) : ℚ) := by
        rw [cast_polar]; push_cast; exact g5
      exact_mod_cast this
    · have : ((gaussPolar A B C (p 0) (q 0) (p 2) (q 2) : ℤ) : ℚ) = ((b * a' : ℤ) : ℚ) := by
        rw [cast_polar]; push_cast; exact g6
      exact_mod_cast this
    · have : ((gaussPolar A B C (p 1) (q 1) (p 3) (q 3) : ℤ) : ℚ) = ((b * c' : ℤ) : ℚ) := by
        rw [cast_polar]; push_cast; exact g7
      exact_mod_cast this
    · have : ((gaussPolar A B C (p 2) (q 2) (p 3) (q 3) : ℤ) : ℚ) = ((c * b' : ℤ) : ℚ) := by
        rw [cast_polar]; push_cast; exact g8
      exact_mod_cast this
    · have : ((gaussPolar A B C (p 0) (q 0) (p 3) (q 3) + gaussPolar A B C (p 1) (q 1) (p 2) (q 2) : ℤ) : ℚ) =
          ((2 * (b * b') : ℤ) : ℚ) := by
        rw [Int.cast_add, cast_polar, cast_polar]; push_cast; exact g9
      exact_mod_cast this
  · have := converse_disc_aux hPd hRd hSd hUd h0 h1 h2 hA hB hC hn'
    simp only [gaussDet]; push_cast; exact this
  · -- the same with the roles of the two factors exchanged: Q, R + S, T
    have hM2 : (p 0 * q 3 + q 0 * p 3 - p 1 * q 2 - q 1 * p 2 : ℚ) ^ 2 -
        4 * (q 1 * q 2 - q 0 * q 3) * (p 1 * p 2 - p 0 * p 3) =
        ((minors p q 2 : ℚ) + minors p q 3) ^ 2 - 4 * (minors p q 1 : ℚ) * minors p q 4 := by
      rw [hQd, hRd, hSd, hTd]; ring
    simp only [gaussDet]; push_cast
    apply mul_left_cancel₀ (pow_ne_zero 2 hn)
    linear_combination -((minors p q 2 : ℚ) + minors p q 3 + 2 * b' * n) / 4 * h4 +
      (minors p q 4 : ℚ) * h3 + a' * n * h5 -
      (2 * B * n * n' + (p 0 * q 3 + q 0 * p 3 - p 1 * q 2 - q 1 * p 2)) / 4 * hB + C * n * n' * hA +
      (q 1 * q 2 - q 0 * q 3) * hC - (1 / 4) * hM2

end QuadFormsKB.Historical.Gauss
