/-
# Cassels, Chapter 9, §3: the closed formula (3.10) and the notes to Lemma 3.2

**Layer:** classically integral forms `f : QuadForm ℤ n` and their Gram determinant $d = $ `Siegel.gramDet f`
$= \det H/2^n$ (Cassels' $d(f) = \det(f_{ij})$), real signature $(r, s)$ as in the library's Lemma 3.2
(`Siegel.exists_pos_value_le`), and Cassels' constant $\theta(r, s)$ = `Siegel.casselsDelta r s`
(Cassels writes $\theta$ in the notes to the lemma, $\delta$ in its statement; the library calls it `casselsDelta`).

**Source (paraphrased).** Cassels, *Rational Quadratic Forms*, Ch. 9, §3, p. 136, Lemma 3.2 and the notes after its proof.
The closed formula (3.10) for the constant is read from the page image:
$$\theta(r, s)^n = 3^{s}\,(4/3)^{n(n-1)/2},\qquad n = r + s,\ r \ge 1.$$
The library defines the constant by the recursion of the proof ((3.17), (3.21)), so (3.10) is a theorem here.

**Proves**
* `casselsDelta_pow` (formula (3.10)), with the values `casselsDelta_one_one` $= 2$ and `casselsDelta_two_zero`
  $= 2/\sqrt3$;
* `casselsLemma32_note2_hyperbolic`, `casselsLemma32_note2_definite` (Note 2): for $f = 2xy$ and
  $f = 2x^2 + 2xy + 2y^2$ the constant of Lemma 3.2 cannot be improved for $n = 2$: every positive integral value is at
  least $\theta(r, s)\lvert d\rvert^{1/2}$, with equality attained, so for every $\theta' < \theta(r, s)$ the conclusion
  of Lemma 3.2 with $\theta'$ in place of $\theta$ fails;
* `CasselsLemma32Real` (Note 1, Blaney 1948), a **named statement** (not proved): Lemma 3.2 for a real symmetric matrix
  instead of an integral form; `exists_pos_value_le_of_real` derives the library's integral Lemma 3.2 from it.

*Indices:* $0$-based (`Fin n`); Cassels' $x_1, \dots, x_n$ are $x_0, \dots, x_{n-1}$ here. In the examples the
variables $x, y$ of the book are $x_0, x_1$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec3

open Matrix

noncomputable section

namespace QuadFormsKB.Siegel

/-! ### Formula (3.10) -/

/-- Helper: the triangular number $n(n-1)/2$ satisfies $T(n+1) = T(n) + n$. -/
theorem triNum_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rcases n with _ | m
  · simp
  · have h : (m + 1 + 1) * (m + 1 + 1 - 1) = (m + 1) * (m + 1 - 1) + 2 * (m + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

/-- Helper: $(X^{m/(m+1)})^{m+1} = X^m$ for $X \ge 0$, with the exponent given as any real $q = m/(m+1)$. -/
theorem rpow_frac_pow {X : ℝ} (hX : 0 ≤ X) (m : ℕ) {q : ℝ} (hq : q = (m : ℝ) / ((m : ℝ) + 1)) :
    (X ^ q) ^ (m + 1) = X ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX, ← Real.rpow_natCast X m]
  congr 1
  rw [hq]
  push_cast
  field_simp

/-- **Cassels, Lemma 3.2, formula (3.10)** (Ch. 9, p. 136): the constant of Lemma 3.2 satisfies
$\theta(r, s)^n = 3^{s}\,(4/3)^{n(n-1)/2}$ with $n = r + s$, for $r \ge 1$ and $s \ge 0$. Here $\theta(r, s)$ is
`casselsDelta r s`, defined by the recursion (3.17), (3.21) of the proof; the exponent $n(n-1)/2$ is the natural
number (natural-number division, exact because $n(n-1)$ is even). -/
@[kb "cassels1978" "Ch. 9, Lemma 3.2, (3.10), p. 136"]
theorem casselsDelta_pow : ∀ r s : ℕ, 1 ≤ r →
    casselsDelta r s ^ (r + s) = 3 ^ s * (4 / 3 : ℝ) ^ ((r + s) * (r + s - 1) / 2)
  | 0, _, h => absurd h (by norm_num)
  | 1, 0, _ => by simp [casselsDelta]
  | 1, s + 1, _ => by
    have ih := casselsDelta_pow (s + 1) 0 (by omega)
    have e1 : 1 + (s + 1) = s + 1 + 1 := by ring
    have e2 : s + 1 + 0 = s + 1 := rfl
    rw [e2] at ih
    rw [e1, casselsDelta, rpow_frac_pow (by have := Ch9Sec3.casselsDelta_nonneg (s + 1) 0; positivity) (s + 1)
      (by push_cast; ring), mul_pow, ih, triNum_succ (s + 1)]
    have h4' : (4 : ℝ) ^ (s + 1) = 3 ^ (s + 1) * (4 / 3) ^ (s + 1) := by rw [← mul_pow]; norm_num
    rw [pow_zero, one_mul, h4', pow_add (4 / 3 : ℝ)]
    ring
  | r + 2, s, _ => by
    have ih := casselsDelta_pow (r + 1) s (by omega)
    have e1 : r + 2 + s = (r + 1 + s) + 1 := by ring
    rw [e1, casselsDelta, rpow_frac_pow
      (by have := Ch9Sec3.casselsDelta_nonneg (r + 1) s; positivity) (r + 1 + s) (by push_cast; ring_nf),
      mul_pow, ih, triNum_succ (r + 1 + s)]
    ring
termination_by r s => r + s

/-- **Value of the constant for $(r, s) = (1, 1)$:** $\theta(1, 1) = 2$ (from the recursion (3.21): $\theta(1,1)^2 =
4\,\theta(1,0)$). -/
theorem casselsDelta_one_one : casselsDelta 1 1 = 2 := by
  have h := casselsDelta.eq_3 0
  rw [h, show casselsDelta (0 + 1) 0 = 1 by rw [casselsDelta]]
  rw [show (((0 : ℕ) : ℝ) + 1) / (((0 : ℕ) : ℝ) + 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [show (4 * 1 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- **Value of the constant for $(r, s) = (2, 0)$:** $\theta(2, 0) = 2/\sqrt3$ (from the recursion (3.17):
$\theta(2,0)^2 = 4\,\theta(1,0)/3$). -/
theorem casselsDelta_two_zero : casselsDelta 2 0 = 2 / Real.sqrt 3 := by
  have h := casselsDelta.eq_4 0 0
  rw [h, show casselsDelta (0 + 1) 0 = 1 by rw [casselsDelta]]
  rw [show (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + 1) / (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + 2) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  rw [show (4 / 3 * 1 : ℝ) = 2 ^ 2 / 3 by norm_num, Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]

/-! ### Note 2: the constant cannot be improved for $n = 2$ -/

/-- Helper: the form $2xy$ (variables $x_0, x_1$): `BinQF.mk 0 2 0`. Its Gram matrix is
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$, so $d = -1$; its real signature is $(r, s) = (1, 1)$. -/
def noteFormHyperbolic : QuadForm ℤ 2 := BinQF.mk 0 2 0

/-- Helper: the form $2x^2 + 2xy + 2y^2$ (variables $x_0, x_1$): `BinQF.mk 2 2 2`. Its Gram matrix is
$\begin{pmatrix}2&1\\1&2\end{pmatrix}$, so $d = 3$; it is positive definite, $(r, s) = (2, 0)$. -/
def noteFormDefinite : QuadForm ℤ 2 := BinQF.mk 2 2 2

/-- Helper: integer values of a binary form $ax_0^2 + bx_0x_1 + cx_1^2$. -/
theorem eval_binMk_int (a b c : ℤ) (x : Fin 2 → ℤ) :
    QuadForm.eval (BinQF.mk a b c) x = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, BinQF.mk, QuadForm.ofUpper]
  ring

/-- Helper: real values of the base change of a binary form $ax_0^2 + bx_0x_1 + cx_1^2$. -/
theorem eval_binMk_real (a b c : ℤ) (x : Fin 2 → ℝ) :
    ((BinQF.mk a b c).map (Int.castRingHom ℝ)).eval x = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, QuadForm.map, BinQF.mk, QuadForm.ofUpper]
  ring

/-- Helper: if every positive integral value is at least $\delta D$, then no $\theta' < \delta$ gives a positive
integral value at most $\theta' D$ (for $D > 0$). -/
theorem not_exists_small_of_lower {n : ℕ} {f : QuadForm ℤ n} {δ θ' D : ℝ} (hD : 0 < D) (hθ : θ' < δ)
    (hlow : ∀ a : Fin n → ℤ, 0 < f.eval a → δ * D ≤ (f.eval a : ℝ)) :
    ¬ ∃ a : Fin n → ℤ, 0 < f.eval a ∧ (f.eval a : ℝ) ≤ θ' * D := by
  rintro ⟨a, ha, h⟩
  have := hlow a ha
  nlinarith

/-- Helper: the Hessian of `noteFormHyperbolic` is $\begin{pmatrix}0&2\\2&0\end{pmatrix}$. -/
theorem hessian_noteFormHyperbolic : noteFormHyperbolic.hessian = !![0, 2; 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [noteFormHyperbolic, QuadForm.hessian, BinQF.mk, QuadForm.ofUpper]

/-- Helper: the Hessian of `noteFormDefinite` is $\begin{pmatrix}4&2\\2&4\end{pmatrix}$. -/
theorem hessian_noteFormDefinite : noteFormDefinite.hessian = !![4, 2; 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [noteFormDefinite, QuadForm.hessian, BinQF.mk, QuadForm.ofUpper]

/-- Helper: $2xy$ is real-equivalent to $x^2 - y^2$ (signature $(1, 1)$). -/
theorem isometricGL_noteFormHyperbolic :
    IsometricGL (noteFormHyperbolic.map (Int.castRingHom ℝ)) (QuadForm.diag ![(1 : ℝ), -1]) := by
  have hM : (!![(1 / 2 : ℝ), 1 / 2; 1, -1]).det ≠ 0 := by
    simp [Matrix.det_fin_two_of]; norm_num
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 / 2 : ℝ), 1 / 2; 1, -1] hM, fun x => ?_⟩
  have e : (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 / 2 : ℝ), 1 / 2; 1, -1] hM).val =
    !![(1 / 2 : ℝ), 1 / 2; 1, -1] := rfl
  rw [e, noteFormHyperbolic, eval_binMk_real]
  simp [QuadForm.eval, QuadForm.evalIn_diag, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  ring

/-- Helper: $2x^2 + 2xy + 2y^2$ is real-equivalent to $x^2 + y^2$ (signature $(2, 0)$); the change of variables is
$(v_0, v_1) \mapsto (v_0/\sqrt2 - v_1/\sqrt6,\ 2v_1/\sqrt6)$. -/
theorem isometricGL_noteFormDefinite :
    IsometricGL (noteFormDefinite.map (Int.castRingHom ℝ)) (QuadForm.diag ![(1 : ℝ), 1]) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have ha : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hb : ((Real.sqrt 6)⁻¹) ^ 2 = 1 / 6 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hM : (!![(Real.sqrt 2)⁻¹, -(Real.sqrt 6)⁻¹; 0, 2 * (Real.sqrt 6)⁻¹]).det ≠ 0 := by
    simp [Matrix.det_fin_two_of]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt 2)⁻¹, -(Real.sqrt 6)⁻¹; 0, 2 * (Real.sqrt 6)⁻¹] hM, fun x => ?_⟩
  have e : (Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt 2)⁻¹, -(Real.sqrt 6)⁻¹; 0, 2 * (Real.sqrt 6)⁻¹] hM).val =
    !![(Real.sqrt 2)⁻¹, -(Real.sqrt 6)⁻¹; 0, 2 * (Real.sqrt 6)⁻¹] := rfl
  rw [e, noteFormDefinite, eval_binMk_real]
  simp [QuadForm.eval, QuadForm.evalIn_diag, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  linear_combination (2 * x 0 ^ 2) * ha + (6 * x 1 ^ 2) * hb

/-- **Cassels, Lemma 3.2, Note 2, first example** (Ch. 9, p. 136): $f = 2xy$ shows that the constant of Lemma 3.2
cannot be improved for $n = 2$, $(r, s) = (1, 1)$. Here $f$ is classically integral and regular (Gram matrix
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$), $d = -1$, real-equivalent to $x_0^2 - x_1^2$, and $\theta(1, 1) = 2$
(`casselsDelta_one_one`). Every integral $\mathbf a$ with $f(\mathbf a) > 0$ has $f(\mathbf a) \ge \theta(1,1)\lvert d\rvert^{1/2}$,
with equality at $\mathbf a = (1, 1)$; hence for every $\theta' < \theta(1, 1)$ the conclusion of Lemma 3.2 with $\theta'$
in place of $\theta$ (some integral $\mathbf a$ with $0 < f(\mathbf a) \le \theta'\lvert d\rvert^{1/2}$) fails for this $f$. -/
@[kb "cassels1978" "Ch. 9, Lemma 3.2, Note 2, p. 136"]
theorem casselsLemma32_note2_hyperbolic :
    IsClassicallyIntegral noteFormHyperbolic ∧ noteFormHyperbolic.hessian.det ≠ 0 ∧
      gramDet noteFormHyperbolic = -1 ∧ casselsDelta 1 1 = 2 ∧
      (∃ ε : Fin 2 → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        IsometricGL (noteFormHyperbolic.map (Int.castRingHom ℝ)) (QuadForm.diag ε) ∧
        (Finset.univ.filter fun i => ε i = 1).card = 1) ∧
      (∀ a : Fin 2 → ℤ, 0 < noteFormHyperbolic.eval a →
        casselsDelta 1 1 * |gramDet noteFormHyperbolic| ^ ((1 : ℝ) / (2 : ℕ)) ≤ (noteFormHyperbolic.eval a : ℝ)) ∧
      (∃ a : Fin 2 → ℤ, (noteFormHyperbolic.eval a : ℝ) =
        casselsDelta 1 1 * |gramDet noteFormHyperbolic| ^ ((1 : ℝ) / (2 : ℕ))) ∧
      ∀ θ' : ℝ, θ' < casselsDelta 1 1 →
        ¬ ∃ a : Fin 2 → ℤ, 0 < noteFormHyperbolic.eval a ∧
          (noteFormHyperbolic.eval a : ℝ) ≤ θ' * |gramDet noteFormHyperbolic| ^ ((1 : ℝ) / (2 : ℕ)) := by
  have hd : noteFormHyperbolic.hessian.det = -4 := by
    rw [hessian_noteFormHyperbolic, Matrix.det_fin_two_of]; norm_num
  have hg : gramDet noteFormHyperbolic = -1 := by
    rw [gramDet, hd]; norm_num
  have hD : |gramDet noteFormHyperbolic| ^ ((1 : ℝ) / (2 : ℕ)) = 1 := by
    rw [hg]; simp
  have hev : ∀ a : Fin 2 → ℤ, noteFormHyperbolic.eval a = 2 * (a 0 * a 1) := fun a => by
    rw [noteFormHyperbolic, eval_binMk_int]; ring
  have hlow : ∀ a : Fin 2 → ℤ, 0 < noteFormHyperbolic.eval a →
      casselsDelta 1 1 * |gramDet noteFormHyperbolic| ^ ((1 : ℝ) / (2 : ℕ)) ≤ (noteFormHyperbolic.eval a : ℝ) := by
    intro a ha
    rw [hD, casselsDelta_one_one, mul_one]
    rw [hev] at ha ⊢
    have : (2 : ℤ) ≤ 2 * (a 0 * a 1) := by
      generalize a 0 * a 1 = p at ha ⊢
      omega
    exact_mod_cast this
  refine ⟨⟨!![0, 1; 1, 0], ?_, fun x => ?_⟩, by rw [hd]; norm_num, hg, casselsDelta_one_one,
    ⟨![1, -1], fun i => by fin_cases i <;> simp, isometricGL_noteFormHyperbolic, ?_⟩, hlow,
    ⟨![1, 1], ?_⟩, fun θ' hθ => not_exists_small_of_lower (by rw [hD]; norm_num) hθ (by
      intro a ha; simpa [hD] using hlow a ha)⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [noteFormHyperbolic, eval_binMk_int]
    simp [gramForm, dotProduct, Fin.sum_univ_two, Matrix.mulVec]
    ring
  · have : (Finset.univ.filter fun i : Fin 2 => (![1, -1] : Fin 2 → ℝ) i = 1) = {0} := by
      ext i; fin_cases i <;> simp
      norm_num
    rw [this]; rfl
  · rw [hD, casselsDelta_one_one, hev]; simp

/-- **Cassels, Lemma 3.2, Note 2, second example** (Ch. 9, p. 136): $f = 2x^2 + 2xy + 2y^2$ shows that the constant of
Lemma 3.2 cannot be improved for $n = 2$, $(r, s) = (2, 0)$. Here $f$ is classically integral and regular (Gram
matrix $\begin{pmatrix}2&1\\1&2\end{pmatrix}$), $d = 3$, positive definite (real-equivalent to $x_0^2 + x_1^2$), and
$\theta(2, 0) = 2/\sqrt3$ (`casselsDelta_two_zero`). Every integral $\mathbf a$ with $f(\mathbf a) > 0$ has
$f(\mathbf a) \ge \theta(2,0)\lvert d\rvert^{1/2} = 2$, with equality at $\mathbf a = (1, 0)$; hence for every
$\theta' < \theta(2, 0)$ the conclusion of Lemma 3.2 with $\theta'$ in place of $\theta$ fails for this $f$. -/
@[kb "cassels1978" "Ch. 9, Lemma 3.2, Note 2, p. 136"]
theorem casselsLemma32_note2_definite :
    IsClassicallyIntegral noteFormDefinite ∧ noteFormDefinite.hessian.det ≠ 0 ∧
      gramDet noteFormDefinite = 3 ∧ casselsDelta 2 0 = 2 / Real.sqrt 3 ∧
      (∃ ε : Fin 2 → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        IsometricGL (noteFormDefinite.map (Int.castRingHom ℝ)) (QuadForm.diag ε) ∧
        (Finset.univ.filter fun i => ε i = 1).card = 2) ∧
      (∀ a : Fin 2 → ℤ, 0 < noteFormDefinite.eval a →
        casselsDelta 2 0 * |gramDet noteFormDefinite| ^ ((1 : ℝ) / (2 : ℕ)) ≤ (noteFormDefinite.eval a : ℝ)) ∧
      (∃ a : Fin 2 → ℤ, (noteFormDefinite.eval a : ℝ) =
        casselsDelta 2 0 * |gramDet noteFormDefinite| ^ ((1 : ℝ) / (2 : ℕ))) ∧
      ∀ θ' : ℝ, θ' < casselsDelta 2 0 →
        ¬ ∃ a : Fin 2 → ℤ, 0 < noteFormDefinite.eval a ∧
          (noteFormDefinite.eval a : ℝ) ≤ θ' * |gramDet noteFormDefinite| ^ ((1 : ℝ) / (2 : ℕ)) := by
  have hd : noteFormDefinite.hessian.det = 12 := by
    rw [hessian_noteFormDefinite, Matrix.det_fin_two_of]; norm_num
  have hg : gramDet noteFormDefinite = 3 := by
    rw [gramDet, hd]; norm_num
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hD : |gramDet noteFormDefinite| ^ ((1 : ℝ) / (2 : ℕ)) = Real.sqrt 3 := by
    rw [hg, abs_of_pos (by norm_num), Real.sqrt_eq_rpow]; norm_num
  have hprod : casselsDelta 2 0 * Real.sqrt 3 = 2 := by
    rw [casselsDelta_two_zero]; field_simp
  have hev : ∀ a : Fin 2 → ℤ, noteFormDefinite.eval a = 2 * (a 0 ^ 2 + a 0 * a 1 + a 1 ^ 2) := fun a => by
    rw [noteFormDefinite, eval_binMk_int]; ring
  have hlow : ∀ a : Fin 2 → ℤ, 0 < noteFormDefinite.eval a →
      casselsDelta 2 0 * |gramDet noteFormDefinite| ^ ((1 : ℝ) / (2 : ℕ)) ≤ (noteFormDefinite.eval a : ℝ) := by
    intro a ha
    rw [hD, hprod]
    rw [hev] at ha ⊢
    have : (2 : ℤ) ≤ 2 * (a 0 ^ 2 + a 0 * a 1 + a 1 ^ 2) := by
      generalize a 0 ^ 2 + a 0 * a 1 + a 1 ^ 2 = p at ha ⊢
      omega
    exact_mod_cast this
  refine ⟨⟨!![2, 1; 1, 2], ?_, fun x => ?_⟩, by rw [hd]; norm_num, hg, casselsDelta_two_zero,
    ⟨![1, 1], fun i => by fin_cases i <;> simp, isometricGL_noteFormDefinite, ?_⟩, hlow,
    ⟨![1, 0], ?_⟩, fun θ' hθ => not_exists_small_of_lower (by rw [hD]; exact h3) hθ hlow⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [noteFormDefinite, eval_binMk_int]
    simp [gramForm, dotProduct, Fin.sum_univ_two, Matrix.mulVec]
    ring
  · have : (Finset.univ.filter fun i : Fin 2 => (![1, 1] : Fin 2 → ℝ) i = 1) = Finset.univ := by
      ext i; fin_cases i <;> simp
    rw [this]; rfl
  · rw [hD, hprod, hev]; simp

/-! ### Note 1: real coefficients (Blaney 1948) -/

/-- **Cassels, Lemma 3.2, Note 1** (Ch. 9, p. 136), a **named statement** (assumed, not proved here; Cassels
attributes it to Blaney, 1948): *Lemma 3.2 remains true if $f$ is supposed only to have real coefficients.* In the
conventions of the library's Lemma 3.2 (`exists_pos_value_le`): for every real symmetric matrix $A$ of size $n$ with
$\det A \ne 0$ (so $A$ is the matrix $(f_{ij})$ of a regular real form $f = \sum f_{ij}x_ix_j$ and $\det A = d(f)$),
every sign vector $\varepsilon \in \{\pm1\}^n$ with exactly $r \ge 1$ entries $+1$, $r + s = n$, such that $A$ is
real-equivalent to $\operatorname{diag}(\varepsilon)$ (`Ch9Sec3.Cong`: $(P\mathbf x)^{\mathsf T}A(P\mathbf x) =
\mathbf x^{\mathsf T}\operatorname{diag}(\varepsilon)\mathbf x$ for some invertible real $P$), there is an integral vector
$\mathbf a \in \mathbb Z^n$ with $0 < \mathbf a^{\mathsf T}A\mathbf a \le \theta(r, s)\lvert\det A\rvert^{1/n}$, where
$\theta(r, s)$ is `casselsDelta r s`. The single field is this universally quantified statement. -/
@[kb "cassels1978" "Ch. 9, Lemma 3.2, Note 1, p. 136"]
structure CasselsLemma32Real : Prop where
  /-- For every regular real symmetric matrix $A$ of signature $(r, s)$ with $r \ge 1$ there is an integral vector
  $\mathbf a$ with $0 < \mathbf a^{\mathsf T}A\mathbf a \le \theta(r, s)\lvert\det A\rvert^{1/n}$. -/
  exists_pos_value_le : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → A.det ≠ 0 →
    ∀ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) → Ch9Sec3.Cong A (Matrix.diagonal ε) →
    ∀ r s : ℕ, (Finset.univ.filter fun i => ε i = 1).card = r → r + s = n → 1 ≤ r →
    ∃ a : Fin n → ℤ, 0 < (fun i => (a i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (a i : ℝ)) ∧
      (fun i => (a i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (a i : ℝ)) ≤ casselsDelta r s * |A.det| ^ ((1 : ℝ) / n)

/-- **The integral Lemma 3.2 is the special case of the real one** (Ch. 9, p. 136, Note 1): the library's
`exists_pos_value_le` (for a regular classically integral form `f`, whose matrix is integral, hence real) follows from
the named statement `CasselsLemma32Real`. The hypotheses and conclusion are those of `exists_pos_value_le`. -/
theorem exists_pos_value_le_of_real (h : CasselsLemma32Real) {n : ℕ} (f : QuadForm ℤ n)
    (hf : IsClassicallyIntegral f) (hd : f.hessian.det ≠ 0)
    (ε : Fin n → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsig : IsometricGL (f.map (Int.castRingHom ℝ)) (QuadForm.diag ε))
    (r s : ℕ) (hr : (Finset.univ.filter fun i => ε i = 1).card = r) (hrs : r + s = n) (hr1 : 1 ≤ r) :
    ∃ a : Fin n → ℤ, 0 < f.eval a ∧ (f.eval a : ℝ) ≤ casselsDelta r s * |gramDet f| ^ ((1 : ℝ) / n) := by
  obtain ⟨A, hA, hAd, hev, hgram, hreal⟩ := Ch9Sec3.classical_data f hf hd
  have hC : Ch9Sec3.Cong (Ch9Sec3.cM A) (Matrix.diagonal ε) := by
    obtain ⟨g, hg⟩ := hsig
    refine ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, fun x => ?_⟩
    rw [← hreal, hg x, Ch9Sec3.dot_diagonal]
    simp [QuadForm.eval, QuadForm.evalIn_diag]
  have hdet : (Ch9Sec3.cM A).det ≠ 0 := by
    rw [Ch9Sec3.cM_det]; exact_mod_cast hAd
  obtain ⟨a, ha0, ha⟩ := h.exists_pos_value_le (Ch9Sec3.cM A) (Ch9Sec3.cM_isSymm hA) hdet ε hε hC r s hr hrs hr1
  rw [← Ch9Sec3.cast_dot] at ha0 ha
  rw [Ch9Sec3.cM_det] at ha
  refine ⟨a, by rw [hev]; exact_mod_cast ha0, ?_⟩
  rw [hev, hgram]
  exact ha

end QuadFormsKB.Siegel
