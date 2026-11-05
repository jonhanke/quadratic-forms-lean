/-
# Cassels, Chapter 9, §1: the introductory example $x^2 + 82y^2$ versus $2x^2 + 41y^2$

**Layer:** integer-valued binary forms `BinQF = QuadForm ℤ 2` (`BinQF.mk a b c` is $ax_0^2 + bx_0x_1 + cx_1^2$,
variables $x_0, x_1$ here, $x, y$ in Cassels), the genus `Siegel.SameGenus` (equivalence over every $\mathbb Z_p$ and
over $\mathbb R$), and integral equivalence `Siegel.IntEquiv`.

**Source (paraphrased).** Cassels, *Rational Quadratic Forms*, Ch. 9, §1, pp. 129–130: the positive definite forms
$x^2 + 82y^2$ and $2x^2 + 41y^2$ lie in the same genus but are not integrally equivalent; and the form
$f = 2x^2 + 41y^2$ with $a = 1$ shows that, in Theorem 1.3, one cannot in general take $f^{*} = f$.

**Proves**
* `sameGenus_not_intEquiv_82_pos`: the two forms are in the same genus and are not integrally equivalent.
  The genus statement is certified by a Kneser neighbour certificate (`Siegel.Kneser.NbCert`) for the prime $7$ and the
  isotropic vector $(4, 1)$ ($4^2 + 82 = 98 = 2 \cdot 7^2$; $7$ does not divide the determinant $328$ of the Hessian of
  $x^2 + 82y^2$), found with the generator in `Siegel/KneserGen.lean` and checked by the kernel with `decide`.
  The inequivalence: $x^2 + 82y^2$ represents $1$, $2x^2 + 41y^2$ does not.
* `theorem_one_three_not_self`: the hypotheses of Theorem 1.3 (`Siegel.exists_sameGenus_represents`) hold for
  $f = 2x^2 + 41y^2$ and $a = 1$ (in exactly the form of that theorem: represented over $\mathbb R$ and over every
  $\mathbb Z_p$), $f$ does not represent $1$ over $\mathbb Z$, but $f^{*} = x^2 + 82y^2$ is in the genus of $f$ and does.
  The local representations are obtained from the genus statement (the local equivalences carry the representation of
  $1$ by $f^{*}$ to one by $f$), so no Hensel lemma is needed.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Siegel.KneserCert

open Matrix

namespace QuadFormsKB.Cassels

open QuadFormsKB.Siegel

/-- Helper: the positive definite form $x_0^2 + 82x_1^2$. -/
def formPos82 : BinQF := BinQF.mk 1 0 82

/-- Helper: the positive definite form $2x_0^2 + 41x_1^2$. -/
def formPos82' : BinQF := BinQF.mk 2 0 41

/-- Helper: values of the two forms over any commutative ring. -/
theorem evalIn_formPos82 (K : Type*) [CommRing K] (x : Fin 2 → K) :
    formPos82.evalIn K x = x 0 ^ 2 + 82 * x 1 ^ 2 := by
  simp [formPos82, QuadForm.evalIn, Fin.sum_univ_two, BinQF.mk, QuadForm.ofUpper]
  ring

/-- Helper: value of $2x_0^2 + 41x_1^2$ over any commutative ring. -/
theorem evalIn_formPos82' (K : Type*) [CommRing K] (x : Fin 2 → K) :
    formPos82'.evalIn K x = 2 * x 0 ^ 2 + 41 * x 1 ^ 2 := by
  simp [formPos82', QuadForm.evalIn, Fin.sum_univ_two, BinQF.mk, QuadForm.ofUpper]
  ring

/-- Helper: integer values of $x_0^2 + 82x_1^2$. -/
theorem eval_formPos82 (x : Fin 2 → ℤ) : QuadForm.eval formPos82 x = x 0 ^ 2 + 82 * x 1 ^ 2 :=
  evalIn_formPos82 ℤ x

/-- Helper: integer values of $2x_0^2 + 41x_1^2$. -/
theorem eval_formPos82' (x : Fin 2 → ℤ) : QuadForm.eval formPos82' x = 2 * x 0 ^ 2 + 41 * x 1 ^ 2 :=
  evalIn_formPos82' ℤ x

/-- Helper: the neighbour certificate for $2x^2 + 41y^2$ as the $7$-neighbour of $x^2 + 82y^2$ at $\vec v = (4, 1)$. -/
def certPos82 : Kneser.NbCert 2 where
  v := ![4, 1]
  G := !![-4, -41; -1, 2]
  k := ![6, 2]
  w := ![1, 0]
  A := !![2, 41; 1, 24]
  cW := ![-2, -1]
  cV := ![-1, 0]
  K := !![-2, -41; -1, 4]

/-- Helper: the certificate is valid (checked by the kernel). -/
theorem certPos82_valid : certPos82.Valid formPos82 formPos82' 7 := by decide

/-- Helper: $7$ does not divide the determinant of the Hessian of $x^2 + 82y^2$ (it is $164 \cdot 2 = 328$). -/
theorem not_seven_dvd_det_pos82 : ¬ ((7 : ℕ) : ℤ) ∣ formPos82.hessian.det := by
  have : formPos82.hessian = !![2, 0; 0, 164] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [formPos82, QuadForm.hessian, BinQF.mk, QuadForm.ofUpper]
  rw [this, Matrix.det_fin_two_of]
  decide

/-- **Example** (Cassels, Ch. 9, §1, p. 129): the positive definite forms $x^2 + 82y^2$ and $2x^2 + 41y^2$ are in the
same genus (`Siegel.SameGenus`) but are not integrally equivalent (`Siegel.IntEquiv`). -/
@[kb "cassels1978" "Ch. 9, §1, p. 129 (x² + 82y² and 2x² + 41y²: same genus, not equivalent)"]
theorem sameGenus_not_intEquiv_82_pos :
    SameGenus formPos82 formPos82' ∧ ¬ IntEquiv formPos82 formPos82' := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨?_, ?_⟩
  · exact Kneser.NbCert.sameGenus (p := 7) (c := certPos82) (by norm_num) not_seven_dvd_det_pos82
      certPos82_valid
  · rintro ⟨g, hg⟩
    have h := hg ![1, 0]
    rw [eval_formPos82, eval_formPos82'] at h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    have h1 : g.val 1 0 = 0 := by
      by_contra hne
      have : 1 ≤ (g.val 1 0) ^ 2 := by nlinarith [sq_pos_of_ne_zero hne, Int.one_le_abs hne, sq_abs (g.val 1 0)]
      nlinarith [sq_nonneg (g.val 0 0)]
    rw [h1] at h
    have h2 : g.val 0 0 ^ 2 = 2 := by linarith
    have hle : |g.val 0 0| ≤ 1 := by
      by_contra hc
      push Not at hc
      nlinarith [sq_abs (g.val 0 0)]
    have hge : |g.val 0 0| ≥ 1 := by
      by_contra hc
      push Not at hc
      have : |g.val 0 0| = 0 := by have := abs_nonneg (g.val 0 0); omega
      rw [abs_eq_zero] at this
      rw [this] at h2
      norm_num at h2
    have : |g.val 0 0| = 1 := le_antisymm hle hge
    nlinarith [sq_abs (g.val 0 0)]

/-- **Cassels' remark after Theorem 1.3** (Ch. 9, §1, p. 130): for $f = 2x^2 + 41y^2$ and $a = 1$ the hypotheses of
Theorem 1.3 (`Siegel.exists_sameGenus_represents`) hold ($\det H \ne 0$; $a \ne 0$; $a$ is represented by $f$ over
$\mathbb R$ and over $\mathbb Z_p$ for every prime $p$), but $f$ does not represent $a$ over $\mathbb Z$, whereas
$f^{*} = x^2 + 82y^2$, which is in the genus of $f$, does. So $f^{*} = f$ cannot be demanded in the theorem. -/
@[kb "cassels1978" "Ch. 9, §1, p. 130 (f = 2x² + 41y², a = 1: f* ≠ f)"]
theorem theorem_one_three_not_self :
    formPos82'.hessian.det ≠ 0 ∧ (1 : ℤ) ≠ 0 ∧
      (∃ x : Fin 2 → ℝ, formPos82'.evalIn ℝ x = (1 : ℤ)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 2 → ℤ_[p],
        (formPos82'.map (Int.castRingHom ℤ_[p])).eval x = (1 : ℤ)) ∧
      (¬ ∃ x : Fin 2 → ℤ, QuadForm.eval formPos82' x = 1) ∧
      SameGenus formPos82' formPos82 ∧ ∃ x : Fin 2 → ℤ, QuadForm.eval formPos82 x = 1 := by
  have hSG : SameGenus formPos82' formPos82 := sameGenus_not_intEquiv_82_pos.1.symm
  have hrep : QuadForm.eval formPos82 ![1, 0] = 1 := by simp [eval_formPos82]
  refine ⟨?_, one_ne_zero, ?_, ?_, ?_, hSG, ⟨![1, 0], hrep⟩⟩
  · have : formPos82'.hessian = !![4, 0; 0, 82] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [formPos82', QuadForm.hessian, BinQF.mk, QuadForm.ofUpper]
    rw [this, Matrix.det_fin_two_of]
    norm_num
  · refine ⟨![Real.sqrt (1 / 2), 0], ?_⟩
    rw [evalIn_formPos82']
    simp
  · intro p _
    obtain ⟨g, hg⟩ := hSG.1 p
    refine ⟨g.val *ᵥ ![1, 0], ?_⟩
    rw [hg]
    have h : (formPos82.map (Int.castRingHom ℤ_[p])).eval ![1, 0] = 1 := by
      simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, QuadForm.map, formPos82, BinQF.mk,
        QuadForm.ofUpper]
    simpa using h
  · rintro ⟨x, hx⟩
    rw [eval_formPos82'] at hx
    have h0 : x 1 = 0 := by
      by_contra hne
      have : 1 ≤ (x 1) ^ 2 := by nlinarith [sq_pos_of_ne_zero hne, Int.one_le_abs hne, sq_abs (x 1)]
      nlinarith [sq_nonneg (x 0)]
    rw [h0] at hx
    have : (2 : ℤ) ∣ 1 := ⟨x 0 ^ 2, by linarith⟩
    omega
