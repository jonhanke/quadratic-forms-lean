/-
# Cassels, Chapter 4: the Corollary to Lemma 2.6, and Example 3

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 4, Corollary to Lemma 2.6 (p. 60) and
*Examples*, Ex. 3 (p. 66).

**Setting.** As in `Ch4/Invariants.lean`: forms over $\mathbb Q_p$ are diagonal, `QuadForm.diag a` with all
$a_i \ne 0$; equivalence over a field $K$ is `QuadForm.IsometricIn K`, representation `QuadForm.RepresentsIn K`.

**Proves.**
* Corollary to Lemma 2.6 (p. 60): a regular ternary form over $\mathbb Q_p$ represents all except possibly one of the
  classes of $\mathbb Q_p^{\times}$ modulo squares (`ternary_represents_all_but_one`).
* Ex. 3 (p. 66): for $\beta \in \mathbb Q_p^{\times}$ ($p \ne \infty$), $x_0^{2} + x_1^{2} + x_2^{2} + x_3^{2}$ and
  $\beta(x_0^{2} + x_1^{2} + x_2^{2} + x_3^{2})$ are equivalent over $\mathbb Q_p$ (`ex3_padic`); for $p = \infty$ they
  are equivalent over $\mathbb R$ if and only if $\beta > 0$ (`ex3_real`).

**Elsewhere:** Ex. 1, 2 and 4 (p. 66; the forms, illegible in the machine-read text, were read from the page image) are
proved in `Ch4/ExamplesScan.lean`.
-/
import QuadFormsKB.Literature.LocalGlobal.PadicClassification

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

open PadicClass QuadForm

variable (p : ℕ) [Fact p.Prime]

/-- **Cassels, Ch. 4, Corollary to Lemma 2.6 (p. 60).** A regular ternary form $f = \langle a_0, a_1, a_2\rangle$
over $\mathbb Q_p$ represents all except possibly one of the cosets of $\mathbb Q_p^{\times}$ modulo
$(\mathbb Q_p^{\times})^{2}$: if $x, y \in \mathbb Q_p^{\times}$ are both not represented, then $x \in y(\mathbb Q_p^{\times})^{2}$
(both lie in the class of $-d(f)$). -/
@[kb "cassels1978" "Ch. 4, Lemma 2.6, Cor., p. 60"]
theorem ternary_represents_all_but_one (a : Fin 3 → ℚ_[p]) (ha : ∀ i, a i ≠ 0) {x y : ℚ_[p]} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxr : ¬ (diag a).RepresentsIn ℚ_[p] x) (hyr : ¬ (diag a).RepresentsIn ℚ_[p] y) :
    ∃ t : ℚ_[p], t ≠ 0 ∧ x = t ^ 2 * y := by
  have hK := localHilbertField_padic p
  rw [eq_vec_three a] at hxr hyr
  rw [represents_three_iff hK (ha 0) (ha 1) (ha 2) hx] at hxr
  rw [represents_three_iff hK (ha 0) (ha 1) (ha 2) hy] at hyr
  push Not at hxr hyr
  obtain ⟨⟨t, ht, rfl⟩, -⟩ := hxr
  obtain ⟨⟨s, hs, rfl⟩, -⟩ := hyr
  exact ⟨t / s, div_ne_zero ht hs, by field_simp⟩

/-- The Hasse invariant of $\langle c, c, c, c\rangle$ is $(c, c)^{6} = 1$. -/
theorem hasseVec_const_four (c : ℚ_[p]) : hasseVec ![c, c, c, c] = 1 := by
  have h : hasseVec ![c, c, c, c] = hilbertSymbol ℚ_[p] c c ^ 6 := by
    simp [hasseVec, Fin.prod_univ_four]
    ring
  rw [h]
  rcases hs_pm c c with h1 | h1 <;> rw [h1] <;> norm_num

/-- **Cassels, Ch. 4, Ex. 3 (p. 66), $p \ne \infty$.** For $\beta \in \mathbb Q_p^{\times}$ the forms
$x_0^{2} + x_1^{2} + x_2^{2} + x_3^{2}$ and $\beta(x_0^{2} + x_1^{2} + x_2^{2} + x_3^{2})$ are equivalent over
$\mathbb Q_p$: they have the same determinant modulo squares ($\beta^{4}$) and the same Hasse invariant ($1$). -/
@[kb "cassels1978" "Ch. 4, Ex. 3, p. 66 (p ≠ ∞)"]
theorem ex3_padic {β : ℚ_[p]} (hβ : β ≠ 0) :
    (diag ![1, 1, 1, 1]).IsometricIn ℚ_[p] (diag ![β, β, β, β]) := by
  have hK := localHilbertField_padic p
  rw [isometric_iff_invariants hK (fun i => by fin_cases i <;> simp) (fun i => by fin_cases i <;> simpa)]
  refine ⟨⟨β ^ 2, pow_ne_zero 2 hβ, by simp [Fin.prod_univ_four]; ring⟩, ?_⟩
  rw [hasseVec_const_four, hasseVec_const_four]

/-- **Cassels, Ch. 4, Ex. 3 (p. 66), $p = \infty$ ("What happens for $p = \infty$?").** Over $\mathbb R$ the forms
$x_0^{2} + x_1^{2} + x_2^{2} + x_3^{2}$ and $\beta(x_0^{2} + x_1^{2} + x_2^{2} + x_3^{2})$ are equivalent if and only if
$\beta > 0$. -/
@[kb "cassels1978" "Ch. 4, Ex. 3, p. 66 (p = ∞)"]
theorem ex3_real {β : ℝ} (hβ : β ≠ 0) :
    (diag ![1, 1, 1, 1]).IsometricIn ℝ (diag ![β, β, β, β]) ↔ 0 < β := by
  constructor
  · intro h
    by_contra hneg
    have hlt : β < 0 := lt_of_le_of_ne (not_lt.mp hneg) hβ
    have hr : (diag ![β, β, β, β]).RepresentsIn ℝ 1 := by
      refine representsIn_of_isometricIn ℝ (isometricIn_symm ℝ h) ?_
      rw [representsIn_diag_iff]
      exact ⟨![1, 0, 0, 0], by simp [Fin.sum_univ_four]⟩
    rw [representsIn_diag_iff] at hr
    obtain ⟨z, hz⟩ := hr
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hz
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
  · intro hpos
    refine ⟨Real.sqrt β • 1, ?_, fun x => ?_⟩
    · simp [(Real.sqrt_pos.mpr hpos).ne']
    · rw [evalIn_diag_self, evalIn_diag_self]
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
      have h := Real.sq_sqrt hpos.le
      linear_combination (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * h

end QuadFormsKB.Cassels
