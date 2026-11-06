/-
# Cassels, Chapter 9, Example 4 (p. 162): proper integral equivalence of five ternary forms

**Source.** Cassels, *Rational Quadratic Forms* (1978), Ch. 9, Example 4, p. 162 (read from the page image): decide which
pairs of
$$Q_1 = x^2 + y^2 - 10z^2,\; Q_2 = x^2 - y^2 + 10z^2,\; Q_3 = x^2 + 2y^2 - 5z^2,\; Q_4 = x^2 - 2y^2 + 5z^2,\;
Q_5 = -x^2 + 2y^2 + 5z^2$$
are properly integrally equivalent. (The machine-read text lost the last two forms; the page image shows them.)
Variables are $x_0, x_1, x_2 = x, y, z$ (0-based).

**Answer (proved, `ex4_complete`).** The proper classes are $\{Q_1, Q_2\}$ and $\{Q_3, Q_4, Q_5\}$. Equivalences within
a class are explicit integral matrices of determinant $+1$; forms in different classes are not even integrally
equivalent, since the numbers of zeros modulo $5$ differ ($45$ for $Q_1, Q_2$; $5$ for $Q_3, Q_4, Q_5$).
This builds on `Ch9Examples5.lean` (`ex4_properIntEquiv`, `card_zeros_eq_of_isometricGL`).
-/
import QuadFormsKB.Literature.Cassels.Ch9Examples5

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-- Helper: a properly integral equivalence from an integral matrix $M$ of determinant $1$ with
$Q'(\vec x) = Q(M\vec x)$ for all $\vec x$. -/
theorem properIntEquiv_of_det_one {n : ℕ} {Q Q' : QuadForm ℤ n} (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det = 1)
    (h : ∀ x, Q.eval (M *ᵥ x) = Q'.eval x) : ProperIntEquiv Q Q' :=
  ⟨Matrix.nonsingInvUnit M (by rw [hM]; exact isUnit_one), hM, h⟩

/-- Helper: the number of zeros modulo $5$ of the diagonal form $\langle d_0, d_1, d_2\rangle$. -/
def zerosMod5 (d : Fin 3 → ℤ) : ℕ :=
  (Finset.univ.filter fun x : Fin 3 → ZMod 5 =>
    ((QuadForm.diag d : QuadForm ℤ 3).map (Int.castRingHom (ZMod 5))).eval x = 0).card

/-- Helper: integrally equivalent ternary diagonal forms have the same number of zeros modulo $5$. -/
theorem zerosMod5_eq_of_intEquiv {d d' : Fin 3 → ℤ}
    (h : IntEquiv (QuadForm.diag d : QuadForm ℤ 3) (QuadForm.diag d')) : zerosMod5 d = zerosMod5 d' :=
  (card_zeros_eq_of_isometricGL (h.sameGenus.isometricGL_zmod (c := 5) (by norm_num))).symm

/-- Helper: forms with different numbers of zeros modulo $5$ are not integrally equivalent. -/
theorem not_intEquiv_of_zerosMod5 {d d' : Fin 3 → ℤ} (h : zerosMod5 d ≠ zerosMod5 d') :
    ¬ IntEquiv (QuadForm.diag d : QuadForm ℤ 3) (QuadForm.diag d') := fun e => h (zerosMod5_eq_of_intEquiv e)

/-- Helper: $Q_1$ has $45$ zeros modulo $5$. -/
theorem zerosMod5_ex4_1 : zerosMod5 ![1, 1, -10] = 45 := by
  unfold zerosMod5; simp only [eval_map_diag_three]; decide

/-- Helper: $Q_2$ has $45$ zeros modulo $5$. -/
theorem zerosMod5_ex4_2 : zerosMod5 ![1, -1, 10] = 45 := by
  unfold zerosMod5; simp only [eval_map_diag_three]; decide

/-- Helper: $Q_3$ has $5$ zeros modulo $5$. -/
theorem zerosMod5_ex4_3 : zerosMod5 ![1, 2, -5] = 5 := by
  unfold zerosMod5; simp only [eval_map_diag_three]; decide

/-- Helper: $Q_4$ has $5$ zeros modulo $5$. -/
theorem zerosMod5_ex4_4 : zerosMod5 ![1, -2, 5] = 5 := by
  unfold zerosMod5; simp only [eval_map_diag_three]; decide

/-- Helper: $Q_5$ has $5$ zeros modulo $5$. -/
theorem zerosMod5_ex4_5 : zerosMod5 ![-1, 2, 5] = 5 := by
  unfold zerosMod5; simp only [eval_map_diag_three]; decide

/-- Helper: $Q_3 = x^2 + 2y^2 - 5z^2$ and $Q_4 = x^2 - 2y^2 + 5z^2$ are properly equivalent. -/
theorem ex4_properIntEquiv_34 :
    ProperIntEquiv (QuadForm.diag ![1, 2, -5] : QuadForm ℤ 3) (QuadForm.diag ![1, -2, 5]) := by
  refine properIntEquiv_of_det_one !![-3, -4, 0; -6, -9, -5; -4, -6, -3] (by decide) fun x => ?_
  rw [eval_diag_three, eval_diag_three]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Helper: $Q_3$ and $Q_5 = -x^2 + 2y^2 + 5z^2$ are properly equivalent. -/
theorem ex4_properIntEquiv_35 :
    ProperIntEquiv (QuadForm.diag ![1, 2, -5] : QuadForm ℤ 3) (QuadForm.diag ![-1, 2, 5]) := by
  refine properIntEquiv_of_det_one !![-6, -8, -5; -2, -3, 0; -3, -4, -2] (by decide) fun x => ?_
  rw [eval_diag_three, eval_diag_three]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- **Cassels, Ch. 9, Example 4** (p. 162), complete answer. With $Q_1 = x^2 + y^2 - 10z^2$, $Q_2 = x^2 - y^2 + 10z^2$,
$Q_3 = x^2 + 2y^2 - 5z^2$, $Q_4 = x^2 - 2y^2 + 5z^2$, $Q_5 = -x^2 + 2y^2 + 5z^2$ (`QuadForm.diag` of
`![1, 1, -10]`, `![1, -1, 10]`, `![1, 2, -5]`, `![1, -2, 5]`, `![-1, 2, 5]`): of the ten pairs, exactly
$(1,2), (3,4), (3,5), (4,5)$ are properly integrally equivalent (`ProperIntEquiv`); the six pairs
$(1,3), (1,4), (1,5), (2,3), (2,4), (2,5)$ are not even integrally equivalent (`IntEquiv`). The conjuncts are in the
order $(1,2), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)$. -/
@[kb "cassels1978" "Ch. 9, Ex. 4, p. 162 (complete answer; the forms read from the page image)"]
theorem ex4_complete :
    ProperIntEquiv (QuadForm.diag ![1, 1, -10] : QuadForm ℤ 3) (QuadForm.diag ![1, -1, 10]) ∧
    ¬ IntEquiv (QuadForm.diag ![1, 1, -10] : QuadForm ℤ 3) (QuadForm.diag ![1, 2, -5]) ∧
    ¬ IntEquiv (QuadForm.diag ![1, 1, -10] : QuadForm ℤ 3) (QuadForm.diag ![1, -2, 5]) ∧
    ¬ IntEquiv (QuadForm.diag ![1, 1, -10] : QuadForm ℤ 3) (QuadForm.diag ![-1, 2, 5]) ∧
    ¬ IntEquiv (QuadForm.diag ![1, -1, 10] : QuadForm ℤ 3) (QuadForm.diag ![1, 2, -5]) ∧
    ¬ IntEquiv (QuadForm.diag ![1, -1, 10] : QuadForm ℤ 3) (QuadForm.diag ![1, -2, 5]) ∧
    ¬ IntEquiv (QuadForm.diag ![1, -1, 10] : QuadForm ℤ 3) (QuadForm.diag ![-1, 2, 5]) ∧
    ProperIntEquiv (QuadForm.diag ![1, 2, -5] : QuadForm ℤ 3) (QuadForm.diag ![1, -2, 5]) ∧
    ProperIntEquiv (QuadForm.diag ![1, 2, -5] : QuadForm ℤ 3) (QuadForm.diag ![-1, 2, 5]) ∧
    ProperIntEquiv (QuadForm.diag ![1, -2, 5] : QuadForm ℤ 3) (QuadForm.diag ![-1, 2, 5]) := by
  refine ⟨ex4_properIntEquiv, ?_, ?_, ?_, ?_, ?_, ?_, ex4_properIntEquiv_34, ex4_properIntEquiv_35,
    ex4_properIntEquiv_34.symm.trans ex4_properIntEquiv_35⟩ <;>
  refine not_intEquiv_of_zerosMod5 ?_ <;>
  simp [zerosMod5_ex4_1, zerosMod5_ex4_2, zerosMod5_ex4_3, zerosMod5_ex4_4, zerosMod5_ex4_5]

end QuadFormsKB.Siegel
