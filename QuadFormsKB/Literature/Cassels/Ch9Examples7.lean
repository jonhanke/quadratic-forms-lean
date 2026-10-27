/-
# Cassels, Chapter 9, Example 3 (i): the forms are in one genus

**Layer:** binary integer-valued forms `QuadForm ℤ 2` (`ex3g`, `ex3h` from `Ch9Examples.lean`), the genus
`Siegel.SameGenus`, Lemma 4.3 (`sameGenus_of_congr`, `Ch9Sec4Congr.lean`).

**Proves** the first half of Example 3 (i) (p. 162): $g = 3x^2 + 2xy + 23y^2$ and $h = 7x^2 + 6xy + 11y^2$ are in the same
genus (`ex3_sameGenus`). (The second half, that they are not equivalent, is `ex3_not_intEquiv`.)

*Proof (Cassels' Lemma 4.3, as in his remark after Lemma 4.2).* Both have determinant $d = 68$. The form
$h' = h(T\mathbf x)$ with $T = \begin{pmatrix} -10 & 797 \\ 7 & -558\end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$ is
$h' = 819x^2 - 130558xy + 5203111y^2$, whose Cassels entries $819, -65279, 5203111$ are congruent to those of $g$
($3, 1, 23$) modulo $4d = 272$; both are positive definite, hence real-equivalent; so $g$ and $h'$ are in one genus by
Lemma 4.3, and $h' \cong h$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec4Congr
import QuadFormsKB.Literature.Cassels.Ch9Examples
import QuadFormsKB.Binary.GenusLocal

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-- $h' = 819x^2 - 130558xy + 5203111y^2 = h(T\mathbf x)$ (Example 3, proof of `ex3_sameGenus`). -/
def ex3h' : QuadForm ℤ 2 := QuadForm.ofUpper ![![819, -130558], ![0, 5203111]]

/-- Evaluation of $h'$. -/
theorem eval_ex3h' (x : Fin 2 → ℤ) :
    ex3h'.eval x = 819 * x 0 ^ 2 - 130558 * x 0 * x 1 + 5203111 * x 1 ^ 2 := by
  simp [ex3h', QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]; ring

/-- Evaluation of $g$. -/
theorem eval_ex3g (x : Fin 2 → ℤ) : ex3g.eval x = 3 * x 0 ^ 2 + 2 * x 0 * x 1 + 23 * x 1 ^ 2 := by
  simp [ex3g, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]; ring

/-- $h'$ is properly equivalent to $h$: $h(T\mathbf x) = h'(\mathbf x)$. -/
theorem ex3h_properIntEquiv : ProperIntEquiv ex3h ex3h' := by
  let T : GL (Fin 2) ℤ := ⟨!![-10, 797; 7, -558], !![-558, -797; -7, -10], by decide, by decide⟩
  refine ⟨T, by decide, fun x => ?_⟩
  rw [eval_ex3h, eval_ex3h']
  simp [T, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The Hessian of $g$. -/
theorem hessian_ex3g : ex3g.hessian = !![6, 2; 2, 46] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The Hessian of $h'$. -/
theorem hessian_ex3h' : ex3h'.hessian = !![1638, -130558; -130558, 10406222] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **Cassels, Ch. 9, Example 3 (i)** (p. 162), first half: *the forms $g = 3x^2 + 2xy + 23y^2$ and
$h = 7x^2 + 6xy + 11y^2$ are in the same genus.* -/
@[kb "cassels1978" "Ch. 9, Ex. 3 (i), p. 162 (the forms are in the same genus)"]
theorem ex3_sameGenus : SameGenus ex3g ex3h := by
  have hci : ∀ Q : QuadForm ℤ 2, (∀ i j, (2 : ℤ) ∣ Q.hessian i j) → IsClassicallyIntegral Q :=
    fun Q h => ci_of_two_dvd_hessian h
  have h1 : SameGenus ex3g ex3h' := by
    refine sameGenus_of_congr ex3g ex3h' (hci _ ?_) (hci _ ?_) ?_ ?_ ?_ ?_
    · intro i j; rw [hessian_ex3g]; fin_cases i <;> fin_cases j <;> decide
    · intro i j; rw [hessian_ex3h']; fin_cases i <;> fin_cases j <;> decide
    · rw [hessian_ex3g, hessian_ex3h', det_fin_two_of, det_fin_two_of]; norm_num
    · rw [hessian_ex3g, det_fin_two_of]; norm_num
    · refine Binary.isometricGL_real ?_ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      decide
    · intro i j
      rw [hessian_ex3g, hessian_ex3h', det_fin_two_of]
      fin_cases i <;> fin_cases j <;> decide
  exact h1.trans (ex3h_properIntEquiv.intEquiv.sameGenus.symm)

end QuadFormsKB.Siegel
