import QuadFormsKB.Historical.Gauss.ReductionNegative
import QuadFormsKB.Literature.ConwaySloane.BinaryTheorem1

/-!
# Reduced forms of positive nonsquare determinant (Disquisitiones Arithmeticae, Arts. 183, 223)

(Art. 223, representatives of classes for $D > 0$ nonsquare).

`art223_positive_nonsquare_reduced` proves `Art223PositiveNonsquareReduced` as a thin wrapper of Conway-Sloane's
cycle theory (Ch. 15, Theorem 1; `QuadFormsKB.ConwaySloane.Binary`): Conway-Sloane's `BinForm` $\langle a, b, c\rangle$
is Gauss's $(a, b, c) = a x^2 + 2bxy + c y^2$ with Conway-Sloane determinant $ac - b^2 = -D$ (Gauss's
determinant is $D = b^2 - ac$). The proof:

* `properEquiv_to_sLEquiv`: Conway-Sloane's `ProperEquiv` ($g = M f M^{\mathrm t}$ on Gram matrices, $\det M = 1$)
  gives the substitution matrix $\begin{pmatrix} p & q \\ r & s\end{pmatrix} = M^{\mathrm t}$, i.e. `SLEquiv` of the
  `gaussForm`s;
* `isReducedIndef_to_gauss`: Conway-Sloane's (12) implies Gauss's Art. 183 conditions (the extra condition
  $(|a| - b)^2 < D$ is derived from $|a||c| = D - b^2$ and $D < (b + |c|)^2$).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary
open QuadFormsKB.ConwaySloane.Binary (BinForm ProperEquiv IsReducedIndef cycleSet)

/-- Conway-Sloane's proper equivalence of `BinForm`s is Gauss's proper equivalence of `gaussForm`s. -/
theorem properEquiv_to_sLEquiv {a b c A B C : ℤ}
    (h : ProperEquiv (⟨a, b, c⟩ : BinForm) ⟨A, B, C⟩) :
    SLEquiv (gaussForm a b c) (gaussForm A B C) := by
  obtain ⟨M, hM, hG⟩ := h
  have h00 := congrFun (congrFun hG 0) 0
  have h01 := congrFun (congrFun hG 0) 1
  have h11 := congrFun (congrFun hG 1) 1
  simp [QuadFormsKB.ConwaySloane.Binary.BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  rw [Matrix.det_fin_two] at hM
  refine (sLEquiv_iff _ _).mpr ⟨M 0 0, M 1 0, M 0 1, M 1 1, by linarith, ?_⟩
  rw [subst_gaussForm]
  apply ext_abc <;> simp <;> nlinarith [h00, h01, h11]

/-- Conway-Sloane's condition (12) implies Gauss's reduced condition of Art. 183. -/
theorem isReducedIndef_to_gauss {A B C : ℤ} (h : IsReducedIndef A B C) : GaussReducedIndef A B C := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold GaussReducedIndef gaussDet
  refine ⟨h1, h2, by rw [add_comm]; exact h3, ?_⟩
  have hAC : A * C < 0 := by linarith
  have hu : |A| * |C| = B ^ 2 - A * C - B ^ 2 := by
    rw [← abs_mul, abs_of_neg hAC]; ring
  have hu0 : 0 < |A| := abs_pos.mpr (by rintro rfl; simp at hAC)
  have hv0 : 0 < |C| := abs_pos.mpr (by rintro rfl; simp at hAC)
  rcases le_or_gt B |A| with hB | hB
  · by_contra hc
    push Not at hc
    have h5 : |A| * |C| ≤ |A| * (|A| - 2 * B) := by nlinarith
    have h6 : |C| ≤ |A| - 2 * B := le_of_mul_le_mul_left h5 hu0
    have h7 : (2 * B + |C|) * |C| ≤ |A| * |C| := by nlinarith
    nlinarith
  · nlinarith [abs_nonneg A]

/-- **Gauss, *Disq. Arith.* Arts. 183, 223: every form $(a, b, c)$ of positive
nonsquare determinant $D = b^2 - ac$ is properly equivalent to a reduced form** $(A, B, C)$
(`GaussReducedIndef`). A wrapper of Conway-Sloane, Ch. 15, Theorem 1 (the cycle of reduced forms of an indefinite
form is nonempty, consists of properly equivalent forms satisfying (12): `ultimatelyPeriodic_indef`,
`properEquiv_of_mem_cycleSet`, `cycleSet_isReducedIndef`). Unconditional; no input structures. -/
@[kb "gauss1801" "Arts. 183, 223"]
theorem art223_positive_nonsquare_reduced : Art223PositiveNonsquareReduced := by
  intro a b c hD hsq
  set f : BinForm := ⟨a, b, c⟩ with hf
  have hdet : f.det = -gaussDet a b c := by
    simp only [hf, QuadFormsKB.ConwaySloane.Binary.BinForm.det, gaussDet]; ring
  have hd : f.det < 0 := by rw [hdet]; linarith
  have hs : ¬ IsSquare (-f.det) := by rw [hdet, neg_neg]; exact hsq
  obtain ⟨x, hx⟩ := QuadFormsKB.ConwaySloane.Binary.recurrentSet_nonempty
    (QuadFormsKB.ConwaySloane.Binary.ultimatelyPeriodic_indef hd hs)
  have hxc : x ∈ cycleSet f := hx
  have hpe := QuadFormsKB.ConwaySloane.Binary.properEquiv_of_mem_cycleSet hs hxc
  have hred := QuadFormsKB.ConwaySloane.Binary.cycleSet_isReducedIndef hd hs x hxc
  exact ⟨x.a, x.b, x.c, properEquiv_to_sLEquiv hpe, isReducedIndef_to_gauss hred⟩

end QuadFormsKB.Historical.Gauss
