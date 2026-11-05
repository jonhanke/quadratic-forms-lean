import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Classification

/-!
# Saha–Hanke: every positive definite integral binary form has a reduced representative

Source: R. Saha and J. Hanke, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §2, Lemma 2.3
(existence part, for integral forms), and its uniqueness part via theta series.

Existence comes from Lagrange–Gauss reduction (`QuadFormsKB.Siegel.exists_reduced`, Cassels):
$Q \sim_{\mathrm{SL}_2(\mathbb{Z})} g$ with $|b| \le a \le c$; if $b < 0$ the substitution
$(x, y) \mapsto (x, -y)$ of determinant $-1$ makes $b \ge 0$. Uniqueness: two
$\mathrm{GL}_2(\mathbb{Z})$-equivalent reduced forms have the same representation numbers, hence
are equal (`reduced_eq_of_theta_eq`).
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel Matrix

/-- $Q(\vec x) = a x_0^2 + b x_0 x_1 + c x_1^2$ for $\vec x \in \mathbb{Z}^2$. -/
lemma qeval_eq (f : BinQF) (x : Fin 2 → ℤ) :
    QuadForm.eval f x = f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2 := by
  have := BinQF.eval_eq f (x 0) (x 1)
  have hx2 : (![x 0, x 1] : Fin 2 → ℤ) = x := by funext i; fin_cases i <;> rfl
  rw [BinQF.eval, hx2] at this; exact this

/-- The substitution $(x, y) \mapsto (x, -y)$ as an element of $\mathrm{GL}_2(\mathbb{Z})$. -/
def flipY : GL (Fin 2) ℤ :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

lemma flipY_mulVec (x : Fin 2 → ℤ) : (flipY.val *ᵥ x) 0 = x 0 ∧ (flipY.val *ᵥ x) 1 = -x 1 := by
  simp [flipY, mulVec, dotProduct, Fin.sum_univ_two]

/-- $a x^2 + b xy + c y^2 \sim_{\mathbb{Z}} a x^2 - b xy + c y^2$. -/
lemma intEquiv_flip (g : BinQF) : IntEquiv g (BinQF.mk g.a (-g.b) g.c) := by
  refine ⟨flipY, fun x => ?_⟩
  rw [qeval_eq, qeval_eq, (flipY_mulVec x).1, (flipY_mulVec x).2]
  simp

/-- `IntQF.PosDef` for a binary form gives the classical positivity `BinQF.PosDef`. -/
lemma binPosDef_of_posDef {Q : BinQF} (hQ : IntQF.PosDef Q) : Q.PosDef := by
  intro x y hxy
  apply hQ ![x, y]
  intro h
  apply hxy
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  rw [h0, h1]

/-- **Lemma 2.3, existence (integral forms).** Every positive definite integral binary form is
$\mathrm{GL}_2(\mathbb{Z})$-equivalent to a reduced form ($0 \le b \le a \le c$, $a > 0$). -/
@[kb "hanke2023threeterm" "§2, Lemma 2.3, p. 3"]
theorem exists_reduced_equiv {Q : BinQF} (hQ : IntQF.PosDef Q) : ∃ R, IsReduced R ∧ IntEquiv Q R := by
  have hPD' : Q.PosDef' := (BinQF.posDef_iff_posDef' Q).1 (binPosDef_of_posDef hQ)
  obtain ⟨g, ⟨γ, -, hγ⟩, hb, hac, hdisc⟩ := Siegel.exists_reduced _ Q rfl hPD'
  have hQg : IntEquiv Q g := ⟨γ, hγ⟩
  have hd : g.disc < 0 := hdisc ▸ hPD'.2
  have ha : 0 < g.a := by
    rcases (abs_nonneg g.b).trans hb |>.lt_or_eq with h | h
    · exact h
    · exfalso
      have : g.b = 0 := by rw [← h] at hb; exact abs_nonpos_iff.1 hb
      simp only [BinQF.disc, this, ← h] at hd; simp at hd
  rcases le_or_gt 0 g.b with h0 | h0
  · exact ⟨g, ⟨h0, (le_abs_self _).trans hb, hac, ha⟩, hQg⟩
  · refine ⟨BinQF.mk g.a (-g.b) g.c, ?_, hQg.trans (intEquiv_flip g)⟩
    simp only [IsReduced, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
    exact ⟨by omega, by rw [abs_of_neg h0] at hb; exact hb, hac, ha⟩

/-- **Lemma 2.3, uniqueness (integral forms).** Two $\mathrm{GL}_2(\mathbb{Z})$-equivalent reduced
integral binary forms are equal. -/
@[kb "hanke2023threeterm" "§2, Lemma 2.3, p. 3"]
theorem reduced_unique {R R' : BinQF} (hR : IsReduced R) (hR' : IsReduced R')
    (h : IntEquiv R R') : R = R' :=
  reduced_eq_of_theta_eq hR hR' fun m => repNum_eq_of_intEquiv h m

end QuadFormsKB.Hanke2023ThreeTerm
