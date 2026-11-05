import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Reduction
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Irrational

/-!
# Saha–Hanke, Corollary 6.1: irrational three-term relations

Source: R. Saha and J. Hanke, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §6.1,
Corollary 6.1, p. 16.

If $\alpha_1 \theta_{Q_1} + \alpha_2 \theta_{Q_2} + \alpha_3 \theta_{Q_3} = 0$ with some ratio
$\alpha_i / \alpha_j$ ($\alpha_j \ne 0$) irrational, then $Q_1 \sim_{\mathbb{Z}} Q_2 \sim_{\mathbb{Z}}
Q_3$. Proof as in the source: Lemma 5.1 gives $\theta_{Q_1} = \theta_{Q_2} = \theta_{Q_3}$, and equal
theta series force equivalence (§6.1; proved here directly, `reduced_eq_of_theta_eq`).
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- **Two positive definite integral binary forms with the same theta series are
$\mathrm{GL}_2(\mathbb{Z})$-equivalent** (§6.1, for arbitrary, not necessarily reduced, forms). -/
@[kb "hanke2023threeterm" "§6.1, p. 16"]
theorem intEquiv_of_theta_eq {Q Q' : BinQF} (hQ : IntQF.PosDef Q) (hQ' : IntQF.PosDef Q')
    (h : ∀ m : ℕ, repNum Q m = repNum Q' m) : IntEquiv Q Q' := by
  obtain ⟨R, hR, hQR⟩ := exists_reduced_equiv hQ
  obtain ⟨R', hR', hQR'⟩ := exists_reduced_equiv hQ'
  have : R = R' := reduced_eq_of_theta_eq hR hR' fun m => by
    rw [← repNum_eq_of_intEquiv hQR, ← repNum_eq_of_intEquiv hQR', h]
  subst this
  exact hQR.trans hQR'.symm

/-- **Corollary 6.1.** Let $Q_1, Q_2, Q_3$ be positive definite integral binary forms with
$\alpha_1 \theta_{Q_1} + \alpha_2 \theta_{Q_2} + \alpha_3 \theta_{Q_3} = 0$ (coefficientwise),
where some ratio $\alpha_i / \alpha_j$ with $\alpha_j \ne 0$ is irrational. Then
$Q_1 \sim_{\mathbb{Z}} Q_2 \sim_{\mathbb{Z}} Q_3$. -/
@[kb "hanke2023threeterm" "§6.1, Corollary 6.1, p. 16"]
theorem corollary_6_1 {Q₁ Q₂ Q₃ : BinQF} (h₁ : IntQF.PosDef Q₁) (h₂ : IntQF.PosDef Q₂)
    (h₃ : IntQF.PosDef Q₃) {α₁ α₂ α₃ : ℝ} (h : ThetaRelation3 Q₁ Q₂ Q₃ α₁ α₂ α₃)
    (hirr : HasIrrationalRatio α₁ α₂ α₃) : IntEquiv Q₁ Q₂ ∧ IntEquiv Q₂ Q₃ := by
  obtain ⟨e12, e23⟩ := irrational_three_term h₁ h₂ h₃ h hirr
  exact ⟨intEquiv_of_theta_eq h₁ h₂ e12, intEquiv_of_theta_eq h₂ h₃ e23⟩

end QuadFormsKB.Hanke2023ThreeTerm
