import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.MainTheorem
import QuadFormsKB.Literature.Hanke2023ThreeTerm.RefinementCount
import QuadFormsKB.Literature.Hanke2023ThreeTerm.RefinementAB11
import QuadFormsKB.Literature.Hanke2023ThreeTerm.RefinementAB12

/-!
# Saha–Hanke §6.2–6.3 proved, and Theorem 1.1 unconditionally

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite binary quadratic
forms*, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §5.3, §6.2, §6.3 and Theorem 1.1.

* `ab11_holds` (§6.2, $a + b = 2$): reduced solutions of $\frac12\theta_{Q_1} + \frac12\theta_{Q_2} = \theta_{Q_3}$ are
  diagonal, $Q_1 = Q_2 = Q_3$.
* `ab12_holds` (§6.3, $a + b = 3$): reduced solutions of $\frac13\theta_{Q_1} + \frac23\theta_{Q_2} = \theta_{Q_3}$ are
  diagonal or $(c(x^2+xy+y^2), 4c(x^2+xy+y^2), c(x^2+3y^2))$, $c > 0$.
* `refinementResults`: the former named input `RefinementResults`, proved.
* `theorem_1_1`: **Theorem 1.1, unconditional.**

*Route (replacing the source's computer search).* By Lemma 3.3 the relation holds for strongly primitive counts,
hence for the cumulative counts $N_i(t)$ (`spCountZ_rel`). For a reduced form, $N(t)$ is bounded below by the number
`cntV` of the twelve vectors of $V$ with value $\le t$, with equality for $t < \min(16a - 4b + c, 6c)$
(`RefinementCount.lean`). The arithmetic statements `core_ab11`, `core_ab12` (generated case trees over the nine
coefficients, each leaf checked by `omega`) finish the proof. This plays the role of the source's Extended
Refinement Algorithm (§5.3): its refined cones are the branches of the tree, its K-sets the values of $V$.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel Refinement

/-- The integer form of a normalized relation: from $\frac{a}{a+b}\theta_1 + \frac{b}{a+b}\theta_2 = \theta_3$
(reduced forms), $a N_1(t) + b N_2(t) = (a + b) N_3(t)$. -/
lemma spCountZ_rel_of_theta {Q₁ Q₂ Q₃ : BinQF} (h₁ : IsReduced Q₁) (h₂ : IsReduced Q₂) (h₃ : IsReduced Q₃)
    {a b : ℕ} (hab : 0 < a + b)
    (h : ThetaRelation3 Q₁ Q₂ Q₃ ((a : ℝ) / (a + b)) ((b : ℝ) / (a + b)) (-1)) (t : ℤ) :
    (a : ℤ) * spCountZ Q₁ t + b * spCountZ Q₂ t = (a + b : ℤ) * spCountZ Q₃ t := by
  have hpos : (0 : ℝ) < a + b := by exact_mod_cast hab
  have hsum : (a : ℝ) / (a + b) + (b : ℝ) / (a + b) + (-1) = 0 := by
    field_simp; ring
  have hs := (lemma_3_3 h₁.posDef h₂.posDef h₃.posDef hsum).1 h
  refine spCountZ_rel (fun m => ?_) t
  have e := hs m
  have : (a : ℝ) * spRepNum Q₁ m + b * spRepNum Q₂ m = (a + b) * spRepNum Q₃ m := by
    field_simp at e; linarith
  exact_mod_cast this

/-- **§6.2 ($a + b = 2$): only diagonal solutions.** Reduced integral binary forms with
$\frac12\theta_{Q_1} + \frac12\theta_{Q_2} = \theta_{Q_3}$ (coefficientwise) are equal. Proved by a case tree
checked by Lean (`core_ab11`), replacing the source's computer run. -/
@[kb "hanke2023threeterm" "§6.2, p. 16"]
theorem ab11_holds {Q₁ Q₂ Q₃ : BinQF} (h₁ : IsReduced Q₁) (h₂ : IsReduced Q₂) (h₃ : IsReduced Q₃)
    (h : ThetaRelation3 Q₁ Q₂ Q₃ (1 / 2) (1 / 2) (-1)) : Q₁ = Q₂ ∧ Q₂ = Q₃ := by
  have hr := spCountZ_rel_of_theta (a := 1) (b := 1) h₁ h₂ h₃ (by norm_num)
    (by convert h using 2 <;> norm_num)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := core_ab11 (N1 := spCountZ Q₁) (N2 := spCountZ Q₂) (N3 := spCountZ Q₃)
    h₁ h₂ h₃ (cntV_le_spCountZ h₁) (cntV_le_spCountZ h₂) (cntV_le_spCountZ h₃)
    (spCountZ_eq_cntV h₁) (spCountZ_eq_cntV h₂) (spCountZ_eq_cntV h₃)
    (fun t _ => by have := hr t; push_cast at this; linarith)
  exact ⟨BinQF.ext_abc e1 e2 e3, BinQF.ext_abc e4 e5 e6⟩

/-- **§6.3 ($a + b = 3$): diagonal solutions and one ray.** Reduced integral binary forms with
$\frac13\theta_{Q_1} + \frac23\theta_{Q_2} = \theta_{Q_3}$ (coefficientwise) are equal, or are
$(c(x^2+xy+y^2), 4c(x^2+xy+y^2), c(x^2+3y^2))$ for an integer $c > 0$. Proved by a case tree checked by Lean
(`core_ab12`), replacing the source's computer run. -/
@[kb "hanke2023threeterm" "§6.3, p. 17"]
theorem ab12_holds {Q₁ Q₂ Q₃ : BinQF} (h₁ : IsReduced Q₁) (h₂ : IsReduced Q₂) (h₃ : IsReduced Q₃)
    (h : ThetaRelation3 Q₁ Q₂ Q₃ (1 / 3) (2 / 3) (-1)) :
    (Q₁ = Q₂ ∧ Q₂ = Q₃) ∨ ∃ c : ℤ, 0 < c ∧ Q₁ = formE c ∧ Q₂ = formE (4 * c) ∧ Q₃ = formF c := by
  have hr := spCountZ_rel_of_theta (a := 1) (b := 2) h₁ h₂ h₃ (by norm_num)
    (by convert h using 2 <;> norm_num)
  rcases core_ab12 (N1 := spCountZ Q₁) (N2 := spCountZ Q₂) (N3 := spCountZ Q₃)
    h₁ h₂ h₃ (cntV_le_spCountZ h₁) (cntV_le_spCountZ h₂) (cntV_le_spCountZ h₃)
    (spCountZ_eq_cntV h₁) (spCountZ_eq_cntV h₂) (spCountZ_eq_cntV h₃)
    (fun t _ => by have := hr t; push_cast at this; linarith) with
    ⟨e1, e2, e3, e4, e5, e6⟩ | ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
  · exact Or.inl ⟨BinQF.ext_abc e1 e2 e3, BinQF.ext_abc e4 e5 e6⟩
  · refine Or.inr ⟨Q₃.a, h₃.2.2.2, ?_, ?_, ?_⟩
    · exact BinQF.ext_abc (by simp [formE, e1]) (by simp [formE, e2]) (by simp [formE, e3])
    · exact BinQF.ext_abc (by simp [formE, e4]) (by simp [formE, e5]) (by simp [formE, e6])
    · exact BinQF.ext_abc (by simp [formF]) (by simp [formF, e7]) (by simp [formF, e8])

/-- **The results of §6.2 and §6.3** (`RefinementResults`), proved. -/
theorem refinementResults : RefinementResults := ⟨ab11_holds, ab12_holds⟩

/-- **Theorem 1.1 (three-term linear relations among binary theta series), unconditional.** Let
$Q_1, Q_2, Q_3$ (`Q 0`, `Q 1`, `Q 2`) be positive definite integral binary quadratic forms and
$\alpha_1, \alpha_2, \alpha_3 \in \mathbb{R}$ with $\alpha_1 \theta_{Q_1} + \alpha_2 \theta_{Q_2} +
\alpha_3 \theta_{Q_3} = 0$ (coefficientwise). Then, after reordering the indices by some permutation $\sigma$, one of
the four cases holds: degenerate, trivial 2-term, trivial 3-term, or the non-trivial relation
$\frac13 \theta_{Q_1} + \frac23 \theta_{Q_2} = \theta_{Q_3}$ with $Q_1 \sim c(x^2+xy+y^2)$,
$Q_2 \sim 4c(x^2+xy+y^2)$, $Q_3 \sim c(x^2+3y^2)$ (`SolutionType`). That at most one case holds is
`solutionType_exclusive`; the converse is `theorem_1_1_converse`. -/
@[kb "hanke2023threeterm" "§1, Theorem 1.1, p. 2"]
theorem theorem_1_1 (Q : Fin 3 → BinQF) (hQ : ∀ i, IntQF.PosDef (Q i))
    (α : Fin 3 → ℝ) (h : ThetaRelation3 (Q 0) (Q 1) (Q 2) (α 0) (α 1) (α 2)) :
    ∃ σ : Equiv.Perm (Fin 3), SolutionType (Q ∘ σ) (α ∘ σ) :=
  theorem_1_1_of_refinement refinementResults Q hQ α h

end QuadFormsKB.Hanke2023ThreeTerm
