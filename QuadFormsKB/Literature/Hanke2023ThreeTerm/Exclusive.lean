import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.MainTheorem

/-!
# Saha–Hanke, Theorem 1.1: the four cases are solutions, and they are mutually exclusive

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), Theorem 1.1, p. 2.

* `theorem_1_1_converse`: every `SolutionType` (up to reordering) is a theta relation.
* `solutionType_exclusive`: the "exactly one" part of Theorem 1.1: no two different cases can hold
  (each possibly after its own reordering of the indices).

Indices are 0-based: $Q_1, Q_2, Q_3$ of the paper are `Q 0`, `Q 1`, `Q 2`.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- Case 4 (non-trivial) gives a theta relation: with $\alpha_1 = 2\alpha_0$, $\alpha_2 = -3\alpha_0$
(0-based), the identity $r_{E}(m) + 2 r_{4E}(m) = 3 r_{F}(m)$ of `relation_scaled`. -/
lemma isNonTrivial_rel {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (h : IsNonTrivial Q α) :
    Rel Q α := by
  obtain ⟨h1, h2, -, c, hc, e0, e1, e2⟩ := h
  intro m
  have key := relation_scaled hc (m : ℤ)
  rw [← repNum_eq_of_intEquiv e0, ← repNum_eq_of_intEquiv e1,
    ← repNum_eq_of_intEquiv e2] at key
  have key' : (repNum (Q 0) m : ℝ) + 2 * repNum (Q 1) m = 3 * repNum (Q 2) m := by
    exact_mod_cast key
  have a1 : α 1 = 2 * α 0 := by linarith
  have a2 : α 2 = -3 * α 0 := by linarith
  simp only [Fin.sum_univ_three]
  rw [a1, a2]
  linear_combination α 0 * key'

/-- The conditions of case 2 give a theta relation. -/
lemma isTrivialTwoTerm_rel {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (h : IsTrivialTwoTerm Q α) :
    Rel Q α := by
  obtain ⟨h1, -, h2, e⟩ := h
  intro m
  have := repNum_eq_of_intEquiv e (m : ℤ)
  simp only [Fin.sum_univ_three]
  rw [h2, h1, this]; ring

/-- The conditions of case 3 give a theta relation. -/
lemma isTrivialThreeTerm_rel {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (h : IsTrivialThreeTerm Q α) :
    Rel Q α := by
  obtain ⟨-, hs, e01, e12⟩ := h
  intro m
  have a := repNum_eq_of_intEquiv e01 (m : ℤ)
  have b := repNum_eq_of_intEquiv e12 (m : ℤ)
  simp only [Fin.sum_univ_three]
  rw [a, b]
  linear_combination (repNum (Q 2) m : ℝ) * hs

/-- Every case of `SolutionType` is a theta relation. -/
lemma solutionType_rel {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (h : SolutionType Q α) : Rel Q α := by
  rcases h with h | h | h | h
  · intro m; simp [Fin.sum_univ_three, h 0, h 1, h 2]
  · exact isTrivialTwoTerm_rel h
  · exact isTrivialThreeTerm_rel h
  · exact isNonTrivial_rel h

/-- **Solutions of the three-term relations are valid.** Each of the four cases of
`SolutionType` satisfies the theta relation $\alpha_0 \theta_{Q_0} + \alpha_1 \theta_{Q_1} +
\alpha_2 \theta_{Q_2} = 0$ (coefficientwise, `ThetaRelation3`). No positive definiteness is
needed. -/
theorem solutionType_is_solution (Q : Fin 3 → BinQF) (_hQ : ∀ i, IntQF.PosDef (Q i))
    (α : Fin 3 → ℝ) (h : SolutionType Q α) :
    ThetaRelation3 (Q 0) (Q 1) (Q 2) (α 0) (α 1) (α 2) :=
  (rel_iff Q α).1 (solutionType_rel h)

/-- **Converse of Theorem 1.1**: if, after some reordering $\sigma$ of the indices, one of the four
cases holds, then $\alpha_0 \theta_{Q_0} + \alpha_1 \theta_{Q_1} + \alpha_2 \theta_{Q_2} = 0$
(coefficientwise). The four cases are solutions (converse of Theorem 1.1; case 4 is Lemma 6.2). -/
@[kb "hanke2023threeterm" "§1, Theorem 1.1, p. 2"]
theorem theorem_1_1_converse {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ}
    (h : ∃ σ : Equiv.Perm (Fin 3), SolutionType (Q ∘ σ) (α ∘ σ)) :
    ThetaRelation3 (Q 0) (Q 1) (Q 2) (α 0) (α 1) (α 2) := by
  obtain ⟨σ, hσ⟩ := h
  have h1 := solutionType_rel hσ
  have h2 := rel_perm (Q ∘ σ) (α ∘ σ) σ⁻¹ h1
  refine (rel_iff Q α).1 fun m => ?_
  have := h2 m
  simpa [Function.comp_def] using this

/-! ### Invariants -/

/-- $\mathrm{E}(u,v) = u^2+uv+v^2 \ge 0$. -/
private lemma E_nonneg (u v : ℤ) : 0 ≤ u ^ 2 + u * v + v ^ 2 := by
  nlinarith [sq_nonneg (2 * u + v), sq_nonneg v]

/-- $r_{cE}(c) \ge 1$ for $c > 0$ (the vector $(1,0)$; the set is finite by `bound_E`). -/
private lemma repNum_formE_self_pos {c : ℤ} (hc : 0 < c) : 1 ≤ repNum (formE c) c := by
  rw [repNum_eq_card_prod]
  have hfin : Finite {p : ℤ × ℤ // (formE c).eval p.1 p.2 = c} := by
    have : Set.Finite {p : ℤ × ℤ | (formE c).eval p.1 p.2 = c} := by
      refine ((Set.finite_Icc (-2 : ℤ) 2).prod (Set.finite_Icc (-2 : ℤ) 2)).subset ?_
      intro p hp
      simp only [Set.mem_ofPred_eq, formE_eval] at hp
      have hE : p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1 := by
        have : c * (p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2) = c * 1 := by linarith
        exact mul_left_cancel₀ hc.ne' this
      obtain ⟨h1, h2⟩ := bound_E hE
      rw [abs_le] at h1 h2
      simp only [abs_one] at h1 h2
      exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
    exact this.to_subtype
  have hne : Nonempty {p : ℤ × ℤ // (formE c).eval p.1 p.2 = c} :=
    ⟨⟨(1, 0), by simp⟩⟩
  exact Nat.card_pos

/-- $r_{4cE}(c) = 0$ for $c > 0$ (since $4cE(u,v) = c$ would force $4E(u,v) = 1$). -/
private lemma repNum_formE_four_self {c : ℤ} (hc : 0 < c) : repNum (formE (4 * c)) c = 0 := by
  rw [repNum_eq_card_prod]
  have : IsEmpty {p : ℤ × ℤ // (formE (4 * c)).eval p.1 p.2 = c} := by
    refine ⟨fun ⟨p, hp⟩ => ?_⟩
    simp only [formE_eval] at hp
    have : 4 * (p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2) = 1 := by
      have : c * (4 * (p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2)) = c * 1 := by linarith
      exact mul_left_cancel₀ hc.ne' this
    omega
  exact Nat.card_of_isEmpty

/-- Case 3 forces all forms to be pairwise equivalent. -/
lemma IsTrivialThreeTerm.equiv {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (h : IsTrivialThreeTerm Q α)
    (i j : Fin 3) : IntEquiv (Q i) (Q j) := by
  obtain ⟨-, -, e01, e12⟩ := h
  have e02 : IntEquiv (Q 0) (Q 2) := IsometricGL.trans e01 e12
  have r : ∀ k, IntEquiv (Q k) (Q k) := fun k => IsometricGL.refl _
  fin_cases i <;> fin_cases j <;> first
    | exact r _ | assumption | exact IsometricGL.symm ‹_›

/-- Case 3 forces every $\alpha_i \ne 0$ (invariant under reordering). -/
lemma IsTrivialThreeTerm.ne_zero {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (σ : Equiv.Perm (Fin 3))
    (h : IsTrivialThreeTerm (Q ∘ σ) (α ∘ σ)) (j : Fin 3) : α j ≠ 0 := by
  have := h.1 (σ.symm j); simpa using this

/-- Case 4 forces every $\alpha_i \ne 0$ (invariant under reordering). -/
lemma IsNonTrivial.ne_zero {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (σ : Equiv.Perm (Fin 3))
    (h : IsNonTrivial (Q ∘ σ) (α ∘ σ)) (j : Fin 3) : α j ≠ 0 := by
  obtain ⟨h1, h2, h0, -⟩ := h
  simp only [Function.comp_apply] at h1 h2 h0
  have a1 : α (σ 1) = 2 * α (σ 0) := by linarith
  have a2 : α (σ 2) = -3 * α (σ 0) := by linarith
  have key : ∀ k, α (σ k) ≠ 0 := by
    intro k; fin_cases k
    · exact h0
    · simp only [Fin.mk_one, Fin.isValue]; rw [a1]; exact mul_ne_zero (by norm_num) h0
    · simp only [Fin.reduceFinMk, Fin.isValue]; rw [a2]; exact mul_ne_zero (by norm_num) h0
  have := key (σ.symm j); simpa using this

/-- **Theorem 1.1, "exactly one" part.** The four cases (degenerate, trivial 2-term, trivial
3-term, non-trivial; each possibly after its own reordering $\sigma$, $\tau$ of the indices) are
pairwise mutually exclusive, in the order (1,2), (1,3), (1,4), (2,3), (2,4), (3,4). -/
@[kb "hanke2023threeterm" "§1, Theorem 1.1, p. 2"]
theorem solutionType_exclusive (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) :
    (∀ σ τ : Equiv.Perm (Fin 3), ¬ (IsDegenerate (α ∘ σ) ∧ IsTrivialTwoTerm (Q ∘ τ) (α ∘ τ))) ∧
    (∀ σ τ : Equiv.Perm (Fin 3), ¬ (IsDegenerate (α ∘ σ) ∧ IsTrivialThreeTerm (Q ∘ τ) (α ∘ τ))) ∧
    (∀ σ τ : Equiv.Perm (Fin 3), ¬ (IsDegenerate (α ∘ σ) ∧ IsNonTrivial (Q ∘ τ) (α ∘ τ))) ∧
    (∀ σ τ : Equiv.Perm (Fin 3),
      ¬ (IsTrivialTwoTerm (Q ∘ σ) (α ∘ σ) ∧ IsTrivialThreeTerm (Q ∘ τ) (α ∘ τ))) ∧
    (∀ σ τ : Equiv.Perm (Fin 3),
      ¬ (IsTrivialTwoTerm (Q ∘ σ) (α ∘ σ) ∧ IsNonTrivial (Q ∘ τ) (α ∘ τ))) ∧
    (∀ σ τ : Equiv.Perm (Fin 3),
      ¬ (IsTrivialThreeTerm (Q ∘ σ) (α ∘ σ) ∧ IsNonTrivial (Q ∘ τ) (α ∘ τ))) := by
  have zero_of : ∀ σ : Equiv.Perm (Fin 3), IsDegenerate (α ∘ σ) → ∀ j, α j = 0 := by
    intro σ h j; have := h (σ.symm j); simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro σ τ ⟨hd, -, h0, -, -⟩
    exact (by simpa using h0 : α (τ 0) ≠ 0) (zero_of σ hd _)
  · rintro σ τ ⟨hd, h⟩
    exact h.ne_zero τ 0 (zero_of σ hd _)
  · rintro σ τ ⟨hd, h⟩
    exact h.ne_zero τ 0 (zero_of σ hd _)
  · rintro σ τ ⟨⟨-, -, h2, -⟩, h⟩
    exact h.ne_zero τ (σ 2) h2
  · rintro σ τ ⟨⟨-, -, h2, -⟩, h⟩
    exact h.ne_zero τ (σ 2) h2
  · rintro σ τ ⟨h3, -, -, -, c, hc, e0, e1, -⟩
    have h3' : IntEquiv (Q (τ 0)) (Q (τ 1)) := by
      simpa using h3.equiv (σ.symm (τ 0)) (σ.symm (τ 1))
    simp only [Function.comp_apply] at e0 e1
    have hE : IntEquiv (formE c) (formE (4 * c)) :=
      IsometricGL.trans (IsometricGL.symm e0)
        (IsometricGL.trans h3' e1)
    have := repNum_eq_of_intEquiv hE c
    have h1 := repNum_formE_self_pos hc
    have h2 := repNum_formE_four_self hc
    omega

end QuadFormsKB.Hanke2023ThreeTerm
