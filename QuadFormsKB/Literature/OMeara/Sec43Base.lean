import QuadFormsKB.Literature.OMeara.Sec43Low

/-!
# O'Meara §43F: bases of vectors of equal length in binary spaces (43:15, the case $n = 2$)

**Setting** (as in `Sec43E.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a regular quadratic space of dimension $2$,
`IsExceptional43 Q` the hyperbolic plane over a field of three elements.

**Proves** (O'Meara 1973 printing, Chapter IV, §43F, p. 112):
* `exists_basis_Q_eq_of_finrank_two` (**43:15**, the case $n = 2$, $\alpha \ne 0$): if $V$ is binary, regular and not
  exceptional, and $0 \ne \alpha \in Q(V)$, then $V$ has a base $x_0, x_1$ with $Q(x_0) = Q(x_1) = \alpha$.

**Proof notes.** As in the book: with $Q(x) = \alpha$ and an anisotropic $x' \perp x$, the symmetry $\tau_u$ with
$u = x + t x'$ ($t \ne 0$, $Q(u) \ne 0$) moves the line $Fx$, and $x, \tau_u x$ is the base. A suitable $t$ exists
unless $Q(x') = -\alpha$ and $F$ has three elements, which is the exceptional case. The cases $n \ge 3$ (which use
43:14) and $\alpha = 0$ are not formalized.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Base

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- **O'Meara 43:15** (p. 112), the binary case with $\alpha \ne 0$: a regular binary space other than a hyperbolic
plane over a field of three elements, with $0 \ne \alpha \in Q(V)$, has a base $x_0, x_1$ with
$Q(x_0) = Q(x_1) = \alpha$. -/
@[kb "omeara1963" "§43F, 43:15, p. 112 (case n = 2, α ≠ 0)"]
theorem exists_basis_Q_eq_of_finrank_two (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h2 : finrank F V = 2) (hexc : ¬ IsExceptional43 Q) {α : F} (hα : α ≠ 0) {x : V} (hx : Q x = α) :
    ∃ b : Basis (Fin 2) F V, ∀ i, Q (b i) = α := by
  have hx0 : x ≠ 0 := fun h => hα (by rw [← hx, h, map_zero])
  have hU : finrank F (F ∙ x) + 1 = finrank F V := by rw [finrank_span_singleton hx0, h2]
  obtain ⟨x', hx', hxx'⟩ : ∃ x', Q x' ≠ 0 ∧ bil Q x x' = 0 := by
    rcases hyperplane_dichotomy Q hQ hU with ⟨w, hw, hw0, hwU⟩ | ⟨z, hz, hzU⟩
    · exfalso
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have := hwU (c • x) hw
      rw [bil_self, Q_smul, hx] at this
      have hc : c ≠ 0 := fun h => hw0 (by rw [h, zero_smul])
      exact mul_ne_zero (pow_ne_zero 2 hc) hα this
    · exact ⟨z, hz, hzU x (Submodule.mem_span_singleton_self x)⟩
  have hQu : ∀ t : F, Q (x + t • x') = α + t ^ 2 * Q x' := fun t => by
    rw [Q_add, Q_smul, bil_smul_right, hxx', hx]; ring
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ Q (x + t • x') ≠ 0 := by
    by_cases h1 : α + Q x' = 0
    · have hcard : Nat.card F ≠ 3 := by
        intro h3
        apply hexc
        refine ⟨h2, ⟨x + (1 : F) • x', ?_, ?_⟩, h3⟩
        · intro h0
          have := congrArg (bil Q x) h0
          rw [bil_add_right, bil_smul_right, hxx', bil_self, hx, iv_bil_zero_right] at this
          exact hα (by simpa using this)
        · rw [hQu]; linear_combination h1
      obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_mul_self_ne_one hcard
      refine ⟨a, ha0, ?_⟩
      rw [hQu]
      have : α + a ^ 2 * Q x' = α * (1 - a * a) := by linear_combination (a ^ 2) * h1
      rw [this]
      exact mul_ne_zero hα (sub_ne_zero.2 (Ne.symm ha1))
    · exact ⟨1, one_ne_zero, by rw [hQu]; simpa using h1⟩
  set u := x + t • x'
  set y := symmetry Q u ht x
  have hy : Q y = α := by rw [← hx]; exact symmetry_mem_orth Q ht x
  have hBxu : bil Q x u = α := by rw [bil_add_right, bil_smul_right, hxx', bil_self, hx]; ring
  set c := 2 * bil Q x u / Q u
  have hc : c ≠ 0 := by
    show 2 * bil Q x u / Q u ≠ 0
    rw [hBxu]; exact div_ne_zero (mul_ne_zero iv_two_ne hα) ht
  have hyx : y = (1 - c) • x - (c * t) • x' := by
    simp only [y, symmetry_apply, u, c]; rw [smul_add, smul_smul]; module
  have hli0 : LinearIndependent F ![x, x'] := by
    apply linearIndependent_of_det_gram_ne_zero (R := F) Q
    rw [Matrix.det_fin_two]
    simp [gram, hxx', bil_comm Q x' x, hx, hα, hx']
  have hli : LinearIndependent F ![x, y] := by
    rw [LinearIndependent.pair_iff] at hli0 ⊢
    intro s r hsr
    rw [hyx] at hsr
    have := hli0 (s + r * (1 - c)) (-(r * (c * t))) (by rw [← hsr]; module)
    have hr : r = 0 := by
      have h' := this.2
      rw [neg_eq_zero] at h'
      exact (mul_eq_zero.1 h').resolve_right (mul_ne_zero hc ht0)
    subst hr
    exact ⟨by simpa using this.1, rfl⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2]), fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  fin_cases i
  · simpa using hx
  · simpa using hy

end Sec43Base

end QuadFormsKB.OMeara
