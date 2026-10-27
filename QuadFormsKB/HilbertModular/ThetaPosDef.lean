import QuadFormsKB.HilbertModular.ThetaGamma0
import QuadFormsKB.Lattices.Finite

/-!
# Total positivity of a form over $\mathcal{O}_F$ at every real place

The theta series of `Theta.lean` assume `IsTotPosGram (gramF Q)`: $\varphi_v(A)$ is positive definite over $\mathbb{R}$ at every real
place $v$. This file derives it from total positivity on $F^n$ (`QuadFormsKB.Lattices.IsTotallyPosDef`: $Q(x) \gg 0$ for
$x \in F^n\setminus0$):

* `isTotPosGram_of_pos`: if $\varphi_v(Q(x)) > 0$ for all $x \in F^n\setminus0$ and all $v$, then $\varphi_v(A)$ is positive definite.
  *Proof:* $y^{\mathsf T}\varphi_v(A)y \ge 0$ on the dense set $\mathbb{Q}^n \subset \mathbb{R}^n$, hence everywhere; and $\det A \ne 0$ because $Q$ is
  anisotropic over $F$, so the positive semidefinite $\varphi_v(A)$ is definite (`Matrix.PosSemidef.posDef_iff_det_ne_zero`).
* `isTotPosGram_of_isTotallyPosDef`: the same from `Lattices.IsTotallyPosDef (Q.map (algebraMap (𝓞 F) F))`.
-/

open Matrix NumberField NumberField.InfinitePlace Complex
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

lemma gramF_transpose (Q : QuadForm (𝓞 F) n) : (gramF Q)ᵀ = gramF Q := by
  rw [gramF_eq, transpose_smul, hessF_transpose]

/-- **Positive definiteness at every real place** from positivity on $F^n$. -/
theorem isTotPosGram_of_pos {Q : QuadForm (𝓞 F) n}
    (h : ∀ x : Fin n → F, x ≠ 0 → ∀ v : InfinitePlace F, 0 < realEmb F v (qv (gramF Q) x)) :
    IsTotPosGram (gramF Q) := by
  intro v
  set B := (gramF Q).map (realEmb F v) with hBdef
  have hB : B.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, hBdef, ← transpose_map,
      gramF_transpose]
  -- `det A ≠ 0`
  have hdet : (gramF Q).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := h x hx v
    rw [qv, hAx, dotProduct_zero, map_zero] at this
    exact lt_irrefl _ this
  have hdetB : B.det ≠ 0 := by
    rw [hBdef, show ((gramF Q).map (realEmb F v)).det = realEmb F v (gramF Q).det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ (realEmb F v).injective).mpr hdet
  -- semidefinite: positivity on `ℚⁿ` and density
  have hsemi : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ B *ᵥ y := by
    have hdense : DenseRange (Pi.map fun (_ : Fin n) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    intro y
    refine hdense.induction_on y ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro q
      by_cases hq : q = 0
      · subst hq; simp [Pi.map, dotProduct]
      · have hx : (fun i => ((q i : ℚ) : F)) ≠ 0 := by
          intro h0; apply hq; funext i
          have := congrFun h0 i
          simpa using this
        have h1 := (h _ hx v).le
        rw [realEmb_qv] at h1
        have hφ : (fun i => realEmb F v ((q i : ℚ) : F)) = Pi.map (fun _ (q : ℚ) => (q : ℝ)) q := by
          funext i; simp [Pi.map]
        rw [hφ] at h1
        exact h1
  have hps : B.PosSemidef := posSemidef_iff_dotProduct_mulVec.mpr ⟨hB, fun y => by
    simpa [star_trivial] using hsemi y⟩
  exact hps.posDef_iff_det_ne_zero.mpr hdetB

/-- $(Q \otimes F)(x) = x^{\mathsf T}Ax$ for $x \in F^n$. -/
lemma eval_map_eq_qv (Q : QuadForm (𝓞 F) n) (x : Fin n → F) :
    (Q.map (algebraMap (𝓞 F) F)).eval x = qv (gramF Q) x := by
  have h1 : (Q.map (algebraMap (𝓞 F) F)).eval x = Q.evalIn F x := by
    simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, Matrix.map_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
  rw [h1, QuadForm.evalIn_eq_dotProduct, qv, gramF, QuadForm.hessian, Matrix.map_add _ (map_add _),
    Matrix.transpose_map, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add]
  generalize Q.coeff.map (algebraMap (𝓞 F) F) = C
  have : x ⬝ᵥ Cᵀ *ᵥ x = x ⬝ᵥ C *ᵥ x := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  rw [this, smul_eq_mul]
  ring

/-- **Total positivity per place from total positive definiteness on $F^n$**: if $Q \otimes F$ is totally positive definite
(`QuadFormsKB.Lattices.IsTotallyPosDef`), then $\varphi_v(A)$ is positive definite at every real place (`IsTotPosGram`), the hypothesis
of the theta series over $F$. -/
@[kb "omeara1963" "§61A, p. 154 (positive definite space over a real field)"]
theorem isTotPosGram_of_isTotallyPosDef {Q : QuadForm (𝓞 F) n}
    (hQ : QuadFormsKB.Lattices.IsTotallyPosDef (Q.map (algebraMap (𝓞 F) F))) :
    IsTotPosGram (gramF Q) := by
  refine isTotPosGram_of_pos fun x hx v => ?_
  have h := hQ x hx (complexEmb v)
  rw [eval_map_eq_qv, complexEmb_apply] at h
  exact_mod_cast h

end

end QuadFormsKB.HilbertModular
