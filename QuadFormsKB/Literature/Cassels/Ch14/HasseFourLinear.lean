/-
# Cassels, Chapter 14, §7: an isotropic vector from three hyperbolic planes

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §7, p. 354, step 4: if $h = f \perp (-g)$ (in $4 + 2$
variables) is the sum of three hyperbolic planes over $\mathbb Q$, then $h = \sum_{j=1}^3 \varphi_j \psi_j$ for
linear forms $\varphi_j, \psi_j$, and a non-zero solution $(a_1, \dots, a_4)$ of the three linear equations
$\varphi_j(a_1, \dots, a_4, 0, 0) = 0$ in four unknowns gives $f(a_1, \dots, a_4) = 0$.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Existence

namespace QuadFormsKB.Composition

open QuadForm

/-- The doubling map $\{0,\dots,5\} \to \{0,1,2\}$, $(0,0,1,1,2,2)$. -/
private def dbl : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

private lemma dbl_surj : Function.Surjective dbl := by decide

/-- The form $\langle 1,-1,1,-1,1,-1 \rangle$ vanishes on doubled vectors $(s_0,s_0,s_1,s_1,s_2,s_2)$. -/
private lemma T_dbl (s : Fin 3 → ℚ) :
    (diag ![(1 : ℚ), -1, 1, -1, 1, -1]).evalIn ℚ (fun i => s (dbl i)) = 0 := by
  rw [QuadForm.evalIn_diag, Fin.sum_univ_six]
  simp [dbl]

/-- **Cassels, Ch. 14, §7, step 4** (p. 354): if $\langle a, c \rangle$ ($a \in \mathbb Q^4$, $c \in \mathbb Q^2$) is
isometric over $\mathbb Q$ to $\langle 1, -1, 1, -1, 1, -1 \rangle$, then $\langle a \rangle$ is isotropic over
$\mathbb Q$. -/
theorem isotropic_of_isometric_hyp_three {a : Fin 4 → ℚ} {c : Fin 2 → ℚ}
    (h : (diag (Fin.append a c)).IsometricIn ℚ (diag ![1, -1, 1, -1, 1, -1])) : (diag a).IsotropicIn ℚ := by
  obtain ⟨P, hP, hPe⟩ := h
  let L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 6 → ℚ) := LinearMap.funLeft ℚ ℚ dbl
  let f : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
    (LinearMap.funLeft ℚ ℚ (Fin.natAdd 4 : Fin 2 → Fin 6)) ∘ₗ (Matrix.mulVecLin P) ∘ₗ L
  have hker : LinearMap.ker f ≠ ⊥ :=
    f.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hsne : s ≠ 0 := hs0
  have hLinj : Function.Injective L := LinearMap.funLeft_injective_of_surjective _ _ _ dbl_surj
  have hPinj : Function.Injective P.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det P).2 hP)
  set x : Fin 6 → ℚ := P.mulVec (L s) with hx
  have hx0 : x ≠ 0 := by
    intro h0
    apply hsne
    apply hLinj
    apply hPinj
    rw [map_zero, Matrix.mulVec_zero]
    exact h0
  have hf : ∀ i : Fin 2, x (Fin.natAdd 4 i) = 0 := by
    intro i
    have := congrFun (LinearMap.mem_ker.1 hs) i
    simpa [f, hx, Matrix.mulVecLin_apply] using this
  have hval := hPe (L s)
  have hT : (diag ![(1 : ℚ), -1, 1, -1, 1, -1]).evalIn ℚ (L s) = 0 := T_dbl s
  rw [hT] at hval
  refine ⟨fun i => x (Fin.castAdd 2 i), ?_, ?_⟩
  · intro h0
    apply hx0
    funext j
    refine Fin.addCases (m := 4) (n := 2) (motive := fun j => x j = (0 : Fin 6 → ℚ) j)
      (fun i => ?_) (fun i => ?_) j
    · exact congrFun h0 i
    · exact hf i
  · rw [QuadForm.evalIn_diag, Fin.sum_univ_add, ← hx] at hval
    rw [QuadForm.evalIn_diag]
    simpa [Fin.append_left, Fin.append_right, hf] using hval


end QuadFormsKB.Composition
