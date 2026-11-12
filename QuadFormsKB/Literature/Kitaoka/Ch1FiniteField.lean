/-
# Kitaoka 1993, Theorem 1.3.1: regular quadratic spaces over a finite field

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms*, Cambridge Tracts in Mathematics 106 (1993), §1.3, Theorem 1.3.1,
p. 14. Page numbers are the printed pages of the book.

**Setting.** $F$ is a finite field and $(V, Q)$ is a finite-dimensional quadratic space whose polar bilinear form is
nondegenerate.

**Proves** `theorem131`: $Q \cong H^k$, or $Q \cong H^k \perp W$ with $W$ an anisotropic quadratic form on $F^2$, or
(only when $\operatorname{char} F \ne 2$) $Q \cong H^k \perp \langle a\rangle$ with $a \ne 0$. The result is
unconditional.

*Proof.* (1) By Witt decomposition (`QuadraticForm.wittIndex_spec`), $Q \cong H^k \perp Q_a$ with $Q_a$ anisotropic on a
finite-dimensional space $U$. (2) An anisotropic form over a finite field has $\dim U \le 2$: a form in three variables
has a nontrivial zero by the Chevalley–Warning theorem (`QuadFormsKB.Siegel.Kneser.exists_isotropic_of_three_le`).
(3) For $\dim U = 0$ one gets $H^k$; for $\dim U = 2$ one transports $Q_a$ to $F^2$; for $\dim U = 1$,
$Q_a \cong \langle a\rangle$ with $a = Q_a(e) \ne 0$, and in characteristic $2$ the vector $(0, e)$ would be in the
kernel of the polar form of $H^k \perp Q_a$, contradicting nondegeneracy.
-/
import QuadFormsKB.Literature.Kitaoka.Ch1Spaces
import QuadFormsKB.Siegel.KneserConnectedProof
import QuadFormsKB.Witt.Extension

open QuadraticMap

noncomputable section

namespace QuadFormsKB.Kitaoka

section FiniteField

variable {F : Type} [Field F]

/-- A quadratic form on $F^3$ over a finite field has a nonzero zero. The form is rewritten as the coordinate
quadratic form $\sum_{i \le j} c_{ij} x_i x_j$ with $c_{ii} = P(e_i)$ and $c_{ij} = B_P(e_i, e_j)$. -/
theorem exists_isotropic_fin_three [Finite F] (P : QuadraticForm F (Fin 3 → F)) :
    ∃ z : Fin 3 → F, z ≠ 0 ∧ P z = 0 := by
  classical
  let e : Fin 3 → (Fin 3 → F) := fun i => Pi.single i 1
  let S : QuadFormsKB.QuadForm F 3 :=
    QuadFormsKB.QuadForm.ofUpper fun i j => if i = j then P (e i) else polar P (e i) (e j)
  obtain ⟨z, hz, hz0⟩ := QuadFormsKB.Siegel.Kneser.exists_isotropic_of_three_le (le_refl 3) S
  refine ⟨z, hz, ?_⟩
  have hdecomp : z = z 0 • e 0 + z 1 • e 1 + z 2 • e 2 := by
    ext i; fin_cases i <;> simp [e]
  have : P z = S.eval z := by
    conv_lhs => rw [hdecomp]
    rw [QuadraticMap.map_add P, QuadraticMap.map_add P, polar_add_left]
    simp only [polar_smul_left, polar_smul_right, QuadraticMap.map_smul]
    simp only [S, QuadFormsKB.QuadForm.eval, QuadFormsKB.QuadForm.evalIn,
      QuadFormsKB.QuadForm.ofUpper, Fin.sum_univ_three, Algebra.algebraMap_self, RingHom.id_apply]
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    simp only [smul_eq_mul, Matrix.of_apply, Fin.isValue, le_refl, ↓reduceIte, Fin.reduceLE, h01,
      h02, h12]
    ring
  rw [this, hz0]

/-- **An anisotropic quadratic space over a finite field has dimension at most $2$.** A three-dimensional subspace
would carry a form in three variables, which has a nonzero zero (`exists_isotropic_fin_three`). -/
theorem finrank_le_two_of_anisotropic [Finite F] {U : Type} [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] (Qa : QuadraticForm F U) (h : Qa.Anisotropic) :
    Module.finrank F U ≤ 2 := by
  by_contra hlt
  have h3 : 3 ≤ Module.finrank F U := by omega
  let b := Module.finBasis F U
  let g : Fin 3 → U := fun i => b (Fin.castLE h3 i)
  have hli : LinearIndependent F g := b.linearIndependent.comp _ (Fin.castLE_injective h3)
  let f : (Fin 3 → F) →ₗ[F] U := Fintype.linearCombination F g
  have hf : Function.Injective f := hli.fintypeLinearCombination_injective
  obtain ⟨z, hz, hz0⟩ := exists_isotropic_fin_three (Qa.comp f)
  exact hz (hf ((h (f z) hz0).trans (map_zero f).symm))

end FiniteField

/-- **Kitaoka 1993, Theorem 1.3.1** (p. 14): a regular quadratic space over a finite field $F$ is isometric to $H^k$,
to $H^k \perp W$ with $W$ an anisotropic quadratic form on $F^2$, or, only when $\operatorname{char} F \ne 2$, to
$H^k \perp \langle a\rangle$ with $a \ne 0$. Unconditional. -/
@[kb "kitaoka1993" "§1.3, Thm. 1.3.1, p. 14"]
theorem theorem131 : Theorem131 := by
  intro F _ _ V _ _ _ Q hQ
  classical
  obtain ⟨U, _, _, _, Qa, ha, hQe⟩ :=
    QuadraticForm.wittIndex_spec Q (QuadraticForm.radical_eq_bot_of_nondegenerate Q hQ)
  refine ⟨QuadraticForm.wittIndex Q, ?_⟩
  have hle := finrank_le_two_of_anisotropic Qa ha
  have hcases : Module.finrank F U = 0 ∨ Module.finrank F U = 1 ∨ Module.finrank F U = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · left
    have : Subsingleton U := Module.finrank_zero_iff.mp h0
    let _ : Unique U := uniqueOfSubsingleton 0
    refine hQe.trans ⟨{ toLinearEquiv := LinearEquiv.prodUnique, map_app' := fun p => ?_ }⟩
    simp [Subsingleton.elim p.2 0]
  · right; right
    let e : (Fin 1 → F) ≃ₗ[F] U := LinearEquiv.ofFinrankEq _ U (by simp [h1])
    let v : U := e (fun _ => 1)
    have hv : v ≠ 0 := by
      intro h
      have := (map_eq_zero_iff e e.injective).mp h
      simp [funext_iff] at this
    have ha0 : Qa v ≠ 0 := fun h => hv (ha v h)
    have hdec : ∀ z : Fin 1 → F, z = z 0 • (fun _ : Fin 1 => (1 : F)) := by
      intro z; ext i; fin_cases i; simp
    have hez : ∀ z : Fin 1 → F, e z = z 0 • v := by
      intro z
      calc e z = e (z 0 • fun _ : Fin 1 => (1 : F)) := congrArg e (hdec z)
        _ = z 0 • v := map_smul e _ _
    have hform : ∀ z : Fin 1 → F, Qa (e z) = z 0 * z 0 * Qa v := by
      intro z
      rw [hez z, QuadraticMap.map_smul, smul_eq_mul]
    have hrefl : Qa.Equivalent (weightedSumSquares F ![Qa v]) :=
      ⟨{ toLinearEquiv := e.symm, map_app' := fun u => by
          obtain ⟨z, rfl⟩ := e.surjective u
          simp [hform z]
          ring }⟩
    refine ⟨?_, Qa v, ha0, hQe.trans (QuadraticMap.Equivalent.prod (QuadraticMap.Equivalent.refl _) hrefl)⟩
    intro hchar
    have hchar2 : CharP F 2 := hchar ▸ ringChar.charP F
    have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
    obtain ⟨g⟩ := hQe
    let w : V := g.symm ((0 : Fin (QuadraticForm.wittIndex Q) → F × F), v)
    have hgw : g w = (0, v) := g.apply_symm_apply _
    have hw0 : w ≠ 0 := by
      intro h
      have : g w = 0 := by rw [h]; exact map_zero g
      rw [hgw] at this
      exact hv (Prod.mk.inj this).2
    refine hw0 (hQ.1 w fun y => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]
    obtain ⟨z, hz⟩ := e.surjective (g y).2
    have hy : g y = ((g y).1, z 0 • v) := by
      exact Prod.ext rfl (hz.symm.trans (hez z))
    have key : Q (w + y) - Q w - Q y = 0 := by
      rw [← g.map_app (w + y), ← g.map_app w, ← g.map_app y, map_add, hgw, hy]
      simp only [prod_apply, Prod.fst_add, Prod.snd_add, zero_add, map_zero]
      have hvv : v + z 0 • v = (1 + z 0) • v := by rw [add_smul, one_smul]
      rw [hvv, QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
      linear_combination (z 0 * Qa v) * h2
    exact key
  · right; left
    let e : U ≃ₗ[F] (Fin 2 → F) := LinearEquiv.ofFinrankEq U _ (by simp [h2])
    refine ⟨Qa.comp e.symm.toLinearMap, ?_, ?_⟩
    · intro x hx
      have := ha _ hx
      simpa using this
    · exact hQe.trans (QuadraticMap.Equivalent.prod (QuadraticMap.Equivalent.refl _)
        ⟨{ toLinearEquiv := e, map_app' := fun u => by simp }⟩)

end QuadFormsKB.Kitaoka
