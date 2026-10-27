/-
# A global diagonalization of a nondegenerate form over $\mathcal O_F$

**Layer:** $F$ a number field, forms over $\mathcal O_F$ and over the completions $\mathfrak o_\mathfrak p$.

**Proves**
* `exists_diag_global`: a nondegenerate $T_0$ over $\mathcal O_F$ has $T_0\circ P = \langle d_0, \dots, d_{r-1}\rangle$ with $P$ integral,
  $\det P \ne 0$, all $d_i \ne 0$ (an orthogonal basis over $F$, `exists_orthogonal_basis`, with denominators cleared);
* `exists_diag_local`: the same over $\mathfrak o_\mathfrak p$ for `NF.Qp v T₀` (the global data mapped by $\iota$).

Indices are 0-based.
-/
import QuadFormsKB.Lattices.CartanDieudonne
import QuadFormsKB.LocalDensity.FormDensity
import QuadFormsKB.LocalDensity.NFBridge

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

theorem hessian_map_alg (T₀ : QuadForm (𝓞 F) r) :
    (T₀.map (algebraMap (𝓞 F) F)).hessian = T₀.hessian.map (algebraMap (𝓞 F) F) := by
  ext i j; simp [QuadForm.hessian, QuadForm.map]

theorem hessian_diag (dg : Fin r → 𝓞 F) :
    (QuadForm.diag dg).hessian = Matrix.diagonal (fun i => 2 * dg i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [QuadForm.hessian, QuadForm.diag, two_mul]
  · simp [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_apply, h, Ne.symm h]

/-- **A global diagonalization** of a nondegenerate form over $\mathcal O_F$: $T_0\circ P = \langle d_0, \dots, d_{r-1}\rangle$ with $P$ integral,
$\det P \ne 0$, all $d_i \ne 0$. -/
theorem exists_diag_global (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) :
    ∃ (P : Matrix (Fin r) (Fin r) (𝓞 F)) (dg : Fin r → 𝓞 F), P.det ≠ 0 ∧ (∀ i, dg i ≠ 0) ∧
      T₀.compMat P = QuadForm.diag dg := by
  classical
  set T := T₀.map (algebraMap (𝓞 F) F) with hTdef
  have hTF : T.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hTdef, hessian_map_alg, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  obtain ⟨e, hort, hne⟩ := exists_orthogonal_basis T F hTF
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (Finset.univ.image fun p : Fin r × Fin r => e p.2 p.1)
  choose a ha using fun p : Fin r × Fin r => hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  let P : Matrix (Fin r) (Fin r) (𝓞 F) := Matrix.of fun i j => a (i, j)
  have hPe : ∀ i j, algebraMap (𝓞 F) F (P i j) = (b : 𝓞 F) • e j i := fun i j => ha (i, j)
  have hcol : ∀ j, (fun l => algebraMap (𝓞 F) F (P l j)) = (algebraMap (𝓞 F) F (b : 𝓞 F)) • e j := by
    intro j; funext l
    rw [hPe, Algebra.smul_def]; rfl
  have hbne : algebraMap (𝓞 F) F (b : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (nonZeroDivisors.coe_ne_zero b)
  have hdiag : ∀ i, algebraMap (𝓞 F) F (T₀.eval fun l => P l i) =
      algebraMap (𝓞 F) F (b : 𝓞 F) ^ 2 * T.evalIn F (e i) := by
    intro i
    rw [← eval_map_comp (algebraMap (𝓞 F) F) T₀ (fun l => P l i)]
    show T.evalIn F _ = _
    rw [hcol i, evalIn_smul']
  have hoff : ∀ i j, i < j →
      (fun l => P l i) ⬝ᵥ (T₀.hessian *ᵥ fun l => P l j) = 0 := by
    intro i j hij
    apply (map_eq_zero_iff _ RingOfIntegers.coe_injective).mp
    have e1 : algebraMap (𝓞 F) F ((fun l => P l i) ⬝ᵥ (T₀.hessian *ᵥ fun l => P l j)) =
        (fun l => algebraMap (𝓞 F) F (P l i)) ⬝ᵥ
          (T₀.hessian.map (algebraMap (𝓞 F) F) *ᵥ fun l => algebraMap (𝓞 F) F (P l j)) := by
      simp [dotProduct, Matrix.mulVec, map_sum, map_mul]
    rw [e1, hcol i, hcol j, ← hessian_map_alg, ← hTdef, smul_dotProduct, mulVec_smul, dotProduct_smul]
    have hq := hort i j hij.ne
    unfold qbil at hq
    simp only [Algebra.algebraMap_self] at hq
    have hm : T.hessian.map (RingHom.id F) = T.hessian := by ext; simp
    rw [hm] at hq
    simp [hq]
  have hdg : ∀ i, T₀.eval (fun l => P l i) ≠ 0 := by
    intro i h0
    have := hdiag i
    rw [h0, map_zero] at this
    exact (mul_ne_zero (pow_ne_zero 2 hbne) (hne i)) this.symm
  have heq : T₀.compMat P = QuadForm.diag (fun i => T₀.eval fun l => P l i) := by
    refine QuadForm.ext_upper fun i j hij => ?_
    rw [QuadForm.compMat_coeff, if_pos hij]
    simp only [QuadForm.diag, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg h]
      exact hoff i j (lt_of_le_of_ne hij h)
  refine ⟨P, fun i => T₀.eval fun l => P l i, ?_, hdg, heq⟩
  intro hP0
  have h1 := congrArg QuadForm.hessian heq
  rw [QuadForm.hessian_compMat, hessian_diag] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hP0, mul_zero] at h2
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero two_ne_zero (hdg i)) h2.symm

/-- **The local diagonalization:** the global data of `exists_diag_global`, mapped to $\mathfrak o_\mathfrak p$ by $\iota$, gives
$T_0\circ P = \langle d_0, \dots, d_{r-1}\rangle$ over $\mathfrak o_\mathfrak p$ with $\det P \ne 0$, all $d_i \ne 0$. -/
theorem exists_diag_local (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (P : Matrix (Fin r) (Fin r) (v.adicCompletionIntegers F)) (dg : Fin r → v.adicCompletionIntegers F),
      P.det ≠ 0 ∧ (∀ i, dg i ≠ 0) ∧ (NF.Qp v T₀).compMat P = QuadForm.diag dg := by
  obtain ⟨P, dg, hP, hdg, h⟩ := exists_diag_global T₀ hT
  refine ⟨P.map (NF.ι v), fun i => NF.ι v (dg i), ?_, fun i => NF.ι_ne_zero v (hdg i), ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact NF.ι_ne_zero v hP
  · rw [NF.Qp, QuadForm.map_compMat, h]
    ext i j
    simp [QuadForm.map, QuadForm.diag, Matrix.diagonal_apply]

end QuadFormsKB.Tamagawa.Frames
