/-
# Watson (1963): tools for the local representations at $2$

Dimension-generic versions of the even unimodular facts (`exists_eval_eq_unit'`, `exists_orth_pair'`,
`exists_rep_unimod'`), unimodular complements inside a unimodular form (`exists_unimod_complement`), and
representations of diagonal forms (`rep2_diag_two`, `map_diag`).
-/
import QuadFormsKB.Literature.Watson1963.Swap2
import QuadFormsKB.Literature.Watson1963.PsiAnis

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

variable {N : ℕ}

theorem exists_eval_eq_unit' {N' : ℕ} (V : QuadForm ℤ_[2] N') (hV : IsUnit V.hessian.det) (hE : Even N')
    (h2 : 2 ≤ N') {u : ℤ_[2]} (hu : IsUnit u) : ∃ x, V.eval x = u := by
  obtain ⟨k, rfl⟩ : ∃ k, N' = 2 * k := ⟨N' / 2, by obtain ⟨r, hr⟩ := hE; omega⟩
  exact exists_eval_eq_unit V hV (by omega) hu

theorem exists_orth_pair' {N' : ℕ} (V : QuadForm ℤ_[2] N') (hV : IsUnit V.hessian.det) (hE : Even N')
    (h4 : 4 ≤ N') (a : ℤ_[2]) {c : ℤ_[2]} (hc : IsUnit c) :
    ∃ x y, V.eval x = a ∧ V.eval y = c ∧ x ⬝ᵥ (V.hessian *ᵥ y) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, N' = 2 * k := ⟨N' / 2, by obtain ⟨r, hr⟩ := hE; omega⟩
  exact exists_orth_pair V hV (by omega) a hc

theorem exists_rep_unimod' {N' v : ℕ} (U : QuadForm ℤ_[2] N') (Y : QuadForm ℤ_[2] v) (hU : IsUnit U.hessian.det)
    (hY : IsUnit Y.hessian.det) (hE : Even N') (hv : Even v) (hle : v + 2 ≤ N') :
    ∃ H₁ : Matrix (Fin N') (Fin v) ℤ_[2], ∀ y, U.eval (H₁ *ᵥ y) = Y.eval y := by
  obtain ⟨j, rfl⟩ : ∃ j, v = 2 * j := ⟨v / 2, by obtain ⟨r, hr⟩ := hv; omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, N' = 2 * j + 2 * (m + 1) := ⟨N' / 2 - j - 1, by obtain ⟨r, hr⟩ := hE; omega⟩
  exact exists_rep_of_even_unimodular U Y hU hY

/-- **The complement of a unimodular summand of a unimodular form is unimodular.** -/
theorem isUnit_det_complement {n v m : ℕ} (hm : v + m = n) {Q : QuadForm ℤ_[2] n} {φ : QuadForm ℤ_[2] v}
    (H : Matrix (Fin n) (Fin v) ℤ_[2]) (hH : ∀ y, Q.eval (H *ᵥ y) = φ.eval y) (K : Matrix (Fin n) (Fin m) ℤ_[2])
    (horth : ∀ y c, (H *ᵥ y) ⬝ᵥ (Q.hessian *ᵥ (K *ᵥ c)) = 0) (hspan : ∀ z, ∃ y c, z = H *ᵥ y + K *ᵥ c)
    (hQ : IsUnit Q.hessian.det) : IsUnit (Q.compMat K).hessian.det := by
  have hiso := isometricGL_of_complement hm H hH K horth hspan
  subst hm
  obtain ⟨w, hw, hd⟩ := exists_hessian_det_of_isometricGL hiso
  rw [hessian_orthSum_det] at hd
  have : IsUnit (φ.hessian.det * (Q.compMat K).hessian.det) := hd ▸ (hw.pow 2).mul hQ
  exact (IsUnit.mul_iff.1 this).2

/-- **A unimodular form with a unimodular subform: the subform and its (unimodular) complement.** If $U$ (rank $N'$)
and $Y$ (rank $v$) are even unimodular, both ranks even and $v + 2 \le N'$, then $U(H_1\vec y) = Y(\vec y)$ and there is
a complement $K_1$ of even rank $N' - v \ge 2$, orthogonal to $H_1$, with $U \circ K_1$ unimodular. -/
theorem exists_unimod_complement {N' v : ℕ} (U : QuadForm ℤ_[2] N') (Y : QuadForm ℤ_[2] v)
    (hU : IsUnit U.hessian.det) (hY : IsUnit Y.hessian.det) (hE : Even N') (hv : Even v) (hle : v + 2 ≤ N') :
    ∃ (H₁ : Matrix (Fin N') (Fin v) ℤ_[2]) (l : ℕ) (K₁ : Matrix (Fin N') (Fin l) ℤ_[2]),
      v + l = N' ∧ (∀ y, U.eval (H₁ *ᵥ y) = Y.eval y) ∧
      (∀ y c, (H₁ *ᵥ y) ⬝ᵥ (U.hessian *ᵥ (K₁ *ᵥ c)) = 0) ∧ IsUnit (U.compMat K₁).hessian.det := by
  obtain ⟨H₁, hH₁⟩ := exists_rep_unimod' U Y hU hY hE hv hle
  have hG : IsUnit (H₁ᵀ * U.hessian * H₁).det := by
    have : (U.compMat H₁) = Y := QuadForm.eq_of_eval_eq fun y => by rw [QuadForm.eval_compMat, hH₁]
    rw [← QuadForm.hessian_compMat, this]; exact hY
  obtain ⟨l, hl, K₁, horth, hspan, -⟩ := exists_complement_unimodular' U.hessian H₁ hG
  exact ⟨H₁, l, K₁, hl, hH₁, horth, isUnit_det_complement hl H₁ hH₁ K₁ horth hspan hU⟩

/-- Base change of a diagonal form. -/
theorem map_diag {k : ℕ} (a : Fin k → ℤ) :
    (QuadForm.diag a).map (Int.castRingHom ℤ_[2]) = QuadForm.diag fun i => (a i : ℤ_[2]) := by
  ext i j
  simp [QuadForm.diag, QuadForm.map, Matrix.diagonal_apply, apply_ite]

/-- **Two orthogonal values give a binary diagonal representation.** -/
theorem rep2_diag_two {G : QuadForm ℤ_[2] N} {a c : ℤ_[2]} (x y : Fin N → ℤ_[2]) (hx : G.eval x = a)
    (hy : G.eval y = c) (hxy : x ⬝ᵥ (G.hessian *ᵥ y) = 0) : Rep2 G (QuadForm.diag ![a, c]) := by
  have h := rep2_orthSum (G := G) (A := QuadForm.diag ![a]) (B := QuadForm.diag ![c]) (Matrix.of fun r _ => x r)
    (Matrix.of fun r _ => y r) ?_ ?_ ?_
  · refine h.congr fun z => ?_
    show (QuadForm.orthSum _ _).evalIn ℤ_[2] z = _
    rw [QuadForm.evalIn_orthSum]
    show (QuadForm.diag ![a]).eval _ + (QuadForm.diag ![c]).eval _ = _
    rw [eval_diag', eval_diag', eval_diag', Fin.sum_univ_two]
    simp
  · intro z
    have : (Matrix.of fun r (_ : Fin 1) => x r) *ᵥ z = z 0 • x := by ext r; simp [mulVec, dotProduct, mul_comm]
    rw [this, eval_smul_sq, hx, eval_diag']; simp [mul_comm]
  · intro z
    have : (Matrix.of fun r (_ : Fin 1) => y r) *ᵥ z = z 0 • y := by ext r; simp [mulVec, dotProduct, mul_comm]
    rw [this, eval_smul_sq, hy, eval_diag']; simp [mul_comm]
  · intro z w
    have h1 : (Matrix.of fun r (_ : Fin 1) => x r) *ᵥ z = z 0 • x := by ext r; simp [mulVec, dotProduct, mul_comm]
    have h2 : (Matrix.of fun r (_ : Fin 1) => y r) *ᵥ w = w 0 • y := by ext r; simp [mulVec, dotProduct, mul_comm]
    rw [h1, h2, mulVec_smul, dotProduct_smul, smul_dotProduct, hxy]; simp

end QuadFormsKB.Watson1963
