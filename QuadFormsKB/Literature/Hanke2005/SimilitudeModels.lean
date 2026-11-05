/-
# Hanke 2005, §6: similitudes of the local models (any field of characteristic ≠ 2)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Explicit similitudes of the pieces of the normal form (2.9), p. 6, used in the proof of Theorem 6.3, p. 21:
$\mathbb H^m$ has similitudes of every multiplier (`hyperbolicSpace_similitude`); a binary diagonal form
$\langle a_0,a_1\rangle$ has a similitude of multiplier $\langle a_0,a_1\rangle(y)/a_0$ for every $y$ (multiplication by
$y_0 + y_1\sqrt{-a_1/a_0}$, `wss_two_similitude`); a quaternary diagonal form of square determinant has a similitude of
multiplier $\langle a\rangle(y)/a_0$ for every $y$ (left multiplication in a quaternion algebra, `wss_four_similitude`);
similitudes of the same multiplier add over orthogonal sums (`prod_similitude`), and a similitude of a form equivalent to
$Q$ gives a multiplier of the Gram matrix of $Q$ (`mem_multipliers_of_equivalent`).
-/
import QuadFormsKB.Literature.Hanke2005.Similitudes
import QuadFormsKB.Literature.Hanke2005.MaximalSimilitude
import QuadFormsKB.Witt.Bridge

open Module QuadraticMap QuadraticForm Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

section Generic

variable {K : Type*} [Field K] {n : ℕ}

/-- Universe-polymorphic copy of `sim_of_eval`. -/
theorem sim_of_eval' {m : ℕ} (Q : QuadForm K m) (A : Matrix (Fin m) (Fin m) K) (ξ : K)
    (h : ∀ z, Q.eval (A *ᵥ z) = ξ * Q.eval z) : Aᵀ * Q.hessian * A = ξ • Q.hessian := by
  have single_dot : ∀ (M : Matrix (Fin m) (Fin m) K) (i j : Fin m),
      (Pi.single i (1 : K) : Fin m → K) ⬝ᵥ (M *ᵥ (Pi.single j (1 : K) : Fin m → K)) = M i j := by
    intro M i j
    simp [mulVec, dotProduct, Pi.single_apply]
  ext i j
  have hp := QuadForm.polar_eq_hessian K Q (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single j 1)
  have hp' := QuadForm.polar_eq_hessian K Q (Pi.single i 1) (Pi.single j 1)
  rw [← mulVec_add] at hp
  simp only [QuadForm.eval] at h
  rw [h, h, h] at hp
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at hp hp'
  rw [Matrix.smul_apply, smul_eq_mul, ← single_dot (Aᵀ * Q.hessian * A) i j,
    ← single_dot Q.hessian i j, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]
  linear_combination (-1 : K) * hp + ξ * hp'

/-- A matrix with unit determinant gives a linear equivalence acting by `mulVec`. -/
theorem exists_equiv_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) K) (hM : IsUnit M.det) :
    ∃ σ : (Fin k → K) ≃ₗ[K] (Fin k → K), ∀ x, σ x = M *ᵥ x := by
  letI := Matrix.invertibleOfIsUnitDet M hM
  exact ⟨M.toLinearEquiv' this, fun x => rfl⟩

/-- The norm form of the quaternion algebra with $i^2=-\alpha$, $j^2=-\beta$. -/
def quatN (α β : K) (v : Fin 4 → K) : K := v 0 ^ 2 + α * v 1 ^ 2 + β * v 2 ^ 2 + α * β * v 3 ^ 2

/-- Left multiplication by a quaternion. -/
def quatL (α β : K) (q : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![q 0, -α * q 1, -β * q 2, -α * β * q 3; q 1, q 0, -β * q 3, β * q 2;
    q 2, α * q 3, q 0, -α * q 1; q 3, -q 2, q 1, q 0]

theorem quatN_mulVec (α β : K) (q x : Fin 4 → K) :
    quatN α β (quatL α β q *ᵥ x) = quatN α β q * quatN α β x := by
  simp [quatN, quatL, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem quatL_mul_conj (α β : K) (hα : α ≠ 0) (hβ : β ≠ 0) (q : Fin 4 → K) (hN : quatN α β q ≠ 0) :
    quatL α β q * ((quatN α β q)⁻¹ • quatL α β ![q 0, -q 1, -q 2, -q 3]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatL, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> (try simp only [quatN]) <;> ring

theorem wss_four_eq (a : Fin 4 → K) (α β r : K) (h1 : a 1 = a 0 * α) (h2 : a 2 = a 0 * β)
    (h3 : a 3 = a 0 * (α * β * r ^ 2)) (x : Fin 4 → K) :
    weightedSumSquares K a x =
      a 0 * quatN α β (Matrix.diagonal ![1, 1, 1, r] *ᵥ x) := by
  simp [weightedSumSquares_apply, Fin.sum_univ_four, quatN, Matrix.mulVec_diagonal, h1, h2, h3]
  ring

/-- **A similitude of a form equivalent to $Q$ gives a multiplier of the Gram matrix $\tfrac12H_Q$.** -/
theorem mem_multipliers_of_equivalent {V : Type*} [AddCommGroup V] [Module K V] (h2 : (2 : K) ≠ 0)
    (Q : QuadForm K n) {T : QuadraticForm K V} (e : Q.toQuadraticForm.Equivalent T) (σ : V ≃ₗ[K] V) {ξ : K}
    (hξ : ξ ≠ 0) (hσ : ∀ x, T (σ x) = ξ * T x) : ξ ∈ multipliers ((1 / 2 : K) • Q.hessian) := by
  obtain ⟨e⟩ := e
  let τ : (Fin n → K) ≃ₗ[K] (Fin n → K) := e.toLinearEquiv ≪≫ₗ σ ≪≫ₗ e.toLinearEquiv.symm
  have hτ : ∀ z, Q.eval (τ z) = ξ * Q.eval z := by
    intro z
    have h1 : ∀ w, T (e.toLinearEquiv w) = Q.eval w := fun w => by
      rw [← QuadForm.toQuadraticForm_apply]; exact e.map_app w
    rw [← h1, ← h1]
    simp only [τ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact hσ _
  have hg : ∀ z, LinearMap.toMatrix' τ.toLinearMap *ᵥ z = τ z := fun z => by
    simp
  have key := sim_of_eval' Q (LinearMap.toMatrix' τ.toLinearMap) ξ (fun z => by rw [hg]; exact hτ z)
  refine ⟨hξ, LinearMap.toMatrix' τ.toLinearMap, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' τ
  · rw [Matrix.mul_smul, Matrix.smul_mul, key, smul_comm]

/-- **$\mathbb H^m$ has similitudes of every multiplier** ($(x_i, y_i)\mapsto(\xi x_i, y_i)$). -/
theorem hyperbolicSpace_similitude (m : ℕ) {ξ : K} (hξ : ξ ≠ 0) :
    ∃ σ : (Fin m → K × K) ≃ₗ[K] (Fin m → K × K), ∀ x, hyperbolicSpace K m (σ x) = ξ * hyperbolicSpace K m x := by
  refine ⟨LinearEquiv.piCongrRight fun _ =>
    LinearEquiv.prodCongr (LinearEquiv.smulOfNeZero K K ξ hξ) (LinearEquiv.refl K K), fun x => ?_⟩
  simp [hyperbolicSpace_apply, Finset.mul_sum, mul_assoc]

/-- **Similitudes of the same multiplier add over orthogonal sums.** -/
theorem prod_similitude {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {Q₁ : QuadraticForm K V} {Q₂ : QuadraticForm K W} {ξ : K} (σ₁ : V ≃ₗ[K] V) (σ₂ : W ≃ₗ[K] W)
    (h₁ : ∀ x, Q₁ (σ₁ x) = ξ * Q₁ x) (h₂ : ∀ x, Q₂ (σ₂ x) = ξ * Q₂ x) :
    ∃ σ : (V × W) ≃ₗ[K] (V × W), ∀ x, (Q₁.prod Q₂) (σ x) = ξ * (Q₁.prod Q₂) x := by
  refine ⟨σ₁.prodCongr σ₂, fun x => ?_⟩
  simp [QuadraticMap.prod_apply, h₁, h₂, mul_add]

/-- **Binary diagonal forms:** $\langle a_0,a_1\rangle$ has a similitude of multiplier $\langle a_0,a_1\rangle(y)/a_0$
(multiplication by $y_0 + y_1\sqrt{-a_1/a_0}$; matrix $\begin{pmatrix}y_0&-(a_1/a_0)y_1\\y_1&y_0\end{pmatrix}$). -/
theorem wss_two_similitude (a : Fin 2 → K) (ha : ∀ i, a i ≠ 0) (y : Fin 2 → K)
    (hy : weightedSumSquares K a y ≠ 0) :
    ∃ σ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K), ∀ x,
      weightedSumSquares K a (σ x) = (weightedSumSquares K a y / a 0) * weightedSumSquares K a x := by
  have hw : ∀ z : Fin 2 → K, weightedSumSquares K a z = a 0 * z 0 ^ 2 + a 1 * z 1 ^ 2 := fun z => by
    simp [weightedSumSquares_apply, Fin.sum_univ_two]
    ring
  have h0 := ha 0
  set c := a 1 / a 0 with hc
  have hξ : weightedSumSquares K a y / a 0 = y 0 ^ 2 + c * y 1 ^ 2 := by
    rw [hw]; rw [hc]; field_simp
  have hξ0 : y 0 ^ 2 + c * y 1 ^ 2 ≠ 0 := by
    rw [← hξ]; exact div_ne_zero hy h0
  have hMN : !![y 0, -c * y 1; y 1, y 0] * ((y 0 ^ 2 + c * y 1 ^ 2)⁻¹ • !![y 0, c * y 1; -y 1, y 0]) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination mul_inv_cancel₀ hξ0 | (field_simp; ring)
  obtain ⟨σ, hσ⟩ := exists_equiv_mulVec _ (Matrix.isUnit_det_of_right_inverse hMN)
  refine ⟨σ, fun x => ?_⟩
  rw [hξ, hw, hw, hσ]
  have ha1 : a 1 = c * a 0 := by rw [hc]; field_simp
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha1]
  ring

/-- **Quaternary diagonal forms of square determinant:** $\langle a_0,\dots,a_3\rangle$ with $a_0a_1a_2a_3$ a square is
$a_0$ times the norm form of a quaternion algebra (after rescaling $x_3$), so it has a similitude of multiplier
$\langle a\rangle(y)/a_0$ (left multiplication by a quaternion of norm $\langle a\rangle(y)/a_0$). -/
theorem wss_four_similitude (a : Fin 4 → K) (ha : ∀ i, a i ≠ 0) (hsq : IsSquare (a 0 * a 1 * a 2 * a 3))
    (y : Fin 4 → K) (hy : weightedSumSquares K a y ≠ 0) :
    ∃ σ : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K), ∀ x,
      weightedSumSquares K a (σ x) = (weightedSumSquares K a y / a 0) * weightedSumSquares K a x := by
  obtain ⟨s, hs⟩ := hsq
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  set α := a 1 / a 0 with hα
  set β := a 2 / a 0 with hβ
  set r := s / (a 1 * a 2) with hr
  have e1 : a 1 = a 0 * α := by rw [hα]; field_simp
  have e2 : a 2 = a 0 * β := by rw [hβ]; field_simp
  have e3 : a 3 = a 0 * (α * β * r ^ 2) := by
    rw [hα, hβ, hr]
    field_simp
    linear_combination (1 : K) * hs
  have hr0 : r ≠ 0 := by
    intro h
    have : s = 0 := by
      rw [hr, div_eq_zero_iff] at h
      rcases h with h | h
      · exact h
      · exact absurd h (mul_ne_zero h1 h2)
    rw [this] at hs
    simp [h0, h1, h2, h3] at hs
  set S : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, 1, 1, r] with hS
  have hSdet : IsUnit S.det := by
    simp [hS, Matrix.det_diagonal, Fin.prod_univ_four, hr0]
  have hw : ∀ x, weightedSumSquares K a x = a 0 * quatN α β (S *ᵥ x) := wss_four_eq a α β r e1 e2 e3
  have hNq : quatN α β (S *ᵥ y) ≠ 0 := by
    intro h
    apply hy
    rw [hw, h, mul_zero]
  have hα0 : α ≠ 0 := div_ne_zero h1 h0
  have hβ0 : β ≠ 0 := div_ne_zero h2 h0
  obtain ⟨eS, heS⟩ := exists_equiv_mulVec S hSdet
  obtain ⟨eL, heL⟩ := exists_equiv_mulVec (quatL α β (S *ᵥ y))
    (Matrix.isUnit_det_of_right_inverse (quatL_mul_conj α β hα0 hβ0 _ hNq))
  refine ⟨eS ≪≫ₗ eL ≪≫ₗ eS.symm, fun x => ?_⟩
  have hSσ : S *ᵥ ((eS ≪≫ₗ eL ≪≫ₗ eS.symm) x) = quatL α β (S *ᵥ y) *ᵥ (S *ᵥ x) := by
    rw [← heS, ← heL, ← heS]
    simp
  rw [hw ((eS ≪≫ₗ eL ≪≫ₗ eS.symm) x), hSσ, quatN_mulVec, hw y, hw x]
  field_simp

end Generic

end QuadFormsKB.Hanke2005
