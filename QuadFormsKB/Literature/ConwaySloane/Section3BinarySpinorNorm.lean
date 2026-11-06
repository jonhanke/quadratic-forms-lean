/-
# The spinor norm of a rotation of a binary quadratic space

Helper for the Estes–Pall theorem (Conway–Sloane, Ch. 15, §3.5, p. 366; `Section3EstesPallIf.lean`).

**Statement.** Let $V = K^2$ with a nondegenerate quadratic form $Q$ (bilinear form $B(x, y) = x^{\mathsf T}Hy$,
$H$ = `Q.hessian`, so $B(x, x) = 2Q(x)$), and let $\sigma \in O^+(V)$ be a rotation. If $x, y \in V$ are anisotropic
with $B(x, y) = 0$ and $u = \sigma x - x$ is anisotropic, then
$$\sigma = \tau_u\,\tau_y, \qquad \theta(\sigma) = Q(\sigma x - x)\,Q(y)\,K^{\times 2}.$$

**Proof.** $\tau_u(\sigma x) = x$ (because $B(u, \sigma x) = Q(u)$), so $\rho = \tau_u\sigma$ fixes $x$ and has
determinant $-1$. The vector $z = \rho y$ is orthogonal to $x$ and $\det[x \mid z] = \det\rho\,\det[x \mid y] =
-\det[x \mid y]$; since the vectors orthogonal to the anisotropic $x$ form a line, $z = -y$. Thus $\rho$ and $\tau_y$
agree on the basis $x, y$ of $V$ (`binary_rotation_eq_symm_mul_symm`); the spinor norm follows from
`spinorNorm_symmProd` (O'Meara 1963, §55, p. 137).

**Proves:** `binary_rotation_eq_symm_mul_symm`, `binary_spinorNorm_eq`.
-/
import QuadFormsKB.Lattices.SpinorNorm
import QuadFormsKB.Tamagawa.LocalVolume

open NumberField Matrix

noncomputable section

namespace QuadFormsKB.ConwaySloane.EstesPall

open QuadFormsKB.Lattices

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] (Q : QuadForm F 2) (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- Two vectors of $K^2$ orthogonal to the same vector $h$ with $x \cdot h \ne 0$ and $\det[x \mid v] = 0$ vanish:
the $2 \times 2$ system $\det[x \mid v] = 0$, $v \cdot h = 0$ has determinant $-(x \cdot h) \ne 0$. -/
theorem eq_zero_of_det_of_dot {x h v : Fin 2 → K} (hxh : x 0 * h 0 + x 1 * h 1 ≠ 0)
    (hdet : x 0 * v 1 - x 1 * v 0 = 0) (hdot : v 0 * h 0 + v 1 * h 1 = 0) : v = 0 := by
  have h0 : v 0 * (x 0 * h 0 + x 1 * h 1) = 0 := by linear_combination x 0 * hdot - h 1 * hdet
  have h1 : v 1 * (x 0 * h 0 + x 1 * h 1) = 0 := by linear_combination x 1 * hdot + h 0 * hdet
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_right hxh
  · exact (mul_eq_zero.mp h1).resolve_right hxh

/-- The matrix with columns $x$ and $y$. -/
def colMat (x y : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K := !![x 0, y 0; x 1, y 1]

theorem mul_colMat (A : Matrix (Fin 2) (Fin 2) K) (x y : Fin 2 → K) :
    A * colMat K x y = colMat K (A *ᵥ x) (A *ᵥ y) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det_colMat (x y : Fin 2 → K) : (colMat K x y).det = x 0 * y 1 - y 0 * x 1 := by
  simp [colMat, Matrix.det_fin_two]

/-- Two matrices agreeing on the columns of an invertible `colMat` are equal. -/
theorem eq_of_colMat {A A' : Matrix (Fin 2) (Fin 2) K} {x y : Fin 2 → K} (hd : (colMat K x y).det ≠ 0)
    (hx : A *ᵥ x = A' *ᵥ x) (hy : A *ᵥ y = A' *ᵥ y) : A = A' := by
  have h : A * colMat K x y = A' * colMat K x y := by rw [mul_colMat, mul_colMat, hx, hy]
  have hu : IsUnit (colMat K x y) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  exact hu.mul_right_cancel h

local notation "H" => Q.hessian.map (algebraMap F K)

theorem bil_symm (x y : Fin 2 → K) : x ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ← Matrix.transpose_map, QuadForm.hessian_transpose, dotProduct_comm]

/-- **A rotation of a binary space is a product of two symmetries**: $\sigma = \tau_{\sigma x - x}\,\tau_y$ for
anisotropic $x, y$ with $B(x, y) = 0$ and $\sigma x - x$ anisotropic. -/
theorem binary_rotation_eq_symm_mul_symm (σ : orthGroup Q K) (hσ : (σ : GL (Fin 2) K).val.det = 1)
    {x y : Fin 2 → K} (hx : Q.evalIn K x ≠ 0) (hy : Q.evalIn K y ≠ 0) (hxy : x ⬝ᵥ (H *ᵥ y) = 0)
    (hu : Q.evalIn K ((σ : GL (Fin 2) K).val *ᵥ x - x) ≠ 0) :
    σ = symm Q K ((σ : GL (Fin 2) K).val *ᵥ x - x) * symm Q K y := by
  set S := (σ : GL (Fin 2) K).val with hS
  set u := S *ᵥ x - x with hudef
  have hσo : (σ : GL (Fin 2) K) ∈ orthGroup Q K := σ.2
  -- `B(u, σx) = Q(u)`
  have hQσx : Q.evalIn K (S *ᵥ x) = Q.evalIn K x := evalIn_mulVec_of_mem Q hσo x
  have h2u := two_mul_evalIn Q u
  have h2x := two_mul_evalIn Q x
  have h2σx := two_mul_evalIn Q (S *ᵥ x)
  have hBu : u ⬝ᵥ (H *ᵥ (S *ᵥ x)) = Q.evalIn K u := by
    have hsym := bil_symm Q K x (S *ᵥ x)
    rw [hudef] at h2u ⊢
    rw [sub_dotProduct] at h2u ⊢
    rw [mulVec_sub, dotProduct_sub, dotProduct_sub] at h2u
    rw [hQσx] at h2σx
    linear_combination (-1/2 : K) * h2u - (1/2 : K) * hsym - (1/2 : K) * h2σx + (1/2 : K) * h2x
  -- `ρ = τ_u σ` fixes `x`
  set ρ : orthGroup Q K := symm Q K u * σ with hρ
  have hρx : (ρ : GL (Fin 2) K).val *ᵥ x = x := by
    rw [hρ]
    change ((symm Q K u : GL (Fin 2) K).val * S) *ᵥ x = x
    rw [← mulVec_mulVec, symm_mulVec Q K hu, hBu, inv_mul_cancel₀ hu, one_smul, hudef]
    abel
  have hρdet : (ρ : GL (Fin 2) K).val.det = -1 := by
    rw [hρ]
    change ((symm Q K u : GL (Fin 2) K).val * S).det = -1
    rw [det_mul, symm_det Q K hu, hσ, mul_one]
  -- `ρ y = -y`
  set z := (ρ : GL (Fin 2) K).val *ᵥ y with hz
  have hzx : z ⬝ᵥ (H *ᵥ x) = 0 := by
    have := bilin_orth Q K ρ y x
    rw [hρx] at this
    rw [hz, this, bil_symm Q K y x, hxy]
  set h := H *ᵥ x with hh
  have hxh : x 0 * h 0 + x 1 * h 1 ≠ 0 := by
    intro h0
    apply hx
    have : x ⬝ᵥ h = 0 := by simpa [dotProduct, Fin.sum_univ_two] using h0
    have h2 : 2 * Q.evalIn K x = 0 := by rw [h2x]; exact this
    simpa using h2
  have hyh : y 0 * h 0 + y 1 * h 1 = 0 := by
    have : y ⬝ᵥ h = 0 := by rw [hh, ← bil_symm Q K x y, hxy]
    simpa [dotProduct, Fin.sum_univ_two] using this
  have hzh : z 0 * h 0 + z 1 * h 1 = 0 := by simpa [dotProduct, Fin.sum_univ_two] using hzx
  have hdetz : (colMat K x z).det = -(colMat K x y).det := by
    have := congrArg Matrix.det (mul_colMat K (ρ : GL (Fin 2) K).val x y)
    rw [det_mul, hρdet, hρx] at this
    rw [← this]; ring
  have hzy : z = -y := by
    have hv := eq_zero_of_det_of_dot K (v := z + y) hxh
      (by rw [det_colMat, det_colMat] at hdetz; simp only [Pi.add_apply]; linear_combination hdetz)
      (by simp only [Pi.add_apply]; linear_combination hzh + hyh)
    exact eq_neg_of_add_eq_zero_left hv
  -- `x, y` is a basis
  have hy0 : y ≠ 0 := by rintro rfl; exact hy (by simp [QuadForm.evalIn_eq_dotProduct])
  have hdxy : (colMat K x y).det ≠ 0 := by
    intro hd
    apply hy0
    exact eq_zero_of_det_of_dot K hxh (by rw [det_colMat] at hd; linear_combination hd) hyh
  -- `τ_y` on `x` and `y`
  have hτx : (symm Q K y : GL (Fin 2) K).val *ᵥ x = x := by
    rw [symm_mulVec Q K hy, ← bil_symm Q K x y, hxy, mul_zero, zero_smul, sub_zero]
  have hτy : (symm Q K y : GL (Fin 2) K).val *ᵥ y = -y := by
    rw [symm_mulVec Q K hy, ← two_mul_evalIn, ← mul_assoc, mul_comm _ (2 : K), mul_assoc,
      inv_mul_cancel₀ hy, mul_one, two_smul]
    abel
  have hρτ : ρ = symm Q K y := by
    refine Subtype.ext (Units.ext (eq_of_colMat K hdxy ?_ ?_))
    · rw [hρx, hτx]
    · rw [← hz, hzy, hτy]
  calc σ = symm Q K u * ρ := by rw [hρ, ← mul_assoc, symm_mul_self, one_mul]
    _ = symm Q K u * symm Q K y := by rw [hρτ]

/-- **The spinor norm of a binary rotation** (O'Meara 1963, §55, p. 137): $\theta(\sigma) = Q(\sigma x - x)\,Q(y)\,
K^{\times 2}$ for anisotropic $x, y$ with $B(x, y) = 0$ and $\sigma x - x$ anisotropic. -/
@[kb "omeara1963" "§55, p. 137 (spinor norm of a binary rotation σ = τ_{σx−x} τ_y)"]
theorem binary_spinorNorm_eq (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (hσ : (σ : GL (Fin 2) K).val.det = 1)
    {x y : Fin 2 → K} (hx : Q.evalIn K x ≠ 0) (hy : Q.evalIn K y ≠ 0) (hxy : x ⬝ᵥ (H *ᵥ y) = 0)
    (hu : Q.evalIn K ((σ : GL (Fin 2) K).val *ᵥ x - x) ≠ 0) :
    spinorNorm Q K σ = sqClassOf (Q.evalIn K ((σ : GL (Fin 2) K).val *ᵥ x - x) * Q.evalIn K y) := by
  have e := binary_rotation_eq_symm_mul_symm Q K σ hσ hx hy hxy hu
  have hl : symmProd Q K [(σ : GL (Fin 2) K).val *ᵥ x - x, y] =
      symm Q K ((σ : GL (Fin 2) K).val *ᵥ x - x) * symm Q K y := by
    simp [symmProd]
  have h := spinorNorm_symmProd Q K hQ [(σ : GL (Fin 2) K).val *ᵥ x - x, y] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    exacts [hu, hy])
  rw [hl, ← e] at h
  rw [h]
  simp [valProd]

end QuadFormsKB.ConwaySloane.EstesPall
