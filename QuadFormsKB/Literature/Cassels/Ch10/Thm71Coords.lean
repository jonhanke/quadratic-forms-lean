/-
# Cassels, Chapter 10, Theorem 7.1: coordinates and the integral model of the form

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, proof of Theorem 7.1 for $n \ge 4$ (p. 189: "We
denote by $f$ the form induced by $\phi$ on $\Lambda$ and its determinant will be $d$").

**Setting.** $V$ a finite-dimensional $\mathbb Q$-vector space with a quadratic form $Q$ and a basis $e_0, \dots, e_{n-1}$; for a
field $K \supseteq \mathbb Q$ the vectors $1 \otimes e_i$ form a basis of $V_K = K \otimes V$. The Gram matrix is
$G_{ij} = B(e_i, e_j)$ ($B$ the polar form with $B(x, x) = Q(x)$, Mathlib's `QuadraticMap.associated`).

**Proves.**
* `eq_dotProduct_gram`: $Q(x) = \xi^{\mathsf T}G\xi$ for the coordinates $\xi$ of $x$ in a basis; `gram_baseChange`: the Gram
  matrix of $1 \otimes e_i$ is the image of $G$;
* `evalIn_ofMatrixZ`: for a symmetric integer matrix $N$, the integral form `LocalDensity.ofMatrixZ N` is
  $\xi \mapsto \xi^{\mathsf T}N\xi$ over every field of characteristic $0$; `det_hessian_ofMatrixZ`: its Hessian determinant is
  $2^n\det N$;
* `exists_pos_neg_of_isotropic`: a regular real symmetric matrix with a nonzero isotropic vector takes both signs
  (Cassels: $V$ indefinite).
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Ternary
import QuadFormsKB.LocalDensity.JordanForm
import QuadFormsKB.Siegel.NeighborGenus

open CliffordAlgebra TensorProduct Module Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Coords

open QuadFormsKB.Cassels QuadFormsKB.Cassels.Thm71Ternary

section Gram

variable {K W : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup W] [Module K W] {n : ℕ}

/-- **The Gram matrix** $G_{ij} = B(e_i, e_j)$ of vectors $e_0, \dots, e_{n-1}$ (polar form with $B(x, x) = Q(x)$).
Arguments: `Q` the form, `e` the vectors. -/
noncomputable def gram (Q : QuadraticForm K W) (e : Fin n → W) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => QuadraticMap.associated Q (e i) (e j)

/-- $Q(x) = \xi^{\mathsf T}G\xi$ for the coordinates $\xi$ of $x$ in the basis $b$. -/
theorem eq_dotProduct_gram (Q : QuadraticForm K W) (b : Basis (Fin n) K W) (x : W) :
    Q x = b.equivFun x ⬝ᵥ gram Q b *ᵥ b.equivFun x := by
  rw [← QuadraticMap.associated_eq_self_apply K Q x]
  conv_lhs => rw [← b.sum_equivFun x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec,
    gram, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change b.equivFun x j * (b.equivFun x i * (QuadraticMap.associated Q (b i) (b j))) = _
  ring

/-- The Gram matrix is symmetric. -/
theorem gram_transpose (Q : QuadraticForm K W) (e : Fin n → W) : (gram Q e)ᵀ = gram Q e := by
  ext i j
  simp only [gram, transpose_apply, of_apply]
  exact QuadraticMap.associated_isSymm K Q (e j) (e i)

/-- The Gram matrix of a basis of a regular space is invertible. -/
theorem det_gram_ne_zero {Q : QuadraticForm K W} (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (b : Basis (Fin n) K W) : (gram Q b).det ≠ 0 := by
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hQ
  have e : LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q) = gram Q b := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rwa [e] at h

end Gram

/-- The Gram matrix of the vectors $1 \otimes e_i$ of $V_L$ is the image of the Gram matrix of $e$. -/
theorem gram_baseChange {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V] {n : ℕ}
    (L : Type*) [Field L] [Algebra k L] [Invertible (2 : L)] (Q : QuadraticForm k V) (e : Fin n → V) :
    gram (Q.baseChange L) (fun i => (1 : L) ⊗ₜ[k] e i) = (gram Q e).map (algebraMap k L) := by
  ext i j
  exact associated_baseChange_one_tmul L Q (e i) (e j)

section IntModel

variable {n : ℕ}

/-- Helper: the Hessian of `ofMatrixZ N` is $N + N^{\mathsf T}$. -/
theorem hessian_ofMatrixZ (N : Matrix (Fin n) (Fin n) ℤ) : (LocalDensity.ofMatrixZ N).hessian = N + Nᵀ := by
  ext i j
  simp only [QuadForm.hessian, LocalDensity.ofMatrixZ, Matrix.add_apply, transpose_apply, of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne']
  · simp
  · simp [h, not_lt.mpr h.le, h.ne']; ring

/-- **The integral form of a symmetric integer matrix**: `ofMatrixZ N` is $\xi \mapsto \xi^{\mathsf T}N\xi$ over every field of
characteristic $0$. Arguments: `N`, `hs` symmetry, `x`. -/
theorem evalIn_ofMatrixZ {K : Type*} [Field K] [CharZero K] (N : Matrix (Fin n) (Fin n) ℤ) (hs : Nᵀ = N)
    (x : Fin n → K) : (LocalDensity.ofMatrixZ N).evalIn K x = x ⬝ᵥ (N.map (Int.cast : ℤ → K)) *ᵥ x := by
  have h := Siegel.Kneser.two_mul_evalIn (K := K) (LocalDensity.ofMatrixZ N) x
  rw [hessian_ofMatrixZ, hs] at h
  have h2 : (N + N).map (algebraMap ℤ K) = (2 : K) • N.map (Int.cast : ℤ → K) := by
    ext i j; simp [two_mul]
  rw [h2, smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  exact mul_left_cancel₀ two_ne_zero h

/-- The Hessian determinant of `ofMatrixZ N` for symmetric `N` is $2^n\det N$. -/
theorem det_hessian_ofMatrixZ (N : Matrix (Fin n) (Fin n) ℤ) (hs : Nᵀ = N) :
    (LocalDensity.ofMatrixZ N).hessian.det = 2 ^ n * N.det := by
  rw [hessian_ofMatrixZ, hs, ← two_smul ℤ N, det_smul, Fintype.card_fin]

end IntModel

section Real

variable {n : ℕ}

/-- **A regular real symmetric matrix with a nonzero isotropic vector takes both signs** (Cassels, p. 188: an indefinite
space). Arguments: `G`, `hG` symmetry, `hdet`, `w`, `hw`, `hiso`. -/
theorem exists_pos_neg_of_isotropic {G : Matrix (Fin n) (Fin n) ℝ} (hG : Gᵀ = G) (hdet : G.det ≠ 0)
    {w : Fin n → ℝ} (hw : w ≠ 0) (hiso : w ⬝ᵥ G *ᵥ w = 0) :
    ∃ x y : Fin n → ℝ, x ⬝ᵥ G *ᵥ x < 0 ∧ 0 < y ⬝ᵥ G *ᵥ y := by
  obtain ⟨y, hy⟩ : ∃ y, y = G *ᵥ w := ⟨_, rfl⟩
  have hy0 : y ≠ 0 := fun h => hw (Matrix.eq_zero_of_mulVec_eq_zero hdet (hy ▸ h))
  obtain ⟨s, hs⟩ : ∃ s, s = y ⬝ᵥ y := ⟨_, rfl⟩
  have hspos : 0 < s := by
    have h0 : 0 ≤ s := hs ▸ Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
    exact lt_of_le_of_ne h0 fun h => hy0 (dotProduct_self_eq_zero.mp (hs ▸ h.symm))
  have hsym : ∀ a b : Fin n → ℝ, a ⬝ᵥ G *ᵥ b = b ⬝ᵥ G *ᵥ a := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]
  have hwy : w ⬝ᵥ G *ᵥ y = s := by rw [hsym, hs, hy]
  obtain ⟨c, hc⟩ : ∃ c, c = y ⬝ᵥ G *ᵥ y := ⟨_, rfl⟩
  have hquad : ∀ t : ℝ, (w + t • y) ⬝ᵥ G *ᵥ (w + t • y) = t * (2 * s + t * c) := by
    intro t
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hiso, hwy, ← hc]
    rw [hsym y w, hwy]
    ring
  set ε := s / (|c| + 1) with hε
  have hεpos : 0 < ε := div_pos hspos (by positivity)
  have hεc : |ε * c| < s := by
    rw [abs_mul, abs_of_pos hεpos, hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg c]
  refine ⟨w + (-ε) • y, w + ε • y, ?_, ?_⟩
  · rw [hquad]
    have : -s < -ε * c := by have := le_abs_self (ε * c); linarith
    have h1 : 0 < 2 * s + -ε * c := by linarith
    nlinarith
  · rw [hquad]
    have : -s < ε * c := by have := neg_abs_le (ε * c); linarith
    have h1 : 0 < 2 * s + ε * c := by linarith
    exact mul_pos hεpos h1

end Real

end QuadFormsKB.Cassels.Thm71Coords
