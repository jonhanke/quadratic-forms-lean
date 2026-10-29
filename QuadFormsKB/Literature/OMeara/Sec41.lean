import QuadFormsKB.Literature.OMeara.Sec82

/-!
# O'Meara §41: representations, matrices and discriminants of quadratic spaces (41:1–41:4)

**Setting** (as in `Sec82.lean` and `Sec43CD.lean`): $F$ a field with $2 \ne 0$ (`[Invertible (2 : F)]`),
$(V, Q)$ and $(W, Q')$ quadratic spaces over $F$ (Mathlib `QuadraticForm F V`), O'Meara's symmetric bilinear form
$B$ = `bil Q` (so $B(x,x) = Q(x)$), and the matrix $(B(x_i, x_j))$ of a family of vectors = `gram Q x`.
A *representation* of $V$ into $W$ is a linear map $\sigma$ with $Q'(\sigma x) = Q(x)$ for all $x$.

**Proves** (O'Meara 1973 printing, Chapter IV, §41, pp. 84–87):
* `rep_of_bil_basis` (**41:1**): a linear map that preserves $B$ on a base is a representation;
* `exists_rep_iff_gram` and `exists_isometry_iff_gram` (**41:2**): $U$ is represented by (resp. isometric to) $V$
  iff $M = T^{\mathsf t} N T$ for a matrix (resp. an invertible matrix) $T$, where $M$, $N$ are the matrices of $U$,
  $V$ in given bases;
* `det_gram_smul` (**41:3**, the discriminant part): $d(V^a) = a^{n} dV$ (the matrix part $V^a \cong aN$ is
  `gram_smul` of `Sec92Class.lean`, and **41:4** is `linearIndependent_of_det_gram_ne_zero` of `Sec91Jordan.lean`;
  both are cited in `CitationsIV.lean`).

**Conventions.** Indices are 0-based (`Fin n`); O'Meara's $x_1, \dots, x_n$ are `b 0, …, b (n-1)`. The matrix of a
space is O'Meara's Gram matrix of $B$ (not the Hessian matrix $2B$). The scaled space $V^a$ is `a • Q`.
-/

open QuadraticMap Submodule Module LinearMap
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec41

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
variable {W : Type*} [AddCommGroup W] [Module F W] (Q' : QuadraticForm F W)

/-- The matrix of $V$ in a base $b$ is the matrix of the bilinear form `associated Q` (Mathlib's `toMatrix₂`). -/
theorem gram_eq_toMatrix₂ {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι F V) :
    gram Q b = LinearMap.toMatrix₂ b b (QuadraticMap.associated Q) := by
  ext i j; simp [gram, LinearMap.toMatrix₂_apply]

/-- **O'Meara 41:1** (p. 84). Let $\sigma : V \to W$ be linear and $x_1, \dots, x_n$ a base of $V$ with
$B(\sigma x_i, \sigma x_j) = B(x_i, x_j)$ for all $i, j$. Then $\sigma$ is a representation:
$Q'(\sigma x) = Q(x)$ for every $\vec{x} \in V$. -/
@[kb "omeara1963" "§41A, 41:1, p. 84"]
theorem rep_of_bil_basis {ι : Type*} (b : Basis ι F V) (σ : V →ₗ[F] W)
    (h : ∀ i j, bil Q' (σ (b i)) (σ (b j)) = bil Q (b i) (b j)) (x : V) : Q' (σ x) = Q x := by
  have hB : (QuadraticMap.associated Q').compl₁₂ σ σ = QuadraticMap.associated Q :=
    LinearMap.BilinForm.ext_basis b fun i j => h i j
  have := congrArg (fun B : LinearMap.BilinForm F V => B x x) hB
  simp only [LinearMap.compl₁₂_apply] at this
  rw [← bil_self Q' (σ x), ← bil_self Q x]
  exact this

/-- A linear map is a representation iff it preserves $B$ (the identity before 41:1, p. 84). -/
theorem rep_iff_compl₁₂ (σ : V →ₗ[F] W) :
    (∀ x, Q' (σ x) = Q x) ↔
      (QuadraticMap.associated Q').compl₁₂ σ σ = QuadraticMap.associated Q := by
  constructor
  · intro h
    ext x y
    simp only [LinearMap.compl₁₂_apply]
    have h1 := Q_add Q' (σ x) (σ y)
    have h2 := Q_add Q x y
    rw [← map_add, h, h x, h y] at h1
    have h2' : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
    apply mul_left_cancel₀ h2'
    show 2 * bil Q' (σ x) (σ y) = 2 * bil Q x y
    linear_combination h2 - h1
  · intro hB x
    have := congrArg (fun B : LinearMap.BilinForm F V => B x x) hB
    simp only [LinearMap.compl₁₂_apply] at this
    rw [← bil_self Q' (σ x), ← bil_self Q x]
    exact this

/-- **O'Meara 41:2 (1)** (p. 86). Let $U = (V, Q)$ have the matrix $M$ in the base $b$ ($m$ vectors) and
$(W, Q')$ the matrix $N$ in the base $c$ ($n$ vectors). Then $U$ is represented by $W$ (there is a linear
$\sigma$ with $Q'(\sigma x) = Q(x)$) if and only if $M = T^{\mathsf t} N T$ for some $n \times m$ matrix $T$ over $F$. -/
@[kb "omeara1963" "§41B, 41:2 (1), p. 86"]
theorem exists_rep_iff_gram {m n : ℕ} (b : Basis (Fin m) F V) (c : Basis (Fin n) F W) :
    (∃ σ : V →ₗ[F] W, ∀ x, Q' (σ x) = Q x) ↔
      ∃ T : Matrix (Fin n) (Fin m) F, gram Q b = Tᵀ * gram Q' c * T := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨LinearMap.toMatrix b c σ, ?_⟩
    rw [gram_eq_toMatrix₂, gram_eq_toMatrix₂, ← LinearMap.toMatrix₂_compl₁₂, (rep_iff_compl₁₂ Q Q' σ).1 hσ]
  · rintro ⟨T, hT⟩
    refine ⟨Matrix.toLin b c T, (rep_iff_compl₁₂ Q Q' _).2 ?_⟩
    apply (LinearMap.toMatrix₂ b b).injective
    rw [LinearMap.toMatrix₂_compl₁₂ c c, LinearMap.toMatrix_toLin, ← gram_eq_toMatrix₂, ← gram_eq_toMatrix₂, hT]

/-- **O'Meara 41:2 (2)** (p. 86). With the notation of 41:2 (1) and $m = n$: $V$ and $W$ are isometric (there is a
linear bijection $\sigma$ with $Q'(\sigma x) = Q(x)$) if and only if $M = T^{\mathsf t} N T$ for some invertible
$n \times n$ matrix $T$ over $F$ (i.e. $M \cong N$). -/
@[kb "omeara1963" "§41B, 41:2 (2), p. 86"]
theorem exists_isometry_iff_gram {n : ℕ} (b : Basis (Fin n) F V) (c : Basis (Fin n) F W) :
    (∃ σ : V ≃ₗ[F] W, ∀ x, Q' (σ x) = Q x) ↔
      ∃ T : Matrix (Fin n) (Fin n) F, IsUnit T.det ∧ gram Q b = Tᵀ * gram Q' c * T := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨LinearMap.toMatrix b c (σ : V →ₗ[F] W), ?_, ?_⟩
    · exact LinearEquiv.isUnit_det σ b c
    · rw [gram_eq_toMatrix₂, gram_eq_toMatrix₂, ← LinearMap.toMatrix₂_compl₁₂,
        (rep_iff_compl₁₂ Q Q' (σ : V →ₗ[F] W)).1 hσ]
  · rintro ⟨T, hTu, hT⟩
    have hu : IsUnit (LinearMap.toMatrix b c (Matrix.toLin b c T)).det := by
      rwa [LinearMap.toMatrix_toLin]
    refine ⟨LinearEquiv.ofIsUnitDet hu, ?_⟩
    have := (rep_iff_compl₁₂ Q Q' (Matrix.toLin b c T)).2 (by
      apply (LinearMap.toMatrix₂ b b).injective
      rw [LinearMap.toMatrix₂_compl₁₂ c c, LinearMap.toMatrix_toLin, ← gram_eq_toMatrix₂, ← gram_eq_toMatrix₂, hT])
    intro x
    exact this x

theorem iv_bil_smul_form (a : F) (x y : V) : bil (a • Q) x y = a * bil Q x y := by
  simp [bil, map_smul]

/-- The matrix part of 41:3 (the tagged version is `gram_smul` of `Sec92Class.lean`, cited in `CitationsIV.lean`):
the scaled space $V^a$ (the form $aQ$) has the matrix $aN$ in a family in which $V$ has the matrix $N$. -/
theorem iv_gram_smul {ι : Type*} (a : F) (x : ι → V) : gram (a • Q) x = a • gram Q x := by
  ext i j; simp [gram, iv_bil_smul_form]

/-- **O'Meara 41:3** (p. 87), the discriminant part. For $n$ vectors, $d_{aQ}(x_1,\dots,x_n) = a^n\, d_Q(x_1, \dots,
x_n)$; hence $d(V^a) = a^{\dim V} dV$ in $F/F^{\times 2}$. -/
@[kb "omeara1963" "§41B, 41:3, p. 87 (dV^a = a^n dV)"]
theorem det_gram_smul {n : ℕ} (a : F) (x : Fin n → V) :
    (gram (a • Q) x).det = a ^ n * (gram Q x).det := by
  rw [iv_gram_smul, Matrix.det_smul, Fintype.card_fin]

end Sec41

end QuadFormsKB.OMeara
