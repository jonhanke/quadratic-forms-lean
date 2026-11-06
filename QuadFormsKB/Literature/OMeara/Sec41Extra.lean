import QuadFormsKB.Literature.OMeara.Sec41
import QuadFormsKB.Defs.QuadForm

/-!
# O'Meara §41: the remaining identities and restatements (pp. 83–87)

**Setting** (as in `Sec41.lean`): $F$ a field with $2 \ne 0$ (`[Invertible (2 : F)]`), $(V, Q)$ and $(W, Q')$
quadratic spaces over $F$ (Mathlib `QuadraticForm F V`), O'Meara's symmetric bilinear form $B$ = `bil Q`
(so $B(x,x) = Q(x)$), the matrix $(B(x_i, x_j))$ of a family = `gram Q x`, the orthogonal group $O(V)$ = `orth Q`,
and the scaled space $V^a$ = `a • Q`.

**Proves**
* `Q_sum_lt` (p. 83; the double-sum form is `Q_sum` of `Sec82Isom.lean`): $Q(\sum a_i x_i) = \sum a_i^2 Q(x_i) + 2\sum_{i<j} a_i a_j B(x_i,x_j)$;
* `range_smul` (p. 83): $Q^a(V) = a\,Q(V)$; $O_Q(V) = O_{Q^a}(V)$ for $a \ne 0$ (p. 84) is `orth_smul` of `Sec55.lean`, tagged in `Sec42Extra.lean`;
* `det_gram_isEmpty` (p. 87): $dV = 1$ for the zero space;
* restatements of items that the book uses without a numbered statement: uniqueness of $B$
  (`bil_unique`), representations preserve $B$ (`bil_of_rep`), representations and Mathlib isometries
  (`exists_rep_iff_isometry`), isometric spaces (`exists_isometry_iff_equivalent`), the equivalence relation on
  matrices (`matRep_refl`, `matRep_trans`, `matEquiv_symm`), the change-of-base formula (`gram_change_of_base`),
  existence of a space with a given matrix (`exists_form_gram_eq`), and $d(x') = (\det T)^2 d(x)$
  (`det_gram_change_of_base`, `det_gram_basis_change`).

**Tags only** (existing declarations of `Sec82.lean`, `Sec41.lean`, `Defs/QuadForm.lean`): `Q_smul`, `Q_add`,
`iv_bil_smul_form`, `rep_iff_compl₁₂`, `gram_eq_toMatrix₂`, `iv_gram_smul`, `QuadForm.diag`,
`QuadForm.IsometricIn` (p. 88).

**Conventions.** Indices are 0-based (`Fin n`); O'Meara's $x_1, \dots, x_n$ are `x 0, …, x (n-1)`.
-/

open QuadraticMap Submodule Module LinearMap
open scoped Matrix Pointwise

set_option linter.unusedSectionVars false

noncomputable section

attribute [kb "omeara1963" "§41C, p. 86 (notation ⟨a₀,…,a_{n-1}⟩ for the diagonal space)"]
  QuadFormsKB.QuadForm.diag
attribute [kb "omeara1963" "§41C, p. 88 (equivalence of quadratic forms by substitution, as for matrices and spaces)"]
  QuadFormsKB.QuadForm.IsometricIn

namespace QuadFormsKB.OMeara

attribute [kb "omeara1963" "§41A, p. 83 (Q(ax) = a²Q(x))"] Q_smul
attribute [kb "omeara1963" "§41A, p. 83 (Q(x+y) = Q(x)+Q(y)+2B(x,y))"] Q_add
attribute [kb "omeara1963" "§41A, p. 83 (B^a = aB, Q^a(x) = aQ(x))"] iv_bil_smul_form
attribute [kb "omeara1963" "§41A, p. 84 (a representation preserves B)"] rep_iff_compl₁₂
attribute [kb "omeara1963" "§41B, p. 85 (the matrix of V in a base)"] gram_eq_toMatrix₂
attribute [kb "omeara1963" "§41B, p. 87 (matrix of the scaled space)"] iv_gram_smul

section Sec41Extra

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
variable {W : Type*} [AddCommGroup W] [Module F W] (Q' : QuadraticForm F W)

/-- Auxiliary: for a symmetric $f$, $\sum_{i,j} f_{ij} = \sum_i f_{ii} + 2\sum_{i<j} f_{ij}$. -/
theorem sum_sum_symm {n : ℕ} (f : Fin n → Fin n → F) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
  have h1 : ∀ i : Fin n, ∑ j, f i j =
      ∑ j ∈ Finset.Iio i, f i j + f i i + ∑ j ∈ Finset.Ioi i, f i j := by
    intro i
    have : (Finset.univ : Finset (Fin n)) = Finset.Iio i ∪ {i} ∪ Finset.Ioi i := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Iio, Finset.mem_singleton,
        Finset.mem_Ioi, true_iff]
      rcases lt_trichotomy j i with h | h | h <;> simp [h]
    have d1 : Disjoint (Finset.Iio i ∪ {i}) (Finset.Ioi i) :=
      Finset.disjoint_left.2 fun a ha hb => by simp at ha hb; omega
    have d2 : Disjoint (Finset.Iio i) {i} :=
      Finset.disjoint_left.2 fun a ha hb => by simp at ha hb; omega
    rw [this, Finset.sum_union d1, Finset.sum_union d2, Finset.sum_singleton]
  have h2 : ∑ i, ∑ j ∈ Finset.Iio i, f i j = ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
    have := Finset.sum_comm' (s := (Finset.univ : Finset (Fin n))) (t := fun i => Finset.Iio i)
      (t' := (Finset.univ : Finset (Fin n))) (s' := fun j => Finset.Ioi j) (f := fun i j => f i j)
      (by intro x y; simp)
    rw [this]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hf _ _
  simp only [h1, Finset.sum_add_distrib, h2]
  ring

/-- **O'Meara §41A, p. 83** (the third displayed identity, $Q(\sum a_i x_i)$). For $x_0,\dots,x_{n-1} \in V$ and
$a_0,\dots,a_{n-1} \in F$:
$$Q\Big(\sum_i a_i x_i\Big) = \sum_i a_i^2\, Q(x_i) + 2\sum_{i<j} a_i a_j\, B(x_i, x_j).$$ -/
@[kb "omeara1963" "§41A, p. 83"]
theorem Q_sum_lt {n : ℕ} (a : Fin n → F) (x : Fin n → V) :
    Q (∑ i, a i • x i) = ∑ i, a i ^ 2 * Q (x i) +
      2 * ∑ i, ∑ j ∈ Finset.Ioi i, a i * a j * bil Q (x i) (x j) := by
  rw [← bil_self, bil_sum_left]
  simp only [bil_sum_right, bil_smul_left, bil_smul_right]
  have := sum_sum_symm (fun i j => a j * (a i * bil Q (x i) (x j))) (by
    intro i j; rw [bil_comm Q (x j) (x i)]; ring)
  rw [this]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [bil_self]; ring
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **O'Meara §41A, p. 83.** The values of the scaled space satisfy $Q^a(V) = a\,Q(V)$, where $Q^a = aQ$. -/
@[kb "omeara1963" "§41A, p. 83 (Q^a(V) = aQ(V))"]
theorem range_smul (a : F) : Set.range (a • Q) = a • Set.range Q := by
  ext y
  simp only [Set.mem_range, Set.mem_smul_set, _root_.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨Q x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩

/-- **O'Meara §41B, p. 87.** The zero space has discriminant $1$: the matrix of the empty family is the
$0\times 0$ matrix, whose determinant is $1$. (For any index type with no elements, in particular for a base of a
zero dimensional space.) -/
@[kb "omeara1963" "§41B, p. 87 (dV = 1 for the zero space)"]
theorem det_gram_isEmpty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι] (x : ι → V) :
    (gram Q x).det = 1 :=
  Matrix.det_isEmpty

/-- **O'Meara §41A, p. 83** (uniqueness of $B$, "from the second identity"). A symmetric bilinear form $B'$ on $V$
with $B'(x,x) = Q(x)$ for all $x$ equals O'Meara's $B$ = `bil Q`. -/
@[kb "omeara1963" "§41A, p. 83 (B is determined by Q)"]
theorem bil_unique (B : LinearMap.BilinForm F V) (hsymm : ∀ x y, B x y = B y x)
    (h : ∀ x, B x x = Q x) (x y : V) : B x y = bil Q x y := by
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  have e1 : Q (x + y) = Q x + 2 * bil Q x y + Q y := Q_add Q x y
  have e2 : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
    simp only [map_add, LinearMap.add_apply]; rw [hsymm y x]; ring
  rw [h, h, h] at e2
  apply mul_left_cancel₀ h2
  linear_combination e1 - e2

/-- **O'Meara §41A, p. 84.** A representation $\sigma$ of $V$ into $W$ ($Q'(\sigma x) = Q(x)$) satisfies
$B'(\sigma x, \sigma y) = B(x, y)$. -/
@[kb "omeara1963" "§41A, p. 84 (B(σx, σy) = B(x, y))"]
theorem bil_of_rep (σ : V →ₗ[F] W) (h : ∀ x, Q' (σ x) = Q x) (x y : V) :
    bil Q' (σ x) (σ y) = bil Q x y := by
  have := congrArg (fun B : LinearMap.BilinForm F V => B x y) ((rep_iff_compl₁₂ Q Q' σ).1 h)
  simpa using this

/-- **O'Meara §41A, p. 84.** A representation of $V$ into $W$ (a linear $\sigma$ with $Q'(\sigma x) = Q(x)$) is
the same as Mathlib's isometry `Q →qᵢ Q'` (which does not require injectivity). -/
@[kb "omeara1963" "§41A, p. 84 (representation = Mathlib isometry)"]
theorem exists_rep_iff_isometry :
    (∃ σ : V →ₗ[F] W, ∀ x, Q' (σ x) = Q x) ↔ Nonempty (Q →qᵢ Q') :=
  ⟨fun ⟨σ, h⟩ => ⟨⟨σ, h⟩⟩, fun ⟨σ⟩ => ⟨σ.toLinearMap, σ.map_app⟩⟩

/-- **O'Meara §41A, p. 84.** $V$ and $W$ are isometric (there is a linear bijection $\sigma : V \to W$ with
$Q'(\sigma x) = Q(x)$) iff the forms are equivalent in Mathlib's sense. -/
@[kb "omeara1963" "§41A, p. 84 (isometric spaces)"]
theorem exists_isometry_iff_equivalent :
    (∃ σ : V ≃ₗ[F] W, ∀ x, Q' (σ x) = Q x) ↔ Q.Equivalent Q' :=
  ⟨fun ⟨σ, h⟩ => ⟨⟨σ, h⟩⟩, fun ⟨σ⟩ => ⟨σ.toLinearEquiv, σ.map_app⟩⟩

section Matrices

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **O'Meara §41B, p. 85** (equivalence of matrices, reflexivity): $M \to M$ via $T = 1$. -/
@[kb "omeara1963" "§41B, p. 85 (M -> M)"]
theorem matRep_refl (M : Matrix ι ι F) : M = (1 : Matrix ι ι F)ᵀ * M * 1 := by simp

/-- **O'Meara §41B, p. 85** (transitivity of "is represented by"): if $M = T^{\mathsf t} N T$ and
$N = S^{\mathsf t} P S$ then $M = (ST)^{\mathsf t} P (ST)$. -/
@[kb "omeara1963" "§41B, p. 85 (M -> N -> P implies M -> P)"]
theorem matRep_trans {μ : Type*} [Fintype μ] [DecidableEq μ]
    {M : Matrix ι ι F} {N : Matrix κ κ F} {P : Matrix μ μ F}
    {T : Matrix κ ι F} {S : Matrix μ κ F} (h1 : M = Tᵀ * N * T) (h2 : N = Sᵀ * P * S) :
    M = (S * T)ᵀ * P * (S * T) := by
  rw [h1, h2, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

/-- **O'Meara §41B, p. 85** (symmetry of equivalence): if $M = T^{\mathsf t} N T$ with $T$ invertible then
$N = (T^{-1})^{\mathsf t} M\, T^{-1}$. -/
@[kb "omeara1963" "§41B, p. 85 (M ≅ N implies N ≅ M)"]
theorem matEquiv_symm {M N : Matrix ι ι F} {T : Matrix ι ι F} (hT : IsUnit T.det)
    (h : M = Tᵀ * N * T) : N = (T⁻¹)ᵀ * M * T⁻¹ := by
  have h1 : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hT
  have h2 : (T⁻¹)ᵀ * Tᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rw [h]
  calc N = ((T⁻¹)ᵀ * Tᵀ) * N * (T * T⁻¹) := by rw [h1, h2]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **O'Meara §41B, pp. 85–86** (change of base). Let $x'_j = \sum_i t_{ij} x_i$, i.e. $x' = x\cdot T$. Then the
matrix of the family $x'$ is $N' = T^{\mathsf t} N T$, where $N$ is the matrix of $x$. -/
@[kb "omeara1963" "§41B, pp. 85-86 (change of base N' = ᵗT N T)"]
theorem gram_change_of_base (x : ι → V) (x' : κ → V) (T : Matrix ι κ F)
    (hx : ∀ j, x' j = ∑ i, T i j • x i) : gram Q x' = Tᵀ * gram Q x * T := by
  ext j k
  simp only [gram, Matrix.of_apply, hx, bil_sum_left, bil_sum_right, bil_smul_left, bil_smul_right,
    Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **O'Meara §41B, p. 87** ($d(x') = (\det T)^2 d(x)$). If $x'_j = \sum_i t_{ij} x_i$ with $T$ a square matrix
(`Fin m`), the discriminants of the families are related by $d(x') = (\det T)^2\, d(x)$. -/
@[kb "omeara1963" "§41B, p. 87 (d(x') = (det T)^2 d(x))"]
theorem det_gram_change_of_base {m : ℕ} (x x' : Fin m → V) (T : Matrix (Fin m) (Fin m) F)
    (hx : ∀ j, x' j = ∑ i, T i j • x i) :
    (gram Q x').det = T.det ^ 2 * (gram Q x).det := by
  rw [gram_change_of_base Q x x' T hx, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- **O'Meara §41B, p. 87** (independence of the base). For two bases $b, b'$ of $V$ there is a non-zero
$\alpha \in F$ (the determinant of the transition matrix) with $d(b') = \alpha^2 d(b)$, so the class of $d(b)$ in
$\{0\} \cup F/F^{\times 2}$ depends only on $V$. -/
@[kb "omeara1963" "§41B, p. 87 (d(b') = α² d(b); the discriminant dV is well defined)"]
theorem det_gram_basis_change {m : ℕ} (b b' : Basis (Fin m) F V) :
    ∃ α : F, α ≠ 0 ∧ (gram Q b').det = α ^ 2 * (gram Q b).det := by
  refine ⟨(b.toMatrix b').det, ?_, ?_⟩
  · have := b.isUnit_det b'
    rw [Basis.det_apply] at this
    exact this.ne_zero
  · refine det_gram_change_of_base Q b b' _ fun j => ?_
    simp [Basis.toMatrix_apply, Basis.sum_repr]

/-- **O'Meara §41B, p. 86.** Given a base $b$ of $V$ and a symmetric matrix $N$ there is a quadratic form
(a space structure on $V$) whose matrix in the base $b$ is $N$. -/
@[kb "omeara1963" "§41B, p. 86 (a form with prescribed matrix in a base)"]
theorem exists_form_gram_eq (b : Basis ι F V) (N : Matrix ι ι F) (hN : Nᵀ = N) :
    ∃ Q : QuadraticForm F V, gram Q b = N := by
  have hB : ∀ i j, Matrix.toLinearMap₂ b b N (b i) (b j) = N i j := by
    intro i j
    have := LinearMap.toMatrix₂_apply b b (Matrix.toLinearMap₂ b b N) i j
    rw [LinearMap.toMatrix₂_toLinearMap₂] at this
    exact this.symm
  have hflip : (Matrix.toLinearMap₂ b b N).flip = Matrix.toLinearMap₂ b b N := by
    refine LinearMap.BilinForm.ext_basis b fun i j => ?_
    rw [LinearMap.flip_apply, hB, hB]
    have := congrFun (congrFun hN i) j
    simpa using this
  refine ⟨LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂ b b N), ?_⟩
  ext i j
  have := QuadraticMap.associated_left_inverse' (S := F) hflip
  simp only [gram, Matrix.of_apply, bil]
  exact (congrArg (fun B : LinearMap.BilinForm F V => B (b i) (b j)) this).trans (hB i j)

end Matrices

end Sec41Extra

end QuadFormsKB.OMeara
