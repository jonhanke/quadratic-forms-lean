/-
# The genus-$g$ theta series and its transformation law

**Layer:** classical, over $\mathbb R$ and $\mathbb Z$.

**Setting.** $S$ a real symmetric positive definite $N\times N$ matrix (the Gram matrix of a lattice $L = \mathbb Z^N$,
$Q(x) = \tfrac12x^{\mathsf T}Sx$), $g$ the genus, $\mathbb H_g = \{Z \in M_g(\mathbb C) : Z^{\mathsf T} = Z,\ \operatorname{Im}Z > 0\}$
the Siegel upper half space (`siegelH`). Points of $L^g$ are integer matrices $X \in M_{N\times g}(\mathbb Z)$ (column $j$ is
$x_j \in L$), and $Q[X] = \tfrac12X^{\mathsf T}SX = (\tfrac12x_i^{\mathsf T}Sx_j)_{ij}$. **The theta series of genus $g$**:
$$\Theta^{(g)}_S(Z) = \sum_{X\in M_{N\times g}(\mathbb Z)}e\big(\operatorname{tr}(Q[X]Z)\big)
  = \sum_X\exp\big(\pi i\operatorname{tr}(X^{\mathsf T}SXZ)\big)\qquad(\texttt{thetaG}).$$

**Results.**
* `summable_thetaG`: absolute convergence on $\mathbb H_g$.
* **`thetaG_inversion`** (theta inversion in genus $g$, $N = 2k$ even): for $Z \in \mathbb H_g$,
  $$\Theta_S(Z) = \det(S)^{-g/2}\,\det(Z/i)^{-k}\,\Theta_{S^{-1}}(-Z^{-1}).$$
  *Proof.* Simultaneous diagonalization $Z = P(\Lambda + iI)P^{\mathsf T}$ with $P$ real invertible and $\Lambda$ real diagonal
  (`exists_siegel_diag`, in `Weil/Genus/SiegelSpace.lean`), $S = C^{\mathsf T}C$; then $\pi i\operatorname{tr}(X^{\mathsf T}SXZ) = -\pi\sum_{r,k}(1 - i\lambda_k)(CXP)_{rk}^2$, a
  diagonal complex Gaussian of the linear map $X \mapsto CXP$ (the Kronecker product $C \otimes P^{\mathsf T}$), and
  Poisson summation `HilbertModular.tsum_gaussAt`. The $N$ square roots $(1 - i\lambda_k)^{-1/2}$ attached to column $k$
  combine to $(1 - i\lambda_k)^{-k}$ because $N$ is even, and $\det(Z/i) = \det(P)^2\prod_k(1 - i\lambda_k)$: no branch of
  $\det(Z/i)^{1/2}$ is needed.
* **`thetaG_neg_inv`** (even unimodular lattices, the first case of the transformation law): $S$ integral, $\det S = 1$, $N = 2k$:
  $$\Theta_S(-Z^{-1}) = \det(Z/i)^{k}\,\Theta_S(Z).$$
  (Unimodularity gives $\Theta_{S^{-1}} = \Theta_S$ by $X \mapsto SX$; evenness is not needed here.)
* `thetaG_add_int`: $\Theta_S(Z + B) = \Theta_S(Z)$ for $B$ integral symmetric, $S$ integral with even diagonal.
* `thetaG_conj`: $\Theta_S(AZA^{\mathsf T}) = \Theta_S(Z)$ for $A \in \mathrm{GL}_g(\mathbb Z)$.
For $g = 1$ these are the classical $\theta_L(-1/z) = (z/i)^{N/2}\theta_L(z)$, $\theta_L(z + 1) = \theta_L(z)$.

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I §0 and Anhang (Thetareihen, Theta-Transformationsformel)
[unverified]; Andrianov–Zhuravlev, *Modular forms and Hecke operators* (1995), Ch. 1 §1.? (theta inversion in genus $g$)
[unverified]; Klingen, *Introductory lectures on Siegel modular forms* (1990), §I.? [unverified]; Kudla, *Notes on the
local theta correspondence* (1996), §I.4 (the classical theta series as a theta distribution) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.HilbertModular.DiagGaussian
import QuadFormsKB.Weil.Genus.SiegelSpace

open Matrix Complex
open scoped Real Kronecker

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

variable {N g : ℕ}

/-- The exponent $\pi i\operatorname{tr}(X^{\mathsf T}SXZ) = 2\pi i\operatorname{tr}(Q[X]Z)$. -/
def thetaArg (S : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin g) (Fin g) ℂ) (X : Matrix (Fin N) (Fin g) ℂ) : ℂ :=
  π * I * trace (Xᵀ * cR S * X * Z)

/-- **The theta series of genus $g$** of the real symmetric matrix $S$:
$\Theta_S(Z) = \sum_{X\in M_{N\times g}(\mathbb Z)}\exp\big(\pi i\operatorname{tr}(X^{\mathsf T}SXZ)\big)$, i.e. $\sum_Xe(\operatorname{tr}(Q[X]Z))$
with $Q[X] = \tfrac12X^{\mathsf T}SX$. -/
@[kb "freitag1983" "Ch. I (Thetareihe $\\vartheta(S, Z) = \\sum_G e^{\\pi i\\,\\sigma(S[G]Z)}$) [unverified]"]
def thetaG (S : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  ∑' X : Matrix (Fin N) (Fin g) ℤ, cexp (thetaArg S Z (cZ X))

/-! ### Parity helper -/

lemma even_sum_sym {n : ℕ} (f : Fin n → Fin n → ℤ) (hf : ∀ i j, f i j = f j i) :
    Even ((∑ i, ∑ j, f i j) - ∑ i, f i i) := by
  rw [← ZMod.intCast_eq_zero_iff_even]
  push_cast
  set F : Fin n → Fin n → ZMod 2 := fun i j => (f i j : ZMod 2) with hF
  have h1 : ∀ i, ∑ j, F i j = ∑ j, (if i = j then 0 else F i j) + F i i := by
    intro i
    have : ∀ j, F i j = (if i = j then 0 else F i j) + (if i = j then F i j else 0) := by
      intro j; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib]
    simp
  have h2 : (∑ i, ∑ j, F i j) - ∑ i, F i i = ∑ i, ∑ j, (if i = j then 0 else F i j) := by
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    ring
  show (∑ i, ∑ j, F i j) - ∑ i, F i i = 0
  rw [h2, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ (by simp) (by simp)
  · rintro ⟨a, b⟩ _
    by_cases h : a = b
    · subst h; simp
    · have : b ≠ a := Ne.symm h
      simp only [h, this, ite_false, hF, hf a b]
      rw [← two_mul]
      have : (2 : ZMod 2) = 0 := by decide
      rw [this]; simp
  · rintro ⟨a, b⟩ _ hne
    intro h
    simp only [Prod.mk.injEq] at h
    apply hne
    rw [h.1] at *
    simp

/-! ### Gaussian reduction helpers -/

/-- Right multiplication by `A ∈ GL_g(ℤ)` on integer matrices. -/
def mulRightGL (A : GL (Fin g) ℤ) : Matrix (Fin N) (Fin g) ℤ ≃ Matrix (Fin N) (Fin g) ℤ where
  toFun X := X * (A : Matrix (Fin g) (Fin g) ℤ)
  invFun X := X * ((A⁻¹ : GL (Fin g) ℤ) : Matrix (Fin g) (Fin g) ℤ)
  left_inv X := by
    show X * (A : Matrix (Fin g) (Fin g) ℤ) * ((A⁻¹ : GL (Fin g) ℤ) : Matrix (Fin g) (Fin g) ℤ) = X
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv X := by
    show X * ((A⁻¹ : GL (Fin g) ℤ) : Matrix (Fin g) (Fin g) ℤ) * (A : Matrix (Fin g) (Fin g) ℤ) = X
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

/-- `cZ` of right multiplication by `A`. -/
lemma cZ_mulRightGL (A : GL (Fin g) ℤ) (X : Matrix (Fin N) (Fin g) ℤ) :
    cZ (mulRightGL A X) = cZ X * cZ (A : Matrix (Fin g) (Fin g) ℤ) := by
  show cZ (X * (A : Matrix (Fin g) (Fin g) ℤ)) = _
  exact (Matrix.map_mul (f := Int.castRingHom ℂ))

/-- Vectorization of an integer matrix as a vector indexed by pairs `(row, column)`. -/
def vecEquiv (N g : ℕ) : Matrix (Fin N) (Fin g) ℤ ≃ (Fin N × Fin g → ℤ) :=
  (Equiv.curry (Fin N) (Fin g) ℤ).symm

/-- Value of `vecEquiv`. -/
lemma vecEquiv_apply (X : Matrix (Fin N) (Fin g) ℤ) (p : Fin N × Fin g) :
    vecEquiv N g X p = X p.1 p.2 := rfl

/-- The Kronecker matrix $C \otimes P^{\mathsf T}$ of the linear map $X \mapsto CXP$. -/
def gaussMat (C : Matrix (Fin N) (Fin N) ℝ) (P : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin N × Fin g) (Fin N × Fin g) ℝ :=
  Matrix.kroneckerMap (· * ·) C Pᵀ

/-- $(M\vec X)_{(r,l)} = (CXP)_{rl}$ for $M = C \otimes P^{\mathsf T}$. -/
lemma gaussMat_mulVec (C : Matrix (Fin N) (Fin N) ℝ) (P : Matrix (Fin g) (Fin g) ℝ)
    (X : Matrix (Fin N) (Fin g) ℤ) (r : Fin N) (l : Fin g) :
    (gaussMat C P *ᵥ fun i => ((vecEquiv N g X i : ℤ) : ℝ)) (r, l) =
      (C * X.map ((↑) : ℤ → ℝ) * P) r l := by
  simp only [gaussMat, vecEquiv_apply, mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply,
    transpose_apply, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- `cR` of a Gram matrix. -/
lemma cR_transpose_mul (C : Matrix (Fin N) (Fin N) ℝ) : cR (Cᵀ * C) = (cR C)ᵀ * cR C := by
  ext i j; simp [Matrix.mul_apply]

/-- **Key pointwise trace identity:**
$\operatorname{tr}(X^{\mathsf T}C^{\mathsf T}CX\cdot P\,\mathrm{diag}(d)P^{\mathsf T}) = \sum_{r,l}d_l\,(CXP)_{rl}^2$. -/
lemma trace_pointwise (C : Matrix (Fin N) (Fin N) ℝ) (P : Matrix (Fin g) (Fin g) ℝ) (d : Fin g → ℂ)
    (X : Matrix (Fin N) (Fin g) ℤ) :
    trace ((cZ X)ᵀ * cR (Cᵀ * C) * cZ X * (cR P * diagonal d * (cR P)ᵀ)) =
      ∑ r, ∑ l, d l * (((C * X.map ((↑) : ℤ → ℝ) * P) r l : ℝ) : ℂ) ^ 2 := by
  have hY : cR (C * X.map ((↑) : ℤ → ℝ) * P) = cR C * cZ X * cR P := by
    ext i j; simp [Matrix.mul_apply]
  set W : Matrix (Fin N) (Fin g) ℂ := cR C * cZ X * cR P with hW
  have h1 : trace ((cZ X)ᵀ * cR (Cᵀ * C) * cZ X * (cR P * diagonal d * (cR P)ᵀ)) =
      trace (Wᵀ * W * diagonal d) := by
    calc _ = trace ((((cZ X)ᵀ * cR (Cᵀ * C) * cZ X) * (cR P * diagonal d)) * (cR P)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = trace ((cR P)ᵀ * (((cZ X)ᵀ * cR (Cᵀ * C) * cZ X) * (cR P * diagonal d))) :=
          Matrix.trace_mul_comm _ _
      _ = _ := by
          rw [hW, cR_transpose_mul]
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h1, ← hY]
  generalize C * X.map ((↑) : ℤ → ℝ) * P = Y
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, cR, Matrix.map_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

open QuadFormsKB.HilbertModular in
/-- The theta summand as a diagonal complex Gaussian of $X \mapsto CXP$. -/
lemma cexp_thetaArg_eq (C : Matrix (Fin N) (Fin N) ℝ) (P : Matrix (Fin g) (Fin g) ℝ)
    (d b : Fin g → ℂ) (hdb : ∀ l, π * I * d l = -π * b l) (X : Matrix (Fin N) (Fin g) ℤ) :
    cexp (thetaArg (Cᵀ * C) (cR P * diagonal d * (cR P)ᵀ) (cZ X)) =
      gaussAt (fun j : Fin N × Fin g => b j.2) (gaussMat C P) (vecEquiv N g X) := by
  unfold thetaArg
  rw [trace_pointwise]
  congr 1
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [gaussMat_mulVec]
  linear_combination (((C * X.map ((↑) : ℤ → ℝ) * P) r l : ℝ) : ℂ) ^ 2 * hdb l

open QuadFormsKB.HilbertModular in
/-- `thetaG` as a Gaussian sum over $\mathbb Z^{N\times g}$ (reindexed to pairs). -/
lemma thetaG_eq_gauss (C : Matrix (Fin N) (Fin N) ℝ) (P : Matrix (Fin g) (Fin g) ℝ)
    (d b : Fin g → ℂ) (hdb : ∀ l, π * I * d l = -π * b l) :
    thetaG (Cᵀ * C) (cR P * diagonal d * (cR P)ᵀ) =
      ∑' k : Fin N × Fin g → ℤ, gaussAt (fun j : Fin N × Fin g => b j.2) (gaussMat C P) k := by
  unfold thetaG
  rw [← (vecEquiv N g).tsum_eq]
  exact tsum_congr fun X => cexp_thetaArg_eq C P d b hdb X

/-- $\pi i(t + i) = -\pi(1 - it)$. -/
lemma hdb_lam (t : ℝ) : (π : ℂ) * I * ((t : ℂ) + I) = -π * (1 - I * t) := by
  linear_combination (π : ℂ) * Complex.I_sq

/-- $\det(C\otimes P^{\mathsf T}) = \det(C)^g\det(P)^N$. -/
lemma det_gaussMat (C : Matrix (Fin N) (Fin N) ℝ) (P : Matrix (Fin g) (Fin g) ℝ) :
    (gaussMat C P).det = C.det ^ g * P.det ^ N := by
  have : gaussMat C P = C ⊗ₖ Pᵀ := rfl
  rw [this, Matrix.det_kronecker, Matrix.det_transpose]
  simp

/-- $M^{\mathsf T}M' = 1$ for $M = C\otimes P^{\mathsf T}$ and $M' = C^{-\mathsf T}\otimes P^{-1}$. -/
lemma gaussMat_transpose_mul (C : Matrix (Fin N) (Fin N) ℝ) (P : Matrix (Fin g) (Fin g) ℝ)
    (hC : C.det ≠ 0) (hP : P.det ≠ 0) :
    (gaussMat C P)ᵀ * gaussMat (C⁻¹)ᵀ (P⁻¹)ᵀ = 1 := by
  have h1 : (gaussMat C P)ᵀ = Cᵀ ⊗ₖ P := by
    show (Matrix.kroneckerMap (· * ·) C Pᵀ)ᵀ = _
    rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_transpose]
  have h2 : gaussMat (C⁻¹)ᵀ (P⁻¹)ᵀ = (C⁻¹)ᵀ ⊗ₖ P⁻¹ := by
    show _ = _
    rw [gaussMat, Matrix.transpose_transpose]
  rw [h1, h2, ← Matrix.mul_kronecker_mul]
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hCu, Matrix.mul_nonsing_inv _ hPu,
    Matrix.transpose_one, Matrix.one_kronecker_one]

/-- `cR` is multiplicative. -/
lemma cR_mul {l m n : Type*} [Fintype m] (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    cR (A * B) = cR A * cR B := by
  ext i j; simp [Matrix.mul_apply]

/-- `cR` preserves `1`. -/
lemma cR_one {n : Type*} [DecidableEq n] : cR (1 : Matrix n n ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]

/-- `cR` commutes with transpose. -/
lemma cR_transpose {m n : Type*} (A : Matrix m n ℝ) : cR Aᵀ = (cR A)ᵀ := by
  ext i j; simp

/-- The determinant commutes with the real-to-complex cast. -/
lemma det_cR (P : Matrix (Fin g) (Fin g) ℝ) : (cR P).det = (P.det : ℂ) := by
  exact (RingHom.map_det Complex.ofRealHom P).symm

/-- $(C^{\mathsf T}C)^{-1} = (C^{-\mathsf T})^{\mathsf T}C^{-\mathsf T}$. -/
lemma inv_gram (C : Matrix (Fin N) (Fin N) ℝ) :
    (Cᵀ * C)⁻¹ = ((C⁻¹)ᵀ)ᵀ * (C⁻¹)ᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]

/-- $-(P\,\mathrm{diag}(d)P^{\mathsf T})^{-1} = P^{-\mathsf T}\mathrm{diag}(-d^{-1})P^{-1}$. -/
lemma neg_inv_siegel_diag (P : Matrix (Fin g) (Fin g) ℝ) (hP : P.det ≠ 0) (d : Fin g → ℂ)
    (hd : ∀ l, d l ≠ 0) :
    -(cR P * diagonal d * (cR P)ᵀ)⁻¹ =
      cR (P⁻¹)ᵀ * diagonal (fun l => -(d l)⁻¹) * (cR (P⁻¹)ᵀ)ᵀ := by
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  set Q : Matrix (Fin g) (Fin g) ℂ := cR (P⁻¹) with hQ
  have h1 : cR P * Q = 1 := by rw [hQ, ← cR_mul, Matrix.mul_nonsing_inv _ hPu, cR_one]
  have h2 : Q * cR P = 1 := by rw [hQ, ← cR_mul, Matrix.nonsing_inv_mul _ hPu, cR_one]
  have h3 : (cR P)ᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  have h4 : diagonal d * diagonal (fun l => (d l)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext l; exact mul_inv_cancel₀ (hd l)
  have h5 : cR P * diagonal d * (cR P)ᵀ * (Qᵀ * diagonal (fun l => (d l)⁻¹) * Q) = 1 := by
    calc _ = cR P * diagonal d * ((cR P)ᵀ * Qᵀ) * diagonal (fun l => (d l)⁻¹) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [h3, Matrix.mul_one, Matrix.mul_assoc (cR P), h4, Matrix.mul_one, h1]
  rw [Matrix.inv_eq_right_inv h5, cR_transpose, ← hQ]
  have : diagonal (fun l => -(d l)⁻¹) = -diagonal (fun l => (d l)⁻¹) := by
    rw [← Matrix.diagonal_neg]
  rw [this, Matrix.transpose_transpose]
  simp only [Matrix.mul_neg, Matrix.neg_mul]

/-- $\det((-i)Z) = \det(P)^2\prod_l(1 - i\lambda_l)$ for $Z = P(\Lambda + i)P^{\mathsf T}$. -/
lemma det_smul_siegel_diag (P : Matrix (Fin g) (Fin g) ℝ) (lam : Fin g → ℝ) :
    det ((-I) • (cR P * diagonal (fun k => (lam k : ℂ) + I) * (cR P)ᵀ)) =
      (P.det : ℂ) ^ 2 * ∏ l, (1 - I * (lam l : ℂ)) := by
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    det_cR, Fintype.card_fin]
  have h1 : ∏ l, (-I * ((lam l : ℂ) + I)) = (-I) ^ g * ∏ l, ((lam l : ℂ) + I) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ∏ l, (-I * ((lam l : ℂ) + I)) = ∏ l, (1 - I * (lam l : ℂ)) := by
    refine Finset.prod_congr rfl fun l _ => ?_
    linear_combination (-1 : ℂ) * Complex.I_sq
  rw [← h2, h1]
  ring

/-- The $N = 2k$ square roots attached to a column combine to a $k$-th power. -/
lemma prod_half_cpow (k : ℕ) (b : Fin g → ℂ) :
    ∏ j : Fin (2 * k) × Fin g, (b j.2)⁻¹ ^ (1 / 2 : ℂ) = (∏ l, b l)⁻¹ ^ k := by
  rw [Fintype.prod_prod_type, Finset.prod_comm, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun l _ => ?_
  dsimp only
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
  congr 1
  simp [one_div]

/-- $\det((-i)Z) \ne 0$ on $\mathbb H_g$. -/
lemma det_smul_siegel_ne_zero {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelH g) :
    det ((-I) • Z) ≠ 0 := by
  obtain ⟨P, lam, hP, rfl⟩ := exists_siegel_diag hZ
  rw [det_smul_siegel_diag]
  refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hP)) (Finset.prod_ne_zero_iff.mpr fun l _ h => ?_)
  have := congrArg Complex.re h
  simp at this

/-- For $\det S = 1$ over $\mathbb Z$, the real inverse of $S$ is its adjugate. -/
lemma inv_map_int {S : Matrix (Fin N) (Fin N) ℤ} (hdet : S.det = 1) :
    (S.map ((↑) : ℤ → ℝ))⁻¹ = S.adjugate.map ((↑) : ℤ → ℝ) := by
  apply Matrix.inv_eq_right_inv
  have : S * S.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  calc S.map ((↑) : ℤ → ℝ) * S.adjugate.map ((↑) : ℤ → ℝ)
      = (S * S.adjugate).map (Int.castRingHom ℝ) := (Matrix.map_mul (f := Int.castRingHom ℝ)).symm
    _ = 1 := by rw [this]; exact Matrix.map_one _ (by simp) (by simp)

/-- Casting the integer quadratic expression $X^{\mathsf T}TX$. -/
lemma cZ_quad (T : Matrix (Fin N) (Fin N) ℤ) (X : Matrix (Fin N) (Fin g) ℤ) :
    (cZ X)ᵀ * cR (T.map ((↑) : ℤ → ℝ)) * cZ X = cZ (Xᵀ * T * X) := by
  ext i j
  simp [Matrix.mul_apply]

/-- For unimodular symmetric integral $S$, $\Theta_{S^{-1}} = \Theta_S$ (via $X \mapsto SX$). -/
lemma thetaG_adjugate {S : Matrix (Fin N) (Fin N) ℤ} (hSsymm : Sᵀ = S) (hdet : S.det = 1)
    (W : Matrix (Fin g) (Fin g) ℂ) :
    thetaG (S.adjugate.map ((↑) : ℤ → ℝ)) W = thetaG (S.map ((↑) : ℤ → ℝ)) W := by
  have hST : S * S.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hTS : S.adjugate * S = 1 := by rw [Matrix.adjugate_mul, hdet, one_smul]
  let e : Matrix (Fin N) (Fin g) ℤ ≃ Matrix (Fin N) (Fin g) ℤ :=
    { toFun := fun Y => S * Y
      invFun := fun X => S.adjugate * X
      left_inv := fun Y => by
        show S.adjugate * (S * Y) = Y
        rw [← Matrix.mul_assoc, hTS, Matrix.one_mul]
      right_inv := fun X => by
        show S * (S.adjugate * X) = X
        rw [← Matrix.mul_assoc, hST, Matrix.one_mul] }
  unfold thetaG
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  unfold thetaArg
  show cexp (π * I * trace ((cZ (S * Y))ᵀ * _ * cZ (S * Y) * W)) = _
  have hq : (S * Y)ᵀ * S.adjugate * (S * Y) = Yᵀ * S * Y := by
    rw [Matrix.transpose_mul, hSsymm]
    calc Yᵀ * S * S.adjugate * (S * Y) = Yᵀ * (S * S.adjugate) * (S * Y) := by simp only [Matrix.mul_assoc]
      _ = Yᵀ * S * Y := by rw [hST, Matrix.mul_one, Matrix.mul_assoc]
  rw [cZ_quad, cZ_quad, hq]

/-- Trace identity for the change of basis $X \mapsto XA$. -/
lemma trace_conj_aux (X' : Matrix (Fin N) (Fin g) ℂ) (R : Matrix (Fin N) (Fin N) ℂ)
    (A' Z : Matrix (Fin g) (Fin g) ℂ) :
    trace ((X' * A')ᵀ * R * (X' * A') * Z) = trace (X'ᵀ * R * X' * (A' * Z * A'ᵀ)) := by
  have h1 : trace (X'ᵀ * R * X' * (A' * Z * A'ᵀ)) = trace ((X'ᵀ * R * X' * (A' * Z)) * A'ᵀ) := by
    simp only [Matrix.mul_assoc]
  have h2 : trace ((X'ᵀ * R * X' * (A' * Z)) * A'ᵀ) = trace (A'ᵀ * (X'ᵀ * R * X' * (A' * Z))) :=
    Matrix.trace_mul_comm _ _
  have h3 : A'ᵀ * (X'ᵀ * R * X' * (A' * Z)) = (X' * A')ᵀ * R * (X' * A') * Z := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h1, h2, h3]

/-! ### The theta inversion formula -/

/-- **Absolute convergence** of the theta series of genus $g$ on $\mathbb H_g$. -/
@[kb "freitag1983" "Ch. I (convergence of the theta series) [unverified]"]
theorem summable_thetaG {S : Matrix (Fin N) (Fin N) ℝ} (hS : S.PosDef) {Z : Matrix (Fin g) (Fin g) ℂ}
    (hZ : Z ∈ siegelH g) :
    Summable fun X : Matrix (Fin N) (Fin g) ℤ => ‖cexp (thetaArg S Z (cZ X))‖ := by
  obtain ⟨C, rfl, hC⟩ := exists_eq_transpose_mul hS
  obtain ⟨P, lam, hP, rfl⟩ := exists_siegel_diag hZ
  have hdb : ∀ l, (π : ℂ) * I * ((lam l : ℂ) + I) = -π * (1 - I * lam l) := fun l => hdb_lam _
  have h := QuadFormsKB.HilbertModular.summable_norm_gaussAt (gaussMat C P)
    (by rw [det_gaussMat]; exact mul_ne_zero (pow_ne_zero _ hC) (pow_ne_zero _ hP))
    (fun j : Fin N × Fin g => 1 - I * (lam j.2 : ℂ)) (fun j => by simp)
  have h' := (vecEquiv N g).summable_iff.mpr h
  refine h'.congr fun X => ?_
  simp only [Function.comp_apply]
  rw [cexp_thetaArg_eq C P _ _ hdb X]

/-- **Theta inversion in genus $g$:** for $S$ real symmetric positive definite of even size $N = 2k$ and
$Z \in \mathbb H_g$,
$$\Theta_S(Z) = \det(S)^{-g/2}\,\det(Z/i)^{-k}\,\Theta_{S^{-1}}(-Z^{-1}).$$
Here $Z/i = (-i)Z$, and $\det(Z/i)^{-k}$ is an integer power (no square root). -/
@[kb "freitag1983" "Ch. I, Anhang (Theta-Transformationsformel $\\vartheta(S^{-1}, -Z^{-1}) = \\det(S)^{n/2}\\det(Z/i)^{m/2}\\vartheta(S, Z)$) [unverified]"]
theorem thetaG_inversion (k : ℕ) {S : Matrix (Fin (2 * k)) (Fin (2 * k)) ℝ} (hS : S.PosDef)
    {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelH g) :
    thetaG S Z = ((Real.sqrt S.det)⁻¹ ^ g : ℝ) * (det ((-I) • Z))⁻¹ ^ k * thetaG S⁻¹ (-Z⁻¹) := by
  obtain ⟨C, rfl, hC⟩ := exists_eq_transpose_mul hS
  obtain ⟨P, lam, hP, rfl⟩ := exists_siegel_diag hZ
  have hd : ∀ l, (fun k => (lam k : ℂ) + I) l ≠ 0 := fun l h => by
    have := congrArg Complex.im h
    simp at this
  have hdb : ∀ l, (π : ℂ) * I * (fun k => (lam k : ℂ) + I) l = -π * (1 - I * lam l) :=
    fun l => hdb_lam _
  have hdb' : ∀ l, (π : ℂ) * I * (fun l => -((fun k => (lam k : ℂ) + I) l)⁻¹) l =
      -π * (fun l => (1 - I * (lam l : ℂ))⁻¹) l := by
    intro l
    have h1 : ((lam l : ℂ) + I) = I * (1 - I * lam l) := by
      linear_combination (lam l : ℂ) * Complex.I_sq
    show (π : ℂ) * I * (-((lam l : ℂ) + I)⁻¹) = -π * (1 - I * lam l)⁻¹
    have h3 : I * (I * (1 - I * (lam l : ℂ)))⁻¹ = (1 - I * (lam l : ℂ))⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
    rw [h1]
    calc (π : ℂ) * I * -(I * (1 - I * (lam l : ℂ)))⁻¹ = -π * (I * (I * (1 - I * (lam l : ℂ)))⁻¹) := by ring
      _ = _ := by rw [h3]
  have hbJ : ∀ j : Fin (2 * k) × Fin g, 0 < ((fun j : Fin (2 * k) × Fin g => 1 - I * (lam j.2 : ℂ)) j).re :=
    fun j => by simp
  have key := QuadFormsKB.HilbertModular.tsum_gaussAt (gaussMat C P) (gaussMat (C⁻¹)ᵀ (P⁻¹)ᵀ)
    (gaussMat_transpose_mul C P hC hP) _ hbJ
  have e1 := thetaG_eq_gauss C P _ _ hdb
  have e2 := thetaG_eq_gauss (C⁻¹)ᵀ (P⁻¹)ᵀ _ _ hdb'
  rw [inv_gram C, neg_inv_siegel_diag P hP _ hd, e2, e1, key]
  rw [det_smul_siegel_diag]
  have hconst : (((|(gaussMat C P).det|)⁻¹ : ℝ) : ℂ) *
        ∏ j : Fin (2 * k) × Fin g, ((fun j : Fin (2 * k) × Fin g => 1 - I * (lam j.2 : ℂ)) j)⁻¹ ^ (1 / 2 : ℂ) =
      (((Real.sqrt (Cᵀ * C).det)⁻¹ ^ g : ℝ) : ℂ) *
        ((P.det : ℂ) ^ 2 * ∏ l, (1 - I * (lam l : ℂ)))⁻¹ ^ k := by
    rw [prod_half_cpow k (fun l => 1 - I * (lam l : ℂ)) , det_gaussMat, Matrix.det_mul,
      Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs, abs_mul, abs_pow, abs_pow]
    push_cast
    rw [mul_inv, mul_inv, mul_pow, inv_pow, inv_pow, inv_pow]
    have hp : ((|P.det| : ℝ) : ℂ) ^ (2 * k) = ((P.det : ℂ) ^ 2) ^ k := by
      rw [pow_mul, ← Complex.ofReal_pow, sq_abs]; push_cast; rfl
    rw [hp]; ring
  rw [hconst]

/-! ### Integral lattices -/

/-- **Even unimodular lattices (genus $g$):** for $S \in M_N(\mathbb Z)$ symmetric positive definite with $\det S = 1$,
$N = 2k$, and $Z \in \mathbb H_g$,
$$\Theta_S(-Z^{-1}) = \det(Z/i)^{k}\,\Theta_S(Z).$$
(For an even unimodular lattice $8 \mid N$; only $\det S = 1$ and $N$ even are used.) -/
@[kb "freitag1983" "Ch. I, Anhang (theta series of an even unimodular lattice under $Z \\mapsto -Z^{-1}$) [unverified]"]
theorem thetaG_neg_inv (k : ℕ) {S : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ} (hSsymm : Sᵀ = S)
    (hS : (S.map ((↑) : ℤ → ℝ)).PosDef) (hdet : S.det = 1) {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelH g) :
    thetaG (S.map ((↑) : ℤ → ℝ)) (-Z⁻¹) = det ((-I) • Z) ^ k * thetaG (S.map ((↑) : ℤ → ℝ)) Z := by
  have hD := det_smul_siegel_ne_zero hZ
  have hdetR : (S.map ((↑) : ℤ → ℝ)).det = 1 := by
    have := (Int.castRingHom ℝ).map_det S
    rw [hdet] at this
    simpa using this.symm
  have h := thetaG_inversion k hS hZ
  rw [hdetR, Real.sqrt_one, inv_one, one_pow, inv_map_int hdet, thetaG_adjugate hSsymm hdet] at h
  rw [h]
  simp only [Complex.ofReal_one, one_mul, inv_pow]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hD), one_mul]

/-- **Integral translations:** for $S \in M_N(\mathbb Z)$ symmetric with even diagonal and $B \in M_g(\mathbb Z)$ symmetric,
$\Theta_S(Z + B) = \Theta_S(Z)$. -/
@[kb "freitag1983" "Ch. I (invariance of $\\vartheta(S, Z)$ under $Z \\mapsto Z + B$, $S$ even) [unverified]"]
theorem thetaG_add_int {S : Matrix (Fin N) (Fin N) ℤ} (hSsymm : Sᵀ = S) (hSeven : ∀ i, Even (S i i))
    {B : Matrix (Fin g) (Fin g) ℤ} (hB : Bᵀ = B) (Z : Matrix (Fin g) (Fin g) ℂ) :
    thetaG (S.map ((↑) : ℤ → ℝ)) (Z + cZ B) = thetaG (S.map ((↑) : ℤ → ℝ)) Z := by
  unfold thetaG
  refine tsum_congr fun X => ?_
  have hcast : (cZ X)ᵀ * cR (S.map ((↑) : ℤ → ℝ)) * cZ X =
      cZ (Xᵀ * S * X) := by
    ext i j
    simp [Matrix.mul_apply]
  set T : Matrix (Fin g) (Fin g) ℤ := Xᵀ * S * X with hT
  have hTsymm : ∀ i j, T i j = T j i := by
    intro i j
    have : Tᵀ = T := by
      rw [hT]; simp [Matrix.transpose_mul, hSsymm, Matrix.mul_assoc]
    have h2 := congrFun (congrFun this i) j
    rw [Matrix.transpose_apply] at h2
    exact h2.symm
  have hTdiag : ∀ i, Even (T i i) := by
    intro i
    have h := even_sum_sym (n := N) (fun a b => X a i * S a b * X b i)
      (fun a b => by
        have h2 := congrFun (congrFun hSsymm a) b
        rw [Matrix.transpose_apply] at h2
        rw [h2]; ring)
    have hsum : T i i = ∑ a, ∑ b, X a i * S a b * X b i := by
      simp [hT, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hdiag : Even (∑ a, X a i * S a a * X a i) :=
      Finset.sum_induction _ Even (fun _ _ => Even.add) (show Even (0:ℤ) from ⟨0, rfl⟩)
        (fun a _ => ((hSeven a).mul_left (X a i)).mul_right (X a i))
    rw [hsum]
    have := h.add hdiag
    simpa using this
  have hB' : ∀ i j, B i j = B j i := by
    intro i j
    have h2 := congrFun (congrFun hB i) j
    rw [Matrix.transpose_apply] at h2
    exact h2.symm
  have htr : Even (trace (T * B)) := by
    have h := even_sum_sym (n := g) (fun a b => T a b * B b a)
      (fun a b => by rw [hTsymm a b, hB' a b])
    have hdiag : Even (∑ a, T a a * B a a) :=
      Finset.sum_induction _ Even (fun _ _ => Even.add) (show Even (0:ℤ) from ⟨0, rfl⟩)
        (fun a _ => (hTdiag a).mul_right (B a a))
    have := h.add hdiag
    simpa [Matrix.trace, Matrix.mul_apply] using this
  obtain ⟨m, hm⟩ := htr
  have hcexp : thetaArg (S.map ((↑) : ℤ → ℝ)) (Z + cZ B) (cZ X) =
      thetaArg (S.map ((↑) : ℤ → ℝ)) Z (cZ X) + (((m + m : ℤ)) : ℂ) * (π * I) := by
    unfold thetaArg
    rw [hcast, Matrix.mul_add, Matrix.trace_add]
    have : trace (cZ T * cZ B) = (trace (T * B) : ℤ) := by
      simp [Matrix.trace, Matrix.mul_apply]
    rw [this, hm]
    push_cast
    ring
  rw [hcexp, Complex.exp_add]
  have : (((m + m : ℤ)) : ℂ) * (π * I) = (m : ℤ) * (2 * π * I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Unimodular change of basis:** for $A \in \mathrm{GL}_g(\mathbb Z)$, $\Theta_S(AZA^{\mathsf T}) = \Theta_S(Z)$. -/
@[kb "freitag1983" "Ch. I (invariance of $\\vartheta(S, Z)$ under $Z \\mapsto Z[U]$, $U$ unimodular) [unverified]"]
theorem thetaG_conj (S : Matrix (Fin N) (Fin N) ℝ) (A : GL (Fin g) ℤ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    thetaG S (cZ (A : Matrix (Fin g) (Fin g) ℤ) * Z * (cZ (A : Matrix (Fin g) (Fin g) ℤ))ᵀ) = thetaG S Z := by
  unfold thetaG
  refine Eq.trans ?_ ((mulRightGL (N := N) A).tsum_eq (fun X => cexp (thetaArg S Z (cZ X))))
  refine tsum_congr fun X => ?_
  show _ = cexp (thetaArg S Z (cZ (mulRightGL A X)))
  rw [cZ_mulRightGL]
  unfold thetaArg
  rw [trace_conj_aux]

end QuadFormsKB.WeilRep.Genus
