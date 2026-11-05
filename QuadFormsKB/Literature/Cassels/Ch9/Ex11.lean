/-
# Cassels, Chapter 9, Example 11: indefinite unimodular forms (Serre's classification)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, *Examples*, Ex. 11, p. 164 (attributed to Serre 1964,
1970). In this example $f, g, h$ denote classically integral forms of determinant $\pm 1$.

**Conventions.** A form is `f : QuadForm ℤ n` (a polynomial $\sum_{i \le j} c_{ij}x_ix_j$; indices are 0-based, variables
$x_0, \dots, x_{n-1}$, so Cassels' $y_1, y_2$ are $y_0, y_1$ here). *Classically integral of determinant $\pm 1$* is
`IsUnimodularCI`: $f(\mathbf x) = \mathbf x^{\mathsf T}F\mathbf x$ for a symmetric integer matrix $F$ (Cassels' $(f_{ij})$,
`Siegel.casselsMat f`) with $\det F = \pm 1$. *Indefinite* (`IsIndefinite`): $f$ takes a positive and a negative value on
$\mathbb R^n$ (this forces $n \ge 2$, so a form in $2 + m$ variables is used throughout). *Properly primitive* and *improperly
primitive* are `Siegel.IsProperlyPrimitive`, `Siegel.IsImproperlyPrimitive` (Ch. 9, §1: for determinant $\pm 1$ these say that
some, respectively no, diagonal coefficient $f_{ii}$ is odd; primitivity is automatic for $n \ge 1$). *Equivalent* is
$\mathrm{GL}_n(\mathbb Z)$-equivalence `Siegel.IntEquiv`; *$\mathbb R$-equivalent* is `QuadForm.IsometricIn ℝ`. The forms
$y_1^2 - y_2^2 + g(\mathbf z)$ and $2y_1y_2 + g(\mathbf z)$ are `QuadForm.orthSum oddPlane g` and `QuadForm.orthSum hypPlane g`
(the sum of the two-variable form `oddPlane` $= y_0^2 - y_1^2$, respectively `hypPlane` $= 2y_0y_1$, with $g$).

**Proves (unconditionally).**
* (i) `ex11_i`: an indefinite properly primitive unimodular form is equivalent to `oddPlane ⊥ g` with $g$ unimodular.
* (iii) `ex11_iii`: an indefinite improperly primitive unimodular form is equivalent to `hypPlane ⊥ g` with $g$ unimodular and
  all diagonal coefficients even (so improperly primitive for $m \ge 1$).
* Isotropy of indefinite unimodular forms (`isIsotropicZ_of_indefinite`; needed for Cassels' hint, Ex. 9): elementary for $2$
  variables (`isIsotropicZ_of_dim_two`), Meyer's theorem (`Cassels.Ch6.meyer`) for $\ge 5$ variables, and for $3$ and $4$
  variables `isotropicIn_rat_three`, `isotropicIn_rat_four` (`indefiniteIsotropic34`): isotropy over $\mathbb R$ (indefinite) and over
  $\mathbb Q_p$ for odd $p$ (Chevalley–Warning modulo $p$, Hensel's lemma: `exists_padic_zero`), and over $\mathbb Q_2$ by Hilbert
  reciprocity (`hilbert_eq_at_of_eq_elsewhere`; for $4$ variables the criterion `isotropic_four_of_symbols` from the local
  classification and $-1 \notin \mathbb Q_2^{\times 2}$), then Hasse–Minkowski in $3$ and $4$ variables.
* Helpers: `exists_normal_form` (Cassels' hint, Ex. 9: `Siegel.ex9`); `split_form`, `split_core` (splitting a unimodular plane off
  a unimodular form, via the orthogonal complement of the plane as a free $\mathbb Z$-module of rank $n - 2$);
  `posDef_or_posDef_neg` (a unimodular form which is not indefinite is definite); `isometricIn_real_of_posDef` (Sylvester's law
  for positive definite forms).

**Named statements (proved in `Ch9/Ex11Serre.lean` and `Ch9/Ex11Cancel.lean`).**
* (ii) `Ex11_ii` and (iv) `Ex11_iv` are stated faithfully as `Prop`-valued definitions. They are the substance of Serre's
  classification (odd indefinite unimodular forms are determined by their signature; the stable equivalence
  $\langle 1, -1\rangle \perp g_1 \cong \langle 1, -1\rangle \perp g_2 \Rightarrow H \perp g_1 \cong H \perp g_2$ for even $g_i$). A proof
  needs the classification of unimodular $\mathbb Z_p$-lattices and one class in the genus for indefinite lattices (spinor
  norms of unimodular lattices, strong approximation); Cassels calls the proof of (iv) "rather difficult".

**Conditional results.**
* (v) `ex11_v` (equivalence over $\mathbb Z$ of $\mathbb R$-equivalent indefinite improperly primitive forms) is proved from
  `Ex11_ii` and `Ex11_iv`, exactly as Cassels indicates ("(iv) permits the reduction of (v) to (ii)").
* (vi) `ex11_vi` (either $f$ or $-f$ is a sum of hyperbolic planes and copies of a positive definite form in $8$ variables) is
  proved from `Ex11_ii` and `Ex11_iv`, with $h = E_8$ (`e8C`, the form $\mathbf x^{\mathsf T}C\mathbf x$ for the Cartan matrix $C$ of
  $E_8$); the target `IsHypE8Sum` allows equivalence by $\mathrm{GL}_n(\mathbb Z)$.

**Reconstructed / updates.** Cassels' hint for (i), (iii) is "cf. example 9", which needs an isotropic vector. *Update (proof gap
in the hint):* for $n \ge 5$ this is Meyer's theorem and for $n = 2$ an elementary computation, but for $n = 3, 4$ it needs the
Hasse–Minkowski theorem together with Hilbert reciprocity (an indefinite unimodular form is not locally isotropic at $2$ by a
local argument alone, e.g. $x^2 + y^2 + z^2$ over $\mathbb Q_2$); this is supplied here. For $m = 0$ the "improperly primitive"
form $g$ in no variables is not primitive in the library's sense (the empty gcd is $0$), so in (iv) and (v) that case is treated
separately.
-/
import QuadFormsKB.Literature.Cassels.Ch9Examples2
import QuadFormsKB.Literature.Cassels.Ch6.Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec8Int
import QuadFormsKB.Literature.Cassels.Ch9Examples6
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Siegel.ThetaCuspidal

open Matrix Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch9Ex11

open QuadFormsKB QuadFormsKB.Siegel


variable {m : ℕ}

/-- Helper: the $2 \times 2$ Gram matrix of a pair of vectors $\mathbf u, \mathbf v \in \mathbb Z^{2+m}$ for a symmetric matrix $A$: entries $\mathbf u^{\mathsf T}A\mathbf u$, $\mathbf u^{\mathsf T}A\mathbf v$, $\mathbf v^{\mathsf T}A\mathbf u$, $\mathbf v^{\mathsf T}A\mathbf v$. -/
def gram2 (A : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (u v : Fin (2 + m) → ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of fun i j => (![u, v] i) ⬝ᵥ A *ᵥ (![u, v] j)

/-- Helper: the $2 \times (2+m)$ matrix with rows $\mathbf u^{\mathsf T}A$ and $\mathbf v^{\mathsf T}A$. -/
def rowsM (A : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (u v : Fin (2 + m) → ℤ) :
    Matrix (Fin 2) (Fin (2 + m)) ℤ :=
  Matrix.of fun i => (![u, v] i) ᵥ* A

/-- Helper: the $(2+m) \times 2$ matrix with columns $\mathbf u$ and $\mathbf v$. -/
def colsM (u v : Fin (2 + m) → ℤ) : Matrix (Fin (2 + m)) (Fin 2) ℤ :=
  Matrix.of fun i j => (![u, v] j) i

/-- Helper: $(\text{rows})(\text{columns}) = $ the Gram matrix of the pair $(\mathbf u, \mathbf v)$, i.e. `rowsM A u v * colsM u v = gram2 A u v`. -/
lemma rowsM_mul_colsM (A : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (u v : Fin (2 + m) → ℤ) :
    rowsM A u v * colsM u v = gram2 A u v := by
  ext i j
  simp only [rowsM, colsM, gram2, Matrix.mul_apply, Matrix.of_apply]
  rw [Matrix.dotProduct_mulVec]
  rfl

/-- Helper: the matrix with columns $\mathbf u, \mathbf v$ sends $(a_0, a_1)$ to $a_0\mathbf u + a_1\mathbf v$. -/
lemma colsM_mulVec (u v : Fin (2 + m) → ℤ) (a : Fin 2 → ℤ) :
    colsM u v *ᵥ a = a 0 • u + a 1 • v := by
  ext i
  simp [colsM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Helper: the $i$-th entry of `rowsM A u v *ᵥ y` is the pairing of the $i$-th vector of the pair $(\mathbf u, \mathbf v)$ with $\mathbf y$ through $A$. -/
lemma rowsM_mulVec (A : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (u v : Fin (2 + m) → ℤ)
    (y : Fin (2 + m) → ℤ) (i : Fin 2) :
    (rowsM A u v *ᵥ y) i = (![u, v] i) ⬝ᵥ A *ᵥ y := by
  simp [rowsM, Matrix.mulVec, Matrix.dotProduct_mulVec]


section Split

variable (A : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (u v : Fin (2 + m) → ℤ)

/-- Helper: the orthogonal complement $\{\mathbf y : \mathbf u^{\mathsf T}A\mathbf y = \mathbf v^{\mathsf T}A\mathbf y = 0\}$ of the plane spanned by $\mathbf u, \mathbf v$, a $\mathbb Z$-submodule of $\mathbb Z^{2+m}$. -/
def kerR : Submodule ℤ (Fin (2 + m) → ℤ) := LinearMap.ker (rowsM A u v).mulVecLin

/-- Helper: membership in the orthogonal complement `kerR A u v` of the plane spanned by $\mathbf u, \mathbf v$. -/
lemma mem_kerR {y : Fin (2 + m) → ℤ} : y ∈ kerR A u v ↔ rowsM A u v *ᵥ y = 0 := by
  simp [kerR]

variable {A u v}
variable (hP : IsUnit (gram2 A u v).det)
include hP

/-- Helper: the Gram matrix of a pair with unit determinant has an integral right inverse. -/
lemma gram2_mul_inv : gram2 A u v * (gram2 A u v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP

/-- Helper: the Gram matrix of a pair with unit determinant has an integral left inverse. -/
lemma gram2_inv_mul : (gram2 A u v)⁻¹ * gram2 A u v = 1 := Matrix.nonsing_inv_mul _ hP

omit hP in
/-- Helper: `rowsM A u v *ᵥ (colsM u v *ᵥ w) = gram2 A u v *ᵥ w`. -/
lemma rows_cols_mulVec (w : Fin 2 → ℤ) : rowsM A u v *ᵥ (colsM u v *ᵥ w) = gram2 A u v *ᵥ w := by
  rw [Matrix.mulVec_mulVec, rowsM_mul_colsM]

/-- Helper: the $\mathbb Z$-linear isomorphism $\mathbb Z^{2} \times (\text{complement}) \to \mathbb Z^{2+m}$, $(\mathbf a, \mathbf z) \mapsto a_0\mathbf u + a_1\mathbf v + \mathbf z$ (its inverse uses the integral inverse of the Gram matrix of the plane). -/
noncomputable def splitEquiv : ((Fin 2 → ℤ) × kerR A u v) ≃ₗ[ℤ] (Fin (2 + m) → ℤ) where
  toFun p := colsM u v *ᵥ p.1 + (p.2 : Fin (2 + m) → ℤ)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.mulVec_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.mulVec_smul, RingHom.id_apply, smul_add]
  invFun y :=
    ((gram2 A u v)⁻¹ *ᵥ (rowsM A u v *ᵥ y),
      ⟨y - colsM u v *ᵥ ((gram2 A u v)⁻¹ *ᵥ (rowsM A u v *ᵥ y)), by
        rw [mem_kerR, Matrix.mulVec_sub, Matrix.mulVec_mulVec, rowsM_mul_colsM, Matrix.mulVec_mulVec,
          gram2_mul_inv hP, Matrix.one_mulVec, sub_self]⟩)
  left_inv p := by
    obtain ⟨a, z, hz⟩ := p
    have hz' : rowsM A u v *ᵥ z = 0 := (mem_kerR A u v).mp hz
    have h1 : rowsM A u v *ᵥ (colsM u v *ᵥ a + z) = gram2 A u v *ᵥ a := by
      rw [Matrix.mulVec_add, hz', add_zero, Matrix.mulVec_mulVec, rowsM_mul_colsM]
    have ha : (gram2 A u v)⁻¹ *ᵥ (rowsM A u v *ᵥ (colsM u v *ᵥ a + z)) = a := by
      rw [h1, Matrix.mulVec_mulVec, gram2_inv_mul hP, Matrix.one_mulVec]
    refine Prod.ext ha (Subtype.ext ?_)
    show colsM u v *ᵥ a + z - colsM u v *ᵥ ((gram2 A u v)⁻¹ *ᵥ (rowsM A u v *ᵥ (colsM u v *ᵥ a + z))) = z
    rw [ha]; abel
  right_inv y := by
    simp only
    abel


/-- Helper: when the Gram matrix of $(\mathbf u, \mathbf v)$ is invertible over $\mathbb Z$, the orthogonal complement of the plane has rank $m$ (the splitting equivalence has $\mathbb Z^{2} \times \text{complement} \cong \mathbb Z^{2+m}$). -/
lemma finrank_kerR : finrank ℤ (kerR A u v) = m := by
  have h := LinearEquiv.finrank_eq (splitEquiv hP)
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

/-- Helper: a $\mathbb Z$-basis of the orthogonal complement, indexed by `Fin m`. -/
noncomputable def bK : Basis (Fin m) ℤ (kerR A u v) := Module.finBasisOfFinrankEq ℤ _ (finrank_kerR hP)

/-- Helper: the $\mathbb Z$-basis $(\mathbf u, \mathbf v, \text{complement basis})$ of $\mathbb Z^{2+m}$, indexed by `Fin (2 + m)`. -/
noncomputable def bb : Basis (Fin (2 + m)) ℤ (Fin (2 + m) → ℤ) :=
  (((Pi.basisFun ℤ (Fin 2)).prod (bK hP)).map (splitEquiv hP)).reindex finSumFinEquiv

/-- Helper: the first two vectors of the basis `bb` are $\mathbf u$ and $\mathbf v$. -/
lemma bb_castAdd (a : Fin 2) : bb hP (Fin.castAdd m a) = ![u, v] a := by
  simp [bb, splitEquiv, colsM_mulVec]
  fin_cases a <;> simp

/-- Helper: the last $m$ vectors of the basis `bb` are the basis vectors of the orthogonal complement. -/
lemma bb_natAdd (b : Fin m) : bb hP (Fin.natAdd 2 b) = ((bK hP b : kerR A u v) : Fin (2 + m) → ℤ) := by
  simp [bb, splitEquiv]

end Split


/-- Helper: $(M\mathbf x)^{\mathsf T}A(N\mathbf y) = \mathbf x^{\mathsf T}(M^{\mathsf T}AN)\mathbf y$ over $\mathbb Z$. -/
lemma bil_mulVec {a b n : Type*} [Fintype a] [Fintype b] [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (M : Matrix n a ℤ) (N : Matrix n b ℤ) (x : a → ℤ) (y : b → ℤ) :
    (M *ᵥ x) ⬝ᵥ A *ᵥ (N *ᵥ y) = x ⬝ᵥ (Mᵀ * A * N) *ᵥ y := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Mᵀ, Matrix.vecMul_transpose]


section Mat

variable {A : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ} {u v : Fin (2 + m) → ℤ}
variable (hP : IsUnit (gram2 A u v).det)

/-- Helper: the matrix whose columns are the basis vectors of the orthogonal complement. -/
noncomputable def Wm : Matrix (Fin (2 + m)) (Fin m) ℤ :=
  Matrix.of fun i b => ((bK hP b : kerR A u v) : Fin (2 + m) → ℤ) i

/-- Helper: the change-of-basis matrix whose columns are the vectors of `bb`. -/
noncomputable def Tm : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ :=
  (Pi.basisFun ℤ (Fin (2 + m))).toMatrix (bb hP)

/-- Helper: the entries of the change-of-basis matrix `Tm` are the coordinates of the basis vectors `bb`. -/
lemma Tm_apply (i j : Fin (2 + m)) : Tm hP i j = bb hP j i := by
  simp [Tm, Basis.toMatrix_apply]

/-- Helper: `Tm` is the matrix with columns $\mathbf u, \mathbf v$ followed by the columns of `Wm`, reindexed by `Fin (2 + m)`. -/
lemma Tm_eq : Tm hP = (Matrix.fromCols (colsM u v) (Wm hP)).submatrix id finSumFinEquiv.symm := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · simp [Tm_apply, bb_castAdd, colsM]
  · simp [Tm_apply, bb_natAdd, Wm]

/-- Helper: the change-of-basis matrix `Tm` has a unit determinant (its columns form a $\mathbb Z$-basis of $\mathbb Z^{2+m}$). -/
lemma isUnit_det_Tm : IsUnit (Tm hP).det := by
  have := (Pi.basisFun ℤ (Fin (2 + m))).isUnit_det (bb hP)
  rwa [Basis.det_apply] at this

omit hP in
/-- Helper: `rowsM A u v` is $(\text{columns})^{\mathsf T}A$. -/
lemma rowsM_eq : rowsM A u v = (colsM u v)ᵀ * A := by
  ext i k
  simp [rowsM, colsM, Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- Helper: the columns of `Wm` are orthogonal to $\mathbf u$ and $\mathbf v$. -/
lemma rows_Wm : rowsM A u v * Wm hP = 0 := by
  ext i b
  have h := congrFun ((mem_kerR A u v).mp (bK hP b).2) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Wm] using h


/-- Helper: the cross terms between the plane and the complement vanish. -/
lemma cross1 : (colsM u v)ᵀ * A * Wm hP = 0 := by
  rw [← rowsM_eq]; exact rows_Wm hP

/-- Helper: the cross terms between the complement and the plane vanish (using symmetry of $A$). -/
lemma cross2 (hA : A.IsSymm) : (Wm hP)ᵀ * A * colsM u v = 0 := by
  have h := congrArg Matrix.transpose (cross1 hP)
  simpa [Matrix.transpose_mul, hA.eq, Matrix.mul_assoc] using h

omit hP in
/-- Helper: the Gram matrix of the plane is $(\text{columns})^{\mathsf T}A(\text{columns})$. -/
lemma colsM_gram : (colsM u v)ᵀ * A * colsM u v = gram2 A u v := by
  rw [← rowsM_eq, rowsM_mul_colsM]

/-- Helper: in the basis $(\mathbf u, \mathbf v, \text{complement})$ the Gram matrix is block diagonal. -/
lemma gram_blocks (hA : A.IsSymm) :
    (Matrix.fromCols (colsM u v) (Wm hP))ᵀ * A * (Matrix.fromCols (colsM u v) (Wm hP)) =
      Matrix.fromBlocks (gram2 A u v) 0 0 ((Wm hP)ᵀ * A * Wm hP) := by
  rw [Matrix.transpose_fromCols, Matrix.mul_assoc, Matrix.mul_fromCols, Matrix.fromRows_mul_fromCols]
  simp only [← Matrix.mul_assoc]
  rw [colsM_gram, cross1 hP, cross2 hP hA]

/-- Helper: $T^{\mathsf T}AT$ is the block-diagonal matrix $\operatorname{diag}(G, B)$ reindexed by `Fin (2 + m)`. -/
lemma gram_Tm (hA : A.IsSymm) :
    (Tm hP)ᵀ * A * Tm hP = (Matrix.fromBlocks (gram2 A u v) 0 0 ((Wm hP)ᵀ * A * Wm hP)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [← gram_blocks hP hA, Tm_eq, Matrix.transpose_submatrix]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]


/-- Helper: the Gram matrix $B$ of the orthogonal complement has a unit determinant. -/
lemma isUnit_det_B (hA : A.IsSymm) (hAd : IsUnit A.det) : IsUnit ((Wm hP)ᵀ * A * Wm hP).det := by
  have h1 := congrArg Matrix.det (gram_Tm hP hA)
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose] at h1
  have h2 : IsUnit ((gram2 A u v).det * ((Wm hP)ᵀ * A * Wm hP).det) := by
    rw [← h1]
    exact ((isUnit_det_Tm hP).mul hAd).mul (isUnit_det_Tm hP)
  exact isUnit_of_mul_isUnit_right h2

include hP in
/-- Helper (the splitting of a unimodular plane, in matrix form): let $A$ be a symmetric integer matrix of size $2 + m$ with unit determinant and $\mathbf u, \mathbf v \in \mathbb Z^{2+m}$ with unit-determinant Gram matrix $G$ (`gram2 A u v`). Then there are a matrix $T$ of unit determinant with $Te_0 = \mathbf u$, $Te_1 = \mathbf v$ and a symmetric integer matrix $B$ of size $m$ with unit determinant whose diagonal entries are values of $A$, such that $(T\mathbf x)^{\mathsf T}A(T\mathbf x) = \mathbf x_{\mathrm{plane}}^{\mathsf T}G\mathbf x_{\mathrm{plane}} + \mathbf x_{\mathrm{rest}}^{\mathsf T}B\mathbf x_{\mathrm{rest}}$ (0-based: $\mathbf x_{\mathrm{plane}} = (x_0, x_1)$, $\mathbf x_{\mathrm{rest}} = (x_2, \dots, x_{m+1})$). The proof splits $\mathbb Z^{2+m}$ as the plane plus its orthogonal complement (a free module of rank $m$) using the integral inverse of $G$. -/
theorem split_core (hA : A.IsSymm) (hAd : IsUnit A.det) :
    ∃ (T : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (B : Matrix (Fin m) (Fin m) ℤ),
      IsUnit T.det ∧ T *ᵥ Pi.single (Fin.castAdd m 0) 1 = u ∧ T *ᵥ Pi.single (Fin.castAdd m 1) 1 = v ∧
      B.IsSymm ∧ IsUnit B.det ∧ (∀ k, ∃ y, B k k = y ⬝ᵥ A *ᵥ y) ∧
      ∀ x : Fin (2 + m) → ℤ, (T *ᵥ x) ⬝ᵥ A *ᵥ (T *ᵥ x) =
        (fun a => x (Fin.castAdd m a)) ⬝ᵥ gram2 A u v *ᵥ (fun a => x (Fin.castAdd m a)) +
        (fun b => x (Fin.natAdd 2 b)) ⬝ᵥ B *ᵥ (fun b => x (Fin.natAdd 2 b)) := by
  refine ⟨Tm hP, (Wm hP)ᵀ * A * Wm hP, isUnit_det_Tm hP, ?_, ?_, ?_, isUnit_det_B hP hA hAd, ?_, ?_⟩
  · ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Tm_apply, bb_castAdd]
  · ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Tm_apply, bb_castAdd]
  · simp [Matrix.IsSymm, Matrix.transpose_mul, hA.eq, Matrix.mul_assoc]
  · intro k
    refine ⟨Wm hP *ᵥ Pi.single k 1, ?_⟩
    rw [bil_mulVec]
    simp [Matrix.mulVec_single_one, Matrix.mulVec, dotProduct, Pi.single_apply]
  · intro x
    have hT : Tm hP *ᵥ x = colsM u v *ᵥ (fun a => x (Fin.castAdd m a)) +
        Wm hP *ᵥ (fun b => x (Fin.natAdd 2 b)) := by
      rw [Tm_eq, Matrix.submatrix_mulVec_equiv, Matrix.fromCols_mulVec]
      ext i
      simp [Function.comp_def]
    rw [hT, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, bil_mulVec, bil_mulVec,
      bil_mulVec, bil_mulVec, colsM_gram, cross1 hP, cross2 hP hA]
    simp

end Mat


/-! ### Forms, unimodularity, parity -/

section Forms

variable {k n m : ℕ}

/-- Helper: an invertible integer matrix as an element of $\mathrm{GL}_k(\mathbb Z)$. -/
noncomputable def glOfUnit (T : Matrix (Fin k) (Fin k) ℤ) (h : IsUnit T.det) : GL (Fin k) ℤ :=
  Matrix.nonsingInvUnit T h

/-- Helper: the underlying matrix of `glOfUnit T h` is $T$. -/
theorem glOfUnit_val (T : Matrix (Fin k) (Fin k) ℤ) (h : IsUnit T.det) : (glOfUnit T h).val = T := rfl

/-- Helper: the diagonal entry of Cassels' matrix is the diagonal coefficient. -/
theorem casselsMat_diag (f : QuadForm ℤ k) (i : Fin k) : Siegel.casselsMat f i i = f.coeff i i := by
  simp only [Siegel.casselsMat, QuadForm.hessian, Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply]
  omega

/-- Helper: a classically integral form with all diagonal coefficients even takes only even values. -/
theorem even_eval_of_diag {f : QuadForm ℤ k} (hf : IsClassicallyIntegral f) (hd : ∀ i, 2 ∣ f.coeff i i)
    (x : Fin k → ℤ) : 2 ∣ f.eval x := by
  rw [isClassicallyIntegral_iff] at hf
  simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  split_ifs with h
  · have : 2 ∣ f.coeff i j := by
      rcases h.lt_or_eq with h' | rfl
      · exact even_iff_two_dvd.mp (hf i j h')
      · exact hd i
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right this _) _
  · exact dvd_zero _

/-- Helper: the value at a standard basis vector is the diagonal coefficient. -/
theorem eval_single (f : QuadForm ℤ k) (i : Fin k) : f.eval (Pi.single i 1) = f.coeff i i := by
  simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      split_ifs <;> simp [Pi.single_apply, hj.symm]
    · simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs <;> simp [Pi.single_apply, hj]
  · simp

/-- Helper: for a classically integral form, "every diagonal coefficient is even" is the same as "every value is even". -/
theorem diag_even_iff {f : QuadForm ℤ k} (hf : IsClassicallyIntegral f) :
    (∀ i, 2 ∣ f.coeff i i) ↔ ∀ x, 2 ∣ f.eval x :=
  ⟨even_eval_of_diag hf, fun h i => by rw [← eval_single]; exact h _⟩

/-- Helper: equivalent classically integral forms have the same parity of values. -/
theorem diag_even_of_intEquiv {f g : QuadForm ℤ k} (hf : IsClassicallyIntegral f)
    (hg : IsClassicallyIntegral g) (h : IntEquiv f g) (hd : ∀ i, 2 ∣ f.coeff i i) : ∀ i, 2 ∣ g.coeff i i := by
  obtain ⟨T, hT⟩ := h
  rw [diag_even_iff hg]
  intro x
  rw [← hT x]
  exact even_eval_of_diag hf hd _

/-- Helper: `IsUnimodularCI` is invariant under integral equivalence among classically integral forms. -/
theorem det_casselsMat_of_intEquiv {f g : QuadForm ℤ k} (hf : IsClassicallyIntegral f)
    (hg : IsClassicallyIntegral g) (h : IntEquiv f g) : (Siegel.casselsMat g).det = (Siegel.casselsMat f).det := by
  obtain ⟨T, hT⟩ := h
  have := (Siegel.eval_mulVec_iff_casselsMat hf hg T.val).mp hT
  rw [← this, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hd : T.val.det = 1 ∨ T.val.det = -1 := Siegel.det_GL_int_eq T
  rcases hd with hd | hd <;> rw [hd] <;> ring

end Forms

/-! ### Definitions of the example -/

section Defs

variable {n m : ℕ}

/-- **Classically integral of determinant $\pm 1$** (Cassels' convention in Ch. 9, Ex. 11: "$f, g, h$ denote classically
integral forms of determinant $\pm 1$"). For a form $f$ in $n$ variables this says: $f(\mathbf x) = \mathbf x^{\mathsf T}F\mathbf x$ for a
symmetric integer matrix $F$ (Cassels' matrix $(f_{ij})$, `casselsMat f`) with $\det F = \pm 1$. -/
def IsUnimodularCI (f : QuadForm ℤ n) : Prop :=
  IsClassicallyIntegral f ∧ ((Siegel.casselsMat f).det = 1 ∨ (Siegel.casselsMat f).det = -1)

/-- **Indefinite** (Cassels: *a real form is indefinite if it takes both signs*): the integral form $f$, read over $\mathbb R$,
has $f(\mathbf x) > 0$ and $f(\mathbf y) < 0$ for some real vectors $\mathbf x, \mathbf y \in \mathbb R^{n}$. In particular $n \ge 2$. -/
def IsIndefinite (f : QuadForm ℤ n) : Prop :=
  (∃ x : Fin n → ℝ, 0 < f.evalIn ℝ x) ∧ ∃ y : Fin n → ℝ, f.evalIn ℝ y < 0

/-- **The odd plane** $y_0^{2} - y_1^{2}$, a form in two variables (Cassels' $y_1^2 - y_2^2$, 0-based variables). -/
def oddPlane : QuadForm ℤ 2 := Siegel.ofGram !![1, 0; 0, -1]

/-- **The hyperbolic plane** $2y_0y_1$, a form in two variables (Cassels' $2y_1y_2$, 0-based variables). -/
def hypPlane : QuadForm ℤ 2 := Siegel.ofGram !![0, 1; 1, 0]

/-- Helper: the values of the odd plane, $y_0^{2} - y_1^{2}$. -/
theorem eval_oddPlane (a : Fin 2 → ℤ) : oddPlane.eval a = a 0 ^ 2 - a 1 ^ 2 := by
  have hs : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [oddPlane, Siegel.eval_ofGram hs]
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
  ring

/-- Helper: the values of the hyperbolic plane, $2y_0y_1$. -/
theorem eval_hypPlane (a : Fin 2 → ℤ) : hypPlane.eval a = 2 * a 0 * a 1 := by
  have hs : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hypPlane, Siegel.eval_ofGram hs]
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
  ring

/-- Helper: the Cassels matrix of the odd plane. -/
theorem casselsMat_oddPlane : Siegel.casselsMat oddPlane = !![1, 0; 0, -1] := by
  have hs : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  exact Siegel.casselsMat_ofGram hs

/-- Helper: the Cassels matrix of the hyperbolic plane. -/
theorem casselsMat_hypPlane : Siegel.casselsMat hypPlane = !![0, 1; 1, 0] := by
  have hs : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  exact Siegel.casselsMat_ofGram hs

/-- Helper: a symmetric matrix of determinant $\pm 1$ gives a form with `IsUnimodularCI`. -/
theorem isUnimodularCI_ofGram {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hd : IsUnit A.det) :
    IsUnimodularCI (Siegel.ofGram A) := by
  refine ⟨Siegel.ci_ofGram hA, ?_⟩
  rw [Siegel.casselsMat_ofGram hA]
  exact Int.isUnit_iff.mp hd

/-- Helper: the Gram matrix of a pair of vectors is symmetric when the matrix is. -/
theorem gram2_isSymm {A : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ} (hA : A.IsSymm) (u v : Fin (2 + m) → ℤ) :
    (gram2 A u v).IsSymm := by
  ext i j
  simp only [gram2, Matrix.transpose_apply, Matrix.of_apply]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm, Matrix.dotProduct_mulVec]

/-- **Splitting off a unimodular plane.** Let $f$ be a classically integral form of determinant $\pm 1$ in $2 + m$ variables and
$\mathbf u, \mathbf v \in \mathbb Z^{2+m}$ vectors whose $2 \times 2$ Gram matrix $G$ (for Cassels' matrix of $f$) has
determinant $\pm 1$. Then there are a form $g$ in $m$ variables, classically integral of determinant $\pm 1$, whose diagonal
coefficients are values of $f$, and $T \in \mathrm{GL}_{2+m}(\mathbb Z)$ with $T e_0 = \mathbf u$, $T e_1 = \mathbf v$ and
$f(T\mathbf x) = (\mathbf x_{\mathrm{plane}})^{\mathsf T} G\, \mathbf x_{\mathrm{plane}} + g(x_2, \dots, x_{m+1})$, where
$\mathbf x_{\mathrm{plane}} = (x_0, x_1)$ (0-based). The plane form is `Siegel.ofGram G`. -/
theorem split_form (f : QuadForm ℤ (2 + m)) (hf : IsUnimodularCI f) (u v : Fin (2 + m) → ℤ)
    (hP : IsUnit (gram2 (Siegel.casselsMat f) u v).det) :
    ∃ g : QuadForm ℤ m, IsUnimodularCI g ∧ (∀ k, ∃ y, g.coeff k k = f.eval y) ∧
      ∃ T : GL (Fin (2 + m)) ℤ, T.val *ᵥ Pi.single (Fin.castAdd m 0) 1 = u ∧
        T.val *ᵥ Pi.single (Fin.castAdd m 1) 1 = v ∧
        ∀ x, f.eval (T.val *ᵥ x) =
          (Siegel.ofGram (gram2 (Siegel.casselsMat f) u v)).eval (fun a => x (Fin.castAdd m a)) +
            g.eval (fun b => x (Fin.natAdd 2 b)) := by
  have hA := Siegel.casselsMat_isSymm f
  have hAd : IsUnit (Siegel.casselsMat f).det := by
    rcases hf.2 with h | h <;> rw [h] <;> simp
  obtain ⟨T, B, hT, h1, h2, hB, hBd, hdiag, hev⟩ := split_core hP hA hAd
  refine ⟨Siegel.ofGram B, ⟨Siegel.ci_ofGram hB, ?_⟩, ?_, glOfUnit T hT, h1, h2, ?_⟩
  · rw [Siegel.casselsMat_ofGram hB]
    exact Int.isUnit_iff.mp hBd
  · intro k
    obtain ⟨y, hy⟩ := hdiag k
    refine ⟨y, ?_⟩
    rw [← casselsMat_diag, Siegel.casselsMat_ofGram hB, hy, Siegel.eval_eq_casselsMat hf.1]
  · intro x
    rw [glOfUnit_val, Siegel.eval_eq_casselsMat hf.1, hev x, Siegel.eval_ofGram (gram2_isSymm hA u v),
      Siegel.eval_ofGram hB]

end Defs

/-! ### Isotropy of indefinite unimodular forms -/

section Isotropy

variable {n m : ℕ}

/-- **Isotropic over $\mathbb Z$:** $f(\mathbf x) = 0$ for some nonzero integer vector $\mathbf x \in \mathbb Z^n$. -/
def IsIsotropicZ (f : QuadForm ℤ n) : Prop := ∃ x : Fin n → ℤ, x ≠ 0 ∧ f.eval x = 0

/-- Helper: the value of the form over a field of characteristic $0$ is $\mathbf x^{\mathsf T}F\mathbf x$ for Cassels' matrix
$F$, when the form is classically integral. -/
theorem evalIn_eq_casselsMat (K : Type*) [Field K] [CharZero K] {f : QuadForm ℤ n}
    (hf : IsClassicallyIntegral f) (x : Fin n → K) :
    f.evalIn K x = x ⬝ᵥ ((Siegel.casselsMat f).map (Int.castRingHom K)) *ᵥ x := by
  have h1 := QuadForm.evalIn_eq_dotProduct K f x
  set C : Matrix (Fin n) (Fin n) K := f.coeff.map (algebraMap ℤ K) with hC
  have hH : C + Cᵀ = (2 : K) • ((Siegel.casselsMat f).map (Int.castRingHom K)) := by
    have h := Siegel.hessian_eq_two_smul_casselsMat hf
    ext i j
    have hij := congrFun (congrFun h i) j
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul] at hij
    simp only [hC, Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, eq_intCast, algebraMap_int_eq, Int.coe_castRingHom]
    exact_mod_cast hij
  have h2 : x ⬝ᵥ Cᵀ *ᵥ x = x ⬝ᵥ C *ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  have h3 : (2 : K) * (x ⬝ᵥ C *ᵥ x) = (2 : K) * (x ⬝ᵥ ((Siegel.casselsMat f).map (Int.castRingHom K)) *ᵥ x) := by
    calc (2 : K) * (x ⬝ᵥ C *ᵥ x) = x ⬝ᵥ C *ᵥ x + x ⬝ᵥ Cᵀ *ᵥ x := by rw [h2]; ring
      _ = x ⬝ᵥ (C + Cᵀ) *ᵥ x := by rw [Matrix.add_mulVec, dotProduct_add]
      _ = _ := by rw [hH, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [h1]
  exact mul_left_cancel₀ two_ne_zero h3

/-- Helper: an indefinite unimodular classically integral binary form is isotropic over $\mathbb Z$.

*Proof.* Write Cassels' matrix as $\begin{pmatrix} a & b \\ b & c \end{pmatrix}$. If $ac - b^{2} = 1$ then
$a f(x_0, x_1) = (a x_0 + b x_1)^{2} + x_1^{2} \ge 0$ and $a \ne 0$, so $f$ is semidefinite, contradicting indefiniteness. So
$ac - b^{2} = -1$, and then $f(1 - b, a) = a(1 + ac - b^{2}) = 0$ (for $a \ne 0$), while $f(1, 0) = a = 0$ otherwise. -/
theorem isIsotropicZ_of_dim_two (f : QuadForm ℤ 2) (hf : IsUnimodularCI f) (hind : IsIndefinite f) :
    IsIsotropicZ f := by
  have hsymm := Siegel.casselsMat_isSymm f
  have hev0 : ∀ x : Fin 2 → ℤ, f.eval x = x ⬝ᵥ (Siegel.casselsMat f *ᵥ x) := Siegel.eval_eq_casselsMat hf.1
  have hevR0 : ∀ x : Fin 2 → ℝ, f.evalIn ℝ x =
      x ⬝ᵥ ((Siegel.casselsMat f).map (Int.castRingHom ℝ)) *ᵥ x := evalIn_eq_casselsMat ℝ hf.1
  have hfd := hf.2
  generalize Siegel.casselsMat f = A at *
  have hA10 : A 1 0 = A 0 1 := hsymm.apply 0 1
  have hdet : A.det = A 0 0 * A 1 1 - A 0 1 * A 0 1 := by
    rw [Matrix.det_fin_two, hA10]
  have hev : ∀ x : Fin 2 → ℤ, f.eval x = A 0 0 * x 0 ^ 2 + 2 * A 0 1 * x 0 * x 1 + A 1 1 * x 1 ^ 2 := by
    intro x
    rw [hev0]
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, hA10]
    ring
  have hevR : ∀ x : Fin 2 → ℝ, f.evalIn ℝ x =
      (A 0 0 : ℝ) * x 0 ^ 2 + 2 * (A 0 1 : ℝ) * x 0 * x 1 + (A 1 1 : ℝ) * x 1 ^ 2 := by
    intro x
    rw [hevR0]
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, hA10]
    ring
  rcases hfd with h1 | h1
  · exfalso
    rw [hdet] at h1
    have ha : A 0 0 ≠ 0 := by
      intro h0
      rw [h0] at h1
      nlinarith [sq_nonneg (A 0 1)]
    have hR : ((A 0 0 : ℝ)) * ((A 1 1 : ℝ)) - (A 0 1 : ℝ) * (A 0 1 : ℝ) = 1 := by exact_mod_cast h1
    have key : ∀ x : Fin 2 → ℝ, 0 ≤ (A 0 0 : ℝ) * f.evalIn ℝ x := by
      intro x
      rw [hevR]
      nlinarith [sq_nonneg ((A 0 0 : ℝ) * x 0 + (A 0 1 : ℝ) * x 1), sq_nonneg (x 1)]
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hind
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have : (A 0 0 : ℝ) < 0 := by exact_mod_cast hneg
      nlinarith [key x]
    · have : (0 : ℝ) < A 0 0 := by exact_mod_cast hpos
      nlinarith [key y]
  · rw [hdet] at h1
    by_cases ha : A 0 0 = 0
    · refine ⟨Pi.single 0 1, ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · rw [hev]
        simp [ha]
    · refine ⟨![1 - A 0 1, A 0 0], ?_, ?_⟩
      · intro h
        have := congrFun h 1
        simp at this
        exact ha this
      · rw [hev]
        simp
        linear_combination (A 0 0) * h1

/-- Helper: the form of an integral form over $\mathbb Q$ takes the same real values. -/
theorem evalIn_real_map_rat (f : QuadForm ℤ n) (x : Fin n → ℝ) :
    (f.map (Int.castRingHom ℚ)).evalIn ℝ x = f.evalIn ℝ x := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- Helper: degree $2$ homogeneity of the value of a form over a commutative ring. -/
theorem evalIn_smul {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (Q : QuadForm R n) (c : K)
    (x : Fin n → K) : Q.evalIn K (c • x) = c ^ 2 * Q.evalIn K x := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Helper: a nontrivial rational zero gives a nontrivial integer zero. -/
theorem isIsotropicZ_of_rat (f : QuadForm ℤ n) (h : (f.map (Int.castRingHom ℚ)).IsotropicIn ℚ) :
    IsIsotropicZ f := by
  obtain ⟨x, hx0, hx⟩ := h
  set D : ℕ := ∏ i, (x i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => Rat.den_pos _
  have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = (D : ℚ) * x i := by
    intro i
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun i => (x i).den) (Finset.mem_univ i)
    refine ⟨c * (x i).num, ?_⟩
    rw [hD, hc]
    have := Rat.mul_den_eq_num (x i)
    push_cast
    rw [← this]
    ring
  choose z hz using hint
  refine ⟨z, ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    have h1 := hz i
    rw [h] at h1
    simp at h1
    rcases h1 with h1 | h1
    · exfalso; have : D = 0 := by exact_mod_cast h1
      omega
    · simpa using h1
  · have h1 : ((f.eval z : ℤ) : ℚ) = (D : ℚ) ^ 2 * (f.map (Int.castRingHom ℚ)).evalIn ℚ x := by
      rw [← Lattices.evalIn_rat_intCast]
      have : (fun i => (z i : ℚ)) = (D : ℚ) • x := by
        funext i; simp [hz i]
      rw [this, evalIn_smul]
    rw [hx, mul_zero] at h1
    exact_mod_cast h1

/-- Helper: the rational form of a unimodular classically integral form is nondegenerate. -/
theorem nondegenerate_map_rat {f : QuadForm ℤ n} (hf : IsUnimodularCI f) :
    (f.map (Int.castRingHom ℚ)).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  have h1 : (f.map (Int.castRingHom ℚ)).hessian = f.hessian.map (Int.castRingHom ℚ) := by
    simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
  rw [h1, show ((f.hessian.map (Int.castRingHom ℚ))).det = ((f.hessian.det : ℤ) : ℚ) from
    (RingHom.map_det (Int.castRingHom ℚ) f.hessian).symm]
  rw [Siegel.hessian_eq_two_smul_casselsMat hf.1, Matrix.det_smul, Fintype.card_fin]
  have : (Siegel.casselsMat f).det ≠ 0 := by rcases hf.2 with h | h <;> rw [h] <;> simp
  exact_mod_cast mul_ne_zero (pow_ne_zero _ two_ne_zero) this

/-- **Isotropy for five or more variables** (Meyer's theorem, `Cassels.Ch6.meyer`): an indefinite unimodular classically
integral form in $n \ge 5$ variables has a nontrivial integer zero. -/
theorem isIsotropicZ_of_five_le (f : QuadForm ℤ n) (hn : 5 ≤ n) (hf : IsUnimodularCI f) (hind : IsIndefinite f) :
    IsIsotropicZ f := by
  apply isIsotropicZ_of_rat
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hind
  exact Cassels.Ch6.meyer _ hn (nondegenerate_map_rat hf)
    ⟨x, by rw [evalIn_real_map_rat]; exact hx⟩ ⟨y, by rw [evalIn_real_map_rat]; exact hy⟩

/-- **Isotropy of indefinite unimodular forms in 3 and 4 variables** (the statement; it is proved in
`indefiniteIsotropic34` below, from the Hasse–Minkowski theorem, Hilbert reciprocity and Hensel's lemma): an indefinite
classically integral form of determinant $\pm 1$ in $2 + m$ variables with $m \in \{1, 2\}$ has a nontrivial integer zero. -/
def IndefiniteIsotropic34 : Prop :=
  ∀ m : ℕ, (m = 1 ∨ m = 2) → ∀ f : QuadForm ℤ (2 + m), IsUnimodularCI f → IsIndefinite f → IsIsotropicZ f

end Isotropy

/-! ### Isotropy over $\mathbb Q_p$ ($p$ odd) of unimodular forms in at least three variables -/

section PadicOdd

variable {n : ℕ}


open MvPolynomial in
/-- Helper (Chevalley–Warning): a quadratic form $\mathbf x^{\mathsf T}A\mathbf x$ in $n \ge 3$ variables over $\mathbb F_p$ has a nontrivial zero. -/
theorem exists_nontrivial_zero_zmod (p : ℕ) [Fact p.Prime] (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    ∃ x : Fin n → ZMod p, x ≠ 0 ∧ x ⬝ᵥ A *ᵥ x = 0 := by
  classical
  set P : MvPolynomial (Fin n) (ZMod p) := ∑ i, ∑ j, C (A i j) * X i * X j with hP
  have hdeg : P.totalDegree < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    have h2 : P.totalDegree ≤ 2 := by
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      have h1 : (C (A i j) * X i : MvPolynomial (Fin n) (ZMod p)).totalDegree ≤ 1 := by
        refine (totalDegree_mul _ _).trans ?_
        simp [totalDegree_C, totalDegree_X]
      have h3 : (X j : MvPolynomial (Fin n) (ZMod p)).totalDegree ≤ 1 := by
        simp [totalDegree_X]
      omega
    omega
  have hcard := char_dvd_card_solutions p hdeg
  have hpos : 0 < Fintype.card { x : Fin n → ZMod p // eval x P = 0 } := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨0, by simp [hP]⟩⟩
  have hp : (1 : ℕ) < p := (Fact.out : p.Prime).one_lt
  have h1 : 1 < Fintype.card { x : Fin n → ZMod p // eval x P = 0 } :=
    lt_of_lt_of_le hp (Nat.le_of_dvd hpos hcard)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1 ⟨0, by simp [hP]⟩
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_⟩
  have := y.2
  simp only [hP, map_sum, map_mul, eval_C, eval_X] at this
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this


/-- Helper: the value $\mathbf w^{\mathsf T}A\mathbf w$ of the quadratic form with matrix $A$. -/
def quadVal {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) (w : Fin n → R) : R := w ⬝ᵥ A *ᵥ w

/-- Helper: $q(\mathbf u + t e_j) = q(\mathbf u) + 2t(A\mathbf u)_j + t^{2}A_{jj}$ for symmetric $A$. -/
theorem quadVal_add_single {R : Type*} [CommRing R] {A : Matrix (Fin n) (Fin n) R} (hA : A.IsSymm) (u : Fin n → R)
    (j : Fin n) (t : R) :
    quadVal A (u + t • Pi.single j 1) = quadVal A u + 2 * t * (A *ᵥ u) j + t ^ 2 * A j j := by
  have h1 : (Pi.single j 1 : Fin n → R) ⬝ᵥ A *ᵥ u = (A *ᵥ u) j := by simp
  have h2 : u ⬝ᵥ A *ᵥ (Pi.single j 1 : Fin n → R) = (A *ᵥ u) j := by
    rw [← h1]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm, Matrix.dotProduct_mulVec]
  have h3 : (Pi.single j 1 : Fin n → R) ⬝ᵥ A *ᵥ (Pi.single j 1 : Fin n → R) = A j j := by simp
  simp only [quadVal, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, h1, h2, h3]
  ring


section Hensel

variable (p : ℕ) [Fact p.Prime]

/-- Helper: $x \in \mathbb Z_p$ reduces to $0$ modulo $p$ iff $\|x\|_p < 1$. -/
theorem toZMod_eq_zero_iff {x : ℤ_[p]} : PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  constructor
  · intro h
    have hx : x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h
    rw [PadicInt.ker_toZMod] at hx
    have hn : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hx
    rw [PadicInt.isUnit_iff] at hn
    exact lt_of_le_of_ne (PadicInt.norm_le_one x) hn
  · intro h
    have hn : ¬ IsUnit x := by rw [PadicInt.isUnit_iff]; exact h.ne
    have hx : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal x).mpr hn
    rw [← PadicInt.ker_toZMod] at hx
    exact hx

/-- Helper: $x \in \mathbb Z_p$ not divisible by $p$ has norm $1$. -/
theorem norm_eq_one_of_toZMod_ne_zero {x : ℤ_[p]} (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 := by
  by_contra hne
  exact h ((toZMod_eq_zero_iff p).mpr (lt_of_le_of_ne (PadicInt.norm_le_one x) hne))


/-- Helper: reduction modulo $p$ commutes with taking the quadratic value. -/
theorem toZMod_quadVal (A : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ_[p]) :
    PadicInt.toZMod (quadVal (A.map (Int.castRingHom ℤ_[p])) w) =
      quadVal (A.map (Int.castRingHom (ZMod p))) (fun i => PadicInt.toZMod (w i)) := by
  simp [quadVal, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]

/-- Helper: reduction modulo $p$ commutes with the matrix-vector product. -/
theorem toZMod_mulVec (A : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ_[p]) (j : Fin n) :
    PadicInt.toZMod ((A.map (Int.castRingHom ℤ_[p]) *ᵥ w) j) =
      (A.map (Int.castRingHom (ZMod p)) *ᵥ (fun i => PadicInt.toZMod (w i))) j := by
  simp [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]

/-- Helper (Hensel): for odd $p$, a symmetric integer matrix $A$ of size $n \ge 3$ with unit determinant has a nonzero vector
$\mathbf w \in \mathbb Z_p^n$ with $\mathbf w^{\mathsf T}A\mathbf w = 0$. (A nontrivial zero modulo $p$ exists by Chevalley–Warning, is
nonsingular because $A$ is invertible modulo $p$, and lifts by Hensel's lemma in one variable.) -/
theorem exists_padic_zero (hp2 : p ≠ 2) (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.IsSymm) (hd : IsUnit A.det) :
    ∃ w : Fin n → ℤ_[p], w ≠ 0 ∧ quadVal (A.map (Int.castRingHom ℤ_[p])) w = 0 := by
  classical
  set Ab : Matrix (Fin n) (Fin n) (ZMod p) := A.map (Int.castRingHom (ZMod p)) with hAb
  set Ar : Matrix (Fin n) (Fin n) ℤ_[p] := A.map (Int.castRingHom ℤ_[p]) with hAr
  have hArs : Ar.IsSymm := by
    ext i j
    have := hA.apply i j
    simp [hAr, Matrix.map_apply, this]
  have hdet : Ab.det ≠ 0 := by
    have : Ab.det = ((A.det : ℤ) : ZMod p) := (RingHom.map_det (Int.castRingHom (ZMod p)) A).symm
    rw [this]
    rcases Int.isUnit_iff.mp hd with h | h <;> rw [h] <;> simp
  obtain ⟨xb, hx0, hx⟩ := exists_nontrivial_zero_zmod p hn Ab
  have hgrad : Ab *ᵥ xb ≠ 0 := fun h => hx0 (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
  obtain ⟨j, hj⟩ : ∃ j, (Ab *ᵥ xb) j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hgrad (funext hcon)
  set y : Fin n → ℤ_[p] := fun i => ((xb i).val : ℤ_[p]) with hy
  have hty : ∀ i, PadicInt.toZMod (y i) = xb i := fun i => by simp [hy]
  set u : Fin n → ℤ_[p] := Function.update y j 0 with hu
  have hyu : y = u + y j • Pi.single j 1 := by
    ext i
    by_cases h : i = j
    · subst h; simp [hu]
    · simp [hu, h, Function.update_of_ne h, Pi.single_apply]
  have hupd : ∀ t : ℤ_[p], Function.update y j t = u + t • Pi.single j 1 := by
    intro t
    ext i
    by_cases h : i = j
    · subst h; simp [hu]
    · simp [hu, h, Function.update_of_ne h, Pi.single_apply]
  set F : Polynomial ℤ_[p] := Polynomial.C (Ar j j) * Polynomial.X ^ 2 + Polynomial.C (2 * (Ar *ᵥ u) j) * Polynomial.X
    + Polynomial.C (quadVal Ar u) with hF
  have hFeval : ∀ t, F.eval t = quadVal Ar (Function.update y j t) := by
    intro t
    rw [hupd, quadVal_add_single hArs]
    simp [hF]
    ring
  have hFder : ∀ t, F.derivative.eval t = 2 * (Ar j j) * t + 2 * (Ar *ᵥ u) j := by
    intro t
    simp [hF, Polynomial.derivative_X_pow]
    ring
  have hy_eval : F.eval (y j) = quadVal Ar y := by
    rw [hFeval, Function.update_eq_self]
  have hmv : (Ar *ᵥ y) j = (Ar *ᵥ u) j + y j * Ar j j := by
    conv_lhs => rw [hyu]
    simp [Matrix.mulVec_add, Matrix.mulVec_smul]
  have hy_der : F.derivative.eval (y j) = 2 * (Ar *ᵥ y) j := by
    rw [hFder, hmv]; ring
  -- reductions mod p
  have hq0 : PadicInt.toZMod (quadVal Ar y) = 0 := by
    rw [hAr, toZMod_quadVal]
    have : (fun i => PadicInt.toZMod (y i)) = xb := funext hty
    rw [this]; exact hx
  have hd1 : PadicInt.toZMod (2 * (Ar *ᵥ y) j) ≠ 0 := by
    rw [map_mul, hAr, toZMod_mulVec]
    have : (fun i => PadicInt.toZMod (y i)) = xb := funext hty
    rw [this]
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := by
        have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
        exact this
      have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
      exact hp2 this
    have h2' : PadicInt.toZMod (2 : ℤ_[p]) = 2 := map_ofNat _ 2
    rw [h2']
    exact mul_ne_zero h2 hj
  have hnorm : ‖F.aeval (y j)‖ < ‖F.derivative.aeval (y j)‖ ^ 2 := by
    rw [Polynomial.coe_aeval_eq_eval, hy_eval, hy_der,
      norm_eq_one_of_toZMod_ne_zero p hd1]
    rw [one_pow]
    exact (toZMod_eq_zero_iff p).mp hq0
  obtain ⟨z, hz, hzd, -, -⟩ := hensels_lemma (p := p) (R := ℤ_[p]) (F := F) (a := y j) hnorm
  rw [Polynomial.coe_aeval_eq_eval] at hz
  rw [Polynomial.coe_aeval_eq_eval, hy_der, norm_eq_one_of_toZMod_ne_zero p hd1] at hzd
  have hzz : PadicInt.toZMod z = PadicInt.toZMod (y j) := by
    have := (toZMod_eq_zero_iff p).mpr hzd
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨Function.update y j z, ?_, ?_⟩
  · intro hw
    apply hx0
    funext i
    have := congrFun hw i
    by_cases h : i = j
    · subst h
      simp at this
      rw [← hty i, ← hzz, this]; simp
    · simp [Function.update_of_ne h] at this
      rw [← hty i, this]; simp
  · rw [← hFeval]; exact hz

end Hensel


/-- Helper: the rational form of a classically integral form of determinant $\pm 1$ in $n \ge 3$ variables is isotropic over
$\mathbb Q_p$ for every odd prime $p$ (a unimodular form is nonsingular modulo $p$; `exists_padic_zero`). -/
theorem isotropicIn_padic_of_unimodular (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n) {f : QuadForm ℤ n}
    (hf : IsUnimodularCI f) : (f.map (Int.castRingHom ℚ)).IsotropicIn ℚ_[p] := by
  have hAd : IsUnit (Siegel.casselsMat f).det := by rcases hf.2 with h | h <;> rw [h] <;> simp
  obtain ⟨w, hw0, hw⟩ := exists_padic_zero p hp2 hn (Siegel.casselsMat f) (Siegel.casselsMat_isSymm f) hAd
  refine ⟨fun i => ((w i : ℤ_[p]) : ℚ_[p]), ?_, ?_⟩
  · intro h
    apply hw0
    funext i
    have h0 : ((w i : ℤ_[p]) : ℚ_[p]) = 0 := congrFun h i
    exact PadicInt.coe_eq_zero.mp h0
  · have e1 : (f.map (Int.castRingHom ℚ)).evalIn ℚ_[p] (fun i => ((w i : ℤ_[p]) : ℚ_[p])) =
        f.evalIn ℚ_[p] (fun i => ((w i : ℤ_[p]) : ℚ_[p])) := by
      simp [QuadForm.evalIn, QuadForm.map]
    rw [e1, evalIn_eq_casselsMat ℚ_[p] hf.1]
    have e2 : (fun i => ((w i : ℤ_[p]) : ℚ_[p])) ⬝ᵥ ((Siegel.casselsMat f).map (Int.castRingHom ℚ_[p])) *ᵥ
        (fun i => ((w i : ℤ_[p]) : ℚ_[p])) =
        ((quadVal ((Siegel.casselsMat f).map (Int.castRingHom ℤ_[p])) w : ℤ_[p]) : ℚ_[p]) := by
      simp [quadVal, dotProduct, Matrix.mulVec, Matrix.map_apply]
    rw [e2, hw]
    simp

end PadicOdd

/-! ### Isotropy of indefinite unimodular ternary forms -/

section Ternary

/-- Helper: the rational form of an indefinite integral form is isotropic over $\mathbb R$. -/
theorem isotropicIn_real_of_indefinite {n : ℕ} {f : QuadForm ℤ n} (hind : IsIndefinite f) :
    (f.map (Int.castRingHom ℚ)).IsotropicIn ℝ := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hind
  exact Cassels.Ch6.isotropic_real_of_indefinite _ ⟨x, by rw [evalIn_real_map_rat]; exact hx⟩
    ⟨y, by rw [evalIn_real_map_rat]; exact hy⟩

/-- Helper: the places other than $2$ are forced by the product formula: if a set of places is finite of even cardinality
and contained in `{v₀}`, then `v₀` is not in it. -/
theorem not_mem_of_even_ncard {α : Type*} {S : Set α} {v₀ : α} (hfin : S.Finite) (hev : Even S.ncard)
    (hsub : ∀ v ∈ S, v = v₀) : v₀ ∉ S := by
  intro h
  have : S = {v₀} := Set.eq_singleton_iff_unique_mem.mpr ⟨h, hsub⟩
  rw [this, Set.ncard_singleton] at hev
  exact absurd hev (by decide)

/-- **Indefinite unimodular ternary forms are isotropic over $\mathbb Q$.** The form is isotropic over $\mathbb R$ (indefinite) and
over $\mathbb Q_p$ for odd $p$ (`isotropicIn_padic_of_unimodular`); by Hilbert reciprocity (an even number of places have Hilbert
symbol $-1$) it is isotropic over $\mathbb Q_2$ as well, so over $\mathbb Q$ by Hasse–Minkowski in three variables. -/
theorem isotropicIn_rat_three (f : QuadForm ℤ 3) (hf : IsUnimodularCI f) (hind : IsIndefinite f) :
    (f.map (Int.castRingHom ℚ)).IsotropicIn ℚ := by
  set Q := f.map (Int.castRingHom ℚ) with hQdef
  have hQ : Q.Nondegenerate := nondegenerate_map_rat hf
  have hreal : Q.IsotropicIn ℝ := isotropicIn_real_of_indefinite hind
  have hodd : ∀ p : ℕ, [Fact p.Prime] → p ≠ 2 → Q.IsotropicIn ℚ_[p] := fun p _ hp2 =>
    isotropicIn_padic_of_unimodular p hp2 (le_refl 3) hf
  obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
  have hae : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
  have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
      hilbertSymbol K (algebraMap ℚ K (-a 1 / a 0)) (algebraMap ℚ K (-a 2 / a 0)) = 1 := by
    intro K _ _
    rw [HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso), hae,
      HM3.isotropic_diag_three_iff K _ _ _ (ha 0) (ha 1) (ha 2)]
    simp
  have hx : -a 1 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 1)) (ha 0)
  have hy : -a 2 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 2)) (ha 0)
  obtain ⟨hfin, hev⟩ := hilbert_product_formula _ _ hx hy
  set v2 : RatPlace := RatPlace.finite ⟨2, Nat.prime_two⟩ with hv2
  have hone : ∀ v : RatPlace, v ≠ v2 → v.hilbert (-a 1 / a 0) (-a 2 / a 0) = 1 := by
    intro v hv
    cases v with
    | infinite =>
      have hv' := (key ℝ).mp hreal
      simpa [RatPlace.hilbert] using hv'
    | finite p =>
      haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      have hp2 : (p : ℕ) ≠ 2 := fun h => hv (by rw [hv2]; congr; exact Subtype.ext h)
      have hv' := (key ℚ_[(p : ℕ)]).mp (hodd p hp2)
      simpa [RatPlace.hilbert] using hv'
  have h2 : v2 ∉ {v : RatPlace | v.hilbert (-a 1 / a 0) (-a 2 / a 0) = -1} := by
    refine not_mem_of_even_ncard hfin hev (fun v hv => ?_)
    by_contra hne
    have := hone v hne
    simp only [Set.mem_setOf_eq] at hv
    rw [this] at hv
    norm_num at hv
  have h2' : v2.hilbert (-a 1 / a 0) (-a 2 / a 0) = 1 := by
    simp only [Set.mem_setOf_eq] at h2
    have hpm : v2.hilbert (-a 1 / a 0) (-a 2 / a 0) = 1 ∨ v2.hilbert (-a 1 / a 0) (-a 2 / a 0) = -1 := by
      simp only [hv2, RatPlace.hilbert, hilbertSymbol]; split_ifs <;> simp
    rcases hpm with h | h
    · exact h
    · exact absurd h h2
  refine (hasseMinkowski_three Q hQ).mpr fun v => ?_
  by_cases hv : v = v2
  · subst hv
    haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    show Q.IsotropicIn ℚ_[2]
    rw [key]
    simpa [hv2, RatPlace.hilbert] using h2'
  · cases v with
    | infinite => exact hreal
    | finite p =>
      haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      have hp2 : (p : ℕ) ≠ 2 := fun h => hv (by rw [hv2]; congr; exact Subtype.ext h)
      exact hodd p hp2

end Ternary

/-! ### Isotropy of indefinite unimodular quaternary forms -/

section Quaternary

/-- Helper: $-1$ is not a square in $\mathbb Q_2$ ($x^2 \equiv 1 \pmod 4$ for a $2$-adic unit $x$). -/
theorem not_isSquare_neg_one_two : ¬ IsSquare (-1 : ℚ_[2]) := by
  rintro ⟨r, hr⟩
  have hr1 : ‖r‖ = 1 := by
    have h : ‖r‖ * ‖r‖ = 1 := by rw [← norm_mul, ← hr]; simp
    nlinarith [norm_nonneg r]
  let z : ℤ_[2] := ⟨r, hr1.le⟩
  have hz : z * z = -1 := by
    apply Subtype.ext
    show r * r = -1
    exact hr.symm
  have := congrArg (PadicInt.toZModPow (p := 2) 2) hz
  rw [map_mul, map_neg, map_one] at this
  generalize PadicInt.toZModPow (p := 2) 2 z = y at this
  revert y
  decide

/-- Helper: if a quaternary diagonal form $\langle b_1, b_2, -b_3, -b_4\rangle$ is isotropic over a field $K$ in which
$b_1b_2b_3b_4$ is a square, then $(b_1, b_2)_K = (b_3, b_4)_K$. (A common value $x$ of $\langle b_1, b_2 \rangle$ and
$\langle b_3, b_4 \rangle$ has $(x, -b_1b_2)(x, -b_3b_4) = (x, b_1b_2b_3b_4) = 1$.) -/
theorem symbols_eq_of_isotropic (K : Type) [Field K] [CharZero K]
    (hmul : ∀ a a' b : K, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol K (a * a') b = hilbertSymbol K a b * hilbertSymbol K a' b)
    (b₁ b₂ b₃ b₄ : ℚ) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) (h₃ : b₃ ≠ 0) (h₄ : b₄ ≠ 0)
    (hiso : (QuadForm.diag ![b₁, b₂, -b₃, -b₄]).IsotropicIn K)
    (hsq : IsSquare (algebraMap ℚ K (b₁ * b₂ * b₃ * b₄))) :
    hilbertSymbol K (algebraMap ℚ K b₁) (algebraMap ℚ K b₂) =
      hilbertSymbol K (algebraMap ℚ K b₃) (algebraMap ℚ K b₄) := by
  obtain ⟨x, hx, e1, e2⟩ := HM4.exists_common_value K b₁ b₂ b₃ b₄ h₁ h₂ h₃ h₄ hiso
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : algebraMap ℚ K (b₁ * b₂ * b₃ * b₄) = 0 := by simpa using hr
    have h0 : b₁ * b₂ * b₃ * b₄ = 0 := by
      exact (map_eq_zero_iff _ (algebraMap ℚ K).injective).mp this
    simp [h₁, h₂, h₃, h₄] at h0
  have hA : algebraMap ℚ K (-(b₁ * b₂)) ≠ 0 := by simpa [h₁, h₂] using fun h => by simp_all
  have hB : algebraMap ℚ K (-(b₃ * b₄)) ≠ 0 := by simpa [h₃, h₄] using fun h => by simp_all
  have hAB : algebraMap ℚ K (-(b₁ * b₂)) * algebraMap ℚ K (-(b₃ * b₄)) = r ^ 2 := by
    rw [sq, ← hr]; simp; ring
  have hxA := hmul (algebraMap ℚ K (-(b₁ * b₂))) (algebraMap ℚ K (-(b₃ * b₄))) x hA hB hx
  have h1 : hilbertSymbol K (r ^ 2) x = 1 := by
    rw [hilbertSymbol_comm]; exact PadicClass.hs_sq x r hr0
  rw [hAB, h1, hilbertSymbol_comm K (algebraMap ℚ K (-(b₁ * b₂))) x,
    hilbertSymbol_comm K (algebraMap ℚ K (-(b₃ * b₄))) x, e1, e2] at hxA
  rcases PadicClass.hs_pm (K := K) (algebraMap ℚ K b₁) (algebraMap ℚ K b₂) with h | h <;>
    rcases PadicClass.hs_pm (K := K) (algebraMap ℚ K b₃) (algebraMap ℚ K b₄) with h' | h' <;>
    rw [h, h'] at hxA ⊢ <;> first | rfl | norm_num at hxA

/-- Helper: the local converse over $\mathbb Q_p$: $\langle b_1, b_2, -b_3, -b_4\rangle$ is isotropic as soon as
$(b_1, b_2) = (b_3, b_4)$ whenever $b_1b_2b_3b_4$ is a square (Serre IV §2.2, proof of Thm. 6, rank $4$). -/
theorem isotropic_four_of_symbols (p : ℕ) [Fact p.Prime] (b₁ b₂ b₃ b₄ : ℚ_[p]) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0)
    (h₃ : b₃ ≠ 0) (h₄ : b₄ ≠ 0)
    (hcompat : IsSquare (b₁ * b₂ * b₃ * b₄) → hilbertSymbol ℚ_[p] b₁ b₂ = hilbertSymbol ℚ_[p] b₃ b₄) :
    (QuadForm.diag ![b₁, b₂, -b₃, -b₄]).IsotropicIn ℚ_[p] := by
  have hK := PadicClass.localHilbertField_padic p
  obtain ⟨x, hx0, hx1, hx2⟩ := (hK.exists_hs_eq_iff (A := -(b₁ * b₂)) (B := -(b₃ * b₄))
    (neg_ne_zero.mpr (mul_ne_zero h₁ h₂)) (neg_ne_zero.mpr (mul_ne_zero h₃ h₄))
    (e₁ := hilbertSymbol ℚ_[p] b₁ b₂) (e₂ := hilbertSymbol ℚ_[p] b₃ b₄)
    (PadicClass.hs_pm _ _) (PadicClass.hs_pm _ _)).mpr
    ⟨fun h => PadicClass.hs_eq_one_of_isSquare_neg_mul hK h₁ h₂ h,
     fun h => PadicClass.hs_eq_one_of_isSquare_neg_mul hK h₃ h₄ h,
     fun h => hcompat (by
       convert h using 1
       ring)⟩
  have hn₃ : -b₃ ≠ 0 := neg_ne_zero.mpr h₃
  have hn₄ : -b₄ ≠ 0 := neg_ne_zero.mpr h₄
  refine (PadicClass.isotropic_four_iff_common h₁ h₂ hn₃ hn₄).mpr ⟨x, hx0, ?_, ?_⟩
  · exact (PadicClass.represents_two_iff hK h₁ h₂ hx0).mpr hx1
  · simp only [neg_neg]
    exact (PadicClass.represents_two_iff hK h₃ h₄ hx0).mpr hx2

end Quaternary

/-! ### Isotropy of indefinite unimodular quaternary forms: the global argument -/

section QuaternaryGlobal

/-- Helper: Hilbert symbols of rationals at a place are $\pm 1$. -/
theorem ratPlace_hilbert_pm (v : RatPlace) (u w : ℚ) : v.hilbert u w = 1 ∨ v.hilbert u w = -1 := by
  cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp

/-- Helper (consequence of Hilbert reciprocity): if two Hilbert symbols of rationals agree at all places except possibly
$v_0$, they agree at $v_0$ too (each symbol is $-1$ at an even number of places). -/
theorem hilbert_eq_at_of_eq_elsewhere (u₁ u₂ u₃ u₄ : ℚ) (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) (h₃ : u₃ ≠ 0) (h₄ : u₄ ≠ 0)
    (v₀ : RatPlace) (h : ∀ v, v ≠ v₀ → v.hilbert u₁ u₂ = v.hilbert u₃ u₄) :
    v₀.hilbert u₁ u₂ = v₀.hilbert u₃ u₄ := by
  obtain ⟨hf1, he1⟩ := hilbert_product_formula u₁ u₂ h₁ h₂
  obtain ⟨hf2, he2⟩ := hilbert_product_formula u₃ u₄ h₃ h₄
  set S₁ : Set RatPlace := {v | v.hilbert u₁ u₂ = -1} with hS₁
  set S₂ : Set RatPlace := {v | v.hilbert u₃ u₄ = -1} with hS₂
  have hiff : ∀ v, v ≠ v₀ → (v ∈ S₁ ↔ v ∈ S₂) := fun v hv => by
    simp only [hS₁, hS₂, Set.mem_setOf_eq]; rw [h v hv]
  by_contra hne
  have hcase : (v₀ ∈ S₁ ∧ v₀ ∉ S₂) ∨ (v₀ ∉ S₁ ∧ v₀ ∈ S₂) := by
    simp only [hS₁, hS₂, Set.mem_setOf_eq]
    rcases ratPlace_hilbert_pm v₀ u₁ u₂ with e | e <;> rcases ratPlace_hilbert_pm v₀ u₃ u₄ with e' | e' <;>
      simp_all
  rcases hcase with ⟨a, b⟩ | ⟨a, b⟩
  · have hS : S₁ = insert v₀ S₂ := by
      ext v
      by_cases hv : v = v₀
      · subst hv; simp [a]
      · simp [hv, hiff v hv]
    have := Set.ncard_insert_of_notMem b hf2
    rw [← hS] at this
    rw [this] at he1
    exact (Nat.even_add_one.mp he1) he2
  · have hS : S₂ = insert v₀ S₁ := by
      ext v
      by_cases hv : v = v₀
      · subst hv; simp [b]
      · simp [hv, hiff v hv]
    have := Set.ncard_insert_of_notMem a hf1
    rw [← hS] at this
    rw [this] at he2
    exact (Nat.even_add_one.mp he2) he1

end QuaternaryGlobal

/-! ### Isotropy of indefinite unimodular quaternary forms -/

section QuaternaryMain

variable {n : ℕ}

/-- Helper: isotropy of a diagonal form with rational entries over $K$, in terms of the entries mapped to $K$. -/
theorem isotropicIn_diag_cast (K : Type) [Field K] [CharZero K] (a : Fin n → ℚ) :
    (QuadForm.diag a).IsotropicIn K ↔ (QuadForm.diag fun i => algebraMap ℚ K (a i)).IsotropicIn K := by
  simp only [QuadForm.IsotropicIn, QuadForm.evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply]

/-- Helper: the product of the entries of a rational diagonalization of the rational form of a classically integral form is
$\det(f_{ij})$ times a nonzero rational square. -/
theorem prod_eq_det_mul_sq {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) (a : Fin n → ℚ)
    (h : (f.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag a)) :
    ∃ t : ℚ, t ≠ 0 ∧ ∏ i, a i = t ^ 2 * ((Siegel.casselsMat f).det : ℚ) := by
  obtain ⟨P, hPu, hP⟩ := h
  have e := congrArg Matrix.det (PadicClass.transpose_mul_hessian_mul hP)
  have hH : (f.map (Int.castRingHom ℚ)).hessian.det = (2 : ℚ) ^ n * ((Siegel.casselsMat f).det : ℚ) := by
    have h1 : (f.map (Int.castRingHom ℚ)).hessian = f.hessian.map (Int.castRingHom ℚ) := by
      simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
    rw [h1, show ((f.hessian.map (Int.castRingHom ℚ))).det = ((f.hessian.det : ℤ) : ℚ) from
      (RingHom.map_det (Int.castRingHom ℚ) f.hessian).symm,
      Siegel.hessian_eq_two_smul_casselsMat hf, Matrix.det_smul, Fintype.card_fin]
    push_cast; ring
  simp only [Matrix.det_mul, Matrix.det_transpose, QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose,
    Matrix.diagonal_add, Matrix.det_diagonal] at e
  have hH' := hH
  simp only [QuadForm.hessian] at hH'
  rw [hH'] at e
  have h2 : (∏ i, (a i + a i)) = 2 ^ n * ∏ i, a i := by
    simp [← two_mul, Finset.prod_mul_distrib]
  rw [h2] at e
  have h20 : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨P.det, hPu.ne_zero, ?_⟩
  apply mul_left_cancel₀ h20
  rw [← e]; ring

/-- **Indefinite unimodular quaternary forms are isotropic over $\mathbb Q$.** Isotropic over $\mathbb R$ (indefinite) and over
$\mathbb Q_p$ for odd $p$ (`isotropicIn_padic_of_unimodular`); over $\mathbb Q_2$: if $\det(f_{ij}) = -1$ the discriminant is
$-1$ times a square, which is not a square in $\mathbb Q_2$, and a quaternary form with a non-square discriminant is isotropic
(`isotropic_four_of_symbols`); if $\det(f_{ij}) = 1$ the discriminant is a square, and the equality of the two Hilbert symbols
$(b_1, b_2) = (b_3, b_4)$ at $2$ follows from the equality at all other places (where the form is isotropic) by Hilbert
reciprocity (`hilbert_eq_at_of_eq_elsewhere`). Then Hasse–Minkowski in four variables. -/
theorem isotropicIn_rat_four (f : QuadForm ℤ 4) (hf : IsUnimodularCI f) (hind : IsIndefinite f) :
    (f.map (Int.castRingHom ℚ)).IsotropicIn ℚ := by
  set Q := f.map (Int.castRingHom ℚ) with hQdef
  have hQ : Q.Nondegenerate := nondegenerate_map_rat hf
  have hreal : Q.IsotropicIn ℝ := isotropicIn_real_of_indefinite hind
  have hodd : ∀ p : ℕ, [Fact p.Prime] → p ≠ 2 → Q.IsotropicIn ℚ_[p] := fun p _ hp2 =>
    isotropicIn_padic_of_unimodular p hp2 (by norm_num) hf
  obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
  obtain ⟨t, ht, hdisc⟩ := prod_eq_det_mul_sq hf.1 a hiso
  obtain ⟨b₁, b₂, b₃, b₄, hb₁, hb₂, hb₃, hb₄, hae, hprod⟩ : ∃ b₁ b₂ b₃ b₄ : ℚ, b₁ ≠ 0 ∧ b₂ ≠ 0 ∧ b₃ ≠ 0 ∧
      b₄ ≠ 0 ∧ a = ![b₁, b₂, -b₃, -b₄] ∧ ∏ i, a i = b₁ * b₂ * b₃ * b₄ :=
    ⟨a 0, a 1, -a 2, -a 3, ha 0, ha 1, neg_ne_zero.mpr (ha 2), neg_ne_zero.mpr (ha 3),
      by funext i; fin_cases i <;> simp, by simp [Fin.prod_univ_four]⟩
  subst hae
  rw [hprod] at hdisc
  have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
      (QuadForm.diag ![b₁, b₂, -b₃, -b₄]).IsotropicIn K := by
    intro K _ _
    rw [HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso)]
  set v2 : RatPlace := RatPlace.finite ⟨2, Nat.prime_two⟩ with hv2
  have hsq_of : ∀ (K : Type) [Field K] [CharZero K], (Siegel.casselsMat f).det = 1 →
      IsSquare (algebraMap ℚ K (b₁ * b₂ * b₃ * b₄)) := by
    intro K _ _ hε
    refine ⟨algebraMap ℚ K t, ?_⟩
    rw [hdisc, hε]; simp [sq]
  have hsymb : (Siegel.casselsMat f).det = 1 → ∀ v : RatPlace, v ≠ v2 →
      v.hilbert b₁ b₂ = v.hilbert b₃ b₄ := by
    intro hε v hv
    cases v with
    | infinite =>
      have := symbols_eq_of_isotropic ℝ HilbertLocal.hilbertSymbol_real_mul_left b₁ b₂ b₃ b₄ hb₁ hb₂ hb₃ hb₄
        ((key ℝ).mp hreal) (hsq_of ℝ hε)
      simpa [RatPlace.hilbert] using this
    | finite p =>
      haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      have hp2 : (p : ℕ) ≠ 2 := fun h => hv (by rw [hv2]; congr; exact Subtype.ext h)
      have := symbols_eq_of_isotropic ℚ_[(p : ℕ)] HilbertLocal.hilbertSymbol_padic_mul_left b₁ b₂ b₃ b₄ hb₁
        hb₂ hb₃ hb₄ ((key _).mp (hodd p hp2)) (hsq_of _ hε)
      simpa [RatPlace.hilbert] using this
  have h2iso : Q.IsotropicIn ℚ_[2] := by
    rw [key, isotropicIn_diag_cast]
    have e : (fun i => algebraMap ℚ ℚ_[2] (![b₁, b₂, -b₃, -b₄] i)) =
        ![(b₁ : ℚ_[2]), (b₂ : ℚ_[2]), -(b₃ : ℚ_[2]), -(b₄ : ℚ_[2])] := by
      funext i; fin_cases i <;> simp
    rw [e]
    refine isotropic_four_of_symbols 2 _ _ _ _ (by exact_mod_cast hb₁) (by exact_mod_cast hb₂)
      (by exact_mod_cast hb₃) (by exact_mod_cast hb₄) ?_
    rcases hf.2 with hε | hε
    · intro _
      have := hilbert_eq_at_of_eq_elsewhere b₁ b₂ b₃ b₄ hb₁ hb₂ hb₃ hb₄ v2 (hsymb hε)
      simpa [hv2, RatPlace.hilbert] using this
    · intro ⟨s, hs⟩
      exfalso
      apply not_isSquare_neg_one_two
      have hdisc' : ((b₁ : ℚ_[2]) * b₂ * b₃ * b₄) = -((t : ℚ_[2]) ^ 2) := by
        have := congrArg (fun q : ℚ => (q : ℚ_[2])) hdisc
        rw [hε] at this
        push_cast at this
        simpa using this
      have ht' : (t : ℚ_[2]) ≠ 0 := by exact_mod_cast ht
      refine ⟨s / t, ?_⟩
      rw [hdisc'] at hs
      field_simp
      linear_combination hs
  refine (hasseMinkowski_four Q hQ).mpr fun v => ?_
  by_cases hv : v = v2
  · subst hv
    haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    exact h2iso
  · cases v with
    | infinite => exact hreal
    | finite p =>
      haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      have hp2 : (p : ℕ) ≠ 2 := fun h => hv (by rw [hv2]; congr; exact Subtype.ext h)
      exact hodd p hp2

/-- **Isotropy of indefinite unimodular forms in 3 and 4 variables** (the named input `IndefiniteIsotropic34` is a theorem):
`isotropicIn_rat_three`, `isotropicIn_rat_four` and clearing denominators. -/
theorem indefiniteIsotropic34 : IndefiniteIsotropic34 := by
  intro m hm f hf hind
  rcases hm with rfl | rfl
  · exact isIsotropicZ_of_rat f (isotropicIn_rat_three f hf hind)
  · exact isIsotropicZ_of_rat f (isotropicIn_rat_four f hf hind)

/-- **Isotropy of indefinite unimodular forms:** an indefinite classically integral form of determinant $\pm 1$ in $2 + m$
variables ($m \ge 0$) has a nontrivial integer zero. Two variables: explicit (`isIsotropicZ_of_dim_two`); three and four
variables: Hasse–Minkowski with Hilbert reciprocity (`indefiniteIsotropic34`); five or more: Meyer's theorem
(`isIsotropicZ_of_five_le`). -/
theorem isIsotropicZ_of_indefinite {m : ℕ} (f : QuadForm ℤ (2 + m)) (hf : IsUnimodularCI f) (hind : IsIndefinite f) :
    IsIsotropicZ f := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m) with rfl | h | h | h
  · exact isIsotropicZ_of_dim_two f hf hind
  · exact indefiniteIsotropic34 m (Or.inl h) f hf hind
  · exact indefiniteIsotropic34 m (Or.inr h) f hf hind
  · exact isIsotropicZ_of_five_le f (by omega) hf hind

end QuaternaryMain

/-! ### Reduction to a hyperbolic or odd plane (Ex. 11 (i), (iii)) -/

section Planes

variable {m : ℕ}

/-- Helper: $e_i^{\mathsf T} G e_j = G_{ij}$. -/
theorem single_bil {k : ℕ} (G : Matrix (Fin k) (Fin k) ℤ) (i j : Fin k) :
    (Pi.single i 1 : Fin k → ℤ) ⬝ᵥ G *ᵥ (Pi.single j 1) = G i j := by
  simp [Matrix.mulVec_single, single_dotProduct]

/-- Helper: symmetry of the bilinear form of a symmetric matrix. -/
theorem bil_comm {k : ℕ} {G : Matrix (Fin k) (Fin k) ℤ} (hG : G.IsSymm) (x y : Fin k → ℤ) :
    x ⬝ᵥ G *ᵥ y = y ⬝ᵥ G *ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG.eq, dotProduct_comm, Matrix.dotProduct_mulVec]

/-- Helper: the Gram matrix of a pair of vectors, entry by entry. -/
theorem gram2_eq (G : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (u v : Fin (2 + m) → ℤ) :
    gram2 G u v = !![u ⬝ᵥ G *ᵥ u, u ⬝ᵥ G *ᵥ v; v ⬝ᵥ G *ᵥ u, v ⬝ᵥ G *ᵥ v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Helper: from an isotropic vector $p$ with $p^{\mathsf T}Gq = c = \pm 1$ and $q^{\mathsf T}Gq = N$ odd one gets two vectors
$u, v$ whose Gram matrix is $\operatorname{diag}(1, -1)$: $u = q + c\,\tfrac{1-N}{2}\,p$, $v = p - c\,u$. -/
theorem exists_odd_pair {G : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ} (hG : G.IsSymm) (p q : Fin (2 + m) → ℤ)
    (c : ℤ) (hc : c = 1 ∨ c = -1) (hpp : p ⬝ᵥ G *ᵥ p = 0) (hpq : p ⬝ᵥ G *ᵥ q = c) (N h : ℤ)
    (hN : q ⬝ᵥ G *ᵥ q = N) (hh : 1 - N = 2 * h) :
    ∃ u v : Fin (2 + m) → ℤ, gram2 G u v = !![1, 0; 0, -1] := by
  have hqp : q ⬝ᵥ G *ᵥ p = c := by rw [bil_comm hG, hpq]
  refine ⟨q + (c * h) • p, p - c • (q + (c * h) • p), ?_⟩
  rw [gram2_eq]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_sub, sub_dotProduct, smul_eq_mul, hpp, hpq, hqp, hN]
  ext i j
  rcases hc with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp <;> omega

/-- Helper: from an isotropic vector $e_0$ with $e_0^{\mathsf T}Ge_1 = c = \pm 1$ and $e_1^{\mathsf T}Ge_1 = a$ even one gets the
pair $u = e_0$, $v = c\,e_1 - \tfrac a2 e_0$ with Gram matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. -/
theorem exists_hyp_pair {G : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ} (hG : G.IsSymm) (p q : Fin (2 + m) → ℤ)
    (c : ℤ) (hc : c = 1 ∨ c = -1) (hpp : p ⬝ᵥ G *ᵥ p = 0) (hpq : p ⬝ᵥ G *ᵥ q = c) (a h : ℤ)
    (ha : q ⬝ᵥ G *ᵥ q = a) (hh : a = 2 * h) :
    ∃ u v : Fin (2 + m) → ℤ, gram2 G u v = !![0, 1; 1, 0] := by
  have hqp : q ⬝ᵥ G *ᵥ p = c := by rw [bil_comm hG, hpq]
  refine ⟨p, c • q - h • p, ?_⟩
  rw [gram2_eq]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_sub, sub_dotProduct, smul_eq_mul, hpp, hpq, hqp, ha]
  ext i j
  rcases hc with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp <;> omega

/-- **Normal form from an isotropic vector** (Cassels, Ch. 9, Ex. 9 applied to a classically integral form of determinant
$\pm 1$): a form $f$ with `IsUnimodularCI` and an isotropic vector is equivalent to a form $g$ with `IsUnimodularCI` whose
Cassels matrix has $G_{00} = 0$, $G_{01} = c = \pm 1$ and $G_{0j} = 0$ for $j \ge 2$ (0-based). -/
theorem exists_normal_form (f : QuadForm ℤ (2 + m)) (hf : IsUnimodularCI f) (hiso : IsIsotropicZ f) :
    ∃ g : QuadForm ℤ (2 + m), IntEquiv f g ∧ IsUnimodularCI g ∧ ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      Siegel.casselsMat g (Fin.castAdd m 0) (Fin.castAdd m 0) = 0 ∧
      Siegel.casselsMat g (Fin.castAdd m 0) (Fin.castAdd m 1) = c ∧
      ∀ k : Fin m, Siegel.casselsMat g (Fin.castAdd m 0) (Fin.natAdd 2 k) = 0 := by
  obtain ⟨g, hfg, hgci, hrow, hdvd⟩ := Siegel.ex9 (by omega : 2 ≤ 2 + m) hf.1 hiso
  have hfg' : IntEquiv f g := hfg.intEquiv
  have hdetf : f.hessian.det / 2 ^ (2 + m) = (Siegel.casselsMat f).det := by
    rw [Siegel.hessian_eq_two_smul_casselsMat hf.1, Matrix.det_smul, Fintype.card_fin]
    exact Int.mul_ediv_cancel_left _ (by positivity)
  have hdetg : (Siegel.casselsMat g).det = (Siegel.casselsMat f).det :=
    det_casselsMat_of_intEquiv hf.1 hgci hfg'
  have hh : ∀ i j, Siegel.casselsMat g i j = g.hessian i j / 2 := fun i j => rfl
  have e0 : (Fin.castAdd m 0 : Fin (2 + m)) = ⟨0, by omega⟩ := Fin.ext rfl
  have e1 : (Fin.castAdd m 1 : Fin (2 + m)) = ⟨1, by omega⟩ := Fin.ext rfl
  have hc2 : (g.hessian ⟨0, by omega⟩ ⟨1, by omega⟩ / 2) ^ 2 ∣ 1 := by
    rw [hdetf] at hdvd
    rcases hf.2 with h | h <;> rw [h] at hdvd
    · exact hdvd
    · exact dvd_neg.mp hdvd
  refine ⟨g, hfg', ⟨hgci, by rw [hdetg]; exact hf.2⟩, g.hessian ⟨0, by omega⟩ ⟨1, by omega⟩ / 2, ?_, ?_, ?_, ?_⟩
  · exact Int.isUnit_iff.mp (isUnit_of_dvd_one (dvd_trans (dvd_pow_self _ two_ne_zero) hc2))
  · rw [e0, hh, hrow ⟨0, by omega⟩ (by simp)]; rfl
  · rw [e0, e1, hh]
  · intro k
    rw [e0, hh, hrow (Fin.natAdd 2 k) (by simp [Fin.natAdd]; omega)]; rfl

end Planes

/-! ### Headline: Ex. 11 (i) and (iii) -/

section Headlines

variable {m : ℕ}

/-- Helper: splitting a plane with prescribed Gram matrix $P$ (of determinant $\pm 1$) off a unimodular form. -/
theorem equiv_orthSum_of_pair (g : QuadForm ℤ (2 + m)) (hg : IsUnimodularCI g) (u v : Fin (2 + m) → ℤ)
    (P : Matrix (Fin 2) (Fin 2) ℤ) (hGram : gram2 (Siegel.casselsMat g) u v = P) (hP : IsUnit P.det) :
    ∃ g' : QuadForm ℤ m, IsUnimodularCI g' ∧ (∀ k, ∃ y, g'.coeff k k = g.eval y) ∧
      IntEquiv g (QuadForm.orthSum (Siegel.ofGram P) g') := by
  obtain ⟨g', hg', hdiag, T, -, -, hT⟩ := split_form g hg u v (by rw [hGram]; exact hP)
  refine ⟨g', hg', hdiag, T, fun x => ?_⟩
  rw [hT x, hGram]
  exact (QuadForm.evalIn_orthSum ℤ (Siegel.ofGram P) g' x).symm

/-- **Cassels, Ch. 9, Ex. 11 (iii)** (p. 164): *let $f$ be indefinite and improperly primitive (classically integral of
determinant $\pm 1$). Show that it is equivalent to $2y_1y_2 + g(\mathbf z)$ for some $g$.* Here $f$ has $2 + m$ variables
(indefinite forces at least two), the hyperbolic plane is `hypPlane` $= 2y_0y_1$ (0-based), the sum is `QuadForm.orthSum`, and
the form $g$ in $m$ variables is again classically integral of determinant $\pm 1$ and has all diagonal coefficients even
(so for $m \ge 1$ it is improperly primitive). Equivalence is $\mathrm{GL}_{2+m}(\mathbb Z)$-equivalence (`Siegel.IntEquiv`).
Isotropy of the form over $\mathbb Z$, needed for Cassels' hint (Ex. 9), is `isIsotropicZ_of_indefinite`.
*Proof:* Ex. 9 (`Siegel.ex9`) puts an isotropic vector first; then the plane spanned by $e_0$ and $c\,e_1 - \tfrac{a}{2}e_0$
(with $a = f(e_1)$ even) is a unimodular hyperbolic plane and splits off (`split_form`). -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (iii), p. 164"]
theorem ex11_iii (f : QuadForm ℤ (2 + m)) (hf : IsUnimodularCI f) (hind : IsIndefinite f)
    (himp : IsImproperlyPrimitive f) :
    ∃ g : QuadForm ℤ m, IsUnimodularCI g ∧ (∀ i, 2 ∣ g.coeff i i) ∧
      IntEquiv f (QuadForm.orthSum hypPlane g) := by
  obtain ⟨g, hfg, hgu, c, hc, h00, h01, hrow⟩ :=
    exists_normal_form f hf (isIsotropicZ_of_indefinite f hf hind)
  have hsymm := Siegel.casselsMat_isSymm g
  have hgeven : ∀ i, 2 ∣ g.coeff i i := diag_even_of_intEquiv hf.1 hgu.1 hfg himp.2
  obtain ⟨h, hh⟩ := hgeven (Fin.castAdd m 1)
  have hpp : (Pi.single (Fin.castAdd m 0) 1 : Fin (2 + m) → ℤ) ⬝ᵥ
      Siegel.casselsMat g *ᵥ Pi.single (Fin.castAdd m 0) 1 = 0 := by rw [single_bil, h00]
  have hpq : (Pi.single (Fin.castAdd m 0) 1 : Fin (2 + m) → ℤ) ⬝ᵥ
      Siegel.casselsMat g *ᵥ Pi.single (Fin.castAdd m 1) 1 = c := by rw [single_bil, h01]
  have hqq : (Pi.single (Fin.castAdd m 1) 1 : Fin (2 + m) → ℤ) ⬝ᵥ
      Siegel.casselsMat g *ᵥ Pi.single (Fin.castAdd m 1) 1 = g.coeff (Fin.castAdd m 1) (Fin.castAdd m 1) := by
    rw [single_bil, casselsMat_diag]
  obtain ⟨u, v, huv⟩ := exists_hyp_pair hsymm _ _ c hc hpp hpq _ (h) hqq (by rw [hh, two_mul])
  obtain ⟨g', hg', hdiag, hgg'⟩ := equiv_orthSum_of_pair g hgu u v !![0, 1; 1, 0] huv
    (by simp [Matrix.det_fin_two])
  refine ⟨g', hg', fun k => ?_, hfg.trans hgg'⟩
  obtain ⟨y, hy⟩ := hdiag k
  rw [hy]
  exact even_eval_of_diag hgu.1 hgeven y

/-- **Cassels, Ch. 9, Ex. 11 (i)** (p. 164): *let $f$ be indefinite and properly primitive of dimension $n$ (classically
integral of determinant $\pm 1$). Show that it is equivalent to $y_1^2 - y_2^2 + g(\mathbf z)$ for some $g$.* Here $f$ has
$2 + m$ variables, the plane is `oddPlane` $= y_0^2 - y_1^2$ (0-based), the sum is `QuadForm.orthSum`, and $g$ in $m$ variables is
classically integral of determinant $\pm 1$. Equivalence is $\mathrm{GL}_{2+m}(\mathbb Z)$-equivalence (`Siegel.IntEquiv`). The
isotropy of the form over $\mathbb Z$ needed for Ex. 9 is `isIsotropicZ_of_indefinite`.
*Proof:* as for (iii), after Ex. 9; if $a = f(e_1)$ is odd, $u = e_1 + t e_0$ with $t = c\,\tfrac{1-a}{2}$ has norm $1$ and
$v = e_0 - c u$ norm $-1$; if $a$ is even, some $e_i$ ($i \ge 2$) has odd norm and $u = e_1 + e_i + t e_0$ is used instead. -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (i), p. 164"]
theorem ex11_i (f : QuadForm ℤ (2 + m)) (hf : IsUnimodularCI f) (hind : IsIndefinite f)
    (hprop : IsProperlyPrimitive f) :
    ∃ g : QuadForm ℤ m, IsUnimodularCI g ∧ IntEquiv f (QuadForm.orthSum oddPlane g) := by
  obtain ⟨g, hfg, hgu, c, hc, h00, h01, hrow⟩ :=
    exists_normal_form f hf (isIsotropicZ_of_indefinite f hf hind)
  have hsymm := Siegel.casselsMat_isSymm g
  have hodd : ¬ ∀ i, 2 ∣ g.coeff i i := by
    intro hev
    obtain ⟨i, hi⟩ := hprop.2
    exact hi (diag_even_of_intEquiv hgu.1 hf.1 (Siegel.IsometricGL.symm hfg) hev i)
  have hpp : (Pi.single (Fin.castAdd m 0) 1 : Fin (2 + m) → ℤ) ⬝ᵥ
      Siegel.casselsMat g *ᵥ Pi.single (Fin.castAdd m 0) 1 = 0 := by rw [single_bil, h00]
  -- a vector `q` with `p ⬝ G q = c` and odd norm
  have hq : ∃ (q : Fin (2 + m) → ℤ) (N h : ℤ), (Pi.single (Fin.castAdd m 0) 1 : Fin (2 + m) → ℤ) ⬝ᵥ
      Siegel.casselsMat g *ᵥ q = c ∧ q ⬝ᵥ Siegel.casselsMat g *ᵥ q = N ∧ 1 - N = 2 * h := by
    by_cases ha : 2 ∣ g.coeff (Fin.castAdd m 1) (Fin.castAdd m 1)
    · -- some `e_i` with `i ≥ 2` has odd norm
      obtain ⟨k, hi⟩ : ∃ k : Fin m, ¬ 2 ∣ g.coeff (Fin.natAdd 2 k) (Fin.natAdd 2 k) := by
        obtain ⟨i, hi⟩ := not_forall.mp hodd
        induction i using Fin.addCases with
        | left a =>
          exfalso
          fin_cases a
          · apply hi
            have : g.coeff (Fin.castAdd m 0) (Fin.castAdd m 0) = 0 := by rw [← casselsMat_diag]; exact h00
            exact this ▸ dvd_zero _
          · exact hi ha
        | right k => exact ⟨k, hi⟩
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨d, hd⟩ : ∃ d, g.coeff (Fin.natAdd 2 k) (Fin.natAdd 2 k) = 2 * d + 1 := by
        rcases Int.emod_two_eq_zero_or_one (g.coeff (Fin.natAdd 2 k) (Fin.natAdd 2 k)) with h | h
        · exact absurd (Int.dvd_of_emod_eq_zero h) hi
        · exact ⟨g.coeff (Fin.natAdd 2 k) (Fin.natAdd 2 k) / 2, by omega⟩
      refine ⟨Pi.single (Fin.castAdd m 1) 1 + Pi.single (Fin.natAdd 2 k) 1,
        g.coeff (Fin.castAdd m 1) (Fin.castAdd m 1) + g.coeff (Fin.natAdd 2 k) (Fin.natAdd 2 k) +
          2 * Siegel.casselsMat g (Fin.castAdd m 1) (Fin.natAdd 2 k),
        -(a' + d + Siegel.casselsMat g (Fin.castAdd m 1) (Fin.natAdd 2 k)), ?_, ?_, ?_⟩
      · rw [Matrix.mulVec_add, dotProduct_add, single_bil, single_bil, h01, hrow k]
        simp
      · simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, single_bil, casselsMat_diag]
        have : Siegel.casselsMat g (Fin.natAdd 2 k) (Fin.castAdd m 1) =
            Siegel.casselsMat g (Fin.castAdd m 1) (Fin.natAdd 2 k) := hsymm.apply _ _
        rw [this]
        ring
      · rw [ha', hd]; ring
    · -- the norm of `e_1` is odd
      obtain ⟨a', ha'⟩ : ∃ a', g.coeff (Fin.castAdd m 1) (Fin.castAdd m 1) = 2 * a' + 1 := by
        rcases Int.emod_two_eq_zero_or_one (g.coeff (Fin.castAdd m 1) (Fin.castAdd m 1)) with h | h
        · exact absurd (Int.dvd_of_emod_eq_zero h) ha
        · exact ⟨g.coeff (Fin.castAdd m 1) (Fin.castAdd m 1) / 2, by omega⟩
      refine ⟨Pi.single (Fin.castAdd m 1) 1, g.coeff (Fin.castAdd m 1) (Fin.castAdd m 1), -a', ?_, ?_, ?_⟩
      · rw [single_bil, h01]
      · rw [single_bil, casselsMat_diag]
      · rw [ha']; ring
  obtain ⟨q, N, h, hpq, hqq, hh⟩ := hq
  obtain ⟨u, v, huv⟩ := exists_odd_pair hsymm _ q c hc hpp hpq N h hqq hh
  obtain ⟨g', hg', -, hgg'⟩ := equiv_orthSum_of_pair g hgu u v !![1, 0; 0, -1] huv
    (by simp [Matrix.det_fin_two])
  exact ⟨g', hg', hfg.trans hgg'⟩

end Headlines

/-! ### Block sums, real equivalence, and the consequences of (ii) and (iv) -/

section Sums

variable {a b m : ℕ}

/-- Helper: the block-diagonal integer matrix $\operatorname{diag}(A, B)$ on `Fin (a + b)`. -/
def blockMat (A : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℤ :=
  (Matrix.fromBlocks A 0 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Helper: a block-diagonal matrix of symmetric matrices is symmetric. -/
theorem blockMat_isSymm {A : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ} (hA : A.IsSymm)
    (hB : B.IsSymm) : (blockMat A B).IsSymm := by
  ext i j
  simp only [blockMat, Matrix.transpose_apply, Matrix.submatrix_apply]
  have : (Matrix.fromBlocks A 0 0 B)ᵀ = Matrix.fromBlocks A 0 0 B := by
    rw [Matrix.fromBlocks_transpose, hA.eq, hB.eq]; simp
  exact congrFun (congrFun this _) _

/-- Helper: the determinant of a block-diagonal matrix. -/
theorem det_blockMat (A : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) :
    (blockMat A B).det = A.det * B.det := by
  rw [blockMat, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]

/-- Helper: the quadratic form of a block-diagonal matrix. -/
theorem dotProduct_blockMat (A : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ)
    (x : Fin (a + b) → ℤ) :
    x ⬝ᵥ blockMat A B *ᵥ x = (fun i => x (Fin.castAdd b i)) ⬝ᵥ A *ᵥ (fun i => x (Fin.castAdd b i)) +
      (fun j => x (Fin.natAdd a j)) ⬝ᵥ B *ᵥ (fun j => x (Fin.natAdd a j)) := by
  simp [blockMat, dotProduct, Matrix.mulVec, Fin.sum_univ_add, Finset.mul_sum, Matrix.fromBlocks,
    Finset.sum_add_distrib, mul_add]

/-- Helper: the orthogonal sum of two forms given by symmetric Gram matrices is the form of the block-diagonal matrix. -/
theorem orthSum_ofGram {A : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ} (hA : A.IsSymm)
    (hB : B.IsSymm) : QuadForm.orthSum (Siegel.ofGram A) (Siegel.ofGram B) = Siegel.ofGram (blockMat A B) := by
  apply QuadForm.eq_of_eval_eq
  intro x
  rw [Siegel.eval_ofGram (blockMat_isSymm hA hB), dotProduct_blockMat]
  exact (QuadForm.evalIn_orthSum ℤ (Siegel.ofGram A) (Siegel.ofGram B) x).trans
    (congrArg₂ (· + ·) (Siegel.eval_ofGram hA _) (Siegel.eval_ofGram hB _))

/-- Helper: an orthogonal sum of classically integral forms of determinant $\pm 1$ is again such a form. -/
theorem isUnimodularCI_orthSum {P : QuadForm ℤ a} {g : QuadForm ℤ b} (hP : IsUnimodularCI P)
    (hg : IsUnimodularCI g) : IsUnimodularCI (QuadForm.orthSum P g) := by
  rw [← Siegel.ofGram_casselsMat hP.1, ← Siegel.ofGram_casselsMat hg.1,
    orthSum_ofGram (Siegel.casselsMat_isSymm P) (Siegel.casselsMat_isSymm g)]
  refine isUnimodularCI_ofGram (blockMat_isSymm (Siegel.casselsMat_isSymm P) (Siegel.casselsMat_isSymm g)) ?_
  rw [det_blockMat]
  have h1 : IsUnit (Siegel.casselsMat P).det := by rcases hP.2 with h | h <;> rw [h] <;> simp
  have h2 : IsUnit (Siegel.casselsMat g).det := by rcases hg.2 with h | h <;> rw [h] <;> simp
  exact h1.mul h2

/-- Helper: a form in zero variables takes the value zero. -/
theorem eval_dim_zero (Q : QuadForm ℤ 0) (x : Fin 0 → ℤ) : Q.eval x = 0 := by
  simp [QuadForm.evalIn]

/-- Helper: the odd plane is unimodular. -/
theorem isUnimodularCI_oddPlane : IsUnimodularCI oddPlane :=
  isUnimodularCI_ofGram (by ext i j; fin_cases i <;> fin_cases j <;> simp) (by simp [Matrix.det_fin_two])

/-- Helper: the hyperbolic plane is unimodular. -/
theorem isUnimodularCI_hypPlane : IsUnimodularCI hypPlane :=
  isUnimodularCI_ofGram (by ext i j; fin_cases i <;> fin_cases j <;> simp) (by simp [Matrix.det_fin_two])

end Sums

/-! ### Real equivalence -/

section RealEquiv

variable {n m a : ℕ}

/-- Helper: bilinear form of a product, over any commutative ring. -/
theorem bil_mulVec_gen {R : Type*} [CommRing R] {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ R) (M : Matrix κ α R) (N : Matrix κ β R) (x : α → R) (y : β → R) :
    (M *ᵥ x) ⬝ᵥ A *ᵥ (N *ᵥ y) = x ⬝ᵥ (Mᵀ * A * N) *ᵥ y := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Mᵀ, Matrix.vecMul_transpose]

/-- Helper: integral equivalence of classically integral forms gives equivalence over $\mathbb R$. -/
theorem isometricIn_real_of_intEquiv {f g : QuadForm ℤ n} (hf : IsClassicallyIntegral f)
    (hg : IsClassicallyIntegral g) (h : IntEquiv f g) : f.IsometricIn ℝ g := by
  obtain ⟨T, hT⟩ := h
  have hA := (Siegel.eval_mulVec_iff_casselsMat hf hg T.val).mp hT
  refine ⟨(Int.castRingHom ℝ).mapMatrix T.val, ?_, fun x => ?_⟩
  · rw [← RingHom.map_det]
    rcases Siegel.det_GL_int_eq T with hd | hd <;> rw [hd] <;> simp
  · rw [evalIn_eq_casselsMat ℝ hf, evalIn_eq_casselsMat ℝ hg]
    have : (Siegel.casselsMat g).map (Int.castRingHom ℝ) =
        ((Int.castRingHom ℝ).mapMatrix T.val)ᵀ * (Siegel.casselsMat f).map (Int.castRingHom ℝ) *
          (Int.castRingHom ℝ).mapMatrix T.val := by
      have h1 := congrArg (Int.castRingHom ℝ).mapMatrix hA
      rw [map_mul, map_mul] at h1
      have h2 : (Int.castRingHom ℝ).mapMatrix T.valᵀ = ((Int.castRingHom ℝ).mapMatrix T.val)ᵀ := by
        ext i j; rfl
      rw [h2] at h1
      exact h1.symm
    rw [this, bil_mulVec_gen]

/-- Helper: reflexivity of real equivalence of integral forms. -/
theorem isometricIn_real_refl (f : QuadForm ℤ n) : f.IsometricIn ℝ f :=
  ⟨1, by simp, fun x => by rw [Matrix.one_mulVec]⟩

/-- Helper: symmetry of real equivalence of integral forms. -/
theorem isometricIn_real_symm {f g : QuadForm ℤ n} (h : f.IsometricIn ℝ g) : g.IsometricIn ℝ f := by
  obtain ⟨P, hP, e⟩ := h
  refine ⟨P⁻¹, ?_, fun x => ?_⟩
  · exact IsUnit.of_mul_eq_one P.det
      (by rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ hP, Matrix.det_one])
  · rw [← e, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]

/-- Helper: transitivity of real equivalence of integral forms. -/
theorem isometricIn_real_trans {f g h : QuadForm ℤ n} (h1 : f.IsometricIn ℝ g) (h2 : g.IsometricIn ℝ h) :
    f.IsometricIn ℝ h := by
  obtain ⟨P, hP, e1⟩ := h1
  obtain ⟨Q, hQ, e2⟩ := h2
  exact ⟨P * Q, by rw [Matrix.det_mul]; exact hP.mul hQ, fun x => by rw [← Matrix.mulVec_mulVec, e1, e2]⟩

end RealEquiv

/-! ### Statements (ii), (iv) and the consequence (v) -/

section Consequences

variable {n m a : ℕ}

/-- Helper: the block matrix $\operatorname{diag}(S, 1)$ over a commutative ring on `Fin (a + m)`. -/
def blockLin {R : Type*} [CommRing R] (S : Matrix (Fin a) (Fin a) R) : Matrix (Fin (a + m)) (Fin (a + m)) R :=
  (Matrix.fromBlocks S 0 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Helper: $\operatorname{diag}(S, 1)$ acts by $S$ on the first $a$ coordinates. -/
theorem blockLin_mulVec_castAdd {R : Type*} [CommRing R] (S : Matrix (Fin a) (Fin a) R) (x : Fin (a + m) → R) :
    (fun i => (blockLin S *ᵥ x) (Fin.castAdd m i)) = S *ᵥ (fun i => x (Fin.castAdd m i)) := by
  ext i
  simp [blockLin, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]

/-- Helper: $\operatorname{diag}(S, 1)$ fixes the last $m$ coordinates. -/
theorem blockLin_mulVec_natAdd {R : Type*} [CommRing R] (S : Matrix (Fin a) (Fin a) R) (x : Fin (a + m) → R) :
    (fun j => (blockLin S *ᵥ x) (Fin.natAdd a j)) = fun j => x (Fin.natAdd a j) := by
  ext j
  simp [blockLin, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks, Matrix.one_apply]

/-- Helper: $\det \operatorname{diag}(S, 1) = \det S$. -/
theorem det_blockLin {R : Type*} [CommRing R] (S : Matrix (Fin a) (Fin a) R) : (blockLin (m := m) S).det = S.det := by
  rw [blockLin, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

/-- Helper: real values of the hyperbolic plane. -/
theorem evalIn_hypPlane (z : Fin 2 → ℝ) : hypPlane.evalIn ℝ z = 2 * z 0 * z 1 := by
  have hci : IsClassicallyIntegral hypPlane := Siegel.ci_ofGram (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  rw [evalIn_eq_casselsMat ℝ hci, casselsMat_hypPlane]
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
  ring

/-- Helper: real values of the odd plane. -/
theorem evalIn_oddPlane (z : Fin 2 → ℝ) : oddPlane.evalIn ℝ z = z 0 ^ 2 - z 1 ^ 2 := by
  have hci : IsClassicallyIntegral oddPlane := Siegel.ci_ofGram (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  rw [evalIn_eq_casselsMat ℝ hci, casselsMat_oddPlane]
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
  ring

/-- Helper: over $\mathbb R$ the hyperbolic plane is equivalent to the odd plane (substitute $y_0 \pm y_1$ over $\sqrt 2$);
so are the orthogonal sums with any fixed form $g$. -/
theorem isometricIn_real_hyp_odd (g : QuadForm ℤ m) :
    (QuadForm.orthSum hypPlane g).IsometricIn ℝ (QuadForm.orthSum oddPlane g) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  set S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹],
    ![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]] with hS
  refine ⟨blockLin S, ?_, fun x => ?_⟩
  · rw [det_blockLin, hS, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have : (Real.sqrt 2)⁻¹ * -(Real.sqrt 2)⁻¹ - (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = -1 := by
      field_simp
      nlinarith
    rw [this]; simp
  · rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum, blockLin_mulVec_castAdd, blockLin_mulVec_natAdd,
      evalIn_hypPlane, evalIn_oddPlane]
    simp only [hS, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    field_simp
    nlinarith

/-- Helper: the orthogonal sum of the odd plane with any form is indefinite. -/
theorem isIndefinite_orthSum_oddPlane (g : QuadForm ℤ m) : IsIndefinite (QuadForm.orthSum oddPlane g) := by
  constructor
  · refine ⟨Pi.single (Fin.castAdd m 0) 1, ?_⟩
    rw [QuadForm.evalIn_orthSum, evalIn_oddPlane]
    have h0 : (fun b : Fin m => (Pi.single (Fin.castAdd m 0) 1 : Fin (2 + m) → ℝ) (Fin.natAdd 2 b)) = 0 := by
      ext b; simp [Pi.single_apply, Fin.ext_iff]; try omega
    rw [h0]
    simp [Pi.single_apply, Fin.ext_iff, QuadForm.evalIn]
  · refine ⟨Pi.single (Fin.castAdd m 1) 1, ?_⟩
    rw [QuadForm.evalIn_orthSum, evalIn_oddPlane]
    have h0 : (fun b : Fin m => (Pi.single (Fin.castAdd m 1) 1 : Fin (2 + m) → ℝ) (Fin.natAdd 2 b)) = 0 := by
      ext b; simp [Pi.single_apply, Fin.ext_iff]; try omega
    rw [h0]
    simp [Pi.single_apply, Fin.ext_iff, QuadForm.evalIn]

/-- Helper: a classically integral form of determinant $\pm 1$ in at least one variable is primitive: a common divisor of
the entries of Cassels' matrix divides its determinant. -/
theorem isPrimitiveCI_of_unimodular {g : QuadForm ℤ n} (hn : 0 < n) (hg : IsUnimodularCI g) :
    IsPrimitiveCI g := by
  refine ⟨hg.1, fun c hc => ?_⟩
  have hc' : ∀ i j, ∃ z, Siegel.casselsMat g i j = c * z := fun i j => hc i j
  choose z hz using hc'
  have hA : Siegel.casselsMat g = c • Matrix.of z := by
    ext i j; simp [hz i j]
  have hdet : (Siegel.casselsMat g).det = c ^ n * (Matrix.of z).det := by
    rw [hA, Matrix.det_smul, Fintype.card_fin]
  have hu : IsUnit (Siegel.casselsMat g).det := by rcases hg.2 with h | h <;> rw [h] <;> simp
  rw [hdet] at hu
  exact isUnit_of_mul_isUnit_left hu |> fun h => (isUnit_pow_iff hn.ne').mp h

/-- Helper: a form in at least one variable which is classically integral of determinant $\pm 1$ with all diagonal
coefficients even is improperly primitive. -/
theorem isImproperlyPrimitive_of_even {g : QuadForm ℤ n} (hn : 0 < n) (hg : IsUnimodularCI g)
    (he : ∀ i, 2 ∣ g.coeff i i) : IsImproperlyPrimitive g :=
  ⟨isPrimitiveCI_of_unimodular hn hg, he⟩

/-- Helper: the orthogonal sum of the odd plane with a unimodular form is properly primitive. -/
theorem isProperlyPrimitive_orthSum_oddPlane {g : QuadForm ℤ m} (hg : IsUnimodularCI g) :
    IsProperlyPrimitive (QuadForm.orthSum oddPlane g) := by
  refine ⟨isPrimitiveCI_of_unimodular (by omega) (isUnimodularCI_orthSum isUnimodularCI_oddPlane hg),
    Fin.castAdd m 0, ?_⟩
  rw [← QuadForm.eval_single]
  show ¬ 2 ∣ (QuadForm.orthSum oddPlane g).evalIn ℤ _
  rw [QuadForm.evalIn_orthSum]
  have h0 : (fun b : Fin m => (Pi.single (Fin.castAdd m 0) 1 : Fin (2 + m) → ℤ) (Fin.natAdd 2 b)) = 0 := by
    ext b; simp [Pi.single_apply, Fin.ext_iff]; try omega
  rw [h0]
  have h1 : (fun a : Fin 2 => (Pi.single (Fin.castAdd m 0) 1 : Fin (2 + m) → ℤ) (Fin.castAdd m a)) =
      Pi.single 0 1 := by
    ext b; fin_cases b <;> simp [Pi.single_apply, Fin.ext_iff]
  rw [h1]
  have := eval_oddPlane (Pi.single 0 1)
  simp only [QuadForm.eval] at this
  rw [this]
  simp [eval_dim_zero, QuadForm.evalIn]

/-- **Cassels, Ch. 9, Ex. 11 (ii)** (p. 164), *as a statement; proved in `Ch9/Ex11Serre.lean` (`ex11_ii_holds`)*: if $f_1, f_2$ are indefinite and properly
primitive (classically integral of determinant $\pm 1$, in the same number $2 + m$ of variables) and equivalent over
$\mathbb R$, then they are equivalent over $\mathbb Z$. (Serre 1964, 1970: odd indefinite unimodular lattices are classified by
their signature. A proof needs the classification of unimodular $\mathbb Z_p$-lattices and one class in the genus for
indefinite lattices of rank at least $3$, together with the small ranks.) -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (ii), p. 164"]
def Ex11_ii : Prop :=
  ∀ (m : ℕ) (f₁ f₂ : QuadForm ℤ (2 + m)), IsUnimodularCI f₁ → IsUnimodularCI f₂ → IsIndefinite f₁ →
    IsIndefinite f₂ → IsProperlyPrimitive f₁ → IsProperlyPrimitive f₂ → f₁.IsometricIn ℝ f₂ →
      IntEquiv f₁ f₂

/-- **Cassels, Ch. 9, Ex. 11 (iv)** (p. 164), *as a statement; proved in `Ch9/Ex11Cancel.lean` (`ex11_iv_holds`)*: if $g_1, g_2$ (in $m$ variables) are
improperly primitive (classically integral of determinant $\pm 1$) and $y_0^2 - y_1^2 + g_1$, $y_0^2 - y_1^2 + g_2$ are
equivalent, then $2y_0y_1 + g_1$ and $2y_0y_1 + g_2$ are equivalent. (Cassels: "The proof of (iv) is rather difficult.") -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (iv), p. 164"]
def Ex11_iv : Prop :=
  ∀ (m : ℕ) (g₁ g₂ : QuadForm ℤ m), IsUnimodularCI g₁ → IsUnimodularCI g₂ → IsImproperlyPrimitive g₁ →
    IsImproperlyPrimitive g₂ → IntEquiv (QuadForm.orthSum oddPlane g₁) (QuadForm.orthSum oddPlane g₂) →
      IntEquiv (QuadForm.orthSum hypPlane g₁) (QuadForm.orthSum hypPlane g₂)

/-- **Cassels, Ch. 9, Ex. 11 (v)** (p. 164): *let $f_1, f_2$ both be indefinite and improperly primitive (classically integral
of determinant $\pm 1$, in $2 + m$ variables). Show that if they are $\mathbb R$-equivalent then they are $\mathbb Z$-equivalent.*
Conditional on the named statements `Ex11_ii` and `Ex11_iv` (parts (ii) and (iv) of the same example, Cassels' remark that (iv)
"permits the reduction of (v) to (ii)").
*Proof:* by (iii) $f_k \cong 2y_0y_1 + g_k$; the forms $y_0^2 - y_1^2 + g_k$ are properly primitive, indefinite and
$\mathbb R$-equivalent (as $2y_0y_1 \cong y_0^2 - y_1^2$ over $\mathbb R$), so (ii) makes them $\mathbb Z$-equivalent and (iv)
turns this into $2y_0y_1 + g_1 \cong 2y_0y_1 + g_2$. For $m = 0$ the forms $2y_0y_1 + g_k$ coincide. -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (v), p. 164"]
theorem ex11_v (h2 : Ex11_ii) (h4 : Ex11_iv) (f₁ f₂ : QuadForm ℤ (2 + m)) (hf₁ : IsUnimodularCI f₁)
    (hf₂ : IsUnimodularCI f₂) (hi₁ : IsIndefinite f₁) (hi₂ : IsIndefinite f₂)
    (hp₁ : IsImproperlyPrimitive f₁) (hp₂ : IsImproperlyPrimitive f₂) (hR : f₁.IsometricIn ℝ f₂) : IntEquiv f₁ f₂ := by
  obtain ⟨g₁, hg₁, he₁, e₁⟩ := ex11_iii f₁ hf₁ hi₁ hp₁
  obtain ⟨g₂, hg₂, he₂, e₂⟩ := ex11_iii f₂ hf₂ hi₂ hp₂
  have key : IntEquiv (QuadForm.orthSum hypPlane g₁) (QuadForm.orthSum hypPlane g₂) := by
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · refine ⟨1, fun x => ?_⟩
      simp only [Units.val_one, Matrix.one_mulVec]
      have h1 := QuadForm.evalIn_orthSum ℤ hypPlane g₁ x
      have h2 := QuadForm.evalIn_orthSum ℤ hypPlane g₂ x
      have e1 : g₁.evalIn ℤ (fun b => x (Fin.natAdd 2 b)) = 0 := eval_dim_zero g₁ _
      have e2 : g₂.evalIn ℤ (fun b => x (Fin.natAdd 2 b)) = 0 := eval_dim_zero g₂ _
      show (QuadForm.orthSum hypPlane g₁).evalIn ℤ x = (QuadForm.orthSum hypPlane g₂).evalIn ℤ x
      rw [h1, h2, e1, e2]
    · have hH₁ := isUnimodularCI_orthSum isUnimodularCI_hypPlane hg₁
      have hH₂ := isUnimodularCI_orthSum isUnimodularCI_hypPlane hg₂
      have hF₁ := isUnimodularCI_orthSum isUnimodularCI_oddPlane hg₁
      have hF₂ := isUnimodularCI_orthSum isUnimodularCI_oddPlane hg₂
      have hreal : (QuadForm.orthSum oddPlane g₁).IsometricIn ℝ (QuadForm.orthSum oddPlane g₂) := by
        refine isometricIn_real_trans (isometricIn_real_symm (isometricIn_real_hyp_odd g₁)) ?_
        refine isometricIn_real_trans (isometricIn_real_symm (isometricIn_real_of_intEquiv hf₁.1 hH₁.1 e₁)) ?_
        refine isometricIn_real_trans hR ?_
        exact isometricIn_real_trans (isometricIn_real_of_intEquiv hf₂.1 hH₂.1 e₂) (isometricIn_real_hyp_odd g₂)
      have hF := h2 m _ _ hF₁ hF₂ (isIndefinite_orthSum_oddPlane g₁) (isIndefinite_orthSum_oddPlane g₂)
        (isProperlyPrimitive_orthSum_oddPlane hg₁) (isProperlyPrimitive_orthSum_oddPlane hg₂) hreal
      exact h4 m g₁ g₂ hg₁ hg₂ (isImproperlyPrimitive_of_even (by omega) hg₁ he₁)
        (isImproperlyPrimitive_of_even (by omega) hg₂ he₂) hF
  exact e₁.trans (key.trans (Siegel.IsometricGL.symm e₂))

end Consequences

/-! ### Negation, definiteness, and copies of $E_8$ (for Ex. 11 (vi)) -/

section Definite

variable {n m a : ℕ}

/-- **The negative of a form:** $(-f)(\mathbf x) = -f(\mathbf x)$. -/
def negForm (f : QuadForm ℤ n) : QuadForm ℤ n := (-1 : ℤ) • f

/-- Helper: values of the negative form. -/
theorem eval_negForm (f : QuadForm ℤ n) (x : Fin n → ℤ) : (negForm f).eval x = -f.eval x := by
  simp only [negForm, QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Helper: real values of the negative form. -/
theorem evalIn_negForm (f : QuadForm ℤ n) (y : Fin n → ℝ) : (negForm f).evalIn ℝ y = -f.evalIn ℝ y := by
  simp only [negForm, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- Helper: the diagonal coefficients of the negative form. -/
theorem coeff_negForm (f : QuadForm ℤ n) (i j : Fin n) : (negForm f).coeff i j = -f.coeff i j := by
  simp [negForm]

/-- Helper: the negative of a classically integral form is the form of the negated Gram matrix. -/
theorem negForm_eq_ofGram {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) :
    negForm f = Siegel.ofGram (-Siegel.casselsMat f) := by
  apply QuadForm.eq_of_eval_eq
  intro x
  rw [eval_negForm, Siegel.eval_ofGram (Siegel.casselsMat_isSymm f).neg, Matrix.neg_mulVec, dotProduct_neg,
    Siegel.eval_eq_casselsMat hf]

/-- Helper: the negative of a unimodular classically integral form is again one. -/
theorem isUnimodularCI_negForm {f : QuadForm ℤ n} (hf : IsUnimodularCI f) : IsUnimodularCI (negForm f) := by
  rw [negForm_eq_ofGram hf.1]
  refine isUnimodularCI_ofGram (Siegel.casselsMat_isSymm f).neg ?_
  rw [Matrix.det_neg]
  have : IsUnit (Siegel.casselsMat f).det := by rcases hf.2 with h | h <;> rw [h] <;> simp
  exact ((IsUnit.neg isUnit_one).pow _).mul this

/-- Helper: the negative of an indefinite form is indefinite. -/
theorem isIndefinite_negForm {f : QuadForm ℤ n} (h : IsIndefinite f) : IsIndefinite (negForm f) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  exact ⟨⟨y, by rw [evalIn_negForm]; linarith⟩, ⟨x, by rw [evalIn_negForm]; linarith⟩⟩

/-- Helper: a form with a real-nonnegative value everywhere and nonzero Hessian determinant is positive definite. -/
theorem posDef_of_nonneg_real {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate)
    (hnn : ∀ y : Fin n → ℝ, 0 ≤ Q.evalIn ℝ y) : IntQF.PosDef Q := by
  intro x hx
  have hxR : (fun i => (x i : ℝ)) ≠ 0 := by
    intro h; apply hx; funext i; have := congrFun h i; simpa using this
  have hval : Q.evalIn ℝ (fun i => (x i : ℝ)) = (Q.eval x : ℝ) := Siegel.evalIn_intCast (K := ℝ) Q x
  rcases (hnn (fun i => (x i : ℝ))).lt_or_eq with h | h
  · rw [hval] at h; exact_mod_cast h
  exfalso
  set y : Fin n → ℝ := fun i => (x i : ℝ) with hy
  set Hr := Q.hessian.map (algebraMap ℤ ℝ)
  have hB : ∀ w, y ⬝ᵥ (Hr *ᵥ w) = 0 := by
    intro w
    set B := y ⬝ᵥ (Hr *ᵥ w)
    set c := Q.evalIn ℝ w
    have hc : 0 ≤ c := hnn w
    have key : ∀ t : ℝ, 0 ≤ t * B + t ^ 2 * c := by
      intro t
      have hp := QuadForm.polar_eq_hessian ℝ Q y (t • w)
      rw [LocalDensity.evalIn_smul, ← h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at hp
      have := hnn (y + t • w)
      linarith
    have := key (-B / (c + 1))
    have hc1 : 0 < c + 1 := by linarith
    rw [div_pow, neg_sq] at this
    have h' : 0 ≤ -B ^ 2 / (c + 1) ^ 2 := by
      have e : -B / (c + 1) * B + B ^ 2 / (c + 1) ^ 2 * c = -B ^ 2 / (c + 1) ^ 2 := by
        field_simp; ring
      linarith
    have : B ^ 2 ≤ 0 := by
      have := div_nonneg_iff.mp h'
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · nlinarith [sq_nonneg (c + 1)]
    nlinarith [sq_nonneg B]
  have hvec : y ᵥ* Hr = 0 := by
    funext j
    have := hB (Pi.single j 1)
    rw [Matrix.dotProduct_mulVec] at this
    simpa using this
  have hdetr : Hr.det = 0 := Matrix.exists_vecMul_eq_zero_iff.mp ⟨y, hxR, hvec⟩
  have : ((Q.hessian.det : ℤ) : ℝ) = 0 := by
    rw [← hdetr]
    exact RingHom.map_det (algebraMap ℤ ℝ) Q.hessian
  exact hQ (by exact_mod_cast this)

/-- Helper: a classically integral form of determinant $\pm 1$ which is not indefinite is positive definite or negative
definite. -/
theorem posDef_or_posDef_neg {f : QuadForm ℤ n} (hf : IsUnimodularCI f) (hind : ¬ IsIndefinite f) :
    IntQF.PosDef f ∨ IntQF.PosDef (negForm f) := by
  have hnd : f.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [Siegel.hessian_eq_two_smul_casselsMat hf.1, Matrix.det_smul, Fintype.card_fin]
    have : (Siegel.casselsMat f).det ≠ 0 := by rcases hf.2 with h | h <;> rw [h] <;> simp
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) this
  have hndn : (negForm f).Nondegenerate := by
    have hu := isUnimodularCI_negForm hf
    unfold QuadForm.Nondegenerate
    rw [Siegel.hessian_eq_two_smul_casselsMat hu.1, Matrix.det_smul, Fintype.card_fin]
    have : (Siegel.casselsMat (negForm f)).det ≠ 0 := by rcases hu.2 with h | h <;> rw [h] <;> simp
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) this
  unfold IsIndefinite at hind
  by_cases hp : ∃ x : Fin n → ℝ, 0 < f.evalIn ℝ x
  · have hneg : ∀ y : Fin n → ℝ, 0 ≤ f.evalIn ℝ y := by
      intro y
      by_contra hy
      exact hind ⟨hp, ⟨y, not_le.mp hy⟩⟩
    exact Or.inl (posDef_of_nonneg_real hnd hneg)
  · right
    apply posDef_of_nonneg_real hndn
    intro y
    rw [evalIn_negForm]
    push Not at hp
    linarith [hp y]

/-- Helper: an indefinite form has at least two variables. -/
theorem two_le_of_isIndefinite {f : QuadForm ℤ n} (h : IsIndefinite f) : 2 ≤ n := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  by_contra hn
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · simp [QuadForm.evalIn] at hx
  · simp [QuadForm.evalIn] at hx hy
    by_cases hc : (0 : ℝ) < (f.coeff 0 0 : ℝ)
    · nlinarith [mul_nonneg hc.le (mul_self_nonneg (y 0))]
    · nlinarith [mul_nonneg (neg_nonneg.mpr (not_lt.mp hc)) (mul_self_nonneg (x 0))]

/-- Helper: a positive definite form cannot be indefinite. -/
theorem not_isIndefinite_of_posDef {f : QuadForm ℤ n} (h : IntQF.PosDef f) : ¬ IsIndefinite f := by
  rintro ⟨-, ⟨y, hy⟩⟩
  exact absurd (h.evalIn_real_nonneg y) (not_le.mpr hy)

/-- Helper: the dimension of an even unimodular positive definite form is divisible by $8$ (Cassels, Ex. 10). -/
theorem eight_dvd_of_even_posDef {g : QuadForm ℤ m} (hu : IsUnimodularCI g) (he : ∀ i, 2 ∣ g.coeff i i)
    (hp : IntQF.PosDef g) : 8 ∣ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact dvd_zero _
  · refine (Siegel.ex10 m hm).mp ⟨g, hu.1, hp, isImproperlyPrimitive_of_even hm hu he, ?_⟩
    have h1 := Siegel.det_hessian_pos hp
    rw [Siegel.hessian_eq_two_smul_casselsMat hu.1, Matrix.det_smul, Fintype.card_fin] at h1
    rcases hu.2 with h | h
    · exact h
    · rw [h] at h1; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) m]

end Definite

/-! ### Copies of $E_8$, Sylvester's law for positive definite forms, and negation -/

section E8

variable {n m a : ℕ}

/-- Helper: a classically integral form with a given orthogonal-sum structure is classically integral. -/
theorem isClassicallyIntegral_orthSum {P : QuadForm ℤ a} {g : QuadForm ℤ m} (hP : IsClassicallyIntegral P)
    (hg : IsClassicallyIntegral g) : IsClassicallyIntegral (QuadForm.orthSum P g) := by
  rw [← Siegel.ofGram_casselsMat hP, ← Siegel.ofGram_casselsMat hg,
    orthSum_ofGram (Siegel.casselsMat_isSymm P) (Siegel.casselsMat_isSymm g)]
  exact Siegel.ci_ofGram (blockMat_isSymm (Siegel.casselsMat_isSymm P) (Siegel.casselsMat_isSymm g))

/-- Helper: the orthogonal sum of two classically integral forms with even diagonals has even diagonal. -/
theorem diag_even_orthSum {P : QuadForm ℤ a} {g : QuadForm ℤ m} (hP : IsClassicallyIntegral P)
    (hg : IsClassicallyIntegral g) (hPe : ∀ i, 2 ∣ P.coeff i i) (hge : ∀ i, 2 ∣ g.coeff i i) :
    ∀ i, 2 ∣ (QuadForm.orthSum P g).coeff i i := by
  rw [diag_even_iff (isClassicallyIntegral_orthSum hP hg)]
  intro x
  show 2 ∣ (QuadForm.orthSum P g).evalIn ℤ x
  rw [QuadForm.evalIn_orthSum]
  exact dvd_add (even_eval_of_diag hP hPe _) (even_eval_of_diag hg hge _)

/-- Helper: the orthogonal sum of two positive definite forms is positive definite. -/
theorem posDef_orthSum {P : QuadForm ℤ a} {g : QuadForm ℤ m} (hP : IntQF.PosDef P) (hg : IntQF.PosDef g) :
    IntQF.PosDef (QuadForm.orthSum P g) := by
  intro x hx
  show 0 < (QuadForm.orthSum P g).evalIn ℤ x
  rw [QuadForm.evalIn_orthSum]
  by_cases h1 : (fun i => x (Fin.castAdd m i)) = 0
  · have h2 : (fun j => x (Fin.natAdd a j)) ≠ 0 := by
      intro h2
      apply hx
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · exact congrFun h1 i
      · exact congrFun h2 j
    have h3 := hP.eval_nonneg (fun i => x (Fin.castAdd m i))
    have h4 := hg _ h2
    show 0 < P.eval _ + g.eval _
    omega
  · have h3 := hP _ h1
    have h4 := hg.eval_nonneg (fun j => x (Fin.natAdd a j))
    show 0 < P.eval _ + g.eval _
    omega

/-- **$E_8$ with Cassels' normalization:** the classically integral form $2Q_{E_8}$ whose Cassels matrix is the Cartan matrix
of $E_8$ (so $e_8^{C}(\mathbf x) = \mathbf x^{\mathsf T}C\mathbf x$); positive definite, with all diagonal coefficients even
and determinant $1$ (the form $h$ of Cassels, Ch. 9, Ex. 11 (vi)). -/
def e8C : QuadForm ℤ 8 := Siegel.ofGram Siegel.e8.hessian

/-- Helper: the Hessian is symmetric. -/
theorem hessian_isSymm' {k : ℕ} (f : QuadForm ℤ k) : f.hessian.IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp [QuadForm.hessian, add_comm]

/-- Helper: values of `e8C`. -/
theorem eval_e8C (x : Fin 8 → ℤ) : e8C.eval x = 2 * Siegel.e8.eval x := by
  rw [e8C, Siegel.eval_ofGram (hessian_isSymm' _)]
  exact (LocalDensity.two_mul_eval_eq_hessian Siegel.e8 x).symm

/-- Helper: `e8C` is classically integral. -/
theorem ci_e8C : IsClassicallyIntegral e8C := Siegel.ci_ofGram (hessian_isSymm' _)

/-- Helper: `e8C` is classically integral of determinant $1$. -/
theorem isUnimodularCI_e8C : IsUnimodularCI e8C :=
  isUnimodularCI_ofGram (hessian_isSymm' _) (by rw [Siegel.e8_det]; exact isUnit_one)

/-- Helper: `e8C` has even diagonal. -/
theorem diag_even_e8C : ∀ i, 2 ∣ e8C.coeff i i := by
  rw [diag_even_iff ci_e8C]
  intro x
  show 2 ∣ e8C.eval x
  rw [eval_e8C]
  exact dvd_mul_right _ _

/-- Helper: `e8C` is positive definite. -/
theorem posDef_e8C : IntQF.PosDef e8C := by
  intro x hx
  rw [eval_e8C]
  have := Siegel.e8_posDef x hx
  omega

/-- **Copies of $E_8$:** `Mform j` is the orthogonal sum of $j$ copies of `e8C`, a form in $8j$ variables. -/
def Mform : (j : ℕ) → QuadForm ℤ (8 * j)
  | 0 => Siegel.ofGram 0
  | j + 1 => QuadForm.orthSum (Mform j) e8C

/-- Helper: `Mform j` is classically integral. -/
theorem ci_Mform : ∀ j, IsClassicallyIntegral (Mform j)
  | 0 => Siegel.ci_ofGram (by simp [Matrix.IsSymm])
  | j + 1 => isClassicallyIntegral_orthSum (ci_Mform j) ci_e8C

/-- Helper: `Mform j` is classically integral of determinant $\pm 1$. -/
theorem isUnimodularCI_Mform : ∀ j, IsUnimodularCI (Mform j)
  | 0 => isUnimodularCI_ofGram (by simp [Matrix.IsSymm])
      (by
        haveI : IsEmpty (Fin (8 * 0)) := inferInstanceAs (IsEmpty (Fin 0))
        rw [Matrix.det_isEmpty]; exact isUnit_one)
  | j + 1 => isUnimodularCI_orthSum (isUnimodularCI_Mform j) isUnimodularCI_e8C

/-- Helper: `Mform j` has even diagonal. -/
theorem diag_even_Mform : ∀ j i, 2 ∣ (Mform j).coeff i i
  | 0 => fun i => absurd i.2 (by norm_num)
  | j + 1 => diag_even_orthSum (ci_Mform j) ci_e8C (diag_even_Mform j) diag_even_e8C

/-- Helper: `Mform j` is positive definite. -/
theorem posDef_Mform : ∀ j, IntQF.PosDef (Mform j)
  | 0 => fun x hx => absurd (funext fun i => absurd i.2 (by norm_num)) hx
  | j + 1 => posDef_orthSum (posDef_Mform j) posDef_e8C

/-- **Sylvester's law for positive definite integral forms:** two positive definite integral forms in the same number of
variables are equivalent over $\mathbb R$. *Proof:* each is $\sum_i (S\mathbf x)_i^2$ for an invertible matrix $S$
(`Siegel.exists_sqrt_factor`). -/
theorem isometricIn_real_of_posDef {f g : QuadForm ℤ n} (hf : IntQF.PosDef f) (hg : IntQF.PosDef g) :
    f.IsometricIn ℝ g := by
  obtain ⟨Sf, hSf, hdf, hdetf⟩ := Siegel.exists_sqrt_factor (Siegel.gramMatrix f) (Siegel.gramMatrix_isHermitian f)
    (fun x hx => by rw [← Siegel.evalIn_real_eq_gram]; exact hf.evalIn_real_pos x hx)
  obtain ⟨Sg, hSg, hdg, hdetg⟩ := Siegel.exists_sqrt_factor (Siegel.gramMatrix g) (Siegel.gramMatrix_isHermitian g)
    (fun x hx => by rw [← Siegel.evalIn_real_eq_gram]; exact hg.evalIn_real_pos x hx)
  have hf0 : Sf.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdetf; exact (Real.sqrt_pos.mpr hdf).ne' hdetf.symm
  have hg0 : Sg.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdetg; exact (Real.sqrt_pos.mpr hdg).ne' hdetg.symm
  have hu : IsUnit Sf.det := isUnit_iff_ne_zero.mpr hf0
  refine ⟨Sf⁻¹ * Sg, ?_, fun x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero hf0) hg0)
  · rw [Siegel.evalIn_real_eq_gram, hSf, Siegel.evalIn_real_eq_gram, hSg, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- Helper: the block matrix $\operatorname{diag}(1, P)$ on `Fin (a + m)`. -/
def blockLinR {R : Type*} [CommRing R] (P : Matrix (Fin m) (Fin m) R) : Matrix (Fin (a + m)) (Fin (a + m)) R :=
  (Matrix.fromBlocks 1 0 0 P).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Helper: $\operatorname{diag}(1, P)$ fixes the first $a$ coordinates. -/
theorem blockLinR_mulVec_castAdd {R : Type*} [CommRing R] (P : Matrix (Fin m) (Fin m) R) (x : Fin (a + m) → R) :
    (fun i => (blockLinR (a := a) P *ᵥ x) (Fin.castAdd m i)) = fun i => x (Fin.castAdd m i) := by
  ext i
  simp [blockLinR, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks, Matrix.one_apply]

/-- Helper: $\operatorname{diag}(1, P)$ acts by $P$ on the last $m$ coordinates. -/
theorem blockLinR_mulVec_natAdd {R : Type*} [CommRing R] (P : Matrix (Fin m) (Fin m) R) (x : Fin (a + m) → R) :
    (fun j => (blockLinR (a := a) P *ᵥ x) (Fin.natAdd a j)) = P *ᵥ (fun j => x (Fin.natAdd a j)) := by
  ext j
  simp [blockLinR, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]

/-- Helper: $\det \operatorname{diag}(1, P) = \det P$. -/
theorem det_blockLinR {R : Type*} [CommRing R] (P : Matrix (Fin m) (Fin m) R) :
    (blockLinR (a := a) P).det = P.det := by
  rw [blockLinR, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

/-- Helper: equivalence over $\mathbb R$ of the second summand gives equivalence of orthogonal sums. -/
theorem isometricIn_real_orthSum_right (Q : QuadForm ℤ a) {g g' : QuadForm ℤ m} (h : g.IsometricIn ℝ g') :
    (QuadForm.orthSum Q g).IsometricIn ℝ (QuadForm.orthSum Q g') := by
  obtain ⟨P, hP, e⟩ := h
  refine ⟨blockLinR P, ?_, fun x => ?_⟩
  · rw [det_blockLinR]; exact hP
  · rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum, blockLinR_mulVec_castAdd, blockLinR_mulVec_natAdd, e]

/-- Helper: equivalent forms have equivalent negatives. -/
theorem IntEquiv.negForm {f g : QuadForm ℤ n} (h : IntEquiv f g) : IntEquiv (negForm f) (negForm g) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun x => by rw [eval_negForm, eval_negForm, hT]⟩

/-- Helper: $-(2y_0y_1 + g) \cong 2y_0y_1 + (-g)$ (substitute $y_0 \mapsto -y_0$). -/
theorem intEquiv_negForm_orthSum_hyp (g : QuadForm ℤ m) :
    IntEquiv (negForm (QuadForm.orthSum hypPlane g)) (QuadForm.orthSum hypPlane (negForm g)) := by
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1] with hS
  have hSd : IsUnit S.det := by simp [hS, Matrix.det_fin_two]
  refine ⟨glOfUnit (blockLin (m := m) S) (by rw [det_blockLin]; exact hSd), fun x => ?_⟩
  rw [glOfUnit_val, eval_negForm]
  show -(QuadForm.orthSum hypPlane g).evalIn ℤ _ = (QuadForm.orthSum hypPlane (negForm g)).evalIn ℤ x
  rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum, blockLin_mulVec_castAdd, blockLin_mulVec_natAdd]
  show -(hypPlane.eval _ + g.eval _) = hypPlane.eval _ + (negForm g).eval _
  rw [eval_negForm, eval_hypPlane, eval_hypPlane]
  simp [hS, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end E8

/-! ### Ex. 11 (vi) -/

section Vi

variable {n m : ℕ}

/-- **Sums of hyperbolic planes and copies of $E_8$** (the target of Cassels, Ch. 9, Ex. 11 (vi)): `IsHypE8Sum n f` says that the
form $f$ in $n$ variables is equivalent to an orthogonal sum of copies of the hyperbolic plane $2y_0y_1$ (`hypPlane`) and of the
positive definite form $h$ in $8$ variables `e8C` (the form $x^{\mathsf T} C x$ with $C$ the Cartan matrix of $E_8$, classically
integral, improperly primitive, determinant $1$). The constructors are the empty sum, adding a hyperbolic plane on the left,
adding a copy of `e8C` on the right, and replacing a form by an $\mathrm{GL}_n(\mathbb Z)$-equivalent one. -/
inductive IsHypE8Sum : (n : ℕ) → QuadForm ℤ n → Prop
  | nil (Q : QuadForm ℤ 0) : IsHypE8Sum 0 Q
  | hyp {m : ℕ} {g : QuadForm ℤ m} : IsHypE8Sum m g → IsHypE8Sum (2 + m) (QuadForm.orthSum hypPlane g)
  | e8 {m : ℕ} {g : QuadForm ℤ m} : IsHypE8Sum m g → IsHypE8Sum (m + 8) (QuadForm.orthSum g e8C)
  | equiv {n : ℕ} {f g : QuadForm ℤ n} : IsHypE8Sum n g → IntEquiv f g → IsHypE8Sum n f

/-- Helper: `Mform j` is a sum of copies of $E_8$. -/
theorem isHypE8Sum_Mform : ∀ j, IsHypE8Sum (8 * j) (Mform j)
  | 0 => IsHypE8Sum.nil _
  | j + 1 => IsHypE8Sum.e8 (isHypE8Sum_Mform j)

/-- Helper: indefiniteness is invariant under equivalence over $\mathbb R$. -/
theorem isIndefinite_of_isometricIn {f g : QuadForm ℤ n} (h : f.IsometricIn ℝ g) (hg : IsIndefinite g) :
    IsIndefinite f := by
  obtain ⟨P, -, e⟩ := h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hg
  exact ⟨⟨P *ᵥ x, by rw [e]; exact hx⟩, ⟨P *ᵥ y, by rw [e]; exact hy⟩⟩

/-- Helper: the hyperbolic plane is classically integral. -/
theorem ci_hypPlane : IsClassicallyIntegral hypPlane :=
  Siegel.ci_ofGram (by ext i j; fin_cases i <;> fin_cases j <;> simp)

/-- Helper: the hyperbolic plane has even diagonal. -/
theorem diag_even_hypPlane : ∀ i, 2 ∣ hypPlane.coeff i i := by
  rw [diag_even_iff ci_hypPlane]
  intro x
  show 2 ∣ hypPlane.eval x
  rw [eval_hypPlane]
  exact ⟨x 0 * x 1, by ring⟩

/-- Helper: an even unimodular form in $2 + 8j$ variables which is indefinite and $\mathbb R$-equivalent to
$2y_0y_1 + E_8^{\perp j}$ is a sum of copies of hyperbolic planes and $E_8$, given (ii) and (iv). -/
theorem isHypE8Sum_of_isometricIn (h2 : Ex11_ii) (h4 : Ex11_iv) {j : ℕ} (g : QuadForm ℤ (2 + 8 * j))
    (hu : IsUnimodularCI g) (he : ∀ i, 2 ∣ g.coeff i i) (hind : IsIndefinite g)
    (hR : g.IsometricIn ℝ (QuadForm.orthSum hypPlane (Mform j))) :
    IsHypE8Sum (2 + 8 * j) g := by
  have hFu := isUnimodularCI_orthSum isUnimodularCI_hypPlane (isUnimodularCI_Mform j)
  have hFe := diag_even_orthSum ci_hypPlane (ci_Mform j) diag_even_hypPlane (diag_even_Mform j)
  have hFind : IsIndefinite (QuadForm.orthSum hypPlane (Mform j)) :=
    isIndefinite_of_isometricIn (isometricIn_real_hyp_odd (Mform j)) (isIndefinite_orthSum_oddPlane _)
  have hequiv : IntEquiv g (QuadForm.orthSum hypPlane (Mform j)) :=
    ex11_v h2 h4 g _ hu hFu hind hFind (isImproperlyPrimitive_of_even (by omega) hu he)
      (isImproperlyPrimitive_of_even (by omega) hFu hFe) hR
  exact IsHypE8Sum.equiv (IsHypE8Sum.hyp (isHypE8Sum_Mform j)) hequiv

/-- Helper: the even unimodular forms either are definite or, after one more hyperbolic plane, are sums of hyperbolic planes
and $E_8$ (or their negatives are). -/
theorem claim_vi (h2 : Ex11_ii) (h4 : Ex11_iv) :
    ∀ (k : ℕ) (g : QuadForm ℤ k), IsUnimodularCI g → (∀ i, 2 ∣ g.coeff i i) →
      IntQF.PosDef g ∨ IntQF.PosDef (negForm g) ∨ IsHypE8Sum k g ∨ IsHypE8Sum k (negForm g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g hu he
  by_cases hind : IsIndefinite g
  · obtain ⟨m, rfl⟩ : ∃ m, k = 2 + m := ⟨k - 2, by have := two_le_of_isIndefinite hind; omega⟩
    have himp := isImproperlyPrimitive_of_even (by omega) hu he
    obtain ⟨g', hg'u, hg'e, e⟩ := ex11_iii g hu hind himp
    have hHu : IsUnimodularCI (QuadForm.orthSum hypPlane g') :=
      isUnimodularCI_orthSum isUnimodularCI_hypPlane hg'u
    have hnegu : IsUnimodularCI (negForm g) := isUnimodularCI_negForm hu
    have hnege : ∀ i, 2 ∣ (negForm g).coeff i i := fun i => by
      rw [coeff_negForm]; exact (dvd_neg.mpr (he i))
    have hg'ne : IsUnimodularCI (negForm g') := isUnimodularCI_negForm hg'u
    have hg'nee : ∀ i, 2 ∣ (negForm g').coeff i i := fun i => by
      rw [coeff_negForm]; exact (dvd_neg.mpr (hg'e i))
    have eneg : IntEquiv (negForm g) (QuadForm.orthSum hypPlane (negForm g')) :=
      Siegel.IsometricGL.trans (IntEquiv.negForm e) (intEquiv_negForm_orthSum_hyp g')
    right; right
    rcases ih m (by omega) g' hg'u hg'e with hp | hp | hs | hs
    · obtain ⟨j, rfl⟩ := eight_dvd_of_even_posDef hg'u hg'e hp
      left
      refine isHypE8Sum_of_isometricIn h2 h4 g hu he hind ?_
      exact isometricIn_real_trans (isometricIn_real_of_intEquiv hu.1 hHu.1 e)
        (isometricIn_real_orthSum_right hypPlane (isometricIn_real_of_posDef hp (posDef_Mform j)))
    · obtain ⟨j, rfl⟩ := eight_dvd_of_even_posDef hg'ne hg'nee hp
      right
      refine isHypE8Sum_of_isometricIn h2 h4 (negForm g) hnegu hnege (isIndefinite_negForm hind) ?_
      exact isometricIn_real_trans
        (isometricIn_real_of_intEquiv hnegu.1
          (isClassicallyIntegral_orthSum ci_hypPlane hg'ne.1) eneg)
        (isometricIn_real_orthSum_right hypPlane (isometricIn_real_of_posDef hp (posDef_Mform j)))
    · exact Or.inl (IsHypE8Sum.equiv (IsHypE8Sum.hyp hs) e)
    · exact Or.inr (IsHypE8Sum.equiv (IsHypE8Sum.hyp hs) eneg)
  · rcases posDef_or_posDef_neg hu hind with hp | hp
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)

/-- **Cassels, Ch. 9, Ex. 11 (vi)** (p. 164): *let $f$ be indefinite and improperly primitive (classically integral of
determinant $\pm 1$). Show that either $+f$ or $-f$ is equivalent to a sum of copies of the forms $2x_1x_2$ and $h(x_1, \dots,
x_8)$, where $h$ is positive definite* (cf. Ex. 10). Here the sum is `IsHypE8Sum` (hyperbolic planes `hypPlane` and copies of the
positive definite form `e8C` in $8$ variables, i.e. $h$ is $E_8$), and $-f$ is `negForm f`. Conditional on the named statements
`Ex11_ii` and `Ex11_iv` (parts (ii), (iv) of the same example; Cassels' remark that (iv) reduces (v) to (ii)).
*Proof:* by (iii) peel off hyperbolic planes $2y_0y_1$ until the rest is definite (the induction `claim_vi`); a definite rest
$g'$ (positive or negative) has $8 \mid \dim g'$ by Ex. 10 and is $\mathbb R$-equivalent to $E_8^{\perp j}$ (Sylvester), so
$2y_0y_1 + g' \cong 2y_0y_1 + E_8^{\perp j}$ by (v). -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (vi), p. 164"]
theorem ex11_vi (h2 : Ex11_ii) (h4 : Ex11_iv) (f : QuadForm ℤ n)
    (hf : IsUnimodularCI f) (hind : IsIndefinite f) (hp : IsImproperlyPrimitive f) :
    IsHypE8Sum n f ∨ IsHypE8Sum n (negForm f) := by
  rcases claim_vi h2 h4 n f hf hp.2 with h | h | h | h
  · exact absurd hind (not_isIndefinite_of_posDef h)
  · exact absurd (isIndefinite_negForm hind) (not_isIndefinite_of_posDef h)
  · exact Or.inl h
  · exact Or.inr h

end Vi

end QuadFormsKB.Cassels.Ch9Ex11
