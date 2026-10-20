/-
# Local densities of forms by forms over a DVR: definitions and the bridge to numbers

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$ and residue field of size $q$, e.g. the
completion $\mathfrak o_\mathfrak p$ of a number field at a finite prime, or $\mathbb Z_p$).

**Defines**
* `QuadForm.compMat Q X`: for $Q$ in $n$ variables and an $n \times r$ matrix $X$ (columns $X_0, \dots, X_{r-1}$), the
  form $Q \circ X$ in $r$ variables, $(Q \circ X)(\vec y) = Q(X\vec y)$ (`eval_compMat`). Its coefficients are
  $Q(X_i)$ on the diagonal and $B_Q(X_i, X_j) = X_i^{\mathsf T} H_Q X_j$ above it, and its Hessian is
  $X^{\mathsf T} H_Q X$ (`hessian_compMat`).
* `DVR.repCountForm Q T π k` $= A_{\pi^k}(Q, T)$, the number of $X \in M_{n \times r}(R/\pi^k)$ with
  $Q \circ X = T$ **as quadratic forms over $R/\pi^k$** (equality of all coefficients);
* `DVR.localDensityForm Q T π` $= \beta_\pi(Q, T) = \lim_k A_{\pi^k}(Q, T) / q^{k(nr - r(r+1)/2)}$;
* `DVR.siegelDensity Q T π` $= \varepsilon_{n,r}\,\beta_\pi(Q, T)$ with $\varepsilon = \tfrac12$ if $n = r$ and $1$
  otherwise (Siegel's normalization of $\alpha_p(S, T)$; Kitaoka 1993, §5.6 [unverified]).

**Proves** the bridge to densities of numbers: for $T = \langle m \rangle$ ($r = 1$),
`repCountForm_unary` $A_{\pi^k}(Q, \langle m\rangle) = r_{\pi^k}(m)$ and `localDensityForm_unary`
$\beta_\pi(Q, \langle m\rangle) = \beta_\pi(m)$ (the repo's `DVR.repCount`, `DVR.localDensity`).

*Conventions.* The condition "$Q \circ X = T$ as quadratic forms" is the repo's `QuadForm` convention
$Q(\vec x) = \sum_{i \le j} c_{ij} x_i x_j$ (no halving): at a non-dyadic prime it is the Gram-matrix condition
$X^{\mathsf T} A_Q X = A_T$ with $A = \tfrac12 H$; at a dyadic prime it is the finer *quadratic* condition
(diagonal values $Q(X_i) = T_{ii}$, not only $2Q(X_i) = 2T_{ii}$), which is the one that makes $r = 1$ the density
of numbers. The exponent $nr - r(r+1)/2 = \dim M_{n\times r} - \dim \mathrm{Sym}_r$ is Siegel's
(Siegel 1935, §1; Kitaoka 1993, §5.6 [unverified]); it is truncated subtraction in `ℕ`, meaningful for $r \le n$.
**Depends on** `DVRGeneral.lean` (and through it `Lemma32.lean`). Indices are 0-based.
-/
import QuadFormsKB.LocalDensity.DVRGeneral

namespace QuadFormsKB

open Matrix

set_option linter.deprecated false

namespace QuadForm

variable {A : Type*} [CommRing A] {n r : ℕ}

/-- **The composite form** $Q \circ X$ for $Q$ in $n$ variables and $X \in M_{n \times r}(A)$ with columns
$X_0, \dots, X_{r-1}$: the form in $r$ variables with coefficients
$$c'_{ii} = Q(X_i), \qquad c'_{ij} = X_i^{\mathsf T} H_Q X_j = B_Q(X_i, X_j) \quad (i < j),$$
so that $(Q \circ X)(\vec y) = Q(X \vec y)$ (`eval_compMat`). This is the form of the sublattice (or the
representation) spanned by the columns of $X$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
def compMat (Q : QuadForm A n) (X : Matrix (Fin n) (Fin r) A) : QuadForm A r :=
  QuadForm.ofUpper fun i j =>
    if i = j then Q.eval (fun l => X l i) else (fun l => X l i) ⬝ᵥ (Q.hessian *ᵥ fun l => X l j)

theorem compMat_coeff (Q : QuadForm A n) (X : Matrix (Fin n) (Fin r) A) (i j : Fin r) :
    (Q.compMat X).coeff i j = if i ≤ j then
      (if i = j then Q.eval (fun l => X l i) else (fun l => X l i) ⬝ᵥ (Q.hessian *ᵥ fun l => X l j))
      else 0 := rfl

/-- $Q(\vec x) = \vec x^{\mathsf T} C \vec x$ over the coefficient ring. -/
theorem eval_eq_dotProduct' (Q : QuadForm A n) (x : Fin n → A) : Q.eval x = x ⬝ᵥ (Q.coeff *ᵥ x) := by
  rw [QuadForm.eval, evalIn_eq_dotProduct]
  simp

/-- The polarization identity over the coefficient ring: $Q(\vec x + \vec y) - Q(\vec x) - Q(\vec y) = \vec x^{\mathsf T} H \vec y$. -/
theorem eval_polar (Q : QuadForm A n) (x y : Fin n → A) :
    Q.eval (x + y) - Q.eval x - Q.eval y = x ⬝ᵥ (Q.hessian *ᵥ y) := by
  have h := polar_eq_hessian A Q x y
  simpa using h

/-- $\vec x^{\mathsf T} H \vec x = 2 Q(\vec x)$. -/
theorem dotProduct_hessian_self (Q : QuadForm A n) (x : Fin n → A) :
    x ⬝ᵥ (Q.hessian *ᵥ x) = 2 * Q.eval x := by
  rw [hessian, add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec, ← eval_eq_dotProduct']
  ring

/-- The entries of $X^{\mathsf T} C X$ are $X_a^{\mathsf T} C X_b$ (columns $X_a, X_b$). -/
theorem transpose_mul_mul_apply (C : Matrix (Fin n) (Fin n) A) (X : Matrix (Fin n) (Fin r) A)
    (a b : Fin r) : (Xᵀ * C * X) a b = (fun l => X l a) ⬝ᵥ (C *ᵥ fun l => X l b) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- $\vec y^{\mathsf T} M \vec y = \sum_{i,j} M_{ij} y_i y_j$. -/
theorem dotProduct_mulVec_self (M : Matrix (Fin r) (Fin r) A) (y : Fin r → A) :
    y ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, M i j * y i * y j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Symmetrizing a double sum over the upper triangle. -/
theorem sum_upper_symm (M : Matrix (Fin r) (Fin r) A) (y : Fin r → A) :
    ∑ i, ∑ j, M i j * y i * y j =
      ∑ i, ∑ j, if i ≤ j then (if i = j then M i i else M i j + M j i) * y i * y j else 0 := by
  have h1 : ∀ i j, M i j * y i * y j = (if i ≤ j then M i j * y i * y j else 0) +
      (if j < i then M i j * y i * y j else 0) := by
    intro i j
    by_cases h : i ≤ j
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · rw [if_neg h, if_pos (lt_of_not_ge h), zero_add]
  have h2 : ∀ i j, (if i ≤ j then (if i = j then M i i else M i j + M j i) * y i * y j else 0) =
      (if i ≤ j then M i j * y i * y j else 0) + (if i < j then M j i * y j * y i else 0) := by
    intro i j
    by_cases h : i ≤ j
    · by_cases he : i = j
      · subst he
        rw [if_pos h, if_pos h, if_pos rfl, if_neg (lt_irrefl _), add_zero]
      · rw [if_pos h, if_pos h, if_neg he, if_pos (lt_of_le_of_ne h he)]
        ring
    · rw [if_neg h, if_neg h, if_neg (fun h' => h h'.le), add_zero]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j,
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h2 i j]
  simp only [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- **$(Q \circ X)(\vec y) = Q(X\vec y)$.** -/
theorem eval_compMat (Q : QuadForm A n) (X : Matrix (Fin n) (Fin r) A) (y : Fin r → A) :
    (Q.compMat X).eval y = Q.eval (X *ᵥ y) := by
  set M : Matrix (Fin r) (Fin r) A := Xᵀ * Q.coeff * X with hM
  have key : Q.eval (X *ᵥ y) = ∑ i, ∑ j, M i j * y i * y j := by
    have : y ⬝ᵥ (M *ᵥ y) = (X *ᵥ y) ⬝ᵥ (Q.coeff *ᵥ (X *ᵥ y)) := by
      rw [hM, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [eval_eq_dotProduct', ← this, dotProduct_mulVec_self]
  have hd : ∀ i, Q.eval (fun l => X l i) = M i i := by
    intro i; rw [hM, transpose_mul_mul_apply, eval_eq_dotProduct']
  have ho : ∀ i j, (fun l => X l i) ⬝ᵥ (Q.hessian *ᵥ fun l => X l j) = M i j + M j i := by
    intro i j
    rw [hM, transpose_mul_mul_apply, transpose_mul_mul_apply, hessian, add_mulVec, dotProduct_add,
      Matrix.dotProduct_transpose_mulVec]
  rw [key, sum_upper_symm]
  show (∑ i, ∑ j, if i ≤ j then algebraMap A A ((Q.compMat X).coeff i j) * y i * y j else 0) = _
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [compMat_coeff]
  by_cases hij : i ≤ j
  · rw [if_pos hij, if_pos hij, if_pos hij]
    by_cases he : i = j
    · subst he; rw [if_pos rfl, if_pos rfl, hd]
    · rw [if_neg he, if_neg he, ho]
  · rw [if_neg hij, if_neg hij]

/-- **The Hessian of $Q \circ X$ is $X^{\mathsf T} H_Q X$.** -/
theorem hessian_compMat (Q : QuadForm A n) (X : Matrix (Fin n) (Fin r) A) :
    (Q.compMat X).hessian = Xᵀ * Q.hessian * X := by
  have hsymm : ∀ a b, (fun l => X l a) ⬝ᵥ (Q.hessian *ᵥ fun l => X l b) = (Xᵀ * Q.hessian * X) a b :=
    fun a b => (transpose_mul_mul_apply _ X a b).symm
  have hT : ∀ a b, (Xᵀ * Q.hessian * X) a b = (Xᵀ * Q.hessian * X) b a := by
    intro a b
    rw [← hsymm, ← hsymm, ← Matrix.dotProduct_transpose_mulVec]
    congr 2
    simp [hessian, add_comm]
  ext i j
  show (Q.compMat X).coeff i j + (Q.compMat X).coeff j i = _
  simp only [compMat_coeff]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h.le, if_neg h.ne, if_neg (not_le.mpr h), add_zero, hsymm]
  · subst h
    rw [if_pos le_rfl, if_pos rfl, ← two_mul, ← dotProduct_hessian_self, hsymm]
  · simp only [if_neg (not_le.mpr h), if_pos h.le, if_neg h.ne', zero_add]
    rw [hsymm, hT]
    simp [h.ne]

/-- Base change commutes with composition: $f(Q) \circ f(X) = f(Q \circ X)$. -/
theorem map_compMat {B : Type*} [CommRing B] (f : A →+* B) (Q : QuadForm A n)
    (X : Matrix (Fin n) (Fin r) A) : (Q.map f).compMat (X.map f) = (Q.compMat X).map f := by
  ext i j
  simp only [compMat_coeff, QuadForm.map, Matrix.map_apply, QuadForm.eval, QuadForm.evalIn,
    Algebra.algebraMap_self, RingHom.id_apply, hessian, dotProduct, mulVec, Matrix.add_apply,
    Matrix.transpose_apply]
  split_ifs <;> simp [map_sum, map_mul, map_add, apply_ite f]

/-- A form is determined by its coefficients on and above the diagonal. -/
theorem ext_upper {Q₁ Q₂ : QuadForm A r} (h : ∀ i j, i ≤ j → Q₁.coeff i j = Q₂.coeff i j) : Q₁ = Q₂ := by
  ext i j
  by_cases hij : i ≤ j
  · exact h i j hij
  · rw [Q₁.upper (show id j < id i from not_le.mp hij), Q₂.upper (show id j < id i from not_le.mp hij)]

end QuadForm

namespace LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n r : ℕ}

/-- **$A_{\pi^k}(Q, T)$, the number of representations of $T$ by $Q$ mod $\pi^k$** (Siegel 1935; Kitaoka 1993,
§5.6 [unverified]): the number of $X \in M_{n \times r}(R/\pi^k)$ with $Q \circ X = T$ as quadratic forms over
$R/\pi^k$, i.e. $Q(X_i) \equiv T_{ii}$ and $B_Q(X_i, X_j) \equiv T_{ij}$ ($i < j$) mod $\pi^k$ for the columns
$X_0, \dots, X_{r-1}$ of $X$. For $r = 1$ this is $r_{\pi^k}(m)$ (`repCountForm_unary`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
noncomputable def repCountForm (Q : QuadForm R n) (T : QuadForm R r) (π : R) (k : ℕ) : ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin r) (R ⧸ Ideal.span {π ^ k}) //
    (Q.map (Ideal.Quotient.mk _)).compMat X = T.map (Ideal.Quotient.mk _)}

/-- **The local density of $T$ by $Q$**, $\beta_\pi(Q, T) = \lim_k A_{\pi^k}(Q, T)/q^{k(nr - r(r+1)/2)}$ (Siegel 1935;
Kitaoka 1993, §5.6 [unverified]; Lean's `limUnder`). It is a genuine limit, attained for large $k$, whenever $T$
is nondegenerate (`localDensityForm_eventually_eq` in `FormDensityStab.lean`). No factor $\tfrac12$ is included
even when $n = r$; that is `siegelDensity`. For $r = 1$, $T = \langle m\rangle$ it is $\beta_\pi(m)$
(`localDensityForm_unary`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
noncomputable def localDensityForm (Q : QuadForm R n) (T : QuadForm R r) (π : R) : ℝ :=
  Filter.limUnder Filter.atTop fun k : ℕ =>
    (repCountForm Q T π k : ℝ) / (q R : ℝ) ^ (k * (n * r - r * (r + 1) / 2))

/-- **Siegel's normalization** $\alpha_\pi(Q, T) = \varepsilon_{n,r}\,\beta_\pi(Q, T)$ with $\varepsilon_{n,r} = \tfrac12$
if $n = r$ and $1$ otherwise (Siegel 1935; Kitaoka 1993, §5.6 [unverified]). With it the mass formula reads
$\sum_i 1/|O(L_i)| = 2 \prod_p \alpha_p(L, L)^{-1} \cdot (\text{archimedean factor})$. The factor $\tfrac12$ is
$1/[O(L_p) : SO(L_p)]$: $\alpha_p(L, L) = \mathrm{vol}(SO(L_p))$ for the gauge-form measure (`Tamagawa.volSO_eq`); this makes
$\prod_p\alpha_p$ converge (*update* of an earlier docstring, which attributed the $\tfrac12$ to $\pm1 \in O(L_p)$; for even
$n$, $-1 \in SO$). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
noncomputable def siegelDensity (Q : QuadForm R n) (T : QuadForm R r) (π : R) : ℝ :=
  (if n = r then (1 / 2 : ℝ) else 1) * localDensityForm Q T π

/-- The unary form $\langle m \rangle = m x_0^2$. -/
def unary (m : R) : QuadForm R 1 := QuadForm.diag fun _ => m

theorem evalIn_eq_eval_map' {A : Type*} [CommRing A] (f : R →+* A) (Q : QuadForm R n) (x : Fin n → A)
    [Algebra R A] (hf : algebraMap R A = f) : Q.evalIn A x = (Q.map f).eval x := by
  subst hf
  simp [QuadForm.evalIn, QuadForm.map]

/-- **The bridge to densities of numbers ($r = 1$):** $A_{\pi^k}(Q, \langle m \rangle) = r_{\pi^k}(m)$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem repCountForm_unary (Q : QuadForm R n) (π : R) (k : ℕ) (m : R) :
    repCountForm Q (unary m) π k = repCount Q π k m := by
  unfold repCountForm repCount
  refine Nat.card_congr ?_
  let e : Matrix (Fin n) (Fin 1) (R ⧸ Ideal.span {π ^ k}) ≃ (Fin n → R ⧸ Ideal.span {π ^ k}) :=
    { toFun := fun X l => X l 0
      invFun := fun x => Matrix.of fun l _ => x l
      left_inv := fun X => by ext l i; rw [Fin.fin_one_eq_zero i]; rfl
      right_inv := fun x => rfl }
  refine Equiv.subtypeEquiv e ?_
  intro X
  show _ ↔ Q.evalIn _ (fun l => X l 0) = _
  rw [evalIn_eq_eval_map' (Ideal.Quotient.mk _) Q _ (Ideal.Quotient.algebraMap_eq _)]
  constructor
  · intro h
    have := congrArg (fun T : QuadForm _ 1 => T.coeff 0 0) h
    simpa [compMat_coeff, unary, QuadForm.map, QuadForm.diag] using this
  · intro h
    apply ext_upper
    intro i j _
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simpa [compMat_coeff, unary, QuadForm.map, QuadForm.diag] using h

/-- **$\beta_\pi(Q, \langle m \rangle) = \beta_\pi(m)$:** the density of forms by forms at $r = 1$ is the repo's
density of numbers (`DVR.localDensity`); the exponents agree, $n \cdot 1 - 1 = n - 1$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_unary (Q : QuadForm R n) (π : R) (m : R) :
    localDensityForm Q (unary m) π = localDensity Q π m := by
  unfold localDensityForm localDensity
  congr 1
  funext k
  rw [repCountForm_unary]
  congr 3
  simp

end LocalDensity.DVR

end QuadFormsKB
