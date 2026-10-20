/-
# Over $\mathbb{Q}$: quadratic polynomials $\iff$ symmetric Gram matrices

The primary definition (`Defs/QuadForm.lean`) is the polynomial
$Q(\vec{x}) = \sum_{0 \le i \le j < n} c_{ij}\, x_i x_j$ (upper-triangular $C$). Over
$\mathbb{Q}$, where $2$ is a unit, it is equivalent to the **symmetric Gram-matrix** definition
$Q(\vec{x}) = \vec{x}^{\mathsf T} A\, \vec{x}$:
$$A = \tfrac12 (C + C^{\mathsf T}) \quad (\texttt{gram}), \qquad
c_{ii} = A_{ii},\ \ c_{ij} = 2A_{ij}\ (i < j) \quad (\texttt{ofGram}).$$
These maps are mutually inverse and preserve values over every field $K \supseteq \mathbb{Q}$.
Over $\mathbb{Z}$ they are not: `gram` leaves $\mathbb{Z}$ exactly when some cross coefficient is
odd. That is the "integral vs. classically integral" distinction of `Equiv/Integral.lean`.
-/
import QuadFormsKB.Defs.Rational

open Matrix

namespace QuadFormsKB.RatQF

variable {n : ℕ}

/-- **The Gram matrix of a rational form:** the symmetric matrix
$A = \tfrac12 (C + C^{\mathsf T})$ over $\mathbb{Q}$ (half the Hessian), so that
$Q(\vec{x}) = \vec{x}^{\mathsf T} A\, \vec{x}$ (`evalIn_eq_gram`). -/
def gram (Q : RatQF n) : Matrix (Fin n) (Fin n) ℚ := (1 / 2 : ℚ) • Q.hessian

/-- **The rational form with a given Gram matrix** $A$ (intended for symmetric $A$): coefficients
$c_{ii} = A_{ii}$ and $c_{ij} = 2 A_{ij}$ for $i < j$ ($0$ below the diagonal). For symmetric
$A$ its values are $\vec{x}^{\mathsf T} A\, \vec{x}$ (`evalIn_ofGram`). -/
def ofGram (A : Matrix (Fin n) (Fin n) ℚ) : RatQF n where
  coeff := Matrix.of fun i j => if i = j then A i j else if i < j then 2 * A i j else 0
  upper := by
    intro i j h
    simp only [id] at h
    simp only [Matrix.of_apply, ite_eq_right h.ne', ite_eq_right (not_lt.mpr h.le)]

/-- **The Gram matrix is symmetric:** $A^{\mathsf T} = A$. -/
@[kb "cassels1978" "Ch. 2, §1"]
theorem gram_isSymm (Q : RatQF n) : Q.gram.IsSymm := by
  ext i j
  simp [gram, QuadFormsKB.QuadForm.hessian]
  ring

/-- **Values via the Gram matrix:** $Q(\vec{x}) = \vec{x}^{\mathsf T} A\, \vec{x}$ for all
$\vec{x} \in K^n$, over every field $K \supseteq \mathbb{Q}$, where $A = $ `gram Q`. -/
@[kb "cassels1978" "Ch. 2, §1"]
theorem evalIn_eq_gram (K : Type*) [Field K] [CharZero K] (Q : RatQF n) (x : Fin n → K) :
    Q.evalIn K x = x ⬝ᵥ (Q.gram.map (algebraMap ℚ K) *ᵥ x) := by
  have hS : QuadForm.evalIn K Q x = ∑ i, ∑ j, algebraMap ℚ K (Q.coeff i j) * x i * x j := by
    unfold QuadForm.evalIn
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · rw [Q.upper (lt_of_not_ge h)]; simp
  have hT : ∑ i, ∑ j, algebraMap ℚ K (Q.coeff j i) * x i * x j = ∑ i, ∑ j, algebraMap ℚ K (Q.coeff i j) * x i * x j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have : x ⬝ᵥ ((Q.gram).map (algebraMap ℚ K) *ᵥ x) = (1/2 : K) * ((∑ i, ∑ j, algebraMap ℚ K (Q.coeff i j) * x i * x j) + ∑ i, ∑ j, algebraMap ℚ K (Q.coeff j i) * x i * x j) := by
    simp only [dotProduct, mulVec, RatQF.gram, QuadForm.hessian, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp
    ring
  rw [this, hT, hS]; ring

/-- **Values of `ofGram`:** for a symmetric rational matrix $A$, the form `ofGram A` takes
the value $\vec{x}^{\mathsf T} A\, \vec{x}$ at every $\vec{x} \in K^n$ ($K \supseteq \mathbb{Q}$ a
field). -/
@[kb "cassels1978" "Ch. 2, §1"]
theorem evalIn_ofGram (K : Type*) [Field K] [CharZero K] (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : A.IsSymm) (x : Fin n → K) :
    (ofGram A).evalIn K x = x ⬝ᵥ (A.map (algebraMap ℚ K) *ᵥ x) := by
  set f : Fin n → Fin n → K := fun i j => algebraMap ℚ K (A i j) * x i * x j with hf
  have hsym : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf]
    rw [show A j i = A i j from by simpa using congrFun (congrFun hA i) j]; ring
  have hR : x ⬝ᵥ (A.map (algebraMap ℚ K) *ᵥ x) = ∑ i, ∑ j, f i j := by
    simp only [dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum, hf]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hL : (ofGram A).evalIn K x
      = ∑ i, ∑ j, ((if i < j then 2 * f i j else 0) + (if i = j then f i j else 0)) := by
    simp only [QuadForm.evalIn, RatQF.ofGram, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.le, h.ne, hf]; ring
    · subst h; simp [hf]
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if i = j then f i j else 0)
      + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hswap : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]
  rw [hL, hR]
  conv_rhs => rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j]
  simp only [Finset.sum_add_distrib] at hswap ⊢
  rw [hswap]
  have : ∀ i j, (if i < j then 2 * f i j else 0) = (if i < j then f i j else 0) + (if i < j then f i j else 0) := by
    intro i j; split_ifs <;> ring
  simp only [this, Finset.sum_add_distrib]
  ring

/-- **Round trip form → Gram matrix → form is the identity:** `ofGram (gram Q) = Q`. Every
rational quadratic form is determined by its Gram matrix. -/
@[kb "cassels1978" "Ch. 2, §1"]
theorem ofGram_gram (Q : RatQF n) : ofGram Q.gram = Q := by
  apply QuadFormsKB.QuadForm.ext
  ext i j
  have hu := Q.upper
  simp only [ofGram, gram, QuadFormsKB.QuadForm.hessian, Matrix.of_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  split_ifs with h1 h2
  · subst h1; ring
  · have : Q.coeff j i = 0 := hu h2
    rw [this]; ring
  · have hji : j < i := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    exact (hu hji).symm

/-- **Round trip Gram matrix → form → Gram matrix is the identity** on symmetric matrices:
`gram (ofGram A) = A` when $A^{\mathsf T} = A$. -/
@[kb "cassels1978" "Ch. 2, §1"]
theorem gram_ofGram (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm) : (ofGram A).gram = A := by
  ext i j
  have hs : A j i = A i j := hA.apply i j
  simp only [gram, ofGram, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
  rcases lt_trichotomy i j with h | h | h
  · rw [ite_eq_right h.ne, ite_eq_left h, ite_eq_right h.ne', ite_eq_right (not_lt.mpr h.le)]; ring
  · subst h; simp; ring
  · rw [ite_eq_right h.ne', ite_eq_right (not_lt.mpr h.le), ite_eq_right h.ne, ite_eq_left h, hs]; ring

/-- **Two nondegeneracy tests agree over $\mathbb{Q}$:** $\det H \ne 0$ for the Hessian
$H = C + C^{\mathsf T}$ (`Nondegenerate`) iff $\det A \ne 0$ for the Gram matrix $A = \tfrac12 H$
(since $\det A = 2^{-n} \det H$). -/
@[kb "cassels1978" "Ch. 2, §1"]
theorem nondegenerate_iff_det_gram (Q : RatQF n) : Q.Nondegenerate ↔ Q.gram.det ≠ 0 := by
  unfold QuadFormsKB.QuadForm.Nondegenerate gram
  rw [Matrix.det_smul]
  constructor
  · intro h; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
  · intro h h'; apply h; rw [h', mul_zero]

end QuadFormsKB.RatQF
