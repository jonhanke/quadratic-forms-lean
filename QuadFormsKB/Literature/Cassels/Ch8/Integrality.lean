/-
# Cassels, Chapter 8, §1: classical versus integer-valued integrality

**Setting** (as in `Ch8/Bases.lean` and `Ch8/Primitive.lean`): a $\mathbb Q_p$-valued form
$f(\vec x) = \sum_{i,j} f_{ij}x_ix_j$ is given by a symmetric matrix $F = (f_{ij}) \in M_n(\mathbb Q_p)$, with value
`qf F x` $= \vec x^{t}F\vec x$. Indices are 0-based. Vectors of $\mathbb Z_p^n$ are the vectors of $\mathbb Q_p^n$
with all coordinates of norm $\le 1$ (`IsIntVec`).

**Defines** (p. 111) integer-valued forms (`IsIntegerValued`): $f(\vec a) \in \mathbb Z_p$ for all
$\vec a \in \mathbb Z_p^n$.

**Proves** (Cassels, p. 111: the classical definition ($f_{ij} \in \mathbb Z_p$, `IsClassIntegral`) and the
integer-valued one "make a difference only when $p = 2$")
* `isIntegerValued_of_isClassIntegral`: classically integral implies integer-valued, for every $p$;
* `isClassIntegral_iff_integerValued`: for $p \ne 2$ and $F$ symmetric the two notions agree
  (as $f_{ii} = f(e_i)$ and $2f_{ij} = f(e_i+e_j) - f(e_i) - f(e_j)$ with $\lvert 2\rvert_p = 1$);
* `not_isClassIntegral_two_example`: for $p = 2$, $x_0x_1$ (matrix with off-diagonal entries $1/2$) is integer-valued
  but not classically integral.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Primitive
import QuadFormsKB.Literature.Cassels.Ch8.Bases

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- A form $f$ with matrix $F \in M_n(\mathbb Q_p)$ is *integer-valued* (Cassels, Ch. 8, p. 111): $f(\vec a) \in
\mathbb Z_p$, i.e. $\lvert f(\vec a)\rvert_p \le 1$, for all $\vec a \in \mathbb Z_p^n$. -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (integer-valued form)"]
def IsIntegerValued (F : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop := ∀ x, IsIntVec x → ‖qf F x‖ ≤ 1

private theorem norm_mul_le_one_aux {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- A classically integral form is integer-valued (Cassels, Ch. 8, p. 111; every $p$). -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (classically integral implies integer-valued)"]
theorem isIntegerValued_of_isClassIntegral {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : IsClassIntegral F) :
    IsIntegerValued F := by
  intro x hx
  unfold qf dotProduct mulVec dotProduct
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  refine norm_mul_le_one_aux (hx i) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  exact norm_mul_le_one_aux (hF i j) (hx j)

private theorem qf_single (F : Matrix (Fin n) (Fin n) ℚ_[p]) (i : Fin n) :
    qf F (Pi.single i 1) = F i i := by
  simp [qf, dotProduct, mulVec, Pi.single_apply]

private theorem qf_add_single (F : Matrix (Fin n) (Fin n) ℚ_[p]) (i j : Fin n) (_hij : i ≠ j) :
    qf F (Pi.single i 1 + Pi.single j 1) = F i i + F j j + F i j + F j i := by
  simp [qf, dotProduct, mulVec, Pi.single_apply, Finset.sum_add_distrib, add_mul, mul_add]
  ring

private theorem isIntVec_single (i : Fin n) : IsIntVec (Pi.single i (1 : ℚ_[p])) := by
  intro k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

private theorem norm_add_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have h : ((2 : ℕ) : ℚ_[p]) = 2 := by norm_num
  rw [← h, Padic.norm_natCast_eq_one_iff]
  exact ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)).symm

/-- For $p \ne 2$ and $F$ symmetric, classically integral is equivalent to integer-valued
(Cassels, Ch. 8, p. 111). -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (integer-valued = classically integral for p ≠ 2)"]
theorem isClassIntegral_iff_integerValued (hp2 : p ≠ 2) {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hFs : Fᵀ = F) :
    IsClassIntegral F ↔ IsIntegerValued F := by
  refine ⟨isIntegerValued_of_isClassIntegral, fun h i j => ?_⟩
  have hd : ∀ k, ‖F k k‖ ≤ 1 := fun k => by
    have := h _ (isIntVec_single (p := p) k)
    rwa [qf_single] at this
  by_cases hij : i = j
  · subst hij; exact hd i
  · have hs : F j i = F i j := by
      simpa using congrFun (congrFun hFs i) j
    have hsum := h _ (show IsIntVec (Pi.single i (1 : ℚ_[p]) + Pi.single j 1) from fun k =>
      norm_add_le_one (isIntVec_single i k) (isIntVec_single j k))
    rw [qf_add_single F i j hij, hs] at hsum
    have e : (2 : ℚ_[p]) * F i j = (F i i + F j j + F i j + F i j) + (-F i i) + (-F j j) := by ring
    have h3 : ‖(2 : ℚ_[p]) * F i j‖ ≤ 1 := by
      rw [e]
      exact norm_add_le_one (norm_add_le_one hsum (by rw [norm_neg]; exact hd i)) (by rw [norm_neg]; exact hd j)
    rwa [norm_mul, norm_two_eq_one hp2, one_mul] at h3

/-- For $p = 2$ the two notions differ (Cassels, Ch. 8, p. 111): $x_0x_1$ with matrix
$\begin{pmatrix}0&1/2\\1/2&0\end{pmatrix}$ is integer-valued but not classically integral. -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (integer-valued but not classically integral, p = 2)"]
theorem not_isClassIntegral_two_example :
    IsIntegerValued (!![0, 1/2; 1/2, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) ∧
      ¬ IsClassIntegral (!![0, 1/2; 1/2, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  constructor
  · intro x hx
    have e : qf (!![0, 1/2; 1/2, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) x = x 0 * x 1 := by
      simp [qf, dotProduct, mulVec, Fin.sum_univ_two]
      ring
    rw [e]
    exact norm_mul_le_one_aux (hx 0) (hx 1)
  · intro h
    have h01 := h 0 1
    have h2 : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
      have : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_num
      rw [← this, Padic.norm_p]
      simp
    simp [h2] at h01
