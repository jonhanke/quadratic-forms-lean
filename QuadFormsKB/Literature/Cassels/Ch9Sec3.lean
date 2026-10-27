/-
# Cassels, Chapter 9, §3: small nonzero values of integral forms (Lemmas 3.1 and 3.2)

**Layer:** classically integral forms `f : QuadForm ℤ n` (`IsClassicallyIntegral`: $f = \sum f_{ij}x_ix_j$ with
$f_{ij} = f_{ji} \in \mathbb Z$), regular ($\det H \ne 0$); Cassels' determinant $d = d(f) = \det(f_{ij}) = \det H/2^n$
= `Siegel.gramDet f` (a real number); the real signature as an equivalence over $\mathbb R$ with a diagonal form
$\sum_i \varepsilon_ix_i^2$, $\varepsilon_i = \pm 1$, with $r$ entries $+1$ and $s$ entries $-1$ (Cassels' form
$x_1^2 + \dots + x_r^2 - x_{r+1}^2 - \dots - x_n^2$ (3.7) up to the order of the variables).

**Defines** `casselsDelta r s`, the constant $\delta(r, s)$ of Lemma 3.2, by the recursion of the proof:
$\delta(1, 0) = 1$, $\delta(r, s)^n = (4\delta(r-1, s)/3)^{n-1}$ for $r \ge 2$ (3.17), $\delta(1, s)^n = (4\delta(s, 0))^{n-1}$
for $s \ge 1$ (3.21), $n = r + s$. (The closed formula (3.10) is lost in the scan; for $s = 0$ the recursion gives
$\delta(r, 0) = (4/3)^{(r-1)/2}$, as in Corollary 1.)

**Proves**
* Lemma 3.2 (`exists_pos_value_le`): a regular classically integral form real-equivalent to $\sum\varepsilon_ix_i^2$
  with $r \ge 1$ plus signs takes a value $0 < f(\mathbf a) \le \delta(r, s)\lvert d\rvert^{1/n}$ at an integral vector;
* Lemma 3.1 (`exists_value_ne_zero_le`): for each $n \ge 1$ there is $C_n$ with $0 < \lvert f(\mathbf a)\rvert \le
  C_n\lvert d\rvert^{1/n}$ for some integral $\mathbf a$, for every regular classically integral $f$ in $n$ variables.

*Proof (Cassels'):* induction on $n$; $M$ the least positive value of $f$ on $\mathbb Z^n$, attained at a primitive vector;
change basis so that $f_{11} = M$, complete the square $Mf = (Mx_1 + \dots)^2 + g(x_2, \dots, x_n)$ with $g$ integral of
determinant $M^{n-2}d$ (3.11)–(3.12), apply the induction hypothesis to $g$ (real-equivalent to the signature
$(r - 1, s)$ by Witt cancellation over $\mathbb R$) or to $-g$ (signature $(s, 0)$ when $r = 1$), and choose $x_1$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Siegel.LocalProduct
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-- **Cassels' constant $\delta(r, s)$** (Ch. 9, Lemma 3.2, p. 136), by the recursion (3.17), (3.21) of the proof
(module docstring); $\delta(0, s) = 1$ is a junk value (never used). -/
@[kb "cassels1978" "Ch. 9, Lemma 3.2, (3.10), (3.17), (3.21), pp. 136–137 (the constant δ(r, s))"]
def casselsDelta : ℕ → ℕ → ℝ
  | 0, _ => 1
  | 1, 0 => 1
  | 1, s + 1 => (4 * casselsDelta (s + 1) 0) ^ ((s + 1 : ℝ) / (s + 2))
  | r + 2, s => (4 / 3 * casselsDelta (r + 1) s) ^ ((r + s + 1 : ℝ) / (r + s + 2))
termination_by r s => r + s

namespace Ch9Sec3

/-- $\delta(r, s) \ge 0$ (all values are real powers of nonnegative numbers). -/
theorem casselsDelta_nonneg : ∀ r s : ℕ, 0 ≤ casselsDelta r s
  | 0, _ => by rw [casselsDelta]; norm_num
  | 1, 0 => by rw [casselsDelta]; norm_num
  | 1, s + 1 => by
    rw [casselsDelta]
    have := casselsDelta_nonneg (s + 1) 0
    exact Real.rpow_nonneg (by positivity) _
  | r + 2, s => by
    rw [casselsDelta]
    have := casselsDelta_nonneg (r + 1) s
    exact Real.rpow_nonneg (by positivity) _
termination_by r s => r + s

/-- Real-power arithmetic: from $M^2 \le KY$ and $Y^m = M^{m-1}D$ deduce $M \le K^{m/(m+1)}D^{1/(m+1)}$. -/
theorem bound_of_sq_le {M K Y D : ℝ} {m : ℕ} (hm : 1 ≤ m) (hM : 0 < M) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hYm : Y ^ m = M ^ (m - 1) * D) (h : M ^ 2 ≤ K * Y) :
    M ≤ K ^ ((m : ℝ) / (m + 1)) * D ^ ((1 : ℝ) / (m + 1)) := by
  have hK : 0 ≤ K := by
    by_contra hneg
    rw [not_le] at hneg
    have : K * Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hY
    nlinarith [sq_pos_of_pos hM]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : (M ^ 2) ^ (k + 1) ≤ (K * Y) ^ (k + 1) := pow_le_pow_left₀ (by positivity) h _
  rw [mul_pow, hYm, Nat.add_sub_cancel] at h1
  have h2 : M ^ (k + 2) * M ^ k ≤ (K ^ (k + 1) * D) * M ^ k := by
    calc M ^ (k + 2) * M ^ k = (M ^ 2) ^ (k + 1) := by ring
      _ ≤ K ^ (k + 1) * (M ^ k * D) := h1
      _ = (K ^ (k + 1) * D) * M ^ k := by ring
  have h3 : M ^ (k + 2) ≤ K ^ (k + 1) * D := le_of_mul_le_mul_right h2 (pow_pos hM k)
  have e1 : M = (M ^ (k + 2)) ^ ((1 : ℝ) / ((k : ℝ) + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    push_cast
    rw [mul_one_div_cancel (by positivity), Real.rpow_one]
  calc M = (M ^ (k + 2)) ^ ((1 : ℝ) / ((k : ℝ) + 2)) := e1
    _ ≤ (K ^ (k + 1) * D) ^ ((1 : ℝ) / ((k : ℝ) + 2)) :=
        Real.rpow_le_rpow (by positivity) h3 (by positivity)
    _ = K ^ (((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) * D ^ ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) := by
        rw [Real.mul_rpow (by positivity) hD, ← Real.rpow_natCast K (k + 1), ← Real.rpow_mul hK]
        push_cast
        ring_nf

section Blocks

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The tail $(F_{0,1}, \dots, F_{0,m})$ of the first row of a matrix. -/
def rowTail (F : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : Fin m → R := fun j => F 0 j.succ

/-- The completed-square matrix $G = F_{00}F' - bb^{\mathsf T}$ ($F'$ the lower right block, $b$ = `rowTail F`). -/
def schur (F : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : Matrix (Fin m) (Fin m) R :=
  F 0 0 • F.submatrix Fin.succ Fin.succ - Matrix.vecMulVec (rowTail F) (rowTail F)

/-- Expansion of $x^{\mathsf T}Fx$ along the first coordinate. -/
theorem dot_expand (F : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (hF : F.IsSymm) (x : Fin (m + 1) → R) :
    x ⬝ᵥ F *ᵥ x = F 0 0 * x 0 ^ 2 + 2 * x 0 * (rowTail F ⬝ᵥ Fin.tail x) +
      Fin.tail x ⬝ᵥ (F.submatrix Fin.succ Fin.succ *ᵥ Fin.tail x) := by
  have hs : ∀ i : Fin m, F i.succ 0 = F 0 i.succ := fun i => by
    have := congrFun (congrFun hF 0) i.succ
    simpa [Matrix.transpose_apply] using this
  have h1 : x ⬝ᵥ F *ᵥ x = x 0 * (F 0 0 * x 0 + ∑ j : Fin m, F 0 j.succ * x j.succ) +
      ∑ i : Fin m, x i.succ * (F i.succ 0 * x 0 + ∑ j : Fin m, F i.succ j.succ * x j.succ) := by
    simp only [dotProduct, mulVec, Fin.sum_univ_succ]
  rw [h1]
  simp only [hs, rowTail, dotProduct, mulVec, Fin.tail, Matrix.submatrix_apply, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  have h2 : ∑ i : Fin m, x i.succ * (F 0 i.succ * x 0) = ∑ i : Fin m, x 0 * (F 0 i.succ * x i.succ) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  have h4 : ∑ i : Fin m, 2 * x 0 * (F 0 i.succ * x i.succ) =
      ∑ i : Fin m, x 0 * (F 0 i.succ * x i.succ) + ∑ i : Fin m, x 0 * (F 0 i.succ * x i.succ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4]
  ring

/-- **Completing the square:** $F_{00}\,(x^{\mathsf T}Fx) = (F_{00}x_0 + b\cdot x')^2 + x'^{\mathsf T}Gx'$. -/
theorem schur_identity (F : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (hF : F.IsSymm) (x : Fin (m + 1) → R) :
    F 0 0 * (x ⬝ᵥ F *ᵥ x) = (F 0 0 * x 0 + rowTail F ⬝ᵥ Fin.tail x) ^ 2 +
      Fin.tail x ⬝ᵥ (schur F *ᵥ Fin.tail x) := by
  have e2 : Fin.tail x ⬝ᵥ (schur F *ᵥ Fin.tail x) =
      F 0 0 * (Fin.tail x ⬝ᵥ (F.submatrix Fin.succ Fin.succ *ᵥ Fin.tail x)) - (rowTail F ⬝ᵥ Fin.tail x) ^ 2 := by
    have h3 : Fin.tail x ⬝ᵥ (Matrix.vecMulVec (rowTail F) (rowTail F) *ᵥ Fin.tail x) =
        (rowTail F ⬝ᵥ Fin.tail x) ^ 2 := by
      simp only [dotProduct, mulVec, Matrix.vecMulVec_apply, Finset.mul_sum, sq, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [schur, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, h3]
  rw [dot_expand F hF x, e2]
  ring

end Blocks

section Cong

variable {k : ℕ}

/-- **Real congruence** of matrices (as quadratic forms): $x \mapsto x^{\mathsf T}Bx$ is $x \mapsto (Px)^{\mathsf T}A(Px)$ for an
invertible real $P$. -/
def Cong (A B : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∃ P : Matrix (Fin k) (Fin k) ℝ, IsUnit P.det ∧ ∀ x, (P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ x)) = x ⬝ᵥ (B *ᵥ x)

/-- Congruence is reflexive: $A$ is congruent to itself via the identity matrix. -/
theorem Cong.refl (A : Matrix (Fin k) (Fin k) ℝ) : Cong A A := ⟨1, by simp, fun x => by simp⟩

/-- Congruence is transitive: composing the two invertible changes of variables gives one from $A$ to $C$. -/
theorem Cong.trans {A B C : Matrix (Fin k) (Fin k) ℝ} (h1 : Cong A B) (h2 : Cong B C) : Cong A C := by
  obtain ⟨P, hP, h⟩ := h1
  obtain ⟨Q, hQ, h'⟩ := h2
  refine ⟨P * Q, by rw [det_mul]; exact hP.mul hQ, fun x => ?_⟩
  rw [← mulVec_mulVec, h, h']

/-- Congruence is symmetric: the inverse change of variables goes the other way. -/
theorem Cong.symm {A B : Matrix (Fin k) (Fin k) ℝ} (h1 : Cong A B) : Cong B A := by
  obtain ⟨P, hP, h⟩ := h1
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det P hP, fun x => ?_⟩
  have := h (P⁻¹ *ᵥ x)
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv P hP, one_mulVec] at this
  exact this.symm

/-- Congruence is preserved by negating both matrices. -/
theorem Cong.neg {A B : Matrix (Fin k) (Fin k) ℝ} (h1 : Cong A B) : Cong (-A) (-B) := by
  obtain ⟨P, hP, h⟩ := h1
  refine ⟨P, hP, fun x => ?_⟩
  simp only [neg_mulVec, dotProduct_neg, h]

/-- Scaling by a positive number is a congruence. -/
theorem cong_smul_pos {c : ℝ} (hc : 0 < c) (A : Matrix (Fin k) (Fin k) ℝ) : Cong (c • A) A := by
  refine ⟨(Real.sqrt c)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ), ?_, fun x => ?_⟩
  · rw [Matrix.det_smul]
    have : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
    simp [this]
  · have h : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
    have h0 : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
    simp only [smul_mulVec, one_mulVec, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
    rw [h]

end Cong

section Cons

variable {m : ℕ}

/-- The block-diagonal matrix $\operatorname{diag}(a) \oplus A$ on $\mathrm{Fin}(m+1)$. -/
def consForm (a : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (Fin.cases a (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

/-- For $y \in \mathbb R^{m+1}$, $y^{\mathsf T}(\operatorname{diag}(a) \oplus A)y = a\,y_0^2 + y'^{\mathsf T}Ay'$ with $y' = (y_1, \dots, y_m)$. -/
theorem dot_consForm (a : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (y : Fin (m + 1) → ℝ) :
    y ⬝ᵥ consForm a A *ᵥ y = a * y 0 ^ 2 + Fin.tail y ⬝ᵥ (A *ᵥ Fin.tail y) := by
  simp only [dotProduct, mulVec, consForm, Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ,
    Fin.tail, Finset.sum_const_zero, add_zero, zero_add, zero_mul]
  ring

/-- $\det(\operatorname{diag}(a) \oplus A) = a\det A$. -/
theorem det_consForm (a : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : (consForm a A).det = a * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h0 : ∀ j : Fin m, consForm a A 0 j.succ = 0 := fun j => by simp [consForm]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero]
  have : (consForm a A).submatrix Fin.succ Fin.succ = A := by
    ext i j; simp [consForm]
  rw [this]
  simp [consForm]

/-- The substitution matrix $E$ with $(Ex)_0 = Mx_0 + b\cdot x'$ and $x' \mapsto x'$. -/
def subMat (M : ℝ) (b : Fin m → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (Fin.cases M (fun j' => b j') j)
    (fun i' => Fin.cases 0 (fun j' => if i' = j' then 1 else 0) j) i

/-- The substitution matrix sends $x$ to $(Mx_0 + b\cdot x',\ x_1, \dots, x_m)$ with $x' = (x_1, \dots, x_m)$. -/
theorem subMat_mulVec (M : ℝ) (b : Fin m → ℝ) (x : Fin (m + 1) → ℝ) :
    subMat M b *ᵥ x = Fin.cons (M * x 0 + b ⬝ᵥ Fin.tail x) (Fin.tail x) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [subMat, mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]
  · simp [subMat, mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]

/-- The substitution matrix $E$ built from $M$ and $b$ has determinant $\det E = M$. -/
theorem det_subMat (M : ℝ) (b : Fin m → ℝ) : (subMat M b).det = M := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ j : Fin m, subMat M b j.succ 0 = 0 := fun j => by simp [subMat]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero]
  have : (subMat M b).submatrix Fin.succ Fin.succ = 1 := by
    ext i j; simp [subMat, Matrix.one_apply]
  rw [this]
  simp [subMat]

end Cons

section Polar

/-- **Polarization:** symmetric matrices with the same quadratic form are equal. -/
theorem eq_of_dot_eq {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {k : ℕ}
    {A B : Matrix (Fin k) (Fin k) R} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x : Fin k → R, x ⬝ᵥ A *ᵥ x = x ⬝ᵥ B *ᵥ x) : A = B := by
  have h1 : ∀ (M : Matrix (Fin k) (Fin k) R) (i : Fin k),
      (Pi.single i 1 : Fin k → R) ⬝ᵥ M *ᵥ (Pi.single i 1) = M i i := by
    intro M i
    simp [mulVec_single, single_dotProduct]
  have h2 : ∀ (M : Matrix (Fin k) (Fin k) R) (i j : Fin k), M.IsSymm →
      (Pi.single i 1 + Pi.single j 1 : Fin k → R) ⬝ᵥ M *ᵥ (Pi.single i 1 + Pi.single j 1)
        = M i i + 2 * M i j + M j j := by
    intro M i j hM
    have hs : M j i = M i j := by
      have := congrFun (congrFun hM i) j
      simpa [Matrix.transpose_apply] using this
    simp [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single, single_dotProduct, hs]
    ring
  ext i j
  have e1 := h (Pi.single i 1)
  have e2 := h (Pi.single j 1)
  have e3 := h (Pi.single i 1 + Pi.single j 1)
  rw [h1, h1] at e1 e2
  rw [h2 _ _ _ hA, h2 _ _ _ hB] at e3
  have : (2 : R) * A i j = 2 * B i j := by linear_combination e3 - e1 - e2
  exact mul_left_cancel₀ two_ne_zero this

end Polar

section Cons2

variable {m : ℕ}

/-- If $A$ is symmetric then so is $\operatorname{diag}(a) \oplus A$. -/
theorem consForm_isSymm (a : ℝ) {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) : (consForm a A).IsSymm := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [consForm]
  · simp [consForm]
  · simp [consForm]
  · have := congrFun (congrFun hA i') j'
    simpa [consForm, Matrix.transpose_apply] using this

/-- The completed-square matrix $G$ of a symmetric matrix is symmetric. -/
theorem schur_isSymm {R : Type*} [CommRing R] {F : Matrix (Fin (m + 1)) (Fin (m + 1)) R} (hF : F.IsSymm) :
    (schur F).IsSymm := by
  ext i j
  have := congrFun (congrFun hF i.succ) j.succ
  simp only [Matrix.transpose_apply] at this ⊢
  simp [schur, Matrix.vecMulVec_apply, this, mul_comm]

/-- Values of $1 \oplus G$ on $Ex$ equal those of $F_{00}F$. -/
theorem val_cons_schur {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hF : F.IsSymm) (x : Fin (m + 1) → ℝ) :
    (subMat (F 0 0) (rowTail F) *ᵥ x) ⬝ᵥ (consForm 1 (schur F) *ᵥ (subMat (F 0 0) (rowTail F) *ᵥ x)) =
      x ⬝ᵥ ((F 0 0 • F) *ᵥ x) := by
  rw [dot_consForm, subMat_mulVec, Fin.tail_cons, Fin.cons_zero, smul_mulVec, dotProduct_smul, smul_eq_mul,
    schur_identity F hF x]
  ring

/-- The completed square as a congruence: $1 \oplus G \sim F_{00}F$. -/
theorem cong_cons_schur {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hF : F.IsSymm) (hM : F 0 0 ≠ 0) :
    Cong (consForm 1 (schur F)) (F 0 0 • F) :=
  ⟨subMat (F 0 0) (rowTail F), by rw [det_subMat]; exact IsUnit.mk0 _ hM, val_cons_schur hF⟩

/-- **Determinant of the completed square:** $F_{00}^2\det G = F_{00}^{m+1}\det F$. -/
theorem det_schur {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hF : F.IsSymm) (_hM : F 0 0 ≠ 0) :
    F 0 0 ^ 2 * (schur F).det = F 0 0 ^ (m + 1) * F.det := by
  set E := subMat (F 0 0) (rowTail F) with hE
  have hsym : ((E)ᵀ * consForm 1 (schur F) * E).IsSymm := by
    have := consForm_isSymm 1 (schur_isSymm hF)
    rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, this.eq, Matrix.mul_assoc]
  have hB : (F 0 0 • F).IsSymm := by rw [Matrix.IsSymm, transpose_smul, hF.eq]
  have hmat : Eᵀ * consForm 1 (schur F) * E = F 0 0 • F := by
    refine eq_of_dot_eq hsym hB fun x => ?_
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
      ← val_cons_schur hF x]
  have := congrArg Matrix.det hmat
  rw [det_mul, det_mul, det_transpose, det_consForm, det_subMat, det_smul, Fintype.card_fin] at this
  linear_combination this

end Cons2

section Witt

variable {m : ℕ}

/-- The real quadratic form $x \mapsto x^{\mathsf T}Ax$ as a `QuadForm` (upper triangular coefficients). -/
def symmForm (A : Matrix (Fin m) (Fin m) ℝ) : QuadForm ℝ m :=
  QuadForm.ofUpper fun i j => if i = j then A i i else 2 * A i j

/-- For symmetric $A$, the Hessian of the real quadratic form $x \mapsto x^{\mathsf T}Ax$ is $2A$. -/
theorem symmForm_hessian {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    (symmForm A).hessian = (2 : ℝ) • A := by
  ext i j
  have hs : A j i = A i j := by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply] using this
  rcases lt_trichotomy i j with h | h | h
  · simp [QuadForm.hessian, symmForm, QuadForm.ofUpper, h.ne, h.le, not_le.mpr h]
  · subst h; simp [QuadForm.hessian, symmForm, QuadForm.ofUpper]; ring
  · simp [QuadForm.hessian, symmForm, QuadForm.ofUpper, h.ne, h.le, not_le.mpr h, hs]

/-- For symmetric $A$, the form `symmForm A` takes the value $x^{\mathsf T}Ax$ at $x$. -/
theorem symmForm_eval {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (x : Fin m → ℝ) :
    (symmForm A).evalIn ℝ x = x ⬝ᵥ A *ᵥ x := by
  have h := QuadForm.polar_eq_hessian ℝ (symmForm A) x x
  rw [← two_smul ℝ x, QuadForm.evalIn_smul, symmForm_hessian hA] at h
  simp only [Algebra.algebraMap_self] at h
  rw [show ((2 : ℝ) • A).map ⇑(RingHom.id ℝ) = (2 : ℝ) • A from rfl] at h
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  nlinarith [h]

/-- The reindexing $\mathrm{Fin}(1+m) \simeq \mathrm{Fin}(m+1)$. -/
def finE (m : ℕ) : Fin (1 + m) ≃ Fin (m + 1) := finCongr (Nat.add_comm 1 m)

/-- The inverse reindexing sends the index $0$ to the index $0$ of the first summand. -/
theorem finE_symm_zero (m : ℕ) : (finE m).symm 0 = Fin.castAdd m (0 : Fin 1) :=
  Fin.ext (by simp [finE])

/-- The inverse reindexing sends the index $j+1$ to the index $j$ of the second summand. -/
theorem finE_symm_succ (m : ℕ) (j : Fin m) : (finE m).symm j.succ = Fin.natAdd 1 j :=
  Fin.ext (by simp [finE]; omega)

/-- The orthogonal sum of $\langle 1\rangle$ and `symmForm A` is evaluated by $\operatorname{diag}(1) \oplus A$ after reindexing $\mathrm{Fin}(1+m)$ to $\mathrm{Fin}(m+1)$. -/
theorem orth_eval {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (z : Fin (1 + m) → ℝ) :
    (QuadForm.orthSum (QuadForm.diag (fun _ : Fin 1 => (1 : ℝ))) (symmForm A)).evalIn ℝ z =
      (z ∘ (finE m).symm) ⬝ᵥ consForm 1 A *ᵥ (z ∘ (finE m).symm) := by
  rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_diag, symmForm_eval hA, dot_consForm]
  simp only [Fin.sum_univ_one, Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply, finE_symm_zero]
  have ht : (fun b => z (Fin.natAdd 1 b)) = Fin.tail (z ∘ (finE m).symm) := by
    funext j; simp [Fin.tail, finE_symm_succ]
  rw [ht]

/-- **Witt cancellation of $\langle 1\rangle$** for real symmetric matrices. -/
theorem witt_cons {G B : Matrix (Fin m) (Fin m) ℝ} (hG : G.IsSymm) (hB : B.IsSymm) (hdet : G.det ≠ 0)
    (h : Cong (consForm 1 G) (consForm 1 B)) : Cong G B := by
  obtain ⟨P, hP, hPv⟩ := h
  have h1 : (QuadForm.orthSum (QuadForm.diag (fun _ : Fin 1 => (1 : ℝ))) (symmForm G)).IsometricIn ℝ
      (QuadForm.orthSum (QuadForm.diag (fun _ : Fin 1 => (1 : ℝ))) (symmForm B)) := by
    refine ⟨P.submatrix (finE m) (finE m), ?_, fun x => ?_⟩
    · rw [Matrix.det_submatrix_equiv_self]; exact hP
    · rw [orth_eval hG, orth_eval hB, Matrix.submatrix_mulVec_equiv]
      have : ((P *ᵥ (x ∘ (finE m).symm)) ∘ (finE m)) ∘ (finE m).symm = P *ᵥ (x ∘ (finE m).symm) := by
        funext i; simp
      rw [this, hPv]
  have hQ : (QuadForm.diag (fun _ : Fin 1 => (1 : ℝ))).Nondegenerate := by
    simp [QuadForm.Nondegenerate, QuadForm.hessian, QuadForm.diag, Matrix.det_unique]
  have hQ1 : (symmForm G).Nondegenerate := by
    rw [QuadForm.Nondegenerate, symmForm_hessian hG, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hdet
  obtain ⟨P₁, hP₁, h2⟩ := QuadForm.isometricIn_of_orthSum ℝ hQ hQ1 h1
  exact ⟨P₁, hP₁, fun x => by rw [← symmForm_eval hG, ← symmForm_eval hB, h2]⟩

end Witt

section Canon

/-- The canonical signature vector: $r$ entries $+1$ followed by entries $-1$. -/
def canonEps (r : ℕ) {k : ℕ} (i : Fin k) : ℝ := if i.val < r then 1 else -1

/-- For a diagonal matrix, $y^{\mathsf T}\operatorname{diag}(v)\,y = \sum_i v_iy_i^2$. -/
theorem dot_diagonal {k : ℕ} (v : Fin k → ℝ) (y : Fin k → ℝ) :
    y ⬝ᵥ diagonal v *ᵥ y = ∑ i, v i * y i ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A $\pm1$ vector with $r$ entries $+1$ is a permutation of `canonEps r`. -/
theorem exists_perm_canon {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (r : ℕ)
    (hr : (Finset.univ.filter fun i => ε i = 1).card = r) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, ε i = canonEps r (σ i) := by
  classical
  have hrn : r ≤ n := by
    rw [← hr]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hq : (Finset.univ.filter fun i : Fin n => i.val < r).card = r := by
    have := Fin.card_filter_val_lt (n := n) (m := r)
    rw [min_eq_right hrn] at this
    exact this
  have c1 : Fintype.card {i // ε i = 1} = Fintype.card {i : Fin n // i.val < r} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hr, hq]
  have c2 : Fintype.card {i // ¬ ε i = 1} = Fintype.card {i : Fin n // ¬ i.val < r} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e1 := Fintype.equivOfCardEq c1
  let e2 := Fintype.equivOfCardEq c2
  refine ⟨(Equiv.sumCompl (fun i => ε i = 1)).symm.trans ((e1.sumCongr e2).trans
    (Equiv.sumCompl (fun i : Fin n => i.val < r))), fun i => ?_⟩
  by_cases h : ε i = 1
  · simp only [Equiv.trans_apply]
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun i => ε i = 1) h]
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    have := (e1 ⟨i, h⟩).2
    simp [canonEps, this, h]
  · simp only [Equiv.trans_apply]
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun i => ε i = 1) h]
    simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    have := (e2 ⟨i, h⟩).2
    rcases hε i with h1 | h1
    · exact absurd h1 h
    · simp [canonEps, this, h1]

/-- A diagonal matrix with entries $\pm1$, exactly $r$ of them $+1$, is congruent to the canonical signature matrix with $r$ entries $+1$ followed by entries $-1$. -/
theorem cong_diag_canon {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (r : ℕ)
    (hr : (Finset.univ.filter fun i => ε i = 1).card = r) :
    Cong (diagonal ε) (diagonal (canonEps r : Fin n → ℝ)) := by
  obtain ⟨σ, hσ⟩ := exists_perm_canon ε hε r hr
  refine ⟨(1 : Matrix (Fin n) (Fin n) ℝ).submatrix σ id, ?_, fun x => ?_⟩
  · rw [Matrix.det_permute]; simp
  · have hx : ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix σ id) *ᵥ x = x ∘ σ := by
      rw [show ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix σ id) = (1 : Matrix (Fin n) (Fin n) ℝ).submatrix σ
        (Equiv.refl _) from rfl, Matrix.submatrix_mulVec_equiv]
      simp
    rw [hx, dot_diagonal, dot_diagonal]
    exact Equiv.sum_comp σ (fun j => canonEps r j * x j ^ 2) ▸
      Finset.sum_congr rfl fun i _ => by simp [hσ i]

end Canon

section Round

/-- One can choose $b_0$ with $|Mb_0 + \beta| \le M/2$. -/
theorem exists_round_half (M β : ℤ) (hM : 0 < M) : ∃ b0 : ℤ, 2 * |M * b0 + β| ≤ M := by
  have h := Int.mul_ediv_add_emod (β + M / 2) M
  have h0 := Int.emod_nonneg (β + M / 2) hM.ne'
  have h1 := Int.emod_lt_of_pos (β + M / 2) hM
  refine ⟨-((β + M / 2) / M), ?_⟩
  have e : M * -((β + M / 2) / M) + β = (β + M / 2) % M - M / 2 := by
    have : M * -((β + M / 2) / M) = -(M * ((β + M / 2) / M)) := by ring
    rw [this]; omega
  rw [e]
  rcases abs_cases ((β + M / 2) % M - M / 2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> rw [h2] <;> omega

/-- One can choose $b_0$ with $M/2 \le |Mb_0 + \beta| \le M$. -/
theorem exists_round_big (M β : ℤ) (hM : 0 < M) : ∃ b0 : ℤ, M ≤ 2 * |M * b0 + β| ∧ |M * b0 + β| ≤ M := by
  have h := Int.mul_ediv_add_emod β M
  have h0 := Int.emod_nonneg β hM.ne'
  have h1 := Int.emod_lt_of_pos β hM
  by_cases hc : M ≤ 2 * (β % M)
  · refine ⟨-(β / M), ?_⟩
    have e : M * -(β / M) + β = β % M := by
      have : M * -(β / M) = -(M * (β / M)) := by ring
      rw [this]; omega
    rw [e, abs_of_nonneg h0]
    omega
  · refine ⟨-(β / M) - 1, ?_⟩
    have e : M * (-(β / M) - 1) + β = β % M - M := by
      have : M * (-(β / M) - 1) = -(M * (β / M)) - M := by ring
      rw [this]; omega
    rw [e, abs_of_nonpos (by omega)]
    omega

end Round

section IntStep

variable {m : ℕ}

/-- The real matrix of an integer matrix. -/
abbrev cM {k : ℕ} (F : Matrix (Fin k) (Fin k) ℤ) : Matrix (Fin k) (Fin k) ℝ := F.map (Int.castRingHom ℝ)

/-- The determinant of the real matrix of an integer matrix $F$ is the integer $\det F$ cast to $\mathbb R$. -/
theorem cM_det {k : ℕ} (F : Matrix (Fin k) (Fin k) ℤ) : (cM F).det = ((F.det : ℤ) : ℝ) := by
  have := RingHom.map_det (Int.castRingHom ℝ) F
  simpa [cM] using this.symm

/-- The integer value $a^{\mathsf T}Fa$ cast to $\mathbb R$ equals the value of the real matrix of $F$ at the cast vector. -/
theorem cast_dot {k : ℕ} (F : Matrix (Fin k) (Fin k) ℤ) (a : Fin k → ℤ) :
    ((a ⬝ᵥ F *ᵥ a : ℤ) : ℝ) = (fun i => (a i : ℝ)) ⬝ᵥ (cM F *ᵥ fun i => (a i : ℝ)) := by
  simp [dotProduct, mulVec, cM]

/-- The real matrix of a symmetric integer matrix is symmetric. -/
theorem cM_isSymm {k : ℕ} {F : Matrix (Fin k) (Fin k) ℤ} (hF : F.IsSymm) : (cM F).IsSymm := by
  ext i j
  have := congrFun (congrFun hF i) j
  simp only [Matrix.transpose_apply] at this ⊢
  simp [cM, this]

/-- The real matrix of the completed-square matrix of $F$ is the completed-square matrix of the real matrix of $F$. -/
theorem cM_schur (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : cM (schur F) = schur (cM F) := by
  ext i j
  simp only [cM, schur, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, Matrix.vecMulVec_apply, rowTail, map_sub, map_mul]

/-- $|\det G| = F_{00}^{m-1}|\det F|$ for the completed square (integer form). -/
theorem abs_det_schur (hm : 1 ≤ m) {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) (hM : 0 < F 0 0) :
    |(((schur F).det : ℤ) : ℝ)| = ((F 0 0 : ℤ) : ℝ) ^ (m - 1) * |((F.det : ℤ) : ℝ)| := by
  have hM' : (0 : ℝ) < ((F 0 0 : ℤ) : ℝ) := by exact_mod_cast hM
  have h := det_schur (cM_isSymm hF) (by simpa [cM] using hM'.ne')
  rw [← cM_schur, cM_det, cM_det] at h
  simp only [cM, Matrix.map_apply, Int.coe_castRingHom] at h
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h2 : (((schur F).det : ℤ) : ℝ) = ((F 0 0 : ℤ) : ℝ) ^ k * ((F.det : ℤ) : ℝ) := by
    have : ((F 0 0 : ℤ) : ℝ) ^ 2 * (((schur F).det : ℤ) : ℝ) = ((F 0 0 : ℤ) : ℝ) ^ 2 * (((F 0 0 : ℤ) : ℝ) ^ k * ((F.det : ℤ) : ℝ)) := by
      rw [h]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hM'.ne') this
  rw [h2, abs_mul, abs_of_pos (pow_pos hM' k)]
  simp

end IntStep

section Steps

variable {m : ℕ}

/-- For $a \ge 0$ and $m \ge 1$, $(a^{1/m})^m = a$. -/
theorem rpow_pow_inv (hm : 1 ≤ m) (a : ℝ) (ha : 0 ≤ a) : (a ^ ((1 : ℝ) / m)) ^ m = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha, one_div_mul_cancel (by positivity), Real.rpow_one]

/-- Value of the vector $(b_0, b')$ in terms of the completed square. -/
theorem value_cons {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) (b0 : ℤ) (b' : Fin m → ℤ) :
    F 0 0 * ((Fin.cons b0 b' : Fin (m + 1) → ℤ) ⬝ᵥ F *ᵥ (Fin.cons b0 b' : Fin (m + 1) → ℤ)) =
      (F 0 0 * b0 + rowTail F ⬝ᵥ b') ^ 2 + b' ⬝ᵥ (schur F *ᵥ b') := by
  have := schur_identity F hF (Fin.cons b0 b' : Fin (m + 1) → ℤ)
  simpa only [Fin.tail_cons, Fin.cons_zero] using this

/-- **Case $r \ge 2$ of Lemma 3.2:** the bound for the minimum $M = F_{00}$ from a small positive value of $G$. -/
theorem step_pos (hm : 1 ≤ m) {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) (hM : 0 < F 0 0)
    (hmin : ∀ x : Fin (m + 1) → ℤ, 0 < x ⬝ᵥ F *ᵥ x → F 0 0 ≤ x ⬝ᵥ F *ᵥ x) {δ : ℝ}
    (hG : ∃ b' : Fin m → ℤ, 0 < b' ⬝ᵥ (schur F *ᵥ b') ∧
      ((b' ⬝ᵥ (schur F *ᵥ b') : ℤ) : ℝ) ≤ δ * |(((schur F).det : ℤ) : ℝ)| ^ ((1 : ℝ) / m)) :
    ((F 0 0 : ℤ) : ℝ) ≤ (4 / 3 * δ) ^ ((m : ℝ) / (m + 1)) * |((F.det : ℤ) : ℝ)| ^ ((1 : ℝ) / (m + 1)) := by
  obtain ⟨b', hg0, hg⟩ := hG
  obtain ⟨b0, hb0⟩ := exists_round_half (F 0 0) (rowTail F ⬝ᵥ b') hM
  have hid := value_cons hF b0 b'
  have hmin' := hmin (Fin.cons b0 b')
  generalize (Fin.cons b0 b' : Fin (m + 1) → ℤ) ⬝ᵥ F *ᵥ (Fin.cons b0 b' : Fin (m + 1) → ℤ) = v at hid hmin'
  have hYm : (|(((schur F).det : ℤ) : ℝ)| ^ ((1 : ℝ) / m)) ^ m =
      ((F 0 0 : ℤ) : ℝ) ^ (m - 1) * |((F.det : ℤ) : ℝ)| := by
    rw [rpow_pow_inv hm _ (abs_nonneg _)]; exact abs_det_schur hm hF hM
  have hY : 0 ≤ |(((schur F).det : ℤ) : ℝ)| ^ ((1 : ℝ) / m) := Real.rpow_nonneg (abs_nonneg _) _
  generalize hg' : b' ⬝ᵥ (schur F *ᵥ b') = g at hid hg0 hg
  generalize ht : F 0 0 * b0 + rowTail F ⬝ᵥ b' = t at hid hb0
  have hsq : (2 * |t|) ^ 2 ≤ F 0 0 ^ 2 := pow_le_pow_left₀ (by positivity) hb0 2
  have hsq2 : 4 * t ^ 2 ≤ F 0 0 ^ 2 := by nlinarith [sq_abs t]
  have hv : 0 < v := by
    by_contra hv
    push Not at hv
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hM.le hv, sq_nonneg t]
  have hvM := hmin' hv
  have h3 : 3 * F 0 0 ^ 2 ≤ 4 * g := by nlinarith [mul_le_mul_of_nonneg_left hvM hM.le]
  have h3r : 3 * ((F 0 0 : ℤ) : ℝ) ^ 2 ≤ 4 * (g : ℝ) := by exact_mod_cast h3
  have hMr : (0 : ℝ) < ((F 0 0 : ℤ) : ℝ) := by exact_mod_cast hM
  refine bound_of_sq_le hm hMr hY (abs_nonneg _) hYm ?_
  nlinarith [h3r, hg]

/-- **Case $r = 1$ of Lemma 3.2:** the bound for the minimum $M = F_{00}$ from a small positive value of $-G$. -/
theorem step_one (hm : 1 ≤ m) {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) (hM : 0 < F 0 0)
    (hmin : ∀ x : Fin (m + 1) → ℤ, 0 < x ⬝ᵥ F *ᵥ x → F 0 0 ≤ x ⬝ᵥ F *ᵥ x) {δ : ℝ}
    (hG : ∃ b' : Fin m → ℤ, 0 < b' ⬝ᵥ ((-schur F) *ᵥ b') ∧
      ((b' ⬝ᵥ ((-schur F) *ᵥ b') : ℤ) : ℝ) ≤ δ * |(((-schur F).det : ℤ) : ℝ)| ^ ((1 : ℝ) / m)) :
    ((F 0 0 : ℤ) : ℝ) ≤ (4 * δ) ^ ((m : ℝ) / (m + 1)) * |((F.det : ℤ) : ℝ)| ^ ((1 : ℝ) / (m + 1)) := by
  obtain ⟨b', hg0, hg⟩ := hG
  obtain ⟨b0, hb1, hb2⟩ := exists_round_big (F 0 0) (rowTail F ⬝ᵥ b') hM
  have hid := value_cons hF b0 b'
  have hmin' := hmin (Fin.cons b0 b')
  generalize (Fin.cons b0 b' : Fin (m + 1) → ℤ) ⬝ᵥ F *ᵥ (Fin.cons b0 b' : Fin (m + 1) → ℤ) = v at hid hmin'
  have hdn : |(((-schur F).det : ℤ) : ℝ)| = |(((schur F).det : ℤ) : ℝ)| := by
    rw [Matrix.det_neg]; push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [hdn] at hg
  have hYm : (|(((schur F).det : ℤ) : ℝ)| ^ ((1 : ℝ) / m)) ^ m =
      ((F 0 0 : ℤ) : ℝ) ^ (m - 1) * |((F.det : ℤ) : ℝ)| := by
    rw [rpow_pow_inv hm _ (abs_nonneg _)]; exact abs_det_schur hm hF hM
  have hY : 0 ≤ |(((schur F).det : ℤ) : ℝ)| ^ ((1 : ℝ) / m) := Real.rpow_nonneg (abs_nonneg _) _
  rw [neg_mulVec, dotProduct_neg] at hg0 hg
  generalize hg' : b' ⬝ᵥ (schur F *ᵥ b') = g at hid hg0 hg
  generalize ht : F 0 0 * b0 + rowTail F ⬝ᵥ b' = t at hid hb1 hb2
  have hsq : t ^ 2 ≤ F 0 0 ^ 2 := by
    have : |t| ^ 2 ≤ F 0 0 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
    rwa [sq_abs] at this
  have hsq' : F 0 0 ^ 2 ≤ 4 * t ^ 2 := by
    have : (F 0 0) ^ 2 ≤ (2 * |t|) ^ 2 := pow_le_pow_left₀ hM.le hb1 2
    nlinarith [sq_abs t]
  have hv : v ≤ 0 := by
    by_contra hv
    push Not at hv
    have hvM := hmin' hv
    nlinarith [mul_le_mul_of_nonneg_left hvM hM.le]
  have h4 : F 0 0 ^ 2 ≤ 4 * (-g) := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hM.le hv]
  have h4r : ((F 0 0 : ℤ) : ℝ) ^ 2 ≤ 4 * ((-g : ℤ) : ℝ) := by exact_mod_cast h4
  have hMr : (0 : ℝ) < ((F 0 0 : ℤ) : ℝ) := by exact_mod_cast hM
  refine bound_of_sq_le hm hMr hY (abs_nonneg _) hYm ?_
  nlinarith [h4r, hg]

end Steps

section Pos

/-- A positive real value of an integer form gives a positive integer value (density of $\mathbb Q^n$). -/
theorem exists_int_pos {n : ℕ} (F : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℝ)
    (hu : 0 < u ⬝ᵥ cM F *ᵥ u) : ∃ a : Fin n → ℤ, 0 < a ⬝ᵥ F *ᵥ a := by
  have hc : Continuous fun y : Fin n → ℝ => y ⬝ᵥ cM F *ᵥ y := by
    unfold dotProduct mulVec
    fun_prop
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hc) u hu
  choose q hq using fun i => exists_rat_btwn (show u i < u i + ε by linarith)
  have hmem : (fun i => (q i : ℝ)) ∈ Metric.ball u ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [(hq i).1, (hq i).2]
  have hpos : 0 < (fun i => (q i : ℝ)) ⬝ᵥ cM F *ᵥ (fun i => (q i : ℝ)) := hball hmem
  set D : ℕ := ∏ i, (q i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (q i).den_pos
  have hz : ∀ i, ∃ z : ℤ, (z : ℝ) = (D : ℝ) * (q i : ℝ) := by
    intro i
    obtain ⟨c, hc⟩ : (q i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨(q i).num * c, ?_⟩
    have h1 : (q i : ℝ) = ((q i).num : ℝ) / ((q i).den : ℝ) := by
      rw [Rat.cast_def]
    have h2 : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
    rw [hc, h1]
    push_cast
    field_simp
  choose a ha using hz
  refine ⟨a, ?_⟩
  have hvec : (fun i => (a i : ℝ)) = (D : ℝ) • fun i => (q i : ℝ) := by
    funext i; simp [ha i]
  have : ((a ⬝ᵥ F *ᵥ a : ℤ) : ℝ) = (D : ℝ) ^ 2 * ((fun i => (q i : ℝ)) ⬝ᵥ cM F *ᵥ (fun i => (q i : ℝ))) := by
    rw [cast_dot, hvec, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have : (0 : ℝ) < ((a ⬝ᵥ F *ᵥ a : ℤ) : ℝ) := by rw [this]; positivity
  exact_mod_cast this

end Pos

section Normalize

variable {m : ℕ}

/-- $x^{\mathsf T}(T^{\mathsf T}FT)x = (Tx)^{\mathsf T}F(Tx)$. -/
theorem dot_congr {R : Type*} [CommRing R] {k : ℕ} (T F : Matrix (Fin k) (Fin k) R) (x : Fin k → R) :
    x ⬝ᵥ (Tᵀ * F * T) *ᵥ x = (T *ᵥ x) ⬝ᵥ F *ᵥ (T *ᵥ x) := by
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The least positive value of an integral form is attained at a vector with $\gcd = 1$. -/
theorem exists_min_primitive (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hpos : ∃ a : Fin (m + 1) → ℤ, 0 < a ⬝ᵥ F *ᵥ a) :
    ∃ a0 : Fin (m + 1) → ℤ, 0 < a0 ⬝ᵥ F *ᵥ a0 ∧ Finset.univ.gcd a0 = 1 ∧
      ∀ x : Fin (m + 1) → ℤ, 0 < x ⬝ᵥ F *ᵥ x → a0 ⬝ᵥ F *ᵥ a0 ≤ x ⬝ᵥ F *ᵥ x := by
  classical
  have hex : ∃ k : ℕ, ∃ a : Fin (m + 1) → ℤ, a ⬝ᵥ F *ᵥ a = (k : ℤ) ∧ 0 < k := by
    obtain ⟨a, ha⟩ := hpos
    refine ⟨(a ⬝ᵥ F *ᵥ a).toNat, a, (Int.toNat_of_nonneg ha.le).symm, Int.lt_toNat.mpr (by simpa using ha)⟩
  obtain ⟨a0, ha0, hk0⟩ := Nat.find_spec hex
  have hmin : ∀ x : Fin (m + 1) → ℤ, 0 < x ⬝ᵥ F *ᵥ x → a0 ⬝ᵥ F *ᵥ a0 ≤ x ⬝ᵥ F *ᵥ x := by
    intro x hx
    have := Nat.find_min' hex (m := (x ⬝ᵥ F *ᵥ x).toNat)
      ⟨x, (Int.toNat_of_nonneg hx.le).symm, Int.lt_toNat.mpr (by simpa using hx)⟩
    rw [ha0]
    omega
  refine ⟨a0, by rw [ha0]; exact_mod_cast hk0, ?_, hmin⟩
  set g := Finset.univ.gcd a0 with hg
  have hg0 : 0 ≤ g := Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  have hgd : ∀ i, g ∣ a0 i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hgne : g ≠ 0 := by
    intro h0
    have : ∀ i, a0 i = 0 := fun i => by simpa [h0] using hgd i
    have h2 : a0 = 0 := funext this
    rw [h2] at ha0
    simp only [Matrix.mulVec_zero, dotProduct_zero] at ha0
    omega
  by_contra hne
  have hg2 : 2 ≤ g := by omega
  choose a' ha' using hgd
  have hvec : a0 = g • a' := funext fun i => by simp [ha' i]
  have hval : a0 ⬝ᵥ F *ᵥ a0 = g ^ 2 * (a' ⬝ᵥ F *ᵥ a') := by
    rw [hvec, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hpos' : 0 < a' ⬝ᵥ F *ᵥ a' := by
    have h1 : 0 < a0 ⬝ᵥ F *ᵥ a0 := by rw [ha0]; exact_mod_cast hk0
    rw [hval] at h1
    exact pos_of_mul_pos_right h1 (by positivity)
  have := hmin a' hpos'
  rw [hval] at this
  have h4 : 4 ≤ g ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h4 hpos'.le]

/-- **Change of basis:** a form with $F_{00} = M$ equal to its least positive value, equivalent over $\mathbb Z$ to $F$. -/
theorem exists_normalized (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hF : F.IsSymm)
    (hpos : ∃ a : Fin (m + 1) → ℤ, 0 < a ⬝ᵥ F *ᵥ a) :
    ∃ F' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ, F'.IsSymm ∧ F'.det = F.det ∧ 0 < F' 0 0 ∧
      (∀ x, 0 < x ⬝ᵥ F' *ᵥ x → F' 0 0 ≤ x ⬝ᵥ F' *ᵥ x) ∧ (∃ T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ,
        IsUnit T.det ∧ F' = Tᵀ * F * T) ∧
      ∃ a0, 0 < a0 ⬝ᵥ F *ᵥ a0 ∧ a0 ⬝ᵥ F *ᵥ a0 = F' 0 0 := by
  obtain ⟨a0, ha0, hgcd, hmin⟩ := exists_min_primitive F hpos
  obtain ⟨T, hT⟩ := (exists_basis_first_iff_gcd (n := m + 1) (by omega) a0).2 hgcd
  have hv : ∀ x, x ⬝ᵥ (T.valᵀ * F * T.val) *ᵥ x = (T.val *ᵥ x) ⬝ᵥ F *ᵥ (T.val *ᵥ x) :=
    dot_congr T.val F
  have h00 : (T.valᵀ * F * T.val) 0 0 = a0 ⬝ᵥ F *ᵥ a0 := by
    have h1 : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ),
        M 0 0 = (Pi.single 0 1 : Fin (m + 1) → ℤ) ⬝ᵥ M *ᵥ (Pi.single 0 1) := fun M => by
      simp [mulVec_single, single_dotProduct]
    rw [h1 (T.valᵀ * F * T.val), hv]
    have : (T.val *ᵥ Pi.single (0 : Fin (m + 1)) 1) = a0 := hT
    rw [this]
  have hdet : (T.valᵀ * F * T.val).det = F.det := by
    rw [det_mul, det_mul, det_transpose]
    rcases det_GL_int_eq T with h | h <;> rw [h] <;> ring
  refine ⟨T.valᵀ * F * T.val, ?_, hdet, by rw [h00]; exact ha0, ?_, ⟨T.val, ?_, rfl⟩, a0, ha0, h00.symm⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, hF.eq, Matrix.mul_assoc]
  · intro x hx
    rw [hv] at hx ⊢
    rw [h00]
    exact hmin _ hx
  · exact (Matrix.isUnit_iff_isUnit_det _).mp T.isUnit

end Normalize

section Chain

variable {m : ℕ}

/-- The canonical signature matrix with $r \ge 1$ plus signs is congruent to $\operatorname{diag}(1) \oplus$ the one with $r-1$ plus signs. -/
theorem cong_diag_cons (r : ℕ) (hr : 1 ≤ r) :
    Cong (diagonal (canonEps r : Fin (m + 1) → ℝ)) (consForm 1 (diagonal (canonEps (r - 1) : Fin m → ℝ))) := by
  refine ⟨1, by simp, fun x => ?_⟩
  rw [one_mulVec, dot_consForm, dot_diagonal, dot_diagonal, Fin.sum_univ_succ]
  have h0 : canonEps r (0 : Fin (m + 1)) = 1 := by
    unfold canonEps; exact ite_eq_left hr
  have h1 : ∀ j : Fin m, canonEps r j.succ = canonEps (r - 1) j := fun j => by
    simp only [canonEps, Fin.val_succ]
    congr 1
    apply propext
    omega
  simp only [h0, h1, Fin.tail]

/-- Congruence of a form with its integral change of basis. -/
theorem cong_cM_conj {k : ℕ} (F T : Matrix (Fin k) (Fin k) ℤ) (hT : IsUnit T.det) :
    Cong (cM F) (cM (Tᵀ * F * T)) := by
  refine ⟨cM T, ?_, fun x => ?_⟩
  · rw [cM_det]; exact hT.map (Int.castRingHom ℝ)
  · have hm : ∀ A B : Matrix (Fin k) (Fin k) ℤ, cM (A * B) = cM A * cM B := fun A B =>
      Matrix.map_mul (f := Int.castRingHom ℝ)
    have : cM (Tᵀ * F * T) = (cM T)ᵀ * cM F * cM T := by
      rw [hm, hm]
      simp [cM, Matrix.transpose_map]
    rw [this, dot_congr]

/-- **The signature of the completed square:** if $F \sim \operatorname{diag}(\varepsilon)$ with $r \ge 1$ plus signs and
$F_{00} > 0$, then $G \sim \operatorname{diag}(\varepsilon')$ with $r - 1$ plus signs, when $\det G \ne 0$. -/
theorem cong_schur_of {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) (hM : 0 < F 0 0)
    (hG : (schur F).det ≠ 0) (r : ℕ) (hr : 1 ≤ r) (hC : Cong (cM F) (diagonal (canonEps r : Fin (m + 1) → ℝ))) :
    Cong (cM (schur F)) (diagonal (canonEps (r - 1) : Fin m → ℝ)) := by
  have hMr : (0 : ℝ) < ((F 0 0 : ℤ) : ℝ) := by exact_mod_cast hM
  have h1 : Cong (consForm 1 (cM (schur F))) (((F 0 0 : ℤ) : ℝ) • cM F) := by
    have := cong_cons_schur (cM_isSymm hF) (by simpa [cM] using hMr.ne')
    rw [cM_schur]
    simpa [cM] using this
  have h2 : Cong (((F 0 0 : ℤ) : ℝ) • cM F) (cM F) := cong_smul_pos hMr _
  have h3 := ((h1.trans h2).trans hC).trans (cong_diag_cons r hr)
  refine witt_cons ?_ ?_ ?_ h3
  · rw [cM_schur]; exact schur_isSymm (cM_isSymm hF)
  · exact (isSymm_diagonal _)
  · rw [cM_det]; exact_mod_cast hG

end Chain

section Core

/-- Negating the canonical signature matrix with no plus signs gives the one with all $m$ entries $+1$. -/
theorem neg_diag_canon (m : ℕ) : -(diagonal (canonEps 0 : Fin m → ℝ)) = diagonal (canonEps m : Fin m → ℝ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [canonEps, i.isLt]
  · simp [h]

/-- **The inductive step of Lemma 3.2** for a form already normalized so that $F_{00} = M$ is its least positive value. -/
theorem core_step (m : ℕ)
    (ih : ∀ r s : ℕ, r + s = m → 1 ≤ r → ∀ G : Matrix (Fin m) (Fin m) ℤ, G.IsSymm → G.det ≠ 0 →
      Cong (cM G) (diagonal (canonEps r : Fin m → ℝ)) →
      ∃ a : Fin m → ℤ, 0 < a ⬝ᵥ G *ᵥ a ∧
        ((a ⬝ᵥ G *ᵥ a : ℤ) : ℝ) ≤ casselsDelta r s * |((G.det : ℤ) : ℝ)| ^ ((1 : ℝ) / m))
    (r s : ℕ) (hrs : r + s = m + 1) (hr : 1 ≤ r) {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm)
    (hd : F.det ≠ 0) (hC : Cong (cM F) (diagonal (canonEps r : Fin (m + 1) → ℝ))) (hM : 0 < F 0 0)
    (hmin : ∀ x : Fin (m + 1) → ℤ, 0 < x ⬝ᵥ F *ᵥ x → F 0 0 ≤ x ⬝ᵥ F *ᵥ x) :
    ((F 0 0 : ℤ) : ℝ) ≤ casselsDelta r s * |((F.det : ℤ) : ℝ)| ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hr1 : r = 1 := by omega
    have hs0 : s = 0 := by omega
    subst hr1 hs0
    have hdet : F.det = F 0 0 := by simp [Matrix.det_unique]
    rw [hdet]
    have hMr : (0 : ℝ) < ((F 0 0 : ℤ) : ℝ) := by exact_mod_cast hM
    simp [casselsDelta, abs_of_pos hMr]
  · have hdG : (schur F).det ≠ 0 := by
      intro h
      have := abs_det_schur hm hF hM
      rw [h] at this
      simp only [Int.cast_zero, abs_zero] at this
      have hMr : (0 : ℝ) < ((F 0 0 : ℤ) : ℝ) := by exact_mod_cast hM
      have hd' : (0 : ℝ) < |((F.det : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast hd)
      have := mul_pos (pow_pos hMr (m - 1)) hd'
      linarith
    have hCG := cong_schur_of hF hM hdG r hr hC
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · -- r = 1
      have hr1 : r = 1 := by omega
      subst hr1
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hm' : m = s' + 1 := by omega
      have hCG' : Cong (cM (-schur F)) (diagonal (canonEps m : Fin m → ℝ)) := by
        have h1 := hCG.neg
        have h2 : (canonEps (1 - 1) : Fin m → ℝ) = canonEps 0 := rfl
        rw [h2, neg_diag_canon] at h1
        have h3 : cM (-schur F) = -cM (schur F) := by ext i j; simp [cM]
        rw [h3]; exact h1
      have hdn : (-schur F).det ≠ 0 := by
        rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdG
      obtain ⟨a, ha0, ha⟩ := ih m 0 (by omega) (by omega) (-schur F) (by rw [Matrix.IsSymm, transpose_neg, (schur_isSymm hF).eq]) hdn hCG'
      have key := step_one hm hF hM hmin ⟨a, ha0, ha⟩
      have hc : casselsDelta m 0 = casselsDelta (s' + 1) 0 := by rw [hm']
      have hmr : (m : ℝ) = s' + 1 := by exact_mod_cast hm'
      rw [hc, hmr] at key
      rw [casselsDelta]
      push_cast at key ⊢
      rw [hmr]
      convert key using 3; ring_nf
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
      have hm' : m = r' + s + 1 := by omega
      have hCG2 : Cong (cM (schur F)) (diagonal (canonEps (r' + 1) : Fin m → ℝ)) := by
        simpa using hCG
      obtain ⟨a, ha0, ha⟩ := ih (r' + 1) s (by omega) (by omega) (schur F) (schur_isSymm hF) hdG hCG2
      have key := step_pos hm hF hM hmin ⟨a, ha0, ha⟩
      have hmr : (m : ℝ) = r' + s + 1 := by exact_mod_cast hm'
      rw [hmr] at key
      rw [casselsDelta]
      push_cast at key ⊢
      rw [hmr]
      convert key using 3; ring_nf

/-- **Lemma 3.2 for symmetric integer matrices** (induction on the dimension). -/
theorem core : ∀ (n r s : ℕ), r + s = n → 1 ≤ r → ∀ F : Matrix (Fin n) (Fin n) ℤ, F.IsSymm → F.det ≠ 0 →
    Cong (cM F) (diagonal (canonEps r : Fin n → ℝ)) →
    ∃ a : Fin n → ℤ, 0 < a ⬝ᵥ F *ᵥ a ∧
      ((a ⬝ᵥ F *ᵥ a : ℤ) : ℝ) ≤ casselsDelta r s * |((F.det : ℤ) : ℝ)| ^ ((1 : ℝ) / n)
  | 0, r, s, hrs, hr, _, _, _, _ => by omega
  | m + 1, r, s, hrs, hr, F, hF, hd, hC => by
    have ih := core m
    have hC0 := hC
    obtain ⟨P, hP, hPv⟩ := hC
    have h1 := hPv (Pi.single 0 1)
    rw [dot_diagonal] at h1
    have h2 : ∑ i : Fin (m + 1), canonEps r i * ((Pi.single (0 : Fin (m + 1)) (1 : ℝ) : Fin (m + 1) → ℝ) i) ^ 2 = 1 := by
      rw [Finset.sum_eq_single (0 : Fin (m + 1))]
      · simp only [Pi.single_eq_same]
        have h0 : canonEps r (0 : Fin (m + 1)) = 1 := by unfold canonEps; exact ite_eq_left hr
        rw [h0]; ring
      · intro b _ hb; simp [hb]
      · simp
    rw [h2] at h1
    obtain ⟨a, ha⟩ := exists_int_pos F (P *ᵥ Pi.single 0 1) (by rw [h1]; norm_num)
    obtain ⟨F', hF's, hdet, hMpos, hmin, ⟨T, hTu, hF'⟩, a0, ha0, ha0eq⟩ := exists_normalized F hF ⟨a, ha⟩
    have hC' : Cong (cM F') (diagonal (canonEps r : Fin (m + 1) → ℝ)) := by
      have := cong_cM_conj F T hTu
      rw [← hF'] at this
      exact this.symm.trans hC0
    have hd' : F'.det ≠ 0 := by rw [hdet]; exact hd
    have key := core_step m ih r s hrs hr hF's hd' hC' hMpos hmin
    refine ⟨a0, ha0, ?_⟩
    rw [ha0eq]
    rw [hdet] at key
    exact key

end Core

section Bridge

variable {n : ℕ}

/-- The Gram matrix data of a classically integral form with nonzero Hessian determinant. -/
theorem classical_data (f : QuadForm ℤ n) (hf : IsClassicallyIntegral f) (hd : f.hessian.det ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, A.IsSymm ∧ A.det ≠ 0 ∧ (∀ x, f.eval x = x ⬝ᵥ A *ᵥ x) ∧
      gramDet f = ((A.det : ℤ) : ℝ) ∧
      ∀ y : Fin n → ℝ, (f.map (Int.castRingHom ℝ)).eval y = y ⬝ᵥ cM A *ᵥ y := by
  obtain ⟨A, hA, hfA⟩ := hf
  have hev : ∀ x, f.eval x = x ⬝ᵥ A *ᵥ x := fun x => hfA x
  have hH : f.hessian = (2 : ℤ) • A := by
    refine eq_of_dot_eq (LocalDensity.hessian_isSymm f) ?_ fun x => ?_
    · rw [Matrix.IsSymm, transpose_smul, hA.eq]
    · rw [← LocalDensity.two_mul_eval_eq_hessian, hev, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hdet : f.hessian.det = 2 ^ n * A.det := by
    rw [hH, det_smul, Fintype.card_fin]
  have hAd : A.det ≠ 0 := by
    intro h; rw [h, mul_zero] at hdet; exact hd hdet
  have hgram : gramDet f = ((A.det : ℤ) : ℝ) := by
    rw [gramDet, hdet]; push_cast; field_simp
  refine ⟨A, hA, hAd, hev, hgram, fun y => ?_⟩
  have h1 : (f.map (Int.castRingHom ℝ)).eval y = f.evalIn ℝ y := by
    simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map]
  rw [h1, evalIn_real_eq_gram]
  congr 2
  rw [gramMatrix, hH]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, cM, eq_intCast, Int.coe_castRingHom]
  push_cast
  ring

end Bridge

section Sign

/-- A nondegenerate real diagonal form is congruent to a $\pm1$ diagonal form. -/
theorem cong_diag_sign {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    Cong (diagonal a) (diagonal (fun i => if 0 < a i then (1 : ℝ) else -1)) := by
  refine ⟨diagonal fun i => (Real.sqrt |a i|)⁻¹, ?_, fun x => ?_⟩
  · rw [det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    have : 0 < Real.sqrt |a i| := Real.sqrt_pos.mpr (abs_pos.mpr (ha i))
    positivity
  · rw [dot_diagonal, dot_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal]
    have hpos : 0 < |a i| := abs_pos.mpr (ha i)
    have hs : Real.sqrt |a i| ^ 2 = |a i| := Real.sq_sqrt hpos.le
    have hs0 : Real.sqrt |a i| ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have : a i * ((Real.sqrt |a i|)⁻¹ * x i) ^ 2 = (a i / |a i|) * x i ^ 2 := by
      rw [mul_pow, inv_pow, hs]; field_simp
    rw [this]
    rcases lt_or_gt_of_ne (ha i) with h | h
    · rw [ite_eq_right (not_lt.mpr h.le), abs_of_neg h, div_neg, div_self (ha i)]
    · rw [ite_eq_left h, abs_of_pos h, div_self (ha i)]

/-- **Lemma 3.1 for matrices:** a small nonzero value of a regular classically integral form of known real signature. -/
theorem exists_small_of_cong {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hAd : A.det ≠ 0) (ε : Fin n → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hC : Cong (cM A) (diagonal ε)) :
    ∃ a : Fin n → ℤ, a ⬝ᵥ A *ᵥ a ≠ 0 ∧ |((a ⬝ᵥ A *ᵥ a : ℤ) : ℝ)| ≤
      (∑ r ∈ Finset.range (n + 1), casselsDelta r (n - r)) * |((A.det : ℤ) : ℝ)| ^ ((1 : ℝ) / n) := by
  classical
  have hY : 0 ≤ |((A.det : ℤ) : ℝ)| ^ ((1 : ℝ) / n) := Real.rpow_nonneg (abs_nonneg _) _
  have hle : ∀ r ∈ Finset.range (n + 1), casselsDelta r (n - r) ≤
      ∑ r ∈ Finset.range (n + 1), casselsDelta r (n - r) := fun r hr =>
    Finset.single_le_sum (f := fun r => casselsDelta r (n - r)) (fun i _ => casselsDelta_nonneg _ _) hr
  by_cases h0 : 0 < (Finset.univ.filter fun i => ε i = 1).card
  · set r := (Finset.univ.filter fun i => ε i = 1).card with hr
    have hrn : r ≤ n := by
      rw [hr]; exact (Finset.card_filter_le _ _).trans (by simp)
    have hC' := hC.trans (cong_diag_canon ε hε r hr.symm)
    obtain ⟨a, ha0, ha⟩ := core n r (n - r) (by omega) h0 A hA hAd hC'
    refine ⟨a, ha0.ne', ?_⟩
    rw [abs_of_pos (by exact_mod_cast ha0)]
    calc _ ≤ _ := ha
      _ ≤ _ := mul_le_mul_of_nonneg_right (hle r (Finset.mem_range.mpr (by omega))) hY
  · have hcard : (Finset.univ.filter fun i => ε i = 1).card = 0 := by omega
    have hall : ∀ i, ε i = -1 := fun i => by
      rcases hε i with h | h
      · exfalso
        have : i ∈ Finset.univ.filter fun i => ε i = 1 := by simp [h]
        rw [Finset.card_eq_zero] at hcard
        rw [hcard] at this
        simp at this
      · exact h
    have hnegε : -(diagonal ε : Matrix (Fin n) (Fin n) ℝ) = diagonal (fun _ => (1 : ℝ)) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [hall i]
      · simp [h]
    have hC' : Cong (cM (-A)) (diagonal (canonEps n : Fin n → ℝ)) := by
      have h1 := hC.neg
      rw [hnegε] at h1
      have h3 : cM (-A) = -cM A := by ext i j; simp [cM]
      have h4 : (diagonal (fun _ => (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) = diagonal (canonEps n) := by
        congr 1; funext i; simp [canonEps, i.isLt]
      rw [h3, ← h4]; exact h1
    have hdn : (-A).det ≠ 0 := by
      rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hAd
    obtain ⟨a, ha0, ha⟩ := core n n 0 (by omega) hn (-A) (by rw [Matrix.IsSymm, transpose_neg, hA.eq]) hdn hC'
    rw [neg_mulVec, dotProduct_neg] at ha0 ha
    have hdabs : |(((-A).det : ℤ) : ℝ)| = |((A.det : ℤ) : ℝ)| := by
      rw [Matrix.det_neg]; push_cast
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [hdabs] at ha
    rw [Int.cast_neg] at ha
    refine ⟨a, by omega, ?_⟩
    rw [abs_of_neg (by exact_mod_cast (by omega : a ⬝ᵥ A *ᵥ a < 0))]
    calc _ ≤ _ := ha
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa using hle n (Finset.mem_range.mpr (by omega))) hY

end Sign

end Ch9Sec3

/-- **Cassels, Lemma 3.2** (Ch. 9, p. 136): *for all pairs of integers $r \ge 1$ and $s \ge 0$ there is a constant
$\delta = \delta(r, s)$ with the following property: let $f(\mathbf x)$ be a regular integral quadratic form which is
real-equivalent to $x_1^2 + \dots + x_r^2 - x_{r+1}^2 - \dots - x_{r+s}^2$ ($r + s = n$). Then there is an integral
vector $\mathbf a$ such that $0 < f(\mathbf a) \le \delta\lvert d\rvert^{1/n}$, where $d = d(f)$.* Here the real form is
$\sum_i \varepsilon_ix_i^2$ with $\varepsilon_i = \pm 1$, $r$ of them $+1$ and $s$ of them $-1$, and $\delta$ is
`casselsDelta r s`. -/
@[kb "cassels1978" "Ch. 9, Lemma 3.2, p. 136"]
theorem exists_pos_value_le {n : ℕ} (f : QuadForm ℤ n) (hf : IsClassicallyIntegral f) (hd : f.hessian.det ≠ 0)
    (ε : Fin n → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsig : IsometricGL (f.map (Int.castRingHom ℝ)) (QuadForm.diag ε))
    (r s : ℕ) (hr : (Finset.univ.filter fun i => ε i = 1).card = r) (hrs : r + s = n) (hr1 : 1 ≤ r) :
    ∃ a : Fin n → ℤ, 0 < f.eval a ∧ (f.eval a : ℝ) ≤ casselsDelta r s * |gramDet f| ^ ((1 : ℝ) / n) := by
  obtain ⟨A, hA, hAd, hev, hgram, hreal⟩ := Ch9Sec3.classical_data f hf hd
  have hC : Ch9Sec3.Cong (Ch9Sec3.cM A) (Matrix.diagonal ε) := by
    obtain ⟨g, hg⟩ := hsig
    refine ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, fun x => ?_⟩
    rw [← hreal, hg x, Ch9Sec3.dot_diagonal]
    simp [QuadForm.eval, QuadForm.evalIn_diag]
  have hC' := hC.trans (Ch9Sec3.cong_diag_canon ε hε r hr)
  obtain ⟨a, ha0, ha⟩ := Ch9Sec3.core n r s hrs hr1 A hA hAd hC'
  refine ⟨a, by rw [hev]; exact ha0, ?_⟩
  rw [hev, hgram]
  exact ha

/-- **Cassels, Lemma 3.1** (Ch. 9, p. 135): *for each $n \ge 1$ there is a constant $C_n$ with the following property:
let $f(\mathbf x)$ be a regular integral quadratic form in $n$ variables. Then there is an integral vector $\mathbf a$
such that $f(\mathbf a) \ne 0$ (3.1) and $\lvert f(\mathbf a)\rvert \le C_n\lvert d\rvert^{1/n}$ (3.2), where
$d = d(f)$ (3.3) is the determinant of $f$.* (Integral in the classical sense.) -/
@[kb "cassels1978" "Ch. 9, Lemma 3.1, p. 135"]
theorem exists_value_ne_zero_le (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ f : QuadForm ℤ n, IsClassicallyIntegral f → f.hessian.det ≠ 0 →
      ∃ a : Fin n → ℤ, f.eval a ≠ 0 ∧ |(f.eval a : ℝ)| ≤ C * |gramDet f| ^ ((1 : ℝ) / n) := by
  refine ⟨∑ r ∈ Finset.range (n + 1), casselsDelta r (n - r), fun f hf hd => ?_⟩
  obtain ⟨A, hA, hAd, hev, hgram, hreal⟩ := Ch9Sec3.classical_data f hf hd
  have hnd : (f.map (Int.castRingHom ℝ)).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    have : (f.map (Int.castRingHom ℝ)).hessian = f.hessian.map (Int.castRingHom ℝ) := by
      simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
    rw [this]
    have h2 := RingHom.map_det (Int.castRingHom ℝ) f.hessian
    rw [RingHom.mapMatrix_apply] at h2
    rw [← h2]
    simpa using hd
  obtain ⟨a, ha, P, hP, hPa⟩ := FieldGen.exists_isometric_diag (f.map (Int.castRingHom ℝ)) hnd
  have hC : Ch9Sec3.Cong (Ch9Sec3.cM A) (Matrix.diagonal a) := by
    refine ⟨P, hP, fun x => ?_⟩
    have h3 := hPa x
    rw [QuadForm.evalIn_diag] at h3
    rw [← hreal]
    show QuadForm.evalIn ℝ _ _ = _
    rw [h3, Ch9Sec3.dot_diagonal]
    simp
  have hC2 := hC.trans (Ch9Sec3.cong_diag_sign a ha)
  obtain ⟨b, hb0, hb⟩ := Ch9Sec3.exists_small_of_cong hn hA hAd _
    (fun i => by by_cases h : 0 < a i <;> simp [h]) hC2
  refine ⟨b, by rw [hev]; exact hb0, ?_⟩
  rw [hev, hgram]
  exact hb


end QuadFormsKB.Siegel
