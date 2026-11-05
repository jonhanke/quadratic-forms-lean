/-
# Cassels, Chapter 13, §9: real automorphs of indefinite quaternary forms

Formalization of the algebraic statements of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §9, *Quaternary
forms*, pp. 317–319. Up to sign there are two real classes of indefinite quaternary forms:

* $f_{3,1} = x_0^2 + x_1^2 + x_2^2 - x_3^2$ (9.1): $-f_{3,1}(\vec{x})$ is the determinant of the Hermitian matrix
  $X(\vec{x}) = \begin{pmatrix} x_3 + x_0 & x_1 + ix_2 \\ x_1 - ix_2 & x_3 - x_0\end{pmatrix}$ ((9.4), `hermOf`), and
  $X \mapsto AXA^{*}$ with $\det A = 1$ (9.5)–(9.8) gives a real automorph $T(A)$ of determinant $1$; the $A$ for which
  $T(A)$ fixes $(0, 0, 0, 1)$ are the unitary ones.
* $f_{2,2} = x_0x_3 - x_1x_2$ (9.10), the determinant of $X = \begin{pmatrix} x_0 & x_1 \\ x_2 & x_3\end{pmatrix}$ (9.11):
  $X \mapsto AXB$ with $\det A = \det B = 1$ (9.12)–(9.13) is an automorph, and it preserves
  $\operatorname{tr}X^{\mathsf T}X$ (9.14) iff $A^{\mathsf T}A = BB^{\mathsf T} = I$ (9.15)–(9.16).

Cassels' variables $x_1, \dots, x_4$ are $x_0, \dots, x_3$ here. The displays (9.1), (9.4), (9.9)–(9.11) are garbled in
the machine-read text; the forms and matrices are reconstructed from the surrounding argument (determinants,
the fixed vector $(0, 0, 0, 1)$ and the trace (9.14)). The geometric identifications (the ball and non-Euclidean
3-space, products of two non-Euclidean planes) are not formalized.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic

open Matrix Complex

namespace QuadFormsKB.Reduction

/-- **The Hermitian matrix of (9.4)**: $X(\vec{x}) = \begin{pmatrix} x_3 + x_0 & x_1 + ix_2 \\ x_1 - ix_2 & x_3 - x_0
\end{pmatrix}$, with $\det X(\vec{x}) = x_3^2 - x_0^2 - x_1^2 - x_2^2 = -f_{3,1}(\vec{x})$. -/
@[kb "cassels1978" "Ch. 13, §9, (9.1)–(9.4), p. 317"]
noncomputable def hermOf (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 3 + x 0 : ℝ), (x 1 : ℂ) + (x 2 : ℂ) * I; (x 1 : ℂ) - (x 2 : ℂ) * I, (x 3 - x 0 : ℝ)]

/-- **(9.4)**: $\det X(\vec{x}) = -(x_0^2 + x_1^2 + x_2^2 - x_3^2)$. -/
@[kb "cassels1978" "Ch. 13, §9, (9.4), p. 317"]
theorem det_hermOf (x : Fin 4 → ℝ) : (hermOf x).det = -((x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2 : ℝ) : ℂ) := by
  rw [hermOf, Matrix.det_fin_two_of]
  apply Complex.ext <;> simp [sq] <;> ring

/-- Helper: the coordinates $(x_0, \dots, x_3)$ of a Hermitian matrix $Y$ in the parametrisation `hermOf`. -/
private noncomputable def coord (Y : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![((Y 0 0).re - (Y 1 1).re) / 2, (Y 0 1).re, (Y 0 1).im, ((Y 0 0).re + (Y 1 1).re) / 2]

/-- Helper: $A X A^{*}$ is Hermitian, so it is `hermOf` of its coordinates. -/
private lemma coord_herm (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    hermOf (coord (A * hermOf x * Aᴴ)) = A * hermOf x * Aᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · apply Complex.ext <;>
    simp [hermOf, coord, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> ring

/-- Helper: the real $4 \times 4$ matrix of $x \mapsto \operatorname{coord}(A X(x) A^{*})$. -/
private noncomputable def Tm (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => coord (A * hermOf (Pi.single j 1) * Aᴴ) i

/-- Helper: `Tm A` acts as $x \mapsto \operatorname{coord}(A X(x) A^{*})$. -/
private lemma Tm_mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    Tm A *ᵥ x = coord (A * hermOf x * Aᴴ) := by
  ext i
  fin_cases i <;>
  · simp [Tm, coord, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hermOf, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
    <;> ring

/-- Helper: $\det T(A) = |\det A|^4$ as a polynomial identity. -/
private lemma det_Tm (a b c d : ℂ) : (Tm !![a, b; c, d]).det =
    ((a*d-b*c).re^2 + (a*d-b*c).im^2)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_succ_row_zero, Matrix.det_fin_zero]
  simp [Fin.succAbove, Fin.lt_def, Tm, coord, hermOf, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  ring_nf

/-- Helper: $X(0,0,0,1) = I$. -/
private lemma hermOf_e3 : hermOf ![0, 0, 0, 1] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hermOf]

/-- **The automorph $T(A)$ of $f_{3,1}$** (Cassels, Ch. 13, §9, (9.5)–(9.9), p. 317): for a complex $2 \times 2$ matrix
$A$ with $\det A = 1$ there is a real $4 \times 4$ matrix $T$ with $X(T\vec{x}) = AX(\vec{x})A^{*}$; it is an automorph of
$f_{3,1} = x_0^2 + x_1^2 + x_2^2 - x_3^2$ with $\det T = 1$ ("It may be checked by direct calculation that
$\det(T(A)) = +1$"); $T$ fixes $(0, 0, 0, 1)$ iff $A$ is unitary ($AA^{*} = I$, p. 318). -/
@[kb "cassels1978" "Ch. 13, §9, (9.5)–(9.9), pp. 317–318"]
theorem exists_automorph_hermOf {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) :
    ∃ T : Matrix (Fin 4) (Fin 4) ℝ, (∀ x, hermOf (T *ᵥ x) = A * hermOf x * Aᴴ) ∧
      (∀ x : Fin 4 → ℝ, (T *ᵥ x) 0 ^ 2 + (T *ᵥ x) 1 ^ 2 + (T *ᵥ x) 2 ^ 2 - (T *ᵥ x) 3 ^ 2 =
        x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2) ∧ T.det = 1 ∧
      (T *ᵥ ![0, 0, 0, 1] = ![0, 0, 0, 1] ↔ A * Aᴴ = 1) := by
  have h1 : ∀ x, hermOf (Tm A *ᵥ x) = A * hermOf x * Aᴴ := fun x => by
    rw [Tm_mulVec, coord_herm]
  refine ⟨Tm A, h1, ?_, ?_, ?_⟩
  · intro x
    have h := congrArg Matrix.det (h1 x)
    rw [det_hermOf, Matrix.det_mul, Matrix.det_mul, hA, det_hermOf, Matrix.det_conjTranspose,
      hA] at h
    simp at h
    have h' : (Tm A *ᵥ x) 3 ^ 2 - ((Tm A *ᵥ x) 0 ^ 2 + (Tm A *ᵥ x) 1 ^ 2 + (Tm A *ᵥ x) 2 ^ 2) =
      x 3 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by exact_mod_cast h
    linarith
  · have h := det_Tm (A 0 0) (A 0 1) (A 1 0) (A 1 1)
    rw [← Matrix.eta_fin_two A] at h
    have hA' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hA
    rw [h, hA']; simp
  · rw [Tm_mulVec]
    constructor
    · intro h
      have := coord_herm A ![0, 0, 0, 1]
      rw [h, hermOf_e3, mul_one] at this
      exact this.symm
    · intro h
      rw [hermOf_e3, mul_one, h]
      ext i; fin_cases i <;> simp [coord]

/-- **The automorph $T(A, B)$ of $f_{2,2}$** (Cassels, Ch. 13, §9, (9.10)–(9.13), p. 318): for real $2 \times 2$
matrices with $\det A = \det B = 1$, $X \mapsto AXB$ preserves $\det X = x_0x_3 - x_1x_2$. -/
@[kb "cassels1978" "Ch. 13, §9, (9.10)–(9.13), p. 318"]
theorem det_mul_mul_eq {A B : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) (hB : B.det = 1)
    (X : Matrix (Fin 2) (Fin 2) ℝ) : (A * X * B).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, hA, hB]; ring

/-- Helper: solving the entrywise conditions for $P = A^{\mathsf T}A$, $Q = BB^{\mathsf T}$ from the trace identity. -/
private lemma trace_aux (P0 P1 P2 Q0 Q1 Q2 : ℝ)
    (h1 : P0 * Q0 = 1) (h2 : P0 * Q2 = 1) (h3 : P2 * Q0 = 1) (h4 : P2 * Q2 = 1)
    (h5 : P0 * Q0 + 2 * (P1 * Q1) + P2 * Q2 = 2)
    (h6 : P0 * (Q0 + 2 * Q1 + Q2) = 2)
    (h7 : (P0 + 2 * P1 + P2) * Q0 = 2)
    (hP0 : 0 < P0) (hdet : P0 * P2 - P1 ^ 2 = 1) :
    P0 = 1 ∧ P1 = 0 ∧ P2 = 1 ∧ Q0 = 1 ∧ Q1 = 0 ∧ Q2 = 1 := by
  have hQ1 : Q1 = 0 := by
    have : P0 * Q1 = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hQ0 : Q0 ≠ 0 := by intro h; rw [h] at h1; simp at h1
  have hP1 : P1 = 0 := by
    have : P1 * Q0 = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hQ0
  have hP2 : P2 = P0 := by
    apply mul_right_cancel₀ hQ0; rw [h3, h1]
  have hQ2 : Q2 = Q0 := by
    apply mul_left_cancel₀ hP0.ne'; rw [h2, h1]
  subst hP1 hP2
  have : P2 = 1 := by nlinarith
  subst this
  refine ⟨rfl, rfl, rfl, ?_, hQ1, ?_⟩ <;> linarith

/-- Helper: positivity of $a^2 + c^2$ when $ad - bc = 1$. -/
private lemma pos_aux {a b c d : ℝ} (hA : a * d - b * c = 1) : 0 < a ^ 2 + c ^ 2 := by
  by_contra hn
  have ha : a ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg c]) (sq_nonneg a)
  have hc : c ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg c)
  have ha' := pow_eq_zero_iff (two_ne_zero) |>.mp ha
  have hc' := pow_eq_zero_iff (two_ne_zero) |>.mp hc
  rw [ha', hc'] at hA; simp at hA

/-- **The compact subgroup $K$** (Cassels, Ch. 13, §9, (9.14)–(9.18), pp. 318–319): for real $2 \times 2$ matrices
with $\det A = \det B = 1$, the automorph $X \mapsto AXB$ preserves $\operatorname{tr} X^{\mathsf T}X$ for all $X$ iff
$A^{\mathsf T}A = BB^{\mathsf T} = I$ (Cassels: the condition (9.16) is sufficient, "and also necessary"). -/
@[kb "cassels1978" "Ch. 13, §9, (9.14)–(9.18), pp. 318–319"]
theorem trace_preserved_iff {A B : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) (hB : B.det = 1) :
    (∀ X : Matrix (Fin 2) (Fin 2) ℝ, ((A * X * B)ᵀ * (A * X * B)).trace = (Xᵀ * X).trace) ↔
      Aᵀ * A = 1 ∧ B * Bᵀ = 1 := by
  constructor
  · intro h
    rw [Matrix.eta_fin_two A, Matrix.eta_fin_two B] at *
    rw [Matrix.det_fin_two_of] at hA hB
    set a := A 0 0; set b := A 0 1; set c := A 1 0; set d := A 1 1
    set p := B 0 0; set q := B 0 1; set r := B 1 0; set s := B 1 1
    have s1 := h !![1, 0; 0, 0]
    have s2 := h !![0, 0; 0, 1]
    have s3 := h !![0, 1; 0, 0]
    have s4 := h !![0, 0; 1, 0]
    have s5 := h !![1, 0; 0, 1]
    have s6 := h !![1, 1; 0, 0]
    have s7 := h !![1, 0; 1, 0]
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at s1 s2 s3 s4 s5 s6 s7
    have key := trace_aux (a^2+c^2) (a*b+c*d) (b^2+d^2) (p^2+q^2) (p*r+q*s) (r^2+s^2)
      (by linear_combination s1) (by linear_combination s3) (by linear_combination s4)
      (by linear_combination s2) (by linear_combination s5) (by linear_combination s6)
      (by linear_combination s7) (pos_aux hA) (by linear_combination (a*d-b*c+1) * hA)
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := key
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
  · rintro ⟨h1, h2⟩ X
    have : (A*X*B)ᵀ * (A*X*B) = Bᵀ * (Xᵀ * (Aᵀ*A) * X) * B := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, h1, mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2,
      Matrix.one_mul]

end QuadFormsKB.Reduction
