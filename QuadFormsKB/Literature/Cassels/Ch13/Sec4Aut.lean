import Mathlib
import QuadFormsKB.Citation

/-!
# Cassels, Chapter 13, §4: automorphs fixing a vector (Theorem 4.1)

Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §4, p. 299.

**Setting.** $f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ with $F$ a symmetric integral $(m+1)\times(m+1)$ matrix
(`qv`), $L(\vec{x}) = (F\vec{x})_0$ (`linL`), and the complementary form $g$ of (4.4) (`complForm`) with
$f_{00}f = L^{2} + g$. The display (4.4) is lost in the machine-read text; this is the completion of the square it
describes.

**What is proved.** Theorem 4.1, first and last statements: an integral automorph fixing $\vec{e}_0$ induces an
automorph of $g$ (`thm_4_1`), and every automorph $S \equiv I \bmod f_{00}$ of $g$ is induced (`thm_4_1_ext`). The
middle statement (the induced $S$ form a subgroup of finite index of $O(g)$) follows from these and the finite index
of congruence subgroups (`Ch13/Sec4.lean`) but is not stated separately.

**Conventions.** 0-based indices: Cassels' $e_1$, $f_{11}$ are $\vec{e}_0$, $f_{00}$ here. Automorphs are integral
matrices $T$ with $T^{\mathsf T}FT = F$ (unimodularity is not needed for these statements).
-/

open Matrix

namespace QuadFormsKB.Cassels.Ch13

variable {m : ℕ}

/-- The value $f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ of the form with integral matrix $F$ on $\mathbb Z^{m+1}$. -/
def qv (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (x : Fin (m + 1) → ℤ) : ℤ := x ⬝ᵥ (F *ᵥ x)

/-- The linear form $L(\vec{x}) = (F\vec{x})_0 = f_{00}x_0 + f_{01}x_1 + \cdots + f_{0m}x_m$. -/
def linL (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (x : Fin (m + 1) → ℤ) : ℤ := (F *ᵥ x) 0

/-- The complementary form $g(\vec{y}) = f_{00}\,f(0,\vec{y}) - L(0,\vec{y})^{2}$ in the variables $\vec{y} = (x_1,\dots,x_m)$, so that $f_{00}f(\vec{x}) = L(\vec{x})^{2} + g(x_1,\dots,x_m)$ (Cassels (4.4), "completing the square"); it is integral-valued. -/
@[kb "cassels1978" "Ch. 13, §4, (4.4), p. 299"]
def complForm (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (y : Fin m → ℤ) : ℤ :=
  F 0 0 * qv F (Fin.cons 0 y) - linL F (Fin.cons 0 y) ^ 2

/-- $f(c,\vec{y}) = f_{00}c^{2} + 2cL(0,\vec{y}) + f(0,\vec{y})$ for symmetric $F$. -/
theorem qv_cons (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hF : Fᵀ = F) (c : ℤ) (y : Fin m → ℤ) :
    qv F (Fin.cons c y) = F 0 0 * c ^ 2 + 2 * c * linL F (Fin.cons 0 y) + qv F (Fin.cons 0 y) := by
  have hx : (Fin.cons c y : Fin (m + 1) → ℤ) = c • Pi.single 0 1 + Fin.cons 0 y := by
    ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hsym : ∀ u v : Fin (m + 1) → ℤ, u ⬝ᵥ (F *ᵥ v) = v ⬝ᵥ (F *ᵥ u) := by
    intro u v
    rw [dotProduct_mulVec, ← mulVec_transpose, hF, dotProduct_comm]
  have he : ∀ v : Fin (m + 1) → ℤ, Pi.single 0 1 ⬝ᵥ v = v 0 := by
    intro v; simp [dotProduct, Pi.single_apply]
  have h00 : (F *ᵥ Pi.single 0 1) 0 = F 0 0 := by simp [mulVec, dotProduct, Pi.single_apply]
  rw [hx]
  simp only [qv, linL, mulVec_add, dotProduct_add, add_dotProduct, mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [hsym (Fin.cons 0 y) (Pi.single 0 1), he, he, h00]
  ring

/-- $L(c,\vec{y}) = f_{00}c + L(0,\vec{y})$. -/
theorem linL_cons (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (c : ℤ) (y : Fin m → ℤ) :
    linL F (Fin.cons c y) = F 0 0 * c + linL F (Fin.cons 0 y) := by
  simp [linL, mulVec, dotProduct, Fin.sum_univ_succ]


/-- Completing the square (4.4): $f_{00}f(\vec{x}) = L(\vec{x})^{2} + g(x_1,\dots,x_m)$. -/
theorem complete_square (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hF : Fᵀ = F) (x : Fin (m + 1) → ℤ) :
    F 0 0 * qv F x = linL F x ^ 2 + complForm F (Fin.tail x) := by
  obtain ⟨c, y, rfl⟩ : ∃ c y, x = Fin.cons c y := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
  rw [qv_cons F hF, linL_cons F c y, Fin.tail_cons]
  unfold complForm; ring

/-- $(T\vec{u})\cdot\vec{w} = \vec{u}\cdot(T^{\mathsf T}\vec{w})$. -/
theorem dot_mulVec_eq (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (u w : Fin (m + 1) → ℤ) :
    (T *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Tᵀ *ᵥ w) := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- An automorph ($T^{\mathsf T}FT = F$) preserves the bilinear form $\vec{u}^{\mathsf T}F\vec{v}$. -/
theorem aut_pol {F T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hT : Tᵀ * F * T = F) (u v : Fin (m + 1) → ℤ) :
    (T *ᵥ u) ⬝ᵥ (F *ᵥ (T *ᵥ v)) = u ⬝ᵥ (F *ᵥ v) := by
  rw [dot_mulVec_eq, mulVec_mulVec, mulVec_mulVec, hT]

/-- The lower right block of $T$ acts on $\vec{y}$ as $T$ acts on $(0,\vec{y})$, followed by dropping the first coordinate. -/
theorem submatrix_mulVec (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (y : Fin m → ℤ) :
    T.submatrix Fin.succ Fin.succ *ᵥ y = Fin.tail (T *ᵥ Fin.cons 0 y) := by
  ext i; simp [mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]

/-- **Theorem 4.1**, first statement: if $T$ is an integral automorph of $f$ ($T^{\mathsf T}FT = F$, $F$ symmetric integral) fixing $\vec{e}_0$ (4.3), then its lower right $m\times m$ block $S$ (4.5) is an automorph of the complementary form $g$ of (4.4): $g(S\vec{y}) = g(\vec{y})$. -/
@[kb "cassels1978" "Ch. 13, §4, Thm. 4.1, p. 299 (T induces S ∈ O(g))"]
theorem thm_4_1 (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hF : Fᵀ = F)
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hT : Tᵀ * F * T = F) (h0 : T *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    ∀ y, complForm F (T.submatrix Fin.succ Fin.succ *ᵥ y) = complForm F y := by
  intro y
  set z : Fin (m + 1) → ℤ := Fin.cons 0 y
  have hq : qv F (T *ᵥ z) = qv F z := aut_pol hT z z
  have hL : linL F (T *ᵥ z) = linL F z := by
    have he : ∀ v : Fin (m + 1) → ℤ, (F *ᵥ v) 0 = Pi.single 0 1 ⬝ᵥ (F *ᵥ v) := by
      intro v; simp [dotProduct, Pi.single_apply]
    simp only [linL]
    rw [he, he]
    calc Pi.single 0 1 ⬝ᵥ (F *ᵥ (T *ᵥ z)) = (T *ᵥ Pi.single 0 1) ⬝ᵥ (F *ᵥ (T *ᵥ z)) := by rw [h0]
      _ = _ := aut_pol hT _ _
  rw [submatrix_mulVec]
  have h1 := complete_square F hF (T *ᵥ z)
  have h2 := complete_square F hF z
  have hz : Fin.tail z = y := Fin.tail_cons _ _
  rw [hz] at h2
  rw [hq, hL] at h1
  linarith


/-- $L(0,\vec{y}) = \sum_i f_{0,i+1}y_i$. -/
theorem linL_cons_zero (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (y : Fin m → ℤ) :
    linL F (Fin.cons 0 y) = ∑ i, F 0 i.succ * y i := by
  simp [linL, mulVec, dotProduct, Fin.sum_univ_succ]

/-- The matrix $\begin{pmatrix}1&\vec{t}^{\mathsf T}\\0&S\end{pmatrix}$ of shape (4.5). -/
def extMat (t : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 t j) (fun i' => Fin.cases 0 (fun j' => S i' j') j) i

/-- $\begin{pmatrix}1&\vec{t}^{\mathsf T}\\0&S\end{pmatrix}(c,\vec{y}) = (c + \vec{t}\cdot\vec{y},\ S\vec{y})$. -/
theorem extMat_mulVec (t : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) (c : ℤ) (y : Fin m → ℤ) :
    extMat t S *ᵥ Fin.cons c y = Fin.cons (c + t ⬝ᵥ y) (S *ᵥ y) := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [extMat, mulVec, dotProduct, Fin.sum_univ_succ]

/-- **Theorem 4.1**, last statement: if $f_{00} \ne 0$ and $S$ is an automorph of $g$ with $S \equiv I \bmod f_{00}$, then $S$ extends to an integral automorph $T = \begin{pmatrix}1&\vec{t}^{\mathsf T}\\0&S\end{pmatrix}$ of $f$ fixing $\vec{e}_0$; so the induced $S$ include all $S \equiv I \bmod f_{00}$. -/
@[kb "cassels1978" "Ch. 13, §4, Thm. 4.1, p. 299 (all S ≡ I mod f_11 occur)"]
theorem thm_4_1_ext (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hF : Fᵀ = F) (ha : F 0 0 ≠ 0)
    (S X : Matrix (Fin m) (Fin m) ℤ) (hSX : S = 1 + F 0 0 • X)
    (hS : ∀ y, complForm F (S *ᵥ y) = complForm F y) :
    ∃ T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ, T *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      T.submatrix Fin.succ Fin.succ = S ∧ ∀ x, qv F (T *ᵥ x) = qv F x := by
  set t : Fin m → ℤ := fun j => -∑ i, F 0 i.succ * X i j
  refine ⟨extMat t S, ?_, ?_, fun x => ?_⟩
  · have : (Pi.single 0 1 : Fin (m + 1) → ℤ) = Fin.cons 1 0 := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [this, extMat_mulVec]; simp
  · ext i j; simp [extMat]
  · obtain ⟨c, y, rfl⟩ : ∃ c y, x = Fin.cons c y := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have key : t ⬝ᵥ y = -∑ i, F 0 i.succ * (X *ᵥ y) i := by
      simp only [t, dotProduct, mulVec, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]; congr 1; apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    have hSy : S *ᵥ y = y + F 0 0 • (X *ᵥ y) := by
      rw [hSX, add_mulVec, one_mulVec, smul_mulVec]
    have hL : linL F (extMat t S *ᵥ Fin.cons c y) = linL F (Fin.cons c y) := by
      rw [extMat_mulVec, linL_cons, linL_cons F c y, linL_cons_zero, linL_cons_zero, key, hSy]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      have : ∑ i, F 0 i.succ * (F 0 0 * (X *ᵥ y) i) = F 0 0 * ∑ i, F 0 i.succ * (X *ᵥ y) i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [this]; ring
    have h1 := complete_square F hF (extMat t S *ᵥ Fin.cons c y)
    have h2 := complete_square F hF (Fin.cons c y)
    rw [hL, extMat_mulVec, Fin.tail_cons, hS] at h1
    rw [Fin.tail_cons] at h2
    rw [extMat_mulVec]
    exact mul_left_cancel₀ ha (by linarith)

end QuadFormsKB.Cassels.Ch13
