/-
# Cassels, Chapter 12: real forms as symmetric matrices, integral unimodular substitutions, extension to a basis

Foundations for the formalization of Cassels, *Rational Quadratic Forms* (1978), Chapter 12, *The reduction of
positive definite quadratic forms* (pp. 255–283).

**Forms as matrices.** Chapter 12 works with real forms
$$f(\vec{x}) = \sum_{i,j} f_{ij}\, x_i x_j, \qquad f_{ij} = f_{ji} \in \mathbb{R}$$
(Ch. 12, (1.1), p. 255), identified with the point $(f_{ij})_{i \le j}$ of $\mathbb{R}^{n(n+1)/2}$ (§5, p. 269). Here a real
form is given by its symmetric matrix $F = (f_{ij}) \in M_n(\mathbb{R})$ (Cassels' $F$, Ch. 1, (2.7), p. 6), and
$f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ (`val`). The library's primary definition (`QuadForm`, upper-triangular
coefficients $c_{ij}$) is related by $F = \tfrac12 H$, $H$ the Hessian (`QuadForm.evalIn_real_eq_val`); the matrix
description is used because Chapter 12 is about the cone of matrices $F$ (Sections 5–7). Strict positive definiteness
("strictly positive definite", p. 255) is Mathlib's `Matrix.PosDef`; Cassels' "positive definite" in the wide sense,
which includes the semi-definite forms (p. 260), is Mathlib's `Matrix.PosSemidef`.

**Indices are 0-based** (`Fin n`): Cassels' variables $x_1, \dots, x_n$ and basis vectors $e_1, \dots, e_n$ are
$x_0, \dots, x_{n-1}$ and $e_0, \dots, e_{n-1}$ here, so his condition "for each $j$, $e^*$ extends $e_1, \dots, e_{j-1}$" is
"for each $j$, $e^*$ extends $e_0, \dots, e_{j-1}$" with $j = 0, \dots, n-1$.

**Substitutions.** An integral unimodular matrix $T$ ($T \in \mathrm{GL}_n(\mathbb{Z})$, i.e. $\det T = \pm 1$, Cassels'
$SL_n^{\pm}(\mathbb{Z})$, p. 257) acts by $f \mapsto f(T\vec{x})$, i.e. $F \mapsto T^{\mathsf T}FT$ (`act`).

**Extension to a basis** (Ch. 12, p. 255). An integral vector $\vec{e}^{\,*}$ *extends* $e_0, \dots, e_{j-1}$
(`ExtendsBasis j e`) if $e_0, \dots, e_{j-1}, \vec{e}^{\,*}$ can be completed to a basis of $\mathbb{Z}^n$; equivalently
(Cassels (1.3)–(1.4)) the coordinates $b_j, \dots, b_{n-1}$ of $\vec{e}^{\,*}$ have greatest common divisor $1$
(`extendsBasis_iff_gcd`).
-/
import QuadFormsKB.Defs.QuadForm

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **The value of a real form given by its matrix:** for $F \in M_n(\mathbb{R})$ and $\vec{x} \in \mathbb{R}^n$,
$$f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x} = \sum_{i,j} f_{ij}\,x_i x_j.$$
Cassels, Ch. 12, (1.1), p. 255 (with $F$ symmetric; the definition makes sense for every matrix, and only the
symmetric part of $F$ matters). Over $\mathbb{R}$; the vector $\vec{x}$ is real. For an integral vector
$\vec{m} \in \mathbb{Z}^n$ the value is `val F (cast m)`. Corresponds to Mathlib's `Matrix.toQuadraticMap'` (not used). -/
@[kb "cassels1978" "Ch. 12, §1, (1.1), p. 255"]
def val (F : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (F *ᵥ x)

/-- **An integral vector as a real vector:** $\vec{m} \in \mathbb{Z}^n \mapsto (m_0, \dots, m_{n-1}) \in \mathbb{R}^n$. -/
abbrev cast (m : Fin n → ℤ) : Fin n → ℝ := fun i => (m i : ℝ)

/-- **An integral matrix as a real matrix:** $T \in M_n(\mathbb{Z}) \mapsto T \in M_n(\mathbb{R})$ (entrywise cast). -/
abbrev castM (T : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ := T.map (Int.cast : ℤ → ℝ)

/-- **The substituted form $f(T\vec{x})$:** for $T \in M_n(\mathbb{Z})$ and a real form with matrix $F$, the form
$\vec{x} \mapsto f(T\vec{x})$ has matrix $T^{\mathsf T}FT$ (`val_act`). Cassels writes it $Tf$ (Ch. 12, p. 257; §6,
p. 275). For $T \in \mathrm{GL}_n(\mathbb{Z})$ the two forms are integrally equivalent (Ch. 12, Thm. 1.1, p. 256). -/
@[kb "cassels1978" "Ch. 12, §1, p. 257 (SL^±_n(ℤ) acts by Tf(x) = f(Tx)); §6, p. 275"]
def act (T : Matrix (Fin n) (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (castM T)ᵀ * F * castM T

/-- $f(T\vec{x}) = (T^{\mathsf T}FT)(\vec{x})$. -/
theorem val_act (T : Matrix (Fin n) (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    val (act T F) x = val F (castM T *ᵥ x) := by
  unfold val act
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- Casting commutes with matrix-vector multiplication: $T\vec{m}$ computed in $\mathbb{Z}^n$ or in $\mathbb{R}^n$. -/
theorem castM_mulVec_cast (T : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ) :
    castM T *ᵥ cast m = cast (T *ᵥ m) := by
  ext i
  simp [Matrix.mulVec, dotProduct, castM, cast]

/-- The entrywise cast is multiplicative: $\mathrm{castM}(ST) = \mathrm{castM}(S)\,\mathrm{castM}(T)$. -/
theorem castM_mul (S T : Matrix (Fin n) (Fin n) ℤ) : castM (S * T) = castM S * castM T := by
  ext i j
  simp [castM, Matrix.mul_apply]

/-- The entrywise cast of the identity is the identity. -/
theorem castM_one : castM (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
  ext i j
  simp [castM, Matrix.one_apply]

/-- $\mathrm{castM}(T^{-1})$ acting on $\mathbb{R}^n$ is injective for $T \in \mathrm{GL}_n(\mathbb{Z})$. -/
theorem injective_castM_inv (T : GL (Fin n) ℤ) :
    Function.Injective (Matrix.mulVecLin (castM (T⁻¹ : GL (Fin n) ℤ).val)) := by
  intro x y hxy
  have := congrArg (fun z => castM T.val *ᵥ z) hxy
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← castM_mul, Units.mul_inv, castM_one,
    Matrix.one_mulVec] at this
  exact this

/-- Substituting $S$ and then $T$: $f(S(T\vec{x}))$, i.e. $(ST)^{\mathsf T}F(ST) = T^{\mathsf T}(S^{\mathsf T}FS)T$. -/
theorem act_mul (S T : Matrix (Fin n) (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) :
    act (S * T) F = act T (act S F) := by
  unfold act
  rw [castM_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem act_one (F : Matrix (Fin n) (Fin n) ℝ) : act 1 F = F := by
  unfold act
  rw [castM_one]
  simp

/-- The diagonal entry $f_{jj} = f(e_j)$. -/
theorem val_single (F : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    val F (Pi.single j 1) = F j j := by
  simp [val]

/-- Casting a standard basis vector: $\mathrm{cast}(e_j) = e_j$. -/
theorem cast_single (j : Fin n) :
    cast (Pi.single j 1 : Fin n → ℤ) = (Pi.single j 1 : Fin n → ℝ) := by
  funext k
  by_cases h : k = j <;> simp [h]

/-- The diagonal entry of a substituted form, $(U^{\mathsf T}GU)_{jj} = g(Ue_j)$. -/
theorem act_diag (U : Matrix (Fin n) (Fin n) ℤ) (G : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    act U G j j = val G (cast (U *ᵥ Pi.single j 1)) := by
  calc act U G j j = val (act U G) (Pi.single j 1) := (val_single _ _).symm
    _ = _ := by rw [val_act, ← cast_single, castM_mulVec_cast]

/-- A matrix fixing column $i$ sends $e_i$ to $e_i$. -/
theorem mulVec_single_of_col (U : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    (h : ∀ k, U k i = (Pi.single i 1 : Fin n → ℤ) k) : U *ᵥ Pi.single i 1 = Pi.single i 1 := by
  funext k
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, h k]

/-- Column $j$ of a matrix is its product with $e_j$. -/
theorem mulVec_single_apply (T : Matrix (Fin n) (Fin n) ℤ) (j a : Fin n) :
    (T *ᵥ Pi.single j 1) a = T a j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The value of the substituted form at an integral vector: $f(T\vec{m})$ computed over $\mathbb{Z}$. -/
theorem val_act_cast (T : Matrix (Fin n) (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℤ) :
    val (act T F) (cast m) = val F (cast (T *ᵥ m)) := by
  rw [val_act, castM_mulVec_cast]

/-- $f(P^{\mathsf T}FP)(\vec{y}) = f(P\vec{y})$ for a real matrix $P$. -/
theorem val_conj (P F : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    val (Pᵀ * F * P) y = val F (P *ᵥ y) := by
  unfold val
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- A unimodular substitution does not change the determinant: $\det(T^{\mathsf T}FT) = \det F$. -/
theorem det_act (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) : (act T.val F).det = F.det := by
  have hu : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit
  have hd : (castM T.val).det = ((T.val.det : ℤ) : ℝ) := by
    have := (Int.castRingHom ℝ).map_det T.val
    simpa [castM, RingHom.mapMatrix_apply] using this.symm
  have hsq : ((T.val.det : ℤ) : ℝ) * ((T.val.det : ℤ) : ℝ) = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h <;> rw [h] <;> norm_num
  unfold act
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd]
  calc _ = (((T.val.det : ℤ) : ℝ) * ((T.val.det : ℤ) : ℝ)) * F.det := by ring
    _ = F.det := by rw [hsq, one_mul]

/-- **Strict positive definiteness in Cassels' terms:** $F$ is Mathlib-`PosDef` iff $F$ is symmetric and
$f(\vec{x}) > 0$ for every nonzero real $\vec{x}$. -/
theorem posDef_iff (F : Matrix (Fin n) (Fin n) ℝ) :
    F.PosDef ↔ F.IsSymm ∧ ∀ x : Fin n → ℝ, x ≠ 0 → 0 < val F x := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have : F.IsHermitian ↔ F.IsSymm := by
    simp [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [this]
  simp [val]

/-- **Positive semi-definiteness in Cassels' terms** (his "positive definite" in the wide sense, p. 260). -/
theorem posSemidef_iff (F : Matrix (Fin n) (Fin n) ℝ) :
    F.PosSemidef ↔ F.IsSymm ∧ ∀ x : Fin n → ℝ, 0 ≤ val F x := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have : F.IsHermitian ↔ F.IsSymm := by
    simp [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [this]
  simp [val]

/-- $f(c\vec{x}) = c^2 f(\vec{x})$. -/
theorem val_smul (F : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    val F (c • x) = c ^ 2 * val F x := by
  simp [val, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  ring

/-- An integral unimodular substitution preserves strict positive definiteness. -/
theorem PosDef.act {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (T : GL (Fin n) ℤ) :
    (act T.val F).PosDef := by
  obtain ⟨hs, hp⟩ := (posDef_iff F).1 hF
  rw [posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · have hs' : Fᵀ = F := hs
    show (QuadFormsKB.Reduction.act T.val F)ᵀ = QuadFormsKB.Reduction.act T.val F
    unfold QuadFormsKB.Reduction.act
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hs', Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [val_act]
    apply hp
    intro h
    apply hx
    have h1 : castM T⁻¹.val * castM T.val = 1 := by
      rw [← castM_mul, Units.inv_mul, castM_one]
    calc x = (castM T⁻¹.val * castM T.val) *ᵥ x := by rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h]; simp

/-- **$\vec{e}^{\,*}$ extends $e_0, \dots, e_{j-1}$ to a basis of $\mathbb{Z}^n$** (Cassels, Ch. 12, p. 255, the condition
on $e^*$ in the definition of reduction, 0-based): there is $T \in \mathrm{GL}_n(\mathbb{Z})$ whose columns
$0, \dots, j-1$ are the standard basis vectors $e_0, \dots, e_{j-1}$ and whose column $j$ is $\vec{e}^{\,*}$ (the columns of
$T$ are then a basis $e_0, \dots, e_{j-1}, \vec{e}^{\,*}, e^*_{j+1}, \dots$ of $\mathbb{Z}^n$). For $j = 0$ this says only that
$\vec{e}^{\,*}$ is primitive (Cassels' parenthesis, p. 255). Equivalent to $\gcd(b_j, \dots, b_{n-1}) = 1$
(`extendsBasis_iff_gcd`). -/
@[kb "cassels1978" "Ch. 12, §1, Definition, p. 255 (e* extends e_1, …, e_{j−1} to a basis)"]
def ExtendsBasis (j : Fin n) (e : Fin n → ℤ) : Prop :=
  ∃ T : GL (Fin n) ℤ, (∀ i < j, ∀ k, T.val k i = (Pi.single i 1 : Fin n → ℤ) k) ∧ ∀ k, T.val k j = e k

/-- $e_j$ itself extends $e_0, \dots, e_{j-1}$ (take $T = 1$). -/
theorem extendsBasis_single (j : Fin n) : ExtendsBasis j (Pi.single j 1) := by
  refine ⟨1, fun i _ k => ?_, fun k => ?_⟩
  · simp [Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.one_apply, Pi.single_apply]

/-- **Transport by a substitution fixing $e_0, \dots, e_{j-1}$:** if $U \in \mathrm{GL}_n(\mathbb{Z})$ has columns
$0, \dots, j-1$ equal to $e_0, \dots, e_{j-1}$, then $U$ maps vectors extending $e_0, \dots, e_{j-1}$ to such vectors. -/
theorem ExtendsBasis.mulVec {j : Fin n} {e : Fin n → ℤ} (he : ExtendsBasis j e) (U : GL (Fin n) ℤ)
    (hU : ∀ i < j, ∀ k, U.val k i = (Pi.single i 1 : Fin n → ℤ) k) : ExtendsBasis j (U.val *ᵥ e) := by
  obtain ⟨T, h1, h2⟩ := he
  refine ⟨U * T, fun i hi k => ?_, fun k => ?_⟩
  · simp only [Units.val_mul, Matrix.mul_apply, h1 i hi]
    simp [Pi.single_apply, hU i hi k]
  · simp only [Units.val_mul, Matrix.mul_apply, h2, Matrix.mulVec, dotProduct]

/-- **The greatest common divisor of the coordinates $b_j, \dots, b_{n-1}$** of an integral vector $\vec{b}$
(Mathlib's normalized `Finset.gcd` in $\mathbb{Z}$, so $\ge 0$; it is $0$ iff these coordinates all vanish, e.g. for
every $\vec{b}$ when $j$ would be $n$). -/
def tailGcd (j : Fin n) (b : Fin n → ℤ) : ℤ := (Finset.univ.filter fun k => j ≤ k).gcd b

/-- Helper: `tailGcd` is nonnegative. -/
private theorem tailGcd_nonneg (j : Fin n) (b : Fin n → ℤ) : 0 ≤ tailGcd j b :=
  Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)

/-- Helper: a tail index lies in the index set of `tailGcd`. -/
private theorem mem_tail {j k : Fin n} (h : j ≤ k) : k ∈ Finset.univ.filter fun k : Fin n => j ≤ k :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩

/-- Helper: `tailGcd` divides every tail coordinate. -/
private theorem tailGcd_dvd (j : Fin n) (b : Fin n → ℤ) {k : Fin n} (h : j ≤ k) : tailGcd j b ∣ b k :=
  Finset.gcd_dvd (mem_tail h)

/-- Helper: if a matrix with unit determinant fixes the columns `< j`, then extension of `M e`
implies extension of `e`. -/
private theorem ExtendsBasis.of_mulVec_mat {j : Fin n} {e : Fin n → ℤ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : IsUnit M.det) (hfix : ∀ i < j, ∀ k, M k i = (Pi.single i 1 : Fin n → ℤ) k)
    (h : ExtendsBasis j (M *ᵥ e)) : ExtendsBasis j e := by
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hM
  subst hU
  have hinv : ∀ i < j, ∀ k, (U⁻¹).val k i = (Pi.single i 1 : Fin n → ℤ) k := by
    intro i hi k
    have h1 := congrFun (congrFun (Units.inv_mul U) k) i
    simp only [Matrix.mul_apply, hfix i hi] at h1
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1
  have := h.mulVec U⁻¹ hinv
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

/-- Helper: coordinates of a transvection applied to a vector. -/
private theorem transvection_mulVec_apply (k l : Fin n) (c : ℤ) (v : Fin n → ℤ) (t : Fin n) :
    (Matrix.transvection k l c *ᵥ v) t = v t + (if t = k then c * v l else 0) := by
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]

/-- Helper: a transvection `1 + c E_{kl}` with `l ≥ j` fixes the columns `< j`. -/
private theorem transvection_fix {j : Fin n} (k l : Fin n) (c : ℤ) (hl : j ≤ l) :
    ∀ i < j, ∀ t, Matrix.transvection k l c t i = (Pi.single i 1 : Fin n → ℤ) t := by
  intro i hi t
  have : i ≠ l := ne_of_lt (lt_of_lt_of_le hi hl)
  simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Pi.single_apply, this,
    this.symm, eq_comm]

/-- Helper: extension is reflected by transvections `1 + c E_{kl}` with `l ≥ j`, `k ≠ l`. -/
private theorem ExtendsBasis.of_transvection {j : Fin n} {k l : Fin n} {c : ℤ} {e : Fin n → ℤ}
    (hkl : k ≠ l) (hl : j ≤ l) (h : ExtendsBasis j (Matrix.transvection k l c *ᵥ e)) :
    ExtendsBasis j e :=
  ExtendsBasis.of_mulVec_mat _ (by rw [Matrix.det_transvection_of_ne _ _ hkl]; exact isUnit_one)
    (transvection_fix k l c hl) h

/-- Helper: a transvection with `l ≥ j` does not enlarge the tail gcd. -/
private theorem tailGcd_transvection_dvd {j : Fin n} {k l : Fin n} (c : ℤ) (v : Fin n → ℤ)
    (hkl : k ≠ l) (hl : j ≤ l) :
    tailGcd j (Matrix.transvection k l c *ᵥ v) ∣ tailGcd j v := by
  apply Finset.dvd_gcd
  intro t ht
  have ht' : j ≤ t := (Finset.mem_filter.1 ht).2
  set w := Matrix.transvection k l c *ᵥ v with hw
  have hwl : w l = v l := by
    rw [hw, transvection_mulVec_apply, if_neg (Ne.symm hkl), add_zero]
  by_cases htk : t = k
  · have : v t = w t - c * w l := by
      rw [hwl, hw, transvection_mulVec_apply, if_pos htk]; ring
    rw [this]
    exact dvd_sub (tailGcd_dvd j w ht') (dvd_mul_of_dvd_right (tailGcd_dvd j w hl) c)
  · have : v t = w t := by
      rw [hw, transvection_mulVec_apply, if_neg htk, add_zero]
    rw [this]
    exact tailGcd_dvd j w ht'

/-- Helper: a vector whose `j`-th coordinate is `±1` extends `e_0, …, e_{j-1}`. -/
private theorem extendsBasis_of_unit {j : Fin n} {v : Fin n → ℤ} (h : v j = 1 ∨ v j = -1) :
    ExtendsBasis j v := by
  set c : Fin n → ℤ := v - Pi.single j 1 with hc
  set M : Matrix (Fin n) (Fin n) ℤ :=
    1 + Matrix.replicateCol Unit c * Matrix.replicateRow Unit (Pi.single j 1 : Fin n → ℤ) with hM
  have hent : ∀ k i, M k i = (1 : Matrix (Fin n) (Fin n) ℤ) k i + c k * (Pi.single j 1 : Fin n → ℤ) i := by
    intro k i
    simp only [hM, Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]
  have hdet : M.det = v j := by
    rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [hc]
  have hu : IsUnit M.det := by
    rw [hdet]; rcases h with h | h <;> rw [h] <;> simp
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hu
  refine ⟨U, fun i hi k => ?_, fun k => ?_⟩
  · rw [hU, hent]
    have : i ≠ j := ne_of_lt hi
    simp [Matrix.one_apply, Pi.single_apply, this, eq_comm]
  · rw [hU, hent]
    simp [Matrix.one_apply, Pi.single_apply, hc, eq_comm]

/-- Helper: the sum of absolute values of the tail coordinates (the Euclid measure). -/
private def tailNorm (j : Fin n) (v : Fin n → ℤ) : ℕ :=
  ∑ k ∈ Finset.univ.filter fun k => j ≤ k, (v k).natAbs

/-- Helper: Euclid's algorithm. -/
private theorem extendsBasis_of_gcd_aux (j : Fin n) :
    ∀ (N : ℕ) (v : Fin n → ℤ), tailNorm j v = N → tailGcd j v = 1 → ExtendsBasis j v := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro v hN hg
  have key : ∀ l m : Fin n, l ≠ m → j ≤ l → j ≤ m → v m ≠ 0 →
      (v m).natAbs ≤ (v l).natAbs → ExtendsBasis j v := by
    intro l m hlm hl hm hvm hle
    set w := Matrix.transvection l m (-(v l / v m)) *ᵥ v with hw
    have hwt : ∀ t, t ≠ l → w t = v t := by
      intro t ht
      rw [hw, transvection_mulVec_apply, if_neg ht, add_zero]
    have hwl : w l = v l % v m := by
      rw [hw, transvection_mulVec_apply, if_pos rfl, Int.emod_def]; ring
    have hlt : (w l).natAbs < (v l).natAbs := by
      rw [hwl]
      have h1 : 0 ≤ v l % v m := Int.emod_nonneg _ hvm
      have h2 : v l % v m < ((v m).natAbs : ℤ) := Int.emod_lt _ hvm
      have h4 : ((v m).natAbs : ℤ) ≤ ((v l).natAbs : ℤ) := by exact_mod_cast hle
      omega
    have hless : tailNorm j w < tailNorm j v := by
      apply Finset.sum_lt_sum
      · intro t _
        by_cases htl : t = l
        · subst htl; exact hlt.le
        · rw [hwt t htl]
      · exact ⟨l, mem_tail hl, hlt⟩
    have hgw : tailGcd j w = 1 :=
      Int.eq_one_of_dvd_one (tailGcd_nonneg j w)
        (hg ▸ tailGcd_transvection_dvd (j := j) (k := l) (l := m) (-(v l / v m)) v hlm hm)
    exact ExtendsBasis.of_transvection hlm hm (ih _ (hN ▸ hless) w rfl hgw)
  by_cases h2 : ∃ l m, l ≠ m ∧ j ≤ l ∧ j ≤ m ∧ v l ≠ 0 ∧ v m ≠ 0
  · obtain ⟨l, m, hlm, hl, hm, hvl, hvm⟩ := h2
    rcases le_total (v m).natAbs (v l).natAbs with h | h
    · exact key l m hlm hl hm hvm h
    · exact key m l hlm.symm hm hl hvl h
  · push_neg at h2
    have hex : ∃ l, j ≤ l ∧ v l ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have : tailGcd j v = 0 :=
        Finset.gcd_eq_zero_iff.2 (fun k hk => hcon k (Finset.mem_filter.1 hk).2)
      rw [hg] at this
      exact one_ne_zero this
    obtain ⟨l, hl, hvl⟩ := hex
    have hzero : ∀ t, j ≤ t → t ≠ l → v t = 0 := by
      intro t ht htl
      by_contra hne
      exact hvl (h2 t l htl ht hl hne)
    have hunit : v l = 1 ∨ v l = -1 := by
      have hd : v l ∣ tailGcd j v := by
        apply Finset.dvd_gcd
        intro t ht
        by_cases htl : t = l
        · rw [htl]
        · rw [hzero t (Finset.mem_filter.1 ht).2 htl]; exact dvd_zero _
      rw [hg] at hd
      exact Int.isUnit_iff.1 (isUnit_of_dvd_one hd)
    by_cases hlj : l = j
    · subst hlj; exact extendsBasis_of_unit hunit
    · apply ExtendsBasis.of_transvection (k := j) (l := l) (c := 1) (Ne.symm hlj) hl
      apply extendsBasis_of_unit
      rw [transvection_mulVec_apply, if_pos rfl, hzero j le_rfl (Ne.symm hlj)]
      rcases hunit with h | h <;> simp [h]

/-- **Extension to a basis by the greatest common divisor** (Cassels, Ch. 12, (1.3)–(1.4), p. 255): $\vec{b}$ extends
$e_0, \dots, e_{j-1}$ to a basis of $\mathbb{Z}^n$ iff $\gcd(b_j, \dots, b_{n-1}) = 1$. *Proof:* ($\Rightarrow$) row $j$ of $T^{-1}$
gives integers $c_k$ with $\sum_{k \ge j} c_k b_k = 1$; ($\Leftarrow$) Euclid's algorithm by elementary column operations
that fix $e_0, \dots, e_{j-1}$. -/
theorem extendsBasis_iff_gcd (j : Fin n) (b : Fin n → ℤ) : ExtendsBasis j b ↔ tailGcd j b = 1 := by
  constructor
  · rintro ⟨T, h1, h2⟩
    have hrow : ∑ l, T⁻¹.val j l * b l = 1 := by
      have := congrFun (congrFun (Units.inv_mul T) j) j
      simp only [Matrix.mul_apply] at this
      rw [Matrix.one_apply_eq] at this
      simpa only [h2] using this
    have hd : tailGcd j b ∣ 1 := by
      rw [← hrow]
      apply Finset.dvd_sum
      intro l _
      by_cases hl : j ≤ l
      · exact dvd_mul_of_dvd_right (tailGcd_dvd j b hl) _
      · have hl' : l < j := not_le.1 hl
        have h0 : T⁻¹.val j l = 0 := by
          have := congrFun (congrFun (Units.inv_mul T) j) l
          simp only [Matrix.mul_apply, h1 l hl'] at this
          simpa [Matrix.one_apply, Pi.single_apply, hl'.ne'] using this
        rw [h0]; simp
    exact Int.eq_one_of_dvd_one (tailGcd_nonneg j b) hd
  · intro h
    exact extendsBasis_of_gcd_aux j _ b rfl h

/-- **Division of an integral vector by the gcd of its tail, with reduced head** (Cassels, Ch. 12, proof of
Thm. 3.1 (ii), p. 264): if some coordinate $u_k$ with $k \ge j$ is nonzero, then
$$\vec{u} = s\,\vec{e}^{\,*} + t_0e_0 + \dots + t_{j-1}e_{j-1}$$
with $s \ge 1$ an integer, $\vec{e}^{\,*}$ extending $e_0, \dots, e_{j-1}$ to a basis, and integers $t_i$ with
$|t_i| \le s/2$ (the vector $\vec{t}$ has $t_k = 0$ for $k \ge j$). -/
theorem exists_extendsBasis_decomp {j : Fin n} {u : Fin n → ℤ} (hu : ∃ k, j ≤ k ∧ u k ≠ 0) :
    ∃ (s : ℤ) (e t : Fin n → ℤ), 0 < s ∧ ExtendsBasis j e ∧ (∀ k, j ≤ k → t k = 0) ∧
      (∀ k, 2 * |t k| ≤ s) ∧ u = s • e + t := by
  obtain ⟨k0, hk0, hu0⟩ := hu
  obtain ⟨s, hs⟩ : ∃ s, s = tailGcd j u := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by
    intro h0
    rw [hs] at h0
    exact hu0 (Finset.gcd_eq_zero_iff.1 h0 k0 (mem_tail hk0))
  have hspos : 0 < s := lt_of_le_of_ne (hs ▸ tailGcd_nonneg j u) (Ne.symm hs0)
  have hdvd : ∀ k, j ≤ k → s ∣ u k := fun k hk => hs ▸ tailGcd_dvd j u hk
  obtain ⟨q, hq⟩ : ∃ q : Fin n → ℤ, ∀ i, q i = (2 * u i + s) / (2 * s) := ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Fin n → ℤ, ∀ k, e k = if k < j then q k else u k / s := ⟨_, fun _ => rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin n → ℤ, ∀ k, t k = if k < j then u k - s * q k else 0 :=
    ⟨_, fun _ => rfl⟩
  have het : ∀ k, j ≤ k → e k = u k / s := fun k hk => by rw [he, if_neg (not_lt.2 hk)]
  have hut : ∀ k, j ≤ k → u k = s * e k := fun k hk => by
    rw [het k hk]; exact (Int.mul_ediv_cancel' (hdvd k hk)).symm
  refine ⟨s, e, t, hspos, ?_, ?_, ?_, ?_⟩
  · apply (extendsBasis_iff_gcd j e).2
    have h1 : s * tailGcd j e ∣ tailGcd j u := by
      apply Finset.dvd_gcd
      intro k hk
      have hk' := (Finset.mem_filter.1 hk).2
      rw [hut k hk']
      exact mul_dvd_mul_left s (tailGcd_dvd j e hk')
    rw [← hs] at h1
    have h2 : tailGcd j e ∣ 1 := (mul_dvd_mul_iff_left hs0).1 (by simpa using h1)
    exact Int.eq_one_of_dvd_one (tailGcd_nonneg j e) h2
  · intro k hk
    rw [ht k, if_neg (not_lt.2 hk)]
  · intro k
    by_cases hk : k < j
    · rw [ht k, if_pos hk, hq k]
      have h1 := Int.emod_nonneg (2 * u k + s) (show 2 * s ≠ 0 by omega)
      have h2 := Int.emod_lt_of_pos (2 * u k + s) (show 0 < 2 * s by omega)
      have h3 := Int.mul_ediv_add_emod (2 * u k + s) (2 * s)
      rcases abs_cases (u k - s * ((2 * u k + s) / (2 * s))) with ⟨h, _⟩ | ⟨h, _⟩ <;>
        rw [h] <;> nlinarith
    · rw [ht k, if_neg hk]; simp; omega
  · funext k
    by_cases hk : k < j
    · show u k = s * e k + t k
      rw [he k, ht k, if_pos hk, if_pos hk]; ring
    · have hk' : j ≤ k := not_lt.1 hk
      show u k = s * e k + t k
      rw [ht k, if_neg hk, add_zero]
      exact hut k hk'

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem bilin_comm {F : Matrix (Fin n) (Fin n) ℝ} (hs : F.IsSymm) (x y : Fin n → ℝ) :
    y ⬝ᵥ (F *ᵥ x) = x ⬝ᵥ (F *ᵥ y) := by
  have hs' : Fᵀ = F := hs
  rw [Matrix.dotProduct_mulVec]
  conv_lhs => rw [← hs']
  rw [Matrix.vecMul_transpose, dotProduct_comm]

/-- Expansion of $f(\vec{x}+\vec{y})$ for symmetric $F$. -/
theorem val_add {F : Matrix (Fin n) (Fin n) ℝ} (hs : F.IsSymm) (x y : Fin n → ℝ) :
    val F (x + y) = val F x + 2 * (x ⬝ᵥ (F *ᵥ y)) + val F y := by
  have := bilin_comm hs x y
  simp only [val, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  linarith

/-- **Cauchy–Schwarz for a positive semi-definite form:** $(\vec{x}^{\mathsf T}F\vec{y})^2 \le f(\vec{x})f(\vec{y})$. -/
theorem sq_bilin_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) (x y : Fin n → ℝ) :
    (x ⬝ᵥ (F *ᵥ y)) ^ 2 ≤ val F x * val F y := by
  obtain ⟨hs, hnn⟩ := (posSemidef_iff F).1 hF
  have key : ∀ t : ℝ, 0 ≤ val F y * (t * t) + 2 * (x ⬝ᵥ (F *ᵥ y)) * t + val F x := by
    intro t
    have h := hnn (x + t • y)
    rw [val_add hs, val_smul] at h
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- **The triangle inequality for $\sqrt f$** (Cassels, Ch. 12, §1, p. 260, the inequality before (1.9)): for a positive
semi-definite real form, $\sqrt{f(\vec{x}_1 + \vec{x}_2)} \le \sqrt{f(\vec{x}_1)} + \sqrt{f(\vec{x}_2)}$. -/
theorem sqrt_val_add_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) (x y : Fin n → ℝ) :
    Real.sqrt (val F (x + y)) ≤ Real.sqrt (val F x) + Real.sqrt (val F y) := by
  obtain ⟨hs, hnn⟩ := (posSemidef_iff F).1 hF
  have hx := hnn x
  have hy := hnn y
  have hB := sq_bilin_le hF x y
  have hB' : x ⬝ᵥ (F *ᵥ y) ≤ Real.sqrt (val F x) * Real.sqrt (val F y) := by
    rw [← Real.sqrt_mul hx]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hB)
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [val_add hs]
  nlinarith

/-- $\sqrt{f(\lambda\vec{x})} = |\lambda|\sqrt{f(\vec{x})}$. -/
theorem sqrt_val_smul {F : Matrix (Fin n) (Fin n) ℝ} (c : ℝ) (x : Fin n → ℝ) :
    Real.sqrt (val F (c • x)) = |c| * Real.sqrt (val F x) := by
  rw [val_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **Convexity of $\sqrt f$** (Cassels, Ch. 12, (1.9), p. 260): for a positive semi-definite real form and real
$\lambda_i$, $\sqrt{f(\sum_i \lambda_i\vec{x}_i)} \le \sum_i |\lambda_i|\sqrt{f(\vec{x}_i)}$. -/
theorem sqrt_val_sum_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (x : ι → Fin n → ℝ) :
    Real.sqrt (val F (∑ i ∈ s, c i • x i)) ≤ ∑ i ∈ s, |c i| * Real.sqrt (val F (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : val F (0 : Fin n → ℝ) = 0 := by simp [val]
    simp [this]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc Real.sqrt (val F (c a • x a + ∑ i ∈ s, c i • x i))
        ≤ Real.sqrt (val F (c a • x a)) + Real.sqrt (val F (∑ i ∈ s, c i • x i)) :=
          sqrt_val_add_le hF _ _
      _ ≤ |c a| * Real.sqrt (val F (x a)) + ∑ i ∈ s, |c i| * Real.sqrt (val F (x i)) := by
          rw [sqrt_val_smul]; gcongr

/-- **A strictly definite form is bounded below by a multiple of $|\vec{x}|^2$** (Cassels, Ch. 12, Lemma 5.2, p. 270):
if $F$ is strictly positive definite there is $K > 0$ with $f(\vec{x}) \ge K|\vec{x}|^2 = K\sum_i x_i^2$ for every real
$\vec{x}$. -/
theorem exists_val_ge {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Fin n → ℝ, K * ∑ i, x i ^ 2 ≤ val F x := by
  obtain ⟨hs, hp⟩ := (posDef_iff F).1 hF
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun x => by simp [val]⟩
  set S : Set (Fin n → ℝ) := {x | ∑ i, x i ^ 2 = 1} with hSdef
  have hcont : Continuous (fun x : Fin n → ℝ => val F x) := by
    unfold val Matrix.mulVec dotProduct
    fun_prop
  have hSc : IsClosed S :=
    isClosed_eq (by fun_prop) continuous_const
  have hSb : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : x i ^ 2 ≤ 1 := by
      have : x i ^ 2 ≤ ∑ i, x i ^ 2 :=
        Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      have hx' : ∑ i, x i ^ 2 = 1 := hx
      linarith
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  have hSk : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSc hSb
  have hne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hn⟩ 1, ?_⟩
    simp [hSdef, Pi.single_apply]
  obtain ⟨x0, hx0, hmin⟩ := hSk.exists_isMinOn hne hcont.continuousOn
  have hx0' : ∑ i, x0 i ^ 2 = 1 := hx0
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    simp at hx0'
  have hK : 0 < val F x0 := hp x0 hx0ne
  refine ⟨val F x0, hK, fun x => ?_⟩
  by_cases hz : ∑ i, x i ^ 2 = 0
  · have : x = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 hz i
        (Finset.mem_univ i)
      simpa using this
    subst this
    simp [val]
  · have hpos : 0 < ∑ i, x i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hz)
    set r := Real.sqrt (∑ i, x i ^ 2) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hpos.le
    have hy : r⁻¹ • x ∈ S := by
      show ∑ i, (r⁻¹ • x) i ^ 2 = 1
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [← hr2]
      field_simp
    have h : val F x0 ≤ val F (r⁻¹ • x) := hmin hy
    rw [val_smul] at h
    have : val F x0 * r ^ 2 ≤ val F x := by
      have := mul_le_mul_of_nonneg_left h (sq_nonneg r)
      calc val F x0 * r ^ 2 ≤ r ^ 2 * ((r⁻¹) ^ 2 * val F x) := by nlinarith
        _ = val F x := by field_simp
    rw [← hr2]; linarith

/-- **Finitely many integral vectors below a bound** (Cassels, Ch. 12, proof of Thm. 1.1, p. 256): for strictly
positive definite $F$ and real $M$, only finitely many $\vec{m} \in \mathbb{Z}^n$ have $f(\vec{m}) \le M$. -/
theorem finite_val_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (M : ℝ) :
    {m : Fin n → ℤ | val F (cast m) ≤ M}.Finite := by
  obtain ⟨K, hK, hKx⟩ := exists_val_ge hF
  set N : ℕ := ⌈M / K⌉₊ with hN
  refine (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-(N : ℤ)) N)
    (fun _ => Set.finite_Icc _ _)).subset ?_
  intro m hm i _
  have hm' : val F (cast m) ≤ M := hm
  have h1 := hKx (cast m)
  have h2 : K * ((m i : ℝ) ^ 2) ≤ K * ∑ i, (cast m i) ^ 2 := by
    gcongr
    exact Finset.single_le_sum (f := fun i => (cast m i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h3 : (m i : ℝ) ^ 2 ≤ N := by
    have : (m i : ℝ) ^ 2 ≤ M / K := by
      rw [le_div_iff₀ hK]; linarith
    exact this.trans (Nat.le_ceil _)
  have h5 : |m i| ≤ m i ^ 2 := by
    have := Int.le_self_sq |m i|
    rwa [sq_abs] at this
  have h6 : ((|m i| : ℤ) : ℝ) ≤ (N : ℝ) := by
    have : ((|m i| : ℤ) : ℝ) ≤ ((m i : ℝ)) ^ 2 := by exact_mod_cast h5
    exact this.trans h3
  have h4 : |m i| ≤ (N : ℤ) := by exact_mod_cast h6
  exact abs_le.1 h4

end QuadFormsKB.Reduction
