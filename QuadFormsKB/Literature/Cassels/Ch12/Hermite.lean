/-
# Cassels, Chapter 12, §1–§2: Hermite's reduction

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §1, p. 259 (Hermite's definition of a reduced form, (1.8)), and §2,
pp. 260–261 (Hermite's proof (i) of Theorem 2.1, $\gamma_n = (4/3)^{(n-1)/2}$).

* `schurCompl`, `val_cons_eq_schurCompl`: completing the square in $x_0$, $f = f_{00}(x_0 + \sum_{j \ge 1}(f_{0j}/f_{00})x_j)^2
  + g(x_1, \dots, x_{n-1})$ ((1.8)).
* `IsHermiteReduced`: Hermite's recursive definition (12.r3).
* `IsHermiteReduced.inSiegelDomain`: a Hermite-reduced form lies in $\mathcal S(4/3, 1/2)$ (p. 259).
* `exists_isHermiteReduced`, `finite_isHermiteReduced`: "the analogue of Theorem 1.1 holds for Hermite-reduction"
  (p. 259).
* `hermiteConstantBound_hermite`: Theorem 2.1 with Hermite's constant $(4/3)^{(n-1)/2}$ (proof (i), pp. 260–261).

The library's integral version of Hermite's argument (positive definite integral matrices, crude constant) is
`Siegel.Hermite.exists_hermite_bound` / `Siegel.Hermite.exists_reduced` (`Siegel/HermiteReduction.lean`); this file is the
real version that Chapter 12 uses.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec4

open Matrix

namespace QuadFormsKB.Reduction

variable {m : ℕ}

/-- **The form left after completing the square in $x_0$** (Cassels, Ch. 12, (1.8), p. 259, and (2.1), p. 260): for
$F \in M_{m+1}(\mathbb{R})$, the $m \times m$ matrix
$$G = F' - f_{00}^{-1}\,\vec{c}\,\vec{r}^{\mathsf T}, \qquad F' = (f_{i+1,j+1}),\ c_i = f_{i+1,0},\ r_j = f_{0,j+1},$$
the Schur complement of $f_{00}$ (Lean's $0^{-1} = 0$ if $f_{00} = 0$). For symmetric $F$ with $f_{00} \ne 0$,
$f(x_0, \vec{x}') = f_{00}(x_0 + \sum_j (f_{0,j+1}/f_{00})x'_j)^2 + g(\vec{x}')$ (`val_cons_eq_schurCompl`). The library's
integral analogue is `Siegel.Hermite.schur` ($= f_{00}G$, to stay integral). -/
@[kb "cassels1978" "Ch. 12, §1, (1.8), p. 259"]
noncomputable def schurCompl (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  F.submatrix Fin.succ Fin.succ - (F 0 0)⁻¹ • vecMulVec (fun i => F i.succ 0) (fun j => F 0 j.succ)

/-- **Completing the square in $x_0$** (Cassels, Ch. 12, (1.8), p. 259): for symmetric $F$ with $f_{00} \ne 0$,
$$f(x_0, \vec{x}') = f_{00}\Bigl(x_0 + \sum_{j} \frac{f_{0,j+1}}{f_{00}}x'_j\Bigr)^2 + g(\vec{x}'),$$
$g$ the form with matrix `schurCompl F`. -/
theorem val_cons_eq_schurCompl {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hF : F.IsSymm) (h0 : F 0 0 ≠ 0)
    (a : ℝ) (x : Fin m → ℝ) :
    val F (Fin.cons a x) = F 0 0 * (a + ∑ j, F 0 j.succ / F 0 0 * x j) ^ 2 + val (schurCompl F) x := by
  have hs : ∀ i : Fin m, F i.succ 0 = F 0 i.succ := fun i => by
    have := congrFun (congrFun hF 0) i.succ
    simpa [Matrix.transpose_apply] using this
  set s := ∑ j, F 0 j.succ * x j with hsdef
  have e1 : ∑ j, F 0 j.succ / F 0 0 * x j = s / F 0 0 := by
    rw [hsdef, Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ i : Fin m, x i * (F i.succ 0 * a) = a * s := by
    rw [hsdef, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hs]; ring
  have e3 : ∑ i : Fin m, x i * (∑ j, (F 0 0)⁻¹ * (F i.succ 0 * F 0 j.succ) * x j) = (F 0 0)⁻¹ * (s * s) := by
    have : ∀ i : Fin m, x i * (∑ j, (F 0 0)⁻¹ * (F i.succ 0 * F 0 j.succ) * x j)
        = (F 0 0)⁻¹ * (F 0 i.succ * x i) * s := by
      intro i
      rw [hsdef, Finset.mul_sum (a := x i), Finset.mul_sum (a := (F 0 0)⁻¹ * (F 0 i.succ * x i))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hs]; ring
    rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_mul, ← Finset.mul_sum, ← hsdef]
    ring
  have e4 : ∑ i : Fin m, x i * (∑ j, F i.succ j.succ * x j) = val (schurCompl F) x + (F 0 0)⁻¹ * (s * s) := by
    rw [← e3]
    simp only [val, schurCompl, dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      Matrix.submatrix_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, mul_sub]
    ring
  simp only [val, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_add,
    Finset.sum_add_distrib, e2]
  rw [e1]
  have := e4
  simp only [val, dotProduct, Matrix.mulVec] at this
  rw [← hsdef]
  field_simp
  rw [this]
  field_simp
  ring

/-- The determinant: $\det F = f_{00}\det G$ (Cassels, Ch. 12, p. 260, "$\det g = D/f_{11}$"). -/
theorem det_eq_mul_det_schurCompl {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (h0 : F 0 0 ≠ 0) :
    F.det = F 0 0 * (schurCompl F).det := by
  set c : Fin (m + 1) → ℝ := fun i => if i = 0 then 0 else -(F i 0 / F 0 0) with hc
  set L : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    1 + Matrix.replicateCol Unit c * Matrix.replicateRow Unit (Pi.single 0 1 : Fin (m + 1) → ℝ) with hL
  have hLdet : L.det = 1 := by
    rw [hL, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [hc]
  have hLF : ∀ i j, (L * F) i j = F i j + c i * F 0 j := by
    intro i j
    simp [hL, Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Pi.single_apply]
    simp [add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul]
  have h1 : F.det = (L * F).det := by rw [Matrix.det_mul, hLdet, one_mul]
  rw [h1, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin m, (L * F) i.succ 0 = 0 := by
    intro i
    rw [hLF]
    simp [hc]
    field_simp
    ring
  simp only [hz, Fin.succAbove_zero, Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  have h00 : (L * F) 0 0 = F 0 0 := by rw [hLF]; simp [hc]
  rw [h00]
  congr 2
  ext i j
  rw [Matrix.submatrix_apply, hLF]
  simp [hc, schurCompl, vecMulVec_apply]
  field_simp
  ring

/-- For strictly positive definite $F$ the form $g$ left after completing the square is strictly positive definite. -/
theorem PosDef.schurCompl {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hF : F.PosDef) : (schurCompl F).PosDef := by
  obtain ⟨hs, hp⟩ := (posDef_iff F).1 hF
  have hs' : ∀ i j, F i j = F j i := fun i j => by
    have := congrFun (congrFun hs j) i
    simpa [Matrix.transpose_apply] using this
  have h0 : 0 < F 0 0 := by
    have := hp (Pi.single 0 1) (by intro h; have := congrFun h 0; simp at this)
    rwa [val_single] at this
  rw [posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, QuadFormsKB.Reduction.schurCompl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      Matrix.submatrix_apply, smul_eq_mul]
    rw [hs' j.succ i.succ, hs' i.succ 0, hs' 0 j.succ]
    ring
  · have hv := val_cons_eq_schurCompl hs h0.ne' (-∑ j, F 0 j.succ / F 0 0 * x j) x
    have hne : (Fin.cons (-∑ j, F 0 j.succ / F 0 0 * x j) x : Fin (m + 1) → ℝ) ≠ 0 := by
      intro h
      apply hx
      ext i
      have := congrFun h i.succ
      simpa using this
    have := hp _ hne
    rw [hv] at this
    simpa using this

/-- **Hermite-reduced form** (Cassels, Ch. 12, §1, p. 259, Hermite's recursive definition, 0-based): a real form in
$0$ variables is reduced; $f$ in $m + 1$ variables is Hermite-reduced if it is strictly positive definite and
(i) $f(1, 0, \dots, 0) = f_{00} = \inf_{\vec{m} \in \mathbb{Z}^{m+1} \setminus 0} f(\vec{m})$,
(ii) $|2f_{0j}| \le f_{00}$ for $j \ge 1$, and the form $g(x_1, \dots, x_m)$ of (1.8), obtained by completing the square
in $x_0$ (`schurCompl`), is Hermite-reduced as a form in $m$ variables.
Cassels also mentions two other notions called "Hermite-reduced" (footnote, p. 259, and the Notes, p. 282); this is
the one of p. 259. Not to be confused with Minkowski reduction (`IsMinkowskiReduced`). -/
@[kb "cassels1978" "Ch. 12, §1, p. 259 (Hermite's definition of a reduced form)"]
def IsHermiteReduced : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → Prop
  | 0, _ => True
  | _ + 1, F => F.PosDef ∧ (∀ v, v ≠ 0 → F 0 0 ≤ val F (cast v)) ∧ (∀ j, |2 * F 0 (Fin.succ j)| ≤ F 0 0) ∧
      IsHermiteReduced (schurCompl F)

/-- Helper: the upper unitriangular matrix of the decomposition of $F$ built from one of the form $g$ left after
completing the square in $x_0$: first row $(1, f_{01}/f_{00}, \dots)$, lower block `C'`, first column $(1, 0, \dots, 0)$. -/
noncomputable def consC (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (C' : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℝ) (Fin.cases (motive := fun _ => ℝ) 1 (fun j' => F 0 j'.succ / F 0 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℝ) 0 (fun j' => C' i' j') j) i

/-- Helper: entries of `consC`. -/
theorem consC_zero_zero (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (C' : Matrix (Fin m) (Fin m) ℝ) :
    consC F C' 0 0 = 1 := rfl

/-- Helper: entry formula `consC_zero_succ`. -/
theorem consC_zero_succ (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (C' : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    consC F C' 0 j.succ = F 0 j.succ / F 0 0 := rfl

/-- Helper: entry formula `consC_succ_zero`. -/
theorem consC_succ_zero (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (C' : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    consC F C' i.succ 0 = 0 := rfl

/-- Helper: entry formula `consC_succ_succ`. -/
theorem consC_succ_succ (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (C' : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    consC F C' i.succ j.succ = C' i j := rfl

/-- Helper: entries of $C^{\mathsf T}\operatorname{diag}(h)C$. -/
theorem conj_diag_apply {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (i j : Fin n) :
    (Cᵀ * diagonal h * C) i j = ∑ k, C k i * h k * C k j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]

/-- Helper: a decomposition of $g$ = `schurCompl F` extends to one of $F$ (the induction step of Hermite's argument). -/
theorem isSqDecomp_cons {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hs : F.IsSymm) (h0 : F 0 0 ≠ 0)
    {h' : Fin m → ℝ} {C' : Matrix (Fin m) (Fin m) ℝ} (hd : IsSqDecomp (schurCompl F) h' C') :
    IsSqDecomp F (Fin.cons (F 0 0) h') (consC F C') := by
  have hs' : ∀ i j, F i j = F j i := fun i j => by
    have := congrFun (congrFun hs j) i
    simpa [Matrix.transpose_apply] using this
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    induction i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ i' =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j' =>
        rw [consC_succ_succ]
        exact hd.1 _ _ (Fin.succ_lt_succ_iff.1 hij)
  · intro i
    refine Fin.cases rfl (fun i' => ?_) i
    rw [consC_succ_succ]; exact hd.2.1 i'
  · ext i j
    rw [conj_diag_apply, Fin.sum_univ_succ]
    have hg : ∀ a b : Fin m, ∑ k, C' k a * h' k * C' k b = schurCompl F a b := by
      intro a b
      rw [← conj_diag_apply, ← hd.2.2]
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [consC_zero_zero, consC_succ_zero]
    · simp [consC_zero_zero, consC_zero_succ, consC_succ_zero]
      field_simp
    · simp [consC_zero_zero, consC_zero_succ, consC_succ_zero]
      rw [hs' i'.succ 0]
      field_simp
    · simp only [consC_zero_succ, consC_succ_succ, Fin.cons_zero, Fin.cons_succ, hg]
      simp only [schurCompl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.submatrix_apply,
        smul_eq_mul]
      rw [hs' i'.succ 0]
      field_simp
      ring

/-- Helper: every real number is within $1/2$ of an integer (up to sign). -/
theorem exists_int_abs_add_le (r : ℝ) : ∃ t : ℤ, |(t : ℝ) + r| ≤ 1 / 2 :=
  ⟨-round r, by
    have := abs_sub_round r
    push_cast
    rwa [show -(round r : ℝ) + r = r - round r by ring]⟩

/-- Helper: casting commutes with `Fin.cons`. -/
theorem cast_cons (t : ℤ) (v : Fin m → ℤ) :
    cast (Fin.cons t v : Fin (m + 1) → ℤ) = (Fin.cons (t : ℝ) (cast v) : Fin (m + 1) → ℝ) := by
  funext i
  induction i using Fin.cases <;> simp [cast]

/-- Helper (Hermite's key inequality, Cassels, Ch. 12, p. 260): if $f_{00}$ is the minimum of $f$ on nonzero integral
vectors, then $f_{00} \le \tfrac14 f_{00} + g(\vec{v}')$ for every nonzero integral $\vec{v}'$ in $m$ variables
(take $\vec{v} = (t, \vec{v}')$ with $t$ rounding $-\sum_j (f_{0j}/f_{00})v'_j$). -/
theorem first_le {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hF : F.PosDef)
    (hmin : ∀ v : Fin (m + 1) → ℤ, v ≠ 0 → F 0 0 ≤ val F (cast v)) (v' : Fin m → ℤ) (hv' : v' ≠ 0) :
    F 0 0 ≤ F 0 0 / 4 + val (schurCompl F) (cast v') := by
  obtain ⟨hs, hp⟩ := (posDef_iff F).1 hF
  have h0 : 0 < F 0 0 := by
    have := hp (Pi.single 0 1) (by intro h; have := congrFun h 0; simp at this)
    rwa [val_single] at this
  obtain ⟨t, ht⟩ := exists_int_abs_add_le (∑ j, F 0 j.succ / F 0 0 * cast v' j)
  have hv : (Fin.cons t v' : Fin (m + 1) → ℤ) ≠ 0 := by
    intro h
    apply hv'
    funext i
    have := congrFun h i.succ
    simpa using this
  have h1 := hmin _ hv
  rw [cast_cons, val_cons_eq_schurCompl hs h0.ne'] at h1
  have h2 : ((t : ℝ) + ∑ j, F 0 j.succ / F 0 0 * cast v' j) ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 ht
    nlinarith [this.1, this.2]
  nlinarith

/-- **A Hermite-reduced form lies in the Siegel domain $\mathcal S(4/3, 1/2)$** (Cassels, Ch. 12, p. 259, "it is easy
to see"; the parameters are garbled in the machine-read text and reconstructed from Hermite's argument:
$|c_{0j}| = |f_{0j}|/f_{00} \le \tfrac12$ by (ii), and $f_{00} \le f(\vec{e}_1 + t\vec{e}_0) \le \tfrac14 f_{00} + h_1$ for a
suitable integer $t$ by (i), so $h_0 \le \tfrac43 h_1$). -/
@[kb "cassels1978" "Ch. 12, §1, p. 259 (a Hermite-reduced form is in 𝒮(4/3, 1/2))"]
theorem IsHermiteReduced.inSiegelDomain {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsHermiteReduced F) :
    InSiegelDomain (4 / 3) (1 / 2) F := by
  induction n with
  | zero =>
    exact ⟨fun _ => 1, 1, ⟨fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨hP, hmin, hoff, hg⟩ := hF
    obtain ⟨hs, hp⟩ := (posDef_iff F).1 hP
    have h0 : 0 < F 0 0 := by
      have := hp (Pi.single 0 1) (by intro h; have := congrFun h 0; simp at this)
      rwa [val_single] at this
    obtain ⟨h', C', hd', hpos', hstep', hC'⟩ := ih hg
    have hd := isSqDecomp_cons hs h0.ne' hd'
    refine ⟨Fin.cons (F 0 0) h', consC F C', hd, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
    · induction i using Fin.cases with
      | zero => simpa using h0
      | succ i' => simpa using hpos' i'
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          have hj : j' = ⟨0, by have := j'.2; omega⟩ := Fin.ext (by simpa using hij)
          rw [hj]
          have hpg := (PosDef.schurCompl hP)
          have hdiag : h' ⟨0, by omega⟩ = schurCompl F ⟨0, by omega⟩ ⟨0, by omega⟩ := by
            rw [hd'.diag_eq]
            have : Finset.Iic (⟨0, by omega⟩ : Fin m) = {⟨0, by omega⟩} := by
              ext k; simp [Fin.le_def, Fin.ext_iff]
            rw [this]
            simp [hd'.2.1]
          have := first_le hP hmin (Pi.single ⟨0, by omega⟩ 1) (by
            intro h; have := congrFun h ⟨0, by omega⟩; simp at this)
          have hc : cast (Pi.single ⟨0, by omega⟩ 1 : Fin m → ℤ) = (Pi.single ⟨0, by omega⟩ 1 : Fin m → ℝ) := by
            funext k; by_cases hk : k = ⟨0, by omega⟩ <;> simp [cast, Pi.single_apply, hk]
          rw [hc, val_single] at this
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hdiag]
          linarith
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          simp only [Fin.cons_succ]
          exact hstep' i' j' (by simpa using hij)
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ j' =>
          rw [consC_zero_succ, abs_div, abs_of_pos h0]
          rw [div_le_iff₀ h0]
          have := hoff j'
          rw [abs_mul] at this
          norm_num at this ⊢
          linarith
      | succ i' =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt_zero _)
        | succ j' =>
          rw [consC_succ_succ]
          exact hC' i' j' (Fin.succ_lt_succ_iff.1 hij)

/-- Helper: the unimodular substitution $\begin{pmatrix}1 & \vec{t}\\ 0 & A\end{pmatrix}$ (first row $(1, \vec{t})$, lower
block $A$, first column $(1, 0, \dots, 0)^{\mathsf T}$), which substitutes $x_0 \mapsto x_0 + \vec{t}\cdot\vec{x}'$,
$\vec{x}' \mapsto A\vec{x}'$. -/
def blockZ (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℤ) (Fin.cases (motive := fun _ => ℤ) 1 t j)
    (fun i' => Fin.cases (motive := fun _ => ℤ) 0 (fun j' => A i' j') j) i

/-- Helper: entry formula `blockZ_zero_zero`. -/
theorem blockZ_zero_zero (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) : blockZ t A 0 0 = 1 := rfl

/-- Helper: entry formula `blockZ_zero_succ`. -/
theorem blockZ_zero_succ (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) (j : Fin m) : blockZ t A 0 j.succ = t j := rfl

/-- Helper: entry formula `blockZ_succ_zero`. -/
theorem blockZ_succ_zero (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) (i : Fin m) : blockZ t A i.succ 0 = 0 := rfl

/-- Helper: entry formula `blockZ_succ_succ`. -/
theorem blockZ_succ_succ (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    blockZ t A i.succ j.succ = A i j := rfl

/-- Helper: `blockZ t A` has determinant $\det A$. -/
theorem det_blockZ (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) : (blockZ t A).det = A.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [blockZ_succ_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, blockZ_zero_zero, Fin.succAbove_zero]
  rfl

/-- Helper: `blockZ t A` as an element of $\mathrm{GL}_{m+1}(\mathbb{Z})$ for $A \in \mathrm{GL}_m(\mathbb{Z})$. -/
noncomputable def blockGL (t : Fin m → ℤ) (A : GL (Fin m) ℤ) : GL (Fin (m + 1)) ℤ :=
  ((Matrix.isUnit_iff_isUnit_det (blockZ t A.val)).2
    (by rw [det_blockZ]; exact (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit)).unit

/-- Helper: entry formula `blockGL_val`. -/
theorem blockGL_val (t : Fin m → ℤ) (A : GL (Fin m) ℤ) : (blockGL t A).val = blockZ t A.val := rfl

/-- Helper: entries of $T^{\mathsf T}FT$. -/
theorem act_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    act T F i j = ∑ a, ∑ b, (T a i : ℝ) * F a b * T b j := by
  simp only [act, castM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Helper: entry formula `act_blockZ_zero_zero`. -/
theorem act_blockZ_zero_zero (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    act (blockZ t A) G 0 0 = G 0 0 := by
  simp [act_apply, Fin.sum_univ_succ, blockZ_zero_zero, blockZ_succ_zero]

/-- Helper: entry formula `act_blockZ_zero_succ`. -/
theorem act_blockZ_zero_succ (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (j : Fin m) :
    act (blockZ t A) G 0 j.succ = G 0 0 * t j + ∑ b, G 0 b.succ * A b j := by
  simp [act_apply, Fin.sum_univ_succ, blockZ_zero_zero, blockZ_succ_zero, blockZ_zero_succ, blockZ_succ_succ]

/-- Helper: entry formula `act_blockZ_succ_zero`. -/
theorem act_blockZ_succ_zero (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (i : Fin m) :
    act (blockZ t A) G i.succ 0 = t i * G 0 0 + ∑ a, A a i * G a.succ 0 := by
  simp [act_apply, Fin.sum_univ_succ, blockZ_zero_zero, blockZ_succ_zero, blockZ_zero_succ, blockZ_succ_succ]

/-- Helper: entry formula `act_blockZ_succ_succ`. -/
theorem act_blockZ_succ_succ (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ) (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (i j : Fin m) :
    act (blockZ t A) G i.succ j.succ = t i * G 0 0 * t j + t i * (∑ b, G 0 b.succ * A b j) +
      (∑ a, A a i * G a.succ 0) * t j + ∑ a, ∑ b, (A a i : ℝ) * G a.succ b.succ * A b j := by
  simp [act_apply, Fin.sum_univ_succ, blockZ_zero_zero, blockZ_succ_zero, blockZ_zero_succ, blockZ_succ_succ,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, Finset.sum_add_distrib]
  ring

/-- Helper: the form $g$ left after completing the square is unchanged by $x_0 \mapsto x_0 + \vec{t}\cdot\vec{x}'$ and
transforms by $A$ under $\vec{x}' \mapsto A\vec{x}'$. -/
theorem schurCompl_act_blockZ (t : Fin m → ℤ) (A : Matrix (Fin m) (Fin m) ℤ)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (h0 : G 0 0 ≠ 0) :
    schurCompl (act (blockZ t A) G) = act A (schurCompl G) := by
  ext i j
  have key : (∑ a, (A a i : ℝ) * G a.succ 0) * (∑ b, G 0 b.succ * A b j) =
      ∑ a, ∑ b, (A a i : ℝ) * (G a.succ 0 * G 0 b.succ) * A b j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have key2 : act A (schurCompl G) i j = (∑ a, ∑ b, (A a i : ℝ) * G a.succ b.succ * A b j) -
      (G 0 0)⁻¹ * ∑ a, ∑ b, (A a i : ℝ) * (G a.succ 0 * G 0 b.succ) * A b j := by
    rw [act_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [schurCompl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.submatrix_apply,
      smul_eq_mul]
    ring
  rw [key2, ← key]
  simp only [schurCompl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.submatrix_apply,
    smul_eq_mul]
  rw [act_blockZ_succ_succ, act_blockZ_succ_zero, act_blockZ_zero_succ, act_blockZ_zero_zero]
  field_simp
  ring

/-- Helper: an invertible integral matrix maps nonzero vectors to nonzero vectors. -/
theorem mulVec_ne_zero_of_gl {n : ℕ} (T : GL (Fin n) ℤ) {v : Fin n → ℤ} (hv : v ≠ 0) : T.val *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun w => (T⁻¹).val *ᵥ w) h
  simpa [Matrix.mulVec_mulVec] using this

/-- Helper: after an integral unimodular substitution, the entry $f_{00}$ is the minimum of the form on nonzero
integral vectors (the value at the shortest primitive vector, Cassels, Ch. 12, p. 259). -/
theorem exists_act_min {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hF : F.PosDef) :
    ∃ T : GL (Fin (m + 1)) ℤ, ∀ v : Fin (m + 1) → ℤ, v ≠ 0 → (act T.val F) 0 0 ≤ val (act T.val F) (cast v) := by
  obtain ⟨hs, hp⟩ := (posDef_iff F).1 hF
  have he0 : (Pi.single 0 1 : Fin (m + 1) → ℤ) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  set S : Set (Fin (m + 1) → ℤ) :=
    {a | a ≠ 0 ∧ val F (cast a) ≤ val F (cast (Pi.single 0 1 : Fin (m + 1) → ℤ))} with hS
  have hfin : S.Finite := (finite_val_le hF _).subset fun a ha => ha.2
  obtain ⟨a, ⟨ha0, hale⟩, hmin⟩ := Set.exists_min_image S (fun a => val F (cast a)) hfin ⟨_, he0, le_rfl⟩
  have hminall : ∀ w : Fin (m + 1) → ℤ, w ≠ 0 → val F (cast a) ≤ val F (cast w) := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact hmin w hwS
    · have : val F (cast (Pi.single 0 1 : Fin (m + 1) → ℤ)) < val F (cast w) := by
        by_contra hcon
        exact hwS ⟨hw, not_lt.1 hcon⟩
      linarith
  obtain ⟨k, hk⟩ := Function.ne_iff.1 ha0
  obtain ⟨s, e, t, hs0, hext, ht, -, hat⟩ :=
    exists_extendsBasis_decomp (j := (0 : Fin (m + 1))) (u := a) ⟨k, Fin.zero_le _, hk⟩
  have ht0 : t = 0 := funext fun k => ht k (Fin.zero_le _)
  rw [ht0, add_zero] at hat
  have he_ne : e ≠ 0 := by
    intro h; apply ha0; rw [hat, h]; simp
  have hcast : cast a = (s : ℝ) • cast e := by
    funext k; rw [hat]; simp [cast]
  have hve : 0 < val F (cast e) := hp _ (by
    intro h; apply he_ne; funext k; have := congrFun h k; simpa [cast] using this)
  have hs1 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ s := hs0
    have h1 : (1 : ℝ) ≤ s := by exact_mod_cast this
    nlinarith
  have hee : val F (cast e) ≤ val F (cast a) := by
    rw [hcast, val_smul]; nlinarith
  obtain ⟨T, -, hT⟩ := hext
  refine ⟨T, fun v hv => ?_⟩
  have hTe : T.val *ᵥ (Pi.single 0 1 : Fin (m + 1) → ℤ) = e := by
    funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply, hT]
  have h00 : (act T.val F) 0 0 = val F (cast e) := by
    rw [← val_single (act T.val F) 0, ← cast_single,val_act_cast, hTe]
  rw [h00, val_act_cast]
  exact hee.trans (hminall _ (mulVec_ne_zero_of_gl T hv))

/-- **Existence of Hermite-reduced forms** (Cassels, Ch. 12, p. 259, "the analogue of Theorem 1.1 holds for
Hermite-reduction"): every strictly positive definite real form is integrally equivalent to a Hermite-reduced one. -/
@[kb "cassels1978" "Ch. 12, §1, p. 259 (analogue of Thm. 1.1 for Hermite reduction: existence)"]
theorem exists_isHermiteReduced {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    ∃ T : GL (Fin n) ℤ, IsHermiteReduced (act T.val F) := by
  induction n with
  | zero => exact ⟨1, trivial⟩
  | succ m ih =>
    obtain ⟨T0, hmin0⟩ := exists_act_min hF
    set G := act T0.val F with hGdef
    have hG : G.PosDef := QuadFormsKB.Reduction.PosDef.act hF T0
    obtain ⟨hGs, hGp⟩ := (posDef_iff G).1 hG
    have h0 : 0 < G 0 0 := by
      have := hGp (Pi.single 0 1) (by intro h; have := congrFun h 0; simp at this)
      rwa [val_single] at this
    obtain ⟨U, hU⟩ := ih (PosDef.schurCompl hG)
    set t : Fin m → ℤ := fun j => -round ((∑ b, G 0 b.succ * U.val b j) / G 0 0) with ht
    refine ⟨T0 * blockGL t U, ?_⟩
    have hact : act (T0 * blockGL t U).val F = act (blockZ t U.val) G := by
      rw [Units.val_mul, act_mul]; rfl
    rw [hact]
    have hH : (act (blockZ t U.val) G).PosDef := QuadFormsKB.Reduction.PosDef.act hG (blockGL t U)
    refine ⟨hH, fun v hv => ?_, fun j => ?_, ?_⟩
    · rw [act_blockZ_zero_zero, val_act_cast]
      exact hmin0 _ (mulVec_ne_zero_of_gl (blockGL t U) hv)
    · rw [act_blockZ_zero_succ, act_blockZ_zero_zero]
      have h1 := abs_sub_round ((∑ b, G 0 b.succ * U.val b j) / G 0 0)
      have h2 : G 0 0 * (t j : ℝ) + ∑ b, G 0 b.succ * U.val b j =
          G 0 0 * (((∑ b, G 0 b.succ * U.val b j) / G 0 0) - round ((∑ b, G 0 b.succ * U.val b j) / G 0 0)) := by
        simp only [ht]; push_cast; field_simp; ring
      rw [h2, ← mul_assoc, abs_mul, abs_of_pos (by positivity : 0 < 2 * G 0 0)]
      nlinarith [h1]
    · rw [schurCompl_act_blockZ t U.val G h0.ne']
      exact hU

/-- **Finiteness of Hermite-reduced forms in a class** (Cassels, Ch. 12, p. 259, the analogue of Theorem 1.1): a
strictly positive definite real form is integrally equivalent to at most finitely many Hermite-reduced forms (by
Theorem 1.4 for $\mathcal S(4/3, 1/2)$). -/
@[kb "cassels1978" "Ch. 12, §1, p. 259 (analogue of Thm. 1.1 for Hermite reduction: finiteness)"]
theorem finite_isHermiteReduced {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    {G | IsHermiteReduced G ∧ ∃ T : GL (Fin n) ℤ, G = act T.val F}.Finite := by
  rcases Set.eq_empty_or_nonempty {G | IsHermiteReduced G ∧ ∃ T : GL (Fin n) ℤ, G = act T.val F} with he | ⟨G0, hG0r, T0, hG0⟩
  · rw [he]; exact Set.finite_empty
  obtain ⟨C, hC⟩ := thm_1_4 n (4 / 3) (1 / 2)
  set N : ℕ := ⌈C⌉₊ with hN
  refine ((Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Set.Icc (-(N : ℤ)) N)
    (fun _ => Set.Finite.pi (fun _ => Set.finite_Icc _ _))).image
      (fun M : Fin n → Fin n → ℤ => act M G0)).subset ?_
  have hkey : ∀ T : GL (Fin n) ℤ, act (T0⁻¹ * T).val G0 = act T.val F := by
    intro T
    have e : act (T0⁻¹).val (act T0.val F) = F := by rw [← act_mul, Units.mul_inv, act_one]
    rw [Units.val_mul, act_mul, hG0, e]
  rintro G ⟨hGr, T, hT⟩
  refine ⟨(T0⁻¹ * T).val, ?_, ?_⟩
  · intro i _ j _
    have hb := hC G0 (T0⁻¹ * T) hG0r.inSiegelDomain (by
      rw [hkey T, ← hT]; exact hGr.inSiegelDomain) i j
    have h1 : ((T0⁻¹ * T).val i j : ℝ) ≤ N := (abs_le.1 hb).2.trans (Nat.le_ceil C)
    have h2 : -(N : ℝ) ≤ ((T0⁻¹ * T).val i j : ℝ) := by
      have := (abs_le.1 hb).1
      have h3 : C ≤ N := Nat.le_ceil C
      linarith
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
  · show act (T0⁻¹ * T).val G0 = G
    rw [hkey T, hT]

/-- Helper (Hermite's induction, in natural powers; Cassels, Ch. 12, pp. 260–261): for $k \ge 0$, every strictly
positive definite form in $k + 1$ variables takes at a nonzero integral vector a value $v$ with
$v^{k+1} \le (4/3)^{\binom{k+1}{2}}D$. -/
theorem hermite_pow_bound (k : ℕ) : ∀ F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, F.PosDef →
    ∃ m : Fin (k + 1) → ℤ, m ≠ 0 ∧ val F (cast m) ^ (k + 1) ≤ (4 / 3 : ℝ) ^ ((k + 1).choose 2) * F.det := by
  induction k with
  | zero =>
    intro F hF
    refine ⟨Pi.single 0 1, by intro h; have := congrFun h 0; simp at this, ?_⟩
    rw [cast_single, val_single]
    simp [Matrix.det_fin_one]
  | succ k ih =>
    intro F hF
    obtain ⟨T, hmin⟩ := exists_act_min hF
    set G := act T.val F with hGdef
    have hG : G.PosDef := QuadFormsKB.Reduction.PosDef.act hF T
    obtain ⟨hGs, hGp⟩ := (posDef_iff G).1 hG
    have h0 : 0 < G 0 0 := by
      have := hGp (Pi.single 0 1) (by intro h; have := congrFun h 0; simp at this)
      rwa [val_single] at this
    obtain ⟨m', hm', hbound⟩ := ih (schurCompl G) (PosDef.schurCompl hG)
    have hfirst := first_le hG hmin m' hm'
    set M := G 0 0 with hM
    set gv := val (schurCompl G) (cast m') with hgv
    have hgvpos : 0 ≤ 3 / 4 * M := by positivity
    have hge : 3 / 4 * M ≤ gv := by linarith
    have hdet : G.det = M * (schurCompl G).det := det_eq_mul_det_schurCompl h0.ne'
    have hdetF : G.det = F.det := det_act T F
    have h1 : (3 / 4 * M) ^ (k + 1) ≤ gv ^ (k + 1) := pow_le_pow_left₀ hgvpos hge _
    have h2 : (3 / 4 * M) ^ (k + 1) ≤ (4 / 3 : ℝ) ^ ((k + 1).choose 2) * (schurCompl G).det := h1.trans hbound
    refine ⟨T.val *ᵥ Pi.single 0 1, mulVec_ne_zero_of_gl T (by
      intro h; have := congrFun h 0; simp at this), ?_⟩
    have hval : val F (cast (T.val *ᵥ Pi.single 0 1)) = M := by
      rw [← val_act_cast, cast_single, val_single]
    rw [hval, ← hdetF, hdet]
    have hc : (k + 1 + 1).choose 2 = (k + 1) + (k + 1).choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    rw [hc, pow_add (4 / 3 : ℝ)]
    have hq : M ^ (k + 1) = (4 / 3 : ℝ) ^ (k + 1) * (3 / 4 * M) ^ (k + 1) := by
      rw [← mul_pow]; ring
    rw [pow_succ M (k + 1), hq]
    have hq0 : (0 : ℝ) < (4 / 3 : ℝ) ^ (k + 1) := by positivity
    calc (4 / 3 : ℝ) ^ (k + 1) * (3 / 4 * M) ^ (k + 1) * M
        ≤ (4 / 3 : ℝ) ^ (k + 1) * ((4 / 3 : ℝ) ^ ((k + 1).choose 2) * (schurCompl G).det) * M := by gcongr
      _ = _ := by ring

/-- **Theorem 2.1 with Hermite's constant** (Cassels, Ch. 12, §2, proof (i), pp. 260–261): for $n \ge 1$,
$\gamma_n = (4/3)^{(n-1)/2}$ satisfies Theorem 2.1: every strictly positive definite real form in $n$ variables takes a
value $\le (4/3)^{(n-1)/2}D^{1/n}$ at a nonzero integral vector. *Proof* (Hermite's, by induction on $n$): with
$f_{00} = M_0$, completing the square and rounding $m_0$ gives $M_0 \le \tfrac14 M_0 + \gamma_{n-1}(D/M_0)^{1/(n-1)}$. -/
@[kb "cassels1978" "Ch. 12, §2, Thm. 2.1, proof (i) (Hermite), pp. 260–261"]
theorem hermiteConstantBound_hermite {n : ℕ} (hn : 0 < n) :
    HermiteConstantBound n ((4 / 3 : ℝ) ^ (((n : ℝ) - 1) / 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro F hF
  obtain ⟨m, hm, hb⟩ := hermite_pow_bound k F hF
  refine ⟨m, hm, ?_⟩
  obtain ⟨hs, hp⟩ := (posDef_iff F).1 hF
  have hv : 0 ≤ val F (cast m) := by
    refine (hp _ ?_).le
    intro h; apply hm; funext i; have := congrFun h i; simpa [cast] using this
  have hD : 0 ≤ F.det := hF.det_pos.le
  have hq : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ ((k + 1).choose 2) := by positivity
  have hkn : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 := Real.rpow_le_rpow (by positivity) hb (inv_nonneg.2 (Nat.cast_nonneg (k + 1)) : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hv (Nat.succ_ne_zero k), Real.mul_rpow hq hD] at h1
  rw [one_div]
  refine h1.trans (le_of_eq ?_)
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Nat.cast_choose_two]
  congr 1
  push_cast
  field_simp

end QuadFormsKB.Reduction
