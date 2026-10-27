/-
# Cassels, Chapter 9, §3: the finiteness theorem (Theorem 1.1) and orbits of representations (Lemma 6.1)

**Layer:** classically integral forms `f : QuadForm ℤ n` (`IsClassicallyIntegral`) with Cassels' determinant
$d = \det(f_{ij}) = \det H/2^n$; $\mathrm{GL}_n(\mathbb Z)$-classes `QClass n`; orbits of representations under the
proper automorphs (`SameOrbit`, `orbitSetoid`, `Ch9Sec6.lean`).

**Proves**
* Theorem 1.1 (`finite_classes_of_det`): for $n \ge 1$ and $d \ne 0$ there are only finitely many classes of
  classically integral forms in $n$ variables of determinant $d$ — definite or indefinite (the library had the positive
  definite case, `Siegel.exists_intEquiv_hessian_bounded`, and O'Meara's lattice version 103:4);
* Lemma 6.1 (`finite_orbits`): for a regular classically integral form $f$ and $a \ne 0$ the representations of $a$ fall
  into finitely many orbits under $O^{+}(f)$ (the library had the positive definite case, `finite_orbits_of_posDef`).

*Proof (Cassels', pp. 135–136 and 144–145):* induction on $n$. By Lemma 3.1 (`exists_value_ne_zero_le`) $f$ takes a
value $h = f(\mathbf a) \ne 0$, $\lvert h\rvert \le C_n\lvert d\rvert^{1/n}$, at a primitive $\mathbf a$ (divide by the
gcd); complete $\mathbf a$ to a basis (Lemma 2.1, Cor.), so $f \sim f^{*}$ with $f^{*}_{11} = h$; completing the
square, $hf^{*} = (hx_1 + \dots)^2 + g(x_2, \dots, x_n)$ with $g$ classically integral of determinant $h^{n-2}d$ (3.5),
(3.6); by induction $g$ may be taken from a finite set, and then a substitution $x_1 \mapsto x_1 + \sum u_jx_j$ makes
$\lvert f^{*}_{1j}\rvert \le \lvert h\rvert/2$; so $f^{*}$ lies in a finite set. For Lemma 6.1 the same reduction,
applied to a basis $b = b_1, b_2, \dots, b_n$ of determinant $+1$ through a primitive representation $b$, puts
$f(x_1b_1 + \dots + x_nb_n)$ in a finite set, and two representations giving the same form are in one orbit.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec3
import QuadFormsKB.Literature.Cassels.Ch9Sec6

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

section Reduction

variable {m : ℕ}

/-- The block matrix $\begin{pmatrix}1 & u^{\mathsf T}\\ 0 & S\end{pmatrix}$ (a substitution fixing $e_0$). -/
def liftU (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℤ) (Fin.cases (motive := fun _ => ℤ) 1 u j)
    (fun i' => Fin.cases (motive := fun _ => ℤ) 0 (fun j' => S i' j') j) i

/-- The $(0,0)$ entry of the block matrix `liftU u S` is $1$. -/
@[simp] theorem liftU_zero_zero (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) : liftU u S 0 0 = 1 := by
  simp [liftU]

/-- The $(0, j+1)$ entry of `liftU u S` is $u_j$. -/
@[simp] theorem liftU_zero_succ (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) (j : Fin m) :
    liftU u S 0 j.succ = u j := by
  simp [liftU]

/-- The $(i+1, 0)$ entry of `liftU u S` is $0$. -/
@[simp] theorem liftU_succ_zero (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) (i : Fin m) :
    liftU u S i.succ 0 = 0 := by
  simp [liftU]

/-- The $(i+1, j+1)$ entry of `liftU u S` is $S_{ij}$. -/
@[simp] theorem liftU_succ_succ (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    liftU u S i.succ j.succ = S i j := by
  simp [liftU]

/-- $\det\begin{pmatrix}1 & u^{\mathsf T}\\ 0 & S\end{pmatrix} = \det S$. -/
theorem det_liftU (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) : (liftU u S).det = S.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [liftU_succ_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, liftU_zero_zero, Fin.succAbove_zero]
  congr 1

/-- The Schur-type complement $G_{ij} = F_{00}F_{i+1,j+1} - F_{i+1,0}F_{j+1,0}$. -/
def schurG (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => F 0 0 * F i.succ j.succ - F i.succ 0 * F j.succ 0

/-- Conjugation by `liftU` keeps the $(0,0)$ entry. -/
theorem conj_zero_zero (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (u : Fin m → ℤ)
    (S : Matrix (Fin m) (Fin m) ℤ) : ((liftU u S)ᵀ * F * liftU u S) 0 0 = F 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The first column of the conjugate. -/
theorem conj_succ_zero (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (u : Fin m → ℤ)
    (S : Matrix (Fin m) (Fin m) ℤ) (i : Fin m) :
    ((liftU u S)ᵀ * F * liftU u S) i.succ 0 = u i * F 0 0 + ∑ k, S k i * F k.succ 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The first row of the conjugate. -/
theorem conj_zero_succ (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (u : Fin m → ℤ)
    (S : Matrix (Fin m) (Fin m) ℤ) (j : Fin m) :
    ((liftU u S)ᵀ * F * liftU u S) 0 j.succ = F 0 0 * u j + ∑ l, F 0 l.succ * S l j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The lower right block of the conjugate. -/
theorem conj_succ_succ (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (u : Fin m → ℤ)
    (S : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    ((liftU u S)ᵀ * F * liftU u S) i.succ j.succ = u i * (F 0 0 * u j + ∑ l, F 0 l.succ * S l j) +
      ∑ k, S k i * (F k.succ 0 * u j + ∑ l, F k.succ l.succ * S l j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
  simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, mul_assoc]
  rw [Finset.sum_comm (f := fun x y => S y i * (F y.succ x.succ * S x j))]
  ring

/-- The Schur complement transforms by $S$: $G(U^{\mathsf T}FU) = S^{\mathsf T}G(F)S$. -/
theorem schurG_conj {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) (u : Fin m → ℤ)
    (S : Matrix (Fin m) (Fin m) ℤ) :
    schurG ((liftU u S)ᵀ * F * liftU u S) = Sᵀ * schurG F * S := by
  ext i j
  have hs : ∀ l : Fin m, F 0 l.succ = F l.succ 0 := fun l => hF.apply _ _ ▸ rfl
  simp only [schurG, Matrix.of_apply, conj_zero_zero, conj_succ_succ, conj_succ_zero, hs]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]
  have hc : ∑ x, F x.succ 0 * S x j = ∑ k, S k j * F k.succ 0 :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  have h2 : ∑ k, S k i * (F k.succ 0 * u j + ∑ l, F k.succ l.succ * S l j) =
      (∑ k, S k i * F k.succ 0) * u j + ∑ k, S k i * ∑ l, F k.succ l.succ * S l j := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  have hQ : ∑ x, (∑ y, S y i * (F 0 0 * F y.succ x.succ)) * S x j =
      F 0 0 * ∑ k, S k i * ∑ l, F k.succ l.succ * S l j := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hC : ∑ x, (∑ y, S y i * (F y.succ 0 * F x.succ 0)) * S x j =
      (∑ k, S k i * F k.succ 0) * ∑ k, S k j * F k.succ 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hc, h2, hQ, hC]
  ring

/-- The elimination matrix $\begin{pmatrix}1 & 0\\ -b & hI\end{pmatrix}$, $h = F_{00}$, $b_i = F_{i+1,0}$. -/
def elimMat (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℤ) (Fin.cases (motive := fun _ => ℤ) 1 (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℤ) (-F i'.succ 0) (fun j' => if i' = j' then F 0 0 else 0) j) i

/-- $\det(\mathrm{elimMat}\,F) = F_{00}^m$. -/
theorem det_elimMat (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : (elimMat F).det = F 0 0 ^ m := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h0 : ∀ j : Fin m, elimMat F 0 j.succ = 0 := fun j => by simp [elimMat]
  have h00 : elimMat F 0 0 = 1 := by simp [elimMat]
  simp only [h0, h00, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero]
  have : (elimMat F).submatrix Fin.succ Fin.succ = Matrix.diagonal (fun _ => F 0 0) := by
    ext i j
    by_cases hij : i = j <;> simp [elimMat, hij]
  rw [this, Matrix.det_diagonal]
  simp

/-- $\det(\mathrm{elimMat}\,F\cdot F) = F_{00}\det G(F)$ for symmetric $F$. -/
theorem det_elimMat_mul {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) :
    (elimMat F * F).det = F 0 0 * (schurG F).det := by
  have hs : ∀ l : Fin m, F 0 l.succ = F l.succ 0 := fun l => hF.apply _ _ ▸ rfl
  have c0 : ∀ i : Fin m, (elimMat F * F) i.succ 0 = 0 := fun i => by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, elimMat]; ring
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [c0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero]
  have e00 : (elimMat F * F) 0 0 = F 0 0 := by simp [Matrix.mul_apply, Fin.sum_univ_succ, elimMat]
  have : (elimMat F * F).submatrix Fin.succ Fin.succ = schurG F := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, elimMat, schurG, hs]
    ring
  rw [e00, this]

/-- **Cassels (3.5)–(3.6):** for symmetric $F$ of size $k+2$ with $F_{00} \ne 0$,
$\det G(F) = F_{00}^{k}\det F$. -/
theorem det_schurG {k : ℕ} {F : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ} (hF : F.IsSymm) (h0 : F 0 0 ≠ 0) :
    (schurG F).det = F 0 0 ^ k * F.det := by
  have h1 := det_elimMat_mul hF
  rw [Matrix.det_mul, det_elimMat] at h1
  apply mul_left_cancel₀ h0
  rw [← h1]
  ring

/-- Rebuild $F$ from $(h, b, G)$: $F_{00} = h$, $F_{0,j+1} = F_{j+1,0} = b_j$, $F' = (G + bb^{\mathsf T})/h$. -/
def rebuild (h : ℤ) (b : Fin m → ℤ) (G : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℤ) (Fin.cases (motive := fun _ => ℤ) h b j)
    (fun i' => Fin.cases (motive := fun _ => ℤ) (b i') (fun j' => (G i' j' + b i' * b j') / h) j) i

/-- A symmetric $F$ is determined by $(F_{00}, F_{\cdot 0}, G(F))$ when $F_{00} \ne 0$. -/
theorem eq_rebuild {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} {h : ℤ} {b : Fin m → ℤ}
    {G : Matrix (Fin m) (Fin m) ℤ} (hF : F.IsSymm) (hh : h ≠ 0) (h00 : F 0 0 = h)
    (hb : ∀ i, F i.succ 0 = b i) (hG : schurG F = G) : F = rebuild h b G := by
  have hs : ∀ l : Fin m, F 0 l.succ = F l.succ 0 := fun l => hF.apply _ _ ▸ rfl
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [rebuild, h00]
  · simp [rebuild, hs, hb]
  · simp [rebuild, hb]
  · have := congrFun (congrFun hG i) j
    simp only [schurG, Matrix.of_apply, h00, hb] at this
    simp only [rebuild, Matrix.of_apply, Fin.cases_succ]
    rw [← this]
    simp [hh]

/-- Conjugation by `liftU` preserves symmetry. -/
theorem isSymm_conj_liftU {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hF : F.IsSymm) (u : Fin m → ℤ)
    (S : Matrix (Fin m) (Fin m) ℤ) : ((liftU u S)ᵀ * F * liftU u S).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hF.eq, Matrix.mul_assoc]

/-- **The reduction step (Cassels, pp. 135–136):** if the $G$-parts of the matrices of size $k+2$ with
$F_{00} = h$ and determinant $D$ are reduced (by $\mathrm{SL}_{k+1}(\mathbb Z)$) into a finite set $S_0$, then
$F$ itself is reduced, by a $U$ with $Ue_0 = e_0$, $\det U = 1$, into a finite set. -/
theorem exists_finite_reduction (k : ℕ) (h D : ℤ) (hh : h ≠ 0)
    {S0 : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)} (hS0 : S0.Finite)
    (hcov : ∀ G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ, G.IsSymm → G.det = h ^ k * D →
      ∃ G0 ∈ S0, ∃ V : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ, V.det = 1 ∧ Vᵀ * G * V = G0) :
    ∃ S1 : Set (Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ), S1.Finite ∧
      ∀ F : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ, F.IsSymm → F.det = D → F 0 0 = h →
        ∃ F1 ∈ S1, ∃ U : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ, U.det = 1 ∧
          (∀ i, U i 0 = if i = 0 then 1 else 0) ∧ Uᵀ * F * U = F1 := by
  refine ⟨(fun p : (Fin (k + 1) → ℤ) × Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ => rebuild h p.1 p.2) ''
    ((Set.pi Set.univ (fun _ => Set.Ico (0 : ℤ) |h|)) ×ˢ S0), ?_, ?_⟩
  · exact ((Set.Finite.pi fun _ => Set.finite_Ico _ _).prod hS0).image _
  intro F hF hD h00
  have hG : (schurG F).IsSymm := by
    ext i j
    simp only [schurG, Matrix.transpose_apply, Matrix.of_apply, hF.apply]
    ring
  have hdet : (schurG F).det = h ^ k * D := by rw [det_schurG hF (h00 ▸ hh), h00, hD]
  obtain ⟨G0, hG0, V, hV, hVG⟩ := hcov _ hG hdet
  set c : Fin (k + 1) → ℤ := fun j => ∑ l, F l.succ 0 * V l j with hc
  set u : Fin (k + 1) → ℤ := fun j => -(c j / h) with hu
  have hs : ∀ l : Fin (k + 1), F 0 l.succ = F l.succ 0 := fun l => hF.apply _ _ ▸ rfl
  have hb0 : ∀ j, ((liftU u V)ᵀ * F * liftU u V) 0 j.succ = c j % h := by
    intro j
    rw [conj_zero_succ, h00]
    simp only [hs, hu, hc, Int.emod_def]
    ring
  refine ⟨_, ⟨(fun j => c j % h, G0), ⟨fun j _ => ⟨Int.emod_nonneg _ hh, (Int.emod_lt _ hh).trans_eq (Int.natCast_natAbs h)⟩, hG0⟩, rfl⟩,
    liftU u V, by rw [det_liftU, hV], fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> simp
  · symm
    show _ = (liftU u V)ᵀ * F * liftU u V
    have hsym := isSymm_conj_liftU hF u V
    refine (eq_rebuild hsym hh ?_ ?_ ?_).symm
    · rw [conj_zero_zero, h00]
    · intro i
      rw [← hsym.apply, hb0]
    · rw [schurG_conj hF, ← hVG]

/-- Conjugation preserves symmetry. -/
theorem isSymm_conj {n : ℕ} {F : Matrix (Fin n) (Fin n) ℤ} (hF : F.IsSymm) (P : Matrix (Fin n) (Fin n) ℤ) :
    (Pᵀ * F * P).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hF.eq, Matrix.mul_assoc]

/-- The value $x^{\mathsf T}(P^{\mathsf T}FP)x = (Px)^{\mathsf T}F(Px)$. -/
theorem qform_conj {n : ℕ} (F P : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    x ⬝ᵥ (Pᵀ * F * P) *ᵥ x = (P *ᵥ x) ⬝ᵥ F *ᵥ (P *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Diagonal entries of a conjugate: $(P^{\mathsf T}FP)_{ii} = p_i^{\mathsf T}Fp_i$ for the $i$-th column $p_i$. -/
theorem conj_diag {n : ℕ} (F P : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (Pᵀ * F * P) i i = (P *ᵥ Pi.single i 1) ⬝ᵥ F *ᵥ (P *ᵥ Pi.single i 1) := by
  rw [← qform_conj]
  simp [Matrix.mulVec_single, single_dotProduct]

/-- $\det(P^{\mathsf T}FP) = \det F$ when $\det P = 1$. -/
theorem det_conj_of_det_one {n : ℕ} (F P : Matrix (Fin n) (Fin n) ℤ) (hP : P.det = 1) :
    (Pᵀ * F * P).det = F.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hP]
  ring

/-- A determinant-one integer matrix as an element of $\mathrm{GL}_n(\mathbb Z)$. -/
def glOfDet {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (h : T.det = 1) : GL (Fin n) ℤ where
  val := T
  inv := T.adjugate
  val_inv := by rw [Matrix.mul_adjugate, h, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, h, one_smul]

/-- The underlying matrix of `glOfDet T h` is $T$. -/
@[simp] theorem glOfDet_val {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (h : T.det = 1) :
    (glOfDet T h).val = T := rfl

/-- A symmetric integer matrix $A$ gives a form with Hessian $A + A$ and value $x^{\mathsf T}Ax$. -/
theorem exists_form_of_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) :
    ∃ g : QuadForm ℤ n, g.hessian = A + A ∧ ∀ x, g.eval x = x ⬝ᵥ A *ᵥ x := by
  obtain ⟨g, hg⟩ := exists_hessian_eq (A + A) (hA.add hA) (fun i => ⟨A i i, by simp⟩)
  refine ⟨g, hg, fun x => ?_⟩
  have h := LocalDensity.two_mul_eval_eq_hessian g x
  rw [hg, Matrix.add_mulVec, dotProduct_add] at h
  omega

/-- If $f(x) = x^{\mathsf T}Ax$ with $A$ symmetric then the Hessian of $f$ is $A + A$. -/
theorem hessian_eq_of_eval {n : ℕ} {f : QuadForm ℤ n} {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hf : ∀ x, f.eval x = x ⬝ᵥ A *ᵥ x) : f.hessian = A + A := by
  obtain ⟨g, hg, hge⟩ := exists_form_of_symm hA
  have := (eval_mulVec_eq_iff_hessian f g 1).mp (fun x => by rw [Matrix.one_mulVec, hf, hge])
  simpa [hg] using this

/-- A classically integral form is $x \mapsto x^{\mathsf T}Ax$ with $A$ symmetric and Hessian $A + A$. -/
theorem exists_symm_of_classicallyIntegral {n : ℕ} {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, A.IsSymm ∧ (∀ x, f.eval x = x ⬝ᵥ A *ᵥ x) ∧ f.hessian = A + A := by
  obtain ⟨A, hA, h⟩ := hf
  exact ⟨A, hA, h, hessian_eq_of_eval hA h⟩

/-- $\det(A + A) = 2^n\det A$. -/
theorem det_add_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : (A + A).det = 2 ^ n * A.det := by
  rw [← two_smul ℤ A, Matrix.det_smul]
  simp

/-- Forms with Hessians $A + A$, $A' + A'$ and $A' = T^{\mathsf T}AT$ ($\det T = 1$) are integrally equivalent. -/
theorem intEquiv_of_conj {n : ℕ} {f g : QuadForm ℤ n} {A A' T : Matrix (Fin n) (Fin n) ℤ}
    (hf : f.hessian = A + A) (hg : g.hessian = A' + A') (hT : T.det = 1) (hTA : Tᵀ * A * T = A') :
    IntEquiv f g := by
  refine ⟨glOfDet T hT, (eval_mulVec_eq_iff_hessian f g T).mpr ?_⟩
  rw [hf, hg, ← hTA, Matrix.mul_add, Matrix.add_mul]

/-- Every nonzero integer vector is a multiple of a primitive one. -/
theorem exists_primitive_scale {n : ℕ} {a : Fin n → ℤ} (ha : a ≠ 0) :
    ∃ e : ℤ, ∃ k : Fin n → ℤ, e ≠ 0 ∧ Finset.univ.gcd k = 1 ∧ a = e • k := by
  have he0 : Finset.univ.gcd a ≠ 0 := by
    intro h0
    apply ha
    rw [Finset.gcd_eq_zero_iff] at h0
    exact funext fun i => h0 i (Finset.mem_univ i)
  choose k hk using fun i => Finset.gcd_dvd (s := Finset.univ) (f := a) (Finset.mem_univ i)
  have hfun : a = fun i => Finset.univ.gcd a * k i := funext hk
  refine ⟨Finset.univ.gcd a, k, he0, ?_, funext fun i => by rw [Pi.smul_apply, smul_eq_mul]; exact hk i⟩
  have h1 := Finset.gcd_mul_left (s := Finset.univ) (a := Finset.univ.gcd a) (f := k)
  rw [Finset.normalize_gcd, ← hfun] at h1
  exact (mul_eq_left₀ he0).mp h1.symm

/-- **Value bound for primitive vectors:** for $\det F = D \ne 0$ there is a primitive $a$ with
$0 < \lvert a^{\mathsf T}Fa\rvert \le B(n, D)$ (Lemma 3.1 and division by the gcd). -/
theorem exists_primitive_value (n : ℕ) (hn : 1 ≤ n) (D : ℤ) (hD : D ≠ 0) :
    ∃ B : ℤ, ∀ F : Matrix (Fin n) (Fin n) ℤ, F.IsSymm → F.det = D →
      ∃ a : Fin n → ℤ, Finset.univ.gcd a = 1 ∧ a ⬝ᵥ F *ᵥ a ≠ 0 ∧ |a ⬝ᵥ F *ᵥ a| ≤ B := by
  obtain ⟨C, hC⟩ := exists_value_ne_zero_le n hn
  refine ⟨⌈C * |(D : ℝ)| ^ ((1 : ℝ) / n)⌉, fun F hF hFD => ?_⟩
  obtain ⟨g, hgH, hge⟩ := exists_form_of_symm hF
  have hint : IsClassicallyIntegral g := ⟨F, hF, hge⟩
  have hdet : g.hessian.det = 2 ^ n * D := by rw [hgH, det_add_self, hFD]
  have hne : g.hessian.det ≠ 0 := by rw [hdet]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hD
  obtain ⟨a, ha0, hab⟩ := hC g hint hne
  have hgd : gramDet g = (D : ℝ) := by
    unfold gramDet
    rw [hdet]
    push_cast
    field_simp
  rw [hgd] at hab
  rw [hge] at ha0 hab
  have hane : a ≠ 0 := fun h => ha0 (by simp [h])
  obtain ⟨e, k, he, hk, hak⟩ := exists_primitive_scale hane
  have hq : a ⬝ᵥ F *ᵥ a = e ^ 2 * (k ⬝ᵥ F *ᵥ k) := by
    rw [hak]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hk0 : k ⬝ᵥ F *ᵥ k ≠ 0 := fun h => ha0 (by rw [hq, h, mul_zero])
  refine ⟨k, hk, hk0, ?_⟩
  have h1 : |k ⬝ᵥ F *ᵥ k| ≤ |a ⬝ᵥ F *ᵥ a| := by
    rw [hq, abs_mul, abs_pow]
    have : 1 ≤ |e| ^ 2 := by
      have := abs_pos.mpr he
      nlinarith
    nlinarith [abs_nonneg (k ⬝ᵥ F *ᵥ k)]
  have h2 : ((|k ⬝ᵥ F *ᵥ k| : ℤ) : ℝ) ≤ C * |(D : ℝ)| ^ ((1 : ℝ) / n) := by
    refine le_trans (Int.cast_le.mpr h1) ?_
    rw [Int.cast_abs]
    exact hab
  exact_mod_cast h2.trans (Int.le_ceil _)

end Reduction

/-- **Finiteness up to $\mathrm{SL}_n(\mathbb Z)$ (matrix form of Theorem 1.1):** the symmetric integer matrices of size
$k+1$ and determinant $D \ne 0$ are $\mathrm{SL}_{k+1}(\mathbb Z)$-reduced, $F \mapsto T^{\mathsf T}FT$, into a finite set. -/
theorem finite_reduction_SL : ∀ (k : ℕ) (D : ℤ), D ≠ 0 →
    ∃ S : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ), S.Finite ∧ (∀ F0 ∈ S, F0.IsSymm ∧ F0.det = D) ∧
      ∀ F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ, F.IsSymm → F.det = D →
        ∃ F0 ∈ S, ∃ T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ, T.det = 1 ∧ Tᵀ * F * T = F0
  | 0, D, hD => by
    refine ⟨{Matrix.of fun _ _ => D}, Set.finite_singleton _, ?_, ?_⟩
    · intro F0 hF0
      rw [Set.mem_singleton_iff] at hF0
      subst hF0
      refine ⟨?_, by simp⟩
      ext i j
      simp
    · intro F _ hFD
      have : F = Matrix.of fun _ _ => D := by
        ext i j
        fin_cases i
        fin_cases j
        simpa [Matrix.det_fin_one] using hFD
      exact ⟨_, Set.mem_singleton _, 1, by simp, by simp [this]⟩
  | k + 1, D, hD => by
    obtain ⟨B, hB⟩ := exists_primitive_value (k + 2) (by omega) D hD
    have key : ∀ h : ℤ, ∃ S1 : Set (Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ), S1.Finite ∧
        (h ≠ 0 → ∀ F : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ, F.IsSymm → F.det = D → F 0 0 = h →
          ∃ F1 ∈ S1, ∃ U : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ, U.det = 1 ∧
            (∀ i, U i 0 = if i = 0 then 1 else 0) ∧ Uᵀ * F * U = F1) := by
      intro h
      by_cases hh : h = 0
      · exact ⟨∅, Set.finite_empty, fun h' => absurd hh h'⟩
      · obtain ⟨S0, hS0, -, hcov⟩ := finite_reduction_SL k (h ^ k * D) (mul_ne_zero (pow_ne_zero _ hh) hD)
        obtain ⟨S1, hS1, hcov1⟩ := exists_finite_reduction k h D hh hS0 (fun G hG hGD => hcov G hG hGD)
        exact ⟨S1, hS1, fun _ => hcov1⟩
    choose S1 hS1 hcov1 using key
    refine ⟨(⋃ h ∈ Set.Icc (-B) B, S1 h) ∩ {F | F.IsSymm ∧ F.det = D}, ?_, fun F0 hF0 => hF0.2, ?_⟩
    · exact (Set.Finite.biUnion (Set.finite_Icc _ _) fun h _ => hS1 h).inter_of_left _
    · intro F hF hFD
      obtain ⟨a, ha1, ha0, haB⟩ := hB F hF hFD
      obtain ⟨T, hT, hTa⟩ := exists_sl_first_of_gcd (n := k + 2) (by omega) a ha1
      have hTa' : T.val *ᵥ Pi.single (0 : Fin (k + 2)) 1 = a := hTa
      have hFs := isSymm_conj hF T.val
      have h00 : (T.val ᵀ * F * T.val) 0 0 = a ⬝ᵥ F *ᵥ a := by
        rw [conj_diag, hTa']
      obtain ⟨F1, hF1, U, hU, -, hUF⟩ := hcov1 (a ⬝ᵥ F *ᵥ a) ha0 (T.val ᵀ * F * T.val) hFs
        (by rw [det_conj_of_det_one _ _ hT, hFD]) h00
      have hP : (T.val * U).det = 1 := by rw [Matrix.det_mul, hT, hU, mul_one]
      have hF1e : (T.val * U)ᵀ * F * (T.val * U) = F1 := by
        rw [← hUF, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      refine ⟨F1, ⟨Set.mem_biUnion (x := a ⬝ᵥ F *ᵥ a) (abs_le.mp haB) hF1, ?_, ?_⟩, T.val * U, hP, hF1e⟩
      · rw [← hF1e]; exact isSymm_conj hF _
      · rw [← hF1e, det_conj_of_det_one _ _ hP, hFD]

/-- **Cassels, Theorem 1.1** (Ch. 9, p. 128; proof §3, pp. 134–136): *let the integers $n \ge 1$ and $d \ne 0$ be
given. Then there are only finitely many equivalence classes of integral quadratic forms $f$ in $n$ variables
$\mathbf x = (x_1, \dots, x_n)$ with $d(f) = d$.* Integral in the classical sense; $d(f) = \det(f_{ij})$, i.e.
$\det H = 2^nd$. -/
@[kb "cassels1978" "Ch. 9, Thm. 1.1, p. 128 (proof: §3, pp. 134–136)"]
theorem finite_classes_of_det (n : ℕ) (hn : 1 ≤ n) {d : ℤ} (hd : d ≠ 0) :
    {c : QClass n | ∃ f : QuadForm ℤ n, classOf f = c ∧ IsClassicallyIntegral f ∧
      f.hessian.det = 2 ^ n * d}.Finite := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  classical
  obtain ⟨S, hS, hSp, hcov⟩ := finite_reduction_SL k d hd
  let φ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ → QClass (k + 1) := fun F0 =>
    if h : ∃ g : QuadForm ℤ (k + 1), g.hessian = F0 + F0 then classOf h.choose
    else classOf (QuadForm.ofUpper fun _ _ => 0)
  refine (hS.image φ).subset ?_
  rintro c ⟨f, rfl, hf, hdet⟩
  obtain ⟨A, hA, -, hH⟩ := exists_symm_of_classicallyIntegral hf
  have hAd : A.det = d := by
    rw [hH, det_add_self] at hdet
    exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) hdet
  obtain ⟨F0, hF0, T, hT, hTA⟩ := hcov A hA hAd
  refine ⟨F0, hF0, ?_⟩
  have hex : ∃ g : QuadForm ℤ (k + 1), g.hessian = F0 + F0 :=
    (exists_form_of_symm (hSp F0 hF0).1).imp fun g hg => hg.1
  simp only [φ, hex, ↓reduceDIte]
  exact (classOf_eq_classOf_iff.mpr (intEquiv_of_conj hH hex.choose_spec hT hTA)).symm

/-- $(ek)^{\mathsf T}A(ek) = e^2\,k^{\mathsf T}Ak$. -/
theorem dot_smul_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (e : ℤ) (k : Fin n → ℤ) :
    (e • k) ⬝ᵥ A *ᵥ (e • k) = e ^ 2 * (k ⬝ᵥ A *ᵥ k) := by
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- A finite set of representatives of the orbits gives finitely many orbits. -/
theorem finite_orbits_of_cover {n : ℕ} {f : QuadForm ℤ n} {a : ℤ} (S : Set (Fin n → ℤ)) (hS : S.Finite)
    (hsub : S ⊆ repSet f a) (hcov : ∀ b ∈ repSet f a, ∃ r ∈ S, SameOrbit f r b) :
    Finite (Quotient (orbitSetoid f a)) := by
  have := hS.to_subtype
  refine Finite.of_surjective (fun r : S => Quotient.mk (orbitSetoid f a) ⟨r.1, hsub r.2⟩) ?_
  intro q
  refine Quotient.inductionOn q fun b => ?_
  obtain ⟨r, hr, hro⟩ := hcov b.1 b.2
  exact ⟨⟨r, hr⟩, Quotient.sound hro⟩

/-- In one variable the representations of $a$ by a nondegenerate form are finite. -/
theorem repSet_finite_one {f : QuadForm ℤ 1} {A : Matrix (Fin 1) (Fin 1) ℤ}
    (hfA : ∀ x, f.eval x = x ⬝ᵥ A *ᵥ x) (hdA : A.det ≠ 0) (a : ℤ) : (repSet f a).Finite := by
  have hA0 : A 0 0 ≠ 0 := by rwa [Matrix.det_fin_one] at hdA
  refine ((Set.finite_Icc (-|a|) |a|).image (fun t : ℤ => fun _ : Fin 1 => t)).subset ?_
  intro b hb
  have hb' : f.eval b = a := hb
  rw [hfA] at hb'
  have h1 : b 0 * (A 0 0 * b 0) = a := by simpa [dotProduct, Matrix.mulVec] using hb'
  refine ⟨b 0, ?_, funext fun i => by fin_cases i; rfl⟩
  have h2 : 1 ≤ |A 0 0| := Int.one_le_abs hA0
  rw [Set.mem_Icc, ← abs_le]
  have h3 : |a| = |A 0 0| * (b 0 * b 0) := by
    rw [← h1, show b 0 * (A 0 0 * b 0) = A 0 0 * (b 0 * b 0) by ring, abs_mul,
      abs_of_nonneg (mul_self_nonneg (b 0))]
  by_cases hz : b 0 = 0
  · simp [hz]
  · have h4 := Int.one_le_abs hz
    nlinarith [abs_mul_abs_self (b 0), mul_nonneg (sub_nonneg.mpr h2) (mul_self_nonneg (b 0)),
      mul_nonneg (abs_nonneg (b 0)) (sub_nonneg.mpr h4)]

/-- Two parametrizations $P, P_0 \in \mathrm{SL}_n(\mathbb Z)$ with the same Gram matrix $P^{\mathsf T}AP$ give
vectors $P_0e$, $Pe$ in one orbit under $O^{+}(f)$ (Cassels, p. 145). -/
theorem sameOrbit_of_conj_eq {n : ℕ} {f : QuadForm ℤ n} {A : Matrix (Fin n) (Fin n) ℤ}
    (hfA : ∀ x, f.eval x = x ⬝ᵥ A *ᵥ x) (P P0 : GL (Fin n) ℤ) (hP : P.val.det = 1) (hP0 : P0.val.det = 1)
    (h : P.valᵀ * A * P.val = P0.valᵀ * A * P0.val) (e : Fin n → ℤ) :
    SameOrbit f (P0.val *ᵥ e) (P.val *ᵥ e) := by
  have key : ∀ y, f.eval (P.val *ᵥ y) = f.eval (P0.val *ᵥ y) := fun y => by
    rw [hfA, hfA, ← qform_conj, ← qform_conj, h]
  have hinv : P0.val * (P0⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv' : (P0⁻¹).val * P0.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (P0⁻¹).val.det = 1 := by
    have := congrArg Matrix.det hinv
    rwa [Matrix.det_mul, hP0, one_mul, Matrix.det_one] at this
  refine ⟨P * P0⁻¹, mem_autPlus_iff.mpr ⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · rw [Units.val_mul, Matrix.det_mul, hP, hdet, one_mul]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (P0⁻¹).val P0.val, hinv', Matrix.one_mulVec]

/-- **Primitive representations fall into finitely many orbits** (Cassels, p. 145). -/
theorem exists_primitive_orbit_reps {k : ℕ} {f : QuadForm ℤ (k + 2)} {A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ}
    (hA : A.IsSymm) (hfA : ∀ x, f.eval x = x ⬝ᵥ A *ᵥ x) (hdA : A.det ≠ 0) {a : ℤ} (ha : a ≠ 0) :
    ∃ R : Set (Fin (k + 2) → ℤ), R.Finite ∧ (∀ r ∈ R, f.eval r = a) ∧
      ∀ b : Fin (k + 2) → ℤ, Finset.univ.gcd b = 1 → f.eval b = a → ∃ r ∈ R, SameOrbit f r b := by
  classical
  obtain ⟨S0, hS0, -, hcov⟩ := finite_reduction_SL k (a ^ k * A.det) (mul_ne_zero (pow_ne_zero _ ha) hdA)
  obtain ⟨S1, hS1, hcov1⟩ := exists_finite_reduction k a A.det ha hS0 (fun G hG hGD => hcov G hG hGD)
  let Rep : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ → (Fin (k + 2) → ℤ) → Prop := fun F1 b =>
    ∃ P : GL (Fin (k + 2)) ℤ, P.val.det = 1 ∧ P.valᵀ * A * P.val = F1 ∧
      b = P.val *ᵥ Pi.single 0 1 ∧ f.eval b = a
  let ρ : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ → (Fin (k + 2) → ℤ) := fun F1 =>
    if h : ∃ b, Rep F1 b then h.choose else 0
  refine ⟨(ρ '' S1) ∩ {b | f.eval b = a}, (hS1.image ρ).inter_of_left _, fun r hr => hr.2, ?_⟩
  intro b hb hfb
  obtain ⟨T, hT, hTb⟩ := exists_sl_first_of_gcd (n := k + 2) (by omega) b hb
  have hTb' : T.val *ᵥ Pi.single (0 : Fin (k + 2)) 1 = b := hTb
  have hFs := isSymm_conj hA T.val
  have h00 : (T.valᵀ * A * T.val) 0 0 = a := by rw [conj_diag, hTb', ← hfA, hfb]
  obtain ⟨F1, hF1, U, hU, hUe, hUF⟩ := hcov1 (T.valᵀ * A * T.val) hFs (by rw [det_conj_of_det_one _ _ hT]) h00
  have hUe' : U *ᵥ Pi.single (0 : Fin (k + 2)) 1 = Pi.single 0 1 := by
    ext i
    rw [Matrix.mulVec_single_one]
    by_cases hi : i = 0
    · subst hi; simp [hUe]
    · simp [hUe, hi]
  have hRep : Rep F1 b := by
    refine ⟨T * glOfDet U hU, ?_, ?_, ?_, hfb⟩
    · simp [Matrix.det_mul, hT, hU]
    · rw [← hUF]
      simp only [Units.val_mul, glOfDet_val, Matrix.transpose_mul, Matrix.mul_assoc]
    · rw [Units.val_mul, glOfDet_val, ← Matrix.mulVec_mulVec, hUe', hTb']
  have hex : ∃ b, Rep F1 b := ⟨b, hRep⟩
  have hρ : Rep F1 (ρ F1) := by
    simp only [ρ, hex, ↓reduceDIte]
    exact hex.choose_spec
  obtain ⟨P0, hP0, hP0F, hρe, hρv⟩ := hρ
  obtain ⟨P, hP, hPF, hbe, -⟩ := hRep
  refine ⟨ρ F1, ⟨⟨F1, hF1, rfl⟩, hρv⟩, ?_⟩
  rw [hρe, hbe]
  exact sameOrbit_of_conj_eq hfA P P0 hP hP0 (hPF.trans hP0F.symm) _

/-- **Lemma 6.1 for $n \ge 2$.** -/
theorem finite_orbits_two {k : ℕ} {f : QuadForm ℤ (k + 2)} {A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ}
    (hA : A.IsSymm) (hfA : ∀ x, f.eval x = x ⬝ᵥ A *ᵥ x) (hdA : A.det ≠ 0) {a : ℤ} (ha : a ≠ 0) :
    Finite (Quotient (orbitSetoid f a)) := by
  classical
  have key : ∀ g : ℤ, ∃ R : Set (Fin (k + 2) → ℤ), R.Finite ∧
      (∀ r ∈ R, g ≠ 0 ∧ g ^ 2 ∣ a ∧ f.eval r = a / g ^ 2) ∧
      (g ≠ 0 → g ^ 2 ∣ a → ∀ b : Fin (k + 2) → ℤ, Finset.univ.gcd b = 1 → f.eval b = a / g ^ 2 →
        ∃ r ∈ R, SameOrbit f r b) := by
    intro g
    by_cases hg : g ≠ 0 ∧ g ^ 2 ∣ a
    · have hne : a / g ^ 2 ≠ 0 := by
        obtain ⟨c, hc⟩ := hg.2
        have : a / g ^ 2 = c := by rw [hc]; exact Int.mul_ediv_cancel_left _ (pow_ne_zero _ hg.1)
        rw [this]
        rintro rfl
        exact ha (by rw [hc, mul_zero])
      obtain ⟨R, hR, hRv, hRc⟩ := exists_primitive_orbit_reps hA hfA hdA hne
      exact ⟨R, hR, fun r hr => ⟨hg.1, hg.2, hRv r hr⟩, fun _ _ => hRc⟩
    · exact ⟨∅, Set.finite_empty, fun r hr => absurd hr (Set.notMem_empty r), fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
  choose R hRfin hRv hRc using key
  refine finite_orbits_of_cover (⋃ g ∈ Set.Icc (-|a|) |a|, (fun r => g • r) '' R g)
    (Set.Finite.biUnion (Set.finite_Icc _ _) fun g _ => (hRfin g).image _) ?_ ?_
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨g, -, r, hr, rfl⟩ := hx
    obtain ⟨-, ⟨c, hc⟩, hv⟩ := hRv g r hr
    show f.eval (g • r) = a
    rw [hfA, dot_smul_sq, ← hfA, hv]
    exact (Int.mul_ediv_cancel' ⟨c, hc⟩)
  · intro b hb
    have hb' : f.eval b = a := hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply ha
      rw [← hb', hfA]
      simp
    obtain ⟨e, k', he, hk, rfl⟩ := exists_primitive_scale hb0
    have hq : a = e ^ 2 * f.eval k' := by
      rw [← hb', hfA, hfA, dot_smul_sq]
    have hdvd : e ^ 2 ∣ a := ⟨_, hq⟩
    have hdiv : f.eval k' = a / e ^ 2 := by
      rw [hq]
      exact (Int.mul_ediv_cancel_left _ (pow_ne_zero _ he)).symm
    obtain ⟨r, hr, hro⟩ := hRc e he hdvd k' hk hdiv
    have hle : e ^ 2 ≤ |a| := Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr hdvd)
    have hee : |e| ≤ |a| := by
      have := Int.one_le_abs he
      nlinarith [sq_abs e]
    refine ⟨e • r, Set.mem_biUnion (abs_le.mp hee) ⟨r, hr, rfl⟩, ?_⟩
    obtain ⟨T, hT, rfl⟩ := hro
    exact ⟨T, hT, (Matrix.mulVec_smul _ _ _).symm⟩

/-- **Cassels, Lemma 6.1** (Ch. 9, p. 144): *let $a \ne 0$ be any integer. Then the set of representations of $a$
[by a regular integral form $f$] fall into finitely many orbits* (under the proper integral automorphs $O^{+}(f)$).
Classically integral $f$ with $\det H \ne 0$. -/
@[kb "cassels1978" "Ch. 9, Lemma 6.1, pp. 144–145"]
theorem finite_orbits {n : ℕ} {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) (hd : f.hessian.det ≠ 0)
    {a : ℤ} (ha : a ≠ 0) : Finite (Quotient (orbitSetoid f a)) := by
  obtain ⟨A, hA, hfA, hH⟩ := exists_symm_of_classicallyIntegral hf
  have hdA : A.det ≠ 0 := by
    intro h
    apply hd
    rw [hH, det_add_self, h, mul_zero]
  rcases n with _ | _ | k
  · exact finite_orbits_of_cover (repSet f a) (Set.toFinite _) (fun _ h => h)
      (fun b hb => ⟨b, hb, (equivalence_sameOrbit f).refl b⟩)
  · exact finite_orbits_of_cover (repSet f a) (repSet_finite_one hfA hdA a) (fun _ h => h)
      (fun b hb => ⟨b, hb, (equivalence_sameOrbit f).refl b⟩)
  · exact finite_orbits_two hA hfA hdA ha

end QuadFormsKB.Siegel
