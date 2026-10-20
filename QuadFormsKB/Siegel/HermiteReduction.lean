/-
# Hermite reduction of positive definite integral symmetric matrices

**Proves** Hermite's finiteness theorem in the form needed for `GenusFinite`: every positive definite integral
symmetric $n\times n$ matrix $A$ (`IsPosDefInt`) is $\mathrm{GL}_n(\mathbb{Z})$-congruent, $A \mapsto g^{\mathsf T}Ag$, to a
matrix all of whose entries are bounded by a number `entryBound n (det A)` depending only on $n$ and $\det A$
(`exists_reduced`).

**Proof (Hermite's reduction, by induction on $n$).** Write $A = \begin{pmatrix} h & r^{\mathsf T}\\ c & A'\end{pmatrix}$ and
let $S(A) = hA' - c\,r^{\mathsf T}$ (`schur`; $h$ times the Schur complement of $h$, so it is integral). Then
$h^{n-1}\det A = h\det S(A)$ (`det_schur`), $S(A)$ is positive definite (`IsPosDefInt.schur`), and $S$ transforms
under $g = \begin{pmatrix}1 & t^{\mathsf T}\\ 0 & u\end{pmatrix}$ (`blk`) by $S(g^{\mathsf T}Ag) = u^{\mathsf T}S(A)u$. One step:
1. move a value $h = A_{00}$ that is minimal over all $\mathrm{GL}_n(\mathbb{Z})$-congruent matrices to the corner (`exists_min`);
2. reduce $S(A)$ by the induction hypothesis (with $u$), and size-reduce the first row by $t$, $|2B_{0j}| \le h$
   (`exists_round`);
3. minimality gives $h \le B_{11}$ and so $3h^2 \le 4S_{00}$; with the induction bound $S_{00}^{n-1} \le C_{n-1}\det S$
   this is **Hermite's bound** $h^n \le C_n \det A$, $C_n = 4^{n-1}C_{n-1}$ (`hermC`), a crude form of
   $h \le (4/3)^{(n-1)/2}(\det A)^{1/n}$;
4. the entries $hB_{ij} = S_{ij} + B_{i0}B_{0j}$ ($i, j \ge 1$) are then bounded in terms of $n$ and $\det A$.

No convex-body theorem and no completion of a primitive vector to a basis are needed: the minimum in step 1 is taken over
first columns of unimodular matrices, which is well founded since the values are nonnegative integers.

*Related work (consulted, not imported):* lean-categories (D. Zack Garza),
`LeanCategories/Lattices/Valued/ReducedBasis.lean` (`exists_reduced_basis`, `genus_finite`), proved there for abstract
lattices via Minkowski's bound; Tau Ceti `IntegralLattice/PosDef` (Minkowski-reduced bases). Classical sources:
Cassels, *Rational Quadratic Forms*, Ch. 9, Thm. 1.1 and its reduction-theory proof [unverified]; Conway–Sloane, *SPLAG*,
Ch. 15 [unverified].
-/
import QuadFormsKB.Siegel.Genus

open Matrix

namespace QuadFormsKB.Siegel.Hermite

variable {m n : ℕ}

/-- **Entries of a congruence:** $(g^{\mathsf T}Ag)_{ij} = g_{\ast i}^{\mathsf T}\,A\,g_{\ast j}$, with $g_{\ast i}$ the $i$-th column of $g$. -/
theorem conj_apply (g A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (gᵀ * A * g) i j = (fun k => g k i) ⬝ᵥ (A *ᵥ fun k => g k j) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The tail of row $0$** of $A$: $r_j = A_{0,j+1}$, $j = 0, \dots, m-1$. -/
def rowT (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : Fin m → ℤ := fun j => A 0 j.succ
/-- **The tail of column $0$** of $A$: $c_i = A_{i+1,0}$, $i = 0, \dots, m-1$. -/
def colT (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : Fin m → ℤ := fun i => A i.succ 0

/-- **Block expansion of $x^{\mathsf T}Ay$** for $x = (a, x')$, $y = (b, y')$:
$x^{\mathsf T}Ay = A_{00}ab + a\,(r\cdot y') + b\,(x'\cdot c) + x'^{\mathsf T}A'y'$, with $r$ = `rowT A`, $c$ = `colT A`,
$A' = (A_{i+1,j+1})$. -/
theorem cons_bilin (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (a b : ℤ) (x y : Fin m → ℤ) :
    (Fin.cons a x : Fin (m + 1) → ℤ) ⬝ᵥ (A *ᵥ (Fin.cons b y : Fin (m + 1) → ℤ)) =
      A 0 0 * a * b + a * (rowT A ⬝ᵥ y) + b * (x ⬝ᵥ colT A) +
        x ⬝ᵥ (A.submatrix Fin.succ Fin.succ *ᵥ y) := by
  have h1 : ∀ i, (A *ᵥ (Fin.cons b y : Fin (m + 1) → ℤ)) i = A i 0 * b + ∑ j, A i j.succ * y j := by
    intro i; simp [mulVec, dotProduct, Fin.sum_univ_succ]
  rw [dotProduct, Fin.sum_univ_succ]
  simp only [h1, Fin.cons_zero, Fin.cons_succ, mul_add, Finset.sum_add_distrib]
  simp only [rowT, colT, dotProduct, mulVec, submatrix_apply, Finset.mul_sum]
  have e1 : ∑ i : Fin m, x i * (A i.succ 0 * b) = ∑ i, b * (x i * A i.succ 0) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]; ring

/-- **The scaled Schur complement** $S(A) = A_{00}A' - c\,r^{\mathsf T}$, $A' = (A_{i+1,j+1})_{i,j<m}$, $c$ = `colT A`, $r$ = `rowT A`:
$S(A)_{ij} = A_{00}A_{i+1,j+1} - A_{i+1,0}A_{0,j+1}$. It is $A_{00}$ times the Schur complement $A' - c\,A_{00}^{-1}r^{\mathsf T}$, hence
integral. -/
def schur (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  A 0 0 • A.submatrix Fin.succ Fin.succ - vecMulVec (colT A) (rowT A)

/-- $x^{\mathsf T}S(A)y = A_{00}\,x^{\mathsf T}A'y - (x\cdot c)(r\cdot y)$. -/
theorem schur_bilin (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (x y : Fin m → ℤ) :
    x ⬝ᵥ (schur A *ᵥ y) = A 0 0 * (x ⬝ᵥ (A.submatrix Fin.succ Fin.succ *ᵥ y)) -
      (x ⬝ᵥ colT A) * (rowT A ⬝ᵥ y) := by
  rw [schur, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, vecMulVec_mulVec,
    op_smul_eq_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring


/-- **Positive definite integral symmetric matrix:** $A \in M_n(\mathbb{Z})$ with $A^{\mathsf T} = A$ and
$x^{\mathsf T}Ax > 0$ for every nonzero $x \in \mathbb{Z}^n$. (No parity condition on the diagonal: Hessians $H$ of positive
definite forms are examples, `hessian_isPosDefInt`, and so are the matrices $S(A)$, which need not have even diagonal.) -/
def IsPosDefInt (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ ∀ x : Fin n → ℤ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

theorem IsPosDefInt.nonneg {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsPosDefInt A) (x : Fin n → ℤ) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hA.2 x hx).le

theorem cons_one_zero_ne : (Fin.cons 1 0 : Fin (m + 1) → ℤ) ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

theorem IsPosDefInt.pos00 {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : IsPosDefInt A) :
    0 < A 0 0 := by
  have := hA.2 _ cons_one_zero_ne
  rw [cons_bilin] at this
  simpa using this

theorem IsPosDefInt.colT_eq {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : IsPosDefInt A) :
    colT A = rowT A := funext fun i => hA.1.apply 0 i.succ

/-- **$S(A)$ is positive definite:** for $y \ne 0$ put $x = (-(r\cdot y), A_{00}y)$; then
$x^{\mathsf T}Ax = A_{00}\cdot y^{\mathsf T}S(A)y$. -/
theorem IsPosDefInt.schur {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : IsPosDefInt A) :
    IsPosDefInt (schur A) := by
  have hs := hA.colT_eq
  have hp := hA.pos00
  refine ⟨?_, fun y hy => ?_⟩
  · refine IsSymm.ext fun i j => ?_
    simp only [Hermite.schur, Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, vecMulVec_apply,
      smul_eq_mul, hs]
    rw [hA.1.apply j.succ i.succ]
    ring
  · have hx : (Fin.cons (-(rowT A ⬝ᵥ y)) (A 0 0 • y) : Fin (m + 1) → ℤ) ≠ 0 := by
      intro h0; apply hy; funext i
      have := congrFun h0 i.succ
      simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left hp.ne'
    have key := hA.2 _ hx
    rw [cons_bilin, hs] at key
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
    rw [dotProduct_comm y (rowT A)] at key
    rw [schur_bilin, hs, dotProduct_comm y (rowT A)]
    have : 0 < A 0 0 * (A 0 0 * (y ⬝ᵥ (A.submatrix Fin.succ Fin.succ *ᵥ y)) - (rowT A ⬝ᵥ y) * (rowT A ⬝ᵥ y)) := by
      linear_combination key
    exact pos_of_mul_pos_right this hp.le

/-- **Determinant of $S(A)$:** $A_{00}^{m}\det A = A_{00}\det S(A)$ ($A$ of size $m+1$). *Proof:* row operations
$E = \begin{pmatrix}1 & 0\\ -c & A_{00}I\end{pmatrix}$, $EA = \begin{pmatrix}A_{00} & r^{\mathsf T}\\ 0 & S(A)\end{pmatrix}$, Laplace expansion. -/
theorem det_schur (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) :
    A 0 0 ^ m * A.det = A 0 0 * (schur A).det := by
  set E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.of (Fin.cons (Pi.single 0 1)
    (fun i' => (Fin.cons (-(A i'.succ 0)) (A 0 0 • Pi.single i' 1) : Fin (m + 1) → ℤ)))
  have hE : E.det = A 0 0 ^ m := by
    rw [det_succ_row_zero, Fin.sum_univ_succ]
    have hsub : E.submatrix Fin.succ Fin.succ = A 0 0 • (1 : Matrix (Fin m) (Fin m) ℤ) := by
      ext i j
      simp [E, Pi.single_apply, one_apply, eq_comm]
    have h0 : ∀ j : Fin m, E 0 j.succ = 0 := fun j => by simp [E]
    simp only [h0, Fin.succAbove_zero, hsub, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [det_smul, det_one, Fintype.card_fin]
    simp [E]
  have hEA0 : ∀ j, (E * A) 0 j = A 0 j := by
    intro j; simp [E, Matrix.mul_apply, Pi.single_apply]
  have hEA : ∀ (i' : Fin m) j, (E * A) i'.succ j = -(A i'.succ 0) * A 0 j + A 0 0 * A i'.succ j := by
    intro i' j
    simp [E, Matrix.mul_apply, Fin.sum_univ_succ, Pi.single_apply]
  have h2 : (E * A).det = A 0 0 * (schur A).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    have hz : ∀ i : Fin m, (E * A) i.succ 0 = 0 := fun i => by rw [hEA]; ring
    have hsub : (E * A).submatrix Fin.succ Fin.succ = schur A := by
      ext i j
      simp only [submatrix_apply, hEA, Hermite.schur, Matrix.sub_apply, Matrix.smul_apply,
        vecMulVec_apply, colT, rowT, smul_eq_mul]
      ring
    simp [hz, hEA0, hsub]
  rw [← hE, ← det_mul, h2]


theorem dotProduct_conj' (g A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    x ⬝ᵥ ((gᵀ * A * g) *ᵥ x) = (g *ᵥ x) ⬝ᵥ (A *ᵥ (g *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x gᵀ, vecMul_transpose]

/-- Congruence $A \mapsto g^{\mathsf T}Ag$ by $g \in \mathrm{GL}_n(\mathbb{Z})$ preserves positive definiteness. -/
theorem IsPosDefInt.conj {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsPosDefInt A) (g : GL (Fin n) ℤ) :
    IsPosDefInt (g.valᵀ * A * g.val) := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, hA.1.eq, Matrix.mul_assoc]
  · rw [dotProduct_conj']
    refine hA.2 _ fun h0 => hx ?_
    have := congrArg (fun v => (g⁻¹).val *ᵥ v) h0
    simpa [mulVec_mulVec, ← Units.val_mul] using this

/-- $\det(g^{\mathsf T}Ag) = \det A$ for $g \in \mathrm{GL}_n(\mathbb{Z})$ ($\det g = \pm 1$). -/
theorem det_conj (A : Matrix (Fin n) (Fin n) ℤ) (g : GL (Fin n) ℤ) :
    (g.valᵀ * A * g.val).det = A.det := by
  have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  rw [det_mul, det_mul, det_transpose]
  have := Int.isUnit_mul_self hu
  linear_combination A.det * this

theorem conj_mul (A : Matrix (Fin n) (Fin n) ℤ) (g g' : GL (Fin n) ℤ) :
    (g * g').valᵀ * A * (g * g').val = g'.valᵀ * (g.valᵀ * A * g.val) * g'.val := by
  simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]

/-- **The block matrix** $\begin{pmatrix}1 & t^{\mathsf T}\\ 0 & u\end{pmatrix}$ (first column $e_0$). -/
def blk (t : Fin m → ℤ) (u : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of (Fin.cons (Fin.cons 1 t) (fun i => (Fin.cons 0 (u i) : Fin (m + 1) → ℤ)))

theorem blk_col0 (t : Fin m → ℤ) (u : Matrix (Fin m) (Fin m) ℤ) :
    (fun k => blk t u k 0) = (Fin.cons 1 0 : Fin (m + 1) → ℤ) := by
  funext k; cases k using Fin.cases <;> simp [blk]

theorem blk_colSucc (t : Fin m → ℤ) (u : Matrix (Fin m) (Fin m) ℤ) (j : Fin m) :
    (fun k => blk t u k j.succ) = (Fin.cons (t j) (fun i => u i j) : Fin (m + 1) → ℤ) := by
  funext k; cases k using Fin.cases <;> simp [blk]

theorem det_blk (t : Fin m → ℤ) (u : Matrix (Fin m) (Fin m) ℤ) : (blk t u).det = u.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin m, blk t u i.succ 0 = 0 := fun i => by simp [blk]
  have hsub : (blk t u).submatrix Fin.succ Fin.succ = u := by ext i j; simp [blk]
  simp only [h0, Fin.succAbove_zero, hsub, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp [blk]

/-- **Size reduction:** for $h > 0$ there is $t \in \mathbb{Z}$ with $|2(ht + a)| \le h$. -/
theorem exists_round (a : ℤ) {h : ℤ} (hh : 0 < h) : ∃ t : ℤ, |2 * (h * t + a)| ≤ h := by
  have h1 := Int.emod_nonneg a hh.ne'
  have h2 := Int.emod_lt_of_pos a hh
  have h3 := Int.emod_add_mul_ediv a h
  by_cases hc : 2 * (a % h) ≤ h
  · exact ⟨-(a / h), by rw [abs_le]; constructor <;> linarith⟩
  · exact ⟨-(a / h) - 1, by rw [abs_le]; constructor <;> linarith⟩

/-- **A minimal corner entry:** some $g_0 \in \mathrm{GL}_n(\mathbb{Z})$ minimizes $(g^{\mathsf T}Ag)_{00}$ (a nonnegative integer) over
all $g \in \mathrm{GL}_n(\mathbb{Z})$. -/
theorem exists_min (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hA : IsPosDefInt A) :
    ∃ g0 : GL (Fin (m + 1)) ℤ, ∀ g : GL (Fin (m + 1)) ℤ,
      (g0.valᵀ * A * g0.val) 0 0 ≤ (g.valᵀ * A * g.val) 0 0 := by
  let f : GL (Fin (m + 1)) ℤ → ℕ := fun g => ((g.valᵀ * A * g.val) 0 0).toNat
  have hnn : ∀ g : GL (Fin (m + 1)) ℤ, 0 ≤ (g.valᵀ * A * g.val) 0 0 := fun g => by
    rw [conj_apply]; exact hA.nonneg _
  refine ⟨Function.argmin f, fun g => ?_⟩
  have := Function.argmin_le f g
  have e1 := Int.toNat_of_nonneg (hnn (Function.argmin f))
  have e2 := Int.toNat_of_nonneg (hnn g)
  rw [← e1, ← e2]
  exact_mod_cast this


/-- **The constant in Hermite's bound** $h^n \le C_n\det A$: $C_0 = 1$, $C_{m+1} = 4^m C_m$ (so $C_n = 2^{n(n-1)}$). -/
def hermC : ℕ → ℤ
  | 0 => 1
  | m + 1 => 4 ^ m * hermC m

theorem hermC_pos : ∀ m, 0 < hermC m
  | 0 => one_pos
  | m + 1 => by have := hermC_pos m; simp only [hermC]; positivity

/-- **The entry bound of a reduced matrix**, by recursion on $n$: with $M = C_{m+1}d$,
$$E_{m+1}(d) = M^2 + M + \sum_{h=1}^{M} E_m(h^m d / h), \qquad E_0 = 0.$$
(The sum dominates $E_m(\det S)$ for the actual corner value $h \le M$, since $\det S = h^m d/h$.) -/
def entryBound : ℕ → ℤ → ℕ
  | 0, _ => 0
  | m + 1, d => (hermC (m + 1) * d).toNat ^ 2 + (hermC (m + 1) * d).toNat +
      ∑ h ∈ Finset.Icc (1 : ℤ) (hermC (m + 1) * d), entryBound m (h ^ m * d / h)

/-- Column $0$ of the transposition matrix of $(0\ 1)$ is $e_1$. -/
theorem swap_col0 (k : ℕ) :
    (fun i => (Equiv.swap (0 : Fin (k + 2)) 1).permMatrix ℤ i 0) = Pi.single 1 1 := by
  funext i
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [Equiv.swap_apply_eq_iff]

/-- **Hermite's reduction (finiteness form).** Every positive definite integral symmetric $n \times n$ matrix $A$ is
$\mathrm{GL}_n(\mathbb{Z})$-congruent to a matrix $B = g^{\mathsf T}Ag$ with
- (Hermite's bound) $B_{00}^{\,n} \le C_n\det A$ (`hermC`), and
- every entry $|B_{ij}| \le E_n(\det A)$ (`entryBound`), a bound depending only on $n$ and $\det A$.

See the module docstring for the proof. -/
@[kb "cassels1978" "Ch. 9, Thm. 1.1, proof by reduction (Hermite) [unverified]"]
theorem exists_reduced : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), IsPosDefInt A →
    ∃ g : GL (Fin n) ℤ,
      (∀ i : Fin n, (i : ℕ) = 0 → ((g.valᵀ * A * g.val) i i) ^ n ≤ hermC n * A.det) ∧
      ∀ i j, |(g.valᵀ * A * g.val) i j| ≤ entryBound n A.det
  | 0, A, _ => ⟨1, fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, A, hA => by
    obtain ⟨g0, hg0⟩ := exists_min A hA
    have hA1 : IsPosDefInt (g0.valᵀ * A * g0.val) := hA.conj g0
    have hdet1 : (g0.valᵀ * A * g0.val).det = A.det := det_conj A g0
    have hmin : ∀ g : GL (Fin (m + 1)) ℤ,
        (g0.valᵀ * A * g0.val) 0 0 ≤ (g.valᵀ * (g0.valᵀ * A * g0.val) * g.val) 0 0 := by
      intro g
      have := hg0 (g0 * g)
      rwa [conj_mul] at this
    suffices H : ∃ g : GL (Fin (m + 1)) ℤ,
        (∀ i : Fin (m + 1), (i : ℕ) = 0 →
          ((g.valᵀ * (g0.valᵀ * A * g0.val) * g.val) i i) ^ (m + 1) ≤ hermC (m + 1) * A.det) ∧
        ∀ i j, |(g.valᵀ * (g0.valᵀ * A * g0.val) * g.val) i j| ≤ entryBound (m + 1) A.det by
      obtain ⟨g, h1, h2⟩ := H
      exact ⟨g0 * g, by simpa only [conj_mul] using h1, by simpa only [conj_mul] using h2⟩
    generalize g0.valᵀ * A * g0.val = A1 at hmin hA1 hdet1
    rw [← hdet1]
    clear hdet1 hg0
    have hh : 0 < A1 0 0 := hA1.pos00
    have hS1 := hA1.schur
    have hdS := det_schur A1
    obtain ⟨u, hu0, hub⟩ := exists_reduced m (schur A1) hS1
    have ht : ∀ j : Fin m, ∃ t : ℤ, |2 * (A1 0 0 * t + rowT A1 ⬝ᵥ (fun k => u.val k j))| ≤ A1 0 0 :=
      fun j => exists_round _ hh
    choose t ht using ht
    have hdetg : IsUnit (blk t u.val).det := by
      rw [det_blk]; exact (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
    set g : GL (Fin (m + 1)) ℤ := Matrix.nonsingInvUnit _ hdetg with hgdef
    have hgv : g.val = blk t u.val := rfl
    have hB := hA1.conj g
    have hsymB : ∀ i j, (g.valᵀ * A1 * g.val) j i = (g.valᵀ * A1 * g.val) i j :=
      fun i j => hB.1.apply i j
    have hB00 : (g.valᵀ * A1 * g.val) 0 0 = A1 0 0 := by
      rw [conj_apply, hgv, blk_col0, cons_bilin]; simp
    have hB0j : ∀ j : Fin m, (g.valᵀ * A1 * g.val) 0 j.succ =
        A1 0 0 * t j + rowT A1 ⬝ᵥ (fun k => u.val k j) := by
      intro j; rw [conj_apply, hgv, blk_col0, blk_colSucc, cons_bilin]; simp
    have hBi0 : ∀ i : Fin m, (g.valᵀ * A1 * g.val) i.succ 0 =
        A1 0 0 * t i + (fun k => u.val k i) ⬝ᵥ colT A1 := by
      intro i; rw [conj_apply, hgv, blk_col0, blk_colSucc, cons_bilin]; simp
    have hBij : ∀ i j : Fin m, A1 0 0 * (g.valᵀ * A1 * g.val) i.succ j.succ -
        (g.valᵀ * A1 * g.val) i.succ 0 * (g.valᵀ * A1 * g.val) 0 j.succ =
          (u.valᵀ * schur A1 * u.val) i j := by
      intro i j
      rw [hBi0, hB0j, conj_apply g.val A1 i.succ j.succ, hgv, blk_colSucc, blk_colSucc, cons_bilin,
        conj_apply u.val, schur_bilin]
      ring
    clear_value g
    set B := g.valᵀ * A1 * g.val with hBdef
    set U := u.valᵀ * schur A1 * u.val with hUdef
    set h := A1 0 0 with hhdef
    have hmb : h ^ (m + 1) ≤ hermC (m + 1) * A1.det := by
      cases m with
      | zero =>
        have e0 : (schur A1).det = 1 := Matrix.det_isEmpty
        rw [e0, pow_zero, one_mul, mul_one] at hdS
        rw [hdS, show hermC (0 + 1) = 1 from rfl, one_mul, zero_add, pow_one]
      | succ k =>
        have h11 : h ≤ B (0 : Fin (k + 1)).succ (0 : Fin (k + 1)).succ := by
          have hP : IsUnit ((Equiv.swap (0 : Fin (k + 2)) 1).permMatrix ℤ).det := by
            rw [det_permutation]
            rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (k + 2)) 1)) with e | e <;>
              simp [e]
          have := hmin (g * Matrix.nonsingInvUnit _ hP)
          rw [conj_mul, conj_apply] at this
          have e2 : (fun i => (Matrix.nonsingInvUnit _ hP).val i 0) = Pi.single 1 1 := swap_col0 k
          rw [e2, mulVec_single_one] at this
          simpa using this
        have e := hBij 0 0
        have hb := ht 0
        rw [← hB0j] at hb
        have hsym := hsymB 0 (0 : Fin (k + 1)).succ
        have hU := hu0 0 rfl
        have hsq : (2 * B 0 (0 : Fin (k + 1)).succ) ^ 2 ≤ h ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have h3 : 3 * h ^ 2 ≤ 4 * U 0 0 := by
          rw [hsym] at e
          nlinarith [mul_le_mul_of_nonneg_left h11 hh.le]
        have hp1 : (3 * h ^ 2) ^ (k + 1) ≤ (4 * U 0 0) ^ (k + 1) :=
          pow_le_pow_left₀ (by positivity) h3 _
        rw [mul_pow, mul_pow] at hp1
        have hp2 : 4 ^ (k + 1) * U 0 0 ^ (k + 1) ≤ 4 ^ (k + 1) * (hermC (k + 1) * (schur A1).det) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
        have key : h ^ (k + 1) * (3 ^ (k + 1) * h ^ (k + 1 + 1)) ≤
            h ^ (k + 1) * (hermC (k + 1 + 1) * A1.det) := by
          have q1 : h ^ (k + 1) * (3 ^ (k + 1) * h ^ (k + 1 + 1)) =
              h * (3 ^ (k + 1) * (h ^ 2) ^ (k + 1)) := by ring
          have q2 : h ^ (k + 1) * (hermC (k + 1 + 1) * A1.det) =
              h * (4 ^ (k + 1) * (hermC (k + 1) * (schur A1).det)) := by
            rw [show hermC (k + 1 + 1) = 4 ^ (k + 1) * hermC (k + 1) from rfl]
            linear_combination (4 ^ (k + 1) * hermC (k + 1)) * hdS
          rw [q1, q2]
          exact mul_le_mul_of_nonneg_left (hp1.trans hp2) hh.le
        have h4 := le_of_mul_le_mul_left key (by positivity)
        have h3k : (1 : ℤ) ≤ 3 ^ (k + 1) := one_le_pow₀ (by norm_num)
        calc h ^ (k + 1 + 1) = 1 * h ^ (k + 1 + 1) := (one_mul _).symm
          _ ≤ 3 ^ (k + 1) * h ^ (k + 1 + 1) := mul_le_mul_of_nonneg_right h3k (by positivity)
          _ ≤ _ := h4
    have hM : h ≤ hermC (m + 1) * A1.det := le_trans (le_self_pow₀ (by omega) (by omega)) hmb
    have hS1det : (schur A1).det = h ^ m * A1.det / h := by
      rw [hdS]; exact (Int.mul_ediv_cancel_left _ hh.ne').symm
    have hb0 : ∀ j : Fin m, |B 0 j.succ| ≤ h := fun j => by
      have h1 := ht j
      rw [← hB0j] at h1
      rw [abs_mul] at h1
      have := abs_nonneg (B 0 j.succ)
      norm_num at h1
      linarith
    refine ⟨g, fun i hi => ?_, fun i j => ?_⟩
    · have : i = 0 := Fin.ext hi
      subst this; change B 0 0 ^ (m + 1) ≤ _; rw [hB00]; exact hmb
    · set M := hermC (m + 1) * A1.det with hMdef
      have hEq : (entryBound (m + 1) A1.det : ℤ) = ((M.toNat ^ 2 + M.toNat +
          ∑ h' ∈ Finset.Icc (1 : ℤ) M, entryBound m (h' ^ m * A1.det / h') : ℕ) : ℤ) := rfl
      have hMt : M ≤ (M.toNat : ℤ) := Int.self_le_toNat M
      have hsum : entryBound m (schur A1).det ≤
          ∑ h' ∈ Finset.Icc (1 : ℤ) M, entryBound m (h' ^ m * A1.det / h') := by
        rw [hS1det]
        exact Finset.single_le_sum (f := fun h' => entryBound m (h' ^ m * A1.det / h'))
          (fun _ _ => Nat.zero_le _) (Finset.mem_Icc.mpr ⟨by omega, hM⟩)
      generalize (∑ h' ∈ Finset.Icc (1 : ℤ) M, entryBound m (h' ^ m * A1.det / h')) = Ssum at hsum hEq
      have hsumZ : ((entryBound m (schur A1).det : ℕ) : ℤ) ≤ (Ssum : ℤ) := by exact_mod_cast hsum
      rw [hEq]; push_cast
      change |B i j| ≤ _
      have hhM : h * h ≤ (M.toNat : ℤ) ^ 2 := by nlinarith
      cases i using Fin.cases with
      | zero => cases j using Fin.cases with
        | zero => rw [hB00, abs_of_pos hh]; nlinarith
        | succ j => have := hb0 j; nlinarith
      | succ i => cases j using Fin.cases with
        | zero => rw [← hsymB]; have := hb0 i; nlinarith
        | succ j =>
          have e := hBij i j
          have hU := hub i j
          have hi0 : |B i.succ 0| ≤ h := by rw [← hsymB]; exact hb0 i
          have hj := hb0 j
          have h1 : |B i.succ j.succ| ≤ h * |B i.succ j.succ| :=
            le_mul_of_one_le_left (abs_nonneg _) (by omega)
          have h2 : h * |B i.succ j.succ| = |U i j + B i.succ 0 * B 0 j.succ| := by
            rw [← e, sub_add_cancel, abs_mul, abs_of_pos hh]
          have h3 : |U i j + B i.succ 0 * B 0 j.succ| ≤ |U i j| + |B i.succ 0| * |B 0 j.succ| :=
            (abs_add_le _ _).trans (by rw [abs_mul])
          have h4 : |B i.succ 0| * |B 0 j.succ| ≤ h * h := mul_le_mul hi0 hj (abs_nonneg _) hh.le
          linarith

end QuadFormsKB.Siegel.Hermite
