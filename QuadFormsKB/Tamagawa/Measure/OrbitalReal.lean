import QuadFormsKB.Tamagawa.Measure.SphereLeray
import QuadFormsKB.Tamagawa.Measure.LerayUnimodular
import QuadFormsKB.Tamagawa.SplitForm

/-!
# The archimedean orbital identity at a real place, any signature

Let $Q = \langle c\rangle \perp Q'$ (`splitForm c Q'`) be a nondegenerate real quadratic form in $m+1$ variables of any
signature, $c \ne 0$, with $e_0 = (1, 0, \dots, 0)$, $Q(e_0) = c$ and $e_0^\perp = \{x_0 = 0\}$ carrying $Q'$. The group
$SO(Q)(\mathbb R)$ acts on the sphere $S_c = \{Q = c\}$ (`SphereLeray.Sph`); the stabilizer of $e_0$ is
$SO(Q')(\mathbb R)$, embedded by $h \mapsto \mathrm{diag}(1, h)$ (`iota`). For any measurable section
$s : S_c \to SO(Q)(\mathbb R)$ of $g \mapsto ge_0$ (`SphSection`; one is built from reflections for $m \ge 1$, `sphSection`), the **archimedean
orbital identity** (`lerayMeasure_orbital`) is
$$\mu_Q = |2c|^{-m}\cdot(\mathrm{orb}_s)_*(\sigma_c \otimes \mu_{Q'}),\qquad \mathrm{orb}_s(x, h) = s(x)\,\mathrm{diag}(1, h),$$
with $\mu_Q$, $\mu_{Q'}$ the Leray measures of `LerayReal.lean` (`LerayReal.lerayMeasure`, Weil's $|dX/dc|$ in the coefficient
coordinates) and $\sigma_c$ the Leray measure $dx/dQ$ on $S_c$ (`SphereLeray.sig`). The constant $|2c|^{-m}$ is the
Jacobian of the coefficient coordinates: $c_{0,j} = 2B(x_0, x_j)$, $j = 1, \dots, m$, has derivative $2c$ in each of the
$m$ new directions. It is a power of an element of the ground field, so the product of the local constants over all
places is $1$ (product formula); this is the form in which the adelic induction consumes it.

**Proof (no Lie theory, no differential forms).** We reuse the fibration theorem
(`LerayReal.lerayMeasure_fibration`): $dX = \mu_Q \otimes \kappa_0$ under the chart $(g, b) \mapsto gb$,
$SO(Q) \times B \to M_{m+1}(\mathbb R)$, $B$ the slice group, for **slice data adapted to $e_0$**: $P = \mathrm{diag}(1, P')$
(`splitDiag`), so that $B = \{\left(\begin{smallmatrix} e^t & r \\ 0 & b'\end{smallmatrix}\right)\}$ with $b' \in B'$
(`bk`, `bk_surjective`). Then
1. (`lintegral_kappa0_split`) $\kappa_0 = |2c|^{m+1}\,e^{(m+1)t}\,dt \otimes dr \otimes \kappa_0'$: a change of variables in
   coefficient space, $\Phi_Q(b) = (ce^{2t},\ 2ce^tr,\ \Phi_{Q'}(b') + c\,rr^{\mathsf T})$ (`beta_bk`), with the explicit
   density $\theta(b) = |\det b|^{-1}$ of $\kappa_0$ (`det_act`);
2. (`lintegral_chart_split`) $dX = e^{(m+1)t}dt \otimes \nu_c \otimes dr \otimes (\mu_{Q'} \otimes \kappa_0')$, by
   splitting off the first column $x_0 = e^tx$ (polar coordinates, `SphereLeray.comap_pol`), rotating the other columns
   by $s(x)$ ($\det = 1$), splitting each into its top entry $r_j$ and the rest, and the fibration for $Q'$;
3. comparing the two decompositions of $dX$ on rectangles $A \times E$ and cancelling $\kappa_0(E) \in (0, \infty)$.
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.OrbitalReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.ArchSOMeasure
open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {m : ℕ}

/-! ### Block matrices $\left(\begin{smallmatrix} \beta & r \\ 0 & M\end{smallmatrix}\right)$ -/

/-- **The block upper triangular matrix** $\left(\begin{smallmatrix} \beta & r \\ 0 & M\end{smallmatrix}\right)$,
$(m+1)\times(m+1)$, with $r$ a row of length $m$ (index $0$ split off, as in `cornerMat`). -/
def rowMat (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (Fin.cases β r j) (fun i' => Fin.cases 0 (fun j' => M i' j') j) i

@[simp] theorem rowMat_zero_zero (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : rowMat β r M 0 0 = β := rfl
@[simp] theorem rowMat_zero_succ (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    rowMat β r M 0 j.succ = r j := rfl
@[simp] theorem rowMat_succ_zero (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    rowMat β r M i.succ 0 = 0 := rfl
@[simp] theorem rowMat_succ_succ (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    rowMat β r M i.succ j.succ = M i j := rfl

theorem cornerMat_eq_rowMat (c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : cornerMat c A = rowMat c 0 A := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem rowMat_mul (β β' : ℝ) (r r' : Fin m → ℝ) (M M' : Matrix (Fin m) (Fin m) ℝ) :
    rowMat β r M * rowMat β' r' M' = rowMat (β * β') (β • r' + r ᵥ* M') (M * M') := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct]

theorem rowMat_one : rowMat (1 : ℝ) 0 (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  rw [← cornerMat_eq_rowMat, cornerMat_one]

theorem det_rowMat (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : (rowMat β r M).det = β * M.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, rowMat_zero_zero, rowMat_succ_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  congr 1

/-- The transpose product $\left(\begin{smallmatrix} \beta & r \\ 0 & M\end{smallmatrix}\right)^{\mathsf T}
\left(\begin{smallmatrix} \beta' & r' \\ 0 & M'\end{smallmatrix}\right)$. -/
theorem transpose_rowMat_mul (β β' : ℝ) (r r' : Fin m → ℝ) (M M' : Matrix (Fin m) (Fin m) ℝ) :
    (rowMat β r M)ᵀ * rowMat β' r' M' = Matrix.of fun i j =>
      Fin.cases (Fin.cases (β * β') (fun j' => β * r' j') j)
        (fun i' => Fin.cases (r i' * β') (fun j' => r i' * r' j' + (Mᵀ * M') i' j') j) i := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-! ### The split form -/

theorem cornerMat_smul (a c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : a • cornerMat c A = cornerMat (a * c) (a • A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem gramMatrixR_splitForm (c : ℝ) (Q' : QuadForm ℝ m) :
    gramMatrixR (splitForm c Q') = cornerMat c (gramMatrixR Q') := by
  rw [gramMatrixR, hessian_splitForm, cornerMat_smul, gramMatrixR]
  congr 1; ring

theorem gramDetR_splitForm (c : ℝ) (Q' : QuadForm ℝ m) : gramDetR (splitForm c Q') = c * gramDetR Q' := by
  rw [gramDetR_eq_det, gramDetR_eq_det, gramMatrixR_splitForm, det_cornerMat]

theorem gramDetR_splitForm_ne_zero {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (hQ' : gramDetR Q' ≠ 0) :
    gramDetR (splitForm c Q') ≠ 0 := by
  rw [gramDetR_splitForm]; exact mul_ne_zero hc hQ'

/-- $u \mapsto (\mathrm{wt}_{ij}u_iu_j)_{i \le j}$: the coefficient coordinates of the form $(r\cdot y)^2$. -/
def wtOuter (r : Fin m → ℝ) : UIdx m → ℝ := fun p => wt p * (r p.1.1 * r p.1.2)

theorem continuous_wtOuter : Continuous (wtOuter : (Fin m → ℝ) → UIdx m → ℝ) :=
  continuous_pi fun p => continuous_const.mul ((continuous_apply _).mul (continuous_apply _))

/-- **$\Phi_Q$ on block matrices**: for $Q = \langle c\rangle \perp Q'$,
$\Phi_Q\left(\begin{smallmatrix} \beta & r \\ 0 & M\end{smallmatrix}\right) = (c\beta^2,\ 2c\beta r,\ \Phi_{Q'}(M) +
c\,(\mathrm{wt}_{ij}r_ir_j))$ in the coordinates $(0,0)$, $(0, j+1)$, $(i+1, j+1)$ (`asm`). -/
theorem phi_rowMat (c : ℝ) (Q' : QuadForm ℝ m) (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    phi (splitForm c Q') (rowMat β r M) = asm (c * β ^ 2) ((2 * c * β) • r) (phi Q' M + c • wtOuter r) := by
  have hAX : gramMatrixR (splitForm c Q') * rowMat β r M = rowMat (c * β) (c • r) (gramMatrixR Q' * M) := by
    rw [gramMatrixR_splitForm, cornerMat_eq_rowMat, rowMat_mul]
    congr 1
    · ext j; simp
  funext p
  obtain ⟨q, rfl⟩ := (eU m).surjective p
  rw [phi, wtU, Matrix.mul_assoc, hAX, transpose_rowMat_mul]
  rcases q with _ | j | q
  · rw [asm_zero]; simp [eU, wt]; ring
  · rw [asm_u]; simp [eU, wt, (Fin.succ_ne_zero j).symm]; ring
  · rw [asm_v]
    simp only [eU, Equiv.coe_fn_mk, Matrix.of_apply, Fin.cases_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      phi, wtU, wtOuter, Matrix.mul_assoc]
    have : wt (⟨(q.1.1.succ, q.1.2.succ), Fin.succ_le_succ_iff.mpr q.2⟩ : UIdx (m + 1)) = wt q := by
      simp [wt, Fin.succ_inj]
    rw [this]
    ring

/-! ### Slice data adapted to $e_0$ -/

theorem cornerMat_diagonal (c : ℝ) (d : Fin m → ℝ) :
    cornerMat c (diagonal d) = diagonal (Fin.cons c d : Fin (m + 1) → ℝ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Fin.succ_inj]

/-- **Slice data for $\langle c\rangle \perp Q'$ adapted to $e_0$**: $P = \mathrm{diag}(1, P')$, $d = (c, d')$. -/
def splitDiag {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (D' : Diag Q') : Diag (splitForm c Q') where
  P := blockGL D'.P
  d := Fin.cons c D'.d
  hd i := Fin.cases hc (fun i => D'.hd i) i
  hP := by
    rw [blockGL_val, gramMatrixR_splitForm, cornerMat_transpose, cornerMat_mul, cornerMat_mul, D'.hP,
      cornerMat_diagonal]
    simp

/-! ### The embedding $SO(Q') \to SO(Q)$ -/

theorem blockGL_mem_soReal (c : ℝ) {Q' : QuadForm ℝ m} (g : GL (Fin m) ℝ) (hg : g ∈ soReal Q') :
    blockGL g ∈ soReal (splitForm c Q') := by
  rw [mem_soReal_iff] at hg ⊢
  rw [blockGL_val, hessian_splitForm, cornerMat_transpose, cornerMat_mul, cornerMat_mul, hg.1, det_cornerMat, hg.2]
  simp

/-- **The embedding** $\iota : SO(Q')(\mathbb R) \to SO(Q)(\mathbb R)$, $h \mapsto \mathrm{diag}(1, h)$. -/
def iota (c : ℝ) (Q' : QuadForm ℝ m) : ArchSO Q' →* ArchSO (splitForm c Q') where
  toFun g := ArchSOInst.mk _ (blockGL (ArchSO.incl Q' g)) (blockGL_mem_soReal c _ (ArchSOInst.incl_mem Q' g))
  map_one' := by
    apply Subtype.ext; simp [ArchSOInst.mk]; rfl
  map_mul' a b := by
    apply Subtype.ext; simp [ArchSOInst.mk]; rfl

theorem mat_iota (c : ℝ) (Q' : QuadForm ℝ m) (g : ArchSO Q') :
    ArchSOInst.mat _ (iota c Q' g) = cornerMat 1 (ArchSOInst.mat Q' g) := rfl

theorem continuous_iota (c : ℝ) (Q' : QuadForm ℝ m) : Continuous (iota c Q') := by
  have hval : Continuous fun g : ArchSO Q' => cornerMat (1 : ℝ) (ArchSOInst.mat Q' g) := by
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp only [cornerMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact ((ArchSOInst.continuous_mat Q').matrix_elem i j)
  have hinv : Continuous fun g : ArchSO Q' => cornerMat (1 : ℝ) (ArchSOInst.mat Q' g⁻¹) := by
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp only [cornerMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact (((ArchSOInst.continuous_mat Q').comp continuous_inv).matrix_elem i j)
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨hval, ?_⟩) _
  convert hinv using 1
  funext g
  rw [← map_inv, blockGL_val, ArchSOInst.mat, map_inv]

theorem continuous_rowMat {X : Type*} [TopologicalSpace X] {β : X → ℝ} {r : X → Fin m → ℝ}
    {M : X → Matrix (Fin m) (Fin m) ℝ} (hβ : Continuous β) (hr : Continuous r) (hM : Continuous M) :
    Continuous fun x => rowMat (β x) (r x) (M x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rowMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
  · exact hβ
  · exact (continuous_apply j).comp hr
  · exact continuous_const
  · exact hM.matrix_elem i j

/-- The lower right $m \times m$ block of an $(m+1)\times(m+1)$ matrix. -/
def blockSub (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Matrix (Fin m) (Fin m) ℝ := X.submatrix Fin.succ Fin.succ

/-- The top row of an $(m+1)\times(m+1)$ matrix without its first entry. -/
def blockRow (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Fin m → ℝ := fun j => X 0 j.succ

theorem eq_rowMat {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hX : ∀ i : Fin m, X i.succ 0 = 0) :
    X = rowMat (X 0 0) (blockRow X) (blockSub X) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · rfl
  · show X i.succ 0 = 0; exact hX i
  · rfl

theorem blockSub_mul {X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hX : ∀ i : Fin m, X i.succ 0 = 0) :
    blockSub (X * Y) = blockSub X * blockSub Y := by
  ext i j
  simp only [blockSub, submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, hX, zero_mul, zero_add]

theorem col_zero_mul {X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hX : ∀ i : Fin m, X i.succ 0 = 0)
    (hY : ∀ i : Fin m, Y i.succ 0 = 0) (i : Fin m) : (X * Y) i.succ 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, hX, hY, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

theorem isUT_rowMat_iff (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    IsUT (rowMat β r M) ↔ IsUT M := by
  constructor
  · intro h i j hij
    exact h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
  · intro h i j hij
    refine Fin.cases (fun hij => absurd hij (Fin.not_lt_zero _)) (fun i hij => ?_) i hij
    refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j hij
    exact h i j (Fin.succ_lt_succ_iff.mp hj)

/-! ### The slice group of the adapted slice data -/

section Slice

variable {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (D' : Diag Q')

theorem conj_rowMat (P : GL (Fin m) ℝ) (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    ((blockGL P)⁻¹ : GL (Fin (m + 1)) ℝ).val * rowMat β r M * (blockGL P).val =
      rowMat β (r ᵥ* P.val) ((P⁻¹ : GL (Fin m) ℝ).val * M * P.val) := by
  rw [← map_inv, blockGL_val, blockGL_val, cornerMat_eq_rowMat, cornerMat_eq_rowMat, rowMat_mul, rowMat_mul]
  congr 1
  · ring
  · ext j; simp [vecMul, dotProduct]

theorem conj_rowMat' (P : GL (Fin m) ℝ) (β : ℝ) (r : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    (blockGL P).val * rowMat β r M * ((blockGL P)⁻¹ : GL (Fin (m + 1)) ℝ).val =
      rowMat β (r ᵥ* (P⁻¹ : GL (Fin m) ℝ).val) (P.val * M * (P⁻¹ : GL (Fin m) ℝ).val) := by
  rw [← map_inv, blockGL_val, blockGL_val, cornerMat_eq_rowMat, cornerMat_eq_rowMat, rowMat_mul, rowMat_mul]
  congr 1
  · ring
  · ext j; simp [vecMul, dotProduct]

theorem rowMat_mem_borelPos_iff {P : GL (Fin m) ℝ} {β : ℝ} {r : Fin m → ℝ} {M : Matrix (Fin m) (Fin m) ℝ}
    (x : GL (Fin (m + 1)) ℝ) (hx : x.val = rowMat β r M) (y : GL (Fin m) ℝ) (hy : y.val = M) :
    x ∈ sliceGroup (blockGL P) ↔ 0 < β ∧ y ∈ sliceGroup P := by
  rw [mem_sliceGroup, mem_sliceGroup]
  change (IsUT ((blockGL P)⁻¹ * x * blockGL P).val ∧ ∀ i, 0 < ((blockGL P)⁻¹ * x * blockGL P).val i i) ↔
    0 < β ∧ (IsUT (P⁻¹ * y * P).val ∧ ∀ i, 0 < (P⁻¹ * y * P).val i i)
  rw [Units.val_mul, Units.val_mul, hx, conj_rowMat, isUT_rowMat_iff, Units.val_mul, Units.val_mul, hy]
  constructor
  · rintro ⟨hU, hd⟩
    exact ⟨hd 0, hU, fun i => hd i.succ⟩
  · rintro ⟨hβ, hU, hd⟩
    exact ⟨hU, fun i => Fin.cases hβ (fun i => hd i) i⟩

/-- The matrix of $b = \left(\begin{smallmatrix} e^t & r \\ 0 & b'\end{smallmatrix}\right)$ as a unit. -/
def bkGL (p : ℝ × (Fin m → ℝ) × SliceB D'.P) : GL (Fin (m + 1)) ℝ where
  val := rowMat (Real.exp p.1) p.2.1 (SliceB.mat D'.P p.2.2)
  inv := rowMat (Real.exp (-p.1)) (-(Real.exp (-p.1)) • (p.2.1 ᵥ* SliceB.mat D'.P p.2.2⁻¹))
    (SliceB.mat D'.P p.2.2⁻¹)
  val_inv := by
    rw [rowMat_mul, SliceB.mat_mul_inv, ← Real.exp_add, add_neg_cancel, Real.exp_zero, smul_smul,
      mul_neg, ← Real.exp_add, add_neg_cancel, Real.exp_zero, neg_one_smul, neg_add_cancel, rowMat_one]
  inv_val := by
    rw [rowMat_mul, SliceB.mat_inv_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, smul_vecMul,
      vecMul_vecMul, SliceB.mat_inv_mul, vecMul_one, neg_smul, add_neg_cancel, rowMat_one]

theorem bkGL_mem (p : ℝ × (Fin m → ℝ) × SliceB D'.P) : bkGL D' p ∈ sliceGroup (splitDiag hc D').P :=
  (rowMat_mem_borelPos_iff (bkGL D' p) rfl (SliceB.incl D'.P p.2.2) rfl).mpr
    ⟨Real.exp_pos _, SliceB.incl_mem D'.P p.2.2⟩

/-- **Coordinates on the adapted slice group**: $(t, r, b') \mapsto
\left(\begin{smallmatrix} e^t & r \\ 0 & b'\end{smallmatrix}\right)$, a bijection
$\mathbb R \times \mathbb R^m \times B' \to B$ (`bk_injective`, `bk_surjective`). -/
def bk (p : ℝ × (Fin m → ℝ) × SliceB D'.P) : SliceB (splitDiag hc D').P :=
  SliceB.mk _ (bkGL D' p) (bkGL_mem hc D' p)

theorem mat_bk (p : ℝ × (Fin m → ℝ) × SliceB D'.P) :
    SliceB.mat _ (bk hc D' p) = rowMat (Real.exp p.1) p.2.1 (SliceB.mat D'.P p.2.2) := rfl

theorem continuous_bk : Continuous (bk hc D') := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · exact continuous_rowMat (Real.continuous_exp.comp continuous_fst) (continuous_fst.comp continuous_snd)
      ((SliceB.continuous_mat D'.P).comp (continuous_snd.comp continuous_snd))
  · exact continuous_rowMat (Real.continuous_exp.comp continuous_fst.neg)
      ((Real.continuous_exp.comp continuous_fst.neg).neg.smul
        ((continuous_fst.comp continuous_snd).matrix_vecMul
          ((SliceB.continuous_mat D'.P).comp (continuous_inv.comp (continuous_snd.comp continuous_snd)))))
      ((SliceB.continuous_mat D'.P).comp (continuous_inv.comp (continuous_snd.comp continuous_snd)))

theorem measurable_bk : Measurable (bk hc D') := (continuous_bk hc D').measurable

theorem SliceB.mat_injective {n : ℕ} (P : GL (Fin n) ℝ) : Function.Injective (SliceB.mat P) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem bk_injective : Function.Injective (bk hc D') := by
  rintro ⟨t, r, b⟩ ⟨t', r', b'⟩ h
  have h1 := congrArg (SliceB.mat _) h
  rw [mat_bk, mat_bk] at h1
  have e0 := congrFun (congrFun h1 0) 0
  simp only [rowMat_zero_zero] at e0
  have ht : t = t' := Real.exp_injective e0
  have hr : r = r' := funext fun j => by simpa using congrFun (congrFun h1 0) j.succ
  have hb : b = b' := SliceB.mat_injective D'.P (funext fun i => funext fun j => by
    simpa using congrFun (congrFun h1 i.succ) j.succ)
  rw [ht, hr, hb]

theorem col_zero_of_mem_slice (x : SliceB (splitDiag hc D').P) (i : Fin m) :
    SliceB.mat _ x i.succ 0 = 0 := by
  have hx := (mem_sliceGroup _ _).mp (SliceB.incl_mem _ x)
  set u := (blockGL D'.P)⁻¹ * SliceB.incl _ x * blockGL D'.P with hu_def
  have hxg : SliceB.incl _ x = blockGL D'.P * u * (blockGL D'.P)⁻¹ := by simp only [u]; group
  have hxu : SliceB.mat _ x = (blockGL D'.P).val * u.val * ((blockGL D'.P)⁻¹ : GL (Fin (m + 1)) ℝ).val := by
    rw [SliceB.mat, hxg, Units.val_mul, Units.val_mul]
  have hB : ∀ (P : GL (Fin m) ℝ) (i : Fin m), (blockGL P).val i.succ 0 = 0 := fun P i => by
    rw [blockGL_val]; rfl
  have hu : ∀ i : Fin m, u.val i.succ 0 = 0 := fun i => hx.1 i.succ 0 (Fin.succ_pos i)
  rw [hxu, col_zero_mul (col_zero_mul (hB _) hu) (by rw [← map_inv]; exact hB _)]

theorem bk_surjective : Function.Surjective (bk hc D') := by
  intro b
  have hc0 := col_zero_of_mem_slice hc D' b
  have hc1 := col_zero_of_mem_slice hc D' b⁻¹
  have hX : SliceB.mat _ b = rowMat (SliceB.mat _ b 0 0) (blockRow (SliceB.mat _ b)) (blockSub (SliceB.mat _ b)) :=
    eq_rowMat hc0
  have h1 : blockSub (SliceB.mat _ b) * blockSub (SliceB.mat _ b⁻¹) = 1 := by
    rw [← blockSub_mul hc0, SliceB.mat_mul_inv]; ext i j; simp [blockSub, Matrix.one_apply, Fin.succ_inj]
  have h2 : blockSub (SliceB.mat _ b⁻¹) * blockSub (SliceB.mat _ b) = 1 := by
    rw [← blockSub_mul hc1, SliceB.mat_inv_mul]; ext i j; simp [blockSub, Matrix.one_apply, Fin.succ_inj]
  let y : GL (Fin m) ℝ := ⟨blockSub (SliceB.mat _ b), blockSub (SliceB.mat _ b⁻¹), h1, h2⟩
  have hmem := (rowMat_mem_borelPos_iff (P := D'.P) (SliceB.incl _ b) hX y rfl).mp (SliceB.incl_mem _ b)
  refine ⟨(Real.log (SliceB.mat _ b 0 0), blockRow (SliceB.mat _ b), SliceB.mk _ y hmem.2), ?_⟩
  apply SliceB.mat_injective
  rw [mat_bk, Real.exp_log hmem.1]
  exact hX.symm

/-- **The orbit map on the adapted slice group**: $\Phi_Q(b) = (ce^{2t},\ 2ce^tr,\ \Phi_{Q'}(b') + c\,(\mathrm{wt}_{ij}r_ir_j))$
for $b = $ `bk (t, r, b')`. -/
theorem beta_bk (p : ℝ × (Fin m → ℝ) × SliceB D'.P) :
    beta (splitDiag hc D') (bk hc D' p) =
      asm (c * Real.exp (2 * p.1)) ((2 * c * Real.exp p.1) • p.2.1) (beta D' p.2.2 + c • wtOuter p.2.1) := by
  rw [beta, mat_bk, phi_rowMat, beta]
  congr 2
  rw [sq, ← Real.exp_add, two_mul]

theorem det_mat_bk (p : ℝ × (Fin m → ℝ) × SliceB D'.P) :
    (SliceB.mat _ (bk hc D' p)).det = Real.exp p.1 * (SliceB.mat D'.P p.2.2).det := by
  rw [mat_bk, det_rowMat]

/-- **The density of $\kappa_0$**: $\theta(b) = |\det b|^{-1}$ (from `det_act`). -/
theorem thetaB_eq {n : ℕ} {Q : QuadForm ℝ n} (D : Diag Q) (x : SliceB D.P) :
    thetaB D x = ‖(SliceB.mat D.P x).det‖₊⁻¹ := by
  have hd : ‖(SliceB.mat D.P x).det‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (det_mat_pos D x).ne'
  simp only [thetaB, chiB, JB, MonoidHom.coe_mk, OneHom.coe_mk, det_act, nnnorm_pow]
  rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hd), one_mul]

/-- **The range of $\beta$ on the adapted slice group**: a coefficient vector with $c\,s \le 0$ is not hit. -/
theorem pos_of_mem_range_beta {y : UIdx (m + 1) → ℝ} (hy : y ∈ range (beta (splitDiag hc D'))) :
    0 < c * sU y := by
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨p, rfl⟩ := bk_surjective hc D' b
  rw [beta_bk, sU_asm, ← mul_assoc]
  exact mul_pos (mul_self_pos.mpr hc) (Real.exp_pos _)

/-- **The range of $\beta$ on the adapted slice group**, the other coordinates. -/
theorem mem_range_beta_iff (t : ℝ) (r : Fin m → ℝ) (v : UIdx m → ℝ) :
    asm (c * Real.exp (2 * t)) ((2 * c * Real.exp t) • r) (v + c • wtOuter r) ∈ range (beta (splitDiag hc D')) ↔
      v ∈ range (beta D') := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨⟨t₁, r₁, b₁⟩, rfl⟩ := bk_surjective hc D' b
    rw [beta_bk] at hb
    have hs := congrArg sU hb
    have hu := congrArg uU hb
    have hv := congrArg vU hb
    simp only [sU_asm, uU_asm, vU_asm] at hs hu hv
    have ht : t₁ = t := by
      have := Real.exp_injective (mul_left_cancel₀ hc hs); linarith
    subst ht
    have hr : r₁ = r := by
      have h2 : (2 * c * Real.exp t₁) ≠ 0 := by
        have := Real.exp_pos t₁; positivity
      exact smul_right_injective _ h2 hu
    subst hr
    exact ⟨b₁, add_right_cancel hv⟩
  · rintro ⟨b', rfl⟩
    exact ⟨bk hc D' (t, r, b'), beta_bk hc D' _⟩

end Slice

/-! ### The comparison measure $\kappa_0$ in the adapted coordinates -/

/-- Integration against a comap along a measurable embedding, by extension by zero. -/
theorem lintegral_comap_eq_extend {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) (μ : Measure β) (F : α → ℝ≥0∞) :
    ∫⁻ a, F a ∂(Measure.comap e μ) = ∫⁻ y, Function.extend e F 0 y ∂μ := by
  have hF : F = Function.extend e F 0 ∘ e := funext fun a => (he.injective.extend_apply F 0 a).symm
  conv_lhs => rw [hF]
  rw [show (∫⁻ a, (Function.extend e F 0 ∘ e) a ∂(Measure.comap e μ)) =
      ∫⁻ a, Function.extend e F 0 (e a) ∂(Measure.comap e μ) from rfl, ← he.lintegral_map, he.map_comap,
    ← lintegral_indicator he.measurableSet_range]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ range e
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, Function.extend_apply' _ _ _ (by simpa using hy), Pi.zero_apply]

section Kappa

variable {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (D' : Diag Q')

theorem lintegral_smul_vec {N : ℕ} {K : (Fin N → ℝ) → ℝ≥0∞} (hK : Measurable K) {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ u, K u = ENNReal.ofReal (|a| ^ N) * ∫⁻ r, K (a • r) := by
  have h := map_addHaar_smul (μ := (volume : Measure (Fin N → ℝ))) ha
  rw [Module.finrank_fin_fun] at h
  rw [← lintegral_map hK (measurable_const_smul a), h, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_inv, abs_pow, mul_inv_cancel₀ (pow_ne_zero _ (abs_pos.mpr ha).ne'),
    ENNReal.ofReal_one, one_mul]

/-- **$\kappa_1 = \beta^*(dc)$ in the adapted coordinates**: for $F \ge 0$ measurable on the slice group $B$ of
`splitDiag hc D'`,
$\int F\,d\kappa_1 = |2c|^{m+1}\int e^{(m+2)t}\int\int F(\mathrm{bk}(t, r, b'))\,d\kappa_1'(b')\,dr\,dt$.
Change of variables $s = ce^{2t}$, $u = 2ce^tr$, $v = v' + c\,(\mathrm{wt}_{ij}r_ir_j)$ in coefficient space
(`beta_bk`). -/
theorem lintegral_kappa1_split {F : SliceB (splitDiag hc D').P → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ b, F b ∂kappa1 (splitDiag hc D') =
      ∫⁻ t, ENNReal.ofReal (|2 * c| ^ (m + 1) * Real.exp ((m + 2) * t)) *
        ∫⁻ r, ∫⁻ b', F (bk hc D' (t, r, b')) ∂kappa1 D' := by
  set G := Function.extend (beta (splitDiag hc D')) F 0 with hGdef
  have hG : Measurable G := (measurableEmbedding_beta (splitDiag hc D')).measurable_extend hF measurable_const
  have hGβ : ∀ b, G (beta (splitDiag hc D') b) = F b := (beta_injective (splitDiag hc D')).extend_apply F 0
  have hG0 : ∀ y, y ∉ range (beta (splitDiag hc D')) → G y = 0 := fun y hy => by
    rw [hGdef, Function.extend_apply' _ _ _ (by simpa using hy), Pi.zero_apply]
  rw [kappa1, lintegral_comap_eq_extend (measurableEmbedding_beta (splitDiag hc D')), lintegral_split hG]
  set H : ℝ → ℝ≥0∞ := fun s => ∫⁻ u : Fin m → ℝ, ∫⁻ v : UIdx m → ℝ, G (asm s u v) with hHdef
  have hH0 : ∀ s, ¬ 0 < c * s → H s = 0 := by
    intro s hs
    refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun u => lintegral_eq_zero_of_ae_eq_zero
      (ae_of_all _ fun v => hG0 _ fun hmem => hs ?_))
    have := pos_of_mem_range_beta hc D' hmem
    rwa [sU_asm] at this
  have himg : (fun t : ℝ => c * Real.exp (2 * t)) '' univ = {s | 0 < c * s} := by
    ext s
    simp only [image_univ, mem_range, mem_ofPred_eq]
    constructor
    · rintro ⟨t, rfl⟩
      rw [← mul_assoc]; exact mul_pos (mul_self_pos.mpr hc) (Real.exp_pos _)
    · intro hs
      have hq : 0 < s / c := by
        have : s / c = c * s / (c * c) := by field_simp
        rw [this]; exact div_pos hs (mul_self_pos.mpr hc)
      refine ⟨Real.log (s / c) / 2, ?_⟩
      rw [show 2 * (Real.log (s / c) / 2) = Real.log (s / c) by ring, Real.exp_log hq]
      field_simp
  have hmS : MeasurableSet {s : ℝ | 0 < c * s} := measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  have hstep1 : ∫⁻ s, H s = ∫⁻ s in {s : ℝ | 0 < c * s}, H s := by
    rw [← lintegral_indicator hmS]
    refine lintegral_congr fun s => ?_
    by_cases hs : 0 < c * s
    · rw [indicator_of_mem (show s ∈ {s : ℝ | 0 < c * s} from hs)]
    · rw [indicator_of_notMem (show s ∉ {s : ℝ | 0 < c * s} from hs), hH0 s hs]
  rw [hstep1, ← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (f' := fun t => 2 * c * Real.exp (2 * t))
    (fun t _ => by
      have h : HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * (2 * 1)) t :=
        ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
      convert (h.const_mul c).hasDerivWithinAt using 1; ring)
    (fun t _ t' _ h => by
      have := Real.exp_injective (mul_left_cancel₀ hc h)
      linarith), Measure.restrict_univ]
  refine lintegral_congr fun t => ?_
  simp only [hHdef]
  have ha : 2 * c * Real.exp t ≠ 0 := by have := Real.exp_pos t; positivity
  have hmK : Measurable fun u : Fin m → ℝ => ∫⁻ v : UIdx m → ℝ, G (asm (c * Real.exp (2 * t)) u v) :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin m → ℝ) × (UIdx m → ℝ) =>
      G (asm (c * Real.exp (2 * t)) p.1 p.2))
      (hG.comp (measurable_asm.comp (measurable_const.prodMk measurable_id)))
  rw [lintegral_smul_vec hmK ha]
  have hinner : ∀ r : Fin m → ℝ, ∫⁻ v : UIdx m → ℝ, G (asm (c * Real.exp (2 * t)) ((2 * c * Real.exp t) • r) v) =
      ∫⁻ b', F (bk hc D' (t, r, b')) ∂kappa1 D' := by
    intro r
    rw [← lintegral_add_right_eq_self _ (c • wtOuter r), kappa1,
      lintegral_comap_eq_extend (measurableEmbedding_beta D')]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ range (beta D')
    · obtain ⟨b', rfl⟩ := hv
      rw [show asm (c * Real.exp (2 * t)) ((2 * c * Real.exp t) • r) (beta D' b' + c • wtOuter r) =
        beta (splitDiag hc D') (bk hc D' (t, r, b')) from (beta_bk hc D' (t, r, b')).symm, hGβ,
        (beta_injective D').extend_apply]
    · rw [hG0 _ (fun h => hv ((mem_range_beta_iff hc D' t r v).mp h)),
        Function.extend_apply' _ _ _ (by simpa using hv), Pi.zero_apply]
  simp_rw [hinner]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  rw [abs_mul (2 * c) (Real.exp (2 * t)), abs_mul (2 * c) (Real.exp t), abs_of_pos (Real.exp_pos (2 * t)),
    abs_of_pos (Real.exp_pos t), mul_pow, ← Real.exp_nat_mul, pow_succ]
  have : Real.exp ((m + 2 : ℝ) * t) = Real.exp (2 * t) * Real.exp (m * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

/-- **$\kappa_0$ in the adapted coordinates**: $\int F\,d\kappa_0 =
|2c|^{m+1}\int e^{(m+1)t}\int\int F(\mathrm{bk}(t, r, b'))\,d\kappa_0'(b')\,dr\,dt$, using the explicit densities
$\theta(b) = |\det b|^{-1}$ and $\det\mathrm{bk}(t, r, b') = e^t\det b'$. -/
theorem lintegral_kappa0_split {F : SliceB (splitDiag hc D').P → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ b, F b ∂kappa0 (splitDiag hc D') =
      ∫⁻ t, ENNReal.ofReal (|2 * c| ^ (m + 1) * Real.exp ((m + 1) * t)) *
        ∫⁻ r, ∫⁻ b', F (bk hc D' (t, r, b')) ∂kappa0 D' := by
  have hθ : ∀ {k : ℕ} {Q : QuadForm ℝ k} (D : Diag Q), Measurable fun x : SliceB D.P => (thetaB D x : ℝ≥0∞) :=
    fun D => Leray.measurable_char (thetaB D) (continuous_thetaB D)
  rw [kappa0, lintegral_withDensity_eq_lintegral_mul _ (hθ _) hF,
    lintegral_kappa1_split hc D' ((hθ _).mul hF)]
  refine lintegral_congr fun t => ?_
  have hinner : ∀ r : Fin m → ℝ, ∫⁻ b', ((fun x => (thetaB (splitDiag hc D') x : ℝ≥0∞)) * F) (bk hc D' (t, r, b'))
      ∂kappa1 D' = ENNReal.ofReal (Real.exp (-t)) * ∫⁻ b', F (bk hc D' (t, r, b')) ∂kappa0 D' := by
    intro r
    have hmF : Measurable fun b' => F (bk hc D' (t, r, b')) :=
      hF.comp ((measurable_bk hc D').comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    rw [kappa0, lintegral_withDensity_eq_lintegral_mul _ (hθ D') hmF, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun b' => ?_
    simp only [Pi.mul_apply, thetaB_eq, det_mat_bk, nnnorm_mul]
    rw [← mul_assoc]
    congr 1
    rw [mul_inv, ENNReal.coe_mul]
    congr 1
    rw [Real.exp_neg, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos t)]
  simp_rw [hinner, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r => lintegral_congr fun b' => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end Kappa

/-! ### Sections of the orbit map and the decomposition of $dX$ -/

/-- **A measurable section of the orbit map** $SO(Q)(\mathbb R) \to S_c$, $g \mapsto ge_0$, for $Q = \langle c\rangle \perp Q'$:
$s(x)e_0 = x$ for every $x \in S_c$. (Data, not a hypothesis: one is constructed in `sphSection`.) -/
structure SphSection (c : ℝ) (Q' : QuadForm ℝ m) where
  /-- the section -/
  toFun : Sph (splitForm c Q') c → ArchSO (splitForm c Q')
  measurable : Measurable toFun
  spec : ∀ x, ArchSOInst.mat _ (toFun x) *ᵥ (e₀ : Fin (m + 1) → ℝ) = (x : Fin (m + 1) → ℝ)

/-- **The orbit map** $(x, h) \mapsto s(x)\,\mathrm{diag}(1, h)$, $S_c \times SO(Q') \to SO(Q)$. -/
def orb {c : ℝ} {Q' : QuadForm ℝ m} (s : SphSection c Q') (p : Sph (splitForm c Q') c × ArchSO Q') :
    ArchSO (splitForm c Q') :=
  s.toFun p.1 * iota c Q' p.2

instance {n : ℕ} (Q : QuadForm ℝ n) : MeasurableMul₂ (ArchSO Q) := ContinuousMul.measurableMul₂

theorem measurable_orb {c : ℝ} {Q' : QuadForm ℝ m} (s : SphSection c Q') : Measurable (orb s) :=
  (s.measurable.comp measurable_fst).mul ((continuous_iota c Q').measurable.comp measurable_snd)

theorem range_chart {n : ℕ} {Q : QuadForm ℝ n} (D : Diag Q) :
    range (chart D) = {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ range (beta D)} := by
  rw [← image_chart D subset_rfl, preimage_range, univ_prod_univ, image_univ]

theorem sU_pullCoeff {n : ℕ} (Q : QuadForm ℝ (n + 1)) (X : Fin (n + 1) → Fin (n + 1) → ℝ) :
    sU (pullCoeff Q X) = Q.eval (X 0) := by
  simp [sU, pullCoeff, eU]

theorem cols_mul_rowMat (S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (β : ℝ) (r : Fin m → ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) :
    cols (S * rowMat β r M) = Fin.cons (S *ᵥ (Fin.cons β 0 : Fin (m + 1) → ℝ))
      (fun j => S *ᵥ (Fin.cons (r j) (cols M j) : Fin (m + 1) → ℝ)) := by
  funext j i
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [cols, Fin.cons_zero, Matrix.mul_apply, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  · simp only [cols, Fin.cons_succ, Matrix.mul_apply, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Fin.cases ?_ (fun k => ?_) k <;> simp [cols]

section Chart

variable {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (hQ' : gramDetR Q' ≠ 0) (D' : Diag Q') (s : SphSection c Q')

theorem chart_orb_bk (t : ℝ) (x : Sph (splitForm c Q') c) (r : Fin m → ℝ) (h : ArchSO Q') (b' : SliceB D'.P) :
    chart (splitDiag hc D') (orb s (x, h), bk hc D' (t, r, b')) =
      Fin.cons (Real.exp t • (x : Fin (m + 1) → ℝ))
        (fun j => ArchSOInst.mat _ (s.toFun x) *ᵥ (Fin.cons (r j) (chart D' (h, b') j) : Fin (m + 1) → ℝ)) := by
  have hR : ArchSOInst.mat _ (orb s (x, h)) * SliceB.mat _ (bk hc D' (t, r, b')) =
      ArchSOInst.mat _ (s.toFun x) * rowMat (Real.exp t) r (ArchSOInst.mat Q' h * SliceB.mat D'.P b') := by
    rw [orb, ArchSOInst.mat_mul, mat_iota, mat_bk, Matrix.mul_assoc, cornerMat_eq_rowMat, rowMat_mul]
    congr 2
    · ring
    · simp
  rw [chart, hR, cols_mul_rowMat]
  congr 1
  rw [show (Fin.cons (Real.exp t) 0 : Fin (m + 1) → ℝ) = Real.exp t • (e₀ : Fin (m + 1) → ℝ) by
    ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp, mulVec_smul, s.spec]

/-- The first column of a point of the chart's range lies in the open cone $\{cQ > 0\}$. -/
theorem mem_posSet_of_mem_range_chart {X : Fin (m + 1) → Fin (m + 1) → ℝ} (hX : X ∈ range (chart (splitDiag hc D'))) :
    X 0 ∈ posSet (splitForm c Q') c := by
  rw [range_chart] at hX
  have := pos_of_mem_range_beta hc D' hX.2
  rwa [sU_pullCoeff] at this

/-- The remaining columns, rotated back by $s(x)$ and with their top entries removed, lie in the range of the chart
for $Q'$. -/
theorem mem_range_chart' (t : ℝ) (x : Sph (splitForm c Q') c) (r : Fin m → ℝ) (Z : Fin m → Fin m → ℝ)
    (hX : (Fin.cons (Real.exp t • (x : Fin (m + 1) → ℝ))
        (fun j => ArchSOInst.mat _ (s.toFun x) *ᵥ (Fin.cons (r j) (Z j) : Fin (m + 1) → ℝ)) :
          Fin (m + 1) → Fin (m + 1) → ℝ) ∈ range (chart (splitDiag hc D'))) :
    Z ∈ range (chart D') := by
  set S := ArchSOInst.mat _ (s.toFun x)
  have hXeq : (Fin.cons (Real.exp t • (x : Fin (m + 1) → ℝ))
        (fun j => S *ᵥ (Fin.cons (r j) (Z j) : Fin (m + 1) → ℝ)) : Fin (m + 1) → Fin (m + 1) → ℝ) =
      cols (S * rowMat (Real.exp t) r (ofCols Z)) := by
    rw [cols_mul_rowMat, cols_ofCols]
    congr 1
    rw [show (Fin.cons (Real.exp t) 0 : Fin (m + 1) → ℝ) = Real.exp t • (e₀ : Fin (m + 1) → ℝ) by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp, mulVec_smul, s.spec]
  rw [hXeq, range_chart] at hX
  obtain ⟨hdet, hphi⟩ := hX
  rw [range_chart]
  refine ⟨?_, ?_⟩
  · rw [show Matrix.of (cols (S * rowMat (Real.exp t) r (ofCols Z))) = (S * rowMat (Real.exp t) r (ofCols Z))ᵀ
      from rfl, det_transpose, det_mul, ArchSOInst.det_mat, one_mul, det_rowMat] at hdet
    rw [← det_ofCols]
    exact pos_of_mul_pos_right hdet (Real.exp_pos t).le
  · rw [← phi_eq_pullCoeff, phi_of_isometry _ (ArchSOInst.isometry _ _), phi_rowMat] at hphi
    rw [show c * Real.exp t ^ 2 = c * Real.exp (2 * t) by rw [sq, ← Real.exp_add, two_mul]] at hphi
    have e : pullCoeff Q' Z = phi Q' (ofCols Z) := by rw [phi_eq_pullCoeff, cols_ofCols]
    rw [e]
    exact (mem_range_beta_iff hc D' t r _).mp hphi

theorem lintegral_fibration_aux {α : Type*} [MeasurableSpace α] {μ : Measure α} {R : Set α}
    (hR : MeasurableSet R) {K : α → ℝ≥0∞} (hK : Measurable K) (hK0 : ∀ z, z ∉ R → K z = 0) :
    ∫⁻ z in R, K z ∂μ = ∫⁻ z, K z ∂μ := by
  rw [← lintegral_indicator hR]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ R
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz, hK0 z hz]

/-- **Splitting off the first column** of a matrix in column coordinates. -/
theorem lintegral_first_col {N : ℕ} {G : (Fin (N + 1) → Fin (N + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X, G X = ∫⁻ x₀ : Fin (N + 1) → ℝ, ∫⁻ X' : Fin N → Fin (N + 1) → ℝ, G (Fin.cons x₀ X') := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Fin (N + 1) → ℝ) 0
  have hE : MeasurePreserving E volume volume := volume_preserving_piFinSuccAbove _ 0
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun x₀ => lintegral_congr fun X' => ?_
  congr 1
  simp [E, MeasurableEquiv.piFinSuccAbove]
  rfl

/-- **The decomposition of $dX$** along $X = s(x)\,\mathrm{diag}(1, h)\,\mathrm{bk}(t, r, b')$: for $G \ge 0$ measurable on
$M_{m+1}(\mathbb R)$ vanishing off the range of the chart,
$\int G\,dX = \int e^{(m+1)t}\int_{S_c}\int_{\mathbb R^m}\int G(\mathrm{chart}(s(x)\,\mathrm{diag}(1, h),
\mathrm{bk}(t, r, b')))\,d(\mu_{Q'}\otimes\kappa_0')\,dr\,d\nu_c\,dt$. -/
theorem lintegral_chart_split {G : (Fin (m + 1) → Fin (m + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G)
    (hG0 : ∀ X, X ∉ range (chart (splitDiag hc D')) → G X = 0) :
    ∫⁻ X, G X = ∫⁻ t, ENNReal.ofReal (Real.exp ((m + 1) * t)) *
      ∫⁻ x, (∫⁻ r : Fin m → ℝ, ∫⁻ p, G (chart (splitDiag hc D') (orb s (x, p.1), bk hc D' (t, r, p.2)))
        ∂((lerayMeasure Q' hQ').prod (kappa0 D'))) ∂(nu (splitForm c Q') c) := by
  rw [lintegral_first_col hG]
  set H : (Fin (m + 1) → ℝ) → ℝ≥0∞ := fun x₀ => ∫⁻ X' : Fin m → Fin (m + 1) → ℝ, G (Fin.cons x₀ X') with hHdef
  have hHm : Measurable H := Measurable.lintegral_prod_right'
    (f := fun q : (Fin (m + 1) → ℝ) × (Fin m → Fin (m + 1) → ℝ) => G (Fin.cons q.1 q.2))
    (hG.comp (by fun_prop))
  have hH0 : ∀ x₀, x₀ ∉ posSet (splitForm c Q') c → H x₀ = 0 := by
    intro x₀ hx₀
    refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun X' => hG0 _ fun hmem => hx₀ ?_)
    have := mem_posSet_of_mem_range_chart hc D' hmem
    simpa using this
  have hmP : MeasurableSet (posSet (splitForm c Q') c) := (isOpen_posSet _ _).measurableSet
  have hstep : ∫⁻ x₀, H x₀ = ∫⁻ x₀ in posSet (splitForm c Q') c, H x₀ := by
    rw [← lintegral_indicator hmP]
    refine lintegral_congr fun x₀ => ?_
    by_cases hx : x₀ ∈ posSet (splitForm c Q') c
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hH0 x₀ hx]
  rw [hstep, lintegral_posSet_pol hc (by omega) hHm]
  refine lintegral_congr fun t => ?_
  congr 1
  · push_cast; ring_nf
  refine lintegral_congr fun x => ?_
  simp only [hHdef]
  set S := ArchSOInst.mat _ (s.toFun x)
  have hdetS : |S.det| = 1 := by rw [ArchSOInst.det_mat, abs_one]
  have hS : MeasurePreserving (fun (Y : Fin m → Fin (m + 1) → ℝ) j => S *ᵥ Y j) volume volume :=
    measurePreserving_pi _ _ fun _ => measurePreserving_mulVec _ hdetS
  rw [← hS.lintegral_comp (f := fun X' => G (Fin.cons (Real.exp t • (x : Fin (m + 1) → ℝ)) X'))
    (hG.comp (by fun_prop))]
  rw [lintegral_cols_split (G := fun Y : Fin m → Fin (m + 1) → ℝ =>
    G (Fin.cons (Real.exp t • (x : Fin (m + 1) → ℝ)) fun j => S *ᵥ Y j)) (hG.comp (by fun_prop))]
  refine lintegral_congr fun r => ?_
  set K : (Fin m → Fin m → ℝ) → ℝ≥0∞ := fun Z =>
    G (Fin.cons (Real.exp t • (x : Fin (m + 1) → ℝ)) fun j => S *ᵥ (Fin.cons (r j) (Z j) : Fin (m + 1) → ℝ))
    with hKdef
  have hKm : Measurable K := hG.comp (by fun_prop)
  have hK0 : ∀ Z, Z ∉ range (chart D') → K Z = 0 := fun Z hZ =>
    hG0 _ fun hmem => hZ (mem_range_chart' hc D' s t x r Z hmem)
  show ∫⁻ Z, K Z = _
  have hR := (measurableEmbedding_chart D').measurableSet_range
  rw [← lintegral_fibration_aux hR hKm hK0, ← (measurableEmbedding_chart D').map_comap,
    (measurableEmbedding_chart D').lintegral_map, lerayMeasure_fibration hQ' D']
  refine lintegral_congr fun p => ?_
  simp only [hKdef, chart_orb_bk hc D' s]
  rfl

end Chart

/-! ### The archimedean orbital identity -/

section Orbital

variable {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (hQ' : gramDetR Q' ≠ 0)

instance {n : ℕ} {Q : QuadForm ℝ n} (D : Diag Q) : SigmaFinite (kappa0 D) := inferInstance

/-- **The archimedean orbital identity at a real place, any signature** (Weil's $\omega_G = \omega_{G/H}\wedge\omega_H$
for $G = SO(Q)$, $H = SO(Q') = \mathrm{Stab}(e_0)$, $G/H \cong S_c$): for $Q = \langle c\rangle \perp Q'$ nondegenerate
($c \ne 0$), every measurable section $s$ of $g \mapsto ge_0$, and the Leray measures $\mu_Q$, $\mu_{Q'}$ and
$\sigma_c$ (`SphereLeray.sig`),
$$\mu_Q = |2c|^{-m}\cdot(\mathrm{orb}_s)_*(\sigma_c \otimes \mu_{Q'}),\qquad
\mathrm{orb}_s(x, h) = s(x)\,\mathrm{diag}(1, h).$$
Equivalently $\int_{SO(Q)} f\,d\mu_Q = |2c|^{-m}\int_{S_c}\int_{SO(Q')} f(s(x)\,\mathrm{diag}(1, h))\,d\mu_{Q'}(h)\,d\sigma_c(x)$
(`lintegral_lerayMeasure_orbital`). -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, Theorem 2.4.3, p. 25 (matching gauge forms on G, H, G/H); §4.5 [unverified]"]
theorem lerayMeasure_orbital (s : SphSection c Q') :
    lerayMeasure (splitForm c Q') (gramDetR_splitForm_ne_zero hc hQ') =
      ENNReal.ofReal ((|2 * c| ^ m)⁻¹) • ((sig (splitForm c Q') c).prod (lerayMeasure Q' hQ')).map (orb s) := by
  set D' := Diag.ofSpectral Q' hQ'
  have hQ := gramDetR_splitForm_ne_zero hc hQ'
  have := sigmaFinite_nu (Q := splitForm c Q') hc
  have := sigmaFinite_sig (Q := splitForm c Q') hc
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : SliceB (splitDiag hc D').P)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKpos : 0 < kappa0 (splitDiag hc D') K := measure_pos_of_mem_nhds _ hK1
  have hKtop : kappa0 (splitDiag hc D') K < ⊤ := hKc.measure_lt_top
  ext A hA
  have hmorb := measurable_orb s
  -- the two sides on A
  have := isHaarMeasure_lerayMeasure hQ'
  set μ' := lerayMeasure Q' hQ'
  set I := (nu (splitForm c Q') c).prod μ' (orb s ⁻¹' A) with hIdef
  set B : ℝ → (Fin m → ℝ) → ℝ≥0∞ := fun t r => ∫⁻ b', K.indicator 1 (bk hc D' (t, r, b')) ∂kappa0 D' with hBdef
  have hBm : Measurable (Function.uncurry B) := Measurable.lintegral_prod_right'
    (f := fun q : (ℝ × (Fin m → ℝ)) × SliceB D'.P => K.indicator 1 (bk hc D' (q.1.1, q.1.2, q.2)))
    ((measurable_one.indicator hKm).comp ((measurable_bk hc D').comp (by fun_prop)))
  have hBm' : ∀ t, Measurable (B t) := fun t => hBm.comp (measurable_const.prodMk measurable_id)
  have hJm : Measurable fun t => ∫⁻ r, B t r := Measurable.lintegral_prod_right' hBm
  set J := ∫⁻ t, ENNReal.ofReal (Real.exp ((m + 1) * t)) * ∫⁻ r, B t r with hJdef
  set a : Sph (splitForm c Q') c → ℝ≥0∞ := fun x => ∫⁻ h, A.indicator 1 (orb s (x, h)) ∂μ' with hadef
  have ham : Measurable a := Measurable.lintegral_prod_right'
    (f := fun q : Sph (splitForm c Q') c × ArchSO Q' => A.indicator 1 (orb s q))
    ((measurable_one.indicator hA).comp hmorb)
  have hIa : I = ∫⁻ x, a x ∂nu (splitForm c Q') c := by
    rw [hIdef, Measure.prod_apply (hmorb hA)]
    refine lintegral_congr fun x => ?_
    rw [hadef, ← lintegral_indicator_one ((hmorb hA).preimage measurable_prodMk_left)]
    rfl
  -- κ₀(K) in the adapted coordinates
  have hκ : kappa0 (splitDiag hc D') K = ENNReal.ofReal (|2 * c| ^ (m + 1)) * J := by
    rw [← lintegral_indicator_one hKm, lintegral_kappa0_split hc D' (measurable_one.indicator hKm), hJdef,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  -- μ_Q(A) κ₀(K) via the fibration theorem and the decomposition of dX
  have hmeasimg : MeasurableSet (chart (splitDiag hc D') '' (A ×ˢ K)) := (measurableEmbedding_chart (splitDiag hc D')).measurableSet_image' (hA.prod hKm)
  have hmain : lerayMeasure (splitForm c Q') hQ A * kappa0 (splitDiag hc D') K = I * J := by
    rw [← Measure.prod_prod, ← lerayMeasure_fibration hQ (splitDiag hc D'), (measurableEmbedding_chart (splitDiag hc D')).comap_apply,
      ← lintegral_indicator_one hmeasimg,
      lintegral_chart_split hc hQ' D' s ((measurable_one.indicator hmeasimg))
        (fun X hX => indicator_of_notMem (fun h => hX (image_subset_range _ _ h)) _)]
    have hind : ∀ g b, (chart (splitDiag hc D') '' (A ×ˢ K)).indicator (1 : (Fin (m + 1) → Fin (m + 1) → ℝ) → ℝ≥0∞)
        (chart (splitDiag hc D') (g, b)) = A.indicator (1 : ArchSO (splitForm c Q') → ℝ≥0∞) g *
          K.indicator (1 : SliceB (splitDiag hc D').P → ℝ≥0∞) b := by
      intro g b
      by_cases hg : g ∈ A <;> by_cases hb : b ∈ K <;>
        simp [indicator, hg, hb, (measurableEmbedding_chart (splitDiag hc D')).injective.mem_set_image]
    simp_rw [hind]
    have hinner : ∀ t x r, ∫⁻ p, A.indicator 1 (orb s (x, p.1)) * K.indicator 1 (bk hc D' (t, r, p.2))
        ∂((lerayMeasure Q' hQ').prod (kappa0 D')) = a x * B t r := by
      intro t x r
      exact lintegral_prod_mul (f := fun h => A.indicator 1 (orb s (x, h)))
        (g := fun b' => K.indicator 1 (bk hc D' (t, r, b')))
        ((measurable_one.indicator hA).comp (hmorb.comp (measurable_const.prodMk measurable_id))).aemeasurable
        ((measurable_one.indicator hKm).comp ((measurable_bk hc D').comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).aemeasurable
    simp_rw [hinner]
    have h2 : ∀ t, ∫⁻ x, (∫⁻ r, a x * B t r) ∂nu (splitForm c Q') c = I * ∫⁻ r, B t r := by
      intro t
      simp_rw [lintegral_const_mul _ (hBm' t)]
      rw [lintegral_mul_const _ ham, hIa]
    simp_rw [h2]
    have hmeasJ : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp ((m + 1) * t)) * ∫⁻ r, B t r :=
      (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp ((m + 1) * t))).mul hJm
    rw [hJdef, ← lintegral_const_mul I hmeasJ]
    refine lintegral_congr fun t => ?_
    ring
  -- cancel κ₀(K)
  rw [hκ] at hmain hKpos hKtop
  have hJ0 : J ≠ 0 := fun h => by rw [h, mul_zero] at hKpos; exact lt_irrefl _ hKpos
  have h2c : 0 < |2 * c| := abs_pos.mpr (mul_ne_zero two_ne_zero hc)
  have hJtop : J ≠ ⊤ := fun h => by
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne'] at hKtop
    exact lt_irrefl _ hKtop
  have hcancel : lerayMeasure (splitForm c Q') hQ A * ENNReal.ofReal (|2 * c| ^ (m + 1)) = I := by
    rw [← mul_assoc] at hmain
    exact (ENNReal.mul_left_inj hJ0 hJtop).mp hmain
  rw [Measure.smul_apply, Measure.map_apply hmorb hA, sig, Measure.prod_smul_left, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← hIdef, ← hcancel,
    mul_comm, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have : |2 * c| ^ (m + 1) * ((|2 * c| ^ m)⁻¹ * (1 / (2 * |c|))) = 1 := by
    rw [abs_mul, abs_two] at h2c ⊢
    field_simp
    ring
  rw [this, ENNReal.ofReal_one, mul_one]

/-- **The orbital identity in integral form**: $\int_{SO(Q)} f\,d\mu_Q =
|2c|^{-m}\int_{S_c}\int_{SO(Q')} f(s(x)\,\mathrm{diag}(1, h))\,d\mu_{Q'}(h)\,d\sigma_c(x)$ for $f \ge 0$ measurable. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, p. 25 (integration over G as an iterated integral over G/H and H) [unverified]"]
theorem lintegral_lerayMeasure_orbital (s : SphSection c Q') {f : ArchSO (splitForm c Q') → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂lerayMeasure (splitForm c Q') (gramDetR_splitForm_ne_zero hc hQ') =
      ENNReal.ofReal ((|2 * c| ^ m)⁻¹) *
        ∫⁻ x, ∫⁻ h, f (s.toFun x * iota c Q' h) ∂lerayMeasure Q' hQ' ∂sig (splitForm c Q') c := by
  have := sigmaFinite_sig (Q := splitForm c Q') hc
  have := isHaarMeasure_lerayMeasure hQ'
  rw [lerayMeasure_orbital hc hQ' s, lintegral_smul_measure, lintegral_map hf (measurable_orb s),
    lintegral_prod (fun p => f (orb s p)) (hf.comp (measurable_orb s)).aemeasurable, smul_eq_mul]
  rfl

end Orbital

/-! ### Reflections; a measurable section of the orbit map -/

section Refl

variable {n : ℕ} (Q : QuadForm ℝ n)

/-- **The reflection** $\tau_v(y) = y - \frac{2B(v, y)}{Q(v)}v$ (as a matrix), $B(v, y) = v^{\mathsf T}Ay$. -/
def refl (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (2 / Q.eval v) • vecMulVec v (gramMatrixR Q *ᵥ v)

theorem refl_mulVec (v y : Fin n → ℝ) :
    refl Q v *ᵥ y = y - (2 / Q.eval v * ((gramMatrixR Q *ᵥ v) ⬝ᵥ y)) • v := by
  rw [refl, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

theorem gram_dot_symm (v y : Fin n → ℝ) : (gramMatrixR Q *ᵥ v) ⬝ᵥ y = v ⬝ᵥ (gramMatrixR Q *ᵥ y) := by
  rw [dotProduct_comm, ArchVol.gram_symm]

theorem eval_eq_dot (v : Fin n → ℝ) : Q.eval v = (gramMatrixR Q *ᵥ v) ⬝ᵥ v := by
  rw [eval_real_eq_gramR, dotProduct_comm]

theorem eq_of_mulVec_eq {M N : Matrix (Fin n) (Fin n) ℝ} (h : ∀ y, M *ᵥ y = N *ᵥ y) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem eq_of_bilin_eq {M N : Matrix (Fin n) (Fin n) ℝ} (h : ∀ y z, y ⬝ᵥ (M *ᵥ z) = y ⬝ᵥ (N *ᵥ z)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single_one] using this

variable {Q}

theorem refl_mul_refl {v : Fin n → ℝ} (hv : Q.eval v ≠ 0) : refl Q v * refl Q v = 1 := by
  refine eq_of_mulVec_eq fun y => ?_
  rw [← mulVec_mulVec, one_mulVec, refl_mulVec, refl_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    ← eval_eq_dot]
  have : 2 / Q.eval v * Q.eval v = 2 := div_mul_cancel₀ _ hv
  set a := 2 / Q.eval v * ((gramMatrixR Q *ᵥ v) ⬝ᵥ y)
  rw [show 2 / Q.eval v * ((gramMatrixR Q *ᵥ v) ⬝ᵥ y - a * Q.eval v) = -a by
    simp only [a]; field_simp; ring]
  rw [neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem refl_isometry {v : Fin n → ℝ} (hv : Q.eval v ≠ 0) :
    (refl Q v)ᵀ * gramMatrixR Q * refl Q v = gramMatrixR Q := by
  refine eq_of_bilin_eq fun y z => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, refl_mulVec, refl_mulVec]
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  have h1 : (v ⬝ᵥ (gramMatrixR Q *ᵥ v)) = Q.eval v := (eval_real_eq_gramR Q v).symm
  have h2 : y ⬝ᵥ (gramMatrixR Q *ᵥ v) = (gramMatrixR Q *ᵥ v) ⬝ᵥ y := dotProduct_comm _ _
  have h3 : v ⬝ᵥ (gramMatrixR Q *ᵥ z) = (gramMatrixR Q *ᵥ v) ⬝ᵥ z := (gram_dot_symm Q v z).symm
  rw [h1, h2, h3]
  field_simp
  ring

theorem det_refl {v : Fin n → ℝ} (hv : Q.eval v ≠ 0) : (refl Q v).det = -1 := by
  have e : refl Q v = 1 + vecMulVec ((-(2 / Q.eval v)) • v) (gramMatrixR Q *ᵥ v) := by
    ext i j; simp [refl, vecMulVec, sub_eq_add_neg]; ring
  rw [e, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul,
    ← eval_eq_dot]
  field_simp
  ring

theorem refl_sub_apply {x y : Fin n → ℝ} (hxy : Q.eval x = Q.eval y) (h : Q.eval (x - y) ≠ 0) :
    refl Q (x - y) *ᵥ x = y := by
  rw [refl_mulVec]
  have hs : (gramMatrixR Q *ᵥ x) ⬝ᵥ y = (gramMatrixR Q *ᵥ y) ⬝ᵥ x := by
    rw [gram_dot_symm, dotProduct_comm]
  have hQ : Q.eval (x - y) = 2 * ((gramMatrixR Q *ᵥ (x - y)) ⬝ᵥ x) := by
    rw [eval_eq_dot, eval_eq_dot] at hxy
    rw [eval_eq_dot]
    simp only [mulVec_sub, sub_dotProduct, dotProduct_sub] at hxy ⊢
    linarith [hs]
  have hb : (gramMatrixR Q *ᵥ (x - y)) ⬝ᵥ x ≠ 0 := by
    intro h0; rw [hQ, h0, mul_zero] at h; exact h rfl
  rw [show 2 / Q.eval (x - y) * ((gramMatrixR Q *ᵥ (x - y)) ⬝ᵥ x) = 1 by
    rw [hQ]; field_simp, one_smul, sub_sub_cancel]

theorem refl_neg (v : Fin n → ℝ) : refl Q (-v) = refl Q v := by
  have : Q.eval (-v) = Q.eval v := by
    rw [show -v = (-1 : ℝ) • v by simp, eval_smul_real]; norm_num
  ext i j; simp [refl, vecMulVec, mulVec_neg, this]

theorem refl_apply_of_orth {v y : Fin n → ℝ} (h : (gramMatrixR Q *ᵥ v) ⬝ᵥ y = 0) : refl Q v *ᵥ y = y := by
  rw [refl_mulVec, h, mul_zero, zero_smul, sub_zero]

theorem continuous_refl {X : Type*} [TopologicalSpace X] {v : X → Fin n → ℝ} (hv : Continuous v)
    (h : ∀ x, Q.eval (v x) ≠ 0) : Continuous fun x => refl Q (v x) :=
  continuous_const.sub ((continuous_const.div ((continuous_eval_real Q).comp hv) h).smul
    (hv.matrix_vecMulVec (continuous_const.matrix_mulVec hv)))

/-- A reflection as a unit (an involution). -/
def reflGL {v : Fin n → ℝ} (hv : Q.eval v ≠ 0) : GL (Fin n) ℝ := ⟨refl Q v, refl Q v, refl_mul_refl hv, refl_mul_refl hv⟩

theorem hessian_eq_two_smul (Q : QuadForm ℝ n) : Q.hessian = (2 : ℝ) • gramMatrixR Q := by
  rw [gramMatrixR, smul_smul]; norm_num

theorem reflGL_mul_mem {v w : Fin n → ℝ} (hv : Q.eval v ≠ 0) (hw : Q.eval w ≠ 0) :
    reflGL hv * reflGL hw ∈ soReal Q := by
  rw [mem_soReal_iff, Units.val_mul, hessian_eq_two_smul]
  refine ⟨?_, ?_⟩
  · change (refl Q v * refl Q w)ᵀ * ((2 : ℝ) • gramMatrixR Q) * (refl Q v * refl Q w) = (2 : ℝ) • gramMatrixR Q
    rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul]
    congr 1
    rw [show (refl Q w)ᵀ * (refl Q v)ᵀ * gramMatrixR Q * (refl Q v * refl Q w) =
      (refl Q w)ᵀ * ((refl Q v)ᵀ * gramMatrixR Q * refl Q v) * refl Q w by simp only [Matrix.mul_assoc],
      refl_isometry hv, refl_isometry hw]
  · change (refl Q v * refl Q w).det = 1
    rw [det_mul, det_refl hv, det_refl hw]; norm_num

end Refl

section Section

variable {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m}

theorem eval_splitForm_e₀ (c : ℝ) (Q' : QuadForm ℝ m) : (splitForm c Q').eval (e₀ : Fin (m + 1) → ℝ) = c := by
  have := evalIn_splitForm_e₀ ℝ c Q'
  simpa using this

theorem exists_eval_ne_zero (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) : ∃ w : Fin m → ℝ, Q'.eval w ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ'
  rw [gramDetR_eq_det]
  have hA : gramMatrixR Q' = 0 := by
    refine eq_of_bilin_eq fun y z => ?_
    have := ArchVol.polar_gram Q' y z
    rw [h, h, h] at this
    rw [zero_mulVec, dotProduct_zero]
    linarith
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [hA, det_zero]


/-- **The witness vector** $w = (0, w')$, orthogonal to $e_0$, with $Q(w) = Q'(w') \ne 0$. -/
def wit (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) : Fin (m + 1) → ℝ := Fin.cons 0 (exists_eval_ne_zero hm hQ').choose

theorem eval_wit (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) : (splitForm c Q').eval (wit hm hQ') ≠ 0 := by
  rw [wit]
  show (splitForm c Q').evalIn ℝ _ ≠ 0
  rw [evalIn_splitForm]
  simpa using (exists_eval_ne_zero hm hQ').choose_spec

theorem gram_wit_e₀ (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) :
    (gramMatrixR (splitForm c Q') *ᵥ wit hm hQ') ⬝ᵥ (e₀ : Fin (m + 1) → ℝ) = 0 := by
  rw [gramMatrixR_splitForm, wit, cornerMat_mulVec]
  simp [dotProduct, Fin.sum_univ_succ]

theorem eval_add_add_eval_sub {n : ℕ} (Q : QuadForm ℝ n) (x y : Fin n → ℝ) :
    Q.eval (x + y) + Q.eval (x - y) = 2 * Q.eval x + 2 * Q.eval y := by
  have hs : x ⬝ᵥ (gramMatrixR Q *ᵥ y) = y ⬝ᵥ (gramMatrixR Q *ᵥ x) := ArchVol.gram_symm Q x y
  rw [eval_real_eq_gramR, eval_real_eq_gramR, eval_real_eq_gramR, eval_real_eq_gramR]
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub]
  linarith [hs]

theorem eval_add_e₀ (hc : c ≠ 0) {x : Fin (m + 1) → ℝ} (hx : (splitForm c Q').eval x = c)
    (h : ¬ (splitForm c Q').eval (x - e₀) ≠ 0) : (splitForm c Q').eval (x + e₀) ≠ 0 := by
  push Not at h
  have := eval_add_add_eval_sub (splitForm c Q') x e₀
  rw [h, hx, eval_splitForm_e₀, add_zero] at this
  rw [this]
  intro h0; apply hc; linarith

/-- **The explicit section** $s(x) = \tau_{x - e_0}\tau_w$ if $Q(x - e_0) \ne 0$, else $s(x) = \tau_{x + e_0}\tau_{e_0}$. -/
def secFun (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) (x : Sph (splitForm c Q') c) : ArchSO (splitForm c Q') :=
  if h : (splitForm c Q').eval ((x : Fin (m + 1) → ℝ) - e₀) ≠ 0 then
    ArchSOInst.mk _ _ (reflGL_mul_mem h (eval_wit hm hQ'))
  else
    ArchSOInst.mk _ _ (reflGL_mul_mem (eval_add_e₀ hc x.2 h) (show (splitForm c Q').eval e₀ ≠ 0 by
      rw [eval_splitForm_e₀]; exact hc))

theorem secFun_spec (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) (x : Sph (splitForm c Q') c) :
    ArchSOInst.mat _ (secFun hc hm hQ' x) *ᵥ (e₀ : Fin (m + 1) → ℝ) = (x : Fin (m + 1) → ℝ) := by
  have hxe : (splitForm c Q').eval (x : Fin (m + 1) → ℝ) = (splitForm c Q').eval e₀ := by
    rw [x.2, eval_splitForm_e₀]
  unfold secFun
  split_ifs with h
  · show (refl _ ((x : Fin (m + 1) → ℝ) - e₀) * refl _ (wit hm hQ')) *ᵥ e₀ = x
    rw [← mulVec_mulVec, refl_apply_of_orth (gram_wit_e₀ hm hQ')]
    have h' : (splitForm c Q').eval (e₀ - (x : Fin (m + 1) → ℝ)) ≠ 0 := by
      rw [show (e₀ : Fin (m + 1) → ℝ) - (x : Fin (m + 1) → ℝ) = (-1 : ℝ) • ((x : Fin (m + 1) → ℝ) - e₀) by
        simp, eval_smul_real]
      simpa using h
    rw [show (x : Fin (m + 1) → ℝ) - e₀ = -(e₀ - (x : Fin (m + 1) → ℝ)) by abel]
    rw [refl_neg, refl_sub_apply hxe.symm h']
  · show (refl _ ((x : Fin (m + 1) → ℝ) + e₀) * refl _ e₀) *ᵥ e₀ = x
    have hce : (splitForm c Q').eval (e₀ : Fin (m + 1) → ℝ) ≠ 0 := by rw [eval_splitForm_e₀]; exact hc
    have h1 : refl (splitForm c Q') e₀ *ᵥ e₀ = -e₀ := by
      rw [refl_mulVec, ← eval_eq_dot, div_mul_cancel₀ _ hce]; module
    rw [← mulVec_mulVec, h1]
    have hxe' : (splitForm c Q').eval (-e₀ : Fin (m + 1) → ℝ) = (splitForm c Q').eval (x : Fin (m + 1) → ℝ) := by
      rw [show (-e₀ : Fin (m + 1) → ℝ) = (-1 : ℝ) • e₀ by simp, eval_smul_real, hxe]; norm_num
    have h2 := eval_add_e₀ hc x.2 h
    have hneg : refl (splitForm c Q') ((x : Fin (m + 1) → ℝ) + e₀) = refl (splitForm c Q') (-e₀ - (x : Fin (m + 1) → ℝ)) := by
      rw [show -e₀ - (x : Fin (m + 1) → ℝ) = -((x : Fin (m + 1) → ℝ) + e₀) by abel, refl_neg]
    rw [hneg, refl_sub_apply hxe' (by
      rw [show -e₀ - (x : Fin (m + 1) → ℝ) = (-1 : ℝ) • ((x : Fin (m + 1) → ℝ) + e₀) by module, eval_smul_real]
      simpa using h2)]

theorem measurable_secFun (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) : Measurable (secFun hc hm hQ') := by
  have hcont : Continuous fun x : Sph (splitForm c Q') c => (splitForm c Q').eval ((x : Fin (m + 1) → ℝ) - e₀) :=
    (continuous_eval_real _).comp (continuous_subtype_val.sub continuous_const)
  set U1 : Set (Sph (splitForm c Q') c) := {x | (splitForm c Q').eval ((x : Fin (m + 1) → ℝ) - e₀) ≠ 0}
  have hU1 : MeasurableSet U1 := hcont.measurable (measurableSet_singleton 0).compl
  have hce : (splitForm c Q').eval (e₀ : Fin (m + 1) → ℝ) ≠ 0 := by rw [eval_splitForm_e₀]; exact hc
  refine measurable_of_restrict_of_restrict_compl hU1 ?_ ?_
  · have hv : Continuous fun y : U1 => ((y : Sph (splitForm c Q') c) : Fin (m + 1) → ℝ) - e₀ :=
      (continuous_subtype_val.comp continuous_subtype_val).sub continuous_const
    have e : U1.domRestrict (secFun hc hm hQ') = fun y : U1 =>
        ArchSOInst.mk _ _ (reflGL_mul_mem (show (splitForm c Q').eval
          (((y : Sph (splitForm c Q') c) : Fin (m + 1) → ℝ) - e₀) ≠ 0 from y.2) (eval_wit hm hQ')) := by
      funext y; show secFun hc hm hQ' y.1 = _; simp only [secFun]
      rw [dif_pos (show (splitForm c Q').eval (((y : Sph (splitForm c Q') c) : Fin (m + 1) → ℝ) - e₀) ≠ 0
        from y.2)]
    rw [e]
    have hcont : Continuous (fun y : U1 => (ArchSOInst.mk _ _ (reflGL_mul_mem (show (splitForm c Q').eval
          (((y : Sph (splitForm c Q') c) : Fin (m + 1) → ℝ) - e₀) ≠ 0 from y.2) (eval_wit hm hQ')) :
          ArchSO (splitForm c Q'))) := by
      refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
      · exact (continuous_refl hv fun y => y.2).matrix_mul continuous_const
      · exact continuous_const.matrix_mul (continuous_refl hv fun y => y.2)
    exact hcont.measurable
  · have hv : Continuous fun y : ↥U1ᶜ => ((y : Sph (splitForm c Q') c) : Fin (m + 1) → ℝ) + e₀ :=
      (continuous_subtype_val.comp continuous_subtype_val).add continuous_const
    have hne : ∀ y : ↥U1ᶜ, (splitForm c Q').eval (((y : Sph (splitForm c Q') c) : Fin (m + 1) → ℝ) + e₀) ≠ 0 :=
      fun y => eval_add_e₀ hc (y : Sph (splitForm c Q') c).2 y.2
    have e : U1ᶜ.domRestrict (secFun hc hm hQ') = fun y : ↥U1ᶜ =>
        ArchSOInst.mk _ _ (reflGL_mul_mem (hne y) hce) := by
      funext y; show secFun hc hm hQ' y.1 = _; simp only [secFun]
      rw [dif_neg (show ¬ (splitForm c Q').eval (((y : Sph (splitForm c Q') c) : Fin (m + 1) → ℝ) - e₀) ≠ 0
        from y.2)]
    rw [e]
    have hcont : Continuous (fun y : ↥U1ᶜ => (ArchSOInst.mk _ _ (reflGL_mul_mem (hne y) hce) :
          ArchSO (splitForm c Q'))) := by
      refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
      · exact (continuous_refl hv hne).matrix_mul continuous_const
      · exact continuous_const.matrix_mul (continuous_refl hv hne)
    exact hcont.measurable

/-- **A measurable section exists** ($m \ge 1$, $Q'$ nondegenerate): $SO(Q)(\mathbb R)$ is transitive on $S_c$, with
an explicit measurable section built from reflections (`secFun`). -/
def sphSection (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) : SphSection c Q' :=
  ⟨secFun hc hm hQ', measurable_secFun hc hm hQ', secFun_spec hc hm hQ'⟩

/-- **Transitivity**: $SO(Q)(\mathbb R)$ acts transitively on $S_c$ ($m \ge 1$, any signature). -/
theorem exists_mulVec_e₀_eq (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetR Q' ≠ 0) (x : Sph (splitForm c Q') c) :
    ∃ g : ArchSO (splitForm c Q'), ArchSOInst.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℝ) = x :=
  ⟨_, secFun_spec hc hm hQ' x⟩

end Section

/-! ### The stabilizer of $e_0$; total masses -/

section Stab

variable {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m}

theorem iota_mulVec_e₀ (h : ArchSO Q') : ArchSOInst.mat _ (iota c Q' h) *ᵥ (e₀ : Fin (m + 1) → ℝ) = e₀ := by
  rw [mat_iota, cornerMat_mulVec]; simp

theorem shape_of_mulVec_e₀ (hc : c ≠ 0) (g : ArchSO (splitForm c Q'))
    (hg : ArchSOInst.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℝ) = e₀) :
    ArchSOInst.mat _ g = cornerMat 1 (blockSub (ArchSOInst.mat _ g)) := by
  set G := ArchSOInst.mat _ g
  have hcol : ∀ i, G i 0 = (e₀ : Fin (m + 1) → ℝ) i := fun i => by
    have := congrFun hg i
    rw [← this]; simp [mulVec, dotProduct, Fin.sum_univ_succ, G]
  have hiso := ArchSOInst.isometry _ g
  rw [gramMatrixR_splitForm] at hiso
  have hrow : ∀ j : Fin m, G 0 j.succ = 0 := by
    intro j
    have := congrFun (congrFun hiso 0) j.succ
    simp only [Matrix.mul_apply, transpose_apply, cornerMat_zero_succ] at this
    have hsum : ∑ x, (∑ x_1, G x_1 0 * cornerMat c (gramMatrixR Q') x_1 x) * G x j.succ = c * G 0 j.succ := by
      rw [Fin.sum_univ_succ]
      simp only [hcol, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, cornerMat_zero_zero,
        cornerMat_zero_succ, cornerMat_succ_zero, zero_mul, mul_zero, add_zero, Finset.sum_const_zero, one_mul]
    rw [hsum] at this
    exact (mul_eq_zero.mp this).resolve_left hc
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hcol 0
  · simpa using hrow j
  · simpa using hcol i.succ
  · rfl

/-- **The stabilizer of $e_0$ in $SO(Q)(\mathbb R)$ is $\iota(SO(Q')(\mathbb R))$** ($Q = \langle c\rangle \perp Q'$, $c \ne 0$). So
$S_c \cong SO(Q)/SO(Q')$ (with `exists_mulVec_e₀_eq`), and `orb s` is a bijection $S_c \times SO(Q') \to SO(Q)$. -/
theorem exists_iota_eq_of_mulVec_e₀ (hc : c ≠ 0) (g : ArchSO (splitForm c Q'))
    (hg : ArchSOInst.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℝ) = e₀) : ∃ h : ArchSO Q', iota c Q' h = g := by
  have hgi : ArchSOInst.mat _ g⁻¹ *ᵥ (e₀ : Fin (m + 1) → ℝ) = e₀ := by
    conv_lhs => rw [← hg]
    rw [mulVec_mulVec, ArchSOInst.mat_inv_mul, one_mulVec]
  have e1 := shape_of_mulVec_e₀ hc g hg
  have e2 := shape_of_mulVec_e₀ hc g⁻¹ hgi
  set G' := blockSub (ArchSOInst.mat _ g)
  set Gi' := blockSub (ArchSOInst.mat _ g⁻¹)
  have h1 : G' * Gi' = 1 := by
    have := ArchSOInst.mat_mul_inv _ g
    rw [e1, e2, cornerMat_mul, ← cornerMat_one] at this
    exact cornerMat_injective_right this
  have h2 : Gi' * G' = 1 := by
    have := ArchSOInst.mat_inv_mul _ g
    rw [e1, e2, cornerMat_mul, ← cornerMat_one] at this
    exact cornerMat_injective_right this
  let u : GL (Fin m) ℝ := ⟨G', Gi', h1, h2⟩
  have hmem : u ∈ soReal Q' := by
    rw [mem_soReal_iff]
    have hiso := (mem_soReal_iff _ _).mp (ArchSOInst.incl_mem _ g)
    change (ArchSOInst.mat _ g)ᵀ * (splitForm c Q').hessian * ArchSOInst.mat _ g = _ ∧
      (ArchSOInst.mat _ g).det = 1 at hiso
    rw [e1, hessian_splitForm, cornerMat_transpose, cornerMat_mul, cornerMat_mul, det_cornerMat, one_mul] at hiso
    exact ⟨cornerMat_injective_right hiso.1, by rw [one_mul] at hiso; exact hiso.2⟩
  refine ⟨ArchSOInst.mk _ u hmem, ?_⟩
  apply Subtype.ext; apply Units.ext
  show cornerMat 1 G' = ArchSOInst.mat _ g
  exact e1.symm

end Stab

section Mass

variable {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (hQ' : gramDetR Q' ≠ 0)

/-- **Total masses** (meaningful in the definite case, where all three are finite):
$\mu_Q(SO(Q)) = |2c|^{-m}\,\sigma_c(S_c)\,\mu_{Q'}(SO(Q'))$. -/
@[kb "weil1982" "§2.4 Theorem 2.4.3, p. 25 (vol G = vol G/H · vol H) [unverified]"]
theorem lerayMeasure_univ_orbital (s : SphSection c Q') :
    lerayMeasure (splitForm c Q') (gramDetR_splitForm_ne_zero hc hQ') univ =
      ENNReal.ofReal ((|2 * c| ^ m)⁻¹) * sig (splitForm c Q') c univ * lerayMeasure Q' hQ' univ := by
  have := sigmaFinite_sig (Q := splitForm c Q') hc
  have := isHaarMeasure_lerayMeasure hQ'
  rw [lerayMeasure_orbital hc hQ' s, Measure.smul_apply, Measure.map_apply (measurable_orb s) MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, smul_eq_mul, mul_assoc]

end Mass

/-! ### Packaging: the local factor at a real place of a number field -/

section NF

open NumberField NumberField.InfinitePlace

/-- **The archimedean orbital identity at a real place of a number field** $F$ (the form used downstream): for
$Q_0 = \langle c_0\rangle \perp Q_0'$ over $F$ ($c_0 \ne 0$) and a real place $w$ with embedding $\sigma_w$, the local form
$Q_0^{\sigma_w} = \langle\sigma_w(c_0)\rangle \perp Q_0'^{\sigma_w}$ (`map_splitForm`) satisfies
$$\mu_{Q_0^{\sigma_w}} = |2c_0|_w^{-m}\cdot(\mathrm{orb}_s)_*(\sigma_{\sigma_w(c_0)} \otimes \mu_{Q_0'^{\sigma_w}}).$$
The local constant $|2c_0|_w^{-m}$ is the $w$-component of an idele of norm $1$ (product formula), so the constants
cancel in the adelic product. -/
@[kb "weil1982" "§2.4 Theorem 2.4.3, p. 25; §4.5 (local factors at the infinite places) [unverified]"]
theorem lerayMeasure_orbital_realPlace {F : Type*} [Field F] [NumberField F] (w : {w : InfinitePlace F // w.IsReal})
    {c₀ : F} (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm F m) (hQ' : gramDetR (Q₀'.map (embedding_of_isReal w.2)) ≠ 0)
    (s : SphSection (embedding_of_isReal w.2 c₀) (Q₀'.map (embedding_of_isReal w.2))) :
    lerayMeasure (splitForm (embedding_of_isReal w.2 c₀) (Q₀'.map (embedding_of_isReal w.2)))
        (gramDetR_splitForm_ne_zero ((map_ne_zero _).mpr hc₀) hQ') =
      ENNReal.ofReal ((w.1 (2 * c₀) ^ m)⁻¹) •
        ((sig (splitForm (embedding_of_isReal w.2 c₀) (Q₀'.map (embedding_of_isReal w.2)))
          (embedding_of_isReal w.2 c₀)).prod (lerayMeasure _ hQ')).map (orb s) := by
  rw [lerayMeasure_orbital ((map_ne_zero _).mpr hc₀) hQ' s, ← norm_embedding_of_isReal w.2, map_mul, map_ofNat,
    Real.norm_eq_abs]

end NF

end QuadFormsKB.Tamagawa.Measure.OrbitalReal
