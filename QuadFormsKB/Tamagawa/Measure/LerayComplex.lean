import QuadFormsKB.Tamagawa.Measure.LerayReal
import QuadFormsKB.Tamagawa.Measure.LerayCount

/-!
# The Leray (gauge-form) measure on $SO(Q)(\mathbb C)$

**At the complex places.** For a nondegenerate quadratic form $Q$ over $\mathbb C$ in $n$ variables (all are
equivalent, but $Q$ is kept general so that it can be `Q₀.map τ` at a complex embedding $\tau$ of a number field),
with Gram matrix $A$ (`gramC Q`, $Q(x) = x^{\mathsf T}Ax$), let
$$\Phi_Q : M_n(\mathbb C) \to \mathbb C^{n(n+1)/2},\qquad X \mapsto \text{the coefficients of } y \mapsto Q(Xy)$$
(`phi`). The fibre of $\Phi_Q$ over $c_Q$ (`coeffUC Q`) is $O(Q)(\mathbb C)$; near it, $\{\operatorname{Re}\det X > 0\}$
cuts out the component of $SO(Q)(\mathbb C)$. The **Leray measure** $\mu_Q$ is the measure with $dX = \mu_Q \otimes dc$
near this fibre ($dX$, $dc$ the real Lebesgue measures on $M_n(\mathbb C) = \mathbb R^{2n^2}$ and on coefficient space
$\mathbb R^{n(n+1)}$; Weil's $|dX/dc|_{\mathbb C}$, Weil 1982 §2.2, with $|\cdot|_{\mathbb C} = |\cdot|^2$).

The construction follows the real places (`LerayReal.lean`) with one change. Over $\mathbb C$ no closed subgroup acts
simply transitively near $c_Q$: the slice group $B = PB_{\mathbb C}P^{-1}$ ($B_{\mathbb C}$ the invertible upper
triangular matrices, $P^{\mathsf T}AP$ diagonal) meets $SO(Q)(\mathbb C)$ in a finite group of signs, so the chart
$(g, b) \mapsto gb$ and the orbit map $b \mapsto \Phi_Q(b)$ are finite-to-one, not injective. Both are **locally
injective** (inverse function theorem over $\mathbb C$), and we pull back the Lebesgue measures by **counting fibres**
(`Leray.fibreCount`, `LerayCount.lean`). Fibre counting is natural for the actions, so the abstract slice decomposition
(`Leray.slice_decomposition`, global Haar uniqueness) applies with no change, and near $1 \in B$, where the maps are
injective, the fibre-counting pull-backs are ordinary pull-backs.

**Results** (for `gramDetC Q ≠ 0`): `isHaarMeasure_lerayMeasureC` (a left Haar measure on $SO(Q)(\mathbb C)$),
`lerayMeasureC_fibration` (the fibration identity $\tau = \mu_Q \otimes \kappa_0$), `tendsto_lerayMeasureC` (the Leray
limit for compactly supported continuous $f$), and `lerayMeasureC_unique` (the Leray limit characterizes $\mu_Q$; in
particular $\mu_Q$ does not depend on the slice data).
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayComplex

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ

/-! ### Coefficient coordinates over $\mathbb C$ -/

theorem wt_ne (p : UIdx n) : (wt p : ℂ) ≠ 0 := by exact_mod_cast (wt_pos p).ne'

/-- **Coefficient coordinates** $c_{ij} = w_{ij}S_{ij}$ ($i \le j$) of a complex matrix. -/
def wtU (S : 𝕄) : UIdx n → ℂ := fun p => (wt p : ℂ) * S p.1.1 p.1.2

/-- **The symmetric matrix with coefficient coordinates** $c$. -/
def symOf (c : UIdx n → ℂ) : 𝕄 := fun i j =>
  if h : i ≤ j then c ⟨(i, j), h⟩ / (wt (⟨(i, j), h⟩ : UIdx n) : ℂ)
  else c ⟨(j, i), le_of_not_ge h⟩ / (wt (⟨(j, i), le_of_not_ge h⟩ : UIdx n) : ℂ)

theorem symOf_transpose (c : UIdx n → ℂ) : (symOf c)ᵀ = symOf c := by
  ext i j
  simp only [transpose_apply, symOf]
  by_cases h1 : j ≤ i <;> by_cases h2 : i ≤ j
  · have : i = j := le_antisymm h2 h1
    subst this; rfl
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_total i j) (by tauto)

theorem wtU_symOf (c : UIdx n → ℂ) : wtU (symOf c) = c := by
  funext p
  simp only [wtU, symOf, dite_eq_left p.2]
  rw [mul_div_cancel₀ _ (wt_ne p)]

theorem symOf_wtU {S : 𝕄} (hS : Sᵀ = S) : symOf (wtU S) = S := by
  ext i j
  simp only [symOf, wtU]
  split_ifs with h
  · rw [mul_div_cancel_left₀ _ (wt_ne _)]
  · rw [mul_div_cancel_left₀ _ (wt_ne _), ← transpose_apply S i j, hS]

theorem wtU_inj {S T : 𝕄} (hS : Sᵀ = S) (hT : Tᵀ = T) (h : wtU S = wtU T) : S = T := by
  rw [← symOf_wtU hS, ← symOf_wtU hT, h]

theorem wtU_add (S T : 𝕄) : wtU (S + T) = wtU S + wtU T := by
  funext p; simp [wtU, mul_add]

theorem wtU_smul (r : ℂ) (S : 𝕄) : wtU (r • S) = r • wtU S := by
  funext p; simp [wtU]; ring

theorem symOf_add (c d : UIdx n → ℂ) : symOf (c + d) = symOf c + symOf d := by
  ext i j; simp only [symOf, Pi.add_apply, Matrix.add_apply]; split_ifs <;> ring

theorem symOf_smul (r : ℂ) (c : UIdx n → ℂ) : symOf (r • c) = r • symOf c := by
  ext i j; simp only [symOf, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- **The right action on coefficient space**: $c \cdot b$ = the coefficients of $y \mapsto c(by)$. -/
def act (b : 𝕄) : (UIdx n → ℂ) →ₗ[ℂ] (UIdx n → ℂ) where
  toFun c := wtU (bᵀ * symOf c * b)
  map_add' c d := by rw [symOf_add, Matrix.mul_add, Matrix.add_mul, wtU_add]
  map_smul' r c := by
    rw [symOf_smul, Matrix.mul_smul, Matrix.smul_mul, wtU_smul]; rfl

theorem act_apply (b : 𝕄) (c : UIdx n → ℂ) : act b c = wtU (bᵀ * symOf c * b) := rfl

theorem symOf_act (b : 𝕄) (c : UIdx n → ℂ) : symOf (act b c) = bᵀ * symOf c * b := by
  rw [act_apply, symOf_wtU]
  rw [transpose_mul, transpose_mul, transpose_transpose, symOf_transpose, Matrix.mul_assoc]

theorem act_mul (b b' : 𝕄) (c : UIdx n → ℂ) : act (b * b') c = act b' (act b c) := by
  rw [act_apply, act_apply, symOf_act, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem act_one (c : UIdx n → ℂ) : act 1 c = c := by
  rw [act_apply, transpose_one, Matrix.one_mul, Matrix.mul_one, wtU_symOf]

theorem act_one_eq : act (1 : 𝕄) = LinearMap.id := LinearMap.ext act_one

theorem act_mul_eq (M N : 𝕄) : act (M * N) = (act N).comp (act M) :=
  LinearMap.ext fun c => act_mul M N c

/-! ### Complex forms: Gram matrix, $\Phi_Q$ -/

/-- **The Gram matrix** $A = \frac12 H$ of a complex form ($Q(x) = x^{\mathsf T}Ax$). -/
def gramC (Q : QuadForm ℂ n) : 𝕄 := (1 / 2 : ℂ) • Q.hessian

/-- **The Gram determinant** $\det A$ of a complex form. -/
def gramDetC (Q : QuadForm ℂ n) : ℂ := (gramC Q).det

/-- **The coefficient vector** $c_Q = (c_{ij})_{i \le j}$ of a complex form. -/
def coeffUC (Q : QuadForm ℂ n) : UIdx n → ℂ := fun p => Q.coeff p.1.1 p.1.2

theorem gramC_transpose (Q : QuadForm ℂ n) : (gramC Q)ᵀ = gramC Q := by
  rw [gramC, transpose_smul]
  congr 1
  simp [QuadForm.hessian, Matrix.transpose_add, add_comm]

theorem coeffUC_eq (Q : QuadForm ℂ n) : coeffUC Q = wtU (gramC Q) := by
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only [coeffUC, wtU, wt, gramC, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp; ring
  · have : Q.coeff j i = 0 := Q.upper (show id i < id j from lt_of_le_of_ne hij h)
    simp [h, this]

/-- **$\Phi_Q(M)$**: the coefficient coordinates of $M^{\mathsf T}AM$. -/
def phi (Q : QuadForm ℂ n) (M : 𝕄) : UIdx n → ℂ := wtU (Mᵀ * gramC Q * M)

theorem gram_sym_mul (Q : QuadForm ℂ n) (M : 𝕄) : (Mᵀ * gramC Q * M)ᵀ = Mᵀ * gramC Q * M := by
  rw [transpose_mul, transpose_mul, transpose_transpose, gramC_transpose, Matrix.mul_assoc]

theorem phi_one (Q : QuadForm ℂ n) : phi Q 1 = coeffUC Q := by
  rw [phi, transpose_one, Matrix.one_mul, Matrix.mul_one, coeffUC_eq]

theorem phi_mul (Q : QuadForm ℂ n) (M b : 𝕄) : phi Q (M * b) = act b (phi Q M) := by
  rw [act_apply, phi, phi, symOf_wtU (gram_sym_mul Q M), transpose_mul]
  simp only [Matrix.mul_assoc]

theorem phi_of_isometry (Q : QuadForm ℂ n) {g : 𝕄} (hg : gᵀ * gramC Q * g = gramC Q) (M : 𝕄) :
    phi Q (g * M) = phi Q M := by
  rw [phi, phi, transpose_mul]
  have : Mᵀ * gᵀ * gramC Q * (g * M) = Mᵀ * (gᵀ * gramC Q * g) * M := by simp only [Matrix.mul_assoc]
  rw [this, hg]

theorem phi_eq_iff (Q : QuadForm ℂ n) (M N : 𝕄) :
    phi Q M = phi Q N ↔ Mᵀ * gramC Q * M = Nᵀ * gramC Q * N :=
  ⟨wtU_inj (gram_sym_mul Q M) (gram_sym_mul Q N), fun h => by rw [phi, phi, h]⟩

theorem continuous_wtU : Continuous (wtU : 𝕄 → UIdx n → ℂ) :=
  continuous_pi fun p => continuous_const.mul ((continuous_apply _).comp (continuous_apply _))

theorem continuous_phi (Q : QuadForm ℂ n) : Continuous (phi Q) :=
  continuous_wtU.comp ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id)

theorem continuous_act (M : 𝕄) : Continuous (act M) := LinearMap.continuous_of_finiteDimensional _

/-! ### Upper triangular matrices -/

/-- Upper triangular: $M_{ij} = 0$ for $j < i$. -/
def IsUT (M : 𝕄) : Prop := ∀ i j : Fin n, j < i → M i j = 0

theorem IsUT.mul {M N : 𝕄} (hM : IsUT M) (hN : IsUT N) : IsUT (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hM i k hk, zero_mul]
  · rw [hN k j (lt_of_lt_of_le hij (not_lt.mp hk)), mul_zero]

theorem IsUT.blockTriangular {M : 𝕄} (hM : IsUT M) : M.BlockTriangular id := fun i j hij => hM i j hij

theorem IsUT.inv {M : 𝕄} (hM : IsUT M) : IsUT M⁻¹ := by
  by_cases hd : IsUnit M.det
  · haveI := M.invertibleOfIsUnitDet hd
    exact fun i j hij => blockTriangular_inv_of_blockTriangular hM.blockTriangular hij
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd]
    intro i j _; rfl

/-- **The complex Borel subgroup** $B_{\mathbb C} \le \mathrm{GL}_n(\mathbb C)$: the invertible upper triangular
matrices. -/
def borelC (n : ℕ) : Subgroup (GL (Fin n) ℂ) where
  carrier := {b | IsUT (b : Matrix (Fin n) (Fin n) ℂ)}
  mul_mem' {a b} ha hb := by
    change IsUT ((a * b : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
    rw [Units.val_mul]; exact IsUT.mul ha hb
  one_mem' := by
    change IsUT ((1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
    intro i j hij; simp [hij.ne']
  inv_mem' {b} hb := by
    change IsUT ((b⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
    rw [Matrix.coe_units_inv]; exact IsUT.inv hb

/-! ### Diagonalization by congruence and the slice group -/

/-- **Diagonalization by congruence** of a nondegenerate complex symmetric Gram matrix: $P^{\mathsf T}AP =
\mathrm{diag}(d)$ with all $d_i \ne 0$ (an orthogonal basis for the bilinear form, `exists_orthogonal_basis`). -/
theorem exists_diag (Q : QuadForm ℂ n) (hQ : gramDetC Q ≠ 0) :
    ∃ (P : GL (Fin n) ℂ) (d : Fin n → ℂ), (∀ i, d i ≠ 0) ∧ (P : 𝕄)ᵀ * gramC Q * P = diagonal d := by
  classical
  set A := gramC Q
  set B : LinearMap.BilinForm ℂ (Fin n → ℂ) := Matrix.toBilin' A
  have hB : LinearMap.IsSymm B := by
    refine ⟨fun x y => ?_⟩
    simp only [B, Matrix.toBilin'_apply', RingHom.id_apply]
    rw [dotProduct_mulVec, ← mulVec_transpose, gramC_transpose, dotProduct_comm]
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  have hdim : Module.finrank ℂ (Fin n → ℂ) = n := Module.finrank_fin_fun ℂ
  set v := v₀.reindex (finCongr hdim)
  have hv : ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
    intro i j hij
    simp only [v, Module.Basis.reindex_apply]
    exact LinearMap.isOrthoᵢ_def.mp hv₀ _ _ (fun h => hij ((finCongr hdim).symm.injective h))
  set Pm : 𝕄 := (Pi.basisFun ℂ (Fin n)).toMatrix v
  have hPm : ∀ i j, Pm i j = v j i := fun i j => by
    simp [Pm, Module.Basis.toMatrix_apply]
  haveI : Invertible Pm := (Pi.basisFun ℂ (Fin n)).invertibleToMatrix v
  have hentry : ∀ i j, (Pmᵀ * A * Pm) i j = B (v i) (v j) := by
    intro i j
    simp only [B, Matrix.toBilin'_apply', Matrix.mul_apply, transpose_apply, hPm, dotProduct, mulVec,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  set d : Fin n → ℂ := fun i => B (v i) (v i)
  have hdiag : Pmᵀ * A * Pm = diagonal d := by
    ext i j
    rw [hentry]
    by_cases hij : i = j
    · subst hij; simp [d]
    · rw [diagonal_apply_ne _ hij, hv i j hij]
  refine ⟨unitOfInvertible Pm, d, fun i => ?_, hdiag⟩
  have h := congrArg Matrix.det hdiag
  rw [det_mul, det_mul, det_transpose, det_diagonal] at h
  have hP0 : Pm.det ≠ 0 := (isUnit_det_of_invertible Pm).ne_zero
  have hne : ∏ i, d i ≠ 0 := by
    rw [← h]; exact mul_ne_zero (mul_ne_zero hP0 hQ) hP0
  exact Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)


/-- **The slice group** $B = PB_{\mathbb C}P^{-1}$. -/
def sliceGroup (P : GL (Fin n) ℂ) : Subgroup (GL (Fin n) ℂ) :=
  (borelC n).comap (MulAut.conj P⁻¹).toMonoidHom

theorem mem_sliceGroup (P x : GL (Fin n) ℂ) : x ∈ sliceGroup P ↔ P⁻¹ * x * P ∈ borelC n := by
  simp [sliceGroup]

/-! ### Invertible matrices as units -/

open Classical in
/-- An invertible matrix as an element of $\mathrm{GL}_n(\mathbb C)$ ($1$ if singular). -/
def toGL (M : 𝕄) : GL (Fin n) ℂ :=
  if h : IsUnit M.det then M.nonsingInvUnit h else 1

theorem toGL_val {M : 𝕄} (h : M.det ≠ 0) : (toGL M : 𝕄) = M := by
  rw [toGL, dif_pos (isUnit_iff_ne_zero.mpr h)]; rfl

theorem toGL_inv_val {M : 𝕄} (h : M.det ≠ 0) : ((toGL M)⁻¹ : GL (Fin n) ℂ) = (M⁻¹ : 𝕄) := by
  rw [toGL, dif_pos (isUnit_iff_ne_zero.mpr h)]; rfl

theorem toGL_coe (g : GL (Fin n) ℂ) : toGL (g : 𝕄) = g := by
  have h : (g : 𝕄).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  exact Units.ext (toGL_val h)

theorem continuousOn_matrix_inv : ContinuousOn (fun M : 𝕄 => M⁻¹) {M | M.det ≠ 0} := by
  have : (fun M : 𝕄 => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (continuous_id.matrix_det.continuousOn.inv₀ fun M hM => hM).smul
    continuous_id.matrix_adjugate.continuousOn

theorem continuousOn_toGL : ContinuousOn (toGL : 𝕄 → GL (Fin n) ℂ) {M | M.det ≠ 0} := by
  rw [Units.isEmbedding_embedProduct.isInducing.continuousOn_iff]
  have : ∀ M ∈ {M : 𝕄 | M.det ≠ 0}, (Units.embedProduct _ ∘ toGL) M = (M, MulOpposite.op M⁻¹) := by
    intro M hM
    simp only [Function.comp_apply, Units.embedProduct_apply, toGL_val hM, toGL_inv_val hM]
  refine ContinuousOn.congr ?_ this
  exact continuousOn_id.prodMk (MulOpposite.continuous_op.comp_continuousOn continuousOn_matrix_inv)

theorem det_conj_P (P : GL (Fin n) ℂ) (M : 𝕄) :
    ((P : 𝕄) * M * ((P⁻¹ : GL (Fin n) ℂ) : 𝕄)).det = M.det := by
  rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    det_one, one_mul]

/-! ### The inverse function theorem at $b = 1$ over $\mathbb C$ -/

/-- **Upper triangular coordinates**: $(i, j)$ entry $y_{ij}$ for $i \le j$, $0$ below. -/
def utU (y : UIdx n → ℂ) : 𝕄 := fun i j => if h : i ≤ j then y ⟨(i, j), h⟩ else 0

theorem isUT_utU (y : UIdx n → ℂ) : IsUT (utU y) := fun i j hij => by simp [utU, not_le.mpr hij]

theorem utU_add (y z : UIdx n → ℂ) : utU (y + z) = utU y + utU z := by
  ext i j; simp only [utU, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp

theorem utU_smul (r : ℂ) (y : UIdx n → ℂ) : utU (r • y) = r • utU y := by
  ext i j; simp only [utU, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem utU_apply_diag (y : UIdx n → ℂ) (i : Fin n) : utU y i i = y ⟨(i, i), le_rfl⟩ := by simp [utU]

theorem utU_injective : Function.Injective (utU : (UIdx n → ℂ) → 𝕄) := by
  intro y z h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [utU, p.2] using this

theorem utU_zero : utU (0 : UIdx n → ℂ) = 0 := by ext i j; simp [utU]

/-- Entrywise smoothness of a matrix-valued map (over $\mathbb C$). -/
def CDMat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → 𝕄) : Prop :=
  ∀ i j, ContDiff ℂ ⊤ fun y => F y i j

section CDMat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem CDMat.mul {F G : E → 𝕄} (hF : CDMat F) (hG : CDMat G) : CDMat fun y => F y * G y :=
  fun i j => by
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun k _ => (hF i k).mul (hG k j)

theorem CDMat.add {F G : E → 𝕄} (hF : CDMat F) (hG : CDMat G) : CDMat fun y => F y + G y :=
  fun i j => by simp only [Matrix.add_apply]; exact (hF i j).add (hG i j)

theorem CDMat.transpose {F : E → 𝕄} (hF : CDMat F) : CDMat fun y => (F y)ᵀ :=
  fun i j => by simp only [transpose_apply]; exact hF j i

theorem CDMat.const (M : 𝕄) : CDMat fun _ : E => M := fun _ _ => contDiff_const

end CDMat

theorem cdMat_utU : CDMat (utU : (UIdx n → ℂ) → 𝕄) := fun i j => by
  by_cases h : i ≤ j
  · simp only [utU, dif_pos h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : UIdx n => ℂ) ⟨(i, j), h⟩).contDiff
  · simp only [utU, h, dite_false]; exact contDiff_const

theorem continuous_utU : Continuous (utU : (UIdx n → ℂ) → 𝕄) :=
  continuous_pi fun i => continuous_pi fun j => by
    by_cases h : i ≤ j
    · simp only [utU, dif_pos h]; exact continuous_apply _
    · simp only [utU, h, dite_false]; exact continuous_const

section IFT

variable (Q : QuadForm ℂ n) (P : GL (Fin n) ℂ)

theorem hPPi : (P : 𝕄) * ((P⁻¹ : GL (Fin n) ℂ) : 𝕄) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem hPiP : ((P⁻¹ : GL (Fin n) ℂ) : 𝕄) * (P : 𝕄) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- **Coordinates on the slice group**: $y \mapsto P(1 + U(y))P^{-1}$. -/
def sliceCoord (y : UIdx n → ℂ) : 𝕄 := (P : 𝕄) * (1 + utU y) * ((P⁻¹ : GL (Fin n) ℂ) : 𝕄)

/-- **The coordinate inverse** $x \mapsto$ the upper triangular entries of $P^{-1}xP - 1$. -/
def coordOf (x : 𝕄) : UIdx n → ℂ := fun p => (((P⁻¹ : GL (Fin n) ℂ) : 𝕄) * x * P - 1) p.1.1 p.1.2

theorem continuous_coordOf : Continuous (coordOf P) :=
  continuous_pi fun p => ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).sub
    continuous_const |>.matrix_elem _ _

theorem sliceCoord_coordOf {x : GL (Fin n) ℂ} (hx : x ∈ sliceGroup P) : sliceCoord P (coordOf P x) = x := by
  rw [mem_sliceGroup] at hx
  have hUT : IsUT ((P⁻¹ * x * P : GL (Fin n) ℂ) : 𝕄) := hx
  rw [Units.val_mul, Units.val_mul] at hUT
  have h1 : 1 + utU (coordOf P x) = ((P⁻¹ : GL (Fin n) ℂ) : 𝕄) * x * P := by
    ext i j
    simp only [Matrix.add_apply, utU, coordOf, Matrix.sub_apply]
    split_ifs with h
    · ring
    · rw [hUT i j (not_le.mp h), Matrix.one_apply_ne (ne_of_gt (not_le.mp h)), add_zero]
  rw [sliceCoord, h1]
  simp only [← Matrix.mul_assoc, hPPi, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hPPi, Matrix.mul_one]

theorem coordOf_sliceCoord (y : UIdx n → ℂ) : coordOf P (sliceCoord P y) = y := by
  funext p
  have : ((P⁻¹ : GL (Fin n) ℂ) : 𝕄) * sliceCoord P y * P = 1 + utU y := by
    rw [sliceCoord]
    simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hPiP, Matrix.mul_one]
  simp only [coordOf, this, add_sub_cancel_left, utU, dif_pos p.2]

/-- $\psi(y) = \Phi_Q(P(1 + U(y))P^{-1})$. -/
def psi (y : UIdx n → ℂ) : UIdx n → ℂ := phi Q (sliceCoord P y)

/-- $E(y) = PU(y)P^{-1}$. -/
def sliceE (y : UIdx n → ℂ) : 𝕄 := (P : 𝕄) * utU y * ((P⁻¹ : GL (Fin n) ℂ) : 𝕄)

theorem sliceCoord_eq (y : UIdx n → ℂ) : sliceCoord P y = 1 + sliceE P y := by
  rw [sliceCoord, sliceE, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPPi]

theorem sliceE_smul (r : ℂ) (y : UIdx n → ℂ) : sliceE P (r • y) = r • sliceE P y := by
  rw [sliceE, sliceE, utU_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem sliceE_add (y z : UIdx n → ℂ) : sliceE P (y + z) = sliceE P y + sliceE P z := by
  rw [sliceE, sliceE, sliceE, utU_add, Matrix.mul_add, Matrix.add_mul]

/-- **The derivative of $\psi$ at $0$**: $y \mapsto$ the coefficients of $E^{\mathsf T}A + AE$. -/
def psiD : (UIdx n → ℂ) →ₗ[ℂ] (UIdx n → ℂ) where
  toFun y := wtU ((sliceE P y)ᵀ * gramC Q + gramC Q * sliceE P y)
  map_add' y z := by
    rw [sliceE_add, transpose_add, Matrix.add_mul, Matrix.mul_add, ← wtU_add]; congr 1; abel
  map_smul' r y := by
    rw [sliceE_smul, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, wtU_smul]; rfl

theorem psi_smul (r : ℂ) (y : UIdx n → ℂ) :
    psi Q P (r • y) = coeffUC Q + r • psiD Q P y + r ^ 2 • wtU ((sliceE P y)ᵀ * gramC Q * sliceE P y) := by
  rw [psi, sliceCoord_eq, sliceE_smul, phi, ← phi_one Q, phi]
  change _ = _ + r • wtU _ + _
  rw [← wtU_smul, ← wtU_smul, ← wtU_add, ← wtU_add]
  congr 1
  simp only [transpose_add, transpose_one, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  module

theorem contDiff_psi : ContDiff ℂ ⊤ (psi Q P) := by
  have hc : CDMat (sliceCoord P) := ((CDMat.const _).mul ((CDMat.const 1).add cdMat_utU)).mul (CDMat.const _)
  have h := (hc.transpose.mul (CDMat.const (gramC Q))).mul hc
  refine contDiff_pi.2 fun p => ?_
  simp only [psi, phi, wtU]
  exact contDiff_const.mul (h p.1.1 p.1.2)

theorem hasDerivAt_psi_line (y : UIdx n → ℂ) : HasDerivAt (fun r : ℂ => psi Q P (r • y)) (psiD Q P y) 0 := by
  simp_rw [psi_smul]
  have h1 : HasDerivAt (fun r : ℂ => r • psiD Q P y) ((1 : ℂ) • psiD Q P y) 0 := (hasDerivAt_id 0).smul_const _
  have h2 : HasDerivAt (fun r : ℂ => r ^ 2 • wtU ((sliceE P y)ᵀ * gramC Q * sliceE P y))
      (((2 : ℕ) * (0 : ℂ) ^ (2 - 1)) • wtU ((sliceE P y)ᵀ * gramC Q * sliceE P y)) 0 :=
    (hasDerivAt_pow 2 (0 : ℂ)).smul_const _
  have := (h1.const_add (coeffUC Q)).add h2
  convert this using 1
  simp

theorem fderiv_psi_zero : (fderiv ℂ (psi Q P) 0 : (UIdx n → ℂ) →ₗ[ℂ] (UIdx n → ℂ)) = psiD Q P := by
  refine LinearMap.ext fun y => ?_
  have hd : HasFDerivAt (psi Q P) (fderiv ℂ (psi Q P) 0) 0 :=
    ((contDiff_psi Q P).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun r : ℂ => r • y) y 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const y
  have hd' : HasFDerivAt (psi Q P) (fderiv ℂ (psi Q P) 0) ((0 : ℂ) • y) := by rwa [zero_smul]
  have h1 : HasDerivAt (fun r : ℂ => psi Q P (r • y)) (fderiv ℂ (psi Q P) 0 y) 0 := by
    have := hd'.comp_hasDerivAt (0 : ℂ) hline
    simpa [Function.comp_def] using this
  exact h1.unique (hasDerivAt_psi_line Q P y)

/-- **The derivative at $0$ is injective.** -/
theorem psiD_injective {d : Fin n → ℂ} (hd : ∀ i, d i ≠ 0) (hP : (P : 𝕄)ᵀ * gramC Q * P = diagonal d) :
    Function.Injective (psiD Q P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set A := gramC Q
  set Pm := (P : 𝕄)
  set Pi := ((P⁻¹ : GL (Fin n) ℂ) : 𝕄)
  set E := sliceE P y
  have hPiP' : Pi * Pm = 1 := hPiP P
  have hsym : (Eᵀ * A + A * E)ᵀ = Eᵀ * A + A * E := by
    rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, gramC_transpose, add_comm]
  have hy' : wtU (Eᵀ * A + A * E) = wtU 0 := by
    have : wtU (Eᵀ * A + A * E) = 0 := hy
    rw [this]; funext p; simp [wtU]
  have h0 : Eᵀ * A + A * E = 0 := wtU_inj hsym (by simp) hy'
  have hEP : E * Pm = Pm * utU y := by
    show Pm * utU y * Pi * Pm = Pm * utU y
    rw [Matrix.mul_assoc, hPiP', Matrix.mul_one]
  have hPE : Pmᵀ * Eᵀ = (utU y)ᵀ * Pmᵀ := by rw [← transpose_mul, hEP, transpose_mul]
  have h1 : (utU y)ᵀ * diagonal d + diagonal d * utU y = 0 := by
    have : Pmᵀ * (Eᵀ * A + A * E) * Pm = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
    rw [Matrix.mul_add, Matrix.add_mul] at this
    rw [← hP]
    calc (utU y)ᵀ * (Pmᵀ * A * Pm) + Pmᵀ * A * Pm * utU y = Pmᵀ * (Eᵀ * A) * Pm + Pmᵀ * (A * E) * Pm := by
          congr 1
          · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hPE]; simp only [Matrix.mul_assoc]
          · rw [Matrix.mul_assoc (Pmᵀ * A), ← hEP]; simp only [Matrix.mul_assoc]
      _ = 0 := this
  have hY : ∀ i j, utU y i j = 0 := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have e := congrFun (congrFun h1 i) j
      have hji : utU y j i = 0 := isUT_utU y j i hij
      rw [Matrix.add_apply, mul_diagonal, diagonal_mul, transpose_apply, hji, zero_mul,
        zero_add, Matrix.zero_apply] at e
      exact (mul_eq_zero.mp e).resolve_left (hd i)
    · have e := congrFun (congrFun h1 i) i
      rw [Matrix.add_apply, mul_diagonal, diagonal_mul, transpose_apply, Matrix.zero_apply] at e
      have : (2 * d i) * utU y i i = 0 := by linear_combination e
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero (hd i))
    · exact isUT_utU y i j hij
  apply utU_injective
  ext i j
  rw [hY i j]; simp [utU]

theorem continuous_sliceCoord : Continuous (sliceCoord P) :=
  (continuous_const.matrix_mul (continuous_const.add continuous_utU)).matrix_mul continuous_const

theorem det_one_add_utU {y : UIdx n → ℂ} (hy : ∀ i : Fin n, 1 + y ⟨(i, i), le_rfl⟩ ≠ 0) :
    (sliceCoord P y).det ≠ 0 := by
  rw [sliceCoord, det_conj_P, det_of_isUpperTriangular]
  · refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, utU_apply_diag]
    exact hy i
  · intro i j hij
    have h1 : (1 : 𝕄) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
    have h2 : utU y i j = 0 := isUT_utU y i j hij
    simp only [Matrix.add_apply, h1, h2, add_zero]

theorem conj_sliceCoord {y : UIdx n → ℂ} (hy : ∀ i : Fin n, 1 + y ⟨(i, i), le_rfl⟩ ≠ 0) :
    P⁻¹ * toGL (sliceCoord P y) * P ∈ borelC n := by
  have hval : ((P⁻¹ * toGL (sliceCoord P y) * P : GL (Fin n) ℂ) : 𝕄) = 1 + utU y := by
    rw [Units.val_mul, Units.val_mul, toGL_val (det_one_add_utU P hy), sliceCoord]
    simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hPiP, Matrix.mul_one]
  change IsUT _
  rw [hval]; intro i j hij
  rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), isUT_utU _ i j hij, add_zero]

theorem hasStrictFDerivAt_psi {d : Fin n → ℂ} (hd : ∀ i, d i ≠ 0) (hP : (P : 𝕄)ᵀ * gramC Q * P = diagonal d) :
    ∃ L : (UIdx n → ℂ) ≃L[ℂ] (UIdx n → ℂ), HasStrictFDerivAt (psi Q P) (L : (UIdx n → ℂ) →L[ℂ] (UIdx n → ℂ)) 0 := by
  refine ⟨(LinearEquiv.ofInjectiveEndo (psiD Q P) (psiD_injective Q P hd hP)).toContinuousLinearEquiv, ?_⟩
  have h := (contDiff_psi Q P).contDiffAt.hasStrictFDerivAt (x := 0) (by simp)
  convert h using 1
  ext1 y
  have := congrArg (fun f : (UIdx n → ℂ) →ₗ[ℂ] (UIdx n → ℂ) => f y) (fderiv_psi_zero Q P)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this]; rfl

/-- **The local chart of the inverse function theorem**: an open set $W \ni 0$ of upper triangular coordinates on which
$\psi$ is injective and open, with $1 + y_{ii} \ne 0$ on $W$, and an open $T \ni c_Q$ with a continuous inverse. -/
theorem exists_local_chart {d : Fin n → ℂ} (hd : ∀ i, d i ≠ 0) (hP : (P : 𝕄)ᵀ * gramC Q * P = diagonal d) :
    ∃ e : OpenPartialHomeomorph (UIdx n → ℂ) (UIdx n → ℂ), (0 : UIdx n → ℂ) ∈ e.source ∧
      (∀ y, e y = psi Q P y) ∧ ∀ y ∈ e.source, ∀ i : Fin n, 1 + y ⟨(i, i), le_rfl⟩ ≠ 0 := by
  obtain ⟨L, hstrict⟩ := hasStrictFDerivAt_psi Q P hd hP
  set e₀ := hstrict.toOpenPartialHomeomorph (psi Q P)
  have h0s : (0 : UIdx n → ℂ) ∈ e₀.source := hstrict.mem_toOpenPartialHomeomorph_source
  set V : Set (UIdx n → ℂ) := {y | ∀ i : Fin n, 1 + y ⟨(i, i), le_rfl⟩ ≠ 0}
  have hV : IsOpen V := by
    simp only [V, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_const.add (continuous_apply _)) continuous_const
  have h0V : (0 : UIdx n → ℂ) ∈ V := fun i => by simp
  refine ⟨e₀.restrOpen V hV, ?_, fun y => by simp [e₀], fun y hy => ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]; exact ⟨h0s, h0V⟩
  · rw [OpenPartialHomeomorph.restrOpen_source] at hy; exact hy.2

end IFT


/-! ### Topology of $\mathrm{GL}_n(\mathbb C)$, $SO(Q)(\mathbb C)$ and the slice group -/

local instance instLCMatrixC : LocallyCompactSpace 𝕄 := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance instPolishMatrixC : PolishSpace 𝕄 := inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))
local instance instSCMatrixC : SecondCountableTopology 𝕄 :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance instPolishMatrixCOp : PolishSpace 𝕄ᵐᵒᵖ := (MulOpposite.opHomeomorph).symm.isClosedEmbedding.polishSpace
local instance instLCGLC : LocallyCompactSpace (GL (Fin n) ℂ) :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace
local instance instPolishGLC : PolishSpace (GL (Fin n) ℂ) := Units.isClosedEmbedding_embedProduct.polishSpace

/-- **$SO(Q)(\mathbb C)$** $= \{g \in \mathrm{GL}_n(\mathbb C) : g^{\mathsf T}Ag = A,\ \det g = 1\}$, $A$ = `gramC Q`. -/
def soC (Q : QuadForm ℂ n) : Subgroup (GL (Fin n) ℂ) where
  carrier := {g | (g : 𝕄)ᵀ * gramC Q * g = gramC Q ∧ (g : 𝕄).det = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, transpose_mul]
      calc (b : 𝕄)ᵀ * (a : 𝕄)ᵀ * gramC Q * ((a : 𝕄) * b) = (b : 𝕄)ᵀ * ((a : 𝕄)ᵀ * gramC Q * a) * b := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [ha1, hb1]
    · rw [Units.val_mul, det_mul, ha2, hb2, one_mul]
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨ha1, ha2⟩ := ha
    have h1 : (a : 𝕄) * ((a⁻¹ : GL (Fin n) ℂ) : 𝕄) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · calc ((a⁻¹ : GL (Fin n) ℂ) : 𝕄)ᵀ * gramC Q * ((a⁻¹ : GL (Fin n) ℂ) : 𝕄)
          = ((a⁻¹ : GL (Fin n) ℂ) : 𝕄)ᵀ * ((a : 𝕄)ᵀ * gramC Q * a) * ((a⁻¹ : GL (Fin n) ℂ) : 𝕄) := by rw [ha1]
        _ = ((a : 𝕄) * ((a⁻¹ : GL (Fin n) ℂ) : 𝕄))ᵀ * gramC Q * ((a : 𝕄) * ((a⁻¹ : GL (Fin n) ℂ) : 𝕄)) := by
            rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1]; simp
    · have := congrArg det h1
      rwa [det_mul, ha2, one_mul, det_one] at this

theorem mem_soC_iff (Q : QuadForm ℂ n) (g : GL (Fin n) ℂ) :
    g ∈ soC Q ↔ (g : 𝕄)ᵀ * gramC Q * g = gramC Q ∧ (g : 𝕄).det = 1 := Iff.rfl

theorem isClosed_soC (Q : QuadForm ℂ n) : IsClosed ((soC Q : Subgroup (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ)) :=
  (isClosed_eq ((Units.continuous_val.matrix_transpose.matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const).inter (isClosed_eq Units.continuous_val.matrix_det continuous_const)

/-- **$SO(Q)(\mathbb C)$ as a type** with its own Borel $\sigma$-algebra. -/
def ArchSOC (Q : QuadForm ℂ n) : Type := soC Q

namespace ArchSOC
variable (Q : QuadForm ℂ n)
instance : Group (ArchSOC Q) := inferInstanceAs (Group (soC Q))
instance : TopologicalSpace (ArchSOC Q) := inferInstanceAs (TopologicalSpace (soC Q))
instance : IsTopologicalGroup (ArchSOC Q) := inferInstanceAs (IsTopologicalGroup (soC Q))
instance : T2Space (ArchSOC Q) := inferInstanceAs (T2Space (soC Q))
instance : LocallyCompactSpace (ArchSOC Q) :=
  show LocallyCompactSpace (soC Q) from (isClosed_soC Q).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance : PolishSpace (ArchSOC Q) := show PolishSpace (soC Q) from (isClosed_soC Q).polishSpace
instance : SecondCountableTopology (ArchSOC Q) := inferInstance
instance : MeasurableSpace (ArchSOC Q) := borel _
instance : BorelSpace (ArchSOC Q) := ⟨rfl⟩

/-- The inclusion into $\mathrm{GL}_n(\mathbb C)$. -/
def incl : ArchSOC Q →* GL (Fin n) ℂ := (soC Q).subtype

theorem continuous_incl : Continuous (incl Q) := continuous_subtype_val

theorem incl_mem (g : ArchSOC Q) : incl Q g ∈ soC Q := (show soC Q from g).2

/-- The underlying matrix. -/
def mat (g : ArchSOC Q) : 𝕄 := (incl Q g : GL (Fin n) ℂ)

theorem continuous_mat : Continuous (mat Q) := Units.continuous_val.comp (continuous_incl Q)

theorem mat_mul (g h : ArchSOC Q) : mat Q (g * h) = mat Q g * mat Q h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat Q 1 = 1 := by simp only [mat, map_one, Units.val_one]

theorem isometry (g : ArchSOC Q) : (mat Q g)ᵀ * gramC Q * mat Q g = gramC Q := (incl_mem Q g).1

theorem det_mat (g : ArchSOC Q) : (mat Q g).det = 1 := (incl_mem Q g).2

/-- An element of `soC Q` as an element of `ArchSOC Q`. -/
def mk (g : GL (Fin n) ℂ) (h : g ∈ soC Q) : ArchSOC Q := (⟨g, h⟩ : soC Q)

theorem mat_mk (g : GL (Fin n) ℂ) (h : g ∈ soC Q) : mat Q (mk Q g h) = g := rfl

end ArchSOC

theorem isClosed_borelC : IsClosed ((borelC n : Subgroup (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ)) := by
  have : ((borelC n : Subgroup (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ)) =
      ⋂ i : Fin n, ⋂ j : Fin n, {b : GL (Fin n) ℂ | j < i → (b : 𝕄) i j = 0} := by
    ext b
    simp only [SetLike.mem_coe, mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : j < i
  · simp only [hij, true_implies]
    exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  · simp only [hij, false_implies, ofPred_true, isClosed_univ]

theorem isClosed_sliceGroup (P : GL (Fin n) ℂ) :
    IsClosed ((sliceGroup P : Subgroup (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ)) := by
  have : ((sliceGroup P : Subgroup (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ)) =
      (fun x => P⁻¹ * x * P) ⁻¹' ((borelC n : Subgroup (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ)) := by
    ext x; exact mem_sliceGroup P x
  rw [this]
  exact isClosed_borelC.preimage ((continuous_const.mul continuous_id).mul continuous_const)

/-- **The slice group as a type** with its Borel $\sigma$-algebra. -/
def SliceB (P : GL (Fin n) ℂ) : Type := sliceGroup P

namespace SliceB
variable (P : GL (Fin n) ℂ)
instance : Group (SliceB P) := inferInstanceAs (Group (sliceGroup P))
instance : TopologicalSpace (SliceB P) := inferInstanceAs (TopologicalSpace (sliceGroup P))
instance : IsTopologicalGroup (SliceB P) := inferInstanceAs (IsTopologicalGroup (sliceGroup P))
instance : T2Space (SliceB P) := inferInstanceAs (T2Space (sliceGroup P))
instance : LocallyCompactSpace (SliceB P) :=
  show LocallyCompactSpace (sliceGroup P) from (isClosed_sliceGroup P).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance : PolishSpace (SliceB P) := show PolishSpace (sliceGroup P) from (isClosed_sliceGroup P).polishSpace
instance : SecondCountableTopology (SliceB P) := inferInstance
instance : MeasurableSpace (SliceB P) := borel _
instance : BorelSpace (SliceB P) := ⟨rfl⟩

/-- The inclusion into $\mathrm{GL}_n(\mathbb C)$. -/
def incl : SliceB P →* GL (Fin n) ℂ := (sliceGroup P).subtype

theorem continuous_incl : Continuous (incl P) := continuous_subtype_val

theorem incl_mem (x : SliceB P) : incl P x ∈ sliceGroup P := (show sliceGroup P from x).2

/-- An element of the slice group as an element of `SliceB P`. -/
def mk (x : GL (Fin n) ℂ) (h : x ∈ sliceGroup P) : SliceB P := (⟨x, h⟩ : sliceGroup P)

theorem incl_mk (x : GL (Fin n) ℂ) (h : x ∈ sliceGroup P) : incl P (mk P x h) = x := rfl

/-- The underlying matrix. -/
def mat (x : SliceB P) : 𝕄 := (incl P x : GL (Fin n) ℂ)

theorem continuous_mat : Continuous (mat P) := Units.continuous_val.comp (continuous_incl P)

theorem mat_mul (x y : SliceB P) : mat P (x * y) = mat P x * mat P y := by simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat P 1 = 1 := by simp only [mat, map_one, Units.val_one]

theorem mat_inv_mul (x : SliceB P) : mat P x⁻¹ * mat P x = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (x : SliceB P) : mat P x * mat P x⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]

theorem det_mat_ne_zero (x : SliceB P) : (mat P x).det ≠ 0 := (Matrix.isUnits_det_units _).ne_zero

end SliceB

/-! ### Slice data, the orbit map, and local injectivity -/

/-- **Diagonalization data** for a complex form $Q$: $P \in \mathrm{GL}_n(\mathbb C)$ with $P^{\mathsf T}AP =
\mathrm{diag}(d)$, all $d_i \ne 0$. Any choice gives the same Leray measure (`lerayDC_eq`). -/
structure DiagC (Q : QuadForm ℂ n) where
  /-- the change of basis -/
  P : GL (Fin n) ℂ
  /-- the diagonal entries -/
  d : Fin n → ℂ
  hd : ∀ i, d i ≠ 0
  hP : (P : 𝕄)ᵀ * gramC Q * P = diagonal d

/-- The diagonalization given by an orthogonal basis (`exists_diag`). -/
def DiagC.ofExists (Q : QuadForm ℂ n) (hQ : gramDetC Q ≠ 0) : DiagC Q :=
  ⟨(exists_diag Q hQ).choose, (exists_diag Q hQ).choose_spec.choose,
    (exists_diag Q hQ).choose_spec.choose_spec.1, (exists_diag Q hQ).choose_spec.choose_spec.2⟩

variable {Q : QuadForm ℂ n} (D : DiagC Q)

theorem DiagC.det_gram_ne_zero (D : DiagC Q) : (gramC Q).det ≠ 0 := by
  have h := congrArg Matrix.det D.hP
  rw [det_mul, det_mul, det_transpose, det_diagonal] at h
  intro h0
  rw [h0, mul_zero, zero_mul] at h
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => D.hd i) h.symm

/-- **The orbit map** $\beta : B \to \mathbb C^{n(n+1)/2}$, $b \mapsto \Phi_Q(b)$ (finite-to-one). -/
def beta (x : SliceB D.P) : UIdx n → ℂ := phi Q (SliceB.mat D.P x)

theorem continuous_beta : Continuous (beta D) := (continuous_phi Q).comp (SliceB.continuous_mat D.P)

theorem beta_mul (x y : SliceB D.P) : beta D (x * y) = act (SliceB.mat D.P y) (beta D x) := by
  rw [beta, beta, SliceB.mat_mul, phi_mul]

theorem beta_one : beta D 1 = coeffUC Q := by rw [beta, SliceB.mat_one, phi_one]

theorem act_mat_inv (x : SliceB D.P) (c : UIdx n → ℂ) :
    act (SliceB.mat D.P x⁻¹) (act (SliceB.mat D.P x) c) = c := by
  rw [← act_mul, SliceB.mat_mul_inv, act_one]

theorem act_mat_inv' (x : SliceB D.P) (c : UIdx n → ℂ) :
    act (SliceB.mat D.P x) (act (SliceB.mat D.P x⁻¹) c) = c := by
  rw [← act_mul, SliceB.mat_inv_mul, act_one]

/-- The chart of the inverse function theorem, for the slice data $D$. -/
def ift : OpenPartialHomeomorph (UIdx n → ℂ) (UIdx n → ℂ) := (exists_local_chart Q D.P D.hd D.hP).choose

theorem zero_mem_ift_source : (0 : UIdx n → ℂ) ∈ (ift D).source := (exists_local_chart Q D.P D.hd D.hP).choose_spec.1

theorem ift_apply (y : UIdx n → ℂ) : ift D y = psi Q D.P y := (exists_local_chart Q D.P D.hd D.hP).choose_spec.2.1 y

theorem ift_diag {y : UIdx n → ℂ} (hy : y ∈ (ift D).source) (i : Fin n) : 1 + y ⟨(i, i), le_rfl⟩ ≠ 0 :=
  (exists_local_chart Q D.P D.hd D.hP).choose_spec.2.2 y hy i

/-- **The injectivity neighbourhood** $V_1 = \{x \in B : $ the coordinates of $x$ lie in the IFT chart$\}$. -/
def V1 : Set (SliceB D.P) := {x | coordOf D.P (SliceB.mat D.P x) ∈ (ift D).source}

theorem isOpen_V1 : IsOpen (V1 D) :=
  (ift D).open_source.preimage ((continuous_coordOf D.P).comp (SliceB.continuous_mat D.P))

theorem coordOf_one : coordOf D.P (1 : 𝕄) = 0 := by
  funext p
  simp [coordOf]

theorem one_mem_V1 : (1 : SliceB D.P) ∈ V1 D := by
  show coordOf D.P (SliceB.mat D.P 1) ∈ (ift D).source
  rw [SliceB.mat_one, coordOf_one]; exact zero_mem_ift_source D

theorem beta_eq_ift (x : SliceB D.P) : beta D x = ift D (coordOf D.P (SliceB.mat D.P x)) := by
  rw [ift_apply, psi, beta, SliceB.mat, sliceCoord_coordOf D.P (SliceB.incl_mem D.P x)]

theorem injOn_beta_V1 : InjOn (beta D) (V1 D) := by
  intro x hx y hy h
  rw [beta_eq_ift, beta_eq_ift] at h
  have h1 := (ift D).injOn hx hy h
  have h2 : SliceB.mat D.P x = SliceB.mat D.P y := by
    rw [SliceB.mat, SliceB.mat, ← sliceCoord_coordOf D.P (SliceB.incl_mem D.P x),
      ← sliceCoord_coordOf D.P (SliceB.incl_mem D.P y)]
    exact congrArg (sliceCoord D.P) h1
  exact Subtype.ext (Units.ext h2)

/-- **A continuous local section of $\beta$** near $c_Q$. -/
theorem exists_local_section :
    ∃ T : Set (UIdx n → ℂ), IsOpen T ∧ coeffUC Q ∈ T ∧ ∃ σ : (UIdx n → ℂ) → SliceB D.P,
      ContinuousOn σ T ∧ σ (coeffUC Q) = 1 ∧ ∀ c ∈ T, beta D (σ c) = c := by
  classical
  set e := ift D
  have hsc0 : sliceCoord D.P 0 = 1 := by rw [sliceCoord, utU_zero, add_zero, Matrix.mul_one, hPPi]
  have hpsi0 : e 0 = coeffUC Q := by rw [ift_apply, psi, hsc0, phi_one]
  have hmem : ∀ c ∈ e.target, toGL (sliceCoord D.P (e.symm c)) ∈ sliceGroup D.P := fun c hc => by
    rw [mem_sliceGroup]; exact conj_sliceCoord D.P (ift_diag D (e.map_target hc))
  let σ : (UIdx n → ℂ) → SliceB D.P := fun c =>
    if h : toGL (sliceCoord D.P (e.symm c)) ∈ sliceGroup D.P then SliceB.mk D.P _ h else 1
  have hval : ∀ c ∈ e.target, SliceB.incl D.P (σ c) = toGL (sliceCoord D.P (e.symm c)) := fun c hc => by
    simp only [σ, dif_pos (hmem c hc), SliceB.incl_mk]
  have h0t : coeffUC Q ∈ e.target := by rw [← hpsi0]; exact e.map_source (zero_mem_ift_source D)
  refine ⟨e.target, e.open_target, h0t, σ, ?_, ?_, fun c hc => ?_⟩
  · have hemb : Topology.IsInducing (SliceB.incl D.P) := Topology.IsInducing.subtypeVal
    rw [hemb.continuousOn_iff]
    have h1 : ContinuousOn (fun c => toGL (sliceCoord D.P (e.symm c))) e.target :=
      continuousOn_toGL.comp ((continuous_sliceCoord D.P).comp_continuousOn e.continuousOn_symm)
        fun c hc => det_one_add_utU D.P (ift_diag D (e.map_target hc))
    exact h1.congr fun c hc => hval c hc
  · apply Subtype.ext
    refine (hval _ h0t).trans ?_
    rw [← hpsi0, e.left_inv (zero_mem_ift_source D), hsc0]
    exact toGL_coe 1
  · rw [beta, SliceB.mat, hval c hc, toGL_val (det_one_add_utU D.P (ift_diag D (e.map_target hc))), ← psi,
      ← ift_apply, e.right_inv hc]

/-- **$\beta$ is an open map** (equivariance spreads the local section). -/
theorem isOpenMap_beta : IsOpenMap (beta D) := by
  obtain ⟨T, hT, hcT, σ, hσc, hσ1, hσ⟩ := exists_local_section D
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x₀, hx₀, rfl⟩
  set F : (UIdx n → ℂ) → SliceB D.P := fun c => σ (act (SliceB.mat D.P x₀⁻¹) c) * x₀
  have hc0 : act (SliceB.mat D.P x₀⁻¹) (beta D x₀) = coeffUC Q := by
    rw [← beta_mul, mul_inv_cancel, beta_one]
  have hF : ContinuousAt F (beta D x₀) := by
    refine ContinuousAt.mul ?_ continuousAt_const
    refine ContinuousAt.comp (f := act (SliceB.mat D.P x₀⁻¹)) ?_ (continuous_act _).continuousAt
    rw [hc0]; exact hσc.continuousAt (hT.mem_nhds hcT)
  have hFx : F (beta D x₀) = x₀ := by simp only [F, hc0, hσ1, one_mul]
  have hpre : F ⁻¹' O ∈ 𝓝 (beta D x₀) := hF.preimage_mem_nhds (by rw [hFx]; exact hO.mem_nhds hx₀)
  have hT' : (act (SliceB.mat D.P x₀⁻¹)) ⁻¹' T ∈ 𝓝 (beta D x₀) :=
    (continuous_act _).continuousAt.preimage_mem_nhds (by rw [hc0]; exact hT.mem_nhds hcT)
  filter_upwards [hpre, hT'] with c hcO hcT'
  refine ⟨F c, hcO, ?_⟩
  simp only [F]
  rw [beta_mul, hσ _ hcT', act_mat_inv']

theorem injective_act_mat (x : SliceB D.P) : Function.Injective (act (SliceB.mat D.P x)) := fun c c' h => by
  rw [← act_mat_inv' D x⁻¹ c, ← act_mat_inv' D x⁻¹ c', inv_inv, h]

/-- **$\beta$ is locally injective**: it is injective on $V_1 x_0$. -/
theorem isLocInj_beta : Leray.IsLocInj (beta D) := by
  intro x₀
  refine ⟨(· * x₀⁻¹) ⁻¹' V1 D, (isOpen_V1 D).preimage (continuous_id.mul continuous_const), by simpa using one_mem_V1 D,
    fun x hx y hy h => ?_⟩
  have h' : beta D (x * x₀⁻¹) = beta D (y * x₀⁻¹) := by rw [beta_mul, beta_mul, h]
  simpa using injOn_beta_V1 D hx hy h'

/-! ### The chart -/

/-- **Column coordinates** of a complex matrix. -/
def cols (M : 𝕄) : Fin n → Fin n → ℂ := fun j i => M i j

/-- The matrix with column coordinates $X$. -/
def ofCols (X : Fin n → Fin n → ℂ) : 𝕄 := fun i j => X j i

theorem ofCols_cols (M : 𝕄) : ofCols (cols M) = M := rfl

theorem cols_ofCols (X : Fin n → Fin n → ℂ) : cols (ofCols X) = X := rfl

theorem continuous_cols : Continuous (cols : 𝕄 → Fin n → Fin n → ℂ) :=
  continuous_pi fun j => continuous_pi fun i => (continuous_apply j).comp (continuous_apply i)

theorem continuous_ofCols : Continuous (ofCols : (Fin n → Fin n → ℂ) → 𝕄) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)

/-- **The chart** $m(g, b) = gb$ in column coordinates. -/
def chart (p : ArchSOC Q × SliceB D.P) : Fin n → Fin n → ℂ := cols (ArchSOC.mat Q p.1 * SliceB.mat D.P p.2)

theorem continuous_chart : Continuous (chart D) :=
  continuous_cols.comp (((ArchSOC.continuous_mat Q).comp continuous_fst).matrix_mul
    ((SliceB.continuous_mat D.P).comp continuous_snd))

theorem phi_chart (p : ArchSOC Q × SliceB D.P) : phi Q (ofCols (chart D p)) = beta D p.2 := by
  rw [chart, ofCols_cols, beta, phi_of_isometry Q (ArchSOC.isometry Q p.1)]

theorem injOn_chart {S : Set (SliceB D.P)} (hS : InjOn (beta D) S) : InjOn (chart D) (univ ×ˢ S) := by
  rintro ⟨g, x⟩ ⟨-, hx⟩ ⟨g', x'⟩ ⟨-, hx'⟩ h
  have hxx : x = x' := hS hx hx' (by rw [← phi_chart D (g, x), ← phi_chart D (g', x'), h])
  subst hxx
  refine Prod.ext ?_ rfl
  have hM : ArchSOC.mat Q g * SliceB.mat D.P x = ArchSOC.mat Q g' * SliceB.mat D.P x := by
    rw [← ofCols_cols (_ * _), ← ofCols_cols (ArchSOC.mat Q g' * _)]; exact congrArg ofCols h
  have hg : ArchSOC.mat Q g = ArchSOC.mat Q g' := by
    have := congrArg (· * SliceB.mat D.P x⁻¹) hM
    simpa only [Matrix.mul_assoc, SliceB.mat_mul_inv, Matrix.mul_one] using this
  exact Subtype.ext (Units.ext hg)

theorem isLocInj_chart : Leray.IsLocInj (chart D) := by
  rintro ⟨g₀, x₀⟩
  obtain ⟨U, hU, hxU, hinj⟩ := isLocInj_beta D x₀
  exact ⟨univ ×ˢ U, isOpen_univ.prod hU, ⟨mem_univ _, hxU⟩, injOn_chart D hinj⟩


/-! ### Lebesgue measure under complex-linear maps -/

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace E]
  [BorelSpace E]

/-- $\det_{\mathbb R} f = |\det_{\mathbb C} f|^2$ for a complex-linear map. -/
theorem det_restrictScalars_complex (f : E →ₗ[ℂ] E) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- **Lebesgue (Haar) measure under a complex-linear map**: $f_*\mu = |\det_{\mathbb C} f|^{-2}\mu$. -/
theorem map_clm_addHaar (μ : Measure E) [μ.IsAddHaarMeasure] (f : E →ₗ[ℂ] E) (hf : LinearMap.det f ≠ 0) :
    μ.map f = (((‖LinearMap.det f‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := by
  have hf' : LinearMap.det (f.restrictScalars ℝ) ≠ 0 := by
    rw [det_restrictScalars_complex]; exact (Complex.normSq_pos.mpr hf).ne'
  have h := map_linearMap_addHaar_eq_smul_addHaar μ hf'
  rw [show ⇑(f.restrictScalars ℝ) = ⇑f from rfl] at h
  rw [h, det_restrictScalars_complex, ← ENNReal.ofReal_coe_nnreal]
  congr 2
  rw [abs_of_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg _)), Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- A complex-linear automorphism (given with its inverse) as a measurable equivalence. -/
def linMEquiv (f g : E →ₗ[ℂ] E) (h1 : ∀ x, f (g x) = x) (h2 : ∀ x, g (f x) = x) : E ≃ᵐ E :=
  (LinearEquiv.ofLinear f g (LinearMap.ext h1) (LinearMap.ext h2)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem linMEquiv_apply (f g : E →ₗ[ℂ] E) (h1 : ∀ x, f (g x) = x) (h2 : ∀ x, g (f x) = x) (x : E) :
    linMEquiv f g h1 h2 x = f x := rfl

theorem coe_linMEquiv (f g : E →ₗ[ℂ] E) (h1 : ∀ x, f (g x) = x) (h2 : ∀ x, g (f x) = x) :
    ⇑(linMEquiv f g h1 h2) = ⇑f := rfl

theorem det_ne_zero_of_inv (f g : E →ₗ[ℂ] E) (h1 : ∀ x, f (g x) = x) : LinearMap.det f ≠ 0 := by
  have : f.comp g = LinearMap.id := LinearMap.ext h1
  have h := congrArg LinearMap.det this
  rw [LinearMap.det_comp, LinearMap.det_id] at h
  exact left_ne_zero_of_mul_eq_one h

end Scaling

instance instHaarMat : (volume : Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

/-! ### Linear changes of variables on $M_n(\mathbb C)$ in column coordinates -/

/-- Left multiplication $X \mapsto MX$ in column coordinates. -/
def lmulL (M : 𝕄) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  LinearMap.pi fun j => (Matrix.toLin' M).comp (LinearMap.proj j)

theorem det_lmulL (M : 𝕄) : LinearMap.det (lmulL M) = M.det ^ n := by
  rw [lmulL, LinearMap.det_pi, LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Transposition of the two indices. -/
def swapL : (Fin n → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toFun X i j := X j i
  invFun X i j := X j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Right multiplication $X \mapsto XM$ in column coordinates. -/
def rmulL (M : 𝕄) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  (swapL (n := n)).toLinearMap ∘ₗ lmulL Mᵀ ∘ₗ (swapL (n := n)).symm.toLinearMap

theorem det_rmulL (M : 𝕄) : LinearMap.det (rmulL M) = M.det ^ n := by
  rw [rmulL, LinearMap.det_conj, det_lmulL, det_transpose]

theorem cols_mul_left (M N : 𝕄) : cols (M * N) = lmulL M (cols N) := by
  funext j i
  simp [cols, lmulL, Matrix.mul_apply, mulVec, dotProduct]

theorem cols_mul_right (N M : 𝕄) : cols (N * M) = rmulL M (cols N) := by
  funext j i
  simp [cols, rmulL, lmulL, swapL, Matrix.mul_apply, mulVec, dotProduct, mul_comm]

theorem lmulL_lmulL {M M' : 𝕄} (h : M * M' = 1) (X : Fin n → Fin n → ℂ) : lmulL M (lmulL M' X) = X := by
  rw [← cols_ofCols X, ← cols_mul_left, ← cols_mul_left, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem rmulL_rmulL {M M' : 𝕄} (h : M' * M = 1) (X : Fin n → Fin n → ℂ) : rmulL M (rmulL M' X) = X := by
  rw [← cols_ofCols X, ← cols_mul_right, ← cols_mul_right, Matrix.mul_assoc, h, Matrix.mul_one]

/-! ### Characters, the comparison measure, the chart measure -/

/-- $\chi(b) = |\det b|^{2n}$: the factor by which $X \mapsto Xb$ scales the real Lebesgue measure $dX$. -/
def chiB : SliceB D.P →* ℝ≥0 where
  toFun x := ‖(SliceB.mat D.P x).det‖₊ ^ (2 * n)
  map_one' := by simp [SliceB.mat_one]
  map_mul' x y := by simp only [SliceB.mat_mul, det_mul, nnnorm_mul, mul_pow]

/-- $J(b) = |\det_{\mathbb C}(c \mapsto c\cdot b)|^2$: the factor by which the action of $b$ scales $dc$. -/
def JB : SliceB D.P →* ℝ≥0 where
  toFun x := ‖LinearMap.det (act (SliceB.mat D.P x))‖₊ ^ 2
  map_one' := by rw [SliceB.mat_one, act_one_eq, LinearMap.det_id, nnnorm_one, one_pow]
  map_mul' x y := by rw [SliceB.mat_mul, act_mul_eq, LinearMap.det_comp, nnnorm_mul, mul_pow, mul_comm]

/-- $\theta = \chi/J$. -/
def thetaB : SliceB D.P →* ℝ≥0 where
  toFun x := chiB D x * (JB D x)⁻¹
  map_one' := by simp
  map_mul' x y := by rw [map_mul, map_mul, mul_inv]; ring

theorem JB_mul_thetaB : JB D * thetaB D = chiB D := by
  ext x
  simp only [MonoidHom.mul_apply, thetaB, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ (Leray.char_ne_zero (JB D) x), mul_one]

theorem continuous_det_act : Continuous fun M : 𝕄 => LinearMap.det (act M) := by
  have : (fun M : 𝕄 => LinearMap.det (act M)) = fun M => (LinearMap.toMatrix' (act M)).det := by
    funext M; rw [LinearMap.det_toMatrix']
  rw [this]
  refine Continuous.matrix_det (continuous_pi fun p => continuous_pi fun q => ?_)
  simp only [LinearMap.toMatrix'_apply, act_apply, wtU]
  exact continuous_const.mul
    (((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).matrix_elem _ _)

theorem continuous_chiB : Continuous (chiB D) :=
  (continuous_nnnorm.comp (SliceB.continuous_mat D.P).matrix_det).pow _

theorem continuous_JB : Continuous (JB D) :=
  (continuous_nnnorm.comp (continuous_det_act.comp (SliceB.continuous_mat D.P))).pow 2

theorem continuous_thetaB : Continuous (thetaB D) :=
  (continuous_chiB D).mul ((continuous_JB D).inv₀ fun x => Leray.char_ne_zero (JB D) x)

/-- The action of $b$ on coefficient space as a measurable equivalence. -/
def actME (b : SliceB D.P) : (UIdx n → ℂ) ≃ᵐ (UIdx n → ℂ) :=
  linMEquiv (act (SliceB.mat D.P b)) (act (SliceB.mat D.P b⁻¹)) (act_mat_inv' D b) (act_mat_inv D b)

/-- $\kappa_1 = \beta^\#(dc)$, the fibre-counting pull-back of Lebesgue measure on coefficient space. -/
def kappa1 : Measure (SliceB D.P) := Leray.fibreCount (beta D) volume

instance : IsFiniteMeasureOnCompacts (kappa1 D) :=
  Leray.fibreCount_isFiniteMeasureOnCompacts (continuous_beta D) (isLocInj_beta D) volume

instance : IsOpenPosMeasure (kappa1 D) :=
  Leray.fibreCount_isOpenPosMeasure (continuous_beta D) (isLocInj_beta D) volume (isOpenMap_beta D)

theorem kappa1_rel : Leray.IsRelRightInvariant (JB D) (kappa1 D) := by
  intro b
  have h := Leray.fibreCount_map (continuous_beta D) (isLocInj_beta D) volume
    (Homeomorph.mulRight b).toMeasurableEquiv (actME D b) (fun y => beta_mul D y b)
  have hdet := det_ne_zero_of_inv _ _ (act_mat_inv' D b)
  rw [actME, coe_linMEquiv] at h
  rw [map_clm_addHaar _ _ hdet, Leray.fibreCount_smul (continuous_beta D) (isLocInj_beta D)] at h
  exact h

/-- **The comparison measure** $\kappa_0 = \theta\,\kappa_1$ on $B$ ($\chi$-relatively right-invariant). -/
def kappa0 : Measure (SliceB D.P) := (kappa1 D).withDensity fun x => (thetaB D x : ℝ≥0∞)

instance : IsFiniteMeasureOnCompacts (kappa0 D) :=
  Leray.withDensity_char_isFiniteMeasureOnCompacts (thetaB D) (continuous_thetaB D)

instance : IsOpenPosMeasure (kappa0 D) :=
  Leray.withDensity_char_isOpenPosMeasure (thetaB D) (continuous_thetaB D)

theorem kappa0_rel : Leray.IsRelRightInvariant (chiB D) (kappa0 D) := by
  have h := Leray.isRelRightInvariant_withDensity (JB D) (thetaB D) (continuous_thetaB D) (kappa1_rel D)
  rwa [JB_mul_thetaB] at h

/-- $\tau = m^\#(dX)$, the fibre-counting pull-back of Lebesgue measure on $M_n(\mathbb C)$ along the chart. -/
def tauM : Measure (ArchSOC Q × SliceB D.P) := Leray.fibreCount (chart D) volume

instance : IsFiniteMeasureOnCompacts (tauM D) :=
  Leray.fibreCount_isFiniteMeasureOnCompacts (continuous_chart D) (isLocInj_chart D) volume

theorem chart_mul_left (g : ArchSOC Q) (p : ArchSOC Q × SliceB D.P) :
    chart D (g * p.1, p.2) = lmulL (ArchSOC.mat Q g) (chart D p) := by
  rw [chart, chart, ArchSOC.mat_mul, Matrix.mul_assoc, cols_mul_left]

theorem chart_mul_right (b : SliceB D.P) (p : ArchSOC Q × SliceB D.P) :
    chart D (p.1, p.2 * b) = rmulL (SliceB.mat D.P b) (chart D p) := by
  rw [chart, chart, SliceB.mat_mul, ← Matrix.mul_assoc, cols_mul_right]

theorem ArchSOC.mat_mul_inv (g : ArchSOC Q) : ArchSOC.mat Q g * ArchSOC.mat Q g⁻¹ = 1 := by
  rw [← ArchSOC.mat_mul, mul_inv_cancel, ArchSOC.mat_one]

theorem ArchSOC.mat_inv_mul (g : ArchSOC Q) : ArchSOC.mat Q g⁻¹ * ArchSOC.mat Q g = 1 := by
  rw [← ArchSOC.mat_mul, inv_mul_cancel, ArchSOC.mat_one]

theorem tauM_left (g : ArchSOC Q) :
    (tauM D).map (fun p : ArchSOC Q × SliceB D.P => (g * p.1, p.2)) = tauM D := by
  have h := Leray.fibreCount_map (continuous_chart D) (isLocInj_chart D) volume
    ((Homeomorph.mulLeft g).prodCongr (Homeomorph.refl _)).toMeasurableEquiv
    (linMEquiv (lmulL (ArchSOC.mat Q g)) (lmulL (ArchSOC.mat Q g⁻¹))
      (lmulL_lmulL (ArchSOC.mat_mul_inv g)) (lmulL_lmulL (ArchSOC.mat_inv_mul g)))
    (fun p => chart_mul_left D g p)
  rw [coe_linMEquiv, map_clm_addHaar _ _ (det_ne_zero_of_inv _ _ (lmulL_lmulL (ArchSOC.mat_mul_inv g))),
    det_lmulL, ArchSOC.det_mat, one_pow, nnnorm_one, one_pow, inv_one, ENNReal.coe_one, one_smul] at h
  exact h

theorem tauM_right (b : SliceB D.P) :
    (tauM D).map (fun p : ArchSOC Q × SliceB D.P => (p.1, p.2 * b)) =
      (((chiB D b)⁻¹ : ℝ≥0) : ℝ≥0∞) • tauM D := by
  have h := Leray.fibreCount_map (continuous_chart D) (isLocInj_chart D) volume
    ((Homeomorph.refl _).prodCongr (Homeomorph.mulRight b)).toMeasurableEquiv
    (linMEquiv (rmulL (SliceB.mat D.P b)) (rmulL (SliceB.mat D.P b⁻¹))
      (rmulL_rmulL (SliceB.mat_inv_mul D.P b)) (rmulL_rmulL (SliceB.mat_mul_inv D.P b)))
    (fun p => chart_mul_right D b p)
  rw [coe_linMEquiv, map_clm_addHaar _ _ (det_ne_zero_of_inv _ _ (rmulL_rmulL (SliceB.mat_inv_mul D.P b))),
    det_rmulL, Leray.fibreCount_smul (continuous_chart D) (isLocInj_chart D)] at h
  rw [show chiB D b = ‖(SliceB.mat D.P b).det ^ n‖₊ ^ 2 by
    simp only [chiB, MonoidHom.coe_mk, OneHom.coe_mk, nnnorm_pow, ← pow_mul, mul_comm]]
  exact h

/-- A fixed compact set with nonempty interior in $SO(Q)(\mathbb C)$ (the Leray constant absorbs the normalization). -/
def K₀ (Q : QuadForm ℂ n) : PositiveCompacts (ArchSOC Q) := Classical.arbitrary _

theorem exists_fibration : ∃ c : ℝ≥0, tauM D = ((c : ℝ≥0∞) • haarMeasure (K₀ Q)).prod (kappa0 D) :=
  Leray.slice_decomposition (K₀ Q) (chiB D) (continuous_chiB D) (tauM D) (tauM_left D) (tauM_right D)
    (kappa0 D) (kappa0_rel D)

/-- The Leray constant for the slice data $D$. -/
def lerayC : ℝ≥0 := (exists_fibration D).choose

/-- **The Leray measure** on $SO(Q)(\mathbb C)$ built from the slice data $D$ (`lerayDC_eq`: independent of $D$). -/
def lerayDC : Measure (ArchSOC Q) := ((lerayC D : ℝ≥0) : ℝ≥0∞) • haarMeasure (K₀ Q)

/-- **The fibration theorem**: the fibre-counting pull-back of $dX$ along $(g, b) \mapsto gb$ is $\mu_Q \otimes \kappa_0$. -/
theorem lerayFibration : Leray.fibreCount (chart D) volume = (lerayDC D).prod (kappa0 D) :=
  (exists_fibration D).choose_spec


/-! ### Near $1 \in B$: the inverse of $\beta$, the density, the image of the chart -/

/-- **The neighbourhood $V_0$ of $1$ in $B$**: $\beta$ is injective on $V_0$ and $\operatorname{Re}\det > 0$ there. -/
def V0 : Set (SliceB D.P) := V1 D ∩ {x | 0 < (SliceB.mat D.P x).det.re}

theorem isOpen_V0 : IsOpen (V0 D) :=
  (isOpen_V1 D).inter (isOpen_lt continuous_const
    (Complex.continuous_re.comp (SliceB.continuous_mat D.P).matrix_det))

theorem one_mem_V0 : (1 : SliceB D.P) ∈ V0 D := ⟨one_mem_V1 D, by simp [SliceB.mat_one]⟩

theorem injOn_beta_V0 : InjOn (beta D) (V0 D) := (injOn_beta_V1 D).mono inter_subset_left

/-- **The neighbourhood $U_0 = \beta(V_0)$ of $c_Q$** in coefficient space (open). -/
def U0 : Set (UIdx n → ℂ) := beta D '' V0 D

theorem isOpen_U0 : IsOpen (U0 D) := isOpenMap_beta D _ (isOpen_V0 D)

theorem coeffUC_mem_U0 : coeffUC Q ∈ U0 D := ⟨1, one_mem_V0 D, beta_one D⟩

/-- $\beta$ restricted to $V_0$. -/
def betaV (x : V0 D) : UIdx n → ℂ := beta D x

theorem isOpenEmbedding_betaV : Topology.IsOpenEmbedding (betaV D) :=
  .of_continuous_injective_isOpenMap ((continuous_beta D).comp continuous_subtype_val)
    (fun x y h => Subtype.ext (injOn_beta_V0 D x.2 y.2 h))
    ((isOpenMap_beta D).comp (isOpen_V0 D).isOpenMap_subtype_val)

instance : Nonempty (V0 D) := ⟨⟨1, one_mem_V0 D⟩⟩

theorem range_betaV : range (betaV D) = U0 D := by
  ext c
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩

/-- **The inverse** $\beta^{-1} : U_0 \to V_0$ of the orbit map near $1$. -/
def sec (c : UIdx n → ℂ) : SliceB D.P :=
  (((isOpenEmbedding_betaV D).toOpenPartialHomeomorph (betaV D)).symm c : V0 D)

theorem sec_mem (c : UIdx n → ℂ) : sec D c ∈ V0 D :=
  (((isOpenEmbedding_betaV D).toOpenPartialHomeomorph (betaV D)).symm c).2

theorem sec_beta {x : SliceB D.P} (hx : x ∈ V0 D) : sec D (beta D x) = x :=
  congrArg Subtype.val ((isOpenEmbedding_betaV D).toOpenPartialHomeomorph_left_inv (betaV D) (x := ⟨x, hx⟩))

theorem beta_sec {c : UIdx n → ℂ} (hc : c ∈ U0 D) : beta D (sec D c) = c :=
  (isOpenEmbedding_betaV D).toOpenPartialHomeomorph_right_inv (betaV D) (by rw [range_betaV]; exact hc)

theorem continuousOn_sec : ContinuousOn (sec D) (U0 D) := by
  have h := ((isOpenEmbedding_betaV D).toOpenPartialHomeomorph (betaV D)).continuousOn_symm
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, range_betaV] at h
  exact continuous_subtype_val.comp_continuousOn h

theorem sec_coeffUC : sec D (coeffUC Q) = 1 := by rw [← beta_one D, sec_beta D (one_mem_V0 D)]

/-- **The Leray density** $\rho = \theta \circ \beta^{-1}$ on $U_0$. -/
def rho (c : UIdx n → ℂ) : ℝ := (thetaB D (sec D c) : ℝ)

theorem rho_coeffUC : rho D (coeffUC Q) = 1 := by simp [rho, sec_coeffUC]

theorem rho_nonneg (c : UIdx n → ℂ) : 0 ≤ rho D c := NNReal.coe_nonneg _

theorem continuousOn_rho : ContinuousOn (rho D) (U0 D) :=
  (NNReal.continuous_coe.comp (continuous_thetaB D)).comp_continuousOn (continuousOn_sec D)

/-- **The region** $\{X \in M_n(\mathbb C) : \operatorname{Re}\det X > 0,\ \Phi_Q(X) \in E\}$ (column coordinates). -/
def regionC (Q : QuadForm ℂ n) (E : Set (UIdx n → ℂ)) : Set (Fin n → Fin n → ℂ) :=
  {X | 0 < (ofCols X).det.re ∧ phi Q (ofCols X) ∈ E}

theorem measurableSet_regionC {E : Set (UIdx n → ℂ)} (hE : MeasurableSet E) : MeasurableSet (regionC Q E) :=
  (measurableSet_lt measurable_const
      (Complex.continuous_re.comp continuous_ofCols.matrix_det).measurable).inter
    (hE.preimage ((continuous_phi Q).comp continuous_ofCols).measurable)

theorem isOpen_regionC {E : Set (UIdx n → ℂ)} (hE : IsOpen E) : IsOpen (regionC Q E) :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_ofCols.matrix_det)).inter
    (hE.preimage ((continuous_phi Q).comp continuous_ofCols))

/-- **The image of the chart near $1$**: for $E \subseteq U_0$,
$m(SO(Q)(\mathbb C) \times (V_0 \cap \beta^{-1}E)) = \{X : \operatorname{Re}\det X > 0,\ \Phi_Q(X) \in E\}$
(an element of $O(Q)$ of determinant $-1$ would make $\operatorname{Re}\det X < 0$). -/
theorem image_chart {E : Set (UIdx n → ℂ)} (hE : E ⊆ U0 D) :
    chart D '' (univ ×ˢ (V0 D ∩ beta D ⁻¹' E)) = regionC Q E := by
  ext X
  constructor
  · rintro ⟨⟨g, x⟩, ⟨-, hxV, hxE⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [chart, ofCols_cols, det_mul, ArchSOC.det_mat, one_mul]; exact hxV.2
    · rw [phi_chart]; exact hxE
  · rintro ⟨hdet, hX⟩
    set M := ofCols X
    obtain ⟨x, hxV, hx⟩ := hE hX
    set N := M * SliceB.mat D.P x⁻¹
    have hNphi : phi Q N = coeffUC Q := by
      rw [phi_mul, ← hx, ← beta_mul, mul_inv_cancel, beta_one]
    have hNiso : Nᵀ * gramC Q * N = gramC Q := by
      have := (phi_eq_iff Q N 1).mp (by rw [hNphi, phi_one])
      rwa [transpose_one, Matrix.one_mul, Matrix.mul_one] at this
    have hMN : M = N * SliceB.mat D.P x := by
      simp only [N, Matrix.mul_assoc, SliceB.mat_inv_mul, Matrix.mul_one]
    have hNdet : N.det = 1 := by
      have hA := D.det_gram_ne_zero
      have h1 := congrArg Matrix.det hNiso
      rw [det_mul, det_mul, det_transpose] at h1
      have h2 : (N.det - 1) * (N.det + 1) = 0 := by
        have : (N.det * N.det - 1) * (gramC Q).det = 0 := by linear_combination h1
        have := (mul_eq_zero.mp this).resolve_right hA
        linear_combination this
      rcases mul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exfalso
        have hN : N.det = -1 := eq_neg_of_add_eq_zero_left h
        have : M.det = - (SliceB.mat D.P x).det := by rw [hMN, det_mul, hN, neg_one_mul]
        have h3 : 0 < (SliceB.mat D.P x).det.re := hxV.2
        have h4 : 0 < M.det.re := hdet
        rw [this, Complex.neg_re] at h4
        linarith
    have hNunit : N.det ≠ 0 := by rw [hNdet]; exact one_ne_zero
    have hmem : toGL N ∈ soC Q := by
      rw [mem_soC_iff, toGL_val hNunit]; exact ⟨hNiso, hNdet⟩
    refine ⟨(ArchSOC.mk Q (toGL N) hmem, x), ⟨mem_univ _, hxV, ?_⟩, ?_⟩
    · show beta D x ∈ E
      rw [hx]; exact hX
    · show cols (ArchSOC.mat Q (ArchSOC.mk Q (toGL N) hmem) * SliceB.mat D.P x) = X
      rw [ArchSOC.mat_mk, toGL_val hNunit, ← hMN]
      rfl

theorem measurableSet_slab {E : Set (UIdx n → ℂ)} (hE : MeasurableSet E) :
    MeasurableSet (V0 D ∩ beta D ⁻¹' E) :=
  (isOpen_V0 D).measurableSet.inter ((continuous_beta D).measurable hE)

theorem injOn_chart_slab (E : Set (UIdx n → ℂ)) : InjOn (chart D) (univ ×ˢ (V0 D ∩ beta D ⁻¹' E)) :=
  injOn_chart D ((injOn_beta_V0 D).mono inter_subset_left)

/-- $\tau$ on the slab over $E \subseteq U_0$ is the volume of the region. -/
theorem tauM_slab {E : Set (UIdx n → ℂ)} (hE : MeasurableSet E) (hEU : E ⊆ U0 D) :
    tauM D (univ ×ˢ (V0 D ∩ beta D ⁻¹' E)) = volume (regionC Q E) := by
  rw [tauM, Leray.fibreCount_apply_of_injOn (continuous_chart D) (isLocInj_chart D) volume
    (MeasurableSet.univ.prod (measurableSet_slab D hE)) (injOn_chart_slab D E), image_chart D hEU]

theorem tauM_ne_zero : tauM D ≠ 0 := by
  intro h0
  have h := tauM_slab D (isOpen_U0 D).measurableSet subset_rfl
  rw [h0, Measure.coe_zero, Pi.zero_apply] at h
  have hne : cols (1 : 𝕄) ∈ regionC Q (U0 D) := by
    refine ⟨?_, ?_⟩
    · rw [ofCols_cols, det_one]; simp
    · rw [ofCols_cols, phi_one]; exact coeffUC_mem_U0 D
  exact (isOpen_regionC (isOpen_U0 D)).measure_ne_zero volume ⟨_, hne⟩ h.symm

theorem lerayC_ne_zero : lerayC D ≠ 0 := by
  intro h0
  have h := lerayFibration D
  rw [lerayDC, h0, ENNReal.coe_zero, zero_smul, Measure.zero_prod] at h
  exact tauM_ne_zero D h

instance : IsFiniteMeasureOnCompacts (lerayDC D) := ⟨fun K hK => by
  rw [lerayDC, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hK.measure_lt_top⟩

/-- **The Leray measure is a left Haar measure on $SO(Q)(\mathbb C)$.** -/
instance isHaarMeasure_lerayDC : (lerayDC D).IsHaarMeasure :=
  IsHaarMeasure.smul _ (by simpa using lerayC_ne_zero D) ENNReal.coe_ne_top

/-! ### The fibration identity on regions -/

theorem image_slab {E : Set (UIdx n → ℂ)} (hEU : E ⊆ U0 D) : beta D '' (V0 D ∩ beta D ⁻¹' E) = E := by
  ext c
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
  · intro hc
    obtain ⟨x, hxV, hx⟩ := hEU hc
    exact ⟨x, ⟨hxV, by rw [mem_preimage, hx]; exact hc⟩, hx⟩

/-- **Integrals against $\kappa_0$ in coefficient space**: for $E \subseteq U_0$,
$\int_{V_0 \cap \beta^{-1}E}\psi\,d\kappa_0 = \int_E\rho(c)\,\psi(\beta^{-1}c)\,dc$. -/
theorem setLIntegral_kappa0 {E : Set (UIdx n → ℂ)} (hE : MeasurableSet E) (hEU : E ⊆ U0 D)
    {ψ : SliceB D.P → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ b in V0 D ∩ beta D ⁻¹' E, ψ b ∂kappa0 D = ∫⁻ c in E, ENNReal.ofReal (rho D c) * ψ (sec D c) := by
  have hS := measurableSet_slab D hE
  set H : (UIdx n → ℂ) → ℝ≥0∞ := fun c => ENNReal.ofReal (rho D c) * ψ (sec D c)
  rw [kappa0, setLIntegral_withDensity_eq_setLIntegral_mul _ (Leray.measurable_char (thetaB D)
    (continuous_thetaB D)) hψ hS]
  have h1 : ∫⁻ b in V0 D ∩ beta D ⁻¹' E, ((fun x => (thetaB D x : ℝ≥0∞)) * ψ) b ∂kappa1 D =
      ∫⁻ b in V0 D ∩ beta D ⁻¹' E, H (beta D b) ∂kappa1 D := by
    refine setLIntegral_congr_fun hS fun b hb => ?_
    simp only [Pi.mul_apply, H, rho, sec_beta D hb.1, ENNReal.ofReal_coe_nnreal]
  have hmap := Leray.map_restrict_fibreCount (continuous_beta D) (isLocInj_beta D) volume hS
    ((injOn_beta_V0 D).mono inter_subset_left)
  rw [image_slab D hEU] at hmap
  have hHm : AEMeasurable H (volume.restrict E) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable ((continuousOn_rho D).mono hEU |>.aemeasurable hE)).mul
      (hψ.comp_aemeasurable ((continuousOn_sec D).mono hEU |>.aemeasurable hE))
  rw [h1, ← lintegral_map' (by rw [kappa1, hmap]; exact hHm) (continuous_beta D).aemeasurable, kappa1, hmap]

/-- **The fibration identity on regions**: for $E \subseteq U_0$ and measurable $\varphi \ge 0$,
$\int_{\{\operatorname{Re}\det X > 0,\ \Phi_Q(X) \in E\}}\varphi\,dX =
\int_E\rho(c)\int_{SO(Q)}\varphi(g\beta^{-1}(c))\,d\mu_Q(g)\,dc$. -/
theorem lintegral_regionC {φ : (Fin n → Fin n → ℂ) → ℝ≥0∞} (hφ : Measurable φ) {E : Set (UIdx n → ℂ)}
    (hE : MeasurableSet E) (hEU : E ⊆ U0 D) :
    ∫⁻ X in regionC Q E, φ X =
      ∫⁻ c in E, ENNReal.ofReal (rho D c) * ∫⁻ g, φ (chart D (g, sec D c)) ∂lerayDC D := by
  have hS := measurableSet_slab D hE
  have hT : MeasurableSet ((univ : Set (ArchSOC Q)) ×ˢ (V0 D ∩ beta D ⁻¹' E)) := MeasurableSet.univ.prod hS
  have hmap := Leray.map_restrict_fibreCount (continuous_chart D) (isLocInj_chart D) volume hT
    (injOn_chart_slab D E)
  rw [image_chart D hEU] at hmap
  rw [← hmap, lintegral_map hφ (continuous_chart D).measurable, lerayFibration, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod_symm (fun z => φ (chart D z))
      (hφ.comp (continuous_chart D).measurable).aemeasurable]
  exact setLIntegral_kappa0 D hE hEU
    (Measurable.lintegral_prod_left' (μ := lerayDC D) (hφ.comp (continuous_chart D).measurable))


/-! ### The Leray limit for compactly supported continuous functions -/

/-- **$g \mapsto g$ is proper** from $SO(Q)(\mathbb C)$ to $M_n(\mathbb C)$ ($g^{-1} = A^{-1}g^{\mathsf T}A$). -/
theorem isCompact_mat_preimage (hA0 : (gramC Q).det ≠ 0) {K : Set 𝕄} (hK : IsCompact K) :
    IsCompact (ArchSOC.mat Q ⁻¹' K) := by
  set A := gramC Q
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hA0
  set C : Set 𝕄 := K ∩ {M | Mᵀ * A * M = A ∧ M.det = 1}
  have hC : IsCompact C := hK.inter_right ((isClosed_eq ((continuous_id.matrix_transpose.matrix_mul
    continuous_const).matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq continuous_id.matrix_det continuous_const))
  let φ : 𝕄 → 𝕄 × 𝕄ᵐᵒᵖ := fun M => (M, MulOpposite.op (A⁻¹ * Mᵀ * A))
  have hφ : Continuous φ := continuous_id.prodMk (MulOpposite.continuous_op.comp
    ((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const))
  set S : Set (GL (Fin n) ℂ) := {x | x ∈ soC Q ∧ (x : 𝕄) ∈ K}
  have hS : IsCompact S := by
    rw [(Units.isEmbedding_embedProduct (M := 𝕄)).isCompact_iff]
    have : Units.embedProduct 𝕄 '' S = φ '' C := by
      ext ⟨M, N⟩
      constructor
      · rintro ⟨x, ⟨hx, hxK⟩, hxMN⟩
        have hiso : (x : 𝕄)ᵀ * A * x = A := hx.1
        refine ⟨x, ⟨hxK, hiso, hx.2⟩, ?_⟩
        rw [← hxMN]
        simp only [φ, Units.embedProduct_apply, Prod.mk.injEq, true_and]
        congr 1
        set X : 𝕄 := (x : 𝕄)
        set Xi : 𝕄 := ((x⁻¹ : GL (Fin n) ℂ) : 𝕄)
        have hXXi : X * Xi = 1 := by simp only [X, Xi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h1 : A⁻¹ * Xᵀ * A * X = 1 := by
          calc A⁻¹ * Xᵀ * A * X = A⁻¹ * (Xᵀ * A * X) := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hiso, Matrix.nonsing_inv_mul _ hA]
        calc A⁻¹ * Xᵀ * A = A⁻¹ * Xᵀ * A * (X * Xi) := by rw [hXXi, Matrix.mul_one]
          _ = Xi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      · rintro ⟨M', ⟨hM'K, hiso, hdet⟩, hM'⟩
        have hinv : A⁻¹ * M'ᵀ * A * M' = 1 := by
          calc A⁻¹ * M'ᵀ * A * M' = A⁻¹ * (M'ᵀ * A * M') := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hiso, Matrix.nonsing_inv_mul _ hA]
        let x : GL (Fin n) ℂ := ⟨M', A⁻¹ * M'ᵀ * A, mul_eq_one_comm.mp hinv, hinv⟩
        have hx : x ∈ soC Q := ⟨hiso, hdet⟩
        exact ⟨x, ⟨hx, hM'K⟩, by rw [← hM']; rfl⟩
    rw [this]; exact hC.image hφ
  have hemb : Topology.IsClosedEmbedding (ArchSOC.incl Q) := (isClosed_soC Q).isClosedEmbedding_subtypeVal
  have : ArchSOC.mat Q ⁻¹' K = ArchSOC.incl Q ⁻¹' S := by
    ext g
    simp only [mem_preimage, S, mem_ofPred_eq, ArchSOC.mat]
    exact ⟨fun h => ⟨ArchSOC.incl_mem Q g, h⟩, fun h => h.2⟩
  rw [this]
  exact hemb.isCompact_preimage hS

theorem continuous_ofCols_mul :
    Continuous fun p : (Fin n → Fin n → ℂ) × SliceB D.P => ofCols p.1 * SliceB.mat D.P p.2⁻¹ :=
  (continuous_ofCols.comp continuous_fst).matrix_mul
    ((SliceB.continuous_mat D.P).comp (continuous_inv.comp continuous_snd))

theorem continuous_chart_swap {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) :
    Continuous (Function.uncurry fun (b : SliceB D.P) (g : ArchSOC Q) => f (chart D (g, b))) :=
  hf.comp ((continuous_chart D).comp (continuous_snd.prodMk continuous_fst))

/-- **The fibre integral** $F_f(b) = \int_{SO(Q)} f(gb)\,d\mu_Q(g)$. -/
def fibreInt (f : (Fin n → Fin n → ℂ) → ℝ) (b : SliceB D.P) : ℝ := ∫ g, f (chart D (g, b)) ∂lerayDC D

theorem ofCols_chart_mul_inv (g : ArchSOC Q) (b : SliceB D.P) :
    ofCols (chart D (g, b)) * SliceB.mat D.P b⁻¹ = ArchSOC.mat Q g := by
  rw [chart, ofCols_cols, Matrix.mul_assoc, SliceB.mat_mul_inv, Matrix.mul_one]

theorem continuous_fibreInt {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (fibreInt D f) := by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨N, hNc, hNn⟩ := exists_compact_mem_nhds b₀
  set K' : Set 𝕄 :=
    (fun p : (Fin n → Fin n → ℂ) × SliceB D.P => ofCols p.1 * SliceB.mat D.P p.2⁻¹) '' (tsupport f ×ˢ N)
  have hK' : IsCompact K' := (hfc.isCompact.prod hNc).image (continuous_ofCols_mul D)
  set L := ArchSOC.mat Q ⁻¹' K'
  have hL : IsCompact L := isCompact_mat_preimage D.det_gram_ne_zero hK'
  have hsupp : ∀ b ∈ N, ∀ g ∉ L, f (chart D (g, b)) = 0 := by
    intro b hb g hg
    by_contra hne
    exact hg ⟨(chart D (g, b), b), ⟨subset_tsupport f hne, hb⟩, ofCols_chart_mul_inv D g b⟩
  have hcont : Continuous fun b : SliceB D.P => ∫ g in L, f (chart D (g, b)) ∂lerayDC D :=
    continuous_parametric_integral_of_continuous (continuous_chart_swap D hf) hL
  refine hcont.continuousAt.congr ?_
  filter_upwards [hNn] with b hb
  rw [fibreInt, setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => hsupp b hb g hg]

theorem hasCompactSupport_fibre {f : (Fin n → Fin n → ℂ) → ℝ} (hfc : HasCompactSupport f) (b : SliceB D.P) :
    HasCompactSupport fun g : ArchSOC Q => f (chart D (g, b)) := by
  set K' : Set 𝕄 := (fun X => ofCols X * SliceB.mat D.P b⁻¹) '' tsupport f
  have hK' : IsCompact K' := hfc.isCompact.image (continuous_ofCols.matrix_mul continuous_const)
  refine HasCompactSupport.intro (isCompact_mat_preimage D.det_gram_ne_zero hK') fun g hg => ?_
  by_contra hne
  exact hg ⟨chart D (g, b), subset_tsupport f hne, ofCols_chart_mul_inv D g b⟩

/-- **The region of the Leray limit**: $\{X \in M_n(\mathbb C) : \operatorname{Re}\det X > 0,\
\Phi_Q(X) \in \bar B_\varepsilon(c_Q)\}$ (sup-norm ball in complex coefficient coordinates). -/
def lerayRegionC (Q : QuadForm ℂ n) (ε : ℝ) : Set (Fin n → Fin n → ℂ) :=
  regionC Q (Metric.closedBall (coeffUC Q) ε)

/-- **The Leray approximant** at a complex place: $\frac{1}{\mathrm{Leb}(\bar B_\varepsilon(c_Q))}
\int_{\{\operatorname{Re}\det X > 0,\ \Phi_Q(X) \in \bar B_\varepsilon(c_Q)\}} f(X)\,dX$ (real Lebesgue measures on
$M_n(\mathbb C) = \mathbb R^{2n^2}$ and on $\mathbb C^{n(n+1)/2}$). It depends only on $Q$. -/
def lerayApproxC (Q : QuadForm ℂ n) (f : (Fin n → Fin n → ℂ) → ℝ) (ε : ℝ) : ℝ :=
  (∫ X in lerayRegionC Q ε, f X) / (volume (Metric.closedBall (coeffUC Q) ε)).toReal

theorem eventually_closedBall_subset :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Metric.closedBall (coeffUC Q) ε ⊆ U0 D := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (isOpen_U0 D) _ (coeffUC_mem_U0 D)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  exact (Metric.closedBall_subset_ball hε.2).trans hsub

/-- The fibration identity on the Leray regions, for $f \ge 0$. -/
theorem lintegral_lerayRegionC {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ X, 0 ≤ f X) {ε : ℝ} (hε : Metric.closedBall (coeffUC Q) ε ⊆ U0 D) :
    ∫⁻ X in lerayRegionC Q ε, ENNReal.ofReal (f X) =
      ∫⁻ c in Metric.closedBall (coeffUC Q) ε, ENNReal.ofReal (fibreInt D f (sec D c) * rho D c) := by
  have hB : MeasurableSet (Metric.closedBall (coeffUC Q) ε) := Metric.isClosed_closedBall.measurableSet
  rw [lerayRegionC, lintegral_regionC D (φ := fun X => ENNReal.ofReal (f X))
    (ENNReal.measurable_ofReal.comp hf.measurable) hB hε]
  refine setLIntegral_congr_fun hB fun c _ => ?_
  have hinner : ∫⁻ g, ENNReal.ofReal (f (chart D (g, sec D c))) ∂lerayDC D =
      ENNReal.ofReal (fibreInt D f (sec D c)) := by
    rw [fibreInt, ofReal_integral_eq_lintegral_ofReal]
    · exact (hf.comp ((continuous_chart D).comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hasCompactSupport_fibre D hfc _)
    · exact Filter.Eventually.of_forall fun g => hf0 _
  have h0 : 0 ≤ fibreInt D f (sec D c) := integral_nonneg fun g => hf0 _
  rw [hinner, mul_comm, ← ENNReal.ofReal_mul h0]

theorem volume_closedBall_pos {ε : ℝ} (hε : 0 < ε) : 0 < volume (Metric.closedBall (coeffUC Q) ε) :=
  Metric.measure_closedBall_pos volume _ hε

theorem volume_closedBall_ne_top (ε : ℝ) : volume (Metric.closedBall (coeffUC Q) ε) ≠ ∞ :=
  measure_closedBall_lt_top.ne

/-- **The Leray limit, $f \ge 0$.** -/
theorem tendsto_lerayApproxC_of_nonneg {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ X, 0 ≤ f X) :
    Tendsto (lerayApproxC Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D)) := by
  set H : (UIdx n → ℂ) → ℝ := fun c => fibreInt D f (sec D c) * rho D c
  have hHc : ContinuousOn H (U0 D) :=
    ((continuous_fibreInt D hf hfc).comp_continuousOn (continuousOn_sec D)).mul (continuousOn_rho D)
  have hH0 : ∀ c ∈ U0 D, 0 ≤ H c := fun c _ => mul_nonneg (integral_nonneg fun g => hf0 _) (rho_nonneg D c)
  have h := Leray.tendsto_avg_closedBall volume (c₀ := coeffUC Q) (fun ε hε => volume_closedBall_pos hε)
    volume_closedBall_ne_top (isOpen_U0 D) (coeffUC_mem_U0 D) hHc hH0
  have hH1 : H (coeffUC Q) = ∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
    simp only [H, rho_coeffUC, mul_one, sec_coeffUC, fibreInt, chart, SliceB.mat_one]
  rw [hH1] at h
  refine h.congr' ?_
  filter_upwards [eventually_closedBall_subset D] with ε hsub
  rw [lerayApproxC, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => hf0 X)
      hf.aestronglyMeasurable, lintegral_lerayRegionC D hf hfc hf0 hsub]

/-- **The Leray limit** at a complex place: for every compactly supported continuous $f$ on $M_n(\mathbb C)$,
`lerayApproxC Q f ε` $\to \int_{SO(Q)(\mathbb C)} f\,d\mu_Q$ as $\varepsilon \to 0^+$. -/
theorem tendsto_lerayApproxC {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (lerayApproxC Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D)) := by
  set fp : (Fin n → Fin n → ℂ) → ℝ := fun X => max (f X) 0
  set fm : (Fin n → Fin n → ℂ) → ℝ := fun X => max (-f X) 0
  have hfp : Continuous fp := hf.max continuous_const
  have hfm : Continuous fm := hf.neg.max continuous_const
  have hfpc : HasCompactSupport fp := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fp, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hfmc : HasCompactSupport fm := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fm, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hp := tendsto_lerayApproxC_of_nonneg D hfp hfpc (fun X => le_max_right _ _)
  have hm := tendsto_lerayApproxC_of_nonneg D hfm hfmc (fun X => le_max_right _ _)
  have hsplit : ∀ ε, lerayApproxC Q f ε = lerayApproxC Q fp ε - lerayApproxC Q fm ε := by
    intro ε
    have hip : IntegrableOn fp (lerayRegionC Q ε) := (hfp.integrable_of_hasCompactSupport hfpc).integrableOn
    have him : IntegrableOn fm (lerayRegionC Q ε) := (hfm.integrable_of_hasCompactSupport hfmc).integrableOn
    rw [lerayApproxC, lerayApproxC, lerayApproxC, ← sub_div, ← integral_sub hip him]
    congr 2; funext X; exact (max_zero_sub_max_neg_zero_eq_self (f X)).symm
  have hG : ∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D =
      ∫ g, fp (cols (ArchSOC.mat Q g)) ∂lerayDC D - ∫ g, fm (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
    have hc1 := hasCompactSupport_fibre D hfpc 1
    have hc2 := hasCompactSupport_fibre D hfmc 1
    simp only [chart, SliceB.mat_one, Matrix.mul_one] at hc1 hc2
    have i1 : Integrable (fun g => fp (cols (ArchSOC.mat Q g))) (lerayDC D) :=
      (hfp.comp (continuous_cols.comp (ArchSOC.continuous_mat Q))).integrable_of_hasCompactSupport hc1
    have i2 : Integrable (fun g => fm (cols (ArchSOC.mat Q g))) (lerayDC D) :=
      (hfm.comp (continuous_cols.comp (ArchSOC.continuous_mat Q))).integrable_of_hasCompactSupport hc2
    rw [← integral_sub i1 i2]
    congr 1; funext g; exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hG, show lerayApproxC Q f = fun ε => lerayApproxC Q fp ε - lerayApproxC Q fm ε from funext hsplit]
  exact hp.sub hm

/-! ### Uniqueness -/

/-- A bump function at the identity matrix. -/
def bump (n : ℕ) (X : Fin n → Fin n → ℂ) : ℝ := max 0 (1 - dist X (cols (1 : Matrix (Fin n) (Fin n) ℂ)))

theorem continuous_bump : Continuous (bump n) :=
  continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))

theorem hasCompactSupport_bump : HasCompactSupport (bump n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (cols (1 : 𝕄)) 1) fun X hX => ?_
  simp only [Metric.mem_closedBall, not_le] at hX
  simp only [bump]
  exact max_eq_left (by linarith)

theorem bump_nonneg (X : Fin n → Fin n → ℂ) : 0 ≤ bump n X := le_max_left _ _

theorem integral_bump_pos : 0 < ∫ g, bump n (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
  have hc := hasCompactSupport_fibre D (hasCompactSupport_bump (n := n)) 1
  simp only [chart, SliceB.mat_one, Matrix.mul_one] at hc
  refine (continuous_bump.comp (continuous_cols.comp (ArchSOC.continuous_mat Q))).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hc (fun g => bump_nonneg _) (x := 1) ?_
  simp [ArchSOC.mat_one, bump]

/-- **Uniqueness**: a left-invariant measure on $SO(Q)(\mathbb C)$, finite on compact sets, that satisfies the Leray
limit for every compactly supported continuous $f$ equals $\mu_Q$. -/
theorem lerayDC_unique (μ' : Measure (ArchSOC Q)) [μ'.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ']
    (h : ∀ f : (Fin n → Fin n → ℂ) → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (lerayApproxC Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q g)) ∂μ'))) :
    μ' = lerayDC D := by
  have hμ := isMulLeftInvariant_eq_smul μ' (lerayDC D)
  set k := haarScalarFactor μ' (lerayDC D)
  have h1 := tendsto_nhds_unique (h (bump n) continuous_bump hasCompactSupport_bump)
    (tendsto_lerayApproxC D continuous_bump hasCompactSupport_bump)
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h1
  have hpos := integral_bump_pos D
  have hk : (k : ℝ) = 1 := mul_right_cancel₀ hpos.ne' (h1.trans (one_mul _).symm)
  rw [hμ, show k = 1 from NNReal.coe_eq_one.mp hk, one_smul]

/-- **Independence of the choices**: two slice data give the same Leray measure. -/
theorem lerayDC_eq (D D' : DiagC Q) : lerayDC D = lerayDC D' :=
  lerayDC_unique D' (lerayDC D) fun _ hf hfc => tendsto_lerayApproxC D hf hfc

/-! ### The canonical Leray measure at a complex place -/

/-- **The Leray (gauge-form) measure** $\mu_Q$ on $SO(Q)(\mathbb C)$ for a nondegenerate complex quadratic form: the
measure with $dX = \mu_Q \otimes dc$ near the fibre $\Phi_Q^{-1}(c_Q) \cap \{\operatorname{Re}\det > 0\}$
(`lerayMeasureC_fibration`), characterized by the Leray limit (`tendsto_lerayMeasureC`, `lerayMeasureC_unique`).
Normalization: the real Lebesgue measures $dX$ on $M_n(\mathbb C) = \mathbb R^{2n^2}$ and $dc$ on the complex
coefficient space $\mathbb C^{n(n+1)/2} = \mathbb R^{n(n+1)}$ (coordinates $c_{ij}$, $i \le j$); this is Weil's
$|dX/dc|_{\mathbb C}$ with $|z|_{\mathbb C} = |z|^2$. -/
@[kb "weil1982" "§2.2 (gauge forms), §2.4 Theorem 2.4.3, p. 25 (matching measures on G, H, G/H) [unverified]"]
def lerayMeasureC (Q : QuadForm ℂ n) (hQ : gramDetC Q ≠ 0) : Measure (ArchSOC Q) :=
  lerayDC (DiagC.ofExists Q hQ)

variable (hQ : gramDetC Q ≠ 0)

/-- **$\mu_Q$ is a left Haar measure** on $SO(Q)(\mathbb C)$. -/
@[kb "weil1982" "§2.2 (gauge forms) [unverified]"]
theorem isHaarMeasure_lerayMeasureC : (lerayMeasureC Q hQ).IsHaarMeasure := isHaarMeasure_lerayDC _

/-- **The fibration identity** at a complex place: for any slice data $D$, the fibre-counting pull-back of $dX$ along
$(g, b) \mapsto gb$ (`Leray.fibreCount`) is $\mu_Q \otimes \kappa_0$. -/
@[kb "weil1982" "§2.4 Theorem 2.4.3, p. 25 (matching measures) [unverified]"]
theorem lerayMeasureC_fibration (D : DiagC Q) :
    Leray.fibreCount (chart D) volume = (lerayMeasureC Q hQ).prod (kappa0 D) := by
  rw [lerayMeasureC, lerayDC_eq (DiagC.ofExists Q hQ) D, lerayFibration]

/-- **The fibration identity on regions near the fibre**: for $E \subseteq U_0$ (a neighbourhood of $c_Q$),
$\int_{\{\operatorname{Re}\det X > 0,\ \Phi_Q(X) \in E\}}\varphi\,dX = \int_E\rho(c)\int\varphi(g\beta^{-1}(c))\,
d\mu_Q(g)\,dc$, with $\rho$ continuous and $\rho(c_Q) = 1$ (`rho_coeffUC`). -/
@[kb "weil1982" "§2.4 Theorem 2.4.3, p. 25 (matching measures) [unverified]"]
theorem lerayMeasureC_region (D : DiagC Q) {φ : (Fin n → Fin n → ℂ) → ℝ≥0∞} (hφ : Measurable φ)
    {E : Set (UIdx n → ℂ)} (hE : MeasurableSet E) (hEU : E ⊆ U0 D) :
    ∫⁻ X in regionC Q E, φ X =
      ∫⁻ c in E, ENNReal.ofReal (rho D c) * ∫⁻ g, φ (chart D (g, sec D c)) ∂lerayMeasureC Q hQ := by
  rw [lerayMeasureC, lerayDC_eq (DiagC.ofExists Q hQ) D]
  exact lintegral_regionC D hφ hE hEU

/-- **The Leray limit** at a complex place. -/
@[kb "weil1982" "§2.2 (gauge forms as limits of volume ratios) [unverified]"]
theorem tendsto_lerayMeasureC {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (lerayApproxC Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayMeasureC Q hQ)) :=
  tendsto_lerayApproxC _ hf hfc

/-- **The Leray limit characterizes $\mu_Q$** at a complex place. -/
@[kb "weil1982" "§2.2 (gauge forms) [unverified]"]
theorem lerayMeasureC_unique (μ' : Measure (ArchSOC Q)) [μ'.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ']
    (h : ∀ f : (Fin n → Fin n → ℂ) → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (lerayApproxC Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q g)) ∂μ'))) :
    μ' = lerayMeasureC Q hQ :=
  lerayDC_unique _ μ' h

end QuadFormsKB.Tamagawa.Measure.LerayComplex
