import QuadFormsKB.Tamagawa.Measure.ArchSO
import QuadFormsKB.Tamagawa.Measure.LeraySlice

/-!
# The Leray (gauge-form) measure on $SO(Q)(\mathbb R)$ for a real form of any signature

**At the real places.** For a nondegenerate real quadratic form $Q$ in $n$ variables (any signature) with
Gram matrix $A$ (`gramMatrixR Q`, $Q(x) = x^{\mathsf T}Ax$), let
$$\Phi_Q : M_n(\mathbb R) \to \mathbb R^{n(n+1)/2},\qquad X \mapsto \text{the coefficients of } y \mapsto Q(Xy)$$
(`phi`; this is `pullCoeff` in matrix form, `phi_eq_pullCoeff`). Its fibre over $c_Q$ (`coeffU Q`) meeting
$\{\det X > 0\}$ is $SO(Q)(\mathbb R)$. The **Leray measure** $\mu_Q$ on $SO(Q)(\mathbb R)$ is the measure with
$dX = \mu_Q \otimes dc$ near this fibre (Weil's gauge form $|dX/dc|$, Weil 1982 §2.2 and §2.4). We construct it
without differential forms:

* **The slice group** $B = P B^+ P^{-1}$ (`sliceGroup`), $B^+$ the upper triangular matrices with positive diagonal
  and $P^{\mathsf T}AP = D$ diagonal (spectral theorem). It acts on coefficient space by $c \mapsto c\cdot b$
  (`act`, the coefficients of $y \mapsto c(by)$), and $b \mapsto \Phi_Q(b)$ is injective on $B$
  (`phi_injOn_slice`; the uniqueness of the $LDL^{\mathsf T}$ decomposition). The inverse function theorem at $b = 1$
  gives a continuous local section, and equivariance spreads it to the open image $U = \Phi_Q(B)$.
* **The chart** $m : SO(Q) \times B \to M_n(\mathbb R)$, $(g, b) \mapsto gb$, is a measurable embedding onto
  $\{X : \Phi_Q(X) \in U,\ \det X > 0\}$. The pull-back $\tau$ of $dX$ is left $SO(Q)$-invariant and relatively
  right $B$-invariant with character $|\det b|^n$, so by the abstract slice decomposition (`Leray.slice_decomposition`)
  $\tau = \mu_Q \otimes \kappa_0$ with an explicit comparison measure $\kappa_0$ on $B$ whose image in coefficient
  space has a continuous density $\rho$ with $\rho(c_Q) = 1$ (`lerayFibration`).

**Results.** `isHaarMeasure_leray` ($\mu_Q$ is a left Haar measure, any signature); `tendsto_leray`: the Leray limit
$$\int_{SO(Q)} f\,d\mu_Q = \lim_{\varepsilon\to0^+}\frac{1}{\mathrm{Leb}(B_\varepsilon(c_Q))}
\int_{\{\det X>0,\ \Phi_Q(X) \in B_\varepsilon(c_Q)\}} f(X)\,dX$$
for every compactly supported continuous $f$ on $M_n(\mathbb R)$, which characterizes $\mu_Q$ (`leray_unique`), so the
construction does not depend on $P$; `leray_eq_mu` (agreement with `ArchSO.mu`): for positive definite $Q$, $\mu_Q$ is `ArchSO.mu Q`, of total mass `archVolSO n (gramDetR Q)`.

Coordinates: matrices $M$ act on columns; the Lebesgue measure on $M_n(\mathbb R)$ is `volume` on
`Fin n → Fin n → ℝ` in the column convention (`cols M j i = M i j`), and on coefficient space `UIdx n → ℝ` (the coefficient coordinates $c_{ij}$, $i \le j$).
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.ArchSOMeasure

variable {n : ℕ}

/-! ### Coefficient coordinates of symmetric matrices -/

/-- **Coefficient coordinates of a matrix** $S$: $c_{ij} = w_{ij}S_{ij}$ ($i \le j$), $w_{ii} = 1$, $w_{ij} = 2$
($i < j$): the coefficients of $y \mapsto y^{\mathsf T}Sy$ when $S$ is symmetric. -/
def wtU (S : Matrix (Fin n) (Fin n) ℝ) : UIdx n → ℝ := fun p => wt p * S p.1.1 p.1.2

/-- **The symmetric matrix with coefficient coordinates** $c$: $S_{ij} = c_{\min,\max}/w_{\min,\max}$. -/
def symOf (c : UIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if h : i ≤ j then c ⟨(i, j), h⟩ / wt (⟨(i, j), h⟩ : UIdx n)
  else c ⟨(j, i), le_of_not_ge h⟩ / wt (⟨(j, i), le_of_not_ge h⟩ : UIdx n)

theorem symOf_transpose (c : UIdx n → ℝ) : (symOf c)ᵀ = symOf c := by
  ext i j
  simp only [transpose_apply, symOf]
  by_cases h1 : j ≤ i <;> by_cases h2 : i ≤ j
  · have : i = j := le_antisymm h2 h1
    subst this; rfl
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_total i j) (by tauto)

theorem wtU_symOf (c : UIdx n → ℝ) : wtU (symOf c) = c := by
  funext p
  simp only [wtU, symOf, dif_pos p.2]
  rw [mul_div_cancel₀ _ (wt_pos p).ne']

theorem symOf_wtU {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = S) : symOf (wtU S) = S := by
  ext i j
  simp only [symOf, wtU]
  split_ifs with h
  · rw [mul_div_cancel_left₀ _ (wt_pos _).ne']
  · rw [mul_div_cancel_left₀ _ (wt_pos _).ne']
    exact (congrFun (congrFun hS i) j).symm.trans (by rfl) |>.symm ▸ by
      rw [← transpose_apply S i j, hS]

theorem wtU_inj {S T : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = S) (hT : Tᵀ = T) (h : wtU S = wtU T) : S = T := by
  rw [← symOf_wtU hS, ← symOf_wtU hT, h]

theorem wtU_add (S T : Matrix (Fin n) (Fin n) ℝ) : wtU (S + T) = wtU S + wtU T := by
  funext p; simp [wtU, mul_add]

theorem wtU_smul (r : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) : wtU (r • S) = r • wtU S := by
  funext p; simp [wtU]; ring

theorem symOf_add (c d : UIdx n → ℝ) : symOf (c + d) = symOf c + symOf d := by
  ext i j; simp only [symOf, Pi.add_apply, Matrix.add_apply]; split_ifs <;> ring

theorem symOf_smul (r : ℝ) (c : UIdx n → ℝ) : symOf (r • c) = r • symOf c := by
  ext i j; simp only [symOf, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- **The right action on coefficient space**: $c \cdot b$ = the coefficients of $y \mapsto c(by)$, i.e. the Gram
matrix $b^{\mathsf T}S_c b$. -/
def act (b : Matrix (Fin n) (Fin n) ℝ) : (UIdx n → ℝ) →ₗ[ℝ] (UIdx n → ℝ) where
  toFun c := wtU (bᵀ * symOf c * b)
  map_add' c d := by rw [symOf_add, Matrix.mul_add, Matrix.add_mul, wtU_add]
  map_smul' r c := by
    rw [symOf_smul, Matrix.mul_smul, Matrix.smul_mul, wtU_smul]; rfl

theorem act_apply (b : Matrix (Fin n) (Fin n) ℝ) (c : UIdx n → ℝ) : act b c = wtU (bᵀ * symOf c * b) := rfl

theorem symOf_act (b : Matrix (Fin n) (Fin n) ℝ) (c : UIdx n → ℝ) : symOf (act b c) = bᵀ * symOf c * b := by
  rw [act_apply, symOf_wtU]
  rw [transpose_mul, transpose_mul, transpose_transpose, symOf_transpose, Matrix.mul_assoc]

theorem act_mul (b b' : Matrix (Fin n) (Fin n) ℝ) (c : UIdx n → ℝ) : act (b * b') c = act b' (act b c) := by
  rw [act_apply, act_apply, symOf_act, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem act_one (c : UIdx n → ℝ) : act 1 c = c := by
  rw [act_apply, transpose_one, Matrix.one_mul, Matrix.mul_one, wtU_symOf]

/-! ### The map $\Phi_Q$ -/

/-- The Gram matrix is symmetric. -/
theorem gram_transpose (Q : QuadForm ℝ n) : (gramMatrixR Q)ᵀ = gramMatrixR Q := by
  have := gramMatrixR_isHermitian Q
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

/-- **$\Phi_Q(M)$**: the coefficient coordinates of $M^{\mathsf T}AM$, i.e. of the form $y \mapsto Q(My)$. -/
def phi (Q : QuadForm ℝ n) (M : Matrix (Fin n) (Fin n) ℝ) : UIdx n → ℝ := wtU (Mᵀ * gramMatrixR Q * M)

/-- **The column coordinates** of a matrix: `cols M j` is column $j$. -/
def cols (M : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ := fun j i => M i j

theorem gram_sym_mul (Q : QuadForm ℝ n) (M : Matrix (Fin n) (Fin n) ℝ) :
    (Mᵀ * gramMatrixR Q * M)ᵀ = Mᵀ * gramMatrixR Q * M := by
  rw [transpose_mul, transpose_mul, transpose_transpose, gram_transpose, Matrix.mul_assoc]

/-- `phi` is `pullCoeff` in matrix form. -/
theorem phi_eq_pullCoeff (Q : QuadForm ℝ n) (M : Matrix (Fin n) (Fin n) ℝ) :
    phi Q M = pullCoeff Q (cols M) := by
  rw [pullCoeff_eq]
  funext p
  simp only [phi, wtU, cols]
  congr 1
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [cols]; ring

theorem phi_one (Q : QuadForm ℝ n) : phi Q 1 = coeffU Q := by
  rw [phi, transpose_one, Matrix.one_mul, Matrix.mul_one, coeffU_eq]; rfl

theorem phi_mul (Q : QuadForm ℝ n) (M b : Matrix (Fin n) (Fin n) ℝ) : phi Q (M * b) = act b (phi Q M) := by
  rw [act_apply, phi, phi, symOf_wtU (gram_sym_mul Q M), transpose_mul]
  simp only [Matrix.mul_assoc]

theorem phi_of_isometry (Q : QuadForm ℝ n) {g : Matrix (Fin n) (Fin n) ℝ}
    (hg : gᵀ * gramMatrixR Q * g = gramMatrixR Q) (M : Matrix (Fin n) (Fin n) ℝ) : phi Q (g * M) = phi Q M := by
  rw [phi, phi, transpose_mul]
  have : Mᵀ * gᵀ * gramMatrixR Q * (g * M) = Mᵀ * (gᵀ * gramMatrixR Q * g) * M := by
    simp only [Matrix.mul_assoc]
  rw [this, hg]

theorem phi_eq_iff (Q : QuadForm ℝ n) (M N : Matrix (Fin n) (Fin n) ℝ) :
    phi Q M = phi Q N ↔ Mᵀ * gramMatrixR Q * M = Nᵀ * gramMatrixR Q * N :=
  ⟨wtU_inj (gram_sym_mul Q M) (gram_sym_mul Q N), fun h => by rw [phi, phi, h]⟩

theorem continuous_wtU : Continuous (wtU : Matrix (Fin n) (Fin n) ℝ → UIdx n → ℝ) :=
  continuous_pi fun p => continuous_const.mul ((continuous_apply _).comp (continuous_apply _))

theorem continuous_phi (Q : QuadForm ℝ n) : Continuous (phi Q) :=
  continuous_wtU.comp ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id)

/-! ### Upper triangular matrices with positive diagonal -/

/-- Upper triangular: $M_{ij} = 0$ for $j < i$. -/
def IsUT (M : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ i j : Fin n, j < i → M i j = 0

theorem IsUT.mul {M N : Matrix (Fin n) (Fin n) ℝ} (hM : IsUT M) (hN : IsUT N) : IsUT (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hM i k hk, zero_mul]
  · rw [hN k j (lt_of_lt_of_le hij (not_lt.mp hk)), mul_zero]

theorem IsUT.mul_diag {M N : Matrix (Fin n) (Fin n) ℝ} (hM : IsUT M) (hN : IsUT N) (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hM i k h, zero_mul]
    · rw [hN k i h, mul_zero]
  · simp

theorem IsUT.blockTriangular {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUT M) : M.BlockTriangular id :=
  fun i j hij => hM i j hij

theorem IsUT.inv {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUT M) : IsUT M⁻¹ := by
  by_cases hd : IsUnit M.det
  · haveI := M.invertibleOfIsUnitDet hd
    exact fun i j hij => blockTriangular_inv_of_blockTriangular hM.blockTriangular hij
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd]
    intro i j _; rfl

/-- **The positive Borel subgroup** $B^+ \le \mathrm{GL}_n(\mathbb R)$: upper triangular with positive diagonal. -/
def borelPos (n : ℕ) : Subgroup (GL (Fin n) ℝ) where
  carrier := {b | IsUT (b : Matrix (Fin n) (Fin n) ℝ) ∧ ∀ i, 0 < (b : Matrix (Fin n) (Fin n) ℝ) i i}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, fun i => ?_⟩
    · rw [Units.val_mul]; exact ha.1.mul hb.1
    · rw [Units.val_mul, ha.1.mul_diag hb.1]; exact mul_pos (ha.2 i) (hb.2 i)
  one_mem' := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp [Matrix.one_apply, hij.ne']
    · simp
  inv_mem' {b} hb := by
    have hinv : ((b⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = (b : Matrix (Fin n) (Fin n) ℝ)⁻¹ := by
      rw [Matrix.coe_units_inv]
    have hUT : IsUT ((b⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by rw [hinv]; exact hb.1.inv
    refine ⟨hUT, fun i => ?_⟩
    have h1 : ((b : Matrix (Fin n) (Fin n) ℝ) * ((b⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [hb.1.mul_diag hUT] at h1
    have := hb.2 i
    by_contra hneg
    push Not at hneg
    nlinarith

/-- **Uniqueness of the $LDL^{\mathsf T}$ decomposition**: if $u \in B^+$ and $u^{\mathsf T}Du = D$ for an invertible
diagonal $D$, then $u = 1$. -/
theorem eq_one_of_transpose_mul_diag {u : Matrix (Fin n) (Fin n) ℝ} (hu : IsUT u) (hpos : ∀ i, 0 < u i i)
    {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) (h : uᵀ * diagonal d * u = diagonal d) : u = 1 := by
  have hdet : IsUnit u.det := by
    rw [det_of_isUpperTriangular hu.blockTriangular]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne')
  -- E := D u = (u⁻¹)ᵀ D is both upper and lower triangular
  have hE : diagonal d * u = (u⁻¹)ᵀ * diagonal d := by
    have : (u⁻¹)ᵀ * (uᵀ * diagonal d * u) = (u⁻¹)ᵀ * diagonal d := by rw [h]
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Matrix.mul_nonsing_inv _ hdet,
      transpose_one, Matrix.one_mul] at this
  have hoff : ∀ i j, i ≠ j → u i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · -- i < j: (D u)_ij = d_i u_ij and ((u⁻¹)ᵀ D)_ij = (u⁻¹)_ji d_j = 0
      have e := congrFun (congrFun hE i) j
      rw [diagonal_mul, mul_diagonal, transpose_apply, hu.inv j i hlt, zero_mul] at e
      exact (mul_eq_zero.mp e).resolve_left (hd i)
    · exact hu i j hgt
  have hdiag : u = diagonal fun i => u i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  ext i j
  by_cases hij : i = j
  · subst hij
    have e := congrFun (congrFun h i) i
    rw [hdiag, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_apply_eq,
      diagonal_apply_eq] at e
    have h1 : u i i * u i i = 1 := by
      have h2 : (u i i * u i i - 1) * d i = 0 := by linear_combination e
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (hd i))
    rw [Matrix.one_apply_eq]
    nlinarith [hpos i]
  · rw [hoff i j hij, Matrix.one_apply_ne hij]

/-! ### Diagonalization and the slice group -/

/-- **Diagonalization** of the Gram matrix of a nondegenerate real form (spectral theorem):
$P^{\mathsf T}AP = \mathrm{diag}(d)$ with all $d_i \ne 0$. -/
theorem exists_diag (Q : QuadForm ℝ n) (hQ : gramDetR Q ≠ 0) :
    ∃ (P : GL (Fin n) ℝ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) ∧
      (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * P = diagonal d := by
  have hA := gramMatrixR_isHermitian Q
  set U := hA.eigenvectorUnitary
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set Um : Matrix (Fin n) (Fin n) ℝ := (U : Matrix (Fin n) (Fin n) ℝ) with hUm
  have hstar : star (U : Matrix (Fin n) (Fin n) ℝ) = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have h1 : star (U : Matrix (Fin n) (Fin n) ℝ) * U = 1 := Unitary.coe_star_mul_self U
  have h2 : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  refine ⟨⟨U, star (U : Matrix (Fin n) (Fin n) ℝ), h2, h1⟩, hA.eigenvalues, fun i => ?_, ?_⟩
  · have hdet := hA.det_eq_prod_eigenvalues
    rw [← gramDetR_eq_det] at hdet
    rw [hdet] at hQ
    simpa using (Finset.prod_ne_zero_iff.mp hQ) i (Finset.mem_univ i)
  · change (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * U = _
    rw [← hstar]
    conv_lhs => rw [hspec]
    rw [show star Um * (Um * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star Um) * Um
        = (star Um * Um) * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (star Um * Um) by
          simp only [Matrix.mul_assoc], h1, Matrix.one_mul, Matrix.mul_one]
    rfl

/-- **The slice group** $B = PB^+P^{-1}$. -/
def sliceGroup (P : GL (Fin n) ℝ) : Subgroup (GL (Fin n) ℝ) :=
  (borelPos n).comap (MulAut.conj P⁻¹).toMonoidHom

theorem mem_sliceGroup (P x : GL (Fin n) ℝ) : x ∈ sliceGroup P ↔ P⁻¹ * x * P ∈ borelPos n := by
  simp [sliceGroup]

/-- $\Phi_Q(PbP^{-1}) = (c_D\cdot b)\cdot P^{-1}$, $c_D$ the coefficients of $D = P^{\mathsf T}AP$. -/
theorem phi_conj (Q : QuadForm ℝ n) (P x : GL (Fin n) ℝ) :
    phi Q x = act ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
      (act ((P⁻¹ * x * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) (phi Q P)) := by
  rw [← phi_mul, ← phi_mul, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

theorem act_eq_self_of_borelPos {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) {u : GL (Fin n) ℝ} (hu : u ∈ borelPos n)
    (h : act (u : Matrix (Fin n) (Fin n) ℝ) (wtU (diagonal d)) = wtU (diagonal d)) : u = 1 := by
  have hD : (diagonal d)ᵀ = diagonal d := diagonal_transpose d
  rw [act_apply, symOf_wtU hD] at h
  have h' := wtU_inj (by rw [transpose_mul, transpose_mul, transpose_transpose, hD, Matrix.mul_assoc]) hD h
  exact Units.ext (eq_one_of_transpose_mul_diag hu.1 hu.2 hd h')

/-- **$\Phi_Q$ is injective on the slice group** (uniqueness of $LDL^{\mathsf T}$). -/
theorem phi_injOn_slice (Q : QuadForm ℝ n) {P : GL (Fin n) ℝ} {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0)
    (hP : (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * P = diagonal d) {x y : GL (Fin n) ℝ}
    (hx : x ∈ sliceGroup P) (hy : y ∈ sliceGroup P) (h : phi Q x = phi Q y) : x = y := by
  rw [mem_sliceGroup] at hx hy
  have hPd : phi Q P = wtU (diagonal d) := by rw [phi, hP]
  set b := P⁻¹ * x * P
  set b' := P⁻¹ * y * P
  rw [phi_conj Q P x, phi_conj Q P y] at h
  -- cancel P⁻¹
  have h1 : act (b : Matrix (Fin n) (Fin n) ℝ) (phi Q P) = act (b' : Matrix (Fin n) (Fin n) ℝ) (phi Q P) := by
    have e : ∀ c, act (P : Matrix (Fin n) (Fin n) ℝ) (act ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) c) = c :=
      fun c => by rw [← act_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, act_one]
    have := congrArg (act (P : Matrix (Fin n) (Fin n) ℝ)) h
    rwa [e, e] at this
  -- u = b' b⁻¹ fixes c_D
  have h2 : act ((b' * b⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) (wtU (diagonal d)) = wtU (diagonal d) := by
    rw [← hPd, Units.val_mul, act_mul, ← h1, ← act_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, act_one]
  have hu := act_eq_self_of_borelPos hd ((borelPos n).mul_mem hy ((borelPos n).inv_mem hx)) h2
  have hbb : b' = b := by rw [← mul_inv_eq_one]; exact hu
  have : P * b * P⁻¹ = x := by simp only [b]; group
  have : P * b' * P⁻¹ = y := by simp only [b']; group
  rw [← ‹P * b * P⁻¹ = x›, ← ‹P * b' * P⁻¹ = y›, hbb]

/-! ### Invertible matrices as units -/

open Classical in
/-- An invertible matrix as an element of $\mathrm{GL}_n(\mathbb R)$ ($1$ if singular). -/
def toGL (M : Matrix (Fin n) (Fin n) ℝ) : GL (Fin n) ℝ :=
  if h : IsUnit M.det then M.nonsingInvUnit h else 1

theorem toGL_val {M : Matrix (Fin n) (Fin n) ℝ} (h : M.det ≠ 0) : (toGL M : Matrix (Fin n) (Fin n) ℝ) = M := by
  rw [toGL, dif_pos (isUnit_iff_ne_zero.mpr h)]; rfl

theorem toGL_inv_val {M : Matrix (Fin n) (Fin n) ℝ} (h : M.det ≠ 0) :
    ((toGL M)⁻¹ : GL (Fin n) ℝ) = (M⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
  rw [toGL, dif_pos (isUnit_iff_ne_zero.mpr h)]; rfl

theorem toGL_coe (g : GL (Fin n) ℝ) : toGL (g : Matrix (Fin n) (Fin n) ℝ) = g := by
  have h : (g : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  exact Units.ext (toGL_val h)

theorem continuousOn_matrix_inv : ContinuousOn (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) {M | M.det ≠ 0} := by
  have : (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (continuous_id.matrix_det.continuousOn.inv₀ fun M hM => hM).smul
    continuous_id.matrix_adjugate.continuousOn

theorem continuousOn_toGL : ContinuousOn (toGL : Matrix (Fin n) (Fin n) ℝ → GL (Fin n) ℝ) {M | M.det ≠ 0} := by
  rw [Units.isEmbedding_embedProduct.isInducing.continuousOn_iff]
  have : ∀ M ∈ {M : Matrix (Fin n) (Fin n) ℝ | M.det ≠ 0},
      (Units.embedProduct _ ∘ toGL) M = (M, MulOpposite.op M⁻¹) := by
    intro M hM
    simp only [Function.comp_apply, Units.embedProduct_apply, toGL_val hM, toGL_inv_val hM]
  refine ContinuousOn.congr ?_ this
  exact continuousOn_id.prodMk (MulOpposite.continuous_op.comp_continuousOn continuousOn_matrix_inv)

theorem det_conj_P (P : GL (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    ((P : Matrix (Fin n) (Fin n) ℝ) * M * ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)).det = M.det := by
  rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    det_one, one_mul]

/-! ### The inverse function theorem at $b = 1$: a local section -/

/-- **Upper triangular coordinates**: the matrix with $(i, j)$ entry $y_{ij}$ for $i \le j$ and $0$ below. -/
def utU (y : UIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if h : i ≤ j then y ⟨(i, j), h⟩ else 0

theorem isUT_utU (y : UIdx n → ℝ) : IsUT (utU y) := fun i j hij => by
  simp [utU, not_le.mpr hij]

theorem utU_add (y z : UIdx n → ℝ) : utU (y + z) = utU y + utU z := by
  ext i j; simp only [utU, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp

theorem utU_smul (r : ℝ) (y : UIdx n → ℝ) : utU (r • y) = r • utU y := by
  ext i j; simp only [utU, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem utU_apply_diag (y : UIdx n → ℝ) (i : Fin n) : utU y i i = y ⟨(i, i), le_rfl⟩ := by
  simp [utU]

theorem utU_injective : Function.Injective (utU : (UIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ) := by
  intro y z h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [utU, p.2] using this

/-- Entrywise smoothness of a matrix-valued map. -/
def CDMat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, ContDiff ℝ ⊤ fun y => F y i j

section CDMat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem CDMat.mul {F G : E → Matrix (Fin n) (Fin n) ℝ} (hF : CDMat F) (hG : CDMat G) : CDMat fun y => F y * G y :=
  fun i j => by
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun k _ => (hF i k).mul (hG k j)

theorem CDMat.add {F G : E → Matrix (Fin n) (Fin n) ℝ} (hF : CDMat F) (hG : CDMat G) : CDMat fun y => F y + G y :=
  fun i j => by simp only [Matrix.add_apply]; exact (hF i j).add (hG i j)

theorem CDMat.transpose {F : E → Matrix (Fin n) (Fin n) ℝ} (hF : CDMat F) : CDMat fun y => (F y)ᵀ :=
  fun i j => by simp only [transpose_apply]; exact hF j i

theorem CDMat.const (M : Matrix (Fin n) (Fin n) ℝ) : CDMat fun _ : E => M := fun _ _ => contDiff_const

end CDMat

theorem cdMat_utU : CDMat (utU : (UIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ) := fun i j => by
  by_cases h : i ≤ j
  · simp only [utU, dif_pos h]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : UIdx n => ℝ) ⟨(i, j), h⟩).contDiff
  · simp only [utU, h, dite_false]; exact contDiff_const

variable (Q : QuadForm ℝ n) (P : GL (Fin n) ℝ)

/-- **Coordinates on the slice group** near $1$: $y \mapsto P(1 + U(y))P^{-1}$. -/
def sliceCoord (y : UIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (P : Matrix (Fin n) (Fin n) ℝ) * (1 + utU y) * ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)

/-- $\psi(y) = \Phi_Q(P(1 + U(y))P^{-1})$. -/
def psi (y : UIdx n → ℝ) : UIdx n → ℝ := phi Q (sliceCoord P y)

theorem hPPi : (P : Matrix (Fin n) (Fin n) ℝ) * ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem hPiP : ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * (P : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- $E(y) = PU(y)P^{-1}$. -/
def sliceE (y : UIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (P : Matrix (Fin n) (Fin n) ℝ) * utU y * ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)

theorem sliceCoord_eq (y : UIdx n → ℝ) : sliceCoord P y = 1 + sliceE P y := by
  rw [sliceCoord, sliceE, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPPi]

theorem sliceE_smul (r : ℝ) (y : UIdx n → ℝ) : sliceE P (r • y) = r • sliceE P y := by
  rw [sliceE, sliceE, utU_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem sliceE_add (y z : UIdx n → ℝ) : sliceE P (y + z) = sliceE P y + sliceE P z := by
  rw [sliceE, sliceE, sliceE, utU_add, Matrix.mul_add, Matrix.add_mul]

/-- **The derivative of $\psi$ at $0$**: $y \mapsto$ the coefficients of $E^{\mathsf T}A + AE$. -/
def psiD : (UIdx n → ℝ) →ₗ[ℝ] (UIdx n → ℝ) where
  toFun y := wtU ((sliceE P y)ᵀ * gramMatrixR Q + gramMatrixR Q * sliceE P y)
  map_add' y z := by
    rw [sliceE_add, transpose_add, Matrix.add_mul, Matrix.mul_add, ← wtU_add]; congr 1; abel
  map_smul' r y := by
    rw [sliceE_smul, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, wtU_smul]; rfl

theorem psi_smul (r : ℝ) (y : UIdx n → ℝ) :
    psi Q P (r • y) = coeffU Q + r • psiD Q P y +
      r ^ 2 • wtU ((sliceE P y)ᵀ * gramMatrixR Q * sliceE P y) := by
  rw [psi, sliceCoord_eq, sliceE_smul, phi, ← phi_one Q, phi]
  change _ = _ + r • wtU _ + _
  rw [← wtU_smul, ← wtU_smul, ← wtU_add, ← wtU_add]
  congr 1
  simp only [transpose_add, transpose_one, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  module

theorem contDiff_psi : ContDiff ℝ ⊤ (psi Q P) := by
  have hc : CDMat (sliceCoord P) :=
    ((CDMat.const _).mul ((CDMat.const 1).add cdMat_utU)).mul (CDMat.const _)
  have h := (hc.transpose.mul (CDMat.const (gramMatrixR Q))).mul hc
  refine contDiff_pi.2 fun p => ?_
  simp only [psi, phi, wtU]
  exact contDiff_const.mul (h p.1.1 p.1.2)

theorem hasDerivAt_psi_line (y : UIdx n → ℝ) :
    HasDerivAt (fun r : ℝ => psi Q P (r • y)) (psiD Q P y) 0 := by
  simp_rw [psi_smul]
  have h1 : HasDerivAt (fun r : ℝ => r • psiD Q P y) ((1 : ℝ) • psiD Q P y) 0 :=
    (hasDerivAt_id 0).smul_const _
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2 • wtU ((sliceE P y)ᵀ * gramMatrixR Q * sliceE P y))
      (((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) • wtU ((sliceE P y)ᵀ * gramMatrixR Q * sliceE P y)) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).smul_const _
  have := (h1.const_add (coeffU Q)).add h2
  convert this using 1
  simp

theorem fderiv_psi_zero : (fderiv ℝ (psi Q P) 0 : (UIdx n → ℝ) →ₗ[ℝ] (UIdx n → ℝ)) = psiD Q P := by
  refine LinearMap.ext fun y => ?_
  have hd : HasFDerivAt (psi Q P) (fderiv ℝ (psi Q P) 0) 0 :=
    ((contDiff_psi Q P).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => r • y) y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const y
  have hd' : HasFDerivAt (psi Q P) (fderiv ℝ (psi Q P) 0) ((0 : ℝ) • y) := by rwa [zero_smul]
  have h1 : HasDerivAt (fun r : ℝ => psi Q P (r • y)) (fderiv ℝ (psi Q P) 0 y) 0 := by
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    simpa [Function.comp_def] using this
  exact h1.unique (hasDerivAt_psi_line Q P y)

/-- **The derivative at $0$ is injective**: $E^{\mathsf T}A + AE = 0$ forces $DU + (DU)^{\mathsf T} = 0$ with $DU$
upper triangular, so $U = 0$. -/
theorem psiD_injective {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0)
    (hP : (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * P = diagonal d) :
    Function.Injective (psiD Q P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set A := gramMatrixR Q
  set Pm := (P : Matrix (Fin n) (Fin n) ℝ)
  set Pi := ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  set E := sliceE P y
  have hPiP' : Pi * Pm = 1 := hPiP P
  have hsym : (Eᵀ * A + A * E)ᵀ = Eᵀ * A + A * E := by
    rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, gram_transpose, add_comm]
  have hy' : wtU (Eᵀ * A + A * E) = wtU 0 := by
    have : wtU (Eᵀ * A + A * E) = 0 := hy
    rw [this]; funext p; simp [wtU]
  have h0 : Eᵀ * A + A * E = 0 := wtU_inj hsym (by simp) hy'
  -- conjugate by P
  have hEP : E * Pm = Pm * utU y := by
    show Pm * utU y * Pi * Pm = Pm * utU y
    rw [Matrix.mul_assoc, hPiP', Matrix.mul_one]
  have hPE : Pmᵀ * Eᵀ = (utU y)ᵀ * Pmᵀ := by
    rw [← transpose_mul, hEP, transpose_mul]
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
      have : 2 * d i * utU y i i = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero (hd i))
    · exact isUT_utU y i j hij
  apply utU_injective
  ext i j
  rw [hY i j]; simp [utU]


theorem continuous_utU : Continuous (utU : (UIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_pi fun i => continuous_pi fun j => by
    by_cases h : i ≤ j
    · simp only [utU, dif_pos h]; exact continuous_apply _
    · simp only [utU, h, dite_false]; exact continuous_const

theorem continuous_sliceCoord : Continuous (sliceCoord P) :=
  (continuous_const.matrix_mul (continuous_const.add continuous_utU)).matrix_mul continuous_const

theorem det_one_add_utU {y : UIdx n → ℝ} (hy : ∀ i : Fin n, -1 < y ⟨(i, i), le_rfl⟩) :
    (sliceCoord P y).det ≠ 0 := by
  rw [sliceCoord, det_conj_P, det_of_isUpperTriangular]
  · refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, utU_apply_diag]
    linarith [hy i]
  · intro i j hij
    have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
    have h2 : utU y i j = 0 := isUT_utU y i j hij
    simp only [Matrix.add_apply, h1, h2, add_zero]

theorem conj_sliceCoord {y : UIdx n → ℝ} (hy : ∀ i : Fin n, -1 < y ⟨(i, i), le_rfl⟩) :
    P⁻¹ * toGL (sliceCoord P y) * P ∈ borelPos n := by
  have hval : ((P⁻¹ * toGL (sliceCoord P y) * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
      = 1 + utU y := by
    rw [Units.val_mul, Units.val_mul, toGL_val (det_one_add_utU P hy), sliceCoord]
    simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hPiP, Matrix.mul_one]
  refine ⟨?_, fun i => ?_⟩
  · rw [hval]; intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), isUT_utU _ i j hij, add_zero]
  · rw [hval, Matrix.add_apply, Matrix.one_apply_eq, utU_apply_diag]
    linarith [hy i]

theorem hasStrictFDerivAt_psi {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0)
    (hP : (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * P = diagonal d) :
    ∃ L : (UIdx n → ℝ) ≃L[ℝ] (UIdx n → ℝ), HasStrictFDerivAt (psi Q P) (L : (UIdx n → ℝ) →L[ℝ] (UIdx n → ℝ)) 0 := by
  refine ⟨(LinearEquiv.ofInjectiveEndo (psiD Q P) (psiD_injective Q P hd hP)).toContinuousLinearEquiv, ?_⟩
  have h := (contDiff_psi Q P).contDiffAt.hasStrictFDerivAt (x := 0) (by simp)
  convert h using 1
  ext1 y
  have := congrArg (fun f : (UIdx n → ℝ) →ₗ[ℝ] (UIdx n → ℝ) => f y) (fderiv_psi_zero Q P)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this]; rfl

/-- **A continuous local section of $\Phi_Q$ on the slice group** near $c_Q$: an open $T \ni c_Q$ and a map
$\sigma : T \to B$, continuous, with $\Phi_Q(\sigma(c)) = c$ and $\sigma(c_Q) = 1$ (inverse function theorem). -/
theorem exists_local_section {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0)
    (hP : (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * P = diagonal d) :
    ∃ T : Set (UIdx n → ℝ), IsOpen T ∧ coeffU Q ∈ T ∧ ∃ σ : (UIdx n → ℝ) → GL (Fin n) ℝ,
      ContinuousOn σ T ∧ σ (coeffU Q) = 1 ∧ ∀ c ∈ T, σ c ∈ sliceGroup P ∧ phi Q (σ c) = c := by
  obtain ⟨L, hstrict⟩ := hasStrictFDerivAt_psi Q P hd hP
  set e := hstrict.toOpenPartialHomeomorph (psi Q P)
  have he : ∀ y, e y = psi Q P y := fun y => by simp [e]
  have h0s : (0 : UIdx n → ℝ) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hutU0 : utU (0 : UIdx n → ℝ) = 0 := by ext i j; simp [utU]
  have hsc0 : sliceCoord P 0 = 1 := by rw [sliceCoord, hutU0, add_zero, Matrix.mul_one, hPPi]
  have hpsi0 : psi Q P 0 = coeffU Q := by rw [psi, hsc0, phi_one]
  set V : Set (UIdx n → ℝ) := {y | ∀ i : Fin n, -1 < y ⟨(i, i), le_rfl⟩}
  have hV : IsOpen V := by
    simp only [V, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply _)
  have h0V : (0 : UIdx n → ℝ) ∈ V := fun i => by simp
  have hcont : ContinuousOn (fun c => toGL (sliceCoord P (e.symm c))) (e.target ∩ e.symm ⁻¹' V) := by
    have h1 : ContinuousOn (fun c => sliceCoord P (e.symm c)) (e.target ∩ e.symm ⁻¹' V) :=
      (continuous_sliceCoord P).comp_continuousOn (e.continuousOn_symm.mono inter_subset_left)
    exact continuousOn_toGL.comp h1 fun c hc => det_one_add_utU P hc.2
  refine ⟨e.target ∩ e.symm ⁻¹' V, e.isOpen_inter_preimage_symm hV, ⟨?_, ?_⟩,
    fun c => toGL (sliceCoord P (e.symm c)), hcont, ?_, fun c hc => ⟨?_, ?_⟩⟩
  · rw [← hpsi0, ← he]; exact e.map_source h0s
  · rw [mem_preimage, ← hpsi0, ← he, e.left_inv h0s]; exact h0V
  · show toGL (sliceCoord P (e.symm (coeffU Q))) = 1
    rw [← hpsi0, ← he, e.left_inv h0s, hsc0]
    exact toGL_coe 1
  · rw [mem_sliceGroup]; exact conj_sliceCoord P hc.2
  · show phi Q (toGL (sliceCoord P (e.symm c))) = c
    rw [toGL_val (det_one_add_utU P hc.2), ← psi, ← he, e.right_inv hc.1]

/-! ### Topology of $\mathrm{GL}_n(\mathbb R)$, $SO(Q)(\mathbb R)$ and the slice group -/

local instance instLCMatrix : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
local instance instPolishMatrix : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
local instance instPolishMatrixOp : PolishSpace (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph).symm.isClosedEmbedding.polishSpace
local instance instLCGL : LocallyCompactSpace (GL (Fin n) ℝ) :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace
local instance instPolishGL : PolishSpace (GL (Fin n) ℝ) :=
  Units.isClosedEmbedding_embedProduct.polishSpace

theorem isClosed_soReal (Q : QuadForm ℝ n) : IsClosed ((soReal Q : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) := by
  have : ((soReal Q : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) =
      {g : GL (Fin n) ℝ | (g : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * g = Q.hessian} ∩
        {g : GL (Fin n) ℝ | (g : Matrix (Fin n) (Fin n) ℝ).det = 1} := by
    ext g; exact mem_soReal_iff Q g
  rw [this]
  exact (isClosed_eq ((Units.continuous_val.matrix_transpose.matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const).inter (isClosed_eq Units.continuous_val.matrix_det continuous_const)

namespace ArchSOInst
variable (Q : QuadForm ℝ n)

/-- $SO(Q)(\mathbb R)$ is locally compact for every real form (a closed subgroup of $\mathrm{GL}_n(\mathbb R)$). -/
instance : LocallyCompactSpace (ArchSO Q) :=
  show LocallyCompactSpace (soReal Q) from (isClosed_soReal Q).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : PolishSpace (ArchSO Q) :=
  show PolishSpace (soReal Q) from (isClosed_soReal Q).polishSpace

end ArchSOInst

theorem isClosed_borelPos : IsClosed ((borelPos n : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) := by
  have : ((borelPos n : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) =
      (⋂ i : Fin n, ⋂ j : Fin n, {b : GL (Fin n) ℝ | j < i → (b : Matrix (Fin n) (Fin n) ℝ) i j = 0}) ∩
        ⋂ i : Fin n, {b : GL (Fin n) ℝ | 0 ≤ (b : Matrix (Fin n) (Fin n) ℝ) i i} := by
    ext b
    simp only [SetLike.mem_coe, mem_inter_iff, mem_iInter, mem_setOf_eq]
    constructor
    · intro hb; exact ⟨fun i j hij => hb.1 i j hij, fun i => (hb.2 i).le⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun i j hij => h1 i j hij, fun i => lt_of_le_of_ne (h2 i) fun h0 => ?_⟩
      have hdet := (Matrix.isUnits_det_units b).ne_zero
      rw [det_of_isUpperTriangular (fun i j hij => h1 i j hij)] at hdet
      exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0.symm)
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun i => isClosed_le continuous_const ?_)
  · by_cases hij : j < i
    · simp only [hij, true_implies]
      exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [hij, false_implies, ofPred_true, isClosed_univ]
  · exact Units.continuous_val.matrix_elem i i

theorem isClosed_sliceGroup (P : GL (Fin n) ℝ) :
    IsClosed ((sliceGroup P : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) := by
  have : ((sliceGroup P : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) =
      (fun x => P⁻¹ * x * P) ⁻¹' ((borelPos n : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) := by
    ext x; exact mem_sliceGroup P x
  rw [this]
  exact isClosed_borelPos.preimage ((continuous_const.mul continuous_id).mul continuous_const)

/-- **The slice group as a type** with its Borel $\sigma$-algebra. -/
def SliceB (P : GL (Fin n) ℝ) : Type := sliceGroup P

namespace SliceB
variable (P : GL (Fin n) ℝ)
instance : Group (SliceB P) := inferInstanceAs (Group (sliceGroup P))
instance : TopologicalSpace (SliceB P) := inferInstanceAs (TopologicalSpace (sliceGroup P))
instance : IsTopologicalGroup (SliceB P) := inferInstanceAs (IsTopologicalGroup (sliceGroup P))
instance : T2Space (SliceB P) := inferInstanceAs (T2Space (sliceGroup P))
instance : LocallyCompactSpace (SliceB P) :=
  show LocallyCompactSpace (sliceGroup P) from
    (isClosed_sliceGroup P).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance : PolishSpace (SliceB P) := show PolishSpace (sliceGroup P) from (isClosed_sliceGroup P).polishSpace
instance : SecondCountableTopology (SliceB P) := inferInstance
instance : MeasurableSpace (SliceB P) := borel _
instance : BorelSpace (SliceB P) := ⟨rfl⟩

/-- The inclusion into $\mathrm{GL}_n(\mathbb R)$. -/
def incl : SliceB P →* GL (Fin n) ℝ := (sliceGroup P).subtype

theorem continuous_incl : Continuous (incl P) := continuous_subtype_val

theorem incl_mem (x : SliceB P) : incl P x ∈ sliceGroup P := (show sliceGroup P from x).2

/-- An element of the slice group as an element of `SliceB P`. -/
def mk (x : GL (Fin n) ℝ) (h : x ∈ sliceGroup P) : SliceB P := (⟨x, h⟩ : sliceGroup P)

theorem incl_mk (x : GL (Fin n) ℝ) (h : x ∈ sliceGroup P) : incl P (mk P x h) = x := rfl

/-- The underlying matrix. -/
def mat (x : SliceB P) : Matrix (Fin n) (Fin n) ℝ := (incl P x : GL (Fin n) ℝ)

theorem continuous_mat : Continuous (mat P) := Units.continuous_val.comp (continuous_incl P)

theorem mat_mul (x y : SliceB P) : mat P (x * y) = mat P x * mat P y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat P 1 = 1 := by simp only [mat, map_one, Units.val_one]

theorem mat_inv_mul (x : SliceB P) : mat P x⁻¹ * mat P x = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (x : SliceB P) : mat P x * mat P x⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

end SliceB

namespace ArchSOInst
variable (Q : QuadForm ℝ n)

/-- The underlying matrix of $g \in SO(Q)(\mathbb R)$. -/
def mat (g : ArchSO Q) : Matrix (Fin n) (Fin n) ℝ := (ArchSO.incl Q g : GL (Fin n) ℝ)

theorem continuous_mat : Continuous (mat Q) := Units.continuous_val.comp (ArchSO.continuous_incl Q)

theorem mat_mul (g h : ArchSO Q) : mat Q (g * h) = mat Q g * mat Q h := by
  simp only [mat, map_mul, Units.val_mul]

theorem incl_mem (g : ArchSO Q) : ArchSO.incl Q g ∈ soReal Q := (show soReal Q from g).2

theorem isometry (g : ArchSO Q) : (mat Q g)ᵀ * gramMatrixR Q * mat Q g = gramMatrixR Q := by
  have h := ((mem_soReal_iff Q _).mp (incl_mem Q g)).1
  rw [gramMatrixR, Matrix.mul_smul, Matrix.smul_mul, mat, h]

theorem det_mat (g : ArchSO Q) : (mat Q g).det = 1 := ((mem_soReal_iff Q _).mp (incl_mem Q g)).2

/-- An element of `soReal Q` as an element of `ArchSO Q`. -/
def mk (g : GL (Fin n) ℝ) (h : g ∈ soReal Q) : ArchSO Q := (⟨g, h⟩ : soReal Q)

theorem mat_mk (g : GL (Fin n) ℝ) (h : g ∈ soReal Q) : mat Q (mk Q g h) = g := rfl

end ArchSOInst

/-! ### Linear changes of variables on $M_n(\mathbb R)$ in column coordinates -/

/-- Left multiplication $X \mapsto MX$ in column coordinates. -/
def lmulL (M : Matrix (Fin n) (Fin n) ℝ) : (Fin n → Fin n → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℝ) :=
  LinearMap.pi fun j => (Matrix.toLin' M).comp (LinearMap.proj j)

theorem det_lmulL (M : Matrix (Fin n) (Fin n) ℝ) : LinearMap.det (lmulL M) = M.det ^ n := by
  rw [lmulL, LinearMap.det_pi, LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Transposition of the two indices. -/
def swapL : (Fin n → Fin n → ℝ) ≃ₗ[ℝ] (Fin n → Fin n → ℝ) where
  toFun X i j := X j i
  invFun X i j := X j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Right multiplication $X \mapsto XM$ in column coordinates. -/
def rmulL (M : Matrix (Fin n) (Fin n) ℝ) : (Fin n → Fin n → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℝ) :=
  (swapL (n := n)).toLinearMap ∘ₗ lmulL Mᵀ ∘ₗ (swapL (n := n)).symm.toLinearMap

theorem det_rmulL (M : Matrix (Fin n) (Fin n) ℝ) : LinearMap.det (rmulL M) = M.det ^ n := by
  rw [rmulL, LinearMap.det_conj, det_lmulL, det_transpose]

theorem cols_mul_left (M N : Matrix (Fin n) (Fin n) ℝ) : cols (M * N) = lmulL M (cols N) := by
  funext j i
  simp [cols, lmulL, Matrix.mul_apply, mulVec, dotProduct]

theorem cols_mul_right (N M : Matrix (Fin n) (Fin n) ℝ) : cols (N * M) = rmulL M (cols N) := by
  funext j i
  simp [cols, rmulL, lmulL, swapL, Matrix.mul_apply, mulVec, dotProduct, mul_comm]

theorem volume_image_cols_mul_left (M : Matrix (Fin n) (Fin n) ℝ) (S : Set (Matrix (Fin n) (Fin n) ℝ)) :
    volume (cols '' ((M * ·) '' S)) = ENNReal.ofReal (|M.det| ^ n) * volume (cols '' S) := by
  have : cols '' ((M * ·) '' S) = lmulL M '' (cols '' S) := by
    rw [image_image, image_image]; simp_rw [cols_mul_left]
  rw [this, addHaar_image_linearMap, det_lmulL, abs_pow]

theorem volume_image_cols_mul_right (M : Matrix (Fin n) (Fin n) ℝ) (S : Set (Matrix (Fin n) (Fin n) ℝ)) :
    volume (cols '' ((· * M) '' S)) = ENNReal.ofReal (|M.det| ^ n) * volume (cols '' S) := by
  have : cols '' ((· * M) '' S) = rmulL M '' (cols '' S) := by
    rw [image_image, image_image]; simp_rw [cols_mul_right]
  rw [this, addHaar_image_linearMap, det_rmulL, abs_pow]

/-! ### The slice data, the chart and the measures -/

/-- **Diagonalization data** for $Q$: $P \in \mathrm{GL}_n(\mathbb R)$ with $P^{\mathsf T}AP = \mathrm{diag}(d)$, all
$d_i \ne 0$. Any choice gives the same Leray measure (`leray_unique`). -/
structure Diag (Q : QuadForm ℝ n) where
  /-- the change of basis -/
  P : GL (Fin n) ℝ
  /-- the diagonal entries -/
  d : Fin n → ℝ
  hd : ∀ i, d i ≠ 0
  hP : (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * P = diagonal d

/-- The diagonalization given by the spectral theorem. -/
def Diag.ofSpectral (Q : QuadForm ℝ n) (hQ : gramDetR Q ≠ 0) : Diag Q :=
  ⟨(exists_diag Q hQ).choose, (exists_diag Q hQ).choose_spec.choose,
    (exists_diag Q hQ).choose_spec.choose_spec.1, (exists_diag Q hQ).choose_spec.choose_spec.2⟩

variable {Q : QuadForm ℝ n} (D : Diag Q)


theorem Diag.det_gram_ne_zero {Q : QuadForm ℝ n} (D : Diag Q) : (gramMatrixR Q).det ≠ 0 := by
  have h := congrArg Matrix.det D.hP
  rw [det_mul, det_mul, det_transpose, det_diagonal] at h
  intro h0
  rw [h0, mul_zero, zero_mul] at h
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => D.hd i) h.symm

/-- **The orbit map** $\beta : B \to \mathbb R^{n(n+1)/2}$, $b \mapsto \Phi_Q(b)$. -/
def beta (x : SliceB D.P) : UIdx n → ℝ := phi Q (SliceB.mat D.P x)

theorem continuous_beta : Continuous (beta D) := (continuous_phi Q).comp (SliceB.continuous_mat D.P)

theorem beta_mul (x y : SliceB D.P) : beta D (x * y) = act (SliceB.mat D.P y) (beta D x) := by
  rw [beta, beta, SliceB.mat_mul, phi_mul]

theorem beta_one : beta D 1 = coeffU Q := by rw [beta, SliceB.mat_one, phi_one]

theorem beta_injective : Function.Injective (beta D) := by
  intro x y h
  have := phi_injOn_slice Q D.hd D.hP (SliceB.incl_mem D.P x) (SliceB.incl_mem D.P y) h
  exact Subtype.ext this

theorem act_mat_inv (x : SliceB D.P) (c : UIdx n → ℝ) : act (SliceB.mat D.P x⁻¹) (act (SliceB.mat D.P x) c) = c := by
  rw [← act_mul, SliceB.mat_mul_inv, act_one]

theorem act_mat_inv' (x : SliceB D.P) (c : UIdx n → ℝ) : act (SliceB.mat D.P x) (act (SliceB.mat D.P x⁻¹) c) = c := by
  rw [← act_mul, SliceB.mat_inv_mul, act_one]

theorem continuous_act (M : Matrix (Fin n) (Fin n) ℝ) : Continuous (act M) :=
  LinearMap.continuous_of_finiteDimensional _

/-- The local section, as a map into the slice group. -/
theorem exists_local_section' :
    ∃ T : Set (UIdx n → ℝ), IsOpen T ∧ coeffU Q ∈ T ∧ ∃ σ : (UIdx n → ℝ) → SliceB D.P,
      ContinuousOn σ T ∧ σ (coeffU Q) = 1 ∧ ∀ c ∈ T, beta D (σ c) = c := by
  classical
  obtain ⟨T, hT, hcT, σ, hσc, hσ1, hσ⟩ := exists_local_section Q D.P D.hd D.hP
  let σ' : (UIdx n → ℝ) → SliceB D.P := fun c =>
    if h : σ c ∈ sliceGroup D.P then SliceB.mk D.P (σ c) h else 1
  have hval : ∀ c ∈ T, SliceB.incl D.P (σ' c) = σ c := fun c hc => by
    rw [show σ' c = SliceB.mk D.P (σ c) (hσ c hc).1 from dif_pos (hσ c hc).1, SliceB.incl_mk]
  refine ⟨T, hT, hcT, σ', ?_, ?_, fun c hc => ?_⟩
  · have hemb : Topology.IsInducing (SliceB.incl D.P) := Topology.IsInducing.subtypeVal
    rw [hemb.continuousOn_iff]
    exact hσc.congr fun c hc => hval c hc
  · apply Subtype.ext
    exact (hval _ hcT).trans hσ1
  · rw [beta, SliceB.mat, hval c hc]; exact (hσ c hc).2

/-- **$\beta$ is an open map** (equivariance spreads the local section). -/
theorem isOpenMap_beta : IsOpenMap (beta D) := by
  obtain ⟨T, hT, hcT, σ, hσc, hσ1, hσ⟩ := exists_local_section' D
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x₀, hx₀, rfl⟩
  -- the map c ↦ σ(c · x₀⁻¹) x₀ is continuous at β(x₀), with value x₀
  set F : (UIdx n → ℝ) → SliceB D.P := fun c => σ (act (SliceB.mat D.P x₀⁻¹) c) * x₀
  have hc0 : act (SliceB.mat D.P x₀⁻¹) (beta D x₀) = coeffU Q := by
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

theorem isOpenEmbedding_beta : Topology.IsOpenEmbedding (beta D) :=
  .of_continuous_injective_isOpenMap (continuous_beta D) (beta_injective D) (isOpenMap_beta D)

theorem det_mat_pos (x : SliceB D.P) : 0 < (SliceB.mat D.P x).det := by
  have h := (mem_sliceGroup D.P _).mp (SliceB.incl_mem D.P x)
  have h1 : ((D.P⁻¹ * SliceB.incl D.P x * D.P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ).det = (SliceB.mat D.P x).det := by
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one, one_mul]; rfl
  rw [← h1, det_of_isUpperTriangular (fun i j hij => h.1 i j hij)]
  exact Finset.prod_pos fun i _ => h.2 i

/-- **The chart** $m(g, b) = gb$ in column coordinates. -/
def chart (p : ArchSO Q × SliceB D.P) : Fin n → Fin n → ℝ := cols (ArchSOInst.mat Q p.1 * SliceB.mat D.P p.2)

theorem continuous_cols : Continuous (cols : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n → ℝ) :=
  continuous_pi fun j => continuous_pi fun i => (continuous_apply j).comp (continuous_apply i)

theorem continuous_chart : Continuous (chart D) :=
  continuous_cols.comp (((ArchSOInst.continuous_mat Q).comp continuous_fst).matrix_mul
    ((SliceB.continuous_mat D.P).comp continuous_snd))

theorem cols_injective : Function.Injective (cols : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n → ℝ) := by
  intro M N h; ext i j; exact congrFun (congrFun h j) i

theorem phi_chart (p : ArchSO Q × SliceB D.P) :
    phi Q (ArchSOInst.mat Q p.1 * SliceB.mat D.P p.2) = beta D p.2 := by
  rw [beta, phi_of_isometry Q (ArchSOInst.isometry Q p.1)]

theorem chart_injective : Function.Injective (chart D) := by
  rintro ⟨g, x⟩ ⟨g', x'⟩ h
  have hM := cols_injective h
  have hx : x = x' := beta_injective D (by
    rw [← phi_chart D (g, x), ← phi_chart D (g', x')]; exact congrArg (phi Q) hM)
  subst hx
  refine Prod.ext ?_ rfl
  have hg : ArchSOInst.mat Q g = ArchSOInst.mat Q g' := by
    have := congrArg (· * SliceB.mat D.P x⁻¹) hM
    simpa only [Matrix.mul_assoc, SliceB.mat_mul_inv, Matrix.mul_one] using this
  apply Subtype.ext
  exact Units.ext hg

theorem measurableEmbedding_chart : MeasurableEmbedding (chart D) :=
  (continuous_chart D).measurableEmbedding (chart_injective D)

/-- The matrix with column coordinates $X$. -/
def ofCols (X : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => X j i

theorem cols_ofCols (X : Fin n → Fin n → ℝ) : cols (ofCols X) = X := rfl

theorem det_ofCols (X : Fin n → Fin n → ℝ) : (ofCols X).det = (Matrix.of X).det := by
  rw [← det_transpose]; rfl

/-- **The image of the chart**: for $E \subseteq U = \beta(B)$,
$m(SO(Q) \times \beta^{-1}E) = \{X : \det X > 0,\ \Phi_Q(X) \in E\}$. -/
theorem image_chart {E : Set (UIdx n → ℝ)} (hE : E ⊆ range (beta D)) :
    chart D '' (univ ×ˢ (beta D ⁻¹' E)) =
      {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ E} := by
  ext X
  constructor
  · rintro ⟨⟨g, x⟩, ⟨-, hx⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← det_ofCols]
      change 0 < (ArchSOInst.mat Q g * SliceB.mat D.P x).det
      rw [det_mul, ArchSOInst.det_mat, one_mul]; exact det_mat_pos D x
    · rw [chart, ← phi_eq_pullCoeff, phi_chart]; exact hx
  · rintro ⟨hdet, hX⟩
    set M := ofCols X
    have hMdet : 0 < M.det := by rw [det_ofCols]; exact hdet
    have hphiM : phi Q M ∈ E := by rw [phi_eq_pullCoeff, cols_ofCols]; exact hX
    obtain ⟨x, hx⟩ := hE hphiM
    set N := M * SliceB.mat D.P x⁻¹
    have hNphi : phi Q N = coeffU Q := by
      rw [phi_mul, ← hx, ← beta_mul, mul_inv_cancel, beta_one]
    have hNiso : Nᵀ * gramMatrixR Q * N = gramMatrixR Q := by
      have := (phi_eq_iff Q N 1).mp (by rw [hNphi, phi_one])
      rwa [transpose_one, Matrix.one_mul, Matrix.mul_one] at this
    have hNdet : N.det = 1 := by
      have hA := D.det_gram_ne_zero
      have h1 := congrArg Matrix.det hNiso
      rw [det_mul, det_mul, det_transpose] at h1
      have h2 : N.det * N.det = 1 := by
        have : (N.det * N.det - 1) * (gramMatrixR Q).det = 0 := by linear_combination h1
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hA)
      have hpos : 0 < N.det := by
        rw [det_mul]
        have h3 := det_mat_pos D x⁻¹
        positivity
      nlinarith
    have hNunit : N.det ≠ 0 := by rw [hNdet]; exact one_ne_zero
    have hmem : toGL N ∈ soReal Q := by
      rw [mem_soReal_iff, toGL_val hNunit]
      refine ⟨?_, hNdet⟩
      have : Q.hessian = (2 : ℝ) • gramMatrixR Q := by
        rw [gramMatrixR, smul_smul]; norm_num
      rw [this, Matrix.mul_smul, Matrix.smul_mul, hNiso]
    refine ⟨(ArchSOInst.mk Q (toGL N) hmem, x), ⟨mem_univ _, ?_⟩, ?_⟩
    · show beta D x ∈ E
      rw [hx]; exact hphiM
    · show cols (ArchSOInst.mat Q (ArchSOInst.mk Q (toGL N) hmem) * SliceB.mat D.P x) = X
      rw [ArchSOInst.mat_mk, toGL_val hNunit]
      simp only [N, Matrix.mul_assoc, SliceB.mat_inv_mul, Matrix.mul_one]
      rfl

/-! ### Characters, the comparison measure, and the fibration theorem -/

/-- $\chi(b) = |\det b|^n$: the factor by which $X \mapsto Xb$ scales $dX$. -/
def chiB : SliceB D.P →* ℝ≥0 where
  toFun x := ‖(SliceB.mat D.P x).det‖₊ ^ n
  map_one' := by simp [SliceB.mat_one]
  map_mul' x y := by simp only [SliceB.mat_mul, det_mul, nnnorm_mul, mul_pow]

theorem act_one_eq : act (1 : Matrix (Fin n) (Fin n) ℝ) = LinearMap.id := LinearMap.ext act_one

theorem act_mul_eq (M N : Matrix (Fin n) (Fin n) ℝ) : act (M * N) = (act N).comp (act M) :=
  LinearMap.ext fun c => act_mul M N c

/-- $J(b) = |\det(c \mapsto c\cdot b)|$: the factor by which the action of $b$ scales $dc$. -/
def JB : SliceB D.P →* ℝ≥0 where
  toFun x := ‖LinearMap.det (act (SliceB.mat D.P x))‖₊
  map_one' := by rw [SliceB.mat_one, act_one_eq, LinearMap.det_id, nnnorm_one]
  map_mul' x y := by rw [SliceB.mat_mul, act_mul_eq, LinearMap.det_comp, nnnorm_mul, mul_comm]

/-- $\theta = \chi/J$. -/
def thetaB : SliceB D.P →* ℝ≥0 where
  toFun x := chiB D x * (JB D x)⁻¹
  map_one' := by simp
  map_mul' x y := by rw [map_mul, map_mul, mul_inv]; ring

theorem JB_mul_thetaB : JB D * thetaB D = chiB D := by
  ext x
  simp only [MonoidHom.mul_apply, thetaB, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ (Leray.char_ne_zero (JB D) x), mul_one]

theorem continuous_det_act : Continuous fun M : Matrix (Fin n) (Fin n) ℝ => LinearMap.det (act M) := by
  have : (fun M : Matrix (Fin n) (Fin n) ℝ => LinearMap.det (act M)) =
      fun M => (LinearMap.toMatrix' (act M)).det := by
    funext M; rw [LinearMap.det_toMatrix']
  rw [this]
  refine Continuous.matrix_det (continuous_pi fun p => continuous_pi fun q => ?_)
  simp only [LinearMap.toMatrix'_apply, act_apply, wtU]
  exact continuous_const.mul
    (((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).matrix_elem _ _)

theorem continuous_chiB : Continuous (chiB D) :=
  (continuous_nnnorm.comp (SliceB.continuous_mat D.P).matrix_det).pow n

theorem continuous_JB : Continuous (JB D) :=
  continuous_nnnorm.comp (continuous_det_act.comp (SliceB.continuous_mat D.P))

theorem continuous_thetaB : Continuous (thetaB D) :=
  (continuous_chiB D).mul ((continuous_JB D).inv₀ fun x => Leray.char_ne_zero (JB D) x)

theorem measurableEmbedding_beta : MeasurableEmbedding (beta D) :=
  (continuous_beta D).measurableEmbedding (beta_injective D)

theorem ofReal_abs_eq (r : ℝ) : ENNReal.ofReal |r| = ((‖r‖₊ : ℝ≥0) : ℝ≥0∞) := by
  rw [← Real.enorm_eq_ofReal_abs, enorm_eq_nnnorm]

theorem image_preimage_mul_right (b : SliceB D.P) (E : Set (SliceB D.P)) :
    beta D '' ((· * b) ⁻¹' E) = act (SliceB.mat D.P b⁻¹) '' (beta D '' E) := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨beta D (x * b), ⟨x * b, hx, rfl⟩, by rw [← beta_mul, mul_inv_cancel_right]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y * b⁻¹, by simpa using hy, by rw [beta_mul]⟩

/-- $\kappa_1 = \beta^*(dc)$, the pull-back of Lebesgue measure on coefficient space. -/
def kappa1 : Measure (SliceB D.P) := Measure.comap (beta D) volume

theorem kappa1_apply {E : Set (SliceB D.P)} (hE : MeasurableSet E) : kappa1 D E = volume (beta D '' E) :=
  (measurableEmbedding_beta D).comap_apply volume E |>.trans rfl

instance : IsFiniteMeasureOnCompacts (kappa1 D) := ⟨fun C hC => by
  rw [kappa1_apply D hC.measurableSet]
  exact (hC.image (continuous_beta D)).measure_lt_top⟩

instance : IsOpenPosMeasure (kappa1 D) := ⟨fun O hO hne => by
  rw [kappa1_apply D hO.measurableSet]
  exact (isOpenMap_beta D O hO).measure_ne_zero volume (hne.image _)⟩

theorem kappa1_rel : Leray.IsRelRightInvariant (JB D) (kappa1 D) := by
  intro b
  ext E hE
  rw [map_apply (measurable_mul_const b) hE, kappa1_apply D (measurable_mul_const b hE), Measure.smul_apply,
    kappa1_apply D hE, image_preimage_mul_right, addHaar_image_linearMap, ofReal_abs_eq, smul_eq_mul]
  congr 2
  change JB D b⁻¹ = (JB D b)⁻¹
  rw [map_inv]

/-- **The comparison measure** $\kappa_0 = \theta\,\kappa_1$ on $B$: $\chi$-relatively right-invariant, and its image
in coefficient space has density $\theta \circ \beta^{-1}$ (continuous, $= 1$ at $c_Q$). -/
def kappa0 : Measure (SliceB D.P) := (kappa1 D).withDensity fun x => (thetaB D x : ℝ≥0∞)

instance : IsFiniteMeasureOnCompacts (kappa0 D) :=
  Leray.withDensity_char_isFiniteMeasureOnCompacts (thetaB D) (continuous_thetaB D)

instance : IsOpenPosMeasure (kappa0 D) :=
  Leray.withDensity_char_isOpenPosMeasure (thetaB D) (continuous_thetaB D)

theorem kappa0_rel : Leray.IsRelRightInvariant (chiB D) (kappa0 D) := by
  have h := Leray.isRelRightInvariant_withDensity (JB D) (thetaB D) (continuous_thetaB D) (kappa1_rel D)
  rwa [JB_mul_thetaB] at h

/-- $\tau = m^*(dX)$. -/
def tauM : Measure (ArchSO Q × SliceB D.P) := Measure.comap (chart D) volume

theorem tauM_apply {E : Set (ArchSO Q × SliceB D.P)} (hE : MeasurableSet E) :
    tauM D E = volume (chart D '' E) :=
  (measurableEmbedding_chart D).comap_apply volume E |>.trans rfl

instance : IsFiniteMeasureOnCompacts (tauM D) := ⟨fun C hC => by
  rw [tauM_apply D hC.measurableSet]
  exact (hC.image (continuous_chart D)).measure_lt_top⟩

theorem chart_mul_left (g : ArchSO Q) (p : ArchSO Q × SliceB D.P) :
    chart D (g * p.1, p.2) = lmulL (ArchSOInst.mat Q g) (chart D p) := by
  rw [chart, chart, ArchSOInst.mat_mul, Matrix.mul_assoc, cols_mul_left]

theorem chart_mul_right (b : SliceB D.P) (p : ArchSO Q × SliceB D.P) :
    chart D (p.1, p.2 * b) = rmulL (SliceB.mat D.P b) (chart D p) := by
  rw [chart, chart, SliceB.mat_mul, ← Matrix.mul_assoc, cols_mul_right]

theorem tauM_left (g : ArchSO Q) : (tauM D).map (fun p : ArchSO Q × SliceB D.P => (g * p.1, p.2)) = tauM D := by
  have hm : Measurable fun p : ArchSO Q × SliceB D.P => (g * p.1, p.2) :=
    (measurable_const_mul g |>.comp measurable_fst).prodMk measurable_snd
  ext E hE
  rw [map_apply hm hE, tauM_apply D (hm hE), tauM_apply D hE]
  have himg : chart D '' ((fun p : ArchSO Q × SliceB D.P => (g * p.1, p.2)) ⁻¹' E) =
      lmulL (ArchSOInst.mat Q g⁻¹) '' (chart D '' E) := by
    ext X
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨_, ⟨_, hp, rfl⟩, ?_⟩
      rw [← chart_mul_left]; simp
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨(g⁻¹ * q.1, q.2), by simpa using hq, by rw [chart_mul_left]⟩
  rw [himg, addHaar_image_linearMap, det_lmulL, ArchSOInst.det_mat, one_pow, abs_one, ENNReal.ofReal_one,
    one_mul]

theorem tauM_right (b : SliceB D.P) :
    (tauM D).map (fun p : ArchSO Q × SliceB D.P => (p.1, p.2 * b)) = (((chiB D b)⁻¹ : ℝ≥0) : ℝ≥0∞) • tauM D := by
  have hm : Measurable fun p : ArchSO Q × SliceB D.P => (p.1, p.2 * b) :=
    measurable_fst.prodMk ((measurable_mul_const b).comp measurable_snd)
  ext E hE
  rw [map_apply hm hE, tauM_apply D (hm hE), Measure.smul_apply, tauM_apply D hE]
  have himg : chart D '' ((fun p : ArchSO Q × SliceB D.P => (p.1, p.2 * b)) ⁻¹' E) =
      rmulL (SliceB.mat D.P b⁻¹) '' (chart D '' E) := by
    ext X
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨_, ⟨_, hp, rfl⟩, ?_⟩
      rw [← chart_mul_right]; simp
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨(q.1, q.2 * b⁻¹), by simpa using hq, by rw [chart_mul_right]⟩
  rw [himg, addHaar_image_linearMap, det_rmulL, abs_pow, smul_eq_mul]
  congr 1
  rw [← map_inv, ← abs_pow, ofReal_abs_eq]
  simp [chiB]

/-- A fixed compact set with nonempty interior in $SO(Q)(\mathbb R)$ (the Haar normalization is irrelevant: the Leray
constant absorbs it). -/
def K₀ (Q : QuadForm ℝ n) : PositiveCompacts (ArchSO Q) := Classical.arbitrary _

theorem exists_fibration : ∃ c : ℝ≥0, tauM D = ((c : ℝ≥0∞) • haarMeasure (K₀ Q)).prod (kappa0 D) :=
  Leray.slice_decomposition (K₀ Q) (chiB D) (continuous_chiB D) (tauM D) (tauM_left D) (tauM_right D)
    (kappa0 D) (kappa0_rel D)

/-- The Leray constant for the slice data $D$. -/
def lerayC : ℝ≥0 := (exists_fibration D).choose

/-- **The Leray measure** on $SO(Q)(\mathbb R)$ built from the slice data $D$ (`leray_unique`: it does not depend on
$D$). -/
def lerayD : Measure (ArchSO Q) := ((lerayC D : ℝ≥0) : ℝ≥0∞) • haarMeasure (K₀ Q)

/-- **The fibration theorem** (the defining property of the gauge-form measure): the pull-back of $dX$ along
$(g, b) \mapsto gb$ is $\mu_Q \otimes \kappa_0$. -/
theorem lerayFibration : Measure.comap (chart D) volume = (lerayD D).prod (kappa0 D) :=
  (exists_fibration D).choose_spec

/-! ### The density of $\kappa_0$ in coefficient space, the Haar property -/

instance : Nonempty (SliceB D.P) := ⟨1⟩

/-- The inverse $\beta^{-1} : U \to B$ of the orbit map (a homeomorphism onto the open set $U = \beta(B)$). -/
def sec : (UIdx n → ℝ) → SliceB D.P := ((isOpenEmbedding_beta D).toOpenPartialHomeomorph (beta D)).symm

theorem sec_beta (x : SliceB D.P) : sec D (beta D x) = x :=
  (isOpenEmbedding_beta D).toOpenPartialHomeomorph_left_inv (beta D)

theorem beta_sec {c : UIdx n → ℝ} (hc : c ∈ range (beta D)) : beta D (sec D c) = c :=
  (isOpenEmbedding_beta D).toOpenPartialHomeomorph_right_inv (beta D) hc

theorem continuousOn_sec : ContinuousOn (sec D) (range (beta D)) := by
  have h := ((isOpenEmbedding_beta D).toOpenPartialHomeomorph (beta D)).continuousOn_symm
  rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at h

theorem isOpen_range_beta : IsOpen (range (beta D)) := (isOpenEmbedding_beta D).isOpen_range

theorem coeffU_mem_range : coeffU Q ∈ range (beta D) := ⟨1, beta_one D⟩

theorem sec_coeffU : sec D (coeffU Q) = 1 := by rw [← beta_one D, sec_beta]

/-- **The Leray density** $\rho = \theta \circ \beta^{-1}$ on $U$: $\beta_*\kappa_0 = \rho\,dc$ on $U$. -/
def rho (c : UIdx n → ℝ) : ℝ := (thetaB D (sec D c) : ℝ)

theorem rho_coeffU : rho D (coeffU Q) = 1 := by simp [rho, sec_coeffU]

theorem rho_nonneg (c : UIdx n → ℝ) : 0 ≤ rho D c := NNReal.coe_nonneg _

theorem continuousOn_rho : ContinuousOn (rho D) (range (beta D)) :=
  (NNReal.continuous_coe.comp (continuous_thetaB D)).comp_continuousOn (continuousOn_sec D)

/-- **$\kappa_0$ in coefficient space**: $\kappa_0(\beta^{-1}E) = \int_{E \cap U}\rho\,dc$. -/
theorem kappa0_preimage {E : Set (UIdx n → ℝ)} (hE : MeasurableSet E) :
    kappa0 D (beta D ⁻¹' E) = ∫⁻ c in E ∩ range (beta D), ENNReal.ofReal (rho D c) := by
  have hmE : MeasurableSet (beta D ⁻¹' E) := (continuous_beta D).measurable hE
  rw [kappa0, withDensity_apply _ hmE, ← lintegral_indicator hmE]
  set G : (UIdx n → ℝ) → ℝ≥0∞ := E.indicator fun c => ENNReal.ofReal (rho D c)
  have hG : (beta D ⁻¹' E).indicator (fun x => (thetaB D x : ℝ≥0∞)) = G ∘ beta D := by
    funext x
    by_cases hx : beta D x ∈ E
    · simp [G, indicator, hx, rho, sec_beta]
    · simp [G, indicator, hx]
  rw [hG, kappa1]
  change ∫⁻ a, G (beta D a) ∂(Measure.comap (beta D) volume) = _
  rw [← (measurableEmbedding_beta D).lintegral_map, (measurableEmbedding_beta D).map_comap,
    lintegral_indicator hE, Measure.restrict_restrict hE]

instance : IsFiniteMeasureOnCompacts (lerayD D) := ⟨fun K hK => by
  rw [lerayD, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hK.measure_lt_top⟩

instance : (lerayD D).IsMulLeftInvariant := by
  unfold lerayD; infer_instance

theorem tauM_univ_ne_zero : tauM D univ ≠ 0 := by
  rw [tauM_apply D MeasurableSet.univ]
  have hsub : chart D '' (univ ×ˢ (beta D ⁻¹' range (beta D))) ⊆ chart D '' univ :=
    image_mono (subset_univ _)
  refine fun h0 => ?_
  have h1 := measure_mono_null hsub h0
  rw [image_chart D subset_rfl] at h1
  have hopen : IsOpen {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ range (beta D)} := by
    have hdc : Continuous fun X : Fin n → Fin n → ℝ => (Matrix.of X).det := by
      have : (fun X : Fin n → Fin n → ℝ => (Matrix.of X).det) = fun X => (ofCols X).det :=
        funext fun X => (det_ofCols X).symm
      rw [this]
      exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j))
    exact (isOpen_lt continuous_const hdc).inter ((isOpen_range_beta D).preimage (continuous_pullCoeff Q))
  have hne : (cols (1 : Matrix (Fin n) (Fin n) ℝ)) ∈
      {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ range (beta D)} := by
    refine ⟨?_, ?_⟩
    · rw [← det_ofCols, show ofCols (cols (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 from rfl, det_one]
      exact one_pos
    · rw [← phi_eq_pullCoeff, phi_one]; exact coeffU_mem_range D
  exact hopen.measure_ne_zero volume ⟨_, hne⟩ h1

theorem lerayC_ne_zero : lerayC D ≠ 0 := by
  intro h0
  have h := lerayFibration D
  rw [lerayD, h0, ENNReal.coe_zero, zero_smul, Measure.zero_prod] at h
  exact tauM_univ_ne_zero D (by rw [tauM, h]; rfl)

/-- **The Leray measure is a left Haar measure on $SO(Q)(\mathbb R)$** (any signature). -/
instance isHaarMeasure_lerayD : (lerayD D).IsHaarMeasure :=
  IsHaarMeasure.smul _ (by simpa using lerayC_ne_zero D) ENNReal.coe_ne_top

/-! ### Total mass in the definite case; agreement with `ArchSO.mu` -/

/-- For $\varepsilon$ small, $\{X : \det X > 0,\ \Phi_Q(X) \in B_\varepsilon(c_Q)\}$ has volume
$\mu_Q(G)\cdot\kappa_0(\beta^{-1}B_\varepsilon)$. -/
theorem volume_tube {E : Set (UIdx n → ℝ)} (hE : MeasurableSet E) (hEU : E ⊆ range (beta D)) :
    volume {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ E} =
      lerayD D univ * ∫⁻ c in E, ENNReal.ofReal (rho D c) := by
  rw [← image_chart D hEU, ← tauM_apply D (MeasurableSet.univ.prod ((continuous_beta D).measurable hE)), tauM,
    lerayFibration, Measure.prod_prod, kappa0_preimage D hE, inter_eq_left.mpr hEU]

theorem eventually_closedBall_subset :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Metric.closedBall (coeffU Q) ε ⊆ range (beta D) := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (isOpen_range_beta D) _ (coeffU_mem_range D)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  exact (Metric.closedBall_subset_ball hε.2).trans hsub

/-- **The Leray density averages to $1$**: $\frac{1}{|B_\varepsilon|}\int_{B_\varepsilon}\rho \to \rho(c_Q) = 1$. -/
theorem tendsto_avg_rho :
    Tendsto (fun ε => (∫⁻ c in Metric.closedBall (coeffU Q) ε, ENNReal.ofReal (rho D c)).toReal /
      (volume (Metric.closedBall (coeffU Q) ε)).toReal) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_avg_box (isOpen_range_beta D) (coeffU_mem_range D) (continuousOn_rho D)
    (fun t _ => rho_nonneg D t) (g := fun c => ENNReal.ofReal (rho D c)) (fun t _ => rfl)
    (fun _ => (1 : ℝ)) (fun _ => one_pos)
  rw [rho_coeffU] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [closedBall_eq_box _ (le_of_lt hε)]

theorem lerayD_univ_lt_top [hQ : Fact (IsPosDefR Q)] : lerayD D univ < ⊤ :=
  isCompact_univ.measure_lt_top

/-- **Total mass in the definite case**: $\mu_Q(SO(Q)(\mathbb R)) = $ `archVolSO n (gramDetR Q)`, Siegel's limit
(`tendsto_siegelRatioSO`). -/
theorem lerayD_univ [hQ : Fact (IsPosDefR Q)] (hn : 1 ≤ n) :
    lerayD D univ = ENNReal.ofReal (Tamagawa.archVolSO n (gramDetR Q)) := by
  have hlim := tendsto_siegelRatioSO hQ.out hn
  have h2 : Tendsto (siegelRatioSO Q) (𝓝[>] 0) (𝓝 ((lerayD D univ).toReal * 1)) := by
    refine ((tendsto_avg_rho D).const_mul (lerayD D univ).toReal).congr' ?_
    filter_upwards [eventually_closedBall_subset D] with ε hε
    rw [siegelRatioSO, volume_tube D Metric.isClosed_closedBall.measurableSet hε, ENNReal.toReal_mul, mul_div_assoc]
  rw [mul_one] at h2
  have := tendsto_nhds_unique h2 hlim
  rw [← this, ENNReal.ofReal_toReal (lerayD_univ_lt_top D).ne]

/-- **Agreement with `ArchSO.mu`** (the measure, not only its mass): for positive definite $Q$ ($n \ge 1$) the Leray measure
is `ArchSO.mu Q`. -/
theorem lerayD_eq_mu [hQ : Fact (IsPosDefR Q)] (hn : 1 ≤ n) : lerayD D = ArchSO.mu Q := by
  have h := isMulLeftInvariant_eq_smul (lerayD D) (ArchSO.mu Q)
  have hu := congrArg (fun μ : Measure (ArchSO Q) => μ univ) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hu
  rw [lerayD_univ D hn, ArchSO.mu_univ] at hu
  have hpos : 0 < Tamagawa.archVolSO n (gramDetR Q) := archVolSO_pos n (gramDetR_pos hQ.out)
  have hk : (haarScalarFactor (lerayD D) (ArchSO.mu Q) : ℝ≥0∞) = 1 := by
    have h1 := congrArg ENNReal.toReal hu
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos.le, ENNReal.coe_toReal] at h1
    have h2 : (haarScalarFactor (lerayD D) (ArchSO.mu Q) : ℝ) = 1 := by
      have := mul_right_cancel₀ hpos.ne' (h1.symm.trans (one_mul _).symm)
      exact this
    rw [← ENNReal.coe_one, ENNReal.coe_inj]
    exact NNReal.coe_eq_one.mp h2
  rw [h, ENNReal.smul_def, hk, one_smul]

/-! ### The Leray limit for compactly supported continuous functions (any signature) -/

/-- **$g \mapsto g$ is proper** from $SO(Q)(\mathbb R)$ to $M_n(\mathbb R)$ (nondegenerate $Q$): preimages of compact
sets are compact (the inverse $g^{-1} = A^{-1}g^{\mathsf T}A$ is a continuous function of $g$). -/
theorem isCompact_mat_preimage (hA0 : (gramMatrixR Q).det ≠ 0) {K : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hK : IsCompact K) : IsCompact (ArchSOInst.mat Q ⁻¹' K) := by
  set A := gramMatrixR Q
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hA0
  set C : Set (Matrix (Fin n) (Fin n) ℝ) := K ∩ {M | Mᵀ * A * M = A ∧ M.det = 1}
  have hC : IsCompact C := hK.inter_right ((isClosed_eq ((continuous_id.matrix_transpose.matrix_mul
    continuous_const).matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq continuous_id.matrix_det continuous_const))
  let φ : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ :=
    fun M => (M, MulOpposite.op (A⁻¹ * Mᵀ * A))
  have hφ : Continuous φ := continuous_id.prodMk (MulOpposite.continuous_op.comp
    ((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const))
  -- the set in GL
  set S : Set (GL (Fin n) ℝ) := {x | x ∈ soReal Q ∧ (x : Matrix (Fin n) (Fin n) ℝ) ∈ K}
  have hS : IsCompact S := by
    rw [(Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) ℝ)).isCompact_iff]
    have : Units.embedProduct (Matrix (Fin n) (Fin n) ℝ) '' S = φ '' C := by
      ext ⟨M, N⟩
      constructor
      · rintro ⟨x, ⟨hx, hxK⟩, hxMN⟩
        have hiso : (x : Matrix (Fin n) (Fin n) ℝ)ᵀ * A * x = A :=
          ArchSOInst.isometry Q (ArchSOInst.mk Q x hx)
        have hdet : (x : Matrix (Fin n) (Fin n) ℝ).det = 1 := ((mem_soReal_iff Q x).mp hx).2
        refine ⟨x, ⟨hxK, hiso, hdet⟩, ?_⟩
        rw [← hxMN]
        simp only [φ, Units.embedProduct_apply, Prod.mk.injEq, true_and]
        congr 1
        set X : Matrix (Fin n) (Fin n) ℝ := (x : Matrix (Fin n) (Fin n) ℝ)
        set Xi : Matrix (Fin n) (Fin n) ℝ := ((x⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
        have hXXi : X * Xi = 1 := by
          simp only [X, Xi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h1 : A⁻¹ * Xᵀ * A * X = 1 := by
          calc A⁻¹ * Xᵀ * A * X = A⁻¹ * (Xᵀ * A * X) := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hiso, Matrix.nonsing_inv_mul _ hA]
        calc A⁻¹ * Xᵀ * A = A⁻¹ * Xᵀ * A * (X * Xi) := by rw [hXXi, Matrix.mul_one]
          _ = Xi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      · rintro ⟨M', ⟨hM'K, hiso, hdet⟩, hM'⟩
        have hinv : A⁻¹ * M'ᵀ * A * M' = 1 := by
          calc A⁻¹ * M'ᵀ * A * M' = A⁻¹ * (M'ᵀ * A * M') := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hiso, Matrix.nonsing_inv_mul _ hA]
        let x : GL (Fin n) ℝ := ⟨M', A⁻¹ * M'ᵀ * A, mul_eq_one_comm.mp hinv, hinv⟩
        have hx : x ∈ soReal Q := by
          rw [mem_soReal_iff]
          refine ⟨?_, hdet⟩
          have : Q.hessian = (2 : ℝ) • A := by simp only [A, gramMatrixR, smul_smul]; norm_num
          change M'ᵀ * Q.hessian * M' = Q.hessian
          rw [this, Matrix.mul_smul, Matrix.smul_mul, hiso]
        exact ⟨x, ⟨hx, hM'K⟩, by rw [← hM']; rfl⟩
    rw [this]; exact hC.image hφ
  have hemb : Topology.IsClosedEmbedding (ArchSO.incl Q) := (isClosed_soReal Q).isClosedEmbedding_subtypeVal
  have : ArchSOInst.mat Q ⁻¹' K = ArchSO.incl Q ⁻¹' S := by
    ext g
    simp only [mem_preimage, S, mem_setOf_eq, ArchSOInst.mat]
    exact ⟨fun h => ⟨ArchSOInst.incl_mem Q g, h⟩, fun h => h.2⟩
  rw [this]
  exact hemb.isCompact_preimage hS

theorem continuous_ofCols : Continuous (ofCols : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)

theorem continuous_ofCols_mul :
    Continuous fun p : (Fin n → Fin n → ℝ) × SliceB D.P => ofCols p.1 * SliceB.mat D.P p.2⁻¹ :=
  (continuous_ofCols.comp continuous_fst).matrix_mul
    ((SliceB.continuous_mat D.P).comp (continuous_inv.comp continuous_snd))

theorem continuous_chart_swap {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Continuous (Function.uncurry fun (b : SliceB D.P) (g : ArchSO Q) => f (chart D (g, b))) :=
  hf.comp ((continuous_chart D).comp (continuous_snd.prodMk continuous_fst))

/-- **The fibre integral** $F_f(b) = \int_{SO(Q)} f(gb)\,d\mu_Q(g)$. -/
def fibreInt (f : (Fin n → Fin n → ℝ) → ℝ) (b : SliceB D.P) : ℝ :=
  ∫ g, f (chart D (g, b)) ∂lerayD D

instance : IsLocallyFiniteMeasure (lerayD D) := inferInstance

theorem continuous_fibreInt {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (fibreInt D f) := by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨N, hNc, hNn⟩ := exists_compact_mem_nhds b₀
  -- all the integrands for b ∈ N are supported in a fixed compact set L ⊆ SO(Q)
  set K' : Set (Matrix (Fin n) (Fin n) ℝ) :=
    (fun p : (Fin n → Fin n → ℝ) × SliceB D.P => ofCols p.1 * SliceB.mat D.P p.2⁻¹) '' (tsupport f ×ˢ N)
  have hK' : IsCompact K' := (hfc.isCompact.prod hNc).image (continuous_ofCols_mul D)
  set L := ArchSOInst.mat Q ⁻¹' K'
  have hL : IsCompact L := isCompact_mat_preimage D.det_gram_ne_zero hK'
  have hsupp : ∀ b ∈ N, ∀ g ∉ L, f (chart D (g, b)) = 0 := by
    intro b hb g hg
    by_contra hne
    apply hg
    refine ⟨(chart D (g, b), b), ⟨subset_tsupport f hne, hb⟩, ?_⟩
    show ofCols (chart D (g, b)) * SliceB.mat D.P b⁻¹ = ArchSOInst.mat Q g
    rw [chart, show ofCols (cols (ArchSOInst.mat Q g * SliceB.mat D.P b)) =
      ArchSOInst.mat Q g * SliceB.mat D.P b from rfl, Matrix.mul_assoc, SliceB.mat_mul_inv, Matrix.mul_one]
  have hcont : Continuous fun b : SliceB D.P => ∫ g in L, f (chart D (g, b)) ∂lerayD D :=
    continuous_parametric_integral_of_continuous (continuous_chart_swap D hf) hL
  refine hcont.continuousAt.congr ?_
  filter_upwards [hNn] with b hb
  rw [fibreInt, setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => hsupp b hb g hg]

theorem hasCompactSupport_fibre {f : (Fin n → Fin n → ℝ) → ℝ} (hfc : HasCompactSupport f) (b : SliceB D.P) :
    HasCompactSupport fun g : ArchSO Q => f (chart D (g, b)) := by
  set K' : Set (Matrix (Fin n) (Fin n) ℝ) := (fun X => ofCols X * SliceB.mat D.P b⁻¹) '' tsupport f
  have hK' : IsCompact K' := hfc.isCompact.image (continuous_ofCols.matrix_mul continuous_const)
  refine HasCompactSupport.intro (isCompact_mat_preimage D.det_gram_ne_zero hK') fun g hg => ?_
  by_contra hne
  apply hg
  refine ⟨chart D (g, b), subset_tsupport f hne, ?_⟩
  show ofCols (cols (ArchSOInst.mat Q g * SliceB.mat D.P b)) * SliceB.mat D.P b⁻¹ = ArchSOInst.mat Q g
  rw [show ofCols (cols (ArchSOInst.mat Q g * SliceB.mat D.P b)) =
    ArchSOInst.mat Q g * SliceB.mat D.P b from rfl, Matrix.mul_assoc, SliceB.mat_mul_inv, Matrix.mul_one]

theorem setLIntegral_image_comap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) (μ : Measure β) {s : Set α} (hs : MeasurableSet s) (φ : β → ℝ≥0∞) :
    ∫⁻ y in e '' s, φ y ∂μ = ∫⁻ x in s, φ (e x) ∂(Measure.comap e μ) := by
  rw [← lintegral_indicator hs]
  have : s.indicator (fun x => φ (e x)) = (e '' s).indicator φ ∘ e := by
    funext x
    by_cases hx : x ∈ s <;> simp [indicator, hx, he.injective.mem_set_image]
  rw [this, show (∫⁻ a, ((e '' s).indicator φ ∘ e) a ∂(Measure.comap e μ)) =
      ∫⁻ a, (e '' s).indicator φ (e a) ∂(Measure.comap e μ) from rfl, ← he.lintegral_map, he.map_comap, lintegral_indicator (he.measurableSet_image' hs),
    Measure.restrict_restrict (he.measurableSet_image' hs), inter_eq_left.mpr (image_subset_range e s)]

/-- **Integrals against $\kappa_0$ in coefficient space**: $\int_{\beta^{-1}E}\psi\,d\kappa_0 =
\int_{E \cap U}\rho(c)\,\psi(\beta^{-1}c)\,dc$. -/
theorem setLIntegral_kappa0 {E : Set (UIdx n → ℝ)} (hE : MeasurableSet E) {ψ : SliceB D.P → ℝ≥0∞}
    (hψ : Measurable ψ) :
    ∫⁻ b in beta D ⁻¹' E, ψ b ∂kappa0 D =
      ∫⁻ c in E ∩ range (beta D), ENNReal.ofReal (rho D c) * ψ (sec D c) := by
  have hmE : MeasurableSet (beta D ⁻¹' E) := (continuous_beta D).measurable hE
  rw [kappa0, setLIntegral_withDensity_eq_setLIntegral_mul _ (Leray.measurable_char (thetaB D) (continuous_thetaB D))
    hψ hmE, ← image_preimage_eq_inter_range,
    setLIntegral_image_comap (measurableEmbedding_beta D) volume hmE]
  refine setLIntegral_congr_fun hmE fun x _ => ?_
  simp only [Pi.mul_apply, rho, sec_beta, ENNReal.ofReal_coe_nnreal]

/-- **The region of the Leray limit**: $\{X \in M_n(\mathbb R) : \det X > 0,\ \Phi_Q(X) \in B_\varepsilon(c_Q)\}$
(sup-norm ball in coefficient coordinates). -/
def lerayRegion (Q : QuadForm ℝ n) (ε : ℝ) : Set (Fin n → Fin n → ℝ) :=
  {X | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ Metric.closedBall (coeffU Q) ε}

/-- **The Leray approximant** $\frac{1}{\mathrm{Leb}(B_\varepsilon(c_Q))}\int_{\{\det X > 0,\ \Phi_Q(X) \in
B_\varepsilon(c_Q)\}} f(X)\,dX$. It depends only on $Q$ (no choices). -/
def lerayApprox (Q : QuadForm ℝ n) (f : (Fin n → Fin n → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  (∫ X in lerayRegion Q ε, f X) / (volume (Metric.closedBall (coeffU Q) ε)).toReal

theorem measurableSet_lerayRegion (ε : ℝ) : MeasurableSet (lerayRegion Q ε) := by
  have hdc : Continuous fun X : Fin n → Fin n → ℝ => (Matrix.of X).det := by
    have : (fun X : Fin n → Fin n → ℝ => (Matrix.of X).det) = fun X => (ofCols X).det :=
      funext fun X => (det_ofCols X).symm
    rw [this]; exact continuous_ofCols.matrix_det
  exact (measurableSet_lt measurable_const hdc.measurable).inter
    (Metric.isClosed_closedBall.measurableSet.preimage (continuous_pullCoeff Q).measurable)

/-- The fibration identity on the Leray regions, for $f \ge 0$. -/
theorem lintegral_lerayRegion {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ X, 0 ≤ f X) {ε : ℝ} (hε : Metric.closedBall (coeffU Q) ε ⊆ range (beta D)) :
    ∫⁻ X in lerayRegion Q ε, ENNReal.ofReal (f X) =
      ∫⁻ c in Metric.closedBall (coeffU Q) ε, ENNReal.ofReal (fibreInt D f (sec D c) * rho D c) := by
  have hB : MeasurableSet (Metric.closedBall (coeffU Q) ε) := Metric.isClosed_closedBall.measurableSet
  have hT : MeasurableSet (beta D ⁻¹' Metric.closedBall (coeffU Q) ε) := (continuous_beta D).measurable hB
  rw [lerayRegion, ← image_chart D hε,
    setLIntegral_image_comap (measurableEmbedding_chart D) volume (MeasurableSet.univ.prod hT), lerayFibration,
    ← Measure.prod_restrict, Measure.restrict_univ]
  rw [lintegral_prod_symm (fun x => ENNReal.ofReal (f (chart D x)))
    ((ENNReal.continuous_ofReal.comp (hf.comp (continuous_chart D))).measurable.aemeasurable)]
  have hinner : ∀ b, ∫⁻ g, ENNReal.ofReal (f (chart D (g, b))) ∂lerayD D = ENNReal.ofReal (fibreInt D f b) := by
    intro b
    rw [fibreInt, ofReal_integral_eq_lintegral_ofReal]
    · exact (hf.comp ((continuous_chart D).comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hasCompactSupport_fibre D hfc b)
    · exact Filter.Eventually.of_forall fun g => hf0 _
  simp_rw [hinner]
  rw [setLIntegral_kappa0 D hB (ψ := fun b => ENNReal.ofReal (fibreInt D f b))
      (ENNReal.continuous_ofReal.comp (continuous_fibreInt D hf hfc)).measurable,
    inter_eq_left.mpr hε]
  refine setLIntegral_congr_fun hB fun c _ => ?_
  have h0 : 0 ≤ fibreInt D f (sec D c) := integral_nonneg fun g => hf0 _
  rw [mul_comm, ← ENNReal.ofReal_mul h0]

/-- **The Leray limit, $f \ge 0$.** -/
theorem tendsto_lerayApprox_of_nonneg {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ X, 0 ≤ f X) :
    Tendsto (lerayApprox Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D)) := by
  set H : (UIdx n → ℝ) → ℝ := fun c => fibreInt D f (sec D c) * rho D c
  have hHc : ContinuousOn H (range (beta D)) :=
    ((continuous_fibreInt D hf hfc).comp_continuousOn (continuousOn_sec D)).mul (continuousOn_rho D)
  have hH0 : ∀ c ∈ range (beta D), 0 ≤ H c := fun c _ =>
    mul_nonneg (integral_nonneg fun g => hf0 _) (rho_nonneg D c)
  have h := tendsto_avg_box (isOpen_range_beta D) (coeffU_mem_range D) hHc hH0
    (g := fun c => ENNReal.ofReal (H c)) (fun t _ => rfl) (fun _ => (1 : ℝ)) (fun _ => one_pos)
  have hH1 : H (coeffU Q) = ∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
    simp only [H, rho_coeffU, mul_one, sec_coeffU, fibreInt, chart, SliceB.mat_one]
  rw [hH1] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_closedBall_subset D] with ε hε hsub
  rw [lerayApprox, ← closedBall_eq_box _ (le_of_lt hε),
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => hf0 X)
      hf.aestronglyMeasurable, lintegral_lerayRegion D hf hfc hf0 hsub]

/-- **The Leray limit** (any signature): for every compactly supported continuous $f$ on $M_n(\mathbb R)$,
$$\frac{1}{\mathrm{Leb}(B_\varepsilon(c_Q))}\int_{\{\det X>0,\ \Phi_Q(X)\in B_\varepsilon(c_Q)\}} f(X)\,dX
\longrightarrow \int_{SO(Q)(\mathbb R)} f\,d\mu_Q \qquad (\varepsilon \to 0^+).$$ -/
theorem tendsto_lerayApprox {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (lerayApprox Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D)) := by
  set fp : (Fin n → Fin n → ℝ) → ℝ := fun X => max (f X) 0
  set fm : (Fin n → Fin n → ℝ) → ℝ := fun X => max (-f X) 0
  have hfp : Continuous fp := hf.max continuous_const
  have hfm : Continuous fm := hf.neg.max continuous_const
  have hfpc : HasCompactSupport fp := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fp, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hfmc : HasCompactSupport fm := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fm, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hp := tendsto_lerayApprox_of_nonneg D hfp hfpc (fun X => le_max_right _ _)
  have hm := tendsto_lerayApprox_of_nonneg D hfm hfmc (fun X => le_max_right _ _)
  have hsplit : ∀ ε, lerayApprox Q f ε = lerayApprox Q fp ε - lerayApprox Q fm ε := by
    intro ε
    have hip : IntegrableOn fp (lerayRegion Q ε) := (hfp.integrable_of_hasCompactSupport hfpc).integrableOn
    have him : IntegrableOn fm (lerayRegion Q ε) := (hfm.integrable_of_hasCompactSupport hfmc).integrableOn
    rw [lerayApprox, lerayApprox, lerayApprox, ← sub_div, ← integral_sub hip him]
    congr 2; funext X; exact (max_zero_sub_max_neg_zero_eq_self (f X)).symm
  have hG : ∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayD D =
      ∫ g, fp (cols (ArchSOInst.mat Q g)) ∂lerayD D - ∫ g, fm (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
    have hc1 := hasCompactSupport_fibre D hfpc 1
    have hc2 := hasCompactSupport_fibre D hfmc 1
    simp only [chart, SliceB.mat_one, Matrix.mul_one] at hc1 hc2
    have i1 : Integrable (fun g => fp (cols (ArchSOInst.mat Q g))) (lerayD D) :=
      (hfp.comp (continuous_cols.comp (ArchSOInst.continuous_mat Q))).integrable_of_hasCompactSupport hc1
    have i2 : Integrable (fun g => fm (cols (ArchSOInst.mat Q g))) (lerayD D) :=
      (hfm.comp (continuous_cols.comp (ArchSOInst.continuous_mat Q))).integrable_of_hasCompactSupport hc2
    rw [← integral_sub i1 i2]
    congr 1; funext g; exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hG, show lerayApprox Q f = fun ε => lerayApprox Q fp ε - lerayApprox Q fm ε from funext hsplit]
  exact hp.sub hm

/-! ### Uniqueness: the Leray limit characterizes $\mu_Q$ -/

/-- A bump function at the identity matrix. -/
def bump (n : ℕ) (X : Fin n → Fin n → ℝ) : ℝ := max 0 (1 - dist X (cols (1 : Matrix (Fin n) (Fin n) ℝ)))

theorem continuous_bump : Continuous (bump n) :=
  continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))

theorem hasCompactSupport_bump : HasCompactSupport (bump n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (cols (1 : Matrix (Fin n) (Fin n) ℝ)) 1) fun X hX => ?_
  simp only [Metric.mem_closedBall, not_le] at hX
  simp only [bump]
  exact max_eq_left (by linarith)

theorem bump_nonneg (X : Fin n → Fin n → ℝ) : 0 ≤ bump n X := le_max_left _ _

theorem integral_bump_pos : 0 < ∫ g, bump n (cols (ArchSOInst.mat Q g)) ∂lerayD D := by
  have hc := hasCompactSupport_fibre D (hasCompactSupport_bump (n := n)) 1
  simp only [chart, SliceB.mat_one, Matrix.mul_one] at hc
  refine (continuous_bump.comp (continuous_cols.comp (ArchSOInst.continuous_mat Q))).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hc (fun g => bump_nonneg _) (x := 1) ?_
  have : ArchSOInst.mat Q 1 = 1 := by simp [ArchSOInst.mat]
  simp [Function.comp_apply, this, bump]

/-- **Uniqueness of the Leray measure**: a left-invariant measure on $SO(Q)(\mathbb R)$, finite on compact sets,
that satisfies the Leray limit (`lerayApprox Q f` $\to \int f\,d\mu'$) for every compactly supported continuous $f$
equals $\mu_Q$. In particular the construction does not depend on the slice data (`lerayD_eq`). -/
theorem lerayD_unique (μ' : Measure (ArchSO Q)) [μ'.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ']
    (h : ∀ f : (Fin n → Fin n → ℝ) → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (lerayApprox Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOInst.mat Q g)) ∂μ'))) :
    μ' = lerayD D := by
  have hμ := isMulLeftInvariant_eq_smul μ' (lerayD D)
  set k := haarScalarFactor μ' (lerayD D)
  have h1 := tendsto_nhds_unique (h (bump n) continuous_bump hasCompactSupport_bump)
    (tendsto_lerayApprox D continuous_bump hasCompactSupport_bump)
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h1
  have hpos := integral_bump_pos D
  have hk : (k : ℝ) = 1 := mul_right_cancel₀ hpos.ne' (h1.trans (one_mul _).symm)
  rw [hμ, show k = 1 from NNReal.coe_eq_one.mp hk, one_smul]

/-- **Independence of the choices**: two slice data give the same Leray measure. -/
theorem lerayD_eq (D D' : Diag Q) : lerayD D = lerayD D' :=
  lerayD_unique D' (lerayD D) fun _ hf hfc => tendsto_lerayApprox D hf hfc

/-! ### The canonical Leray measure -/

/-- **The Leray (gauge-form) measure** $\mu_Q$ on $SO(Q)(\mathbb R)$ for a nondegenerate real quadratic form of any
signature: the measure with $dX = \mu_Q \otimes dc$ along the fibre $\Phi_Q^{-1}(c_Q) \cap \{\det > 0\}$
(`lerayMeasure_fibration`), characterized by the Leray limit (`tendsto_lerayMeasure`, `lerayMeasure_unique`).
Normalization: Lebesgue measure $dX$ on $M_n(\mathbb R)$ and $dc$ on coefficient space ($c_{ij}$, $i \le j$), as in `archVolSOLim`. -/
@[kb "weil1982" "§2.2 (gauge forms), §2.4 Theorem 2.4.3, p. 25 (matching measures on G, H, G/H) [unverified]"]
def lerayMeasure (Q : QuadForm ℝ n) (hQ : gramDetR Q ≠ 0) : Measure (ArchSO Q) :=
  lerayD (Diag.ofSpectral Q hQ)

variable (hQ : gramDetR Q ≠ 0)

/-- **$\mu_Q$ is a left Haar measure** on $SO(Q)(\mathbb R)$, any signature. -/
@[kb "weil1982" "§2.2 (gauge forms) [unverified]"]
theorem isHaarMeasure_lerayMeasure : (lerayMeasure Q hQ).IsHaarMeasure :=
  isHaarMeasure_lerayD _

/-- **The fibration identity**: for any slice data $D$, the pull-back of $dX$ along $(g, b) \mapsto gb$ is
$\mu_Q \otimes \kappa_0$. -/
@[kb "weil1982" "§2.4 Theorem 2.4.3, p. 25 (matching measures) [unverified]"]
theorem lerayMeasure_fibration (D : Diag Q) :
    Measure.comap (chart D) volume = (lerayMeasure Q hQ).prod (kappa0 D) := by
  rw [lerayMeasure, lerayD_eq (Diag.ofSpectral Q hQ) D, lerayFibration]

/-- **The Leray limit** (any signature). -/
@[kb "weil1982" "§2.2 (gauge forms as limits of volume ratios) [unverified]"]
theorem tendsto_lerayMeasure {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (lerayApprox Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOInst.mat Q g)) ∂lerayMeasure Q hQ)) :=
  tendsto_lerayApprox _ hf hfc

/-- **The Leray limit characterizes $\mu_Q$.** -/
@[kb "weil1982" "§2.2 (gauge forms) [unverified]"]
theorem lerayMeasure_unique (μ' : Measure (ArchSO Q)) [μ'.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ']
    (h : ∀ f : (Fin n → Fin n → ℝ) → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (lerayApprox Q f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOInst.mat Q g)) ∂μ'))) :
    μ' = lerayMeasure Q hQ :=
  lerayD_unique _ μ' h

/-- **Total mass in the definite case**: $\mu_Q(SO(Q)(\mathbb R)) = $ `archVolSO n (gramDetR Q)`. -/
@[kb "siegel1935" "vol(SO_n(R), dX/dS) [unverified]"]
theorem lerayMeasure_univ [Fact (IsPosDefR Q)] (hn : 1 ≤ n) :
    lerayMeasure Q hQ univ = ENNReal.ofReal (Tamagawa.archVolSO n (gramDetR Q)) :=
  lerayD_univ _ hn

/-- **Agreement with `ArchSO.mu`**: for positive definite $Q$ ($n \ge 1$) the Leray measure is `ArchSO.mu Q`. -/
@[kb "weil1982" "§2.2 (gauge forms); cf. archVolSO_eq_volume [unverified]"]
theorem lerayMeasure_eq_mu [Fact (IsPosDefR Q)] (hn : 1 ≤ n) : lerayMeasure Q hQ = ArchSO.mu Q :=
  lerayD_eq_mu _ hn

end QuadFormsKB.Tamagawa.Measure.LerayReal
