import QuadFormsKB.Tamagawa.Measure.SphereLerayC
import QuadFormsKB.Tamagawa.Measure.LerayCount
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqLocal

/-!
# The norm-one quaternions as a locally compact group with Haar measure $\sigma$

**Layer:** one archimedean place; a quaternion algebra $\mathbb H[K,A,B]$ over $K = \mathbb R$ or $\mathbb C$ with its norm form
$N = \langle1,-A,-B,AB\rangle$ (`normForm A B`, $N(v) = \operatorname{nrd}(v_0 + v_1i + v_2j + v_3k)$, `eval_normForm`).

* **`NormOne K A B`**: the sphere $\{v\in K^4 : N(v) = 1\}$ (the group $\mathrm{SL}_1(\mathbb H[K,A,B])$ in the coordinates $1,i,j,k$),
  with the quaternion product (`NormOne.mul_val`), a topological group, closed in $K^4$.
* The same group structure on the sphere types `SphereLeray.Sph (normForm A B) 1` ($K = \mathbb R$) and
  `SphereLerayC.SphC (normForm A B) 1` ($K = \mathbb C$), on which the sphere Leray measures $\sigma$ = `sig`, `sigC` live.
* **`lmat`**: the matrix of left multiplication $v\mapsto xv$; $L_x^{\mathsf T}NL_x = \operatorname{nrd}(x)N$ (`lmat_isometry`),
  $\det L_x = \operatorname{nrd}(x)^2$ (`det_lmat`).
* **`isHaarMeasure_sig`**, **`isHaarMeasure_sigC`**: $\sigma$ is a left Haar measure on $\mathrm{SL}_1$ (left multiplication is an isometry
  of $N$ of determinant $1$, `map_sphMap_sig`; finite on bounded sets; positive on open sets because the polar map is a
  homeomorphism onto the open set $\{N > 0\}$, resp. its complex analogue).
-/

open MeasureTheory Measure Set Matrix Topology Filter
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil

/-! ### The norm form -/

section Generic

variable {K : Type*} [Field K]

/-- **The norm form** $\langle1,-A,-B,AB\rangle$ of $\mathbb H[K,A,B]$. -/
def normForm (A B : K) : QuadForm K 4 := QuadForm.diag ![1, -A, -B, A * B]

theorem eval_normForm (A B : K) (v : Fin 4 → K) :
    (normForm A B).eval v = nrd (vecQ v : ℍ[K,A,B]) := by
  simp only [normForm, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal_apply]
  simp [nrd, vecQ]
  ring

theorem eval_normForm_qVec (A B : K) (x : ℍ[K,A,B]) : (normForm A B).eval (qVec x) = nrd x := by
  rw [eval_normForm, vecQ_qVec]

variable (K) in
/-- **The norm-one quaternions** $\{v\in K^4 : N(v) = 1\}$ (coordinates in the basis $1, i, j, k$). -/
def NormOne (A B : K) : Type _ := ↥{v : Fin 4 → K | (normForm A B).eval v = 1}

namespace NormOne

variable {A B : K}

theorem nrd_val (x : NormOne K A B) : nrd (vecQ (x.1 : Fin 4 → K) : ℍ[K,A,B]) = 1 := by
  rw [← eval_normForm]; exact x.2

/-- The point of `NormOne` given by a quaternion of reduced norm $1$. -/
def ofQuat (q : ℍ[K,A,B]) (hq : nrd q = 1) : NormOne K A B := ⟨qVec q, by
  show (normForm A B).eval (qVec q) = 1
  rw [eval_normForm_qVec, hq]⟩

instance : Mul (NormOne K A B) where
  mul x y := ofQuat (vecQ x.1 * vecQ y.1) (by rw [nrd_mul, nrd_val, nrd_val, one_mul])

instance : One (NormOne K A B) where
  one := ofQuat 1 nrd_one

instance : Inv (NormOne K A B) where
  inv x := ofQuat (star (vecQ x.1)) (by rw [nrd_star, nrd_val])

theorem mul_val (x y : NormOne K A B) : (x * y).1 = qVec (vecQ x.1 * vecQ y.1 : ℍ[K,A,B]) := rfl

theorem one_val : (1 : NormOne K A B).1 = qVec (1 : ℍ[K,A,B]) := rfl

theorem inv_val (x : NormOne K A B) : (x⁻¹).1 = qVec (star (vecQ x.1 : ℍ[K,A,B])) := rfl

theorem ext' {x y : NormOne K A B} (h : (vecQ x.1 : ℍ[K,A,B]) = vecQ y.1) : x = y := by
  apply Subtype.ext
  have := congrArg qVec h
  rwa [qVec_vecQ, qVec_vecQ] at this

theorem vecQ_mul (x y : NormOne K A B) :
    (vecQ (x * y).1 : ℍ[K,A,B]) = vecQ x.1 * vecQ y.1 := by
  rw [mul_val, vecQ_qVec]

theorem vecQ_one : (vecQ (1 : NormOne K A B).1 : ℍ[K,A,B]) = 1 := by
  rw [one_val, vecQ_qVec]

theorem vecQ_inv (x : NormOne K A B) : (vecQ x⁻¹.1 : ℍ[K,A,B]) = star (vecQ x.1) := by
  rw [inv_val, vecQ_qVec]

instance : Group (NormOne K A B) where
  mul_assoc x y z := ext' (by rw [vecQ_mul, vecQ_mul, vecQ_mul, vecQ_mul, mul_assoc])
  one_mul x := ext' (by rw [vecQ_mul, vecQ_one, one_mul])
  mul_one x := ext' (by rw [vecQ_mul, vecQ_one, mul_one])
  inv_mul_cancel x := ext' (by
    rw [vecQ_mul, vecQ_inv, vecQ_one, star_mul_eq_nrd, nrd_val]; rfl)

/-- $-1$ in `NormOne`. -/
instance : Neg (NormOne K A B) where
  neg x := ofQuat (-vecQ x.1) (by
    rw [show (-vecQ x.1 : ℍ[K,A,B]) = ((-1 : K) : ℍ[K,A,B]) * vecQ x.1 by simp, nrd_mul, nrd_coe, nrd_val]; ring)

theorem neg_val (x : NormOne K A B) : (-x).1 = -x.1 := by
  show qVec (-vecQ x.1 : ℍ[K,A,B]) = -x.1
  funext i; fin_cases i <;> rfl

end NormOne

end Generic

/-! ### Topology -/

section Topology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {A B : K}

instance : TopologicalSpace (NormOne K A B) := inferInstanceAs (TopologicalSpace (↥{v : Fin 4 → K | _}))

theorem continuous_val : Continuous (fun x : NormOne K A B => (x.1 : Fin 4 → K)) := continuous_subtype_val

theorem continuous_qVec_mul {X : Type*} [TopologicalSpace X] {f g : X → Fin 4 → K} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => qVec (vecQ (f x) * vecQ (g x) : ℍ[K,A,B]) := by
  have h : ∀ i, Continuous fun x => f x i := fun i => (continuous_apply i).comp hf
  have h' : ∀ i, Continuous fun x => g x i := fun i => (continuous_apply i).comp hg
  refine continuous_pi fun i => ?_
  fin_cases i <;>
  simp only [qVec, vecQ, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
  fun_prop

instance : IsTopologicalGroup (NormOne K A B) where
  continuous_mul := by
    refine Continuous.subtype_mk (continuous_qVec_mul (continuous_val.comp continuous_fst)
      (continuous_val.comp continuous_snd)) _
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    have hg : Continuous fun v : Fin 4 → K => qVec (star (vecQ v : ℍ[K,A,B])) := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp only [qVec, vecQ, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
        QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val] <;> fun_prop
    exact hg.comp continuous_val

theorem continuous_eval_normForm : Continuous fun v : Fin 4 → K => (normForm A B).eval v := by
  have : (fun v : Fin 4 → K => (normForm A B).eval v) = fun v => nrd (vecQ v : ℍ[K,A,B]) :=
    funext (eval_normForm A B)
  rw [this]
  simp only [nrd, vecQ]
  fun_prop

theorem isClosed_normOne [T2Space K] : IsClosed {v : Fin 4 → K | (normForm A B).eval v = 1} :=
  isClosed_eq continuous_eval_normForm continuous_const

end Topology

/-! ### Left multiplication -/

section LMat

variable {K : Type*} [Field K] {A B : K}

/-- **The matrix of left multiplication** $v\mapsto xv$ in the basis $1,i,j,k$. -/
def lmat (x : ℍ[K,A,B]) : Matrix (Fin 4) (Fin 4) K := sqMat x 1

theorem lmat_mulVec (x : ℍ[K,A,B]) (v : Fin 4 → K) : lmat x *ᵥ v = qVec (x * vecQ v) := by
  funext i
  fin_cases i <;>
  simp [lmat, sqMat, qVec, vecQ, mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring

/-- The diagonal matrix of $N$. -/
def nDiag (A B : K) : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, -A, -B, A * B]

/-- **$L_x^{\mathsf T}\,\mathrm{diag}(1,-A,-B,AB)\,L_x = \operatorname{nrd}(x)\,\mathrm{diag}(1,-A,-B,AB)$.** -/
theorem lmat_isometry (x : ℍ[K,A,B]) : (lmat x)ᵀ * nDiag A B * lmat x = nrd x • nDiag A B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [lmat, sqMat, nDiag, qVec, vecQ, Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply,
    QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    Matrix.diagonal_apply, nrd] <;> ring

/-- **$\det L_x = \operatorname{nrd}(x)^2$.** -/
theorem lmat_eq (x : ℍ[K,A,B]) : lmat x = !![x.re, A * x.imI, B * x.imJ, -(A * B) * x.imK;
    x.imI, x.re, B * x.imK, -B * x.imJ; x.imJ, -A * x.imK, x.re, A * x.imI; x.imK, -x.imJ, x.imI, x.re] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [lmat, sqMat, qVec, vecQ, Pi.single_apply, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring

theorem det_lmat (x : ℍ[K,A,B]) : (lmat x).det = nrd x ^ 2 := by
  rw [lmat_eq, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, nrd, Fin.succAbove]
  ring

/-- **The matrix of right multiplication** $v\mapsto vx$. -/
def rmat (x : ℍ[K,A,B]) : Matrix (Fin 4) (Fin 4) K := sqMat 1 x

theorem rmat_mulVec (x : ℍ[K,A,B]) (v : Fin 4 → K) : rmat x *ᵥ v = qVec (vecQ v * x) := by
  funext i
  fin_cases i <;>
  simp [rmat, sqMat, qVec, vecQ, mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring

theorem rmat_isometry (x : ℍ[K,A,B]) : (rmat x)ᵀ * nDiag A B * rmat x = nrd x • nDiag A B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [rmat, sqMat, nDiag, qVec, vecQ, Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply,
    QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    Matrix.diagonal_apply, nrd] <;> ring

theorem rmat_eq (x : ℍ[K,A,B]) : rmat x = !![x.re, A * x.imI, B * x.imJ, -(A * B) * x.imK;
    x.imI, x.re, -B * x.imK, B * x.imJ; x.imJ, A * x.imK, x.re, -A * x.imI; x.imK, x.imJ, -x.imI, x.re] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [rmat, sqMat, qVec, vecQ, Pi.single_apply, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring

theorem det_rmat (x : ℍ[K,A,B]) : (rmat x).det = nrd x ^ 2 := by
  rw [rmat_eq, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, nrd, Fin.succAbove]
  ring

end LMat

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
