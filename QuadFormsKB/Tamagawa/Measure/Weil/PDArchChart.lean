import QuadFormsKB.Tamagawa.Measure.Weil.PDCongruence
import QuadFormsKB.Tamagawa.Measure.Weil.ArchFirstOrder

open Matrix Quaternion

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.ArchVol

section Alg

variable {K : Type*} [Field K] (A B : K)

/-- $q(y) = \operatorname{nrd}(y)$ for a pure quaternion $y = y_0i + y_1j + y_2k$ of $(A,B)_K$. -/
def qPure (y : Fin 3 → K) : K := -A * y 0 ^ 2 - B * y 1 ^ 2 + A * B * y 2 ^ 2

theorem nrd_one_add_pure_eq (y : Fin 3 → K) : nrd (1 + Quat.pure y : ℍ[K,A,B]) = 1 + qPure A B y := by
  rw [nrd_one_add_pure, qPure]; ring

theorem qPure_smul (t : K) (y : Fin 3 → K) : qPure A B (t • y) = t ^ 2 * qPure A B y := by
  simp only [qPure, Pi.smul_apply, smul_eq_mul]; ring

/-- The quadratic part $N(y) = $ the matrix of $z \mapsto y z \bar y$ ($y$ pure). -/
def nTwo (y : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K := nMat (Quat.pure y : ℍ[K,A,B])

theorem nMat_one_add_pure_eq (y : Fin 3 → K) :
    nMat (1 + Quat.pure y : ℍ[K,A,B]) = 1 + adMat A B y + nTwo A B y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [nMat, nTwo, adMat, imv, Quat.pure, Pi.single_apply] <;> ring

theorem adMat_smul (t : K) (y : Fin 3 → K) : adMat A B (t • y) = t • adMat A B y := by
  rw [adMat_eq, adMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem nTwo_smul (t : K) (y : Fin 3 → K) : nTwo A B (t • y) = t ^ 2 • nTwo A B y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nTwo, nMat, imv, Quat.pure, Pi.single_apply] <;> ring

/-- **The conjugation matrix of $1 + y$**: $c(1+y) = \operatorname{nrd}(1+y)^{-1}N(1+y)$. -/
def cMat (y : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K := (1 + qPure A B y)⁻¹ • nMat (1 + Quat.pure y : ℍ[K,A,B])

theorem conjGL_eq_cMat (u : (ℍ[K,A,B])ˣ) (y : Fin 3 → K) (hu : (u : ℍ[K,A,B]) = 1 + Quat.pure y) :
    ((conjGL u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cMat A B y := by
  have hinv : nrd ((u⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = (nrd (u : ℍ[K,A,B]))⁻¹ := by
    have h := nrd_mul (u : ℍ[K,A,B]) ((u⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
    rw [Units.mul_inv, nrd_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  rw [conjGL_val, hinv, hu, nrd_one_add_pure_eq, cMat]

/-- Upper triangular matrix with entries $w_{ij}$, $i \le j$. -/
def utK (w : UIdx 3 → K) : Matrix (Fin 3) (Fin 3) K := fun i j => if h : i ≤ j then w ⟨(i, j), h⟩ else 0

theorem utK_add (w w' : UIdx 3 → K) : utK (w + w') = utK w + utK w' := by
  ext i j; simp only [utK, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp

theorem utK_sub (w w' : UIdx 3 → K) : utK (w - w') = utK w - utK w' := by
  ext i j; simp only [utK, Pi.sub_apply, Matrix.sub_apply]; split_ifs <;> simp

theorem utK_smul (t : K) (w : UIdx 3 → K) : utK (t • w) = t • utK w := by
  ext i j; simp only [utK, Pi.smul_apply, Matrix.smul_apply]; split_ifs <;> simp

/-- The upper triangular entries of $\operatorname{ad}(y)$. -/
def upVec (y : Fin 3 → K) : UIdx 3 → K := fun p => adMat A B y p.1.1 p.1.2

theorem upVec_smul (t : K) (y : Fin 3 → K) : upVec A B (t • y) = t • upVec A B y := by
  funext p; simp [upVec, adMat_smul]

/-- The strictly lower triangular part of $\operatorname{ad}(y)$. -/
def lowMat (y : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K := adMat A B y - utK (upVec A B y)

theorem lowMat_eq (y : Fin 3 → K) :
    lowMat A B y = !![0, 0, 0; -(2 * A * y 2), 0, 0; -(2 * y 1), 2 * y 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowMat, upVec, utK, adMat_eq]

/-- **The chart at the identity**: $(y, w) \mapsto c(1+y)\,(1 + U(w - u(y)))$, $u(y)$ the upper part of
$\operatorname{ad} y$. -/
def chartMat (p : (Fin 3 → K) × (UIdx 3 → K)) : Matrix (Fin 3) (Fin 3) K :=
  cMat A B p.1 * (1 + utK (p.2 - upVec A B p.1))

/-- The line through $0$ in the direction $p$, as a polynomial over a rational function. -/
theorem chartMat_smul (t : K) (p : (Fin 3 → K) × (UIdx 3 → K)) :
    chartMat A B (t • p) = (1 + t ^ 2 * qPure A B p.1)⁻¹ •
      (1 + t • (adMat A B p.1 + utK (p.2 - upVec A B p.1)) +
        t ^ 2 • (nTwo A B p.1 + adMat A B p.1 * utK (p.2 - upVec A B p.1)) +
        t ^ 3 • (nTwo A B p.1 * utK (p.2 - upVec A B p.1))) := by
  rw [chartMat, cMat, Prod.smul_fst, Prod.smul_snd, qPure_smul, nMat_one_add_pure_eq, adMat_smul, nTwo_smul,
    upVec_smul, ← smul_sub, utK_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  module

theorem lowMat_add (y y' : Fin 3 → K) : lowMat A B (y + y') = lowMat A B y + lowMat A B y' := by
  rw [lowMat_eq, lowMat_eq, lowMat_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem lowMat_smul (t : K) (y : Fin 3 → K) : lowMat A B (t • y) = t • lowMat A B y := by
  rw [lowMat_eq, lowMat_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

end Alg

/-! ### The strict derivative of the chart at $0$ -/

section Analysis

variable {𝕜 : Type*} [RCLike 𝕜] (A B : 𝕜)

theorem hasDerivAt_ratPoly (q c0 c1 c2 c3 : 𝕜) :
    HasDerivAt (fun t : 𝕜 => (1 + t ^ 2 * q)⁻¹ * (c0 + t * c1 + t ^ 2 * c2 + t ^ 3 * c3)) c1 0 := by
  have h1 : HasDerivAt (fun t : 𝕜 => 1 + t ^ 2 * q) (((2 : ℕ) * (0 : 𝕜) ^ (2 - 1)) * q) 0 :=
    ((hasDerivAt_pow 2 (0 : 𝕜)).mul_const q).const_add 1
  have h1' : HasDerivAt (fun t : 𝕜 => (1 + t ^ 2 * q)⁻¹)
      (-(((2 : ℕ) * (0 : 𝕜) ^ (2 - 1)) * q) / (1 + 0 ^ 2 * q) ^ 2) 0 := h1.inv (by simp)
  have h2 : HasDerivAt (fun t : 𝕜 => c0 + t * c1 + t ^ 2 * c2 + t ^ 3 * c3)
      (1 * c1 + ((2 : ℕ) * (0 : 𝕜) ^ (2 - 1)) * c2 + ((3 : ℕ) * (0 : 𝕜) ^ (3 - 1)) * c3) 0 :=
    ((((hasDerivAt_id (0 : 𝕜)).mul_const c1).const_add c0).add ((hasDerivAt_pow 2 (0 : 𝕜)).mul_const c2)).add
      ((hasDerivAt_pow 3 (0 : 𝕜)).mul_const c3)
  convert h1'.mul h2 using 1
  simp

/-- Column coordinates of a $3\times3$ matrix ($X_{ji} = M_{ij}$, as in `cols`). -/
def colsK (M : Matrix (Fin 3) (Fin 3) 𝕜) : Fin 3 → Fin 3 → 𝕜 := fun j i => M i j

/-- **The chart at the identity in column coordinates.** -/
def chartF (p : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) : Fin 3 → Fin 3 → 𝕜 := colsK (chartMat A B p)

/-- **The derivative of the chart at $0$**: $(y, w) \mapsto \operatorname{low}(\operatorname{ad}y) + U(w)$. -/
def chartDL : ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) →ₗ[𝕜] (Fin 3 → Fin 3 → 𝕜) where
  toFun p := colsK (lowMat A B p.1 + utK p.2)
  map_add' p q := by
    funext j i
    simp only [colsK, Prod.fst_add, Prod.snd_add, lowMat_add, utK_add, Matrix.add_apply, Pi.add_apply]
    ring
  map_smul' t p := by
    funext j i
    simp only [colsK, Prod.smul_fst, Prod.smul_snd, lowMat_smul, utK_smul, Matrix.add_apply, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hasDerivAt_chartF_line (p : (Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) :
    HasDerivAt (fun t : 𝕜 => chartF A B (t • p)) (chartDL A B p) 0 := by
  rw [hasDerivAt_pi]; intro j; rw [hasDerivAt_pi]; intro i
  have h := hasDerivAt_ratPoly (qPure A B p.1) ((1 : Matrix (Fin 3) (Fin 3) 𝕜) i j)
    ((adMat A B p.1 + utK (p.2 - upVec A B p.1)) i j)
    ((nTwo A B p.1 + adMat A B p.1 * utK (p.2 - upVec A B p.1)) i j)
    ((nTwo A B p.1 * utK (p.2 - upVec A B p.1)) i j)
  convert h using 1
  · funext t
    simp only [chartF, colsK, chartMat_smul, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  · simp only [chartDL, LinearMap.coe_mk, AddHom.coe_mk, colsK, lowMat, utK_sub, Matrix.add_apply,
      Matrix.sub_apply]
    ring


theorem contDiffAt_chartF : ContDiffAt 𝕜 ⊤ (chartF A B) 0 := by
  rw [contDiffAt_pi]; intro j; rw [contDiffAt_pi]; intro i
  simp only [chartF, colsK, chartMat, cMat, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_three, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
  simp [nMat, imv, Quat.pure, Pi.single_apply, utK, upVec, adMat_eq, qPure] <;>
  fun_prop (disch := simp)

theorem fderiv_chartF_zero : (fderiv 𝕜 (chartF A B) 0 : ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) →ₗ[𝕜] _) = chartDL A B := by
  refine LinearMap.ext fun p => ?_
  have hd : HasFDerivAt (chartF A B) (fderiv 𝕜 (chartF A B) 0) ((0 : 𝕜) • p) := by
    rw [zero_smul]
    exact ((contDiffAt_chartF A B).differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun r : 𝕜 => r • p) p 0 := by simpa using (hasDerivAt_id (0 : 𝕜)).smul_const p
  have h1 : HasDerivAt (fun r : 𝕜 => chartF A B (r • p)) (fderiv 𝕜 (chartF A B) 0 p) 0 := by
    simpa [Function.comp_def] using hd.comp_hasDerivAt (0 : 𝕜) hline
  exact h1.unique (hasDerivAt_chartF_line A B p)

/-- **The strict derivative of the chart at $0$.** -/
theorem hasStrictFDerivAt_chartF :
    HasStrictFDerivAt (chartF A B) (LinearMap.toContinuousLinearMap (chartDL A B)) 0 := by
  have h := (contDiffAt_chartF A B).hasStrictFDerivAt (by simp)
  convert h using 1
  refine ContinuousLinearMap.ext fun p => ?_
  have := congrArg (fun f : ((Fin 3 → 𝕜) × (UIdx 3 → 𝕜)) →ₗ[𝕜] _ => f p) (fderiv_chartF_zero A B)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this]; rfl

/-- **Coordinates on $M_3$** adapted to the chart: the strictly lower entries $(M_{21}, M_{20}, M_{10})$ and the upper
triangular entries $(M_{ij})_{i\le j}$ (column coordinates $X_{ji} = M_{ij}$). -/
def eMatL : (Fin 3 → Fin 3 → 𝕜) →ₗ[𝕜] (Fin 3 → 𝕜) × (UIdx 3 → 𝕜) where
  toFun X := (![X 1 2, X 0 2, X 0 1], fun p => X p.1.2 p.1.1)
  map_add' X Y := by ext i <;> [fin_cases i <;> simp; simp]
  map_smul' t X := by ext i <;> [fin_cases i <;> simp; simp]

/-- The diagonal part $y \mapsto (2y_0, -2y_1, -2Ay_2)$ of the derivative in these coordinates. -/
def dLow : (Fin 3 → 𝕜) →ₗ[𝕜] (Fin 3 → 𝕜) := Matrix.toLin' (Matrix.diagonal ![2, -2, -2 * A])

theorem eMatL_chartDL : eMatL ∘ₗ chartDL A B = LinearMap.prodMap (dLow A) LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  ext i
  · fin_cases i <;> simp [eMatL, chartDL, colsK, lowMat_eq, utK, dLow, Matrix.mulVec, dotProduct,
      Matrix.diagonal]
  · obtain ⟨⟨i, j⟩, hij⟩ := i
    simp only [eMatL, chartDL, colsK, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.prodMap_apply, LinearMap.id_apply, Matrix.add_apply, utK]
    rw [lowMat_eq]
    fin_cases i <;> fin_cases j <;> first | (simp at hij; done) | simp_all

theorem det_dLow : LinearMap.det (dLow A) = 8 * A := by
  rw [dLow, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]
  simp; ring

end Analysis

end QuadFormsKB.Tamagawa.Measure.Weil
