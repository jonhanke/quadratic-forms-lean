import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSplitR
import QuadFormsKB.Tamagawa.Measure.Weil.QuatUnits

/-!
# The map $\varphi_w$ at a real place with $E_w = \mathbb C$: matrices

**Layer:** one real place $w$ of $F$ with $d = d_w < 0$, so $E_w = \mathbb R(\sqrt d)\cong\mathbb C$ via $\delta\mapsto t$, $t\in\mathbb C$,
$t^2 = d$, $\operatorname{Re}t = 0$ (one complex place of $K$ over $w$); $D\otimes E_w = \mathbb H[\mathbb C,A,B]$ with $A, B$ real, and the
real structure $\sigma$ = coefficientwise complex conjugation (`conjQ`). For $X\in\mathbb H[\mathbb C,A,B]$ of reduced norm $1$:

* `MC X` $= T^{-1}\,(v\mapsto Xv\,\sigma(\bar X))\,T$ with $T = \mathrm{diag}(1,t,t,t)$ (the action of $X$ on
  $V_0 = \{y : \sigma(\bar y) = y\} = T(\mathbb R^4)$ in the coordinates of $V_0$) has **real** entries (`MC_eq_map`, via
  `MR X`);
* `MR` is multiplicative (`MR_mul`), preserves $Q_0 = \langle1,-Ad,-Bd,ABd\rangle$ (`MR_isometry`) and has determinant $1$
  (`det_MR`), i.e. $X\mapsto$ `MR X` is the map $\mathrm{SL}_1(D\otimes E_w)\to SO(Q_0)(\mathbb R)$ of the non-square model.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix Complex
open scoped ENNReal NNReal Quaternion ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Siegel QuadFormsKB.Tamagawa

variable {A B d : ℝ} {t : ℂ}

/-- **The real structure** $\sigma$: coefficientwise complex conjugation on $\mathbb H[\mathbb C,A,B]$, $A,B$ real. -/
def conjQ : ℍ[ℂ, (A : ℂ), (B : ℂ)] →+* ℍ[ℂ, (A : ℂ), (B : ℂ)] :=
  QuaternionAlgebra.mapRingHom (starRingEnd ℂ) (conj_ofReal A) (map_zero _) (conj_ofReal B)

@[simp] theorem conjQ_re (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : (conjQ x).re = conj x.re := rfl
@[simp] theorem conjQ_imI (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : (conjQ x).imI = conj x.imI := rfl
@[simp] theorem conjQ_imJ (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : (conjQ x).imJ = conj x.imJ := rfl
@[simp] theorem conjQ_imK (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : (conjQ x).imK = conj x.imK := rfl

theorem conjQ_star (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : conjQ (star x) = star (conjQ x) := by ext <;> simp

theorem conjQ_conjQ (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : conjQ (conjQ x) = x := by ext <;> simp

theorem nrd_conjQ (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : nrd (conjQ x) = conj (nrd x) := by
  simp [nrd, map_sub, map_add, map_mul, map_pow, conj_ofReal]

/-- $T = \mathrm{diag}(1,t,t,t)$ over $\mathbb C$. -/
def tMatN (t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, t, t, t]

/-- $T^{-1}$ over $\mathbb C$. -/
def tInvN (t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, t⁻¹, t⁻¹, t⁻¹]

theorem tMatN_mul_tInvC (ht0 : t ≠ 0) : tMatN t * tInvN t = 1 := by
  rw [tMatN, tInvN, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i
  fin_cases i <;> simp [ht0]

theorem tInvN_mul_tMatC (ht0 : t ≠ 0) : tInvN t * tMatN t = 1 := by
  rw [tMatN, tInvN, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i
  fin_cases i <;> simp [ht0]

/-- **The complex matrix** $T^{-1}(v\mapsto Xv\sigma(\bar X))T$. -/
def MC (t : ℂ) (X : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : Matrix (Fin 4) (Fin 4) ℂ :=
  tInvN t * sqMat X (conjQ (star X)) * tMatN t

theorem MC_mul (ht0 : t ≠ 0) (X Y : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : MC t (X * Y) = MC t X * MC t Y := by
  have h : MC t X * MC t Y = tInvN t * (sqMat X (conjQ (star X)) * (tMatN t * tInvN t) *
      sqMat Y (conjQ (star Y))) * tMatN t := by simp only [MC, Matrix.mul_assoc]
  rw [h, tMatN_mul_tInvC ht0, Matrix.mul_one, sqMat_mul, MC, star_mul, map_mul]

theorem MC_one (ht0 : t ≠ 0) : MC t (1 : ℍ[ℂ, (A : ℂ), (B : ℂ)]) = 1 := by
  rw [MC, star_one, map_one, sqMat_one_one, Matrix.mul_one, tInvN_mul_tMatC ht0]

/-! ### Realness -/

theorem conj_t (htre : t.re = 0) : conj t = -t := by
  apply Complex.ext <;> simp [htre]

theorem tMatN_mulVec (u : Fin 4 → ℂ) : tMatN t *ᵥ u = ![u 0, t * u 1, t * u 2, t * u 3] := by
  funext i; fin_cases i <;> simp [tMatN, Matrix.mulVec_diagonal]

theorem tInvN_mulVec (u : Fin 4 → ℂ) : tInvN t *ᵥ u = ![u 0, t⁻¹ * u 1, t⁻¹ * u 2, t⁻¹ * u 3] := by
  funext i; fin_cases i <;> simp [tInvN, Matrix.mulVec_diagonal]

/-- The points $T(v)$, $v$ real, are fixed by $y\mapsto\sigma(\bar y)$. -/
theorem conjQ_star_tvec (htre : t.re = 0) (v : Fin 4 → ℝ) :
    conjQ (star (vecQ (tMatN t *ᵥ (fun i => (v i : ℂ))) : ℍ[ℂ, (A : ℂ), (B : ℂ)])) =
      vecQ (tMatN t *ᵥ (fun i => (v i : ℂ))) := by
  rw [tMatN_mulVec]
  ext <;> simp [vecQ, conj_t htre]

theorem conjQ_star_conj (X Y : ℍ[ℂ, (A : ℂ), (B : ℂ)]) (hY : conjQ (star Y) = Y) :
    conjQ (star (X * Y * conjQ (star X))) = X * Y * conjQ (star X) := by
  rw [star_mul, star_mul, map_mul, map_mul, conjQ_star (conjQ (star X)), conjQ_conjQ, star_star, hY, mul_assoc]

/-- **`MC X` maps real vectors to real vectors.** -/
theorem MC_mulVec_im (htre : t.re = 0) (ht0 : t ≠ 0) (X : ℍ[ℂ, (A : ℂ), (B : ℂ)]) (v : Fin 4 → ℝ) (i : Fin 4) :
    (MC t X *ᵥ (fun i => (v i : ℂ))) i = (((MC t X *ᵥ (fun i => (v i : ℂ))) i).re : ℂ) := by
  set y := tMatN t *ᵥ (fun i => (v i : ℂ))
  set z := X * vecQ y * conjQ (star X)
  have hz : conjQ (star z) = z := conjQ_star_conj X _ (conjQ_star_tvec htre v)
  have e : MC t X *ᵥ (fun i => (v i : ℂ)) = tInvN t *ᵥ qVec z := by
    rw [MC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sqMat_mulVec]
  have h0 : conj z.re = z.re := by have := congrArg QuaternionAlgebra.re hz; simpa using this
  have h1 : conj z.imI = -z.imI := by
    have := congrArg QuaternionAlgebra.imI hz; simp at this; linear_combination -this
  have h2 : conj z.imJ = -z.imJ := by
    have := congrArg QuaternionAlgebra.imJ hz; simp at this; linear_combination -this
  have h3 : conj z.imK = -z.imK := by
    have := congrArg QuaternionAlgebra.imK hz; simp at this; linear_combination -this
  have hq : ∀ w : ℂ, conj w = -w → conj (t⁻¹ * w) = t⁻¹ * w := fun w hw => by
    rw [map_mul, map_inv₀, conj_t htre, hw, inv_neg, neg_mul_neg]
  rw [e, tInvN_mulVec]
  refine (Complex.conj_eq_iff_re.1 ?_).symm
  fin_cases i <;> simp [qVec, h0, hq _ h1, hq _ h2, hq _ h3]

/-- **The real matrix** `MR X` with `MC X = (MR X).map ofReal`. -/
def MR (t : ℂ) (X : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => (MC t X i j).re

theorem MC_eq_map (htre : t.re = 0) (ht0 : t ≠ 0) (X : ℍ[ℂ, (A : ℂ), (B : ℂ)]) :
    MC t X = (MR t X).map Complex.ofRealHom := by
  ext i j
  have h := MC_mulVec_im htre ht0 X (Pi.single j 1) i
  have e : (fun k => ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) k : ℂ)) = Pi.single j 1 := by
    funext k; by_cases hk : k = j <;> simp [Pi.single_apply, hk]
  rw [e, Matrix.mulVec_single_one] at h
  simpa [MR, Matrix.map_apply] using h

theorem map_ofReal_injective : Function.Injective (fun M : Matrix (Fin 4) (Fin 4) ℝ => M.map Complex.ofRealHom) :=
  fun M N h => by
    ext i j
    have := congrFun (congrFun h i) j
    simpa using this

theorem MR_mul (htre : t.re = 0) (ht0 : t ≠ 0) (X Y : ℍ[ℂ, (A : ℂ), (B : ℂ)]) :
    MR t (X * Y) = MR t X * MR t Y := by
  apply map_ofReal_injective
  simp only
  rw [Matrix.map_mul, ← MC_eq_map htre ht0, ← MC_eq_map htre ht0, ← MC_eq_map htre ht0, MC_mul ht0]

theorem MR_one (htre : t.re = 0) (ht0 : t ≠ 0) : MR t (1 : ℍ[ℂ, (A : ℂ), (B : ℂ)]) = 1 := by
  apply map_ofReal_injective
  simp only
  rw [← MC_eq_map htre ht0, MC_one ht0, Matrix.map_one _ (map_zero _) (map_one _)]

/-! ### Isometry and determinant -/

theorem sqMat_isometry_gen {K : Type*} [Field K] {A' B' : K} (x z : ℍ[K,A',B']) :
    (sqMat x z)ᵀ * nDiag A' B' * sqMat x z = (nrd x * nrd z) • nDiag A' B' := by
  rw [sqMat_eq_lmat_mul_rmat_gen, Matrix.transpose_mul]
  calc (rmat z)ᵀ * (lmat x)ᵀ * nDiag A' B' * (lmat x * rmat z)
      = (rmat z)ᵀ * ((lmat x)ᵀ * nDiag A' B' * lmat x) * rmat z := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [lmat_isometry, Matrix.mul_smul, Matrix.smul_mul, rmat_isometry, smul_smul, mul_comm]
where
  sqMat_eq_lmat_mul_rmat_gen (x z : ℍ[K,A',B']) : sqMat x z = lmat x * rmat z := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [sqMat_mulVec, ← Matrix.mulVec_mulVec, rmat_mulVec, lmat_mulVec, vecQ_qVec, mul_assoc]

theorem det_sqMat_gen {K : Type*} [Field K] {A' B' : K} (x z : ℍ[K,A',B']) :
    (sqMat x z).det = nrd x ^ 2 * nrd z ^ 2 := by
  rw [sqMat_isometry_gen.sqMat_eq_lmat_mul_rmat_gen, Matrix.det_mul, det_lmat, det_rmat]

/-- The diagonal matrix of $Q_0 = \langle1,-Ad,-Bd,ABd\rangle$. -/
def q0Diag (A B d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -(A * d), -(B * d), A * B * d]

theorem hessian_nsFormR_eq_q0 : (nsFormR A B d).hessian = (2 : ℝ) • q0Diag A B d := by
  rw [hessian_nsFormR, q0Diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> ring

theorem q0Diag_map (ht : t ^ 2 = (d : ℂ)) :
    (q0Diag A B d).map Complex.ofRealHom = (tMatN t)ᵀ * nDiag (A : ℂ) (B : ℂ) * tMatN t := by
  rw [q0Diag, tMatN, nDiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_map (map_zero _)]
  congr 1; funext i; fin_cases i <;> simp <;> rw [← ht] <;> ring

theorem tInvN_transpose : (tInvN t)ᵀ = tInvN t := Matrix.diagonal_transpose _

theorem tMatN_transpose : (tMatN t)ᵀ = tMatN t := Matrix.diagonal_transpose _

theorem MC_isometry (ht : t ^ 2 = (d : ℂ)) (ht0 : t ≠ 0) {X : ℍ[ℂ, (A : ℂ), (B : ℂ)]} (hX : nrd X = 1) :
    (MC t X)ᵀ * (q0Diag A B d).map Complex.ofRealHom * MC t X = (q0Diag A B d).map Complex.ofRealHom := by
  rw [q0Diag_map ht, MC, Matrix.transpose_mul, Matrix.transpose_mul, tInvN_transpose, tMatN_transpose]
  have hZ : nrd (conjQ (star X)) = 1 := by rw [nrd_conjQ, nrd_star, hX, map_one]
  calc tMatN t * ((sqMat X (conjQ (star X)))ᵀ * tInvN t) * (tMatN t * nDiag (A : ℂ) (B : ℂ) * tMatN t) *
        (tInvN t * sqMat X (conjQ (star X)) * tMatN t)
      = tMatN t * ((sqMat X (conjQ (star X)))ᵀ * (tInvN t * tMatN t) * nDiag (A : ℂ) (B : ℂ) *
          (tMatN t * tInvN t) * sqMat X (conjQ (star X))) * tMatN t := by simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [tInvN_mul_tMatC ht0, tMatN_mul_tInvC ht0, Matrix.mul_one, Matrix.mul_one, sqMat_isometry_gen, hX, hZ,
          mul_one, one_smul]

theorem MR_isometry (ht : t ^ 2 = (d : ℂ)) (htre : t.re = 0) (ht0 : t ≠ 0) {X : ℍ[ℂ, (A : ℂ), (B : ℂ)]}
    (hX : nrd X = 1) : (MR t X)ᵀ * (nsFormR A B d).hessian * MR t X = (nsFormR A B d).hessian := by
  rw [hessian_nsFormR_eq_q0, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  apply map_ofReal_injective
  simp only
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, ← MC_eq_map htre ht0, MC_isometry ht ht0 hX]

theorem det_MR (htre : t.re = 0) (ht0 : t ≠ 0) {X : ℍ[ℂ, (A : ℂ), (B : ℂ)]} (hX : nrd X = 1) :
    (MR t X).det = 1 := by
  apply Complex.ofReal_injective
  rw [show ((MR t X).det : ℂ) = Complex.ofRealHom (MR t X).det from rfl, RingHom.map_det,
    show Complex.ofRealHom.mapMatrix (MR t X) = (MR t X).map Complex.ofRealHom from rfl, ← MC_eq_map htre ht0, MC,
    Matrix.det_mul, Matrix.det_mul, det_sqMat_gen, hX, nrd_conjQ, nrd_star, hX, map_one]
  have h := congrArg Matrix.det (tInvN_mul_tMatC ht0)
  rw [Matrix.det_mul, Matrix.det_one] at h
  simp only [one_pow, mul_one, Complex.ofReal_one]
  exact h

/-! ### Real quaternions act by conjugation -/

/-- A real quaternion as a complex one. -/
def qC : ℍ[ℝ,A,B] →+* ℍ[ℂ, (A : ℂ), (B : ℂ)] :=
  QuaternionAlgebra.mapRingHom Complex.ofRealHom rfl (map_zero _) rfl

@[simp] theorem qC_re (x : ℍ[ℝ,A,B]) : (qC x).re = x.re := rfl
@[simp] theorem qC_imI (x : ℍ[ℝ,A,B]) : (qC x).imI = x.imI := rfl
@[simp] theorem qC_imJ (x : ℍ[ℝ,A,B]) : (qC x).imJ = x.imJ := rfl
@[simp] theorem qC_imK (x : ℍ[ℝ,A,B]) : (qC x).imK = x.imK := rfl

theorem conjQ_qC (x : ℍ[ℝ,A,B]) : conjQ (qC x) = qC x := by ext <;> simp

theorem star_qC (x : ℍ[ℝ,A,B]) : star (qC x) = qC (star x) := by ext <;> simp

theorem nrd_qC (x : ℍ[ℝ,A,B]) : nrd (qC x) = Complex.ofReal (nrd x) := by simp [nrd]

theorem qVec_qC (q : ℍ[ℝ,A,B]) : qVec (qC q) = fun i => ((qVec q i : ℝ) : ℂ) := by
  funext i; fin_cases i <;> rfl

theorem vecQ_single_C (j : Fin 4) :
    (vecQ (Pi.single j 1 : Fin 4 → ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) = qC (vecQ (Pi.single j 1 : Fin 4 → ℝ)) := by
  ext <;> fin_cases j <;> simp [vecQ]

theorem sqMat_qC (x y : ℍ[ℝ,A,B]) : sqMat (qC x) (qC y) = (sqMat x y).map Complex.ofRealHom := by
  ext i j
  simp only [sqMat, Matrix.of_apply, Matrix.map_apply]
  rw [vecQ_single_C, ← map_mul, ← map_mul, qVec_qC]
  rfl

theorem tInvN_corner_tMatC (ht0 : t ≠ 0) (C : Matrix (Fin 3) (Fin 3) ℂ) :
    tInvN t * cornerMat 1 C * tMatN t = cornerMat 1 C := by
  have h1 : tInvN t = cornerMat 1 (t⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
    rw [tInvN, show t⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal ![t⁻¹, t⁻¹, t⁻¹] by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal], cornerMat_diagonal']
    congr 1
  have h2 : tMatN t = cornerMat 1 (t • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
    rw [tMatN, show t • (1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal ![t, t, t] by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal], cornerMat_diagonal']
    congr 1
  rw [h1, h2, cornerMat_mul, cornerMat_mul, one_mul, one_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, mul_inv_cancel₀ ht0, one_smul]

/-- **A real quaternion $h$ of norm one acts by $\mathrm{diag}(1, c_h)$.** -/
theorem cornerMat_map (C : Matrix (Fin 3) (Fin 3) ℝ) :
    (cornerMat 1 C).map Complex.ofRealHom = cornerMat 1 (C.map Complex.ofRealHom) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem MR_qC (htre : t.re = 0) (ht0 : t ≠ 0) {h : ℍ[ℝ,A,B]} (hh : nrd h = 1) :
    MR t (qC h) = cornerMat 1 ((conjGL (unitOfNrdOne h hh) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  apply map_ofReal_injective
  simp only
  have hs : sqMat h (star h) = cornerMat 1 ((conjGL (unitOfNrdOne h hh) : GL (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) := sqMat_conj (unitOfNrdOne h hh)
  rw [← MC_eq_map htre ht0, MC, star_qC, conjQ_qC, sqMat_qC, hs, cornerMat_map, tInvN_corner_tMatC ht0]

/-! ### The Cayley section -/

/-- The quaternion $Y = T(y)$ for real $y$. -/
def yQ (t : ℂ) (y : Fin 4 → ℝ) : ℍ[ℂ, (A : ℂ), (B : ℂ)] := vecQ (tMatN t *ᵥ (fun i => (y i : ℂ)))

theorem nrd_yQ (ht : t ^ 2 = (d : ℂ)) (y : Fin 4 → ℝ) :
    nrd (yQ (A := A) (B := B) t y) = ((nsFormR A B d).eval y : ℂ) := by
  rw [eval_nsFormR, yQ, tMatN_mulVec]
  simp [nrd, vecQ]
  linear_combination (-(A : ℂ) * (y 1 : ℂ) ^ 2 - B * (y 2 : ℂ) ^ 2 + A * B * (y 3 : ℂ) ^ 2) * ht

theorem conjQ_star_yQ (htre : t.re = 0) (y : Fin 4 → ℝ) :
    conjQ (star (yQ (A := A) (B := B) t y)) = yQ t y := conjQ_star_tvec htre y

/-- $q^2 = 2\operatorname{Re}(q)\,q - \operatorname{nrd}(q)$. -/
theorem sq_eq_trace {K : Type*} [Field K] {A' B' : K} (q : ℍ[K,A',B']) :
    q * q = (2 * q.re) • q - ((nrd q : K) : ℍ[K,A',B']) := by
  ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub, QuaternionAlgebra.imJ_sub,
    QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe, smul_eq_mul, nrd] <;> ring

/-- **The Cayley point** $X(y) = (2(1+y_0))^{-1/2}(1 + T(y))$. -/
def cayX (t : ℂ) (y : Fin 4 → ℝ) : ℍ[ℂ, (A : ℂ), (B : ℂ)] :=
  (((2 * (1 + y 0)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (1 + yQ t y)

theorem yQ_re (y : Fin 4 → ℝ) : (yQ (A := A) (B := B) t y).re = (y 0 : ℂ) := by
  simp [yQ, tMatN_mulVec, vecQ]

theorem nrd_cayX (ht : t ^ 2 = (d : ℂ)) {y : Fin 4 → ℝ} (hy : (nsFormR A B d).eval y = 1) (hy0 : 0 < 1 + y 0) :
    nrd (cayX (A := A) (B := B) t y) = 1 := by
  have h1 : nrd (1 + yQ (A := A) (B := B) t y) = 2 * (1 + (y 0 : ℂ)) := by
    have := nrd_yQ (A := A) (B := B) ht y
    rw [hy] at this
    have e := sq_eq_trace (1 + yQ (A := A) (B := B) t y)
    simp only [nrd, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
      QuaternionAlgebra.imK_one] at this ⊢
    rw [← yQ_re (A := A) (B := B) (t := t)]
    simp only [Complex.ofReal_one] at this
    linear_combination this
  have hr : (0 : ℝ) < 2 * (1 + y 0) := by linarith
  rw [cayX, nrd_smul, h1, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  norm_num
  rw [show (2 : ℂ) * (1 + (y 0 : ℂ)) = ((2 * (1 + y 0) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
    Real.rpow_neg_one, inv_mul_cancel₀ hr.ne', Complex.ofReal_one]

theorem conjQ_star_cayX (htre : t.re = 0) (y : Fin 4 → ℝ) :
    conjQ (star (cayX (A := A) (B := B) t y)) = cayX t y := by
  ext <;> simp [cayX, yQ, tMatN_mulVec, vecQ, conj_t htre]

theorem cayX_sq (ht : t ^ 2 = (d : ℂ)) {y : Fin 4 → ℝ} (hy : (nsFormR A B d).eval y = 1) (hy0 : 0 < 1 + y 0) :
    cayX (A := A) (B := B) t y * cayX t y = yQ t y := by
  have hr : (0 : ℝ) < 2 * (1 + y 0) := by linarith
  have hn : nrd (1 + yQ (A := A) (B := B) t y) = 2 * (1 + (y 0 : ℂ)) := by
    have := nrd_cayX (A := A) (B := B) ht hy hy0
    rw [cayX, nrd_smul] at this
    have hc : ((((2 * (1 + y 0)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ 2 = ((2 * (1 + y 0) : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
        show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one, Complex.ofReal_inv]
    rw [hc] at this
    have h2 : ((2 * (1 + y 0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp at this
    push_cast at this ⊢
    linear_combination this
  have hsq := sq_eq_trace (1 + yQ (A := A) (B := B) t y)
  rw [hn, QuaternionAlgebra.re_add, QuaternionAlgebra.re_one, yQ_re] at hsq
  rw [cayX, smul_mul_smul_comm, hsq]
  have hc : ((((2 * (1 + y 0)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * ((((2 * (1 + y 0)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      ((2 * (1 + y 0) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hr, show (-(1 / 2 : ℝ)) + -(1 / 2) = -1 by norm_num,
      Real.rpow_neg_one, Complex.ofReal_inv]
  rw [hc]
  have h2 : ((2 * (1 + y 0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have key : ∀ c : ℂ, c • (1 + yQ (A := A) (B := B) t y) - ((c : ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) =
      c • yQ (A := A) (B := B) t y := fun c => by
    ext <;> simp [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
      QuaternionAlgebra.imK_coe]
  rw [key, show (2 * (1 + (y 0 : ℂ))) = ((2 * (1 + y 0) : ℝ) : ℂ) by push_cast; ring]
  rw [smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem e0C_eq : (fun i => ((e₀ : Fin 4 → ℝ) i : ℂ)) = (e₀ : Fin 4 → ℂ) := by
  funext i; fin_cases i <;> rfl

/-- **The Cayley point lies over $y$**: $\varphi(X(y))(e_0) = y$. -/
theorem MR_cayX_e0 (ht : t ^ 2 = (d : ℂ)) (htre : t.re = 0) (ht0 : t ≠ 0) {y : Fin 4 → ℝ}
    (hy : (nsFormR A B d).eval y = 1) (hy0 : 0 < 1 + y 0) :
    MR t (cayX (A := A) (B := B) t y) *ᵥ (e₀ : Fin 4 → ℝ) = y := by
  funext i
  apply Complex.ofReal_injective
  have e1 : ((MR t (cayX (A := A) (B := B) t y) *ᵥ (e₀ : Fin 4 → ℝ)) i : ℂ) =
      (MC t (cayX (A := A) (B := B) t y) *ᵥ (e₀ : Fin 4 → ℂ)) i := by
    rw [show ((MR t (cayX (A := A) (B := B) t y) *ᵥ (e₀ : Fin 4 → ℝ)) i : ℂ) =
      Complex.ofRealHom ((MR t (cayX (A := A) (B := B) t y) *ᵥ (e₀ : Fin 4 → ℝ)) i) from rfl,
      RingHom.map_mulVec, ← MC_eq_map htre ht0, show (Complex.ofRealHom ∘ (e₀ : Fin 4 → ℝ)) = e₀ from e0C_eq]
  rw [e1, MC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have he : (e₀ : Fin 4 → ℂ) = ![1, 0, 0, 0] := by funext k; fin_cases k <;> rfl
  have h1 : tMatN t *ᵥ (e₀ : Fin 4 → ℂ) = e₀ := by
    rw [he, tMatN_mulVec]; funext k; fin_cases k <;> simp
  rw [h1, sqMat_mulVec, vecQ_e₀, mul_one, conjQ_star_cayX htre, cayX_sq ht hy hy0, yQ, qVec_vecQ,
    Matrix.mulVec_mulVec, tInvN_mul_tMatC ht0, Matrix.one_mulVec]

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
