import QuadFormsKB.Tamagawa.Measure.Weil.GLPoisson
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropic

/-!
# The $g$-twisted Poisson formula on $V_{\mathbb A}$

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n$ variables, $Q = Q_0\otimes F$ with Hessian
$H = (\partial^2Q/\partial x_i\partial x_j)$ (so $B_Q(x,y) = x^{\mathsf T}Hy$), $G$ the standard Gaussian on $F_\infty^n$ (`gV`). This file
proves the named input `AdelicThetaPoisson` (TauTwoAnisotropic.lean) for the test functions
$$\Phi = G\otimes\mathbf 1_{\hat{\mathcal O}^n}\ (\texttt{gaussTest}),\qquad
  \hat\Phi(y) = \mu_f(\hat{\mathcal O}^n)\,\big(G\otimes\mathbf 1_{\hat{\mathfrak d}^{-1,n}}\big)(Hy)\ (\texttt{gaussTestHat}),$$
$\hat\Phi$ being the Fourier transform of $\Phi$ for the character $\psi(B_Q(x,y))$ and its self-dual measure ($\mu_f$ is
the self-dual measure of $\mathbb A_f$, so $\mu_f(\hat{\mathcal O}^n) = |d_F|^{-n/2}$):

**`adelicThetaPoisson_gauss`**: for $g\in SO(V)(\mathbb A)$, $z\in\mathbb A_F^\times$,
$$\|z\|^n\sum_{\xi\in F^n}\Phi(z\,g^{-1}\xi) = \sum_{\xi\in F^n}\hat\Phi(z^{-1}g^{-1}\xi).$$

*Proof.* The action of $g$ is a matrix $S(g)\in\mathrm{GL}_n(\mathbb A_F)$ (`soGL`, from the local matrices of
SOAdeleAction.lean) with $S^{\mathsf T}HS = H$ at every place (`soMat_transpose_hessian`) and $\|\det S\| = 1$. Put
$M = zS(g^{-1})$ and $M' = z^{-1}HS(g^{-1})H^{-1}$; then $M'^{\mathsf T}M = 1$ and $\|\det M\| = \|z\|^n$, so the
$\mathrm{GL}_n(\mathbb A_F)$-twisted Gaussian Poisson formula `glTheta_poisson_dual` (GLPoisson.lean) applies; the substitution
$\eta = H\xi$ on $F^n$ turns its right side into $\sum_\xi\hat\Phi(z^{-1}g^{-1}\xi)$.
-/

open MeasureTheory Set Matrix
open scoped ENNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Projections of adeles to the completions -/

variable (F) in
/-- The component at a real place $w$, a ring homomorphism $\mathbb A_F\to\mathbb R$. -/
def adProjR (w : {w : InfinitePlace F // w.IsReal}) : Adeles F →+* ℝ :=
  (Pi.evalRingHom (fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) w).comp
    ((RingHom.fst _ _).comp (RingHom.fst V AF))

variable (F) in
/-- The component at a complex place $w$, a ring homomorphism $\mathbb A_F\to\mathbb C$. -/
def adProjC (w : {w : InfinitePlace F // w.IsComplex}) : Adeles F →+* ℂ :=
  (Pi.evalRingHom (fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ) w).comp
    ((RingHom.snd _ _).comp (RingHom.fst V AF))

variable (F) in
/-- The component at a finite place $v$, a ring homomorphism $\mathbb A_F\to F_v$. -/
def adProjV (v : HeightOneSpectrum (𝓞 F)) : Adeles F →+* v.adicCompletion F := (evalAt v).comp (RingHom.snd V AF)

theorem adeles_ext_proj {x y : Adeles F} (hR : ∀ w, adProjR F w x = adProjR F w y) (hC : ∀ w, adProjC F w x = adProjC F w y)
    (hV : ∀ v, adProjV F v x = adProjV F v y) : x = y :=
  Prod.ext (Prod.ext (funext hR) (funext hC)) (Subtype.ext (funext hV))

theorem adeleMatrix_ext {ι : Type*} {A B : Matrix ι ι (Adeles F)} (hR : ∀ w, A.map (adProjR F w) = B.map (adProjR F w))
    (hC : ∀ w, A.map (adProjC F w) = B.map (adProjC F w)) (hV : ∀ v, A.map (adProjV F v) = B.map (adProjV F v)) : A = B :=
  Matrix.ext fun i j => adeles_ext_proj (fun w => congrFun (congrFun (hR w) i) j) (fun w => congrFun (congrFun (hC w) i) j)
    (fun v => congrFun (congrFun (hV v) i) j)

theorem adProjR_diagRing (w : {w : InfinitePlace F // w.IsReal}) :
    (adProjR F w).comp (diagRing F) = embedding_of_isReal w.2 := by
  ext x; exact mixedEmbedding_apply_isReal F x w

theorem adProjC_diagRing (w : {w : InfinitePlace F // w.IsComplex}) :
    (adProjC F w).comp (diagRing F) = w.1.embedding := by
  ext x; exact mixedEmbedding_apply_isComplex F x w

theorem adProjV_diagRing (v : HeightOneSpectrum (𝓞 F)) :
    (adProjV F v).comp (diagRing F) = algebraMap F (v.adicCompletion F) :=
  RingHom.ext fun _ => rfl

/-! ### The matrix of $g\in SO(V)(\mathbb A)$ -/

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The matrix of $g\in SO(V)(\mathbb A)$** over $\mathbb A_F$: its components are the local matrices `matR`, `matC`,
`matV` of SOAdeleAction.lean. -/
def soMat (g : SOAdele Q₀) : Matrix (Fin n) (Fin n) (Adeles F) := fun i j =>
  ((fun w => matR Q₀ g w i j, fun w => matC Q₀ g w i j),
    ⟨fun v => matV Q₀ g v i j, by
      filter_upwards [eventually_matV_integral Q₀ g] with v hv
      exact hv i j⟩)

theorem soMat_map_projR (g : SOAdele Q₀) (w) : (soMat Q₀ g).map (adProjR F w) = matR Q₀ g w := by
  ext i j; rfl

theorem soMat_map_projC (g : SOAdele Q₀) (w) : (soMat Q₀ g).map (adProjC F w) = matC Q₀ g w := by
  ext i j; rfl

theorem soMat_map_projV (g : SOAdele Q₀) (v) : (soMat Q₀ g).map (adProjV F v) = matV Q₀ g v := by
  ext i j; rfl

/-- **The action is the matrix**: $g\cdot y = S(g)\,y$. -/
theorem soMat_mulVec (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) : soMat Q₀ g *ᵥ y = g • y := by
  funext i
  refine adeles_ext_proj (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · rw [RingHom.map_mulVec, soMat_map_projR]; rfl
  · rw [RingHom.map_mulVec, soMat_map_projC]; rfl
  · rw [RingHom.map_mulVec, soMat_map_projV]; rfl

theorem soMat_mul (g h : SOAdele Q₀) : soMat Q₀ (g * h) = soMat Q₀ g * soMat Q₀ h :=
  adeleMatrix_ext (fun w => by rw [Matrix.map_mul, soMat_map_projR, soMat_map_projR, soMat_map_projR, matR_mul])
    (fun w => by rw [Matrix.map_mul, soMat_map_projC, soMat_map_projC, soMat_map_projC, matC_mul])
    (fun v => by rw [Matrix.map_mul, soMat_map_projV, soMat_map_projV, soMat_map_projV, matV_mul])

theorem soMat_one : soMat Q₀ 1 = 1 :=
  adeleMatrix_ext (fun w => by rw [soMat_map_projR, matR_one, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun w => by rw [soMat_map_projC, matC_one, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun v => by rw [soMat_map_projV, matV_one, Matrix.map_one _ (map_zero _) (map_one _)])

/-- $g\mapsto S(g)$ as an element of $\mathrm{GL}_n(\mathbb A_F)$. -/
def soGL (g : SOAdele Q₀) : GL (Fin n) (Adeles F) where
  val := soMat Q₀ g
  inv := soMat Q₀ g⁻¹
  val_inv := by rw [← soMat_mul, mul_inv_cancel, soMat_one]
  inv_val := by rw [← soMat_mul, inv_mul_cancel, soMat_one]

theorem coe_soGL (g : SOAdele Q₀) : (soGL Q₀ g : Matrix (Fin n) (Fin n) (Adeles F)) = soMat Q₀ g := rfl

/-! ### Orthogonality at every place -/

/-- The Hessian of $Q$ over $\mathbb A_F$. -/
def hessA : Matrix (Fin n) (Fin n) (Adeles F) := (QF).hessian.map (diagRing F)

theorem hessian_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Q : QuadForm R n) :
    (Q.map f).hessian = Q.hessian.map f := by
  simp [QuadForm.hessian, QuadForm.map, Matrix.map_add _ (map_add f), Matrix.transpose_map]

theorem hessA_map_projR (w : {w : InfinitePlace F // w.IsReal}) :
    (hessA Q₀).map (adProjR F w) = (QRe Q₀ w).hessian := by
  rw [hessA, Matrix.map_map, ← RingHom.coe_comp, adProjR_diagRing, ← hessian_map']

theorem hessA_map_projC (w : {w : InfinitePlace F // w.IsComplex}) :
    (hessA Q₀).map (adProjC F w) = (QCx Q₀ w).hessian := by
  rw [hessA, Matrix.map_map, ← RingHom.coe_comp, adProjC_diagRing, ← hessian_map']

theorem hessA_map_projV (v : HeightOneSpectrum (𝓞 F)) :
    (hessA Q₀).map (adProjV F v) = (QF).hessian.map (algebraMap F (v.adicCompletion F)) := by
  rw [hessA, Matrix.map_map, ← RingHom.coe_comp, adProjV_diagRing]

theorem matR_transpose_hessian (g : SOAdele Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    (matR Q₀ g w)ᵀ * (QRe Q₀ w).hessian * matR Q₀ g w = (QRe Q₀ w).hessian :=
  ((mem_soReal_iff _ _).mp (g.1.1 w).property).1

theorem matC_transpose_hessian (g : SOAdele Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    (matC Q₀ g w)ᵀ * (QCx Q₀ w).hessian * matC Q₀ g w = (QCx Q₀ w).hessian := by
  have h := (g.1.2 w).property.1
  change (matC Q₀ g w)ᵀ * gramC (QCx Q₀ w) * matC Q₀ g w = gramC (QCx Q₀ w) at h
  rw [gramC, Matrix.mul_smul, Matrix.smul_mul] at h
  exact smul_right_injective _ (by norm_num : (1 / 2 : ℂ) ≠ 0) h

theorem matV_transpose_hessian (g : SOAdele Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    (matV Q₀ g v)ᵀ * (QF).hessian.map (algebraMap F (v.adicCompletion F)) * matV Q₀ g v =
      (QF).hessian.map (algebraMap F (v.adicCompletion F)) :=
  (((g.2 : OAf QF) v : orthGroup QF (v.adicCompletion F))).2

/-- **$S(g)^{\mathsf T}HS(g) = H$** over $\mathbb A_F$. -/
theorem soMat_transpose_hessian (g : SOAdele Q₀) : (soMat Q₀ g)ᵀ * hessA Q₀ * soMat Q₀ g = hessA Q₀ :=
  adeleMatrix_ext
    (fun w => by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, soMat_map_projR, hessA_map_projR]
      exact matR_transpose_hessian Q₀ g w)
    (fun w => by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, soMat_map_projC, hessA_map_projC]
      exact matC_transpose_hessian Q₀ g w)
    (fun v => by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, soMat_map_projV, hessA_map_projV]
      exact matV_transpose_hessian Q₀ g v)

theorem hessA_transpose : (hessA Q₀)ᵀ = hessA Q₀ := by
  rw [hessA, ← Matrix.transpose_map, QuadForm.hessian, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-! ### The pair $M = zS(g^{-1})$, $M' = z^{-1}HS(g^{-1})H^{-1}$ -/

variable {Q₀}

theorem hessF_det_ne_zero (hQ : Q₀.Nondegenerate) : (QF).hessian.det ≠ 0 := by
  rw [hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hQ

/-- $H\in\mathrm{GL}_n(F)$. -/
def hessGLF (hQ : Q₀.Nondegenerate) : GL (Fin n) F :=
  GeneralLinearGroup.mkOfDetNeZero (QF).hessian (hessF_det_ne_zero hQ)

/-- $H\in\mathrm{GL}_n(\mathbb A_F)$. -/
def hessGL (hQ : Q₀.Nondegenerate) : GL (Fin n) (Adeles F) := GeneralLinearGroup.map (diagRing F) (hessGLF hQ)

theorem coe_hessGLF (hQ : Q₀.Nondegenerate) : (hessGLF hQ : Matrix (Fin n) (Fin n) F) = (QF).hessian := rfl

theorem coe_hessGL (hQ : Q₀.Nondegenerate) : (hessGL hQ : Matrix (Fin n) (Fin n) (Adeles F)) = hessA Q₀ := rfl

theorem coe_hessGL_inv_transpose (hQ : Q₀.Nondegenerate) :
    (((hessGL hQ)⁻¹ : GL (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F))ᵀ =
      ((hessGL hQ)⁻¹ : GL (Fin n) (Adeles F)) := by
  set Hm := ((hessGL hQ : GL (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F))
  set Hi := (((hessGL hQ)⁻¹ : GL (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F))
  have h1 : Hm * Hi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hT : Hmᵀ = Hm := hessA_transpose Q₀
  calc Hiᵀ = Hiᵀ * (Hm * Hi) := by rw [h1, Matrix.mul_one]
    _ = (Hm * Hi)ᵀ * Hi := by rw [Matrix.transpose_mul, hT, Matrix.mul_assoc]
    _ = Hi := by rw [h1, Matrix.transpose_one, Matrix.one_mul]

theorem scalar_mul_eq_smul (a : Adeles F) (A : Matrix (Fin n) (Fin n) (Adeles F)) :
    Matrix.scalar (Fin n) a * A = a • A := by
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

variable (Q₀) in
/-- $M = z\,S(g^{-1})$. -/
def pairM (g : SOAdele Q₀) (z : (Adeles F)ˣ) : GL (Fin n) (Adeles F) :=
  GeneralLinearGroup.scalar (Fin n) z * soGL Q₀ g⁻¹

/-- $M' = z^{-1}H\,S(g^{-1})H^{-1}$. -/
def pairM' (hQ : Q₀.Nondegenerate) (g : SOAdele Q₀) (z : (Adeles F)ˣ) : GL (Fin n) (Adeles F) :=
  GeneralLinearGroup.scalar (Fin n) z⁻¹ * hessGL hQ * soGL Q₀ g⁻¹ * (hessGL hQ)⁻¹

theorem coe_pairM (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    (pairM Q₀ g z : Matrix (Fin n) (Fin n) (Adeles F)) = (z : Adeles F) • soMat Q₀ g⁻¹ := by
  rw [pairM, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul, coe_soGL]

theorem coe_pairM' (hQ : Q₀.Nondegenerate) (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    (pairM' hQ g z : Matrix (Fin n) (Fin n) (Adeles F)) = ((z⁻¹ : (Adeles F)ˣ) : Adeles F) •
      (hessA Q₀ * soMat Q₀ g⁻¹ * (((hessGL hQ)⁻¹ : GL (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F))) := by
  rw [pairM', Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.mul_assoc,
    Matrix.mul_assoc, scalar_mul_eq_smul, coe_hessGL, coe_soGL, Matrix.mul_assoc]

/-- **$M'^{\mathsf T}M = 1$.** -/
theorem pairM'_transpose_mul (hQ : Q₀.Nondegenerate) (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    (pairM' hQ g z : Matrix (Fin n) (Fin n) (Adeles F))ᵀ * pairM Q₀ g z = 1 := by
  set Hi := (((hessGL hQ)⁻¹ : GL (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F))
  set S := soMat Q₀ g⁻¹
  have hHi : Hi * hessA Q₀ = 1 := by
    rw [← coe_hessGL hQ, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hz : ((z⁻¹ : (Adeles F)ˣ) : Adeles F) * (z : Adeles F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [coe_pairM', coe_pairM, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    coe_hessGL_inv_transpose, hessA_transpose, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, one_smul]
  rw [Matrix.mul_assoc, soMat_transpose_hessian, hHi]

/-- $\|\det S(g)\|_{\mathbb A} = 1$ (from $S^{\mathsf T}HS = H$). -/
theorem ideleNorm_det_soGL (hQ : Q₀.Nondegenerate) (g : SOAdele Q₀) :
    ideleNorm F (GeneralLinearGroup.det (soGL Q₀ g)) = 1 := by
  set u := GeneralLinearGroup.det (hessGL hQ)
  have h := congrArg Matrix.det (soMat_transpose_hessian Q₀ g)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← coe_hessGL hQ,
    ← GeneralLinearGroup.val_det_apply] at h
  have h2 : (GeneralLinearGroup.det (soGL Q₀ g)) ^ 2 = 1 := by
    refine Units.ext ?_
    have h3 : ((soMat Q₀ g).det ^ 2) * (u : Adeles F) = 1 * (u : Adeles F) := by
      calc ((soMat Q₀ g).det ^ 2) * (u : Adeles F) = (soMat Q₀ g).det * (u : Adeles F) * (soMat Q₀ g).det := by
            ring
        _ = 1 * (u : Adeles F) := by rw [h, one_mul]
    rw [Units.mul_left_inj] at h3
    rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, coe_soGL, h3, Units.val_one]
  have h4 := congrArg (fun x => (ideleNormHom F x : ℝ)) h2
  simp only [map_pow, NNReal.coe_pow, map_one, NNReal.coe_one, coe_ideleNormHom] at h4
  have hp := ideleNorm_pos (GeneralLinearGroup.det (soGL Q₀ g))
  nlinarith

theorem ideleNorm_det_pairM (hQ : Q₀.Nondegenerate) (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    ideleNorm F (GeneralLinearGroup.det (pairM Q₀ g z)) = ideleNorm F z ^ n := by
  rw [pairM, map_mul, ideleNorm_mul, ideleNorm_det_soGL hQ, mul_one, GeneralLinearGroup.det_scalar,
    Fintype.card_fin, ← coe_ideleNormHom, map_pow, NNReal.coe_pow, coe_ideleNormHom]

/-! ### The test functions and the twisted Poisson formula -/

variable (F n) in
/-- **The Gaussian test function** $\Phi = G\otimes\mathbf 1_{\hat{\mathcal O}^n}$ on $\mathbb A_F^n$, values in $[0,\infty]$. -/
def gaussTest (y : AdeleSpace F (Fin n)) : ℝ≥0∞ :=
  (OHatVec : Set (Fin n → AF)).indicator (fun _ => 1) (fun i => (y i).2) * ENNReal.ofReal (gV fun i => (y i).1)

variable (F n) in
/-- $G\otimes\mathbf 1_{\hat{\mathfrak d}^{-1,n}}$ on $\mathbb A_F^n$. -/
def gaussDualTest (y : AdeleSpace F (Fin n)) : ℝ≥0∞ :=
  {c : Fin n → AF | ∀ i, c i ∈ DHat}.indicator (fun _ => 1) (fun i => (y i).2) * ENNReal.ofReal (gV fun i => (y i).1)

variable (Q₀) in
/-- **The Fourier transform of $\Phi$** for $\psi(B_Q(x,y))$ and the self-dual measure:
$\hat\Phi(y) = \mu_f(\hat{\mathcal O}^n)\,(G\otimes\mathbf 1_{\hat{\mathfrak d}^{-1,n}})(Hy)$. -/
def gaussTestHat (y : AdeleSpace F (Fin n)) : ℝ≥0∞ := muFinVec F (Fin n) OHatVec * gaussDualTest F n (hessA Q₀ *ᵥ y)

theorem mulVec_diagVec_snd (M : GL (Fin n) (Adeles F)) (ξ : Fin n → F) :
    (fun i => ((M : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) ξ) i |>.2) =
      (glFin M : Matrix (Fin n) (Fin n) AF) *ᵥ jFin F (Fin n) ξ :=
  funext fun i => RingHom.map_mulVec (RingHom.snd V AF) (M : Matrix (Fin n) (Fin n) (Adeles F)) _ i

theorem mulVec_diagVec_fst (M : GL (Fin n) (Adeles F)) (ξ : Fin n → F) :
    (fun i => ((M : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) ξ) i |>.1) =
      (glInf M : Matrix (Fin n) (Fin n) V) *ᵥ jInf F (Fin n) ξ :=
  funext fun i => RingHom.map_mulVec (RingHom.fst V AF) (M : Matrix (Fin n) (Fin n) (Adeles F)) _ i

theorem gaussTest_mulVec (M : GL (Fin n) (Adeles F)) (ξ : Fin n → F) :
    gaussTest F n ((M : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) ξ) =
      ((OHatVecSub F (Fin n) : Set (Fin n → AF))).indicator (fun _ => (1 : ℝ≥0∞))
        ((glFin M : Matrix (Fin n) (Fin n) AF) *ᵥ jFin F (Fin n) ξ) *
        ENNReal.ofReal (gV ((glInf M : Matrix (Fin n) (Fin n) V) *ᵥ jInf F (Fin n) ξ)) := by
  rw [gaussTest, mulVec_diagVec_snd, mulVec_diagVec_fst, coe_OHatVecSub]

theorem gaussDualTest_mulVec (M : GL (Fin n) (Adeles F)) (ξ : Fin n → F) :
    gaussDualTest F n ((M : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) ξ) =
      ((DHatVecSub F (Fin n) : Set (Fin n → AF))).indicator (fun _ => (1 : ℝ≥0∞))
        ((glFin M : Matrix (Fin n) (Fin n) AF) *ᵥ jFin F (Fin n) ξ) *
        ENNReal.ofReal (gV ((glInf M : Matrix (Fin n) (Fin n) V) *ᵥ jInf F (Fin n) ξ)) := by
  rw [gaussDualTest, mulVec_diagVec_snd, mulVec_diagVec_fst, coe_DHatVecSub]

theorem units_smul_eq (z : (Adeles F)ˣ) (y : AdeleSpace F (Fin n)) : z • y = (z : Adeles F) • y := rfl

theorem pairM_mulVec (g : SOAdele Q₀) (z : (Adeles F)ˣ) (y : AdeleSpace F (Fin n)) :
    (pairM Q₀ g z : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ y = z • g⁻¹ • y := by
  rw [coe_pairM, Matrix.smul_mulVec, soMat_mulVec, units_smul_eq]

theorem diagVec_mulVec' (A : Matrix (Fin n) (Fin n) F) (ξ : Fin n → F) :
    diagVec F (Fin n) (A *ᵥ ξ) = A.map (diagRing F) *ᵥ diagVec F (Fin n) ξ := by
  funext i
  exact RingHom.map_mulVec (diagRing F) A ξ i

theorem pairM'_mulVec_hess (hQ : Q₀.Nondegenerate) (g : SOAdele Q₀) (z : (Adeles F)ˣ) (ξ : Fin n → F) :
    (pairM' hQ g z : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) ((hessGLF hQ : Matrix (Fin n) (Fin n) F) *ᵥ ξ) =
      hessA Q₀ *ᵥ (z⁻¹ • g⁻¹ • diagVec F (Fin n) ξ) := by
  have hHi : (((hessGL hQ)⁻¹ : GL (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F)) * hessA Q₀ = 1 := by
    rw [← coe_hessGL hQ, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [diagVec_mulVec', coe_hessGLF, ← hessA, coe_pairM', Matrix.smul_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, hHi, Matrix.mul_one, ← Matrix.mulVec_mulVec, soMat_mulVec, units_smul_eq,
    Matrix.mulVec_smul]

/-- The reindexing $\xi\mapsto H\xi$ of $F^n$. -/
def hessEquiv (hQ : Q₀.Nondegenerate) : (Fin n → F) ≃ (Fin n → F) where
  toFun ξ := (hessGLF hQ : Matrix (Fin n) (Fin n) F) *ᵥ ξ
  invFun ξ := (((hessGLF hQ)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ ξ
  left_inv ξ := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv ξ := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/-- **The $g$-twisted Poisson formula on $V_{\mathbb A}$** (Weil 1982, §4.5, p. 109, applied with the Poisson formula on
$X_{\mathbb A}$): for the Gaussian $\Phi$ = `gaussTest` and its transform $\hat\Phi$ = `gaussTestHat Q₀`, every
$g\in SO(V)(\mathbb A)$ and every idele $z$,
$$\|z\|^n\sum_{\xi\in F^n}\Phi(z\,g^{-1}\xi) = \sum_{\xi\in F^n}\hat\Phi(z^{-1}g^{-1}\xi).$$
This discharges the named input `AdelicThetaPoisson` for these test functions. -/
@[kb "weil1982" "§4.5, p. 108–109 (Poisson formula on X_A applied to Φ(z g⁻¹ ·)) [unverified page]"]
theorem adelicThetaPoisson_gauss (hQ : Q₀.Nondegenerate) :
    AdelicThetaPoisson Q₀ (gaussTest F n) (gaussTestHat Q₀) := by
  refine ⟨fun g z => ?_⟩
  have hL : ∑' ξ : Fin n → F, gaussTest F n (z • g⁻¹ • diagVec F (Fin n) ξ) =
      glTheta (pairM Q₀ g z) (OHatVecSub F (Fin n)) := by
    refine tsum_congr fun ξ => ?_
    rw [← pairM_mulVec, gaussTest_mulVec]
  have hR : ∑' ξ : Fin n → F, gaussTestHat Q₀ (z⁻¹ • g⁻¹ • diagVec F (Fin n) ξ) =
      muFinVec F (Fin n) OHatVec * glTheta (pairM' hQ g z) (DHatVecSub F (Fin n)) := by
    simp only [gaussTestHat]
    rw [ENNReal.tsum_mul_left, glTheta]
    congr 1
    conv_rhs => rw [← (hessEquiv hQ).tsum_eq]
    refine tsum_congr fun ξ => ?_
    rw [← gaussDualTest_mulVec]
    show _ = gaussDualTest F n ((pairM' hQ g z : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ
      diagVec F (Fin n) ((hessGLF hQ : Matrix (Fin n) (Fin n) F) *ᵥ ξ))
    rw [pairM'_mulVec_hess]
  rw [hL, hR, ← glTheta_poisson_dual (pairM'_transpose_mul hQ g z), ideleNorm_det_pairM hQ, Real.rpow_natCast]

end QuadFormsKB.Tamagawa.Measure.Weil
