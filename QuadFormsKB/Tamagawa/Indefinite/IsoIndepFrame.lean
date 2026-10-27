/-
# The norm-one measures under a change of frame data

**Layer:** number fields. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 2$ variables (any signature),
$T_0$ nondegenerate of rank $r$, $\Xi$ a rational frame of $T_0$, and two algebraic frame data `D D' : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)`
(complement matrices $C_D, C_{D'}$, complement forms $Q''_D, Q''_{D'}$, embeddings $\iota_D, \iota_{D'}$).

**Defines** `frameChange D D'` $= R\in GL_2(F)$, the lower block of $g_D^{-1}C_{D'}$ ($g_D = [\Xi\mid C_D]$).

**Proves**
* `cm_frameChange`: $C_{D'} = C_DR$ (the upper block of $g_D^{-1}C_{D'}$ vanishes: $\Xi^{\mathsf T}HC_{D'} = 0$, $H_{T_0}$ invertible);
  `hessian_frameChange`: $H''_{D'} = R^{\mathsf T}H''_DR$; `det_adaptedMat_frameChange`: $\det g_{D'} = \det g_D\det R$;
* `ιInf_frameChange`: $\iota_{D'}(R^{-1}hR) = \iota_D(h)$ at every infinite place;
* `isoFrameLamOf_frameChange`: $\lambda_{D'} = |\det R|_\infty^{3}\,\lambda_D$;
* **`isoStabMeasureOf_frameChange`**: for every isotropic vector $v'$ of $Q''_{D'}$, the norm-one stabilizer measures of
  $(D', v')$ are those of $(D, Rv')$ (Weil's measure transforms by $|\det R|^3_\infty$ under $h\mapsto R^{-1}hR$,
  `map_muArchTamSO_equivConjInf`, which cancels against $\lambda$; the characters correspond, `isoCharInf_equivConjInf`);
  hence `repMeasureIsoOf_frameChange`.
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoIndepLine
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchGlobalF

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames

/-! ### Matrix algebra -/

section Alg

theorem wittG_mul_eq {K : Type*} [CommRing K] {r n' m : ℕ} (Ξ' : Matrix (Fin (r + n')) (Fin r) K)
    (C : Matrix (Fin (r + n')) (Fin n') K) (Y : Matrix (Fin (r + n')) (Fin m) K) :
    wittG Ξ' C * Y = Ξ' * Matrix.of (fun i j => Y (Fin.castAdd n' i) j) +
      C * Matrix.of (fun i j => Y (Fin.natAdd r i) j) := by
  ext i k
  simp [wittG, Matrix.mul_apply, Fin.sum_univ_add]

theorem mul_right_cancel_of_det_ne_zero {K : Type*} [Field K] {m n : ℕ} {X Y : Matrix (Fin m) (Fin n) K}
    {N : Matrix (Fin n) (Fin n) K} (hN : N.det ≠ 0) (h : X * N = Y * N) : X = Y := by
  have h' := congrArg (· * N⁻¹) h
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hN), Matrix.mul_one] at h'
  exact h'

/-- **The local identity behind `ιInf_frameChange`**: if $M$ and $M'$ fix $\Xi_w$, $MC_w = C_wh_w$ and
$M'(C_wR_w) = (C_wR_w)(R_w^{-1}h_wR_w)$, and $[\Xi_w\mid C_w]$ is invertible, then $M' = M$. -/
theorem eq_of_frame_conj {K : Type*} [Field K] {r : ℕ} (M M' : Matrix (Fin (r + 2)) (Fin (r + 2)) K)
    (Ξw : Matrix (Fin (r + 2)) (Fin r) K) (Cw : Matrix (Fin (r + 2)) (Fin 2) K) (hw Rw Rinv : Matrix (Fin 2) (Fin 2) K)
    (hG : (wittG Ξw Cw).det ≠ 0) (hR : Rinv * Rw = 1) (h1 : M * Ξw = Ξw) (h1' : M' * Ξw = Ξw)
    (h2 : M * Cw = Cw * hw) (h2' : M' * (Cw * Rw) = Cw * Rw * (Rinv * hw * Rw)) : M' = M := by
  have hR' : Rw * Rinv = 1 := mul_eq_one_comm.1 hR
  have hRd : Rw.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have h3 : M' * Cw * Rw = M * Cw * Rw := by
    rw [Matrix.mul_assoc M', h2', h2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Rw Rinv, hR', Matrix.one_mul]
  have h4 : M' * Cw = M * Cw := mul_right_cancel_of_det_ne_zero hRd h3
  have h5 : M' * wittG Ξw Cw = M * wittG Ξw Cw := by
    rw [IsoAlg.mul_wittG, IsoAlg.mul_wittG, h1, h1', h4]
  exact mul_right_cancel_of_det_ne_zero hG h5

end Alg

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-! ### Orthogonality of the complement -/

section Orth

variable (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1))

theorem FrameTowerAlg.cmT_hess_Ξ : D.Cmᵀ * (QF).hessian * Ξ.1 = 0 := by
  ext b j
  exact congrFun (D.hΞC j) b

theorem FrameTowerAlg.ΞT_hess_cm : (Ξ.1)ᵀ * (QF).hessian * D.Cm = 0 := by
  have h := congrArg Matrix.transpose (D.cmT_hess_Ξ Q₀ hQ T₀ Ξ)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, witt_hessian_symm,
    Matrix.transpose_zero, ← Matrix.mul_assoc] at h

theorem ΞT_hess_Ξ : (Ξ.1)ᵀ * (QF).hessian * Ξ.1 = (T₀.map (algebraMap (𝓞 F) F)).hessian := by
  rw [← QuadForm.hessian_compMat, Ξ.2]

end Orth

/-! ### The change of complement basis -/

section Change

variable (D D' : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1))

/-- $g_D^{-1}C_{D'}$. -/
def frameChangeY : Matrix (Fin (r + 2)) (Fin 2) F :=
  (((IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT).g⁻¹ : GL (Fin (r + 2)) F) : Matrix (Fin (r + 2)) (Fin (r + 2)) F) * D'.Cm

/-- The lower $2\times2$ block of $g_D^{-1}C_{D'}$. -/
def frameChangeMat : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => frameChangeY Q₀ hQ T₀ hT Ξ D D' (Fin.natAdd r i) j

theorem cm_eq_frameChangeMat : D'.Cm = D.Cm * frameChangeMat Q₀ hQ T₀ hT Ξ D D' := by
  set A : Matrix (Fin r) (Fin 2) F := Matrix.of fun i j => frameChangeY Q₀ hQ T₀ hT Ξ D D' (Fin.castAdd 2 i) j
    with hA
  have hgY : ((IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT).g : Matrix (Fin (r + 2)) (Fin (r + 2)) F) *
      frameChangeY Q₀ hQ T₀ hT Ξ D D' = D'.Cm := by
    rw [frameChangeY, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hsplit : D'.Cm = Ξ.1 * A + D.Cm * frameChangeMat Q₀ hQ T₀ hT Ξ D D' := by
    conv_lhs => rw [← hgY]
    rw [IsoAlg.towerAdapted_g_val, IsoAlg.adaptedMat_eq, wittG_mul_eq]
    rfl
  have hA0 : A = 0 := by
    have h0 := D'.ΞT_hess_cm Q₀ hQ T₀ Ξ
    rw [hsplit] at h0
    simp only [Matrix.mul_add, ← Matrix.mul_assoc] at h0
    rw [D.ΞT_hess_cm Q₀ hQ T₀ Ξ, Matrix.zero_mul, add_zero, ΞT_hess_Ξ] at h0
    have hT' := witt_nd T₀ hT
    unfold QuadForm.Nondegenerate at hT'
    calc A = ((T₀.map (algebraMap (𝓞 F) F)).hessian)⁻¹ * ((T₀.map (algebraMap (𝓞 F) F)).hessian * A) :=
          (Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 hT')).symm
      _ = 0 := by rw [h0, Matrix.mul_zero]
  rw [hsplit, hA0, Matrix.mul_zero, zero_add]

theorem hessian_frameChangeMat : (D'.Q''.map (algebraMap (𝓞 F) F)).hessian =
    (frameChangeMat Q₀ hQ T₀ hT Ξ D D')ᵀ * (D.Q''.map (algebraMap (𝓞 F) F)).hessian *
      frameChangeMat Q₀ hQ T₀ hT Ξ D D' := by
  rw [← D'.hCH, ← D.hCH, cm_eq_frameChangeMat Q₀ hQ T₀ hT Ξ D D', Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem det_frameChangeMat_ne_zero : (frameChangeMat Q₀ hQ T₀ hT Ξ D D').det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hessian_frameChangeMat Q₀ hQ T₀ hT Ξ D D')
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at h
  have hd := witt_nd _ D'.hQ''
  unfold QuadForm.Nondegenerate at hd
  exact hd h

/-- **The change of complement basis** $R\in GL_2(F)$ from the frame data `D` to `D'`: $C_{D'} = C_DR$. -/
def frameChange : GL (Fin 2) F :=
  Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.2 (det_frameChangeMat_ne_zero Q₀ hQ T₀ hT Ξ D D'))

theorem frameChange_val :
    ((frameChange Q₀ hQ T₀ hT Ξ D D' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = frameChangeMat Q₀ hQ T₀ hT Ξ D D' :=
  rfl

/-- $C_{D'} = C_DR$. -/
theorem cm_frameChange :
    D'.Cm = D.Cm * ((frameChange Q₀ hQ T₀ hT Ξ D D' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  cm_eq_frameChangeMat Q₀ hQ T₀ hT Ξ D D'

/-- $H''_{D'} = R^{\mathsf T}H''_DR$. -/
theorem hessian_frameChange : (D'.Q''.map (algebraMap (𝓞 F) F)).hessian =
    ((frameChange Q₀ hQ T₀ hT Ξ D D' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *
      (D.Q''.map (algebraMap (𝓞 F) F)).hessian *
      ((frameChange Q₀ hQ T₀ hT Ξ D D' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  hessian_frameChangeMat Q₀ hQ T₀ hT Ξ D D'

/-- $\det g_{D'} = \det g_D\det R$. -/
theorem det_adaptedMat_frameChange :
    (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D' hT).g.val.det =
      (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det * (frameChangeMat Q₀ hQ T₀ hT Ξ D D').det := by
  rw [IsoAlg.towerAdapted_g_val, IsoAlg.towerAdapted_g_val, IsoAlg.adaptedMat_eq, IsoAlg.adaptedMat_eq,
    cm_eq_frameChangeMat Q₀ hQ T₀ hT Ξ D D', ← IsoAlg.wittG_mul_blockMat, Matrix.det_mul, det_blockMat_diag,
    Matrix.det_one, one_mul]

/-! ### The embeddings at infinity -/

/-- $\iota(h)$ fixes $\Xi$ at a real place. -/
theorem FrameTowerAlg.matR_ι_mul_Ξ (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)) (h : SOAdele D.Q'')
    (w : {w : InfinitePlace F // w.IsReal}) :
    matR Q₀ (MonoidHom.prodMap D.ιInf D.ιFin h) w * Ξ.1.map (σR w) = Ξ.1.map (σR w) := by
  have e := D.fix h
  have hd : ∀ c : F, (diag F c).1.1 w = σR w c := fun c => mixedEmbedding.mixedEmbedding_apply_isReal F c w
  refine Matrix.ext fun i j => ?_
  have h1 : (matR Q₀ (MonoidHom.prodMap D.ιInf D.ιFin h) w *ᵥ fun k => (diag F (Ξ.1 k j)).1.1 w) i =
      (diag F (Ξ.1 i j)).1.1 w :=
    congrArg (fun y => (y j i).1.1 w) e
  simpa only [hd, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

/-- $\iota(h)$ fixes $\Xi$ at a complex place. -/
theorem FrameTowerAlg.matC_ι_mul_Ξ (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)) (h : SOAdele D.Q'')
    (w : {w : InfinitePlace F // w.IsComplex}) :
    matC Q₀ (MonoidHom.prodMap D.ιInf D.ιFin h) w * Ξ.1.map (σC w) = Ξ.1.map (σC w) := by
  have e := D.fix h
  have hd : ∀ c : F, (diag F c).1.2 w = σC w c := fun c => mixedEmbedding.mixedEmbedding_apply_isComplex F c w
  refine Matrix.ext fun i j => ?_
  have h1 : (matC Q₀ (MonoidHom.prodMap D.ιInf D.ιFin h) w *ᵥ fun k => (diag F (Ξ.1 k j)).1.2 w) i =
      (diag F (Ξ.1 i j)).1.2 w :=
    congrArg (fun y => (y j i).1.2 w) e
  simpa only [hd, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

include hT in
theorem det_map_adaptedMat_ne_zero {K : Type*} [Field K] (σ : F →+* K) :
    (wittG (Ξ.1.map σ) (D.Cm.map σ)).det ≠ 0 := by
  rw [← IsoAlg.map_wittG, ← IsoAlg.adaptedMat_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero σ).2 ((isUnit_iff_ne_zero).1 (IsoAlg.isUnit_det_adaptedMat Q₀ hQ T₀ Ξ D hT))

/-- **The embeddings of two frame data differ by the change of basis**: $\iota_{D'}(R^{-1}hR) = \iota_D(h)$. -/
theorem ιInf_frameChange (h : GInfSO D.Q'') :
    D'.ιInf (equivConjInf (frameChange Q₀ hQ T₀ hT Ξ D D') (hessian_frameChange Q₀ hQ T₀ hT Ξ D D') h) =
      D.ιInf h := by
  set R := frameChange Q₀ hQ T₀ hT Ξ D D' with hRdef
  set x := equivConjInf R (hessian_frameChange Q₀ hQ T₀ hT Ξ D D') h with hx
  have hC := cm_frameChange Q₀ hQ T₀ hT Ξ D D'
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · refine Subtype.ext (Units.ext ?_)
    change matR Q₀ (MonoidHom.prodMap D'.ιInf D'.ιFin ((x, 1) : SOAdele D'.Q'')) w =
      matR Q₀ (MonoidHom.prodMap D.ιInf D.ιFin ((h, 1) : SOAdele D.Q'')) w
    have h2' := D'.hCR ((x, 1) : SOAdele D'.Q'') w
    have hxw : matR D'.Q'' ((x, 1) : SOAdele D'.Q'') w =
        (((Matrix.GeneralLinearGroup.map (σR w) R)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
          matR D.Q'' ((h, 1) : SOAdele D.Q'') w *
          ((Matrix.GeneralLinearGroup.map (σR w) R : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hx]
      rfl
    rw [hC, Matrix.map_mul, hxw] at h2'
    refine eq_of_frame_conj _ _ (Ξ.1.map (σR w)) (D.Cm.map (σR w)) (matR D.Q'' ((h, 1) : SOAdele D.Q'') w)
      ((Matrix.GeneralLinearGroup.map (σR w) R : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      (((Matrix.GeneralLinearGroup.map (σR w) R)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      (det_map_adaptedMat_ne_zero Q₀ hQ T₀ hT Ξ D (σR w))
      (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
      (D.matR_ι_mul_Ξ Q₀ hQ T₀ Ξ _ w) (D'.matR_ι_mul_Ξ Q₀ hQ T₀ Ξ _ w) (D.hCR ((h, 1) : SOAdele D.Q'') w) h2'
  · refine Subtype.ext (Units.ext ?_)
    change matC Q₀ (MonoidHom.prodMap D'.ιInf D'.ιFin ((x, 1) : SOAdele D'.Q'')) w =
      matC Q₀ (MonoidHom.prodMap D.ιInf D.ιFin ((h, 1) : SOAdele D.Q'')) w
    have h2' := D'.hCC ((x, 1) : SOAdele D'.Q'') w
    have hxw : matC D'.Q'' ((x, 1) : SOAdele D'.Q'') w =
        (((Matrix.GeneralLinearGroup.map (σC w) R)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
          matC D.Q'' ((h, 1) : SOAdele D.Q'') w *
          ((Matrix.GeneralLinearGroup.map (σC w) R : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hx]
      rfl
    rw [hC, Matrix.map_mul, hxw] at h2'
    refine eq_of_frame_conj _ _ (Ξ.1.map (σC w)) (D.Cm.map (σC w)) (matC D.Q'' ((h, 1) : SOAdele D.Q'') w)
      ((Matrix.GeneralLinearGroup.map (σC w) R : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      (((Matrix.GeneralLinearGroup.map (σC w) R)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      (det_map_adaptedMat_ne_zero Q₀ hQ T₀ hT Ξ D (σC w))
      (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
      (D.matC_ι_mul_Ξ Q₀ hQ T₀ Ξ _ w) (D'.matC_ι_mul_Ξ Q₀ hQ T₀ Ξ _ w) (D.hCC ((h, 1) : SOAdele D.Q'') w) h2'

/-! ### The scales -/

open Classical in
/-- $\prod_{w\ \mathrm{real}}|\sigma_wx|^k\prod_{w\ \mathrm{complex}}\|\sigma_wx\|^{2k} = \prod_{w\mid\infty}w(x)^{k\,m_w}$. -/
theorem prod_places_pow (x : F) (k : ℕ) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w x| ^ k) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w x‖ ^ (2 * k)) =
      ∏ w : InfinitePlace F, w x ^ (k * w.mult) := by
  rw [← sim_prod_places (fun w => w x ^ (k * w.mult))]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal w, mul_one, ← Real.norm_eq_abs, norm_embedding_of_isReal]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex w, norm_embedding_eq, mul_comm k 2]

open Classical in
/-- **The scales of two frame data**: $\lambda_{D'} = |\det R|_\infty^{3}\,\lambda_D$. -/
theorem isoFrameLamOf_frameChange :
    isoFrameLamOf Q₀ hQ T₀ hT Ξ D' =
      ENNReal.ofReal (∏ w : InfinitePlace F,
          w ((frameChange Q₀ hQ T₀ hT Ξ D D' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ^ ((2 + 1) * w.mult)) *
        isoFrameLamOf Q₀ hQ T₀ hT Ξ D := by
  unfold isoFrameLamOf
  rw [det_adaptedMat_frameChange Q₀ hQ T₀ hT Ξ D D', frameChange_val,
    ← prod_places_pow (frameChangeMat Q₀ hQ T₀ hT Ξ D D').det (2 + 1),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [map_mul, abs_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

/-! ### The norm-one stabilizer measures -/

theorem isoNormInf_vec_congr {Q : QuadForm (𝓞 F) 2} {hQ' : Q.Nondegenerate} {e e' : Fin 2 → F}
    (he : IsIsoVec Q e) (he' : IsIsoVec Q e') (h : e = e') (a : GInfSO Q) :
    isoNormInf Q hQ' he a = isoNormInf Q hQ' he' a := by
  subst h; rfl

/-- The isotropic vector $Rv'$ of $Q''_D$ attached to an isotropic vector $v'$ of $Q''_{D'}$. -/
theorem isIsoVec_frameChange {v' : Fin 2 → F} (hv' : IsIsoVec D'.Q'' v') :
    IsIsoVec D.Q'' (((frameChange Q₀ hQ T₀ hT Ξ D D' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v') := by
  set R := frameChange Q₀ hQ T₀ hT Ξ D D'
  refine ⟨fun h0 => hv'.1 ?_, ?_⟩
  · have := congrArg (fun x => ((R⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) h0
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · have h2 := (qF_eq_zero_iff_hessian D'.Q'' v').1 hv'.2
    rw [hessian_frameChange Q₀ hQ T₀ hT Ξ D D', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at h2
    exact (qF_eq_zero_iff_hessian D.Q'' _).2 h2

theorem inv_frameChange_mulVec (v' : Fin 2 → F) :
    (((frameChange Q₀ hQ T₀ hT Ξ D D')⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
      (((frameChange Q₀ hQ T₀ hT Ξ D D' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v') = v' := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/-- The shells correspond under $h\mapsto R^{-1}hR$. -/
theorem preimage_isoShellInf_frameChange {v' : Fin 2 → F} (hv' : IsIsoVec D'.Q'' v') :
    equivConjInf (frameChange Q₀ hQ T₀ hT Ξ D D') (hessian_frameChange Q₀ hQ T₀ hT Ξ D D') ⁻¹'
        isoShellInf D'.Q'' D'.hQ'' hv' =
      isoShellInf D.Q'' D.hQ'' (isIsoVec_frameChange Q₀ hQ T₀ hT Ξ D D' hv') := by
  ext a
  have hn : isoNormInf D'.Q'' D'.hQ'' hv'
      (equivConjInf (frameChange Q₀ hQ T₀ hT Ξ D D') (hessian_frameChange Q₀ hQ T₀ hT Ξ D D') a) =
      isoNormInf D.Q'' D.hQ'' (isIsoVec_frameChange Q₀ hQ T₀ hT Ξ D D' hv') a := by
    rw [isoNormInf_vec_congr hv' (isIsoVec_equivF _ (hessian_frameChange Q₀ hQ T₀ hT Ξ D D')
      (isIsoVec_frameChange Q₀ hQ T₀ hT Ξ D D' hv')) (inv_frameChange_mulVec Q₀ hQ T₀ hT Ξ D D' v').symm]
    exact isoNormInf_eq_of_isoCharInf (isoCharInf_equivConjInf _ _ D.hQ'' D'.hQ'' _ a)
  simp only [isoShellInf, Set.mem_preimage, hn]

/-- **Weil's measure on the shell under the change of frame data**: the norm-one stabilizer measure of $(D, Rv')$ at $\Xi$,
carried by $h\mapsto R^{-1}hR$, is that of $(D', v')$. -/
theorem map_isoStabBaseOf_frameChange {v' : Fin 2 → F} (hv' : IsIsoVec D'.Q'' v') :
    (isoStabBaseOf Q₀ hQ T₀ hT Ξ D (isIsoVec_frameChange Q₀ hQ T₀ hT Ξ D D' hv')).map
        (equivConjInf (frameChange Q₀ hQ T₀ hT Ξ D D') (hessian_frameChange Q₀ hQ T₀ hT Ξ D D')) =
      isoStabBaseOf Q₀ hQ T₀ hT Ξ D' hv' := by
  set c := equivConjInf (frameChange Q₀ hQ T₀ hT Ξ D D') (hessian_frameChange Q₀ hQ T₀ hT Ξ D D') with hc
  have hcm : Measurable c := c.continuous.measurable
  unfold isoStabBaseOf
  rw [Measure.map_smul, ← preimage_isoShellInf_frameChange Q₀ hQ T₀ hT Ξ D D' hv',
    ← Measure.restrict_map hcm (measurableSet_isoShellInf D'.Q'' D'.hQ'' hv'),
    map_muArchTamSO_equivConjInf _ _ D.hQ'' D'.hQ'', Measure.restrict_smul, smul_smul,
    isoFrameLamOf_frameChange Q₀ hQ T₀ hT Ξ D D', mul_comm]
  exact hcm.aemeasurable

/-- **Changing the frame data changes only the isotropic vector**: for every isotropic vector $v'$ of $Q''_{D'}$, the
norm-one stabilizer measures of $(D', v')$ are those of $(D, Rv')$, $R$ = `frameChange D D'`. -/
theorem isoStabMeasureOf_frameChange {v' : Fin 2 → F} (hv' : IsIsoVec D'.Q'' v') :
    isoStabMeasureOf Q₀ hQ T₀ hT Ξ D' hv' =
      isoStabMeasureOf Q₀ hQ T₀ hT Ξ D (isIsoVec_frameChange Q₀ hQ T₀ hT Ξ D D' hv') := by
  funext X
  unfold isoStabMeasureOf
  split_ifs with hX
  · set c := equivConjInf (frameChange Q₀ hQ T₀ hT Ξ D D') (hessian_frameChange Q₀ hQ T₀ hT Ξ D D') with hc
    have hcm : Measurable (⇑(equivConjInf (frameChange Q₀ hQ T₀ hT Ξ D D')
        (hessian_frameChange Q₀ hQ T₀ hT Ξ D D'))) := c.continuous.measurable
    rw [← map_isoStabBaseOf_frameChange Q₀ hQ T₀ hT Ξ D D' hv',
      Measure.map_map (measurable_isoConjOf Q₀ hQ T₀ Ξ D' _ _) hcm]
    congr 1
    funext h
    apply Subtype.ext
    show hX.choose * D'.ιInf (c h) * hX.choose⁻¹ = hX.choose * D.ιInf h * hX.choose⁻¹
    rw [hc, ιInf_frameChange Q₀ hQ T₀ hT Ξ D D' h]
  · rfl

/-- **The measure of representations under a change of frame data**: `repMeasureIsoOf D' v'` is
`repMeasureIsoOf D (R v')`. -/
theorem repMeasureIsoOf_frameChange {v' : Fin 2 → F} (hv' : IsIsoVec D'.Q'' v') (i : DC Q₀) :
    repMeasureIsoOf Q₀ hQ T₀ hT Ξ D' hv' i =
      repMeasureIsoOf Q₀ hQ T₀ hT Ξ D (isIsoVec_frameChange Q₀ hQ T₀ hT Ξ D D' hv') i := by
  unfold repMeasureIsoOf
  rw [isoStabMeasureOf_frameChange Q₀ hQ T₀ hT Ξ D D' hv']

end Change

end QuadFormsKB.Tamagawa.Indefinite
