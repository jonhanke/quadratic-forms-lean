/-
# Weil's measure of the integral adelic frames: auxiliary lemmas

Helper file for `FrameDensities.lean`: the adapted frame $g = [\Xi\mid C]$ of a frame tower, its local components,
the dictionary between $SO(\hat L)$-orbits of integral finite-adelic frames and families of local orbits, and the
measures of the orbit stabilizers.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameSiegelReduce
import QuadFormsKB.Tamagawa.Indefinite.FrameLocalSO
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereConst

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}
  (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTower Q₀ hQ n' (cols Ξ.1))

/-- The matrix $[\Xi\mid C]$ of the frame and the complement. -/
def adaptedMat : Matrix (Fin (r + n')) (Fin (r + n')) F :=
  Matrix.of fun i j => Fin.addCases (fun a => Ξ.1 i a) (fun b => D.Cm i b) j

theorem adaptedMat_eq : adaptedMat Q₀ hQ T₀ Ξ D = wittG Ξ.1 D.Cm := rfl

theorem gram_adaptedMat : (adaptedMat Q₀ hQ T₀ Ξ D)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian *
    adaptedMat Q₀ hQ T₀ Ξ D = (blockForm (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F))).hessian := by
  have hΞ : (Ξ.1)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * Ξ.1 = (T₀.map (algebraMap (𝓞 F) F)).hessian := by
    rw [← QuadForm.hessian_compMat, Ξ.2]
  rw [adaptedMat_eq, wittG_gram _ (witt_hessian_symm _) Ξ.1 D.Cm D.hΞC, hessian_blockForm, D.hCH, hΞ]

/-- $Q_0\circ[\Xi\mid C] = T_0\perp Q''$. -/
theorem compMat_adaptedMat : (Q₀.map (algebraMap (𝓞 F) F)).compMat (adaptedMat Q₀ hQ T₀ Ξ D) =
    blockForm (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F)) := by
  apply witt_eq_of_hessian_eq
  rw [QuadForm.hessian_compMat]
  exact gram_adaptedMat Q₀ hQ T₀ Ξ D

theorem isUnit_det_adaptedMat (hT : T₀.Nondegenerate) : IsUnit (adaptedMat Q₀ hQ T₀ Ξ D).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hdetB : (blockForm (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F))).hessian.det ≠ 0 := by
    rw [det_hessian_blockForm]; exact mul_ne_zero (witt_nd T₀ hT) (witt_nd _ D.hQ'')
  apply hdetB
  rw [← gram_adaptedMat Q₀ hQ T₀ Ξ D, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; ring

/-- **The adapted frame of the tower**: $g = [\Xi\mid C]$, $Q_0\circ g = T_0\perp Q''$. -/
abbrev towerAdapted (hT : T₀.Nondegenerate) :
    AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)) where
  g := Matrix.nonsingInvUnit _ (isUnit_det_adaptedMat Q₀ hQ T₀ Ξ D hT)
  Q' := D.Q''
  compMat_eq := compMat_adaptedMat Q₀ hQ T₀ Ξ D

/-- The local factor $\beta_\mathfrak p(L,T_0)\,|\det g|_\mathfrak p^{n'+1}\,|\det H_{T_0}|_\mathfrak p^{-n'}$. -/
def frameLocFactor (hT : T₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  NF.localDensityForm v Q₀ T₀ * ‖σV v (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det‖ ^ (n' + 1) /
    ‖σV v (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n'

theorem towerAdapted_g_val (hT : T₀.Nondegenerate) :
    (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val = adaptedMat Q₀ hQ T₀ Ξ D := rfl

/-! ### Block matrix algebra -/

theorem wittG_mul_blockMat {K : Type*} [CommRing K] (Ξ' : Matrix (Fin (r + n')) (Fin r) K)
    (C : Matrix (Fin (r + n')) (Fin n') K) (Dm : Matrix (Fin n') (Fin n') K) :
    wittG Ξ' C * blockMat (1 : Matrix (Fin r) (Fin r) K) 0 0 Dm = wittG Ξ' (C * Dm) := by
  ext i j
  induction j using Fin.addCases with
  | left a => simp [wittG, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]
  | right b => simp [wittG, Matrix.mul_apply, Fin.sum_univ_add]

theorem mul_wittG {K : Type*} [CommRing K] (M : Matrix (Fin (r + n')) (Fin (r + n')) K)
    (Ξ' : Matrix (Fin (r + n')) (Fin r) K) (C : Matrix (Fin (r + n')) (Fin n') K) :
    M * wittG Ξ' C = wittG (M * Ξ') (M * C) := by
  ext i j
  induction j using Fin.addCases with
  | left a => simp [wittG, Matrix.mul_apply]
  | right b => simp [wittG, Matrix.mul_apply]

/-! ### The local components of $\iota_f$ -/

theorem matV_ι_mul_Ξ (h : SOAdele D.Q'') (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀ (MonoidHom.prodMap D.ιInf D.ιFin h) v * Ξ.1.map (σV v) = Ξ.1.map (σV v) := by
  have e := D.C.ι_smul h
  refine Matrix.ext fun i j => ?_
  have h1 : (matV Q₀ (MonoidHom.prodMap D.ιInf D.ιFin h) v *ᵥ fun k => σV v (Ξ.1 k j)) i = σV v (Ξ.1 i j) :=
    congrArg (fun y => (y j i).2 v) e
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

theorem map_wittG {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (Ξ' : Matrix (Fin (r + n')) (Fin r) K)
    (C : Matrix (Fin (r + n')) (Fin n') K) : (wittG Ξ' C).map f = wittG (Ξ'.map f) (C.map f) := by
  ext i j
  induction j using Fin.addCases with
  | left a => simp [wittG]
  | right b => simp [wittG]

theorem adaptedMat_map (v : HeightOneSpectrum (𝓞 F)) :
    (adaptedMat Q₀ hQ T₀ Ξ D).map (σV v) = wittG (Ξ.1.map (σV v)) (D.Cm.map (σV v)) := by
  rw [adaptedMat_eq, map_wittG]

theorem matV_ι_mul_adapted (h : SOAdele D.Q'') (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀ (MonoidHom.prodMap D.ιInf D.ιFin h) v * (adaptedMat Q₀ hQ T₀ Ξ D).map (σV v) =
      (adaptedMat Q₀ hQ T₀ Ξ D).map (σV v) * blockMat (1 : Matrix (Fin r) (Fin r) (v.adicCompletion F)) 0 0
        (matV D.Q'' h v) := by
  rw [adaptedMat_map, mul_wittG, wittG_mul_blockMat, matV_ι_mul_Ξ, D.hCV]

section Loc

variable (hT : T₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "fr" => towerAdapted Q₀ hQ T₀ Ξ D hT
local notation "gv" => Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
  (AdaptedFrameT.g (towerAdapted Q₀ hQ T₀ Ξ D hT))

theorem evalSO_ιFin (h : SOAf D.Q'') :
    evalSO Q₀ v (D.ιFin h) = locIota v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) (evalSO D.Q'' v h) := by
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  have e := matV_ι_mul_adapted Q₀ hQ T₀ Ξ D ((1 : GInfSO D.Q''), h) v
  have hg : (gv).val = (adaptedMat Q₀ hQ T₀ Ξ D).map (σV v) := rfl
  have hu : (gv).val * (gv)⁻¹.val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  show matV Q₀ (MonoidHom.prodMap D.ιInf D.ιFin ((1 : GInfSO D.Q''), h)) v =
    (gv).val * blockMat 1 0 0 (matV D.Q'' ((1 : GInfSO D.Q''), h) v) * (gv)⁻¹.val
  rw [← hg] at e
  rw [← e, Matrix.mul_assoc, hu, Matrix.mul_one]

theorem locBase_eq : locBase v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) = Ξ.1.map (σV v) := by
  show (adaptedMat Q₀ hQ T₀ Ξ D).map (σV v) *
    (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F)) = _
  rw [adaptedMat_map, wittG_mul_std]

/-- **The local frame** $b_v\,\Xi$ of $b\in SO(V)(\mathbb A_f)$ at $v$. -/
def locFr (b : SOAf Q₀) : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F) :=
  soMat v (evalSO Q₀ v b) * locBase v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT)

theorem smul_ratFT_apply (b : SOAf Q₀) (i : Fin (r + n')) (j : Fin r) :
    ((b • ratFT Q₀ T₀ Ξ) j i) v = locFr Q₀ hQ T₀ Ξ D hT v b i j := by
  rw [locFr, locBase_eq Q₀ hQ T₀ Ξ D hT v]
  show (matV Q₀ ((1 : GInfSO Q₀), b) v *ᵥ fun k => σV v (Ξ.1 k j)) i = _
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply]
  rfl

theorem locFr_mul (k b : SOAf Q₀) :
    locFr Q₀ hQ T₀ Ξ D hT v (k * b) = soMat v (evalSO Q₀ v k) * locFr Q₀ hQ T₀ Ξ D hT v b := by
  rw [locFr, locFr, map_mul, soMat_mul, Matrix.mul_assoc]

end Loc

variable (hT : T₀.Nondegenerate)

theorem mem_latHatT_smul_iff (b : SOAf Q₀) :
    b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r ↔
      ∀ (v : HeightOneSpectrum (𝓞 F)) i j, Valued.v (locFr Q₀ hQ T₀ Ξ D hT v b i j) ≤ 1 := by
  constructor
  · intro h v i j
    have := h j i v
    rw [smul_ratFT_apply Q₀ hQ T₀ Ξ D hT v b i j] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp this
  · intro h j i v
    show ((b • ratFT Q₀ T₀ Ξ) j i) v ∈ _
    rw [smul_ratFT_apply Q₀ hQ T₀ Ξ D hT v b i j]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h v i j)

/-- The local integral frame of an integral $b\,\Xi$. -/
def locFrAt (b : SOAf Q₀) (hb : b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r) (v : HeightOneSpectrum (𝓞 F)) :
    locFrameSet v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) :=
  ⟨locFr Q₀ hQ T₀ Ξ D hT v b, ⟨evalSO Q₀ v b, rfl⟩, fun i j => (mem_latHatT_smul_iff Q₀ hQ T₀ Ξ D hT b).mp hb v i j⟩

theorem exists_KSO_of_fam (x : ∀ v : HeightOneSpectrum (𝓞 F), soStabSO v Q₀) :
    ∃ k ∈ KSO Q₀, ∀ v, evalSO Q₀ v k = (x v : SOv v Q₀) := by
  refine ⟨ofRes Q₀ (⟨fun v => (x v : SOv v Q₀), Filter.Eventually.of_forall fun v => (x v).2⟩ : SOAfRes Q₀), ?_,
    fun v => rfl⟩
  rw [mem_KSO_iff]
  exact fun v => (x v).2

open scoped Classical in
theorem exists_SOAf_of_fam (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : ∀ v, SOv v Q₀) :
    ∃ b : SOAf Q₀, (∀ v ∈ S, evalSO Q₀ v b = φ v) ∧ ∀ v ∉ S, evalSO Q₀ v b = 1 := by
  refine ⟨ofRes Q₀ (⟨fun v => if v ∈ S then φ v else 1, ?_⟩ : SOAfRes Q₀), fun v hv => ?_, fun v hv => ?_⟩
  · refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun v hv => ?_)
    by_contra hvS
    have hvS' : v ∉ S := hvS
    exact hv (by simp only [hvS', ite_false]; exact (soStabSO v Q₀).one_mem)
  · show (if v ∈ S then φ v else 1) = φ v
    simp [hv]
  · show (if v ∈ S then φ v else 1) = 1
    simp [hv]

/-- **Orbits of integral adelic frames are determined place by place.** -/
theorem finOrbit_rel_iff (b b' : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r}) :
    (finOrbitSetoid Q₀ T₀ Ξ).r b b' ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      (locOrbitSetoid v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT)).r (locFrAt Q₀ hQ T₀ Ξ D hT b.1 b.2 v)
        (locFrAt Q₀ hQ T₀ Ξ D hT b'.1 b'.2 v) := by
  constructor
  · intro h v
    obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨evalSO Q₀ v k, (mem_KSO_iff Q₀ k).mp hk v, ?_⟩
    show locFr Q₀ hQ T₀ Ξ D hT v b'.1 = soMat v (evalSO Q₀ v k) * locFr Q₀ hQ T₀ Ξ D hT v b.1
    rw [← locFr_mul]
    refine Matrix.ext fun i j => ?_
    rw [← smul_ratFT_apply Q₀ hQ T₀ Ξ D hT v, ← smul_ratFT_apply Q₀ hQ T₀ Ξ D hT v, mul_smul, hky]
  · intro h
    choose x hx using fun v => h v
    obtain ⟨k, hk, hkv⟩ := exists_KSO_of_fam Q₀ (fun v => ⟨x v, (hx v).1⟩)
    refine Set.mem_smul.2 ⟨k, hk, _, rfl, ?_⟩
    rw [← mul_smul]
    funext j i
    refine Subtype.ext (funext fun v => ?_)
    show (((k * b.1) • ratFT Q₀ T₀ Ξ) j i) v = ((b'.1 • ratFT Q₀ T₀ Ξ) j i) v
    rw [smul_ratFT_apply Q₀ hQ T₀ Ξ D hT v, smul_ratFT_apply Q₀ hQ T₀ Ξ D hT v, locFr_mul, hkv]
    have := (hx v).2
    simp only [locFrAt] at this
    rw [← this]

/-! ### The good places -/

section Good

variable (hT : T₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "gv" => Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
  (AdaptedFrameT.g (towerAdapted Q₀ hQ T₀ Ξ D hT))

/-- The lattice $g^{-1}\mathcal O_F^N$ of the adapted frame. -/
def towerLat : Lat F (r + n') := Lat.image (AdaptedFrameT.g (towerAdapted Q₀ hQ T₀ Ξ D hT))⁻¹ (stdLat F (r + n'))

/-- **The exceptional places**: those where the local theory is not the standard one. -/
def towerBad : Finset (HeightOneSpectrum (𝓞 F)) := frameBadSetG T₀ hT (towerLat Q₀ hQ T₀ Ξ D hT)

theorem loc_towerLat : loc v (towerLat Q₀ hQ T₀ Ξ D hT).1 = locAct v (gv)⁻¹ (std v) := by
  show loc v (glImage _ intVec) = _
  rw [loc_glImage, loc_intVec, map_inv]

theorem good_loc (hv : v ∉ towerBad Q₀ hQ T₀ Ξ D hT) : locAct v (gv)⁻¹ (std v) = std v := by
  rw [← loc_towerLat]; exact (not_mem_frameBadSetG T₀ hT _ hv).2

theorem good_loc' (hv : v ∉ towerBad Q₀ hQ T₀ Ξ D hT) : locAct v (gv) (std v) = std v :=
  locAct_eq_iff.mpr (good_loc Q₀ hQ T₀ Ξ D hT v hv).symm

theorem good_base_int (hv : v ∉ towerBad Q₀ hQ T₀ Ξ D hT) (i : Fin (r + n')) (j : Fin r) :
    Valued.v ((locBase v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT)) i j) ≤ 1 := by
  have h1 : (gv).val *ᵥ stdCol v (n' := n') j ∈ locAct v (gv) (std v) := ⟨stdCol v j, stdCol_mem_std v j, rfl⟩
  rw [good_loc' Q₀ hQ T₀ Ξ D hT v hv] at h1
  have h2 := congrFun (mulVec_stdCol v (gv).val j) i
  have h3 := h1 i
  rw [neg_zero, WithZero.exp_zero] at h3
  rw [h2] at h3
  exact h3

theorem locIota_mem_iff (hv : v ∉ towerBad Q₀ hQ T₀ Ξ D hT) (h : SOv v D.Q'') :
    locIota v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) h ∈ soStabSO v Q₀ ↔ h ∈ soStabSO v D.Q'' := by
  show locAct v (soGL v (locIota v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) h)) (std v) = std v ↔
    locAct v (soGL v h) (std v) = std v
  have e : soGL v (locIota v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) h) =
      (gv) * blockGLB (r := r) ((h : orthGroup (D.Q''.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv) * (gv)⁻¹ :=
    locIota_val v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) h
  rw [e, locAct_mul, locAct_mul, good_loc Q₀ hQ T₀ Ξ D hT v hv, locAct_eq_iff,
    good_loc Q₀ hQ T₀ Ξ D hT v hv]
  exact locAct_blockGLB_std_iff v _

/-- At a good place all the lattices of $Y_v(\Lambda)$ lie in one $SO(Q'')(F_v)$-orbit. -/
theorem good_allSO (hv : v ∉ towerBad Q₀ hQ T₀ Ξ D hT) (hn' : 1 ≤ n')
    (M M' : LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F))
      (locAct v (gv)⁻¹ (std v))) :
    ∃ a : soSub (D.Q''.map (algebraMap (𝓞 F) F)) (v.adicCompletion F),
      (a : orthGroup (D.Q''.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) • M = M' := by
  have key : ∀ M M' : LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F))
      (loc v (towerLat Q₀ hQ T₀ Ξ D hT).1),
      M' ∈ orbit (orthGroup (D.Q''.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) M :=
    fun M M' => exists_smul_of_not_memG T₀ hT D.Q'' D.hQ'' (towerLat Q₀ hQ T₀ Ξ D hT) hv M M'
  rw [loc_towerLat Q₀ hQ T₀ Ξ D hT v] at key
  have hΛ := good_loc Q₀ hQ T₀ Ξ D hT v hv
  have hstd : ∀ j, stdCol v (n' := n') j ∈ locAct v (gv)⁻¹ (std v) := fun j => by
    rw [hΛ]; exact stdCol_mem_std v j
  set M0 := locFrameStdPtG v (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F))
    (locAct v (gv)⁻¹ (std v)) hstd with hM0
  obtain ⟨ρ, hρ, hρdet⟩ := exists_stdStab_det_neg_one v D.Q'' D.hQ'' (by omega)
  have hρM : ρ • M0 = M0 := Subtype.ext (by
    show locAct v (orthEmbB (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F)) _ ρ :
      GL (Fin (r + n')) _) (locAct v (gv)⁻¹ (std v)) = locAct v (gv)⁻¹ (std v)
    rw [hΛ]
    exact (mem_stdStab_orthEmbB_iff (T₀.map (algebraMap (𝓞 F) F)) (D.Q''.map (algebraMap (𝓞 F) F)) v ρ).mpr hρ)
  have hSO : ∀ N, ∃ a : soSub (D.Q''.map (algebraMap (𝓞 F) F)) (v.adicCompletion F),
      (a : orthGroup (D.Q''.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) • M0 = N := by
    intro N
    obtain ⟨h, rfl⟩ := key M0 N
    rcases det_eq_one_or_neg_one (D.Q''.map (algebraMap (𝓞 F) F)) (nondegenerate_QF D.Q'' D.hQ'') h with h1 | h1
    · exact ⟨⟨h, h1⟩, rfl⟩
    · refine ⟨⟨h * ρ, ?_⟩, ?_⟩
      · show (((h * ρ : orthGroup (D.Q''.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) :
            GL (Fin n') (v.adicCompletion F))).val.det = 1
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, h1, hρdet]; norm_num
      · show (h * ρ) • M0 = h • M0
        rw [mul_smul, hρM]
  obtain ⟨a1, h1⟩ := hSO M
  obtain ⟨a2, h2⟩ := hSO M'
  refine ⟨a2 * a1⁻¹, ?_⟩
  subst h1 h2
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul]

/-- **At a good place there is a single orbit of integral frames.** -/
theorem good_subsingleton (hv : v ∉ towerBad Q₀ hQ T₀ Ξ D hT) (hn' : 1 ≤ n') :
    Subsingleton (LocOrbit v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT)) := by
  have hbij := ThQ_bijective v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) hQ hT (by omega)
  refine ⟨fun o o' => hbij.1 ?_⟩
  induction o using Quotient.inductionOn with | _ y => ?_
  induction o' using Quotient.inductionOn with | _ y' => ?_
  rw [ThQ_mk, ThQ_mk]
  apply Quotient.sound'
  obtain ⟨a, ha⟩ := good_allSO Q₀ hQ T₀ Ξ D hT v hv hn'
    (Th v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) y') (Th v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) y)
  exact orbitRel_apply.mpr ⟨a, Subtype.ext (congrArg Subtype.val ha)⟩

end Good

end QuadFormsKB.Tamagawa.Indefinite
