/-
# Weil's measure of the integral adelic frames for the algebraic frame data

**Layer:** number fields, adeles. The finite-place computation for rank-2 complements (`FrameDensitiesAux.lean`,
`FrameDensities.lean`,
`Rank2Orbit.lean`) uses only the algebraic fields of a frame tower. This file re-runs it, unchanged, for the algebraic
frame data `D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1)` (`IsoTowerAlg.lean`), which exist also when the complement is an
isotropic binary form (no `FrameTower` exists then). Everything is in the namespace `IsoAlg`; the main result is
$$\texttt{IsoAlg.frameOrbitSumLam} = \sum_O\frac{\mu_f(SO(\hat L))}{\mu^\lambda_{H,f}(K_O)} = \prod_\mathfrak p
  \beta_\mathfrak p(L,T_0)\,\frac{|\det g|_\mathfrak p^{\,n'+1}}{|\det H_{T_0}|_\mathfrak p^{\,n'}}\,\lambda_\mathfrak p
  \qquad(\texttt{IsoAlg.frameOrbitSum\_lam}),$$
for convergence factors $\lambda_v>0$ on the stabilizer with $\prod_v\lambda_v^{-1}\alpha_v(L'')$ absolutely convergent and
nonzero (for an isotropic binary $Q''$: $\lambda_v = 1 - Nv^{-1}$). The proofs are those of the rank-2 case (including
the orbit
dictionary), with `D.fix` and `D.stab` in place of the orbit coordinates of a tower.
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoTowerAlg
import QuadFormsKB.Tamagawa.Indefinite.Rank2Orbit

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite.IsoAlg

open QuadFormsKB.Tamagawa.Indefinite

section Prelude

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}
  (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1))

/-- The stabilizer of $(\Xi_\infty, \Xi_f)$ is $\iota(SO(Q'')(\mathbb A))$ (from `D.stab`). -/
theorem stabIn_frameCprod : StabIn (MonoidHom.prodMap D.ιInf D.ιFin) (ratAT Q₀ T₀ Ξ, ratFT Q₀ T₀ Ξ) := by
  intro g hg
  refine D.stab g (splitFrame_injective ?_)
  rw [splitFrame_smul, splitFrame_ratFrame]
  exact hg

end Prelude

section Aux

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}
  (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1))

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
  have e := D.fix h
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


end Aux

section Densities

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.Tamagawa.Measure.ConeFinite

/-! ### Generic lemmas -/

section Generic

theorem mem_orbitStab' {B B' : Type*} [Group B] [Group B'] {ιB : B' →* B} {K : Subgroup B} {gO : B} {h : B'} :
    h ∈ orbitStab ιB K gO ↔ gO * ιB h * gO⁻¹ ∈ K := by
  simp [orbitStab, MulAut.conj_apply]

theorem orbitStab_mul_mul {B B' : Type*} [Group B] [Group B'] (ιB : B' →* B) (K : Subgroup B) (b k : B)
    (hk : k ∈ K) (a : B') :
    orbitStab ιB K (k * b * ιB a) = (orbitStab ιB K b).comap (MulAut.conj a).toMonoidHom := by
  ext h
  rw [Subgroup.mem_comap, mem_orbitStab', mem_orbitStab']
  have e : k * b * ιB a * ιB h * (k * b * ιB a)⁻¹ =
      k * (b * ιB ((MulAut.conj a).toMonoidHom h) * b⁻¹) * k⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    group
  rw [e]
  constructor
  · intro H
    have := K.mul_mem (K.mul_mem (K.inv_mem hk) H) hk
    simpa [mul_assoc] using this
  · intro H
    exact K.mul_mem (K.mul_mem hk H) (K.inv_mem hk)

theorem measure_comap_conj {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (U : Subgroup G) (a : G) :
    μ ((U.comap (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) = μ U := by
  have e : ((U.comap (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) =
      (fun h => h * a⁻¹) ⁻¹' ((fun h => a * h) ⁻¹' (U : Set G)) := by
    ext h
    simp [MulAut.conj_apply, mul_assoc]
  rw [e, measure_preimage_mul_right, measure_preimage_mul]

theorem multipliable_ite_one {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (ha : Multipliable a) (S : Finset ι)
    (hS : ∀ v ∈ S, a v ≠ 0) : Multipliable fun v => if v ∈ S then 1 else a v := by
  set c : ι → ℝ := fun v => if v ∈ S then (a v)⁻¹ else 1 with hc
  have hcm : Multipliable c :=
    (hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional ι) (s := S) (f := c) fun v hv => by simp [c, hv]).multipliable
  convert ha.mul hcm using 1
  ext v
  by_cases hv : v ∈ S
  · simp [c, hv, mul_inv_cancel₀ (hS v hv)]
  · simp [c, hv]

theorem hasProd_prod_mul_tprod_ite {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (S : Finset ι)
    (h : Multipliable fun v => if v ∈ S then 1 else a v) :
    HasProd a ((∏ v ∈ S, a v) * ∏' v, if v ∈ S then 1 else a v) := by
  have h1 : HasProd (fun v => if v ∈ S then a v else 1) (∏ v ∈ S, a v) := by
    have := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional ι) (s := S) (f := fun v => if v ∈ S then a v else 1)
      (fun v hv => by simp [hv])
    rwa [Finset.prod_congr rfl fun v hv => (show (if v ∈ S then a v else 1) = a v by simp [hv])] at this
  convert h1.mul h.hasProd using 1
  ext v
  by_cases hv : v ∈ S <;> simp [hv]

theorem ennreal_prod_div {ι : Type*} (s : Finset ι) (A U : ι → ℝ≥0∞) (hU : ∀ i ∈ s, U i ≠ 0) (x y : ℝ)
    (hy : 0 < y) :
    ((∏ i ∈ s, A i) * ENNReal.ofReal x) / ((∏ i ∈ s, U i) * ENNReal.ofReal y) =
      (∏ i ∈ s, A i / U i) * ENNReal.ofReal (x / y) := by
  rw [ENNReal.ofReal_div_of_pos hy]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr (ENNReal.ofReal_pos.2 hy).ne'),
    ENNReal.prod_inv_distrib (fun i hi j _ _ => Or.inl (hU i hi)), Finset.prod_mul_distrib]
  ring

end Generic

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

/-! ### Local lemmas -/

section Local

variable (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
  (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))

theorem continuous_locIota : Continuous (locIota v Q₀ T₀ fr) :=
  Continuous.subtype_mk (Continuous.subtype_mk ((continuous_const.mul ((continuous_blockGLB v).comp
    (continuous_subtype_val.comp continuous_subtype_val))).mul continuous_const) _) _

theorem isOpen_orbitStab_loc (φ : SOv v Q₀) :
    IsOpen (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) φ : Set (SOv v (fr).Q')) := by
  have e : (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) φ : Set (SOv v (fr).Q')) =
      (fun h => φ * locIota v Q₀ T₀ fr h * φ⁻¹) ⁻¹' (soStabSO v Q₀ : Set (SOv v Q₀)) := by
    ext h
    exact mem_orbitStab'
  rw [e]
  exact (isOpen_soStabSO v Q₀).preimage
    ((continuous_const.mul (continuous_locIota v Q₀ T₀ fr)).mul continuous_const)

/-- The measure of $K_\varphi = \{h : \varphi\,\iota(h)\,\varphi^{-1}\in SO(L_v)\}$ depends only on the local orbit of
$\varphi\,\Xi$. -/
theorem muLocSO_orbitStab_eq (hT : T₀.Nondegenerate) (hQ' : (fr).Q'.Nondegenerate) (hn' : 1 ≤ n') (φ : SOv v Q₀)
    (y : locFrameSet v Q₀ T₀ fr) (hy : y.1 = soMat v φ * locBase v Q₀ T₀ fr) :
    muLocSO v (fr).Q' 1 (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) φ : Set (SOv v (fr).Q')) =
      muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (Quotient.mk _ y) : Set (SOv v (fr).Q')) := by
  set o : LocOrbit v Q₀ T₀ fr := Quotient.mk _ y
  obtain ⟨k, hk, hky⟩ := Quotient.mk_out (s := locOrbitSetoid v Q₀ T₀ fr) y
  have hrep : (Quotient.out o : locFrameSet v Q₀ T₀ fr).1 =
      soMat v (locOrbitRep v Q₀ T₀ fr o) * locBase v Q₀ T₀ fr := by
    rw [locOrbitRep_eq]; exact frPhi_spec v Q₀ T₀ fr _
  have hφ : soMat v φ * locBase v Q₀ T₀ fr = soMat v (k * locOrbitRep v Q₀ T₀ fr o) * locBase v Q₀ T₀ fr := by
    rw [← hy, hky, hrep, soMat_mul, Matrix.mul_assoc]
  obtain ⟨a, ha⟩ := Xi_stab v Q₀ T₀ fr hT _ _ hφ
  have := isHaarMeasure_muLocSO v (fr).Q' hQ'
  have := Weil.isMulRightInvariant_muLocSO v (fr).Q' hQ' hn'
  rw [ha, orbitStab_mul_mul _ _ _ _ hk, measure_comap_conj]
  rfl

theorem finite_locOrbit (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) (hn' : 1 ≤ n') :
    Finite (LocOrbit v Q₀ T₀ fr) := by
  have hQ' : (fr).Q'.Nondegenerate := adapted_nondegenerate Q₀ T₀ fr hQ₀
  obtain ⟨ρ, -, hρdet⟩ := exists_stdStab_det_neg_one v (fr).Q' hQ' (by omega)
  have hQF' := nondegenerate_QF (fr).Q' hQ'
  have hH2 : (soSub ((fr).Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).index = 2 := by
    have := relIndex_soSub_eq_two _ hQF' ⊤ ρ (Subgroup.mem_top _) hρdet
    rwa [Subgroup.relIndex_top_right, inf_top_eq] at this
  have := finite_types v Q₀ T₀ fr hQ₀ hT
  have := Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero
    (X := LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) ((fr).Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)))
    (H := soSub ((fr).Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) (by rw [hH2]; norm_num)
  exact Finite.of_injective _ (ThQ_bijective v Q₀ T₀ fr hQ₀ hT (by omega)).1

include fr in
theorem localDensityForm_nonneg_of_frame (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) :
    0 ≤ NF.localDensityForm v Q₀ T₀ := by
  have hQ' : (fr).Q'.Nondegenerate := adapted_nondegenerate Q₀ T₀ fr hQ₀
  have hid := frameLocalIdentityGen v Q₀ hQ₀ T₀ hT fr
  have hW : 0 ≤ locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) ((fr).Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) :=
    finsum_nonneg fun t => locFrameWeightG_nonneg v Q₀ T₀ fr _
  have hβ₀ := LatChange.localDensityForm_self_pos v Q₀ hQ₀
  have hβ' := LatChange.localDensityForm_self_pos v (fr).Q' hQ'
  have hg : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1) := by
    have : fr.g.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
    exact pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 this)) _
  have hL : 0 ≤ NF.localDensityForm v (fr).Q' (fr).Q' * NF.localDensityForm v Q₀ T₀ *
      ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1) := by
    rw [← hid]; positivity
  have h2 : 0 ≤ NF.localDensityForm v (fr).Q' (fr).Q' * NF.localDensityForm v Q₀ T₀ :=
    nonneg_of_mul_nonneg_left hL hg
  exact nonneg_of_mul_nonneg_right h2 hβ'

end Local

/-! ### The global objects -/

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)

local notation "fr" => towerAdapted Q₀ hQ T₀ Ξ D hT
local notation "Bad" => towerBad Q₀ hQ T₀ Ξ D hT

/-- The integral adelic frames in the orbit of $\Xi$. -/
abbrev IntFr : Type := {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r}

/-- Every orbit has a representative $b$ with $b_v = 1$ outside the exceptional places. -/
theorem exists_goodRep (hn' : 1 ≤ n') (b : IntFr Q₀ T₀ Ξ) :
    ∃ b' : IntFr Q₀ T₀ Ξ, (finOrbitSetoid Q₀ T₀ Ξ).r b b' ∧ ∀ v ∉ Bad, evalSO Q₀ v b'.1 = 1 := by
  classical
  obtain ⟨c, hcS, hcn⟩ := exists_SOAf_of_fam Q₀ Bad (fun v => evalSO Q₀ v b.1)
  have hS : ∀ v ∈ Bad, locFr Q₀ hQ T₀ Ξ D hT v c = locFr Q₀ hQ T₀ Ξ D hT v b.1 := fun v hv => by
    simp only [locFr, hcS v hv]
  have hN : ∀ v ∉ Bad, locFr Q₀ hQ T₀ Ξ D hT v c = locBase v Q₀ T₀ fr := fun v hv => by
    simp only [locFr, hcn v hv, soMat_one, Matrix.one_mul]
  have hint : c • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r := by
    rw [mem_latHatT_smul_iff Q₀ hQ T₀ Ξ D hT]
    intro v i j
    by_cases hv : v ∈ Bad
    · rw [hS v hv]; exact (mem_latHatT_smul_iff Q₀ hQ T₀ Ξ D hT b.1).mp b.2 v i j
    · rw [hN v hv]; exact good_base_int Q₀ hQ T₀ Ξ D hT v hv i j
  refine ⟨⟨c, hint⟩, ?_, hcn⟩
  rw [finOrbit_rel_iff Q₀ hQ T₀ Ξ D hT]
  intro v
  by_cases hv : v ∈ Bad
  · refine ⟨1, (soStabSO v Q₀).one_mem, ?_⟩
    show locFr Q₀ hQ T₀ Ξ D hT v c = soMat v 1 * locFr Q₀ hQ T₀ Ξ D hT v b.1
    rw [soMat_one, Matrix.one_mul, hS v hv]
  · have := good_subsingleton Q₀ hQ T₀ Ξ D hT v hv hn'
    exact Quotient.exact (Subsingleton.elim (Quotient.mk _ _) (Quotient.mk _ _))

/-- **The measure of $K_O$ does not depend on the representative of $O$.** -/
theorem muFin_orbitStab_congr (hn' : 1 ≤ n') (b b' : IntFr Q₀ T₀ Ξ) (h : (finOrbitSetoid Q₀ T₀ Ξ).r b b') :
    muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) b'.1) =
      muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) b.1) := by
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfix : ((k * b.1)⁻¹ * b'.1) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
    rw [mul_smul, ← hky, ← mul_smul k, inv_smul_smul]
  obtain ⟨a, ha⟩ := stab_iotaB (stabIn_frameCprod Q₀ hQ T₀ Ξ D) _ hfix
  have hb' : b'.1 = k * b.1 * D.ιFin a := by rw [ha]; group
  have := isMulRightInvariant_muFin D.Q'' D.hQ'' (by omega)
  rw [hb', orbitStab_mul_mul _ _ _ _ hk, measure_comap_conj]

/-- For a representative with $b_v = 1$ outside $B$, the orbit stabilizer $K_O$ is a box. -/
theorem orbitStab_eq_boxSO (b : SOAf Q₀) (hb : ∀ v ∉ Bad, evalSO Q₀ v b = 1) :
    (orbitStab D.ιFin (KSO Q₀) b : Set (SOAf D.Q'')) = boxSO D.Q'' Bad
      (fun v => ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q''))) := by
  ext h
  have e : ∀ v, evalSO Q₀ v (b * D.ιFin h * b⁻¹) =
      evalSO Q₀ v b * locIota v Q₀ T₀ fr (evalSO D.Q'' v h) * (evalSO Q₀ v b)⁻¹ := fun v => by
    rw [map_mul, map_mul, map_inv, evalSO_ιFin Q₀ hQ T₀ Ξ D hT]
  simp only [SetLike.mem_coe, mem_orbitStab', mem_KSO_iff, boxSO, Set.mem_ofPred_eq, e]
  constructor
  · intro H
    refine ⟨fun v _ => H v, fun v hv => ?_⟩
    have := H v
    rw [hb v hv, one_mul, inv_one, mul_one] at this
    exact (locIota_mem_iff Q₀ hQ T₀ Ξ D hT v hv _).mp this
  · rintro ⟨H1, H2⟩ v
    by_cases hv : v ∈ Bad
    · exact H1 v hv
    · rw [hb v hv, one_mul, inv_one, mul_one]
      exact (locIota_mem_iff Q₀ hQ T₀ Ξ D hT v hv _).mpr (H2 v hv)

/-- The local orbit at $v$ of an orbit $O$ of integral adelic frames. -/
def finToLoc (O : FinOrbit Q₀ T₀ Ξ) (v : HeightOneSpectrum (𝓞 F)) : LocOrbit v Q₀ T₀ fr :=
  Quotient.mk _ (locFrAt Q₀ hQ T₀ Ξ D hT (Quotient.out O).1 (Quotient.out O).2 v)

theorem finToLoc_eq (b : IntFr Q₀ T₀ Ξ) (v : HeightOneSpectrum (𝓞 F)) :
    finToLoc Q₀ hQ T₀ Ξ D hT (Quotient.mk _ b) v = Quotient.mk _ (locFrAt Q₀ hQ T₀ Ξ D hT b.1 b.2 v) := by
  apply Quotient.sound
  have h : (finOrbitSetoid Q₀ T₀ Ξ).r (Quotient.out (Quotient.mk (finOrbitSetoid Q₀ T₀ Ξ) b)) b :=
    Quotient.mk_out (s := finOrbitSetoid Q₀ T₀ Ξ) b
  exact (finOrbit_rel_iff Q₀ hQ T₀ Ξ D hT _ _).mp h v

/-- The real local measures $\mu_v(SO(L_v))$. -/
def aSO {N : ℕ} (Q : QuadForm (𝓞 F) N) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (muLocSO v Q 1 (soStabSO v Q : Set (SOv v Q))).toReal

theorem ofReal_aSO {N : ℕ} (Q : QuadForm (𝓞 F) N) (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (aSO Q v) = muLocSO v Q 1 (soStabSO v Q : Set (SOv v Q)) := by
  rw [aSO, ENNReal.ofReal_toReal]; rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top

theorem aSO_pos {N : ℕ} (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    0 < aSO Q v :=
  ENNReal.toReal_pos (muLocSO_soStabSO_pos Q hQ v one_pos) (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)

theorem tprod_aSO_pos {N : ℕ} (hN : 3 ≤ N) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) : 0 < ∏' v, aSO Q v := by
  have := tprod_siegelDensity_pos hN Q hQ
  rwa [← finFactor_one Q hQ] at this

theorem multipliable_aSO {N : ℕ} (hN : 3 ≤ N) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) :
    Multipliable (aSO Q) :=
  multipliable_muLocSO_one Q hQ (by omega) (by omega)

theorem tprod_ite_aSO_pos {N : ℕ} (hN : 3 ≤ N) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate)
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)] :
    0 < ∏' v, if v ∈ S then 1 else aSO Q v := by
  classical
  have h := tprod_eq_prod_mul_tprod_ite (aSO Q) (multipliable_aSO hN Q hQ) S (fun v _ => (aSO_pos Q hQ v).ne')
  have hp := tprod_aSO_pos hN Q hQ
  rw [h] at hp
  convert pos_of_mul_pos_right hp (Finset.prod_nonneg fun v _ => (aSO_pos Q hQ v).le)

/-- The local orbits at the exceptional places of an orbit of integral adelic frames. -/
def finOrbitMap (O : FinOrbit Q₀ T₀ Ξ) : ∀ v : Bad, LocOrbit v.1 Q₀ T₀ fr :=
  fun v => finToLoc Q₀ hQ T₀ Ξ D hT O v.1

/-- **The orbits of integral adelic frames are the families of local orbits at the exceptional places.** -/
theorem finOrbitMap_bijective (hn' : 1 ≤ n') : Function.Bijective (finOrbitMap Q₀ hQ T₀ Ξ D hT) := by
  classical
  constructor
  · intro O O' h
    rw [← Quotient.out_eq O, ← Quotient.out_eq O']
    apply Quotient.sound
    refine (finOrbit_rel_iff Q₀ hQ T₀ Ξ D hT _ _).mpr fun v => ?_
    by_cases hv : v ∈ Bad
    · exact Quotient.exact (congrFun h ⟨v, hv⟩)
    · have := good_subsingleton Q₀ hQ T₀ Ξ D hT v hv hn'
      exact Quotient.exact (Subsingleton.elim (Quotient.mk _ _) (Quotient.mk _ _))
  · intro x
    set φ : ∀ v, SOv v Q₀ := fun v => if hv : v ∈ Bad then locOrbitRep v Q₀ T₀ fr (x ⟨v, hv⟩) else 1 with hφ
    obtain ⟨c, hcS, hcn⟩ := exists_SOAf_of_fam Q₀ Bad φ
    have hS : ∀ (v) (hv : v ∈ Bad), locFr Q₀ hQ T₀ Ξ D hT v c =
        (Quotient.out (x ⟨v, hv⟩) : locFrameSet v Q₀ T₀ fr).1 := by
      intro v hv
      show soMat v (evalSO Q₀ v c) * locBase v Q₀ T₀ fr = _
      rw [hcS v hv, frPhi_spec v Q₀ T₀ fr (Quotient.out (x ⟨v, hv⟩))]
      simp only [hφ, hv, ↓reduceDIte, locOrbitRep_eq]
    have hN : ∀ v ∉ Bad, locFr Q₀ hQ T₀ Ξ D hT v c = locBase v Q₀ T₀ fr := fun v hv => by
      simp only [locFr, hcn v hv, soMat_one, Matrix.one_mul]
    have hint : c • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r := by
      rw [mem_latHatT_smul_iff Q₀ hQ T₀ Ξ D hT]
      intro v i j
      by_cases hv : v ∈ Bad
      · rw [hS v hv]; exact (Quotient.out (x ⟨v, hv⟩)).2.2 i j
      · rw [hN v hv]; exact good_base_int Q₀ hQ T₀ Ξ D hT v hv i j
    refine ⟨Quotient.mk _ ⟨c, hint⟩, funext fun v => ?_⟩
    show finToLoc Q₀ hQ T₀ Ξ D hT (Quotient.mk _ ⟨c, hint⟩) v.1 = x v
    rw [finToLoc_eq]
    conv_rhs => rw [← Quotient.out_eq (x v)]
    exact congrArg _ (Subtype.ext (hS v.1 v.2))

theorem frameLocFactor_nonneg (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ frameLocFactor Q₀ hQ T₀ Ξ D hT v := by
  unfold frameLocFactor
  have := localDensityForm_nonneg_of_frame v Q₀ T₀ fr hQ hT
  positivity

theorem ofReal_frameLocFactor (hn' : 1 ≤ n') (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (frameLocFactor Q₀ hQ T₀ Ξ D hT v) = locOrbitSum v Q₀ T₀ fr :=
  (locOrbitSum_eq v Q₀ T₀ fr hQ hT hn').symm

/-- At a good place the local factor is $\mu_v(SO(L_v))/\mu''_v(SO(L''_v))$. -/
theorem frameLocFactor_good (hn' : 1 ≤ n') (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Bad) :
    frameLocFactor Q₀ hQ T₀ Ξ D hT v = aSO Q₀ v / aSO D.Q'' v := by
  have := good_subsingleton Q₀ hQ T₀ Ξ D hT v hv hn'
  set y : locFrameSet v Q₀ T₀ fr := ⟨locBase v Q₀ T₀ fr, ⟨1, by rw [soMat_one, Matrix.one_mul]⟩,
    good_base_int Q₀ hQ T₀ Ξ D hT v hv⟩
  have hstab : (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) 1 : Set (SOv v (fr).Q')) =
      (soStabSO v D.Q'' : Set (SOv v D.Q'')) := by
    ext h
    simp only [SetLike.mem_coe, mem_orbitStab', one_mul, inv_one, mul_one]
    exact locIota_mem_iff Q₀ hQ T₀ Ξ D hT v hv h
  have hK := muLocSO_orbitStab_eq v Q₀ T₀ fr hT D.hQ'' hn' 1 y (by rw [soMat_one, Matrix.one_mul])
  rw [hstab] at hK
  have hsum : locOrbitSum v Q₀ T₀ fr = ENNReal.ofReal (aSO Q₀ v) / ENNReal.ofReal (aSO D.Q'' v) := by
    rw [locOrbitSum, tsum_eq_single (Quotient.mk _ y) (fun o ho => absurd (Subsingleton.elim o _) ho),
      ofReal_aSO, ofReal_aSO, ← hK]
  rw [← ofReal_frameLocFactor Q₀ hQ T₀ Ξ D hT (by omega) v, ← ENNReal.ofReal_div_of_pos (aSO_pos D.Q'' D.hQ'' v)]
    at hsum
  exact (ENNReal.ofReal_eq_ofReal_iff (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v)
    (div_nonneg (aSO_pos Q₀ hQ v).le (aSO_pos D.Q'' D.hQ'' v).le)).mp hsum


end Densities

section Orbit

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.Tamagawa.Measure.ConeFinite

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)
  (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hlam : ∀ v, 0 < lam v)
  (hmult : Multipliable fun v => (muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q''))).toReal)
  (hpos : 0 < ∏' v, (muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q''))).toReal)

/-- **The orbit sum with the stabilizer measure `muFin Q'' λ`**:
$\sum_O\mu_f(SO(\hat L))/\mu^\lambda_{H,f}(K_O)$. -/
def frameOrbitSumLam : ℝ≥0∞ :=
  ∑' O : FinOrbit Q₀ T₀ Ξ, muFin Q₀ (fun _ => 1) (KSO Q₀) /
    muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O))

section LamHelpers

local notation "fr" => towerAdapted Q₀ hQ T₀ Ξ D hT
local notation "Bad" => towerBad Q₀ hQ T₀ Ξ D hT
set_option quotPrecheck false in
local notation "aL " v:max => (muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q''))).toReal

theorem muLocSO_eq_ofReal_smul {m : ℕ} (Q : QuadForm (𝓞 F) m) (v : HeightOneSpectrum (𝓞 F)) {l : ℝ}
    (hl : 0 < l) : muLocSO v Q l = ENNReal.ofReal l⁻¹ • muLocSO v Q 1 := by
  have h : Real.toNNReal (NF.siegelDensity v Q Q / l) =
      Real.toNNReal l⁻¹ * Real.toNNReal (NF.siegelDensity v Q Q / 1) := by
    rw [← Real.toNNReal_mul (inv_nonneg.2 hl.le), div_one, inv_mul_eq_div]
  unfold muLocSO haarNorm
  rw [h, mul_smul]
  rfl

theorem muLocSO_apply_lam {m : ℕ} (Q : QuadForm (𝓞 F) m) (v : HeightOneSpectrum (𝓞 F)) {l : ℝ}
    (hl : 0 < l) (S : Set (SOv v Q)) : muLocSO v Q l S = ENNReal.ofReal l⁻¹ * muLocSO v Q 1 S := by
  rw [muLocSO_eq_ofReal_smul Q v hl, Measure.smul_apply, smul_eq_mul]

theorem ennreal_div_ofReal_inv_mul (A M : ℝ≥0∞) {l : ℝ} (hl : 0 < l) :
    A / (ENNReal.ofReal l⁻¹ * M) = ENNReal.ofReal l * (A / M) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.ofReal_inv_of_pos hl,
    ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top))
      (Or.inl (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hl).ne')), inv_inv]
  ring

theorem toReal_muLocSO_soStab_lam {m : ℕ} (Q : QuadForm (𝓞 F) m) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 F)) {l : ℝ} (hl : 0 < l) :
    (muLocSO v Q l (soStabSO v Q : Set (SOv v Q))).toReal = aSO Q v / l := by
  have hd := siegelDensity_self_pos' Q hQ v
  rw [aSO, muLocSO_soStabSO, muLocSO_soStabSO, ENNReal.toReal_ofReal (div_pos hd hl).le,
    ENNReal.toReal_ofReal (by rw [div_one]; exact hd.le), div_one]

/-- Right invariance of `muFin Q lam` for arbitrary convergence factors. -/
theorem isMulRightInvariant_muFin_lam {m : ℕ} (Q : QuadForm (𝓞 F) m)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hQ : Q.Nondegenerate) (hn : 0 < m) :
    (QuadFormsKB.Tamagawa.Measure.muFin Q lam).IsMulRightInvariant := by
  classical
  by_cases hc : Real.toNNReal (finFactor Q lam) = 0
  · have h0 : QuadFormsKB.Tamagawa.Measure.muFin Q lam = 0 := by
      unfold QuadFormsKB.Tamagawa.Measure.muFin haarNorm; rw [hc]; simp
    rw [h0]
    exact ⟨fun g => MeasureTheory.Measure.map_zero _⟩
  · have : (QuadFormsKB.Tamagawa.Measure.muFin Q lam).IsHaarMeasure := by
      unfold QuadFormsKB.Tamagawa.Measure.muFin haarNorm; exact MeasureTheory.Measure.IsHaarMeasure.nnreal_smul _ hc
    refine Weil.isMulRightInvariant_of_conj _ (KSO Q : Set (SOAf Q)) (isCompact_KSO Q) ⟨1, ?_⟩ ?_
    · rw [(isOpen_KSO Q).interior_eq]; exact (KSO Q).one_mem
    intro g
    have hev : ∀ᶠ v in Filter.cofinite, evalSO Q v g ∈ soStabSO v Q := by
      have := (g : OAf (Q.map (algebraMap (𝓞 F) F))).2
      filter_upwards [this] with v hv
      exact hv
    set S := (Filter.eventually_cofinite.mp hev).toFinset with hS
    have hgK : ∀ v, v ∉ S → evalSO Q v g ∈ soStabSO v Q := by
      intro v hv
      have : v ∉ {v | ¬ evalSO Q v g ∈ soStabSO v Q} := by
        simpa [hS] using hv
      simpa using this
    set U : ∀ v, Set (SOv v Q) := fun v => {y | evalSO Q v g * y * (evalSO Q v g)⁻¹ ∈ soStabSO v Q} with hU
    have key : ∀ x : SOAf Q, (g * x * g⁻¹ ∈ KSO Q) ↔
        ∀ v, evalSO Q v g * evalSO Q v x * (evalSO Q v g)⁻¹ ∈ soStabSO v Q := by
      intro x
      rw [mem_KSO_iff]
      simp only [map_mul, map_inv, SetLike.mem_coe]
    have hbox : {x | g * x * g⁻¹ ∈ (KSO Q : Set (SOAf Q))} = boxSO Q S U := by
      ext x
      show g * x * g⁻¹ ∈ KSO Q ↔ _
      rw [key]
      simp only [boxSO, hU, Set.mem_ofPred_eq, SetLike.mem_coe]
      constructor
      · intro hx
        refine ⟨fun v _ => hx v, fun v hv => ?_⟩
        have hg := hgK v hv
        have := (soStabSO v Q).mul_mem ((soStabSO v Q).mul_mem ((soStabSO v Q).inv_mem hg) (hx v)) hg
        simpa [mul_assoc] using this
      · rintro ⟨h1, h2⟩ v
        by_cases hv : v ∈ S
        · exact h1 v hv
        · have hg := hgK v hv
          exact (soStabSO v Q).mul_mem ((soStabSO v Q).mul_mem hg (h2 v hv)) ((soStabSO v Q).inv_mem hg)
    have hUm : ∀ v ∈ S, MeasurableSet (U v) := by
      intro v _
      refine IsOpen.measurableSet ?_
      exact (isOpen_soStabSO v Q).preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    have hone : ∀ v ∈ S, haarSO Q v (U v) = 1 := by
      intro v _
      haveI := Weil.isMulRightInvariant_muLocSO v Q hQ hn
      haveI : (muLocSO v Q 1).IsMulLeftInvariant := by unfold muLocSO; infer_instance
      rw [haarSO_eq_div Q hQ v one_pos]
      have hconj := Weil.measure_conj_set_eq (muLocSO v Q 1) (evalSO Q v g) (soStabSO v Q : Set (SOv v Q))
      have : muLocSO v Q 1 (U v) = muLocSO v Q 1 (soStabSO v Q : Set (SOv v Q)) := hconj
      rw [this]
      exact ENNReal.div_self (muLocSO_soStabSO_pos Q hQ v one_pos)
        (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
    rw [hbox, QuadFormsKB.Tamagawa.Measure.muFin_boxSO_haar Q _ S U hUm, Finset.prod_eq_one hone, mul_one,
      muFin_KSO]

include hlam hmult hpos in
theorem muFin_orbitStab_congr_lam (hn' : 1 ≤ n') (b b' : IntFr Q₀ T₀ Ξ)
    (h : (finOrbitSetoid Q₀ T₀ Ξ).r b b') :
    muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b'.1) = muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b.1) := by
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfix : ((k * b.1)⁻¹ * b'.1) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
    rw [mul_smul, ← hky, ← mul_smul k, inv_smul_smul]
  obtain ⟨a, ha⟩ := stab_iotaB (stabIn_frameCprod Q₀ hQ T₀ Ξ D) _ hfix
  have hb' : b'.1 = k * b.1 * D.ιFin a := by rw [ha]; group
  have := isMulRightInvariant_muFin_lam D.Q'' lam D.hQ'' (by omega)
  rw [hb', orbitStab_mul_mul _ _ _ _ hk, measure_comap_conj]

open Classical in
include hlam hmult hpos in
theorem tprod_ite_aL_pos : 0 < ∏' v, if v ∈ Bad then 1 else aL v := by
  classical
  have ha0 : ∀ v, 0 < aL v := fun v =>
    ENNReal.toReal_pos (muLocSO_soStabSO_pos D.Q'' D.hQ'' v (hlam v))
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have h := tprod_eq_prod_mul_tprod_ite (fun v => aL v) hmult Bad (fun v _ => (ha0 v).ne')
  have hp := hpos
  rw [show (∏' v, aL v) = _ from h] at hp
  convert pos_of_mul_pos_right hp (Finset.prod_nonneg fun v _ => (ha0 v).le)

open Classical in
include hlam hmult hpos in
/-- **One orbit term with the convergence factors**. -/
theorem orbit_term_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') (O : FinOrbit Q₀ T₀ Ξ) :
    muFin Q₀ (fun _ => 1) (KSO Q₀) /
        muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)) =
      (∏ v ∈ Bad, ENNReal.ofReal (lam v) * (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) /
          muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q')))) *
        ENNReal.ofReal ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aL v) := by
  obtain ⟨b', hrel, hgood⟩ := exists_goodRep Q₀ hQ T₀ Ξ D hT hn' (Quotient.out O)
  have hO : O = Quotient.mk _ b' := by
    conv_lhs => rw [← Quotient.out_eq O]
    exact Quotient.sound hrel
  show _ / muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (Quotient.out O).1) = _
  rw [← muFin_orbitStab_congr_lam Q₀ hQ T₀ Ξ D lam hlam hmult hpos hn' _ _ hrel,
    orbitStab_eq_boxSO Q₀ hQ T₀ Ξ D hT b'.1 hgood]
  have hU : ∀ v ∈ Bad, MeasurableSet
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) :=
    fun v _ => (isOpen_orbitStab_loc v Q₀ T₀ fr _).measurableSet
  rw [muFin_boxSO_split D.Q'' D.hQ'' hlam hmult Bad _ hU]
  rw [muFin_KSO, finFactor_one Q₀ hQ, ← finFactor_one Q₀ hQ]
  have hKa : ENNReal.ofReal (finFactor Q₀ fun _ => 1) =
      (∏ v ∈ Bad, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))) *
        ENNReal.ofReal (∏' v, if v ∈ Bad then 1 else aSO Q₀ v) := by
    rw [finFactor, show (fun v => (muLocSO v Q₀ ((fun _ => (1 : ℝ)) v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal) =
      aSO Q₀ from rfl, tprod_eq_prod_mul_tprod_ite (aSO Q₀) (multipliable_aSO hN Q₀ hQ) Bad
        (fun v _ => (aSO_pos Q₀ hQ v).ne'),
      ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => (aSO_pos Q₀ hQ v).le),
      ENNReal.ofReal_prod_of_nonneg fun v _ => (aSO_pos Q₀ hQ v).le]
    simp only [ofReal_aSO]
  rw [hKa]
  have hposL := tprod_ite_aL_pos Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos
  have hloc : ∀ v ∈ Bad, muLocSO v D.Q'' 1
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) =
      muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q')) := by
    intro v _
    rw [hO, finToLoc_eq]
    exact muLocSO_orbitStab_eq v Q₀ T₀ fr hT D.hQ'' hn' _ _ rfl
  have hU0 : ∀ v ∈ Bad, muLocSO v D.Q'' (lam v)
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) ≠ 0 := by
    intro v _
    have := isHaarMeasure_muLocSO v (fr).Q' D.hQ''
    rw [muLocSO_apply_lam D.Q'' v (hlam v)]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (inv_pos.2 (hlam v))).ne'
      ((isOpen_orbitStab_loc v Q₀ T₀ fr _).measure_pos _ ⟨1, Subgroup.one_mem _⟩).ne'
  rw [ennreal_prod_div _ _ _ hU0 _ _ hposL]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun v hv => ?_) rfl
  rw [muLocSO_apply_lam D.Q'' v (hlam v), ennreal_div_ofReal_inv_mul _ _ (hlam v), hloc v hv]

open Classical in
theorem tsum_prod_finToLoc (hn' : 1 ≤ n') :
    ∑' O : FinOrbit Q₀ T₀ Ξ, ∏ v ∈ Bad, (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) /
          muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q'))) =
      ∏ v ∈ Bad, locOrbitSum v Q₀ T₀ fr := by
  set e := Equiv.ofBijective _ (finOrbitMap_bijective Q₀ hQ T₀ Ξ D hT hn')
  have : ∀ v : Bad, Fintype (LocOrbit v.1 Q₀ T₀ fr) := fun v =>
    @Fintype.ofFinite _ (finite_locOrbit v.1 Q₀ T₀ fr hQ hT hn')
  set w : ∀ v : HeightOneSpectrum (𝓞 F), LocOrbit v Q₀ T₀ fr → ℝ≥0∞ := fun v o =>
    muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) / muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr o : Set (SOv v (fr).Q'))
    with hw
  have h1 : ∀ O : FinOrbit Q₀ T₀ Ξ, (∏ v ∈ Bad, w v (finToLoc Q₀ hQ T₀ Ξ D hT O v)) =
      ∏ v : Bad, w v.1 (e O v) := fun O => (Finset.prod_coe_sort Bad _).symm
  rw [tsum_congr h1, e.tsum_eq (f := fun x => ∏ v : Bad, w v.1 (x v)), tsum_fintype, ← Fintype.prod_sum,
    ← Finset.prod_coe_sort Bad]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [locOrbitSum, tsum_fintype]

open Classical in
include hlam hmult hpos in
theorem frameOrbitSumLam_eq_prod (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    frameOrbitSumLam Q₀ hQ T₀ Ξ D lam = (∏ v ∈ Bad, ENNReal.ofReal (lam v) * locOrbitSum v Q₀ T₀ fr) *
      ENNReal.ofReal ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aL v) := by
  unfold frameOrbitSumLam
  rw [tsum_congr (orbit_term_lam Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN), ENNReal.tsum_mul_right]
  congr 1
  simp_rw [Finset.prod_mul_distrib]
  rw [ENNReal.tsum_mul_left, tsum_prod_finToLoc Q₀ hQ T₀ Ξ D hT hn']

open Classical in
include hlam hmult hpos in
theorem hasProd_frameLocFactor_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    HasProd (fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v)
      ((∏ v ∈ Bad, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) *
        ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aL v)) := by
  have ha0 : ∀ v, 0 < aL v := fun v =>
    ENNReal.toReal_pos (muLocSO_soStabSO_pos D.Q'' D.hQ'' v (hlam v))
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hA := multipliable_ite_one (aSO Q₀) (multipliable_aSO hN Q₀ hQ) Bad (fun v _ => (aSO_pos Q₀ hQ v).ne')
  have hB := multipliable_ite_one (fun v => aL v) hmult Bad (fun v _ => (ha0 v).ne')
  have hdiv := hA.hasProd.div₀ hB.hasProd (tprod_ite_aL_pos Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos).ne'
  have hg : (fun v => (if v ∈ Bad then 1 else aSO Q₀ v) / (if v ∈ Bad then 1 else aL v)) =
      fun v => if v ∈ Bad then 1 else frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v := by
    funext v
    by_cases hv : v ∈ Bad
    · simp [hv]
    · simp only [hv, ite_false]
      rw [frameLocFactor_good Q₀ hQ T₀ Ξ D hT hn' v hv, toReal_muLocSO_soStab_lam D.Q'' D.hQ'' v (hlam v)]
      have h1 := aSO_pos D.Q'' D.hQ'' v
      have h2 := hlam v
      field_simp
  rw [hg] at hdiv
  rw [← hdiv.tprod_eq]
  exact hasProd_prod_mul_tprod_ite _ Bad hdiv.multipliable

end LamHelpers

include hlam hmult hpos in
/-- The local factors with the convergence factors converge absolutely:
$\prod_\mathfrak p\beta_\mathfrak p|\det g|_\mathfrak p^{n'+1}|\det H_{T_0}|_\mathfrak p^{-n'}\lambda_\mathfrak p$. -/
theorem multipliable_frameLocFactor_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    Multipliable fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v :=
  (hasProd_frameLocFactor_lam Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN).multipliable

include hlam hmult hpos in
/-- **Weil's measure of the integral adelic frames with convergence factors on the stabilizer.** -/
theorem frameOrbitSum_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    frameOrbitSumLam Q₀ hQ T₀ Ξ D lam = ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) := by
  classical
  rw [(hasProd_frameLocFactor_lam Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN).tprod_eq,
    frameOrbitSumLam_eq_prod Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ =>
      mul_nonneg (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v) (hlam v).le),
    ENNReal.ofReal_prod_of_nonneg fun v _ =>
      mul_nonneg (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v) (hlam v).le]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [ENNReal.ofReal_mul (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v),
    ofReal_frameLocFactor Q₀ hQ T₀ Ξ D hT hn' v, mul_comm]


end Orbit

end QuadFormsKB.Tamagawa.Indefinite.IsoAlg
