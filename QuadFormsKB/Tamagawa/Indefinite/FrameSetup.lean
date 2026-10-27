/-
# The complement of the base vector of an adelic sphere setup

**Layer:** number fields, adeles. For the setup `S : AdelicSphereSetup Q₀ ρ` (base point $\xi$, integral
complement $G = [d\xi\mid G']$ with $Q_0\circ G = \langle m_0\rangle\perp Q'$, $\iota(h) = G\,\mathrm{diag}(1,h)\,G^{-1}$), the
vectors orthogonal to $\xi$ are the images of the complement coordinates under $G' = G e_{1..k}$ (`Gc`):

* `complRat` $x\mapsto$ the last $k$ coordinates of $G^{-1}x$; `Gc_mulVec_complRat`: $G'\,\mathrm{complRat}(x) = x$ for $x\perp\xi$;
  `bH_complRat`: the complement form of $Q'$ on these coordinates is that of $Q_0$ (`Gc_hes`: $G'^{\mathsf T}HG' = H'$);
* `complA` $: \mathbb A^k\to\mathbb A^{k+1}$, $y\mapsto G'y$ (placewise), injective, with **`iota_smul_complA`**
  $\iota(h)\,G'y = G'(hy)$: the embedding of the complement is $SO(Q')(\mathbb A)$-equivariant.

These are the data of the induction step of the frame coordinates (`FrameTower.lean`). Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereFibProof
import QuadFormsKB.Tamagawa.Measure.Weil.NrdSurjective

open MeasureTheory Set Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-! ### A block identity -/

section Block

variable {R : Type*} [Field R] {k : ℕ}

/-- $\mathrm{diag}(1, h)$ maps the last $k$ coordinates by $h$: $\mathrm{diag}(1,h)\,E = E\,h$, $E = 1_{k+1}$ restricted to the
columns $1, \dots, k$. -/
theorem cornerMat_mul_submatrix_succ (h : Matrix (Fin k) (Fin k) R) :
    cornerMat 1 h * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R).submatrix id Fin.succ =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R).submatrix id Fin.succ * h := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Matrix.mul_apply, Matrix.one_apply, (Fin.succ_ne_zero _).symm]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Fin.succ_inj]

theorem submatrix_succ_eq_mul (P : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    P.submatrix id Fin.succ = P * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R).submatrix id Fin.succ := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- **$G\,\mathrm{diag}(1,h)\,G^{-1}\cdot G' = G'h$.** -/
theorem conjBlock_mul_submatrix_succ {P : Matrix (Fin (k + 1)) (Fin (k + 1)) R} (hP : IsUnit P.det)
    (h : Matrix (Fin k) (Fin k) R) : conjBlock P h * P.submatrix id Fin.succ = P.submatrix id Fin.succ * h := by
  rw [submatrix_succ_eq_mul P]
  unfold conjBlock
  rw [show P * cornerMat 1 h * P⁻¹ * (P * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R).submatrix id Fin.succ) =
      P * cornerMat 1 h * (P⁻¹ * P) * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R).submatrix id Fin.succ by
    simp only [Matrix.mul_assoc], nonsing_inv_mul P hP, Matrix.mul_one, Matrix.mul_assoc P (cornerMat 1 h),
    cornerMat_mul_submatrix_succ, Matrix.mul_assoc]

end Block

variable {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ)

/-- The integral complement matrix over $F$. -/
abbrev GF : Matrix (Fin (k + 1)) (Fin (k + 1)) F := S.C.G.map (algebraMap (𝓞 F) F)

/-- **The complement columns** $G' = G\,e_{1..k}$ over $F$. -/
abbrev Gc : Matrix (Fin (k + 1)) (Fin k) F := S.GF.submatrix id Fin.succ

theorem isUnit_det_GF : IsUnit S.GF.det := by
  show IsUnit (S.C.G.map (algebraMap (𝓞 F) F)).det
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.C.hG)

/-- $G^{\mathsf T}HG = \mathrm{diag}(2m_0, H')$ over $F$. -/
theorem GF_hes :
    S.GFᵀ * (QF).hessian * S.GF = cornerMat (algebraMap (𝓞 F) F (2 * S.C.m₀)) (S.C.Q'.map (algebraMap (𝓞 F) F)).hessian := by
  have h := S.PAt_hes (RingHom.id F)
  simpa [AdelicSphereSetup.PAt_val, hesAt] using h

/-- $G'^{\mathsf T}HG' = H'$. -/
theorem Gc_hes : S.Gcᵀ * (QF).hessian * S.Gc = (S.C.Q'.map (algebraMap (𝓞 F) F)).hessian := by
  have h := congrArg (fun M => M.submatrix Fin.succ Fin.succ) S.GF_hes
  simp only [cornerMat_submatrix_succ] at h
  rw [← h]
  ext i j
  simp [Matrix.mul_apply]

/-- $G'^{\mathsf T}H\xi = 0$. -/
theorem Gc_hes_ξ : (S.Gcᵀ * (QF).hessian) *ᵥ S.ξ.1 = 0 := by
  have hd : algebraMap (𝓞 F) F S.C.d ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.C.hd
  have hcol : S.GF *ᵥ (e0 : Fin (k + 1) → F) = algebraMap (𝓞 F) F S.C.d • S.ξ.1 := by
    have := S.PAt_mulVec_e0 (RingHom.id F)
    simpa [AdelicSphereSetup.PAt_val] using this
  have h : (S.GFᵀ * (QF).hessian * S.GF) *ᵥ (e0 : Fin (k + 1) → F) =
      cornerMat (algebraMap (𝓞 F) F (2 * S.C.m₀)) (S.C.Q'.map (algebraMap (𝓞 F) F)).hessian *ᵥ
        (e0 : Fin (k + 1) → F) := by rw [S.GF_hes]
  rw [← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul] at h
  funext j
  have hj := congrFun h j.succ
  have hr : (cornerMat (algebraMap (𝓞 F) F (2 * S.C.m₀)) (S.C.Q'.map (algebraMap (𝓞 F) F)).hessian *ᵥ
      (e0 : Fin (k + 1) → F)) j.succ = 0 := by
    simp [cornerMat, mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply]
  rw [hr, Pi.smul_apply, smul_eq_mul] at hj
  have h3 := (mul_eq_zero.mp hj).resolve_left hd
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h3

/-- **The complement coordinates** of $x\in F^{k+1}$: the last $k$ coordinates of $G^{-1}x$. -/
def complRat (x : Fin (k + 1) → F) : Fin k → F := fun j => (S.GF⁻¹ *ᵥ x) j.succ

/-- For $x\perp\xi$, $G'\,\mathrm{complRat}(x) = x$. -/
theorem Gc_mulVec_complRat {x : Fin (k + 1) → F} (hx : bH (QF).hessian S.ξ.1 x = 0) :
    S.Gc *ᵥ S.complRat x = x := by
  set u := S.GF⁻¹ *ᵥ x with hu
  have hxu : x = S.GF *ᵥ u := by
    rw [hu, Matrix.mulVec_mulVec, mul_nonsing_inv _ S.isUnit_det_GF, Matrix.one_mulVec]
  have hm : algebraMap (𝓞 F) F (2 * S.C.m₀) ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (mul_ne_zero two_ne_zero S.C.hm)
  have hd : algebraMap (𝓞 F) F S.C.d ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.C.hd
  have hcol : S.GF *ᵥ (e0 : Fin (k + 1) → F) = algebraMap (𝓞 F) F S.C.d • S.ξ.1 := by
    have := S.PAt_mulVec_e0 (RingHom.id F)
    simpa [AdelicSphereSetup.PAt_val] using this
  -- the first coordinate of `u` vanishes
  have hu0 : u 0 = 0 := by
    have h1 : ((S.GFᵀ * (QF).hessian) *ᵥ x) 0 = algebraMap (𝓞 F) F (2 * S.C.m₀) * u 0 := by
      rw [hxu, Matrix.mulVec_mulVec, S.GF_hes]
      simp [cornerMat, mulVec, dotProduct, Fin.sum_univ_succ]
    have h2 : ((S.GFᵀ * (QF).hessian) *ᵥ x) 0 = algebraMap (𝓞 F) F S.C.d * bH (QF).hessian S.ξ.1 x := by
      have : ((S.GFᵀ * (QF).hessian) *ᵥ x) 0 = (S.GF *ᵥ (e0 : Fin (k + 1) → F)) ⬝ᵥ ((QF).hessian *ᵥ x) := by
        rw [← Matrix.mulVec_mulVec]
        simp [mulVec, dotProduct, Pi.single_apply]
      rw [this, hcol, smul_dotProduct, smul_eq_mul, bH]
    rw [hx, mul_zero, h1] at h2
    exact (mul_eq_zero.mp h2).resolve_left hm
  have hc : S.complRat x = fun j => u j.succ := rfl
  clear_value u
  rw [hc]
  conv_rhs => rw [hxu]
  funext i
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, hu0, mul_zero, zero_add, Matrix.submatrix_apply, id]

/-- The complement form on the complement coordinates: $b'(\mathrm{complRat}\,x, \mathrm{complRat}\,y) = b(x, y)$. -/
theorem bH_complRat {x y : Fin (k + 1) → F} (hx : bH (QF).hessian S.ξ.1 x = 0)
    (hy : bH (QF).hessian S.ξ.1 y = 0) :
    bH (S.C.Q'.map (algebraMap (𝓞 F) F)).hessian (S.complRat x) (S.complRat y) = bH (QF).hessian x y := by
  conv_rhs => rw [← S.Gc_mulVec_complRat hx, ← S.Gc_mulVec_complRat hy]
  rw [← S.Gc_hes]
  simp only [bH, Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, Matrix.vecMul_mulVec, Matrix.vecMul_transpose]

theorem qF_complRat {x : Fin (k + 1) → F} (hx : bH (QF).hessian S.ξ.1 x = 0) :
    qF S.C.Q' (S.complRat x) = qF Q₀ x := by
  have h := S.bH_complRat hx hx
  rw [← qH_eq_bH, ← qH_eq_bH, qH_hessian, qH_hessian] at h
  exact mul_left_cancel₀ two_ne_zero h

/-- **The complement embedding** $\mathbb A^k\to\mathbb A^{k+1}$, $y\mapsto G'y$. -/
def complA (y : AdeleSpace F (Fin k)) : AdeleSpace F (Fin (k + 1)) := fun i => ∑ j, diag F (S.Gc i j) * y j

/-- `diag F` is multiplicative. -/
theorem diag_mul (a b : F) : diag F (a * b) = diag F a * diag F b := by
  refine Prod.ext ?_ ?_
  · rw [diag_fst, Prod.fst_mul, diag_fst, diag_fst, map_mul]
  · rw [diag_snd, Prod.snd_mul, diag_snd, diag_snd, map_mul]

/-- The complex component of `diag F c`. -/
theorem diag_fst_snd (c : F) (w : {w : InfinitePlace F // w.IsComplex}) :
    (diag F c).1.2 w = w.1.embedding c :=
  mixedEmbedding.mixedEmbedding_apply_isComplex F c w

theorem complA_diagVec (x : Fin k → F) : S.complA (diagVec F (Fin k) x) = diagVec F (Fin (k + 1)) (S.Gc *ᵥ x) := by
  funext i
  simp only [complA, diagVec_apply, mulVec, dotProduct, ← diag_mul, map_sum]

/-- The component of `complA y` at a real place: $G'_w y_w$. -/
theorem adR_complA (y : AdeleSpace F (Fin k)) (w : {w : InfinitePlace F // w.IsReal}) :
    (fun i => (S.complA y i).1.1 w) = S.Gc.map (σR w) *ᵥ fun j => (y j).1.1 w := by
  funext i
  simp [complA, mulVec, dotProduct, Prod.fst_sum, Finset.sum_apply, diag_fst_fst]

/-- The component of `complA y` at a complex place. -/
theorem adC_complA (y : AdeleSpace F (Fin k)) (w : {w : InfinitePlace F // w.IsComplex}) :
    (fun i => (S.complA y i).1.2 w) = S.Gc.map (σC w) *ᵥ fun j => (y j).1.2 w := by
  funext i
  simp [complA, mulVec, dotProduct, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, diag_fst_snd]

/-- The component of `complA y` at a finite place. -/
theorem adV_complA (y : AdeleSpace F (Fin k)) (v : HeightOneSpectrum (𝓞 F)) :
    (fun i => (S.complA y i).2 v) = S.Gc.map (σV v) *ᵥ fun j => (y j).2 v := by
  funext i
  change evalAt v ((∑ j, diag F (S.Gc i j) * y j).2) = _
  rw [Prod.snd_sum, map_sum]
  simp only [mulVec, dotProduct, diag_snd, Prod.snd_mul, map_mul, Matrix.map_apply]
  exact Finset.sum_congr rfl fun x _ => rfl

/-- The local matrices of $\iota(h)$: $G\,\mathrm{diag}(1,h)\,G^{-1}$ (real places). -/
theorem matR_iota (h : SOAdele S.C.Q') (w : {w : InfinitePlace F // w.IsReal}) :
    matR Q₀ (S.iota h) w = conjBlock (S.PAt (σR w)).val (matR S.C.Q' h w) :=
  conjBlockGL_val _ _

theorem matC_iota (h : SOAdele S.C.Q') (w : {w : InfinitePlace F // w.IsComplex}) :
    matC Q₀ (S.iota h) w = conjBlock (S.PAt (σC w)).val (matC S.C.Q' h w) :=
  conjBlockGL_val _ _

theorem matV_iota (h : SOAdele S.C.Q') (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀ (S.iota h) v = conjBlock (S.PAt (σV v)).val (matV S.C.Q' h v) :=
  S.iotaV_val v _

/-- $G'$ at an embedding is the complement block of $G$ at that embedding. -/
theorem Gc_map {K : Type*} [Field K] (σ : F →+* K) : S.Gc.map σ = (S.PAt σ).val.submatrix id Fin.succ := by
  ext i j; simp [AdelicSphereSetup.PAt_val]

/-- $\iota(h)$ acts on the complement columns by $h$: $\iota(h)_\sigma G'_\sigma = G'_\sigma h_\sigma$ (finite places). -/
theorem matV_iota_mul_Gc (h : SOAdele S.C.Q') (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀ (S.iota h) v * S.Gc.map (σV v) = S.Gc.map (σV v) * matV S.C.Q' h v := by
  rw [matV_iota, Gc_map]; exact conjBlock_mul_submatrix_succ (S.isUnit_det_PAt _) _

theorem matR_iota_mul_Gc (h : SOAdele S.C.Q') (w : {w : InfinitePlace F // w.IsReal}) :
    matR Q₀ (S.iota h) w * S.Gc.map (σR w) = S.Gc.map (σR w) * matR S.C.Q' h w := by
  rw [matR_iota, Gc_map]; exact conjBlock_mul_submatrix_succ (S.isUnit_det_PAt _) _

theorem matC_iota_mul_Gc (h : SOAdele S.C.Q') (w : {w : InfinitePlace F // w.IsComplex}) :
    matC Q₀ (S.iota h) w * S.Gc.map (σC w) = S.Gc.map (σC w) * matC S.C.Q' h w := by
  rw [matC_iota, Gc_map]; exact conjBlock_mul_submatrix_succ (S.isUnit_det_PAt _) _

/-- **The complement embedding is equivariant**: $\iota(h)\,G'y = G'(hy)$. -/
theorem iota_smul_complA (h : SOAdele S.C.Q') (y : AdeleSpace F (Fin k)) :
    S.iota h • S.complA y = S.complA (h • y) := by
  funext i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) (Subtype.ext (funext fun v => ?_))
  · show (matR Q₀ (S.iota h) w *ᵥ fun j => (S.complA y j).1.1 w) i = _
    rw [S.adR_complA y w, Matrix.mulVec_mulVec, S.matR_iota_mul_Gc h w, ← Matrix.mulVec_mulVec]
    exact (congrFun (S.adR_complA (h • y) w) i).symm
  · show (matC Q₀ (S.iota h) w *ᵥ fun j => (S.complA y j).1.2 w) i = _
    rw [S.adC_complA y w, Matrix.mulVec_mulVec, S.matC_iota_mul_Gc h w, ← Matrix.mulVec_mulVec]
    exact (congrFun (S.adC_complA (h • y) w) i).symm
  · show (matV Q₀ (S.iota h) v *ᵥ fun j => (S.complA y j).2 v) i = _
    rw [S.adV_complA y v, Matrix.mulVec_mulVec, S.matV_iota_mul_Gc h v, ← Matrix.mulVec_mulVec]
    exact (congrFun (S.adV_complA (h • y) v) i).symm

/-- A left inverse of $G'$: the rows $1,\dots,k$ of $G^{-1}$. -/
abbrev Lc : Matrix (Fin k) (Fin (k + 1)) F := S.GF⁻¹.submatrix Fin.succ id

theorem Lc_mul_Gc : S.Lc * S.Gc = 1 := by
  have h : S.GF⁻¹ * S.GF = 1 := nonsing_inv_mul _ S.isUnit_det_GF
  ext i j
  have := congrFun (congrFun h i.succ) j.succ
  simpa [Matrix.mul_apply, Matrix.one_apply, Fin.succ_inj] using this

theorem cancel_Gc_map {K : Type*} [Field K] (σ : F →+* K) {a b : Fin k → K}
    (h : S.Gc.map σ *ᵥ a = S.Gc.map σ *ᵥ b) : a = b := by
  have h1 : S.Lc.map σ * S.Gc.map σ = 1 := by
    rw [← Matrix.map_mul, S.Lc_mul_Gc]; exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have := congrArg (fun z => S.Lc.map σ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this

/-- The complement embedding is injective ($G$ is invertible). -/
theorem complA_injective : Function.Injective S.complA := by
  intro y z hyz
  have hR : ∀ w, (fun j => (y j).1.1 w) = fun j => (z j).1.1 w := fun w =>
    S.cancel_Gc_map (σR w) (by rw [← S.adR_complA, ← S.adR_complA, hyz])
  have hC : ∀ w, (fun j => (y j).1.2 w) = fun j => (z j).1.2 w := fun w =>
    S.cancel_Gc_map (σC w) (by rw [← S.adC_complA, ← S.adC_complA, hyz])
  have hV : ∀ v, (fun j => (y j).2 v) = fun j => (z j).2 v := fun v =>
    S.cancel_Gc_map (σV v) (by rw [← S.adV_complA, ← S.adV_complA, hyz])
  funext j
  exact Prod.ext (Prod.ext (funext fun w => congrFun (hR w) j) (funext fun w => congrFun (hC w) j))
    (Subtype.ext (funext fun v => congrFun (hV v) j))

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil
