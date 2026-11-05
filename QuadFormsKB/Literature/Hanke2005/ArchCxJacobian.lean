/-
# Hanke 2005, §4.3: the Jacobian of the coordinates $\Psi$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

For the map $\Psi(u, Y, \sigma) = (1 - iu)\,Y\,(1 - i\sigma)$ of `ArchCxParam.lean` (in column coordinates, as `psi`)
this file proves that $\Psi$ is differentiable with an explicit derivative `psiD p`, that `psi` is continuous, and
computes the absolute value of the real Jacobian determinant:
$$|\det D\Psi| = 2^{n(n-1)/2}\,|\det Y|^{-1}\,\det(1+\sigma^2)^n\,\bigl|\det\varphi_1(T,(1+\sigma^2)^{-1})\bigr|,\qquad
T = {}^tY(1 - {}^tuu)Y,$$
valid when $\det(1 - {}^tuu)\ne 0$.

**Proves**
* `psiD p`: the derivative of `psi` at `p`; `hasFDerivAt_psi`;
* `abs_det_psiD`: the Jacobian formula (hypotheses $\det Y\ne0$, $\det(1-{}^tuu)\ne0$);
* `continuous_det_phi1`, `continuous_psi`.

All auxiliary material is in the namespace `QuadFormsKB.Hanke2005.ArchCx.Jac`.
-/
import QuadFormsKB.Literature.Hanke2005.ArchCxParam
import QuadFormsKB.Literature.Hanke2005.InvarianceZC

open Matrix Complex

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

namespace Jac

section Triang

variable {M M' : Type*} [AddCommGroup M] [Module ℝ M] [Module.Free ℝ M] [Module.Finite ℝ M]
  [AddCommGroup M'] [Module ℝ M'] [Module.Free ℝ M'] [Module.Finite ℝ M']

/-- The shear $(x,y)\mapsto(x+Ky,y)$. -/
def shear (K : M' →ₗ[ℝ] M) : M × M' →ₗ[ℝ] M × M' :=
  LinearMap.prod (LinearMap.fst ℝ M M' + K ∘ₗ LinearMap.snd ℝ M M') (LinearMap.snd ℝ M M')

theorem det_shear (K : M' →ₗ[ℝ] M) : LinearMap.det (shear K) = 1 := by
  classical
  let b := Module.Free.chooseBasis ℝ M
  let b' := Module.Free.chooseBasis ℝ M'
  rw [← LinearMap.det_toMatrix (b.prod b')]
  have : LinearMap.toMatrix (b.prod b') (b.prod b') (shear K) =
      Matrix.fromBlocks 1 (LinearMap.toMatrix b' b K) 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply, shear, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [this, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The block-triangular map $(x,y)\mapsto(ax+Ky,dy)$. -/
def triang (a : M →ₗ[ℝ] M) (K : M' →ₗ[ℝ] M) (d : M' →ₗ[ℝ] M') : M × M' →ₗ[ℝ] M × M' :=
  LinearMap.prod (a ∘ₗ LinearMap.fst ℝ M M' + K ∘ₗ LinearMap.snd ℝ M M') (d ∘ₗ LinearMap.snd ℝ M M')

theorem triang_eq (a : M →ₗ[ℝ] M) (K : M' →ₗ[ℝ] M) (d : M' →ₗ[ℝ] M') :
    triang a K d = LinearMap.prodMap LinearMap.id d ∘ₗ shear K ∘ₗ LinearMap.prodMap a LinearMap.id := by
  ext <;> simp [triang, shear]

theorem det_triang (a : M →ₗ[ℝ] M) (K : M' →ₗ[ℝ] M) (d : M' →ₗ[ℝ] M') :
    LinearMap.det (triang a K d) = LinearMap.det a * LinearMap.det d := by
  rw [triang_eq, LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_prodMap,
    det_shear]
  simp [mul_comm]

end Triang


/-! ### Real matrices -/

/-- Real $n\times n$ matrices. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

section RealMul

variable {n : ℕ}

/-- Column coordinates of a real matrix. -/
def trE : Mat n ≃ₗ[ℝ] (Fin n → Fin n → ℝ) where
  toFun X := fun j i => X i j
  invFun Y := Matrix.of fun i j => Y j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Row coordinates of a real matrix (the identity, with the `Pi` module structure). -/
def rowE : Mat n ≃ₗ[ℝ] (Fin n → Fin n → ℝ) where
  toFun X := fun i k => X i k
  invFun Y := Matrix.of fun i k => Y i k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem rowE_apply (X : Mat n) (i k : Fin n) : rowE X i k = X i k := rfl

@[simp] theorem trE_apply (X : Mat n) (j i : Fin n) : trE X j i = X i j := rfl

theorem det_of_conj {P : Type*} [AddCommGroup P] [Module ℝ P] (f : Mat n →ₗ[ℝ] Mat n) (g : P →ₗ[ℝ] P)
    (e : Mat n ≃ₗ[ℝ] P) (h : ∀ X, g (e X) = e (f X)) : LinearMap.det f = LinearMap.det g := by
  rw [← LinearMap.det_conj f e]
  congr 1
  apply LinearMap.ext; intro Y
  obtain ⟨X, rfl⟩ := e.surjective Y
  simp [← h]

/-- $\det(X\mapsto AX) = \det(A)^n$ on $M_n(\mathbb R)$. -/
theorem det_mulLeft (A : Mat n) :
    LinearMap.det (LinearMap.mulLeft ℝ A : Mat n →ₗ[ℝ] Mat n) = A.det ^ n := by
  rw [det_of_conj (LinearMap.mulLeft ℝ A)
    (LinearMap.pi fun j => (Matrix.toLin' A).comp (LinearMap.proj j)) trE ?_]
  · rw [LinearMap.det_pi, LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro X
    funext j i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- $\det(X\mapsto XA) = \det(A)^n$ on $M_n(\mathbb R)$. -/
theorem det_mulRight (A : Mat n) :
    LinearMap.det (LinearMap.mulRight ℝ A : Mat n →ₗ[ℝ] Mat n) = A.det ^ n := by
  rw [det_of_conj (LinearMap.mulRight ℝ A)
    (LinearMap.pi fun i => (Matrix.toLin' Aᵀ).comp (LinearMap.proj i)) rowE ?_]
  · rw [LinearMap.det_pi, LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      det_transpose]
  · intro X
    funext i k
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- The matrix with given strictly-lower and upper-with-diagonal coordinates. -/
def kinv (l : LIdx n → ℝ) (t : UIdx n → ℝ) : Mat n :=
  Matrix.of fun i j => if h : j < i then l ⟨(i, j), h⟩ else t ⟨(i, j), not_lt.mp h⟩

/-- A real matrix as its pair of lower and upper coordinates. -/
def kap : Mat n ≃ₗ[ℝ] (LIdx n → ℝ) × (UIdx n → ℝ) where
  toFun y := (lowerOf y, upperOf y)
  invFun p := kinv p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    ext i j
    by_cases h : j < i <;> simp [kinv, lowerOf, upperOf, h]
  right_inv p := by
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · obtain ⟨⟨i, j⟩, h⟩ := q
      simp [kinv, lowerOf, h]
    · obtain ⟨⟨i, j⟩, h⟩ := q
      simp [kinv, upperOf, not_lt.mpr h]

/-- $\iota$-comparison: $V\mapsto V + J V$ where $(JV)_{ik} = \operatorname{sgn}(i-k)V_{ki}$. -/
def Jm : Mat n →ₗ[ℝ] Mat n where
  toFun V := Matrix.of fun i k => if k < i then V k i else if i < k then -V k i else 0
  map_add' V W := by
    ext i k
    simp only [of_apply, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c V := by
    ext i k
    simp only [of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem Jm_apply (V : Mat n) (i k : Fin n) :
    Jm V i k = if k < i then V k i else if i < k then -V k i else 0 := rfl

/-- The map $\iota(V) = \mathrm{skewOf}(\mathrm{lowerOf}\,V) + \mathrm{symU}(\mathrm{upperOf}\,V)$. -/
def iota : Mat n →ₗ[ℝ] Mat n := LinearMap.id + Jm

theorem iota_apply (V : Mat n) : iota V = skewOf (lowerOf V) + symU (upperOf V) := by
  ext i k
  simp only [iota, LinearMap.add_apply, LinearMap.id_apply, Matrix.add_apply, Jm_apply, skewOf, symU,
    lowerOf, upperOf, of_apply]
  rcases lt_trichotomy k i with h | h | h
  · simp [h, h.not_ge]
  · subst h; simp
  · simp [h, h.not_gt, h.le]; ring

theorem Jm_transpose (V : Mat n) : (Jm Vᵀ)ᵀ = -Jm V := by
  ext i k
  simp only [transpose_apply, Jm_apply, Matrix.neg_apply]
  rcases lt_trichotomy k i with h | h | h
  · simp [h, h.not_gt]
  · subst h; simp
  · simp [h, h.not_gt]

theorem Jm_Jm (V : Mat n) (i k : Fin n) : Jm (Jm V) i k = if i = k then 0 else -V i k := by
  simp only [Jm_apply]
  rcases lt_trichotomy k i with h | h | h
  · simp [h, h.not_gt, h.ne']
  · subst h; simp
  · simp [h, h.not_gt, h.ne]

/-- The diagonal map multiplying off-diagonal entries by $2$. -/
def dg : Mat n →ₗ[ℝ] Mat n where
  toFun V := Matrix.of fun i k => (if i = k then 1 else 2) * V i k
  map_add' V W := by ext i k; simp [mul_add]
  map_smul' c V := by ext i k; simp; ring

theorem det_dg : LinearMap.det (dg : Mat n →ₗ[ℝ] Mat n) = 2 ^ (n * (n - 1)) := by
  rw [det_of_conj dg
    (LinearMap.pi fun i => (Matrix.toLin' (Matrix.diagonal fun k : Fin n => if i = k then (1 : ℝ) else 2)).comp
      (LinearMap.proj i)) rowE ?_]
  · rw [LinearMap.det_pi]
    simp only [LinearMap.det_toLin', Matrix.det_diagonal]
    have h : ∀ i : Fin n, ∏ k : Fin n, (if i = k then (1 : ℝ) else 2) = 2 ^ (n - 1) := by
      intro i
      rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
      congr 1
      have : Finset.filter (fun k : Fin n => ¬ i = k) Finset.univ = Finset.univ.erase i := by
        ext k; simp [eq_comm]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  · intro X
    funext i k
    simp [dg, Matrix.mulVec_diagonal]

theorem iota_mul_iota' : ((LinearMap.id + Jm : Mat n →ₗ[ℝ] Mat n)) ∘ₗ (LinearMap.id - Jm) = dg := by
  apply LinearMap.ext; intro V; ext i k
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    Matrix.add_apply, Matrix.sub_apply, Jm_Jm, dg, of_apply]
  by_cases h : i = k <;> simp [h] <;> ring

/-- Conjugating $\mathrm{id}+J$ by transposition gives $\mathrm{id}-J$. -/
theorem det_one_sub_Jm : LinearMap.det (LinearMap.id - Jm : Mat n →ₗ[ℝ] Mat n) =
    LinearMap.det (LinearMap.id + Jm : Mat n →ₗ[ℝ] Mat n) := by
  rw [← LinearMap.det_conj (LinearMap.id + Jm : Mat n →ₗ[ℝ] Mat n) (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ)]
  congr 1
  apply LinearMap.ext; intro V; ext i k
  have := congrFun (congrFun (Jm_transpose V) i) k
  simp only [Matrix.neg_apply] at this
  simp [Matrix.transposeLinearEquiv, Matrix.transpose_apply] at *
  linarith

theorem det_iota_sq : LinearMap.det (iota : Mat n →ₗ[ℝ] Mat n) ^ 2 = 2 ^ (n * (n - 1)) := by
  have h := congrArg LinearMap.det (iota_mul_iota' (n := n))
  rw [LinearMap.det_comp, det_dg, det_one_sub_Jm] at h
  rw [iota, sq, ← h]

theorem abs_det_iota : |LinearMap.det (iota : Mat n →ₗ[ℝ] Mat n)| = 2 ^ (n * (n - 1) / 2) := by
  have h2 : n * (n - 1) = 2 * (n * (n - 1) / 2) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_pred_self n
    omega
  have h := det_iota_sq (n := n)
  have h3 : |LinearMap.det (iota : Mat n →ₗ[ℝ] Mat n)| ^ 2 = (2 ^ (n * (n - 1) / 2)) ^ 2 := by
    rw [sq_abs, h, ← pow_mul]
    congr 1
    omega
  exact (sq_eq_sq₀ (abs_nonneg _) (by positivity)).mp h3

end RealMul

/-! ### The skew/symmetric splitting -/

section SkewSym

variable {n : ℕ}

theorem skewOf_transpose (l : LIdx n → ℝ) : (skewOf l)ᵀ = -skewOf l := by
  ext i k
  simp only [transpose_apply, skewOf, of_apply, Matrix.neg_apply]
  rcases lt_trichotomy i k with h | h | h
  · simp [h, h.not_gt]
  · subst h; simp
  · simp [h, h.not_gt]

theorem symU_transpose (t : UIdx n → ℝ) : (symU t)ᵀ = symU t := by
  ext i k
  simp only [transpose_apply, symU, of_apply]
  rcases lt_trichotomy i k with h | h | h
  · simp [h.le, h.not_ge]
  · subst h; simp
  · simp [h.le, h.not_ge]

/-- $\mathrm{skew}(W)=\tfrac12(W-{}^tW)$ as a linear map. -/
def skewP : Mat n →ₗ[ℝ] Mat n :=
  (1 / 2 : ℝ) • (LinearMap.id - (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap)

/-- $\mathrm{sym}(W)=\tfrac12(W+{}^tW)$ as a linear map. -/
def symP : Mat n →ₗ[ℝ] Mat n :=
  (1 / 2 : ℝ) • (LinearMap.id + (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap)

theorem skewP_apply (W : Mat n) : skewP W = (1 / 2 : ℝ) • (W - Wᵀ) := rfl

theorem symP_apply (W : Mat n) : symP W = (1 / 2 : ℝ) • (W + Wᵀ) := rfl

theorem skewP_add {K S : Mat n} (hK : Kᵀ = -K) (hS : Sᵀ = S) : skewP (K + S) = K := by
  rw [skewP_apply, transpose_add, hK, hS]; module

theorem symP_add {K S : Mat n} (hK : Kᵀ = -K) (hS : Sᵀ = S) : symP (K + S) = S := by
  rw [symP_apply, transpose_add, hK, hS]; module

/-- $C_Y(W)={}^tY\,\mathrm{skew}(W)\,Y+\mathrm{sym}(W)$. -/
def Cm (Y : Mat n) : Mat n →ₗ[ℝ] Mat n :=
  (LinearMap.mulLeft ℝ Yᵀ ∘ₗ LinearMap.mulRight ℝ Y) ∘ₗ skewP + symP

theorem Cm_apply (Y W : Mat n) : Cm Y W = Yᵀ * skewP W * Y + symP W := by
  simp [Cm, Matrix.mul_assoc]

/-- $C_Y$ on skew-plus-symmetric matrices. -/
theorem Cm_add {Y K S : Mat n} (hK : Kᵀ = -K) (hS : Sᵀ = S) : Cm Y (K + S) = Yᵀ * K * Y + S := by
  rw [Cm_apply, skewP_add hK hS, symP_add hK hS]

theorem transpose_conj_skew {Y K : Mat n} (hK : Kᵀ = -K) : (Yᵀ * K * Y)ᵀ = -(Yᵀ * K * Y) := by
  rw [transpose_mul, transpose_mul, hK, transpose_transpose]
  simp [Matrix.mul_assoc]

/-- $C_Y\circ\iota=\iota\circ\widetilde C_Y$ with $\widetilde C_Y$ conjugate to $(\mathrm{dAct}\,Y)\times\mathrm{id}$. -/
def Cc (Y : Mat n) : Mat n →ₗ[ℝ] Mat n :=
  (kap (n := n)).symm.toLinearMap ∘ₗ LinearMap.prodMap (dAct Y) LinearMap.id ∘ₗ (kap (n := n)).toLinearMap

theorem det_Cc (Y : Mat n) : LinearMap.det (Cc Y) = Y.det ^ (n - 1) := by
  have := LinearMap.det_conj (LinearMap.prodMap (dAct Y) (LinearMap.id : (UIdx n → ℝ) →ₗ[ℝ] _)) (kap (n := n)).symm
  rw [LinearEquiv.symm_symm] at this
  rw [Cc, this, LinearMap.det_prodMap, det_dAct, LinearMap.det_id, mul_one]

theorem Cm_iota (Y : Mat n) (y : Mat n) : Cm Y (iota y) = iota (Cc Y y) := by
  have h : (kap (n := n)) (Cc Y y) = (dAct Y (lowerOf y), upperOf y) := by
    simp only [Cc, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hl : lowerOf (Cc Y y) = dAct Y (lowerOf y) := congrArg Prod.fst h
  have hu : upperOf (Cc Y y) = upperOf y := congrArg Prod.snd h
  rw [iota_apply, iota_apply, Cm_add (skewOf_transpose _) (symU_transpose _), hl, hu, dAct_apply,
    skewOf_lowerOf (transpose_conj_skew (skewOf_transpose _))]

theorem det_Cm_iota (Y : Mat n) :
    LinearMap.det (Cm Y ∘ₗ iota) = Y.det ^ (n - 1) * LinearMap.det (iota : Mat n →ₗ[ℝ] Mat n) := by
  have : Cm Y ∘ₗ iota = iota ∘ₗ Cc Y := LinearMap.ext fun y => Cm_iota Y y
  rw [this, LinearMap.det_comp, det_Cc, mul_comm]

end SkewSym

/-! ### The derivative of $\Psi$ -/

section Deriv

variable {n : ℕ}

/-- Complex matrices as a `Pi` type (the type on which derivatives are taken). -/
abbrev Ev (n : ℕ) := Fin n → Fin n → ℂ

/-- Complex matrices. -/
abbrev CM (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Matrix product on `Ev n`. -/
def mm (A B : Ev n) : Ev n := fun i j => ∑ k, A i k * B k j

theorem mm_eq (A B : CM n) : mm (n := n) A B = A * B := rfl

/-- Matrix multiplication as an $\mathbb R$-bilinear map. -/
def mmL : Ev n →ₗ[ℝ] Ev n →ₗ[ℝ] Ev n :=
  LinearMap.mk₂ ℝ mm
    (fun A A' B => by ext i j; simp [mm, add_mul, Finset.sum_add_distrib])
    (fun c A B => by ext i j; simp [mm, Finset.smul_sum, mul_assoc])
    (fun A B B' => by ext i j; simp [mm, mul_add, Finset.sum_add_distrib])
    (fun c A B => by ext i j; simp [mm, Finset.smul_sum, mul_left_comm])

theorem mmL_apply (A B : Ev n) : mmL A B = mm A B := rfl

/-- Matrix multiplication as a continuous bilinear map. -/
def mmC : Ev n →L[ℝ] Ev n →L[ℝ] Ev n :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Ev n) (F' := Ev n)).toLinearMap ∘ₗ mmL)

theorem mmC_apply (A B : Ev n) : mmC A B = mm A B := rfl

theorem hasFDerivAt_mm {F G : Ev n → Ev n} {F' G' : Ev n →L[ℝ] Ev n} {x : Ev n}
    (hF : HasFDerivAt F F' x) (hG : HasFDerivAt G G' x) :
    HasFDerivAt (fun y => mm (F y) (G y))
      ((mmC (F x)).comp G' + (mmC.flip (G x)).comp F') x := by
  have h := mmC.hasFDerivAt_of_bilinear hF hG
  have h' : (fun y => mm (F y) (G y)) = fun y => mmC (F y) (G y) := rfl
  rw [h']
  refine h.congr_fderiv ?_
  ext q
  rfl

/-- $\mathrm{cplx}$ as an $\mathbb R$-linear map. -/
def cplxL : Mat n →ₗ[ℝ] CM n where
  toFun := cplx
  map_add' A B := by ext i j; simp [cplx]
  map_smul' c A := by ext i j; simp [cplx]

/-- $p\mapsto\operatorname{Re}p$. -/
def pYL : Ev n →ₗ[ℝ] Mat n where
  toFun := pY
  map_add' p q := by ext i j; simp [pY]
  map_smul' c p := by ext i j; simp [pY]

/-- $p\mapsto\operatorname{Im}p$. -/
def pVL : Ev n →ₗ[ℝ] Mat n where
  toFun := pV
  map_add' p q := by ext i j; simp [pV]
  map_smul' c p := by ext i j; simp [pV]

/-- $\mathrm{upperOf}$ as a linear map. -/
def upperLin : Mat n →ₗ[ℝ] (UIdx n → ℝ) where
  toFun := upperOf
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- $\mathrm{symU}$ as a linear map. -/
def symLin : (UIdx n → ℝ) →ₗ[ℝ] Mat n where
  toFun := symU
  map_add' t t' := by
    ext i j
    simp only [symU, of_apply, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> rfl
  map_smul' c t := by
    ext i j
    simp only [symU, of_apply, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> rfl

/-- $p\mapsto u$ as a linear map. -/
def puL : Ev n →ₗ[ℝ] Mat n := skewLin ∘ₗ lowerLin ∘ₗ pVL

/-- $p\mapsto\sigma$ as a linear map. -/
def psL : Ev n →ₗ[ℝ] Mat n := symLin ∘ₗ upperLin ∘ₗ pVL

theorem pYL_apply (p : Ev n) : pYL p = pY p := rfl
theorem puL_apply (p : Ev n) : puL p = pu p := rfl
theorem psL_apply (p : Ev n) : psL p = ps p := rfl

/-- Multiplication by $i$ as an $\mathbb R$-linear map. -/
def Isc : Ev n →ₗ[ℝ] Ev n := ((Complex.I • (LinearMap.id : Ev n →ₗ[ℂ] Ev n)).restrictScalars ℝ)

theorem Isc_apply (X : Ev n) : Isc X = Complex.I • X := rfl

/-- $q\mapsto i\cdot u(q)$. -/
def LAu : Ev n →ₗ[ℝ] Ev n := Isc ∘ₗ cplxL ∘ₗ puL
/-- $q\mapsto i\cdot\sigma(q)$. -/
def LAs : Ev n →ₗ[ℝ] Ev n := Isc ∘ₗ cplxL ∘ₗ psL
/-- $q\mapsto\operatorname{Re}q$ as a complex matrix. -/
def LY : Ev n →ₗ[ℝ] Ev n := cplxL ∘ₗ pYL

/-- $1 - iu$. -/
def aF (p : Ev n) : Ev n := (1 : CM n) - Complex.I • cplx (pu p)
/-- $\operatorname{Re}p$ as a complex matrix. -/
def yF (p : Ev n) : Ev n := cplx (pY p)
/-- $1 - i\sigma$. -/
def bF (p : Ev n) : Ev n := (1 : CM n) - Complex.I • cplx (ps p)

/-- The column-coordinate map as a linear map. -/
def colsL : Ev n →ₗ[ℝ] Ev n where
  toFun X := cols (X : CM n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The unscrambled derivative of $\Psi$ (before taking columns). -/
def D1 (p : Ev n) : Ev n →ₗ[ℝ] Ev n :=
  (mmL.flip (bF p) ∘ₗ mmL.flip (yF p)) ∘ₗ (-LAu) + (mmL.flip (bF p) ∘ₗ mmL (aF p)) ∘ₗ LY
    + (mmL (mm (aF p) (yF p))) ∘ₗ (-LAs)

theorem psi_eq : (psi : Ev n → Ev n) = fun p => colsL (mm (mm (aF p) (yF p)) (bF p)) := rfl

theorem mm_add_left (A A' B : Ev n) : mm (A + A') B = mm A B + mm A' B := (mmL.flip B).map_add A A'

theorem hasFDerivAt_psi_aux (p : Ev n) :
    HasFDerivAt (psi : Ev n → Ev n) (LinearMap.toContinuousLinearMap (colsL ∘ₗ D1 p)) p := by
  have ha : HasFDerivAt aF (-(LinearMap.toContinuousLinearMap LAu)) p :=
    (LinearMap.toContinuousLinearMap LAu).hasFDerivAt.const_sub (show Ev n from (1 : CM n))
  have hy : HasFDerivAt yF (LinearMap.toContinuousLinearMap LY) p :=
    (LinearMap.toContinuousLinearMap LY).hasFDerivAt
  have hb : HasFDerivAt bF (-(LinearMap.toContinuousLinearMap LAs)) p :=
    (LinearMap.toContinuousLinearMap LAs).hasFDerivAt.const_sub (show Ev n from (1 : CM n))
  have h3 := (LinearMap.toContinuousLinearMap (colsL (n := n))).hasFDerivAt.comp p
    (hasFDerivAt_mm (hasFDerivAt_mm ha hy) hb)
  rw [psi_eq]
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun q => ?_
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, ContinuousLinearMap.flip_apply,
    _root_.neg_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, D1,
    LinearMap.add_apply, LinearMap.neg_apply, LinearMap.flip_apply, mmC_apply, mmL_apply, mm_add_left]
  congr 1
  abel

end Deriv

section Cont

variable {n : ℕ}

/-- A family of linear maps of $M_n(\mathbb R)$ that is entrywise continuous has continuous determinant. -/
theorem continuous_det_of_entries {X : Type*} [TopologicalSpace X] (f : X → (Mat n →ₗ[ℝ] Mat n))
    (h : ∀ (W : Mat n) (i k : Fin n), Continuous fun x => f x W i k) :
    Continuous fun x => LinearMap.det (f x) := by
  classical
  let b := Matrix.stdBasis ℝ (Fin n) (Fin n)
  have e : (fun x => LinearMap.det (f x)) = fun x => Matrix.det (LinearMap.toMatrix b b (f x)) := by
    funext x; rw [LinearMap.det_toMatrix]
  rw [e]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  have hr : ∀ w : Mat n, b.repr w i = w i.1 i.2 := by
    intro w
    simp [b, Matrix.stdBasis]
  simp only [LinearMap.toMatrix_apply, hr]
  exact h (b j) i.1 i.2

theorem continuous_phi1_entry (W : Mat n) (i k : Fin n) :
    Continuous fun q : Mat n × Mat n => phi1 q.1 q.2 W i k := by
  have h : Continuous fun q : Mat n × Mat n => phi1 q.1 q.2 W :=
    continuous_const.add ((continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd)
  exact (continuous_apply k).comp ((continuous_apply i).comp h)

end Cont

/-! ### The complex algebra of the Jacobian -/

section Alg

variable {n : ℕ}

theorem alg_identity (U Sg X Y Du Ds : CM n) :
    (1 + Complex.I • U) * ((-(Complex.I • Du)) * Y * (1 - Complex.I • Sg) + (1 - Complex.I • U) * X * (1 - Complex.I • Sg)
        + (1 - Complex.I • U) * Y * (-(Complex.I • Ds))) * (1 + Complex.I • Sg)
      = ((1 + U * U) * X * (1 + Sg * Sg) + U * Du * Y * (1 + Sg * Sg) + (1 + U * U) * Y * Ds * Sg)
        + Complex.I • (-(Du * Y * (1 + Sg * Sg) + (1 + U * U) * Y * Ds)) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_sub,
    smul_neg, smul_smul, Complex.I_mul_I, Matrix.mul_assoc, neg_smul, one_smul, neg_neg]
  module

theorem cplx_add (A B : Mat n) : cplx (A + B) = cplx A + cplx B := by ext i j; simp [cplx]
theorem cplx_neg (A : Mat n) : cplx (-A) = -cplx A := by ext i j; simp [cplx]
theorem cplx_mul (A B : Mat n) : cplx (A * B) = cplx A * cplx B := by
  ext i j; simp [cplx, Matrix.mul_apply, Complex.ofReal_sum]
theorem cplx_one : cplx (1 : Mat n) = 1 := by
  ext i j; by_cases h : i = j <;> simp [cplx, h, Matrix.one_apply]

/-- Real and imaginary parts as a linear equivalence $M_n(\mathbb R)^2\simeq M_n(\mathbb C)$. -/
def Ct : (Mat n × Mat n) ≃ₗ[ℝ] Ev n where
  toFun x := fun i j => ⟨x.1 i j, x.2 i j⟩
  invFun z := (pY z, pV z)
  map_add' a b := by funext i j; apply Complex.ext <;> simp
  map_smul' c a := by funext i j; apply Complex.ext <;> simp
  left_inv a := by ext <;> simp [pY, pV]
  right_inv z := by funext i j; apply Complex.ext <;> simp [pY, pV]

theorem Ct_eq (x y : Mat n) : Ct (x, y) = cplx x + Complex.I • cplx y := by
  funext i j; apply Complex.ext <;> simp [Ct, cplx]

/-- The real Jacobian structure: $\mathrm{lower}$-coordinates to the skew matrix. -/
def duL : Mat n →ₗ[ℝ] Mat n := skewLin ∘ₗ lowerLin

/-- Upper coordinates to the symmetric matrix. -/
def dsL : Mat n →ₗ[ℝ] Mat n := symLin ∘ₗ upperLin

/-- The $(x,y)\mapsto x$ block: $x\mapsto MxS$. -/
def aM (u σ : Mat n) : Mat n →ₗ[ℝ] Mat n :=
  LinearMap.mulLeft ℝ (1 + u * u) ∘ₗ LinearMap.mulRight ℝ (1 + σ * σ)

/-- The off-diagonal block. -/
def Kl (u Y σ : Mat n) : Mat n →ₗ[ℝ] Mat n :=
  (LinearMap.mulLeft ℝ u ∘ₗ LinearMap.mulRight ℝ (Y * (1 + σ * σ))) ∘ₗ duL
    + (LinearMap.mulLeft ℝ ((1 + u * u) * Y) ∘ₗ LinearMap.mulRight ℝ σ) ∘ₗ dsL

/-- The $y\mapsto y$ block. -/
def dl (u Y σ : Mat n) : Mat n →ₗ[ℝ] Mat n :=
  -(LinearMap.mulRight ℝ (Y * (1 + σ * σ)) ∘ₗ duL + LinearMap.mulLeft ℝ ((1 + u * u) * Y) ∘ₗ dsL)

/-- $1 + iu$. -/
def aG (p : Ev n) : Ev n := (1 : CM n) + Complex.I • cplx (pu p)
/-- $1 + i\sigma$. -/
def bG (p : Ev n) : Ev n := (1 : CM n) + Complex.I • cplx (ps p)

/-- $q\mapsto(1+iu)\,D_1(q)\,(1+i\sigma)$. -/
def Nm (p : Ev n) : Ev n →ₗ[ℝ] Ev n := mmL.flip (bG p) ∘ₗ mmL (aG p) ∘ₗ D1 p

theorem Nm_Ct (p : Ev n) (x y : Mat n) :
    Nm p (Ct (x, y)) = Ct (aM (pu p) (ps p) x + Kl (pu p) (pY p) (ps p) y, dl (pu p) (pY p) (ps p) y) := by
  have h : @Eq (CM n) (Nm p (Ct (x, y))) (((1 : CM n) + Complex.I • cplx (pu p)) *
      ((-(Complex.I • cplx (duL y))) * cplx (pY p) * (1 - Complex.I • cplx (ps p))
        + (1 - Complex.I • cplx (pu p)) * cplx x * (1 - Complex.I • cplx (ps p))
        + (1 - Complex.I • cplx (pu p)) * cplx (pY p) * (-(Complex.I • cplx (dsL y))))
      * ((1 : CM n) + Complex.I • cplx (ps p))) := by
    rfl
  rw [h, alg_identity, Ct_eq]
  simp only [aM, Kl, dl, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, cplx_add, cplx_neg, cplx_mul, cplx_one,
    Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul]
  abel

end Alg

/-! ### Determinants -/

section Dets

variable {n : ℕ}

/-- Column coordinates as a linear equivalence of `Ev n`. -/
def colsE : Ev n ≃ₗ[ℝ] Ev n where
  toFun X := fun j i => X i j
  invFun X := fun j i => X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_mmL_left (A : CM n) :
    LinearMap.det (mmL (n := n) A) = Complex.normSq (A.det ^ n) := by
  rw [← LinearMap.det_conj (mmL (n := n) A) colsE]
  have : (colsE (n := n)).toLinearMap ∘ₗ mmL A ∘ₗ (colsE (n := n)).symm.toLinearMap =
      (lmulL A).restrictScalars ℝ := by
    apply LinearMap.ext; intro X
    exact cols_mul_left A (colsE.symm X)
  rw [this, det_restrictScalars_complex, det_lmulL]

theorem det_mmL_right (B : CM n) :
    LinearMap.det ((mmL (n := n)).flip B) = Complex.normSq (B.det ^ n) := by
  rw [← LinearMap.det_conj ((mmL (n := n)).flip B) colsE]
  have : (colsE (n := n)).toLinearMap ∘ₗ mmL.flip B ∘ₗ (colsE (n := n)).symm.toLinearMap =
      (rmulL B).restrictScalars ℝ := by
    apply LinearMap.ext; intro X
    exact cols_mul_right (colsE.symm X) B
  rw [this, det_restrictScalars_complex, det_rmulL]

theorem abs_det_colsL : |LinearMap.det (colsL : Ev n →ₗ[ℝ] Ev n)| = 1 := by
  have h : (colsL : Ev n →ₗ[ℝ] Ev n) ∘ₗ colsL = LinearMap.id := rfl
  have h2 := congrArg LinearMap.det h
  rw [LinearMap.det_comp, LinearMap.det_id] at h2
  have h3 : |LinearMap.det (colsL : Ev n →ₗ[ℝ] Ev n)| * |LinearMap.det (colsL : Ev n →ₗ[ℝ] Ev n)| = 1 := by
    rw [← abs_mul, h2, abs_one]
  rcases mul_self_eq_one_iff.mp h3 with h4 | h4
  · exact h4
  · linarith [abs_nonneg (LinearMap.det (colsL : Ev n →ₗ[ℝ] Ev n))]

/-- $|\det(1+iu)|^2=\det(1+u^2)$ for a real matrix $u$. -/
theorem normSq_det_one_add (u : Mat n) :
    Complex.normSq (((1 : CM n) + Complex.I • cplx u).det) = (1 + u * u).det := by
  set A' : CM n := (1 : CM n) + Complex.I • cplx u with hA'
  set A : CM n := (1 : CM n) - Complex.I • cplx u with hA
  have h1 : A.det = (starRingEnd ℂ) A'.det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [hA, hA', cplx, h, Matrix.one_apply, sub_eq_add_neg]
  have h2 : A' * A = cplx (1 + u * u) := by
    rw [cplx_add, cplx_mul, cplx_one, hA, hA']
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_sub, smul_add, smul_smul, Complex.I_mul_I,
      neg_smul, one_smul]
    abel
  have h3 : ((Complex.normSq A'.det : ℝ) : ℂ) = (((1 + u * u).det : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, ← h1, ← det_mul, h2]
    have := (RingHom.map_det Complex.ofRealHom (1 + u * u)).symm
    simpa [cplx, Complex.ofRealHom, RingHom.mapMatrix_apply] using this
  exact_mod_cast h3

theorem det_Nm (p : Ev n) :
    LinearMap.det (Nm p) =
      (1 + ps p * ps p).det ^ n * (1 + pu p * pu p).det ^ n * LinearMap.det (D1 p) := by
  have hb : Complex.normSq (Matrix.det (bG p : CM n)) = (1 + ps p * ps p).det := normSq_det_one_add (ps p)
  have ha : Complex.normSq (Matrix.det (aG p : CM n)) = (1 + pu p * pu p).det := normSq_det_one_add (pu p)
  have e1 := det_mmL_right (bG p)
  have e2 := det_mmL_left (aG p)
  rw [Nm, LinearMap.det_comp, LinearMap.det_comp, e1, e2, map_pow, map_pow, hb, ha, mul_assoc]

theorem det_Nm_triang (p : Ev n) :
    LinearMap.det (Nm p) = (1 + pu p * pu p).det ^ n * (1 + ps p * ps p).det ^ n *
      LinearMap.det (dl (pu p) (pY p) (ps p)) := by
  have h : Nm p = (Ct (n := n)).toLinearMap ∘ₗ
      triang (aM (pu p) (ps p)) (Kl (pu p) (pY p) (ps p)) (dl (pu p) (pY p) (ps p)) ∘ₗ
        (Ct (n := n)).symm.toLinearMap := by
    apply LinearMap.ext; intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := Ct.surjective z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [Nm_Ct]
    rfl
  rw [h, LinearMap.det_conj, det_triang, aM, LinearMap.det_comp, det_mulLeft, det_mulRight]

theorem phi1_skew_sym (T R K Sy : Mat n) (hK : Kᵀ = -K) (hS : Syᵀ = Sy) :
    phi1 T R (K + Sy) = K + T * Sy * R := by
  rw [phi1_apply, transpose_add, hK, hS]
  have e1 : (1 / 2 : ℝ) • (K + Sy - (-K + Sy)) = K := by module
  have e2 : (1 / 2 : ℝ) • (K + Sy + (-K + Sy)) = Sy := by module
  rw [e1, e2]

theorem dl_rel (u Y σ : Mat n) (hσ : (1 + σ * σ)⁻¹ * (1 + σ * σ) = 1) :
    LinearMap.mulLeft ℝ Yᵀ ∘ₗ dl u Y σ =
      -(LinearMap.mulRight ℝ (1 + σ * σ) ∘ₗ phi1 (Yᵀ * (1 + u * u) * Y) (1 + σ * σ)⁻¹ ∘ₗ (Cm Y ∘ₗ iota)) := by
  apply LinearMap.ext; intro y
  have hK : (duL y)ᵀ = -duL y := skewOf_transpose _
  have hS : (dsL y)ᵀ = dsL y := symU_transpose _
  have hi : iota y = duL y + dsL y := iota_apply y
  have hK' : (Yᵀ * duL y * Y)ᵀ = -(Yᵀ * duL y * Y) := transpose_conj_skew hK
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    dl, LinearMap.add_apply, hi, Cm_add hK hS, phi1_skew_sym _ _ _ _ hK' hS]
  generalize (1 + σ * σ)⁻¹ = R at hσ ⊢
  generalize (1 + σ * σ) = S at hσ ⊢
  generalize (1 + u * u) = Mm
  simp only [Matrix.mul_neg, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hσ, Matrix.mul_one]

theorem hS_pos (σ : Mat n) (hσ : σᵀ = σ) : 0 < (1 + σ * σ).det := by
  have h1 : (1 : Mat n) + σ * σ = 1 + σᴴ * σ := by
    rw [conjTranspose_eq_transpose_of_trivial, hσ]
  rw [h1]
  exact ((Matrix.PosDef.one (n := Fin n) (R := ℝ)).add_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self σ)).det_pos

theorem abs_det_dl (u Y σ : Mat n) (hσ : σᵀ = σ) :
    |Y.det| ^ n * |LinearMap.det (dl u Y σ)| =
      (1 + σ * σ).det ^ n * |LinearMap.det (phi1 (Yᵀ * (1 + u * u) * Y) (1 + σ * σ)⁻¹)| *
        (|Y.det| ^ (n - 1) * 2 ^ (n * (n - 1) / 2)) := by
  have hpos := hS_pos σ hσ
  have hRS : (1 + σ * σ)⁻¹ * (1 + σ * σ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos.ne')
  have h := congrArg LinearMap.det (dl_rel u Y σ hRS)
  have hneg : ∀ f : Mat n →ₗ[ℝ] Mat n, |LinearMap.det (-f)| = |LinearMap.det f| := by
    intro f
    rw [show -f = (-1 : ℝ) • f from (neg_one_smul ℝ f).symm, LinearMap.det_smul]
    simp [abs_mul]
  have h2 := congrArg abs h
  rw [LinearMap.det_comp, det_mulLeft, det_transpose, abs_mul, abs_pow, hneg, LinearMap.det_comp,
    LinearMap.det_comp, det_mulRight, det_Cm_iota] at h2
  simp only [abs_mul, abs_pow, abs_of_pos hpos, abs_det_iota] at h2
  linarith [h2]

end Dets

end Jac

/-- **The derivative of $\Psi$** at $p$. -/
def psiD {n : ℕ} (p : Fin n → Fin n → ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (Jac.colsL ∘ₗ Jac.D1 p)

/-- $\Psi$ is differentiable, with derivative `psiD p`. -/
theorem hasFDerivAt_psi {n : ℕ} (p : Fin n → Fin n → ℂ) : HasFDerivAt psi (psiD p) p :=
  Jac.hasFDerivAt_psi_aux p

/-- **The Jacobian of $\Psi$** (Hanke, §4.3, pp. 14–15): for $\det Y\neq0$ and $\delta(u)=\det(1-{}^tuu)\ne0$,
$$|\det D\Psi| = 2^{n(n-1)/2}\,|\det Y|^{-1}\,\det(1+\sigma^2)^n\,
  \bigl|\det\varphi_1\bigl({}^tY(1-{}^tuu)Y,\ (1+\sigma^2)^{-1}\bigr)\bigr|.$$
(The hypothesis $\delta(u)\ne0$ is automatic on $u\in Z_{\mathbb C}$, where $1-{}^tuu$ is positive definite.) -/
@[kb "hanke2005crelle" "§4.3, pp. 14–15 (Jacobian of the coordinates; Lemma A5)"]
theorem abs_det_psiD {n : ℕ} (p : Fin n → Fin n → ℂ) (hY : (pY p).det ≠ 0)
    (hM : (mZ (pu p)).det ≠ 0) :
    |LinearMap.det (psiD p : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ))| =
      (2 : ℝ) ^ (n * (n - 1) / 2) * |(pY p).det|⁻¹ * (1 + ps p * ps p).det ^ n *
        |LinearMap.det (phi1 (tT (pu p) (pY p)) (1 + ps p * ps p)⁻¹)| := by
  have hu : (pu p)ᵀ = -(pu p) := Jac.skewOf_transpose _
  have hσ : (ps p)ᵀ = ps p := Jac.symU_transpose _
  have hMeq : mZ (pu p) = 1 + pu p * pu p := by simp [mZ, hu]
  have hMne : (1 + pu p * pu p).det ≠ 0 := hMeq ▸ hM
  have hSpos := Jac.hS_pos (ps p) hσ
  have hD : LinearMap.det (Jac.D1 p) = LinearMap.det (Jac.dl (pu p) (pY p) (ps p)) := by
    have h1 := Jac.det_Nm p
    have h2 := Jac.det_Nm_triang p
    rw [h1] at h2
    have hc : (1 + ps p * ps p).det ^ n * (1 + pu p * pu p).det ^ n ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hSpos.ne') (pow_ne_zero _ hMne)
    apply mul_left_cancel₀ hc
    rw [h2]; ring
  have hpsi : |LinearMap.det (psiD p : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ))| =
      |LinearMap.det (Jac.D1 p)| := by
    have : (psiD p : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ)) = Jac.colsL ∘ₗ Jac.D1 p := rfl
    rw [this, LinearMap.det_comp, abs_mul, Jac.abs_det_colsL, one_mul]
  have hdl := Jac.abs_det_dl (pu p) (pY p) (ps p) hσ
  have hT : tT (pu p) (pY p) = (pY p)ᵀ * (1 + pu p * pu p) * pY p := by rw [tT, hMeq]
  rw [hT, hpsi, hD]
  have ha : 0 < |(pY p).det| := abs_pos.mpr hY
  have hYn : |(pY p).det| ^ n = |(pY p).det| ^ (n - 1) * |(pY p).det| := by
    cases n with
    | zero => simp
    | succ m => simp [pow_succ]
  have h3 : |(pY p).det| * |LinearMap.det (Jac.dl (pu p) (pY p) (ps p))| =
      (1 + ps p * ps p).det ^ n *
        |LinearMap.det (phi1 ((pY p)ᵀ * (1 + pu p * pu p) * pY p) (1 + ps p * ps p)⁻¹)| *
        2 ^ (n * (n - 1) / 2) := by
    have hpos' : 0 < |(pY p).det| ^ (n - 1) := pow_pos ha _
    apply mul_left_cancel₀ hpos'.ne'
    calc |(pY p).det| ^ (n - 1) * (|(pY p).det| * |LinearMap.det (Jac.dl (pu p) (pY p) (ps p))|)
        = |(pY p).det| ^ n * |LinearMap.det (Jac.dl (pu p) (pY p) (ps p))| := by rw [hYn]; ring
      _ = _ := hdl
      _ = _ := by ring
  field_simp
  linarith [h3]

/-- $\Psi$ is continuous. -/
theorem continuous_psi {n : ℕ} : Continuous (psi : (Fin n → Fin n → ℂ) → Fin n → Fin n → ℂ) :=
  continuous_iff_continuousAt.2 fun p => (hasFDerivAt_psi p).continuousAt

/-- The determinant of $\varphi_1(T,R)$ is continuous in $(T,R)$. -/
theorem continuous_det_phi1 {n : ℕ} :
    Continuous fun q : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      LinearMap.det (phi1 q.1 q.2) :=
  Jac.continuous_det_of_entries (X := Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (fun q => phi1 q.1 q.2) (fun W i k => Jac.continuous_phi1_entry W i k)

end QuadFormsKB.Hanke2005.ArchCx
