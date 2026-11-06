/-
# Splitting off a block of a quadratic form over a DVR

For a quadratic form $Q$ on $R^{m+k}$ over a discrete valuation ring $R$ and a matrix $X$ whose $k$ columns span a
"block", write $G=X^{\mathsf T}HX$ for the Gram matrix of the columns ($H$ the Hessian of $Q$). If $G$ is nonsingular
and every functional $X^{\mathsf T}Hv$ lies in the image of $G$ (witnessed by $GP=X^{\mathsf T}H$), then $R^{m+k}$
is the direct sum of the columns of $X$ and their orthogonal complement, and $Q$ is $\mathrm{GL}$-equivalent to
$Q'\perp(Q\circ X)$ for some form $Q'$ in $m$ variables.  This generalizes `exists_split_aux` (which handles a
hyperbolic pair).  Corollaries: a unimodular block ($G$ invertible), and a scaled block ($G=cG'$ with $G'$ invertible
and $X^{\mathsf T}H=cY$).
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelShape
open Matrix
noncomputable section
namespace QuadFormsKB.Hanke2005
open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadForm

section SplitBlock

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The orthogonal complement of a block:** $\{w : X^{\mathsf T}Hw=0\}$, a submodule of $R^n$. -/
def blockOrth {n k : ℕ} (Q : QuadForm R n) (X : Matrix (Fin n) (Fin k) R) : Submodule R (Fin n → R) :=
  LinearMap.ker (Matrix.mulVecLin (Xᵀ * Q.hessian))

theorem mem_blockOrth {n k : ℕ} (Q : QuadForm R n) (X : Matrix (Fin n) (Fin k) R) (w : Fin n → R) :
    w ∈ blockOrth Q X ↔ (Xᵀ * Q.hessian) *ᵥ w = 0 := by
  rw [blockOrth, LinearMap.mem_ker, Matrix.mulVecLin_apply]

/-- The map $(w,s)\mapsto w+Xs$ from $\mathrm{blockOrth}\times R^k$ to $R^n$. -/
def blockMap {n k : ℕ} (Q : QuadForm R n) (X : Matrix (Fin n) (Fin k) R) :
    (blockOrth Q X × (Fin k → R)) →ₗ[R] (Fin n → R) :=
  (blockOrth Q X).subtype.coprod (Matrix.mulVecLin X)

theorem blockMap_apply {n k : ℕ} (Q : QuadForm R n) (X : Matrix (Fin n) (Fin k) R) (w : blockOrth Q X)
    (s : Fin k → R) : blockMap Q X (w, s) = (w : Fin n → R) + X *ᵥ s := by
  simp [blockMap]

theorem blockMap_bijective {n k : ℕ} (Q : QuadForm R n) (X : Matrix (Fin n) (Fin k) R)
    (P : Matrix (Fin k) (Fin n) R) (hG : (Xᵀ * Q.hessian * X).det ≠ 0)
    (hP : (Xᵀ * Q.hessian * X) * P = Xᵀ * Q.hessian) : Function.Bijective (blockMap Q X) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w, s⟩ h0
    rw [blockMap_apply] at h0
    have hw := (mem_blockOrth Q X w).1 w.2
    have h1 : (Xᵀ * Q.hessian * X) *ᵥ s = 0 := by
      have := congrArg (fun v => (Xᵀ * Q.hessian) *ᵥ v) h0
      simp only [Matrix.mulVec_add, hw, zero_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      exact this
    have hs : s = 0 := Matrix.eq_zero_of_mulVec_eq_zero hG h1
    subst hs
    refine Prod.ext (Subtype.ext ?_) rfl
    simpa using h0
  · intro v
    have hw : v - X *ᵥ (P *ᵥ v) ∈ blockOrth Q X := by
      rw [mem_blockOrth, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP, sub_self]
    exact ⟨(⟨_, hw⟩, P *ᵥ v), by rw [blockMap_apply]; simp⟩

/-- **Splitting off a block** (O'Meara 91:9 style). If the Gram matrix $G=X^{\mathsf T}HX$ of the columns of $X$ is
nonsingular and every $X^{\mathsf T}Hv$ lies in the image of $G$ (witnessed by a matrix $P$ with
$GP=X^{\mathsf T}H$), then $Q$ is $\mathrm{GL}_{m+k}(R)$-equivalent to $Q'\perp(Q\circ X)$ for some $Q'$ in $m$
variables. -/
@[kb "omeara1963" "§91C, 91:9 (splitting off a modular component)"]
theorem exists_split_block {m k : ℕ} (Q : QuadForm R (m + k)) (X : Matrix (Fin (m + k)) (Fin k) R)
    (P : Matrix (Fin k) (Fin (m + k)) R)
    (hG : (Xᵀ * Q.hessian * X).det ≠ 0) (hP : (Xᵀ * Q.hessian * X) * P = Xᵀ * Q.hessian) :
    ∃ Q' : QuadForm R m, DVR.IsGLEquiv Q (orthSum Q' (Q.compMat X)) := by
  have hg := blockMap_bijective Q X P hG hP
  have hrk : Module.finrank R (blockOrth Q X) = m := by
    have h := LinearEquiv.finrank_eq (LinearEquiv.ofBijective (blockMap Q X) hg)
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  let bM := Module.finBasisOfFinrankEq R (blockOrth Q X) hrk
  let bV : Module.Basis (Fin (m + k)) R (Fin (m + k) → R) :=
    ((bM.prod (Pi.basisFun R (Fin k))).map (LinearEquiv.ofBijective (blockMap Q X) hg)).reindex
      finSumFinEquiv
  let Z : Matrix (Fin (m + k)) (Fin m) R := Matrix.of fun l a => (bM a : Fin (m + k) → R) l
  let U : Matrix (Fin (m + k)) (Fin (m + k)) R := Matrix.of fun i j => bV j i
  have hbl : ∀ (a : Fin m) l, bV (Fin.castAdd k a) l = Z l a := by
    intro a l
    simp [bV, Z, Module.Basis.reindex_apply, blockMap_apply]
  have hbr : ∀ (j : Fin k) l, bV (Fin.natAdd m j) l = X l j := by
    intro j l
    simp [bV, Module.Basis.reindex_apply, blockMap_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hU : ∀ x : Fin (m + k) → R, U *ᵥ x =
      Z *ᵥ (fun a => x (Fin.castAdd k a)) + X *ᵥ (fun j => x (Fin.natAdd m j)) := by
    intro x
    funext i
    simp only [U, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Pi.add_apply, hbl, hbr]
  have hdet : IsUnit U.det := by
    have : U = (Pi.basisFun R (Fin (m + k))).toMatrix bV := by
      ext i j; simp [U, Module.Basis.toMatrix_apply]
    rw [this, ← Module.Basis.det_apply]
    exact Module.Basis.isUnit_det _ _
  refine ⟨Q.compMat Z, U, hdet, fun x => ?_⟩
  set y : Fin m → R := fun a => x (Fin.castAdd k a) with hy_def
  set t : Fin k → R := fun j => x (Fin.natAdd m j) with ht_def
  have hy : (Z *ᵥ y) ∈ blockOrth Q X := by
    have : Z *ᵥ y = ((∑ a, y a • bM a : blockOrth Q X) : Fin (m + k) → R) := by
      funext l
      simp [Matrix.mulVec, dotProduct, Z, mul_comm]
    rw [this]
    exact (∑ a, y a • bM a : blockOrth Q X).2
  have hc : (Z *ᵥ y) ⬝ᵥ (Q.hessian *ᵥ (X *ᵥ t)) = 0 := by
    rw [dot_hessian_comm, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, (mem_blockOrth Q X _).1 hy, zero_dotProduct]
  rw [QuadForm.eval, evalIn_orthSum, hU]
  change (Q.compMat Z).eval y + (Q.compMat X).eval t = _
  rw [eval_compMat, eval_compMat, eval_add_hessian, hc]
  ring

/-- **Splitting off a unimodular block:** if the Gram matrix $G=X^{\mathsf T}HX$ has unit determinant, then $Q$ is
$\mathrm{GL}$-equivalent to $Q'\perp(Q\circ X)$ for some $Q'$ (O'Meara 91:9; take $P=G^{-1}X^{\mathsf T}H$). -/
@[kb "omeara1963" "§91C, 91:9 (splitting off a modular component)"]
theorem exists_split_unimodular {m k : ℕ} (Q : QuadForm R (m + k)) (X : Matrix (Fin (m + k)) (Fin k) R)
    (hG : IsUnit (Xᵀ * Q.hessian * X).det) :
    ∃ Q' : QuadForm R m, DVR.IsGLEquiv Q (orthSum Q' (Q.compMat X)) := by
  refine exists_split_block Q X ((Xᵀ * Q.hessian * X)⁻¹ * (Xᵀ * Q.hessian)) hG.ne_zero ?_
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]

/-- **Splitting off a scaled block:** if $G=X^{\mathsf T}HX=cG'$ with $G'$ invertible, $c\ne0$, and
$X^{\mathsf T}H=cY$, then $Q$ is $\mathrm{GL}$-equivalent to $Q'\perp(Q\circ X)$ for some $Q'$
(O'Meara 91:9; take $P=G'^{-1}Y$). -/
@[kb "omeara1963" "§91C, 91:9 (splitting off a modular component)"]
theorem exists_split_scaled {m k : ℕ} (Q : QuadForm R (m + k)) (X : Matrix (Fin (m + k)) (Fin k) R) {c : R}
    (hc : c ≠ 0) (G' : Matrix (Fin k) (Fin k) R) (hG' : IsUnit G'.det)
    (hG : Xᵀ * Q.hessian * X = c • G') (Y : Matrix (Fin k) (Fin (m + k)) R)
    (hY : Xᵀ * Q.hessian = c • Y) :
    ∃ Q' : QuadForm R m, DVR.IsGLEquiv Q (orthSum Q' (Q.compMat X)) := by
  refine exists_split_block Q X (G'⁻¹ * Y) ?_ ?_
  · rw [hG, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hG'.ne_zero
  · rw [hG, hY, Matrix.smul_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG', Matrix.one_mul]

end SplitBlock

end QuadFormsKB.Hanke2005
