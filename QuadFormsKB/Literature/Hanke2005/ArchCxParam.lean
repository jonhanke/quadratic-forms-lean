/-
# Hanke 2005, §4.3: coordinates near $SO_n(\mathbb C)$ adapted to $F_{\mathbb C}$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

This file sets up the coordinates used to compute the fibre volume $\mathrm{vol}_C(C_{\mathbb C})$ of §4.3 (pp. 14–15)
measure-theoretically (`ArchVolumeComplex.lean`). Every complex matrix $X$ near $SO_n(\mathbb C)$ is written as
$$X = \Psi(u, Y, \sigma) = (1 - iu)\,Y\,(1 - i\sigma),$$
with $u$ real skew-symmetric (the coordinate $z = F_{\mathbb C}$ of §4.3), $Y$ real and $\sigma$ real symmetric. Then
$${}^tXX = (1 - i\sigma)\,T\,(1 - i\sigma),\qquad T = {}^tY(1 - {}^tuu)Y,$$
so the Gram matrix depends only on $(T, \sigma)$, and on $SO_n(\mathbb C)$ ($\sigma = 0$, $T = 1$) one has $X = s(u)k$ with
$k\in SO_n(\mathbb R)$ and $F_{\mathbb C}(X) = u$. This is the measure-theoretic form of Hanke's use of Lemma A6: the
differential of $F_{\mathbb C}$ is only needed along the fibre $C_{\mathbb C} = \{b = 0\}$.

**Defines**
* `cplx A`: a real matrix as a complex matrix;
* `upperOf V`: the coordinates $V_{ij}$, $i\le j$;
* for $p\in M_n(\mathbb C)$ (as `Fin n → Fin n → ℂ`, $p_{ij}$ = entry $(i, j)$): `pY p` $= \operatorname{Re}p$, `pV p` $=
  \operatorname{Im}p$, `pu p` (the skew matrix with lower coordinates those of $\operatorname{Im}p$) and `ps p` (the symmetric
  matrix with upper coordinates those of $\operatorname{Im}p$); so $p\mapsto(u, Y, \sigma)$ is a coordinate permutation;
* `psiM u Y σ` $= (1 - iu)Y(1 - i\sigma)$ and `psi p` its column vector form (the convention of `LerayComplex.cols`);
* `mZ u` $= 1 - {}^tuu$ and `tT u Y` $= {}^tY(1 - {}^tuu)Y$;
* `phi1 T R`: the linear map $W\mapsto\tfrac12(W - {}^tW) + T\cdot\tfrac12(W + {}^tW)\cdot R$ on $M_n(\mathbb R)$.
-/
import QuadFormsKB.Literature.Hanke2005.ArchFibrationComplex

open Matrix Complex

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

/-- A real matrix as a complex matrix. -/
def cplx (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ := A.map fun x : ℝ => (x : ℂ)

/-- The coordinates $V_{ij}$, $i\le j$, of a real matrix. -/
def upperOf (V : Matrix (Fin n) (Fin n) ℝ) : UIdx n → ℝ := fun p => V p.1.1 p.1.2

/-- The real part $Y$ of the coordinate point $p$. -/
def pY (p : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (p i j).re

/-- The imaginary part of the coordinate point $p$. -/
def pV (p : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (p i j).im

/-- The skew coordinate $u$ of $p$: the skew matrix whose entries below the diagonal are those of $\operatorname{Im}p$. -/
def pu (p : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℝ := skewOf (lowerOf (pV p))

/-- The symmetric coordinate $\sigma$ of $p$: the symmetric matrix whose entries on and above the diagonal are those of
$\operatorname{Im}p$. -/
def ps (p : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℝ := symU (upperOf (pV p))

/-- $\Psi(u, Y, \sigma) = (1 - iu)\,Y\,(1 - i\sigma)$. -/
def psiM (u Y σ : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 - I • cplx u) * cplx Y * (1 - I • cplx σ)

/-- $\Psi$ on coordinate points, with values in column coordinates (`LerayComplex.cols`). -/
def psi (p : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ := cols (psiM (pu p) (pY p) (ps p))

/-- $M(u) = 1 - {}^tuu$ ($= 1 + u^2$ for skew $u$; $\delta(u) = \det M(u)$). -/
def mZ (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 - uᵀ * u

/-- $T = {}^tY(1 - {}^tuu)Y$. -/
def tT (u Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := Yᵀ * mZ u * Y

/-- The linear map $W\mapsto\tfrac12(W - {}^tW) + T\cdot\tfrac12(W + {}^tW)\cdot R$ on $M_n(\mathbb R)$. Its determinant
at $(T, R) = (1, 1)$ is $1$; it enters the Jacobian of $\Psi$ with $R = (1 + \sigma^2)^{-1}$. -/
def phi1 (T R : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun W := (1 / 2 : ℝ) • (W - Wᵀ) + T * ((1 / 2 : ℝ) • (W + Wᵀ)) * R
  map_add' W W' := by
    simp only [transpose_add, smul_add, Matrix.mul_add, Matrix.add_mul]
    rw [show W + W' - (Wᵀ + W'ᵀ) = (W - Wᵀ) + (W' - W'ᵀ) by abel, smul_add]
    abel
  map_smul' c W := by
    simp only [transpose_smul, RingHom.id_apply, ← smul_sub, ← smul_add, Matrix.mul_smul,
      Matrix.smul_mul]
    rw [smul_comm]

theorem phi1_apply (T R W : Matrix (Fin n) (Fin n) ℝ) :
    phi1 T R W = (1 / 2 : ℝ) • (W - Wᵀ) + T * ((1 / 2 : ℝ) • (W + Wᵀ)) * R := rfl

theorem phi1_one_one : phi1 (1 : Matrix (Fin n) (Fin n) ℝ) 1 = LinearMap.id := by
  refine LinearMap.ext fun W => ?_
  rw [phi1_apply, Matrix.one_mul, Matrix.mul_one, LinearMap.id_apply, ← smul_add]
  rw [show W - Wᵀ + (W + Wᵀ) = (2 : ℝ) • W by rw [two_smul]; abel, smul_smul]
  norm_num

theorem det_phi1_one_one : LinearMap.det (phi1 (1 : Matrix (Fin n) (Fin n) ℝ) 1) = 1 := by
  rw [phi1_one_one, LinearMap.det_id]

end QuadFormsKB.Hanke2005.ArchCx
