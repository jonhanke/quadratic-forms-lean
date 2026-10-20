import QuadFormsKB.Tamagawa.Measure.Weil.QuatLocal

/-!
# The reduced-trace normalization for $\mathbb H$: Gram matrix, local scaling, global product

The additive measure on $\mathbb H_v$ that is self-dual for $\psi_v(\operatorname{trd}(xy))$ differs from the coordinate
self-dual measure (self-dual for $\psi_v(\sum_i x_iy_i)$) by the factor $|\det G|_v^{1/2}$, where $G$ is the Gram matrix
of the trace form in the basis $1,i,j,k$. This file proves the three *algebraic/scaling* ingredients; the
identification of the self-dual measure itself (a 4-variable Fourier inversion) is in `TrdSelfDual.lean`.

* **`trdGram_eq`**: $G = (\operatorname{trd}(e_ie_j))_{ij} = \operatorname{diag}(2, 2a, 2b, -2ab)$, $\operatorname{trd} = 2\operatorname{re}$,
  over any commutative ring; `det_trdGram`: $\det G = -16a^2b^2$.
* **`map_trdGram_mulVec`** (local scaling, via `glHaarChar_eq_of_field`): over a locally compact field $K$ with
  $16a^2b^2\ne0$, $G_*\nu = \Delta_K(\det G)^{-1}\nu$ for every regular Haar measure $\nu$ on $K^4$. With
  $\widehat f_G(y) = \widehat f(Gy)$ this is the change of variables that gives the factor $|\det G|^{1/2}$.
* **`ideleNorm_det_trdGram`** (global product): for $a, b\in F^\times$, $\prod_v|\det G|_v = \|-16a^2b^2\|_{\mathbb A} = 1$
  (product formula `ideleNorm_diagUnits`), so $\prod_v|\det G|_v^{1/2} = 1$ and the global measure does not depend on
  the choice (coordinate vs. trace) of self-dual normalization.
-/

open MeasureTheory Matrix
open scoped ENNReal NNReal Quaternion Matrix.GLmulVec

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-- The Gram matrix $(\operatorname{trd}(e_ie_j))_{ij}$ of the reduced trace form $\operatorname{trd}(xy) = 2\operatorname{re}(xy)$ in
the basis $1,i,j,k$ of $\mathbb H[R,a,0,b]$. -/
def trdGram {R : Type*} [CommRing R] (a b : R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => 2 * (QuaternionAlgebra.basisOneIJK a 0 b i * QuaternionAlgebra.basisOneIJK a 0 b j).re

/-- **$G = \operatorname{diag}(2, 2a, 2b, -2ab)$.** -/
theorem trdGram_eq {R : Type*} [CommRing R] (a b : R) :
    trdGram a b = Matrix.diagonal ![2, 2 * a, 2 * b, -(2 * a * b)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [trdGram, QuaternionAlgebra.basisOneIJK, Matrix.diagonal, mul_assoc]

theorem det_trdGram {R : Type*} [CommRing R] (a b : R) : (trdGram a b).det = -(16 * a ^ 2 * b ^ 2) := by
  rw [trdGram_eq, Matrix.det_diagonal, Fin.prod_univ_four]
  simp
  ring

section Local

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]

/-- $G$ as an element of $\mathrm{GL}_4(K)$ when $16a^2b^2\ne0$. -/
def trdGramGL (a b : K) (h : (16 : K) * a ^ 2 * b ^ 2 ≠ 0) : GL (Fin 4) K :=
  GeneralLinearGroup.mkOfDetNeZero (trdGram a b) (by rw [det_trdGram]; exact neg_ne_zero.mpr h)

/-- **Local scaling for the trace form**: $G_*\nu = \Delta_K(\det G)^{-1}\nu$, $\det G = -16a^2b^2$. -/
@[kb "weil1982" "§2.3 [unverified page] (self-dual measure for ψ∘trd)"]
theorem map_trdGram_mulVec (a b : K) (h : (16 : K) * a ^ 2 * b ^ 2 ≠ 0) (ν : Measure (Fin 4 → K))
    [ν.IsAddHaarMeasure] [ν.Regular] :
    ν.map (trdGram a b).mulVec = (distribHaarChar K (Units.mk0 _ (neg_ne_zero.mpr h)) : ℝ≥0∞)⁻¹ • ν := by
  have := map_mulVec_eq_glHaarChar_inv ν (trdGramGL a b h)
  rw [glHaarChar_eq_of_field] at this
  have hdet : GeneralLinearGroup.det (trdGramGL a b h) = Units.mk0 _ (neg_ne_zero.mpr h) := Units.ext (det_trdGram a b)
  rw [hdet] at this
  rw [show (trdGram a b) = ((trdGramGL a b h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) from rfl, this,
    ← ENNReal.coe_inv (distribHaarChar_ne_zero _)]
  rfl

end Local

section Global

open NumberField

variable {F : Type} [Field F] [NumberField F]

theorem trdGram_det_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : (16 : F) * a ^ 2 * b ^ 2 ≠ 0 := by
  have : (16 : F) ≠ 0 := by exact_mod_cast (show (16 : ℕ) ≠ 0 by norm_num)
  exact mul_ne_zero (mul_ne_zero this (pow_ne_zero 2 ha)) (pow_ne_zero 2 hb)

/-- **Global product of the trace-normalization factors**: $\prod_v|\det G|_v = \|-16a^2b^2\|_{\mathbb A} = 1$ for
$a, b\in F^\times$ (product formula). -/
@[kb "weil1982" "§2.3 [unverified page]"]
theorem ideleNorm_det_trdGram {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ideleNorm F (diagUnits F (Units.mk0 _ (neg_ne_zero.mpr (trdGram_det_ne_zero ha hb)))) = 1 :=
  ideleNorm_diagUnits _

end Global

end

end QuadFormsKB.Tamagawa.Measure.Weil
