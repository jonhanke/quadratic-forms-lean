import QuadFormsKB.Tamagawa.Measure.Weil.AdelicMinkowski

/-!
# Pieces of the $\mathrm{GL}_n$ and quaternion scaling

The scaling $g_*\mu = \|\det g\|_{\mathbb A}^{-1}\mu$ for $g\in\mathrm{GL}_n(\mathbb A_F)$ acting on $\mathbb A_F^n$ is what the
twisted adelic Minkowski (`exists_ne_zero_map_mem_of_sub_mem`) needs for $\mathrm{SL}_2$-finiteness ($n = 2$) and for
Fujisaki on a quaternion algebra ($g = L_x$, $n = 4$, $\det L_x = \operatorname{nrd}(x)^2$). This file proves:

* `QuaternionAlgebra.det_mulLeft` (generic, any commutative ring): $\det(L_x) = \operatorname{nrd}(x)^2$ on
  $\mathbb H[R,a,0,b]$, with $\operatorname{nrd}(x) = \operatorname{re}(x\bar x)$;
* `map_mulVec_muInfVec`: the archimedean part, $M_*\mu_\infty^n = |\det_{\mathbb R}(\det M\cdot)|^{-1}\mu_\infty^n$ for
  $M\in\mathrm{GL}_n(F_\infty)$ (restriction of scalars: $\det_{\mathbb R} = N_{F_\infty/\mathbb R}\circ\det$,
  `LinearMap.det_restrictScalars`).

The finite-place part ($\Delta_f(M) = \prod_v|\det M_v|_v$) is not done.
-/

open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped Quaternion Classical

/-- **$\det(L_x) = \operatorname{nrd}(x)^2$** for left multiplication on $\mathbb H[R,a,0,b]$ over any commutative ring,
with $\operatorname{nrd}(x) = \operatorname{re}(x\bar x) = x_0^2 - a x_1^2 - b x_2^2 + ab x_3^2$. -/
theorem QuaternionAlgebra.det_mulLeft {R : Type*} [CommRing R] (a b : R) (x : ℍ[R,a,0,b]) :
    LinearMap.det (LinearMap.mulLeft R x) = ((x * star x).re) ^ 2 := by
  rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK a 0 b), Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, LinearMap.toMatrix_apply, Fin.succAbove,
    QuaternionAlgebra.basisOneIJK, Matrix.submatrix]
  ring

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

/-- **Archimedean $\mathrm{GL}_n$ scaling.** For $M\in\mathrm{GL}_n(F_\infty)$ acting on $F_\infty^n$,
$M_*\mu_\infty^n = |\det_{\mathbb R}(x\mapsto\det M\cdot x)|^{-1}\,\mu_\infty^n$ (for $n = 1$ this is
`distribHaarChar_mixedSpace`). -/
theorem map_mulVec_muInfVec {n : ℕ} (M : Matrix (Fin n) (Fin n) (mixedSpace F)) (hM : IsUnit M.det) :
    Measure.map M.mulVec (muInfVec F (Fin n)) =
      ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ M.det)|⁻¹ • muInfVec F (Fin n) := by
  have hdet : LinearMap.det ((Matrix.mulVecLin M).restrictScalars ℝ) =
      Algebra.norm ℝ M.det := by
    rw [LinearMap.det_restrictScalars, show Matrix.mulVecLin M = Matrix.toLin' M from rfl,
      LinearMap.det_toLin']
  have h0 : LinearMap.det ((Matrix.mulVecLin M).restrictScalars ℝ) ≠ 0 := by
    rw [hdet]; exact (hM.map (Algebra.norm ℝ)).ne_zero
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := muInfVec F (Fin n)) h0
  rw [hdet, Algebra.norm_apply, abs_inv] at this
  exact this
