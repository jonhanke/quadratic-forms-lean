/-
Adapted from Sphere-Packing-Lean (Apache-2.0), math-inc/Sphere-Packing-Lean
file `SpherePacking/ForMathlib/FourierLinearEquiv.lean`, commit 1e98fb493088948ca7bbf47d7faed49cc5b39fc4.
Ported to Mathlib for Lean v4.35.0 for QuadFormsKB.
Original copyright: the Sphere-Packing-Lean contributors. Licensed under the Apache License 2.0.
-/
import Mathlib


/-!
# Fourier linear equivalences

This file proves results such as `fourier_comp_linearEquiv`.
-/

namespace SpherePacking.ForMathlib.Fourier

open scoped FourierTransform
open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Change-of-variables formula for the Fourier transform under an invertible linear map.

For `A : V ≃ₗ[ℝ] V`, we have
`𝓕 (f ∘ A) w = |det A|⁻¹ • 𝓕 f ((A.symm).adjoint w)`.
-/
theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
        𝓕 f (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) := by
  simp only [Real.fourier_eq]
  have hmap :
      Measure.map (⇑A) (volume : Measure V) =
        ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • (volume : Measure V) := by
    simpa using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure V))
        (LinearEquiv.isUnit_det' A).ne_zero)
  let g : V → ℂ := fun y ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y
  have hsub :
      (∫ x : V, Real.fourierChar (-(inner ℝ x w)) • f (A x)) =
        ∫ y : V, g y ∂Measure.map (⇑A) (volume : Measure V) := by
    let e : V ≃ᵐ V := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
    simpa [g, e] using (MeasureTheory.integral_map_equiv (μ := (volume : Measure V)) e g).symm
  have hscale :
      (∫ y : V, g y ∂Measure.map (⇑A) (volume : Measure V)) =
        (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ • ∫ y : V, g y := by
    rw [hmap, MeasureTheory.integral_smul_measure]
    simp [abs_inv]
  have hadj :
      (fun y : V ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y) =
        fun y : V ↦
          Real.fourierChar (-(inner ℝ y (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w))) • f y := by
    funext y
    simp [LinearMap.adjoint_inner_right]
  calc
    (∫ x : V, Real.fourierChar (-(inner ℝ x w)) • f (A x)) =
        ∫ y : V, g y ∂Measure.map (⇑A) (volume : Measure V) := hsub
    _ = (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ • ∫ y : V, g y := hscale
    _ = (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
          ∫ y : V,
            Real.fourierChar (-(inner ℝ y (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w))) •
              f y := by
          simp [g, hadj]

end SpherePacking.ForMathlib.Fourier
