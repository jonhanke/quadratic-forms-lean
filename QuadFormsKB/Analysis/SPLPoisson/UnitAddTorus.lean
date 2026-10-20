/-
Adapted from Sphere-Packing-Lean (Apache-2.0), math-inc/Sphere-Packing-Lean
file `SpherePacking/CohnElkies/PoissonSummationLattices/UnitAddTorus.lean`, commit 1e98fb493088948ca7bbf47d7faed49cc5b39fc4.
Ported to Mathlib for Lean v4.35.0 for QuadFormsKB.
Original copyright: the Sphere-Packing-Lean contributors. Licensed under the Apache License 2.0.
-/
import Mathlib

/-!
Helper lemmas about the quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n` used in the Poisson summation
development.
-/

open scoped BigOperators Real
open MeasureTheory

namespace SchwartzMap.UnitAddTorus

/-- The coordinatewise quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n`. -/
def coeFun (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)

/-- Continuity of the coordinatewise quotient map `coeFun`. -/
@[continuity]
theorem continuous_coeFun {n : ℕ} : Continuous (coeFun n) :=
  continuous_pi fun i => (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_apply i)

/-- `coeFun` is an open quotient map, so it presents `(ℝ/ℤ)^n` as a quotient of `ℝ^n`.
(Port note: the original proof by induction on `n` is replaced by Mathlib's
`IsOpenQuotientMap.piMap`.) -/
theorem isOpenQuotientMap_coeFun (n : ℕ) : IsOpenQuotientMap (coeFun n) :=
  IsOpenQuotientMap.piMap (A := fun _ : Fin n => ℝ) (B := fun _ : Fin n => UnitAddCircle)
    fun _ => QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ))

theorem measurePreserving_coeFun (n : ℕ) (t : ℝ) :
    MeasurePreserving (coeFun n)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus (Fin n))) := by
  -- `coeFun` is the product of the coordinatewise quotient maps `ℝ → UnitAddCircle`,
  -- each of which is measure-preserving on a fundamental interval.
  exact
    (MeasureTheory.measurePreserving_pi
      (μ := fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (ν := fun _ : Fin n => (volume : Measure UnitAddCircle))
      (hf := fun _ => UnitAddCircle.measurePreserving_mk t))

theorem volume_restrict_pi_eq_pi_restrict (n : ℕ) (t : ℝ) :
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) := by
  exact (Measure.restrict_pi_pi
    (μ := fun _ : Fin n => (volume : Measure ℝ)) (s := fun _ : Fin n => Set.Ioc t (t + 1)))

theorem mFourier_apply_coeFun (n : ℕ) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (coeFun n x) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  -- Unfold, then rewrite `fourier` explicitly on real representatives and use `exp_sum`.
  simpa [UnitAddTorus.mFourier, ContinuousMap.coe_mk, coeFun, fourier_coe_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 2 * π * Complex.I * ((k i : ℝ) * x i))).symm

/--
Evaluate the additive character `mFourier k` on a point `x : ℝ^n`
viewed in the torus via `coeFun`.
-/
theorem mFourier_apply_coeFun_ofLp (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coeFun n (WithLp.ofLp x)) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa using (mFourier_apply_coeFun (n := n) (k := k) (x := WithLp.ofLp x))

/--
Pull back Haar integration on `(ℝ/ℤ)^n` to the fundamental cube `∏ i, (t, t+1] ⊆ ℝ^n`.
-/
theorem integral_eq_integral_preimage_coeFun (n : ℕ) (t : ℝ) (g : UnitAddTorus (Fin n) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin n)))) :
    (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coeFun n x) ∂(volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) := by
  have hmp := measurePreserving_coeFun n t
  have h1 :
      (∫ y : UnitAddTorus (Fin n), g y) =
        ∫ x, g (coeFun n x) ∂(Measure.pi fun _ : Fin n =>
          (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))) := by
    rw [← hmp.map_eq]
    simpa using (MeasureTheory.integral_map (hφ := hmp.aemeasurable) (f := g)
      (hfm := by simpa [hmp.map_eq] using hg))
  simpa [(volume_restrict_pi_eq_pi_restrict n t).symm] using h1

end SchwartzMap.UnitAddTorus
