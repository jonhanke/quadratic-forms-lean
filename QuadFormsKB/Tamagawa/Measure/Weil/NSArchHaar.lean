import QuadFormsKB.Tamagawa.Measure.LerayCount

/-!
# Local ratios of Haar measures along a locally injective homomorphism

**Layer:** abstract. $L$ a second countable locally compact group with a left Haar measure $\sigma$, $H$ a topological group with a
left-invariant measure $\lambda$ finite on compact sets (e.g. a Leray measure on $SO(Q)(F_w)$), $\varphi : L\to H$ a continuous
homomorphism which is locally injective (e.g. with finite kernel).

* **`exists_fibreCount_eq_smul`**: the fibre-counting pull-back $\varphi^\#\lambda$ (`Leray.fibreCount`) is a left-invariant measure on $L$,
  finite on compact sets, hence $\varphi^\#\lambda = \kappa\,\sigma$ with $\kappa$ = `haarScalarFactor` (Haar uniqueness on $L$).
* **`exists_measure_image_eq_smul`**: $\lambda(\varphi(Y)) = \kappa\,\sigma(Y)$ for every measurable $Y\subseteq L$ on which $\varphi$ is injective.
* **`ratio_eq_of_tendsto`**: the constant $\kappa$ is the limit of $\lambda(\varphi(Y_\delta))/\sigma(Y_\delta)$ along any family of such sets; in
  the form used below, $\kappa = \ell/s$ when $\lambda(\varphi(Y_\delta))/v_\delta\to\ell$ and $\sigma(Y_\delta)/v_\delta\to s > 0$.

This replaces the comparison of total masses of the definite proofs (where $L$ and $H$ are compact) by a comparison on one small
set, and needs no information on the image or the cokernel of $\varphi$.
-/

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Tamagawa.Measure.Leray

variable {L H : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [PolishSpace L] [MeasurableSpace L] [BorelSpace L]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  (σ : Measure L) [σ.IsHaarMeasure] (lam : Measure H) [lam.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts lam]
  (φ : L →* H) (hφ : Continuous φ) (hloc : IsLocInj φ)

include hφ hloc in
/-- $\varphi^\#\lambda$ is left invariant. -/
theorem isMulLeftInvariant_fibreCount : (fibreCount φ lam).IsMulLeftInvariant := by
  refine ⟨fun x => ?_⟩
  have hT : ∀ y : L, φ ((MeasurableEquiv.mulLeft x) y) = (MeasurableEquiv.mulLeft (φ x)) (φ y) := fun y => by
    simp [MeasurableEquiv.mulLeft]
  have h := fibreCount_map hφ hloc lam (MeasurableEquiv.mulLeft x) (MeasurableEquiv.mulLeft (φ x)) hT
  have h2 : lam.map (MeasurableEquiv.mulLeft (φ x)) = lam := map_mul_left_eq_self lam (φ x)
  rw [h2] at h
  exact h

include hφ hloc in
/-- **Haar uniqueness along $\varphi$**: $\varphi^\#\lambda = \kappa\,\sigma$ for some $\kappa\ge0$. -/
theorem exists_fibreCount_eq_smul : ∃ c : ℝ≥0, fibreCount φ lam = c • σ := by
  have := isMulLeftInvariant_fibreCount lam φ hφ hloc
  have := fibreCount_isFiniteMeasureOnCompacts hφ hloc lam
  exact ⟨_, isMulLeftInvariant_eq_smul _ σ⟩

include hφ hloc in
/-- **The local ratio**: there is $\kappa\ge0$ with $\lambda(\varphi(Y)) = \kappa\,\sigma(Y)$ for every measurable $Y$ on which
$\varphi$ is injective. -/
theorem exists_measure_image_eq_smul :
    ∃ c : ℝ≥0, ∀ Y : Set L, MeasurableSet Y → InjOn φ Y → lam (φ '' Y) = (c : ℝ≥0∞) * σ Y := by
  obtain ⟨c, hc⟩ := exists_fibreCount_eq_smul σ lam φ hφ hloc
  refine ⟨c, fun Y hY hinj => ?_⟩
  rw [← fibreCount_apply_of_injOn hφ hloc lam hY hinj, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

/-- **Identifying the constant from asymptotics**: if $f(\delta) = \kappa\,g(\delta)$ eventually,
$f/v\to\ell$ and $g/v\to s\ne0$, then $\kappa = \ell/s$. -/
theorem ratio_eq_of_tendsto {f g v : ℝ → ℝ} {κ ℓ s : ℝ} {l : Filter ℝ} [l.NeBot]
    (hfg : ∀ᶠ δ in l, f δ = κ * g δ) (hf : Tendsto (fun δ => f δ / v δ) l (𝓝 ℓ))
    (hg : Tendsto (fun δ => g δ / v δ) l (𝓝 s)) (hs : s ≠ 0) : κ = ℓ / s := by
  have h : Tendsto (fun δ => f δ / v δ) l (𝓝 (κ * s)) := by
    refine (hg.const_mul κ).congr' ?_
    filter_upwards [hfg] with δ hδ
    rw [hδ, mul_div_assoc]
  rw [tendsto_nhds_unique hf h, mul_div_cancel_right₀ _ hs]

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
