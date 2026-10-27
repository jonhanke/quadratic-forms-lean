import QuadFormsKB.Tamagawa.Measure.SphereLerayC
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchReal

/-!
# Densities of the sphere Leray measures in a chart at a point

**Layer:** one archimedean place. For a quaternary form $Q$ and a family of sets $A_\delta$ in the sphere $S_1 = \{Q = 1\}$ which are the
images of small balls under a chart $g$, the cone over $A_\delta$ with radial parameters in a small interval (real) or a small disc
around $1$ (complex) is the image of a small ball under $G(t,z) = e^tg(z)$, resp. $\beta g(z)$. Polar coordinates
(`comap_pol`, `MC_prod`) and the image-of-a-ball asymptotics `tendsto_image_ball_div` give

* **`tendsto_nu_div`** (real): $\nu(A_\delta)/\mathrm{vol}(B^3_\delta)\to|\det DG(0)|$;
* **`tendsto_nuC_div`** (complex chart, $z\in\mathbb C^3$): $\nu_{\mathbb C}(A_\delta)/\mathrm{vol}(B^{\mathbb C^3}_\delta)\to|\det_{\mathbb R}DG(0)|$;

with $\sigma = \nu/(2|c|)$, resp. $\sigma = \nu/|2c|^2$ (`sig`, `sigC`). These are the sphere-side inputs of the local ratios.
Balls are for the sup norms, so $B^4_\delta = (-\delta,\delta)\times B^3_\delta$ and $B^{\mathbb C^4}_\delta = D_\delta(0)\times B^{\mathbb C^3}_\delta$.
-/

open MeasureTheory Measure Set Filter Topology Metric
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

/-! ### Real spheres -/

section Real

open SphereLeray

variable {n : ℕ}

/-- **Polar coordinates on product sets**: $\mathrm{vol}(\mathrm{pol}(T\times A)) = \mathrm{rad}_n(T)\,\nu(A)$. -/
theorem volume_pol_prod {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (hn : 1 ≤ n) {T : Set ℝ} (hT : MeasurableSet T)
    {A : Set (Sph Q c)} (hA : MeasurableSet A) :
    volume (pol Q c '' (T ×ˢ A)) = rad n T * nu Q c A := by
  haveI := sigmaFinite_nu (Q := Q) hc
  rw [← (measurableEmbedding_pol hc).comap_apply, comap_pol hc hn, Measure.prod_prod]

/-- $2\delta e^{-n\delta}\le\mathrm{rad}_n(-\delta,\delta)\le2\delta e^{n\delta}$. -/
theorem rad_Ioo_bounds {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (2 * δ * Real.exp (-(n * δ))) ≤ rad n (Ioo (-δ) δ) ∧
      rad n (Ioo (-δ) δ) ≤ ENNReal.ofReal (2 * δ * Real.exp (n * δ)) := by
  have hvol : volume (Ioo (-δ) δ) = ENNReal.ofReal (2 * δ) := by rw [Real.volume_Ioo]; ring_nf
  rw [rad, withDensity_apply _ measurableSet_Ioo]
  constructor
  · calc ENNReal.ofReal (2 * δ * Real.exp (-(n * δ)))
        = ∫⁻ _ in Ioo (-δ) δ, ENNReal.ofReal (Real.exp (-(n * δ))) := by
          rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
      _ ≤ _ := setLIntegral_mono (by fun_prop) fun t ht => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (by nlinarith [ht.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  · calc ∫⁻ t in Ioo (-δ) δ, ENNReal.ofReal (Real.exp (n * t))
        ≤ ∫⁻ _ in Ioo (-δ) δ, ENNReal.ofReal (Real.exp (n * δ)) := setLIntegral_mono (by fun_prop)
          fun t ht => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [ht.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      _ = _ := by rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem tendsto_two_mul_div_rad :
    Tendsto (fun δ => 2 * δ / (rad n (Ioo (-δ) δ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto (fun δ : ℝ => Real.exp (-(n * δ))) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun δ : ℝ => Real.exp (-(n * δ)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun δ : ℝ => Real.exp (n * δ)) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun δ : ℝ => Real.exp (n * δ) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hhi' : Tendsto (fun δ : ℝ => (Real.exp (n * δ))⁻¹) (𝓝[>] 0) (𝓝 1) := by simpa using hhi.inv₀ one_ne_zero
  have hlo' : Tendsto (fun δ : ℝ => (Real.exp (-(n * δ)))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using hlo.inv₀ one_ne_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hhi' hlo' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    obtain ⟨-, h2⟩ := rad_Ioo_bounds (n := n) hδ
    have hpos : 0 < (rad n (Ioo (-δ) δ)).toReal := by
      obtain ⟨h1, -⟩ := rad_Ioo_bounds (n := n) hδ
      refine ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le ?_ h1)) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2)
      exact ENNReal.ofReal_pos.2 (by positivity)
    have h2' : (rad n (Ioo (-δ) δ)).toReal ≤ 2 * δ * Real.exp (n * δ) :=
      (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2) ENNReal.ofReal_ne_top).2 h2 |>.trans
        (le_of_eq (ENNReal.toReal_ofReal (by positivity)))
    show (Real.exp (n * δ))⁻¹ ≤ 2 * δ / (rad n (Ioo (-δ) δ)).toReal
    rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hpos]
    linarith
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    obtain ⟨h1, h2⟩ := rad_Ioo_bounds (n := n) hδ
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    have h1' : 2 * δ * Real.exp (-(n * δ)) ≤ (rad n (Ioo (-δ) δ)).toReal := by
      rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ * Real.exp (-(n * δ)))]
      exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).2 h1
    have hpos : 0 < 2 * δ * Real.exp (-(n * δ)) := by positivity
    show 2 * δ / (rad n (Ioo (-δ) δ)).toReal ≤ (Real.exp (-(n * δ)))⁻¹
    rw [inv_eq_one_div, div_le_div_iff₀ (hpos.trans_le h1') (Real.exp_pos _)]
    linarith

theorem volume_ball_four (δ : ℝ) (hδ : 0 < δ) :
    (volume (ball (0 : Fin 4 → ℝ) δ)).toReal = 2 * δ * (volume (ball (0 : Fin 3 → ℝ) δ)).toReal := by
  rw [Real.volume_pi_ball _ hδ, Real.volume_pi_ball _ hδ, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [Fintype.card_fin]; ring

/-- **The cone density in a chart** (real): if $G(B^4_\delta) = \mathrm{pol}((-\delta,\delta)\times A_\delta)$ for small $\delta$ and $G$ has strict
derivative $L$ at $0$, then $\nu(A_\delta)/\mathrm{vol}(B^3_\delta)\to|\det L|$. -/
theorem tendsto_nu_div {Q : QuadForm ℝ 4} {A : ℝ → Set (Sph Q 1)} (hA : ∀ δ, MeasurableSet (A δ))
    {G : (Fin 4 → ℝ) → Fin 4 → ℝ} {L : (Fin 4 → ℝ) →L[ℝ] Fin 4 → ℝ} (hG : HasStrictFDerivAt G L 0)
    (himg : ∀ᶠ δ in 𝓝[>] (0 : ℝ), G '' ball 0 δ = pol Q 1 '' (Ioo (-δ) δ ×ˢ A δ)) :
    Tendsto (fun δ => (nu Q 1 (A δ)).toReal / (volume (ball (0 : Fin 3 → ℝ) δ)).toReal) (𝓝[>] 0)
      (𝓝 |L.det|) := by
  have hT := tendsto_image_ball_div (volume : Measure (Fin 4 → ℝ)) hG
  -- `G` is bounded on small balls
  have hbdd : ∀ᶠ δ in 𝓝[>] (0 : ℝ), volume (G '' ball 0 δ) ≠ ⊤ := by
    have hc : ContinuousAt G 0 := hG.hasFDerivAt.continuousAt
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds (ball_mem_nhds (G 0) one_pos))
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hr)] with δ hδ
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (measure_ball_lt_top (x := G 0) (r := 1)))
    rintro _ ⟨z, hz, rfl⟩
    exact hsub (ball_subset_ball (le_of_lt hδ) hz)
  have key : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (nu Q 1 (A δ)).toReal / (volume (ball (0 : Fin 3 → ℝ) δ)).toReal =
      (volume (G '' ball 0 δ)).toReal / (volume (ball (0 : Fin 4 → ℝ) δ)).toReal *
        (2 * δ / (rad 4 (Ioo (-δ) δ)).toReal) := by
    filter_upwards [himg, hbdd, self_mem_nhdsWithin] with δ hδ hfin (hδ0 : 0 < δ)
    rw [hδ, volume_pol_prod one_ne_zero (by norm_num) measurableSet_Ioo (hA δ)] at hfin ⊢
    obtain ⟨h1, h2⟩ := rad_Ioo_bounds (n := 4) hδ0
    have hr0 : rad 4 (Ioo (-δ) δ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) h1)
    have hrt : rad 4 (Ioo (-δ) δ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    have hnt : nu Q 1 (A δ) ≠ ⊤ := fun h => hfin (by rw [h, ENNReal.mul_top hr0])
    have hrpos : 0 < (rad 4 (Ioo (-δ) δ)).toReal := ENNReal.toReal_pos hr0 hrt
    have hv3 : 0 < (volume (ball (0 : Fin 3 → ℝ) δ)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos volume _ hδ0).ne' measure_ball_lt_top.ne
    rw [ENNReal.toReal_mul, volume_ball_four δ hδ0]
    field_simp
  have h := hT.mul (tendsto_two_mul_div_rad (n := 4))
  rw [mul_one] at h
  exact h.congr' (key.mono fun δ hδ => hδ.symm)

end Real

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
