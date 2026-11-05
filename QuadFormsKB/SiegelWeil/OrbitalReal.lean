/-
# Whittaker integral = orbital integral at a real place, any signature
**Layer:** one real place. This is the archimedean half of the *Fourier-coefficient form* of the Siegel–Weil formula
for indefinite forms (Weil 1965, *Sur la formule de Siegel*, §§ 8–10 [unverified]; Kudla, *Some extensions of the
Siegel–Weil formula*, §1 [unverified]): the $m$-th local Whittaker integral of the Siegel–Weil section of $\Phi$ is
the integral of $\Phi$ over the quadric $\{Q = m\}$ for the Leray measure.

**Setting.** $Q$ a real quadratic form in $n$ variables (`QuadForm ℝ n`, any signature), $S_t = \{x\in\mathbb R^n : Q(x) = t\}$
and $\sigma_t$ the Leray measure $|dx/dQ|$ on $S_t$ (`SphereLeray.sig`, $t\ne0$). For $\Phi\ge0$ on $\mathbb R^n$ the
**orbital integral** is
$$\rho_\Phi(t) = \int_{S_t}\Phi\,d\sigma_t\qquad(\texttt{orbI}).$$

**Proves**
* `lintegral_eq_lintegral_orbI` (**coarea formula**, $Q$ with null cone of measure zero, e.g. every nondegenerate
  diagonal form, `volume_diag_eval_eq_zero`): $\int_{\mathbb R^n}\Phi\,dx = \int_{\mathbb R}\rho_\Phi(t)\,dt$, and more
  generally $\int\Phi(x)g(Q(x))\,dx = \int g(t)\rho_\Phi(t)\,dt$ (`lintegral_mul_comp_eq`), i.e. $Q_*(\Phi\,dx) = \rho_\Phi\,dt$
  (`map_withDensity_eq`).
* `fourier_orbR` : the Fourier transform of $\rho_\Phi$ is $\int\Phi(x)e(-bQ(x))\,dx$ (for $\Phi$ integrable).
* `tendsto_integral_cexp_fourier`: regularized Fourier inversion at a point of continuity (from Mathlib's proof of
  Fourier inversion; no integrability of $\hat f$ needed).
* **`tendsto_whittakerReg`** (the local identity, regularized): for $\Phi\ge0$ integrable and $\rho_\Phi$ continuous at $m$,
  $$\lim_{c\to\infty}\int_{\mathbb R}e^{-b^2/c}\Big(\int_{\mathbb R^n}\Phi(x)e(bQ(x))\,dx\Big)e(-mb)\,db = \rho_\Phi(m).$$
* **`integral_whittaker_eq_orbR`**: if $b\mapsto\int\Phi(x)e(bQ(x))\,dx$ is integrable, the Whittaker integral converges
  absolutely and equals $\rho_\Phi(m)$.

The Weil-representation section is $f_\Phi(wn(b)) = \gamma_Vc_B\int\Phi(x)\psi(bQ(x))\,dx$ (`SiegelWeil.sec_wMat_nMat`), so
$W_\infty(m,\Phi) = \gamma_Vc_B\,\rho_\Phi(m)$: the archimedean analogue of `whittakerV_eq_localDensity`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.SphereLeray

open MeasureTheory Measure Set Filter Topology Complex
open scoped ENNReal FourierTransform RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Orbital

/-! ### Regularized Fourier inversion -/

section Inversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

/-- **Regularized Fourier inversion at a point of continuity**: for $f$ integrable and continuous at $v$,
$$\lim_{c\to\infty}\int_Ve^{-\|w\|^2/c}\,e(\langle v,w\rangle)\,\hat f(w)\,dw = f(v).$$
No integrability of $\hat f$ is assumed (Mathlib's `Real.tendsto_integral_gaussian_smul'` after Parseval for the
Gaussian). -/
theorem tendsto_integral_cexp_fourier {f : V → ℂ} (hf : Integrable f) {v : V} (hv : ContinuousAt f v) :
    Tendsto (fun c : ℝ => ∫ w : V, cexp (-c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫) * 𝓕 f w) atTop (𝓝 (f v)) := by
  refine (Real.tendsto_integral_gaussian_smul' hf hv).congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  have J : Integrable (fun w : V ↦ cexp (-c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫)) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
  have h2 : ∫ w : V, cexp (-c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫) * 𝓕 f w =
      ∫ w : V, 𝓕 (fun w ↦ cexp (-c⁻¹ * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫)) w • f w := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner J hf).symm
  rw [h2]
  congr with w
  symm
  have hc' : 0 < ((c⁻¹ : ℝ) : ℂ).re := by simpa using inv_pos.2 hc
  rw [fourier_gaussian_innerProductSpace' hc' v w]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  congr 2
  · congr 1; push_cast; field_simp
  · congr 1; push_cast; field_simp

end Inversion

/-! ### The coarea formula for a real quadratic form -/

section Coarea

open QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Siegel

variable {n : ℕ} (Q : QuadForm ℝ n)

/-- **The orbital integral** $\rho_\Phi(t) = \int_{S_t}\Phi\,d\sigma_t$ of $\Phi\ge0$ over the quadric $S_t = \{Q = t\}$ for the
Leray measure $\sigma_t$ (`SphereLeray.sig`; it is $0$ at $t = 0$). Parameters: `Q`, `Φ`, `t`. -/
@[kb "weil1965" "Sur la formule de Siegel: the integral of Φ over {Q = t} for |dx/dQ| [unverified]"]
def orbI (Φ : (Fin n → ℝ) → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ := ∫⁻ x, Φ x ∂sig Q t

/-- **Homogeneity**: $\rho_\Phi(a^2c) = a^{n-2}\int_{S_c}\Phi(ax)\,d\sigma_c(x)$ for $a > 0$. -/
theorem orbI_sq_mul {c a : ℝ} (hc : c ≠ 0) (ha : 0 < a) (hn : 2 ≤ n) {Φ : (Fin n → ℝ) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    orbI Q Φ (a ^ 2 * c) = ENNReal.ofReal (a ^ (n - 2)) * ∫⁻ x, Φ (a • (x : Fin n → ℝ)) ∂sig Q c := by
  rw [orbI, sig_scale hc ha hn, lintegral_smul_measure,
    lintegral_map (f := fun x : Sph Q (a ^ 2 * c) => Φ x) (hΦ.comp measurable_subtype_coe)
      (continuous_sphScale Q c a).measurable]
  rfl

theorem sqrt_pow_sub_two {u : ℝ} (hu : 0 < u) (hn : 2 ≤ n) :
    Real.sqrt u ^ (n - 2) = u ^ ((n : ℝ) / 2 - 1) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 1
  rw [Nat.cast_sub hn]; push_cast; ring

/-- The fibration over a half-line: $\int_{cQ>0}\Phi\,dx = \int_0^\infty\rho_\Phi(uc)\,du$ for $|c| = 1$. -/
theorem lintegral_posSet_eq {c : ℝ} (hc : |c| = 1) (hn : 2 ≤ n) {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y in posSet Q c, Φ y = ∫⁻ u in Ioi 0, orbI Q Φ (u * c) := by
  have hc0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; exact zero_ne_one hc
  rw [lintegral_posSet_fibration hc0 (by omega) hΦ]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu' : (0 : ℝ) < u := hu
  rw [show u * c = Real.sqrt u ^ 2 * c by rw [Real.sq_sqrt hu'.le], orbI_sq_mul Q hc0 (Real.sqrt_pos.2 hu') hn hΦ,
    hc, one_mul, sqrt_pow_sub_two hu' hn]

/-- $\{Q > 0\}$: $\int_{Q>0}\Phi\,dx = \int_{t>0}\rho_\Phi(t)\,dt$. -/
theorem lintegral_pos_eq (hn : 2 ≤ n) {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y in posSet Q 1, Φ y = ∫⁻ t in Ioi 0, orbI Q Φ t := by
  rw [lintegral_posSet_eq Q (by simp) hn hΦ]
  simp only [mul_one]

/-- $\{Q < 0\}$: $\int_{Q<0}\Phi\,dx = \int_{t<0}\rho_\Phi(t)\,dt$. -/
theorem lintegral_neg_eq (hn : 2 ≤ n) {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y in posSet Q (-1), Φ y = ∫⁻ t in Iio 0, orbI Q Φ t := by
  rw [lintegral_posSet_eq Q (by simp) hn hΦ]
  simp only [mul_neg, mul_one]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (orbI Q Φ) (Iio 0)
  rw [← h, show (Neg.neg ⁻¹' Iio (0 : ℝ)) = Ioi 0 by ext u; simp]

theorem orbI_zero (Φ : (Fin n → ℝ) → ℝ≥0∞) : orbI Q Φ 0 = 0 := by
  simp [orbI, sig]

/-- $t\mapsto\rho_\Phi(t)$ is measurable (by homogeneity it is $t^{n/2-1}\int_{S_{\pm1}}\Phi(\sqrt{|t|}x)\,d\sigma_{\pm1}$). -/
theorem measurable_orbI (hn : 2 ≤ n) {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) : Measurable (orbI Q Φ) := by
  have := sigmaFinite_sig (Q := Q) (c := 1) one_ne_zero
  have := sigmaFinite_sig (Q := Q) (c := -1) (by norm_num)
  set gp : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.sqrt t ^ (n - 2)) * ∫⁻ x, Φ (Real.sqrt t • (x : Fin n → ℝ)) ∂sig Q 1
  set gm : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.sqrt (-t) ^ (n - 2)) * ∫⁻ x, Φ (Real.sqrt (-t) • (x : Fin n → ℝ)) ∂sig Q (-1)
  have hmp : Measurable gp := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).mul ?_
    exact Measurable.lintegral_prod_right' (f := fun p : ℝ × Sph Q 1 => Φ (Real.sqrt p.1 • (p.2 : Fin n → ℝ)))
      (hΦ.comp (by fun_prop))
  have hmm : Measurable gm := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).mul ?_
    exact Measurable.lintegral_prod_right'
      (f := fun p : ℝ × Sph Q (-1) => Φ (Real.sqrt (-p.1) • (p.2 : Fin n → ℝ))) (hΦ.comp (by fun_prop))
  have e : orbI Q Φ = (Ioi 0).piecewise gp ((Iio 0).piecewise gm 0) := by
    funext t
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have h1 : t ∉ Ioi (0 : ℝ) := fun h => lt_asymm ht h
      rw [piecewise_eq_of_notMem _ _ _ h1, piecewise_eq_of_mem _ _ _ (show t ∈ Iio 0 from ht)]
      have hneg : 0 < -t := neg_pos.mpr ht
      conv_lhs => rw [show t = Real.sqrt (-t) ^ 2 * (-1) by rw [Real.sq_sqrt hneg.le]; ring]
      exact orbI_sq_mul Q (by norm_num) (Real.sqrt_pos.2 hneg) hn hΦ
    · simp [orbI_zero]
    · rw [piecewise_eq_of_mem _ _ _ (show t ∈ Ioi 0 from ht)]
      conv_lhs => rw [show t = Real.sqrt t ^ 2 * 1 by rw [Real.sq_sqrt ht.le]; ring]
      exact orbI_sq_mul Q one_ne_zero (Real.sqrt_pos.2 ht) hn hΦ
  rw [e]
  exact hmp.piecewise measurableSet_Ioi (hmm.piecewise measurableSet_Iio measurable_const)

theorem posSet_one : posSet Q 1 = {x | 0 < Q.eval x} := by ext x; simp [posSet]

theorem posSet_neg_one : posSet Q (-1) = {x | Q.eval x < 0} := by ext x; simp [posSet]

/-- **The coarea formula** $\int_{\mathbb R^n}\Phi\,dx = \int_{\mathbb R}\rho_\Phi(t)\,dt$ (Leray), for $Q$ whose null cone
$\{Q = 0\}$ has measure zero (`volume_diag_eval_eq_zero` for nondegenerate diagonal $Q$). -/
@[kb "weil1982" "§2.2 (dx = σ_t ⊗ dt on the fibres of Q) [unverified]"]
theorem lintegral_eq_lintegral_orbI (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0)
    {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) : ∫⁻ x, Φ x = ∫⁻ t, orbI Q Φ t := by
  have hmP : MeasurableSet (posSet Q 1) := (isOpen_posSet Q 1).measurableSet
  have hmN : MeasurableSet (posSet Q (-1)) := (isOpen_posSet Q (-1)).measurableSet
  have hdisj : Disjoint (posSet Q 1) (posSet Q (-1)) := by
    rw [posSet_one, posSet_neg_one]
    exact Set.disjoint_left.mpr fun x h1 h2 => lt_asymm (show 0 < Q.eval x from h1) h2
  have hcompl : (posSet Q 1 ∪ posSet Q (-1))ᶜ = {x | Q.eval x = 0} := by
    rw [posSet_one, posSet_neg_one]; ext x; simp [le_antisymm_iff]
  have hdisjT : Disjoint (Ioi (0 : ℝ)) (Iio 0) := Set.disjoint_left.mpr fun x h1 h2 =>
    lt_asymm (show (0 : ℝ) < x from h1) h2
  have hcomplT : (Ioi (0 : ℝ) ∪ Iio 0)ᶜ = {0} := by ext t; simp [le_antisymm_iff]
  have hT := lintegral_add_compl (orbI Q Φ) ((measurableSet_Ioi (a := (0 : ℝ))).union (measurableSet_Iio (a := (0 : ℝ))))
    (μ := volume)
  rw [hcomplT, setLIntegral_measure_zero _ _ Real.volume_singleton, add_zero,
    lintegral_union measurableSet_Iio hdisjT] at hT
  have hX := lintegral_add_compl Φ (hmP.union hmN) (μ := volume)
  rw [hcompl, setLIntegral_measure_zero _ _ hnull, add_zero, lintegral_union hmN hdisj] at hX
  rw [← hX, ← hT, lintegral_pos_eq Q hn hΦ, lintegral_neg_eq Q hn hΦ]

/-- $\rho_{\Phi\cdot g\circ Q} = g\cdot\rho_\Phi$. -/
theorem orbI_mul_comp (Φ : (Fin n → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) (g : ℝ → ℝ≥0∞) (t : ℝ) :
    orbI Q (fun x => Φ x * g (Q.eval x)) t = orbI Q Φ t * g t := by
  have h : ∀ x : Sph Q t, Φ x * g (Q.eval x) = Φ x * g t := fun x => by
    rw [show Q.eval (x : Fin n → ℝ) = t from x.2]
  rw [orbI, orbI]
  simp_rw [h]
  exact lintegral_mul_const _ (hΦ.comp measurable_subtype_coe)

/-- **The coarea formula, weighted**: $\int\Phi(x)\,g(Q(x))\,dx = \int\rho_\Phi(t)\,g(t)\,dt$. -/
theorem lintegral_mul_comp_eq (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0)
    {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, Φ x * g (Q.eval x) = ∫⁻ t, orbI Q Φ t * g t := by
  have h := lintegral_eq_lintegral_orbI Q hn hnull (Φ := fun x => Φ x * g (Q.eval x))
    (hΦ.mul (hg.comp (continuous_eval_real Q).measurable))
  rw [h]
  exact lintegral_congr fun t => orbI_mul_comp Q Φ hΦ g t

/-- **Push-forward**: $Q_*(\Phi\,dx) = \rho_\Phi\,dt$. -/
theorem map_withDensity_eq (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0)
    {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (volume.withDensity Φ).map Q.eval = volume.withDensity (orbI Q Φ) := by
  ext s hs
  rw [Measure.map_apply (continuous_eval_real Q).measurable hs, withDensity_apply _ ((continuous_eval_real Q).measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator ((continuous_eval_real Q).measurable hs),
    ← lintegral_indicator hs]
  have h := lintegral_mul_comp_eq Q hn hnull hΦ (g := s.indicator 1) (measurable_one.indicator hs)
  have e1 : ∀ x, (Q.eval ⁻¹' s).indicator Φ x = Φ x * s.indicator 1 (Q.eval x) := fun x => by
    by_cases hx : Q.eval x ∈ s
    · simp [Set.indicator_of_mem (show x ∈ Q.eval ⁻¹' s from hx), Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem (show x ∉ Q.eval ⁻¹' s from hx), Set.indicator_of_notMem hx]
  have e2 : ∀ t, s.indicator (orbI Q Φ) t = orbI Q Φ t * s.indicator 1 t := fun t => by
    by_cases ht : t ∈ s
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  simp_rw [e1, e2]
  exact h

/-! ### Real-valued test functions and the Fourier transform of $\rho_\Phi$ -/

/-- **The orbital integral of a real test function** $\Phi\ge0$: $\rho_\Phi(t)\in\mathbb R$ (`orbI` of $\Phi$, as a real
number). Parameters: `Q`, `Φ`, `t`. -/
def orbR (Φ : (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ := (orbI Q (fun x => ENNReal.ofReal (Φ x)) t).toReal

variable {Q}

theorem ae_orbI_lt_top (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0) {Φ : (Fin n → ℝ) → ℝ}
    (hΦm : Measurable Φ) (hΦ : Integrable Φ) : ∀ᵐ t, orbI Q (fun x => ENNReal.ofReal (Φ x)) t < ∞ := by
  refine ae_lt_top (measurable_orbI Q hn hΦm.ennreal_ofReal) ?_
  rw [← lintegral_eq_lintegral_orbI Q hn hnull hΦm.ennreal_ofReal]
  exact hΦ.lintegral_lt_top.ne

/-- **The coarea formula against a bounded weight** (Bochner form): for $\Phi\ge0$ measurable and integrable and $g$
continuous, $\int_{\mathbb R}\rho_\Phi(t)\,g(t)\,dt = \int_{\mathbb R^n}\Phi(x)\,g(Q(x))\,dx$. -/
theorem integral_orbR_mul (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0) {Φ : (Fin n → ℝ) → ℝ}
    (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ) {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ t, (orbR Q Φ t : ℂ) * g t = ∫ x, (Φ x : ℂ) * g (Q.eval x) := by
  have hm := hΦm.ennreal_ofReal
  have h1 : ∫ t, g t ∂(volume.withDensity (orbI Q fun x => ENNReal.ofReal (Φ x))) =
      ∫ t, (orbR Q Φ t : ℂ) * g t := by
    rw [integral_withDensity_eq_integral_toReal_smul (measurable_orbI Q hn hm) (ae_orbI_lt_top hn hnull hΦm hΦ)]
    simp [orbR, Complex.real_smul]
  have h2 : ∫ x, g (Q.eval x) ∂(volume.withDensity fun x => ENNReal.ofReal (Φ x)) =
      ∫ x, (Φ x : ℂ) * g (Q.eval x) := by
    rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp [ENNReal.toReal_ofReal (hΦ0 _), Complex.real_smul]
  rw [← h1, ← h2, ← map_withDensity_eq Q hn hnull hm,
    integral_map (continuous_eval_real Q).measurable.aemeasurable hg.aestronglyMeasurable]

theorem integrable_orbR (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0) {Φ : (Fin n → ℝ) → ℝ}
    (hΦm : Measurable Φ) (hΦ : Integrable Φ) : Integrable fun t => (orbR Q Φ t : ℂ) := by
  have hm := hΦm.ennreal_ofReal
  refine Integrable.ofReal (integrable_toReal_of_lintegral_ne_top (measurable_orbI Q hn hm).aemeasurable ?_)
  rw [← lintegral_eq_lintegral_orbI Q hn hnull hm]
  exact hΦ.lintegral_lt_top.ne

/-- **The Fourier transform of the orbital integral** is the oscillatory integral of $\Phi$ against $Q$:
$\hat\rho_\Phi(b) = \int_{\mathbb R}\rho_\Phi(t)e^{-2\pi itb}\,dt = \int_{\mathbb R^n}\Phi(x)\,e^{-2\pi ibQ(x)}\,dx$. -/
theorem fourier_orbR (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0) {Φ : (Fin n → ℝ) → ℝ}
    (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ) (b : ℝ) :
    𝓕 (fun t => (orbR Q Φ t : ℂ)) b = ∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (-b * Q.eval x)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := integral_orbR_mul hn hnull hΦm hΦ0 hΦ (g := fun t => cexp (2 * Real.pi * I * (-b * t)))
    (by fun_prop)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast; ring

/-- **The local identity, regularized** ("Whittaker = orbital integral" at a real place, any signature): for $\Phi\ge0$
integrable and $\rho_\Phi$ continuous at $m$,
$$\lim_{c\to\infty}\int_{\mathbb R}e^{-b^2/c}\Big(\int_{\mathbb R^n}\Phi(x)\,e(bQ(x))\,dx\Big)e(-mb)\,db = \rho_\Phi(m),$$
$e(x) = e^{2\pi ix}$. The inner integral is $f_\Phi(wn(b))/(\gamma_Vc_B)$ for the Siegel–Weil section of $\Phi$
(`sec_wMat_nMat`), so the left side is the $m$-th Whittaker integral of the normalized section, Gauss-regularized (the
archimedean analogue of the truncation $\lim_k\int_{\mathfrak p^{-k}}$). -/
@[kb "weil1965" "Sur la formule de Siegel: the local Whittaker integral is the integral over {Q = m} (real place) [unverified]"]
theorem tendsto_whittakerReg (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0) {Φ : (Fin n → ℝ) → ℝ}
    (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ) {m : ℝ}
    (hcont : ContinuousAt (orbR Q Φ) m) :
    Tendsto (fun c : ℝ => ∫ b : ℝ, cexp (-c⁻¹ * b ^ 2) *
      (∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (b * Q.eval x))) * cexp (2 * Real.pi * I * (-(m * b))))
      atTop (𝓝 (orbR Q Φ m : ℂ)) := by
  have hc' : ContinuousAt (fun t => (orbR Q Φ t : ℂ)) m := Complex.continuous_ofReal.continuousAt.comp hcont
  refine (tendsto_integral_cexp_fourier (integrable_orbR hn hnull hΦm hΦ) hc').congr fun c => ?_
  conv_rhs => rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [fourier_orbR hn hnull hΦm hΦ0 hΦ w, Complex.exp_add]
  simp only [Real.norm_eq_abs, RCLike.inner_apply, conj_trivial, ofReal_neg, neg_mul, neg_neg, mul_neg, even_two,
    Even.neg_pow]
  push_cast
  have hw : ((|w| : ℝ) : ℂ) ^ 2 = (w : ℂ) ^ 2 := by rw [← ofReal_pow, sq_abs, ofReal_pow]
  rw [hw]
  ring_nf

/-- **The local identity, absolutely convergent form**: if $b\mapsto\int\Phi(x)e(bQ(x))\,dx$ is integrable (e.g. the
Gaussian of the majorant for $n\ge3$), then
$$\int_{\mathbb R}\Big(\int_{\mathbb R^n}\Phi(x)\,e(bQ(x))\,dx\Big)e(-mb)\,db = \rho_\Phi(m)$$
at every $m$ where $\rho_\Phi$ is continuous. -/
@[kb "weil1965" "Sur la formule de Siegel: the local Whittaker integral is the integral over {Q = m} (real place) [unverified]"]
theorem integral_whittaker_eq_orbR (hn : 2 ≤ n) (hnull : volume {x | Q.eval x = 0} = 0) {Φ : (Fin n → ℝ) → ℝ}
    (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦ : Integrable Φ)
    (hW : Integrable fun b : ℝ => ∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (b * Q.eval x))) {m : ℝ}
    (hcont : ContinuousAt (orbR Q Φ) m) :
    ∫ b : ℝ, (∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (b * Q.eval x))) * cexp (2 * Real.pi * I * (-(m * b))) =
      orbR Q Φ m := by
  have hW' : Integrable fun b : ℝ => (∫ x, (Φ x : ℂ) * cexp (2 * Real.pi * I * (b * Q.eval x))) *
      cexp (2 * Real.pi * I * (-(m * b))) := by
    refine hW.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun b => ?_)
    rw [Complex.norm_exp]
    simp
  have h := Real.tendsto_integral_cexp_sq_smul hW'
  refine tendsto_nhds_unique h ((tendsto_whittakerReg hn hnull hΦm hΦ0 hΦ hcont).congr fun c => ?_)
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [Real.norm_eq_abs, smul_eq_mul]
  have hb : ((|b| : ℝ) : ℂ) ^ 2 = (b : ℂ) ^ 2 := by rw [← ofReal_pow, sq_abs, ofReal_pow]
  push_cast
  rw [hb]
  ring

end Coarea

/-! ### The null cone of a diagonal form; continuity of the orbital integral -/

section Regularity

open QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Siegel

theorem eval_diag_real {n : ℕ} (b z : Fin n → ℝ) : (QuadForm.diag b).eval z = ∑ i, b i * z i ^ 2 := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- **The null cone of a nondegenerate diagonal form has measure zero**: $\{x\in\mathbb R^{k+1} : \sum_ia_ix_i^2 = 0\}$ is
Lebesgue-null when $a_0\ne0$ (each line parallel to the $x_0$-axis meets it in at most two points). -/
theorem volume_diag_eval_eq_zero {k : ℕ} {a : Fin (k + 1) → ℝ} (ha : a 0 ≠ 0) :
    volume {x : Fin (k + 1) → ℝ | (QuadForm.diag a).eval x = 0} = 0 := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  set R : (Fin k → ℝ) → ℝ := fun y => ∑ i : Fin k, a i.succ * y i ^ 2
  set T : Set (ℝ × (Fin k → ℝ)) := {p | a 0 * p.1 ^ 2 + R p.2 = 0}
  have hT : MeasurableSet T := measurableSet_eq_fun (by fun_prop) measurable_const
  have hS : {x : Fin (k + 1) → ℝ | (QuadForm.diag a).eval x = 0} = e ⁻¹' T := by
    ext x
    simp only [mem_preimage, T, R, eval_diag_real, e,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    simp only [Set.mem_ofPred_eq, Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove_zero]
  rw [hS, hp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
  refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun y => ?_)
  simp only [Pi.zero_apply]
  set r := -R y / a 0
  have hsub : (fun x : ℝ => (x, y)) ⁻¹' T ⊆ {Real.sqrt r, -Real.sqrt r} := by
    intro x hx
    have hx' : a 0 * x ^ 2 + R y = 0 := hx
    have hx2 : x ^ 2 = r := by simp only [r]; rw [eq_div_iff ha]; linarith
    have habs : |x| = Real.sqrt r := by rw [← hx2, Real.sqrt_sq_eq_abs]
    rcases (abs_eq (Real.sqrt_nonneg r)).1 habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

variable {n : ℕ} {Q : QuadForm ℝ n}

/-- **Polynomial decay is integrable on $S_c$**: $\int_{S_c}(1+\|x\|)^{-(n+1)}\,d\nu_c < \infty$ (from $dx = e^{nt}dt\otimes\nu_c$ on
$\{cQ>0\}$, restricted to $t\in[-1,0]$). -/
theorem lintegral_nu_decay_lt_top {c : ℝ} (hc : c ≠ 0) (hn : 1 ≤ n) :
    ∫⁻ x, ENNReal.ofReal ((1 + ‖(x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ))) ∂nu Q c < ⊤ := by
  set f : Sph Q c → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + ‖(x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ)))
  set G : (Fin n → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal ((1 + ‖y‖) ^ (-(n + 1 : ℝ)))
  have hG : Measurable G := by fun_prop
  have hGfin : ∫⁻ y, G y < ⊤ :=
    (integrable_one_add_norm (E := Fin n → ℝ) (μ := volume) (r := n + 1) (by simp)).lintegral_lt_top
  have hlow : ENNReal.ofReal (Real.exp (-n)) * ∫⁻ x, f x ∂nu Q c ≤ ∫⁻ y in posSet Q c, G y := by
    rw [lintegral_posSet_pol hc hn hG]
    calc ENNReal.ofReal (Real.exp (-n)) * ∫⁻ x, f x ∂nu Q c
        = ∫⁻ t in Icc (-1 : ℝ) 0, ENNReal.ofReal (Real.exp (-n)) * ∫⁻ x, f x ∂nu Q c := by
          rw [setLIntegral_const, Real.volume_Icc]; norm_num
      _ ≤ ∫⁻ t in Icc (-1 : ℝ) 0, ENNReal.ofReal (Real.exp (n * t)) *
            ∫⁻ x, G (Real.exp t • (x : Fin n → ℝ)) ∂nu Q c := by
          refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
          gcongr with x
          · nlinarith [ht.1, (show (0 : ℝ) ≤ n by positivity)]
          · simp only [f, G]
            refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
            have : Real.exp t ≤ 1 := Real.exp_le_one_iff.2 ht.2
            nlinarith [norm_nonneg (x : Fin n → ℝ)]
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have h1 : ∫⁻ y in posSet Q c, G y < ⊤ := lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hGfin
  exact ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hlow h1).ne (by simp [Real.exp_pos])

theorem lintegral_sig_decay_lt_top {c : ℝ} (hc : c ≠ 0) (hn : 1 ≤ n) :
    ∫⁻ x, ENNReal.ofReal ((1 + ‖(x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ))) ∂sig Q c < ⊤ := by
  rw [sig, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_nu_decay_lt_top hc hn)

/-- **Continuity of the orbital integral off $0$**: if $\Phi\ge0$ is continuous with $\Phi(x)\le C(1+\|x\|)^{-(n+1)}$ (e.g. a
Schwartz function or the Gaussian), then $t\mapsto\rho_\Phi(t)$ is continuous at every $m\ne0$. -/
theorem continuousAt_orbR (hn : 2 ≤ n) {Φ : (Fin n → ℝ) → ℝ} (hΦc : Continuous Φ) (hΦ0 : ∀ x, 0 ≤ Φ x)
    {C : ℝ} (hdec : ∀ x, Φ x ≤ C * (1 + ‖x‖) ^ (-(n + 1 : ℝ))) {m : ℝ} (hm : m ≠ 0) :
    ContinuousAt (orbR Q Φ) m := by
  set F : ℝ → ℝ≥0∞ := fun a => ∫⁻ x, ENNReal.ofReal (Φ (a • (x : Fin n → ℝ))) ∂sig Q m
  set B : Sph Q m → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (C * 2 ^ (n + 1 : ℝ)) * ENNReal.ofReal ((1 + ‖(x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ)))
  have hBfin : ∫⁻ x, B x ∂sig Q m ≠ ⊤ := by
    rw [lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_sig_decay_lt_top hm (by omega)).ne
  have hC : 0 ≤ C := by
    have h1 := (hΦ0 0).trans (hdec 0)
    have h0 : (0 : ℝ) < (1 + ‖(0 : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ)) := by positivity
    exact nonneg_of_mul_nonneg_left h1 h0
  have hF : Tendsto F (𝓝 1) (𝓝 (F 1)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence B ?_ ?_ hBfin ?_
    · exact Eventually.of_forall fun a => (hΦc.comp (by fun_prop)).measurable.ennreal_ofReal
    · filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with a ha
      refine Eventually.of_forall fun x => ?_
      simp only [B]
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((hdec _).trans ?_)
      have ha0 : 0 < a := by linarith [show (0 : ℝ) < 1 / 2 by norm_num, ha.out]
      have hx : (1 + ‖(x : Fin n → ℝ)‖) / 2 ≤ 1 + ‖a • (x : Fin n → ℝ)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
        have : (1 / 2 : ℝ) < a := ha
        nlinarith [norm_nonneg (x : Fin n → ℝ)]
      have h2 : (1 + ‖a • (x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ)) ≤
          ((1 + ‖(x : Fin n → ℝ)‖) / 2) ^ (-(n + 1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith [(show (0 : ℝ) ≤ n by positivity)])
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul] at h2
      calc C * (1 + ‖a • (x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ))
          ≤ C * ((1 + ‖(x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ)) * 2 ^ (n + 1 : ℝ)) := by gcongr
        _ = C * 2 ^ (n + 1 : ℝ) * (1 + ‖(x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ)) := by ring
    · refine Eventually.of_forall fun x => ?_
      exact (ENNReal.continuous_ofReal.comp (hΦc.comp (by fun_prop))).tendsto 1
  have hF1 : F 1 = orbI Q (fun x => ENNReal.ofReal (Φ x)) m := by simp [F, orbI]
  have hF1fin : F 1 ≠ ⊤ := by
    refine ne_top_of_le_ne_top hBfin (lintegral_mono fun x => ?_)
    simp only [one_smul, B]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((hdec _).trans ?_)
    have h2 : (1 : ℝ) ≤ 2 ^ (n + 1 : ℝ) := Real.one_le_rpow (by norm_num) (by positivity)
    have h3 : (0 : ℝ) ≤ (1 + ‖(x : Fin n → ℝ)‖) ^ (-(n + 1 : ℝ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hC]
  -- the scaling parameter a(t) = √(t/m)
  have ha : Tendsto (fun t : ℝ => Real.sqrt (t / m)) (𝓝 m) (𝓝 1) := by
    have : Continuous fun t : ℝ => Real.sqrt (t / m) := by fun_prop
    simpa [div_self hm] using this.tendsto m
  have hev : ∀ᶠ t in 𝓝 m, orbI Q (fun x => ENNReal.ofReal (Φ x)) t =
      ENNReal.ofReal (Real.sqrt (t / m) ^ (n - 2)) * F (Real.sqrt (t / m)) := by
    have hpos : ∀ᶠ t in 𝓝 m, 0 < t / m := by
      have : Continuous fun t : ℝ => t / m := by fun_prop
      exact this.continuousAt.eventually (Ioi_mem_nhds (by simp [div_self hm] : (0 : ℝ) < m / m))
    filter_upwards [hpos] with t ht
    have ht' : t = Real.sqrt (t / m) ^ 2 * m := by rw [Real.sq_sqrt ht.le]; field_simp
    conv_lhs => rw [ht']
    exact orbI_sq_mul Q hm (Real.sqrt_pos.2 ht) hn hΦc.measurable.ennreal_ofReal
  have hlim : Tendsto (fun t => orbI Q (fun x => ENNReal.ofReal (Φ x)) t) (𝓝 m)
      (𝓝 (orbI Q (fun x => ENNReal.ofReal (Φ x)) m)) := by
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    have h1 : Tendsto (fun t => ENNReal.ofReal (Real.sqrt (t / m) ^ (n - 2))) (𝓝 m) (𝓝 1) := by
      have := ((ENNReal.continuous_ofReal.comp (continuous_pow (n - 2))).tendsto 1).comp ha
      simp only [Function.comp_def, one_pow, ENNReal.ofReal_one] at this
      exact this
    have h2 := (hF.comp ha)
    rw [← hF1, ← one_mul (F 1)]
    exact ENNReal.Tendsto.mul h1 (Or.inr hF1fin) h2 (Or.inr ENNReal.one_ne_top)
  rw [hF1] at hF1fin
  exact (ENNReal.tendsto_toReal hF1fin).comp hlim

end Regularity

/-! ### The Gaussian of the majorant -/

section Gauss

open QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Siegel

theorem exp_neg_mul_sq_mul_pow_le {α : ℝ} (hα : 0 < α) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-α * s ^ 2) * (1 + s) ^ N ≤ 2 ^ N * (1 + N.factorial / α ^ N) := by
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have h1 : s ^ (2 * N) ≤ N.factorial / α ^ N * Real.exp (α * s ^ 2) := by
    have := Real.pow_div_factorial_le_exp (α * s ^ 2) (by positivity) N
    rw [div_le_iff₀ hfac, mul_pow, ← pow_mul] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [this]
  have h2 : (1 + s) ^ N ≤ 2 ^ N * (1 + s ^ (2 * N)) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
        _ ≤ 2 ^ N * (1 + s ^ (2 * N)) := by
          have : (0 : ℝ) ≤ s ^ (2 * N) := by positivity
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) N]
    · calc (1 + s) ^ N ≤ (2 * s ^ 2) ^ N := pow_le_pow_left₀ (by linarith) (by nlinarith) N
        _ = 2 ^ N * s ^ (2 * N) := by rw [mul_pow, ← pow_mul]
        _ ≤ 2 ^ N * (1 + s ^ (2 * N)) := by
          have : (0 : ℝ) < 2 ^ N := by positivity
          nlinarith
  have he1 : Real.exp (-α * s ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hee : Real.exp (-α * s ^ 2) * Real.exp (α * s ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-α * s ^ 2) * (1 + s) ^ N ≤ Real.exp (-α * s ^ 2) * (2 ^ N * (1 + s ^ (2 * N))) := by gcongr
    _ = 2 ^ N * (Real.exp (-α * s ^ 2) + Real.exp (-α * s ^ 2) * s ^ (2 * N)) := by ring
    _ ≤ 2 ^ N * (1 + Real.exp (-α * s ^ 2) * (N.factorial / α ^ N * Real.exp (α * s ^ 2))) := by gcongr
    _ = 2 ^ N * (1 + N.factorial / α ^ N) := by
      congr 2
      rw [mul_comm, mul_assoc, mul_comm (Real.exp _), hee, mul_one]

variable {n : ℕ} (a : Fin n → ℝ)

/-- **The Gaussian of the majorant** of $Q = \sum_ia_ix_i^2$: $\Phi_a(x) = \exp(-\pi\sum_i|a_i|x_i^2)$ (the standard
archimedean test function of the Siegel–Weil formula; for $Q$ positive definite it is $e^{-\pi Q}$). Parameters: `a`,
`x`. -/
def gaussMaj (x : Fin n → ℝ) : ℝ := Real.exp (-Real.pi * ∑ i, |a i| * x i ^ 2)

theorem gaussMaj_nonneg (x : Fin n → ℝ) : 0 ≤ gaussMaj a x := (Real.exp_pos _).le

theorem continuous_gaussMaj : Continuous (gaussMaj a) := by unfold gaussMaj; fun_prop

theorem sq_norm_le_sum_sq (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have h : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, x i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- **Decay of the Gaussian**: $\Phi_a(x)\le C(1+\|x\|)^{-(n+1)}$ when all $a_i\ne0$. -/
theorem gaussMaj_decay (ha : ∀ i, a i ≠ 0) : ∃ C, ∀ x, gaussMaj a x ≤ C * (1 + ‖x‖) ^ (-(n + 1 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, fun x => ?_⟩
    have hx : ‖x‖ = 0 := by rw [Subsingleton.elim x 0, norm_zero]
    simp [gaussMaj, hx]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set α := Finset.univ.inf' hne fun i => |a i|
  have hα : 0 < α := (Finset.lt_inf'_iff hne).2 fun i _ => abs_pos.2 (ha i)
  refine ⟨2 ^ (n + 1) * (1 + (n + 1).factorial / (Real.pi * α) ^ (n + 1)), fun x => ?_⟩
  have hsum : Real.pi * α * ‖x‖ ^ 2 ≤ Real.pi * ∑ i, |a i| * x i ^ 2 := by
    have : α * ∑ i, x i ^ 2 ≤ ∑ i, |a i| * x i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ i))
        (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left (sq_norm_le_sum_sq x) hα.le
    have h3 := mul_le_mul_of_nonneg_left (h2.trans this) Real.pi_pos.le
    linarith [show Real.pi * α * ‖x‖ ^ 2 = Real.pi * (α * ‖x‖ ^ 2) by ring]
  have hb := exp_neg_mul_sq_mul_pow_le (mul_pos Real.pi_pos hα) (n + 1) (norm_nonneg x)
  have hpos : (0 : ℝ) < (1 + ‖x‖) ^ (n + 1) := by positivity
  rw [Real.rpow_neg (by positivity), show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc gaussMaj a x * (1 + ‖x‖) ^ (n + 1) ≤ Real.exp (-(Real.pi * α) * ‖x‖ ^ 2) * (1 + ‖x‖) ^ (n + 1) := by
        gcongr
        unfold gaussMaj
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ _ := hb

theorem integrable_gaussMaj (ha : ∀ i, a i ≠ 0) : Integrable (gaussMaj a) := by
  obtain ⟨C, hC⟩ := gaussMaj_decay a ha
  refine ((integrable_one_add_norm (E := Fin n → ℝ) (μ := volume) (r := n + 1) (by simp)).const_mul C).mono'
    (continuous_gaussMaj a).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussMaj_nonneg a x)]
  exact hC x

/-- The one-variable factor $\beta_i(b) = \pi|a_i| - 2\pi iba_i$ (real part $\pi|a_i| > 0$). -/
def gβ (b : ℝ) (i : Fin n) : ℂ := Real.pi * |a i| - 2 * Real.pi * I * b * a i

theorem gβ_re (b : ℝ) (i : Fin n) : (gβ a b i).re = Real.pi * |a i| := by simp [gβ]

/-- **The oscillatory Gaussian integral in closed form**:
$\int_{\mathbb R^n}\Phi_a(x)\,e(bQ(x))\,dx = \prod_i(\pi/\beta_i(b))^{1/2}$, $\beta_i(b) = \pi|a_i| - 2\pi iba_i$. -/
theorem integral_gaussMaj_osc (ha : ∀ i, a i ≠ 0) (b : ℝ) :
    ∫ x, (gaussMaj a x : ℂ) * cexp (2 * Real.pi * I * (b * (QuadForm.diag a).eval x)) =
      ∏ i, ((Real.pi : ℂ) / gβ a b i) ^ (1 / 2 : ℂ) := by
  have hpt : ∀ x : Fin n → ℝ, (gaussMaj a x : ℂ) * cexp (2 * Real.pi * I * (b * (QuadForm.diag a).eval x)) =
      ∏ i, cexp (-gβ a b i * (x i : ℂ) ^ 2) := fun x => by
    rw [← Complex.exp_sum, gaussMaj, Complex.ofReal_exp, ← Complex.exp_add, eval_diag_real]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [gβ]
    ring
  simp_rw [hpt]
  rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi fun _ => volume from rfl,
    integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => cexp (-gβ a b i * (t : ℂ) ^ 2))]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact integral_gaussian_complex (by rw [gβ_re]; exact mul_pos Real.pi_pos (abs_pos.2 (ha i)))

theorem norm_gβ_ge (b : ℝ) (i : Fin n) : Real.pi * |a i| * (1 + |b|) / 2 ≤ ‖gβ a b i‖ := by
  have h1 : Real.pi * |a i| ≤ ‖gβ a b i‖ := by
    rw [← gβ_re a b i]; exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h2 : 2 * Real.pi * |b| * |a i| ≤ ‖gβ a b i‖ := by
    have : (gβ a b i).im = -(2 * Real.pi * b * a i) := by simp [gβ]
    have h := Complex.abs_im_le_norm (gβ a b i)
    rw [this, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two] at h
    linarith
  nlinarith [Real.pi_pos, abs_nonneg (a i), abs_nonneg b]

/-- **The bound** $\big|\int\Phi_a(x)e(bQ(x))\,dx\big|\le\prod_i(2/|a_i|)^{1/2}\cdot(1+|b|)^{-n/2}$. -/
theorem norm_gaussMaj_osc_le (ha : ∀ i, a i ≠ 0) (b : ℝ) :
    ‖∫ x, (gaussMaj a x : ℂ) * cexp (2 * Real.pi * I * (b * (QuadForm.diag a).eval x))‖ ≤
      (∏ i, (2 / |a i|) ^ (1 / 2 : ℝ)) * ((1 + |b|) ^ (-(1 / 2 : ℝ))) ^ n := by
  rw [integral_gaussMaj_osc a ha b, norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
  have hai : 0 < |a i| := abs_pos.2 (ha i)
  have hβ : 0 < ‖gβ a b i‖ := lt_of_lt_of_le (by positivity) (norm_gβ_ge a b i)
  have hle : ‖(Real.pi : ℂ) / gβ a b i‖ ≤ 2 / |a i| * (1 + |b|)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_iff₀ hβ]
    have := norm_gβ_ge a b i
    have hb : 0 < 1 + |b| := by positivity
    calc Real.pi = 2 / |a i| * (1 + |b|)⁻¹ * (Real.pi * |a i| * (1 + |b|) / 2) := by field_simp
      _ ≤ 2 / |a i| * (1 + |b|)⁻¹ * ‖gβ a b i‖ := by gcongr
  calc ‖(Real.pi : ℂ) / gβ a b i‖ ^ (1 / 2 : ℝ) ≤ (2 / |a i| * (1 + |b|)⁻¹) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hle (by norm_num)
    _ = (2 / |a i|) ^ (1 / 2 : ℝ) * (1 + |b|) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
          Real.rpow_neg (by positivity)]

/-- **Absolute convergence of the archimedean Whittaker integral for the Gaussian**, $n\ge3$, any signature:
$b\mapsto\int\Phi_a(x)e(bQ(x))\,dx$ is integrable on $\mathbb R$ (it is $O((1+|b|)^{-n/2})$). -/
theorem integrable_gaussMaj_osc (ha : ∀ i, a i ≠ 0) (hn : 3 ≤ n) :
    Integrable fun b : ℝ => ∫ x, (gaussMaj a x : ℂ) * cexp (2 * Real.pi * I * (b * (QuadForm.diag a).eval x)) := by
  have hre : ∀ b i, 0 < (gβ a b i).re := fun b i => by
    rw [gβ_re]; exact mul_pos Real.pi_pos (abs_pos.2 (ha i))
  have hcont : Continuous fun b : ℝ =>
      ∫ x, (gaussMaj a x : ℂ) * cexp (2 * Real.pi * I * (b * (QuadForm.diag a).eval x)) := by
    simp_rw [integral_gaussMaj_osc a ha]
    refine continuous_finsetProd _ fun i _ => ?_
    refine Continuous.cpow (continuous_const.div (by unfold gβ; fun_prop) fun b => ?_) continuous_const
      fun b => ?_
    · intro h; have := hre b i; rw [h] at this; simp at this
    · refine mem_slitPlane_iff.2 (Or.inl ?_)
      rw [Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
      have h0 : gβ a b i ≠ 0 := fun h => by have := hre b i; rw [h] at this; simp at this
      exact div_pos (mul_pos Real.pi_pos (hre b i)) (Complex.normSq_pos.2 h0)
  set K := ∏ i, (2 / |a i|) ^ (1 / 2 : ℝ)
  refine ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)).const_mul K).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun b => ?_)
  refine (norm_gaussMaj_osc_le a ha b).trans ?_
  have hK : 0 ≤ K := Finset.prod_nonneg fun i _ => by positivity
  gcongr
  rw [Real.norm_eq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  refine Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg b]) ?_
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **Whittaker integral = orbital integral for the Gaussian, real place, any signature** ($Q = \sum_ia_ix_i^2$, all
$a_i\ne0$, $n = k+1\ge3$, $m\ne0$): the integral converges absolutely and
$$\int_{\mathbb R}\Big(\int_{\mathbb R^n}\Phi_a(x)\,e(bQ(x))\,dx\Big)e(-mb)\,db = \int_{\{Q = m\}}\Phi_a\,d\sigma_m.$$
With the Siegel–Weil section ($f(wn(b)) = \gamma_Vc_B\int\Phi\psi(bQ)$) this is $W_\infty(m) = \gamma_Vc_B\,\rho_{\Phi_a}(m)$: for
indefinite $Q$ the right side is the archimedean factor of the library's indefinite Siegel formula
(`siegelWeil_indefinite_uncond`). -/
@[kb "weil1965" "Sur la formule de Siegel: archimedean Whittaker integral = integral over {Q = m}, any signature [unverified]"]
theorem whittaker_gaussMaj_eq_orbR {k : ℕ} (a : Fin (k + 1) → ℝ) (ha : ∀ i, a i ≠ 0) (hk : 2 ≤ k) {m : ℝ}
    (hm : m ≠ 0) :
    ∫ b : ℝ, (∫ x, (gaussMaj a x : ℂ) * cexp (2 * Real.pi * I * (b * (QuadForm.diag a).eval x))) *
        cexp (2 * Real.pi * I * (-(m * b))) =
      orbR (QuadForm.diag a) (gaussMaj a) m := by
  obtain ⟨C, hC⟩ := gaussMaj_decay a ha
  exact integral_whittaker_eq_orbR (by omega) (volume_diag_eval_eq_zero (ha 0))
    (continuous_gaussMaj a).measurable (gaussMaj_nonneg a) (integrable_gaussMaj a ha)
    (integrable_gaussMaj_osc a ha (by omega)) (continuousAt_orbR (by omega) (continuous_gaussMaj a)
      (gaussMaj_nonneg a) hC hm)

end Gauss

end QuadFormsKB.SiegelWeil.Orbital
