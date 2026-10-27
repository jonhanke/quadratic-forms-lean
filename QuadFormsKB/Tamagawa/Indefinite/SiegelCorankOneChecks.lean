/-
# Corank one: the measure form, consistency with the shape of `siegelIndefiniteForms_uncond`

**Layer:** number fields. Setting of `SiegelCorankOne.lean` ($Q_0$ in $N = r + 1$ variables, $T_0$ of rank $r$, a rational
frame $\Xi$). The headline `siegelIndefiniteForms_corank1_uncond` counts classes of representations. Here it is restated
in the **measure form** of `siegelIndefiniteForms_uncond` ($n'\ge3$): with the archimedean constant
$c_\infty(T_0) = c_F(N)\prod_{w\mid\infty}|\det H_{T_0}|_w^{-n'}$ (`cInfTNF`, $n' = 1$) and Siegel's measure on the one-point
stabilizers of mass
$$m = \prod_{w\mid\infty}\frac{|\det H_{T_0}|_w}{|\det H_{Q_0}|_w}\qquad(\texttt{stabMassCorankOne}),$$
the formula reads $c_\infty(T_0)\sum_i\rho(M_i,T_0) = \frac12\,|d_F|^{-N(N-1)/4}\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\sum_iv(M_i)$: the
shape of `siegelIndefiniteForms_uncond` times Siegel's $\varepsilon = \frac12$. ($m$ is the $n' = 1$ value of the normalization
there, $\prod_w|\det g|_w^{n'+1}$ times the Leray mass $\prod_w|2c''|_w^{-1}$ of $SO(\langle c''\rangle)(F_\infty)$, by
$\det(g)^2\det H_{Q_0} = \det H_{T_0}\cdot2c''$.)

**Proves:** `archFibCorankOne` (the fibration), `repMeasureT_archFibCorankOne` ($\rho = m\cdot n$),
`cInfTNF_mul_stabMass` ($c_\infty(T_0)\,m = c^{(1)}_\infty(Q_0)$), **`siegelIndefiniteForms_corank1_measure`**.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

open Classical in
/-- **The mass of Siegel's measure on the one-point stabilizer** of a representation (corank one):
$m = \prod_{w\ \mathrm{real}}|\sigma_w\det H_{T_0}|/|\sigma_w\det H_{Q_0}|\cdot\prod_{w\ \mathrm{complex}}|\sigma_w\det H_{T_0}|^2/
|\sigma_w\det H_{Q_0}|^2$. Parameters: `Q₀`, `T₀`. -/
def stabMassCorankOne {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (algebraMap (𝓞 F) F T₀.hessian.det)| * |σR w (algebraMap (𝓞 F) F Q₀.hessian.det)|⁻¹) *
    ∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 * (‖σC w (algebraMap (𝓞 F) F Q₀.hessian.det)‖ ^ 2)⁻¹)

variable (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (Ξ : RatFrame Q₀ T₀)

open Classical in
include hQ hT in
theorem stabMassCorankOne_pos : 0 < ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (algebraMap (𝓞 F) F T₀.hessian.det)| * |σR w (algebraMap (𝓞 F) F Q₀.hessian.det)|⁻¹) *
    ∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 * (‖σC w (algebraMap (𝓞 F) F Q₀.hessian.det)‖ ^ 2)⁻¹) := by
  have ht := algebraMap_det_ne_zero T₀ hT
  have hq := algebraMap_det_ne_zero Q₀ hQ
  refine mul_pos (Finset.prod_pos fun w _ => mul_pos ?_ ?_) (Finset.prod_pos fun w _ => mul_pos ?_ ?_)
  · exact abs_pos.2 ((map_ne_zero _).2 ht)
  · exact inv_pos.2 (abs_pos.2 ((map_ne_zero _).2 hq))
  · exact pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 ht)) _
  · exact inv_pos.2 (pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hq)) _)

open Classical in
include hQ hT in
/-- $c_\infty(T_0)\cdot m = c^{(1)}_\infty(Q_0)$: the constant of the measure form times the stabilizer mass is the constant
of the count form. -/
theorem cInfTNF_mul_stabMass : cInfTNF (n' := 1) Q₀ T₀ * stabMassCorankOne Q₀ T₀ = cInfCorankOne Q₀ := by
  set t := algebraMap (𝓞 F) F T₀.hessian.det
  set q := algebraMap (𝓞 F) F Q₀.hessian.det
  have ht : t ≠ 0 := algebraMap_det_ne_zero T₀ hT
  rw [cInfCorankOne_eq, cInfTNF, stabMassCorankOne]
  have h1 : ∀ w : {w : InfinitePlace F // w.IsReal}, 0 ≤ (|σR w t| ^ 1)⁻¹ := fun w => by positivity
  have h2 : ∀ w : {w : InfinitePlace F // w.IsComplex}, 0 ≤ (‖σC w t‖ ^ (2 * 1))⁻¹ := fun w => by positivity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => h1 w), ← ENNReal.ofReal_prod_of_nonneg (fun w _ => h2 w),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => h1 w),
    ← ENNReal.ofReal_mul (cF_pos' (F := F) _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (cF_pos' (F := F) _).le
      (mul_nonneg (Finset.prod_nonneg fun w _ => h1 w) (Finset.prod_nonneg fun w _ => h2 w)))]
  congr 1
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal}, |σR w t| ≠ 0 := fun w => abs_ne_zero.2 ((map_ne_zero _).2 ht)
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w t‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 ((map_ne_zero _).2 ht)
  rw [mul_assoc]
  congr 1
  have eR : (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w t| ^ 1)⁻¹) *
      ∏ w : {w : InfinitePlace F // w.IsReal}, |σR w t| = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun w _ => by rw [pow_one, inv_mul_cancel₀ (hR w)]
  have eC : (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w t‖ ^ (2 * 1))⁻¹) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w t‖ ^ 2 = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun w _ => by rw [mul_one, inv_mul_cancel₀ (pow_ne_zero _ (hC w))]
  rw [Finset.prod_mul_distrib (f := fun w => |σR w t|) (g := fun w => |σR w q|⁻¹),
    Finset.prod_mul_distrib (f := fun w => ‖σC w t‖ ^ 2) (g := fun w => (‖σC w q‖ ^ 2)⁻¹)]
  calc (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w t| ^ 1)⁻¹) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w t‖ ^ (2 * 1))⁻¹) *
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w t|) * (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w q|⁻¹) *
        ((∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w t‖ ^ 2) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w q‖ ^ 2)⁻¹))
      = ((∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w t| ^ 1)⁻¹) *
          ∏ w : {w : InfinitePlace F // w.IsReal}, |σR w t|) *
        ((∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w t‖ ^ (2 * 1))⁻¹) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w t‖ ^ 2) *
        ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w q|⁻¹) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w q‖ ^ 2)⁻¹) := by ring
    _ = _ := by rw [eR, eC, one_mul, one_mul]

include hQ in
theorem cInfCorankOne_ne_zero : cInfCorankOne Q₀ ≠ 0 := by
  have hq := algebraMap_det_ne_zero Q₀ hQ
  rw [cInfCorankOne_eq]
  refine (ENNReal.ofReal_pos.2 (mul_pos (cF_pos' (F := F) _) (mul_pos (Finset.prod_pos fun w _ => ?_)
    (Finset.prod_pos fun w _ => ?_)))).ne'
  · exact inv_pos.2 (abs_pos.2 ((map_ne_zero _).2 hq))
  · exact inv_pos.2 (pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hq)) _)

theorem cInfCorankOne_ne_top : cInfCorankOne Q₀ ≠ ⊤ := by
  rw [cInfCorankOne_eq]; exact ENNReal.ofReal_ne_top

/-- **The archimedean fibration of corank one in Siegel's normalization**: constant $c_\infty(T_0)$ (`cInfTNF`),
stabilizer measures $m\,\delta_1$ ($m$ = `stabMassCorankOne`), measure $(c_\infty(T_0)\,m)^{-1}\mu_\infty$ on
$T = SO(V)(F_\infty)$, $\tau(x) = x^{-1}\Xi_\infty$. -/
def archFibCorankOne :
    ArchFibration (muArchTamSO Q₀ hQ) (orbInf Q₀ T₀ Ξ)
      ((cInfTNF (n' := 1) Q₀ T₀ * stabMassCorankOne Q₀ T₀)⁻¹ • muArchTamSO Q₀ hQ)
      (fun x : GInfSO Q₀ => x⁻¹ • ratAT Q₀ T₀ Ξ) (cInfTNF (n' := 1) Q₀ T₀) :=
  (archFibTriv Q₀ hQ T₀ hT Ξ).rescale (stabMassCorankOne Q₀ T₀)
    (cInfTNF (n' := 1) Q₀ T₀ * stabMassCorankOne Q₀ T₀)⁻¹ (cInfTNF (n' := 1) Q₀ T₀) ENNReal.ofReal_ne_top (by
      calc cInfTNF (n' := 1) Q₀ T₀ * (cInfTNF (n' := 1) Q₀ T₀ * stabMassCorankOne Q₀ T₀)⁻¹ *
            stabMassCorankOne Q₀ T₀
          = (cInfTNF (n' := 1) Q₀ T₀ * stabMassCorankOne Q₀ T₀) *
            (cInfTNF (n' := 1) Q₀ T₀ * stabMassCorankOne Q₀ T₀)⁻¹ := by ring
        _ = 1 := by
          rw [cInfTNF_mul_stabMass Q₀ hQ T₀ hT]
          exact ENNReal.mul_inv_cancel (cInfCorankOne_ne_zero Q₀ hQ) (cInfCorankOne_ne_top Q₀))

/-- **With Siegel's stabilizer measures, the measure of representations is $m$ times the count.** -/
theorem repMeasureT_archFibCorankOne (i : DC Q₀) :
    repMeasureT Q₀ T₀ hQ (archFibCorankOne Q₀ hQ T₀ hT Ξ) i = stabMassCorankOne Q₀ T₀ * repCount Q₀ T₀ i := by
  have := countable_GammaSOAdele Q₀
  have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  rw [← repMeasureT_archFibTriv Q₀ hQ T₀ hT Ξ i]
  exact repMeasureOf_smul _ _ _ (archFibTriv Q₀ hQ T₀ hT Ξ).leftInv _
    (ENNReal.ofReal_pos.2 (stabMassCorankOne_pos Q₀ hQ T₀ hT)).ne'

/-- **Siegel's formula for frames of corank one in the measure form** (the shape of `siegelIndefiniteForms_uncond`,
times Siegel's $\varepsilon = \frac12$): for $N = r + 1\ge3$,
$$c_\infty(T_0)\sum_i\rho(M_i,T_0) = \frac12\,|d_F|^{-N(N-1)/4}\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i),$$
$c_\infty(T_0) = c_F(N)\prod_w|\det H_{T_0}|_w^{-1}$ (`cInfTNF`), $\rho$ = `repMeasureT` for `archFibCorankOne` (stabilizer mass
$m = \prod_w|\det H_{T_0}|_w/|\det H_{Q_0}|_w$). Unconditional (from `siegelIndefiniteForms_corank1_uncond`). -/
theorem siegelIndefiniteForms_corank1_measure (hr : 2 ≤ r) :
    cInfTNF (n' := 1) Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (archFibCorankOne Q₀ hQ T₀ hT Ξ) i =
      2⁻¹ * ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i := by
  simp_rw [repMeasureT_archFibCorankOne Q₀ hQ T₀ hT Ξ]
  rw [ENNReal.tsum_mul_left, ← mul_assoc, cInfTNF_mul_stabMass Q₀ hQ T₀ hT]
  exact siegelIndefiniteForms_corank1_uncond Q₀ hQ T₀ hT Ξ hr

end QuadFormsKB.Tamagawa.Indefinite
