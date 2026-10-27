/-
# Siegel's formula for representations of forms by indefinite forms over every number field

**Layer:** number fields. $F$ **any** number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $N = r + n'$
variables of any signature, $L = \mathcal O_F^N$, $T_0$ a nondegenerate form over $\mathcal O_F$ of rank $r\ge1$ represented over
$F$ (a rational frame $\Xi$, $Q_0\circ\Xi = T_0$), $n' = N - r\ge3$. This removes `[IsTotallyReal F]` from
`siegelIndefiniteForms_totallyReal`: the adelic frame fibration, Weil's form `siegelFormsWeil` and the local densities
`frameOrbitSum_eq` hold over every number field; only the archimedean constants and the product formula change.

Write $|x|_w$ for the normalized absolute value at an archimedean place $w$: $|\sigma_wx|$ at a real place, $|\sigma_wx|^2$ at a
complex place.

**Headline** (`siegelIndefiniteForms_uncond`, unconditional):
$$c_\infty(T_0)\sum_i\rho(M_i, T_0) = |d_F|^{-(N(N-1) - n'(n'-1))/4}\prod_\mathfrak p\beta_\mathfrak p(L, T_0)\cdot\sum_iv(M_i),$$
* $c_\infty(T_0) = c_F(N)\prod_{w\mid\infty}|\det H_{T_0}|_w^{-n'}$ (`cInfTNF`);
* $\rho(M_i, T_0)$ = `repMeasureT` for `frameArchFibrationNF`: the measure on the stabilizer $H_\Xi\cong SO(Q'')(F_\infty)$ is
  $\prod_{w\mid\infty}|\det g|_w^{\,n'+1}$ times Weil's measure of $SO(Q'')(F_\infty)$ (the Leray measure, with
  $|dz\wedge d\bar z| = 2\,dx\,dy$ at the complex places, `cxWeil`) transported by $h\mapsto g\,\mathrm{diag}(1_r,h)\,g^{-1}$,
  $g = [\Xi\mid C]$ the adapted frame of the chosen frame coordinates; at $a\Xi$ conjugated by $a$;
* $\beta_\mathfrak p$ = `NF.localDensityForm v Q₀ T₀`, the right side `frameDensityProduct` (unchanged).

**Consistency** (`cInfTNF_eq_cInfT`, `frameLamNF_eq_frameLam`, `repMeasureT_frameArchFibrationNF_eq`): for totally real $F$
the constants and the representation measures are those of `siegelIndefiniteForms_totallyReal`.
-/
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefinite

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

open Classical in
/-- **The archimedean constant over every number field**
$c_\infty(T_0) = c_F(N)\prod_{w\ \mathrm{real}}|\sigma_w\det H_{T_0}|^{-n'}\prod_{w\ \mathrm{complex}}|\sigma_w\det H_{T_0}|^{-2n'}$
($N = r + n'$), i.e. $c_F(N)\prod_{w\mid\infty}|\det H_{T_0}|_w^{-n'}$ with normalized absolute values. -/
def cInfTNF (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r) : ℝ≥0∞ :=
  ENNReal.ofReal (cF F (r + n')) *
    ((∏ w : {w : InfinitePlace F // w.IsReal}, ENNReal.ofReal ((|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹)) *
      ∏ w : {w : InfinitePlace F // w.IsComplex},
        ENNReal.ofReal ((‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * n'))⁻¹))

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (hn' : 3 ≤ n') (Ξ : RatFrame Q₀ T₀)

open Classical in
/-- The scale of the stabilizer measures over every number field:
$\lambda = \prod_{w\mid\infty}|\det g|_w^{n'+1}/c_F(n')$ (normalized absolute values). -/
def frameLamNF : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (towerAdapted Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT).g.val.det| ^ (n' + 1)) *
    (∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖σC w (towerAdapted Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT).g.val.det‖ ^ (2 * (n' + 1))) / cF F n')

open Classical in
theorem cInfTNF_ne_zero_top (h : T₀.Nondegenerate) : cInfTNF Q₀ T₀ ≠ 0 ∧ cInfTNF Q₀ T₀ ≠ ⊤ := by
  have hd := algebraMap_det_ne_zero T₀ h
  refine ⟨mul_ne_zero (ENNReal.ofReal_pos.2 (cF_pos' _)).ne' (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => ?_)
      (Finset.prod_ne_zero_iff.2 fun w _ => ?_)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
      (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top))⟩
  · exact (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (abs_pos.2 ((map_ne_zero _).2 hd)) _))).ne'
  · exact (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hd)) _))).ne'

open Classical in
theorem frameLamNF_ne_zero_top : frameLamNF Q₀ hQ T₀ hT hn' Ξ ≠ 0 ∧ frameLamNF Q₀ hQ T₀ hT hn' Ξ ≠ ⊤ := by
  have hg := det_towerAdapted_ne_zero Q₀ hQ T₀ hT hn' Ξ
  refine ⟨(ENNReal.ofReal_pos.2 (div_pos (mul_pos (Finset.prod_pos fun w _ => pow_pos (abs_pos.2
    ((map_ne_zero _).2 hg)) _) (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hg)) _))
    (cF_pos' _))).ne', ENNReal.ofReal_ne_top⟩

/-- **The archimedean fibration of frames over every number field**, Siegel's normalization: constant $c_\infty(T_0)$
(`cInfTNF`), stabilizer measures $\lambda\,\mu^{\mathrm{Tam}}_H$ ($\lambda$ = `frameLamNF`; $=\prod_{w\mid\infty}|\det g|_w^{n'+1}$ times
Weil's measure of $SO(Q'')(F_\infty)$, transported), measure $(c_\infty(T_0)\lambda)^{-1}\sigma_A$ on the orbit of $\Xi_\infty$. -/
def frameArchFibrationNF :
    ArchFibration (muArchTamSO Q₀ hQ) (Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ)
      ((cInfTNF Q₀ T₀ * frameLamNF Q₀ hQ T₀ hT hn' Ξ)⁻¹ • frameσA Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ))
      Subtype.val (cInfTNF Q₀ T₀) :=
  (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)).rescale (frameLamNF Q₀ hQ T₀ hT hn' Ξ)
    (cInfTNF Q₀ T₀ * frameLamNF Q₀ hQ T₀ hT hn' Ξ)⁻¹ (cInfTNF Q₀ T₀) ENNReal.ofReal_ne_top (by
      have h0 := (cInfTNF_ne_zero_top Q₀ T₀ hT).1
      have ht := (cInfTNF_ne_zero_top Q₀ T₀ hT).2
      have h1 := (frameLamNF_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).1
      have h2 := (frameLamNF_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).2
      calc cInfTNF Q₀ T₀ * (cInfTNF Q₀ T₀ * frameLamNF Q₀ hQ T₀ hT hn' Ξ)⁻¹ * frameLamNF Q₀ hQ T₀ hT hn' Ξ
          = (cInfTNF Q₀ T₀ * frameLamNF Q₀ hQ T₀ hT hn' Ξ) * (cInfTNF Q₀ T₀ * frameLamNF Q₀ hQ T₀ hT hn' Ξ)⁻¹ := by
            ring
        _ = 1 := ENNReal.mul_inv_cancel (mul_ne_zero h0 h1) (ENNReal.mul_ne_top ht h2))

open Classical in
/-- The identity in $\mathbb R$ behind the headline over every number field: the product formula for $\det g$ and
$\det H_{T_0}$ at all places. -/
theorem frameDensity_identityNF (D : FrameTower Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate) (hn' : 3 ≤ n') :
    cF F (r + n') * ((∏ w : {w : InfinitePlace F // w.IsReal},
        (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * n'))⁻¹) *
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det| ^ (n' + 1)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det‖ ^ (2 * (n' + 1))) /
        cF F n') * ∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v = frameDensityProduct Q₀ T₀ := by
  set g := (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det with hgdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  have hg : g ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have ha : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v g‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hg)
  have hb : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v h‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
  have hfa := mulSupport_finite_norm (F := F) hg
  have hfb := mulSupport_finite_norm (F := F) hh
  have hpow : ∀ (f : HeightOneSpectrum (𝓞 F) → ℝ) (k : ℕ), (Function.mulSupport f).Finite →
      (Function.mulSupport fun v => f v ^ k).Finite := fun f k hf => hf.subset fun v hv => by
    intro h1
    apply hv
    show f v ^ k = 1
    rw [show f v = 1 from h1, one_pow]
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v h‖ ^ n' * (‖σV v g‖ ^ (n' + 1))⁻¹ with hu
  have hpa := hpow _ (n' + 1) hfa
  have hpb := hpow _ n' hfb
  have hpai : (Function.mulSupport fun v => (‖σV v g‖ ^ (n' + 1))⁻¹).Finite := by
    refine hpa.subset fun v hv => ?_
    intro h1
    apply hv
    show (‖σV v g‖ ^ (n' + 1))⁻¹ = 1
    rw [show ‖σV v g‖ ^ (n' + 1) = 1 from h1, inv_one]
  have hufin : (Function.mulSupport u).Finite := by
    refine (hpb.union hpai).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show u v = 1
    simp only [hu, hcon.1, hcon.2, one_mul]
  have hUval : ∏' v, u v = (∏' v, ‖σV v h‖) ^ n' * ((∏' v, ‖σV v g‖) ^ (n' + 1))⁻¹ := by
    rw [tprod_eq_finprod hufin, tprod_eq_finprod hfa, tprod_eq_finprod hfb, finprod_mul_distrib hpb hpai,
      finprod_inv_distrib, finprod_pow hfb, finprod_pow hfa]
  have hβ : ∀ v, NF.localDensityForm v Q₀ T₀ = frameLocFactor Q₀ hQ T₀ Ξ D hT v * u v := fun v => by
    have := ha v
    have := hb v
    simp only [frameLocFactor, hu]
    rw [← hgdef, ← hhdef]
    field_simp
  have hprod : ∏' v, NF.localDensityForm v Q₀ T₀ = (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v) * ∏' v, u v := by
    rw [tprod_congr hβ]
    exact (multipliable_frameLocFactor Q₀ hQ T₀ Ξ D hT hn').tprod_mul (multipliable_of_hasFiniteMulSupport hufin)
  have hPg := prod_places_mul_tprod (F := F) hg
  have hPh := prod_places_mul_tprod (F := F) hh
  set Gs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w g|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w g‖ ^ 2 with hGs
  set Hs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w h|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w h‖ ^ 2 with hHs
  have hGne : Gs ≠ 0 := left_ne_zero_of_mul_eq_one hPg
  have hHne : Hs ≠ 0 := left_ne_zero_of_mul_eq_one hPh
  have hA : ∏' v, ‖σV v g‖ = Gs⁻¹ := eq_inv_of_mul_eq_one_right hPg
  have hB : ∏' v, ‖σV v h‖ = Hs⁻¹ := eq_inv_of_mul_eq_one_right hPh
  have h1 : (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w h| ^ n')⁻¹) *
      (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w h‖ ^ (2 * n'))⁻¹) = (Hs ^ n')⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow, ← mul_inv, hHs, mul_pow,
      ← Finset.prod_pow, ← Finset.prod_pow]
    simp_rw [← pow_mul]
  have h2 : (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w g| ^ (n' + 1)) *
      (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w g‖ ^ (2 * (n' + 1))) = Gs ^ (n' + 1) := by
    rw [hGs, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    simp_rw [← pow_mul]
  have hcd : cF F (r + n') / cF F n' =
      |(discr F : ℝ)| ^ (-(((r + n' : ℕ) : ℝ) * ((r + n' : ℕ) - 1) - (n' : ℝ) * (n' - 1)) / 4) := by
    unfold cF
    rw [← Real.rpow_sub (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F))]
    congr 1
    ring
  have hcn : cF F n' ≠ 0 := (cF_pos' _).ne'
  rw [frameDensityProduct, hprod, hUval, hA, hB, h1, h2, ← hcd]
  simp only [inv_pow, inv_inv]
  field_simp

/-- **Siegel's formula for representations of forms by indefinite forms over every number field — unconditional**
(Siegel 1936, Hauptsatz for indefinite forms, measure form; Weil 1965; for forms by forms Siegel 1935): for $F$ a number
field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + n'$ variables of any signature, $T_0$ nondegenerate of rank
$r\ge1$ with a rational frame $\Xi$ ($Q_0\circ\Xi = T_0$), $n' = N - r\ge3$,
$$c_\infty(T_0)\sum_i\rho(M_i, T_0) = |d_F|^{-(N(N-1)-n'(n'-1))/4}\prod_\mathfrak p\beta_\mathfrak p(L, T_0)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^N$, $c_\infty(T_0) = c_F(N)\prod_{w\mid\infty}|\det
H_{T_0}|_w^{-n'}$ (`cInfTNF`, normalized absolute values), $\rho$ the measures of the representations of $T_0$ (`repMeasureT`
for `frameArchFibrationNF`), $v$ the unit volumes. No hypotheses beyond these. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; forms by forms; every number field) [unverified]"]
theorem siegelIndefiniteForms_uncond (hr : 1 ≤ r) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationNF Q₀ hQ T₀ hT hn' Ξ) i =
      ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i := by
  classical
  have hN : 3 ≤ r + n' := by omega
  have hτ : TamagawaNumberTwoAdelic Q₀ hQ := tauTwoAll_release_uncond (r + n') hN Q₀ hQ
  have hτ' : TamagawaNumberTwoAdelic (chosenTower Q₀ hQ T₀ hT hn' Ξ).Q'' (chosenTower Q₀ hQ T₀ hT hn' Ξ).hQ'' :=
    tauTwoAll_release_uncond n' hn' _ _
  have hW := siegelFormsWeil Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT hn' hτ hτ'
  have := countable_GammaSOAdele Q₀
  have hscale : ∀ i, repMeasureT Q₀ T₀ hQ (frameArchFibrationNF Q₀ hQ T₀ hT hn' Ξ) i =
      frameLamNF Q₀ hQ T₀ hT hn' Ξ *
        repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)) i :=
    fun i => by
      have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
      exact repMeasureOf_smul _ _ _ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)).leftInv _
        (frameLamNF_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).1
  simp_rw [hscale]
  rw [ENNReal.tsum_mul_left, hW, frameOrbitSum_eq Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT hn']
  have key : cInfTNF Q₀ T₀ * frameLamNF Q₀ hQ T₀ hT hn' Ξ *
      ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT v) =
      ENNReal.ofReal (frameDensityProduct Q₀ T₀) := by
    rw [← frameDensity_identityNF Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT hn']
    unfold cInfTNF frameLamNF
    have hnn : ∀ w : {w : InfinitePlace F // w.IsReal},
        0 ≤ (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹ := fun w => by positivity
    have hnnC : ∀ w : {w : InfinitePlace F // w.IsComplex},
        0 ≤ (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * n'))⁻¹ := fun w => by positivity
    have hnn2 : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹) :=
      Finset.prod_nonneg fun w _ => hnn w
    have hnn2C : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsComplex},
        (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * n'))⁻¹) := Finset.prod_nonneg fun w _ => hnnC w
    have hnn3 := mul_nonneg (cF_pos' (F := F) (r + n')).le (mul_nonneg hnn2 hnn2C)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => hnn w), ← ENNReal.ofReal_prod_of_nonneg (fun w _ => hnnC w),
      ← ENNReal.ofReal_mul hnn2, ← ENNReal.ofReal_mul (cF_pos' _).le,
      ← ENNReal.ofReal_mul hnn3, ← ENNReal.ofReal_mul (mul_nonneg hnn3 (div_nonneg
        (mul_nonneg (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity))
        (cF_pos' _).le))]
  calc cInfTNF Q₀ T₀ * (frameLamNF Q₀ hQ T₀ hT hn' Ξ *
        (ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT v) *
          ∑' i, unitVolume Q₀ hQ i))
      = (cInfTNF Q₀ T₀ * frameLamNF Q₀ hQ T₀ hT hn' Ξ *
          ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT v)) *
          ∑' i, unitVolume Q₀ hQ i := by ring
    _ = _ := by rw [key]

/-! ### Consistency with the totally real headline -/

open Classical in
/-- For totally real $F$, `cInfTNF` is the constant `cInfT` of `siegelIndefiniteForms_totallyReal`. -/
theorem cInfTNF_eq_cInfT [IsTotallyReal F] : cInfTNF Q₀ T₀ = cInfT Q₀ T₀ := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩
  rw [cInfTNF, cInfT, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty, mul_one]

open Classical in
/-- For totally real $F$, `frameLamNF` is the scale `frameLam` of `siegelIndefiniteForms_totallyReal`. -/
theorem frameLamNF_eq_frameLam [IsTotallyReal F] : frameLamNF Q₀ hQ T₀ hT hn' Ξ = frameLam Q₀ hQ T₀ hT hn' Ξ := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩
  rw [frameLamNF, frameLam, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty,
    mul_one]

/-- **Consistency with the totally real headline**: for totally real $F$ the measures of representations of
`siegelIndefiniteForms_uncond` are those of `siegelIndefiniteForms_totallyReal` (and the constants agree,
`cInfTNF_eq_cInfT`), so the new headline specializes to the old one. -/
theorem repMeasureT_frameArchFibrationNF_eq [IsTotallyReal F] (i : DC Q₀) :
    repMeasureT Q₀ T₀ hQ (frameArchFibrationNF Q₀ hQ T₀ hT hn' Ξ) i =
      repMeasureT Q₀ T₀ hQ (frameArchFibration Q₀ hQ T₀ hT hn' Ξ) i := by
  have := countable_GammaSOAdele Q₀
  have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  have h1 : repMeasureT Q₀ T₀ hQ (frameArchFibrationNF Q₀ hQ T₀ hT hn' Ξ) i =
      frameLamNF Q₀ hQ T₀ hT hn' Ξ *
        repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)) i :=
    repMeasureOf_smul _ _ _ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)).leftInv _
      (frameLamNF_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).1
  have h2 : repMeasureT Q₀ T₀ hQ (frameArchFibration Q₀ hQ T₀ hT hn' Ξ) i =
      frameLam Q₀ hQ T₀ hT hn' Ξ *
        repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)) i :=
    repMeasureOf_smul _ _ _ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)).leftInv _
      (frameLam_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).1
  rw [h1, h2, frameLamNF_eq_frameLam]

end QuadFormsKB.Tamagawa.Indefinite
