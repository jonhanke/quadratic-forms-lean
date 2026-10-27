/-
# Siegel's formula for representations of forms by indefinite forms, measure form, totally real F

**Layer:** number fields. $F$ a totally real number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in
$N = r + n'$ variables of **any signature**, $L = \mathcal O_F^N$, $T_0$ a nondegenerate form over $\mathcal O_F$ of rank $r\ge1$
represented over $F$ (a rational frame $\Xi$, $Q_0\circ\Xi = T_0$), $n' = N - r\ge3$. The proper classes $M_i$ in the genus of
$L$ (`DC Q₀`), their unit groups $\Gamma_i = SO(M_i)$ and unit volumes $v(M_i)$ (`unitVolume`) are those of the case $r = 1$.

**Headline** (`siegelIndefiniteForms_totallyReal`, unconditional):
$$c_\infty(T_0)\sum_i\rho(M_i, T_0) = |d_F|^{-(N(N-1) - n'(n'-1))/4}\prod_\mathfrak p\beta_\mathfrak p(L, T_0)\cdot\sum_iv(M_i),$$
* $\rho(M_i, T_0) = \sum_{X\in\Gamma_i\backslash R(M_i, T_0)}\operatorname{vol}(\Gamma_{i,X}\backslash H_X)$ (`repMeasureT`), $R(M_i,T_0)$ the
  representations $X\in M_i^r$, $Q\circ X = T_0$, $H_X$ the stabilizer of $X$ in $SO(V)(F_\infty)$;
* the measures on the stabilizers are those of `frameArchFibration`: at $\Xi$, $\prod_w|\det g|_w^{\,n'+1}$ times the Leray
  (gauge) measure of $SO(Q'')(F_\infty)$ transported by $h\mapsto g\,\mathrm{diag}(1_r,h)\,g^{-1}$, $g = [\Xi\mid C]$ the adapted
  frame of the chosen frame coordinates ($Q_0\circ g = T_0\perp Q''$); at $a\Xi$ conjugated by $a$;
* $c_\infty(T_0) = c_F(N)\prod_w|\det H_{T_0}|_w^{-n'}$ (`cInfT`), $\beta_\mathfrak p$ = `NF.localDensityForm v Q₀ T₀` (Siegel's
  $\varepsilon = 1$, $n'\ge3$), the right side `frameDensityProduct`.

For $r = 1$ ($T_0 = \langle m\rangle$, $H_T = (2m)$) this has the shape of `siegelIndefinite_release_totallyReal_uncond`:
$c_\infty(\langle m\rangle)$ = `cInf m` and $\prod_\mathfrak p\beta_\mathfrak p(L,\langle m\rangle)$ = `finDensityProduct` (`cInfT_unary`,
`frameDensityProduct_unary`).

**Proof.** Weil's form `siegelFormsWeil` ($\sum_i\rho^{\mathrm{Tam}} = \texttt{frameOrbitSum}\cdot\sum_iv$, from the adelic frame
fibration and $\tau(SO(V)) = \tau(SO(Q'')) = 2$, `tauTwoAll_release_totallyReal_uncond`), the local densities
`frameOrbitSum_eq`, the rescaling of the stabilizer measures and the product formula for $\det g$ and $\det H_{T_0}$.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameDensities
import QuadFormsKB.Tamagawa.Indefinite.FrameTowerFrame
import QuadFormsKB.Tamagawa.Measure.Weil.ReleaseHeadlines

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

/-! ### Rescaling an archimedean fibration -/

section Rescale

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] {μA : Measure A}
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T] {P : Set Y} {σ : Measure T} {τ : T → Y} {c : ℝ≥0∞}

/-- **Rescaling the stabilizer measures** of an archimedean fibration by $\lambda$ and its measure by $\kappa$, with constant
$c'$, when $c'\kappa\lambda = c$. -/
def ArchFibration.rescale (𝔉 : ArchFibration μA P σ τ c) (lam κ c' : ℝ≥0∞) (hlam : lam ≠ ⊤) (hc : c' * κ * lam = c) :
    ArchFibration μA P (κ • σ) τ c' where
  μH y := lam • 𝔉.μH y
  coord := 𝔉.coord
  sigmaFinite y := by
    have := 𝔉.sigmaFinite y
    exact sigmaFinite_smul (𝔉.μH y) hlam
  leftInv y := by
    have := measurableMul_subgroup (stabilizer A y)
    have := 𝔉.leftInv y
    infer_instance
  fib y hy := by
    have h := 𝔉.fib y hy
    have := 𝔉.sigmaFinite y
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul, smul_smul,
      hc]
    · exact h
    all_goals exact (𝔉.coord y hy).coord.measurable.aemeasurable

theorem repMeasureOf_smul (Γ' : Subgroup A) [Countable Γ'] (S : SubMulAction Γ' Y)
    (μH : (y : Y) → Measure (stabilizer A y)) (hinv : ∀ y, (μH y).IsMulLeftInvariant)
    (lam : ℝ≥0∞) (hlam : lam ≠ 0) : repMeasureOf Γ' S (fun y => lam • μH y) = lam * repMeasureOf Γ' S μH := by
  unfold repMeasureOf
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun q => ?_
  have := hinv ((q.out : S) : Y)
  have := measurableMul_subgroup (stabilizer A ((q.out : S) : Y))
  have : Countable (stabArith Γ' ((q.out : S) : Y)) :=
    Function.Injective.countable (f := fun g : stabArith Γ' ((q.out : S) : Y) => (⟨g.1.1, g.2⟩ : Γ'))
      fun a b h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  exact covolume_smul _ _ hlam

end Rescale

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

open Classical in
/-- **The archimedean constant** $c_\infty(T_0) = c_F(N)\prod_w|\det H_{T_0}|_w^{-n'}$ ($N = r + n'$, real places). -/
def cInfT (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r) : ℝ≥0∞ :=
  ENNReal.ofReal (cF F (r + n')) *
    ∏ w : {w : InfinitePlace F // w.IsReal}, ENNReal.ofReal ((|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹)

/-- **The local side**: $|d_F|^{-(N(N-1)-n'(n'-1))/4}\prod_\mathfrak p\beta_\mathfrak p(L, T_0)$. -/
@[kb "siegel1935" "Über die analytische Theorie der quadratischen Formen; local densities of forms [unverified]"]
def frameDensityProduct (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  |(discr F : ℝ)| ^ (-(((r + n' : ℕ) : ℝ) * ((r + n' : ℕ) - 1) - (n' : ℝ) * (n' - 1)) / 4) *
    ∏' v : HeightOneSpectrum (𝓞 F), NF.localDensityForm v Q₀ T₀

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (hn' : 3 ≤ n') (Ξ : RatFrame Q₀ T₀)

/-- The chosen frame coordinates of $\Xi$. -/
def chosenTower : FrameTower Q₀ hQ n' (cols Ξ.1) :=
  Classical.choice (nonempty_frameTower_ratFrame hn' Q₀ hQ T₀ hT Ξ)

open Classical in
/-- The scale of the stabilizer measures: $\lambda = \prod_w|\det g|_w^{n'+1}/c_F(n')$. -/
def frameLam : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (towerAdapted Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT).g.val.det| ^ (n' + 1)) / cF F n')

theorem cF_pos' (m : ℕ) : 0 < cF F m :=
  Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)) _

theorem algebraMap_det_ne_zero {m : ℕ} (T : QuadForm (𝓞 F) m) (h : T.Nondegenerate) :
    algebraMap (𝓞 F) F T.hessian.det ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 h

open Classical in
theorem cInfT_ne_zero_top (h : T₀.Nondegenerate) : cInfT Q₀ T₀ ≠ 0 ∧ cInfT Q₀ T₀ ≠ ⊤ := by
  refine ⟨mul_ne_zero (ENNReal.ofReal_pos.2 (cF_pos' _)).ne' (Finset.prod_ne_zero_iff.2 fun w _ => ?_),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)⟩
  exact (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (abs_pos.2 ((map_ne_zero _).2 (algebraMap_det_ne_zero T₀ h))) _))).ne'

theorem det_towerAdapted_ne_zero :
    (towerAdapted Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT).g.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero

open Classical in
theorem frameLam_ne_zero_top : frameLam Q₀ hQ T₀ hT hn' Ξ ≠ 0 ∧ frameLam Q₀ hQ T₀ hT hn' Ξ ≠ ⊤ := by
  refine ⟨(ENNReal.ofReal_pos.2 (div_pos (Finset.prod_pos fun w _ => pow_pos (abs_pos.2 ((map_ne_zero _).2
    (det_towerAdapted_ne_zero Q₀ hQ T₀ hT hn' Ξ))) _) (cF_pos' _))).ne', ENNReal.ofReal_ne_top⟩

/-- **The archimedean fibration of frames** in Siegel's normalization: constant $c_\infty(T_0)$, stabilizer measures
$\lambda\,\mu^{\mathrm{Tam}}_{H}$ ($=\prod_w|\det g|_w^{n'+1}$ times the transported Leray measures), measure
$(c_\infty(T_0)\lambda)^{-1}\sigma_A$. -/
def frameArchFibration :
    ArchFibration (muArchTamSO Q₀ hQ) (Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ)
      ((cInfT Q₀ T₀ * frameLam Q₀ hQ T₀ hT hn' Ξ)⁻¹ • frameσA Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)) Subtype.val
      (cInfT Q₀ T₀) :=
  (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)).rescale (frameLam Q₀ hQ T₀ hT hn' Ξ)
    (cInfT Q₀ T₀ * frameLam Q₀ hQ T₀ hT hn' Ξ)⁻¹ (cInfT Q₀ T₀) ENNReal.ofReal_ne_top (by
      have h0 := (cInfT_ne_zero_top Q₀ T₀ hT).1
      have ht := (cInfT_ne_zero_top Q₀ T₀ hT).2
      have h1 := (frameLam_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).1
      have h2 := (frameLam_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).2
      calc cInfT Q₀ T₀ * (cInfT Q₀ T₀ * frameLam Q₀ hQ T₀ hT hn' Ξ)⁻¹ * frameLam Q₀ hQ T₀ hT hn' Ξ
          = (cInfT Q₀ T₀ * frameLam Q₀ hQ T₀ hT hn' Ξ) * (cInfT Q₀ T₀ * frameLam Q₀ hQ T₀ hT hn' Ξ)⁻¹ := by ring
        _ = 1 := ENNReal.mul_inv_cancel (mul_ne_zero h0 h1) (ENNReal.mul_ne_top ht h2))

open Classical in
/-- The identity in $\mathbb R$ behind the headline: product formula for $\det g$ and $\det H_{T_0}$. -/
theorem frameDensity_real_identity [IsTotallyReal F] (D : FrameTower Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)
    (hn' : 3 ≤ n') :
    cF F (r + n') * (∏ w : {w : InfinitePlace F // w.IsReal},
        (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹) *
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det| ^ (n' + 1)) /
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
  have hPg := prod_real_mul_tprod (F := F) hg
  have hPh := prod_real_mul_tprod (F := F) hh
  set Gs := ∏ w : {w : InfinitePlace F // w.IsReal}, |σR w g| with hGs
  set Hs := ∏ w : {w : InfinitePlace F // w.IsReal}, |σR w h| with hHs
  have hGne : Gs ≠ 0 := left_ne_zero_of_mul_eq_one hPg
  have hHne : Hs ≠ 0 := left_ne_zero_of_mul_eq_one hPh
  have hA : ∏' v, ‖σV v g‖ = Gs⁻¹ := eq_inv_of_mul_eq_one_right hPg
  have hB : ∏' v, ‖σV v h‖ = Hs⁻¹ := eq_inv_of_mul_eq_one_right hPh
  have h1 : (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w h| ^ n')⁻¹) = (Hs ^ n')⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_pow]
  have h2 : (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w g| ^ (n' + 1)) = Gs ^ (n' + 1) := by
    rw [Finset.prod_pow]
  have hcd : cF F (r + n') / cF F n' = |(discr F : ℝ)| ^ (-(((r + n' : ℕ) : ℝ) * ((r + n' : ℕ) - 1) - (n' : ℝ) * (n' - 1)) / 4) := by
    unfold cF
    rw [← Real.rpow_sub (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F))]
    congr 1
    ring
  have hcn : cF F n' ≠ 0 := (cF_pos' _).ne'
  rw [frameDensityProduct, hprod, hUval, hA, hB, h1, h2, ← hcd]
  simp only [inv_pow, inv_inv]
  field_simp

/-- **Siegel's formula for representations of forms by indefinite forms over a totally real field — unconditional**
(Siegel 1936, Hauptsatz for indefinite forms, measure form; Weil 1965; for forms by forms Siegel 1935): for $Q_0$ nondegenerate
over $\mathcal O_F$ in $N = r + n'$ variables of any signature, $T_0$ nondegenerate of rank $r\ge1$ with a rational frame $\Xi$,
$n' = N - r\ge3$,
$$c_\infty(T_0)\sum_i\rho(M_i, T_0) = |d_F|^{-(N(N-1)-n'(n'-1))/4}\prod_\mathfrak p\beta_\mathfrak p(L, T_0)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^N$, $\rho$ the measures of the representations of
$T_0$ (`repMeasureT` for `frameArchFibration`), $v$ the unit volumes. No hypotheses beyond these. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; forms by forms; totally real) [unverified]"]
theorem siegelIndefiniteForms_totallyReal [IsTotallyReal F] (hr : 1 ≤ r) :
    cInfT Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibration Q₀ hQ T₀ hT hn' Ξ) i =
      ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i := by
  classical
  have hN : 3 ≤ r + n' := by omega
  have hτ : TamagawaNumberTwoAdelic Q₀ hQ := tauTwoAll_release_totallyReal_uncond (r + n') hN Q₀ hQ
  have hτ' : TamagawaNumberTwoAdelic (chosenTower Q₀ hQ T₀ hT hn' Ξ).Q'' (chosenTower Q₀ hQ T₀ hT hn' Ξ).hQ'' :=
    tauTwoAll_release_totallyReal_uncond n' hn' _ _
  have hW := siegelFormsWeil Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT hn' hτ hτ'
  have := countable_GammaSOAdele Q₀
  have hscale : ∀ i, repMeasureT Q₀ T₀ hQ (frameArchFibration Q₀ hQ T₀ hT hn' Ξ) i =
      frameLam Q₀ hQ T₀ hT hn' Ξ * repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)) i :=
    fun i => by
      have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
      exact repMeasureOf_smul _ _ _ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ)).leftInv _
        (frameLam_ne_zero_top Q₀ hQ T₀ hT hn' Ξ).1
  simp_rw [hscale]
  rw [ENNReal.tsum_mul_left, hW, frameOrbitSum_eq Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT hn']
  have key : cInfT Q₀ T₀ * frameLam Q₀ hQ T₀ hT hn' Ξ *
      ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT v) =
      ENNReal.ofReal (frameDensityProduct Q₀ T₀) := by
    rw [← frameDensity_real_identity Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT hn']
    unfold cInfT frameLam
    have hnn : ∀ w : {w : InfinitePlace F // w.IsReal},
        0 ≤ (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹ := fun w => by positivity
    have hnn2 : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹) :=
      Finset.prod_nonneg fun w _ => hnn w
    have hnn3 : 0 ≤ cF F (r + n') * ∏ w : {w : InfinitePlace F // w.IsReal},
        (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹ := mul_nonneg cF_nonneg hnn2
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => hnn w), ← ENNReal.ofReal_mul cF_nonneg,
      ← ENNReal.ofReal_mul hnn3, ← ENNReal.ofReal_mul (mul_nonneg hnn3 (div_nonneg
        (Finset.prod_nonneg fun w _ => by positivity) cF_nonneg))]
  calc cInfT Q₀ T₀ * (frameLam Q₀ hQ T₀ hT hn' Ξ *
        (ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT v) *
          ∑' i, unitVolume Q₀ hQ i))
      = (cInfT Q₀ T₀ * frameLam Q₀ hQ T₀ hT hn' Ξ *
          ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ (chosenTower Q₀ hQ T₀ hT hn' Ξ) hT v)) *
          ∑' i, unitVolume Q₀ hQ i := by ring
    _ = _ := by rw [key]

end QuadFormsKB.Tamagawa.Indefinite
