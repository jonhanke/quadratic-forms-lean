/-
# Siegel's formula with a rank-2 anisotropic stabilizer, indefinite, every number field

**Layer:** number fields. $F$ **any** number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $N = r + 2$
variables of any signature, $L = \mathcal O_F^N$, $T_0$ nondegenerate of rank $r\ge1$ with a rational frame $\Xi$
($Q_0\circ\Xi = T_0$), and the complement $W = \Xi^\perp$ (of dimension $n' = 2$) **anisotropic**, i.e.
$$\delta = -\det H_{Q_0}\det H_{T_0}\ (\texttt{deltaForms Q₀ T₀})\ \text{is not a square in }F$$
(`complAnisotropic_iff`: this is equivalent to the anisotropy of $W$, for every rational frame; so it does not depend on
the frame). The isotropic complement ($SO(W)\cong\mathbb G_m$) is excluded.

**Headline** (`siegelIndefiniteForms_rank2_uncond`, unconditional):
$$c_\infty(T_0)\sum_i\rho(M_i, T_0) = |d_F|^{-(N(N-1)-2)/4}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\Bigl(1-\frac{\chi(\mathfrak p)}{N\mathfrak p}\Bigr)
  \cdot\sum_iv(M_i),$$
* $\chi$ = `chiForms Q₀ T₀`, $\chi(\mathfrak p) = (\delta/\mathfrak p)$ at $\mathfrak p\nmid2\delta$ (the character of $E = F(\sqrt\delta)$
  off a finite set), $L(1,\chi) = \lim_{s\to1^+}L_F(s,\chi)$ (exists and is positive, `lOne_chiForms_nf`); the local side is
  the regularized product `regProd χ 1 β` $= L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p/L_\mathfrak p(1,\chi)$,
  whose product
  converges absolutely (`multipliable_localDensityForm_rank2`); the plain product $\prod_\mathfrak p\beta_\mathfrak p$ converges only
  conditionally, to the same value in the natural order given the prime ideal theorem for $\chi$
  (`hasProd_normOrder_localDensityForm_rank2`);
* $c_\infty(T_0)$ = `cInfTNF` $= c_F(N)\prod_{w\mid\infty}|\det H_{T_0}|_w^{-2}$ (normalized absolute values);
* $\rho$ = `repMeasureT` for `frameArchFibrationRank2`: the measure on the stabilizer $H_\Xi\cong SO(W)(F_\infty)$ is
  $\prod_{w\mid\infty}|\det g|_w^{3}$ times Weil's measure of $SO(Q'')(F_\infty)$ (`muArchTamSO`, the archimedean part of
  `muTamBin`: Leray measures of $SO(2)$ / $SO(1,1)$ at the real places, $2\times$ that of $SO_2(\mathbb C)$ at the complex
  places), transported by $h\mapsto g\,\mathrm{diag}(1_r,h)\,g^{-1}$, $g = [\Xi\mid C]$; at $a\Xi$ conjugated by $a$.

**Proof.** Weil's form `siegelFormsWeil_gen` with $\tau(SO(V)) = 2$; the stabilizer: $\tau(SO(W)) = 2$ for Weil's measure
with the convergence factors $L_v(1,\chi)$ (`tauTwoBinaryAll_uncond`, via `covolume_muTam_one_binary`); the orbit sums with
the same factors (`frameOrbitSum_lam`); the product formula.

**Numbers, $N = 3$** (`siegelIndefinite_ternary_uncond`): the case $r = 1$, $T_0 = \langle m\rangle$ ($H_T = (2m)$,
$\delta = -2m\det H_{Q_0}$): representations of $m$ by a ternary $Q_0$ with $m^\perp$ anisotropic; the character is the
ternary character `chiTern Q₀ m` (`chiForms_unary_eq_chiTern`).
-/
import QuadFormsKB.Tamagawa.Indefinite.Rank2Measures
import QuadFormsKB.Tamagawa.Indefinite.Rank2Orbit
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteNF
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteChecks

open MeasureTheory Set Matrix MulAction Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.RegProd NFEuler

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

/-! ### The regularized local side -/

/-- **The local side with a rank-2 complement, regularized**:
$|d_F|^{-(N(N-1)-2)/4}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\,(1-\chi(\mathfrak p)/N\mathfrak p)$ ($N = r + 2$,
$\chi$ = `chiForms Q₀ T₀`, $\beta_\mathfrak p$ = `NF.localDensityForm v Q₀ T₀`; the product `regProd χ 1`). -/
@[kb "siegel1935" "Hauptsatz (local side, forms by forms, complement of rank 2, regularized) [unverified]"]
def frameDensityProductReg (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  |(discr F : ℝ)| ^ (-(((r + 2 : ℕ) : ℝ) * ((r + 2 : ℕ) - 1) - 2) / 4) *
    regProd (chiForms Q₀ T₀) 1 (fun v => NF.localDensityForm v Q₀ T₀)

/-! ### The product formula with convergence factors (any complement rank) -/

section Identity

variable {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (Ξ : RatFrame Q₀ T₀)

open Classical in
/-- The identity in $\mathbb R$ behind the headline: the product formula for $\det g$ and $\det H_{T_0}$, with the
convergence factors $\lambda_v$ carried along. -/
theorem frameDensity_identity_lam (D : FrameTower Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hm : Multipliable fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) :
    cF F (r + n') * ((∏ w : {w : InfinitePlace F // w.IsReal},
        (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * n'))⁻¹) *
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det| ^ (n' + 1)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det‖ ^ (2 * (n' + 1))) /
        cF F n') * ∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v =
      |(discr F : ℝ)| ^ (-(((r + n' : ℕ) : ℝ) * ((r + n' : ℕ) - 1) - (n' : ℝ) * (n' - 1)) / 4) *
        ∏' v, NF.localDensityForm v Q₀ T₀ * lam v := by
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
  have hβ : ∀ v, NF.localDensityForm v Q₀ T₀ * lam v = (frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) * u v :=
    fun v => by
      have := ha v
      have := hb v
      simp only [frameLocFactor, hu]
      rw [← hgdef, ← hhdef]
      field_simp
  have hprod : ∏' v, NF.localDensityForm v Q₀ T₀ * lam v =
      (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) * ∏' v, u v := by
    rw [tprod_congr hβ]
    exact hm.tprod_mul (multipliable_of_hasFiniteMulSupport hufin)
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
  rw [hprod, hUval, hA, hB, h1, h2, ← hcd]
  simp only [inv_pow, inv_inv]
  field_simp

end Identity

/-! ### The data of the headline -/

variable (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (hW : ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀)

/-- The chosen frame coordinates of $\Xi$, complement of rank $2$. -/
def chosenTowerRank2 : FrameTower Q₀ hQ 2 (cols Ξ.1) :=
  Classical.choice (nonempty_frameTower_ratFrame_rank2 Q₀ hQ T₀ hT hW Ξ)

open Classical in
/-- The scale of the stabilizer measures, complement of rank $2$: $\lambda = \prod_{w\mid\infty}|\det g|_w^{3}/c_F(2)$
(normalized absolute values). -/
def frameLamRank2 : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (towerAdapted Q₀ hQ T₀ Ξ (chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ) hT).g.val.det| ^ (2 + 1)) *
    (∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖σC w (towerAdapted Q₀ hQ T₀ Ξ (chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ) hT).g.val.det‖ ^ (2 * (2 + 1))) / cF F 2)

open Classical in
theorem frameLamRank2_ne_zero_top : frameLamRank2 Q₀ hQ T₀ hT hW Ξ ≠ 0 ∧ frameLamRank2 Q₀ hQ T₀ hT hW Ξ ≠ ⊤ := by
  have hg : (towerAdapted Q₀ hQ T₀ Ξ (chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ) hT).g.val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  refine ⟨(ENNReal.ofReal_pos.2 (div_pos (mul_pos (Finset.prod_pos fun w _ => pow_pos (abs_pos.2
    ((map_ne_zero _).2 hg)) _) (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hg)) _))
    (cF_pos' _))).ne', ENNReal.ofReal_ne_top⟩

/-- **The archimedean fibration of frames, complement of rank 2** (Siegel's normalization): constant $c_\infty(T_0)$
(`cInfTNF`), stabilizer measures $\lambda\,\mu^{\mathrm{Tam}}_H$ ($\lambda$ = `frameLamRank2`; $\prod_{w\mid\infty}|\det g|_w^{3}$
times Weil's measure of $SO(Q'')(F_\infty)$, transported), measure $(c_\infty(T_0)\lambda)^{-1}\sigma_A$ on the orbit of
$\Xi_\infty$. -/
def frameArchFibrationRank2 :
    ArchFibration (muArchTamSO Q₀ hQ) (Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ)
      ((cInfTNF Q₀ T₀ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ)⁻¹ •
        frameσA Q₀ hQ T₀ Ξ (chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ)) Subtype.val (cInfTNF Q₀ T₀) :=
  (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ)).rescale (frameLamRank2 Q₀ hQ T₀ hT hW Ξ)
    (cInfTNF Q₀ T₀ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ)⁻¹ (cInfTNF Q₀ T₀) ENNReal.ofReal_ne_top (by
      have h0 := (cInfTNF_ne_zero_top Q₀ T₀ hT).1
      have ht := (cInfTNF_ne_zero_top Q₀ T₀ hT).2
      have h1 := (frameLamRank2_ne_zero_top Q₀ hQ T₀ hT hW Ξ).1
      have h2 := (frameLamRank2_ne_zero_top Q₀ hQ T₀ hT hW Ξ).2
      calc cInfTNF Q₀ T₀ * (cInfTNF Q₀ T₀ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ)⁻¹ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ
          = (cInfTNF Q₀ T₀ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ) *
              (cInfTNF Q₀ T₀ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ)⁻¹ := by ring
        _ = 1 := ENNReal.mul_inv_cancel (mul_ne_zero h0 h1) (ENNReal.mul_ne_top ht h2))

/-! ### Weil's form with the convergence factors -/

section Weil

variable (Q₁ : QuadForm (𝓞 F) (r + 2)) (hQ₁ : Q₁.Nondegenerate) (T₁ : QuadForm (𝓞 F) r)
  (Ξ₁ : RatFrame Q₁ T₁) (D : FrameTower Q₁ hQ₁ 2 (cols Ξ₁.1))

/-- Changing the stabilizer measure `muFin Q'' 1` to `muFin Q'' λ` in the orbit sum: both are multiples of `muFinOne`. -/
theorem frameOrbitSum_mul_finFactor (lam : HeightOneSpectrum (𝓞 F) → ℝ) (h1 : 0 < finFactor D.Q'' fun _ => 1)
    (hl : 0 < finFactor D.Q'' lam) :
    frameOrbitSum Q₁ hQ₁ T₁ Ξ₁ D * ENNReal.ofReal (finFactor D.Q'' fun _ => 1) =
      ENNReal.ofReal (finFactor D.Q'' lam) * frameOrbitSumLam Q₁ hQ₁ T₁ Ξ₁ D lam := by
  unfold frameOrbitSum frameOrbitSumLam
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun O => ?_
  rw [muFin_eq_smul_muFinOne, muFin_eq_smul_muFinOne D.Q'' lam, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul]
  set a := muFin Q₁ (fun _ => 1) (KSO Q₁)
  set m := muFinOne D.Q'' (orbitStab D.ιFin (KSO Q₁) (finOrbitRep Q₁ T₁ Ξ₁ O))
  have e : ∀ c : ℝ, 0 < c → a / (ENNReal.ofReal c * m) = (ENNReal.ofReal c)⁻¹ * (a / m) := fun c hc => by
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 hc).ne')
      (Or.inl ENNReal.ofReal_ne_top)]
    ring
  rw [e _ h1, e _ hl]
  have c1 := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 h1).ne' (ENNReal.ofReal_ne_top (r := finFactor D.Q'' _))
  have c2 := ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hl).ne' (ENNReal.ofReal_ne_top (r := finFactor D.Q'' lam))
  calc (ENNReal.ofReal (finFactor D.Q'' fun _ => 1))⁻¹ * (a / m) * ENNReal.ofReal (finFactor D.Q'' fun _ => 1)
      = ((ENNReal.ofReal (finFactor D.Q'' fun _ => 1))⁻¹ * ENNReal.ofReal (finFactor D.Q'' fun _ => 1)) * (a / m) := by
        ring
    _ = (ENNReal.ofReal (finFactor D.Q'' lam) * (ENNReal.ofReal (finFactor D.Q'' lam))⁻¹) * (a / m) := by
        rw [c1, c2]
    _ = _ := by ring

end Weil

/-- **The measures of representations with the Tamagawa stabilizer measures**, complement of rank $2$:
$\sum_i\rho^{\mathrm{Tam}}(M_i,T_0) = L(1,\chi)\prod_\mathfrak p\bigl(\beta_\mathfrak p|\det g|_\mathfrak p^3|\det H_{T_0}|_\mathfrak p^{-2}
(1-\chi(\mathfrak p)/N\mathfrak p)\bigr)\cdot\sum_iv(M_i)$. -/
theorem tsum_repMeasureT_tam_rank2 (hr : 1 ≤ r) :
    ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ (chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ)) i =
      ENNReal.ofReal (LOne (chiForms Q₀ T₀)) *
        (ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ (chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ) hT v *
          lamL (chiForms Q₀ T₀) v) * ∑' i, unitVolume Q₀ hQ i) := by
  classical
  set D := chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ with hD
  set χ := chiForms Q₀ T₀ with hχdef
  have hN : 3 ≤ r + 2 := by omega
  have hτ : TamagawaNumberTwoAdelic Q₀ hQ := tauTwoAll_release_uncond (r + 2) hN Q₀ hQ
  have hWeil := siegelFormsWeil_gen Q₀ hQ T₀ Ξ D hT (by norm_num) hN hτ
  have hA : AnisotropicF D.Q'' := (anisotropicF_adapted_iff Q₀ T₀ hT (towerAdapted Q₀ hQ T₀ Ξ D hT)).2 hW
  obtain ⟨hL0, hL⟩ := lOne_chiForms_nf hQ hT hW
  obtain ⟨S, hS⟩ := chiP_frame_eq_chiForms_nf Q₀ T₀ hQ hT hW (towerAdapted Q₀ hQ T₀ Ξ D hT) D.hQ''
  have hχ : ∀ v, |χ v| ≤ 1 := abs_chiForms_le Q₀ T₀
  have hcov := covolume_muTam_one_binary D.Q'' D.hQ'' hχ S hS hA hL hL0
  have hf1 := finFactor_one_pos_of_anisotropicF D.Q'' D.hQ'' hA
  have hfl := finFactor_lamL_pos D.Q'' D.hQ'' hχ S hS
  have hsum := frameOrbitSum_mul_finFactor Q₀ hQ T₀ Ξ D (lamL χ) hf1 hfl
  have hLam := frameOrbitSum_lam Q₀ hQ T₀ Ξ D hT (lamL χ) (lamL_pos hχ)
    (multipliable_muLocSO_lamL D.Q'' D.hQ'' hχ S hS) hfl (by norm_num) hN
  rw [hLam] at hsum
  set ρ := ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) i
  set tH := covolume (GammaSOAdele D.Q'') (SOAdele D.Q'') (muTam D.Q'' D.hQ'' fun _ => 1)
  set Sm := frameOrbitSum Q₀ hQ T₀ Ξ D
  set V := ∑' i, unitVolume Q₀ hQ i
  set f1 := ENNReal.ofReal (finFactor D.Q'' fun _ => 1)
  set fl := ENNReal.ofReal (finFactor D.Q'' (lamL χ))
  set P := ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lamL χ v)
  set L := ENNReal.ofReal (LOne χ)
  have hf10 : f1 ≠ 0 := (ENNReal.ofReal_pos.2 hf1).ne'
  have hfl0 : fl ≠ 0 := (ENNReal.ofReal_pos.2 hfl).ne'
  have hc0 : 2 * (f1 * fl) ≠ 0 := mul_ne_zero two_ne_zero (mul_ne_zero hf10 hfl0)
  have hct : 2 * (f1 * fl) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  refine (ENNReal.mul_right_inj hc0 hct).1 ?_
  calc 2 * (f1 * fl) * ρ = (2 * ρ) * f1 * fl := by ring
    _ = tH * (Sm * V) * f1 * fl := by rw [hWeil]
    _ = (tH * fl) * (Sm * f1) * V := by ring
    _ = (2 * L * f1) * (fl * P) * V := by rw [hcov, hsum]
    _ = 2 * (f1 * fl) * (L * (P * V)) := by ring

/-! ### The headline -/

/-- **Siegel's formula for representations of forms by indefinite forms with a rank-2 anisotropic complement, over every
number field — unconditional** (Siegel 1936, Hauptsatz for indefinite forms, measure form; Siegel 1935 for forms by
forms; Weil 1965, convergence factors $L_v(1,\chi)$ for the stabilizer as in Weil 1982, §2.3): for $F$ a number field,
$Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 2$ variables of any signature, $T_0$ nondegenerate of rank $r\ge1$ with
a rational frame $\Xi$, and $\delta = -\det H_{Q_0}\det H_{T_0}$ not a square in $F$ (equivalently, the orthogonal complement
of $\Xi$ is anisotropic, `complAnisotropic_iff`),
$$c_\infty(T_0)\sum_i\rho(M_i, T_0) = |d_F|^{-(N(N-1)-2)/4}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L, T_0)
  \Bigl(1-\frac{\chi(\mathfrak p)}{N\mathfrak p}\Bigr)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^N$, $\chi$ = `chiForms Q₀ T₀`,
$c_\infty(T_0)$ = `cInfTNF`, $\rho$ the measures of the representations of $T_0$ (`repMeasureT` for
`frameArchFibrationRank2`), $v$ the unit volumes. No hypotheses beyond these. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; forms by forms; N − r = 2; every number field) [unverified]"]
theorem siegelIndefiniteForms_rank2_uncond (hr : 1 ≤ r) :
    cInfTNF Q₀ T₀ * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibrationRank2 Q₀ hQ T₀ hT hW Ξ) i =
      ENNReal.ofReal (frameDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i := by
  classical
  set D := chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ with hD
  set χ := chiForms Q₀ T₀ with hχdef
  have := countable_GammaSOAdele Q₀
  have hscale : ∀ i, repMeasureT Q₀ T₀ hQ (frameArchFibrationRank2 Q₀ hQ T₀ hT hW Ξ) i =
      frameLamRank2 Q₀ hQ T₀ hT hW Ξ * repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) i :=
    fun i => by
      have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
      exact repMeasureOf_smul _ _ _ (frameArchFibTam Q₀ hQ T₀ Ξ D).leftInv _
        (frameLamRank2_ne_zero_top Q₀ hQ T₀ hT hW Ξ).1
  simp_rw [hscale]
  rw [ENNReal.tsum_mul_left, tsum_repMeasureT_tam_rank2 Q₀ hQ T₀ hT hW Ξ hr]
  obtain ⟨hL0, hL⟩ := lOne_chiForms_nf hQ hT hW
  have hA : AnisotropicF D.Q'' := (anisotropicF_adapted_iff Q₀ T₀ hT (towerAdapted Q₀ hQ T₀ Ξ D hT)).2 hW
  obtain ⟨S, hS⟩ := chiP_frame_eq_chiForms_nf Q₀ T₀ hQ hT hW (towerAdapted Q₀ hQ T₀ Ξ D hT) D.hQ''
  have hχ : ∀ v, |χ v| ≤ 1 := abs_chiForms_le Q₀ T₀
  have hm := multipliable_frameLocFactor_lam Q₀ hQ T₀ Ξ D hT (lamL χ) (lamL_pos hχ)
    (multipliable_muLocSO_lamL D.Q'' D.hQ'' hχ S hS) (finFactor_lamL_pos D.Q'' D.hQ'' hχ S hS) (by norm_num)
    (by omega)
  have hid := frameDensity_identity_lam Q₀ hQ T₀ Ξ D hT (lamL χ) hm
  have hreg : frameDensityProductReg Q₀ T₀ = LOne χ *
      (|(discr F : ℝ)| ^ (-(((r + 2 : ℕ) : ℝ) * ((r + 2 : ℕ) - 1) - ((2 : ℕ) : ℝ) * ((2 : ℕ) - 1)) / 4) *
        ∏' v, NF.localDensityForm v Q₀ T₀ * lamL χ v) := by
    rw [frameDensityProductReg, regProd, zpow_one]
    simp only [lamL, zpow_one]
    norm_num
    ring
  have key : cInfTNF Q₀ T₀ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ * ENNReal.ofReal (LOne χ) *
      ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lamL χ v) =
      ENNReal.ofReal (frameDensityProductReg Q₀ T₀) := by
    rw [hreg, ← hid]
    unfold cInfTNF frameLamRank2
    have hnn : ∀ w : {w : InfinitePlace F // w.IsReal},
        0 ≤ (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ 2)⁻¹ := fun w => by positivity
    have hnnC : ∀ w : {w : InfinitePlace F // w.IsComplex},
        0 ≤ (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * 2))⁻¹ := fun w => by positivity
    have hnn2 : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ 2)⁻¹) :=
      Finset.prod_nonneg fun w _ => hnn w
    have hnn2C : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsComplex},
        (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * 2))⁻¹) := Finset.prod_nonneg fun w _ => hnnC w
    have hnn3 := mul_nonneg (cF_pos' (F := F) (r + 2)).le (mul_nonneg hnn2 hnn2C)
    have hlam : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal},
        |σR w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det| ^ (2 + 1)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex},
          ‖σC w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det‖ ^ (2 * (2 + 1))) / cF F 2 :=
      div_nonneg (mul_nonneg (Finset.prod_nonneg fun w _ => by positivity)
        (Finset.prod_nonneg fun w _ => by positivity)) (cF_pos' (F := F) 2).le
    have hP : 0 ≤ ∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lamL χ v :=
      tprod_nonneg fun v => mul_nonneg (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v) (lamL_pos hχ v).le
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => hnn w), ← ENNReal.ofReal_prod_of_nonneg (fun w _ => hnnC w),
      ← ENNReal.ofReal_mul hnn2, ← ENNReal.ofReal_mul (cF_pos' _).le,
      ← ENNReal.ofReal_mul hnn3, ← ENNReal.ofReal_mul (mul_nonneg hnn3 hlam),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hnn3 hlam) hL0.le)]
    congr 1
    ring
  calc cInfTNF Q₀ T₀ * (frameLamRank2 Q₀ hQ T₀ hT hW Ξ * (ENNReal.ofReal (LOne χ) *
        (ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lamL χ v) * ∑' i, unitVolume Q₀ hQ i)))
      = (cInfTNF Q₀ T₀ * frameLamRank2 Q₀ hQ T₀ hT hW Ξ * ENNReal.ofReal (LOne χ) *
          ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lamL χ v)) * ∑' i, unitVolume Q₀ hQ i := by
        ring
    _ = _ := by rw [key]

end QuadFormsKB.Tamagawa.Indefinite
