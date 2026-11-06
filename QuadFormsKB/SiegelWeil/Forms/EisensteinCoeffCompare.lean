/-
# The nonsingular Fourier coefficients of the big-cell part of $E(g_Z, s_0)$ are those of the genus theta series

**Layer:** global over a totally real number field $F$ of degree $d$.

**Setting.** $Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m$, $L = \mathcal O_F^n$, $\Phi_v = \mathbf 1_{L_v^r}$;
$r \ge 1$, $m > 4r^2$; $T_0$ totally positive definite over $\mathcal O_F$; $Y = (Y_w)_w$ positive definite; $c_T(f, Y)$ = `coeffR`.

**Results.**
* `placeOf`, `realEmb_placeOf`: the real place of an embedding $\sigma : F \to \mathbb C$ and the agreement of the two real embeddings.
* `gammaV_cB_inf_pow`: $(\gamma_{V,\infty}c_{B,\infty})^r = \prod_w(2i)^{rm}\prod_i\sqrt{\sigma_w(b_i)}^{\,r}$.

Sources: Weil, Acta Math. 113 (1965), Ch. II–IV [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.SingularSeriesREuler
import QuadFormsKB.SiegelWeil.Forms.ArchBridge
import QuadFormsKB.SiegelWeil.SiegelWeilFormula
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.SiegelWeil.Forms.EisensteinArchPlace
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldJac

open Matrix NumberField Complex MeasureTheory
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus
  QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames QuadFormsKB.Tamagawa.ArchVol
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

/-- The real place of an embedding $\sigma : F \to \mathbb C$ ($F$ totally real). -/
def placeOf (σ : F →ₐ[ℚ] ℂ) : InfinitePlace F := (Tamagawa.Measure.Weil.realPlaceEquiv σ).1

/-- $\sigma \mapsto$ its place is a bijection onto the infinite places. -/
def placeEquiv : (F →ₐ[ℚ] ℂ) ≃ InfinitePlace F :=
  Tamagawa.Measure.Weil.realPlaceEquiv.trans (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w)

lemma placeEquiv_apply (σ : F →ₐ[ℚ] ℂ) : placeEquiv σ = placeOf σ := rfl

/-- The real embedding of the place of $\sigma$ is $\rho_\sigma$. -/
lemma realEmb_placeOf (σ : F →ₐ[ℚ] ℂ) (x : F) :
    HilbertModular.realEmb F (placeOf σ) x = Tamagawa.Measure.realEmb σ x := by
  have h := Tamagawa.Measure.Weil.embedding_realPlaceEquiv (σ := σ) rfl
  unfold HilbertModular.realEmb placeOf
  rw [← h]

/-- **The archimedean Weil constants**: $(\gamma_{V,\infty}c_{B,\infty})^r = \prod_w(2i)^{rm}\big(\prod_i\sqrt{\sigma_w(b_i)}\big)^r$. -/
lemma gammaV_cB_inf_pow (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (algebraMap (𝓞 F) F (b i))) :
    ((localDataInf (F := F)).gammaV (aInf (unitsOfInt b hb)) * (localDataInf (F := F)).cB (aInf (unitsOfInt b hb))) ^ r =
      ∏ w : InfinitePlace F, (2 * I) ^ (r * m) *
        (((∏ i, Real.sqrt (realEmb F w (algebraMap (𝓞 F) F (b i))) ^ r : ℝ)) : ℂ) := by
  have hpos : ∀ i (w : {w : InfinitePlace F // w.IsReal}), 0 < ew w ((unitsOfInt b hb i : Fˣ) : F) := fun i w => by
    rw [ew_eq_realEmbF]; exact hbpos i w.1
  rw [gammaV_inf_eq _ hpos, cB_inf_eq b hb hbpos, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hsq : ∀ w : InfinitePlace F, Real.sqrt (∏ i, realEmb F w (algebraMap (𝓞 F) F (b i))) =
      ∏ i, Real.sqrt (realEmb F w (algebraMap (𝓞 F) F (b i))) := fun w =>
    Real.sqrt_prod _ fun i _ => (hbpos i w).le
  simp_rw [hsq]
  push_cast
  have hP : ∀ (g : InfinitePlace F → Fin (2 * m) → ℂ), ∏ x, ∏ i, g x i ^ r = (∏ x, ∏ i, g x i) ^ r := by
    intro g; rw [← Finset.prod_pow]; congr 1; funext x; rw [Finset.prod_pow]
  rw [hP]
  ring

lemma iY_mem_siegelH (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hY : ∀ w, (Y w).PosDef) (w : InfinitePlace F) :
    iY Y w ∈ WeilRep.Genus.siegelH r := by
  have h := zPt_mem_siegelHF Y hY 0 w
  have e : zPt Y 0 w = iY Y w := by
    have hx : xMat (0 : JR F r → ℝ) w = 0 := by
      ext i j; simp [xMat, xCoord, symOf]
    simp [zPt, iY, hx]
  rwa [e] at h

/-- $\prod_v\operatorname{vol}(\mathcal O_v)^{r(r+1)/2} = |d_F|^{-r(r+1)/4}$. -/
lemma hasProd_volR : HasProd (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => volR r v)
    ((((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ) : ℂ) ^ Fintype.card (SymIdx r)) := by
  have hfin := hasFiniteMulSupport_vol (F := F)
  have hfin' : Function.HasFiniteMulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => volR r v :=
    hfin.subset fun v hv h' => hv (by simp only at h' ⊢; simp [volR, h'])
  have h := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hfin').hasProd
  rw [tprod_eq_finprod (L := SummationFilter.unconditional _) hfin'] at h
  convert h using 1
  unfold volR
  have hC : Function.HasFiniteMulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (((Analysis.selfDualV v).real (Analysis.latticeV v 0) : ℝ) : ℂ) :=
    hfin.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  symm
  rw [← finprod_pow hC]
  have e := (map_finprod Complex.ofRealHom hfin).symm
  simp only [Complex.ofRealHom_eq_coe] at e
  rw [e, finprod_vol]

/-- **The nonsingular Fourier coefficients of the big-cell part of $E(g_Z, s_0)$ are those of the genus theta series**
($F$ totally real, $Q_0 = \sum_ib_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m$, $r \ge 1$, $m > 4r^2$, $T_0$ totally
positive definite over $\mathcal O_F$, $Y_w$ positive definite):
$$c_T(E_{\mathrm{big}}, Y) = \prod_w\det(Y_w)^{m/2}\cdot\frac{\mathrm{repMass}(L, T_0)}{\mathrm{Mass}(L)}\cdot
  \prod_we^{-2\pi\operatorname{tr}(\sigma_w(T_G)Y_w)},$$
i.e. the $T_0$-th coefficient of $\det(\operatorname{Im}Z)^{-m/2}E_{\mathrm{big}}(g_Z, s_0)$ is the $T_0$-th coefficient
$\sum_{\mathrm{cls}(M)}r_M(T_0)/|O(M)|\big/\mathrm{Mass}(L)$ of $\theta_{\mathrm{gen}(L)}$ (`thetaGenR_hasSum_whittaker`). All constants match:
the Jacobian $|d_F|^{r(r+1)/4}$ of the coordinates against $\prod_v\operatorname{vol}(\mathcal O_v)^{-r(r+1)/2}$, and the archimedean
Weil constants $(\gamma_{V,\infty}c_{B,\infty})^r$ against the factors $(2i)^{rm}\prod_i\sqrt{\sigma_w(b_i)}^{\,r}$ of `archPlaceR_eq_gaussR`. -/
@[kb "weil1965" "Ch. II–IV (Siegel–Weil formula of degree r: the nonsingular Fourier coefficients) [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem coeffR_eisBigR_eq_thetaCoeff (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (algebraMap (𝓞 F) F (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F))) (T₀ : QuadForm (𝓞 F) r)
    (hT₀ : T₀.Nondegenerate) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) :
    coeffR (eisBigR b hb) (T₀.map (algebraMap (𝓞 F) F)) Y =
      (∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)) *
        ((repMassT ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m))
            (T₀.map (algebraMap (𝓞 F) F)) /
          mass ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m)) : ℝ) : ℂ) *
        ∏ w, cexp (2 * π * I * ArchR.trU (tW (T₀.map (algebraMap (𝓞 F) F)) w) (iY Y w)) := by
  set T := T₀.map (algebraMap (𝓞 F) F)
  have hmr : r < m := by
    have : (r : ℝ) ≤ 4 * (r : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    exact_mod_cast this.trans_lt hm
  have hrN : r + 3 ≤ 2 * m := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : ((r + 3 : ℕ) : ℝ) < 2 * m := by push_cast; nlinarith
    exact_mod_cast this.le
  obtain ⟨hS, hc⟩ := coeffR_eisBigR_eq_euler b hb hbpos hr hm hpd T₀ hT₀ hpdT hY
  set s : InfinitePlace F → Fin (2 * m) → ℝ := fun w i => realEmb F w (algebraMap (𝓞 F) F (b i))
  have hs : ∀ w i, 0 < s w i := fun w i => hbpos i w
  set J : InfinitePlace F → ℂ := fun w => ∫ B : SymIdx r → ℝ, ArchR.gaussR (s w) (iY Y w + cR (symU B)) *
    cexp (-2 * π * I * ArchR.trU (tW T w) (cR (symU B)))
  set E : InfinitePlace F → ℂ := fun w => cexp (2 * π * I * ArchR.trU (tW T w) (iY Y w))
  set W : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℂ :=
    fun v => whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀)
  set D : ℂ := (((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ) : ℂ) ^ Fintype.card (SymIdx r)
  -- the finite part
  have hW : HasProd W (singR b hb T * D) := by
    refine (hS.mul hasProd_volR).congr_fun fun v => ?_
    simp only [W]; rw [div_mul_cancel₀ _ (volR_ne_zero v)]
  have hD : D ≠ 0 := by
    refine pow_ne_zero _ ?_
    have : 0 < Real.sqrt |(NumberField.discr F : ℝ)| :=
      Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F))
    exact_mod_cast (inv_pos.mpr this).ne'
  have hsing : singR b hb T = (∏' v, W v) * D⁻¹ := by
    rw [hW.tprod_eq, mul_inv_cancel_right₀ hD]
  -- the archimedean part
  have harch : archIntR m T Y = (∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)) * ((phiDetR F r : ℝ) : ℂ)⁻¹ *
      ∏ w, ((2 * I) ^ (r * m) * ((∏ i, (Real.sqrt (s w i) ^ r) : ℝ) : ℂ) * J w) := by
    rw [archIntR_eq_prod Y hY hmr T]
    congr 1
    exact Finset.prod_congr rfl fun w _ => archPlaceR_eq_gaussR (s w) (hs w) T Y hY w
  -- the theta side
  have hθ := thetaGenR_coeff_eq_whittaker_all_places b hb hr hrN hmr hpd T₀ hpdT (fun σ => iY Y (placeOf σ))
    (fun σ => iY_mem_siegelH Y hY (placeOf σ))
  have htS : ∀ σ : F →ₐ[ℚ] ℂ, tSigma T₀ σ = tW T (placeOf σ) := fun σ => by
    funext p; simp only [tSigma, tW, realEmb_placeOf]; rfl
  have hsS : ∀ σ : F →ₐ[ℚ] ℂ, (fun i => Tamagawa.Measure.realEmb σ (algebraMap (𝓞 F) F (b i))) = s (placeOf σ) :=
    fun σ => by funext i; simp only [s, realEmb_placeOf]
  have hσ : ∀ σ : F →ₐ[ℚ] ℂ, cexp (-2 * π * I * ArchR.trU (tSigma T₀ σ) (iY Y (placeOf σ))) *
      ∫ B : UIdx r → ℝ, ArchR.gaussR (fun i => Tamagawa.Measure.realEmb σ (algebraMap (𝓞 F) F (b i)))
          (iY Y (placeOf σ) + cR (symU B)) * cexp (-2 * π * I * ArchR.trU (tSigma T₀ σ) (cR (symU B))) =
      (E (placeOf σ))⁻¹ * J (placeOf σ) := fun σ => by
    rw [htS, hsS]
    simp only [E, J, ← Complex.exp_neg]
    congr 2; ring
  have hprodσ : ∏ σ : F →ₐ[ℚ] ℂ, ((E (placeOf σ))⁻¹ * J (placeOf σ)) = ∏ w, ((E w)⁻¹ * J w) :=
    Fintype.prod_equiv placeEquiv _ _ fun σ => rfl
  have hW' : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), whittakerR v (aOfInt v b hb)
      ((LocalDensity.NF.Qp v T₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) = W v := fun v => by
    simp only [W, aOfInt_eq_aV, locT_eq]
  simp_rw [hσ, hW'] at hθ
  rw [hprodσ, gammaV_cB_inf_pow b hb hbpos] at hθ
  -- assemble
  rw [hc, harch, hsing, hθ, phiDetR_eq]
  have hE : ∀ w, E w ≠ 0 := fun w => Complex.exp_ne_zero _
  have hprodE : (∏ w, (E w)⁻¹) * Finset.univ.prod E = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun w _ => inv_mul_cancel₀ (hE w)
  have hDphi : ((((Real.sqrt |(NumberField.discr F : ℝ)|) ^ Fintype.card (SymIdx r) : ℝ) : ℂ))⁻¹ * D⁻¹ = 1 := by
    simp only [D]
    push_cast
    have hd : (0 : ℝ) < |(NumberField.discr F : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))
    rw [← mul_inv, ← mul_pow, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'), one_pow,
      inv_one]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib (f := fun w => (E w)⁻¹)]
  linear_combination (∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)) * (∏ w : InfinitePlace F, (2 * I) ^ (r * m)) *
    (∏ w, (((∏ i, Real.sqrt (s w i) ^ r : ℝ)) : ℂ)) * (∏ w, J w) * (∏' v, W v) * (hDphi - hprodE)

end QuadFormsKB.SiegelWeil.Forms
