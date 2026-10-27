import QuadFormsKB.Tamagawa.Measure.Weil.QuatZetaLocal
import QuadFormsKB.Tamagawa.Measure.Weil.ChartMeasures

/-!
# The finite part of the zeta integral of $\mathbb H[F,a,b]$: the Euler product

$a, b\in\mathcal O_F\setminus0$, $\hat\Lambda = \hat{\mathcal O}\langle1,i,j,k\rangle$, `muFinQuat` $=\prod_v\lambda_v^{-1}\omega_v$ on
$(\mathbb H\otimes\mathbb A_f)^\times$. For $z\in(\mathbb H\otimes\mathbb A_f)^\times$, $\|\operatorname{nrd}z\|_f = \prod_v|\operatorname{nrd}z_v|_v$
(`normFinQ`).

* **`quatFinZeta a b s`** $=\int\mathbf 1_{\hat\Lambda}(z)\,\|\operatorname{nrd}z\|_f^s\,d\mu_f(z)$.
* **`lintegral_quatBoxSet`** (the chart lemma applied to the integrand): on
  $E_S = \{z : z_v\in\Lambda_v^\times\ (v\notin S)\}$ the integral is
  $\mu_f(\hat\Lambda^\times)\prod_{v\in S}Z_v(s)/\omega_v(\Lambda_v^\times)$.
* **`quatFinZeta_eq`** (**the Euler product**, Weil AAG §3.1, pp. 36–38): for real $s > 2$,
  $$\int\mathbf 1_{\hat\Lambda}\,\|\operatorname{nrd}z\|_f^s\,d\mu_f = \prod_v\frac{Z_v^{\mathrm{sd}}(s-2)}{1 - N(v)^{-1}},$$
  the product of the self-dual local zeta functions of the norm form with Weil's convergence factors (absolutely
  convergent, `hasProd_quatSelfDualZeta`).
* **`tendsto_mul_quatFinZeta`**: $(s-2)\int\mathbf 1_{\hat\Lambda}\|\operatorname{nrd}z\|_f^s\,d\mu_f\to|d_F|^{-2}\rho_F$ as $s\to2^+$
  ($\zeta_F(s-1)$ times an Euler product continuous at $s = 2$ with value $1$ in the standard normalization).

**Outside results used**: Mathlib's `lintegral_iSup_directed_of_measurable`,
`tendsto_atTop_iSup` (monotone exhaustion of the restricted product), `Filter.Tendsto.div`; the library's Euler product
`hasProd_zetaWeil`, `tendsto_zetaRatioProd_zero`, `zetaInt_selfDual` and the chart lemma `map_restrict_quat_eq_pi`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

open LocalZeta GlobalZeta QuadFormsKB.LocalDensity QuadFormsKB.NFEuler

/-! ### The global norm form and its self-dual Euler product -/

section Euler

variable (a b : 𝓞 F)

/-- $Q = \langle1,-a,-b,ab\rangle$ is nondegenerate for $a, b\ne0$. -/
theorem nondegenerate_normForm {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) : (QuatZeta.normForm a b).Nondegenerate :=
  nondegenerate_of_map (by
    rw [QuatZeta.map_normForm]
    exact Quat.nrdForm_nondegenerate two_ne_zero (by simpa using ha) (by simpa using hb))

/-- The self-dual local factor with Weil's convergence factor, $Z_v^{\mathrm{sd}}(\sigma)/(1 - N(v)^{-1})$. -/
def quatSelfDualFactor (v : HeightOneSpectrum (𝓞 F)) (σ : ℝ) : ℝ :=
  zetaInt v (Analysis.selfDualV v) (LocalDensity.NF.Qp v (QuatZeta.normForm a b)) σ /
    (1 - ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ)⁻¹)

/-- **The self-dual Euler product converges** for $\sigma > 0$, to $|d_F|^{-2}\zeta_F(1+\sigma)R(\sigma)$
(the proof of `globalZeta_eq_selfDual`). -/
theorem hasProd_quatSelfDualFactor {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    HasProd (fun v => quatSelfDualFactor a b v σ)
      (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2) * (dedekindZetaR F (1 + σ) *
        zetaRatioProd (QuatZeta.normForm a b) σ)) := by
  classical
  set Q := QuatZeta.normForm a b
  have hQ := nondegenerate_normForm ha hb
  set S := (Analysis.finite_support_diffExp (F := F)).toFinset
  have hfin : ∀ v ∉ S, (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).real (latL v 4) = 1 := fun v hv => by
    have h0 : Analysis.diffExp v = 0 := by by_contra h; apply hv; simp [S, h]
    rw [selfDual_vol_latL, h0, pow_zero, Real.one_rpow]
  have hc : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).real (latL v 4))
      (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2)) := by
    have h1 : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).real (latL v 4))
        (∏ v ∈ S, (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).real (latL v 4)) :=
      hasProd_prod_of_ne_finset_one hfin
    have h2 : ∏' v : HeightOneSpectrum (𝓞 F), (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).real (latL v 4) =
        ∏ v ∈ S, (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).real (latL v 4) := tprod_eq_prod hfin
    have := prod_selfDual_vol (F := F) (n := 4)
    rw [h2] at this
    rw [this] at h1
    convert h1 using 2
  have hw := hasProd_zetaWeil Q hQ (le_refl 4) hσ
  rw [← zetaRatioProd] at hw
  refine (hc.mul hw).congr_fun fun v => ?_
  rw [quatSelfDualFactor, zetaWeil, zetaStd, zetaInt_selfDual v _ (LocalDensity.NF.nondegenerate_Qp v hQ)
    (by norm_num) hσ.le, Measure.real, measure_latL, ENNReal.toReal_pow, ← Measure.real, Analysis.selfDualV_real_Ov,
    mul_div_assoc]

/-- **The residue of the self-dual Euler product**: $\sigma\prod_v Z_v^{\mathrm{sd}}(\sigma)/(1-N(v)^{-1})\to|d_F|^{-2}\rho_F$. -/
theorem tendsto_mul_tprod_quatSelfDualFactor {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) :
    Tendsto (fun σ => σ * ∏' v, quatSelfDualFactor a b v σ) (𝓝[>] 0)
      (𝓝 (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2) * dedekindZeta_residue F)) := by
  have hQ := nondegenerate_normForm ha hb
  have h := ((tendsto_const_nhds (x := |(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2))).mul
    (tendsto_mul_dedekindZetaR_one_add (F := F))).mul (tendsto_zetaRatioProd_zero _ hQ (le_refl 4))
  rw [mul_one] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun σ hσ => ?_)
  show _ = σ * ∏' v, quatSelfDualFactor a b v σ
  rw [(hasProd_quatSelfDualFactor ha hb hσ).tprod_eq]; ring

end Euler

/-! ### The adelic integral and its Euler product -/

section Integral

variable {a b : F}

variable (a b) in
/-- $\|\operatorname{nrd}z\|_f = \prod_v|\operatorname{nrd}z_v|_v$ for $z\in(\mathbb H\otimes\mathbb A_f)^\times$. -/
def normFinQ (z : (QuatFin a b)ˣ) : ℝ := ∏ᶠ v, ‖nrdLoc _ _ (projQ a b v (z : QuatFin a b))‖

variable (a b) in
/-- The local integrand $\mathbf 1_{\Lambda_v}(u)\,|\operatorname{nrd}u|_v^s$ on $(\mathbb H\otimes F_v)^\times$. -/
def quatLocIntegrand (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) (u : (QuatV a b v)ˣ) : ℝ≥0∞ :=
  (lamLoc a b v).indicator (fun _ => (1 : ℝ≥0∞)) (u : QuatV a b v) * ENNReal.ofReal ‖nrdLoc _ _ (u : QuatV a b v)‖ ^ s

variable (a b) in
/-- The finite integrand $\mathbf 1_{\hat\Lambda}(z)\,\|\operatorname{nrd}z\|_f^s$. -/
def quatFinIntegrand (s : ℝ) (z : (QuatFin a b)ˣ) : ℝ≥0∞ :=
  (lamHat a b).indicator (fun _ => (1 : ℝ≥0∞)) (z : QuatFin a b) * ENNReal.ofReal (normFinQ a b z) ^ s

variable (a b) in
/-- **The finite part of the zeta integral of $\mathbb H$**: $\int\mathbf 1_{\hat\Lambda}(z)\,\|\operatorname{nrd}z\|_f^s\,d\mu_f(z)$,
$\mu_f = \prod_v\lambda_v^{-1}\omega_v$ (`muFinQuat`). -/
@[kb "weil1982" "§3.1, the multiplicative calculation, pp. 36-38 (finite part of Z_Φ(s))"]
def quatFinZeta (s : ℝ) : ℝ≥0∞ := ∫⁻ z, quatFinIntegrand a b s z ∂muFinQuat a b

variable (a b) in
/-- $E_S = \{z : z_v\in\Lambda_v^\times\ (v\notin S)\}$. -/
def quatAway (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (QuatFin a b)ˣ :=
  {z | ∀ v, v ∉ S → unitAtQ a b v z ∈ lamLocUnits a b v}

theorem quatAway_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    quatAway a b S ⊆ quatAway a b T := fun _ hx v hv => hx v fun h' => hv (h h')

theorem quatLocalZeta_eq_lintegral (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) :
    quatLocalZeta v a b s = ∫⁻ u, quatLocIntegrand a b v s u ∂omegaQuatV v a b := rfl

theorem measurable_quatLocIntegrand (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) :
    Measurable (quatLocIntegrand a b v s) :=
  ((measurable_const.indicator (measurableSet_lamLoc v a b)).comp Units.continuous_val.measurable).mul
    (((ENNReal.measurable_ofReal.comp (measurable_nrdLoc_norm v a b)).pow_const s).comp
      Units.continuous_val.measurable)

/-- Every $z\in(\mathbb H\otimes\mathbb A_f)^\times$ has $z_v\in\Lambda_v^\times$ for almost all $v$. -/
theorem finite_not_mem_lamLocUnits (z : (QuatFin a b)ˣ) :
    {v | unitAtQ a b v z ∉ lamLocUnits a b v}.Finite := by
  have h1 : ∀ x : FiniteAdeleRing (𝓞 F) F,
      {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite := fun x => x.2
  set y := ((z⁻¹ : (QuatFin a b)ˣ) : QuatFin a b)
  refine (((((h1 (z : QuatFin a b).re).union (h1 (z : QuatFin a b).imI)).union (h1 (z : QuatFin a b).imJ)).union
    (h1 (z : QuatFin a b).imK)).union ((((h1 y.re).union (h1 y.imI)).union (h1 y.imJ)).union (h1 y.imK))).subset ?_
  intro v hv
  simp only [mem_ofPred_eq, lamLocUnits, lamLoc, not_and_or] at hv
  have hinv : (((unitAtQ a b v z)⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) = projQ a b v y := by
    rw [← map_inv]; rfl
  rw [hinv] at hv
  simp only [unitAtQ_val, projQ_re, projQ_imI, projQ_imJ, projQ_imK] at hv
  simp only [mem_union, mem_ofPred_eq]
  tauto

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

include ha hb in
theorem norm_nrdLoc_eq_one {v : HeightOneSpectrum (𝓞 F)} {u : (QuatV a b v)ˣ} (hu : u ∈ lamLocUnits a b v) :
    ‖nrdLoc _ _ (u : QuatV a b v)‖ = 1 := by
  rw [FinitePlace.norm_def, ((mem_lamLocUnits_iff ha hb u).mp hu).2, map_one]; rfl

include ha hb in
/-- **On $E_S$ the finite integrand is a product over $S$**: $\mathbf 1_{\hat\Lambda}(z)\|\operatorname{nrd}z\|_f^s =
\prod_{v\in S}\mathbf 1_{\Lambda_v}(z_v)|\operatorname{nrd}z_v|_v^s$. -/
theorem quatFinIntegrand_eq_prod (S : Finset (HeightOneSpectrum (𝓞 F))) {s : ℝ} (hs : 0 ≤ s)
    {z : (QuatFin a b)ˣ} (hz : z ∈ quatAway a b S) :
    quatFinIntegrand a b s z = ∏ v : S, quatLocIntegrand a b v s (unitAtQ a b v z) := by
  classical
  rw [Finset.prod_coe_sort S (fun v => quatLocIntegrand a b v s (unitAtQ a b v z))]
  have hnorm : normFinQ a b z = ∏ v ∈ S, ‖nrdLoc _ _ (projQ a b v (z : QuatFin a b))‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    have h1 := norm_nrdLoc_eq_one ha hb (hz v hvS)
    rw [unitAtQ_val] at h1
    exact hv h1
  have hind : (lamHat a b).indicator (fun _ => (1 : ℝ≥0∞)) (z : QuatFin a b) =
      ∏ v ∈ S, (lamLoc a b v).indicator (fun _ => (1 : ℝ≥0∞)) (projQ a b v (z : QuatFin a b)) := by
    by_cases h : ∀ v ∈ S, projQ a b v (z : QuatFin a b) ∈ lamLoc a b v
    · have hmem : (z : QuatFin a b) ∈ lamHat a b := (mem_lamHat_iff a b _).mpr fun v => by
        by_cases hv : v ∈ S
        · exact h v hv
        · exact (hz v hv).1
      rw [indicator_of_mem hmem, Finset.prod_eq_one fun v hv => indicator_of_mem (h v hv) _]
    · push Not at h
      obtain ⟨v, hvS, hv⟩ := h
      have hnot : (z : QuatFin a b) ∉ lamHat a b := fun hm => hv ((mem_lamHat_iff a b _).mp hm v)
      rw [indicator_of_notMem hnot, Finset.prod_eq_zero hvS (indicator_of_notMem hv _)]
  rw [quatFinIntegrand, hnorm, hind, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
    ← ENNReal.prod_rpow_of_nonneg hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [quatLocIntegrand, unitAtQ_val]

theorem measurableSet_quatAway (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (quatAway a b S) := by
  have : quatAway a b S = ⋂ v, ⋂ (_ : v ∉ S), unitAtQ a b v ⁻¹' lamLocUnits a b v := by
    ext z; simp [quatAway]
  rw [this]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    (isOpen_lamLocUnits a b v).measurableSet.preimage (continuous_unitAtQ a b v).measurable

theorem measurable_unitAtQ_pi (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Measurable fun (z : (QuatFin a b)ˣ) (v : S) => unitAtQ a b v z :=
  measurable_pi_iff.mpr fun v => (continuous_unitAtQ a b v).measurable

include ha hb ha0 hb0 in
/-- **The chart lemma for the zeta integrand**: $\int_{E_S}\mathbf 1_{\hat\Lambda}\|\operatorname{nrd}\|_f^s\,d\mu_f =
\mu_f(\hat\Lambda^\times)\prod_{v\in S}\omega_v(\Lambda_v^\times)^{-1}Z_v(s)$. -/
theorem lintegral_quatAway (S : Finset (HeightOneSpectrum (𝓞 F))) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ z in quatAway a b S, quatFinIntegrand a b s z ∂muFinQuat a b =
      ENNReal.ofReal (quatHatVol a b) *
        ∏ v : S, ((omegaQuatV v.1 a b (lamLocUnits a b v.1)).toNNReal)⁻¹ * quatLocalZeta v.1 a b s := by
  have h1 : ∫⁻ z in quatAway a b S, quatFinIntegrand a b s z ∂muFinQuat a b =
      ∫⁻ z in quatAway a b S, ∏ v : S, quatLocIntegrand a b v.1 s (unitAtQ a b v z) ∂muFinQuat a b := by
    refine setLIntegral_congr_fun (measurableSet_quatAway S) fun z hz => ?_
    exact quatFinIntegrand_eq_prod ha hb S hs hz
  rw [h1]
  set P : (QuatFin a b)ˣ → ((v : S) → (QuatV a b v.1)ˣ) := fun z v => unitAtQ a b v z with hP
  set G : ((v : S) → (QuatV a b v.1)ˣ) → ℝ≥0∞ := fun y => ∏ v : S, quatLocIntegrand a b v.1 s (y v) with hG
  have hm : Measurable G :=
    Finset.measurable_prod _ fun v _ => (measurable_quatLocIntegrand v.1 s).comp (measurable_pi_apply v)
  have h2 : ∫⁻ z in quatAway a b S, ∏ v : S, quatLocIntegrand a b v.1 s (unitAtQ a b v z) ∂muFinQuat a b =
      ∫⁻ z in quatAway a b S, G (P z) ∂muFinQuat a b := rfl
  rw [h2, ← lintegral_map hm (measurable_unitAtQ_pi S)]
  have h3 := map_restrict_quat_eq_pi ha hb ha0 hb0 S
  have h4 : (muFinQuat a b).restrict (quatAway a b S) = (muFinQuat a b).restrict
      {x : (QuatFin a b)ˣ | ∀ v, v ∉ S → unitAtQ a b v x ∈ lamLocUnits a b v} := rfl
  rw [h4, h3, lintegral_smul_measure, smul_eq_mul]
  congr 1
  rw [hG, lintegral_fintype_prod_eq_prod (fun v : S => quatLocIntegrand a b v.1 s)
    (fun v => measurable_quatLocIntegrand v.1 s)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [lintegral_smul_measure, quatLocalZeta_eq_lintegral, ENNReal.smul_def, smul_eq_mul]

include ha hb in
theorem iSup_indicator_quatAway (s : ℝ) (z : (QuatFin a b)ˣ) :
    ⨆ S : Finset (HeightOneSpectrum (𝓞 F)), (quatAway a b S).indicator (quatFinIntegrand a b s) z =
      quatFinIntegrand a b s z := by
  refine le_antisymm (iSup_le fun S => indicator_le_self _ _ z) ?_
  refine le_iSup_of_le (finite_not_mem_lamLocUnits z).toFinset ?_
  rw [indicator_of_mem]
  intro v hv
  by_contra h
  exact hv ((finite_not_mem_lamLocUnits z).mem_toFinset.mpr h)

include ha hb in
theorem quatFinZeta_eq_iSup {s : ℝ} (hs : 0 ≤ s) :
    quatFinZeta a b s = ⨆ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∫⁻ z in quatAway a b S, quatFinIntegrand a b s z ∂muFinQuat a b := by
  have hmeas : ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      Measurable ((quatAway a b S).indicator (quatFinIntegrand a b s)) := by
    intro S
    have heq : (quatAway a b S).indicator (quatFinIntegrand a b s) = (quatAway a b S).indicator
        (fun z => ∏ v : S, quatLocIntegrand a b v.1 s (unitAtQ a b v z)) := by
      funext z
      by_cases hz : z ∈ quatAway a b S
      · rw [indicator_of_mem hz, indicator_of_mem hz]
        exact quatFinIntegrand_eq_prod ha hb S hs hz
      · rw [indicator_of_notMem hz, indicator_of_notMem hz]
    rw [heq]
    have hG : Measurable fun y : (v : S) → (QuatV a b v.1)ˣ => ∏ v : S, quatLocIntegrand a b v.1 s (y v) :=
      Finset.measurable_prod _ fun v _ => (measurable_quatLocIntegrand v.1 s).comp (measurable_pi_apply v)
    exact (hG.comp (measurable_unitAtQ_pi S)).indicator (measurableSet_quatAway S)
  have hdir : Directed (· ≤ ·) fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      (quatAway a b S).indicator (quatFinIntegrand a b s) := by
    classical
    intro S T
    refine ⟨S ∪ T, fun z => ?_, fun z => ?_⟩
    · exact indicator_le_indicator_of_subset (quatAway_mono Finset.subset_union_left) (fun _ => bot_le) z
    · exact indicator_le_indicator_of_subset (quatAway_mono Finset.subset_union_right) (fun _ => bot_le) z
  calc quatFinZeta a b s = ∫⁻ z, ⨆ S : Finset (HeightOneSpectrum (𝓞 F)),
        (quatAway a b S).indicator (quatFinIntegrand a b s) z ∂muFinQuat a b :=
        lintegral_congr fun z => (iSup_indicator_quatAway ha hb s z).symm
    _ = ⨆ S : Finset (HeightOneSpectrum (𝓞 F)), ∫⁻ z, (quatAway a b S).indicator (quatFinIntegrand a b s) z
        ∂muFinQuat a b := lintegral_iSup_directed_of_measurable hmeas hdir
    _ = _ := iSup_congr fun S => lintegral_indicator (measurableSet_quatAway S) _

include ha hb in
/-- $Z_v(s)\ge\omega_v(\Lambda_v^\times)$: the integrand is $1$ on $\Lambda_v^\times$. -/
theorem omegaQuatV_lamLocUnits_le_quatLocalZeta (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) :
    omegaQuatV v a b (lamLocUnits a b v) ≤ quatLocalZeta v a b s := by
  rw [quatLocalZeta_eq_lintegral, ← setLIntegral_one]
  refine (setLIntegral_le_lintegral _ _).trans' (setLIntegral_mono (measurable_quatLocIntegrand v s) fun u hu => ?_)
  rw [quatLocIntegrand, indicator_of_mem hu.1, norm_nrdLoc_eq_one ha hb hu, ENNReal.ofReal_one, ENNReal.one_rpow,
    one_mul]

end Integral

/-! ### The value: the self-dual Euler product -/

section Value

theorem valued_coe_le_one (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := by
  rw [show algebraMap F (v.adicCompletion F) (a : F) = algebraMap (𝓞 F) (v.adicCompletion F) a from
    (IsScalarTower.algebraMap_apply _ _ _ _).symm]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (HeightOneSpectrum.coe_mem_adicCompletionIntegers v a)

theorem absNorm_eq_q (v : HeightOneSpectrum (𝓞 F)) :
    ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [LocalDensity.NF.q_completion]

/-- The local factor of the chart formula as a real number:
$\omega_v(\Lambda_v^\times)^{-1}Z_v(s) = \bigl(Z_v^{\mathrm{sd}}(s-2)/(1-N(v)^{-1})\bigr)\big/\bigl(\lambda_v^{-1}\omega_v(\Lambda_v^\times)\bigr)$. -/
theorem inv_omega_mul_quatLocalZeta {a b : 𝓞 F} (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 2 < s) :
    ((omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toNNReal)⁻¹ *
        quatLocalZeta v (a : F) (b : F) s =
      ENNReal.ofReal (quatSelfDualFactor a b v (s - 2) / quatLocalFactor (a : F) (b : F) v) := by
  set ω := omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)
  have hω0 : ω ≠ 0 := omegaQuatV_lamLocUnits_ne_zero _ _ v
  have hωT : ω ≠ ⊤ := omegaQuatV_lamLocUnits_ne_top _ _ v
  have hωr : 0 < ω.toReal := ENNReal.toReal_pos hω0 hωT
  have hlam := lamV_pos v
  set Z := LocalZeta.zetaInt v (Analysis.selfDualV v) (LocalDensity.NF.Qp v (QuatZeta.normForm a b)) (s - 2)
  have hZ0 : 0 ≤ Z := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hq : quatLocalFactor (a : F) (b : F) v = (lamV v)⁻¹ * ω.toReal := by
    rw [quatLocalFactor, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hlam.le)]
  have hr : quatSelfDualFactor a b v (s - 2) = Z / lamV v := by
    rw [quatSelfDualFactor, absNorm_eq_q, lamV]
  rw [ENNReal.coe_inv (by simp [ENNReal.toNNReal_eq_zero_iff, hω0, hωT]), quatLocalZeta_eq v a b hs, hq, hr,
    ENNReal.coe_toNNReal hωT]
  rw [show Z / lamV v / ((lamV v)⁻¹ * ω.toReal) = Z / ω.toReal by field_simp]
  rw [ENNReal.ofReal_div_of_pos hωr, ENNReal.ofReal_toReal hωT, div_eq_mul_inv, mul_comm]

/-- **The Euler product** (Weil AAG §3.1, pp. 36–38): for $a, b\in\mathcal O_F\setminus0$ and real $s > 2$,
$$\int_{(\mathbb H\otimes\mathbb A_f)^\times}\mathbf 1_{\hat\Lambda}(z)\,\|\operatorname{nrd}z\|_f^s\,d\mu_f(z) =
\prod_v\frac{Z_v^{\mathrm{sd}}(s-2)}{1-N(v)^{-1}} .$$
*Proof.* $\int = \sup_S\int_{E_S}$ (monotone exhaustion, every $z$ has $z_v\in\Lambda_v^\times$ for almost all $v$); on $E_S$ the
chart lemma gives $\mu_f(\hat\Lambda^\times)\prod_{v\in S}Z_v/\omega_v(\Lambda_v^\times)$; with
$\mu_f(\hat\Lambda^\times) = \prod_v\lambda_v^{-1}\omega_v(\Lambda_v^\times)$ the net tends to $\prod_v\lambda_v^{-1}Z_v$, and the
sup of a monotone net is its limit. -/
@[kb "weil1982" "§3.1, the multiplicative calculation, pp. 36-38 (Euler product)"]
theorem quatFinZeta_eq {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) {s : ℝ} (hs : 2 < s) :
    quatFinZeta (a : F) (b : F) s = ENNReal.ofReal (∏' v, quatSelfDualFactor a b v (s - 2)) := by
  have ha := valued_coe_le_one (F := F) a
  have hb := valued_coe_le_one (F := F) b
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have hσ : 0 < s - 2 := by linarith
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => quatSelfDualFactor a b v (s - 2) with hrdef
  set q : HeightOneSpectrum (𝓞 F) → ℝ := fun v => quatLocalFactor (a : F) (b : F) v with hqdef
  have hrP : HasProd r (∏' v, r v) := (hasProd_quatSelfDualFactor ha0 hb0 hσ).multipliable.hasProd
  have hqV : HasProd q (quatHatVol (a : F) (b : F)) := (multipliable_quatLocalFactor ha hb ha0' hb0').hasProd
  have hV := quatHatVol_pos ha hb ha0' hb0'
  have hq0 : ∀ v, 0 < q v := fun v => quatLocalFactor_pos _ _ v
  have hr0 : ∀ v, 0 ≤ r v := fun v => div_nonneg (setIntegral_nonneg_of_ae_restrict
    (ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _)) (by rw [absNorm_eq_q]; exact (lamV_pos v).le)
  -- the chart integrals
  set Fn : Finset (HeightOneSpectrum (𝓞 F)) → ℝ≥0∞ := fun S =>
    ∫⁻ z in quatAway (a : F) (b : F) S, quatFinIntegrand (a : F) (b : F) s z ∂muFinQuat (a : F) (b : F) with hFn
  have hFeq' : ∀ S, Fn S = ENNReal.ofReal (quatHatVol (a : F) (b : F)) * ∏ v ∈ S, ENNReal.ofReal (r v / q v) := by
    intro S
    simp only [hFn]
    rw [lintegral_quatAway ha hb ha0' hb0' S (by linarith : (0 : ℝ) ≤ s)]
    congr 1
    rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => inv_omega_mul_quatLocalZeta (a := a) (b := b) v.1 hs
  have hFeq : ∀ S, Fn S = ENNReal.ofReal (quatHatVol (a : F) (b : F) * ((∏ v ∈ S, r v) / ∏ v ∈ S, q v)) := by
    intro S
    rw [hFeq', ← Finset.prod_div_distrib, ENNReal.ofReal_mul hV.le,
      ENNReal.ofReal_prod_of_nonneg fun v _ => div_nonneg (hr0 v) (hq0 v).le]
  have hone : ∀ v, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (r v / q v) := by
    intro v
    have h1 := omegaQuatV_lamLocUnits_le_quatLocalZeta ha hb v s
    have h2 := inv_omega_mul_quatLocalZeta (a := a) (b := b) v hs
    have hωT := omegaQuatV_lamLocUnits_ne_top (a : F) (b : F) v
    have hω0 := omegaQuatV_lamLocUnits_ne_zero (a : F) (b : F) v
    rw [← h2, ENNReal.coe_inv (by simp [ENNReal.toNNReal_eq_zero_iff, hω0, hωT]), ENNReal.coe_toNNReal hωT]
    calc (1 : ℝ≥0∞) = (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v))⁻¹ *
          omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v) := (ENNReal.inv_mul_cancel hω0 hωT).symm
      _ ≤ _ := mul_le_mul_right h1 _
  have hmono : Monotone Fn := by
    intro S T hST
    rw [hFeq', hFeq']
    exact mul_le_mul_right (Finset.prod_le_prod_of_subset_of_one_le hST fun v _ _ => hone v) _
  have hsup := tendsto_atTop_iSup hmono
  have hlim : Tendsto Fn atTop (𝓝 (ENNReal.ofReal (∏' v, r v))) := by
    have h1 : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (∏ v ∈ S, r v) / ∏ v ∈ S, q v) atTop
        (𝓝 ((∏' v, r v) / quatHatVol (a : F) (b : F))) :=
      Filter.Tendsto.div (show Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ S, r v) atTop
        (𝓝 (∏' v, r v)) from hrP) (show Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ S, q v) atTop
        (𝓝 (quatHatVol (a : F) (b : F))) from hqV) hV.ne'
    have h2 := (tendsto_const_nhds (x := quatHatVol (a : F) (b : F))).mul h1
    rw [mul_div_cancel₀ _ hV.ne'] at h2
    have h3 := (ENNReal.continuous_ofReal.tendsto _).comp h2
    have hfun : Fn = ENNReal.ofReal ∘ fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
        quatHatVol (a : F) (b : F) * ((∏ v ∈ S, r v) / ∏ v ∈ S, q v) := funext hFeq
    rw [hfun]; exact h3
  rw [quatFinZeta_eq_iSup ha hb (by linarith : (0 : ℝ) ≤ s)]
  exact tendsto_nhds_unique hsup hlim

theorem tendsto_sub_two_nhdsGT : Tendsto (fun s : ℝ => s - 2) (𝓝[>] 2) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
  · have : Tendsto (fun s : ℝ => s - 2) (𝓝 2) (𝓝 (2 - 2)) := tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  · simp only [Set.mem_Ioi] at hs ⊢; linarith

theorem quatFinZeta_ne_top {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) {s : ℝ} (hs : 2 < s) :
    quatFinZeta (a : F) (b : F) s ≠ ⊤ := by
  rw [quatFinZeta_eq ha0 hb0 hs]; exact ENNReal.ofReal_ne_top

theorem toReal_quatFinZeta {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) {s : ℝ} (hs : 2 < s) :
    (quatFinZeta (a : F) (b : F) s).toReal = ∏' v, quatSelfDualFactor a b v (s - 2) := by
  rw [quatFinZeta_eq ha0 hb0 hs, ENNReal.toReal_ofReal]
  exact tprod_nonneg fun v => div_nonneg (setIntegral_nonneg_of_ae_restrict
    (ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _)) (by rw [absNorm_eq_q]; exact (lamV_pos v).le)

/-- **The residue of the finite part** (Weil AAG §3.1, p. 38): $(s-2)\int\mathbf 1_{\hat\Lambda}\|\operatorname{nrd}\|_f^s\,d\mu_f\to
|d_F|^{-2}\rho_F$ as $s\to2^+$. -/
@[kb "weil1982" "§3.1, p. 38 (the residue of the multiplicative zeta function)"]
theorem tendsto_mul_quatFinZeta {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    Tendsto (fun s => (s - 2) * (quatFinZeta (a : F) (b : F) s).toReal) (𝓝[>] 2)
      (𝓝 (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2) * dedekindZeta_residue F)) := by
  refine ((tendsto_mul_tprod_quatSelfDualFactor ha0 hb0).comp tendsto_sub_two_nhdsGT).congr'
    (eventually_nhdsWithin_of_forall fun s hs => ?_)
  simp only [Function.comp_apply]
  rw [toReal_quatFinZeta ha0 hb0 hs]

end Value

end

end QuadFormsKB.Tamagawa.Measure.Weil
