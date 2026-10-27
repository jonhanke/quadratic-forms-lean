import QuadFormsKB.Tamagawa.Measure.Weil.IdeleIdeal
import QuadFormsKB.Tamagawa.Measure.Weil.SL1Tamagawa

/-!
# $\operatorname{vol}(F^\times\backslash\mathbb A_F^1) = \rho_F$ for the measure, and $\tau(\mathrm{SL}_1(D)) = 1$


$F$ is any number field. This file bridges the concrete model of the unramified ideles (`IdeleClass.lean`:
pairs $(x,\mathfrak a)\in F_\infty\times I_F$, `ideleLIntegral`, `ideleClassLIntegral`) to the measure-theoretic
Tamagawa measure `tamIdeles F` on $\mathbb A_F^\times$ and its quotient `muIdeleClass F` on
$F^\times\backslash\mathbb A_F^1$.

* **`lintegral_tamIdeles_ideal`** (pushforward): for $G\ge0$ on $F_\infty\times I_F$ measurable in $x$,
  $\int_{\mathbb A_F^\times}G(g_\infty,\mathfrak a(g_f))\,d\mu = $ `IdeleClass.ideleLIntegral F G`
  $= |d_F|^{-1/2}2^{r_2}\sum_{\mathfrak b}\int G(x,\mathfrak b)\,dx/N(x)$. *Proof.* $\mathbb A_f^\times$ is the disjoint union
  of the cosets $z_{\mathfrak b}\hat{\mathcal O}^\times$ (`IdeleIdeal.lean`), each of mass $|d_F|^{-1/2}$ (`muFinUnits`), and
  $\omega_\infty = |\det(x\cdot)|^{-1}\,2^{r_2}dx = 2^{r_2}dx/N(x)$ (`omegaInf_eq`, `selfDualInf`).
* **`tsum_ideleWeight`**: the weight $w(x,\mathfrak a) = w_F^{-1}\sum_c\mathbf 1_C(x)\mathbf 1[\mathfrak a = \mathfrak a_c]$
  ($C$ the fundamental cone, $\mathfrak a_c$ the class representatives) satisfies
  $\sum_{\gamma\in F^\times}w(\gamma x,(\gamma)\mathfrak a) = 1$ for $N(x)\ne0$ (`sum_tsum_fiber_indicator`).
* **`muIdeleClass_univ_eq_residue`**: $\operatorname{vol}(F^\times\backslash\mathbb A_F^1,\mu^1) = \rho_F$. *Proof.*
  With $\Phi(g) = \mathbf 1_{(1,e]}(\|g\|)\,w(g_\infty,\mathfrak a(g_f))$: through the splitting
  $\mathbb A^\times\cong\mathbb A^1\times\mathbb R_{>0}$ and a fundamental domain $D$ of $F^\times$ in $\mathbb A^1$,
  $\int\Phi\,d\mu = \mu^1(D)\int_1^e dt/t = \mu^1(D)$; by the pushforward and the unfolding
  (`ideleLIntegral_eq_ideleClassLIntegral`) and Thm 3.1.1 (iii) in the model
  (`ideleClassLIntegral_indicator_Ioc`), $\int\Phi\,d\mu = \rho_F\log e = \rho_F$.
* **`idelesClassVolumeResidue`**: the named input `IdeleClassVolumeResidue F` holds for every number field;
  hence **`tamagawa_SL1_division_unconditional`**: $\tau(\mathrm{SL}_1(D)) = 1$ for every quaternion division algebra
  $D = \mathbb H[F,a,b]$ ($a,b\in\mathcal O_F\setminus0$) over every number field.

Weil 1982, Thm 3.1.1 (iii), p. 41 (for $D = k$); §2.4, Lemma 2.4.1, pp. 25–26 (unfolding); §3.7 [unverified page].
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open MeasureTheory Set Filter
open scoped ENNReal NNReal nonZeroDivisors Classical Quaternion

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "FI" => IdeleClass.FracIdeal F

/-! ### Countability of $I_F$ -/

/-- $I_F$ is countable (an ideal is determined by its finitely many nonzero exponents). -/
instance countable_fracIdeal : Countable FI := by
  have hs : Function.Surjective fun f : HeightOneSpectrum (𝓞 F) →₀ ℤ => primeProd (F := F) f := by
    intro I
    have hfin := FractionalIdeal.finite_factors (K := F) (I : FractionalIdeal (𝓞 F)⁰ F)
    refine ⟨Finsupp.ofSupportFinite (fun v => FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F)) hfin, ?_⟩
    refine fracIdeal_ext_count fun v => ?_
    rw [count_primeProd _ ((Finsupp.support _).finite_toSet.subset fun w hw => by simpa using hw)]
    rfl
  exact hs.countable

/-! ### The fibers of $z\mapsto\mathfrak a(z)$ -/

/-- The fiber $\{z : \mathfrak a(z) = \mathfrak b\}$ is the coset $z_{\mathfrak b}\hat{\mathcal O}^\times$. -/
theorem ideleIdeal_fiber_eq (𝔟 : FI) {z₀ : AFˣ} (hz₀ : ideleIdeal F z₀ = 𝔟) :
    {z : AFˣ | ideleIdeal F z = 𝔟} = (fun z => z₀⁻¹ * z) ⁻¹' (OHatUnits F : Set AFˣ) := by
  ext z
  simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, ← ideleIdeal_eq_one_iff, map_mul, map_inv, hz₀]
  rw [inv_mul_eq_one, eq_comm]

theorem isOpen_ideleIdeal_fiber (𝔟 : FI) : IsOpen {z : AFˣ | ideleIdeal F z = 𝔟} := by
  obtain ⟨z₀, hz₀⟩ := ideleIdeal_surjective 𝔟
  rw [ideleIdeal_fiber_eq 𝔟 hz₀]
  exact isOpen_OHatUnits.preimage (continuous_const.mul continuous_id)

theorem measurableSet_ideleIdeal_fiber (𝔟 : FI) : MeasurableSet {z : AFˣ | ideleIdeal F z = 𝔟} :=
  (isOpen_ideleIdeal_fiber 𝔟).measurableSet

/-- **Each fiber of $z\mapsto\mathfrak a(z)$ has mass $\mu_f(\hat{\mathcal O}^\times) = |d_F|^{-1/2}$.** -/
theorem muFinUnits_ideleIdeal_fiber (𝔟 : FI) :
    muFinUnits F {z : AFˣ | ideleIdeal F z = 𝔟} = ENNReal.ofReal (ohatVol F) := by
  obtain ⟨z₀, hz₀⟩ := ideleIdeal_surjective 𝔟
  rw [ideleIdeal_fiber_eq 𝔟 hz₀, measure_preimage_mul, muFinUnits_OHatUnits]

/-- A function of $\mathfrak a(z)$ as a countable sum of fiber indicators. -/
theorem comp_ideleIdeal_eq_tsum (H : FI → ℝ≥0∞) (z : AFˣ) :
    H (ideleIdeal F z) = ∑' 𝔟 : FI, {z : AFˣ | ideleIdeal F z = 𝔟}.indicator (fun _ => H 𝔟) z := by
  rw [tsum_eq_single (ideleIdeal F z)]
  · rw [indicator_of_mem (by simp)]
  · intro 𝔟 h𝔟
    rw [indicator_of_notMem (by simpa [eq_comm] using h𝔟)]

theorem measurable_comp_ideleIdeal (G : mixedSpace F → FI → ℝ≥0∞) (hG : ∀ 𝔟, Measurable (G · 𝔟)) :
    Measurable fun g : (Adeles F)ˣ => G (infPart g) (ideleIdeal F (finPart g)) := by
  have hinf : Measurable fun g : (Adeles F)ˣ => ((infPart g : (mixedSpace F)ˣ) : mixedSpace F) :=
    (Units.continuous_val.comp continuous_infPart).measurable
  have hfin : Measurable fun g : (Adeles F)ˣ => finPart g := continuous_finPart.measurable
  have : (fun g : (Adeles F)ˣ => G (infPart g) (ideleIdeal F (finPart g))) = fun g =>
      ∑' 𝔟 : FI, G (infPart g) 𝔟 * {z : AFˣ | ideleIdeal F z = 𝔟}.indicator 1 (finPart g) := by
    funext g
    rw [tsum_eq_single (ideleIdeal F (finPart g))]
    · rw [indicator_of_mem (by simp), Pi.one_apply, mul_one]
    · intro 𝔟 h𝔟
      rw [indicator_of_notMem (by simpa [eq_comm] using h𝔟), mul_zero]
  rw [this]
  exact Measurable.tsum fun 𝔟 =>
    ((hG 𝔟).comp hinf).mul ((measurable_one.indicator (measurableSet_ideleIdeal_fiber 𝔟)).comp hfin)

/-! ### $\omega_\infty$ against Lebesgue measure -/

theorem isUnit_of_norm_ne_zero {x : mixedSpace F} (h : mixedEmbedding.norm x ≠ 0) : IsUnit x := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ x) ≠ 0 := fun h0 => h (by
    rw [← IdeleClass.abs_det_mulLeft_mixedSpace, h0, abs_zero])
  have hu : IsUnit (LinearMap.mulLeft ℝ x) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨y, hy⟩ := (Module.End.isUnit_iff _).mp hu |>.surjective 1
  exact isUnit_iff_exists_inv.mpr ⟨y, hy⟩

/-- **$\int_{F_\infty^\times}h\,d\omega_\infty = 2^{r_2}\int_{F_\infty}h(x)\,dx/N(x)$.** -/
theorem lintegral_omegaInf (h : mixedSpace F → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ u, h (u : mixedSpace F) ∂omegaInf F =
      2 ^ nrComplexPlaces F * ∫⁻ x, h x * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ := by
  have hemb : MeasurableEmbedding (Units.val : (mixedSpace F)ˣ → mixedSpace F) :=
    isOpenEmbedding_val_mixedSpace.measurableEmbedding
  set k : mixedSpace F → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ with hk
  have hkm : Measurable k := hh.mul (IdeleClass.measurable_invNorm F)
  have hdens : Measurable fun u : (mixedSpace F)ˣ =>
      ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (u : mixedSpace F))|⁻¹ :=
    ((continuous_abs_det_mulLeft (F := F)).comp Units.continuous_val).measurable.inv.ennreal_ofReal
  rw [omegaInf_eq, lintegral_withDensity_eq_lintegral_mul _ hdens
    (show Measurable fun u : (mixedSpace F)ˣ => h u from hh.comp Units.continuous_val.measurable)]
  trans ∫⁻ u, k (u : mixedSpace F) ∂(Measure.comap Units.val (Analysis.selfDualInf (F := F)))
  · exact lintegral_congr fun u => by
      simp only [Pi.mul_apply, k, IdeleClass.abs_det_mulLeft_mixedSpace, mul_comm]
  rw [← hemb.lintegral_map, hemb.map_comap, Analysis.selfDualInf]
  have hk0 : ∀ x ∉ range (Units.val : (mixedSpace F)ˣ → mixedSpace F), k x = 0 := by
    intro x hx
    have hN : mixedEmbedding.norm x = 0 := by
      by_contra hN
      exact hx ⟨(isUnit_of_norm_ne_zero hN).unit, rfl⟩
    simp [k, hN]
  rw [setLIntegral_eq_of_support_subset (fun x hx => by
      by_contra h'; exact hx (hk0 x h')), lintegral_smul_measure]
  simp [ENNReal.smul_def]

/-! ### The pushforward of `tamIdeles` -/

theorem ofReal_ideleConst :
    ENNReal.ofReal (IdeleClass.ideleConst F) = ENNReal.ofReal (ohatVol F) * 2 ^ nrComplexPlaces F := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  rw [IdeleClass.ideleConst, ohatVol, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- **The pushforward of Weil's Tamagawa measure on $\mathbb A_F^\times$ to the model**: for $G\ge0$ on
$F_\infty\times I_F$ measurable in $x$,
$$\int_{\mathbb A_F^\times}G(g_\infty,\mathfrak a(g_f))\,d\mu(g) = |d_F|^{-1/2}\,2^{r_2}\sum_{\mathfrak b}\int_{F_\infty}
G(x,\mathfrak b)\,\frac{dx}{N(x)}$$
(`IdeleClass.ideleLIntegral`). So the concrete integral is the integral against `tamIdeles` of the corresponding
$\hat{\mathcal O}^\times$-invariant function. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure of I_k); §3.2, p. 42 (ω_Z on I_k)"]
theorem lintegral_tamIdeles_ideal (G : mixedSpace F → FI → ℝ≥0∞) (hG : ∀ 𝔟, Measurable (G · 𝔟)) :
    ∫⁻ g, G (infPart g) (ideleIdeal F (finPart g)) ∂tamIdeles F = IdeleClass.ideleLIntegral F G := by
  have he : ((idelesEquiv F).symm : _ → (Adeles F)ˣ) = (idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [tamIdeles, he, lintegral_map_equiv]
  have hinf : ∀ p : (mixedSpace F)ˣ × AFˣ, infPart ((idelesEquiv F).symm p) = p.1 := fun p =>
    congrArg Prod.fst ((idelesEquiv F).apply_symm_apply p)
  have hfin : ∀ p : (mixedSpace F)ˣ × AFˣ, finPart ((idelesEquiv F).symm p) = p.2 := fun p =>
    congrArg Prod.snd ((idelesEquiv F).apply_symm_apply p)
  change ∫⁻ p, G (infPart ((idelesEquiv F).symm p)) (ideleIdeal F (finPart ((idelesEquiv F).symm p)))
    ∂(omegaInf F).prod (muFinUnits F) = _
  simp_rw [hinf, hfin]
  have hsum : ∀ p : (mixedSpace F)ˣ × AFˣ, G (p.1 : mixedSpace F) (ideleIdeal F p.2) =
      ∑' 𝔟 : FI, G (p.1 : mixedSpace F) 𝔟 * {z : AFˣ | ideleIdeal F z = 𝔟}.indicator 1 p.2 := by
    intro p
    rw [tsum_eq_single (ideleIdeal F p.2)]
    · rw [indicator_of_mem (by simp), Pi.one_apply, mul_one]
    · intro 𝔟 h𝔟
      rw [indicator_of_notMem (by simpa [eq_comm] using h𝔟), mul_zero]
  simp_rw [hsum]
  have hm : ∀ 𝔟 : FI, Measurable fun p : (mixedSpace F)ˣ × AFˣ =>
      G (p.1 : mixedSpace F) 𝔟 * {z : AFˣ | ideleIdeal F z = 𝔟}.indicator 1 p.2 :=
    fun 𝔟 => ((hG 𝔟).comp (Units.continuous_val.measurable.comp measurable_fst)).mul
      ((measurable_one.indicator (measurableSet_ideleIdeal_fiber 𝔟)).comp measurable_snd)
  rw [lintegral_tsum fun 𝔟 => (hm 𝔟).aemeasurable]
  have hprod : ∀ 𝔟 : FI, ∫⁻ p, G (p.1 : mixedSpace F) 𝔟 * {z : AFˣ | ideleIdeal F z = 𝔟}.indicator 1 p.2
      ∂(omegaInf F).prod (muFinUnits F) =
      (2 ^ nrComplexPlaces F * ∫⁻ x, G x 𝔟 * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹) *
        ENNReal.ofReal (ohatVol F) := by
    intro 𝔟
    rw [lintegral_prod_mul (f := fun u : (mixedSpace F)ˣ => G u 𝔟)
      ((hG 𝔟).comp Units.continuous_val.measurable).aemeasurable
      (measurable_one.indicator (measurableSet_ideleIdeal_fiber 𝔟)).aemeasurable,
      lintegral_omegaInf _ (hG 𝔟), lintegral_indicator_one (measurableSet_ideleIdeal_fiber 𝔟),
      muFinUnits_ideleIdeal_fiber]
  simp_rw [hprod]
  rw [IdeleClass.ideleLIntegral, ofReal_ideleConst, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun 𝔟 => ?_
  ring

/-! ### The weight function $w$ with $\sum_{\gamma\in F^\times}w(\gamma z) = 1$ -/

/-- **The weight** $w(x,\mathfrak a) = w_F^{-1}\sum_{c\in\mathrm{Cl}_F}\mathbf 1_C(x)\,\mathbf 1[\mathfrak a = \mathfrak a_c]$
($C$ = `fundamentalCone F`, $\mathfrak a_c$ = `IdeleClass.classRep F c`, $w_F$ = `torsionOrder F`). -/
def ideleWeight (x : mixedSpace F) (𝔞 : FI) : ℝ≥0∞ :=
  (torsionOrder F : ℝ≥0∞)⁻¹ * ∑ c : ClassGroup (𝓞 F),
    if 𝔞 = IdeleClass.classRep F c then (fundamentalCone F).indicator 1 x else 0

theorem measurable_ideleWeight (𝔞 : FI) : Measurable (ideleWeight · 𝔞) := by
  unfold ideleWeight
  refine measurable_const.mul (Finset.measurable_sum _ fun c _ => ?_)
  by_cases h : 𝔞 = IdeleClass.classRep F c
  · simp only [h, ↓reduceIte]
    exact measurable_one.indicator (measurableSet_fundamentalCone F)
  · simp only [h, ↓reduceIte]
    exact measurable_const

theorem principalSMulFin_inv_eq_iff (γ : Fˣ) (𝔞 𝔟 : FI) :
    IdeleClass.principalSMulFin F γ⁻¹ 𝔟 = 𝔞 ↔ IdeleClass.principalSMulFin F γ 𝔞 = 𝔟 := by
  simp only [IdeleClass.principalSMulFin, map_inv]
  rw [inv_mul_eq_iff_eq_mul, eq_comm]

/-- **$\sum_{\gamma\in F^\times}w(\gamma x,(\gamma)\mathfrak b) = 1$** for $N(x)\ne0$: each $F^\times$-orbit meets
$\bigsqcup_c C\times\{\mathfrak a_c\}$ in exactly $w_F$ points (`sum_tsum_fiber_indicator`). -/
theorem tsum_ideleWeight (𝔟 : FI) {y : mixedSpace F} (hy : mixedEmbedding.norm y ≠ 0) :
    ∑' γ : Fˣ, ideleWeight (IdeleClass.principalSMulInf F γ y) (IdeleClass.principalSMulFin F γ 𝔟) = 1 := by
  have key := IdeleClass.sum_tsum_fiber_indicator F 𝔟 hy
  rw [← (Equiv.inv Fˣ).tsum_eq]
  simp only [ideleWeight, ENNReal.tsum_mul_left, Equiv.inv_apply]
  have hw0 : (torsionOrder F : ℝ≥0∞) ≠ 0 := by exact_mod_cast (torsionOrder_pos F).ne'
  have hswap : ∑' γ : Fˣ, ∑ c : ClassGroup (𝓞 F),
      (if IdeleClass.principalSMulFin F γ⁻¹ 𝔟 = IdeleClass.classRep F c then
        (fundamentalCone F).indicator (1 : mixedSpace F → ℝ≥0∞) (IdeleClass.principalSMulInf F γ⁻¹ y) else 0) =
      ∑ c : ClassGroup (𝓞 F), ∑' γ : Fˣ,
        (if IdeleClass.principalSMulFin F γ (IdeleClass.classRep F c) = 𝔟 then
          (fundamentalCone F).indicator (1 : mixedSpace F → ℝ≥0∞) (IdeleClass.principalSMulInf F γ⁻¹ y) else 0) := by
    rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    refine Finset.sum_congr rfl fun c _ => tsum_congr fun γ => ?_
    simp only [principalSMulFin_inv_eq_iff]
  rw [hswap, key, ENNReal.inv_mul_cancel hw0 (ENNReal.natCast_ne_top _)]

theorem norm_unit_ne_zero (u : (mixedSpace F)ˣ) : mixedEmbedding.norm (u : mixedSpace F) ≠ 0 := by
  intro h
  have h1 : mixedEmbedding.norm ((u : mixedSpace F) * ((u⁻¹ : (mixedSpace F)ˣ) : mixedSpace F)) = 1 := by
    rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem infPart_mul (g h : (Adeles F)ˣ) : infPart (g * h) = infPart g * infPart h := map_mul _ g h

theorem finPart_mul (g h : (Adeles F)ˣ) : finPart (g * h) = finPart g * finPart h := map_mul _ g h

/-- The weight on $\mathbb A_F^\times$: $w'(g) = w(g_\infty,\mathfrak a(g_f))$. -/
def ideleWeight' (g : (Adeles F)ˣ) : ℝ≥0∞ := ideleWeight (infPart g : mixedSpace F) (ideleIdeal F (finPart g))

theorem measurable_ideleWeight' : Measurable (ideleWeight' (F := F)) :=
  measurable_comp_ideleIdeal _ measurable_ideleWeight

/-- **$\sum_{\gamma\in F^\times}w'(\gamma g) = 1$ for every idele $g$.** -/
theorem tsum_ideleWeight' (g : (Adeles F)ˣ) : ∑' γ : Fˣ, ideleWeight' (diagUnits F γ * g) = 1 := by
  have h : ∀ γ : Fˣ, ideleWeight' (diagUnits F γ * g) = ideleWeight
      (IdeleClass.principalSMulInf F γ (infPart g : mixedSpace F))
      (IdeleClass.principalSMulFin F γ (ideleIdeal F (finPart g))) := by
    intro γ
    rw [ideleWeight', infPart_mul, finPart_mul, map_mul, finPart_diagUnits, ideleIdeal_finDiag, Units.val_mul,
      infPart_diagUnits_val]
    rfl
  simp_rw [h]
  exact tsum_ideleWeight _ (norm_unit_ne_zero _)

/-! ### $F^\times$ as the group of principal ideles of norm one -/

theorem diagUnits_injective : Function.Injective (diagUnits F) := by
  intro ξ η h
  have h' : diagRing F (ξ : F) = diagRing F (η : F) := congrArg Units.val h
  exact Units.ext ((diagRing F).injective h')

/-- $F^\times\cong$ `diagUnitsOne F` ($\xi\mapsto$ the principal idele $\xi$, of norm one). -/
def diagUnitsOneEquiv : Fˣ ≃ diagUnitsOne F :=
  Equiv.ofBijective (fun ξ => ⟨⟨diagUnits F ξ, diagUnitsSub_le_ideleOne ⟨ξ, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨ξ, rfl⟩⟩)
    ⟨fun ξ η h => diagUnits_injective (congrArg (fun γ : diagUnitsOne F => ((γ : ideleOne F) : (Adeles F)ˣ)) h),
      fun γ => by
        obtain ⟨ξ, hξ⟩ := Subgroup.mem_subgroupOf.mp γ.2
        exact ⟨ξ, Subtype.ext (Subtype.ext hξ)⟩⟩

theorem coe_diagUnitsOneEquiv (ξ : Fˣ) :
    (((diagUnitsOneEquiv ξ : diagUnitsOne F) : ideleOne F) : (Adeles F)ˣ) = diagUnits F ξ := rfl

/-! ### The main computation -/

theorem ideleSplit_symm_apply (a : ideleOne F) (t : Multiplicative ℝ) :
    (ideleSplit F).symm (a, t) = (a : (Adeles F)ˣ) * normSectionHom F t := rfl

theorem ideleNorm_normSectionHom (t : Multiplicative ℝ) :
    ideleNorm F (normSectionHom F t) = Real.exp t.toAdd :=
  ideleNorm_normSection (Real.exp t.toAdd) (Real.exp_pos _)

/-- The test function $\Phi(g) = \mathbf 1_{(1,e]}(\|g\|)\,w'(g)$. -/
def ideleTest (g : (Adeles F)ˣ) : ℝ≥0∞ := (Ioc 1 (Real.exp 1)).indicator 1 (ideleNorm F g) * ideleWeight' g

theorem measurable_ideleTest : Measurable (ideleTest (F := F)) :=
  ((measurable_one.indicator measurableSet_Ioc).comp continuous_ideleNorm.measurable).mul measurable_ideleWeight'

/-- **$\int_{\mathbb A^1}w'(a\,s)\,d\mu^1(a) = \mu^1(D)$** for every idele $s$ and every fundamental domain $D$ of
$F^\times$ in $\mathbb A^1$. -/
theorem lintegral_ideleWeight'_mul (s : (Adeles F)ˣ) :
    ∫⁻ a, ideleWeight' ((a : (Adeles F)ˣ) * s) ∂muIdeleOne F = muIdeleOne F (ideleClassFD F) := by
  have hD := isFundamentalDomain_ideleClassFD (F := F)
  have hm : Measurable fun a : ideleOne F => ideleWeight' ((a : (Adeles F)ˣ) * s) :=
    measurable_ideleWeight'.comp ((continuous_subtype_val.mul continuous_const).measurable)
  rw [hD.lintegral_eq_tsum'']
  rw [← lintegral_tsum (μ := (muIdeleOne F).restrict (ideleClassFD F))
    (f := fun (γ : diagUnitsOne F) (a : ideleOne F) => ideleWeight' (((γ • a : ideleOne F) : (Adeles F)ˣ) * s))
    fun γ => (hm.comp (measurable_const_smul γ)).aemeasurable]
  rw [← setLIntegral_one]
  refine lintegral_congr fun a => ?_
  rw [← diagUnitsOneEquiv.tsum_eq]
  have h : ∀ ξ : Fˣ, (((diagUnitsOneEquiv ξ • a : ideleOne F) : (Adeles F)ˣ) * s) =
      diagUnits F ξ * ((a : (Adeles F)ˣ) * s) := fun ξ => by
    rw [← mul_assoc]; rfl
  simp_rw [h]
  exact tsum_ideleWeight' _

theorem dtt_toAdd_Ioc : dtt (Multiplicative.toAdd ⁻¹' Ioc (0 : ℝ) 1) = 1 := by
  rw [dtt_apply]
  change volume (Ioc (0 : ℝ) 1) = 1
  simp

theorem exp_mem_Ioc_iff (t : ℝ) : Real.exp t ∈ Ioc 1 (Real.exp 1) ↔ t ∈ Ioc (0 : ℝ) 1 := by
  simp only [mem_Ioc, Real.one_lt_exp_iff, Real.exp_le_exp]

/-- **$\int_{\mathbb A^\times}\Phi\,d\mu = \mu^1(D)$**: through $\mathbb A^\times\cong\mathbb A^1\times\mathbb R_{>0}$
(`map_ideleSplit_tamIdeles`), $\int\Phi = \int_{(1,e]}\int_{\mathbb A^1}w'(a\,s(t))\,d\mu^1(a)\,\frac{dt}{t}
= \mu^1(D)\int_1^e\frac{dt}{t}$. -/
theorem lintegral_ideleTest : ∫⁻ g, ideleTest g ∂tamIdeles F = muIdeleOne F (ideleClassFD F) := by
  have he : ((ideleSplit F) : (Adeles F)ˣ → ideleOne F × Multiplicative ℝ) =
      (ideleSplit F).toHomeomorph.toMeasurableEquiv := rfl
  have hmeas : Measurable fun p : ideleOne F × Multiplicative ℝ => ideleTest ((ideleSplit F).symm p) :=
    measurable_ideleTest.comp (ideleSplit F).symm.continuous.measurable
  have h1 : ∫⁻ g, ideleTest g ∂tamIdeles F =
      ∫⁻ p, ideleTest ((ideleSplit F).symm p) ∂(tamIdeles F).map (ideleSplit F) := by
    rw [he, lintegral_map_equiv]
    refine lintegral_congr fun g => ?_
    change ideleTest g = ideleTest ((ideleSplit F).symm (ideleSplit F g))
    rw [(ideleSplit F).symm_apply_apply]
  rw [h1, map_ideleSplit_tamIdeles, lintegral_prod_symm _ hmeas.aemeasurable]
  have h2 : ∀ t : Multiplicative ℝ, ∫⁻ a, ideleTest ((ideleSplit F).symm (a, t)) ∂muIdeleOne F =
      (Multiplicative.toAdd ⁻¹' Ioc (0 : ℝ) 1).indicator 1 t * muIdeleOne F (ideleClassFD F) := by
    intro t
    have hval : ∀ a : ideleOne F, ideleTest ((ideleSplit F).symm (a, t)) =
        (Multiplicative.toAdd ⁻¹' Ioc (0 : ℝ) 1).indicator 1 t *
          ideleWeight' ((a : (Adeles F)ˣ) * normSectionHom F t) := by
      intro a
      rw [ideleSplit_symm_apply, ideleTest, ideleNorm_mul, mem_ideleOne.mp a.2, one_mul,
        ideleNorm_normSectionHom]
      congr 1
      by_cases ht : t.toAdd ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem ((exp_mem_Ioc_iff _).2 ht),
          indicator_of_mem (show t ∈ Multiplicative.toAdd ⁻¹' Ioc (0 : ℝ) 1 from ht)]
        rfl
      · rw [indicator_of_notMem (fun h => ht ((exp_mem_Ioc_iff _).1 h)),
          indicator_of_notMem (show t ∉ Multiplicative.toAdd ⁻¹' Ioc (0 : ℝ) 1 from ht)]
    simp_rw [hval]
    rw [lintegral_const_mul _ (show Measurable fun a : ideleOne F =>
      ideleWeight' ((a : (Adeles F)ˣ) * normSectionHom F t) from measurable_ideleWeight'.comp
        ((continuous_subtype_val.mul continuous_const).measurable)), lintegral_ideleWeight'_mul]
  simp_rw [h2]
  have hS : MeasurableSet (Multiplicative.toAdd ⁻¹' Ioc (0 : ℝ) 1) := (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))
  rw [lintegral_mul_const _ (measurable_one.indicator hS), lintegral_indicator_one hS, dtt_toAdd_Ioc, one_mul]

/-- The integrand corresponding to $\Phi$:
$G(x,\mathfrak a) = \mathbf 1_{(1,e]}(N(x)/N(\mathfrak a))\,w(x,\mathfrak a)$. -/
def ideleTestModel (x : mixedSpace F) (𝔞 : FI) : ℝ≥0∞ :=
  (Ioc 1 (Real.exp 1)).indicator 1 (IdeleClass.ideleNorm F x 𝔞) * ideleWeight x 𝔞

theorem measurable_ideleTestModel (𝔞 : FI) : Measurable (ideleTestModel · 𝔞) :=
  ((measurable_one.indicator measurableSet_Ioc).comp
    ((mixedEmbedding.continuous_norm F).measurable.div_const _)).mul (measurable_ideleWeight 𝔞)

theorem ideleTest_eq (g : (Adeles F)ˣ) :
    ideleTest g = ideleTestModel (infPart g : mixedSpace F) (ideleIdeal F (finPart g)) := by
  rw [ideleTest, ideleTestModel, ideleWeight', ideleNorm_eq_ideleClass]

/-- **Weil's Theorem 3.1.1 (iii) for $\mathbb G_m$, for the measure:**
$$\operatorname{vol}(F^\times\backslash\mathbb A_F^1,\ \mu^1) = \rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$$
for every number field $F$ (`muIdeleClass`, the quotient of the Haar measure $\mu^1$ with
$\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v = \mu^1\times dt/t$; no global factor $\rho_F^{-1}$).
*Proof.* $\int_{\mathbb A^\times}\Phi\,d\mu = \mu^1(D)$ (`lintegral_ideleTest`); the pushforward to the model
(`lintegral_tamIdeles_ideal`), the unfolding and $\sum_\gamma w(\gamma z) = 1$ turn it into
$\int_{I_F/F^\times}\mathbf 1_{(1,e]}(|z|)\,d^\times z = \rho_F\log e$ (`ideleClassLIntegral_indicator_Ioc`, proved with the
fundamental cone, the unit theorem and the class number). -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41 (D = k: vol(I_k^1/k*) = ρ_k); §2.4, Lemma 2.4.1, pp. 25–26"]
theorem muIdeleClass_univ_eq_residue :
    muIdeleClass F univ = ENNReal.ofReal (dedekindZeta_residue F) := by
  rw [muIdeleClass_univ isFundamentalDomain_ideleClassFD, ← lintegral_ideleTest]
  simp_rw [ideleTest_eq]
  rw [lintegral_tamIdeles_ideal _ measurable_ideleTestModel,
    IdeleClass.ideleLIntegral_eq_ideleClassLIntegral F _ measurable_ideleTestModel]
  have h : IdeleClass.ideleClassLIntegral F (fun x 𝔞 => ∑' γ : Fˣ,
      ideleTestModel (IdeleClass.principalSMulInf F γ x) (IdeleClass.principalSMulFin F γ 𝔞)) =
      IdeleClass.ideleClassLIntegral F (fun x 𝔞 => (Ioc 1 (Real.exp 1)).indicator 1 (IdeleClass.ideleNorm F x 𝔞)) := by
    unfold IdeleClass.ideleClassLIntegral
    congr 1
    refine Finset.sum_congr rfl fun c _ => lintegral_congr fun x => ?_
    rcases eq_or_ne (mixedEmbedding.norm x) 0 with hx | hx
    · simp [hx]
    · simp only [ideleTestModel, IdeleClass.ideleNorm_principal]
      rw [ENNReal.tsum_mul_left, tsum_ideleWeight _ hx, mul_one]
  rw [h, IdeleClass.ideleClassLIntegral_indicator_Ioc F one_pos (Real.one_le_exp zero_le_one), div_one,
    Real.log_exp, mul_one]

/-- **The named input `IdeleClassVolumeResidue F` holds for every number field.** -/
theorem idelesClassVolumeResidue : IdeleClassVolumeResidue F := ⟨muIdeleClass_univ_eq_residue⟩

/-- **$\tau(\mathrm{SL}_1(D)) = 1$ for every quaternion division algebra $D = \mathbb H[F,a,b]$ over every number field**
($a, b\in\mathcal O_F\setminus0$, any signature), for Weil's Tamagawa measure $\mu_{\mathrm{SL}_1}$ (`muSL1`),
**unconditionally**:
$$\operatorname{covol}(\mathrm{SL}_1(D)(F)\backslash\mathrm{SL}_1(D)(\mathbb A),\ \mu_{\mathrm{SL}_1}) = 1.$$
`tamagawa_SL1_division` with its input discharged by `idelesClassVolumeResidue`. -/
@[kb "weil1982" "§3.1, Thm 3.1.1 (iii), p. 41 and §3.7 (τ(SL₁(D)) = 1) [unverified page for §3.7]"]
theorem tamagawa_SL1_division_unconditional {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) = 1 :=
  tamagawa_SL1_division ha0 hb0 hdiv idelesClassVolumeResidue

end

end QuadFormsKB.Tamagawa.Measure.Weil
