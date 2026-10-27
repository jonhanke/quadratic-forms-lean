import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerIdele
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerBox
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerLocalFin
import QuadFormsKB.Tamagawa.Measure.Weil.EulerFinsupp
import QuadFormsKB.Tamagawa.SphericalResidue

/-!
# `AdelicSphericalEuler` for the Gaussian test function over a totally real field

$F$ totally real, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1\ge5$ variables, $\rho\in F^\times$, $\sigma$ the
constructed measure on the adelic sphere $T(\rho)_{\mathbb A}$ (`sphereMeasure`), $\Phi$ = `gaussTest`, $a = N + 2s$,
$s > 0$. **`lintegral_mellinPhi_gaussTest`**:
$$Z(s,\rho) = \int_{T(\rho)_{\mathbb A}}M_s\Phi\,d\sigma = |d_F|^{-N/2}\prod_wZ_w(s,\rho)\prod_\mathfrak pZ_\mathfrak p(s,\rho)
= \texttt{sphericalZetaAt}\ Q_0\ G\ \rho\ s,$$
i.e. `AdelicSphericalEuler` with $\kappa = 1$ and $\Phi_w = G$ the standard Gaussian (**`adelicSphericalEuler_gaussTest`**).

*Proof.* (1) $M_s\Phi(y) = |d_F|^{-1/2}\prod_wM_a(y_w)\sum_e\mathrm{finWeight}(y,e)$ (`mellinPhi_gaussTest`); (2) Tonelli and
The box formula with the free places $\operatorname{supp}e$ (`lintegral_boxG_prod`): the $e$-term is
$|d_F|^{-(N-1)/2}\prod'_va_v(e_v)\prod_w\int M_a\,d\sigma_w$, $a_v(j) = q_v^{-ja}\sigma_v(T_v\cap\mathfrak p^{-j}L_v)$;
(3) the Euler factorisation `tsum_finsupp_ofReal_tprod`; (4) the local identities `hasSum_sphLat` (finite) and
`lintegral_archMellin_sigR` (real); (5) the product formula for $|2\rho|\,|\rho|^s$.
-/

open MeasureTheory Set Filter WithZero
open scoped ENNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

namespace AdelicSphereSetup

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

/-- **The product function on a box**: $\prod_wM_a(y_w)\cdot\mathrm{finWeight}_a(y,e)$ is
$\prod_{v}q_v^{-e_va}$ times the indicator of the box $\prod_v(T_v\cap\mathfrak p^{-e_v}L_v)$. -/
theorem archMellin_mul_finWeight (a : ℝ) (y : adelicSphere Q₀ ρ) (e : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    (∏ w, archMellin a (adR y.1 w)) * finWeight a y.1 e =
      ENNReal.ofReal (∏ v ∈ e.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(e v : ℝ) * a)) *
        (boxG Q₀ ρ (fun _ => univ) fun v => sphLat Q₀ ρ v (e v)).indicator
          (fun y => ∏ w, archMellin a (projR Q₀ ρ y w : Fin (k + 1) → ℝ)) y := by
  by_cases h : ∀ v i, Valued.v (adV y.1 v i) ≤ exp (e v)
  · have hb : y ∈ boxG Q₀ ρ (fun _ => univ) fun v => sphLat Q₀ ρ v (e v) := ⟨fun _ => trivial, fun v => h v⟩
    rw [finWeight, indicator_of_mem (show y.1 ∈ {y : AdeleSpace F (Fin (k + 1)) |
      ∀ v i, Valued.v (adV y v i) ≤ exp (e v)} from h), indicator_of_mem hb, Pi.one_apply, mul_one, mul_comm]
    rfl
  · have hb : y ∉ boxG Q₀ ρ (fun _ => univ) fun v => sphLat Q₀ ρ v (e v) := fun hb => h fun v => hb.2 v
    rw [finWeight, indicator_of_notMem (show y.1 ∉ {y : AdeleSpace F (Fin (k + 1)) |
      ∀ v i, Valued.v (adV y v i) ≤ exp (e v)} from h), indicator_of_notMem hb]
    simp

end AdelicSphereSetup

/-- A real product modified at finitely many places, where the old factors are nonzero, stays multipliable. -/
theorem multipliable_of_eq_off {ι : Type*} [DecidableEq ι] {f g : ι → ℝ} (hg : Multipliable g) (T : Finset ι)
    (hT : ∀ v ∈ T, g v ≠ 0) (hfg : ∀ v ∉ T, f v = g v) : Multipliable f := by
  set c : ι → ℝ := fun v => if v ∈ T then f v / g v else 1
  have hc : Multipliable c := multipliable_of_ne_finset_one (s := T) fun v hv => by simp [c, hv]
  convert hg.mul hc using 1
  funext v
  by_cases hv : v ∈ T
  · simp [c, hv, mul_div_cancel₀ _ (hT v hv)]
  · simp [c, hv, hfg v hv]

/-- A finitely supported real product: $\prod'_vf_v = \prod_{v\in T}f_v$ and it is multipliable. -/
theorem hasProd_of_one_off {ι : Type*} {f : ι → ℝ} (T : Finset ι) (hf : ∀ v ∉ T, f v = 1) :
    HasProd f (∏ v ∈ T, f v) :=
  hasProd_prod_of_ne_finset_one hf

namespace AdelicSphereSetup

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

/-- **The product formula for $|2\rho|\,|\rho|^s$**:
$\prod_w|2\rho|_w|\rho|_w^s\cdot\prod_v|2\rho|_v|\rho|_v^s = 1$ ($\rho\in F^\times$). -/
theorem prod_formula_two_rho (hρ : ρ ≠ 0) (s : ℝ) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w (2 * ρ)| * |σR w ρ| ^ s)) *
      ∏' v : HeightOneSpectrum (𝓞 F), (‖σV v (2 * ρ)‖ * ‖σV v ρ‖ ^ s) = 1 := by
  classical
  have h2 : (2 : F) * ρ ≠ 0 := mul_ne_zero two_ne_zero hρ
  set T := (mulSupport_finite_norm h2).toFinset ∪ (mulSupport_finite_norm hρ).toFinset
  have e1 : ∀ x : F, x ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖σV v x‖) ⊆ T →
      ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v x‖ = ∏ v ∈ T, ‖σV v x‖ := fun x _ hx =>
    tprod_eq_prod fun v hv => by
      by_contra h'; exact hv (Finset.mem_coe.mp (hx h'))
  have hT2 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖σV v (2 * ρ)‖) ⊆ T := fun v hv =>
    Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr hv)
  have hT1 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖σV v ρ‖) ⊆ T := fun v hv =>
    Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hv)
  have p2 := prod_real_mul_tprod h2
  have p1 := prod_real_mul_tprod hρ
  rw [e1 _ h2 hT2] at p2
  rw [e1 _ hρ hT1] at p1
  have hprod : ∏' v : HeightOneSpectrum (𝓞 F), (‖σV v (2 * ρ)‖ * ‖σV v ρ‖ ^ s) =
      ∏ v ∈ T, (‖σV v (2 * ρ)‖ * ‖σV v ρ‖ ^ s) := tprod_eq_prod fun v hv => by
    have a2 : ‖σV v (2 * ρ)‖ = 1 := by
      by_contra h'; exact hv (hT2 h')
    have a1 : ‖σV v ρ‖ = 1 := by
      by_contra h'; exact hv (hT1 h')
    rw [a2, a1, Real.one_rpow, mul_one]
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Real.finsetProd_rpow _ _ fun w _ => abs_nonneg _, Real.finsetProd_rpow _ _ fun v _ => norm_nonneg _]
  calc (∏ w, |σR w (2 * ρ)|) * (∏ w, |σR w ρ|) ^ s * ((∏ v ∈ T, ‖σV v (2 * ρ)‖) * (∏ v ∈ T, ‖σV v ρ‖) ^ s)
      = ((∏ w, |σR w (2 * ρ)|) * ∏ v ∈ T, ‖σV v (2 * ρ)‖) *
          ((∏ w, |σR w ρ|) ^ s * (∏ v ∈ T, ‖σV v ρ‖) ^ s) := by ring
    _ = 1 := by
      rw [← Real.mul_rpow (Finset.prod_nonneg fun w _ => abs_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _),
        p2, p1, Real.one_rpow, mul_one]

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)

open Classical in
/-- **The adelic spherical integral of the Gaussian is Weil's Euler product** (totally real $F$, $N = k+1\ge5$, $s>0$):
$\int_{T(\rho)_{\mathbb A}}M_s\Phi\,d\sigma = $ `sphericalZetaAt Q₀ G ρ s`. -/
theorem lintegral_mellinPhi_gaussTest [IsTotallyReal F] (hk4 : 4 ≤ k) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, mellinPhi (gaussTest F (k + 1)) s y.1 ∂S.sphereMeasure hρ hQ hk =
      ENNReal.ofReal (SphericalZeta.sphericalZetaAt Q₀ (fun _ => gaussFn) ρ s) := by
  set a : ℝ := ((k + 1 : ℕ) : ℝ) + 2 * s with ha
  set σ := S.sphereMeasure hρ hQ hk with hσ
  set q : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ) with hqdef
  have hq : ∀ v, 0 < q v := fun v => zero_lt_one.trans (one_lt_absNorm v)
  set A : HeightOneSpectrum (𝓞 F) → ℤ → ℝ := fun v j =>
    q v ^ (-(j : ℝ) * a) * (sigV Q₀ ρ hQ v (sphLat Q₀ ρ v j)).toReal with hAdef
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v (2 * ρ)‖ * ‖σV v ρ‖ ^ s with hgdef
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v => SphericalZeta.sphLocal Q₀ v (σV v ρ) s / g v with hEdef
  have hA : ∀ v, HasSum (A v) (E v) := fun v => hasSum_sphLat v hQ hρ hs.le
  have hA0 : ∀ v j, 0 ≤ A v j := fun v j => mul_nonneg (Real.rpow_nonneg (hq v).le _) ENNReal.toReal_nonneg
  have hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤ := fun v => by
    rw [← sphLat_zero]; exact sigV_sphLat_ne_top v hQ hρ 0
  have hAzero : ∀ v, A v 0 = (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal := fun v => by
    simp only [hAdef, Int.cast_zero, neg_zero, zero_mul, Real.rpow_zero, one_mul, sphLat_zero]
  obtain ⟨S₀, hS₀, hPm, hP0⟩ := S.exists_hasProd_sigV_intSph hρ hQ hk hfin
  -- the archimedean constant
  set K : ℝ≥0∞ := ∏ w, ∫⁻ x, archMellin a (x : Fin (k + 1) → ℝ) ∂sig (QRe Q₀ w) (σR w ρ) with hK
  set r : {w : InfinitePlace F // w.IsReal} → ℝ := fun w =>
    SphericalZeta.sphArchAt Q₀ w gaussFn (Siegel.realEmb w ρ) s / (|σR w (2 * ρ)| * |σR w ρ| ^ s) with hrdef
  have hr0 : ∀ w, 0 ≤ r w := fun w => div_nonneg (mul_nonneg zero_le_two (integral_nonneg fun x =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)) (by positivity)
  have hKr : K = ENNReal.ofReal (∏ w, r w) := by
    rw [hK, ENNReal.ofReal_prod_of_nonneg fun w _ => hr0 w]
    exact Finset.prod_congr rfl fun w _ => lintegral_archMellin_sigR Q₀ w hρ hs.le
  -- step 1: the pointwise decomposition
  set Nw : (HeightOneSpectrum (𝓞 F) →₀ ℤ) → ℝ := fun e => ∏ v ∈ e.support, q v ^ (-(e v : ℝ) * a) with hNw
  set box : (HeightOneSpectrum (𝓞 F) →₀ ℤ) → Set (adelicSphere Q₀ ρ) := fun e =>
    boxG Q₀ ρ (fun _ => univ) fun v => sphLat Q₀ ρ v (e v) with hbox
  set fR : adelicSphere Q₀ ρ → ℝ≥0∞ := fun y => ∏ w, archMellin a (projR Q₀ ρ y w : Fin (k + 1) → ℝ) with hfR
  have hfRm : Measurable fR := Finset.measurable_prod _ fun w _ =>
    (measurable_archMellin a).comp (measurable_subtype_coe.comp ((measurable_pi_apply w).comp measurable_projR))
  have h1 : ∀ y : adelicSphere Q₀ ρ, mellinPhi (gaussTest F (k + 1)) s y.1 =
      ENNReal.ofReal (IdeleClass.ideleConst F) * ∑' e, ENNReal.ofReal (Nw e) * (box e).indicator fR y := fun y => by
    rw [mellinPhi_gaussTest, mul_assoc, ← ENNReal.tsum_mul_left]
    congr 1
    exact tsum_congr fun e => archMellin_mul_finWeight a y e
  -- step 2: each term by the box formula
  have hterm : ∀ e, ∫⁻ y, ENNReal.ofReal (Nw e) * (box e).indicator fR y ∂σ =
      ENNReal.ofReal (Nw e) * (ENNReal.ofReal (cF F (k + 1) / cF F k *
        ∏' v, (sigV Q₀ ρ hQ v (sphLat Q₀ ρ v (e v))).toReal) * K) := fun e => by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact S.lintegral_boxG_prod hρ hQ hk e.support (fun v => sphLat Q₀ ρ v (e v))
      (fun v => measurableSet_sphLat Q₀ ρ v _)
      (fun v hv => by rw [Finsupp.notMem_support_iff.mp hv, sphLat_zero])
      (fun v => sigV_sphLat_ne_top v hQ hρ _) hfin (fun w x => archMellin a (x : Fin (k + 1) → ℝ))
      (fun w => (measurable_archMellin a).comp measurable_subtype_coe)
  have hmeas : ∀ e, AEMeasurable (fun y => ENNReal.ofReal (Nw e) * (box e).indicator fR y) σ := fun e =>
    ((hfRm.indicator (measurableSet_boxG _ (fun _ => MeasurableSet.univ) _
      fun v => measurableSet_sphLat Q₀ ρ v _)).const_mul _).aemeasurable
  rw [lintegral_congr h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeas]
  simp_rw [hterm]
  -- step 3: the e-terms are Euler products
  set g0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if v ∈ S₀ then 1 else A v 0 with hg0
  have hg0m : Multipliable g0 := by simpa only [hg0, hAzero] using hPm
  have hg0ne : ∀ v, g0 v ≠ 0 := fun v => by
    by_cases hv : v ∈ S₀
    · simp [hg0, hv]
    · simp only [hg0, hv, ite_false, hAzero]; exact hS₀ v hv
  have hsig : ∀ e : HeightOneSpectrum (𝓞 F) →₀ ℤ,
      Multipliable fun v => (sigV Q₀ ρ hQ v (sphLat Q₀ ρ v (e v))).toReal := fun e => by
    refine multipliable_of_eq_off hg0m (S₀ ∪ e.support) (fun v _ => hg0ne v) fun v hv => ?_
    have hv1 : v ∉ S₀ := fun h => hv (Finset.mem_union_left _ h)
    have hv2 : e v = 0 := Finsupp.notMem_support_iff.mp fun h => hv (Finset.mem_union_right _ h)
    simp only [hg0, hv1, ite_false, hAzero, hv2, sphLat_zero]
  have hEuler : ∀ e : HeightOneSpectrum (𝓞 F) →₀ ℤ,
      Nw e * ∏' v, (sigV Q₀ ρ hQ v (sphLat Q₀ ρ v (e v))).toReal = ∏' v, A v (e v) := fun e => by
    have hqp : HasProd (fun v => q v ^ (-(e v : ℝ) * a)) (Nw e) :=
      hasProd_of_one_off e.support fun v hv => by
        rw [Finsupp.notMem_support_iff.mp hv, Int.cast_zero, neg_zero, zero_mul, Real.rpow_zero]
    rw [← hqp.tprod_eq, ← hqp.multipliable.tprod_mul (hsig e)]
  have hterm' : ∀ e : HeightOneSpectrum (𝓞 F) →₀ ℤ, ENNReal.ofReal (Nw e) * (ENNReal.ofReal (cF F (k + 1) / cF F k *
      ∏' v, (sigV Q₀ ρ hQ v (sphLat Q₀ ρ v (e v))).toReal) * K) =
      ENNReal.ofReal (cF F (k + 1) / cF F k) * K * ENNReal.ofReal (∏' v, A v (e v)) := fun e => by
    have hN0 : 0 ≤ Nw e := Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hq v).le _
    have hc0 : 0 ≤ cF F (k + 1) / cF F k := div_nonneg cF_nonneg cF_nonneg
    rw [← hEuler e, ENNReal.ofReal_mul hN0, ENNReal.ofReal_mul hc0]
    ring
  simp_rw [hterm']
  rw [ENNReal.tsum_mul_left]
  -- step 4: the Euler factorisation
  have hgfin : HasProd g (∏ v ∈ ((mulSupport_finite_norm (mul_ne_zero (two_ne_zero (α := F)) hρ)).toFinset ∪
      (mulSupport_finite_norm hρ).toFinset), g v) := hasProd_of_one_off _ fun v hv => by
    have a2 : ‖σV v (2 * ρ)‖ = 1 := by
      by_contra h'; exact hv (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h'))
    have a1 : ‖σV v ρ‖ = 1 := by
      by_contra h'; exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h'))
    simp only [hgdef, a2, a1, Real.one_rpow, mul_one]
  have hgpos : ∀ v, 0 < g v := fun v => mul_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr
    (mul_ne_zero two_ne_zero hρ))) (Real.rpow_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr hρ)) _)
  have hGne : (∏' v, g v) ≠ 0 := by
    rw [hgfin.tprod_eq]; exact (Finset.prod_pos fun v _ => hgpos v).ne'
  have hloc : HasProd (fun v => SphericalZeta.sphLocal Q₀ v (σV v ρ) s)
      (∏' v, SphericalZeta.sphLocal Q₀ v (σV v ρ) s) :=
    (SphericalZeta.multipliable_zf hQ (by omega) (Units.mk0 ρ hρ) hs.le).hasProd
  have hEprod : HasProd E ((∏' v, SphericalZeta.sphLocal Q₀ v (σV v ρ) s) / ∏' v, g v) := by
    unfold HasProd
    refine (Filter.Tendsto.div hloc hgfin.multipliable.hasProd hGne).congr fun T => ?_
    simp only [Pi.div_apply, hEdef, Finset.prod_div_distrib]
  have hEuler2 := tsum_finsupp_ofReal_tprod A hA0 (fun v => (hA v).summable) S₀
    (fun v hv => by rw [hAzero]; exact hS₀ v hv) hg0m (by simpa only [hAzero] using hP0)
    (by simpa only [fun v => (hA v).tsum_eq] using hEprod.multipliable)
  rw [hEuler2]
  simp only [fun v => (hA v).tsum_eq]
  rw [hEprod.tprod_eq, hKr]
  -- step 5: the constants
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hc0 : 0 ≤ IdeleClass.ideleConst F := by
    rw [IdeleClass.ideleConst]; positivity
  have hc1 : 0 ≤ cF F (k + 1) / cF F k := div_nonneg cF_nonneg cF_nonneg
  have hR : 0 ≤ ∏ w, r w := Finset.prod_nonneg fun w _ => hr0 w
  rw [← ENNReal.ofReal_mul hc1, ← ENNReal.ofReal_mul (mul_nonneg hc1 hR), ← ENNReal.ofReal_mul hc0]
  congr 1
  have hconst : IdeleClass.ideleConst F * (cF F (k + 1) / cF F k) =
      |(NumberField.discr F : ℝ)| ^ (-((k + 1 : ℕ) : ℝ) / 2) := by
    rw [IdeleClass.ideleConst, show NumberField.InfinitePlace.nrComplexPlaces F = 0 from Fintype.card_eq_zero,
      pow_zero, mul_one, Indefinite.cF_succ_eq, mul_div_assoc, div_self cF_pos'.ne', mul_one, ← Real.rpow_add hd]
    congr 1; push_cast; ring
  have hpf := prod_formula_two_rho hρ s
  set D := ∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w (2 * ρ)| * |σR w ρ| ^ s) with hDdef
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero
    (abs_ne_zero.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ)))
    (Real.rpow_pos_of_pos (abs_pos.mpr ((map_ne_zero _).mpr hρ)) _).ne'
  have hG : ∏' v, g v = D⁻¹ := eq_inv_of_mul_eq_one_right hpf
  have hrP : ∏ w, r w = (∏ w, SphericalZeta.sphArchAt Q₀ w gaussFn (Siegel.realEmb w ρ) s) / D := by
    rw [hrdef, Finset.prod_div_distrib]
  rw [hrP, hG, SphericalZeta.sphericalZetaAt, ← hconst]
  field_simp

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
