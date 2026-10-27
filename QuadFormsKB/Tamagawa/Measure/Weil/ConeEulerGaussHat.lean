import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerGauss

/-!
# `AdelicConeEuler` for the Fourier transform of the Gaussian

$\hat\Phi$ = `gaussTestHat Q₀` is $\mu_f(\hat{\mathcal O}^n)\cdot\mathbf 1_{\hat{\mathfrak d}^{-1,n}}(Hx)_f\cdot G(Hx)_\infty$
($H$ the Hessian). Over a totally real field it factors as
$$\hat\Phi(x) = \mu_f(\hat{\mathcal O}^n)\,\mathbf 1\{x_v\in K_v\ \forall v\}\prod_we^{-\pi|H_wx_w|^2},\qquad
  K_v = \{z : H_vz\in\mathfrak d_v^{-1,n}\}$$
(`gaussTestHat_apply`). Each $K_v$ is measurable and bounded, and $K_v = L_v$ when $H_v, H_v^{-1}$ are integral and
$\mathfrak d_v = 1$, i.e. for all but finitely many $v$ (`eventually_KH_eq_latL`). The archimedean factors are
Gaussian-bounded through $H_w^{-1}$ (`exists_gaussRe_mulVec_le`). Then `lintegral_coneMeasure_prod` and
`adelicConeEuler_of_prod` give **`adelicConeEuler_gaussTestHat`**.
-/

open MeasureTheory Set Matrix Filter Topology
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra QuadFormsKB.Tamagawa.Measure.LerayReal

/-- **A Gaussian through an invertible matrix is Gaussian-bounded**: $e^{-\pi|Mz|^2}\le e^{-a\|z\|^2}$ for some
$a>0$. -/
theorem exists_gaussRe_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ z, gaussRe (M *ᵥ z) ≤ ENNReal.ofReal (Real.exp (-(a * ‖z‖ ^ 2))) := by
  set f := LinearMap.toContinuousLinearMap (Matrix.toLin' M⁻¹)
  set C := ‖f‖ + 1
  have hC : 0 < C := by positivity
  have hz : ∀ z, ‖z‖ ≤ C * ‖M *ᵥ z‖ := fun z => by
    have h1 : f (M *ᵥ z) = z := by
      simp only [f, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (Ne.isUnit hM), Matrix.one_mulVec]
    calc ‖z‖ = ‖f (M *ᵥ z)‖ := by rw [h1]
      _ ≤ ‖f‖ * ‖M *ᵥ z‖ := f.le_opNorm _
      _ ≤ C * ‖M *ᵥ z‖ := mul_le_mul_of_nonneg_right (by simp [C]) (norm_nonneg _)
  refine ⟨Real.pi / C ^ 2, by positivity, fun z => (gaussRe_le _).trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr ?_))⟩
  have h2 : ‖z‖ ^ 2 ≤ C ^ 2 * ‖M *ᵥ z‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hz z) 2
  have h3 : Real.pi / C ^ 2 * ‖z‖ ^ 2 ≤ Real.pi * ‖M *ᵥ z‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  linarith

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

section Generic

variable {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem hessA_map_projR' (w : {w : InfinitePlace F // w.IsReal}) :
    (hessA Q₀).map (adProjR F w) = hesAt Q₀ (σR w) := by
  rw [hessA, Matrix.map_map, ← RingHom.coe_comp, adProjR_diagRing]

theorem hessA_map_projV' (v : HeightOneSpectrum (𝓞 F)) :
    (hessA Q₀).map (adProjV F v) = hesAt Q₀ (σV v) := by
  rw [hessA, Matrix.map_map, ← RingHom.coe_comp, adProjV_diagRing]

theorem adR_mulVec' (M : Matrix (Fin n) (Fin n) (Adeles F)) (y : AdeleSpace F (Fin n))
    (w : {w : InfinitePlace F // w.IsReal}) : adR (M *ᵥ y) w = M.map (adProjR F w) *ᵥ adR y w :=
  funext fun i => RingHom.map_mulVec (adProjR F w) M y i

theorem adV_mulVec' (M : Matrix (Fin n) (Fin n) (Adeles F)) (y : AdeleSpace F (Fin n)) (v : HeightOneSpectrum (𝓞 F)) :
    adV (M *ᵥ y) v = M.map (adProjV F v) *ᵥ adV y v :=
  funext fun i => RingHom.map_mulVec (adProjV F v) M y i

/-- $\mathfrak d_v^{-1,n}$. -/
def DV (v : HeightOneSpectrum (𝓞 F)) : Set (Fin n → v.adicCompletion F) :=
  univ.pi fun _ => (Analysis.latticeV v (-(Analysis.diffExp v : ℤ)) : Set (v.adicCompletion F))

theorem mem_DV_iff (v : HeightOneSpectrum (𝓞 F)) (u : Fin n → v.adicCompletion F) :
    u ∈ DV v ↔ ∀ i, Valued.v (u i) ≤ WithZero.exp (Analysis.diffExp v : ℤ) := by
  simp only [DV, mem_univ_pi, SetLike.mem_coe, Analysis.mem_latticeV, neg_neg]

theorem isCompact_DV (v : HeightOneSpectrum (𝓞 F)) : IsCompact (DV (n := n) v) :=
  isCompact_univ_pi fun _ => Analysis.isCompact_latticeV v _

/-- $K_v = \{z : H_vz\in\mathfrak d_v^{-1,n}\}$. -/
def KH (v : HeightOneSpectrum (𝓞 F)) : Set (Fin n → v.adicCompletion F) :=
  (fun z => hesAt Q₀ (σV v) *ᵥ z) ⁻¹' DV v

theorem measurableSet_KH (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (KH Q₀ v) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    (MeasurableSet.univ_pi fun _ => Analysis.measurableSet_latticeV v _)

/-- $(H^{-1})_v H_v = 1$. -/
theorem hesAt_inv_mul (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    ((QF).hessian⁻¹).map (σV v) * hesAt Q₀ (σV v) = 1 := by
  rw [hesAt, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit (hessF_det_ne_zero hQ)), Matrix.map_one _ (map_zero _)
    (map_one _)]

theorem isBounded_KH (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    Bornology.IsBounded (KH Q₀ v) := by
  refine (((isCompact_DV v).image (Continuous.matrix_mulVec (continuous_const (y := ((QF).hessian⁻¹).map (σV v)))
    continuous_id)).isBounded).subset fun z hz => ⟨_, hz, ?_⟩
  simp only [id, Matrix.mulVec_mulVec, hesAt_inv_mul Q₀ hQ v, Matrix.one_mulVec]

/-- **$K_v = L_v$** when $H_v$, $H_v^{-1}$ are integral and $\mathfrak d_v = 1$. -/
theorem KH_eq_latL (hQ : Q₀.Nondegenerate) {v : HeightOneSpectrum (𝓞 F)}
    (h1 : hesAt Q₀ (σV v) ∈ QuadFormsKB.Tamagawa.Measure.intMat v)
    (h2 : ((QF).hessian⁻¹).map (σV v) ∈ QuadFormsKB.Tamagawa.Measure.intMat v) (hd : Analysis.diffExp v = 0) :
    KH Q₀ v = LocalZeta.latL v n := by
  ext z
  have hiff : z ∈ KH Q₀ v ↔ IntVec v (hesAt Q₀ (σV v) *ᵥ z) := by
    simp only [KH, mem_preimage, mem_DV_iff, hd, Nat.cast_zero, WithZero.exp_zero]; rfl
  rw [hiff]
  constructor
  · intro h
    have := IntVec.mulVec v h2 h
    rwa [Matrix.mulVec_mulVec, hesAt_inv_mul Q₀ hQ v, Matrix.one_mulVec] at this
  · exact fun h => IntVec.mulVec v h1 h

theorem eventually_KH_eq_latL (hQ : Q₀.Nondegenerate) :
    ∀ᶠ v in Filter.cofinite, KH Q₀ v = LocalZeta.latL v n := by
  have hd : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Analysis.diffExp v = 0 := by
    filter_upwards [(Analysis.finite_support_diffExp (F := F)).eventually_cofinite_notMem] with v hv
    simpa [Function.mem_support] using hv
  filter_upwards [eventually_map_mem_intMat (QF).hessian, eventually_map_mem_intMat (QF).hessian⁻¹, hd]
    with v h1 h2 h3
  exact KH_eq_latL Q₀ hQ h1 h2 h3

open Classical in
/-- **$\hat\Phi$ over a totally real field**: $\hat\Phi(y) = \mu_f(\hat{\mathcal O}^n)\,\mathbf 1\{y_v\in K_v\ \forall v\}
\prod_we^{-\pi|H_wy_w|^2}$. -/
theorem gaussTestHat_apply [IsEmpty {w : InfinitePlace F // w.IsComplex}] (y : AdeleSpace F (Fin n)) :
    gaussTestHat Q₀ y = muFinVec F (Fin n) OHatVec *
      {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v}.indicator
        (fun y => ∏ w, gaussRe (hesAt Q₀ (σR w) *ᵥ adR y w)) y := by
  classical
  rw [gaussTestHat, gaussDualTest, ofReal_gV_fst]
  simp only [adR_mulVec', hessA_map_projR']
  have hiff : (fun i => (hessA Q₀ *ᵥ y) i |>.2) ∈ {c : Fin n → AF | ∀ i, c i ∈ DHat} ↔ ∀ v, adV y v ∈ KH Q₀ v := by
    have : ∀ v, adV y v ∈ KH Q₀ v ↔ adV (hessA Q₀ *ᵥ y) v ∈ DV v := fun v => by
      rw [adV_mulVec', hessA_map_projV']; rfl
    simp only [this, mem_DV_iff, mem_setOf_eq, DHat]
    exact forall_comm
  by_cases h : ∀ v, adV y v ∈ KH Q₀ v
  · rw [indicator_of_mem (hiff.mpr h), indicator_of_mem (show y ∈ {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v}
      from h), one_mul]
  · rw [indicator_of_notMem (fun h' => h (hiff.mp h')),
      indicator_of_notMem (show y ∉ {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v} from h), zero_mul, mul_zero]

end Generic

/-! ### The cone form -/

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

open Classical in
/-- The finite places excluded for $\hat\Phi$: `badCone` and the places with $K_v\ne L_v$. -/
def badHat : Finset (HeightOneSpectrum (𝓞 F)) :=
  badCone hc hQ' hk ∪ (Filter.eventually_cofinite.mp (eventually_KH_eq_latL QC (nondeg_QC hc hQ'))).toFinset

open Classical in
theorem KH_eq_latL_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badHat hc hQ' hk) :
    KH QC v = LocalZeta.latL v (k + 1 + 1) := by
  by_contra h
  exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))

section Euler

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

open Classical in
theorem gaussTestHat_cone (x : adelicCone QC) :
    gaussTestHat QC x.1 = muFinVec F (Fin (k + 1 + 1)) OHatVec *
      (Yset (badHat hc hQ' hk) (KH QC)).indicator
        (fun x => ∏ w, gaussRe (hesAt QC (σR w) *ᵥ (coneRpt x w).1)) x := by
  have hY : x ∈ Yset (badHat hc hQ' hk) (KH QC) ↔ ∀ v, adV x.1 v ∈ KH QC v := by
    simp only [Yset, mem_setOf_eq]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ badHat hc hQ' hk
    · rw [boxSet_of_mem hv]
    · rw [boxSet_of_not_mem hv, KH_eq_latL_of_not_mem hc hQ' hk hv]
  rw [gaussTestHat_apply]
  congr 1
  by_cases h : ∀ v, adV x.1 v ∈ KH QC v
  · rw [indicator_of_mem (show x.1 ∈ {y : AdeleSpace F (Fin (k + 1 + 1)) | ∀ v, adV y v ∈ KH QC v} from h),
      indicator_of_mem (hY.mpr h)]
    rfl
  · rw [indicator_of_notMem (show x.1 ∉ {y : AdeleSpace F (Fin (k + 1 + 1)) | ∀ v, adV y v ∈ KH QC v} from h),
      indicator_of_notMem (fun h' => h (hY.mp h'))]

include hc hQ' in
theorem hesAt_σR_det_ne_zero (w : {w : InfinitePlace F // w.IsReal}) : (hesAt QC (σR w)).det ≠ 0 := by
  have h := gramDetR_QRe_ne_zero QC (nondeg_QC hc hQ') w
  rw [Siegel.gramDetR, div_ne_zero_iff] at h
  rw [hesAt, ← hessian_map']
  exact h.1

/-- **`AdelicConeEuler` for $\hat\Phi$** = `gaussTestHat` ($F$ totally real, $k\ge3$). -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral of the Fourier transform of the Gaussian) [unverified page]"]
theorem adelicConeEuler_gaussTestHat (hQ : (coneFormO c₀ Q₀').Nondegenerate) :
    AdelicConeEuler hc Q₀' hQ (coneData hc hQ' hk).σ (gaussTestHat (coneFormO c₀ Q₀')) := by
  classical
  set S := badHat hc hQ' hk
  have hS : badCone hc hQ' hk ⊆ S := Finset.subset_union_left
  have hμ : muFinVec F (Fin (k + 1 + 1)) OHatVec ≠ ⊤ := fun h => by
    have := muFinVec_OHatVec_toReal_pos (F := F) (n := k + 1 + 1)
    rw [h, ENNReal.toReal_top] at this
    exact lt_irrefl 0 this
  choose a ha hb using fun w => exists_gaussRe_mulVec_le _ (hesAt_σR_det_ne_zero hc hQ' w)
  have hfin : ConeAdelic.boxMass QC hQ S (KH QC) ≠ ⊤ :=
    (ConeAdelic.boxMass_lt_top (Q₀ := QC) (hQ := hQ) (by omega) S _ fun v _ => isBounded_KH QC (nondeg_QC hc hQ') v).ne
  refine adelicConeEuler_of_prod hc hQ' hk hQ (muFinVec F (Fin (k + 1 + 1)) OHatVec * coneConst hc hQ' S)
    (ENNReal.mul_ne_top hμ (coneConst_ne_top hc hQ' hk S hS)) S (KH QC)
    (fun v _ => isBounded_KH QC (nondeg_QC hc hQ') v) (fun w z => gaussRe (hesAt QC (σR w) *ᵥ z.1))
    (fun w => measurable_gaussRe.comp ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp
      measurable_subtype_coe)) a (fun _ => 1) ha (fun _ => zero_le_one)
    (fun w z => by rw [one_mul]; exact hb w z.1) ?_
  show ∫⁻ x, gaussTestHat QC x.1 ∂coneMeasure hc hQ' hk = _
  rw [lintegral_congr fun x => gaussTestHat_cone hc hQ' hk x, lintegral_const_mul' _ _ hμ,
    lintegral_coneMeasure_prod hc hQ' hk S hS (fun v _ => measurableSet_KH QC v) hQ hfin
      (φ := fun w z => gaussRe (hesAt QC (σR w) *ᵥ z.1))
      (fun w => measurable_gaussRe.comp ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp
        measurable_subtype_coe))]
  ring

end Euler

end QuadFormsKB.Tamagawa.Measure.Weil

end
