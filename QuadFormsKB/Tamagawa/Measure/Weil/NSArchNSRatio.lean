import QuadFormsKB.Tamagawa.Measure.Weil.NSArchNSGroup
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchNSChart

/-!
# The local ratio at a real place with $E_w = \mathbb C$

**Layer:** one real place $w$ of $F$ with $d_w < 0$; $A, B$ real, $t\in\mathbb C$ with $t^2 = d$, $\operatorname{Re}t = 0$;
$L_w = S_1(\mathbb C)$ with its Haar measure $\sigma_{\mathbb C}$ (`sigC`), $\varphi = $ `phiNS` $: L_w\to SO(Q_0)(\mathbb R)$.

* `secNS`: a measurable section of the orbit map $SO(Q_0)\to\{Q_0 = 1\}$ equal to $y\mapsto\varphi(X(y))$ on $\{y_0>-1\}$
  ($X(y)$ the Cayley point).
* `phiNS_image_ysNS`: $\varphi(Y_\delta)$ is the orbit box of `secNS` over $\mathrm{grBall}_\delta\times c(\mathrm{cayBall}_\delta)$,
  and $\varphi$ is injective on $Y_\delta$ (`injOn_phiNS_ysNS`).
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix Complex
open scoped ENNReal NNReal Quaternion ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Siegel QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  SphereLeray SphereLerayC QuadFormsKB.Tamagawa.Measure.Leray QuadFormsKB.Tamagawa.Measure.OrbitalReal

variable {A B d : ℝ} {t : ℂ} (ht : t ^ 2 = (d : ℂ)) (htre : t.re = 0) (ht0 : t ≠ 0)

local notation "LC" => SphC (normForm (A : ℂ) (B : ℂ)) 1
local notation "Q0" => nsFormR A B d

/-! ### The section -/

/-- **A measurable section** of the orbit map, equal to $y\mapsto\varphi(X(y))$ where $y_0>-1$. -/
def secNS (hQ' : gramDetR (pureFormD A B d) ≠ 0) (y : Sph Q0 1) : ArchSO Q0 :=
  if hy : 0 < 1 + (y : Fin 4 → ℝ) 0 then phiNS ht htre ht0 (sNS ht y hy)
  else (sphSection one_ne_zero (by norm_num) hQ').toFun y

theorem secNS_spec (hQ' : gramDetR (pureFormD A B d) ≠ 0) (y : Sph Q0 1) :
    ArchSOInst.mat _ (secNS ht htre ht0 hQ' y) *ᵥ (e₀ : Fin 4 → ℝ) = (y : Fin 4 → ℝ) := by
  unfold secNS
  split_ifs with hy
  · exact phiNS_sNS_e0 ht htre ht0 y hy
  · exact (sphSection one_ne_zero (by norm_num) hQ').spec y

theorem continuous_cayX_vec : ContinuousOn (fun y : Fin 4 → ℝ => qVec (cayX (A := A) (B := B) t y))
    {y | 0 < 1 + y 0} := by
  have hr : ContinuousOn (fun y : Fin 4 → ℝ => (2 * (1 + y 0)) ^ (-(1 / 2 : ℝ))) {y | 0 < 1 + y 0} :=
    ContinuousOn.rpow_const (by fun_prop) fun y hy => Or.inl (by
      have : 0 < 1 + y 0 := hy
      positivity)
  refine continuousOn_pi.2 fun i => ?_
  have hc : ContinuousOn (fun y : Fin 4 → ℝ => (((2 * (1 + y 0)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) {y | 0 < 1 + y 0} :=
    Complex.continuous_ofReal.comp_continuousOn hr
  fin_cases i <;> simp only [qVec, cayX, yQ, tMatN_mulVec, vecQ, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
    QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one,
    QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val] <;>
    exact hc.mul (by fun_prop)

theorem measurable_secNS (hQ' : gramDetR (pureFormD A B d) ≠ 0) : Measurable (secNS (A := A) (B := B) ht htre ht0 hQ') := by
  have hs : MeasurableSet {y : Sph Q0 1 | 0 < 1 + (y : Fin 4 → ℝ) 0} :=
    (isOpen_lt continuous_const (continuous_const.add ((continuous_apply 0).comp continuous_subtype_val))).measurableSet
  have hf : Measurable fun y : {y : Sph Q0 1 | 0 < 1 + (y : Fin 4 → ℝ) 0} => phiNS ht htre ht0 (sNS ht y.1 y.2) := by
    refine Continuous.measurable ?_
    refine (continuous_phiNS ht htre ht0).comp ?_
    refine Continuous.subtype_mk ?_ _
    exact (continuous_cayX_vec (A := A) (B := B) (t := t)).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)
  have hg : Measurable fun y : ({y : Sph Q0 1 | 0 < 1 + (y : Fin 4 → ℝ) 0}ᶜ : Set (Sph Q0 1)) =>
      (sphSection one_ne_zero (by norm_num) hQ').toFun y.1 :=
    (sphSection one_ne_zero (by norm_num) hQ').measurable.comp measurable_subtype_coe
  classical
  have := Measurable.dite hf hg hs
  convert this using 1
  funext y
  by_cases hy : 0 < 1 + (y : Fin 4 → ℝ) 0
  · simp [secNS, hy]
  · simp [secNS, hy]

/-! ### The image of the test set -/

theorem secNS_of_pos (hQ' : gramDetR (pureFormD A B d) ≠ 0) {y : Sph Q0 1} (hy : 0 < 1 + (y : Fin 4 → ℝ) 0) :
    secNS ht htre ht0 hQ' y = phiNS ht htre ht0 (sNS ht y hy) := dif_pos hy

theorem pos_of_mem_grBall {δ : ℝ} {y : Sph Q0 1} (hy : y ∈ grBall A B d δ) : 0 < 1 + (y : Fin 4 → ℝ) 0 := by
  have := hy.1; linarith

theorem phiNS_decomp (hd0 : d ≠ 0) (hQ' : gramDetR (pureFormD A B d) ≠ 0) {y : Sph Q0 1}
    (hy : 0 < 1 + (y : Fin 4 → ℝ) 0) (h : Sph (normForm A B) 1) :
    phiNS ht htre ht0 (sNS0 ht y * realS h) =
      secNS ht htre ht0 hQ' y * iota 1 (pureFormD A B d) (cS hd0 (conjS h)) := by
  rw [map_mul, sNS0_of_pos ht hy, phiNS_realS ht htre ht0 hd0, secNS_of_pos ht htre ht0 hQ' hy]

theorem phiNS_image_ysNS (hd0 : d ≠ 0) (hQ' : gramDetR (pureFormD A B d) ≠ 0) (δ : ℝ) :
    phiNS ht htre ht0 '' ysNS ht δ =
      (fun q : Sph Q0 1 × ArchSO (pureFormD A B d) => secNS ht htre ht0 hQ' q.1 * iota 1 (pureFormD A B d) q.2) ''
        (grBall A B d δ ×ˢ (cS hd0 '' (conjS '' cayBall A B δ))) := by
  ext g
  constructor
  · rintro ⟨_, ⟨⟨y, h⟩, ⟨hy, hh⟩, rfl⟩, rfl⟩
    exact ⟨(y, cS hd0 (conjS h)), ⟨hy, ⟨conjS h, ⟨h, hh, rfl⟩, rfl⟩⟩,
      (phiNS_decomp ht htre ht0 hd0 hQ' (pos_of_mem_grBall hy) h).symm⟩
  · rintro ⟨⟨y, _⟩, ⟨hy, ⟨_, ⟨h, hh, rfl⟩, rfl⟩⟩, rfl⟩
    exact ⟨sNS0 ht y * realS h, ⟨(y, h), ⟨hy, hh⟩, rfl⟩, phiNS_decomp ht htre ht0 hd0 hQ' (pos_of_mem_grBall hy) h⟩

theorem iota_cS_injective (hd0 : d ≠ 0) :
    Function.Injective fun g : ArchSO (pureForm A B) => iota 1 (pureFormD A B d) (cS hd0 g) := by
  intro g g' h
  apply (cS (A := A) (B := B) hd0).injective
  apply Subtype.ext; apply Units.ext
  have := congrArg (ArchSOInst.mat _) h
  simp only [mat_iota] at this
  exact cornerMat_one_injective this

theorem injOn_phiNS_ysNS (hA : A ≠ 0) (hd0 : d ≠ 0) (hQ' : gramDetR (pureFormD A B d) ≠ 0) (δ : ℝ) :
    InjOn (phiNS ht htre ht0) (ysNS (A := A) (B := B) ht δ) := by
  rintro _ ⟨⟨y, h⟩, ⟨hy, hh⟩, rfl⟩ _ ⟨⟨y', h'⟩, ⟨hy', hh'⟩, rfl⟩ heq
  simp only at heq ⊢
  rw [phiNS_decomp ht htre ht0 hd0 hQ' (pos_of_mem_grBall hy), phiNS_decomp ht htre ht0 hd0 hQ'
    (pos_of_mem_grBall hy')] at heq
  have he : ∀ g : ArchSO (pureForm A B), ArchSOInst.mat _ (iota 1 (pureFormD A B d) (cS hd0 g)) *ᵥ
      (e₀ : Fin 4 → ℝ) = e₀ := fun g => by rw [mat_iota, cornerMat_one_mulVec_e₀]
  have hyy : y = y' := by
    apply Subtype.ext
    have := congrArg (fun g : ArchSO Q0 => ArchSOInst.mat _ g *ᵥ (e₀ : Fin 4 → ℝ)) heq
    simp only at this
    rw [show ∀ (a b : ArchSO Q0), ArchSOInst.mat _ (a * b) = ArchSOInst.mat _ a * ArchSOInst.mat _ b from
      fun _ _ => rfl, show ∀ (a b : ArchSO Q0), ArchSOInst.mat _ (a * b) = ArchSOInst.mat _ a * ArchSOInst.mat _ b from
      fun _ _ => rfl, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, he, he, secNS_spec, secNS_spec] at this
    exact this
  subst hyy
  have h2 := mul_left_cancel heq
  have h3 := iota_cS_injective hd0 h2
  rcases eq_or_eq_neg_of_conjS_eq hA h3 with h4 | h4
  · rw [show h' = h from Subtype.ext h4]
  · exfalso
    have a1 := hh.1; have a2 := hh'.1
    have := congrFun h4 0
    simp only [Pi.neg_apply] at this
    linarith

include htre ht0 in
theorem injOn_param_ysNS (hA : A ≠ 0) (hd0 : d ≠ 0) (hQ' : gramDetR (pureFormD A B d) ≠ 0) (δ : ℝ) :
    InjOn (fun p : Sph Q0 1 × Sph (normForm A B) 1 => sNS0 ht p.1 * realS p.2)
      (grBall A B d δ ×ˢ cayBall A B δ) := by
  rintro ⟨y, h⟩ ⟨hy, hh⟩ ⟨y', h'⟩ ⟨hy', hh'⟩ heq
  simp only at heq
  have heq' := congrArg (phiNS ht htre ht0) heq
  rw [phiNS_decomp ht htre ht0 hd0 hQ' (pos_of_mem_grBall hy), phiNS_decomp ht htre ht0 hd0 hQ'
    (pos_of_mem_grBall hy')] at heq'
  have he : ∀ g : ArchSO (pureForm A B), ArchSOInst.mat _ (iota 1 (pureFormD A B d) (cS hd0 g)) *ᵥ
      (e₀ : Fin 4 → ℝ) = e₀ := fun g => by rw [mat_iota, cornerMat_one_mulVec_e₀]
  have hyy : y = y' := by
    apply Subtype.ext
    have := congrArg (fun g : ArchSO Q0 => ArchSOInst.mat _ g *ᵥ (e₀ : Fin 4 → ℝ)) heq'
    simp only at this
    rw [show ∀ (a b : ArchSO Q0), ArchSOInst.mat _ (a * b) = ArchSOInst.mat _ a * ArchSOInst.mat _ b from
      fun _ _ => rfl, show ∀ (a b : ArchSO Q0), ArchSOInst.mat _ (a * b) = ArchSOInst.mat _ a * ArchSOInst.mat _ b from
      fun _ _ => rfl, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, he, he, secNS_spec, secNS_spec] at this
    exact this
  subst hyy
  have h3 := iota_cS_injective hd0 (mul_left_cancel heq')
  rcases eq_or_eq_neg_of_conjS_eq hA h3 with h4 | h4
  · rw [show h' = h from Subtype.ext h4]
  · exfalso
    have a1 := hh.1; have a2 := hh'.1
    have := congrFun h4 0
    simp only [Pi.neg_apply] at this
    linarith

theorem continuousOn_sNS0 :
    ContinuousOn (sNS0 (A := A) (B := B) ht) {y : Sph Q0 1 | 0 < 1 + (y : Fin 4 → ℝ) 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : {y : Sph Q0 1 | 0 < 1 + (y : Fin 4 → ℝ) 0}.domRestrict (sNS0 (A := A) (B := B) ht) =
      fun y => sNS ht y.1 y.2 := funext fun y => sNS0_of_pos ht y.2
  rw [e]
  refine Continuous.subtype_mk ?_ _
  exact (continuous_cayX_vec (A := A) (B := B) (t := t)).comp_continuous
    (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

include htre ht0 in
theorem measurableSet_ysNS (hA : A ≠ 0) (hd0 : d ≠ 0) (hQ' : gramDetR (pureFormD A B d) ≠ 0) (δ : ℝ) :
    MeasurableSet (ysNS (A := A) (B := B) ht δ) := by
  refine ((measurableSet_grBall δ).prod (measurableSet_cayBall δ)).image_of_continuousOn_injOn ?_
    (injOn_param_ysNS ht htre ht0 hA hd0 hQ' δ)
  refine ContinuousOn.mul ?_ (continuous_realS.comp continuous_snd).continuousOn
  exact (continuousOn_sNS0 ht).comp continuous_fst.continuousOn fun p hp => pos_of_mem_grBall hp.1

/-! ### The constant -/

theorem volume_ball_three (δ : ℝ) (hδ : 0 < δ) : (volume (ball (0 : Fin 3 → ℝ) δ)).toReal = (2 * δ) ^ 3 := by
  rw [Real.volume_pi_ball _ hδ, ENNReal.toReal_ofReal (by positivity)]; simp

theorem toReal_pos_of_tendsto {f v : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hv : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < v δ)
    (h : Tendsto (fun δ => f δ / v δ) (𝓝[>] 0) (𝓝 L)) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < f δ := by
  filter_upwards [h.eventually (lt_mem_nhds hL), hv] with δ h1 h2
  exact (div_pos_iff_of_pos_right h2).1 h1

/-- **The local ratio at a real place with $E_w = \mathbb C$.** For every measurable $Y\subseteq S_1(\mathbb C)$ on which
$\varphi_w$ is injective, $\mu_{Q_0}(\varphi_w(Y)) = (4|A|^3|B|^3|d|^6|t|^3)^{-1}\sigma_{\mathbb C}(Y)$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratio, real place, d < 0); §3.7, pp. 64-65 [unverified page]"]
theorem leray_phiNS_image (hA : A ≠ 0) (hB : B ≠ 0) (hd0 : d ≠ 0) (hQ3 : gramDetR (pureForm A B) ≠ 0)
    (hQ3d : gramDetR (pureFormD A B d) ≠ 0) (hQ0 : gramDetR Q0 ≠ 0) {Y : Set LC} (hY : MeasurableSet Y)
    (hinj : InjOn (phiNS ht htre ht0) Y) :
    lerayMeasure Q0 hQ0 (phiNS ht htre ht0 '' Y) =
      ENNReal.ofReal (1 / (4 * |A| ^ 3 * |B| ^ 3 * |d| ^ 6 * ‖t‖ ^ 3)) * sigC (normForm (A : ℂ) (B : ℂ)) 1 Y := by
  have := isHaarMeasure_lerayMeasure hQ0
  obtain ⟨c, hc⟩ := exists_measure_image_eq_smul (sigC (normForm (A : ℂ) (B : ℂ)) 1) (lerayMeasure Q0 hQ0)
    (phiNS ht htre ht0) (continuous_phiNS ht htre ht0) (isLocInj_phiNS ht htre ht0 hA)
  set δ₀ := min (min (radG A B d) (radR A B)) (1 / 2)
  have hδ₀ : 0 < δ₀ := lt_min (lt_min (radG_pos A B d) (radR_pos A B)) (by norm_num)
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ δ₀ :=
    Filter.Eventually.and eventually_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds hδ₀))
  -- the two evaluations
  have hsig : ∀ S, sig (nsFormR A B d) 1 S = ENNReal.ofReal (1 / 2) * nu (nsFormR A B d) 1 S := fun S => by
    rw [sig, Measure.smul_apply, smul_eq_mul]; norm_num
  have hsig' : ∀ S, sig (normForm A B) 1 S = ENNReal.ofReal (1 / 2) * nu (normForm A B) 1 S := fun S => by
    rw [sig, Measure.smul_apply, smul_eq_mul]; norm_num
  have hsigC : ∀ S, sigC (normForm (A : ℂ) (B : ℂ)) 1 S = ENNReal.ofReal (1 / 4) * nuC (normForm (A : ℂ) (B : ℂ)) 1 S :=
    fun S => by
      rw [sigC, Measure.smul_apply, smul_eq_mul]
      congr 1
      rw [← ENNReal.ofReal_coe_nnreal]; congr 1; push_cast; norm_num
  have heq : ∀ δ, 0 < δ → δ ≤ δ₀ → (c : ℝ≥0∞) * (ENNReal.ofReal (1 / 4) * nuC (normForm (A : ℂ) (B : ℂ)) 1
      (ysNS (A := A) (B := B) ht δ)) = ENNReal.ofReal ((|2 * 1| ^ 3)⁻¹) * (ENNReal.ofReal (1 / 2) *
        nu (nsFormR A B d) 1 (grBall A B d δ) * (ENNReal.ofReal (|d| ^ 6)⁻¹ *
          (ENNReal.ofReal (1 / (4 * |A| ^ 3 * |B| ^ 3)) * (ENNReal.ofReal (1 / 2) *
            nu (normForm A B) 1 (cayBall A B δ))))) := by
    intro δ hδ hδ'
    have h1 := hc _ (measurableSet_ysNS ht htre ht0 hA hd0 hQ3d δ) (injOn_phiNS_ysNS ht htre ht0 hA hd0 hQ3d δ)
    have hW : MeasurableSet (conjS '' cayBall A B δ) :=
      (measurableSet_cayBall δ).image_of_continuousOn_injOn continuous_conjS.continuousOn (injOn_conjS_cayBall hA δ)
    have hWm : MeasurableSet (cS (A := A) (B := B) hd0 '' (conjS '' cayBall A B δ)) :=
      (cS (A := A) (B := B) hd0).toHomeomorph.measurableEmbedding.measurableSet_image.2 hW
    have h2 := lerayMeasure_image_sec one_ne_zero hQ3d Q0 rfl hQ0 (secNS ht htre ht0 hQ3d)
      (measurable_secNS ht htre ht0 hQ3d) (secNS_spec ht htre ht0 hQ3d) (iota 1 (pureFormD A B d))
      (mat_iota 1 (pureFormD A B d)) (measurableSet_grBall δ) hWm
    rw [← phiNS_image_ysNS ht htre ht0 hd0 hQ3d δ, leray_cS_image hd0 hQ3 hQ3d _ hW,
      leray_conjS_image hA hB hQ3 (measurableSet_cayBall δ) (injOn_conjS_cayBall hA δ), h1, hsigC, hsig,
      hsig'] at h2
    exact h2
  -- the asymptotics
  have tG := (tendsto_nu_grBall (A := A) (B := B) (d := d))
  have tC := (tendsto_nu_cayBall (A := A) (B := B))
  have hv3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < (volume (ball (0 : Fin 3 → ℝ) δ)).toReal :=
    hsmall.mono fun δ hδ => by have := hδ.1; rw [volume_ball_three δ hδ.1]; positivity
  have hfin_g := toReal_pos_of_tendsto one_pos hv3 tG
  have hfin_c := toReal_pos_of_tendsto one_pos hv3 tC
  have tY : Tendsto (fun δ => (nuC (normForm (A : ℂ) (B : ℂ)) 1 (ysNS (A := A) (B := B) ht δ)).toReal / (2 * δ) ^ 6)
      (𝓝[>] 0) (𝓝 |LinearMap.det (LNS t : E8 →ₗ[ℝ] E8)|) :=
    tendsto_nuC_div8 (fun δ => measurableSet_ysNS ht htre ht0 hA hd0 hQ3d δ) (hasStrictFDerivAt_chartNS htre)
      (hsmall.mono fun δ hδ => chartNS_image ht hδ.1 hδ.2)
  rw [det_LNS htre] at tY
  have ht3 : 0 < ‖t‖ ^ 3 / 8 := by have : 0 < ‖t‖ := norm_pos_iff.2 ht0; positivity
  have hv6 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < (2 * δ) ^ 6 := hsmall.mono fun δ hδ => by have := hδ.1; positivity
  have hfin_y := toReal_pos_of_tendsto ht3 hv6 tY
  set K0 : ℝ := 1 / (128 * |A| ^ 3 * |B| ^ 3 * |d| ^ 6)
  have hfg : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (nu (nsFormR A B d) 1 (grBall A B d δ)).toReal * (nu (normForm A B) 1 (cayBall A B δ)).toReal * K0 =
        ((c : ℝ) / 4) * (nuC (normForm (A : ℂ) (B : ℂ)) 1 (ysNS (A := A) (B := B) ht δ)).toReal := by
    filter_upwards [hsmall, hfin_g, hfin_c, hfin_y] with δ hδ hg hcay hy
    have h := congrArg ENNReal.toReal (heq δ hδ.1 hδ.2)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4),
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.coe_toReal] at h
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h
    rw [show |(2 : ℝ) * 1| ^ 3 = 8 by norm_num] at h
    simp only [K0]
    have hA3 : 0 < |A| ^ 3 := pow_pos (abs_pos.2 hA) 3
    have hB3 : 0 < |B| ^ 3 := pow_pos (abs_pos.2 hB) 3
    have hd6 : 0 < |d| ^ 6 := pow_pos (abs_pos.2 hd0) 6
    field_simp at h ⊢
    linarith
  have tF : Tendsto (fun δ => (nu (nsFormR A B d) 1 (grBall A B d δ)).toReal *
      (nu (normForm A B) 1 (cayBall A B δ)).toReal * K0 / (2 * δ) ^ 6) (𝓝[>] 0) (𝓝 (1 * 1 * K0)) := by
    refine ((tG.mul tC).mul_const K0).congr' ?_
    filter_upwards [hsmall] with δ hδ
    rw [volume_ball_three δ hδ.1]
    have : (0 : ℝ) < 2 * δ := by linarith [hδ.1]
    field_simp
  have hκ := ratio_eq_of_tendsto hfg tF tY ht3.ne'
  have hc' : (c : ℝ) = 1 / (4 * |A| ^ 3 * |B| ^ 3 * |d| ^ 6 * ‖t‖ ^ 3) := by
    have hA3 : 0 < |A| ^ 3 := pow_pos (abs_pos.2 hA) 3
    have hB3 : 0 < |B| ^ 3 := pow_pos (abs_pos.2 hB) 3
    have hd6 : 0 < |d| ^ 6 := pow_pos (abs_pos.2 hd0) 6
    have htt : 0 < ‖t‖ ^ 3 := by have : 0 < ‖t‖ := norm_pos_iff.2 ht0; positivity
    simp only [K0] at hκ
    field_simp at hκ ⊢
    linarith
  rw [hc Y hY hinj, ← ENNReal.ofReal_coe_nnreal, hc']

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
