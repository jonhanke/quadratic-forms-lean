/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelLatRanks
import QuadFormsKB.Tamagawa.SiegelRankOneGeneral

/-!
# Siegel's formula in rank 1 for every genus

**Layer:** $F$ totally real (any class number); $Q_0 = \langle c\rangle$ over $\mathcal O_F$ totally positive; $L = \mathfrak a e_0$ an
**arbitrary** lattice in $F$ ($\mathfrak a$ any fractional ideal) with $c\,\mathfrak a^2 \subseteq \mathcal O_F$; $m \in \mathcal O_F$ totally positive.

`siegelProduct` is degenerate in rank $1$; the correct statement carries Siegel's $\varepsilon = \tfrac12$ at every place
(`SiegelRankOne.siegelProductOne`). Its lattice version is
$$\mathcal S_1(L, m) = \prod_\sigma\frac{\beta_\sigma(m)}2\prod_\mathfrak p\frac{\beta_\mathfrak p(L, m)}2$$
(`siegelProductOneLat`, with the $\beta_\mathfrak p(L, m)$).

**Local values** (`latBeta_rankOne_of_mem`, `latBeta_rankOne_of_not_mem`): for $m = ct^2$, $t \in F^\times$,
$\beta_\mathfrak p(L, m) = 2\,|2ct|_\mathfrak p^{-1}$ if $t \in L_\mathfrak p$ and $0$ otherwise (the model $\langle ca^2\rangle$, $L_\mathfrak p = a\mathfrak o_\mathfrak p$, at
$m = ca^2(t/a)^2$: the DVR count `localDensity_rankOne_sq`, resp. no solutions modulo $\pi^k$ when $ca^2 \nmid m$).

**Proves** **`siegelFormulaOneLat_totallyReal`** (unconditional): for every such $L$ and every totally positive $m$,
$$\mathrm{repMass}(L, m) = \mathrm{Mass}(L)\cdot 2\,\mathcal S_1(L, m),$$
with $\mathrm{Mass}(L) = \tfrac12$ (the genus of $L$ is $\{L\}$), $\mathcal S_1(L, m) = 1$ if $m = ct^2$ with $t \in L$ (the product formula for $2ct$) and
$\mathcal S_1(L, m) = 0$ otherwise (a vanishing local factor: $t \notin L_\mathfrak p$ for some $\mathfrak p$, or $m \notin cF_\mathfrak p^{\times2}$ for some
$\mathfrak p$ by Hasse–Minkowski). For $L = \mathcal O_F$ it extends `siegelFormulaOne_sq` to every totally positive $m$
(`siegelFormulaOne_totallyReal_std`).

Sources: Siegel 1935, Hauptsatz ($n = 1$, $\varepsilon = \tfrac12$) [unverified]; Weil 1982, §3.7 ($\tau(SO_1) = 1$) [unverified].
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelLat

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
open QuadFormsKB.HilbertModular LatChange

/-! ### Local densities of $\langle c\rangle$ -/

section DVRPart

open QuadFormsKB.LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **No solutions when $c \nmid m$**: $\beta_\pi(\langle c\rangle, m) = 0$ (modulo $\pi^k \subseteq (c)$, $cx^2 \equiv m$ forces $c \mid m$). -/
theorem localDensity_unary_eq_zero_of_not_dvd {π : R} (hπ : Irreducible π) (Q : QuadForm R 1) {c m : R}
    (hQ : Q.coeff 0 0 = c) (hc : c ≠ 0) (hcm : ¬ c ∣ m) : DVR.localDensity Q π m = 0 := by
  obtain ⟨e, u, hce, hu⟩ := dvr_eq_pow_mul_unit hπ hc
  unfold DVR.localDensity
  refine Filter.Tendsto.limUnder_eq (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
  filter_upwards [Filter.eventually_ge_atTop e] with k hk
  have h0 : DVR.repCount Q π k m = 0 := by
    unfold DVR.repCount
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x 0)
    have hev : Q.evalIn (R ⧸ Ideal.span {π ^ k}) x = Ideal.Quotient.mk _ (c * y ^ 2) := by
      simp only [QuadForm.evalIn, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, le_refl,
        if_true, hQ, ← hy, Ideal.Quotient.algebraMap_eq, map_mul, map_pow]
      ring
    rw [hev] at hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hx)
    have hcπ : c ∣ π ^ k := by
      rw [hce, hu.mul_right_dvd]; exact pow_dvd_pow π hk
    apply hcm
    have hm : m = c * y ^ 2 - z * π ^ k := by linear_combination hz
    rw [hm]
    exact dvd_sub (dvd_mul_right c _) (dvd_mul_of_dvd_right hcπ z)
  rw [h0]; simp

end DVRPart

section Local

open QuadFormsKB.LocalDensity.DVR

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\beta_\mathfrak p(\langle c\rangle, cs^2) = 2/|2cs|_\mathfrak p$ for $c, s \in \mathfrak o_\mathfrak p\setminus0$. -/
theorem localDensity_unary_sq (Q : QuadForm 𝔬 1) {c s : 𝔬} (hQ : Q.coeff 0 0 = c) (hc : c ≠ 0) (hs : s ≠ 0) :
    DVR.localDensity Q (NF.π v) (c * s ^ 2) = 2 / ‖((2 * c * s : 𝔬) : Fv)‖ := by
  obtain ⟨t, w, h2, hw⟩ := dvr_eq_pow_mul_unit (NF.irreducible_π v) (mul_ne_zero (NF.two_ne_zero' v) hs)
  obtain ⟨e, u, hce, hu⟩ := dvr_eq_pow_mul_unit (NF.irreducible_π v) hc
  rw [SiegelRankOne.localDensity_rankOne_sq (NF.irreducible_π v) h2 hw hce hu Q hQ]
  have hx : (2 * c * s : 𝔬) = NF.π v ^ (t + e) * (w * u) := by
    rw [show (2 * c * s : 𝔬) = (2 * s) * c by ring, h2, hce]; ring
  rw [hx, norm_coe_of_pow_dvd v (e := t + e) (dvd_mul_right _ _)
    (dvr_not_pow_succ_dvd (NF.irreducible_π v) (hw.mul hu) _)]
  have hq : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast DVR.q_pos
  field_simp

variable {Q₀ : QuadForm (𝓞 F) 1} {L : Lat F 1}

/-- The coefficient of the model form $Q_A = \langle ca^2\rangle$, $a = A_{00}$. -/
theorem coeff_gramZ_rankOne (A : GL (Fin 1) F) (h : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) :
    algebraMap (𝓞 F) F ((gramZ (formF Q₀) A h).coeff 0 0) =
      algebraMap (𝓞 F) F (Q₀.coeff 0 0) * A.val 0 0 ^ 2 := by
  have h1 : (HilbertModular.formF (gramZ (HilbertModular.formF Q₀) A h)).eval (fun _ => 1) =
      ((HilbertModular.formF Q₀).compMat A.val).eval (fun _ => 1) := by
    rw [formF_gramZ]
  rw [eval_compMat, SiegelRankOne.eval_rankOne, SiegelRankOne.eval_rankOne] at h1
  simpa [mulVec, dotProduct] using h1

/-- $L_\mathfrak p = A\,\mathfrak o_\mathfrak p$ contains $t$ iff $t/A_{00} \in \mathfrak o_\mathfrak p$. -/
theorem locVec_mem_locAct_rankOne (A : GL (Fin 1) F) (t : F) :
    locVec v (fun _ => t) ∈ locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (std v) ↔
      Valued.v (algebraMap F Fv t / algebraMap F Fv (A.val 0 0)) ≤ 1 := by
  have ha : A.val 0 0 ≠ 0 := by
    have := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    simpa [Matrix.det_fin_one] using this
  have haF : algebraMap F Fv (A.val 0 0) ≠ 0 := (map_ne_zero _).mpr ha
  rw [mem_locAct]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h0 := congrFun hyx 0
    simp only [Matrix.GeneralLinearGroup.map_apply, mulVec, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, Matrix.map_apply, locVec_apply] at h0
    have hy0 := hy 0
    rw [neg_zero, WithZero.exp_zero] at hy0
    rw [← h0, mul_div_cancel_left₀ _ haF]
    exact hy0
  · intro hle
    refine ⟨fun _ => algebraMap F Fv t / algebraMap F Fv (A.val 0 0), fun i => ?_, ?_⟩
    · rw [neg_zero, WithZero.exp_zero]; exact hle
    · funext i
      fin_cases i
      simp only [Matrix.GeneralLinearGroup.map_apply, mulVec, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton, Matrix.map_apply, locVec_apply]
      field_simp
      rw [mul_comm]; rfl

variable [IsTotallyReal F]

/-- **$\beta_\mathfrak p(L, ct^2) = 2/|2ct|_\mathfrak p$ when $t \in L_\mathfrak p$.** -/
theorem latBeta_rankOne_of_mem (hQ : Q₀.Nondegenerate) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F} {t : F}
    (ht : t ≠ 0) (hmt : algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2)
    (hmem : locVec v (fun _ => t) ∈ loc v L.1) :
    latBeta v Q₀ L m = 2 / ‖algebraMap F Fv (2 * algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t)‖ := by
  obtain ⟨A, hA⟩ := exists_isLocModel v L
  have hint := hA.isIntegral v hLi
  set QA := gramZ (formF Q₀) A hint
  have ha : (A.val 0 0) ≠ 0 := by
    have := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    simpa [Matrix.det_fin_one] using this
  have hloc : loc v L.1 = locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (std v) := by
    rw [← hA.2, Lattices.latOf, loc_glImage, loc_intVec]
  rw [hloc, locVec_mem_locAct_rankOne] at hmem
  have hc0 : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hcA : QA.coeff 0 0 ≠ 0 := by
    intro h0
    have := coeff_gramZ_rankOne A hint
    rw [show QA.coeff 0 0 = 0 from h0, map_zero] at this
    exact mul_ne_zero ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc0) (pow_ne_zero 2 ha) this.symm
  set s : 𝔬 := toO v _ hmem
  have hs : s ≠ 0 := by
    intro h0
    have := congrArg (fun z : 𝔬 => (z : Fv)) h0
    simp only [s, toO, ZeroMemClass.coe_zero] at this
    exact div_ne_zero ((map_ne_zero _).mpr ht) ((map_ne_zero _).mpr ha) this
  have hsF : (s : Fv) = algebraMap F Fv t / algebraMap F Fv (A.val 0 0) := rfl
  have hcAF : ((NF.ι v (QA.coeff 0 0) : 𝔬) : Fv) =
      algebraMap F Fv (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) * algebraMap F Fv (A.val 0 0) ^ 2 := by
    rw [show ((NF.ι v (QA.coeff 0 0) : 𝔬) : Fv) = algebraMap F Fv (algebraMap (𝓞 F) F (QA.coeff 0 0)) from rfl,
      coeff_gramZ_rankOne A hint, map_mul, map_pow]
  have haF : algebraMap F Fv (A.val 0 0) ≠ 0 := (map_ne_zero _).mpr ha
  have hm' : NF.ι v m = NF.ι v (QA.coeff 0 0) * s ^ 2 := by
    apply Subtype.ext
    push_cast
    rw [hcAF, hsF, show ((NF.ι v m : 𝔬) : Fv) = algebraMap F Fv (algebraMap (𝓞 F) F m) from rfl, hmt, map_mul,
      map_pow]
    field_simp
  rw [latBeta_eq v Q₀ L hA hint, NF.localDensity_eq_completion, hm',
    localDensity_unary_sq v (NF.Qp v QA) (by simp [NF.Qp, QuadForm.map]) (NF.ι_ne_zero v hcA) hs]
  have hnorm : ‖((2 * NF.ι v (QA.coeff 0 0) * s : 𝔬) : Fv)‖ =
      ‖algebraMap F Fv (A.val 0 0)‖ * ‖algebraMap F Fv (2 * algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t)‖ := by
    rw [← norm_mul]
    congr 1
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hcAF, hsF, map_mul, map_mul, map_ofNat]
    show (2 : Fv) * _ * _ = _
    field_simp
  rw [hnorm]
  have : 0 < ‖algebraMap F Fv (A.val 0 0)‖ := norm_pos_iff.mpr haF
  have h2 : algebraMap F Fv (A.val.det) = algebraMap F Fv (A.val 0 0) := by rw [Matrix.det_fin_one]
  rw [h2]
  field_simp

/-- **$\beta_\mathfrak p(L, ct^2) = 0$ when $t \notin L_\mathfrak p$** (and $m = ct^2 \ne 0$). -/
theorem latBeta_rankOne_of_not_mem (hQ : Q₀.Nondegenerate) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    {t : F} (ht : t ≠ 0) (hmt : algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2)
    (hmem : locVec v (fun _ => t) ∉ loc v L.1) : latBeta v Q₀ L m = 0 := by
  obtain ⟨A, hA⟩ := exists_isLocModel v L
  have hint := hA.isIntegral v hLi
  set QA := gramZ (formF Q₀) A hint
  have ha : (A.val 0 0) ≠ 0 := by
    have := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    simpa [Matrix.det_fin_one] using this
  have haF : algebraMap F Fv (A.val 0 0) ≠ 0 := (map_ne_zero _).mpr ha
  have hloc : loc v L.1 = locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (std v) := by
    rw [← hA.2, Lattices.latOf, loc_glImage, loc_intVec]
  rw [hloc, locVec_mem_locAct_rankOne] at hmem
  have hc0 : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hcF : algebraMap F Fv (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc0)
  have hcA : QA.coeff 0 0 ≠ 0 := by
    intro h0
    have := coeff_gramZ_rankOne A hint
    rw [show QA.coeff 0 0 = 0 from h0, map_zero] at this
    exact mul_ne_zero ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc0) (pow_ne_zero 2 ha) this.symm
  have hcAF : ((NF.ι v (QA.coeff 0 0) : 𝔬) : Fv) =
      algebraMap F Fv (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) * algebraMap F Fv (A.val 0 0) ^ 2 := by
    rw [show ((NF.ι v (QA.coeff 0 0) : 𝔬) : Fv) = algebraMap F Fv (algebraMap (𝓞 F) F (QA.coeff 0 0)) from rfl,
      coeff_gramZ_rankOne A hint, map_mul, map_pow]
  have hndvd : ¬ NF.ι v (QA.coeff 0 0) ∣ NF.ι v m := by
    rintro ⟨z, hz⟩
    apply hmem
    have hzF : ((NF.ι v m : 𝔬) : Fv) = ((NF.ι v (QA.coeff 0 0) : 𝔬) : Fv) * (z : Fv) := by
      rw [hz, MulMemClass.coe_mul]
    rw [show ((NF.ι v m : 𝔬) : Fv) = algebraMap F Fv (algebraMap (𝓞 F) F m) from rfl, hmt, map_mul, map_pow,
      hcAF] at hzF
    have h3 : algebraMap F Fv t ^ 2 = algebraMap F Fv (A.val 0 0) ^ 2 * (z : Fv) :=
      mul_left_cancel₀ hcF (by linear_combination hzF)
    have hsq : (algebraMap F Fv t / algebraMap F Fv (A.val 0 0)) ^ 2 = (z : Fv) := by
      rw [div_pow, h3]; field_simp
    have hz1 : Valued.v (z : Fv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp z.2
    rw [← hsq, map_pow] at hz1
    exact (pow_le_one_iff_of_nonneg zero_le (by norm_num)).mp hz1
  rw [latBeta_eq v Q₀ L hA hint, NF.localDensity_eq_completion,
    localDensity_unary_eq_zero_of_not_dvd (NF.irreducible_π v) (NF.Qp v QA) (by simp [NF.Qp, QuadForm.map])
      (NF.ι_ne_zero v hcA) hndvd, mul_zero]

end Local

/-! ### The global formula -/

section Global

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **The rank-one Siegel product of an arbitrary lattice** (Siegel's $\varepsilon = \tfrac12$ at every place):
$\mathcal S_1(L, m) = \prod_\sigma\beta_\sigma(m)/2\cdot\prod_\mathfrak p\beta_\mathfrak p(L, m)/2$. For $L = \mathcal O_F$ it is `siegelProductOne`. -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2 at every place), arbitrary lattice [unverified]"]
def siegelProductOneLat (Q₀ : QuadForm (𝓞 F) 1) (L : Lat F 1) (m : 𝓞 F) : ℝ :=
  (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ) / 2) *
    ∏' v : HeightOneSpectrum (𝓞 F), latBeta v Q₀ L m / 2

theorem siegelProductOneLat_std (Q₀ : QuadForm (𝓞 F) 1) (m : 𝓞 F) :
    siegelProductOneLat Q₀ (stdLat F 1) m = SiegelRankOne.siegelProductOne Q₀ m := by
  unfold siegelProductOneLat SiegelRankOne.siegelProductOne; simp_rw [latBeta_std]

/-- $\beta_\sigma(ct^2)/2 = 1/(2|\sigma(ct)|)$ for $t \in F^\times$. -/
theorem archRepDensity_rankOne_F (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) {m : 𝓞 F} {t : F} (ht : t ≠ 0)
    (hmt : algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2) (σ : F →ₐ[ℚ] ℂ) :
    archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ) / 2 =
      1 / (2 * ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t)‖) := by
  have hd := TauSOOne.detGram_rankOne Q₀ σ
  have ha : 0 < ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ := by
    rw [norm_pos_iff, map_ne_zero]; exact_mod_cast hc
  have hb : 0 < ‖σ t‖ := by rw [norm_pos_iff, map_ne_zero]; exact ht
  have e1 : ‖σ (algebraMap (𝓞 F) F m)‖ = ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ * ‖σ t‖ ^ 2 := by
    rw [hmt, map_mul, map_pow, norm_mul, norm_pow]
  have e2 : ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t)‖ = ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ * ‖σ t‖ := by
    rw [map_mul, norm_mul]
  rw [e1, e2, hd, archRepDensity]
  have h1 : Real.pi ^ (((1 : ℕ) : ℝ) / 2) / Real.Gamma (((1 : ℕ) : ℝ) / 2) = 1 := by
    have : Real.pi ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt Real.pi := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [this]; norm_num [Real.Gamma_one_half_eq]
    exact Real.sqrt_ne_zero'.mpr Real.pi_pos
  set a := ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖
  set b := ‖σ t‖
  have h2 : (a * b ^ 2) ^ ((((1 : ℕ) : ℝ) - 2) / 2) * a ^ (-(1 / 2 : ℝ)) = (a * b)⁻¹ := by
    rw [show ((((1 : ℕ) : ℝ) - 2) / 2) = -(1 / 2 : ℝ) by norm_num, Real.mul_rpow ha.le (sq_nonneg b),
      Real.rpow_neg ha.le, Real.rpow_neg (sq_nonneg b), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hb.le]
    have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    have hsa2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    field_simp
    nlinarith [hsa2]
  rw [mul_assoc, h2, h1]
  field_simp

/-- $\mathrm{repMass}(L, t) = r_L(t)/2$ in rank one (the genus of $L$ is $\{L\}$, $|O(L)| = 2$). -/
theorem repMass_rankOne_lat {Q : QuadForm F 1} (hc : Q.coeff 0 0 ≠ 0) (L : Lat F 1) (t : F) :
    repMass Q L t = (repCount Q L t : ℝ) / 2 := by
  rw [repMass, RankOne.genusClasses_rankOne hc L, finsum_mem_singleton]
  change ((repCount Q L t : ℕ) : ℝ) / (Nat.card (autLat Q L.1) : ℝ) = _
  rw [RankOne.card_autLat_rankOne hc]; norm_num

/-- The solutions of $cx^2 = ct^2$ are $x = \pm t$. -/
theorem eq_or_eq_neg_of_eval (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) {t : F} {x : Fin 1 → F}
    (h : (formF Q₀).eval x = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2) :
    x = (fun _ => t) ∨ x = -(fun _ => t) := by
  have hcF : algebraMap (𝓞 F) F (Q₀.coeff 0 0) ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc
  rw [SiegelRankOne.eval_rankOne] at h
  have h1 : (x 0 - t) * (x 0 + t) = 0 := by
    have : algebraMap (𝓞 F) F (Q₀.coeff 0 0) * ((x 0 - t) * (x 0 + t)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left hcF
  rcases mul_eq_zero.mp h1 with h2 | h2
  · left; funext i; fin_cases i; simpa [sub_eq_zero] using h2
  · right; funext i; fin_cases i; simpa [add_eq_zero_iff_eq_neg] using h2

theorem repCount_rankOne_lat_of_mem (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) (L : Lat F 1) {m : 𝓞 F} {t : F}
    (ht : t ≠ 0) (hmt : algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2)
    (hmem : (fun _ => t) ∈ L.1) : repCount (formF Q₀) L (algebraMap (𝓞 F) F m) = 2 := by
  have hset : {x : Fin 1 → F | x ∈ L.1 ∧ (formF Q₀).eval x = algebraMap (𝓞 F) F m} =
      {fun _ => t, -(fun _ => t)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩; rw [hmt] at h; exact eq_or_eq_neg_of_eval Q₀ hc h
    · rintro (rfl | rfl)
      · exact ⟨hmem, by rw [SiegelRankOne.eval_rankOne, hmt]⟩
      · exact ⟨L.1.neg_mem hmem, by rw [SiegelRankOne.eval_rankOne, hmt]; simp⟩
  unfold repCount
  rw [show Nat.card {x : Fin 1 → F // x ∈ L.1 ∧ (formF Q₀).eval x = algebraMap (𝓞 F) F m} =
    Set.ncard {x : Fin 1 → F | x ∈ L.1 ∧ (formF Q₀).eval x = algebraMap (𝓞 F) F m} from Nat.card_coe_set_eq _,
    hset, Set.ncard_pair]
  intro h
  have : t = -t := congrFun h 0
  exact ht (self_eq_neg.mp this)

theorem repCount_rankOne_lat_of_not_mem (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) (L : Lat F 1) {m : 𝓞 F}
    {t : F} (hmt : algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2)
    (hmem : (fun _ => t) ∉ L.1) : repCount (formF Q₀) L (algebraMap (𝓞 F) F m) = 0 := by
  unfold repCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨x, hx, hev⟩
  rw [hmt] at hev
  rcases eq_or_eq_neg_of_eval Q₀ hc hev with h | h
  · rw [h] at hx; exact hmem hx
  · rw [h] at hx; exact hmem (by simpa using L.1.neg_mem hx)

/-- **A vanishing local factor when $m$ is not represented over $F$** (any rank): by Hasse–Minkowski some prime $\mathfrak p$ has
$m \notin Q_0(F_\mathfrak p^N)$, and then $\beta_\mathfrak p(L, m) = 0$. -/
theorem exists_latBeta_eq_zero_of_not_rep {n : ℕ} (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (h : ¬ ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m) : ∃ v, latBeta v Q₀ L m = 0 := by
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    by
    intro h0; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := hm w; rw [h0, map_zero] at this; exact lt_irrefl 0 this
  have hQF := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hQF
  have hnot : ¬ (formF Q₀).RepresentsIn F (algebraMap (𝓞 F) F m) := by
    rintro ⟨x, hx⟩; exact h ⟨x, hx⟩
  rw [represents_iff_everywhere_nf (formF Q₀) hQF _ hρ] at hnot
  simp only [NFPlace.Everywhere, not_forall] at hnot
  obtain ⟨p, hp⟩ := hnot
  cases p with
  | infinite w => exact absurd (representsIn_real Q₀ hpd hm w) hp
  | finite v =>
    refine ⟨v, ?_⟩
    obtain ⟨A, hA⟩ := exists_isLocModel v L
    have hint := hA.isIntegral v hLi
    have hQ₁ := nondegenerate_gramZ hQ₀ A hint
    have hp₁ : ¬ (formF (gramZ (formF Q₀) A hint)).RepresentsIn (v.adicCompletion F) (algebraMap (𝓞 F) F m) := by
      rintro ⟨x, hx⟩
      apply hp
      refine ⟨(A.val.map (algebraMap F (v.adicCompletion F))) *ᵥ x, ?_⟩
      rw [← evalIn_compMat_gl, ← formF_gramZ Q₀ A hint]
      exact hx
    rw [latBeta_eq v Q₀ L hA hint, ← betaZ_algebraMap,
      betaZ_eq_zero_of_not_rep _ hQ₁ (by omega) v hρ hp₁, mul_zero]

/-- **Siegel's formula in rank one for every genus, every totally real field** (unconditional; Siegel 1935, Hauptsatz, $n = 1$,
$\varepsilon = \tfrac12$ [unverified]): for $Q_0 = \langle c\rangle$ totally positive over $\mathcal O_F$, **every** lattice $L$ in $(F, cx^2)$ with $Q_0$
integral on $L$ and every totally positive $m \in \mathcal O_F$,
$$\mathrm{repMass}(L, m) = \mathrm{Mass}(L)\cdot 2\,\mathcal S_1(L, m).$$
(Both sides are $1$ if $m = ct^2$ with $t \in L$, and $0$ otherwise.) -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2), every genus, over a totally real field [unverified]"]
theorem siegelFormulaOneLat_totallyReal (Q₀ : QuadForm (𝓞 F) 1) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F 1)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass (formF Q₀) L (algebraMap (𝓞 F) F m) = mass (formF Q₀) L * (2 * siegelProductOneLat Q₀ L m) := by
  classical
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hc0 : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hc' : (formF Q₀).coeff 0 0 ≠ 0 := RankOne.coeff_ne_zero_of_nondegenerate Q₀ hQ
  have hm0 : algebraMap (𝓞 F) F m ≠ 0 :=
    by
    intro h0; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := hm w; rw [h0, map_zero] at this; exact lt_irrefl 0 this
  rw [RankOne.mass_rankOne hc' L, repMass_rankOne_lat hc' L]
  by_cases hrep : ∃ t : F, algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2
  · obtain ⟨t, hmt⟩ := hrep
    have ht : t ≠ 0 := by rintro rfl; apply hm0; rw [hmt]; ring
    by_cases hmem : (fun _ => t) ∈ L.1
    · rw [repCount_rankOne_lat_of_mem Q₀ hc0 L ht hmt hmem]
      -- `S₁(L, m) = 1`
      set x : F := 2 * algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t
      have hcF : algebraMap (𝓞 F) F (Q₀.coeff 0 0) ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc0
      have hx : x ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hcF) ht
      have hloc : ∀ v : HeightOneSpectrum (𝓞 F), latBeta v Q₀ L m / 2 = ‖algebraMap F (v.adicCompletion F) x‖⁻¹ := by
        intro v
        rw [latBeta_rankOne_of_mem v hQ hLi ht hmt (locVec_mem_loc v hmem)]
        ring
      have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) x‖⁻¹ := by
        refine (finite_valuation_ne_one hx).subset fun v hv => ?_
        by_contra h
        apply hv
        show ‖algebraMap F (v.adicCompletion F) x‖⁻¹ = 1
        rw [norm_algebraMap_eq_one (by simpa using h), inv_one]
      have hS : siegelProductOneLat Q₀ L m = 1 := by
        unfold siegelProductOneLat
        rw [Finset.prod_congr rfl fun σ _ => archRepDensity_rankOne_F Q₀ hc0 ht hmt σ,
          show (fun v => latBeta v Q₀ L m / 2) = fun v => ‖algebraMap F (v.adicCompletion F) x‖⁻¹ from funext hloc,
          tprod_eq_finprod hfin, finprod_inv_distrib, finprod_norm_eq x hx, inv_inv, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun σ _ => ?_
        have hσ : ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t)‖ ≠ 0 := by
          rw [norm_ne_zero_iff]; exact (map_ne_zero σ).mpr (mul_ne_zero hcF ht)
        have e : ‖σ x‖ = 2 * ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t)‖ := by
          simp only [x, mul_assoc, map_mul, norm_mul, map_ofNat, Complex.norm_ofNat]
        rw [e]; field_simp
      rw [hS]; norm_num
    · rw [repCount_rankOne_lat_of_not_mem Q₀ hc0 L hmt hmem]
      obtain ⟨v, hv⟩ : ∃ v, locVec v (fun _ => t) ∉ loc v L.1 := by
        by_contra hall
        push Not at hall
        exact hmem ((mem_iff_forall_loc L.2 _).mpr hall)
      have h0 : latBeta v Q₀ L m / 2 = 0 := by
        rw [latBeta_rankOne_of_not_mem v hQ hLi ht hmt hv, zero_div]
      unfold siegelProductOneLat
      rw [tprod_of_exists_eq_zero ⟨v, h0⟩]; simp
  · have hnr : ¬ ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m := by
      rintro ⟨ξ, hξ⟩
      exact hrep ⟨ξ 0, by rw [← hξ, SiegelRankOne.eval_rankOne]⟩
    have hrc : repCount (formF Q₀) L (algebraMap (𝓞 F) F m) = 0 := by
      unfold repCount
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun x => hnr ⟨x.1, x.2.2⟩⟩
    obtain ⟨v, hv⟩ := exists_latBeta_eq_zero_of_not_rep (n := 0) Q₀ hpd L hLi hm hnr
    have h0 : latBeta v Q₀ L m / 2 = 0 := by rw [hv, zero_div]
    rw [hrc]
    unfold siegelProductOneLat
    rw [tprod_of_exists_eq_zero ⟨v, h0⟩]; simp

/-- For $L = \mathcal O_F$: the corrected rank-one formula for **every** totally positive $m$ (extending `siegelFormulaOne_sq`,
which treats $m = cs^2$, $s \in \mathcal O_F$). -/
theorem siegelFormulaOne_totallyReal_std (Q₀ : QuadForm (𝓞 F) 1) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass (formF Q₀) (stdLat F 1) (algebraMap (𝓞 F) F m) =
      mass (formF Q₀) (stdLat F 1) * (2 * SiegelRankOne.siegelProductOne Q₀ m) := by
  rw [← siegelProductOneLat_std]
  exact siegelFormulaOneLat_totallyReal Q₀ hpd (stdLat F 1) (HilbertModular.isIntegral_stdLat Q₀) hm

end Global

end QuadFormsKB.Tamagawa.SiegelLat
