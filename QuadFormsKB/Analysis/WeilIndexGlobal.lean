import QuadFormsKB.Analysis.WeilIndexNF
import QuadFormsKB.Analysis.WeilIndexInf

/-!
# The product formula for the Weil index

For $b \in F^\times$,
$$\gamma_\infty(b)\prod_v\gamma_v(b) = 1$$
(`weilInf_mul_finprod_weilV`), where $\gamma_v(b)$ is the Weil constant at the finite place $v$ (`weilV`) and
$\gamma_\infty(b) = \prod_{w\mid\infty}\gamma_w(b)$ (`weilInf`). This is Weil's theorem (Acta Math. 111, 1964) that the
global Weil index is trivial on $F$, in the unnormalized form needed for Hilbert reciprocity.

*Proof* (Poisson summation three times). Let $\Phi = \Phi_\infty\otimes\bigotimes_v\mathbf 1_{\mathcal O_v}$ with the
self-dual Gaussian $\Phi_\infty$, $\Theta = \sum_{\gamma\in F}\Phi(\gamma)$, and $c = -1/(4b)$. Since $\psi(b\gamma^2) = 1$
for $\gamma\in F$,
$$\Theta = \sum_\gamma\hat\Phi(\gamma) = \sum_\gamma\psi(b\gamma^2)\hat\Phi(\gamma) =
\sum_\gamma\mathcal F\big(\psi(bx^2)\hat\Phi\big)(\gamma) = \Gamma(b)\sum_\gamma\psi(c\gamma^2)\,
\mathcal F\big(\Phi\psi(cx^2)\big)(2c\gamma) = \Gamma(b)\sum_\gamma\Phi(\gamma)\psi(c\gamma^2) = \Gamma(b)\,\Theta,$$
using the local Weil identities (`weilV_identity`, `weilInf_identity`) and $\gamma \mapsto 2c\gamma$ being a bijection
of $F$. Finally $\Theta \ge \Phi(0) = 1$.
-/

open IsDedekindDomain NumberField WithZero MeasureTheory NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Real FourierTransform Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

/-! ### Finiteness of the local factors -/

lemma hasFiniteMulSupport_psiV_coe (x : F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (psiV v (algebraMap F (v.adicCompletion F) x) : ℂ) :=
  (hasFiniteMulSupport_psiV x).subset fun v hv h =>
    hv ((congrArg (fun z : Circle => (z : ℂ)) h).trans Circle.coe_one)

/-- **The product formula for $\psi$, complex-valued:** $\psi_\infty(x)\prod_v\psi_v(x) = 1$ for $x \in F$. -/
lemma psiInf_mul_finprod_psiV (x : F) :
    (psiInf (mixedEmbedding F x) : ℂ) *
      ∏ᶠ v, (psiV v (algebraMap F (v.adicCompletion F) x) : ℂ) = 1 := by
  have h := congrArg (fun z : Circle => (z : ℂ)) (fourierChar_trace_mul_finprod_psiV x)
  have hm : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), psiV v (algebraMap F (v.adicCompletion F) x) : Circle) : ℂ) =
      ∏ᶠ v, (psiV v (algebraMap F (v.adicCompletion F) x) : ℂ) :=
    MonoidHom.map_finprod Circle.coeHom (hasFiniteMulSupport_psiV x)
  simp only [Circle.coe_mul, Circle.coe_one] at h
  rw [hm] at h
  simpa only [psiInf, traceInf_mixedEmbedding] using h

lemma valued_le_one_of_not_mem_support {v : HeightOneSpectrum (𝓞 F)} {x : F}
    (hv : v ∉ HeightOneSpectrum.Support (𝓞 F) x) :
    Valued.v (algebraMap F (v.adicCompletion F) x) ≤ 1 := by
  rw [HN.valued_algebraMap]; simpa [HeightOneSpectrum.Support] using hv

lemma hasFiniteMulSupport_ballIndV (γ : F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ballIndV v 0 0 (algebraMap F (v.adicCompletion F) γ) := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) γ).subset fun v hv => ?_
  simp only [Function.mem_mulSupport, ne_eq] at hv
  by_contra h
  apply hv
  rw [ballIndV, Set.indicator_of_mem]
  simpa using valued_le_one_of_not_mem_support h

lemma hasFiniteMulSupport_fourierV_ballIndV (γ : F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      fourierV v (ballIndV v 0 0) (algebraMap F (v.adicCompletion F) γ) := by
  refine (finite_support_diffExp.union (HeightOneSpectrum.Support.finite (𝓞 F) γ)).subset fun v hv => ?_
  simp only [Function.mem_mulSupport, ne_eq] at hv
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hv (fourierV_ballIndV_zero_eq_one v (by exact_mod_cast h.1) (valued_le_one_of_not_mem_support h.2))

/-- If $v(c) \le 1$, the chirp $\psi_v(cx^2)$ is trivial on $\mathcal O_v$. -/
lemma ballIndV_mul_chirp_eq {v : HeightOneSpectrum (𝓞 F)} {c : v.adicCompletion F}
    (hc : Valued.v c ≤ 1) :
    (fun x => ballIndV v 0 0 x * (psiV v (c * x ^ 2) : ℂ)) = ballIndV v 0 0 := by
  ext x
  by_cases hx : x ∈ {x : v.adicCompletion F | Valued.v (x - 0) ≤ exp (-(0 : ℤ))}
  · rw [ballIndV, Set.indicator_of_mem hx, one_mul, psiV_eq_one_of_le_one v, Circle.coe_one]
    simp only [sub_zero, neg_zero, exp_zero, Set.mem_ofPred_eq] at hx
    rw [map_mul, map_pow]
    calc Valued.v c * Valued.v x ^ 2 ≤ 1 * 1 := by gcongr; exact pow_le_one₀ zero_le hx
      _ = 1 := one_mul 1
  · rw [ballIndV, Set.indicator_of_notMem hx, zero_mul]

lemma hasFiniteMulSupport_fourierV_chirp (c γ : F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      fourierV v (fun x => ballIndV v 0 0 x * (psiV v (algebraMap F (v.adicCompletion F) c * x ^ 2) : ℂ))
        (algebraMap F (v.adicCompletion F) γ) := by
  refine ((finite_support_diffExp.union (HeightOneSpectrum.Support.finite (𝓞 F) γ)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) c)).subset fun v hv => ?_
  simp only [Function.mem_mulSupport, ne_eq] at hv
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  apply hv
  rw [ballIndV_mul_chirp_eq (valued_le_one_of_not_mem_support h.2)]
  exact fourierV_ballIndV_zero_eq_one v (by exact_mod_cast h.1.1) (valued_le_one_of_not_mem_support h.1.2)

/-! ### The mixed embedding -/

lemma mixedEmbedding_inv (b : F) : mixedEmbedding F b⁻¹ = (mixedEmbedding F b)⁻¹ := by
  ext w
  · simp [mixedEmbedding_apply_isReal]
  · simp [mixedEmbedding_apply_isComplex]

lemma mixedEmbedding_fst_ne_zero {b : F} (hb : b ≠ 0) (w : {w : InfinitePlace F // IsReal w}) :
    (mixedEmbedding F b).1 w ≠ 0 := by
  rw [mixedEmbedding_apply_isReal]; exact (map_ne_zero _).mpr hb

lemma mixedEmbedding_snd_ne_zero {b : F} (hb : b ≠ 0) (w : {w : InfinitePlace F // IsComplex w}) :
    (mixedEmbedding F b).2 w ≠ 0 := by
  rw [mixedEmbedding_apply_isComplex]; exact (map_ne_zero _).mpr hb

/-! ### The theta value -/

/-- $\Theta = \sum_{\gamma\in F}\Phi_\infty(\gamma)\prod_v\mathbf 1_{\mathcal O_v}(\gamma)$. -/
def thetaGauss (F : Type) [Field F] [NumberField F] : ℂ :=
  ∑' γ : F, gaussInf (mixedEmbedding F γ) * ∏ᶠ v, ballIndV v 0 0 (algebraMap F (v.adicCompletion F) γ)

lemma ballIndV_real (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ballIndV v 0 0 x = ((({x : v.adicCompletion F | Valued.v (x - 0) ≤ exp (-(0 : ℤ))}.indicator
      fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
  by_cases hx : x ∈ {x : v.adicCompletion F | Valued.v (x - 0) ≤ exp (-(0 : ℤ))}
  · rw [ballIndV, Set.indicator_of_mem hx, Set.indicator_of_mem hx]; simp
  · rw [ballIndV, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

lemma gaussInfFun_eq_ofReal (x : V) :
    gaussInfFun x = ((Real.exp (-π * ‖gaussT (F := F) x‖ ^ 2) : ℝ) : ℂ) := by
  rw [← gaussInf_apply, gaussInf, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    gaussianSchwartz_apply, Complex.ofReal_exp]
  push_cast; ring_nf

/-- **$\Theta \ne 0$:** all terms are $\ge 0$ and the term $\gamma = 0$ is $1$. -/
theorem thetaGauss_ne_zero : thetaGauss F ≠ 0 := by
  set r : F → ℝ := fun γ => Real.exp (-π * ‖gaussT (F := F) (mixedEmbedding F γ)‖ ^ 2) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ({x : v.adicCompletion F | Valued.v (x - 0) ≤ exp (-(0 : ℤ))}.indicator
      fun _ => (1 : ℝ)) (algebraMap F (v.adicCompletion F) γ) with hr
  have hfinR : ∀ γ : F, Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ({x : v.adicCompletion F | Valued.v (x - 0) ≤ exp (-(0 : ℤ))}.indicator fun _ => (1 : ℝ))
        (algebraMap F (v.adicCompletion F) γ) := by
    intro γ
    refine (hasFiniteMulSupport_ballIndV γ).subset fun v hv h => hv ?_
    simp only at h ⊢
    rw [ballIndV_real] at h
    exact_mod_cast h
  have hterm : ∀ γ : F, gaussInf (mixedEmbedding F γ) *
      ∏ᶠ v, ballIndV v 0 0 (algebraMap F (v.adicCompletion F) γ) = (r γ : ℂ) := by
    intro γ
    rw [gaussInf_apply, gaussInfFun_eq_ofReal, hr]
    simp_rw [ballIndV_real]
    rw [Complex.ofReal_mul]
    congr 1
    exact (MonoidHom.map_finprod Complex.ofRealHom.toMonoidHom (hfinR γ)).symm
  have hsum := summable_adelicPoisson_factorizable_lhs (fun v => ballIndV v 0 0) ∅ (by simp)
    (fun v _ => rfl) (gaussInf (F := F))
  simp_rw [hterm] at hsum
  have hsumR : Summable r := Complex.summable_ofReal.mp hsum
  have hnn : ∀ γ, 0 ≤ r γ := fun γ => mul_nonneg (Real.exp_pos _).le
    (finprod_nonneg fun v => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have h0 : r 0 = 1 := by
    simp only [hr, map_zero, _root_.map_zero, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero, one_mul]
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [Set.indicator_of_mem]; simp
  have hle : 1 ≤ ∑' γ, r γ := by rw [← h0]; exact hsumR.le_tsum 0 fun γ _ => hnn γ
  unfold thetaGauss
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum]
  exact_mod_cast (lt_of_lt_of_le one_pos hle).ne'

/-! ### The local test functions -/

/-- $g_v(x) = \psi_v(bx^2)\,\widehat{\mathbf 1_{\mathcal O_v}}(x)$. -/
def gV (b : F) (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : ℂ :=
  (psiV v (algebraMap F (v.adicCompletion F) b * x ^ 2) : ℂ) * fourierV v (ballIndV v 0 0) x

/-- $h_v(x) = \mathbf 1_{\mathcal O_v}(x)\,\psi_v(cx^2)$. -/
def hV (c : F) (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : ℂ :=
  ballIndV v 0 0 x * (psiV v (algebraMap F (v.adicCompletion F) c * x ^ 2) : ℂ)

lemma gV_eq (b : F) (v : HeightOneSpectrum (𝓞 F)) :
    gV b v = fun x => ((selfDualV v).real (latticeV v 0) : ℂ) *
      (ballIndV v 0 (-0 - diffExp v) x * (psiV v (algebraMap F (v.adicCompletion F) b * x ^ 2) : ℂ)) := by
  ext x
  rw [gV, fourierV_ballIndV_eq]
  simp only [zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  ring

lemma isSchwartzBruhatV_gV (b : F) (v : HeightOneSpectrum (𝓞 F)) : IsSchwartzBruhatV v (gV b v) := by
  rw [gV_eq]
  exact (isSchwartzBruhatV_chirp v _ _).const_mul v _

lemma gV_eq_ballIndV (b : F) {v : HeightOneSpectrum (𝓞 F)} (hd : diffExp v = 0)
    (hb : Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1) : gV b v = ballIndV v 0 0 := by
  rw [gV_eq, hd, selfDualV_real_Ov_of_diffExp v hd]
  simp only [CharP.cast_eq_zero, sub_zero, neg_zero, Complex.ofReal_one, one_mul]
  exact ballIndV_mul_chirp_eq hb

/-! ### The product formula for the Weil constants -/

/-- **Weil's product formula** (unnormalized): for $b \in F^\times$,
$$\gamma_\infty(b)\prod_v\gamma_v(b) = 1,$$
where $\gamma_v(b) = \int_{\|x\|_v \le R}\psi_v(bx^2)\,dx_v$ ($R \gg 0$, self-dual measure) at the finite places and
$\gamma_\infty(b) = \prod_{w\ \mathrm{real}}(i/(2b_w))^{1/2}\prod_{w\ \mathrm{complex}}(2|b_w|)^{-1}$. Equivalently, Weil's
index $\prod_v\gamma_v(b)/|\gamma_v(b)| = 1$ (the moduli multiply to $|2b|_{\mathbb A}^{-1/2} = 1$). -/
@[kb "weil1964" "§28, Thm. 6 (the Weil index is trivial on $F$) [unverified]"]
theorem weilInf_mul_finprod_weilV (b : F) (hb : b ≠ 0) :
    weilInf (mixedEmbedding F b) * ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) b) = 1 := by
  set B : V := mixedEmbedding F b with hB
  set c : F := -(4 * b)⁻¹ with hc
  have hc0 : c ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) hb))
  have h2c : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc0
  have hC : mixedEmbedding F c = -(4 * B)⁻¹ := by
    rw [hc, map_neg, mixedEmbedding_inv, map_mul, map_ofNat]
  have hcv : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap F (v.adicCompletion F) c = -(4 * algebraMap F (v.adicCompletion F) b)⁻¹ := by
    intro v; rw [hc, map_neg, map_inv₀, map_mul, map_ofNat]
  have hFΦ : fourierInf (gaussInf (F := F) : V → ℂ) = gaussInfFun := by
    rw [show (gaussInf (F := F) : V → ℂ) = gaussInfFun from funext gaussInf_apply]
    exact fourierInf_gaussInfFun
  -- the exceptional sets
  set Sb : Finset (HeightOneSpectrum (𝓞 F)) :=
    (finite_support_diffExp.union (HeightOneSpectrum.Support.finite (𝓞 F) b)).toFinset
  set Sc : Finset (HeightOneSpectrum (𝓞 F)) := (HeightOneSpectrum.Support.finite (𝓞 F) c).toFinset
  have hout2 : ∀ v ∉ Sb, gV b v = ballIndV v 0 0 := by
    intro v hv
    simp only [Sb, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support, not_or, not_not] at hv
    exact gV_eq_ballIndV b (by exact_mod_cast hv.1) (valued_le_one_of_not_mem_support hv.2)
  have hout3 : ∀ v ∉ Sc, hV c v = ballIndV v 0 0 := by
    intro v hv
    simp only [Sc, Set.Finite.mem_toFinset] at hv
    exact ballIndV_mul_chirp_eq (valued_le_one_of_not_mem_support hv)
  -- the three Poisson formulas
  have P1 := adelicPoisson_factorizable (fun v => ballIndV v 0 0) ∅ (by simp) (fun v _ => rfl)
    (gaussInf (F := F))
  have P2 := adelicPoisson_factorizable (gV b) Sb (fun v _ => isSchwartzBruhatV_gV b v) hout2
    (chirpGauss B)
  have P3 := adelicPoisson_factorizable (hV c) Sc (fun v _ => isSchwartzBruhatV_chirp v 0 _) hout3
    (chirpGauss (mixedEmbedding F c))
  -- `Θ` is the left side of `P2`
  have E1 : thetaGauss F = ∑' γ : F, chirpGauss B (mixedEmbedding F γ) *
      ∏ᶠ v, gV b v (algebraMap F (v.adicCompletion F) γ) := by
    rw [thetaGauss, P1, hFΦ]
    congr 1; ext γ
    rw [chirpGauss_apply]
    simp only [gV]
    rw [finprod_mul_distrib (hasFiniteMulSupport_psiV_coe (b * γ ^ 2) |>.subset fun v hv => by
      simpa [map_mul, map_pow] using hv) (hasFiniteMulSupport_fourierV_ballIndV γ)]
    have hpsi := psiInf_mul_finprod_psiV (b * γ ^ 2)
    simp only [map_mul, map_pow] at hpsi
    rw [show B * mixedEmbedding F γ * mixedEmbedding F γ = mixedEmbedding F b * mixedEmbedding F γ ^ 2 by
      rw [hB]; ring]
    linear_combination (-(gaussInfFun (mixedEmbedding F γ)) *
      ∏ᶠ v, fourierV v (ballIndV v 0 0) (algebraMap F (v.adicCompletion F) γ)) * hpsi
  -- the transform side of `P2`, termwise
  set Λ : ℂ := weilInf B * ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) b) with hΛ
  set H : F → ℂ := fun η => fourierInf (chirpGauss (mixedEmbedding F c)) (mixedEmbedding F η) *
    ∏ᶠ v, fourierV v (hV c v) (algebraMap F (v.adicCompletion F) η) with hH
  have E2 : ∀ γ : F, fourierInf (chirpGauss B) (mixedEmbedding F γ) *
      ∏ᶠ v, fourierV v (gV b v) (algebraMap F (v.adicCompletion F) γ) = Λ * H (2 * c * γ) := by
    intro γ
    have hchB : (chirpGauss B : V → ℂ) = fun x => (psiInf (B * x * x) : ℂ) * fourierInf gaussInfFun x := by
      ext x; rw [chirpGauss_apply, fourierInf_gaussInfFun]
    have hchC : (chirpGauss (mixedEmbedding F c) : V → ℂ) = fun x =>
        gaussInfFun x * (psiInf (-(4 * B)⁻¹ * x * x) : ℂ) := by
      ext x; rw [chirpGauss_apply, hC, mul_comm]
    rw [hchB, weilInf_identity (mixedEmbedding_fst_ne_zero hb) (mixedEmbedding_snd_ne_zero hb)]
    have hloc : ∀ v : HeightOneSpectrum (𝓞 F), fourierV v (gV b v) (algebraMap F (v.adicCompletion F) γ) =
        weilV v (algebraMap F (v.adicCompletion F) b) *
          (psiV v (algebraMap F (v.adicCompletion F) (c * γ ^ 2)) : ℂ) *
            fourierV v (hV c v) (algebraMap F (v.adicCompletion F) (2 * c * γ)) := by
      intro v
      have hbv : algebraMap F (v.adicCompletion F) b ≠ 0 := (map_ne_zero _).mpr hb
      have := weilV_identity v hbv (algebraMap F (v.adicCompletion F) γ)
      rw [show gV b v = fun x => (psiV v (algebraMap F (v.adicCompletion F) b * x ^ 2) : ℂ) *
        fourierV v (ballIndV v 0 0) x from rfl, this, ← hcv v]
      simp only [map_mul, map_pow, map_ofNat]
      rfl
    simp_rw [hloc]
    have hfw : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        weilV v (algebraMap F (v.adicCompletion F) b) := finite_weilV_ne_one b hb
    have hfwp : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        weilV v (algebraMap F (v.adicCompletion F) b) *
          (psiV v (algebraMap F (v.adicCompletion F) (c * γ ^ 2)) : ℂ) :=
      hfw.mul (hasFiniteMulSupport_psiV_coe (c * γ ^ 2))
    have hfh : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        fourierV v (hV c v) (algebraMap F (v.adicCompletion F) (2 * c * γ)) :=
      hasFiniteMulSupport_fourierV_chirp c (2 * c * γ)
    rw [finprod_mul_distrib hfwp hfh,
      finprod_mul_distrib hfw (hasFiniteMulSupport_psiV_coe (c * γ ^ 2))]
    have hpsi := psiInf_mul_finprod_psiV (c * γ ^ 2)
    rw [hH, hchC]
    simp only
    rw [show -(4 * B)⁻¹ * mixedEmbedding F γ * mixedEmbedding F γ = mixedEmbedding F (c * γ ^ 2) by
        rw [map_mul, map_pow, hC]; ring,
      show 2 * -(4 * B)⁻¹ * mixedEmbedding F γ = mixedEmbedding F (2 * c * γ) by
        rw [map_mul, map_mul, map_ofNat, hC]]
    rw [hΛ]
    linear_combination (weilInf B * (∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) b)) *
      (fourierInf (fun x => gaussInfFun x * (psiInf (-(4 * B)⁻¹ * x * x) : ℂ))
        (mixedEmbedding F (2 * c * γ)) *
      ∏ᶠ v, fourierV v (hV c v) (algebraMap F (v.adicCompletion F) (2 * c * γ)))) * hpsi
  -- the left side of `P3` is `Θ`
  have E3 : ∑' γ : F, chirpGauss (mixedEmbedding F c) (mixedEmbedding F γ) *
      ∏ᶠ v, hV c v (algebraMap F (v.adicCompletion F) γ) = thetaGauss F := by
    rw [thetaGauss]
    congr 1; ext γ
    rw [chirpGauss_apply, gaussInf_apply]
    simp only [hV]
    rw [finprod_mul_distrib (hasFiniteMulSupport_ballIndV γ) (hasFiniteMulSupport_psiV_coe (c * γ ^ 2)
      |>.subset fun v hv => by simpa [map_mul, map_pow] using hv)]
    have hpsi := psiInf_mul_finprod_psiV (c * γ ^ 2)
    simp only [map_mul, map_pow] at hpsi
    rw [show mixedEmbedding F c * mixedEmbedding F γ * mixedEmbedding F γ =
      mixedEmbedding F c * mixedEmbedding F γ ^ 2 by ring]
    linear_combination (gaussInfFun (mixedEmbedding F γ) *
      ∏ᶠ v, ballIndV v 0 0 (algebraMap F (v.adicCompletion F) γ)) * hpsi
  -- reindexing `γ ↦ 2cγ`
  have E4 : ∑' γ : F, H (2 * c * γ) = ∑' γ : F, H γ :=
    (Equiv.mulLeft₀ (2 * c) h2c).tsum_eq H
  have key : thetaGauss F = Λ * thetaGauss F := by
    calc thetaGauss F = ∑' γ : F, Λ * H (2 * c * γ) := by
          rw [E1, P2]; exact tsum_congr E2
      _ = Λ * ∑' γ : F, H γ := by rw [tsum_mul_left, E4]
      _ = Λ * thetaGauss F := by rw [← E3, P3]
  have := thetaGauss_ne_zero (F := F)
  have h1 : (Λ - 1) * thetaGauss F = 0 := by rw [sub_mul, ← key, one_mul, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right this)

end

end QuadFormsKB.Analysis
