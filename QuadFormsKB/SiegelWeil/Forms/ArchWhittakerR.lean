/-
# The archimedean Whittaker integral of degree $r$ is the archimedean density of forms by forms

**Layer:** local, one real place; classical analysis on $\mathbb R^{N\times r}$ and on the space $\mathrm{Sym}_r(\mathbb R)$ of real
symmetric matrices (no global input).

**Setting.** $Q = \sum_{i<N}s_ix_i^2$ on $\mathbb R^N$, $s_i > 0$, Gram matrix $S = \operatorname{diag}(s)$, $N = 2k$; $Z \in \mathbb H_r$
(`WeilRep.Genus.siegelH r`). Symmetric matrices are written in upper coordinates $t = (t_{ij})_{0\le i\le j<r}$ (`symU t`), with
Lebesgue measure $dt = \prod_{i\le j}dt_{ij}$; $\operatorname{tr}(tW) = \sum_{a,b}t_{ab}W_{ba}$ (`trU`). $G_S(W) = \int_{\mathbb R^{N\times r}}
e^{2\pi i\operatorname{tr}(X^{\mathsf T}SXW)}dX$ (`gaussR`); in the Schrödinger model the archimedean big-cell section of the Gaussian is
$f_\infty(wn(B)g_Z) = \gamma_V^rc_B^r\det(Y)^{N/4}G_S(Z + B)$ (as for $r = 1$ in the degree-one theory), so the integral below is the archimedean Whittaker
integral $W_{T,\infty}(g_Z)$ up to these constants.

**Results.**
* `fourier_inversion_pi`: Fourier inversion on $\mathbb R^\iota$ with the dot product (Mathlib's theorem, transported from the Euclidean
  space);
* `gaussR_eq_gram`: $G_S(W) = \det(S)^{-r/2}\int\rho_{N,r}(t)e^{2\pi i\operatorname{tr}(tW)}dt$, $\rho_{N,r}$ the density of the Gram map
  (`densRect`, `ArchGram.lean`);
* `integrable_gram`, `integrable_gaussR_add`: the two integrability conditions of Fourier inversion;
* **`archWhittakerR_eq`** (Siegel's computation of the archimedean factor, degree $r$): for $k > r$ (i.e. $N > 2r$),
  $$\int_{\mathrm{Sym}_r(\mathbb R)}G_S(Z + B)e^{-2\pi i\operatorname{tr}(TB)}dB = \beta_\infty(Q, T)\,e^{2\pi i\operatorname{tr}(TZ)}$$
  for $T$ positive definite, and $0$ otherwise; $\beta_\infty$ = `Tamagawa.Frames.archDensityForm` (Siegel's archimedean density of forms
  by forms, the one in `siegelForms_eq_whittaker`). For $r = 1$ this is the degree-one `SiegelWeil.archWhittaker_eq` (there $k \ge 2$).

**Range.** $k > r$ ($N > 2r$) is Siegel's range, and it is sharp: it is exactly the range in which $B \mapsto G_S(Z + B)
\propto\det(Z + B)^{-k}$ is integrable over $\mathrm{Sym}_r(\mathbb R)$ (Hua's integral, `integrable_inv_norm_det_pow_sharp` in
`ArchHua.lean`; the first version of this file had $k > r(r+1)/2$ from the crude bound of `ArchDetBound.lean`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935), §§ on the archimedean factor
[unverified]; Siegel, *Einführung in die Theorie der Modulfunktionen n-ten Grades*, Math. Ann. 116 (1939), §6 [unverified]; Kudla,
*Some extensions of the Siegel–Weil formula* (2008), §1 [unverified]; Shimura, *Confluent hypergeometric functions on tube domains*,
Math. Ann. 260 (1982), §1 (the integral of $\det(Y+iX)^{-k}e(-\operatorname{tr}TX)$) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.ArchGaussR
import QuadFormsKB.SiegelWeil.Forms.ArchGram
import QuadFormsKB.SiegelWeil.Forms.ArchGramCont
import QuadFormsKB.SiegelWeil.Forms.ArchDetBound
import QuadFormsKB.SiegelWeil.Forms.ArchHua
import QuadFormsKB.SiegelWeil.Forms.ArchSymCoord
import QuadFormsKB.Tamagawa.FrameArch

open MeasureTheory Matrix Complex
open scoped Real FourierTransform RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open WeilRep.Genus QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Hanke2005.ArchReal

/-! ### Fourier inversion on $\mathbb R^\iota$ with the dot product -/

/-- **Fourier inversion on $\mathbb R^\iota$** (Mathlib's inversion theorem on the Euclidean space, transported to the coordinate space
with the dot product $\langle v, w\rangle = \sum_iv_iw_i$): if $h$ is integrable, continuous at $T$, and
$\check h(w) = \int e^{2\pi i\langle v, w\rangle}h(v)\,dv$ is integrable, then $\int e^{-2\pi i\langle T, w\rangle}\check h(w)\,dw = h(T)$. -/
theorem fourier_inversion_pi {ι : Type*} [Fintype ι] {h : (ι → ℝ) → ℂ} (hi : Integrable h)
    (hF : Integrable fun w : ι → ℝ => ∫ v : ι → ℝ, cexp (2 * π * I * ∑ i, (v i : ℂ) * w i) * h v)
    {T : ι → ℝ} (hc : ContinuousAt h T) :
    ∫ w : ι → ℝ, cexp (-2 * π * I * ∑ i, (T i : ℂ) * w i) *
      ∫ v : ι → ℝ, cexp (2 * π * I * ∑ i, (v i : ℂ) * w i) * h v = h T := by
  set E := EuclideanSpace ℝ ι
  set e : (ι → ℝ) ≃ᵐ E := MeasurableEquiv.toLp 2 (ι → ℝ)
  have he : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp ι
  set h' : E → ℂ := fun x => h (e.symm x)
  have hinner : ∀ (v w : ι → ℝ), ⟪e v, e w⟫ = ∑ i, v i * w i := by
    intro v w
    simp only [e, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinv : ∀ w : ι → ℝ, 𝓕⁻ h' (e w) = ∫ v : ι → ℝ, cexp (2 * π * I * ∑ i, (v i : ℂ) * w i) * h v := by
    intro w
    rw [Real.fourierInv_eq', ← he.integral_comp e.measurableEmbedding]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [h', MeasurableEquiv.symm_apply_apply, hinner, smul_eq_mul]
    congr 1; push_cast; ring_nf
  set F : (ι → ℝ) → ℂ := fun w => ∫ v : ι → ℝ, cexp (2 * π * I * ∑ i, (v i : ℂ) * w i) * h v
  have hinv' : 𝓕⁻ h' = fun x => F (e.symm x) := by
    funext x
    have := hinv (e.symm x)
    rwa [MeasurableEquiv.apply_symm_apply] at this
  have hiF : Integrable (𝓕⁻ h') := by
    rw [hinv']
    exact (he.symm e).integrable_comp_emb e.symm.measurableEmbedding |>.mpr hF
  have hiF' : Integrable (𝓕 h') := by
    have : 𝓕 h' = fun x => 𝓕⁻ h' (-x) := by
      funext x; rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [this]; exact hiF.comp_neg
  have hi' : Integrable h' := (he.symm e).integrable_comp_emb e.symm.measurableEmbedding |>.mpr hi
  have hc' : ContinuousAt h' (e T) := by
    have hcont : Continuous e.symm := PiLp.continuous_ofLp 2 _
    exact ContinuousAt.comp (f := e.symm) (g := h) (by rw [e.symm_apply_apply]; exact hc) hcont.continuousAt
  have key := hi'.fourier_fourierInv_eq hiF' hc'
  rw [Real.fourier_eq', ← he.integral_comp e.measurableEmbedding] at key
  simp only [h', MeasurableEquiv.symm_apply_apply, hinv, hinner, smul_eq_mul] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  congr 1; push_cast
  rw [Finset.sum_congr rfl fun i _ => mul_comm (w i : ℂ) (T i)]; ring

/-! ### The Gaussian integral in Gram coordinates -/

/-- **The trace pairing** $\operatorname{tr}(t\,W) = \sum_{a,b}t_{ab}W_{ba}$ of the real symmetric matrix with upper coordinates $t$
(`symU t`) and a complex $r\times r$ matrix $W$. -/
def trU {r : ℕ} (t : UIdx r → ℝ) (W : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∑ a, ∑ b, ((symU t a b : ℝ) : ℂ) * W b a

lemma symU_gramH_diag {N r : ℕ} (s : Fin N → ℝ) (X : Fin r → Fin N → ℝ) (a b : Fin r) :
    symU (gramH (diagonal s) X) a b = ∑ i, s i * X a i * X b i := by
  by_cases h : a ≤ b
  · simp only [symU, Matrix.of_apply, dif_pos h, gramH, dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [symU, Matrix.of_apply, dif_neg h, gramH, dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma continuous_trU {r : ℕ} (W : Matrix (Fin r) (Fin r) ℂ) : Continuous fun t : UIdx r → ℝ => trU t W := by
  unfold trU
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  refine (Complex.continuous_ofReal.comp ?_).mul continuous_const
  simp only [symU, Matrix.of_apply]
  split_ifs <;> exact continuous_apply _

lemma gaussR_integrand_gram {N r : ℕ} (s : Fin N → ℝ) (W : Matrix (Fin r) (Fin r) ℂ) (X : Fin r → Fin N → ℝ) :
    cexp (2 * π * I * ∑ a, ∑ b, ((∑ i, s i * X a i * X b i : ℝ) : ℂ) * W b a) =
      cexp (2 * π * I * trU (gramH (diagonal s) X) W) := by
  simp only [trU, symU_gramH_diag]

lemma measurable_gramH_diag {N r : ℕ} (s : Fin N → ℝ) :
    Measurable (gramH (diagonal s) : (Fin r → Fin N → ℝ) → UIdx r → ℝ) := by
  refine measurable_pi_iff.2 fun p => ?_
  simp only [gramH, dotProduct, mulVec]
  fun_prop

/-- **$G_S$ in Gram coordinates** (from the rectangular Gram disintegration `map_gramRectH`): for $r \le N$, $s_i > 0$ and every
complex $r\times r$ matrix $W$,
$$G_S(W) = \det(S)^{-r/2}\int_{\mathrm{Sym}_r(\mathbb R)}\rho_{N,r}(t)\,e^{2\pi i\operatorname{tr}(tW)}\,dt,$$
$\rho_{N,r}$ = `densRect N r` (both sides are Bochner integrals; no integrability is needed for the identity). -/
theorem gaussR_eq_gram {N r : ℕ} (hr : r ≤ N) {s : Fin N → ℝ} (hs : ∀ i, 0 < s i) (W : Matrix (Fin r) (Fin r) ℂ) :
    gaussR s W = (((∏ i, s i) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
      ∫ t : UIdx r → ℝ, ((densRect N r t).toReal : ℂ) * cexp (2 * π * I * trU t W) := by
  have hH : (diagonal s).PosDef := posDef_diagonal_iff.2 hs
  have hg := gaussR_integrand_gram s W
  have hgm := measurable_gramH_diag (r := r) s
  have hc : Continuous fun t : UIdx r → ℝ => cexp (2 * π * I * trU t W) :=
    Complex.continuous_exp.comp (continuous_const.mul (continuous_trU W))
  unfold gaussR
  simp_rw [hg]
  rw [← integral_map hgm.aemeasurable hc.aestronglyMeasurable, map_gramRectH hr hH, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_densRect N r)
      (Filter.Eventually.of_forall fun t => (densRect_ne_top N r t).lt_top), det_diagonal,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (Finset.prod_nonneg fun i _ => (hs i).le) _), Complex.real_smul]
  simp only [Complex.real_smul]

/-- **The Gram-coordinate integrand is integrable:** $t \mapsto \rho_{N,r}(t)e^{2\pi i\operatorname{tr}(tZ)}$ is integrable on
$\mathrm{Sym}_r(\mathbb R)$ for $r \le N$, $Z \in \mathbb H_r$ (it is the push-forward of the integrable Gaussian `integrable_gaussR`). -/
theorem integrable_gram {N r : ℕ} (hr : r ≤ N) {s : Fin N → ℝ} (hs : ∀ i, 0 < s i) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) :
    Integrable fun t : UIdx r → ℝ => ((densRect N r t).toReal : ℂ) * cexp (2 * π * I * trU t Z) := by
  have hH : (diagonal s).PosDef := posDef_diagonal_iff.2 hs
  have hc : Continuous fun t : UIdx r → ℝ => cexp (2 * π * I * trU t Z) :=
    Complex.continuous_exp.comp (continuous_const.mul (continuous_trU Z))
  have hX := integrable_gaussR hs hZ
  simp_rw [gaussR_integrand_gram s Z] at hX
  have h1 := (integrable_map_measure hc.aestronglyMeasurable (measurable_gramH_diag s).aemeasurable).mpr hX
  have hpos : 0 < (diagonal s).det ^ (-(r : ℝ) / 2) := by
    rw [det_diagonal]; exact Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => hs i) _
  rw [map_gramRectH hr hH, integrable_smul_measure (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top,
    integrable_withDensity_iff_integrable_smul' (measurable_densRect N r)
      (Filter.Eventually.of_forall fun t => (densRect_ne_top N r t).lt_top)] at h1
  simpa only [Complex.real_smul] using h1

/-! ### The archimedean Whittaker integral -/

lemma trU_add {r : ℕ} (t : UIdx r → ℝ) (W W' : Matrix (Fin r) (Fin r) ℂ) :
    trU t (W + W') = trU t W + trU t W' := by
  simp only [trU, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma trU_symU {r : ℕ} (t b : UIdx r → ℝ) :
    trU t (cR (symU b)) = ∑ p, (t p : ℂ) * (scaleU r b p : ℂ) := by
  rw [show (∑ p, (t p : ℂ) * (scaleU r b p : ℂ)) = ∑ p, (t p : ℂ) * ((cU p * b p : ℝ) : ℂ) from rfl,
    ← trace_symU_symU]
  rfl

lemma add_symU_mem {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) (b : UIdx r → ℝ) :
    Z + cR (symU b) ∈ siegelH r := by
  refine ⟨?_, ?_⟩
  · rw [transpose_add, hZ.1, ← transpose_map, symU_transpose]
  · have : (Z + cR (symU b)).map Complex.im = Z.map Complex.im := by
      ext i j; simp
    rw [this]; exact hZ.2

/-- $G_S(Z + B)$ is integrable over $B \in \mathrm{Sym}_r(\mathbb R)$ when $N = 2k$, $k > r$ (from `gaussR_eq` and Hua's
`integrable_inv_norm_det_pow_sharp`). -/
theorem integrable_gaussR_add {k r : ℕ} (hk : r < k) {s : Fin (2 * k) → ℝ} (hs : ∀ i, 0 < s i)
    {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) :
    Integrable fun b : UIdx r → ℝ => gaussR s (Z + cR (symU b)) := by
  have he : ∀ b : UIdx r → ℝ, gaussR s (Z + cR (symU b)) =
      (((∏ i, (Real.sqrt (s i) ^ r)⁻¹ : ℝ) : ℂ) * (((-2 * I) ^ r)⁻¹) ^ k) * ((Z + cR (symU b)).det)⁻¹ ^ k := by
    intro b
    rw [gaussR_eq s hs (add_symU_mem hZ b), det_smul, Fintype.card_fin, mul_inv, mul_pow]; ring
  simp_rw [he]
  refine Integrable.const_mul ?_ _
  refine (integrable_inv_norm_det_pow_sharp hk hZ).mono'
    (((continuous_det_add_symU Z).measurable.inv.pow_const k).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun b => by rw [norm_pow, norm_inv]

open scoped Classical in
/-- **The archimedean Whittaker integral of degree $r$** (Siegel's computation of $\beta_\infty(Q, T)$, degree $r$): for
$Q = \sum_{i<N}s_ix_i^2$ with $s_i > 0$, $N = 2k$, $k > r$, $Z \in \mathbb H_r$ and $T$ a real symmetric $r\times r$ matrix in upper
coordinates,
$$\int_{\mathrm{Sym}_r(\mathbb R)}G_S(Z + B)\,e^{-2\pi i\operatorname{tr}(TB)}\,dB = \begin{cases}\beta_\infty(Q, T)\,e^{2\pi i\operatorname{tr}(TZ)}, & T > 0,\\
  0, & \text{otherwise,}\end{cases}$$
$dB = \prod_{i\le j}dB_{ij}$, $\beta_\infty(Q,T)$ = `Tamagawa.Frames.archDensityForm N r (∏ s_i) (det T)`
$= 2^{-r(r-1)/2}\prod_{i<r}\frac{\pi^{(N-i)/2}}{\Gamma(\frac{N-i}2)}\det(T)^{(N-r-1)/2}\det(S)^{-r/2}$ (Siegel's archimedean density of forms by forms,
in the coefficient coordinates of the repository; the factor $2^{-r(r-1)/2}$ appears here as the Jacobian of $B \mapsto (c_{ij}B_{ij})$,
$c_{ij} = 2$ off the diagonal). For $r = 1$ this is the degree-one `SiegelWeil.archWhittaker_eq`. *Proof:* $G_S(Z + B)$ is the inverse Fourier
transform of $h(t) = \det(S)^{-r/2}\rho_{N,r}(t)e^{2\pi i\operatorname{tr}(tZ)}$ (`gaussR_eq_gram`), and Fourier inversion
(`fourier_inversion_pi`) applies: $h$ is integrable (`integrable_gram`) and continuous (`continuousAt_densRect_mul`, $N > r + 1$),
$G_S(Z + \cdot)$ is integrable (`integrable_gaussR_add`, which needs $k > r$, Hua's integral). -/
@[kb "siegel1935" "the archimedean factor of the Fourier coefficients, forms by forms [unverified]"]
theorem archWhittakerR_eq {k r : ℕ} (hk : r < k) {s : Fin (2 * k) → ℝ} (hs : ∀ i, 0 < s i)
    {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) (T : UIdx r → ℝ) :
    ∫ b : UIdx r → ℝ, gaussR s (Z + cR (symU b)) * cexp (-2 * π * I * trU T (cR (symU b))) =
      if PDU T then (Tamagawa.Frames.archDensityForm (2 * k) r (∏ i, s i) (symU T).det : ℂ) *
        cexp (2 * π * I * trU T Z) else 0 := by
  have hrk : r < k := hk
  have hrN : r ≤ 2 * k := by omega
  have hrN' : r + 1 < 2 * k := by omega
  set C : ℂ := (((∏ i, s i) ^ (-(r : ℝ) / 2) : ℝ) : ℂ)
  set h : (UIdx r → ℝ) → ℂ := fun t => ((densRect (2 * k) r t).toReal : ℂ) * cexp (2 * π * I * trU t Z)
  set Fh : (UIdx r → ℝ) → ℂ := fun w => ∫ v : UIdx r → ℝ, cexp (2 * π * I * ∑ p, (v p : ℂ) * w p) * h v
  have hC : C ≠ 0 := by
    simp only [C, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => hs i) _).ne'
  have key1 : ∀ b, gaussR s (Z + cR (symU b)) = C * Fh (scaleU r b) := by
    intro b
    rw [gaussR_eq_gram hrN hs]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [h, trU_add, trU_symU, mul_add, Complex.exp_add]
    push_cast
    ring
  have hFh : Integrable Fh := by
    rw [← integrable_comp_scaleU_iff]
    have := (integrable_gaussR_add hk hs hZ).const_mul C⁻¹
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    rw [key1, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  have hih : Integrable h := integrable_gram hrN hs hZ
  have hch : ContinuousAt h T :=
    continuousAt_densRect_mul hrN' (Complex.continuous_exp.comp (continuous_const.mul (continuous_trU Z))).continuousAt
  have hinv := fourier_inversion_pi hih hFh hch
  have e1 : ∀ b, gaussR s (Z + cR (symU b)) * cexp (-2 * π * I * trU T (cR (symU b))) =
      C * ((fun w => cexp (-2 * π * I * ∑ p, (T p : ℂ) * w p) * Fh w) (scaleU r b)) := by
    intro b
    rw [key1, trU_symU]; ring
  simp_rw [e1]
  have hsc := integral_comp_scaleU (fun w => cexp (-2 * π * I * ∑ p, (T p : ℂ) * w p) * Fh w)
  rw [integral_const_mul, hsc, hinv, Complex.real_smul]
  simp only [h]
  by_cases hT : PDU T
  · have hp : piv r T := piv_of_PDU r T hT
    obtain ⟨hdet, hd⟩ := densRect_of_piv (2 * k) r T hrN hp
    rw [if_pos hT, hd, ENNReal.toReal_ofReal (mul_nonneg (cprodRect_pos hrN).le (Real.rpow_nonneg hdet.le _))]
    unfold Tamagawa.Frames.archDensityForm cprodRect kap
    simp only [C]
    have hprod : ∏ j ∈ Finset.range r, Real.pi ^ ((((2 * k) - j : ℕ) : ℝ) / 2) / Real.Gamma ((((2 * k) - j : ℕ) : ℝ) / 2) =
        ∏ i ∈ Finset.range r, Real.pi ^ ((((2 * k : ℕ) : ℝ) - i) / 2) / Real.Gamma ((((2 * k : ℕ) : ℝ) - i) / 2) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Nat.cast_sub (by have := Finset.mem_range.mp hj; omega)]
    rw [hprod]
    push_cast
    ring
  · rw [if_neg hT, densRect_eq_zero_of_not_piv (2 * k) r T (fun hp => hT (PDU_of_piv r T hp))]
    simp

end QuadFormsKB.SiegelWeil.Forms.ArchR
