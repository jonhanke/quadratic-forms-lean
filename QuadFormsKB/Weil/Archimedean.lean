/-
# The Weil representation at the infinite places

**Layer:** local, archimedean, for any number field $F$: the block $F_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$
(`mixedSpace F`) with the local data `localDataInf` of `Weil/Global.lean` ($\psi_\infty = e\circ\operatorname{Tr}_\infty$, the
self-dual measure, $|t|_\infty$, $\gamma_\infty$ = `weilInf`, $(\cdot,\cdot)_\infty$ = `hilbInf`, Schwartz functions).

**Purpose.** The inputs for `(localDataInf).IsModel` (all axioms of `LocalData.IsModel` at infinity), which is assembled
in `Weil/ArchimedeanWeil.lean` (`isModel_inf`, with the Weil identity for every Schwartz function) and gives the
archimedean Weil representation
$$\omega_\infty : \mathrm{SL}_2(k) \to \operatorname{End}_{\mathbb C}S(V_\infty)\qquad(\texttt{weilRepInf})$$
for every field $k \to F_\infty$ (e.g. $k = F$), a genuine representation (no cocycle; $n$ even).

**The ingredients.**
* *Coordinates.* $S : F_\infty \to E$ (`Sinf`), $E$ = `euclidean.mixedSpace F` (a real inner product space), scales the
  complex coordinates by $\sqrt2$; it carries the self-dual measure to Lebesgue measure (`measurePreserving_Sinf`,
  from $\det = 2^{r_2}$), and $\operatorname{Tr}_\infty(xy) = \langle Sx, S\bar y\rangle$ (`traceInf_mul_eq_inner`), $\bar y$ = conjugation
  at the complex places (`conjC`). Hence $\hat f = (\mathcal F_E(f\circ S^{-1}))\circ(-S\,\overline{\,\cdot\,})$
  (`fourierInf_eq_fourier`), with Mathlib's Fourier transform $\mathcal F_E$ on $E$.
* `fourierInf_mem_schwartzInf`: **the Fourier transform of a Schwartz function is Schwartz** (`SchwartzMap.fourierTransformCLM`).
* `fourierInf_fourierInf`: **Fourier inversion** $\hat{\hat f}(x) = f(-x)$ (Mathlib's `fourierInv_fourier_eq`, and the
  isometry $u \mapsto -S\overline{S^{-1}u}$ of $E$).
* `fourierInf_dil`: $\widehat{D_tf} = |t|_\infty^{-1}D_{t^{-1}}\hat f$ ($\det(x \mapsto tx) = \prod_{w\ \mathrm{real}}t_w\prod_{w\ \mathrm{complex}}|t_w|^2$).
* `weilInf_mul_sq`, `weilInf_mul`: (S) $\gamma_\infty(ts^2) = |s|_\infty^{-1}\gamma_\infty(t)$ and (H)
  $\gamma_\infty(st)\gamma_\infty(1) = (s,t)_\infty\gamma_\infty(s)\gamma_\infty(t)$ on all units of $F_\infty$.
* `isOps_inf`: the operator axioms (Schwartz space stable under chirps, dilations and $\mathcal F$; the Hilbert symbol
  `hilbInf` on units).
* The Weil identity for every Schwartz function: `weilInf_identity_schwartz` in `Weil/ArchimedeanWeil.lean`.

**Why $F_\infty$ as a whole.** The global data `GDatum` and the theta distribution use $F_\infty$ as one block,
and every identity above is proved through the product structure (Fubini over the places, or the Euclidean
coordinates $E$), so nothing is gained by splitting; the representation of $\mathrm{SL}_2(F_\infty)$ itself (rather than of
$\mathrm{SL}_2(k)$ for fields $k \to F_\infty$) still needs the presentation for a product of fields (gap 4, open).

Sources: Weil, Acta Math. 111 (1964), §§14, 26 [unverified]; Kudla, *Notes on the local theta correspondence*
(1996), §I.1 [unverified]; Tate's thesis (Cassels–Fröhlich Ch. XV, §2.2, Thm. 2.2.2, p. 310; the dilation formula as in the proof of
Thm. 4.2.1, p. 333).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.ThetaKernel
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open QuadFormsKB.Analysis
open scoped Classical MatrixGroups FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

variable {F : Type} [Field F] [NumberField F]

local notation "V∞" => mixedSpace F
local notation "E∞" => euclidean.mixedSpace F

/-! ### Euclidean coordinates on $F_\infty$ -/

/-- Scaling the complex coordinates by $\sqrt2$. -/
def scaleC : V∞ ≃L[ℝ] V∞ :=
  ((LinearEquiv.refl ℝ ({w : InfinitePlace F // IsReal w} → ℝ)).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ({w : InfinitePlace F // IsComplex w} → ℂ) (Real.sqrt 2)
      (by positivity))).toContinuousLinearEquiv

/-- **Euclidean coordinates** $S : F_\infty \to E$ = `euclidean.mixedSpace F`: the identity at the real places and
$\sqrt2$ times the identity at the complex places. -/
def Sinf : V∞ ≃L[ℝ] E∞ := scaleC.trans (euclidean.toMixed F).symm

/-- Complex conjugation at the complex places. -/
def conjC : V∞ ≃L[ℝ] V∞ :=
  ((LinearEquiv.refl ℝ ({w : InfinitePlace F // IsReal w} → ℝ)).prodCongr
    (LinearEquiv.piCongrRight fun _ => Complex.conjAe.toLinearEquiv)).toContinuousLinearEquiv

@[simp] lemma conjC_conjC (y : V∞) : conjC (conjC y) = y := by
  ext w <;> simp [conjC]

/-- $\operatorname{Tr}_\infty(xy) = \langle Sx, S\bar y\rangle_E$. -/
lemma traceInf_mul_eq_inner (x y : V∞) : traceInf (x * y) = inner ℝ (Sinf x) (Sinf (conjC y)) := by
  simp [Sinf, scaleC, conjC, euclidean.toMixed, traceInf, PiLp.inner_apply]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    linear_combination (-((x.2 w).re * (y.2 w).re - (x.2 w).im * (y.2 w).im)) * h

lemma scaleC_toLinearMap : (scaleC (F := F) : V∞ →ₗ[ℝ] V∞) =
    LinearMap.prodMap LinearMap.id (Real.sqrt 2 • LinearMap.id) := by
  apply LinearMap.ext; intro x
  rfl

lemma det_scaleC : LinearMap.det (scaleC (F := F) : V∞ →ₗ[ℝ] V∞) = 2 ^ nrComplexPlaces F := by
  rw [scaleC_toLinearMap, LinearMap.det_prodMap, LinearMap.det_id, LinearMap.det_smul, LinearMap.det_id,
    one_mul, mul_one, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [pow_mul', Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **$S$ carries the self-dual measure to Lebesgue measure on $E$.** -/
lemma measurePreserving_Sinf : MeasurePreserving (Sinf (F := F)) selfDualInf volume := by
  refine ⟨(Sinf (F := F)).continuous.measurable, ?_⟩
  have hdet : LinearMap.det (scaleC (F := F) : V∞ →ₗ[ℝ] V∞) ≠ 0 := by rw [det_scaleC]; positivity
  have h1 : Measure.map (scaleC (F := F)) (volume : Measure V∞) =
      ENNReal.ofReal |(LinearMap.det (scaleC (F := F) : V∞ →ₗ[ℝ] V∞))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have h2 : Measure.map (scaleC (F := F)) (selfDualInf (F := F)) = volume := by
    unfold selfDualInf
    rw [Measure.map_smul, h1, det_scaleC]
    have : ((2 : NNReal) ^ nrComplexPlaces F : ENNReal) * ENNReal.ofReal |((2 : ℝ) ^ nrComplexPlaces F)⁻¹| = 1 := by
      rw [abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
      push_cast
      rw [ENNReal.ofReal_ofNat]
      exact ENNReal.mul_inv_cancel (by positivity) (by simp)
    ext s hs
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, ← mul_assoc]
    rw [show (((2 : NNReal) ^ nrComplexPlaces F : NNReal) : ENNReal) = ((2 : NNReal) ^ nrComplexPlaces F : ENNReal)
      by push_cast; rfl, this, one_mul]
    exact (scaleC (F := F)).continuous.measurable.aemeasurable
  have h3 := (euclidean.volumePreserving_toMixed_symm F).map_eq
  show Measure.map ((euclidean.toMixed F).symm ∘ scaleC) selfDualInf = volume
  rw [← Measure.map_map (euclidean.toMixed F).symm.continuous.measurable scaleC.continuous.measurable, h2, h3]

/-! ### The Fourier transform in Euclidean coordinates -/

/-- $y \mapsto -S\bar y$. -/
def Tinf : V∞ ≃L[ℝ] E∞ := conjC.trans (Sinf.trans (ContinuousLinearEquiv.neg ℝ))

@[simp] lemma Tinf_apply (y : V∞) : Tinf y = -Sinf (conjC y) := rfl

/-- **$\hat f = \mathcal F_E(f\circ S^{-1})\circ T$**, $T(y) = -S\bar y$, $\mathcal F_E$ Mathlib's Fourier transform on $E$. -/
lemma fourierInf_eq_fourier (f : V∞ → ℂ) (y : V∞) :
    fourierInf f y = 𝓕 (f ∘ (Sinf (F := F)).symm) (Tinf y) := by
  have hmp := measurePreserving_Sinf (F := F)
  rw [fourierInf, Real.fourier_eq, ← hmp.integral_comp (Sinf (F := F)).toHomeomorph.measurableEmbedding
    (fun v => 𝐞 (-inner ℝ v (Tinf y)) • (f ∘ (Sinf (F := F)).symm) v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, Homeomorph.toMeasurableEquiv_coe,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, Tinf_apply, inner_neg_right, neg_neg,
    Circle.smul_def, smul_eq_mul, psiInf, traceInf_mul_eq_inner]
  ring

lemma fourierInf_coe_schwartz (G : SchwartzMap V∞ ℂ) :
    fourierInf (G : V∞ → ℂ) = ⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Tinf (F := F))
      (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Sinf (F := F)).symm G))) := by
  funext y
  rw [fourierInf_eq_fourier]
  rfl

/-- **The Fourier transform of a Schwartz function on $F_\infty$ is Schwartz.** -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, Thm. 2.2.2, p. 310 (Tate uses the class 𝔅₁, not Schwartz functions)"]
theorem fourierInf_mem_schwartzInf {f : V∞ → ℂ} (hf : f ∈ schwartzInf (F := F)) :
    fourierInf f ∈ schwartzInf (F := F) := by
  obtain ⟨G, rfl⟩ := hf
  exact ⟨_, (fourierInf_coe_schwartz G).symm⟩

lemma traceInf_conjC_mul (x y : V∞) : traceInf (conjC x * y) = traceInf (x * conjC y) := by
  simp only [traceInf, conjC]
  simp [Complex.mul_re]

/-- The isometry $u \mapsto -S\overline{S^{-1}u}$ of $E$. -/
def Jinf : E∞ ≃ₗᵢ[ℝ] E∞ :=
  LinearEquiv.isometryOfInner ((Sinf (F := F)).symm.trans Tinf).toLinearEquiv fun u v => by
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.trans_apply, Tinf_apply,
      inner_neg_neg]
    rw [← traceInf_mul_eq_inner, traceInf_conjC_mul, traceInf_mul_eq_inner, conjC_conjC]
    simp

lemma Jinf_Tinf (x : V∞) : Jinf (Tinf x) = Sinf x := by
  show Tinf ((Sinf (F := F)).symm (Tinf x)) = Sinf x
  simp only [Tinf_apply, map_neg, ContinuousLinearEquiv.symm_apply_apply, conjC_conjC, neg_neg]

/-- **Fourier inversion on $F_\infty$**: $\hat{\hat f}(x) = f(-x)$ for Schwartz $f$ (self-dual measure). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, Thm. 2.2.2, p. 310 (f̂̂(ξ) = f(−ξ))"]
theorem fourierInf_fourierInf {f : V∞ → ℂ} (hf : f ∈ schwartzInf (F := F)) (x : V∞) :
    fourierInf (fourierInf f) x = f (-x) := by
  obtain ⟨G, rfl⟩ := hf
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Sinf (F := F)).symm G with hg
  have h1 : fourierInf (G : V∞ → ℂ) ∘ (Sinf (F := F)).symm = (𝓕 (g : E∞ → ℂ)) ∘ Jinf := by
    funext u
    rw [fourierInf_coe_schwartz]
    rfl
  rw [fourierInf_eq_fourier, h1, Real.fourier_comp_linearIsometry, Jinf_Tinf]
  have h2 : 𝓕 (𝓕 (g : E∞ → ℂ)) (Sinf x) = g (-(Sinf x)) := by
    have h3 : 𝓕⁻ (𝓕 g) = g := FourierTransform.fourierInv_fourier_eq g
    have := congrArg (fun φ : SchwartzMap E∞ ℂ => φ (-(Sinf x))) h3
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg, SchwartzMap.fourier_coe] at this
    exact this
  rw [h2, hg]
  simp

/-! ### The modulus and dilations -/

/-- $|x|_\infty = \prod_{w\ \mathrm{real}}|x_w|\prod_{w\ \mathrm{complex}}|x_w|^2$. -/
lemma norm_eq_prod_prod (x : V∞) :
    mixedEmbedding.norm x = (∏ w : {w : InfinitePlace F // IsReal w}, |x.1 w|) *
      ∏ w : {w : InfinitePlace F // IsComplex w}, ‖x.2 w‖ ^ 2 := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2]

lemma unit_fst_ne_zero (t : (V∞)ˣ) (w : {w : InfinitePlace F // IsReal w}) : (t : V∞).1 w ≠ 0 := by
  intro h
  have := congrArg (fun z : V∞ => z.1 w) t.mul_inv
  simp only [Prod.fst_mul, Pi.mul_apply, h, zero_mul, Prod.fst_one, Pi.one_apply] at this
  exact zero_ne_one this

lemma unit_snd_ne_zero (t : (V∞)ˣ) (w : {w : InfinitePlace F // IsComplex w}) : (t : V∞).2 w ≠ 0 := by
  intro h
  have := congrArg (fun z : V∞ => z.2 w) t.mul_inv
  simp only [Prod.snd_mul, Pi.mul_apply, h, zero_mul, Prod.snd_one, Pi.one_apply] at this
  exact zero_ne_one this

/-- The determinant of $x \mapsto tx$ on $F_\infty$: $\prod_{w\ \mathrm{real}}t_w\prod_{w\ \mathrm{complex}}|t_w|^2$. -/
lemma det_mulLeft_inf (t : V∞) :
    LinearMap.det (LinearMap.mulLeft ℝ t) = (∏ w : {w : InfinitePlace F // IsReal w}, t.1 w) *
      ∏ w : {w : InfinitePlace F // IsComplex w}, Complex.normSq (t.2 w) := by
  have h1 : LinearMap.mulLeft ℝ t = LinearMap.prodMap
      (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (t.1 w)).comp (LinearMap.proj w))
      (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (t.2 w)).comp (LinearMap.proj w)) := by
    apply LinearMap.ext; intro x; rfl
  rw [h1, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => LinearMap.det_mulLeft _
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl

lemma abs_det_mulLeft_inf (t : V∞) :
    |LinearMap.det (LinearMap.mulLeft ℝ t)| = mixedEmbedding.norm t := by
  rw [det_mulLeft_inf, norm_eq_prod_prod, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.sq_norm]

/-- **Dilation:** $\widehat{D_tf}(y) = |t|_\infty^{-1}\hat f(t^{-1}y)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.2, proof of Thm. 4.2.1, p. 333 (ĝ(x) = |a|^{−1} f̂(x/a) for g(x) = f(ax)); Lemma 2.2.5, p. 310"]
theorem fourierInf_dil {f : V∞ → ℂ} (hf : f ∈ schwartzInf (F := F)) (t : (V∞)ˣ) (y : V∞) :
    fourierInf (dil (t : V∞) f) y =
      ((mixedEmbedding.norm (t : V∞) : ℝ) : ℂ)⁻¹ * fourierInf f (((t⁻¹ : (V∞)ˣ) : V∞) * y) := by
  obtain ⟨G, rfl⟩ := hf
  set L : V∞ →ₗ[ℝ] V∞ := LinearMap.mulLeft ℝ (t : V∞)
  have hdet : LinearMap.det L ≠ 0 := by
    rw [det_mulLeft_inf]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => unit_fst_ne_zero t w)
      (Finset.prod_ne_zero_iff.mpr fun w _ => Complex.normSq_pos.mpr (unit_snd_ne_zero t w) |>.ne')
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure V∞) hdet
  set g : V∞ → ℂ := fun x => G x * (psiInf (x * (((t⁻¹ : (V∞)ˣ) : V∞) * y)) : ℂ)
  have hg : Continuous g := G.continuous.mul (continuous_subtype_val.comp
    ((Real.continuous_fourierChar).comp (continuous_traceInf.comp (continuous_id.mul continuous_const))))
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have key : ∫ x, g (L x) = ENNReal.toReal (ENNReal.ofReal |(LinearMap.det L)⁻¹|) • ∫ x, g x := by
    rw [← integral_smul_measure, ← hmap, integral_map hL.measurable.aemeasurable hg.aestronglyMeasurable]
  unfold fourierInf selfDualInf
  rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  have e : ∀ x, dil (t : V∞) (G : V∞ → ℂ) x * (psiInf (x * y) : ℂ) = g (L x) := by
    intro x
    simp only [g, L, dil, LinearMap.mulLeft_apply]
    congr 3
    rw [show (t : V∞) * x * (↑t⁻¹ * y) = x * y * ((t : V∞) * ↑t⁻¹) by ring, Units.mul_inv, mul_one]
  simp only [e, key]
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_det_mulLeft_inf]
  simp only [NNReal.smul_def, Complex.real_smul]
  push_cast
  simp only [g, Units.val_inv_eq_inv_val]
  ring

/-! ### The Weil constant and the Hilbert symbol on units of $F_\infty$ -/

lemma weilR_mul_sq {t s : ℝ} (ht : t ≠ 0) (hs : s ≠ 0) : weilR (t * s ^ 2) = ((|s|)⁻¹ : ℝ) * weilR t := by
  have hs2 : (0 : ℝ) < (s ^ 2)⁻¹ := by positivity
  have e : Complex.I / (2 * ((t * s ^ 2 : ℝ) : ℂ)) = Complex.I / (2 * (t : ℂ)) * (((s ^ 2)⁻¹ : ℝ) : ℂ) := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast; field_simp
  have hu : 0 ≤ (Complex.I / (2 * (t : ℂ))).re := by
    rw [show Complex.I / (2 * (t : ℂ)) = ((1 / (2 * t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp
  have hu0 : Complex.I / (2 * (t : ℂ)) ≠ 0 :=
    div_ne_zero Complex.I_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast ht))
  unfold weilR
  rw [show (2 : ℂ) * ((t * s ^ 2 : ℝ) : ℂ) = 2 * ((t * s ^ 2 : ℝ) : ℂ) from rfl, e,
    cpow_mul_of_re hu hu0 (by rw [Complex.ofReal_re]; exact hs2)]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hs2.le,
    ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_sq_eq_abs]
  ring

lemma weilC_mul_sq (t s : ℂ) : weilC (t * s ^ 2) = ((‖s‖ ^ 2)⁻¹ : ℝ) * weilC t := by
  unfold weilC
  rw [norm_mul, norm_pow]
  push_cast
  ring

/-- **(S) at infinity:** $\gamma_\infty(ts^2) = |s|_\infty^{-1}\gamma_\infty(t)$ for units $t, s$ of $F_\infty$. -/
theorem weilInf_mul_sq (t s : (V∞)ˣ) :
    weilInf ((t : V∞) * (s : V∞) ^ 2) = ((mixedEmbedding.norm (s : V∞) : ℝ) : ℂ)⁻¹ * weilInf (t : V∞) := by
  rw [weilInf, weilInf, norm_eq_prod_prod]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Pi.mul_apply, Pi.pow_apply]
  rw [Finset.prod_congr rfl fun w _ => weilR_mul_sq (unit_fst_ne_zero t w) (unit_fst_ne_zero s w),
    Finset.prod_congr rfl fun w _ => weilC_mul_sq ((t : V∞).2 w) ((s : V∞).2 w),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  push_cast
  rw [mul_inv, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring

/-- **(H) at infinity:** $\gamma_\infty(st)\gamma_\infty(1) = (s,t)_\infty\gamma_\infty(s)\gamma_\infty(t)$. -/
theorem weilInf_mul (s t : (V∞)ˣ) :
    weilInf ((s : V∞) * (t : V∞)) * weilInf (1 : V∞) = (hilbInf (s : V∞) (t : V∞) : ℂ) * weilInf (s : V∞) * weilInf (t : V∞) := by
  have hR : ∀ w, weilR (((s : V∞) * (t : V∞)).1 w) * weilR ((1 : V∞).1 w) =
      (hilbertSymbol ℝ ((s : V∞).1 w) ((t : V∞).1 w) : ℂ) * weilR ((s : V∞).1 w) * weilR ((t : V∞).1 w) :=
    fun w => HN.weilR_mul_identity (unit_fst_ne_zero s w) (unit_fst_ne_zero t w)
  have hC : ∀ w, weilC (((s : V∞) * (t : V∞)).2 w) * weilC ((1 : V∞).2 w) =
      weilC ((s : V∞).2 w) * weilC ((t : V∞).2 w) := fun w => by
    have := HN.weilC_mul_identity ((s : V∞).2 w) ((t : V∞).2 w)
    rw [HN.hilbertSymbol_complex] at this
    simpa using this
  have e : weilInf ((s : V∞) * (t : V∞)) * weilInf (1 : V∞) = (∏ w, weilR (((s : V∞) * (t : V∞)).1 w) * weilR ((1 : V∞).1 w)) *
      ∏ w, weilC (((s : V∞) * (t : V∞)).2 w) * weilC ((1 : V∞).2 w) := by
    rw [weilInf, weilInf, Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
  rw [e, Finset.prod_congr rfl fun w _ => hR w, Finset.prod_congr rfl fun w _ => hC w, hilbInf, weilInf, weilInf]
  simp only [Finset.prod_mul_distrib]
  push_cast
  ring

lemma hilbInf_pm (s t : V∞) : hilbInf s t = 1 ∨ hilbInf s t = -1 := by
  unfold hilbInf
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun w _ =>
    HN.hilbertSymbol_eq_one_or ℝ _ _
  rintro a b (rfl | rfl) (rfl | rfl) <;> simp

/-! ### The axioms -/

lemma norm_unit_pos (t : (V∞)ˣ) : 0 < mixedEmbedding.norm (t : V∞) := by
  have h := congrArg mixedEmbedding.norm t.mul_inv
  rw [map_mul, map_one] at h
  refine lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) fun h0 => ?_
  rw [← h0, zero_mul] at h
  exact zero_ne_one h

lemma gaussInfFun_mem : gaussInfFun (F := F) ∈ schwartzInf (F := F) := ⟨gaussInf, funext gaussInf_apply⟩

/-- The operator axioms `IsOps` at infinity. -/
theorem isOps_inf : (localDataInf (F := F)).IsOps where
  sigmaFinite := by show SigmaFinite selfDualInf; unfold selfDualInf; infer_instance
  md_pos t := norm_unit_pos t
  md_mul s t := map_mul mixedEmbedding.norm _ _
  integrable_char f hf y := by
    obtain ⟨G, rfl⟩ := hf
    have hG : Integrable (G : V∞ → ℂ) (selfDualInf (F := F)) := by
      unfold selfDualInf; exact G.integrable.smul_measure_nnreal
    refine hG.norm.mono' (G.continuous.mul (continuous_subtype_val.comp ((Real.continuous_fourierChar).comp
      (continuous_traceInf.comp (continuous_id.mul continuous_const))))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖G x * (psiInf (x * y) : ℂ)‖ ≤ ‖G x‖
    rw [norm_mul, Circle.norm_coe, mul_one]
  chirp_mem f hf s := chirp_mem_schwartzInf s hf
  dil_mem f hf t := dil_mem_schwartzInf t hf
  four_mem f hf := fourierInf_mem_schwartzInf hf
  hilb_pm s t := hilbInf_pm (s : V∞) (t : V∞)
  hilb_comm s t := Finset.prod_congr rfl fun w _ => hilbertSymbol_comm _ _ _
  hilb_mul_left s s' t := by
    show hilbInf ((s : V∞) * (s' : V∞)) (t : V∞) = hilbInf (s : V∞) (t : V∞) * hilbInf (s' : V∞) (t : V∞)
    unfold hilbInf
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => HilbertLocal.hilbertSymbol_real_mul_left _ _ _ (unit_fst_ne_zero s w)
      (unit_fst_ne_zero s' w) (unit_fst_ne_zero t w)
  hilb_neg s := by
    show hilbInf (s : V∞) (-(s : V∞)) = 1
    exact Finset.prod_eq_one fun w _ => hilbertSymbol_self_neg _ _

end QuadFormsKB.WeilRep
