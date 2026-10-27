import QuadFormsKB.Tamagawa.Measure.Weil.TrdNormalization
import QuadFormsKB.Tamagawa.Measure.Weil.AdditivePoisson
import QuadFormsKB.Tamagawa.Measure.Weil.QuatFinite

/-!
# The $\psi_v\circ\operatorname{trd}$ self-dual measure on $\mathbb H_v$

$F$ a number field, $v$ a finite place, $\psi_v$ the standard character of $F_v$ (`Analysis.psiV`), $dx_v$ the
self-dual measure on $F_v$ (`selfDualV`), $\Delta_v = |\cdot|_v$ (`distribHaarChar`).

**Diagonal pairings on $F_v^4$.** For $g\in(F_v^\times)^4$ and a measure $\mu$ on $F_v^4$ let
$\mathcal F_{g,\mu}f(y) = \int f(x)\,\psi_v(\sum_ig_ix_iy_i)\,d\mu(x)$ and
$\mathcal F^{-}_{g,\mu}f(x) = \int f(y)\,\psi_v(-\sum_ig_ix_iy_i)\,d\mu(y)$ (`fourierDiag`, `fourierDiagInv`).

* **`fourierDiagInv_fourierDiag_boxInd`**: for $\mu = r\cdot dx_v^{\otimes4}$ and $f$ the indicator of a box
  $\prod_i(c_i + \mathfrak p_v^{k_i})$, $\mathcal F^-_{g,\mu}\mathcal F_{g,\mu}f = r^2\prod_i|g_i|_v^{-1}\cdot f$
  (Fubini over the product measure, the one-variable inversion `fourierInvV_fourierV_ballIndV` and the change of
  variables $s\mapsto g_is$, `integral_comp_mul_left`).
* **`selfDual_diag_iff`**: $\mu = r\,dx_v^{\otimes4}$ ($r\ge0$) is self-dual for the pairing (Fourier inversion holds on
  box indicators) **iff** $r = \prod_i|g_i|_v^{1/2} = |\det G|_v^{1/2}$, $G = \operatorname{diag}(g)$.

**Reduced trace.** On $\mathbb H_v = \mathbb H[F_v,a,b]$, $\operatorname{trd}(xy) = \sum_ig_ix_iy_i$ with
$g = (2, 2a, 2b, -2ab)$, the diagonal of the Gram matrix `trdGram` (`trd_mul_eq`).

* **`trdFourierInv_trdFourier`**: for $a, b\ne0$ and every finite place $v$, the measure
  $|\det G|_v^{1/2}\,dx$ (`trdSelfDualV`, $dx$ = `quatLocVol` the coordinate self-dual measure) satisfies Fourier inversion
  for $\psi_v(\operatorname{trd}(xy))$ on coordinate box indicators: **it is the $\psi_v\circ\operatorname{trd}$ self-dual
  measure** on $\mathbb H_v$; and it is the only multiple of $dx$ that does (`trdSelfDual_unique`).
* **Global identification** (**`finprod_trdFactor_mul_inf`**): $\prod_v|\det G|_v^{1/2}\cdot|\det G|_\infty^{1/2} = 1$
  ($\det G = -16a^2b^2\in F^\times$, product formula `ideleNorm_det_trdGram`): the product of the trace-self-dual local
  measures is the product of coordinate self-dual measures.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F

/-! ### Diagonal pairings on $F_v^4$ -/

/-- $\mathcal F_{g,\mu}f(y) = \int f(x)\,\psi_v(\sum_ig_ix_iy_i)\,d\mu(x)$. -/
def fourierDiag (μ : Measure (Fin 4 → Kv)) (g : Fin 4 → Kv) (f : (Fin 4 → Kv) → ℂ) (y : Fin 4 → Kv) : ℂ :=
  ∫ x, f x * (Analysis.psiV v (∑ i, g i * x i * y i) : ℂ) ∂μ

/-- $\mathcal F^-_{g,\mu}f(x) = \int f(y)\,\psi_v(-\sum_ig_ix_iy_i)\,d\mu(y)$. -/
def fourierDiagInv (μ : Measure (Fin 4 → Kv)) (g : Fin 4 → Kv) (f : (Fin 4 → Kv) → ℂ) (x : Fin 4 → Kv) : ℂ :=
  ∫ y, f y * (Analysis.psiV v (-(∑ i, g i * x i * y i)) : ℂ) ∂μ

/-- The indicator of the box $\prod_i(c_i + \mathfrak p_v^{k_i})\subseteq F_v^4$. -/
def boxInd (c : Fin 4 → Kv) (k : Fin 4 → ℤ) (x : Fin 4 → Kv) : ℂ := ∏ i, Analysis.ballIndV v (c i) (k i) (x i)

theorem psiV_sum_four (s : Fin 4 → Kv) : (Analysis.psiV v (∑ i, s i) : ℂ) = ∏ i, (Analysis.psiV v (s i) : ℂ) := by
  rw [Fin.sum_univ_four, Fin.prod_univ_four, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul]
  simp only [Circle.coe_mul]

/-- The (pi) coordinate self-dual measure $dx_v^{\otimes4}$. -/
abbrev volV4 : Measure (Fin 4 → Kv) := Measure.pi fun _ : Fin 4 => Analysis.selfDualV v

/-- **First transform of a box**: $\mathcal F_{g,r\,dx}\mathbf 1_{\mathrm{box}}(y) = r\prod_i\hat{\mathbf 1}_{c_i+\mathfrak p^{k_i}}(g_iy_i)$. -/
theorem fourierDiag_boxInd (r : ℝ) (hr : 0 ≤ r) (g : Fin 4 → Kv) (c : Fin 4 → Kv) (k : Fin 4 → ℤ)
    (y : Fin 4 → Kv) :
    fourierDiag v (ENNReal.ofReal r • volV4 v) g (boxInd v c k) y =
      r * ∏ i, Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * y i) := by
  unfold fourierDiag
  rw [integral_smul_measure, ENNReal.toReal_ofReal hr, Complex.real_smul]
  congr 1
  have hfun : (fun x : Fin 4 → Kv => boxInd v c k x * (Analysis.psiV v (∑ i, g i * x i * y i) : ℂ)) =
      fun x => ∏ i, (Analysis.ballIndV v (c i) (k i) (x i) * (Analysis.psiV v (x i * (g i * y i)) : ℂ)) := by
    funext x
    rw [boxInd, psiV_sum_four, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 3; ring
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun i t => Analysis.ballIndV v (c i) (k i) t * (Analysis.psiV v (t * (g i * y i)) : ℂ))
    (μ := fun _ : Fin 4 => Analysis.selfDualV v)
  rw [hfun]
  exact hprod

/-- **Fourier inversion for diagonal pairings on boxes, with the scale factor**:
$\mathcal F^-_{g,\mu}\mathcal F_{g,\mu}\mathbf 1_{\mathrm{box}} = r^2\prod_i|g_i|_v^{-1}\,\mathbf 1_{\mathrm{box}}$ for $\mu = r\,dx_v^{\otimes4}$. -/
theorem fourierDiagInv_fourierDiag_boxInd (r : ℝ) (hr : 0 ≤ r) (g : Fin 4 → Kv) (hg : ∀ i, g i ≠ 0)
    (c : Fin 4 → Kv) (k : Fin 4 → ℤ) :
    fourierDiagInv v (ENNReal.ofReal r • volV4 v) g (fourierDiag v (ENNReal.ofReal r • volV4 v) g (boxInd v c k)) =
      fun x => ((r ^ 2 * ∏ i, ((distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ))⁻¹ : ℝ) : ℂ) * boxInd v c k x := by
  funext x
  unfold fourierDiagInv
  simp_rw [fourierDiag_boxInd v r hr g c k]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hr, Complex.real_smul]
  have hfun : (fun y : Fin 4 → Kv => ((r : ℂ) * ∏ i, Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * y i)) *
      (Analysis.psiV v (-(∑ i, g i * x i * y i)) : ℂ)) =
      fun y => (r : ℂ) * ∏ i, (Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * y i) *
        (Analysis.psiV v (-(x i * (g i * y i))) : ℂ)) := by
    funext y
    rw [mul_assoc, ← neg_neg (∑ i, g i * x i * y i), neg_neg, ← Finset.sum_neg_distrib, psiV_sum_four,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 3; ring
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun i s => Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * s) *
      (Analysis.psiV v (-(x i * (g i * s))) : ℂ))
    (μ := fun _ : Fin 4 => Analysis.selfDualV v)
  rw [hfun, integral_const_mul]
  erw [hprod]
  have hfac : ∀ i, ∫ s, Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * s) *
      (Analysis.psiV v (-(x i * (g i * s))) : ℂ) ∂(Analysis.selfDualV v) =
      ((distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ))⁻¹ • Analysis.ballIndV v (c i) (k i) (x i) := by
    intro i
    have := integral_comp_mul_left (Analysis.selfDualV v) (Units.mk0 (g i) (hg i))
      (fun u => Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) u * (Analysis.psiV v (-(x i * u)) : ℂ))
    simp only [Units.val_mk0] at this
    rw [this]
    congr 1
    have h2 := congrFun (Analysis.fourierInvV_fourierV_ballIndV v (c i) (k i)) (x i)
    unfold Analysis.fourierInvV at h2
    exact h2
  simp_rw [hfac]
  rw [boxInd]
  simp only [Complex.real_smul, Finset.prod_mul_distrib]
  push_cast
  ring

/-- The factor $\prod_i|g_i|_v^{1/2}$ ($=|\det\operatorname{diag}(g)|_v^{1/2}$). -/
def diagFactor (g : Fin 4 → Kv) (hg : ∀ i, g i ≠ 0) : ℝ :=
  ∏ i, Real.sqrt (distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ)

theorem diagFactor_pos (g : Fin 4 → Kv) (hg : ∀ i, g i ≠ 0) : 0 < diagFactor v g hg :=
  Finset.prod_pos fun _ _ => Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (distribHaarChar_ne_zero _)))

theorem diagFactor_sq_mul (g : Fin 4 → Kv) (hg : ∀ i, g i ≠ 0) :
    diagFactor v g hg ^ 2 * ∏ i, ((distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ))⁻¹ = 1 := by
  rw [diagFactor, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Real.sq_sqrt (NNReal.coe_nonneg _), mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr (distribHaarChar_ne_zero _))]

/-- **Self-duality for a diagonal pairing**: $r\,dx_v^{\otimes4}$ ($r\ge0$) satisfies Fourier inversion on all box
indicators iff $r = \prod_i|g_i|_v^{1/2}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified] (self-dual measures)"]
theorem selfDual_diag_iff (g : Fin 4 → Kv) (hg : ∀ i, g i ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    (∀ c k, fourierDiagInv v (ENNReal.ofReal r • volV4 v) g
        (fourierDiag v (ENNReal.ofReal r • volV4 v) g (boxInd v c k)) = boxInd v c k) ↔
      r = diagFactor v g hg := by
  set P := ∏ i, ((distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ))⁻¹
  have hP : 0 < P := Finset.prod_pos fun i _ =>
    inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (distribHaarChar_ne_zero _)))
  have hD := diagFactor_sq_mul v g hg
  constructor
  · intro h
    have h1 := congrFun ((fourierDiagInv_fourierDiag_boxInd v r hr g hg 0 0).symm.trans (h 0 0)) 0
    have hb : boxInd v 0 0 (0 : Fin 4 → Kv) = 1 := by
      simp [boxInd, Analysis.ballIndV]
    rw [hb, mul_one] at h1
    have h2 : r ^ 2 * P = 1 := by exact_mod_cast h1
    have h3 : r ^ 2 = diagFactor v g hg ^ 2 := by
      have := hD.trans h2.symm
      exact (mul_right_cancel₀ hP.ne' this).symm
    exact (pow_left_inj₀ hr (diagFactor_pos v g hg).le two_ne_zero).mp h3
  · rintro rfl c k
    rw [fourierDiagInv_fourierDiag_boxInd v _ (diagFactor_pos v g hg).le g hg]
    funext x
    rw [hD]; simp

/-! ### The reduced trace on $\mathbb H_v$ -/

variable {v}

/-- The diagonal of the Gram matrix of $\operatorname{trd}(xy)$: $(2, 2a, 2b, -2ab)$. -/
def trdDiag {K : Type*} [CommRing K] (a b : K) : Fin 4 → K := ![2, 2 * a, 2 * b, -(2 * a * b)]

theorem trd_mul_eq {K : Type*} [Field K] (a b : K) (x y : QuatLoc a b) :
    2 * (x * y).re = ∑ i, trdDiag a b i * quatLocCoord a b x i * quatLocCoord a b y i := by
  have hx : quatLocCoord a b x = ![x.re, x.imI, x.imJ, x.imK] := by ext i; fin_cases i <;> rfl
  have hy : quatLocCoord a b y = ![y.re, y.imI, y.imJ, y.imK] := by ext i; fin_cases i <;> rfl
  rw [hx, hy, Fin.sum_univ_four]
  simp [trdDiag, QuaternionAlgebra.re_mul]
  ring

variable (v) in
theorem trdDiag_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 4) :
    trdDiag (algebraMap F Kv a) (algebraMap F Kv b) i ≠ 0 := by
  have h2 : (2 : Kv) ≠ 0 := by
    have : (2 : Kv) = algebraMap F Kv 2 := (map_ofNat _ 2).symm
    rw [this]; exact (map_ne_zero _).mpr two_ne_zero
  have ha' : algebraMap F Kv a ≠ 0 := (map_ne_zero _).mpr ha
  have hb' : algebraMap F Kv b ≠ 0 := (map_ne_zero _).mpr hb
  fin_cases i <;> simp [trdDiag, h2, ha', hb']

variable (v) in
/-- The trace-form Fourier transform on $\mathbb H_v$: $\int f(x)\,\psi_v(\operatorname{trd}(xy))\,d\mu(x)$. -/
def trdFourier (a b : F) (μ : Measure (QuatV a b v)) (f : QuatV a b v → ℂ) (y : QuatV a b v) : ℂ :=
  ∫ x, f x * (Analysis.psiV v (2 * (x * y).re) : ℂ) ∂μ

variable (v) in
/-- The inverse trace-form transform: $\int f(y)\,\psi_v(-\operatorname{trd}(xy))\,d\mu(y)$. -/
def trdFourierInv (a b : F) (μ : Measure (QuatV a b v)) (f : QuatV a b v → ℂ) (x : QuatV a b v) : ℂ :=
  ∫ y, f y * (Analysis.psiV v (-(2 * (x * y).re)) : ℂ) ∂μ

variable (v) in
/-- $|\det G|_v^{1/2} = \prod_i|g_i|_v^{1/2}$ for the trace form. -/
def trdFactor {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : ℝ := diagFactor v _ (trdDiag_ne_zero v ha hb)

variable (v) in
/-- **The $\psi_v\circ\operatorname{trd}$ self-dual measure** $|\det G|_v^{1/2}\,dx$ on $\mathbb H_v$. -/
def trdSelfDualV {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : Measure (QuatV a b v) :=
  ENNReal.ofReal (trdFactor v ha hb) • quatLocVol _ _ (Analysis.selfDualV v)

theorem trdFourier_eq_fourierDiag {a b : F} (r : ℝ) (f : QuatV a b v → ℂ) (y : QuatV a b v) :
    trdFourier v a b (ENNReal.ofReal r • quatLocVol _ _ (Analysis.selfDualV v)) f y =
      fourierDiag v (ENNReal.ofReal r • volV4 v) (trdDiag (algebraMap F Kv a) (algebraMap F Kv b)) (f ∘ (quatLocCLE _ _).symm) (quatLocCoord _ _ y) := by
  unfold trdFourier fourierDiag
  have hf : MeasurableEmbedding ((quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm :
      (Fin 4 → Kv) → QuatV a b v) := (quatLocCLE _ _).symm.toHomeomorph.measurableEmbedding
  rw [quatLocVol, ← Measure.map_smul, hf.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  congr 3
  rw [trd_mul_eq]
  have hx : quatLocCoord (algebraMap F Kv a) (algebraMap F Kv b) ((quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm x) = x := (quatLocCoord (algebraMap F Kv a) (algebraMap F Kv b)).apply_symm_apply x
  rw [hx]
  exact hf.measurable.aemeasurable

theorem trdFourierInv_eq_fourierDiagInv {a b : F} (r : ℝ) (f : QuatV a b v → ℂ) (x : QuatV a b v) :
    trdFourierInv v a b (ENNReal.ofReal r • quatLocVol _ _ (Analysis.selfDualV v)) f x =
      fourierDiagInv v (ENNReal.ofReal r • volV4 v) (trdDiag (algebraMap F Kv a) (algebraMap F Kv b)) (f ∘ (quatLocCLE _ _).symm)
        (quatLocCoord _ _ x) := by
  unfold trdFourierInv fourierDiagInv
  have hf : MeasurableEmbedding ((quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm :
      (Fin 4 → Kv) → QuatV a b v) := (quatLocCLE _ _).symm.toHomeomorph.measurableEmbedding
  rw [quatLocVol, ← Measure.map_smul, hf.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  congr 4
  rw [trd_mul_eq]
  have hy : quatLocCoord (algebraMap F Kv a) (algebraMap F Kv b) ((quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm y) = y := (quatLocCoord (algebraMap F Kv a) (algebraMap F Kv b)).apply_symm_apply y
  rw [hy]
  exact hf.measurable.aemeasurable

/-- The coordinate box indicator on $\mathbb H_v$. -/
def quatBoxInd (a b : F) (c : Fin 4 → Kv) (k : Fin 4 → ℤ) (x : QuatV a b v) : ℂ := boxInd v c k (quatLocCoord _ _ x)

theorem trdFourierInv_trdFourier_scale {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (r : ℝ) (hr : 0 ≤ r)
    (c : Fin 4 → Kv) (k : Fin 4 → ℤ) :
    trdFourierInv v a b (ENNReal.ofReal r • quatLocVol _ _ (Analysis.selfDualV v))
        (trdFourier v a b (ENNReal.ofReal r • quatLocVol _ _ (Analysis.selfDualV v)) (quatBoxInd a b c k)) =
      fun x => ((r ^ 2 * ∏ i, ((distribHaarChar Kv (Units.mk0 _ (trdDiag_ne_zero v ha hb i)) : ℝ))⁻¹ : ℝ) : ℂ) *
        quatBoxInd a b c k x := by
  funext x
  rw [trdFourierInv_eq_fourierDiagInv]
  have hf : (trdFourier v a b (ENNReal.ofReal r • quatLocVol _ _ (Analysis.selfDualV v)) (quatBoxInd a b c k)) ∘
      (quatLocCLE _ _).symm = fourierDiag v (ENNReal.ofReal r • volV4 v) (trdDiag (algebraMap F Kv a) (algebraMap F Kv b)) (boxInd v c k) := by
    funext y
    simp only [Function.comp_apply]
    rw [trdFourier_eq_fourierDiag]
    have h1 : quatBoxInd a b c k ∘ (quatLocCLE _ _).symm = boxInd v c k := by
      funext z
      simp only [Function.comp_apply, quatBoxInd]
      congr 1
      exact (quatLocCoord _ _).apply_symm_apply z
    rw [h1]
    congr 1
    exact (quatLocCoord _ _).apply_symm_apply y
  rw [hf, fourierDiagInv_fourierDiag_boxInd v r hr _ (trdDiag_ne_zero v ha hb)]
  rfl

/-- **$|\det G|_v^{1/2}\,dx$ is the $\psi_v\circ\operatorname{trd}$ self-dual measure on $\mathbb H_v$**: Fourier inversion
for the pairing $\psi_v(\operatorname{trd}(xy))$ holds on every coordinate box indicator. -/
@[kb "weil1982" "§2.3 [unverified page] (self-dual measure for ψ∘trd on A_v)"]
theorem trdFourierInv_trdFourier {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (c : Fin 4 → Kv) (k : Fin 4 → ℤ) :
    trdFourierInv v a b (trdSelfDualV v ha hb) (trdFourier v a b (trdSelfDualV v ha hb) (quatBoxInd a b c k)) =
      quatBoxInd a b c k := by
  rw [trdSelfDualV, trdFactor, trdFourierInv_trdFourier_scale ha hb _ (diagFactor_pos v _ _).le,
    diagFactor_sq_mul]
  funext x; simp

/-- **Uniqueness**: if $r\,dx$ ($r\ge0$) satisfies trace-form Fourier inversion on the box indicators, then
$r = |\det G|_v^{1/2}$. -/
theorem trdSelfDual_unique {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ c k, trdFourierInv v a b (ENNReal.ofReal r • quatLocVol _ _ (Analysis.selfDualV v))
      (trdFourier v a b (ENNReal.ofReal r • quatLocVol _ _ (Analysis.selfDualV v)) (quatBoxInd a b c k)) =
        quatBoxInd a b c k) :
    r = trdFactor v ha hb := by
  refine (selfDual_diag_iff v _ (trdDiag_ne_zero v ha hb) r hr).mp fun c k => ?_
  funext y
  have h1 := congrFun (h c k) ((quatLocCoord _ _).symm y)
  rw [trdFourierInv_trdFourier_scale ha hb r hr] at h1
  rw [fourierDiagInv_fourierDiag_boxInd v r hr _ (trdDiag_ne_zero v ha hb)]
  simp only [quatBoxInd, LinearEquiv.apply_symm_apply] at h1
  exact h1

/-! ### Global identification -/

/-- $\det G = -16a^2b^2\in F^\times$. -/
def trdDetUnit {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : Fˣ := Units.mk0 _ (neg_ne_zero.mpr (trdGram_det_ne_zero ha hb))

variable (v) in
theorem trdFactor_sq {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    trdFactor v ha hb ^ 2 = (modAt (finPart (diagUnits F (trdDetUnit ha hb))) v : ℝ) := by
  rw [trdFactor, diagFactor, ← Finset.prod_pow]
  simp_rw [Real.sq_sqrt (NNReal.coe_nonneg _)]
  rw [← NNReal.coe_prod, ← map_prod, modAt]
  congr 2
  refine Units.ext ?_
  rw [Units.coe_prod]
  simp only [Units.val_mk0, Fin.prod_univ_four, trdDiag]
  change _ = algebraMap F Kv (-(16 * a ^ 2 * b ^ 2))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, map_neg, map_mul, map_pow, map_ofNat]
  simp
  ring

theorem mulSupport_trdFactor_finite {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => trdFactor v ha hb).Finite := by
  refine (mulSupport_modAt_finite (finPart (diagUnits F (trdDetUnit ha hb)))).subset fun v hv => ?_
  rw [Function.mem_mulSupport] at hv ⊢
  intro h1
  apply hv
  have h2 := trdFactor_sq v ha hb
  rw [h1, NNReal.coe_one] at h2
  have h0 : 0 ≤ trdFactor v ha hb := (diagFactor_pos v _ (trdDiag_ne_zero v ha hb)).le
  exact (pow_left_inj₀ h0 zero_le_one two_ne_zero).mp (by rw [h2, one_pow])

/-- **Global identification of the trace-self-dual measure**: $\prod_v|\det G|_v^{1/2}\cdot|\det G|_\infty^{1/2} = 1$
($\det G = -16a^2b^2$, product formula). Hence $\bigotimes_v|\det G|_v^{1/2}dx_v\otimes|\det G|_\infty^{1/2}dx_\infty$ (the
$\psi\circ\operatorname{trd}$ self-dual measure on $\mathbb H_{\mathbb A}$) equals the coordinate self-dual measure. -/
@[kb "weil1982" "§2.3 [unverified page]"]
theorem finprod_trdFactor_mul_inf {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ᶠ v, trdFactor v ha hb) *
      Real.sqrt |LinearMap.det (LinearMap.mulLeft ℝ (mixedEmbedding F (-(16 * a ^ 2 * b ^ 2))))| = 1 := by
  have hnorm := ideleNorm_det_trdGram ha hb
  rw [ideleNorm] at hnorm
  set M := |LinearMap.det (LinearMap.mulLeft ℝ (mixedEmbedding F (-(16 * a ^ 2 * b ^ 2))))|
  have hM : |LinearMap.det (LinearMap.mulLeft ℝ ((infPart (diagUnits F (trdDetUnit ha hb)) : mixedSpace F)))| =
      M := rfl
  change |LinearMap.det (LinearMap.mulLeft ℝ ((infPart (diagUnits F (trdDetUnit ha hb)) : mixedSpace F)))| *
    ∏ᶠ v, (modAt (finPart (diagUnits F (trdDetUnit ha hb))) v : ℝ) = 1 at hnorm
  rw [hM] at hnorm
  set P := ∏ᶠ v, trdFactor v ha hb
  have hP0 : 0 ≤ P := finprod_nonneg fun v => (diagFactor_pos v _ (trdDiag_ne_zero v ha hb)).le
  have hP2 : P ^ 2 = ∏ᶠ v, (modAt (finPart (diagUnits F (trdDetUnit ha hb))) v : ℝ) := by
    rw [show P ^ 2 = ∏ᶠ v, trdFactor v ha hb ^ 2 from finprod_pow (mulSupport_trdFactor_finite ha hb) 2]
    exact finprod_congr fun v => trdFactor_sq v ha hb
  have hM0 : 0 ≤ M := abs_nonneg _
  have hsq : (P * Real.sqrt M) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hM0, hP2, mul_comm]; exact hnorm
  have hnn : 0 ≤ P * Real.sqrt M := mul_nonneg hP0 (Real.sqrt_nonneg _)
  exact (pow_left_inj₀ hnn zero_le_one two_ne_zero).mp (by rw [hsq, one_pow])

end

end QuadFormsKB.Tamagawa.Measure.Weil
