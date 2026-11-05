/-
# Hanke 2005, §4.3: $\mathrm{vol}_C(C_{\mathbb C})$ is the volume of the fibre of $F_{\mathbb C}$ (proof of `ArchFibrationComplex`)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Main result** (`archFibrationComplex`, unconditional, $n\ge1$): the named statement `ArchFibrationComplex n` holds,
$$(F_{\mathbb C})_*\widetilde\omega_G = \mathrm{vol}_C(C_{\mathbb C})\,\omega_Z,\qquad
\mathrm{vol}_C(C_{\mathbb C}) = 2^{n(n-3)/2}\tau_{\mathbb R}(SO_n(\mathbb R)),$$
for Hanke's measure $\widetilde\omega_G = 2^{3n(n-1)/2}\mu$ on $SO_n(\mathbb C)$ ($\mu$ the complex Leray measure) and Shimura's
$\omega_Z = \delta(z)^{(1-n)/2}dz$ on $Z_{\mathbb C}$. (For $n = 0$ the statement is false: $SO_0(\mathbb C)$ is a point of Leray
mass $1$, while `volCComplex 0` $= \tfrac12$; the factor $\tfrac12$ is the passage from $O_n$ to $SO_n$, which needs $n\ge1$.)

**Proof** (Hanke's computation, pp. 14–15, in measure-theoretic form). In the coordinates $X = \Psi(u, Y, \sigma) =
(1 - iu)Y(1 - i\sigma)$ near $SO_n(\mathbb C)$ (`ArchCxParam`, `ArchCxRegion`) the Jacobian is
$|\det D\Psi| = 2^{n(n-1)/2}|\det Y|^{-1}e(T, \sigma)$ (`abs_det_psiD`, Hanke's Lemma A5 step), the Gram matrix is
$(1 - i\sigma)T(1 - i\sigma)$ with $T = {}^tY(1 - {}^tuu)Y$, and on the group $u = F_{\mathbb C}$. For a test function
$f_\varphi(X) = \varphi(u(X))\chi({}^tXX)$ (`ArchCxTest`) the Leray region integral factors exactly (`lintegral_region_fTest`):
the $Y$-integral, by the weighted Gram co-area formula (`lintegral_gramH_det_pos`), produces Shimura's density
$\delta(u)^{(1-n)/2}$ and $\tfrac12c_n$, and what remains is an integral over the coefficients $c = (T, \sigma)$. Divided by the
volume of the Leray ball it tends to the value on the fibre $T = 1$, $\sigma = 0$ (`tendsto_avg_hmap`; this is where Lemma A6
enters: only the restriction to the fibre matters). Comparing with the Leray limit (`tendsto_lerayMeasureC`):
$\int_G\varphi(F_{\mathbb C})\,d\mu = 2^{-n^2}\tau_{\mathbb R}(SO_n(\mathbb R))\int\varphi\,d\omega_Z$ (`integral_FCG`), and test
functions determine measures on $Z_{\mathbb C}$ (`eq_of_lintegral_testFun_eq`).
-/
import QuadFormsKB.Literature.Hanke2005.ArchCxRegion
import QuadFormsKB.Literature.Hanke2005.ArchCxJacobian
import QuadFormsKB.Literature.Hanke2005.ArchCxUnique
import QuadFormsKB.Literature.Hanke2005.ArchVolumeReal
import QuadFormsKB.Literature.Hanke2005.ArchTransportComplex

open MeasureTheory Matrix Complex Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

/-! ### The fibre density -/

theorem det_one_add_sq_pos {σ : Matrix (Fin n) (Fin n) ℝ} (hσ : σᵀ = σ) : 0 < (1 + σ * σ).det := by
  refine Matrix.PosDef.det_pos ?_
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_one, transpose_mul, hσ]
  · rw [star_trivial, add_mulVec, one_mulVec, dotProduct_add, ← mulVec_mulVec]
    have h1 : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
    have h2 : 0 ≤ x ⬝ᵥ (σ *ᵥ (σ *ᵥ x)) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hσ]
      rw [show σ *ᵥ x ⬝ᵥ σ *ᵥ x = (σ *ᵥ x) ⬝ᵥ (σ *ᵥ x) from rfl]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith

/-- $e(c) = \det(1 + \sigma^2)^n\,|\det\Phi_1(T, (1 + \sigma^2)^{-1})|$: the part of the Jacobian of $\Psi$ that depends on
$(T, \sigma)$. -/
def eF (c : UIdx n → ℂ) : ℝ :=
  (1 + cS c * cS c).det ^ n * |LinearMap.det (phi1 (cT c) (1 + cS c * cS c)⁻¹)|

theorem eF_nonneg (c : UIdx n → ℂ) : 0 ≤ eF c :=
  mul_nonneg (pow_nonneg (det_one_add_sq_pos (cS_transpose c)).le _) (abs_nonneg _)

theorem continuous_eF : Continuous (eF : (UIdx n → ℂ) → ℝ) := by
  have hS : Continuous fun c : UIdx n → ℂ => 1 + cS c * cS c :=
    continuous_const.add (continuous_cS.matrix_mul continuous_cS)
  have hR : Continuous fun c : UIdx n → ℂ => (1 + cS c * cS c)⁻¹ := by
    refine continuous_iff_continuousAt.2 fun c => ?_
    exact (continuousOn_matrix_inv_real.continuousAt (IsOpen.mem_nhds
      (isOpen_ne_fun continuous_id.matrix_det continuous_const)
      (det_one_add_sq_pos (cS_transpose c)).ne')).comp (f := fun c : UIdx n → ℂ => 1 + cS c * cS c)
      hS.continuousAt
  have hD : Continuous fun c : UIdx n → ℂ => LinearMap.det (phi1 (cT c) (1 + cS c * cS c)⁻¹) :=
    continuous_det_phi1.comp (f := fun c : UIdx n → ℂ => (cT c, (1 + cS c * cS c)⁻¹)) (continuous_cT.prodMk hR)
  have hd : Continuous fun c : UIdx n → ℂ => (1 + cS c * cS c).det ^ n := hS.matrix_det.pow n
  exact hd.mul (continuous_abs.comp hD)

theorem eF_c0 : eF (c0 : UIdx n → ℂ) = 1 := by
  rw [eF, cS_c0, cT_c0, Matrix.zero_mul, add_zero, det_one, one_pow, inv_one, det_phi1_one_one, abs_one, one_mul]

/-- The fibre density $k(c) = c_n\det(T)^{-1}e(c)\chi(h(c))$ in the coefficient coordinates $c = (T, \sigma)$. -/
def kF (c : UIdx n → ℂ) : ℝ := cprod n * ((cT c).det)⁻¹ * eF c * chiB n (hmap c)

theorem det_cT_pos {c : UIdx n → ℂ} (hc : c ∈ Wc n) : 0 < (cT c).det :=
  (densR_of_piv n _ (piv_of_PDU n _ (PDU_of_Wc hc))).1

theorem kF_nonneg {c : UIdx n → ℂ} (hc : c ∈ Wc n) : 0 ≤ kF c :=
  mul_nonneg (mul_nonneg (mul_nonneg (cprod_pos n).le (inv_nonneg.mpr (det_cT_pos hc).le)) (eF_nonneg c))
    (chiB_nonneg _)

theorem continuousOn_kF : ContinuousOn (kF : (UIdx n → ℂ) → ℝ) (Wc n) := by
  refine ((continuousOn_const.mul ?_).mul continuous_eF.continuousOn).mul
    (continuous_chiB.comp continuous_hmap).continuousOn
  exact (continuous_cT.matrix_det.continuousOn).inv₀ fun c hc => (det_cT_pos hc).ne'

theorem kF_c0 : kF (c0 : UIdx n → ℂ) = cprod n := by
  rw [kF, cT_c0, det_one, inv_one, mul_one, eF_c0, mul_one, hmap_c0, chiB_cQ, mul_one]

/-! ### The integrand on $\Omega_\varepsilon$ -/

theorem aOf_psiM {p : Fin n → Fin n → ℂ} (hp : cP p ∈ Wc n) :
    aOf (psiM (pu p) (pY p) (ps p)) (cP p) = (1 - I • cplx (pu p)) * cplx (pY p) := by
  have hd := det_ne_zero_of_Wc hp
  rw [cS_cP] at hd
  have hu : IsUnit (1 - I • cplx (ps p)).det := isUnit_iff_ne_zero.mpr hd
  rw [aOf, cS_cP, psiM, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]

theorem uOf_psi {p : Fin n → Fin n → ℂ} (hp : cP p ∈ Wc n) : uOf (psi p) = pu p := by
  have hY : IsUnit (pY p).det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_PDU (PDU_cP hp))
  rw [uOf, show ofCols (psi p) = psiM (pu p) (pY p) (ps p) from rfl, phi_psiM (pu_skew p) (ps_symm p),
    show hmap (cOf (tT (pu p) (pY p)) (ps p)) = hmap (cP p) from rfl, gc_hmap hp, uOfc, aOf_psiM hp,
    (reM_imM_one_sub_mul _ _).1, (reM_imM_one_sub_mul _ _).2, neg_neg, Matrix.mul_assoc,
    mul_nonsing_inv _ hY, Matrix.mul_one]

theorem fTest_psi (φ : (LIdx n → ℝ) → ℝ) {p : Fin n → Fin n → ℂ} (hp : cP p ∈ Wc n) :
    fTest φ (psi p) = φ (lowerOf (pu p)) * chiB n (hmap (cP p)) := by
  rw [fTest, uOf_psi hp, phi_psi]

theorem det_mZ_pos {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ ZC n) : 0 < (mZ u).det := hu.2.det_pos

theorem abs_det_psiD_Om {ε : ℝ} {p : Fin n → Fin n → ℂ} (hp : p ∈ Om n ε) :
    |LinearMap.det (psiD p : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ))| =
      (2 : ℝ) ^ (n * (n - 1) / 2) * |(pY p).det|⁻¹ * eF (cP p) := by
  rw [abs_det_psiD p (det_ne_zero_of_PDU (PDU_cP hp.2.1)) (det_mZ_pos hp.1).ne', eF, cS_cP, cT_cP]
  ring

/-! ### Algebra for the $Y$-integral -/

/-- The coefficient vector with $\operatorname{Re} = t$, $\operatorname{Im} = w$. -/
def cG (t w : UIdx n → ℝ) : UIdx n → ℂ := fun q => ⟨t q, w q⟩

theorem cT_cG (t w : UIdx n → ℝ) : cT (cG t w) = symU t := rfl

theorem cS_cG (t w : UIdx n → ℝ) : cS (cG t w) = symU w := rfl

theorem re_cG (t w : UIdx n → ℝ) : (fun q => (cG t w q).re) = t := rfl

theorem continuous_cG (w : UIdx n → ℝ) : Continuous fun t : UIdx n → ℝ => cG t w := by
  refine continuous_pi fun q => ?_
  have e : (fun t : UIdx n → ℝ => cG t w q) = fun t => ((t q : ℝ) : ℂ) + ((w q : ℝ) : ℂ) * I := by
    funext t; exact Complex.mk_eq_add_mul_I _ _
  rw [e]
  exact (Complex.continuous_ofReal.comp (continuous_apply q)).add continuous_const

theorem gram_entry (Y M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    (Yᵀ * M * Y) a b = (fun i => Y i a) ⬝ᵥ (M *ᵥ fun i => Y i b) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem gramH_transpose (u : Matrix (Fin n) (Fin n) ℝ) (B : Fin n → Fin n → ℝ) :
    ArchReal.gramH (mZ u) B = upperOf (tT u (Matrix.of fun i j => B j i)) := by
  funext q
  rw [upperOf, tT, gram_entry]
  rfl

theorem cP_pE (x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ))) :
    cP (pE n x) = cG (upperOf (tT (skewOf x.2.1) (Matrix.of x.1))) x.2.2 := by
  funext q
  rw [cP, pu_pE, ps_pE, pY_pE]
  apply Complex.ext
  · rfl
  · show symU x.2.2 q.1.1 q.1.2 = x.2.2 q
    exact symU_apply_le _ q.2

theorem map_conj_one_sub_I (u : Matrix (Fin n) (Fin n) ℝ) :
    (1 - I • cplx u).map (starRingEnd ℂ) = 1 + I • cplx u := by
  ext i j
  by_cases h : i = j <;> simp [cplx, one_apply, h]

theorem det_one_sub_I_im {u : Matrix (Fin n) (Fin n) ℝ} (hu : uᵀ = -u) : (1 - I • cplx u).det.im = 0 := by
  have h1 : (starRingEnd ℂ) (1 - I • cplx u).det = (1 - I • cplx u).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_conj_one_sub_I, ← transpose_one_sub_I_skew hu,
      det_transpose]
  exact Complex.conj_eq_iff_im.mp h1

theorem det_one_sub_I_eq_re {u : Matrix (Fin n) (Fin n) ℝ} (hu : uᵀ = -u) :
    (1 - I • cplx u).det = (((1 - I • cplx u).det.re : ℝ) : ℂ) :=
  (Complex.ext rfl (by rw [ofReal_im, det_one_sub_I_im hu]))

theorem det_one_sub_I_re_ne_zero {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ ZC n) :
    (1 - I • cplx u).det.re ≠ 0 := by
  intro h0
  have h1 : (1 - I • cplx u).det = 0 := by rw [det_one_sub_I_eq_re hu.1, h0, ofReal_zero]
  have h2 := congrArg Matrix.det (one_add_mul_one_sub hu.1)
  rw [det_mul, h1, mul_zero, det_cplx] at h2
  exact (det_mZ_pos hu).ne' (by exact_mod_cast h2.symm)

theorem re_det_psiM {u Y σ : Matrix (Fin n) (Fin n) ℝ} (hu : uᵀ = -u) :
    (psiM u Y σ).det.re = ((1 - I • cplx u).det.re * (1 - I • cplx σ).det.re) * Y.det := by
  rw [psiM, det_mul, det_mul, det_cplx, det_one_sub_I_eq_re hu, ← ofReal_mul, re_ofReal_mul]
  simp only [ofReal_re]
  ring

theorem det_tT (u Y : Matrix (Fin n) (Fin n) ℝ) : (tT u Y).det = Y.det ^ 2 * (mZ u).det := by
  rw [tT, det_mul, det_mul, det_transpose]; ring

/-! ### The $Y$-integral: the weighted Gram co-area formula -/

/-- The integrand on coordinate space after the change of variables. -/
def Gint (φ : (LIdx n → ℝ) → ℝ) (p : Fin n → Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2) * |(pY p).det|⁻¹ * eF (cP p) *
    (φ (lowerOf (pu p)) * chiB n (hmap (cP p))))

/-- The integrand in the coefficient $t$ of $T$ (for fixed $\sigma$-coordinates $w$). -/
def gT (ε : ℝ) (w t : UIdx n → ℝ) : ℝ≥0∞ :=
  {t | cG t w ∈ Wc n ∧ hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε}.indicator
    (fun t => ENNReal.ofReal ((symU t).det ^ (-(1 / 2 : ℝ)) * eF (cG t w) * chiB n (hmap (cG t w)))) t

/-- $J_\varepsilon(w) = \int\rho_n(t)\,g(t)\,dt$. -/
def Jt (ε : ℝ) (w : UIdx n → ℝ) : ℝ≥0∞ := ∫⁻ t, densR n t * gT ε w t

theorem measurableSet_gT (ε : ℝ) (w : UIdx n → ℝ) :
    MeasurableSet {t : UIdx n → ℝ | cG t w ∈ Wc n ∧ hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε} :=
  ((continuous_cG w).measurable isOpen_Wc.measurableSet).inter
    ((continuous_hmap.comp (continuous_cG w)).measurable Metric.isClosed_closedBall.measurableSet)

theorem measurable_gT (ε : ℝ) (w : UIdx n → ℝ) : Measurable (gT ε w) := by
  refine Measurable.indicator ?_ (measurableSet_gT ε w)
  refine ENNReal.measurable_ofReal.comp (Measurable.mul (Measurable.mul ?_ ?_) ?_)
  · exact (continuous_symU.matrix_det).measurable.pow_const _
  · exact (continuous_eF.comp (continuous_cG w)).measurable
  · exact (continuous_chiB.comp (continuous_hmap.comp (continuous_cG w))).measurable

theorem measurable_Gint {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) : Measurable (Gint φ) := by
  refine ENNReal.measurable_ofReal.comp (Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_)
  · exact measurable_const
  · exact (continuous_abs.comp (continuous_pY.matrix_det)).measurable.inv
  · exact (continuous_eF.comp continuous_cP).measurable
  · exact ((hφ.comp (continuous_lowerOf.comp continuous_pu)).mul
      (continuous_chiB.comp (continuous_hmap.comp continuous_cP))).measurable

theorem measurable_indicator_Gint {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) (ε : ℝ) :
    Measurable ((Om n ε).indicator (Gint φ)) :=
  (measurable_Gint hφ).indicator (measurableSet_Om ε)

theorem not_mem_Om_of_re {ε : ℝ} {p : Fin n → Fin n → ℂ} (h : ¬ 0 < (1 - I • cplx (ps p)).det.re) :
    p ∉ Om n ε := fun hp => h (by have := det_re_pos_of_Wc hp.2.1; rwa [cS_cP] at this)

theorem abs_det_inv_eq {Y M : Matrix (Fin n) (Fin n) ℝ} (hM : 0 < M.det) (hY : Y.det ≠ 0) :
    |Y.det|⁻¹ = Real.sqrt M.det * (Y.det ^ 2 * M.det) ^ (-(1 / 2 : ℝ)) := by
  have ha : 0 < |Y.det| := abs_pos.mpr hY
  have h1 : (Y.det ^ 2) ^ (-(1 / 2 : ℝ)) = |Y.det|⁻¹ := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
    exact Real.rpow_neg_one _
  have h2 : Real.sqrt M.det * M.det ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hM]; norm_num
  rw [Real.mul_rpow (by positivity) hM.le, h1]
  calc |Y.det|⁻¹ = |Y.det|⁻¹ * (Real.sqrt M.det * M.det ^ (-(1 / 2 : ℝ))) := by rw [h2, mul_one]
    _ = _ := by ring

theorem mem_Om_pE_iff {ε : ℝ} {lv : LIdx n → ℝ} (hlv : skewOf lv ∈ ZC n) (w : UIdx n → ℝ)
    (B : Fin n → Fin n → ℝ) :
    pE n (fun i j => B j i, (lv, w)) ∈ Om n ε ↔
      (cG (ArchReal.gramH (mZ (skewOf lv)) B) w ∈ Wc n ∧
        hmap (cG (ArchReal.gramH (mZ (skewOf lv)) B) w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε) ∧
      0 < ((1 - I • cplx (skewOf lv)).det.re * (1 - I • cplx (symU w)).det.re) * (Matrix.of B).det := by
  set x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ)) := (fun i j => B j i, (lv, w))
  have hcP : cP (pE n x) = cG (ArchReal.gramH (mZ (skewOf lv)) B) w := by
    rw [cP_pE, gramH_transpose]
  have hdet : (psiM (pu (pE n x)) (pY (pE n x)) (ps (pE n x))).det.re =
      ((1 - I • cplx (skewOf lv)).det.re * (1 - I • cplx (symU w)).det.re) * (Matrix.of B).det := by
    rw [pu_pE, ps_pE, pY_pE, re_det_psiM (skewOf_transpose lv)]
    congr 1
    rw [← det_transpose]; rfl
  show (pu (pE n x) ∈ ZC n ∧ cP (pE n x) ∈ Wc n ∧
      hmap (cP (pE n x)) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε ∧
      0 < (psiM (pu (pE n x)) (pY (pE n x)) (ps (pE n x))).det.re) ↔ _
  rw [hdet, hcP]
  exact ⟨fun h => ⟨⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨by rw [pu_pE]; exact hlv, h.1.1, h.1.2, h.2⟩⟩

theorem integrand_transpose {φ : (LIdx n → ℝ) → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) {ε : ℝ} {lv : LIdx n → ℝ}
    (hlv : skewOf lv ∈ ZC n) (w : UIdx n → ℝ) (B : Fin n → Fin n → ℝ) :
    (Om n ε).indicator (Gint φ) (pE n (fun i j => B j i, (lv, w))) =
      {B : Fin n → Fin n → ℝ | 0 < ((1 - I • cplx (skewOf lv)).det.re * (1 - I • cplx (symU w)).det.re) *
        (Matrix.of B).det}.indicator
        (fun B => ENNReal.ofReal (Real.sqrt (mZ (skewOf lv)).det * (2 : ℝ) ^ (n * (n - 1) / 2) * φ lv) *
          gT ε w (ArchReal.gramH (mZ (skewOf lv)) B)) B := by
  set x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ)) := (fun i j => B j i, (lv, w))
  set u := skewOf lv
  set M := mZ u
  set t := ArchReal.gramH M B
  have hMpos : 0 < M.det := det_mZ_pos hlv
  have hiff := mem_Om_pE_iff (ε := ε) hlv w B
  by_cases hB : 0 < ((1 - I • cplx u).det.re * (1 - I • cplx (symU w)).det.re) * (Matrix.of B).det
  · rw [indicator_of_mem (show B ∈ {B : Fin n → Fin n → ℝ | 0 < ((1 - I • cplx u).det.re *
      (1 - I • cplx (symU w)).det.re) * (Matrix.of B).det} from hB)]
    by_cases hW : cG t w ∈ Wc n ∧ hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε
    · have hp : pE n x ∈ Om n ε := hiff.mpr ⟨hW, hB⟩
      rw [indicator_of_mem hp, gT, indicator_of_mem (show t ∈ {t | cG t w ∈ Wc n ∧
        hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε} from hW)]
      have hcP : cP (pE n x) = cG t w := by
        rw [cP_pE]
        show cG (upperOf (tT (skewOf lv) (Matrix.of fun i j => B j i))) w = cG t w
        rw [← gramH_transpose]
      have hdetB : (Matrix.of B).det ≠ 0 := fun h => by rw [h, mul_zero] at hB; exact lt_irrefl _ hB
      have hYdet : (pY (pE n x)).det = (Matrix.of B).det := by
        rw [pY_pE, ← det_transpose]; rfl
      have hsym : (symU t).det = (pY (pE n x)).det ^ 2 * M.det := by
        rw [show t = upperOf (tT u (pY (pE n x))) from gramH_transpose u B, symU_upperOf (tT_transpose _ _),
          det_tT]
      rw [Gint, hcP, pu_pE, lowerOf_skewOf, hsym, ← ENNReal.ofReal_mul
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (hφ0 lv))]
      congr 1
      rw [abs_det_inv_eq hMpos (hYdet ▸ hdetB)]
      ring
    · have hp : pE n x ∉ Om n ε := fun h => hW (hiff.mp h).1
      rw [indicator_of_notMem hp, gT, indicator_of_notMem (show t ∉ {t | cG t w ∈ Wc n ∧
        hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε} from hW), mul_zero]
  · have hp : pE n x ∉ Om n ε := fun h => hB (hiff.mp h).2
    rw [indicator_of_notMem hp, indicator_of_notMem (show B ∉ {B : Fin n → Fin n → ℝ |
      0 < ((1 - I • cplx u).det.re * (1 - I • cplx (symU w)).det.re) * (Matrix.of B).det} from hB)]

theorem not_mem_gT_set {ε : ℝ} {w : UIdx n → ℝ} (hσ : ¬ 0 < (1 - I • cplx (symU w)).det.re) (t : UIdx n → ℝ) :
    gT ε w t = 0 := by
  refine indicator_of_notMem (fun h => hσ ?_) _
  have := det_re_pos_of_Wc h.1
  rwa [cS_cG] at this

/-- **The $Y$-integral** (weighted Gram co-area formula): for fixed $u$ (lower coordinates `lv`) and $\sigma$ (upper
coordinates `w`), integrating out $Y$ produces Shimura's density $\delta(u)^{(1-n)/2}$. -/
theorem lintegral_inner (hn : 1 ≤ n) {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (ε : ℝ)
    (lv : LIdx n → ℝ) (w : UIdx n → ℝ) :
    ∫⁻ Y : Fin n → Fin n → ℝ, (Om n ε).indicator (Gint φ) (pE n (Y, (lv, w))) =
      (skewOf ⁻¹' ZC n).indicator (fun lv => ENNReal.ofReal (deltaC (skewOf lv) ^ ((1 - (n : ℝ)) / 2) * φ lv)) lv *
        (ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2) / 2) * Jt ε w) := by
  have hmeasF : Measurable fun Y : Fin n → Fin n → ℝ => (Om n ε).indicator (Gint φ) (pE n (Y, (lv, w))) :=
    (measurable_indicator_Gint hφ ε).comp ((pE n).measurable.comp (measurable_id.prodMk measurable_const))
  rw [← measurePreserving_transpose.lintegral_comp hmeasF]
  by_cases hlv : skewOf lv ∈ ZC n
  · rw [indicator_of_mem (show lv ∈ skewOf ⁻¹' ZC n from hlv)]
    by_cases hσ : 0 < (1 - I • cplx (symU w)).det.re
    · have hs : (1 - I • cplx (skewOf lv)).det.re * (1 - I • cplx (symU w)).det.re ≠ 0 :=
        mul_ne_zero (det_one_sub_I_re_ne_zero hlv) hσ.ne'
      simp_rw [integrand_transpose hφ0 hlv w]
      have hPD : (mZ (skewOf lv)).PosDef := hlv.2
      rw [ArchReal.lintegral_gramH_det_pos hn hPD hs
        (f := fun t => ENNReal.ofReal (Real.sqrt (mZ (skewOf lv)).det * (2 : ℝ) ^ (n * (n - 1) / 2) * φ lv) *
          gT ε w t) (measurable_const.mul (measurable_gT ε w))]
      simp_rw [mul_left_comm (densR n _)]
      rw [lintegral_const_mul (f := fun t => densR n t * gT ε w t) _
        ((measurable_densR n).mul (measurable_gT ε w)), ← Jt, ← mul_assoc, ← mul_assoc]
      congr 1
      have hd : 0 < (mZ (skewOf lv)).det := det_mZ_pos hlv
      have e1 : deltaC (skewOf lv) = (mZ (skewOf lv)).det := rfl
      rw [e1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hd.le _) (hφ0 lv))]
      congr 1
      rw [Real.sqrt_eq_rpow]
      have e2 : (mZ (skewOf lv)).det ^ ((1 - (n : ℝ)) / 2) =
          (mZ (skewOf lv)).det ^ (-(n : ℝ) / 2) * (mZ (skewOf lv)).det ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hd]; ring_nf
      rw [e2]
      ring
    · have h0 : ∀ B : Fin n → Fin n → ℝ, (Om n ε).indicator (Gint φ) (pE n (fun i j => B j i, (lv, w))) = 0 :=
        fun B => indicator_of_notMem (not_mem_Om_of_re (by rw [ps_pE]; exact hσ)) _
      have hJ : Jt ε w = 0 := by
        rw [Jt]; simp_rw [not_mem_gT_set hσ, mul_zero, lintegral_zero]
      simp_rw [h0, lintegral_zero, hJ, mul_zero]
  · have h0 : ∀ B : Fin n → Fin n → ℝ, (Om n ε).indicator (Gint φ) (pE n (fun i j => B j i, (lv, w))) = 0 :=
      fun B => indicator_of_notMem (fun h => hlv (by have := h.1; rwa [pu_pE] at this)) _
    simp_rw [h0, lintegral_zero]
    rw [indicator_of_notMem (show lv ∉ skewOf ⁻¹' ZC n from hlv), zero_mul]

/-! ### The $u$- and $c$-integrals -/

/-- $\int\mathbf 1_{Z_{\mathbb C}}(u)\,\delta(u)^{(1-n)/2}\varphi(u)\,du = \int\varphi\,d\omega_Z$. -/
theorem lintegral_muZC {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) :
    ∫⁻ lv, (skewOf ⁻¹' ZC n).indicator
        (fun lv => ENNReal.ofReal (deltaC (skewOf lv) ^ ((1 - (n : ℝ)) / 2) * φ lv)) lv =
      ∫⁻ v, ENNReal.ofReal (φ v) ∂muZC n := by
  rw [muZC, lintegral_withDensity_eq_lintegral_mul _ (measurable_rhoZC n)
    (show Measurable fun v => ENNReal.ofReal (φ v) from ENNReal.measurable_ofReal.comp hφ.measurable),
    lintegral_indicator measurableSet_skewOf_ZC]
  refine setLIntegral_congr_fun measurableSet_skewOf_ZC fun v hv => ?_
  rw [Pi.mul_apply]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg (det_mZ_pos hv).le _)

/-- $(t, w)\mapsto t + iw$ on coefficient vectors preserves Lebesgue measure. -/
theorem measurePreserving_cGpair :
    MeasurePreserving (fun q : (UIdx n → ℝ) × (UIdx n → ℝ) => cG q.1 q.2) volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (UIdx n)).symm
  have h2 : MeasurePreserving (fun f : UIdx n → ℝ × ℝ => fun q => Complex.measurableEquivRealProd.symm (f q))
      volume volume :=
    measurePreserving_pi _ _ fun _ => Complex.volume_preserving_equiv_real_prod.symm
  exact h2.comp h1

theorem continuous_cGpair : Continuous fun q : (UIdx n → ℝ) × (UIdx n → ℝ) => cG q.1 q.2 := by
  refine continuous_pi fun r => ?_
  have e : (fun q : (UIdx n → ℝ) × (UIdx n → ℝ) => cG q.1 q.2 r) =
      fun q => ((q.1 r : ℝ) : ℂ) + ((q.2 r : ℝ) : ℂ) * I := by
    funext q; exact Complex.mk_eq_add_mul_I _ _
  rw [e]
  exact (Complex.continuous_ofReal.comp ((continuous_apply r).comp continuous_fst)).add
    ((Complex.continuous_ofReal.comp ((continuous_apply r).comp continuous_snd)).mul continuous_const)

theorem measurable_gT_pair (ε : ℝ) :
    Measurable fun q : (UIdx n → ℝ) × (UIdx n → ℝ) => densR n q.1 * gT ε q.2 q.1 := by
  set S := {q : (UIdx n → ℝ) × (UIdx n → ℝ) | cG q.1 q.2 ∈ Wc n ∧
    hmap (cG q.1 q.2) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε}
  have hS : MeasurableSet S :=
    (continuous_cGpair.measurable isOpen_Wc.measurableSet).inter
      ((continuous_hmap.comp continuous_cGpair).measurable Metric.isClosed_closedBall.measurableSet)
  have hf : Measurable fun q : (UIdx n → ℝ) × (UIdx n → ℝ) => ENNReal.ofReal ((symU q.1).det ^ (-(1 / 2 : ℝ)) *
      eF (cG q.1 q.2) * chiB n (hmap (cG q.1 q.2))) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul (Measurable.mul ?_ ?_) ?_)
    · exact ((continuous_symU.matrix_det).measurable.pow_const _).comp measurable_fst
    · exact (continuous_eF.comp continuous_cGpair).measurable
    · exact (continuous_chiB.comp (continuous_hmap.comp continuous_cGpair)).measurable
  have e : (fun q : (UIdx n → ℝ) × (UIdx n → ℝ) => densR n q.1 * gT ε q.2 q.1) =
      fun q => densR n q.1 * S.indicator (fun q => ENNReal.ofReal ((symU q.1).det ^ (-(1 / 2 : ℝ)) *
        eF (cG q.1 q.2) * chiB n (hmap (cG q.1 q.2)))) q := by
    funext q
    rfl
  rw [e]
  exact ((measurable_densR n).comp measurable_fst).mul (hf.indicator hS)

theorem measurable_Jt (ε : ℝ) : Measurable (Jt ε : (UIdx n → ℝ) → ℝ≥0∞) := by
  have h := (measurable_gT_pair (n := n) ε).comp measurable_swap
  exact h.lintegral_prod_right'

/-- **The $c$-integral**: $\int J_\varepsilon(w)\,dw = \int_W k(c)\,[h(c)\in\bar B_\varepsilon]\,dc$. -/
theorem lintegral_Jt (ε : ℝ) :
    ∫⁻ w : UIdx n → ℝ, Jt ε w = ∫⁻ c in Wc n, ENNReal.ofReal (kF c) *
      (Metric.closedBall (coeffUC (sumSqC n)) ε).indicator 1 (hmap c) := by
  have hm := measurable_gT_pair (n := n) ε
  simp only [Jt]
  rw [← lintegral_prod_symm (fun q : (UIdx n → ℝ) × (UIdx n → ℝ) => densR n q.1 * gT ε q.2 q.1) hm.aemeasurable]
  rw [← Measure.volume_eq_prod]
  set H : (UIdx n → ℂ) → ℝ≥0∞ := (Wc n).indicator fun c =>
    ENNReal.ofReal (kF c) * (Metric.closedBall (coeffUC (sumSqC n)) ε).indicator 1 (hmap c)
  have hHm : Measurable H := by
    refine Measurable.indicator ?_ isOpen_Wc.measurableSet
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp ((((measurable_const.mul
        (continuous_cT.matrix_det.measurable.inv)).mul continuous_eF.measurable).mul
        (continuous_chiB.comp continuous_hmap).measurable))
    · exact (measurable_one.indicator Metric.isClosed_closedBall.measurableSet).comp continuous_hmap.measurable
  rw [← lintegral_indicator isOpen_Wc.measurableSet, ← measurePreserving_cGpair.lintegral_comp hHm]
  refine lintegral_congr fun q => ?_
  obtain ⟨t, w⟩ := q
  show densR n t * gT ε w t = H (cG t w)
  by_cases hc : cG t w ∈ Wc n
  · by_cases hB : hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε
    · rw [gT, indicator_of_mem (show t ∈ {t | cG t w ∈ Wc n ∧
        hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε} from ⟨hc, hB⟩)]
      simp only [H, indicator_of_mem hc, indicator_of_mem hB, Pi.one_apply, mul_one]
      have hP := PDU_of_Wc hc
      rw [re_cG] at hP
      obtain ⟨hdpos, hdens⟩ := densR_of_piv n t (piv_of_PDU n t hP)
      rw [hdens, ← ENNReal.ofReal_mul (mul_nonneg (cprod_pos n).le (Real.rpow_nonneg hdpos.le _))]
      congr 1
      rw [kF, cT_cG]
      have e : (symU t).det ^ (-(1 / 2 : ℝ)) * (symU t).det ^ (-(1 / 2 : ℝ)) = ((symU t).det)⁻¹ := by
        rw [← Real.rpow_add hdpos]; norm_num; exact Real.rpow_neg_one _
      calc cprod n * (symU t).det ^ (-(1 / 2 : ℝ)) * ((symU t).det ^ (-(1 / 2 : ℝ)) * eF (cG t w) *
            chiB n (hmap (cG t w)))
          = cprod n * ((symU t).det ^ (-(1 / 2 : ℝ)) * (symU t).det ^ (-(1 / 2 : ℝ))) * eF (cG t w) *
            chiB n (hmap (cG t w)) := by ring
        _ = _ := by rw [e]
    · rw [gT, indicator_of_notMem (show t ∉ {t | cG t w ∈ Wc n ∧
        hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε} from fun h => hB h.2), mul_zero]
      simp only [H, indicator_of_mem hc, indicator_of_notMem hB, mul_zero]
  · rw [gT, indicator_of_notMem (show t ∉ {t | cG t w ∈ Wc n ∧
      hmap (cG t w) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε} from fun h => hc h.1), mul_zero]
    simp only [H, indicator_of_notMem hc]

/-! ### The Leray region integral of a test function -/

/-- **The Leray region integral factors** (for $\bar B_\varepsilon(c_Q)\subseteq h(W)$):
$$\int_{\{\operatorname{Re}\det X > 0,\ \Phi(X)\in\bar B_\varepsilon\}}f_\varphi\,dX = \frac{2^{n(n-1)/2}}{2}
\int\varphi\,d\omega_Z\int_Wk(c)\,[h(c)\in\bar B_\varepsilon]\,dc.$$ -/
theorem lintegral_region_fTest (hn : 1 ≤ n) {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {ε : ℝ} (hε : Metric.closedBall (coeffUC (sumSqC n)) ε ⊆ hmap '' Wc n) :
    ∫⁻ X in lerayRegionC (sumSqC n) ε, ENNReal.ofReal (fTest φ X) =
      ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2) / 2) * (∫⁻ v, ENNReal.ofReal (φ v) ∂muZC n) *
        ∫⁻ c in Wc n, ENNReal.ofReal (kF c) * (Metric.closedBall (coeffUC (sumSqC n)) ε).indicator 1 (hmap c) := by
  rw [← image_psi_Om hε, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_Om ε)
    (fun p _ => (hasFDerivAt_psi p).hasFDerivWithinAt) (injOn_psi_Om ε)]
  have h1 : ∫⁻ p in Om n ε, ENNReal.ofReal |(psiD p).det| * ENNReal.ofReal (fTest φ (psi p)) =
      ∫⁻ p in Om n ε, Gint φ p := by
    refine setLIntegral_congr_fun (measurableSet_Om ε) fun p hp => ?_
    have hdet : |(psiD p).det| = (2 : ℝ) ^ (n * (n - 1) / 2) * |(pY p).det|⁻¹ * eF (cP p) :=
      abs_det_psiD_Om hp
    rw [hdet, fTest_psi φ hp.2.1, Gint, ← ENNReal.ofReal_mul (by
      have := eF_nonneg (cP p); positivity)]
  rw [h1, ← lintegral_indicator (measurableSet_Om ε),
    ← measurePreserving_pE.lintegral_comp (measurable_indicator_Gint hφ ε), Measure.volume_eq_prod,
    lintegral_prod_symm (fun x => (Om n ε).indicator (Gint φ) (pE n x))
      ((measurable_indicator_Gint hφ ε).comp (pE n).measurable).aemeasurable]
  simp_rw [lintegral_inner hn hφ hφ0 ε]
  have hδ : Measurable fun lv : LIdx n → ℝ => deltaC (skewOf lv) :=
    (Continuous.matrix_det (continuous_const.sub
      ((continuous_skewOf.matrix_transpose).matrix_mul continuous_skewOf))).measurable
  have ha : Measurable fun lv : LIdx n → ℝ => (skewOf ⁻¹' ZC n).indicator
      (fun lv => ENNReal.ofReal (deltaC (skewOf lv) ^ ((1 - (n : ℝ)) / 2) * φ lv)) lv :=
    (ENNReal.measurable_ofReal.comp ((hδ.pow_const _).mul hφ.measurable)).indicator measurableSet_skewOf_ZC
  have hJ := measurable_Jt (n := n) ε
  have hmeas : Measurable fun y : (LIdx n → ℝ) × (UIdx n → ℝ) => (skewOf ⁻¹' ZC n).indicator
      (fun lv => ENNReal.ofReal (deltaC (skewOf lv) ^ ((1 - (n : ℝ)) / 2) * φ lv)) y.1 *
        (ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2) / 2) * Jt ε y.2) :=
    (ha.comp measurable_fst).mul (measurable_const.mul (hJ.comp measurable_snd))
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  have hCJ : Measurable fun w : UIdx n → ℝ => ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2) / 2) * Jt ε w :=
    measurable_const.mul hJ
  simp_rw [lintegral_const_mul _ hCJ]
  rw [lintegral_mul_const _ ha, lintegral_muZC hφ, lintegral_const_mul _ hJ, lintegral_Jt]
  ring

/-! ### $Z_{\mathbb C}$ is open; $\omega_Z$ is finite on compact subsets -/

theorem isOpen_posDef_of_continuous {X : Type*} [TopologicalSpace X] {M : X → Matrix (Fin n) (Fin n) ℝ}
    (hM : Continuous M) (hsym : ∀ x, (M x)ᵀ = M x) : IsOpen {x | (M x).PosDef} := by
  refine isOpen_iff_mem_nhds.mpr fun x₀ hx₀ => ?_
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hcont : Continuous fun p : X × (Fin n → ℝ) => p.2 ⬝ᵥ (M p.1 *ᵥ p.2) :=
    continuous_snd.dotProduct ((hM.comp continuous_fst).matrix_mulVec continuous_snd)
  have hpd := (posDef_iff_dotProduct_mulVec.mp hx₀).2
  have h0 : ∀ v ∈ Metric.sphere (0 : Fin n → ℝ) 1,
      ∀ᶠ p : X × (Fin n → ℝ) in 𝓝 (x₀, v), 0 < p.2 ⬝ᵥ (M p.1 *ᵥ p.2) := by
    intro v hv
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    refine hcont.continuousAt.eventually (lt_mem_nhds ?_)
    have := hpd hv0; rwa [star_trivial] at this
  have h1 := hS.eventually_forall_of_forall_eventually (P := fun x v => 0 < v ⬝ᵥ (M x *ᵥ v)) h0
  filter_upwards [h1] with x hx
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hsym x, fun v hv => ?_⟩
  rw [star_trivial]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have := hx _ hw
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
  have h2 : 0 < ‖v‖⁻¹ * ‖v‖⁻¹ := by positivity
  nlinarith

theorem isOpen_skewOf_ZC : IsOpen (skewOf ⁻¹' ZC n : Set (LIdx n → ℝ)) := by
  have e : (skewOf ⁻¹' ZC n : Set (LIdx n → ℝ)) = {v | (mZ (skewOf v)).PosDef} := by
    ext v; exact ⟨fun h => h.2, fun h => ⟨skewOf_transpose v, h⟩⟩
  rw [e]
  exact isOpen_posDef_of_continuous (continuous_const.sub
    ((continuous_skewOf.matrix_transpose).matrix_mul continuous_skewOf)) fun v => mZ_transpose _

theorem lintegral_muZC_lt_top {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφZ : tsupport φ ⊆ skewOf ⁻¹' ZC n) : ∫⁻ v, ENNReal.ofReal (φ v) ∂muZC n < ∞ := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  set K := tsupport φ
  have hK : IsCompact K := hφc
  have hρ : ContinuousOn (fun v : LIdx n → ℝ => deltaC (skewOf v) ^ ((1 - (n : ℝ)) / 2)) K := by
    refine ContinuousOn.rpow_const ?_ fun v hv => Or.inl (det_mZ_pos (hφZ hv)).ne'
    exact (Continuous.matrix_det (continuous_const.sub
      ((continuous_skewOf.matrix_transpose).matrix_mul continuous_skewOf))).continuousOn
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hρ
  rw [← lintegral_muZC hφ]
  calc ∫⁻ lv, (skewOf ⁻¹' ZC n).indicator
        (fun lv => ENNReal.ofReal (deltaC (skewOf lv) ^ ((1 - (n : ℝ)) / 2) * φ lv)) lv
      ≤ ∫⁻ lv, K.indicator (fun _ => ENNReal.ofReal (R * C)) lv := by
        refine lintegral_mono fun v => ?_
        by_cases hv : v ∈ K
        · rw [indicator_of_mem hv]
          by_cases hvO : v ∈ skewOf ⁻¹' ZC n
          · rw [indicator_of_mem hvO]
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 := hR v hv
            have h2 := hC v
            rw [Real.norm_eq_abs] at h1 h2
            calc deltaC (skewOf v) ^ ((1 - (n : ℝ)) / 2) * φ v
                ≤ |deltaC (skewOf v) ^ ((1 - (n : ℝ)) / 2)| * |φ v| := by
                  rw [← abs_mul]; exact le_abs_self _
              _ ≤ R * C := mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
          · rw [indicator_of_notMem hvO]; exact zero_le
        · have : φ v = 0 := image_eq_zero_of_notMem_tsupport hv
          rw [indicator_of_notMem hv]
          by_cases hvO : v ∈ skewOf ⁻¹' ZC n
          · rw [indicator_of_mem hvO, this, mul_zero, ENNReal.ofReal_zero]
          · rw [indicator_of_notMem hvO]
    _ = ENNReal.ofReal (R * C) * volume K := lintegral_indicator_const hK.isClosed.measurableSet _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-! ### The fibre integral and the push-forward -/

/-- The constant $\frac{2^{n(n-1)/2}}{2}\cdot\frac{c_n}{|\det Dh(c_0)|}$. -/
def Kc (n : ℕ) : ℝ := (2 : ℝ) ^ (n * (n - 1) / 2) / 2 *
  (cprod n / ((2 : ℝ) ^ (n * (n - 1)) * 2 ^ (n * (n + 1) / 2)))

theorem fTest_nonneg {φ : (LIdx n → ℝ) → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (X : Fin n → Fin n → ℂ) : 0 ≤ fTest φ X :=
  mul_nonneg (hφ0 _) (chiB_nonneg _)

/-- **The fibre integral** (Hanke, §4.3): $\int_{SO_n(\mathbb C)}\varphi(F_{\mathbb C}(g))\,d\mu(g) = K\int\varphi\,d\omega_Z$ for
continuous $\varphi\ge0$ with compact support in $Z_{\mathbb C}$. -/
theorem integral_FCG (hn : 1 ≤ n) {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφZ : tsupport φ ⊆ skewOf ⁻¹' ZC n) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫ g, φ (FCG g) ∂lerayMeasureC (sumSqC n) gramDetC_sumSqC_ne_zero =
      Kc n * (∫⁻ v, ENNReal.ofReal (φ v) ∂muZC n).toReal := by
  set f := fTest φ
  have hf : Continuous f := continuous_fTest hφ
  have hfc : HasCompactSupport f := hasCompactSupport_fTest hφc hφZ
  have h1 := tendsto_lerayMeasureC (Q := sumSqC n) gramDetC_sumSqC_ne_zero hf hfc
  simp_rw [f, fTest_mat] at h1
  refine tendsto_nhds_unique h1 ?_
  -- the explicit limit
  set C := (2 : ℝ) ^ (n * (n - 1) / 2) / 2
  set Φ := ∫⁻ v, ENNReal.ofReal (φ v) ∂muZC n
  have hlim := tendsto_avg_hmap (n := n) isOpen_Wc c0_mem_Wc isOpen_hmap_Wc continuousOn_gc
    (fun c hc => gc_hmap hc) (fun c hc => det_fderiv_ne_zero_of_Wc hc) continuousOn_kF
    (fun c hc => kF_nonneg hc)
  rw [kF_c0, fderiv_hmap_c0, abs_det_hmapD] at hlim
  have h2 := hlim.const_mul (C * Φ.toReal)
  have hK : C * Φ.toReal * (cprod n / ((2 : ℝ) ^ (n * (n - 1)) * 2 ^ (n * (n + 1) / 2))) = Kc n * Φ.toReal := by
    rw [Kc]; ring
  rw [hK] at h2
  refine h2.congr' ?_
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp isOpen_hmap_Wc _ cQ_mem
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hB : Metric.closedBall (coeffUC (sumSqC n)) ε ⊆ hmap '' Wc n :=
    (Metric.closedBall_subset_ball hε.2).trans hsub
  rw [lerayApproxC, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fTest_nonneg hφ0))
    hf.aestronglyMeasurable.restrict, lerayRegionC, ← lerayRegionC, lintegral_region_fTest hn hφ hφ0 hB,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem Kc_nonneg : 0 ≤ Kc n := by
  have := cprod_pos n
  rw [Kc]; positivity

theorem integrable_FCG {φ : (LIdx n → ℝ) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφZ : tsupport φ ⊆ skewOf ⁻¹' ZC n) :
    Integrable (fun g => φ (FCG g)) (lerayMeasureC (sumSqC n) gramDetC_sumSqC_ne_zero) := by
  have := isHaarMeasure_lerayMeasureC (Q := sumSqC n) gramDetC_sumSqC_ne_zero
  have e : (fun g => φ (FCG g)) = fun g : ArchSOC (sumSqC n) => fTest φ (cols (ArchSOC.mat _ g)) :=
    funext fun g => (fTest_mat φ g).symm
  rw [e]
  have hc := hasCompactSupport_fibre (DiagC.ofExists (sumSqC n) gramDetC_sumSqC_ne_zero)
    (hasCompactSupport_fTest hφc hφZ) 1
  simp only [chart, SliceB.mat_one, Matrix.mul_one] at hc
  exact ((continuous_fTest hφ).comp (continuous_cols.comp (ArchSOC.continuous_mat _))).integrable_of_hasCompactSupport hc

/-- **The push-forward** of the complex Leray measure by $F_{\mathbb C}$ is $K\,\omega_Z$. -/
theorem map_FCG_lerayMeasureC (hn : 1 ≤ n) :
    (lerayMeasureC (sumSqC n) gramDetC_sumSqC_ne_zero).map FCG = ENNReal.ofReal (Kc n) • muZC n := by
  set μ := lerayMeasureC (sumSqC n) gramDetC_sumSqC_ne_zero
  have hO := isOpen_skewOf_ZC (n := n)
  refine eq_of_lintegral_testFun_eq hO ?_ ?_ fun φ hφ hφc hφZ hφ0 => ?_
  · rw [Measure.map_apply measurable_FCG hO.measurableSet.compl]
    have : FCG ⁻¹' (skewOf ⁻¹' ZC n)ᶜ = (∅ : Set (ArchSOC (sumSqC n))) := by
      ext g; simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact FCG_mem g
    rw [this, measure_empty]
  · rw [Measure.smul_apply, muZC, withDensity_apply _ hO.measurableSet.compl, Measure.restrict_restrict
      hO.measurableSet.compl, compl_inter_self, Measure.restrict_empty, lintegral_zero_measure, smul_zero]
  · have hint := integrable_FCG hφ hφc hφZ
    have hfin := lintegral_muZC_lt_top hφ hφc hφZ
    rw [lintegral_map (show Measurable fun v => ENNReal.ofReal (φ v) from
      ENNReal.measurable_ofReal.comp hφ.measurable) measurable_FCG,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun g => hφ0 _),
      integral_FCG hn hφ hφc hφZ hφ0, lintegral_smul_measure, ENNReal.ofReal_mul Kc_nonneg,
      ENNReal.ofReal_toReal hfin.ne, smul_eq_mul]
    exact ⟨rfl, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne⟩

/-- The constant: $2^{3n(n-1)/2}\cdot K = 2^{n(n-3)/2}\tau_{\mathbb R}(SO_n(\mathbb R))$. -/
theorem two_pow_mul_Kc (hn : 1 ≤ n) : (2 : ℝ) ^ (3 * (n * (n - 1) / 2)) * Kc n = volCComplex n := by
  set a := n * (n - 1) / 2 with ha_def
  have ha : n * (n - 1) = 2 * a := (Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)).symm
  have hb : n * (n + 1) / 2 = a + n := by
    have : n * (n + 1) = n * (n - 1) + 2 * n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    rw [this, ha, ← mul_add, Nat.mul_div_cancel_left _ two_pos]
  have hreal : (n : ℝ) * ((n : ℝ) - 3) / 2 = (a : ℝ) - n := by
    have h1 : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]
    have h2 : ((n * (n - 1) : ℕ) : ℝ) = 2 * (a : ℝ) := by rw [ha]; push_cast; ring
    linarith
  rw [Kc, ArchReal.cprod_eq_two_mul_tauR, volCComplex, hreal, ← ha_def, ha, hb,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, Real.rpow_natCast]
  field_simp
  ring

/-- **`ArchFibrationComplex n` holds** for $n\ge1$ (Hanke thesis, §4.3, pp. 14–15): Hanke's Haar measure on $SO_n(\mathbb C)$
pushed forward by $F_{\mathbb C}$ is $\mathrm{vol}_C(C_{\mathbb C})\,\omega_Z$, $\mathrm{vol}_C(C_{\mathbb C}) =
2^{n(n-3)/2}\tau_{\mathbb R}(SO_n(\mathbb R))$. Unconditional. -/
@[kb "hanke2005crelle" "§4.3, pp. 14–15 (ω_C and vol_C(C_C))"]
theorem archFibrationComplex (hn : 1 ≤ n) : ArchFibrationComplex n := by
  refine ⟨?_⟩
  rw [hankeHaarC, Measure.map_smul, map_FCG_lerayMeasureC hn, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), two_pow_mul_Kc hn]
  all_goals exact measurable_FCG.aemeasurable

/-! ### $n = 0$: the named statement is false -/

theorem volume_univ_isEmpty {ι α : Type*} [Fintype ι] [IsEmpty ι] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] :
    (volume : Measure (ι → α)) univ = 1 := by
  rw [volume_pi, Measure.pi_univ, Finset.univ_eq_empty, Finset.prod_empty]

theorem volume_isEmpty_eq {ι α : Type*} [Fintype ι] [IsEmpty ι] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] {s : Set (ι → α)}
    (hs : s.Nonempty) : (volume : Measure (ι → α)) s = 1 := by
  have : s = univ := by
    obtain ⟨x, hx⟩ := hs
    ext y; simp only [mem_univ, iff_true]
    rwa [Subsingleton.elim y x]
  rw [this, volume_univ_isEmpty]

/-- For $n = 0$ the Leray measure of the trivial group $SO_0(\mathbb C)$ has mass $1$. -/
theorem lerayMeasureC_zero_univ :
    lerayMeasureC (sumSqC 0) gramDetC_sumSqC_ne_zero univ = 1 := by
  set μ := lerayMeasureC (sumSqC 0) gramDetC_sumSqC_ne_zero
  have hc : HasCompactSupport (fun _ : Fin 0 → Fin 0 → ℂ => (1 : ℝ)) :=
    (Set.subsingleton_of_subsingleton).isCompact
  have ht := tendsto_lerayMeasureC (Q := sumSqC 0) gramDetC_sumSqC_ne_zero continuous_const hc
  have hconst : ∀ ε : ℝ, 0 < ε → lerayApproxC (sumSqC 0) (fun _ => 1) ε = 1 := by
    intro ε hε
    have hreg : (lerayRegionC (sumSqC 0) ε).Nonempty := by
      refine ⟨0, ?_, ?_⟩
      · simp [Matrix.det_isEmpty]
      · rw [Metric.mem_closedBall, Subsingleton.elim (phi (sumSqC 0) (ofCols 0)) (coeffUC (sumSqC 0)),
          dist_self]; exact hε.le
    rw [lerayApproxC, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      volume_isEmpty_eq hreg, volume_isEmpty_eq (Metric.nonempty_closedBall.mpr hε.le)]
    simp
  have h1 : Tendsto (lerayApproxC (sumSqC 0) (fun _ => 1)) (𝓝[>] 0) (𝓝 1) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ε hε using (hconst ε hε).symm)
  have h2 := tendsto_nhds_unique ht h1
  have hsub : Subsingleton (ArchSOC (sumSqC 0)) := by
    show Subsingleton (soC (sumSqC 0))
    exact ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  have : IsFiniteMeasure μ := by
    have := isHaarMeasure_lerayMeasureC (Q := sumSqC 0) gramDetC_sumSqC_ne_zero
    exact ⟨(Set.subsingleton_of_subsingleton (s := (univ : Set (ArchSOC (sumSqC 0))))).isCompact.measure_lt_top⟩
  rw [integral_const, smul_eq_mul, mul_one, Measure.real] at h2
  exact (ENNReal.toReal_eq_one_iff _).mp h2

/-- **For $n = 0$ the named statement is false**: $SO_0(\mathbb C)$ is a point of Leray mass $1$, while
`volCComplex 0` $= \tfrac12$ (the factor $\tfrac12$ of $\tau_{\mathbb R}(SO_n(\mathbb R))$ is the passage from $O_n$ to $SO_n$,
which needs $n\ge1$). So `archFibrationComplex` ($n\ge1$) is the full range of validity. -/
theorem not_archFibrationComplex_zero : ¬ ArchFibrationComplex 0 := by
  intro h
  have e := congrArg (fun μ : Measure (LIdx 0 → ℝ) => μ univ) h.map_eq
  rw [Measure.map_apply measurable_FCG MeasurableSet.univ, preimage_univ, hankeHaarC, Measure.smul_apply,
    lerayMeasureC_zero_univ, Measure.smul_apply] at e
  have hS : (skewOf ⁻¹' ZC 0 : Set (LIdx 0 → ℝ)) = univ := by
    ext v
    simp only [mem_preimage, mem_univ, iff_true]
    refine ⟨skewOf_transpose v, ?_⟩
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact mZ_transpose _,
      fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  have hZ : muZC 0 univ = 1 := by
    rw [muZC, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hS, Measure.restrict_univ]
    have hρ : ∀ v : LIdx 0 → ℝ,
        ENNReal.ofReal (deltaC (skewOf v) ^ ((1 - ((0 : ℕ) : ℝ)) / 2)) = 1 := by
      intro v; simp [deltaC, Matrix.det_isEmpty]
    simp_rw [hρ]
    rw [lintegral_const, one_mul, volume_univ_isEmpty]
  rw [hZ, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at e
  have hv : volCComplex 0 = 1 / 2 := by
    simp [volCComplex, tauR]
  rw [hv] at e
  have h2 : ENNReal.ofReal (1 / 2) < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num)
  norm_num at e
  exact absurd e h2.ne'

end QuadFormsKB.Hanke2005.ArchCx
