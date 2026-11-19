/-
# Chenevier–Lannes: theta series with a harmonic coefficient of degree 2, and Venkov's identity

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §2.3, Proposition 2.3.2, p. 35 (Venkov). Printed page numbers.

**Layer.** An even unimodular lattice is recorded by its integral form $Q = q_L$ (`IsEvenUnimodular`), Hessian
$H$ (the Gram matrix $x \cdot y = x^{\mathsf T}Hy$, $\det H = 1$), $x \cdot x = 2Q(x)$; `latDot Q x u` is
$x \cdot u = x^{\mathsf T}Hu$ for $x \in \mathbb{Z}^n$, $u \in \mathbb{R}^n$. Here $n = 2k$ with $4 \mid k$.

For $u \in \mathbb{R}^n$ the polynomial
$$P_u(x) = (x \cdot u)^2 - \frac{(u \cdot u)\,(x \cdot x)}{n}$$
(`harmPoly`) is harmonic for the metric $H$, and
$$\vartheta_{L,P_u}(\tau) = \sum_{x \in \mathbb{Z}^n} P_u(x)\, e^{2\pi i \tau Q(x)}$$
(`thetaHarm`) is a cusp form of weight $k + 2$ for $\mathrm{SL}_2(\mathbb{Z})$.

**Main results** (all unconditional).
* `thetaLin_S`, `thetaNorm_S`: the inversion laws of $f_u(\tau) = \sum_x (x\cdot u)^2 e^{2\pi i\tau Q(x)}$ and
  $g(\tau) = \sum_x (x\cdot x)\,e^{2\pi i\tau Q(x)}$ (the first from `Analysis.tsum_sq_gaussian_quadratic`, the second
  by differentiating $\vartheta_L(-1/\tau) = \tau^k\vartheta_L(\tau)$):
  $f_u(-1/\tau) = \tau^k\big(\tau^2 f_u(\tau) - \tfrac{i}{2\pi}\tau\,(u\cdot u)\,\vartheta_L(\tau)\big)$ and
  $g(-1/\tau) = \tau^k\big(\tau^2 g(\tau) - \tfrac{i}{2\pi}\tau\, n\,\vartheta_L(\tau)\big)$.
* `thetaHarm_S`: $\vartheta_{L,P_u}(-1/\tau) = \tau^{k+2}\,\vartheta_{L,P_u}(\tau)$ (the correction terms cancel).
* `thetaHarmMF`: $\vartheta_{L,P_u} \in M_{k+2}(\mathrm{SL}_2(\mathbb{Z}))$ (Mathlib's `ModularForm 𝒮ℒ (k + 2)`), with
  $q$-expansion coefficients $\sum_{Q(x) = m} P_u(x)$ (`qExpansion_thetaHarmMF_coeff`).
* `thetaHarmMF_eq_zero`: for $k \le 12$ (weights $6, 10, 14$) it vanishes: its constant term is $P_u(0) = 0$, and
  cusp forms of weight $6, 10, 14$ for $\mathrm{SL}_2(\mathbb{Z})$ are $0$ (Mathlib's `CuspForm.discriminantEquiv`,
  `levelOne_neg_weight_rank_zero`, `levelOne_weight_two_rank_zero`).
* **`venkovRootSum_eight`, `venkovRootSum_sixteen`, `venkovRootSum_twentyFour`**: Proposition 2.3.2
  (`VenkovRootSum n`) for $n = 8, 16, 24$, from the vanishing of the coefficient of $q^1$.
-/
import QuadFormsKB.Analysis.HarmonicPoisson
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Venkov

open Complex Matrix ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-! ### Helper lemmas -/

section Helpers

open QuadFormsKB.Analysis (quadAt quadAtR)

/-- $|e(zQ(x))| = e^{-2\pi \operatorname{Im}(z) Q(x)}$. -/
private lemma norm_theta_term' (Q : QuadForm ℤ n) (z : ℂ) (x : Fin n → ℤ) :
    ‖cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖ = Real.exp (-(2 * Real.pi * z.im * Q.eval x)) := by
  rw [Complex.norm_exp]; congr 1
  simp [mul_re, mul_im]

private lemma re_neg_two_I_mul' {z : ℂ} (hz : 0 < z.im) : 0 < (-2 * I * z).re := by
  simp [Complex.mul_re]; linarith

private lemma exp_arg (Q : QuadForm ℤ n) (z : ℂ) (x : Fin n → ℤ) :
    cexp (2 * Real.pi * I * z * (Q.eval x : ℂ)) =
      cexp (-Real.pi * (-2 * I * z) * (quadAt (gramMatrix Q) x : ℂ)) := by
  rw [quadAt_gramMatrix]; push_cast; congr 1; ring

private lemma gramMatrix_eq' (Q : QuadForm ℤ n) :
    gramMatrix Q = (1 / 2 : ℝ) • Q.hessian.map (Int.cast : ℤ → ℝ) := rfl

private lemma dot_gram (Q : QuadForm ℤ n) (x : Fin n → ℤ) (u : Fin n → ℝ) :
    ((fun i => (x i : ℝ)) ⬝ᵥ (gramMatrix Q *ᵥ u)) = latDot Q x u / 2 := by
  rw [gramMatrix_eq', smul_mulVec, dotProduct_smul, smul_eq_mul]; unfold latDot; ring

private lemma hessR_symm (Q : QuadForm ℤ n) :
    (Q.hessian.map (Int.cast : ℤ → ℝ))ᵀ = Q.hessian.map (Int.cast : ℤ → ℝ) := by
  rw [← Matrix.transpose_map, (QuadFormsKB.LocalDensity.hessian_isSymm Q).eq]

private lemma dot_hx (Q : QuadForm ℤ n) (x : Fin n → ℤ) (u : Fin n → ℝ) :
    (∑ i, (((Q.hessian *ᵥ x) i : ℤ) : ℝ) * u i) = latDot Q x u := by
  have hcast : (fun i => (((Q.hessian *ᵥ x) i : ℤ) : ℝ)) =
      Q.hessian.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) := by
    ext i; simp [mulVec, dotProduct]
  have h1 : (∑ i, (((Q.hessian *ᵥ x) i : ℤ) : ℝ) * u i) =
      (fun i => (((Q.hessian *ᵥ x) i : ℤ) : ℝ)) ⬝ᵥ u := rfl
  rw [h1, hcast, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hessR_symm,
    dotProduct_comm]
  rfl

private lemma quadAt_smul' (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℤ) :
    quadAt (c • A) x = c * quadAt A x := by
  simp [quadAt, smul_mulVec, dotProduct_smul]

private lemma key_dual {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) (x : Fin n → ℤ) :
    quadAt (dualGram Q) (Q.hessian *ᵥ x) = quadAt (gramMatrix Q) x := by
  set H := Q.hessian with hH
  set Hr : Matrix (Fin n) (Fin n) ℝ := H.map (Int.cast : ℤ → ℝ) with hHr
  have hdetr : IsUnit Hr.det := by
    have h := RingHom.map_det (Int.castRingHom ℝ) H
    rw [RingHom.mapMatrix_apply] at h
    have : Hr.det = (H.det : ℝ) := by rw [hHr]; exact h.symm
    rw [this]
    rcases Int.isUnit_iff.mp hdet with h1 | h1 <;> simp [h1]
  have hcast : (fun i => ((H *ᵥ x) i : ℝ)) = Hr *ᵥ (fun i => (x i : ℝ)) := by
    ext i; simp [hHr, mulVec, dotProduct]
  have hinv : ((1 / 2 : ℝ) • Hr)⁻¹ = (2 : ℝ) • Hr⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, nonsing_inv_mul _ hdetr]; norm_num
  rw [quadAt, quadAt, hcast, dualGram, gramMatrix_eq', ← hHr, hinv, smul_smul, smul_mulVec,
    mulVec_mulVec, nonsing_inv_mul _ hdetr, one_mulVec, smul_mulVec, dotProduct_smul,
    dotProduct_smul, dotProduct_comm]
  simp only [smul_eq_mul]; ring

private lemma quadAt_inv_hess {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) (x : Fin n → ℤ) :
    quadAt (gramMatrix Q)⁻¹ (Q.hessian *ᵥ x) = 4 * (Q.eval x : ℝ) := by
  have : (gramMatrix Q)⁻¹ = (4 : ℝ) • dualGram Q := by
    rw [dualGram, smul_smul]; norm_num
  rw [this, quadAt_smul', key_dual hdet, quadAt_gramMatrix]

/-- The bijection $\vec x \mapsto H\vec x$ of $\mathbb{Z}^n$ (for $\det H$ a unit). -/
private def hessEquiv {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) :
    (Fin n → ℤ) ≃ (Fin n → ℤ) where
  toFun := fun x => Q.hessian *ᵥ x
  invFun := fun y => Q.hessian⁻¹ *ᵥ y
  left_inv := fun x => by simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
  right_inv := fun y => by simp [mulVec_mulVec, mul_nonsing_inv _ hdet]

private lemma hessEquiv_apply {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) (x : Fin n → ℤ) :
    hessEquiv hdet x = Q.hessian *ᵥ x := rfl

/-- $\sum_x Q(x) e^{-2\pi y Q(x)}$ converges for $y > 0$. -/
private lemma summable_poly {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {y : ℝ} (hy : 0 < y) :
    Summable fun x : Fin n → ℤ => (Q.eval x : ℝ) * Real.exp (-(2 * Real.pi * y * Q.eval x)) := by
  have hs := (summable_theta_term hQ (z := ((y / 2 : ℝ) : ℂ) * I) (by simp; positivity)).norm
  have him : (((y / 2 : ℝ) : ℂ) * I).im = y / 2 := by simp
  have hpy : 0 < Real.pi * y := by positivity
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) (hs.mul_left (1 / (Real.pi * y)))
  · have : (0 : ℝ) ≤ Q.eval x := by exact_mod_cast Siegel.eval_nonneg hQ x
    positivity
  · rw [norm_theta_term', him]
    have ht : (0 : ℝ) ≤ Q.eval x := by exact_mod_cast Siegel.eval_nonneg hQ x
    set t : ℝ := (Q.eval x : ℝ)
    have hE : Real.exp (-(2 * Real.pi * y * t)) =
        Real.exp (-(Real.pi * y * t)) * Real.exp (-(Real.pi * y * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : 2 * Real.pi * (y / 2) * t = Real.pi * y * t := by ring
    rw [e2, hE]
    set E := Real.exp (-(Real.pi * y * t)) with hEdef
    have hEpos : 0 < E := Real.exp_pos _
    have h1 : Real.pi * y * t * E ≤ 1 := by
      have h0 := Real.add_one_le_exp (Real.pi * y * t)
      have hE2 : Real.exp (Real.pi * y * t) * E = 1 := by
        rw [hEdef, ← Real.exp_add]; simp
      nlinarith
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpy]
    have := mul_le_mul_of_nonneg_left h1 hEpos.le
    nlinarith

end Helpers

/-- **The harmonic polynomial** $P_u(x) = (x\cdot u)^2 - (u\cdot u)(x\cdot x)/n$ of degree $2$ attached to
$u \in \mathbb{R}^n$, evaluated at $x \in \mathbb{Z}^n$; here $x \cdot u$ = `latDot Q x u`, $u \cdot u = 2Q(u)$ and
$x \cdot x = 2Q(x)$. -/
def harmPoly (Q : QuadForm ℤ n) (u : Fin n → ℝ) (x : Fin n → ℤ) : ℝ :=
  latDot Q x u ^ 2 - (2 * Q.evalIn ℝ u) * (2 * (Q.eval x : ℝ)) / n

/-- $f_u(z) = \sum_{x \in \mathbb{Z}^n} (x \cdot u)^2\, e^{2\pi i z Q(x)}$. -/
def thetaLin (Q : QuadForm ℤ n) (u : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑' x : Fin n → ℤ, ((latDot Q x u ^ 2 : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))

/-- $g(z) = \sum_{x \in \mathbb{Z}^n} (x \cdot x)\, e^{2\pi i z Q(x)}$, $x \cdot x = 2Q(x)$.
**Restriction:** the series converges for $\operatorname{Im} z > 0$ when $Q$ is positive definite (neither enforced
by the type; `summable_thetaNorm_term`); where it does not converge the value is $0$ by Lean's `tsum` convention, not
the analytic continuation or the intended value. -/
def thetaNorm (Q : QuadForm ℤ n) (z : ℂ) : ℂ :=
  ∑' x : Fin n → ℤ, ((2 * (Q.eval x : ℝ) : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))

/-- **The theta series with harmonic coefficient** $\vartheta_{L,P_u}(z) = \sum_{x} P_u(x)\, e^{2\pi i z Q(x)}$. -/
@[kb "chenevierlannes2019" "proof of Prop. 2.3.2, p. 35 (theta series with harmonic coefficients)"]
def thetaHarm (Q : QuadForm ℤ n) (u : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑' x : Fin n → ℤ, ((harmPoly Q u x : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))

/-- Absolute convergence of $f_u$ on the upper half plane. -/
theorem summable_thetaLin_term {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (u : Fin n → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    Summable fun x : Fin n → ℤ =>
      ‖((latDot Q x u ^ 2 : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖ := by
  have hA := gramMatrix_posDef hQ
  have h := QuadFormsKB.Analysis.summable_sq_mul_gaussian_quadratic hA (re_neg_two_I_mul' hz)
    (Q.hessian.map (Int.cast : ℤ → ℝ) *ᵥ u)
  refine h.congr (fun x => ?_)
  have e1 : (∑ i, (x i : ℝ) * (Q.hessian.map (Int.cast : ℤ → ℝ) *ᵥ u) i) = latDot Q x u := rfl
  rw [e1, exp_arg Q z x, Complex.ofReal_pow]

/-- Absolute convergence of $g$ on the upper half plane. -/
theorem summable_thetaNorm_term {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {z : ℂ} (hz : 0 < z.im) :
    Summable fun x : Fin n → ℤ =>
      ‖((2 * (Q.eval x : ℝ) : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖ := by
  refine ((summable_poly hQ hz).mul_left 2).congr (fun x => ?_)
  have hq : (0 : ℝ) ≤ Q.eval x := by exact_mod_cast Siegel.eval_nonneg hQ x
  rw [norm_mul, norm_theta_term', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  ring

/-- Pointwise: the harmonic term is a combination of the two. -/
private lemma harm_term (Q : QuadForm ℤ n) (u : Fin n → ℝ) (z : ℂ) (x : Fin n → ℤ) :
    ((harmPoly Q u x : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ)) =
      ((latDot Q x u ^ 2 : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ)) -
        ((2 * Q.evalIn ℝ u / n : ℝ) : ℂ) *
          (((2 * (Q.eval x : ℝ) : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))) := by
  unfold harmPoly; push_cast; ring

/-- Absolute convergence of $\vartheta_{L,P_u}$ on the upper half plane. -/
theorem summable_thetaHarm_term {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (u : Fin n → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    Summable fun x : Fin n → ℤ =>
      ‖((harmPoly Q u x : ℝ) : ℂ) * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖ := by
  have h1 := summable_thetaLin_term hQ u hz
  have h2 := (summable_thetaNorm_term hQ hz).mul_left ‖((2 * Q.evalIn ℝ u / n : ℝ) : ℂ)‖
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (h1.add h2)
  rw [harm_term]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  simp only [norm_mul]

/-- $\vartheta_{L,P_u} = f_u - \frac{u \cdot u}{n}\, g$ on the upper half plane. -/
theorem thetaHarm_eq {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (u : Fin n → ℝ) {z : ℂ} (hz : 0 < z.im) :
    thetaHarm Q u z = thetaLin Q u z - ((2 * Q.evalIn ℝ u / n : ℝ) : ℂ) * thetaNorm Q z := by
  have s1 := (summable_thetaLin_term hQ u hz).of_norm
  have s2 := (summable_thetaNorm_term hQ hz).of_norm.mul_left ((2 * Q.evalIn ℝ u / n : ℝ) : ℂ)
  unfold thetaHarm thetaLin thetaNorm
  rw [← tsum_mul_left, ← s1.tsum_sub s2]
  exact tsum_congr fun x => harm_term Q u z x

/-- Differentiability of the theta series with a general coefficient. -/
private lemma differentiableOn_gen {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (c : (Fin n → ℤ) → ℂ)
    (hs : ∀ z : ℂ, 0 < z.im →
      Summable fun x : Fin n → ℤ => ‖c x * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖) :
    DifferentiableOn ℂ (fun z => ∑' x : Fin n → ℤ, c x * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ)))
      {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0
  have hy0pos : 0 < y0 := by positivity
  set U : Set ℂ := {w : ℂ | y0 < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by show y0 < z.im; linarith
  have hsum := hs ((y0 : ℂ) * I) (by simpa using hy0pos)
  have hD : DifferentiableOn ℂ
      (fun z => ∑' x : Fin n → ℤ, c x * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun x => ?_) hUo (fun x w hw => ?_)
    · exact (by fun_prop : Differentiable ℂ fun w : ℂ =>
        c x * cexp (2 * Real.pi * I * w * (Q.eval x : ℂ))).differentiableOn
    · have hq : (0 : ℝ) ≤ Q.eval x := by exact_mod_cast Siegel.eval_nonneg hQ x
      have hw' : y0 < w.im := hw
      rw [norm_mul, norm_mul, norm_theta_term', norm_theta_term']
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [Real.exp_le_exp, neg_le_neg_iff]
      simp only [mul_im, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one]
      have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hw'.le)) hq
      nlinarith
  exact (hD.differentiableAt (hUo.mem_nhds hzU)).differentiableWithinAt

/-- Uniform bound at $i\infty$ for a general coefficient. -/
private lemma norm_gen_le {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (c : (Fin n → ℤ) → ℂ)
    (hs : ∀ z : ℂ, 0 < z.im →
      Summable fun x : Fin n → ℤ => ‖c x * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖)
    {z : ℂ} (hz : 1 ≤ z.im) :
    ‖∑' x : Fin n → ℤ, c x * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖ ≤
      ∑' x : Fin n → ℤ, ‖c x * cexp (2 * Real.pi * I * I * (Q.eval x : ℂ))‖ := by
  have hsI := hs I (by simp)
  have hsz := hs z (by linarith)
  refine (norm_tsum_le_tsum_norm hsz).trans ?_
  refine Summable.tsum_le_tsum (fun x => ?_) hsz hsI
  have hq : (0 : ℝ) ≤ Q.eval x := by exact_mod_cast Siegel.eval_nonneg hQ x
  rw [norm_mul, norm_mul, norm_theta_term', norm_theta_term']
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  simp only [Complex.I_im]
  have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hz)) hq
  nlinarith

/-- A `tsum` over a (finite) fibre is the corresponding `finsum`. -/
private lemma tsum_repSet_eq {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (c : (Fin n → ℤ) → ℂ) (m : ℤ) :
    ∑' b : repSet Q m, c b = ∑ᶠ x ∈ repSet Q m, c x := by
  have hfin := IntQF.PosDef.repSet_finite hQ m
  rw [tsum_subtype, finsum_mem_def]
  exact tsum_eq_finsum (hfin.subset (Set.support_indicator_subset))

/-- The $q$-expansion for a general coefficient. -/
private lemma hasSum_gen {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (c : (Fin n → ℤ) → ℂ) {z : ℂ}
    (hs : Summable fun x : Fin n → ℤ => ‖c x * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖) :
    HasSum (fun m : ℕ => (∑ᶠ x ∈ repSet Q m, c x) * cexp (2 * Real.pi * I * z * m))
      (∑' x : Fin n → ℤ, c x * cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))) := by
  have hf := hs.of_norm.hasSum
  have h := hf.tsum_fiberwise (fun x => (Q.eval x).toNat)
  have key : ∀ m : ℕ, ∑' b : ↑((fun x : Fin n → ℤ => (Q.eval x).toNat) ⁻¹' {m}),
      c b * cexp (2 * Real.pi * I * z * (Q.eval (b : Fin n → ℤ) : ℂ)) =
        (∑ᶠ x ∈ repSet Q m, c x) * cexp (2 * Real.pi * I * z * m) := by
    intro m
    have hset : (fun x : Fin n → ℤ => (Q.eval x).toNat) ⁻¹' {m} = repSet Q m := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, repSet, Set.mem_ofPred_eq]
      have := Siegel.eval_nonneg hQ x
      omega
    rw [hset]
    have hc : ∀ b : repSet Q m, c b * cexp (2 * Real.pi * I * z * (Q.eval (b : Fin n → ℤ) : ℂ)) =
        c b * cexp (2 * Real.pi * I * z * m) := by
      intro b; rw [show Q.eval (b : Fin n → ℤ) = m from b.2]; push_cast; rfl
    rw [tsum_congr hc, tsum_mul_right, tsum_repSet_eq hQ]
  have hfun : (fun m : ℕ => (∑ᶠ x ∈ repSet Q m, c x) * cexp (2 * Real.pi * I * z * m)) =
      fun m : ℕ => ∑' b : ↑((fun x : Fin n → ℤ => (Q.eval x).toNat) ⁻¹' {m}),
        c b * cexp (2 * Real.pi * I * z * (Q.eval (b : Fin n → ℤ) : ℂ)) :=
    funext fun m => (key m).symm
  rw [hfun]; exact h

/-- $\operatorname{Im}(-1/z) > 0$. -/
private lemma im_neg_inv_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have : (-1 / z).im = z.im / Complex.normSq z := by
    rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
  rw [this]
  exact div_pos hz (Complex.normSq_pos.mpr hz0)

/-- **Inversion law of $f_u$**: for $Q$ even unimodular of dimension $n = 2k$, $4 \mid k$, and
$\operatorname{Im} z > 0$,
$f_u(-1/z) = z^k\big(z^2 f_u(z) - \frac{i}{2\pi}\,z\,(u \cdot u)\,\vartheta_L(z)\big)$, $u \cdot u = 2Q(u)$. -/
theorem thetaLin_S {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ} (hn : n = 2 * k) (hk : 4 ∣ k)
    (u : Fin n → ℝ) {z : ℂ} (hz : 0 < z.im) :
    thetaLin Q u (-1 / z) =
      z ^ k * (z ^ 2 * thetaLin Q u z -
        I / (2 * Real.pi) * z * ((2 * Q.evalIn ℝ u : ℝ) : ℂ) * theta Q z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hQp := hQ.posDef
  have hA := gramMatrix_posDef hQp
  have hunit : IsUnit Q.hessian.det := by rw [hQ.det_one]; exact isUnit_one
  have hw : 0 < (-2 * I * z).re := re_neg_two_I_mul' hz
  have h := QuadFormsKB.Analysis.tsum_sq_gaussian_quadratic hA hw u
  have s1 := ((summable_thetaLin_term hQp u hz).of_norm).mul_left (-4 * (Real.pi : ℂ) ^ 2 * z ^ 2)
  have s2 := (summable_theta_term hQp hz).mul_left (4 * Real.pi * I * z * ((Q.evalIn ℝ u : ℝ) : ℂ))
  have hwinv : (-2 * I * z)⁻¹ = I / (2 * z) := by
    field_simp
    ring_nf
    rw [I_sq]
  -- the dual sum
  have hsum : ∑' y : Fin n → ℤ, ((∑ i, (y i : ℝ) * u i : ℝ) : ℂ) ^ 2 *
      cexp (-Real.pi * (-2 * I * z)⁻¹ * (QuadFormsKB.Analysis.quadAt (gramMatrix Q)⁻¹ y : ℂ)) =
        thetaLin Q u (-1 / z) := by
    refine (Equiv.tsum_eq (hessEquiv hunit) _).symm.trans ?_
    unfold thetaLin
    refine tsum_congr fun x => ?_
    rw [hessEquiv_apply, dot_hx Q x u, quadAt_inv_hess hunit x, Complex.ofReal_pow]
    congr 2
    rw [hwinv]
    push_cast
    field_simp
    ring_nf
  -- the constant
  have hC : (((Real.sqrt (gramMatrix Q).det)⁻¹ : ℝ) : ℂ) * (-2 * I * z)⁻¹ ^ ((n : ℂ) / 2) =
      (z ^ k)⁻¹ := by
    have hk' : ((n : ℂ) / 2) = ((k : ℕ) : ℂ) := by rw [hn]; push_cast; ring
    rw [hk', cpow_natCast]
    have hdetA : (gramMatrix Q).det = (1 / 2 : ℝ) ^ n := by
      rw [← gramDet_eq_det, gramDet, hQ.det_one]; simp [div_eq_mul_inv]
    have hsq : Real.sqrt ((1 / 2 : ℝ) ^ n) = (1 / 2) ^ k := by
      rw [hn, pow_mul']
      exact Real.sqrt_sq (by positivity)
    have hinv : (Real.sqrt (gramMatrix Q).det)⁻¹ = (2 : ℝ) ^ k := by
      rw [hdetA, hsq, one_div, inv_pow, inv_inv]
    rw [hinv]
    obtain ⟨j, hj⟩ := hk
    have hIk : I ^ k = 1 := by rw [hj, pow_mul, I_pow_four, one_pow]
    rw [hwinv, div_pow, hIk]
    push_cast
    field_simp
    rw [mul_pow]
  have h1 : (-4 * (Real.pi : ℂ) ^ 2 * z ^ 2) * thetaLin Q u z +
      (4 * Real.pi * I * z * ((Q.evalIn ℝ u : ℝ) : ℂ)) * theta Q z =
      -4 * (Real.pi : ℂ) ^ 2 *
        (((Real.sqrt (gramMatrix Q).det)⁻¹ : ℝ) * (-2 * I * z)⁻¹ ^ ((n : ℂ) / 2)) *
        thetaLin Q u (-1 / z) := by
    rw [← hsum]
    refine Eq.trans ?_ h
    unfold thetaLin theta
    rw [← tsum_mul_left, ← tsum_mul_left, ← s1.tsum_add s2]
    refine tsum_congr fun x => ?_
    rw [show (QuadFormsKB.Analysis.quadAtR (gramMatrix Q) u : ℝ) = Q.evalIn ℝ u from
        (evalIn_real_eq_gram Q u).symm, dot_gram Q x u, exp_arg Q z x]
    push_cast
    linear_combination (-4 * (Real.pi : ℂ) ^ 2 * z ^ 2 * (latDot Q x u : ℂ) ^ 2 *
      cexp (-Real.pi * (-2 * I * z) * (QuadFormsKB.Analysis.quadAt (gramMatrix Q) x : ℂ))) * I_sq
  rw [hC] at h1
  have hzk : z ^ k ≠ 0 := pow_ne_zero _ hz0
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp at h1 ⊢
  linear_combination h1

/-- The theta series is differentiable with derivative $\pi i\, g$. -/
private lemma hasDerivAt_theta {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (theta Q) ((Real.pi : ℂ) * I * thetaNorm Q z) z := by
  set y0 := z.im / 2 with hy0
  have hy0pos : 0 < y0 := by positivity
  set t : Set ℂ := {w : ℂ | y0 < w.im} with ht_def
  have ht : IsOpen t := isOpen_lt continuous_const Complex.continuous_im
  have htc : IsPreconnected t := (convex_halfSpace_im_gt y0).isPreconnected
  have hzt : z ∈ t := by show y0 < z.im; linarith
  have himy : (((y0 : ℝ) : ℂ) * I).im = y0 := by simp
  have hnorm : ∀ q : ℤ, ‖(2 * (Real.pi : ℂ) * I * (q : ℂ))‖ =
      Real.pi * ‖((2 * (q : ℝ) : ℝ) : ℂ)‖ := by
    intro q
    have : (2 * (Real.pi : ℂ) * I * (q : ℂ)) = (Real.pi : ℂ) * I * ((2 * (q : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hg : ∀ (x : Fin n → ℤ) (w : ℂ),
      HasDerivAt (fun w : ℂ => cexp (2 * Real.pi * I * w * (Q.eval x : ℂ)))
        (cexp (2 * Real.pi * I * w * (Q.eval x : ℂ)) * (2 * Real.pi * I * (Q.eval x : ℂ))) w := by
    intro x w
    have h1 : HasDerivAt (fun w : ℂ => 2 * Real.pi * I * w * (Q.eval x : ℂ))
        (2 * Real.pi * I * (Q.eval x : ℂ)) w := by
      simpa using ((hasDerivAt_id w).const_mul (2 * (Real.pi : ℂ) * I)).mul_const (Q.eval x : ℂ)
    exact h1.cexp
  have hu : Summable (fun x : Fin n → ℤ => Real.pi *
      ‖((2 * (Q.eval x : ℝ) : ℝ) : ℂ) *
        cexp (2 * Real.pi * I * (((y0 : ℝ) : ℂ) * I) * (Q.eval x : ℂ))‖) :=
    (summable_thetaNorm_term hQ (z := ((y0 : ℝ) : ℂ) * I) (by rw [himy]; exact hy0pos)).mul_left _
  have hb : ∀ (x : Fin n → ℤ) (w : ℂ), w ∈ t →
      ‖cexp (2 * Real.pi * I * w * (Q.eval x : ℂ)) * (2 * Real.pi * I * (Q.eval x : ℂ))‖ ≤
        Real.pi * ‖((2 * (Q.eval x : ℝ) : ℝ) : ℂ) *
          cexp (2 * Real.pi * I * (((y0 : ℝ) : ℂ) * I) * (Q.eval x : ℂ))‖ := by
    intro x w hw
    have hq : (0 : ℝ) ≤ Q.eval x := by exact_mod_cast Siegel.eval_nonneg hQ x
    have hw' : y0 < w.im := hw
    rw [norm_mul, hnorm, norm_mul, norm_theta_term', norm_theta_term', himy]
    have hE : Real.exp (-(2 * Real.pi * w.im * Q.eval x)) ≤
        Real.exp (-(2 * Real.pi * y0 * Q.eval x)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hw'.le)) hq
      nlinarith
    have hn0 : 0 ≤ Real.pi * ‖((2 * (Q.eval x : ℝ) : ℝ) : ℂ)‖ := by positivity
    linarith [mul_le_mul_of_nonneg_right hE hn0]
  have hd := hasDerivAt_tsum_of_isPreconnected hu ht htc (fun x w _ => hg x w)
    (fun x w hw => hb x w hw) hzt (summable_theta_term hQ hz) hzt
  have hsum : ∑' x : Fin n → ℤ, cexp (2 * Real.pi * I * z * (Q.eval x : ℂ)) *
      (2 * Real.pi * I * (Q.eval x : ℂ)) = (Real.pi : ℂ) * I * thetaNorm Q z := by
    unfold thetaNorm
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    push_cast; ring
  rw [← hsum]; exact hd

/-- **Inversion law of $g$**: under the hypotheses of `thetaLin_S`,
$g(-1/z) = z^k\big(z^2 g(z) - \frac{i}{2\pi}\,z\, n\,\vartheta_L(z)\big)$ (*proof:* differentiate
$\vartheta_L(-1/z) = z^k\vartheta_L(z)$, `theta_S_unimodular`, using $\vartheta_L' = \pi i\, g$). -/
theorem thetaNorm_S {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ} (hn : n = 2 * k) (hk : 4 ∣ k)
    {z : ℂ} (hz : 0 < z.im) :
    thetaNorm Q (-1 / z) =
      z ^ k * (z ^ 2 * thetaNorm Q z - I / (2 * Real.pi) * z * (n : ℂ) * theta Q z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hw := im_neg_inv_pos hz
  have hnC : (n : ℂ) = 2 * k := by rw [hn]; push_cast; ring
  have h1 : HasDerivAt (fun w : ℂ => theta Q (-1 / w))
      (((Real.pi : ℂ) * I * thetaNorm Q (-1 / z)) * (z ^ 2)⁻¹) z := by
    have hin : HasDerivAt (fun w : ℂ => -1 / w) ((z ^ 2)⁻¹) z := by
      have := (hasDerivAt_inv hz0).neg
      convert this using 1
      all_goals first | (funext w; simp [neg_div]) | simp
    exact (hasDerivAt_theta hQ.posDef hw).comp z hin
  have h2 : HasDerivAt (fun w : ℂ => w ^ k * theta Q w)
      ((k : ℂ) * z ^ (k - 1) * theta Q z + z ^ k * ((Real.pi : ℂ) * I * thetaNorm Q z)) z :=
    (hasDerivAt_pow k z).mul (hasDerivAt_theta hQ.posDef hz)
  have heq : (fun w : ℂ => theta Q (-1 / w)) =ᶠ[nhds z] fun w : ℂ => w ^ k * theta Q w :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
      (fun w hw => theta_S_unimodular hQ.posDef hQ.det_one hn hk hw)
  have huniq := h1.unique (h2.congr_of_eventuallyEq heq)
  have e : (Real.pi : ℂ) * I * thetaNorm Q (-1 / z) =
      ((k : ℂ) * z ^ (k - 1) * theta Q z + z ^ k * ((Real.pi : ℂ) * I * thetaNorm Q z)) * z ^ 2 := by
    rw [← huniq]; field_simp
  have hpow : (k : ℂ) * z ^ (k - 1) * z ^ 2 = k * z ^ (k + 1) := by
    rcases k with _ | k <;> simp <;> ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hpiI : (Real.pi : ℂ) * I ≠ 0 := mul_ne_zero hpi I_ne_zero
  have hcancel : (Real.pi : ℂ) * I * (I / (2 * Real.pi)) * 2 = I ^ 2 := by
    field_simp
  rw [I_sq] at hcancel
  apply mul_left_cancel₀ hpiI
  rw [e, hnC]
  linear_combination (theta Q z) * hpow + ((k : ℂ) * z ^ (k + 1) * theta Q z) * hcancel

/-- **Inversion law of the harmonic theta series**: for $Q$ even unimodular of dimension $n = 2k$, $4 \mid k$,
$\vartheta_{L,P_u}(-1/z) = z^{k+2}\,\vartheta_{L,P_u}(z)$. -/
@[kb "chenevierlannes2019" "proof of Prop. 2.3.2, p. 35 (modularity of the harmonic theta series)"]
theorem thetaHarm_S {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ} (hn : n = 2 * k) (hk : 4 ∣ k)
    (u : Fin n → ℝ) {z : ℂ} (hz : 0 < z.im) :
    thetaHarm Q u (-1 / z) = z ^ (k + 2) * thetaHarm Q u z := by
  have hz' := im_neg_inv_pos hz
  have hcn : ((2 * Q.evalIn ℝ u / n : ℝ) : ℂ) * (n : ℂ) = ((2 * Q.evalIn ℝ u : ℝ) : ℂ) := by
    by_cases hn0 : n = 0
    · have h0 : Q.evalIn ℝ u = 0 := by
        rw [evalIn_real_eq_gram]; subst hn0; simp
      rw [h0]; simp
    · have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
      push_cast; field_simp
  rw [thetaHarm_eq hQ.posDef u hz', thetaHarm_eq hQ.posDef u hz, thetaLin_S hQ hn hk u hz,
    thetaNorm_S hQ hn hk hz]
  linear_combination (z ^ (k + 1) * (I / (2 * (Real.pi : ℂ))) * theta Q z) * hcn

/-- $\vartheta_{L,P_u}(z + 1) = \vartheta_{L,P_u}(z)$. -/
theorem thetaHarm_add_one (Q : QuadForm ℤ n) (u : Fin n → ℝ) (z : ℂ) :
    thetaHarm Q u (z + 1) = thetaHarm Q u z := by
  unfold thetaHarm
  congr 1; funext x
  congr 1
  rw [show 2 * Real.pi * I * (z + 1) * (Q.eval x : ℂ) =
      2 * Real.pi * I * z * (Q.eval x : ℂ) + (Q.eval x : ℤ) * (2 * Real.pi * I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- $\vartheta_{L,P_u}$ is holomorphic on the upper half plane. -/
theorem differentiableOn_thetaHarm {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (u : Fin n → ℝ) :
    DifferentiableOn ℂ (thetaHarm Q u) {z : ℂ | 0 < z.im} :=
  differentiableOn_gen hQ (fun x => ((harmPoly Q u x : ℝ) : ℂ))
    (fun z hz => summable_thetaHarm_term hQ u hz)

/-- $\vartheta_{L,P_u}$ is bounded on $\operatorname{Im} z \ge 1$. -/
theorem norm_thetaHarm_le {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (u : Fin n → ℝ) {z : ℂ}
    (hz : 1 ≤ z.im) :
    ‖thetaHarm Q u z‖ ≤ ∑' x : Fin n → ℤ,
      ‖((harmPoly Q u x : ℝ) : ℂ) * cexp (2 * Real.pi * I * I * (Q.eval x : ℂ))‖ :=
  norm_gen_le hQ (fun x => ((harmPoly Q u x : ℝ) : ℂ)) (fun z hz => summable_thetaHarm_term hQ u hz) hz

/-- **The $q$-expansion** of $\vartheta_{L,P_u}$: $\vartheta_{L,P_u}(z) = \sum_{m \ge 0} c_m\, e^{2\pi i m z}$ with
$c_m = \sum_{Q(x) = m} P_u(x)$ (a finite sum). -/
theorem hasSum_thetaHarm {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (u : Fin n → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    HasSum (fun m : ℕ => (∑ᶠ x ∈ repSet Q m, ((harmPoly Q u x : ℝ) : ℂ)) * cexp (2 * Real.pi * I * z * m))
      (thetaHarm Q u z) :=
  hasSum_gen hQ (fun x => ((harmPoly Q u x : ℝ) : ℂ)) (summable_thetaHarm_term hQ u hz)

/-- Slash invariance under $S$ from the inversion law. -/
private lemma slash_S_gen (G : ℂ → ℂ) (m : ℕ) (h : ∀ z : ℂ, 0 < z.im → G (-1 / z) = z ^ m * G z) :
    (fun τ : ℍ => G τ) ∣[(m : ℤ)] ModularGroup.S = fun τ : ℍ => G τ := by
  ext τ
  have h' := h τ τ.im_pos
  suffices G (-(τ : ℂ)⁻¹) * ((τ : ℂ) ^ m)⁻¹ = G τ by
    rw [SL_slash_apply, ModularGroup.denom_S, UpperHalfPlane.modular_S_smul]
    simpa using this
  rw [show -(τ : ℂ)⁻¹ = -1 / (τ : ℂ) by rw [neg_div, one_div], h']
  field_simp [τ.ne_zero]

/-- Slash invariance under $T$ from periodicity. -/
private lemma slash_T_gen (G : ℂ → ℂ) (m : ℤ) (h : ∀ z : ℂ, G (z + 1) = G z) :
    (fun τ : ℍ => G τ) ∣[m] ModularGroup.T = fun τ : ℍ => G τ := by
  ext τ
  rw [SL_slash_apply, ModularGroup.denom_apply, modular_T_smul]
  simp [ModularGroup.coe_T, coe_vadd, add_comm (1 : ℂ), h]

/-- **The harmonic theta series is a modular form of weight $k + 2$** for $\mathrm{SL}_2(\mathbb{Z})$, for $Q$ even
unimodular of dimension $n = 2k$ with $4 \mid k$. -/
@[kb "chenevierlannes2019" "proof of Prop. 2.3.2, p. 35 (θ_{L,P} ∈ M_{n/2+2})"]
def thetaHarmMF {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ} (hn : n = 2 * k) (hk : 4 ∣ k)
    (u : Fin n → ℝ) : ModularForm 𝒮ℒ ((k + 2 : ℕ) : ℤ) where
  toFun := fun τ : ℍ => thetaHarm Q u τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z
      (slash_S_gen (thetaHarm Q u) (k + 2) (fun z hz => thetaHarm_S hQ hn hk u hz))
      (slash_T_gen (thetaHarm Q u) _ (thetaHarm_add_one Q u)) A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (differentiableOn_thetaHarm hQ.posDef u).congr fun z hz => ?_
    simp [ofComplex_apply_of_im_pos hz]
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z
      (slash_S_gen (thetaHarm Q u) (k + 2) (fun z hz => thetaHarm_S hQ hn hk u hz))
      (slash_T_gen (thetaHarm Q u) _ (thetaHarm_add_one Q u))]
    rw [isBoundedAtImInfty_iff]
    exact ⟨_, 1, fun z hz => norm_thetaHarm_le hQ.posDef u hz⟩

@[simp] theorem thetaHarmMF_apply {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ} (hn : n = 2 * k)
    (hk : 4 ∣ k) (u : Fin n → ℝ) (τ : ℍ) : thetaHarmMF hQ hn hk u τ = thetaHarm Q u τ := rfl

private theorem thetaHarmMF_hasSum {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) (u : Fin n → ℝ) (τ : ℍ) :
    HasSum (fun m : ℕ => (∑ᶠ x ∈ repSet Q m, ((harmPoly Q u x : ℝ) : ℂ)) •
      Function.Periodic.qParam 1 τ ^ m) (thetaHarmMF hQ hn hk u τ) := by
  rw [thetaHarmMF_apply]
  convert hasSum_thetaHarm hQ.posDef u τ.im_pos using 2 with m
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- The $q$-expansion coefficients of `thetaHarmMF` are $\sum_{Q(x) = m} P_u(x)$. -/
theorem qExpansion_thetaHarmMF_coeff {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) (u : Fin n → ℝ) (m : ℕ) :
    (qExpansion 1 (thetaHarmMF hQ hn hk u)).coeff m = ∑ᶠ x ∈ repSet Q m, ((harmPoly Q u x : ℝ) : ℂ) :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (thetaHarmMF_hasSum hQ hn hk u) m).symm

/-- A level-one form of weight $2, 6, 10, 14$ with vanishing constant term is zero. -/
private lemma levelOne_eq_zero {w : ℤ} (hw : w = 2 ∨ w = 6 ∨ w = 10 ∨ w = 14) (f : ModularForm 𝒮ℒ w)
    (h0 : (qExpansion 1 f).coeff 0 = 0) : f = 0 := by
  rcases hw with rfl | rfl | rfl | rfl
  · exact rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f
  · have hg := rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := 6) (by norm_num)) (ModularForm.toCuspForm f h0)
    exact DFunLike.ext _ _ fun τ => by simpa using congrArg (fun g : CuspForm 𝒮ℒ 6 => g τ) hg
  · have hg := rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := 10) (by norm_num)) (ModularForm.toCuspForm f h0)
    exact DFunLike.ext _ _ fun τ => by simpa using congrArg (fun g : CuspForm 𝒮ℒ 10 => g τ) hg
  · have hr : Module.rank ℂ (CuspForm 𝒮ℒ 14) = 0 := by
      refine CuspForm.discriminantEquiv.rank_eq.trans ?_
      have h12 : (14 : ℤ) - 12 = 2 := by norm_num
      rw [h12]
      exact levelOne_weight_two_rank_zero
    have hg := rank_zero_iff_forall_zero.mp hr (ModularForm.toCuspForm f h0)
    exact DFunLike.ext _ _ fun τ => by simpa using congrArg (fun g : CuspForm 𝒮ℒ 14 => g τ) hg

/-- **Vanishing in weights $6$, $10$, $14$**: for $k \le 12$ the harmonic theta series is $0$ (a cusp form of weight
$k + 2 \in \{6, 10, 14\}$ for $\mathrm{SL}_2(\mathbb{Z})$). -/
@[kb "chenevierlannes2019" "proof of Prop. 2.3.2, p. 35 (no cusp forms of weight 6, 10, 14)"]
theorem thetaHarmMF_eq_zero {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ} (hn : n = 2 * k)
    (hk : 4 ∣ k) (hk12 : k ≤ 12) (u : Fin n → ℝ) : thetaHarmMF hQ hn hk u = 0 := by
  have h0 : (qExpansion 1 (thetaHarmMF hQ hn hk u)).coeff 0 = 0 := by
    rw [qExpansion_thetaHarmMF_coeff]
    have hrep : repSet Q ((0 : ℕ) : ℤ) = {0} := by
      ext x
      simp only [repSet, Set.mem_setOf_eq, Set.mem_singleton_iff, Nat.cast_zero]
      constructor
      · intro h; by_contra hx; have := hQ.posDef x hx; omega
      · rintro rfl; simp [QuadForm.evalIn]
    rw [hrep, finsum_mem_singleton]
    simp [harmPoly, latDot, QuadForm.evalIn]
  have hw : ((k + 2 : ℕ) : ℤ) = 2 ∨ ((k + 2 : ℕ) : ℤ) = 6 ∨ ((k + 2 : ℕ) : ℤ) = 10 ∨
      ((k + 2 : ℕ) : ℤ) = 14 := by
    obtain ⟨j, hj⟩ := hk
    omega
  exact levelOne_eq_zero hw _ h0

/-- **Venkov's identity for $n \le 24$**: for $Q$ even unimodular of dimension $n = 2k$, $4 \mid k$, $k \le 12$, and
$x \in \mathbb{R}^n$, $\sum_{\alpha \in R(L)} (\alpha \cdot x)^2 = \frac{2|R(L)|}{n}\, x \cdot x$ (the coefficient of
$q^1$ in `thetaHarmMF_eq_zero`). -/
theorem venkov_root_sum_of_le {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {k : ℕ} (hn : n = 2 * k)
    (hk : 4 ∣ k) (hk12 : k ≤ 12) (x : Fin n → ℝ) :
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 2 * ((rootSet Q).ncard : ℝ) / n * (2 * Q.evalIn ℝ x) := by
  have h0 := thetaHarmMF_eq_zero hQ hn hk hk12 x
  have hrep : repSet Q ((1 : ℕ) : ℤ) = rootSet Q := by
    ext y; simp [repSet, rootSet]
  have hc : ∑ᶠ y ∈ rootSet Q, ((harmPoly Q x y : ℝ) : ℂ) = 0 := by
    rw [← hrep, ← qExpansion_thetaHarmMF_coeff hQ hn hk x 1, h0]
    simp [qExpansion_zero]
  have hfin := rootSet_finite hQ.posDef
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hc
  have hr : ∑ y ∈ hfin.toFinset, harmPoly Q x y = 0 := by exact_mod_cast hc
  have hterm : ∀ y ∈ hfin.toFinset, harmPoly Q x y =
      latDot Q y x ^ 2 - 2 * Q.evalIn ℝ x * 2 / n := by
    intro y hy
    have h1 : Q.eval y = 1 := by simpa [rootSet] using hy
    unfold harmPoly; rw [h1]; push_cast; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hr
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin]
  have := sub_eq_zero.mp hr
  rw [this]; ring

/-- **Proposition 2.3.2 (Venkov) for $n = 8$** (Chenevier–Lannes, p. 35). Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 2.3.2, p. 35 (n = 8)"]
theorem venkovRootSum_eight : VenkovRootSum 8 :=
  ⟨fun _Q hQ x => venkov_root_sum_of_le hQ (k := 4) rfl (dvd_refl 4) (by norm_num) x⟩

/-- **Proposition 2.3.2 (Venkov) for $n = 16$** (Chenevier–Lannes, p. 35). Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 2.3.2, p. 35 (n = 16)"]
theorem venkovRootSum_sixteen : VenkovRootSum 16 :=
  ⟨fun _Q hQ x => venkov_root_sum_of_le hQ (k := 8) rfl ⟨2, rfl⟩ (by norm_num) x⟩

/-- **Proposition 2.3.2 (Venkov) for $n = 24$** (Chenevier–Lannes, p. 35). Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 2.3.2, p. 35 (n = 24)"]
theorem venkovRootSum_twentyFour : VenkovRootSum 24 :=
  ⟨fun _Q hQ x => venkov_root_sum_of_le hQ (k := 12) rfl ⟨3, rfl⟩ (by norm_num) x⟩

end

end QuadFormsKB.ChenevierLannes