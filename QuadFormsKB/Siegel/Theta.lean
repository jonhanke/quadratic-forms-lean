/-
# Theta series of a positive definite form

For an integral form $Q$ in $n$ variables (Hessian $H$, Gram matrix $A = H/2$, so $Q(\vec{x}) = \vec{x}^{\mathsf T} A \vec{x}$)
and $z$ in the upper half plane $\mathbb{H} = \{\operatorname{Im} z > 0\}$:

* `theta Q z` $= \Theta_Q(z) = \sum_{\vec{x} \in \mathbb{Z}^n} e(z\,Q(\vec{x}))$, $e(t) = e^{2\pi i t}$ (Hanke 2004, (1.1)).
* `hasSum_theta`: $\Theta_Q(z) = \sum_{m \ge 0} r_Q(m)\, q^m$, $q = e(z)$, with $r_Q$ = `repNum`.
* `differentiableOn_theta`: $\Theta_Q$ is holomorphic on $\mathbb{H}$.
* `theta_S`: the inversion law
  $$\Theta_Q(-1/z) = \Big(\frac{-iz}{2}\Big)^{n/2} D^{-1/2}\, \Theta_{Q^*}(z), \qquad D = \det A,$$
  and `theta_S'`: the same as $(-iz)^{n/2} (\det H)^{-1/2}\, \Theta_{Q^*}(z)$, where
  $Q^*(\vec{y}) = \tfrac14 \vec{y}^{\mathsf T} A^{-1} \vec{y} = \tfrac12 \vec{y}^{\mathsf T} H^{-1} \vec{y}$ (`dualGram`), i.e. $Q$ on the dual
  lattice $H^{-1}\mathbb{Z}^n$, and all powers are principal branches (`Complex.cpow`).
* Sanity checks: $\Theta_{I_1}(z) = \vartheta(2z)$ (Mathlib's `jacobiTheta`) with the $n = 1$ law equal to Mathlib's
  `jacobiTheta_S_smul`, and $\Theta_{I_4}(-1/z) = -\tfrac{z^2}{4}\,\Theta_{I_4}(z/4)$.
-/
import QuadFormsKB.Analysis.LatticePoisson
import QuadFormsKB.Siegel.Archimedean
import QuadFormsKB.Siegel.FourSquares

open Complex Matrix Filter Topology
open QuadFormsKB.Analysis (quadAt)

namespace QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-! ### Theta series of a real quadratic form -/

/-- **The theta series of a real matrix** $A$ (used for real symmetric positive definite $A$):
$$\Theta_A(z) = \sum_{\vec{x} \in \mathbb{Z}^n} e^{2\pi i z\, \vec{x}^{\mathsf T} A \vec{x}}, \qquad z \in \mathbb{C}$$
(a `tsum`; it converges absolutely for $A$ positive definite and $\operatorname{Im} z > 0$, `summable_thetaGram_term`). -/
def thetaGram (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) : ℂ :=
  ∑' x : Fin n → ℤ, cexp (2 * Real.pi * I * z * (quadAt A x : ℂ))

/-- The term $e^{2\pi i z q}$ is $e^{-\pi w q}$ with $w = -2iz$. -/
private lemma term_eq (z : ℂ) (q : ℝ) :
    cexp (2 * Real.pi * I * z * (q : ℂ)) = cexp (-Real.pi * (-2 * I * z) * (q : ℂ)) := by
  congr 1; ring

private lemma re_neg_two_I_mul {z : ℂ} (hz : 0 < z.im) : 0 < (-2 * I * z).re := by
  simp [Complex.mul_re]; linarith

/-- **Absolute convergence** of $\Theta_A(z)$ for $A$ positive definite and $\operatorname{Im} z > 0$. -/
theorem summable_thetaGram_term {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {z : ℂ}
    (hz : 0 < z.im) :
    Summable fun x : Fin n → ℤ => ‖cexp (2 * Real.pi * I * z * (quadAt A x : ℂ))‖ := by
  simp_rw [term_eq]
  exact Analysis.summable_norm_gaussian_quadratic hA (re_neg_two_I_mul hz)

private lemma quadAt_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℤ) :
    quadAt (c • A) x = c * quadAt A x := by
  simp [quadAt, smul_mulVec, dotProduct_smul]

lemma quadAt_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (x : Fin n → ℤ) :
    0 ≤ quadAt A x := by
  simpa using hA.posSemidef.dotProduct_mulVec_nonneg (fun i => (x i : ℝ))

/-- **Theta inversion for a real positive definite matrix** $A$: for $\operatorname{Im} z > 0$,
$$\Theta_A(-1/z) = (\det A)^{-1/2} \Big(\frac{-iz}{2}\Big)^{n/2}\, \Theta_{A^{-1}/4}(z),$$
with the principal branch of $(-iz/2)^{n/2}$ (`Complex.cpow`; $-iz/2$ lies in the right half plane).
*Proof:* `Analysis.tsum_gaussian_quadratic` with $S = A$ and $w = 2i/z$, so $w^{-1} = -iz/2$. -/
@[kb "serre1973" "Ch. VII §6.2, theta of a lattice [unverified]"]
theorem thetaGram_S {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {z : ℂ} (hz : 0 < z.im) :
    thetaGram A (-1 / z) =
      ((Real.sqrt A.det)⁻¹ : ℝ) * (-I * z / 2) ^ ((n : ℂ) / 2) * thetaGram ((1 / 4 : ℝ) • A⁻¹) z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  set w : ℂ := 2 * I / z with hw
  have hwre : 0 < w.re := by
    have : w = (2 / Complex.normSq z : ℝ) * (I * (starRingEnd ℂ) z) := by
      rw [hw, div_eq_mul_inv, Complex.inv_def]; push_cast; ring
    rw [this, Complex.re_ofReal_mul]
    have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    simp only [mul_re, I_re, conj_re, zero_mul, I_im, conj_im, one_mul, zero_sub, neg_neg]
    positivity
  have hwinv : w⁻¹ = -I * z / 2 := by
    rw [hw]; field_simp; rw [I_sq]; ring
  have h := Analysis.tsum_gaussian_quadratic hA hwre
  rw [hwinv] at h
  unfold thetaGram
  have hl : ∀ x : Fin n → ℤ, cexp (2 * Real.pi * I * (-1 / z) * (quadAt A x : ℂ)) =
      cexp (-Real.pi * w * (quadAt A x : ℂ)) := by
    intro x; congr 1; rw [hw]; field_simp
  have hr : ∀ y : Fin n → ℤ, cexp (-Real.pi * (-I * z / 2) * (quadAt A⁻¹ y : ℂ)) =
      cexp (2 * Real.pi * I * z * (quadAt ((1 / 4 : ℝ) • A⁻¹) y : ℂ)) := by
    intro y; congr 1; rw [quadAt_smul]; push_cast; ring
  simp_rw [hl, h, hr]

/-! ### The theta series of an integral form -/

/-- **The theta series of an integral quadratic form** $Q$ in $n$ variables:
$$\Theta_Q(z) = \sum_{\vec{x} \in \mathbb{Z}^n} e(z\, Q(\vec{x})), \qquad e(t) = e^{2\pi i t},\ z \in \mathbb{C},$$
a `tsum` over $\mathbb{Z}^n$. For $Q$ positive definite and $\operatorname{Im} z > 0$ it converges absolutely and equals
$\sum_{m \ge 0} r_Q(m) e(mz)$ (`hasSum_theta`), Hanke's (1.1). -/
@[kb "hanke2004" "(1.1), p. 352"]
def theta (Q : QuadForm ℤ n) (z : ℂ) : ℂ :=
  ∑' x : Fin n → ℤ, cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))

/-- $\vec{x}^{\mathsf T} A \vec{x} = Q(\vec{x})$ for the Gram matrix $A = H/2$ and $\vec{x} \in \mathbb{Z}^n$. -/
theorem quadAt_gramMatrix (Q : QuadForm ℤ n) (x : Fin n → ℤ) :
    quadAt (gramMatrix Q) x = (Q.eval x : ℝ) := by
  rw [quadAt, ← evalIn_real_eq_gram, evalIn_intCast]

/-- $\Theta_Q = \Theta_A$ for the Gram matrix $A = H/2$. -/
theorem theta_eq_thetaGram (Q : QuadForm ℤ n) (z : ℂ) : theta Q z = thetaGram (gramMatrix Q) z := by
  simp [theta, thetaGram, quadAt_gramMatrix]

/-- The Gram matrix of a positive definite integral form is positive definite (as a real matrix). -/
theorem gramMatrix_posDef {Q : IntQF n} (hQ : Q.PosDef) : (gramMatrix Q).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (gramMatrix_isHermitian Q) fun x hx => by
    simpa [← evalIn_real_eq_gram] using hQ.evalIn_real_pos x hx

/-- **The dual Gram matrix** $A^* = \tfrac14 A^{-1} = \tfrac12 H^{-1}$, so that
$Q^*(\vec{y}) = \vec{y}^{\mathsf T} A^* \vec{y} = \tfrac12 \vec{y}^{\mathsf T} H^{-1}\vec{y} = Q(H^{-1}\vec{y})$: the form $Q$ on the dual lattice
$L^\# = H^{-1}\mathbb{Z}^n = \{\vec{v} \in \mathbb{Q}^n : \vec{v}^{\mathsf T} H \mathbb{Z}^n \subseteq \mathbb{Z}\}$, written in the coordinates
$\vec{y} = H\vec{v} \in \mathbb{Z}^n$. Its values are rational, not integral in general. -/
def dualGram (Q : QuadForm ℤ n) : Matrix (Fin n) (Fin n) ℝ := (1 / 4 : ℝ) • (gramMatrix Q)⁻¹

/-- **The theta series of the dual form** $\Theta_{Q^*}(z) = \sum_{\vec{y} \in \mathbb{Z}^n} e(z\, Q^*(\vec{y}))$,
$Q^*(\vec{y}) = \tfrac14 \vec{y}^{\mathsf T} A^{-1}\vec{y}$ (`dualGram`). -/
def thetaDual (Q : QuadForm ℤ n) (z : ℂ) : ℂ := thetaGram (dualGram Q) z

/-- **Theta inversion for a positive definite integral form** (Gram normalization): for $\operatorname{Im} z > 0$,
$$\Theta_Q(-1/z) = \Big(\frac{-iz}{2}\Big)^{n/2} D^{-1/2}\, \Theta_{Q^*}(z),$$
where $D$ = `gramDet Q` $= \det(H/2)$ (Hanke's $D$), $Q^*$ is the dual form (`dualGram`), and the power is the
principal branch (`Complex.cpow`) of a number in the right half plane. For $n$ even it is the polynomial
$(-iz/2)^{n/2}$. -/
@[kb "serre1973" "Ch. VII §6.2, theta of a lattice [unverified]"]
theorem theta_S {Q : IntQF n} (hQ : Q.PosDef) {z : ℂ} (hz : 0 < z.im) :
    theta Q (-1 / z) =
      (-I * z / 2) ^ ((n : ℂ) / 2) * ((Real.sqrt (gramDet Q))⁻¹ : ℝ) * thetaDual Q z := by
  rw [theta_eq_thetaGram, thetaGram_S (gramMatrix_posDef hQ) hz, gramDet_eq_det, thetaDual, dualGram]
  ring


/-- **$\Theta_A$ is holomorphic on the upper half plane** for $A$ real positive definite: the series converges
uniformly on $\{\operatorname{Im} z > y_0\}$ for every $y_0 > 0$ (Weierstrass M-test with the terms at $z = i y_0$). -/
theorem differentiableOn_thetaGram {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    DifferentiableOn ℂ (thetaGram A) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0
  have hy0pos : 0 < y0 := by positivity
  set U : Set ℂ := {w : ℂ | y0 < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by show y0 < z.im; linarith
  have hsum := summable_thetaGram_term hA (z := (y0 * I : ℂ)) (by simpa using hy0pos)
  have hD : DifferentiableOn ℂ (thetaGram A) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun x => ?_) hUo (fun x w hw => ?_)
    · exact (by fun_prop : Differentiable ℂ fun w : ℂ => cexp (2 * Real.pi * I * w * (quadAt A x : ℂ))).differentiableOn
    · have hq := quadAt_nonneg hA x
      have hw' : y0 < w.im := hw
      rw [Complex.norm_exp, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
      have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hw'.le)) hq
      nlinarith
  exact (hD.differentiableAt (hUo.mem_nhds hzU)).differentiableWithinAt

/-- **$\Theta_Q$ is holomorphic on the upper half plane** $\{z : \operatorname{Im} z > 0\}$, for $Q$ positive definite. -/
@[kb "hanke2004" "§4, p. 364 (holomorphy part of modularity)"]
theorem differentiableOn_theta {Q : IntQF n} (hQ : Q.PosDef) :
    DifferentiableOn ℂ (theta Q) {z : ℂ | 0 < z.im} := by
  have : theta Q = thetaGram (gramMatrix Q) := funext (theta_eq_thetaGram Q)
  rw [this]
  exact differentiableOn_thetaGram (gramMatrix_posDef hQ)


/-- A positive definite integral form takes nonnegative values on $\mathbb{Z}^n$. -/
theorem eval_nonneg {Q : IntQF n} (hQ : Q.PosDef) (x : Fin n → ℤ) : 0 ≤ Q.eval x := by
  by_cases hx : x = 0
  · subst hx; simp [QuadForm.evalIn]
  · exact (hQ x hx).le

/-- **Absolute convergence** of $\Theta_Q(z)$ for $Q$ positive definite and $\operatorname{Im} z > 0$. -/
theorem summable_theta_term {Q : IntQF n} (hQ : Q.PosDef) {z : ℂ} (hz : 0 < z.im) :
    Summable fun x : Fin n → ℤ => cexp (2 * Real.pi * I * z * (Q.eval x : ℂ)) := by
  have h := summable_thetaGram_term (gramMatrix_posDef hQ) hz
  simp only [quadAt_gramMatrix, ofReal_intCast] at h
  exact h.of_norm

/-- **The $q$-expansion** (Hanke 2004, (1.1)): for $Q$ positive definite and $\operatorname{Im} z > 0$,
$$\Theta_Q(z) = \sum_{m \ge 0} r_Q(m)\, e^{2\pi i m z},$$
with $r_Q(m)$ = `repNum Q m` $= \#\{\vec{x} \in \mathbb{Z}^n : Q(\vec{x}) = m\}$; the series converges (it is a regrouping of the
absolutely convergent series over $\mathbb{Z}^n$ by the value $Q(\vec{x})$). -/
@[kb "hanke2004" "(1.1), p. 352"]
theorem hasSum_theta {Q : IntQF n} (hQ : Q.PosDef) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m : ℕ => (repNum Q m : ℂ) * cexp (2 * Real.pi * I * z * m)) (theta Q z) := by
  have hf := (summable_theta_term hQ hz).hasSum
  have h := hf.tsum_fiberwise (fun x => (Q.eval x).toNat)
  convert h using 1
  swap; · rfl
  funext m
  have hset : (fun x : Fin n → ℤ => (Q.eval x).toNat) ⁻¹' {m} = repSet Q m := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, repSet, Set.mem_ofPred_eq]
    have := eval_nonneg hQ x
    omega
  rw [hset]
  have hc : ∀ b : repSet Q m, cexp (2 * Real.pi * I * z * (Q.eval (b : Fin n → ℤ) : ℂ)) =
      cexp (2 * Real.pi * I * z * m) := by
    intro b; rw [show Q.eval (b : Fin n → ℤ) = m from b.2]; push_cast; rfl
  rw [tsum_congr hc, tsum_const, nsmul_eq_mul, repNum]


private lemma ofReal_mul_cpow {c : ℝ} (hc : 0 < c) {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    ((c : ℂ) * x) ^ s = (c : ℂ) ^ s * x ^ s := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hc' hx), cpow_def_of_ne_zero hc', cpow_def_of_ne_zero hx,
    log_ofReal_mul hc hx, ← Complex.exp_add, add_mul, ofReal_log hc.le]

private lemma half_rpow_mul_inv_sqrt (n : ℕ) (D : ℝ) :
    (1 / 2 : ℝ) ^ ((n : ℝ) / 2) * (Real.sqrt D)⁻¹ = (Real.sqrt (2 ^ n * D))⁻¹ := by
  rw [Real.sqrt_mul (by positivity), mul_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow (2 ^ n),
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.div_rpow (by norm_num) (by norm_num),
    Real.one_rpow, one_div]
  congr 3; ring

/-- **Theta inversion, Hessian normalization:** for $Q$ positive definite and $\operatorname{Im} z > 0$,
$$\Theta_Q(-1/z) = (-iz)^{n/2} (\det H)^{-1/2}\, \Theta_{Q^*}(z),$$
with $H$ the Hessian ($\det H = 2^n D > 0$), $Q^*(\vec{y}) = \tfrac12\vec{y}^{\mathsf T}H^{-1}\vec{y}$ (`dualGram`), and the
principal branch of $(-iz)^{n/2}$ ($-iz$ lies in the right half plane). Equivalent to `theta_S` because
$(-iz/2)^{n/2} = 2^{-n/2}(-iz)^{n/2}$ for the principal branch. -/
@[kb "serre1973" "Ch. VII §6.2, theta of a lattice [unverified]"]
theorem theta_S' {Q : IntQF n} (hQ : Q.PosDef) {z : ℂ} (hz : 0 < z.im) :
    theta Q (-1 / z) =
      (-I * z) ^ ((n : ℂ) / 2) * ((Real.sqrt (Q.hessian.det : ℝ))⁻¹ : ℝ) * thetaDual Q z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hx : -I * z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  have hD : 0 ≤ gramDet Q := by
    rw [gramDet_eq_det]; exact (gramMatrix_posDef hQ).det_pos.le
  have hH : (Q.hessian.det : ℝ) = 2 ^ n * gramDet Q := by
    rw [gramDet]; field_simp
  rw [theta_S hQ hz, show -I * z / 2 = ((1 / 2 : ℝ) : ℂ) * (-I * z) by push_cast; ring,
    ofReal_mul_cpow (by norm_num) hx, hH, ← half_rpow_mul_inv_sqrt n,
    show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by norm_num)]
  push_cast
  ring


/-! ### Sanity checks: sums of squares and Jacobi's theta function -/

/-- The Gram matrix of $I_n = x_0^2 + \dots + x_{n-1}^2$ is the identity. -/
theorem gramMatrix_sumSq : gramMatrix (sumSq n) = 1 := by
  rw [gramMatrix, hessian_sumSq]
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- $D(I_n) = 1$. -/
theorem gramDet_sumSq : gramDet (sumSq n) = 1 := by
  rw [gramDet_eq_det, gramMatrix_sumSq, det_one]

/-- $\Theta_{cA}(z) = \Theta_A(cz)$ for real $c$. -/
theorem thetaGram_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) :
    thetaGram (c • A) z = thetaGram A (c * z) := by
  unfold thetaGram
  congr 1; funext x
  congr 1
  simp only [quadAt, smul_mulVec, dotProduct_smul, smul_eq_mul]
  push_cast; ring

/-- $I_n^* = \tfrac14 I_n$, so $\Theta_{I_n^*}(z) = \Theta_{I_n}(z/4)$. -/
theorem thetaDual_sumSq (z : ℂ) : thetaDual (sumSq n) z = theta (sumSq n) (z / 4) := by
  rw [thetaDual, dualGram, gramMatrix_sumSq, inv_one, thetaGram_smul, theta_eq_thetaGram,
    gramMatrix_sumSq]
  congr 1; push_cast; ring

/-- **Inversion for $n$ squares:** $\Theta_{I_n}(-1/z) = (-iz/2)^{n/2}\,\Theta_{I_n}(z/4)$ for $\operatorname{Im} z > 0$. -/
theorem theta_sumSq_S {z : ℂ} (hz : 0 < z.im) :
    theta (sumSq n) (-1 / z) = (-I * z / 2) ^ ((n : ℂ) / 2) * theta (sumSq n) (z / 4) := by
  rw [theta_S posDef_sumSq hz, gramDet_sumSq, thetaDual_sumSq]
  simp

/-- **Four squares:** $\Theta_{I_4}(-1/z) = -\tfrac{z^2}{4}\,\Theta_{I_4}(z/4)$ for $\operatorname{Im} z > 0$. Since
$\Theta_{I_4}(z) = \vartheta(2z)^4$, this is the fourth power of $\vartheta(-1/\tau) = (-i\tau)^{1/2}\vartheta(\tau)$ at $\tau = z/2$. -/
theorem theta_sumSq_four_S {z : ℂ} (hz : 0 < z.im) :
    theta (sumSq 4) (-1 / z) = -(z ^ 2 / 4) * theta (sumSq 4) (z / 4) := by
  rw [theta_sumSq_S hz]
  have : ((4 : ℕ) : ℂ) / 2 = ((2 : ℕ) : ℂ) := by norm_num
  rw [this, cpow_natCast]
  congr 1
  ring_nf; rw [I_sq]; ring

/-- $\Theta_{I_1}(z) = \vartheta(2z)$, with $\vartheta(\tau) = \sum_{m \in \mathbb{Z}} e^{\pi i m^2 \tau}$ Mathlib's `jacobiTheta`. -/
theorem theta_sumSq_one (z : ℂ) : theta (sumSq 1) z = jacobiTheta (2 * z) := by
  rw [theta, jacobiTheta, ← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  congr 1; funext m
  rw [eval_sumSq]
  simp only [Equiv.funUnique_symm_apply, Fin.sum_univ_one, uniqueElim_const, Int.cast_pow]
  ring_nf

/-- **Normalization check against Mathlib:** the case $n = 1$ of `theta_S` gives back Jacobi's inversion law
$\vartheta(-1/\tau) = (-i\tau)^{1/2}\vartheta(\tau)$ (Mathlib's `jacobiTheta_S_smul`, proved there independently),
including the branch of the square root. -/
theorem jacobiTheta_S_of_theta_S {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
  have hz : 0 < (2 * τ).im := by simp; linarith
  have h := theta_sumSq_S (n := 1) hz
  rw [theta_sumSq_one, theta_sumSq_one] at h
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  rw [show 2 * (-1 / (2 * τ)) = -1 / τ by field_simp, show 2 * (2 * τ / 4) = τ by ring,
    show -I * (2 * τ) / 2 = -I * τ by ring] at h
  rw [h]; norm_num

end

end QuadFormsKB.Siegel
