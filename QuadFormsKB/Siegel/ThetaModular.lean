/-
# Modularity of theta series

For a positive definite integral form $Q$ in $n$ variables with Hessian $H$ (so $Q(\vec{x}) = \tfrac12 \vec{x}^{\mathsf T}H\vec{x}$)
and $\Theta_Q(z) = \sum_{\vec{x} \in \mathbb{Z}^n} e(z\,Q(\vec{x}))$ (`theta`, `Siegel/Theta.lean`):

* `theta_add_one`: $\Theta_Q(z+1) = \Theta_Q(z)$.
* `thetaDual_eq_theta_of_isUnit`: if $\det H = \pm1$ then $\Theta_{Q^*} = \Theta_Q$.
* `theta_S_unimodular`: if moreover $Q$ is positive definite, $\det H = 1$ and $n = 2k$ with $4 \mid k$, then
  $\Theta_Q(-1/z) = z^k \Theta_Q(z)$.
* `thetaMF`: then $\Theta_Q$ is a modular form of weight $k$ for $\mathrm{SL}_2(\mathbb{Z})$
  (Mathlib's `ModularForm 𝒮ℒ k`), with $q$-expansion coefficients $r_Q(m)$ (`qExpansion_thetaMF_coeff`).

The E₈ application ($\Theta_{E_8} = E_4$, $r_{E_8}(m) = 240\,\sigma_3(m)$) is in `Siegel/E8.lean`.

Level $N$ (even $n = 2k$, $N Q^*$ integral, `IsThetaLevel`):

* `theta_fricke`: $\Theta_Q(-1/(Nz)) = (-iNz)^k (\det H)^{-1/2}\, \Theta_{Q^*}(Nz)$ (the Fricke involution).
* `theta_U`: $\Theta_Q(z/(Nz+1)) = (Nz+1)^k\, \Theta_Q(z)$.
* `thetaSIF`: $\Theta_Q$ is slash-invariant of weight $k$ for $\langle T, U_N\rangle \le \Gamma_1(N)$; example
  $\Theta_{I_4}$ for $\langle T, U_4 \rangle$ (`thetaSIF_sumSq_four`).

*Scope.* Full modularity on $\Gamma_0(N)$ with the character $\chi_Q$ for even $n$ (theta series over residue classes,
$n$-ary quadratic Gauss sums) is in `Siegel/ThetaGamma0.lean` (`theta_gamma0_chi`, `thetaMFGamma1`).

Sources: Serre, *A Course in Arithmetic*, Ch. VII §6.5–6.6 [unverified]. The construction of a level-one modular
form from $S$- and $T$-invariance follows Mathlib's `CuspForm.discriminant` (generators `slash_action_generators_SL2Z`).
-/
import QuadFormsKB.Siegel.Theta

open Complex Matrix Filter Topology ModularForm
open UpperHalfPlane hiding I
open QuadFormsKB.Analysis (quadAt)
open scoped MatrixGroups

namespace QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-- **Translation invariance:** $\Theta_Q(z + 1) = \Theta_Q(z)$ for every $z \in \mathbb{C}$, since $e(Q(\vec{x})) = 1$
for $Q(\vec{x}) \in \mathbb{Z}$ (termwise; no convergence needed). -/
@[kb "serre1973" "Ch. VII §6.5, Thm. 7 (proof) [unverified]"]
theorem theta_add_one (Q : QuadForm ℤ n) (z : ℂ) : theta Q (z + 1) = theta Q z := by
  unfold theta
  congr 1; funext x
  rw [show 2 * Real.pi * I * (z + 1) * (Q.eval x : ℂ) =
      2 * Real.pi * I * z * (Q.eval x : ℂ) + (Q.eval x : ℤ) * (2 * Real.pi * I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `gramMatrix Q` $= \tfrac12 H$ as a real matrix. -/
private lemma gramMatrix_eq (Q : QuadForm ℤ n) :
    gramMatrix Q = (1 / 2 : ℝ) • Q.hessian.map (Int.cast : ℤ → ℝ) := rfl

/-- **A unimodular lattice is its own dual:** if $\det H = \pm 1$ then $\Theta_{Q^*} = \Theta_Q$ on all of $\mathbb{C}$.
*Proof:* $\vec{x} \mapsto H\vec{x}$ is a bijection of $\mathbb{Z}^n$ (its inverse $H^{-1}$ is integral), and
$Q^*(H\vec{x}) = \tfrac12 (H\vec{x})^{\mathsf T} H^{-1} (H\vec{x}) = \tfrac12 \vec{x}^{\mathsf T} H \vec{x} = Q(\vec{x})$. -/
@[kb "serre1973" "Ch. VII §6.5 (unimodular lattices) [unverified]"]
theorem thetaDual_eq_theta_of_isUnit {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) (z : ℂ) :
    thetaDual Q z = theta Q z := by
  set H := Q.hessian with hH
  set Hr : Matrix (Fin n) (Fin n) ℝ := H.map (Int.cast : ℤ → ℝ) with hHr
  have hdetr : IsUnit Hr.det := by
    have h := RingHom.map_det (Int.castRingHom ℝ) H
    rw [RingHom.mapMatrix_apply] at h
    have : Hr.det = (H.det : ℝ) := by rw [hHr]; exact h.symm
    rw [this]
    rcases Int.isUnit_iff.mp hdet with h1 | h1 <;> simp [h1]
  -- the bijection x ↦ H x of ℤⁿ
  let e : (Fin n → ℤ) ≃ (Fin n → ℤ) :=
    { toFun := fun x => H *ᵥ x
      invFun := fun y => H⁻¹ *ᵥ y
      left_inv := fun x => by simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
      right_inv := fun y => by simp [mulVec_mulVec, mul_nonsing_inv _ hdet] }
  rw [thetaDual, thetaGram, theta, ← e.tsum_eq]
  congr 1; funext x
  congr 2
  have hcast : (fun i => ((H *ᵥ x) i : ℝ)) = Hr *ᵥ (fun i => (x i : ℝ)) := by
    ext i; simp [hHr, mulVec, dotProduct]
  have hinv : ((1 / 2 : ℝ) • Hr)⁻¹ = (2 : ℝ) • Hr⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, nonsing_inv_mul _ hdetr]; norm_num
  have key : quadAt (dualGram Q) (H *ᵥ x) = quadAt (gramMatrix Q) x := by
    rw [quadAt, quadAt, hcast, dualGram, gramMatrix_eq, ← hHr, hinv, smul_smul, smul_mulVec,
      mulVec_mulVec, nonsing_inv_mul _ hdetr, one_mulVec, smul_mulVec, dotProduct_smul,
      dotProduct_smul, dotProduct_comm]
    simp only [smul_eq_mul]; ring
  show (quadAt (dualGram Q) (H *ᵥ x) : ℂ) = _
  rw [key, quadAt_gramMatrix]; push_cast; rfl

/-- **Inversion law for an even unimodular form:** if $Q$ is positive definite with $\det H = 1$, $n = 2k$ and
$4 \mid k$ (i.e. $8 \mid n$), then for $\operatorname{Im} z > 0$
$$\Theta_Q(-1/z) = z^k\, \Theta_Q(z).$$
*Proof:* `theta_S'` gives $(-iz)^{k} (\det H)^{-1/2} \Theta_{Q^*}(z)$; here $\det H = 1$, $\Theta_{Q^*} = \Theta_Q$
(`thetaDual_eq_theta_of_isUnit`), and $(-i)^k = 1$ because $4 \mid k$. (The condition $8 \mid n$ is in fact
automatic for even unimodular positive definite lattices, but that is not proved here.) -/
@[kb "serre1973" "Ch. VII §6.5, Thm. 7 [unverified]"]
theorem theta_S_unimodular {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) {z : ℂ} (hz : 0 < z.im) :
    theta Q (-1 / z) = z ^ k * theta Q z := by
  rw [theta_S' hQ hz, hdet, thetaDual_eq_theta_of_isUnit (by rw [hdet]; exact isUnit_one)]
  obtain ⟨j, rfl⟩ := hk
  have hc : ((n : ℂ) / 2) = ((4 * j : ℕ) : ℂ) := by rw [hn]; push_cast; ring
  rw [hc, cpow_natCast, mul_pow, pow_mul (-I), show (-I) ^ 4 = (1 : ℂ) by
    rw [neg_pow, I_pow_four]; norm_num]
  simp

/-- $\Theta_Q$ restricted to the upper half plane $\mathbb{H}$ (Mathlib's `UpperHalfPlane`), as a function
$\mathbb{H} \to \mathbb{C}$ for the slash action. -/
def thetaH (Q : QuadForm ℤ n) : ℍ → ℂ := fun τ => theta Q τ

/-- $\Theta_Q \mid_k T = \Theta_Q$ for $T = \begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$ and every weight $k$. -/
theorem thetaH_T (Q : QuadForm ℤ n) (k : ℤ) : thetaH Q ∣[k] ModularGroup.T = thetaH Q := by
  ext τ
  rw [SL_slash_apply, ModularGroup.denom_apply, modular_T_smul]
  simp [thetaH, ModularGroup.coe_T, coe_vadd, add_comm (1 : ℂ), theta_add_one]

/-- $\Theta_Q \mid_k S = \Theta_Q$ for $S = \begin{pmatrix} 0 & -1 \\ 1 & 0\end{pmatrix}$, under the hypotheses of
`theta_S_unimodular`: $(\Theta_Q \mid_k S)(\tau) = \Theta_Q(-1/\tau)\, \tau^{-k}$. -/
theorem thetaH_S {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) : thetaH Q ∣[(k : ℤ)] ModularGroup.S = thetaH Q := by
  ext τ
  have h := theta_S_unimodular hQ hdet hn hk τ.im_pos
  suffices theta Q (-(τ : ℂ)⁻¹) * ((τ : ℂ) ^ k)⁻¹ = theta Q τ by
    rw [SL_slash_apply, ModularGroup.denom_S, UpperHalfPlane.modular_S_smul]
    simpa [thetaH] using this
  rw [show -(τ : ℂ)⁻¹ = -1 / (τ : ℂ) by rw [neg_div, one_div], h]
  field_simp [τ.ne_zero]

/-- $|e(z\,Q(\vec{x}))| = e^{-2\pi \operatorname{Im}(z)\, Q(\vec{x})}$. -/
private lemma norm_theta_term (Q : QuadForm ℤ n) (z : ℂ) (x : Fin n → ℤ) :
    ‖cexp (2 * Real.pi * I * z * (Q.eval x : ℂ))‖ = Real.exp (-(2 * Real.pi * z.im * Q.eval x)) := by
  rw [Complex.norm_exp]; congr 1
  simp [mul_re, mul_im]

/-- **Uniform bound at $i\infty$:** for $\operatorname{Im} z \ge 1$, $|\Theta_Q(z)| \le \sum_{\vec{x}} e^{-2\pi Q(\vec{x})}$
(the absolutely convergent series at $z = i$). -/
theorem norm_theta_le {Q : IntQF n} (hQ : Q.PosDef) {z : ℂ} (hz : 1 ≤ z.im) :
    ‖theta Q z‖ ≤ ∑' x : Fin n → ℤ, ‖cexp (2 * Real.pi * I * I * (Q.eval x : ℂ))‖ := by
  have hsI := (summable_theta_term hQ (z := I) (by simp)).norm
  refine (norm_tsum_le_tsum_norm (summable_theta_term hQ (by linarith)).norm).trans ?_
  refine Summable.tsum_le_tsum (fun x => ?_) (summable_theta_term hQ (by linarith)).norm hsI
  rw [norm_theta_term, norm_theta_term, Real.exp_le_exp, neg_le_neg_iff]
  have := eval_nonneg hQ x
  simp only [Complex.I_im]
  have hq : (0 : ℝ) ≤ Q.eval x := by exact_mod_cast this
  have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hz)) hq
  nlinarith

/-- $\Theta_Q$ is bounded as $\operatorname{Im} \tau \to \infty$ (for $Q$ positive definite). -/
theorem isBoundedAtImInfty_thetaH {Q : IntQF n} (hQ : Q.PosDef) :
    IsBoundedAtImInfty (thetaH Q) := by
  rw [isBoundedAtImInfty_iff]
  exact ⟨_, 1, fun z hz => norm_theta_le hQ hz⟩

/-- **The theta series of an even unimodular lattice is a level-one modular form.** For $Q$ positive definite
with $\det H = 1$, $n = 2k$ and $4 \mid k$, $\Theta_Q \in M_k(\mathrm{SL}_2(\mathbb{Z}))$ (Mathlib's
`ModularForm 𝒮ℒ k`): invariant under $S$ and $T$ (`thetaH_S`, `thetaH_T`, which generate $\mathrm{SL}_2(\mathbb{Z})$),
holomorphic on $\mathbb{H}$ (`differentiableOn_theta`) and bounded at the cusp (`isBoundedAtImInfty_thetaH`). -/
@[kb "serre1973" "Ch. VII §6.5, Thm. 7 [unverified]"]
def thetaMF {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) : ModularForm 𝒮ℒ k where
  toFun := thetaH Q
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z (thetaH_S hQ hdet hn hk) (thetaH_T Q k) A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (differentiableOn_theta hQ).congr fun z hz => ?_
    simp [thetaH, ofComplex_apply_of_im_pos hz]
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z (thetaH_S hQ hdet hn hk) (thetaH_T Q k)]
    exact isBoundedAtImInfty_thetaH hQ

/-- `thetaMF` is $\Theta_Q$ on $\mathbb{H}$. -/
@[simp] theorem thetaMF_apply {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) (τ : ℍ) : thetaMF hQ hdet hn hk τ = theta Q τ := rfl

/-- The $q$-expansion of `thetaMF` in Mathlib's normalization: $\Theta_Q(\tau) = \sum_{m \ge 0} r_Q(m)\, q^m$,
$q = $ `Function.Periodic.qParam 1 τ` $= e^{2\pi i \tau}$ (from `hasSum_theta`). -/
theorem thetaMF_hasSum {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) (τ : ℍ) :
    HasSum (fun m : ℕ => (repNum Q m : ℂ) • Function.Periodic.qParam 1 τ ^ m) (thetaMF hQ hdet hn hk τ) := by
  rw [thetaMF_apply]
  convert hasSum_theta hQ τ.im_pos using 2 with m
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- **The $q$-expansion coefficients of $\Theta_Q$ are the representation numbers:** the $m$-th coefficient of
Mathlib's `qExpansion 1` of `thetaMF` is $r_Q(m)$ = `repNum Q m` (uniqueness of $q$-expansions). -/
@[kb "serre1973" "Ch. VII §6.5 [unverified]"]
theorem qExpansion_thetaMF_coeff {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) (hk : 4 ∣ k) (m : ℕ) :
    (qExpansion 1 (thetaMF hQ hdet hn hk)).coeff m = repNum Q m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (thetaMF_hasSum hQ hdet hn hk) m).symm

/-! ### Level $N$: translations, the Fricke relation, and $U_N = \begin{pmatrix}1&0\\N&1\end{pmatrix}$ -/

/-- **$N$ is a level for $\Theta_Q$:** $N\,Q^*(\vec{y}) \in \mathbb{Z}$ for every $\vec{y} \in \mathbb{Z}^n$, where
$Q^*(\vec{y}) = \tfrac12\vec{y}^{\mathsf T}H^{-1}\vec{y}$ (`dualGram`). Equivalently, $N H^{-1}$ is an even integral matrix
(integer entries, even diagonal), the usual definition of the level when $N$ is minimal. Example:
$x_0^2 + \dots + x_{n-1}^2$ has level $4$ (`isThetaLevel_sumSq`). -/
@[kb "serre1973" "Ch. VII §6 (level of a lattice) [unverified]"]
def IsThetaLevel (Q : QuadForm ℤ n) (N : ℕ) : Prop :=
  ∀ y : Fin n → ℤ, ∃ m : ℤ, (N : ℝ) * quadAt (dualGram Q) y = m

/-- **$\Theta_{Q^*}$ has period $N$** when $N$ is a level: $\Theta_{Q^*}(w + jN) = \Theta_{Q^*}(w)$ for all $w \in \mathbb{C}$,
$j \in \mathbb{Z}$. -/
theorem thetaDual_add_level {Q : QuadForm ℤ n} {N : ℕ} (hN : IsThetaLevel Q N) (w : ℂ) (j : ℤ) :
    thetaDual Q (w + j * N) = thetaDual Q w := by
  unfold thetaDual thetaGram
  congr 1; funext y
  obtain ⟨m, hm⟩ := hN y
  have hm' : ((N : ℂ) * (quadAt (dualGram Q) y : ℂ)) = (m : ℂ) := by exact_mod_cast hm
  rw [show 2 * Real.pi * I * (w + j * N) * (quadAt (dualGram Q) y : ℂ) =
      2 * Real.pi * I * w * (quadAt (dualGram Q) y : ℂ) + (j * m : ℤ) * (2 * Real.pi * I) by
        push_cast; rw [← hm']; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The Fricke relation** (even $n = 2k$, $Q$ positive definite, $N \ge 1$, $\operatorname{Im} z > 0$):
$$\Theta_Q\Big(\frac{-1}{Nz}\Big) = (-iNz)^k\, (\det H)^{-1/2}\, \Theta_{Q^*}(Nz).$$
When $N$ is a level, $\Theta_{Q^*}(Nz) = \sum_{\vec{y}} e(z\, N Q^*(\vec{y}))$ is the theta series of the integral form
$NQ^*$ (the "dual form of level $N$"), so this is the action of the Fricke involution $W_N$. This is `theta_S'` at $Nz$. -/
@[kb "serre1973" "Ch. VII §6 [unverified]"]
theorem theta_fricke {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N)
    {z : ℂ} (hz : 0 < z.im) :
    theta Q (-1 / (N * z)) =
      (-I * N * z) ^ k * ((Real.sqrt (Q.hessian.det : ℝ))⁻¹ : ℝ) * thetaDual Q (N * z) := by
  have hNz : 0 < ((N : ℂ) * z).im := by simp; exact mul_pos (by exact_mod_cast hN0) hz
  rw [theta_S' hQ hNz, show ((n : ℂ) / 2) = ((k : ℕ) : ℂ) by rw [hn]; push_cast; ring, cpow_natCast,
    mul_assoc (-I)]

/-- **Transformation under $U_N = \begin{pmatrix}1&0\\N&1\end{pmatrix}$** (even $n = 2k$, $Q$ positive definite, $N \ge 1$ a
level, `IsThetaLevel`): for $\operatorname{Im} z > 0$,
$$\Theta_Q\Big(\frac{z}{Nz + 1}\Big) = (Nz + 1)^k\, \Theta_Q(z).$$
*Proof:* with $\tau = -1/(Nz)$ one has $z/(Nz+1) = -1/(N(\tau - 1))$; apply the Fricke relation at $\tau$ and
$\tau - 1$, and use $\Theta_{Q^*}(N\tau - N) = \Theta_{Q^*}(N\tau)$ (`thetaDual_add_level`); the ratio of the factors is
$((\tau - 1)/\tau)^k = (Nz + 1)^k$. No character appears: $U_N$ has $d = 1$. -/
@[kb "serre1973" "Ch. VII §6 [unverified]"]
theorem theta_U {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N)
    (hN : IsThetaLevel Q N) {z : ℂ} (hz : 0 < z.im) :
    theta Q (z / (N * z + 1)) = (N * z + 1) ^ k * theta Q z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  set τ : ℂ := -1 / (N * z) with hτ
  have hτim : 0 < τ.im := by
    rw [hτ, neg_div, neg_im, div_eq_mul_inv, one_mul, inv_im, neg_div, neg_neg]
    apply div_pos
    · simp; exact mul_pos (by exact_mod_cast hN0) hz
    · exact Complex.normSq_pos.mpr (mul_ne_zero hN0' hz0)
  have hτ0 : τ ≠ 0 := by rintro h; rw [h] at hτim; simp at hτim
  have hτ1im : 0 < (τ - 1).im := by simpa using hτim
  have hz' : z = -1 / (N * τ) := by rw [hτ]; field_simp
  have hτ10 : τ - 1 ≠ 0 := by rintro h; rw [h] at hτ1im; simp at hτ1im
  have hNz1 : (N : ℂ) * z + 1 = (τ - 1) / τ := by
    rw [hz']; field_simp; ring
  have hU : z / (N * z + 1) = -1 / (N * (τ - 1)) := by
    rw [hNz1, hz']; field_simp
  have hper : thetaDual Q (N * (τ - 1)) = thetaDual Q (N * τ) := by
    rw [show (N : ℂ) * (τ - 1) = N * τ + ((-1 : ℤ) : ℂ) * N by push_cast; ring, thetaDual_add_level hN]
  have hF : ∀ w : ℂ, 0 < w.im → theta Q (-1 / (N * w)) =
      (-I * N * w) ^ k * ((Real.sqrt (Q.hessian.det : ℝ))⁻¹ : ℝ) * thetaDual Q (N * w) :=
    fun w hw => theta_fricke hQ hn hN0 hw
  rw [hU, hF _ hτ1im, hper]
  conv_rhs => rw [hNz1, hz', hF _ hτim]
  rw [show -I * N * (τ - 1) = ((τ - 1) / τ) * (-I * N * τ) by field_simp, mul_pow]
  ring

/-- $U_N = \begin{pmatrix}1&0\\N&1\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$. -/
def unipotentLower (N : ℤ) : SL(2, ℤ) := ⟨!![1, 0; N, 1], by simp [Matrix.det_fin_two]⟩

/-- $\Theta_Q \mid_k U_N = \Theta_Q$ (slash-action form of `theta_U`). -/
theorem thetaH_unipotentLower {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) :
    thetaH Q ∣[(k : ℤ)] unipotentLower N = thetaH Q := by
  ext τ
  rw [SL_slash_apply, ModularGroup.denom_apply]
  have hτ := theta_U hQ hn hN0 hN τ.im_pos
  have hd : (N : ℂ) * τ + 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
    rcases this with h1 | h1
    · exact hN0.ne' (by exact_mod_cast h1)
    · exact τ.im_pos.ne' h1
  have hsmul : ((unipotentLower N • τ : ℍ) : ℂ) = τ / (N * τ + 1) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [unipotentLower]
  have hden : (((unipotentLower N) 1 0 : ℤ) : ℂ) * τ + (((unipotentLower N) 1 1 : ℤ) : ℂ) =
      N * τ + 1 := by simp [unipotentLower]
  rw [hden, thetaH, thetaH, hsmul, hτ, _root_.zpow_neg, zpow_natCast]
  field_simp

/-- **The theta group of level $N$** used here: the subgroup $\langle T, U_N\rangle$ of $\mathrm{SL}_2(\mathbb{Z})$ generated by
$T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ and $U_N = \begin{pmatrix}1&0\\N&1\end{pmatrix}$. It lies in $\Gamma_1(N)$
(`thetaGroup_le_Gamma1`); it is known to equal $\Gamma_1(N)$ for $N \le 4$ (not proved here) and has infinite index
for $N \ge 5$, so it is **not** $\Gamma_0(N)$ in general. -/
def thetaGroup (N : ℤ) : Subgroup SL(2, ℤ) := Subgroup.closure {ModularGroup.T, unipotentLower N}

/-- **$\Theta_Q$ is invariant of weight $k$ under $\langle T, U_N\rangle$** (even $n = 2k$, $Q$ positive definite, $N \ge 1$ a
level): a Mathlib `SlashInvariantForm` for that group. Holomorphy is `differentiableOn_theta`; boundedness at the
cusps of this group and invariance under all of $\Gamma_0(N)$ (with the character $\chi_D$) are not proved here. -/
@[kb "serre1973" "Ch. VII §6 [unverified]"]
def thetaSIF {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) :
    SlashInvariantForm ((thetaGroup N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k where
  toFun := thetaH Q
  slash_action_eq' := by
    rw [SlashInvariantForm.slash_action_generators (s := Matrix.SpecialLinearGroup.mapGL ℝ ''
      {ModularGroup.T, unipotentLower N}) (by rw [thetaGroup, MonoidHom.map_closure])]
    rintro _ ⟨γ, hγ, rfl⟩
    rcases hγ with rfl | rfl
    · exact thetaH_T Q k
    · exact thetaH_unipotentLower hQ hn hN0 hN

/-- $\langle T, U_N\rangle \le \Gamma_1(N)$. -/
theorem thetaGroup_le_Gamma1 (N : ℕ) : thetaGroup N ≤ CongruenceSubgroup.Gamma1 N := by
  rw [thetaGroup, Subgroup.closure_le]
  rintro γ (rfl | rfl) <;> rw [SetLike.mem_coe, CongruenceSubgroup.Gamma1_mem]
  · simp [ModularGroup.T]
  · simp [unipotentLower]

/-- **$4$ is a level of $x_0^2 + \dots + x_{n-1}^2$:** $Q^*(\vec{y}) = \tfrac14 \sum y_i^2$, so $4Q^*(\vec{y}) \in \mathbb{Z}$.
With `thetaSIF` ($n = 4$, $k = 2$) this makes $\Theta_{I_4}$ invariant of weight 2 under $\langle T, U_4\rangle$. -/
theorem isThetaLevel_sumSq : IsThetaLevel (sumSq n) 4 := by
  intro y
  refine ⟨∑ i, y i ^ 2, ?_⟩
  rw [quadAt, dualGram, gramMatrix_sumSq, inv_one]
  simp only [dotProduct, Finset.mul_sum, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Four squares:** $\Theta_{I_4}$ is invariant of weight 2 under $\langle T, U_4\rangle$ ($= \Gamma_1(4)$, not proved here). -/
def thetaSIF_sumSq_four : SlashInvariantForm ((thetaGroup 4).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2 :=
  thetaSIF posDef_sumSq (n := 4) (k := 2) rfl (by norm_num) isThetaLevel_sumSq

end

end QuadFormsKB.Siegel
