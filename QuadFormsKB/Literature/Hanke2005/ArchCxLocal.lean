/-
# Hanke 2005, §4.3: the Gram map $(T, \sigma)\mapsto(1 - i\sigma)T(1 - i\sigma)$ near the fibre

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

In the coordinates $X = (1 - iu)Y(1 - i\sigma)$ of `ArchCxParam.lean` the Gram matrix is ${}^tXX = (1 - i\sigma)T(1 - i\sigma)$.
Here $(T, \sigma)$ (two real symmetric matrices) are packed into one complex coefficient vector $c$ (`cT c`, `cS c`: the
symmetric matrices with upper coordinates $\operatorname{Re}c$, $\operatorname{Im}c$), and
$$h(c) = \text{the coefficient coordinates of } (1 - i\sigma)T(1 - i\sigma)\qquad(\texttt{hmap}).$$
The fibre of $SO_n(\mathbb C)$ is $c_0$ ($T = 1$, $\sigma = 0$), with $h(c_0) = c_Q$ the coefficient vector of the sum of squares.

**Proves**
* `contDiff_hmap`, `hasFDerivAt_hmap_c0` (the derivative at $c_0$ is $c\mapsto w\cdot(\operatorname{Re}c - 2i\operatorname{Im}c)$),
  `abs_det_hmapD`: its real Jacobian is $2^{n(n-1)}\cdot2^{n(n+1)/2}$;
* `exists_chart`: an open $W\ni c_0$ on which $h$ is injective with open image and a continuous inverse, and on which
  $T$ is positive definite (with positive Schur pivots), $\operatorname{Re}\det(1 - i\sigma) > 0$ and $\det Dh\ne0$;
* `tendsto_avg_hmap` (**the fibre limit**): for $k$ continuous on $W$,
  $$\frac{1}{\mathrm{Leb}(\bar B_\varepsilon(c_Q))}\int_W k(c)\,[h(c)\in\bar B_\varepsilon(c_Q)]\,dc\ \longrightarrow\ \frac{k(c_0)}{|\det Dh(c_0)|}.$$
-/
import QuadFormsKB.Literature.Hanke2005.ArchCxParam
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarDet

open MeasureTheory Matrix Complex Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

/-! ### `cplx` and `symU` -/

theorem cplx_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : cplx A i j = (A i j : ℂ) := rfl

theorem cplx_add (A B : Matrix (Fin n) (Fin n) ℝ) : cplx (A + B) = cplx A + cplx B := by
  ext i j; simp [cplx]

theorem cplx_sub (A B : Matrix (Fin n) (Fin n) ℝ) : cplx (A - B) = cplx A - cplx B := by
  ext i j; simp [cplx]

theorem cplx_smul (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : cplx (r • A) = (r : ℂ) • cplx A := by
  ext i j; simp [cplx]

theorem cplx_one : cplx (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [cplx, one_apply, h]

theorem cplx_zero : cplx (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  ext i j; simp [cplx]

theorem cplx_mul (A B : Matrix (Fin n) (Fin n) ℝ) : cplx (A * B) = cplx A * cplx B := by
  ext i j; simp [cplx, Matrix.mul_apply]

theorem cplx_transpose (A : Matrix (Fin n) (Fin n) ℝ) : cplx Aᵀ = (cplx A)ᵀ := by
  ext i j; simp [cplx]

theorem cplx_neg (A : Matrix (Fin n) (Fin n) ℝ) : cplx (-A) = -cplx A := by
  ext i j; simp [cplx]

theorem det_cplx (A : Matrix (Fin n) (Fin n) ℝ) : (cplx A).det = (A.det : ℂ) := by
  exact (Complex.ofRealHom.map_det A).symm

theorem symU_add' (s t : UIdx n → ℝ) : symU (s + t) = symU s + symU t := by
  ext i j; simp only [symU, of_apply, Pi.add_apply, Matrix.add_apply]; split_ifs <;> rfl

theorem symU_smul' (r : ℝ) (t : UIdx n → ℝ) : symU (r • t) = r • symU t := by
  ext i j; simp only [symU, of_apply, Pi.smul_apply, Matrix.smul_apply]; split_ifs <;> rfl

theorem symU_transpose' (t : UIdx n → ℝ) : (symU t)ᵀ = symU t := by
  ext i j
  simp only [transpose_apply, symU, of_apply]
  by_cases h1 : j ≤ i <;> by_cases h2 : i ≤ j
  · have : i = j := le_antisymm h2 h1
    subst this; rfl
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_total i j) (by tauto)

theorem symU_apply_le (t : UIdx n → ℝ) {i j : Fin n} (h : i ≤ j) : symU t i j = t ⟨(i, j), h⟩ := by
  simp [symU, h]

/-! ### The coordinates $(T, \sigma)$ of a complex coefficient vector -/

/-- $T$: the symmetric matrix with upper coordinates $\operatorname{Re}c$. -/
def cT (c : UIdx n → ℂ) : Matrix (Fin n) (Fin n) ℝ := symU fun q => (c q).re

/-- $\sigma$: the symmetric matrix with upper coordinates $\operatorname{Im}c$. -/
def cS (c : UIdx n → ℂ) : Matrix (Fin n) (Fin n) ℝ := symU fun q => (c q).im

/-- **The Gram map** $h(c)$: the coefficient coordinates of $(1 - i\sigma)T(1 - i\sigma)$, $T = $ `cT c`,
$\sigma = $ `cS c`. -/
def hmap (c : UIdx n → ℂ) : UIdx n → ℂ :=
  wtU ((1 - I • cplx (cS c)) * cplx (cT c) * (1 - I • cplx (cS c)))

/-- The point $c_0$: $T = 1$, $\sigma = 0$. -/
def c0 : UIdx n → ℂ := fun q => if q.1.1 = q.1.2 then 1 else 0

theorem cT_add (c d : UIdx n → ℂ) : cT (c + d) = cT c + cT d := by
  rw [cT, cT, cT, ← symU_add']; rfl

theorem cS_add (c d : UIdx n → ℂ) : cS (c + d) = cS c + cS d := by
  rw [cS, cS, cS, ← symU_add']; rfl

theorem cT_smul (r : ℝ) (c : UIdx n → ℂ) : cT (r • c) = r • cT c := by
  rw [cT, cT, ← symU_smul']; congr 1; funext q; simp

theorem cS_smul (r : ℝ) (c : UIdx n → ℂ) : cS (r • c) = r • cS c := by
  rw [cS, cS, ← symU_smul']; congr 1; funext q; simp

theorem cT_c0 : cT (c0 : UIdx n → ℂ) = 1 := by
  ext i j
  simp only [cT, symU, c0, of_apply, one_apply]
  by_cases h : i = j
  · subst h; simp
  · by_cases h1 : i ≤ j
    · simp [h1, h]
    · simp [h1, h, Ne.symm h]

theorem cS_c0 : cS (c0 : UIdx n → ℂ) = 0 := by
  ext i j
  simp only [cS, symU, c0, of_apply, Matrix.zero_apply]
  split_ifs <;> simp

theorem cT_transpose (c : UIdx n → ℂ) : (cT c)ᵀ = cT c := symU_transpose' _

theorem cS_transpose (c : UIdx n → ℂ) : (cS c)ᵀ = cS c := symU_transpose' _

theorem hmap_c0 : hmap (c0 : UIdx n → ℂ) = coeffUC (sumSqC n) := by
  rw [hmap, cT_c0, cS_c0, cplx_one, cplx_zero, smul_zero, sub_zero, Matrix.one_mul, Matrix.one_mul,
    coeffUC_eq, gramC_sumSqC]

/-! ### Smoothness of $h$ -/

section CDR
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Entrywise smoothness (over $\mathbb R$) of a complex-matrix-valued map. -/
def CDR (F : E → Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, ContDiff ℝ ⊤ fun y => F y i j

theorem CDR.mul {F G : E → Matrix (Fin n) (Fin n) ℂ} (hF : CDR F) (hG : CDR G) : CDR fun y => F y * G y :=
  fun i j => by
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun k _ => (hF i k).mul (hG k j)

theorem CDR.sub {F G : E → Matrix (Fin n) (Fin n) ℂ} (hF : CDR F) (hG : CDR G) : CDR fun y => F y - G y :=
  fun i j => by simp only [Matrix.sub_apply]; exact (hF i j).sub (hG i j)

theorem CDR.const (M : Matrix (Fin n) (Fin n) ℂ) : CDR fun _ : E => M := fun _ _ => contDiff_const

theorem CDR.smul_I {F : E → Matrix (Fin n) (Fin n) ℂ} (hF : CDR F) : CDR fun y => I • F y :=
  fun i j => by simp only [Matrix.smul_apply, smul_eq_mul]; exact contDiff_const.mul (hF i j)

end CDR

theorem contDiff_coord_re (q : UIdx n) : ContDiff ℝ ⊤ fun c : UIdx n → ℂ => (((c q).re : ℝ) : ℂ) :=
  (ofRealCLM.comp (reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : UIdx n => ℂ) q))).contDiff

theorem contDiff_coord_im (q : UIdx n) : ContDiff ℝ ⊤ fun c : UIdx n → ℂ => (((c q).im : ℝ) : ℂ) :=
  (ofRealCLM.comp (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : UIdx n => ℂ) q))).contDiff

theorem cdr_cT : CDR fun c : UIdx n → ℂ => cplx (cT c) := fun i j => by
  simp only [cplx_apply, cT, symU, of_apply]
  split_ifs
  · exact contDiff_coord_re _
  · exact contDiff_coord_re _

theorem cdr_cS : CDR fun c : UIdx n → ℂ => cplx (cS c) := fun i j => by
  simp only [cplx_apply, cS, symU, of_apply]
  split_ifs
  · exact contDiff_coord_im _
  · exact contDiff_coord_im _

theorem contDiff_hmap : ContDiff ℝ ⊤ (hmap : (UIdx n → ℂ) → UIdx n → ℂ) := by
  have hA : CDR fun c : UIdx n → ℂ => 1 - I • cplx (cS c) := (CDR.const 1).sub cdr_cS.smul_I
  have h := (hA.mul cdr_cT).mul hA
  refine contDiff_pi.2 fun p => ?_
  simp only [hmap, wtU]
  exact contDiff_const.mul (h p.1.1 p.1.2)

theorem continuous_hmap : Continuous (hmap : (UIdx n → ℂ) → UIdx n → ℂ) := contDiff_hmap.continuous

/-! ### The derivative at $c_0$ -/

/-- The coordinate map $z\mapsto w\,(\operatorname{Re}z - 2i\operatorname{Im}z)$ on $\mathbb C$ (real-linear). -/
def ellW (w : ℝ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := (w : ℂ) * ((z.re : ℂ) - 2 * I * (z.im : ℂ))
  map_add' z z' := by simp only [add_re, add_im, ofReal_add]; ring
  map_smul' r z := by
    simp only [RingHom.id_apply, real_smul, re_ofReal_mul, im_ofReal_mul, ofReal_mul]; ring

/-- **The derivative of $h$ at $c_0$**: $c\mapsto\big(w_q(\operatorname{Re}c_q - 2i\operatorname{Im}c_q)\big)_q$. -/
def hmapD : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ) := LinearMap.pi fun q => (ellW (wt q)).comp (LinearMap.proj q)

theorem hmapD_apply (d : UIdx n → ℂ) (q : UIdx n) :
    hmapD d q = (wt q : ℂ) * (((d q).re : ℂ) - 2 * I * ((d q).im : ℂ)) := rfl

theorem cplx_cT_c0_add (r : ℝ) (d : UIdx n → ℂ) :
    cplx (cT (c0 + r • d)) = 1 + (r : ℂ) • cplx (cT d) := by
  rw [cT_add, cT_smul, cT_c0, cplx_add, cplx_smul, cplx_one]

theorem cplx_cS_c0_add (r : ℝ) (d : UIdx n → ℂ) :
    I • cplx (cS (c0 + r • d)) = (r : ℂ) • (I • cplx (cS d)) := by
  rw [cS_add, cS_smul, cS_c0, zero_add, cplx_smul, smul_comm]

theorem hmap_line (r : ℝ) (d : UIdx n → ℂ) :
    hmap (c0 + r • d) = coeffUC (sumSqC n) + r • wtU (cplx (cT d) - (2 : ℂ) • (I • cplx (cS d))) +
      r ^ 2 • wtU ((I • cplx (cS d)) * (I • cplx (cS d)) - (I • cplx (cS d)) * cplx (cT d) -
        cplx (cT d) * (I • cplx (cS d))) +
      r ^ 3 • wtU ((I • cplx (cS d)) * cplx (cT d) * (I • cplx (cS d))) := by
  rw [hmap, cplx_cT_c0_add, cplx_cS_c0_add, coeffUC_eq, gramC_sumSqC]
  set a := I • cplx (cS d)
  set b := cplx (cT d)
  have e : (1 - (r : ℂ) • a) * (1 + (r : ℂ) • b) * (1 - (r : ℂ) • a) =
      1 + (r : ℂ) • (b - (2 : ℂ) • a) + (r : ℂ) ^ 2 • (a * a - a * b - b * a) + (r : ℂ) ^ 3 • (a * b * a) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [e, wtU_add, wtU_add, wtU_add, wtU_smul, wtU_smul, wtU_smul]
  simp only [← ofReal_pow, ← Complex.coe_smul]

theorem hasDerivAt_hmap_line (d : UIdx n → ℂ) :
    HasDerivAt (fun r : ℝ => hmap (c0 + r • d)) (hmapD d) 0 := by
  simp_rw [hmap_line]
  set L := wtU (cplx (cT d) - (2 : ℂ) • (I • cplx (cS d)))
  set A := wtU ((I • cplx (cS d)) * (I • cplx (cS d)) - (I • cplx (cS d)) * cplx (cT d) -
        cplx (cT d) * (I • cplx (cS d)))
  set B := wtU ((I • cplx (cS d)) * cplx (cT d) * (I • cplx (cS d)))
  have h1 : HasDerivAt (fun r : ℝ => r • L) ((1 : ℝ) • L) 0 := (hasDerivAt_id 0).smul_const _
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2 • A) (((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) • A) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).smul_const _
  have h3 : HasDerivAt (fun r : ℝ => r ^ 3 • B) (((3 : ℕ) * (0 : ℝ) ^ (3 - 1)) • B) 0 :=
    (hasDerivAt_pow 3 (0 : ℝ)).smul_const _
  have := ((h1.const_add (coeffUC (sumSqC n))).add h2).add h3
  convert this using 1
  funext q
  have h0 : ((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) = 0 := by norm_num
  have h0' : ((3 : ℕ) * (0 : ℝ) ^ (3 - 1)) = 0 := by norm_num
  rw [h0, h0', zero_smul, zero_smul, add_zero, add_zero, one_smul]
  simp only [L, wtU, hmapD_apply, Matrix.sub_apply, Matrix.smul_apply, cplx_apply, cT, cS,
    symU_apply_le _ q.2, smul_eq_mul]
  ring

theorem fderiv_hmap_c0 :
    ((fderiv ℝ hmap (c0 : UIdx n → ℂ) : (UIdx n → ℂ) →L[ℝ] (UIdx n → ℂ)) : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) =
      hmapD := by
  refine LinearMap.ext fun d => ?_
  have hd : HasFDerivAt hmap (fderiv ℝ hmap (c0 : UIdx n → ℂ)) c0 :=
    (contDiff_hmap.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => c0 + r • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (c0 : UIdx n → ℂ)
  have hd' : HasFDerivAt hmap (fderiv ℝ hmap (c0 : UIdx n → ℂ)) (c0 + (0 : ℝ) • d) := by
    rwa [zero_smul, add_zero]
  have h1 : HasDerivAt (fun r : ℝ => hmap (c0 + r • d)) (fderiv ℝ hmap (c0 : UIdx n → ℂ) d) 0 := by
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    simpa [Function.comp_def] using this
  exact h1.unique (hasDerivAt_hmap_line d)

theorem hmapD_injective : Function.Injective (hmapD : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro d hd
  funext q
  have h := congrFun hd q
  rw [hmapD_apply, Pi.zero_apply] at h
  have hw : (wt q : ℂ) ≠ 0 := wt_ne q
  have h' := (mul_eq_zero.mp h).resolve_left hw
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp at hre him
  exact Complex.ext hre him

theorem det_ellW (w : ℝ) : LinearMap.det (ellW w) = -2 * w ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  simp [ellW]
  ring

theorem det_hmapD : LinearMap.det (hmapD : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) =
    ∏ q : UIdx n, (-2 * wt q ^ 2) := by
  rw [hmapD, LinearMap.det_pi]
  exact Finset.prod_congr rfl fun q _ => det_ellW _

/-- **The Jacobian of $h$ at $c_0$**: $|\det Dh(c_0)| = 2^{n(n-1)}\cdot2^{n(n+1)/2}$ (each coordinate $c_q$ contributes
$|{-2}w_q^2|$, and $\prod_q w_q = 2^{n(n-1)/2}$). -/
theorem abs_det_hmapD : |LinearMap.det (hmapD : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ))| =
    (2 : ℝ) ^ (n * (n - 1)) * 2 ^ (n * (n + 1) / 2) := by
  rw [det_hmapD, Finset.abs_prod]
  have h : ∀ q : UIdx n, |(-2 * wt q ^ 2)| = 2 * wt q ^ 2 := fun q => by
    rw [abs_mul, abs_neg, abs_two, abs_pow, abs_of_pos (wt_pos q)]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_pow, prod_wt, Finset.prod_const, Finset.card_univ,
    QuadFormsKB.Tamagawa.Measure.Weil.card_UIdx, ← pow_mul, mul_comm]
  congr 1
  rw [mul_comm (n * (n - 1) / 2) 2]
  congr 1
  rcases Nat.even_mul_pred_self n with ⟨k, hk⟩
  omega

/-! ### The chart near $c_0$ (inverse function theorem) -/

theorem continuous_cT : Continuous (cT : (UIdx n → ℂ) → Matrix (Fin n) (Fin n) ℝ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [cT, symU, of_apply]
  split_ifs
  · exact Complex.continuous_re.comp (continuous_apply _)
  · exact Complex.continuous_re.comp (continuous_apply _)

theorem continuous_cS : Continuous (cS : (UIdx n → ℂ) → Matrix (Fin n) (Fin n) ℝ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [cS, symU, of_apply]
  split_ifs
  · exact Complex.continuous_im.comp (continuous_apply _)
  · exact Complex.continuous_im.comp (continuous_apply _)

theorem continuous_cplx : Continuous (cplx : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℂ) :=
  continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))

theorem dotProduct_self_pos {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm ?_)
  exact fun h => hx (dotProduct_self_eq_zero.mp h)

/-- Near $c_0$, $T$ is positive definite. -/
theorem eventually_PDU : ∀ᶠ c in 𝓝 (c0 : UIdx n → ℂ), PDU (fun q => (c q).re) := by
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hcont : Continuous fun p : (UIdx n → ℂ) × (Fin n → ℝ) => p.2 ⬝ᵥ (cT p.1 *ᵥ p.2) :=
    continuous_snd.dotProduct ((continuous_cT.comp continuous_fst).matrix_mulVec continuous_snd)
  have h0 : ∀ x ∈ Metric.sphere (0 : Fin n → ℝ) 1,
      ∀ᶠ p : (UIdx n → ℂ) × (Fin n → ℝ) in 𝓝 ((c0 : UIdx n → ℂ), x), 0 < p.2 ⬝ᵥ (cT p.1 *ᵥ p.2) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl; simp at hx
    refine hcont.continuousAt.eventually (lt_mem_nhds ?_)
    simp only [cT_c0, one_mulVec]
    exact dotProduct_self_pos hx0
  have h1 := hS.eventually_forall_of_forall_eventually (P := fun c x => 0 < x ⬝ᵥ (cT c *ᵥ x)) h0
  filter_upwards [h1] with c hc x hx
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have := hc _ hy
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
  have h2 : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ := by positivity
  have h3 : x ⬝ᵥ (cT c *ᵥ x) = x ⬝ᵥ (symU (fun q => (c q).re) *ᵥ x) := rfl
  rw [← h3]
  nlinarith [mul_pos h2 (show (0 : ℝ) < 1 by norm_num)]

theorem continuous_det_one_sub : Continuous fun c : UIdx n → ℂ => (1 - I • cplx (cS c)).det.re := by
  have h : Continuous fun c : UIdx n → ℂ => 1 - I • cplx (cS c) :=
    continuous_const.sub ((continuous_cplx.comp continuous_cS).const_smul I)
  exact Complex.continuous_re.comp h.matrix_det

theorem continuous_det_fderiv_hmap :
    Continuous fun c : UIdx n → ℂ => LinearMap.det (fderiv ℝ hmap c : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) :=
  ContinuousLinearMap.continuous_det.comp (contDiff_hmap.continuous_fderiv (by simp))

/-- The derivative of $h$ at $c_0$ as a continuous linear equivalence. -/
def hmapL : (UIdx n → ℂ) ≃L[ℝ] (UIdx n → ℂ) :=
  (LinearEquiv.ofInjectiveEndo hmapD hmapD_injective).toContinuousLinearEquiv

theorem hasFDerivAt_hmap_c0 :
    HasFDerivAt hmap ((hmapL : (UIdx n → ℂ) ≃L[ℝ] (UIdx n → ℂ)) : (UIdx n → ℂ) →L[ℝ] (UIdx n → ℂ)) c0 := by
  have h := (contDiff_hmap.differentiable (by simp)).differentiableAt (x := (c0 : UIdx n → ℂ)).hasFDerivAt
  convert h using 1
  ext1 d
  have := congrArg (fun f : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ) => f d) (fderiv_hmap_c0 (n := n))
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this]; rfl

/-- **The chart**: an open $W\ni c_0$ on which $h$ is injective, with open image $h(W)$ and a continuous inverse $g$ on
$h(W)$, and on which $T$ is positive definite, $\operatorname{Re}\det(1 - i\sigma) > 0$ and $\det Dh\ne0$. -/
theorem exists_chart : ∃ (W : Set (UIdx n → ℂ)) (g : (UIdx n → ℂ) → UIdx n → ℂ),
    IsOpen W ∧ c0 ∈ W ∧ IsOpen (hmap '' W) ∧ ContinuousOn g (hmap '' W) ∧ (∀ c ∈ W, g (hmap c) = c) ∧
    ∀ c ∈ W, PDU (fun q => (c q).re) ∧ 0 < (1 - I • cplx (cS c)).det.re ∧
      LinearMap.det (fderiv ℝ hmap c : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) ≠ 0 := by
  have hcd : ContDiffAt ℝ ⊤ hmap (c0 : UIdx n → ℂ) := contDiff_hmap.contDiffAt
  set e := hcd.toOpenPartialHomeomorph hmap hasFDerivAt_hmap_c0 (by simp)
  have he : (e : (UIdx n → ℂ) → UIdx n → ℂ) = hmap := rfl
  have h0s : (c0 : UIdx n → ℂ) ∈ e.source := hcd.mem_toOpenPartialHomeomorph_source _ _
  have hdet0 : LinearMap.det (fderiv ℝ hmap (c0 : UIdx n → ℂ) : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) ≠ 0 := by
    rw [fderiv_hmap_c0, det_hmapD]
    exact Finset.prod_ne_zero_iff.mpr fun q _ => by have := wt_pos q; positivity
  have hev : ∀ᶠ c in 𝓝 (c0 : UIdx n → ℂ), PDU (fun q => (c q).re) ∧ 0 < (1 - I • cplx (cS c)).det.re ∧
      LinearMap.det (fderiv ℝ hmap c : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) ≠ 0 := by
    refine eventually_PDU.and (Filter.Eventually.and ?_ ?_)
    · refine continuous_det_one_sub.continuousAt.eventually (lt_mem_nhds ?_)
      show 0 < (1 - I • cplx (cS (c0 : UIdx n → ℂ))).det.re
      rw [cS_c0, cplx_zero, smul_zero, sub_zero, det_one, one_re]; norm_num
    · exact continuous_det_fderiv_hmap.continuousAt.eventually_ne hdet0
  obtain ⟨t, ht, hto, hc0t⟩ := eventually_nhds_iff.mp hev
  refine ⟨e.source ∩ t, e.symm, e.open_source.inter hto, ⟨h0s, hc0t⟩, ?_, ?_, ?_, ?_⟩
  · rw [← he]; exact e.isOpen_image_of_subset_source (e.open_source.inter hto) inter_subset_left
  · refine e.continuousOn_symm.mono ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [← he]; exact e.map_source hc.1
  · intro c hc; rw [← he]; exact e.left_inv hc.1
  · intro c hc; exact ht c hc.2

/-! ### The fibre limit -/

/-- **The fibre limit** (the measure-theoretic content of Lemma A6 for the Gram map): if $h$ is injective on an open
$W\ni c_0$ with left inverse $g$ continuous on the open set $h(W)$ and $\det Dh\ne0$ on $W$, then for $k\ge0$ continuous
on $W$,
$$\frac{1}{\mathrm{Leb}(\bar B_\varepsilon(c_Q))}\int_W k(c)\,[h(c)\in\bar B_\varepsilon(c_Q)]\,dc\to\frac{k(c_0)}{|\det Dh(c_0)|}.$$ -/
theorem tendsto_avg_hmap {W : Set (UIdx n → ℂ)} {g : (UIdx n → ℂ) → UIdx n → ℂ} (hW : IsOpen W)
    (hc0 : (c0 : UIdx n → ℂ) ∈ W) (hWo : IsOpen (hmap '' W)) (hg : ContinuousOn g (hmap '' W))
    (hgh : ∀ c ∈ W, g (hmap c) = c)
    (hdet : ∀ c ∈ W, LinearMap.det (fderiv ℝ hmap c : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ)) ≠ 0)
    {k : (UIdx n → ℂ) → ℝ} (hk : ContinuousOn k W) (hk0 : ∀ c ∈ W, 0 ≤ k c) :
    Tendsto (fun ε => (∫⁻ c in W, ENNReal.ofReal (k c) *
        (Metric.closedBall (coeffUC (sumSqC n)) ε).indicator 1 (hmap c)).toReal /
        (volume (Metric.closedBall (coeffUC (sumSqC n)) ε)).toReal) (𝓝[>] 0)
      (𝓝 (k c0 / |LinearMap.det (fderiv ℝ hmap (c0 : UIdx n → ℂ) : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ))|)) := by
  set J : (UIdx n → ℂ) → ℝ := fun c =>
    |LinearMap.det (fderiv ℝ hmap c : (UIdx n → ℂ) →ₗ[ℝ] (UIdx n → ℂ))| with hJ
  have hJc : Continuous J := continuous_abs.comp continuous_det_fderiv_hmap
  set G : (UIdx n → ℂ) → ℝ := fun w => k (g w) / J (g w) with hG
  have hmaps : MapsTo g (hmap '' W) W := by
    rintro _ ⟨c, hc, rfl⟩; rw [hgh c hc]; exact hc
  have hGc : ContinuousOn G (hmap '' W) := by
    refine (hk.comp hg hmaps).div (hJc.comp_continuousOn hg) ?_
    intro w hw
    exact abs_ne_zero.mpr (hdet _ (hmaps hw))
  have hG0 : ∀ w ∈ hmap '' W, 0 ≤ G w := fun w hw =>
    div_nonneg (hk0 _ (hmaps hw)) (abs_nonneg _)
  have hcQ : coeffUC (sumSqC n) ∈ hmap '' W := ⟨c0, hc0, hmap_c0⟩
  have h := QuadFormsKB.Tamagawa.Measure.Leray.tendsto_avg_closedBall volume
    (c₀ := coeffUC (sumSqC n)) (fun ε hε => Metric.measure_closedBall_pos volume _ hε)
    (fun ε => measure_closedBall_lt_top.ne) hWo hcQ hGc hG0
  have hGv : G (coeffUC (sumSqC n)) = k c0 / J c0 := by
    simp only [G, ← hmap_c0, hgh _ hc0]
  rw [hGv] at h
  refine h.congr' ?_
  -- for small ε the ball lies in h(W)
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hWo _ hcQ
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hB : Metric.closedBall (coeffUC (sumSqC n)) ε ⊆ hmap '' W :=
    (Metric.closedBall_subset_ball hε.2).trans hsub
  have hBm : MeasurableSet (Metric.closedBall (coeffUC (sumSqC n)) ε) := Metric.isClosed_closedBall.measurableSet
  set s := W ∩ hmap ⁻¹' Metric.closedBall (coeffUC (sumSqC n)) ε
  have hs : MeasurableSet s := hW.measurableSet.inter (continuous_hmap.measurable hBm)
  have himg : hmap '' s = Metric.closedBall (coeffUC (sumSqC n)) ε := by
    ext w; constructor
    · rintro ⟨c, hc, rfl⟩; exact hc.2
    · intro hw
      obtain ⟨c, hc, rfl⟩ := hB hw
      exact ⟨c, ⟨hc, hw⟩, rfl⟩
  have hinj : InjOn hmap s := fun c hc c' hc' he => by
    rw [← hgh c hc.1, ← hgh c' hc'.1, he]
  have hderiv : ∀ c ∈ s, HasFDerivWithinAt hmap (fderiv ℝ hmap c) s c := fun c _ =>
    ((contDiff_hmap.differentiable (by simp)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv hinj
    (fun w => ENNReal.ofReal (G w))
  rw [himg] at hcov
  congr 1
  rw [hcov]
  -- left side: restrict to `s`
  have hL : ∫⁻ c in W, ENNReal.ofReal (k c) * (Metric.closedBall (coeffUC (sumSqC n)) ε).indicator 1 (hmap c) =
      ∫⁻ c in s, ENNReal.ofReal (k c) := by
    rw [← lintegral_indicator hs, ← lintegral_indicator hW.measurableSet]
    refine lintegral_congr fun c => ?_
    by_cases hcW : c ∈ W
    · by_cases hcB : hmap c ∈ Metric.closedBall (coeffUC (sumSqC n)) ε
      · rw [indicator_of_mem hcW, indicator_of_mem hcB, Pi.one_apply, mul_one,
          indicator_of_mem (show c ∈ s from ⟨hcW, hcB⟩)]
      · rw [indicator_of_mem hcW, indicator_of_notMem hcB, mul_zero,
          indicator_of_notMem (show c ∉ s from fun h => hcB h.2)]
    · rw [indicator_of_notMem hcW, indicator_of_notMem (show c ∉ s from fun h => hcW h.1)]
  rw [hL]
  congr 1
  refine (setLIntegral_congr_fun hs fun c hc => ?_).symm
  have hJ0 : J c ≠ 0 := abs_ne_zero.mpr (hdet c hc.1)
  have hGc' : G (hmap c) = k c / J c := by simp only [G, hgh c hc.1]
  rw [hGc', ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  change k c = J c * (k c / J c)
  rw [mul_div_cancel₀ _ hJ0]

end QuadFormsKB.Hanke2005.ArchCx
