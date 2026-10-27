import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeQuat
import QuadFormsKB.Tamagawa.Measure.Weil.TrdSelfDual

/-!
# The local $\psi_v\circ\operatorname{Tr}_{K/k}$ self-dual measure (local part)

The diagonal self-duality (`selfDual_diag_iff`, for $F_v^4$) for an arbitrary finite index set $\iota$, and its
application to a quadratic extension $K = k(\delta)$, $\delta^2 = d$, with basis $b = (1,\delta)$:

* **`selfDual_diagN_iff`**: on $k_v^\iota$ with the pairing $\psi_v(\sum_ig_ix_iy_i)$ ($g_i\ne0$), the measure
  $r\,dx_v^{\otimes\iota}$ satisfies Fourier inversion on all box indicators iff $r = \prod_i|g_i|_v^{1/2}$.
* **`traceMatrix_basisOneDelta`**: the trace Gram matrix of $(1,\delta)$ is $\operatorname{diag}(2, 2d)$, i.e.
  $\operatorname{Tr}_{K/k}(xy) = 2x_0y_0 + 2d\,x_1y_1$; `discr_basisOneDelta`: $\det G = 4d$.
* **`traceFactor_eq_diagFactorN`**: the local factor `traceFactor b v` $=|\det G|_v^{1/2}$ of `BaseChangeMeasure.lean`
  is $\prod_i|g_i|_v^{1/2}$ for $g = (2, 2d)$. Hence (**`selfDual_trace_iff`**) `traceFactor b v`$\cdot dx_v^{\otimes2}$ is
  the unique $\psi_v\circ\operatorname{Tr}_{K/k}$-self-dual multiple of the coordinate measure on $K\otimes_kk_v = k_v^2$;
  with `finprod_traceFactor_mul_inf` (product $=1$) and `map_adeleBaseChange_muAddVec` this completes the construction:
  the restricted product of the local $\psi_v\circ\operatorname{Tr}$-self-dual measures is `muAddVec k (Fin 2)`, which
  `adeleBaseChange b` carries to `muAdd K`. (The archimedean self-duality is, as elsewhere in the library, not formalized; only the
  factor $|\det G|_\infty^{1/2}$ enters.)
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

section DiagN

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {ι : Type} [Fintype ι]

local notation "Kv" => v.adicCompletion F

/-- $\mathcal F_{g,\mu}f(y) = \int f(x)\,\psi_v(\sum_ig_ix_iy_i)\,d\mu(x)$ on $F_v^\iota$. -/
def fourierDiagN (μ : Measure (ι → Kv)) (g : ι → Kv) (f : (ι → Kv) → ℂ) (y : ι → Kv) : ℂ :=
  ∫ x, f x * (Analysis.psiV v (∑ i, g i * x i * y i) : ℂ) ∂μ

/-- $\mathcal F^-_{g,\mu}f(x) = \int f(y)\,\psi_v(-\sum_ig_ix_iy_i)\,d\mu(y)$ on $F_v^\iota$. -/
def fourierDiagInvN (μ : Measure (ι → Kv)) (g : ι → Kv) (f : (ι → Kv) → ℂ) (x : ι → Kv) : ℂ :=
  ∫ y, f y * (Analysis.psiV v (-(∑ i, g i * x i * y i)) : ℂ) ∂μ

/-- The indicator of the box $\prod_i(c_i + \mathfrak p_v^{k_i})\subseteq F_v^\iota$. -/
def boxIndN (c : ι → Kv) (k : ι → ℤ) (x : ι → Kv) : ℂ := ∏ i, Analysis.ballIndV v (c i) (k i) (x i)

theorem psiV_sum (s : ι → Kv) : (Analysis.psiV v (∑ i, s i) : ℂ) = ∏ i, (Analysis.psiV v (s i) : ℂ) := by
  suffices h : ∀ S : Finset ι, (Analysis.psiV v (∑ i ∈ S, s i) : ℂ) = ∏ i ∈ S, (Analysis.psiV v (s i) : ℂ) from
    h Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

/-- The coordinate self-dual measure $dx_v^{\otimes\iota}$. -/
abbrev volVN : Measure (ι → Kv) := Measure.pi fun _ : ι => Analysis.selfDualV v

theorem fourierDiagN_boxIndN (r : ℝ) (hr : 0 ≤ r) (g : ι → Kv) (c : ι → Kv) (k : ι → ℤ) (y : ι → Kv) :
    fourierDiagN v (ENNReal.ofReal r • volVN v) g (boxIndN v c k) y =
      r * ∏ i, Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * y i) := by
  unfold fourierDiagN
  rw [integral_smul_measure, ENNReal.toReal_ofReal hr, Complex.real_smul]
  congr 1
  have hfun : (fun x : ι → Kv => boxIndN v c k x * (Analysis.psiV v (∑ i, g i * x i * y i) : ℂ)) =
      fun x => ∏ i, (Analysis.ballIndV v (c i) (k i) (x i) * (Analysis.psiV v (x i * (g i * y i)) : ℂ)) := by
    funext x
    rw [boxIndN, psiV_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 3; ring
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun i t => Analysis.ballIndV v (c i) (k i) t * (Analysis.psiV v (t * (g i * y i)) : ℂ))
    (μ := fun _ : ι => Analysis.selfDualV v)
  rw [hfun]
  exact hprod

theorem fourierDiagInvN_fourierDiagN_boxIndN (r : ℝ) (hr : 0 ≤ r) (g : ι → Kv) (hg : ∀ i, g i ≠ 0)
    (c : ι → Kv) (k : ι → ℤ) :
    fourierDiagInvN v (ENNReal.ofReal r • volVN v) g
        (fourierDiagN v (ENNReal.ofReal r • volVN v) g (boxIndN v c k)) =
      fun x => ((r ^ 2 * ∏ i, ((distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ))⁻¹ : ℝ) : ℂ) *
        boxIndN v c k x := by
  funext x
  unfold fourierDiagInvN
  simp_rw [fourierDiagN_boxIndN v r hr g c k]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hr, Complex.real_smul]
  have hfun : (fun y : ι → Kv => ((r : ℂ) * ∏ i, Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * y i)) *
      (Analysis.psiV v (-(∑ i, g i * x i * y i)) : ℂ)) =
      fun y => (r : ℂ) * ∏ i, (Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * y i) *
        (Analysis.psiV v (-(x i * (g i * y i))) : ℂ)) := by
    funext y
    rw [mul_assoc, ← neg_neg (∑ i, g i * x i * y i), neg_neg, ← Finset.sum_neg_distrib, psiV_sum,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 3; ring
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun i s => Analysis.fourierV v (Analysis.ballIndV v (c i) (k i)) (g i * s) *
      (Analysis.psiV v (-(x i * (g i * s))) : ℂ))
    (μ := fun _ : ι => Analysis.selfDualV v)
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
  rw [boxIndN]
  simp only [Complex.real_smul, Finset.prod_mul_distrib]
  push_cast
  ring

/-- $\prod_i|g_i|_v^{1/2}$ $(=|\det\operatorname{diag}(g)|_v^{1/2})$. -/
def diagFactorN (g : ι → Kv) (hg : ∀ i, g i ≠ 0) : ℝ :=
  ∏ i, Real.sqrt (distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ)

theorem diagFactorN_pos (g : ι → Kv) (hg : ∀ i, g i ≠ 0) : 0 < diagFactorN v g hg :=
  Finset.prod_pos fun _ _ => Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (distribHaarChar_ne_zero _)))

theorem diagFactorN_sq_mul (g : ι → Kv) (hg : ∀ i, g i ≠ 0) :
    diagFactorN v g hg ^ 2 * ∏ i, ((distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ))⁻¹ = 1 := by
  rw [diagFactorN, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Real.sq_sqrt (NNReal.coe_nonneg _), mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr (distribHaarChar_ne_zero _))]

/-- **Self-duality for a diagonal pairing on $F_v^\iota$**: $r\,dx_v^{\otimes\iota}$ ($r\ge0$) satisfies Fourier inversion
on all box indicators iff $r = \prod_i|g_i|_v^{1/2}$ (`selfDual_diag_iff` for any finite $\iota$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified] (self-dual measures)"]
theorem selfDual_diagN_iff (g : ι → Kv) (hg : ∀ i, g i ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    (∀ c k, fourierDiagInvN v (ENNReal.ofReal r • volVN v) g
        (fourierDiagN v (ENNReal.ofReal r • volVN v) g (boxIndN v c k)) = boxIndN v c k) ↔
      r = diagFactorN v g hg := by
  set P := ∏ i, ((distribHaarChar Kv (Units.mk0 (g i) (hg i)) : ℝ))⁻¹
  have hP : 0 < P := Finset.prod_pos fun i _ =>
    inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (distribHaarChar_ne_zero _)))
  have hD := diagFactorN_sq_mul v g hg
  constructor
  · intro h
    have h1 := congrFun ((fourierDiagInvN_fourierDiagN_boxIndN v r hr g hg 0 0).symm.trans (h 0 0)) 0
    have hb : boxIndN v 0 0 (0 : ι → Kv) = 1 := by
      simp [boxIndN, Analysis.ballIndV]
    rw [hb, mul_one] at h1
    have h2 : r ^ 2 * P = 1 := Complex.ofReal_eq_one.mp h1
    have h3 : r ^ 2 = diagFactorN v g hg ^ 2 := by
      have := hD.trans h2.symm
      exact (mul_right_cancel₀ hP.ne' this).symm
    exact (pow_left_inj₀ hr (diagFactorN_pos v g hg).le two_ne_zero).mp h3
  · rintro rfl c k
    rw [fourierDiagInvN_fourierDiagN_boxIndN v _ (diagFactorN_pos v g hg).le g hg]
    funext x
    rw [hD]; simp

end DiagN

section QuadraticTrace

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {d : k} {b : Module.Basis (Fin 2) k K} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d)

include hb0 in
theorem trace_one_eq_two : Algebra.trace k K 1 = 2 := by
  rw [← map_one (algebraMap k K), Algebra.trace_algebraMap, Module.finrank_eq_card_basis b, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_ofNat]

include hb0 hb1 in
theorem trace_delta_eq_zero : Algebra.trace k K (b 1) = 0 := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  have h0 : b.repr (b 1 * b 0) 0 = 0 := by
    rw [hb0, mul_one, b.repr_self, Finsupp.single_apply, if_neg (by decide)]
  have h1 : b.repr (b 1 * b 1) 1 = 0 := by
    rw [hb1, Algebra.algebraMap_eq_smul_one, ← hb0, map_smul, b.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, if_neg (by decide), smul_zero]
  rw [h0, h1, add_zero]

include hb0 hb1 in
/-- **The trace Gram matrix of $(1,\delta)$ is $\operatorname{diag}(2, 2d)$**:
$\operatorname{Tr}_{K/k}(xy) = 2x_0y_0 + 2d\,x_1y_1$. -/
theorem traceMatrix_basisOneDelta : Algebra.traceMatrix k b = Matrix.diagonal ![2, 2 * d] := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  fin_cases i <;> fin_cases j
  · simp [hb0, trace_one_eq_two hb0]
  · simp [hb0, trace_delta_eq_zero hb0 hb1]
  · simp [hb0, trace_delta_eq_zero hb0 hb1]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.diagonal_apply_eq, Matrix.cons_val_one,
      Matrix.head_cons]
    rw [hb1, Algebra.trace_algebraMap, Module.finrank_eq_card_basis b, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat]
    rfl

include hb0 hb1 in
/-- $\det G = 4d$. -/
theorem discr_basisOneDelta : Algebra.discr k b = 4 * d := by
  rw [Algebra.discr_def, traceMatrix_basisOneDelta hb0 hb1, Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

omit [NumberField K] [Algebra k K] in
theorem two_d_ne_zero (hd : d ≠ 0) (v : HeightOneSpectrum (𝓞 k)) :
    ∀ i, algebraMap k (v.adicCompletion k) (![2, 2 * d] i) ≠ 0 := by
  intro i
  rw [map_ne_zero_iff _ (algebraMap k (v.adicCompletion k)).injective]
  fin_cases i
  · exact two_ne_zero
  · exact mul_ne_zero two_ne_zero hd

include hb0 hb1 in
/-- **The local factor is the diagonal factor**: `traceFactor b v` $=|\det G|_v^{1/2} = (|2|_v|2d|_v)^{1/2}$. -/
theorem traceFactor_eq_diagFactorN (hd : d ≠ 0) (v : HeightOneSpectrum (𝓞 k)) :
    traceFactor b v =
      diagFactorN v (fun i => algebraMap k (v.adicCompletion k) (![2, 2 * d] i)) (two_d_ne_zero hd v) := by
  rw [traceFactor, diagFactorN, Fin.prod_univ_two, ← Real.sqrt_mul (NNReal.coe_nonneg _)]
  congr 1
  rw [← NNReal.coe_mul, ← map_mul, modAt]
  congr 2
  refine Units.ext ?_
  rw [unitAt_val, Units.val_mul, Units.val_mk0, Units.val_mk0]
  change algebraMap k (v.adicCompletion k) (Algebra.discr k b) = _
  rw [discr_basisOneDelta hb0 hb1, ← map_mul]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

include hb0 hb1 in
/-- **The local $\psi_v\circ\operatorname{Tr}_{K/k}$-self-dual measure on $K\otimes_kk_v = k_v^2$** is
`traceFactor b v`$\cdot dx_v^{\otimes2}$, and it is the only multiple of $dx_v^{\otimes2}$ that is self-dual
($\operatorname{Tr}(xy) = 2x_0y_0 + 2dx_1y_1$ by `traceMatrix_basisOneDelta`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem selfDual_trace_iff (hd : d ≠ 0) (v : HeightOneSpectrum (𝓞 k)) (r : ℝ) (hr : 0 ≤ r) :
    (∀ c kk, fourierDiagInvN v (ENNReal.ofReal r • volVN v) (fun i => algebraMap k _ (![2, 2 * d] i))
        (fourierDiagN v (ENNReal.ofReal r • volVN v) (fun i => algebraMap k _ (![2, 2 * d] i))
          (boxIndN v c kk)) = boxIndN v c kk) ↔ r = traceFactor b v := by
  rw [traceFactor_eq_diagFactorN hb0 hb1 hd v]
  exact selfDual_diagN_iff v _ (two_d_ne_zero hd v) r hr

end QuadraticTrace

end

end QuadFormsKB.Tamagawa.Measure.Weil
