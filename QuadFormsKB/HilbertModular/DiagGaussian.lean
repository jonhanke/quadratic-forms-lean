import QuadFormsKB.Analysis.LatticePoisson

/-!
# Poisson summation for diagonal complex Gaussians

For a finite index set $J$, rates $b \in \mathbb{C}^J$ with $\operatorname{Re} b_j > 0$ and
$G_b(\vec{v}) = \exp\big(-\pi\sum_j b_jv_j^2\big)$ on $\mathbb{R}^J$:

* `diagGaussian`: $G_b$ as a Schwartz function (the product of the scalar Gaussian $e^{-\pi c\|\vec{v}\|^2}$, $0 < c <
  \min_j\operatorname{Re}b_j$, with a function of temperate growth);
* `fourier_diagGaussian`: $\hat G_b(\xi) = \prod_j(b_j^{-1})^{1/2}\cdot G_{b^{-1}}(\xi)$ (Mathlib's
  `integral_cexp_neg_sum_mul_add`);
* **`tsum_diagGaussian`**: for real matrices $M, M'$ with $M^{\mathsf T}M' = 1$ (so $M' = M^{-\mathsf T}$),
  $$\sum_{\vec{k}\in\mathbb{Z}^J}G_b(M\vec{k}) = |\det M|^{-1}\prod_j(b_j^{-1})^{1/2}\sum_{\vec{m}\in\mathbb{Z}^J}G_{b^{-1}}(M'\vec{m}),$$
  with the principal branch of $(\cdot)^{1/2}$ (`Complex.cpow`; $b_j^{-1}$ lies in the right half plane). Both sides
  converge absolutely (`summable_norm_diagGaussian`).

This generalizes `QuadFormsKB.Analysis.tsum_gaussian_quadratic` (one complex rate $w$ for all coordinates) to
**one complex rate per coordinate**. That is what the theta series of a totally positive definite form over a
totally real field needs: the rate at the coordinates of the real place $v$ is $-2iz_v$, and the $z_v$ are
independent (`QuadFormsKB.HilbertModular.ThetaInversion`).

*Proof.* Poisson summation over $\mathbb{Z}^N$ (`QuadFormsKB.Analysis.intPoisson`) for $G_b\circ M$, with
$\widehat{f\circ M}(\xi) = |\det M|^{-1}\hat f(M^{-\mathsf T}\xi)$ (Sphere-Packing-Lean's `fourier_comp_linearEquiv`),
after reindexing $J \simeq \mathrm{Fin}\,N$.

Sources: Stein–Shakarchi, *Fourier Analysis*, Ch. 6 (Poisson summation) [unverified].
-/

open MeasureTheory Complex Matrix
open scoped FourierTransform RealInnerProductSpace SchwartzMap

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

noncomputable section

section Schwartz

variable {J : Type*} [Fintype J]

/-- The rate $c = (1 + \sum_j 1/\operatorname{Re}b_j)^{-1}$; it satisfies $0 < c < \operatorname{Re} b_j$ for all $j$. -/
def diagRate (b : J → ℂ) : ℝ := (1 + ∑ j, 1 / (b j).re)⁻¹

lemma diagRate_pos {b : J → ℂ} (hb : ∀ j, 0 < (b j).re) : 0 < diagRate b := by
  unfold diagRate
  have : 0 ≤ ∑ j, 1 / (b j).re := Finset.sum_nonneg fun j _ => (one_div_pos.2 (hb j)).le
  positivity

lemma diagRate_lt {b : J → ℂ} (hb : ∀ j, 0 < (b j).re) (j : J) : diagRate b < (b j).re := by
  unfold diagRate
  have h1 : 1 / (b j).re ≤ ∑ i, 1 / (b i).re :=
    Finset.single_le_sum (f := fun i => 1 / (b i).re) (fun i _ => (one_div_pos.2 (hb i)).le)
      (Finset.mem_univ j)
  have hj := hb j
  have h0 : 0 ≤ ∑ i, 1 / (b i).re := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hb i)).le
  rw [inv_lt_comm₀ (by linarith) hj]
  calc ((b j).re)⁻¹ = 1 / (b j).re := by rw [one_div]
    _ < 1 + ∑ i, 1 / (b i).re := by linarith

omit [Fintype J] in
lemma hasTemperateGrowth_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset J) (g : J → E → ℂ) (hg : ∀ j, (g j).HasTemperateGrowth) :
    (fun x => ∏ j ∈ s, g j x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have : (fun x => ∏ j ∈ insert a s, g j x) = g a * fun x => ∏ j ∈ s, g j x := by
      funext x; simp [Finset.prod_insert ha]
    rw [this]
    exact (hg a).mul ih

/-- The remaining factor $\prod_j e^{-\pi(b_j - c)v_j^2}$, of temperate growth. -/
lemma hasTemperateGrowth_diagFactor {b : J → ℂ} (hb : ∀ j, 0 < (b j).re) :
    (fun x : EuclideanSpace ℝ J =>
      ∏ j, cexp (-(Real.pi * (b j - diagRate b)) * (((‖x j‖ ^ 2 : ℝ)) : ℂ))).HasTemperateGrowth := by
  refine hasTemperateGrowth_prod _ _ fun j => ?_
  have hre : 0 < (Real.pi * (b j - diagRate b) : ℂ).re := by
    simp only [mul_re, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos (by linarith [diagRate_lt hb j])
  have h1 := (QuadFormsKB.Analysis.gaussianSchwartz (E := ℝ) _ hre).hasTemperateGrowth
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) j : EuclideanSpace ℝ J →L[ℝ] ℝ).hasTemperateGrowth
  have := h1.comp h2
  convert this using 1
  funext x
  simp

private lemma pi_rate_re {b : J → ℂ} (hb : ∀ j, 0 < (b j).re) :
    0 < ((Real.pi : ℂ) * (diagRate b : ℂ)).re := by
  simpa [mul_re] using mul_pos Real.pi_pos (diagRate_pos hb)

/-- **The diagonal complex Gaussian** $G_b(\vec{v}) = e^{-\pi\sum_jb_jv_j^2}$ on $\mathbb{R}^J$ as a Schwartz function,
for $\operatorname{Re} b_j > 0$ (`diagGaussian_apply`). -/
def diagGaussian (b : J → ℂ) (hb : ∀ j, 0 < (b j).re) : 𝓢(EuclideanSpace ℝ J, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x : EuclideanSpace ℝ J =>
      ∏ j, cexp (-(Real.pi * (b j - diagRate b)) * (((‖x j‖ ^ 2 : ℝ)) : ℂ)))
    (QuadFormsKB.Analysis.gaussianSchwartz _ (pi_rate_re hb))

theorem diagGaussian_apply (b : J → ℂ) (hb : ∀ j, 0 < (b j).re) (x : EuclideanSpace ℝ J) :
    diagGaussian b hb x = cexp (-Real.pi * ∑ j, b j * ((x j : ℝ) : ℂ) ^ 2) := by
  rw [diagGaussian, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_diagFactor hb),
    QuadFormsKB.Analysis.gaussianSchwartz_apply, smul_eq_mul, ← Complex.exp_sum, ← Complex.exp_add,
    EuclideanSpace.real_norm_sq_eq]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Fintype J] in
private lemma pi_mul_re {b : J → ℂ} (hb : ∀ j, 0 < (b j).re) (j : J) :
    0 < ((Real.pi : ℂ) * b j).re := by
  simpa [mul_re] using mul_pos Real.pi_pos (hb j)

/-- **Fourier transform of the diagonal Gaussian:**
$\hat G_b(\xi) = \prod_j(b_j^{-1})^{1/2}\,e^{-\pi\sum_jb_j^{-1}\xi_j^2}$, with Mathlib's
$\hat f(\xi) = \int f(\vec{x})e^{-2\pi i\langle\vec{x},\xi\rangle}d\vec{x}$ and the principal branch of $(\cdot)^{1/2}$. -/
theorem fourier_diagGaussian (b : J → ℂ) (hb : ∀ j, 0 < (b j).re) (ξ : EuclideanSpace ℝ J) :
    𝓕 (fun x : EuclideanSpace ℝ J => diagGaussian b hb x) ξ =
      (∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ)) * cexp (-Real.pi * ∑ j, (b j)⁻¹ * ((ξ j : ℝ) : ℂ) ^ 2) := by
  rw [Real.fourier_eq']
  simp_rw [diagGaussian_apply, smul_eq_mul, ← Complex.exp_add]
  rw [← (PiLp.volume_preserving_toLp J).integral_comp
    (MeasurableEquiv.toLp 2 (J → ℝ)).measurableEmbedding]
  have h := GaussianFourier.integral_cexp_neg_sum_mul_add (fun j => pi_mul_re hb j)
    (fun j => -2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))
  convert h using 1
  · congr 1
    funext x
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ofReal_neg, ofReal_mul,
      ofReal_ofNat, ofReal_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
  · rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have hb0 : b j ≠ 0 := by intro h0; have := hb j; rw [h0] at this; simp at this
      congr 1
      field_simp
    · congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hb0 : b j ≠ 0 := by intro h0; have := hb j; rw [h0] at this; simp at this
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring

end Schwartz

section Poisson

variable {N : ℕ}

local notation "EN" => EuclideanSpace ℝ (Fin N)

/-- The linear automorphism $\vec{v} \mapsto M\vec{v}$ of $\mathbb{R}^N$ for $\det M \ne 0$. -/
private def matEquiv (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0) : EN ≃ₗ[ℝ] EN :=
  LinearEquiv.ofLinearMap (Matrix.toEuclideanLin M) (Matrix.toEuclideanLin M⁻¹)
    (by rw [← Matrix.toLpLin_mul_same, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.toLpLin_one])
    (by rw [← Matrix.toLpLin_mul_same, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.toLpLin_one])

private lemma det_ne_zero_of_mul {M M' : Matrix (Fin N) (Fin N) ℝ} (hMM : Mᵀ * M' = 1) :
    M.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hMM
  rw [det_mul, det_transpose, h, zero_mul, det_one] at this
  exact zero_ne_one this

private lemma toEuclideanLin_apply_ofLp (M : Matrix (Fin N) (Fin N) ℝ) (v : EN) (j : Fin N) :
    (Matrix.toEuclideanLin M v) j = (M *ᵥ v.ofLp) j := by
  simp [Matrix.toLpLin_apply]

private lemma intPt_ofLp' (k : Fin N → ℤ) :
    (QuadFormsKB.Analysis.intPt k).ofLp = fun i => (k i : ℝ) := by
  ext i; simp [QuadFormsKB.Analysis.intPt]

/-- The Schwartz function $G_b\circ M$. -/
private def diagGaussianComp (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0) (b : Fin N → ℂ)
    (hb : ∀ j, 0 < (b j).re) : 𝓢(EN, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (matEquiv M hM).toContinuousLinearEquiv
    (diagGaussian b hb)

private lemma diagGaussianComp_intPt (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0)
    (b : Fin N → ℂ) (hb : ∀ j, 0 < (b j).re) (k : Fin N → ℤ) :
    diagGaussianComp M hM b hb (QuadFormsKB.Analysis.intPt k) =
      cexp (-Real.pi * ∑ j, b j * (((M *ᵥ fun i => (k i : ℝ)) j : ℝ) : ℂ) ^ 2) := by
  change diagGaussian b hb (Matrix.toEuclideanLin M (QuadFormsKB.Analysis.intPt k)) = _
  rw [diagGaussian_apply]
  simp_rw [toEuclideanLin_apply_ofLp, intPt_ofLp']

theorem summable_norm_diagGaussian_fin (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0)
    (b : Fin N → ℂ) (hb : ∀ j, 0 < (b j).re) :
    Summable fun k : Fin N → ℤ =>
      ‖cexp (-Real.pi * ∑ j, b j * (((M *ᵥ fun i => (k i : ℝ)) j : ℝ) : ℂ) ^ 2)‖ := by
  simpa [diagGaussianComp_intPt] using
    QuadFormsKB.Analysis.summable_norm_intPt (diagGaussianComp M hM b hb)

theorem tsum_diagGaussian_fin (M M' : Matrix (Fin N) (Fin N) ℝ) (hMM : Mᵀ * M' = 1)
    (b : Fin N → ℂ) (hb : ∀ j, 0 < (b j).re) :
    ∑' k : Fin N → ℤ, cexp (-Real.pi * ∑ j, b j * (((M *ᵥ fun i => (k i : ℝ)) j : ℝ) : ℂ) ^ 2) =
      ((|M.det|)⁻¹ : ℝ) * (∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ)) *
        ∑' m : Fin N → ℤ,
          cexp (-Real.pi * ∑ j, (b j)⁻¹ * (((M' *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) := by
  have hM := det_ne_zero_of_mul hMM
  have hM' : M' = M⁻¹ᵀ := by
    rw [Matrix.transpose_nonsing_inv, eq_comm]
    exact Matrix.inv_eq_right_inv hMM
  let L : EN ≃ₗ[ℝ] EN := matEquiv M hM
  have hP := QuadFormsKB.Analysis.intPoisson (diagGaussianComp M hM b hb)
  have hdetL : LinearMap.det (L : EN →ₗ[ℝ] EN) = M.det := by
    change LinearMap.det (Matrix.toEuclideanLin M) = M.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hadj : ((L.symm : EN ≃ₗ[ℝ] EN).toLinearMap).adjoint = Matrix.toEuclideanLin M' := by
    change (Matrix.toEuclideanLin M⁻¹).adjoint = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial,
      hM']
  have hrhs : ∀ m : Fin N → ℤ,
      𝓕 (fun x : EN => diagGaussianComp M hM b hb x) (QuadFormsKB.Analysis.intPt m) =
        ((|M.det|)⁻¹ : ℝ) * (∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ)) *
          cexp (-Real.pi * ∑ j, (b j)⁻¹ * (((M' *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) := by
    intro m
    have h1 := SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv L
      (fun x : EN => diagGaussian b hb x) (QuadFormsKB.Analysis.intPt m)
    have hfx : (fun x : EN => diagGaussianComp M hM b hb x) = fun x => diagGaussian b hb (L x) := rfl
    rw [hfx, h1, hadj, fourier_diagGaussian, hdetL, Complex.real_smul]
    simp_rw [toEuclideanLin_apply_ofLp, intPt_ofLp']
    push_cast
    ring
  simp_rw [diagGaussianComp_intPt, hrhs] at hP
  rw [hP, tsum_mul_left]

theorem tsum_diagGaussian_shift_fin (M M' : Matrix (Fin N) (Fin N) ℝ) (hMM : Mᵀ * M' = 1)
    (b : Fin N → ℂ) (hb : ∀ j, 0 < (b j).re) (h : Fin N → ℝ) :
    ∑' k : Fin N → ℤ, cexp (-Real.pi * ∑ j, b j * (((M *ᵥ fun i => (k i : ℝ) + h i) j : ℝ) : ℂ) ^ 2) =
      ((|M.det|)⁻¹ : ℝ) * (∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ)) *
        ∑' m : Fin N → ℤ,
          cexp (-Real.pi * ∑ j, (b j)⁻¹ * (((M' *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
            cexp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * h i : ℝ) : ℂ)) := by
  have hM := det_ne_zero_of_mul hMM
  have hM' : M' = M⁻¹ᵀ := by
    rw [Matrix.transpose_nonsing_inv, eq_comm]
    exact Matrix.inv_eq_right_inv hMM
  let L : EN ≃ₗ[ℝ] EN := matEquiv M hM
  set v : EN := WithLp.toLp 2 h with hv
  have hP := SchwartzMap.PoissonSummation.Standard.poissonSummation_standard (d := N)
    (diagGaussianComp M hM b hb) v
  rw [← (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := N)).tsum_eq] at hP
  have hdetL : LinearMap.det (L : EN →ₗ[ℝ] EN) = M.det := by
    change LinearMap.det (Matrix.toEuclideanLin M) = M.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hadj : ((L.symm : EN ≃ₗ[ℝ] EN).toLinearMap).adjoint = Matrix.toEuclideanLin M' := by
    change (Matrix.toEuclideanLin M⁻¹).adjoint = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial,
      hM']
  have hrhs : ∀ m : Fin N → ℤ,
      𝓕 (fun x : EN => diagGaussianComp M hM b hb x) (QuadFormsKB.Analysis.intPt m) =
        ((|M.det|)⁻¹ : ℝ) * (∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ)) *
          cexp (-Real.pi * ∑ j, (b j)⁻¹ * (((M' *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) := by
    intro m
    have h1 := SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv L
      (fun x : EN => diagGaussian b hb x) (QuadFormsKB.Analysis.intPt m)
    have hfx : (fun x : EN => diagGaussianComp M hM b hb x) = fun x => diagGaussian b hb (L x) := rfl
    rw [hfx, h1, hadj, fourier_diagGaussian, hdetL, Complex.real_smul]
    simp_rw [toEuclideanLin_apply_ofLp, intPt_ofLp']
    push_cast
    ring
  have hl : ∀ k : Fin N → ℤ, diagGaussianComp M hM b hb
      (v + ((SchwartzMap.PoissonSummation.Standard.equivIntVec (d := N) k :
        SchwartzMap.standardLattice N) : EN)) =
      cexp (-Real.pi * ∑ j, b j * (((M *ᵥ fun i => (k i : ℝ) + h i) j : ℝ) : ℂ) ^ 2) := by
    intro k
    change diagGaussian b hb (Matrix.toEuclideanLin M _) = _
    rw [diagGaussian_apply]
    simp_rw [toEuclideanLin_apply_ofLp]
    congr 3
    funext j
    congr 4
    funext i
    simp [hv, SchwartzMap.PoissonSummation.Standard.intVec, add_comm]
  have hinner : ∀ k : Fin N → ℤ,
      ⟪v, SchwartzMap.PoissonSummation.Standard.intVec (d := N) k⟫_[ℝ] = ∑ i, (k i : ℝ) * h i := by
    intro k
    rw [← RCLike.inner_eq_wInner_one]
    simp [hv, SchwartzMap.PoissonSummation.Standard.intVec, PiLp.inner_apply, mul_comm]
  simp_rw [hl] at hP
  rw [hP, ← tsum_mul_left]
  congr 1; funext k
  rw [show SchwartzMap.PoissonSummation.Standard.intVec (d := N) k =
      QuadFormsKB.Analysis.intPt k from rfl, hrhs,
    ← show SchwartzMap.PoissonSummation.Standard.intVec (d := N) k =
      QuadFormsKB.Analysis.intPt k from rfl, hinner]
  ring

end Poisson

section General

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The value $G_b(M\vec{k}) = e^{-\pi\sum_jb_j(M\vec{k})_j^2}$ at an integer vector. -/
abbrev gaussAt (b : J → ℂ) (M : Matrix J J ℝ) (k : J → ℤ) : ℂ :=
  cexp (-Real.pi * ∑ j, b j * (((M *ᵥ fun i => (k i : ℝ)) j : ℝ) : ℂ) ^ 2)

private lemma gaussAt_reindex (e : J ≃ Fin (Fintype.card J)) (b : J → ℂ) (M : Matrix J J ℝ)
    (k : J → ℤ) :
    cexp (-Real.pi * ∑ j, (b ∘ e.symm) j *
      ((((Matrix.reindex e e M) *ᵥ fun i => ((k ∘ e.symm) i : ℝ)) j : ℝ) : ℂ) ^ 2) =
      gaussAt b M k := by
  have h : ((Matrix.reindex e e M) *ᵥ fun i => ((k ∘ e.symm) i : ℝ)) =
      (M *ᵥ fun i => (k i : ℝ)) ∘ e.symm := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    funext i
    simp
  rw [h]
  congr 2
  exact e.symm.sum_comp (fun j => b j * (((M *ᵥ fun i => (k i : ℝ)) j : ℝ) : ℂ) ^ 2)

/-- **Absolute convergence** of $\sum_{\vec{k}\in\mathbb{Z}^J}G_b(M\vec{k})$ for $\det M \ne 0$, $\operatorname{Re} b_j > 0$. -/
theorem summable_norm_gaussAt (M : Matrix J J ℝ) (hM : M.det ≠ 0) (b : J → ℂ)
    (hb : ∀ j, 0 < (b j).re) : Summable fun k : J → ℤ => ‖gaussAt b M k‖ := by
  set e := Fintype.equivFin J
  have h := summable_norm_diagGaussian_fin (Matrix.reindex e e M)
    (by rwa [Matrix.det_reindex_self]) (b ∘ e.symm) (fun j => hb _)
  have h' := (e.arrowCongr (Equiv.refl ℤ)).summable_iff.mpr h
  refine h'.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [← gaussAt_reindex e]
  rfl

/-- **Poisson summation for a diagonal complex Gaussian** (theta inversion with one complex rate per
coordinate). Let $J$ be finite, $b \in \mathbb{C}^J$ with $\operatorname{Re} b_j > 0$, and $M, M'$ real $J\times J$ matrices
with $M^{\mathsf T}M' = 1$. Then
$$\sum_{\vec{k}\in\mathbb{Z}^J}e^{-\pi\sum_jb_j(M\vec{k})_j^2}
  = |\det M|^{-1}\prod_j(b_j^{-1})^{1/2}\sum_{\vec{m}\in\mathbb{Z}^J}e^{-\pi\sum_jb_j^{-1}(M'\vec{m})_j^2},$$
with `Complex.cpow` (principal branch) for $(b_j^{-1})^{1/2}$. Both sides converge absolutely
(`summable_norm_gaussAt`). For $b_j = w$ constant and $M = S^{1/2}$ this is
`QuadFormsKB.Analysis.tsum_gaussian_quadratic`. -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem tsum_gaussAt (M M' : Matrix J J ℝ) (hMM : Mᵀ * M' = 1) (b : J → ℂ)
    (hb : ∀ j, 0 < (b j).re) :
    ∑' k : J → ℤ, gaussAt b M k =
      ((|M.det|)⁻¹ : ℝ) * (∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ)) * ∑' m : J → ℤ, gaussAt (fun j => (b j)⁻¹) M' m := by
  set e := Fintype.equivFin J
  have hMM' : (Matrix.reindex e e M)ᵀ * Matrix.reindex e e M' = 1 := by
    rw [Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, hMM, Matrix.submatrix_one_equiv]
  have h := tsum_diagGaussian_fin (Matrix.reindex e e M) (Matrix.reindex e e M') hMM'
    (b ∘ e.symm) (fun j => hb _)
  rw [← (e.arrowCongr (Equiv.refl ℤ)).tsum_eq, ← (e.arrowCongr (Equiv.refl ℤ)).tsum_eq] at h
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp] at h
  rw [Matrix.det_reindex_self] at h
  have hp : ∏ j, ((b ∘ e.symm) j)⁻¹ ^ (1 / 2 : ℂ) = ∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ) :=
    e.symm.prod_comp (fun j => (b j)⁻¹ ^ (1 / 2 : ℂ))
  rw [hp] at h
  convert h using 3
  · exact (gaussAt_reindex e b M _).symm
  · funext m
    rw [← gaussAt_reindex e (fun j => (b j)⁻¹) M' m]
    rfl

/-- The value $G_b(M(\vec{k} + \vec{h}))$ at a shifted integer vector, $\vec{h} \in \mathbb{R}^J$. -/
abbrev gaussAtShift (b : J → ℂ) (M : Matrix J J ℝ) (h : J → ℝ) (k : J → ℤ) : ℂ :=
  cexp (-Real.pi * ∑ j, b j * (((M *ᵥ fun i => (k i : ℝ) + h i) j : ℝ) : ℂ) ^ 2)

/-- **Shifted Poisson summation for a diagonal complex Gaussian** (theta with characteristics). With the
hypotheses of `tsum_gaussAt` and $\vec{h} \in \mathbb{R}^J$:
$$\sum_{\vec{k}\in\mathbb{Z}^J}G_b(M(\vec{k}+\vec{h})) = |\det M|^{-1}\prod_j(b_j^{-1})^{1/2}
  \sum_{\vec{m}\in\mathbb{Z}^J}G_{b^{-1}}(M'\vec{m})\,e(\vec{m}\cdot\vec{h}).$$ -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem tsum_gaussAtShift (M M' : Matrix J J ℝ) (hMM : Mᵀ * M' = 1) (b : J → ℂ)
    (hb : ∀ j, 0 < (b j).re) (h : J → ℝ) :
    ∑' k : J → ℤ, gaussAtShift b M h k =
      ((|M.det|)⁻¹ : ℝ) * (∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ)) *
        ∑' m : J → ℤ, gaussAt (fun j => (b j)⁻¹) M' m *
          cexp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * h i : ℝ) : ℂ)) := by
  set e := Fintype.equivFin J
  have hMM' : (Matrix.reindex e e M)ᵀ * Matrix.reindex e e M' = 1 := by
    rw [Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, hMM, Matrix.submatrix_one_equiv]
  have hh := tsum_diagGaussian_shift_fin (Matrix.reindex e e M) (Matrix.reindex e e M') hMM'
    (b ∘ e.symm) (fun j => hb _) (h ∘ e.symm)
  rw [← (e.arrowCongr (Equiv.refl ℤ)).tsum_eq, ← (e.arrowCongr (Equiv.refl ℤ)).tsum_eq] at hh
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp] at hh
  rw [Matrix.det_reindex_self] at hh
  have hp : ∏ j, ((b ∘ e.symm) j)⁻¹ ^ (1 / 2 : ℂ) = ∏ j, (b j)⁻¹ ^ (1 / 2 : ℂ) :=
    e.symm.prod_comp (fun j => (b j)⁻¹ ^ (1 / 2 : ℂ))
  rw [hp] at hh
  convert hh using 3
  · rename_i k
    have hv : ((Matrix.reindex e e M) *ᵥ fun i => ((k ∘ e.symm) i : ℝ) + (h ∘ e.symm) i) =
        (M *ᵥ fun i => (k i : ℝ) + h i) ∘ e.symm := by
      rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
      congr 2
      funext i
      simp
    rw [hv, gaussAtShift]
    congr 2
    exact (e.symm.sum_comp (fun j => b j * (((M *ᵥ fun i => (k i : ℝ) + h i) j : ℝ) : ℂ) ^ 2)).symm
  · funext m
    rw [← gaussAt_reindex e (fun j => (b j)⁻¹) M' m]
    congr 3
    exact_mod_cast (e.symm.sum_comp (fun i => (m i : ℝ) * h i)).symm

end General

end

end QuadFormsKB.HilbertModular
