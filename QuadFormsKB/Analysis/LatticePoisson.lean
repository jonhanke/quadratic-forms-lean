import QuadFormsKB.Analysis.SPLPoisson.General
import QuadFormsKB.Analysis.GaussianSchwartz
import QuadFormsKB.Citation

/-!
# Poisson summation for lattices, and for Gaussian quadratic forms

Throughout, $E = \mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with the standard inner product, Lebesgue measure,
and Mathlib's Fourier transform
$$\hat f(\xi) = \mathcal{F}f(\xi) = \int_E f(\vec{x})\, e^{-2\pi i \langle \vec{x}, \xi\rangle}\, d\vec{x}.$$

* `latticePoisson`: for a full-rank lattice $\Lambda \subset E$, a Schwartz function $f$ and $\vec{v} \in E$,
  $$\sum_{\lambda \in \Lambda} f(\vec{v} + \lambda) = \frac{1}{\operatorname{covol}(\Lambda)}
    \sum_{\mu \in \Lambda^*} \hat f(\mu)\, e^{2\pi i \langle \vec{v}, \mu\rangle},
    \qquad \Lambda^* = \{\mu : \langle \mu, \Lambda\rangle \subseteq \mathbb{Z}\}.$$
  The proof is vendored from Sphere-Packing-Lean (`QuadFormsKB/Analysis/SPLPoisson/`, Apache-2.0).
* `latticePoisson_zero`: the case $\vec{v} = 0$.
* `tsum_gaussian_quadratic`: the **theta inversion formula** for a real positive definite matrix $S$ and
  $\operatorname{Re} w > 0$,
  $$\sum_{\vec{x} \in \mathbb{Z}^n} e^{-\pi w\, \vec{x}^{\mathsf T} S \vec{x}}
    = (\det S)^{-1/2}\, (w^{-1})^{n/2} \sum_{\vec{y} \in \mathbb{Z}^n} e^{-\pi w^{-1}\, \vec{y}^{\mathsf T} S^{-1} \vec{y}},$$
  with the principal branch of $(w^{-1})^{n/2}$ (`Complex.cpow`; $w^{-1}$ lies in the right half plane).
  Here $\vec{x}^{\mathsf T} S \vec{x}$ is `quadAt S x`. The series converges absolutely
  (`summable_norm_gaussian_quadratic`), via `summable_norm_intPt` for Schwartz functions.

Sources: Stein–Shakarchi, *Fourier Analysis*, Ch. 5 Thm. 3.1 and Ch. 6 (Poisson summation) [unverified];
Serre, *A Course in Arithmetic*, Ch. VII §6.1–6.2 (Poisson formula, theta of a lattice) [unverified].
-/

open MeasureTheory Complex Matrix
open scoped FourierTransform RealInnerProductSpace

namespace QuadFormsKB.Analysis

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- **Poisson summation for a full-rank lattice** $\Lambda \subset \mathbb{R}^n$ (Euclidean inner product):
for a Schwartz function $f$ and $\vec{v} \in \mathbb{R}^n$,
$$\sum_{\lambda \in \Lambda} f(\vec{v} + \lambda) = \operatorname{covol}(\Lambda)^{-1}
  \sum_{\mu \in \Lambda^*} \hat f(\mu)\, e^{2\pi i \langle \vec{v}, \mu\rangle}.$$
Here $\Lambda$ is a `Submodule ℤ` with `DiscreteTopology` and `IsZLattice ℝ` (discrete, spanning),
$\operatorname{covol}$ is `ZLattice.covolume` for Lebesgue measure, $\Lambda^*$ is the dual lattice
`SchwartzMap.dualLattice` (for the inner product), and $\hat f = \mathcal{F} f$ is Mathlib's Fourier transform
with kernel $e^{-2\pi i\langle \vec{x}, \xi\rangle}$. Both sums converge absolutely.

*Proof:* Sphere-Packing-Lean's `SchwartzMap.poissonSummation_lattice` (vendored and ported, see
`QuadFormsKB/Analysis/SPLPoisson/General.lean`). -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem latticePoisson (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (f : SchwartzMap E ℂ) (v : E) :
    (∑' ℓ : Λ, f (v + (ℓ : E))) =
      (1 / ZLattice.covolume Λ) *
        ∑' m : SchwartzMap.dualLattice (d := n) Λ,
          (𝓕 (fun x : E => f x) m) * Complex.exp (2 * Real.pi * Complex.I * ⟪v, (m : E)⟫) := by
  have h := SchwartzMap.poissonSummation_lattice Λ f v
  simp only [← RCLike.inner_eq_wInner_one] at h
  exact h

/-- **Poisson summation at $\vec{v} = 0$:**
$\sum_{\lambda \in \Lambda} f(\lambda) = \operatorname{covol}(\Lambda)^{-1}\sum_{\mu \in \Lambda^*} \hat f(\mu)$. -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem latticePoisson_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (f : SchwartzMap E ℂ) :
    (∑' ℓ : Λ, f (ℓ : E)) =
      (1 / ZLattice.covolume Λ) *
        ∑' m : SchwartzMap.dualLattice (d := n) Λ, 𝓕 (fun x : E => f x) m := by
  simpa using latticePoisson Λ f 0

/-- The integer vector $\vec{k} \in \mathbb{Z}^n$ as a point of $E = \mathbb{R}^n$. -/
abbrev intPt (k : Fin n → ℤ) : E := SchwartzMap.PoissonSummation.Standard.intVec (d := n) k

/-- **Poisson summation over $\mathbb{Z}^n$** at $\vec{v} = 0$:
$\sum_{\vec{k} \in \mathbb{Z}^n} f(\vec{k}) = \sum_{\vec{k} \in \mathbb{Z}^n} \hat f(\vec{k})$. -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem intPoisson (f : SchwartzMap E ℂ) :
    (∑' k : Fin n → ℤ, f (intPt k)) = ∑' k : Fin n → ℤ, 𝓕 (fun x : E => f x) (intPt k) := by
  have h := SchwartzMap.PoissonSummation.Standard.poissonSummation_standard (d := n) f 0
  rw [← (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := n)).tsum_eq] at h
  simpa using h

/-! ### The Gaussian of a positive definite matrix -/

open scoped MatrixOrder

/-- The square root $B = S^{1/2}$ (continuous functional calculus) of a positive definite real matrix
is symmetric with $B B = S$. -/
private lemma sqrt_spec {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    (CFC.sqrt S)ᵀ = CFC.sqrt S ∧ CFC.sqrt S * CFC.sqrt S = S := by
  have h0 : 0 ≤ S := (nonneg_iff_posSemidef).2 hS.posSemidef
  have hsa : IsSelfAdjoint (CFC.sqrt S) := (CFC.sqrt_nonneg S).isSelfAdjoint
  refine ⟨?_, CFC.sqrt_mul_sqrt_self S h0⟩
  simpa [Matrix.star_eq_conjTranspose] using hsa.star_eq

/-- The real vector $\vec{k} \in \mathbb{R}^n$ underlying an integer vector. -/
private abbrev castVec (k : Fin n → ℤ) : Fin n → ℝ := fun i => (k i : ℝ)

/-- $\|M\vec{x}\|^2 = \vec{x}^{\mathsf T} M^{\mathsf T} M \vec{x}$ in $E$. -/
private lemma norm_sq_toEuclideanLin (M : Matrix (Fin n) (Fin n) ℝ) (x : E) :
    ‖Matrix.toEuclideanLin M x‖ ^ 2 = x.ofLp ⬝ᵥ ((Mᵀ * M) *ᵥ x.ofLp) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.toLpLin_apply, dotProduct, sq]

/-- The value $\vec{x}^{\mathsf T} S\, \vec{x} \in \mathbb{R}$ of a real matrix at an integer vector. -/
abbrev quadAt (S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℤ) : ℝ :=
  (fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (x i : ℝ))

private lemma sqrt_det_ne_zero {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    (CFC.sqrt S).det ≠ 0 := by
  obtain ⟨-, hBB⟩ := sqrt_spec hS
  intro h
  have := hS.det_pos
  rw [← hBB, det_mul, h, zero_mul] at this
  exact lt_irrefl _ this

/-- The linear automorphism $\vec{v} \mapsto S^{1/2}\vec{v}$ of $E$. -/
private def sqrtEquiv {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofLinearMap (Matrix.toEuclideanLin (CFC.sqrt S)) (Matrix.toEuclideanLin (CFC.sqrt S)⁻¹)
    (by rw [← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (sqrt_det_ne_zero hS)), Matrix.toLpLin_one])
    (by rw [← Matrix.toLpLin_mul_same,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (sqrt_det_ne_zero hS)), Matrix.toLpLin_one])

private lemma pi_mul_re_pos {w : ℂ} (hw : 0 < w.re) : 0 < ((Real.pi : ℂ) * w).re := by
  simpa [Complex.mul_re] using mul_pos Real.pi_pos hw

/-- **The Gaussian of $S$** as a Schwartz function: $\vec{v} \mapsto e^{-\pi w \|S^{1/2}\vec{v}\|^2}$, so that
its value at $\vec{x} \in \mathbb{Z}^n$ is $e^{-\pi w\, \vec{x}^{\mathsf T} S \vec{x}}$ (`quadGaussian_intPt`). -/
def quadGaussian {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ} (hw : 0 < w.re) :
    SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (sqrtEquiv hS).toContinuousLinearEquiv
    (gaussianSchwartz ((Real.pi : ℂ) * w) (pi_mul_re_pos hw))

private lemma intPt_ofLp (k : Fin n → ℤ) : (intPt k).ofLp = fun i => (k i : ℝ) := by
  ext i; simp [intPt]

theorem quadGaussian_intPt {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ} (hw : 0 < w.re)
    (k : Fin n → ℤ) :
    quadGaussian hS hw (intPt k) = cexp (-Real.pi * w * (quadAt S k : ℂ)) := by
  obtain ⟨hBt, hBB⟩ := sqrt_spec hS
  have : quadGaussian hS hw (intPt k) =
      gaussianSchwartz ((Real.pi : ℂ) * w) (pi_mul_re_pos hw)
        (Matrix.toEuclideanLin (CFC.sqrt S) (intPt k)) := rfl
  rw [this, gaussianSchwartz_apply, norm_sq_toEuclideanLin, hBt, hBB, intPt_ofLp]
  ring_nf

/-- A Schwartz function is absolutely summable over $\mathbb{Z}^n$. -/
theorem summable_norm_intPt (f : SchwartzMap E ℂ) : Summable fun k : Fin n → ℤ => ‖f (intPt k)‖ := by
  let K : TopologicalSpace.Compacts E := ⟨{0}, isCompact_singleton⟩
  have h := SchwartzMap.PoissonSummation.Standard.summable_norm_translate_restrict (d := n) f K
  have h' := (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := n)).summable_iff.mpr h
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) h'
  have := ContinuousMap.norm_coe_le_norm
    ((SchwartzMap.PoissonSummation.Standard.translate (d := n) f
      (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := n) k)).restrict K) ⟨0, rfl⟩
  have e : ((SchwartzMap.PoissonSummation.Standard.translate (d := n) f
      (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := n) k)).restrict K) ⟨0, rfl⟩ =
      f (intPt k) := by
    change f (0 + _) = _
    rw [zero_add]; rfl
  rw [e] at this
  exact this

/-- **Absolute convergence** of $\sum_{\vec{x} \in \mathbb{Z}^n} e^{-\pi w\, \vec{x}^{\mathsf T} S \vec{x}}$ for $S$
positive definite and $\operatorname{Re} w > 0$. -/
theorem summable_norm_gaussian_quadratic {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ}
    (hw : 0 < w.re) :
    Summable fun x : Fin n → ℤ => ‖cexp (-Real.pi * w * (quadAt S x : ℂ))‖ := by
  simpa [quadGaussian_intPt hS hw] using summable_norm_intPt (quadGaussian hS hw)

/-- **Theta inversion (Poisson summation for a Gaussian quadratic form).** Let $S$ be a real symmetric
positive definite $n \times n$ matrix (`Matrix.PosDef`) and $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$. Then
$$\sum_{\vec{x} \in \mathbb{Z}^n} e^{-\pi w\, \vec{x}^{\mathsf T} S \vec{x}}
  = \frac{(w^{-1})^{n/2}}{\sqrt{\det S}} \sum_{\vec{y} \in \mathbb{Z}^n} e^{-\pi w^{-1}\, \vec{y}^{\mathsf T} S^{-1} \vec{y}},$$
where $(w^{-1})^{n/2}$ is `Complex.cpow` (principal branch; $w^{-1}$ has positive real part, so this is the
branch that is positive on $(0, \infty)$), and $\sqrt{\det S} > 0$. Both series converge absolutely.

*Proof.* Write $S = B^{\mathsf T}B$ with $B = S^{1/2}$, apply Poisson summation over $\mathbb{Z}^n$ (`intPoisson`) to
$f(\vec{v}) = e^{-\pi w\|B\vec{v}\|^2}$, use $\widehat{f\circ B}(\xi) = |\det B|^{-1}\hat f(B^{-\mathsf T}\xi)$
(Sphere-Packing-Lean's `fourier_comp_linearEquiv`) and Mathlib's Fourier transform of the Gaussian
(`fourier_gaussian_innerProductSpace`). -/
@[kb "serre1973" "Ch. VII §6.2, theta of a lattice [unverified]"]
theorem tsum_gaussian_quadratic {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ}
    (hw : 0 < w.re) :
    ∑' x : Fin n → ℤ, cexp (-Real.pi * w * (quadAt S x : ℂ)) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2) *
        ∑' y : Fin n → ℤ, cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ y : ℂ)) := by
  obtain ⟨hBt, hBB⟩ := sqrt_spec hS
  set B := CFC.sqrt S with hBdef
  have hdetS : S.det = B.det * B.det := by rw [← hBB, det_mul]
  have hb := pi_mul_re_pos hw
  let L : E ≃ₗ[ℝ] E := sqrtEquiv hS
  let g : SchwartzMap E ℂ := gaussianSchwartz ((Real.pi : ℂ) * w) hb
  have hP := intPoisson (quadGaussian hS hw)
  have hdetL : LinearMap.det (L : E →ₗ[ℝ] E) = B.det := by
    change LinearMap.det (Matrix.toEuclideanLin B) = B.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hadj : ((L.symm : E ≃ₗ[ℝ] E).toLinearMap).adjoint = Matrix.toEuclideanLin B⁻¹ := by
    change (Matrix.toEuclideanLin B⁻¹).adjoint = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_nonsing_inv, hBt]
  have hSinv : (B⁻¹)ᵀ * B⁻¹ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hBt, ← Matrix.mul_inv_rev, hBB]
  have hrhs : ∀ k : Fin n → ℤ, 𝓕 (fun x : E => quadGaussian hS hw x) (intPt k) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2) *
        cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ k : ℂ)) := by
    intro k
    have h1 := SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv L (fun x : E => g x) (intPt k)
    have h2 := fourier_gaussian_innerProductSpace (V := E) hb
      (((L.symm : E ≃ₗ[ℝ] E).toLinearMap).adjoint (intPt k))
    have hfx : (fun x : E => quadGaussian hS hw x) = fun x => g (L x) := rfl
    rw [hfx, h1]
    have hg : (fun x : E => g x) = fun v : E => cexp (-((Real.pi : ℂ) * w) * ‖v‖ ^ 2) := by
      funext v; simp [g]
    rw [hg, h2, hadj]
    have hn : ((n : ℂ) / 2) = ((Module.finrank ℝ E : ℕ) : ℂ) / 2 := by simp
    rw [← hn]
    have hnorm : (‖Matrix.toEuclideanLin B⁻¹ (intPt k)‖ : ℂ) ^ 2 = (quadAt S⁻¹ k : ℂ) := by
      rw [← Complex.ofReal_pow, norm_sq_toEuclideanLin, hSinv, intPt_ofLp]
    rw [hnorm, hdetL, hdetS, Real.sqrt_mul_self_eq_abs]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [Complex.real_smul]
    have e1 : (Real.pi : ℂ) / ((Real.pi : ℂ) * w) = w⁻¹ := by field_simp
    rw [e1]
    have e2 : -(Real.pi : ℂ) ^ 2 * (quadAt S⁻¹ k : ℂ) / ((Real.pi : ℂ) * w) =
        -Real.pi * w⁻¹ * (quadAt S⁻¹ k : ℂ) := by
      field_simp
    rw [e2]
    push_cast
    ring
  simp_rw [quadGaussian_intPt hS hw, hrhs] at hP
  rw [hP, tsum_mul_left]

/-! ### Shifted Gaussian sums (theta series with characteristics) -/

/-- The value $\vec{v}^{\mathsf T} S\, \vec{v} \in \mathbb{R}$ of a real matrix at a real vector. -/
abbrev quadAtR (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ := v ⬝ᵥ S *ᵥ v

/-- Value of the Gaussian `quadGaussian` at an arbitrary point $\vec{v}$: $e^{-\pi w\, \vec{v}^{\mathsf T} S \vec{v}}$. -/
theorem quadGaussian_apply {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ} (hw : 0 < w.re)
    (v : E) : quadGaussian hS hw v = cexp (-Real.pi * w * (quadAtR S v.ofLp : ℂ)) := by
  obtain ⟨hBt, hBB⟩ := sqrt_spec hS
  have : quadGaussian hS hw v =
      gaussianSchwartz ((Real.pi : ℂ) * w) (pi_mul_re_pos hw)
        (Matrix.toEuclideanLin (CFC.sqrt S) v) := rfl
  rw [this, gaussianSchwartz_apply, norm_sq_toEuclideanLin, hBt, hBB]
  ring_nf

/-- **Shifted theta inversion (Poisson summation for a shifted Gaussian quadratic form).** Let $S$ be a real
symmetric positive definite $n \times n$ matrix, $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$, and
$\vec{h} \in \mathbb{R}^n$. Then
$$\sum_{\vec{x} \in \mathbb{Z}^n} e^{-\pi w\, (\vec{x}+\vec{h})^{\mathsf T} S (\vec{x}+\vec{h})}
  = \frac{(w^{-1})^{n/2}}{\sqrt{\det S}} \sum_{\vec{y} \in \mathbb{Z}^n}
    e^{-\pi w^{-1}\, \vec{y}^{\mathsf T} S^{-1} \vec{y}}\, e^{2\pi i\, \vec{y}\cdot\vec{h}},$$
with the principal branch of $(w^{-1})^{n/2}$ (`Complex.cpow`). The case $\vec{h} = 0$ is `tsum_gaussian_quadratic`.

*Proof:* as for `tsum_gaussian_quadratic`, with Poisson summation at the shift $\vec{h}$
(`SchwartzMap.PoissonSummation.Standard.poissonSummation_standard`). -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem tsum_gaussian_quadratic_shift {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ}
    (hw : 0 < w.re) (h : Fin n → ℝ) :
    ∑' x : Fin n → ℤ, cexp (-Real.pi * w * (quadAtR S (fun i => (x i : ℝ) + h i) : ℂ)) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2) *
        ∑' y : Fin n → ℤ, cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ y : ℂ)) *
          cexp (2 * Real.pi * I * ((∑ i, (y i : ℝ) * h i : ℝ) : ℂ)) := by
  obtain ⟨hBt, hBB⟩ := sqrt_spec hS
  set B := CFC.sqrt S with hBdef
  have hdetS : S.det = B.det * B.det := by rw [← hBB, det_mul]
  have hb := pi_mul_re_pos hw
  let L : E ≃ₗ[ℝ] E := sqrtEquiv hS
  let g : SchwartzMap E ℂ := gaussianSchwartz ((Real.pi : ℂ) * w) hb
  set v : E := WithLp.toLp 2 h with hv
  have hP := SchwartzMap.PoissonSummation.Standard.poissonSummation_standard (d := n)
    (quadGaussian hS hw) v
  rw [← (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := n)).tsum_eq] at hP
  have hdetL : LinearMap.det (L : E →ₗ[ℝ] E) = B.det := by
    change LinearMap.det (Matrix.toEuclideanLin B) = B.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hadj : ((L.symm : E ≃ₗ[ℝ] E).toLinearMap).adjoint = Matrix.toEuclideanLin B⁻¹ := by
    change (Matrix.toEuclideanLin B⁻¹).adjoint = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_nonsing_inv, hBt]
  have hSinv : (B⁻¹)ᵀ * B⁻¹ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hBt, ← Matrix.mul_inv_rev, hBB]
  have hrhs : ∀ k : Fin n → ℤ, 𝓕 (fun x : E => quadGaussian hS hw x) (intPt k) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2) *
        cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ k : ℂ)) := by
    intro k
    have h1 := SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv L (fun x : E => g x) (intPt k)
    have h2 := fourier_gaussian_innerProductSpace (V := E) hb
      (((L.symm : E ≃ₗ[ℝ] E).toLinearMap).adjoint (intPt k))
    have hfx : (fun x : E => quadGaussian hS hw x) = fun x => g (L x) := rfl
    rw [hfx, h1]
    have hg : (fun x : E => g x) = fun v : E => cexp (-((Real.pi : ℂ) * w) * ‖v‖ ^ 2) := by
      funext v; simp [g]
    rw [hg, h2, hadj]
    have hn : ((n : ℂ) / 2) = ((Module.finrank ℝ E : ℕ) : ℂ) / 2 := by simp
    rw [← hn]
    have hnorm : (‖Matrix.toEuclideanLin B⁻¹ (intPt k)‖ : ℂ) ^ 2 = (quadAt S⁻¹ k : ℂ) := by
      rw [← Complex.ofReal_pow, norm_sq_toEuclideanLin, hSinv, intPt_ofLp]
    rw [hnorm, hdetL, hdetS, Real.sqrt_mul_self_eq_abs]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [Complex.real_smul]
    have e1 : (Real.pi : ℂ) / ((Real.pi : ℂ) * w) = w⁻¹ := by field_simp
    rw [e1]
    have e2 : -(Real.pi : ℂ) ^ 2 * (quadAt S⁻¹ k : ℂ) / ((Real.pi : ℂ) * w) =
        -Real.pi * w⁻¹ * (quadAt S⁻¹ k : ℂ) := by
      field_simp
    rw [e2]
    push_cast
    ring
  have hl : ∀ k : Fin n → ℤ, quadGaussian hS hw
      (v + ((SchwartzMap.PoissonSummation.Standard.equivIntVec (d := n) k :
        SchwartzMap.standardLattice n) : E)) =
      cexp (-Real.pi * w * (quadAtR S (fun i => (k i : ℝ) + h i) : ℂ)) := by
    intro k
    rw [quadGaussian_apply]
    congr 4
    ext i
    simp [hv, SchwartzMap.PoissonSummation.Standard.intVec, add_comm]
  have hinner : ∀ k : Fin n → ℤ,
      ⟪v, SchwartzMap.PoissonSummation.Standard.intVec (d := n) k⟫_[ℝ] = ∑ i, (k i : ℝ) * h i := by
    intro k
    rw [← RCLike.inner_eq_wInner_one]
    simp [hv, SchwartzMap.PoissonSummation.Standard.intVec, PiLp.inner_apply, mul_comm]
  simp_rw [hl] at hP
  rw [hP, ← tsum_mul_left]
  congr 1; funext k
  rw [show SchwartzMap.PoissonSummation.Standard.intVec (d := n) k = intPt k from rfl, hrhs,
    ← show SchwartzMap.PoissonSummation.Standard.intVec (d := n) k = intPt k from rfl, hinner]
  ring

end

end QuadFormsKB.Analysis
