import QuadFormsKB.Analysis.MinkowskiPoisson
import QuadFormsKB.Tamagawa.Measure.Weil.BasisPoisson

open IsDedekindDomain NumberField MeasureTheory NumberField.InfinitePlace
open NumberField.mixedEmbedding
open scoped Real FourierTransform nonZeroDivisors Classical

/-!
# Poisson summation over a product of fractional ideals in $F_\infty^n$

The $n$-variable form of `poisson_fractionalIdeal` (`Analysis/MinkowskiPoisson.lean`), for the lattice
$I_0\times\dots\times I_{n-1} \subset F^n$ of a family of nonzero fractional ideals of a number field $F$, embedded in
$F_\infty^n$, $F_\infty = F\otimes_{\mathbb{Q}}\mathbb{R}$ the mixed (Minkowski) space.

* `fourierInfPi`: $\hat f(z) = \int_{F_\infty^n} f(y)\,e\big(\sum_{i<n}\operatorname{Tr}_\infty(y_iz_i)\big)\,dy$, the
  product of the self-dual measures `selfDualInf`.
* **`poisson_fractionalIdeal_pi`**: for a Schwartz function $f$ on $F_\infty^n$ and $\xi \in F^n$,
  $$\sum_{x\in\prod_i I_i} f(\xi+x) = \prod_{i<n}\big(2^{r_2}\operatorname{covol}(I_i)\big)^{-1}
    \sum_{\mu\in\prod_i I_i^\vee}\hat f(\mu)\,e\Big(-\sum_{i<n}\operatorname{Tr}_{F/\mathbb{Q}}(\xi_i\mu_i)\Big),$$
  $I_i^\vee$ = `FractionalIdeal.dual ℤ ℚ (I i)` the trace dual; both sides converge absolutely
  (`summable_poisson_pi_lhs`, `summable_poisson_pi_rhs`).
* `exists_schwartz_fourierInfPi`: $\hat f$ is again a Schwartz function on $F_\infty^n$ (from the generic
  `exists_schwartz_fourier_basis`: $z \mapsto \int_W f(y)\,e(\beta(y,z))\,d\mu(y)$ is Schwartz for every basis with a
  $\beta$-dual family).

*Proof.* The generic `poisson_basis` (`Tamagawa/Measure/Weil/BasisPoisson.lean`) for the basis `piB` of $F_\infty^n$
made of the $\mathbb{Z}$-bases of the $I_i$ placed in coordinate $i$, the pairing
$\beta(y, z) = \sum_i\operatorname{Tr}_\infty(y_iz_i)$ (`betaPi`) and the $\beta$-dual family `piBd` of trace-dual
bases; the parallelepiped of `piB` is the product of the parallelepipeds of the $I_i$
(`parallelepiped_piB`, `measure_parallelepiped_piB`).

This is the first step towards $\omega(w)$ on non-factorizable archimedean data. Sources: as for `poisson_fractionalIdeal` (Cassels–Fröhlich Ch. XV, §4.2,
Lemma 4.2.4, p. 333).
-/

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "V" => mixedSpace F
local notation "d" => Module.finrank ℚ F

instance : (selfDualInf (F := F)).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.nnreal_smul _ (pow_ne_zero _ two_ne_zero)

instance : SigmaFinite (selfDualInf (F := F)) := by
  unfold selfDualInf; infer_instance

instance : MeasurableAdd V := ContinuousAdd.measurableAdd

instance : BorelSpace (Fin n → V) := Pi.borelSpace

lemma traceInf_zero : traceInf (0 : V) = 0 := by simpa using traceInf_smul (F := F) 0 0

example : (Measure.pi fun _ : Fin n => (selfDualInf (F := F))).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

/-- The pairing $\beta(y, z) = \sum_i \operatorname{Tr}_\infty(y_i z_i)$ on $F_\infty^n$. -/
def betaPi : (Fin n → V) →ₗ[ℝ] (Fin n → V) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y z => ∑ i, traceInf (y i * z i))
    (fun y y' z => by simp [add_mul, traceInf_add, Finset.sum_add_distrib])
    (fun c y z => by simp [traceInf_smul, Finset.mul_sum])
    (fun y z z' => by simp [mul_add, traceInf_add, Finset.sum_add_distrib])
    (fun c y z => by simp [traceInf_smul, Finset.mul_sum])

lemma betaPi_apply (y z : Fin n → V) : betaPi y z = ∑ i, traceInf (y i * z i) := rfl

/-- $\Sigma_{i<n}\{0,\dots,d-1\} \cong \{0,\dots,nd-1\}$. -/
def sigE (n : ℕ) (k : ℕ) : (Σ _ : Fin n, Fin k) ≃ Fin (n * k) :=
  (Equiv.sigmaEquivProd (Fin n) (Fin k)).trans finProdFinEquiv

variable (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-- The basis of $F_\infty^n$ made of the bases `bR (I i)` placed in coordinate $i$. -/
def piB : Module.Basis (Fin (n * d)) ℝ (Fin n → V) :=
  (Pi.basis fun i => bR (I i)).reindex (sigE n d)

lemma piB_sigE (i : Fin n) (j : Fin d) : piB I (sigE n d ⟨i, j⟩) = Pi.single i (bR (I i) j) := by
  simp [piB]

/-- The $\beta$-dual family: the trace-dual bases placed in coordinate $i$. -/
def piBd (k : Fin (n * d)) : Fin n → V :=
  Pi.single ((sigE n d).symm k).1 (mixedEmbedding F ((bq (I ((sigE n d).symm k).1)).traceDual
    ((sigE n d).symm k).2))

lemma betaPi_single (i i' : Fin n) (u w : V) :
    betaPi (Pi.single i u) (Pi.single i' w) = if i = i' then traceInf (u * w) else 0 := by
  rw [betaPi_apply]
  by_cases h : i = i'
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb, traceInf_zero]
    · simp
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = i
    · subst hb; simp [Pi.single_eq_of_ne h, traceInf_zero]
    · simp [Pi.single_eq_of_ne hb, traceInf_zero]

lemma piB_dual (k l : Fin (n * d)) : betaPi (piB I k) (piBd I l) = if k = l then 1 else 0 := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (sigE n d).surjective k
  obtain ⟨⟨i', j'⟩, rfl⟩ := (sigE n d).surjective l
  rw [piB_sigE, piBd, Equiv.symm_apply_apply, betaPi_single]
  simp only [(sigE n d).apply_eq_iff_eq, Sigma.mk.injEq]
  by_cases h : i = i'
  · subst h
    simp only [↓reduceIte]
    rw [bR_apply, ← map_mul, traceInf_mixedEmbedding, Module.Basis.trace_mul_traceDual]
    simp only [heq_eq_eq, true_and]
    split_ifs <;> simp
  · simp [h]

lemma piBd_sigE (i : Fin n) (j : Fin d) :
    piBd I (sigE n d ⟨i, j⟩) = Pi.single i (mixedEmbedding F ((bq (I i)).traceDual j)) := by
  simp [piBd]

lemma sum_piB (k : Fin (n * d) → ℤ) :
    ∑ l, (k l : ℝ) • piB I l = fun i => mixedEmbedding F (latElt (I i) fun j => k (sigE n d ⟨i, j⟩)) := by
  funext i
  rw [← (sigE n d).sum_comp, Fintype.sum_sigma, Finset.sum_apply]
  rw [Finset.sum_eq_single i (fun a _ ha => by
    simp [Finset.sum_apply, piB_sigE, Pi.single_eq_of_ne' ha]) (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, piB_sigE, Pi.single_eq_same, latElt, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bR_apply, map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

lemma sum_piBd (m : Fin (n * d) → ℤ) :
    ∑ l, (m l : ℝ) • piBd I l = fun i => mixedEmbedding F (dualElt (I i) fun j => m (sigE n d ⟨i, j⟩)) := by
  funext i
  rw [← (sigE n d).sum_comp, Fintype.sum_sigma, Finset.sum_apply]
  rw [Finset.sum_eq_single i (fun a _ ha => by
    simp [Finset.sum_apply, piBd_sigE, Pi.single_eq_of_ne' ha]) (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, piBd_sigE, Pi.single_eq_same, dualElt, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

lemma parallelepiped_piB :
    ((piB I).parallelepiped : Set (Fin n → V)) =
      Set.univ.pi fun i => ((bR (I i)).parallelepiped : Set V) := by
  ext x
  simp only [Module.Basis.coe_parallelepiped, parallelepiped_basis_eq, Set.mem_ofPred_eq, Set.mem_pi,
    Set.mem_univ, true_imp_iff]
  constructor
  · intro h i j
    have := h (sigE n d ⟨i, j⟩)
    simpa [piB] using this
  · intro h l
    obtain ⟨⟨i, j⟩, rfl⟩ := (sigE n d).surjective l
    simpa [piB] using h i j

lemma volume_parallelepiped_bR (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (volume : Measure V) ((bR J).parallelepiped : Set V) =
      ENNReal.ofReal (ZLattice.covolume (idealLattice F J)) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice F J),
    measureReal_def, ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne,
    Module.Basis.coe_parallelepiped,
    ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (bR J) volume), bR,
    ZSpan.fundamentalDomain_reindex]

lemma measure_parallelepiped_piB :
    ((Measure.pi fun _ : Fin n => (selfDualInf (F := F))) (piB I).parallelepiped).toReal =
      ∏ i, ((2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F (I i))) := by
  rw [parallelepiped_piB, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [selfDualInf, Measure.smul_apply, volume_parallelepiped_bR, ENNReal.smul_def, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (ZLattice.covolume_pos _ _).le]
  simp

/-- $\mathbb{Z}^{nd} \cong \prod_i I_i$, $k \mapsto \big(\sum_j k_{(i,j)} b_{i,j}\big)_i$. -/
def latPi : (Fin (n * d) → ℤ) ≃ ((i : Fin n) → ((I i : FractionalIdeal (𝓞 F)⁰ F) : Set F)) :=
  (Equiv.arrowCongr (sigE n d).symm (Equiv.refl ℤ)).trans
    ((Equiv.piCurry fun (_ : Fin n) (_ : Fin d) => ℤ).trans (Equiv.piCongrRight fun i => latEquiv (I i)))

lemma latPi_coe (k : Fin (n * d) → ℤ) (i : Fin n) :
    (latPi I k i : F) = latElt (I i) fun j => k (sigE n d ⟨i, j⟩) := by
  rw [← latEquiv_coe]
  rfl

/-- $\mathbb{Z}^{nd} \cong \prod_i I_i^\vee$, $m \mapsto \big(\sum_j m_{(i,j)} b_{i,j}^\vee\big)_i$. -/
def dualPi : (Fin (n * d) → ℤ) ≃
    ((i : Fin n) → ((FractionalIdeal.dual ℤ ℚ (I i : FractionalIdeal (𝓞 F)⁰ F) :
      FractionalIdeal (𝓞 F)⁰ F) : Set F)) :=
  (Equiv.arrowCongr (sigE n d).symm (Equiv.refl ℤ)).trans
    ((Equiv.piCurry fun (_ : Fin n) (_ : Fin d) => ℤ).trans (Equiv.piCongrRight fun i => dualEquiv (I i)))

lemma dualPi_coe (m : Fin (n * d) → ℤ) (i : Fin n) :
    (dualPi I m i : F) = dualElt (I i) fun j => m (sigE n d ⟨i, j⟩) := by
  rw [← dualEquiv_coe]
  rfl

/-- **The Fourier transform on $F_\infty^n$:** $\hat f(z) = \int_{F_\infty^n} f(y)\,
e\big(\sum_{i<n}\operatorname{Tr}_\infty(y_iz_i)\big)\,dy$ for the product of the self-dual measures. -/
def fourierInfPi (f : (Fin n → V) → ℂ) (z : Fin n → V) : ℂ :=
  ∫ y, f y * ((𝐞 (∑ i, traceInf (y i * z i)) : Circle) : ℂ) ∂(Measure.pi fun _ => selfDualInf)

/-- **Poisson summation for a product of fractional ideals in $F_\infty^n$:** for nonzero fractional ideals
$I_0, \dots, I_{n-1}$ of $F$, a Schwartz function $f$ on $F_\infty^n$ and $\xi \in F^n$,
$$\sum_{x\in\prod_i I_i} f(\xi + x) = \prod_{i<n}\big(2^{r_2}\operatorname{covol}(I_i)\big)^{-1}
\sum_{\mu\in\prod_i I_i^\vee}\hat f(\mu)\,e\Big(-\sum_{i<n}\operatorname{Tr}_{F/\mathbb{Q}}(\xi_i\mu_i)\Big),$$
$\hat f$ = `fourierInfPi` (product of the self-dual measures), $I_i^\vee$ the trace dual of $I_i$, $r_2$ the number
of complex places and $\operatorname{covol}$ Mathlib's covolume of the ideal lattice. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.2, Lemma 4.2.4, p. 333 (n-variable form)"]
theorem poisson_fractionalIdeal_pi (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F) :
    ∑' x : ((i : Fin n) → ((I i : FractionalIdeal (𝓞 F)⁰ F) : Set F)),
        f (fun i => mixedEmbedding F (ξ i + x i)) =
      ((∏ i, ((2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F (I i))))⁻¹ : ℝ) *
        ∑' μ : ((i : Fin n) → ((FractionalIdeal.dual ℤ ℚ (I i : FractionalIdeal (𝓞 F)⁰ F) :
            FractionalIdeal (𝓞 F)⁰ F) : Set F)),
          fourierInfPi f (fun i => mixedEmbedding F (μ i)) *
            ((𝐞 (-∑ i, ((Algebra.trace ℚ F (ξ i * μ i) : ℚ) : ℝ)) : Circle) : ℂ) := by
  have hP := QuadFormsKB.Tamagawa.Measure.Weil.poisson_basis (Measure.pi fun _ : Fin n => selfDualInf)
    (piB I) betaPi (piBd I) (piB_dual I) f (fun i => mixedEmbedding F (ξ i))
  rw [measure_parallelepiped_piB] at hP
  rw [← (latPi I).tsum_eq, ← (dualPi I).tsum_eq]
  have hL : ∀ k : Fin (n * d) → ℤ, f (fun i => mixedEmbedding F (ξ i + latPi I k i)) =
      f ((fun i => mixedEmbedding F (ξ i)) + ∑ l, (k l : ℝ) • piB I l) := by
    intro k
    rw [sum_piB]
    congr 1
    funext i
    rw [Pi.add_apply, latPi_coe, map_add]
  simp_rw [hL]
  rw [hP]
  refine congrArg₂ (· * ·) (by push_cast; rfl) (tsum_congr fun m => ?_)
  rw [sum_piBd]
  congr 1
  · simp only [fourierInfPi, betaPi_apply, dualPi_coe]
  · congr 3
    rw [betaPi_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dualPi_coe, ← map_mul, traceInf_mixedEmbedding]

/-! ### Absolute convergence -/

section Summable

open QuadFormsKB.Tamagawa.Measure.Weil

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] {N : ℕ}

/-- The Fourier coefficient in `poisson_basis`: the Euclidean transform of $f \circ T$ at $-m$. -/
lemma fourier_basisT_neg (μ : Measure W) [μ.IsAddHaarMeasure] (b : Module.Basis (Fin N) ℝ W)
    (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W) (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0)
    (f : SchwartzMap W ℂ) (m : Fin N → ℤ) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin N) => SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (basisT b) f x)
        (SchwartzMap.PoissonSummation.Standard.intVec (-m)) =
      ((μ b.parallelepiped).toReal⁻¹ : ℝ) *
        ∫ y, f y * ((𝐞 (β y (∑ j, (m j : ℝ) • bd j)) : Circle) : ℂ) ∂μ := by
  set T := basisT b
  set h : W → ℂ := fun y => f y * ((𝐞 (β y (∑ j, (m j : ℝ) • bd j)) : Circle) : ℂ) with hh
  have h1 : 𝓕 (fun x : EuclideanSpace ℝ (Fin N) => SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T f x)
      (SchwartzMap.PoissonSummation.Standard.intVec (-m)) = ∫ t, h (T t) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have : inner ℝ t (SchwartzMap.PoissonSummation.Standard.intVec (-m)) =
        -β (T t) (∑ j, (m j : ℝ) • bd j) := by
      rw [← inner_basisT_symm b β bd hbd (T t) m, ContinuousLinearEquiv.symm_apply_apply]
      have : SchwartzMap.PoissonSummation.Standard.intVec (-m) =
          -SchwartzMap.PoissonSummation.Standard.intVec m := by
        ext i; simp [SchwartzMap.PoissonSummation.Standard.intVec]
      rw [this, inner_neg_right]
    simp only [hh, Circle.smul_def, smul_eq_mul, this, neg_neg]
    exact mul_comm _ _
  have h2 : ∫ t, h (T t) = ∫ y, h y ∂(Measure.map T (volume : Measure (EuclideanSpace ℝ (Fin N)))) := by
    rw [show (Measure.map T (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      Measure.map T.toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
    rfl
  rw [h1, h2, map_basisT_volume μ b, integral_smul_measure, ENNReal.toReal_inv]
  rw [Complex.real_smul, Complex.ofReal_inv]

/-- The dual side of `poisson_basis` converges absolutely. -/
lemma summable_basis_dual (μ : Measure W) [μ.IsAddHaarMeasure] (b : Module.Basis (Fin N) ℝ W)
    (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W) (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0)
    (f : SchwartzMap W ℂ) :
    Summable fun m : Fin N → ℤ => ‖∫ y, f y * ((𝐞 (β y (∑ j, (m j : ℝ) • bd j)) : Circle) : ℂ) ∂μ‖ := by
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (basisT b) f
  set K : ℝ := (μ b.parallelepiped).toReal
  have hK : 0 < K := ENNReal.toReal_pos
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior μ b.parallelepiped.interior_nonempty).ne'
    b.parallelepiped.isCompact.measure_lt_top.ne
  have hs := (summable_norm_intPt (𝓕 g)).comp_injective (neg_injective (G := Fin N → ℤ))
  refine (hs.mul_left K).congr fun m => ?_
  simp only [Function.comp_apply]
  rw [SchwartzMap.fourier_coe, intPt, fourier_basisT_neg μ b β bd hbd f m, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK), ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]

/-- The map $\mathbb R^N \to W$, $w \mapsto \sum_j w_jb_j^\vee$. -/
def dualMap (bd : Fin N → W) : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] W where
  toFun w := ∑ j, w j • bd j
  map_add' w w' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

lemma inner_basisT_symm_real (b : Module.Basis (Fin N) ℝ W) (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W)
    (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0) (y : W) (w : EuclideanSpace ℝ (Fin N)) :
    inner ℝ ((basisT b).symm y) w = β y (dualMap bd w) := by
  let L1 : W →ₗ[ℝ] ℝ := (innerSL ℝ w).toLinearMap ∘ₗ (basisT b).symm.toLinearMap
  let L2 : W →ₗ[ℝ] ℝ := β.flip (dualMap bd w)
  have h : L1 = L2 := by
    refine b.ext fun i => ?_
    rw [← basisT_single]
    show inner ℝ w ((basisT b).symm ((basisT b) (EuclideanSpace.single i 1))) =
      β ((basisT b) (EuclideanSpace.single i 1)) (dualMap bd w)
    rw [ContinuousLinearEquiv.symm_apply_apply, basisT_single, EuclideanSpace.inner_single_right]
    simp only [dualMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, hbd, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp
  have := congrArg (fun L : W →ₗ[ℝ] ℝ => L y) h
  simp only [L1, L2, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, LinearMap.flip_apply] at this
  rw [real_inner_comm]
  exact this

lemma dualMap_injective (b : Module.Basis (Fin N) ℝ W) (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W)
    (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0) : Function.Injective (dualMap bd) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  ext k
  have := congrArg (β (b k)) hw
  simp only [dualMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, hbd, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero] at this
  simpa using this

/-- $w \mapsto \sum_j w_jb_j^\vee$ as a continuous linear equivalence. -/
def dualEquivL (b : Module.Basis (Fin N) ℝ W) (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W)
    (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0) : EuclideanSpace ℝ (Fin N) ≃L[ℝ] W :=
  ((dualMap bd).linearEquivOfInjective (dualMap_injective b β bd hbd)
    (by rw [finrank_euclideanSpace_fin, Module.finrank_eq_card_basis b, Fintype.card_fin])).toContinuousLinearEquiv

/-- **The $\beta$-Fourier transform of a Schwartz function is a Schwartz function:**
$z \mapsto \int_W f(y)\,e(\beta(y, z))\,d\mu(y)$ is $\mu(P_b)\cdot\widehat{f\circ T}(-T'^{-1}z)$. -/
theorem exists_schwartz_fourier_basis (μ : Measure W) [μ.IsAddHaarMeasure] (b : Module.Basis (Fin N) ℝ W)
    (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W) (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0)
    (f : SchwartzMap W ℂ) :
    ∃ H : SchwartzMap W ℂ, ∀ z, H z = ∫ y, f y * ((𝐞 (β y z) : Circle) : ℂ) ∂μ := by
  set T := basisT b
  set S := dualEquivL b β bd hbd
  set g : SchwartzMap (EuclideanSpace ℝ (Fin N)) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T f
  set c : ℝ := (μ b.parallelepiped).toReal
  have hc : 0 < c := ENNReal.toReal_pos
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior μ b.parallelepiped.interior_nonempty).ne'
    b.parallelepiped.isCompact.measure_lt_top.ne
  refine ⟨(c : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (S.symm.trans (ContinuousLinearEquiv.neg ℝ))
    (𝓕 g), fun z => ?_⟩
  set h : W → ℂ := fun y => f y * ((𝐞 (β y z) : Circle) : ℂ) with hh
  have h1 : 𝓕 (g : EuclideanSpace ℝ (Fin N) → ℂ) (-(S.symm z)) = ∫ t, h (T t) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have : inner ℝ t (-(S.symm z)) = -β (T t) z := by
      rw [inner_neg_right, ← ContinuousLinearEquiv.symm_apply_apply T t, inner_basisT_symm_real b β bd hbd]
      congr 2
      · simp [T]
      · exact S.apply_symm_apply z
    simp only [hh, Circle.smul_def, smul_eq_mul, this, neg_neg]
    exact mul_comm _ _
  have h2 : ∫ t, h (T t) = ∫ y, h y ∂(Measure.map T (volume : Measure (EuclideanSpace ℝ (Fin N)))) := by
    rw [show (Measure.map T (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      Measure.map T.toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
    rfl
  rw [h2, map_basisT_volume μ b, integral_smul_measure, ENNReal.toReal_inv] at h1
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_neg, SchwartzMap.fourier_coe, smul_eq_mul]
  rw [show ((-id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (S.symm z)) = -(S.symm z) from rfl, h1,
    Complex.real_smul,
    Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hc.ne'), one_mul]

end Summable

variable (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-- The left side of `poisson_fractionalIdeal_pi` converges absolutely. -/
theorem summable_poisson_pi_lhs (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F) :
    Summable fun x : ((i : Fin n) → ((I i : FractionalIdeal (𝓞 F)⁰ F) : Set F)) =>
      f (fun i => mixedEmbedding F (ξ i + x i)) := by
  rw [← (latPi I).summable_iff]
  refine Summable.of_norm ?_
  have h := QuadFormsKB.Tamagawa.Measure.Weil.summable_basis (piB I)
    (SchwartzMap.compSubConstCLM ℂ (-fun i => mixedEmbedding F (ξ i)) f)
  refine h.congr fun k => ?_
  rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, sum_piB]
  simp only [Function.comp_apply]
  congr 2
  funext i
  rw [Pi.add_apply, latPi_coe, map_add, add_comm]

/-- The right side of `poisson_fractionalIdeal_pi` converges absolutely. -/
theorem summable_poisson_pi_rhs (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F) :
    Summable fun μ : ((i : Fin n) → ((FractionalIdeal.dual ℤ ℚ (I i : FractionalIdeal (𝓞 F)⁰ F) :
        FractionalIdeal (𝓞 F)⁰ F) : Set F)) =>
      fourierInfPi f (fun i => mixedEmbedding F (μ i)) *
        ((𝐞 (-∑ i, ((Algebra.trace ℚ F (ξ i * μ i) : ℚ) : ℝ)) : Circle) : ℂ) := by
  rw [← (dualPi I).summable_iff]
  refine Summable.of_norm ?_
  have h := summable_basis_dual (Measure.pi fun _ : Fin n => selfDualInf) (piB I) betaPi (piBd I)
    (piB_dual I) f
  refine h.congr fun m => ?_
  simp only [Function.comp_apply, norm_mul, Circle.norm_coe, mul_one, sum_piBd, fourierInfPi,
    betaPi_apply, dualPi_coe]

/-- **`fourierInfPi` maps Schwartz functions to Schwartz functions** on $F_\infty^n$. -/
theorem exists_schwartz_fourierInfPi (f : SchwartzMap (Fin n → V) ℂ) :
    ∃ H : SchwartzMap (Fin n → V) ℂ, (H : (Fin n → V) → ℂ) = fourierInfPi f := by
  obtain ⟨H, hH⟩ := exists_schwartz_fourier_basis (Measure.pi fun _ : Fin n => selfDualInf)
    (piB fun _ => (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) betaPi (piBd fun _ => 1) (piB_dual fun _ => 1) f
  exact ⟨H, funext fun z => by rw [hH z, fourierInfPi]; rfl⟩

end

end QuadFormsKB.Analysis
