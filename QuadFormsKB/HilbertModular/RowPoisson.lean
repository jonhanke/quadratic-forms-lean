/-
# Poisson summation for lattice periodizations

Generic Fourier analysis on $\mathbb{R}^J/\mathbb{Z}^J$, used for the rows $d \mapsto W(c, d)N(cz + d)^{-k}|N(cz+d)|^{-2s}$ of
Hilbert Eisenstein series.

* `cubeCoeff Q n` $= \int_{(0,1]^J}Q(t)\,e(-n\cdot t)\,dt$; **Fourier inversion** for continuous $\mathbb{Z}^J$-periodic $Q$ with
  absolutely summable coefficients (`hasSum_cubeCoeff`), from Mathlib's `hasSum_mFourier_series_apply_of_summable`.
* **Unfolding** (`cubeCoeff_tsum`): for $G$ continuous and integrable on $\mathbb{R}^J$, the coefficients of the periodization
  $\sum_{m\in\mathbb{Z}^J}G(t + m)$ are the Fourier transform $\int_{\mathbb{R}^J}G(t)e(-n\cdot t)\,dt$ (the unit cube is a
  fundamental domain, `ZSpan.isAddFundamentalDomain`).
-/
import QuadFormsKB.HilbertModular.FourierInversion

open Complex MeasureTheory Filter Topology Set UnitAddTorus
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {J : Type*} [Fintype J]

/-- **The Fourier coefficient on the unit cube**: $\int_{(0,1]^J}Q(t)\,e(-\sum_jn_jt_j)\,dt$. -/
noncomputable def cubeCoeff (Q : (J → ℝ) → ℂ) (n : J → ℤ) : ℂ :=
  ∫ t in unitCube J, Q t * cexp (-(2 * π * I) * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ))

/-- $\theta \mapsto Q(\tilde\theta)$ on the torus, $\tilde\theta \in (0, 1]^J$ the representative. -/
noncomputable def torusOf (Q : (J → ℝ) → ℂ) (θ : UnitAddTorus J) : ℂ :=
  Q fun j => ((AddCircle.equivIoc 1 0 (θ j)) : ℝ)

lemma torusOf_mk {Q : (J → ℝ) → ℂ} (hper : ∀ (m : J → ℤ) t, Q (t + fun j => (m j : ℝ)) = Q t)
    (t : J → ℝ) : torusOf Q (torusMk t) = Q t := by
  choose n hn using fun i => rep_sub_int (t i)
  simp only [torusOf, torusMk]
  rw [show (fun j => ((AddCircle.equivIoc 1 0 ((t j : UnitAddCircle))) : ℝ)) =
    t + fun j => (n j : ℝ) from funext fun j => hn j]
  exact hper n t

lemma continuous_torusOf {Q : (J → ℝ) → ℂ} (hQ : Continuous Q)
    (hper : ∀ (m : J → ℤ) t, Q (t + fun j => (m j : ℝ)) = Q t) : Continuous (torusOf Q) := by
  rw [isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff]
  have : torusOf Q ∘ torusMk = Q := funext fun t => torusOf_mk hper t
  rw [this]; exact hQ

lemma cubeCoeff_eq_mFourierCoeff {Q : (J → ℝ) → ℂ}
    (hper : ∀ (m : J → ℤ) t, Q (t + fun j => (m j : ℝ)) = Q t) (n : J → ℤ) :
    cubeCoeff Q n = mFourierCoeff (torusOf Q) n := by
  rw [mFourierCoeff_eq_integral _ n 0, cubeCoeff]
  have hs : {x : J → ℝ | ∀ i, x i ∈ Ioc ((0 : J → ℝ) i) ((0 : J → ℝ) i + 1)} = unitCube J := by
    ext t; simp [unitCube]
  rw [hs]
  refine setIntegral_congr_fun measurableSet_unitCube fun t _ => ?_
  change _ = mFourier (-n) (torusMk t) • torusOf Q (torusMk t)
  rw [torusOf_mk hper, mFourier_torusMk, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Fourier inversion on $\mathbb{R}^J/\mathbb{Z}^J$**: a continuous $\mathbb{Z}^J$-periodic $Q$ with $\sum_n|\hat Q(n)| < \infty$ is the
sum of its Fourier series, $Q(t) = \sum_n\hat Q(n)\,e(n\cdot t)$. -/
theorem hasSum_cubeCoeff {Q : (J → ℝ) → ℂ} (hQ : Continuous Q)
    (hper : ∀ (m : J → ℤ) t, Q (t + fun j => (m j : ℝ)) = Q t)
    (hsum : Summable fun n => ‖cubeCoeff Q n‖) (t : J → ℝ) :
    HasSum (fun n => cubeCoeff Q n * cexp (2 * π * I * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ))) (Q t) := by
  set g : C(UnitAddTorus J, ℂ) := ⟨torusOf Q, continuous_torusOf hQ hper⟩
  have hs : Summable (mFourierCoeff g) := by
    refine Summable.of_norm ?_
    have : ∀ n, mFourierCoeff g n = cubeCoeff Q n := fun n => (cubeCoeff_eq_mFourierCoeff hper n).symm
    simp only [this]; exact hsum
  have h := hasSum_mFourier_series_apply_of_summable hs (torusMk t)
  have hg : g (torusMk t) = Q t := torusOf_mk hper t
  rw [hg] at h
  convert h using 2 with n
  rw [smul_eq_mul, mFourier_torusMk]
  change _ = mFourierCoeff (torusOf Q) n * _
  rw [← cubeCoeff_eq_mFourierCoeff hper n]

/-! ### Unfolding -/

/-- The lattice $\mathbb{Z}^J \subset \mathbb{R}^J$ as the $\mathbb{Z}$-span of the standard basis. -/
abbrev intLattice (J : Type*) [Fintype J] : Submodule ℤ (J → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ J))

lemma intCast_mem_intLattice (m : J → ℤ) : (fun j => (m j : ℝ)) ∈ intLattice J := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro i
  exact ⟨m i, by simp⟩

/-- $\mathbb{Z}^J \simeq$ `intLattice J`. -/
noncomputable def intLatticeEquiv : (J → ℤ) ≃ intLattice J :=
  Equiv.ofBijective (fun m => ⟨fun j => (m j : ℝ), intCast_mem_intLattice m⟩) <| by
    constructor
    · intro m m' h
      funext j
      have := congrFun (congrArg Subtype.val h) j
      simpa using this
    · rintro ⟨x, hx⟩
      rw [Module.Basis.mem_span_iff_repr_mem] at hx
      choose m hm using hx
      refine ⟨m, Subtype.ext (funext fun j => ?_)⟩
      have := hm j
      simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
      exact this

lemma integral_eq_tsum_cube {f : (J → ℝ) → ℂ} (hf : Integrable f) :
    ∫ t, f t = ∑' m : J → ℤ, ∫ t in unitCube J, f (t + fun j => (m j : ℝ)) := by
  have h := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ J) (volume : Measure (J → ℝ))
  have : Countable (intLattice J) := (intLatticeEquiv (J := J)).symm.injective.countable
  have : Countable (intLattice J).toAddSubgroup := inferInstanceAs (Countable (intLattice J))
  let e' : (J → ℤ) ≃ ↥(intLattice J).toAddSubgroup := intLatticeEquiv
  rw [h.integral_eq_tsum'' f hf, ← e'.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [ZSpan.fundamentalDomain_pi_basisFun]
  have hae : (unitCube J : Set (J → ℝ)) =ᵐ[volume] Set.pi Set.univ fun _ : J => Set.Ico (0 : ℝ) 1 := by
    have h1 : (unitCube J : Set (J → ℝ)) = Set.pi Set.univ fun _ : J => Set.Ioc (0 : ℝ) 1 := by
      ext t; simp [unitCube]
    rw [h1]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  rw [setIntegral_congr_set hae]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun t _ => ?_
  change f ((e' m : J → ℝ) + t) = f (t + fun j => (m j : ℝ))
  rw [add_comm]; rfl

lemma lintegral_eq_tsum_cube (f : (J → ℝ) → ENNReal) :
    ∫⁻ t, f t = ∑' m : J → ℤ, ∫⁻ t in unitCube J, f (t + fun j => (m j : ℝ)) := by
  have h := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ J) (volume : Measure (J → ℝ))
  have : Countable (intLattice J) := (intLatticeEquiv (J := J)).symm.injective.countable
  have : Countable (intLattice J).toAddSubgroup := inferInstanceAs (Countable (intLattice J))
  let e' : (J → ℤ) ≃ ↥(intLattice J).toAddSubgroup := intLatticeEquiv
  rw [h.lintegral_eq_tsum'' f, ← e'.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [ZSpan.fundamentalDomain_pi_basisFun]
  have hae : (unitCube J : Set (J → ℝ)) =ᵐ[volume] Set.pi Set.univ fun _ : J => Set.Ico (0 : ℝ) 1 := by
    have h1 : (unitCube J : Set (J → ℝ)) = Set.pi Set.univ fun _ : J => Set.Ioc (0 : ℝ) 1 := by
      ext t; simp [unitCube]
    rw [h1]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  rw [setLIntegral_congr hae]
  refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun t _ => ?_
  change f ((e' m : J → ℝ) + t) = f (t + fun j => (m j : ℝ))
  rw [add_comm]; rfl

lemma cexp_neg_int_pair_add (n m : J → ℤ) (t : J → ℝ) :
    cexp (-(2 * π * I) * ((∑ j, (n j : ℝ) * (t + fun j => (m j : ℝ)) j : ℝ) : ℂ)) =
      cexp (-(2 * π * I) * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) := by
  have hr : (∑ j, (n j : ℝ) * (t + fun j => (m j : ℝ)) j) =
      (∑ j, (n j : ℝ) * t j) + ((∑ j, n j * m j : ℤ) : ℝ) := by
    push_cast; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have : ((∑ j, (n j : ℝ) * (t + fun j => (m j : ℝ)) j : ℝ) : ℂ) =
      ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ) + ((∑ j, n j * m j : ℤ) : ℂ) := by
    rw [hr]; push_cast; ring
  rw [this, mul_add, Complex.exp_add]
  have h1 : cexp (-(2 * π * I) * ((∑ j, n j * m j : ℤ) : ℂ)) = 1 := by
    rw [show -(2 * π * I) * ((∑ j, n j * m j : ℤ) : ℂ) = ((-(∑ j, n j * m j) : ℤ) : ℂ) * (2 * π * I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h1, mul_one]

/-- **Unfolding**: the cube coefficients of the periodization of an integrable continuous $G$ are its Fourier transform,
$\widehat{\sum_mG(\cdot + m)}(n) = \int_{\mathbb{R}^J}G(t)e(-n\cdot t)\,dt$. -/
theorem cubeCoeff_tsum {G : (J → ℝ) → ℂ} (hG : Continuous G) (hGi : Integrable G) (n : J → ℤ) :
    cubeCoeff (fun t => ∑' m : J → ℤ, G (t + fun j => (m j : ℝ))) n =
      ∫ t, G t * cexp (-(2 * π * I) * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) := by
  set e : (J → ℝ) → ℂ := fun t => cexp (-(2 * π * I) * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) with he
  have hcont_e : Continuous e := by
    simp only [he]; fun_prop
  have hnorm_e : ∀ t, ‖e t‖ = 1 := by
    intro t
    simp only [he]
    rw [show -(2 * π * I) * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ) =
      ((-(2 * π) * ∑ j, (n j : ℝ) * t j : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hint : Integrable fun t => G t * e t := by
    refine Integrable.mono' hGi.norm (hG.mul hcont_e).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, hnorm_e, mul_one]
  rw [integral_eq_tsum_cube hint, cubeCoeff]
  have hper : ∀ (m : J → ℤ) t, e (t + fun j => (m j : ℝ)) = e t := fun m t => cexp_neg_int_pair_add n m t
  simp_rw [hper]
  rw [← integral_tsum]
  · refine setIntegral_congr_fun measurableSet_unitCube fun t _ => ?_
    exact tsum_mul_right.symm
  · intro m
    exact ((hG.comp (continuous_id.add continuous_const)).mul hcont_e).aestronglyMeasurable
  · have h := lintegral_eq_tsum_cube (fun t => ‖G t‖ₑ)
    have hfin : ∫⁻ t, ‖G t‖ₑ ≠ ⊤ := hGi.hasFiniteIntegral.ne
    rw [h] at hfin
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun m => ?_)
    refine setLIntegral_mono' measurableSet_unitCube fun t _ => ?_
    rw [enorm_mul]
    have : ‖e t‖ₑ = 1 := by
      rw [← ofReal_norm, hnorm_e, ENNReal.ofReal_one]
    rw [this, mul_one]

/-! ### Lattices in $\mathbb{R}^\iota$: change of variables and Poisson summation -/

variable {ι : Type*} [Fintype ι]

/-- **The inverse covolume of the lattice $\bigoplus_j\mathbb{Z}b_j$**: the Haar scalar factor $c_b$ with
$\int_{\mathbb{R}^J}h(\sum_jt_jb_j)\,dt = c_b\int_{\mathbb{R}^\iota}h(x)\,dx$ (`integral_comp_basis`); $c_b = 1/\operatorname{covol}$. -/
noncomputable def latConst (b : Module.Basis J ℝ (ι → ℝ)) : NNReal :=
  Measure.addHaarScalarFactor (Measure.map (b.equivFun.symm.toContinuousLinearEquiv : (J → ℝ) → ι → ℝ)
    (volume : Measure (J → ℝ))) (volume : Measure (ι → ℝ))

lemma map_basis_volume (b : Module.Basis J ℝ (ι → ℝ)) :
    Measure.map (b.equivFun.symm.toContinuousLinearEquiv : (J → ℝ) → ι → ℝ) (volume : Measure (J → ℝ)) =
      latConst b • (volume : Measure (ι → ℝ)) :=
  Measure.isAddLeftInvariant_eq_smul _ _

lemma integral_comp_basis (b : Module.Basis J ℝ (ι → ℝ)) (h : (ι → ℝ) → ℂ) :
    ∫ t, h (b.equivFun.symm t) = (latConst b : ℂ) * ∫ x, h x := by
  have hme := (b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have := hme.integral_map (μ := (volume : Measure (J → ℝ))) h
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at this
  rw [map_basis_volume, integral_smul_nnreal_measure] at this
  have h3 : ∫ t, h (b.equivFun.symm t) = ∫ x, h (b.equivFun.symm.toContinuousLinearEquiv x) := rfl
  rw [h3, ← this, NNReal.smul_def, Complex.real_smul]

lemma integrable_comp_basis (b : Module.Basis J ℝ (ι → ℝ)) {h : (ι → ℝ) → ℂ} (hh : Integrable h) :
    Integrable fun t => h (b.equivFun.symm t) := by
  have hme := (b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have := (hme.integrable_map_iff (μ := (volume : Measure (J → ℝ))) (g := h)).mp
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at this
  rw [map_basis_volume] at this
  exact this (hh.smul_measure_nnreal)

lemma pair_symm_int (b : Module.Basis J ℝ (ι → ℝ)) (n : J → ℤ) (t : J → ℝ) :
    pair (dualVec b n) (b.equivFun.symm t) = ∑ j, (n j : ℝ) * t j :=
  pair_dualVec_symm b n t

/-- **Poisson summation over the lattice $\Lambda = \bigoplus_j\mathbb{Z}b_j$**: for $\Phi$ continuous and integrable on $\mathbb{R}^\iota$,
whose translates $\Phi(w + \lambda)$, $\lambda\in\Lambda$, are summable locally uniformly (`hloc`), and whose Fourier transform
is absolutely summable over the dual lattice $\Lambda^\vee = \{\nu_n\}$ (`hsum`),
$$\sum_{\lambda\in\Lambda}\Phi(w + \lambda) = c_b\sum_{n}\hat\Phi(\nu_n)\,e(\langle\nu_n, w\rangle),\qquad
  \hat\Phi(\nu) = \int_{\mathbb{R}^\iota}\Phi(x)e(-\langle\nu, x\rangle)\,dx.$$ -/
theorem hasSum_lattice_fourier (b : Module.Basis J ℝ (ι → ℝ)) {Φ : (ι → ℝ) → ℂ}
    (hΦc : Continuous Φ) (hΦi : Integrable Φ) (w : ι → ℝ)
    (hloc : ∀ R : ℝ, ∃ u : (J → ℤ) → ℝ, Summable u ∧ ∀ t : J → ℝ, ‖t‖ ≤ R → ∀ n : J → ℤ,
      ‖Φ (w + b.equivFun.symm (t + fun j => (n j : ℝ)))‖ ≤ u n)
    (hsum : Summable fun n : J → ℤ =>
      ‖∫ x, Φ x * cexp (-(2 * π * I) * (pair (dualVec b n) x : ℂ))‖) :
    HasSum (fun n : J → ℤ => (latConst b : ℂ) * (∫ x, Φ x * cexp (-(2 * π * I) * (pair (dualVec b n) x : ℂ))) *
      cexp (2 * π * I * (pair (dualVec b n) w : ℂ)))
      (∑' m : J → ℤ, Φ (w + b.equivFun.symm fun j => (m j : ℝ))) := by
  set G : (J → ℝ) → ℂ := fun t => Φ (w + b.equivFun.symm t) with hG
  have hGc : Continuous G := hΦc.comp (continuous_const.add
    (b.equivFun.symm.toContinuousLinearEquiv.continuous))
  have hGi : Integrable G := by
    have : Integrable fun x => Φ (w + x) := hΦi.comp_add_left w
    exact integrable_comp_basis b this
  set Q : (J → ℝ) → ℂ := fun t => ∑' m : J → ℤ, G (t + fun j => (m j : ℝ)) with hQ
  -- periodicity and continuity of `Q`
  have hQper : ∀ (m : J → ℤ) t, Q (t + fun j => (m j : ℝ)) = Q t := by
    intro m t
    simp only [hQ]
    conv_rhs => rw [← (Equiv.addRight m).tsum_eq]
    refine tsum_congr fun n => ?_
    congr 1
    funext j
    simp [add_assoc, add_comm]
  have hQc : Continuous Q := by
    rw [continuous_iff_continuousAt]
    intro t₀
    obtain ⟨u, hu, hub⟩ := hloc (‖t₀‖ + 1)
    have hcont : ContinuousOn Q (Metric.ball t₀ 1) := by
      refine continuousOn_tsum (fun n => (hGc.comp (continuous_id.add continuous_const)).continuousOn)
        hu fun n t ht => ?_
      have : ‖t‖ ≤ ‖t₀‖ + 1 := by
        have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall ht)
        have h2 := norm_sub_norm_le t t₀
        rw [Metric.mem_ball, dist_eq_norm] at ht
        linarith
      exact hub t this n
    exact hcont.continuousAt (Metric.ball_mem_nhds t₀ one_pos)
  -- the coefficients
  have hcoeff : ∀ n : J → ℤ, cubeCoeff Q n = (latConst b : ℂ) *
      (∫ x, Φ x * cexp (-(2 * π * I) * (pair (dualVec b n) x : ℂ))) *
        cexp (2 * π * I * (pair (dualVec b n) w : ℂ)) := by
    intro n
    rw [hQ, cubeCoeff_tsum hGc hGi n]
    have h1 : ∫ t, G t * cexp (-(2 * π * I) * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) =
        ∫ t, (fun x => Φ (w + x) * cexp (-(2 * π * I) * (pair (dualVec b n) x : ℂ)))
          (b.equivFun.symm t) := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hG, pair_symm_int]
    rw [h1, integral_comp_basis b (fun x => Φ (w + x) * cexp (-(2 * π * I) * (pair (dualVec b n) x : ℂ)))]
    have h2 : ∫ x, Φ (w + x) * cexp (-(2 * π * I) * (pair (dualVec b n) x : ℂ)) =
        ∫ x, Φ x * cexp (-(2 * π * I) * (pair (dualVec b n) (x - w) : ℂ)) := by
      have := integral_add_left_eq_self (μ := (volume : Measure (ι → ℝ)))
        (fun x => Φ x * cexp (-(2 * π * I) * (pair (dualVec b n) (x - w) : ℂ))) w
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [add_sub_cancel_left]
    have h3 : ∫ x, Φ x * cexp (-(2 * π * I) * (pair (dualVec b n) (x - w) : ℂ)) =
        (∫ x, Φ x * cexp (-(2 * π * I) * (pair (dualVec b n) x : ℂ))) *
          cexp (2 * π * I * (pair (dualVec b n) w : ℂ)) := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [mul_assoc (Φ x), ← Complex.exp_add, pair_sub]
      congr 2
      push_cast; ring
    rw [h2, h3]; ring
  have hsumQ : Summable fun n => ‖cubeCoeff Q n‖ := by
    refine (hsum.mul_left (latConst b : ℝ)).congr fun n => ?_
    rw [hcoeff, norm_mul, norm_mul, show (2 * π * I * (pair (dualVec b n) w : ℂ)) =
      ((2 * π * pair (dualVec b n) w : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, NNReal.norm_eq]
  have h := hasSum_cubeCoeff hQc hQper hsumQ 0
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, ofReal_zero, Complex.exp_zero,
    mul_one] at h
  rw [hQ] at h
  simp only [zero_add] at h
  convert h using 1
  funext n; exact (hcoeff n).symm

end QuadFormsKB.HilbertModular
