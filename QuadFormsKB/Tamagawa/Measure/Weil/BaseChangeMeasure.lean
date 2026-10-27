import QuadFormsKB.Tamagawa.Measure.Weil.BaseChange

/-!
# Base change of adeles: compatibility of self-dual measures
$K/k$ a finite extension of number fields, $b$ a $k$-basis of $K$, $\Psi$ = `adeleBaseChange b` :
$K\otimes_k\mathbb A_k = \mathbb A_k^\iota\cong\mathbb A_K$.

* **`map_adeleBaseChange_muAddVec`**: $\Psi_*(\mu_k^{\otimes\iota}) = \mu_K$, where $\mu_F$ = `muAdd F` is the self-dual
  measure of $\mathbb A_F$ and $\mu_k^{\otimes\iota}$ = `muAddVec k ι` is the coordinate self-dual measure.
  *Proof:* $\Psi_*\mu_k^{\otimes\iota}$ is a Haar measure on $\mathbb A_K$, hence $c\,\mu_K$; $\Psi$ maps a fundamental
  domain of $k^\iota$ to one of $K$ (`isAddFundamentalDomain_baseChange`), and both covolumes are $1$
  (`addCovolume_muAddVec`, `addCovolume_muAdd`), so $c = 1$. No local computation and no discriminant tower
  formula is needed.
* **`finprod_traceFactor_mul_inf`** (the trace normalization): the $\psi\circ\operatorname{Tr}_{K/k}$-self-dual measure on
  $K\otimes k_v$ is $|\det G|_v^{1/2}$ times the coordinate one, $G = (\operatorname{Tr}_{K/k}(b_ib_j))$ the trace Gram
  matrix (`Algebra.traceMatrix`, $\det G$ = `Algebra.discr k b` $\ne0$), and
  $\prod_v|\det G|_v^{1/2}\cdot|\det G|_\infty^{1/2} = 1$ by the product formula. Hence the global
  $\psi\circ\operatorname{Tr}$-self-dual measure on $K\otimes_k\mathbb A_k$ *is* `muAddVec k ι`, and by the first item it
  corresponds to `muAdd K` (**`map_adeleBaseChange_traceSelfDual`**). The local identification of the
  $\psi_v\circ\operatorname{Tr}$-self-dual measure with $|\det G|_v^{1/2}dx$ is in `BaseChangeTraceLocal.lean`
  (`selfDual_trace_iff`, for $K = k(\delta)$ with basis $(1,\delta)$, $G = \operatorname{diag}(2, 2d)$).
* **`addCovolume_baseChange`**: $\operatorname{vol}(\mathbb A_K/K)$ computed on either side agrees (both are $1$).
-/

open IsDedekindDomain NumberField Topology Filter MeasureTheory NumberField.mixedEmbedding
open scoped ENNReal

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

set_option synthInstance.maxHeartbeats 200000

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K)

/-- The fundamental domain $\Psi\big((D_\infty\times\hat{\mathcal O}_k)^\iota\big)$ of $K$ in $\mathbb A_K$. -/
def fundDomBaseChange : Set (Adeles K) := (adeleBaseChange b).symm ⁻¹' fundDomVec k ι

theorem measurableSet_fundDomBaseChange : MeasurableSet (fundDomBaseChange b) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_fundDom).preimage
    (adeleBaseChange b).symm.continuous.measurable

theorem existsUnique_vadd_mem_fundDomBaseChange (y : Adeles K) :
    ∃! g : diagSub K, g +ᵥ y ∈ fundDomBaseChange b := by
  obtain ⟨⟨_, ξ, rfl⟩, hg, huniq⟩ := existsUnique_vadd_mem_fundDomVec ((adeleBaseChange b).symm y)
  have key : ∀ z : K, (adeleBaseChange b).symm (diag K z + y) =
      diagVec k ι (b.equivFun z) + (adeleBaseChange b).symm y := by
    intro z
    rw [map_add, ← LinearEquiv.symm_apply_apply b.equivFun z, ← adeleBaseChange_diag,
      ContinuousAddEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  refine ⟨⟨diag K (b.equivFun.symm ξ), _, rfl⟩, ?_, ?_⟩
  · show (adeleBaseChange b).symm (diag K (b.equivFun.symm ξ) + y) ∈ fundDomVec k ι
    rw [key, LinearEquiv.apply_symm_apply]; exact hg
  · rintro ⟨_, z, rfl⟩ hz
    have hz' : (⟨diagVec k ι (b.equivFun z), _, rfl⟩ : diagVecSub k ι) +ᵥ (adeleBaseChange b).symm y ∈
        fundDomVec k ι := by
      show diagVec k ι (b.equivFun z) + _ ∈ _
      rw [← key]; exact hz
    have h := congrArg Subtype.val (huniq _ hz')
    have h2 : b.equivFun z = ξ := diagVec_injective h
    refine Subtype.ext ?_
    show diag K z = diag K (b.equivFun.symm ξ)
    rw [← h2, LinearEquiv.symm_apply_apply]

/-- $\Psi$ maps the fundamental domain of $k^\iota$ to a fundamental domain of $K$ (for every measure). -/
theorem isAddFundamentalDomain_baseChange (μ : Measure (Adeles K)) :
    IsAddFundamentalDomain (diagSub K) (fundDomBaseChange b) μ :=
  IsAddFundamentalDomain.mk' (measurableSet_fundDomBaseChange b).nullMeasurableSet
    (existsUnique_vadd_mem_fundDomBaseChange b)

instance : MeasurableAdd (Adeles K) := ContinuousAdd.measurableAdd

theorem muAdd_fundDomBaseChange : muAdd K (fundDomBaseChange b) = 1 := by
  rw [← (isAddFundamentalDomain_baseChange b (muAdd K)).covolume_eq_volume, addCovolume_muAdd]

/-- **Compatibility of self-dual measures**: $\Psi_*(\mu_k^{\otimes\iota}) = \mu_K$. -/
@[kb "weil1982" "§2.1.3 [unverified page]"]
theorem map_adeleBaseChange_muAddVec : (muAddVec k ι).map (adeleBaseChange b) = muAdd K := by
  set ν := (muAddVec k ι).map (adeleBaseChange b) with hν
  have hH : ν.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map _ _
  have hc := Measure.isAddLeftInvariant_eq_smul ν (muAdd K)
  set c := Measure.addHaarScalarFactor ν (muAdd K)
  have h1 : ν (fundDomBaseChange b) = 1 := by
    have hm : Measurable (adeleBaseChange b) := (adeleBaseChange b).continuous.measurable
    rw [hν, Measure.map_apply hm (measurableSet_fundDomBaseChange b)]
    have : (adeleBaseChange b) ⁻¹' fundDomBaseChange b = fundDomVec k ι := by
      ext x; simp [fundDomBaseChange]
    rw [this, ← (isAddFundamentalDomain_fundDomVec (muAddVec k ι)).covolume_eq_volume, addCovolume_muAddVec]
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have := h1
    rw [hc, Measure.smul_apply, muAdd_fundDomBaseChange, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this
  rw [hc, show c = 1 by exact_mod_cast hc1, one_smul]

/-- $\Psi$ is measure preserving from $(\mathbb A_k^\iota, \mu_k^{\otimes\iota})$ to $(\mathbb A_K,\mu_K)$. -/
theorem measurePreserving_adeleBaseChange :
    MeasurePreserving (adeleBaseChange b) (muAddVec k ι) (muAdd K) :=
  ⟨(adeleBaseChange b).continuous.measurable, map_adeleBaseChange_muAddVec b⟩

/-- **$\operatorname{vol}(\mathbb A_K/K)$ is the same computed on either side**: the covolume of $K$ in $\mathbb A_K$ for
$\Psi_*\mu_k^{\otimes\iota}$ equals the covolume of $k^\iota$ in $\mathbb A_k^\iota$ for $\mu_k^{\otimes\iota}$ (both $1$). -/
theorem addCovolume_baseChange :
    addCovolume (diagSub K) (Adeles K) ((muAddVec k ι).map (adeleBaseChange b)) =
      addCovolume (diagVecSub k ι) (AdeleSpace k ι) (muAddVec k ι) := by
  rw [map_adeleBaseChange_muAddVec, addCovolume_muAdd, addCovolume_muAddVec]

/-! ### The trace normalization: $\prod_v|\det G|_v^{1/2} = 1$ -/

/-- $\det G = \operatorname{disc}_{K/k}(b)\in k^\times$, $G = (\operatorname{Tr}_{K/k}(b_ib_j))_{ij}$. -/
def discrUnit [DecidableEq ι] : kˣ := Units.mk0 (Algebra.discr k b) (Algebra.discr_not_zero_of_basis k b)

omit [NumberField k] [NumberField K] in
theorem discr_eq_det_traceMatrix [DecidableEq ι] : Algebra.discr k b = (Algebra.traceMatrix k b).det :=
  Algebra.discr_def k b

/-- The local factor $|\det G|_v^{1/2}$ relating the $\psi_v\circ\operatorname{Tr}_{K/k}$-self-dual measure on
$K\otimes k_v = k_v^\iota$ to the coordinate one. -/
def traceFactor [DecidableEq ι] (v : HeightOneSpectrum (𝓞 k)) : ℝ :=
  Real.sqrt (modAt (finPart (diagUnits k (discrUnit b))) v)

/-- **Global trace normalization**: $\prod_v|\det G|_v^{1/2}\cdot|\det G|_\infty^{1/2} = 1$ (product formula,
`ideleNorm_diagUnits`). So the product of the local $\psi\circ\operatorname{Tr}_{K/k}$-self-dual measures on
$K\otimes_k\mathbb A_k$ is the coordinate self-dual measure `muAddVec k ι`. -/
@[kb "weil1982" "§2.1 [unverified page] (‖det G‖ = 1 by the product formula)"]
theorem finprod_traceFactor_mul_inf [DecidableEq ι] :
    (∏ᶠ v, traceFactor b v) *
      Real.sqrt |LinearMap.det (LinearMap.mulLeft ℝ (mixedEmbedding k (Algebra.discr k b)))| = 1 := by
  have hnorm := ideleNorm_diagUnits (F := k) (discrUnit b)
  rw [ideleNorm] at hnorm
  set M := |LinearMap.det (LinearMap.mulLeft ℝ (mixedEmbedding k (Algebra.discr k b)))|
  have hM : |LinearMap.det (LinearMap.mulLeft ℝ ((infPart (diagUnits k (discrUnit b)) : mixedSpace k)))| = M :=
    rfl
  rw [hM] at hnorm
  set P := ∏ᶠ v, traceFactor b v
  have hfin : (Function.mulSupport fun v => traceFactor b v).Finite := by
    refine (mulSupport_modAt_finite (finPart (diagUnits k (discrUnit b)))).subset fun v hv => ?_
    rw [Function.mem_mulSupport] at hv ⊢
    intro h1
    apply hv
    rw [traceFactor, h1, NNReal.coe_one, Real.sqrt_one]
  have hP0 : 0 ≤ P := finprod_nonneg fun v => Real.sqrt_nonneg _
  have hP2 : P ^ 2 = ∏ᶠ v, (modAt (finPart (diagUnits k (discrUnit b))) v : ℝ) := by
    rw [show P ^ 2 = ∏ᶠ v, traceFactor b v ^ 2 from finprod_pow hfin 2]
    exact finprod_congr fun v => Real.sq_sqrt (NNReal.coe_nonneg _)
  have hM0 : 0 ≤ M := abs_nonneg _
  have hsq : (P * Real.sqrt M) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hM0, hP2, mul_comm]; exact hnorm
  have hnn : 0 ≤ P * Real.sqrt M := mul_nonneg hP0 (Real.sqrt_nonneg _)
  exact (pow_left_inj₀ hnn zero_le_one two_ne_zero).mp (by rw [hsq, one_pow])

/-- **The $\psi\circ\operatorname{Tr}_{K/k}$-self-dual measure on $K\otimes_k\mathbb A_k$ corresponds to the self-dual
measure of $\mathbb A_K$**: with the global factor $\prod_v|\det G|_v^{1/2}\cdot|\det G|_\infty^{1/2}$ (which is $1$),
$\Psi_*\big((\prod_v|\det G|_v^{1/2}|\det G|_\infty^{1/2})\,\mu_k^{\otimes\iota}\big) = \mu_K$. -/
theorem map_adeleBaseChange_traceSelfDual [DecidableEq ι] :
    (ENNReal.ofReal ((∏ᶠ v, traceFactor b v) *
      Real.sqrt |LinearMap.det (LinearMap.mulLeft ℝ (mixedEmbedding k (Algebra.discr k b)))|) •
        muAddVec k ι).map (adeleBaseChange b) = muAdd K := by
  rw [finprod_traceFactor_mul_inf, ENNReal.ofReal_one, one_smul, map_adeleBaseChange_muAddVec]

end

end QuadFormsKB.Tamagawa.Measure.Weil
