import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeFinite

/-!
# Base change of the archimedean part
For a finite extension $K/k$ of number fields with a $k$-basis $b$ of $K$:
* `infMap k K` : $k_\infty\to K_\infty$ ($\mathbb R$-linear, `mixedSpace`), with
  `infMap_mixedEmbedding` : it extends $k\hookrightarrow K$;
* **`infBaseChange b`** : $k_\infty^\iota\cong K_\infty$ ($\mathbb R$-linear homeomorphism),
  $(a_i)\mapsto\sum_ib_i\,L(a_i)$, with `infBaseChange_diag` : it is $x\mapsto\sum_ix_ib_i$ on $k^\iota$.
  Bijectivity: the range contains $K$, whose $\mathbb R$-span is $K_\infty$ (`span_range_mixedEmbedding`), and
  $\dim_{\mathbb R}k_\infty^\iota = |\iota|[k:\mathbb Q] = [K:\mathbb Q] = \dim_{\mathbb R}K_\infty$.
No decomposition $K\otimes_kk_v\cong\prod_{w\mid v}K_w$ of the "mixed spaces" is needed.
-/

open IsDedekindDomain NumberField Topology Filter NumberField.mixedEmbedding

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

section InfiniteBaseChange

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K)

variable (k K) in
/-- The $\mathbb R$-linear extension $k_\infty\to K_\infty$ of $k\hookrightarrow K$, defined on the basis
`latticeBasis k` (the image of an integral basis). -/
def infMap : mixedSpace k →ₗ[ℝ] mixedSpace K :=
  (latticeBasis k).constr ℝ fun i => mixedEmbedding K (algebraMap k K (integralBasis k i))

/-- The mixed embedding is $\mathbb Q$-linear. -/
theorem mixedEmbedding_rat_smul {F : Type} [Field F] [NumberField F] (q : ℚ) (x : F) :
    mixedEmbedding F (q • x) = (q : ℝ) • mixedEmbedding F x := by
  ext w
  · simp only [mixedEmbedding_apply_isReal, map_rat_smul, Prod.smul_fst, Pi.smul_apply]
    rw [Rat.smul_def, smul_eq_mul]
  · simp only [mixedEmbedding_apply_isComplex, map_rat_smul, Prod.smul_snd, Pi.smul_apply]
    rw [Rat.smul_def, Complex.real_smul, Complex.ofReal_ratCast]

/-- `infMap` extends $k\hookrightarrow K$. -/
theorem infMap_mixedEmbedding (x : k) :
    infMap k K (mixedEmbedding k x) = mixedEmbedding K (algebraMap k K x) := by
  rw [← (integralBasis k).sum_repr x]
  simp only [map_sum, mixedEmbedding_rat_smul, map_smul, ← latticeBasis_apply, Module.Basis.constr_basis,
    infMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_rat_smul, mixedEmbedding_rat_smul]

/-- $\Psi_\infty : k_\infty^\iota\to K_\infty$, $a\mapsto\sum_i b_i\cdot L(a_i)$ with $L$ = `infMap`. -/
def infBaseChangeLin : (ι → mixedSpace k) →ₗ[ℝ] mixedSpace K :=
  ∑ i, (LinearMap.mulLeft ℝ (mixedEmbedding K (b i))) ∘ₗ infMap k K ∘ₗ LinearMap.proj i

theorem infBaseChangeLin_apply (a : ι → mixedSpace k) :
    infBaseChangeLin b a = ∑ i, mixedEmbedding K (b i) * infMap k K (a i) := by
  simp [infBaseChangeLin]

theorem infBaseChangeLin_diag (x : ι → k) :
    infBaseChangeLin b (fun i => mixedEmbedding k (x i)) = mixedEmbedding K (b.equivFun.symm x) := by
  rw [infBaseChangeLin_apply, Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [infMap_mixedEmbedding, Algebra.smul_def, map_mul, mul_comm]

/-- $F$ spans $F_\infty$ over $\mathbb R$. -/
theorem span_range_mixedEmbedding (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (mixedEmbedding F)) = ⊤ := by
  refine eq_top_iff.mpr ((latticeBasis F).span_eq.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨_, (latticeBasis_apply F i).symm⟩

theorem infBaseChangeLin_surjective : Function.Surjective (infBaseChangeLin b) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_mixedEmbedding K, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  refine ⟨fun i => mixedEmbedding k (b.equivFun y i), ?_⟩
  rw [infBaseChangeLin_diag, LinearEquiv.symm_apply_apply]

include b in
theorem finrank_baseChange_inf :
    Module.finrank ℝ (ι → mixedSpace k) = Module.finrank ℝ (mixedSpace K) := by
  rw [Module.finrank_pi_fintype, mixedEmbedding.finrank, mixedEmbedding.finrank,
    ← Module.finrank_mul_finrank ℚ k K, Module.finrank_eq_card_basis b, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_comm]

theorem infBaseChangeLin_bijective : Function.Bijective (infBaseChangeLin b) :=
  ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_baseChange_inf b)).mpr
    (infBaseChangeLin_surjective b), infBaseChangeLin_surjective b⟩

/-- **The archimedean base change** $k_\infty^\iota\cong K_\infty$ ($\mathbb R$-linear homeomorphism), with
$(x_i)\mapsto\sum_ix_ib_i$ on $k^\iota$. -/
def infBaseChange : (ι → mixedSpace k) ≃L[ℝ] mixedSpace K :=
  (LinearEquiv.ofBijective _ (infBaseChangeLin_bijective b)).toContinuousLinearEquiv

theorem infBaseChange_apply (a : ι → mixedSpace k) : infBaseChange b a = infBaseChangeLin b a := rfl

@[kb "casselsfrohlich1967" "Ch. II (Cassels), §10, Thm., (10.2), p. 57, at the infinite places"]
theorem infBaseChange_diag (x : ι → k) :
    infBaseChange b (fun i => mixedEmbedding k (x i)) = mixedEmbedding K (b.equivFun.symm x) :=
  infBaseChangeLin_diag b x

end InfiniteBaseChange

end

end QuadFormsKB.Tamagawa.Measure.Weil
