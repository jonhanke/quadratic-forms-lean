import QuadFormsKB.Tamagawa.Measure.Weil.SL2Approx

/-!
# Base change of finite adeles by density (finite part)

For a finite extension $K/k$ of number fields and a $k$-basis $b = (b_i)_{i\in\iota}$ of $K$, the additive
isomorphism $k^\iota\cong K$, $x\mapsto\sum_ix_ib_i$, extends to an **additive homeomorphism**
$$\Psi_f : \mathbb A_{k,f}^\iota\;\xrightarrow{\ \sim\ }\;\mathbb A_{K,f},$$
i.e. $K\otimes_k\mathbb A_{k,f}\cong\mathbb A_{K,f}$ in coordinates (`finBaseChange`, `finBaseChange_diag`).

*Route (a lean rewrite; no new dependency).* No local decomposition $K\otimes k_v\cong\prod_{w\mid v}K_w$ is used.
Instead, $\mathbb A_{F,f}$ is the completion of $F$ for the "ideal-adic" uniformity: $F$ is dense
(`denseRange_algebraMap_finiteAdele`, strong approximation), $\mathbb A_{F,f}$ is complete (locally compact), and the
sets $m\mathcal O_F$ ($m\in\mathbb Z\setminus0$) are a neighbourhood basis of $0$ for the induced topology
(`exists_int_forall_isIntegral_mul_mem`, `natNbhd_mem_nhds`, `isIntegral_of_mem_natNbhd`). Since $\mathcal O_K$ and
$\bigoplus_i\mathcal O_kb_i$ are commensurable (bounded denominators: `exists_int_isIntegral_mul_basis`,
`exists_int_isIntegral_mul_repr`), $x\mapsto\sum x_ib_i$ is a homeomorphism for the induced topologies, and the
generic `exists_continuousAddEquiv_of_denseRange` (uniqueness of completions, Mathlib's `AbstractCompletion`)
extends it.

*Comparison.* The FLT project proves the same statement as an algebra isomorphism by the local route:
`IsDedekindDomain.FiniteAdeleRing.baseChangeAlgEquiv : L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[L] 𝔸ᶠ[B, L]` in
`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` (367 lines, on top of `FLT/DedekindDomain/Completion/BaseChange.lean`,
870 lines; ImperialCollegeLondon/FLT, read 2026-10-18). It is cited, not imported.
-/

open IsDedekindDomain NumberField Topology Filter

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

section Generic


variable {K L A B : Type*} [AddCommGroup K] [AddCommGroup L]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B] [LocallyCompactSpace B]

/-- **Uniqueness of completions, additive form.** Let $A$, $B$ be locally compact Hausdorff commutative topological
groups, $i : K\to A$ and $j : L\to B$ additive maps with dense range, and $\varphi : K\cong L$ an additive isomorphism
that is a homeomorphism for the topologies induced by $i$ and $j$ (`h1`, `h2`: continuity at $0$). Then $\varphi$
extends to an additive homeomorphism $\Psi : A\cong B$ with $\Psi\circ i = j\circ\varphi$. (Both are completions:
locally compact groups are complete, `IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace`.) -/
theorem exists_continuousAddEquiv_of_denseRange (i : K →+ A) (j : L →+ B)
    (hi : DenseRange i) (hj : DenseRange j) (φ : K ≃+ L)
    (h1 : Tendsto (fun x => j (φ x)) (comap i (𝓝 0)) (𝓝 0))
    (h2 : Tendsto (fun y => i (φ.symm y)) (comap j (𝓝 0)) (𝓝 0)) :
    ∃ Ψ : A ≃ₜ+ B, ∀ x, Ψ (i x) = j (φ x) := by
  let uA : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let uB : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace A := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace A
  have : CompleteSpace B := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace B
  let uK : UniformSpace K := UniformSpace.comap i uA
  let uL : UniformSpace L := UniformSpace.comap j uB
  have : IsUniformAddGroup K := IsUniformAddGroup.comap i
  have : IsUniformAddGroup L := IsUniformAddGroup.comap j
  let pA : AbstractCompletion K :=
    { space := A, coe := i, uniformStruct := uA, complete := inferInstance,
      separation := inferInstance, isUniformInducing := ⟨rfl⟩, dense := hi }
  let pB : AbstractCompletion L :=
    { space := B, coe := j, uniformStruct := uB, complete := inferInstance,
      separation := inferInstance, isUniformInducing := ⟨rfl⟩, dense := hj }
  have hnK : (𝓝 (0 : K)) = comap i (𝓝 0) := by
    rw [nhds_induced, map_zero]
  have hnL : (𝓝 (0 : L)) = comap j (𝓝 0) := by
    rw [nhds_induced, map_zero]
  have hφ : UniformContinuous φ := by
    refine uniformContinuous_of_continuousAt_zero φ.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, hnK, hnL, tendsto_comap_iff]
    exact h1
  have hψ : UniformContinuous φ.symm := by
    refine uniformContinuous_of_continuousAt_zero φ.symm.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, hnK, hnL, tendsto_comap_iff]
    exact h2
  let e : K ≃ᵤ L := ⟨φ.toEquiv, hφ, hψ⟩
  let E := pA.mapEquiv pB e
  have hE : ∀ x, E (i x) = j (φ x) := fun x => pA.map_coe pB hφ x
  have hadd : ∀ a b : A, E (a + b) = E a + E b := by
    intro a b
    refine hi.induction_on₂ (p := fun a b => E (a + b) = E a + E b) ?_ ?_ a b
    · exact isClosed_eq (E.continuous.comp continuous_add)
        ((E.continuous.comp continuous_fst).add (E.continuous.comp continuous_snd))
    · intro x y
      simp only [← map_add, hE]
  refine ⟨⟨⟨E.toEquiv, hadd⟩, E.continuous, E.symm.continuous⟩, hE⟩

end Generic

section Nbhd

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-- **The sets $m\mathcal O_F$ form a neighbourhood basis of $0$ for the topology induced on $F$**, upper half: every
neighbourhood $U$ of $0$ in $\mathbb A_{F,f}$ contains $m\mathcal O_F$ for some $m\in\mathbb Z\setminus0$
($m = N(\prod_{v\in S}\mathfrak p_v^{k_v})$ for the finitely many places $S$ that $U$ constrains). -/
theorem exists_int_forall_isIntegral_mul_mem (U : Set AF) (hU : U ∈ 𝓝 0) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ ξ : F, IsIntegral ℤ ξ → algebraMap F AF ((m : F) * ξ) ∈ U := by
  have h0 : iK F 0 = 0 := rfl
  have hzW : iK F ⁻¹' U ∈ 𝓝 (0 : OProd F) :=
    (isOpenEmbedding_iK (F := F)).continuous.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  rw [nhds_pi, Filter.mem_pi'] at hzW
  obtain ⟨I, t, ht, hsub⟩ := hzW
  have hu : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u : Set (v.adicCompletion F),
      u ∈ 𝓝 (0 : v.adicCompletion F) ∧ Subtype.val ⁻¹' u ⊆ t v :=
    fun v => by
      obtain ⟨u, hu, hus⟩ := (mem_nhds_induced _ _ _).mp (ht v)
      exact ⟨u, hu, hus⟩
  choose u hu hus using hu
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > 0, Metric.ball (0 : v.adicCompletion F) ε ⊆ u v :=
    fun v => Metric.mem_nhds_iff.mp (hu v)
  choose ε hεpos hball using hε
  have hk : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, ‖QuadFormsKB.HN.ϖ v ^ (k : ℤ)‖ < ε v := by
    intro v
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (hεpos v) (QuadFormsKB.Analysis.norm_ϖ_lt_one v)
    exact ⟨k, by rw [zpow_natCast, norm_pow]; exact hk⟩
  choose kk hkk using hk
  set J : Ideal (𝓞 F) := ∏ v ∈ I, v.asIdeal ^ kk v with hJdef
  have hJ : J ≠ ⊥ := by
    rw [hJdef, Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    rintro ⟨v, -, hv⟩
    exact v.ne_bot (pow_eq_zero_iff'.mp hv).1
  set m : ℤ := (Ideal.absNorm J : ℤ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Int.natCast_ne_zero]
    exact fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)
  have hmJ : (m : 𝓞 F) ∈ J := by
    rw [hm]; push_cast; exact Ideal.absNorm_mem J
  refine ⟨m, hm0, fun ξ hξ => ?_⟩
  set η : 𝓞 F := ⟨ξ, hξ⟩
  have hη : ((m : F) * ξ) = algebraMap (𝓞 F) F ((m : 𝓞 F) * η) := by rw [map_mul, map_intCast]; rfl
  have hval : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (v.adicCompletion F) ((m : F) * ξ)) = v.intValuation ((m : 𝓞 F) * η) := by
    intro v
    rw [hη, QuadFormsKB.HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap F (v.adicCompletion F) ((m : F) * ξ) ∈ v.adicCompletionIntegers F := by
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
    exact v.intValuation_le_one _
  let w : OProd F := fun v => ⟨algebraMap F (v.adicCompletion F) ((m : F) * ξ), hint v⟩
  have hwI : w ∈ (I : Set (HeightOneSpectrum (𝓞 F))).pi t := by
    intro v hv
    refine hus v (hball v ?_)
    rw [Metric.mem_ball, dist_zero_right]
    have hmem : (m : 𝓞 F) * η ∈ v.asIdeal ^ kk v :=
      Ideal.mul_mem_right _ _ ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hmJ)
    have hle : Valued.v (algebraMap F (v.adicCompletion F) ((m : F) * ξ)) ≤ WithZero.exp (-((kk v : ℕ) : ℤ)) := by
      rw [hval]; exact (v.intValuation_le_pow_iff_mem _ _).mpr hmem
    have : algebraMap F (v.adicCompletion F) ((m : F) * ξ) ∈
        Metric.closedBall (0 : v.adicCompletion F) ‖QuadFormsKB.HN.ϖ v ^ ((kk v : ℕ) : ℤ)‖ := by
      rw [← QuadFormsKB.Analysis.coe_latticeV, SetLike.mem_coe, QuadFormsKB.Analysis.mem_latticeV]
      exact hle
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact lt_of_le_of_lt this (hkk v)
  have hmem := hsub hwI
  simp only [Set.mem_preimage] at hmem
  have hw : iK F w = algebraMap F AF ((m : F) * ξ) := Subtype.ext (funext fun v => rfl)
  rwa [hw] at hmem

/-- The open neighbourhood $m\hat{\mathcal O}$ of $0$ (for $m\ne0$), written as $\{x : m^{-1}x\in\hat{\mathcal O}\}$. -/
def natNbhd (m : ℤ) : Set AF := {x | algebraMap F AF ((m : F)⁻¹) * x ∈ OHat}

theorem natNbhd_mem_nhds (m : ℤ) : natNbhd (F := F) m ∈ 𝓝 0 := by
  refine (isOpen_OHat.preimage (continuous_const_mul (algebraMap F AF ((m : F)⁻¹)))).mem_nhds ?_
  simp only [Set.mem_preimage, mul_zero]
  exact zero_mem_OHat

/-- Lower half: $F\cap m\hat{\mathcal O} = m\mathcal O_F$. -/
theorem isIntegral_of_mem_natNbhd {m : ℤ} {ξ : F} (h : algebraMap F AF ξ ∈ natNbhd m) :
    IsIntegral ℤ ((m : F)⁻¹ * ξ) := by
  have : algebraMap F AF ((m : F)⁻¹ * ξ) ∈ OHat := by rw [map_mul]; exact h
  obtain ⟨a, ha⟩ := (algebraMap_mem_OHat_iff _).mp this
  rw [← ha]
  exact a.2

end Nbhd

section Denominators

/-- A number field is algebraic over $\mathbb Z$. -/
theorem isAlgebraic_int_numberField (F : Type) [Field F] [NumberField F] : Algebra.IsAlgebraic ℤ F := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  exact Algebra.IsAlgebraic.trans ℤ ℚ F

attribute [local instance] isAlgebraic_int_numberField

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K)

/-- Bounded denominators of a $k$-basis of $K$: $a\,b_i\in\mathcal O_K$ for some $a\in\mathbb Z\setminus0$. -/
theorem exists_int_isIntegral_mul_basis : ∃ a : ℤ, a ≠ 0 ∧ ∀ i, IsIntegral ℤ ((a : K) * b i) := by
  classical
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image b)
  refine ⟨y, hy, fun i => ?_⟩
  have := hint (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rwa [zsmul_eq_mul] at this

/-- Bounded denominators of coordinates: $a\cdot b^*_i(z)\in\mathcal O_k$ for all $z\in\mathcal O_K$, all $i$. -/
theorem exists_int_isIntegral_mul_repr :
    ∃ a : ℤ, a ≠ 0 ∧ ∀ z : K, IsIntegral ℤ z → ∀ i, IsIntegral ℤ ((a : k) * b.repr z i) := by
  classical
  let e := RingOfIntegers.basis K
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 K) => b.repr (e p.2 : K) p.1)
  refine ⟨y, hy, fun z hz i => ?_⟩
  set w : 𝓞 K := ⟨z, hz⟩
  have hz' : z = ∑ j, (e.repr w j : ℤ) • (e j : K) := by
    have := congrArg (algebraMap (𝓞 K) K) (e.sum_repr w)
    simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast] at this
    change z = _
    rw [show z = algebraMap (𝓞 K) K w from rfl, ← this]
    simp [zsmul_eq_mul]
  rw [hz', map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  have hj := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  rw [zsmul_eq_mul] at hj
  have : (y : k) * (b.repr ((e.repr w j : ℤ) • (e j : K))) i =
      (e.repr w j : ℤ) • ((y : k) * b.repr (e j : K) i) := by
    rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, zsmul_eq_mul]; ring
  rw [this]
  exact hj.smul _

end Denominators

section FiniteBaseChange


variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {ι : Type} [Fintype ι] (b : Module.Basis ι k K)

local notation "Ak" => FiniteAdeleRing (𝓞 k) k
local notation "AK" => FiniteAdeleRing (𝓞 K) K

/-- The diagonal $k^\iota\to\mathbb A_{k,f}^\iota$. -/
def diagFinVec : (ι → k) →+ (ι → Ak) := AddMonoidHom.compLeft (algebraMap k Ak).toAddMonoidHom ι

@[simp] theorem diagFinVec_apply (x : ι → k) (i : ι) : diagFinVec x i = algebraMap k Ak (x i) := rfl

/-- $x\mapsto\sum_ix_ib_i$ is continuous at $0$ for the induced topologies. -/
theorem tendsto_basis_finite :
    Tendsto (fun x : ι → k => algebraMap K AK (b.equivFun.symm x)) (comap diagFinVec (𝓝 0)) (𝓝 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨m, hm0, hm⟩ := exists_int_forall_isIntegral_mul_mem U hU
  obtain ⟨a, ha0, ha⟩ := exists_int_isIntegral_mul_basis b
  rw [Filter.mem_comap]
  refine ⟨Set.univ.pi fun _ => natNbhd (a * m),
    set_pi_mem_nhds Set.finite_univ fun _ _ => natNbhd_mem_nhds _, fun x hx => ?_⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, diagFinVec_apply] at hx
  have hη := fun i => isIntegral_of_mem_natNbhd (hx i)
  have hk0 : ((a * m : ℤ) : k) ≠ 0 := by exact_mod_cast mul_ne_zero ha0 hm0
  set η : ι → k := fun i => ((a * m : ℤ) : k)⁻¹ * x i
  have hxη : ∀ i, x i = ((a * m : ℤ) : k) * η i := fun i => by simp only [η]; field_simp
  have heq : b.equivFun.symm x = (m : K) * ∑ i, algebraMap k K (η i) * ((a : K) * b i) := by
    rw [Module.Basis.equivFun_symm_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, hxη i, map_mul, map_intCast]
    push_cast; ring
  rw [Set.mem_preimage, heq]
  refine hm _ (IsIntegral.sum _ fun i _ => ?_)
  exact ((hη i).algebraMap).mul (ha i)

/-- The coordinate map $K\to k^\iota$ is continuous at $0$ for the induced topologies. -/
theorem tendsto_basis_finite_symm :
    Tendsto (fun y : K => diagFinVec (b.equivFun y)) (comap (algebraMap K AK) (𝓝 0)) (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i0
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨m, hm0, hm⟩ := exists_int_forall_isIntegral_mul_mem U hU
  obtain ⟨a, ha0, ha⟩ := exists_int_isIntegral_mul_repr b
  rw [Filter.mem_comap]
  refine ⟨natNbhd (a * m), natNbhd_mem_nhds _, fun y hy => ?_⟩
  have hK0 : ((a * m : ℤ) : K) ≠ 0 := by exact_mod_cast mul_ne_zero ha0 hm0
  have h1 : algebraMap K AK y ∈ natNbhd (a * m) := hy
  have h2 := isIntegral_of_mem_natNbhd (F := K) h1
  obtain ⟨ζ, hζ, hyζ⟩ : ∃ ζ : K, IsIntegral ℤ ζ ∧ y = algebraMap k K ((a * m : ℤ) : k) * ζ :=
    ⟨((a * m : ℤ) : K)⁻¹ * y, h2, by rw [map_intCast, ← mul_assoc, mul_inv_cancel₀ hK0, one_mul]⟩
  subst hyζ
  have heq : b.equivFun (algebraMap k K ((a * m : ℤ) : k) * ζ) i0 = (m : k) * ((a : k) * b.repr ζ i0) := by
    rw [Module.Basis.equivFun_apply, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
    push_cast; ring
  show algebraMap k _ (b.equivFun _ i0) ∈ U
  rw [heq]
  exact hm _ (ha ζ hζ i0)

/-- $k^\iota$ is dense in $\mathbb A_{k,f}^\iota$. -/
theorem denseRange_diagFinVec : DenseRange (diagFinVec (k := k) (ι := ι)) := by
  have : ⇑(diagFinVec (k := k) (ι := ι)) = Pi.map fun _ => algebraMap k Ak := by
    funext x i; exact diagFinVec_apply x i
  rw [this]
  exact DenseRange.piMap fun _ => denseRange_algebraMap_finiteAdele

/-- **Base change of finite adeles** (existence): an additive homeomorphism $\mathbb A_{k,f}^\iota\cong\mathbb A_{K,f}$
extending $x\mapsto\sum_ix_ib_i$ on $k^\iota$. -/
@[kb "casselsfrohlich1967" "Ch. II §14 (adeles of an extension) [unverified]; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem exists_finBaseChange :
    ∃ Ψ : (ι → Ak) ≃ₜ+ AK, ∀ x : ι → k, Ψ (diagFinVec x) = algebraMap K AK (b.equivFun.symm x) := by
  have h1 : Tendsto (fun x => (algebraMap K AK).toAddMonoidHom (b.equivFun.symm.toAddEquiv x))
      (comap diagFinVec (𝓝 0)) (𝓝 0) := tendsto_basis_finite b
  have h2 : Tendsto (fun y => diagFinVec (b.equivFun.symm.toAddEquiv.symm y))
      (comap (algebraMap K AK).toAddMonoidHom (𝓝 0)) (𝓝 0) := by
    have h := tendsto_basis_finite_symm b
    have e1 : (fun y => diagFinVec (b.equivFun.symm.toAddEquiv.symm y)) = fun y => diagFinVec (b.equivFun y) := by
      funext y; rfl
    have e2 : ((algebraMap K AK).toAddMonoidHom : K → AK) = algebraMap K AK := rfl
    rw [e1, e2]; exact h
  have G := exists_continuousAddEquiv_of_denseRange (K := ι → k) (L := K) (A := ι → Ak) (B := AK)
  have G2 := G diagFinVec (algebraMap K AK).toAddMonoidHom
  have G3 := G2 denseRange_diagFinVec denseRange_algebraMap_finiteAdele
  have G4 := G3 b.equivFun.symm.toAddEquiv h1 h2
  obtain ⟨Ψ, hΨ⟩ := G4
  exact ⟨Ψ, hΨ⟩

/-- **The finite base change** $\Psi_f : \mathbb A_{k,f}^\iota\cong\mathbb A_{K,f}$ (additive homeomorphism), chosen by
`exists_finBaseChange`; it is unique (`finBaseChange_unique`). -/
def finBaseChange : (ι → Ak) ≃ₜ+ AK := (exists_finBaseChange b).choose

/-- $\Psi_f(x) = \sum_ix_ib_i$ for $x\in k^\iota$. -/
theorem finBaseChange_diag (x : ι → k) :
    finBaseChange b (diagFinVec x) = algebraMap K AK (b.equivFun.symm x) :=
  (exists_finBaseChange b).choose_spec x

/-- Uniqueness: a continuous map agreeing with $\Psi_f$ on $k^\iota$ is $\Psi_f$. -/
theorem finBaseChange_unique {f : (ι → Ak) → AK} (hf : Continuous f)
    (h : ∀ x : ι → k, f (diagFinVec x) = algebraMap K AK (b.equivFun.symm x)) : f = finBaseChange b :=
  denseRange_diagFinVec.equalizer hf (finBaseChange b).continuous (funext fun x => by
    simp only [Function.comp_apply, h, finBaseChange_diag])

end FiniteBaseChange

end

end QuadFormsKB.Tamagawa.Measure.Weil
